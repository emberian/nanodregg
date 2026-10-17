/-
# Protocol.Rows.Writer — HOST's loop, run in process for the member rows

The writer the rows drive is `Host.serve` (the deployed loop: group commit, the seal cadence,
whole-World bases) over the in-memory disk (`Host.Sim.memStore`, `Host.Sim.memCheckpoint`), on a
dedicated thread, fed through a channel port; it reopens with `Host.openWith` (one base, the tail
after it, `Host.Record.step` folding each batch record and asserting its chain). The sealers are the
Sim's toy MACs (`Host.Sim.keys`); the cadence is small enough that the rows seal bases.

Every arm is HOST's: `log` is `Host.handle`'s (the read envelope checked against the World as the
batch advanced it) and its page is `Host.Page.build` over the in-memory segment (`pager`), the
same code `Host.Deployed.pager` runs over the segment file. The one deviation is a plant
(`Params.gateLog = false`).
-/
import Protocol.Rows.Sim
import Protocol.Envelope
import Host.Serve
import Host.Loop
import Host.Open
import Host.Record
import Host.Sim.MemStore
import Host.Sim.Toy
import Host.Page

namespace Nanodregg.Protocol.Rows.Writer

open Nanodregg.Kernel Nanodregg.Kernel.Receive Nanodregg.Host Nanodregg.Protocol
open Nanodregg.Protocol.Rows.Sim (D)

/-- The writer's parameters, which a plant may mutate. -/
structure Params where
  X : Ctx D
  /-- serve `log` only to an envelope `Envelope.check` accepts (HOST's `handle`); `false` is the
  plant that answers a page to any envelope that decodes -/
  gateLog : Bool := true
  /-- reopen to a World whose journal is empty -/
  forgetJournal : Bool := false
  /-- every page states its own end as the tip (a plant: the writer hides the rest of its log) -/
  lieTip : Bool := false
  /-- `read` pages serve the newest base with one World byte flipped, stating the honest digest (a
  plant: a forged base) -/
  forgeBase : Bool := false

/-- Small enough that a row of a few dozen turns seals bases; the deployed bounds on size. -/
def cadence : Cadence :=
  { sealMinBytes := 8192, worldBytesMax := Cadence.deployed.worldBytesMax,
    recordBytesMax := Cadence.deployed.recordBytesMax }

/-- The page budget the rows' writer pages with: HOST's `Page.budget` is a frame, which no row's
log reaches, so a row would never see a page end before the tip. 4096 bytes holds every single
event the rows log (the largest is a package install) and makes a cold follower page. -/
def pageBudget : Nat := 4096

def limits : Limits := ⟨16, 1 <<< 20⟩
/-- Batches one loop process serves before it exits `fuel` (the supervisor restarts it). -/
def fuel : Nat := 1000000

/-- `Host.handle`, except under the `openLog` plant: a `log` envelope that decodes is paged
without `Envelope.check`. -/
def machine (P : Params) : Machine (World D) (Turn D) (Reject D) Frame where
  admit := World.admit P.X.env
  handle w f :=
    if !P.gateLog && f.op = Op.log.code then
      match Envelope.ofBytes P.X f.payload with
      | some e => .defer (.log e.start)
      | none => Host.handle P.X w f
    else Host.handle P.X w f
  refuse w t r := Host.onReject P.X w t r
  ok := Status.ok.code

/-- The Store in memory: the segment and the base file. -/
structure Mem where
  disk : IO.Ref Host.Sim.Disk
  bases : IO.Ref Host.Sim.Bases

/-- HOST's in-memory checkpoint. -/
def checkpoint (m : Mem) : Checkpoint (World D) :=
  Host.Sim.memCheckpoint m.disk m.bases Host.Sim.keys cadence Sim.world

/-- HOST's pager (`Host.Page.build` + `Host.Page.bytes`) over the in-memory segment's synced bytes:
what `Host.Deployed.pager` does over the segment file. -/
def pager (X : Ctx D) (lieTip forgeBase : Bool) (m : Mem) (r : Resident (World D)) :
    Deferred → IO (UInt8 × ByteArray)
  | .read start => do
    if !forgeBase then Host.Sim.memBasePage Page.budget m.bases r start else
    -- the World bytes follow the base frame's 4-byte length; flip one in the middle
    let file := Host.Sim.flipByte (← m.bases.get).file (4 + r.sealed.bytes / 2)
    match Id.run (Page.basePage Page.budget (fun off len => pure (file.extract off (off + len))) r.sealed start) with
    | .ok b => pure (Status.ok.code, b)
    | .error f => pure (Status.refused.code, f.name.toUTF8)
  | .log start => do
  let seg := (← m.disk.get).synced
  match Id.run (Page.build X.env Sim.dc X.digestOf Host.Sim.keys.segment cadence.recordBytesMax
      pageBudget (fun off len => pure (seg.extract off (off + len))) r.index
      (r.world.height, X.env.bytes r.world.chain) start) with
  | .error f => pure (Status.refused.code, f.name.toUTF8)
  | .ok a => match Page.bytes a (if lieTip then a.height else r.world.height) with
    | .ok b => pure (Status.ok.code, b)
    | .error f => pure (Status.refused.code, f.name.toUTF8)

/-- A Store as genesis leaves it (HOST's `memGenesis`: the origin frame, the base after it), and
the loop's state the one open gives over it. -/
def genesisStore (P : Params) (g : World D) : IO (Except String (Mem × Resident (World D))) := do
  match Host.Sim.memGenesis Host.Sim.keys cadence Sim.world (fun w => (w.height, P.X.env.bytes w.chain))
      (Record.step Sim.dc (World.fold P.X.env)) g with
  | .error f => return .error f.name
  | .ok (d, b, r) => return .ok (⟨← IO.mkRef d, ← IO.mkRef b⟩, r)

/-- The one open over the in-memory Store: HOST's `openWith`, the writer's fold. -/
def reopen (P : Params) (base seg : ByteArray) : Except String (Resident (World D)) :=
  match Id.run (openWith Host.Sim.keys cadence Sim.world (fun w => (w.height, P.X.env.bytes w.chain))
      (Record.step Sim.dc (World.fold P.X.env))
      base seg.size fun off len => pure (.ok (seg.extract off (off + len)))) with
  | .error f => .error f.name
  | .ok o =>
      let w := if P.forgetJournal then { o.opened.world with journal := {} } else o.opened.world
      .ok { world := w, pos := o.pos, sealed := o.sealed,
            index := o.index }

/-- A loop running on its own thread. -/
structure Running where
  reqs : Std.CloseableChannel.Sync Frame
  reps : Std.CloseableChannel.Sync Host.Reply
  task : Task (Except IO.Error (Exit × Resident (World D)))

def start (P : Params) (m : Mem) (r : Resident (World D)) : IO Running := do
  let reqs ← Std.CloseableChannel.Sync.new
  let reps ← Std.CloseableChannel.Sync.new
  let port : Port :=
    { recv := reqs.recv
      poll := reqs.tryRecv
      send := fun r => do discard <| (reps.send r).toBaseIO }
  let task ← IO.asTask (prio := .dedicated) do
    try
      serve (machine P) ⟨fun w ts => Record.encode Sim.dc w ts,
          fun w => (w.height, P.X.env.bytes w.chain)⟩ Host.Sim.keys.segment
        (checkpoint m) cadence (Host.Sim.memStore m.disk none) (pager P.X P.lieTip P.forgeBase m)
        port limits fuel r none
    finally
      discard <| (reps.close).toBaseIO
  pure ⟨reqs, reps, task⟩

/-- One request and its reply; `none` once the loop has stopped. -/
def Running.ask (h : Running) (f : Frame) : IO (Option Host.Reply) := do
  match ← (h.reqs.send f).toBaseIO with
  | .error _ => pure none
  | .ok () => h.reps.recv

/-- Stop the loop at a frame boundary; why it stopped and its last state. -/
def Running.stop (h : Running) : IO (Except String (Exit × Resident (World D))) := do
  discard <| (h.reqs.close).toBaseIO
  match ← IO.wait h.task with
  | .ok r => pure (.ok r)
  | .error e => pure (.error (toString e))

end Nanodregg.Protocol.Rows.Writer
