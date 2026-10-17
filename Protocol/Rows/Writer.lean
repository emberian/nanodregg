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
  /-- an `expired` refusal states the name alone, no height (a plant: the shape before
  PROTOCOL-19, which leaves a follower more than a window behind unable to catch up) -/
  unstatedExpiry : Bool := false
  /-- `log` serves an envelope the gate refuses `notYet` (a plant: the read gate without the
  envelope's lower bound, PROTOCOL-27) -/
  ignoreNotBefore : Bool := false
  /-- admit against the World with every spent nullifier forgotten (a plant: a writer that does
  not keep its spent set) -/
  forgetSpent : Bool := false

/-- Small enough that a row of a few dozen turns seals bases; the deployed bounds on size. -/
def cadence : Cadence :=
  { sealMinBytes := 8192, worldBytesMax := Cadence.deployed.worldBytesMax,
    recordBytesMax := Cadence.deployed.recordBytesMax }

/-- The page budget the rows' writer pages with: HOST's `Page.budget` is a frame, which no row's
log reaches, so a row would never see a page end before the tip. It must hold every single event
the rows log (HOST's own premise, `Host.Page.budget_fits_event`, restated for the rows' events):
the largest is the grain row's install of the shipped lifecycle package (9000 bytes of text). An
event past it is never served, and the follower refuses the empty page short of the tip
`badResult` (how the 4096 this replaced was found). 16384 still makes a cold follower page. -/
def pageBudget : Nat := 16384

def limits : Limits := ⟨16, 1 <<< 20⟩
/-- Batches one round of the loop serves before it ends `fuel` (`Host.restarts` reopens in process). -/
def fuel : Nat := 1000000

/-- The World with its spent nullifiers removed and its cells kept (the `writerForgetsSpent`
plant's view; the trie is rebuilt from the kept listing). -/
def unspend (E : Env D) (w : World D) : World D :=
  { w with trie := (w.trie.toList.filter fun p => match p.1 with
      | .cell _ => true
      | .nullifier _ => false).foldl (fun m p => m.insert (trieSpec E) p.1 p.2) .empty }

/-- `Host.handle`, except under the `openLog` plant: a `log` envelope that decodes is paged
without `Envelope.check`. -/
def machine (P : Params) : Machine (World D) (Turn D) (Reject D) Frame D where
  admit w t := World.admit P.X.env (if P.forgetSpent then unspend P.X.env w else w) t
  note := World.root P.X.env
  handle w f :=
    if !P.gateLog && f.op = Op.log.code then
      match Envelope.ofBytes P.X f.payload with
      | some e => .defer (.log e.start)
      | none => Host.handle P.X w f
    else if P.ignoreNotBefore && f.op = Op.log.code then
      match Envelope.ofBytes P.X f.payload with
      | some e => match Envelope.check P.X w e with
        | .error .notYet => .defer (.log e.start)
        | _ => Host.handle P.X w f
      | none => Host.handle P.X w f
    else match Host.handle P.X w f with
      | .reply c p =>
        if P.unstatedExpiry && (expiredHeight? p).isSome then .reply c "expired".toUTF8 else .reply c p
      | a => a
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
      (fun w => P.X.env.bytes (World.genesisChain P.X.env w.origin))
      (Record.step Sim.dc (World.admit P.X.env) (World.root P.X.env)) g with
  | .error f => return .error f.name
  | .ok (d, b, r) => return .ok (⟨← IO.mkRef d, ← IO.mkRef b⟩, r)

/-- The one open over the in-memory Store: HOST's `openWith`, the writer's fold. -/
def reopen (P : Params) (base seg : ByteArray) : Except String (Resident (World D)) :=
  match Id.run (openWith Host.Sim.keys cadence Sim.world (fun w => (w.height, P.X.env.bytes w.chain))
      (fun w => P.X.env.bytes (World.genesisChain P.X.env w.origin))
      (Record.step Sim.dc (World.admit P.X.env) (World.root P.X.env))
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
  let port := channelPort reqs (← IO.mkRef none) fun r => do discard <| (reps.send r).toBaseIO
  let task ← IO.asTask (prio := .dedicated) do
    try
      serve (machine P) ⟨fun _ ts => Record.encode Sim.dc ts,
          fun w => (w.height, P.X.env.bytes w.chain)⟩ Host.Sim.keys.segment
        (checkpoint m) cadence (Host.Sim.memStore m.disk none) (pager P.X P.lieTip P.forgeBase m)
        port limits fuel r
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
