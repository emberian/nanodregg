/-
# Protocol.Rows.Writer — HOST's loop, run in process for the member rows

The writer the rows drive is `Host.serve` (the deployed loop: group commit, the seal cadence,
whole-World bases) over the in-memory disk (`Host.Sim.memStore`, `Host.Sim.memCheckpoint`), on a
dedicated thread, fed through a channel port; it reopens with `Host.openWith` (one base, the tail
after it, `Host.Record.step` folding each batch record and asserting its chain). The sealers are the
Sim's toy MACs (`Host.Sim.keys`); the cadence is small enough that the rows seal bases.

ONE ARM IS NOT HOST'S YET: `Host.handle` refuses `log` as `notServed` until HOST-3 serves it
(HOST-11; HOST-3 confirmed it will, gated by `Protocol.Envelope.check` on the loop's World). Until
then this machine answers `log` itself by exactly that rule (the envelope checked against the World
as the batch has advanced it, then every event logged from the envelope's height, with the writer's
height and chain), from `HostState.events`, which a reopen rebuilds from the whole segment. The arm,
`HostState.events` and `eventsOf` are deleted the day HOST's lands.
-/
import Protocol.Rows.Sim
import Protocol.Envelope
import Host.Serve
import Host.Loop
import Host.Open
import Host.Record
import Host.Sim.MemStore
import Host.Sim.Toy

namespace Nanodregg.Protocol.Rows.Writer

open Nanodregg.Kernel Nanodregg.Kernel.Receive Nanodregg.Host Nanodregg.Protocol
open Nanodregg.Protocol.Rows.Sim (D)

/-- The loop's state: the World and the events logged so far (event `i` landed at height `i + 1`). -/
structure HostState where
  world : World D
  events : Array ByteArray

/-- The writer's parameters, which a plant may mutate. -/
structure Params where
  X : Ctx D
  /-- serve `log` only to an envelope `Envelope.check` accepts -/
  gateLog : Bool := true
  /-- reopen to a World whose journal is empty -/
  forgetJournal : Bool := false

/-- Small enough that a row of a few dozen turns seals bases; the deployed bounds on size. -/
def cadence : Cadence :=
  { sealMinBytes := 8192, worldBytesMax := Cadence.deployed.worldBytesMax,
    recordBytesMax := Cadence.deployed.recordBytesMax }

def limits : Limits := ⟨16, 1 <<< 20⟩
/-- Batches one loop process serves before it exits `fuel` (the supervisor restarts it). -/
def fuel : Nat := 1000000

def refusedA (name : String) : Answer HostState (Turn D) := .reply Status.refused.code name.toUTF8

/-- The log page from height `start`: every event since, the height, the chain. `none` when it does
not fit one reply frame (HOST-11 pages; the follow machine reads one page per command). -/
def page (X : Ctx D) (hs : HostState) (start : Nat) : Option ByteArray := do
  let l ← Text.fitList Bounds.frameBytesMax (hs.events.extract start hs.events.size).toList
  let h ← Text.fit Bounds.frameBytesMax (Text.u64 hs.world.height)
  let c ← Text.fit Bounds.frameBytesMax (X.env.bytes hs.world.chain)
  let b := logReplyFrame.bytes (l, h, c, ())
  if b.size + 1 ≤ Bounds.frameBytesMax then some b else none

def logAnswer (P : Params) (hs : HostState) (payload : ByteArray) : Answer HostState (Turn D) :=
  match Envelope.ofBytes P.X payload with
  | none => refusedA ReadRefusal.badEnvelope.name
  | some e =>
      match (if P.gateLog then Envelope.check P.X hs.world e else .ok ()) with
      | .error r => refusedA r.name
      | .ok () =>
          match page P.X hs e.start with
          | some b => .reply Status.ok.code b
          | none => refusedA "pageTooLarge"

def admit (P : Params) (hs : HostState) (t : Turn D) : Except (Reject D) HostState :=
  match World.admit P.X.env hs.world t with
  | .ok w => .ok { world := w, events := hs.events.push t.event }
  | .error r => .error r

def machine (P : Params) : Machine HostState (Turn D) (Reject D) Frame where
  admit := admit P
  handle hs f :=
    if f.op = Op.log.code then logAnswer P hs f.payload else
    match Host.handle P.X hs.world f with
    | .reply s p => .reply s p
    | .admit t r => .admit t fun hs' => r hs'.world
    | .page start => .page start
  refuse hs t r := Host.onReject P.X hs.world t r
  ok := Status.ok.code

/-- The Store in memory: the segment and the base file. -/
structure Mem where
  disk : IO.Ref Host.Sim.Disk
  bases : IO.Ref Host.Sim.Bases

/-- HOST's in-memory checkpoint, sealing the World part of the loop's state. -/
def checkpoint (m : Mem) : Checkpoint HostState :=
  let ck := Host.Sim.memCheckpoint m.disk m.bases Host.Sim.keys cadence Sim.world
  { async := ck.async, write := fun hs offset tag index => ck.write hs.world offset tag index }

/-- A Store as genesis leaves it: the genesis base at offset 0, an empty segment. -/
def genesisStore (g : World D) : IO (Except String Mem) := do
  match Base.file Host.Sim.keys cadence Sim.world g 0 Codec.Digest.zero [] with
  | .error f => return .error f.name
  | .ok file => return .ok ⟨← IO.mkRef {}, ← IO.mkRef { file, history := #[(file, 0)] }⟩

def genesisResident (g : World D) : Resident HostState :=
  { world := ⟨g, #[]⟩, pos := ⟨0, Codec.Digest.zero⟩, sealed := ⟨0, Sim.world.size g⟩, index := #[] }

/-- Every event a whole segment logged, in order: the stand-in log arm's source (see above). -/
def eventsOf (seg : ByteArray) : Array ByteArray :=
  let rv := Log.recover Host.Sim.keys.segment cadence.recordBytesMax segmentInitial seg
  rv.records.foldl (fun acc r => match (Record.codec Sim.dc).decode r with
    | .ok (ts, _) => ts.foldl (fun a t => a.push t.event) acc
    | .error _ => acc) #[]

/-- The one open over the in-memory Store: HOST's `openWith`, the writer's fold. -/
def reopen (P : Params) (base seg : ByteArray) : Except String (Resident HostState) :=
  match Id.run (openWith Host.Sim.keys cadence Sim.world (fun w => (w.height, P.X.env.bytes w.chain))
      (Record.step Sim.dc (World.fold P.X.env))
      base seg.size fun off len => pure (.ok (seg.extract off (off + len)))) with
  | .error f => .error f.name
  | .ok o =>
      let w := if P.forgetJournal then { o.opened.world with journal := {} } else o.opened.world
      .ok { world := ⟨w, eventsOf (seg.extract 0 o.pos.offset)⟩, pos := o.pos, sealed := o.sealed,
            index := o.index }

/-- A loop running on its own thread. -/
structure Running where
  reqs : Std.CloseableChannel.Sync Frame
  reps : Std.CloseableChannel.Sync Host.Reply
  task : Task (Except IO.Error (Exit × Resident HostState))

def start (P : Params) (m : Mem) (r : Resident HostState) : IO Running := do
  let reqs ← Std.CloseableChannel.Sync.new
  let reps ← Std.CloseableChannel.Sync.new
  let port : Port :=
    { recv := reqs.recv
      poll := reqs.tryRecv
      send := fun r => do discard <| (reps.send r).toBaseIO }
  let task ← IO.asTask (prio := .dedicated) do
    try
      serve (machine P) ⟨fun hs ts => Record.encode Sim.dc hs.world ts,
          fun hs => (hs.world.height, P.X.env.bytes hs.world.chain)⟩ Host.Sim.keys.segment
        (checkpoint m) cadence (Host.Sim.memStore m.disk none) (fun _ _ => pure (Status.ok.code, ByteArray.empty))
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
def Running.stop (h : Running) : IO (Except String (Exit × Resident HostState)) := do
  discard <| (h.reqs.close).toBaseIO
  match ← IO.wait h.task with
  | .ok r => pure (.ok r)
  | .error e => pure (.error (toString e))

end Nanodregg.Protocol.Rows.Writer
