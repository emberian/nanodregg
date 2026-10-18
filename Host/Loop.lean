/-
# Host.Loop — the resident loop of `host serve`

    serve fuel:
      batch  ← one frame (blocking), then what is already queued (≤ batchMax frames, ≤ batchBytesMax)
      (w', out) := admitBatch w batch                    -- pure (Host.Batch)
      if out.staged ≠ ∅: append one Log frame of the batch record; sync
         failure → every reply of the batch is `uncertain`; stop (`Exit.uncertain`)
      send out.replies
      serve (fuel - 1)

Group commit with no timer (HOST-3): while one sync runs, requests queue in the channel and become
the next batch. Replies leave only after the sync, so no reply reports a state a crash can take
back. A failed append or sync is never retried (HOST-4: after a failed fsync the kernel may have
dropped the dirty pages); the supervisor restarts the Host and `recover` decides what is on disk.

A round of `serve` runs `fuel` batches and returns `Exit.fuel`; `restarts` (the resident's one
fuel-and-restart loop, LAW 4 as amended) then reopens the Store from disk IN PROCESS, asserts the
reopened state is the state the loop held (`reopenDiverged` otherwise), and serves the next round
on the same port. So reopen runs routinely and no connection notices (D4). The loop holds no frame
between batches: a frame that does not fit a batch goes back into the port (`Port.unread`), so a
round can end at any batch boundary without dropping one (`Host.Proofs.Loop.drainM_conserves`).

The physical store is a record of two IO actions (`Store`), so the simulation and the crash plants
drive this same loop over an in-memory disk (`Host.MemStore`), and `host serve` over the file.
-/
import Host.Batch
import Host.Base
import Host.Wire
import Protocol.Table
import Std.Sync.Channel

namespace Nanodregg.Host

open Nanodregg.Codec (Digest)

/-- The physical segment, as the loop sees it. -/
structure Store where
  /-- write all of these bytes at the end of the segment -/
  append : ByteArray → IO Unit
  /-- make every appended byte durable (`F_FULLFSYNC` / `fdatasync`) -/
  sync : IO Unit

/-- Where requests come from and replies go. -/
structure Port where
  /-- block for the next frame; `none` once the stream has stopped -/
  recv : IO (Option Frame)
  /-- a frame already queued, without blocking -/
  poll : IO (Option Frame)
  /-- put a frame back at the front: the next `recv` or `poll` returns it. Called only right after
  a `poll` returned it, so the port holds at most one frame put back. -/
  unread : Frame → IO Unit
  send : Reply → IO Unit
  /-- stop accepting frames; the ones already queued stay readable by `poll` -/
  close : IO Unit

structure Limits where
  batchMax : Nat
  batchBytesMax : Nat

/-- Why `serve` returned (law 7: each by name, `Exit.name`). -/
inductive Exit where
  /-- the request stream ended -/
  | eof
  /-- the batch budget of this round is spent; `restarts` reopens and continues -/
  | fuel
  /-- an append or sync failed: the batch's replies were `uncertain`; restart and recover -/
  | uncertain (detail : String)
  /-- a seal failed; every reply already sent is durable in the segment; restart and recover -/
  | sealFailed (fault : SealFault)
  /-- a batch the recorder refuses (more Turns than one record holds, `bytes = none`) or whose
  record is over `Cadence.recordBytesMax` bytes: the batch was not appended and its replies were
  `uncertain`. At the deployed cadence the byte arm never fires on steps `World.step` took
  (`Host.Deployed.recorder_encode_size_le`, HOST-47); it stays as the refusal of anything else. -/
  | recordTooLarge (turns : Nat) (bytes : Option Nat)
  /-- a fuel restart's reopen refused (the refusal's name) -/
  | reopenFailed (name : String)
  /-- the reopened Store is not the state the loop held: a defect in the open or the append path -/
  | reopenDiverged
  /-- the resident's restart budget is spent (unreachable before the port's own lifetime bound) -/
  | lifetime
  /-- the request stream stopped other than at a frame boundary, or at the reader's lifetime -/
  | stream (stop : Stop)
  deriving Repr

def Exit.name : Exit → String
  | .eof => "eof"
  | .fuel => "fuel"
  | .uncertain _ => "uncertain"
  | .sealFailed _ => "sealFailed"
  | .recordTooLarge _ _ => "recordTooLarge"
  | .reopenFailed _ => "reopenFailed"
  | .reopenDiverged => "reopenDiverged"
  | .lifetime => "lifetime"
  | .stream _ => "stream"

/-- How the loop seals a base: `write w seg entries index` appends `entries` (the index entries
since the last base, never the whole index: HOST-30) to `index.log` after the `index.count`
entries there, syncs them, then writes the base of `w`, which is the segment prefix
`[0, seg.offset)` chained to `seg.tag`, counting the entries up to the last appended, durably; it
returns the World's encoded size, the digest of its bytes and what the new base names of the
index (HOST-33). With `async`
(`host serve`) it runs in a dedicated Task over the immutable `w`, off the loop; without it (the
simulation) it runs inline, so a seeded run seals at the same points every time. -/
structure Checkpoint (W : Type) where
  /-- returns the World's encoded size, the digest of its bytes (`Keys.worldDigest`) and the
  entry count and last tag the new base names -/
  write : W → Position → Array Entry → IndexAt → IO (Except SealFault (Nat × ByteArray × IndexAt))
  async : Bool

/-- How the loop writes a batch record and indexes it: the record of the staged entries (each step
with the roots digest after it, HOST-29, KERNEL-47) given the World after them, and the log
position of a World: its step count and chain (`Env.bytes`). The position is steps, not height: a
recorded refusal is a step at an unchanged height. -/
structure Recorder (W T : Type) where
  /-- the batch record of the staged pairs, or `none` when they are more than one record may hold -/
  encode : W → Array T → Option ByteArray
  mark : W → Nat × ByteArray

/-- A seal in flight: the offset it seals at, the sealed World's step count and chain, the index
entries its base will name, and its Task. -/
structure Pending where
  offset : Nat
  steps : Nat
  chain : ByteArray
  indexCount : Nat
  task : Task (Except IO.Error (Except SealFault (Nat × ByteArray × IndexAt)))

/-- Everything the resident loop holds. -/
structure Resident (W : Type) where
  world : W
  pos : Position
  sealed : Sealed
  /-- one entry per record AFTER the newest durable base, in order: entries
  `sealed.index.count, sealed.index.count + 1, …` of the index. The base's own are on disk in
  `index.log`; the loop never holds them (HOST-33: RAM O(tail), not O(records)) -/
  index : Array Entry
  pending : Option Pending := none

/-- A frame of `n` bytes appended at `pos` keeps the tail after the newest durable base within
`tailMax` (HOST-14 condition 4). `commitBatch` cannot be called without a proof of it. -/
def withinTail (c : Cadence) (sealed : Sealed) (pos n : Nat) : Bool :=
  decide (pos + n - sealed.offset ≤ c.tailMax sealed.bytes)

/-- Take the queued frames after `first`: at most `limits.batchMax` frames and, past the first,
`limits.batchBytesMax` payload bytes. A frame that does not fit is put back (`unread`), so the
caller holds nothing but the batch. Generic in the monad so its conservation is a theorem over a
list model of the port (`Host.Proofs.Loop.drainM_conserves`); the loop runs it in `IO`. -/
def drainM {m : Type → Type} [Monad m] (poll : m (Option Frame)) (unread : Frame → m Unit)
    (limits : Limits) (first : Frame) : m (Array Frame) :=
  go limits.batchMax #[first] first.payload.size
where
  go : Nat → Array Frame → Nat → m (Array Frame)
    | 0, acc, _ => pure acc
    | fuel + 1, acc, bytes => do
      if limits.batchMax ≤ acc.size then return acc
      match ← poll with
      | none => return acc
      | some f =>
        if limits.batchBytesMax < bytes + f.payload.size then
          unread f
          return acc
        go fuel (acc.push f) (bytes + f.payload.size)

def drain (port : Port) (limits : Limits) (first : Frame) : IO (Array Frame) :=
  drainM port.poll port.unread limits first

variable {W T R : Type}

/-- The replies of a batch whose append did not complete: all `uncertain`. -/
def uncertainAll (replies : Array Reply) : Array Reply :=
  replies.map fun r => { r with status := Protocol.Status.uncertain.code, payload := ByteArray.empty }

/-- Append one batch record as one Log frame and make it durable. Only within the tail bound. -/
def commitBatch (c : Cadence) (sealed : Sealed) (store : Store) (s : Log.Sealer) (pos : Position)
    (record : ByteArray) (_within : withinTail c sealed pos.offset (frameSize record) = true) :
    IO (Except String Position) := do
  try
    store.append (Log.frame s pos.tag.bytes record)
    store.sync
    return .ok ⟨pos.offset + frameSize record, tagDigest s (pos.tag.bytes ++ record)⟩
  catch e => return .error (toString e)

/-- The entries a seal writes: every entry the loop holds (those after the newest base), as a
fresh Array. The Task is handed this and never the loop's own index, so no `push` on the loop
shares an array with a Task (a shared push copies the whole array, on the request path, law 5;
HOST-30). -/
def sealEntries (index : Array Entry) : Array Entry :=
  index.extract 0 index.size

/-- Start sealing `w` at `pos` in a dedicated Task, after the newest base `sealed`. -/
def spawnSeal (ck : Checkpoint W) (mark : W → Nat × ByteArray) (w : W) (pos : Position)
    (sealed : Sealed) (index : Array Entry) : IO Pending := do
  let (h, chain) := mark w
  let fresh := sealEntries index
  let count := sealed.index.count + index.size
  if ck.async then
    return ⟨pos.offset, h, chain, count, ← IO.asTask (ck.write w pos fresh sealed.index) .dedicated⟩
  else
    return ⟨pos.offset, h, chain, count, .pure (.ok (← ck.write w pos fresh sealed.index))⟩

/-- Wait for a seal; the base it made is the newest durable one. -/
def settle (p : Pending) : IO (Except SealFault Sealed) := do
  match ← IO.wait p.task with
  | .error e => return .error (.io (toString e))
  | .ok (.error f) => return .error f
  | .ok (.ok (bytes, digest, index)) => return .ok ⟨p.offset, bytes, p.steps, p.chain, digest, index⟩

/-- Take up a settled base: it is the newest durable one, and the entries it counts leave the
loop's memory (they are on disk), so the loop holds only the entries after it. O(entries held)
once per seal. -/
def Resident.install (r : Resident W) (sealed : Sealed) : Resident W :=
  { r with sealed, pending := none,
           index := r.index.extract (sealed.index.count - r.sealed.index.count) r.index.size }

/-- A finished seal is taken up without waiting. -/
def reap (r : Resident W) : IO (Except SealFault (Resident W)) := do
  match r.pending with
  | none => return .ok r
  | some p =>
    if ← IO.hasFinished p.task then
      match ← settle p with
      | .ok sealed => return .ok (r.install sealed)
      | .error f => return .error f
    else return .ok r

/-- Wait for the seal in flight, if any, and take its base up. -/
def settlePending (r : Resident W) : IO (Except SealFault (Resident W)) := do
  match r.pending with
  | none => return .ok r
  | some p => match ← settle p with
    | .ok sealed => return .ok (r.install sealed)
    | .error f => return .error f

/-- THE seal act (HOST-43): wait for the seal in flight; then, unless the newest base is already at
the World's position, seal the World as it stands through `ck` (the Store's own checkpoint path:
entries since the base, the base file, sync, rename) and take the base up. The operator's
`host seal STORE`, the loop's inline seal (`makeRoom`) and the member rows' checkpoint are this one
function over their Store's `Checkpoint` (law 1). -/
def sealNow (ck : Checkpoint W) (mark : W → Nat × ByteArray) (r : Resident W) :
    IO (Except SealFault (Resident W)) := do
  let r ← match ← settlePending r with
    | .ok r => pure r
    | .error f => return .error f
  if r.sealed.offset = r.pos.offset then return .ok r
  match ← settle (← spawnSeal ck mark r.world r.pos r.sealed r.index) with
  | .ok sealed => return .ok (r.install sealed)
  | .error f => return .error f

/-- Make room for a frame of `n` bytes: wait for the seal in flight, and if the tail is still too
long, seal the World as it stands (`sealNow`). After the second step the newest base is at
`pos`, so any frame up to `Log.frameMax c.recordBytesMax` fits (`Host.Proofs.Base.within_after_seal`). -/
def makeRoom (ck : Checkpoint W) (mark : W → Nat × ByteArray) (c : Cadence) (r : Resident W) (n : Nat) :
    IO (Except SealFault (Resident W)) := do
  if withinTail c r.sealed r.pos.offset n then return .ok r
  let r ← match ← settlePending r with
    | .ok r => pure r
    | .error f => return .error f
  if withinTail c r.sealed r.pos.offset n then return .ok r
  sealNow ck mark r

/-- The end of a run: the seal in flight is waited for, so a base the loop started is never
abandoned half-written by the exit. -/
def finish (exit : Exit) (r : Resident W) : IO (Exit × Resident W) := do
  match r.pending with
  | none => return (exit, r)
  | some p => match ← settle p with
    | .ok sealed => return (exit, r.install sealed)
    | .error f => return (.sealFailed f, { r with pending := none })

/-- Put built pages into their replies: reply `i` takes page `(i, status, payload)`'s status and
payload, and nothing else of any reply changes (its conn above all: `Proofs.Loop.applyPages_conns`). -/
def applyPages (replies : Array Reply) (pages : Array (Nat × UInt8 × ByteArray)) : Array Reply :=
  pages.foldl (fun rs (i, status, payload) => rs.modify i fun rep => { rep with status, payload }) replies

/-- Fill the replies that wait for a log page, from the durable state: build every page, then
`applyPages`. -/
def fillPages (pager : Resident W → Deferred → IO (UInt8 × ByteArray)) (r : Resident W) (out : Out T) :
    IO (Array Reply) := do
  let built ← out.pages.mapM fun (i, d) => do
    let (status, payload) ← pager r d
    return (i, status, payload)
  return applyPages out.replies built

/-- Append one record that takes the World to `w'`, durably, within the tail bound, and index it;
start a seal if the cadence is reached. The writer's loop and the follower's (`Host.Follow`) both
append through this, so both keep the same Store invariants. On a refusal nothing was appended
past what was synced, and the caller answers its requests `uncertain`. -/
def append (rec : Recorder W T) (s : Log.Sealer) (ck : Checkpoint W) (c : Cadence) (store : Store)
    (r : Resident W) (w' : W) (staged : Array T) : IO (Except Exit (Resident W)) := do
  let some record := rec.encode w' staged | return .error (.recordTooLarge staged.size none)
  if c.recordBytesMax < record.size then return .error (.recordTooLarge staged.size (some record.size))
  let r ← match ← makeRoom ck rec.mark c r (frameSize record) with
    | .ok r => pure r
    | .error f => return .error (.sealFailed f)
  if within : withinTail c r.sealed r.pos.offset (frameSize record) = true then
    match ← commitBatch c r.sealed store s r.pos record within with
    | .error detail => return .error (.uncertain detail)
    | .ok pos =>
      let (h, chain) := rec.mark r.world
      let r := { r with world := w', pos, index := r.index.push ⟨h, r.pos.offset, chain⟩ }
      if shouldSeal c r.sealed r.pending.isSome pos.offset then
        return .ok { r with pending := some (← spawnSeal ck rec.mark w' pos r.sealed r.index) }
      return .ok r
  else
    -- not proved unreachable (makeRoom's inline seal is IO): a named stop
    return .error (.recordTooLarge staged.size (some record.size))

/-- The loop. `append` writes `rec.encode after staged`, the batch record (`Host.Record.encode`); `pager r d`
builds a deferred reply (a `log` or `read` page: status, payload) from the durable state `r`. -/
def serve {N : Type} (m : Machine W T Frame N) (rec : Recorder W (T × N)) (s : Log.Sealer) (ck : Checkpoint W)
    (c : Cadence) (store : Store) (pager : Resident W → Deferred → IO (UInt8 × ByteArray)) (port : Port)
    (limits : Limits) : Nat → Resident W → IO (Exit × Resident W)
  | 0, r => finish .fuel r
  | fuel + 1, r => do
    let r ← match ← reap r with
      | .ok r => pure r
      | .error f => return (.sealFailed f, { r with pending := none })
    let some first ← port.recv | finish .eof r
    let batch ← drain port limits first
    let (w', out) := m.admitBatch r.world (batch.toList.map fun f => ⟨f.conn, f⟩)
    if out.staged.isEmpty then
      let r := { r with world := w' }
      (← fillPages pager r out).forM port.send
      serve m rec s ck c store pager port limits fuel r
    else
      match ← append rec s ck c store r w' out.staged with
      | .error e =>
        (uncertainAll out.replies).forM port.send
        finish e r
      | .ok r =>
        (← fillPages pager r out).forM port.send
        serve m rec s ck c store pager port limits fuel r

/-- What a reopened Store must agree with the loop on: the World's step count and chain, the segment
position and its tag, the entries the newest base counts and its last tag, and the entries held
after it. The pair assertion of every fuel restart. -/
def agrees (mark : W → Nat × ByteArray) (a b : Resident W) : Bool :=
  mark a.world == mark b.world && a.pos.offset == b.pos.offset && a.pos.tag == b.pos.tag &&
    a.sealed.index.count == b.sealed.index.count && a.sealed.index.last == b.sealed.index.last &&
    a.index.size == b.index.size && b.pending.isNone

/-- The resident's one fuel-and-restart loop (LAW 4 as amended): run a round; on `fuel`, reopen
the Store from disk in process (`reopen` names its own refusal: `reopenFailed` for an open that
refuses, `reopenDiverged` for bytes on disk the loop never synced) (the round's `finish` has settled any seal, and every appended byte
was synced), refuse a reopen that disagrees with the state the loop held, and run the next round
from the REOPENED state on the same port. Every other exit ends the resident. `rounds` is a static
bound the port's lifetime reaches first (`Host.Cli.restartsMax`). -/
def restarts (round : Resident W → IO (Exit × Resident W))
    (reopen : IO (Except Exit (Resident W))) (mark : W → Nat × ByteArray) :
    Nat → Resident W → IO (Exit × Resident W)
  | 0, r => return (.lifetime, r)
  | k + 1, r => do
    let (exit, r) ← round r
    match exit with
    | .fuel =>
      match ← reopen with
      | .error e => return (e, r)
      | .ok r' =>
        if agrees mark r r' then restarts round reopen mark k r'
        else return (.reopenDiverged, r)
    | e => return (e, r)

/-- At an exit that ends the resident: stop the port and answer every frame still queued
`refused stopped`, so no accepted request goes unanswered; a queued hang-up is acknowledged by
`hangUp` (its name, never `stopped`). At most `bound` frames. -/
def refuseQueued (port : Port) (stopped : UInt8 × ByteArray) (hangUp : Frame → Option (UInt8 × ByteArray))
    (bound : Nat) : IO Nat := do
  port.close
  go bound 0
where
  go : Nat → Nat → IO Nat
    | 0, n => pure n
    | k + 1, n => do
      match ← port.poll with
      | none => pure n
      | some f =>
        let (s, p) := (hangUp f).getD stopped
        port.send ⟨f.conn, s, p⟩; go k (n + 1)

/-! ## The stdio port: a reader task frames stdin into a bounded channel -/

/-- Frame `input` into `ch` until it stops; at most `fuel` frames (`Stop.lifetime`). Closes the
channel and returns why it stopped. -/
def pump (input : IO.FS.Stream) (ch : Std.CloseableChannel.Sync Frame) : Nat → IO Stop
  | 0 => do discard <| (ch.close).toBaseIO; pure .lifetime
  | fuel + 1 => do
    match ← readFrame input with
    | .ok f =>
      match ← (ch.send f).toBaseIO with
      | .ok () => pump input ch fuel
      | .error _ => pure .eof
    | .error stop => do discard <| (ch.close).toBaseIO; pure stop

/-- A reply, written and flushed. -/
def sendTo (output : IO.FS.Stream) (r : Reply) : IO Unit := do
  output.write (encodeReply r)
  output.flush

/-- The port over a channel, with a one-frame slot for `unread`; replies go to `send`. -/
def channelPort (ch : Std.CloseableChannel.Sync Frame) (back : IO.Ref (Option Frame))
    (send : Reply → IO Unit) : Port where
  recv := do
    match ← back.swap none with
    | some f => pure (some f)
    | none => ch.recv
  poll := do
    match ← back.swap none with
    | some f => pure (some f)
    | none => ch.tryRecv
  unread f := back.set (some f)
  send
  close := discard <| (ch.close).toBaseIO

end Nanodregg.Host
