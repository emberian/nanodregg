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

The loop is the one unbounded loop (LAW 4 as amended): `fuel` batches, then `Exit.fuel`, and the
supervisor restarts it, so reopen runs routinely.

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
  send : Reply → IO Unit

structure Limits where
  batchMax : Nat
  batchBytesMax : Nat

/-- Why `serve` returned (law 7: each by name, `Exit.name`). -/
inductive Exit where
  /-- the request stream ended -/
  | eof
  /-- the batch budget of this process is spent; restart -/
  | fuel
  /-- an append or sync failed: the batch's replies were `uncertain`; restart and recover -/
  | uncertain (detail : String)
  /-- a seal failed; every reply already sent is durable in the segment; restart and recover -/
  | sealFailed (fault : SealFault)
  /-- a batch record over `Cadence.recordBytesMax`: the batch was not appended and its replies
  were `uncertain` -/
  | recordTooLarge (bytes : Nat)
  deriving Repr

def Exit.name : Exit → String
  | .eof => "eof"
  | .fuel => "fuel"
  | .uncertain _ => "uncertain"
  | .sealFailed _ => "sealFailed"
  | .recordTooLarge _ => "recordTooLarge"

/-- How the loop seals a base: `seal w offset tag` writes the base of `w`, which is the segment
prefix `[0, offset)` chained to `tag`, durably, and returns its World's encoded size. With `async`
(`host serve`) it runs in a dedicated Task over the immutable `w`, off the loop; without it (the
simulation) it runs inline, so a seeded run seals at the same points every time. -/
structure Checkpoint (W : Type) where
  write : W → Nat → Digest → Array Entry → IO (Except SealFault Nat)
  async : Bool

/-- How the loop writes a batch record and indexes it: the record of the staged Turns given the
World after them, and the height and chain (`Env.bytes`) of a World. -/
structure Recorder (W T : Type) where
  encode : W → Array T → ByteArray
  mark : W → Nat × ByteArray

/-- A seal in flight: the offset it seals at, and its Task. -/
structure Pending where
  offset : Nat
  task : Task (Except IO.Error (Except SealFault Nat))

/-- Everything the resident loop holds. -/
structure Resident (W : Type) where
  world : W
  pos : Position
  sealed : Sealed
  /-- one entry per record in the segment, in order -/
  index : Array Entry
  pending : Option Pending := none

/-- A frame of `n` bytes appended at `pos` keeps the tail after the newest durable base within
`tailMax` (HOST-14 condition 4). `commitBatch` cannot be called without a proof of it. -/
def withinTail (c : Cadence) (sealed : Sealed) (pos n : Nat) : Bool :=
  decide (pos + n - sealed.offset ≤ c.tailMax sealed.bytes)

/-- Take the queued frames after `first`: at most `limits.batchMax` frames and, past the first,
`limits.batchBytesMax` payload bytes. A frame that does not fit is carried into the next batch. -/
def drain (port : Port) (limits : Limits) (first : Frame) : IO (Array Frame × Option Frame) :=
  go limits.batchMax #[first] first.payload.size
where
  go : Nat → Array Frame → Nat → IO (Array Frame × Option Frame)
    | 0, acc, _ => pure (acc, none)
    | fuel + 1, acc, bytes => do
      if limits.batchMax ≤ acc.size then return (acc, none)
      match ← port.poll with
      | none => return (acc, none)
      | some f =>
        if limits.batchBytesMax < bytes + f.payload.size then return (acc, some f)
        go fuel (acc.push f) (bytes + f.payload.size)

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

/-- Start sealing `w` at `pos` in a dedicated Task. -/
def spawnSeal (ck : Checkpoint W) (w : W) (pos : Position) (index : Array Entry) : IO Pending := do
  if ck.async then
    return ⟨pos.offset, ← IO.asTask (ck.write w pos.offset pos.tag index) .dedicated⟩
  else
    return ⟨pos.offset, .pure (.ok (← ck.write w pos.offset pos.tag index))⟩

/-- Wait for a seal; the base it made is the newest durable one. -/
def settle (p : Pending) : IO (Except SealFault Sealed) := do
  match ← IO.wait p.task with
  | .error e => return .error (.io (toString e))
  | .ok (.error f) => return .error f
  | .ok (.ok bytes) => return .ok ⟨p.offset, bytes⟩

/-- A finished seal is taken up without waiting. -/
def reap (r : Resident W) : IO (Except SealFault (Resident W)) := do
  match r.pending with
  | none => return .ok r
  | some p =>
    if ← IO.hasFinished p.task then
      match ← settle p with
      | .ok sealed => return .ok { r with sealed, pending := none }
      | .error f => return .error f
    else return .ok r

/-- Make room for a frame of `n` bytes: wait for the seal in flight, and if the tail is still too
long, seal the World as it stands and wait for that. After the second step the newest base is at
`pos`, so any frame up to `Log.frameMax c.recordBytesMax` fits (`Host.Proofs.Base.within_after_seal`). -/
def makeRoom (ck : Checkpoint W) (c : Cadence) (r : Resident W) (n : Nat) :
    IO (Except SealFault (Resident W)) := do
  if withinTail c r.sealed r.pos.offset n then return .ok r
  let r ← match r.pending with
    | none => pure r
    | some p => match ← settle p with
      | .ok sealed => pure { r with sealed, pending := none }
      | .error f => return .error f
  if withinTail c r.sealed r.pos.offset n then return .ok r
  match ← settle (← spawnSeal ck r.world r.pos r.index) with
  | .ok sealed => return .ok { r with sealed, pending := none }
  | .error f => return .error f

/-- The end of a run: the seal in flight is waited for, so a base the loop started is never
abandoned half-written by the exit. -/
def finish (exit : Exit) (r : Resident W) : IO (Exit × Resident W) := do
  match r.pending with
  | none => return (exit, r)
  | some p => match ← settle p with
    | .ok sealed => return (exit, { r with sealed, pending := none })
    | .error f => return (.sealFailed f, { r with pending := none })

/-- Fill the replies that wait for a log page, from the durable state. -/
def fillPages (pager : Resident W → Nat → IO (UInt8 × ByteArray)) (r : Resident W) (out : Out T) :
    IO (Array Reply) :=
  out.pages.foldlM (init := out.replies) fun rs (i, start) => do
    let (status, payload) ← pager r start
    return rs.modify i fun rep => { rep with status, payload }

/-- Append one record that takes the World to `w'`, durably, within the tail bound, and index it;
start a seal if the cadence is reached. The writer's loop and the follower's (`Host.Follow`) both
append through this, so both keep the same Store invariants. On a refusal nothing was appended
past what was synced, and the caller answers its requests `uncertain`. -/
def append (rec : Recorder W T) (s : Log.Sealer) (ck : Checkpoint W) (c : Cadence) (store : Store)
    (r : Resident W) (w' : W) (record : ByteArray) : IO (Except Exit (Resident W)) := do
  if c.recordBytesMax < record.size then return .error (.recordTooLarge record.size)
  let r ← match ← makeRoom ck c r (frameSize record) with
    | .ok r => pure r
    | .error f => return .error (.sealFailed f)
  if within : withinTail c r.sealed r.pos.offset (frameSize record) = true then
    match ← commitBatch c r.sealed store s r.pos record within with
    | .error detail => return .error (.uncertain detail)
    | .ok pos =>
      let (h, chain) := rec.mark r.world
      let r := { r with world := w', pos, index := r.index.push ⟨h, r.pos.offset, chain⟩ }
      if shouldSeal c r.sealed r.pending.isSome pos.offset then
        return .ok { r with pending := some (← spawnSeal ck w' pos r.index) }
      return .ok r
  else
    -- not proved unreachable (makeRoom's inline seal is IO): a named stop
    return .error (.recordTooLarge record.size)

/-- The loop. `rec.encode after staged` is the batch record (`Host.Record.encode`); `pager r start`
builds a `log` page (status, payload) from the durable state `r`. -/
def serve (m : Machine W T R Frame) (rec : Recorder W T) (s : Log.Sealer) (ck : Checkpoint W)
    (c : Cadence) (store : Store) (pager : Resident W → Nat → IO (UInt8 × ByteArray)) (port : Port)
    (limits : Limits) : Nat → Resident W → Option Frame → IO (Exit × Resident W)
  | 0, r, _ => finish .fuel r
  | fuel + 1, r, carried => do
    let r ← match ← reap r with
      | .ok r => pure r
      | .error f => return (.sealFailed f, { r with pending := none })
    let first ← match carried with
      | some f => pure (some f)
      | none => port.recv
    let some first := first | finish .eof r
    let (batch, carry) ← drain port limits first
    let (w', out) := m.admitBatch r.world (batch.toList.map fun f => ⟨f.conn, f⟩)
    if out.staged.isEmpty then
      let r := { r with world := w' }
      (← fillPages pager r out).forM port.send
      serve m rec s ck c store pager port limits fuel r carry
    else
      match ← append rec s ck c store r w' (rec.encode w' out.staged) with
      | .error e =>
        (uncertainAll out.replies).forM port.send
        finish e r
      | .ok r =>
        (← fillPages pager r out).forM port.send
        serve m rec s ck c store pager port limits fuel r carry

/-! ## The stdio port: a reader task frames stdin into a bounded channel -/

/-- Frame `input` into `ch` until it stops; at most `fuel` frames. Closes the channel and returns
why it stopped. -/
def pump (input : IO.FS.Stream) (ch : Std.CloseableChannel.Sync Frame) : Nat → IO Stop
  | 0 => do discard <| (ch.close).toBaseIO; pure .eof
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

/-- The port over a channel the reader task fills. -/
def channelPort (ch : Std.CloseableChannel.Sync Frame) (output : IO.FS.Stream) : Port where
  recv := ch.recv
  poll := ch.tryRecv
  send := sendTo output

end Nanodregg.Host
