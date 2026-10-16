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
import Host.Log
import Host.Wire
import Protocol.Table
import Std.Sync.Channel

namespace Nanodregg.Host

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

/-- Why `serve` returned. -/
inductive Exit where
  /-- the request stream ended -/
  | eof
  /-- the batch budget of this process is spent; restart -/
  | fuel
  /-- an append or sync failed: the batch's replies were `uncertain`; restart and recover -/
  | uncertain (detail : String)
  deriving Repr

/-- What a batch record is: CODEC's encoding of the staged Turns, given the World before them. -/
structure Recorder (W T : Type) where
  record : W → Array T → ByteArray

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

/-- Append one batch record as one Log frame and make it durable. -/
def commitBatch (store : Store) (s : Log.Sealer) (tag record : ByteArray) : IO (Except String ByteArray) := do
  try
    store.append (Log.frame s tag record)
    store.sync
    return .ok (s.tag (tag ++ record))
  catch e => return .error (toString e)

/-- The loop. `tag` is the last frame's tag (the segment's chain so far). -/
def serve (m : Machine W T R Frame) (rec : Recorder W T) (s : Log.Sealer) (store : Store)
    (port : Port) (limits : Limits) : Nat → W → ByteArray → Option Frame → IO (Exit × W)
  | 0, w, _, _ => pure (.fuel, w)
  | fuel + 1, w, tag, carried => do
    let first ← match carried with
      | some f => pure (some f)
      | none => port.recv
    let some first := first | return (.eof, w)
    let (batch, carry) ← drain port limits first
    let (w', out) := m.admitBatch w (batch.toList.map fun f => ⟨f.conn, f⟩)
    if out.staged.isEmpty then
      out.replies.forM port.send
      serve m rec s store port limits fuel w' tag carry
    else
      match ← commitBatch store s tag (rec.record w out.staged) with
      | .error detail =>
        (uncertainAll out.replies).forM port.send
        return (.uncertain detail, w)
      | .ok tag' =>
        out.replies.forM port.send
        serve m rec s store port limits fuel w' tag' carry

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
