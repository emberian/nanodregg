/-
# Host.Wire — the frames between the supervisor and `host serve`

Toward the Host (one per client request): `u32le len ‖ u32le conn ‖ u8 op ‖ payload`, `len` the
body's size, `5 ≤ len ≤ bodyMax`. Toward the supervisor: `u32le len ‖ u32le conn ‖ u8 status ‖
payload`. (`client/src/mux.rs` is the other end; the op and status bytes are PROTOCOL's table.)

The supervisor is trusted to frame (it decides nothing, but it is ours): a body outside the bounds
means the mux is broken, and the Host stops by name rather than guess where the next frame starts.
-/
import Host.Batch
import Host.Log
import Protocol.Table

namespace Nanodregg.Host

open Nanodregg.Codec (Stream)

/-- One request from the supervisor. -/
structure Frame where
  conn : UInt32
  op : UInt8
  payload : ByteArray

/-- The largest body toward the Host: a client frame body plus the connection id. -/
def bodyMax : Nat := Protocol.Bounds.frameBytesMax + 4

/-- Why the request stream stopped. -/
inductive Stop where
  /-- the supervisor closed the stream at a frame boundary -/
  | eof
  /-- the stream ended inside a frame -/
  | truncated
  /-- a frame body outside `5 ≤ len ≤ bodyMax` -/
  | badLength (len : Nat)
  /-- the reader's frame budget (`Host.Cli.lifetimeFrames`) is spent -/
  | lifetime
  /-- reading the stream raised an IO error -/
  | readFailed
  deriving DecidableEq, Repr

def Stop.name : Stop → String
  | .eof => "eof"
  | .truncated => "truncated"
  | .badLength _ => "badLength"
  | .lifetime => "lifetime"
  | .readFailed => "readFailed"

/-- The frame a body holds: `u32 conn ‖ u8 op ‖ payload`. -/
def decodeBody (body : ByteArray) : Except Stop Frame :=
  match Stream.u32.get body 0, Stream.u8.get body 4 with
  | .ok (conn, _), .ok (op, _) => .ok { conn, op, payload := body.extract 5 body.size }
  | _, _ => .error (.badLength body.size)

/-- A body's frame on the wire. -/
def encodeFrame (f : Frame) : ByteArray :=
  Stream.u8.put f.op (Stream.u32.put f.conn (Log.lenBytes (5 + f.payload.size))) ++ f.payload

/-- A reply on the wire. -/
def encodeReply (r : Reply) : ByteArray :=
  Stream.u8.put r.status (Stream.u32.put r.conn (Log.lenBytes (5 + r.payload.size))) ++ r.payload

/-- Read exactly `n` bytes, in at most `n + 1` reads (each read that returns bytes makes
progress; an empty read is the end of the stream). -/
def readExact (s : IO.FS.Stream) (n : Nat) : IO (Option ByteArray) :=
  go (n + 1) ByteArray.empty
where
  go : Nat → ByteArray → IO (Option ByteArray)
    | 0, _ => pure none
    | fuel + 1, acc => do
      if n ≤ acc.size then return some acc
      let chunk ← s.read (n - acc.size).toUSize
      if chunk.isEmpty then return none
      go fuel (acc ++ chunk)

/-- Read one request frame. -/
def readFrame (s : IO.FS.Stream) : IO (Except Stop Frame) := do
  let head ← s.read 4
  if head.isEmpty then return .error .eof
  let head ← if head.size = 4 then pure (some head) else do
    match ← readExact s (4 - head.size) with
    | some rest => pure (some (head ++ rest))
    | none => pure none
  let some head := head | return .error .truncated
  let some len := Log.lenAt head 0 | return .error .truncated
  if len < 5 ∨ bodyMax < len then return .error (.badLength len)
  match ← readExact s len with
  | none => return .error .truncated
  | some body => return decodeBody body

end Nanodregg.Host
