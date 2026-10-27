/-
# Hosting.Resident.Sockets — the resident's two sockets, through `Host.Sock` (HOSTING-27)

- The member socket (`nd --stdio` behind nd-supervise, HOSTING-20/25): one command per connection.
  The request frame is `u32le len ‖ Op.command ‖ version ‖ commandLayout(argv)` (PROTOCOL-87), where `len` counts the op byte
  (the client's frame). The reply frame is `u32le len ‖ status ‖ commandReplyLayout`, the `done`
  step's exit, stdout and stderr. Every layout is `Protocol.Table`'s, through the one codec.
- The broker socket (keybroker, HOSTING-12): one ask per connection, `u32le len ‖ ask`, answered
  by `u32le len ‖ answer`. Encoded by `Broker.Wire.encodeAsk` and read by
  `Broker.Wire.decodeAnswer`, the one codec (HOSTING-29: the answer carries text, never a provider
  body).

Every call is bounded by `Host.Sock`'s per-call deadline. Every failure comes back as a value naming
it, never as a thrown error, so the loop decides what each one means.
-/
import Host.Sock
import Host.Wire
import Protocol.Command.Stdio
import Hosting.BrokerWire

namespace Nanodregg.Hosting.Resident

open Nanodregg.Host Nanodregg.Codec

/-- How long one member command may take: the client's own reply bound. -/
def memberMs : Nat := Protocol.Bounds.replyMsMax

/-- How long one ask may take, from its first byte to its answer's last (keybroker's upstream call
is inside it). -/
def askMs : Nat := 120000

/-- One frame's body off a stream: `u32le len ‖ body`, `1 ≤ len ≤ max`. -/
def readBody (s : IO.FS.Stream) (max : Nat) : IO (Except String ByteArray) := do
  let some head ← Host.readExact s 4 | return .error "closed"
  let some len := Host.Log.lenAt head 0 | return .error "closed"
  if len = 0 ∨ max < len then return .error s!"frameLength {len}"
  let some body ← Host.readExact s len | return .error "truncated"
  return .ok body

/-- `u32le n` -/
def le32 (n : Nat) : ByteArray := Stream.u32.bytes n.toUInt32

/-- The `command` payload for `argv`, when it fits `argvBytesMax`. -/
def commandPayload (argv : List ByteArray) : Option ByteArray := do
  let items ← argv.mapM fun a =>
    if h : a.size ≤ Protocol.Bounds.argvBytesMax then some (⟨a, h⟩ : Bytes Protocol.Bounds.argvBytesMax)
    else none
  if h : items.toArray.size ≤ Protocol.Bounds.argvBytesMax then
    let b := (Layout.codec Protocol.Bounds.argvBytesMax (by decide) Protocol.commandLayout).bytes
      (⟨items.toArray, h⟩, ())
    if b.size ≤ Protocol.Bounds.argvBytesMax then some b else none
  else none

/-- What one member command answered: its `CommandExit` code, stdout, stderr. -/
structure Reply where
  exit : Nat
  stdout : ByteArray
  stderr : ByteArray

/-- A reply body: the status byte, then `commandReplyLayout`. -/
def Reply.ofBody (body : ByteArray) : Except String Reply :=
  if body.size = 0 then .error "emptyReply"
  else if body[0]! ≠ Protocol.Status.ok.code then .error s!"status {body[0]!}"
  else
    match (Layout.codec Protocol.Bounds.frameBytesMax (by decide) Protocol.commandReplyLayout).decode
        (body.extract 1 body.size) with
    | .ok (e, o, r, ()) => .ok ⟨e.toNat, o.val, r.val⟩
    | .error _ => .error "replyUndecodable"

/-- Run one command through the member socket at `path`. -/
def command (path : String) (argv : List ByteArray) : IO (Except String Reply) := do
  let some p := commandPayload argv | return .error "argvPastBound"
  let r ← (do
      let c ← Conn.connect path memberMs.toUInt32
      c.writeAll (le32 (p.size + 1 + Protocol.versionBytes) ++ ByteArray.mk #[Protocol.Op.command.code] ++ Protocol.versioned p)
      readBody c.stream Protocol.Bounds.frameBytesMax).toBaseIO
  pure <| match r with
    | .error e => .error s!"io {e}"
    | .ok (.error e) => .error e
    | .ok (.ok body) => Reply.ofBody body

/-- How an ask ended. `notSent`: its frame never left in full, so keybroker made no call and the
meter is untouched; the ring may be asked about again. `answered` and `lost`: the ask is SPENT. -/
inductive AskEnd
  | notSent (why : String)
  | answered (a : Broker.Answer)
  | lost (why : String)

/-- One ask on the broker socket at `path`. -/
def ask (path : String) (a : Broker.Ask) : IO AskEnd := do
  let some p := Broker.Wire.encodeAsk a | return .notSent "askUnencodable"
  match ← (do
      let c ← Conn.connect path askMs.toUInt32
      c.writeAll (le32 p.size ++ p)
      pure c).toBaseIO with
  | .error e => return .notSent s!"io {e}"
  | .ok c =>
    match ← (readBody c.stream Broker.Bounds.frameMax).toBaseIO with
    | .error e => return .lost s!"io {e}"
    | .ok (.error e) => return .lost e
    | .ok (.ok body) =>
      match Broker.Wire.decodeAnswer body with
      | .ok ans => return .answered ans
      | .error _ => return .lost "answerUndecodable"

end Nanodregg.Hosting.Resident
