import Protocol.Frames
import Codec.Tag
import Codec.Deployed
import Kernel.Receive.Submit

/-!
# Protocol.Version — the frame wire's version, in the header of every request (PROTOCOL-87)

A request on either socket is `u32le len ‖ op ‖ version ‖ payload`: four bytes after the op byte,
`wireBytes`, before anything the op's payload holds. The answering side (`host serve`, `host follow`,
`nd --stdio`) reads them before it reads anything else of the frame, and a request whose four bytes
are not its own (or that has fewer than four after the op) is answered `refused wireVersion N
expected M` by name, N the four bytes the request carries (`none` when it has fewer) and M its own,
both as hex. Replies carry no version: a reply answers a request the server accepted at its own
version, and the one reply a request at another version receives, `refused ‖ text`, has the shape
every version shares (`Status.refused`'s byte and UTF-8).

THE VERSION IS COMPUTED, never edited (as `Codec.Tag`'s are): the first four bytes of the digest of
everything a frame's bytes mean. The op, status and step tables (names and bytes), the close reasons
and the child wire's hang-up byte, the frame bound, every payload's codec by its content-addressed
tag (`Tag.of`: the command, resume, custody answers, envelope, log and read replies, the step frames,
the refusal payloads), the deployed call, turn and World codecs a payload carries (submit and lookup
send a call, a log page carries turns and calls, a read page World bytes), and the kernel's refusal
code table (a recorded refusal answers by its name). A change to any of them moves `wireVersion`
by itself. What it cannot see: a meaning that changes under an unchanged shape (a refine's accepted
set, the same as `Codec.Tag`'s caveat), and a wire element not listed here; adding one is a line in
`wireMessage`.

Four bytes, not the digest: the version answers "are we speaking one wire", a question an honest
mismatch asks; an adversary can send anything it likes either way, and every field after the version
is checked on its own terms. Two wires that collide in 32 bits would decode each other's frames as
they decode a malformed frame today: by name, later.
-/

namespace Nanodregg.Protocol

open Nanodregg.Codec

/-- The domain of the wire stamp. -/
def domWire : String := "nanodregg/protocol/wire/v1"

/-- A list's entries, each length-prefixed (LEB128), so two lists encode alike only when equal. -/
def wireList (xs : List ByteArray) : ByteArray :=
  xs.foldl (fun b x => Stream.putVarint x.size b ++ x) (Stream.putVarint xs.length ByteArray.empty)

/-- `name=code` of a table row. -/
def wireRow (name : String) (code : Nat) : ByteArray := s!"{name}={code}".toUTF8

/-- What the wire stamp hashes (see the module doc for the list). -/
def wireMessage : ByteArray :=
  wireList [
    wireList (Op.all.map fun o => wireRow o.name o.code.toNat),
    wireList (Status.all.map fun s => wireRow (toString (repr s)) s.code.toNat),
    wireList (Step.all.map fun s => wireRow (toString (repr s)) s.code.toNat),
    wireList (CloseReason.all.map fun r => r.name.toUTF8),
    wireList (CustodyRefusal.all.map fun r => wireRow r.name r.code.toNat),
    wireRow "hangup" hangupCode.toNat,
    wireRow "frameBytesMax" Bounds.frameBytesMax,
    (Tag.of "protocol/socket-frame" socketFrame).bytes,
    (Tag.of "protocol/step" Step.frame).bytes,
    (Tag.of "protocol/command" commandFrame).bytes,
    (Tag.of "protocol/resume" resumeFrame).bytes,
    (Tag.of "protocol/sign-result" signResultFrame).bytes,
    (Tag.of "protocol/precommit-result" precommitResultFrame).bytes,
    (Tag.of "protocol/custody-refusal" custodyRefusalFrame).bytes,
    (Tag.of "protocol/envelope" envelopeFrame).bytes,
    (Tag.of "protocol/expired-refusal" expiredRefusalFrame).bytes,
    (Tag.of "protocol/log-reply" logReplyFrame).bytes,
    (Tag.of "protocol/read-reply" readReplyFrame).bytes,
    (Tag.of "kernel/call" (Codec.Kernel.call Deployed.digestCodec)).bytes,
    (Tag.of "kernel/turn" (Codec.Kernel.turn Deployed.digestCodec)).bytes,
    (Tag.of "kernel/world" Deployed.world).bytes,
    Kernel.Receive.codeTable.toUTF8]

/-- The wire stamp: the digest of `wireMessage`. -/
def wireStamp : Digest := Hash.digest domWire wireMessage

/-- How many bytes the version takes in a request's header. -/
def versionBytes : Nat := 4

/-- THE VERSION: the stamp's first `versionBytes` bytes, as they travel. -/
def wireBytes : ByteArray := wireStamp.bytes.extract 0 versionBytes

/-- The version a request's bytes after its op carry: their first `versionBytes`, or `none` when
there are fewer. -/
def versionOf? (b : ByteArray) : Option ByteArray :=
  if versionBytes ≤ b.size then some (b.extract 0 versionBytes) else none

/-- Lowercase hex of some bytes. -/
def wireHex (b : ByteArray) : String :=
  String.join (b.toList.map fun x =>
    let d := fun (n : Nat) => if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)
    String.ofList [d (x.toNat / 16), d (x.toNat % 16)])

/-- The refusal's text: `wireVersion N expected M` (N `none` for a request too short to carry one). -/
def wireRefusal (got : Option ByteArray) : String :=
  s!"wireVersion {(got.map wireHex).getD "none"} expected {wireHex wireBytes}"

/-- A request's bytes after its op, read for the version FIRST: the rest when it is ours, else the
refusal's text. Nothing after the version is looked at before this answers. -/
def unwire (b : ByteArray) : Except String ByteArray :=
  match versionOf? b with
  | some v => if v = wireBytes then .ok (b.extract versionBytes b.size) else .error (wireRefusal (some v))
  | none => .error (wireRefusal none)

/-- A request's bytes after its op, as a client sends them: the version, then the payload. -/
def versioned (p : ByteArray) : ByteArray := wireBytes ++ p

end Nanodregg.Protocol
