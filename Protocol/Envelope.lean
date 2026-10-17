/-
# Protocol.Envelope — the READ ENVELOPE: who may read the log, decided in Lean

`log` (and `read`) carry an envelope: the member, its follow grant, the height to read from, a
`validUntil` height, the member's current key and its signature over `Envelope.message`. The Host
answers only when `Envelope.check` accepts (`Protocol.Proofs.Envelope.check_ok_iff`): the member is
live and the key is its current one, the signature verifies, the follow grant's chain is live to a
root (`Receive.mayFollow`, PROTOCOL-3), and the World has not passed `validUntil`. A replayed
envelope re-reads at most what its signer may read, and only until `validUntil`.

Expiry is checked LAST, and `expired` states the writer's height (PROTOCOL-19): a member more than
a window behind the tip cannot know the height to sign for, so the Host tells it, and only it
(`Envelope.check_expired_authenticated`: the height reaches only the current key of a live member
whose follow grant is live). Follow re-signs once with `validUntil` = that height + window.
-/
import Kernel.Receive.Follow
import Protocol.Frames
import Protocol.Command.Text

namespace Nanodregg.Protocol

open Nanodregg.Kernel Nanodregg.Kernel.Receive

structure Envelope (D : Type) where
  member : D
  grant : D
  start : Nat
  validUntil : Nat
  key : ByteArray
  signature : ByteArray

/-- Why the Host refuses to serve a read. -/
inductive ReadRefusal
  | badEnvelope
  /-- not a live member, or not its current key -/
  | unknownKey
  | badSignature
  /-- the World is past the envelope's `validUntil`; the writer's height is stated -/
  | expired (height : Nat)
  | noFollowGrant
  deriving DecidableEq, Repr

/-- The refusal's name on the wire (law 7; `ReadRefusal.name_injective`). -/
def ReadRefusal.name : ReadRefusal → String
  | .badEnvelope => "badEnvelope" | .unknownKey => "unknownKey" | .badSignature => "badSignature"
  | .expired _ => "expired" | .noFollowGrant => "noFollowGrant"

def expiredName : ByteArray := "expired".toUTF8

/-- The refusal's payload in a `refused` reply: its name as UTF-8, except `expired`, which is
`expiredRefusalLayout` (the name, then the writer's height). -/
def ReadRefusal.payload : ReadRefusal → ByteArray
  | .expired h => expiredRefusalFrame.bytes (⟨expiredName, by decide⟩, h.toUInt64, ())
  | r => r.name.toUTF8

/-- The writer's height a refused `log` or `read` payload states, if it is `expired`'s. -/
def expiredHeight? (b : ByteArray) : Option Nat :=
  match expiredRefusalFrame.decode b with
  | .ok (n, h, ()) => if n.1 = expiredName then some h.toNat else none
  | .error _ => none

def domEnvelope : ByteArray := "nanodregg/protocol/read-envelope/v1".toUTF8

variable {D : Type} [Ord D] [DecidableEq D]

/-- What the member signs: the domain tag, then each field at its fixed width. -/
def Envelope.message (X : Ctx D) (member grant : D) (start validUntil : Nat) : ByteArray :=
  domEnvelope ++ X.env.bytes member ++ X.env.bytes grant ++ Text.u64 start ++ Text.u64 validUntil

/-- The member's current key, if `member` is a live member. -/
def currentKey (w : World D) (member : D) : Option ByteArray :=
  match w.live member with
  | some m => if m.kind = kindMember then m.slots.get slotKey else none
  | none => none

def Envelope.check (X : Ctx D) (w : World D) (e : Envelope D) : Except ReadRefusal Unit := do
  req (currentKey w e.member = some e.key) .unknownKey
  req (X.verify e.key (Envelope.message X e.member e.grant e.start e.validUntil) e.signature) .badSignature
  req (mayFollow X w e.member e.grant) .noFollowGrant
  req (w.height ≤ e.validUntil) (.expired w.height)

def Envelope.bytes (X : Ctx D) (e : Envelope D) : Option ByteArray := do
  let f := Text.fit Bounds.frameBytesMax
  pure (envelopeFrame.bytes (← f (X.env.bytes e.member), ← f (X.env.bytes e.grant),
    ← f (Text.u64 e.start), ← f (Text.u64 e.validUntil), ← f e.key, ← f e.signature, ()))

def Envelope.ofBytes (X : Ctx D) (b : ByteArray) : Option (Envelope D) :=
  match envelopeFrame.decode b with
  | .ok (m, g, s, v, k, sig, ()) => do
      pure { member := ← X.digestOf m.1, grant := ← X.digestOf g.1, start := ← Text.ofU64 s.1,
             validUntil := ← Text.ofU64 v.1, key := k.1, signature := sig.1 }
  | .error _ => none

end Nanodregg.Protocol
