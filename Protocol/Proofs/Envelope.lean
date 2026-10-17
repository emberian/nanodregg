/-
# Protocol.Proofs.Envelope — the read gate, and its refusal names
-/
import Protocol.Envelope
import Protocol.Proofs.Frames

namespace Nanodregg.Protocol

open Nanodregg.Codec Nanodregg.Kernel Nanodregg.Kernel.Receive

/-- Names up to the argument: two refusals with one name are the same refusal, or both `expired`
(at heights the name does not show). -/
theorem ReadRefusal.name_injective : ∀ a b : ReadRefusal, a.name = b.name →
    a = b ∨ ∃ h h', a = .expired h ∧ b = .expired h' := by
  intro a b; cases a <;> cases b <;> simp [ReadRefusal.name]

/-- Every refusal but `expired` travels as its name. -/
theorem ReadRefusal.payload_name : ∀ r : ReadRefusal, (∀ h, r ≠ .expired h) → r.payload = r.name.toUTF8
  | .badEnvelope, _ | .unknownKey, _ | .badSignature, _ | .noFollowGrant, _ => rfl
  | .expired h, hr => absurd rfl (hr h)

/-- An `expired` payload states the writer's height, which `expiredHeight?` reads back. -/
theorem expiredHeight?_payload (h : Nat) (hh : h < 2 ^ 64) :
    expiredHeight? (ReadRefusal.expired h).payload = some h := by
  simp only [expiredHeight?, ReadRefusal.payload, Stream.decode_bytes expiredRefusalFrame_lawful]
  simp [UInt64.toNat_ofNat_of_lt' hh]

/-- What `expiredHeight?` accepts is an `expired` payload, byte for byte (the frame is canonical). -/
theorem expiredHeight?_eq_some {b : ByteArray} {h : Nat} (hb : expiredHeight? b = some h) :
    h < 2 ^ 64 ∧ b = (ReadRefusal.expired h).payload := by
  unfold expiredHeight? at hb
  split at hb
  · rename_i n v hd
    split at hb
    · rename_i hn
      cases hb
      have e := (Stream.decode_eq_ok_iff expiredRefusalFrame_lawful).mp hd
      refine ⟨v.toNat_lt, ?_⟩
      rw [e]
      simp only [ReadRefusal.payload, UInt64.ofNat_toNat]
      congr
      exact Subtype.ext hn
    · cases hb
  · cases hb

/-- An `expired` payload begins with the byte 7 (the name's length, little-endian). -/
theorem expired_payload_head (h : Nat) : (ReadRefusal.expired h).payload[0]? = some 7 := by
  show ((Stream.product (Stream.bytesOf Bounds.frameBytesMax (by decide)) (Layout.codec Bounds.frameBytesMax (by decide) [.u64 "height"])).bytes _)[0]? = _
  rw [Stream.product_bytes (Layout.codec_lawful _ _ _), Stream.bytesOf_bytes, Stream.u32_bytes]
  rfl

/-- No name the Host refuses by is mistaken for `expired` (HOST-5's ask): a payload whose first
byte is not 7 (every name: names are identifiers) states no height. -/
theorem expiredHeight?_of_head {b : ByteArray} (hb : b[0]? ≠ some 7) : expiredHeight? b = none := by
  cases e : expiredHeight? b with
  | none => rfl
  | some h =>
    obtain ⟨_, rfl⟩ := expiredHeight?_eq_some e
    exact absurd (expired_payload_head h) hb

/-- The names `ReadRefusal` sends as UTF-8 state no height. -/
theorem expiredHeight?_name : ∀ r : ReadRefusal, (∀ h, r ≠ .expired h) → expiredHeight? r.payload = none
  | .badEnvelope, _ | .unknownKey, _ | .badSignature, _ | .noFollowGrant, _ =>
    expiredHeight?_of_head (by decide)
  | .expired h, hr => absurd rfl (hr h)

variable {D : Type} [Ord D] [DecidableEq D]

/-- The Host serves a read exactly when the member's current key signed the envelope, the
member's follow grant is live to a root, and it has not expired. -/
theorem Envelope.check_ok_iff (X : Ctx D) (w : World D) (e : Envelope D) :
    Envelope.check X w e = .ok () ↔
      currentKey w e.member = some e.key ∧
      X.verify e.key (Envelope.message X e.member e.grant e.start e.validUntil) e.signature = true ∧
      mayFollow X w e.member e.grant = true ∧ w.height ≤ e.validUntil := by
  simp only [Envelope.check, bind, Except.bind, req]
  by_cases h1 : currentKey w e.member = some e.key <;>
  by_cases h2 : X.verify e.key (Envelope.message X e.member e.grant e.start e.validUntil) e.signature = true <;>
  by_cases h3 : mayFollow X w e.member e.grant = true <;>
  by_cases h4 : w.height ≤ e.validUntil <;>
  simp [h1, h2, h3, h4]

/-- The writer's height reaches only an authenticated reader: `expired` is refused only to the
current key of a live member that signed the envelope and whose follow grant is live, and the
height it states is the World's. A stranger, a revoked member, a forged signature learn nothing. -/
theorem Envelope.check_expired_authenticated (X : Ctx D) (w : World D) (e : Envelope D) (h : Nat)
    (he : Envelope.check X w e = .error (.expired h)) :
      currentKey w e.member = some e.key ∧
      X.verify e.key (Envelope.message X e.member e.grant e.start e.validUntil) e.signature = true ∧
      mayFollow X w e.member e.grant = true ∧ e.validUntil < w.height ∧ h = w.height := by
  simp only [Envelope.check, bind, Except.bind, req] at he
  by_cases h1 : currentKey w e.member = some e.key <;>
  by_cases h2 : X.verify e.key (Envelope.message X e.member e.grant e.start e.validUntil) e.signature = true <;>
  by_cases h3 : mayFollow X w e.member e.grant = true <;>
  by_cases h4 : w.height ≤ e.validUntil <;>
  simp_all <;> omega

end Nanodregg.Protocol
