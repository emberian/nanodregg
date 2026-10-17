/-
# Protocol.Proofs.Envelope — the read gate, and its refusal names
-/
import Protocol.Envelope
import Protocol.Proofs.Frames
import Kernel.Proofs.RootedDeployed

namespace Nanodregg.Protocol

open Nanodregg.Codec Nanodregg.Kernel Nanodregg.Kernel.Receive

/-- Names up to the argument: two refusals with one name are the same refusal, or both `expired`
(at heights the name does not show). -/
theorem ReadRefusal.name_injective : ∀ a b : ReadRefusal, a.name = b.name →
    a = b ∨ ∃ h h', a = .expired h ∧ b = .expired h' := by
  intro a b; cases a <;> cases b <;> simp [ReadRefusal.name]

/-- Every refusal but `expired` travels as its name. -/
theorem ReadRefusal.payload_name : ∀ r : ReadRefusal, (∀ h, r ≠ .expired h) → r.payload = r.name.toUTF8
  | .wrongWorld, _ | .badEnvelope, _ | .unknownKey, _ | .badSignature, _ | .noFollowGrant, _
  | .notYet, _ | .wideWindow, _ => rfl
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
  | .wrongWorld, _ | .badEnvelope, _ | .unknownKey, _ | .badSignature, _ | .noFollowGrant, _
  | .notYet, _ | .wideWindow, _ =>
    expiredHeight?_of_head (by decide)
  | .expired h, hr => absurd rfl (hr h)

variable {D : Type} [Ord D] [DecidableEq D]

/-- The Host serves a read exactly when the envelope names this World, its window is at most `windowMax` wide, the
member's current key signed it, the member's follow grant is live to a root, and the World's height
is inside the window. -/
theorem Envelope.check_ok_iff (X : Ctx D) (w : World D) (e : Envelope D) :
    Envelope.check X w e = .ok () ↔
      e.world = w.origin ∧ e.validUntil ≤ e.notBefore + Kernel.Bounds.windowMax ∧
      currentKey X.env w e.member = some e.key ∧
      X.verify e.key (Envelope.message X e.world e.member e.grant e.start e.notBefore e.validUntil) e.signature = true ∧
      mayFollow X w e.member e.grant = true ∧ e.notBefore ≤ w.height ∧ w.height ≤ e.validUntil := by
  simp only [Envelope.check, bind, Except.bind, req]
  generalize Envelope.message X e.world e.member e.grant e.start e.notBefore e.validUntil = msg
  by_cases hw : e.world = w.origin <;>
  by_cases h0 : e.validUntil ≤ e.notBefore + Kernel.Bounds.windowMax <;>
  by_cases h1 : currentKey X.env w e.member = some e.key <;>
  by_cases h2 : X.verify e.key msg e.signature = true <;>
  by_cases h3 : mayFollow X w e.member e.grant = true <;>
  by_cases h5 : e.notBefore ≤ w.height <;>
  by_cases h4 : w.height ≤ e.validUntil <;>
  simp [hw, h0, h1, h2, h3, h4, h5]

/-- One signature reads inside one window of heights, whatever height anyone stated to its signer
(PROTOCOL-27): an accepted envelope has `notBefore ≤ height ≤ validUntil ≤ notBefore + windowMax`. -/
theorem Envelope.check_ok_within {X : Ctx D} {w : World D} {e : Envelope D}
    (h : Envelope.check X w e = .ok ()) :
    e.notBefore ≤ w.height ∧ w.height ≤ e.validUntil ∧ e.validUntil ≤ e.notBefore + Kernel.Bounds.windowMax := by
  obtain ⟨-, h0, -, -, -, h5, h4⟩ := (Envelope.check_ok_iff X w e).mp h
  exact ⟨h5, h4, h0⟩

/-- `notYet` reaches only an authenticated reader, like `expired`: the current key of a live member
that signed the envelope and whose follow grant is live; the World is below `notBefore`. -/
theorem Envelope.check_notYet_authenticated (X : Ctx D) (w : World D) (e : Envelope D)
    (he : Envelope.check X w e = .error .notYet) :
      e.world = w.origin ∧ currentKey X.env w e.member = some e.key ∧
      X.verify e.key (Envelope.message X e.world e.member e.grant e.start e.notBefore e.validUntil) e.signature = true ∧
      mayFollow X w e.member e.grant = true ∧ w.height < e.notBefore := by
  simp only [Envelope.check, bind, Except.bind, req] at he ⊢
  generalize Envelope.message X e.world e.member e.grant e.start e.notBefore e.validUntil = msg at he ⊢
  by_cases hw : e.world = w.origin <;>
  by_cases h0 : e.validUntil ≤ e.notBefore + Kernel.Bounds.windowMax <;>
  by_cases h1 : currentKey X.env w e.member = some e.key <;>
  by_cases h2 : X.verify e.key msg e.signature = true <;>
  by_cases h3 : mayFollow X w e.member e.grant = true <;>
  by_cases h5 : e.notBefore ≤ w.height <;>
  by_cases h4 : w.height ≤ e.validUntil <;>
  simp_all <;> omega

/-- The writer's height reaches only an authenticated reader: `expired` is refused only to the
current key of a live member that signed the envelope and whose follow grant is live, and the
height it states is the World's. A stranger, a revoked member, a forged signature learn nothing. -/
theorem Envelope.check_expired_authenticated (X : Ctx D) (w : World D) (e : Envelope D) (h : Nat)
    (he : Envelope.check X w e = .error (.expired h)) :
      e.world = w.origin ∧ e.notBefore ≤ w.height ∧ currentKey X.env w e.member = some e.key ∧
      X.verify e.key (Envelope.message X e.world e.member e.grant e.start e.notBefore e.validUntil) e.signature = true ∧
      mayFollow X w e.member e.grant = true ∧ e.validUntil < w.height ∧ h = w.height := by
  simp only [Envelope.check, bind, Except.bind, req] at he ⊢
  generalize Envelope.message X e.world e.member e.grant e.start e.notBefore e.validUntil = msg at he ⊢
  by_cases hw : e.world = w.origin <;>
  by_cases h0 : e.validUntil ≤ e.notBefore + Kernel.Bounds.windowMax <;>
  by_cases h1 : currentKey X.env w e.member = some e.key <;>
  by_cases h2 : X.verify e.key msg e.signature = true <;>
  by_cases h3 : mayFollow X w e.member e.grant = true <;>
  by_cases h5 : e.notBefore ≤ w.height <;>
  by_cases h4 : w.height ≤ e.validUntil <;>
  simp_all <;> omega

/-- The width bound is checked FIRST: an envelope wider than `windowMax` is refused `wideWindow`,
whoever signed it (it states nothing about the member, so a stranger learns nothing from it). -/
theorem Envelope.check_wideWindow (X : Ctx D) (w : World D) (e : Envelope D)
    (hw : e.world = w.origin) (h : e.notBefore + Kernel.Bounds.windowMax < e.validUntil) :
    Envelope.check X w e = .error .wideWindow := by
  simp [Envelope.check, bind, Except.bind, req, hw.symm, Nat.not_le.mpr h]

/-- The World binding is checked FIRST (KERNEL-24): an envelope that names another World than this
one is refused `wrongWorld`, whoever signed it and whatever else it carries — never `unknownKey` or
`badSignature`, the names a replay against a clone with the same founders would otherwise get. -/
theorem Envelope.check_wrongWorld (X : Ctx D) (w : World D) (e : Envelope D) (h : e.world ≠ w.origin) :
    Envelope.check X w e = .error .wrongWorld := by
  simp [Envelope.check, bind, Except.bind, req, h]

/-- The converse of `check_notYet_authenticated`: an authenticated reader whose window is in
bounds and starts above the World's height is refused `notYet`, by that name and no other. -/
theorem Envelope.check_notYet_of (X : Ctx D) (w : World D) (e : Envelope D)
    (hw : e.world = w.origin) (h0 : e.validUntil ≤ e.notBefore + Kernel.Bounds.windowMax)
    (h1 : currentKey X.env w e.member = some e.key)
    (h2 : X.verify e.key (Envelope.message X e.world e.member e.grant e.start e.notBefore e.validUntil) e.signature = true)
    (h3 : mayFollow X w e.member e.grant = true) (h5 : w.height < e.notBefore) :
    Envelope.check X w e = .error .notYet := by
  simp [Envelope.check, bind, Except.bind, req, hw.symm, h0, h1, h2, h3, Nat.not_le.mpr h5]

theorem Text.u64_inj {n m : Nat} (hn : n < 2 ^ 64) (hm : m < 2 ^ 64) (h : Text.u64 n = Text.u64 m) :
    n = m := by
  have := Stream.bytes_injective Stream.u64_lawful h
  have h1 := congrArg UInt64.toNat this
  simpa [Nat.toUInt64, UInt64.toNat_ofNat_of_lt' hn, UInt64.toNat_ofNat_of_lt' hm] using h1

theorem Text.u64_data_size (n : Nat) : (Text.u64 n).data.size = 8 := Stream.u64_size n.toUInt64

omit [Ord D] [DecidableEq D] in
/-- The signature binds the heights (PROTOCOL-27): two envelope messages of one member and grant
are equal only if their `start`, `notBefore` and `validUntil` are, so a signature over one window
is not a signature over another. -/
theorem Envelope.message_heights_inj {X : Ctx D} {o m g : D} {s nb v s' nb' v' : Nat}
    (hs : s < 2 ^ 64) (hnb : nb < 2 ^ 64) (hv : v < 2 ^ 64)
    (hs' : s' < 2 ^ 64) (hnb' : nb' < 2 ^ 64) (hv' : v' < 2 ^ 64)
    (h : Envelope.message X o m g s nb v = Envelope.message X o m g s' nb' v') :
    s = s' ∧ nb = nb' ∧ v = v' := by
  have hd := congrArg ByteArray.data h
  simp only [Envelope.message, ByteArray.data_append, Array.append_assoc] at hd
  have hd := (Array.append_right_inj _).mp hd
  have hd := (Array.append_right_inj _).mp hd
  have hd := (Array.append_right_inj _).mp hd
  have hd := (Array.append_right_inj _).mp hd
  obtain ⟨e1, hd⟩ := Array.append_inj hd (by rw [Text.u64_data_size, Text.u64_data_size])
  obtain ⟨e2, e3⟩ := Array.append_inj hd (by rw [Text.u64_data_size, Text.u64_data_size])
  exact ⟨Text.u64_inj hs hs' (ByteArray.ext e1), Text.u64_inj hnb hnb' (ByteArray.ext e2),
    Text.u64_inj hv hv' (ByteArray.ext e3)⟩

omit [DecidableEq D] in
/-- The signature binds EVERY field it covers (PROTOCOL-29's named gap, closed with KERNEL-37's
`Env.Lawful`): under a lawful `Env` (one digest size, injective bytes), two envelope messages
are equal only if their world, member, grant, start, notBefore and validUntil are. A signature
over one World's envelope is not a signature over another's. -/
theorem Envelope.message_inj {X : Ctx D} {n : Nat} (hE : X.env.Lawful n) {o m g o' m' g' : D}
    {s nb v s' nb' v' : Nat}
    (hs : s < 2 ^ 64) (hnb : nb < 2 ^ 64) (hv : v < 2 ^ 64)
    (hs' : s' < 2 ^ 64) (hnb' : nb' < 2 ^ 64) (hv' : v' < 2 ^ 64)
    (h : Envelope.message X o m g s nb v = Envelope.message X o' m' g' s' nb' v') :
    o = o' ∧ m = m' ∧ g = g' ∧ s = s' ∧ nb = nb' ∧ v = v' := by
  have sz : ∀ d : D, (X.env.bytes d).data.size = n := fun d => hE.size d
  have hd := congrArg ByteArray.data h
  simp only [Envelope.message, ByteArray.data_append, Array.append_assoc] at hd
  have hd := (Array.append_right_inj _).mp hd
  obtain ⟨eo, hd⟩ := Array.append_inj hd (by rw [sz, sz])
  obtain ⟨em, hd⟩ := Array.append_inj hd (by rw [sz, sz])
  obtain ⟨eg, hd⟩ := Array.append_inj hd (by rw [sz, sz])
  obtain ⟨e1, hd⟩ := Array.append_inj hd (by rw [Text.u64_data_size, Text.u64_data_size])
  obtain ⟨e2, e3⟩ := Array.append_inj hd (by rw [Text.u64_data_size, Text.u64_data_size])
  exact ⟨hE.bytes_eq (ByteArray.ext eo), hE.bytes_eq (ByteArray.ext em), hE.bytes_eq (ByteArray.ext eg),
    Text.u64_inj hs hs' (ByteArray.ext e1), Text.u64_inj hnb hnb' (ByteArray.ext e2),
    Text.u64_inj hv hv' (ByteArray.ext e3)⟩

/-- At the deployed `Env`, with no premise on it (`Receive.deployed_lawful`): an envelope signature
binds the World's origin bytes and every other field. -/
theorem Envelope.deployed_message_inj {program : Program Codec.Digest} {o m g o' m' g' : Codec.Digest}
    {s nb v s' nb' v' : Nat}
    (hs : s < 2 ^ 64) (hnb : nb < 2 ^ 64) (hv : v < 2 ^ 64)
    (hs' : s' < 2 ^ 64) (hnb' : nb' < 2 ^ 64) (hv' : v' < 2 ^ 64)
    (h : Envelope.message (Codec.Deployed.ctx program) o m g s nb v =
      Envelope.message (Codec.Deployed.ctx program) o' m' g' s' nb' v') :
    o = o' ∧ m = m' ∧ g = g' ∧ s = s' ∧ nb = nb' ∧ v = v' :=
  Envelope.message_inj Receive.deployed_lawful hs hnb hv hs' hnb' hv' h

end Nanodregg.Protocol
