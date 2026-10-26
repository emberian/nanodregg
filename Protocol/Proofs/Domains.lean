/-
# Protocol.Proofs.Domains — every message a member key signs begins with its own domain (KERNEL-42)

A member key signs seven shapes, and a World's certifier an eighth (`Head.certifyMessage`, `Head.domCertify`, PROTOCOL-76, never a member's): a call (`Receive.Ctx.callMessage`, `domCall`), a possession
proof (`Receive.possessionMessage`, `tagPossession`), a read envelope (`Envelope.message`,
`domEnvelope`), `init`'s identity probe (`Command.whoami`, a constant), an invitation
(`Invite.message`, `domInvite`, PROTOCOL-42), a cancel (`Receive.Ctx.cancelMessage`,
`domCancel`, KERNEL-60; PROTOCOL-60) and a head attestation (`Head.message`, `Head.domHead`,
PROTOCOL-74). Each pair of domains
differs at a byte both hold, so no message of one shape is a message of another, whatever follows
the domain: a signature made for one is never one over another, with no hash premise. An observer
custody that signs only messages beginning with `domEnvelope` (HOSTING-17 §7, CLIENT-22) therefore
never signs a call, a possession proof, a probe, an invitation, a cancel or an attestation
(`call_not_envelope`, `possession_not_envelope`, `whoami_not_envelope`, `invite_not_envelope`,
`cancel_not_envelope`, `head_not_envelope`), and
a cancel signature is never a call's (`cancel_not_call`): a member's cancel of one call cannot be
replayed as a signed call, nor a signed call as a cancel.
-/
import Protocol.Command.Machine

namespace Nanodregg.Protocol

open Nanodregg.Kernel Nanodregg.Kernel.Receive

/-- Two byte strings that differ at a byte both hold begin no common string: whatever follows
them, the results differ. -/
theorem append_ne_of_byte {a b r s : ByteArray} {i : Nat} (ha : i < a.size) (hb : i < b.size)
    (h : a[i] ≠ b[i]) : a ++ r ≠ b ++ s := by
  intro e
  apply h
  have h1 : i < (a ++ r).size := by rw [ByteArray.size_append]; omega
  have h2 : i < (b ++ s).size := by rw [ByteArray.size_append]; omega
  have k : (a ++ r)[i]'h1 = (b ++ s)[i]'h2 := by simp only [e]
  rwa [ByteArray.getElem_append_left ha, ByteArray.getElem_append_left hb] at k

/-! ## The six pairs of domains (`nanodregg/` is common; byte 10 or 17 or 19 differs) -/

theorem call_envelope_disjoint (r s : ByteArray) : domCall ++ r ≠ domEnvelope ++ s :=
  append_ne_of_byte (i := 10) (by decide) (by decide) (by decide)

theorem call_possession_disjoint (r s : ByteArray) : domCall ++ r ≠ tagPossession ++ s :=
  append_ne_of_byte (i := 17) (by decide) (by decide) (by decide)

theorem call_whoami_disjoint (r s : ByteArray) : domCall ++ r ≠ Command.whoami ++ s :=
  append_ne_of_byte (i := 10) (by decide) (by decide) (by decide)

theorem possession_envelope_disjoint (r s : ByteArray) : tagPossession ++ r ≠ domEnvelope ++ s :=
  append_ne_of_byte (i := 10) (by decide) (by decide) (by decide)

theorem possession_whoami_disjoint (r s : ByteArray) : tagPossession ++ r ≠ Command.whoami ++ s :=
  append_ne_of_byte (i := 10) (by decide) (by decide) (by decide)

theorem envelope_whoami_disjoint (r s : ByteArray) : domEnvelope ++ r ≠ Command.whoami ++ s :=
  append_ne_of_byte (i := 19) (by decide) (by decide) (by decide)

/-! ## The signed messages -/

variable {D : Type}

/-- **No call message begins with the envelope domain**: an envelope-only custody never signs a
call or a rotation (`signNext` signs a `callMessage` too). -/
theorem call_not_envelope (X : Ctx D) (u : Unsigned D) (r : ByteArray) :
    domEnvelope ++ r ≠ X.callMessage u :=
  fun h => call_envelope_disjoint (X.unsignedBytes u) r (by simp only [Ctx.callMessage] at h; exact h.symm)

/-- **A read envelope's message is never a call's**, for every field of either. -/
theorem envelope_call_disjoint (X : Ctx D) (u : Unsigned D) (world member grant : D)
    (start notBefore validUntil : Nat) :
    Envelope.message X world member grant start notBefore validUntil ≠ X.callMessage u := by
  unfold Envelope.message
  simp only [ByteArray.append_assoc]
  exact call_not_envelope X u _

theorem possession_not_envelope (X : Ctx D) (sponsor next : D) (key r : ByteArray) :
    domEnvelope ++ r ≠ possessionMessage X sponsor next key := by
  unfold possessionMessage
  simp only [ByteArray.append_assoc]
  exact fun h => possession_envelope_disjoint _ r h.symm

theorem whoami_not_envelope (r : ByteArray) : domEnvelope ++ r ≠ Command.whoami := by
  intro h
  exact envelope_whoami_disjoint r ByteArray.empty (by rw [ByteArray.append_empty]; exact h)

/-- A call's message is never a possession proof's. -/
theorem call_not_possession (X : Ctx D) (u : Unsigned D) (sponsor next : D) (key : ByteArray) :
    X.callMessage u ≠ possessionMessage X sponsor next key := by
  unfold Ctx.callMessage possessionMessage
  simp only [ByteArray.append_assoc]
  exact call_possession_disjoint _ _

/-- A call's message is never the identity probe. -/
theorem call_not_whoami (X : Ctx D) (u : Unsigned D) : X.callMessage u ≠ Command.whoami := by
  intro h
  exact call_whoami_disjoint (X.unsignedBytes u) ByteArray.empty
    (by rw [ByteArray.append_empty]; exact h)

/-! ## The invitation's domain against the other four (byte 10 or 19 differs) -/

theorem invite_call_disjoint (r s : ByteArray) : Invite.domInvite ++ r ≠ domCall ++ s :=
  append_ne_of_byte (i := 10) (by decide) (by decide) (by decide)

theorem invite_possession_disjoint (r s : ByteArray) : Invite.domInvite ++ r ≠ tagPossession ++ s :=
  append_ne_of_byte (i := 10) (by decide) (by decide) (by decide)

theorem invite_envelope_disjoint (r s : ByteArray) : Invite.domInvite ++ r ≠ domEnvelope ++ s :=
  append_ne_of_byte (i := 19) (by decide) (by decide) (by decide)

theorem invite_whoami_disjoint (r s : ByteArray) : Invite.domInvite ++ r ≠ Command.whoami ++ s :=
  append_ne_of_byte (i := 19) (by decide) (by decide) (by decide)

/-- **No invitation message begins with the envelope domain**: an envelope-only custody never
signs an invitation. -/
theorem invite_not_envelope (u r : ByteArray) : domEnvelope ++ r ≠ Invite.message u :=
  fun h => invite_envelope_disjoint u r h.symm

/-- **An invitation's message is never a call's**: a signed invitation is never a signed call. -/
theorem invite_not_call (X : Ctx D) (v : Unsigned D) (u : ByteArray) : Invite.message u ≠ X.callMessage v :=
  invite_call_disjoint u (X.unsignedBytes v)

theorem invite_not_possession (X : Ctx D) (sponsor next : D) (key u : ByteArray) :
    Invite.message u ≠ possessionMessage X sponsor next key := by
  unfold possessionMessage
  simp only [ByteArray.append_assoc]
  exact invite_possession_disjoint _ _

/-! ## The cancel's domain against the other five (KERNEL-60; byte 19, 17 or 10 differs) -/

theorem cancel_call_disjoint (r s : ByteArray) : domCancel ++ r ≠ domCall ++ s :=
  append_ne_of_byte (i := 19) (by decide) (by decide) (by decide)

theorem cancel_possession_disjoint (r s : ByteArray) : domCancel ++ r ≠ tagPossession ++ s :=
  append_ne_of_byte (i := 17) (by decide) (by decide) (by decide)

theorem cancel_envelope_disjoint (r s : ByteArray) : domCancel ++ r ≠ domEnvelope ++ s :=
  append_ne_of_byte (i := 10) (by decide) (by decide) (by decide)

theorem cancel_whoami_disjoint (r s : ByteArray) : domCancel ++ r ≠ Command.whoami ++ s :=
  append_ne_of_byte (i := 10) (by decide) (by decide) (by decide)

theorem cancel_invite_disjoint (r s : ByteArray) : domCancel ++ r ≠ Invite.domInvite ++ s :=
  append_ne_of_byte (i := 10) (by decide) (by decide) (by decide)

/-- **No cancel message begins with the envelope domain**: an envelope-only custody never signs a
cancel. -/
theorem cancel_not_envelope (X : Ctx D) (c : Call D) (r : ByteArray) :
    domEnvelope ++ r ≠ X.cancelMessage c :=
  fun h => cancel_envelope_disjoint (X.env.bytes (txIdOf X c)) r (by simp only [Ctx.cancelMessage] at h; exact h.symm)

/-- **A cancel's message is never a call's**: a cancel signature is never a call signature, for
every call either names. -/
theorem cancel_not_call (X : Ctx D) (c : Call D) (u : Unsigned D) : X.cancelMessage c ≠ X.callMessage u := by
  unfold Ctx.cancelMessage Ctx.callMessage
  exact cancel_call_disjoint _ _

theorem cancel_not_possession (X : Ctx D) (c : Call D) (sponsor next : D) (key : ByteArray) :
    X.cancelMessage c ≠ possessionMessage X sponsor next key := by
  unfold Ctx.cancelMessage possessionMessage
  simp only [ByteArray.append_assoc]
  exact cancel_possession_disjoint _ _

theorem cancel_not_whoami (X : Ctx D) (c : Call D) : X.cancelMessage c ≠ Command.whoami := by
  intro h
  exact cancel_whoami_disjoint (X.env.bytes (txIdOf X c)) ByteArray.empty
    (by rw [ByteArray.append_empty]; exact h)

theorem cancel_not_invite (X : Ctx D) (c : Call D) (u : ByteArray) : X.cancelMessage c ≠ Invite.message u :=
  fun h => cancel_invite_disjoint _ u h

/-! ## The head attestation's domain against the other six (PROTOCOL-74; byte 10 or 19 differs) -/

theorem head_call_disjoint (r s : ByteArray) : Head.domHead ++ r ≠ domCall ++ s :=
  append_ne_of_byte (i := 10) (by decide) (by decide) (by decide)

theorem head_possession_disjoint (r s : ByteArray) : Head.domHead ++ r ≠ tagPossession ++ s :=
  append_ne_of_byte (i := 10) (by decide) (by decide) (by decide)

theorem head_cancel_disjoint (r s : ByteArray) : Head.domHead ++ r ≠ domCancel ++ s :=
  append_ne_of_byte (i := 10) (by decide) (by decide) (by decide)

theorem head_envelope_disjoint (r s : ByteArray) : Head.domHead ++ r ≠ domEnvelope ++ s :=
  append_ne_of_byte (i := 19) (by decide) (by decide) (by decide)

theorem head_whoami_disjoint (r s : ByteArray) : Head.domHead ++ r ≠ Command.whoami ++ s :=
  append_ne_of_byte (i := 19) (by decide) (by decide) (by decide)

theorem head_invite_disjoint (r s : ByteArray) : Head.domHead ++ r ≠ Invite.domInvite ++ s :=
  append_ne_of_byte (i := 19) (by decide) (by decide) (by decide)

/-- **No attestation message begins with the envelope domain**: an envelope-only custody never
attests a head. -/
theorem head_not_envelope (u r : ByteArray) : domEnvelope ++ r ≠ Head.message u :=
  fun h => head_envelope_disjoint u r h.symm

/-- **An attestation's message is never a call's**: a signed head is never a signed call. -/
theorem head_not_call (X : Ctx D) (v : Unsigned D) (u : ByteArray) : Head.message u ≠ X.callMessage v :=
  head_call_disjoint u (X.unsignedBytes v)

theorem head_not_possession (X : Ctx D) (sponsor next : D) (key u : ByteArray) :
    Head.message u ≠ possessionMessage X sponsor next key := by
  unfold possessionMessage
  simp only [ByteArray.append_assoc]
  exact head_possession_disjoint _ _

theorem head_not_whoami (u : ByteArray) : Head.message u ≠ Command.whoami := by
  intro h
  exact head_whoami_disjoint u ByteArray.empty (by rw [ByteArray.append_empty]; exact h)

theorem head_not_invite (u v : ByteArray) : Head.message u ≠ Invite.message v :=
  head_invite_disjoint u v

theorem head_not_cancel (X : Ctx D) (c : Call D) (u : ByteArray) : Head.message u ≠ X.cancelMessage c := by
  unfold Ctx.cancelMessage
  exact head_cancel_disjoint _ _

/-! ## The certificate's domain against the other seven (PROTOCOL-76; byte 10 or 19 differs) -/

theorem certify_call_disjoint (r s : ByteArray) : Head.domCertify ++ r ≠ domCall ++ s :=
  append_ne_of_byte (i := 10) (by decide) (by decide) (by decide)

theorem certify_possession_disjoint (r s : ByteArray) : Head.domCertify ++ r ≠ tagPossession ++ s :=
  append_ne_of_byte (i := 10) (by decide) (by decide) (by decide)

theorem certify_cancel_disjoint (r s : ByteArray) : Head.domCertify ++ r ≠ domCancel ++ s :=
  append_ne_of_byte (i := 10) (by decide) (by decide) (by decide)

theorem certify_envelope_disjoint (r s : ByteArray) : Head.domCertify ++ r ≠ domEnvelope ++ s :=
  append_ne_of_byte (i := 19) (by decide) (by decide) (by decide)

theorem certify_whoami_disjoint (r s : ByteArray) : Head.domCertify ++ r ≠ Command.whoami ++ s :=
  append_ne_of_byte (i := 19) (by decide) (by decide) (by decide)

theorem certify_invite_disjoint (r s : ByteArray) : Head.domCertify ++ r ≠ Invite.domInvite ++ s :=
  append_ne_of_byte (i := 19) (by decide) (by decide) (by decide)

theorem certify_head_disjoint (r s : ByteArray) : Head.domCertify ++ r ≠ Head.domHead ++ s :=
  append_ne_of_byte (i := 19) (by decide) (by decide) (by decide)

/-- **No certificate message begins with the envelope domain**: an envelope-only custody never
certifies a head. -/
theorem certify_not_envelope (u r : ByteArray) : domEnvelope ++ r ≠ Head.certifyMessage u :=
  fun h => certify_envelope_disjoint u r h.symm

/-- **A certificate is never a member's attestation, nor an attestation a certificate**: what the
World's certifier signs and what one member signs never share a message, whatever key signs. -/
theorem certify_not_head (u v : ByteArray) : Head.certifyMessage u ≠ Head.message v :=
  certify_head_disjoint u v

theorem certify_not_call (X : Ctx D) (v : Unsigned D) (u : ByteArray) :
    Head.certifyMessage u ≠ X.callMessage v :=
  certify_call_disjoint u (X.unsignedBytes v)

theorem certify_not_possession (X : Ctx D) (sponsor next : D) (key u : ByteArray) :
    Head.certifyMessage u ≠ possessionMessage X sponsor next key := by
  unfold possessionMessage
  simp only [ByteArray.append_assoc]
  exact certify_possession_disjoint _ _

theorem certify_not_whoami (u : ByteArray) : Head.certifyMessage u ≠ Command.whoami := by
  intro h
  exact certify_whoami_disjoint u ByteArray.empty (by rw [ByteArray.append_empty]; exact h)

theorem certify_not_invite (u v : ByteArray) : Head.certifyMessage u ≠ Invite.message v :=
  certify_invite_disjoint u v

theorem certify_not_cancel (X : Ctx D) (c : Call D) (u : ByteArray) :
    Head.certifyMessage u ≠ X.cancelMessage c := by
  unfold Ctx.cancelMessage
  exact certify_cancel_disjoint _ _

end Nanodregg.Protocol
