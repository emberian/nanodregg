/-
# Protocol.Proofs.Domains — every message a member key signs begins with its own domain (KERNEL-42)

A member key signs five shapes: a call (`Receive.Ctx.callMessage`, `domCall`), a possession
proof (`Receive.possessionMessage`, `tagPossession`), a read envelope (`Envelope.message`,
`domEnvelope`), `init`'s identity probe (`Command.whoami`, a constant) and an invitation
(`Invite.message`, `domInvite`, PROTOCOL-42). Each pair of domains
differs at a byte both hold, so no message of one shape is a message of another, whatever follows
the domain: a signature made for one is never one over another, with no hash premise. An observer
custody that signs only messages beginning with `domEnvelope` (HOSTING-17 §7, CLIENT-22) therefore
never signs a call, a possession proof, a probe or an invitation (`call_not_envelope`,
`possession_not_envelope`, `whoami_not_envelope`, `invite_not_envelope`).
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

end Nanodregg.Protocol
