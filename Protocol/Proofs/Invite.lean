/-
# Protocol.Proofs.Invite — what a joiner accepts is what its trusted sponsor signed

`accept_ok`: an accepted invitation's every field (the origin inputs, the pin, the sponsor and its key)
is what the signed bytes decode to, the key is the one the joiner trusts and verifies over exactly
those bytes, and the World returned is `Receive.genesis` of those inputs, its origin computed
(`accept_origin`). So nothing a relay changes after the sponsor signed reaches the joiner's World
without the signature failing: `accept_unverified` refuses it `pinMismatch`, `accept_untrusted`
refuses another signer `notSponsor`.
-/
import Protocol.Invite
import Kernel.Proofs.Origin

namespace Nanodregg.Protocol.Invite

open Nanodregg.Kernel Nanodregg.Kernel.Receive

theorem Refusal.name_injective (a b : Refusal) (h : a.name = b.name) : a.tag = b.tag := by
  rcases a with _ | _ | _ | r | _ <;> rcases b with _ | _ | _ | r' | _ <;>
    (try cases r) <;> (try cases r') <;> simp_all [Refusal.name, Refusal.tag, GenesisRefusal.name]

variable {D : Type} [Ord D] [DecidableEq D]

omit [Ord D] [DecidableEq D] in
theorem ofBytes_said {X : Ctx D} {b : ByteArray} {inv : Invitation D} (h : ofBytes X b = some inv) :
    said X inv.unsigned = some ⟨inv.name, inv.nonce, inv.allowance, inv.founders, inv.pin, inv.sponsor, inv.key⟩ := by
  unfold ofBytes at h
  split at h
  · cases h
  · rename_i u s _
    cases hv : said X u.1 with
    | none => simp [hv] at h
    | some v =>
      simp only [hv, Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq] at h
      subst h
      show said X u.1 = _
      rw [hv]

/-- **An accepted invitation is what the trusted key signed.** Its fields are the decode of the
bytes the key verifies over, and the World is the genesis of the inputs among them. -/
theorem accept_ok {X : Ctx D} {trusted b : ByteArray} {inv : Invitation D} {w : World D}
    (h : accept X trusted b = .ok (inv, w)) :
    said X inv.unsigned = some ⟨inv.name, inv.nonce, inv.allowance, inv.founders, inv.pin, inv.sponsor, inv.key⟩ ∧
      inv.key = trusted ∧ X.verify trusted (message inv.unsigned) inv.signature = true ∧
      genesis X inv.name inv.nonce inv.allowance inv.founders = .ok w := by
  unfold accept at h
  cases hb : ofBytes X b with
  | none => simp [hb] at h
  | some i =>
    simp only [hb] at h
    by_cases hk : i.key = trusted
    · simp only [hk, ne_eq, not_true_eq_false, ↓reduceIte] at h
      by_cases hv : X.verify trusted (message i.unsigned) i.signature = true
      · simp only [hv, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
        cases hg : genesis X i.name i.nonce i.allowance i.founders with
        | error r => simp [hg] at h
        | ok w' =>
          simp only [hg] at h
          cases h
          exact ⟨ofBytes_said hb, hk, hv, hg⟩
      · simp only [hv] at h; simp at h; cases h
    · simp [hk] at h; cases h

/-- The joiner's World is the World of the signed inputs: its origin is computed from them. -/
theorem accept_origin {X : Ctx D} {trusted b : ByteArray} {inv : Invitation D} {w : World D}
    (h : accept X trusted b = .ok (inv, w)) :
    w = genesisWorld X inv.name inv.nonce inv.allowance inv.founders :=
  (genesis_ok.mp (accept_ok h).2.2.2).2

/-- A signature that does not verify over the bytes carried (a relay changed an input, the pin or
the sponsor after the sponsor signed) is refused `pinMismatch`, whatever the inputs make. -/
theorem accept_unverified {X : Ctx D} {trusted b : ByteArray} {inv : Invitation D}
    (hb : ofBytes X b = some inv) (hk : inv.key = trusted)
    (hv : X.verify trusted (message inv.unsigned) inv.signature = false) :
    accept X trusted b = .error .pinMismatch := by
  unfold accept
  simp [hb, hk, hv]
  rfl

/-- An invitation signed by any key but the trusted one is refused `notSponsor`. -/
theorem accept_untrusted {X : Ctx D} {trusted b : ByteArray} {inv : Invitation D}
    (hb : ofBytes X b = some inv) (hk : inv.key ≠ trusted) :
    accept X trusted b = .error .notSponsor := by
  unfold accept
  simp [hb, hk]
  rfl

end Nanodregg.Protocol.Invite
