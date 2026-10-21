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
    said X inv.unsigned = some ⟨inv.start, inv.pin, inv.sponsor, inv.key⟩ := by
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

omit [Ord D] [DecidableEq D] in
/-- Both admissions require the trusted key's signature over the exact decoded fields. -/
theorem verified_ok {X : Ctx D} {trusted b : ByteArray} {inv : Invitation D}
    (h : verified X trusted b = .ok inv) :
    said X inv.unsigned = some ⟨inv.start, inv.pin, inv.sponsor, inv.key⟩ ∧
      inv.key = trusted ∧ X.verify trusted (message inv.unsigned) inv.signature = true := by
  unfold verified at h
  cases hb : ofBytes X b with
  | none => simp [hb] at h
  | some i =>
    simp only [hb] at h
    by_cases hk : i.key = trusted
    · simp only [hk, ne_eq, not_true_eq_false, ↓reduceIte] at h
      by_cases hv : X.verify trusted (message i.unsigned) i.signature = true
      · simp only [hv, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
        cases h
        exact ⟨ofBytes_said hb, hk, hv⟩
      · simp [hv] at h; cases h
    · simp [hk] at h; cases h

theorem accept_ok {X : Ctx D} {trusted b : ByteArray} {inv : Invitation D} {w : World D}
    (h : accept X trusted b = .ok (inv, w)) :
    said X inv.unsigned = some ⟨inv.start, inv.pin, inv.sponsor, inv.key⟩ ∧
      inv.key = trusted ∧ X.verify trusted (message inv.unsigned) inv.signature = true ∧
      startGenesis X inv.start = .ok w := by
  unfold accept at h
  cases hv : verified X trusted b with
  | error e => simp [hv, bind, Except.bind] at h
  | ok i =>
    simp only [hv, bind, Except.bind] at h
    cases hg : startGenesis X i.start with
    | error e => simp [hg] at h
    | ok v =>
      simp only [hg, pure, Except.pure] at h
      cases h
      exact ⟨(verified_ok hv).1, (verified_ok hv).2.1, (verified_ok hv).2.2, hg⟩

/-- Genesis-only admission produces a genesis with the signed inputs, never a carried start. -/
theorem accept_genesis {X : Ctx D} {trusted b : ByteArray} {inv : Invitation D} {w : World D}
    (h : accept X trusted b = .ok (inv, w)) :
    ∃ name nonce allowance fs, inv.start = .genesis name nonce allowance fs ∧
      genesis X name nonce allowance fs = .ok w := by
  have hg := (accept_ok h).2.2.2
  cases hs : inv.start with
  | genesis name nonce allowance fs =>
    refine ⟨name, nonce, allowance, fs, rfl, ?_⟩
    cases he : genesis X name nonce allowance fs with
    | error r => simp [hs, startGenesis, he, Except.mapError] at hg
    | ok g => simpa [hs, startGenesis, he, Except.mapError] using hg
  | carried o name nonce fromO height chain => simp [hs, startGenesis] at hg

theorem accept_origin {X : Ctx D} {trusted b : ByteArray} {inv : Invitation D} {w : World D}
    (h : accept X trusted b = .ok (inv, w)) :
    ∃ name nonce allowance fs, inv.start = .genesis name nonce allowance fs ∧
      w = genesisWorld X name nonce allowance fs := by
  obtain ⟨name, nonce, allowance, fs, hs, hg⟩ := accept_genesis h
  exact ⟨name, nonce, allowance, fs, hs, (genesis_ok.mp hg).2⟩

theorem acceptStart_ok {X : Ctx D} {trusted b : ByteArray} {inv : Invitation D} {o : D}
    (h : acceptStart X trusted b = .ok (inv, o)) :
    said X inv.unsigned = some ⟨inv.start, inv.pin, inv.sponsor, inv.key⟩ ∧
      inv.key = trusted ∧ X.verify trusted (message inv.unsigned) inv.signature = true ∧
      startOrigin X inv.start = .ok o := by
  unfold acceptStart at h
  cases hv : verified X trusted b with
  | error e => simp [hv, bind, Except.bind] at h
  | ok i =>
    simp only [hv, bind, Except.bind] at h
    cases hg : startOrigin X i.start with
    | error e => simp [hg] at h
    | ok v =>
      simp only [hg, pure, Except.pure] at h
      cases h
      exact ⟨(verified_ok hv).1, (verified_ok hv).2.1, (verified_ok hv).2.2, hg⟩

/-- The accepted origin is exactly the carried origin inside the signed start. -/
theorem acceptStart_carried_origin {X : Ctx D} {trusted b : ByteArray} {inv : Invitation D}
    {o signed fromO chain : D} {name nonce : ByteArray} {height : Nat}
    (ha : acceptStart X trusted b = .ok (inv, o))
    (hs : inv.start = .carried signed name nonce fromO height chain) : o = signed := by
  have h := (acceptStart_ok ha).2.2.2
  simpa [hs, startOrigin] using h.symm

theorem accept_unverified {X : Ctx D} {trusted b : ByteArray} {inv : Invitation D}
    (hb : ofBytes X b = some inv) (hk : inv.key = trusted)
    (hv : X.verify trusted (message inv.unsigned) inv.signature = false) :
    accept X trusted b = .error .pinMismatch := by
  simp [accept, verified, hb, hk, hv, bind, Except.bind, pure, Except.pure]

theorem accept_untrusted {X : Ctx D} {trusted b : ByteArray} {inv : Invitation D}
    (hb : ofBytes X b = some inv) (hk : inv.key ≠ trusted) :
    accept X trusted b = .error .notSponsor := by
  simp [accept, verified, hb, hk, bind, Except.bind]

theorem acceptStart_unverified {X : Ctx D} {trusted b : ByteArray} {inv : Invitation D}
    (hb : ofBytes X b = some inv) (hk : inv.key = trusted)
    (hv : X.verify trusted (message inv.unsigned) inv.signature = false) :
    acceptStart X trusted b = .error .pinMismatch := by
  simp [acceptStart, verified, hb, hk, hv, bind, Except.bind, pure, Except.pure]

theorem acceptStart_untrusted {X : Ctx D} {trusted b : ByteArray} {inv : Invitation D}
    (hb : ofBytes X b = some inv) (hk : inv.key ≠ trusted) :
    acceptStart X trusted b = .error .notSponsor := by
  simp [acceptStart, verified, hb, hk, bind, Except.bind]

end Nanodregg.Protocol.Invite
