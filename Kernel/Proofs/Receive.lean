/-
# Kernel.Proofs.Receive — what a derived Turn guarantees before `World.admit` sees it
-/
import Kernel.Receive.Derive
import Kernel.Proofs.Check

namespace Nanodregg.Kernel.Receive

open Nanodregg.Kernel

variable {D : Type} [Ord D] [DecidableEq D]

/-- **Consent determinism.** A derivation depends only on the cells the caller pinned: two
Worlds that agree there derive the same Turn (or the same refusal) from the same call. -/
theorem receive_congr {X : Ctx D} {w₁ w₂ : World D} {c : Call D}
    (agree : ∀ p ∈ c.unsigned.pins, w₁.live p.1 = w₂.live p.1) :
    receive X w₁ c = receive X w₂ c := by
  have hv : pinned w₁ c.unsigned.pins = pinned w₂ c.unsigned.pins := by
    funext x
    unfold pinned
    by_cases hx : c.unsigned.pins.any (fun p => p.1 = x) = true
    · obtain ⟨p, hp, hpx⟩ := List.any_eq_true.mp hx
      have hpx' : p.1 = x := of_decide_eq_true hpx
      simp only [hx, if_true]
      rw [← hpx', agree p hp]
    · simp only [hx]; rfl
  unfold receive; rw [hv]

omit [Ord D] [DecidableEq D] in
/-- A sealed Turn pays exactly its weight, within the signed ceiling, and carries the caller's
pins, window and call. -/
theorem sealTurn_ok {X : Ctx D} {c : Call D} {cr : List Cell} {lg : List (Leg D)} {rt : List D}
    {t : Turn D} (h : sealTurn X c cr lg rt = .ok t) :
    t.charge = t.weight ∧ t.charge ≤ c.unsigned.maxCharge ∧ t.pins = c.unsigned.pins ∧
      t.event = X.callBytes c ∧ t.txId = txIdOf X c ∧ t.notBefore = c.unsigned.notBefore ∧
      t.validUntil = c.unsigned.validUntil ∧ t.creates = cr ∧ t.legs = lg ∧ t.retires = rt ∧
      t.nullifiers = [] := by
  unfold sealTurn at h
  dsimp only at h
  split at h
  · simp only [Except.ok.injEq] at h
    subst h
    exact ⟨rfl, by assumption, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · simp at h

omit [Ord D] in
/-- Every derivation of a kind ends in a seal of the call. -/
theorem dispatch_sealed {X : Ctx D} {look : Pinned D} {c : Call D} {b : Body D} {t : Turn D}
    (h : dispatch X look c b = .ok t) : ∃ cr lg rt, sealTurn X c cr lg rt = .ok t := by
  cases b <;>
    simp only [dispatch, enroll, rotate, install, create, write, law, invoke, grant, follow, revoke,
      except_bind_ok] at h <;>
    (repeat' (first | (obtain ⟨_, _, h⟩ := h) | exact ⟨_, _, _, h⟩))

omit [Ord D] in
theorem receiveWith_sealed {X : Ctx D} {look : Pinned D} {c : Call D} {t : Turn D}
    (h : receiveWith X look c = .ok t) :
    X.verify c.unsigned.key (X.unsignedBytes c.unsigned) c.signature = true ∧
      ∃ cr lg rt, sealTurn X c cr lg rt = .ok t := by
  unfold receiveWith at h
  simp only [except_bind_ok] at h
  obtain ⟨⟨⟩, hs, ⟨⟩, _, h⟩ := h
  unfold checkSignature at hs
  exact ⟨req_ok.mp hs, dispatch_sealed h⟩

/-- **Derive-then-admit, the receive half.** A derived Turn is signed with the key the call
names, pays exactly its weight within the signed price, and carries exactly the caller's pins
and window — so `World.admit`'s charge check passes by construction and its pin check is the
caller's own observation. -/
theorem receive_ok {X : Ctx D} {w : World D} {c : Call D} {t : Turn D}
    (h : receive X w c = .ok t) :
    X.verify c.unsigned.key (X.unsignedBytes c.unsigned) c.signature = true ∧
      t.charge = t.weight ∧ t.charge ≤ c.unsigned.maxCharge ∧ t.pins = c.unsigned.pins ∧
      t.event = X.callBytes c ∧ t.txId = txIdOf X c ∧ t.notBefore = c.unsigned.notBefore ∧
      t.validUntil = c.unsigned.validUntil := by
  obtain ⟨hv, cr, lg, rt, hs⟩ := receiveWith_sealed h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, _⟩ := sealTurn_ok hs
  exact ⟨hv, h1, h2, h3, h4, h5, h6, h7⟩

omit [Ord D] in
/-- Every call but a rotation is signed by its member's current key. -/
theorem receiveWith_key {X : Ctx D} {look : Pinned D} {c : Call D} {t : Turn D}
    (h : receiveWith X look c = .ok t) : keyRule look c.unsigned = .ok () := by
  unfold receiveWith at h
  simp only [except_bind_ok] at h
  obtain ⟨⟨⟩, _, ⟨⟩, hk, _⟩ := h
  exact hk

end Nanodregg.Kernel.Receive
