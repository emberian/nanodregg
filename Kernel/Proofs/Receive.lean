/-
# Kernel.Proofs.Receive — what a derived Turn guarantees before `World.admit` sees it
-/
import Kernel.Receive.Submit
import Kernel.Proofs.Check

namespace Nanodregg.Kernel.Receive

open Nanodregg.Kernel

variable {D : Type} [Ord D] [DecidableEq D]

omit [Ord D] [DecidableEq D] in
/-- Distinct constructors have distinct wire names (law 7): equal names, same constructor. -/
theorem Refusal.name_injective (a b : Refusal D) (h : a.name = b.name) : a.ctorIdx = b.ctorIdx := by
  cases a <;> cases b <;> simp_all [Refusal.name] <;> rfl

/-- **The World binding (KERNEL-24).** A call that names another World is refused `wrongWorld`,
before its signature, its key or any pinned read is looked at. -/
theorem receive_wrongWorld {X : Ctx D} {w : World D} {c : Call D} (h : c.unsigned.world ≠ w.origin) :
    receive X w c = .error .wrongWorld := by
  simp [receive, req, h, bind, Except.bind]

/-- A derived call named this World, and is the derivation through its pins. -/
theorem receive_ok_with {X : Ctx D} {w : World D} {c : Call D} {t : Turn D}
    (h : receive X w c = .ok t) :
    c.unsigned.world = w.origin ∧ receiveWith X (pinned X.env w c.unsigned.pins) c = .ok t := by
  unfold receive at h
  simp only [except_bind_ok] at h
  obtain ⟨⟨⟩, hw, h⟩ := h
  rw [req_ok, decide_eq_true_eq] at hw
  exact ⟨hw, h⟩

/-- **Consent determinism.** A derivation depends only on the World's identity and the cells the
caller pinned: two Worlds that agree there derive the same Turn (or the same refusal) from the
same call. -/
theorem receive_congr {X : Ctx D} {w₁ w₂ : World D} {c : Call D} (ho : w₁.origin = w₂.origin)
    (agree : ∀ p ∈ c.unsigned.pins, w₁.live X.env p.1 = w₂.live X.env p.1) :
    receive X w₁ c = receive X w₂ c := by
  have hv : pinned X.env w₁ c.unsigned.pins = pinned X.env w₂ c.unsigned.pins := by
    funext x
    unfold pinned
    by_cases hx : c.unsigned.pins.any (fun p => p.1 = x) = true
    · obtain ⟨p, hp, hpx⟩ := List.any_eq_true.mp hx
      have hpx' : p.1 = x := of_decide_eq_true hpx
      simp only [hx, if_true]
      rw [← hpx', agree p hp]
    · simp only [hx]; rfl
  unfold receive; rw [hv, ho]

/-- A sealed Turn pays exactly its weight, within the signed ceiling, and carries the caller's
pins as its touches, its window, its call and the receiver's nullifiers; every effect is on a
pinned cell. -/
theorem sealTurn_ok {X : Ctx D} {c : Call D} {cr : List (D × Cell)} {efs : List (D × Act)}
    {ns : List D} {t : Turn D} (h : sealTurn X c cr efs ns = .ok t) :
    t.charge = t.weight ∧ t.charge ≤ c.unsigned.maxCharge ∧
      t.touches = touchesOf c.unsigned.pins efs ∧
      t.event = X.callBytes c ∧ t.txId = txIdOf X c ∧ t.notBefore = c.unsigned.notBefore ∧
      t.validUntil = c.unsigned.validUntil ∧ t.creates = cr ∧ t.nullifiers = ns ∧
      (∀ e ∈ efs, ∃ p ∈ c.unsigned.pins, p.1 = e.1) := by
  unfold sealTurn at h
  simp only [except_bind_ok] at h
  obtain ⟨⟨⟩, hp, h⟩ := h
  split at h
  · simp only [Except.ok.injEq] at h
    subst h
    refine ⟨rfl, by assumption, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
    intro e he
    unfold effectsPinned at hp
    simp only [except_bind_ok] at hp
    obtain ⟨⟨⟩, hall, _⟩ := hp
    have := (forEx_ok.mp hall) e he
    rw [req_ok] at this
    obtain ⟨p, hp, hpe⟩ := List.any_eq_true.mp this
    exact ⟨p, hp, of_decide_eq_true hpe⟩
  · simp at h

omit [Ord D] [DecidableEq D] in
/-- A seal bears exactly the receiver's cells, each at its `bornId`. -/
theorem bornAt_cells {X : Ctx D} {c : Call D} {base : Nat} {cr : List Cell} :
    (bornAt X c base cr).map Prod.snd = cr := by
  unfold bornAt; rw [List.map_map]
  exact List.zipIdx_map_fst base cr

omit [Ord D] [DecidableEq D] in
theorem mem_bornAt_cell {X : Ctx D} {c : Call D} {base : Nat} {cr : List Cell} {p : D × Cell}
    (h : p ∈ bornAt X c base cr) : p.2 ∈ cr := by
  have := List.mem_map_of_mem (f := Prod.snd) h
  rwa [bornAt_cells] at this

omit [Ord D] in
theorem touchesOf_pins (pins : List (D × D)) (efs : List (D × Act)) :
    (touchesOf pins efs).map (fun x => (x.cell, x.seen)) = pins := by
  induction pins with
  | nil => rfl
  | cons p rest ih => simp only [touchesOf, List.map_cons] at ih ⊢; rw [ih]

/-- **One seal per call** (KERNEL-28 (c)). A derived Turn is the ONE seal of the call's whole
Draft: what its Body derived at the signer, and every call of its tree. -/
theorem receiveWith_sealed {X : Ctx D} {look : Pinned D} {c : Call D} {t : Turn D}
    (h : receiveWith X look c = .ok t) :
    X.verify c.unsigned.key (X.callMessage c.unsigned) c.signature = true ∧
      ∃ d, derive X look c = .ok d ∧ sealTurn X c d.creates d.effects d.nullifiers = .ok t := by
  unfold receiveWith at h
  simp only [except_bind_ok] at h
  obtain ⟨⟨⟩, hs, ⟨⟩, _, h⟩ := h
  unfold deriveTurn at h
  simp only [except_bind_ok] at h
  obtain ⟨d, hd, h⟩ := h
  unfold checkSignature at hs
  exact ⟨req_ok.mp hs, d, hd, h⟩

/-- **Derive-then-admit, the receive half.** A derived Turn is signed with the key the call
names, pays exactly its weight within the signed price, and touches exactly the caller's pins,
in order, with what the signer saw — so `World.admit`'s charge check passes by construction and
its pin check is the caller's own observation. -/
theorem receive_ok {X : Ctx D} {w : World D} {c : Call D} {t : Turn D}
    (h : receive X w c = .ok t) :
    X.verify c.unsigned.key (X.callMessage c.unsigned) c.signature = true ∧
      t.charge = t.weight ∧ t.charge ≤ c.unsigned.maxCharge ∧
      t.touches.map (fun x => (x.cell, x.seen)) = c.unsigned.pins ∧
      t.event = X.callBytes c ∧ t.txId = txIdOf X c ∧ t.notBefore = c.unsigned.notBefore ∧
      t.validUntil = c.unsigned.validUntil := by
  obtain ⟨hv, _, _, hs⟩ := receiveWith_sealed (receive_ok_with h).2
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, _⟩ := sealTurn_ok hs
  exact ⟨hv, h1, h2, by rw [h3]; exact touchesOf_pins _ _, h4, h5, h6, h7⟩

/-- Every call but a rotation is signed by its member's current key. -/
theorem receiveWith_key {X : Ctx D} {look : Pinned D} {c : Call D} {t : Turn D}
    (h : receiveWith X look c = .ok t) : keyRule look c.unsigned = .ok () := by
  unfold receiveWith at h
  simp only [except_bind_ok] at h
  obtain ⟨⟨⟩, _, ⟨⟩, hk, _⟩ := h
  exact hk

/-- A submission commits exactly `World.admit` of exactly what `receive` derived, for a call not
yet in the journal. -/
theorem submit_ok {X : Ctx D} {w w' : World D} {c : Call D} {t : Turn D}
    (h : submit X w c = .ok (t, w')) :
    w.journal[txIdOf X c]? = none ∧ receive X w c = .ok t ∧ World.admit X.env w t = .ok w' := by
  unfold submit at h
  split at h
  · simp at h
  · rename_i hj
    split at h
    · simp at h
    · rename_i t' hr
      split at h
      · simp at h
      · rename_i w'' ha
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨hj, hr, ha⟩

/-- **A retry is never re-judged.** A call already in the journal is `replayed` at its height,
whatever the World and the call's own derivation would say now. -/
theorem submit_replayed {X : Ctx D} {w : World D} {c : Call D} {h : Nat} {d : D}
    (hj : w.journal[txIdOf X c]? = some (h, d)) :
    submit X w c = .error (.rejected (.replayed h)) := by
  unfold submit; rw [hj]

end Nanodregg.Kernel.Receive
