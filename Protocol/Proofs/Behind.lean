/-
# Protocol.Proofs.Behind — a call refused stale BEHIND is never admitted later (PROTOCOL-57)

The settlement's `refused staleCode` arm (KERNEL-54, PROTOCOL-52) is final BY THEOREM: the member's
own call, as `plan` signed it at a World `w₀` of follow's fold, that follow's World `w` reached from
`w₀` refuses `stale`, is admitted by no `submit` at any World the fold reaches from `w`, or the
deployed hash collides among the call's pin inputs at `w₀` and there (`behindPres`, an explicit
list). The pieces: `plan_pins` (the W0 premise: every pin `plan` signs is the planning World's, and
it signs no range), `receive_pins` (a derived Turn checks every pin its call carries, at any World),
`Kernel.admit_stale_pin` (a `stale` refusal names a pin that disagrees), and
`Kernel.stale_behind_forever` / `row_stale_behind_forever` (a pin stale on the fold stays stale).
-/
import Protocol.Proofs.Command
import Kernel.Proofs.StaleOnly
import Kernel.Proofs.Versions

namespace Nanodregg.Protocol.Command

open Nanodregg.Kernel Nanodregg.Kernel.Receive
open Nanodregg.Codec.Kernel (Cell.Fits)

variable {D : Type} [Ord D] [DecidableEq D]

/-- Every cell pin `derivePins` adds is the planning World's own `pinOf`. -/
theorem derivePins_pins {X : Ctx D} {w : World D} :
    ∀ (n : Nat) (u u' : Unsigned D) (t : Turn D), derivePins X w n u = .ok (u', t) →
      ∀ p ∈ u'.pins, p ∈ u.pins ∨ p.2 = Kernel.pinOf X.env (w.entry X.env p.1)
  | 0, _, _, _, h => by simp [derivePins] at h
  | n + 1, u, u', t, h => by
      simp only [derivePins] at h
      split at h
      · intro p hp
        rcases derivePins_pins n _ u' t h p hp with hm | hk
        · simp only [List.mem_append, List.mem_singleton] at hm
          rcases hm with hm | rfl
          · exact .inl hm
          · exact .inr rfl
        · exact .inr hk
      · split at h
        · cases h
        · have := derivePins_pins n _ u' t h
          simpa using this
      · cases h
      · cases h; intro p hp; exact .inl hp

/-- `derivePins` never adds a range read. -/
theorem derivePins_ranges {X : Ctx D} {w : World D} :
    ∀ (n : Nat) (u u' : Unsigned D) (t : Turn D), derivePins X w n u = .ok (u', t) → u'.ranges = u.ranges
  | 0, _, _, _, h => by simp [derivePins] at h
  | n + 1, u, u', t, h => by
      simp only [derivePins] at h
      split at h
      · have := derivePins_ranges n _ u' t h
        simpa using this
      · split at h
        · cases h
        · have := derivePins_ranges n _ u' t h
          simpa using this
      · cases h
      · cases h; rfl

/-- **The pins `plan` signs are the planning World's** (KERNEL-54, the W0 premise of the BEHIND
finality): every cell pin is `pinOf` of `w`'s entry, every row pin is `rowPinAt` of `w`, and the
call reads no range (the plan-side gap's second half). -/
theorem plan_pins {X : Ctx D} {me : Self D} {w : World D} {key : ByteArray} {b : Body D}
    {u : Unsigned D} (h : plan X me w key b = .ok u) :
    (∀ p ∈ u.pins, p.2 = Kernel.pinOf X.env (w.entry X.env p.1)) ∧
      (∀ p ∈ u.rowPins, ∃ k, p = rowPinAt X.env w k) ∧ u.ranges = [] := by
  unfold plan at h
  split at h
  · cases h
  · rename_i u' t hp
    split at h
    · cases h
    · cases h
      refine ⟨?_, planUnchecked_rowPins hp, ?_⟩
      · simp only [planUnchecked, bind, Except.bind] at hp
        split at hp
        · cases hp
        · rename_i q hq
          obtain ⟨u1, t1⟩ := q
          simp only at hp
          split at hp
          · cases hp
          · cases hp
            intro p hm
            rcases derivePins_pins _ _ _ _ hq p hm with hm | hk
            · simp at hm
            · exact hk
      · simp only [planUnchecked, bind, Except.bind] at hp
        split at hp
        · cases hp
        · rename_i q hq
          obtain ⟨u1, t1⟩ := q
          simp only at hp
          split at hp
          · cases hp
          · cases hp
            exact derivePins_ranges _ _ _ _ hq

/-- Every row pin of a call is a row touch of its Turn, at the digest the caller saw. -/
theorem rowTouchesOf_pins {pins : List (RowSlot D × D)} {rows : List (RowSlot D × RowAct)}
    {rts : List (RowTouch D)} (h : rowTouchesOf pins rows = .ok rts) :
    (∀ p ∈ pins, ∃ x ∈ rts, x.slot = p.1 ∧ x.seen = some p.2) ∧
      ∀ x ∈ rts, ∀ s, x.seen = some s → (x.slot, s) ∈ pins := by
  unfold rowTouchesOf at h
  simp only [except_bind_ok] at h
  obtain ⟨⟨⟩, -, h⟩ := h
  split at h
  · simp [bind, Except.bind] at h
  · simp only [except_bind_ok] at h
    obtain ⟨⟨⟩, -, h⟩ := h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    refine ⟨fun p hp => ⟨_, List.mem_append_left _ (List.mem_map_of_mem hp), rfl, rfl⟩, ?_⟩
    intro x hx s hs
    rcases List.mem_append.mp hx with hx | hx
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
      cases hs
      exact hp
    · obtain ⟨e, -, rfl⟩ := List.mem_map.mp hx
      cases hs

/-- **A derived Turn checks every pin its call carries** (the receive half of the BEHIND
finality): its touches are the call's cell pins, every row pin is a row touch at the caller's
digest, and its range reads are the call's. Whatever World derived it. -/
theorem receive_pins {X : Ctx D} {v : World D} {c : Call D} {t : Turn D} (h : receive X v c = .ok t) :
    t.touches.map (fun x => (x.cell, x.seen)) = c.unsigned.pins ∧
      (∀ p ∈ c.unsigned.rowPins, ∃ x ∈ t.rows, x.slot = p.1 ∧ x.seen = some p.2) ∧
      (∀ x ∈ t.rows, ∀ s, x.seen = some s → (x.slot, s) ∈ c.unsigned.rowPins) ∧
      t.ranges = c.unsigned.ranges := by
  refine ⟨(receive_ok h).2.2.2.1, ?_⟩
  obtain ⟨-, d, -, hs⟩ := receiveWith_sealed (receive_ok_with h).2
  unfold sealTurn at hs
  simp only [except_bind_ok] at hs
  obtain ⟨⟨⟩, -, rts, hr, hs⟩ := hs
  split at hs
  · simp only [Except.ok.injEq] at hs
    subst hs
    exact ⟨(rowTouchesOf_pins hr).1, (rowTouchesOf_pins hr).2, rfl⟩
  · cases hs

/-- **A call refused stale BEHIND on follow's fold is never admitted later** (cv 01a15187; the
settlement's `refused staleCode` arm, PROTOCOL-52's "final by fold structure" now by theorem). The
member's own call, as `plan` signed it at a World `w₀` of follow's fold (the W0 premise: its pins
are `w₀`'s, `plan_pins`), that follow's World `w` reached from `w₀` refuses `stale`
(`staleBehind`), is admitted by no `submit` at any World `w'` the fold reaches from `w`, unless the
deployed hash collides among the call's pin inputs at `w₀` and `w'` (`behindPres`). -/
theorem staleBehind_final [Std.TransOrd D] [Std.LawfulEqOrd D] {X : Ctx D} {n : Nat}
    (hE : X.env.Lawful n) {me : Self D} {w₀ w w' : World D} {l₁ l₂ : List (Kernel.Step D)}
    {key : ByteArray} {b : Body D} {u : Unsigned D} {c : Call D}
    (hf : w₀.CellsFit Cell.Fits X.env) (hr : w₀.RowsCanon X.env) (hok : w₀.RowsOk X.env)
    (hplan : plan X me w₀ key b = .ok u) (hc : c.unsigned = u)
    (h₁ : World.fold X.env w₀ l₁ = .ok w) (h₂ : World.fold X.env w l₂ = .ok w')
    (hs : staleBehind X me w c = true) :
    (∀ r, submit X w' c ≠ .ok r) ∨ CollidesAmong X.env.hash (behindPres X.env w₀ w' u) := by
  obtain ⟨-, -, -, t, y, hrt, hat⟩ := staleBehind_spec hs
  obtain ⟨hpc, hpr, hpq⟩ := plan_pins hplan
  obtain ⟨htc, -, htr, htq⟩ := receive_pins hrt
  have hrw := fold_rowsCanon hr h₁
  have hrw' := fold_rowsCanon hrw h₂
  by_cases hsub : ∃ r, submit X w' c = .ok r
  case neg => exact .inl fun r hr => hsub ⟨r, hr⟩
  obtain ⟨⟨t', v⟩, hsub⟩ := hsub
  right
  obtain ⟨-, hrt', hat'⟩ := submit_ok hsub
  obtain ⟨htc', htr', -, -⟩ := receive_pins hrt'
  rcases admit_stale_pin hrw hat with ⟨x, hx, -, hne⟩ | ⟨x, hx, k, s, hxs, -, hseen, hne⟩ | ⟨q, hq, -⟩
  · -- a cell pin
    have hm : (x.cell, x.seen) ∈ c.unsigned.pins := by
      rw [← htc]; exact List.mem_map_of_mem hx
    have hseen : x.seen = Kernel.pinOf X.env (w₀.entry X.env x.cell) := by
      rw [hc] at hm; exact hpc _ hm
    have hm' : (x.cell, x.seen) ∈ t'.touches.map (fun x => (x.cell, x.seen)) := by rw [htc']; exact hm
    obtain ⟨x', hx', he⟩ := List.mem_map.mp hm'
    simp only [Prod.mk.injEq] at he
    have hp' := admit_pins hat' x' hx'
    rw [he.1, he.2, hseen] at hp'
    rcases stale_behind_forever hf h₁ h₂ (c := x.cell) (by rw [← hseen]; exact hne) with h | h
    · exact (h hp').elim
    · refine CollidesAmong.mono ?_ h
      intro z hz
      refine List.mem_append_left _ (List.mem_flatMap.mpr ⟨_, by rw [← hc]; exact hm, ?_⟩)
      simpa using hz
  · -- a row pin
    have hm := htr x hx s hseen
    rw [hc] at hm
    obtain ⟨k', hk'⟩ := hpr _ hm
    simp only [rowPinAt, hxs, Prod.mk.injEq, RowSlot.row.injEq] at hk'
    obtain ⟨rfl, rfl⟩ := hk'
    obtain ⟨x', hx', hs', hseen'⟩ := htr' _ (by rw [hc]; exact hm)
    simp only at hs' hseen'
    rw [hxs] at hs'
    have hp' := admit_row_pins hrw' hat' x' hx' k _ hs' hseen'
    rcases row_stale_behind_forever hE hr hok h₁ h₂ (key := k) hne with h | h | h
    · exact (h hp').elim
    · have hl : w'.live X.env k.parent = none := by simp [World.live, h]
      exact (admit_dead hl ⟨x', hx', hs'⟩ hat').elim
    · refine CollidesAmong.mono ?_ h
      intro z hz
      refine List.mem_append_right _ (List.mem_flatMap.mpr ⟨_, hm, ?_⟩)
      simpa [hxs] using hz
  · -- a range pin: `plan` signs none
    rw [htq, hc, hpq] at hq
    cases hq

/-- TOOTH (`staleBehind_final`): where the hash separates the call's pin inputs at the two Worlds,
a call refused stale BEHIND is admitted by no later World of the fold. -/
theorem staleBehind_final_sep [Std.TransOrd D] [Std.LawfulEqOrd D] {X : Ctx D} {n : Nat}
    (hE : X.env.Lawful n) {me : Self D} {w₀ w w' : World D} {l₁ l₂ : List (Kernel.Step D)}
    {key : ByteArray} {b : Body D} {u : Unsigned D} {c : Call D}
    (hf : w₀.CellsFit Cell.Fits X.env) (hr : w₀.RowsCanon X.env) (hok : w₀.RowsOk X.env)
    (hplan : plan X me w₀ key b = .ok u) (hc : c.unsigned = u)
    (h₁ : World.fold X.env w₀ l₁ = .ok w) (h₂ : World.fold X.env w l₂ = .ok w')
    (hsep : Separates X.env.hash (behindPres X.env w₀ w' u))
    (hs : staleBehind X me w c = true) : ∀ r, submit X w' c ≠ .ok r :=
  hsep.elim (staleBehind_final hE hf hr hok hplan hc h₁ h₂ hs)

end Nanodregg.Protocol.Command
