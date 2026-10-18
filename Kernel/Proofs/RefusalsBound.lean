/-
# Kernel.Proofs.RefusalsBound — the refusals trie is bounded by the kernel (KERNEL-55 R1)

The refusals trie is in the encoded World but in neither `World.weight` nor the charge, so its size
needs its own bound. R1 (ROOT's ruling on KERNEL-55 Q2): a kernel-wide cap,
`Bounds.refusalsPerWindowMax` (C) recorded refusals per window, all members together, checked in
`checkRefusal` (`refusalsFull`) and counted by a `total` leaf (`refusalTotal`).

The bound (`refusals_bounded`): on every `RefusalsOk` World that is `CountedOk` (every reached
World, `fold_refusals_bounded`, `reach_refusals_bounded`; every base CODEC's
`kernel/refusals-counted` admits, `refusals_bounded_of_counted`), the listing holds at most 3C
records, at most C counts, at most 1 total, and nothing else. No receive premise.

* **Three windows, exactly** (`refusal_window_range`): a record lives while `H < h + 2 * windowMax`
  at the multiples of `windowMax`, so a World in window j holds records of windows j, j-1 and j-2
  only; and window j-2's do survive the prune that opens window j (`refusal_window_three`), so two
  windows would be wrong.
* **C per window**: the current window's records are its total (≤ C by `refusalFits`), the two before
  are bounded by `refusalsCounted`'s clause, which the fold keeps (a window's total becomes the
  previous window's records when the window turns).
* **Counts ≤ C**: each count leaf is a member with at least one record this window, keys are
  distinct, so the counts are at most the window's records.
* **One total**: every total leaf is at (origin, current window).

Teeth: `refusalsOk_bounds_nothing` (the per-leaf check `refusalFits` alone admits a World with any
number of records: the bound rests on `CountedOk`); `checkRefusal_full` and
`refusalsFull_independent` (on a World passing every refusals check, `counted_world`, at total C
with every member charged once, the refusal is declined `refusalsFull`: the cap binds where the
per-member budget does not); `uncapped_overflows` (a refusal
committed at total C, as a kernel without the cap would, leaves a World that is not `RefusalsOk`);
`refusalsCounted_total_lowered` (a decoded base whose total is lowered, to reset the World's budget,
passes `refusalsFits` and is refused by `refusalsCounted`).
-/
import Kernel.Proofs.RefusalsCounted

namespace Nanodregg.Kernel

variable {D : Type} [Ord D] [DecidableEq D]

/-! ## Sums -/

omit [Ord D] [DecidableEq D] in
theorem sumN_le_of_le {α : Type} (f g : α → Nat) :
    ∀ {l : List α}, (∀ x ∈ l, f x ≤ g x) → (l.map f).sum ≤ (l.map g).sum
  | [], _ => by simp
  | x :: l, h => by
      have h1 := h x (List.mem_cons_self ..)
      have h2 := sumN_le_of_le f g (l := l) (fun y hy => h y (List.mem_cons_of_mem _ hy))
      simp only [List.map_cons, List.sum_cons]; omega

omit [Ord D] [DecidableEq D] in
theorem sumN_eq_length {α : Type} (g : α → Nat) :
    ∀ {l : List α}, (∀ x ∈ l, g x = 1) → (l.map g).sum = l.length
  | [], _ => rfl
  | x :: l, h => by
      have h1 := h x (List.mem_cons_self ..)
      have h2 := sumN_eq_length g (l := l) (fun y hy => h y (List.mem_cons_of_mem _ hy))
      simp only [List.map_cons, List.sum_cons, List.length_cons]; omega

omit [Ord D] [DecidableEq D] in
theorem sumN_add3 {α : Type} (f g k : α → Nat) :
    ∀ l : List α, (l.map fun x => f x + g x + k x).sum = (l.map f).sum + (l.map g).sum + (l.map k).sum
  | [] => rfl
  | x :: l => by
      have := sumN_add3 f g k l
      simp only [List.map_cons, List.sum_cons]; omega

omit [Ord D] [DecidableEq D] in
theorem sumN_swap {α β : Type} (f : α → β → Nat) :
    ∀ (l₁ : List α) (l₂ : List β),
      (l₁.map fun x => (l₂.map (f x)).sum).sum = (l₂.map fun y => (l₁.map fun x => f x y).sum).sum
  | [], l₂ => by
      simp only [List.map_nil, List.sum_nil]
      exact (sumN_eq_zero_of _ (fun _ _ => rfl)).symm
  | x :: l₁, l₂ => by
      simp only [List.map_cons, List.sum_cons]
      rw [sumN_swap f l₁ l₂]
      induction l₂ with
      | nil => rfl
      | cons y l₂ ih =>
          simp only [List.map_cons, List.sum_cons]
          omega

omit [Ord D] [DecidableEq D] in
/-- In a listing with distinct keys, at most one entry is at any key. -/
theorem sumN_key_le_one {K V : Type} [DecidableEq K] (k : K) :
    ∀ {l : List (K × V)}, (l.map Prod.fst).Nodup → (l.map fun p => if p.1 = k then 1 else 0).sum ≤ 1
  | [], _ => by simp
  | p :: l, h => by
      rw [List.map_cons, List.nodup_cons] at h
      simp only [List.map_cons, List.sum_cons]
      by_cases hp : p.1 = k
      · have hz : (l.map fun p => if p.1 = k then 1 else 0).sum = 0 := by
          apply sumN_eq_zero_of
          intro q hq
          rw [if_neg]
          intro hq'
          exact h.1 (List.mem_map.mpr ⟨q, hq, hq'.trans hp.symm⟩)
        rw [if_pos hp, hz]
        omega
      · rw [if_neg hp]
        have := sumN_key_le_one k (l := l) h.2
        omega

/-! ## Three windows -/

omit [Ord D] [DecidableEq D] in
/-- **A record a World at height `H` can hold is of window `H / windowMax`, the one before, or the
one before that** (`refusalFits`: refused at most at `H + 1`, and not pruned at the last multiple of
`windowMax`). -/
theorem refusal_window_range {H h c : Nat} {id m : D}
    (hf : refusalFits H (.tx id) (.refused h c m) = true) :
    (h - 1) / Bounds.windowMax = H / Bounds.windowMax ∨
      (h - 1) / Bounds.windowMax = H / Bounds.windowMax - 1 ∨
      (h - 1) / Bounds.windowMax = H / Bounds.windowMax - 2 := by
  simp only [refusalFits, decide_eq_true_eq] at hf
  rw [windowMax_eq] at hf ⊢
  omega

omit [Ord D] [DecidableEq D] in
/-- **Three windows is tight**: at the prune that opens window `j` (height `j * windowMax`), the last
record of window `j - 2` (refused at `(j - 1) * windowMax`) is kept, and it fits the World there.
So two windows' records would not bound the trie. -/
theorem refusal_window_three (j : Nat) (hj : 2 ≤ j) (id m : D)
    (hlim : (j - 1) * Bounds.windowMax < Bounds.counterLimit) :
    keptRefusal (j * Bounds.windowMax) (.tx id) (.refused ((j - 1) * Bounds.windowMax) 0 m) = true ∧
      refusalFits (j * Bounds.windowMax) (.tx id) (.refused ((j - 1) * Bounds.windowMax) 0 m) = true ∧
      ((j - 1) * Bounds.windowMax - 1) / Bounds.windowMax = j * Bounds.windowMax / Bounds.windowMax - 2 := by
  simp only [keptRefusal, refusalFits, decide_eq_true_eq]
  have h0 : 0 < Bounds.counterLimit := Nat.lt_of_le_of_lt (Nat.zero_le _) hlim
  rw [windowMax_eq] at hlim ⊢
  refine ⟨?_, ⟨?_, ?_, ?_, hlim, h0⟩, ?_⟩ <;> clear hlim h0 <;> omega

omit [Ord D] [DecidableEq D] in
/-- A fitting entry is a record of one of the three windows, or not a record. -/
theorem refusedOne_le_windows {H : Nat} {p : RefusalSlot D × RefusalLeaf D} (hf : refusalFits H p.1 p.2 = true) :
    refusedOne p ≤ refusedWin (H / Bounds.windowMax) p + refusedWin (H / Bounds.windowMax - 1) p +
      refusedWin (H / Bounds.windowMax - 2) p := by
  obtain ⟨k, v⟩ := p
  cases k with
  | count _ _ => exact Nat.zero_le _
  | total _ _ => exact Nat.zero_le _
  | tx id =>
      cases v with
      | count _ => exact Nat.zero_le _
      | refused h c m =>
          have := refusal_window_range hf
          simp only [refusedOne, refusedWin]
          split <;> split <;> split <;> omega

/-! ## The bound -/

/-- **The refusals trie is bounded by the kernel** (KERNEL-55 R1): on a `RefusalsOk`, `CountedOk`
World, the listing holds at most `3 * C` records, at most `C` member counts, at most one total, and
every entry is one of the three (C = `Bounds.refusalsPerWindowMax`). What CODEC's size equality and
HOST's `worldBytesMax` derivation read: a count of each key kind. -/
theorem refusals_bounded {E : Env D} {w : World D} (hw : w.RefusalsOk E) (hc : w.CountedOk E) :
    (w.refusals.toList.map refusedOne).sum ≤ 3 * Bounds.refusalsPerWindowMax ∧
      (w.refusals.toList.map countKeyOne).sum ≤ Bounds.refusalsPerWindowMax ∧
      (w.refusals.toList.map totalKeyOne).sum ≤ 1 ∧
      w.refusals.toList.length = (w.refusals.toList.map refusedOne).sum +
        (w.refusals.toList.map countKeyOne).sum + (w.refusals.toList.map totalKeyOne).sum := by
  obtain ⟨-, hc2, hc3, hc4, hc5, hc6⟩ := hc
  have hmem : ∀ k v, (k, v) ∈ w.refusals.toList ↔ w.refusalAt E k = some v :=
    fun k v => Trie.mem_toList (refusalSpec E) 0 w.refusals hw.1.1 k v
  have hfit : ∀ p ∈ w.refusals.toList, refusalFits w.height p.1 p.2 = true :=
    fun p hp => hw.2 p.1 p.2 ((hmem p.1 p.2).mp hp)
  have hnd := Trie.toList_nodup (refusalSpec E) 0 w.refusals hw.1.1
  have htot := refusalTotal_le hw
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- records: three windows of at most C each
    have h1 := sumN_le_of_le refusedOne (fun p => refusedWin (w.height / Bounds.windowMax) p +
      refusedWin (w.height / Bounds.windowMax - 1) p + refusedWin (w.height / Bounds.windowMax - 2) p)
      (fun p hp => refusedOne_le_windows (hfit p hp))
    rw [sumN_add3] at h1
    omega
  · -- counts: each one a member with a record this window, keys distinct
    let f : RefusalSlot D × RefusalLeaf D → RefusalSlot D × RefusalLeaf D → Nat := fun q p =>
      match q with
      | (.count m win, _) => if win = refusalWindow w.height then refusedIn w.height m p else 0
      | _ => 0
    have hq : ∀ q ∈ w.refusals.toList, countKeyOne q ≤ (w.refusals.toList.map (f q)).sum := by
      intro q hq
      obtain ⟨k, v⟩ := q
      cases k with
      | tx _ => exact Nat.zero_le _
      | total _ _ => exact Nat.zero_le _
      | count m win =>
          have hf := hfit _ hq
          cases v with
          | refused _ _ _ => simp [refusalFits] at hf
          | count n =>
              simp only [refusalFits, decide_eq_true_eq] at hf
              obtain ⟨rfl, hn, -⟩ := hf
              have hcm := hc2 m
              unfold refusalCount at hcm
              rw [(hmem _ _).mp hq] at hcm
              simp only at hcm
              have hfq : f (RefusalSlot.count m (refusalWindow w.height), RefusalLeaf.count n) =
                  refusedIn w.height m := by
                funext p; simp [f]
              rw [hfq]
              simp only [countKeyOne]
              omega
    have hp : ∀ p ∈ w.refusals.toList,
        (w.refusals.toList.map fun q => f q p).sum ≤ refusedWin (w.height / Bounds.windowMax) p := by
      intro p _
      obtain ⟨k, v⟩ := p
      cases k with
      | count _ _ =>
          rw [sumN_eq_zero_of]; · exact Nat.zero_le _
          intro q _; obtain ⟨k', v'⟩ := q; cases k' <;> simp [f, refusedIn]
      | total _ _ =>
          rw [sumN_eq_zero_of]; · exact Nat.zero_le _
          intro q _; obtain ⟨k', v'⟩ := q; cases k' <;> simp [f, refusedIn]
      | tx id =>
          cases v with
          | count _ =>
              rw [sumN_eq_zero_of]; · exact Nat.zero_le _
              intro q _; obtain ⟨k', v'⟩ := q; cases k' <;> simp [f, refusedIn]
          | refused h c m' =>
              by_cases hwin : (h - 1) / Bounds.windowMax = w.height / Bounds.windowMax
              · have hle := sumN_le_of_le (fun q => f q (.tx id, .refused h c m'))
                  (fun q : RefusalSlot D × RefusalLeaf D =>
                    if q.1 = RefusalSlot.count m' (refusalWindow w.height) then 1 else 0)
                  (l := w.refusals.toList) (by
                    intro q _
                    obtain ⟨k', v'⟩ := q
                    cases k' with
                    | tx _ => exact Nat.zero_le _
                    | total _ _ => exact Nat.zero_le _
                    | count m win =>
                        simp only [f, refusedIn]
                        by_cases hw' : win = refusalWindow w.height
                        · by_cases hm : m' = m
                          · subst hm; subst hw'; simp [hwin]
                          · simp [hm, Ne.symm hm]
                        · simp [hw'])
                have h1 := sumN_key_le_one (RefusalSlot.count m' (refusalWindow w.height)) hnd
                simp only [refusedWin, hwin, if_true]
                omega
              · rw [sumN_eq_zero_of]; · exact Nat.zero_le _
                intro q _; obtain ⟨k', v'⟩ := q
                cases k' <;> simp [f, refusedIn, hwin]
    have hsw := sumN_swap f w.refusals.toList w.refusals.toList
    have a1 := sumN_le_of_le _ _ hq
    have a2 := sumN_le_of_le _ _ hp
    omega
  · -- one total: every total leaf is at (origin, current window)
    have hle := sumN_le_of_le totalKeyOne
      (fun q : RefusalSlot D × RefusalLeaf D =>
        if q.1 = RefusalSlot.total w.origin (refusalWindow w.height) then 1 else 0)
      (l := w.refusals.toList) (by
        intro q hq
        obtain ⟨k, v⟩ := q
        cases k with
        | tx _ => exact Nat.zero_le _
        | count _ _ => exact Nat.zero_le _
        | total o win =>
            have hf := hfit _ hq
            have ho := hc6 o win v ((hmem _ _).mp hq)
            cases v with
            | refused _ _ _ => simp [refusalFits] at hf
            | count n =>
                simp only [refusalFits, decide_eq_true_eq] at hf
                subst ho; rw [hf.1]; simp [totalKeyOne])
    have := sumN_key_le_one (RefusalSlot.total w.origin (refusalWindow w.height)) hnd
    omega
  · -- every entry is one of the three kinds
    rw [← sumN_add3, sumN_eq_length]
    intro q hq
    have hf := hfit q hq
    obtain ⟨k, v⟩ := q
    cases k <;> cases v <;> simp_all [refusedOne, countKeyOne, totalKeyOne, refusalFits]

/-- **The trie's length**: at most `4 * C + 1` entries (49,152 records, 16,384 counts and one total at
the deployed C). -/
theorem refusals_length_le {E : Env D} {w : World D} (hw : w.RefusalsOk E) (hc : w.CountedOk E) :
    w.refusals.toList.length ≤ 4 * Bounds.refusalsPerWindowMax + 1 := by
  obtain ⟨h1, h2, h3, h4⟩ := refusals_bounded hw hc
  omega

/-- **Every fold keeps the refusals bounded** from a `RefusalsOk`, `CountedOk` World: no receive
premise. -/
theorem fold_refusals_bounded {E : Env D} {w w' : World D} {l : List (Step D)} (hw : w.RefusalsOk E)
    (hc : w.CountedOk E) (h : World.fold E w l = .ok w') :
    (w'.refusals.toList.map refusedOne).sum ≤ 3 * Bounds.refusalsPerWindowMax ∧
      (w'.refusals.toList.map countKeyOne).sum ≤ Bounds.refusalsPerWindowMax ∧
      (w'.refusals.toList.map totalKeyOne).sum ≤ 1 ∧
      w'.refusals.toList.length = (w'.refusals.toList.map refusedOne).sum +
        (w'.refusals.toList.map countKeyOne).sum + (w'.refusals.toList.map totalKeyOne).sum :=
  refusals_bounded (fold_refusalsOk hw h) (fold_countedOk hw hc h)

/-- **A decoded base CODEC admits is bounded**: `kernel/refusals` (`RefusalsOk`) and
`kernel/refusals-counted` give the same bound. -/
theorem refusals_bounded_of_counted {E : Env D} {w : World D} (hw : w.RefusalsOk E)
    (hc : refusalsCounted E w = true) :
    (w.refusals.toList.map refusedOne).sum ≤ 3 * Bounds.refusalsPerWindowMax ∧
      (w.refusals.toList.map countKeyOne).sum ≤ Bounds.refusalsPerWindowMax ∧
      (w.refusals.toList.map totalKeyOne).sum ≤ 1 ∧
      w.refusals.toList.length = (w.refusals.toList.map refusedOne).sum +
        (w.refusals.toList.map countKeyOne).sum + (w.refusals.toList.map totalKeyOne).sum :=
  refusals_bounded hw ((refusalsCounted_iff hw).mp hc)

/-! ## Teeth -/

/-- TOOTH (the cap is not the per-member budget): with every other check passing and the member
under its own budget, a refusal at total C is declined `refusalsFull`. -/
theorem checkRefusal_full {E : Env D} {w : World D} {r : Refused D} (hb : checkRefusedBounds r = .ok ())
    (hs : checkSteps w = .ok ()) (hnb : r.notBefore ≤ w.height + 1) (hvu : w.height + 1 ≤ r.validUntil)
    (hj : w.journalAt E r.txId = none) (hx : w.refusalAt E (.tx r.txId) = none)
    (hm : refusalCount E w r.member < Bounds.refusalsPerWindow)
    (ht : refusalTotal E w = Bounds.refusalsPerWindowMax) :
    checkRefusal E w r = .error .refusalsFull := by
  unfold checkRefusal
  simp [hb, hs, hj, hx, req, hm, ht, hnb, hvu, bind, Except.bind]

/-- **A World passing every refusals check, at any total `n ≤ C`**: members `0 … n-1`, one record
each (refused at height 1, window 0), each counted 1, the total `n`, `n` steps, at height 0 with
origin 0. `RefusalsOk` and `CountedOk` both hold, so the fold reaches its shape and the decoder
admits it: what the teeth below that need a World passing the checks stand on. -/
theorem counted_world (E : Env Nat) (n : Nat) (hn : n ≤ Bounds.refusalsPerWindowMax) :
    ∃ w : World Nat, w.height = 0 ∧ w.steps = n ∧ w.origin = 0 ∧ w.journal = .empty ∧
      w.RefusalsOk E ∧ w.CountedOk E ∧ refusalTotal E w = n ∧
      (∀ m, refusalCount E w m ≤ 1) ∧ (∀ i, n ≤ i → w.refusalAt E (.tx i) = none) := by
  have key : ∀ n, ∃ t : Refusals Nat, Trie.Canon (refusalSpec E) 0 t ∧
      (∀ i, t.get (refusalSpec E) (.tx i) = if i < n then some (.refused 1 0 i) else none) ∧
      (∀ i win, t.get (refusalSpec E) (.count i win) = if i < n ∧ win = 0 then some (.count 1) else none) ∧
      (∀ o win, t.get (refusalSpec E) (.total o win) =
        if o = 0 ∧ win = 0 ∧ 1 ≤ n then some (.count n) else none) ∧
      (t.toList.map refusedOne).sum = n ∧
      (∀ m, (t.toList.map (refusedIn 0 m)).sum = if m < n then 1 else 0) ∧
      (∀ k, (t.toList.map (refusedWin k)).sum = if k = 0 then n else 0) := by
    intro n
    induction n with
    | zero =>
        refine ⟨.empty, Trie.canon_empty _ 0, ?_, ?_, ?_, rfl, fun m => rfl, fun k => by simp [Trie.T.toList]⟩ <;>
          intros <;> simp [Trie.get_empty]
    | succ n ih =>
        obtain ⟨t, hc, htx, hcnt, htot, hs1, hs2, hs3⟩ := ih
        have hr1 := Trie.routed_insert (refusalSpec E) (.tx n) (.refused 1 0 n) hc.1
        have hr2 := Trie.routed_insert (refusalSpec E) (.count n 0) (.count 1) hr1
        have hnone : t.get (refusalSpec E) (.tx n) = none := by rw [htx]; simp
        have hsum : ∀ g : RefusalSlot Nat × RefusalLeaf Nat → Nat, (∀ m win v, g (.count m win, v) = 0) →
            (∀ o win v, g (.total o win, v) = 0) →
            ((((t.insert (refusalSpec E) (.tx n) (.refused 1 0 n)).insert (refusalSpec E) (.count n 0)
              (.count 1)).insert (refusalSpec E) (.total 0 0) (.count (n + 1))).toList.map g).sum =
              (t.toList.map g).sum + g (.tx n, .refused 1 0 n) := by
          intro g hg hgt
          rw [sumN_insert_zero g hr2 _ _ (hgt _ _), sumN_insert_count g hg hr1,
            Trie.sumN_insert_none _ g hc.1 _ hnone]
        refine ⟨((t.insert (refusalSpec E) (.tx n) (.refused 1 0 n)).insert (refusalSpec E) (.count n 0)
            (.count 1)).insert (refusalSpec E) (.total 0 0) (.count (n + 1)),
          Trie.canon_insert _ _ _ (Trie.canon_insert _ _ _ (Trie.canon_insert _ _ _ hc)),
          ?_, ?_, ?_, ?_, ?_, ?_⟩
        · intro i
          simp only [Trie.get_insert]
          by_cases hi : i = n
          · subst hi; simp
          · rw [if_neg (by simp), if_neg (by simp), if_neg (by simp [hi]), htx]
            by_cases h1 : i < n
            · rw [if_pos h1, if_pos (by omega)]
            · rw [if_neg h1, if_neg (by omega)]
        · intro i win
          simp only [Trie.get_insert]
          by_cases hi : i = n ∧ win = 0
          · obtain ⟨rfl, rfl⟩ := hi; simp
          · rw [if_neg (by simp), if_neg (by simpa using hi), if_neg (by simp), hcnt]
            by_cases h1 : i < n ∧ win = 0
            · rw [if_pos h1, if_pos ⟨Nat.lt_succ_of_lt h1.1, h1.2⟩]
            · rw [if_neg h1, if_neg (fun h => h1
                ⟨Nat.lt_of_le_of_ne (Nat.le_of_lt_succ h.1) (fun he => hi ⟨he, h.2⟩), h.2⟩)]
        · intro o win
          simp only [Trie.get_insert]
          by_cases ho : o = 0 ∧ win = 0
          · obtain ⟨rfl, rfl⟩ := ho; simp
          · rw [if_neg (by simpa using ho), if_neg (by simp), if_neg (by simp), htot,
              if_neg (fun h => ho ⟨h.1, h.2.1⟩), if_neg (fun h => ho ⟨h.1, h.2.1⟩)]
        · rw [hsum refusedOne (fun _ _ v => by cases v <;> rfl) (fun _ _ v => by cases v <;> rfl), hs1]; rfl
        · intro m
          rw [hsum (refusedIn 0 m) (fun _ _ v => by cases v <;> rfl) (fun _ _ v => by cases v <;> rfl), hs2]
          simp only [refusedIn, Nat.sub_self, Nat.zero_div, and_true]
          by_cases hm : m = n
          · subst hm; simp
          · simp only [Ne.symm hm, if_false, Nat.add_zero]
            by_cases h1 : m < n
            · rw [if_pos h1, if_pos (by omega)]
            · rw [if_neg h1, if_neg (by omega)]
        · intro k
          rw [hsum (refusedWin k) (fun _ _ v => by cases v <;> rfl) (fun _ _ v => by cases v <;> rfl), hs3]
          simp only [refusedWin, Nat.sub_self, Nat.zero_div]
          by_cases hk : k = 0
          · subst hk; simp
          · simp [hk, Ne.symm hk]
  obtain ⟨t, hc, htx, hcnt, htot, hs1, hs2, hs3⟩ := key n
  have hw0 : refusalWindow 0 = 0 := by decide
  let w : World Nat := { World.genesis E 0 0 with refusals := t, steps := n }
  have hat : ∀ k, w.refusalAt E k = t.get (refusalSpec E) k := fun k => rfl
  have hwh : w.height = 0 := rfl
  have hwo : w.origin = 0 := rfl
  have hcount : ∀ m, refusalCount E w m = if m < n then 1 else 0 := by
    intro m
    unfold refusalCount
    rw [hat, hwh, hw0, hcnt]
    by_cases h1 : m < n
    · rw [if_pos ⟨h1, rfl⟩, if_pos h1]
    · rw [if_neg (fun h => h1 h.1), if_neg h1]
  have htotal : refusalTotal E w = n := by
    unfold refusalTotal
    rw [hat, hwh, hwo, hw0, htot]
    by_cases h1 : 1 ≤ n
    · rw [if_pos ⟨rfl, rfl, h1⟩]
    · rw [if_neg (fun h => h1 h.2.2)]; show 0 = n; omega
  have hok : w.RefusalsOk E := by
    refine ⟨hc, fun k v hk => ?_⟩
    rw [hat] at hk
    show refusalFits 0 k v = true
    cases k with
    | tx i =>
        rw [htx] at hk
        split at hk
        · cases hk; simp [refusalFits, windowMax_eq, counterLimit_eq]
        · cases hk
    | count i win =>
        rw [hcnt] at hk
        split at hk
        · rename_i h; obtain ⟨-, rfl⟩ := h; cases hk; simp [refusalFits, Bounds.refusalsPerWindow, hw0]
        · cases hk
    | total o win =>
        rw [htot] at hk
        split at hk
        · rename_i h; obtain ⟨rfl, rfl, h1⟩ := h; cases hk
          simp only [refusalFits, decide_eq_true_eq]
          exact ⟨by decide, h1, hn⟩
        · cases hk
  refine ⟨w, rfl, rfl, rfl, rfl, hok, ?_, htotal, fun m => by rw [hcount]; split <;> omega, ?_⟩
  · refine ⟨?_, fun m => ?_, ?_, ?_, ?_, ?_⟩
    · show (t.toList.map refusedOne).sum + 0 ≤ n; rw [hs1]; exact Nat.le_refl _
    · rw [hcount]; show _ = (t.toList.map (refusedIn 0 m)).sum; rw [hs2]
    · rw [htotal]; show n = (t.toList.map (refusedWin (0 / Bounds.windowMax))).sum
      rw [Nat.zero_div, hs3, if_pos rfl]
    · show (t.toList.map (refusedWin (0 / Bounds.windowMax - 1))).sum ≤ _
      rw [Nat.zero_div, Nat.zero_sub, hs3, if_pos rfl]; exact hn
    · show (t.toList.map (refusedWin (0 / Bounds.windowMax - 2))).sum ≤ _
      rw [Nat.zero_div, Nat.zero_sub, hs3, if_pos rfl]; exact hn
    · intro o win v hk
      rw [hat, htot] at hk
      split at hk
      · rename_i h; exact h.1
      · cases hk
  · intro i hi
    rw [hat, htx, if_neg (by omega)]

/-- **The cap binds where the per-member budget does not** (`checkRefusal_full`'s premises are
satisfiable on a World that passes every refusals check): at total C, every member charged once
(count 1, under `Bounds.refusalsPerWindow`), a fresh member's refusal is declined `refusalsFull`.
The World is `counted_world` at C: `RefusalsOk ∧ CountedOk`, so the fold reaches its shape and the
decoder admits it. -/
theorem refusalsFull_independent (E : Env Nat) {r : Refused Nat}
    (hb : checkRefusedBounds r = .ok ()) (hnb : r.notBefore ≤ 1) (hvu : 1 ≤ r.validUntil)
    (hid : Bounds.refusalsPerWindowMax ≤ r.txId) :
    ∃ w : World Nat, w.RefusalsOk E ∧ w.CountedOk E ∧ (∀ m, refusalCount E w m ≤ 1) ∧
      refusalTotal E w = Bounds.refusalsPerWindowMax ∧ checkRefusal E w r = .error .refusalsFull := by
  obtain ⟨w, hh, hst, -, hj, hok, hcnt, htot, hle, hnone⟩ :=
    counted_world E Bounds.refusalsPerWindowMax (Nat.le_refl _)
  refine ⟨w, hok, hcnt, hle, htot, ?_⟩
  apply checkRefusal_full hb
  · unfold checkSteps req; rw [hst, if_pos (by decide)]
  · rw [hh]; exact hnb
  · rw [hh]; exact hvu
  · unfold World.journalAt; rw [hj]; rfl
  · exact hnone _ hid
  · have := hle r.member; unfold Bounds.refusalsPerWindow; omega
  · exact htot

/-- TOOTH (the cap is what keeps the trie bounded): a refusal committed at total C, as a kernel
without the `refusalsFull` check would commit it, leaves a total of C + 1, which no `RefusalsOk`
World holds. -/
theorem uncapped_overflows {E : Env D} {w : World D} {r : Refused D}
    (ht : refusalTotal E w = Bounds.refusalsPerWindowMax) :
    (commitRefusal E w r).refusalAt E (.total w.origin (refusalWindow w.height)) =
        some (.count (Bounds.refusalsPerWindowMax + 1)) ∧
      ¬ (commitRefusal E w r).RefusalsOk E := by
  have hat : (commitRefusal E w r).refusalAt E (.total w.origin (refusalWindow w.height)) =
      some (.count (Bounds.refusalsPerWindowMax + 1)) := by
    unfold World.refusalAt
    rw [commitRefusal_refusals, Trie.get_insert, if_pos rfl, ht]
  refine ⟨hat, fun hok => ?_⟩
  have := hok.2 _ _ hat
  simp [refusalFits, Bounds.refusalsPerWindowMax] at this

/-- TOOTH (`refusalsCounted`'s total clause): **a total lowered by one, to reset the World's budget,
is refused, and by this check alone.** The lowered World still holds only leaves that fit
(`RefusalsOk`, so `refusalsFits` admits it). -/
theorem refusalsCounted_total_lowered {E : Env D} {w w' : World D} (hw : w.RefusalsOk E)
    (hc : refusalsCounted E w = true) (hT : 2 ≤ refusalTotal E w)
    (hr : w'.refusals = w.refusals.insert (refusalSpec E) (.total w.origin (refusalWindow w.height))
      (.count (refusalTotal E w - 1)))
    (hh : w'.height = w.height) (ho : w'.origin = w.origin) :
    w'.RefusalsOk E ∧ refusalsCounted E w' = false := by
  have hle := refusalTotal_le hw
  have hok : w'.RefusalsOk E := by
    refine ⟨?_, fun k v hk => ?_⟩
    · unfold World.RefusalsCanon; rw [hr]; exact Trie.canon_insert _ _ _ hw.1
    · rw [hh]
      unfold World.refusalAt at hk
      rw [hr, Trie.get_insert] at hk
      split at hk
      · rename_i he; cases hk; subst he
        simp only [refusalFits, decide_eq_true_eq]; exact ⟨trivial, by omega, by omega⟩
      · exact hw.2 k v hk
  refine ⟨hok, ?_⟩
  cases hb : refusalsCounted E w' with
  | false => rfl
  | true =>
      exfalso
      have h' := ((refusalsCounted_iff hok).mp hb).2.2.1
      have h0 := ((refusalsCounted_iff hw).mp hc).2.2.1
      have ht' : refusalTotal E w' = refusalTotal E w - 1 := by
        unfold refusalTotal World.refusalAt
        rw [hr, hh, ho, Trie.get_insert, if_pos rfl]
        rfl
      have hsum : (w'.refusals.toList.map (refusedWin (w'.height / Bounds.windowMax))).sum =
          (w.refusals.toList.map (refusedWin (w.height / Bounds.windowMax))).sum := by
        rw [hr, hh, sumN_insert_zero _ hw.1.1 _ _ (fun v => by cases v <;> rfl)]
      omega

/-- The tooth is not vacuous, with no premise: a World passing `refusalsCounted` with two records
this window exists (`counted_world` at 2), and so does its lowered copy (the World with only its
refusals replaced), which `refusalsCounted` refuses. -/
theorem refusalsCounted_total_lowered_exists (E : Env Nat) :
    ∃ w w' : World Nat, w.RefusalsOk E ∧ refusalsCounted E w = true ∧ w'.height = w.height ∧
      w'.RefusalsOk E ∧ refusalsCounted E w' = false := by
  obtain ⟨w, -, -, -, -, hok, hc, htot, -, -⟩ := counted_world E 2 (by decide)
  have hc' := (refusalsCounted_iff hok).mpr hc
  let r₂ := w.refusals.insert (refusalSpec E) (.total w.origin (refusalWindow w.height))
    (.count (refusalTotal E w - 1))
  exact ⟨w, { w with refusals := r₂ }, hok, hc', rfl,
    refusalsCounted_total_lowered hok hc' (by rw [htot]; exact Nat.le_refl _) rfl rfl rfl⟩

/-- TOOTH (the bound rests on `CountedOk`, not on `refusalFits`): **for every `n` there is a
`RefusalsOk` World holding `n` records**, all in one window, each leaf fitting. So no bound on the
listing follows from the per-leaf check `refusalsFits` alone; `refusals_bounded` uses the
`CountedOk` premise (CODEC's `kernel/refusals-counted`). -/
theorem refusalsOk_bounds_nothing (E : Env Nat) (m : Nat) (n : Nat) :
    ∃ w : World Nat, w.height = 0 ∧ w.RefusalsOk E ∧ (w.refusals.toList.map refusedOne).sum = n := by
  have key : ∀ n, ∃ t : Refusals Nat, Trie.Canon (refusalSpec E) 0 t ∧
      (∀ k v, t.get (refusalSpec E) k = some v → (∃ i, i < n ∧ k = .tx i) ∧ v = .refused 1 0 m) ∧
      t.toList.length = n := by
    intro n
    induction n with
    | zero => exact ⟨.empty, Trie.canon_empty _ 0, fun k v h => by simp [Trie.get_empty] at h, rfl⟩
    | succ n ih =>
        obtain ⟨t, hc, hg, hl⟩ := ih
        refine ⟨t.insert (refusalSpec E) (.tx n) (.refused 1 0 m), Trie.canon_insert _ _ _ hc, ?_, ?_⟩
        · intro k v hk
          rw [Trie.get_insert] at hk
          split at hk
          · rename_i he; cases hk; exact ⟨⟨n, by omega, he⟩, rfl⟩
          · obtain ⟨⟨i, hi, hk'⟩, hv⟩ := hg k v hk
            exact ⟨⟨i, by omega, hk'⟩, hv⟩
        · rw [(Trie.toList_insert_perm (refusalSpec E) hc.1 _ _).length_eq, List.length_append,
            List.length_singleton, List.filter_eq_self.mpr, hl]
          intro p hp
          have := hg p.1 p.2 ((Trie.mem_toList (refusalSpec E) 0 t hc.1 p.1 p.2).mp hp)
          obtain ⟨⟨i, hi, hk⟩, -⟩ := this
          simp only [hk, ne_eq, decide_eq_true_eq, RefusalSlot.tx.injEq]
          omega
  obtain ⟨t, hc, hg, hl⟩ := key n
  refine ⟨{ World.genesis E 0 0 with refusals := t }, rfl, ⟨hc, fun k v hk => ?_⟩, ?_⟩
  · obtain ⟨⟨i, -, rfl⟩, rfl⟩ := hg k v hk
    simp [refusalFits, World.genesis, windowMax_eq, counterLimit_eq]
  · show (t.toList.map refusedOne).sum = n
    rw [sumN_eq_length, hl]
    intro p hp
    obtain ⟨⟨i, -, hk⟩, hv⟩ := hg p.1 p.2 ((Trie.mem_toList (refusalSpec E) 0 t hc.1 p.1 p.2).mp hp)
    obtain ⟨k, v⟩ := p
    simp only at hk hv
    subst hk hv
    rfl

end Nanodregg.Kernel

namespace Nanodregg.Kernel.Receive

open Nanodregg.Kernel

variable {D : Type} [Ord D] [DecidableEq D]

/-- **A refusal past the World's cap is declined, never recorded**: `judgeBy` answers it
`rejected refusalsFull` (a liveness cost on refusal finality, never a verdict on the call). -/
theorem judgeBy_refusalsFull {X : Ctx D} {w : World D} {c : Call D} {auth : Verdict D → Bool}
    {v : Verdict D} (hs : submit X w c = .error v) (hst : v.isStale = false) (ha : auth v = true)
    (hr : World.refuse X.env w (refusedOf X c v) = .error .refusalsFull) :
    judgeBy X w c auth = .declined (.rejected .refusalsFull) := by
  unfold judgeBy
  simp [hs, hst, ha, hr]

/-- **Every World a checked genesis and a fold reach has bounded refusals**: no premise beyond the
genesis check. -/
theorem reach_refusals_bounded {X : Ctx D} {name nonce : ByteArray} {allowance : Nat}
    {founders : List (ByteArray × D)} {w : World D} {l : List (Step D)}
    (h : World.fold X.env (genesisWorld X name nonce allowance founders) l = .ok w) :
    (w.refusals.toList.map refusedOne).sum ≤ 3 * Bounds.refusalsPerWindowMax ∧
      (w.refusals.toList.map countKeyOne).sum ≤ Bounds.refusalsPerWindowMax ∧
      (w.refusals.toList.map totalKeyOne).sum ≤ 1 ∧
      w.refusals.toList.length = (w.refusals.toList.map refusedOne).sum +
        (w.refusals.toList.map countKeyOne).sum + (w.refusals.toList.map totalKeyOne).sum :=
  fold_refusals_bounded (genesisWorld_refusalsOk X name nonce allowance founders)
    (countedOk_of_empty rfl (Nat.le_refl _)) h

open Nanodregg.Codec Nanodregg.Codec.Deployed in
/-- **Deployed**: no premise. Every World the deployed genesis and a fold reach holds at most 49,152
records, 16,384 counts and one total in its refusals trie. -/
theorem deployed_reach_refusals_bounded (program : Program Digest) {name nonce : ByteArray} {allowance : Nat}
    {founders : List (ByteArray × Digest)} {g w : World Digest} {l : List (Step Digest)}
    (hg : genesis (ctx program) name nonce allowance founders = .ok g) (hl : World.fold env g l = .ok w) :
    (w.refusals.toList.map refusedOne).sum ≤ 3 * Bounds.refusalsPerWindowMax ∧
      (w.refusals.toList.map countKeyOne).sum ≤ Bounds.refusalsPerWindowMax ∧
      (w.refusals.toList.map totalKeyOne).sum ≤ 1 ∧
      w.refusals.toList.length = (w.refusals.toList.map refusedOne).sum +
        (w.refusals.toList.map countKeyOne).sum + (w.refusals.toList.map totalKeyOne).sum := by
  obtain ⟨_, rfl⟩ := genesis_ok.mp hg
  exact reach_refusals_bounded (X := ctx program) hl

end Nanodregg.Kernel.Receive
