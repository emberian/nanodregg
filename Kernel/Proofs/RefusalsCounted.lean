/-
# Kernel.Proofs.RefusalsCounted — a World's refusal counts are its records' (KERNEL-50)

A member's window count is a cache of its records: `checkRefusal` reads it in one lookup instead of
scanning. `World.CountedOk` says the cache is exact: every record cost a step that did not raise the
height (records + height ≤ steps), every member's count for the current window is the number of
its records this window, the World's total (KERNEL-55 R1) is the number of all records this window
and sits under the World's origin, and the two windows before hold at most
`Bounds.refusalsPerWindowMax` records each (what `Kernel.Proofs.RefusalsBound` reads). Every reached World holds it (`fold_countedOk`, `reach_countedOk`,
`deployed_reach_refusalsCounted`), and `refusalsCounted` decides it (`refusalsCounted_iff`), so
CODEC's `kernel/refusals-counted` refuses a base holding a count no history produces. The tooth
`refusalsCounted_moved` (and `refusalsCounted_moved_exists`): a World with one member's charge moved
to another still passes `refusalsFits` (`RefusalsOk`), and `refusalsCounted` refuses it; the sim
plant `refusals-counted-plant` builds that World on every seed.
-/
import Kernel.Proofs.Refusals
import Kernel.Proofs.RootedDeployed

namespace Nanodregg.Kernel

variable {D : Type} [Ord D] [DecidableEq D]

/-! ## Sums over a list -/

omit [Ord D] [DecidableEq D] in
theorem sumN_filter_le {α : Type} (g : α → Nat) (q : α → Bool) :
    ∀ l : List α, ((l.filter q).map g).sum ≤ (l.map g).sum
  | [] => by simp
  | x :: l => by
      have := sumN_filter_le g q l
      by_cases hq : q x = true
      · simp [hq]; omega
      · simp [hq]; omega

omit [Ord D] [DecidableEq D] in
theorem le_sumN_of_mem {α : Type} (g : α → Nat) {x : α} : ∀ {l : List α}, x ∈ l → g x ≤ (l.map g).sum
  | [], h => by simp at h
  | y :: l, h => by
      rcases List.mem_cons.mp h with rfl | h
      · simp
      · have := le_sumN_of_mem g h; simp; omega

omit [Ord D] [DecidableEq D] in
theorem exists_pos_of_sumN_pos {α : Type} (g : α → Nat) :
    ∀ {l : List α}, 0 < (l.map g).sum → ∃ x ∈ l, 0 < g x
  | [], h => by simp at h
  | y :: l, h => by
      by_cases hy : 0 < g y
      · exact ⟨y, List.mem_cons_self .., hy⟩
      · simp only [List.map_cons, List.sum_cons] at h
        obtain ⟨x, hx, hp⟩ := exists_pos_of_sumN_pos g (l := l) (by omega)
        exact ⟨x, List.mem_cons_of_mem _ hx, hp⟩

omit [Ord D] [DecidableEq D] in
theorem sumN_eq_zero_of {α : Type} (g : α → Nat) : ∀ {l : List α}, (∀ x ∈ l, g x = 0) → (l.map g).sum = 0
  | [], _ => rfl
  | y :: l, h => by
      simp only [List.map_cons, List.sum_cons]
      rw [h y (List.mem_cons_self ..), sumN_eq_zero_of g (fun x hx => h x (List.mem_cons_of_mem _ hx))]

omit [Ord D] [DecidableEq D] in
theorem sumN_le_of_le {α : Type} (f g : α → Nat) :
    ∀ {l : List α}, (∀ x ∈ l, f x ≤ g x) → (l.map f).sum ≤ (l.map g).sum
  | [], _ => by simp
  | x :: l, h => by
      have h1 := h x (List.mem_cons_self ..)
      have h2 := sumN_le_of_le f g (l := l) (fun y hy => h y (List.mem_cons_of_mem _ hy))
      simp only [List.map_cons, List.sum_cons]; omega

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

omit [Ord D] in
/-- An insert at a key whose entries a sum ignores moves the sum not at all. -/
theorem sumN_insert_zero {E : Env D} (g : WindowSlot D × RefusalLeaf D → Nat) {t : Refusals D}
    (hr : Trie.Routed (refusalSpec E) 0 t) (k : WindowSlot D) (v : RefusalLeaf D) (hg : ∀ v, g (k, v) = 0) :
    ((t.insert (refusalSpec E) k v).toList.map g).sum = (t.toList.map g).sum := by
  cases hk : t.get (refusalSpec E) k with
  | none => rw [Trie.sumN_insert_none _ g hr v hk, hg]; rfl
  | some old =>
      have := Trie.sumN_insert_some _ g hr v hk
      rw [hg, hg] at this; omega

omit [Ord D] in
/-- An insert at a count key moves no sum that ignores count entries. -/
theorem sumN_insert_count {E : Env D} (g : WindowSlot D × RefusalLeaf D → Nat)
    (hg : ∀ m win v, g (.refusal (.count m win), v) = 0) {t : Refusals D} (hr : Trie.Routed (refusalSpec E) 0 t)
    (m : D) (win : UInt64) (v : RefusalLeaf D) :
    ((t.insert (refusalSpec E) (.refusal (.count m win)) v).toList.map g).sum = (t.toList.map g).sum := by
  cases hk : t.get (refusalSpec E) (.refusal (.count m win)) with
  | none => rw [Trie.sumN_insert_none _ g hr v hk, hg]; rfl
  | some old =>
      have := Trie.sumN_insert_some _ g hr v hk
      rw [hg, hg] at this; omega

/-! ## The tally -/

omit [Ord D] in
theorem tallyAt_step (E : Env D) (seed : D) (H : Nat) (m : D) (t : Refusals D)
    (p : WindowSlot D × RefusalLeaf D) :
    tallyAt E seed (tallyStep E seed H t p) (.count m (refusalWindow H)) =
      tallyAt E seed t (.count m (refusalWindow H)) + refusedIn H m p := by
  obtain ⟨k, v⟩ := p
  rcases k with k | k
  case meter => cases k; cases v <;> simp [tallyStep, refusedIn]
  cases k with
  | count m' win => cases v <;> simp [tallyStep, refusedIn]
  | total o win => cases v <;> simp [tallyStep, refusedIn]
  | tx id =>
      cases v with
      | count n => simp [tallyStep, refusedIn]
      | refused h c m' =>
          by_cases hw : (h - 1) / Bounds.windowMax = H / Bounds.windowMax
          · by_cases hm : m' = m
            · subst hm
              simp only [tallyStep, refusedIn, hw, if_true, and_self]
              unfold tallyAt
              rw [Trie.get_insert, if_pos rfl]
            · simp only [tallyStep, refusedIn, hw, hm, if_true, and_true, if_false, Nat.add_zero]
              unfold tallyAt
              rw [Trie.get_insert, if_neg (by simp [Ne.symm hm])]
          · simp [tallyStep, refusedIn, hw]

omit [Ord D] in
theorem tallyAt_foldl (E : Env D) (seed : D) (H : Nat) (m : D) :
    ∀ (l : List (WindowSlot D × RefusalLeaf D)) (t : Refusals D),
      tallyAt E seed (l.foldl (tallyStep E seed H) t) (.count m (refusalWindow H)) =
        tallyAt E seed t (.count m (refusalWindow H)) + (l.map (refusedIn H m)).sum
  | [], t => by simp
  | p :: l, t => by
      rw [List.foldl_cons, tallyAt_foldl E seed H m l, tallyAt_step]
      simp only [List.map_cons, List.sum_cons]; omega

omit [Ord D] in
/-- A tally holds only positive counts of the current window. -/
theorem tally_support (E : Env D) (seed : D) (H : Nat) :
    ∀ (l : List (WindowSlot D × RefusalLeaf D)) (t : Refusals D),
      (∀ k v, t.get (tallySpec E seed) k = some v → ∃ m n, k = .refusal (.count m (refusalWindow H)) ∧ v = .count n ∧ 0 < n) →
      ∀ k v, (l.foldl (tallyStep E seed H) t).get (tallySpec E seed) k = some v →
        ∃ m n, k = .refusal (.count m (refusalWindow H)) ∧ v = .count n ∧ 0 < n
  | [], t, ht => by simpa using ht
  | p :: l, t, ht => by
      rw [List.foldl_cons]
      apply tally_support E seed H l
      intro k v hk
      obtain ⟨k', v'⟩ := p
      rcases k' with k' | k'
      · cases k' with
        | count m' win => cases v' <;> exact ht k v hk
        | total o win => cases v' <;> exact ht k v hk
        | tx id =>
            cases v' with
            | count n => exact ht k v hk
            | refused h c m' =>
                simp only [tallyStep] at hk
                split at hk
                · rw [Trie.get_insert] at hk
                  split at hk
                  · rename_i he; cases hk; exact ⟨m', _, he, rfl, Nat.succ_pos _⟩
                  · exact ht k v hk
                · exact ht k v hk
      · cases k'; cases v' <;> exact ht k v hk

omit [Ord D] in
/-- **The tally at a count key**: the member's records of window `H / windowMax`, where it has any. -/
theorem refusalTally_get (E : Env D) (seed : D) (H : Nat) (l : List (WindowSlot D × RefusalLeaf D))
    (m : D) (win : UInt64) :
    (refusalTally E seed H l).get (tallySpec E seed) (.refusal (.count m win)) =
      if win = refusalWindow H ∧ 0 < (l.map (refusedIn H m)).sum then
        some (.count (l.map (refusedIn H m)).sum) else none := by
  have hs := tally_support E seed H l .empty (fun k v h => by simp [Trie.get_empty] at h)
  have ht := tallyAt_foldl E seed H m l .empty
  have h0 : tallyAt E seed (Trie.T.empty : Refusals D) (.count m (refusalWindow H)) = 0 := rfl
  rw [h0, Nat.zero_add] at ht
  unfold refusalTally
  cases hg : (l.foldl (tallyStep E seed H) .empty).get (tallySpec E seed) (.refusal (.count m win)) with
  | some v =>
      obtain ⟨m', n, hk, rfl, hn⟩ := hs _ _ hg
      cases hk
      unfold tallyAt at ht
      rw [hg] at ht
      simp only at ht
      rw [if_pos ⟨rfl, by omega⟩, ← ht]
  | none =>
      by_cases hw : win = refusalWindow H
      · subst hw
        unfold tallyAt at ht
        rw [hg] at ht
        simp only at ht
        rw [if_neg (by omega)]
      · rw [if_neg (fun h => hw h.1)]

/-! ## The invariant -/

/-- **A World's refusal counts are its records'**: records + height ≤ steps; every member's count
for the current window is the number of its records this window; the World's total for the current
window is the number of all records this window (KERNEL-55 R1); each of the two windows before holds
at most `Bounds.refusalsPerWindowMax` records; every total leaf is under the World's origin; and (KERNEL-68)
the meter leaves are at most one more than the heights elapsed in the current window. -/
def World.CountedOk (E : Env D) (w : World D) : Prop :=
  (w.refusals.toList.map refusedOne).sum + w.height ≤ w.steps ∧
    (∀ m, refusalCount E w m = (w.refusals.toList.map (refusedIn w.height m)).sum) ∧
    refusalTotal E w = (w.refusals.toList.map (refusedWin (w.height / Bounds.windowMax))).sum ∧
    (w.refusals.toList.map (refusedWin (w.height / Bounds.windowMax - 1))).sum ≤ Bounds.refusalsPerWindowMax ∧
    (w.refusals.toList.map (refusedWin (w.height / Bounds.windowMax - 2))).sum ≤ Bounds.refusalsPerWindowMax ∧
    (∀ o win v, w.refusalAt E (.total o win) = some v → o = w.origin) ∧
    (w.refusals.toList.map meterKeyOne).sum ≤ w.height % Bounds.windowMax + 1

omit [Ord D] [DecidableEq D] in
/-- Two consecutive windows have different names (UInt64 never wraps onto its predecessor). -/
theorem refusalWindow_succ_ne {H : Nat} (hz : (H + 1) % Bounds.windowMax = 0) :
    refusalWindow (H + 1) ≠ refusalWindow H := by
  unfold refusalWindow
  intro he
  have := congrArg UInt64.toNat he
  rw [UInt64.toNat_ofNat', UInt64.toNat_ofNat'] at this
  have hq : (H + 1) / Bounds.windowMax = H / Bounds.windowMax + 1 := by
    rw [windowMax_eq] at hz ⊢; omega
  rw [hq] at this
  omega

/-- **`refusalsCounted` decides the invariant** on every `RefusalsOk` World. -/
theorem refusalsCounted_iff {E : Env D} {w : World D} (hw : w.RefusalsOk E) :
    refusalsCounted E w = true ↔ w.CountedOk E := by
  have hmem : ∀ k v, (k, v) ∈ w.refusals.toList ↔ w.refusals.get (refusalSpec E) k = some v :=
    fun k v => Trie.mem_toList (refusalSpec E) 0 w.refusals hw.1.1 k v
  unfold refusalsCounted World.CountedOk
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
  constructor
  · rintro ⟨⟨⟨h1, hp1, hp2⟩, hall⟩, hm⟩
    have hrec : ∀ id h c mb, (WindowSlot.refusal (.tx id), RefusalLeaf.refused h c mb) ∈ w.refusals.toList →
        (h - 1) / Bounds.windowMax = w.height / Bounds.windowMax →
        (w.refusalAt E (.count mb (refusalWindow w.height))).isSome = true ∧
          (w.refusalAt E (.total w.origin (refusalWindow w.height))).isSome = true := by
      intro id h c mb hp hwin
      have := hall _ hp
      simp only [hwin, decide_true, Bool.not_true, Bool.false_or, Bool.and_eq_true] at this
      exact this
    refine ⟨h1, fun m => ?_, ?_, hp1, hp2, ?_, hm⟩
    · unfold refusalCount
      cases hg : w.refusalAt E (.count m (refusalWindow w.height)) with
      | some v =>
          cases v with
          | refused h c mb =>
              have := hw.2 _ _ hg; simp [refusalFits] at this
          | count n =>
              have := hall _ ((hmem (.refusal _) _).mpr hg)
              simp only [decide_eq_true_eq] at this
              rw [refusalTally_get] at this
              split at this
              · cases this; rfl
              · cases this
      | none =>
          simp only
          apply Eq.symm
          apply Nat.eq_zero_of_not_pos
          intro hpos
          obtain ⟨⟨k, v⟩, hp, hpos'⟩ := exists_pos_of_sumN_pos _ hpos
          rcases k with k | k
          · cases k with
            | count m' win => cases v <;> simp [refusedIn] at hpos'
            | total o win => cases v <;> simp [refusedIn] at hpos'
            | tx id =>
                cases v with
                | count n => simp [refusedIn] at hpos'
                | refused h c mb =>
                    simp only [refusedIn] at hpos'
                    split at hpos'
                    · rename_i hc
                      obtain ⟨rfl, hwin⟩ := hc
                      have := (hrec id h c _ hp hwin).1
                      unfold World.refusalAt at this hg
                      rw [hg] at this; cases this
                    · simp at hpos'
          · cases k; cases v <;> simp [refusedIn] at hpos'
    · unfold refusalTotal
      cases hg : w.refusalAt E (.total w.origin (refusalWindow w.height)) with
      | some v =>
          cases v with
          | refused h c mb => have := hw.2 _ _ hg; simp [refusalFits] at this
          | count n =>
              have := hall _ ((hmem (.refusal _) _).mpr hg)
              simp only [decide_eq_true_eq] at this
              exact this.2.2
      | none =>
          simp only
          apply Eq.symm
          apply Nat.eq_zero_of_not_pos
          intro hpos
          obtain ⟨⟨k, v⟩, hp, hpos'⟩ := exists_pos_of_sumN_pos _ hpos
          rcases k with k | k
          · cases k with
            | count m' win => cases v <;> simp [refusedWin] at hpos'
            | total o win => cases v <;> simp [refusedWin] at hpos'
            | tx id =>
                cases v with
                | count n => simp [refusedWin] at hpos'
                | refused h c mb =>
                    simp only [refusedWin] at hpos'
                    split at hpos'
                    · rename_i hwin
                      have := (hrec id h c mb hp hwin).2
                      unfold World.refusalAt at this hg
                      rw [hg] at this; cases this
                    · simp at hpos'
          · cases k; cases v <;> simp [refusedWin] at hpos'
    · intro o win v hg
      cases v with
      | refused h c mb => have := hw.2 _ _ hg; simp [refusalFits] at this
      | count n =>
          have := hall _ ((hmem (.refusal _) _).mpr hg)
          simp only [decide_eq_true_eq] at this
          exact this.1
  · rintro ⟨h1, hcount, htot, hp1, hp2, horig, hm⟩
    refine ⟨⟨⟨h1, hp1, hp2⟩, ?_⟩, hm⟩
    rintro ⟨k, v⟩ hp
    have hg := (hmem _ _).mp hp
    rcases k with k | k
    case meter => cases k; cases v <;> rfl
    cases k with
    | count m win =>
        cases v with
        | refused h c mb => trivial
        | count n =>
            simp only [decide_eq_true_eq]
            have hf := hw.2 _ _ hg
            simp only [refusalFits, decide_eq_true_eq] at hf
            obtain ⟨rfl, hn, -⟩ := hf
            have hc := hcount m
            unfold refusalCount World.refusalAt at hc
            rw [hg] at hc
            simp only at hc
            rw [refusalTally_get, if_pos ⟨rfl, by omega⟩, ← hc]
    | total o win =>
        cases v with
        | refused h c mb => trivial
        | count n =>
            simp only [decide_eq_true_eq]
            have hf := hw.2 _ _ hg
            simp only [refusalFits, decide_eq_true_eq] at hf
            obtain ⟨rfl, -, -⟩ := hf
            have ho := horig _ _ _ hg
            subst ho
            refine ⟨rfl, rfl, ?_⟩
            unfold refusalTotal World.refusalAt at htot
            rw [hg] at htot
            exact htot
    | tx id =>
        cases v with
        | count n => trivial
        | refused h c mb =>
            simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, Bool.and_eq_true]
            by_cases hwin : (h - 1) / Bounds.windowMax = w.height / Bounds.windowMax
            · right
              refine ⟨?_, ?_⟩
              · have hle := le_sumN_of_mem (refusedIn w.height mb) hp
                simp only [refusedIn, hwin, and_self, if_true] at hle
                have hc := hcount mb
                unfold refusalCount at hc
                cases hr : w.refusalAt E (.count mb (refusalWindow w.height)) with
                | some _ => rfl
                | none => rw [hr] at hc; simp only at hc; omega
              · have hle := le_sumN_of_mem (refusedWin (w.height / Bounds.windowMax)) hp
                simp only [refusedWin, hwin, if_true] at hle
                unfold refusalTotal at htot
                cases hr : w.refusalAt E (.total w.origin (refusalWindow w.height)) with
                | some _ => rfl
                | none => rw [hr] at htot; simp only at htot; omega
            · left; exact hwin

/-- **The counts are the records' on a World that passes `refusalsCounted`**: the reader the codec's
refusal hands a decoded base. -/
theorem refusalCount_eq_of_counted {E : Env D} {w : World D} (hw : w.RefusalsOk E)
    (hc : refusalsCounted E w = true) (m : D) :
    refusalCount E w m = (w.refusals.toList.map (refusedIn w.height m)).sum :=
  ((refusalsCounted_iff hw).mp hc).2.1 m

/-! ## Every step keeps it -/

theorem countedOk_of_empty {E : Env D} {w : World D} (h : w.refusals = .empty) (hs : w.height ≤ w.steps) :
    w.CountedOk E := by
  refine ⟨by rw [h]; show 0 + w.height ≤ w.steps; omega, fun m => ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold refusalCount World.refusalAt
    rw [h]; rfl
  · unfold refusalTotal World.refusalAt
    rw [h]; rfl
  · rw [h]; exact Nat.zero_le _
  · rw [h]; exact Nat.zero_le _
  · intro o win v hg
    unfold World.refusalAt at hg; rw [h] at hg; cases hg
  · rw [h]; exact Nat.zero_le _

/-- A recorded refusal adds its one record to every sum over the listing that ignores count and
total entries. -/
theorem refuse_sumN {E : Env D} {w w' : World D} {r : Refused D} (hw : w.RefusalsOk E)
    (h : World.refuse E w r = .ok w') (g : WindowSlot D × RefusalLeaf D → Nat)
    (hg : ∀ m win v, g (.refusal (.count m win), v) = 0) (hgt : ∀ o win v, g (.refusal (.total o win), v) = 0) :
    (w'.refusals.toList.map g).sum =
      (w.refusals.toList.map g).sum + g (.refusal (.tx r.txId), .refused (w.height + 1) r.code r.member) := by
  obtain ⟨-, -, -, -, hnot, -⟩ := refuse_facts h
  have hnone : w.refusals.get (refusalSpec E) (.refusal (.tx r.txId)) = none := by
    cases hk : w.refusals.get (refusalSpec E) (.refusal (.tx r.txId)) with
    | none => rfl
    | some v =>
        cases v with
        | refused hh code mb => exact absurd hk (hnot hh code mb)
        | count n => have := hw.2 _ _ hk; simp [refusalFits] at this
  obtain ⟨_, rfl⟩ := refuse_ok h
  rw [commitRefusal_refusals,
    sumN_insert_zero g (Trie.routed_insert _ _ _ (Trie.routed_insert _ _ _ hw.1.1)) _ _ (hgt _ _),
    sumN_insert_count g hg (Trie.routed_insert _ _ _ hw.1.1), Trie.sumN_insert_none _ g hw.1.1 _ hnone]

theorem refuse_countedOk {E : Env D} {w w' : World D} {r : Refused D} (hw : w.RefusalsOk E)
    (hc : w.CountedOk E) (h : World.refuse E w r = .ok w') : w'.CountedOk E := by
  have hh := (refuse_frame h).2.2.1
  have ho := (refuse_frame h).2.2.2.2
  obtain ⟨-, -, -, -, -, -, htl⟩ := refuse_facts h
  obtain ⟨hc1, hc2, hc3, hc4, hc5, hc6, hc7⟩ := hc
  have hs : ∀ k, (w'.refusals.toList.map (refusedWin k)).sum =
      (w.refusals.toList.map (refusedWin k)).sum + (if w.height / Bounds.windowMax = k then 1 else 0) := by
    intro k
    rw [refuse_sumN hw h (refusedWin k) (fun _ _ v => by cases v <;> rfl) (fun _ _ v => by cases v <;> rfl)]
    simp [refusedWin]
  refine ⟨?_, fun m => ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [refuse_sumN hw h refusedOne (fun _ _ v => by cases v <;> rfl) (fun _ _ v => by cases v <;> rfl), hh,
      refuse_steps h]
    simp only [refusedOne]; omega
  · rw [refuse_refusalCount h m, hh,
      refuse_sumN hw h (refusedIn w.height m) (fun _ _ v => by cases v <;> rfl) (fun _ _ v => by cases v <;> rfl),
      hc2 m]
    simp only [refusedIn, Nat.add_sub_cancel, and_true]
    by_cases hm : m = r.member
    · subst hm; simp
    · simp [hm, Ne.symm hm]
  · have ht : refusalTotal E w' = refusalTotal E w + 1 := by
      unfold refusalTotal
      rw [ho, hh, refuse_refusalAt h, if_pos rfl]
      rfl
    rw [ht, hh, hs, hc3, if_pos rfl]
  · rw [hh, hs]
    by_cases he : w.height / Bounds.windowMax = w.height / Bounds.windowMax - 1
    · rw [if_pos he, ← he, ← hc3]; omega
    · rw [if_neg he]; omega
  · rw [hh, hs]
    by_cases he : w.height / Bounds.windowMax = w.height / Bounds.windowMax - 2
    · rw [if_pos he, ← he, ← hc3]; omega
    · rw [if_neg he]; omega
  · intro o win v hg
    rw [refuse_refusalAt h] at hg
    rw [ho]
    split at hg
    · rename_i he; cases he; rfl
    · split at hg
      · rename_i he; cases he
      · split at hg
        · rename_i he; cases he
        · exact hc6 o win v hg
  · -- the meter leaves (KERNEL-68): a refusal writes none, and the height stays
    rw [refuse_sumN hw h meterKeyOne (fun _ _ v => by cases v <;> rfl) (fun _ _ v => by cases v <;> rfl), hh]
    simp only [meterKeyOne, Nat.add_zero]
    exact hc7

theorem admit_countedOk {E : Env D} {w w' : World D} {t : Turn D} (hw : w.RefusalsOk E)
    (hc : w.CountedOk E) (h : World.admit E w t = .ok w') : w'.CountedOk E := by
  have hh := admit_height h
  have hst := admit_steps h
  have ho : w'.origin = w.origin := step_origin (s := .turn t) h
  -- the meter's write (KERNEL-68): one insert at a meter key, or nothing. The trie it leaves is
  -- canonical, every sum over records ignores the new entry, and every refusal-window key reads as before.
  have hRc : Trie.Canon (refusalSpec E) 0 (commitMeter E w t) := commitMeter_canon hw.1
  have hr : w'.refusals = pruneRefusals E (w.height + 1) (commitMeter E w t) := by
    obtain ⟨_, _, rfl⟩ := admit_ok h; exact commit_refusals
  have hsum : ∀ g : WindowSlot D × RefusalLeaf D → Nat, (∀ k v, g (.meter k, v) = 0) →
      ((commitMeter E w t).toList.map g).sum = (w.refusals.toList.map g).sum := by
    intro g hg
    unfold commitMeter
    split
    · rfl
    · exact sumN_insert_zero g hw.1.1 _ _ (hg _)
  have hmemR : ∀ k v, (.refusal k, v) ∈ (commitMeter E w t).toList →
      w.refusals.get (refusalSpec E) (.refusal k) = some v := by
    intro k v hp
    have := (Trie.mem_toList (refusalSpec E) 0 _ hRc.1 _ _).mp hp
    exact (commitMeter_get_refusal k).symm.trans this
  obtain ⟨hc1, hc2, hc3, hc4, hc5, hc6, hc7⟩ := hc
  have hc6' : ∀ o win v, w'.refusalAt E (.total o win) = some v → o = w'.origin := by
    intro o win v hg
    rw [ho]
    rw [admit_refusalAt hw.1 h] at hg
    split at hg
    · exact hc6 o win v (Option.filter_eq_some_iff.mp hg).1
    · exact hc6 o win v hg
  by_cases hz : (w.height + 1) % Bounds.windowMax = 0
  · have hl : w'.refusals.toList = (commitMeter E w t).toList.filter fun p => keptRefusal (w.height + 1) p.1 p.2 := by
      rw [hr]; unfold pruneRefusals; rw [if_pos hz]
      exact Trie.toList_retainAt (refusalSpec E) _ [] 0 _ hRc.1 (fun _ _ _ _ _ _ h => by simp at h)
    have hq : (w.height + 1) / Bounds.windowMax = w.height / Bounds.windowMax + 1 := by
      rw [windowMax_eq] at hz ⊢; omega
    -- no record of the old World is of the new window
    have hold : ∀ p ∈ (commitMeter E w t).toList, ∀ m,
        refusedIn (w.height + 1) m p = 0 ∧ refusedWin ((w.height + 1) / Bounds.windowMax) p = 0 := by
      intro p hp m
      obtain ⟨k, v⟩ := p
      rcases k with k | k
      · cases k with
        | count _ _ => cases v <;> exact ⟨rfl, rfl⟩
        | total _ _ => cases v <;> exact ⟨rfl, rfl⟩
        | tx id =>
            cases v with
            | count _ => exact ⟨rfl, rfl⟩
            | refused hh' c mb =>
                have hf := hw.2 _ _ (hmemR _ _ hp)
                simp only [refusalFits, decide_eq_true_eq] at hf
                have : (hh' - 1) / Bounds.windowMax ≤ w.height / Bounds.windowMax :=
                  Nat.div_le_div_right (by omega)
                refine ⟨?_, ?_⟩
                · simp only [refusedIn]
                  rw [if_neg]
                  rintro ⟨-, hwin⟩
                  omega
                · simp only [refusedWin]
                  rw [if_neg]
                  omega
      · cases k; cases v <;> exact ⟨rfl, rfl⟩
    have hle : ∀ k, (w'.refusals.toList.map (refusedWin k)).sum ≤ (w.refusals.toList.map (refusedWin k)).sum := by
      intro k
      rw [hl, ← hsum (refusedWin k) (fun _ v => by cases v <;> rfl)]
      exact sumN_filter_le _ _ _
    refine ⟨?_, fun m => ?_, ?_, ?_, ?_, hc6', ?_⟩
    · rw [hl, hh, hst]
      have := sumN_filter_le refusedOne (fun p => keptRefusal (w.height + 1) p.1 p.2) (commitMeter E w t).toList
      rw [hsum refusedOne (fun _ v => by cases v <;> rfl)] at this
      omega
    · have h0 : refusalCount E w' m = 0 := by
        unfold refusalCount
        rw [admit_refusalAt hw.1 h, if_pos hz, hh]
        cases hg : w.refusalAt E (.count m (refusalWindow (w.height + 1))) with
        | none => rfl
        | some v =>
            have hf := hw.2 _ _ hg
            cases v with
            | refused _ _ _ => simp [refusalFits] at hf
            | count n =>
                simp only [refusalFits, decide_eq_true_eq] at hf
                exact absurd hf.1 (refusalWindow_succ_ne hz)
      rw [h0, hl, hh]
      apply Eq.symm
      apply sumN_eq_zero_of
      intro p hp
      exact (hold p (List.mem_filter.mp hp).1 m).1
    · have h0 : refusalTotal E w' = 0 := by
        unfold refusalTotal
        rw [admit_refusalAt hw.1 h, if_pos hz, hh, ho]
        cases hg : w.refusalAt E (.total w.origin (refusalWindow (w.height + 1))) with
        | none => rfl
        | some v =>
            have hf := hw.2 _ _ hg
            cases v with
            | refused _ _ _ => simp [refusalFits] at hf
            | count n =>
                simp only [refusalFits, decide_eq_true_eq] at hf
                exact absurd hf.1 (refusalWindow_succ_ne hz)
      rw [h0, hl, hh]
      apply Eq.symm
      apply sumN_eq_zero_of
      intro p hp
      exact (hold p (List.mem_filter.mp hp).1 w.origin).2
    · rw [hh, hq, Nat.add_sub_cancel]
      have := hle (w.height / Bounds.windowMax)
      have := refusalTotal_le hw
      omega
    · rw [hh, hq]
      have h2 : w.height / Bounds.windowMax + 1 - 2 = w.height / Bounds.windowMax - 1 := by omega
      rw [h2]
      have := hle (w.height / Bounds.windowMax - 1)
      omega
    · -- the meter leaves (KERNEL-68): at a window's start only the turn's own survives the prune
      rw [hl, hh]
      have hnd : (((commitMeter E w t).toList.filter fun p => keptRefusal (w.height + 1) p.1 p.2).map
          Prod.fst).Nodup :=
        (List.filter_sublist.map Prod.fst).nodup (Trie.toList_nodup (refusalSpec E) 0 _ hRc.1)
      have hle1 := sumN_key_le_one (.meter (.ticks t.member (refusalWindow (w.height + 1)))) hnd
      have hb := sumN_le_of_le meterKeyOne
        (fun q : WindowSlot D × RefusalLeaf D =>
          if q.1 = .meter (.ticks t.member (refusalWindow (w.height + 1))) then 1 else 0)
        (l := (commitMeter E w t).toList.filter fun p => keptRefusal (w.height + 1) p.1 p.2) (by
          intro q hq
          obtain ⟨hq, hkept⟩ := List.mem_filter.mp hq
          obtain ⟨k, v⟩ := q
          rcases k with k | k
          · exact Nat.zero_le _
          · obtain ⟨m, win⟩ := k
            by_cases hown : MeterSlot.ticks m win = .ticks t.member (refusalWindow (w.height + 1))
            · rw [hown]; simp [meterKeyOne]
            · exfalso
              have hg : (commitMeter E w t).get (refusalSpec E) (.meter (.ticks m win)) = some v :=
                (Trie.mem_toList (refusalSpec E) 0 _ hRc.1 _ _).mp hq
              rw [commitMeter_get_meter_ne hown] at hg
              have hf := hw.2 _ _ hg
              cases v with
              | refused _ _ _ => simp [refusalFits] at hf
              | count n =>
                  simp only [refusalFits, decide_eq_true_eq] at hf
                  simp only [keptRefusal, decide_eq_true_eq] at hkept
                  rw [hf.1] at hkept
                  exact refusalWindow_succ_ne hz hkept.symm)
      rw [hz]
      omega
  · have hl : w'.refusals = commitMeter E w t := by rw [hr]; unfold pruneRefusals; rw [if_neg hz]
    have hq : (w.height + 1) / Bounds.windowMax = w.height / Bounds.windowMax := by
      rw [windowMax_eq] at hz ⊢; omega
    have hfun : ∀ m, refusedIn (D := D) (w.height + 1) m = refusedIn w.height m := by
      intro m; funext p
      obtain ⟨k, v⟩ := p
      rcases k with k | k <;> cases k <;> cases v <;> simp only [refusedIn, hq]
    have hwin : refusalWindow (w.height + 1) = refusalWindow w.height := by
      unfold refusalWindow; rw [hq]
    refine ⟨?_, fun m => ?_, ?_, ?_, ?_, hc6', ?_⟩
    · rw [hl, hh, hst, hsum refusedOne (fun _ v => by cases v <;> rfl)]; omega
    · rw [admit_refusalCount hw.1 h hz m, hl, hh, hfun m, hsum (refusedIn w.height m) (fun _ v => by cases v <;> rfl)]
      exact hc2 m
    · have ht : refusalTotal E w' = refusalTotal E w := by
        unfold refusalTotal
        rw [admit_refusalAt hw.1 h, if_neg hz, hh, ho, hwin]
      rw [ht, hl, hh, hq, hsum (refusedWin (w.height / Bounds.windowMax)) (fun _ v => by cases v <;> rfl)]
      exact hc3
    · rw [hl, hh, hq, hsum (refusedWin (w.height / Bounds.windowMax - 1)) (fun _ v => by cases v <;> rfl)]
      exact hc4
    · rw [hl, hh, hq, hsum (refusedWin (w.height / Bounds.windowMax - 2)) (fun _ v => by cases v <;> rfl)]
      exact hc5
    · -- the meter leaves (KERNEL-68): one more at most, as the height is one more
      rw [hl, hh]
      have hq1 : (w.height + 1) % Bounds.windowMax = w.height % Bounds.windowMax + 1 := by
        rw [windowMax_eq] at hz ⊢; omega
      rw [hq1]
      unfold commitMeter
      split
      · omega
      · cases hg : w.refusals.get (refusalSpec E) (.meter (.ticks t.member (refusalWindow (w.height + 1)))) with
        | none =>
            rw [Trie.sumN_insert_none _ meterKeyOne hw.1.1 _ hg]
            simp only [meterKeyOne]; omega
        | some old =>
            have := Trie.sumN_insert_some _ meterKeyOne hw.1.1
              (RefusalLeaf.count (ticksUsed E w t.member + t.ticks)) hg
            simp only [meterKeyOne] at this; omega

theorem step_countedOk {E : Env D} {w w' : World D} {s : Step D} (hw : w.RefusalsOk E)
    (hc : w.CountedOk E) (h : World.step E w s = .ok w') : w'.CountedOk E := by
  cases s with
  | turn t => exact admit_countedOk hw hc h
  | refusal r => exact refuse_countedOk hw hc h

/-- **Every fold keeps the counts the records'.** -/
theorem fold_countedOk {E : Env D} {w w' : World D} {l : List (Step D)} (hw : w.RefusalsOk E)
    (hc : w.CountedOk E) (h : World.fold E w l = .ok w') : w'.CountedOk E :=
  (fold_keeps (P := fun v => v.RefusalsOk E ∧ v.CountedOk E)
    (fun hp ha => ⟨admit_refusalsOk hp.1 ha, admit_countedOk hp.1 hp.2 ha⟩)
    (fun hp hr => ⟨refuse_refusalsOk hp.1 hr, refuse_countedOk hp.1 hp.2 hr⟩) ⟨hw, hc⟩ h).2

/-- **A fold's World passes `refusalsCounted`**, so the codec's refusal never refuses a base a fold
wrote. -/
theorem fold_refusalsCounted {E : Env D} {w w' : World D} {l : List (Step D)} (hw : w.RefusalsOk E)
    (hc : w.CountedOk E) (h : World.fold E w l = .ok w') : refusalsCounted E w' = true :=
  (refusalsCounted_iff (fold_refusalsOk hw h)).mpr (fold_countedOk hw hc h)

/-! ## The tooth -/

/-- TOOTH (`refusalsCounted`): **a charge moved from one member to another is refused, and by this
check alone.** On a World that passes the check, lower `m`'s count by one and raise `m'`'s by one:
the result still holds only leaves that fit (`RefusalsOk`, so `refusalsFits` admits it), and
`refusalsCounted` refuses it. The sum of the counts is unchanged (`refusalsCounted_moved_sum`), so a
check of the sum alone would pass it. That the rest of the World-wire ladder (journal, disjoint,
steps) also admits such a World is CODEC's concrete plant `world_refuses_moved_charge`. -/
theorem refusalsCounted_moved {E : Env D} {w w' : World D} (hw : w.RefusalsOk E)
    (hc : refusalsCounted E w = true) {m m' : D} (hne : m ≠ m') (hm : 2 ≤ refusalCount E w m)
    (hm' : refusalCount E w m' < Bounds.refusalsPerWindow)
    (hr : w'.refusals =
      (w.refusals.insert (refusalSpec E) (.refusal (.count m (refusalWindow w.height))) (.count (refusalCount E w m - 1))).insert
        (refusalSpec E) (.refusal (.count m' (refusalWindow w.height))) (.count (refusalCount E w m' + 1)))
    (hh : w'.height = w.height) :
    w'.RefusalsOk E ∧ refusalsCounted E w' = false := by
  have hle := refusalCount_le hw m
  have hok : w'.RefusalsOk E := by
    refine ⟨?_, fun k v hk => ?_⟩
    · unfold World.RefusalsCanon; rw [hr]
      exact Trie.canon_insert _ _ _ (Trie.canon_insert _ _ _ hw.1)
    · rw [hh]
      rw [hr, Trie.get_insert, Trie.get_insert] at hk
      split at hk
      · rename_i he; cases hk; subst he
        simp only [refusalFits, decide_eq_true_eq]; exact ⟨trivial, by omega, by omega⟩
      · split at hk
        · rename_i _ he; cases hk; subst he
          simp only [refusalFits, decide_eq_true_eq]; exact ⟨trivial, by omega, by omega⟩
        · exact hw.2 k v hk
  refine ⟨hok, ?_⟩
  cases hb : refusalsCounted E w' with
  | false => rfl
  | true =>
      exfalso
      have h' := refusalCount_eq_of_counted hok hb m
      have h0 := refusalCount_eq_of_counted hw hc m
      have hcnt : refusalCount E w' m = refusalCount E w m - 1 := by
        conv => lhs; unfold refusalCount World.refusalAt
        rw [hr, hh, Trie.get_insert, Trie.get_insert, if_neg (by simp [hne]),
          if_pos rfl]
      have hsum : (w'.refusals.toList.map (refusedIn w'.height m)).sum =
          (w.refusals.toList.map (refusedIn w.height m)).sum := by
        rw [hr, hh,
          sumN_insert_count _ (fun _ _ v => by cases v <;> rfl) (Trie.routed_insert _ _ _ hw.1.1),
          sumN_insert_count _ (fun _ _ v => by cases v <;> rfl) hw.1.1]
      omega

/-- **The moved World has the same sum of counts** (`refusalsCounted_moved`'s other half): the
refused sum form (Σ counts = this window's records) cannot tell the two Worlds apart, since the
records are untouched too. -/
theorem refusalsCounted_moved_sum {E : Env D} {w w' : World D} (hw : w.RefusalsOk E) {m m' : D}
    (hne : m ≠ m') (hm : 2 ≤ refusalCount E w m)
    (hr : w'.refusals =
      (w.refusals.insert (refusalSpec E) (.refusal (.count m (refusalWindow w.height))) (.count (refusalCount E w m - 1))).insert
        (refusalSpec E) (.refusal (.count m' (refusalWindow w.height))) (.count (refusalCount E w m' + 1))) :
    (w'.refusals.toList.map fun p => match p with | (.refusal (.count _ _), .count n) => n | _ => 0).sum =
      (w.refusals.toList.map fun p => match p with | (.refusal (.count _ _), .count n) => n | _ => 0).sum := by
  let g : WindowSlot D × RefusalLeaf D → Nat := fun p => match p with | (.refusal (.count _ _), .count n) => n | _ => 0
  show (w'.refusals.toList.map g).sum = (w.refusals.toList.map g).sum
  obtain ⟨c, hc⟩ : ∃ c, refusalCount E w m = c := ⟨_, rfl⟩
  obtain ⟨c', hc'⟩ : ∃ c', refusalCount E w m' = c' := ⟨_, rfl⟩
  rw [hc, hc'] at hr
  rw [hc] at hm
  have h1 : w.refusals.get (refusalSpec E) (.refusal (.count m (refusalWindow w.height))) = some (.count c) := by
    have hc2 := hc
    unfold refusalCount World.refusalAt at hc2
    split at hc2
    · rename_i n hg; rw [hg, hc2]
    · omega
  have hr1 := Trie.routed_insert (refusalSpec E) (.refusal (.count m (refusalWindow w.height))) (.count (c - 1)) hw.1.1
  have s1 := Trie.sumN_insert_some _ g hw.1.1 (.count (c - 1)) h1
  have hk2 : (w.refusals.insert (refusalSpec E) (.refusal (.count m (refusalWindow w.height)))
      (.count (c - 1))).get (refusalSpec E) (.refusal (.count m' (refusalWindow w.height))) =
      w.refusals.get (refusalSpec E) (.refusal (.count m' (refusalWindow w.height))) := by
    rw [Trie.get_insert, if_neg (by simp [Ne.symm hne])]
  rw [hr]
  cases h2 : w.refusals.get (refusalSpec E) (.refusal (.count m' (refusalWindow w.height))) with
  | none =>
      have hc0 : c' = 0 := by
        rw [← hc']; unfold refusalCount World.refusalAt; rw [h2]
      have s2 := Trie.sumN_insert_none _ g hr1 (.count (c' + 1)) (hk2.trans h2)
      simp only [g] at s1 s2 ⊢; omega
  | some v =>
      cases v with
      | refused _ _ _ => have := hw.2 _ _ h2; simp [refusalFits] at this
      | count n =>
          have hn : c' = n := by rw [← hc']; unfold refusalCount World.refusalAt; rw [h2]
          have s2 := Trie.sumN_insert_some _ g hr1 (.count (c' + 1)) (hk2.trans h2)
          simp only [g] at s1 s2 ⊢; omega

/-- The tooth is not vacuous: on every World that passes the check and has a member with two charges
this window and another with room, the moved World exists (the World with only its refusals
replaced). -/
theorem refusalsCounted_moved_exists {E : Env D} {w : World D} (hw : w.RefusalsOk E)
    (hc : refusalsCounted E w = true) {m m' : D} (hne : m ≠ m') (hm : 2 ≤ refusalCount E w m)
    (hm' : refusalCount E w m' < Bounds.refusalsPerWindow) :
    ∃ w' : World D, w'.height = w.height ∧ w'.RefusalsOk E ∧ refusalsCounted E w' = false :=
  let r₂ := (w.refusals.insert (refusalSpec E) (.refusal (.count m (refusalWindow w.height)))
    (.count (refusalCount E w m - 1))).insert (refusalSpec E) (.refusal (.count m' (refusalWindow w.height)))
    (.count (refusalCount E w m' + 1))
  ⟨{ w with refusals := r₂ }, rfl, refusalsCounted_moved hw hc hne hm hm' rfl rfl⟩

/-! ## On every reached World -/

end Nanodregg.Kernel

namespace Nanodregg.Kernel.Receive

open Nanodregg.Kernel

variable {D : Type} [Ord D] [DecidableEq D]

/-- **Every World a checked genesis and a fold reach passes `refusalsCounted`.** -/
theorem reach_refusalsCounted {X : Ctx D} {name nonce : ByteArray} {allowance : Nat}
    {founders : List (ByteArray × D)} {auth : Authority} {w : World D} {l : List (Step D)}
    (h : World.fold X.env (genesisWorld X name nonce allowance founders auth) l = .ok w) :
    refusalsCounted X.env w = true :=
  fold_refusalsCounted (genesisWorld_refusalsOk X name nonce allowance founders auth)
    (countedOk_of_empty rfl (Nat.le_refl _)) h

open Nanodregg.Codec Nanodregg.Codec.Deployed in
/-- **Deployed**: no premise. -/
theorem deployed_reach_refusalsCounted (program : Program Digest) {name nonce : ByteArray} {allowance : Nat}
    {founders : List (ByteArray × Digest)} {auth : Authority} {g w : World Digest} {l : List (Step Digest)}
    (hg : genesis (ctx program) name nonce allowance founders auth = .ok g) (hl : World.fold env g l = .ok w) :
    refusalsCounted env w = true := by
  obtain ⟨_, rfl⟩ := genesis_ok.mp hg
  exact reach_refusalsCounted (X := ctx program) hl

end Nanodregg.Kernel.Receive
