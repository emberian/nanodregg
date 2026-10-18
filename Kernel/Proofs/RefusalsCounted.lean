/-
# Kernel.Proofs.RefusalsCounted — a World's refusal counts are its records' (KERNEL-50)

A member's window count is a cache of its records: `checkRefusal` reads it in one lookup instead of
scanning. `World.CountedOk` says the cache is exact: every record cost a step that did not raise the
height (records + height ≤ steps), and every member's count for the current window is the number of
its records this window. Every reached World holds it (`fold_countedOk`, `reach_countedOk`,
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

omit [Ord D] in
/-- An insert at a count key moves no sum that ignores count entries. -/
theorem sumN_insert_count {E : Env D} (g : RefusalSlot D × RefusalLeaf D → Nat)
    (hg : ∀ m win v, g (.count m win, v) = 0) {t : Refusals D} (hr : Trie.Routed (refusalSpec E) 0 t)
    (m : D) (win : UInt64) (v : RefusalLeaf D) :
    ((t.insert (refusalSpec E) (.count m win) v).toList.map g).sum = (t.toList.map g).sum := by
  cases hk : t.get (refusalSpec E) (.count m win) with
  | none => rw [Trie.sumN_insert_none _ g hr v hk, hg]; rfl
  | some old =>
      have := Trie.sumN_insert_some _ g hr v hk
      rw [hg, hg] at this; omega

/-! ## The tally -/

omit [Ord D] in
theorem tallyAt_step (E : Env D) (seed : D) (H : Nat) (m : D) (t : Refusals D)
    (p : RefusalSlot D × RefusalLeaf D) :
    tallyAt E seed (tallyStep E seed H t p) (.count m (refusalWindow H)) =
      tallyAt E seed t (.count m (refusalWindow H)) + refusedIn H m p := by
  obtain ⟨k, v⟩ := p
  cases k with
  | count m' win => cases v <;> simp [tallyStep, refusedIn]
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
    ∀ (l : List (RefusalSlot D × RefusalLeaf D)) (t : Refusals D),
      tallyAt E seed (l.foldl (tallyStep E seed H) t) (.count m (refusalWindow H)) =
        tallyAt E seed t (.count m (refusalWindow H)) + (l.map (refusedIn H m)).sum
  | [], t => by simp
  | p :: l, t => by
      rw [List.foldl_cons, tallyAt_foldl E seed H m l, tallyAt_step]
      simp only [List.map_cons, List.sum_cons]; omega

omit [Ord D] in
/-- A tally holds only positive counts of the current window. -/
theorem tally_support (E : Env D) (seed : D) (H : Nat) :
    ∀ (l : List (RefusalSlot D × RefusalLeaf D)) (t : Refusals D),
      (∀ k v, t.get (tallySpec E seed) k = some v → ∃ m n, k = .count m (refusalWindow H) ∧ v = .count n ∧ 0 < n) →
      ∀ k v, (l.foldl (tallyStep E seed H) t).get (tallySpec E seed) k = some v →
        ∃ m n, k = .count m (refusalWindow H) ∧ v = .count n ∧ 0 < n
  | [], t, ht => by simpa using ht
  | p :: l, t, ht => by
      rw [List.foldl_cons]
      apply tally_support E seed H l
      intro k v hk
      obtain ⟨k', v'⟩ := p
      cases k' with
      | count m' win => cases v' <;> exact ht k v hk
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

omit [Ord D] in
/-- **The tally at a count key**: the member's records of window `H / windowMax`, where it has any. -/
theorem refusalTally_get (E : Env D) (seed : D) (H : Nat) (l : List (RefusalSlot D × RefusalLeaf D))
    (m : D) (win : UInt64) :
    (refusalTally E seed H l).get (tallySpec E seed) (.count m win) =
      if win = refusalWindow H ∧ 0 < (l.map (refusedIn H m)).sum then
        some (.count (l.map (refusedIn H m)).sum) else none := by
  have hs := tally_support E seed H l .empty (fun k v h => by simp [Trie.get_empty] at h)
  have ht := tallyAt_foldl E seed H m l .empty
  have h0 : tallyAt E seed (Trie.T.empty : Refusals D) (.count m (refusalWindow H)) = 0 := rfl
  rw [h0, Nat.zero_add] at ht
  unfold refusalTally
  cases hg : (l.foldl (tallyStep E seed H) .empty).get (tallySpec E seed) (.count m win) with
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

/-- **A World's refusal counts are its records'**: records + height ≤ steps, and every member's count
for the current window is the number of its records this window. -/
def World.CountedOk (E : Env D) (w : World D) : Prop :=
  (w.refusals.toList.map refusedOne).sum + w.height ≤ w.steps ∧
    ∀ m, refusalCount E w m = (w.refusals.toList.map (refusedIn w.height m)).sum

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
  have hmem : ∀ k v, (k, v) ∈ w.refusals.toList ↔ w.refusalAt E k = some v :=
    fun k v => Trie.mem_toList (refusalSpec E) 0 w.refusals hw.1.1 k v
  unfold refusalsCounted World.CountedOk
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
  constructor
  · rintro ⟨h1, hall⟩
    refine ⟨h1, fun m => ?_⟩
    unfold refusalCount
    cases hg : w.refusalAt E (.count m (refusalWindow w.height)) with
    | some v =>
        cases v with
        | refused h c mb =>
            have := hw.2 _ _ hg; simp [refusalFits] at this
        | count n =>
            have := hall _ ((hmem _ _).mpr hg)
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
        cases k with
        | count m' win => cases v <;> simp [refusedIn] at hpos'
        | tx id =>
            cases v with
            | count n => simp [refusedIn] at hpos'
            | refused h c mb =>
                simp only [refusedIn] at hpos'
                split at hpos'
                · rename_i hc
                  obtain ⟨rfl, hwin⟩ := hc
                  have := hall _ hp
                  simp only [hwin, decide_true, Bool.not_true, Bool.false_or] at this
                  rw [hg] at this; cases this
                · simp at hpos'
  · rintro ⟨h1, hcount⟩
    refine ⟨h1, ?_⟩
    rintro ⟨k, v⟩ hp
    have hg := (hmem _ _).mp hp
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
            unfold refusalCount at hc
            rw [hg] at hc
            simp only at hc
            rw [refusalTally_get, if_pos ⟨rfl, by omega⟩, ← hc]
    | tx id =>
        cases v with
        | count n => trivial
        | refused h c mb =>
            simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not]
            by_cases hwin : (h - 1) / Bounds.windowMax = w.height / Bounds.windowMax
            · right
              have hle := le_sumN_of_mem (refusedIn w.height mb) hp
              simp only [refusedIn, hwin, and_self, if_true] at hle
              have hc := hcount mb
              unfold refusalCount at hc
              cases hr : w.refusalAt E (.count mb (refusalWindow w.height)) with
              | some _ => rfl
              | none => rw [hr] at hc; simp only at hc; omega
            · left; exact hwin

/-- **The counts are the records' on a World that passes `refusalsCounted`**: the reader the codec's
refusal hands a decoded base. -/
theorem refusalCount_eq_of_counted {E : Env D} {w : World D} (hw : w.RefusalsOk E)
    (hc : refusalsCounted E w = true) (m : D) :
    refusalCount E w m = (w.refusals.toList.map (refusedIn w.height m)).sum :=
  ((refusalsCounted_iff hw).mp hc).2 m

/-! ## Every step keeps it -/

theorem countedOk_of_empty {E : Env D} {w : World D} (h : w.refusals = .empty) (hs : w.height ≤ w.steps) :
    w.CountedOk E := by
  refine ⟨by rw [h]; show 0 + w.height ≤ w.steps; omega, fun m => ?_⟩
  unfold refusalCount World.refusalAt
  rw [h]; rfl

/-- A recorded refusal adds its one record to every sum over the listing that ignores count
entries. -/
theorem refuse_sumN {E : Env D} {w w' : World D} {r : Refused D} (hw : w.RefusalsOk E)
    (h : World.refuse E w r = .ok w') (g : RefusalSlot D × RefusalLeaf D → Nat)
    (hg : ∀ m win v, g (.count m win, v) = 0) :
    (w'.refusals.toList.map g).sum =
      (w.refusals.toList.map g).sum + g (.tx r.txId, .refused (w.height + 1) r.code r.member) := by
  obtain ⟨-, -, -, -, hnot, -⟩ := refuse_facts h
  have hnone : w.refusals.get (refusalSpec E) (.tx r.txId) = none := by
    cases hk : w.refusals.get (refusalSpec E) (.tx r.txId) with
    | none => rfl
    | some v =>
        cases v with
        | refused hh code mb => exact absurd hk (hnot hh code mb)
        | count n => have := hw.2 _ _ hk; simp [refusalFits] at this
  obtain ⟨_, rfl⟩ := refuse_ok h
  rw [commitRefusal_refusals, sumN_insert_count g hg (Trie.routed_insert _ _ _ hw.1.1),
    Trie.sumN_insert_none _ g hw.1.1 _ hnone]

theorem refuse_countedOk {E : Env D} {w w' : World D} {r : Refused D} (hw : w.RefusalsOk E)
    (hc : w.CountedOk E) (h : World.refuse E w r = .ok w') : w'.CountedOk E := by
  have hh := (refuse_frame h).2.2.1
  refine ⟨?_, fun m => ?_⟩
  · rw [refuse_sumN hw h refusedOne (fun _ _ v => by cases v <;> rfl), hh, refuse_steps h]
    have := hc.1; simp only [refusedOne]; omega
  · rw [refuse_refusalCount h m, hh, refuse_sumN hw h (refusedIn w.height m) (fun _ _ v => by cases v <;> rfl),
      hc.2 m]
    simp only [refusedIn, Nat.add_sub_cancel, and_true]
    by_cases hm : m = r.member
    · subst hm; simp
    · simp [hm, Ne.symm hm]

theorem admit_countedOk {E : Env D} {w w' : World D} {t : Turn D} (hw : w.RefusalsOk E)
    (hc : w.CountedOk E) (h : World.admit E w t = .ok w') : w'.CountedOk E := by
  have hh := admit_height h
  have hst := admit_steps h
  have hr : w'.refusals = pruneRefusals E (w.height + 1) w.refusals := by
    obtain ⟨_, _, rfl⟩ := admit_ok h; rfl
  by_cases hz : (w.height + 1) % Bounds.windowMax = 0
  · have hl : w'.refusals.toList = w.refusals.toList.filter fun p => keptRefusal (w.height + 1) p.1 p.2 := by
      rw [hr]; unfold pruneRefusals; rw [if_pos hz]
      exact Trie.toList_retainAt (refusalSpec E) _ [] 0 w.refusals hw.1.1 (fun _ _ _ _ _ _ h => by simp at h)
    refine ⟨?_, fun m => ?_⟩
    · rw [hl, hh, hst]
      have := sumN_filter_le refusedOne (fun p => keptRefusal (w.height + 1) p.1 p.2) w.refusals.toList
      have := hc.1; omega
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
      have hp' := (List.mem_filter.mp hp).1
      obtain ⟨k, v⟩ := p
      cases k with
      | count _ _ => cases v <;> rfl
      | tx id =>
          cases v with
          | count _ => rfl
          | refused hh' c mb =>
              have hf := hw.2 _ _ ((Trie.mem_toList (refusalSpec E) 0 w.refusals hw.1.1 _ _).mp hp')
              simp only [refusalFits, decide_eq_true_eq] at hf
              simp only [refusedIn]
              rw [if_neg]
              rintro ⟨-, hwin⟩
              have hq : (w.height + 1) / Bounds.windowMax = w.height / Bounds.windowMax + 1 := by
                rw [windowMax_eq] at hz ⊢; omega
              have : (hh' - 1) / Bounds.windowMax ≤ w.height / Bounds.windowMax :=
                Nat.div_le_div_right (by omega)
              omega
  · have hl : w'.refusals = w.refusals := by rw [hr]; unfold pruneRefusals; rw [if_neg hz]
    have hq : (w.height + 1) / Bounds.windowMax = w.height / Bounds.windowMax := by
      rw [windowMax_eq] at hz ⊢; omega
    have hfun : ∀ m, refusedIn (D := D) (w.height + 1) m = refusedIn w.height m := by
      intro m; funext p
      obtain ⟨k, v⟩ := p
      cases k <;> cases v <;> simp only [refusedIn, hq]
    refine ⟨?_, fun m => ?_⟩
    · rw [hl, hh, hst]; have := hc.1; omega
    · rw [admit_refusalCount hw.1 h hz m, hl, hh, hfun m]; exact hc.2 m

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
      (w.refusals.insert (refusalSpec E) (.count m (refusalWindow w.height)) (.count (refusalCount E w m - 1))).insert
        (refusalSpec E) (.count m' (refusalWindow w.height)) (.count (refusalCount E w m' + 1)))
    (hh : w'.height = w.height) :
    w'.RefusalsOk E ∧ refusalsCounted E w' = false := by
  have hle := refusalCount_le hw m
  have hok : w'.RefusalsOk E := by
    refine ⟨?_, fun k v hk => ?_⟩
    · unfold World.RefusalsCanon; rw [hr]
      exact Trie.canon_insert _ _ _ (Trie.canon_insert _ _ _ hw.1)
    · rw [hh]
      unfold World.refusalAt at hk
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
      (w.refusals.insert (refusalSpec E) (.count m (refusalWindow w.height)) (.count (refusalCount E w m - 1))).insert
        (refusalSpec E) (.count m' (refusalWindow w.height)) (.count (refusalCount E w m' + 1))) :
    (w'.refusals.toList.map fun p => match p with | (.count _ _, .count n) => n | _ => 0).sum =
      (w.refusals.toList.map fun p => match p with | (.count _ _, .count n) => n | _ => 0).sum := by
  let g : RefusalSlot D × RefusalLeaf D → Nat := fun p => match p with | (.count _ _, .count n) => n | _ => 0
  show (w'.refusals.toList.map g).sum = (w.refusals.toList.map g).sum
  obtain ⟨c, hc⟩ : ∃ c, refusalCount E w m = c := ⟨_, rfl⟩
  obtain ⟨c', hc'⟩ : ∃ c', refusalCount E w m' = c' := ⟨_, rfl⟩
  rw [hc, hc'] at hr
  rw [hc] at hm
  have h1 : w.refusals.get (refusalSpec E) (.count m (refusalWindow w.height)) = some (.count c) := by
    have hc2 := hc
    unfold refusalCount World.refusalAt at hc2
    split at hc2
    · rename_i n hg; rw [hg, hc2]
    · omega
  have hr1 := Trie.routed_insert (refusalSpec E) (.count m (refusalWindow w.height)) (.count (c - 1)) hw.1.1
  have s1 := Trie.sumN_insert_some _ g hw.1.1 (.count (c - 1)) h1
  have hk2 : (w.refusals.insert (refusalSpec E) (.count m (refusalWindow w.height))
      (.count (c - 1))).get (refusalSpec E) (.count m' (refusalWindow w.height)) =
      w.refusals.get (refusalSpec E) (.count m' (refusalWindow w.height)) := by
    rw [Trie.get_insert, if_neg (by simp [Ne.symm hne])]
  rw [hr]
  cases h2 : w.refusals.get (refusalSpec E) (.count m' (refusalWindow w.height)) with
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
  let r₂ := (w.refusals.insert (refusalSpec E) (.count m (refusalWindow w.height))
    (.count (refusalCount E w m - 1))).insert (refusalSpec E) (.count m' (refusalWindow w.height))
    (.count (refusalCount E w m' + 1))
  ⟨{ w with refusals := r₂ }, rfl, refusalsCounted_moved hw hc hne hm hm' rfl rfl⟩

/-! ## On every reached World -/

end Nanodregg.Kernel

namespace Nanodregg.Kernel.Receive

open Nanodregg.Kernel

variable {D : Type} [Ord D] [DecidableEq D]

/-- **Every World a checked genesis and a fold reach passes `refusalsCounted`.** -/
theorem reach_refusalsCounted {X : Ctx D} {name nonce : ByteArray} {allowance : Nat}
    {founders : List (ByteArray × D)} {w : World D} {l : List (Step D)}
    (h : World.fold X.env (genesisWorld X name nonce allowance founders) l = .ok w) :
    refusalsCounted X.env w = true :=
  fold_refusalsCounted (genesisWorld_refusalsOk X name nonce allowance founders)
    (countedOk_of_empty rfl (Nat.le_refl _)) h

open Nanodregg.Codec Nanodregg.Codec.Deployed in
/-- **Deployed**: no premise. -/
theorem deployed_reach_refusalsCounted (program : Program Digest) {name nonce : ByteArray} {allowance : Nat}
    {founders : List (ByteArray × Digest)} {g w : World Digest} {l : List (Step Digest)}
    (hg : genesis (ctx program) name nonce allowance founders = .ok g) (hl : World.fold env g l = .ok w) :
    refusalsCounted env w = true := by
  obtain ⟨_, rfl⟩ := genesis_ok.mp hg
  exact reach_refusalsCounted (X := ctx program) hl

end Nanodregg.Kernel.Receive
