/-
Stable alternatives, completed-search reports and world-indexed grounding.
Every Prop statement lives here. The definition module exports only data.
-/
import Lang.Contextual.Worlds
import Lang.Proofs.Contextual.Stability

namespace Nanodregg.Lang.Contextual.Worlds

/-- Stable-model semantics: exactly the well-founded consequences of this world's
positive reduct. No union of alternative worlds appears in this judgment. -/
def Stable {E : Type} (P : Program) (w : World E) (v : Alternative) : Prop :=
  ∀ x, x ∈ v ↔ Derives (reduct P w v) (fun _ => false) x

theorem derives_head {E : Type} {P : Program} {w : World E} {v : Alternative} {x : Nat}
    (h : Derives (reduct P w v) (fun _ => false) x) : x ∈ heads P := by
  cases h with
  | fact h => cases h
  | @rule r hr _ =>
    obtain ⟨n, hn, he⟩ := List.mem_map.1 hr
    have hnP := (List.mem_filter.1 hn).1
    cases he
    simp only [heads, List.mem_eraseDups, List.mem_map]
    exact ⟨n, hnP, rfl⟩

/-- Checked saturation turns finite iteration into the full inductive semantics,
even when the supplied fuel was smaller than a general worst-case bound. -/
theorem closed_complete {R : List Rule} {n : Nat}
    (hc : closed R (ground R n) = true) {x : Nat}
    (h : Derives R (fun _ => false) x) : ground R n x = true := by
  induction h with
  | fact h => cases h
  | @rule r hr _ ih =>
    have hc' := (List.all_eq_true.1 hc) r hr
    have hb : r.body.all (ground R n) = true := List.all_eq_true.2 ih
    simpa [hb] using hc'

theorem check_iff_stable {E : Type} {rounds : Nat} {P : Program} {w : World E}
    {v : Alternative} (hc : closed (reduct P w v) (ground (reduct P w v) rounds) = true) :
    check rounds P w v = some true ↔ Stable P w v := by
  simp only [check, hc, if_true, Option.some.injEq, Bool.and_eq_true, List.all_eq_true]
  constructor
  · rintro ⟨hvg, hgv⟩ x
    constructor
    · intro hx
      exact lfpIter_sound rounds x (hvg x hx)
    · intro hx
      have hg := closed_complete hc hx
      have := hgv x (derives_head hx)
      simpa [hg] using this
  · intro hs
    constructor
    · intro x hx
      exact closed_complete hc ((hs x).1 hx)
    · intro x _
      cases hg : ground (reduct P w v) rounds x
      · rfl
      · have hx := (hs x).2 (lfpIter_sound rounds x hg)
        simpa [hg] using hx

/-- A completed check decides stable semantics; unfinished is not rejection. -/
theorem check_decides {E : Type} {rounds : Nat} {P : Program} {w : World E}
    {v : Alternative} {b : Bool} (h : check rounds P w v = some b) :
    b = true ↔ Stable P w v := by
  have hc : closed (reduct P w v) (ground (reduct P w v) rounds) = true := by
    dsimp only [check] at h
    split at h
    · assumption
    · cases h
  rw [← check_iff_stable hc, h, Option.some.injEq]

/-- Accepted worlds contain no unfounded atom, even beside unrelated live facts. -/
theorem unfounded_excluded {E : Type} {rounds : Nat} {P : Program} {w : World E}
    {v : Alternative} (hv : check rounds P w v = some true) {S : Nat → Prop}
    (hr : ∀ r ∈ reduct P w v, S r.head → ∃ y ∈ r.body, S y) {x : Nat}
    (hx : S x) : x ∉ v := by
  intro hm
  exact unfounded_not_derivable (fun _ _ => rfl) hr hx
    (((check_decides hv).1 rfl x).1 hm)

theorem collect_checked {E : Type} {rounds : Nat} {P : Program} {w : World E} :
    ∀ {vs ws : List Alternative}, collect rounds P w vs = some ws →
      ∀ v ∈ vs, ∃ b, check rounds P w v = some b := by
  intro vs
  induction vs with
  | nil => intro ws h v hv; cases hv
  | cons a vs ih =>
    intro ws h v hv
    cases ha : check rounds P w a with
    | none => simp [collect, ha] at h
    | some b =>
      cases ht : collect rounds P w vs with
      | none => simp [collect, ha, ht] at h
      | some rest =>
        rcases List.mem_cons.1 hv with rfl | hv
        · exact ⟨b, ha⟩
        · exact ih ht v hv

theorem collect_mem {E : Type} {rounds : Nat} {P : Program} {w : World E} :
    ∀ {vs ws : List Alternative}, collect rounds P w vs = some ws →
      ∀ v, v ∈ ws ↔ v ∈ vs ∧ check rounds P w v = some true := by
  intro vs
  induction vs with
  | nil =>
    intro ws h v
    simp only [collect, Option.some.injEq] at h
    subst ws
    simp
  | cons a vs ih =>
    intro ws h v
    cases ha : check rounds P w a with
    | none => simp [collect, ha] at h
    | some b =>
      cases ht : collect rounds P w vs with
      | none => simp [collect, ha, ht] at h
      | some rest =>
        cases b <;> simp [collect, ha, ht] at h
        · subst ws
          rw [ih ht v]
          simp only [List.mem_cons]
          constructor
          · rintro ⟨hv, hc⟩; exact ⟨Or.inr hv, hc⟩
          · rintro ⟨rfl | hv, hc⟩
            · rw [ha] at hc; cases hc
            · exact ⟨hv, hc⟩
        · subst ws
          rw [List.mem_cons, ih ht v]
          constructor
          · rintro (rfl | ⟨hv, hc⟩)
            · exact ⟨List.mem_cons_self, ha⟩
            · exact ⟨List.mem_cons_of_mem _ hv, hc⟩
          · rintro ⟨hv, hc⟩
            rcases List.mem_cons.1 hv with rfl | hv
            · exact Or.inl rfl
            · exact Or.inr ⟨hv, hc⟩

/-- A completed answer is exact over the enumerated finite worlds, not merely
a collection of sound successes from an unfinished search. -/
theorem analyze_exact {E : Type} {rounds : Nat} {P : Program} {w : World E}
    {ws : List Alternative} (h : analyze rounds P w = some ws) (v : Alternative) :
    v ∈ ws ↔ v ∈ subsets (heads P) ∧ Stable P w v := by
  rw [collect_mem h v]
  constructor
  · rintro ⟨hm, hc⟩
    exact ⟨hm, (check_decides hc).1 rfl⟩
  · rintro ⟨hm, hs⟩
    obtain ⟨b, hb⟩ := collect_checked h v hm
    have := (check_decides hb).2 hs
    subst b
    exact ⟨hm, hb⟩


/-- Enumeration covers every sublist, so a completed search is exhaustive over
canonical finite worlds, including the empty world. -/
theorem mem_subsets_iff (v xs : List Nat) : v ∈ subsets xs ↔ v.Sublist xs := by
  induction xs generalizing v with
  | nil => simp [subsets]
  | cons a xs ih =>
    simp only [subsets, List.mem_append, List.mem_map, ih, List.sublist_cons_iff]
    constructor
    · rintro (h | ⟨r, hr, he⟩)
      · exact Or.inl h
      · exact Or.inr ⟨r, he.symm, hr⟩
    · rintro (h | ⟨r, he, hr⟩)
      · exact Or.inl h
      · exact Or.inr ⟨r, hr, he.symm⟩

theorem analyze_sublist_exact {E : Type} {rounds : Nat} {P : Program} {w : World E}
    {ws : List Alternative} (h : analyze rounds P w = some ws) (v : Alternative) :
    v ∈ ws ↔ v.Sublist (heads P) ∧ Stable P w v := by
  rw [analyze_exact h v, mem_subsets_iff]

/-- An alternatives report contains two different admissible worlds and evidence
on the two sides. Merely accumulating both observations cannot produce this report. -/
theorem alternatives_sound {E : Type} {rounds : Nat} {P : Program} {w : World E}
    {positive negative : Nat} {proposed left right : Alternative}
    (h : report rounds P w positive negative proposed = .alternatives left right) :
    Stable P w left ∧ Stable P w right ∧ positive ∈ left ∧ negative ∈ right ∧ left ≠ right := by
  unfold report at h
  cases ha : analyze rounds P w with
  | none => simp [ha] at h
  | some ws =>
    simp only [ha] at h
    split at h
    · cases h
    · split at h
      · cases h
      · cases hp : ws.find? (·.contains positive) <;>
          cases hn : ws.find? (·.contains negative) <;> simp only [hp, hn] at h
        · cases h
        · cases h
        · cases h
        · rename_i l r
          split at h
          · cases h
          · rename_i hne
            cases h
            exact ⟨((analyze_exact ha left).1 (List.mem_of_find?_eq_some hp)).2,
              ((analyze_exact ha right).1 (List.mem_of_find?_eq_some hn)).2,
              by simpa using List.find?_some hp,
              by simpa using List.find?_some hn,
              by simpa using hne⟩

/-- A no-justification report is completed search with at least one admissible
world, and neither queried evidence atom occurs in any of those worlds. -/
theorem noJustification_sound {E : Type} {rounds : Nat} {P : Program} {w : World E}
    {positive negative : Nat} {proposed : Alternative}
    (h : report rounds P w positive negative proposed = .noJustification) :
    ∃ ws, analyze rounds P w = some ws ∧ ws ≠ [] ∧
      ∀ v ∈ ws, positive ∉ v ∧ negative ∉ v := by
  unfold report at h
  cases ha : analyze rounds P w with
  | none => simp [ha] at h
  | some ws =>
    simp only [ha] at h
    split at h
    · cases h
    · split at h
      · cases h
      · rename_i hne
        cases hp : ws.find? (·.contains positive) <;>
          cases hn : ws.find? (·.contains negative) <;> simp only [hp, hn] at h
        · refine ⟨ws, rfl, ?_, ?_⟩
          · intro he; subst ws; simp at hne
          · intro v hv
            exact ⟨by simpa using (List.find?_eq_none.1 hp) v hv,
              by simpa using (List.find?_eq_none.1 hn) v hv⟩
        · cases h
        · cases h
        · split at h <;> cases h

namespace Experiment

/-- The two-rule program has exactly two alternatives, each separately checked. -/
theorem two_rule_worlds :
    analyze 2 twoRules initial = some [[1], [0]] ∧
    check 2 twoRules initial [0] = some true ∧
    check 2 twoRules initial [1] = some true := by decide

/-- Non-closure under union, with both operands certified admissible. -/
theorem admissible_not_union_closed :
    check 2 twoRules initial [0] = some true ∧
    check 2 twoRules initial [1] = some true ∧
    check 2 twoRules initial (union [0] [1]) = some false := by decide

/-- The union also fails the independent inductive stable-model statement. -/
theorem union_not_stable : ¬ Stable twoRules initial (union [0] [1]) := by
  intro h
  have hc : check 2 twoRules initial (union [0] [1]) = some false := by decide
  have := (check_decides hc).2 h
  cases this

/-- Withdrawal removes applicability, reassertion restores the same immutable rule.
The empty world is a world; an empty list of worlds is a different outcome. -/
theorem withdraw_and_reassert :
    session 2 twoRules [.withdraw pToken, .withdraw qToken,
      .assert pToken, .assert qToken] initial =
      [some [[1], [0]], some [[1]], some [[]], some [[0]], some [[1], [0]]] := by decide

/-- Reissuing p's identity at version 1 leaves the rule citing version 0 disabled. -/
theorem reissue_does_not_restore_rule :
    analyze 2 twoRules (applyAll (reissue 10 0 1) neither) = some [[]] ∧
    (applyAll (reissue 10 0 1) neither).live ⟨10, 1⟩ = true ∧
    (applyAll (reissue 10 0 1) neither).live pToken = false := by decide

/-- The four reports are reached through the analyzer, not hand-constructed tags.
p and q are the opposed possibilities here; defaults remain absence tests. -/
theorem four_reports :
    report 2 twoRules neither 0 1 [] = .noJustification ∧
    report 2 twoRules initial 0 1 [] = .alternatives [0] [1] ∧
    report 2 twoRules initial 0 1 both = .conflictingEvidence both ∧
    report 0 twoRules initial 0 1 [] = .unfinished := by decide

/-- No stable world is distinct from no recorded justification in the empty world. -/
theorem no_world_is_distinct :
    report 2 [⟨0, [], [0], []⟩] initial 0 1 [] = .noWorld ∧
    report 2 twoRules neither 0 1 [] = .noJustification ∧
    report 2 twoRules withdrawn 0 1 [] = .supported [[1]] := by decide

/-- The original positive-cycle experiment, now over the exact alternative set
at each revision, retaining the independent fact 5 and consequence 6. -/
theorem cycle_loses_grounding_over_worlds :
    session 4 cycle [.withdraw pToken, .assert pToken] initial =
      [some [beforeCycle], some [afterCycle], some [beforeCycle]] ∧
    check 4 cycle withdrawn beforeCycle = some false := by decide

/-- Immediate support counting still keeps both cycle members forever, even
though completed stable-world analysis rejects them after withdrawal. -/
theorem counting_keeps_cycle_over_worlds :
    ∀ n, countRun (reduct cycle withdrawn beforeCycle) (fun _ => false)
      beforeCycle.contains n 1 = true ∧
      countRun (reduct cycle withdrawn beforeCycle) (fun _ => false)
      beforeCycle.contains n 2 = true := by
  intro n
  induction n with
  | zero => exact ⟨by decide, by decide⟩
  | succ n ih =>
    obtain ⟨h1, h2⟩ := ih
    have hp : 0 < supportCount (reduct cycle withdrawn beforeCycle) (fun _ => false)
        (countRun (reduct cycle withdrawn beforeCycle) (fun _ => false) beforeCycle.contains n) 1 := by
      simp only [supportCount, Bool.false_eq_true, if_false, Nat.zero_add]
      apply List.length_pos_of_mem (a := ⟨1, [2]⟩)
      rw [List.mem_filter]
      exact ⟨by change _ ∈ ([⟨1, [0]⟩, ⟨1, [2]⟩, ⟨2, [1]⟩, ⟨5, []⟩, ⟨6, [5]⟩] : List Rule); simp, by simp [h2]⟩
    have hq : 0 < supportCount (reduct cycle withdrawn beforeCycle) (fun _ => false)
        (countRun (reduct cycle withdrawn beforeCycle) (fun _ => false) beforeCycle.contains n) 2 := by
      simp only [supportCount, Bool.false_eq_true, if_false, Nat.zero_add]
      apply List.length_pos_of_mem (a := ⟨2, [1]⟩)
      rw [List.mem_filter]
      exact ⟨by change _ ∈ ([⟨1, [0]⟩, ⟨1, [2]⟩, ⟨2, [1]⟩, ⟨5, []⟩, ⟨6, [5]⟩] : List Rule); simp, by simp [h1]⟩
    simp only [countRun, h1, h2, hp, hq, decide_true, Bool.and_self, and_self]

end Experiment
end Nanodregg.Lang.Contextual.Worlds

/-! ## P11a literature restatement (append-only; statements preserved)
cycle_loses_grounding_over_worlds and counting_keeps_cycle_over_worlds retain
their names and premises. They express unfounded-set exclusion (Lifschitz,
Thirteen Definitions, Definition D, PDF p8) and the boundary of immediate-support
counting (Gupta–Mumick–Subrahmanian 1993, printed pp158,164–166).
The new WorldsField proof module proves stable_iff_labelling independently:
model closure plus absence of unfounded IN sets equals reduct semantics.
This is the finite propositional JTMS/stable-model correspondence identified
by Elkan (1990), p219, abstract; NP-completeness concerns the general existence
problem, not a proof that a particular finite search cannot complete.
An unfinished fuel-bounded reduct remains an operational observation. -/
