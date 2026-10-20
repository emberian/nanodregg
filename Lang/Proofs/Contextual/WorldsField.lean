/-
P11a: stable IN/OUT labellings and unfounded sets.
Lifschitz, Thirteen Definitions, PDF pp7–8 (Definitions C/D).
Elkan, Artificial Intelligence 43 (1990), pp219–234: JTMS/stable-set bridge;
the publisher abstract (p219) was read, not the unavailable full text.
This is the finite propositional rule model, not hole-to-hole provenance.
-/
import Lang.Proofs.Contextual.Worlds

namespace Nanodregg.Lang.Contextual.Worlds.Field

/-- Lifschitz, Definition D, PDF p8: every applicable justification whose IN-list
holds must label its head IN. The reduct freezes OUT-lists and external tokens. -/
def Model {E : Type} (P : Program) (w : World E) (v : Alternative) : Prop :=
  ∀ r ∈ reduct P w v, (∀ a ∈ r.body, a ∈ v) → r.head ∈ v

/-- Lifschitz, Definition D, PDF p8: every otherwise satisfied rule for U depends
positively on U. Rules with false bodies do not provide external support. -/
def Unfounded {E : Type} (P : Program) (w : World E) (v : Alternative)
    (U : Nat → Prop) : Prop :=
  ∀ r ∈ reduct P w v, U r.head → (∀ a ∈ r.body, a ∈ v) →
    ∃ a ∈ r.body, U a

/-- Lifschitz, Definition D, PDF p8; Elkan (1990), p219, abstract: the independent
IN/OUT characterization requires model closure AND exclusion of unfounded IN atoms.
Mere supportedness would admit self-supporting cycles. -/
def StableLabelling {E : Type} (P : Program) (w : World E) (v : Alternative) : Prop :=
  Model P w v ∧
    ∀ U : Nat → Prop, (∀ a, U a → a ∈ v) → Unfounded P w v U → ∀ a, ¬ U a

/-- Lifschitz, Definition C, PDF p7: the least reduct model is contained in every
model. This induction is the non-circular direction of the labelling bridge. -/
theorem derives_in_model {E : Type} {P : Program} {w : World E} {v : Alternative}
    (hm : Model P w v) {a : Nat}
    (ha : Derives (reduct P w v) (fun _ => false) a) : a ∈ v := by
  induction ha with
  | fact h => cases h
  | rule hr _ ih => exact hm _ hr ih

/-- Lifschitz, Definitions C/D, PDF pp7–8: stable reduct semantics equals a closed
IN/OUT labelling with no nonempty unfounded IN set; neither is defined by a checker. -/
theorem stable_iff_labelling {E : Type} {P : Program} {w : World E}
    {v : Alternative} : Stable P w v ↔ StableLabelling P w v := by
  classical
  constructor
  · intro hs
    refine ⟨?_, ?_⟩
    · intro r hr hb
      exact (hs r.head).2 (.rule hr fun a ha => (hs a).1 (hb a ha))
    · intro U hsub hu a ha
      have hd := (hs a).1 (hsub a ha)
      have hnot : ∀ x, Derives (reduct P w v) (fun _ => false) x → ¬ U x := by
        intro x hx
        induction hx with
        | fact h => cases h
        | @rule r hr hb ih =>
          intro hU
          obtain ⟨y, hy, hyU⟩ := hu r hr hU (fun y hy => (hs y).2 (hb y hy))
          exact ih y hy hyU
      exact hnot a hd ha
  · rintro ⟨hm, hu⟩ a
    constructor
    · intro ha
      apply Classical.byContradiction
      intro hn
      let U := fun x => x ∈ v ∧ ¬ Derives (reduct P w v) (fun _ => false) x
      have hU : Unfounded P w v U := by
        intro r hr hhead hb
        apply Classical.byContradiction
        intro hnone
        apply hhead.2
        apply Derives.rule hr
        intro y hy
        apply Classical.byContradiction
        intro hny
        exact hnone ⟨y, hy, hb y hy, hny⟩
      exact hu U (fun _ hx => hx.1) hU a ⟨ha, hn⟩
    · exact derives_in_model hm

/-- Elkan (1990), p219, and Lifschitz Definition D, PDF p8: the completed analyzer's
admissible worlds are EXACTLY its canonical stable IN/OUT labellings. Completion
and canonical enumeration are inherited from analyze_sublist_exact unchanged. -/
theorem admissibleWorlds_eq_stableLabellings {E : Type} {P : Program} {w : World E}
    {rounds : Nat} {ws : List Alternative} (h : analyze rounds P w = some ws) :
    (fun v => v ∈ ws) =
      (fun v => v.Sublist (heads P) ∧ StableLabelling P w v) := by
  funext v
  apply propext
  rw [analyze_sublist_exact h v, stable_iff_labelling]

/-- Lifschitz Definition D, PDF p8: the withdrawn cycle {1,2} is unfounded relative
to the proposal with its unsupported root 0 removed. The independent fact survives. -/
theorem cycle_unfounded :
    Unfounded Experiment.cycle Experiment.withdrawn [1, 2, 5, 6]
      (fun a => a = 1 ∨ a = 2) := by
  intro r hr hh hb
  change r ∈ ([⟨1, [0]⟩, ⟨1, [2]⟩, ⟨2, [1]⟩, ⟨5, []⟩, ⟨6, [5]⟩] : List Rule) at hr
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · have := hb 0 (by simp)
    simp at this
  · exact ⟨2, by simp, Or.inr rfl⟩
  · exact ⟨1, by simp, Or.inl rfl⟩
  · simp at hh
  · simp at hh

/-- Lifschitz Definition D, PDF p8: supported but unfounded IN labels are rejected
even when an unrelated component remains grounded; concrete witness for the bridge. -/
theorem unfounded_cycle_not_labelling :
    ¬ StableLabelling Experiment.cycle Experiment.withdrawn [1, 2, 5, 6] := by
  intro h
  have := h.2 (fun a => a = 1 ∨ a = 2)
    (by intro a ha; rcases ha with rfl | rfl <;> simp) cycle_unfounded 1
  exact this (Or.inl rfl)

/-- Lifschitz Definition C, PDF p7; Elkan (1990), p219: alternative JTMS labellings
cannot be unioned. This consumes the existing independent union counterexample. -/
theorem union_not_labelling :
    ¬ StableLabelling Experiment.twoRules Experiment.initial (Experiment.union [0] [1]) :=
  fun h => Experiment.union_not_stable (stable_iff_labelling.mpr h)

end Nanodregg.Lang.Contextual.Worlds.Field
