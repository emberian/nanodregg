/- Two-hole exactness and named-refusal teeth for the separate adapter. -/
import Lang.Contextual.AcyclicExamples
import Lang.Proofs.Contextual.Acyclic

namespace Nanodregg.Lang.Contextual.Acyclic

theorem chain_stratifies (p q : Polynomial) : Ranked (chain p q) := by
  apply (validate_iff _).mp
  rfl

/-- Arbitrary finite local provenances, not just the concrete token fixture. -/
theorem chain_exact (p q : Polynomial) :
    adapt (chain p q) 1 = .ok (product q p) := by rfl

/-- Actual landed candidate judges compose through the new dependency.
The environment is fixed at the leaves, exactly as in the landed provenance theorem. -/
theorem chain_candidates {D : CalculusData} {E : Type}
    (dependency consumer : Iface D E) (w : World E) (ds cs : List (Candidate D)) :
    Derives (chain (provenance dependency w.env ds) (provenance consumer w.env cs))
      w (.hole 1) ↔
      (∃ c ∈ cs, judge consumer w c = .verified) ∧
      (∃ d ∈ ds, judge dependency w d = .verified) := by
  rw [← adapt_correct (chain_exact _ _) w, holds_product]
  exact and_congr provenance_iff.symm provenance_iff.symm

theorem two_hole_direct :
    adapt (chain seed localCondition) 1 =
      .ok [([⟨13, 0⟩, ⟨10, 0⟩], [⟨14, 0⟩, ⟨11, 0⟩]),
           ([⟨13, 0⟩, ⟨12, 0⟩], [⟨14, 0⟩])] := by rfl

theorem self_refused_by_name :
    adapt selfDependent 0 = .error (.fixedPointDependency 0) := by rfl

/-- This successful polynomial is exactly the silent drop that bypassing validation exposes.
It is an internal approximation, never the adapter result on selfDependent. -/
theorem unchecked_self_drops :
    unroll selfDependent (selfDependent.rank 0 + 1) 0 = seed := by rfl

theorem mutual_refused_by_edge :
    adapt mutualCycle 1 = .error (.rankNotDecreasing 0 1) := by rfl

theorem undemanded_cycle_refused :
    adapt hiddenCycle 0 = .error (.fixedPointDependency 1) := by rfl

theorem zero_masked_cycle_refused :
    adapt zeroMaskedCycle 0 = .error (.fixedPointDependency 0) := by rfl

theorem bad_rank_witness_refused :
    adapt badWitness 1 = .error (.rankNotDecreasing 1 0) := by rfl

/-- Invalid rank evidence is not a claim that the underlying graph is cyclic. -/
theorem bad_witness_has_valid_replacement :
    adapt (chain seed localCondition) 1 = .ok (product localCondition seed) :=
  chain_exact _ _

/-- Concrete reflexive path inhabits the general boundary theorem's premise. -/
theorem self_dependency : Depends selfDependent (0 : Fin 1) 0 := by
  apply Depends.edge
  simp [selfDependent, Expr.refs]

theorem mutual_dependency : Depends mutualCycle (0 : Fin 2) 0 := by
  apply Depends.trans (j := 1)
  · apply Depends.edge
    simp [mutualCycle, Expr.refs]
  · apply Depends.edge
    simp [mutualCycle, Expr.refs]

end Nanodregg.Lang.Contextual.Acyclic
