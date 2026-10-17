/-
# Hosting.Proofs.Lifecycle — the edge list, `step`, and what the law and methods are made of

`step` is read off `edges`; `admits` (what the law decides) and `target` (what a method computes)
are read off `step`. These pin the machine itself: the edge list is deterministic and has no
self-loop (so a method that does not move the phase is always refused), `running` is entered only
by `start`, `removed` is terminal, and a birth may only write the initial phase.
-/
import Hosting.Lifecycle

namespace Nanodregg.Hosting.Proofs

open Nanodregg.Hosting

theorem Phase.mem_all (p : Phase) : p ∈ Phase.all := by cases p <;> decide
theorem Event.mem_all (e : Event) : e ∈ Event.all := by cases e <;> decide

/-- At most one edge leaves a phase on an event. -/
theorem edges_deterministic :
    ∀ a ∈ edges, ∀ b ∈ edges, a.1 = b.1 → a.2.1 = b.2.1 → a = b := by decide

/-- No edge is a self-loop. -/
theorem edges_irreflexive : ∀ x ∈ edges, x.1 ≠ x.2.2 := by decide

/-- `step` is exactly the edge list. -/
theorem step_table :
    (Phase.all.flatMap fun p => Event.all.filterMap fun e => (step p e).map fun q => (p, e, q)) =
      edges := by decide

theorem step_iff_edge (p : Phase) (e : Event) (q : Phase) : step p e = some q ↔ (p, e, q) ∈ edges := by
  cases p <;> cases e <;> cases q <;> decide

/-- The method indices are distinct and in `Event.all`'s order. -/
theorem index_injective (a b : Event) (h : a.index = b.index) : a = b := by
  cases a <;> cases b <;> simp_all [Event.index]

theorem no_double_start : step .running .start = none := by decide

theorem removed_terminal (e : Event) : step .removed e = none := by cases e <;> decide

/-- `running` is entered only by `start`. -/
theorem running_only_by_start (p : Phase) (e : Event) (h : step p e = some .running) :
    e = .start := by
  cases p <;> cases e <;> simp_all [step, edges]

/-- A birth writes only the initial phase (the seed `create` judges as `old = new`). -/
theorem born_initial_only (p q : Phase) (h : admits p none q = true) :
    p = .installed ∧ q = .installed := by
  cases p <;> cases q <;> simp_all [admits, bornOk, initial]

/-- A method's result is admitted exactly when its event is an edge from the phase. -/
theorem target_admitted_iff (p : Phase) (e : Event) :
    admits p (some e) (target p e) = (step p e).isSome := by
  cases p <;> cases e <;> decide

/-- The phase moves exactly on an edge. -/
theorem target_moves_iff (p : Phase) (e : Event) : target p e ≠ p ↔ (step p e).isSome := by
  cases p <;> cases e <;> decide

end Nanodregg.Hosting.Proofs
