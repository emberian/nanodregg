/-
# Protocol.Proofs.Rows — no operation without a row

The deletion rule as a theorem: an operation that no row drives is not part of the system. Adding
an operation to `Op` without a row that exercises it breaks this proof by name.

The rows' writer serves every event the kernel admits (PROTOCOL-55): both parameter sets' budgets
meet the premise of HOST's `Host.Page.walkTurnsAt_serves` and `Host.Page.walk_serves` (a budget of
`eventBytesMax + 5`; the tooth at `+ 4` is `Host.Page.walkTurnsAt_one_short`).
-/
import Protocol.Rows
import Protocol.Rows.Writer
import Protocol.Rows.Deployed
import Protocol.Proofs.Table

namespace Nanodregg.Protocol

/-- Every operation is driven by some row. -/
theorem every_op_has_a_row (op : Op) : ∃ r ∈ rows, op ∈ r.ops := by
  have h : rows.any (fun r => r.ops.contains op) = true := by cases op <;> decide
  obtain ⟨r, hr, hc⟩ := List.any_eq_true.mp h
  exact ⟨r, hr, List.elem_iff.mp hc⟩

theorem row_names_distinct : (rows.map Row.name).Nodup := by decide

end Nanodregg.Protocol

namespace Nanodregg.Protocol.Rows.Params

/-- The toy rows' budget is `Host.Page.walkTurnsAt_serves`' premise: a record's walk that has
served nothing serves the first step past its start, whatever event the kernel admitted there. -/
theorem toy_budget_serves : Kernel.Bounds.eventBytesMax + 5 ≤ toy.pageBudget := Nat.le_refl _

/-- The deployed rows' budget is `Host.Page.walkTurnsAt_serves`' premise. -/
theorem deployed_budget_serves : Kernel.Bounds.eventBytesMax + 5 ≤ deployed.pageBudget :=
  Nat.le_refl _

end Nanodregg.Protocol.Rows.Params
