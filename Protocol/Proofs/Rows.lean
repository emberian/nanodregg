/-
# Protocol.Proofs.Rows — no operation without a row

The deletion rule as a theorem: an operation that no row drives is not part of the system. Adding
an operation to `Op` without a row that exercises it breaks this proof by name.

The rows' writer pages at HOST's own `Page.budget` under both parameter sets (PROTOCOL-70), so that it
serves every event the kernel admits is HOST's `Host.Page.budget_fits_event`, not a fact of the rows.
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
