/-
# Protocol.Proofs.Rows — no operation without a row

The deletion rule as a theorem: an operation that no row drives is not part of the system. Adding
an operation to `Op` without a row that exercises it breaks this proof by name.
-/
import Protocol.Rows
import Protocol.Proofs.Table

namespace Nanodregg.Protocol

/-- Every operation that is not reserved is driven by some row. -/
theorem every_op_has_a_row (op : Op) (h : op.reserved = false) : ∃ r ∈ rows, op ∈ r.ops := by
  have h : rows.any (fun r => r.ops.contains op) = true := by cases op <;> first | decide | cases h
  obtain ⟨r, hr, hc⟩ := List.any_eq_true.mp h
  exact ⟨r, hr, List.elem_iff.mp hc⟩

/-- No row claims a reserved operation. -/
theorem no_row_claims_reserved : ∀ r ∈ rows, ∀ op ∈ r.ops, op.reserved = false := by decide

theorem row_names_distinct : (rows.map Row.name).Nodup := by decide

end Nanodregg.Protocol
