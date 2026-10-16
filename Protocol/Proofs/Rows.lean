/-
# Protocol.Proofs.Rows — no operation without a row

The deletion rule as a theorem: an operation that no row drives is not part of the system. Adding
an operation to `Op` without a row that exercises it breaks this proof by name.
-/
import Protocol.Rows
import Protocol.Proofs.Table

namespace Nanodregg.Protocol

theorem every_op_has_a_row (op : Op) : ∃ r ∈ rows, op ∈ r.ops := by
  have h : rows.any (fun r => r.ops.contains op) = true := by cases op <;> decide
  obtain ⟨r, hr, hc⟩ := List.any_eq_true.mp h
  exact ⟨r, hr, List.elem_iff.mp hc⟩

theorem row_names_distinct : (rows.map Row.name).Nodup := by decide

end Nanodregg.Protocol
