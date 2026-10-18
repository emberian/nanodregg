/-
# Lang.Proofs.PrintTeeth — the round trip's premises hold where it matters, and the printer refuses

`reqTy_reads`: the request type every law takes prints, and its text reads back to it (so
`readTy_ty`'s premises are met by the type the rows and journeys paste). `five_reads`: a datum
reads back at its type; `id_reads` a term with a binder; `empty_package_reads` a package. The refusals: a label that is not one atom has no text, and neither has a
free variable. These are what `none` means.
-/
import Lang.Proofs.Print

namespace Nanodregg.Lang.Print

theorem reqTy_wf : reqTy.wf = true := by decide

theorem reqTy_reads : Read.readTy (tyText reqTy) = .ok reqTy :=
  readTy_ty reqTy_wf (Option.some_get _).symm

theorem five_reads : Read.readData .nat "5" = .ok (.nat 5) :=
  readData_data (.nat (by decide)) rfl (by decide)

theorem spaced_label_refused : ty (.record [("a b", .nat)]) = none := by decide

theorem paren_label_refused : data (.inj "a)" (.nat 0)) = none := by decide

theorem free_var_refused : term (.lam .nat (.var 1)) = none := by decide

theorem bound_var_prints : (term (.lam .nat (.var 0))).isSome = true := by decide

/-- The identity on naturals: a term with a binder reads back from its text. -/
theorem id_reads : Read.readTerm ((term (.lam .nat (.var 0))).get bound_var_prints) = .ok (.lam .nat (.var 0)) :=
  readTerm_term (.lam rfl .var) (Option.some_get _).symm

/-- LANG-51: `refuse` prints as `(refuse T "why")` and reads back; it checks at its annotation, which
must be canonical; `len<=` checks at `bytes, nat`, nothing else. -/
theorem refuse_prints : (term (.refuse .nat ⟨#[108, 97, 116, 101]⟩)).isSome = true := by decide

theorem refuse_reads :
    Read.readTerm ((term (.refuse .nat ⟨#[108, 97, 116, 101]⟩)).get refuse_prints) =
      .ok (.refuse .nat ⟨#[108, 97, 116, 101]⟩) :=
  readTerm_term (.refuse rfl) (Option.some_get _).symm

theorem refuse_typed : infer [] [] (.refuse (.record []) ⟨#[108]⟩) = some (.record []) := by decide +kernel

theorem refuse_unsorted_refused :
    infer [] [] (.refuse (.record [("b", .nat), ("a", .nat)]) ⟨#[108]⟩) = none := by decide +kernel

/-- A reason that is not a printable name is refused by the checker: a newline, and 257 bytes. -/
theorem refuse_newline_refused : infer [] [] (.refuse .nat ⟨#[108, 10]⟩) = none := by decide +kernel

theorem refuse_long_refused : infer [] [] (.refuse .nat ⟨(List.replicate 257 (108 : UInt8)).toArray⟩) = none := by
  decide +kernel

theorem lenLe_typed : infer [] [] (.prim .lenLe (.bytes ⟨#[1]⟩) (.nat 3)) = some .bool := by decide +kernel

theorem lenLe_nat_refused : infer [] [] (.prim .lenLe (.nat 1) (.nat 3)) = none := by decide +kernel

/-- The empty package (WireTeeth's `tiny`): `readPackage_package`'s premises are met. -/
theorem empty_package_prints : (package (Package.mk [] (.record []) (.record []) (.record []) [] [] [])).isSome = true := by
  decide

theorem empty_package_reads :
    Read.readPackage ((package (Package.mk [] (.record []) (.record []) (.record []) [] [] [])).get empty_package_prints) =
      .ok (Package.mk [] (.record []) (.record []) (.record []) [] [] []) :=
  readPackage_package rfl rfl rfl (.record rfl .nil) (Option.some_get _).symm

/-- A relation whose value type is not canonical (a record with its fields descending): the
package prints, and reads back as a DIFFERENT package (the reader sorts the fields), so
`readPackage_package`'s `relWf` premise is not idle. -/
private def badRel : Package :=
  Package.mk [] (.record []) (.record []) (.record []) [] []
    [("r", { key := [("k", .nat)], val := .record [("b", .nat), ("a", .nat)], limit := 1, sum := none,
             cap := 0, retract := false, guard := none })]

theorem badRel_prints : (package badRel).isSome = true := by decide

theorem badRel_reads_other :
    (match Read.readPackage ((package badRel).get badRel_prints) with
     | .ok q => decide (q.rels ≠ badRel.rels)
     | .error _ => false) = true := by
  native_decide

end Nanodregg.Lang.Print
