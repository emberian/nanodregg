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

/-- The empty package (WireTeeth's `tiny`): `readPackage_package`'s premises are met. -/
theorem empty_package_prints : (package (Package.mk [] (.record []) (.record []) (.record []) [] [])).isSome = true := by
  decide

theorem empty_package_reads :
    Read.readPackage ((package (Package.mk [] (.record []) (.record []) (.record []) [] [])).get empty_package_prints) =
      .ok (Package.mk [] (.record []) (.record []) (.record []) [] []) :=
  readPackage_package rfl rfl (.record rfl .nil) (Option.some_get _).symm

end Nanodregg.Lang.Print
