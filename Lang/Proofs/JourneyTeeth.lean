/-
# Lang.Proofs.JourneyTeeth — the journey's packages pass (and fail) the install check as terms

`law_never_stuck` and `invoke_never_stuck` hang on a loaded package, and `load` re-runs
`Package.checkWith`; these pin, by the kernel evaluating the checker, that a package with a method
and two laws passes it (so the closure invariant's checked-package conjunct is satisfiable by a
package with laws), and that the ill-typed twin does not.
-/
import Lang.Journey

namespace Nanodregg.Lang.Teeth

private def isOk : Except CheckError Unit → Bool
  | .ok () => true
  | .error _ => false

private def isIllTyped : Except CheckError Unit → Bool
  | .error (.illTyped _) => true
  | _ => false

theorem owned_checks : isOk (Journey.owned.checkWith []) = true := by decide +kernel

theorem illTyped_refused : isIllTyped (Journey.illTyped.checkWith []) = true := by decide +kernel

end Nanodregg.Lang.Teeth
