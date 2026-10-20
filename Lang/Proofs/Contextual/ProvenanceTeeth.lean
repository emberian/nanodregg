/- P9's first tooth: fixed-environment provenance loses a future answer. -/
import Lang.Proofs.Contextual.Judge
import Lang.Contextual.CoreCalculus

namespace Nanodregg.Lang.Contextual.P9

private def toothIface : Iface cmttData Bool :=
  ⟨0, [], .arr .base .base, [], by simp, fun env _ => env, 10, 1, 2⟩
private def toothCandidate : Candidate cmttData :=
  ⟨.lam .base (.var 0), [], [], 1, 3, .verified⟩
private def toothWorld : World Bool := ⟨fun _ => false, false⟩

/-- Grädel–Tannen (2024), §6 p19: specializing too early erases future answers.
The actual guard edit verifies a candidate absent from the old polynomial. -/
theorem provenance_env_specialized :
    Nanodregg.Lang.Contextual.provenance toothIface toothWorld.env [toothCandidate] = [] ∧
    judge toothIface ((Edit.setEnv true).apply toothWorld) toothCandidate = .verified := by
  decide

end Nanodregg.Lang.Contextual.P9
