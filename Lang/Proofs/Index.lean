/- The de Bruijn index maps of `Lang.Index` compose: the facts both the deployed renaming
(`Lang.Proofs.Subst`) and the CMTT core (`Lang.Proofs.Contextual.Core`) rewrite with. -/
import Lang.Index

namespace Nanodregg.Lang

theorem upR_upR (ρ ρ' : Nat → Nat) :
    (fun i => upR ρ (upR ρ' i)) = upR (fun i => ρ (ρ' i)) := by
  funext i; cases i <;> rfl

theorem upR_id : upR (fun i => i) = (fun i => i) := by
  funext i; cases i <;> rfl

end Nanodregg.Lang
