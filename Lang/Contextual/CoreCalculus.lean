/-
# Lang.Contextual.CoreCalculus — CMTT's data as a `CalculusData` (lane CMTT-CORE)

The data half of CMTT as an instance of CLOSURE's abstract calculus (`Lang.Contextual.Closure`);
the laws are `Lang.Proofs.Contextual.CoreInstance.cmttLaws`, over the typing judgment
`fun Ω => HasTy (holeEnv Ω)`. A template's holes are the FREE metavariables of a Core term: the
hole named `n` is `mvar (n + d)` under `d` `letbox`es.
-/
import Lang.Contextual.Core
import Lang.Contextual.Closure

namespace Nanodregg.Lang.Contextual

/-- The modal environment of a hole list: the hole named `n` is the first declaration named `n`. -/
def holeEnv (Ω : List (HoleDecl Ctx Ty)) : MEnv := fun n =>
  (Ω.find? fun d => d.name == n).map fun d => (d.ctx, d.ty)

/-- CMTT's data: hand-written decidable equality, hole filling `msubstP θ 0`, the exact checker,
free-variable occurrence, context deletion, strengthening/weakening at a position, variables. -/
def cmttData : CalculusData where
  Ty := Ty
  Ctx := Ctx
  Tm := Tm
  tmEq := Tm.decEq
  msubst θ t := msubstP θ 0 t
  check := check
  uses t x := uses x t
  drop Γ x := Γ.eraseIdx x
  strengthen x t := unshiftAt x t
  weaken x t := shiftAt x t
  var := Tm.var
  lookup Γ x := Γ[x]?

end Nanodregg.Lang.Contextual
