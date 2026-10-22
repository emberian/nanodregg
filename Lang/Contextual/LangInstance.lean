/-
# Lang.Contextual.LangInstance — the DEPLOYED term language as a contextual calculus

`CalculusData` is the data of a contextual calculus (its laws, with the typing relation, are `CalculusLaws` in
`Lang.Proofs.Contextual.LangInstance`); `langData` is `Lang.Term` as one, built from the operations the Host
runs (`Lang.Subst`): `msubst` is `fillRefs`; strengthening and weakening rename ordinary variables at a position
with `lowerIdx`/`liftIdx` (`Lang.Index`). It is the only instance: the deployed hole judgment is `selectHole`
(`Lang.LiveHoles`), a substituted hole `Term.hole n σ` is CMTT's closure `clo(u, σ)`, and `HoleCode.body` is a
`box` at ROM grain (C2, R3: LANG-75.3). No deployed module imports this one.
-/
import Lang.Subst

namespace Nanodregg.Lang.Contextual

/-- The DATA of a contextual calculus (its laws, with the typing relation, are `CalculusLaws`). -/
structure CalculusData where
  Ty : Type
  Ctx : Type
  Tm : Type
  tmEq : DecidableEq Tm
  /-- Simultaneous meta-substitution `⟦σ⟧P` for a PARTIAL `σ` (unfilled holes stay). -/
  msubst : (Nat → Option Tm) → Tm → Tm
  /-- The checker: a proposed filling acquires authority only through it. -/
  check : Ctx → Tm → Ty → Bool
  /-- `uses M x`: the filling mentions hypothesis `x` of its context (free-variable occurrence). -/
  uses : Tm → Nat → Bool
  /-- The context without hypothesis `x`. -/
  drop : Ctx → Nat → Ctx
  /-- Strengthening `t ≡ t₀[π]`: `strengthen x t` is `t₀`, `weaken x` is `π`. -/
  strengthen : Nat → Tm → Tm
  weaken : Nat → Tm → Tm
  /-- The variable term for hypothesis `x`. -/
  var : Nat → Tm
  /-- The type a context gives hypothesis `x`, if it has one. -/
  lookup : Ctx → Nat → Option Ty

instance (D : CalculusData) : DecidableEq D.Tm := D.tmEq

/-- `Lang.Term` as a `CalculusData`. -/
def langData : CalculusData where
  Ty := Lang.Ty
  Ctx := List Lang.Ty
  Tm := Term
  tmEq := Term.decEq
  msubst := Term.fillRefs
  check Ψ M A := decide (Lang.infer [] Ψ M (Ω := []) = some A)
  uses M x := Term.usesVar x M
  drop Ψ x := Ψ.eraseIdx x
  strengthen x := Term.renameVar (lowerIdx x)
  weaken x := Term.renameVar (liftIdx x)
  var := Term.var
  lookup Ψ x := Ψ[x]?

end Nanodregg.Lang.Contextual
