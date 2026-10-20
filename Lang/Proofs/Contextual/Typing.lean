/-
# Lang.Proofs.Contextual.Typing — the judgments of `Lang.Contextual.Core` (lane CMTT-CORE)

`HasTy Δ Γ t A` is CMTT's typing judgment; `HasSubst Δ Γ σ Ψ` (`σ : Ψ` under `Δ; Γ`) its pointwise
lift, inlined into the `mvar` rule so the judgment is one inductive (`HasTy.mvar'` is the textbook
rule); `Step` is weak-head reduction. Statements, hence a proof module (gate C3).
-/
import Lang.Contextual.Core

namespace Nanodregg.Lang.Contextual

/-! ## Typing -/

/-- `HasTy Δ Γ t A`: CMTT's typing judgment, `Δ; Γ ⊢ t : A`. -/
inductive HasTy : MEnv → Ctx → Tm → Ty → Prop
  | var {Δ : MEnv} {Γ : Ctx} {i : Nat} {A : Ty} :
      Γ[i]? = some A → HasTy Δ Γ (.var i) A
  | lam {Δ : MEnv} {Γ : Ctx} {A B : Ty} {t : Tm} :
      HasTy Δ (A :: Γ) t B → HasTy Δ Γ (.lam A t) (.arr A B)
  | app {Δ : MEnv} {Γ : Ctx} {A B : Ty} {t s : Tm} :
      HasTy Δ Γ t (.arr A B) → HasTy Δ Γ s A → HasTy Δ Γ (.app t s) B
  /-- The body is typed under `Ψ` ONLY; the ambient `Γ` is not available. -/
  | box {Δ : MEnv} {Γ Ψ : Ctx} {A : Ty} {t : Tm} :
      HasTy Δ Ψ t A → HasTy Δ Γ (.box Ψ t) (.box Ψ A)
  | letbox {Δ : MEnv} {Γ Ψ : Ctx} {A B : Ty} {t s : Tm} :
      HasTy Δ Γ t (.box Ψ A) → HasTy (MEnv.cons (Ψ, A) Δ) Γ s B → HasTy Δ Γ (.letbox t s) B
  /-- `u :: (Ψ ⊢ A) ∈ Δ` and `σ : Ψ` (the premises of `HasSubst`, inlined). -/
  | mvar {Δ : MEnv} {Γ Ψ : Ctx} {A : Ty} {u : Nat} {σ : List Tm} :
      Δ u = some (Ψ, A) → σ.length = Ψ.length →
      (∀ (i : Nat) (s : Tm) (C : Ty), σ[i]? = some s → Ψ[i]? = some C → HasTy Δ Γ s C) →
      HasTy Δ Γ (.mvar u σ) A

/-- `HasSubst Δ Γ σ Ψ`: `Δ; Γ ⊢ σ : Ψ`, pointwise. -/
def HasSubst (Δ : MEnv) (Γ : Ctx) (σ : List Tm) (Ψ : Ctx) : Prop :=
  σ.length = Ψ.length ∧
    ∀ (i : Nat) (s : Tm) (C : Ty), σ[i]? = some s → Ψ[i]? = some C → HasTy Δ Γ s C

/-- The `mvar` rule in its textbook form: `u :: (Ψ ⊢ A) ∈ Δ` and `Δ; Γ ⊢ σ : Ψ`. -/
theorem HasTy.mvar' {Δ : MEnv} {Γ Ψ : Ctx} {A : Ty} {u : Nat} {σ : List Tm}
    (hu : Δ u = some (Ψ, A)) (hσ : HasSubst Δ Γ σ Ψ) : HasTy Δ Γ (.mvar u σ) A :=
  .mvar hu hσ.1 hσ.2

/-! ## Reduction -/

/-- Weak-head small-step reduction: β, the contextual β (`letbox (box Ψ t) s ↦ ⟦Ψ.t/u⟧s`), and
congruence in the function position of `app` and the scrutinee of `letbox`. Nothing reduces under
`lam` or inside `box` (a box body is closed over its own `Ψ` and is a value). -/
inductive Step : Tm → Tm → Prop
  | beta {A : Ty} {t s : Tm} : Step (.app (.lam A t) s) (subst [s] t)
  | letboxBox {Ψ : Ctx} {t s : Tm} : Step (.letbox (.box Ψ t) s) (msubst t 0 s)
  | appL {t t' s : Tm} : Step t t' → Step (.app t s) (.app t' s)
  | letboxL {t t' s : Tm} : Step t t' → Step (.letbox t s) (.letbox t' s)

end Nanodregg.Lang.Contextual
