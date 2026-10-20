import Lang.Contextual.ContextMorphisms
import Lang.Proofs.Contextual.Core

namespace Nanodregg.Lang.Contextual.ContextMorphisms

/-- Context morphisms map each declared variable to a term of the same type
(Cave–Pientka p1). -/
def Valid {Γ Ψ : Ctx} (Δ : MEnv) (s : Morphism Γ Ψ) : Prop :=
  ∀ i A, Γ[i]? = some A → HasTy Δ Ψ (s.term i) A

/-- The morphism action preserves typing (Cave–Pientka pp1–2). -/
theorem apply_typed {Γ Ψ : Ctx} {Δ : MEnv} {s : Morphism Γ Ψ}
    (hs : Valid Δ s) {t : Tm} {A : Ty} (ht : HasTy Δ Γ t A) :
    HasTy Δ Ψ (apply s t) A :=
  hasTy_substFn ht Ψ s.term hs

/-- Identity substitution is scoped and typed (Cave–Pientka p2). -/
theorem identity_valid (Δ : MEnv) (Γ : Ctx) : Valid Δ (identity Γ) := by
  intro i A h
  exact .var h

/-- Composed substitutions remain scoped (Cave–Pientka pp1–2). -/
theorem compose_valid {Γ Ψ Φ : Ctx} {Δ : MEnv}
    {s : Morphism Γ Ψ} {t : Morphism Ψ Φ} (hs : Valid Δ s) (ht : Valid Δ t) :
    Valid Δ (compose s t) := by
  intro i A h
  exact apply_typed ht (hs i A h)

/-- Substitution composition agrees with sequential application (Cave–Pientka p2). -/
theorem apply_compose {Γ Ψ Φ : Ctx} (s : Morphism Γ Ψ) (t : Morphism Ψ Φ) (a : Tm) :
    apply (compose s t) a = apply t (apply s a) :=
  (substFn_substFn t.term s.term a).symm

/-- Identity acts on terms, including under binders (Cave–Pientka p2). -/
theorem apply_identity (Γ : Ctx) (a : Tm) : apply (identity Γ) a = a := substFn_var a

/-- Weakening preserves each declared variable (Cave–Pientka p1). -/
theorem weakening_valid (Δ : MEnv) (Γ : Ctx) (A : Ty) :
    Valid Δ (weakening Γ A) := by
  intro i B h
  exact .var h

/-- Exchange is typed for heterogeneous adjacent variables (Cave–Pientka p1). -/
theorem exchange_valid (Δ : MEnv) (Γ : Ctx) (A B : Ty) :
    Valid Δ (exchange Γ A B) := by
  intro i C h
  cases i with
  | zero =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst C
    exact .var rfl
  | succ i =>
    cases i with
    | zero =>
      simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at h
      subst C
      exact .var rfl
    | succ i => exact .var h

/-- A strengthening result is typed in the reduced context and reconstructs the original
through projection (Cave–Pientka p1; CMTT factorization). -/
theorem strengthen_sound {Δ : MEnv} {Γ : Ctx} {t s : Tm} {A : Ty} {x : Nat}
    (ht : HasTy Δ Γ t A) (h : strengthen x t = some s) :
    HasTy Δ (Γ.eraseIdx x) s A ∧ shiftAt x s = t := by
  unfold strengthen at h
  split at h
  · cases h
  · rename_i hu
    have hfalse : uses x t = false := Bool.eq_false_iff.2 hu
    cases h
    exact ⟨hasTy_unshiftAt ht hfalse, shiftAt_unshiftAt hfalse⟩

/-- Removing a used hypothesis refuses; exchanging distinct typed variables computes
(Cave–Pientka p1). -/
theorem scope_teeth :
    strengthen 0 (.var 0) = none ∧
    apply (exchange [] .base (.arr .base .base)) (.var 0) = .var 1 := by decide

end Nanodregg.Lang.Contextual.ContextMorphisms
