/- Ordinary substitution preserves the deployed typing judgment.
No new assumption is attached to a landed theorem. -/
import Lang.Subst
import Lang.Proofs.Contextual.LangRenaming

namespace Nanodregg.Lang.Contextual

/-- Substitution changes field bodies, never their labels or order. -/
theorem substVarRow_ascending (σ : Nat → Term) :
    ∀ fs : List (Label × Term), Row.ascending (Term.substVarRow σ fs) = Row.ascending fs
  | [] => rfl
  | [_] => rfl
  | (a, s) :: (b, t) :: rest => by
      have ih := substVarRow_ascending σ ((b, t) :: rest)
      simp only [Term.substVarRow] at ih ⊢
      simp only [Row.ascending, ih]

/-- A typed substitution remains typed under a fresh binder. -/
theorem upVarSubst_typed {Δ Γ Γ' : List Lang.Ty} {Ω : HoleSignature} (A : Lang.Ty) (σ : Nat → Term)
    (hσ : ∀ i B, Γ[i]? = some B → HasType (Ω := Ω) Δ Γ' (σ i) B) :
    ∀ i B, (A :: Γ)[i]? = some B → HasType (Ω := Ω) Δ (A :: Γ') (Term.upVarSubst σ i) B
  | 0, B, h => by
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst B
      exact .var rfl
  | i + 1, B, h => by
      exact hasType_renameVar_live (hσ i B (by simpa using h)) (A :: Γ') Nat.succ
        (fun j C _ hj => by simpa using hj)

mutual
/-- Substitution's typing lemma, over every deployed term and ambient context. -/
theorem substVar_typed {Δ : List Lang.Ty} {Ω : HoleSignature} :
    ∀ {Γ : List Lang.Ty} {t : Term} {T : Lang.Ty}, HasType (Ω := Ω) Δ Γ t T →
      ∀ (Γ' : List Lang.Ty) (σ : Nat → Term),
        (∀ i B, Γ[i]? = some B → HasType (Ω := Ω) Δ Γ' (σ i) B) →
        HasType (Ω := Ω) Δ Γ' (Term.substVar σ t) T
  | _, _, _, .var h, _, _, hσ => hσ _ _ h
  | _, _, _, .lam (A := A) hw hb, Γ', σ, hσ =>
      .lam hw (substVar_typed hb (A :: Γ') (Term.upVarSubst σ) (upVarSubst_typed A σ hσ))
  | _, _, _, .app hf ha, Γ', σ, hσ =>
      .app (substVar_typed hf Γ' σ hσ) (substVar_typed ha Γ' σ hσ)
  | _, _, _, .fix h, Γ', σ, hσ => .fix (substVar_typed h Γ' σ hσ)
  | _, _, _, .nat h, _, _, _ => .nat h
  | _, _, _, .bool, _, _, _ => .bool
  | _, _, _, .bytes h, _, _, _ => .bytes h
  | _, _, _, .digest h, _, _, _ => .digest h
  | _, _, _, .prim ha hb, Γ', σ, hσ =>
      .prim (substVar_typed ha Γ' σ hσ) (substVar_typed hb Γ' σ hσ)
  | _, _, _, .record ha hf, Γ', σ, hσ => by
      exact .record (by rw [substVarRow_ascending]; exact ha)
        (substVarFields_typed hf Γ' σ hσ)
  | _, _, _, .get ht hl, Γ', σ, hσ => .get (substVar_typed ht Γ' σ hσ) hl
  | _, _, _, .extend ht ha hf, Γ', σ, hσ => by
      exact .extend (substVar_typed ht Γ' σ hσ)
        (by rw [substVarRow_ascending]; exact ha) (substVarFields_typed hf Γ' σ hσ)
  | _, _, _, .inj hw hl ht, Γ', σ, hσ => .inj hw hl (substVar_typed ht Γ' σ hσ)
  | _, _, _, .case ht ha, Γ', σ, hσ =>
      .case (substVar_typed ht Γ' σ hσ) (substVarArms_typed ha Γ' σ hσ)
  | _, _, _, .ite hc ha hb, Γ', σ, hσ =>
      .ite (substVar_typed hc Γ' σ hσ) (substVar_typed ha Γ' σ hσ) (substVar_typed hb Γ' σ hσ)
  | _, _, _, .ref h, _, _, _ => .ref h
  | _, _, _, .refuse hw hn, _, _, _ => .refuse hw hn
  | _, _, _, .hole hd hs, Γ', σ, hσ =>
      .hole hd (substVarSubst_typed hs Γ' σ hσ)
theorem substVarSubst_typed {Δ : List Lang.Ty} {Ω : HoleSignature} :
    ∀ {Γ : List Lang.Ty} {ts : List Term} {Ψ : List Lang.Ty}, SubstTy Δ Γ ts Ψ Ω →
      ∀ (Γ' : List Lang.Ty) (σ : Nat → Term),
        (∀ i B, Γ[i]? = some B → HasType Δ Γ' (σ i) B Ω) →
        SubstTy Δ Γ' (Term.substVarList σ ts) Ψ Ω
  | _, _, _, .nil, _, _, _ => .nil
  | _, _, _, .cons ht hs, Γ', σ, hσ =>
      .cons (substVar_typed ht Γ' σ hσ) (substVarSubst_typed hs Γ' σ hσ)
theorem substVarFields_typed {Δ : List Lang.Ty} {Ω : HoleSignature} :
    ∀ {Γ : List Lang.Ty} {fs : List (Label × Term)} {r : List (Label × Lang.Ty)},
      FieldsTy (Ω := Ω) Δ Γ fs r → ∀ (Γ' : List Lang.Ty) (σ : Nat → Term),
        (∀ i B, Γ[i]? = some B → HasType (Ω := Ω) Δ Γ' (σ i) B) →
        FieldsTy (Ω := Ω) Δ Γ' (Term.substVarRow σ fs) r
  | _, _, _, .nil, _, _, _ => .nil
  | _, _, _, .cons h hs, Γ', σ, hσ =>
      .cons (substVar_typed h Γ' σ hσ) (substVarFields_typed hs Γ' σ hσ)
theorem substVarArms_typed {Δ : List Lang.Ty} {Ω : HoleSignature} :
    ∀ {Γ : List Lang.Ty} {arms : List (Label × Term)} {r : List (Label × Lang.Ty)} {T : Lang.Ty},
      ArmsTy (Ω := Ω) Δ Γ arms r T → ∀ (Γ' : List Lang.Ty) (σ : Nat → Term),
        (∀ i B, Γ[i]? = some B → HasType (Ω := Ω) Δ Γ' (σ i) B) →
        ArmsTy (Ω := Ω) Δ Γ' (Term.substVarArms σ arms) r T
  | _, _, _, _, .one (A := A) h, Γ', σ, hσ =>
      .one (substVar_typed h (A :: Γ') (Term.upVarSubst σ) (upVarSubst_typed A σ hσ))
  | _, _, _, _, .cons (A := A) (arms := a :: arms) h hs _, Γ', σ, hσ =>
      .cons (substVar_typed h (A :: Γ') (Term.upVarSubst σ) (upVarSubst_typed A σ hσ))
        (substVarArms_typed hs Γ' σ hσ) (by simp [Term.substVarArms])
  | _, _, _, _, .cons (arms := []) _ _ hne, _, _, _ => absurd rfl hne
end

/-- Every component is checked against the corresponding context entry.
The nil rule forbids both missing and extra arguments. -/
abbrev LangSubstTy (Δ Γ : List Lang.Ty) (ts : List Term) (Ψ : List Lang.Ty)
    (Ω : optParam HoleSignature []) : Prop := SubstTy Δ Γ ts Ψ Ω

theorem substListFn_typed {Δ Γ : List Lang.Ty} {Ω : HoleSignature} :
    ∀ {σ : List Term} {Ψ : List Lang.Ty}, LangSubstTy (Ω := Ω) Δ Γ σ Ψ →
      ∀ i A, Ψ[i]? = some A → HasType (Ω := Ω) Δ Γ (Term.substListFn σ i) A
  | _, _, .nil, i, A, h => by simp at h
  | _, _, .cons ht _, 0, A, h => by
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst A
      exact ht
  | _, _, .cons _ hs, i + 1, A, h =>
      substListFn_typed hs i A (by simpa using h)

/-- An explicit substitution instantiates a term checked in its own context. -/
theorem substList_typed {Δ Γ Ψ : List Lang.Ty} {Ω : HoleSignature} {σ : List Term} {t : Term} {T : Lang.Ty}
    (hσ : LangSubstTy (Ω := Ω) Δ Γ σ Ψ) (ht : HasType (Ω := Ω) Δ Ψ t T) :
    HasType (Ω := Ω) Δ Γ (Term.substList σ t) T :=
  substVar_typed ht Γ (Term.substListFn σ) (substListFn_typed hσ)

/-- A free variable supplied by the ambient context survives a lambda. -/
theorem substList_lam_capture :
    Term.substList [.var 0] (.lam .bool (.var 1)) = .lam .bool (.var 1) := rfl

/-- A case arm binds its payload; the substituted free variable is not that payload. -/
theorem substList_case_capture :
    Term.substList [.var 0]
      (.case (.inj (.sum [("a", .bool)]) "a" (.bool true)) [("a", .var 1)]) =
      .case (.inj (.sum [("a", .bool)]) "a" (.bool true)) [("a", .var 1)] := rfl

/-- Two nested binders shift the supplied variable twice. -/
theorem substList_nested_capture :
    Term.substList [.var 0] (.lam .bool (.lam .bytes (.var 2))) =
      .lam .bool (.lam .bytes (.var 2)) := rfl

/-- Distinct replacement types make capture observable to the real checker. -/
theorem substList_ambient_checked :
    Lang.infer [] [.nat] (Term.substList [.var 0] (.lam .bool (.var 1))) =
      some (.fn .bool .nat) := by
  rw [substList_lam_capture]
  exact Lang.infer_complete (.lam (by decide) (.var rfl))

/-- The former hypothesis is actually replaced, not left untouched. -/
theorem substList_replaces :
    Term.substList [.nat 7] (.lam .bool (.var 1)) = .lam .bool (.nat 7) := rfl

end Nanodregg.Lang.Contextual
