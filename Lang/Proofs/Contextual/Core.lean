/-
# Lang.Proofs.Contextual.Core — the metatheory of `Lang.Contextual.Core` (lane CMTT-CORE)

* equations: `rename_rename`, `mren_mren`, `mren_rename`, `substFn_rename`, `rename_substFn`,
  `mren_substFn`, `substFn_substFn`, `substFn_var`, `substFn_congr`, and `subst_comp`
  (`subst τ (subst σ t) = subst (comp τ σ) t`, unconditionally);
* typing: `hasTy_rename` (renaming restricted to USED variables), `hasTy_weaken`,
  `hasTy_weaken_append`, `hasTy_mren`, `hasTy_mweaken`, `hasTy_substFn`, `subst_lemma`,
  `hasSubst_id`, `hasSubst_proj`, `hasTy_msubst_gen` / `msubst_lemma`, `hasTy_uses_lt`,
  `strengthen` (factorisation through the projection `π`);
* teeth: `box_cannot_capture` (+ `_toy`), `box_ambient_free`, `mvar_blocked` and
  `subst_keeps_blocked` (definitional), `msubst_mvar_self`, `msubst_unblocks`,
  `msubst_other_blocked` (+ `mvar_blocked_toy`), `strengthen_needs_unused`;
* the checker: `Ty.beq_iff`, `Tm.beq_iff` (the instances are Core's), `infer_sound`,
  `infer_complete`, `check_sound`, `check_complete`;
* strengthening at any position: `rename_congr`, `shiftAt_unshiftAt`, `hasTy_unshiftAt`,
  `uses_rename`, `uses_shiftAt`;
* hole filling: `hasTy_msubstP`;
* reduction: `hasTy_beta`, `subject_reduction`, `step_deterministic`, `no_step_under_box`,
  `lam_no_step`, `var_no_step`, `mvar_no_step`, `letbox_needs_box` (+ `_toy`s);
* toy instances: `bell_resume_computes`, `bell_resume_toy`, `subst_lemma_toy`, `subst_comp_toy`, `msubst_lemma_toy`, `letbox_toy`,
  `strengthen_toy`, `weaken_toy`.
-/
import Lang.Proofs.Contextual.Typing

namespace Nanodregg.Lang.Contextual

/-! ## List forms -/

theorem renameL_eq (ρ : Nat → Nat) : ∀ σ : List Tm, renameL ρ σ = σ.map (rename ρ)
  | [] => rfl
  | t :: σ => by simp only [renameL, renameL_eq ρ σ, List.map_cons]

theorem mrenL_eq (ρ : Nat → Nat) : ∀ σ : List Tm, mrenL ρ σ = σ.map (mren ρ)
  | [] => rfl
  | t :: σ => by simp only [mrenL, mrenL_eq ρ σ, List.map_cons]

theorem substFnL_eq (f : Nat → Tm) : ∀ σ : List Tm, substFnL f σ = σ.map (substFn f)
  | [] => rfl
  | t :: σ => by simp only [substFnL, substFnL_eq f σ, List.map_cons]

theorem msubstL_eq (s : Tm) (u : Nat) : ∀ σ : List Tm, msubstL s u σ = σ.map (msubst s u)
  | [] => rfl
  | t :: σ => by simp only [msubstL, msubstL_eq s u σ, List.map_cons]

theorem usesL_of_getElem? (k : Nat) :
    ∀ (σ : List Tm) (i : Nat) (s : Tm), σ[i]? = some s → uses k s = true → usesL k σ = true
  | [], _, _, h, _ => by simp at h
  | t :: σ, 0, s, h, hu => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h; simp [usesL, hu]
  | t :: σ, i + 1, s, h, hu => by
    simp only [List.getElem?_cons_succ] at h
    simp [usesL, usesL_of_getElem? k σ i s h hu]

theorem usesL_true (k : Nat) :
    ∀ σ : List Tm, usesL k σ = true → ∃ (i : Nat) (s : Tm), σ[i]? = some s ∧ uses k s = true
  | [], h => by simp [usesL] at h
  | t :: σ, h => by
    simp only [usesL, Bool.or_eq_true] at h
    rcases h with h | h
    · exact ⟨0, t, rfl, h⟩
    · obtain ⟨i, s, hi, hs⟩ := usesL_true k σ h
      exact ⟨i + 1, s, by simpa using hi, hs⟩

/-! ## Renamings compose -/

theorem upR_upR (ρ ρ' : Nat → Nat) :
    (fun i => upR ρ (upR ρ' i)) = upR (fun i => ρ (ρ' i)) := by
  funext i; cases i <;> rfl

theorem upR_id : upR (fun i => i) = (fun i => i) := by
  funext i; cases i <;> rfl

mutual
theorem rename_rename (ρ ρ' : Nat → Nat) :
    ∀ t : Tm, rename ρ (rename ρ' t) = rename (fun i => ρ (ρ' i)) t
  | .var _ => rfl
  | .lam A t => by simp only [rename, rename_rename (upR ρ) (upR ρ') t, upR_upR]
  | .app t s => by simp only [rename, rename_rename ρ ρ' t, rename_rename ρ ρ' s]
  | .box _ _ => rfl
  | .letbox t s => by simp only [rename, rename_rename ρ ρ' t, rename_rename ρ ρ' s]
  | .mvar u σ => by simp only [rename, renameL_renameL ρ ρ' σ]
theorem renameL_renameL (ρ ρ' : Nat → Nat) :
    ∀ σ : List Tm, renameL ρ (renameL ρ' σ) = renameL (fun i => ρ (ρ' i)) σ
  | [] => rfl
  | t :: σ => by simp only [renameL, rename_rename ρ ρ' t, renameL_renameL ρ ρ' σ]
end

mutual
theorem rename_id : ∀ t : Tm, rename (fun i => i) t = t
  | .var _ => rfl
  | .lam A t => by simp only [rename, upR_id, rename_id t]
  | .app t s => by simp only [rename, rename_id t, rename_id s]
  | .box _ _ => rfl
  | .letbox t s => by simp only [rename, rename_id t, rename_id s]
  | .mvar u σ => by simp only [rename, renameL_id σ]
theorem renameL_id : ∀ σ : List Tm, renameL (fun i => i) σ = σ
  | [] => rfl
  | t :: σ => by simp only [renameL, rename_id t, renameL_id σ]
end

mutual
theorem mren_mren (ρ ρ' : Nat → Nat) :
    ∀ t : Tm, mren ρ (mren ρ' t) = mren (fun i => ρ (ρ' i)) t
  | .var _ => rfl
  | .lam A t => by simp only [mren, mren_mren ρ ρ' t]
  | .app t s => by simp only [mren, mren_mren ρ ρ' t, mren_mren ρ ρ' s]
  | .box Ψ t => by simp only [mren, mren_mren ρ ρ' t]
  | .letbox t s => by simp only [mren, mren_mren ρ ρ' t, mren_mren (upR ρ) (upR ρ') s, upR_upR]
  | .mvar u σ => by simp only [mren, mrenL_mrenL ρ ρ' σ]
theorem mrenL_mrenL (ρ ρ' : Nat → Nat) :
    ∀ σ : List Tm, mrenL ρ (mrenL ρ' σ) = mrenL (fun i => ρ (ρ' i)) σ
  | [] => rfl
  | t :: σ => by simp only [mrenL, mren_mren ρ ρ' t, mrenL_mrenL ρ ρ' σ]
end

mutual
/-- Metavariable renaming and ordinary renaming commute. -/
theorem mren_rename (ρ ρ' : Nat → Nat) :
    ∀ t : Tm, mren ρ (rename ρ' t) = rename ρ' (mren ρ t)
  | .var _ => rfl
  | .lam A t => by simp only [mren, rename, mren_rename ρ (upR ρ') t]
  | .app t s => by simp only [mren, rename, mren_rename ρ ρ' t, mren_rename ρ ρ' s]
  | .box _ _ => rfl
  | .letbox t s => by
    simp only [mren, rename, mren_rename ρ ρ' t, mren_rename (upR ρ) ρ' s]
  | .mvar u σ => by simp only [mren, rename, mrenL_renameL ρ ρ' σ]
theorem mrenL_renameL (ρ ρ' : Nat → Nat) :
    ∀ σ : List Tm, mrenL ρ (renameL ρ' σ) = renameL ρ' (mrenL ρ σ)
  | [] => rfl
  | t :: σ => by simp only [mrenL, renameL, mren_rename ρ ρ' t, mrenL_renameL ρ ρ' σ]
end

/-! ## Substitution meets renaming -/

mutual
theorem substFn_rename (f : Nat → Tm) (ρ : Nat → Nat) :
    ∀ t : Tm, substFn f (rename ρ t) = substFn (fun i => f (ρ i)) t
  | .var _ => rfl
  | .lam A t => by
    have h : (fun i => upS f (upR ρ i)) = upS (fun i => f (ρ i)) := by
      funext i; cases i <;> rfl
    simp only [rename, substFn, substFn_rename (upS f) (upR ρ) t, h]
  | .app t s => by simp only [rename, substFn, substFn_rename f ρ t, substFn_rename f ρ s]
  | .box _ _ => rfl
  | .letbox t s => by
    simp only [rename, substFn, substFn_rename f ρ t, substFn_rename (mshiftS f) ρ s]; rfl
  | .mvar u σ => by simp only [rename, substFn, substFnL_renameL f ρ σ]
theorem substFnL_renameL (f : Nat → Tm) (ρ : Nat → Nat) :
    ∀ σ : List Tm, substFnL f (renameL ρ σ) = substFnL (fun i => f (ρ i)) σ
  | [] => rfl
  | t :: σ => by simp only [renameL, substFnL, substFn_rename f ρ t, substFnL_renameL f ρ σ]
end

mutual
theorem rename_substFn (ρ : Nat → Nat) (f : Nat → Tm) :
    ∀ t : Tm, rename ρ (substFn f t) = substFn (fun i => rename ρ (f i)) t
  | .var _ => rfl
  | .lam A t => by
    have h : (fun i => rename (upR ρ) (upS f i)) = upS (fun i => rename ρ (f i)) := by
      funext i; cases i with
      | zero => rfl
      | succ j =>
        simp only [upS, rename_rename]; rfl
    simp only [rename, substFn, rename_substFn (upR ρ) (upS f) t, h]
  | .app t s => by simp only [rename, substFn, rename_substFn ρ f t, rename_substFn ρ f s]
  | .box _ _ => rfl
  | .letbox t s => by
    have h : (fun i => rename ρ (mshiftS f i)) = mshiftS (fun i => rename ρ (f i)) := by
      funext i; simp only [mshiftS, mshift, mren_rename]
    simp only [rename, substFn, rename_substFn ρ f t, rename_substFn ρ (mshiftS f) s, h]
  | .mvar u σ => by simp only [rename, substFn, renameL_substFnL ρ f σ]
theorem renameL_substFnL (ρ : Nat → Nat) (f : Nat → Tm) :
    ∀ σ : List Tm, renameL ρ (substFnL f σ) = substFnL (fun i => rename ρ (f i)) σ
  | [] => rfl
  | t :: σ => by simp only [renameL, substFnL, rename_substFn ρ f t, renameL_substFnL ρ f σ]
end

mutual
/-- Metavariable renaming distributes over ordinary substitution. -/
theorem mren_substFn (ρ : Nat → Nat) (f : Nat → Tm) :
    ∀ t : Tm, mren ρ (substFn f t) = substFn (fun i => mren ρ (f i)) (mren ρ t)
  | .var _ => rfl
  | .lam A t => by
    have h : (fun i => mren ρ (upS f i)) = upS (fun i => mren ρ (f i)) := by
      funext i; cases i with
      | zero => rfl
      | succ j => simp only [upS, mren_rename]
    simp only [mren, substFn, mren_substFn ρ (upS f) t, h]
  | .app t s => by simp only [mren, substFn, mren_substFn ρ f t, mren_substFn ρ f s]
  | .box _ _ => rfl
  | .letbox t s => by
    have h : (fun i => mren (upR ρ) (mshiftS f i)) = mshiftS (fun i => mren ρ (f i)) := by
      funext i; simp only [mshiftS, mshift, mren_mren]; rfl
    simp only [mren, substFn, mren_substFn ρ f t, mren_substFn (upR ρ) (mshiftS f) s, h]
  | .mvar u σ => by simp only [mren, substFn, mrenL_substFnL ρ f σ]
theorem mrenL_substFnL (ρ : Nat → Nat) (f : Nat → Tm) :
    ∀ σ : List Tm, mrenL ρ (substFnL f σ) = substFnL (fun i => mren ρ (f i)) (mrenL ρ σ)
  | [] => rfl
  | t :: σ => by simp only [mrenL, substFnL, mren_substFn ρ f t, mrenL_substFnL ρ f σ]
end

mutual
/-- Ordinary substitutions compose, for every pair of functions. -/
theorem substFn_substFn (g f : Nat → Tm) :
    ∀ t : Tm, substFn g (substFn f t) = substFn (fun i => substFn g (f i)) t
  | .var _ => rfl
  | .lam A t => by
    have h : (fun i => substFn (upS g) (upS f i)) = upS (fun i => substFn g (f i)) := by
      funext i; cases i with
      | zero => rfl
      | succ j => simp only [upS, substFn_rename, rename_substFn]
    simp only [substFn, substFn_substFn (upS g) (upS f) t, h]
  | .app t s => by simp only [substFn, substFn_substFn g f t, substFn_substFn g f s]
  | .box _ _ => rfl
  | .letbox t s => by
    have h : (fun i => substFn (mshiftS g) (mshiftS f i)) = mshiftS (fun i => substFn g (f i)) := by
      funext i; simp only [mshiftS, mshift, mren_substFn]; rfl
    simp only [substFn, substFn_substFn g f t, substFn_substFn (mshiftS g) (mshiftS f) s, h]
  | .mvar u σ => by simp only [substFn, substFnL_substFnL g f σ]
theorem substFnL_substFnL (g f : Nat → Tm) :
    ∀ σ : List Tm, substFnL g (substFnL f σ) = substFnL (fun i => substFn g (f i)) σ
  | [] => rfl
  | t :: σ => by simp only [substFnL, substFn_substFn g f t, substFnL_substFnL g f σ]
end

mutual
/-- The identity function substitution is the identity. -/
theorem substFn_var : ∀ t : Tm, substFn Tm.var t = t
  | .var _ => rfl
  | .lam A t => by
    have h : upS Tm.var = Tm.var := by funext i; cases i <;> rfl
    simp only [substFn, h, substFn_var t]
  | .app t s => by simp only [substFn, substFn_var t, substFn_var s]
  | .box _ _ => rfl
  | .letbox t s => by
    have h : mshiftS Tm.var = Tm.var := by funext i; rfl
    simp only [substFn, h, substFn_var t, substFn_var s]
  | .mvar u σ => by simp only [substFn, substFnL_var σ]
theorem substFnL_var : ∀ σ : List Tm, substFnL Tm.var σ = σ
  | [] => rfl
  | t :: σ => by simp only [substFnL, substFn_var t, substFnL_var σ]
end

mutual
/-- A substitution acts only through the variables a term uses. -/
theorem substFn_congr :
    ∀ (t : Tm) (f g : Nat → Tm), (∀ k, uses k t = true → f k = g k) → substFn f t = substFn g t
  | .var i, f, g, h => h i (by simp [uses])
  | .lam A t, f, g, h => by
    have h' : ∀ k, uses k t = true → upS f k = upS g k := by
      intro k hk; cases k with
      | zero => rfl
      | succ j => simp only [upS, h j (by simpa [uses] using hk)]
    simp only [substFn, substFn_congr t (upS f) (upS g) h']
  | .app t s, f, g, h => by
    simp only [substFn,
      substFn_congr t f g (fun k hk => h k (by simp [uses, hk])),
      substFn_congr s f g (fun k hk => h k (by simp [uses, hk]))]
  | .box _ _, _, _, _ => rfl
  | .letbox t s, f, g, h => by
    simp only [substFn,
      substFn_congr t f g (fun k hk => h k (by simp [uses, hk])),
      substFn_congr s (mshiftS f) (mshiftS g)
        (fun k hk => by simp only [mshiftS, h k (by simp [uses, hk])])]
  | .mvar u σ, f, g, h => by
    simp only [substFn, substFnL_congr σ f g (fun k hk => h k (by simpa [uses] using hk))]
theorem substFnL_congr :
    ∀ (σ : List Tm) (f g : Nat → Tm), (∀ k, usesL k σ = true → f k = g k) →
      substFnL f σ = substFnL g σ
  | [], _, _, _ => rfl
  | t :: σ, f, g, h => by
    simp only [substFnL,
      substFn_congr t f g (fun k hk => h k (by simp [usesL, hk])),
      substFnL_congr σ f g (fun k hk => h k (by simp [usesL, hk]))]
end

/-! ## List substitutions -/

theorem ofList_nil : ofList [] = Tm.var := by funext i; rfl

theorem subst_nil (t : Tm) : subst [] t = t := by
  simp only [subst, ofList_nil, substFn_var]

theorem ofList_getElem? : ∀ (σ : List Tm) (i : Nat) (s : Tm), σ[i]? = some s → ofList σ i = s
  | [], _, _, h => by simp at h
  | t :: _, 0, s, h => by simpa [ofList] using h
  | _ :: σ, i + 1, s, h => by simpa [ofList] using ofList_getElem? σ i s (by simpa using h)

theorem ofList_comp (τ : List Tm) :
    ∀ (σ : List Tm) (i : Nat), ofList (comp τ σ) i = substFn (ofList τ) (ofList σ i)
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: σ, i + 1 => ofList_comp τ σ i

/-- **Composition.** `comp τ σ` is the composite of the two list substitutions, for every
term (no scoping premise: a list denotes itself followed by the shifted identity). -/
theorem subst_comp (τ σ : List Tm) (t : Tm) : subst τ (subst σ t) = subst (comp τ σ) t := by
  simp only [subst, substFn_substFn]
  congr 1; funext i; exact (ofList_comp τ σ i).symm

/-! ## Typing: renaming, weakening, modal weakening -/

/-- **Renaming**, restricted to the variables the term uses: a renaming that preserves the type
of every USED variable preserves typing. -/
theorem hasTy_rename {Δ : MEnv} {Γ : Ctx} {t : Tm} {A : Ty} (h : HasTy Δ Γ t A) :
    ∀ (Γ' : Ctx) (ρ : Nat → Nat),
      (∀ i B, uses i t = true → Γ[i]? = some B → Γ'[ρ i]? = some B) →
      HasTy Δ Γ' (rename ρ t) A := by
  induction h with
  | @var Δ Γ i A hi =>
    intro Γ' ρ hρ; exact .var (hρ i A (by simp [uses]) hi)
  | @lam Δ Γ A B t _ ih =>
    intro Γ' ρ hρ
    refine .lam (ih (A :: Γ') (upR ρ) ?_)
    intro i C hu hC
    cases i with
    | zero => simpa [upR] using hC
    | succ j =>
      simp only [List.getElem?_cons_succ] at hC
      simpa [upR] using hρ j C (by simpa [uses] using hu) hC
  | @app Δ Γ A B t s _ _ iht ihs =>
    intro Γ' ρ hρ
    exact .app (iht Γ' ρ fun i C hu hC => hρ i C (by simp [uses, hu]) hC)
      (ihs Γ' ρ fun i C hu hC => hρ i C (by simp [uses, hu]) hC)
  | @box Δ Γ Ψ A t ht _ =>
    intro Γ' ρ _; exact .box ht
  | @letbox Δ Γ Ψ A B t s _ _ iht ihs =>
    intro Γ' ρ hρ
    exact .letbox (iht Γ' ρ fun i C hu hC => hρ i C (by simp [uses, hu]) hC)
      (ihs Γ' ρ fun i C hu hC => hρ i C (by simp [uses, hu]) hC)
  | @mvar Δ Γ Ψ A u σ hu hlen _ ih =>
    intro Γ' ρ hρ
    show HasTy Δ Γ' (.mvar u (renameL ρ σ)) A
    refine .mvar hu (by simp [renameL_eq, hlen]) ?_
    intro i s' C hs' hC
    rw [renameL_eq, List.getElem?_map] at hs'
    cases hσ : σ[i]? with
    | none => simp [hσ] at hs'
    | some s =>
      simp only [hσ, Option.map_some, Option.some.injEq] at hs'
      subst hs'
      exact ih i s C hσ hC Γ' ρ fun k D hk hD =>
        hρ k D (by simp only [uses]; exact usesL_of_getElem? k σ i s hσ hk) hD

/-- **Weakening** by one ordinary hypothesis (the new variable is index 0). -/
theorem hasTy_weaken {Δ : MEnv} {Γ : Ctx} {t : Tm} {A : Ty} (h : HasTy Δ Γ t A) (B : Ty) :
    HasTy Δ (B :: Γ) (rename Nat.succ t) A :=
  hasTy_rename h (B :: Γ) Nat.succ fun i C _ hC => by simpa using hC

/-- Weakening at the outer end of the context needs no renaming. -/
theorem hasTy_weaken_append {Δ : MEnv} {Γ : Ctx} {t : Tm} {A : Ty} (h : HasTy Δ Γ t A)
    (Γ'' : Ctx) : HasTy Δ (Γ ++ Γ'') t A := by
  have h' := hasTy_rename h (Γ ++ Γ'') (fun i => i) fun i C _ hC => by
    obtain ⟨hi, _⟩ := List.getElem?_eq_some_iff.1 hC
    rw [List.getElem?_append_left hi]; exact hC
  rwa [rename_id] at h'

/-- **Metavariable renaming** preserves typing when it preserves every declaration. -/
theorem hasTy_mren {Δ : MEnv} {Γ : Ctx} {t : Tm} {A : Ty} (h : HasTy Δ Γ t A) :
    ∀ (Δ' : MEnv) (ρ : Nat → Nat), (∀ v P, Δ v = some P → Δ' (ρ v) = some P) →
      HasTy Δ' Γ (mren ρ t) A := by
  induction h with
  | @var Δ Γ i A hi => intro Δ' ρ _; exact .var hi
  | @lam Δ Γ A B t _ ih => intro Δ' ρ hρ; exact .lam (ih Δ' ρ hρ)
  | @app Δ Γ A B t s _ _ iht ihs => intro Δ' ρ hρ; exact .app (iht Δ' ρ hρ) (ihs Δ' ρ hρ)
  | @box Δ Γ Ψ A t _ ih => intro Δ' ρ hρ; exact .box (ih Δ' ρ hρ)
  | @letbox Δ Γ Ψ A B t s _ _ iht ihs =>
    intro Δ' ρ hρ
    refine .letbox (iht Δ' ρ hρ) (ihs (MEnv.cons (Ψ, A) Δ') (upR ρ) ?_)
    intro v P hP
    cases v with
    | zero => exact hP
    | succ w => exact hρ w P hP
  | @mvar Δ Γ Ψ A u σ hu hlen _ ih =>
    intro Δ' ρ hρ
    show HasTy Δ' Γ (.mvar (ρ u) (mrenL ρ σ)) A
    refine .mvar (hρ u _ hu) (by simp [mrenL_eq, hlen]) ?_
    intro i s' C hs' hC
    rw [mrenL_eq, List.getElem?_map] at hs'
    cases hσ : σ[i]? with
    | none => simp [hσ] at hs'
    | some s =>
      simp only [hσ, Option.map_some, Option.some.injEq] at hs'
      subst hs'
      exact ih i s C hσ hC Δ' ρ hρ

/-- **Modal weakening** by one metavariable declaration (the new one is index 0). -/
theorem hasTy_mweaken {Δ : MEnv} {Γ : Ctx} {t : Tm} {A : Ty} (h : HasTy Δ Γ t A)
    (P : Ctx × Ty) : HasTy (MEnv.cons P Δ) Γ (mshift t) A :=
  hasTy_mren h (MEnv.cons P Δ) Nat.succ fun _ _ hQ => hQ

/-! ## Typing: substitution -/

/-- **Substitution** by a function: a substitution typing every variable of `Γ` in `Γ'`. -/
theorem hasTy_substFn {Δ : MEnv} {Γ : Ctx} {t : Tm} {A : Ty} (h : HasTy Δ Γ t A) :
    ∀ (Γ' : Ctx) (f : Nat → Tm), (∀ i B, Γ[i]? = some B → HasTy Δ Γ' (f i) B) →
      HasTy Δ Γ' (substFn f t) A := by
  induction h with
  | @var Δ Γ i A hi => intro Γ' f hf; exact hf i A hi
  | @lam Δ Γ A B t _ ih =>
    intro Γ' f hf
    refine .lam (ih (A :: Γ') (upS f) ?_)
    intro i C hC
    cases i with
    | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at hC; subst hC; exact .var rfl
    | succ j =>
      simp only [List.getElem?_cons_succ] at hC
      exact hasTy_weaken (hf j C hC) A
  | @app Δ Γ A B t s _ _ iht ihs => intro Γ' f hf; exact .app (iht Γ' f hf) (ihs Γ' f hf)
  | @box Δ Γ Ψ A t ht _ => intro Γ' f _; exact .box ht
  | @letbox Δ Γ Ψ A B t s _ _ iht ihs =>
    intro Γ' f hf
    exact .letbox (iht Γ' f hf)
      (ihs Γ' (mshiftS f) fun i C hC => hasTy_mweaken (hf i C hC) (Ψ, A))
  | @mvar Δ Γ Ψ A u σ hu hlen _ ih =>
    intro Γ' f hf
    show HasTy Δ Γ' (.mvar u (substFnL f σ)) A
    refine .mvar hu (by simp [substFnL_eq, hlen]) ?_
    intro i s' C hs' hC
    rw [substFnL_eq, List.getElem?_map] at hs'
    cases hσ : σ[i]? with
    | none => simp [hσ] at hs'
    | some s =>
      simp only [hσ, Option.map_some, Option.some.injEq] at hs'
      subst hs'
      exact ih i s C hσ hC Γ' f hf

/-- **The substitution lemma**: `Δ; Γ' ⊢ σ : Γ` and `Δ; Γ ⊢ t : A` give `Δ; Γ' ⊢ [σ]t : A`. -/
theorem subst_lemma {Δ : MEnv} {Γ Γ' : Ctx} {σ : List Tm} {t : Tm} {A : Ty}
    (hσ : HasSubst Δ Γ' σ Γ) (ht : HasTy Δ Γ t A) : HasTy Δ Γ' (subst σ t) A := by
  refine hasTy_substFn ht Γ' (ofList σ) fun i B hB => ?_
  obtain ⟨hi, _⟩ := List.getElem?_eq_some_iff.1 hB
  have hi' : i < σ.length := by rw [hσ.1]; exact hi
  have hs : σ[i]? = some σ[i] := List.getElem?_eq_getElem hi'
  rw [ofList_getElem? σ i σ[i] hs]
  exact hσ.2 i σ[i] B hs hB

theorem shiftSub_length : ∀ (k n : Nat), (shiftSub k n).length = n
  | _, 0 => rfl
  | k, n + 1 => by simp [shiftSub, shiftSub_length (k + 1) n]

theorem shiftSub_getElem? :
    ∀ (k n i : Nat) (s : Tm), (shiftSub k n)[i]? = some s → i < n ∧ s = .var (k + i)
  | _, 0, _, _, h => by simp [shiftSub] at h
  | k, n + 1, 0, s, h => by simp [shiftSub] at h; exact ⟨by omega, by simp [h]⟩
  | k, n + 1, i + 1, s, h => by
    simp only [shiftSub, List.getElem?_cons_succ] at h
    obtain ⟨hi, hs⟩ := shiftSub_getElem? (k + 1) n i s h
    exact ⟨by omega, by rw [hs]; congr 1; omega⟩

theorem ofList_shiftSub :
    ∀ (k n j : Nat), j < n → ofList (shiftSub k n) j = .var (k + j)
  | _, 0, _, h => absurd h (Nat.not_lt_zero _)
  | k, n + 1, 0, _ => rfl
  | k, n + 1, j + 1, h => by
    show ofList (shiftSub (k + 1) n) j = _
    rw [ofList_shiftSub (k + 1) n j (by omega)]; congr 1; omega

/-- The shifted identity `[var |Γ₀|, …]` is a substitution from `Γ₀ ++ Γ` for `Γ`. -/
theorem hasSubst_shiftSub (Δ : MEnv) (Γ₀ Γ : Ctx) :
    HasSubst Δ (Γ₀ ++ Γ) (shiftSub Γ₀.length Γ.length) Γ := by
  refine ⟨shiftSub_length _ _, fun i s C hs hC => ?_⟩
  obtain ⟨_, rfl⟩ := shiftSub_getElem? _ _ i s hs
  refine .var ?_
  rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]; exact hC

/-- **The identity substitution** is well typed: `Δ; Γ ⊢ id : Γ`. -/
theorem hasSubst_id (Δ : MEnv) (Γ : Ctx) : HasSubst Δ Γ (idSub Γ.length) Γ :=
  hasSubst_shiftSub Δ [] Γ

/-- The projection `π` is well typed: `Δ; Γ', A ⊢ π : Γ'`. -/
theorem hasSubst_proj (Δ : MEnv) (A : Ty) (Γ' : Ctx) :
    HasSubst Δ (A :: Γ') (proj Γ'.length) Γ' :=
  hasSubst_shiftSub Δ [A] Γ'

/-! ## Typing: metavariable substitution -/

theorem MEnv.cons_insert (Q P : Ctx × Ty) (k : Nat) (Δ : MEnv) :
    MEnv.cons Q (MEnv.insert k P Δ) = MEnv.insert (k + 1) P (MEnv.cons Q Δ) := by
  funext v
  cases v with
  | zero => simp [MEnv.cons, MEnv.insert]
  | succ w =>
    simp only [MEnv.cons, MEnv.insert]
    by_cases h1 : w < k
    · simp [h1]
    · by_cases h2 : w = k
      · simp [h2]
      · obtain ⟨w', rfl⟩ : ∃ w', w = w' + 1 := ⟨w - 1, by omega⟩
        simp [h1, h2]

theorem MEnv.cons_eq_insert (P : Ctx × Ty) (Δ : MEnv) : MEnv.cons P Δ = MEnv.insert 0 P Δ := by
  funext v; cases v <;> simp [MEnv.cons, MEnv.insert]

/-- Metavariable substitution at any depth: the declaration `(Ψ, A)` sits at index `k` of the
environment, and `s : A` under `Ψ` in the environment with it removed. -/
theorem hasTy_msubst_gen {Δ : MEnv} {Γ : Ctx} {t : Tm} {B : Ty} (h : HasTy Δ Γ t B) :
    ∀ (k : Nat) (Δ₀ : MEnv) (Ψ : Ctx) (A : Ty) (s : Tm), Δ = MEnv.insert k (Ψ, A) Δ₀ →
      HasTy Δ₀ Ψ s A → HasTy Δ₀ Γ (msubst s k t) B := by
  induction h with
  | @var Δ Γ i A hi => intro _ _ _ _ _ _ _; exact .var hi
  | @lam Δ Γ A B t _ ih => intro k Δ₀ Ψ A' s hΔ hs; exact .lam (ih k Δ₀ Ψ A' s hΔ hs)
  | @app Δ Γ A B t₁ t₂ _ _ ih₁ ih₂ =>
    intro k Δ₀ Ψ A' s hΔ hs; exact .app (ih₁ k Δ₀ Ψ A' s hΔ hs) (ih₂ k Δ₀ Ψ A' s hΔ hs)
  | @box Δ Γ Φ A t _ ih => intro k Δ₀ Ψ A' s hΔ hs; exact .box (ih k Δ₀ Ψ A' s hΔ hs)
  | @letbox Δ Γ Φ C B t₁ t₂ _ _ ih₁ ih₂ =>
    intro k Δ₀ Ψ A s hΔ hs
    refine .letbox (ih₁ k Δ₀ Ψ A s hΔ hs) ?_
    exact ih₂ (k + 1) (MEnv.cons (Φ, C) Δ₀) Ψ A (mshift s)
      (by rw [hΔ, MEnv.cons_insert]) (hasTy_mweaken hs (Φ, C))
  | @mvar Δ Γ Φ C v σ hv hlen _ ih =>
    intro k Δ₀ Ψ A s hΔ hs
    subst hΔ
    have hσ : HasSubst Δ₀ Γ (msubstL s k σ) Φ := by
      refine ⟨by simp [msubstL_eq, hlen], fun i s' D hs' hD => ?_⟩
      rw [msubstL_eq, List.getElem?_map] at hs'
      cases hσi : σ[i]? with
      | none => simp [hσi] at hs'
      | some r =>
        simp only [hσi, Option.map_some, Option.some.injEq] at hs'
        subst hs'
        exact ih i r D hσi hD k Δ₀ Ψ A s rfl hs
    by_cases h1 : v = k
    · subst h1
      simp only [MEnv.insert, Nat.lt_irrefl, if_false, if_true, Option.some.injEq,
        Prod.mk.injEq] at hv
      obtain ⟨rfl, rfl⟩ := hv
      simp only [msubst]
      exact subst_lemma hσ hs
    · by_cases h2 : v < k
      · simp only [msubst, if_neg h1, if_pos h2]
        refine .mvar ?_ hσ.1 hσ.2
        simpa [MEnv.insert, h2] using hv
      · simp only [msubst, if_neg h1, if_neg h2]
        refine .mvar ?_ hσ.1 hσ.2
        simpa [MEnv.insert, h1, h2] using hv

/-- **The metavariable substitution lemma**: `Δ; Ψ ⊢ s : A` and `Δ, u::(Ψ ⊢ A); Γ ⊢ t : B`
give `Δ; Γ ⊢ ⟦Ψ.s/u⟧t : B`. -/
theorem msubst_lemma {Δ : MEnv} {Γ Ψ : Ctx} {s t : Tm} {A B : Ty}
    (hs : HasTy Δ Ψ s A) (ht : HasTy (MEnv.cons (Ψ, A) Δ) Γ t B) : HasTy Δ Γ (msubst s 0 t) B :=
  hasTy_msubst_gen ht 0 Δ Ψ A s (MEnv.cons_eq_insert _ _) hs

/-! ## Scoping and strengthening -/

/-- A typed term uses only variables of its context. -/
theorem hasTy_uses_lt {Δ : MEnv} {Γ : Ctx} {t : Tm} {A : Ty} (h : HasTy Δ Γ t A) :
    ∀ k, uses k t = true → k < Γ.length := by
  induction h with
  | @var Δ Γ i A hi =>
    intro k hk
    simp only [uses, beq_iff_eq] at hk; subst hk
    exact (List.getElem?_eq_some_iff.1 hi).1
  | @lam Δ Γ A B t _ ih =>
    intro k hk; have := ih (k + 1) (by simpa [uses] using hk); simp at this; omega
  | @app Δ Γ A B t s _ _ iht ihs =>
    intro k hk; simp only [uses, Bool.or_eq_true] at hk
    rcases hk with hk | hk
    · exact iht k hk
    · exact ihs k hk
  | @box Δ Γ Ψ A t _ _ => intro k hk; simp [uses] at hk
  | @letbox Δ Γ Ψ A B t s _ _ iht ihs =>
    intro k hk; simp only [uses, Bool.or_eq_true] at hk
    rcases hk with hk | hk
    · exact iht k hk
    · exact ihs k hk
  | @mvar Δ Γ Ψ A u σ hu hlen _ ih =>
    intro k hk
    simp only [uses] at hk
    obtain ⟨i, s, hi, hs⟩ := usesL_true k σ hk
    have hiσ : i < σ.length := (List.getElem?_eq_some_iff.1 hi).1
    have hiΨ : i < Ψ.length := hlen ▸ hiσ
    exact ih i s Ψ[i] hi (List.getElem?_eq_getElem hiΨ) k hs

/-- **Strengthening, as a factorisation through the projection.** A term typed under `Γ', A`
that never uses the variable of `A` is the projection `π : Γ', A ⊢ π : Γ'` applied to a term
typed under `Γ'`: a conditional derivation survives the loss of a hypothesis it did not use. -/
theorem strengthen {Δ : MEnv} {Γ' : Ctx} {A B : Ty} {t : Tm}
    (h : HasTy Δ (A :: Γ') t B) (hu : uses 0 t = false) :
    ∃ t₀, HasTy Δ Γ' t₀ B ∧ t = subst (proj Γ'.length) t₀ := by
  refine ⟨rename (fun i => i - 1) t, ?_, ?_⟩
  · refine hasTy_rename h Γ' (fun i => i - 1) fun i C hi hC => ?_
    cases i with
    | zero => rw [hu] at hi; exact absurd hi (by decide)
    | succ j => simpa using hC
  · have hlt := hasTy_uses_lt h
    rw [subst, substFn_rename]
    conv => lhs; rw [← substFn_var t]
    refine substFn_congr t _ _ fun k hk => ?_
    have hk0 : k ≠ 0 := by intro e; subst e; rw [hu] at hk; exact absurd hk (by decide)
    have hkl := hlt k hk
    simp only [List.length_cons] at hkl
    simp only [proj]
    rw [ofList_shiftSub 1 Γ'.length (k - 1) (by omega)]
    congr 1; omega

/-! ## Building substitutions -/

theorem hasSubst_nil (Δ : MEnv) (Γ : Ctx) : HasSubst Δ Γ [] [] :=
  ⟨rfl, fun _ _ _ h _ => by simp at h⟩

theorem hasSubst_cons {Δ : MEnv} {Γ Ψ : Ctx} {s : Tm} {σ : List Tm} {A : Ty}
    (hs : HasTy Δ Γ s A) (hσ : HasSubst Δ Γ σ Ψ) : HasSubst Δ Γ (s :: σ) (A :: Ψ) := by
  refine ⟨by simp [hσ.1], fun i s' C hs' hC => ?_⟩
  cases i with
  | zero =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hs' hC
    subst hs'; subst hC; exact hs
  | succ j =>
    simp only [List.getElem?_cons_succ] at hs' hC
    exact hσ.2 j s' C hs' hC

/-! ## Teeth: the box closes its body over `Ψ` alone -/

/-- **A box cannot capture the ambient context.** A box whose body is a variable pointing past
`Ψ` has no type, whatever the ambient `Γ` holds at that index. -/
theorem box_cannot_capture {Δ : MEnv} {Γ Ψ : Ctx} {k : Nat} (hk : Ψ.length ≤ k) (T : Ty) :
    ¬ HasTy Δ Γ (.box Ψ (.var k)) T := by
  intro h
  cases h with
  | box hb =>
    cases hb with
    | var hv => exact absurd (List.getElem?_eq_some_iff.1 hv).1 (by omega)

/-- **The ambient context is irrelevant to a box**: a box typed under one ambient context is typed
under every other. The general fact behind `box_cannot_capture`. -/
theorem box_ambient_free {Δ : MEnv} {Γ Γ' Ψ : Ctx} {t : Tm} {T : Ty}
    (h : HasTy Δ Γ (.box Ψ t) T) : HasTy Δ Γ' (.box Ψ t) T := by
  cases h with
  | box ht => exact .box ht

/-- The concrete refutation: `x : base ⊢ box [] x` is ill typed at every type, though `x` itself
is typed at `base` in the same context, and the same body is typed once `Ψ` declares it. -/
theorem box_cannot_capture_toy :
    (∀ T, ¬ HasTy MEnv.nil [.base] (.box [] (.var 0)) T) ∧
      HasTy MEnv.nil [.base] (.var 0) .base ∧
      HasTy MEnv.nil [.base] (.box [.base] (.var 0)) (.box [.base] .base) :=
  ⟨fun T => box_cannot_capture (Nat.le_refl 0) T, .var rfl, .box (.var rfl)⟩

/-! ## Teeth: inspection is blocked at a metavariable (Layered MTT §5.2) -/

/-- An ordinary substitution never unblocks a metavariable occurrence: whatever `f` substitutes
for the ordinary variables, `u[σ]` stays a metavariable occurrence. DEFINITIONAL (`rfl`): it
records that `substFn` maps `mvar` to `mvar`, nothing deeper. -/
theorem mvar_blocked (f : Nat → Tm) (u : Nat) (σ : List Tm) :
    headKnown (.mvar u σ) = false ∧ headKnown (substFn f (.mvar u σ)) = false :=
  ⟨rfl, rfl⟩

/-- The same for list substitutions, and for every term whose head is blocked. DEFINITIONAL
(case split, each case `rfl`). -/
theorem subst_keeps_blocked (σ : List Tm) (t : Tm) (h : headKnown t = false) :
    headKnown (subst σ t) = false := by
  cases t <;> first | rfl | simp [headKnown] at h

/-- A metavariable substitution for `u` replaces `u[σ]` by `[σ']s`. -/
theorem msubst_mvar_self (s : Tm) (u : Nat) (σ : List Tm) :
    msubst s u (.mvar u σ) = subst (msubstL s u σ) s := by
  simp [msubst]

/-- **A metavariable substitution for `u` unblocks `u[σ]`** when the filling's head is known and
is not a variable (a variable could be mapped by `σ'` to a metavariable occurrence, and a
metavariable occurrence stays blocked). -/
theorem msubst_unblocks (s : Tm) (u : Nat) (σ : List Tm) (hs : headKnown s = true)
    (hv : ∀ i, s ≠ .var i) : headKnown (msubst s u (.mvar u σ)) = true := by
  rw [msubst_mvar_self]
  cases s with
  | var i => exact absurd rfl (hv i)
  | mvar => simp [headKnown] at hs
  | _ => rfl

/-- A metavariable substitution for a different `u` leaves `v[σ]` blocked. -/
theorem msubst_other_blocked (s : Tm) {u v : Nat} (h : v ≠ u) (σ : List Tm) :
    headKnown (msubst s u (.mvar v σ)) = false := by
  by_cases h2 : v < u <;> simp [msubst, h, h2, headKnown]

/-- The toy: `u[]` is blocked under every ordinary substitution and unblocked by `⟦λx.x/u⟧`. -/
theorem mvar_blocked_toy :
    headKnown (subst [.lam .base (.var 0)] (.mvar 0 [])) = false ∧
      headKnown (msubst (.lam .base (.var 0)) 0 (.mvar 0 [])) = true :=
  ⟨rfl, rfl⟩

/-! ## Teeth: strengthening needs the hypothesis unused -/

/-- Without `uses 0 t = false` the factorisation fails: `x₀` under `x₀ : base, x₁ : base` is not
`π` applied to any term typed under `x₁ : base`. -/
theorem strengthen_needs_unused :
    ¬ ∃ t₀, HasTy MEnv.nil [.base] t₀ .base ∧ Tm.var 0 = subst (proj 1) t₀ := by
  rintro ⟨t₀, ht, he⟩
  cases t₀ with
  | var j =>
    cases j with
    | zero => simp [subst, substFn, proj, shiftSub, ofList] at he
    | succ j =>
      cases j with
      | zero => cases ht with | var hv => simp at hv
      | succ j => simp [subst, substFn, proj, shiftSub, ofList] at he
  | lam => simp [subst, substFn] at he
  | app => simp [subst, substFn] at he
  | box => simp [subst, substFn] at he
  | letbox => simp [subst, substFn] at he
  | mvar => simp [subst, substFn] at he

/-! ## Toy instances of the main theorems -/

/-- `subst_lemma`: `[λy.y, z] (x₀ x₁) = (λy.y) z`, typed under `z : base`. -/
theorem subst_lemma_toy :
    subst [.lam .base (.var 0), .var 0] (.app (.var 0) (.var 1)) =
        .app (.lam .base (.var 0)) (.var 0) ∧
      HasTy MEnv.nil [.base] (subst [.lam .base (.var 0), .var 0] (.app (.var 0) (.var 1))) .base :=
  ⟨rfl, subst_lemma (Γ := [.arr .base .base, .base])
    (hasSubst_cons (.lam (.var rfl)) (hasSubst_cons (.var rfl) (hasSubst_nil _ _)))
    (.app (.var rfl) (.var rfl))⟩

/-- `subst_comp` on a term with a binder, a box and a metavariable occurrence. -/
theorem subst_comp_toy :
    let τ : List Tm := [.var 7, .lam .base (.var 1)]
    let σ : List Tm := [.app (.var 1) (.var 0), .var 3]
    let t : Tm := .lam .base (.app (.app (.var 1) (.var 2))
      (.app (.box [.base] (.var 0)) (.mvar 0 [.var 0, .var 4])))
    subst τ (subst σ t) = subst (comp τ σ) t ∧
      subst (comp τ σ) t = .lam .base (.app (.app (.app (.lam .base (.var 2)) (.var 8)) (.var 2))
        (.app (.box [.base] (.var 0)) (.mvar 0 [.var 0, .lam .base (.var 2)]))) :=
  ⟨subst_comp _ _ _, rfl⟩

/-- `msubst_lemma`: `⟦x.x/u⟧ (λy. u[y]) = λy.y`, from `u :: (x:base ⊢ base) ⊢ λy. u[y] : base → base`. -/
theorem msubst_lemma_toy :
    msubst (.var 0) 0 (.lam .base (.mvar 0 [.var 0])) = .lam .base (.var 0) ∧
      HasTy MEnv.nil [] (msubst (.var 0) 0 (.lam .base (.mvar 0 [.var 0]))) (.arr .base .base) :=
  ⟨rfl, msubst_lemma (Ψ := [.base]) (A := .base) (.var rfl)
    (.lam (HasTy.mvar' rfl (hasSubst_cons (.var rfl) (hasSubst_nil _ _))))⟩

/-- The whole round trip: `let box u = box (x.x) in λy. u[y]` is typed, and its body
instantiated at the boxed term is the `msubst_lemma_toy` result. -/
theorem letbox_toy :
    HasTy MEnv.nil [] (.letbox (.box [.base] (.var 0)) (.lam .base (.mvar 0 [.var 0])))
      (.arr .base .base) :=
  .letbox (.box (.var rfl)) (.lam (HasTy.mvar' rfl (hasSubst_cons (.var rfl) (hasSubst_nil _ _))))

/-- `strengthen`: `x₁` under `x₀ : base, x₁ : base → base` is `π x₀'` for `x₀' : base → base`. -/
theorem strengthen_toy :
    ∃ t₀, HasTy MEnv.nil [.arr .base .base] t₀ (.arr .base .base) ∧
      Tm.var 1 = subst (proj [Ty.arr .base .base].length) t₀ :=
  strengthen (A := .base) (.var rfl) rfl

/-- Weakening and modal weakening on a term with a box and a metavariable occurrence. -/
theorem weaken_toy :
    rename Nat.succ (.lam .base (.app (.var 1) (.box [] (.mvar 0 [])))) =
        .lam .base (.app (.var 2) (.box [] (.mvar 0 []))) ∧
      mshift (.lam .base (.app (.var 1) (.box [] (.mvar 0 [])))) =
        .lam .base (.app (.var 1) (.box [] (.mvar 1 []))) :=
  ⟨rfl, rfl⟩

/-! ## Reduction: subject reduction, determinism, blocked redexes -/

/-- β's substitution `[s/0]` is typed: `s : A` under `Γ` and `t : B` under `A :: Γ`. -/
theorem hasTy_beta {Δ : MEnv} {Γ : Ctx} {A B : Ty} {t s : Tm}
    (ht : HasTy Δ (A :: Γ) t B) (hs : HasTy Δ Γ s A) : HasTy Δ Γ (subst [s] t) B := by
  refine hasTy_substFn ht Γ (ofList [s]) fun i C hC => ?_
  cases i with
  | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at hC; subst hC; exact hs
  | succ j => simp only [List.getElem?_cons_succ] at hC; exact .var hC

/-- **Subject reduction.** Its two redex cases are `subst_lemma`'s (through `hasTy_beta`) and
`msubst_lemma`'s. -/
theorem subject_reduction {Δ : MEnv} {Γ : Ctx} {t t' : Tm} {A : Ty}
    (h : HasTy Δ Γ t A) (hs : Step t t') : HasTy Δ Γ t' A := by
  induction hs generalizing A with
  | beta =>
    cases h with
    | app hf ha => cases hf with | lam hb => exact hasTy_beta hb ha
  | letboxBox =>
    cases h with
    | letbox hb hs => cases hb with | box ht => exact msubst_lemma ht hs
  | appL _ ih =>
    cases h with
    | app hf ha => exact .app (ih hf) ha
  | letboxL _ ih =>
    cases h with
    | letbox hb hs => exact .letbox (ih hb) hs

/-- Values do not step: `lam`, `box`, variables and metavariable occurrences. -/
theorem lam_no_step {A : Ty} {t t' : Tm} : ¬ Step (.lam A t) t' := by
  intro h; cases h

/-- **Nothing steps under `box`.** The body is closed over its own `Ψ`, and the box is a value,
whatever its body could do on its own (see `no_step_under_box_toy`). -/
theorem no_step_under_box {Ψ : Ctx} {t t' : Tm} : ¬ Step (.box Ψ t) t' := by
  intro h; cases h

theorem no_step_under_box_toy :
    Step (.app (.lam .base (.var 0)) (.var 0)) (.var 0) ∧
      ¬ ∃ t', Step (.box [.base] (.app (.lam .base (.var 0)) (.var 0))) t' :=
  ⟨.beta, fun ⟨_, h⟩ => no_step_under_box h⟩

theorem var_no_step {i : Nat} {t' : Tm} : ¬ Step (.var i) t' := by
  intro h; cases h

theorem mvar_no_step {u : Nat} {σ : List Tm} {t' : Tm} : ¬ Step (.mvar u σ) t' := by
  intro h; cases h

/-- **Determinism.** -/
theorem step_deterministic {t t₁ t₂ : Tm} (h₁ : Step t t₁) (h₂ : Step t t₂) : t₁ = t₂ := by
  induction h₁ generalizing t₂ with
  | beta =>
    cases h₂ with
    | beta => rfl
    | appL h => exact absurd h lam_no_step
  | letboxBox =>
    cases h₂ with
    | letboxBox => rfl
    | letboxL h => exact absurd h no_step_under_box
  | appL h ih =>
    cases h₂ with
    | beta => exact absurd h lam_no_step
    | appL h' => rw [ih h']
  | letboxL h ih =>
    cases h₂ with
    | letboxBox => exact absurd h no_step_under_box
    | letboxL h' => rw [ih h']

/-- **A `letbox` needs a box.** With an unknown contextual object `v[σ]` as its scrutinee, a
`letbox` is stuck: the Layered-MTT blocking, now operational. -/
theorem letbox_needs_box {v : Nat} {σ : List Tm} {s t' : Tm} :
    ¬ Step (.letbox (.mvar v σ) s) t' := by
  intro h
  cases h with
  | letboxL h => exact mvar_no_step h

/-- The stuck `letbox` under an outer `letbox` binding `v`: once the outer redex fires,
`⟦x.x/v⟧` replaces the blocked scrutinee by a box, and the inner `letbox` steps. -/
theorem letbox_needs_box_toy :
    ¬ (∃ t', Step (.letbox (.mvar 0 []) (.mvar 0 [])) t') ∧
      Step (.letbox (.box [] (.box [] (.lam .base (.var 0))))
              (.letbox (.mvar 0 []) (.mvar 0 [])))
        (.letbox (.box [] (.lam .base (.var 0))) (.mvar 0 [])) ∧
      Step (.letbox (.box [] (.lam .base (.var 0))) (.mvar 0 [])) (.lam .base (.var 0)) :=
  ⟨fun ⟨_, h⟩ => letbox_needs_box h, .letboxBox, .letboxBox⟩

/-- The terms of `letbox_needs_box_toy` are typed: the stuck `letbox` under the declaration
`u₀ :: (· ⊢ [· ⊢ base → base])`, the outer redex and its reduct closed. -/
theorem letbox_needs_box_toy_typed :
    HasTy (MEnv.cons ([], .box [] (.arr .base .base)) MEnv.nil) []
        (.letbox (.mvar 0 []) (.mvar 0 [])) (.arr .base .base) ∧
      HasTy MEnv.nil [] (.letbox (.box [] (.box [] (.lam .base (.var 0))))
          (.letbox (.mvar 0 []) (.mvar 0 []))) (.arr .base .base) ∧
      HasTy MEnv.nil [] (.letbox (.box [] (.lam .base (.var 0))) (.mvar 0 [])) (.arr .base .base) := by
  have hin : HasTy (MEnv.cons ([], .box [] (.arr .base .base)) MEnv.nil) []
      (.letbox (.mvar 0 []) (.mvar 0 [])) (.arr .base .base) :=
    .letbox (HasTy.mvar' rfl (hasSubst_nil _ _)) (HasTy.mvar' rfl (hasSubst_nil _ _))
  exact ⟨hin, .letbox (.box (.box (.lam (.var rfl)))) hin,
    .letbox (.box (.lam (.var rfl))) (HasTy.mvar' rfl (hasSubst_nil _ _))⟩

/-! ## Toy: a Bell-shaped resumption -/

/-- The continuation: a contextual object `k = box [r : base] ((λy. y) r)` closed over the
response `r` alone. -/
private def bellK : Tm := .box [.base] (.app (.lam .base (.var 0)) (.var 0))

/-- Resuming it at the response `x` (variable 0 of the ambient `[x : base]`):
`let box u = k in u[x]`. -/
private def bellResume : Tm := .letbox bellK (.mvar 0 [.var 0])

/-- The contextual β of the resumption, computed: `⟦r.(λy.y) r / u⟧ u[x] = (λy.y) x`. -/
theorem bell_resume_computes :
    msubst (.app (.lam .base (.var 0)) (.var 0)) 0 (.mvar 0 [.var 0]) =
      .app (.lam .base (.var 0)) (.var 0) := rfl

/-- **The resumption runs.** `let box u = k in u[x] ↦ (λy. y) x ↦ x`, every term along the way
typed at `base` under `x : base`, and the continuation itself typed at `[base ⊢ base]` under ANY
ambient context (it captures nothing). -/
theorem bell_resume_toy :
    (∀ Γ : Ctx, HasTy MEnv.nil Γ bellK (.box [.base] .base)) ∧
      HasTy MEnv.nil [.base] bellResume .base ∧
      Step bellResume (.app (.lam .base (.var 0)) (.var 0)) ∧
      Step (.app (.lam .base (.var 0)) (.var 0)) (.var 0) ∧
      HasTy MEnv.nil [.base] (.app (.lam .base (.var 0)) (.var 0)) .base ∧
      HasTy MEnv.nil [.base] (.var 0) .base := by
  have hk : ∀ Γ : Ctx, HasTy MEnv.nil Γ bellK (.box [.base] .base) :=
    fun _ => .box (.app (.lam (.var rfl)) (.var rfl))
  have hr : HasTy MEnv.nil [.base] bellResume .base :=
    .letbox (hk _) (HasTy.mvar' rfl (hasSubst_cons (.var rfl) (hasSubst_nil _ _)))
  have s1 : Step bellResume (.app (.lam .base (.var 0)) (.var 0)) := Step.letboxBox
  have s2 : Step (.app (.lam .base (.var 0)) (.var 0)) (.var 0) := Step.beta
  exact ⟨hk, hr, s1, s2, subject_reduction hr s1, subject_reduction (subject_reduction hr s1) s2⟩

/-! ## Decidable equality -/

theorem Ty.decide_eq (a b : Ty) : decide (a = b) = Ty.beq a b := by
  simp only [decide, Ty.decEq, decidable_of_iff, decidable_of_decidable_of_iff]
  split <;> simp_all

/-- `Ty.beq` decides equality (the public face of `Ty.decEq`'s private correctness). -/
theorem Ty.beq_iff (a b : Ty) : Ty.beq a b = true ↔ a = b := by
  rw [← Ty.decide_eq]; exact decide_eq_true_iff

theorem Tm.decide_eq (a b : Tm) : decide (a = b) = Tm.beq a b := by
  simp only [decide, Tm.decEq, decidable_of_iff, decidable_of_decidable_of_iff]
  split <;> simp_all

/-- `Tm.beq` decides equality. -/
theorem Tm.beq_iff (a b : Tm) : Tm.beq a b = true ↔ a = b := by
  rw [← Tm.decide_eq]; exact decide_eq_true_iff

/-- The instance decides: two different terms, one `decide`. -/
theorem tm_decEq_toy :
    (Tm.letbox (.box [.base] (.var 0)) (.mvar 0 [.var 0]) ≠
      .letbox (.box [.base] (.var 0)) (.mvar 0 [.var 1])) ∧
    Tm.mvar 3 [.lam .base (.var 0)] = Tm.mvar 3 [.lam .base (.var 0)] := by decide

/-! ## The checker is exact -/

mutual
theorem infer_sound :
    ∀ (t : Tm) (Δ : MEnv) (Γ : Ctx) (A : Ty), infer Δ Γ t = some A → HasTy Δ Γ t A
  | .var _, _, _, _, h => .var h
  | .lam B t, Δ, Γ, A, h => by
    simp only [infer, Option.map_eq_some_iff] at h
    obtain ⟨C, hC, rfl⟩ := h
    exact .lam (infer_sound t _ _ _ hC)
  | .app t s, Δ, Γ, A, h => by
    cases ht : infer Δ Γ t with
    | none => simp [infer, ht] at h
    | some T =>
      cases hs : infer Δ Γ s with
      | none => cases T <;> simp [infer, ht, hs] at h
      | some A' =>
        cases T with
        | arr A₁ B₁ =>
          by_cases hb : A₁ = A'
          · subst hb
            simp only [infer, ht, hs, if_true, Option.some.injEq] at h
            subst h
            exact .app (infer_sound t _ _ _ ht) (infer_sound s _ _ _ hs)
          · simp [infer, ht, hs, hb] at h
        | _ => simp [infer, ht, hs] at h
  | .box Ψ t, Δ, Γ, A, h => by
    simp only [infer, Option.map_eq_some_iff] at h
    obtain ⟨C, hC, rfl⟩ := h
    exact .box (infer_sound t _ _ _ hC)
  | .letbox t s, Δ, Γ, A, h => by
    cases ht : infer Δ Γ t with
    | none => simp [infer, ht] at h
    | some T =>
      cases T with
      | box Ψ B =>
        simp only [infer, ht] at h
        exact .letbox (infer_sound t _ _ _ ht) (infer_sound s _ _ _ h)
      | _ => simp [infer, ht] at h
  | .mvar u σ, Δ, Γ, A, h => by
    cases hu : Δ u with
    | none => simp [infer, hu] at h
    | some P =>
      obtain ⟨Ψ, B⟩ := P
      cases hl : inferL Δ Γ σ with
      | none => simp [infer, hu, hl] at h
      | some Ψ' =>
        by_cases hb : Ψ' = Ψ
        · subst hb
          simp only [infer, hu, hl, if_true, Option.some.injEq] at h
          subst h
          have hσ := inferL_sound σ Δ Γ Ψ' hl
          exact .mvar hu hσ.1 hσ.2
        · simp [infer, hu, hl, hb] at h
theorem inferL_sound :
    ∀ (σ : List Tm) (Δ : MEnv) (Γ : Ctx) (Ψ : List Ty), inferL Δ Γ σ = some Ψ → HasSubst Δ Γ σ Ψ
  | [], Δ, Γ, Ψ, h => by
    simp only [inferL, Option.some.injEq] at h; subst h; exact hasSubst_nil Δ Γ
  | t :: σ, Δ, Γ, Ψ, h => by
    cases ht : infer Δ Γ t with
    | none => simp [inferL, ht] at h
    | some A =>
      cases hl : inferL Δ Γ σ with
      | none => simp [inferL, ht, hl] at h
      | some As =>
        simp only [inferL, ht, hl, Option.some.injEq] at h
        subst h
        exact hasSubst_cons (infer_sound t _ _ _ ht) (inferL_sound σ _ _ _ hl)
end

theorem inferL_complete {Δ : MEnv} {Γ : Ctx} :
    ∀ (σ : List Tm) (Ψ : List Ty), σ.length = Ψ.length →
      (∀ (i : Nat) (s : Tm) (C : Ty), σ[i]? = some s → Ψ[i]? = some C → infer Δ Γ s = some C) →
      inferL Δ Γ σ = some Ψ
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | t :: σ, C :: Ψ, h, hp => by
    have h0 := hp 0 t C rfl rfl
    have hl := inferL_complete σ Ψ (by simpa using h) fun i s D hs hD => hp (i + 1) s D hs hD
    simp [inferL, h0, hl]

/-- **Completeness of the checker.** -/
theorem infer_complete {Δ : MEnv} {Γ : Ctx} {t : Tm} {A : Ty} (h : HasTy Δ Γ t A) :
    infer Δ Γ t = some A := by
  induction h with
  | var hi => exact hi
  | lam _ ih => simp [infer, ih]
  | app _ _ ih₁ ih₂ => simp [infer, ih₁, ih₂]
  | box _ ih => simp [infer, ih]
  | letbox _ _ ih₁ ih₂ => simp [infer, ih₁, ih₂]
  | @mvar Δ Γ Ψ A u σ hu hlen _ ih =>
    have hl := inferL_complete (Δ := Δ) (Γ := Γ) σ Ψ hlen ih
    simp [infer, hu, hl]

/-- The checker is sound ... -/
theorem check_sound {Γ : Ctx} {t : Tm} {A : Ty} (h : check Γ t A = true) :
    HasTy MEnv.nil Γ t A := by
  unfold check at h
  cases hi : infer MEnv.nil Γ t with
  | none => simp [hi] at h
  | some B =>
    simp only [hi, decide_eq_true_eq] at h
    subst h
    exact infer_sound t _ _ _ hi

/-- ... and complete: `check` is exactly typing in the empty modal environment. -/
theorem check_complete {Γ : Ctx} {t : Tm} {A : Ty} (h : HasTy MEnv.nil Γ t A) :
    check Γ t A = true := by
  simp [check, infer_complete h]

/-- The checker's two verdicts on the box tooth: the capturing box is refused, its closed twin is
accepted. -/
theorem check_toy :
    check [.base] (.box [] (.var 0)) (.box [] .base) = false ∧
      check [.base] (.box [.base] (.var 0)) (.box [.base] .base) = true := by decide

/-! ## Strengthening at any position -/

mutual
/-- A renaming acts only through the variables a term uses. -/
theorem rename_congr :
    ∀ (t : Tm) (ρ ρ' : Nat → Nat), (∀ k, uses k t = true → ρ k = ρ' k) → rename ρ t = rename ρ' t
  | .var i, ρ, ρ', h => by simp only [rename, h i (by simp [uses])]
  | .lam A t, ρ, ρ', h => by
    have h' : ∀ k, uses k t = true → upR ρ k = upR ρ' k := by
      intro k hk; cases k with
      | zero => rfl
      | succ j => simp only [upR, h j (by simpa [uses] using hk)]
    simp only [rename, rename_congr t (upR ρ) (upR ρ') h']
  | .app t s, ρ, ρ', h => by
    simp only [rename,
      rename_congr t ρ ρ' (fun k hk => h k (by simp [uses, hk])),
      rename_congr s ρ ρ' (fun k hk => h k (by simp [uses, hk]))]
  | .box _ _, _, _, _ => rfl
  | .letbox t s, ρ, ρ', h => by
    simp only [rename,
      rename_congr t ρ ρ' (fun k hk => h k (by simp [uses, hk])),
      rename_congr s ρ ρ' (fun k hk => h k (by simp [uses, hk]))]
  | .mvar u σ, ρ, ρ', h => by
    simp only [rename, renameL_congr σ ρ ρ' (fun k hk => h k (by simpa [uses] using hk))]
theorem renameL_congr :
    ∀ (σ : List Tm) (ρ ρ' : Nat → Nat), (∀ k, usesL k σ = true → ρ k = ρ' k) →
      renameL ρ σ = renameL ρ' σ
  | [], _, _, _ => rfl
  | t :: σ, ρ, ρ', h => by
    simp only [renameL,
      rename_congr t ρ ρ' (fun k hk => h k (by simp [usesL, hk])),
      renameL_congr σ ρ ρ' (fun k hk => h k (by simp [usesL, hk]))]
end

/-- **The factorisation `t ≡ t₀[π]` at any position**: a term that does not use `x` is the
weakening at `x` of its strengthening at `x`. -/
theorem shiftAt_unshiftAt {x : Nat} {t : Tm} (hu : uses x t = false) :
    shiftAt x (unshiftAt x t) = t := by
  unfold shiftAt unshiftAt
  rw [rename_rename]
  conv => rhs; rw [← rename_id t]
  refine rename_congr t _ _ fun k hk => ?_
  have hkx : k ≠ x := by intro e; subst e; rw [hu] at hk; exact absurd hk (by decide)
  simp only [liftIdx, lowerIdx]
  by_cases hlt : k < x
  · simp [hlt]
  · have h2 : ¬ (k - 1 < x) := by omega
    simp only [hlt, h2, if_false]
    omega

/-- **Strengthening at any position**: the strengthened term is typed without hypothesis `x`. -/
theorem hasTy_unshiftAt {Δ : MEnv} {Γ : Ctx} {t : Tm} {A : Ty} {x : Nat}
    (h : HasTy Δ Γ t A) (hu : uses x t = false) : HasTy Δ (Γ.eraseIdx x) (unshiftAt x t) A := by
  refine hasTy_rename h _ _ fun i B hi hB => ?_
  have hix : i ≠ x := by intro e; subst e; rw [hu] at hi; exact absurd hi (by decide)
  simp only [lowerIdx]
  by_cases hlt : i < x
  · rw [if_pos hlt, List.getElem?_eraseIdx_of_lt hlt]; exact hB
  · rw [if_neg hlt, List.getElem?_eraseIdx_of_ge (by omega), Nat.sub_add_cancel (by omega)]
    exact hB

/-- The toy: `x₀ x₂` under `x₀ : base → base, x₁ : base, x₂ : base` does not use `x₁`;
strengthened it is `x₀ x₁`, typed under the context without `x₁`, and weakening at `1` gives the
original back. -/
theorem unshiftAt_toy :
    unshiftAt 1 (.app (.var 0) (.var 2)) = .app (.var 0) (.var 1) ∧
      shiftAt 1 (.app (.var 0) (.var 1)) = .app (.var 0) (.var 2) ∧
      HasTy MEnv.nil [.arr .base .base, .base] (unshiftAt 1 (.app (.var 0) (.var 2))) .base :=
  ⟨rfl, rfl, hasTy_unshiftAt (Γ := [.arr .base .base, .base, .base]) (x := 1)
    (HasTy.app (A := .base) (.var rfl) (.var rfl)) rfl⟩

/-! ## Partial metavariable substitution (hole filling) -/

theorem msubstPL_eq (θ : Nat → Option Tm) (d : Nat) :
    ∀ σ : List Tm, msubstPL θ d σ = σ.map (msubstP θ d)
  | [] => rfl
  | t :: σ => by simp only [msubstPL, msubstPL_eq θ d σ, List.map_cons]

/-- **Hole filling preserves typing.** At depth `d`, the environment `Δ'` agrees with `Δ` on the
bound metavariables and on every unfilled hole; a filled hole's filling is typed in the empty
environment under its declared context. The filled holes are free to be absent from `Δ'`. -/
theorem hasTy_msubstP {Δ : MEnv} {Γ : Ctx} {t : Tm} {B : Ty} (h : HasTy Δ Γ t B) :
    ∀ (θ : Nat → Option Tm) (d : Nat) (Δ' : MEnv),
      (∀ v, v < d → Δ' v = Δ v) →
      (∀ n, θ n = none → Δ' (n + d) = Δ (n + d)) →
      (∀ n M Ψ A, θ n = some M → Δ (n + d) = some (Ψ, A) → HasTy MEnv.nil Ψ M A) →
      HasTy Δ' Γ (msubstP θ d t) B := by
  induction h with
  | @var Δ Γ i A hi => intro _ _ _ _ _ _; exact .var hi
  | @lam Δ Γ A B t _ ih => intro θ d Δ' h1 h2 h3; exact .lam (ih θ d Δ' h1 h2 h3)
  | @app Δ Γ A B t s _ _ iht ihs =>
    intro θ d Δ' h1 h2 h3; exact .app (iht θ d Δ' h1 h2 h3) (ihs θ d Δ' h1 h2 h3)
  | @box Δ Γ Ψ A t _ ih => intro θ d Δ' h1 h2 h3; exact .box (ih θ d Δ' h1 h2 h3)
  | @letbox Δ Γ Φ C B t s _ _ iht ihs =>
    intro θ d Δ' h1 h2 h3
    refine .letbox (iht θ d Δ' h1 h2 h3) (ihs θ (d + 1) (MEnv.cons (Φ, C) Δ') ?_ ?_ ?_)
    · intro v hv
      cases v with
      | zero => rfl
      | succ w => exact h1 w (by omega)
    · intro n hn
      rw [show n + (d + 1) = (n + d) + 1 by omega]
      exact h2 n hn
    · intro n M Ψ A hn hv
      rw [show n + (d + 1) = (n + d) + 1 by omega] at hv
      exact h3 n M Ψ A hn hv
  | @mvar Δ Γ Φ C v σ hv hlen _ ih =>
    intro θ d Δ' h1 h2 h3
    have hσ : HasSubst Δ' Γ (msubstPL θ d σ) Φ := by
      refine ⟨by simp [msubstPL_eq, hlen], fun i s' D hs' hD => ?_⟩
      rw [msubstPL_eq, List.getElem?_map] at hs'
      cases hσi : σ[i]? with
      | none => simp [hσi] at hs'
      | some r =>
        simp only [hσi, Option.map_some, Option.some.injEq] at hs'
        subst hs'
        exact ih i r D hσi hD θ d Δ' h1 h2 h3
    by_cases hd : d ≤ v
    · cases hθ : θ (v - d) with
      | none =>
        simp only [msubstP, if_pos hd, hθ]
        refine .mvar ?_ hσ.1 hσ.2
        have e := h2 (v - d) hθ
        rw [Nat.sub_add_cancel hd] at e
        rw [e]; exact hv
      | some M =>
        simp only [msubstP, if_pos hd, hθ]
        have hM := h3 (v - d) M Φ C hθ (by rw [Nat.sub_add_cancel hd]; exact hv)
        have hM' : HasTy Δ' Φ (mren (· + d) M) C :=
          hasTy_mren hM Δ' (· + d) fun _ _ hP => by simp [MEnv.nil] at hP
        exact subst_lemma hσ hM'
    · simp only [msubstP, if_neg hd]
      refine .mvar ?_ hσ.1 hσ.2
      rw [h1 v (by omega)]; exact hv

/-! ## Weakening avoids the variable it inserts -/

mutual
/-- A renamed term uses only images of variables the original used. -/
theorem uses_rename :
    ∀ (t : Tm) (ρ : Nat → Nat) (k : Nat), uses k (rename ρ t) = true →
      ∃ j, uses j t = true ∧ ρ j = k
  | .var i, ρ, k, h => ⟨i, by simp [uses], by simpa [rename, uses] using h⟩
  | .lam A t, ρ, k, h => by
    obtain ⟨j, hj, e⟩ := uses_rename t (upR ρ) (k + 1) (by simpa [rename, uses] using h)
    cases j with
    | zero => simp [upR] at e
    | succ j => exact ⟨j, by simpa [uses] using hj, by simpa [upR] using e⟩
  | .app t s, ρ, k, h => by
    simp only [rename, uses, Bool.or_eq_true] at h
    rcases h with h | h
    · obtain ⟨j, hj, e⟩ := uses_rename t ρ k h; exact ⟨j, by simp [uses, hj], e⟩
    · obtain ⟨j, hj, e⟩ := uses_rename s ρ k h; exact ⟨j, by simp [uses, hj], e⟩
  | .box _ _, _, _, h => by simp [rename, uses] at h
  | .letbox t s, ρ, k, h => by
    simp only [rename, uses, Bool.or_eq_true] at h
    rcases h with h | h
    · obtain ⟨j, hj, e⟩ := uses_rename t ρ k h; exact ⟨j, by simp [uses, hj], e⟩
    · obtain ⟨j, hj, e⟩ := uses_rename s ρ k h; exact ⟨j, by simp [uses, hj], e⟩
  | .mvar u σ, ρ, k, h => by
    obtain ⟨j, hj, e⟩ := usesL_renameL σ ρ k (by simpa [rename, uses] using h)
    exact ⟨j, by simpa [uses] using hj, e⟩
theorem usesL_renameL :
    ∀ (σ : List Tm) (ρ : Nat → Nat) (k : Nat), usesL k (renameL ρ σ) = true →
      ∃ j, usesL j σ = true ∧ ρ j = k
  | [], _, _, h => by simp [renameL, usesL] at h
  | t :: σ, ρ, k, h => by
    simp only [renameL, usesL, Bool.or_eq_true] at h
    rcases h with h | h
    · obtain ⟨j, hj, e⟩ := uses_rename t ρ k h; exact ⟨j, by simp [usesL, hj], e⟩
    · obtain ⟨j, hj, e⟩ := usesL_renameL σ ρ k h; exact ⟨j, by simp [usesL, hj], e⟩
end

/-- **Weakening at `x` never uses `x`**: the inserted hypothesis is fresh. -/
theorem uses_shiftAt (x : Nat) (t : Tm) : uses x (shiftAt x t) = false := by
  cases h : uses x (shiftAt x t) with
  | false => rfl
  | true =>
    obtain ⟨j, _, e⟩ := uses_rename t (liftIdx x) x h
    simp only [liftIdx] at e
    split at e <;> omega

end Nanodregg.Lang.Contextual
