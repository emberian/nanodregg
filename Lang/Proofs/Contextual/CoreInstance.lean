/-
# Lang.Proofs.Contextual.CoreInstance — the laws of CMTT as a `Calculus` (lane CMTT-CORE)

`cmttLaws : CalculusLaws cmttData (fun Ω => HasTy (holeEnv Ω))`: every theorem
`Lang.Proofs.Contextual.Closure` proves over all lawful calculi holds of CMTT. Law by law:

| law | Core |
|---|---|
| `msubst_lemma` | `hasTy_msubstP` + `holeEnv_filter` + `holeEnv_some` |
| `check_sound`, `check_complete` | `check_sound`, `check_complete` |
| `strengthen_lemma` | `hasTy_unshiftAt` |
| `strengthen_factor` | `shiftAt_unshiftAt` |
| `weaken_avoids` | `uses_shiftAt` (holds without the typing premise) |
| `hasTy_var` | `HasTy.var` |
| `uses_var` | `uses` on `var` |
-/
import Lang.Contextual.CoreCalculus
import Lang.Proofs.Contextual.Typing
import Lang.Proofs.Contextual.Core
import Lang.Proofs.Contextual.ClosureStatements

namespace Nanodregg.Lang.Contextual

theorem holeEnv_nil : holeEnv [] = MEnv.nil := rfl

/-- Removing declarations of OTHER names (or none of name `n`) leaves `n`'s lookup alone. -/
theorem holeEnv_filter (p : HoleDecl Ctx Ty → Bool) (n : Nat) :
    ∀ Ω : List (HoleDecl Ctx Ty), (∀ d ∈ Ω, d.name = n → p d = true) →
      holeEnv (Ω.filter p) n = holeEnv Ω n
  | [], _ => rfl
  | d :: Ω, h => by
    have ih := holeEnv_filter p n Ω fun d' hd' => h d' (List.mem_cons_of_mem _ hd')
    by_cases hn : d.name = n
    · have hp := h d List.mem_cons_self hn
      simp only [holeEnv, List.filter_cons_of_pos hp, List.find?_cons, hn, beq_self_eq_true]
    · have hb : (d.name == n) = false := by simp [hn]
      by_cases hp : p d = true
      · simp only [holeEnv, List.filter_cons_of_pos hp, List.find?_cons, hb] at ih ⊢
        exact ih
      · simp only [holeEnv, List.filter_cons_of_neg hp, List.find?_cons, hb] at ih ⊢
        exact ih

theorem holeEnv_some {Ω : List (HoleDecl Ctx Ty)} {n : Nat} {Ψ : Ctx} {A : Ty}
    (h : holeEnv Ω n = some (Ψ, A)) : ∃ d ∈ Ω, d.name = n ∧ d.ctx = Ψ ∧ d.ty = A := by
  unfold holeEnv at h
  simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
  obtain ⟨d, hd, hc, ht⟩ := h
  exact ⟨d, List.mem_of_find?_eq_some hd, by simpa using List.find?_some hd, hc, ht⟩

/-- **CMTT is a lawful `Calculus`.** -/
theorem cmttLaws : CalculusLaws cmttData (fun Ω => HasTy (holeEnv Ω)) where
  msubst_lemma := by
    intro Ω Γ P T θ hP hθ
    refine hasTy_msubstP hP θ 0 _ (fun v hv => absurd hv (Nat.not_lt_zero v)) ?_ ?_
    · intro n hn
      exact holeEnv_filter _ n Ω fun d _ hd => by rw [hd, hn]; rfl
    · intro n M Ψ A hn hv
      obtain ⟨d, hd, hname, hctx, hty⟩ := holeEnv_some hv
      have := hθ d hd M (by rw [hname]; exact hn)
      rw [hctx, hty] at this
      exact this
  check_sound := check_sound
  check_complete := check_complete
  strengthen_lemma := hasTy_unshiftAt
  strengthen_factor := shiftAt_unshiftAt
  weaken_avoids := fun {_ M _ x} _ => uses_shiftAt x M
  hasTy_var := HasTy.var
  uses_var := by intro x; simp [cmttData, uses]

/-! ## Toy: a template with one hole, filled -/

/-- The hole `0 :: [r : base ⊢ base]` (a continuation awaiting a response `r`). -/
private def bellHole : HoleDecl Ctx Ty := ⟨0, [.base], .base⟩

/-- The template `λx. u₀[x]`: resume the hole at the argument. -/
private def bellTemplate : Tm := .lam .base (.mvar 0 [.var 0])

/-- The filling `u₀ := r.(λy.y) r`. -/
private def bellFill : Nat → Option Tm :=
  fun n => if n = 0 then some (.app (.lam .base (.var 0)) (.var 0)) else none

/-- The template is typed WITH the hole and NOT without it; filled, it computes to
`λx. (λy.y) x` and is typed with the hole gone, through `cmttLaws.msubst_lemma`. -/
theorem bell_template_toy :
    HasTy (holeEnv [bellHole]) [] bellTemplate (.arr .base .base) ∧
      ¬ HasTy (holeEnv []) [] bellTemplate (.arr .base .base) ∧
      cmttData.msubst bellFill bellTemplate = .lam .base (.app (.lam .base (.var 0)) (.var 0)) ∧
      HasTy (holeEnv []) [] (cmttData.msubst bellFill bellTemplate) (.arr .base .base) := by
  have hT : HasTy (holeEnv [bellHole]) [] bellTemplate (.arr .base .base) :=
    HasTy.lam (HasTy.mvar' rfl (hasSubst_cons (.var rfl) (hasSubst_nil _ _)))
  refine ⟨hT, ?_, rfl, ?_⟩
  · intro h
    cases h with
    | lam hb => cases hb with | mvar hu _ _ => cases hu
  · have := cmttLaws.msubst_lemma (Ω := [bellHole]) (Γ := []) (P := bellTemplate)
      (T := .arr .base .base) bellFill hT
      (fun d hd M hM => by
        simp only [List.mem_singleton] at hd
        subst hd
        simp only [bellHole, bellFill, if_true] at hM
        injection hM with hM
        subst hM
        show HasTy (holeEnv []) [.base] _ .base
        exact HasTy.app (HasTy.lam (HasTy.var rfl)) (HasTy.var rfl))
    simpa [bellHole, bellFill] using this

/-- The instance's strengthening is the real one: `t ≡ t₀[π]` with `t₀ ≠ t`. -/
theorem cmtt_strengthen_toy :
    cmttData.strengthen 1 (.app (.var 0) (.var 2)) = (.app (.var 0) (.var 1) : Tm) ∧
      cmttData.weaken 1 (cmttData.strengthen 1 (.app (.var 0) (.var 2))) =
        (.app (.var 0) (.var 2) : Tm) :=
  ⟨rfl, rfl⟩

end Nanodregg.Lang.Contextual
