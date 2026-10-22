/- The deployed language, including substituted contextual holes, is a lawful calculus. -/
import Lang.Contextual.LangInstance
import Lang.Proofs.Contextual.LangOccurrences
import Lang.Proofs.Contextual.ClosureStatements

namespace Nanodregg.Lang.Contextual

/-- A closed term is typed under every library and ordinary ambient context. -/
theorem hasType_closed_lift {M : Term} {A : Lang.Ty} (h : HasType [] [] M A)
    (Δ' Γ : List Lang.Ty) : HasType Δ' Γ M A := by
  have h1 := hasType_library (Δ' := Δ') (fun _ _ hA => by simp at hA) h
  have h2 := hasType_renameVar_live h1 Γ (fun i => i) fun _ _ _ hB => by simp at hB
  rwa [renameVar_id] at h2

/-! ## The holes' declarations -/

theorem holeTy_some {Ω : List (HoleDecl (List Lang.Ty) Lang.Ty)} {n : Nat} {A : Lang.Ty}
    (h : holeTy Ω n = some A) : ∃ d ∈ Ω, d.name = n ∧ d.ty = A := by
  unfold holeTy at h
  simp only [Option.map_eq_some_iff] at h
  obtain ⟨d, hd, ht⟩ := h
  exact ⟨d, List.mem_of_find?_eq_some hd, by simpa using List.find?_some hd, ht⟩

/-- Removing declarations of OTHER names (or none of name `n`) leaves `n`'s type alone. -/
theorem holeTy_filter (p : HoleDecl (List Lang.Ty) Lang.Ty → Bool) (n : Nat) :
    ∀ Ω : List (HoleDecl (List Lang.Ty) Lang.Ty), (∀ d ∈ Ω, d.name = n → p d = true) →
      holeTy (Ω.filter p) n = holeTy Ω n
  | [], _ => rfl
  | d :: Ω, h => by
    have ih := holeTy_filter p n Ω fun d' hd' => h d' (List.mem_cons_of_mem _ hd')
    by_cases hn : d.name = n
    · have hp := h d List.mem_cons_self hn
      simp only [holeTy, List.filter_cons_of_pos hp, List.find?_cons, hn, beq_self_eq_true]
    · have hb : (d.name == n) = false := by simp [hn]
      by_cases hp : p d = true
      · simp only [holeTy, List.filter_cons_of_pos hp, List.find?_cons, hb] at ih ⊢
        exact ih
      · simp only [holeTy, List.filter_cons_of_neg hp, List.find?_cons, hb] at ih ⊢
        exact ih

/-- Every contextual hole occurrence has its named declaration. -/
def RefsDeclared (Ω : HoleSignature) (t : Term) : Prop :=
  ∀ n, Term.usesRef n t = true → (holeTy Ω n).isSome = true

/-- The contextual judgment uses the deployed checker signature. Ordinary imports
remain unavailable to standalone calculus fillings; their namespace is distinct. -/
def LangHasTy (Ω : HoleSignature) (Γ : List Lang.Ty) (t : Term) (T : Lang.Ty) : Prop :=
  HasType [] Γ t T Ω

theorem refsDeclared_nil {t : Term} (h : RefsDeclared [] t) (n : Nat) : Term.usesRef n t = false := by
  cases hn : Term.usesRef n t with
  | false => rfl
  | true => have := h n hn; simp [holeTy] at this

theorem langHasTy_nil_iff {Γ : List Lang.Ty} {t : Term} {T : Lang.Ty} :
    LangHasTy [] Γ t T ↔ HasType [] Γ t T := Iff.rfl

/-- The signature-aware typing relation itself enforces declarations. -/
theorem langHasTy_declared {Ω : HoleSignature} {Γ : List Lang.Ty} {t : Term} {T : Lang.Ty}
    (h : LangHasTy Ω Γ t T) : RefsDeclared Ω t := by
  intro n hn
  have hd := hasType_declaresHole h n hn
  simpa [holeTy] using hd

theorem langLaws : CalculusLaws langData LangHasTy where
  msubst_lemma := by
    intro Ω Γ P T σ hP hfill
    apply fillHoles_typed σ ?_ ?_ hP
    · intro n d M hd hm
      have hn : d.name = n := by simpa using List.find?_some hd
      exact hfill d (List.mem_of_find?_eq_some hd) M (hn ▸ hm)
    · intro n d hd hn
      exact (declaration_filter (fun d => (σ d.name).isNone) n Ω (fun e _ he => by
        change (σ e.name).isNone = true
        rw [he, hn]
        rfl)).trans hd
  check_sound := by
    intro Ψ M A h
    exact Lang.infer_sound (of_decide_eq_true h)
  check_complete := by
    intro Ψ M A h
    exact decide_eq_true (Lang.infer_complete h)
  strengthen_lemma := by
    intro Ψ M A x h hu
    exact hasType_unshiftAt_live h hu
  strengthen_factor := Term.shiftAt_unshiftAt
  weaken_avoids := fun {_ M _ x} _ => usesVar_shiftAt x M
  hasTy_var := fun h => .var h
  uses_var := by intro x; simp [langData, Term.usesVar]

/-- Strengthening changes indices and weakening recovers the original term. -/
theorem lang_strengthen_toy :
    langData.strengthen 1 (.app (.var 0) (.var 2)) = (.app (.var 0) (.var 1) : Term) ∧
      langData.weaken 1 (langData.strengthen 1 (.app (.var 0) (.var 2))) =
        (.app (.var 0) (.var 2) : Term) := ⟨rfl, rfl⟩

private def natHole : HoleDecl (List Lang.Ty) Lang.Ty := ⟨0, [], .fn .nat .nat⟩
private def natTemplate : Term := .app (.hole 0 []) (.nat 3)
private def natFill : Nat → Option Term := fun n => if n = 0 then some (.lam .nat (.var 0)) else none

/-- A declared hole checks, an undeclared one refuses, and filling removes the obligation. -/
theorem lang_template_toy :
    LangHasTy [natHole] [] natTemplate .nat ∧
      ¬ LangHasTy [] [] natTemplate .nat ∧
      langData.msubst natFill natTemplate = .app (.lam .nat (.var 0)) (.nat 3) ∧
      LangHasTy [] [] (langData.msubst natFill natTemplate) .nat := by
  have hT : LangHasTy [natHole] [] natTemplate .nat :=
    .app (.hole (d := natHole) rfl .nil) (.nat (by decide))
  refine ⟨hT, fun h => ?_, rfl, ?_⟩
  · have := hasType_declaresHole h 0 (by simp [natTemplate, Term.usesRef, Term.usesRefList])
    simp at this
  · have := langLaws.msubst_lemma (Ω := [natHole]) (Γ := []) (P := natTemplate) (T := .nat) natFill hT
      (fun d hd M hM => by
        simp only [List.mem_singleton] at hd
        subst hd
        simp only [natHole, natFill, if_true] at hM
        injection hM with hM
        subst hM
        exact .lam (by decide) (.var rfl))
    simpa [natHole, natFill] using this

end Nanodregg.Lang.Contextual
