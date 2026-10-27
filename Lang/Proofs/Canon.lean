/-
# Lang.Proofs.Canon — rows stay ascending, so every inferred type is canonical

`put_ascending`/`merge_ascending`: `Row.put` and `Row.merge` keep an ascending row ascending (and
`find_merge` is their spec: a merged row reads every new field, the last write winning, and
otherwise the base). With them, `hasType_wf`/`infer_wf`: under canonical package and local types,
the type a term has is canonical (`Ty.wf`), so `extend` cannot manufacture a row the annotations
could not write. (Discharged wherever interfaces come from the loader, where each passed `checkShape`: the run,
the judge and, since LANG-35, `checkInstall`.)
-/
import Lang.Proofs.Typing
import Lang.Proofs.Row
import Lang.Proofs.Check

namespace Nanodregg.Lang

namespace Row

variable {α β : Type}

theorem ascending_cons_iff {k : Label} {a : α} :
    ∀ {r : List (Label × α)}, ascending ((k, a) :: r) = true ↔ (∀ e ∈ r, k < e.1) ∧ ascending r = true
  | [] => by simp [ascending]
  | (k2, b) :: r => by
    rw [show ascending ((k, a) :: (k2, b) :: r) = (decide (k < k2) && ascending ((k2, b) :: r)) from rfl]
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · rintro ⟨hk, hr⟩
      refine ⟨?_, hr⟩
      intro e he
      simp only [List.mem_cons] at he
      rcases he with rfl | he
      · exact hk
      · exact String.lt_trans hk ((ascending_cons_iff.mp hr).1 e he)
    · rintro ⟨hall, hr⟩
      exact ⟨hall _ (List.mem_cons_self ..), hr⟩


/-- An ascending row is already sorted. -/
theorem sort_of_ascending : ∀ {r : List (Label × α)}, ascending r = true → sort r = r
  | [], _ => rfl
  | (k, a) :: r, h => by
    obtain ⟨hall, hr⟩ := ascending_cons_iff.mp h
    show insert (k, a) (sort r) = (k, a) :: r
    rw [sort_of_ascending hr]
    cases r with
    | nil => rfl
    | cons e r => simp [insert, String.lt_asymm (hall e (List.mem_cons_self ..))]

theorem lt_of_not_lt_ne {a b : Label} (h1 : ¬ a < b) (h2 : a ≠ b) : b < a := by
  rcases String.le_total a b with h | h
  · exact absurd (String.le_antisymm h (String.not_lt.mp h1)) h2
  · by_cases h3 : b < a
    · exact h3
    · exact absurd (String.le_antisymm (String.not_lt.mp h3) h) h2

theorem mem_put {ℓ : Label} {a : α} :
    ∀ {r : List (Label × α)} {e : Label × α}, e ∈ put ℓ a r → e = (ℓ, a) ∨ e ∈ r
  | [], e, h => by simp [put] at h; exact .inl h
  | (k, b) :: rest, e, h => by
    simp only [put] at h
    by_cases lt : ℓ < k
    · simp only [if_pos lt, List.mem_cons] at h ⊢; exact h
    · by_cases eq : ℓ = k
      · simp only [if_neg lt, if_pos eq, List.mem_cons] at h ⊢
        rcases h with h | h
        · exact .inl h
        · exact .inr (.inr h)
      · simp only [if_neg lt, if_neg eq, List.mem_cons] at h ⊢
        rcases h with h | h
        · exact .inr (.inl h)
        · rcases mem_put h with h | h
          · exact .inl h
          · exact .inr (.inr h)

theorem put_ascending {ℓ : Label} {a : α} :
    ∀ {r : List (Label × α)}, ascending r = true → ascending (put ℓ a r) = true
  | [], _ => rfl
  | (k, b) :: rest, h => by
    have ⟨hall, hr⟩ := ascending_cons_iff.mp h
    simp only [put]
    split
    · rename_i lt
      refine ascending_cons_iff.mpr ⟨?_, h⟩
      intro e he
      simp only [List.mem_cons] at he
      rcases he with rfl | he
      · exact lt
      · exact String.lt_trans lt (hall e he)
    · split
      · rename_i _ eq; subst eq; exact ascending_cons_iff.mpr ⟨hall, hr⟩
      · rename_i nlt ne
        refine ascending_cons_iff.mpr ⟨?_, put_ascending hr⟩
        intro e he
        rcases mem_put he with rfl | he
        · exact lt_of_not_lt_ne nlt ne
        · exact hall e he

theorem mem_merge : ∀ {base over : List (Label × α)} {e : Label × α},
    e ∈ merge base over → e ∈ base ∨ e ∈ over
  | base, [], e, h => .inl h
  | base, (ℓ, a) :: rest, e, h => by
    simp only [merge] at h
    rcases mem_merge h with h | h
    · rcases mem_put h with rfl | h
      · exact .inr (List.mem_cons_self ..)
      · exact .inl h
    · exact .inr (List.mem_cons_of_mem _ h)

/-- `put` writes its entry and leaves every other label's lookup alone. -/
theorem find_put {ℓ k : Label} {a : α} :
    ∀ {r : List (Label × α)}, find? ℓ (put k a r) = if ℓ = k then some a else find? ℓ r
  | [] => by simp [put, find?]
  | (j, b) :: rest => by
    simp only [put]
    by_cases lt : k < j
    · simp only [if_pos lt, find?]
    · by_cases eq : k = j
      · subst eq; simp only [if_neg lt, if_true, find?]; by_cases h : ℓ = k <;> simp [h]
      · simp only [if_neg lt, if_neg eq, find?]
        by_cases hj : ℓ = j
        · subst hj
          have : ℓ ≠ k := fun e => eq e.symm
          simp [this]
        · simp only [if_neg hj]; exact find_put

theorem find_append {ℓ : Label} : ∀ {xs ys : List (Label × α)},
    find? ℓ (xs ++ ys) = (find? ℓ xs).orElse fun _ => find? ℓ ys
  | [], _ => by simp [find?]
  | (k, a) :: xs, ys => by
    simp only [List.cons_append, find?]
    split
    · rfl
    · exact find_append

/-- The spec of `extend`'s row: a label reads its LAST write in `over`, else its value in `base`.
(Every new field survives; nothing else changes.) -/
theorem find_merge {ℓ : Label} : ∀ {base over : List (Label × α)},
    find? ℓ (merge base over) = (find? ℓ over.reverse).orElse fun _ => find? ℓ base
  | base, [] => by simp [merge, find?]
  | base, (k, a) :: rest => by
    simp only [merge, List.reverse_cons]
    rw [find_merge, find_append, find_put]
    simp only [find?]
    cases find? ℓ rest.reverse <;> by_cases h : ℓ = k <;> simp [h]

/-- `extend`'s row is canonical when its base is (whatever order the new fields come in). -/
theorem merge_ascending : ∀ {base : List (Label × α)} (over : List (Label × α)),
    ascending base = true → ascending (merge base over) = true
  | _, [], h => h
  | _, (_, _) :: rest, h => merge_ascending rest (put_ascending h)

/-- Ascending is a property of the labels alone. -/
theorem ascending_of_labels : ∀ {xs : List (Label × α)} {ys : List (Label × β)},
    xs.map Prod.fst = ys.map Prod.fst → ascending xs = ascending ys
  | [], [], _ => rfl
  | [_], [_], _ => rfl
  | x :: x' :: xs, y :: y' :: ys, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    have ih := ascending_of_labels (xs := x' :: xs) (ys := y' :: ys) (by simp [h.2.1, h.2.2])
    simp only [ascending, h.1, h.2.1, ih]
  | [], _ :: _, h | _ :: _, [], h => by simp at h
  | [_], _ :: _ :: _, h | _ :: _ :: _, [_], h => by simp at h

end Row

/-! ## Inferred types are canonical -/

theorem rowWf_iff : ∀ {r : List (Label × Ty)}, Ty.rowWf r = true ↔ ∀ e ∈ r, e.2.wf = true
  | [] => by simp [Ty.rowWf]
  | (_, t) :: r => by simp [Ty.rowWf, rowWf_iff (r := r)]

theorem rowWf_find {ℓ : Label} {t : Ty} :
    ∀ {row : List (Label × Ty)}, Ty.rowWf row = true → Row.find? ℓ row = some t → t.wf = true
  | [], _, h => by simp [Row.find?] at h
  | (k, u) :: row, hw, h => by
    simp only [Ty.rowWf, Bool.and_eq_true] at hw
    simp only [Row.find?] at h
    split at h
    · cases h; exact hw.1
    · exact rowWf_find hw.2 h

theorem fieldsTy_labels {Δ : List Ty} {Ω : HoleSignature} : ∀ {Γ : List Ty} {fs : List (Label × Term)} {r : List (Label × Ty)},
    FieldsTy (Ω := Ω) Δ Γ fs r → fs.map Prod.fst = r.map Prod.fst
  | _, _, _, .nil => rfl
  | _, _, _, .cons _ h => by simp [fieldsTy_labels h]

theorem cons_wf {A : Ty} {Γ : List Ty} (hA : A.wf = true) (hΓ : ∀ B ∈ Γ, B.wf = true) :
    ∀ B ∈ A :: Γ, B.wf = true := by
  intro B hm
  simp only [List.mem_cons] at hm
  rcases hm with rfl | hm
  · exact hA
  · exact hΓ B hm

variable {Δ : List Ty}

mutual
theorem hasType_wf {Ω : HoleSignature} (hΔ : ∀ A ∈ Δ, A.wf = true) (hΩ : ∀ d ∈ Ω, d.ty.wf = true) :
    ∀ {Γ : List Ty} {t : Term} {T : Ty}, (∀ A ∈ Γ, A.wf = true) → HasType (Ω := Ω) Δ Γ t T → T.wf = true
  | _, _, _, hΓ, .var h => hΓ _ (List.mem_of_getElem? h)
  | _, _, _, hΓ, .lam hA hb => by
    simp only [Ty.wf, hA, hasType_wf hΔ hΩ (cons_wf hA hΓ) hb, Bool.and_self]
  | _, _, _, hΓ, .app hf _ => by
    have := hasType_wf hΔ hΩ hΓ hf; simp only [Ty.wf, Bool.and_eq_true] at this; exact this.2
  | _, _, _, hΓ, .fix ht => by
    have := hasType_wf hΔ hΩ hΓ ht; simp only [Ty.wf, Bool.and_eq_true] at this ⊢; exact this.1
  | _, _, _, _, .nat _ | _, _, _, _, .bool | _, _, _, _, .bytes _ | _, _, _, _, .digest _ => rfl
  | _, _, _, _, .refuse hw _ => hw
  | _, _, _, _, .prim (p := p) _ _ => by cases p <;> rfl
  | _, _, _, hΓ, .record hasc hfs => by
    simp only [Ty.wf, Bool.and_eq_true]
    exact ⟨(Row.ascending_of_labels (fieldsTy_labels hfs)) ▸ hasc, fieldsTy_wf hΔ hΩ hΓ hfs⟩
  | _, _, _, hΓ, .get ht hf => by
    have := hasType_wf hΔ hΩ hΓ ht; simp only [Ty.wf, Bool.and_eq_true] at this
    exact rowWf_find this.2 hf
  | _, _, _, hΓ, .extend (r := r) (r2 := r2) ht _ hfs => by
    have hb := hasType_wf hΔ hΩ hΓ ht
    simp only [Ty.wf, Bool.and_eq_true] at hb ⊢
    refine ⟨Row.merge_ascending _ hb.1, rowWf_iff.mpr fun e he => ?_⟩
    rcases Row.mem_merge he with he | he
    · exact rowWf_iff.mp hb.2 e he
    · exact rowWf_iff.mp (fieldsTy_wf hΔ hΩ hΓ hfs) e he
  | _, _, _, _, .inj hw _ _ => hw
  | _, _, _, hΓ, .case ht ha => by
    have := hasType_wf hΔ hΩ hΓ ht; simp only [Ty.wf, Bool.and_eq_true] at this
    exact armsTy_wf hΔ hΩ hΓ this.2 ha
  | _, _, _, hΓ, .ite _ ha _ => hasType_wf hΔ hΩ hΓ ha
  | _, _, _, _, .ref h => hΔ _ (List.mem_of_getElem? h)
  | _, _, _, _, .hole hf _ => hΩ _ (List.mem_of_find?_eq_some hf)

theorem fieldsTy_wf {Ω : HoleSignature} (hΔ : ∀ A ∈ Δ, A.wf = true) (hΩ : ∀ d ∈ Ω, d.ty.wf = true) :
    ∀ {Γ : List Ty} {fs : List (Label × Term)} {r : List (Label × Ty)},
      (∀ A ∈ Γ, A.wf = true) → FieldsTy (Ω := Ω) Δ Γ fs r → Ty.rowWf r = true
  | _, _, _, _, .nil => rfl
  | _, _, _, hΓ, .cons ht hfs => by
    simp only [Ty.rowWf, Bool.and_eq_true]; exact ⟨hasType_wf hΔ hΩ hΓ ht, fieldsTy_wf hΔ hΩ hΓ hfs⟩

theorem armsTy_wf {Ω : HoleSignature} (hΔ : ∀ A ∈ Δ, A.wf = true) (hΩ : ∀ d ∈ Ω, d.ty.wf = true) :
    ∀ {Γ : List Ty} {arms : List (Label × Term)} {r : List (Label × Ty)} {B : Ty},
      (∀ A ∈ Γ, A.wf = true) → Ty.rowWf r = true → ArmsTy (Ω := Ω) Δ Γ arms r B → B.wf = true
  | _, _, _, _, hΓ, hr, .one hb => by
    simp only [Ty.rowWf, Bool.and_eq_true] at hr
    exact hasType_wf hΔ hΩ (cons_wf hr.1 hΓ) hb
  | _, _, _, _, hΓ, hr, .cons hb _ _ => by
    simp only [Ty.rowWf, Bool.and_eq_true] at hr
    exact hasType_wf hΔ hΩ (cons_wf hr.1 hΓ) hb
end

/-- Under canonical package and local types, every type `infer` returns is canonical. -/
theorem infer_wf {Γ : List Ty} {t : Term} {T : Ty} (hΔ : ∀ A ∈ Δ, A.wf = true)
    (hΓ : ∀ A ∈ Γ, A.wf = true) (h : infer Δ Γ t (Ω := []) = some T) : T.wf = true :=
  hasType_wf hΔ (by simp) hΓ (infer_sound h)

/-- The tooth: `merge` puts a new field in its place and overrides in place (an appending or
prepending `put` would turn this red, and with it `merge_ascending`). -/
theorem merge_in_order :
    Row.merge [("a", Ty.nat), ("c", .bool)] [("b", .bytes), ("a", .bool)] =
      [("a", .bool), ("b", .bytes), ("c", .bool)] := by decide

/-- A new label past the last and a merge into nothing (a `put` that drops at the end of the row
keeps every ascending theorem green; these and `find_merge` do not). -/
theorem merge_past_end : Row.merge [("a", Ty.nat)] [("z", .bool)] = [("a", .nat), ("z", .bool)] := by
  decide

theorem merge_into_empty : Row.merge [] [("a", Ty.nat)] = [("a", .nat)] := by decide

end Nanodregg.Lang
