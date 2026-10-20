/-
# Lang.Proofs.Contextual.LangInstance — the laws of `Lang.Term` as a `Calculus` (ACTIVITIES-2)

`langLaws : CalculusLaws langData LangHasTy`. `LangHasTy Ω Γ t T` asks every hole's context to be
empty, every `ref` to be a declared hole, and `t` typed by `Lang.HasType` with the holes as the
package types (`ΔOf Ω`). Law by law:

| law | Lang theorem |
|---|---|
| `msubst_lemma` | `fillRefs_typed` + `usesRef_fillRefs` + `tyOf_filter` + `ΔOf_getElem?` |
| `check_sound`, `check_complete` | `Lang.infer_sound`, `Lang.infer_complete` (+ `hasType_usesRef` for the refs) |
| `strengthen_lemma` | `hasType_unshiftAt` (+ `usesRef_renameVar`) |
| `strengthen_factor` | `shiftAt_unshiftAt` |
| `weaken_avoids` | `usesVar_shiftAt` (holds without the typing premise) |
| `hasTy_var` | `HasType.var` |
| `uses_var` | `Term.usesVar` on `var` |

The REACH theorem `langTemplate_no_hyps`: in every template typed by `LangHasTy`, every hole has
no token-backed hypothesis, so the closure's strengthening outcome, its alternative-by-hypothesis
outcome and its hypothesis-derived supports are EMPTY on every Lang template (the closed-hole
fragment; the CMTT instance `cmttLaws` is where they are exercised).
-/
import Lang.Contextual.LangCalculus
import Lang.Proofs.Check
import Lang.Proofs.Load
import Lang.Proofs.Contextual.Core
import Lang.Proofs.Contextual.Closure

namespace Nanodregg.Lang.Contextual

/-! ## Row shapes -/

theorem renameVarRow_ascending (ρ : Nat → Nat) :
    ∀ fs : List (Label × Term), Row.ascending (Term.renameVarRow ρ fs) = Row.ascending fs
  | [] => rfl
  | [_] => rfl
  | (a, s) :: (b, t) :: rest => by
      have ih := renameVarRow_ascending ρ ((b, t) :: rest)
      simp only [Term.renameVarRow] at ih ⊢
      simp only [Row.ascending, ih]

theorem fillRefsRow_ascending (σ : Nat → Option Term) :
    ∀ fs : List (Label × Term), Row.ascending (Term.fillRefsRow σ fs) = Row.ascending fs
  | [] => rfl
  | [_] => rfl
  | (a, s) :: (b, t) :: rest => by
      have ih := fillRefsRow_ascending σ ((b, t) :: rest)
      simp only [Term.fillRefsRow] at ih ⊢
      simp only [Row.ascending, ih]

/-! ## Renaming composes -/

mutual
theorem renameVar_renameVar (ρ ρ' : Nat → Nat) : ∀ t : Term,
    Term.renameVar ρ (Term.renameVar ρ' t) = Term.renameVar (fun i => ρ (ρ' i)) t
  | .var _ | .nat _ | .bool _ | .bytes _ | .digest _ | .ref _ | .refuse _ _ => rfl
  | .lam _ b => by simp only [Term.renameVar, renameVar_renameVar (upR ρ) (upR ρ') b, upR_upR]
  | .app f a => by
    simp only [Term.renameVar, renameVar_renameVar ρ ρ' f, renameVar_renameVar ρ ρ' a]
  | .fix t => by simp only [Term.renameVar, renameVar_renameVar ρ ρ' t]
  | .prim _ a b => by
    simp only [Term.renameVar, renameVar_renameVar ρ ρ' a, renameVar_renameVar ρ ρ' b]
  | .record fs => by simp only [Term.renameVar, renameVarRow_renameVarRow ρ ρ' fs]
  | .get t _ => by simp only [Term.renameVar, renameVar_renameVar ρ ρ' t]
  | .extend t fs => by
    simp only [Term.renameVar, renameVar_renameVar ρ ρ' t, renameVarRow_renameVarRow ρ ρ' fs]
  | .inj _ _ t => by simp only [Term.renameVar, renameVar_renameVar ρ ρ' t]
  | .case t as => by
    simp only [Term.renameVar, renameVar_renameVar ρ ρ' t, renameVarArms_renameVarArms ρ ρ' as]
  | .ite c a b => by
    simp only [Term.renameVar, renameVar_renameVar ρ ρ' c, renameVar_renameVar ρ ρ' a,
      renameVar_renameVar ρ ρ' b]
theorem renameVarRow_renameVarRow (ρ ρ' : Nat → Nat) : ∀ fs : List (Label × Term),
    Term.renameVarRow ρ (Term.renameVarRow ρ' fs) = Term.renameVarRow (fun i => ρ (ρ' i)) fs
  | [] => rfl
  | (_, t) :: fs => by
    simp only [Term.renameVarRow, renameVar_renameVar ρ ρ' t, renameVarRow_renameVarRow ρ ρ' fs]
theorem renameVarArms_renameVarArms (ρ ρ' : Nat → Nat) : ∀ as : List (Label × Term),
    Term.renameVarArms ρ (Term.renameVarArms ρ' as) = Term.renameVarArms (fun i => ρ (ρ' i)) as
  | [] => rfl
  | (_, t) :: as => by
    simp only [Term.renameVarArms, renameVar_renameVar (upR ρ) (upR ρ') t, upR_upR,
      renameVarArms_renameVarArms ρ ρ' as]
end

mutual
theorem renameVar_id : ∀ t : Term, Term.renameVar (fun i => i) t = t
  | .var _ | .nat _ | .bool _ | .bytes _ | .digest _ | .ref _ | .refuse _ _ => rfl
  | .lam _ b => by simp only [Term.renameVar, upR_id, renameVar_id b]
  | .app f a => by simp only [Term.renameVar, renameVar_id f, renameVar_id a]
  | .fix t => by simp only [Term.renameVar, renameVar_id t]
  | .prim _ a b => by simp only [Term.renameVar, renameVar_id a, renameVar_id b]
  | .record fs => by simp only [Term.renameVar, renameVarRow_id fs]
  | .get t _ => by simp only [Term.renameVar, renameVar_id t]
  | .extend t fs => by simp only [Term.renameVar, renameVar_id t, renameVarRow_id fs]
  | .inj _ _ t => by simp only [Term.renameVar, renameVar_id t]
  | .case t as => by simp only [Term.renameVar, renameVar_id t, renameVarArms_id as]
  | .ite c a b => by simp only [Term.renameVar, renameVar_id c, renameVar_id a, renameVar_id b]
theorem renameVarRow_id : ∀ fs : List (Label × Term), Term.renameVarRow (fun i => i) fs = fs
  | [] => rfl
  | (_, t) :: fs => by simp only [Term.renameVarRow, renameVar_id t, renameVarRow_id fs]
theorem renameVarArms_id : ∀ as : List (Label × Term), Term.renameVarArms (fun i => i) as = as
  | [] => rfl
  | (_, t) :: as => by simp only [Term.renameVarArms, upR_id, renameVar_id t, renameVarArms_id as]
end

/-! ## A renaming acts only through the variables a term uses -/

mutual
theorem renameVar_congr : ∀ (t : Term) (ρ ρ' : Nat → Nat),
    (∀ k, Term.usesVar k t = true → ρ k = ρ' k) → Term.renameVar ρ t = Term.renameVar ρ' t
  | .var i, ρ, ρ', h => by simp only [Term.renameVar, h i (by simp [Term.usesVar])]
  | .nat _, _, _, _ | .bool _, _, _, _ | .bytes _, _, _, _ | .digest _, _, _, _
  | .ref _, _, _, _ | .refuse _ _, _, _, _ => rfl
  | .lam _ b, ρ, ρ', h => by
    have h' : ∀ k, Term.usesVar k b = true → upR ρ k = upR ρ' k := by
      intro k hk; cases k with
      | zero => rfl
      | succ j => simp only [upR, h j (by simpa [Term.usesVar] using hk)]
    simp only [Term.renameVar, renameVar_congr b _ _ h']
  | .app f a, ρ, ρ', h => by
    simp only [Term.renameVar,
      renameVar_congr f ρ ρ' fun k hk => h k (by simp [Term.usesVar, hk]),
      renameVar_congr a ρ ρ' fun k hk => h k (by simp [Term.usesVar, hk])]
  | .fix t, ρ, ρ', h => by
    simp only [Term.renameVar, renameVar_congr t ρ ρ' fun k hk => h k (by simp [Term.usesVar, hk])]
  | .prim _ a b, ρ, ρ', h => by
    simp only [Term.renameVar,
      renameVar_congr a ρ ρ' fun k hk => h k (by simp [Term.usesVar, hk]),
      renameVar_congr b ρ ρ' fun k hk => h k (by simp [Term.usesVar, hk])]
  | .record fs, ρ, ρ', h => by
    simp only [Term.renameVar,
      renameVarRow_congr fs ρ ρ' fun k hk => h k (by simp [Term.usesVar, hk])]
  | .get t _, ρ, ρ', h => by
    simp only [Term.renameVar, renameVar_congr t ρ ρ' fun k hk => h k (by simp [Term.usesVar, hk])]
  | .extend t fs, ρ, ρ', h => by
    simp only [Term.renameVar,
      renameVar_congr t ρ ρ' fun k hk => h k (by simp [Term.usesVar, hk]),
      renameVarRow_congr fs ρ ρ' fun k hk => h k (by simp [Term.usesVar, hk])]
  | .inj _ _ t, ρ, ρ', h => by
    simp only [Term.renameVar, renameVar_congr t ρ ρ' fun k hk => h k (by simp [Term.usesVar, hk])]
  | .case t as, ρ, ρ', h => by
    simp only [Term.renameVar,
      renameVar_congr t ρ ρ' fun k hk => h k (by simp [Term.usesVar, hk]),
      renameVarArms_congr as ρ ρ' fun k hk => h k (by simp [Term.usesVar, hk])]
  | .ite c a b, ρ, ρ', h => by
    simp only [Term.renameVar,
      renameVar_congr c ρ ρ' fun k hk => h k (by simp [Term.usesVar, hk]),
      renameVar_congr a ρ ρ' fun k hk => h k (by simp [Term.usesVar, hk]),
      renameVar_congr b ρ ρ' fun k hk => h k (by simp [Term.usesVar, hk])]
theorem renameVarRow_congr : ∀ (fs : List (Label × Term)) (ρ ρ' : Nat → Nat),
    (∀ k, Term.usesVarRow k fs = true → ρ k = ρ' k) →
      Term.renameVarRow ρ fs = Term.renameVarRow ρ' fs
  | [], _, _, _ => rfl
  | (_, t) :: fs, ρ, ρ', h => by
    simp only [Term.renameVarRow,
      renameVar_congr t ρ ρ' fun k hk => h k (by simp [Term.usesVarRow, hk]),
      renameVarRow_congr fs ρ ρ' fun k hk => h k (by simp [Term.usesVarRow, hk])]
theorem renameVarArms_congr : ∀ (as : List (Label × Term)) (ρ ρ' : Nat → Nat),
    (∀ k, Term.usesVarArms k as = true → ρ k = ρ' k) →
      Term.renameVarArms ρ as = Term.renameVarArms ρ' as
  | [], _, _, _ => rfl
  | (_, t) :: as, ρ, ρ', h => by
    have h' : ∀ k, Term.usesVar k t = true → upR ρ k = upR ρ' k := by
      intro k hk; cases k with
      | zero => rfl
      | succ j => simp only [upR, h j (by simp [Term.usesVarArms, hk])]
    simp only [Term.renameVarArms, renameVar_congr t _ _ h',
      renameVarArms_congr as ρ ρ' fun k hk => h k (by simp [Term.usesVarArms, hk])]
end

/-! ## Renaming moves occurrences only along the renaming -/

/-- Where an occurrence of `k` in a renamed term comes from. -/
def VarFrom (ρ : Nat → Nat) (k : Nat) (u : Nat → Bool) : Prop := ∃ j, u j = true ∧ ρ j = k

theorem VarFrom.mono {ρ : Nat → Nat} {k : Nat} {u u' : Nat → Bool}
    (hu : ∀ j, u j = true → u' j = true) : VarFrom ρ k u → VarFrom ρ k u'
  | ⟨j, hj, e⟩ => ⟨j, hu j hj, e⟩

mutual
theorem usesVar_renameVar : ∀ (t : Term) (ρ : Nat → Nat) (k : Nat),
    Term.usesVar k (Term.renameVar ρ t) = true → VarFrom ρ k (fun j => Term.usesVar j t)
  | .var i, ρ, k, h => ⟨i, by simp [Term.usesVar], by simpa [Term.renameVar, Term.usesVar] using h⟩
  | .nat _, _, _, h | .bool _, _, _, h | .bytes _, _, _, h | .digest _, _, _, h
  | .ref _, _, _, h | .refuse _ _, _, _, h => by simp [Term.renameVar, Term.usesVar] at h
  | .lam _ b, ρ, k, h => by
    obtain ⟨j, hj, e⟩ := usesVar_renameVar b (upR ρ) (k + 1) (by simpa [Term.renameVar, Term.usesVar] using h)
    cases j with
    | zero => simp [upR] at e
    | succ j => exact ⟨j, by simpa [Term.usesVar] using hj, by simpa [upR] using e⟩
  | .app f a, ρ, k, h => by
    simp only [Term.renameVar, Term.usesVar, Bool.or_eq_true] at h
    rcases h with h | h
    · exact (usesVar_renameVar f ρ k h).mono fun j hj => by simp [Term.usesVar, hj]
    · exact (usesVar_renameVar a ρ k h).mono fun j hj => by simp [Term.usesVar, hj]
  | .fix t, ρ, k, h => by
    simp only [Term.renameVar, Term.usesVar] at h
    exact (usesVar_renameVar t ρ k h).mono fun j hj => by simp [Term.usesVar, hj]
  | .prim _ a b, ρ, k, h => by
    simp only [Term.renameVar, Term.usesVar, Bool.or_eq_true] at h
    rcases h with h | h
    · exact (usesVar_renameVar a ρ k h).mono fun j hj => by simp [Term.usesVar, hj]
    · exact (usesVar_renameVar b ρ k h).mono fun j hj => by simp [Term.usesVar, hj]
  | .record fs, ρ, k, h => by
    simp only [Term.renameVar, Term.usesVar] at h
    exact (usesVarRow_renameVarRow fs ρ k h).mono fun j hj => by simp [Term.usesVar, hj]
  | .get t _, ρ, k, h => by
    simp only [Term.renameVar, Term.usesVar] at h
    exact (usesVar_renameVar t ρ k h).mono fun j hj => by simp [Term.usesVar, hj]
  | .extend t fs, ρ, k, h => by
    simp only [Term.renameVar, Term.usesVar, Bool.or_eq_true] at h
    rcases h with h | h
    · exact (usesVar_renameVar t ρ k h).mono fun j hj => by simp [Term.usesVar, hj]
    · exact (usesVarRow_renameVarRow fs ρ k h).mono fun j hj => by simp [Term.usesVar, hj]
  | .inj _ _ t, ρ, k, h => by
    simp only [Term.renameVar, Term.usesVar] at h
    exact (usesVar_renameVar t ρ k h).mono fun j hj => by simp [Term.usesVar, hj]
  | .case t as, ρ, k, h => by
    simp only [Term.renameVar, Term.usesVar, Bool.or_eq_true] at h
    rcases h with h | h
    · exact (usesVar_renameVar t ρ k h).mono fun j hj => by simp [Term.usesVar, hj]
    · exact (usesVarArms_renameVarArms as ρ k h).mono fun j hj => by simp [Term.usesVar, hj]
  | .ite c a b, ρ, k, h => by
    simp only [Term.renameVar, Term.usesVar, Bool.or_eq_true] at h
    rcases h with (h | h) | h
    · exact (usesVar_renameVar c ρ k h).mono fun j hj => by simp [Term.usesVar, hj]
    · exact (usesVar_renameVar a ρ k h).mono fun j hj => by simp [Term.usesVar, hj]
    · exact (usesVar_renameVar b ρ k h).mono fun j hj => by simp [Term.usesVar, hj]
theorem usesVarRow_renameVarRow : ∀ (fs : List (Label × Term)) (ρ : Nat → Nat) (k : Nat),
    Term.usesVarRow k (Term.renameVarRow ρ fs) = true →
      VarFrom ρ k (fun j => Term.usesVarRow j fs)
  | [], _, _, h => by simp [Term.renameVarRow, Term.usesVarRow] at h
  | (_, t) :: fs, ρ, k, h => by
    simp only [Term.renameVarRow, Term.usesVarRow, Bool.or_eq_true] at h
    rcases h with h | h
    · exact (usesVar_renameVar t ρ k h).mono fun j hj => by simp [Term.usesVarRow, hj]
    · exact (usesVarRow_renameVarRow fs ρ k h).mono fun j hj => by simp [Term.usesVarRow, hj]
theorem usesVarArms_renameVarArms : ∀ (as : List (Label × Term)) (ρ : Nat → Nat) (k : Nat),
    Term.usesVarArms k (Term.renameVarArms ρ as) = true →
      VarFrom ρ k (fun j => Term.usesVarArms j as)
  | [], _, _, h => by simp [Term.renameVarArms, Term.usesVarArms] at h
  | (_, t) :: as, ρ, k, h => by
    simp only [Term.renameVarArms, Term.usesVarArms, Bool.or_eq_true] at h
    rcases h with h | h
    · obtain ⟨j, hj, e⟩ := usesVar_renameVar t (upR ρ) (k + 1) h
      cases j with
      | zero => simp [upR] at e
      | succ j => exact ⟨j, by simp [Term.usesVarArms, hj], by simpa [upR] using e⟩
    · exact (usesVarArms_renameVarArms as ρ k h).mono fun j hj => by simp [Term.usesVarArms, hj]
end

/-- **Weakening at `x` never uses `x`.** -/
theorem usesVar_shiftAt (x : Nat) (t : Term) : Term.usesVar x (Term.renameVar (liftIdx x) t) = false := by
  cases h : Term.usesVar x (Term.renameVar (liftIdx x) t) with
  | false => rfl
  | true =>
    obtain ⟨j, _, e⟩ := usesVar_renameVar t (liftIdx x) x h
    simp only [liftIdx] at e
    split at e <;> omega

/-- **The factorisation `t ≡ t₀[π]` at any position.** -/
theorem Term.shiftAt_unshiftAt {x : Nat} {t : Term} (hu : Term.usesVar x t = false) :
    Term.renameVar (liftIdx x) (Term.renameVar (lowerIdx x) t) = t := by
  rw [renameVar_renameVar]
  conv => rhs; rw [← renameVar_id t]
  refine renameVar_congr t _ _ fun k hk => ?_
  have hkx : k ≠ x := by intro e; subst e; rw [hu] at hk; exact absurd hk (by decide)
  simp only [liftIdx, lowerIdx]
  by_cases hlt : k < x
  · simp [hlt]
  · have h2 : ¬ (k - 1 < x) := by omega
    simp only [hlt, h2, if_false]
    omega

/-! ## Typing under renaming -/

theorem upR_lookup {Γ Γ' : List Lang.Ty} (A : Lang.Ty) (ρ : Nat → Nat) (u : Nat → Bool)
    (hρ : ∀ i B, u (i + 1) = true → Γ[i]? = some B → Γ'[ρ i]? = some B) :
    ∀ i B, u i = true → (A :: Γ)[i]? = some B → (A :: Γ')[upR ρ i]? = some B
  | 0, _, _, hB => by simpa [upR] using hB
  | i + 1, B, hu, hB => by simpa [upR] using hρ i B hu (by simpa using hB)

mutual
/-- **Renaming**, restricted to the variables the term uses. -/
theorem hasType_renameVar {Δ : List Lang.Ty} : ∀ {Γ : List Lang.Ty} {t : Term} {T : Lang.Ty},
    HasType Δ Γ t T → ∀ (Γ' : List Lang.Ty) (ρ : Nat → Nat),
      (∀ i B, Term.usesVar i t = true → Γ[i]? = some B → Γ'[ρ i]? = some B) →
      HasType Δ Γ' (Term.renameVar ρ t) T
  | _, _, _, .var h, _, _, hρ => .var (hρ _ _ (by simp [Term.usesVar]) h)
  | _, _, _, .lam (A := A) (b := b) hw hb, Γ', ρ, hρ =>
    .lam hw (hasType_renameVar hb (A :: Γ') (upR ρ)
      (upR_lookup A ρ (fun i => Term.usesVar i b) fun i B hu hB =>
        hρ i B (by simpa [Term.usesVar] using hu) hB))
  | _, _, _, .app h1 h2, Γ', ρ, hρ =>
    .app (hasType_renameVar h1 Γ' ρ fun i B hu hB => hρ i B (by simp [Term.usesVar, hu]) hB)
      (hasType_renameVar h2 Γ' ρ fun i B hu hB => hρ i B (by simp [Term.usesVar, hu]) hB)
  | _, _, _, .fix h, Γ', ρ, hρ =>
    .fix (hasType_renameVar h Γ' ρ fun i B hu hB => hρ i B (by simp [Term.usesVar, hu]) hB)
  | _, _, _, .nat h, _, _, _ => .nat h
  | _, _, _, .bool, _, _, _ => .bool
  | _, _, _, .bytes h, _, _, _ => .bytes h
  | _, _, _, .digest h, _, _, _ => .digest h
  | _, _, _, .prim h1 h2, Γ', ρ, hρ =>
    .prim (hasType_renameVar h1 Γ' ρ fun i B hu hB => hρ i B (by simp [Term.usesVar, hu]) hB)
      (hasType_renameVar h2 Γ' ρ fun i B hu hB => hρ i B (by simp [Term.usesVar, hu]) hB)
  | _, _, _, .record ha h, Γ', ρ, hρ => by
    simp only [Term.renameVar]
    exact .record (by rw [renameVarRow_ascending]; exact ha)
      (renameVarFields_typed h Γ' ρ fun i B hu hB => hρ i B (by simp [Term.usesVar, hu]) hB)
  | _, _, _, .get h hl, Γ', ρ, hρ =>
    .get (hasType_renameVar h Γ' ρ fun i B hu hB => hρ i B (by simp [Term.usesVar, hu]) hB) hl
  | _, _, _, .extend h ha hfs, Γ', ρ, hρ => by
    simp only [Term.renameVar]
    exact .extend (hasType_renameVar h Γ' ρ fun i B hu hB => hρ i B (by simp [Term.usesVar, hu]) hB)
      (by rw [renameVarRow_ascending]; exact ha)
      (renameVarFields_typed hfs Γ' ρ fun i B hu hB => hρ i B (by simp [Term.usesVar, hu]) hB)
  | _, _, _, .inj hw hl h, Γ', ρ, hρ =>
    .inj hw hl (hasType_renameVar h Γ' ρ fun i B hu hB => hρ i B (by simp [Term.usesVar, hu]) hB)
  | _, _, _, .case h ha, Γ', ρ, hρ =>
    .case (hasType_renameVar h Γ' ρ fun i B hu hB => hρ i B (by simp [Term.usesVar, hu]) hB)
      (renameVarArms_typed ha Γ' ρ fun i B hu hB => hρ i B (by simp [Term.usesVar, hu]) hB)
  | _, _, _, .ite h1 h2 h3, Γ', ρ, hρ =>
    .ite (hasType_renameVar h1 Γ' ρ fun i B hu hB => hρ i B (by simp [Term.usesVar, hu]) hB)
      (hasType_renameVar h2 Γ' ρ fun i B hu hB => hρ i B (by simp [Term.usesVar, hu]) hB)
      (hasType_renameVar h3 Γ' ρ fun i B hu hB => hρ i B (by simp [Term.usesVar, hu]) hB)
  | _, _, _, .ref h, _, _, _ => .ref h
  | _, _, _, .refuse hw hn, _, _, _ => .refuse hw hn
theorem renameVarFields_typed {Δ : List Lang.Ty} : ∀ {Γ : List Lang.Ty}
    {fs : List (Label × Term)} {r : List (Label × Lang.Ty)},
    FieldsTy Δ Γ fs r → ∀ (Γ' : List Lang.Ty) (ρ : Nat → Nat),
      (∀ i B, Term.usesVarRow i fs = true → Γ[i]? = some B → Γ'[ρ i]? = some B) →
      FieldsTy Δ Γ' (Term.renameVarRow ρ fs) r
  | _, _, _, .nil, _, _, _ => .nil
  | _, _, _, .cons h hs, Γ', ρ, hρ =>
    .cons (hasType_renameVar h Γ' ρ fun i B hu hB => hρ i B (by simp [Term.usesVarRow, hu]) hB)
      (renameVarFields_typed hs Γ' ρ fun i B hu hB => hρ i B (by simp [Term.usesVarRow, hu]) hB)
theorem renameVarArms_typed {Δ : List Lang.Ty} : ∀ {Γ : List Lang.Ty}
    {as : List (Label × Term)} {r : List (Label × Lang.Ty)} {B : Lang.Ty},
    ArmsTy Δ Γ as r B → ∀ (Γ' : List Lang.Ty) (ρ : Nat → Nat),
      (∀ i C, Term.usesVarArms i as = true → Γ[i]? = some C → Γ'[ρ i]? = some C) →
      ArmsTy Δ Γ' (Term.renameVarArms ρ as) r B
  | _, _, _, _, .one (A := A) (b := b) h, Γ', ρ, hρ =>
    .one (hasType_renameVar h (A :: Γ') (upR ρ)
      (upR_lookup A ρ (fun i => Term.usesVar i b) fun i C hu hC =>
        hρ i C (by simp [Term.usesVarArms, hu]) hC))
  | _, _, _, _, .cons (A := A) (b := b) (arms := a :: as) h ha _, Γ', ρ, hρ =>
    .cons (hasType_renameVar h (A :: Γ') (upR ρ)
        (upR_lookup A ρ (fun i => Term.usesVar i b) fun i C hu hC =>
          hρ i C (by simp [Term.usesVarArms, hu]) hC))
      (renameVarArms_typed ha Γ' ρ fun i C hu hC => hρ i C
        (by show (Term.usesVar (i + 1) b || Term.usesVarArms i (a :: as)) = true
            rw [hu, Bool.or_true]) hC)
      (by simp [Term.renameVarArms])
  | _, _, _, _, .cons (arms := []) _ _ hne, _, _, _ => absurd rfl hne
end

/-- **Strengthening at any position.** -/
theorem hasType_unshiftAt {Δ Γ : List Lang.Ty} {t : Term} {T : Lang.Ty} {x : Nat}
    (h : HasType Δ Γ t T) (hu : Term.usesVar x t = false) :
    HasType Δ (Γ.eraseIdx x) (Term.renameVar (lowerIdx x) t) T := by
  refine hasType_renameVar h _ _ fun i B hi hB => ?_
  have hix : i ≠ x := by intro e; subst e; rw [hu] at hi; exact absurd hi (by decide)
  simp only [lowerIdx]
  by_cases hlt : i < x
  · rw [if_pos hlt, List.getElem?_eraseIdx_of_lt hlt]; exact hB
  · rw [if_neg hlt, List.getElem?_eraseIdx_of_ge (by omega), Nat.sub_add_cancel (by omega)]
    exact hB

/-- A closed term is typed under every library and every context. -/
theorem hasType_closed_lift {M : Term} {A : Lang.Ty} (h : HasType [] [] M A)
    (Δ' Γ : List Lang.Ty) : HasType Δ' Γ M A := by
  have h1 := relocate_typed (Δ := []) (Δ' := Δ') (f := fun i => i) (fun _ _ hA => by simp at hA) h
  rw [relocate_id] at h1
  have h2 := hasType_renameVar h1 Γ (fun i => i) fun _ _ _ hB => by simp at hB
  rwa [renameVar_id] at h2

/-! ## Holes: the `ref`s a term uses -/

/-- `t` uses ref `n` only if `t`'s sub-term-or-row does; the shape every compound case lifts. -/
abbrev RefsSub (s t : Nat → Bool) : Prop := ∀ n, s n = true → t n = true

mutual
/-- A typed term's refs are declared in its library. -/
theorem hasType_usesRef {Δ : List Lang.Ty} : ∀ {Γ : List Lang.Ty} {t : Term} {T : Lang.Ty},
    HasType Δ Γ t T → ∀ n, Term.usesRef n t = true → (Δ[n]?).isSome = true
  | _, _, _, .ref h, n, hn => by
    simp only [Term.usesRef, beq_iff_eq] at hn; subst hn; simp [h]
  | _, _, _, .var _, _, hn | _, _, _, .nat _, _, hn | _, _, _, .bool, _, hn
  | _, _, _, .bytes _, _, hn | _, _, _, .digest _, _, hn | _, _, _, .refuse _ _, _, hn => by
    simp [Term.usesRef] at hn
  | _, _, _, .lam _ h, n, hn => hasType_usesRef h n (by simpa [Term.usesRef] using hn)
  | _, _, _, .fix h, n, hn => hasType_usesRef h n (by simpa [Term.usesRef] using hn)
  | _, _, _, .get h _, n, hn => hasType_usesRef h n (by simpa [Term.usesRef] using hn)
  | _, _, _, .inj _ _ h, n, hn => hasType_usesRef h n (by simpa [Term.usesRef] using hn)
  | _, _, _, .app h1 h2, n, hn => by
    simp only [Term.usesRef, Bool.or_eq_true] at hn
    rcases hn with hn | hn
    · exact hasType_usesRef h1 n hn
    · exact hasType_usesRef h2 n hn
  | _, _, _, .prim h1 h2, n, hn => by
    simp only [Term.usesRef, Bool.or_eq_true] at hn
    rcases hn with hn | hn
    · exact hasType_usesRef h1 n hn
    · exact hasType_usesRef h2 n hn
  | _, _, _, .record _ h, n, hn => fieldsTy_usesRef h n (by simpa [Term.usesRef] using hn)
  | _, _, _, .extend h _ hfs, n, hn => by
    simp only [Term.usesRef, Bool.or_eq_true] at hn
    rcases hn with hn | hn
    · exact hasType_usesRef h n hn
    · exact fieldsTy_usesRef hfs n hn
  | _, _, _, .case h ha, n, hn => by
    simp only [Term.usesRef, Bool.or_eq_true] at hn
    rcases hn with hn | hn
    · exact hasType_usesRef h n hn
    · exact armsTy_usesRef ha n hn
  | _, _, _, .ite h1 h2 h3, n, hn => by
    simp only [Term.usesRef, Bool.or_eq_true] at hn
    rcases hn with (hn | hn) | hn
    · exact hasType_usesRef h1 n hn
    · exact hasType_usesRef h2 n hn
    · exact hasType_usesRef h3 n hn
theorem fieldsTy_usesRef {Δ : List Lang.Ty} : ∀ {Γ : List Lang.Ty}
    {fs : List (Label × Term)} {r : List (Label × Lang.Ty)},
    FieldsTy Δ Γ fs r → ∀ n, Term.usesRefRow n fs = true → (Δ[n]?).isSome = true
  | _, _, _, .nil, _, hn => by simp [Term.usesRefRow] at hn
  | _, _, _, .cons h hs, n, hn => by
    simp only [Term.usesRefRow, Bool.or_eq_true] at hn
    rcases hn with hn | hn
    · exact hasType_usesRef h n hn
    · exact fieldsTy_usesRef hs n hn
theorem armsTy_usesRef {Δ : List Lang.Ty} : ∀ {Γ : List Lang.Ty}
    {as : List (Label × Term)} {r : List (Label × Lang.Ty)} {B : Lang.Ty},
    ArmsTy Δ Γ as r B → ∀ n, Term.usesRefRow n as = true → (Δ[n]?).isSome = true
  | _, _, _, _, .one h, n, hn => by
    simp only [Term.usesRefRow, Bool.or_eq_true, Bool.false_eq_true, or_false] at hn
    exact hasType_usesRef h n hn
  | _, _, _, _, .cons h ha _, n, hn => by
    simp only [Term.usesRefRow, Bool.or_eq_true] at hn
    rcases hn with hn | hn
    · exact hasType_usesRef h n hn
    · exact armsTy_usesRef ha n hn
end

mutual
/-- Renaming variables leaves the refs alone. -/
theorem usesRef_renameVar (n : Nat) : ∀ (t : Term) (ρ : Nat → Nat),
    Term.usesRef n (Term.renameVar ρ t) = Term.usesRef n t
  | .var _, _ | .nat _, _ | .bool _, _ | .bytes _, _ | .digest _, _ | .ref _, _
  | .refuse _ _, _ => rfl
  | .lam _ b, ρ => by simp only [Term.renameVar, Term.usesRef, usesRef_renameVar n b]
  | .app f a, ρ => by simp only [Term.renameVar, Term.usesRef, usesRef_renameVar n f, usesRef_renameVar n a]
  | .fix t, ρ => by simp only [Term.renameVar, Term.usesRef, usesRef_renameVar n t]
  | .prim _ a b, ρ => by simp only [Term.renameVar, Term.usesRef, usesRef_renameVar n a, usesRef_renameVar n b]
  | .record fs, ρ => by simp only [Term.renameVar, Term.usesRef, usesRefRow_renameVarRow n fs]
  | .get t _, ρ => by simp only [Term.renameVar, Term.usesRef, usesRef_renameVar n t]
  | .extend t fs, ρ => by
    simp only [Term.renameVar, Term.usesRef, usesRef_renameVar n t, usesRefRow_renameVarRow n fs]
  | .inj _ _ t, ρ => by simp only [Term.renameVar, Term.usesRef, usesRef_renameVar n t]
  | .case t as, ρ => by
    simp only [Term.renameVar, Term.usesRef, usesRef_renameVar n t, usesRefRow_renameVarArms n as]
  | .ite c a b, ρ => by
    simp only [Term.renameVar, Term.usesRef, usesRef_renameVar n c, usesRef_renameVar n a,
      usesRef_renameVar n b]
theorem usesRefRow_renameVarRow (n : Nat) : ∀ (fs : List (Label × Term)) (ρ : Nat → Nat),
    Term.usesRefRow n (Term.renameVarRow ρ fs) = Term.usesRefRow n fs
  | [], _ => rfl
  | (_, t) :: fs, ρ => by
    simp only [Term.renameVarRow, Term.usesRefRow, usesRef_renameVar n t, usesRefRow_renameVarRow n fs]
theorem usesRefRow_renameVarArms (n : Nat) : ∀ (as : List (Label × Term)) (ρ : Nat → Nat),
    Term.usesRefRow n (Term.renameVarArms ρ as) = Term.usesRefRow n as
  | [], _ => rfl
  | (_, t) :: as, ρ => by
    simp only [Term.renameVarArms, Term.usesRefRow, usesRef_renameVar n t, usesRefRow_renameVarArms n as]
end

/-- Where a ref surviving `fillRefs σ` comes from: an unfilled ref of the term, or a ref of the
filling of one of its refs. -/
def FillOrigin (σ : Nat → Option Term) (n : Nat) (u : Nat → Bool) : Prop :=
  (u n = true ∧ σ n = none) ∨ ∃ m M, u m = true ∧ σ m = some M ∧ Term.usesRef n M = true

theorem FillOrigin.mono {σ : Nat → Option Term} {n : Nat} {u u' : Nat → Bool}
    (hu : RefsSub u u') : FillOrigin σ n u → FillOrigin σ n u'
  | .inl ⟨h1, h2⟩ => .inl ⟨hu n h1, h2⟩
  | .inr ⟨m, M, h1, h2, h3⟩ => .inr ⟨m, M, hu m h1, h2, h3⟩

mutual
theorem usesRef_fillRefs (σ : Nat → Option Term) (n : Nat) : ∀ t : Term,
    Term.usesRef n (Term.fillRefs σ t) = true → FillOrigin σ n (fun m => Term.usesRef m t)
  | .ref i, h => by
    cases hs : σ i with
    | none =>
      simp only [Term.fillRefs, hs, Option.getD_none, Term.usesRef, beq_iff_eq] at h
      subst h; exact .inl ⟨by simp [Term.usesRef], hs⟩
    | some M =>
      simp only [Term.fillRefs, hs, Option.getD_some] at h
      exact .inr ⟨i, M, by simp [Term.usesRef], hs, h⟩
  | .var _, h | .nat _, h | .bool _, h | .bytes _, h | .digest _, h | .refuse _ _, h => by
    simp [Term.fillRefs, Term.usesRef] at h
  | .lam _ b, h => (usesRef_fillRefs σ n b (by simpa [Term.fillRefs, Term.usesRef] using h)).mono
      fun m hm => by simp [Term.usesRef, hm]
  | .fix b, h => (usesRef_fillRefs σ n b (by simpa [Term.fillRefs, Term.usesRef] using h)).mono
      fun m hm => by simp [Term.usesRef, hm]
  | .get b _, h => (usesRef_fillRefs σ n b (by simpa [Term.fillRefs, Term.usesRef] using h)).mono
      fun m hm => by simp [Term.usesRef, hm]
  | .inj _ _ b, h => (usesRef_fillRefs σ n b (by simpa [Term.fillRefs, Term.usesRef] using h)).mono
      fun m hm => by simp [Term.usesRef, hm]
  | .app f a, h => by
    simp only [Term.fillRefs, Term.usesRef, Bool.or_eq_true] at h
    rcases h with h | h
    · exact (usesRef_fillRefs σ n f h).mono fun m hm => by simp [Term.usesRef, hm]
    · exact (usesRef_fillRefs σ n a h).mono fun m hm => by simp [Term.usesRef, hm]
  | .prim _ a b, h => by
    simp only [Term.fillRefs, Term.usesRef, Bool.or_eq_true] at h
    rcases h with h | h
    · exact (usesRef_fillRefs σ n a h).mono fun m hm => by simp [Term.usesRef, hm]
    · exact (usesRef_fillRefs σ n b h).mono fun m hm => by simp [Term.usesRef, hm]
  | .record fs, h => (usesRefRow_fillRefsRow σ n fs (by simpa [Term.fillRefs, Term.usesRef] using h)).mono
      fun m hm => by simp [Term.usesRef, hm]
  | .extend t fs, h => by
    simp only [Term.fillRefs, Term.usesRef, Bool.or_eq_true] at h
    rcases h with h | h
    · exact (usesRef_fillRefs σ n t h).mono fun m hm => by simp [Term.usesRef, hm]
    · exact (usesRefRow_fillRefsRow σ n fs h).mono fun m hm => by simp [Term.usesRef, hm]
  | .case t fs, h => by
    simp only [Term.fillRefs, Term.usesRef, Bool.or_eq_true] at h
    rcases h with h | h
    · exact (usesRef_fillRefs σ n t h).mono fun m hm => by simp [Term.usesRef, hm]
    · exact (usesRefRow_fillRefsRow σ n fs h).mono fun m hm => by simp [Term.usesRef, hm]
  | .ite c a b, h => by
    simp only [Term.fillRefs, Term.usesRef, Bool.or_eq_true] at h
    rcases h with (h | h) | h
    · exact (usesRef_fillRefs σ n c h).mono fun m hm => by simp [Term.usesRef, hm]
    · exact (usesRef_fillRefs σ n a h).mono fun m hm => by simp [Term.usesRef, hm]
    · exact (usesRef_fillRefs σ n b h).mono fun m hm => by simp [Term.usesRef, hm]
theorem usesRefRow_fillRefsRow (σ : Nat → Option Term) (n : Nat) : ∀ fs : List (Label × Term),
    Term.usesRefRow n (Term.fillRefsRow σ fs) = true →
      FillOrigin σ n (fun m => Term.usesRefRow m fs)
  | [], h => by simp [Term.fillRefsRow, Term.usesRefRow] at h
  | (_, t) :: fs, h => by
    simp only [Term.fillRefsRow, Term.usesRefRow, Bool.or_eq_true] at h
    rcases h with h | h
    · exact (usesRef_fillRefs σ n t h).mono fun m hm => by simp [Term.usesRefRow, hm]
    · exact (usesRefRow_fillRefsRow σ n fs h).mono fun m hm => by simp [Term.usesRefRow, hm]
end

/-! ## Filling preserves typing -/

mutual
/-- **Filling the declared refs preserves typing**: the library `Δ` gives every declared ref
its declared type `τ`; a filled ref is replaced by a filling of that type; an unfilled one keeps
its type in `Δ'`. -/
theorem fillRefs_typed {Δ Δ' : List Lang.Ty}
    (τ : Nat → Option Lang.Ty) (σ : Nat → Option Term)
    (hΔ : ∀ n A, τ n = some A → Δ[n]? = some A)
    (hσ : ∀ n M A, σ n = some M → τ n = some A → ∀ Γ : List Lang.Ty, HasType Δ' Γ M A)
    (hΔ' : ∀ n A, σ n = none → τ n = some A → Δ'[n]? = some A) : ∀ {Γ : List Lang.Ty} {t : Term} {T : Lang.Ty}, HasType Δ Γ t T →
    (∀ n, Term.usesRef n t = true → (τ n).isSome = true) →
      HasType Δ' Γ (Term.fillRefs σ t) T
  | Γ, _, _, .ref (i := i) h, hR => by
    obtain ⟨A, hA⟩ := Option.isSome_iff_exists.1 (hR i (by simp [Term.usesRef]))
    have hT := hΔ i A hA
    rw [h] at hT
    cases hT
    cases hs : σ i with
    | none =>
      simp only [Term.fillRefs, hs, Option.getD_none]
      exact .ref (hΔ' i _ hs hA)
    | some M =>
      simp only [Term.fillRefs, hs, Option.getD_some]
      exact hσ i M _ hs hA Γ
  | _, _, _, .var h, _ => .var h
  | _, _, _, .lam hw hb, hR =>
    .lam hw (fillRefs_typed τ σ hΔ hσ hΔ' hb fun n hn => hR n (by simp [Term.usesRef, hn]))
  | _, _, _, .app h1 h2, hR =>
    .app (fillRefs_typed τ σ hΔ hσ hΔ' h1 fun n hn => hR n (by simp [Term.usesRef, hn]))
      (fillRefs_typed τ σ hΔ hσ hΔ' h2 fun n hn => hR n (by simp [Term.usesRef, hn]))
  | _, _, _, .fix h, hR => .fix (fillRefs_typed τ σ hΔ hσ hΔ' h fun n hn => hR n (by simp [Term.usesRef, hn]))
  | _, _, _, .nat h, _ => .nat h
  | _, _, _, .bool, _ => .bool
  | _, _, _, .bytes h, _ => .bytes h
  | _, _, _, .digest h, _ => .digest h
  | _, _, _, .prim h1 h2, hR =>
    .prim (fillRefs_typed τ σ hΔ hσ hΔ' h1 fun n hn => hR n (by simp [Term.usesRef, hn]))
      (fillRefs_typed τ σ hΔ hσ hΔ' h2 fun n hn => hR n (by simp [Term.usesRef, hn]))
  | _, _, _, .record ha h, hR => by
    simp only [Term.fillRefs]
    exact .record (by rw [fillRefsRow_ascending]; exact ha)
      (fillRefsFields_typed τ σ hΔ hσ hΔ' h fun n hn => hR n (by simp [Term.usesRef, hn]))
  | _, _, _, .get h hl, hR => .get (fillRefs_typed τ σ hΔ hσ hΔ' h fun n hn => hR n (by simp [Term.usesRef, hn])) hl
  | _, _, _, .extend h ha hfs, hR => by
    simp only [Term.fillRefs]
    exact .extend (fillRefs_typed τ σ hΔ hσ hΔ' h fun n hn => hR n (by simp [Term.usesRef, hn]))
      (by rw [fillRefsRow_ascending]; exact ha)
      (fillRefsFields_typed τ σ hΔ hσ hΔ' hfs fun n hn => hR n (by simp [Term.usesRef, hn]))
  | _, _, _, .inj hw hl h, hR =>
    .inj hw hl (fillRefs_typed τ σ hΔ hσ hΔ' h fun n hn => hR n (by simp [Term.usesRef, hn]))
  | _, _, _, .case h ha, hR =>
    .case (fillRefs_typed τ σ hΔ hσ hΔ' h fun n hn => hR n (by simp [Term.usesRef, hn]))
      (fillRefsArms_typed τ σ hΔ hσ hΔ' ha fun n hn => hR n (by simp [Term.usesRef, hn]))
  | _, _, _, .ite h1 h2 h3, hR =>
    .ite (fillRefs_typed τ σ hΔ hσ hΔ' h1 fun n hn => hR n (by simp [Term.usesRef, hn]))
      (fillRefs_typed τ σ hΔ hσ hΔ' h2 fun n hn => hR n (by simp [Term.usesRef, hn]))
      (fillRefs_typed τ σ hΔ hσ hΔ' h3 fun n hn => hR n (by simp [Term.usesRef, hn]))
  | _, _, _, .refuse hw hn, _ => .refuse hw hn
theorem fillRefsFields_typed {Δ Δ' : List Lang.Ty}
    (τ : Nat → Option Lang.Ty) (σ : Nat → Option Term)
    (hΔ : ∀ n A, τ n = some A → Δ[n]? = some A)
    (hσ : ∀ n M A, σ n = some M → τ n = some A → ∀ Γ : List Lang.Ty, HasType Δ' Γ M A)
    (hΔ' : ∀ n A, σ n = none → τ n = some A → Δ'[n]? = some A) : ∀ {Γ : List Lang.Ty} {fs : List (Label × Term)}
    {r : List (Label × Lang.Ty)}, FieldsTy Δ Γ fs r →
    (∀ n, Term.usesRefRow n fs = true → (τ n).isSome = true) →
      FieldsTy Δ' Γ (Term.fillRefsRow σ fs) r
  | _, _, _, .nil, _ => .nil
  | _, _, _, .cons h hs, hR =>
    .cons (fillRefs_typed τ σ hΔ hσ hΔ' h fun n hn => hR n (by simp [Term.usesRefRow, hn]))
      (fillRefsFields_typed τ σ hΔ hσ hΔ' hs fun n hn => hR n (by simp [Term.usesRefRow, hn]))
theorem fillRefsArms_typed {Δ Δ' : List Lang.Ty}
    (τ : Nat → Option Lang.Ty) (σ : Nat → Option Term)
    (hΔ : ∀ n A, τ n = some A → Δ[n]? = some A)
    (hσ : ∀ n M A, σ n = some M → τ n = some A → ∀ Γ : List Lang.Ty, HasType Δ' Γ M A)
    (hΔ' : ∀ n A, σ n = none → τ n = some A → Δ'[n]? = some A) : ∀ {Γ : List Lang.Ty} {as : List (Label × Term)}
    {r : List (Label × Lang.Ty)} {B : Lang.Ty}, ArmsTy Δ Γ as r B →
    (∀ n, Term.usesRefRow n as = true → (τ n).isSome = true) →
      ArmsTy Δ' Γ (Term.fillRefsRow σ as) r B
  | _, _, _, _, .one h, hR =>
    .one (fillRefs_typed τ σ hΔ hσ hΔ' h fun n hn => hR n (by simp [Term.usesRefRow, hn]))
  | _, _, _, _, .cons (b := b) (arms := a :: as) h ha _, hR =>
    .cons (fillRefs_typed τ σ hΔ hσ hΔ' h fun n hn => hR n (by simp [Term.usesRefRow, hn]))
      (fillRefsArms_typed τ σ hΔ hσ hΔ' ha fun n hn => hR n
        (by show (Term.usesRef n b || Term.usesRefRow n (a :: as)) = true
            rw [hn, Bool.or_true]))
      (by simp [Term.fillRefsRow])
  | _, _, _, _, .cons (arms := []) _ _ hne, _ => absurd rfl hne
end


/-! ## The holes' declarations -/

theorem tyOf_some {Ω : List (HoleDecl (List Lang.Ty) Lang.Ty)} {n : Nat} {A : Lang.Ty}
    (h : tyOf Ω n = some A) : ∃ d ∈ Ω, d.name = n ∧ d.ty = A := by
  unfold tyOf at h
  simp only [Option.map_eq_some_iff] at h
  obtain ⟨d, hd, ht⟩ := h
  exact ⟨d, List.mem_of_find?_eq_some hd, by simpa using List.find?_some hd, ht⟩

/-- Removing declarations of OTHER names (or none of name `n`) leaves `n`'s type alone. -/
theorem tyOf_filter (p : HoleDecl (List Lang.Ty) Lang.Ty → Bool) (n : Nat) :
    ∀ Ω : List (HoleDecl (List Lang.Ty) Lang.Ty), (∀ d ∈ Ω, d.name = n → p d = true) →
      tyOf (Ω.filter p) n = tyOf Ω n
  | [], _ => rfl
  | d :: Ω, h => by
    have ih := tyOf_filter p n Ω fun d' hd' => h d' (List.mem_cons_of_mem _ hd')
    by_cases hn : d.name = n
    · have hp := h d List.mem_cons_self hn
      simp only [tyOf, List.filter_cons_of_pos hp, List.find?_cons, hn, beq_self_eq_true]
    · have hb : (d.name == n) = false := by simp [hn]
      by_cases hp : p d = true
      · simp only [tyOf, List.filter_cons_of_pos hp, List.find?_cons, hb] at ih ⊢
        exact ih
      · simp only [tyOf, List.filter_cons_of_neg hp, List.find?_cons, hb] at ih ⊢
        exact ih

theorem lt_holeBound : ∀ {Ω : List (HoleDecl (List Lang.Ty) Lang.Ty)} {d : HoleDecl (List Lang.Ty) Lang.Ty},
    d ∈ Ω → d.name < holeBound Ω
  | d' :: Ω, d, h => by
    simp only [holeBound, List.foldr_cons] at *
    rcases List.mem_cons.1 h with rfl | h
    · omega
    · have := lt_holeBound h; simp only [holeBound] at this; omega

theorem ΔOf_getElem? {Ω : List (HoleDecl (List Lang.Ty) Lang.Ty)} {n : Nat} {A : Lang.Ty}
    (h : tyOf Ω n = some A) : (ΔOf Ω)[n]? = some A := by
  obtain ⟨d, hd, hn, _⟩ := tyOf_some h
  have hlt : n < holeBound Ω := hn ▸ lt_holeBound hd
  simp [ΔOf, hlt, h]

theorem ΔOf_nil : ΔOf [] = [] := rfl

/-! ## The typing judgment of the instance -/

/-- Every `ref` the term uses is a declared hole. -/
def RefsDeclared (Ω : List (HoleDecl (List Lang.Ty) Lang.Ty)) (t : Term) : Prop :=
  ∀ n, Term.usesRef n t = true → (tyOf Ω n).isSome = true

/-- `Ω; Γ ⊢ t : T` for `Lang.Term`: every hole's context empty (a `ref` is a closed package
reference: it has no local context to substitute), every ref declared, and `t` typed by
`Lang.HasType` with the holes as the package types. -/
def LangHasTy (Ω : List (HoleDecl (List Lang.Ty) Lang.Ty)) (Γ : List Lang.Ty) (t : Term)
    (T : Lang.Ty) : Prop :=
  (∀ d ∈ Ω, d.ctx = []) ∧ RefsDeclared Ω t ∧ HasType (ΔOf Ω) Γ t T

/-- A term typed in the empty meta-context uses no ref. -/
theorem refsDeclared_nil {t : Term} (h : RefsDeclared [] t) (n : Nat) : Term.usesRef n t = false := by
  cases hn : Term.usesRef n t with
  | false => rfl
  | true => have := h n hn; simp [tyOf] at this

theorem langHasTy_nil_iff {Γ : List Lang.Ty} {t : Term} {T : Lang.Ty} :
    LangHasTy [] Γ t T ↔ HasType [] Γ t T := by
  constructor
  · exact fun h => h.2.2
  · intro h
    refine ⟨fun d hd => by simp at hd, fun n hn => ?_, h⟩
    have := hasType_usesRef h n hn
    simp at this

/-! ## The laws -/

/-- **The deployed term language is a lawful `Calculus`** (with closed holes). -/
theorem langLaws : CalculusLaws langData LangHasTy where
  msubst_lemma := by
    intro Ω Γ P T σ hP hfill
    obtain ⟨hcl, hR, hT⟩ := hP
    have hτf : ∀ n, σ n = none →
        tyOf (Ω.filter fun d => (σ d.name).isNone) n = tyOf Ω n := fun n hn =>
      tyOf_filter _ n Ω fun d _ hd => by rw [hd, hn]; rfl
    have hM : ∀ n M A, σ n = some M → tyOf Ω n = some A → LangHasTy [] [] M A := by
      intro n M A hs ht
      obtain ⟨d, hd, hn, hA⟩ := tyOf_some ht
      have := hfill d hd M (by rw [hn]; exact hs)
      rw [hcl d hd, hA] at this
      exact this
    refine ⟨fun d hd => hcl d (List.mem_filter.1 hd).1, ?_, ?_⟩
    · intro n hn
      rcases usesRef_fillRefs σ n P hn with ⟨h1, h2⟩ | ⟨m, M, h1, h2, h3⟩
      · exact (congrArg Option.isSome (hτf n h2)).trans (hR n h1)
      · obtain ⟨A, hA⟩ := Option.isSome_iff_exists.1 (hR m h1)
        have := refsDeclared_nil (hM m M A h2 hA).2.1 n
        rw [h3] at this; cases this
    · exact fillRefs_typed (tyOf Ω) σ (fun n A h => ΔOf_getElem? h)
        (fun n M A hs ht Γ' => hasType_closed_lift (hM n M A hs ht).2.2 _ Γ')
        (fun n A hs ht => ΔOf_getElem? ((hτf n hs).trans ht)) hT hR
  check_sound := by
    intro Ψ M A h
    exact langHasTy_nil_iff.2 (Lang.infer_sound (of_decide_eq_true h))
  check_complete := by
    intro Ψ M A h
    exact decide_eq_true (Lang.infer_complete (langHasTy_nil_iff.1 h))
  strengthen_lemma := by
    intro Ψ M A x h hu
    exact langHasTy_nil_iff.2 (hasType_unshiftAt (langHasTy_nil_iff.1 h) hu)
  strengthen_factor := Term.shiftAt_unshiftAt
  weaken_avoids := fun {_ M _ x} _ => usesVar_shiftAt x M
  hasTy_var := fun h => langHasTy_nil_iff.2 (.var h)
  uses_var := by intro x; simp [langData, Term.usesVar]

/-! ## The reach: a Lang template's holes have no hypotheses -/

/-- **The boundary of the closed-hole fragment.** Every hole of a template typed by `LangHasTy`
has the empty context (the definition's first conjunct: a Lang `ref` is a closed package reference),
so no hole has a token-backed hypothesis (`Iface.hyps_real` asks each hypothesis to be a real
variable of the hole's context). Three closure paths are therefore EMPTY on every Lang template:
the `strengthening` outcome (`repairSelected`'s `D.uses` branch), the alternative-by-hypothesis
outcome, and hypothesis-derived supports (`effSupports`' second summand). They are exercised only
by the CMTT instance (`cmttLaws`). -/
theorem langTemplate_no_hyps {E : Type} (tpl : Template langData E)
    (h : Template.Typed tpl LangHasTy) : ∀ I ∈ tpl.Ω, I.hyps = [] := by
  intro I hI
  have hc : I.ctx = [] := h.1 I.decl (List.mem_map.2 ⟨I, hI, rfl⟩)
  apply List.eq_nil_iff_forall_not_mem.2
  intro x hx
  have := I.hyps_real x hx
  rw [hc] at this
  simp [langData] at this

/-! ## Toys -/

/-- The instance's strengthening is the real one: `t ≡ t₀[π]` with `t₀ ≠ t`. -/
theorem lang_strengthen_toy :
    langData.strengthen 1 (.app (.var 0) (.var 2)) = (.app (.var 0) (.var 1) : Term) ∧
      langData.weaken 1 (langData.strengthen 1 (.app (.var 0) (.var 2))) =
        (.app (.var 0) (.var 2) : Term) :=
  ⟨rfl, rfl⟩

/-- The hole `0 :: [· ⊢ nat → nat]`. -/
private def natHole : HoleDecl (List Lang.Ty) Lang.Ty := ⟨0, [], .fn .nat .nat⟩

/-- The template `(ref 0) 3`. -/
private def natTemplate : Term := .app (.ref 0) (.nat 3)

/-- The filling `ref 0 := λx. x`. -/
private def natFill : Nat → Option Term := fun n => if n = 0 then some (.lam .nat (.var 0)) else none

/-- The template is typed WITH the hole and NOT without it; filled, it computes to `(λx.x) 3` and
is typed with the hole gone, through `langLaws.msubst_lemma`. -/
theorem lang_template_toy :
    LangHasTy [natHole] [] natTemplate .nat ∧
      ¬ LangHasTy [] [] natTemplate .nat ∧
      langData.msubst natFill natTemplate = .app (.lam .nat (.var 0)) (.nat 3) ∧
      LangHasTy [] [] (langData.msubst natFill natTemplate) .nat := by
  have hT : LangHasTy [natHole] [] natTemplate .nat := by
    refine ⟨fun d hd => by simp [natHole] at hd; subst hd; rfl, fun n hn => ?_, ?_⟩
    · simp [natTemplate, Term.usesRef] at hn
      subst hn; rfl
    · exact .app (.ref rfl) (.nat (by decide))
  refine ⟨hT, fun h => ?_, rfl, ?_⟩
  · have := h.2.1 0 (by simp [natTemplate, Term.usesRef])
    simp [tyOf] at this
  · have := langLaws.msubst_lemma (Ω := [natHole]) (Γ := []) (P := natTemplate) (T := .nat) natFill hT
      (fun d hd M hM => by
        simp only [List.mem_singleton] at hd
        subst hd
        simp only [natHole, natFill, if_true] at hM
        injection hM with hM
        subst hM
        exact langHasTy_nil_iff.2 (.lam (by decide) (.var rfl)))
    simpa [natHole, natFill] using this

end Nanodregg.Lang.Contextual
