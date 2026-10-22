/-
# Lang.Proofs.Subst — renaming and substitution preserve the deployed typing judgment

Binder-aware renaming and strengthening for every contextual Lang term (`hasType_renameVar(_live)`,
`hasType_unshiftAt(_live)`, `Term.shiftAt_unshiftAt`), then ordinary substitution (`substList_typed` and the
capture teeth). Subject: `Lang.Subst`'s `renameVar`/`substVar`/`substList`, which the live loader runs
(`Lang.LiveHoles`: `Term.renameVar (lowerIdx x)` in `selectHole`). No new assumption is attached to a landed
theorem.
-/
import Lang.Subst
import Lang.Proofs.Check
import Lang.Proofs.Index

namespace Nanodregg.Lang

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
  | .hole n σ => by simp only [Term.renameVar, renameVarList_renameVarList ρ ρ' σ]
theorem renameVarList_renameVarList (ρ ρ' : Nat → Nat) : ∀ fs : List Term,
    Term.renameVarList ρ (Term.renameVarList ρ' fs) = Term.renameVarList (fun i => ρ (ρ' i)) fs
  | [] => rfl
  | t :: fs => by
    simp only [Term.renameVarList, renameVar_renameVar ρ ρ' t, renameVarList_renameVarList ρ ρ' fs]
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
  | .hole n σ => by simp only [Term.renameVar, renameVarList_id σ]
theorem renameVarList_id : ∀ fs : List Term, Term.renameVarList (fun i => i) fs = fs
  | [] => rfl
  | t :: fs => by simp only [Term.renameVarList, renameVar_id t, renameVarList_id fs]
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
  | .hole n σ, ρ, ρ', h => by
    simp only [Term.renameVar,
      renameVarList_congr σ ρ ρ' fun k hk => h k (by simp [Term.usesVar, hk])]
theorem renameVarList_congr : ∀ (fs : List Term) (ρ ρ' : Nat → Nat),
    (∀ k, Term.usesVarList k fs = true → ρ k = ρ' k) →
      Term.renameVarList ρ fs = Term.renameVarList ρ' fs
  | [], _, _, _ => rfl
  | t :: fs, ρ, ρ', h => by
    simp only [Term.renameVarList,
      renameVar_congr t ρ ρ' fun k hk => h k (by simp [Term.usesVarList, hk]),
      renameVarList_congr fs ρ ρ' fun k hk => h k (by simp [Term.usesVarList, hk])]
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
  | .hole n σ, ρ, k, h => by
    exact (usesVarList_renameVarList σ ρ k h).mono fun j hj => hj
theorem usesVarList_renameVarList : ∀ (fs : List Term) (ρ : Nat → Nat) (k : Nat),
    Term.usesVarList k (Term.renameVarList ρ fs) = true →
      VarFrom ρ k (fun j => Term.usesVarList j fs)
  | [], _, _, h => by simp [Term.renameVarList, Term.usesVarList] at h
  | t :: fs, ρ, k, h => by
    simp only [Term.renameVarList, Term.usesVarList, Bool.or_eq_true] at h
    rcases h with h | h
    · exact (usesVar_renameVar t ρ k h).mono fun j hj => by simp [Term.usesVarList, hj]
    · exact (usesVarList_renameVarList fs ρ k h).mono fun j hj => by simp [Term.usesVarList, hj]
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
theorem hasType_renameVar_live {Δ : List Lang.Ty} {Ω : HoleSignature} : ∀ {Γ : List Lang.Ty} {t : Term} {T : Lang.Ty},
    HasType (Ω := Ω) Δ Γ t T → ∀ (Γ' : List Lang.Ty) (ρ : Nat → Nat),
      (∀ i B, Term.usesVar i t = true → Γ[i]? = some B → Γ'[ρ i]? = some B) →
      HasType (Ω := Ω) Δ Γ' (Term.renameVar ρ t) T
  | _, _, _, .var h, _, _, hρ => .var (hρ _ _ (by simp [Term.usesVar]) h)
  | _, _, _, .lam (A := A) (b := b) hw hb, Γ', ρ, hρ =>
    .lam hw (hasType_renameVar_live hb (A :: Γ') (upR ρ)
      (upR_lookup A ρ (fun i => Term.usesVar i b) fun i B hu hB =>
        hρ i B (by simpa [Term.usesVar] using hu) hB))
  | _, _, _, .app h1 h2, Γ', ρ, hρ =>
    .app (hasType_renameVar_live h1 Γ' ρ fun i B hu hB => hρ i B (by simp [Term.usesVar, hu]) hB)
      (hasType_renameVar_live h2 Γ' ρ fun i B hu hB => hρ i B (by simp [Term.usesVar, hu]) hB)
  | _, _, _, .fix h, Γ', ρ, hρ =>
    .fix (hasType_renameVar_live h Γ' ρ fun i B hu hB => hρ i B (by simp [Term.usesVar, hu]) hB)
  | _, _, _, .nat h, _, _, _ => .nat h
  | _, _, _, .bool, _, _, _ => .bool
  | _, _, _, .bytes h, _, _, _ => .bytes h
  | _, _, _, .digest h, _, _, _ => .digest h
  | _, _, _, .prim h1 h2, Γ', ρ, hρ =>
    .prim (hasType_renameVar_live h1 Γ' ρ fun i B hu hB => hρ i B (by simp [Term.usesVar, hu]) hB)
      (hasType_renameVar_live h2 Γ' ρ fun i B hu hB => hρ i B (by simp [Term.usesVar, hu]) hB)
  | _, _, _, .record ha h, Γ', ρ, hρ => by
    simp only [Term.renameVar]
    exact .record (by rw [renameVarRow_ascending]; exact ha)
      (renameVarFields_typed_live h Γ' ρ fun i B hu hB => hρ i B (by simp [Term.usesVar, hu]) hB)
  | _, _, _, .get h hl, Γ', ρ, hρ =>
    .get (hasType_renameVar_live h Γ' ρ fun i B hu hB => hρ i B (by simp [Term.usesVar, hu]) hB) hl
  | _, _, _, .extend h ha hfs, Γ', ρ, hρ => by
    simp only [Term.renameVar]
    exact .extend (hasType_renameVar_live h Γ' ρ fun i B hu hB => hρ i B (by simp [Term.usesVar, hu]) hB)
      (by rw [renameVarRow_ascending]; exact ha)
      (renameVarFields_typed_live hfs Γ' ρ fun i B hu hB => hρ i B (by simp [Term.usesVar, hu]) hB)
  | _, _, _, .inj hw hl h, Γ', ρ, hρ =>
    .inj hw hl (hasType_renameVar_live h Γ' ρ fun i B hu hB => hρ i B (by simp [Term.usesVar, hu]) hB)
  | _, _, _, .case h ha, Γ', ρ, hρ =>
    .case (hasType_renameVar_live h Γ' ρ fun i B hu hB => hρ i B (by simp [Term.usesVar, hu]) hB)
      (renameVarArms_typed_live ha Γ' ρ fun i B hu hB => hρ i B (by simp [Term.usesVar, hu]) hB)
  | _, _, _, .ite h1 h2 h3, Γ', ρ, hρ =>
    .ite (hasType_renameVar_live h1 Γ' ρ fun i B hu hB => hρ i B (by simp [Term.usesVar, hu]) hB)
      (hasType_renameVar_live h2 Γ' ρ fun i B hu hB => hρ i B (by simp [Term.usesVar, hu]) hB)
      (hasType_renameVar_live h3 Γ' ρ fun i B hu hB => hρ i B (by simp [Term.usesVar, hu]) hB)
  | _, _, _, .ref h, _, _, _ => .ref h
  | _, _, _, .refuse hw hn, _, _, _ => .refuse hw hn
  | _, _, _, .hole hd hs, Γ', ρ, hρ =>
    .hole hd (renameVarSubst_typed hs Γ' ρ hρ)
theorem renameVarSubst_typed {Δ : List Lang.Ty} {Ω : HoleSignature} :
    ∀ {Γ : List Lang.Ty} {σ : List Term} {Ψ : List Lang.Ty},
      SubstTy Δ Γ σ Ψ Ω → ∀ (Γ' : List Lang.Ty) (ρ : Nat → Nat),
        (∀ i B, Term.usesVarList i σ = true → Γ[i]? = some B → Γ'[ρ i]? = some B) →
        SubstTy Δ Γ' (Term.renameVarList ρ σ) Ψ Ω
  | _, _, _, .nil, _, _, _ => .nil
  | _, _, _, .cons h hs, Γ', ρ, hρ =>
    .cons (hasType_renameVar_live h Γ' ρ fun i B hu hB =>
      hρ i B (by simp [Term.usesVarList, hu]) hB)
      (renameVarSubst_typed hs Γ' ρ fun i B hu hB =>
        hρ i B (by simp [Term.usesVarList, hu]) hB)
theorem renameVarFields_typed_live {Δ : List Lang.Ty} {Ω : HoleSignature} : ∀ {Γ : List Lang.Ty}
    {fs : List (Label × Term)} {r : List (Label × Lang.Ty)},
    FieldsTy (Ω := Ω) Δ Γ fs r → ∀ (Γ' : List Lang.Ty) (ρ : Nat → Nat),
      (∀ i B, Term.usesVarRow i fs = true → Γ[i]? = some B → Γ'[ρ i]? = some B) →
      FieldsTy (Ω := Ω) Δ Γ' (Term.renameVarRow ρ fs) r
  | _, _, _, .nil, _, _, _ => .nil
  | _, _, _, .cons h hs, Γ', ρ, hρ =>
    .cons (hasType_renameVar_live h Γ' ρ fun i B hu hB => hρ i B (by simp [Term.usesVarRow, hu]) hB)
      (renameVarFields_typed_live hs Γ' ρ fun i B hu hB => hρ i B (by simp [Term.usesVarRow, hu]) hB)
theorem renameVarArms_typed_live {Δ : List Lang.Ty} {Ω : HoleSignature} : ∀ {Γ : List Lang.Ty}
    {as : List (Label × Term)} {r : List (Label × Lang.Ty)} {B : Lang.Ty},
    ArmsTy (Ω := Ω) Δ Γ as r B → ∀ (Γ' : List Lang.Ty) (ρ : Nat → Nat),
      (∀ i C, Term.usesVarArms i as = true → Γ[i]? = some C → Γ'[ρ i]? = some C) →
      ArmsTy (Ω := Ω) Δ Γ' (Term.renameVarArms ρ as) r B
  | _, _, _, _, .one (A := A) (b := b) h, Γ', ρ, hρ =>
    .one (hasType_renameVar_live h (A :: Γ') (upR ρ)
      (upR_lookup A ρ (fun i => Term.usesVar i b) fun i C hu hC =>
        hρ i C (by simp [Term.usesVarArms, hu]) hC))
  | _, _, _, _, .cons (A := A) (b := b) (arms := a :: as) h ha _, Γ', ρ, hρ =>
    .cons (hasType_renameVar_live h (A :: Γ') (upR ρ)
        (upR_lookup A ρ (fun i => Term.usesVar i b) fun i C hu hC =>
          hρ i C (by simp [Term.usesVarArms, hu]) hC))
      (renameVarArms_typed_live ha Γ' ρ fun i C hu hC => hρ i C
        (by show (Term.usesVar (i + 1) b || Term.usesVarArms i (a :: as)) = true
            rw [hu, Bool.or_true]) hC)
      (by simp [Term.renameVarArms])
  | _, _, _, _, .cons (arms := []) _ _ hne, _, _, _ => absurd rfl hne
end

/-! A variable a typed term uses is in its context (C5, LANG-75.6: the factor's re-embedding reads only those). -/
mutual
/-- A variable a typed term uses is in its context. -/
theorem hasType_usesVar_lt {Δ : List Ty} {Ω : HoleSignature} : ∀ {Γ : List Ty} {t : Term} {T : Ty},
    HasType (Ω := Ω) Δ Γ t T → ∀ k, Term.usesVar k t = true → k < Γ.length
  | _, _, _, .var h, k, hk => by
    simp only [Term.usesVar, beq_iff_eq] at hk
    subst hk; exact (List.getElem?_eq_some_iff.mp h).1
  | _, _, _, .lam _ hb, k, hk => by
    have := hasType_usesVar_lt hb (k + 1) (by simpa [Term.usesVar] using hk)
    simpa using this
  | _, _, _, .app h1 h2, k, hk => by
    simp only [Term.usesVar, Bool.or_eq_true] at hk
    rcases hk with hk | hk
    · exact hasType_usesVar_lt h1 k hk
    · exact hasType_usesVar_lt h2 k hk
  | _, _, _, .fix h, k, hk => hasType_usesVar_lt h k (by simpa [Term.usesVar] using hk)
  | _, _, _, .nat _, k, hk => by simp [Term.usesVar] at hk
  | _, _, _, .bool, k, hk => by simp [Term.usesVar] at hk
  | _, _, _, .bytes _, k, hk => by simp [Term.usesVar] at hk
  | _, _, _, .digest _, k, hk => by simp [Term.usesVar] at hk
  | _, _, _, .prim h1 h2, k, hk => by
    simp only [Term.usesVar, Bool.or_eq_true] at hk
    rcases hk with hk | hk
    · exact hasType_usesVar_lt h1 k hk
    · exact hasType_usesVar_lt h2 k hk
  | _, _, _, .record _ h, k, hk => fieldsTy_usesVar_lt h k (by simpa [Term.usesVar] using hk)
  | _, _, _, .get h _, k, hk => hasType_usesVar_lt h k (by simpa [Term.usesVar] using hk)
  | _, _, _, .extend h _ hfs, k, hk => by
    simp only [Term.usesVar, Bool.or_eq_true] at hk
    rcases hk with hk | hk
    · exact hasType_usesVar_lt h k hk
    · exact fieldsTy_usesVar_lt hfs k hk
  | _, _, _, .inj _ _ h, k, hk => hasType_usesVar_lt h k (by simpa [Term.usesVar] using hk)
  | _, _, _, .case h ha, k, hk => by
    simp only [Term.usesVar, Bool.or_eq_true] at hk
    rcases hk with hk | hk
    · exact hasType_usesVar_lt h k hk
    · exact armsTy_usesVar_lt ha k hk
  | _, _, _, .ite h1 h2 h3, k, hk => by
    simp only [Term.usesVar, Bool.or_eq_true] at hk
    rcases hk with (hk | hk) | hk
    · exact hasType_usesVar_lt h1 k hk
    · exact hasType_usesVar_lt h2 k hk
    · exact hasType_usesVar_lt h3 k hk
  | _, _, _, .ref _, k, hk => by simp [Term.usesVar] at hk
  | _, _, _, .refuse _ _, k, hk => by simp [Term.usesVar] at hk
  | _, _, _, .hole _ hs, k, hk => substTy_usesVar_lt hs k (by simpa [Term.usesVar] using hk)
theorem substTy_usesVar_lt {Δ : List Ty} {Ω : HoleSignature} : ∀ {Γ : List Ty} {σ : List Term} {Ψ : List Ty},
    SubstTy Δ Γ σ Ψ Ω → ∀ k, Term.usesVarList k σ = true → k < Γ.length
  | _, _, _, .nil, k, hk => by simp [Term.usesVarList] at hk
  | _, _, _, .cons h hs, k, hk => by
    simp only [Term.usesVarList, Bool.or_eq_true] at hk
    rcases hk with hk | hk
    · exact hasType_usesVar_lt h k hk
    · exact substTy_usesVar_lt hs k hk
theorem fieldsTy_usesVar_lt {Δ : List Ty} {Ω : HoleSignature} : ∀ {Γ : List Ty}
    {fs : List (Label × Term)} {r : List (Label × Ty)},
    FieldsTy (Ω := Ω) Δ Γ fs r → ∀ k, Term.usesVarRow k fs = true → k < Γ.length
  | _, _, _, .nil, k, hk => by simp [Term.usesVarRow] at hk
  | _, _, _, .cons h hs, k, hk => by
    simp only [Term.usesVarRow, Bool.or_eq_true] at hk
    rcases hk with hk | hk
    · exact hasType_usesVar_lt h k hk
    · exact fieldsTy_usesVar_lt hs k hk
theorem armsTy_usesVar_lt {Δ : List Ty} {Ω : HoleSignature} : ∀ {Γ : List Ty}
    {as : List (Label × Term)} {r : List (Label × Ty)} {B : Ty},
    ArmsTy (Ω := Ω) Δ Γ as r B → ∀ k, Term.usesVarArms k as = true → k < Γ.length
  | _, _, _, _, .one h, k, hk => by
    have := hasType_usesVar_lt h (k + 1) (by simpa [Term.usesVarArms] using hk)
    simpa using this
  | _, _, _, _, .cons h ha _, k, hk => by
    simp only [Term.usesVarArms, Bool.or_eq_true] at hk
    rcases hk with hk | hk
    · have := hasType_usesVar_lt h (k + 1) hk
      simpa using this
    · exact armsTy_usesVar_lt ha k hk
end

/-- **Strengthening at any position.** -/
theorem hasType_unshiftAt_live {Δ Γ : List Lang.Ty} {Ω : HoleSignature} {t : Term} {T : Lang.Ty} {x : Nat}
    (h : HasType (Ω := Ω) Δ Γ t T) (hu : Term.usesVar x t = false) :
    HasType (Ω := Ω) Δ (Γ.eraseIdx x) (Term.renameVar (lowerIdx x) t) T := by
  refine hasType_renameVar_live h _ _ fun i B hi hB => ?_
  have hix : i ≠ x := by intro e; subst e; rw [hu] at hi; exact absurd hi (by decide)
  simp only [lowerIdx]
  by_cases hlt : i < x
  · rw [if_pos hlt, List.getElem?_eraseIdx_of_lt hlt]; exact hB
  · rw [if_neg hlt, List.getElem?_eraseIdx_of_ge (by omega), Nat.sub_add_cancel (by omega)]
    exact hB

/- Closed theorem API: statements copied verbatim from landed main. -/
theorem hasType_renameVar {Δ : List Lang.Ty} : ∀ {Γ : List Lang.Ty} {t : Term} {T : Lang.Ty},
    HasType Δ Γ t T → ∀ (Γ' : List Lang.Ty) (ρ : Nat → Nat),
      (∀ i B, Term.usesVar i t = true → Γ[i]? = some B → Γ'[ρ i]? = some B) →
      HasType Δ Γ' (Term.renameVar ρ t) T :=
  hasType_renameVar_live (Ω := [])

theorem renameVarFields_typed {Δ : List Lang.Ty} : ∀ {Γ : List Lang.Ty}
    {fs : List (Label × Term)} {r : List (Label × Lang.Ty)},
    FieldsTy Δ Γ fs r → ∀ (Γ' : List Lang.Ty) (ρ : Nat → Nat),
      (∀ i B, Term.usesVarRow i fs = true → Γ[i]? = some B → Γ'[ρ i]? = some B) →
      FieldsTy Δ Γ' (Term.renameVarRow ρ fs) r :=
  renameVarFields_typed_live (Ω := [])

theorem renameVarArms_typed {Δ : List Lang.Ty} : ∀ {Γ : List Lang.Ty}
    {as : List (Label × Term)} {r : List (Label × Lang.Ty)} {B : Lang.Ty},
    ArmsTy Δ Γ as r B → ∀ (Γ' : List Lang.Ty) (ρ : Nat → Nat),
      (∀ i C, Term.usesVarArms i as = true → Γ[i]? = some C → Γ'[ρ i]? = some C) →
      ArmsTy Δ Γ' (Term.renameVarArms ρ as) r B :=
  renameVarArms_typed_live (Ω := [])

theorem hasType_unshiftAt {Δ Γ : List Lang.Ty} {t : Term} {T : Lang.Ty} {x : Nat}
    (h : HasType Δ Γ t T) (hu : Term.usesVar x t = false) :
    HasType Δ (Γ.eraseIdx x) (Term.renameVar (lowerIdx x) t) T :=
  hasType_unshiftAt_live (Ω := []) h hu

/-! ## Ordinary substitution -/

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
    Lang.infer [] [.nat] (Term.substList [.var 0] (.lam .bool (.var 1))) (Ω := []) =
      some (.fn .bool .nat) := by
  rw [substList_lam_capture]
  exact Lang.infer_complete (.lam (by decide) (.var rfl))

/-- The former hypothesis is actually replaced, not left untouched. -/
theorem substList_replaces :
    Term.substList [.nat 7] (.lam .bool (.var 1)) = .lam .bool (.nat 7) := rfl

end Nanodregg.Lang
