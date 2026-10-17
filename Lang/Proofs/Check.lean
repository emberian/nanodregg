/-
# Lang.Proofs.Check — `inferE` decides `HasType` exactly; a term's type is unique

`inferE_sound` and `inferE_complete` make the checker and the relation one thing; `infer` (its
`toOption`) inherits both. `hasType_unique` is the determinism of typing: a package's interface type
is a function of its body, so the interface a package's identity commits to is well-defined.
-/
import Lang.Proofs.Typing

namespace Nanodregg.Lang

variable {Δ : List Ty}

mutual
theorem inferE_sound : ∀ {Γ : List Ty} {t : Term} {T : Ty}, inferE Δ Γ t = .ok T → HasType Δ Γ t T
  | Γ, .var i, T, h => by
      simp only [inferE] at h
      split at h
      · rename_i T' hT; cases h; exact .var hT
      · simp [typeErr] at h
  | Γ, .lam A b, T, h => by
      simp only [inferE] at h
      split at h
      · rename_i hw
        split at h
        · rename_i B hb; cases h; exact .lam hw (inferE_sound hb)
        · simp at h
      · simp [typeErr] at h
  | Γ, .app f a, T, h => by
      simp only [inferE] at h
      split at h
      · rename_i A B A' hf ha
        split at h
        · rename_i e; subst e; cases h; exact .app (inferE_sound hf) (inferE_sound ha)
        · simp [typeErr] at h
      all_goals simp [typeErr] at h
  | Γ, .fix t, T, h => by
      simp only [inferE] at h
      split at h
      · rename_i r r' ht
        split at h
        · rename_i e; subst e; cases h; exact .fix (inferE_sound ht)
        · simp [typeErr] at h
      all_goals simp [typeErr] at h
  | _, .nat _, _, h => by
      simp only [inferE] at h
      split at h
      · rename_i hn; cases h; exact .nat hn
      · simp [typeErr] at h
  | _, .bool _, _, h => by simp only [inferE, Except.ok.injEq] at h; subst h; exact .bool
  | _, .bytes _, _, h => by
      simp only [inferE] at h
      split at h
      · rename_i hn; cases h; exact .bytes hn
      · simp [typeErr] at h
  | _, .digest _, _, h => by
      simp only [inferE] at h
      split at h
      · rename_i hn; cases h; exact .digest hn
      · simp [typeErr] at h
  | Γ, .prim p a b, T, h => by
      simp only [inferE] at h
      split at h
      · rename_i A B ha hb
        split at h
        · rename_i e; obtain ⟨e1, e2⟩ := e; subst e1; subst e2; cases h
          exact .prim (inferE_sound ha) (inferE_sound hb)
        · simp [typeErr] at h
      all_goals simp at h
  | Γ, .record fs, T, h => by
      simp only [inferE] at h
      split at h
      · rename_i hasc
        split at h
        · rename_i r hf; cases h; exact .record hasc (inferFields_sound hf)
        · simp at h
      · simp [typeErr] at h
  | Γ, .get t ℓ, T, h => by
      simp only [inferE] at h
      split at h
      · rename_i r ht
        split at h
        · rename_i T' hf; cases h; exact .get (inferE_sound ht) hf
        · simp [typeErr] at h
      all_goals simp [typeErr] at h
  | Γ, .extend t fs, T, h => by
      simp only [inferE] at h
      split at h
      · rename_i r ht
        split at h
        · rename_i hasc
          split at h
          · rename_i r2 hf; cases h; exact .extend (inferE_sound ht) hasc (inferFields_sound hf)
          · simp at h
        · simp [typeErr] at h
      all_goals simp [typeErr] at h
  | Γ, .inj (.sum r) ℓ t, T, h => by
      simp only [inferE] at h
      split at h
      · rename_i hw
        split at h
        · rename_i A A' hA ht
          split at h
          · rename_i e; subst e; cases h; exact .inj hw hA (inferE_sound ht)
          · simp [typeErr] at h
        all_goals simp [typeErr] at h
      · simp [typeErr] at h
  | _, .inj .nat _ _, _, h | _, .inj .bool _ _, _, h | _, .inj .bytes _ _, _, h
  | _, .inj .digest _ _, _, h
  | _, .inj (.fn _ _) _ _, _, h | _, .inj (.record _) _ _, _, h => by simp [inferE, typeErr] at h
  | Γ, .case t arms, T, h => by
      simp only [inferE] at h
      split at h
      · rename_i r ht; exact .case (inferE_sound ht) (inferArms_sound h)
      all_goals simp [typeErr] at h
  | Γ, .ite c a b, T, h => by
      simp only [inferE] at h
      split at h
      · rename_i A B hc ha hb
        split at h
        · rename_i e; subst e; cases h
          exact .ite (inferE_sound hc) (inferE_sound ha) (inferE_sound hb)
        · simp [typeErr] at h
      all_goals simp [typeErr] at h
  | Γ, .ref i, T, h => by
      simp only [inferE] at h
      split at h
      · rename_i T' hT; cases h; exact .ref hT
      · simp [typeErr] at h

theorem inferFields_sound :
    ∀ {Γ : List Ty} {fs : List (Label × Term)} {r : List (Label × Ty)},
      inferFields Δ Γ fs = .ok r → FieldsTy Δ Γ fs r
  | _, [], _, h => by simp only [inferFields, Except.ok.injEq] at h; subst h; exact .nil
  | Γ, (ℓ, t) :: fs, r, h => by
      simp only [inferFields] at h
      split at h
      · rename_i T r' ht hfs; cases h; exact .cons (inferE_sound ht) (inferFields_sound hfs)
      all_goals simp at h

theorem inferArms_sound :
    ∀ {Γ : List Ty} {arms : List (Label × Term)} {r : List (Label × Ty)} {B : Ty},
      inferArms Δ Γ arms r = .ok B → ArmsTy Δ Γ arms r B
  | Γ, [(ℓ, b)], [(ℓ', A)], B, h => by
      simp only [inferArms] at h
      split at h
      · rename_i e; subst e
        split at h
        · rename_i B' hb; cases h; exact .one (inferE_sound hb)
        · simp at h
      · simp at h
  | Γ, (ℓ, b) :: (a2 :: arms), (ℓ', A) :: r, B, h => by
      simp only [inferArms] at h
      split at h
      · rename_i e; subst e
        split at h
        · rename_i B1 B2 hb harms
          split at h
          · rename_i e; subst e; cases h
            exact .cons (inferE_sound hb) (inferArms_sound harms) (by simp)
          · simp at h
        all_goals simp at h
      · simp at h
  | _, [], _, _, h => by simp [inferArms] at h
  | _, [_], [], _, h => by simp [inferArms] at h
  | _, [_], _ :: _ :: _, _, h => by simp [inferArms] at h
  | _, _ :: _ :: _, [], _, h => by simp [inferArms] at h
end

mutual
theorem inferE_complete : ∀ {Γ : List Ty} {t : Term} {T : Ty}, HasType Δ Γ t T → inferE Δ Γ t = .ok T
  | _, _, _, .var h => by simp [inferE, h]
  | _, _, _, .lam hw hb => by simp [inferE, hw, inferE_complete hb]
  | _, _, _, .app hf ha => by simp [inferE, inferE_complete hf, inferE_complete ha]
  | _, _, _, .fix ht => by simp [inferE, inferE_complete ht]
  | _, _, _, .nat hn => by simp [inferE, hn]
  | _, _, _, .bool => by simp [inferE]
  | _, _, _, .bytes hn => by simp [inferE, hn]
  | _, _, _, .digest hn => by simp [inferE, hn]
  | _, _, _, .prim ha hb => by simp [inferE, inferE_complete ha, inferE_complete hb]
  | _, _, _, .record hasc hf => by simp [inferE, hasc, inferFields_complete hf]
  | _, _, _, .get ht hf => by simp [inferE, inferE_complete ht, hf]
  | _, _, _, .extend ht hasc hf => by simp [inferE, inferE_complete ht, hasc, inferFields_complete hf]
  | _, _, _, .inj hw hA ht => by
      simp only [inferE, hw, if_true, hA, inferE_complete ht]
  | _, _, _, .case ht ha => by simp [inferE, inferE_complete ht, inferArms_complete ha]
  | _, _, _, .ite hc ha hb => by
      simp [inferE, inferE_complete hc, inferE_complete ha, inferE_complete hb]
  | _, _, _, .ref h => by simp [inferE, h]

theorem inferFields_complete :
    ∀ {Γ : List Ty} {fs : List (Label × Term)} {r : List (Label × Ty)},
      FieldsTy Δ Γ fs r → inferFields Δ Γ fs = .ok r
  | _, _, _, .nil => by simp [inferFields]
  | _, _, _, .cons ht hf => by simp [inferFields, inferE_complete ht, inferFields_complete hf]

theorem inferArms_complete :
    ∀ {Γ : List Ty} {arms : List (Label × Term)} {r : List (Label × Ty)} {B : Ty},
      ArmsTy Δ Γ arms r B → inferArms Δ Γ arms r = .ok B
  | _, _, _, _, .one hb => by simp [inferArms, inferE_complete hb]
  | _, _, _, _, .cons (arms := a2 :: arms) hb ha _ => by
      simp [inferArms, inferE_complete hb, inferArms_complete ha]
  | _, _, _, _, .cons (arms := []) _ _ hne => absurd rfl hne
end

theorem inferE_iff {Γ : List Ty} {t : Term} {T : Ty} : inferE Δ Γ t = .ok T ↔ HasType Δ Γ t T :=
  ⟨inferE_sound, inferE_complete⟩

theorem toOption_eq_some {ε α : Type} {x : Except ε α} {a : α} : x.toOption = some a ↔ x = .ok a := by
  cases x <;> simp [Except.toOption]

theorem infer_sound {Γ : List Ty} {t : Term} {T : Ty} (h : infer Δ Γ t = some T) : HasType Δ Γ t T :=
  inferE_sound (toOption_eq_some.1 h)

theorem infer_complete {Γ : List Ty} {t : Term} {T : Ty} (h : HasType Δ Γ t T) : infer Δ Γ t = some T :=
  toOption_eq_some.2 (inferE_complete h)

theorem infer_iff {Γ : List Ty} {t : Term} {T : Ty} : infer Δ Γ t = some T ↔ HasType Δ Γ t T :=
  ⟨infer_sound, infer_complete⟩

/-- Typing is deterministic: a term has at most one type. -/
theorem hasType_unique {Γ : List Ty} {t : Term} {A B : Ty}
    (ha : HasType Δ Γ t A) (hb : HasType Δ Γ t B) : A = B := by
  have := (infer_complete ha).symm.trans (infer_complete hb)
  exact Option.some.inj this

/-- `checkE` accepts exactly the closed terms of the declared type, and its refusal names a rule. -/
theorem checkE_ok_iff {t : Term} {T : Ty} : checkE Δ t T = .ok () ↔ HasType Δ [] t T := by
  unfold checkE
  constructor
  · intro h
    split at h
    · rename_i T' hT
      split at h
      · rename_i e; subst e; exact inferE_sound hT
      · simp at h
    · simp at h
  · intro h
    simp [inferE_complete h]

/-- `check` accepts exactly the closed terms of the declared type. -/
theorem check_iff {t : Term} {T : Ty} : check Δ t T = true ↔ HasType Δ [] t T := by
  rw [← checkE_ok_iff]
  unfold check
  cases checkE Δ t T <;> simp [Except.toBool]

end Nanodregg.Lang
