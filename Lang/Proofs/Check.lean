/-
# Lang.Proofs.Check — `infer` decides `HasType` exactly; a term's type is unique

`infer_sound` and `infer_complete` make the checker and the relation one thing. `hasType_unique`
is the determinism of typing: a package's interface type is a function of its body, so the
interface a package's identity commits to is well-defined.
-/
import Lang.Proofs.Typing

namespace Nanodregg.Lang

variable {Δ : List Ty}

mutual
theorem infer_sound : ∀ {Γ : List Ty} {t : Term} {T : Ty}, infer Δ Γ t = some T → HasType Δ Γ t T
  | _, .var _, _, h => .var (by simpa [infer] using h)
  | Γ, .lam A b, T, h => by
      simp only [infer] at h
      split at h
      · rename_i hw
        cases hb : infer Δ (A :: Γ) b with
        | none => simp [hb] at h
        | some B => simp [hb] at h; subst h; exact .lam hw (infer_sound hb)
      · simp at h
  | Γ, .app f a, T, h => by
      simp only [infer] at h
      split at h
      · rename_i A B A' hf ha
        split at h
        · rename_i e; subst e; cases h; exact .app (infer_sound hf) (infer_sound ha)
        · simp at h
      · simp at h
  | Γ, .fix t, T, h => by
      simp only [infer] at h
      split at h
      · rename_i r r' ht
        split at h
        · rename_i e; subst e; cases h; exact .fix (infer_sound ht)
        · simp at h
      · simp at h
  | _, .nat _, _, h => by
      simp only [infer] at h
      split at h
      · rename_i hn; cases h; exact .nat hn
      · simp at h
  | _, .bool _, _, h => by simp only [infer, Option.some.injEq] at h; subst h; exact .bool
  | _, .bytes _, _, h => by
      simp only [infer] at h
      split at h
      · rename_i hn; cases h; exact .bytes hn
      · simp at h
  | Γ, .prim p a b, T, h => by
      simp only [infer] at h
      split at h
      · rename_i A B ha hb
        split at h
        · rename_i e; obtain ⟨e1, e2⟩ := e; subst e1; subst e2; cases h
          exact .prim (infer_sound ha) (infer_sound hb)
        · simp at h
      · simp at h
  | Γ, .record fs, T, h => by
      simp only [infer] at h
      split at h
      · rename_i hasc
        cases hf : inferFields Δ Γ fs with
        | none => simp [hf] at h
        | some r => simp [hf] at h; subst h; exact .record hasc (inferFields_sound hf)
      · simp at h
  | Γ, .get t ℓ, T, h => by
      simp only [infer] at h
      split at h
      · rename_i r ht; exact .get (infer_sound ht) h
      · simp at h
  | Γ, .extend t fs, T, h => by
      simp only [infer] at h
      split at h
      · rename_i r ht
        split at h
        · rename_i hasc
          cases hf : inferFields Δ Γ fs with
          | none => simp [hf] at h
          | some r2 => simp [hf] at h; subst h; exact .extend (infer_sound ht) hasc (inferFields_sound hf)
        · simp at h
      · simp at h
  | Γ, .inj (.sum r) ℓ t, T, h => by
      simp only [infer] at h
      split at h
      · rename_i hw
        split at h
        · rename_i A A' hA ht
          split at h
          · rename_i e; subst e; cases h; exact .inj hw hA (infer_sound ht)
          · simp at h
        · simp at h
      · simp at h
  | _, .inj .nat _ _, _, h | _, .inj .bool _ _, _, h | _, .inj .bytes _ _, _, h
  | _, .inj (.fn _ _) _ _, _, h | _, .inj (.record _) _ _, _, h => by simp [infer] at h
  | Γ, .case t arms, T, h => by
      simp only [infer] at h
      split at h
      · rename_i r ht; exact .case (infer_sound ht) (inferArms_sound h)
      · simp at h
  | Γ, .ite c a b, T, h => by
      simp only [infer] at h
      split at h
      · rename_i A B hc ha hb
        split at h
        · rename_i e; subst e; cases h
          exact .ite (infer_sound hc) (infer_sound ha) (infer_sound hb)
        · simp at h
      · simp at h
  | _, .ref _, _, h => .ref (by simpa [infer] using h)

theorem inferFields_sound :
    ∀ {Γ : List Ty} {fs : List (Label × Term)} {r : List (Label × Ty)},
      inferFields Δ Γ fs = some r → FieldsTy Δ Γ fs r
  | _, [], _, h => by simp only [inferFields, Option.some.injEq] at h; subst h; exact .nil
  | Γ, (ℓ, t) :: fs, r, h => by
      simp only [inferFields] at h
      split at h
      · rename_i T r' ht hfs; cases h; exact .cons (infer_sound ht) (inferFields_sound hfs)
      · simp at h

theorem inferArms_sound :
    ∀ {Γ : List Ty} {arms : List (Label × Term)} {r : List (Label × Ty)} {B : Ty},
      inferArms Δ Γ arms r = some B → ArmsTy Δ Γ arms r B
  | Γ, [(ℓ, b)], [(ℓ', A)], B, h => by
      simp only [inferArms] at h
      split at h
      · rename_i e; subst e; exact .one (infer_sound h)
      · simp at h
  | Γ, (ℓ, b) :: (a2 :: arms), (ℓ', A) :: r, B, h => by
      simp only [inferArms] at h
      split at h
      · rename_i e; subst e
        split at h
        · rename_i B1 B2 hb harms
          split at h
          · rename_i e; subst e; cases h
            exact .cons (infer_sound hb) (inferArms_sound harms) (by simp)
          · simp at h
        · simp at h
      · simp at h
  | _, [], _, _, h => by simp [inferArms] at h
  | _, [_], [], _, h => by simp [inferArms] at h
  | _, [_], _ :: _ :: _, _, h => by simp [inferArms] at h
  | _, _ :: _ :: _, [], _, h => by simp [inferArms] at h
end

mutual
theorem infer_complete : ∀ {Γ : List Ty} {t : Term} {T : Ty}, HasType Δ Γ t T → infer Δ Γ t = some T
  | _, _, _, .var h => by simpa [infer] using h
  | _, _, _, .lam hw hb => by simp [infer, hw, infer_complete hb]
  | _, _, _, .app hf ha => by simp [infer, infer_complete hf, infer_complete ha]
  | _, _, _, .fix ht => by simp [infer, infer_complete ht]
  | _, _, _, .nat hn => by simp [infer, hn]
  | _, _, _, .bool => by simp [infer]
  | _, _, _, .bytes hn => by simp [infer, hn]
  | _, _, _, .prim ha hb => by simp [infer, infer_complete ha, infer_complete hb]
  | _, _, _, .record hasc hf => by simp [infer, hasc, inferFields_complete hf]
  | _, _, _, .get ht hf => by simp [infer, infer_complete ht, hf]
  | _, _, _, .extend ht hasc hf => by simp [infer, infer_complete ht, hasc, inferFields_complete hf]
  | _, _, _, .inj hw hA ht => by
      simp only [infer, hw, if_true, hA, infer_complete ht]
  | _, _, _, .case ht ha => by simp [infer, infer_complete ht, inferArms_complete ha]
  | _, _, _, .ite hc ha hb => by
      simp [infer, infer_complete hc, infer_complete ha, infer_complete hb]
  | _, _, _, .ref h => by simpa [infer] using h

theorem inferFields_complete :
    ∀ {Γ : List Ty} {fs : List (Label × Term)} {r : List (Label × Ty)},
      FieldsTy Δ Γ fs r → inferFields Δ Γ fs = some r
  | _, _, _, .nil => by simp [inferFields]
  | _, _, _, .cons ht hf => by simp [inferFields, infer_complete ht, inferFields_complete hf]

theorem inferArms_complete :
    ∀ {Γ : List Ty} {arms : List (Label × Term)} {r : List (Label × Ty)} {B : Ty},
      ArmsTy Δ Γ arms r B → inferArms Δ Γ arms r = some B
  | _, _, _, _, .one hb => by simp [inferArms, infer_complete hb]
  | _, _, _, _, .cons (arms := a2 :: arms) hb ha _ => by
      simp [inferArms, infer_complete hb, inferArms_complete ha]
  | _, _, _, _, .cons (arms := []) _ _ hne => absurd rfl hne
end

theorem infer_iff {Γ : List Ty} {t : Term} {T : Ty} : infer Δ Γ t = some T ↔ HasType Δ Γ t T :=
  ⟨infer_sound, infer_complete⟩

/-- Typing is deterministic: a term has at most one type. -/
theorem hasType_unique {Γ : List Ty} {t : Term} {A B : Ty}
    (ha : HasType Δ Γ t A) (hb : HasType Δ Γ t B) : A = B := by
  have := (infer_complete ha).symm.trans (infer_complete hb)
  exact Option.some.inj this

/-- `check` accepts exactly the closed terms of the declared type. -/
theorem check_iff {t : Term} {T : Ty} : check Δ t T = true ↔ HasType Δ [] t T := by
  simp [check, infer_iff]

end Nanodregg.Lang
