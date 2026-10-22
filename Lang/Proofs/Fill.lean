/-
# Lang.Proofs.Fill — contextual filling for the deployed syntax

Signature transport and filling (`fillHoles_typed`, `fillHolesFields_typed`, `fillHolesArms_typed`), then the
occurrence facts for contextual holes and ordinary substitutions (`hasType_declaresHole` and its field/arm
forms; `usesRef` through renaming, substitution and filling). Subject: `Lang.Subst`'s `fillRefs`, which
`Lang.LiveHoles.instantiateHoles` runs.
-/
import Lang.Proofs.Subst

namespace Nanodregg.Lang

mutual
theorem hasType_signature {Δ : List Lang.Ty} {Ω Ω' : HoleSignature}
    (hΩ : ∀ n d, Ω.find? (fun e => e.name == n) = some d →
      Ω'.find? (fun e => e.name == n) = some d) :
    ∀ {Γ : List Lang.Ty} {t : Term} {T : Lang.Ty},
      HasType Δ Γ t T Ω → HasType Δ Γ t T Ω'
  | _, _, _, .var h => .var h
  | _, _, _, .lam hw h => .lam hw (hasType_signature hΩ h)
  | _, _, _, .app hf ha => .app (hasType_signature hΩ hf) (hasType_signature hΩ ha)
  | _, _, _, .fix h => .fix (hasType_signature hΩ h)
  | _, _, _, .nat h => .nat h
  | _, _, _, .bool => .bool
  | _, _, _, .bytes h => .bytes h
  | _, _, _, .digest h => .digest h
  | _, _, _, .prim ha hb => .prim (hasType_signature hΩ ha) (hasType_signature hΩ hb)
  | _, _, _, .record hw h => .record hw (fieldsTy_signature hΩ h)
  | _, _, _, .get h hl => .get (hasType_signature hΩ h) hl
  | _, _, _, .extend h hw hs => .extend (hasType_signature hΩ h) hw (fieldsTy_signature hΩ hs)
  | _, _, _, .inj hw hl h => .inj hw hl (hasType_signature hΩ h)
  | _, _, _, .case h ha => .case (hasType_signature hΩ h) (armsTy_signature hΩ ha)
  | _, _, _, .ite hc ha hb =>
      .ite (hasType_signature hΩ hc) (hasType_signature hΩ ha) (hasType_signature hΩ hb)
  | _, _, _, .ref h => .ref h
  | _, _, _, .refuse hw hn => .refuse hw hn
  | _, _, _, .hole hd hs => .hole (hΩ _ _ hd) (substTy_signature hΩ hs)
theorem fieldsTy_signature {Δ : List Lang.Ty} {Ω Ω' : HoleSignature}
    (hΩ : ∀ n d, Ω.find? (fun e => e.name == n) = some d →
      Ω'.find? (fun e => e.name == n) = some d) :
    ∀ {Γ : List Lang.Ty} {ts : List (Label × Term)} {r : List (Label × Lang.Ty)},
      FieldsTy Δ Γ ts r Ω → FieldsTy Δ Γ ts r Ω'
  | _, _, _, .nil => .nil
  | _, _, _, .cons h hs => .cons (hasType_signature hΩ h) (fieldsTy_signature hΩ hs)
theorem armsTy_signature {Δ : List Lang.Ty} {Ω Ω' : HoleSignature}
    (hΩ : ∀ n d, Ω.find? (fun e => e.name == n) = some d →
      Ω'.find? (fun e => e.name == n) = some d) :
    ∀ {Γ : List Lang.Ty} {ts : List (Label × Term)} {r : List (Label × Lang.Ty)} {T : Lang.Ty},
      ArmsTy Δ Γ ts r T Ω → ArmsTy Δ Γ ts r T Ω'
  | _, _, _, _, .one h => .one (hasType_signature hΩ h)
  | _, _, _, _, .cons h hs hn => .cons (hasType_signature hΩ h) (armsTy_signature hΩ hs) hn
theorem substTy_signature {Δ : List Lang.Ty} {Ω Ω' : HoleSignature}
    (hΩ : ∀ n d, Ω.find? (fun e => e.name == n) = some d →
      Ω'.find? (fun e => e.name == n) = some d) :
    ∀ {Γ : List Lang.Ty} {ts : List Term} {Ψ : List Lang.Ty},
      SubstTy Δ Γ ts Ψ Ω → SubstTy Δ Γ ts Ψ Ω'
  | _, _, _, .nil => .nil
  | _, _, _, .cons h hs => .cons (hasType_signature hΩ h) (substTy_signature hΩ hs)
end

mutual
theorem hasType_library {Δ Δ' : List Lang.Ty} {Ω : HoleSignature}
    (hΩ : ∀ (n : Nat) (A : Lang.Ty), Δ[n]? = some A → Δ'[n]? = some A) :
    ∀ {Γ : List Lang.Ty} {t : Term} {T : Lang.Ty},
      HasType Δ Γ t T Ω → HasType Δ' Γ t T Ω
  | _, _, _, .var h => .var h
  | _, _, _, .lam hw h => .lam hw (hasType_library hΩ h)
  | _, _, _, .app hf ha => .app (hasType_library hΩ hf) (hasType_library hΩ ha)
  | _, _, _, .fix h => .fix (hasType_library hΩ h)
  | _, _, _, .nat h => .nat h
  | _, _, _, .bool => .bool
  | _, _, _, .bytes h => .bytes h
  | _, _, _, .digest h => .digest h
  | _, _, _, .prim ha hb => .prim (hasType_library hΩ ha) (hasType_library hΩ hb)
  | _, _, _, .record hw h => .record hw (fieldsTy_library hΩ h)
  | _, _, _, .get h hl => .get (hasType_library hΩ h) hl
  | _, _, _, .extend h hw hs => .extend (hasType_library hΩ h) hw (fieldsTy_library hΩ hs)
  | _, _, _, .inj hw hl h => .inj hw hl (hasType_library hΩ h)
  | _, _, _, .case h ha => .case (hasType_library hΩ h) (armsTy_library hΩ ha)
  | _, _, _, .ite hc ha hb =>
      .ite (hasType_library hΩ hc) (hasType_library hΩ ha) (hasType_library hΩ hb)
  | _, _, _, .ref h => .ref (hΩ _ _ h)
  | _, _, _, .refuse hw hn => .refuse hw hn
  | _, _, _, .hole hd hs => .hole hd (substTy_library hΩ hs)
theorem fieldsTy_library {Δ Δ' : List Lang.Ty} {Ω : HoleSignature}
    (hΩ : ∀ (n : Nat) (A : Lang.Ty), Δ[n]? = some A → Δ'[n]? = some A) :
    ∀ {Γ : List Lang.Ty} {ts : List (Label × Term)} {r : List (Label × Lang.Ty)},
      FieldsTy Δ Γ ts r Ω → FieldsTy Δ' Γ ts r Ω
  | _, _, _, .nil => .nil
  | _, _, _, .cons h hs => .cons (hasType_library hΩ h) (fieldsTy_library hΩ hs)
theorem armsTy_library {Δ Δ' : List Lang.Ty} {Ω : HoleSignature}
    (hΩ : ∀ (n : Nat) (A : Lang.Ty), Δ[n]? = some A → Δ'[n]? = some A) :
    ∀ {Γ : List Lang.Ty} {ts : List (Label × Term)} {r : List (Label × Lang.Ty)} {T : Lang.Ty},
      ArmsTy Δ Γ ts r T Ω → ArmsTy Δ' Γ ts r T Ω
  | _, _, _, _, .one h => .one (hasType_library hΩ h)
  | _, _, _, _, .cons h hs hn => .cons (hasType_library hΩ h) (armsTy_library hΩ hs) hn
theorem substTy_library {Δ Δ' : List Lang.Ty} {Ω : HoleSignature}
    (hΩ : ∀ (n : Nat) (A : Lang.Ty), Δ[n]? = some A → Δ'[n]? = some A) :
    ∀ {Γ : List Lang.Ty} {ts : List Term} {Ψ : List Lang.Ty},
      SubstTy Δ Γ ts Ψ Ω → SubstTy Δ' Γ ts Ψ Ω
  | _, _, _, .nil => .nil
  | _, _, _, .cons h hs => .cons (hasType_library hΩ h) (substTy_library hΩ hs)
end

/-- Filtering another name preserves this declaration, including its context. -/
theorem declaration_filter (p : HoleDecl (List Lang.Ty) Lang.Ty → Bool) (n : Nat) :
    ∀ Ω : HoleSignature, (∀ d ∈ Ω, d.name = n → p d = true) →
      (Ω.filter p).find? (fun d => d.name == n) = Ω.find? (fun d => d.name == n)
  | [], _ => rfl
  | d :: Ω, h => by
    have ih := declaration_filter p n Ω fun d' hd' => h d' (List.mem_cons_of_mem _ hd')
    by_cases hn : d.name = n
    · have hp := h d List.mem_cons_self hn
      simp [List.filter_cons_of_pos hp, hn]
    · have hb : (d.name == n) = false := by simp [hn]
      by_cases hp : p d = true
      · simp only [List.filter_cons_of_pos hp, List.find?_cons, hb] at ih ⊢; exact ih
      · simp only [List.filter_cons_of_neg hp, List.find?_cons, hb] at ih ⊢; exact ih

mutual
/-- Contextual filling preserves the import library, instantiates the declared context,
and retains unfilled declarations in the target signature. -/
theorem fillHoles_typed {Δ : List Lang.Ty} {Ω Ω' : HoleSignature}
    (σ : Nat → Option Term)
    (hfill : ∀ n d M, Ω.find? (fun e => e.name == n) = some d → σ n = some M →
      HasType Δ d.ctx M d.ty)
    (hkeep : ∀ n d, Ω.find? (fun e => e.name == n) = some d → σ n = none →
      Ω'.find? (fun e => e.name == n) = some d) : ∀ {Γ : List Lang.Ty} {t : Term} {T : Lang.Ty}, HasType Δ Γ t T Ω →
      HasType Δ Γ (Term.fillRefs σ t) T Ω' 

  | _, _, _, .ref h => .ref h
  | Γ, _, _, .hole (n := n) (σ := ts) (d := d) hd hs => by
      have hts := fillRefsSubst_typed σ hfill hkeep hs
      cases he : σ n with
      | none =>
        simp only [Term.fillRefs, he]
        exact .hole (hkeep n d hd he) hts
      | some M =>
        simp only [Term.fillRefs, he]
        have hm : HasType Δ d.ctx M d.ty Ω' :=
          hasType_signature (fun _ _ h => by simp at h) (hfill n d M hd he)
        exact substList_typed hts hm
  | _, _, _, .var h => .var h
  | _, _, _, .lam hw hb =>
    .lam hw (fillHoles_typed σ hfill hkeep hb)
  | _, _, _, .app h1 h2 =>
    .app (fillHoles_typed σ hfill hkeep h1)
      (fillHoles_typed σ hfill hkeep h2)
  | _, _, _, .fix h => .fix (fillHoles_typed σ hfill hkeep h)
  | _, _, _, .nat h => .nat h
  | _, _, _, .bool => .bool
  | _, _, _, .bytes h => .bytes h
  | _, _, _, .digest h => .digest h
  | _, _, _, .prim h1 h2 =>
    .prim (fillHoles_typed σ hfill hkeep h1)
      (fillHoles_typed σ hfill hkeep h2)
  | _, _, _, .record ha h => by
    simp only [Term.fillRefs]
    exact .record (by rw [fillRefsRow_ascending]; exact ha)
      (fillHolesFields_typed σ hfill hkeep h)
  | _, _, _, .get h hl => .get (fillHoles_typed σ hfill hkeep h) hl
  | _, _, _, .extend h ha hfs => by
    simp only [Term.fillRefs]
    exact .extend (fillHoles_typed σ hfill hkeep h)
      (by rw [fillRefsRow_ascending]; exact ha)
      (fillHolesFields_typed σ hfill hkeep hfs)
  | _, _, _, .inj hw hl h =>
    .inj hw hl (fillHoles_typed σ hfill hkeep h)
  | _, _, _, .case h ha =>
    .case (fillHoles_typed σ hfill hkeep h)
      (fillHolesArms_typed σ hfill hkeep ha)
  | _, _, _, .ite h1 h2 h3 =>
    .ite (fillHoles_typed σ hfill hkeep h1)
      (fillHoles_typed σ hfill hkeep h2)
      (fillHoles_typed σ hfill hkeep h3)
  | _, _, _, .refuse hw hn => .refuse hw hn
theorem fillHolesFields_typed {Δ : List Lang.Ty} {Ω Ω' : HoleSignature}
    (σ : Nat → Option Term)
    (hfill : ∀ n d M, Ω.find? (fun e => e.name == n) = some d → σ n = some M →
      HasType Δ d.ctx M d.ty)
    (hkeep : ∀ n d, Ω.find? (fun e => e.name == n) = some d → σ n = none →
      Ω'.find? (fun e => e.name == n) = some d) : ∀ {Γ : List Lang.Ty} {fs : List (Label × Term)} {r : List (Label × Lang.Ty)},
      FieldsTy Δ Γ fs r Ω → FieldsTy Δ Γ (Term.fillRefsRow σ fs) r Ω' 

  | _, _, _, .nil => .nil
  | _, _, _, .cons h hs =>
    .cons (fillHoles_typed σ hfill hkeep h)
      (fillHolesFields_typed σ hfill hkeep hs)
theorem fillHolesArms_typed {Δ : List Lang.Ty} {Ω Ω' : HoleSignature}
    (σ : Nat → Option Term)
    (hfill : ∀ n d M, Ω.find? (fun e => e.name == n) = some d → σ n = some M →
      HasType Δ d.ctx M d.ty)
    (hkeep : ∀ n d, Ω.find? (fun e => e.name == n) = some d → σ n = none →
      Ω'.find? (fun e => e.name == n) = some d) : ∀ {Γ : List Lang.Ty} {as : List (Label × Term)} {r : List (Label × Lang.Ty)} {B : Lang.Ty},
      ArmsTy Δ Γ as r B Ω → ArmsTy Δ Γ (Term.fillRefsRow σ as) r B Ω' 

  | _, _, _, _, .one h =>
    .one (fillHoles_typed σ hfill hkeep h)
  | _, _, _, _, .cons (b := b) (arms := a :: as) h ha _ =>
    .cons (fillHoles_typed σ hfill hkeep h)
      (fillHolesArms_typed σ hfill hkeep ha)
      (by simp [Term.fillRefsRow])
  | _, _, _, _, .cons (arms := []) _ _ hne => absurd rfl hne
theorem fillRefsSubst_typed {Δ : List Lang.Ty} {Ω Ω' : HoleSignature}
    (σ : Nat → Option Term)
    (hfill : ∀ n d M, Ω.find? (fun e => e.name == n) = some d → σ n = some M →
      HasType Δ d.ctx M d.ty)
    (hkeep : ∀ n d, Ω.find? (fun e => e.name == n) = some d → σ n = none →
      Ω'.find? (fun e => e.name == n) = some d) : ∀ {Γ : List Lang.Ty} {ts : List Term} {Ψ : List Lang.Ty},
      SubstTy Δ Γ ts Ψ Ω → SubstTy Δ Γ (Term.fillRefsList σ ts) Ψ Ω' 

  | _, _, _, .nil => .nil
  | _, _, _, .cons h hs =>
      .cons (fillHoles_typed σ hfill hkeep h) (fillRefsSubst_typed σ hfill hkeep hs)

end

/-! ## Occurrences -/

/-! ## Named contextual-hole occurrences -/

/-- `t` uses ref `n` only if `t`'s sub-term-or-row does; the shape every compound case lifts. -/
abbrev RefsSub (s t : Nat → Bool) : Prop := ∀ n, s n = true → t n = true

mutual
/-- A typed term's holes are declared in its signature. -/
theorem hasType_declaresHole {Δ : List Lang.Ty} {Ω : HoleSignature} : ∀ {Γ : List Lang.Ty} {t : Term} {T : Lang.Ty},
    HasType (Ω := Ω) Δ Γ t T → ∀ n, Term.usesRef n t = true → (Ω.find? (fun d => d.name == n)).isSome = true
  | _, _, _, .ref _, _, hn => by simp [Term.usesRef] at hn
  | _, _, _, .hole (n := m) hd hs, n, hn => by
    simp only [Term.usesRef, Bool.or_eq_true, beq_iff_eq] at hn
    rcases hn with he | hn
    · subst m; simp [hd]
    · exact substTy_usesRef hs n hn
  | _, _, _, .var _, _, hn | _, _, _, .nat _, _, hn | _, _, _, .bool, _, hn
  | _, _, _, .bytes _, _, hn | _, _, _, .digest _, _, hn | _, _, _, .refuse _ _, _, hn => by
    simp [Term.usesRef] at hn
  | _, _, _, .lam _ h, n, hn => hasType_declaresHole h n (by simpa [Term.usesRef] using hn)
  | _, _, _, .fix h, n, hn => hasType_declaresHole h n (by simpa [Term.usesRef] using hn)
  | _, _, _, .get h _, n, hn => hasType_declaresHole h n (by simpa [Term.usesRef] using hn)
  | _, _, _, .inj _ _ h, n, hn => hasType_declaresHole h n (by simpa [Term.usesRef] using hn)
  | _, _, _, .app h1 h2, n, hn => by
    simp only [Term.usesRef, Bool.or_eq_true] at hn
    rcases hn with hn | hn
    · exact hasType_declaresHole h1 n hn
    · exact hasType_declaresHole h2 n hn
  | _, _, _, .prim h1 h2, n, hn => by
    simp only [Term.usesRef, Bool.or_eq_true] at hn
    rcases hn with hn | hn
    · exact hasType_declaresHole h1 n hn
    · exact hasType_declaresHole h2 n hn
  | _, _, _, .record _ h, n, hn => fieldsTy_declaresHole h n (by simpa [Term.usesRef] using hn)
  | _, _, _, .extend h _ hfs, n, hn => by
    simp only [Term.usesRef, Bool.or_eq_true] at hn
    rcases hn with hn | hn
    · exact hasType_declaresHole h n hn
    · exact fieldsTy_declaresHole hfs n hn
  | _, _, _, .case h ha, n, hn => by
    simp only [Term.usesRef, Bool.or_eq_true] at hn
    rcases hn with hn | hn
    · exact hasType_declaresHole h n hn
    · exact armsTy_declaresHole ha n hn
  | _, _, _, .ite h1 h2 h3, n, hn => by
    simp only [Term.usesRef, Bool.or_eq_true] at hn
    rcases hn with (hn | hn) | hn
    · exact hasType_declaresHole h1 n hn
    · exact hasType_declaresHole h2 n hn
    · exact hasType_declaresHole h3 n hn
theorem fieldsTy_declaresHole {Δ : List Lang.Ty} {Ω : HoleSignature} : ∀ {Γ : List Lang.Ty}
    {fs : List (Label × Term)} {r : List (Label × Lang.Ty)},
    FieldsTy (Ω := Ω) Δ Γ fs r → ∀ n, Term.usesRefRow n fs = true → (Ω.find? (fun d => d.name == n)).isSome = true
  | _, _, _, .nil, _, hn => by simp [Term.usesRefRow] at hn
  | _, _, _, .cons h hs, n, hn => by
    simp only [Term.usesRefRow, Bool.or_eq_true] at hn
    rcases hn with hn | hn
    · exact hasType_declaresHole h n hn
    · exact fieldsTy_declaresHole hs n hn
theorem armsTy_declaresHole {Δ : List Lang.Ty} {Ω : HoleSignature} : ∀ {Γ : List Lang.Ty}
    {as : List (Label × Term)} {r : List (Label × Lang.Ty)} {B : Lang.Ty},
    ArmsTy (Ω := Ω) Δ Γ as r B → ∀ n, Term.usesRefRow n as = true → (Ω.find? (fun d => d.name == n)).isSome = true
  | _, _, _, _, .one h, n, hn => by
    simp only [Term.usesRefRow, Bool.or_eq_true, Bool.false_eq_true, or_false] at hn
    exact hasType_declaresHole h n hn
  | _, _, _, _, .cons h ha _, n, hn => by
    simp only [Term.usesRefRow, Bool.or_eq_true] at hn
    rcases hn with hn | hn
    · exact hasType_declaresHole h n hn
    · exact armsTy_declaresHole ha n hn
theorem substTy_usesRef {Δ : List Lang.Ty} {Ω : HoleSignature} :
    ∀ {Γ : List Lang.Ty} {ts : List Term} {Ψ : List Lang.Ty},
      SubstTy Δ Γ ts Ψ Ω → ∀ n, Term.usesRefList n ts = true →
      (Ω.find? (fun d => d.name == n)).isSome = true
  | _, _, _, .nil, _, hn => by simp [Term.usesRefList] at hn
  | _, _, _, .cons h hs, n, hn => by
    simp only [Term.usesRefList, Bool.or_eq_true] at hn
    rcases hn with hn | hn
    · exact hasType_declaresHole h n hn
    · exact substTy_usesRef hs n hn

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
  | .hole m σ, ρ => by
    simp only [Term.renameVar, Term.usesRef, usesRefList_renameVarList n σ]
theorem usesRefList_renameVarList (n : Nat) : ∀ (fs : List Term) (ρ : Nat → Nat),
    Term.usesRefList n (Term.renameVarList ρ fs) = Term.usesRefList n fs
  | [], _ => rfl
  | t :: fs, ρ => by
    simp only [Term.renameVarList, Term.usesRefList, usesRef_renameVar n t, usesRefList_renameVarList n fs]
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



/-- Substitution cannot manufacture a hole absent from both its source and replacements. -/
def SubstOrigin (σ : Nat → Term) (n : Nat) (used : Bool) : Prop :=
  used = true ∨ ∃ i, Term.usesRef n (σ i) = true

theorem SubstOrigin.mono {σ : Nat → Term} {n : Nat} {a b : Bool}
    (h : a = true → b = true) : SubstOrigin σ n a → SubstOrigin σ n b
  | .inl ha => .inl (h ha)
  | .inr hs => .inr hs

theorem substOrigin_up {σ : Nat → Term} {n : Nat} {a : Bool} :
    SubstOrigin (Term.upVarSubst σ) n a → SubstOrigin σ n a
  | .inl h => .inl h
  | .inr ⟨0, h⟩ => by simp [Term.upVarSubst, Term.usesRef] at h
  | .inr ⟨i + 1, h⟩ =>
      .inr ⟨i, by simpa [Term.upVarSubst, usesRef_renameVar] using h⟩

mutual
theorem usesRef_substVar (σ : Nat → Term) (n : Nat) : ∀ t : Term,
    Term.usesRef n (Term.substVar σ t) = true → SubstOrigin σ n (Term.usesRef n t)
  | .var i, h => .inr ⟨i, h⟩
  | .nat _, h | .bool _, h | .bytes _, h | .digest _, h | .ref _, h | .refuse _ _, h => by
      simp [Term.substVar, Term.usesRef] at h
  | .lam A b, h => by
      exact substOrigin_up (usesRef_substVar (Term.upVarSubst σ) n b h)
  | .fix t, h => usesRef_substVar σ n t h
  | .get t l, h => usesRef_substVar σ n t h
  | .inj A l t, h => usesRef_substVar σ n t h
  | .app f a, h | .prim _ f a, h => by
      simp only [Term.substVar, Term.usesRef, Bool.or_eq_true] at h
      rcases h with h | h
      · exact (usesRef_substVar σ n f h).mono fun hu => by simp [Term.usesRef, hu]
      · exact (usesRef_substVar σ n a h).mono fun hu => by simp [Term.usesRef, hu]
  | .record fs, h => usesRef_substVarRow σ n fs h
  | .extend t fs, h => by
      simp only [Term.substVar, Term.usesRef, Bool.or_eq_true] at h
      rcases h with h | h
      · exact (usesRef_substVar σ n t h).mono fun hu => by simp [Term.usesRef, hu]
      · exact (usesRef_substVarRow σ n fs h).mono fun hu => by simp [Term.usesRef, hu]
  | .case t arms, h => by
      simp only [Term.substVar, Term.usesRef, Bool.or_eq_true] at h
      rcases h with h | h
      · exact (usesRef_substVar σ n t h).mono fun hu => by simp [Term.usesRef, hu]
      · exact (usesRef_substVarArms σ n arms h).mono fun hu => by simp [Term.usesRef, hu]
  | .ite c a b, h => by
      simp only [Term.substVar, Term.usesRef, Bool.or_eq_true] at h
      rcases h with (h | h) | h
      · exact (usesRef_substVar σ n c h).mono fun hu => by simp [Term.usesRef, hu]
      · exact (usesRef_substVar σ n a h).mono fun hu => by simp [Term.usesRef, hu]
      · exact (usesRef_substVar σ n b h).mono fun hu => by simp [Term.usesRef, hu]
  | .hole m ts, h => by
      simp only [Term.substVar, Term.usesRef, Bool.or_eq_true] at h
      rcases h with h | h
      · exact .inl (by simp [Term.usesRef, h])
      · exact (usesRef_substVarList σ n ts h).mono fun hu => by simp [Term.usesRef, hu]
theorem usesRef_substVarRow (σ : Nat → Term) (n : Nat) : ∀ fs : List (Label × Term),
    Term.usesRefRow n (Term.substVarRow σ fs) = true → SubstOrigin σ n (Term.usesRefRow n fs)
  | [], h => by simp [Term.substVarRow, Term.usesRefRow] at h
  | (_, t) :: ts, h => by
      simp only [Term.substVarRow, Term.usesRefRow, Bool.or_eq_true] at h
      rcases h with h | h
      · exact (usesRef_substVar σ n t h).mono fun hu => by simp [Term.usesRefRow, hu]
      · exact (usesRef_substVarRow σ n ts h).mono fun hu => by simp [Term.usesRefRow, hu]
theorem usesRef_substVarArms (σ : Nat → Term) (n : Nat) : ∀ fs : List (Label × Term),
    Term.usesRefRow n (Term.substVarArms σ fs) = true → SubstOrigin σ n (Term.usesRefRow n fs)
  | [], h => by simp [Term.substVarArms, Term.usesRefRow] at h
  | (_, t) :: ts, h => by
      simp only [Term.substVarArms, Term.usesRefRow, Bool.or_eq_true] at h
      rcases h with h | h
      · exact (substOrigin_up (usesRef_substVar (Term.upVarSubst σ) n t h)).mono
          fun hu => by simp [Term.usesRefRow, hu]
      · exact (usesRef_substVarArms σ n ts h).mono fun hu => by simp [Term.usesRefRow, hu]
theorem usesRef_substVarList (σ : Nat → Term) (n : Nat) : ∀ ts : List Term,
    Term.usesRefList n (Term.substVarList σ ts) = true → SubstOrigin σ n (Term.usesRefList n ts)
  | [], h => by simp [Term.substVarList, Term.usesRefList] at h
  | t :: ts, h => by
      simp only [Term.substVarList, Term.usesRefList, Bool.or_eq_true] at h
      rcases h with h | h
      · exact (usesRef_substVar σ n t h).mono fun hu => by simp [Term.usesRefList, hu]
      · exact (usesRef_substVarList σ n ts h).mono fun hu => by simp [Term.usesRefList, hu]
end

theorem substListFn_holes (n : Nat) : ∀ (ts : List Term) (i : Nat),
    Term.usesRef n (Term.substListFn ts i) = true → Term.usesRefList n ts = true
  | [], _, h => by simp [Term.substListFn, Term.usesRef] at h
  | t :: ts, 0, h => by simp [Term.usesRefList, show Term.usesRef n t = true from h]
  | t :: ts, i + 1, h => by
      have ih := substListFn_holes n ts i h
      simp [Term.usesRefList, ih]

theorem usesRef_substList (n : Nat) (ts : List Term) (t : Term)
    (h : Term.usesRef n (Term.substList ts t) = true) :
    Term.usesRef n t = true ∨ Term.usesRefList n ts = true := by
  rcases usesRef_substVar (Term.substListFn ts) n t h with h | ⟨i, hi⟩
  · exact .inl h
  · exact .inr (substListFn_holes n ts i hi)

/-- Where a hole surviving `fillRefs σ` comes from: an unfilled hole of the term, or a hole of the
filling selected for one of its holes. -/
def FillOrigin (σ : Nat → Option Term) (n : Nat) (u : Nat → Bool) : Prop :=
  (u n = true ∧ σ n = none) ∨ ∃ m M, u m = true ∧ σ m = some M ∧ Term.usesRef n M = true

theorem FillOrigin.mono {σ : Nat → Option Term} {n : Nat} {u u' : Nat → Bool}
    (hu : RefsSub u u') : FillOrigin σ n u → FillOrigin σ n u'
  | .inl ⟨h1, h2⟩ => .inl ⟨hu n h1, h2⟩
  | .inr ⟨m, M, h1, h2, h3⟩ => .inr ⟨m, M, hu m h1, h2, h3⟩

mutual
theorem usesRef_fillRefs (σ : Nat → Option Term) (n : Nat) : ∀ t : Term,
    Term.usesRef n (Term.fillRefs σ t) = true → FillOrigin σ n (fun m => Term.usesRef m t)
  | .ref _, h => by simp [Term.fillRefs, Term.usesRef] at h
  | .hole i ts, h => by
    cases hs : σ i with
    | none =>
      simp only [Term.fillRefs, hs, Term.usesRef, Bool.or_eq_true] at h
      rcases h with hi | ht
      · have he : i = n := by simpa using hi
        subst n
        exact .inl ⟨by simp [Term.usesRef], hs⟩
      · exact (usesRefList_fillRefsList σ n ts ht).mono fun m hm => by simp [Term.usesRef, hm]
    | some M =>
      simp only [Term.fillRefs, hs] at h
      rcases usesRef_substList n (Term.fillRefsList σ ts) M h with hm | ht
      · exact .inr ⟨i, M, by simp [Term.usesRef], hs, hm⟩
      · exact (usesRefList_fillRefsList σ n ts ht).mono fun m hm => by simp [Term.usesRef, hm]
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
theorem usesRefList_fillRefsList (σ : Nat → Option Term) (n : Nat) : ∀ fs : List Term,
    Term.usesRefList n (Term.fillRefsList σ fs) = true →
      FillOrigin σ n (fun m => Term.usesRefList m fs)
  | [], h => by simp [Term.fillRefsList, Term.usesRefList] at h
  | t :: fs, h => by
    simp only [Term.fillRefsList, Term.usesRefList, Bool.or_eq_true] at h
    rcases h with h | h
    · exact (usesRef_fillRefs σ n t h).mono fun m hm => by simp [Term.usesRefList, hm]
    · exact (usesRefList_fillRefsList σ n fs h).mono fun m hm => by simp [Term.usesRefList, hm]
end

end Nanodregg.Lang
