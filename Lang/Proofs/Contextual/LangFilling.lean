/- Signature transport and contextual filling for the deployed syntax. -/
import Lang.Proofs.Contextual.LangSubstitution

namespace Nanodregg.Lang.Contextual

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


end Nanodregg.Lang.Contextual
