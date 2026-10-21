/- Successor teeth for the six superseded ref-model statements. -/
import Lang.Proofs.Contextual.LangInstance

namespace Nanodregg.Lang.Contextual

private theorem identityCandidate_typed :
    ∀ n d M, ([⟨7, [.nat], .nat⟩] : HoleSignature).find? (fun e => e.name == n) = some d →
      (some (.var 0) : Option Term) = some M → HasType [] d.ctx M d.ty := by
  intro n d M hd hm
  have he := List.mem_of_find?_eq_some hd
  simp only [List.mem_singleton] at he
  subst d
  cases hm
  exact .var rfl

theorem fillHoles_term_tooth :
    HasType [] [] (Term.fillRefs (fun _ => some (.var 0)) (.hole 7 [.nat 9])) .nat ∧
      Term.fillRefs (fun _ => some (.var 0)) (.hole 7 [.nat 9]) = .nat 9 := by
  refine ⟨fillHoles_typed (Ω := [⟨7, [.nat], .nat⟩]) (fun _ => some (.var 0))
    identityCandidate_typed (by intro n d hd hn; cases hn)
    (.hole (d := ⟨7, [.nat], .nat⟩) rfl (.cons (.nat (by decide)) .nil)), rfl⟩

theorem fillHoles_fields_tooth :
    FieldsTy [] [] (Term.fillRefsRow (fun _ => some (.var 0))
      [("v", .hole 7 [.nat 9])]) [("v", .nat)] ∧
      Term.fillRefsRow (fun _ => some (.var 0)) [("v", .hole 7 [.nat 9])] = [("v", .nat 9)] := by
  refine ⟨fillHolesFields_typed (Ω := [⟨7, [.nat], .nat⟩]) (fun _ => some (.var 0))
    identityCandidate_typed (by intro n d hd hn; cases hn)
    (.cons (.hole (d := ⟨7, [.nat], .nat⟩) rfl (.cons (.nat (by decide)) .nil)) .nil), rfl⟩

theorem fillHoles_arms_tooth :
    ArmsTy [] [] (Term.fillRefsRow (fun _ => some (.var 0))
      [("v", .hole 7 [.prim .add (.var 0) (.nat 9)])]) [("v", .nat)] .nat ∧
      Term.fillRefsRow (fun _ => some (.var 0)) [("v", .hole 7 [.prim .add (.var 0) (.nat 9)])] = [("v", .prim .add (.var 0) (.nat 9))] := by
  refine ⟨fillHolesArms_typed (Ω := [⟨7, [.nat], .nat⟩]) (fun _ => some (.var 0))
    identityCandidate_typed (by intro n d hd hn; cases hn)
    (.one (.hole (d := ⟨7, [.nat], .nat⟩) rfl (.cons (.prim (.var rfl) (.nat (by decide))) .nil))), rfl⟩

theorem declaredHole_term_tooth :
    HasType [] [] (.hole 7 [.nat 9]) .nat [⟨7, [.nat], .nat⟩] ∧
      ¬ HasType [] [] (.hole 7 [.nat 9]) .nat := by
  refine ⟨.hole (d := ⟨7, [.nat], .nat⟩) rfl (.cons (.nat (by decide)) .nil), ?_⟩
  intro h
  have hd := hasType_declaresHole h 7 (by decide)
  simp at hd

theorem declaredHole_fields_tooth :
    FieldsTy [] [] [("v", .hole 7 [.nat 9])] [("v", .nat)] [⟨7, [.nat], .nat⟩] ∧
      ¬ FieldsTy [] [] [("v", .hole 7 [.nat 9])] [("v", .nat)] := by
  refine ⟨.cons (.hole (d := ⟨7, [.nat], .nat⟩) rfl (.cons (.nat (by decide)) .nil)) .nil, ?_⟩
  intro h
  have hd := fieldsTy_declaresHole h 7 (by decide)
  simp at hd

theorem declaredHole_arms_tooth :
    ArmsTy [] [] [("v", .hole 7 [.var 0])] [("v", .nat)] .nat [⟨7, [.nat], .nat⟩] ∧
      ¬ ArmsTy [] [] [("v", .hole 7 [.var 0])] [("v", .nat)] .nat := by
  refine ⟨.one (.hole (d := ⟨7, [.nat], .nat⟩) rfl (.cons (.var rfl) .nil)), ?_⟩
  intro h
  have hd := armsTy_declaresHole h 7 (by decide)
  simp at hd

/-- The reader's old premises hold, but live filling does not eliminate imports.
The new statement requires the SAME library on source and target; its instance
at the proposed empty target fails before the filling theorem can be applied. -/
theorem reader_import_contract_tooth :
    HasType [.nat] [] (.ref 0) .nat ∧
    (∀ (Γ : List Lang.Ty), HasType [] Γ (.nat 0) .nat) ∧
    Term.fillRefs (fun _ => some (.nat 0)) (.ref 0) = .ref 0 ∧
    ¬ HasType [] [] (.ref 0) .nat ∧
    ¬ HasType [] [] (Term.fillRefs (fun _ => some (.nat 0)) (.ref 0)) .nat := by
  refine ⟨.ref rfl, fun _ => .nat (by decide), rfl, ?_, ?_⟩
  all_goals
    intro h
    cases h with
    | ref h => simp at h

/-- An import remains an import under the new theorem, with the same library.
It is NOT reported as a contextual-hole occurrence. -/
theorem fillHoles_preserves_import_tooth :
    HasType [.nat] [] (Term.fillRefs (fun _ => some (.nat 0)) (.ref 0)) .nat ∧
      Term.usesRef 0 (.ref 0) = false := by
  refine ⟨fillHoles_typed (Ω := []) (Ω' := []) (fun _ => some (.nat 0))
    (by intro n d M hd; simp at hd)
    (by intro n d hd; simp at hd) (.ref rfl), rfl⟩

end Nanodregg.Lang.Contextual
