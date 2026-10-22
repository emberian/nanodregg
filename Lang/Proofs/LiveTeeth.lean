/-
# Lang.Proofs.LiveTeeth — counterexample teeth of the live checker, filling and law receiver

The successor teeth of the six superseded ref-model `fillRefs` contracts (subject: the deployed checker and
`fillRefs`), and the dormant/demanded-hole law teeth (subject: the deployed law loader). Leaf module.
-/
import Lang.Proofs.Fill
import Lang.Proofs.LawReceiver

namespace Nanodregg.Lang

/-! ## From `Lang.Proofs.Contextual.ContractTeeth`: Successor teeth for the six superseded ref-model statements. -/
section

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

end

/-! ## From `Lang.Proofs.Contextual.LawReceiverTeeth` -/
section

open Nanodregg.Kernel Nanodregg.Kernel.Receive

private def toothLaw (demand : Bool) : Term :=
  .lam (.record []) (.lam (.record []) (.lam reqTy
    (.ite (.bool demand) (.hole 0 []) Std.okT)))

private def toothPackage (demand : Bool) : Package :=
  { imports := [], state := .record [], iface := .record [("law", lawTy (.record []))],
    body := .record [("law", toothLaw demand)], methods := [], laws := ["law"],
    holes := [⟨0, [], verdictTy, [], 0, .empty, [], none, .bool true⟩] }

private def toothBytes (demand : Bool) : ByteArray :=
  (Wire.encodePackage (toothPackage demand)).getD .empty
private def toothCell (demand : Bool) : Cell :=
  { kind := kindPackage, discipline := .rom, slots := [(0, toothBytes demand)] }
private def toothLook (demand : Bool) : Pinned UInt8 := fun _ => .ok (some (toothCell demand))
private def toothDecode (_ : ByteArray) : Option UInt8 := some 7
private def toothEncode (d : UInt8) : ByteArray := ⟨#[d]⟩
private def toothReq : Req UInt8 :=
  { agent := 7, principal := 7, self := 7, notBefore := 0, validUntil := 0, occasion := .write }
private def toothAdmission (demand : Bool) : Except (Refusal UInt8) (Loaded × Nat) :=
  admitContextual toothDecode (fun _ => unresolvedBody) (toothEncode 7) (toothPackage demand) ⟨[],[],[]⟩ []
private def toothLoaded (demand : Bool) : Loaded × Nat :=
  (toothAdmission demand).toOption.getD (⟨[],[],[]⟩,0)

private theorem tooth_encodes (demand : Bool) :
    Wire.encodePackage (toothPackage demand) = some (toothBytes demand) := by
  cases demand <;> rfl

private theorem tooth_read (demand : Bool) :
    readPackage (toothLook demand) 7 = .ok (toothPackage demand) :=
  readPackage_installed (by rfl) (by rfl) (tooth_encodes demand)

private theorem tooth_load (demand : Bool) :
    loadContextual toothDecode (toothLook demand) closureDepthMax (toothEncode 7) ⟨[], [], []⟩ =
      .ok (toothLoaded demand) := by
  unfold loadContextual
  rw [loadUsing.eq_def]
  simp only [indexIn, closureDepthMax, idOf, toothDecode, tooth_read,
    show (toothPackage demand).imports = [] from rfl]
  rw [loadAllUsing.eq_def]
  change toothAdmission demand = .ok (toothLoaded demand)
  have hs : (toothAdmission demand).isOk = true := by cases demand <;> decide +kernel
  unfold toothLoaded
  cases ha : toothAdmission demand with
  | error e => rw [ha] at hs; cases hs
  | ok x => rfl

private theorem tooth_ok {x : Except (Refusal UInt8) Unit} (h : x.isOk = true) : x = .ok () := by
  cases x with
  | ok u => cases u; rfl
  | error e => cases h

private theorem tooth_denied {x : Except (Refusal UInt8) Unit}
    (h : (match x with
      | .error (.lawDenied k msg) => k == 7 && msg == "law: refused holeUnresolved"
      | _ => false) = true) :
    x = .error (.lawDenied 7 "law: refused holeUnresolved") := by
  split at h
  · simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  · cases h

/-- A real contextual law package admits with a dormant hole, and its ROM law
has the admitted meaning. This witnesses the generalized History bridge without
an empty-signature or no-hole premise. -/
theorem contextual_law_dormant_hole :
    ∃ (p : Package) (look : Pinned UInt8) (t : Term),
      p.holes ≠ [] ∧ readPackage look 7 = .ok p ∧
      p.body = .record [("law", t)] ∧ NoRef t ∧ Term.usesRef 0 t = true ∧
      (program toothEncode toothDecode).judge look (some 7) [] [] [] toothReq = .ok () ∧
      Std.Admits [] t (reqData toothEncode toothReq) (.record []) (.record []) := by
  have hj : judgeOneWith toothEncode toothDecode (loadContextual toothDecode)
      (toothLook false) 7 [] [] toothReq = .ok () := by
    unfold judgeOneWith
    rw [tooth_load]
    exact tooth_ok (by decide +kernel)
  refine ⟨toothPackage false, toothLook false, toothLaw false, by decide, tooth_read false,
    rfl, by trivial, rfl, ?_, ?_⟩
  · change judgeContextual toothEncode toothDecode (toothLook false) (some 7) [] [] [] toothReq = .ok ()
    simp [judgeContextual, hj, bind, Except.bind, pure, Except.pure]
  · obtain ⟨o, n, ho, hn, hall⟩ := judgeOneContextual_admits_relib toothEncode toothDecode
      rfl (tooth_read false) rfl hj
    have ho' : o = .record [] := by simpa [readState, readState.go, toothPackage, recordRow] using ho.symm
    have hn' : n = .record [] := by simpa [readState, readState.go, toothPackage, recordRow] using hn.symm
    subst o; subst n
    exact hall "law" (by simp [toothPackage]) (toothLaw false) rfl
      ⟨_, _, _, _, rfl⟩ (by trivial) []

/-- The same package demands its hole: the deployed judge refuses by name,
rather than manufacturing an admitted law from a blocked term. -/
theorem contextual_law_demanded_hole :
    (program toothEncode toothDecode).judge (toothLook true) (some 7) [] [] [] toothReq =
      .error (.lawDenied 7 "law: refused holeUnresolved") := by
  have hj : judgeOneWith toothEncode toothDecode (loadContextual toothDecode)
      (toothLook true) 7 [] [] toothReq = .error (.lawDenied 7 "law: refused holeUnresolved") := by
    unfold judgeOneWith
    rw [tooth_load]
    exact tooth_denied (by decide +kernel)
  change judgeContextual toothEncode toothDecode (toothLook true) (some 7) [] [] [] toothReq = _
  simp [judgeContextual, hj, bind, Except.bind]

end

end Nanodregg.Lang
