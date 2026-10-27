/-
# Lang.Proofs.StdOfferEscrow — what the escrow instance of `Std.offer` does at the deployed run (PROT-8)

Every theorem here is about `Lang.program`'s `run` of the generated package
`offerEscrowPackageOf theta roles ol sl pt b`, the run the kernel records:

* `escrow_take_run_sound`: a returned take decoded its deal, read both pinned offers, its own the
  one the deal names for it, found them `JointOk`, makes ONE call, its own offer's leg from the
  object to the peer's offer's `payTo` (`transfer (of self asset) (of payTo asset) amount`, no
  grant, no once key), and its row acts are exactly its own offer's retract and its session insert.
* `escrow_withdraw_run_sound`: a returned withdraw read its own pinned offer (present); its one call
  pays that offer's leg back to the offer's own `payTo`; its one row act is that offer's retract.
* `escrow_post_run_sound`: a returned post's one call moves the leg from the agent's account into
  the object's through the poster's grant; its one row act inserts exactly the offer value.
* `escrow_retract_moves_leg` (the linear corollary, over every method of the package): every
  retract of an offer row among a returned run's row acts comes with a call in the same result that
  transfers THAT row's leg out of the object, to the row's own `payTo` or to the `payTo` of the
  offer the run read under its peer (the escrow fuse retracts its own offer and pays its leg, as the
  take does). `post` only inserts.
* `escrow_take_iff_compliant`, `escrow_fuse_iff_compliant` (as the receiver applies them): with both
  offer slots present, the take and the fuse return iff `NamedKey`, `JointOk` and `LegsMatch` of the
  two pinned offers.

What leaves the object arrives in the named account by the kernel's conservation of every
denomination (`Kernel.Proofs.Value.admit_value`); this module states the CALL, not the transfer's
admission. Each run-grain theorem reads the generator's call term itself (the `calls` field of
`escrowTakeDone` / `escrowWithdrawDone` / the post's result), so a plant there reds it by name.
-/
import Lang.StdOfferEscrow
import Lang.Proofs.StdOfferFuse

namespace Nanodregg.Lang.Std

open Nanodregg.Lang

/-! ## The method table -/

private theorem slot_p1 : slotLabels "p" 1 = ["p0"] := by decide
private theorem slot_e1 : slotLabels "e" 1 = ["e0"] := by decide
private theorem slot_e2 : slotLabels "e" 2 = ["e0", "e1"] := by decide
private theorem slot_c1 : slotLabels "c" 1 = ["c0"] := by decide
private theorem slot_c2 : slotLabels "c" 2 = ["c0", "c1"] := by decide

private theorem calls1 : callSlotsOf [("c0", optTy escrowCallTy)] = some [escrowCallTy] := by decide

private theorem take_rowsOf (theta roles : List Label) (ol sl : Nat) :
    rowsOf (escrowRels theta roles ol sl) (offerTakeRows (escrowRels theta roles ol sl)) =
      some (offerRead, offerRead) := by
  simp [rowsOf, offerTakeRows, rowsTy, readsTy, offerRead, escrowRels, Row.find?, relReadTy, readsOf,
    relReadOf, relReadShape, peerLabel, slot_p1, Row.sort, Row.insert, pointsMax, rangeRowsMax]

private theorem withdraw_rowsOf (theta roles : List Label) (ol sl : Nat) :
    rowsOf (escrowRels theta roles ol sl) (escrowWithdrawRows (escrowRels theta roles ol sl)) =
      some (offerRead, []) := by
  simp [rowsOf, escrowWithdrawRows, rowsTy, readsTy, offerRead, escrowRels, Row.find?, relReadTy, readsOf,
    relReadOf, relReadShape, peerLabel, slot_p1, pointsMax, rangeRowsMax]

private theorem empty_rowsOf (theta roles : List Label) (ol sl : Nat) :
    rowsOf (escrowRels theta roles ol sl) (.record []) = some ([], []) := by
  simp [rowsOf, readsOf, readsTy, Row.find?]

private theorem take_resolve {D : Type} {theta roles : List Label} {ol sl pt b : Nat} {x : Label × Sig}
    (h : resolveMethod (D := D) (offerEscrowPackageOf theta roles ol sl pt b) offerTakeIx = .ok x) :
    x = ("take", ⟨offerTakeArg theta, [escrowCallTy], offerRead, 2⟩) := by
  have he : editSlotsOf (escrowRels theta roles ol sl)
      [("e0", optTy (editTy (escrowRels theta roles ol sl))), ("e1", optTy (editTy (escrowRels theta roles ol sl)))] =
      some 2 := by simp [editSlotsOf, editsMax, slot_e2]
  have hn : pairNamed (offerTakeArg theta) offerRead = true := by
    simp [pairNamed, offerTakeArg, Row.find?, offerRead]
  simp [resolveMethod, offerEscrowPackageOf, offerTakeIx, offerMethods, recordRow, Row.find?, methodSig, methodTy,
    resultTy, callsTy, slot_e2, slot_c1, calls1, he, take_rowsOf, hn] at h
  split at h
  · rename_i sg hsg
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    split at hsg
    · cases hsg; rfl
    · cases hsg
  · simp [throw, throwThe, MonadExceptOf.throw] at h

private theorem withdraw_resolve {D : Type} {theta roles : List Label} {ol sl pt b : Nat} {x : Label × Sig}
    (h : resolveMethod (D := D) (offerEscrowPackageOf theta roles ol sl pt b) offerWithdrawIx = .ok x) :
    x = ("withdraw", ⟨.record [], [escrowCallTy], offerRead, 1⟩) := by
  have he : editSlotsOf (escrowRels theta roles ol sl) [("e0", optTy (editTy (escrowRels theta roles ol sl)))] =
      some 1 := by simp [editSlotsOf, editsMax, slot_e1]
  simp [resolveMethod, offerEscrowPackageOf, offerWithdrawIx, offerMethods, recordRow, Row.find?, methodSig,
    methodTy, resultTy, callsTy, slot_e1, slot_c1, calls1, he, withdraw_rowsOf, pairNamed] at h
  split at h
  · rename_i sg hsg
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    split at hsg
    · cases hsg; rfl
    · cases hsg
  · simp [throw, throwThe, MonadExceptOf.throw] at h

private theorem post_resolve {D : Type} {theta roles : List Label} {ol sl pt b : Nat} {x : Label × Sig}
    (h : resolveMethod (D := D) (offerEscrowPackageOf theta roles ol sl pt b) offerPostIx = .ok x) :
    x = ("post", ⟨escrowPostArg theta roles, [escrowCallTy], [], 1⟩) := by
  have he : editSlotsOf (escrowRels theta roles ol sl) [("e0", optTy (editTy (escrowRels theta roles ol sl)))] =
      some 1 := by simp [editSlotsOf, editsMax, slot_e1]
  simp [resolveMethod, offerEscrowPackageOf, offerPostIx, offerMethods, recordRow, Row.find?, methodSig,
    methodTy, resultTy, callsTy, slot_e1, slot_c1, calls1, he, empty_rowsOf, pairNamed] at h
  split at h
  · rename_i sg hsg
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    split at hsg
    · cases hsg; rfl
    · cases hsg
  · simp [throw, throwThe, MonadExceptOf.throw] at h

private theorem retire_resolve {D : Type} {theta roles : List Label} {ol sl pt b : Nat} {x : Label × Sig}
    (h : resolveMethod (D := D) (offerEscrowPackageOf theta roles ol sl pt b) offerRetireIx = .ok x) :
    x = ("retire", ⟨keyTy (offerSessionDecl theta sl), [], [], 1⟩) := by
  have he : editSlotsOf (escrowRels theta roles ol sl) [("e0", optTy (editTy (escrowRels theta roles ol sl)))] =
      some 1 := by simp [editSlotsOf, editsMax, slot_e1]
  simp [resolveMethod, offerEscrowPackageOf, offerRetireIx, offerMethods, recordRow, Row.find?, methodSig,
    methodTy, resultTy, callsTy, activityRetireTy, slot_e1, he, empty_rowsOf, pairNamed] at h
  split at h
  · rename_i sg hsg
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    split at hsg
    · cases hsg; rfl
    · cases hsg
  · simp [throw, throwThe, MonadExceptOf.throw] at h

/-- The escrow package's `fuse` resolves to its signature: the deal with `via`, a transfer slot and an
invoke slot at the take's argument type, the one offer point read under itself and under its peer,
two edits (`escrow_fuse_run_sound`'s premise). -/
theorem escrow_fuse_resolve {D : Type} {theta roles : List Label} {ol sl pt b : Nat} {x : Label × Sig}
    (h : resolveMethod (D := D) (offerEscrowPackageOf theta roles ol sl pt b) offerFuseIx = .ok x) :
    x = ("fuse", ⟨offerFuseArg theta, [escrowCallTy, offerCallTy theta], offerRead, 2⟩) := by
  have he : editSlotsOf (escrowRels theta roles ol sl)
      [("e0", optTy (editTy (escrowRels theta roles ol sl))), ("e1", optTy (editTy (escrowRels theta roles ol sl)))] =
      some 2 := by simp [editSlotsOf, editsMax, slot_e2]
  have hn : pairNamed (offerFuseArg theta) offerRead = true := by
    simp [pairNamed, offerFuseArg, Row.find?, offerRead]
  have hc := callSlotsOf_two escrowCallTy (offerCallTy theta)
  rw [if_pos (by decide)] at hc
  by_cases hok : callSlotOk (offerCallTy theta) = true
  · rw [if_pos hok] at hc
    simp [resolveMethod, offerEscrowPackageOf, offerFuseIx, offerMethods, recordRow, Row.find?, methodSig, methodTy,
      resultTy, callsTy, slot_c2, slot_e2, hc, he, take_rowsOf, hn] at h
    split at h
    · rename_i sg hsg
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      split at hsg
      · cases hsg; rfl
      · cases hsg
    · simp [throw, throwThe, MonadExceptOf.throw] at h
  · rw [if_neg hok] at hc
    simp [resolveMethod, offerEscrowPackageOf, offerFuseIx, offerMethods, recordRow, Row.find?, methodSig, methodTy,
      resultTy, callsTy, slot_c2, slot_e2, hc, he, take_rowsOf, throw, throwThe, MonadExceptOf.throw] at h

private theorem escrow_fuse_peerReads (theta roles : List Label) (ol sl pt b : Nat) :
    (offerEscrowPackageOf theta roles ol sl pt b).peerReads "fuse" = offerRead := by
  simp [Package.peerReads, offerEscrowPackageOf, recordRow, Row.find?, methodPeer, methodTy, take_rowsOf]

/-- The package has five methods: no other index resolves. -/
private theorem resolve_lt {D : Type} {theta roles : List Label} {ol sl pt b m : Nat} {x : Label × Sig}
    (h : resolveMethod (D := D) (offerEscrowPackageOf theta roles ol sl pt b) (m + 5) = .ok x) : False := by
  simp [resolveMethod, offerEscrowPackageOf, offerMethods, throw, throwThe, MonadExceptOf.throw] at h

private theorem take_peerReads (theta roles : List Label) (ol sl pt b : Nat) :
    (offerEscrowPackageOf theta roles ol sl pt b).peerReads "take" = offerRead := by
  simp [Package.peerReads, offerEscrowPackageOf, recordRow, Row.find?, methodPeer, methodTy, take_rowsOf]

private theorem withdraw_peerReads (theta roles : List Label) (ol sl pt b : Nat) :
    (offerEscrowPackageOf theta roles ol sl pt b).peerReads "withdraw" = [] := by
  simp [Package.peerReads, offerEscrowPackageOf, recordRow, Row.find?, methodPeer, methodTy, withdraw_rowsOf]

private theorem retire_peerReads (theta roles : List Label) (ol sl pt b : Nat) :
    (offerEscrowPackageOf theta roles ol sl pt b).peerReads "retire" = [] := by
  simp [Package.peerReads, offerEscrowPackageOf, recordRow, Row.find?, methodPeer, methodTy, activityRetireTy,
    empty_rowsOf]

private theorem post_peerReads (theta roles : List Label) (ol sl pt b : Nat) :
    (offerEscrowPackageOf theta roles ol sl pt b).peerReads "post" = [] := by
  simp [Package.peerReads, offerEscrowPackageOf, recordRow, Row.find?, methodPeer, methodTy, empty_rowsOf]

/-! ## Relocation: the escrow's method terms name no closure package -/

private theorem noRef_take (theta roles : List Label) (rels : List (Label × RelDecl)) (od sd : RelDecl) :
    NoRef (activityMethod offerStateTy (offerTakeArg theta) (offerTakeRows rels) (escrowTakeBody theta roles rels od sd)) := by
  simp [activityMethod, escrowTakeBody, offerTakeTree, offerUnwrap, offerGate, escrowTakeDone, escrowResult, escrowPay, escrowTransfer,
    escrowAcct, escrowNoVia, offerTakeEdits, NoRef, NoRefRow, resultT, callsT, someCallT, activityEdit,
    activityKeyTerm, noCallT, slot_e2, slot_c1, activityApply, noRef_offerJoint, offerNamedOkT, offerNamedT, escrowFairT, escrowLegMeetsT, andT]

private theorem noRef_escrow_fuse (theta roles : List Label) (rels : List (Label × RelDecl)) (od sd : RelDecl)
    (budget : Nat) :
    NoRef (activityMethod offerStateTy (offerFuseArg theta) (offerTakeRows rels)
      (escrowFuseBody theta roles rels od sd budget)) := by
  simp [activityMethod, escrowFuseBody, offerTakeTree, offerUnwrap, offerGate, escrowFuseDone, activityResultCalls, escrowPay, escrowTransfer,
    escrowAcct, escrowNoVia, offerFuseCall, offerTakeCall, offerPeerT, offerTakeEdits, NoRef, NoRefRow, resultT,
    callsT, someCallT, activityEdit, activityKeyTerm, noCallT, slot_e2, slot_c2, activityApply, noRef_offerJoint,
    offerNamedOkT, offerNamedT, escrowFairT, escrowLegMeetsT, andT]

private theorem noRef_withdraw (rels : List (Label × RelDecl)) (od : RelDecl) :
    NoRef (activityMethod offerStateTy (.record []) (escrowWithdrawRows rels) (escrowWithdrawBody rels od)) := by
  simp [activityMethod, escrowWithdrawBody, escrowWithdrawDone, escrowResult, escrowPay, escrowTransfer, escrowAcct,
    escrowNoVia, NoRef, NoRefRow, resultT, callsT, someCallT, activityEdit, slot_e1, slot_c1]

private theorem noRef_post (theta roles : List Label) (rels : List (Label × RelDecl)) (od : RelDecl) :
    NoRef (activityMethod offerStateTy (escrowPostArg theta roles) (.record []) (escrowPostBody rels od)) := by
  simp [activityMethod, escrowPostBody, escrowResult, escrowTransfer, escrowAcct, NoRef, NoRefRow, resultT, callsT,
    someCallT, activityEdit, slot_e1, slot_c1]

private theorem noRef_retire (rels : List (Label × RelDecl)) (sd : RelDecl) :
    NoRef (offerRetireBody rels sd) := by
  simp [offerRetireBody, activityRetireMethod, activityMethod, activityResult, activityResultCalls, NoRef, NoRefRow,
    resultT, someCallT, activityEdit, activityKeyTerm, slot_e1]

/-! ## Shapes -/

/-- An escrow offer value: its leg, its `payTo`, its role and box. -/
theorem escrow_shape {theta roles : List Label} {o : Data} (h : Conforms o (escrowValTy theta roles)) :
    ∃ amt ab po ro ot wamt wab, o = .record [("give", .record [("amount", .nat amt), ("asset", .digest ab)]),
        ("payTo", .digest po), ("role", ro), ("terms", ot),
        ("want", .record [("amount", .nat wamt), ("asset", .digest wab)])] ∧
      Conforms ro (offerRoleTy roles) ∧ Conforms ot (offerTermsTy theta) := by
  unfold escrowValTy legTy at h
  cases h with
  | record hr =>
    cases hr with
    | cons h1 hr => cases hr with
      | cons h2 hr => cases hr with
        | cons h3 hr => cases hr with
          | cons h4 hr => cases hr with
            | cons h5 hr =>
            cases hr; cases h2
            cases h5 with
            | record hw => cases hw with
              | cons hwa hw => cases hw with
                | cons hwb hw =>
                cases hw; cases hwa; cases hwb
                cases h1 with
                | record hg => cases hg with
                  | cons ha hg => cases hg with
                    | cons hb hg => cases hg; cases ha; cases hb; exact ⟨_, _, _, _, _, _, _, rfl, h3, h4⟩

theorem escrow_fields {theta roles : List Label} {u : Data} (h : Conforms u (escrowValTy theta roles)) :
    (∃ ru, u.field "role" = some ru ∧ Conforms ru (offerRoleTy roles)) ∧
      (∃ tu, u.field "terms" = some tu ∧ Conforms tu (offerTermsTy theta)) := by
  obtain ⟨_, _, _, ro, ot, _, _, rfl, hro, hot⟩ := escrow_shape h
  exact ⟨⟨ro, by simp [Data.field, Row.find?], hro⟩, ⟨ot, by simp [Data.field, Row.find?], hot⟩⟩

private theorem withdraw_rows_cases {theta roles : List Label} {ol sl : Nat} {wd : Data}
    (h : Conforms wd (escrowWithdrawRows (escrowRels theta roles ol sl))) :
    ∃ X, wd = .record [("offer", .record [("p0", X)])] ∧
      Conforms X (optTy (pointRecTy (escrowDecl theta roles ol) false)) := by
  have ht : escrowWithdrawRows (escrowRels theta roles ol sl) =
      .record [("offer", .record [("p0", optTy (pointRecTy (escrowDecl theta roles ol) false))])] := by
    simp [escrowWithdrawRows, rowsTy, readsTy, offerRead, escrowRels, Row.find?, relReadTy, slot_p1]
  rw [ht] at h
  obtain ⟨P, rfl, hp⟩ := rec1_cases h
  obtain ⟨X, rfl, hx⟩ := rec1_cases hp
  exact ⟨X, rfl, hx⟩

/-! ## The legs (LANG-82) -/

/-- **What the escrow's compliance decides** (LANG-82, `escrowFairT`): what `q` gives meets what `o`
wants, and what `o` gives meets what `q` wants: the same denomination, at least the amount. -/
def LegsMatch (o q : Data) : Prop :=
  ∃ ga gb wa wb qa qb va vb, o.field "give" = some (escrowLegD ga gb) ∧ o.field "want" = some (escrowLegD wa wb) ∧
    q.field "give" = some (escrowLegD qa qb) ∧ q.field "want" = some (escrowLegD va vb) ∧
    qb = wb ∧ wa ≤ qa ∧ gb = vb ∧ va ≤ ga

private theorem meets_eval {lib : List Term} {env : Env} {g w : Term} {ga gb wa wb : _}
    (hg : BigStep lib env g (.ok (escrowLegD ga gb).toVal)) (hw : BigStep lib env w (.ok (escrowLegD wa wb).toVal)) :
    BigStep lib env (escrowLegMeetsT g w) (.ok (.bool (decide (gb = wb) && decide (wa ≤ ga)))) :=
  andT_eval
    (BigStep.prim (x := .digest gb) (y := .digest wb) (get_data (d := escrowLegD ga gb) (ℓ := "asset") (x := .digest gb) hg rfl)
      (get_data (d := escrowLegD wa wb) (ℓ := "asset") (x := .digest wb) hw rfl) (by simp [primEval]))
    (BigStep.prim (x := .nat wa) (y := .nat ga) (get_data (d := escrowLegD wa wb) (ℓ := "amount") (x := .nat wa) hw rfl)
      (get_data (d := escrowLegD ga gb) (ℓ := "amount") (x := .nat ga) hg rfl) (by simp [primEval]))

/-- The escrow's compliance evaluates, in any environment holding the peer's value at 1 and the own at
3 (the judge's `ok` arm), to a Boolean that is `true` exactly when the legs match. -/
theorem escrowFair_eval {theta roles : List Label} {lib : List Term} {env : Env} {o q : Data}
    (ho : Conforms o (escrowValTy theta roles)) (hq : Conforms q (escrowValTy theta roles))
    (h1 : env[1]? = some q.toVal) (h3 : env[3]? = some o.toVal) :
    ∃ b, BigStep lib env escrowFairT (.ok (.bool b)) ∧ (b = true ↔ LegsMatch o q) := by
  obtain ⟨ga, gb, po, ro, ot, wa, wb, rfl, -, -⟩ := escrow_shape ho
  obtain ⟨qa, qb, pq, rq, qt, va, vb, rfl, -, -⟩ := escrow_shape hq
  have hq1 : BigStep lib env (.var 1) (.ok (Data.record [("give", escrowLegD qa qb), ("payTo", .digest pq), ("role", rq),
      ("terms", qt), ("want", escrowLegD va vb)]).toVal) := .var h1
  have ho3 : BigStep lib env (.var 3) (.ok (Data.record [("give", escrowLegD ga gb), ("payTo", .digest po), ("role", ro),
      ("terms", ot), ("want", escrowLegD wa wb)]).toVal) := .var h3
  refine ⟨_, andT_eval (meets_eval (get_data hq1 rfl) (get_data ho3 rfl)) (meets_eval (get_data ho3 rfl) (get_data hq1 rfl)), ?_⟩
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨e1, l1⟩, e2, l2⟩
    exact ⟨ga, gb, wa, wb, qa, qb, va, vb, rfl, rfl, rfl, rfl, e1, l1, e2, l2⟩
  · rintro ⟨ga', gb', wa', wb', qa', qb', va', vb', h1, h2, h3, h4, e1, l1, e2, l2⟩
    have k1 : escrowLegD ga gb = escrowLegD ga' gb' := Option.some.inj h1
    have k2 : escrowLegD wa wb = escrowLegD wa' wb' := Option.some.inj h2
    have k3 : escrowLegD qa qb = escrowLegD qa' qb' := Option.some.inj h3
    have k4 : escrowLegD va vb = escrowLegD va' vb' := Option.some.inj h4
    simp [escrowLegD] at k1 k2 k3 k4
    obtain ⟨rfl, rfl⟩ := k1
    obtain ⟨rfl, rfl⟩ := k2
    obtain ⟨rfl, rfl⟩ := k3
    obtain ⟨rfl, rfl⟩ := k4
    exact ⟨⟨e1, l1⟩, e2, l2⟩

theorem escrow_fair_true {theta roles : List Label} {lib : List Term} {env : Env} {o q : Data}
    (ho : Conforms o (escrowValTy theta roles)) (hq : Conforms q (escrowValTy theta roles))
    (h1 : env[1]? = some q.toVal) (h3 : env[3]? = some o.toVal)
    (h : BigStep lib env escrowFairT (.ok (.bool true))) : LegsMatch o q := by
  obtain ⟨b, hb, hi⟩ := escrowFair_eval ho hq h1 h3
  have := bigStep_deterministic hb h
  simp only [Except.ok.injEq, Val.bool.injEq] at this
  exact hi.mp this

/-! ## The escrow's take and fuse, as the receiver applies them -/

/-- **Each escrow party's honesty** (the generated escrow `take` as the receiver applies it:
`apply4 g "take"` over `[req, arg, state, rows]`, at a `lib[g]` whose `take` is the generated method;
the escrow twin of `take_iff_compliant`): with both offer slots pinned and present, the take returns iff
its own pinned offer is the one the deal names for `self` (`NamedKey`), the two are `JointOk` at θ,
and their legs match (`LegsMatch`, LANG-82). Mutation P8j (the judge ignores the legs) makes it false
at LE7's unfair deal. -/
theorem escrow_take_iff_compliant {theta roles : List Label} {rels : List (Label × RelDecl)} {od sd : RelDecl}
    {lib : List Term} {g : Nat} {f : Nat → Nat} {fs : List (Label × Term)}
    {state : Val} {rq keys pair th k o kq q : Data} {sb : ByteArray}
    (hlib : lib[g]? = some ((Term.record fs).relocate f))
    (hf : Row.find? "take" fs = some (activityMethod offerStateTy (offerTakeArg theta) (offerTakeRows rels)
      (escrowTakeBody theta roles rels od sd)))
    (hR : (offerRoleTy roles).wf = true)
    (ho : Conforms o (escrowValTy theta roles)) (hq : Conforms q (escrowValTy theta roles))
    (hth : Conforms th (offerThetaTy theta)) (hself : rq.field "self" = some (.digest sb))
    (hkeys : Conforms keys offerKeysTy) (hpair : Conforms pair pairTy) (hk : Conforms k (.record [("n", .nat)])) :
    (∃ v, BigStep lib [rq.toVal, (Data.record [("keys", keys), ("pair", pair), ("theta", th)]).toVal, state,
        (Data.record [("offer", .record [("p0", .inj "some" (.record [("key", k), ("val", .inj "some" o)]))]),
          ("peer", .record [("offer", .record [("p0", .inj "some" (.record [("key", kq), ("val", .inj "some" q)]))])])]).toVal]
      (apply4 g "take") (.ok v)) ↔
    NamedKey sb keys pair k ∧ JointOk (offerLabels theta) o q th ∧ LegsMatch o q := by
  obtain ⟨r, hr, hiff⟩ := offerTakeTree_decides_fair (done := escrowTakeDone theta rels od sd) (tail := [])
    (lib := lib) (state := state) (kq := kq) rfl escrow_fields (fun _ h1 h3 => escrowFair_eval ho hq h1 h3)
    hR ho hq hth hself hkeys hpair hk
  have hap := apply4_method_iff hlib rfl hf (noRef_take _ _ _ _ _) hr
  rw [← hiff]
  exact ⟨fun ⟨v, hv⟩ => ⟨v, ((hap _).mp hv).symm⟩, fun ⟨v, e⟩ => ⟨v, (hap _).mpr e.symm⟩⟩

/-- **The escrow fuser's honesty** (the generated escrow `fuse` as the receiver applies it; the
twin of `escrow_take_iff_compliant` and `fuse_iff_compliant`): with both offer slots pinned and
present, the argument `{keys, pair, theta := th, via}`, the fuse returns iff `NamedKey`, `JointOk`
and `LegsMatch` of the two pinned offers: the first judge of every escrow fuse decides exactly what
the take decides, before it pays or calls. -/
theorem escrow_fuse_iff_compliant {theta roles : List Label} {rels : List (Label × RelDecl)} {od sd : RelDecl}
    {budget : Nat} {lib : List Term} {g : Nat} {f : Nat → Nat} {fs : List (Label × Term)}
    {state : Val} {rq keys pair th via k o kq q : Data} {sb : ByteArray}
    (hlib : lib[g]? = some ((Term.record fs).relocate f))
    (hf : Row.find? "fuse" fs = some (activityMethod offerStateTy (offerFuseArg theta) (offerTakeRows rels)
      (escrowFuseBody theta roles rels od sd budget)))
    (hR : (offerRoleTy roles).wf = true)
    (ho : Conforms o (escrowValTy theta roles)) (hq : Conforms q (escrowValTy theta roles))
    (hth : Conforms th (offerThetaTy theta)) (hself : rq.field "self" = some (.digest sb))
    (hkeys : Conforms keys offerKeysTy) (hpair : Conforms pair pairTy) (hk : Conforms k (.record [("n", .nat)])) :
    (∃ v, BigStep lib [rq.toVal, (Data.record [("keys", keys), ("pair", pair), ("theta", th), ("via", via)]).toVal,
        state, (Data.record [("offer", .record [("p0", .inj "some" (.record [("key", k), ("val", .inj "some" o)]))]),
          ("peer", .record [("offer", .record [("p0", .inj "some" (.record [("key", kq), ("val", .inj "some" q)]))])])]).toVal]
      (apply4 g "fuse") (.ok v)) ↔
    NamedKey sb keys pair k ∧ JointOk (offerLabels theta) o q th ∧ LegsMatch o q := by
  obtain ⟨r, hr, hiff⟩ := offerTakeTree_decides_fair (done := escrowFuseDone theta rels od sd budget)
    (tail := [("via", via)]) (lib := lib) (state := state) (kq := kq) rfl escrow_fields
    (fun _ h1 h3 => escrowFair_eval ho hq h1 h3) hR ho hq hth hself hkeys hpair hk
  have hap := apply4_method_iff hlib rfl hf (noRef_escrow_fuse _ _ _ _ _ _) hr
  rw [← hiff]
  exact ⟨fun ⟨v, hv⟩ => ⟨v, ((hap _).mp hv).symm⟩, fun ⟨v, e⟩ => ⟨v, (hap _).mpr e.symm⟩⟩

/-! ## The one transfer -/

private def transferTy : Ty :=
  .record [("amount", .nat), ("dst", acctRefTy), ("once", optTy .bytes), ("src", acctRefTy), ("via", optTy .digest)]

private theorem find_transfer : Row.find? "transfer" ((callArms none).filter fun a => ["transfer"].contains a.1) =
    some transferTy := by decide

private theorem find_of : Row.find? "of" [("of", Ty.record [("asset", .digest), ("owner", .digest)]), ("well", .digest)] =
    some (.record [("asset", .digest), ("owner", .digest)]) := by decide

/-- What a calls row holding `transfer amount (of src asset) (of dst asset) via` means. -/
private theorem transfer_means {lib : List Term} {env : Env} {amtT assetT srcT dstT viaT : Term}
    {amt : Nat} {ab sb db : ByteArray} {vd : Data} {W : Val}
    (ha : BigStep lib env amtT (.ok (.nat amt))) (hs : BigStep lib env srcT (.ok (.digest sb)))
    (hd : BigStep lib env dstT (.ok (.digest db))) (hab : BigStep lib env assetT (.ok (.digest ab)))
    (hv : BigStep lib env viaT (.ok vd.toVal)) (hvc : Conforms vd (optTy .digest))
    (hW : BigStep lib env (callsT [someCallT escrowCallTy
      (escrowTransfer amtT (escrowAcct srcT assetT) (escrowAcct dstT assetT) viaT)]) (.ok W)) :
    Means lib (callsTy [escrowCallTy]) W
      (.record [("c0", .inj "some" (.inj "transfer" (.record [("amount", .nat amt),
        ("dst", .inj "of" (.record [("asset", .digest ab), ("owner", .digest db)])),
        ("once", .inj "none" (.record [])),
        ("src", .inj "of" (.record [("asset", .digest ab), ("owner", .digest sb)])), ("via", vd)])))]) := by
  unfold callsT at hW
  cases hW
  simp only [callsTy, List.map, List.zip, List.length, suspend, escrowTransfer, escrowAcct]
  refine .record .record (.cons (.inj (.inj .record)) ?_ .nil)
  exact .inj rfl (.inj find_transfer (.record .record
    (.cons ha .nat
    (.cons (.inj .record) (.inj find_of (.record .record (.cons hab .digest (.cons hd .digest .nil))))
    (.cons (.inj .record) (.inj rfl (.record .record .nil))
    (.cons (.inj .record) (.inj find_of (.record .record (.cons hab .digest (.cons hs .digest .nil))))
    (.cons hv (means_toVal hvc) .nil)))))))

/-- The Body a transfer's call data reads as. -/
private theorem transfer_callsOf {D : Type} {digestOf : ByteArray → Option D} {amt : Nat} {ab sb db : ByteArray}
    {vd : Data} {calls : List (Kernel.Receive.Body D)}
    (h : callsOf digestOf [escrowCallTy] (.record [("c0", .inj "some" (.inj "transfer" (.record [("amount", .nat amt),
        ("dst", .inj "of" (.record [("asset", .digest ab), ("owner", .digest db)])),
        ("once", .inj "none" (.record [])),
        ("src", .inj "of" (.record [("asset", .digest ab), ("owner", .digest sb)])), ("via", vd)])))]) = .ok calls) :
    ∃ s' a' d' v', digestOf sb = some s' ∧ digestOf ab = some a' ∧ digestOf db = some d' ∧
      optOf (digestAt digestOf "via") "via" vd = .ok v' ∧ calls = [.transfer (.of s' a') (.of d' a') amt v' none] := by
  have hn : optOf (bytesAt "once") "once" (Data.inj "none" (.record [])) = (.ok none : Except String (Option ByteArray)) :=
    rfl
  cases h1 : digestOf sb <;> cases h2 : digestOf ab <;> cases h3 : digestOf db <;>
    cases h4 : optOf (digestAt digestOf "via") "via" vd <;>
    simp [callsOf, callsOf.go, bodyOf, acctRefOf, digestAt, natOf, h1, h2, h3, h4, hn, bind,
      Except.bind, pure, Except.pure, Except.map] at h
  exact ⟨_, _, _, _, rfl, rfl, rfl, rfl, h.symm⟩

/-! ## The take -/

/-- The take's `ok`-arm environment. -/
private abbrev takeOkEnv (rq keys pair th k o kq q : Data) (state : Val) : Env :=
  .record [] :: q.toVal :: (Data.record [("key", kq), ("val", .inj "some" q)]).toVal ::
    o.toVal :: (Data.record [("key", k), ("val", .inj "some" o)]).toVal :: rq.toVal ::
    (Data.record [("keys", keys), ("pair", pair), ("theta", th)]).toVal :: state ::
    (Data.record [("offer", .record [("p0", .inj "some" (.record [("key", k), ("val", .inj "some" o)]))]),
      ("peer", .record [("offer", .record [("p0", .inj "some" (.record [("key", kq), ("val", .inj "some" q)]))])])]).toVal ::
      []

/-- The take's run, all but reading its call off the generator: the call conjunct is stated under
the premise that the success term's `calls` field is the leg paid to the peer (each theorem below
discharges it against `escrowTakeDone` itself). -/
private theorem take_core {D : Type} [DecidableEq D] (bytesOf : D → ByteArray) (digestOf : ByteArray → Option D)
    {rc : Lang.ReceiptCheck} {theta roles : List Label} {ol sl pt budget : Nat}
    {look : Kernel.Receive.Pinned D} {rv : Kernel.Receive.RowView D} {pkg : D} {state : Kernel.Slots}
    {args : ByteArray} {r : Kernel.Receive.Req D} {budget' : Nat} {s : Kernel.Slots}
    {calls : List (Kernel.Receive.Body D)} {rows : List (Kernel.RowSlot D × Kernel.RowAct)} {used : Nat}
    (hR : (offerRoleTy roles).wf = true) (hid : digestOf (bytesOf pkg) = some pkg)
    (hp : readPackage look pkg = .ok (offerEscrowPackageOf theta roles ol sl pt budget))
    (h : (Lang.program bytesOf digestOf rc).run look rv pkg state offerTakeIx args r budget' =
      .ok (s, calls, rows, used)) :
    ∃ keys pair th k o kq q amt ab pb kb sb vb,
      Wire.decodeData (offerTakeArg theta) args = .ok (.record [("keys", keys), ("pair", pair), ("theta", th)]) ∧
      methodReads bytesOf digestOf rc look pkg (escrowRels theta roles ol sl) rv r.self
        (.record [("keys", keys), ("pair", pair), ("theta", th)]) offerRead offerRead =
        .ok (.record [("offer", .record [("p0", .inj "some" (.record [("key", k), ("val", .inj "some" o)]))]),
          ("peer", .record [("offer", .record [("p0", .inj "some" (.record [("key", kq), ("val", .inj "some" q)]))])])]) ∧
      NamedKey (bytesOf r.self) keys pair k ∧ JointOk (offerLabels theta) o q th ∧ LegsMatch o q ∧
      o.field "give" = some (.record [("amount", .nat amt), ("asset", .digest ab)]) ∧
      q.field "payTo" = some (.digest pb) ∧
      ((∀ fs, escrowTakeDone theta (escrowRels theta roles ol sl) (escrowDecl theta roles ol) (offerSessionDecl theta sl) =
          .record fs → Row.find? "calls" fs = some (callsT [someCallT escrowCallTy
            (escrowPay (.get (.var 5) "self") (.get (.var 1) "payTo") (.get (.var 3) "give"))])) →
        ∃ self' asset' payTo', digestOf (bytesOf r.self) = some self' ∧ digestOf ab = some asset' ∧
          digestOf pb = some payTo' ∧ calls = [.transfer (.of self' asset') (.of payTo' asset') amt none none]) ∧
      keyBytes (escrowDecl theta roles ol) k = some kb ∧
      keyBytes (offerSessionDecl theta sl)
        (.record [("agent", .digest (bytesOf r.agent)), ("notBefore", .nat r.notBefore)]) = some sb ∧
      Wire.encodeData (offerSessionDecl theta sl).val
        (.record [("answered", .inj "none" (.record [])),
          ("captured", .inj "settle" (.record [("pair", pair), ("theta", th)]))]) = some vb ∧
      rows = [(.row ⟨r.self, 0, kb⟩, .retract), (.row ⟨r.self, 1, sb⟩, .insert 0 vb)] := by
  change (runMeasuredLive bytesOf digestOf rc look rv pkg state offerTakeIx args r budget').map _ = _ at h
  rw [runMeasuredLive_leaf_closed hid hp rfl rfl] at h
  cases hm : runMeasured bytesOf digestOf rc look rv pkg state offerTakeIx args r budget' with
  | error e => rw [hm] at h; cases h
  | ok x =>
  rw [hm] at h
  obtain ⟨s', calls', rows', t', n'⟩ := x
  simp only [Except.map, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl, rfl⟩ := h
  obtain ⟨S, v, used, c, e, ds, left, es, hS, hrun, hx, hc, hes, hrows⟩ := runMeasured_inv hm
  obtain ⟨L, g, p, ℓ, sg, sd, ad, wd, -, hl, hpg, hres, -, had, -, hwd, rfl⟩ := runSetup_spec hS
  obtain ⟨hpg', f, hlib⟩ := load_top bytesOf digestOf (fuel := closureDepthMax - 1) hid hp hl
  rw [hpg'] at hpg
  cases hpg
  have hsig := take_resolve hres
  cases hsig
  rw [take_peerReads] at hwd
  simp only at hrun hx hes
  obtain ⟨keys, pair, th, rfl, hkeys, hpair, hth⟩ := offerTakeArg_cases (decodeData_conforms had)
  obtain ⟨X, Y, rfl, hX, hY⟩ := offerTakeRows_cases (methodReads_conforms hwd)
  have hbig := run_bigStep hrun
  have hself : (reqData bytesOf r).field "self" = some (.digest (bytesOf r.self)) := by
    simp [reqData, Data.field, Row.find?]
  have fwd : ∀ {r' : Except Fault Val}, BigStep L.lib
      [(reqData bytesOf r).toVal, (Data.record [("keys", keys), ("pair", pair), ("theta", th)]).toVal, sd.toVal,
        (Data.record [("offer", .record [("p0", X)]), ("peer", .record [("offer", .record [("p0", Y)])])]).toVal]
      (escrowTakeBody theta roles (escrowRels theta roles ol sl) (escrowDecl theta roles ol) (offerSessionDecl theta sl)) r' →
      BigStep L.lib [(reqData bytesOf r).toVal, (Data.record [("keys", keys), ("pair", pair), ("theta", th)]).toVal,
        sd.toVal, (Data.record [("offer", .record [("p0", X)]), ("peer", .record [("offer", .record [("p0", Y)])])]).toVal]
        (apply4 g "take") r' :=
    fun hb => apply4_method hlib rfl (by simp [Row.find?, activityMethod]) (noRef_take _ _ _ _ _) hb
  obtain ⟨fs, hfs⟩ : ∃ fs, escrowTakeDone theta (escrowRels theta roles ol sl) (escrowDecl theta roles ol)
      (offerSessionDecl theta sl) = .record fs := ⟨_, rfl⟩
  obtain ⟨k, o, kq, q, rfl, rfl, hk, ho, hq, hnk, hok, hfair, rfl⟩ :=
    offerTakeTree_inv escrow_fields hR rfl hth hself hkeys hpair hX hY hfs
      (fun f e k o kq q ho hq => by cases e; exact Exists.imp (fun _ h => h.1) (escrowFair_eval ho hq rfl rfl))
      fwd hbig
  have hlm := escrow_fair_true ho hq rfl rfl (hfair _ rfl)
  obtain ⟨amt, ab, po, ro, ot, _wa, _wb, hoe, -, -⟩ := escrow_shape ho
  obtain ⟨amtq, abq, pb, rq', qt, _qwa, _qwb, hqe, -, -⟩ := escrow_shape hq
  have hog : o.field "give" = some (.record [("amount", .nat amt), ("asset", .digest ab)]) := by rw [hoe]; rfl
  have hqp : q.field "payTo" = some (.digest pb) := by rw [hqe]; rfl
  have hM := extract_means _ _ hx
  -- the edits
  have hfE : Row.find? "edits" fs = some (.record ((slotLabels "e"
      (offerTakeEdits theta (escrowRels theta roles ol sl) (escrowDecl theta roles ol) (offerSessionDecl theta sl)).length).zip
      ((offerTakeEdits theta (escrowRels theta roles ol sl) (escrowDecl theta roles ol) (offerSessionDecl theta sl)).map
        fun t => someCallT (editTy (escrowRels theta roles ol sl)) t))) := by
    simp only [escrowTakeDone, escrowResult, resultT, Term.record.injEq] at hfs
    subst hfs; rfl
  have hwE := BigStep.get (ℓ := "edits") hbig (.field (find_suspend_of hfE) .record)
  obtain ⟨A, hA, hmA⟩ := means_get hbig hM rfl hwE
  simp [Row.find?] at hA
  subst hA
  have hED := offerTakeEdits_means (lib := L.lib) (od := escrowDecl theta roles ol) (sl := sl)
    (env := takeOkEnv (reqData bytesOf r) keys pair th k o kq q sd.toVal) rfl
    (get_data (BigStep.var (i := 4) rfl) rfl) hk
    (get_data (ℓ := "agent") (d := reqData bytesOf r) (x := .digest (bytesOf r.agent)) (BigStep.var (i := 5) rfl) rfl)
    (get_data (ℓ := "notBefore") (d := reqData bytesOf r) (x := .nat r.notBefore) (BigStep.var (i := 5) rfl) rfl)
    (get_data (BigStep.var (i := 6) rfl) rfl) hpair (get_data (BigStep.var (i := 6) rfl) rfl) hth .record
  have he := means_deterministic hmA hED
  subst he
  obtain ⟨kb, sb, vb, hkb, hsb, hvb, hmap⟩ := offerTake_editsOf (od := escrowDecl theta roles ol) rfl hes
  refine ⟨keys, pair, th, k, o, kq, q, amt, ab, pb, kb, sb, vb, had, hwd, hnk, hok, hlm, hog, hqp, ?_, hkb, hsb, hvb,
    hrows.trans hmap⟩
  -- the call, under the premise that the generator's `calls` field is the leg paid to the peer
  intro hcalls
  have hwC := BigStep.get (ℓ := "calls") hbig (.field (find_suspend_of (hcalls fs hfs)) .record)
  obtain ⟨A', hA', hmC⟩ := means_get hbig hM rfl hwC
  simp [Row.find?] at hA'
  subst hA'
  have hgive := get_data (ℓ := "give")
    (BigStep.var (i := 3) rfl (lib := L.lib) (env := takeOkEnv (reqData bytesOf r) keys pair th k o kq q sd.toVal)) hog
  have hce := means_deterministic hmC (transfer_means (vd := .inj "none" (.record []))
    (get_data (ℓ := "amount") (x := .nat amt) hgive rfl)
    (get_data (ℓ := "self") (x := .digest (bytesOf r.self)) (BigStep.var (i := 5) rfl) hself)
    (get_data (ℓ := "payTo") (x := .digest pb) (BigStep.var (i := 1) rfl) hqp)
    (get_data (ℓ := "asset") (x := .digest ab) hgive rfl)
    (.inj .record) (.inj rfl (.record .nil)) .record)
  subst hce
  obtain ⟨s', a', d', v', h1, h2, h3, h4, rfl⟩ := transfer_callsOf hc
  have hv' : v' = none := by simp [optOf] at h4; exact h4.symm
  subst hv'
  exact ⟨s', a', d', h1, h2, h3, rfl⟩

/-- **The deployed escrow take is sound** (`Lang.program`'s `run` of `take` of an object of the
generated escrow package): a run that RETURNED decoded the deal `{keys, pair, theta := th}`, read
(by the declared peer read) its own pinned offer `o` and its peer's `q`, its own the one the deal
names for `self` (`NamedKey`), found them `JointOk` at θ, makes exactly ONE call, `transfer (of self
asset) (of payTo asset) amount` with no grant and no once key, where `{amount, asset}` is its OWN
offer's leg and `payTo` the PEER's offer's, and its row acts are exactly the retract of its own offer
and the insert of its session row. Mutation P8d (the take pays nothing: its call slot `none`) makes
the call conjunct false: the run returns with no call. -/
theorem escrow_take_run_sound {D : Type} [DecidableEq D] (bytesOf : D → ByteArray) (digestOf : ByteArray → Option D)
    {rc : Lang.ReceiptCheck} {theta roles : List Label} {ol sl pt budget : Nat}
    {look : Kernel.Receive.Pinned D} {rv : Kernel.Receive.RowView D} {pkg : D} {state : Kernel.Slots}
    {args : ByteArray} {r : Kernel.Receive.Req D} {budget' : Nat} {s : Kernel.Slots}
    {calls : List (Kernel.Receive.Body D)} {rows : List (Kernel.RowSlot D × Kernel.RowAct)} {used : Nat}
    (hR : (offerRoleTy roles).wf = true) (hid : digestOf (bytesOf pkg) = some pkg)
    (hp : readPackage look pkg = .ok (offerEscrowPackageOf theta roles ol sl pt budget))
    (h : (Lang.program bytesOf digestOf rc).run look rv pkg state offerTakeIx args r budget' =
      .ok (s, calls, rows, used)) :
    ∃ keys pair th k o kq q amt ab pb self' asset' payTo' kb sb vb,
      Wire.decodeData (offerTakeArg theta) args = .ok (.record [("keys", keys), ("pair", pair), ("theta", th)]) ∧
      methodReads bytesOf digestOf rc look pkg (escrowRels theta roles ol sl) rv r.self
        (.record [("keys", keys), ("pair", pair), ("theta", th)]) offerRead offerRead =
        .ok (.record [("offer", .record [("p0", .inj "some" (.record [("key", k), ("val", .inj "some" o)]))]),
          ("peer", .record [("offer", .record [("p0", .inj "some" (.record [("key", kq), ("val", .inj "some" q)]))])])]) ∧
      NamedKey (bytesOf r.self) keys pair k ∧ JointOk (offerLabels theta) o q th ∧ LegsMatch o q ∧
      o.field "give" = some (.record [("amount", .nat amt), ("asset", .digest ab)]) ∧
      q.field "payTo" = some (.digest pb) ∧
      digestOf (bytesOf r.self) = some self' ∧ digestOf ab = some asset' ∧ digestOf pb = some payTo' ∧
      calls = [.transfer (.of self' asset') (.of payTo' asset') amt none none] ∧
      keyBytes (escrowDecl theta roles ol) k = some kb ∧
      keyBytes (offerSessionDecl theta sl)
        (.record [("agent", .digest (bytesOf r.agent)), ("notBefore", .nat r.notBefore)]) = some sb ∧
      Wire.encodeData (offerSessionDecl theta sl).val
        (.record [("answered", .inj "none" (.record [])),
          ("captured", .inj "settle" (.record [("pair", pair), ("theta", th)]))]) = some vb ∧
      rows = [(.row ⟨r.self, 0, kb⟩, .retract), (.row ⟨r.self, 1, sb⟩, .insert 0 vb)] := by
  obtain ⟨keys, pair, th, k, o, kq, q, amt, ab, pb, kb, sb, vb, hd, hm, hn, hj, hl, hg, hpb, hcall, hkb, hsb, hvb, hrows⟩ :=
    take_core bytesOf digestOf hR hid hp h
  obtain ⟨self', asset', payTo', h1, h2, h3, hc⟩ := hcall (fun fs hfs => by
    simp only [escrowTakeDone, escrowResult, resultT, Term.record.injEq] at hfs
    subst hfs; rfl)
  exact ⟨keys, pair, th, k, o, kq, q, amt, ab, pb, self', asset', payTo', kb, sb, vb, hd, hm, hn, hj, hl, hg, hpb,
    h1, h2, h3, hc, hkb, hsb, hvb, hrows⟩

/-! ## The escrow fuse: its leg paid, the peer's take invoked on the judged deal (LANG-77) -/

/-- The fuse's `ok`-arm environment (as `Lang.Proofs.StdOfferFuse` spells it, private there): payload 0, peer
value 1, peer point 2, own value 3, own point 4, request 5, argument 6, state 7, rows 8. -/
private abbrev fuseOkEnv (rq keys pair th via k o kq q : Data) (state : Val) : Env :=
  .record [] :: q.toVal :: (Data.record [("key", kq), ("val", .inj "some" q)]).toVal ::
    o.toVal :: (Data.record [("key", k), ("val", .inj "some" o)]).toVal :: rq.toVal ::
    (Data.record [("keys", keys), ("pair", pair), ("theta", th), ("via", via)]).toVal :: state ::
    (Data.record [("offer", .record [("p0", .inj "some" (.record [("key", k), ("val", .inj "some" o)]))]),
      ("peer", .record [("offer", .record [("p0", .inj "some" (.record [("key", kq), ("val", .inj "some" q)]))])])]).toVal ::
      []

/-- **What the escrow fuse's calls row means** in the `ok` arm: the own leg paid to the peer offer's
`payTo`, and one invoke of the peer's `take`, its argument the VALUE `{keys, pair, theta}`. -/
private theorem escrowFuseCalls_means {lib : List Term} {theta : List Label} {budget : Nat}
    {rq keys th via k o kq q : Data} {state : Val} {a b sb : ByteArray} {amt : Nat} {ab pb : ByteArray}
    (hself : rq.field "self" = some (.digest sb))
    (hog : o.field "give" = some (.record [("amount", .nat amt), ("asset", .digest ab)]))
    (hqp : q.field "payTo" = some (.digest pb))
    (hkeys : Conforms keys offerKeysTy)
    (hpair : Conforms (Data.record [("a", .digest a), ("b", .digest b)]) pairTy)
    (hth : Conforms th (offerThetaTy theta)) (hvia : Conforms via (optTy .digest)) {W : Val}
    (hW : BigStep lib (fuseOkEnv rq keys (.record [("a", .digest a), ("b", .digest b)]) th via k o kq q state)
      (callsT [someCallT escrowCallTy (escrowPay (.get (.var 5) "self") (.get (.var 1) "payTo") (.get (.var 3) "give")),
        someCallT (offerCallTy theta) (offerFuseCall theta budget (.var 5) (.var 6))]) (.ok W)) :
    Means lib (callsTy [escrowCallTy, offerCallTy theta]) W
      (.record [("c0", .inj "some" (.inj "transfer" (.record [("amount", .nat amt),
          ("dst", .inj "of" (.record [("asset", .digest ab), ("owner", .digest pb)])),
          ("once", .inj "none" (.record [])),
          ("src", .inj "of" (.record [("asset", .digest ab), ("owner", .digest sb)])),
          ("via", .inj "none" (.record []))]))),
        ("c1", .inj "some" (.inj "invoke" (.record [
          ("args", .record [("keys", keys), ("pair", .record [("a", .digest a), ("b", .digest b)]), ("theta", th)]),
          ("budget", .nat budget), ("method", .nat offerTakeIx),
          ("obj", .digest (if sb = a then b else a)), ("via", via)])))]) := by
  unfold callsT at hW
  cases hW
  simp only [callsTy, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, slot_c2, List.map, List.zip,
    suspend, escrowPay, escrowTransfer, escrowAcct, escrowNoVia, offerFuseCall, offerTakeCall]
  have hf : Row.find? "invoke" ((callArms (some (offerTakeArg theta))).filter
      fun x => x.1 == "invoke" || ([] : List Label).contains x.1) = some (invokeArm (offerTakeArg theta)) := rfl
  have hs : BigStep lib (fuseOkEnv rq keys (.record [("a", .digest a), ("b", .digest b)]) th via k o kq q state)
      (.get (.var 5) "self") (.ok (.digest sb)) :=
    get_data (x := .digest sb) (BigStep.var (i := 5) rfl) hself
  have hpa : BigStep lib (fuseOkEnv rq keys (.record [("a", .digest a), ("b", .digest b)]) th via k o kq q state)
      (.get (.var 6) "pair") (.ok (Data.record [("a", .digest a), ("b", .digest b)]).toVal) :=
    get_data (ℓ := "pair") (x := .record [("a", .digest a), ("b", .digest b)]) (BigStep.var (i := 6) rfl) rfl
  have hgive : BigStep lib (fuseOkEnv rq keys (.record [("a", .digest a), ("b", .digest b)]) th via k o kq q state)
      (.get (.var 3) "give") (.ok (Data.record [("amount", .nat amt), ("asset", .digest ab)]).toVal) :=
    get_data (x := .record [("amount", .nat amt), ("asset", .digest ab)]) (BigStep.var (i := 3) rfl) hog
  have hd : BigStep lib (fuseOkEnv rq keys (.record [("a", .digest a), ("b", .digest b)]) th via k o kq q state)
      (.get (.var 1) "payTo") (.ok (.digest pb)) :=
    get_data (x := .digest pb) (BigStep.var (i := 1) rfl) hqp
  refine .record .record (.cons (.inj (.inj .record)) ?_ (.cons (.inj (.inj .record)) ?_ .nil))
  · exact .inj rfl (.inj find_transfer (.record .record
      (.cons (get_data (ℓ := "amount") (x := .nat amt) hgive rfl) .nat
      (.cons (.inj .record) (.inj find_of (.record .record
        (.cons (get_data (ℓ := "asset") (x := .digest ab) hgive rfl) .digest (.cons hd .digest .nil))))
      (.cons (.inj .record) (.inj rfl (.record .record .nil))
      (.cons (.inj .record) (.inj find_of (.record .record
        (.cons (get_data (ℓ := "asset") (x := .digest ab) hgive rfl) .digest (.cons hs .digest .nil))))
      (.cons (.inj .record) (.inj rfl (.record .record .nil)) .nil)))))))
  · exact .inj rfl (.inj hf (.record .record
      (.cons .record (.record .record
        (.cons (get_data (ℓ := "keys") (x := keys) (BigStep.var (i := 6) rfl) rfl) (means_toVal hkeys)
        (.cons hpa (means_toVal hpair)
        (.cons (get_data (ℓ := "theta") (x := th) (BigStep.var (i := 6) rfl) rfl) (means_toVal hth) .nil))))
      (.cons .nat .nat (.cons .nat .nat
      (.cons (peerT_eval hs hpa) .digest
      (.cons (get_data (ℓ := "via") (x := via) (BigStep.var (i := 6) rfl) rfl) (means_toVal hvia) .nil)))))))

/-- **The deployed escrow fuse is sound** (`Lang.program`'s `run` of `fuse` of an object of the
generated escrow package): a run that RETURNED decoded `{keys, pair, theta := th, via}`, read (by the
declared peer read) its own pinned offer `o` and its peer's `q`, its own the one the deal names for
`self` (`NamedKey`), found them `JointOk` at θ, makes exactly TWO calls — `transfer (of self asset)
(of payTo asset) amount` of its OWN leg to the PEER offer's `payTo`, and `invoke p take db budget via'`
with `p` the peer and `db` the bytes of the VALUE `{keys, pair, theta}` (LANG-77) — and its row acts
are exactly the retract of its own offer and the insert of its session row. Mutations: the leg not
paid (its call slot `none`) and PT4 (the invoke dropped) each make the calls conjunct false. -/
theorem escrow_fuse_run_sound {D : Type} [DecidableEq D] (bytesOf : D → ByteArray) (digestOf : ByteArray → Option D)
    {rc : Lang.ReceiptCheck} {theta roles : List Label} {ol sl pt budget : Nat}
    {look : Kernel.Receive.Pinned D} {rv : Kernel.Receive.RowView D} {pkg : D} {state : Kernel.Slots}
    {args : ByteArray} {r : Kernel.Receive.Req D} {budget' : Nat} {s : Kernel.Slots}
    {calls : List (Kernel.Receive.Body D)} {rows : List (Kernel.RowSlot D × Kernel.RowAct)} {used : Nat}
    (hR : (offerRoleTy roles).wf = true) (hid : digestOf (bytesOf pkg) = some pkg)
    (hp : readPackage look pkg = .ok (offerEscrowPackageOf theta roles ol sl pt budget))
    (h : (Lang.program bytesOf digestOf rc).run look rv pkg state offerFuseIx args r budget' =
      .ok (s, calls, rows, used)) :
    ∃ keys pair th via k o kq q amt ab pb self' asset' payTo' p db via' kb sb vb,
      Wire.decodeData (offerFuseArg theta) args =
        .ok (.record [("keys", keys), ("pair", pair), ("theta", th), ("via", via)]) ∧
      methodReads bytesOf digestOf rc look pkg (escrowRels theta roles ol sl) rv r.self
        (.record [("keys", keys), ("pair", pair), ("theta", th), ("via", via)]) offerRead offerRead =
        .ok (.record [("offer", .record [("p0", .inj "some" (.record [("key", k), ("val", .inj "some" o)]))]),
          ("peer", .record [("offer", .record [("p0", .inj "some" (.record [("key", kq), ("val", .inj "some" q)]))])])]) ∧
      NamedKey (bytesOf r.self) keys pair k ∧ JointOk (offerLabels theta) o q th ∧ LegsMatch o q ∧
      o.field "give" = some (.record [("amount", .nat amt), ("asset", .digest ab)]) ∧
      q.field "payTo" = some (.digest pb) ∧
      digestOf (bytesOf r.self) = some self' ∧ digestOf ab = some asset' ∧ digestOf pb = some payTo' ∧
      Nanodregg.Lang.peerOf bytesOf digestOf r.self
        (.record [("keys", keys), ("pair", pair), ("theta", th), ("via", via)]) = .ok p ∧
      Wire.encodeData (offerTakeArg theta) (.record [("keys", keys), ("pair", pair), ("theta", th)]) = some db ∧
      ViaReads digestOf via via' ∧
      calls = [.transfer (.of self' asset') (.of payTo' asset') amt none none, .invoke p offerTakeIx db budget via'] ∧
      keyBytes (escrowDecl theta roles ol) k = some kb ∧
      keyBytes (offerSessionDecl theta sl)
        (.record [("agent", .digest (bytesOf r.agent)), ("notBefore", .nat r.notBefore)]) = some sb ∧
      Wire.encodeData (offerSessionDecl theta sl).val
        (.record [("answered", .inj "none" (.record [])),
          ("captured", .inj "settle" (.record [("pair", pair), ("theta", th)]))]) = some vb ∧
      rows = [(.row ⟨r.self, 0, kb⟩, .retract), (.row ⟨r.self, 1, sb⟩, .insert 0 vb)] := by
  change (runMeasuredLive bytesOf digestOf rc look rv pkg state offerFuseIx args r budget').map _ = _ at h
  rw [runMeasuredLive_leaf_closed hid hp rfl rfl] at h
  cases hm : runMeasured bytesOf digestOf rc look rv pkg state offerFuseIx args r budget' with
  | error e => rw [hm] at h; cases h
  | ok x =>
  rw [hm] at h
  obtain ⟨s', calls', rows', t', n'⟩ := x
  simp only [Except.map, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl, rfl⟩ := h
  obtain ⟨S, v, used, c, e, ds, left, es, hS, hrun, hx, hc, hes, hrows⟩ := runMeasured_inv hm
  obtain ⟨L, g, p, ℓ, sg, sd, ad, wd, -, hl, hpg, hres, -, had, -, hwd, rfl⟩ := runSetup_spec hS
  obtain ⟨hpg', f, hlib⟩ := load_top bytesOf digestOf (fuel := closureDepthMax - 1) hid hp hl
  rw [hpg'] at hpg
  cases hpg
  obtain ⟨mty, -, hA⟩ := resolveMethod_spec hres
  have hks := methodSig_slots hA
  have hsig := escrow_fuse_resolve hres
  cases hsig
  have hT : Wire.dataTy (offerTakeArg theta) = true :=
    callSlotOk_dataTy (hks _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))) _ (slotInvokeArg_offer theta)
  rw [escrow_fuse_peerReads] at hwd
  simp only at hrun hx hes
  obtain ⟨keys, pair, th, via, rfl, hkeys, hpair, hth, hvia⟩ := fuseArg_cases (decodeData_conforms had)
  obtain ⟨X, Y, rfl, hX, hY⟩ := offerTakeRows_cases (methodReads_conforms hwd)
  have hbig := run_bigStep hrun
  have hself : (reqData bytesOf r).field "self" = some (.digest (bytesOf r.self)) := by
    simp [reqData, Data.field, Row.find?]
  have fwd : ∀ {r' : Except Fault Val}, BigStep L.lib
      [(reqData bytesOf r).toVal, (Data.record [("keys", keys), ("pair", pair), ("theta", th), ("via", via)]).toVal, sd.toVal,
        (Data.record [("offer", .record [("p0", X)]), ("peer", .record [("offer", .record [("p0", Y)])])]).toVal]
      (escrowFuseBody theta roles (escrowRels theta roles ol sl) (escrowDecl theta roles ol) (offerSessionDecl theta sl) budget) r' →
      BigStep L.lib [(reqData bytesOf r).toVal, (Data.record [("keys", keys), ("pair", pair), ("theta", th), ("via", via)]).toVal,
        sd.toVal, (Data.record [("offer", .record [("p0", X)]), ("peer", .record [("offer", .record [("p0", Y)])])]).toVal]
        (apply4 g "fuse") r' :=
    fun hb => apply4_method hlib rfl (by simp [Row.find?, activityMethod]) (noRef_escrow_fuse _ _ _ _ _ _) hb
  obtain ⟨fs, hfs⟩ : ∃ fs, escrowFuseDone theta (escrowRels theta roles ol sl) (escrowDecl theta roles ol)
      (offerSessionDecl theta sl) budget = .record fs := ⟨_, rfl⟩
  obtain ⟨k, o, kq, q, rfl, rfl, hk, ho, hq, hnk, hok, hfair, rfl⟩ :=
    offerTakeTree_inv escrow_fields hR rfl hth hself hkeys hpair hX hY hfs
      (fun f e k o kq q ho hq => by cases e; exact Exists.imp (fun _ h => h.1) (escrowFair_eval ho hq rfl rfl))
      fwd hbig
  have hlm := escrow_fair_true ho hq rfl rfl (hfair _ rfl)
  obtain ⟨a, b, rfl⟩ := pair_shape hpair
  obtain ⟨amt, ab, po, ro, ot, _wa, _wb, hoe, -, -⟩ := escrow_shape ho
  obtain ⟨amtq, abq, pb, rq', qt, _qwa, _qwb, hqe, -, -⟩ := escrow_shape hq
  have hog : o.field "give" = some (.record [("amount", .nat amt), ("asset", .digest ab)]) := by rw [hoe]; rfl
  have hqp : q.field "payTo" = some (.digest pb) := by rw [hqe]; rfl
  have hM := extract_means _ _ hx
  -- the edits
  have hfE : Row.find? "edits" fs = some (.record ((slotLabels "e"
      (offerTakeEdits theta (escrowRels theta roles ol sl) (escrowDecl theta roles ol) (offerSessionDecl theta sl)).length).zip
      ((offerTakeEdits theta (escrowRels theta roles ol sl) (escrowDecl theta roles ol) (offerSessionDecl theta sl)).map
        fun t => someCallT (editTy (escrowRels theta roles ol sl)) t))) := by
    simp only [escrowFuseDone, activityResultCalls, resultT, Term.record.injEq] at hfs
    subst hfs; rfl
  have hwE := BigStep.get (ℓ := "edits") hbig (.field (find_suspend_of hfE) .record)
  obtain ⟨A, hA, hmA⟩ := means_get hbig hM rfl hwE
  simp [Row.find?] at hA
  subst hA
  have hED := offerTakeEdits_means (lib := L.lib) (od := escrowDecl theta roles ol) (sl := sl)
    (env := fuseOkEnv (reqData bytesOf r) keys (.record [("a", .digest a), ("b", .digest b)]) th via k o kq q sd.toVal) rfl
    (get_data (d := .record [("key", k), ("val", .inj "some" o)]) (BigStep.var (i := 4) rfl) rfl) hk
    (get_data (ℓ := "agent") (d := reqData bytesOf r) (x := .digest (bytesOf r.agent)) (BigStep.var (i := 5) rfl) rfl)
    (get_data (ℓ := "notBefore") (d := reqData bytesOf r) (x := .nat r.notBefore) (BigStep.var (i := 5) rfl) rfl)
    (get_data (ℓ := "pair") (x := .record [("a", .digest a), ("b", .digest b)]) (BigStep.var (i := 6) rfl) rfl) hpair
    (get_data (ℓ := "theta") (x := th) (BigStep.var (i := 6) rfl) rfl) hth .record
  have he := means_deterministic hmA hED
  subst he
  obtain ⟨kb, sb, vb, hkb, hsb, hvb, hmap⟩ := offerTake_editsOf (od := escrowDecl theta roles ol) rfl hes
  -- the calls
  have hfC : Row.find? "calls" fs = some (callsT [someCallT escrowCallTy
      (escrowPay (.get (.var 5) "self") (.get (.var 1) "payTo") (.get (.var 3) "give")),
      someCallT (offerCallTy theta) (offerFuseCall theta budget (.var 5) (.var 6))]) := by
    simp only [escrowFuseDone, activityResultCalls, resultT, Term.record.injEq] at hfs
    subst hfs; rfl
  have hwC := BigStep.get (ℓ := "calls") hbig (.field (find_suspend_of hfC) .record)
  obtain ⟨A', hA', hmC⟩ := means_get hbig hM rfl hwC
  simp [Row.find?] at hA'
  subst hA'
  have hce := means_deterministic hmC (escrowFuseCalls_means (budget := budget) (k := k) (o := o) (kq := kq) (q := q)
    (state := sd.toVal) hself hog hqp hkeys hpair hth hvia .record)
  subst hce
  obtain ⟨pr, A, B, hpeer, -, -, -⟩ := methodReads_offer hwd
  have hpd := peer_term (bytesOf := bytesOf) (digestOf := digestOf) (self := r.self) (a := a) (b := b)
    (args := .record [("keys", keys), ("pair", .record [("a", .digest a), ("b", .digest b)]), ("theta", th), ("via", via)])
    (by simp [Data.field, Row.find?]) hpeer
  have hdc : Conforms (Data.record [("keys", keys), ("pair", .record [("a", .digest a), ("b", .digest b)]), ("theta", th)])
      (offerTakeArg theta) := .record (.cons hkeys (.cons hpair (.cons hth .nil)))
  obtain ⟨db, hdb⟩ := encodeData_of_conforms hT hdc
  have hn : optOf (bytesAt "once") "once" (Data.inj "none" (.record [])) = (.ok none : Except String (Option ByteArray)) :=
    rfl
  have hnv : optOf (digestAt digestOf "via") "via" (Data.inj "none" (.record [])) = (.ok none : Except String (Option D)) :=
    rfl
  cases h1 : digestOf (bytesOf r.self) <;> cases h2 : digestOf ab <;> cases h3 : digestOf pb <;>
    cases hov : optOf (digestAt digestOf "via") "via" via <;>
    simp [callsOf, callsOf.go, bodyOf, acctRefOf, argsBytes, slotInvokeArg_offer, digestAt, natOf, hdb, hpd, h1, h2, h3,
      hov, hn, hnv, bind, Except.bind, pure, Except.pure, Except.map] at hc
  rename_i self' asset' payTo' via'
  exact ⟨keys, .record [("a", .digest a), ("b", .digest b)], th, via, k, o, kq, q, amt, ab, pb, self', asset', payTo', pr,
    db, via', kb, sb, vb, had, hwd, hnk, hok, hlm, hog, hqp, rfl, h2, h3, hpeer, hdb, viaReads_of hvia hov, hc.symm, hkb, hsb,
    hvb, hrows.trans hmap⟩

/-! ## The withdraw -/

private theorem wd_offerUnpinned {rels : List (Label × RelDecl)} {od : RelDecl} {lib : List Term} {E : Env}
    {req state : Val} {arg : Data} :
    BigStep lib (req :: arg.toVal :: state ::
        (Data.record [("offer", .record [("p0", .inj "none" (.record []))])]).toVal :: E)
      (escrowWithdrawBody rels od) (.error (.refused "offerUnpinned".toUTF8)) := by
  unfold escrowWithdrawBody; dsimp only
  exact .case (get_data (ℓ := "p0") (x := .inj "none" (.record [])) (get_data (ℓ := "offer") (x := .record [("p0", .inj "none" (.record []))])
    (BigStep.var (i := 3) rfl) rfl) rfl) rfl .refuse

private theorem wd_noOffer {rels : List (Label × RelDecl)} {od : RelDecl} {lib : List Term} {E : Env}
    {req state : Val} {arg k : Data} :
    BigStep lib (req :: arg.toVal :: state ::
        (Data.record [("offer", .record [("p0", .inj "some" (.record [("key", k), ("val", .inj "none" (.record []))]))])]).toVal :: E)
      (escrowWithdrawBody rels od) (.error (.refused "noOffer".toUTF8)) := by
  unfold escrowWithdrawBody; dsimp only
  refine .case (get_data (ℓ := "p0") (x := .inj "some" (.record [("key", k), ("val", .inj "none" (.record []))])) (get_data (ℓ := "offer") (x := .record [("p0", .inj "some" (.record [("key", k), ("val", .inj "none" (.record []))]))])
    (BigStep.var (i := 3) rfl) rfl) rfl) rfl ?_
  exact .case (get_data (ℓ := "val") (x := .inj "none" (.record [])) (BigStep.var (i := 0) rfl) rfl) rfl .refuse

private theorem wd_ok {rels : List (Label × RelDecl)} {od : RelDecl} {lib : List Term} {E : Env}
    {req state : Val} {arg k o : Data} {fs : List (Label × Term)} (hfs : escrowWithdrawDone rels od = .record fs) :
    BigStep lib (req :: arg.toVal :: state ::
        (Data.record [("offer", .record [("p0", .inj "some" (.record [("key", k), ("val", .inj "some" o)]))])]).toVal :: E)
      (escrowWithdrawBody rels od) (.ok (.record (suspend (o.toVal ::
        (Data.record [("key", k), ("val", .inj "some" o)]).toVal :: req :: arg.toVal :: state ::
        (Data.record [("offer", .record [("p0", .inj "some" (.record [("key", k), ("val", .inj "some" o)]))])]).toVal ::
          E) fs))) := by
  unfold escrowWithdrawBody; dsimp only
  refine .case (get_data (ℓ := "p0") (x := .inj "some" (.record [("key", k), ("val", .inj "some" o)])) (get_data (ℓ := "offer") (x := .record [("p0", .inj "some" (.record [("key", k), ("val", .inj "some" o)]))])
    (BigStep.var (i := 3) rfl) rfl) rfl) rfl ?_
  refine .case (get_data (ℓ := "val") (x := .inj "some" o) (BigStep.var (i := 0) rfl) rfl) rfl ?_
  rw [hfs]; exact .record

/-- The withdraw's run, all but reading its call off the generator (as `take_core`). -/
private theorem withdraw_core {D : Type} [DecidableEq D] (bytesOf : D → ByteArray) (digestOf : ByteArray → Option D)
    {rc : Lang.ReceiptCheck} {theta roles : List Label} {ol sl pt budget : Nat}
    {look : Kernel.Receive.Pinned D} {rv : Kernel.Receive.RowView D} {pkg : D} {state : Kernel.Slots}
    {args : ByteArray} {r : Kernel.Receive.Req D} {budget' : Nat} {s : Kernel.Slots}
    {calls : List (Kernel.Receive.Body D)} {rows : List (Kernel.RowSlot D × Kernel.RowAct)} {used : Nat}
    (hid : digestOf (bytesOf pkg) = some pkg)
    (hp : readPackage look pkg = .ok (offerEscrowPackageOf theta roles ol sl pt budget))
    (h : (Lang.program bytesOf digestOf rc).run look rv pkg state offerWithdrawIx args r budget' =
      .ok (s, calls, rows, used)) :
    ∃ k o amt ab po kb,
      Wire.decodeData (.record []) args = .ok (.record []) ∧
      methodReads bytesOf digestOf rc look pkg (escrowRels theta roles ol sl) rv r.self (.record []) offerRead [] =
        .ok (.record [("offer", .record [("p0", .inj "some" (.record [("key", k), ("val", .inj "some" o)]))])]) ∧
      o.field "give" = some (.record [("amount", .nat amt), ("asset", .digest ab)]) ∧
      o.field "payTo" = some (.digest po) ∧
      ((∀ fs, escrowWithdrawDone (escrowRels theta roles ol sl) (escrowDecl theta roles ol) = .record fs →
          Row.find? "calls" fs = some (callsT [someCallT escrowCallTy
            (escrowPay (.get (.var 2) "self") (.get (.var 0) "payTo") (.get (.var 0) "give"))])) →
        ∃ self' asset' to', digestOf (bytesOf r.self) = some self' ∧ digestOf ab = some asset' ∧
          digestOf po = some to' ∧ calls = [.transfer (.of self' asset') (.of to' asset') amt none none]) ∧
      keyBytes (escrowDecl theta roles ol) k = some kb ∧ rows = [(.row ⟨r.self, 0, kb⟩, .retract)] := by
  change (runMeasuredLive bytesOf digestOf rc look rv pkg state offerWithdrawIx args r budget').map _ = _ at h
  rw [runMeasuredLive_leaf_closed hid hp rfl rfl] at h
  cases hm : runMeasured bytesOf digestOf rc look rv pkg state offerWithdrawIx args r budget' with
  | error e => rw [hm] at h; cases h
  | ok x =>
  rw [hm] at h
  obtain ⟨s', calls', rows', t', n'⟩ := x
  simp only [Except.map, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl, rfl⟩ := h
  obtain ⟨S, v, used, c, e, ds, left, es, hS, hrun, hx, hc, hes, hrows⟩ := runMeasured_inv hm
  obtain ⟨L, g, p, ℓ, sg, sd, ad, wd, -, hl, hpg, hres, -, had, -, hwd, rfl⟩ := runSetup_spec hS
  obtain ⟨hpg', f, hlib⟩ := load_top bytesOf digestOf (fuel := closureDepthMax - 1) hid hp hl
  rw [hpg'] at hpg
  cases hpg
  have hsig := withdraw_resolve hres
  cases hsig
  rw [withdraw_peerReads] at hwd
  simp only at hrun hx hes
  obtain rfl := conforms_empty (decodeData_conforms had)
  obtain ⟨X, rfl, hX⟩ := withdraw_rows_cases (methodReads_conforms hwd)
  have hbig := run_bigStep hrun
  have fwd : ∀ {r' : Except Fault Val}, BigStep L.lib
      [(reqData bytesOf r).toVal, (Data.record []).toVal, sd.toVal, (Data.record [("offer", .record [("p0", X)])]).toVal]
      (escrowWithdrawBody (escrowRels theta roles ol sl) (escrowDecl theta roles ol)) r' →
      BigStep L.lib [(reqData bytesOf r).toVal, (Data.record []).toVal, sd.toVal,
        (Data.record [("offer", .record [("p0", X)])]).toVal] (apply4 g "withdraw") r' :=
    fun hb => apply4_method hlib rfl (by simp [Row.find?, activityMethod]) (noRef_withdraw _ _) hb
  rcases point_cases hX with rfl | ⟨k, hk, rfl | ⟨o, ho, rfl⟩⟩
  · cases bigStep_deterministic hbig (fwd wd_offerUnpinned)
  · cases bigStep_deterministic hbig (fwd wd_noOffer)
  obtain ⟨fs, hfs⟩ : ∃ fs, escrowWithdrawDone (escrowRels theta roles ol sl) (escrowDecl theta roles ol) = .record fs :=
    ⟨_, rfl⟩
  cases bigStep_deterministic hbig (fwd (wd_ok hfs))
  obtain ⟨amt, ab, po, ro, ot, _wa, _wb, hoe, -, -⟩ := escrow_shape ho
  have hog : o.field "give" = some (.record [("amount", .nat amt), ("asset", .digest ab)]) := by rw [hoe]; rfl
  have hop : o.field "payTo" = some (.digest po) := by rw [hoe]; rfl
  have hM := extract_means _ _ hx
  -- the edit
  have hfE : Row.find? "edits" fs = some (.record ((slotLabels "e" 1).zip
      [someCallT (editTy (escrowRels theta roles ol sl))
        (activityEdit (escrowRels theta roles ol sl) "offer" (escrowDecl theta roles ol) "retract" (.get (.var 1) "key"))])) := by
    simp only [escrowWithdrawDone, escrowResult, resultT, Term.record.injEq] at hfs
    subst hfs; rfl
  have hwE := BigStep.get (ℓ := "edits") hbig (.field (find_suspend_of hfE) .record)
  obtain ⟨A, hA, hmA⟩ := means_get hbig hM rfl hwE
  simp [Row.find?] at hA
  subst hA
  have hED : Means L.lib (.record ((slotLabels "e" 1).map fun l => (l, optTy (editTy (escrowRels theta roles ol sl)))))
      (.record (suspend (o.toVal :: (Data.record [("key", k), ("val", .inj "some" o)]).toVal :: (reqData bytesOf r).toVal ::
        (Data.record []).toVal :: sd.toVal ::
        (Data.record [("offer", .record [("p0", .inj "some" (.record [("key", k), ("val", .inj "some" o)]))])]).toVal :: [])
        ((slotLabels "e" 1).zip [someCallT (editTy (escrowRels theta roles ol sl))
          (activityEdit (escrowRels theta roles ol sl) "offer" (escrowDecl theta roles ol) "retract" (.get (.var 1) "key"))])))
      (.record [("e0", .inj "some" (.inj "offer" (.inj "retract" (.record [("key", k)]))))]) := by
    simp only [slot_e1, activityEdit, List.map, List.zip, List.zipWith, suspend, ↓reduceIte]
    refine .record .record (.cons (.inj (.inj (.inj .record))) ?_ .nil)
    exact .inj rfl (.inj rfl (.inj (A := .record [("key", keyTy (escrowDecl theta roles ol))])
      (by simp [escrowDecl, Row.find?]) (.record .record
        (.cons (get_data (BigStep.var (i := 1) rfl) rfl) (means_toVal hk) .nil))))
  have he := means_deterministic hmA hED
  subst he
  have i0 : List.findIdx? (fun x => decide (x.fst = "offer"))
      [("offer", escrowDecl theta roles ol), ("session", offerSessionDecl theta sl)] = some 0 := rfl
  have hr : (escrowDecl theta roles ol).retract = true := rfl
  rw [show (offerEscrowPackageOf theta roles ol sl pt budget).rels = escrowRels theta roles ol sl from rfl] at hes
  cases hkb : keyBytes (escrowDecl theta roles ol) k with
  | none =>
    simp [editsOf, editsOf.go, editOf, relIndex, i0, escrowRels, Row.find?, hkb, hr, bind, Except.bind] at hes
  | some kb =>
  simp [editsOf, editsOf.go, editOf, relIndex, i0, escrowRels, Row.find?, hkb, hr, bind, Except.bind, pure,
    Except.pure] at hes
  subst hes
  refine ⟨k, o, amt, ab, po, kb, had, hwd, hog, hop, ?_, hkb, hrows⟩
  intro hcalls
  have hwC := BigStep.get (ℓ := "calls") hbig (.field (find_suspend_of (hcalls fs hfs)) .record)
  obtain ⟨A', hA', hmC⟩ := means_get hbig hM rfl hwC
  simp [Row.find?] at hA'
  subst hA'
  have hgive := get_data (ℓ := "give") (BigStep.var (i := 0) rfl (lib := L.lib) (env := o.toVal ::
    (Data.record [("key", k), ("val", .inj "some" o)]).toVal :: (reqData bytesOf r).toVal :: (Data.record []).toVal ::
    sd.toVal :: (Data.record [("offer", .record [("p0", .inj "some" (.record [("key", k), ("val", .inj "some" o)]))])]).toVal ::
    [])) hog
  have hself : (reqData bytesOf r).field "self" = some (.digest (bytesOf r.self)) := by
    simp [reqData, Data.field, Row.find?]
  have hce := means_deterministic hmC (transfer_means (vd := .inj "none" (.record []))
    (get_data (ℓ := "amount") (x := .nat amt) hgive rfl)
    (get_data (ℓ := "self") (x := .digest (bytesOf r.self)) (BigStep.var (i := 2) rfl) hself)
    (get_data (ℓ := "payTo") (x := .digest po) (BigStep.var (i := 0) rfl) hop)
    (get_data (ℓ := "asset") (x := .digest ab) hgive rfl)
    (.inj .record) (.inj rfl (.record .nil)) .record)
  subst hce
  obtain ⟨s', a', d', v', h1, h2, h3, h4, rfl⟩ := transfer_callsOf hc
  have hv' : v' = none := by simp [optOf] at h4; exact h4.symm
  subst hv'
  exact ⟨s', a', d', h1, h2, h3, rfl⟩

/-! ## The retire (LANG-80) -/

private theorem key_arg_cases {theta : List Label} {sl : Nat} {ad : Data}
    (h : Conforms ad (keyTy (offerSessionDecl theta sl))) :
    ∃ ag nb, ad = .record [("agent", .digest ag), ("notBefore", .nat nb)] := by
  have hk : keyTy (offerSessionDecl theta sl) = .record [("agent", .digest), ("notBefore", .nat)] := rfl
  rw [hk] at h
  cases h with
  | record hr =>
  cases hr with | cons h1 hr => cases hr with | cons h2 hr =>
  cases hr; cases h1; cases h2
  exact ⟨_, _, rfl⟩

/-- The retire's run: its one row act is the retract of a SESSION row (relation 1), never of an
offer row, and it makes no call. -/
private theorem retire_core {D : Type} [DecidableEq D] (bytesOf : D → ByteArray) (digestOf : ByteArray → Option D)
    {rc : Lang.ReceiptCheck} {theta roles : List Label} {ol sl pt budget : Nat}
    {look : Kernel.Receive.Pinned D} {rv : Kernel.Receive.RowView D} {pkg : D} {state : Kernel.Slots}
    {args : ByteArray} {r : Kernel.Receive.Req D} {budget' : Nat} {s : Kernel.Slots}
    {calls : List (Kernel.Receive.Body D)} {rows : List (Kernel.RowSlot D × Kernel.RowAct)} {used : Nat}
    (hid : digestOf (bytesOf pkg) = some pkg)
    (hp : readPackage look pkg = .ok (offerEscrowPackageOf theta roles ol sl pt budget))
    (h : (Lang.program bytesOf digestOf rc).run look rv pkg state offerRetireIx args r budget' =
      .ok (s, calls, rows, used)) :
    ∃ kb, rows = [(.row ⟨r.self, 1, kb⟩, .retract)] := by
  change (runMeasuredLive bytesOf digestOf rc look rv pkg state offerRetireIx args r budget').map _ = _ at h
  rw [runMeasuredLive_leaf_closed hid hp rfl rfl] at h
  cases hm : runMeasured bytesOf digestOf rc look rv pkg state offerRetireIx args r budget' with
  | error e => rw [hm] at h; cases h
  | ok x =>
  rw [hm] at h
  obtain ⟨s', calls', rows', t', n'⟩ := x
  simp only [Except.map, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl, rfl⟩ := h
  obtain ⟨S, v, used, c, e, ds, left, es, hS, hrun, hx, hc, hes, hrows⟩ := runMeasured_inv hm
  obtain ⟨L, g, p, ℓ, sg, sd, ad, wd, -, hl, hpg, hres, -, had, -, hwd, rfl⟩ := runSetup_spec hS
  obtain ⟨hpg', f, hlib⟩ := load_top bytesOf digestOf (fuel := closureDepthMax - 1) hid hp hl
  rw [hpg'] at hpg
  cases hpg
  have hsig := retire_resolve hres
  cases hsig
  simp only at hrun hx hes
  obtain ⟨ag, nb, rfl⟩ := key_arg_cases (decodeData_conforms had)
  have hbig := run_bigStep hrun
  obtain ⟨fs, hfs⟩ : ∃ fs, activityResult (escrowRels theta roles ol sl) (.var 2)
      [activityEdit (escrowRels theta roles ol sl) "session" (offerSessionDecl theta sl) "retract"
        (activityKeyTerm (.get (.var 1) "agent") (.get (.var 1) "notBefore"))] = .record fs := ⟨_, rfl⟩
  have hval : BigStep L.lib [(reqData bytesOf r).toVal,
      (Data.record [("agent", .digest ag), ("notBefore", .nat nb)]).toVal, sd.toVal, wd.toVal]
      (activityResult (escrowRels theta roles ol sl) (.var 2)
        [activityEdit (escrowRels theta roles ol sl) "session" (offerSessionDecl theta sl) "retract"
          (activityKeyTerm (.get (.var 1) "agent") (.get (.var 1) "notBefore"))])
      (.ok (.record (suspend [(reqData bytesOf r).toVal,
        (Data.record [("agent", .digest ag), ("notBefore", .nat nb)]).toVal, sd.toVal, wd.toVal] fs))) := by
    rw [hfs]; exact .record
  cases bigStep_deterministic hbig (apply4_method hlib rfl
    (by simp [Row.find?, offerRetireBody, activityRetireMethod, activityMethod]) (noRef_retire _ _) hval)
  have hM := extract_means _ _ hx
  have hfE : Row.find? "edits" fs = some (.record ((slotLabels "e" 1).zip
      [someCallT (editTy (escrowRels theta roles ol sl))
        (activityEdit (escrowRels theta roles ol sl) "session" (offerSessionDecl theta sl) "retract"
          (activityKeyTerm (.get (.var 1) "agent") (.get (.var 1) "notBefore")))])) := by
    simp only [activityResult, activityResultCalls, resultT, Term.record.injEq] at hfs
    subst hfs; rfl
  have hwE := BigStep.get (ℓ := "edits") hbig (.field (find_suspend_of hfE) .record)
  obtain ⟨A, hA, hmA⟩ := means_get hbig hM rfl hwE
  simp [Row.find?] at hA
  subst hA
  have harg := BigStep.var (i := 1) rfl (lib := L.lib) (env := [(reqData bytesOf r).toVal,
      (Data.record [("agent", .digest ag), ("notBefore", .nat nb)]).toVal, sd.toVal, wd.toVal])
  have hED : Means L.lib (.record ((slotLabels "e" 1).map fun l => (l, optTy (editTy (escrowRels theta roles ol sl)))))
      (.record (suspend [(reqData bytesOf r).toVal,
        (Data.record [("agent", .digest ag), ("notBefore", .nat nb)]).toVal, sd.toVal, wd.toVal]
        ((slotLabels "e" 1).zip [someCallT (editTy (escrowRels theta roles ol sl))
          (activityEdit (escrowRels theta roles ol sl) "session" (offerSessionDecl theta sl) "retract"
            (activityKeyTerm (.get (.var 1) "agent") (.get (.var 1) "notBefore")))])))
      (.record [("e0", .inj "some" (.inj "session" (.inj "retract" (.record [("key",
        .record [("agent", .digest ag), ("notBefore", .nat nb)])]))))]) := by
    simp only [slot_e1, activityEdit, activityKeyTerm, List.map, List.zip, List.zipWith, suspend, ↓reduceIte]
    refine .record .record (.cons (.inj (.inj (.inj .record))) ?_ .nil)
    refine .inj rfl (.inj rfl (.inj (A := .record [("key", keyTy (offerSessionDecl theta sl))])
      (by simp [offerSessionDecl, activityLog, Row.find?]) (.record .record (.cons .record ?_ .nil))))
    have hkt : keyTy (offerSessionDecl theta sl) = .record [("agent", .digest), ("notBefore", .nat)] := rfl
    rw [hkt]
    exact .record .record (.cons (get_data harg rfl) .digest (.cons (get_data harg rfl) .nat .nil))
  have he := means_deterministic hmA hED
  subst he
  have i1 : List.findIdx? (fun x => decide (x.fst = "session"))
      [("offer", escrowDecl theta roles ol), ("session", offerSessionDecl theta sl)] = some 1 := rfl
  have hr : (offerSessionDecl theta sl).retract = true := rfl
  rw [show (offerEscrowPackageOf theta roles ol sl pt budget).rels = escrowRels theta roles ol sl from rfl] at hes
  cases hkb : keyBytes (offerSessionDecl theta sl) (.record [("agent", .digest ag), ("notBefore", .nat nb)]) with
  | none =>
    simp [editsOf, editsOf.go, editOf, relIndex, i1, escrowRels, Row.find?, hkb, hr, bind, Except.bind] at hes
  | some kb =>
  simp [editsOf, editsOf.go, editOf, relIndex, i1, escrowRels, Row.find?, hkb, hr, bind, Except.bind, pure,
    Except.pure] at hes
  subst hes
  exact ⟨kb, hrows⟩

/-- **The deployed escrow withdraw is sound** (`Lang.program`'s `run` of `withdraw`): a run that
RETURNED read its own pinned offer `o` (present: `offerUnpinned` and `noOffer` refuse), makes
exactly ONE call, paying `o`'s leg from the object back to `o`'s own `payTo` (`transfer (of self
asset) (of payTo asset) amount`, no grant, no once key), and its one row act is that offer's retract.
Mutation P8e (the withdraw pays nothing) makes the call conjunct false. -/
theorem escrow_withdraw_run_sound {D : Type} [DecidableEq D] (bytesOf : D → ByteArray) (digestOf : ByteArray → Option D)
    {rc : Lang.ReceiptCheck} {theta roles : List Label} {ol sl pt budget : Nat}
    {look : Kernel.Receive.Pinned D} {rv : Kernel.Receive.RowView D} {pkg : D} {state : Kernel.Slots}
    {args : ByteArray} {r : Kernel.Receive.Req D} {budget' : Nat} {s : Kernel.Slots}
    {calls : List (Kernel.Receive.Body D)} {rows : List (Kernel.RowSlot D × Kernel.RowAct)} {used : Nat}
    (hid : digestOf (bytesOf pkg) = some pkg)
    (hp : readPackage look pkg = .ok (offerEscrowPackageOf theta roles ol sl pt budget))
    (h : (Lang.program bytesOf digestOf rc).run look rv pkg state offerWithdrawIx args r budget' =
      .ok (s, calls, rows, used)) :
    ∃ k o amt ab po self' asset' to' kb,
      methodReads bytesOf digestOf rc look pkg (escrowRels theta roles ol sl) rv r.self (.record []) offerRead [] =
        .ok (.record [("offer", .record [("p0", .inj "some" (.record [("key", k), ("val", .inj "some" o)]))])]) ∧
      o.field "give" = some (.record [("amount", .nat amt), ("asset", .digest ab)]) ∧
      o.field "payTo" = some (.digest po) ∧
      digestOf (bytesOf r.self) = some self' ∧ digestOf ab = some asset' ∧ digestOf po = some to' ∧
      calls = [.transfer (.of self' asset') (.of to' asset') amt none none] ∧
      keyBytes (escrowDecl theta roles ol) k = some kb ∧ rows = [(.row ⟨r.self, 0, kb⟩, .retract)] := by
  obtain ⟨k, o, amt, ab, po, kb, -, hm, hg, hpo, hcall, hkb, hrows⟩ := withdraw_core bytesOf digestOf hid hp h
  obtain ⟨self', asset', to', h1, h2, h3, hc⟩ := hcall (fun fs hfs => by
    simp only [escrowWithdrawDone, escrowResult, resultT, Term.record.injEq] at hfs
    subst hfs; rfl)
  exact ⟨k, o, amt, ab, po, self', asset', to', kb, hm, hg, hpo, h1, h2, h3, hc, hkb, hrows⟩

/-! ## The post -/

private theorem post_arg_cases {theta roles : List Label} {ad : Data} (h : Conforms ad (escrowPostArg theta roles)) :
    ∃ amt ab grant n payTo role terms want,
      ad = .record [("give", .record [("amount", .nat amt), ("asset", .digest ab)]), ("grant", .digest grant),
        ("n", .nat n), ("payTo", payTo), ("role", role), ("terms", terms), ("want", want)] ∧
      Conforms (.record [("amount", .nat amt), ("asset", .digest ab)]) legTy ∧
      Conforms (.digest grant) .digest ∧ Conforms payTo .digest ∧ Conforms role (offerRoleTy roles) ∧
      Conforms terms (offerTermsTy theta) ∧ Conforms want legTy := by
  unfold escrowPostArg at h
  cases h with
  | record hr =>
  cases hr with | cons h1 hr => cases hr with | cons h2 hr => cases hr with | cons h3 hr => cases hr with
    | cons h4 hr => cases hr with | cons h5 hr => cases hr with | cons h6 hr => cases hr with | cons h7 hr =>
  cases hr
  have hg := h1
  have hgr := h2
  unfold legTy at h1
  cases h1 with | record hg' => cases hg' with | cons ha hg' => cases hg' with | cons hb hg' =>
  cases hg'; cases ha; cases hb; cases h2; cases h3
  exact ⟨_, _, _, _, _, _, _, _, rfl, hg, hgr, h4, h5, h6, h7⟩

/-- The post's run, all but reading its call off the generator. -/
private theorem post_core {D : Type} [DecidableEq D] (bytesOf : D → ByteArray) (digestOf : ByteArray → Option D)
    {rc : Lang.ReceiptCheck} {theta roles : List Label} {ol sl pt budget : Nat}
    {look : Kernel.Receive.Pinned D} {rv : Kernel.Receive.RowView D} {pkg : D} {state : Kernel.Slots}
    {args : ByteArray} {r : Kernel.Receive.Req D} {budget' : Nat} {s : Kernel.Slots}
    {calls : List (Kernel.Receive.Body D)} {rows : List (Kernel.RowSlot D × Kernel.RowAct)} {used : Nat}
    (hid : digestOf (bytesOf pkg) = some pkg)
    (hp : readPackage look pkg = .ok (offerEscrowPackageOf theta roles ol sl pt budget))
    (h : (Lang.program bytesOf digestOf rc).run look rv pkg state offerPostIx args r budget' =
      .ok (s, calls, rows, used)) :
    ∃ amt ab grant n payTo role terms want kb vb,
      Wire.decodeData (escrowPostArg theta roles) args = .ok (.record [
        ("give", .record [("amount", .nat amt), ("asset", .digest ab)]), ("grant", .digest grant), ("n", .nat n),
        ("payTo", payTo), ("role", role), ("terms", terms), ("want", want)]) ∧
      ((∀ fs, escrowPostBody (escrowRels theta roles ol sl) (escrowDecl theta roles ol) = .record fs →
          Row.find? "calls" fs = some (callsT [someCallT escrowCallTy
            (escrowTransfer (.get (.get (.var 1) "give") "amount")
              (escrowAcct (.get (.var 0) "agent") (.get (.get (.var 1) "give") "asset"))
              (escrowAcct (.get (.var 0) "self") (.get (.get (.var 1) "give") "asset"))
              (.inj (optTy .digest) "some" (.get (.var 1) "grant")))])) →
        ∃ agent' self' asset' grant', digestOf (bytesOf r.agent) = some agent' ∧
          digestOf (bytesOf r.self) = some self' ∧ digestOf ab = some asset' ∧ digestOf grant = some grant' ∧
          calls = [.transfer (.of agent' asset') (.of self' asset') amt (some grant') none]) ∧
      keyBytes (escrowDecl theta roles ol) (.record [("n", .nat n)]) = some kb ∧
      Wire.encodeData (escrowDecl theta roles ol).val (.record [
        ("give", .record [("amount", .nat amt), ("asset", .digest ab)]), ("payTo", payTo), ("role", role),
        ("terms", terms), ("want", want)]) = some vb ∧
      rows = [(.row ⟨r.self, 0, kb⟩, .insert 0 vb)] := by
  change (runMeasuredLive bytesOf digestOf rc look rv pkg state offerPostIx args r budget').map _ = _ at h
  rw [runMeasuredLive_leaf_closed hid hp rfl rfl] at h
  cases hm : runMeasured bytesOf digestOf rc look rv pkg state offerPostIx args r budget' with
  | error e => rw [hm] at h; cases h
  | ok x =>
  rw [hm] at h
  obtain ⟨s', calls', rows', t', n'⟩ := x
  simp only [Except.map, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl, rfl⟩ := h
  obtain ⟨S, v, used, c, e, ds, left, es, hS, hrun, hx, hc, hes, hrows⟩ := runMeasured_inv hm
  obtain ⟨L, g, p, ℓ, sg, sd, ad, wd, -, hl, hpg, hres, -, had, -, hwd, rfl⟩ := runSetup_spec hS
  obtain ⟨hpg', f, hlib⟩ := load_top bytesOf digestOf (fuel := closureDepthMax - 1) hid hp hl
  rw [hpg'] at hpg
  cases hpg
  have hsig := post_resolve hres
  cases hsig
  simp only at hrun hx hes
  obtain ⟨amt, ab, grant, n, payTo, role, terms, want, rfl, hgc, hgrc, h4, h5, h6, h7⟩ :=
    post_arg_cases (decodeData_conforms had)
  have hbig := run_bigStep hrun
  obtain ⟨fs, hfs⟩ : ∃ fs, escrowPostBody (escrowRels theta roles ol sl) (escrowDecl theta roles ol) = .record fs :=
    ⟨_, rfl⟩
  have hval : BigStep L.lib [(reqData bytesOf r).toVal, (Data.record [
      ("give", .record [("amount", .nat amt), ("asset", .digest ab)]), ("grant", .digest grant), ("n", .nat n),
      ("payTo", payTo), ("role", role), ("terms", terms), ("want", want)]).toVal, sd.toVal, wd.toVal]
      (escrowPostBody (escrowRels theta roles ol sl) (escrowDecl theta roles ol))
      (.ok (.record (suspend [(reqData bytesOf r).toVal, (Data.record [
        ("give", .record [("amount", .nat amt), ("asset", .digest ab)]), ("grant", .digest grant), ("n", .nat n),
        ("payTo", payTo), ("role", role), ("terms", terms), ("want", want)]).toVal, sd.toVal, wd.toVal] fs))) := by
    rw [hfs]; exact .record
  cases bigStep_deterministic hbig (apply4_method hlib rfl (by simp [Row.find?, activityMethod]) (noRef_post theta roles _ _) hval)
  have hM := extract_means _ _ hx
  have hfE : Row.find? "edits" fs = some (.record ((slotLabels "e" 1).zip
      [someCallT (editTy (escrowRels theta roles ol sl))
        (activityEdit (escrowRels theta roles ol sl) "offer" (escrowDecl theta roles ol) "insert"
          (.record [("n", .get (.var 1) "n")])
          (.record [("give", .get (.var 1) "give"), ("payTo", .get (.var 1) "payTo"), ("role", .get (.var 1) "role"),
            ("terms", .get (.var 1) "terms"), ("want", .get (.var 1) "want")]))])) := by
    simp only [escrowPostBody, escrowResult, resultT, Term.record.injEq] at hfs
    subst hfs; rfl
  have hwE := BigStep.get (ℓ := "edits") hbig (.field (find_suspend_of hfE) .record)
  obtain ⟨A, hA, hmA⟩ := means_get hbig hM rfl hwE
  simp [Row.find?] at hA
  subst hA
  have harg := BigStep.var (i := 1) rfl (lib := L.lib) (env := [(reqData bytesOf r).toVal, (Data.record [
      ("give", .record [("amount", .nat amt), ("asset", .digest ab)]), ("grant", .digest grant), ("n", .nat n),
      ("payTo", payTo), ("role", role), ("terms", terms), ("want", want)]).toVal, sd.toVal, wd.toVal])
  have hED : Means L.lib (.record ((slotLabels "e" 1).map fun l => (l, optTy (editTy (escrowRels theta roles ol sl)))))
      (.record (suspend [(reqData bytesOf r).toVal, (Data.record [
        ("give", .record [("amount", .nat amt), ("asset", .digest ab)]), ("grant", .digest grant), ("n", .nat n),
        ("payTo", payTo), ("role", role), ("terms", terms), ("want", want)]).toVal, sd.toVal, wd.toVal]
        ((slotLabels "e" 1).zip [someCallT (editTy (escrowRels theta roles ol sl))
          (activityEdit (escrowRels theta roles ol sl) "offer" (escrowDecl theta roles ol) "insert"
            (.record [("n", .get (.var 1) "n")])
            (.record [("give", .get (.var 1) "give"), ("payTo", .get (.var 1) "payTo"), ("role", .get (.var 1) "role"),
              ("terms", .get (.var 1) "terms"), ("want", .get (.var 1) "want")]))])))
      (.record [("e0", .inj "some" (.inj "offer" (.inj "insert" (.record [("key", .record [("n", .nat n)]),
        ("val", .record [("give", .record [("amount", .nat amt), ("asset", .digest ab)]), ("payTo", payTo),
          ("role", role), ("terms", terms), ("want", want)])]))))]) := by
    simp only [slot_e1, activityEdit, List.map, List.zip, List.zipWith, suspend]
    refine .record .record (.cons (.inj (.inj (.inj .record))) ?_ .nil)
    refine .inj rfl (.inj rfl (.inj (A := rowTy (escrowDecl theta roles ol)) (by simp [Row.find?]) (.record .record
      (.cons .record ?_ (.cons .record ?_ .nil)))))
    · have hkt : keyTy (escrowDecl theta roles ol) = .record [("n", .nat)] := rfl
      rw [hkt]
      exact .record .record (.cons (get_data harg rfl) .nat .nil)
    · exact .record .record (.cons (get_data harg rfl) (means_toVal hgc)
        (.cons (get_data harg rfl) (means_toVal h4) (.cons (get_data harg rfl) (means_toVal h5)
          (.cons (get_data harg rfl) (means_toVal h6) (.cons (get_data harg rfl) (means_toVal h7) .nil)))))
  have he := means_deterministic hmA hED
  subst he
  have i0 : List.findIdx? (fun x => decide (x.fst = "offer"))
      [("offer", escrowDecl theta roles ol), ("session", offerSessionDecl theta sl)] = some 0 := rfl
  have ha : amtOf (escrowDecl theta roles ol) (.record [("give", .record [("amount", .nat amt), ("asset", .digest ab)]),
      ("payTo", payTo), ("role", role), ("terms", terms), ("want", want)]) = 0 := rfl
  rw [show (offerEscrowPackageOf theta roles ol sl pt budget).rels = escrowRels theta roles ol sl from rfl] at hes
  cases hkb : keyBytes (escrowDecl theta roles ol) (.record [("n", .nat n)]) with
  | none =>
    simp [editsOf, editsOf.go, editOf, relIndex, i0, escrowRels, Row.find?, hkb, bind, Except.bind] at hes
  | some kb =>
  cases hvb : Wire.encodeData (escrowDecl theta roles ol).val (.record [("give", .record [("amount", .nat amt),
      ("asset", .digest ab)]), ("payTo", payTo), ("role", role), ("terms", terms), ("want", want)]) with
  | none =>
    simp [editsOf, editsOf.go, editOf, relIndex, i0, escrowRels, Row.find?, hkb, hvb, bind, Except.bind] at hes
  | some vb =>
  simp [editsOf, editsOf.go, editOf, relIndex, i0, escrowRels, Row.find?, hkb, hvb, ha, bind, Except.bind, pure,
    Except.pure] at hes
  subst hes
  refine ⟨amt, ab, grant, n, payTo, role, terms, want, kb, vb, had, ?_, hkb, hvb, hrows⟩
  intro hcalls
  have hwC := BigStep.get (ℓ := "calls") hbig (.field (find_suspend_of (hcalls fs hfs)) .record)
  obtain ⟨A', hA', hmC⟩ := means_get hbig hM rfl hwC
  simp [Row.find?] at hA'
  subst hA'
  have hgive := get_data (ℓ := "give") harg rfl
  have hreq := BigStep.var (i := 0) rfl (lib := L.lib) (env := [(reqData bytesOf r).toVal, (Data.record [
      ("give", .record [("amount", .nat amt), ("asset", .digest ab)]), ("grant", .digest grant), ("n", .nat n),
      ("payTo", payTo), ("role", role), ("terms", terms), ("want", want)]).toVal, sd.toVal, wd.toVal])
  have hce := means_deterministic hmC (transfer_means (vd := .inj "some" (.digest grant))
    (get_data (ℓ := "amount") (x := .nat amt) hgive rfl)
    (get_data (ℓ := "agent") (d := reqData bytesOf r) (x := .digest (bytesOf r.agent)) hreq rfl)
    (get_data (ℓ := "self") (d := reqData bytesOf r) (x := .digest (bytesOf r.self)) hreq rfl)
    (get_data (ℓ := "asset") (x := .digest ab) hgive rfl)
    (.inj (get_data (ℓ := "grant") (x := .digest grant) harg rfl)) (.inj rfl hgrc) .record)
  subst hce
  obtain ⟨s', a', d', v', h1, h2, h3, h4, rfl⟩ := transfer_callsOf hc
  cases hg : digestOf grant with
  | none => simp [optOf, digestAt, hg, Except.map] at h4
  | some gr =>
    have hv' : v' = some gr := by simp [optOf, digestAt, hg, Except.map] at h4; exact h4.symm
    subst hv'
    exact ⟨s', d', a', gr, h1, h3, h2, rfl, rfl⟩

/-- **The deployed escrow post is sound** (`Lang.program`'s `run` of `post`): a run that RETURNED
decoded `{give {amount, asset}, grant, n, payTo, role, terms}`, makes exactly ONE call, moving the
leg from the agent's account into the object's through the poster's grant (`transfer (of agent
asset) (of self asset) amount (via := some grant)`, no once key), and its one row act inserts offer
`n` with exactly the value `{give, payTo, role, terms}`. Mutation P8f (the post deposits nothing)
makes the call conjunct false. -/
theorem escrow_post_run_sound {D : Type} [DecidableEq D] (bytesOf : D → ByteArray) (digestOf : ByteArray → Option D)
    {rc : Lang.ReceiptCheck} {theta roles : List Label} {ol sl pt budget : Nat}
    {look : Kernel.Receive.Pinned D} {rv : Kernel.Receive.RowView D} {pkg : D} {state : Kernel.Slots}
    {args : ByteArray} {r : Kernel.Receive.Req D} {budget' : Nat} {s : Kernel.Slots}
    {calls : List (Kernel.Receive.Body D)} {rows : List (Kernel.RowSlot D × Kernel.RowAct)} {used : Nat}
    (hid : digestOf (bytesOf pkg) = some pkg)
    (hp : readPackage look pkg = .ok (offerEscrowPackageOf theta roles ol sl pt budget))
    (h : (Lang.program bytesOf digestOf rc).run look rv pkg state offerPostIx args r budget' =
      .ok (s, calls, rows, used)) :
    ∃ amt ab grant n payTo role terms want agent' self' asset' grant' kb vb,
      Wire.decodeData (escrowPostArg theta roles) args = .ok (.record [
        ("give", .record [("amount", .nat amt), ("asset", .digest ab)]), ("grant", .digest grant), ("n", .nat n),
        ("payTo", payTo), ("role", role), ("terms", terms), ("want", want)]) ∧
      digestOf (bytesOf r.agent) = some agent' ∧ digestOf (bytesOf r.self) = some self' ∧
      digestOf ab = some asset' ∧ digestOf grant = some grant' ∧
      calls = [.transfer (.of agent' asset') (.of self' asset') amt (some grant') none] ∧
      keyBytes (escrowDecl theta roles ol) (.record [("n", .nat n)]) = some kb ∧
      Wire.encodeData (escrowDecl theta roles ol).val (.record [
        ("give", .record [("amount", .nat amt), ("asset", .digest ab)]), ("payTo", payTo), ("role", role),
        ("terms", terms), ("want", want)]) = some vb ∧
      rows = [(.row ⟨r.self, 0, kb⟩, .insert 0 vb)] := by
  obtain ⟨amt, ab, grant, n, payTo, role, terms, want, kb, vb, hd, hcall, hkb, hvb, hrows⟩ := post_core bytesOf digestOf hid hp h
  obtain ⟨agent', self', asset', grant', h1, h2, h3, h4, hc⟩ := hcall (fun fs hfs => by
    simp only [escrowPostBody, escrowResult, resultT, Term.record.injEq] at hfs
    subst hfs; rfl)
  exact ⟨amt, ab, grant, n, payTo, role, terms, want, agent', self', asset', grant', kb, vb, hd, h1, h2, h3, h4, hc, hkb,
    hvb, hrows⟩

/-! ## The linear corollary, over every method -/

/-- **A standing offer's leg leaves the object only with its row** (PROT-8's linear half, at the
deployed run of every method of the escrow package). For a returned run of ANY method `m` of an
object of `offerEscrowPackageOf …`, every retract of an `offer` row among its row acts (at
`⟨self, 0, kb⟩`) is of a row the run READ (its own pinned point `{key k, val o}`, `keyBytes k = kb`),
and the run's calls include `transfer (of self asset) (of to asset) amount` of THAT row's leg
`o.give = {amount, asset}`, where `to` is the row's own `payTo` or the `payTo` of the offer the run
read under its peer. `fuse` retracts as a take does, with its leg's transfer beside the invoke of its peer; `post` only
inserts; `retire` retracts only a session row (LANG-80). The kernel
then conserves the denomination over the Turn (`admit_value`). Mutations P8d (the take pays nothing)
and P8e (the withdraw pays nothing) each make it false: a retract with no transfer. -/
theorem escrow_retract_moves_leg {D : Type} [DecidableEq D] (bytesOf : D → ByteArray) (digestOf : ByteArray → Option D)
    {rc : Lang.ReceiptCheck} {theta roles : List Label} {ol sl pt budget : Nat}
    {look : Kernel.Receive.Pinned D} {rv : Kernel.Receive.RowView D} {pkg : D} {state : Kernel.Slots}
    {m : Nat} {args : ByteArray} {r : Kernel.Receive.Req D} {budget' : Nat} {s : Kernel.Slots}
    {calls : List (Kernel.Receive.Body D)} {rows : List (Kernel.RowSlot D × Kernel.RowAct)} {used : Nat}
    (hR : (offerRoleTy roles).wf = true) (hid : digestOf (bytesOf pkg) = some pkg)
    (hp : readPackage look pkg = .ok (offerEscrowPackageOf theta roles ol sl pt budget))
    (h : (Lang.program bytesOf digestOf rc).run look rv pkg state m args r budget' = .ok (s, calls, rows, used))
    {kb : ByteArray} (hmem : (Kernel.RowSlot.row ⟨r.self, 0, kb⟩, Kernel.RowAct.retract) ∈ rows) :
    ∃ (A : Ty) (ad : Data) (ps : List (Label × RelRead)) (RD k o : Data) (amt : Nat) (ab to : ByteArray),
      Wire.decodeData A args = .ok ad ∧
      methodReads bytesOf digestOf rc look pkg (escrowRels theta roles ol sl) rv r.self ad offerRead ps = .ok RD ∧
      RD.field "offer" = some (.record [("p0", .inj "some" (.record [("key", k), ("val", .inj "some" o)]))]) ∧
      keyBytes (escrowDecl theta roles ol) k = some kb ∧
      o.field "give" = some (.record [("amount", .nat amt), ("asset", .digest ab)]) ∧
      (o.field "payTo" = some (.digest to) ∨ ∃ kq q, RD.field "peer" = some (.record [("offer",
        .record [("p0", .inj "some" (.record [("key", kq), ("val", .inj "some" q)]))])]) ∧
        q.field "payTo" = some (.digest to)) ∧
      ∃ self' asset' to', digestOf (bytesOf r.self) = some self' ∧ digestOf ab = some asset' ∧
        digestOf to = some to' ∧ Kernel.Receive.Body.transfer (.of self' asset') (.of to' asset') amt none none ∈ calls := by
  match m, h with
  | 0, h =>
    obtain ⟨keys, pair, th, via, k, o, kq, q, amt, ab, pb, self', asset', payTo', p, db, via', kb', sb, vb, hd, hm, -, -, -,
      hg, hpb, h1, h2, h3, -, -, -, hcalls, hkb, -, -, hrows⟩ := escrow_fuse_run_sound bytesOf digestOf hR hid hp h
    subst hcalls hrows
    have hk : kb = kb' := by simp at hmem; first | exact hmem | exact hmem.symm
    subst hk
    exact ⟨_, _, _, _, k, o, amt, ab, pb, hd, hm, by simp [Data.field, Row.find?], hkb, hg,
      .inr ⟨kq, q, by simp [Data.field, Row.find?], hpb⟩, self', asset', payTo', h1, h2, h3, by simp⟩
  | 1, h =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, -, -, -, -, rfl⟩ := post_core bytesOf digestOf hid hp h
    simp at hmem
  | 2, h =>
    obtain ⟨kb', rfl⟩ := retire_core bytesOf digestOf hid hp h
    simp at hmem
  | 3, h =>
    obtain ⟨keys, pair, th, k, o, kq, q, amt, ab, pb, kb', sb, vb, hd, hm, -, -, -, hg, hpb, hcall, hkb, -, -, rfl⟩ :=
      take_core bytesOf digestOf hR hid hp h
    obtain ⟨self', asset', payTo', h1, h2, h3, rfl⟩ := hcall (fun fs hfs => by
      simp only [escrowTakeDone, escrowResult, resultT, Term.record.injEq] at hfs
      subst hfs; rfl)
    have hk : kb = kb' := by simp at hmem; first | exact hmem | exact hmem.symm
    subst hk
    exact ⟨_, _, _, _, k, o, amt, ab, pb, hd, hm, by simp [Data.field, Row.find?], hkb, hg,
      .inr ⟨kq, q, by simp [Data.field, Row.find?], hpb⟩, self', asset', payTo', h1, h2, h3, by simp⟩
  | 4, h =>
    obtain ⟨k, o, amt, ab, po, kb', hd, hm, hg, hpo, hcall, hkb, rfl⟩ := withdraw_core bytesOf digestOf hid hp h
    obtain ⟨self', asset', to', h1, h2, h3, rfl⟩ := hcall (fun fs hfs => by
      simp only [escrowWithdrawDone, escrowResult, resultT, Term.record.injEq] at hfs
      subst hfs; rfl)
    have hk : kb = kb' := by simp at hmem; first | exact hmem | exact hmem.symm
    subst hk
    exact ⟨_, _, _, _, k, o, amt, ab, po, hd, hm, by simp [Data.field, Row.find?], hkb, hg, .inl hpo,
      self', asset', to', h1, h2, h3, by simp⟩
  | m + 5, h =>
    exfalso
    change (runMeasuredLive bytesOf digestOf rc look rv pkg state (m + 5) args r budget').map _ = _ at h
    rw [runMeasuredLive_leaf_closed hid hp rfl rfl] at h
    cases hm : runMeasured bytesOf digestOf rc look rv pkg state (m + 5) args r budget' with
    | error e => rw [hm] at h; cases h
    | ok x =>
    obtain ⟨s', calls', rows', t', n'⟩ := x
    obtain ⟨S, -, -, -, -, -, -, -, hS, -⟩ := runMeasured_inv hm
    obtain ⟨L, g, p, ℓ, sg, -, -, -, -, hl, hpg, hres, -⟩ := runSetup_spec hS
    obtain ⟨hpg', -, -⟩ := load_top bytesOf digestOf (fuel := closureDepthMax - 1) hid hp hl
    rw [hpg'] at hpg
    cases hpg
    exact resolve_lt hres

end Nanodregg.Lang.Std
