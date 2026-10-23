/-
# Ledger.Proofs.EscrowAdmitted — a deposit and a release the World admits, through a capped grant

`escrow_invokes_one_payout` bounds the payouts along every `ObjectHistory` of an escrow object.
This module shows such a history exists with the bound attained, through the REAL `receive` and
`World.admit` (KERNEL's derivation, sealing and admission, `Lang.program` as the program), and that
the deposit's authority is exactly its amount (LEDGER-18, on KERNEL-60's `Right.transfer (cap)`):

* `escrow_history_witnessed`: a signed deposit (method 0) then a signed release (method 2) of one
  escrow object, each derived by `receive` and admitted by `World.admit`, form an `ObjectHistory`
  whose every step reads the object's package as `escrow`, at a lawful `Ctx` running the language;
  exactly one returned call is a payout.
* `escrow_deposit_spends_cap`: the deposit (an admitted `ObjectStep`) moves the escrow's own
  `amount` (read off the state it ran on) through the depositor's grant to the escrow object: before
  the deposit the grant's ledger reads `(1, amount)`, after it `(2, 0)`, and the depositor's
  balance fell by exactly `amount`.
  On the World it left, the same transfer through the same grant is `transferSpent`: the cap is
  spent on this instance (over every history, `grant_moves_le_cap`'s read-back, on KERNEL-30's
  invariant).
* Tooth: `escrow_short_cap_refused`: the same deposit transfer through a grant capped one below the
  amount is `transferSpent` of that grant.

The instance (KERNEL's `InvokeWitness` shape). A toy `Env` over one-byte digests: the hash of `b`
is `64 + 8·b₀ + b₁` (so the three accounts, the grant, the object, the member and the package have
distinct ids and the two once nullifiers differ; Poseidon2 and cSHAKE are out of the kernel
evaluator's reach), every signature accepted, a call's bytes its window end. The World holds, at
version 0: member 1 (the depositor, key `42`), escrow object 3 (package 9, owner 1, born `open` on
terms amount 5, arbiter 7, asset 4, beneficiary 2, depositor 1, nonce `n`), package 9 (`encodePackage
escrow`), the accounts of 1 (balance 100), 3 and 2 in asset 4, and grant 6: issued by 1 to object 3
on 1's account, `transfer amount`. It is built by hand, not reached from a genesis (ids are not
content or transaction hashes); the theorems witnessed carry no reachability premise.

The kernel never evaluates the package decoder or `Lang.load` (well-founded recursion): the package
is read from its install bytes (`readPackage_installed`), the closure through `load`'s equation
(`load_one`). Everything else, both derivations (the deposit's transfer through the grant, its
ledger append and once nullifier; the release's payout), both runs, both judgements and both
admissions, is evaluated by `decide +kernel`; nothing by compiled code.
-/
import Ledger.Proofs.EscrowInvokes
import Kernel.Proofs.InvokeWitness

namespace Nanodregg.Ledger.Proofs

open Nanodregg.Lang Nanodregg.Kernel Nanodregg.Kernel.Receive Nanodregg.Ledger.Escrow

/-! ## Boolean forms the kernel evaluates -/

private def isOkAs {ε α : Type} [DecidableEq α] : Except ε α → α → Bool
  | .ok b, a => decide (b = a)
  | .error _, _ => false

private theorem of_isOkAs {ε α : Type} [DecidableEq α] {x : Except ε α} {a : α}
    (h : isOkAs x a = true) : x = .ok a := by
  cases x with
  | ok b => simp only [isOkAs, decide_eq_true_eq] at h; rw [h]
  | error _ => cases h

private theorem of_isOk {ε α : Type} {x : Except ε α} {d : α} (h : x.isOk = true) : x = .ok (x.toOption.getD d) := by
  cases x with
  | ok a => rfl
  | error _ => cases h

/-- A run returned `(s, calls, [], used)`. -/
private def runIs {ε D : Type} [DecidableEq D] (x : Except ε (Slots × List (Body D) × List (RowSlot D × RowAct) × Nat))
    (s : Slots) (calls : List (Body D)) (used : Nat) : Bool :=
  match x with
  | .ok (s', c', [], u) => decide (s' = s) && decide (c' = calls) && decide (u = used)
  | _ => false

private theorem of_runIs {ε D : Type} [DecidableEq D]
    {x : Except ε (Slots × List (Body D) × List (RowSlot D × RowAct) × Nat)} {s : Slots} {calls : List (Body D)}
    {used : Nat} (h : runIs x s calls used = true) : x = .ok (s, calls, [], used) := by
  unfold runIs at h
  split at h
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    rw [h.1.1, h.1.2, h.2]
  · cases h

/-- A refusal by `transferSpent g`. -/
private def spentAs {D α : Type} [DecidableEq D] : Except (Refusal D) α → D → Bool
  | .error (.transferSpent g'), g => decide (g' = g)
  | _, _ => false

private theorem of_spentAs {D α : Type} [DecidableEq D] {x : Except (Refusal D) α} {g : D}
    (h : spentAs x g = true) : x = .error (.transferSpent g) := by
  unfold spentAs at h
  split at h
  · simp only [decide_eq_true_eq] at h; rw [h]
  · cases h

/-! ## The instance -/

private def tEnv : Env UInt8 where
  hash _ b := 64 + 8 * b.data.getD 0 0 + b.data.getD 1 0
  bytes d := ⟨#[d]⟩
  turnBytes _ := ByteArray.empty
  cellBytes _ := ByteArray.empty

private def tDigestOf (b : ByteArray) : Option UInt8 := if b.size = 1 then some (b.data.getD 0 0) else none

private def tX : Ctx UInt8 where
  env := tEnv
  unsignedBytes _ := ByteArray.empty
  callBytes c := ⟨#[UInt8.ofNat c.unsigned.validUntil]⟩
  decodeCall _ := none
  digestOf := tDigestOf
  verify _ _ _ := true
  program := Lang.program tEnv.bytes tDigestOf noReceipts

private def dep : UInt8 := 1
private def ben : UInt8 := 2
private def obj : UInt8 := 3
private def asset : UInt8 := 4
private def gr : UInt8 := 6
private def pkg : UInt8 := 9

private def terms : Terms := ⟨5, ⟨#[7]⟩, ⟨#[asset]⟩, ⟨#[ben]⟩, ⟨#[dep]⟩, "n".toUTF8⟩

/-- The escrow's state slots in phase `p` (what `create` seeds for `open`, what a run writes). -/
private def slotsAt (p : Label) : Slots :=
  match stateD terms p with
  | .record fs => (stateSlots (recordRow escrow.state) fs 0).getD []
  | _ => []

@[irreducible] private def pkgB : ByteArray := (Wire.encodePackage escrow).getD .empty

private theorem pkgB_eq : Wire.encodePackage escrow = some pkgB := by
  have h := escrow_encodes
  unfold pkgB
  cases he : Wire.encodePackage escrow with
  | none => rw [he] at h; cases h
  | some b => rfl

private def memberCell : Cell := { kind := kindMember, discipline := .ram, slots := [(slotKey, ⟨#[42]⟩)] }
private def pkgCell : Cell := { kind := kindPackage, discipline := .rom, slots := [(0, pkgB)] }
private def objCell : Cell := objectCell tX dep (some pkg) [] (slotsAt "open")

/-- An account of `owner` in `asset` holding `b`. -/
private def funded (owner : UInt8) (b : Int) : Cell :=
  let c := accountCell tX owner (tEnv.bytes asset) 0
  { c with slots := c.slots.set Value.balanceKey (Value.balanceBytes b) }

/-- The depositor's grant to the escrow object on its own account: `transfer` capped at the escrow's
amount (the cell `grant` makes: target, grantee, issuer, then the right's ledger). -/
private def grantCell : Cell :=
  { kind := kindGrant, discipline := .appendOnly,
    slots := slotsOf ([(grantTarget, tEnv.bytes (accountId tX dep asset)), (grantGrantee, tEnv.bytes obj),
      (grantIssuer, tEnv.bytes dep)] ++ rightSlots [.transfer terms.amount]) }

private def cells : List (UInt8 × Cell) :=
  [(dep, memberCell), (obj, objCell), (gr, grantCell), (pkg, pkgCell),
   (accountId tX dep asset, funded dep 100), (accountId tX obj asset, funded obj 0),
   (accountId tX ben asset, funded ben 0)]

private def w0 : World UInt8 :=
  { trie := cells.foldl (fun t p => t.insert (trieSpec tEnv) (.cell p.1) (.entry (.live p.2 0))) Trie.T.empty,
    journal := .empty, refusals := .empty, rows := .empty, height := 0, steps := 0,
    chain := 0, allowance := 1000000, origin := 0 }

/-- Every cell of the instance, pinned at what `w` holds. -/
private def pinsAt (w : World UInt8) : List (UInt8 × UInt8) := cells.map fun p => (p.1, pinOf tEnv (w.entry tEnv p.1))

/-- The depositor invokes `method` of the escrow with `args`, on `w`'s pins, window `[1, vu]`. -/
private def callAt (w : World UInt8) (vu method : Nat) (args : ByteArray) : Call UInt8 :=
  { unsigned :=
      { world := 0, member := dep, key := ⟨#[42]⟩, notBefore := 1, validUntil := vu, pins := pinsAt w,
        maxCharge := 100000, body := .invoke obj method args 1000 none }
    signature := .empty }

private def dummy : Turn UInt8 :=
  { txId := 0, notBefore := 0, validUntil := 0, touches := [], creates := [], nullifiers := [],
    charge := 0, event := .empty }

private def noDraft : Draft UInt8 × Walk UInt8 := (⟨[], [], [], []⟩, ⟨[], 0, 0⟩)

/-! ## The package, read and loaded through its equations -/

private theorem hlits : checkLits tDigestOf escrow = .ok () := by
  have h : (checkLits tDigestOf escrow matches .ok ()) = true := by decide +kernel
  split at h
  · assumption
  · cases h

private theorem hchecks : escrow.checkWith [] = .ok () := by
  have := escrow_checks
  split at this
  · assumption
  · cases this

private theorem readPackage_esc {look : Pinned UInt8} (h : readKind look pkg kindPackage = .ok pkgCell) :
    readPackage look pkg = .ok escrow :=
  readPackage_installed h (by simp [pkgCell, Slots.get]) pkgB_eq rfl

private def L0 : Loaded := ⟨[tEnv.bytes pkg], [escrow.body.relocate fun i => ([] : List Nat).getD i 0], [escrow]⟩

private theorem load_esc {look : Pinned UInt8} (h : readKind look pkg kindPackage = .ok pkgCell) :
    load tDigestOf look closureDepthMax (tEnv.bytes pkg) ⟨[], [], []⟩ = .ok (L0, 0) :=
  load_one (fuel := 7) rfl (readPackage_esc h) rfl (admit_one hchecks hlits)

/-! ## The deposit, on `w0` -/

private def a1 : ByteArray := (depositArgs (tEnv.bytes gr)).getD .empty
private def c1 : Call UInt8 := callAt w0 5 deposit a1
private def req1 : Req UInt8 := reqOf c1.unsigned obj dep (.invoke deposit)
/-- The deposit's one call: `amount` from the depositor's account to the escrow's, through grant
`gr`, once under the nonce. -/
private def calls1 : List (Body UInt8) :=
  [.transfer (.of dep asset) (.of obj asset) terms.amount (some gr) (some terms.nonce)]
private def look1 : Pinned UInt8 := pinned tEnv w0 c1.unsigned.pins
private def rv1 : RowView UInt8 := rowView tEnv w0 c1.unsigned
private def sub1 : Receive.Sub UInt8 := tree tX look1 rv1 c1 Bounds.callDepthMax
private def out1 : Draft UInt8 × Walk UInt8 :=
  ((deriveCalls sub1 obj ⟨[], writeOf obj (diffOps (stateOf objCell) (slotsAt "held")), [], []⟩
    { visited := [obj], pool := poolOf c1.unsigned.body - 119, born := 0 } calls1).toOption).getD noDraft
private def t1 : Turn UInt8 :=
  ((sealTurn tX c1 out1.1.creates out1.1.effects out1.1.nullifiers out1.1.rows).toOption).getD dummy
private def w1 : World UInt8 := ((World.admit tEnv w0 t1).toOption).getD w0

private theorem c1_pkg : readKind look1 pkg kindPackage = .ok pkgCell := by rfl

private theorem c1_invokeRun : invokeRun tX look1 c1 dep obj deposit none = .ok (objCell, pkg, req1) :=
  of_isOkAs (by decide +kernel)

private theorem c1_run :
    tX.program.run look1 rv1 pkg (stateOf objCell) deposit a1 req1 (min 1000 (poolOf c1.unsigned.body)) =
      .ok (slotsAt "held", calls1, [], 119) := by
  show (runMeasuredLive tEnv.bytes tDigestOf noReceipts _ _ _ _ _ _ _ _).map _ = _
  rw [runMeasuredLive_leaf_closed (show tDigestOf (tEnv.bytes pkg) = some pkg from rfl)
    (readPackage_esc c1_pkg) rfl rfl]
  unfold runMeasured runMeasuredWith runSetup runSetupWith
  rw [load_esc c1_pkg]
  exact of_runIs (by decide +kernel)

private theorem c1_judge : tX.program.judge look1 (some pkg) [] (stateOf objCell) (slotsAt "held") req1 = .ok () := by
  have h1 : judgeOne tEnv.bytes tDigestOf look1 pkg (stateOf objCell) (slotsAt "held") req1 = .ok () := by
    unfold judgeOne judgeOneWith
    rw [load_esc c1_pkg]
    exact of_isOkAs (by decide +kernel)
  show Nanodregg.Lang.judgeContextual tEnv.bytes tDigestOf look1 (some pkg) [] (stateOf objCell) (slotsAt "held") req1 = .ok ()
  unfold Nanodregg.Lang.judgeContextual
  simp only [judgeOneContextual_leaf_closed (show tDigestOf (tEnv.bytes pkg) = some pkg from rfl)
    (readPackage_esc c1_pkg) rfl rfl]
  simp only [h1]
  rfl

private theorem c1_laws : lawsOf tX obj objCell = .ok [] := of_isOkAs (by decide +kernel)

private theorem c1_derive :
    deriveCalls sub1 obj ⟨[], writeOf obj (diffOps (stateOf objCell) (slotsAt "held")), [], []⟩
      { visited := [obj], pool := poolOf c1.unsigned.body - 119, born := 0 } calls1 = .ok out1 :=
  of_isOk (by decide +kernel)

private theorem c1_receive : receive tX w0 c1 = .ok t1 := by
  rw [receive_of rfl (of_isOkAs (by decide +kernel)) (of_isOkAs (by decide +kernel)) rfl
    (invoke_of (by decide) c1_invokeRun c1_run (by decide) (of_isOkAs (by decide +kernel)) c1_laws c1_judge
      (by decide) c1_derive)]
  exact of_isOk (by decide +kernel)

private theorem c1_admit : World.admit tX.env w0 t1 = .ok w1 := of_isOk (by decide +kernel)

/-! ## The release, on `w1` -/

private def a2 : ByteArray := noArgs.getD .empty
private def c2 : Call UInt8 := callAt w1 6 release a2
private def cell2 : Cell := (w1.live tEnv obj).getD objCell
private def req2 : Req UInt8 := reqOf c2.unsigned obj dep (.invoke release)
/-- The release's one call: the payout, `amount` from the escrow's account to the beneficiary's. -/
private def calls2 : List (Body UInt8) :=
  [.transfer (.of obj asset) (.of ben asset) terms.amount none (some payoutKey)]
private def look2 : Pinned UInt8 := pinned tEnv w1 c2.unsigned.pins
private def rv2 : RowView UInt8 := rowView tEnv w1 c2.unsigned
private def sub2 : Receive.Sub UInt8 := tree tX look2 rv2 c2 Bounds.callDepthMax
private def out2 : Draft UInt8 × Walk UInt8 :=
  ((deriveCalls sub2 obj ⟨[], writeOf obj (diffOps (stateOf cell2) (slotsAt "released")), [], []⟩
    { visited := [obj], pool := poolOf c2.unsigned.body - 113, born := 0 } calls2).toOption).getD noDraft
private def t2 : Turn UInt8 :=
  ((sealTurn tX c2 out2.1.creates out2.1.effects out2.1.nullifiers out2.1.rows).toOption).getD dummy
private def w2 : World UInt8 := ((World.admit tEnv w1 t2).toOption).getD w1

private theorem c2_pkg : readKind look2 pkg kindPackage = .ok pkgCell := by rfl

private theorem c2_invokeRun : invokeRun tX look2 c2 dep obj release none = .ok (cell2, pkg, req2) :=
  of_isOkAs (by decide +kernel)

private theorem c2_state : stateOf cell2 = slotsAt "held" := by decide +kernel

private theorem c2_run :
    tX.program.run look2 rv2 pkg (stateOf cell2) release a2 req2 (min 1000 (poolOf c2.unsigned.body)) =
      .ok (slotsAt "released", calls2, [], 113) := by
  show (runMeasuredLive tEnv.bytes tDigestOf noReceipts _ _ _ _ _ _ _ _).map _ = _
  rw [runMeasuredLive_leaf_closed (show tDigestOf (tEnv.bytes pkg) = some pkg from rfl)
    (readPackage_esc c2_pkg) rfl rfl]
  unfold runMeasured runMeasuredWith runSetup runSetupWith
  rw [load_esc c2_pkg, c2_state]
  exact of_runIs (by decide +kernel)

private theorem c2_judge :
    tX.program.judge look2 (some pkg) [] (stateOf cell2) (slotsAt "released") req2 = .ok () := by
  have h1 : judgeOne tEnv.bytes tDigestOf look2 pkg (stateOf cell2) (slotsAt "released") req2 = .ok () := by
    unfold judgeOne judgeOneWith
    rw [load_esc c2_pkg, c2_state]
    exact of_isOkAs (by decide +kernel)
  show Nanodregg.Lang.judgeContextual tEnv.bytes tDigestOf look2 (some pkg) [] (stateOf cell2) (slotsAt "released") req2 = .ok ()
  unfold Nanodregg.Lang.judgeContextual
  simp only [judgeOneContextual_leaf_closed (show tDigestOf (tEnv.bytes pkg) = some pkg from rfl)
    (readPackage_esc c2_pkg) rfl rfl]
  simp only [h1]
  rfl

private theorem c2_laws : lawsOf tX obj cell2 = .ok [] := of_isOkAs (by decide +kernel)

private theorem c2_derive :
    deriveCalls sub2 obj ⟨[], writeOf obj (diffOps (stateOf cell2) (slotsAt "released")), [], []⟩
      { visited := [obj], pool := poolOf c2.unsigned.body - 113, born := 0 } calls2 = .ok out2 :=
  of_isOk (by decide +kernel)

private theorem c2_receive : receive tX w1 c2 = .ok t2 := by
  rw [receive_of rfl (of_isOkAs (by decide +kernel)) (of_isOkAs (by decide +kernel)) rfl
    (invoke_of (by decide) c2_invokeRun c2_run (by decide) (of_isOkAs (by decide +kernel)) c2_laws c2_judge
      (by decide) c2_derive)]
  exact of_isOk (by decide +kernel)

private theorem c2_admit : World.admit tX.env w1 t2 = .ok w2 := of_isOk (by decide +kernel)

/-! ## The witnesses -/

private def e1 : Pinned UInt8 × Option UInt8 × List UInt8 × Req UInt8 × Slots × Slots × List (Body UInt8) :=
  (look1, some pkg, [], req1, stateOf objCell, slotsAt "held", calls1)
private def e2 : Pinned UInt8 × Option UInt8 × List UInt8 × Req UInt8 × Slots × Slots × List (Body UInt8) :=
  (look2, some pkg, [], req2, stateOf cell2, slotsAt "released", calls2)

private theorem hist : ObjectHistory tX obj w0 w2 [e1, e2] :=
  .cons (.invoke c1_receive c1_admit rfl c1_invokeRun c1_run c1_laws)
    (.cons (.invoke c2_receive c2_admit rfl c2_invokeRun c2_run c2_laws) (.nil w2))

/-- **An admitted history of an escrow object, with the bound attained.** At a lawful `Ctx` running
the language over its own codec, a signed deposit and then a signed release of one escrow object,
each derived by `receive` (the deposit's transfer through the depositor's capped grant; the
release's payout) and admitted by `World.admit`, are an `ObjectHistory` whose every judged step
reads the object's package as `escrow`, and exactly one call they return is a payout. So the
premises of `escrow_invokes_one_payout` hold together, and its `≤ 1` is reached. -/
theorem escrow_history_witnessed :
    ∃ (X : Ctx UInt8) (o p : UInt8) (w w' : World UInt8)
      (tr : List (Pinned UInt8 × Option UInt8 × List UInt8 × Req UInt8 × Slots × Slots × List (Body UInt8))),
      X.Lawful ∧ X.program = Lang.program X.env.bytes X.digestOf Lang.noReceipts ∧ ObjectHistory X o w w' tr ∧
      (∀ e ∈ tr, e.2.1 = some p ∧ readPackage e.1 p = .ok escrow) ∧
      payoutCalls (tr.map fun e => e.2.2.2.2.2.2) = 1 := by
  refine ⟨tX, obj, pkg, w0, w2, [e1, e2], ⟨fun _ => rfl⟩, rfl, hist, ?_, by decide⟩
  intro e he
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with rfl | rfl
  · exact ⟨rfl, readPackage_esc c1_pkg⟩
  · exact ⟨rfl, readPackage_esc c2_pkg⟩

/-- **The deposit's authority is exactly its amount.** At a lawful `Ctx` running the language, the
escrow's deposit (an admitted `ObjectStep` of an object whose package reads as `escrow`) has one call,
moving the `amount` its own old state holds (`amountOf`) through grant `g`; before it `g`'s transfer
ledger reads `(1, amount)` (the cap IS the amount), after it `(2, 0)`; the source account's balance
fell by exactly `amount`; and on the World it left, the same transfer through `g` is refused
`transferSpent g`: one deposit spent the whole cap. (Over every history, the read-back is
`grant_moves_le_cap`'s, on KERNEL-30's `LedgerContiguous`.) -/
theorem escrow_deposit_spends_cap :
    ∃ (X : Ctx UInt8) (o p g : UInt8) (w w' : World UInt8)
      (e : Pinned UInt8 × Option UInt8 × List UInt8 × Req UInt8 × Slots × Slots × List (Body UInt8))
      (src dst : AcctRef UInt8) (amt : Nat) (nk : ByteArray) (gc gc' : Cell) (ps : List (UInt8 × UInt8)),
      X.Lawful ∧ X.program = Lang.program X.env.bytes X.digestOf Lang.noReceipts ∧
      ObjectStep X o w w' (some e) ∧ e.2.1 = some p ∧ readPackage e.1 p = .ok escrow ∧
      e.2.2.2.2.2.2 = [.transfer src dst amt (some g) (some nk)] ∧ amountOf e.2.2.2.2.1 = some amt ∧
      w.live X.env g = some gc ∧ ledgerLeft transferBase g gc = .ok (1, amt) ∧
      w'.live X.env g = some gc' ∧ ledgerLeft transferBase g gc' = .ok (2, 0) ∧
      ((w.live X.env (src.resolve X)).bind Value.ofCell).map Value.balance = some 100 ∧
      ((w'.live X.env (src.resolve X)).bind Value.ofCell).map Value.balance = some (100 - amt) ∧
      transfer X (pinned X.env w' ps) ⟨o, 0⟩ src dst amt (some g) (some nk) = .error (.transferSpent g) :=
  ⟨tX, obj, pkg, gr, w0, w1, e1, _, _, _, _, grantCell, (w1.live tEnv gr).getD grantCell, c2.unsigned.pins,
    ⟨fun _ => rfl⟩, rfl, .invoke c1_receive c1_admit rfl c1_invokeRun c1_run c1_laws, rfl,
    readPackage_esc c1_pkg, rfl, by decide +kernel, by decide +kernel,
    of_isOkAs (by decide +kernel), by decide +kernel, of_isOkAs (by decide +kernel), by decide +kernel,
    by decide +kernel, of_spentAs (by decide +kernel)⟩

/-- **Tooth: the same deposit, through a grant capped one below its amount, is refused.** The
admitted deposit of `escrow_deposit_spends_cap` (its call moves the `amount` its old state holds,
through `g`), read in a view equal to its own pinned view except that `g` lends `amount - 1`, has its
transfer refused `transferSpent g`: the cap, not the package text, bounds what the deposit moves
(ledger-sim's short-cap plant, in the kernel). -/
theorem escrow_short_cap_refused :
    ∃ (X : Ctx UInt8) (o g : UInt8) (w w' : World UInt8)
      (e : Pinned UInt8 × Option UInt8 × List UInt8 × Req UInt8 × Slots × Slots × List (Body UInt8))
      (src dst : AcctRef UInt8) (amt : Nat) (nk : ByteArray) (look : Pinned UInt8) (gc : Cell),
      ObjectStep X o w w' (some e) ∧ e.2.2.2.2.2.2 = [.transfer src dst amt (some g) (some nk)] ∧
      amountOf e.2.2.2.2.1 = some amt ∧ 0 < amt ∧ (∀ i, i ≠ g → look i = e.1 i) ∧
      look g = .ok (some gc) ∧ ledgerLeft transferBase g gc = .ok (1, amt - 1) ∧
      transfer X look ⟨o, 0⟩ src dst amt (some g) (some nk) = .error (.transferSpent g) := by
  let short : Cell := { grantCell with slots := grantCell.slots.set transferBase (countBytes (terms.amount - 1)) }
  exact ⟨tX, obj, gr, w0, w1, e1, _, _, _, _, fun i => if i = gr then .ok (some short) else look1 i, short,
    .invoke c1_receive c1_admit rfl c1_invokeRun c1_run c1_laws, rfl, by decide +kernel, by decide,
    fun i hi => if_neg hi, by simp, of_isOkAs (by decide +kernel), of_spentAs (by decide +kernel)⟩

end Nanodregg.Ledger.Proofs
