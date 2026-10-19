/-
# Ledger.Proofs.EscrowRun — the escrow's calls are what the RECEIVER's run returns

`Ledger.Proofs.Escrow` reads each method's result as `methodResult`: the method application
`apply4 0 ℓ` under the closure `[escrow.body]`, extracted whole at the methods' result type. The
receiver runs `Lang.runMeasured`: it loads the package's closure from the pinned view, resolves the
method index, reads the state slots, decodes the arguments, runs `apply4 g ℓ` under the loaded
closure at the call's budget, extracts the result, and reads its calls slot into `Body D`. Here the
two meet, through LANG-61 (`Lang.Proofs.Extract`):

* `escrow_noRef`: the escrow's body mentions no closure package, so the loaded closure holds it
  unrelocated and its meaning does not depend on the closure (`relocate_noRef`, `relib_apply4`).
* `escrow_resolve`: the method indices the receiver resolves are exactly 0 deposit, 1 refund,
  2 release, each at argument type `depositArg` / `unit`, result type `resultOf`, reading no rows.
* `escrow_state_shape`: a state that reads at the escrow's row is `stateOf` of seven terms.
* `run_result`: what a receiver extracts from `apply4 g ℓ` under a closure holding the body at
  `g` is `methodResult ℓ`, at every budget the run succeeded under (`runMeasured_means`,
  `bigStep_deterministic`, `means_deterministic`).
* `escrow_run_calls`, the escrow's payout theorem of the deployed path: a successful run of the
  escrow package (`readPackage look pkg = .ok escrow`, under a decoder that reads every id's bytes
  back) is `RunCalls`: it read the state as seven terms, and its calls are exactly the one transfer
  the method makes: `deposit` from `of depositor asset` into `of self asset` through the grant its
  argument names, spending the nonce; `refund` and `release` out of `of self asset` (`self` the
  request's object) to the depositor and the beneficiary, through no grant, spending `"payout"`;
  any other index does not run. KERNEL resolves `AcctRef.of o a` to `accountId X o a`
  (`AcctRef.resolve`), so a payout's source is `accountId X e asset`, the account both payouts'
  one nullifier names.
* `escrow_program_calls`: the same at `invoke`'s call `X.program.run`, for a lawful `Ctx` whose
  program is `Lang.program` over its own codec; `escrow_run_deployed`: at the node's `Ctx`
  (`Host.Deployed.X`), both discharged (`Receive.deployed_ctx_lawful`, `rfl`).

Teeth: `run_result_needs_body` (another body at `g` gives the release another result: the body
premise is not idle); `run_calls_pins_payee` (a release paying the depositor, from a state whose
beneficiary is another, is not `RunCalls`); `escrow_run_spends` (`spends` tells a release's result
from a deposit's, so the chain's count is not constant).
-/
import Ledger.Proofs.Escrow
import Lang.Proofs.Extract
import Lang.Proofs.Invoke
import Kernel.Proofs.RootedDeployed

namespace Nanodregg.Ledger.Proofs

open Nanodregg.Lang
open Nanodregg.Kernel Nanodregg.Kernel.Receive
open Nanodregg.Ledger.Escrow

/-! ## The body holds no closure reference -/

private def mth (n : Nat) : Term :=
  match methods[n]? with
  | some (_, _, _, t) => t
  | none => .nat 0

private theorem fields_eq :
    bodyFields = [("deposit", mth 0), ("escrow", law), ("refund", mth 1), ("release", mth 2)] := rfl

open NoRefStd Std in
/-- **The escrow's body mentions no closure package**: no `ref` in its law or its methods. -/
theorem escrow_noRef : NoRef escrow.body := by
  rw [escrow_body, fields_eq]
  have hp : ∀ (a : At) (f p : Label), NoRef (isPh (a.oldF f) p) ∧ NoRef (isPh (a.newF f) p) := fun a f p => by
    simp only [isPh, Std.isState, At.oldF, At.newF, At.old, At.new, NoRef, row_iff]
    refine ⟨⟨trivial, ?_⟩, ⟨trivial, ?_⟩⟩ <;>
    · intro e he
      obtain ⟨_, _, rfl⟩ := List.mem_map.1 he
      trivial
  have hq : ∀ (a : At) (f : Label), NoRef (agentIs a f) := fun a f => by
    simp [agentIs, At.reqF, At.oldF, At.req, At.old, NoRef]
  refine ⟨?_, ?_, ?_, ?_, trivial⟩
  · simp [mth, methods, NoRef, NoRefRow, resultT, callsT, someCallT, depositCall, transferT, ofT, st, rq,
      someD, someB, keep, phaseT, slotLabels]
  · exact lawOf5_ (allOf_ (by simp [hp])) (allOf_ (by simp [hp])) refusedT_ refusedT_
      (by simp [invokeC, Std.guard, NoRef, methodClause, methodIs, refusedT_, allOf_, anyOf_, notT_, hp, hq,
        At.payload, natT])
  · simp [mth, methods, NoRef, NoRefRow, resultT, callsT, someCallT, payoutCall, transferT, ofT, st, rq,
      noneD, someB, keep, phaseT, slotLabels]
  · simp [mth, methods, NoRef, NoRefRow, resultT, callsT, someCallT, payoutCall, transferT, ofT, st, rq,
      noneD, someB, keep, phaseT, slotLabels]

/-! ## The method the receiver resolves, the state it reads -/

private theorem resolve0 {D : Type} :
    resolveMethod (D := D) escrow 0 = .ok ("deposit", ⟨depositArg, [T], [], 0⟩) := rfl
private theorem resolve1 {D : Type} :
    resolveMethod (D := D) escrow 1 = .ok ("refund", ⟨unit, [T], [], 0⟩) := rfl
private theorem resolve2 {D : Type} :
    resolveMethod (D := D) escrow 2 = .ok ("release", ⟨unit, [T], [], 0⟩) := rfl

/-- **The methods the receiver resolves**: index 0 is `deposit` at `depositArg`, 1 `refund` and
2 `release` at `unit`; every one returns at `resultOf` and reads no rows; any other index is
refused. -/
theorem escrow_resolve {D : Type} {m : Nat} {x : Label × Sig} (h : resolveMethod (D := D) escrow m = .ok x) :
    (m = deposit ∧ x = ("deposit", ⟨depositArg, [T], [], 0⟩) ∨ m = refund ∧ x = ("refund", ⟨unit, [T], [], 0⟩) ∨
      m = release ∧ x = ("release", ⟨unit, [T], [], 0⟩)) ∧
    resultTy escrow.state x.2.calls (editTy escrow.rels) x.2.edits = resultOf := by
  match m, h with
  | 0, h => rw [resolve0] at h; cases h; exact ⟨.inl ⟨rfl, rfl⟩, rfl⟩
  | 1, h => rw [resolve1] at h; cases h; exact ⟨.inr (.inl ⟨rfl, rfl⟩), rfl⟩
  | 2, h => rw [resolve2] at h; cases h; exact ⟨.inr (.inr ⟨rfl, rfl⟩), rfl⟩
  | m + 3, h =>
    have hn : escrow.methods[m + 3]? = none := by rw [escrow_methods]; simp
    simp [resolveMethod, hn] at h

private theorem phase_row :
    Row.sort (phaseLabels.map fun s => (s, Ty.record [])) =
      [("held", .record []), ("open", .record []), ("refunded", .record []), ("released", .record [])] := rfl

/-- **A state read at the escrow's row is seven terms**: the amount, the four parties' and the
asset's digests, the nonce, and a phase label. -/
theorem escrow_state_shape {d : Data} (h : Conforms d stateTy) :
    ∃ amount arb asset ben dep nk p, d = stateOf amount arb asset ben dep nk p := by
  cases h with
  | record hr =>
    rcases hr with _ | ⟨h1, _ | ⟨h2, _ | ⟨h3, _ | ⟨h4, _ | ⟨h5, _ | ⟨h6, _ | ⟨h7, _ | _⟩⟩⟩⟩⟩⟩⟩
    cases h1; cases h2; cases h3; cases h4; cases h5; cases h6
    cases h7 with
    | inj hf hw =>
      have hm := find?_mem hf
      rw [phase_row] at hm
      simp only [List.mem_cons, Prod.mk.injEq, List.mem_nil_iff, or_false] at hm
      rcases hm with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;>
      · cases hw with
        | record hr0 => cases hr0; exact ⟨_, _, _, _, _, _, _, rfl⟩

/-- `deposit`'s argument is a grant. -/
theorem deposit_arg_shape {d : Data} (h : Conforms d depositArg) : ∃ g, d = .record [("grant", .digest g)] := by
  cases h with
  | record hr =>
    rcases hr with _ | ⟨h1, _ | _⟩
    cases h1
    exact ⟨_, rfl⟩

/-! ## The receiver's result is `methodResult` -/

/-- **What the receiver extracts is `methodResult`**: under any closure holding the escrow's body at
`g`, if the method application `apply4 g ℓ` means `v` in the run's environment and `v` means `d`
at `resultOf`, then `d` is the result `methodResult ℓ` computes under `[escrow.body]`. -/
theorem run_result {lib : List Term} {g : Nat} (hg : lib[g]? = some escrow.body) {ℓ : Label}
    {rq ad sd wd : Data} {v : Val} {d dE : Data}
    (hb : BigStep lib [rq.toVal, ad.toVal, sd.toVal, wd.toVal] (apply4 g ℓ) (.ok v))
    (hm : Means lib resultOf v d) (hr : methodResult ℓ sd ad rq wd = some dE) : d = dE := by
  unfold methodResult at hr
  split at hr
  · rename_i v' u heval
    split at hr
    · rename_i dE' f hext
      cases hr
      have hb' : BigStep [escrow.body] [rq.toVal, ad.toVal, sd.toVal, wd.toVal] (apply4 0 ℓ) (.ok v') :=
        run_bigStep heval
      obtain ⟨hb'', hnr⟩ := relib_apply4 (lib := [escrow.body]) (lib' := lib) (g := 0) rfl hg escrow_noRef
        (toVal4_noRef rq ad sd wd) hb'
      cases bigStep_deterministic hb hb''
      exact means_deterministic (means_relib hm (hnr _ rfl)) (extract_means _ _ hext)
    · cases hr
  · cases hr

/-! ## The escrow's calls, as the receiver runs it -/

section
variable {D : Type} {bytesOf : D → ByteArray} {digestOf : ByteArray → Option D}

/-- The receiver's environment holds the request as `reqAt` of its fields. -/
private theorem reqData_eq (r : Req D) :
    reqData bytesOf r = reqAt (.digest (bytesOf r.agent)) (.nat r.notBefore) (occasionData bytesOf r.occasion)
      (.digest (bytesOf r.principal)) (bytesOf r.self) (.nat r.validUntil) := rfl

/-- **What a run of the escrow returned**, read off its inputs: the state slots read as seven terms
(`stateOf`), the asset is a digest of the World, and the calls are exactly the method's one
transfer: `deposit` (0) from `of depositor asset` into `of self asset` through the grant its
argument names, spending the nonce; `refund` (1) and `release` (2) out of `of self asset` to the
depositor and to the beneficiary, through no grant, spending `"payout"`. Each case names its
method, so the three are exclusive, and no other index is one. -/
def RunCalls (digestOf : ByteArray → Option D) (state : Slots) (method : Nat) (args : ByteArray) (self : D)
    (calls : List (Body D)) : Prop :=
  ∃ (amount : Nat) (arb asset ben dep nk : ByteArray) (p : Label) (a : D),
    readState digestOf (recordRow escrow.state) state = .ok (stateOf amount arb asset ben dep nk p) ∧
    digestOf asset = some a ∧
    ((method = deposit ∧ ∃ (gb : ByteArray) (gd d : D),
        Wire.decodeData depositArg args = .ok (.record [("grant", .digest gb)]) ∧ digestOf gb = some gd ∧
        digestOf dep = some d ∧ calls = [.transfer (.of d a) (.of self a) amount (some gd) (some nk)]) ∨
     (method = refund ∧ ∃ d : D, digestOf dep = some d ∧
        calls = [.transfer (.of self a) (.of d a) amount none (some payoutKey)]) ∨
     (method = release ∧ ∃ b : D, digestOf ben = some b ∧
        calls = [.transfer (.of self a) (.of b a) amount none (some payoutKey)]))

/-- **The escrow's calls are what the receiver's run returns.** A successful `runMeasured` of the
escrow package (the pinned package cell reads as `escrow`; the World's digest decoder reads every
id's bytes back) is `RunCalls` of its state, method, arguments, request object and calls, for every
value of the terms, of the rest of the request and of the rows. -/
theorem escrow_run_calls (hdig : ∀ x, digestOf (bytesOf x) = some x)
    {look : Pinned D} {rv : RowView D} {pkg : D} {state : Slots} {method : Nat} {args : ByteArray}
    {r : Req D} {budget : Nat} {s : Slots} {calls : List (Body D)} {rows : List (RowSlot D × RowAct)}
    {t n : Nat}
    (hpkg : readPackage look pkg = .ok escrow)
    (h : runMeasured bytesOf digestOf look rv pkg state method args r budget = .ok (s, calls, rows, t, n)) :
    RunCalls digestOf state method args r.self calls := by
  obtain ⟨L, g, p, x, sd, ad, wd, v, c, e, ds, hl, hp, hres, hsd, had, -, hb, hm, hc, -, -⟩ := runMeasured_means h
  obtain ⟨hpe, f, hlib⟩ := load_top bytesOf digestOf (fuel := closureDepthMax - 1) (hdig pkg) hpkg hl
  rw [hp] at hpe
  cases hpe
  rw [relocate_noRef f _ escrow_noRef] at hlib
  obtain ⟨hx, hty⟩ := escrow_resolve hres
  rw [hty] at hm
  obtain ⟨amount, arb, asset, ben, dep, nk, ph, rfl⟩ := escrow_state_shape (readState_conforms hsd)
  rw [reqData_eq] at hb
  refine ⟨amount, arb, asset, ben, dep, nk, ph, ?_⟩
  rcases hx with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · obtain ⟨gb, rfl⟩ := deposit_arg_shape (decodeData_conforms had)
    have hd := run_result hlib hb hm (escrow_method_results amount arb asset ben dep nk (bytesOf r.self) gb ph
      _ _ _ _ _ (.record []) wd).1
    simp only [resultD, Data.record.injEq, List.cons.injEq, Prod.mk.injEq, and_true, true_and] at hd
    obtain ⟨rfl, -, -⟩ := hd
    cases ha : digestOf asset <;> cases hg : digestOf gb <;> cases hdp : digestOf dep <;>
      simp [callsOf, callsOf.go, bodyOf, acctRefOf, Lang.digestAt, natOf, optOf, bytesAt, hdig, ha, hg, hdp,
        transferD, ofD, optSome, bind, Except.bind, pure, Except.pure, Except.map] at hc
    exact ⟨_, hsd, rfl, .inl ⟨rfl, gb, _, _, had, hg, rfl, hc.symm⟩⟩
  · have hd := run_result hlib hb hm (escrow_method_results amount arb asset ben dep nk (bytesOf r.self) .empty ph
      _ _ _ _ _ ad wd).2.1
    simp only [resultD, Data.record.injEq, List.cons.injEq, Prod.mk.injEq, and_true, true_and] at hd
    obtain ⟨rfl, -, -⟩ := hd
    cases ha : digestOf asset <;> cases hdp : digestOf dep <;>
      simp [callsOf, callsOf.go, bodyOf, acctRefOf, Lang.digestAt, natOf, optOf, bytesAt, hdig, ha, hdp,
        transferD, ofD, optSome, optNone, bind, Except.bind, pure, Except.pure, Except.map] at hc
    exact ⟨_, hsd, rfl, .inr (.inl ⟨rfl, _, rfl, hc.symm⟩)⟩
  · have hd := run_result hlib hb hm (escrow_method_results amount arb asset ben dep nk (bytesOf r.self) .empty ph
      _ _ _ _ _ ad wd).2.2
    simp only [resultD, Data.record.injEq, List.cons.injEq, Prod.mk.injEq, and_true, true_and] at hd
    obtain ⟨rfl, -, -⟩ := hd
    cases ha : digestOf asset <;> cases hbn : digestOf ben <;>
      simp [callsOf, callsOf.go, bodyOf, acctRefOf, Lang.digestAt, natOf, optOf, bytesAt, hdig, ha, hbn,
        transferD, ofD, optSome, optNone, bind, Except.bind, pure, Except.pure, Except.map] at hc
    exact ⟨_, hsd, rfl, .inr (.inr ⟨rfl, _, rfl, hc.symm⟩)⟩

/-- **At the kernel's call**: `invoke` runs `X.program.run` on the object's package; where that
program is the language over the World's own codec and the `Ctx` is lawful, a successful run of the
escrow package returns exactly the method's one transfer (`escrow_run_calls`). -/
theorem escrow_program_calls {X : Ctx D} (hX : X.Lawful) (hp : X.program = Lang.program X.env.bytes X.digestOf)
    {look : Pinned D} {rv : RowView D} {pkg : D} {state : Slots} {method : Nat} {args : ByteArray}
    {r : Req D} {budget : Nat} {s : Slots} {calls : List (Body D)} {rows : List (RowSlot D × RowAct)}
    {used : Nat}
    (hpkg : readPackage look pkg = .ok escrow)
    (h : X.program.run look rv pkg state method args r budget = .ok (s, calls, rows, used)) :
    RunCalls X.digestOf state method args r.self calls := by
  rw [hp] at h
  change (runMeasured X.env.bytes X.digestOf look rv pkg state method args r budget).map _ = _ at h
  cases hm : runMeasured X.env.bytes X.digestOf look rv pkg state method args r budget with
  | error _ => rw [hm] at h; cases h
  | ok y =>
    obtain ⟨s', calls', rows', t', n'⟩ := y
    rw [hm] at h
    simp only [Except.map, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl, -⟩ := h
    exact escrow_run_calls hX.digestOf_bytes hpkg hm

end

/-- **Deployed**: the node's `Ctx` (`Host.Deployed.X`: the deployed codec, `Lang.program` over it)
meets both premises (`Receive.deployed_ctx_lawful`, the program is its own codec's by
construction), so a successful run of the escrow package there returns exactly the method's one
transfer, with no premise but the package. -/
theorem escrow_run_deployed
    {look : Pinned Codec.Digest} {rv : RowView Codec.Digest} {pkg : Codec.Digest} {state : Slots}
    {method : Nat} {args : ByteArray} {r : Req Codec.Digest} {budget : Nat} {s : Slots}
    {calls : List (Body Codec.Digest)} {rows : List (RowSlot Codec.Digest × RowAct)} {used : Nat}
    (hpkg : readPackage look pkg = .ok escrow)
    (h : (Codec.Deployed.ctx (Lang.program Codec.Digest.bytes Codec.Digest.ofBytes?)).program.run look rv pkg
      state method args r budget = .ok (s, calls, rows, used)) :
    RunCalls Codec.Digest.ofBytes? state method args r.self calls :=
  escrow_program_calls (deployed_ctx_lawful _) rfl hpkg h

/-! ## Teeth -/

/-- The escrow's body with `release` holding `refund`'s method term: one field moved. -/
private def swapped : Term :=
  .record [("deposit", mth 0), ("escrow", law), ("refund", mth 1), ("release", mth 1)]

private def stT : Data := stateOf 5 "a".toUTF8 "x".toUTF8 "b".toUTF8 "d".toUTF8 "n".toUTF8 "held"
private def rqT : Data := reqAt (.digest "s".toUTF8) (.nat 0) (.inj "invoke" (.nat 2)) (.digest "s".toUTF8) "e".toUTF8 (.nat 0)
private def envT : Env := [rqT.toVal, (Data.record []).toVal, stT.toVal, (Data.record []).toVal]

private theorem swapped_run : ∃ v u, eval [swapped] 1000 (apply4 0 "release") envT = .value v u ∧
    ∃ f, (Machine.mk [swapped]).extract resultOf 1000 v =
      .ok (resultD (transferD (ofD "e".toUTF8 "x".toUTF8) (ofD "d".toUTF8 "x".toUTF8) 5 optNone
        (optSome (.bytes payoutKey))) (stateOf 5 "a".toUTF8 "x".toUTF8 "b".toUTF8 "d".toUTF8 "n".toUTF8 "refunded"), f) :=
  ⟨_, _, rfl, _, rfl⟩

/-- **Tooth for `run_result`: the body premise bites.** Under a closure whose body differs from
the escrow's in one field (`release` holding `refund`'s term), `apply4 0 "release"` means a result
(the depositor paid, phase `refunded`) that is not `methodResult "release"` (the beneficiary paid,
phase `released`): `run_result` without `lib[g]? = some escrow.body` is false. -/
theorem run_result_needs_body : ∃ v d dE,
    BigStep [swapped] envT (apply4 0 "release") (.ok v) ∧ Means [swapped] resultOf v d ∧
      methodResult "release" stT (.record []) rqT (.record []) = some dE ∧ d ≠ dE := by
  obtain ⟨v, u, he, f, hx⟩ := swapped_run
  refine ⟨v, _, _, run_bigStep he, extract_means _ _ hx,
    (escrow_method_results 5 "a".toUTF8 "x".toUTF8 "b".toUTF8 "d".toUTF8 "n".toUTF8 "e".toUTF8 .empty "held"
      _ _ _ _ _ _ _).2.2, ?_⟩
  intro hd
  simp only [resultD, transferD, ofD, optSome, Data.record.injEq, List.cons.injEq, Prod.mk.injEq, Data.inj.injEq,
    Data.digest.injEq, true_and, and_true] at hd
  exact absurd hd.1 (by decide)

/-- **Tooth for `escrow_method_results` and the chain's count**: `spends` tells the results apart:
a release's spends the payout key out of the escrow's own account, a deposit's (by a depositor that
is not the escrow) does not, so `escrow_one_payout` does not hold by `spends` being constant. -/
theorem escrow_run_spends (amount : Nat) (arb asset ben dep nk self g : ByteArray) (p : Label)
    (agent nb occ pr vu arg rows : Data) (hne : dep ≠ self) :
    spends self asset (methodResult "release" (stateOf amount arb asset ben dep nk p) arg
      (reqAt agent nb occ pr self vu) rows) = true ∧
    spends self asset (methodResult "deposit" (stateOf amount arb asset ben dep nk p) (.record [("grant", .digest g)])
      (reqAt agent nb occ pr self vu) rows) = false := by
  obtain ⟨h0, -, h2⟩ := escrow_method_results amount arb asset ben dep nk self g p agent nb occ pr vu arg rows
  rw [h0, h2]
  simp [spends, resultD, transferD, ofD, optSome, Data.field, Row.find?, hne, payoutKey]

/-- **Tooth for `escrow_run_calls`: `RunCalls` pins the payee.** Over a decoder that names one id per
bytes, from a state whose beneficiary and depositor differ, a release whose call pays the depositor
is not `RunCalls`: the conclusion is not satisfied by any call to the escrow's own asset. -/
theorem run_calls_pins_payee {D : Type} {digestOf : ByteArray → Option D}
    (hinj : ∀ x y z, digestOf x = some z → digestOf y = some z → x = y)
    {state : Slots} {amount : Nat} {arb asset ben dep nk : ByteArray} {p : Label} {args : ByteArray}
    {self a d : D} (hst : readState digestOf (recordRow escrow.state) state = .ok (stateOf amount arb asset ben dep nk p))
    (hne : ben ≠ dep) (hd : digestOf dep = some d) :
    ¬ RunCalls digestOf state release args self [.transfer (.of self a) (.of d a) amount none (some payoutKey)] := by
  rintro ⟨amount', arb', asset', ben', dep', nk', p', a', hst', -, hc⟩
  rw [hst] at hst'
  simp only [Escrow.stateOf, Except.ok.injEq, Data.record.injEq, List.cons.injEq, Prod.mk.injEq, Data.nat.injEq,
    Data.digest.injEq, Data.bytes.injEq, true_and, and_true] at hst'
  obtain ⟨-, -, -, rfl, -⟩ := hst'
  rcases hc with ⟨hm, -⟩ | ⟨hm, -⟩ | ⟨-, b, hb, hcs⟩
  · cases hm
  · cases hm
  · simp only [List.cons.injEq, Body.transfer.injEq, AcctRef.of.injEq, and_true] at hcs
    obtain ⟨-, ⟨rfl, -⟩, -⟩ := hcs
    exact hne (hinj _ _ _ hb hd)

end Nanodregg.Ledger.Proofs
