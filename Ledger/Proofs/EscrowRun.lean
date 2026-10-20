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

* `escrow_runs_one_payout`, the package's statement over the receiver's runs: along any sequence
  of runs the receiver commits on one escrow (`Runs`: each a successful run in its own view whose
  package cell reads as `escrow`, judged by the package's law and the cell's laws over the slots
  before and after, the next run reading slots that hold, key by key, what this one wrote (read by
  `readState` through Lang's `readState_get`), read back by LANG-63's
  `runMeasured_means`), at most one returned call is a payout (`payoutCalls`: a transfer through
  no grant), by `Std.chain_count`: `runs_chain` reads the runs as a `Std.Chain` of the escrow law's
  admitted steps under every lib (`escrow_step_admits`, through LANG's `judgeOne_admits_relib`;
  `escrow_law_noRef`, `escrow_law_isLaw`), each paired with its run's calls, of which at most one
  is a payout and a payout only into a settled state (`runCalls_payout`); `payoutCalls_le_one`
  marks the settled steps and `escrow_absorbing` stops the chain at one. The same count serves the
  World's history (`Ledger.Proofs.EscrowInvokes`). `escrow_runs_after_payout`: a run that pays out
  is the last the receiver commits (`chain_stops` on the same chain; `escrow_judge_settled`: the
  judge refuses everything out of `released` and `refunded`).
  `escrow_program_one_payout` and `escrow_runs_deployed`: at a lawful `Ctx` over its own codec
  and at the node's, premise only the runs (`Ledger.Proofs.EscrowWitness.escrow_runs_witness`: a
  deposit then a release there, evaluated by the kernel, is a `Runs` with exactly one payout).

Teeth: `run_result_needs_body` (another body at `g` gives the release another result: the body
premise is not idle); `run_calls_pins_payee` (a release paying the depositor, from a state whose
beneficiary is another, is not `RunCalls`); `escrow_judge_bites` (from `released` the method still
pays, the law admits nothing: the bound is the judge's); `payout_call_tells` (the count is not
constant: a deposit's grant-named transfer is not a payout).
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

/-- The escrow's law mentions no closure package. -/
theorem escrow_law_noRef : NoRef law := by
  have h := escrow_noRef
  rw [escrow_body, fields_eq] at h
  exact h.2.1

/-- The escrow's law has a law's shape (`λ old new req. body`). -/
theorem escrow_law_isLaw : IsLaw law := ⟨_, _, _, _, rfl⟩

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
(`stateOf`), the asset is a digest of the World, the slots the run wrote read back as the same
terms in the method's target phase, and the calls are exactly the method's one transfer: `deposit`
(0, to `held`) from `of depositor asset` into `of self asset` through the grant its argument
names, spending the nonce; `refund` (1, to `refunded`) and `release` (2, to `released`) out of
`of self asset` to the depositor and to the beneficiary, through no grant, spending `"payout"`.
Each case names its method, so the three are exclusive, and no other index is one. -/
def RunCalls (digestOf : ByteArray → Option D) (state : Slots) (method : Nat) (args : ByteArray) (self : D)
    (calls : List (Body D)) (s : Slots) : Prop :=
  ∃ (amount : Nat) (arb asset ben dep nk : ByteArray) (p : Label) (a : D),
    readState digestOf (recordRow escrow.state) state = .ok (stateOf amount arb asset ben dep nk p) ∧
    digestOf asset = some a ∧
    ((method = deposit ∧
        readState digestOf (recordRow escrow.state) s = .ok (stateOf amount arb asset ben dep nk "held") ∧
        ∃ (gb : ByteArray) (gd d : D),
        Wire.decodeData depositArg args = .ok (.record [("grant", .digest gb)]) ∧ digestOf gb = some gd ∧
        digestOf dep = some d ∧ calls = [.transfer (.of d a) (.of self a) amount (some gd) (some nk)]) ∨
     (method = refund ∧
        readState digestOf (recordRow escrow.state) s = .ok (stateOf amount arb asset ben dep nk "refunded") ∧
        ∃ d : D, digestOf dep = some d ∧
        calls = [.transfer (.of self a) (.of d a) amount none (some payoutKey)]) ∨
     (method = release ∧
        readState digestOf (recordRow escrow.state) s = .ok (stateOf amount arb asset ben dep nk "released") ∧
        ∃ b : D, digestOf ben = some b ∧
        calls = [.transfer (.of self a) (.of b a) amount none (some payoutKey)]))

/-- **The escrow's calls are what the receiver's run returns.** A successful `runMeasured` of the
escrow package (the pinned package cell reads as `escrow`; the World's digest decoder reads every
id's bytes back) is `RunCalls` of its state, method, arguments, request object, calls and written
slots, for every value of the terms, of the rest of the request and of the rows. -/
theorem escrow_run_calls (hdig : ∀ x, digestOf (bytesOf x) = some x)
    {look : Pinned D} {rv : RowView D} {pkg : D} {state : Slots} {method : Nat} {args : ByteArray}
    {r : Req D} {budget : Nat} {s : Slots} {calls : List (Body D)} {rows : List (RowSlot D × RowAct)}
    {t n : Nat}
    (hpkg : readPackage look pkg = .ok escrow)
    (h : runMeasured bytesOf digestOf look rv pkg state method args r budget = .ok (s, calls, rows, t, n)) :
    RunCalls digestOf state method args r.self calls s := by
  obtain ⟨L, g, p, x, sd, ad, wd, v, c, e, ds, hl, hp, hres, hsd, had, -, hb, hm, hc, -, -, hrb⟩ :=
    runMeasured_means h
  have hrb := hrb fun x => by rw [hdig]; rfl
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
    obtain ⟨rfl, -, hds⟩ := hd
    cases ha : digestOf asset <;> cases hg : digestOf gb <;> cases hdp : digestOf dep <;>
      simp [callsOf, callsOf.go, bodyOf, acctRefOf, Lang.digestAt, natOf, optOf, bytesAt, hdig, ha, hg, hdp,
        transferD, ofD, optSome, bind, Except.bind, pure, Except.pure, Except.map] at hc
    exact ⟨_, hsd, rfl, .inl ⟨rfl, hds ▸ hrb, gb, _, _, had, hg, rfl, hc.symm⟩⟩
  · have hd := run_result hlib hb hm (escrow_method_results amount arb asset ben dep nk (bytesOf r.self) .empty ph
      _ _ _ _ _ ad wd).2.1
    simp only [resultD, Data.record.injEq, List.cons.injEq, Prod.mk.injEq, and_true, true_and] at hd
    obtain ⟨rfl, -, hds⟩ := hd
    cases ha : digestOf asset <;> cases hdp : digestOf dep <;>
      simp [callsOf, callsOf.go, bodyOf, acctRefOf, Lang.digestAt, natOf, optOf, bytesAt, hdig, ha, hdp,
        transferD, ofD, optSome, optNone, bind, Except.bind, pure, Except.pure, Except.map] at hc
    exact ⟨_, hsd, rfl, .inr (.inl ⟨rfl, hds ▸ hrb, _, rfl, hc.symm⟩)⟩
  · have hd := run_result hlib hb hm (escrow_method_results amount arb asset ben dep nk (bytesOf r.self) .empty ph
      _ _ _ _ _ ad wd).2.2
    simp only [resultD, Data.record.injEq, List.cons.injEq, Prod.mk.injEq, and_true, true_and] at hd
    obtain ⟨rfl, -, hds⟩ := hd
    cases ha : digestOf asset <;> cases hbn : digestOf ben <;>
      simp [callsOf, callsOf.go, bodyOf, acctRefOf, Lang.digestAt, natOf, optOf, bytesAt, hdig, ha, hbn,
        transferD, ofD, optSome, optNone, bind, Except.bind, pure, Except.pure, Except.map] at hc
    exact ⟨_, hsd, rfl, .inr (.inr ⟨rfl, hds ▸ hrb, _, rfl, hc.symm⟩)⟩

/-- **At the kernel's call**: `invoke` runs `X.program.run` on the object's package; where that
program is the language over the World's own codec and the `Ctx` is lawful, a successful run of the
escrow package returns exactly the method's one transfer (`escrow_run_calls`). -/
theorem escrow_program_calls {X : Ctx D} (hX : X.Lawful) (hp : X.program = Lang.program X.env.bytes X.digestOf)
    {look : Pinned D} {rv : RowView D} {pkg : D} {state : Slots} {method : Nat} {args : ByteArray}
    {r : Req D} {budget : Nat} {s : Slots} {calls : List (Body D)} {rows : List (RowSlot D × RowAct)}
    {used : Nat}
    (hpkg : readPackage look pkg = .ok escrow)
    (h : X.program.run look rv pkg state method args r budget = .ok (s, calls, rows, used)) :
    RunCalls X.digestOf state method args r.self calls s := by
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
    RunCalls Codec.Digest.ofBytes? state method args r.self calls s :=
  escrow_program_calls (deployed_ctx_lawful _) rfl hpkg h

/-! ## The chain: the runs the receiver commits on one escrow -/

section
variable {D : Type}

/-- **A sequence of runs the receiver commits** on one object of package `pkg`, from the state slots
`state`, under the program `prog` (the `Ctx`'s, what `invoke` calls): each step, in its own pinned
view `look` (whose package cell reads as `p`), is a successful `prog.run` of any method on any
arguments, request and budget, whose written slots `prog.judge` admits over the slots before (the
package's own law first, then the cell's laws `laws`: what `invoke` checks before it derives the
calls), and the next step reads slots that hold, key by key, what it wrote (`Slots.get`: the cell
`invoke`'s write leaves need not be the same list, only the same contents). The list holds each
step's calls. -/
inductive Runs (prog : Program D) (pkg : D) (p : Package) : Slots → List (List (Body D)) → Prop
  | nil (state : Slots) : Runs prog pkg p state []
  | cons {look : Pinned D} {rv : RowView D} {state : Slots} {method : Nat} {args : ByteArray} {r : Req D}
      {budget : Nat} {s : Slots} {calls : List (Body D)} {rows : List (RowSlot D × RowAct)} {used : Nat}
      {laws : List D} {next : Slots} {rest : List (List (Body D))} :
      readPackage look pkg = .ok p →
      prog.run look rv pkg state method args r budget = .ok (s, calls, rows, used) →
      prog.judge look (some pkg) laws state s r = .ok () →
      (∀ k, next.get k = s.get k) →
      Runs prog pkg p next rest → Runs prog pkg p state (calls :: rest)

variable {bytesOf : D → ByteArray} {digestOf : ByteArray → Option D}

private theorem run_of_program {look : Pinned D} {rv : RowView D} {pkg : D} {state : Slots} {method : Nat}
    {args : ByteArray} {r : Req D} {budget : Nat} {s : Slots} {calls : List (Body D)}
    {rows : List (RowSlot D × RowAct)} {used : Nat}
    (h : (Lang.program bytesOf digestOf).run look rv pkg state method args r budget = .ok (s, calls, rows, used)) :
    ∃ t n, runMeasured bytesOf digestOf look rv pkg state method args r budget = .ok (s, calls, rows, t, n) := by
  change (runMeasured bytesOf digestOf look rv pkg state method args r budget).map _ = _ at h
  cases hm : runMeasured bytesOf digestOf look rv pkg state method args r budget with
  | error _ => rw [hm] at h; cases h
  | ok y =>
    obtain ⟨s', calls', rows', t', n'⟩ := y
    rw [hm] at h
    simp only [Except.map, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl, -⟩ := h
    exact ⟨_, _, rfl⟩

/-- **A settled escrow admits no run**: the receiver's judge of the escrow package (and any further
laws) refuses every transition out of slots that read as a `released` or `refunded` state, whatever
the new slots and the request (`judgeOne_ok`, `escrow_judge_admits`, `escrow_absorbing`). -/
theorem escrow_judge_settled (hdig : ∀ x, digestOf (bytesOf x) = some x)
    {look : Pinned D} {pkg : D} {laws : List D} {old new : Slots} {r : Req D} {o : Data}
    (hpkg : readPackage look pkg = .ok escrow)
    (ho : readState digestOf (recordRow escrow.state) old = .ok o) (hs : Settled o)
    (h : Lang.judge bytesOf digestOf look (some pkg) laws old new r = .ok ()) : False := by
  have h1 : judgeOne bytesOf digestOf look pkg old new r = .ok () := by
    unfold Lang.judge at h
    simp only [bind, Except.bind] at h
    split at h
    · cases h
    · rename_i u hj
      cases u
      exact hj
  obtain ⟨L, g, p, o', n, hload, hpg, ho', -, hall⟩ := judgeOne_ok bytesOf digestOf h1
  obtain ⟨hpg', f, hlib⟩ := load_top bytesOf digestOf (fuel := closureDepthMax - 1) (hdig pkg) hpkg hload
  rw [hpg'] at hpg
  cases hpg
  rw [relocate_noRef f _ escrow_noRef] at hlib
  rw [ho] at ho'
  cases ho'
  exact escrow_absorbing hs (escrow_judge_admits hlib (hall "escrow" (by rw [escrow_laws]; simp)))

/-- The escrow's judge passed its own law: the package's verdict is the first of `judge`'s. -/
theorem escrow_judgeOne {look : Pinned D} {pkg : D} {laws : List D} {old new : Slots} {r : Req D}
    (h : Lang.judge bytesOf digestOf look (some pkg) laws old new r = .ok ()) :
    judgeOne bytesOf digestOf look pkg old new r = .ok () := by
  unfold Lang.judge at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  · rename_i u hj
    cases u
    exact hj

/-- **One judged step of the escrow is one admitted step of its law**, under every lib: the judge's
verdict on the escrow package (`judgeOne_admits_relib`, the law mentions no closure package). -/
theorem escrow_step_admits (hdig : ∀ x, digestOf (bytesOf x) = some x)
    {look : Pinned D} {pkg : D} {laws : List D} {old new : Slots} {r : Req D}
    (hpkg : readPackage look pkg = .ok escrow)
    (h : Lang.judge bytesOf digestOf look (some pkg) laws old new r = .ok ()) :
    ∃ o n, readState digestOf (recordRow escrow.state) old = .ok o ∧
      readState digestOf (recordRow escrow.state) new = .ok n ∧ Std.Admits [] law (reqData bytesOf r) n o := by
  obtain ⟨o, n, ho, hn, hall⟩ := judgeOne_admits_relib bytesOf digestOf (hdig pkg) hpkg escrow_body (escrow_judgeOne h)
  exact ⟨o, n, ho, hn, hall "escrow" (by rw [escrow_laws]; simp) law escrow_field escrow_law_isLaw escrow_law_noRef []⟩

/-- **What a run's calls say of the state it leaves**: at most one payout, and a payout only from
`refund` or `release`, whose state is settled. -/
theorem runCalls_payout {state : Slots} {method : Nat} {args : ByteArray} {self : D} {calls : List (Body D)}
    {s : Slots} (h : RunCalls digestOf state method args self calls s) {n : Data}
    (hn : readState digestOf (recordRow escrow.state) s = .ok n) :
    (calls.filter isPayoutCall).length ≤ 1 ∧ (0 < (calls.filter isPayoutCall).length → Settled n) := by
  obtain ⟨amount, arb, asset, ben, dep, nk, ph, a, -, -, hx⟩ := h
  rcases hx with ⟨-, -, gb, gd, d, -, -, -, rfl⟩ | ⟨-, hs, d, -, rfl⟩ | ⟨-, hs, b, -, rfl⟩
  · exact ⟨by simp [isPayoutCall], fun h => by simp [isPayoutCall] at h⟩
  · rw [hs] at hn; cases hn
    exact ⟨by simp [isPayoutCall], fun _ => .inr ⟨_, rfl⟩⟩
  · rw [hs] at hn; cases hn
    exact ⟨by simp [isPayoutCall], fun _ => .inl ⟨_, rfl⟩⟩

end

section
variable {D : Type}

open Classical in
/-- **The count, by `chain_count`.** Along a chain of the escrow law's admitted steps, each paired
with the calls of the run it came from, where a run returns at most one payout and a payout only
into a settled state, at most one call is a payout: `chain_count` marks the steps into a settled
state, and the law admits nothing out of one (`escrow_absorbing`). -/
theorem payoutCalls_le_one {o : Data} :
    ∀ (ps : List (List (Body D) × (Data × Data))), Std.Chain (Std.Admits [] law) o (ps.map Prod.snd) →
      (∀ x ∈ ps, (x.1.filter isPayoutCall).length ≤ 1 ∧ (0 < (x.1.filter isPayoutCall).length → Settled x.2.2)) →
      payoutCalls (ps.map Prod.fst) ≤ 1 := by
  intro ps hc hp
  have hcount := Std.chain_count (fun s => decide (Settled s.2)) Settled
    (fun _ _ _ _ hm => of_decide_eq_true hm) (fun _ _ _ hs ha => escrow_absorbing hs ha) hc
  have key : ∀ (qs : List (List (Body D) × (Data × Data))),
      (∀ x ∈ qs, (x.1.filter isPayoutCall).length ≤ 1 ∧ (0 < (x.1.filter isPayoutCall).length → Settled x.2.2)) →
      payoutCalls (qs.map Prod.fst) ≤ ((qs.map Prod.snd).filter fun s => decide (Settled s.2)).length := by
    intro qs
    induction qs with
    | nil => intro _; simp [payoutCalls]
    | cons x rest ih =>
        intro hq
        have hr := ih (fun y hy => hq y (List.mem_cons_of_mem _ hy))
        obtain ⟨h1, h2⟩ := hq x (List.mem_cons_self ..)
        simp only [payoutCalls, List.map_cons, List.sum_cons, List.filter_cons] at hr ⊢
        by_cases hs : Settled x.2.2
        · simp only [hs, decide_true, if_true, List.length_cons]
          omega
        · have h0 : (x.1.filter isPayoutCall).length = 0 := by
            rcases Nat.eq_zero_or_pos (x.1.filter isPayoutCall).length with h | h
            · exact h
            · exact absurd (h2 h) hs
          simp only [hs, decide_false, Bool.false_eq_true, if_false]
          omega
  exact Nat.le_trans (key ps hp) hcount

end

section
variable {D : Type} {bytesOf : D → ByteArray} {digestOf : ByteArray → Option D}

/-- **The receiver's runs on an escrow are a chain of its law**, step for step, each paired with the
calls its run returned (`escrow_step_admits`; the next run reads what this one wrote, `readState_get`). -/
theorem runs_chain (hdig : ∀ x, digestOf (bytesOf x) = some x) {pkg : D} :
    ∀ {state : Slots} {runs : List (List (Body D))},
      Runs (Lang.program bytesOf digestOf) pkg escrow state runs →
      ∀ {o : Data}, readState digestOf (recordRow escrow.state) state = .ok o →
        ∃ ps : List (List (Body D) × (Data × Data)), ps.map Prod.fst = runs ∧
          Std.Chain (Std.Admits [] law) o (ps.map Prod.snd) ∧
          ∀ x ∈ ps, (x.1.filter isPayoutCall).length ≤ 1 ∧ (0 < (x.1.filter isPayoutCall).length → Settled x.2.2) := by
  intro state runs h
  induction h with
  | nil => exact fun _ => ⟨[], rfl, .nil _, by simp⟩
  | @cons look rv state method args r budget s calls rows used laws next rest hpkg hrun hj hnext hr ih =>
      intro o ho
      obtain ⟨o', n, ho', hn, hadm⟩ := escrow_step_admits hdig hpkg hj
      rw [ho] at ho'
      cases ho'
      have hn' : readState digestOf (recordRow escrow.state) next = .ok n := (readState_get hnext).trans hn
      obtain ⟨ps, hps, hc, hp⟩ := ih hn'
      obtain ⟨t, k, hm⟩ := run_of_program hrun
      have hpay := runCalls_payout (escrow_run_calls hdig hpkg hm) hn
      refine ⟨(calls, (reqData bytesOf r, n)) :: ps, by simp [hps], .cons hadm hc, fun x hx => ?_⟩
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hpay
      · exact hp x hx

/-- A sequence of runs with a first run starts from a state the escrow reads. -/
theorem runs_start (hdig : ∀ x, digestOf (bytesOf x) = some x) {pkg : D} {state : Slots}
    {calls : List (Body D)} {rest : List (List (Body D))}
    (h : Runs (Lang.program bytesOf digestOf) pkg escrow state (calls :: rest)) :
    ∃ o, readState digestOf (recordRow escrow.state) state = .ok o := by
  cases h with
  | cons hpkg _ hj _ _ =>
      obtain ⟨o, -, ho, -⟩ := escrow_step_admits hdig hpkg hj
      exact ⟨o, ho⟩

/-- **After a payout, the receiver commits nothing more** on the escrow: a run that returned a
payout (`isPayoutCall`) is the last step of every sequence of committed runs it starts. A
corollary of the chain: the payout's step leaves a settled state, and `chain_stops`. -/
theorem escrow_runs_after_payout (hdig : ∀ x, digestOf (bytesOf x) = some x) {pkg : D} {state : Slots}
    {calls : List (Body D)} {rest : List (List (Body D))}
    (h : Runs (Lang.program bytesOf digestOf) pkg escrow state (calls :: rest))
    (hp : 0 < payoutCalls [calls]) : rest = [] := by
  obtain ⟨o, ho⟩ := runs_start hdig h
  obtain ⟨ps, hps, hc, hpay⟩ := runs_chain hdig h ho
  cases ps with
  | nil => cases hps
  | cons x ps' =>
      obtain ⟨xc, rq, n⟩ := x
      simp only [List.map_cons, List.cons.injEq] at hps
      obtain ⟨rfl, rfl⟩ := hps
      have hs : Settled n := (hpay _ (List.mem_cons_self ..)).2 (by simpa [payoutCalls] using hp)
      cases hc with
      | cons _ hrest =>
          have := Std.chain_stops Settled (fun _ _ _ hs' ha => escrow_absorbing hs' ha) hs hrest
          simpa using congrArg List.length this

/-- **The escrow pays out at most once, over the receiver's own runs.** Along any sequence of runs
the receiver commits on an object whose package cell reads as `escrow` (each a successful
`runMeasured`, the next one reading slots that hold what it wrote, each admitted by the judge),
from any state, of any methods on any arguments, requests and budgets, at most one call the runs
return is a payout (a transfer through no grant), under a decoder that reads every id's bytes
back. `chain_count` over `runs_chain` (`payoutCalls_le_one`). -/
theorem escrow_runs_one_payout (hdig : ∀ x, digestOf (bytesOf x) = some x) {pkg : D} {state : Slots}
    {runs : List (List (Body D))} (h : Runs (Lang.program bytesOf digestOf) pkg escrow state runs) :
    payoutCalls runs ≤ 1 := by
  cases runs with
  | nil => simp [payoutCalls]
  | cons calls rest =>
      obtain ⟨o, ho⟩ := runs_start hdig h
      obtain ⟨ps, hps, hc, hp⟩ := runs_chain hdig h ho
      rw [← hps]
      exact payoutCalls_le_one ps hc hp

/-- **At the kernel's program**: the same for the runs and judges of a lawful `Ctx` whose program
is the language over the World's own codec. -/
theorem escrow_program_one_payout {X : Ctx D} (hX : X.Lawful) (hp : X.program = Lang.program X.env.bytes X.digestOf)
    {pkg : D} {state : Slots} {runs : List (List (Body D))} (h : Runs X.program pkg escrow state runs) :
    payoutCalls runs ≤ 1 := by
  rw [hp] at h
  exact escrow_runs_one_payout hX.digestOf_bytes h

end

/-- **Deployed**: along any sequence of runs the node's receiver (`Host.Deployed.X`) commits on an
object whose package cell reads as `escrow` in each run's view, at most one call is a payout; no
premise but the runs (each carrying its package read). -/
theorem escrow_runs_deployed {pkg : Codec.Digest} {state : Slots} {runs : List (List (Body Codec.Digest))}
    (h : Runs (Codec.Deployed.ctx (Lang.program Codec.Digest.bytes Codec.Digest.ofBytes?)).program pkg escrow
      state runs) :
    payoutCalls runs ≤ 1 :=
  escrow_program_one_payout (deployed_ctx_lawful _) rfl h

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

/-- **Tooth for `escrow_run_calls`: `RunCalls` pins the payee.** Over a decoder that names one id per
bytes, from a state whose beneficiary and depositor differ, a release whose call pays the depositor
is not `RunCalls`: the conclusion is not satisfied by any call to the escrow's own asset. -/
theorem run_calls_pins_payee {D : Type} {digestOf : ByteArray → Option D}
    (hinj : ∀ x y z, digestOf x = some z → digestOf y = some z → x = y)
    {state s : Slots} {amount : Nat} {arb asset ben dep nk : ByteArray} {p : Label} {args : ByteArray}
    {self a d : D} (hst : readState digestOf (recordRow escrow.state) state = .ok (stateOf amount arb asset ben dep nk p))
    (hne : ben ≠ dep) (hd : digestOf dep = some d) :
    ¬ RunCalls digestOf state release args self [.transfer (.of self a) (.of d a) amount none (some payoutKey)] s := by
  rintro ⟨amount', arb', asset', ben', dep', nk', p', a', hst', -, hc⟩
  rw [hst] at hst'
  simp only [Escrow.stateOf, Except.ok.injEq, Data.record.injEq, List.cons.injEq, Prod.mk.injEq, Data.nat.injEq,
    Data.digest.injEq, Data.bytes.injEq, true_and, and_true] at hst'
  obtain ⟨-, -, -, rfl, -⟩ := hst'
  rcases hc with ⟨hm, -⟩ | ⟨hm, -⟩ | ⟨-, -, b, hb, hcs⟩
  · cases hm
  · cases hm
  · simp only [List.cons.injEq, Body.transfer.injEq, AcctRef.of.injEq, and_true] at hcs
    obtain ⟨-, ⟨rfl, -⟩, -⟩ := hcs
    exact hne (hinj _ _ _ hb hd)

/-- **Tooth for `escrow_runs_one_payout`: the judge premise bites.** From a `released` state the
receiver's term still returns a payout (the method does not read its phase), and the law admits no
act out of that state: a sequence of runs without the judge (release, then release again) would
return two payouts, so the bound is the judge's, not the method's. -/
theorem escrow_judge_bites {lib : List Term} (amount : Nat) (arb asset ben dep nk self : ByteArray)
    (agent nb occ pr vu arg rows : Data) :
    methodResult "release" (stateOf amount arb asset ben dep nk "released") arg (reqAt agent nb occ pr self vu) rows =
      some (resultD (transferD (ofD self asset) (ofD ben asset) amount optNone (optSome (.bytes payoutKey)))
        (stateOf amount arb asset ben dep nk "released")) ∧
    ∀ rq n, ¬ Std.Admits lib law rq n (stateOf amount arb asset ben dep nk "released") :=
  ⟨(escrow_method_results amount arb asset ben dep nk self .empty "released" agent nb occ pr vu arg rows).2.2,
    fun _ _ => escrow_absorbing (.inl ⟨_, rfl⟩)⟩

/-- **Tooth for the count**: `isPayoutCall` tells a payout's call from a deposit's (which names its
grant), so `payoutCalls` is not constant over what `RunCalls` allows. -/
theorem payout_call_tells {D : Type} (src dst : AcctRef D) (amount : Nat) (g : D) (once : Option ByteArray) :
    isPayoutCall (.transfer src dst amount none once) = true ∧
      isPayoutCall (.transfer src dst amount (some g) once) = false := ⟨rfl, rfl⟩

end Nanodregg.Ledger.Proofs
