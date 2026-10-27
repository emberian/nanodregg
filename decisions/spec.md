# decisions/spec.md — the top-level spec (`Spec/`)

Owner: SPEC (its own layer since SPEC-3: gates/OWNERS rows `Spec/` and `decisions/spec.md`, prefix `spec:`;
the first four landings went in as `root:`). Design:
`redregg/work/promo/TOPLEVEL-SPEC.md`. Format per decisions/README.md.

## SPEC-1 Claims are predicates on a record of the deployed entry points (2026-10-26)

**Decision.** `Spec/System.lean` defines `System D`, a record whose fields are the decisions the
binaries run (`receive`, `recordedBy`, `admit`, `refuse`, `submit`, `follow`, `settle`, `handle`) plus
the context they read through (`X`, `dc`, `B`); `deployed d` fills each with the deployed definition
(`B` exactly as `Host/Follow.lean` builds it from the Store's `worldDigest`). Every claim is
`System D → Prop`; the top theorem is `Claim (deployed d)`; the floor is `¬ Claim trivial` for a
trivial system that is `deployed d` with one field replaced.

**Alternatives.** (a) An abstract vat the kernel refines (GATES' reading): a second machine beside
`World.admit`, a twin by law 1, and its own non-vacuity needs the same floors. (b) Claims stated
directly over the deployed definitions: no field to swap, so no floor can be stated; the kernel's
transition is a fixed `def` (`World.admit`, `receive`), not a `Ctx` field. (c) Claims parameterised by
the whole `Ctx`: `Ctx` varies the codec, `verify` and the program, not the kernel's decisions.

**Why.** It is the shape the four `host_step_folds_tooth_*` already use (one arm of a record
replaced, the statement refused), generalised; it costs one record and no second semantics.

**CRITIQUE.** The fields fix the granularity of every floor: a trivial system can swap `receive` as a
whole, not one check inside it (the spec's `openKernel`, "`ownerAuthority` returns the actor", is not
expressible without copying `receive`). `deployed` can drift from what the binaries call: it is a
second list of the wiring `Host/Follow.lean` and `Host/Serve.lean` perform, checked by nothing but
reading; a binary that called a different `step` would leave `deployed` true and the claims about
the wrong thing.

**META-CRITIQUE.** I took KERNEL's side of the GATES/KERNEL debate because the design document did,
and the design document did because it is cheaper to reuse names than to write a model. The drift
risk of `deployed` is the same risk the readers named in `host_run_audits` (a theorem about a
re-deriver nobody ran); the remedy (the binaries' `main` taking a `System`) is not taken here.

**Status.** open.

## SPEC-2 The layout the closure gates force: the trusted reading lives under `Spec/Proofs/` (2026-10-26)

**Decision.** `Spec/System.lean` (a def-module: the record and `deployed`, no statement);
`Spec/Proofs/Claims.lean` (every claim, and the vocabulary they share: `Decided`, `Audited`, `Start`,
`keyFaithful`, `Moves`, `Reach`); `Spec/Proofs/Floor.lean` (the trivial systems, their refutations, the
deployed run); `Spec/Proofs/Bridge.lean` and `Spec/Proofs/Deployed.lean` (proofs). The trusted
reading is System + Claims + Floor (≈ 520 lines); Bridge and Deployed are checked, not read.

**Alternatives.** TOPLEVEL-SPEC §12's `Spec/Claims.lean` beside `Spec/Floor.lean`: red at closure C3 (a
def-module exporting a statement) and C4 (importing `Kernel.Proofs.Rederive`, where `Honest` lives).
Amending law 8 so a spec tier may hold statements outside `Proofs` (the design's own proposal).

**Why.** The gates are right that a statement is not a definition; the path name is the only cost.

**CRITIQUE.** A reader looking for "the spec" finds it in a directory named `Proofs`, beside the
proofs it is meant to be read without. `Floor.lean` must hold its deployed run's defs `private` (C3),
so the run cannot be named from outside the file.

**META-CRITIQUE.** Choosing not to amend law 8 is choosing the path of no argument with GATES; the
design said the amendment was owed. If a second spec-tier consumer appears, amend it then.

**Status.** open.

## SPEC-3 `Decided`/`Audited`: the kernel's honesty with the kernel a parameter (2026-10-26)

**Decision.** `Decided S` is `Receive.Honest` with `receive`, `recordedBy`, `admit`, `refuse` read from
`S`; `Audited S w l w' := S.fold w l = .ok w' ∧ Decided S w l`. `Spec.Proofs.Bridge` proves
`audited_iff`: for any `S` whose four kernel fields are the kernel's, `Audited` is exactly
`World.fold ∧ Honest`, so every theorem over the kernel's audit is a theorem about `Audited deployed`.

**Alternatives.** (a) Claims over `Receive.Honest X` directly: then a kernel that admits everything
cannot be plugged in and INTEGRITY has no floor (the apex argument of TOPLEVEL-SPEC §2.FLOOR needs
`OneHistory` to hold of that kernel and `Integrity` to fail of it). (b) Make `Kernel.Receive.Honest`
itself the instance `Decided (deployed …)`: a cross-layer change under every audit theorem.

**Why.** The bridge is four `Iff.rfl`s under an induction; the shape is identical by construction.

**CRITIQUE.** Law 1: two shapes of one predicate. They agree today by a proof that breaks loudly if
`Honest` changes (good), but a reader can trust `Decided`'s text while `Honest` grows a clause.

**META-CRITIQUE.** (b) is the right end state and I priced it as "a cross-layer change", which is the
cost-estimate-as-constraint substitution CLAUDE.md names. It is not done here because the statement
the kernel lane owns should be restated by the kernel lane; it is filed, not deferred in prose.

**Status.** open; (b) tasked to KERNEL.

## SPEC-4 A1 needs a named relay premise, and its `Start` names the trusted key (2026-10-26)

**Decision.** `OneHistory.member S relay` quantifies over the frames `Reach S relay` allows; the
deployed theorem is stated under `keyFaithful`: every continuation that parses as `adopt INVITE KEY`
names the sponsor key the member trusts. `Start S me trusted` is a genesis World, or a base whose
bytes hash to the pin of an invitation `trusted` signed for `me.world`.

**Found.** TOPLEVEL-SPEC §2.1 says A1 holds "whatever frames a follower is fed". It does not, for one
arm: `Command.step`'s adopt reads its sponsor key from the continuation's argv, and the continuation
is client-held bytes (`State.ofBytes`); from a World that holds nothing (`atGenesis`, every fresh
member), a forged `adopt INV KEY'` makes follow adopt any base whose pin `KEY'` signed. With `Start`'s
key existentially quantified the claim would be VACUOUS (every World with the member's origin is a
pinned start); with it fixed the claim is false under an arbitrary relay. Every other arm re-derives
whatever the continuation says, so `keyFaithful` is the whole premise.

**Alternatives.** An arbitrary relay and a vacuous `Start` (rejected: the floor would not go
through, which is how this was found). `relay` as the full faithful-relay model (`FollowRun`'s `hk`):
stronger than needed; the claim's other arms need nothing.

**Why.** It is the smallest true premise, and it is exactly what TOPLEVEL-SPEC §11.2 (the command's
state inside follow) deletes.

**CRITIQUE.** `keyFaithful` is a property of the Rust `nd` process's continuation handling, which
nothing in Lean checks; the premise is the `stdio-leg` TCB row in miniature.

**META-CRITIQUE.** The design document's "true, not composed" was read as permission to compose; the
composition is where the false clause showed. Every "true, not composed" in the design deserves
the same suspicion.

**Status.** open; premise deleted by §11.2.

## SPEC-5 The INHABITED run is computed at the deployed `Ctx` by `native_decide` (2026-10-26)

**Decision.** `Spec.Proofs.Floor`'s run: a genesis World with one founder (keys from Ed25519 seeds),
and the founder's `rotate` to its precommitted key (signed by the key it moves to), staged by
`submit` and re-derived by `rederiveLog` at `Host.Deployed.X`. Four facts about it (`run_rederives`,
`run_continuation`, `run_call_decodes`, `run_call_admits`) are `native_decide`, with allow and TCB
rows; everything else is kernel-checked from them.

**Alternatives.** A toy `Ctx UInt8` with `decide +kernel` (the tree's precedent, GrantCapTooth): a toy
run inhabits a toy system, not the deployed one. A staged kernel proof: cSHAKE256 and Ed25519 under
whnf are measured reduction bombs (9.2 GB for one verify).

**Why.** The claim is about the deployed system; the run must be one.

**CRITIQUE.** The run is the cheapest Turn there is: it runs no program, moves no value and touches no
object, so `inhabited_audited` reaches INTEGRITY's premise but not the non-trivial case of B2 (value
moved) or B3 (a law judged a step). Those need a run with a well and an object; not yet built.

**META-CRITIQUE.** I picked `rotate` because it needs nothing installed, i.e. because it was cheap;
the witness should be chosen by which case it inhabits.

**Status.** open; richer run owed (value, law, a deferred envelope, a settled command).

## SPEC-6 A1's proof sharpens `step_world` inside Spec; B2's floor must be a non-reachable World (2026-10-26)

**Decision.** `top_oneHistory_member` rests on `step_world_start` (`Spec/Proofs/Member.lean`): the
third arm of `Protocol.Proofs.FollowHead.step_world` ("an adopt, from a World `atGenesis`") with the
adopt's evidence carried (the continuation's parsed `adopt INV KEY`, `adoptPin`, `Thin.accept`, the
origin check). It lives in Spec, not Protocol, because Spec is its only consumer today.

**Found (INFERRED from `admit_value`, `refuse_sumOf`).** Every World a fold reaches from a genesis
World has value sum 0 in every denomination: the system is closed. So B2's floor cannot use a
reachable World on either side; its refuting start must be a canonical World no fold reaches (or the
trivial kernel must be a copy of `World.admit` without `checkValue` with an unbalanced Turn).

**Alternatives.** Land `step_world_start` in Protocol beside `step_world` (cross-layer, and two
statements of one fact until `step_world` is restated as its corollary).

**CRITIQUE.** A Protocol reader extending the adopt arm will not see the Spec lemma that pins it;
the next change to `Command.step` breaks Spec, which is the point, but far from the change.

**META-CRITIQUE.** Kept in my own directory to avoid a cross-layer landing: convenience.

**Status.** open; `step_world` restated as a corollary is PROTOCOL's to take.

## SPEC-7 The floors of B2 and B3: two kernels with one check missing, run at the deployed `Ctx` (2026-10-26)

**Decision.** `Spec/Trivial.lean` gains `minting` (`World.admitImpl` with `checkValue` dropped from
`checkWith`'s sequence, every other check in its order) and `rawWriter` (the kernel's receivers, but a
signed `write` checks the World, the signature, the key and the owner's authority, then lands its
edits at RAW slot keys, judged by no law). `floor_integrity_value`: from the genesis World (canonical,
`receive_genesis_canon`), one Turn bearing a 10-unit value cell is refused `notConserved` by the kernel
and admitted by `minting`, and the denomination's sum moves (`run_mint`). `floor_integrity_law`: the
founder's `create` of a data object re-derives from genesis (so the start is an honest fold, and
`CellsCanon` by `fold_cellsCanon`); the founder's `write` of 32 bytes at edit key 0 is derived by
`rawWriter` and admitted, and the object's package is `none` before and `some _` after
(`run_raw_write`). Both facts are `native_decide` (allow and TCB rows as SPEC-5).

**Found.** SPEC-6 inferred that B2's floor needs a canonical World no fold reaches, built as a term
(cv 01a17a38-9802's recipe). It does not: the claim quantifies over the TRIVIAL system's folds, and
`minting`'s fold from genesis reaches the unbalanced World. What no deployed fold reaches is the end
of the run, which is the floor's point. The term-built World is not needed and was not built.

**Alternatives.** (B2) A `minting` that adds a unit to some balance after `World.admit` (one line, no
copy of the check sequence): refutes the claim but is not a kernel anyone would write; the copy is the
plant TOPLEVEL-SPEC §3.FLOOR names. (B3) `unjudgedKernel` (the program's `judge` admitting all):
refutes the law-chain clause, but refuting it means showing NO `tr` with `ObjectHistory` carries the
chain, and `ObjectHistory` is a relation over Worlds, not over the log, so every path between the two
Worlds must be excluded. Not done.

**Why.** Each trivial kernel is the deployed one with exactly the check the claim is about removed,
so each floor says the claim sees that check.

**CRITIQUE.** `checkMinting` is a second copy of `checkWith`'s sequence: when KERNEL adds a check,
`minting` lacks it and still refutes B2, so the copy drifts silently (the floor stays true; it just
stops being "deployed minus one"). B3's floor refutes only the package clause; a kernel that skipped
`judge` but kept the package slot fixed is not refuted by any floor here, so the third conjunct of
`Integrity.law` (the clause an author most cares about) carries no vacuity witness of its own.

**META-CRITIQUE.** I picked the package clause because its refutation needs no reasoning about
`ObjectHistory`; that is choosing the floor by cost. The honest remedy is the unjudged floor with a
lemma that `ObjectHistory` over a one-step audited log has exactly the judged step (a determinism
lemma KERNEL does not have), filed as owed.

**Status.** open; the law-chain floor owed.

## SPEC-8 C(ii)'s cancel arm and C(iii)'s stale arm are claims; C(ii) and C(iii) are inhabited at the Store's digest (2026-10-26)

**Decision.** `Consent.cancelOk` (a `cancel CALL` step ending `done ok` leaves follow at a World whose
`S.settle` of the call is `refused cancelled`), proved of `deployed` by `cancel_ok_settled`
(PROTOCOL-71) and refused of `hostWord` (`floor_consent_cancelOk`: the continuation parses as
`cancel` of the run's call, and at the genesis World follow does not settle it cancelled,
`run_cancel_state`). `Consent.staleFinal` (a call follow planned at `w₀` and settles `refused stale`
at a later World of its fold is admitted at no World the fold reaches, or the hash collides among
`behindPres`), proved by splitting the settlement: a recorded `stale` refusal is final by
`settle_final_never_admits`, follow's own `staleBehind` by `staleBehind_final`. The inhabited runs
are at `deployed storeDigest`: `Spec.storeDigest` is `Host.Keys.ofKey`'s `worldDigest`, which reads
no key, so it is the digest of every deployed Store and the runs are deployed runs, not one Store's.

**Alternatives.** Inhabit at `∃ d` (weaker: says nothing of the deployment's digest). Prove the
settle-phase step independent of `B` (it is, by inspection) so the run holds at every `d`: an
unfolding of `Command.step` at a concrete continuation, which is the elaboration bomb measured here
(two OOMs at 6 GB, one kernel deterministic timeout: a `show`/eta conversion between
`(deployed d).follow` and `Command.step`, and Prod eta over a concrete step, each made the kernel
evaluate `step`).

**Why.** The claims are the PROTOCOL theorems, stated over the System's fields, so a follower field
replaced by the Host's word is refused; the runs reach the premises of C(ii) and C(iii) at the
digest the binaries use.

`floor_consent_staleFinal` refuses `staleOnWord` (every call settled `refused stale`): the founder's
`issue 1000` as `Command.plan` plans it at the genesis World (`run_plan`), which the writer admits
there, with no collision among its pin inputs (`run_planned`; the genesis World's `CellsFit` from
`checkGenesis_ok` and `genesis_cellsFit`).

**CRITIQUE.** `cancelOk` is not inhabited: a deployed World holding a recorded cancel is a two-call run
(the call, then its cancel) not built. `inhabited_final` uses `expired`; a final `refused NAME`
(a recorded refusal) is not run.

**META-CRITIQUE.** The inhabited runs reuse the one founder and its rotate because every new deployed
run cost an OOM to shape; the lesson (state native facts over the System's own field at a fixed `d`,
generalize every concrete constant before the closing `exact`, never let a conversion meet a
concrete `step`) is in the continuation so the next run costs one build.

Two more runs at the deployed `Ctx` (any `d`: neither `handle` nor the kernel reads it):
`inhabited_shown` (G2: `Host.handle` defers the founder's `log` frame, its envelope under the
founder's root grant, `run_shown`) and `inhabited_value` (B2's non-trivial case: issue, account,
transfer 10, re-derived, the account holds 10, `run_value`).

**Status.** open; the cancel run and B3's law-judged run owed.

## SPEC-9 One claim, one proof module and one Sim module; five components become System fields (2026-10-26)

**Decision.** A claim stated after SPEC-8 lives in `Spec/Proofs/<Name>.lean` (the claim, its Prop
vocabulary, top theorem, floor, inhabited fact, lemmas) beside `Spec/Sim/<Name>.lean` (every non-Prop
def: its trivial system(s) and the inputs of its runs). Floor.lean's run inputs moved to
`Spec/Sim/Run.lean`, shared by every floor. `System` gains `rc` (the receipt check a law's foreign read
runs), `reopen` (the writer's open after a crash), `exchange` (the stdlib exchange package),
`bellAccept` and `ringAct` (the resident's bell check and its act on the rings); `deployed` fills each
with the definition the binaries run.

**Alternatives.** (a) Every claim in Claims.lean and every floor in Floor.lean (SPEC-2's layout): one
reading, but a 3000-line Floor and every lane editing two shared files. (b) The new components as claim
parameters (the drafts' shape): a parameter the system does not own cannot be refused by a trivial
system, and a reader may instantiate it with anything. (c) Trivial systems in `Spec/Trivial.lean`: they
read run inputs (a check that answers the run's call), which are tooling; C9 forbids a deployed
def-module importing a Sim module.

**Why.** Closure C3/C9 decide the split (non-Prop defs out of `Proofs`, run inputs are tooling); one
module per claim lets claims be drafted in parallel and read one at a time.

**CRITIQUE.** The trusted reading now spans a file per claim, and new trivial systems sit in `Sim`
modules beside run data, not in `Trivial.lean` with the first ones. `deployed` grew five more wirings
that only reading checks (SPEC-1's drift risk, five times).

**META-CRITIQUE.** The layout was chosen to let nine drafting lanes work without touching one file;
that is a property of this session's method, not of the spec. If the claims stop growing, fold the
claim statements back into one `Claims` reading.

**Status.** open.

## SPEC-10 §9 is `Foreign` over the `rc` field, under the named premise `HeadOf` (2026-10-26)

**Decision.** `foreign_receipt_sound` over `S.fold`/`S.admit`/`S.rc`; `HeadOf S cell wA` (the held
head's roots are those of the fold) is a named premise, undischargeable today (PROTOCOL E-3).
`deployed_program_reads` ties `(deployed d).rc` by `rfl` to the check `Host.Deployed.X`'s program
reads. Floor: `acceptingHead` (a check that shows the run's call committed for any cell and bytes) at
the genesis World and the empty log. Inhabited: the deployed check shows a committed receipt against
a head cell holding the roots of THE re-deriver's fold.

**Alternatives.** `rc` as a claim parameter; make `X`'s program read the field (the trivial system
would change what laws read; §9 does not need it).

**CRITIQUE.** The floor's cell is no head, so `HeadOf` holds vacuously there: the floor refutes the
lazy CHECK, not a lazy head. The inhabited head cell is synthetic, not one a head object's `post` made.

**META-CRITIQUE.** Deleting `HeadOf` (writer-signed step-indexed heads, §9) is the strengthening the
checker sees; until then the claim is a consequence under trust.

**Status.** open.

## SPEC-11 DURABILITY's writer half needs a completeness clause: `host_reopen_folds` alone admits the amnesiac open (2026-10-26)

**Decision.** `Durable.reopen (S : System Digest)`: an open that succeeds returns `S.fold`, from the
`Kept` base World, of EXACTLY the records `Log.recover` verifies past the base (completeness), whose
encoding is the bytes up to the open's position; the opened World is `Kept`. Floor: `amnesiac` (the
base's World at the base's position). Inhabited: a computed Store (genesis + one rotate record)
reopens to height 1.

**Found.** `host_reopen_folds`'s statement verbatim is met by the amnesiac open on every Store
(`amnesiac_reopenSound`, kept as the reason): zero records, an empty prefix. TOPLEVEL-SPEC §5.FLOOR's
"`o.records = rs.length` fails on a one-record segment" is false of that open.

**Alternatives.** The verbatim statement (refuted above); a crash-image form (Log-level premises on
the top claim); generic in `D` (`Kept` and `foldStep` are the deployed instance's).

**CRITIQUE.** "On disk" is defined by `Log.recover`, which the open itself runs: a recover that
stopped early would pass with its open. Fold, not audit: `Honest` is not carried across the crash and
nothing ties a record to what `admitBatch` staged; the acknowledged-reply half needs §11.4.

**META-CRITIQUE.** The floor refutes exactly the open the design's own form admitted; that is the
test of the added clause, not of D1.

**Status.** open; D1 over `Crash` images owed (§11.4).

## SPEC-12 C(i) signing is stated per signing DOMAIN, with a companion over every shape (2026-10-26)

**Decision.** `Consent.signs`: every message follow offers custody (`sign`/`signNext`/`signIncoming`)
that is `callMessage v` for some `v` is `callMessage u` for the `u` `plan` produced on follow's World
after the step (`f'.world`) from the command the continuation's argv parses to, the member's own
call, its Turn admitted there. `Consent.signShapes`: every offered message is a planned call, an
own-World envelope, a possession proof, an invitation, a head attestation or a cancel. Floor:
`relaySigner` (signs the Host's bytes once the continuation decodes and parses), refuted on a decoding
`sync` continuation with no `native_decide`.

**Alternatives.** By reply constructor (`sign` carries seven kinds of message); `signShapes` alone;
a floor on an undecodable continuation (escaped by a signer that checks decoding).

**CRITIQUE.** The argv and custody's key are continuation bytes: "planned from the continuation's
argv", not "the member's" (§11.2, named, not assumed). `start`'s `whoami` arm is outside `System`.

**META-CRITIQUE.** No floor exhibits a signer that plans on a World other than its own.

**Status.** open.

## SPEC-13 The grant cap is stated over the system's own step chain, both ledgers (2026-10-26)

**Decision.** `Integrity.grantCap`: from a canonical World whose grant ledgers are contiguous, along an
audited log and ANY chain of the system's own steps over it (`System.Steps`), the transfers (credit
lines) dispatched through a live grant sum to at most what its transfer (credit) ledger had left.
Floors: `capless` (transfer and credit without `spendVia`), one per ledger. Inhabited: one deployed
move of 10 through a cap-10 grant.

**Alternatives.** Keep `GrantStep` (names `World.step`/`Honest`, so no floor could swap `receive`); an
existential chain; the transfer ledger only.

**CRITIQUE.** A nested move is read through the kernel's walk of the call, so under a non-kernel
`receive` a nested move that walk refuses is not counted; the floors exercise only the root case.

**META-CRITIQUE.** `LedgerContiguous` is a separate premise (the design said `Kept` discharges it; it
does not, `honest_ledgerContiguous` does).

**Status.** open.

## SPEC-14 A2′ fork consistency is stated at the post comparison, with the refusal carrying its evidence (2026-10-26)

**Decision.** `ForkConsistent`: a frame that persists a page carrying another fold's self-head post
(from the same start) at a step the page walks has one history with that fold up to there (or a
collision among a length-pinned explicit list), or ends `refused forkedPost` WITH a post its own fold
passed at another chain. Floor: `postBlind` (the deployed follower with `forkedPost` replaced by ok),
on a computed run at `storeDigest`.

**Found.** "Never moves past a forked post" is false by design (the page is kept). A post naming a
step past the page's end is compared by nobody (cv 01a17ac1-5204), hence the premise
`wg.steps ≤ f'.world.steps`; a writer's refusal can print as `refused forkedPost` (cv 01a17ac1-5233).

**CRITIQUE.** Behind-position posts are the Host loop's (`behindOr`, no System field): the premise
`f.world.steps < wg.steps` stands for it. The `sync --to` arm is not stated.

**META-CRITIQUE.** The evidence disjunct is what the member saw, not what it can show a third party;
that needs signed heads.

**Status.** open.

## SPEC-15 THE BELL as two slices; the composite owed; "once per key" is false (2026-10-26)

**Decision.** `Bell.ringer` (over `bellAccept`): every `rings` upsert of a returning run of the package
the resident accepts answers a row the caller pinned waiting, same capture, signed by the state's
resident. `Bell.oneAsk` (over `ringAct`): every path of the resident's act asks at most once, about
the decided ring, right after the intent is kept; within one process two spent asks for one ring have
a freeing effect between. Floors: `laxBell` (accepts by layout, not guards), `askFirstResident`.

**Found.** At most one answer per ring KEY is false of the deployed Bell (retire, re-ring at the same
`notBefore`; cv 01a17ab4-17b1); the claim is per ring life.

**CRITIQUE.** (1) is against the caller's pinned row, not the World's; (2) is one process: the crash
between keep and ask is uncovered across a restart. The composite needs `RingLife` (§11.5).

**META-CRITIQUE.** The three run facts do not hash; the kernel blocks on the package decoder's
well-founded recursion. A structural decoder would make them `decide +kernel`.

**Status.** open; composite owed.

## SPEC-16 B2's exchange is `Integrity.exchange` over the `exchange` field; the one-party escrow is another claim (2026-10-26)

**Decision.** A signed fuse of an object of `S.exchange …` that `S.receive` derives and `S.admit` admits
from canonical cells and rows moves both legs (each offer row retracted and absent after), the two
offers are one pair whose legs match (`LegsMatch`: each party receives what its offer wants), and every
denomination's sum is unchanged (`escrow_fuse_admitted`). Floor: `lazyExchange` (the legs' judge
`escrowFairT` replaced by `true`, P8j), refuted by a deployed run that admits a fuse paying X 1 β where
X wants 7 β. Inhabited: a fair fuse under the deployed package.

**Alternatives.** Fold `escrow_invokes_one_payout` in as "once": it is LEDGER's one-party escrow
(world/escrow), another package (cv 01a17ad6-7245 for its own claim); a toy-Ctx floor.

**CRITIQUE.** Per Turn only: nothing of withdraw or of a take without a fuse. The id read-back premises
hold of every `Digest` and exist only because the claim is generic in `D`.

**META-CRITIQUE.** The floor varies one term; an exchange paying the wrong `payTo` or dropping the
peer's take is refused by the claim but not exhibited.

**Status.** open.

## SPEC-17 B3 over every history; its law-chain floor is the unjudged kernel; B3 and the cancel inhabited (2026-10-26)

**Decision.** B3 (`Integrity.law`, Claims) is restated in place: EVERY `ObjectHistory` between the two Worlds in whose judged steps a `NoRef` law is in force is a `Std.Chain (Std.Step [] t)` (was: SOME history). `top_integrity_law` (Deployed) keeps its proof (`object_history_chain` was already stated for every history); the new form implies the old one, so it is a strengthening, and the old existential statement is deleted. `floor_integrity_law` (Floor, the raw writer) refutes the new statement's package clause unchanged. Floor `floor_integrity_lawChain` (Spec/Proofs/Law.lean): `unjudged` (the deployed system over `Xu`, `Lang.program` with `judge := fun … => .ok ()`) admits the founder's write `n := 9` to a data object under `Std.boundedPackage {n} n 5`, re-derived from genesis; `bounded_spec` admits no step to `n = 9`. Inhabited: `inhabited_law` (the deployed kernel judges and admits `n := 3`: one judged step, state moved, law in force); `inhabited_cancelOk` (follow at the World holding the founder's recorded cancel ends `cancel CALL` `done ok`).

**Alternatives.** (1) Keep the existential and prove "a one-step audited log has exactly that judged step" (SPEC-2): unprovable — another call reaching the same World with a view lacking the law is excluded only by a collision over an unbounded preimage set, so the floor would carry a pigeonhole-true disjunct. (2) A log-indexed history: names the log, but a new inductive and a new totality proof for what the universal form already states. (3) A law that admits nothing as the floor's law: refutes, but cannot share the object with the inhabited run.

**Why.** The universal form is the stronger promise (however the object's past is decomposed into judged steps, the law admitted each), costs nothing for the deployed system, and its floor is the bad step's own history, so it needs no collision argument.

**CRITIQUE.** `unjudged` swaps seven fields (every one that reads the program), not one: the replaced component is the program's `judge`, inside `X`. The floor runs only the write receiver; a kernel that judged writes but skipped invokes is refused by this claim only via an invoke run, which no floor runs. The histories quantified over go World to World, so they include paths off the log: true of the deployed kernel, but the claim no longer says "this log's steps".

**META-CRITIQUE.** The existential form survived because its floor was never attempted; the restatement came from trying to write the floor, not from reading the claim. `NoRef` is still the claim's largest hole and this entry does not move it.

**Status.** open; `NoRef` removed by §11.6.

## SPEC-18 B1 authority confinement, per step, over every cell (2026-10-26)

**Decision.** `Integrity.authority`: every step of an audited log that changes a cell live at that
step's World is a Turn `S.receive` derived from the call its event decodes to, and `Authorized`
holds: objects (an owner/chain `write` or `law`, an authorized dispatched invoke), members (only its
own `rotate`, to the precommitted key, signed by it), grants (the issuer's retire, a holder's single
ledger append), accounts (a transfer or credit leg under the source/well owner's authority at the
dispatched actor), ROM never. The kernel lemma it needs (`effect_prov`, `node_effect`,
`changed_effect`: what each receiver of a walk wrote and on whose authority, generalising
InvokeTree's private `dispatched_effects`) is proved in `Spec/Proofs/AuthKernel.lean`, stated for
KERNEL to move down. Floor: `openKernel` (a `write` with no owner check), on a two-founder run where
founder 1 writes founder 0's object. Inhabited: the owner's write.

**Alternatives.** The design's endpoint form (implied by the per-step one, and needs a `foldSteps`); a
scope parameter (the first draft: objects, grants, ROM; now closed); chaining each nested actor to
the signer.

**CRITIQUE.** Authority is named at the DISPATCHED actor: for a nested receiver that is the calling
object, so "the signer exercised authority" holds only through the object's own invoke step, which
the claim does not compose. Births (create/issue/account/grant/enroll/install) are not changes of a
live cell: who may bear a cell is unclaimed. A Spec-side kernel lemma is a second home for a kernel
fact until KERNEL moves it.

**META-CRITIQUE.** One floor refutes only the object arm; the member, grant and account arms have no
run of their own (a kernel letting a member rotate another's key, or revoke a grant it did not issue).
The vacuity rule needs only the top claim refuted, and it is; the arms' floors are owed as teeth.

**Status.** open; the AuthKernel lemma is KERNEL's to move.

## SPEC-19 The apex is an observational contract, not ONE HISTORY ∧ INTEGRITY: CRIT-SPEC accepted, with what lands now and what is owed (2026-10-27)

An outside statement review (redregg/work/critiques/CRIT-SPEC.md, Codex, read at 4bb86ea, before
80791d0 landed B1 and A2′) found the apex's predicates admit countermodels to their own prose. Its
three required statements, verbatim, are adopted as THE apex this directory is building toward:

> For an honest writer and the declared platform assumptions, every observable execution of the
> deployed member, Store, and resident processes refines the intent-indexed durable contract,
> including the Bell's per-ring charge and answer limits across retries and crashes.

> Every accepted step implements an independently defined transition relation that confines
> authority, conserves value under the stated issuance rule, enforces delegation caps, and gives
> contextual programs and applicable laws their reference meaning within the declared resource budget.

> Every accepted member view or foreign receipt is justified by a history extending its explicitly
> trusted start, with prefix consistency or checkable equivocation evidence under the declared
> head-authority and comparison assumptions.

**Decision.** (1) The landed claims are COMPONENTS of those three, not the apex; README says so and
names, per statement, which components exist and which are owed. (2) `Shown.onlyFollowers` leaves the
top-level contract (its theorem stays, as a handler lemma: it constrains the `defer` arm only; a handle
that leaks through `reply`, or through `lookup` which no envelope guards, satisfies it). (3) Land now
the restatements that are compositions of existing lemmas: A1 per step from the member's OWN start
(each frame extends follow's World by an audited log, or adopts a pinned base of `me.world` from a World
holding nothing; `Start.genesis` tied to `me.world`) — this refutes the review's reset-to-genesis
follower; C(ii) over `f'.world` (the World follow keeps, so a destructive success is refused) and the
cancel arm naming the recorded cancel; B3's ObjectHistory over the system's own `receive`/`admit`
where the shape allows. (4) The review's B1 objection (endpoint form) does not apply to the landed
B1, which is per step over every cell (SPEC-18); its "births are unclaimed" stands as owed.

**Owed, with prices** (each a card, not a note):
* The deployment wiring (SPEC-1's gap, the central weakness: the System's fields are semantically
  independent; a binary wired to another function leaves every theorem intact). Remedy: the binaries'
  entry points take the System they run (`host serve`/`host follow` read `(deployed d).handle`/
  `.follow`, and `deployed`'s `follow` is built from `deployed`'s own `receive`/`admit`), so a field is
  the function called, and an execution relation over Store/Port effects ties replies to records.
  Price: one HOST+PROTOCOL change of the entry points (days) for the first half; §11.4's interpreter
  (a month) for the second.
* Statement 1's intent-indexed contract: the command's state inside follow with an explicit intent id
  (§11.2/§11.3: deletes `keyFaithful`, ties `okCommitted`'s call to argv, makes C(v) a theorem); the
  durable trace (acknowledgment after persistence, §11.4); the Bell end-to-end over one ring identity
  (RingLife, §11.5: at most one charged ask per ring and one accepted answer across restarts; "once per
  key" is false today, cv 01a17ab4-17b1). Price: §11's quarter.
* Statement 2's independently defined transition relation: a relation over observations and authority
  effects (NOT a second executable kernel; the review is right that SPEC-1's "a model is a twin"
  conflated a specification with a competing implementation): births' authority, the issuance rule
  behind B2's floor-sum exception, metering adequacy for the contextual language, the `NoRef` lift.
  Price: weeks per clause; the authority and value clauses compose from B1/B2/grant-cap today.
* Statement 3's trust cases: retained audited views with prefix consistency across unequal positions,
  passed anchors and forgotten positions; for receipts, the source of validity chosen explicitly.

**Found (the review's, recorded as ours).** TOPLEVEL-SPEC §9's proposed discharge of `HeadOf` ("A's
writer signs at most one head per step count") is WRONG: a writer can sign exactly one fabricated head
per step, satisfying it, and that head need belong to no lawful fold; a signature is attributable
endorsement, not the endorsed proposition. The foreign-head contract must choose its validity source
— re-execution, an authenticated checkpoint trusted for validity, or an authority assumed to certify
only valid extensions — and the authority must be authenticated independently of the object checked
(`certifiesWorld`'s reliance on prior trust in the pinned bytes is the right shape; `Foreign.check`
reads roots from the head object and calls no certificate verifier).

**CRITIQUE.** Adopting statements no theorem yet proves risks the reverse of the honest-label sin: a
grand apex that every landing can claim to "contribute to". The guard is that README lists, per
statement, the exact components proved and the exact gaps, and a gap leaves only by a theorem.

**META-CRITIQUE.** I accept nearly all of it because nearly all of it is right; the part I resist is
none, and that is itself worth noting: the floor method had become the thing being optimized (one
refuted mutant per claim) while the claims' quantifiers went unread. The review read the quantifiers.

**Status.** open; the compositions in (3) are in flight.

## SPEC-20 Three more System fields — `receiptCheck`, `keep`, `escrow` — and the claims over them (2026-10-27)

**Decision.** `receiptCheck` (deployed `Receipt.check Host.Deployed.X.env`) carries §7's `ReceiptTruth`:
on a World folded from genesis, a receipt checked against that World's own head is its journal entry,
its recorded refusal, or the absence of both, up to a premise-fixed collision list; floor: a check that
believes the receipt's stated answer. `keep` (deployed `Hosting.Resident.keepOps`; the resume is built
from it, as in the code) carries D3 `Durable.resident`; floor: the in-place keep. `escrow` (deployed
`Ledger.Escrow.escrow`) carries the one-party `Integrity.escrow` (at most one payout along any history
of one escrow object); floor: no law on its invokes and two once keys, a deployed run whose
ObjectHistory is built from the computed steps (not an existential). D2 `Durable.follower` and A1′
`Agree.pageAbsorbs` and A2′'s `sync --to` arm need no field.

**Alternatives.** The components as claim parameters (refused by SPEC-9's reasoning: a parameter the
system does not own cannot be refused by a trivial system).

**CRITIQUE.** No member command runs `Receipt.check` on a receipt of its own World today (settle builds
the receipt from its own World and reads it; the callers are `Foreign.check` and the rows harness), so
`ReceiptTruth` is about the deployed function, not about a reply a member sees; a `verify RECEIPT`
command would close it. A1′'s page is a PREMISE (the pager over durable records is IO, tied to
`admitBatch` nowhere). D2's "appended before sent" is unstatable while the follow loop is IO.

**META-CRITIQUE.** Each new field widens SPEC-19's wiring gap by one more function only reading checks.

**Status.** open.
