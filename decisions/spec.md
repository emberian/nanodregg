# decisions/spec.md — the top-level spec (`Spec/`)

Owner: SPEC (a ROOT lane; `Spec/` has no OWNERS row, so it is ROOT's and lands as `root:`). Design:
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
