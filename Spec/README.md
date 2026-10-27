# Spec — what nanodregg is for, as theorems

The top of the tree. Each claim below is a `Prop` over `System` (`Spec/System.lean`: the deployed
entry points as fields). It has a top theorem `top_* : Claim (deployed d)`, a floor
`floor_* : ¬ Claim trivial` refuting a lazy system, and a deployed run that reaches it. Only these
claims owe a vacuity argument; a lemma under a top theorem means what the claim says it means
(TOPLEVEL-SPEC §1.3). Design: `redregg/work/promo/TOPLEVEL-SPEC.md`; decisions: `decisions/spec.md`.

**The trusted reading** is `System.lean` + `Trivial.lean` + `Proofs/Claims.lean` + `Proofs/Floor.lean`'s floor
statements, and for each claim after SPEC-8 (SPEC-9) its claim definition and floor statement in
`Proofs/<Name>.lean` with its trivial system in `Sim/<Name>.lean`. Everything else (`Bridge`, `Member`,
`Deployed`, the lemmas and run facts in each `Proofs/<Name>.lean`, the run inputs in `Sim/`) is proofs and
tooling: checked, not read.

## The claims

| § | claim | one sentence | top theorem | floor (the system it refuses) |
|---|---|---|---|---|
| 2 A1 | `OneHistory.member` | whatever frames follow is fed, the member's World is an audited fold from a start it consented to | `top_oneHistory_member` (under `keyFaithful`; `Proofs/Member.lean`) | `floor_oneHistory_member`: the follower that takes the World it is told |
| 2 A2 | `OneHistory.pair` | two folds from one World that agree on step count and chain are one World, up to a collision among their link inputs | `top_oneHistory_pair` | `floor_oneHistory_pair`: the kernel whose chain does not move |
| 3 B2 | `Integrity.value` | along any fold, every denomination's balance sum is unchanged, and its floor sum unless the log created its well | `top_integrity_value` | `floor_integrity_value`: the kernel that admits without `checkValue` |
| 3 B1 | `Integrity.authority` (`Proofs/Auth.lean`) | along an audited log every step that changes a live cell is a Turn derived from a signed call entitled to that change (owner or chain for objects, its own precommitted rotate for a member, issuer retire or holder spend for grants, an owner-authorized transfer or credit leg for accounts, never for ROM) | `top_integrity_authority` | `floor_integrity_authority`: the kernel whose `write` checks no owner |
| 3 B3 | `Integrity.law` | along an audited log an object's package never changes, and EVERY history of it in which a `NoRef` law is in force is a chain the law's reference meaning admits | `top_integrity_law` | `floor_integrity_law`: the receiver whose `write` reaches the package slot; `floor_integrity_lawChain` (`Proofs/Law.lean`): the unjudged kernel |
| 4 C(ii) | `Consent.okCommitted` | a command that ends `done ok` at the settle phase means follow's own World journals the call | `top_consent_okCommitted` | `floor_consent_okCommitted`: the follower that says ok on the Host's word |
| 4 C(iii) | `Consent.final` | a settlement `expired`, or `refused` other than `stale`, is never contradicted on any extension | `top_consent_final` | `floor_consent_final`: the settlement that is always final |
| 4 C(ii) | `Consent.cancelOk` | a `cancel CALL` step that ends `done ok` leaves follow at a World that settles the call `refused cancelled` | `top_consent_cancelOk` | `floor_consent_cancelOk`: the follower that says ok on the writer's word |
| 4 C(iii) | `Consent.staleFinal` | a planned call follow settles `refused stale` is admitted on no extension, up to a collision among its pin inputs | `top_consent_staleFinal` | `floor_consent_staleFinal`: the settlement that says stale on its own word |
| 2 A2′ | `ForkConsistent` (`Proofs/Fork.lean`) | a frame that absorbs a page carrying another fold's self-head post at a step the page walks has one history with that fold up to there (up to a collision among a listed set), or ends `refused forkedPost` with a post its own fold passed at another chain | `top_forkConsistent` | `floor_forkConsistent`: the post-blind follower (the `forkedPost` verdict replaced by ok; at `storeDigest`) |
| 3 B2 | `Integrity.grantCap` (`Proofs/Cap.lean`) | along an audited log, the transfers (credit lines) sent through a live grant sum to at most what its transfer (credit) ledger had left | `top_integrity_grantCap` | `floor_integrity_grantCap` / `_credit`: the capless kernel, whose transfer and credit do not spend the grant's ledger |
| 3 B2 | `Integrity.exchange` (`Proofs/Exchange.lean`) | a fuse the kernel admits pays each party what its offer wants: both legs moved with their rows retracted, the legs matching, value conserved | `top_integrity_exchange` | `floor_integrity_exchange`: the exchange whose judge ignores the legs (`lazyExchange`, P8j) |
| 4 C(i) | `Consent.signs` (`Proofs/Sign.lean`) | every call-domain message follow offers custody is `callMessage u` for the `u` `plan` produced on follow's World from the continuation's command, the member's own call, admitted there | `top_consent_signs` | `floor_consent_signs`: the relay signer that has custody sign the Host's bytes |
| 4 C(i) | `Consent.signShapes` (`Proofs/Sign.lean`) | every message follow offers custody is a planned call, an own-World envelope, a possession proof, an invitation, a head attestation or a cancel | `top_consent_signShapes` | `floor_consent_signShapes`: the relay signer |
| 5 D1 | `Durable.reopen` (`Proofs/Durable.lean`) | an open that succeeds returns the fold, from the `Kept` base World, of exactly the records `Log.recover` verifies past the base (their encoding is the bytes up to the open's position), and that World is `Kept` | `top_durable_reopen` | `floor_durable_reopen`: the writer whose reopen returns the base's World at the base's position (`amnesiac`) |
| 6 (1) | `Bell.ringer` (`Proofs/Bell.lean`) | for the package the resident accepts, every `rings` upsert of a returning run answers a row the caller pinned waiting, with the same capture, signed by the state's resident | `top_bell_ringer` | `floor_bell_ringer`: `laxBell`, which accepts the bell by layout not guards (its unguarded Bell admits a second answer) |
| 6 (2) | `Bell.oneAsk` (`Proofs/Bell.lean`) | every path of the resident's act asks at most once, about the decided ring, right after the intent is kept; within one process two spent asks for one ring have a freeing effect between | `top_bell_oneAsk` | `floor_bell_oneAsk`: `askFirstResident`, which asks before keeping the intent |
| 8 G2 | `Shown.onlyFollowers` | the writer defers a frame (answers with a page) only past an `Envelope.check` on its World | `top_shown` | `floor_shown`: the host that serves every frame |
| 9 | `Foreign` (`Proofs/Foreign.lean`) | a receipt the system's check shows committed against a head holding a fold's roots names a call admitted in that fold, under `HeadOf`, up to a collision among the receipt's listed inputs | `top_foreign` | `floor_foreign`: the receipt check that accepts any head |

**The apex** is `OneHistory.member ∧ Integrity.*`: the member's World is audited (A1) and audited
means lawful (B2, B3). Neither half excludes the other's trivial system: a kernel that admits
everything makes every log `Decided`, which A1 cannot see and B2/B3 refuse.

## Premises (each a parameter of the claim, named; deleting one is a strengthening)

* **`keyFaithful`** (A1): every continuation that parses as `adopt INVITE KEY` names the sponsor key
  the member trusts. Under an arbitrary relay A1 is FALSE today: a forged continuation makes a fresh
  member adopt any base the forger pinned (SPEC-4). Deleted by keeping the command's state inside
  follow (TOPLEVEL-SPEC §11.2).
* **`NoRef`** (B3): the chain lift exists for laws without holes only (TOPLEVEL-SPEC §11.6).
* **`HeadOf`** (§9): the held head's roots are those of a fold of A from A's genesis. Undischargeable
  today (PROTOCOL E-3: heads are posted by grantees, unsigned by A's writer). Deleted by writer-signed
  step-indexed heads (TOPLEVEL-SPEC §9).
* **The post's step inside the walk** (A2′): `f.world.steps < wg.steps ≤ f'.world.steps`. Below: behind
  posts are compared by the Host loop (`behindOr`), not a System field. Above: a post past the page's
  end is compared by nobody today (cv 01a17ac1-5204).
* **The continuation's argv** (C(i)): the claim says "planned from the continuation's command"; that it
  is the MEMBER's command is §11.2 (as `keyFaithful`).
* **`LedgerContiguous`** (grant cap): true of every World a follower reaches (`honest_ledgerContiguous`).
* **Canonical tries** (B2: `w.Canon`; B3: `CellsCanon`; C(iii): `RefusalsCanon`, `JournalCanon`): true of
  every World a Store opens to (`Kept`), carried as premises because the claims are generic in `D`.

B2's floor starts at the genesis World and ends at a World no deployed fold reaches, reached by the
minting kernel's fold (SPEC-7). B3's package clause is refuted by the raw writer, its law-chain clause by the unjudged kernel
(SPEC-17: the chain clause is over EVERY history, the existential form had no floor).

## Inhabited

At `deployed storeDigest` (the digest every deployed Store pins by; it does not depend on the Store's
key): `inhabited_okCommitted` (follow, holding the World THE re-deriver reaches on the run's log,
ends the rotate's settle phase `done ok`: C(ii)'s premise) and `inhabited_final` (on that World
follow settles `expired` a call the writer would have admitted at genesis: C(iii)'s premise, by a
call that was not final before), `inhabited_shown` (the writer defers the founder's `log` frame under
its root grant's envelope at the genesis World: G2's premise) and `inhabited_value` (the founder
issues a well, opens an account and transfers 10 into it; THE re-deriver accepts the three calls and
the account holds 10: B2's non-trivial case, value moved).

`deployed_run` / `inhabited_audited` (`Floor.lean`): at the deployed `Ctx`, a genesis World with one
founder and the founder's signed `rotate`, re-derived by THE re-deriver, reaches height 1 — a
`native_decide` fact about a computed run (SPEC-5). It inhabits A1/A2/B2/B3's premise (an audited log
with a Turn); it does not move value or run a law, so the non-trivial cases of B2 and B3 are not yet
reached by a deployed run here: B2's is by `inhabited_value`, B3's (a law judging a step) by
`inhabited_law`, a cancel that ends `ok` by `inhabited_cancelOk` (`Proofs/Law.lean`).

Since SPEC-9 each new claim is inhabited in its own module: `inhabited_forkConsistent` (the deployed
follower refuses a forked post, every premise met), `inhabited_integrity_grantCap` (a deployed move of
10 through a cap-10 grant), `inhabited_exchange` (a fair fuse under the deployed package),
`inhabited_signs` (the rotate's `signNext` of its planned call), `inhabited_durable_reopen` (a Store of
genesis + one record reopens to height 1), `inhabited_bell_ringer`, `inhabited_bell_oneAsk`,
`inhabited_foreign` (the deployed check shows a committed receipt against a head of the run's fold).

## Not yet claims (TOPLEVEL-SPEC sections, and why)

* B1's member, grant and account arms have no floor run of their own (the object arm's refutes the claim).
* The one-party escrow's "at most one payout" (`escrow_invokes_one_payout`, cv 01a17ad6-7245).
* A2′'s `sync --to STEPS:CHAIN` arm.
* C(v) at most once per intent (§4): Rust today; a theorem when the attempt is follow's state (§11.3).
* DURABILITY D1 over `Crash` images with acknowledged replies, D2 the follower, D3 the resident volume
  (§5, §11.4); THE BELL's composite (`RingLife`, §6, §11.5); "once per ring key" is false today
  (cv 01a17ab4-17b1).
