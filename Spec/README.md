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
| 2 A1 | `OneHistory.member` | per frame, follow's World is an audited extension of the one it held, or an adoption, only from a World that holds nothing, of a base the trusted sponsor pinned for the member's own World (certificate checked); along a run from the member's own start every World is `Kept` (implies the old endpoint form: `OneHistory.member_audited`) | `top_oneHistory_member` (under `keyFaithful`; `Proofs/Member.lean`) | `floor_oneHistory_member`: the follower that takes the World it is told; `floor_oneHistory_reset`: the follower that resets to a fixed genesis |
| 2 A2 | `OneHistory.pair` | two folds from one World that agree on step count and chain are one World, up to a collision among their link inputs | `top_oneHistory_pair` | `floor_oneHistory_pair`: the kernel whose chain does not move |
| 3 B2 | `Integrity.value` | along any fold, every denomination's balance sum is unchanged, and its floor sum unless the log created its well | `top_integrity_value` | `floor_integrity_value`: the kernel that admits without `checkValue` |
| 3 B1 | `Integrity.authority` (`Proofs/Auth.lean`) | along an audited log every step that changes a live cell is a Turn derived from a signed call entitled to that change (owner or chain for objects, its own precommitted rotate for a member, issuer retire or holder spend for grants, an owner-authorized transfer or credit leg for accounts, never for ROM) | `top_integrity_authority` | `floor_integrity_authority`: the kernel whose `write` checks no owner |
| 3 B3 | `Integrity.law` | along an audited log an object's package never changes, and EVERY history of it in which a `NoRef` law is in force is a chain the law's reference meaning admits | `top_integrity_law` | `floor_integrity_law`: the receiver whose `write` reaches the package slot; `floor_integrity_lawChain` (`Proofs/Law.lean`): the unjudged kernel |
| 4 C(ii) | `Consent.okCommitted` | a command that ends `done ok` at the settle phase means the World follow KEEPS journals the call (the call↔argv tie is owed, §11.2) | `top_consent_okCommitted` | `floor_consent_okCommitted`: the follower that says ok on the Host's word; `floor_consent_okCommitted_kept`: the forgetful follower (ok, World erased) |
| 4 C(iii) | `Consent.final` | a settlement `expired`, or `refused` other than `stale`, is never contradicted on any extension | `top_consent_final` | `floor_consent_final`: the settlement that is always final |
| 4 C(ii) | `Consent.cancelOk` | a `cancel CALL` step that ends `done ok` leaves follow at a World that settles the call `refused cancelled` AND holds its record (no journal entry; a recorded refusal with the cancel's code) | `top_consent_cancelOk` | `floor_consent_cancelOk`: the follower that says ok on the writer's word; `floor_consent_cancelOk_record`: that follower paired with a settle that always says cancelled |
| 4 C(iii) | `Consent.staleFinal` | a planned call follow settles `refused stale` is admitted on no extension, up to a collision among its pin inputs | `top_consent_staleFinal` | `floor_consent_staleFinal`: the settlement that says stale on its own word |
| 2 A2′ | `HeadsCompared` (`Proofs/Fork.lean`) | a frame that absorbs a page carrying another fold's self-head post (read from the step that made it) past follow's position has one history with that fold up to there (up to a collision among a listed set), or ends `refused forkedPost` with a post its own fold passed at another chain, or `refused postBeyondPage` with a post naming a step past its own position. Prefix agreement on comparison, not fork consistency (PROTOCOL-82) | `top_headsCompared` | `floor_headsCompared`: the post-blind follower (the `forkedPost` verdict replaced by ok; at `storeDigest`) |
| 2 A2′ | `HeadsCompared.sync` (`Proofs/Fork.lean`) | a `sync --to STEPS:CHAIN` frame that moves follow's World to the stated head or past it holds the other fold's log up to there, up to a collision among the two folds' listed link inputs | `top_headsCompared_sync` | `floor_headsCompared_sync`: the anchor-blind follower (every `sync --to` read as `sync`) |
| 2 A1′ | `Agree.pageAbsorbs` (`Proofs/Agree.lean`) | the writer's page of what a batch staged, handed to follow at its log phase, moves follow to the World the writer keeps | `top_agree_pageAbsorbs` | `floor_agree_pageAbsorbs`: the deaf follower, which takes no page |
| 3 B2 | `Integrity.escrow` (`Proofs/Escrow.lean`) | along any history of one escrow object the kernel admits, at most one returned call is a payout | `top_integrity_escrow` | `floor_integrity_escrow`: the escrow with no law on its invokes and two once keys (`esLazy`) |
| 3 B2 | `Integrity.grantCap` (`Proofs/Cap.lean`) | along an audited log, the transfers (credit lines) sent through a live grant sum to at most what its transfer (credit) ledger had left | `top_integrity_grantCap` | `floor_integrity_grantCap` / `_credit`: the capless kernel, whose transfer and credit do not spend the grant's ledger |
| 3 B2 | `Integrity.exchange` (`Proofs/Exchange.lean`) | a fuse the kernel admits pays each party what its offer wants: both legs moved with their rows retracted, the legs matching, value conserved | `top_integrity_exchange` | `floor_integrity_exchange`: the exchange whose judge ignores the legs (`lazyExchange`, P8j) |
| 4 C(i) | `Consent.signs` (`Proofs/Sign.lean`) | every call-domain message follow offers custody is `callMessage u` for the `u` `plan` produced on follow's World from the continuation's command, the member's own call, admitted there | `top_consent_signs` | `floor_consent_signs`: the relay signer that has custody sign the Host's bytes |
| 4 C(i) | `Consent.signShapes` (`Proofs/Sign.lean`) | every message follow offers custody is a planned call, an own-World envelope, a possession proof, an invitation, a head attestation or a cancel | `top_consent_signShapes` | `floor_consent_signShapes`: the relay signer |
| 5 D1 | `Durable.reopen` (`Proofs/Durable.lean`) | an open that succeeds returns the fold, from the `Kept` base World, of exactly the records `Log.recover` verifies past the base (their encoding is the bytes up to the open's position), and that World is `Kept` | `top_durable_reopen` | `floor_durable_reopen`: the writer whose reopen returns the base's World at the base's position (`amnesiac`) |
| 5 D2 | `Durable.follower` (`Proofs/Durable2.lean`) | every step of follow's machine that persists steps persists a rooted run of the system's kernel from follow's World to its next | `top_durable_follower` | `floor_durable_follower`: the follower that takes the World it is told |
| 5 D3 | `Durable.resident` (`Proofs/Durable2.lean`) | a keep of the kept answer is atomic across a crash after any prefix of its steps, durable once complete, and the restart's resume reads back what the start read | `top_durable_resident` | `floor_durable_resident`: the resident that writes the kept name in place |
| 7 | `ReceiptTruth` (`Proofs/Receipt.lean`) | a receipt the check answers against a folded World's own head is its journal entry, its recorded refusal, or the absence of both, up to a collision among the receipt's listed inputs | `top_receiptTruth` | `floor_receiptTruth`: the check that believes the receipt's stated answer |
| 6 (1) | `Bell.ringer` (`Proofs/Bell.lean`) | for the package the resident accepts, every `rings` upsert of a returning run answers a row the caller pinned waiting, with the same capture, signed by the state's resident | `top_bell_ringer` | `floor_bell_ringer`: `laxBell`, which accepts the bell by layout not guards (its unguarded Bell admits a second answer) |
| 6 (2) | `Bell.oneAsk` (`Proofs/Bell.lean`) | every path of the resident's act asks at most once, about the decided ring, right after the intent is kept; within one process two spent asks for one ring have a freeing effect between | `top_bell_oneAsk` | `floor_bell_oneAsk`: `askFirstResident`, which asks before keeping the intent |
| 9 | `Foreign` (`Proofs/Foreign.lean`) | a receipt the system's check shows committed against a head holding a fold's roots names a call admitted in that fold, under `HeadOf`, up to a collision among the receipt's listed inputs | `top_foreign` | `floor_foreign`: the receipt check that accepts any head |

**Handler lemma (not a top-level claim, SPEC-19):** `Shown.onlyFollowers` (G2): the writer defers a
frame only past `Envelope.check` (a live follow grant chain, the member's current key, a verifying
signature): `top_shown`, refused by `openHost`. It constrains the `defer` arm only; a `reply` or a
`lookup` (which no envelope guards) is not covered, so it is no confidentiality theorem.

**The apex (SPEC-19, adopted from the outside review CRIT-SPEC, verbatim)** is three statements; the
claims above are their components, and what is owed is listed beside each:
1. *For an honest writer and the declared platform assumptions, every observable execution of the
   deployed member, Store, and resident processes refines the intent-indexed durable contract,
   including the Bell's per-ring charge and answer limits across retries and crashes.* Components:
   C(i)–C(iii), D1–D3, A1′, the Bell slices. Owed: the command state and an intent id inside follow
   (§11.2/§11.3: deletes `keyFaithful`, ties `okCommitted`'s call to argv, C(v)); the durable trace
   (acknowledgment after persistence, §11.4); the Bell over one ring identity (§11.5); the deployment
   wiring (the binaries run the System's own fields; today the fields are independent).
2. *Every accepted step implements an independently defined transition relation that confines
   authority, conserves value under the stated issuance rule, enforces delegation caps, and gives
   contextual programs and applicable laws their reference meaning within the declared resource
   budget.* Components: B1 (every cell, per step), B2 value, grant cap, exchange, escrow, B3 (`NoRef`).
   Owed: births' authority, the issuance rule, metering adequacy, the `NoRef` lift, B3's history bound
   to the log and to the system's own `receive`.
3. *Every accepted member view or foreign receipt is justified by a history extending its explicitly
   trusted start, with prefix consistency or checkable equivocation evidence under the declared
   head-authority and comparison assumptions.* (A2′ is prefix agreement for members who compare stated
   heads; it is not SUNDR's fork consistency, which no claim here states: a call names no prefix, so a
   writer can admit one call on two branches; PROTOCOL-82.) Components: A1 (under `keyFaithful`), A2, A2′ (posts and
   `sync --to`), receipts (§7), §9 under `HeadOf`. Owed: unequal positions, passed anchors and forgotten
   positions; §9's validity source chosen explicitly (signed heads give accountability, not validity).


## Premises (each a parameter of the claim, named; deleting one is a strengthening)

* **`keyFaithful`** (A1): every continuation that parses as `adopt INVITE KEY` names the sponsor key
  the member trusts. Under an arbitrary relay A1 is FALSE today: a forged continuation makes a fresh
  member adopt any base the forger pinned (SPEC-4). Deleted by keeping the command's state inside
  follow (TOPLEVEL-SPEC §11.2).
* **`NoRef`** (B3): the chain lift exists for laws that name no closure package: `Lang.NoRef t`
  (`Lang/Proofs/Receiver.lean`) says no `ref` occurs anywhere in `t`, so relocation is the identity on it
  (TOPLEVEL-SPEC §11.6). It is not "no holes": a hole is `NoRef` when its substitution's terms are, so
  contextual laws are inside the fragment, and the chain clause does not by itself say a hole-bearing
  law was judged at its contextual reference meaning under the pins it depended on (CRIT-SPEC).
* **`HeadOf`** (§9): the held head's roots are those of a fold of A from A's genesis. Undischargeable
  today (PROTOCOL E-3: heads are posted by grantees, unsigned by A's writer). Deleted by writer-signed
  step-indexed heads (TOPLEVEL-SPEC §9).
* **The post past follow's position** (A2′): `f.world.steps < wg.steps`. Behind it, posts are compared
  by the Host loop (`behindOr`), not a System field. The old upper premise (`wg.steps ≤ f'.world.steps`)
  is deleted: a post's position is inside its page, and a post past its position is `postBeyondPage`
  (PROTOCOL-83).
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

Since SPEC-9 each new claim is inhabited in its own module: `inhabited_headsCompared` (the deployed
follower refuses a forked post, every premise met), `inhabited_integrity_grantCap` (a deployed move of
10 through a cap-10 grant), `inhabited_exchange` (a fair fuse under the deployed package),
`inhabited_signs` (the rotate's `signNext` of its planned call), `inhabited_durable_reopen` (a Store of
genesis + one record reopens to height 1), `inhabited_bell_ringer`, `inhabited_bell_oneAsk`,
`inhabited_foreign` (the deployed check shows a committed receipt against a head of the run's fold).

## Not yet claims (TOPLEVEL-SPEC sections, and why)

* B1's member, grant and account arms have no floor run of their own (the object arm's refutes the claim).
* C(v) at most once per intent (§4): Rust today; a theorem when the attempt is follow's state (§11.3).
* DURABILITY D1 over `Crash` images with acknowledged replies (§5, §11.4); D2's "appended before sent"
  (the follow loop is IO, not an interpreter); THE BELL's composite (`RingLife`, §6, §11.5); "once per ring key" is false today
  (cv 01a17ab4-17b1).
