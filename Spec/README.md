# Spec — what nanodregg is for, as theorems

The top of the tree. Each claim below is a `Prop` over `System` (`Spec/System.lean`: the deployed
entry points as fields). It has a top theorem `top_* : Claim (deployed d)`, a floor
`floor_* : ¬ Claim trivial` refuting a lazy system, and a deployed run that reaches it. Only these
claims owe a vacuity argument; a lemma under a top theorem means what the claim says it means
(TOPLEVEL-SPEC §1.3). Design: `redregg/work/promo/TOPLEVEL-SPEC.md`; decisions: `decisions/spec.md`.

**The trusted reading** is `System.lean` + `Trivial.lean` + `Proofs/Claims.lean` + `Proofs/Floor.lean` (≈ 620 lines).
`Proofs/Bridge.lean`, `Proofs/Member.lean` and `Proofs/Deployed.lean` are proofs: checked, not read.

## The claims

| § | claim | one sentence | top theorem | floor (the system it refuses) |
|---|---|---|---|---|
| 2 A1 | `OneHistory.member` | whatever frames follow is fed, the member's World is an audited fold from a start it consented to | `top_oneHistory_member` (under `keyFaithful`; `Proofs/Member.lean`) | `floor_oneHistory_member`: the follower that takes the World it is told |
| 2 A2 | `OneHistory.pair` | two folds from one World that agree on step count and chain are one World, up to a collision among their link inputs | `top_oneHistory_pair` | `floor_oneHistory_pair`: the kernel whose chain does not move |
| 3 B2 | `Integrity.value` | along any fold, every denomination's balance sum is unchanged, and its floor sum unless the log created its well | `top_integrity_value` | `floor_integrity_value`: the kernel that admits without `checkValue` |
| 3 B3 | `Integrity.law` | along an audited log an object's package never changes and its states are a chain its `NoRef` laws' reference meaning admits | `top_integrity_law` | `floor_integrity_law`: the receiver whose `write` reaches the package slot |
| 4 C(ii) | `Consent.okCommitted` | a command that ends `done ok` at the settle phase means follow's own World journals the call | `top_consent_okCommitted` | `floor_consent_okCommitted`: the follower that says ok on the Host's word |
| 4 C(iii) | `Consent.final` | a settlement `expired`, or `refused` other than `stale`, is never contradicted on any extension | `top_consent_final` | `floor_consent_final`: the settlement that is always final |
| 8 G2 | `Shown.onlyFollowers` | the writer defers a frame (answers with a page) only past an `Envelope.check` on its World | `top_shown` | `floor_shown`: the host that serves every frame |

**The apex** is `OneHistory.member ∧ Integrity.*`: the member's World is audited (A1) and audited
means lawful (B2, B3). Neither half excludes the other's trivial system: a kernel that admits
everything makes every log `Decided`, which A1 cannot see and B2/B3 refuse.

## Premises (each a parameter of the claim, named; deleting one is a strengthening)

* **`keyFaithful`** (A1): every continuation that parses as `adopt INVITE KEY` names the sponsor key
  the member trusts. Under an arbitrary relay A1 is FALSE today: a forged continuation makes a fresh
  member adopt any base the forger pinned (SPEC-4). Deleted by keeping the command's state inside
  follow (TOPLEVEL-SPEC §11.2).
* **`NoRef`** (B3): the chain lift exists for laws without holes only (TOPLEVEL-SPEC §11.6).
* **Canonical tries** (B2: `w.Canon`; B3: `CellsCanon`; C(iii): `RefusalsCanon`, `JournalCanon`): true of
  every World a Store opens to (`Kept`), carried as premises because the claims are generic in `D`.

B2's floor starts at the genesis World and ends at a World no deployed fold reaches, reached by the
minting kernel's fold (SPEC-7). B3's floor refutes the package clause; the law-chain clause has no
floor of its own yet (SPEC-7).

## Inhabited

`deployed_run` / `inhabited_audited` (`Floor.lean`): at the deployed `Ctx`, a genesis World with one
founder and the founder's signed `rotate`, re-derived by THE re-deriver, reaches height 1 — a
`native_decide` fact about a computed run (SPEC-5). It inhabits A1/A2/B2/B3's premise (an audited log
with a Turn); it does not move value or run a law, so the non-trivial cases of B2 and B3 are not yet
reached by a deployed run; nor are a deferred envelope (G2), a settled command (C(ii)) or a final
settlement (C(iii)).

## Not yet claims (TOPLEVEL-SPEC sections, and why)

* B1 authority (§3.1): the `Authorized` inductive over every cell kind; the statement is the work.
* B2's grant cap and escrow (§3.2): exist as theorems (`grant_moves_le_cap`, `escrow_invokes_one_payout`).
* A2′ fork consistency (§2.3): landed as an act (PROTOCOL-74/75); the claim over `Command.step` is new.
* C(i) signing, C(v) at most once, the cancel arm of C(ii), `refused stale` final (§4).
* DURABILITY (§5), THE BELL (§6), RECEIPTS BETWEEN WORLDS (§9): their models (`Crash`, `RingLife`)
  or the writer's signed heads are §11's items.
