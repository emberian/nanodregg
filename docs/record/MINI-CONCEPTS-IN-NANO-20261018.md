> record copy of redregg/work/MINI-CONCEPTS-IN-NANO-20261018.md, 2026-10-18; the lane logs stay in redregg

# Mini's coordination concepts in nanodregg: intents, co-receipts, joint turns, hyperedges, guarded holes (2026-10-18)

Ember asked: "does nanodregg preserve the intent-centric design? the co-receipts? joint turns? the hyperedge
consensus stuff? 'guarded holes'/contexts?" ROOT had measured that none of co-receipt, joint turn, hyperedge or
guarded hole appears by name in nanodregg's CHARTER, decisions or Lean. The one trace ROOT found is the charter's
"guard-from-intent staleness refusal" (CHARTER.md:95).

**Sources.** Mini at its spec commit `2c27b08b` (M:, via `git show`). nanodregg `main` at `921d2d0` on hbox (N:,
`/tank/dregg-build/nanodregg/main`, read-only). breadstuffs (B:, `~/dev/breadstuffs`), where several of these ideas
started. The scope table in `NANO-VS-MINI-20261017.md` §2 is cited, not redone.
**Labels.** [read] means I opened the pointer. [inferred] means a judgment or estimate of mine that nobody measured.
No build was run. Prices are in premises and flag days, as the brief asked.

---

## 0. The short answer

- **One signer, many cells: survives.** One signer can change several cells atomically, value is conserved across
  them, and the whole call tree fails together. The names are now `Turn.touches`, `checkValue` and effects-as-calls.
- **Several signers in one atomic turn: gone.** Nobody decided to cut it. Nano's substitute is sequential: a
  `quorum` law collects approvals over several turns.
- **The hyperedge as the turn's universal object** (N2/N4, tiers, distributed knowledge, the agreement mesh): absent.
  Most of it was theory in Mini too, and in Mini it never reached admission.
- **Intent-as-co-receipt** (the breadstuffs design): never reached Mini. Mini kept the word "intent" for a plain
  request. Nano deleted even that ("no intermediate intent type").
- **Guarded holes:** the kernel object is gone. The *weak* hole can be written as an ordinary package (LANG-45's
  CappedTally is one). The *strong* hole stays inexpressible, which is correct.
- **LANG-44** (rows, `admit_comm`) is the first nano decision that touches this family. It is the single-node half of
  Mini's "independence logic". It is still only PROPOSED.

## 1. Summary table

| concept | Mini meaning (pointer) | built in Mini? | nano status | needed for the single-node vat? |
|---|---|---|---|---|
| intent-centric turn / intent as co-receipt | B: `INTENT-AS-CO-RECEIPT.md` §1–3; Mini kept "intent" = one request (M:`Kernel/Contracts/Intents.lean`) | the co-receipt idea: no (breadstuffs Lean only); request-intent: yes | request: PRESENT as the signed `Call` + pins. Co-receipt: ABSENT, never decided | no |
| receipts | M:`Kernel/Receipt.lean`, `docs/OB3-RECEIPT-ENCODING.md` | yes (J6) | PRESENT: the journal entry (KERNEL-17/33/41), `replayed`, `lookup` | yes, and present |
| joint turn, one signer | M:D-0002, `HYPEREDGE-DESIGN.md` §0 | yes (JPAY6, JJOBM, JJ, call trees) | PRESENT under other names (touches + `checkValue` + LANG-21/23/33) | yes, and present |
| joint turn, N signers | M:`Kernel/Turn.lean` `Hyperedge` (one leg per party); D-0002 | single-Store multi-leg: yes; multi-signer cross-Store (Generic Simplex): compiled in, no journey | ABSENT; sequential `quorum` instead; cross-World refused `wrongWorld` (KERNEL-24) | no, multi-node |
| invariant domains (a law across several objects) | M:`Kernel/ObjectiveDomain.lean` | yes (OB GPT-6 row A) | ABSENT (NANO-VS-MINI §2) | arguably yes; see §4.4 |
| hyperedge as limit (N2), distributive law (N4) | M:`N2-HYPEREDGE-LIMIT.md`, `N4-DISTRIBUTIVE-LAW.md` | N2a + N4's abstract half proved; never on admission | ABSENT | no |
| finality tiers / distributed knowledge / agreement mesh | M:`DISTRIBUTED-DESIGN.md`, `Kernel/HyperedgeTier.lean`, `HyperedgeKnowledge.lean`, `NativeJointAgreement.lean` | theory leaves; agreement seam only | ABSENT; one writer per Store | no, multi-node |
| independence logic (disjoint footprints commute) | M:`DISTRIBUTED-DESIGN.md` §2.1 `Theory/Confluence.lean`; journey BD | yes (BD row) | PROPOSED: LANG-44 `admit_comm` | yes |
| guarded hole (weak) | B:`docs/DESIGN-partial-turn-promises.md` §1; M:`Theory/GuardedAdvice.lean` | Theory only in Mini; deployed in Bread | expressible as a package (LANG-6, LANG-45); no kernel object | partly |
| activities / sends / continuations | M:`docs/OBJECTIVE-BEND.md` §Activities, §Calls and sends | yes | ABSENT on purpose (LANG-6) | no |
| attenuable token (the through-line) | B:HORIZONLOG.md:17203 | grants yes, proofs no | PRESENT: grant chains (KERNEL-20/21/25/26); "proof-carrying" = re-execution | yes, and present |

---

## 2. Intent-centric turns and co-receipts

**(1) What it meant.** The design is in B:`.docs-history-noclaude/rebuild/metatheory/INTENT-AS-CO-RECEIPT.md`
[read]: "The turn has two faces: the receipt (it happened) and the intent (let it happen). They are adjoint through
`Predicate ⊣ Witness`." Read as a string diagram, a co-receipt is a receipt whose interior is left as a typed hole (§1).
An intent has four faces (§2): boundary (offered ⊗ wanted), predicate, funding (an escrow cell), and validity (a
causal-or-frame time window). Fulfilment plugs in a morphism and turns the co-receipt into a receipt
(`fulfill : Intent ⊗ Morphism ⟶ Receipt`). Matching is a coend `∫^B Offer(A→B) × Match(B,C)`, which is what a solver
computes (§3). The problem it solved: an Anoma-style exchange of "I bring A, I want C", with anti-frontrunning as a
causal type. The Lean is B:`metatheory/Dregg2/Intent/Core.lean` (`fulfill_discharges`, `no_double_fulfill`), with
siblings `Intent/{Match,Kernel,KernelBridge,Lifecycle,Centers}.lean`; it is consumed by
`Dregg2/Apps/SealedBidAuction.lean` [read: header and importers].

**(2) Was it built in Mini?** No. Mini kept the word with a narrower meaning:
- `Kernel/Contracts/Intents.lean` [read]: "An `Intent` is one semantic request by one actor: a 16-byte salt …, the
  actor, and one `Cut`". There is no hole, no predicate face and no funding face.
- `Kernel/DurableDataIntent.DataIntent` [read via `Kernel/TurnOfIntent.lean` header]: every Host admission ends in one
  `DataIntent`, and `Turn.ofIntent` emits the turn as a diff against the held cell. Here "intent" means the
  receiver's planned write.

Mini's closest relatives of the four-faced intent are product rows: JMKT ("the sealed market: bids commit, reveals
open, the runner settles on revealed bids") and JJOBM (escrow, bond, payout) [read: M:`native/resource-client/journey.sh`
TITLE lines]. A grep at 2c27b08b for `coreceipt|co-receipt` outside evidence finds only key "co-signature" hits
[read]. **The co-receipt never reached Mini.**

**(3) In nano.** The request half is PRESENT under another name. A request is the signed `Call`: the member, its key,
`pins`, the window and `maxCharge`. N:`Kernel/Receive/Call.lean` header [read]: "There is no intermediate intent type."
K0's critique deleted Mini's `DataIntent` stage as "minidregg's K1 twin" [read: N:`DECISIONS.md` K0].

The charter's "guard-from-intent staleness refusal" is this [read: N:`Kernel/Proofs/Admit.lean`]:
- `stale_refused`: a touched cell whose current pin ≠ what the signer saw is never admitted.
- `admit_pins`.
- `receive_congr` (N:`Kernel/Proofs/Receive.lean`): two Worlds that agree on the pinned cells derive the same Turn.

So the "intent" a turn is judged against is exactly *what the signer observed*.

Three of the four faces exist as separate parts:
- **Predicate:** laws and LANG-44's proposed row guards.
- **Funding:** the escrow package `world/escrow/Escrow` with phases `open|held|released|refunded` (LEDGER-6, LEDGER-10)
  [read].
- **Validity:** `notBefore`/`validUntil`, a window of heights (PROTOCOL-27) [read: heading].

The **co-receipt as an object** (a typed hole a third party fills, and the filling becomes the receipt) is ABSENT.
No decision names it, so it is lost by omission. The solver/matching face is absent from both trees [inferred: no
solver module in either].

**(4) Cost of bringing it back** [inferred]. On one node the co-receipt is a *package*, not a kernel change:
- an object whose state holds the boundary and the predicate;
- funded through LEDGER-6's mutate grant into an escrow account;
- with a `fill` method whose law checks the predicate, and whose emitted `transfer` (LANG-23) releases the funds.

That adds zero premises to landed kernel theorems and needs no flag day; it is one more `world/` package with its
law theorems, like Escrow. Two things it cannot have today:
- **A typed hole:** the language has no list type and no polymorphic boundary (LANG-1 critique, LANG-23).
- **A solver:** a coend needs search, and LANG-44 critique (2) says a method "cannot search; it must be told which key
  to check".

LANG-44's rows would make an *order book* expressible: offers as rows keyed by (asset, price, id), many writers
inserting without conflict. A refusal journal does not help here (§3).

**(5) Need for the vat.** Not needed. One node with a trusted operator has nobody to match against but its own members.
The escrow, the windows and the laws already cover "let this happen, funded, before height h". The co-receipt as a
*concept* is worth one sentence in a nano decision; see §8.

## 3. Receipts, and receipts as proofs

**(1) Mini.** M:`Kernel/Receipt.lean` header [read]: "a committed turn leaves one receipt Q — the committed …"
(OB3-RECEIPT-ENCODING §1). HYPEREDGE-DESIGN §4 [read] made it "one receipt Q … anchored at `apex`", uniform over ι,
so a joint turn has one receipt and not N of them. That is requirement R6 ("leaving one shared receipt",
M:`KERNEL-NECESSITY.md:42`).

**(2) Built in Mini?** Yes. J6 is "stop/reopen: receipts recovered, exact retry replays"; the fleet-surface
evidence has receipt-by-hash and receipt-by-head lookups (`docs/evidence/2026-09-30-fleet-surface/journey/`) [read:
file list].

**(3) Nano.** PRESENT:
- KERNEL-17 [read]: "the journal entry … IS the receipt: `lookup` (HOST-8) answers `committed (height, digest)`".
- KERNEL-7: a retry is `replayed h` by txId alone.
- KERNEL-33 / PROTOCOL-33: past the window a lookup is `uncertain forgotten`, never `refused`.
- KERNEL-41 (a′), as LANG-44 describes it [read: N:`decisions/lang.md` LANG-44 (a)]: the journal is a second instance
  of the one trie, and the head link commits its root. So a receipt can be proved against a head
  (`journal_inclusion_sound` and the other 6 JournalHead statements, listed in LANG-44 (c)).

"Receipt as proof" in nano means **inclusion against an authenticated head, checked by re-execution upstream**. It is
not a STARK; this matches the Mini decision in memory `project-no-proof-system-in-mini-admission`. Thin consent
(PROTOCOL-14 option A, PROTOCOL-18 `adopt HEIGHT DIGEST`) [read] is the read-side form: a member trusts a base digest
and re-derives the suffix.

**Refusal journal.** I find no decided entry. On disk, KERNEL-43 is the *allowance budget* decision [read:
N:`wt/kernel/decisions/kernel.md:1728`]. "KERNEL-43 refusal journal + checkpoint proposal" appears only as KERNEL-13's
work queue in `redregg/work/ROLES.txt:136` [read]. Today refusals are not journaled: "lookup never answers `refused`"
[read: N:`decisions/host.md:34`]. A refusal journal would record failed attempts. It would cover none of the
co-receipt (a co-receipt is an *open* offer, not a failed one) and none of the joint turn.

**(5) Need.** Needed, and present.

## 4. Joint turns

**(1) What Mini meant.** M:`docs/HYPEREDGE-DESIGN.md` §0 [read]: "Minidregg has ONE turn model: the hyperedge … A
single-cell action is the `ι = 1` hyperedge. A transfer is `ι = 2` … An N-party joint turn is `ι = N` — the same
object, no special shape."
- M:`Kernel/Turn.lean:38` `structure Hyperedge` has fields `agree : ∀ i, turnId i (step (x i) t) = tid` and
  `balanced`, plus the theorems `legs_agree` (pairwise agreement *derived* from one apex, not C(N,2) data) and
  `binding_is_proper` (a cone that agrees but does not balance) [read].
- D-0002 [read]: "Joint turns are finite N-incidence hyperedges over one canonical pre-state and shared apex. Every leg
  is authorized against that same state; … aggregate full-width resource delta is checked once; one post-state and
  receipt are committed atomically. This replaces the Mina call forest."

The problem it solved: breadstuffs had two turn models (the executed delegation forest and the proved-but-disconnected
hyperedge) joined by `JointViaHyper` welds. Mini made the hyperedge the only turn model.

**(2) Built in Mini?** Yes, inside one Store:
- M:`Kernel/MultiCellHyperedge.lean` (718 lines; "every incidence chooses its own store layout … The only shared data
  are the turn header, the joint receipt binding, and the resource equation") [read].
- `Kernel/PurseRefill.lean` ("A Book burn funds an AgentGrain purse in one joint turn over two cells", with
  `overclaim_fails_commit` and `refill_conserves`), wired into `Kernel/NativeHost.lean:2263–2298` [read]. It is
  exercised by journey **JPAY6**.
- JJOBM (job money as conservation-checked Book turns) and **JJ** ("a law reads another participant by position",
  `joint/index/i`) [read: journey titles].
- `Kernel/ActivitySeatEnd.lean:80` "The joint turn conserves every asset" [read].
- Objective Bend call trees: "The whole tree co-fails: any refusal refuses the turn" (M:`docs/OBJECTIVE-BEND.md`
  §Calls and sends; the DAO mutant is journey row C5) [read].

Across Stores, Mini compiled a joint-reservation and agreement path (`Kernel/Joint{Reservation,Receiver,PromiseAuthorization,…}`,
`Compiler/GenericSimplex*`). Its imports are wired into `Kernel/NativeHostReplay.lean:69–72` [read]. But
`NativeJointAgreement.lean` says of itself "This is NOT a network certificate verifier or an implementation of Generic
Simplex" [read], and no journey title names a cross-Store joint commit [read: journey.sh TITLE list]. So the
multi-party, multi-node joint turn was a seam, never a journey.

**(3) Nano.** For one signer it is PRESENT under other names, with the same meaning:
- N:`Kernel/Turn.lean` [read]: a Turn names many cells (`touches : List (Touch D)`, each with `seen` and
  `keep | write | retire`) plus `creates` and `nullifiers`, all admitted atomically by `World.admit`.
- `balanced` is LEDGER-2's `checkValue`: `World.admit` refuses `notConserved` when a turn moves a denomination's
  balance sum (N:`Kernel/Receive/Ledger.lean` header, `Kernel.Proofs.Value.admit_value`) [read].
- The call tree is LANG-21 → LANG-23 → LANG-33 [read]: a method returns its calls as data; the invoke receiver visits
  each object once (`visit_distinct`), refuses re-entry by name, and is bounded by `callDepthMax = 4` and
  `callsMax = 8`. Every visited object's laws judge its own `old → new`, and `sealTurn` takes all the effects into one
  Turn, so the tree commits or fails as a whole.
- The bounty row (escrow `release` emits the transfer) is Mini's "approve ⇒ transfer" joint turn (LANG-21) [read].

What nano dropped:
- **Several signers in one turn.** A `Call` has one member and one key (N:`Kernel/Receive/Call.lean` header) [read].
  The substitute is `Std.quorum` (k of m members approve across turns; LANG-19, KERNEL-27, the `quorum_text_at` and
  `judgeOne_quorum_*` theorems) [read]. It is sequential and not atomic: a proposal sits in state between approvals.
- **A law over several objects.** Mini's `Kernel/ObjectiveDomain.lean` ("a set of member objects with a JOINT law …
  'these two balances sum to the reserve'") [read] is listed NO in NANO-VS-MINI §2. LANG-21's critique names the gap
  ("no law spans the objects changed together") [read]. LANG-44 critique (4) excludes the analogous law for rows on
  purpose.
- **Cross-World turns.** These are refused before anything else: KERNEL-24, `wrongWorld` [read: N:`decisions/kernel.md:579–598`].

None of these drops is a charter law. Multi-signer and domain laws were never decided; they are lost by omission.
Cross-World refusal is a decision (KERNEL-24) whose purpose was replay safety, not a ruling against joint turns.

**(4) Cost of bringing back multi-signer** [inferred; the theorem names are read, the counts are not measured].
- *Shape.* `Call` carries a list of `(member, key, signature)` over the same `callMessage` (KERNEL-42's domain);
  `receive` checks every signer; authority becomes "ownership or a chain, for the signer who owns that cell".
- *Premises on landed theorems.* `receive_ok`'s "signed" clause; `write_authorized`, `invoke_authorized` and
  `enroll_authorized` gain a signer index; PROTOCOL-39's pairwise-disjoint signed shapes gain one shape; the follower's
  `rederive` (Audit) is unchanged in form. `receive_congr` keeps its statement, because pins do not change.
  `stale_refused`, `admit_value` and the frame theorems are untouched: `World.admit` never sees signers.
- *Flag day.* Call codec and `callMessage`; every Store re-geneses (free under law 1); CLIENT custody must assemble
  co-signatures, which is new protocol, since today the client signs alone.
- *Domain law* (the ObjectiveDomain sibling). It is a new kernel-judged object. It adds a premise to every law-running
  statement in `Lang/Proofs/Receiver.lean` (the 85 law theorems LANG-44 kept unchanged) unless it is a separate
  judge, as row guards are in LANG-44. Neither LANG-44's rows nor a refusal journal covers it.

**(5) Need.** The single-signer joint turn is needed and present. Multi-signer atomic turns matter even on one node
whenever two members swap value at once (A's asset for B's in one turn); today that takes escrow plus two turns.
That is the first concept here that a *single-node* vat could want without any trigger. Multi-Store joint turns are
multi-node machinery.

## 5. Hyperedge consensus: the canonical hyperedge kernel, N2, N4, tiers, knowledge

**(1) What Mini meant.** M:`docs/KERNEL-NECESSITY.md` [read] set out six "necessity theorems". The ones that matter
here:
- **N2:** the hyperedge is the *limit* of N-party atomic-update cones; pairwise agreement holds because of the limit.
- **N4:** "the kernel … is exactly a distributive law λ : Σ∘B ⇒ B∘Σ". From Turi–Plotkin this would give
  bisimilarity-as-congruence and operational = denotational.
- **N6:** aggregation is a colimit.

`DISTRIBUTED-DESIGN.md` §0 [read] judges every turn by three logics: conservation, ordering (a finality-tier lattice)
and independence (I-confluent merges). It says Mini had "the first logic end to end … and none of the other two".

The "consensus" reading is in two files:
- `Kernel/HyperedgeKnowledge.lean` [read]: "the apex is DISTRIBUTED KNOWLEDGE among the honest legs";
  `fork_has_no_distributed_apex`.
- `Kernel/HyperedgeTier.lean` [read]: `commitTier := Finset.univ.sup tierOf`; a turn runs coordination-free iff every
  written cell is tier 1.

**(2) Built in Mini?** As theory, partly. None of it reached admission.
- N2a is proved (`Kernel/TurnLimit.lean`, `hyperedge_is_wide_pullback`). N2b (the balanced-cone category) was designed
  in `N2-HYPEREDGE-LIMIT.md` §1 [read].
- N4's *abstract* half is proved in `Compiler/DistributiveLaw.lean` (`N4_adequacy`, `N4_congruence`, `FailClosed`
  proved for `strictLaw` and refuted for `openLaw` on `joinT goT stopT`) [read]. Its own residual
  `[N4-hyperedge-instance]` says the kernel instance "Waits on the twin decision … and on `Obs`" [read]. The only
  importer is the `Minidregg.lean` umbrella [read: git grep].
- The tier and knowledge files are imported only by `Kernel.lean`, `Theory/Finality.lean` and the Assurance manifest
  [read: git grep]. Their own residuals are `[TIER-gate]` ("`admit` does not consult tiers") and
  `[HYPEREDGE-operational]` [read: DISTRIBUTED-DESIGN §2.3, §2.5].
- The agreement mesh (Generic Simplex, 4 replicas on one host) is NANO-VS-MINI §2's row "NO" [read].

The independence logic did reach a journey: **BD**, "two plans on disjoint cells are admitted in both orders without
re-plan; a second plan on the same cell is refused" [read].

**(3) Nano.** ABSENT, with no charter law against it and no decision deferring it. The structural reason:
- One writer per Store ("ONE writer (`host serve`)", N:`decisions/perf.md:11–12`).
- Followers re-derive (`Kernel/Receive/Audit.lean`).
- A cross-World call is refused (KERNEL-24).

There is no apex to agree on. Every Turn has one total order, and the head chain is the agreement.

One piece is coming back by another route. LANG-44 (PROPOSED, 2026-10-18) [read] states `admit_comm`: "two turns whose
footprints are disjoint … admitted in either order from `w` reach Worlds with equal cells and rows tries". That is the
single-node form of DISTRIBUTED-DESIGN's independence logic and of Mini's BD row. LANG-44 (b) also records the CRDT
reading: "an insert-only relation is a grow-only set … replicas could converge by union". It declines to build that
reading, because value, authority, limits and once-keys do not commute.

**(4) Cost of bringing back** [inferred].
- *N2/N4 as theorems about nano's Turn.* Cheap in premises: they are statements *about* `World.admit`, not changes
  to it, so no landed theorem gains a premise. But they need Mathlib (category theory; `PFunctor.M`), and LANG-15 and
  GATES-1 rule Mathlib out of nano [read: N:`decisions/lang.md` LANG-15 heading]. Reintroducing it is a charter-level
  change to the build (law 8's closure ceiling, the 150-module Host closure). Mini's own N4 finding says the content
  lives only at the joint (binary) node (`sequential_law_is_option_map`), so on a one-signer nano it would be nearly
  empty.
- *Tiers and agreement.* A second writer is a whole layer: Turns gain foreign pins (pins into another World's head),
  and `fold`'s statements gain a merge premise (every fold/chain theorem LANG-44 (c) lists assumes one log). The flag
  day is the World and head shape.

**(5) Need.** Not needed for the vat. It is multi-node machinery behind a trigger, and the natural trigger is "a
second writer for one World" (two vats co-owning state). Before that trigger, `admit_comm` is the only part with
single-node value.

## 6. Guarded holes and contexts

**(1) What it meant.** B:`docs/DESIGN-partial-turn-promises.md` §1 [read]: "A guarded hole is a typed promise: a slot
in a turn's effect stream that commits now but is filled by a later resolution turn, and only if a guard predicate
holds at fill time." The design splits holes in two:
- The **weak** hole (a guard on a late-filled *value*) is built. Its Lean is B:`Exec/GuardedHole.lean`,
  `holeFill_binds_in_circuit`; the deployed Bread effect pair is Promise/Notify/React (§2.2).
- The **strong** hole (an undetermined δ or shape) is "deliberately inexpressible".

The governing rule: "determination is EAGER, witness is LAZY." HYPEREDGE-DESIGN §5 [read] carried this into Mini:
"Holes are legs with lazy witnesses. An intent is a turn shape with an unfilled leg whose δ, footprint, and demand are
already fixed".

"Contexts": the co-receipt is literally a one-hole context (a receipt diagram with its interior removed; §2), and
filling the hole is plugging. That is the only sense I found in which holes and contexts are one idea. Mini's
`docs/RESIDENT-CONTEXT.md` is unrelated: it is about an agent's document context [read].

**(2) Built in Mini?**
- The kernel object is Theory only: M:`Theory/GuardedAdvice.lean` [read] (`HoleSpec` fixes turn, root, authority
  demand, footprint, guard, effect, deadline, continuation and nullifier domain eagerly; `Advice` "contains exactly one
  thing: a value"; `verifyFill`, `commitFill`) and `Theory/CanonicalReactiveView.lean:235` ("Accepted guarded holes as
  canonical prepared reactions"). Outside Theory and Assurance, these are imported only by
  `Compiler/{MinidreggV1Artifact,SemanticArtifactBundle}.lean`, with no Host importer [read: git grep].
- The *runtime* holes Mini did deploy were Objective Bend activities: "An activity hands a typed Plan to its host,
  waits, and continues with the typed response" [read: `OBJECTIVE-BEND.md` §Activities]. Alongside them: inboxes,
  sends, `deliverMessage`, prepaid continuations with `escrow_conservation` (§Calls and sends).

**(3) Nano.** The kernel object is ABSENT. Suspension was cut **on purpose** by LANG-6 [read: N:`DECISIONS.md:525`]: "No
`perform` in v0 … Multi-turn behaviour is explicit data in the object's state (a defunctionalised state machine)."
Its reasons are measured: delvetalk's checkpointing cost, and Mini's "~25 files of checkpoint/settle/collect
metatheory".

The weak hole is still *expressible*, and one has been built. LANG-45 [read] ports Mini's CappedTally:
- "The patience is a `closes` height. The law `decider` holds the signer's window to it … and refuses any agent but the
  decider", with laws `cap` and `grows`.
- That is a weak guarded hole in package form: the shape is eager (who fills, by when, the bound) and the value is lazy
  (the amount).
- The escrow's `held → released | refunded` is another.

The strong hole stays inexpressible: a Turn's `touches` and `charge` are fixed by the signer, and `charge = weight`
exactly (KERNEL-12).

**(4) Cost of bringing back a kernel `HoleSpec`** [inferred]. It is not worth it on one node. It would be a second shape
of "a law over a pending state" (law 1), because packages already express it with proved law theorems (the 85 in
`Lang/Proofs`). Mini's own record is that the kernel object never reached the Host.

LANG-44's rows help the *many-holes* case: one open hole per row (keyed by requester), each filled by an `upsert`
pinned at that row. Many fills on one object then commute (`admit_comm`).

Bringing back `perform` and sends would be a LANG flag day (method type, package ids, demand-machine budget theorems,
which LANG-44 (f) already counts against recursive types). LANG-6 is the decision it would reverse.

**(5) Need.** The weak hole is needed and present as a package pattern; it deserves a name in the Std library (§8).
Suspended activities are not needed for the vat.

## 7. Siblings

- **Attenuable proof-carrying token** (the through-line, B:HORIZONLOG.md:17203 [read]: "a turn = an attenuable
  proof-carrying token over conserved state leaving a receipt"). In nano:
  - *Attenuable:* grant cells, chains walked to the owner, `grantWidens`, `revoke` kills every chain through it, the
    enrol ledger carved from its parent (KERNEL-4/20/21/25/26) [read].
  - *Proof-carrying:* the call carries its grant chain (pins), not a proof; admission is re-execution.
  - *Conserved state:* `checkValue`, with storage conserved too (KERNEL-19).
  - *Receipt:* the journal (§3).

  All four words survive; "proof" means "checkable by re-derivation", which is the Mini decision.
- **Witness DAG / intra-turn conferral** (HYPEREDGE-DESIGN §2: a leg cites a grant conferred by another leg of the same
  turn). Nano's nearest relative is LANG-21's "object-as-grantee: a callee's `Req.principal` is the CALLING OBJECT".
  Conferral within a turn does not exist: grants are cells born by one turn and used by a later one. Lost by omission;
  not needed on one node [inferred].
- **Invariant domains.** See §4. This is the sibling most likely to be wanted first.
- **Fail-closed joint refusal** (N4's `strictLaw` vs `openLaw`). Nano has the property by construction: `sealTurn`
  takes the whole tree or the receiver refuses. A named theorem would be "an invoke tree with a refusing node derives
  no Turn". I did not find one under that name [inferred: not grepped exhaustively].

## 8. For Ember (half a page)

**What survived.**
- **The atomic multi-cell turn under one signer, with conservation.** `touches`, `checkValue`/`notConserved`, and
  call trees that fail as a whole (LANG-21/23/33). It is the hyperedge with ι cells and one authority.
- **Receipts:** the journal entry is the receipt, authenticated by the head (KERNEL-17/33/41).
- **The guard-from-intent:** every touch pins what the signer saw (`stale_refused`, `receive_congr`).
- **Attenuable authority:** grant chains.
- **Weak guarded holes:** writable as packages (LANG-45's CappedTally, the escrow).
- **Independence logic:** returning as LANG-44's `admit_comm`, proposed and not yet built.

**What was cut on purpose.**
- Suspension (`perform`, activities, sends, continuations): LANG-6.
- The `DataIntent` middle stage: K0.
- Cross-World calls: KERNEL-24, `wrongWorld`.
- Mathlib, and with it N2/N4: LANG-15, GATES-1.
- The agreement mesh, implicitly: one writer per Store.

**What was lost by omission (nobody decided).**
- **Multi-signer atomic turns.** Nano's `quorum` is a sequential substitute, not the same thing.
- **Joint laws across several objects** (Mini's invariant domains).
- **The co-receipt as a first-class open offer, and matching.** Mini had already lost this from breadstuffs.
- **Intra-turn conferral.**
- **The finality-tier and distributed-knowledge theory.** It never reached Mini's admission either, so little was
  lost in practice.

**Worth restating as nano decisions now.**
1. **The joint turn's scope, decided in writing.** One KERNEL entry should say three things. A Turn is the hyperedge
   for one signer. Multi-signer atomic turns are deferred, with the trigger "the first row where two members must
   exchange in one turn" and the price from §4(4). Cross-World joint turns are deferred behind "a second writer for
   one World". The cost is a paragraph, and it turns an omission into a decision with a trigger.
2. **The intent as an eager-shape/lazy-value hole, named once.** One Std law family (LANG-20's library) should say
   "a pending slot: who may fill it, by when, under what bound, funded by which escrow". Its meaning theorem would
   follow `holeFill_binds_in_circuit`: a fill commits exactly its value and its guard. CappedTally and the escrow then
   become instances, not two hand-written patterns. That is the co-receipt idea brought into nano's shape at zero
   kernel cost. LANG-44's rows are what let many such holes on one object be filled concurrently.
