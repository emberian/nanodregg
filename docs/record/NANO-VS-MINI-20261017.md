> record copy of redregg/work/NANO-VS-MINI-20261017.md, 2026-10-17; the lane logs stay in redregg

# nanodregg vs minidregg — scope, semantics, and which way to go (2026-10-17)

> **CORRECTION (2026-10-21, Ember, recorded by ROOT-DOCS).** This brief's framing of breadstuffs is wrong and
> out of date: its row assigning "PoA / bread / galley / atproto / federation" to breadstuffs as a live line, and any reading of breadstuffs as a running main line. Ember: "PoA actually isn't even a real or running thing, so the idea that breadstuffs is
> PoA mainline is hilarious and extremely wrong/out of date … breadstuffs is where our whole system we built
> lives and we've been splintering out into these side projects (mini, nano) for diversity and continued focused
> exploration while the whole breadstuffs system waits there to be either resumed or truly composted into the
> next version of robigalia." Read every PoA / main-line / quarry / museum sentence below against that.

Reader: ROOT and Ember. Read-only pass. Pointers:
`M:` = minidregg at **2c27b08b** (the charter's spec commit), read with `git show 2c27b08b:PATH` in
`~/dev/minidregg` (the Mac checkout is at `dcab86da`, **158 commits behind** 2c27b08b; nothing here reads the stale tree).
`N:` = nanodregg at hbox `/tank/dregg-build/nanodregg/main`, **71379a1** (405 commits since the first, 2026-10-16 18:30 −0400).
Tags: **[read]** = I read it at the pointer; **[inferred]** = my conclusion from what I read.

## 0. Ember's questions, in four sentences

1. **Going well, at the part it chose:** in 405 commits nanodregg has built a small, proved core (≈62K Lean lines, 2,828
   theorems, 0 `sorry`, 0 deployed `partial`) whose 21 conformance rows pass against real processes over sockets, but
   it covers Mini's KERNEL plus the skeleton of the October-13 shellserver, not Mini's product: documents, rooms, chat,
   the shell for remote friends over ssh, SPK apps, Solana pay, activities, the agreement mesh and privacy have no
   nano counterpart, and THE BAR has not been judged.
2. **The semantics are aligned at the core and diverged on purpose in the language:** nano's World/Turn/`admit` is
   Mini's TURN-LOG end state restated (pins as the one staleness check, a windowed journal, nullifiers, exact charge,
   ROM at birth, one admit, re-execution rather than proof), while Objective Bend was cut on purpose (LANG-0..6:
   monomorphic call-by-value with lazy record fields, laws as ordinary terms, the checked core installed instead of a
   front end re-run, append-only laws, no activities, reflection or quantities), and carry keeps state but never history.
3. **The actual difference** is about 10× in scope (586K vs 62K Lean lines; 167 Host opcodes vs 6 wire operations and
   13 call kinds) and the discipline: nano decides every byte in Lean (pure-Lean Ed25519, generated client tables,
   gates that refuse commits), and Mini has the working product surface on top of a kernel that carries ~58
   per-receiver copies of `Reject`.
4. **Nano should not become a component inside Mini** (its laws forbid a second World, and the only parts that come
   out cleanly are libraries: codec, Ed25519, trie); the right path is to keep Mini as the spec while nano grows to
   cover it, then move Mini's product layers onto nano's kernel. The switch happens when THE BAR passes, judged over
   sockets with two remote friends and Hermes, **and** one real Mini `.obend` application runs on nano's core.

## 1. Sizes (measured)

| | minidregg @2c27b08b | nanodregg @71379a1 |
|---|---|---|
| Lean files / lines | 1,625 / 586,348 (Kernel 204,945; Compiler 101,744; Theory 86,022; Selvage 78,021; Assurance 60,217; Host 38,337) [read: `git grep -c ''`] | 288 modules (144 proof modules) / ≈62K (Lang 16.7K, Kernel 12.1K, Codec 9.6K, Host 8.9K, Hosting 5.3K, Protocol 5.1K) [read: N:`SIZE.md`] |
| Rust lines | 291,827 across ~25 crates (resource-client 140 files, spk-host 85, grain-runtime 59, private-backend 42, …) [read] | 12,431 (nd 90, nd-supervise 154, client lib 1,864, generated 1,921) [read: N:`SIZE.md`] |
| wire surface | 167 opcode arms in `Host/Main.lean`, 176 allocations in `protocol/host-operations.json` [read: M:`docs/design/RECEIVER.md` §1, measured at 5216e02f] | 6 operations, 13 `Receive.Body` kinds, 17 command verbs, 59 refusal constructors [read: N:`SIZE.md`] |
| acceptance | runner rows: 28 (`JOURNEY_ROWS`), plus ~85 `journey.sh` STEPS [read: M:`scripts/pipeline/journey-rows`, M:`native/resource-client/journey.sh`] | 21 rows in `Protocol/Rows.lean`, each with a plant [read] |
| open backlog | 429 open+claimed `cv task`s in repo minidregg: 44 touched ≤3 d (23 titled "census defect …"), 385 older (274 at 13 d) [read: `cv task list --all --tsv`] | 21 open, 17 done [read: same] |

## 2. Scope table: every Mini subsystem vs nano

HAS = same job exists in nano; SHAPE = exists in a different shape; NO = absent.

| Mini subsystem | Mini pointer | nano | nano pointer / note |
|---|---|---|---|
| Kernel World / Turn / `admit` / `fold` | M:`Kernel/World.lean` (2,814 lines) | HAS (smaller) | N:`Kernel/World.lean` (659), `Kernel/Turn.lean` (101) [read] |
| Receivers (signed call → Turn) | ~57 `*Receiver*` files; 58 `inductive Reject` copies [read: M:RECEIVER.md] | SHAPE: one `receive`, one derivation per kind, one `Refusal` | N:`Kernel/Receive/{Derive,Call,Authority,Ledger,Submit}.lean` [read] |
| Objective Bend language | M:`Theory/ObjectiveBend*` (~46 files), `Compiler/ObjectiveBend*` (28) | SHAPE (cut on purpose) | N:`Lang/` 16.7K lines; DECISIONS.md LANG-0..7 [read]; §3.4 below |
| `.obend` surface + front end (parser, elaborator, C4) | M:`Compiler/ObjectiveBendFrontEnd*`, `Host/ObjectiveBendFrontEnd.lean` | NO: an s-expression core reader + one printer | N:`Lang/Read.lean`, `Lang/Print.lean`; LANG-0 point 2 [read] |
| Law fragment (`LawExpr → Pred`) | M:`Compiler/ObjectiveBendLaw.lean`, `Pred/` | SHAPE: a law is a term returning a Verdict | LANG-0 point 1, LANG-4, LANG-8 [read] |
| Activities (perform/done, checkpointed machine state) | M:docs/OBJECTIVE-BEND.md §Activities; `state_roundTrip` | NO (on purpose) | LANG-6 [read] |
| Object upgrade (ADOPT / MIGRATE / drain / rebirth) | M:`Kernel/ObjectiveActivityUpgrade.lean` | SHAPE: append-only laws + `adopt` occasion | LANG-4, LANG-24, KERNEL-27 [read] |
| Invariant domains (joint-state laws) | M:`Kernel/ObjectiveDomain.lean` | NO | grep for domain/joint-state laws: none [read] |
| Cross-object calls / sends | M:OBJECTIVE-BEND.md §Calls and sends | SHAPE: method returns calls as data, run under the object's authority; no sends | LANG-21, LANG-23, LANG-33 [read] |
| Seats / invitations | M:docs/SEATS.md | NO (grants + `enroll` only) | [inferred from Body list] |
| Nock + evaluator registry | M:`Kernel/NockRun.lean`, `Compiler/Evaluator.lean` | NO | [read: no such module in N] |
| Admission check | re-execution; `witnessed` compiles to FALSE [read: memory `project-no-proof-system-in-mini-admission`] | same: re-execution; no proof slot | N:README "What is true today" [read] |
| Signature verification | Rust helper `minidregg-credential-signature-verifier` (tests for ML-DSA, sshsig) [read: M:`native/credential-signature-verifier/tests/`] | pure-Lean Ed25519 (RFC 8032), proved field/curve; ML-DSA hybrid NOT built | CODEC-11/18/23; CLIENT-11 "NOT IMPLEMENTED" [read] |
| Durable store | SQLite `forward-link.sqlite3` + KMAC log tags + head anchor + checkpoint every 64 [read: M:docs/DURABLE-STORE.md] | SHAPE: framed append-only segment + sealed whole-World base + MAC'd fixed-entry index | HOST-4, HOST-14, HOST-30, HOST-33 [read] |
| Carry across runtimes | carry verifier: old runtime verifies continuity across an edge [read: M:docs/CARRY-VERIFIER.md] | SHAPE (diverged): export → re-genesis; state carried, history never | Law 1, OPS-1, KERNEL-29, HOST-28/34 [read] |
| Members, keys, rotation | participant enrolment, pre-rotation (JROT) | HAS: member cell, precommitted next key, `rotate` | KERNEL-6, `Body.rotate` [read] |
| Grants / capabilities | `caps : CellId → List Cap` [read: M:`Kernel/State.lean`] | SHAPE: grant cells, chain walk to owner, `grantWidens`, `revoke`, public grants | KERNEL-20/21/25/26 [read] |
| Value / ledger | `bal : CellId → AssetId → ℤ`, issuer wells at −supply, Books [read: M:`Kernel/State.lean`, `Kernel/World.lean` header] | SHAPE: `value` discipline, wells, floors, credit, escrow | LEDGER-2..11 [read] |
| Pay rail (Solana watcher, pay-to-enrol) | M:`native/pay-watcher`, JPAY1–6 | NO (the `pay` row is a once-key transfer only) | N:`Protocol/Rows.lean` `pay` [read] |
| Rooms, parentage | `parent` system namespace, K-ROOM rows | NO (K2(i): a parent would be a ROM slot; no rooms built) | DECISIONS.md K2 [read] |
| Documents / docuverse / marks / transclusion | ~20 journey hooks (j12*, jdocuverse) | NO | [read: no such module] |
| Chat, channels, relay | `jchat`, `jchan-*` | NO | |
| Studio, web entrance | `native/resource-client/src/web/` | NO | |
| Shell + friends over ssh | M4, J9, JP2, `sshe2e` | NO: CLIENT-12 is DESIGN ONLY; `attach/` exists (148 lines) | CLIENT-12; synthesis: "`nd-attach` under a real sshd waits" [read] |
| Client | `mini` (resource-client, 140 Rust files) | SHAPE: `nd` + `nd-supervise`, protocol knowledge only from a generated table | N:`client/`, PROTOCOL-6 [read] |
| Sandbox | grain-runtime + sandbox floor (M11) | SHAPE: one confinement shape per platform (bwrap / sandbox-exec), plant + bisection | CLIENT-9 [read] |
| Hosted apps (SPK, Sandstorm-style grains) | M:`native/spk-host` (85 files), 44/44 rows on 10-01 [read: M:README] | SHAPE (much smaller): a grain-lifecycle package + controller + launcher; no SPK format, no app has run | HOSTING-3..24 [read] |
| Hermes residents | M5, J14, Hermes controller | SHAPE: a member with its own seed; keybroker (TLS, allowances in the World, key never reaches the resident) | HOSTING-12..21 [read] |
| Key custody split (`mini-keys`) | M:`native/mini-keys` | HAS (different cut): custody records, observer record, keybroker | CLIENT-15/22/23, HOSTING-12 [read] |
| Thin consent (no full fold) | `jthin-consent` | HAS: `adopt HEIGHT DIGEST` | PROTOCOL-14/18/37 [read] |
| Agreement mesh (Generic Simplex BFT) | M:docs/agreement/CUTOVER.md; 4 replicas, one host [read] | NO: one writer per Store, followers re-derive | [read: N:README] |
| Distributed logics (confluence, finality tiers) | M:docs/DISTRIBUTED-DESIGN.md (designs) | NO | |
| Privacy (private rooms, disclosure, hiding, sealed channels, MPC/FHE research) | JPRIV1/2, JDISCLOSE, K-NARROW-HIDE | NO: "per-cell hiding is not designed" | N:README [read] |
| Proof-system research (Selvage, Assurance, zk) | 152 + 154 files [read] | NO (by design) | |
| Fleet surface (agent join/send/receipts/topics) | M:docs/FLEET-SURFACE.md, M8, fleetsign | NO | |
| Cross-Store publication over fn (selected release/exchange) | M:docs/FN-*.md, `exchange` row | NO | |
| Discord entrance | M:`native/discord-entrance` | NO | |
| Ops: units, runbook, backups | `deploy/`, dregg-infra | HAS: units rendered from Lean exit tables, runbook, `host check` | OPS-0..14 [read] |
| Census / gates | AxiomCensus, objective manifests, census-defect tasks | HAS, and stronger: commit judge (owners, size ratchet, axiom census, refine census, TCB table, vector immutability, runs table) | GATES-1..13 [read] |
| Perf workload / THE BAR | `scripts/perf/workload.{py,sh}`, rows births/growth/perf | SHAPE: deterministic waste ratios pinned + `scripts/bar.sh`; BAR unjudged | `gates/waste.tsv`, PERF-1 [read] |
| PoA / bread / galley / atproto / federation | not in Mini (0 paths each) [read: `git ls-tree`] | not in nano | these belong to breadstuffs; neither tree has them |

## 3. Semantics of the shared core

### 3.1 World, cells, nullifiers — **ALIGNED-DIFFERENT-SHAPE**
- Mini: `Cells R := Π₀ CellId, Option (Cell R)` with **typed** cells (a `Registry` of kinds and layouts), plus a
  **system cell** with namespaces `journal`, `head`, `retired`, `parent`, `spent`, `allowance : Lane ↦ Nat`
  [read: M:`Kernel/World.lean` header, lines 1–60]. Cell ids are `Nat`s `create` names.
- Nano: one persistent binary Merkle trie of cells **and** nullifiers, root committed into the chain every turn;
  a cell is untyped bounded slots `{kind, discipline : rom|appendOnly|ram|value, slots}`; retirement is a tombstone in
  the same map; ids are derived digests (`hash(txId ‖ i)`, content ids for ROM, keyed ids for accounts); one allowance
  [read: N:`Kernel/World.lean` 1–150, `Kernel/Cell.lean`; DECISIONS.md K2; KERNEL-23/28/30/41].
- Same meaning: a finite map of cells, ROM fixed at birth, nullifiers spent once, retired ids never reused.
- **Nano's shape is better** on four counts: the trie is canonical, so equal content means `=`, which matters
  for reopen and the follower; there is an authenticated root a phone can check (designed, the trie is proved, not yet
  consumed by the World per N:README); there are no `parent`/`retired` twins of facts the cells already hold (Mini's
  own header calls its authority-cell parent plane "the twin" T7 must delete); derived ids need no allocator.
  **Mini's shape is better** in one place: typed layouts let the kernel know a value's type. Nano moves all slot
  typing to the receivers and LANG, and K2's own critique says "a receiver bug can write a mistyped value the kernel
  happily stores" [read].
- **Lanes:** Mini meters by lane (`Charge` per `Lane`); nano uses one number, `charge = Turn.weight` exactly
  (storage), and compute (law/method ticks) is a consensus constant, not charged
  [read: KERNEL-12, `Lang/Law.lean` `lawTicks`]. **DIVERGED on purpose** (K2(e) critique names it as an open gap).

### 3.2 Turn and its signing — **ALIGNED**, nano smaller
- Mini Turn: txId, creates with ROM images, one guarded patch per written cell (`Leg`), retires, event, nullifiers,
  exact charge, signing subject and key epoch, the exercised capability, height window; no post bytes, no signatures
  [read: M:`Kernel/World.lean` header].
- Nano Turn: txId, window, `touches` (each cell named once, with the digest the signer saw and `keep|write|retire`),
  `creates` with ids, nullifiers, `charge`, `event` (the signed call, kept in the log as the audit trail)
  [read: N:`Kernel/Turn.lean`].
- The refusal sets match almost one for one: Mini `replayedTransaction / outsideWindow / nullifierSpent /
  chargeMismatch / overAllowance / imageNotRom / guardFailed` ↔ nano `replayed / outsideWindow / spent /
  chargeMismatch / overAllowance / notContentId / stale` [read: both `inductive Reject`].
- Differences: nano's pin (`seen` digest) replaces Mini's guarded legs, as the one staleness check; nano's
  `event` carries the signed call, so a follower **re-derives** every Turn (`Receive.Audit.rederive`) instead of
  trusting it [read]. Signing: nano signs `callMessage = domCall ‖ unsignedBytes`, every signed shape with its own
  domain, and the call names its World's origin (`wrongWorld` is checked first) [read: KERNEL-24, KERNEL-42,
  PROTOCOL-39]. Mini has the key epoch and subject inside the Turn. **Nano is better**: the cross-World replay
  (`ops/replay-20261016`) is refused by construction; Mini has no row for it [inferred: no Mini journey names it].

### 3.3 Admission — **ALIGNED** (re-execution), different structure
- Both admit by re-execution and run no proof system: Mini `witnessed` compiles to FALSE and runs are checked by
  re-execution [read: memory]; nano's README states the follower "re-derives every Turn from its signed request".
- Mini splits admission into a kernel transition plus ~57 receiver families with their own Reject/Accepted/Prepared/
  charge/replay copies [read: M:RECEIVER.md census]. Nano has exactly one path:
  `submit = journal check → receive (derive Turn over a pinned view) → World.admit`, no intermediate intent type
  [read: N:`Kernel/Receive/Submit.lean`; K0a]. **Nano's shape is better**: it is law 1 applied to the measured Mini
  failure, Mini's own "K1 twin" of receiver → DataIntent → execute [read: K0 critique].
- Objective admission: Mini re-runs the **front end** at admission and admits only a byte-identical typed core,
  then re-executes [read: M:OBJECTIVE-BEND.md §Native admission]. Nano installs the **checked core** (a ROM cell whose
  id is its content digest) and never re-runs a front end [read: LANG-0 point 2, LANG-5].
  **DIVERGED on purpose**: LANG-0's critique records the lost property ("install nothing not re-derivable from
  source") and prices restoring it at one source-digest field plus an offline gate.

### 3.4 Language — **DIVERGED on purpose** (and the largest semantic gap)
| aspect | Mini Core4 | nano Objective Bend | decision |
|---|---|---|---|
| evaluation | lazy call-by-name reference; **call-by-need** demand machine (heap, update frames, blackholes) | **call-by-value CEK**; record fields suspended, **no sharing**: a field is re-evaluated at every selection | LANG-2 (names the exponential case: `{a=1, b=self.a+self.a, …}`) |
| open recursion | `mix`, `fix spec inherited`, first-class `specification`, `prototype`, `reflect`, `metadata`, `project` | `fix t` with `t : R → R` (record knot) only; `mix` is authoring sugar; no prototype/reflection constructors | LANG-1 ("Dies" list; reflection on construction history is gone) |
| scalars | unbounded `Nat`, Bool, opaque labels; no bytes, no digest | Nat < 2^64 (overflow is a named fault), Bool, bytes, **`digest`** (ids are a type, never made from bytes) | LANG-L, LANG-38 |
| types | rows with tails, bounded type variables, quantities (affine/linear), computation type | **monomorphic**, exact rows, no quantities; checker proved equal to the typing relation | LANG-3 |
| effects | `perform plan` / `done`; activities persist as checkpointed machine state | none; a method is `State → Args → Req → {calls, state}`; calls are data run by the kernel under the object's authority | LANG-6, LANG-21/23/33 |
| laws | separate fragment `LawExpr → Pred` (decidable, comparisons over top-level fields); spec `claim` never checked | a law is an ordinary term `Old → New → Req → Verdict` under `lawTicks = 100000`; std laws are generators with meaning theorems over the reference semantics | LANG-0 point 1, LANG-4, LANG-8, LANG-20, LANG-26 |
| upgrade | ADOPT/MIGRATE with floor entailment (`adopt_floors_entailed`), drain, rebirth | laws only append; a new law judges the existing state at `adopt` | LANG-4, LANG-24, KERNEL-27 |
| packages | published core plus front-end identity; `.obend` source | `Package {imports, state, iface, body, methods, laws}`, id = content digest of the canonical bytes (imports included) | LANG-5, LANG-9 |
| printing / reading | `.obend` parser + elaborator + C4 | s-expression reader with a fuel bound; one printer with a proved round trip for every installable package | LANG-22, LANG-28..31 |
| digests | `Theory/ObjectiveBendDigest` exists, no term | `deq` is the only primitive that consumes ids | LANG-38 |
- What is proved on each side: Mini proves determinism, machine ↔ reference soundness, completeness, preservation
  and no-refusal for checked closed terms, plus admission theorems (`admitted_source_semantics`), all in the
  **opt-in** `ObjectiveProofs` library, not the default build; the surface has no semantics of its own
  [read: M:OBJECTIVE-BEND.md §What is proved / §What is open]. Nano proves unique typing, never stuck, fuel
  independence, the machine computes exactly the reference relation, the reader/printer round trip, and the law
  library's meanings, all inside the one build under the axiom census [read: N:README Layers table; LANG-18/29/42].
- Judgement [inferred]: **neither language is a strict improvement**. Nano's is smaller, bounded and checked
  end to end. Mini's has the parts its own design documents treat as the point (Faré-style partial specifications,
  reflection, sharing, persistent activities; M:BEND-WORLD-LANGUAGE "Decision and destination"). LANG-1's
  meta-critique says plainly that "the kept set is Core4 minus the parts whose proofs scared me" and files the rest
  as tasks. No Mini `.obend` program (ReviewBase, CappedTally, `world/market/*.obend`) has been run on nano's core.
  **That is the decisive open question for any path that retires Mini.**

### 3.5 Store — **ALIGNED-DIFFERENT-SHAPE**
- Same meaning: log of Turns, checkpoint = a World at a height, MAC-tagged records under a Store key, reopen =
  checkpoint + fold of the suffix, a lost tail is never invented.
- Mini: SQLite (`durable_log`, `durable_checkpoint` keeping the latest two, `archive_journal`), KMAC256 tags chained
  over the log root, an independent head anchor outside the Store, checkpoint every 64 [read: M:DURABLE-STORE.md].
- Nano: flat framed segment (group commit, one fsync per batch), a sealed whole-World base written off-loop and
  amortised to O(appended bytes), a fixed-entry MAC'd index (open reads one entry), named open faults (`missing FILE`,
  `foreignSegment`, `foreignOrigin`, `tailTooManyTurns`), a shape stamp that refuses old shapes, export/import as the
  one carry decision [read: HOST-4, 14, 18, 20, 22, 25, 30, 33, 35; `gates/waste.tsv`].
- **Nano is better measured**: every cost is a pinned ratio that may only fall (e.g. `open bytes-read-per-record
  1.007`, `fsyncs-per-batch 1.000`, `seal base-bytes-net-of-growth ≤ 4` in the growing and the steady World)
  [read: `gates/waste.tsv`]. Mini's growth is a wall-clock journey step (G). **Mini is better at independent
  continuity**: the head anchor outside the Store; nano's nearest equivalent is the backup order fact (HOST-32/37)
  [inferred]. HOST-4a lists what SQLite gave for free that nano now owns itself [read].

### 3.6 Carry — **DIVERGED on purpose**
- Mini keeps **history** continuous across a runtime change: a separate carry verifier re-runs the retained old
  executable to verify the edge [read: M:CARRY-VERIFIER.md].
- Nano carries **state only**: `host export` (the folded World) → `host import --digest` = genesis under a new
  origin whose World is the old cells re-sealed; ids are kept, so a carry changes no authority (KERNEL-40); "every
  signature over old bytes is NOT carried, so history is never carried" [read: CHARTER law 1, OPS-1, KERNEL-29,
  PROTOCOL-35/36].
- Judgement [inferred]: nano's carry is far simpler and fits the greenfield doctrine, but an outside party can no
  longer verify the old history through a carry. If that property is ever wanted (audit across epochs), it is a
  KERNEL design item, not a Store one.

### 3.7 Members, keys, grants — **ALIGNED-DIFFERENT-SHAPE**
- Both: enrolment by a sponsor; an independently generated newcomer key; pre-rotation, where a stolen daily key
  cannot rotate; observation needs authority; grants survive a law change; a resource can lock its own management
  (J5/J7/J8 encode these decisions [read: M:docs/JOURNEY.md]; nano rows `journey`, `laws`, `rotate` restate them
  [read]).
- Nano: identity is a member cell with a stable id and a rotating key; one grant kind with a chain to the owner and
  attenuation (`grantWidens`); invoke is owner-gated like write (KERNEL-25); public grants to `anyone` are used but
  never re-delegated (KERNEL-26); following the log is itself a World grant rooted at genesis (KERNEL-20/21)
  [read]. Mini: capabilities as a per-cell slot list (`caps`) [read: M:`Kernel/State.lean`], plus seats and
  invitations.
- **Gap in nano:** Ed25519 only. Mini's verifier already handles ML-DSA and sshsig [read: M:verifier tests];
  nano's CLIENT-11 hybrid is "NOT IMPLEMENTED" [read].

### 3.8 Value / ledger — **ALIGNED-DIFFERENT-SHAPE**
- Same meaning: per-denomination conservation as an equality, issuer wells at minus supply, a transfer cannot
  overdraw [read: M:`Kernel/State.lean` header; N:LEDGER-2/3].
- Nano adds floors (credit lines as floor transfers, LEDGER-4) and a one-nullifier escrow (LEDGER-6/10), and puts
  conservation inside `World.admit` itself (`notConserved`, `belowFloor`) [read]. Mini keeps conservation as a
  property of legs over Book cells (`TurnCensus.step_conserves`) and has the external pay rail (Solana
  watcher, pay-to-enrol, tariff) [read: M:`Kernel/World.lean` header, M:README Payments row]. **Nano's kernel
  placement is better** [inferred: one check, every turn]; **the pay rail is MINI-ONLY**.

### 3.9 Hosting — **ALIGNED in intent, different scope**
- Same rule: the model or provider key never reaches a process that parses untrusted bytes; grain phase is World
  state, not outside truth [read: HOSTING-0; M:README split tenancy row].
- Mini has SPK packaging, running apps, a supervisor restart, export/freeze/restore, Discord, and Hermes in a room
  [read: M:README]. Nano has a lifecycle package generated from an edge list, a controller that tails the Store, a
  launcher that spawns only through the sandbox crate, and a TLS keybroker that meters allowances read from the
  World [read: HOSTING-3..24; synthesis]. No app has run on nano [inferred: no row or evidence names one].

## 4. Journeys and rows

### 4.1 Mini runner rows (28) → nano rows
| Mini row (M:`journey-rows`) | nano row (`replaces` field) | fidelity [inferred unless marked] |
|---|---|---|
| journey: J0–J5 | `journey` | full; adds a raced stale write and public grants |
| journey: J6 | `reopen` (also `hostupgrade/REOPEN`) | full |
| journey: J7, J8 (+ J13 law clause) | `laws`, `lang-journey` (J7 law) | full for the World facts; Mini's J13 refusal names a Pred clause, nano names `lawDenied law "label: reason"` |
| journey: JROT, JROTL | `rotate` | full |
| journey: JAUDIT (+ jstoreaudit) | `audit` | stronger: re-derives every Turn from its event |
| journey: JRLANE, JGATE, seat steps | — | none |
| welcomecontinuity | `journey` | partial |
| objective | `lang-journey`, `bounty` | the install → create → invoke shape only; Mini's 13 refusals are front-end replay refusals that cannot exist in nano |
| activity, seats, call, send | `bounty` (also `well` for seats) | **thin**: nano has no activities, seats or sends; the bounty restates an escrow with a method-triggered transfer |
| bounty | `bounty` | full at the World level |
| hermes (M5, J14) | `hermes` | partial: lost-reply settlement + grant write; the model provider is HOSTING's cargo row, not this row |
| m6grain | `grain` + `cargo:launcher:grain` | lifecycle and authority full; no SPK app |
| jpay (JPAY1–4, 6) | `pay` | **thin**: a once-key transfer; no watcher, no pay cell, no enrol-by-paying |
| births, growth (G), perf | `bar` | liveness deadlines only (5 s / 60 s are `hang` thresholds, not THE BAR); THE BAR is `scripts/bar.sh`, unjudged [read: row doc, PERF-1] |
| hostupgrade | `reopen`, `carry` | different meaning (re-genesis, not an epoch reopen) |
| rooms, domain, upgrade, objectrecord, sshe2e, m3, m4, m7, m8, fleetsign, exchange, chargedfailure, jserve | — | **no row** |

### 4.2 Mini `journey.sh` STEPS with no nano row (grouped)
K4 (32 typed fields); J12X (malformed requests survive); KC (clock); KT (tail bound); JJ (joint index); KCH/KCHR/KCHC
(channels); K10*/K11/K12* (rooms, streams, index, marks, element tree, history, links, render, transclusion); WEB; JLI
(law inheritance); KTPL (templates); J15/J17 (story, credit); JPRIV1, JP2, JDISCLOSE (privacy); JN2/JN3/JN3P/JN5
(Nock); JSYNC; M3/M4/M7/M8; BD (bind); J12/J12W/JNAMES/JDV/JPD (documents); JJOB1/JJOB/JJOBM (compute jobs); KCL
(field closure); J12A (affordances); JCHAT; JINSPECT; JLS (law sat); JPAYE1–3; JSERVE. **KW → `well`** and
**THIN → `thin`** are the two non-core steps nano does restate. [read: M:`journey.sh` STEPS; N:`Protocol/Rows.lean`
`replaces`]

### 4.3 nano rows with no Mini journey
`paging` (log pages, HOST-17), `coldCatchUp` (two windows behind, PROTOCOL-19), `inflatedHeight` (man in the
middle, PROTOCOL-27), `forgotten` (lookup after the journal prune is `uncertain forgotten`), `thinStale`,
`wrongWorld` / `wrongWorldRead` (cross-World replay, found against nano's own host), `carry` (OPS-P1). [read]
Each answers a failure Mini did not test, for example a whole-log single frame or replay across Worlds.

## 5. Honest state

### 5.1 What Mini does end to end that nano cannot do today
- A member-facing product: shell, documents (new/show/append/edit/link/backlinks), boards. Mini's README marks these
  **deployed** on a public node from the 10-01 candidate [read: M:README line 69]. The brief says nothing is
  deployed now; I did not check the node [inferred: treat as "was deployed"]. Main at `4795b657` failed J5/J8/JROT
  on 10-04 [read: same row].
- Rooms, invitations and the workroom template on development worlds (J15, J17); SPK apps installed, started,
  restarted after SIGKILL and exported (44/44, 10-01); Hermes in a room against a scripted provider; Discord against
  a simulated Discord; a pay journey on fixtures; four agreement replicas on one host [read: M:README Honest state].
- Authored `.obend` programs with sharing, polymorphism, activities, reflection and upgrade with migration, admitted
  natively by re-execution (row `objective`, 17 rows PASS at `4795b657`) [read].
- Known red at the spec commit: a fixture waiting on codec-shape charge encodings, one uidmap-dependent row, one
  JPAY row, the hbox-only upgrade artifact [read: SESSION-SYNTHESIS-20261017 "Backlog"].

### 5.2 What nano has that Mini does not
- **One admission path with named theorems** (follower reaches the host's World or exhibits a collision; storage
  and value conserved as equalities; every live grant rooted at genesis), all in the default build, with a
  tree-wide axiom census and 0 `sorry` [read: N:README; SIZE.md]. Mini's Core4 proofs are opt-in, and its census is
  still producing defects (23 open "census defect" tasks from the last 3 days) [read: cv].
- **Rows with plants over real sockets:** each row names a mutation that must turn a named line red, and a row
  without a driver is PENDING, never PASS (PROTOCOL-10) [read]. Mini's runner rows are scripts judged by exit code
  and `journey-result.json` [read: M:`journey-rows`].
- **Deterministic simulation**: 64 seeds under deployed parameters, 12 refusal kinds planted; host sims with crash
  cuts at every byte, fuel restarts, a second writer, foreign segments, forged bases [read: N:README].
- **Lean decides, Rust moves bytes**, measured: the Rust client is 1,864 lines plus a generated table; Ed25519 is
  verified in Lean [read]. Mini's Rust is ~292K lines, and signature verification is a Rust executable
  [read], against its own 08-09 rule that native code returns bytes, never a verdict [inferred tension].
- **Commit gates that refuse** (layer ownership, size ratchet, def/proof split, TCB table, vector immutability,
  the runs table on every landing) [read: GATES-*]. Per memory `minted-fail-open-gate-class`, Mini's gates report
  and none blocks [read: MEMORY.md index].
- Pinned **waste ratios** for every hot operation, which only fall [read: `gates/waste.tsv`].

### 5.3 Is nano "going well"? [inferred, from the record]
Yes, on velocity and quality per line: 405 commits in about 1.5 days, 21/21 rows, every decision written with
critique and meta-critique (10,477 lines of `decisions/`). Three cautions:
(1) the README on main still says "eleven rows … five pending … INCOMPLETE", which is stale against 21/21 [read], so the
docs lag the gates; (2) several rows' `replaces` lists claim more Mini rows than their bodies exercise (`bounty`
claims activity/call/send/seats/objective; `pay` claims JPAY1–6); (3) nano has not yet met the hardest Mini
requirements: remote friends over ssh, a model-backed resident doing work, an app, and THE BAR judged on a quiet box.
The charter's own meta-critique warns that phase ordering can be chosen to avoid the hard part, and LANG-1 admits
this about activities and reflection [read].

## 6. Three paths (costs are rebuild work; nothing deployed needs to be kept)

### (a) nano replaces Mini's core; Mini's product layers move onto it
- **Work:** (1) language: either extend nano's core with what the products need (sharing, or a per-run memo;
  recursive data such as lists; something to replace activities, for example defunctionalised state machines in
  object state, which is what LANG-6 already prescribes; polymorphism stays in an authoring tool), **or** write an
  `.obend` → nano-core compiler that does C4 linearisation and template instantiation offline (LANG-0 sends the
  front end to the client). (2) Re-express each product feature as nano packages plus at most a few new `Body`
  kinds: rooms (a parent is a ROM slot, per K2(i)), documents, chat, seats, the pay rail (a watcher outside, credit
  through `credit`), fleet. (3) Rewrite Rust clients against nano's 6-op table; Mini's 167-opcode `mini` cannot be
  reused. (4) Re-genesis every world (free).
- **Order of size** [inferred]: Mini's product is roughly Kernel receivers (~205K lines of Kernel, mostly
  receivers) plus resource-client/spk-host (~225 Rust files). Restated at nano's density (about 10× smaller), that is
  tens of thousands of lines, several lane-weeks, gated by the language question in §3.4.
- **Risk:** the language cut proves wrong for real applications (the exponential no-sharing case, no recursive
  data), and nano reintroduces the heap machine it deleted.

### (b) nano becomes a component inside Mini
- Which component could be swapped in, and through what interface:
  - **Codec / crypto library** (`Codec/`: StreamCodec with canonicity, cSHAKE/KMAC, pure-Lean Ed25519): Lean core +
    Std only (GATES-1), so it imports cleanly. Mini would replace its digest/codec code and the Rust signature
    helper. Cost: moderate, and a real win.
  - **Store** (`Host/` framed log + base + index) under Mini's Host: the interface is `World.fold` over a Turn codec,
    and Mini's Turn and World codecs differ (typed Registry, guarded legs, lanes). Cost: the store must be generic
    over Mini's Turn, which nano's HOST is not built for (it imports nano's Kernel) [inferred].
  - **Kernel** (`World.admit` + `Receive`) inside Mini: Mini would then hold two Worlds. That breaks nano's law 1 and
    law 11 and is exactly the twin class both repos spend effort deleting [read: CHARTER].
- **Verdict:** (b) only makes sense at the library level. At kernel level it is (a) under another name, or a twin.

### (c) separate: nano is the substrate, Mini the spec, until nano covers Mini
- Already the charter's arrangement [read: CHARTER "the spec is … the journey ROWS"]. Cost: Mini and nano both
  accrue work. Mini's 429 open tasks keep growing (44 in 3 days), and every Mini fix that is not a spec
  clarification is spent on a tree slated to be the battleground [inferred].
- Discipline it needs: Mini changes only where a journey clarifies the spec; product lanes target nano rows.

### Recommendation [inferred]
**(c) now, converging on (a). Do (b) only at the library level, and only if Mini must ship something before (a)
lands.** Freeze Mini to spec-only (journeys and design docs); triage the 385 older Mini tasks as "spec" vs
"Mini-implementation", and drop the second kind. Make the next nano epoch the language decision, measured: port
**one** real Mini `.obend` application (CappedTally, ReviewBase, or a `world/market` settlement) to nano's core, with
its waste ratio pinned.

**Triggers.**
- **Flip (c) → (a)** (retire Mini's core, re-target the product) when both hold: (i) THE BAR passes, judged on a
  quiet machine over sockets, with two friends where one is **remote over ssh** (CLIENT-12 built, `sshe2e`
  restated) plus a hosted Hermes resident doing model-backed work through the keybroker; (ii) the one-app port above
  runs without bringing back a heap machine or activities, or it shows exactly which extension is needed and that
  extension lands with its theorems.
- **Flip toward (b)** (lift `Codec/` + Ed25519 into Mini) only if a Mini deployment date is set before (i) can be met.
- **Flip against nano's language** (restore call-by-need or activities) if the one-app port hits the LANG-2
  exponential case or needs cross-turn suspension that defunctionalised state cannot express. That is a LANG
  decision inside nano, not a reason to keep Mini.
