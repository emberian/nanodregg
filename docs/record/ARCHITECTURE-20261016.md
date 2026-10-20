> record copy of redregg/work/ARCHITECTURE-20261016.md, 2026-10-16; the lane logs stay in redregg

# ARCHITECTURE — Mini's layers, interfaces, data model and TODO, read from the code

ARCH-MAP (scholar), 2026-10-16, for Ember's question: *"what IS our core architecture? what are all the layers and
modules of our software, what are the interfaces between them, what protocol functionality shows up where, what's the
core heart of the server's data & persistence model, … all the functionalities at each point, what the todolist looks
like at each one."*

**Tree.** GitHub `main` = **2c27b08b** (ROOT fast-forwarded main 7ffd6524 → 2c27b08b on 10-16 20:45Z and retired
`next`; `work/resume/STALL-WATCH-20261007.md:199`). Read from a detached checkout; lane tips read with
`git show gh/lane/<name>:<path>`. Nothing was built or run.

**Tags.** **READ** = read at the cited `path:line` on main 2c27b08b. **LANE** = read on the named `gh/lane/*` tip.
**DOC** = a doc says it (the doc is cited; the code was not checked). **ASSUMED** = my inference. A bare `path:line`
is READ. Four read-only sub-scholars swept the Rust crates, deploy/scripts, the lane logs and the Objective Bend
compiler; their findings are folded in under the same tags (they quoted path:line; I spot-checked the load-bearing
ones).

**Size, measured (READ, `wc -l`).** Lean 576 k lines in the libraries (Kernel 205 k, Compiler 102 k, Theory 86 k,
Selvage 78 k, Assurance 60 k, Host 38 k), 1,625 `.lean` files. Rust 281 k lines in `native/` (resource-client 114 k,
grain-runtime 56 k, spk-host 54 k, private-backend 26 k, the rest under 6 k each) plus 9.6 k in `prover/`. The Host
executable's import closure is **776 modules** (Kernel 405, Compiler 158, Theory 107, Host 87, Selvage 12, Pred 7;
`scripts/gates/host-closure.pin`). ATLAS's budget was ≤ 290 k for everything (`ATLAS.md:12`).

**Stale docs to not orient from.** `GOAL.md` is a trail of the August/September proof-system campaign (READ
headings); `ATLAS.md §7` is the founding carve, not the current tree (no `Distributed/`, `Apps/`, `Deos/`, `rust/`
exist; `Effects/` is 2 files). `docs/OVERVIEW.md` and `docs/HP-DESIGN.md` do not exist on main; HP-DESIGN is on
`lane/hp-design` 4329b99c (LANE, read in full). The live navigation page is `docs/README.md`.


## 0. Headline findings (details in the sections cited)

1. **Two state machines, joined by a theorem, not by shared code.** The Host persists `IntentRecord`s and runs
   `DurableDataIntent.execute` over a `DataSnapshot`; the kernel `World`/`Turn`/`World.admit` is run only by the
   follower exe, the totality runner and proofs. `deployed_refines_step` is proved; **`host_submit_is_step` — "what the
   Host committed is a World step" — exists only in a docstring** (`Kernel/HostRefinesWorldCore.lean:75-99`). The
   relation does not bind the log chain (`head : ∃ r`) or parentage (`parent = none`). TURN-LOG (lane/turn-log
   dbb4f0f4, steps 4a → CHARGE → guards → a0 → step 2 → step 1 → 4b → R5b) is the collapse (§5.1, §6.1).
2. **The persistence heart is sound in shape and wasteful in approach.** One SQLite file, MAC-tagged log with a v4
   trailer (root, chain, MMR frontier, index root), MAC'd checkpoints whose root is recomputed, a content-addressed
   `StoreEpoch` that refuses old Stores by name; but a store-helper child process per call, `List UInt8` everywhere
   (4,798 lines vs 329 `ByteArray`), 0 runtime assertions, 56 `partial def`, and 11×–6,700× the necessary work per
   operation (DOC WASTE-MODEL). HP-1/3/5/6/2/7 are the designed fix; only HP-1 (lane) and HP-6 (inside lane/turn-log)
   exist (§5.4, §6.2).
3. **The protocol surface is wide**: 184 active Host opcodes in 25 owner families (186 allocated; one JSON registry
   generates the Rust constants), ~120 Host CLI verbs that duplicate session ops one-shot, 12 consent frames, ~100
   `mini` verbs, 14 SPK broker verbs; 51 `NativeAdmission` constructors and 70 versioned/legacy modules (§4, §6.10 H1).
4. **"Rust decides nothing" is not yet true.** 281 k lines of Rust, with at least six Rust-side decisions or codec
   twins that no test holds to Lean: the hiding root's hand cSHAKE/KMAC (`hiding.rs`), the v4 retry selector
   (spk-host), the sealed-market clearing allocation, the key broker's authorization, the thin-consent stream encoder,
   the delegation pre-check; plus 50 copies of a decimal parser and three copies of the socket envelope (§6.10 R).
5. **Mainline state.** main = 2c27b08b (= the retired `next` v3.2: gate red=0, no landing verdict). Three known-red
   rows (fleetsign, JPAY6, m6grain), each with its fix on a lane (consent-model 1e3ad928 for JPAY6, spk-ns 5919eb8b for
   m6grain). The integration branch `lane/v4-next` b5fd9ee1 is red at `DurableReceiverCore.lean:1655` (Part A ×
   turn-log 4a `Loaded` field clash). Nothing proof-system is in admission: `witnessed` lowers to constant 0, but 12
   Selvage modules still sit in the Host's 776-module import closure (§2, §6).

## 1. The one-paragraph answer

**Mini is a single-writer, re-execution-checked shared world.** Its *meaning* is a Lean kernel model — a `World`
(a finite map of typed cells plus one system cell holding journal, head/chain, retired, parent, spent and allowance,
`Kernel/World.lean:264`) advanced by exactly one fail-closed transition `World.admit` over a deterministic `Turn`
(`:370`, `:607`) — with Objective Bend as the authored language whose checked core terms become installed laws and
invocable packages (`Theory/ObjectiveBendOpenRecursion.lean:21`, `Kernel/ObjectiveActivity.lean:2125`). Its
*running server* is one Lean process per Store, `minidregg-host CONFIG stdio` (`Host/Main.lean:6650`), which holds a
verified opening of the Store (`Session` → `Opened` → `Loaded`), answers length-prefixed opcode frames, and commits by
building a `DataIntent` (post bytes + roots, read guards, nullifiers, exact charge, event), executing it against a
`DataSnapshot`, and appending one MAC-tagged `IntentRecord` to SQLite through a Rust store helper. **The two are
joined by a refinement theorem (`deployed_refines_step`), not by running the same code: the Host does not call
`World.admit` today**; TURN-LOG (in flight) makes the Turn the log entry and the World the Host's state. Nothing is
admitted by proof: `witnessed` compiles to constant false (`Compiler/PredCompile.lean:602-603`), and every
computation is checked by re-executing it. Around the Host: a resident **consent provider** (a second Lean
executable, `minidregg-client-consent`, holding the member's own verified prefix and refusing to sign anything it
did not re-derive), the Rust **client** `mini` (custody, signing, transport, workspace; it "decides nothing"), the
Rust **SPK/grain** hosting layer (bwrap sandboxes, a user-mode broker, per-app uids) and the **pipeline** (warm-base
lanes, an umbrella gate, journey rows, a baseline-relative landing verdict).

**One request, end to end** (an ordinary signed write; READ unless marked):

1. **Client observes.** `mini` signs a local intent (consent frame 220), sends op 4 `challenge` (intent → observation
   challenge, `NativeHost.challengeWireLoaded`, `Kernel/NativeHost.lean:986`); the consent provider checks the
   challenge against its own admitted prefix before custody signs it (frame 221, `NativeClientConsent.checkObservation`,
   `Host/ClientConsentCore.lean:322-346`); op 10 (pure codec) assembles the signed observation.
2. **Plan.** Op 1 `prepare` → `NativeHost.prepareAuthorizedLoaded config opened light bytes : IO (Except Refusal
   SigningPlan)` (`Kernel/NativeHost.lean:829`; `Host/Main.lean:2058-2064`); consent frame 222 re-derives the plan
   headers (`checkIntentPlan`) before custody signs. (Op 5 `query` reads a view the same way.)
3. **Assemble.** Op 11 (a pure codec frame, no Store) → `NativeHost.assemble plan signatures` → `callCodec` bytes
   (`Host/Main.lean:2036-2041`).
4. **Submit.** Op 2 → `callCodec.decode` → `NativeHost.submitDisclosedWith` → `submitLoadedVia`
   (`Kernel/NativeHost.lean:3057`), which routes the `SignedCall` (`birth | invoke | install | delegate | revoke |
   renounce`, `Compiler/NativeHostCodec.lean:154`) to its receiver. The receiver re-checks signature (native verifier),
   current authority, law and funding against the session's opening and emits a `DataIntent`.
5. **Commit.** `DurableCheckpoint.prepare` runs `execute` (journal lookup first, so an exact retry replays; then
   preflight; then install) → `prepareAppend` builds `Entry {record = DREGG.DURABLE.LOG/v2 IntentRecord, tag = {worldRoot,
   chain, frontier, indexRoot} ‖ KMAC}` plus MMR/index node rows (`Compiler/DurableReceiverIO.lean:158-196`) →
   `Transport.append (h+1)` CAS in one SQLite transaction → exact readback → every 64 records a MAC'd checkpoint
   (`publishAfter`, `:198-228`).
6. **Reply.** The outcome frame (`outcomeCodec`) carries the receipt (`acceptedCount`, `worldRoot`, transaction and
   event ids) or a named refusal under opcode 255 (`RequestRefusal.frame`); an append whose readback fails is
   `uncertain`, never "refused" (`publishAfter` `.uncertain`). The client retries by op 3 `lookup` with the same call.
7. **Afterwards.** A follower can export the Store as a Turn log and fold it with `World.admit` in a second process to
   the same root (`Host/TurnLogFollower.lean`, `TurnLog.followFrom_sound`); the operator `audit` re-admits every signed
   ingress from genesis (`NativeHostReplay.verifyLoaded`).


## 2. LAYERS AND MODULES

One row per layer. "Owns" = the decisions and state it is the one home of. "Must never" = the rule the code or its
headers state (cited), or that a design doc in force states (cited).

| # | layer | modules (files / dirs) | owns | must never |
|---|---|---|---|---|
| L1 | **Kernel model** (spec of state and transition) | `Theory/Store.lean` (Layout, Op, Patch, run/ValidFrom), `Kernel/World.lean` (World, Turn, Leg, History, Reject, admit, fold, ~60 theorems), `Kernel/DeployedBridge.lean` (`deployedR`, one Wire per kind), `Kernel/DeployedHistory.lean`, `Kernel/WorldRoot.lean`, `Kernel/WorldRootCache.lean`, `Kernel/TurnOfIntent.lean`, `Kernel/HostRefinesWorld{,Core}.lean`, `Kernel/TurnLog.lean`, `Kernel/DeployedTurnCompact.lean`, `Kernel/DeployedTurnCodec.lean`, `Kernel/WorldSystemCodec.lean`, `Kernel/CellTable.lean`; registry `Compiler/CanonicalCellRegistry.lean` (19 kinds) | what a cell, a turn, a refusal and a history mean; the one transition; the frame/ROM/WF/journal/head laws | hold post bytes, roots or signatures in a Turn ("It carries no post bytes, no post roots and no signatures", `Kernel/World.lean:20`); decide authority ("`admit` decides none of them", `:362`); keep an index as state ("Indexes are not state", `:66`) |
| L2 | **Deployed engine + durable Store** | `Kernel/DurableDataIntent.lean` (DataIntent, DataSnapshot, execute), `Kernel/DurableReceiver.lean` (IntentRecord, Seed, Image, replay), `Kernel/DurableCheckpoint.lean` (State, resume, prepare), `Kernel/DurableCommitProtocol.lean` (crash model), `Compiler/DurableReceiverCore.lean` (Entry, Transport, Loaded, load, extendFrom), `Compiler/DurableReceiverIO.lean` (judge, prepareAppend, publish), `Compiler/DurableCheckpointCodec.lean` (frames, MAC, StoreEpoch), `Compiler/DurableHistory.lean` (MMR, verifyAt), `Compiler/DurableIndex.lean` (one index trie), `Compiler/DurableLogTags.lean`, `Compiler/DurableServed.lean` + `Kernel/NativeHostLight.lean` (light opening), `Compiler/NativeCoprocess.lean`; Rust `native/hyperdocument-link-sqlite-store` (SQLite v5 schema, MINIANC2 anchor, `serve` loop) | the persisted bytes and their meaning; open/append/seal; MACs; the epoch; at-use verification of old records | let the helper assign meaning ("the native helper stores opaque bytes, appends entry h + 1 only while the head is h, and assigns no meaning to anything", `Compiler/DurableReceiverCore.lean:7`); migrate ("there is no migration: re-genesis", :19); trust a checkpoint's root ("Recomputed on open, never trusted", `DurableCheckpointCodec.lean:604`); return an unverified history byte (`DurableHistory.lean:24-28`) |
| L3 | **Host / server** | `Host/Main.lean` (9,163 lines: `run`, `serveSession`, `serveFrame`, `dispatchSession`, `pureCodec`, `serveCodec`, `objectKernelOperation`, ~120 CLI verbs), `Kernel/NativeHost.lean` (3,351: prepare, challenge, submit*, lookup), `Kernel/NativeHostContext.lean` (Config, Opened), `Kernel/NativeHostSession.lean` (Session, start, refresh), `Kernel/NativeHostReplay.lean` (4,590: NativeAdmission ×51, verifyLoaded = audit), `Kernel/NativeHostServed.lean`, `Kernel/NativeHostGenesis.lean`; ~400 receiver/controller modules (`Kernel/Application*` 146, `Fn*` 45, `Pay*` 34, `Objective*` 32, `Joint*` 16, …); `Host/*` (123 files: authoring, inspection, JSON, consent cores, benches); `protocol/host-operations.json` | the live decision for every request: signature (via the native verifier), current authority, law, funding, replay identity; the outcome frame | admit by proof (`witnessed` ⇒ constant 0, `Compiler/PredCompile.lean:602-603`; `docs/ZK.md:3` "Today Mini admits by proof: never"); answer a frame twice or desynchronise the pipe (`serveFrame` doc, `Host/Main.lean:2606-2612`); read operator pins during replay (`Kernel/World.lean:65`) |
| L4 | **Compiler / Objective Bend** | `Theory/ObjectiveBend*.lean` (46 files: Core4 `Term`, types, typing/check, demand machine, proofs), `Compiler/ObjectiveBend{Parse,Elaborate,FrontEnd,C4,Contract,Publication,SourceArtifact,Law,TermWire,…}.lean` (28), `Compiler/ObjectiveSourcePackage.lean`, `Host/ObjectiveBendFrontEnd.lean`, `Host/ObjectivePackageAuthor.lean`, `Host/ObjectiveInvocationQuote.lean`, `Kernel/ObjectiveActivity.lean`, `Kernel/ObjectiveCall.lean`, `Kernel/ObjectiveAdmittedTurn.lean`, `Kernel/ObjectiveBendNativeAdmission.lean`, `Kernel/ObjectLaw.lean`, `ObjectiveProofs.lean`; C backend `Compiler/ObjectiveBendEmitC.lean` + `native/objective-emit/runtime.c`; plus the `Pred` algebra (`Pred/Core.lean` …, 7 of 10 in the Host closure) and `Compiler/PredCompile.lean`/`Air*` (policy lowering on the deployed path) | the language, its checked core, the package/artifact identity (pin), the law compiler `LawExpr → Pred`, bounded execution | install anything not re-derivable from source (the kernel re-runs the front end: `Program.runs_front_end_output`, `Kernel/ObjectiveActivity.lean:1264`); let the C runtime decide (differential only, `runtime.c:1-13`) |
| L5 | **Consent provider** | `Host/ClientConsentCore.lean` (serve, frames 220-233), `Host/ClientConsentSession.lean` / `…SpecializedSession.lean` (exes), `Host/ObjectiveConsent.lean`, `Host/NativeLifecycleConsent.lean`, `Kernel/NativeClientConsent.lean`, `Kernel/NativeThinConsent.lean`, `Kernel/NativeSpecializedConsent.lean`, `Kernel/ConsentAnchor.lean`; Rust side `native/resource-client/src/client_consent.rs` (spawn, resident `r-<binding>.sock`, anchors under `~/.mini/consent-anchors/`) | what custody may sign: only headers it re-derived from its own admitted prefix | sign proposed bytes it did not reconstruct ("The remote endpoint proposes bytes; it never chooses what custody signs", `Kernel/NativeClientConsent.lean:3`); copy protected source state to a client (:7); fall back to signing what thin consent could not show (`Host/ClientConsentCore.lean:351`) |
| L6 | **Client (Rust)** | `native/resource-client` (bin `mini`, 114 k lines: `main.rs` dispatch, `transport.rs` frames/serve/socket filters, `workspace.rs` (8.8 k), `client_consent.rs`, `activity.rs`, `seat.rs`, `hiding.rs`, `pay*.rs`, `roomkey.rs`, `private.rs`, `shell.rs`, `fleet*.rs` …), `native/mini-sdk` (intent codec, signer Ed25519 + ML-DSA-65, lean-codec dlopen of `libminidregg-intents.so`), `native/mini-sdk-ts`, `native/mini-keys` (key broker, SO_PEERCRED roles), `native/credential-signature-verifier`, `native/discord-entrance`, `native/pay-watcher`, `native/inference-scheduler`, `native/compatible-upgrade-custody`, `native/private-backend`, loose `native/{hybrid_kem,crypto_transit,pinned_execution}.rs` | custody (keys, attempts, retries), transport (`serve` binds the socket and supervises one Host child), the workspace on disk, client-side encryption | decide semantics ("Rust decides nothing", HP-DESIGN §2; AGENTS.md: "Lean owns semantics and admission; Rust provides the physical client/custody boundary"); decode a refusal frame itself (it asks the Host with op 8 "outcome", `main.rs:1343-1369`, Rust-agent READ) |
| L7 | **Codecs / wire** | `Compiler/Tower256ConcreteBackend.lean` (`StreamCodec`, `fixedStream`, `digestStream`, `Digest256`), `Theory/IndexedProgram.lean` (`LawfulCodec`), `Compiler/PersistedCodecTags.lean` (+Registry, Census; 637 tag lines), `Compiler/NativeHostCodec.lean` (SignedCall, Outcome, Receipt), `Compiler/NativeObservationCodec.lean`, `Compiler/RefusalReason.lean`, `Compiler/NativeProtocolFrames.lean`, `Compiler/FnWire*`, `Compiler/StoreCodec.lean`, `Kernel/Contracts/Intents.lean`; `protocol/host-operations.json` + `scripts/host-operations.py` + generated `native/host-operations.rs`; Rust mirrors (§6.9) | canonical bytes and tags for everything persisted or sent | reinterpret an old shape (frames of retired versions refuse: `v1_record_refused`, `retiredOutcomeFrame*`); prove canonicity by re-encoding (W8; CODEC-SHAPES deletes it) |
| L8 | **Hosting / sandbox** | `native/spk-host` (54 k: broker, hostd, sandbox.rs `FIXED_ARGS`, resident launch, lifecycle_v3/v4 natives, spawn_gate, volume helper), `native/spk-rpc` (pinned Sandstorm capnp), `native/grain-runtime` (56 k: Hermes/agent controller, control socket, credentials), `native/signed-api-path`, `deploy/spk-host` (install-user-world, spk-ingest, units), `deploy/grain-host` (bwrap wrapper, launch-gate, resolve-bwrap), `deploy/hermes*`, `deploy/candidate` (package.py roles, build.sh, run.sh), `deploy/{checkpoint,clock,pay,discord,shell}` units; Lean side `Kernel/ApplicationGrain*.lean`, `Kernel/ApplicationLifecycle*` (66 files) | process isolation (bwrap profiles), the grain lifecycle's physical half, per-app uids, volumes, the candidate format | admit semantically ("Semantic admission is exclusively a signed call to the native Lean host through `mini`", `native/grain-runtime/src/main.rs:1-2`, Rust-agent READ); run root daemons (the user-tenancy design: root only through the one-shot volume helper's seven verbs and newuidmap, `USER-TENANCY.md:28-37`, deploy-agent READ) |
| L9 | **Pipeline / gates** | `scripts/pipeline/` (landing.sh, run-gate-burst.sh, merge-gate-checks.sh, publish-artifacts, journey-runner, journey-rows, required-rows, lib.sh slots, mk-lane, lake-shim …), `scripts/local-gates.sh`, `scripts/build-native-host.sh` (seats), `scripts/check-*.sh`, `scripts/gates/` (host-closure.pin, objective-manifest/, waste-model, …), `scripts/kern/`, `scripts/perf/` (workload, box.py), `native/resource-client/journey.sh` (+ `journey.d/`), `AxiomCensus*.lean`, `TokenCensus/`, `scripts/HypothesisLedger.lean` | what "landed" means: gate red=0, no new red vs main's baseline on the same box, required rows PASS | let a lane drop its own required rows (`required-rows` is read from main's tree, `:8-9`); judge on a busy box (births returns UNCONFIGURED, `journey-rows:633-637`); push (landing.sh "never pushes") |
| — | **Research (not deployed)** | `Selvage/` (152 files, 78 k: the proof system), most of `Assurance/` (154 files; only `EvaluatorAudit`, `NockDoorAudit`, `StoryLaw` enter `Deployed`), `ResearchWip.lean`, `Theory/{Bfv*,BendMasking*,Zkml*,Evm*,…}`, Compiler groups 2 and 6 (96 + 32 files, 14 in the Host closure via `PredCompile`) | — | enter admission (memory `project-no-proof-system-in-mini-admission`; yet 12 Selvage modules sit in the Host closure through `Compiler/Tower256CshakeMerkleController.lean:25` → `Selvage.BinaryLookup`, `Deployed.lean:14-17`) |
| — | **Vestigial / parallel** | vestigial: `Effects/` (2 files, imported only by the umbrellas; 0 modules in the Host closure), `Pred/CoordinationDial.lean`, `Kernel/State.lean` (not in the Host closure). Parallel turn carriers still in the Host closure: `Kernel/Turn.lean` (`structure Hyperedge`, :38), `Kernel/TypedCellHyperedge.lean`, `Kernel/MultiCellHyperedge.lean` (used by `HyperdocumentPublication`, `CanonicalResourceEffect`, `DurableCommitProtocol`) — a different turn shape from `World.Turn` | — | — |


## 3. INTERFACES BETWEEN LAYERS

Each boundary: the types and functions that cross it (signatures quoted), the wire tags, and the theorems that bind
it, with their honest status. **Status words**: *proved* (a theorem on main with the stated content), *stated-only*
(a statement in a docstring, no proof), *gate* (an executable check, not a theorem), *trust floor* (an explicit
premise: SQLite, OS, the host's own MAC, the native signature verifier, cSHAKE collision resistance).

### 3.1 Kernel model ⇄ deployed engine (the refinement seam)

- Crossing: `Turn.ofLoaded (B : Bridge R D) (H : History R TransactionId StableEvent D) (p : Loaded rootBytes) (intent :
  DataIntent rootBytes) : Except Refusal (DTurn R D)` (`Kernel/HostRefinesWorldCore.lean:408`); `Turn.ofIntent`
  (`Kernel/TurnOfIntent.lean`); `structure Bridge (R) (D) where codec : Codec R; key : StableNullifier → D;
  key_injective` (`TurnOfIntent.lean:540`); the deployed `bridge := ⟨Codec.ofWires decodeCell wireOf, digestKey,
  digestKey_injective⟩` (`Kernel/DeployedBridge.lean:240`).
- The relation: `SnapRepresents B snap height w` with fields `cells` (every cell's canonical bytes decode to the
  World's cell), `spent` (↔ consumed under the injective key), `journal`, `head : ∃ r, w.head = some (height, r)`,
  `meter` (all lanes but storage equal), `storage : snap.model.available .storageBytes ≤ w.meter .storageBytes`,
  `retired`, `parent : ∀ c, w.parent c = none` (`HostRefinesWorldCore.lean:383-399`).
- Theorems: `deployed_refines_step` (proved, :698), `host_trace_represents_fold` (proved, :719), `ofIntent_step`
  (proved, `TurnOfIntent.lean:1551`), `ofLoaded_eq` (proved, :419), `represents_rebaseD`/`confirmed_represents`
  (proved, :922/:961), `represents_logicalHeight` (proved, `Kernel/HostRefinesWorld.lean:27`).
  **`host_submit_is_step` is stated-only** (`HostRefinesWorldCore.lean:75-99`): no theorem says the receive path's
  actual commit is a World step. `Kernel/ObjectiveAdmissible.lean:137` `Admissible ob w t = {loaded, represents :
  DeployedRepresents loaded w, commit : CheckedCommit ob loaded t}` with `Admissible.turn_determined` (proved, :184)
  covers the Objective activity family only.
- Gaps the relation itself names: the chain is not bound (`head` is `∃ r`), parentage lives in authority plane 13
  (G-PARENT/T7), capability/key epoch/window are not in `DataIntent` (G-AUTH, `:66-69`), storage is `≤` not `=`
  (G-CHARGE; TURN-LOG CHARGE 7877e6e7 makes it `=`, LANE).

### 3.2 Host ⇄ durable Store (the native boundary)

- Crossing: `structure Transport` (`Compiler/DurableReceiverCore.lean:97`), `Entry {record tag : List UInt8}` (:59),
  `NodeWrite {space : Nat; key value : List UInt8}` (:72), `Stored {head; seed; checkpoint; entries}` (:91),
  `CasObservation = installed | alreadyPresent | conflict | uncertain detail` (:52). Implemented by
  `NativeConfig.transport` (:408) as argv verbs `durable-read | durable-append | durable-append-crash |
  durable-checkpoint | durable-init | durable-seed | durable-history | durable-checkpoint-at` (:216-392) to the Rust
  helper `minidregg-link-sqlite-store` (`native/hyperdocument-link-sqlite-store`), through
  `NativeCoprocess.output` — frames `u32 argc, (u32 len, bytes)*` → `replyTag, u32 code, u64 len stdout, u64 len
  stderr` (`Compiler/NativeCoprocess.lean:14-17`).
- Wire tags: `DREGG.DURABLE.SEED/v1` (+ the `StoreEpoch` label), `DREGG.DURABLE.LOG` byte 2, log trailer v4 under
  `logTagLabel = native_host_log_tag_v4`, `DREGG.DURABLE.CHECKPOINT` byte 3, `DREGG/NATIVE-HOST/CHECKPOINT-MAC/v1`,
  `…/CHECKPOINT-BODY/v1`, `…/MAC-KEY-ID/v1`, `DREGG/NATIVE-HOST/ARCHIVE-JOURNAL-TAG/v1`, head anchor `MINIANC2`.
- What the helper may decide: nothing. "the native helper stores opaque bytes, appends entry h + 1 only while the head
  is h, and assigns no meaning to anything" (`Compiler/DurableReceiverCore.lean:7`). It does hold the head anchor (fsync/rename/dir-fsync, `docs/DURABLE-STORE.md`
  write path) — a trust floor, not a theorem.
- Theorems: `publishAfter_conflict` (proved: a conflict reads/writes nothing more, `DurableReceiverIO.lean:238`),
  `Commit.tail_pinned`/`ordinary_preserves`/`Judged.tail_pinned` (proved, :82-116), `verifyAt_sound` (proved,
  `DurableHistory.lean:253`), `resume_sound` (proved, under the host's own MAC: `DurableCheckpoint.lean:225`),
  `execute_no_partial_data_commit` (proved, model; physical atomicity is SQLite's, `ImplementationRefinement` premise
  `DurableDataIntent.lean:492`). Gates: `coprocess-faults` (`scripts/kn2/coprocess-faults.lean`), `api-faults`,
  `kernel-transport` (merge-gate readers).

### 3.3 Client ⇄ Host (frames)

- Frame (READ `Host/Main.lean:2655-2689`, `Host/ClientConsentCore.lean:211-223`): **u32 little-endian length ‖ opcode
  byte ‖ payload**; replies use the same shape; any handler error is answered under opcode **255** with
  `RequestRefusal.frame operation error`; a poisoned session answers `unavailable "host session reopening"` and the
  process exits so `mini serve` restarts it (`serveFrame`, :2613-2653). Length bound
  `maxFrame = FnEvidenceCodec.maxHostFrameBytes = 2 · maxConsumerReportBytes + 262144`
  (`Compiler/FnEvidenceCodec.lean:88`) — a bound derived from the fn consumer report, which HP-1 moves to
  `Kernel/Bounds.frameBytesMax` (LANE).
- Outcome: `inductive Outcome | confirmed kind receipt | charged kind receipt cause | refused reason phase detail leaf
  | contention | unavailable detail | uncertain detail | absent` (`Compiler/NativeHostCodec.lean:320-330`), framed
  `DREGG/NATIVE-HOST/OUTCOME/v5` (`PersistedCodecTags.lean:608`; v1–v4 are kept as refusing frames, `:369-405`);
  `Receipt {transactionId; eventId; acceptedCount; worldRoot}` (`:287-294`); `RefusalReason` = malformed,
  unknownKey, staleRoot, badSignature, noGrant, revoked, outsideValidity, staleGrant, lawDenied, lawInputRange,
  operationRejected, conflict, undisclosed, tailBound, audienceTransition (`Compiler/RefusalReason.lean:56-83`).
- Calls: `SignedCall = birth | invoke (DeclaredResourceController.SignedCommand) | install | delegate | revoke |
  renounce` (`Compiler/NativeHostCodec.lean:154`) under `callCodec`; signing plans under `signingPlanCodec`;
  observations under `NativeObservationCodec.{challengeCodec, signedCodec, intentCodec}`.
- Theorems binding it: none end to end. The Rust side's codecs are hand-written twins of these (see §3.6 and §6.10 R-rows).
- How the client reaches the Host (Rust-agent READ, `native/resource-client/src/main.rs:1230-1376`,
  `transport.rs:1098-1150`): `process` routes pure verbs (author, inspect, signatures, observe-assemble, assemble)
  to the local **codec child** (`<host> <settings> codec` = `serveCodec`, one per process, `client_consent.rs:983-1058`);
  with `--socket`/`--remote` it uses `socket_process` (verb → op: describe 0, prepare 1, submit 2, lookup 3,
  challenge(-batch) 4, query(-batch) 5, profile 6, author 7, inspect 8, signatures 9, observe-assemble 10, assemble 11,
  dry-run 130, law-sat 150); otherwise **`local_process` (`main.rs:1245`) execs the Host one-shot** (`Command::new(host)
  .arg(config).args(arguments)`; a failing exit is "request status uncertain"). Over a socket the frame is wrapped
  in an envelope `[1|2] ‖ u32LE(config.len) ‖ config ‖ (v2: host_sha256[32]) ‖ op ‖ payload`, itself u32-LE length
  prefixed; reply byte 254 = the socket refused and never forwarded, 255 = Host refusal, otherwise it must equal the
  op. `mini serve` binds the socket (0600, sibling `.lock/.config/.mode`), seals the Host image and config into memfd
  copies on Linux and supervises `<host> <pinned-config> stdio` (`transport.rs:1222-1283, 1356-1449`). **There is no
  `<workspace>/SOCKET` file**: the socket path (or `ssh:DEST`, relayed by `mini socket-proxy`) is a field of
  `workspace.json` (`minidregg-participant-workspace-v1`, `workspace.rs:633-650`), which also pins `hostSha256` at
  init; `host_image_sha256` caches per file identity (dev, ino, size, mtime, ctime) and is skipped when the workspace
  pin answers, unless `--verify-host` (`main.rs:440-493`). The served socket refuses "host image pin mismatch"
  (`transport.rs:205-218`). Socket op filters `allowed_operation`/`allowed_operator_operation` re-list the route table
  (`transport.rs:306-616`), checked against `protocol/host-operations.json` by `scripts/host-operations.py`.

### 3.4 Client ⇄ consent provider

- Spawn: `<exe> <settings> stdio`, exe from pins / `MINI_CONSENT_HOST` / `host.with_file_name("minidregg-client-consent")`
  (`client_consent.rs:104-141`); resident by default (`MINI_CONSENT_RESIDENT=0` disables) at socket
  `r-<hex(binding[..16])>.sock`, started as `mini consent-resident --consent EXE --settings S` under setsid
  (`:380-425`). Frames as in §4.2 (u32 LE (len+1) ‖ op ‖ payload, `:78-95`). Anchors are files under
  `~/.mini/consent-anchors/` tagged `MINI-CONSENT-ANCHOR-CUSTODY/v1` (`:19`). Ops whose plans are re-derived through
  frame 224: 32, 36, 44, 48, 50, 52, 58, 66, 68, 70, 74, 78, 80, 82, 86, 92, 96, 103, 108, 113, 117, 123, 126, 140, 160,
  170, 183, 201, 206, 210, 215 (`:1093-1095`).
- Lean types crossing: `ObservationConsent config basis wanted intentSignature candidate` (private constructor;
  `derived : NativeObservationController.challenge … = .ok challenge`, `exactBytes : challengeCodec.encode challenge =
  candidate`, `Kernel/NativeClientConsent.lean:31-39`); `ConsentAnchor.Anchor`/`Basis`; `Session config =
  (target : Durable) × basis` (`Host/ClientConsentCore.lean:264-297`).
- Theorems: the private constructors make "only this module constructs consent" a type fact; Part A's
  `Kept.own_sound`/`atPrefix_own` are LANE (consent-model, in v4-next). Trust floor: "Signature validity remains the
  native verifier's existing assumption" (`NativeClientConsent.lean:11`). Known-red: fleetsign's "remote challenge
  differs from locally prepared intent" is this boundary (`NativeClientConsent.lean:55`).
- **The provider and the Host read the same Store through the same `Transport`** (`verifyInitial` →
  `DurableReceiverIO.loadChained config.transport`): consent is a second verifier of the operator's bytes, not of the
  Host's replies.

### 3.5 Host ⇄ native helpers and external programs

| helper | how | interface | READ |
|---|---|---|---|
| store `minidregg-link-sqlite-store` | resident `serve` via `NativeCoprocess` (`/bin/sh -c 'exec "$0" serve'`), child exec per call | argv verbs (§3.2); reply tag `MDCOPRC1`, BE lengths ≤ 64 MiB | `Compiler/NativeCoprocess.lean`; sqlite-store `main.rs:319-390` |
| signature verifier `minidregg-credential-signature-verifier` | same coprocess | `verify`, `verify-mldsa`, `verify-sshsig`; Lean calls `verify-sshsig` | `Compiler/CredentialSignatureIO.lean:119-139`; config `signatureBinary` |
| fn binary | `IO.Process.spawn` per poll/ack | `--fn consumer --frame ack <control> <cursor>` etc., bounded line reads | `Host/Main.lean:6118-6141` |
| joint-agreement-crypto | exec | `keygen`, `mac-keygen`, `session` | `Compiler/GenericSimplexNative.lean:16` |
| mini-sdk `libminidregg-intents.so` | dlopen of a Lean-built shared library | `@[export] minidregg_intent_encode`, `minidregg_intent_id_preimage` (`Kernel.Contracts.Intents`) | `native/mini-sdk/lean-codec/`, `lean_codec.rs` |

There are **12 `@[export]`** in Kernel/Host/Compiler (`Kernel/DomainEpochExport.lean` 7, `Kernel/FinalityGate.lean` 1,
`Kernel/NockEntry.lean` 2, `Compiler/Evaluator.lean` 2; READ grep). Every other Lean↔Rust crossing is a process
frame with a codec on each side.

### 3.6 Hosting (spk-host, grain-runtime) ⇄ Host

- spk-host calls the Host three ways (Rust-agent READ): exec `<host> <config> profile` (`grain.rs:1426`), exec
  `<host> <config> <cmd> <kind> <in> <out>` (`launch_descriptor_native.rs:149`, `lifecycle_v3_stop_native.rs:524`), and the
  socket envelope directly (`dispatch_native.rs:531-541`, a second copy of the v2 envelope) with ops 22, 26, 36, 38,
  39, 46, 48, 49, 66-71, 76, 78, 79, 164 (`dispatch_native.rs:24,504`). It hand-encodes v4 retry request frames
  (`lifecycle_v4_retry_native.rs:77-120, 322`) and decides the retry selector "from protected local evidence before
  any Mini call" (`:7-8`).
- grain-runtime calls `mini` (submit, retry `--mode lookup`) and the Host directly for `inspect outcome` and
  `inspect-agent-lifetime-paid-ingress` (`main.rs:2481, 6228, 4310ff`).
- Lean side of the lifecycle: `Kernel/ApplicationGrain.lean` (beginStart +1 gen → phase 3, claimStart → 9,
  completeStart → 4, stop begin/claim/complete → 5/10/2, reconcileFailedStart +1 → 2; `docs/SPK-LIFECYCLE.md:15-21`),
  create-once by the `firstAttempt`/`created` nullifiers; v4 retry gated by `RetryHistory`
  (`Kernel/NativeHostReplay.lean:725`).
- Theorems: the lifecycle families' receivers carry their own (`Kernel/ApplicationLifecycle*`, 66 modules); no theorem
  spans the Rust half (sandbox, broker).

### 3.7 Compiler / Objective Bend ⇄ kernel

- Crossing: `Accepted l` (`Compiler/ObjectiveBendFrontEnd.lean:283`; `packetTerm : packet.source.term = erased`,
  `checkedExact : check source [] packet.fuel = some typed`), `ObjectiveSourcePackage.Package {frontEnd; modules;
  entryModule; entryDefinition}` (`ObjectiveSourcePackage.lean:29`), `ObjectiveBendSourceArtifact.Artifact {package;
  declaration; typedCore; inputCodec; outputCodec; laws}` (`:20`), the pin `identity a` (`:58`), `LawExpr → Pred`
  (`Compiler/ObjectiveBendLaw.lean:100`), `InvokeRequest` (`Kernel/ObjectiveCall.lean:2171`), `runBounded (limits) :
  Nat → State → Outcome` (`Theory/ObjectiveBendDemandMachine.lean:227`).
- Tags: `DREGG.OBJECTIVE-BEND.SOURCE-ARTIFACT/v2`, `…SOURCE-PACKAGE/v3`, `DREGG/OBJECTIVE/ACTIVITY/PLAN/v4`,
  `…/RECORDED-FAILURE/v2`, `DREGG.OBJECTIVE.ACTIVITY.OUTCOME/v1`, `DREGG.OBJECTIVE.ACTIVITY.CELL.ID/v1`; the front-end
  identity is a hex SHA-256 of a manifest of front-end source files (`Compiler/ObjectiveBendFrontEndIdentity.lean:48-51`)
  — a second hash family inside one package.
- Theorems (proved): `Program.runs_front_end_output` (the kernel re-runs the front end on the package and gets the
  artifact's typed core), `Replayed.core_replayed`, `accepted_execution_semantics`, `admitted_source_semantics`,
  `ObjectLaw.compile_sound`, `runBounded_value_sound`, `Admissible.turn_determined`. The Objective family is the one
  family with a certificate-to-Turn statement on main (`Kernel/ObjectiveAdmissible.lean:1-3`: "Stage-0 certificates
  bind the exact source intent and its derived Turn. The durable log still encodes the intent").

## 4. PROTOCOL FUNCTIONALITY MAP

### 4.1 Host request opcodes (all 186, by family)

Source of truth: `protocol/host-operations.json` (`format: mini-host-request-operations-v1`, 186 operations: 184
active, 2 reserved), generated into `native/host-operations.rs` and checked against the Lean dispatchers and Rust
callers by `scripts/host-operations.py` (gate `host-operations` in both `local-gates.sh` and `merge-gate-checks.sh`).
Response markers: **255** Host refusal/outcome envelope, **254** transport refusal (never forwarded), **164** also a
definitive no-record refusal of a private dispatch. "op" = operator route only; otherwise public + operator.
Dispatch: `serveFrame` special-cases 26, 34/164, 46, 76, 152, 154 (`Host/Main.lean:2624-2636`); everything else goes
to `dispatchSession` (`:2047`), which forwards unknown ops to `fnDispatch` (the big operation match in `run`'s
`stdio` arm, `:6655ff`), which forwards 210-219 to `objectKernelOperation` (`:5958`) and 66-71 to
`launchLifecycleOperatorOp` (`:6136`). Ops 7, 9, 10, 11 (and 8 except session kinds) are `pureCodec`
(`:1997-2045`): "the ONE implementation" served both by the session and by the storeless `minidregg-host CONFIG
codec` loop (`serveCodec`, `:2691`).

| ops | family (owner) | what | where (READ) |
|---|---|---|---|
| 0 describe · 6 profile | kernel-client | deployment description, metering profile | `dispatchSession` `Host/Main.lean:2054,2081` |
| 1 prepare · 2 submit · 3 lookup | kernel-client | signing plan from a signed observation; submit a `SignedCall`; exact-retry lookup | `:2058`, `:6662-6684` → `NativeHost.prepareAuthorizedLoaded` `Kernel/NativeHost.lean:829`, `submitDisclosedWith`/`submitLoadedVia` `:3057`, `lookupLoaded` |
| 4 challenge · 5 query · 10 observation-assemble | kernel-client | observation challenge for a signed intent; authorized view; assemble signed observation | `:2066`, `:2072` (`NativeObservationOpeningCache.queryWireLoaded`), `:2029` |
| 7 author · 8 inspect · 9 signatures · 11 call-assemble | kernel-client | pure codec frames (JSON ↔ canonical bytes, plan+sigs → call) | `pureCodec` `:1997-2045` |
| 12-16, 18 | fn-services | fn consumer poll/ack, reply poll/ack, origin outbox (+export) — spawns the fn binary over its control socket | `:6685-6739`, e.g. `--fn consumer --frame ack` `:6122` |
| 17 · 19 | inference | provider continuity, provider usage quote | `fnDispatch` |
| 20/21 · 24/25 | selected-release | selected release submit/lookup; selected source publication submit/lookup | `:2119-2140` |
| 22/23, 26/27, 38/39, 44/45, 50-53 (op) | spk-lifecycle | application lifecycle begin / claim / completion: plan, assemble, submit, lookup | `:2122-2160`, `dispatchLifecycleClaimSubmitSession` `:2547` |
| 66-71 (op) | spk-lifecycle | launch begin/claim/completion plan + assemble, with the v4 failed-create retry frames routed first | `launchLifecycleOperatorOp` `:6136` |
| 28-37, 54-57, 82-85, 152, 154, 164 (mostly op) | spk | share issue, current birth, application dispatch (submit 34/164 streamed), grain share issue, session enrollment, stream renew, route inspect / route-bound dispatch | `serveFrame` `:2624-2636`; `dispatchApplicationSubmitSession` `:2350`, `dispatchRouteAdmissionSession` `:2414`, `dispatchStreamContinuitySession` `:2396` |
| 206-209 (op) | spk-recovery | failed-start recovery prepare/assemble/submit/lookup | `fnDispatch` |
| 40-43, 60-65 (op) | fn-services | fn namespace, selected coverage, empty progress, frontier plan/assemble | `:2161`, `fnDispatch` |
| 46-49, 58/59, 72-81 (op) | hermes | paid agent dispatch, agent reserve, agent lifetime grant / dispatch / reserve | `dispatchAgentSubmitSession` `:2434`, `dispatchAgentLifetimeSubmitSession` `:2471`, `agentDispatchAuthorSession` `:2174` |
| 86-89, 92-95, 140-144, 187-190 | identity | participant key enrollment, participant provisioning, key rotation (144 = key status), next-key adoption | `fnDispatch` |
| 91 · 123-125 · 130 | world | current resource birth; realm well plan/assemble/submit; affordance dry run (plan as 1, assemble as 11, submit as 2 over a Store writer that never appends) | `:2106` (`DryRun.dryRunLoaded`) |
| 96-102 · 180 | fleet | fleet turn plan/assemble/submit/lookup, topic poll, head, receipt; incoming ledger | `fnDispatch` |
| 103-121, 181-186 | payments | pay command, view, observation, enrollment view/quote, refill, self-enrollment (op), pay claim view/quote/plan/assemble/submit/lookup | `fnDispatch`; `Host/PayClaims.lean` (author/inspect kinds via 7/8) |
| 126-129 | clock | clock tick plan/assemble/submit; clock view | `fnDispatch` |
| 131-137 | nock | program check/show, sample, dry run, app poke dry run / peek / state | `fnDispatch` |
| 150 · 192 | laws · law-diagnostics | law-sat (pure function of request bytes); 192 reserved | `:2115` `LawSatWire.lawSatSession` |
| 151 · 153 · 191 | receipt-continuity · checked-carry | receipt continuity; carry receipt lookup (oversize frame allowed, `:2683`); 191 reserved | `:2118`, `fnDispatch` |
| 160-163 | job-money | job money plan/assemble/submit/lookup | `fnDispatch` |
| 170-173 | history | certify plan/assemble/submit/view (the C14 tail-bound certify; `deploy/checkpoint` timer every 15 s) | `fnDispatch` |
| 193/194 | application-dispatch/member-workspace | dispatch ready; authenticated dispatch plan | `fnDispatch` |
| 201/202 | resource-reserve-birth | reserve resource birth plan/assemble | `fnDispatch` |
| 210-214 | activity-native (Objective Bend) | 210 signing plan · 211 detached assembly · 212 submit · 213 receipt-only lookup · 214 public view (incl. `pins[].frontEnd = {replayBytes, coreBytes}`) | `objectKernelOperation` `:5958-5996`; `Host/ObjectiveActivityJson.lean:588-597`; `Kernel/ObjectiveActivity.lean:984-991` |
| 215-219 | seats-native | seat plan/assemble/submit/lookup/view | `objectKernelOperation` |

Most families follow one shape — **plan → (custody signs) → assemble → submit → lookup** — with plan/assemble able to
run without the Store (assemble ops are pure functions of plan + signatures). A `submit` always re-reads the current
tip (`sessionCurrent`); a `lookup` of the same call is the uncertain-reply recovery.

### 4.2 Consent provider frames (executable `minidregg-client-consent CONFIG stdio`)

Same frame shape (u32 LE length ‖ opcode ‖ payload, bound `maxFrame`), served by `ClientConsentCore.serve`
(`Host/ClientConsentCore.lean:507-571`):

| frame | meaning | where |
|---|---|---|
| 220 | intent consent: custody signs its own retained intent (signer must be the subject's current key) | `consent` `:336` |
| 221 | observation consent: check the Host's challenge against the provider's own admitted prefix (`NativeClientConsent.checkObservation`), return selected headers | `:339` |
| 222 | plan consent: re-derive the plan headers (`NativeClientConsent.checkIntentPlan`) | `:344` |
| 224 | specialized consent (lifecycle families; may upgrade to a full re-admission) | `:562-566`, `ClientConsentSession.lifecycleExpected` |
| 226 | possession consent (no Store) | `possession` `:438` |
| 227 | objective headers (Objective Bend invocation: re-derives the quote, `Host/ObjectiveConsent.lean:22-46`) | `objectiveHeaders` `:469` |
| 228 | offer a retained consent anchor before the first admission (`ConsentAnchor.decode`) | `:524-535` |
| 229 | return the anchor of what this provider admitted, for custody to retain | `:545-550` |
| 230-232 | thin consent (intent / observation / plan) from custody alone, no Store, no replay (`Kernel/NativeThinConsent.lean`) | `thin` `:377` |
| 233 | resident provider's per-connection re-check that the Store still extends its admitted prefix (`ConsentAnchor.recheckStore`) | `:536-544` |

How it admits: first frame → `verifyInitial` (anchor resume via `ConsentAnchor.resume`, else
`NativeHostReplay.verifyLoaded` from genesis) (`:264-279`); later frames → `refresh` (`DurableReceiverIO.extendFrom`,
only the new suffix; an anchored basis whose suffix fails is re-admitted from genesis) (`:281-297`). The provider
reads the Store through `config.transport` (the same `Transport` as the Host) — it is a second full verifier of the
same bytes, not a client of the Host.

### 4.3 Host command-line verbs (operator / one-shot)

`minidregg-host CONFIG.json <verb>` — about 120 verbs dispatched in `run` (`Host/Main.lean:6312-9121`; usage string
`:6127-6131`): the session (`stdio` :6650, `codec` :6647), store life (`genesis` :6610, `bootstrap` :7797, `audit`
:7881, `store-audit` :7887, `checkpoint-differential` :7905, `store-bench`), one-shot twins of every session op
(`prepare`, `submit`, `lookup`, `challenge`, `query`, `assemble`, `law-sat`, `dry-run`, the lifecycle/fn/selected
release families), authoring (`author`, `objective-quote`, `objective-publication`, `objective-front …`,
`grain-origin-prepare`), evidence (`export-evidence`, `verify-evidence`, `portable-verify-fn`, the fn consumer
verbs), ledgers (`well-ledger`, `pay-ledger`, `pay-purse`, `pay-job`), and `store-epoch` (no config). One-shot verbs
that fail write the same refusal frame under 255 with exit 2 (`main`, `:9144-9160`).

### 4.4 Follower / export

- `turn-log-follower export CONFIG OUT` → `genesis.bin`, `turns.bin` (`DeployedTurnCompact.encodeTurnAt` per entry,
  framed by `TurnLog.frameEntries`), `root`; it re-checks the World against the Store's cells, spent set and height.
- `turn-log-follower follow OUT [--plant-drop K]` → `ROOT <digest>` or `STOP undecodable|refused <height>`
  (`Host/TurnLogFollower.lean:1-14`, :162); driven by `scripts/kern/turn-log-follower.sh` (two plants: flipped last
  byte, `--plant-drop 0`). Not in any gate or journey row (READ grep).
- fn archive: `archive_journal` table, `FnArchivePublisher.run` (`Host/Main.lean:6632-6646`), own KMAC chain.
- Evidence export: `export-evidence CALL PACKAGE` / `verify-evidence`.

### 4.5 Client commands (`mini`)

Dispatch in `run` (`native/resource-client/src/main.rs:3195-4500`; Rust-agent READ). `bend-session-sign` and
`fleet-sign` are routed before argument parsing (`main` :4502). Groups:

- **Workspace and documents**: `workspace` (~90 actions, `workspace.rs:6165+`: init, import, list, describe/read,
  submit, room-key, room-kick, transclude, doc-* (search, show, outline, insert, move, history, diff, share, revoke,
  epoch export/import, protect …), mark/unmark, law-check/law-show/law-export-show, propose, program-create,
  instance-call, kind-*/instance-*, create, provision, recover, publish-delegation, market-open/bid/reveal/settle),
  `member`, `web`, `shell` (M4), `channel`, `traffic`, `mix`, `mix-live`, `relay*`.
- **Kernel calls**: `submit` :4299, `query` :4327, `retry` :4389, `author` :3817, `inspect` :3826, `objective-invoke`
  :4372, `activity` :3221 (ops 210-214, `activity.rs`), `seat` :3222 (215-219), `checkpoint` :3218 (certify 170-173),
  `clock` :3217, `job` :3220, `well`, `credit`, `meter`, `story-law`, `export-evidence`/`verify-evidence`.
- **Identity**: `join` (solana v1/v2 or participant enrollment), `enroll`, `keygen`, `key`, `rotate-key`,
  `adopt-next-key`, `key-status` (op 144), `enrollment-bootstrap`/`enrollment-view`, `session-reenroll`,
  `session-enrollment-*`; `key-service*` refuse ("gone").
- **Payments**: `pay`, `pay-claim`.
- **Agents / Hermes**: `agent-reserve-*`, `agent-lifetime-{reserve,paid,grant}-*`, `agent-payer-sign`,
  `hermes-handoff`, `provider-continuity`.
- **SPK / grains**: `share-issue-*`, `grain-share-issue-*`, `historical-call-receipt-lookup`.
- **fn**: `fn-namespace-*`, `fn-frontier-*`, `consumer-poll`/`reply-consumer-poll`, `consumer-ack`,
  `origin-outbox-*`, `origin-publish`, `selected-release-*`, `selected-source-*`, `selected-exchange`.
- **Serving and operating**: `serve` :3290, `consent-resident` :3305, `serve-operator` :3312, `serve-public-proxy`
  :3325, `socket-proxy` :3203, `operator-status`, `drain-operator`, `host-command` :3348, `bootstrap` :3806, `store`
  :3624 (incl. `mini store audit`), `audit` :3625, `consumer-host-upgrade` :3568, `escrow-recover`, `enc-public`,
  `enc-key-id`, `verify-view` :3728.
- Allowed over `--remote`: workspace, enroll, join, pay-claim, shell, submit, query, retry, author, inspect,
  describe, profile (`main.rs:846-849`).

### 4.6 SPK broker and grain verbs

- **`mini-spk-broker`** (user unit `mini-spk-broker@.service`; JSON `tag = "verb"`, kebab-case, `deny_unknown_fields`;
  `native/spk-host/src/broker.rs:291-363`): identify, init-store, place, set-cgroup, ingest, mount-volume, unmount,
  adopt-runtime, runtime-status, install-unit, start, stop, export-volume, backup. Size classes set memory, cpu/io/tasks
  weights, volume size and WebSocket caps (`:40-80`). Config protocol v2 on main; v3 (adds `bwrap`, `bwrapSha256`) on
  `lane/spk-ns`.
- **`spk-host` verbs** (`main.rs:36-197`): qualify-launch, install-prepare, install-complete, broker-serve,
  checkpoint-pause-check, checkpoint-backup, `grain …` (init-store, current-profile, rebind-profile, register-route,
  adopt-runtime, runtime-status, install, unit, unit-name, supervise-instance, host; `grain.rs:1463+`),
  resident-bootstrap, resident-validate, resident-run, resident-stop, human-custodian-init, qualify, inspect-installed.
- **Root volume helper** `mini-spk-volume-helper` (sudo, one-shot): create, mount, unmount, freeze, thaw, destroy,
  volumes-status (`USER-TENANCY.md:28-37`).
- **Resident grain phases** (`hostd.rs:105-113`): Armed → LaunchRequested → Entered → Running → Fenced → Stopped;
  delivery DeliveryRequested / Delivered / Uncertain (:329-331).
- **Sandbox** (`native/spk-host/src/sandbox.rs:41-50` `FIXED_ARGS`): `--die-with-parent --new-session --unshare-user
  --disable-userns --unshare-pid --unshare-ipc --unshare-uts --unshare-cgroup --unshare-net --cap-drop ALL --seccomp 6
  --clearenv --ro-bind-fd 4 / --bind-fd 5 /var --size 134217728 --tmpfs /tmp --proc /proc --dev /dev --chdir /`
  (fd 3 capnp, fd 4 image, fd 5 /var, fd 6 seccomp `resident-web.policy`). The **Hermes/agent worker** profile
  `deploy/grain-host/bwrap:116-138` has no `--cap-drop`, `--seccomp`, `--disable-userns` or `--new-session`; it runs
  under `systemd-run --user … RuntimeMaxSec≤1800 MemoryMax=2G TasksMax=128` via `launch-gate`.
- **grain-runtime** control socket: JSON lines, modes Hard / Soft / Inspect (`control.rs:19-27`); controller unit
  `mini-grain-controller@.service` (`grain-runtime serve /opt/mini/grains/%i.json`, MemoryMax 1G).
- **Key broker `mini-keys`**: verbs serve, relay, hello, pool, namespace (`main.rs:139-183`); u32 LE + JSON frames
  (`wire.rs:1-7`); roles by SO_PEERCRED; authorizes provider actions from the Host's op 144 key status
  (`server/native.rs:34-45`) under the Rust-only domain `mini/member-provider-action/v1`.

### 4.7 Where each operation is checked

- **Every state-changing op**: the Host receiver (Lean) re-derives the intent from signed ingress against the current
  opening; `execute` re-checks replay identity, read guards, nullifiers and the meter; `prepareAppend` CAS; readback.
- **Plans before signing**: the consent provider re-derives (220-224, 227) or thin-checks (230-232).
- **History**: open re-verifies chain + checkpoint MAC + root; old records are verified at use (`verifyAt`); operator
  `audit` / `mini store audit` re-admits every signed ingress from genesis (`JAUDIT` row).
- **Computation**: Nock runs and Objective Bend runs are re-executed by the referee (`checkRun_sound` `Kernel/Run.lean:316`,
  `no_accepted_of_output_mismatch` :383; memory `project-no-proof-system-in-mini-admission`); nothing is accepted on a proof.
- **Bytes on the wire**: `host-operations` gate (opcode allocation ↔ receivers ↔ Rust routes), `fn-wire` gate,
  `native-transcripts` gate (verifier transcripts re-verify; a flipped byte reads invalid).

## 5. THE HEART: the server's data and persistence model

Tags: **READ** = read at the cited path:line on main 2c27b08b; **LANE** = read on the named `gh/lane/*` tip;
**ASSUMED** = my inference, not read.

### 5.1 Two state models, one bridge (the single most important fact)

Mini has **two** state machines today, and the Host runs the second one:

| | the kernel model (spec) | the deployed engine (what runs) |
|---|---|---|
| state | `World R TxId D = {cells : Cells R, system : Store (sysLayout TxId D)}` (`Kernel/World.lean:264-266`) | `Loaded rootBytes = {image : Image, baseHeight, base : State, snapshot : DataSnapshot rootBytes, …, roots : RootCache, index, links, ids, txs, rootLog, frontier, headTag}` (`Compiler/DurableReceiverCore.lean:854-900`) |
| transition | `World.admit : World → Turn → Except Reject World` (`Kernel/World.lean:607`) | `DurableDataIntent.execute : Schedule → DataSnapshot → DataIntent → Outcome` (`Kernel/DurableDataIntent.lean:429`), reached through `DurableCheckpoint.prepare` and `DurableReceiverIO.prepareAppend` (`Compiler/DurableReceiverIO.lean:167`) |
| history | `fold g log := log.foldlM (World.step H) g` (`Kernel/World.lean:634`) | `Image = {seed : Seed, accepted : List IntentRecord}` replayed by `DurableReceiver.replay` (`Kernel/DurableReceiver.lean:156-175`) |
| log entry | `Turn` (deterministic data, no post bytes, `Kernel/World.lean:370-383`) | `IntentRecord = {transactionId, writes : List DataWrite, readGuards, nullifiers, exactCharge, event, subject}` (`Kernel/DurableReceiver.lean:66-74`), each `DataWrite` carrying `canonicalPostBytes` (`Kernel/DurableDataIntent.lean:71-76`) |
| cell ids | `CellId := Nat` (`Kernel/World.lean:91`) | `CellId := TypedAuthorization.Digest` (`Kernel/DurableDataIntent.lean:47`); bridged by `.value` |

The bridge is `Represents B p w := SnapRepresents B p.snapshot p.height w` (`Kernel/HostRefinesWorldCore.lean:405`) with
`deployed_refines_step : ImplementationRefinement H (Loaded rootBytes) (HostStep B H) (Represents B)`
(`:698`) and `host_trace_represents_fold` (`:719`). **On main the World is never run on the receive path**:
`World.admit` is called only by the exporter/follower (`Host/TurnLogFollower.lean:86`), the totality runner
(`Host/ObjectiveTurnTotalityRunner.lean:48`, via `Turn.ofLoaded`) and receivers' proofs (READ by grep; no
`World.admit` in `Compiler/DurableReceiverIO.lean` or `Kernel/NativeHost.lean`). Two consequences, READ:

- **`host_submit_is_step` — the theorem that says "what the Host committed is a World step" — is not proved.** It
  exists only inside a docstring, "The statement left for T4" (`Kernel/HostRefinesWorldCore.lean:75-99`;
  `docs/design/RECEIVER.md:294`). What IS proved is the abstract `deployed_refines_step`, whose premise
  `HostStep` must be constructed per receiver (`extendStep`, `:740`).
- **`SnapRepresents.head : ∃ r, w.head = some (height, r)`** (`Kernel/HostRefinesWorldCore.lean:392`) binds the height
  but not the log root: the deployed chain (cSHAKE over `IntentRecord` bytes, `DurableCheckpointCodec.recordDigest`,
  `Compiler/DurableCheckpointCodec.lean:505`) and the World chain (`H.chain` over `H.turnDigest t`,
  `Kernel/World.lean:461-469`) are two different chains. Likewise `parent : ∀ c, w.parent c = none` (`:398`) —
  parentage still lives in the authority cell's plane 13.

TURN-LOG (lane/turn-log dbb4f0f4, LANE) is the collapse: 4a puts a `WorldTrack` (`held (world) (represents)`) into
`Loaded` and makes `prepareAppend` refuse what the World does not admit; step 2 makes the log entry the Turn; 4b makes
`Represents` equality; R5b deletes `execute`, `DataSnapshot.install`, `IntentRecord.writes`/`canonicalPostBytes` and
`ReplayEnvelope`. See §6.1.

### 5.2 The kernel model, quoted

```lean
-- Theory/Store.lean:46-65, 126-134 : the one storage primitive
inductive Discipline | rom | ram | appendOnly
structure Layout where Namespace : Type u; Key : Namespace → Type v; Value : Namespace → Type w
  discipline : Namespace → Discipline; [namespaceDecEq …] [keyDecEq …] [valueDecEq …]
inductive Op (L : Layout) | read (space) (key) (observed : Option (L.Value space))
  | write (space) (key) (before after) | allocate (space) (key) (value) | free (space) (key) (before)
abbrev Patch (L : Layout) := List (Op L)                                   -- :252

-- Kernel/World.lean
structure Registry where Kind : Type; layout : Kind → Layout; [kindDecEq : DecidableEq Kind]     -- :96
structure Cell (R : Registry) where kind : R.Kind; store : Store (R.layout kind)                 -- :104
inductive SysSpace | journal | head | retired | parent | spent | allowance                      -- :187
--   keys/values (:198-217): journal TxId ↦ (height, D) appendOnly · head () ↦ (height, logRoot) ram
--   retired CellId ↦ () appendOnly · parent CellId ↦ CellId appendOnly · spent D ↦ () appendOnly · allowance Lane ↦ Nat ram
structure World (R) (TxId D) where cells : Cells R; system : Store (sysLayout TxId D)           -- :264
structure Leg (R) where cell : CellId; kind : R.Kind; patch : Patch (R.layout kind)              -- :338
structure Turn (R) (TxId Ev D) where                                                              -- :370
  txId; creates : List (CellId × Cell R × Option CellId); legs : List (Leg R); retires : List CellId
  event : Ev; nullifiers : List D := []; charge : Charge := 0; subject : Option SubjectId := none
  keyEpoch : Nat := 0; capability : Option D := none; notBefore : Nat := 0; validUntil : Option Nat := none
  absent : List CellId := []
structure History (R) (TxId Ev D) where turnDigest; chain : D → D → D; logRoot0 : D             -- :409
  legBytes : Leg R → Nat; imageBytes : Cell R → Nat
inductive Reject | emptyTurn | duplicateLegCell | duplicateCreate | duplicateRetire | invalidAbsenceGuard
  | noHead | replayedTransaction | retiredIdentifier | cellPresent c | missingCell c | kindMismatch c
  | guardFailed c i | retireNonEmpty c | missingParent c room | duplicateNullifier | outsideWindow
  | nullifierSpent | chargeMismatch | overAllowance | imageNotRom c                                  -- :424
def World.admit (w) (t) : Except Reject World   -- :607  shape → head → journal fresh → turnCheck → absentCheck
                                                --        → sysPatch ValidFrom → applyCells (creates, legs, retires)
def fold (g) (log) := log.foldlM (World.step H) g                                                  -- :634
```

The deployed instantiation: `deployedR : Registry := ⟨CanonicalCellRegistry.Kind, CanonicalCellRegistry.layout⟩`
(`Kernel/DeployedBridge.lean:49`) over **19 cell kinds** with byte tags (`Compiler/CanonicalCellRegistry.lean:88-123`,
`:269-308`): content 1, eventHistory 2, authority 3, declaredObject 5, resourceBook 6, accountMetadata 8,
declaredProgram 9, policySource 10, pay 11, stream 12, nockProgram 13, clock 14, streamEntry 15, system 16,
worldKind 17, worldInstance 18, objectiveActivity 19, seat 20. One `StoreCodec.Wire` per kind (`wireOf`,
`Kernel/DeployedBridge.lean:115`); the deployed History is `DeployedHistory.history` with `opBytes` counting only new
values (`Kernel/DeployedHistory.lean:22-30`).

The model's proved invariants (all READ, `Kernel/World.lean`): `fold_append` (:670), `fold_snoc` (:680),
`fold_eq_some_iff` (:699), `admit_ok` (:771), `step_frame` (:1533), `step_leg` (:1545), `step_create` (:1559),
`step_retire` (:1580), `step_wf` (:1594), `step_parent_recorded`/`_exists`/`_stable` (:1615-1634),
`step_retired_stable` (:1654), `step_rom_preserved` (:1683), `rom_cell_immutable_after_birth` (:1724), `fold_wf`
(:1748), `genesis_wf` (:1768), `step_head`/`fold_head` (:1784/:1793), `step_journal`/`journal_exact` (:1810/:1836),
`sysPost_spent/_allowance/_parent/_journal/_head/_retired` (:1420-1473), `absentCheck_eq_none_iff` (:591),
`meterLanes_nodup` (:1370).

### 5.3 The deployed engine, quoted

```lean
-- Kernel/DurableDataIntent.lean
structure DataWrite where cellId : CellId; expectedPre exactPost : Digest; canonicalPostBytes : List UInt8   -- :71
structure ReadGuard where cellId : CellId; expectedRoot : Digest                                         -- :79
structure DataIntent (rootBytes : List UInt8 → Digest) where                                            -- :99
  transactionId; writes : List DataWrite; readGuards; nullifiers : List StableNullifier; exactCharge : Charge
  event : StableEvent; subject : Option SubjectId
  postRootsBound : ∀ w ∈ writes, rootBytes w.canonicalPostBytes = w.exactPost
  guardsReadOnly : ∀ g ∈ readGuards, g.cellId ∉ writes.map DataWrite.cellId
structure DataSnapshot (rootBytes) where model : Snapshot …; canonicalBytes : CellId → List UInt8
  coherent : ∀ c, rootBytes (canonicalBytes c) = model.roots c                                          -- :193
inductive Outcome | accepted next | replayed recorded | rejected reason | crashed point next             -- :408
def execute (schedule) (before) (intent) : Outcome   -- :429: journal lookup first (replay), then preflight, then install

-- Kernel/DurableReceiver.lean
structure Seed where absentBytes : List UInt8; cells : List (CellId × List UInt8); available : Charge   -- :130
structure Image where seed : Seed; accepted : List IntentRecord                                         -- :156
-- Kernel/DurableCheckpoint.lean
structure State where absentBytes : List UInt8; cells : List (CellId × List UInt8); available : Charge   -- :65
```

`Loaded` (`Compiler/DurableReceiverCore.lean:854`) carries, each with its exactness proof: the image, the checkpoint
base, the resumed snapshot (`resumed : resume rootBytes image baseHeight base = some snapshot`), `chain`
(`chainExact : chain = chainAfter logStart image.accepted`), `roots : RootCache` with
`rootsExact : RootsExact roots (entriesOf image snapshot chain)`, the presence `index` and `links` (`= ofRecords
image.accepted`), `ids`, `txs`, `rootLog`, `frontier`, `headTag`. It is aliased `NativeHostContext.Durable`
(`Kernel/NativeHostContext.lean:27`) and wrapped by `Opened config = {durable, directory, authority, pins, lawful}`
(`:439-447`) and the session `Session config = {opened, openingCache, walked, light : NativeHostLight.Light config}`
(`Kernel/NativeHostSession.lean:37-43`). Its light twin is `DurableServed.Opening` / `OpenedServed`
(`Kernel/NativeHostServed.lean:39`, `Kernel/NativeHostLight.lean`).

### 5.4 The Store on disk

READ from `docs/DURABLE-STORE.md:8-16`, `Compiler/DurableCheckpointCodec.lean`, `Compiler/DurableHistory.lean`,
`Compiler/DurableIndex.lean`, `Compiler/DurableReceiverCore.lean:59-140`:

- **Files**: `DEPLOYMENT/checkpoint.key` (32 B MAC key, 0600, `mini bootstrap`), `DEPLOYMENT/pinned-config.json`,
  `STORE.head-anchor` (+`.lock`, MINIANC2 head anchor, outside the Store dir), `STORE/forward-link.sqlite3`
  (SQLite schema v4: `durable_seed`, `durable_log(height, record, tag)`, `durable_checkpoint(height, bytes)` latest two
  kept, `archive_journal(seq, record, tag)` for fn; plus `durable_node` rows, space 1 = log accumulator, space 3 =
  index trie, `Compiler/DurableReceiverCore.lean:72-77`).
- **The physical boundary** is `Transport` (`Compiler/DurableReceiverCore.lean:97-140`):
  `read : Nat → Bool → IO (Except String (Option Stored))`, `append : Nat → Entry → List NodeWrite → IO
  CasObservation` (CAS "iff the head is one below"), `putCheckpoint`, `initializeSeed`, `key`, `checkpointEvery`,
  `logStart`, `systemCell`, `sourceGate`, `peekSeed`, `history`, `checkpointAt`, `readFromCheckpoint`.
  `NativeConfig.transport` (`:408`) implements it by calling the Rust store helper with verbs `durable-read`,
  `durable-append`, `durable-checkpoint`, `durable-init`, `durable-seed`, `durable-history`, `durable-checkpoint-at`
  (`:216-392`) through `NativeCoprocess.output` (`:147`): one resident `<binary> serve` helper per Host that still
  runs `<binary> args` as **its own child per call** (`Compiler/NativeCoprocess.lean:1-20`).
- **Seed**: `DREGG.DURABLE.SEED/v1` frame carrying the `StoreEpoch` label (`seedFrameFor`,
  `Compiler/DurableCheckpointCodec.lean:296`).
- **Log entry** `h`: `Entry = {record : List UInt8, tag : List UInt8}` (`DurableReceiverCore.lean:59`).
  `record = recordFrame.encode (IntentRecord.ofIntent intent)` under `DREGG.DURABLE.LOG` byte v2
  (`DurableCheckpointCodec.lean:478`, tag `PersistedCodecTags.lean:209`; v1 refuses, `v1_record_refused` :482).
  `tag` = the v4 trailer `Carried = {root, chain, frontier, indexRoot}` ++ `tagMac` (KMAC256 over all four)
  (`Compiler/DurableHistory.lean:99-127`).
- **Chain**: `chain₀ = logStart seed` (`NativeHostCodec.logRoot0 domain semantics`), `chainₕ = chainDigest chainₕ₋₁
  (recordDigest recordₕ)`, `recordDigest = turnDigestOfBytes (intentStream.encode record)`
  (`DurableCheckpointCodec.lean:505-513`; `Kernel/WorldRoot.lean:560-564`).
- **History accumulator** (KN2-STORE-OPEN): an MMR over leaves `leafDigest h record chain root`
  (`DurableHistory.lean:62`); old records are read only through `verifyAt` (`verifyAt_included` :226,
  `verifyAt_bytes` :233, `verifyAt_sound` :253). Fields of `RawEntry` are private: "no read path returns unverified
  bytes" is compiler-enforced (`:24-28`).
- **Index trie** (`Compiler/DurableIndex.lean:1-24`): ONE compressed authenticated trie whose families are the spent
  map, the transaction index, presence, links, backlinks, fleet; 65-byte keys, 520 path bits; `lookup_sound`,
  `reveal_sound`, `collision_is_cshake`.
- **Checkpoint**: `Sealed = {body : Body, root : Digest, mac}` with `Body = {keyId, height, chain, frontier, indexRoot,
  state : State}` (`DurableCheckpointCodec.lean:566-618`), framed `DREGG.DURABLE.CHECKPOINT` byte v3 (`:622`,
  `PersistedCodecTags.lean:153`), MAC = `KMAC256(key, "DREGG/NATIVE-HOST/CHECKPOINT-MAC/v1", (keyId, height, root,
  cSHAKE(body)))` (`:630-636`). The root is **recomputed on open, never trusted** (`worldRoot`, `:604`;
  `openSealedWith`, `:684`). Cadence `checkpointEvery` default 64 (`docs/DURABLE-STORE.md:11`).
- **StoreEpoch** (`DurableCheckpointCodec.lean:144-260`): `{stateKey, schemaRefs, logTag, accumulator, commands}`;
  `current = ⟨stateKeyCodecId, persistedSchemaRefs, logTagLabel, "history/mmr-v1;index/trie-v1;checkpoint/v4",
  "commands/v2"⟩` (:194). `persistedSchemaRefs` is already **content-addressed**: cSHAKE of the length-prefixed
  corpus of every `@[persisted_codec_tag]` (637 lines in `Compiler/PersistedCodecTags.lean`) plus every cell kind's
  structural descriptor (`persistedCellDescriptors`, :166-189). Read BY NAME (`StoreEpoch.parse`, :230); a differing
  component is refused naming it (`differing`, :246; `differing_nil_iff`). The seed is peeked before the anchor, so an
  old Store refuses by epoch (`Transport.peekSeed`).

### 5.5 Roots and digests

- **Cell root**: `ResourceBirthCodec.rootBytes bytes = (cSHAKE256 "DREGG.CELL.LIFECYCLE/v1" bytes).digest`
  (`Compiler/ResourceBirthCodec.lean:419-422`).
- **World root** `deployedRoot es = AuthTrie.root worldDig deployedIx 256 es` (`Kernel/WorldRoot.lean:518`), keys
  `Key.system | Key.cell c` (:67), nodes framed `nodeBytes` (0 empty / 1 leaf key++digest / 2 branch, :452),
  hashed by cSHAKE256 `DREGG.WORLD-ROOT/v2` (`PersistedCodecTags.lean:37`), index `deployedIx k` = 256 bits of
  cSHAKE (:500). Binding: `deployedRoot_binds` (:537) is premise-free up to a deployed-hash collision;
  `rootOf_eq_exhibits_collision` (:407). The system slot is `systemLeaf height chain` under
  `DREGG.NATIVE-HOST.SYSTEM/v1` (`DurableCheckpointCodec.lean:552`).
- **Kept trie**: `Theory.AuthTrieCache.Cache` with `Holds` a Prop (`Theory/AuthTrieCache.lean:681-760`;
  `digest_eq` :704, `build_holds` :731, `insert_holds` :749, `opening` :886); deployed as `WorldRootCache.RootCache`
  with `RootsExact.root_eq/advance/opening_complete` (`Kernel/WorldRootCache.lean:1-24`).
- **Digest types** (twin C1, §6.10): `Theory.TypedAuthorization.Digest = {value : Nat}` (`Theory/TypedAuthorization.lean:53`)
  and `Digest256 := Fin (256 ^ 32)` with `toDigest256`/`ofDigest256` (`Compiler/Tower256ConcreteBackend.lean:401-417`).
- **cSHAKE/KMAC**: spec `Theory/Sp800185Cshake256Spec.lean`, fast path attached by `@[csimp]`
  (`Theory/Sp800185Cshake256Fast.lean:853,858`), conformance vectors `Theory/Sp800185Cshake256Conformance.lean`,
  API `Compiler/Sp800185Cshake256.lean`, KMAC `Compiler/Sp800185Kmac256.lean`. One function, layered (not a twin).

### 5.6 Diagram

```
                       client (Rust `mini`)                         consent provider (Lean, local custody)
                              │  4-byte len ‖ opcode ‖ payload (stdio frames; §3.3)     │ frames 220-233
                              ▼                                                          ▼
 ┌──────────────────────── minidregg-host `CONFIG stdio` (Host/Main.lean:6650) ─────────────────────────────┐
 │ serveSession → serveFrame → dispatchSession (op#) ; ops 7-11 = pureCodec (no Store)                       │
 │ Session {opened : Opened, light : Light, openingCache, walked}        (Kernel/NativeHostSession.lean:37)  │
 │   Opened {durable : Loaded, directory, authority, pins, lawful}       (Kernel/NativeHostContext.lean:439) │
 │   Loaded {image = Seed + [IntentRecord], base : State, snapshot : DataSnapshot,                           │
 │           chain, roots : RootCache ⊨ RootsExact, index, links, ids, txs, rootLog, frontier, headTag}       │
 │                                                                                                           │
 │ op 2 submit: callCodec.decode → NativeHost.submitLoadedVia (Kernel/NativeHost.lean:3057)                   │
 │   → receiver (birth/invoke/install/delegate/revoke/renounce, OB activity, lifecycle, fn …)                 │
 │   → DataIntent (writes = post bytes + roots, readGuards, nullifiers, exactCharge, event)                   │
 │   → DurableCheckpoint.prepare → execute (journal → preflight → install)                                   │
 │   → prepareAppend: Entry {record = LOG/v2 IntentRecord, tag = v4 trailer + KMAC}  + node rows             │
 │   → Transport.append h e nodes  (CAS on head) → readback → (every 64) seal checkpoint                     │
 │        ┊ (spec only, not run here)  Turn.ofLoaded ⇒ World.admit ⇐ Represents (∃r head; parent = none)     │
 └───────────────────────────────┬───────────────────────────────────────────────────────────────────────────┘
                                 │ NativeCoprocess: argv frames → resident `serve` helper → child exec per call
                                 ▼
   Rust store helper ─ STORE/forward-link.sqlite3 ─────────────────────────────────────────────────────────────
   │ durable_seed: SEED/v1 {StoreEpoch label, Seed{absentBytes, cells, available}}                            │
   │ durable_log(h): record = LOG/v2 IntentRecord · tag = {worldRoot_h, chain_h, frontier_h, indexRoot_h, MAC}│
   │ durable_node: space1 = MMR (leafDigest h rec chain root) · space3 = index trie (spent, tx, presence, …)  │
   │ durable_checkpoint(h): CHECKPOINT/v3 Sealed{Body{keyId,h,chain,frontier,indexRoot,State}, root, MAC}     │
   │ archive_journal(seq): fn archive (own chain + ARCHIVE-JOURNAL-TAG/v1)                                    │
   └──────────────────────────────────────────────────────────────────────────────────────────────────────────┘
   STORE.head-anchor (MINIANC2) ── outside the Store dir; checked under lock before Lean's checks
   DEPLOYMENT/checkpoint.key (KMAC key, 0600)

   Derived, never persisted: snapshot, roots/RootCache (rebuilt from State at open), presence/link indexes,
   ids/txs, consumed set (from the verified prefix, `consumed_of_loaded`), `Opened.directory/authority`.
   Persisted: seed, records, tags, node rows, checkpoints (State + roots-to-check), anchor, key.

   Side exe: turn-log-follower export/follow (Host/TurnLogFollower.lean): Store → genesis.bin + turns.bin
   (DeployedTurnCompact.encodeTurnAt) → second process folds with World.admit → ROOT <digest>
```

### 5.7 What is persisted vs derived, and what re-genesis means

- **Persisted**: seed (with the epoch label), the log (IntentRecord bytes + trailer), accumulator and index node rows,
  the latest two checkpoints, the anchor, the MAC key, the fn archive journal (READ, above).
- **Derived at open**: the chain (recomputed over the records it must check), the checkpoint's world root (recomputed
  from its State), the snapshot (`DurableCheckpoint.resume` = materialize + replay suffix, `Kernel/DurableCheckpoint.lean:151`),
  the consumed set (from the verified prefix: G-REBASE closed, `HostRefinesWorldCore.lean:69-73`), indexes, the directory
  and authority views, the RootCache.
- **Re-genesis** = a new seed under a new `StoreEpoch.current`; any Store whose label differs in any named component
  is refused by name before the anchor is touched (`StoreEpoch.differing`, `Transport.peekSeed`). There is no migration
  ("A store holding the retired whole-image record refuses …; there is no migration: re-genesis",
  `Compiler/DurableReceiverCore.lean:18-19`). Fixtures that pin a Store (the native accepted fixture, the 7 retained
  j1 Stores the follower journey uses) must be re-emitted after a flag day (LANE: TURN-LOG-LOG says those 7 now refuse
  at height 1 on the new charge rule).

### 5.8 The invariants that hold it together (named)

| invariant | theorem (READ path:line on main, or LANE) |
|---|---|
| the model is a monoid action; replay is exact | `fold_append` `Kernel/World.lean:670`, `journal_exact` :1836, `fold_head` :1793 |
| frame, ROM, WF | `step_frame` :1533, `step_rom_preserved` :1683, `rom_cell_immutable_after_birth` :1724, `fold_wf` :1748 |
| deployed engine is atomic | `execute_no_partial_data_commit` `Kernel/DurableDataIntent.lean:448`; crash model `Kernel/DurableCommitProtocol.lean` |
| record ↔ intent | `IntentRecord.bind_ofIntent`, `bind_exact` `Kernel/DurableReceiver.lean:101,111` |
| checkpoint resume | `resume_sound` `Kernel/DurableCheckpoint.lean:225`; teeth `dishonest_checkpoint_diverges` :338 (trust = the host's own MAC) |
| epoch refusal | `StoreEpoch.differing_nil_iff` `Compiler/DurableCheckpointCodec.lean:258` |
| world root binds | `deployedRoot_binds` `Kernel/WorldRoot.lean:537`, `rootOf_eq_exhibits_collision` :407 |
| kept trie = spec | `AuthTrieCache.digest_eq` `Theory/AuthTrieCache.lean:704`, `insert_holds` :749; `RootsExact.root_eq` (WorldRootCache) |
| history read only verified | `verifyAt_sound` `Compiler/DurableHistory.lean:253` |
| index trie answers | `DurableIndex.lookup_sound`/`reveal_sound` (`Compiler/DurableIndex.lean`) |
| engine refines the model | `deployed_refines_step` `Kernel/HostRefinesWorldCore.lean:698`, `host_trace_represents_fold` :719, `ofIntent_step` `Kernel/TurnOfIntent.lean:1551` |
| **host commit = World step** | **`host_submit_is_step`: STATED IN A DOCSTRING ONLY, NOT PROVED** (`HostRefinesWorldCore.lean:75-99`) |
| Turn log reproduces the World | `followFrom_sound` `Kernel/TurnLog.lean:110`, `followFrom_writeLog` :146, `decodeTurnAt_encodeTurnAt` `Kernel/DeployedTurnCompact.lean:351`; `decodeLegAt_other` :236 (digest guard is as strong as cSHAKE) |
| cell table | `CellTable.get_ofList` `Kernel/CellTable.lean:77` |
| lane-only (not on main) | `representsCheck_sound`, `toWorld_ofWorld`, `ofIntent_stale_refused` (`TurnOfIntent.lean:1583` on lane/turn-log), `preflight_of_admit`/`represents_of_admitted` (`Kernel/SnapRepresents.lean:470,495` on lane/turn-log), `Kernel/Bounds` relation theorems (lane/hp-1-bounds) |

## 6. FUNCTIONALITY + TODO PER LAYER

Branch tips are GitHub `gh/lane/*` as of the read (LANE: `git rev-parse`, `merge-base --is-ancestor 2c27b08b`).
"Merged" = an ancestor of main 2c27b08b. Rows are the journey/landing rows in `scripts/pipeline/required-rows`
(READ, 26-74). **Main's own standing run is not on disk in this checkout**: "PASS on main" below means "required
row, not on the known-red list" — the last recorded verdicts are v3.2's gate red=0 with NO landing verdict
(`ROOT-CONTINUATION-20261015.md` PAUSE). To settle per-row status, see §7 Q1.

Known-red on main (READ `required-rows:69-71`): **fleetsign** (cv 01a13985-48ef, `Kernel/NativeClientConsent.lean:55`
"remote challenge differs from locally prepared intent", hbox timing), **jpay/JPAY6** (cv 01a13c42-dc55, consent
allowlist refuses `continuityProviderResourceId`/`providerMetering`), **m6grain** (cv 01a13d9c-8a9d, spk-host makes
its own userns; hbox AppArmor). Pending: **births** (THE BAR, p99 ≤ 5 s writes, reopen ≤ 60 s, flips to required when
green at main), **HERMES-LIVE**, **jcertify**. Standing reds outside the gate: orphan modules
`Host.PrivateCircuitPlanFixture`, `Kernel.NativeCurrentMemberKey` (FOLLIES I2, LANE-log). The integration branch
`lane/v4-next` b5fd9ee1 is **red** at `Compiler/DurableReceiverCore.lean:1655` ("Loaded.mk has 24 explicit fields, but
only 23 were provided": consent-model `Loaded.prefixOwn` × turn-log 4a `Loaded.track`; fix proposed: compute the track
with `trackOf rootBytes image resumed`) (INTEGRATOR-LOG, LANE-log).

### 6.1 Kernel model (Kernel/World, Theory/Store, deployed registry)

- **Works on main.** The model and its theorems (§5.8); `turn-log-follower` export/follow over the deployed seed
  (`Host/TurnLogFollower.lean`), the totality pole `objective-turn-totality` 422/422 (LANE-log), first real fold 69/69
  records, 7/7 OB journey follower root = exporter root (TURN-LOG-LOG). **No row or gate runs
  `scripts/kern/turn-log-follower.sh`** (READ grep; WASTE-MODEL calls it "ungated").
- **Not proved / not wired.** `host_submit_is_step` (docstring only, `HostRefinesWorldCore.lean:75-99`).
  `SnapRepresents.parent = none`, `head = ∃ r` (§5.1). The Host does not run `World.admit`.
- **In flight.** TURN-LOG `lane/turn-log` **dbb4f0f4** (10 ahead of a5483db3; 83 files +3485/−1095):
  - **4a** 88e790b9 (`Loaded.track : WorldTrack`, open folds and decides, `prepareAppend` refuses what the World does
    not admit) — green 7421 jobs; merged only into `lane/v4-next`.
  - **CHARGE** 7877e6e7 — one storage rule (legs + born images + `History.eventBytes`); Host charge = World charge.
  - **guards** 45aadc74 — `Turn.pins : List (CellId × D)` (LANE `Kernel/World.lean:391`), `History.cellDigest`
    (:436), pin check first (`guardFailed`); world-sim receiver-only refusals 395 → 0.
  - **a0** dbb4f0f4 WIP — delete `Turn.absent` (absence = pin at `H.cellDigest none`); built green on burst4 only;
    world-sim gate NOT run.
  - HP-6 SIM (`lane/hp-6-sim` 75887614, merged into turn-log): `Kernel/TurnGen.lean` + `Host/WorldSim.lean` +
    `scripts/gates/check-world-sim` — seeded driver of the Host path against the follower, with crash-restart.
  - Next (log's order): rebuild a0 on hbox → world-sim PASS receiver-only=0 (re-record plants s1@41/s1@49) →
    (a) carries (`CarriedSegment.intent` exactCharge 0 → storageCharge) → merge hp-1-bounds → **step 2** → rows on
    fresh Stores → **step 1** → **4b** → **R5b**. The pole and follower rows are VACUOUS until the 7 retained Stores
    are re-emitted (they refuse at height 1 on the new charge).
- **Designed, not started.**
  - **TURN-LOG step 2** (`work/TURN-LOG-STEP2-BRIEF.md`): the ingress archive (DurableIndex family `archive`,
    event digest ↦ `StableEvent.canonicalBytes`, same `Transport.append` transaction); `DREGG.DURABLE.LOG` **v2 → v3**
    (`PersistedCodecTags.lean:209`); entry = `encodeTurnAt` with the event as its digest; the World's chain replaces
    the Store's; `recordsOf` rebuilds `IntentRecord` views from Turn + World + archive.
  - **step 1**: checkpoint = World v1 `{cells : CellTable, system : systemStream}` (`Kernel/WorldSystemCodec.lean`,
    on main; `CellTableCodec`/`WorldCheckpoint` drafts on `lane/turn-log-step1-wip` acc14e4e: take the files, not the
    commit); `durable_checkpoint_byte_v3 → v4`; epoch `checkpoint/v4 → v5`; no rootTree; open recomputes the root.
  - **4b**: `Loaded` holds the World; snapshot = view; append = `ofIntent → admit`; `Represents` := equality.
  - **R5b**: delete `execute`, `DataSnapshot.install`, `IntentRecord.writes`/`canonicalPostBytes`, `ReplayEnvelope`
    (20 files).
- **Twins in this layer**: see §6.10 rows K1–K15.

### 6.2 Deployed / durable store (Compiler/Durable*, Kernel/Durable*, store helper)

- **Works on main.** Open = anchor + one SQLite read + MAC'd checkpoint + suffix replay; append = CAS + readback +
  seal every 64; MMR history read at use (`verifyAt`); one index trie (spent, tx, presence, links, fleet);
  `WORLD-ROOT/v2` compressed trie with a kept `RootCache` (STORE-ROOT, merged as 30a080a6/340b2dd6/ca427c06); one
  cached checkpoint open (`openSealedWith`); STATE-AT 11c4226f merged (kept checkpoint bases; `atPrefix` deleted).
  Content-addressed `schemaRefs` in `StoreEpoch` (§5.4). Rows exercising it: `journey` J0–J8, JROT, JROTL, JAUDIT;
  `hostupgrade`; every OB row writes through it.
- **Measured waste (DOC `docs/WASTE-MODEL.md:23-38`, raw instructions at N=32 M=32 K=16, after STORE-ROOT):** birth
  29.4 G vs 15.2 M necessary (1,933×), invoke 12.4 G (1,647×), past read 10.0 G (6,656×), cold open 6.5 G (11×),
  session refresh p50 33 ms (~10,000×), current read 0.559 G (385×). Ceilings are pinned in `docs/waste-model.tsv` and
  may only fall (`scripts/gates/check-waste-model`).
- **In flight.**
  - STATE-AT-3 `lane/state-at-c2` **f7c998b6** (3 WIP commits; `Kernel/DurableEngine.lean` +702): umbrella green 13086
    jobs, rows PASS, past reads 2–3× faster at 30 k; TO DO: objective ratchet, squash, force-push as `lane/state-at`.
  - HP-1b BOUNDS `lane/hp-1-bounds` **e59ea490**: `Kernel/Bounds.lean` (LANE: `frameBytesMax 12102760`,
    `turnBytesMax := frameBytesMax`, `legsPerTurnMax 256`, `cellsTouchedMax 512`, `cellBytesMax 8388608`,
    `nullifiersPerTurnMax 64`, `batchTurnsMax 64`, `stateBytesMax 67108864`, relation theorems by `decide`), overBound
    as wire tag 15 with OUTCOME v6, `prepare` checks bounds first; Lean green 7587 jobs; Rust build, candidate, rows,
    frame and follower plants NOT run.
  - PERF-MEMO `lane/perf-memo` **77355fdf** (resident Host holds package replay + method fronts, `LoadMemo`): builds
    green; `--pin`, candidate, ON/OFF measurement and deleting `MINIDREGG_HOST_HELD` remain.
- **Designed, not started.** HP-3 LOOP (`Host/Resident.lean`, `Host/ResidentLoop.lean`, `appendBatch`: one transaction,
  one fsync, one tag per batch; linked store, not exec'd; `NativeHostLight` deleted) — HP-DESIGN §5.2. HP-5 ASSERT
  (needs `lean_set_exit_on_panic` via `@[extern]`; 55–56 `partial def`, 0 `panic!`/`assert!` in Kernel/Compiler/Host,
  READ grep). HP-2 BYTES+DIGEST (one flag day: `ByteArray` end to end, `Digest := {bytes : ByteArray // size = 32}`;
  4,798 lines mention `List UInt8` vs 329 `ByteArray` in Kernel/Compiler/Host, READ grep). HP-7 KECCAK (scalar
  `UInt64` lanes in `Theory/Sp800185Cshake256Fast.lean`; W14 ~17.4 k → ~1.2 k instr/permutation).

### 6.3 Host / server (Host/Main, Kernel/NativeHost*, receivers)

- **Works on main.** One `stdio` session per Store under `mini serve`; 184 active opcodes (§4.1); poisoned-session
  restart; storeless `codec` loop; dry run (op 130); every required row except the three known-red goes through it.
  Cold start is a gate (`check-host-cold-start.sh`); the Host closure is pinned (`host-closure.pin`, 776 modules).
- **Known-red.** fleetsign (consent challenge mismatch under interleaving, cv 01a13985-48ef).
- **Shape debts (READ).** `Host/Main.lean` is 9,163 lines; 51 `NativeAdmission` constructors
  (`Kernel/NativeHostReplay.lean:976`) with V2/V3/V4 families; 70 versioned/legacy module names in Kernel/Host/Compiler
  (`ls | grep -E "V[0-9]|Legacy|Historical"`); helper processes per request (store helper child per call, verifier
  per signature: `NativeCoprocess`, W13); `Opened` (full) beside `OpenedServed`/`Light` (light) opening; the
  session refreshes and re-verifies after its own commit (W6).
- **In flight.** HP-1b bounds (frame/turn/cell/nullifier refusals by name, outcome v6); PERF-MEMO (held entries by pin);
  TURN-LOG 4a (the append path refuses what the World does not admit).
- **Designed, not started.** **HP-3 LOOP**: `Resident {world, trie, held, retained, height, chain, archive, batch}`
  (HP-DESIGN §1.1), one loop (`drain → decode → admit → seal? → append → assert → reply`), batched durability (≤64
  turns, 2 ms, one fsync, one tag), ops 7-11 in-process, `NativeHostSession`/`NativeHostLight` deleted, zero execs per
  request (`strace` row). **HP-5 ASSERT**: pair assertions per §6 table of HP-DESIGN (head/chain after admit, journal,
  nullifiers, absent pins, meter, charge, trie leaf, codec pair, canonical read-back, chain/tag, Represents equality,
  seal reopen, held entry), needing `lean_set_exit_on_panic`. **SINS T4/T5/T6** (no lane): collapse the 51 admission
  constructors and the SPK v4 retry path onto OB rebirth (OB-WORLD §8.3/§8.5).

### 6.4 Compiler / Objective Bend

- **Works on main.** Parse (`Compiler/ObjectiveBendParse.lean:819`) → elaborate (`ObjectiveBendElaborate.lean:2037`) →
  proof-producing check (`Theory/ObjectiveBendTyping.lean:620`, `Checked`) → `accept` (`Compiler/ObjectiveBendFrontEnd.lean:304`,
  `Accepted` carries `packetTerm` and `checkedExact` as theorems) → `Package` (edition 3) → `publishedCore`
  (`ObjectiveBendPublication.lean:88`) → `Artifact` → pin `identity a = cSHAKE256 "DREGG.OBJECTIVE-BEND.SOURCE-ARTIFACT/v2"`
  (`ObjectiveBendSourceArtifact.lean:58`) → kernel `publish` (`Kernel/ObjectiveActivity.lean:2125`) / `create` → `invoke`
  (`Kernel/ObjectiveCall.lean:2314`, one of 16 `AdmittedTurn` constructors) → `runBounded` (`Theory/ObjectiveBendDemandMachine.lean:227`,
  `@[csimp]` fast path) → receipt (ops 212/213). Native route: `DeclaredResourceController.admitObjective`
  (`:2050-2088`) → `ObjectiveBendNativeAdmission.select/prepareCore/admit`.
  Theorems: `sourceStep_deterministic`, `runBounded_value_sound` (`Theory/ObjectiveBendDemandAdequacy.lean:27,3600`),
  `machine_evaluation_complete`, `typed_stepRaw_preserved`, `checked_reachable_no_refusal`, `execution_source_semantics`,
  `accepted_typed/never_refused/execution_semantics`, `Replayed.core_replayed`, `Program.runs_front_end_output`
  (`Kernel/ObjectiveActivity.lean:1264`), `admitted_source_semantics`, `ObjectLaw.compile_sound` (`Kernel/ObjectLaw.lean:507`).
  `ObjectiveProofs` (separate lib, 28 imports) gates the metatheory (`objective-proofs` gate); the C backend is
  checked by differential only (`objective-c`, `objective-cgen` with 1000 programs + 2 planted miscompiles).
  Rows: `objective` (not required, needs a lean env), `activity`, `seats`, `bounty`, `call` (C1–C8), `send` (S1–S13),
  `domain`, `upgrade`, `objectrecord`, `chargedfailure`, `rooms`.
- **Stated as not-proof (DOC `docs/OBJECTIVE-BEND.md:785,806-808`).** `mix_append`/`composition_associative` live on a
  separate list model with no theorem to `Term.mix`; `TotalProof law := law`; `checked_erasure`/`native_matches` are
  projections. Native objective admission is "integrated on scratch worlds, not deployed" (`:705`).
- **In flight.** PERF-MEMO (front end once per `(pin, fuel, maxBytes)`); OB-WORLD R-steps ride TURN-LOG (FD-1:
  ACTIVITY/COMMAND v12 → v13, SIGNED v2 → v3, claimed outcome = `H.turnDigest t`).
- **Designed, not started.** OB-WORLD R4 (package body ROM, today RAM), R5 (`step_conserves` at the Book), R6 (delete
  OB `Step` over `DataSnapshot`, SINS T10); one publish route and one invoke route (today two each, §6.10 H6).

### 6.5 Consent provider

- **Works on main.** Frames 220-233 (§4.2); anchored resume (frames 228/229); resident re-check (233); thin consent
  (230-232). Rows: `journey`, `call`, `send`, `seats`, `fleetsign` (known-red), `jpay/JPAY6` (known-red: allowlist).
- **Measured.** Consent per frame 19.5 G cold vs 1.63 G resident vs 3.8 M necessary (DOC WASTE-MODEL §0, W1).
- **In flight.** CONSENT-3 `lane/consent-model` **1e3ad928** (on 03d338ee, UNBUILT): Part A (963d9818, own bases
  only: `Loaded.prefixOwn`, `atPrefixFrom_own`, `OwnBase`, `Reader.ownOnly`, ≤16 retained bases) is in `lane/v4-next`;
  5fb20bc5 deletes the legacy scalar pair and checks `providerServices` (`Kernel/ProviderRouteConsent.lean`, fixes
  JPAY6); 1e3ad928 refuses the grain-runtime legacy branch. Real finding (LANE-log): `State.available` (the metering
  budget) is bound by neither the world root nor `Admissible`. Rows must stop writing into the real
  `~/.mini/consent-anchors` (`MINI_CONSENT_ANCHOR_DIR`, unverified).
- **Designed, not started.** **CONSENT Part B**: persist `MINI-CONSENT-FRONTIER/v1` = epoch tag ‖ Anchor ‖
  `DurableCheckpoint.State` at the anchor ‖ MAC, at `<anchor_dir>/f-<binding[..16]>.frontier` (0600); MAC key ruled by
  Ember 10-15 = a subkey `cSHAKE256(key = consent signing seed, "DREGG.MINI.CONSENT-FRONTIER-MAC/v1", binding id)`;
  `Kernel/ConsentFrontier.lean` with the persisted provenance stated as a trust premise; refusals by name (epoch,
  noncanonical, MAC, frontier ≠ anchor, root, cell-id set/`available`).

### 6.6 Codecs / wire

- **Works on main.** `StreamCodec` (in `Compiler/Tower256ConcreteBackend.lean:62`) and `LawfulCodec`
  (`Theory/IndexedProgram.lean:29`), both over `List UInt8`; 637 `@[persisted_codec_tag]` lines with a census that
  must equal the reachable tag set (`Compiler/PersistedCodecTags.lean:1-4`); content-addressed `schemaRefs`;
  `protocol/host-operations.json` + its generator/checker; `fn-wire` gate (fn grammar, pinned BLAKE3).
- **In flight.** CODEC-SHAPES `lane/codec-shapes` **e317c181** (167 files, +4710/−1610): item 1 canonical codecs
  (`encode_decodePrefix` a field of `StreamCodec`; 22 non-canonical decoders fixed, encodings unchanged; ~90
  strict re-encode sites deleted), item 2 `ByteArray` cursor (`decodeAt`/`cursorNative` + `@[csimp]`; codec-bench
  −67.6 % to −72.2 %); rows PASS at 58b3ae50. Item 3 (e317c181, moves `StoreEpoch` ⇒ re-genesis): 635 identities
  fingerprinted; rows not re-run; objective draft not done. `lane/codec-shapes-rust` **b90b8403** (needs rebase): 13
  hand-copied Rust digit loops deleted; no Rust decoder accepts what canonical Lean refuses.
- **Designed, not started.** CODEC-SHAPES item 3 completion: 8 owner-less fingerprints, the auto-bump path tested end
  to end, the 949 hand-written tag literals replaced by content-addressed `H(structural descriptor)` tags
  (HP-DESIGN §3, `#emit_persisted_codec_shapes`). **Rust twins**: codecs generated from the Lean descriptors
  (TWINS.md on hbox: 65 dual labels, 33 unregistered); `hiding.rs` `verify_view` → codec-child opcode 12; opcode 13 waits
  on Ember's blinding-key custody ruling. **HP-2** replaces `List UInt8`/`Nat` digests on every runtime path (§6.2).


### 6.7 Client (Rust)

- **Works on main.** `mini` with ~100 verbs (§4.5), `serve` supervising one Host child per Store, socket and `ssh:`
  relay transport, workspace on disk with `hostSha256` pinned at init (the per-call 173 MB hash is skipped when the
  pin answers; HP-DESIGN's item "never hashes the Host image" is half done: `session_invoke` still hashes for non-codec
  ops, `main.rs:595-612`, Rust-agent READ), resident consent provider by default, one codec child per process.
  Rows: `journey`, `m3` (provisioning), `m4` (shell), `sshe2e`, `welcomecontinuity`, `m8` (fleet), `fleetsign`
  (known-red), `jpay/*`, `exchange`.
- **Measured.** Current read 0.559 G vs 1.45 M necessary; W5 = one Lean process per `mini` for its codec child
  (0.38 G ≈ 68 % of a current read) (DOC WASTE-MODEL).
- **In flight.** `lane/codec-shapes-rust` b90b8403 (digit loops, `nat_prefix`); HP-1b generates the client's frame
  constants (`native/resource-client/src/bounds.rs`, LANE).
- **Designed, not started.** **HP-4 CLIENT** (`main.rs`, `transport.rs`, `client_consent.rs`, `workspace.rs`,
  `activity.rs`; `activity_world.py` probe deleted; `scripts/perf/workload.py`): delete `local_process` (a workspace
  without a socket is an error, not a fallback), one process per invoke (front-end quote read from op 214
  `pins[].frontEnd`, deleting `--prepare-only` probing), codec verbs over the socket, gate `op.read.current` ≤ 3×
  necessary and zero execs per op (HP-DESIGN §2, §5.2). Generate Rust codecs from Lean descriptors (CODEC-SHAPES item 3).
- **Shape debt.** 114 k lines for a layer that "decides nothing"; at least the decisions listed in §6.10 R-rows are
  made in Rust today.

### 6.8 Hosting / sandbox

- **Works on main.** SPK app sandbox with the full floor (`sandbox.rs:41-50`); user-mode broker; root only through the
  one-shot volume helper and newuidmap; Hermes workers under bwrap `--network none` with keys held by `mini-keys`;
  the candidate format (`deploy/candidate/package.py:57-95`: 16 roles, REQUIRED host, consent, mini, store, verifier,
  keys); systemd units for checkpoint certify (every 15 s, L = 256), clock tick (1 min), pay watcher (60 s), Discord.
  Rows: `m6grain` (known-red), `hermes` (declared absent on hbox: userns), `m7`, `hostupgrade`.
- **In flight.** SPK-NS `lane/spk-ns` **5919eb8b** (DONE, not merged, not in v4-next): spk-host stops making its own
  userns (AppArmor `unprivileged_userns` denied CAP_SETGID on hbox) and uses the broker-pinned bwrap + newuidmap +
  `setns()`; broker config v2 → v3 (refuses v2); `spawn_gate` reads POSIX ACLs; `install-user-world` grants/revokes
  per-app-uid `r-x` on the profiled bwrap; m6grain PASS r5 on hbox as mini-operator. Merging it removes the m6grain
  known-red line. BURST-NOROOT-HOST `lane/burst-noroot-host` 9066a518 (in v4-next): `--no-root` pipeline host mode,
  `with-lean-slot`.
- **Designed, not started.** Bring the Hermes worker profile to the SPK floor (`--cap-drop ALL --seccomp
  --disable-userns --new-session`; ASSUMED desirable, no lane names it). SINS T7/T8/T9 (two authority vocabularies:
  SPK's 4-field grain machine + Linux capabilities vs OB grants and laws; two state homes: app `/var` vs cells; two
  Hermes drivers: scripted ACP stand-in + `hermes-test-provider` vs live Hermes) — no lane. Docs to fix:
  `deploy/spk-host/README.md:36-60` and `docs/SPK-RESIDENT-PRIVILEGE-BOUNDARY.md:12` still describe the deleted root
  broker; `docs/WORLD-RUNBOOK.md §1` omits the consent and keys roles `package.py` requires.


### 6.9 Pipeline / gates

- **Works on main.** `scripts/pipeline/landing.sh` (stages: mk-lane from the warm base → TIP's `run-gate-burst.sh`
  (umbrella `lake build Minidregg +Host.Main:leanArts ObjectiveProofs` + `merge-gate-checks.sh`) → `publish-artifacts`
  (candidate READY set) → `pipeline-journeys.service` runs the tip's own `journey-runner` → `judge`), the
  baseline-relative verdict (`required-rows:17-25`; exits 10 gate red / 11 publish / 12 run / 13 rows), `required-rows`
  read from main's tree (a lane cannot drop its own rows), known-red lines with cv ids, pending rows that flip to
  required, the waste gate (ceilings only fall). `local-gates.sh` (25 gates) is the CI gate; `merge-gate-checks.sh`
  (builders / ledger / readers) is the landing gate.
- **Known-red / gaps (LANE-logs, DOC).** v4-next red at `DurableReceiverCore.lean:1655`; the gate lists in
  `local-gates.sh` and `merge-gate-checks.sh` diverge (9 gates only in the first, 10 only in the second); a
  SIGKILLed `build-native-host.sh` leaves its mkdir seat forever (nothing checks `owner.txt`'s pid,
  `build-native-host.sh:383-426`); `births` can never flip to required on a box that is never quiet
  (`journey-rows:633-637` returns 98 under load, contradicting `docs/PIPELINE-HBOX.md:124-126`); five gate scripts
  nothing calls (`check-objective-machine-perf.sh`, `check-repository-trust.sh`, `check-tower-controller.sh`,
  `check-char2-vacuity.sh`, `kern/check-native-fixture-transcripts.sh`); `step_JJOBM` defined twice in `journey.sh`
  (:1053, :1060).
- **In flight.** INTEGRATOR v4 `lane/v4-next` **b5fd9ee1** (42 ahead of main; merges census-review, consent-model Part A,
  turn-log 4a, hyp-instances, guards, m6grain-hbox, hp-design, burst-noroot-host, seat-count): fix :1655, merge
  hp-1-bounds, floors, codec-shapes; then objective draft, candidate, rows, land — now "lane tips to main in 3
  batches", hbox one slot only (STALL-WATCH 10-16). `with-lean-slot` (FIFO PID-file tickets) exists only on
  `lane/burst-noroot-host`/`lane/v4-next`. GUARDS e22cdedc (70 `#guard` → 0) and HYP-INSTANCES 357273ab (allowlist
  75 → 48) are in v4-next. CENSUS-REVIEW `gh/lane/census-review` 2287f581 (WIP 95861a59 only on hbox3; GitHub tip
  disagrees with the PAUSE note — §7 Q8). FLOORS-2 `lane/floors-rebase-wip` **743fc5ce** (issuer cap accepted;
  `isIssuerMint` deleted; `Book.floors`; tags `DREGG/RESOURCE/3`, `RESOURCE.STATE/v3`, `GENESIS-SOURCE/v6`): objective
  draft, candidate, fixture re-emit, rows remain.
- **Designed, not started.** FOLLIES F1–F10 + I1–I10 (`work/FOLLIES-20261014.md`): F4 delete the closure-hash
  objective ledger (decided; `objective-contract-changes.txt` ~60 MB, no lane executes it), F7 compute host-closure,
  F8 delete always-UNCONFIGURED rows, F10 one shrink-only trust list instead of 4,107 `#assert_axioms` lines. HP-6 SIM
  as the gate for every range (on lane/turn-log; not on main).

### 6.10 Twins: two shapes of one thing (every one found; ID · the two shapes · where · who deletes it)

**Kernel model / store (K)**

| id | shape A | shape B | where (READ unless LANE) | deleted by |
|---|---|---|---|---|
| K1 | `World`/`Turn`/`World.admit` (spec) | `DataSnapshot`/`DataIntent`/`execute` (runs) | `Kernel/World.lean:264,370,607` · `Kernel/DurableDataIntent.lean:99,193,429` | TURN-LOG 4b + R5b |
| K2 | log entry = `IntentRecord` (+`canonicalPostBytes`) | log entry = compact `Turn` (`encodeTurnAt`) | `Kernel/DurableReceiver.lean:66` · `Kernel/DeployedTurnCompact.lean:300` (follower only) | TURN-LOG step 2 |
| K3 | Store chain: cSHAKE over `IntentRecord` bytes | World chain: `H.chain` over `H.turnDigest t` | `DurableCheckpointCodec.lean:505-513` · `World.lean:461-469`; unbound by `SnapRepresents.head : ∃ r` | step 2 |
| K4 | deployed root `entriesOf` over `rootBytes` of cell bytes | `WorldRoot.rootOf` over the World's slot roots | `DurableReceiverCore.lean:454` · `WorldRoot.lean:290` | implied by 4b; **no step names it** |
| K5 | spent: `Snapshot.consumed`, index-trie family, DurableView overlay, authority-domain projection | `SysSpace.spent` | `HostRefinesWorldCore.lean:388` (relation) | 4b (via R3) |
| K6 | journal: `Snapshot.journal`/`lookupRecorded`/`Loaded.txs`/trie | `SysSpace.journal` | `HostRefinesWorldCore.lean:390` | 4b + archive |
| K7 | clock: `NativeHost.logicalHeight` = genesisHeight + h | head height | `HostRefinesWorld.lean:27` | 4b |
| K8 | parentage: authority cell plane 13 | `SysSpace.parent` | `HostRefinesWorldCore.lean:398` (`parent = none`) | 4b / T7 |
| K9 | `Turn.absent` | pin at `H.cellDigest none` | `World.lean:383` · LANE turn-log a0 | TURN-LOG a0 (WIP) |
| K10 | state-derived guard legs / `DeployedTurnCompact.cellDigest` | intent's `expectedPre`/`expectedRoot` as `Turn.pins` / `History.cellDigest` | `DeployedTurnCompact.lean:111` · LANE `World.lean:391,436` | TURN-LOG guards (on lane) |
| K11 | full opening `Opened`/`Loaded` | light opening `OpenedServed`/`NativeHostLight.Light`/`DurableServed.Opening` | `NativeHostContext.lean:439` · `NativeHostServed.lean:39` · `NativeHostLight.lean` | HP-3 (Resident) |
| K12 | Host storage charge (image bytes) | World meter (patch bytes); `storage ≤` | `HostRefinesWorldCore.lean:394-395` | TURN-LOG CHARGE (on lane) |
| K13 | ATLAS hyperedge `Kernel/Turn.lean` `Hyperedge`; `TypedCellHyperedge`; `MultiCellHyperedge`; `DurableCommitProtocol` carrier | `World.Turn` | `Kernel/Turn.lean:38`, `MultiCellHyperedge.lean:206`, all in the Host closure | **no lane** |
| K14 | OB invariant `Step` over `DataSnapshot` | `WStep := Admissible ∧ World.step` | `Kernel/ObjectiveCheckpointInvariant.lean:1683-1697` (SINS T10) | OB-WORLD R6 |
| K15 | CarriedSegment charges 0 but writes | every other write is charged | LANE-log `CarriedSegment.intent` exactCharge `:210` | TURN-LOG (a) carries |

**Host / admission (H)**

| id | shapes | where | deleted by |
|---|---|---|---|
| H1 | 51 `NativeAdmission` constructors with V2/V3/V4 families; 70 versioned/legacy module names (`ApplicationLifecycle{Begin,Claim,Completion}{V2,V3}*`, `…RetryV4*` (≈30 files), `FnEmptyPoll*V2`, `PayEnrolV2*`, `PayCellLegacyV4`, `LegacyContent*`, `LegacyStoreCarry`, `SourceAgreementLegacy*`, `MinidreggV1*`) | `Kernel/NativeHostReplay.lean:976`; `ls Kernel Host Compiler` | **no lane** (SINS T4; OB-WORLD §8.5 names the direction) |
| H2 | SPK v4 failed-create retry (`RetryHistory`, `BeginAtV4`…, `lifecycle_v4_retry_*.rs`) | OB "retry is a new birth" | `NativeHostReplay.lean:725` | OB-WORLD §8.3 (no lane) |
| H3 | `ApplicationGrain` begin/claim/completeUpgrade | OB `adopt`/`migrate` (`ObjectiveUpgradeInvariant`) | `Kernel/ApplicationGrain.lean:372,394` | no lane (SINS T6) |
| H4 | one-shot CLI verb for every session op (`prepare`, `submit`, `lookup`, …) | the session op | `Host/Main.lean:7961-8108` vs `:2047` | HP-4 deletes the client's `local_process` caller |
| H5 | bounds scattered: `maxFrame = FnEvidenceCodec.maxHostFrameBytes`, `RetainedSegmentInspection.maxLookupFrame`, `GrainResourceBirthPolicyController.maxSourceBytes` | `Kernel/Bounds` | `Host/Main.lean:2669,2677`; `Compiler/FnEvidenceCodec.lean:88` | HP-1b (lane) |
| H6 | two publish routes (kernel `publish` turn; content-atom publication `"authority": "none"`) and two invoke routes (`ObjectiveCall.invoke`; `DeclaredResourceController.admitObjective`) | | `Kernel/ObjectiveActivity.lean:2125`, `Host/ObjectivePackageAuthor.lean:43-80`; `Kernel/ObjectiveCall.lean:2314`, `DeclaredResourceController.lean:2050` | no lane |
| H7 | `MINIDREGG_HOST_HELD` knob | | LANE perf-memo | PERF-MEMO after measuring |

**Codecs / digests (C)**

| id | shapes | where | deleted by |
|---|---|---|---|
| C1 | Digest ×5: `Digest {value : Nat}`; `Digest256 := Fin (256^32)`; `Digest := Blob 32`; `Digest32 := Fin 32 → Fin 256`; Selvage `Fin 8 → F` | `Theory/TypedAuthorization.lean:53`; `Compiler/Tower256ConcreteBackend.lean:401`; `Kernel/DomainEpoch.lean:58`; `Compiler/BfvInputValidity.lean:36`; `Selvage/BaseFoldPoseidon2.lean:39` | HP-2 (one 32-byte `Digest`) |
| C2 | `List UInt8` (4,798 lines) | `ByteArray` (329 lines), `abbrev Bytes := List UInt8` defined 3× | `Kernel/ObjectiveActivityWire.lean:31`, `Kernel/GenericSimplex.lean:13`, `Kernel/PortableContinuationManifest.lean:14` | HP-2; CODEC-SHAPES item 2 (cursor) |
| C3 | `LawfulCodec` | `StreamCodec` | `Theory/IndexedProgram.lean:29` · `Compiler/Tower256ConcreteBackend.lean:62` | no lane names it |
| C4 | strict re-encode wrappers (strictCodec/framedRaw/rawCodec) | canonical `StreamCodec` with `encode_decodePrefix` | ~90 sites on main | CODEC-SHAPES item 1 (lane; four kept) |
| C5 | hand-written tag literals (949) + counter tags | `H(structural descriptor)` | `PersistedCodecTags.lean` | CODEC-SHAPES item 3 |
| C6 | package/artifact identity cSHAKE256 (`Digest`) | `Package.frontEnd` = hex SHA-256 of a source manifest | `ObjectiveSourcePackage.lean:68` · `ObjectiveBendFrontEndIdentity.lean:48-51` | no lane |
| C7 | proven-equal fast twins (`decodeRecord`/`Fast`, `stepRaw`/`Fast`, `runBounded`/`Fast`, `forceWith`/`Fast`, cSHAKE spec/fast) | — | `@[csimp]` (acceptable: proved equal; not counted as debt). `Compiler/{EmitSystemFast, NatDigits255Fast, ObliviousEmbedFast, PrivateCircuitAllocationFast}` not checked for `@[csimp]` (§7 Q6) | — |
| C8 | `Diagnostic` defined twice | | `Compiler/ObjectiveBendParse.lean:172`, `Compiler/ObjectiveBendFrontEnd.lean:33` | — |
| C9 | term shapes `Term`, `ATerm`, `AnnotatedTerm`, `Data`; `ObjectiveBendExtensions` list model vs `Term.mix` (no theorem) | | `Theory/ObjectiveBendOpenRecursion.lean:21`, `Compiler/ObjectiveBendElaborate.lean:322`, `Theory/ObjectiveBendTyping.lean:144`, `Theory/ObjectiveBendExtensions.lean:70` | — |
| C10 | C demand machine | Lean demand machine (differential only) | `native/objective-emit/runtime.c:1-13` | — (by design a backend; refinement unproved) |

**Rust ⇄ Lean (R)** (Rust-agent READ; "guard" = what holds them together)

| id | Rust | Lean | guard |
|---|---|---|---|
| R1 | `hiding.rs:69-330,445` hand cSHAKE/KMAC (`left_encode`, `bytepad`), `DREGG.STORE.SALT/v1`, `…LEAF/v1`, `ROOT/v2`, blinding ratchet, `verify_view` | `Compiler/StoreCodec.lean` hiding root, `Compiler/Sp800185Kmac256.lean` | one KMAC vector (`hiding.rs:537-548`); no root vector found |
| R2 | `mini-sdk/src/contracts.rs` intent codec, `integer_value`, `canonical_json` | `Kernel/Contracts/Intents.lean` | golden vectors + dlopen test (guarded) |
| R3 | `client_consent.rs:277-290` `stream_nat`/`stream_byte_list` (frame 232 payload) | `StreamCodec.nat`/`list` | none found |
| R4 | `spk-host/src/lifecycle_v4_retry_native.rs:77-120,291,322` v4 retry frames + retry selection | `Host/ApplicationLifecycleRetryBeginV4Authoring.lean`, `Kernel/ApplicationFailedCreateRetryEvidence.lean` | — (and a Rust-side decision) |
| R5 | `pay_memo_v2.rs:87-623`, `join_solana.rs:11-33` enrol memo encode/decode/verify | `Kernel/PayEnrolMemoV2.lean` | — |
| R6 | `key_rotation.rs:150-160` next-possession frame | `ParticipantKeyEnrollment.nextPossessionFrame` | rechecked at runtime against the Host's bytes |
| R7 | `market.rs:45` hashEq commitment; clearing allocation decided in Rust (`settle` :476), law only bounds it | `Pred/HashEq.lean` | — (a Rust-side decision) |
| R8 | `private-backend/src/codec.rs` "canonical subset of `PrivateSuccessorCustodyCodec`" + 4 `fn nat` copies | `Compiler/PrivateSuccessorCustodyCodec.lean` | codec-shapes-rust deletes the copies |
| R9 | `claim_descriptor.rs:45` `DREGG/SPK-IMAGE/v1` | `Kernel/ApplicationSpkPackageIdentity.lean` | — |
| R10 | `native_dispatch.rs:14-95`, `dispatch_native.rs:703,1282` committed-permit/attestation parsing | `Kernel/ApplicationDispatchProjection.lean` | tag "only framing" |
| R11 | `transport.rs:306-616` socket op filters (with stale operator arms 130-133 = "C14 TAIL-BOUND", `:591-595`) | `protocol/host-operations.json` | `host-operations` gate (does not catch the stale arms? §7 Q9) |
| R12 | `workspace.rs:107-121` `readable_delegation_verbs` decides parent scope + observe | the Host's delegation receiver | ASSUMED re-decided by the Host |
| R13 | `mini-keys/src/server/native.rs:34-45` authorizes from op 144; domain `mini/member-provider-action/v1` Rust-only | — | — (a Rust-side decision) |
| R14 | v2 socket envelope built 3× (`transport.rs:1110-1120`, `spk-host dispatch_native.rs:531-541`, `mini-keys server/native.rs:55-59`); `MDCOPRC1` serve loop 2× (verifier, sqlite-store) | `Compiler/NativeCoprocess.lean` | Rust–Rust copies |
| R15 | ~50 local `canonical_decimal`/`decimal` fns (spk-host ≈25, resource-client ≈20, grain-runtime 4, …) beside `mini_sdk::decimal` | Host JSON natural parsing (ASSUMED) | — |
| R16 | 65 Lean/Rust dual labels, 33 unregistered (TWINS.md — on hbox only; **not on any `gh/lane` ref**, Rust-agent READ `git ls-tree`); SINS T2 counted 53 incl. `NATIVE-HOST/OUTCOME/v5` in 8 spk-host files | the Lean tags | CODEC-SHAPES item 3 |
| R17 | `explain.rs` | `mini-sdk-ts/src/explain.ts` | wasm differential |

**Pipeline / docs (P)**

| id | shapes | where |
|---|---|---|
| P1 | `local-gates.sh GATES` vs `merge-gate-checks.sh` (9 gates only in the first, 10 only in the second; deploy-scripts command copied verbatim) | `local-gates.sh:84,126` · `merge-gate-checks.sh:158` |
| P2 | four lock mechanisms: lib.sh flock slots, slot-mk gate flock, build-native-host mkdir seats, lane-only `with-lean-slot` | `lib.sh:54-90`, `slot-mk.sh:9-11`, `build-native-host.sh:341-426` |
| P3 | two bwrap profiles with different floors | `deploy/grain-host/bwrap:116-138` · `spk-host/src/sandbox.rs:41-50` |
| P4 | four umbrella target sets (gate, `ub.sh`, `rb.sh`, `build-native-host --umbrella`) | `run-gate-burst.sh:18`, `scripts/lane/` |
| P5 | four "fast enough" bars (births p99 ≤ 5 s; growth max ≤ 5 s at 1000; perf < 180 s; waste ceilings) | `journey-rows:579-649`, `waste-model.tsv` |
| P6 | two candidate builders (`build.sh`, `lane-build.sh`) | `deploy/candidate/` |
| P7 | `step_JJOBM` defined twice | `journey.sh:1053,1060` |
| P8 | root broker vs user broker in the docs | `deploy/spk-host/README.md:36-60` vs `USER-TENANCY.md` |
| P9 | `growth` (updates) vs `births` (THE BAR) | FOLLIES F1 |
| P10 | seat-count commit cherry-picked 4× (4a83fdb7, e7038991, 743fc5ce, 8c00ac15) | INTEGRATOR (LANE-log) |

## 7. OPEN QUESTIONS (could not be settled by reading)

Each with the narrowest thing that would settle it. None needs a full test suite.

1. **What PASSes on main 2c27b08b right now, row by row?** The checkout holds no `results.tsv`; v3.2 had gate red=0
   and no landing verdict before the pause. Settle: on hbox, read `$JOURNEY_ROOT/2c27b08b/results.tsv` if the standing
   run exists, else run `scripts/pipeline/landing.sh 2c27b08b` once in hbox's one quiet slot (it builds the warm base,
   gate, candidate and standing run and prints "new reds vs baseline" and "required unmet").
2. **Is `host_submit_is_step` provable as stated, or is the statement wrong?** It is a docstring
   (`Kernel/HostRefinesWorldCore.lean:75-99`). Settle: write it as a `theorem … := by sorry` in a scratch file against
   main and `lake env lean` it (does it typecheck?), then decide whether TURN-LOG 4b makes it trivial (`Represents` :=
   equality) and should be stated then instead.
3. **Do the deployed root (`entriesOf`, cell `rootBytes`) and `WorldRoot.rootOf` of the represented World agree?**
   (twin K4; no step owns it.) Settle: in `Host/WorldSim.lean` (lane/turn-log) assert
   `loaded.worldRoot = WorldRoot.rootOf … world` per step over seeds 1–20 × 300 (`world-sim` exe), or read whether
   `turnLogRoot` (`Kernel/TurnLog.lean:194`) is already that function.
4. **Does the follower journey still pass on main?** No gate or row runs `scripts/kern/turn-log-follower.sh`.
   Settle: `lake build turn-log-follower` and run it over `kern/objective-turn-totality.sh`'s STORES.json once (7
   Stores). TURN-LOG-LOG says the retained Stores refuse at height 1 on the lane's new charge rule; on main they
   should still fold.
5. **Is `State.available` (the metering budget) really unbound by the world root and by `Admissible`?** (CONSENT-2
   finding, LANE-log.) READ: `stateEntries` (`Compiler/DurableCheckpointCodec.lean:598`) puts only the system leaf and
   the cells under the root; `available` is covered by the checkpoint MAC (body hash) but not by the root, so whoever
   holds the Store's MAC key (the operator) can seal a different budget that every root check accepts. Settle: plant
   a checkpoint with a changed `available` under a valid MAC (`scripts/consent/own-base-plant.lean` on
   lane/consent-model is the closest plant) and see whether any open, or any consent provider on an own base, refuses.
6. **Are `Compiler/{EmitSystemFast, NatDigits255Fast, ObliviousEmbedFast, PrivateCircuitAllocationFast}` proved-equal
   `@[csimp]` twins or unproved duplicates?** Settle: `grep -n "@\[csimp\]" Compiler/*Fast.lean`.
7. **Is native Objective Bend admission (`.objectiveMethod`) registered by any deployed genesis, or scratch-world
   only?** (`docs/OBJECTIVE-BEND.md:705` says scratch-only.) Settle: grep the genesis producers
   (`Kernel/NativeHostGenesis.lean`, `deploy/candidate/params.sh fill-genesis`) for the route.
8. **Which census-review tip is real?** `gh/lane/census-review` is 2287f581 in this checkout; the PAUSE note says
   95861a59 is on GitHub; 95861a59 is only on `hbox3/lane/census-review`. Settle: `git ls-remote
   git@github.com:emberian/minidregg.git refs/heads/lane/census-review`.
9. **Does `scripts/host-operations.py check` see the stale operator arms for ops 130-133 in `transport.rs:591-595`?**
   Settle: read `rust_routes` (~`host-operations.py:220-275`), or run `python3 scripts/host-operations.py check`
   (pure, no Lean).
10. **Where is TWINS.md (65 dual labels, 33 unregistered)?** It is cited by HP-DESIGN and the CODEC-SHAPES log but is
    on no `gh/lane` ref. Settle: `ssh hbox ls /tank/dregg-build/claude-lanes/*/TWINS.md` and commit it to
    `lane/codec-shapes-rust`.
11. **Does the ML-DSA half of hybrid signing have a Lean caller?** The verifier names
    `CredentialSignatureIO.combineHalves`, and the SDK signs under `MINI/SDK/HYBRID/ML-DSA-65/v1`, but no `.lean` file
    mentions `verify-mldsa`/`combineHalves`. Settle: `git grep -n "combineHalves\|verify-mldsa" $(git for-each-ref
    --format='%(refname)' refs/remotes/gh/lane)`.
12. **Can the sealed-market law accept a different but bounded allocation than the one Rust computes?** (R7.)
    Settle: read `deploy/shell/templates/market/sealed/law.market` with `Kernel/SealedMarket.lean`'s guarantees; if
    the law only bounds, the clearing is a Rust decision and belongs in Lean.
13. **How much of `Kernel/Turn.lean`/`TypedCellHyperedge`/`MultiCellHyperedge` is load-bearing for the deployed
    path?** They are in the Host closure. Settle: `lake env lean` a scratch file that `#print`s the reverse
    dependencies, or trace which receivers construct a `MultiCellHyperedge.Commit` at runtime (grep in
    `Kernel/Hyperdocument*Publication*` callers from `Host/Main.lean`).
14. **Seats leak on SIGKILL.** `build-native-host.sh:383-426` never reclaims a seat whose `owner.txt` pid is dead.
    Settle: read `with-lean-slot` on `lane/v4-next` (it prunes dead PIDs) and decide whether it replaces the mkdir
    seats.
15. **Will `births` ever flip to required on hbox?** Its flip needs a PASS at main, but `row_births` returns 98 on a
    non-quiet box. Settle: check whether main baselines on hbox are taken quiet (`box.py quiet` log in the standing
    run).
16. **Is the 12-module Selvage residual in the Host closure removable by moving `StreamCodec`/`digestStream` out of
    `Compiler/Tower256ConcreteBackend.lean`?** Settle: `lake env lean` a scratch module that imports only the codec
    pieces, and recompute the closure with `scripts/check-host-closure.sh` on a lane.
