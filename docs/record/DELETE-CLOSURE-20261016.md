> record copy of redregg/work/DELETE-CLOSURE-20261016.md, 2026-10-16; the lane logs stay in redregg

# DELETE-CLOSURE — the module graph of Mini main 2c27b08b (short form)

DISCOVER-CLOSURE, 2026-10-16. **Cut short by ROOT's order** (the scholar became BUILD-GATES for
~/dev/nanodregg). What is here is measured; the full per-cut theorem audit (gate/census citations) was
NOT done. Tags: READ = read at path:line; DERIVED = from my import-graph script (header parser =
`scripts/lean_imports.py`, the same reader the gates use); ASSUMED = inference.
Scripts + graph: `/private/tmp/claude-501/-Users-ember-dev-breadstuffs/b3795e84-08d4-436c-9079-91d4e05687e9/scratchpad/dc/{g.py,lib.py,r1..r9.py,graph.json}`.

## 1. Closures (DERIVED; 1,620 .lean files, 585,988 lines in tree)

| root | modules | lines |
|---|---|---|
| minidregg-host (Host.Main) | 776 | 320,587 (Kernel 405, Compiler 158, Theory 107, Host 87, Selvage 12, Pred 7) — matches `scripts/gates/host-closure.pin` |
| minidregg-client-consent | 645 | 278,980 |
| objective-turn-totality / turn-log-follower / consent-specialized | 616 / 618 / 615 | ~273 k |
| minidregg-four-source-fixture | 599 | 264,105 |
| Deployed | 940 | 377,909 |
| ub.sh set (Deployed + exe + every Host.* + AxiomCensus) | 992 | 384,463 |
| gate burst (Minidregg + Host.Main + ObjectiveProofs) | 1,319 | 545,152 |
| local-gates lake-build (all libs but ResearchWip + all 18 exes) | 1,387 | 558,434 |
| orphans (no lib/exe root reaches them) | 96 | 9,033 (57 scripts/, 11 docs/evidence, 9 tests/, 8 Host: BendCommitmentIR2Emit, BendTraceIR2Emit, ObjectiveBendFrontEndMain, ObjectiveStudioPublication, PortableContinuationProbe, PrivateCircuitPlanFixture, SourceAgreementReader, WorldPrototypeDefinitionAuthor; + Kernel.Contracts.IntentVectors, Compiler.PrivateBackendBoundaryFixture, 2 Verify) |

Nine exes are referenced by no script/journey (world-fold-bench, world-root-bench, kn2-store-bench,
nock-eval, cshake-bench, codec-bench, minidregg-carry-verifier, 4× generic-simplex/four-source) (DERIVED grep
of scripts/ deploy/ journey.sh) — yet `local-gates.sh:83-84` builds every lakefile exe.

## 2. Research inside the Host closure — the lesson

The 12 Selvage modules (7,457 lines: Accumulator, BinaryLookup, Commitment, ConstrainedCode,
CorrelatedAgreement, Decider, Depth, MultilinearExtension, Rbr, ReedSolomon, Sumcheck, SumcheckReduction)
enter through ONE inverted edge, not two: the deployed hash imports the PCS.

    Host.Main → Kernel.ObjectiveBendNativeAdmission → Compiler.Evaluator → Compiler.Sp800185Cshake256
      → Compiler.Tower256CshakeMerkleController → {Compiler.AuthenticatedColumnPlan → Selvage.Commitment,
                                                   Selvage.BinaryLookup}           (DERIVED shortest path)

- `Compiler/Sp800185Cshake256.lean:19` imports the Merkle controller only for `structure Cshake256`
  (`Tower256CshakeMerkleController.lean:54`) and `XofRequest`/`checkedXofCall` (:376,:383) (READ).
- `Compiler/Tower256ConcreteBackend.lean:20` (the deployed `StreamCodec`/`digestStream`/`bytesStream` home)
  imports `BinaryTower256Profile` only for `backend` (:794) and the PCS transcript codecs (:539-857);
  name search finds no Host-closure use of anything at or after :539 (DERIVED, textual; collisions possible).

**Cut C1** (move `Cshake256`+`XofRequest`+`checkedXofCall` into Sp800185Cshake256; reverse the edge) +
**C2** (split ConcreteBackend at :539, PCS half becomes a research module): Host closure **776 → 740
modules, 320,587 → 303,144 lines (−36, −17,443)**; Selvage in Host **12 → 0**; Deployed 940 → 910; it also
drops Compiler.BabyBear, Emit, EmitSerialize, Air{Bignum,Flatten,Hash,Membership,ModularView}, NoteSpend,
NativeKernelPlan, BignumKernelABI, SemanticArtifactBundle, MinidreggV1Artifact, TranscriptController,
Theory.BinaryTower* (5), Theory.CrossModulus (DERIVED simulation, r7.py). Each edge alone drops 0 and 10.
Selvage.CorrelatedAgreement today has 576 dependents inside the Host closure (it sits under the hash).

Proof-only modules in the Host closure (theorems, no defs; DERIVED): Compiler.FnWireRoundTrip,
Kernel.GenericSimplexQuorum, Kernel.PhysicalResourceReadGuard, Theory.ObjectiveBendCheckpointRoundTrip,
Theory.ObjectiveBendDemandPreservation (+Cases.Arithmetic, Cases.Records) — 7 modules, 2,200 lines.

Heavy modules: Kernel.PayEnrolProofs (8,715 s) is NOT in Host (Deployed only, 0 Host dependents) → move to
nightly costs nothing at the Host. Kernel.PayEnrolV2Legs (7,311 s, 434 lines) IS in Host with 136
dependents; PayEnrolV2Receiver 133; Kernel.Job 134. Assurance.NativeAcceptedFixture{,Projection,Authority,
Data} are in Minidregg only (not Host, not Deployed) (DERIVED).

## 3. Hubs (dependents inside the Host closure; defs / theorems / #guard counts DERIVED by regex)

| module | Host dependents | lines | defs | thms |
|---|---|---|---|---|
| Theory.AxiomPin | 637 | 41 | 1 | 0 |
| Theory.IndexedProgram | 624 | 273 | 24 | 7 |
| Theory.TypedAuthorization | 616 | 1,557 | 77 | 81 |
| Theory.Store | 611 | 653 | 37 | 40 |
| Theory.ReactiveReceipt / GuardedAdvice / ReactiveController | 608 / 608 / 607 | 277 / 349 / 453 | mixed | mixed |
| Theory.AuthorizationDeclaration | 594 | 823 | 45 | 23 |
| Theory.AssertAxioms | 593 | 84 | 5 | 0 |
| Theory.Sp800185Cshake256Fast | 585 | 880 | 29 | 202 |
| Compiler.Signature | 582 | 495 | 27 | 22 |
| Compiler.Air / AirRange | 581 / 579 | 182 / 375 | 13 / 10 | 5 / 19 |

Every top hub mixes defs with theorems, so a proof edit rebuilds ~600 modules. Lesson for nanodregg: the
def/proof split is a gate, and the hash/codec spine must import nothing proof-system.

## 4. Not done
Per-cut theorem audit against AxiomCensus / TokenCensus / objective manifest / hypothesis ledger; the
"zero-reference" vestigial scan; Effects/Kernel.State/Hyperedge confirmation.

## 5. Caveat on C1+C2 (DERIVED, unverified)
A name-level scan of the retained Host closure after the C1+C2 simulation found possible real uses of dropped
modules: `Coordinate` (Theory.BinaryTowerCodec) in Kernel.TypedCellHyperedge, Kernel.MultiCellHyperedge,
Kernel.DurableCommitProtocol; `Tower256` in Compiler.Sp800185Cshake256; `BindingCommitment` (Selvage.Commitment) in
Theory.AuthMap. Most other hits were common words. So −36 modules is an upper bound until someone builds the cut.
