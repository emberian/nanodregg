# PE1 Census tooling: scoped release

ROOT's scoped release follows CONSOLIDATION-MAP-20261021.md §6: the real Kernel
environment exporter, retained-term kernel replay, audit, finite receipt records,
journal validation and derived index land as Census tooling. The only new Lean
modules are Census.JournalExpr, Census.Journal and Census.JournalRun. Their import
closure contains no Lang.Contextual module. The consolidation's S0 impact analysis
and statement digest work are the intended next consumer.

Census.JournalRun now checks finite receipt records directly. It defines no
CalculusData instance, substitution or hypothetical typing judgment. Receipt
revision, successful result, complete coverage, input versions, availability,
blockers and supplied cost remain separate fields and checks. Kernel replay
remains Lean's separate command; an exhausted receipt never asserts theorem falsity.

The unlanded Lang Journal data/proof/teeth modules and their 21 theorems are
excluded. The toy-world command and its two active matrix cases are removed.
The active matrix has 13 cases; archived cycle-grounding/alternative-worlds outputs
below remain historical only. No repair/composition theorem is claimed for this
landing. Index/list and sequential/batch comparisons are executable observations
on fixed finite receipt sets. Existing gates remain authoritative.

The excluded sources and original full pilot sources are preserved privately in
logs/CX-READER-PE1-excluded and logs/CX-READER-PE1-prescope. No landed theorem,
Kernel signature, production check, pin or gate is removed or weakened.
PRICE PREMISES: none; landed statements restated: none; new theorems: none.

## Historical comparison before scoped release

Everything below through the second-reader additions records the original
15-case experiment at fe89edf using the now-excluded Closure adapter. It is retained
as evidence, not a claim that those modules or toy-world cases are shipped. Current
Census-only validation is reported separately at the end. The historical adapter's
formal claims do not become theorems about the new Census command.

### Original comparison: one Kernel slice, three observations

Run date: 2026-10-21. Checked source base: fe89edfe72f73fa17c14b28a42f81d1998337087. Kernel files and landed signatures are unchanged. PRICE PREMISES: landed theorems gaining hypotheses: none; restated: none.

Raw matrix: /tank/dregg-build/nanodregg/logs/CX-PE1-run4. Final explicit-result finite receipts: /tank/dregg-build/nanodregg/logs/CX-PE1-final1. The append-only events.jsonl retains original and subsequent observations; it is replayed by gates/journal.py inspect. Eight persistent obligations have sixteen archived candidate routes. Every edit branches from the same checked baseline, rather than being silently accumulated.

A is the landed Closure.judge over archived finite receipts. B independently kernel-checks all 2520 saved theorem terms against current types, then requires success throughout each old root's support cone. C freshly elaborates each of eight saved source recipes under the current scratch environment and fixed budget. B and C are recorded separately; no failing C overwrites a successful retained B receipt. A's non-admission is evidence unavailable for that revision, not a false theorem.

V = verified, I = inputMismatch, R = receiptMismatch, S = suspended, P = pruned. B/C columns count roots accepted, not theorem terms. Residual candidate work can remain when another route discharges the obligation; owed counts roots with zero surviving routes.

| Edit | A: 16 candidate statuses | B / 8 | C / 8 | Owed / 8 | Surviving alternatives (roots with 0/1/2) |
|---|---|---:|---:|---:|---|
| unrelated | 8I, 8V | 8 | 8 | 0 | 0/8/0 |
| support-proof | 10I, 6V | 8 | 8 | 2 | 2/6/0 |
| definition-body | 7I, 2R, 7V | 8 | 8 | 1 | 1/7/0 |
| required-hypothesis | 9I, 2R, 5V | 5 | 7 | 3 | 3/5/0 |
| unused-hypothesis | 9I, 2R, 5V | 5 | 8 | 3 | 3/5/0 |
| global-collision | 16R | 6 | 6 | 8 | 8/0/0 |
| hidden-projection | 10I, 6V | 8 | 8 | 2 | 2/6/0 |
| simp-input | 8I, 8V | 8 | 8 | 0 | 0/8/0 |
| withdraw-reissue | 8S, 8V | 8 | 8 | 0 | 0/8/0 |
| exhausted | 16S | 8 | 0 | 8 | 8/0/0 |
| pruning-withdrawal | 16V | 8 | 8 | 0 | 0/0/8 |
| cycle-grounding | 16S | 8 | 8 | 8 | 8/0/0 |
| alternative-worlds | 16S | 8 | 8 | 8 | 8/0/0 |
| cost-evidence | 16S | 8 | 8 | 8 | 8/0/0 |
| partial-audit | 16S | 8 | 8 | 8 | 8/0/0 |

## Disagreements and premise price

**unrelated.** An appended irrelevant theorem leaves all retained terms valid. The conservative recipe import-closure hash invalidates eight old recipe receipts; all saved recipes still elaborate.

**support-proof.** Wrapping call_frame's proof with id preserves its contract. Old receipts for call_frame and its submit_frame consumer become inputMismatch; B and C independently pass. Six retained routes survive.

**definition-body.** Triple's body is wrapped with id, leaving the target expression unchanged and its meaning definitionally equal. The contract-definition identity changes for submit_frame, so its old revision is unavailable although B/C pass. This tests body tracking and conservative invalidation, not a semantic change to Triple.

**required-hypothesis.** Scratch receive_ok_with gains audit : Bool and newPremise : audit = true; its conclusion also requires audit = true and the new proof uses the premise. Its retained proof and saved recipe both fail. Old receive_derived also fails against the changed support signature, affecting both frame-root cones; fresh frame recipes succeed with the scratch environment's repaired support. This is a real new premise price, not an unused binder masquerading as one.

**unused-hypothesis.** Scratch receive_ok_with gains _unused : True without changing its conclusion. The old closed term does not have the new type, and old receive_derived applies the old signature. Fresh recipes all elaborate. A refuses old evidence; B/C disagree without either being a truth oracle for the advertised claim.

**global-collision.** The scratch chain_binds specializes to Bool digests and replaces the bounded collision branch by an unbounded existential. Three distinct byte arrays into Bool prove that branch from the instance alone; its proof ignores chain evidence. The real audit flags exactly this root. Old chain proofs and recipes fail; two old auxiliary theorem names are explicitly unavailable (inventory stays 2520). Generated binder hygiene names additionally over-invalidate unrelated exact structural revisions: A reports 16 receipt mismatches, while six B/C roots succeed. ROOT granted B (bound-label alpha normalization); it was not implemented. The reader brief accepts this measured conservative limitation for the pilot, without treating it as a semantic dependency change.

**hidden-projection.** A fresh JournalWrapper structure/constructor/projection is introduced around call_frame's proof. The export grows from 5697 to 5700 declarations and records those auxiliary dependencies; call_frame and submit_frame old receipt inputs change. All retained proofs and recipes pass.

**simp-input.** The scratch environment removes the simp attribute from List.mem_cons. Kernel expression dependencies stay the same. The separately recorded recipe attribute input changes, so only recipe receipts become unavailable. Every fixed saved recipe still elaborates under this particular change; no claim that all simp mutations are harmless.

**withdraw-reissue.** Receipt support token (1,0) is withdrawn and (1,1) issued. Old retained evidence stays suspended; the independently checked recipe route survives for every obligation. Reissuing a name does not revive its old version. B/C still pass because policy availability is a different observation.

**exhausted.** The kernel allocation allowance and fresh elaboration heartbeat cap are reduced to 1 in this scratch run. All 2520 B terms nevertheless check; all eight C elaborations actually exhaust their budget (with downstream missing-binder diagnostics after the exhausted preamble). The scenario explicitly withdraws both archived receipt-service tokens, so A suspends all candidates even though independent B succeeds. This is a receipt-availability policy plus actual recipe exhaustion, not a kernel-exhaustion demonstration. A future producer should retain or freshly authorize the successful B route; no claim of theorem falsity follows.

**pruning-withdrawal.** The same recipe candidates are initially pruned by live blocker (6,0). Removing it reopens them; both routes then verify. No candidate is regenerated or discarded. B/C pass throughout.

**cycle-grounding.** The landed Worlds experiment actually changes groundedBefore [[0,1,2,5,6]] to groundedAfter [[5,6]]. Loss of atom 1 withdraws the grounding evidence token and suspends all candidates. The cycle alone does not count as grounded evidence. B/C can still check the literal terms.

**alternative-worlds.** The landed Worlds analysis returns separate alternatives [[1],[0]] and rejects their union. No common selected world is asserted; the adapter suspends evidence requiring that grounding choice. B/C still pass and cannot settle this world-selection obligation.

**cost-evidence.** Withdrawal of the cost receipt token suspends all candidates, while B/C pass. This is lost evidence, distinct from a proved bound violation; cost_tooth separately computes uncovered at cost 2 with budget 1.

**partial-audit.** Withdrawal of audit coverage suspends all candidates, while B/C pass. Neither incomplete coverage nor a missing-import export shrinks the eight-obligation seed.

A fresh literal receipt for the new global-collision theorem is separately checked by the finite adapter: literal-audited-out.json is pruned, and literal-audit-withdrawn-out.json is verified. It is a NEW revision candidate, deliberately not mixed into the fixed old-candidate equality. This shows why literal kernel success does not establish the advertised binding obligation.

## Index and checker measures

The fixed candidate index costs 53994 support-posting insertions once, zero per edit (candidate set unchanged). Its reference list scans all 53994 supports each query. The table reports queries/scans, checker calls and peak child RSS separately; elapsed time never determines a verdict. A full oracle judgment evaluates 16 finite receipts per edit. Additional baseline/initial/control evaluations are retained in the raw process receipts and are not hidden in the optimized-call column. Export/validation costs and external B/C calls are paid separately; no end-to-end asymptotic claim follows from an index-query saving.

| Edit | Index lookups / postings | Indexed A / full A | B kernel invocations / retained inventory | C elaborations | Peak child RSS MiB |
|---|---:|---:|---:|---:|---:|
| unrelated | 1 / 8 | 8 / 16 | 2520 / 2520 | 8 | 4171.9 |
| support-proof | 2 / 12 | 10 / 16 | 2520 / 2520 | 8 | 4191.2 |
| definition-body | 3 / 12 | 9 / 16 | 2520 / 2520 | 8 | 4223.7 |
| required-hypothesis | 6 / 20 | 11 / 16 | 2520 / 2520 | 8 | 4193.4 |
| unused-hypothesis | 6 / 20 | 11 / 16 | 2520 / 2520 | 8 | 4073.2 |
| global-collision | 487 / 4956 | 16 / 16 | 2518 / 2520 | 8 | 4202.4 |
| hidden-projection | 5 / 12 | 10 / 16 | 2520 / 2520 | 8 | 4201.6 |
| simp-input | 1 / 8 | 8 / 16 | 2520 / 2520 | 8 | 4202.5 |
| withdraw-reissue | 16 / 16 | 16 / 16 | 2520 / 2520 | 8 | 4201.9 |
| exhausted | 16 / 16 | 16 / 16 | 2520 / 2520 | 8 | 4201.2 |
| pruning-withdrawal | 16 / 16 | 16 / 16 | 2520 / 2520 | 8 | 4201.7 |
| cycle-grounding | 16 / 16 | 16 / 16 | 2520 / 2520 | 8 | 4201.8 |
| alternative-worlds | 16 / 16 | 16 / 16 | 2520 / 2520 | 8 | 4201.9 |
| cost-evidence | 16 / 16 | 16 / 16 | 2520 / 2520 | 8 | 4229.9 |
| partial-audit | 16 / 16 | 16 / 16 | 2520 / 2520 | 8 | 4188.8 |

Every affected set equals the list oracle, and every incremental status/detail map and residual candidate list equals full recomputation. Candidate identity includes id, complete receipt data, supports, blockers and cost. Exact digests beside those equalities:

| Edit / repair equality | Candidate count | Same archived candidates | SHA-256 candidate identity |
|---|---:|---|---|
| unrelated: indexed = full | 16 | yes | 05fe22507ed9df24f01458a4ebc10fb353ac9cd534789fd237aac0599f8e8326 |
| support-proof: indexed = full | 16 | yes | 05fe22507ed9df24f01458a4ebc10fb353ac9cd534789fd237aac0599f8e8326 |
| definition-body: indexed = full | 16 | yes | 05fe22507ed9df24f01458a4ebc10fb353ac9cd534789fd237aac0599f8e8326 |
| required-hypothesis: indexed = full | 16 | yes | 05fe22507ed9df24f01458a4ebc10fb353ac9cd534789fd237aac0599f8e8326 |
| unused-hypothesis: indexed = full | 16 | yes | 05fe22507ed9df24f01458a4ebc10fb353ac9cd534789fd237aac0599f8e8326 |
| global-collision: indexed = full | 16 | yes | 05fe22507ed9df24f01458a4ebc10fb353ac9cd534789fd237aac0599f8e8326 |
| hidden-projection: indexed = full | 16 | yes | 05fe22507ed9df24f01458a4ebc10fb353ac9cd534789fd237aac0599f8e8326 |
| simp-input: indexed = full | 16 | yes | 05fe22507ed9df24f01458a4ebc10fb353ac9cd534789fd237aac0599f8e8326 |
| withdraw-reissue: indexed = full | 16 | yes | 05fe22507ed9df24f01458a4ebc10fb353ac9cd534789fd237aac0599f8e8326 |
| exhausted: indexed = full | 16 | yes | 05fe22507ed9df24f01458a4ebc10fb353ac9cd534789fd237aac0599f8e8326 |
| pruning-withdrawal: indexed = full | 16 | yes | 3750b741dd11bbcbaf19fdf7c22c9221043be87a75abd13a4a27f5cf4dbc2166 |
| cycle-grounding: indexed = full | 16 | yes | 05fe22507ed9df24f01458a4ebc10fb353ac9cd534789fd237aac0599f8e8326 |
| alternative-worlds: indexed = full | 16 | yes | 05fe22507ed9df24f01458a4ebc10fb353ac9cd534789fd237aac0599f8e8326 |
| cost-evidence: indexed = full | 16 | yes | 05fe22507ed9df24f01458a4ebc10fb353ac9cd534789fd237aac0599f8e8326 |
| partial-audit: indexed = full | 16 | yes | 05fe22507ed9df24f01458a4ebc10fb353ac9cd534789fd237aac0599f8e8326 |
| sequential = full = batch (withdraw then reopen) | 16 | yes | 3750b741dd11bbcbaf19fdf7c22c9221043be87a75abd13a4a27f5cf4dbc2166 |

The sequential experiment has 88 initial token postings. Each of two edits performs one lookup, scans eight postings and rejudges eight candidates; the oracle scans 88 supports and evaluates sixteen. Withdrawal suspends eight retained routes; removing the pruning token reopens eight recipe routes. Sequential, full and batch residuals agree. Initial blocked candidates are retained, not recreated.

## Coverage, receipts and interpretation

Baseline export: 5697 declarations, 809578 shared expression nodes and 2520 theorem artifacts. All baseline artifacts kernel-check; all eight saved recipes elaborate before either receipt route is authorized. Whole process outputs, exact commands, source mutations, exit codes, output hashes and per-process resource measures are retained in each case folder. The run's original implicit-success finite request schema was migrated into new explicit checked-result records only for already successful archived evidence; all 46 finite observations were rerun and matched. No external B/C execution was rerun merely to search its output.

Four core check-disabling teeth cover revision, successful result, completeness and exact inputs. Eight actual-export plants cover incomplete marker, root inventory, missing declaration, omitted value edge, saved inventory, cyclic DAG, mismatched artifact and omitted recursor-rule dependency. A missing import causes real Lean failure, no export, INCOMPLETE COVERAGE, and eight still-owed obligations. Further real teeth cover discarding an exhausted result, disabling the global-collision detector and tampering with the journal history. Each disabled check accepts its malformed input or loses its expected finding; the enabled check's real diagnostic is preserved. Locations: CX-PE1-plants2, CX-PE1-coverage1, CX-PE1-coverage2, CX-PE1-final1/{result,audit,history}. None changes an installed production check.

The proof boundary is finite receipts and declared read sets. Export authenticity/completeness, SHA-256's engineering identity, token issuance and semantic audit coverage are producer responsibilities. The detector covers the tested outer existential escape, not arbitrary statement vacuity. Source closure hashing is conservative; exact Expr hashes also retain binder hygiene labels. ROOT granted canonical alpha hashing (B), but the builder did not apply it. The reader brief permits retaining the measured conservative identity for this pilot. B's canonicalization law, roundtrip and both-direction plants remain follow-on obligations; there is no normalized comparison run. Therefore the all-root global-collision over-invalidation is a known measured limitation, not a soundness claim or a performance win.

Receipt-first remains ROOT's sequencing ruling. The dependent-context bridge, mini constructor redesign and bread premise-flow acceptance cases remain the next card; this pilot does not claim to complete them.


## Second-reader additions (2026-10-21)

CX-READER-PE1 independently read all mutation environment, export, retained-check
failure and recipe outputs; verified 227 distinct recorded output hashes; and
recomputed every affected-set/count/status/detail/residual comparison from the
saved finite requests. All 15 candidate identities and index/list equalities agree.

The missing-import disabling tooth is now executed separately at
/tank/dregg-build/nanodregg/logs/CX-READER-PE1-coverage1/missing-import.
Its real Lean missing-module diagnostic is lean.log:1. With the missing-file
refusal enabled, adapter.log:1 reports INCOMPLETE and the journal retains all eight
owed obligations. A scratch-only bypass of that refusal accepts the absent export;
the coverage tooth then reports RED at disabled.log:1: complete=True with zero
obligations. No production validator is weakened.

The scoped coverage receipt writer now emits an actual newline, so receipts.json
parses as JSON. The historical coverage2 file with its literal backslash-n remains
untouched. Six new Lean modules were independently rechecked once at 6G/two threads
and maxHeartbeats=800000 (CX-READER-PE1-check1.log). No Lean statement or Kernel
source changed during this review.


P7 integration: the reader worktree is rebased onto d7989d94af13b9ff2ca4301f0c3780611033d925.
No P7-changed module occurs in the baseline exported declaration slice, and every
recorded recipe input hash remains equal. The raw matrix therefore remains evidence
for its stated fe89edf source, with no affected exporter/recipe source hidden by the
integration. Closure's HoleDecl moved into its own def module; the receipt interfaces
and Protocol repair theorem are unchanged.


## Current scoped validation

Census-only import closure: JournalRun → Journal → JournalExpr and Statements → Lean.
All three excluded Lang source files are absent from the working tree and preserved
in scratch. The scoped build completes in five jobs, without a contextual import
(CX-READER-PE1-scoped-check1.log).

The direct Census command reproduced all 46 historical finite named-status
observations. Exact new Census status/detail maps, affected sets, residuals and
candidate identities agree between indexed and full evaluation for all saved
requests. Historical toy-world rows are replayed only as finite supplied policy
data; no toy-world command exists or runs. The active source-edit matrix omits them.

Four actual receipt mutations turn red with revision/result/completeness/input
checks disabled; the result-decoder, actual global-collision audit, history and
missing-import plants also pass. Whole child outputs and actual verdict JSON were
read. Paths: logs/CX-READER-PE1-scoped-plants1, -scoped-final1 and -scoped-coverage1.
Only deliberately disabled-check builds emit unused-variable warnings.

Fresh sequential/full/batch Census comparisons agree on candidate hash
3750b741dd11bbcbaf19fdf7c22c9221043be87a75abd13a4a27f5cf4dbc2166, with 88 initial
postings and each edit costing one lookup/eight postings/eight checks versus
88 oracle scans/sixteen checks (CX-READER-PE1-scoped-compose1). These are
executable receipt observations, not the excluded Protocol repair theorem.
