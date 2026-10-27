# nanodregg — the charter (2026-10-16)

Ember: "rebuild whatever shape you think will be better. Go hardcore. ONLY GOOD CODE AND BEST
PRACTICES. All decisions get critically and metacritically examined."

nanodregg is the same end-computing system as minidregg (main 2c27b08b) rebuilt from its spec,
not ported from its code. The spec is: the journey ROWS, the deterministic SIMULATION, THE BAR
(two friends + hosted Hermes over ssh; 1000 records, write ≤ 5 s, cold reopen ≤ 60 s), and the
THEOREM STATEMENTS that mean something (not the vacuous ones; see the discovery dossiers). The
historical target shape came from minidregg's HP design and the reorientation dossiers.
The current system guide is [docs/OVERVIEW.md](docs/OVERVIEW.md); the theorem boundary is
[Spec/README.md](Spec/README.md). The decision ledger retains design reasons and recovered obligations.

## Scope (Ember, 2026-10-21)

Ember: "we agree that nano has nothing to do with proof systems, host-hiding, or multi-node
agreement." nanodregg is an object of study more than the seed of a prototype: a side exploration,
for diversity and focus, while breadstuffs (the whole system built before it) waits to be resumed
or composted into the next robigalia. It is a single-node vat with one writer per Store, members
who consent by re-execution, and an operator who sees every byte. It demonstrates where minidregg
could be better where that is cheap. Two demonstrations are approved: documents and escrow. No
other minidregg aspect is pulled in to demonstrate.

Three things are ruled, not omitted: the first two are outside nanodregg, the third bounds it.

1. **Proof systems.** Nothing. Admission is re-execution; the proof slot stays empty; no circuit,
   STARK, folding scheme or accumulator is built here or enters the TCB. breadstuffs holds that
   lineage.
2. **Hiding from the Host.** Nothing. The operator is a trusted vat: the Host and every key holding
   a follow grant see every byte; membership is the confidentiality boundary; a member is kept out
   of a World by holding no follow grant (decisions/protocol.md PROTOCOL-3, ruling (a)).
3. **Writers.** One writer per World; followers re-derive every Turn (law 1, PROTOCOL-4). Many parties and
   many processes over one writer are in scope: residents, member sockets, followers, and the protocols
   between objects, with the member socket modelled. Many Worlds are in scope: a protocol between Worlds
   runs on receipts checked against held heads; it has no atomic cross-World commitment. Replication of a
   World's writer by agreement is a planned, priced phase that keeps one decided log per World; liveness is
   measured, never proved. Merging divergent histories of one World is refused: a fork is a new World.
   (Ember, real 2026-10-22, approving `redregg/work/PROGRAM-20261022.md` §2(d); decisions/lang.md LANG-75.)

A lane briefed to "add a proof", "hide it from the Host", "merge two histories of a World", "replicate
the writer" outside its planned phase, or "bring in another minidregg feature as a demo" is briefed
against this section: the brief is wrong, not the charter. The meta-critique below applies here too: a
scope chosen to avoid a hard part is the smell. This one is chosen because each excluded part is a
measured failure of the trees before it: breadstuffs' soundness apex vacuous at BabyBear, minidregg's
empty proof slot, an agreement mesh with one host.

## Laws (every commit obeys; a reviewer may revert on sight)

1. **One of everything.** One World, one Turn, one admission path (`World.admit` IS the receive
   path), one Store format, one codec family, one digest type (32 fixed bytes), one dispatch over
   one operation table, one sandbox shape, one build. A second shape of an existing thing is a
   defect, not a transition. Old SHAPES refuse to load; STATE may be carried only by re-genesis
   from a checked export (export = the fold, the World a Store opens to; import = genesis under a
   new epoch whose initial World is that World's cells re-sealed; check = canonical World bytes equal
   up to the epoch header; every signature over old bytes is NOT carried, so history is never
   carried, only state); re-genesis is free (OPS-1, accepted 10-17).
2. **Lean decides, Rust moves bytes.** Every accept/refuse/select/order/digest decision is a Lean
   definition with a named theorem. Rust (if any) is transport, custody, sockets, sandbox plumbing,
   and consumes Lean-generated tables (opcodes, bounds), never hand-copied constants. A PLATFORM
   FACT (an OS sandbox floor: which paths a process must see to start at all) is a table in the layer
   that touches the platform, not a decision; it carries a plant proving it does not over-allow (a
   file nobody named must be unreadable) and a recorded bisection for its minimality (CLIENT-9,
   accepted 10-16; CLIENT-2's correction: the plant proves no-over-allow, the bisection minimality).
3. **Bytes end to end.** `ByteArray` everywhere; no `List UInt8` in a deployed path; one-pass
   canonical decoders with a canonicity proof; content-addressed tags.
4. **TigerStyle.** A static bound on everything (`Bounds`); an assertion for every PREMISE the
   types do not carry (decoded bytes, disk reads, FFI results, anything that crosses a boundary),
   placed where the premise enters, each paired with the theorem that relies on it (KERNEL's K1
   restatement, accepted 10-16: inside a total Lean definition an "invariant assertion" only
   re-checks the compiler); no `partial def` in deployed code; no unbounded recursion; no
   allocation per byte; O(touched) work per request, never O(store). The resident's top-level
   fuel-and-restart loop is TOTAL: bounded by a LIFETIME constant (fuelBatches × restartsMax, larger
   than the reader's 2^48-frame lifetime) that no physical run can exhaust, with the theorem that
   exhausting it exits by name, never silently; no `partial` anywhere (HOST-19, blessed 10-17;
   supersedes the 10-16 "one unbounded loop" wording). A resource whose LIFETIME is the guarantee (a lock, a lease, a
   PID-file descriptor) lives in the value the running code holds, never in a separate local kept by
   a dummy later use, and a plant against the LIVE process refutes its early release: compiled Lean
   frees a value at its last use, which dropped the writer lock mid-serve while the lock was a local
   (HOST 7e23642; the plant was a second writer). The writer lock is the key file's read handle, a
   field of the `Writer` every effect of the loop holds (HOST-64, HOST-76); store-plants
   `seal-live-writer-locked` and `follow-live-locked` are its teeth (a second process against a live
   `host serve` / `host follow` is refused `locked`; RED with the lock removed).
5. **Performance is designed.** The resident Host is one deterministic loop per Store holding the
   World, the trie and the memo; admission is batched; the follower is the only replayer. "Checkpoint
   = World" means the World is what a checkpoint DENOTES. O(store) work is forbidden on the REQUEST
   path; off-loop sealing of a whole-World base that amortises to O(appended bytes) is allowed, with
   its cadence a named Bound, a `worldBytesMax` bound that refuses by name where the design must
   change, and a WASTE line that keeps the amortisation visible (HOST-14, measured 10-16: the encode
   is 25–35× cheaper than one fsync at THE BAR; it replaced K1's incremental deltas). HOST and CODEC
   own that representation. Measure
   at range ends with `perf stat --no-scale`; the waste ratio of every operation is pinned and may
   only fall.
6. **Named theorems, never `#guard`.** `theorem … := by decide/rfl`. One tree-wide axiom census
   (`Census/Axioms.lean`, run by `gates/census.py` in the convergence report) lists every declaration's
   axioms instead of per-theorem `#assert_axioms` lines; where the compiler must be trusted,
   `native_decide` with a row in `gates/axioms-allow.tsv`, which is its record. No `sorry` lands. A
   theorem's statement says something: the top-level claims (Spec/) are refused by a trivial system,
   and that is where vacuity is checked.
7. **Refusals by name.** Every refusal is a constructor with a name on the wire; a parse failure is
   never rendered as a verdict; "uncertain" is a real outcome.
8. **Small modules, split proofs.** A module exports definitions OR proofs about them, not both,
   so a proof edit rebuilds nothing downstream; the split is BY FILE (a `Proofs` path component),
   because Lean v4.30.0's `module` system still rebuilds importers on a proof-only edit (GATES-2,
   measured 10-16). No import hubs. Target: the Host closure under 150 modules; a one-module edit
   rebuilds its dependents in under 2 minutes on a laptop.
9. **Every landing builds what it changed and runs what it touched.** `scripts/commit` rebases on
   origin/main, builds the changed modules and their importers (and `cargo check` of the reached Rust
   packages), runs the rows those reach, and pushes. Main is the only branch. Small commits, often. A red
   the convergence report names is fixed forward by the lane whose landing it names; `git revert` is
   always allowed.
10. **Decisions are examined, then re-examined.** Every design decision goes in `decisions/<layer>.md` (one file per layer; `DECISIONS.md` is frozen after 10-16: seven writers on one append-only file collided twice):
    the decision, the alternatives, why this one, the CRITIQUE (what would make it wrong), and the
    META-CRITIQUE (what bias produced it: familiarity with minidregg's shape, an estimate mistaken
    for a constraint, a phase ordering chosen to avoid a hard part). A decision without both
    critiques is not made.
11. **No twins of minidregg.** Reading minidregg is allowed to learn the spec and the mistakes;
    copying a file is not. If a minidregg definition is right, restate it from its theorem, smaller.
    Carve-out (PROTOCOL, 10-16): the conformance ROWS restate the minidregg journeys step for step,
    because the journeys ARE the spec; that is restating the spec, not copying code.
12. **Small is a design goal.** Fewer modules, opcodes, constructors and lines is better, argued in
    the decision that adds them; no file over 1 MB lands (`gates/size_limit.py`, in the report).

## Layers and owners (the six rebuild agents)

Dependency order is top to bottom; a lower layer builds against the REAL signatures the layer
above has committed, never against prose.

| layer | owner | owns | first deliverable |
|---|---|---|---|
| KERNEL | DISCOVER-KERNEL → BUILD-KERNEL | `Kernel/`: World, Turn, Leg, History, `World.admit`, `fold`, Bounds, the Store model (log of Turns, checkpoint = World, roots), the simulation generator, AND `Kernel/Receive/`: the RECEIVERS (signed request → Turn: authority, law, funding; one derivation per operation kind, each a def with its theorem; derive-then-admit, the World's guard check is the one staleness refusal) — ROOT ruling 10-16 on HOST-1; HOST drives and decides nothing |
| LANG | BUILD-LANG | `Lang/`: Objective Bend — the Core4 term language, typing/checking, the demand machine, compilation of a checked term to an installed law / invocable package, and the hosted-resident surface (what a Hermes resident can author and install); minidregg's `Theory/ObjectiveBend*` (46 files) and `Compiler/ObjectiveBend*` (28) are the SPEC to restate smaller, never copy; consumes KERNEL's `install`/`invoke` receiver signatures | `Lang/Term.lean` + `Lang/Check.lean` with the preservation/determinism theorems, and one law compiled end to end through a KERNEL receiver | `Kernel/World.lean` + `Kernel/Turn.lean` + `Kernel/Bounds.lean` with the admit/fold theorems (determinism, follower soundness, charge exactness, guard-from-intent staleness refusal) and `Kernel/Sim.lean` (seeded generator + Host/follower side-by-side check) |
| CODEC | DISCOVER-CODEC → BUILD-CODEC | `Codec/`: the one `StreamCodec` family over ByteArray, `Digest256`, content-addressed tags, canonicity proofs, the generated operation table and bounds for Rust | `Codec/Stream.lean` with canonicity theorem, `Codec/Tag.lean`, and the generator for `protocol/*.json` |
| HOST | DISCOVER-HOST → BUILD-HOST | `Host/`: the resident loop (one per Store), batched admission, the single dispatcher over the op table, the durable Store (SQLite or a flat log: decide and critique), checkpoints, crash protocol, the consent provider as the SAME code path in a second process | `Host/Loop.lean` admitting Turns through `World.admit`, persisting through one append, with the crash-restart plant |
| PROTOCOL | DISCOVER-PROTOCOL → BUILD-PROTOCOL | `protocol/`: the operation table (target ≤ 40 ops), consent frames (merged), client commands, the SPK broker verbs; every op's receiver named; the conformance rows (the journeys rewritten as executable rows against nanodregg) | `protocol/operations.lean` (the table as data with a theorem that every op has exactly one receiver) + `rows/` (journey J0–J8, JPAY, jwell, m6grain, hermes as nanodregg rows) |
| CLIENT | DISCOVER-RUST → BUILD-CLIENT | `client/` (Rust, one crate, one process over two sockets: custody + transport + workspace; decides nothing) and `sandbox/` (bwrap launcher, SPK broker, grain runtime as thin plumbing over Lean-decided policy) | `client/` that performs challenge → prepare → assemble → submit → lookup against BUILD-HOST's loop, with the generated op table as its only protocol knowledge |
| CLOSURE | DISCOVER-CLOSURE → BUILD-GATES | `gates/` + the build: the lakefile, `scripts/commit` (a landing: build what changed, run what it touched, push) and the convergence report (`scripts/converge`, `scripts/standing.sh`: the whole build, every row, the census, the source checks) | `lakefile`, `gates/closure` (a def-module importing a proof-module, in the report), `scripts/standing.sh` |
| HOSTING | BUILD-HOSTING | `Hosting/` (lifecycle generator + theorems, Plan, controller + broker decisions with the lease, resident profile), the `launcher/` Rust crate, `world/grain/` + `world/hosting/` package texts, `decisions/hosting.md`; must never hold a member seed in a process that parses model/provider bytes, keep grain phase/pid/volumes as truth outside the World, or add a Body constructor/receiver without KERNEL (current contracts: `docs/OPERATING.md` and `decisions/hosting.md`) | the grain lifecycle green through `Receive.submit`; the broker's first refusal by name with no key reaching the resident |
| LEDGER | BUILD-LEDGER (a KERNEL deliverable, prefix `kernel:`) | `Kernel/Value.lean`, `Kernel/Proofs/Value.lean`, `Kernel/Receive/Ledger.lean`, `Kernel/Proofs/Ledger.lean`, the ledger arms of `Kernel/Sim/Gen.lean`; edits Cell/World/Call/Derive only by agreement with KERNEL (full row: `ASSEMBLY-ledger.md`) | value conservation as an equality with its plant; floors + wells (pug's rule); escrow never both released and refunded |
| OPS | BUILD-OPS | `Ops/` (unit renderer emitted with `--check`, Node values, the BAR driver), `ops/` (units, RUNBOOK, live/), `decisions/ops.md`; must never decide what HOST/KERNEL/CLIENT decide, touch a service manager outside its scratch, hold key material, or delete a Store (full row: `ASSEMBLY-ops.md`) | units emitted + live harness green against the real `host`; world-carry round trip with its check |
| PERF | BUILD-PERF (a lane, not a decision layer) | `Bench/` (C9 tooling), `scripts/bar.sh`, `gates/bar.tsv`, `decisions/perf.md`; must never decide anything, copy a deployed definition, quote a toy/warm/extrapolated number as THE BAR, or add a wall-clock row to waste.tsv (full row: `ASSEMBLY-perf.md`) | THE BAR over sockets on a quiet machine, with load recorded |
| TRANSPORT | BUILD-TRANSPORT (temporary; dissolves when D1–D7 land) | nothing permanently: drives store identity, the mux close, thin-consent plumbing into the owners' paths under their prefixes (full row: `ASSEMBLY-transport-consent.md`) | D1+D2: a request and an envelope bound to their Store (flag day), with the foreign-segment plant |
| SPEC | SPEC (a ROOT lane) | `Spec/` (the top-level claims over the deployed entry points: `System`, the trivial systems, each claim with its top theorem, floor and deployed run), `decisions/spec.md`; must never restate a deployed definition (a field of `deployed` names it) or land a claim without a floor | every TOPLEVEL-SPEC claim proved of `deployed` and refused by a trivial system |

The 10-17 rows (HOSTING, LEDGER, OPS, PERF, TRANSPORT) came from the scoutotype swarm (27 Sonnet scouts → 6 Opus assemblies, recorded in historical assembly dossiers; surviving obligations are in `decisions/root.md`); the primary checkout `~/dev/nanodregg` is a read-only reference that follows origin/main (`scripts/mac-pull`).

Until KERNEL commits its first signatures, the other five write their layer's `DESIGN.md`
(decisions with critiques) and their interface PROPOSAL as Lean/Rust signatures in a
`proposals/<layer>.md`, and build whatever does not depend on the kernel (CODEC's StreamCodec,
CLOSURE's lakefile and gates, CLIENT's socket/custody skeleton, PROTOCOL's rows as specs). KERNEL
reads the proposals before committing signatures and answers each in `DECISIONS.md`.

## Working rules

- Repo: github.com/emberian/nanodregg, branch `main`, no other branches; origin/main on GitHub is the
  truth. Clones: the Mac (`~/dev/nanodregg`) and hbox (`/tank/dregg-build/nanodregg/main`, the build box,
  shared with other work: be considerate).
- One agent per worktree (`scripts/worktree <layer>`). Commit with git in your worktree, or name your
  paths to `scripts/commit -m MSG PATH...`. Never `git add -A` in a tree others touch, never
  `git stash`, never rewrite pushed history.
- **A landing** (`scripts/commit`): rebase on origin/main; build what you changed (the modules your diff
  touches and their importers; `cargo check` of the reached packages); run the rows and journeys your
  change touches; push to main. If main moved, it rebases and pushes again; if the rebase conflicts,
  you resolve it. Its build and test trees live on the home disk (`~/nd-land/<worktree>/`; on hbox the
  NVMe, never /tank), at idle priority under swarm-build. That is the whole gate.
- The commit message is prose: what changed and what it lets the system do. No form lines.
- Tests are theorems, journeys and rows. The whole is a periodic REPORT: `scripts/converge` builds
  the tree, runs every row, test and bench, the census and the tables, and says what is red and
  which landing it came from. It never refuses and never reverts; a red is a task for that lane,
  fixed forward. No unfiltered test suites.
- Decisions: `decisions/<layer>.md`, append-only, one critiqued entry per real design choice (law 10).
- Box safety: PID file or nothing for kills (never by pattern); every loop sleeps and has a deadline;
  every build runs through `scripts/nd-build` (one of six box-wide build slots, `ionice -c3 nice -n 15`,
  swarm-build at a lane budget: 6G a module, 24G a tree);
  disk pressure is Ember's (stop and report, delete nothing outside your own scratch).
- When a process constraint appears, the first question is "do we need this at all?". When a lane
  spends more time landing than building, the gate is the defect.

## The meta-critique that applies to this whole charter

It was written in one pass by ROOT, from the minidregg map, under the bias that minidregg's layer
names are the right names. The first job of each owner is to attack the row of this table they
own: if the layer should not exist, or should be two, or should be inside another, say so in
`DECISIONS.md` with the critique, and ROOT re-cuts the table. The second job is to attack the laws:
each is a response to a measured minidregg failure (cite the dossier), and a law that answers a
failure nanodregg cannot have is dead weight.
