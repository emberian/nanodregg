# nanodregg — the charter (2026-10-16)

Ember: "rebuild whatever shape you think will be better. Go hardcore. ONLY GOOD CODE AND BEST
PRACTICES. All decisions get critically and metacritically examined."

nanodregg is the same end-computing system as minidregg (main 2c27b08b) rebuilt from its spec,
not ported from its code. The spec is: the journey ROWS, the deterministic SIMULATION, THE BAR
(two friends + hosted Hermes over ssh; 1000 records, write ≤ 5 s, cold reopen ≤ 60 s), and the
THEOREM STATEMENTS that mean something (not the vacuous ones; see the discovery dossiers). The
target shape is minidregg's `docs/HP-DESIGN.md` taken literally, and the reorientation documents
in `~/dev/redregg/work/`: `ARCHITECTURE-20261016.md`, `CYCLE-TIME-20261016.md`,
`RECOVERY-20261016.md`, and each `DELETE-<layer>-20261016.md` as it lands.

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
   PID-file descriptor) must be the handle actually in use, never a held-but-unused value: compiled
   Lean frees a value at its last use, which dropped the writer lock mid-serve until the lock became
   the append fd itself (HOST 7e23642; the plant was a second writer).
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
6. **Named theorems, never `#guard`.** `theorem … := by decide/rfl`; the ONE tree-wide axiom census
   (`Census/Axioms.lean`, gate `gates/census.py`) replaces per-theorem `#assert_axioms` lines, because
   it checks every declaration rather than the ones someone remembered (GATES-4, accepted 10-16);
   only where the compiler must be trusted, `native_decide` with an allow row in
   `gates/axioms-allow.tsv`, which is its record. No `sorry` ever lands. Every
   theorem statement is read by a second agent before it lands (vacuity check: identity carriers,
   `P → P`, empty premises).
7. **Refusals by name.** Every refusal is a constructor with a name on the wire; a parse failure is
   never rendered as a verdict; "uncertain" is a real outcome.
8. **Small modules, split proofs.** A module exports definitions OR proofs about them, not both,
   so a proof edit rebuilds nothing downstream; the split is BY FILE (a `Proofs` path component),
   because Lean v4.30.0's `module` system still rebuilds importers on a proof-only edit (GATES-2,
   measured 10-16). "No import hubs" is measured as the SIZE metric `max dependents of one module`
   with a ceiling (GATES-6). Target: the Host closure under 150 modules; a one-module edit rebuilds
   its dependents in under 2 minutes on a laptop.
9. **Every commit builds.** `lake build` of the commit's import closure (and `cargo check` where
   Rust exists) passes BEFORE push. Main is the only branch. Small commits, often. A red on main is
   fixed forward within the hour by whoever sees it; `git revert` is always allowed.
10. **Decisions are examined, then re-examined.** Every design decision goes in `decisions/<layer>.md` (one file per layer; `DECISIONS.md` is frozen after 10-16: seven writers on one append-only file collided twice):
    the decision, the alternatives, why this one, the CRITIQUE (what would make it wrong), and the
    META-CRITIQUE (what bias produced it: familiarity with minidregg's shape, an estimate mistaken
    for a constraint, a phase ordering chosen to avoid a hard part). A decision without both
    critiques is not made.
11. **No twins of minidregg.** Reading minidregg is allowed to learn the spec and the mistakes;
    copying a file is not. If a minidregg definition is right, restate it from its theorem, smaller.
    Carve-out (PROTOCOL, 10-16): the conformance ROWS restate the minidregg journeys step for step,
    because the journeys ARE the spec; that is restating the spec, not copying code.
12. **Size is a ratchet.** `SIZE.md` holds the counts (modules, lines per layer, opcodes,
    constructors, Rust lines, partial defs, theorems); a commit that raises a count explains why in
    the message or is reverted.

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
| CLOSURE | DISCOVER-CLOSURE → BUILD-GATES | `gates/` + the build: lakefile with small modules and the def/proof split enforced, the size ratchet, the waste ratchet, the import-closure gate, `#assert_axioms` census, the standing service script (tip → build → sim → rows), the CI that runs on a laptop | `lakefile`, `gates/size`, `gates/closure` (refuses a def-module importing a proof-module), `SIZE.md` seeded, `scripts/standing.sh` |
| HOSTING | BUILD-HOSTING | `Hosting/` (lifecycle generator + theorems, Plan, controller + broker decisions with the lease, resident profile), the `hosting/` Rust crate, `world/grain/` + `world/hosting/` package texts, `decisions/hosting.md`; must never hold a member seed in a process that parses model/provider bytes, keep grain phase/pid/volumes as truth outside the World, or add a Body constructor/receiver without KERNEL (full row: `redregg/work/nanodregg-scout/ASSEMBLY-hosting.md` §4) | the grain lifecycle green through `Receive.submit`; the broker's first refusal by name with no key reaching the resident |
| LEDGER | BUILD-LEDGER (a KERNEL deliverable, prefix `kernel:`) | `Kernel/Value.lean`, `Kernel/Proofs/Value.lean`, `Kernel/Receive/Ledger.lean`, `Kernel/Proofs/Ledger.lean`, the ledger arms of `Kernel/Sim/Gen.lean`; edits Cell/World/Call/Derive only by agreement with KERNEL (full row: `ASSEMBLY-ledger.md`) | value conservation as an equality with its plant; floors + wells (pug's rule); escrow never both released and refunded |
| OPS | BUILD-OPS | `Ops/` (unit renderer emitted with `--check`, Node values, the BAR driver), `ops/` (units, RUNBOOK, live/), `decisions/ops.md`; must never decide what HOST/KERNEL/CLIENT decide, touch a service manager outside its scratch, hold key material, or delete a Store (full row: `ASSEMBLY-ops.md`) | units emitted + live harness green against the real `host`; world-carry round trip with its check |
| PERF | BUILD-PERF (a lane, not a decision layer) | `Bench/` (C9 tooling), `scripts/bar.sh`, `gates/bar.tsv`, `decisions/perf.md`; must never decide anything, copy a deployed definition, quote a toy/warm/extrapolated number as THE BAR, or add a wall-clock row to waste.tsv (full row: `ASSEMBLY-perf.md`) | THE BAR over sockets on a quiet machine, with load recorded |
| TRANSPORT | BUILD-TRANSPORT (temporary; dissolves when D1–D7 land) | nothing permanently: drives store identity, the mux close, thin-consent plumbing into the owners' paths under their prefixes (full row: `ASSEMBLY-transport-consent.md`) | D1+D2: a request and an envelope bound to their Store (flag day), with the foreign-segment plant |

The 10-17 rows (HOSTING, LEDGER, OPS, PERF, TRANSPORT) came from the scoutotype swarm (27 Sonnet scouts → 6 Opus assemblies in `redregg/work/nanodregg-scout/`); the primary checkout `~/dev/nanodregg` is the READ-ONLY reference at main, moved by `scripts/commit` after each landing.

Until KERNEL commits its first signatures, the other five write their layer's `DESIGN.md`
(decisions with critiques) and their interface PROPOSAL as Lean/Rust signatures in a
`proposals/<layer>.md`, and build whatever does not depend on the kernel (CODEC's StreamCodec,
CLOSURE's lakefile and gates, CLIENT's socket/custody skeleton, PROTOCOL's rows as specs). KERNEL
reads the proposals before committing signatures and answers each in `DECISIONS.md`.

## Working rules

- Repo: `~/dev/nanodregg` (git, branch `main`, no other branches); remote `origin` = github.com/emberian/nanodregg (public, created by Ember's order 10-17). Until scripts/commit pushes after landing (a GATES successor item), ROOT pushes main to origin at each report. Commit messages: what, why, what
  it refuses, with `Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>` (unsigned is fine).
- Build on the Mac: `lake build` / `cargo check` of your import closure before every push. Keep
  `.lake` small; the Mac data volume is nearly full: no large artifacts, no fixtures over 1 MB, no
  copies of minidregg. hbox is Ember's: do not use it. No box builds until ROOT says.
- Seven agents, ONE REPO, SEPARATE WORKTREES (ruled 10-16 after six collisions in one shared
  checkout): every layer edits in its own `git worktree` (`scripts/worktree <layer>` →
  `~/dev/nanodregg-wt/<layer>`, same `.git`, same `refs/heads/main`); the primary checkout
  `~/dev/nanodregg` is nobody's editing surface. Commit ONLY with `scripts/commit -m MSG PATH...`
  from your worktree: it builds the candidate from CURRENT main plus exactly your paths, runs the
  gates, and lands on main by compare-and-swap (retrying when main moved). A plain `git commit` is
  refused by the hook. Commit small, commit only your layer's files, never `git add -A`, never
  `git stash`, never rewrite history. THE SHARED INDEX IS NOT YOURS: never stage into the default index (another agent's
  stale index reverted a charter commit on 10-16, 65e3c1c → fixed forward feeaed3). Either commit
  with explicit paths (`git commit --only`) or use a private index (`GIT_INDEX_FILE=$(mktemp)`,
  `git read-tree HEAD`, add your paths, `write-tree`, `commit-tree`, `update-ref`). Before every
  push, `git show --stat HEAD` must list ONLY your files; a commit that touches another layer's file
  or reverts someone's hunk is a defect: fix forward, tell the owner.
- The primary checkout `~/dev/nanodregg` is the READ-ONLY reference (scouts, evaluators, `lake env lean` against its .lake); `scripts/commit` refuses to commit from it and moves it to each new main when clean. Lane-private file names in the shared scratchpad (a message file overwritten by another lane was judged under the wrong subject).
- Lakefile rule (GATES): add your `lean_lib` entry (`globs = ["X.+"]`) in the SAME commit as your
  first `.lean` file; a glob over a directory missing from the commit breaks everyone's build. A conflict in a shared file (lakefile, DECISIONS.md, SIZE.md) is resolved by reading
  both sides. Talk to the owner of a layer you need something from (SendMessage); do not build
  your own copy of their thing.
- Tests are theorems, plants and rows. A plant is a mutation that must go red by name; record the
  plant line in the commit. No unfiltered test suites.
- Process rules from minidregg still apply: PID file or nothing for kills; every loop sleeps and
  has a deadline; disk pressure is Ember's (stop and report, delete nothing).
- Report to ROOT ("main") on events only: first signatures committed, a decision that another
  layer must answer, a law you think is wrong (argue it in DECISIONS.md with both critiques; ROOT
  rules), your first green row, your handoff (write `<LAYER>-LOG.md` in `~/dev/redregg/work/` as
  your continuation before 350K tokens).

## The meta-critique that applies to this whole charter

It was written in one pass by ROOT, from the minidregg map, under the bias that minidregg's layer
names are the right names. The first job of each owner is to attack the row of this table they
own: if the layer should not exist, or should be two, or should be inside another, say so in
`DECISIONS.md` with the critique, and ROOT re-cuts the table. The second job is to attack the laws:
each is a response to a measured minidregg failure (cite the dossier), and a law that answers a
failure nanodregg cannot have is dead weight.
