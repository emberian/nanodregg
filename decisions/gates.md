# decisions/gates.md — BUILD-GATES (format: decisions/README.md)

## GATES-1 · No package dependencies: Lean core + Std only (2026-10-16)

**Decision.** `lakefile.toml` requires nothing. No Mathlib, no Batteries. `import Lean` only inside `Census/`.
**Alternatives.** Mathlib pinned like minidregg (rev 1c2b90b1); Batteries only.
**Why.** The Mac has ~54 GB free and six agents; Mathlib is ~5 GB of `.lake/packages` per tree and minutes of
`lake` startup per gate run. Nothing in the spec needs it: bytes, maps, digests and Nat arithmetic have `omega`,
`decide`, `simp`, `grind` and `Std.TreeMap` in core v4.30.0. Every minidregg Mathlib use I saw in the Host
closure was the proof system's (`ZMod`, fields, `Finset` sums in Selvage/BabyBear — DELETE-CLOSURE §2).
**Critique.** A proof that needs real algebra (a field for a future PCS, `Finset.sum` for conservation) will be
written badly against core, or someone smuggles a vendored copy. If CODEC's canonicity or KERNEL's conservation
proofs come out 3× longer than with Mathlib, this was wrong. **Meta-critique.** I am reacting to minidregg's
proof-system bloat and to disk pressure; both are real but the second is an estimate of a cost, and a cost
estimate is never a reason (CLAUDE.md). The test: if a layer argues for Mathlib with a named theorem it cannot
state without it, it goes in as a separate proof-only lib that no def-module may import.
**Status.** open.

## GATES-2 · The def/proof split is structural: a `Proofs` path component (2026-10-16)

**Decision.** A module whose name has a `Proofs` component (`Kernel.Proofs.World`) is a proof-module; every
other module is a def-module. `gates/closure.py`: a def-module exports no theorem (private helpers allowed), a
proof-module exports no non-`Prop` definition (statements such as `structure Checked … : Prop` allowed), a
def-module importing a proof-module is red, an exe root is a def-module, and every `.lean` file sits in a
declared lib rooted by `globs = ["X.+"]` (no orphans, no umbrella files).
**Alternatives.** (a) Lean's `module` system (`public section`, `@[expose]`) to stop proof edits rebuilding
dependents without moving files. (b) A content rule (a file with both `def` and `theorem` is red) with no naming.
**Why.** (a) MEASURED on v4.30.0 in a scratch project: with `module` + `public import`, editing only a theorem's
proof in A rebuilt its importer B (twice, different tactics); a comment edit did not. The module system does not
give proof-edit insulation here, so it buys `@[expose]` friction for nothing; files must be split. (b) gives no
way to tell from an import whether it drags proofs into an executable; the name does, and KERNEL and HOST
already chose `Proofs/` independently.
**Critique.** Proofs that are part of a definition's type (subtypes, `decreasing_by`) stay inline, so a def-module
still rebuilds dependents on those edits. And a proof-module may now hide a `Prop`-valued "definition" that is
really a premise bundle (the identity-carrier class) — the vacuity reader (law 6) must read those. **Meta-
critique.** I tested the module system for ten minutes; a lake option I did not try (or a later Lean) may make
(a) right, and I may be keeping file splits because they are visible and checkable by a 100-line script.
**Status.** open.

## GATES-3 · Gates judge a private copy of the exact commit, both by the parent's gates and its own (2026-10-16)

**Decision.** There is no remote, so "pre-push" is the `commit-msg` hook (`scripts/install-hooks` sets
`core.hooksPath=scripts/hooks`). `scripts/pre-push --index` materializes `git write-tree` (so `--only` commits
are judged as recorded) into `<git-common-dir>/nanodregg-gate/tree` with `read-tree -u` (its `.lake` stays
incremental), runs the source gates as defined by the PARENT and by the candidate, builds the changed modules
plus every module importing them (everything if `lakefile.toml`/`lean-toolchain` changed), runs the census, and
`cargo check/clippy -D warnings/fmt --check` for changed crates. One lock directory with a PID file.
**Alternatives.** Build in the shared working tree; build only the changed modules' import closures; one gate
definition (the candidate's).
**Why.** The shared tree is six agents' half-written files: it is systematically greener or redder than HEAD
(memory: verify HEAD, not the working tree). Building only the import closure of a changed module misses the
consumers it breaks (minidregg "per-file green hides a red umbrella", "caller committed, callee not"). Running
only the candidate's gates lets a commit disarm a gate and pass by it (minidregg "hardening commit disarms a
guard"); a deliberate gate change passes the parent's gates only with a `GATE-CHANGE: <why>` line, printed in
the verdict.
**Critique.** `--no-verify` bypasses everything; there is no server to enforce. And `GATE-CHANGE:` is a
one-line bypass anyone can type. Reverse-dependent builds grow with the tree; at 150+ modules a hub edit may
blow the 2-minute target. **Meta-critique.** I built the strongest local gate because there is no remote to
put it on; the honest enforcement is standing.sh at HEAD plus a reviewer reverting, and the hook is a
convenience that makes red commits rare, not impossible.
**Status.** open.

## GATES-4 · One axiom census instead of per-theorem `#assert_axioms` (2026-10-16) — argues law 6

**Decision.** `Census/Axioms.lean` defines `#axiom_census "gates/axioms-allow.tsv" <libs>`: every constant
declared in a tree module may use only `propext`, `Quot.sound`, `Classical.choice`, or a row
`decl<TAB>axiom<TAB>reason`; an allow row matching nothing is red (it cannot outlive what it excused).
`native_decide` shows up as `Lean.ofReduceBool` and so needs a row: that row is the `#assert_compiled` record.
`sorryAx` is always red (and `sorry` is a source refusal too). Run by `gates/census.py` over a generated file
importing every module.
**Alternatives.** Law 6 as written: an `#assert_axioms` line beside each theorem (minidregg has 4,136).
**Why.** A per-theorem line checks only the theorems someone wrote a line for, adds a line per theorem, and
lives in proof files (so it re-runs on every rebuild). The census sees every declaration, definitions
included (a def can depend on `sorryAx` or an `implemented_by` twin's axioms too). FOLLIES F10 in minidregg
proposed exactly this replacement.
**Critique.** The census runs only where every module is built; a commit's census is only as good as the gate
tree's oleans. **Meta-critique.** I prefer one central check because I own the gates; a census is one more
thing that can silently check nothing — so it prints the declaration count, and a planted `sorry` is its
acceptance test.
**Status.** open.

## GATES-5 · The size ratchet's mechanics (2026-10-16)

**Decision.** `gates/size.py` measures the candidate tree (modules, proof-modules, lines per lib, deployed lines,
Host-closure modules = closure of the `lean_exe` named `nanodregg-host`, max dependents of one module, theorems,
partial defs, sorry, extern/implemented_by, Rust lines, plus any `gates/metrics/*` executable's
`metric<TAB>n` lines). SIZE.md's `now` must equal the measurement (`scripts/size-sync PATH…` writes it for
HEAD + those paths); a value above the parent's `now` needs `SIZE: <metric>: <why>`; a raised ceiling needs
`SIZE-CEILING:`; above-ceiling is red; a ceiling nobody measures (protocol operations today) prints
`WARN unmeasured` and makes standing INCOMPLETE.
**Critique.** Every commit that adds code raises "Lean lines" and so must carry a `SIZE:` line: a ritual that
will be typed without thought. The SIZE.md `now` column also conflicts between agents committing in sequence
(the second one re-runs size-sync). **Meta-critique.** Law 12 asks for exactly this, and I implemented it
literally rather than asking whether lines are the right count; ceilings on the few counts that matter
(Host closure, ops, partial, sorry) may be the whole value.
**Status.** open.

## GATES-6 · Law 8's "No import hubs" is unmeasurable as stated (2026-10-16) — argues law 8

Proposal: replace "No import hubs" with a measured count, `max dependents of one module` in SIZE.md with a
ceiling (none yet), and keep the 2-minute rebuild target as the bar. Minidregg's hubs were `Theory.AxiomPin`
(637 Host dependents, 41 lines), `Theory.IndexedProgram` (624), `Theory.TypedAuthorization` (616, 77 defs +
81 theorems), and the cSHAKE spine (585) — the deployed hash imported the PCS, which put 12 Selvage modules and
`Compiler.BabyBear` in the Host (DELETE-CLOSURE §2–3). Every system has a bottom module everyone imports; what
hurt was (1) proofs in the hub and (2) research below the hub. GATES-2 kills (1); C2 (imports must be tree or
Init/Std) plus review kills (2). **Critique.** A count with no ceiling is a number nobody acts on. **Meta.** I am
softening a law because I cannot gate it mechanically.
**Status.** open.

## GATES-7 · Commits stay inside their layer: gates/OWNERS (2026-10-16)

**Decision.** ROOT's ruling after two stale-index collisions (65e3c1c reverted 617bb3a's CHARTER.md; d882895
reverted CHARTER.md and decisions/README.md). `gates/owners.py`: the subject prefix (`kernel:`, `gates:` …) names
the layer; every changed path must be owned by it (gates/OWNERS, longest prefix; unlisted = ROOT) or SHARED
(`SIZE.md`, `lakefile.toml`). Otherwise red, naming each foreign path and owner, unless the message has
`CROSS-LAYER: <reason>`. A commit-msg hook cannot take flags, so the message line IS the `--cross-layer`
override and its record.
**Alternatives.** `lakefile.toml` owned by GATES (ROOT's table); per-hunk ownership.
**Why SHARED for the lakefile.** Every layer must add its `lean_lib` entry in the commit that adds its first
`.lean` file (a glob over a missing directory fails the build); with GATES ownership every such commit would
carry a ritual CROSS-LAYER line. **Critique.** SHARED is exactly where a stale index reverts someone else's
entry; the real defence is that pre-push judges `git write-tree` against current HEAD and `update-ref` refuses
a moved HEAD. **Meta-critique.** Ownership by path is a proxy for "did you mean to change this": it catches the
stale-index class, not a deliberate cross-layer edit with a reason typed in to pass.
**Status.** open (the SHARED lakefile departs from ROOT's table).

## GATES-8 · `scripts/commit` is the only sanctioned way to commit; a commit is refused only for reds it introduces (2026-10-16)

**Decision.** ROOT's ruling after five stale-index incidents. `scripts/commit (-m|-F) [--cross-layer R]
[--no-build R] PATH…` builds the candidate from CURRENT main in a private index plus exactly PATH…, regenerates
SIZE.md for it, refuses any change outside PATH…, runs scripts/pre-push, and lands by compare-and-swap
`update-ref refs/heads/main NEW BASE` (a moved main writes nothing; re-run). Pre-push now reports a closure or
refusal red that the PARENT tree already had as PRE-EXISTING and does not block on it; standing.sh still counts
it, and its owner fixes it forward.
**Alternatives.** Keep `git commit --only` with the commit-msg hook; block every commit while any red stands.
**Why.** `--only` and the shared index both build from an index that can predate someone else's commit; only a
tree built from main at commit time plus a CAS cannot revert work it never saw. Blocking on someone else's red
stops all six layers for one layer's defect (it happened: CODEC's `def manyBytes` in a proof-module).
**Critique.** A PATH that is itself a stale copy of a file another layer just changed still reverts it, and
nothing here can tell; PRE-EXISTING lets a red sit as steady state ("red as steady state hides everything").
**Meta-critique.** A wrapper script is the tool I can build fastest; the class is "a write without a
read of the current version", and only the CAS addresses it, the rest is convenience.
**Status.** open.

## GATES-9 · The waste ratchet measures from the sims' own output: `WASTE <op> <metric> <ratio>` (2026-10-16)

**Decision.** Law 5's waste ratio is pinned in gates/waste.tsv (`op metric ceiling measured source`). The
measurement is a line `WASTE <op> <metric> <ratio>` printed by any `*-sim` exe (ratio = work done / work the
operation must do, e.g. bytes appended per byte of Turn frame, cells read per cell touched, fsyncs per batch).
standing.sh collects them: a pinned row above its ceiling is RED, a pinned row nothing measured is RED, a
measurement without a row is listed `unpinned`. Commit-time (`gates/waste.py` in pre-push) only checks the table:
ceilings never rise and rows never vanish without `WASTE: <op>: <why>`. No measurement and no row = ABSENT =>
standing INCOMPLETE.
**Alternatives.** `perf stat --no-scale` instruction counts (law 5's wording); running the sims in every
pre-push.
**Why.** perf does not exist on the Mac and instruction counts are noisy across machines; a ratio of logical
work the code itself counts is deterministic under the seeded sim, so the ceiling can be exact and only fall.
Sims in pre-push would put the slowest stage in front of every commit; standing runs them at HEAD.
**Critique.** A ratio the code reports about itself can lie (the counter sits next to the work it counts and
drifts from it); and logical work misses constant factors (a `List UInt8` copy counts as one "byte appended").
The ratio is only as good as HOST's counter. **Meta-critique.** I chose the measurement I can gate without a
perf box; wall time on the laptop is the measure THE BAR actually uses (write ≤ 5 s, reopen ≤ 60 s) and this
does not see it.
**Status.** open.
