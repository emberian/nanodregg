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

## GATES-9 · A commit is CURRENT main + its paths, and a path is taken only from a worktree whose base for it IS main's (2026-10-17)

**Decision.** `scripts/commit` refuses, per file and by name, every given path whose version at the worktree's
HEAD differs from current main's (`worktree behind main on <path>: git checkout --detach main, re-apply your
edit`); it refuses the primary checkout (the read-only reference) and any branch checkout; and it hands
pre-push the exact main the candidate was built on (`--base`), so the judged diff is the landed diff.
**Alternatives.** (a) Rebase: three-way merge the worktree's edit (HEAD → worktree) onto main and commit the
merge. (b) Per-hunk ownership. (c) Leave it to review (GATES-8's critique named the hole and left it).
**Why.** The class is a write without a read of the current version. The worktree HEAD is exactly the version
the author read; if it is main's, every byte the candidate removes was removed by the author's edit of the
current file. (a) would land a merge nobody read or built in their own tree (a clean textual merge is not a
correct one); a refusal costs one `checkout --detach main`, which carries the edit when main did not touch the
file and refuses when it did. The base race (pre-push re-reading a moved main) was the more likely cause of
ROOT's "touches decisions/client.md": judged against the moved main, the candidate looked like a revert of
every intervening commit (plant in 9db4020).
**Critique.** The check reads the worktree's HEAD, not what the author's editor read: a full-file write from a
buffer read BEFORE `checkout --detach main` (an agent's Write of remembered content) reverts with HEAD = main,
and nothing here can see it. The reflog (`HEAD@{1}`) would show the previous base, but not which version the
writer actually read. **Meta-critique.** I picked the check git can answer in one command; the remaining hole
is the same class one level up (the editor's read), and I am calling it review's because I cannot measure it.
**Status.** built (9db4020).

## GATES-10 · No separate gate for "a commit reverts another layer's CROSS-LAYER hunk in its own file" (2026-10-17)

**Decision.** The ownership gate does not grow a revert detector. GATES-9 closes the class it would catch.
**The question.** KERNEL-4's 9e60d7f changed PROTOCOL's Protocol/Rows/Sim.lean under CROSS-LAYER; PROTOCOL-4's
051a8cc, a protocol commit of its own file, reverted that hunk. Should owners refuse a commit whose diff of its
own file undoes a hunk a CROSS-LAYER commit landed?
**Why not.** Every way that revert happens silently is a stale base: the author's copy predates the hunk.
GATES-9 refuses exactly that (plant: a worktree at f654009 = 9e60d7f^ editing Protocol/Rows/Sim.lean →
`REFUSED — worktree behind main on Protocol/Rows/Sim.lean`). With the base equal to main, the author's
editor showed them the hunk and they removed it: that is a deliberate edit of their own file, which law 9
allows (`git revert` is always allowed) and which a reviewer judges. A detector would have to blame every
removed line back to its commit and read that commit's message: a heuristic with false positives on every
legitimate rewrite of a file another layer once touched (the owner is MEANT to own the file), for a case
GATES-9 has already made deliberate. **Critique.** The GATES-9 critique's hole (a stale editor buffer
written whole over a current file) is exactly the case a blame-based detector WOULD catch and GATES-9 does
not. If one more silent revert happens with HEAD = main, this decision is wrong and the detector is the
answer. **Meta-critique.** "Closed by the other fix" is the conclusion that saves me building a hard gate;
it rests on the claim that an agent's tooling re-reads the file it edits, which is true of Edit and false of
Write.
**Status.** decided; reopen on the first revert with a current base.

## GATES-11 · One landing clone (hbox), N judge slots under flock, every target built and censused every commit (2026-10-17)

**Decision.** (MIGRATE-HBOX's four asks, ROOT/Ember's load ruling.) `scripts/commit` lands only in a clone whose
own config says `nanodregg.landing=true` (hbox); every other clone is a reader that follows origin with
`scripts/mac-pull`. Judges take one of N slots (`nanodregg.gateslots`, default 4 on the landing clone, else 1),
each `$common/nanodregg-gate-<k>` with its own tree and .lake, held by an flock(1) fd for the life of the
judging process; standing takes one flock. Every lake/cargo/census run goes through `nanodregg.buildwrap`
(hbox: `swarm-build`, the memory-capped cgroup). pre-push builds EVERY target every commit and always runs the
census; the hand-computed `affected` list is deleted. Worktrees live at `nanodregg.worktrees`.
**Alternatives.** Hostname detection for landing and wrapping; one gate tree; keep `affected`; mkdir+PID locks.
**Why.** A config key is explicit, survives a renamed box, and no pull can carry it to a reader. One gate tree
made box-wide concurrency 1 with 12 lanes landing; CAS already makes two candidates on one base safe. flock
locks die with their holder, so the stale-PID takeover code goes. `affected` could only ever build LESS than
lake's traces would, and it let a commit that changed only gates/axioms-allow.tsv skip the census (plant: a
stale allow row judged `build: nothing to build` → `PRE-PUSH GREEN`).
**Critique.** N slots are N cold .lake trees (a few hundred MB each) and N first builds; four concurrent full
`lake build`s under one 96G cgroup can still thrash it. Building every target makes every commit pay lake's
no-op traversal and a census (MIGRATE-HBOX measures it). A Mac without flock can no longer run standing at
all. **Meta-critique.** I accepted a lane's design whole because it was well argued and the load emergency
made speed feel like the constraint; the slot count is a guess, not a measurement.
**Status.** written 10-17; lands as the first hbox commit.
