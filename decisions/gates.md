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
**Status.** built: 194cefb (the first hbox commit) and d5871cb. 194cefb's message lost three quoted plant
lines to shell substitution while it was being filled on hbox (history is not rewritten); they are, verbatim:
the reader plant `scripts/commit: REFUSED — this clone is a reader; main lives on hbox: ssh hbox, cd
/tank/dregg-build/nanodregg/wt/<layer>`; the LAKE-DROP summary line `targets: lakefile dropped target
host-file-sim; needs 'LAKE-DROP: host-file-sim: <why>'`; and, from the first cold slot build, `build: RED` /
`census: RED` with `error: Lean exited with code 143` (earlyoom, Codec.Proofs.Ed25519 at 9 GB), which became
d5871cb's KILLED(load). The stale-allow-row plant, re-run warm: `allow row matches nothing:
Nanodregg.Kernel.noSuchDecl Lean.ofReduceBool`.
**Amendment (d5871cb, ROOT 10-17).** A step killed by signal 15/9 with no real Lean error is `KILLED(load)`:
pre-push exits 76, scripts/commit writes nothing (`NOT JUDGED … re-run`). Memory-weighted per-module seats
(minidregg 5e29e086) were considered and not built: lake schedules modules, so weighting them means a second
scheduler beside lake's. **Critique.** A commit that itself makes a module's elaboration explode (a reduction
bomb) is killed every time and reads as load forever; the log names the module, and a second KILLED on a quiet
box is the author's. **Meta-critique.** I declined the seat scheduler partly because it is big; the honest
reason that survives is that it duplicates lake, and the 9-14 GB proof module is the defect to fix.

## GATES-12 · The TCB table is gated: what the tree trusts without a proof has a row, pinned to what is actually used (2026-10-17)

**Decision.** (ROOT ruling 10-18; HOSTING-5 created `gates/tcb.tsv` in 0eb0803.) `gates/tcb.py`, run by check.py as
gate `tcb`, refuses by name: a malformed row, an unknown kind (trusted-unverified | verified | platform-fact) or
owner (a layer in gates/OWNERS, or ROOT), two rows for one component; a crate of the root Cargo.lock on the
crypto/TLS match list (`CRATES`/`PREFIXES` in tcb.py, data) with no row whose component is its name, or whose pin
is not exactly its locked version set; a row for a listed crate no longer locked (stale); no `lean4` row, or its pin
is not lean-toolchain's version; a native_decide allow row (an `…._native.native_decide.ax_…` axiom, or
Lean.ofReduceBool/ofReduceNat/trustCompiler) whose theorem has no `native_decide:<theorem>` row pinned to the
toolchain, and the converse stale row; a gates/native-allow.tsv module with no `extern:<module>` row, and the
converse; a lake-manifest package with no row. This commit carries a row for every component that is matched today
(42 rows beside HOSTING-5's two), with the text CODEC-6 and CLIENT-3 sent for theirs.
**Alternatives.** (1) One `native_decide` row pointing at gates/axioms-allow.tsv. (2) Read the build graph (`cargo
tree --target all`) instead of the lock. (3) Rows only for direct dependencies; transitive crates covered by their
parent's row.
**Why.** (1) A pointer row lets native_decides accrue with no TCB line ever being written: the gate would refuse
nothing. One row per theorem, pinned to the toolchain, makes a toolchain bump re-read every compiler-trusted
verdict. (2) The lock is a superset, deterministic and pure data: a locked crate is one feature away from built,
and a source gate that runs cargo is a second build. The cost is rows that say "locked, outside every build
graph … trusted for nothing today" (pkcs8, der, spki, const-oid, base64ct, rand_core, x509-parser, der-parser,
asn1-rs*, oid-registry), measured with cargo tree at 0eb0803. (3) A bug in block-buffer or subtle breaks the
signer as surely as one in sha2; a row per crate is what makes a new transitive crate visible in review.
**Plants** (`logs/gates3-plants.sh`, candidate = main + the gate files + one mutation, judged by pre-push
--no-build): control `PRE-PUSH GREEN`; `tcb: crate untrusted 0.9.0 is in Cargo.lock with no gates/tcb.tsv row`;
a new locked crate `tcb: crate hmac 0.12.1 is in Cargo.lock with no gates/tcb.tsv row`; `tcb: crate ring: gates/tcb.tsv
pin 0.17.13 but Cargo.lock has 0.17.14`; `tcb: stale gates/tcb.tsv row: crate sha3 is not in Cargo.lock`; `tcb:
native_decide allow row for Nanodregg.Kernel.Proofs.planted with no gates/tcb.tsv row
native_decide:Nanodregg.Kernel.Proofs.planted`; `tcb: lean4: gates/tcb.tsv pin v4.29.0 but lean-toolchain is v4.30.0`;
`tcb: native-allow module Host.File (trusted C) with no gates/tcb.tsv row extern:Host.File`; `tcb: gates/tcb.tsv:5:
ring: kind 'trusted' is not one of …` and `owner 'NOBODY' is not a layer in gates/OWNERS`.
**Critique.** The match list is a name list: a crypto crate under a name it does not know (a new RustCrypto crate,
a vendored fork, a `-sys` wrapper under another name) passes with no row, and the gate cannot tell. The gate checks
that a row EXISTS and its pin matches; it cannot check that "trusted for" is true or complete: the rows for
platform binaries (nd-bwrap, sandbox-exec, cc) carry sha256 pins nothing re-measures, and Lean's own Lean-side
trusted code (CODEC's Sha512 and Hash rows, which CODEC-6 adds itself) is not detectable by any rule here, so those
rows depend on the layer writing them. **Meta-critique.** I made the gate as strict as data allows (lock not
build graph, every transitive crate) partly because strictness is easy to defend; the honest cost is ~15 rows that
say "trusted for nothing", which is noise a reader must skip, and the unmatched-name hole is the one that matters.
Reopen if a crypto crate lands that the list did not name: then the list is wrong, not the commit.
**Status.** built (this commit).

## GATES-13 · A codec vector is immutable under an unchanged tag (2026-10-17)

**Decision.** (CODEC-6's ask on CODEC-28 (d), ec2db07.) `gates/vectors.py`, check.py gate `vectors`: for every
(site, tag) present in both the parent's and the candidate's gates/codec-vectors.tsv, the candidate's rows are the
parent's rows byte for byte: an edited, removed or added row under an unchanged tag is red by name. A site whose
tag moved is free (`codec-vectors --write` re-draws it, and `--check`, a gates/generated.tsv row, proves every row's
tag is the site's CURRENT tag and its bytes decode to its text).
**Why.** `--check` is a decode check, not byte equality, so a hand edit of a same-tag row's text to the relabelled
meaning checks green: the relabelling CODEC-28 (d) exists to catch would pass with the table edited to agree. The
two halves cover each other: a hand edit that also invents a tag is refused by `--check` (tag != current tag); a
hand edit under the real tag is refused here.
**Alternatives.** Byte equality of the whole table against `--write`'s output (refuses CODEC's design, which keeps
old-tag rows verbatim and draws from a generator only on a move); OWNERS `gates/codec-vectors.tsv SHARED` so a
re-pin needs no CROSS-LAYER (not done: that loosens the owners check, a pause item, and this gate does not need it).
**Plants** (`logs/gates3-vplants.sh`, main + gate files + one mutation, pre-push --no-build): control `PRE-PUSH
GREEN`; `vectors: gates/codec-vectors.tsv: bool vector 0 edited under its unchanged tag c4615aa8e59d: 'ok false' ->
'ok true' (a change of meaning needs a new tag: rename the refinement)`; `… i64 vector 1 removed under its unchanged
tag 7ea896dd7e23`; `… bool vector 2 added under its unchanged tag c4615aa8e59d`; and the control that a moved tag
re-draws freely: bool's two rows under a new tag with new text, `PRE-PUSH GREEN` (this gate; `--check` judges the tag).
**Critique.** The comparison is against the PARENT only: a row's history is one commit deep, so two commits that
each change nothing per-commit cannot exist, but a tag that moves away and later moves BACK to an old value lets
that old tag's rows be re-drawn with no record of the first meaning. Tags are content hashes of the codec's shape,
so returning to one means the shape returned too; the meaning of the old vectors is then the meaning of that shape.
**Meta-critique.** I took the 20-line version CODEC-6 specified; the deeper question, whether "decoded text" is a
faithful enough witness of meaning (Repr can print two different values alike), belongs to CODEC's printer.
**Status.** built (this commit).

## GATES-14 · The ungated toy run is deleted; the judge writes its own PID (2026-10-18)

**Decision.** (a) `kernel-sim --toy` is deleted (Kernel/Sim/Main.lean runs the deployed parameters and refuses `--toy` by name; the
Kernel/Sim.lean docstring says so). The toy PARAMETERS stay: `lang-journey`, `host-sim`, `Protocol.Rows.Sim` and the codec
teeth build on `Kernel.Sim.toy`; only the one ungated driver of the generator under them goes. (cv 01a14d89-b259;
KERNEL-47's find: `carry-budget-plant` red on 9/16 seeds at the 8-byte digest with and without the real code.)
(b) `scripts/commit`'s header gains the rule: a detached landing records the PID of scripts/commit ITSELF
(`nohup bash -c 'exec scripts/commit -m MSG PATH...' > LOG 2>&1 & echo $! > job.pid`), not a subshell's; never stop a judge
by its PID file, wait for it with a deadline. And the attempt that judges, which is a re-exec of main's own copy (so
`$!` of the outer is not its PID once anything wraps it), writes `$$` to `$NANODREGG_COMMIT_PID_FILE` when that is set
(one line). (cv 01a14be4-9353; KERNEL-12's orphaned judge.) CROSS-LAYER: Kernel/Sim is KERNEL's.
**Why (a).** A run in no gates/runs.tsv row is one nobody reads, and this one's plant could not go red: at a UInt64
digest a cell weighs less than the 32 bytes a retire charges per digest field, so no live set can outweigh a retire and
`carry-budget-plant:overflow` has nothing to find. "A plant that cannot go red is not a plant" (CHARTER, teeth; a gate
that cannot go red is not a gate). An ungated run with a vacuous plant is worse than no run: it reads as coverage.
**Alternatives.** (1) A runs.tsv row `kernel-sim --toy --seeds N` that must PASS, with the plant made to bite by scaling
the retire charge to the toy digest width (`digestWeight` is the constant 32 in Kernel/Turn.lean and the plant's crafted
carry is built against it). Biting needs the weight function parameterised on the digest width, which touches
Kernel/Budget, its proofs (`Kernel/Proofs/Budget.lean` names this arm as its tooth) and the deployed weight pins: far more
than 20 lines, and it would change what `logWeight` means at the toy only to make a toy plant bite. Not done. (2) Keep
`--toy` and skip the plant at a toy width, as `weighed` already skips the logWeight comparison (Gen.lean:309): a run that
silently skips its own teeth is the same defect with a quieter face. Not done. The plant itself stays and bites in the
gated deployed run (runs.tsv `kernel-sim --seeds 64`, `carry-budget-plant:overflow` in `Gen.planted`).
**Plants.** (a) `kernel-sim --toy 1` exits 2 with `kernel-sim: --toy was removed (GATES-14 …)`, not a silent deployed run (the first draft let `parseSeeds` ignore the flag and print ALL PASS; found by running it). `grep -rn -- '--toy' gates scripts lakefile.lean` empty (only decisions history names it). (b) `logs/gates4-pidplant.sh`
from a layer worktree, running the re-exec'd path directly with SIZE.md (refused right after the PID line): control, the
file holds the script's own PID (`bash -c 'echo $$ > own; exec scripts/commit ...'` then `pf == own`); var unset, no file;
the line removed from a copy, no file, plant red. Output: `control: PASS`, `unset var: PASS`, `mutation (line removed):
RED as it must`.
**Critique.** Deleting the mode leaves the generator under toy parameters untested by any simulation other than the
journeys' own: the toy Gen coverage (random acts at a UInt64 digest, where tries are shallow and adversarially weak,
decisions/kernel.md) was real signal for the other 11 planted refusals, and it is gone. It was ungated, so no landing
depended on it, but a developer iterating on a probe in seconds at a toy lost a fast loop; the deployed run is minutes.
The PID line only helps a caller who sets the variable; the rule in the header is prose, and nothing refuses a
subshell-wrapped landing.
**Meta-critique.** I priced option (1) as "more than 20 lines" without writing it; the estimate is from the call sites I
read (Budget, its proof file, the weight pins), and the instruction preferred deletion above that bound. The wording
"cannot go red" is the real reason, not the cost: even at 5 lines a plant that bites only because the toy charge was
retuned tests the retune, not the deployed budget. And the PID plant runs the inner path directly: it does not exercise
the outer re-exec materialisation, which `scripts/commit` landing this very commit does (the first landing after this
one is its end-to-end check).
**Status.** built (this commit).

## GATES-15 · A runner that cannot read a failure is not a runner: every verdict reader proves it can read red first (2026-10-18)

**Decision (landing A, this commit).** (cv 01a14e41-d666; CLIENT-6's mutation harness read every mutation green behind `cargo test -q`.)
(1) scripts/pre-push judges the verdict runs fail-closed. If runs.py or waste.py printed no verdict line (`runs: …` / `waste-measured: …`), exited 1 with no named red, or exited with any other code, the result is `runs: NO VERDICT …` and RED. If a run has no binary after a green build (`ABSENT`), that is RED as well. None of these is ever PRE-EXISTING: they all come from the candidate's own runner and build. A failed copy of the runner is red; before this, judge_runs returned 1 and its caller ignored it.
(2) runs.py prints every failure line of a red run as its own key (`    red RUN: LINE`: an exe's FAIL/FAILED/BLIND/RED lines, a cargo row's failed test names). PRE-EXISTING is now judged line by line, so a new failure behind an old one on the same exe counts as new. Before, the key was `run EXE ARGS` alone.
(3) Cargo rows of gates/runs.tsv gain a fourth column, the known-red control, which runs FIRST:
- `nobin RED`: the run with ND_LEAN_BIN set to an empty directory must read red and name a failed test. If it does not, the test never drove the exes it names: `RED(harness: the known-red control passed: …)` and its runs are `UNREAD`.
- `nobin ok`: the test runs no exe and must pass without any. cargo:launcher:path_vectors reads the compiled-in table; emit-hosting only selects it.

The cargo reader is proven in every invocation: whenever a cargo row runs, some `nobin RED` control runs first. check.py refuses a table in which no cargo row has one. A cargo run passes only if libtest's summary says at least one test passed. Zero tests, or no `test result:` line, is `RED(harness: …)`. The launcher tests are `#![cfg(target_os = "linux")]` and are empty anywhere else. ABSENT counts as INCOMPLETE in runs.py's own verdict (it used to be dropped).
(4) `rust_changed` judges the workspace whole when the root Cargo.toml does not parse or names no member list (it used to skip the Rust steps).
(5) `scripts/plant` is the in-tree plant harness and replaces ~/gates2/plant2.sh/plant3.sh, which piped pre-push through grep and so read no exit code at all; a human read the output. Its interface: `scripts/plant [--build] [--with PATH]... NAME EXPECT [PATH=FILE]...`. The candidate is main + the --with files + the mutation, never committed. The verdict is `PLANT NAME RED: <line>` only on exit 1 with EXPECT read; `GREEN` is a control that must exit 0. Output and exit code are read from files. Its own known-red control runs first: a conflict marker in gates/harness-control.txt, refused by the `paths` gate. If that does not read red by name, every plant is refused: `plant: harness: the known-red control passed`.
**Landing B (next, one CROSS-LAYER commit; ROOT 10-18).** Every Lean verdict exe gains `--harness-control`. It adds one expectation nothing meets INSIDE its ordinary run, so it reads `FAIL … harness-control` by the normal verdict path. runs.tsv then requires the column on every verdict row (the landing-A clause that lets a Lean row omit it is deleted), runs it first, and reads no verdict of an exe whose control does not read red. kernel-sim's half lands after KERNEL-18's trie day, with KERNEL's two fail-opens fixed in the same commit: parseSeeds silently drops unknown arguments (`kernel-sim foo` runs zero seeds and prints ALL PASS), and below 16 seeds the planted-refusal gate is skipped while ALL PASS prints.
**Why.** The runner is the one component every verdict passes through, and nothing checked that it could read red. Measured with the OLD judge (main's scripts/pre-push, candidate = main with runs.py raising at entry, built): `runs: ok ()` / `PRE-PUSH GREEN tree c260c49f760b`. A broken runner landed green. standing.sh was already fail-closed here: it maps runs.py's exit code and runs waste.py through `run`. The six standing GREENs (2f5a201, 53af302, 10fd373, 2d76795, 38d94e1, 42c261b) each carry `runs: ok`, `waste-measured: ok`, their run lines, no traceback and no zero-test summary. None was a silent crash.
**Alternatives.** (a) Make a crash a key like any red, so a parent that crashes too reads PRE-EXISTING. Refused: the parent is judged by the candidate's runner, so a crash on both sides is the candidate's own defect. (b) A synthetic control (a stub process printing FAIL) instead of the real tool. Refused: it proves the parsing function and not the tool's real output. The CLIENT-6 failure was exactly a reader that matched a format the real tool did not print. (c) A source scan for ND_LEAN_BIN to decide nobin RED vs ok. Refused: the tests reach it through devtools/src/lib.rs and launcher/tests/common, so the scan is prose-matching. Running the test without the binaries measures it.
**Plants** (hbox logs/gates5-plants.sh, gates5-plants2.sh, gates5-oldjudge.sh; candidate = main + this commit's files + one mutation, built):
- `PLANT runs-crash RED: runs: NO VERDICT runs.py printed no verdict line (exit 1)`. Under the old judge the same crash: `runs: ok ()`, `PRE-PUSH GREEN`.
- `PLANT waste-crash RED: runs: NO VERDICT waste.py printed no verdict line (exit 1): RuntimeError: planted crash`
- `PLANT nobin-red-passes RED: run cargo:launcher:path_vectors  (control): RED(harness: the known-red control passed: ok)`
- `PLANT nobin-ok-lies RED: run cargo:client:stdio  (control): RED(harness: declared `nobin ok` but with no Lean binaries it read RED(FAIL a_resident_runs_world_verbs_through_nd_stdio_and_nothing_else))`
- `PLANT zero-tests RED: run cargo:client:stdio : RED(harness: zero tests ran)` (every #[test] ignored)
- `PLANT cargo-toml-unparsable RED: cargo-check: RED`
- Plant the plant: scripts/plant with its control file made benign gives `PLANT harness-control FAIL: pre-push passed it (exit 0) …` / `plant: harness: the known-red control passed — no plant is read`, exit 1.
- Control: `PLANT landa-green2 GREEN` with `runs: ok (36 runs of 30 exes)`: 10 `nobin RED` controls read red, path_vectors' `nobin ok` passed.
Measured before the column was written: 10 of the 11 cargo rows go red with no Lean binaries, and path_vectors stays green.
**Critique.** The `nobin` control proves that a cargo test needs SOME binary. It does not prove that the test checks what that binary answers: a test that only spawns `host --version` would pass it. The Lean `--harness-control` (B) proves an exe's aggregation reads one false expectation. It does not prove that each plant inside the exe is wired; that stays per-plant teeth (kernel-sim's required arms, rows' BLIND). Per-line PRE-EXISTING is conservative: a pre-existing red whose FAIL text embeds a count that the candidate legitimately moves now reads as new and blocks. The fix is to fix main's red, which is the pressure wanted, but it can block an unrelated lane. Exit 3 (pending rows, a `HANG`) still does not block pre-push. That is by design (law 7, pending is an outcome) and is kept; standing reports it INCOMPLETE. The rust_changed hole was reachable only with a root Cargo.toml already unparsable on main (an unparsable candidate manifest is itself a changed path). An absent gates/generated.tsv still means zero generated checks; deleting it is a GATES-owned change in review, and that is not a gate.
**Meta-critique.** I found the pre-push hole by having the audit read the plumbing around the runners rather than the runners alone. Every runner the audit read was fail-closed inside; the open path sat in the code that reads them, the code I own. The brief named the exes. A brief that names targets finds the targets.
**Landing B (2026-10-19, CROSS-LAYER; KERNEL-18, PROTOCOL-12, OPS-4 agreed; ROOT for HOST, LANG, HOSTING, LEDGER).** Eight Lean verdict exes take `--harness-control`: kernel-sim, host-sim, host-file-sim, hosting-sim, ledger-sim, lang-journey, rows, store-plants. Each adds one expectation nothing meets inside its ordinary run and reads it by its normal verdict path: kernel-sim adds `harness-control` to the required planted arms (`FAIL planted refusals never met: [harness-control]`); host-sim, host-file-sim, hosting-sim, ledger-sim and lang-journey add one false check to the failure count; rows reads every plant at a line its row does not have (`BLIND … (harness-control)`); store-plants judges the intact copy as if it had to be refused `corrupt`. gates/runs.tsv carries the control as the fourth column of every verdict row and runs.py requires it: the landing-A clause that let a Lean row omit it is deleted, and a verdict row whose control lacks `--harness-control` is refused by name. The arguments are now read strictly. host-sim and host-file-sim read any unknown argument as seed 1, lang-journey took no arguments at all, and kernel-sim's parseSeeds dropped what it could not read (`kernel-sim foo` ran zero seeds and printed `ALL PASS`; `--seeds 0` likewise). Each now refuses an argument it does not read with exit 2 and a usage line. kernel-sim below 16 seeds skipped the planted-refusal gate and still printed `ALL PASS`; it now ends `PLANTS NOT JUDGED (N seeds; …)` with exit 3, so its control runs at `--seeds 16 --harness-control`.
**Plants (B)** (hbox logs/gates5-plantsB.sh; `scripts/plant`; candidate = d377d5b + B's 12 files built; the same diff, md5 1772074e, lands on 8ad3982, and no file of B changed between the two):
- Control: `runs: ok ((44 runs of 30 exes))` with all eight Lean controls `ok(known-red control read red)`, e.g. `run kernel-sim --seeds 16 --harness-control (control): ok(known-red control read red)`.
- `PLANT rows-control-inert RED: run rows --harness-control (control): RED(harness: the known-red control passed: ok)`, then `run rows : UNREAD(its known-red control did not read red)` (Protocol/Rows/Run.lean with the control made inert).
- `PLANT verdict-row-no-control RED: runs: gates/runs.tsv:10: verdict row host-sim needs a known-red control, an argument list with --harness-control (GATES-15)` (check.py refuses the table).
- `PLANT args-refused RED`: `run kernel-sim foo: RED(exit 2, last line: usage: kernel-sim [SEED… | --seeds N] [--harness-control] (got [foo]))`; `run kernel-sim --seeds 0: RED(exit 2, …)`; `run host-sim foo: RED(exit 2, …)`; `run host-file-sim 1 2 3: RED(exit 2, …)`; `run lang-journey foo: RED(exit 2, …)`; `run kernel-sim 1: INCOMPLETE(PLANTS NOT JUDGED (1 seeds; the planted refusals need 16 or more))`.
**Critique (B).** The control proves an exe's aggregation, its count and its exit read one false expectation. It does not prove that each plant inside the exe is wired. PROTOCOL-12's scope: in rows the control reaches only the `.caught` plant rows (27 at review, 29 after PROTOCOL-47). OPS-4's scope: in store-plants it proves `judge`, the count and the exit, not the rows that print through their own `say` predicates (live, carry, join, seal, use). Those stay per-plant teeth: kernel-sim's required arms, rows' BLIND. A plant row with `kernel-sim 1` would read INCOMPLETE, not red: exit 3 is pending by law 7, and standing reports it INCOMPLETE.
**Status.** A landed 56f4689; B landed in this commit. cv 01a14e41-d666 closes with it.

## GATES-16 · A wall-clock deadline withholds a verdict, never gives one: a timed-out run is UNREAD, re-run once, and the commit is not judged (2026-10-19)

**Decision.** gates/runs.py runs a run past DEADLINE (600 s of wall clock) once more. A second timeout is `UNREAD(timeout twice: past 600 s of wall clock; last line: …)`, the last line coming from what the run printed before it was killed. It is never RED. runs.py's verdict for a table with no red and a twice-timed-out run is `runs: UNREAD(timeout)`, exit 76, the code KILLED(load) already uses: pre-push prints `runs: NOT JUDGED (UNREAD(timeout)) — re-run` and `PRE-PUSH NOT JUDGED tree …`, and scripts/commit writes nothing and says why. A known-red control that times out is UNREAD as well, and the exe's runs are UNREAD under it, as for a killed control. standing reports `runs=UNJUDGED(first killed or twice-timed-out run)`, which is INCOMPLETE, never GREEN. A timeout is no longer a pre-push key (`run X` keys come from RED lines only), so it is never PRE-EXISTING either. `ND_RUN_DEADLINE` overrides the 600 s; a shorter deadline can only withhold verdicts.
**Why.** KERNEL-19's attempt 2 (logs/kernel19-land2.log) was refused on `run cargo:launcher:isolation : TIMEOUT(600 s)` / `runs: NEW RED run cargo:launcher:isolation` with no Rust changed; attempts 1 and 3 ran the same test green. The judge slots run four judges at once on 24 cpus; THE BAR printed `load-before 20.83 19.58 15.88 (24 cpus)` inside one of this decision's plants. A fixed wall-clock number measures the box as much as the commit: that is the wall-clock class the gates refuse everywhere else ("no wall-clock benchmarks"), sitting inside the judge. Before this, a timeout read RED, blocked the lander for nothing it did, and printed no line of what the run was doing.
**Alternatives.** (a) A deadline that scales with load. Refused: still wall clock, and still able to manufacture a red. (b) A per-row deterministic budget (the test's own step count). Right in principle and not available: a cargo test has no step counter the runner can read. Its form here is the tests' own: every wait inside a test carries its own deadline and FAILs by name (launcher/tests mostly do: common::wait_until, the 10/20/30/60 s loops). A run that times out at 600 s is then a hang no test deadline caught, and the partial output now names it (libtest prints a test running past 60 s). (c) Re-run on a quieter slot. A slot cannot be chosen from inside the judge; one immediate re-run is the form available, and a lane re-running scripts/commit gets a fresh slot.
**Not weaker.** A timeout was RED; it is now not judged. Neither lands. A commit that hangs a test still never lands: it reads NOT JUDGED on every attempt. A timeout that the parent also had used to be PRE-EXISTING and let the lander through; it now holds the lander until the hang is fixed. Standing never reads GREEN with a timed-out run.
**Plants** (hbox logs/gates6-g16plants.sh, .out; candidate = main + this commit's files, built):
- `ND_RUN_DEADLINE=1`: `run script:scripts/bar.sh --records 60 --standing --root {fresh} --harness-control (control): UNREAD(timeout twice: past 1 s of wall clock; last line: no output)`, then `run script:scripts/bar.sh … : UNREAD(its known-red control did not read red)`, `runs: NOT JUDGED (UNREAD(timeout)) — re-run`, `PRE-PUSH NOT JUDGED tree 6fd97f630ae8: runs — …`, scripts/plant exit 76.
- Control: `PLANT g16-green GREEN (control)` (the default deadline: `runs: ok (2 runs of 1 exes)`).
- A red stays red: runs.tsv with bar.sh's pass line changed reads `run script:scripts/bar.sh --records 60 --standing --root {fresh}: RED(exit 0, last line: BAR verdict PASS)`, `runs: RED`, `PRE-PUSH RED`.
- The old judge: KERNEL-19's attempt 2, quoted above.
**Critique.** A real hang now costs a lander two deadlines (20 min) per attempt instead of one, and it reads NOT JUDGED rather than naming a red; the partial output in the log is where the name is. KILLED(load) and UNREAD(timeout) share exit 76, so a lane that loops on NOT JUDGED will loop on a real hang too. The message says which, and the log has the last line.

## GATES-17 · A standing-only verdict row: `standing:EXE` runs in standing and never in pre-push (2026-10-19)

**Decision.** gates/runs.tsv accepts a row key `standing:EXE` for a lean_exe EXE. It has the four columns of an exe row and needs a `--harness-control` control; `-` is refused. An EXE has one row, plain or standing. runs.py runs `standing:` rows only with `--standing`, which scripts/standing.sh passes and pre-push never does. Without it the row prints `run standing:EXE: NOT RUN(standing-only)`, whatever changed, a lakefile or runs.tsv change included. First row: PERF-5's bench-worstcut, about 4.5 min with its control (ROOT: standing-only).
**Absence is refused.** Deleting the row reds check.py: `lean_exe EXE has no row`. Turning it into a `-` row passes check.py, but its pinned WASTE rows then go unmeasured, and standing's full waste check (waste.py --measured) reds a pinned row with no measurement. Pre-push's waste check is partial and skips pinned-but-unmeasured rows, which is why the row may be absent from pre-push without going red there.
**Alternatives.** (a) A separate standing table (gates/standing-runs.tsv). Refused: two tables that classify the same exes are two shapes that will disagree; check.py would have to join them. (b) A fifth column. Refused: every row would gain a column that means nothing for all but one, and the strict four-column parse would need an optional field again (the leniency GATES-15 B deleted). (c) Select standing rows by a cost estimate. Refused: wall clock.
**Plants** (hbox logs/gates6-g17plants.sh, .out; ledger-sim's row as the stand-in standing row):
- `PLANT g17-dash RED: runs: gates/runs.tsv:13: a standing row is a verdict run (runs, pass, a --harness-control control), never `-``
- `PLANT g17-dup RED: runs: gates/runs.tsv:41: second row for ledger-sim`
- `PLANT g17-gone RED: runs: lean_exe ledger-sim has no row in gates/runs.tsv …`
- `PLANT g17-prepush-skips GREEN (control)` with a runs.tsv change (which selects every exe) and `run standing:ledger-sim: NOT RUN(standing-only)`. Pre-push never ran it.
- The standing side, that the row runs under --standing and its unmeasured waste rows red, is quoted by PERF-5's landing from the first standing that holds bench-worstcut.
**Critique.** A standing row's verdict arrives a landing late, at the next standing and not at the commit that broke it. That is the price ROOT accepted for a minutes-long bench. Standing names the first red run, so the breaking commit is found by bisecting standing, not by the judge.

## GATES-18 · A CROSS-LAYER reason names the owner of each foreign path (2026-10-19, ROOT ruling)

**Decision.** gates/owners.py no longer accepts any `CROSS-LAYER:` line as cover for every foreign path. Each foreign path's owner layer (gates/OWNERS, longest prefix; ROOT for a path no row covers) must be named in some CROSS-LAYER line of the message. It must appear as a word, alone or as a lane: `HOST`, `HOST-13 agreed`, `ROOT for HOST` (the form for a layer with no live lane). A layer named only inside another word does not count: `HOST` is not named by `HOSTING`. `_` and `/` separate words, so `ROOT_for_HOSTING/LEDGER` names both. An unnamed owner is refused path by path: `KERNEL commit touches gates/waste.tsv, owned by GATES, and no CROSS-LAYER line names GATES`, followed by the line to add. scripts/plant's own message names every layer OWNERS lists (and ROOT), so a plant mutating any layer's file still passes owners. `--cross-layer REASON` replaces that line, and an empty REASON omits it, to plant the owners gate itself.
**Why.** c18e028 (KERNEL-53) changed gates/waste.tsv under a reason naming only HOST and PROTOCOL, and nothing objected. Before this rule, a CROSS-LAYER line with any text covered every path of every layer, so the record could say nothing about the owner it bypassed. Replaying the new rule over the last 150 first-parent commits of main (logs/gates6-replay.py) refuses 16 of the 55 that carry CROSS-LAYER. The owner most often left unnamed is GATES, for gates/codec-vectors.tsv, gates/waste.tsv and gates/ceilings.tsv inside a flag day. Others: CODEC for Emit/Rust.lean / client/src/generated.rs in protocol commits, PROTOCOL/OPS in 1ed7867, GATES for gates/OWNERS in c4d9229.
**Not weaker.** It refuses strictly more than before. It still checks only that the owner is NAMED: the reason is the record, and the owner's agreement is the lander's word, not something this gate can verify.
**Alternatives.** (a) Require `<LAYER>-N agreed`. Refused: ROOT stands in for retired lanes, and the "agreed" wording carries no more truth than the name. (b) Case-insensitive names. Refused: `codec`, `host` and `ops` are ordinary words in reasons; lane names are upper case.
**Plants** (hbox logs/gates6-g18plants.sh/.out, gates6-g18default.out; candidate = main + owners.py + scripts/plant + Host/Store.lean with one comment character changed, no build):
- `PLANT g18-wrong-layer RED: owners: GATES commit touches Host/Store.lean, owned by HOST, and no CROSS-LAYER line names HOST` (reason `HOSTING-9 agreed`)
- `PLANT g18-no-reason RED: owners: split the commit, or add 'CROSS-LAYER: <reason>' naming each owner to the message`
- `PLANT g18-named GREEN (control)` (reason `HOST-13 agreed`)
- `PLANT g18-root-for GREEN (control)` (reason `ROOT for HOST`)
- `PLANT g18-default GREEN (control)` (scripts/plant's own line: `CROSS-LAYER: plant: CLIENT CODEC GATES HOST HOSTING KERNEL LANG LEDGER OPS PERF PROTOCOL ROOT TRANSPORT`)
- Old judge: c18e028 passed it; the new rule refuses c18e028 (replay).
**Critique.** A name in a reason is not an agreement. The gate makes the bypass legible; it does not prevent it. A reason that names every layer (as the plant's does) passes everything, and only a reader catches that. gates/codec-vectors.tsv being GATES-owned makes every codec re-emit name GATES. That is right while GATES-13's immutability check is GATES', but it is the most frequent refusal in the replay. If it turns into noise, the fix is an OWNERS row for that file, argued separately.

## GATES-19 · The landing queue: behind-main is a judged merge, readiness order with an age bound, verdicts carried only under a byte-identical input key (2026-10-19/20, ROOT rulings; design docs/record/GATES-19-DESIGN.md)

**Why.** Measured over 36 h of commit logs (GATES-6): 216 landings took 306 full judges. 90 GREEN judges lost the compare-and-swap and were thrown away; attempts per landing 153/45/10/7/1 and one gave up; 19 runs were refused `worktree behind main on F` and re-applied by hand (runs.tsv, waste.tsv, the lakefile, decisions/*.md, mostly different lines). HOST-52 took six runs: seven GREEN judges thrown away and five hand re-applies, none caused by a commit touching its modules. CLIENT-8 (ecb02bf, CLIENT-29) while this was built: 10 GREEN judges across its commit3-6 runs, 9 thrown away to the CAS, behind-main refusals in three runs (runs.tsv, lib.rs, Cargo.toml re-applied by hand).

**Decision.** Four pieces; the first is ROOT's addition (LANG-18's finding).
0. **A data path selects every row, standing rows included** (runs.py `data_paths`/`selected`). A verdict row was selected only by the import closure of changed .lean modules (or the lakefile, toolchain, runs.tsv, a C source). A re-emitted world/ package text (world/resident/Bell, installed by cargo:launcher:resident_bell and the rows) selected no row: a `lang!` that broke it landed GREEN and standing went RED afterwards, a silent landing of a known red. Now any changed path that is not a .lean source, not under gates/doc-allow.tsv and not SIZE.md selects every row, printed `selection: every row (N changed path(s) a run may read: …)`. No row declares what it reads (a `reads` column would be unchecked prose; ROOT agreed), so this is the fail-closed set. **Cost, stated:** 96 of the last 150 landings touch such a path (deploy/ 92, launcher/ 70, gates/ 69, client/ 63, scripts/ 15, world/ 11), so most judges now run the full row set until traced read-sets narrow it. ROOT: a slow judge beats one that lands a known red. Standing-only is a COST choice, never a correctness one (ROOT, LANG-18 / PERF-9: bench-worstcut installs world/resident/Bell.ob): a `standing:` row whose inputs this commit changed (a data path, or a module of its exe's closure) runs in pre-push like any selected row, control included, `run standing:X: selected in pre-push (its inputs changed: …; a standing-only row costs minutes)`; an unchanged one prints `NOT RUN(standing-only; its inputs are unchanged)`. This amends GATES-17's "never runs it, whatever changed".
1. **Behind main is a 3-way merge whose result is judged** (gates/rebase.py merge, called by scripts/commit where the refusal was). For each named file whose copy at the worktree's HEAD differs from main's: base = the copy the lander edited (HEAD's; on a re-based attempt, the main copy the previous merge took, from the lander's own merged.tsv), ours = the worktree file, theirs = main's. All files merge cleanly or nothing is written: a conflict is refused by name with its hunks (`REFUSED — merge conflict in F`), never resolved by the tool. A file deleted or added on one side, or one git cannot merge, is refused. The clean result is written into the worktree file, because the candidate is built from the worktree and a worktree left on the pre-merge copy would revert main's change at the lander's next commit (051a8cc). The candidate is then judged whole, as any other.
2. **Readiness order with an age bound** (gates/land.py; ROOT ruling 2). Every lander's outer scripts/commit holds a ticket `<common>/nanodregg-queue/<seq>.<pid>` flock'd for its life (fd 6, closed in each attempt so no judge's child keeps a dead lander's ticket alive); the file holds how often it was displaced. A green lander whose base is still main lands at once: a lander still being judged blocks nobody. The check and the CAS run under one flock, so two ready landers are serialized and the second finds main moved: displaced, exit 75, re-based. A lander displaced twice is head regardless: until it lands or dies, every lander with fewer displacements (or a younger ticket) waits, printing `queue: waiting for <ticket> (displaced 2)`. A dead lander's flock is released by the kernel, so a dead head is skipped with no stale-ticket logic. The CAS stays the proof (`update-ref main NEW BASE`). An outer loop older than this commit holds no ticket; its attempt takes one at landing time, starting at zero (it can be made to wait, never to land out of turn).
3. **A verdict is carried only under a byte-identical input key** (gates/rebase.py keys/verify, runs.py --keys/--reuse/--record, pre-push --record/--reuse/--verify). The lander's directory keeps the previous attempt's record (`unit<TAB>key<TAB>run|reused<TAB>payload`, ok units only: a red, INCOMPLETE, UNREAD, KILLED or ABSENT verdict is never carried). On the re-based attempt the JUDGE's rebase.py (main's copy, never the candidate's) computes every unit's key after the build; a run row (control and runs), the census and each cargo step whose key equals the recorded one is carried, `reuse U: reused (key …)`, anything else runs, `reuse U: re-run (key changed)`. check.py, SIZE, the build and the generated checks always run. Before the verdict, while the slot still holds the candidate's binaries, `rebase.py verify` re-computes every key of the record on the candidate and refuses `stale verdict: UNIT` when one differs or when a unit claimed as reused has no ok verdict under that exact key in the previous record. The keys: a run row covers its row text, every path that is neither a .lean source nor under gates/doc-allow.tsv (decisions/) nor derived (SIZE.md), the bytes of EVERY executable in the built bin directory, and the Python and rustc versions; the census covers every path outside the doc list; a cargo step every non-.lean path and rustc. `rebase.py check` (check.py gate `rebase`) refuses any file outside the doc list naming a path under it in a string literal.

**Why every binary.** The design keyed a run on its own exe's binary. That is a false reuse: the rows exe runs `lake exe NAME` for every exe row of its table (Protocol/Rows/Run.lean), and store-plants drives {host}. A key narrower than what a run executes carries a verdict whose inputs changed. Every binary is the sound static set; the traced read-set (design §7: strace execve/openat) is how a run gets a narrower one, and it is not built here.

**Replay, re-measured for the key as built** (hbox logs/gates7-reuse.py, the same 150 first-parent pairs as gates6-reuse2.py). Static reuse is **10.4%**, not the design's 42.9%: 20 of 150 re-bases re-run nothing; 94 re-run everything because D touched a non-.lean path every run's key holds (deploy/ 91 paths, gates/ 67, launcher/ 63, client/ 63, scripts/ 15, world/ 11), 36 because a .lean module inside some exe's closure changed (counted as changing the binaries; a proof-only edit usually leaves the bytes alone, so the real figure is at least this). With SIZE.md in the keys it was 5.4%. The 42.9% assumed per-exe closures (unsound, above) and only world/ and deploy/ as run-time data. So the key-reuse half saves little until traced read-sets land; the merge and the bound carry the win, as the design said they would. Predicted against the 36 h: full judges 306 → 216 + re-bases (each re-base is a judge whose runs are ~90% re-run under the static key, but whose build is incremental and whose CAS it can no longer lose to a younger lander more than twice); no landing above 3 passes unless two landers reach two displacements together (then the younger takes a fourth); the 19 hand re-applies become judged merges.

**Not weaker.** Nothing that was refused passes. The merge replaces a refusal by a judged result and refuses every case it cannot make cleanly. The queue only delays. A carried verdict is re-keyed on the candidate before the verdict by code the candidate cannot change. The fail-closed rules of GATES-15/16/17/18 are untouched and re-planted below.

**Plants** (hbox logs/gates7-keys2.sh/.out for the second pass, logs/gates7-merge.sh/.out, gates7-queue.sh/.out, gates7-keys.sh/.out):
- selection (LANG-18): one byte of world/resident/Bell, no .lean. Old runner: `PLANT g19-select-old GREEN`, and no resident_bell run line at all (the known red lands). New: `PLANT g19-select RED: runs: NEW RED run cargo:launcher:resident_bell` (`FAIL the_resident_answers_every_ring_lowest_first_once_and_nothing_else`), with lang-journey LB0 and rows red beside it.
- standing-only rule (ROOT via LANG-18/PERF-9): the selection on main's tree with changed = exactly `world/resident/Bell.ob` gives `standing:bench-worstcut: changed path world/resident/Bell.ob` (and bench-worstworld); `Ledger/Sim/Journey.lean` gives no standing row (outside both closures). Through pre-push, Bell.ob plus one appended byte: `run standing:bench-worstcut: selected in pre-push (its inputs changed: …)`, the bench and its control run, `PLANT g19-standing-input GREEN (control)`.
- 4 doc-only: B0 = main + one line of decisions/gates.md, M = one comment line of Ledger/Sim/Journey.lean (line count equal). `plant: g19-doc: C0 on e5704bed01ad GREEN (24 units recorded)`, then on main `PLANT g19-doc GREEN (control)` with `census: ok (reused: key 5e55b39b…)` and every row `reuse …: reused (key …, byte-identical to the previous judge's)`.
- 3 data path: B0 = main + world/plant-g19.txt (nothing reads it). `PLANT g19-data GREEN (control)` with every row `reuse …: re-run (key changed)`.
- 2 forged reuse: C1's record with run:ledger-sim given C0's key and marked reused: `PLANT g19-forge RED: stale verdict: run:ledger-sim (recorded key 3d81c294aa58bd65, the candidate's key now 6bdd09b2e3af69c2)`. Control, the same record unforged, on the plant's own candidate: `PRE-PUSH VERIFY ok tree b0c3c46cef45: verify: ok (24 units, every key re-computed on the candidate)`. (Verifying it against another tree read `stale verdict: census …` on every unit: a record does not verify against a tree it was not judged on.)
- 1 semantic conflict with no textual overlap: B0 = main with ledger-sim's final line `ALL PASS (b0)`, P = runs.tsv expecting it. `plant: g19-semantic: C0 on a570808d2e54 GREEN (23 units recorded)`, then on main `reuse ledger-sim: re-run (key changed)` and `PLANT g19-semantic RED: runs: NEW RED run ledger-sim 1`.
- 7 doc allow-list: `PLANT g19-allow RED: rebase: scripts/plant-g19.txt:1: names "decisions/gates.md", under the doc allow-list decisions/ that no input key covers`.
- merge: a scratch worktree at 35daeab (main then added runs.tsv rows), judged by the unlanded attempt with a conflict-marker file beside it so it cannot land. Old judge: `REFUSED — worktree behind main on gates/runs.tsv`. Clean: `merged main's change to gates/runs.tsv into your copy (3-way, base = this worktree's HEAD); the merged file is judged`, and the worktree copy holds the kernel-sim edit and main's host-sock-probe and cargo:launcher:sock rows. Same-spot insert: `REFUSED — merge conflict in gates/runs.tsv (1 hunk(s) …)` with the hunk printed and the worktree md5 unchanged. Deleted vs changed: `REFUSED — cannot merge gates/runs.tsv: deleted in your worktree …`.
- queue (land.py on a scratch ref, tickets from gate-lib.sh new_ticket): a lander still judging blocks no ready one (`queue: head (displaced 0 times)`); a twice-displaced live ticket makes a ready younger lander print `queue: waiting for 00000003.2204417 (displaced 2): displaced 2 times, it is head regardless (GATES-19)`, the ref does not move until the old one lands, and the younger is then displaced (75, count 1); a dead head (holder stopped by its PID) is skipped and the waiter lands; the age bound: displaced on passes 1 and 2, then `A pass 3 exit=0` while a younger ready D waits and is displaced after; a stale base is still refused by the CAS.
- fail-closed, re-planted under the new runner: `PLANT g19-inert-control RED: run ledger-sim 1 --harness-control (control): RED(harness: the known-red control passed: ok)` (GATES-15); `ND_RUN_DEADLINE=1`: `PLANT g19-timeout NOT JUDGED` with `UNREAD(timeout twice: past 1 s …)` lines (GATES-16); `PLANT g19-owner-unnamed RED: owners: GATES commit touches Host/Store.lean, owned by HOST, and no CROSS-LAYER line names HOST` (GATES-18). KERNEL-54's attempt 1 refused by owners on LEDGER's files is GATES-18 working in the wild.

**What the old judge says about this commit:** main's scripts/commit and pre-push judge it (a judge change lands under the old judge). **What the new judge would have said about it:** the same build and runs; had main moved under it, its scripts/commit, gates/*.py and scripts/* paths would have merged (no overlap with any landing in the window) and re-judged with every run re-run (gates/ and scripts/ are in every run key), and it would have landed on its second pass.

**Critique.** (a) The static key re-runs ~90% of runs on a re-base: the over-approximation (every non-.lean path, every binary) is sound and nearly useless for reuse; its value today is the record and the re-check, ready for traced keys. (b) The merge edits a lander's worktree without asking; a lane that reads its file afterwards sees main's lines in it. That is ROOT's ruling and the message names each merged file. (c) The age bound makes every ready lander wait behind a twice-displaced one still judging, up to a full judge (a KERNEL re-genesis judge is long). (d) Displacements are counted whoever moved main, older landers included: the bound bites sooner than the ruling's "loses the head to a later one". Counting only younger winners would need land.py to record who landed, and only delays the bound. (e) `rebase.py check` reads string literals; a run that walks the tree from its cwd (runs start in the tree) would read decisions/ without naming it. No exe does so today; traced read-sets would see it.
**Meta-critique.** The design's headline number (42.9% reuse) was a replay of a key that was never sound, and I nearly built to it. The replay that matters is of the key as built; it says the reuse half of this commit is groundwork, and that traced read-sets are the next GATES item, not an optional one.

**Measured first day (GATES-8, 2026-10-19, every scripts/commit log on hbox under the new queue).** 13 landers logged `queue: head (displaced N)`: N=0: 5, N=1: 1, N=2: 6, N=3: 1 (HOST-61, bd39f78). Reaching the bound is the common case (6 of 13). Every pass beyond 3 was a TIE, which the age bound allows: two landers twice-displaced at once (tickets 21, 22 at c7f455e), then four (28, 33, 35, 36 at bd39f78 → 224e9fe; OPS-18 oldest). k tied landers landing serially onto each other's tips cost the youngest k−1 more re-bases by construction (each is judged on the tip it lands onto), so no ordering rule bounds that below 2 + k; ROOT withdrew a 4-pass rule on this. What shortens a tie re-base is reuse (GATES-20); a merge-train is GATES-21, PROPOSED (docs/record/GATES-21-PROPOSED.md), built only if the measured tail stays long under GATES-20. Admission control (refusing entry while ties stand) is refused: it shortens nothing a lander can see and starves the newest.

## GATES-20a · A run is selected by every binary it runs, not only its own: spawning rows, declared drives, and names in the static key (2026-10-20, ROOT ruling; found by GATES-8's traced read-sets)

**Finding (fail-open in pre-push, measured).** Every runs.tsv row was traced under `strace -f --seccomp-bpf -e trace=%file,execve` on the standing tree at 1a6163b (hbox logs/gates8-trace.py, traces in logs/gates8-traces; the traced run read `runs: ok (57 runs of 43 exes)`, as untraced). Each trace's execve set was then compared with what selection assumes (logs/gates8-replay.py, gates8-extra2.py, gates8-drives.py, over main's last 150 first-parent landings and the real `runs.selected`):
- `store-plants` runs `{host}` (Ops.Plants), `rows` runs `lake exe lang-journey` (Protocol.Rows.Run), and each was selected by its OWN exe's closure only. **Ten landings carried a pre-push GREEN without the run**: five changed a module only host links (3f6d8833, 4e81a85a, 7932cb39, 0a808e4f, 45102b29: Protocol.Command.Machine, Lang.Print, Host.Cli, Protocol.Command.Describe) and did not run store-plants; five changed Lang/Journey.lean (519ac30f, 119d2dc9, e40d520f, 7869bbc4, 921d2d03) and did not run rows. **Standing was the backstop**: it runs every row, so a red there would have surfaced only after landing.
- `cargo:launcher:resident` and `cargo:launcher:resident_bell` run hosting-residents (since HOSTING-35, 9d5b293) through launcher/tests/common, and their drives column did not name it, so a change only it links selected neither. No landing hit it yet.
- GATES-19's critique (e) said no exe walks the tree; `cargo:devtools:workspace` does: it stats every entry under the root, decisions/ included (`crates()`), so a `decisions/x/Cargo.toml` changes its verdict while GATES-19's static key held no decisions/ path at all.

**The rule.**
- `runs.reach(exe)`: a Lean row is selected by its closure, and when that closure holds a module that spawns a process (`IO.Process` / `Process.spawn|output|run` in the blanked code: today Ops.Plants and Protocol.Rows.Run, so rows, store-plants and live-calls) by EVERY exe's closure: what it spawns is data. Standing selection reads the same reach. Derived, not declared: matches the traced execve sets exactly.
- `runs.py check` is RED when a cargo row's sources (tests/TEST.rs, tests/common/ when it says `mod common`, src/) resolve a lean_exe through `devtools::lean_bin("NAME")` / `lean_bin_in(DIR, "NAME")` that its drives column omits; and RED when a Rust file outside devtools/src reaches the bin directory itself (`"ND_LEAN_BIN"` or `".lake/build/bin` literals), the second door no scan would see. The drives column now means "may run": tests/common's helpers make every launcher row that says `mod common` declare host, hosting-broker and hosting-residents (an over-approximation: it costs selections, never a missed run).
- rebase.py's static key covers the NAMES and modes (not the blobs) of DOC_ALLOW and .lean paths: an add or a remove re-keys, a prose edit still reuses. KEY_VERSION v2, so no v1 record verifies.
- gate_slot: with every slot busy, it retries all of them each 5 s (deadline 30 min unchanged) and takes the first that frees, where it waited on slot (pid mod N) alone.

**Plants** (hbox logs/gates8-selplant.py over a `git archive` of main, logs/gates8-plant-tree; logs/gates8-slotplant.sh). Main's gates: `select-store-plants (Host/Cli.lean) GREEN (missed)`, `select-rows (Lang/Journey.lean) GREEN (missed)`, `select-resident-rows (Hosting/ResidentsCli.lean) GREEN (missed)`, `check-undeclared-drive GREEN (missed)`, `check-second-door GREEN (missed)`, `key-doc-add-rekeys GREEN (missed)`. This commit's gates with its runs.tsv: all six `RED (caught)`. Control: `key-doc-edit-reuses: ok` under both (a decisions/ blob edit leaves the key). Main's runs.py with the new runs.tsv catches only the resident rows (the drives fix alone), so both halves are needed. Slot: three slots held, one other than the waiter's pid-mod slot released: main's lib `did NOT take the freed slot 3` after 15 s; this one `gate: slot 2 freed; judging in it`.

**Not weaker.** Selection only grows; the check only adds refusals; the key only gains inputs (a v1 record re-runs).

**Critique.** (a) Spawning rows select on every exe's closure: rows and store-plants run on nearly every Lean landing. They are seconds, and the traced read-set (GATES-20) is what narrows them to what they actually run. (b) The lean_bin scan reads string literals; an exe name built at run time (`format!`) escapes it, and only a trace sees that: the standing trace should be a check, not a measurement (GATES-20). (c) The tests/common over-approximation names drives a test never runs.
**Meta-critique.** GATES-19 keyed reuse on "every binary" precisely because a run may drive any other, and never asked the same question of selection: the key and the selection answered "what can move this run" differently, and only the key was right. The invariant now stated: a row is selected whenever a binary it may run can change.

## GATES-20b · The landed copy: every path is merged from what the lander recorded, never taken from the working tree; a landing that would revert a recent commit is refused `stale path` unless named; a head lander is never charged for a tie (2026-10-21, ROOT rulings; HOSTING-13's hazard, LANG-21's finding)

**Why.** HOSTING-13 caught by hand, mid-judge, that a re-based attempt re-read `launcher/tests/members.rs` from the working tree while CLIENT-31 (cdc0e9a) had added 70 lines to it on main. Verified at source (hbox logs/gates9-verify.sh; a scratch worktree, main's own judge with a stub pre-push that prints the candidate and refuses, so nothing could land): GATES-19's merge ran only for a path whose copy at the worktree's HEAD differed from main's, with HEAD's copy as the base, and the candidate was then `git add -A` of the working copy. HEAD stands in for "the copy the lander edited", and nothing checks that. **V1**: a copy made from a1ca640 plus one lane line, written into a worktree at main (a scratch copy copied in, the scp workflow several lanes use): candidate `members.rs | 81 +++----`, 1003 lines, CLIENT-31's lines gone and the lane line in. **V2**: worktree at a1ca640, lane line added, then `git reset main` (HEAD moved, the file left): the same 1003-line candidate. **V0** (control): HEAD left at a1ca640: merged, 1077 lines. A green judge lands V1 and V2. HOSTING-39 itself (ea52a4a) was safe: its HEAD stayed at a1ca640, so its attempt 5 merged. How GATES-19 missed it: its plants put the lane's HEAD at the lane's real base each time, the one case where HEAD is right. The rewrite case was also open: the working file was re-read on every attempt, so a file rewritten between attempts (P4 below) landed whole.

**Decision.**
1. **The landed copy comes from a record, never from the working tree** (gates/rebase.py `snapshot`/`candidate`). The lander's first attempt records, per file under its PATH..., BASE = the blob at the worktree's HEAD then and OURS = the working copy then (written to the object store), in `<lander dir>/snapshot.tsv`. Every attempt builds its candidate from that record against main's blob M: OURS = M nothing; OURS = BASE (not edited) main's copy; BASE = M (main did not change it) OURS; otherwise `git merge-file OURS BASE M`, a conflict refused by name with its hunks, an absent side refused. The working tree is not read again during the landing. After the compare-and-swap `writeback` writes the landed copy into each working file that still holds OURS. A file edited while the lander ran keeps that edit, merged 3-way onto the landed copy (base = OURS), as an uncommitted edit, or is named when it does not merge. GATES-19's merged.tsv is deleted, because the record makes it unnecessary.
2. **`stale path: P`** (gates/rebase.py `stale`; ROOT: on the FINAL candidate, after the merge, so a merge that loses a hunk is also caught). No recorded base helps when the base itself is wrong (V1, V2: HEAD == main). So for every path the candidate changes, and every commit C of main's last 300 first-parent commits that changed it: C's change is LACKING in a copy X when `git merge-file X pre_C post_C` is clean and changes X, and CONTAINED when it is clean and leaves X as it is (a conflict is neither: a later edit of C's lines is not a revert). A candidate copy that lacks C while main's copy contains it would revert C. It is refused, with the hunk, unless the lander names it `--reverts C`. A named revert of another layer's commit needs that layer named in a CROSS-LAYER line (ROOT: reverting another layer's change is cross-layer by definition). Its hunk is appended to the message under `REVERTS: C in P (subject)`, so the revert is findable six weeks out. A `--reverts C` that the candidate does not revert is refused. Every refusal prints the exact addition, so the cost is one copy: `add: --reverts ea52a4ab4046 and name HOSTING in --cross-layer (e.g. "HOSTING-N agreed: …", or "ROOT for HOSTING")`. **Why 300** (ROOT): measured 2026-10-21, the oldest live worktree base (wt/transport) sat 297 commits behind main, two days.
3. **The retry budget counts only non-head losses** (gates/land.py `--charge`; LANG-21's finding). The outer scripts/commit gave up after COMMIT_RETRIES (5) exits 75 whatever caused them. LANG-21's c1166ce (logs/lang21-commit2.log) was displaced 0→1, 1→2 while not head, then three times more while head, losing ties to older heads (blockers() lets nothing else land), and gave up. Now, after each exit 75, land.py says whether it is charged: a displacement while not head is; one while head (a tie) is not, nor a deadline wait (count unchanged). A head lander waits for the tie winners and never fails for them. A refused CAS now counts as a displacement too.

**What breaks.** `scripts/commit --reverts C` is new. A lane deliberately deleting a block a commit of main's last 300 added must now name that commit: measured over main's last 150 landings (hbox logs/gates9-stale-replay.py/.out, each landing as the candidate on its parent), **14 of 150 (9.3%)** would have been refused first: c0cd535, 5fff199, 16f3b9f, cfdb08d, e1e8084, da0593e, eaa591a, a130087, 42c261b (two paths), 6558c56, 38d94e1 (two paths), 5eb9b30. Each is a deliberate deletion (theorems, defs, RUNBOOK paragraphs, a C export, a Cargo dev-dependency; logs/gates9-hunks.out), none a silent revert. Seven reverted another layer's commit and would have had to name it. ROOT: land as built, no narrowing. A deletion of a block an earlier commit added carries that commit's hash and its owner ("say what you broke" at the gate), and the seven foreign ones should have been cross-layer anyway. Content cannot tell a deletion from a stale copy (CLIENT-31's +70 lines was a pure insertion), so this cost is the price of catching V1/V2. Nothing re-emits; no format changes. A lander already running keeps its own outer loop. Its attempts run main's new copy, which records at the first attempt it runs.

**Plants** (hbox logs/gates9-plants.sh with a stub pre-push, so no judge slot is taken and nothing lands; -old.out under main's judge, -new.out under this one; P = launcher/tests/members.rs; a1ca640 = before CLIENT-31):
- P1 V1 (a1ca640's copy + a lane line, HEAD == main). Old judge: candidate 1003 lines, CLIENT-31's lines gone. New judge: `stale path: launcher/tests/members.rs: the landing would revert ea52a4ab4046's change to it (hosting: …)` and the same for `cdc0e9a978f3`, each with its hunk.
- P2 V2 (`git reset main` under an edited file): old 1003 lines; new the same two `stale path` refusals.
- P3 (HEAD at the lane's real base): both judges `merged main's change … ; the merged file is judged`, 1077 lines = main + the lane hunk.
- P4 (the lander recorded at a1ca640; then the working file is overwritten with a1ca640's copy and HEAD reset to main; its next attempt). Old judge: lands 1002 lines, losing main's change AND the lane hunk. New judge: 1077 lines, from the record.
- P5 conflict (worktree at cdc0e9a, the line ea52a4a replaced, edited differently): `REFUSED — merge conflict in launcher/tests/members.rs (1 hunk(s); base = your recorded base b34d44e4692b)`.
- P6 clean (worktree at main, a lane line): unchanged, 1077 lines.
- P7 a deliberate revert of ea52a4a's hunk, unnamed: old judge lands it; new `stale path: …`. With `--reverts ea52a4a`: `--reverts ea52a4ab4046: ea52a4ab4046 is HOSTING's (…); reverting another layer's change is cross-layer: name HOSTING in a CROSS-LAYER line`. With `--cross-layer "plant: HOSTING-13 agreed"`: passes to pre-push, and the message carries `REVERTS: ea52a4ab4046 in launcher/tests/members.rs (…)` plus the hunk. P8: `--reverts cdc0e9a` on a candidate that reverts nothing: `the candidate reverts no change of cdc0e9a … drop the flag`.
- writeback (logs/gates9-wb.sh): the landed copy written (`equals landed: yes`). An edit made meanwhile: `changed in your worktree while this lander ran … kept, merged onto the landed copy`.
- budget (logs/gates9-loop.sh: the REAL outer loop over a shared clone whose main holds a stub inner attempt replaying LANG-21's displacement sequence). Main's loop: `gave up after 5 attempts`. This one: `charged … (now 1)`, `(now 2)`, then three `not charged: displaced while head (… a tie)`, and attempt 6 lands, exit 0. COMMIT_RETRIES=2: `gave up after 2 displacements while not head`.

**What the old judge says about this commit:** main's scripts/commit and gates/rebase.py build its candidate (the HEAD-based merge) and main's pre-push judges it; its paths are GATES' own. **What the new judge would have said:** the same candidate. wt/gates was detached at main before launch (ROOT's mitigation), so its record equals main plus these four files, and `stale` finds no revert in them (rebase.py's old `merge` is deleted, the block GATES-19 added: that is 6527d9f's/1a6163b's hunk being replaced, which GATES names for itself).

**Critique.** (a) The window is a count. A copy made from a main older than 300 commits is not caught by `stale`, though its recorded base still merges it when HEAD is right. (b) `stale` is per commit and needs a CLEAN merge of C's change. A stale copy that also edited inside C's lines conflicts and is not seen. (c) 9.3% of landings pay one flag. That is the visible price of an invisible defect, and the escape writes the deletion into the message where it was silent before. (d) The record is taken at the first attempt that runs this code, so a lander launched before this lands records at its next attempt. (e) A head lander may now re-judge without bound while ties keep landing. Each re-judge is bounded by the heads alive, and a lander that dies releases its ticket.
**Meta-critique.** GATES-19 trusted HEAD as "the copy the lander edited" and its plants never moved HEAD. The defect lived in what the plants held fixed. This decision's own blind spot is the window; the measure that would expose it is the age of the oldest copy a lane copies in, which nothing records.

## GATES-20 · Traced read-sets select the runs and key the reuse; the judge's code is main's, the candidate supplies only its table (2026-10-20, landed 10-21 after GATES-20b; ROOT rulings F1/F2 and "the judge's CODE is main's"; design docs/record/GATES-20-DESIGN.md)

**The rule.**
- **Every judge traces every run (F1).** runs.py runs each verdict run under `strace -f -qq -y --seccomp-bpf -e trace=%file,execve,getdents64` (gates/readset.py). The trace is reduced to a read-set: T, the tree paths the run touched by name; L, the tree directories it listed; X, the binaries it exec'd from .lake/build/bin. T covers opens, execs, stats, accesses and readlinks, including absent probes (ENOENT is a read of absence). Excluded from the read-set: .lake/runs/, .lake/cargo-target/, and anything under a directory the run itself created. strace -y's fd annotations place a name relative to a directory fd or a chdir'd cwd where it was really opened.
- **A traced key** hashes the row line, the runner's bytes (runs.py, tree.py, readset.py), each T path's bytes, each L directory's sorted names, and each X binary's bytes, all read off the materialized tree. **A stat is keyed by content, like an open**: cargo's fingerprint compares mtime and size, so a stat is a proxy for the bytes. (The design's mode-only stat key was unsound and was not built.)
- **Selection.** A row is selected iff any of:
  1. its reach (GATES-20a) meets the changed .lean modules;
  2. it holds no read-set valid for the parent; or
  3. its valid read-set touched a changed path, or listed a directory where a path was added or deleted.

  A read-set is valid for the parent iff, between the tree it was traced on and the parent, no path it touched changed, no listed directory gained or lost a path, no .lean of its reach changed, no runner file changed, and its row line is the same. A script row is selected on every judge, as before, and so is a cargo row whose crate changed.
- **No valid read-set falls back to the static rules (fail-closed).** That covers no strace on the box (`trace: strace unavailable`), an unparsable or missing trace, and one untraced run in a row.
- **Reuse.** A lander's previous judge records each ok row under `t:<traced key>`, with the read-set in the payload. On the re-based candidate the read-set is re-keyed, and the verdict is carried only when the key is byte-identical. `rebase.py verify` re-keys every `t:` unit from its payload with the JUDGE's readset.py.
- **The judge's code is main's.** pre-push runs `$J/runs.py` and `$J/waste.py` (J = the judging scripts' tree: main's copy under scripts/commit). The candidate supplies only its runs.tsv and waste.tsv; a candidate's gates/*.py is never executed by its own judge. Consequence (ROOT): a new row KIND and the first rows that use it are two commits, runner first. Why: GATES-19 (1a6163b) and GATES-20a (6527d9f) both changed gates/runs.py and were judged by their own runner. Standing on each read GREEN (1a6163beb767, 6527d9f146e0), and that was the only check after the fact.
- **Standing's re-trace check.** Standing traces every row. Each stored read-set whose own key re-computes equal on the standing tree must contain the fresh one (fresh ⊆ stored: cargo with a warm cache reads less, never more). Anything more is RED `trace: the run touched P …`. That catches a forged or narrowed record, a nondeterministic run, and an input no key covers. The first version compared only records whose key equalled the FRESH read-set's key, which is vacuous: a differing read-set always has a differing key. It was rebuilt before landing.
- **Reads outside the tree (F2) are reported, not RED.** runs.py prints `outside EXE: home N, tmp M`, and standing's line carries `outside=N(traced|untraced)`. **GATES-20c** turns it RED. Trigger: the census below is sorted. Dated: 2026-10-27.

**Measured.**
- Replay of main's last 150 first-parent landings, with the read-sets as built (logs/gates8-replay3.py over two traced standings):
  - selected runs 3025 (static, GATES-20a) → **1922**;
  - re-base reuse **41.8%** (803 of 1922), against **10.4%** for the static key;
  - re-runs: **804 from the binary-closure floor** (a .lean of a run binary's reach, which no binary-byte key avoids), 130 touched paths, 91 runner, 46 script rows, 44 crate, 4 row lines.
- The design's figures (2994 → 1672 runs, 53.4% reuse, a 512-run floor) came from a mode-only stat key and own-closure reach. Both are corrected here: content-keyed stats, and 20a's reach, which makes the spawning rows reach every exe.
- Determinism (plant 8): two traced standing passes on the same tree. 24 of 25 rows came back with fresh ⊆ stored. host-file-sim read RED, touching `.lake/host-file-sim/run-<random>` (+675 more): its own scratch outside .lake/runs. That was fixed by the run-created-directory exclusion, then re-measured: two passes of host-file-sim alone gave one stored read-set and no re-trace red.
- Census of outside reads (store over two passes, by prefix):
  - ~/.cache/nd-t: 472 (test temp roots);
  - LD_LIBRARY_PATH and PATH probes into ~/src/hacl-star, ~/src/HOL, ~/r05, ~/.local/share/solana: 176 + 54, mostly ENOENT;
  - ~/.nd-bar/run.* and ~/ndbar.*: bar.sh scratch;
  - /tmp/nd-attach-*: tempdirs;
  - **real inputs no key covers**: ~/.gitconfig and ~/.config/git (git, inside tests), and ~/.lake/config.toml (lake).

  GATES-20c's first item is to sort those three: key them, or make the runs not read them, with HOME pointed at the run's fresh dir.
- strace cost, as a count rather than wall clock: every row stayed inside its 600 s deadline under tracing on hbox, in both standing passes and in every plant judge.

**Plants.**
- logs/gates8-g20plant.py, function-level, over real read-sets:
  - S1: .gitignore, read only by cargo:devtools:workspace, selects it (and the script row). Control: rows that never read it, holding valid read-sets, are not selected; the static rule selects every row for it.
  - S2: `.cargo`, probed absent by cargo:attach:attach, once added selects it.
  - S3: a file added to Bench/, which devtools lists, selects it.
  - S4: with no strace on PATH, `available()` is None, so every key and every selection is static.
  - S5: an unparsable or missing trace leaves no read-set.
  - S6: a parent that changed .gitignore since the trace invalidates devtools' read-set, so it falls back to static.
- logs/gates8-g20e2e.sh, through scripts/plant and this judge:
  - R1 `g20-evil-runner`: a candidate runs.py that prints `runs: ok` and exits 0, plus one byte of world/resident/Bell, reads `PLANT g20-evil-runner RED: runs: NEW RED run cargo:launcher:resident_bell`. Before this commit the candidate's runner was the one executed (pre-push judge_runs copied `$G/tree/gates/*.py`).
  - R2 `g20-data`: B0 = main plus world/plant-g20.txt (a file nothing reads), M = one comment line of Ledger/Sim/Journey.lean. Result: `PLANT g20-data GREEN (control)`, 24 units reused and 2 re-run. The re-runs were census and cargo:devtools:workspace, which lists world/ and saw the added path. GATES-19's static key re-ran every row (g19-data).
  - R3 `g20-forge`: the C1 record of cargo:devtools:workspace (re-run, key changed) is made to claim C0's traced key. Result: `PLANT g20-forge RED: stale verdict: run:cargo:devtools:workspace (recorded key t:355e479e97b07d, the candidate's key now t:1823186b82597d)`.
  - R2 and R3 were re-run with the final readset.py (logs/gates8-g20e2e-b.out), which adds the toolchain to the key.

**Not weaker.**
- Selection narrows only through a read-set validated against the parent, and every gap in it falls back to the static rules.
- Reuse is carried only under a byte-identical traced key, which the judge re-computes.
- The candidate no longer runs its own runner.
- The re-trace check is new red. The outside report is new information, and RED is dated as GATES-20c.

**Critique.**
- (a) The binary-closure floor (804 of 1119 re-runs) dominates. A finer key needs a deterministic per-module link map, which is not proposed.
- (b) Validity on the parent checks only the git-tracked part; .lake products are taken as functions of the .lean sources and the toolchain, covered by reach. The toolchain outside the tree is in the traced key as `rustc -Vv`, `cargo -V` and the Python version (found while writing this: the first traced key had none of them, so a rustc upgrade would have carried a cargo verdict); the Lean toolchain is lean-toolchain (a tree path lake touches) and the X binaries' bytes. Selection validity does not see a toolchain change at all; a toolchain upgrade is a box event, and standing's re-trace is the check.
- (c) A read-set stored by a judge of a candidate that never landed may later validate for a parent. That is sound by the validity argument, but the store grows without bound. Pruning is a follow-up and is not needed for correctness.
- (d) The outside census found three real inputs no key covers. Until GATES-20c, a change to ~/.gitconfig can move a verdict that a re-base then carries.

**Meta-critique.**
- The design's two soundness claims both failed when built: a mode-only stat, and a re-trace check keyed on the fresh read-set. Each would have been a quiet false reuse.
- They were found by building and running the check, not by reading the design. The determinism plant found a third defect, run-created scratch.
- The design's number (53.4%) was the flattering one. As built it is 41.8%.
- Built by GATES-8 on 6527d9f and saved uncommitted while GATES-20b (8c2c5fd) landed first (ROOT: the silent revert outranked it); re-applied --3way by GATES-9 onto main with no conflict. runs.py, pre-push and standing.sh are byte-identical to the planted copies (logs/gates9-saved-20/), and rebase.py differs only by GATES-20b, which does not touch keys or verify. So the plants above stand for the landed code. The outside-reads RED, called GATES-20b in ROOT's ruling, is renumbered GATES-20c because GATES-20b is the landed copy.

## GATES-20d · A compile's reads are C, compared only against a compile; an escaped name invalidates the trace; an implied directory is not an extra (2026-10-21, ROOT ruling; standing 145283a RED)

**Why.** The first standing after GATES-20 (145283aa3e71) read RED: `runs=RED(cargo:attach:attach (re-trace): RED(trace: the run touched attach/src (+14 more), which a stored read-set valid on this tree omits …))`, on 13 of the 14 cargo rows. Every row's own verdict was ok. Measured over the store (hbox logs/gates9-rs.py, gates9-rs2.py): the stored read-sets valid on that tree came from judges whose cargo cache was warm (attach: 76 touched paths), and standing compiled (91). Every extra on every cargo row was a directory or an ABSENT `X/mod.rs` probe, read only when rustc runs: rustc tries `X.rs` and `X/mod.rs` for each `mod X;`, and cargo resolves each dep-info path's ancestors after a compile (`readlink launcher/tests` = EINVAL). GATES-20 assumed that a warm cargo reads less and never more. That is true, but the check assumed the stored record was the larger one, and the judges' warm records are the smaller. So it read RED on every standing that compiled, which is red as steady state. GATES-8's determinism plant missed it because its second pass was the warm one.

**Decision.**
1. **C, a compile's reads** (readset.reduce). strace now also traces clone, clone3, fork and vfork. A pid that exec'd rustc, and every pid or thread cloned from such a pid, is a compile, and the tree paths it touches go into C instead of T. A path both touch stays in T: cargo's own fingerprint stats every dep-info source, so a warm run's sources are in T whatever the cache holds. **Keys and selection cover T ∪ C**: the traced key hashes each C path like a T path (VERSION v2, so every v1 record re-keys and re-runs once), and `touched_by` reads T ∪ C. Nothing narrows there.
2. **The re-trace check** (readset.subset_violation) compares T, L and X always. It compares C only when the stored record compiled too (C non-empty): whether cargo compiles is its cache's state, not the run's. A compile against a compile is still compared. ROOT: a correction, not a weakening. A forged record would have to hide in T, L or X, where cargo's stats and the runtime reads are, and those are compared strictly.
3. **An implied directory is not an extra.** A directory D that the fresh run touched by name is not reported when the record touched a path under D that is a FILE on this tree. That file's key pins its bytes, so it exists, so D is a directory, and a stat or readlink of D reads nothing more. A LISTING of D is never implied (names are information).
4. **An escaped name invalidates the whole trace** (ROOT). In 145283a's standing, members' fresh read-set held `O\222\17\333\5`. That is strace reading a string argument from tracee memory while a thread rewrote it. It was not reproduced in a standalone traced run (logs/gates9-tr-members.sh: 91 paths, none odd). Any name the reducer places or resolves against (the path argument, the directory-fd and cwd annotations; never an execve's argv) that strace printed with a backslash makes reduce return None. That row then has no read-set: the static rules apply (fail-closed), and runs.py prints `untraced EXE: no read-set (an escaped name: …); the static rules apply`. The name is never silently dropped. Standing counts those lines as `untraced=N` and reads INCOMPLETE when N > 0, because the re-trace check did not run on those rows.

**Plants** (hbox logs/gates9-20d.sh: cargo:launcher:members traced three times on the standing tree under the standing lock. COLD1 = members.rs touched so the test binary recompiles; WARM = nothing changed; COLD2 = `mod gates9_probe;` and an empty launcher/tests/gates9_probe.rs, a changed source. members.rs restored, cmp-verified. Verdicts: logs/gates9-20d-check.py/.out, logs/gates9-20d-forge.out):
- read-sets, new reducer: COLD1 T 93 C 2, WARM T 91 C 0, COLD2 T 94 C 3 (L 24 and X 2 in all three).
- warm record against a cold run: main's check `touched launcher/tests (+3 more)` (the standing RED reproduced); this one `ok`. Cold record against a warm run: `ok`.
- narrowed record: members.rs dropped from T gives `touched launcher/tests/members.rs`; a listing dropped gives `listed attach/benches`.
- two compiles with a changed source: `touched launcher/tests/gates9_probe.rs`. The same with T held equal, so that only C differs: `compiled from launcher/tests/gates9_probe/mod.rs`. The nondeterminism catch survives in C.
- key: key(WARM) ≠ key(COLD1), so C is keyed.
- forged record through rebase.traced_now (the verify path): the honest payload re-keys equal; with members.rs dropped from the payload and the recorded key kept, `stale verdict: run:cargo:launcher:members (recorded key t:1f20d3a64e1674d8, now t:45fff7452b9e69b5)`.
- escaped name: WARM's trace with one statx path replaced by `O\222\17\333\5`. Main's reducer keeps it as a tree path (`['O\\222\\17\\333\\5']`). This one returns None, `WHY = an escaped name: O\222\17\333\5`.

**Blind spot (ROOT: in the decision AND dated under GATES-20c).** A warm cargo, judge and standing alike, cannot see a file ADDED at a rustc `mod` probe path (`client/src/attempt/mod.rs` beside `attempt.rs`, or a new `X/mod.rs` for a `mod X;` that resolved to `X.rs`), because dep-info lists only the files the compile read. A warm read-set inherits that: its C is empty, so the probe paths are in no key. GATES-20 did not cause this; it inherits it from cargo's fingerprint.
**GATES-20c, item 2, dated 2026-10-27**: close it. The mitigations, priced:
- (a) a cold compile once per standing day. That is one full rebuild of the 101-package workspace in standing's target per day, with every cargo row then carrying a C.
- (b) probe the absent paths: selection reads the C of EVERY stored record of the row, not only the valid one, and selects a row when a path is added at one of its recorded probe paths. That costs no run, but it needs one cold record per row, which (a) or any judge that compiled provides.
(b) is the cheaper one and is sound only with (a) as its floor.

**Critique.** (a) Attribution by pid relies on clone lines. A compile reached by a path that strace's clone tracing misses (a process created before tracing) would put its reads in T. That is the safe side: more strict comparison, never less. (b) The implied-directory rule trusts the recorded file to be a file on the re-checked tree, which holds because the check runs only on records whose key re-computes equal there. (c) An escaped name now costs that row its read-set for one judge. If one row escapes on every trace, standing reads INCOMPLETE every day, and that is the signal to fix the row.
**Meta-critique.** Planted with two passes, both warm-after-cold, the check passed. Run in the wild against a warm record, it read red at once. The plant held the cache order fixed, the way GATES-19's plants held HEAD fixed: the same blind spot, a week apart.

## GATES-20e · A judge table is an input of every row it judges: a changed waste ceiling selects the row that measured it, standing-only included (2026-10-21, ROOT ruling; PERF-4's fail-open at 41e041f)

**Finding (fail-open under GATES-20, 145283a).** PERF-4's landing 41e041f re-pinned worstcut ceilings in gates/waste.tsv. Attempt 1, judged before GATES-20, ran standing:bench-worstcut and bench-worstworld GREEN against the new ceilings. Attempts 2–6 printed `NOT RUN (standing-only; its inputs are unchanged)`. The bench never READS gates/waste.tsv: the JUDGE compares the bench's `WASTE` lines against it. So no trace holds it, and the traced read-set made the ceiling invisible to selection. A ceiling edit landed without the row it changes being judged. This is the same class as the self-judge finding: a table the judge reads to form a verdict was outside what the verdict was keyed on.

**Decision.** Every read-set carries W, the waste rows (`op<TAB>metric`) its row MEASURED (the row's own `WASTE` lines, added by runs.py after the union).
- **Selection** (runs.traced_selected): when gates/waste.tsv changed, the changed rows are those whose ceiling or measured value differs, or that were added or removed (prose is not a judge input; readset.waste_changed). Then:
  - a row whose valid read-set's W meets them is selected: `its waste row worstcut reopen-trie-hashes-per-step changed (gates/waste.tsv, a judge input)`;
  - a row whose read-set has no W (a record from before this commit) is selected;
  - when a changed row is measured by no valid read-set, every row the static rule selects runs (`no read-set says which row measures it`).
  Standing-only rows are selected the same way, so a changed ceiling runs its bench in pre-push.
- **Key** (readset.key, VERSION v3): each W row's ceiling and measured value from the judged tree's gates/waste.tsv. A re-based verdict is carried only under the same ceilings.
- **The other judge tables.** gates/runs.tsv already enters as each row's own line (key and selection: `its row changed`). gates/ceilings.tsv is read by gates/size.py inside check.py, which runs on every judge. gates/generated.tsv's checks run on every judge. None of them names a row that a trace could hide.

**Plants** (hbox logs/gates9-20e.py/.out, function-level over runs.traced_selected on the standing tree at 145283a with its gates/waste.tsv edited and restored under the standing lock; main's judge = GATES-20, new = this commit's runs.py/readset.py; the store a copy with W set per case):
- worstcut reopen-trie-hashes-per-step ceiling 32.217 → 33.000, no other change. **Main:** `standing:bench-worstcut not selected` (PERF-4's fail-open reproduced). **New, records without W:** `SELECTED (… and its read-set does not say what it measures)`. **New, records with W:** `standing:bench-worstcut SELECTED (its waste row worstcut reopen-trie-hashes-per-step changed …)`; kernel-sim and host-sim, which do not measure it, not selected by it.
- prose-only edit of that row (control): new, bench-worstcut `not selected`.
- admit trie-hashes-per-turn ceiling changed while no record claims it (orphan): new selects every static row, `… no read-set says which row measures it`; main selects no bench.

**Critique.** (a) W is what a row PRINTED the last time it was traced. A row that measures a waste row only on some inputs claims it only in records from those inputs. The orphan rule is the floor: unclaimed means everything runs. (b) The first judge after this commit re-runs every row once (key v3; and records without W select on any waste change), which is a cost, not a hole. (c) The class: any input the JUDGE reads is invisible to a trace of the run. The judge's other tables are named above. A new table the judge reads needs the same entry, and nothing checks that mechanically.

## GATES-20f · A dead lander's scratch is reaped at a later lander's start, by liveness only (2026-10-21, ROOT ruling; PROTOCOL-21's 709572)

**Why.** Each outer scripts/commit removes only its own `nanodregg-commit-main/$$` (each attempt, and on EXIT) and its own `nanodregg-landers/<ticket>` (EXIT trap). A lander killed before its trap ran leaves both forever: no other lander touches another pid's directory. PROTOCOL-21's misfired lander (stopped by its PID file 2 s in; the re-exec ran orphaned and landed nothing) left `nanodregg-commit-main/709572` (6.2M). land.py already removes a dead ticket FILE after 10 min, but not the lander directory beside it.

**Decision.** `reap_dead` (scripts/commit), run once at each outer lander's start, after it holds its own ticket:
- a `nanodregg-commit-main/<pid>` is removed only when that pid exists neither for `kill -0` nor in /proc. A reused pid keeps its directory, which is the safe side, and a name is never matched.
- a `nanodregg-landers/<ticket>` is removed only when its queue ticket nobody holds flock'd (`flock -n` takes it), or when the ticket is gone. The lander's own ticket is held on fd 6, so its own directory is never reaped. The ticket file stays land.py's to remove.

**Plant** (hbox logs/gates9-reap.sh/.out; the REAL outer loop in a shared clone, so its `$common` is the clone's .git and never main's; a stub inner attempt). Planted: a dead pid's scratch and lander dir (an exited `sleep 0`), and a live pid's scratch and lander dir (a running `sleep 600`, its ticket held by `flock … sleep 60`). Main's loop: all four `KEPT`. This one: `reaped a dead lander's scratch …/nanodregg-commit-main/1332376 (pid 1332376 is gone)` and `reaped a dead lander's directory …/nanodregg-landers/00000901.1332376 (its ticket is not held)`; the live pair `KEPT`.

**Critique.** A dead lander's scratch survives until the next landing starts, which is a disk matter of minutes. A pid reused by an unrelated process keeps a dead lander's 6 MB until that process exits, and that is accepted. 709572 is reaped by the first landing after this one, under code, not by hand.

**GATES-20e fix (landed with GATES-20f).** 20e's selection read `wchg & set(rs["W"])` on every row whose valid read-set has no W key, including when gates/waste.tsv had NOT changed. Every record stored before 20e has no W, so runs.py crashed with `KeyError: 'W'` in traced_selected, and pre-push refused with no verdict line (`runs: NO VERDICT`/`RED`). That refused every landing after c8ebb06 whose change met a pre-20e record (KERNEL-23, PROTOCOL-21, this lane's own GATES-20f). It failed closed: nothing landed on it. The cause was that every 20e plant changed waste.tsv, the one case where the branch above guards the read. Fix: the W branch runs only when a waste row changed (`wchg and …`); a record without W is still taken by the "does not say what it measures" branch whenever one did. Plant (hbox logs/gates9-20e-fix.py/.out; a change to Kernel/Proofs/InvokeTree.lean only, over the real store): main (c8ebb06) `KeyError: 'W' (elif wchg & set(rs["W"]):)`; this one `ok, 2 rows selected`. The 20e plants (logs/gates9-20e.py) are unchanged by it.

## GATES-20b′ · A prior commit's change is contained when the copy holds it, whatever its context (2026-10-21, ROOT ruling; PERF-6's false positive)

**Why.** `stale` (GATES-20b) read a commit C's change as CONTAINED in a copy X only when `git merge-file X pre_C post_C` was clean and left X unchanged. 35daeab (PERF-8) added the bench-worstworld block to lakefile.lean, using the bench-worstcut lines as its context. PERF-12 deletes those lines and keeps the block unchanged. The merge re-anchors on the context that survives and inserts the block a SECOND time. X "changes", so lacks() read LACKING, and PERF-6's landing was refused `stale path: lakefile.lean: the landing would revert 35daeab's change` (hbox logs/perf6-commit1.log, reproduced by logs/perf6-lacks.py). Any deletion of a prior commit's context lines tripped it. That is a false refusal: the copy reverts nothing.

**Decision.** `lacks(X, pre, post)` is True only when the merge is clean, changes X, AND X does not hold the change. `holds`: for every non-equal opcode of a line diff pre → post (difflib, no autojunk), the block of lines C added appears in X contiguously and at line boundaries, and the block it removed does not. The merge test stays first: what it calls contained is still contained, and a conflict is still neither. Whole blocks are compared, so a removed block X still holds, or an added block it lacks, reads LACKING, which is the refusing side. A single-line added block X holds elsewhere by coincidence reads contained. That is accepted: the line C added is in the copy.

**Plants** (hbox logs/gates10-lacks-plant.sh/.out; scratch worktree wt/gates9-plant; judge = a copy of the scripts with a STUB pre-push, so no slot is taken and nothing lands):
- P9, PERF-12's exact shape: a worktree at main, with lakefile.lean set to PERF-12's copy (wt/perf). Main's judge (fc4022d): `stale path: lakefile.lean: the landing would revert 35daeab421fa`. This one: stale passes and reaches the stub.
- GATES-9's P1–P8 (logs/gates9-plants.sh) under this judge: P1 (V1) and P2 (V2) are still refused `stale path` naming both ea52a4a and cdc0e9a. P7 (an unnamed revert) is still refused. P7b/P7c/P8 read as before, and P3/P4/P6 merge and reach the stub as before.

**Breaks.** Nothing; no format change. It refuses less: only copies that hold every prior change.

## GATES-22 · The fast landing and the convergence: a landing is judged by what it reaches, the whole system every 3 h, a red names the commits it read (2026-10-21, Ember's ruling via ROOT)

**Why.** Ember, 10-21: "we don't need to focus on landings as much, as long as every now and then we make sure the whole system still builds and passes its tests, and do convergences at those points instead of EVERY LANDING." The numbers before (GATES-10, hbox logs/gates10-fluid-measure.out and the landing logs): **61 re-judges in 24 h for 57 landings**, each a full judge (every target, the census, every selected row, the waste, the generated files, the Rust workspace with clippy); a standing pass **41 min** (fc4022d); GATES-20b′'s own landing **~2.5 h through the queue**, displaced twice, and refused once by a **30-min slot starvation** that read `REFUSED by scripts/pre-push`; on 10-21 evening all four slots were held by full judges for **45 min straight** (ROOT), and this lane's own first two plant judges waited 30 min each and got no slot (the second already printing NOT JUDGED, item 6). GATES-20j itself (a 3-file `gates:` change): judged GREEN, displaced; GREEN, displaced; then REFUSED by the 30-min slot wait, ~2 h after launch, with nothing wrong in it. Of 60 landings in the 24 h to cdd9d84, 7 were flag days and 8 changed the judge's code (7 of them GATES' own); the other ~45 were judged in full for changes the next standing judged again anyway.

**Decision.**
1. **The fast landing (scripts/commit's default).** gates/fast.py `mode` decides on the real candidate, by main's copy: a flag-day subject (`kernel!:`) or a change of the judge's CODE (gates/*.py, scripts/) is judged in FULL, exactly as before; everything else is FAST: `scripts/pre-push --fast` =
   - the stale-path guard (GATES-20b/20b′, in scripts/commit, unchanged) and every source gate, the candidate's and the parent's (gates/check.py: owners, closure, refusals, size, paths, the runs table, tcb, vectors, the waste ratchet, targets);
   - `lake build` of only the targets the change REACHES (gates/fast.py `targets`): the lean_libs holding a changed module or one of its importers or an importer of a deleted module, and the lean_exes whose import closure holds one; a non-module build input (lakefile.lean, lean-toolchain, lake-manifest.json, a C source) builds every target; no module changed, nothing is built;
   - `cargo check --locked --all-targets` and `cargo fmt --check` of only the packages it reaches (gates/fast.py `crates`: a changed member and every member with a path dependency on it; the root manifest or lock: the workspace);
   - then the compare-and-swap. No ticket, no charge: main moved, the lander re-bases from its recorded copy and is judged again (FAST_RETRIES 12). It lets a FULL lander displaced twice land first, for at most 60 min (land.py `--fast`): a full judge is ~40 min and would otherwise never win against a landing every ~25 min.
   - The landed message carries `JUDGED: fast (GATES-22) — (built: …; cargo: …)`, which the convergence reads.
   gates/*.tsv changes are DATA (20h (b)): they land fast, judged by the source gates (the ceilings and waste ratchets, the runs table's classification) and, at the convergence, by every row they feed.
2. **What moved from every landing to the convergence. Nothing is deleted.** Per FAST landing, these no longer run; each runs at every convergence (scripts/standing.sh), and on every FULL landing as before:
   - the axiom census (gates/census.py);
   - every verdict row the change selected (sims, journeys, plants, cargo rows, script rows: THE BAR), with their known-red controls and traces, and the standing-only benches GATES-19 ran in pre-push when their inputs changed;
   - the measured waste ratios against their ceilings (the ratchet stays per landing);
   - the generated-file checks (gates/generated.tsv);
   - clippy -D warnings over the workspace, and cargo check / fmt of the packages the change does not reach;
   - the build of the targets the change does not reach;
   - GATES-19's keyed reuse and the PRE-EXISTING parent re-judge exist only in the full judge, where they still apply.
   standing.sh gains the one of these it lacked: `cargo=` (cargo check, clippy -D warnings, fmt over the whole workspace), and the generated files get their own stage, `generated=RED(out,…)`, split from `census=`.
3. **The convergence (scripts/converge).** standing.sh on main, in the converge worktree (wt/converge, reset to main on every run; nothing else edits it), one at a time box-wide (nanodregg-converge.flock), on the systemd user timer nanodregg-converge.timer (every 3 h at :17, `--scheduled`: skipped when main has not moved or one is running), or on demand (`scripts/converge`, ROOT or Ember). gates/converge.py `record` appends to <common>/nanodregg-standing/convergence.log:
   `CONVERGENCE <sha> range <green>..<sha> landings=N (fast F, full U) => GREEN|RED|INCOMPLETE reds=K fixed=J`, one `RED <unit> … attributed to <commit> <OWNER> "<subject>" (<why>)` per red unit, `FIXED <unit> after <h> h (red at N convergences)` (time-to-fix), and the revert decisions. The range is since the last GREEN standing. A unit is `gates`, `build`, `census`, `generated:<out>`, `cargo`, `run:<row>` (its re-trace included) or `waste:<op> <metric>`. ATTRIBUTION: for a row, the commits of the range a full judge of that commit alone would have selected it for (its row line, the runner, a module of its reach, its crate, a waste row it measured, or its newest stored read-set touched; no read-set: the static rule, which over-attributes); for the build, the commits that changed the import closure of a module named in an error; the others as gates/converge.py says. Each commit printed with its owner (its subject's layer). ROOT routes; the owner fixes forward.
4. **The revert rule.** A unit still red at the next convergence (a stage that did not run proves nothing and changes no count), whose commit is attributed both at its first sighting and now, and is the only one: scripts/converge lands its revert by name, a `gates:` landing through scripts/commit with `--reverts C` (GATES-20b: the REVERTS: hunk in the message) and C's owners in CROSS-LAYER. Several attributed: `REVERT-PENDING` names them and ROOT runs `scripts/converge --revert C`. A commit is reverted once; a revert that does not apply cleanly is `REVERT-FAILED`, for ROOT.
5. **20h (a), stat by kind (inside 22: attribution needs it).** readset.reduce: a tree path some process other than cargo or a compile only stat'ed, accessed or readlink'd goes to K, keyed by KIND (DIR, FILE, ABSENT, LINK target, OTHER), not bytes; only an add, delete or kind change reaches it (touched_by); a fresh K path must lie in the record's K∪T∪C, and a fresh T path the record only stat'ed is an extra. A CARGO process exec'd `cargo` (clones inherit) until it exec's anything else; its stats stay content-keyed (its fingerprint compares mtime and size). Key VERSION v4: the first standing after this commit seeds (no re-trace comparison). Without it devtools:workspace's 754-path walk and THE BAR's 1216 paths attribute every commit of a range.
6. **Who takes a slot, and a slot wait is not a verdict.** A slot (a warm .lake and cargo target) is taken by: the FULL judge (flag days, judge-code changes), and a FAST judge only when it has something to build or check (a reached Lean target or Rust package). A fast landing that reaches neither (docs, decisions, gates/*.tsv, world texts, deploy/) decides that before asking and is judged in a private directory with no slot. The convergence has its own directory (the standing lock), never a slot. A slot wait past 30 min (gate_slot returns 3) prints the HOLDERS (each slot's pid and command, `fuser` on its flock, and the tree it last judged) and `PRE-PUSH NOT JUDGED` (exit 76); scripts/commit says `NOT JUDGED` (until now it read `REFUSED by scripts/pre-push`: GATES-16's class, an absent verdict is neither a pass nor a refusal).
7. **The lanes' adds (ROOT 10-21, from every lane's measured answer).** (a) THE SOURCE GATES FIRST: every judge, fast or full, runs gates/check.py (the candidate's and the parent's: owners and CROSS-LAYER, SIZE lines, the waste and ceiling ratchets, closure, …) on a private copy BEFORE it asks for a slot; a red is refused in seconds with the lines to add (a lane waited 30 min for a slot to learn it had indented a line). (d) DOCS-ONLY: a change that reaches no Lean target and no Rust package (README.md, CHARTER.md, docs/, decisions/, gates/doc-allow.tsv and every gates/*.tsv, world texts, deploy/, generated docs) is the no-slot fast path: the source gates only, seconds. Before 22 CHARTER.md, README.md and gates/doc-allow.tsv selected every row as paths a run may read (a one-line doc-allow commit cost 70 min; a docs-only ops: commit 2–4 h); now no row runs for them per landing, and a row that reads them is judged at the convergence, where every row runs. (f) KEEP THE PLACE: a judge whose slots are all busy waits on, naming the holders every 30 min, and is NOT JUDGED (exit 76) only after 4 h (ND_SLOT_WAIT); a full lander keeps its ticket meanwhile (HOSTING-16 lost its place behind 9 landers). (c) THE DISJOINT RE-MERGE is what the fast path already is: a displaced fast lander is re-merged from its record and re-judged by the gates and its reached build, never by rows (seconds to minutes); a FULL lander keeps GATES-19's keyed reuse. (b) APPEND-ONLY MERGE (gates/rebase.py candidate, the directories in gates/append-only.tsv: a table, since the judge code names no doc-allow path itself): a decisions/*.md that both the lander and main only APPENDED to since the lander's base lands as main's copy with the lander's addition after it, never a conflict (KERNEL-26 was refused on decisions/protocol.md and trial-merged every main commit by hand); an edit above the end on either side is merged and refused as before (plant hbox logs/gates11-append-plant.out: both appended → `a b main mine`; an edit above → the conflict; main's rebase.py on the same append → the conflict). (e) one retry of a row's flake (printed FLAKE by row, counted by standing) loosens a check, so it is its own `gates:` commit with its own decision, right after this one.
8. **Not needed: GATES-21 (merge train) and 20i (batch integration).** Both existed to make a full judge per landing affordable; with no full judge per landing, nothing is left for them to batch. **20g (concurrent standing rows) is next**: the convergence is now the only full run, and its 41-min wall is the whole system's latency to a verdict.

**Plants.**
- Lander side (hbox logs/gates11-fast-plant.sh, `-new.out`; the REAL outer loop in a shared scratch clone, a stub pre-push recording its flags): F1 an ordinary landing: `judge: fast`, pre-push `--fast`, no ticket, `queue: fast; landed by compare-and-swap`, message `JUDGED: fast`. F2 displaced under its verdict: re-based, judged fast again, landed (1 of 12 charged). F3 `protocol!:` → `full a flag day`, ticket, full pre-push. F4 gates/plant_lander.py and F5 scripts/plant-lander → `full the judge's code changes`. F6 gates/plant-lander.tsv → fast. land.py `--fast` (logs/gates11-yield.out): a live twice-displaced ticket → waits, lands past it at its deadline; a dead one does not block; main moved → 75.
- Judge side (logs/gates11-fast-judge-plant.sh, `.out`; the REAL pre-push --fast of this commit on index candidates of main, nothing landed; run directly, not through scripts/commit, so SIZE.md is not regenerated and each candidate's `size` gate reads red on that, as expected): P0 README.md: `slot: none`, gates ok, `build: none`, `cargo: none`, `PRE-PUSH FAST GREEN` in **29 s** (21 s with the pre-lint) (its first run under the old slot rule waited 30 min and read NOT JUDGED, the box's four slots held by full judges). P1 a type error in the leaf module Codec/Proofs/Sha512.lean: `build targets (reached): Codec`, `build: RED` naming `Codec/Proofs/Sha512.lean:16:0` (refused at the build of the one library it reaches). P2 a syntax error in sandbox/src/lib.rs: `cargo packages (reached): nanodregg-attach nanodregg-client nanodregg-launcher nanodregg-sandbox` (sandbox and its path dependents), `cargo-check: RED`, `fmt: RED`, no Lean built. P3 the same leaf with a true theorem: `build targets (reached): Codec`, `build: ok`.
- Convergence side (logs/gates11-converge-plant.sh, `-new.out`; the REAL scripts/converge, converge.py and scripts/commit in a shared scratch clone over the REAL read-set store, standing.sh and pre-push stubbed: ledger-sim reads red iff world/escrow/Escrow.ob holds the plant line): C0 GREEN; fast landing L1 (`ledger:`, world/escrow/Escrow.ob: a path of ledger-sim's stored read-set, no module, nothing built) and decoy L2 land; C1 `RED run:ledger-sim … attributed to f41b606 LEDGER "ledger: plant L1 …" (changed path world/escrow/Escrow.ob (traced))`, L2 not named; decoy L3; C2 red at 2 → `REVERT f41b606…`, the revert lands fast with `CROSS-LAYER: LEDGER: …` and `REVERTS: f41b60670383 in world/escrow/Escrow.ob`; C3 `GREEN … FIXED run:ledger-sim after 0.0 h (red at 2 convergence(s))`.
- Pre-lint (logs/gates11-fast-judge-plant3.sh/.out, the same harness with SIZE.md regenerated as scripts/commit does): P4 a Lean change whose message lacks its SIZE lines: `PRE-PUSH RED … the source gates, before any slot (nothing was built)` in 18 s, printing the two `SIZE: …: <why>` lines to add.
- readset K (a synthetic trace over main's tree): a lean exe's statx/access → K, its open → T; cargo's stat → T; the test binary cargo spawned → K after its exec; `touched_by` on a content edit of a K path: None; on its delete: reached; a fresh K path outside the record: `stat'ed …`; a fresh T path the record had only in K: `touched …`.

**Critique.** (a) A fast landing that breaks a row it does not build lands, and main is red until the next convergence finds it (≤3 h plus ~45 min) and its owner fixes it, or until the convergence after that reverts it (≤~7 h): that latency is the price Ember chose, stated. Landings on a red main still land fast; the range grows and attribution narrows it. (b) Attribution is as good as the read-sets: an input no trace holds (outside reads, GATES-20c) attributes to nothing (`no commit of the range (ROOT)`); a row with no stored read-set falls to the static rule and over-attributes; the build names only modules its errors name. (c) K by kind: a non-cargo program that branches on a stat's size or mtime of a tree file is not keyed by it (ROOT's ruling for 20h (a)). (d) The revert is automatic only for exactly one commit attributed at both sightings; a red that two commits make together is ROOT's. (e) The fast build compiles lib targets whole and follows imports only: a file a module reads at elaboration time is not traced to its targets (the convergence's full build is). (f) A fast lander waits up to 60 min behind a twice-displaced full lander. (g) The first convergence after this commit seeds key v4 and runs every row; its re-trace check compares nothing that pass.

**GATES-22 fix (2026-10-21, KERNEL-28's crash).** The outer loop read `$ND_TICKET` before every attempt (`before=$(cat "$ND_TICKET" …)`, for land.py --charge). A FAST lander holds no ticket, so under `set -u` every fast attempt printed `ND_TICKET: unbound variable`. In KERNEL-28's landing, after a FAST GREEN displaced by e568634→b50da06, the lander's directory was gone and rebase.py's snapshot failed (`snapshot.tsv.tmp: No such file`): kernel28-commit1/2.log. The read is now `${ND_TICKET:-/dev/null}`. Plant (hbox logs/gates11-fastfix-plant.sh/.out, the real outer loop in a scratch clone, stub pre-push): main's loop prints `line 119: ND_TICKET: unbound variable` before every attempt of F1 and of the displaced F2; this one prints none, and F2 re-bases once and lands. The harness reproduces the unbound read, not the directory loss KERNEL-28 saw after it; that loss follows the same read and is gone with it. My GATES-22 plants printed the same line, and their summary grep did not look for it.

**GATES-22 (b) fix: the LANDER's copy decides an append (2026-10-21).** 22's rule needed both sides to be pure appends since the lander's base. b50da06 (ROOT) edited GATES-19/20 headings above the end of decisions/gates.md, so 20j, which had only appended, was refused with a conflict at its re-base (logs/gates11-commit20j-3.log). The rule now reads only the lander's copy: if it is its base plus a tail, the landed copy is main's as it is (whatever main changed, above the end or at it) followed by that tail. A lander that edited above the end is merged, and refused on overlap, as any file. Plant (hbox logs/gates11-append2-plant.out; scratch repo, main edits line 1 and appends, the lander appends): main's rebase.py `REFUSED — merge conflict`, this one `A b c main mine`; a lander edit above the end: still the conflict.

## GATES-20k · A failure of the tracer is not a verdict: UNREAD(tracer), re-run once, twice NOT JUDGED; a retry that passes is a counted flake (2026-10-21, ROOT ruling; GATES-10 verified at source)

**Why.** The GATES-20 tracer sometimes fails mid-run: `strace: ptrace(PTRACE_LISTEN, …): Input/output error`. The run then exits 1 and runs.py read RED. It refused KERNEL-26's `kernel!` (gate-2/4c04f20aa738.log) and another lander's broker row (gate-3/2b29a0426731.log). Those were false refusals, never false passes. Under GATES-22 the convergence would read the same failure as a red row and attribute it to commits that did nothing.

**Decision.** gates/runs.py run: a run under the tracer that did not read ok, and whose output holds a line starting `strace: ` (strace's own, never the tracee's), is `UNREAD(tracer: LINE)`. run_once_more re-runs it once, as it does a timeout (GATES-16). If it fails twice it is `UNREAD(tracer twice: …)` and runs.py exits 76: NOT JUDGED in pre-push, UNJUDGED in standing, never RED. If the re-run passes, runs.py prints `  flake ROW ARGS: the tracer failed once; the re-run read ok`, and standing's line gains `flakes=N`, so a tracer that keeps failing shows up as the box's problem. A run that fails without a strace line is judged as before.

**Plant** (hbox logs/gates11-tracer-plant.sh, `.out` main vs patched, `-new.out` this commit; a fake strace that prints strace's error and exits 1, once or always, over a one-line exe): main's runner reads `RED(exit 1, last line: strace: ptrace(PTRACE_LISTEN …))` both times. This one reads `once` → `flake x …`, `ok` (2 calls), and `always` → `UNREAD(tracer twice: …)` (2 calls).

**Critique.** A run whose real failure also makes strace print a line (the tracee dies under it) is re-run, and if it fails again it is NOT JUDGED, not RED: a false refusal is traded for a withheld verdict. The convergence's UNJUDGED stage then names it, and an untraced re-run settles it.

## GATES-20j · A skipped cargo test is never ok: INCOMPLETE in pre-push, RED in standing; `cargo-untraced:` rows run without the tracer (2026-10-21, ROOT ruling; HOSTING-15's fence, built and planted by GATES-10)

**Why.** HOSTING-15's two-uid fence checks (a test that `sudo`s to the deployed uids) skip themselves when the fence is absent (no nd-hosted uid, /run cleared by a reboot): the test prints `skipped: …` and returns, and libtest counts it PASSED. A box without the fence would read every such row `ok`: the fail-open shape (an absent verdict read as a pass). And such a test cannot run under the GATES-20 tracer at all: strace --seccomp-bpf sets no_new_privs, so sudo refuses (measured on hbox 10-21: `sudo -n -u nd true` exit 0 plain, exit 1 traced).

**Decision.** gates/runs.py:
- A cargo run (either kind) that prints a line starting `skipped: ` (stdout or stderr) is never ok, whatever its exit and libtest's summary. In pre-push it reads `INCOMPLETE(skipped: N, first: LINE)`: pending, named in the verdict line `(pending: …)`, and the landing proceeds (ROOT). In standing (`--standing`) it reads `RED(skipped: N, first: LINE)`: an environment that went missing is a standing red until restored (the test's skip line carries its restore command). Neither is recorded or carried; on a `nobin RED` control a skip is a control that did not read red.
- A row `cargo-untraced:CRATE:TEST` is a cargo row run WITHOUT the tracer. It holds no read-set, so it is selected by the static rules alone (its crate, its drives' closures, every non-.lean change) and carried only under GATES-19's static key (every non-.lean source, the built binaries, the toolchain).
Under GATES-22 a row runs at the convergence (standing: a skip is RED) and on a full landing (pending); a fast landing runs no row.

**Plants** (hbox logs/gates11-fence-plant.sh/.out, GATES-10's logs/gates10-fence-plant.sh plus a standing case; the standing tree under the standing lock, planted test files and a trimmed runs.tsv, restored): main's runner reads the planted skipping test `cargo:launcher:gplantskip : ok` (the fail-open); this runner `INCOMPLETE(skipped: 1, first: skipped: no nd-hosted uid …)`; the sudo test traced `RED(FAIL sudo_reaches_nd)`, as `cargo-untraced:` `ok`; with `--standing` the skip reads `RED(skipped: 1, …)`.

**Critique.** A test that skips without printing `skipped: ` still reads ok: the rule reads the convention, and the convention is HOSTING's to keep (its tests print it). An untraced row is selected and keyed only statically, so it runs more often than a traced one, which is the safe side.

## GATES-20g · Rows run concurrently on free judge slots, each in its own scratch; GATES-20l · the convergence carries what the delta cannot reach, for at most a day (2026-10-21, Ember's question via ROOT; GATES-11 measured, GATES-12 built)

**Why.** Ember asked why a convergence takes 46 minutes. GATES-11 measured convergence 1 (0b86cb067bec): the gates, the full build, the census, the generated files and cargo take about 3 minutes on a warm tree. The rows take about 43 minutes, because they run one after another in one directory. A docs-only delta paid all 46 minutes as well.

**Decision, 20g (gates/runs.py, gates/readset.py, scripts/gate-lib.sh, scripts/pre-push, scripts/standing.sh).**
- *Concurrency.* With `--slots-dir/--slots N` (pre-push's full judge, and standing), up to N rows run at once in the one tree. The caller's own place runs one row: a judge's gate slot, or standing's lock. Each further row BORROWS a free judge slot: the slot's flock is taken non-blocking for as long as that one row runs, then given back. A row's own runs stay in order. Its lines are printed in row order, whatever order the rows finished in, and each row is followed by `  time ROW: N s (own|borrowed slot K|alone)` from the runner's own clock. `  runs wall: N s` and a `  concurrency:` line close the stage. Longest rows go first, by their last wall in `<traces>/_walls.json`, which is a schedule hint and never a verdict.
- *How landers' slots compose.* There are N slots, and gate_slot still gives each judge one. A convergence holds no slot of its own; standing's lock is its own place. Under 20g a convergence borrows at most N-1 slots, one per running row. While gate_slot waits for a slot it keeps `<common>/nanodregg-slot-wait/<its pid>`. While any such file names a live process, nothing new is borrowed. So a lander that arrives waits at most for one borrowed row to end. The longest row is the worstcut-rows bench, at 436 s. Nothing is killed to make room. The box never runs more than N slots' worth of judging plus standing's one row, which was also the bound before.
- *Each row in its own scratch.* A traced run's reduce now also records what it WROTE. This record is never keyed, since a write is no input:
  - `WR`: the paths it wrote.
  - `O`: the outermost directories it made.
  - `RM`: the outermost paths it removed or renamed away.
  - `LD`: the directories it listed with getdents.
  - `NS`: whether it entered a mount namespace.
  Paths come from the tree, /tmp, /var/tmp and home; `.lake/runs/` and `.lake/cargo-target/` are excluded. To place these paths correctly, the reducer now traces bind, unshare, setns and fchdir, follows chdir and fchdir, and gives a child its parent's cwd. Two rows are RED (`run concurrency A + B: RED(shared scratch: …)`) when any of these holds:
  - one writes a path the other writes;
  - one removes a path that holds the other's write or directory;
  - one writes inside a directory the other made;
  - one writes a path the other reads, either touched or stat'ed;
  - one adds or removes an entry of a directory the other lists.
  This is judged over every pair of rows run now, and each row run now against every carried row's record, whether or not they overlapped in time this once. The next schedule may overlap them. Two rows that each make their own directory under one parent (host-file-sim's `.lake/host-file-sim/run-<random>` shape, the tests' `~/.cache/nd-t/<unique>`) do not collide unless one lists, empties or writes into the other's. A concurrent red is a red like any other. In pre-push a concurrency red has no parent counterpart, since the parent's judge is untraced and runs one row at a time, so it is a NEW RED.
- *Rows whose writes cannot be seen run alone.* That covers a `cargo-untraced:` row, every row of an untraced judge, and a row whose last run entered a mount namespace of its own. Measured: 12 rows, the launcher, client and devtools cargo rows and bar.sh, all through bwrap. Their paths are named in the namespace's view; `/tmp/newroot` is bwrap's pivot inside its own tmpfs. A row found unseen after running beside others, either with no read-set or with NS, is re-run alone, and so is every row that ran beside it. Those runs are the verdicts (`  alone ROW: …`), and from then on the hint schedules the row alone from the start.
- *A read-set traced in a mount namespace never narrows and never carries.* This tightens GATES-20 and closes a fail-open candidate. A sandboxed process reads through mounts and names what it reads in its own view; the measured read-sets hold `launcher/newroot`, `client/newroot`. So its read-set may miss a box path its verdict depends on. Such a record no longer narrows selection (valid_readset) and is never reused or carried. The same holds for a record from before GATES-20g, which does not say whether it was traced in a namespace. The static rules apply. The in-namespace path is the SYMPTOM. The proper key for those rows is the HOST view of what bwrap mounted: trace the parent's mounts, or translate newroot paths through the bind table. That is GATES-20m (cv 01a15816-7439), and it would also let them run beside others (ROOT approved this containment inside 20g).

**Decision, 20l (scripts/standing.sh, gates/runs.py, gates/converge.py): the carry.**
- *Rows.* Standing runs runs.py with `--reuse <G>/carry.record --record <G>/carry.new --daily ND_DAILY` (default 86400). A row whose traced key is byte-identical on this tree is not run; its lines and WASTE lines are carried (`  carry ROW: carried (key …, byte-identical to its run at TREE TIME)`). The key covers every path it touched, stat'ed, listed or exec'd, its row line, its waste rows, the runner and the tools. The rule is GATES-19's reuse key, now also used in standing. A record whose run is older than a day is re-run (`  daily ROW: re-run …`). The re-trace check is what catches a narrowed record, and only a run can make it, so every row runs at least daily. Only ok rows are recorded, so a red is never carried.
- *Build and census.* `build=ok(carried SHA: inputs byte-identical)` when the build inputs are byte-identical to those of the last build that read ok in this directory, whose `.lake` is that build's product. The build inputs are every `.lean`, `.c` and `.h`, `lakefile.lean`, `lean-toolchain` and `lake-manifest.json`, as git blob ids from the judged tree object. The census is carried the same way over the build inputs and every path under `gates/`, which holds the census's allow tables and its code. Each carry lasts at most a day. A key file is removed before its stage runs and written only after it reads ok. The gates, the generated files, the Rust workspace and the waste ceilings run every time.
- *Times.* The STANDING line gains `carried=N daily=N`. Standing writes `stages: gates=Ns build=Ns cargo=Ns census=Ns generated=Ns runs=Ns waste=Ns total=Ns` from its own clock (`<sha12>.times`). Every CONVERGENCE gains `TIMES …` and `ROWS wall …; ran N: ROW Ns (where), …; carried N: …; daily N: …`, read from the runner's own lines and never from the read-set store's mtimes, which concurrent judges write. Times are reported and never gated.

**Measured** (hbox logs/g12/meas*.{log,runs.out}; the standing tree at 0b86cb067bec, the tree convergence 1 judged, under standing's lock, with a private trace store, `SWARM_MEM_MAX=6G`):

| | rows wall | how |
|---|---|---|
| before (convergence 1) | ~43 min (~2580 s) | serial, one directory |
| 20g, steady state (run 3) | **875 s (14.6 min)** | 16 rows concurrent in ~558 s (row time 1631 s; the critical path is bench-worstcut-rows at 436 s), then 12 namespace rows alone in 317 s; 11 rows on borrowed slots; waste 79/79 ok |
| 20g, first sighting (run 2) | 2157 s | the 12 namespace rows found NS beside others: they and their neighbours re-run alone (once) |

The first model (run 1, 805 s) placed writes too coarsely, at the first component under home or /tmp. It read 90 false pairs: `~/.cache` (the tests' unique dirs) and `/tmp/newroot` (bwrap's in-namespace pivot). The model above replaced it. With 20l, a docs-only delta carries the build, the census and every row whose key it does not touch. That leaves the gates, the generated files, cargo and the waste check, about 3 minutes warm, until a row's daily re-run falls due.

**Plants** (hbox `logs/g12/new/plant20g.sh` → `plant-final.out`, 5/5 repeated runs green; a fake tree of shell exes under the real strace and a fake common dir; `plant20l.sh` → `plant20l.out`):
- P1: two rows write `.lake/shared/out` → RED; a third row in its own `{fresh}` → not red.
- P1b: `run-<random>` dirs under one parent, with one row listing the parent → RED.
- P1c: the same dirs, unseen by each other → ok.
- P1d / P1e: a row removing another's scratch → RED, including when it made the parent itself.
- P2: rows in their own `{fresh}` → ok, 2 borrowed, 3 s wall against ≥ 9 s serial.
- P3: a write of a path another row reads → RED.
- P4: a FAIL beside passing rows → RED, exit 1.
- P5: a live waiter → 0 borrowed; P5b: a dead waiter's file is ignored.
- P6: every slot held → 0 borrowed.
- P7: no read-set beside others → it and its neighbour re-run alone.
- P8 / P8b: carry, a changed read re-runs only its row, `--daily 0` re-runs all, and the carried WASTE line is measured.
- P9: untraced → one at a time.
- P10: an `unshare -rm` row → re-run alone, then scheduled alone.
- P11: a namespace row is never carried.
- L1–L9: a docs change moves neither the build key nor the census key; a gates/ change moves only the census key; .lean, .c and lean-toolchain changes move the build key; an equal key carries within a day; a different, stale or absent key does not carry.
- L10: TIMES/ROWS come from the standing's own lines.
Controls (grep for error|unbound|No such file|Traceback over every output): none.

**Re-emits / refusals.** readset.py and runs.py are runner files, so every traced key changes (RUNNER bytes). The first traced judge after this landing re-runs and re-stores every row. Records from before 20g never narrow or carry. `_walls.json` is new.

**Critique.**
- (1) The 12 namespace rows run alone: about 5 minutes of the 14.6 that cannot overlap. Mapping bwrap's mounts (mount/pivot_root are already in %file) would let them run beside others. That needs a mount table in reduce, and until it exists alone is the sound answer.
- (2) A write the tracer cannot see escapes the collision check: an fd inherited from outside, a sandbox's bind mount, or the new mount API. Such a row is either NS (alone) or untraced (alone); a traced row with an open-by-fd write is the residual.
- (3) A lander may wait up to one row (436 s at worst) for a borrowed slot. That cost was chosen over killing a judged row.
- (4) Reads outside the tree are not compared for write-read collisions; only tree reads are. Two rows sharing a fixed /tmp name are still caught when both write it.
- (5) `~/.cache/nd-t` holds 7295 leaked test dirs: CLIENT's (devtools::scratch); ROOT filed it. (6) The next lever on wall time is the critical-path bench itself (bench-worstcut-rows, 436 s): PERF's package-check-per-call (cv 01a1558a-1644, LANG), as ROOT named.

**GATES-20k fix: the tracer's own line as the box prints it (2026-10-21, PROTOCOL-23's refusal; GATES-12 verified at source).** 20k matched `^strace: `, so it never caught the failure it was written for. strace names itself by its argv[0], the absolute path readset.available() found, and writes on the same line as the tracee's unterminated output: `........../usr/bin/strace: ptrace(PTRACE_LISTEN,pid:…,sig:0): Input/output error`. All three hbox occurrences have that shape: gate-2/4c04f20aa738.log:860 and gate-3/2b29a0426731.log:412, which are 20k's own motivating cases, and gate-3/846590c46570.log:301, PROTOCOL-63's false refusal at about 04:30. 20k's plant used a fake strace that printed `strace: ` at a line start, so it checked its own fake and not the box's output. TRACER is now `(?m)(?:^|/)strace: .*$`.
Plant (hbox logs/g12/plant20k2.sh, over the three real lines and a fake strace at an absolute path that prints the dots and then `$0: ptrace(…)`): main's runner matches none of the three and reads RED once and RED always. This one matches all three, leaves ordinary lines (`test result: FAILED…`, `the strace tool`) unmatched, reads once → `flake`, ok, and reads always → `UNREAD(tracer twice: …)`. A plant's input must be the box's own output, never a reconstruction of it.

## GATES-23 · A whole-tree census of disjunctive theorem conclusions (2026-10-20, CX-GATES)

**Premise price.** Landed theorems gaining a hypothesis: none. Landed theorems restated: none.

**Decision.** The existing standing axiom/refinement census imports every built library module, then runs `#statement_census` over the same elaborated environment. For every theorem whose conclusion, after its binders and premises, is an outer `Or A B`, it writes `.lake/gates/statements.tsv`: source file, fully qualified theorem name, each pretty-printed disjunct and an ok/RED verdict. It errors when either disjunct is an existential containing a predicate named exactly `Collision`, the unbounded pigeonhole escape KERNEL-56 removed. `CollidesAmong` over an explicit list is a different constant and is not red. The census runs at every convergence (or carries only when the whole build and gates inputs are byte-identical), and on every full judge. A red census is a red verdict.

**Why Lean metaprogramming.** An elaborated type identifies the theorem, its actual binders, its actual conclusion and the constants inside the existential. Source parsing would have to approximate notation, implicit binders, macros and qualified names. The axiom and refinement censuses already pay for a whole-tree imported environment.

**Plant.** A real temporary Census module with `True ∨ CollidesAmong [1]` writes an ok row (`logs/CX-GATES-statement-green.log`, `.lake/gates/CXGatesPlant.tsv`); adding `True ∨ (∃ x : Nat, Collision x)` writes RED and Lean exits 1 (`logs/CX-GATES-statement-red.log:1-2`). The plant module was removed after the run.

**Critique.** This is a syntax census, not a proof that each disjunct depends on its premises. It catches the precise named existential shape and leaves logically equivalent aliases or unbounded collision claims written as a different predicate to the vacuity reader. Every disjunct remains listed for inspection. Pretty-printed expressions can be long, but the output is derived and does not enter the source tree.

**Meta-critique.** The temptation was to call a text search a theorem census because the target phrase is visually obvious. The Lean environment is a little more work but keeps the check attached to elaborated claims instead of comments or spelling.

## GATES-20m · Namespace read-sets use bwrap's host bind sources (2026-10-20, CX-GATES)

**Premise price.** Landed theorems gaining a hypothesis: none. Landed theorems restated: none.

**Finding.** GATES-20g made every NS read-set ineligible for selection narrowing or carry. A real hbox strace of the deployed bwrap mechanism has `mount("/oldroot/tank/…/source", "/newroot/input", … MS_BIND) = 0` (logs/CX-GATES-20m-bind.trace:144), then the child reads `/input` (line 213). The prior reducer names the latter in the namespace's view; a tree key cannot match it to the host source. On a busy trace, strace splits the mount call and its success across unfinished/resumed lines (logs/gates8-traces/cargo_launcher_resident.24.trace:4365 and the resumed line). The old reducer discarded that success.

**Decision.** The reducer now joins the unfinished and resumed setup calls. strace runs with `--decode-pids=pidns`: inside bwrap's PID namespace, `clone = 2` is annotated with the host PID that prefixes the child's lines (logs/CX-GATES-20m-pidns.trace:167). Without the annotation, the child is unknown and a directory bind would key its directory but miss its read of `OWNERS`; the reducer now leaves that record `HOST_VIEW=false` (logs/CX-GATES-20m-dir.trace:167,213). It records each successful bwrap bind from `/oldroot/S` to `/newroot/D`, and translates reads at `/newroot/D` during setup and `/D` after the second pivot to host path `S`. A source inside the judged tree is itself a keyed read, and the child's reads below the bind are keyed at their host paths. The row record says `HOST_VIEW` only when every process known to enter a namespace has traced bind sources and no unknown mount or foreign `setns`. A namespace record without that evidence remains ineligible. Key version v5 re-seeds records. NS rows still run alone because their writes are not translated for concurrency.

**Plants from real runs.** A real nd-bwrap/strace bind of the worktree file to `/input` produced `NS=true, HOST_VIEW=true, T=[CX-GATES-20m-source.txt]` (logs/CX-GATES-20m-bind.trace:144,213). The actual runs.py row over a directory bind read `CX-GATES-20m-dir/child.txt` in host view, then an unchanged second run carried it with zero rows executed (logs/CX-GATES-20m-dir-run1.out and -run2.out). Changing that child file moved the traced key and re-ran the row (logs/CX-GATES-20m-dir-run3.out). The parent runner over the same unchanged record did not carry it (logs/CX-GATES-20m-dir-old.out, `PLANT RED`). A real stored record from before GATES-20g lacks `NS`; `keyable` rejects it (logs/CX-GATES-20m-vintage.out), preserving the old fail-closed rule. The full outputs were read for error, unbound variable, missing file and traceback controls; the expected `FAIL harness-control` and `ALL PASS` came from actual executions. The temporary row, script, source and dummy host were removed after the runs.

**Critique.** A namespace using the new mount API, an unknown bind source, an unplaced child PID or `setns` remains unkeyed. External home/tmp host sources still follow GATES-20c's separately reported F2 boundary; this change keys host paths inside the judged tree. Bind writes remain unseen, so NS rows remain isolated rather than joining the concurrent schedule.

**Meta-critique.** The tempting shortcut was to strip `/newroot` from every path. That would call bwrap's own tmpfs scaffolding a host read and miss a bind whose source and destination differ. Reading the successful mount as the mapping is what gives the carry a defensible input key.

## GATES-20n · Complete the host-view evidence for real bwrap rows (2026-10-20, CX-GATES; follow-up to 20m)

**Premise price.** Landed theorems gaining a hypothesis: none. Landed theorems restated: none.

**Finding.** The first convergence on ed34b1b had 166 disjunctions censused and still recorded `HOST_VIEW=false` for cargo:client:real, cargo:launcher:members and script:scripts/bar.sh. A filtered real CLIENT test under the deployed strace flags reads ok and reproduces `NS=true, HOST_VIEW=false` (logs/CX-GATES-clientreal-trace.out). The actual trace contains `umount2("oldroot", MNT_DETACH <unfinished ...>` then `<... umount2 resumed>) = 0`, and an idle clone child whose host PID is explicitly annotated in the successful clone return. 20m did not join the unmount halves; the resumed half lost the `oldroot` argument and falsely marked the mount unknown. It also required a child to emit its own selected syscall line even when the clone line already identified that child in the host PID view.

**Decision.** Join unfinished/resumed `umount2` exactly as other mount setup calls are joined. A successful `oldroot` or `.` unmount remains the known bwrap cleanup; any other target remains unknown and ineligible. Count a clone child as seen when the parent return gives its host PID. An unannotated clone inside the PID namespace is explicitly marked unknown and remains ineligible. No key or eligibility check is removed; this supplies the evidence those checks require. Key version v6 re-seeds records.

**Plants.** On the full trace of the real filtered CLIENT run, the landed 20m reducer reads `HOST_VIEW=false` and this reducer reads true. The exact resumed unmount and host-PID clone lines are printed in logs/CX-GATES-20m-followup-plant.out. Mutating the real trace to unmount `unexpected` still reads false, as does removing the host-PID annotation from the real clone return. Both negative traces remain under the CX-GATES log prefix. The filtered CLIENT test read one passed, zero failed. A separate real filtered launcher members run read ten passed, zero failed and already has  under this reducer (logs/CX-GATES-members-trace.out); its multiple bwrap spawns did not need a new exception.

**Critique.** Tracer filtering can make an idle child lack a prefixed syscall line, but the parent clone return is still direct evidence it exists. Key safety still depends on strace -f following any child that actually makes a traced path call. If strace loses a child entirely, that is a tracer failure beyond this mount parser and should be handled as UNREAD, not inferred from an idle child.

**Meta-critique.** The synthetic single-bind plant for 20m had no interleaved unmount or idle threaded child. Production convergence exposed the missing trace shapes. This follow-up uses the actual filtered row trace and keeps adversarial unmount and unannotated-clone cases red.
## GATES-20o · A completed pre-bind namespace child has a host-view read-set (2026-10-20, CX-GATES; ROOT ruling A)

**Premise price.** Landed theorems gaining a hypothesis: none. Landed theorems restated: none.

**Finding.** The real filtered members trace at logs/CX-GATES-members2.trace had one NEWNS child with pre-pivot readlinks and no bind, pivot or exit marker. strace -qq suppressed exits, so 20n correctly recorded HOST_VIEW=false. The same filtered row under -q recorded exits and was HOST_VIEW=true (logs/CX-GATES-members3.trace). A smaller real bwrap plant isolates the case: logs/CX-GATES-20o-real.trace:142 cloned host PID 670549 into NEWNS; lines 158-164 read host paths before any mount; line 165 proves it exited. The landed 20n reducer reads HOST_VIEW=false on this trace.

**Decision.** Trace with strace -q. The reducer accepts an unmapped NEWNS PID in the host-view proof only when its trace has an exact exited-with marker, no mount, pivot_root or umount2 attempt, no later syscall or second exit marker for that PID, and no unknown mount. Before its first pivot, host_path already translates its path names as host paths; no bind map is needed for this proved-safe lifetime. A missing exit marker, setns, a new mount API call, an unknown mount, or an unplaced clone remains HOST_VIEW=false and is never narrowed or carried. Mapped children retain their existing rule. The traced key advances to v7, so older records re-run.

**Real plants.** The script scripts/CX-GATES-20o-plant.sh in the private worktree ran two real nd-bwrap children under the deployed tracer: the first stopped after a missing source read and before a bind, the second bound and read CX-GATES-20o-source.txt. The former generated the proved exit above; the latter put that source in T. The old reducer read false, this reducer true. With the actual runs.py row, the first run passed its known-red control and stored an eligible read-set (logs/CX-GATES-20o-run1.out); an unchanged second run reused the verdict with zero rows executed (run2.out); changing the bound source re-ran it (run3.out). Deleting only the real exit marker at logs/CX-GATES-20o-real.trace:165 produced logs/CX-GATES-20o-incomplete.trace: its reduction is NS=true, HOST_VIEW=false, keyable=false (incomplete-plant.out). Feeding that read-set to the actual runner as an otherwise byte-identical prior record forced a re-run, not a carry (incomplete-rerun.out). All plant outputs were read whole and checked for accidental error, unbound variable, missing file and traceback lines.

**Runtime price.** Six paired runs of the same two-bwrap plant, alternating -q and -qq, measured median wall 0.027 s in both modes. Median trace size was 46,673 bytes with -q and 46,499 with -qq: six exit markers and 174 extra bytes (logs/CX-GATES-20o-cost.out). This bounds the observed cost of this small plant; it does not predict the wall cost of the larger members row.

**Critique.** The proof relies on strace having followed the child through its exit. A tracer failure can withhold a verdict, and a truncated trace without the exit cannot carry. Exact exit-marker matching may reject a new strace spelling until the parser is updated. Marking even a failed mount attempt unsafe is deliberately stricter than the final mount state; it keeps a setup path from being called pre-bind after partial observation.

**Meta-critique.** The schedule-sensitive members row invited a blanket exception for a child with no observed bind. Absence of a bind in an incomplete trace proves too little. The real exit marker and the absence of any setup attempt give a concrete boundary that can be removed and tested red.

## GATES-20p · A moved added theorem keeps its statement (2026-10-21, CX-GATES; ROOT ruling A)

**Premise price.** Landed theorems gaining a hypothesis: none. Landed theorems restated: none.

**Finding.** P7's real failed land (logs/CX-P7-land4.log and logs/CX-P7-run4-stale-diagnostic.log) retains the byte-identical statement of e86f237's `escrow_link_bites` in Ledger/Proofs/EscrowWitness.lean, but moves it and changes one proof line to `judge_live judge2`. `git merge-file` cleanly replays e86f237's addition at EOF, duplicating the theorem; GATES-20b's whole-added-block comparison calls that a lack and refuses `stale path`. The replay's duplicate is not a removed declaration.

**Decision.** For a pure insertion of one Lean `theorem`, identify its exact statement through `:= by` and count it as retained when the candidate has that statement exactly once as active code, outside Lean comments and strings. The other added blocks of the commit still need their ordinary contiguous matches. Conversely, when that statement is absent, `lacks` is true even if the replay conflicts on other edits; a missing added theorem remains a stale-path refusal. A conflict discovered this way reports the exact missing theorem statement rather than merge conflict markers. Changes of statement, unknown declaration shapes, and multiple declarations in one insertion block retain the conservative existing treatment.

**Real plants.** logs/CX-GATES-stale-plant.py uses the P7 working file and the historical e86f237 before/after blobs. The real P7 candidate now gives `lacks=False` and the full `stale` guard passes. Removing `escrow_link_bites` from a scratch byte copy of that same P7 file gives `lacks=True` despite replay conflict and the full guard refuses `stale path: Ledger/Proofs/EscrowWitness.lean` naming e86f237. A copy whose theorem text is present only inside a Lean comment is also refused. The existing GATES-20b stale-copy plant uses the real a1ca640 launcher/tests/members.rs plus its original lane line (logs/gates9-plants.sh P1; verdict logs/gates9-plants-new.out); the full guard still refuses `stale path: launcher/tests/members.rs`. Full output: logs/CX-GATES-stale-plant.out.

**Critique.** This is a conservative textual declaration check, not Lean elaboration. A statement rephrased but equivalent still needs a manual rebase or explicit revert; a novel syntax of theorem declaration may not get the moved-statement exception. The full judge remains responsible for compiling the candidate. A true removal now refuses even where merge replay conflicts, closing a gap exposed by the removal plant.

**Meta-critique.** The original whole-block comparison treated an implementation proof as the identity of a declaration. That was an attractive general text rule, but it made the replay location more important than the theorem actually retained by the candidate. The replacement scopes the exception to the byte-identical statement and tests it against both the real false positive and a true deletion.

## GATES-20q · The charter's 1 MB file law is a source gate (2026-10-21, ROOT review H3; written by GLM-5.3-flash under supervision)

**Premise price.** Landed theorems gaining a hypothesis: none. Landed theorems restated: none.

**Finding.** CHARTER.md, Working rules: "no large artifacts, no fixtures over 1 MB". Nothing enforced it: a0eb75f landed gates/certificate-grant.json.gz at 11,961,094 bytes, the full judge passed it and so did its reader (REVIEW-20261021 H3).

**Decision.** gates/size_limit.py (stdlib only, `python3 -I` safe) is a source gate in gates/check.py (`size_limit`). Every file of the judged tree above 1,048,576 bytes is red by name with its exact size; exactly 1,048,576 is fine. A git tree is listed by `git ls-files` (a failing git raises); an exported candidate tree, which is what scripts/pre-push hands check.py, is walked outside .lake .git target node_modules. gates/size-allow.tsv (`path<TAB>bytes-ceiling<TAB>reason`) holds the exceptions (its single row is below): an allowed file is red above its ceiling, a malformed row (not 3 fields, non-integer ceiling, ceiling not above the limit, empty reason, duplicate path) is red, and a stale row (file gone or now under the limit) is red. gates/size_limit_plants.py is the plant: a synthetic tree with a 1,048,577-byte file is red by name, a 1,048,576-byte file is not, allow/ceiling/malformed rows behave, and a mutant with the `size > LIMIT` comparison replaced by an unreachable bound must exit 0 on the same tree where the real gate exits 1 (the plant asserts the comparison occurs exactly once, so a refactor cannot silently disarm it); `--real ROOT PATH BYTES` additionally asserts the real tree is red naming PATH at BYTES.

**One dated exception (ROOT ruling A, 2026-10-21).** gates/size-allow.tsv carries exactly one row, dated 2026-10-21: `gates/certificate-grant.json.gz`, ceiling 11961094 (its exact current byte count), reason "review H3 (REVIEW-20261021.md); the certificate pins a 6,857-declaration closure; re-pin pending under cv task 01a15f18-25ce; this row goes RED by the stale-row check when the blob is re-pinned". Without the row the gate is RED on main (`gates/certificate-grant.json.gz: 11961094 bytes exceeds the 1048576-byte limit`) and refuses every landing, including the one that re-pins the blob. This is not a weakened check: no size gate existed before, so the law goes from unenforced to enforced for every tracked file; the one exception is named, bounded to the exact current byte count (any growth is refused), dated, and self-removing (when the blob is re-pinned at or under 1 MB the row is stale and the gate goes RED on the row until it is deleted). The certificate card owns the re-pin.

**Plants.** Before the row existed, `python3 gates/size_limit_plants.py --real . gates/certificate-grant.json.gz 11961094` printed (with the row, `--real` is expected to fail: the tree is allowed; the synthetic plants still run) `PLANT RED: size comparison disabled -> the 1048577-byte file escapes; the real gate refuses it` and `SIZE_LIMIT PLANTS GREEN`.

**Critique.** The limit is on tracked file bytes on disk, so a compressed blob is measured compressed and a 1 MB file that unpacks to 1 GB passes; the law as written is about committed bytes. Git-tree mode counts tracked files under SKIP_DIRS names while walk mode skips them, an asymmetry that only matters if something under target/ is ever tracked. The allowlist can launder an exception, but only as a reviewable row with a reason and a ceiling that goes stale loudly.

**Meta-critique.** The review noted that the instrument was blind to the next wound, "red as steady state hides everything". Landing a gate with a standing exception risks being exactly that. The mitigation is that the exception is one named file, ceilinged at its exact bytes, and removes itself loudly: the stale-row check is the timer.

## GATES-20s · The statement census reads the escape's shape, not its name; a standing plant proves it can fail (2026-10-22, ROOT review H4, program card G1; Claude baseline of experiment 2)

**Premise price.** Landed theorems gaining a hypothesis: none. Landed theorems restated: none.

**Finding.** GATES-23's census could not go red on a real vacuous theorem. It flagged an existential holding a constant named exactly `Collision`, and KERNEL-56 (482aecc) deleted every such constant (`Collision`, `Trie.Coll`, `HashColl`) two days before GATES-23 landed. The rule matched nothing the tree can contain. Its plant declared a new `Collision` to make it bite, so it tested its own fixture and not the class (the GATES-20k lesson). Measured on f8d04ac: main's census over the built tree plus three real vacuous theorems printed `STATEMENT-CENSUS ok: 171 disjunctions`, with all three rows `ok`. It also listed only conclusions whose outermost connective is `∨`. A disjunction under `∧`, `↔`, `∃` or behind a definition was never seen (78 theorems).

**Decision.** A disjunct is RED when it holds a digest equation `f a = f b` (one head, different arguments) whose two sides BOTH mention variables the statement chooses. A chosen variable is one bound by an `∃` of the disjunct or of the conclusion and not bounded by a conjunct `t ∈ L` whose list `L` mentions no free chosen variable. That is the pigeonhole shape: for any `f` into a finite type it holds without the theorem's premises. `CollidesAmong hash S` and `Trie.CollAmong S L` unfold to `∃ p ∈ S, ∃ q ∈ S, …`, so they read ok over a list of the theorem's own objects and RED over a list the statement chooses (`∃ S, CollidesAmong hash S`). No name is special-cased. The walk goes through `∧`, `↔`, `∃` and up to four one-step unfoldings of the census roots' own definitions, so an alias is read through its body. Every maximal disjunction is a row of `.lake/gates/statements.tsv`. The walks are total (law 4, no `partial`): a statement more than 256 connectives deep reads RED as `deeper than 256 connectives: not judged`, never ok. My first build used four `partial def`s, and `gates/size.py --write` read `partial defs (deployed) 4` against its ceiling of 0.
Before it reads the tree, the command judges four fixed statements. Two must read RED: `True ∨ ∃ a b : Nat, a ≠ b ∧ a % 2 = b % 2`, and the same over `∃ L, ∃ a ∈ L, ∃ b ∈ L`. Two must read ok: the same over `[x, y]` for bound `x y`, and `∃ a b, (a, b) ∈ S ∧ …` for a bound `S`. A misread fixture prints `STATEMENT-CENSUS harness: …`, which census.py reads as RED.
**The standing plant** is `gates/statement_plants.py`, a `script:` row of gates/runs.tsv (selected on every judge, run after the build). In its `{fresh}` directory it compiles `StatementPlant.Vacuous`, a module outside every lib. That module holds three real vacuous theorems with `chain_binds`'s binders and premises, each proved by `.inr` from `lawful_collides hE` (KERNEL-56's pigeonhole proof from `E.Lawful` alone, logs/kernel21-ver-pigeon.lean), so no chain premise is used:
- `chain_binds_inline`: the escape written inline;
- `chain_binds_alias`: the escape through `def Escape`;
- `chain_binds_chosen_list`: `∃ S, CollidesAmong E.hash S`.

It also holds a control, `chain_binds_named`, which is the landed statement `:= chain_binds hE`. The script asserts three things:
- the census over the tree plus the plant reads `STATEMENT-CENSUS RED (3)` and names exactly the three, with the control's row ok;
- the tree alone reads `STATEMENT-CENSUS ok`;
- a scratch copy of Census/Statements.lean with the two-sides test disabled is refused by its own fixtures.

Its `--harness-control` expects a fourth RED that the plant does not hold. The first full judge (logs/base2-land1.log) refused it twice. (1) The judge's `{fresh}` is `.lake/runs/script:gates/statement_plants.py-N`, and a `:` splits a LEAN_PATH entry: the plant run read `unknown module prefix 'StatementPlant'` and the mutant run silently loaded the real Census.Statements (`0 disjunctions … fixtures: 2 RED, 2 ok`). The script now runs the tree's `lean` with cwd = SCRATCH and names scratch directories relatively, and it refuses a LEAN_PATH entry holding `:` by name. (2) Importing census.py wrote `gates/__pycache__`, which the concurrent `cargo:devtools:workspace` row reads (GATES-20g's shared-scratch RED). The script sets `sys.dont_write_bytecode`. The plant was re-run in a `script:`-named scratch on hbox: GREEN, and `--harness-control` RED. My own runs had used colon-free scratch paths, so they could not see (1).

**Plants** (hbox wt/base2 at f8d04ac, against the built f8d04ac oleans of wt/cxfold, read only):
- `python3 gates/statement_plants.py .lake/sp1`, exit 0, 19 s:
  - `STATEMENT-CENSUS RED (3):` names `…StatementPlant.chain_binds_inline`, `chain_binds_alias` and `chain_binds_chosen_list`, each with `right disjunct: \`E.hash … = E.hash …\` compares two inputs the statement chooses`;
  - `STATEMENT-CENSUS ok: 250 disjunctions … (fixtures: 2 RED, 2 ok as required)`;
  - `STATEMENT-CENSUS harness: fixture \`True ∨ ∃ a b : Nat, …\` read ok over 1 disjunctions; it must read RED over 1`;
  - `PLANT RED: the two-chosen-sides test disabled -> the census's own fixtures refuse it`;
  - `STATEMENT PLANTS GREEN`.
- `--harness-control`: the same lines, then `STATEMENT PLANTS RED: plant (harness-control: a fourth RED expected): wanted \`STATEMENT-CENSUS RED (4):\` with Lean exit 1, read exit 1`, exit 1.
- The control is REVIEW H4's listing. Every theorem main's census listed is still listed, and none reads RED. The 250 rows are main's 167 (H4 counted 166 at its tip) plus 78 theorems whose disjunctions sit under `∧`/`↔`/`∃`/a definition. The 81 `CollidesAmong` rows and 3 `Trie.CollAmong` rows read ok. Peak 1.65 GB per census run.

**Critique.** The rule's first draft was "one chosen side suffices; membership bounds only as the first conjunct of its own `∃`". It read five landed theorems RED, and none of them is vacuous:
- `Protocol.Settle.settle_refused_final`, `settle_refused_absorbed` and `windowedIn_refused` (`∃ c' v a, recordOf X c' v a ∈ S ∧ txIdOf X c' = txIdOf X c ∧ …`). One side of the equation is the theorem's own `c`, and the witnesses range over `S`.
- `Host.openWith_backup` and `openWith_backup_restart` (`∃ o' more, R = .ok o' ∧ o'.sealed = o.sealed ∧ …`). One side is the theorem's own `o`.

I tightened the rule instead of allow-listing them: both sides must be chosen, and a membership guard anywhere in the `∧`-spine bounds every chosen variable in its element term. I added no equation-pin rule (`R = .ok o'` bounds `o'`): nothing landed needs one, and each extra bounding rule is a way around the census.
What it still misses (verbatim from the experiment narrative): a lucky second preimage, a closed list big enough for pigeonhole, contradictory premises, definitions outside the roots or deeper than four unfoldings, or a membership guard over a term that forgets its witness (`a.size ∈ L`). In that last case `∃ a b, a.size ∈ L ∧ hash a = hash b` reads ok though `a` ranges over infinitely many strings of each size. **The named next tooth** (the cross-family reader, promo/READ-G1-grok.md, verbatim): "a membership that finites a projection and forgets the witness": `theorem forgotten (hE : E.Lawful n) : True ∨ ∃ a b : ByteArray, a.size ∈ [n + 1] ∧ b.size ∈ [n + 1] ∧ a ≠ b ∧ E.hash "x" a = E.hash "x" b`. `[n + 1]` mentions no chosen variable, and `leftFree` strikes every chosen variable inside the element term, so `a.size` strikes `a` and the row reads ok. It is nevertheless `lawful_collides`: a digest has `n` bytes and there are `256 ^ (n + 1)` strings of length `n + 1`. It is the fifth miss above pinned to a length that exceeds the codomain, and it matters because every digest input in this tree is a `ByteArray`. The tooth: a membership strikes a variable only when the element term is the variable itself or a constructor application that keeps it (`recordOf X c' v a`, `(a, b)`), never a projection of it (`.size`). Filed as cv task 01a1654c-543c, with `forgotten` as a fourth plant theorem. The fixtures prove the classifier, not the environment walk. A census that read zero theorems would still pass them, so the printed row count and the plant's tree run are the walk's evidence.
**Meta-critique.** The bias is confirmation: I wrote the plants first and then a rule that fired on them, and the first rule over-fired five times on real theorems. Only the tree-wide control caught it; the plants could not, because they were what the rule had been shaped to. A detector tuned to the examples its author already holds looks finished when it fires on them. The opposite pull is the one that made GATES-23: a name list (`Collision`, `Coll`, `HashColl`) would have made every plant I wrote bite and still read the next renamed escape ok.

## GATES-20t · The stale-path guard's `.lean` half is a declaration diff from the census environment, and a landing's map of what it deletes and restates is checked (2026-10-22, Ember's R-0023; R-0034 under promo/READ-GUARD-grok.md; card cv 01a15f18-2636; CX-GUARD; supersedes GATES-20p)

**Premise price.** Landed theorems gaining a hypothesis: none. Landed theorems restated: none. Gates code only.

**Finding.** GATES-20b's `stale` decided "this landing reverts commit C on path P" from text on every path. For `.lean` paths GATES-20p added a Python lexer of Lean (`active_lean_statement`, the `^theorem … := by` regex) and a rule that a missing added theorem is a lack even where the replay conflicts. Three bites:
- P7 (d7989d9 on fe89edf): `escrow_link_bites` moved and re-proved, read as a revert of e86f237. That bite is what produced 20p.
- E1 (4916f3a on f8d04ac), today: `runSetupWith_spec`/`runSetup_spec` in Lang/Proofs/Load.lean were restated (`readsData` gained `look`). 20p's missing-statement rule read that as a revert of d7989d9, and the landing needed `--reverts d7989d94af13` (R-0029). Without 20p's rule plain 20b finds no lack in E1 (measured: this guard's `stale` forwards none; that the replay conflicts is inferred).
- Replayed over main's last 80 landings (logs/guard/replay80.out), today's `stale` would refuse three landings of 10-20 that passed the guard live then: 80419cf, 832a815 and eb7028d, all `.lean` restatements. The stricter rule came with 20p. The fold's S9 did not bite: no S-step is refused and no S9 land log holds `stale path`.

Text cannot tell a moved, re-proved or deliberately restated declaration from a stale copy. The elaborated environment can. The census already pays for it (GATES-4, GATES-23).

**Decision.**
1. **The export** (gates/decls.py, the judge's code). A Lean command, kept as text in decls.py and written after the imports into `.lake/gates/DeclRun.lean` as census.py writes CensusRun, writes one row per constant that has a declaration range. That range is the elaborator's record that the source declared the constant: generated `.eq_1`, `match_`, `_proof_` and `_simp_` constants have none. Each row holds: name, owner, module, kind and source lines; the statement's canonical serialization; and, for a non-theorem, the value's. A theorem's proof is irrelevant. The serialization is the term's post-order DAG, hash-consed on the emitted token. Binder names are erased, binder info is kept, and constants are abstracted to a first-visit list. The digest is SHA-256 over it, taken in Python. No hash is equality inside Lean. A theorem also carries its statement as the kernel printer's text, for the diff a refusal prints. The text is never compared.
2. **Check 1: the direct diff against the parent.** Every parent declaration absent from the candidate, and every theorem or axiom whose statement digest differs, is named by a message line:
   - `RENAMES: OLD → NEW`: NEW's statement must equal OLD's under the map (checked).
   - `RESTATES: OLD → NEW`: the same check. A line naming an unrelated declaration is refused `restate not equal`, with the diff.
   - `RESTATES-MEANING: OLD [→ NEW]`: a deliberate change of meaning. The statement must differ.
   - `DELETES: NAME`.
   - `DELETES-MODULE: M`: one line for a removed module and every declaration in it. A removed module is never a free pass (R-0034 (2)).

   A theorem whose statement differs without a line is `undeclared restatement: NAME (M:a-b)`, printed with the token diff of the two statements. A line that applies to nothing is `unused map line`. A line covers what its declaration owns: constructors, recursor and projections (from Lean), and a constant whose name extends the declaration's and whose recorded range lies inside it (`casesOn`, `noConfusion`, a `where` helper, the axiom `native_decide` adds). A two-name line renames OLD inside every candidate statement, inverted (NEW → OLD by the longest component-wise prefix), so the cached parent digest never depends on a map. A private declaration whose user name is unique in both trees is matched across a module move by that name. The refusal prints the lines to paste. The lines live in the message, so `git log --grep RESTATES-MEANING:` finds every change of meaning. This makes a message's restatement prose a checked list. E1's message described its restatements in prose (eight LiveHoles statements and the `readsData`/`relReads` family). Its measured map is 66 lines: 48 changes of meaning and 18 deletions.
3. **Check 2: the stale copy.** `stale` keeps the language-agnostic detector (20b, 20b′: `git merge-file` replay, then contiguous block containment). For a `.lean` module it no longer refuses. It writes each lack to `--lean-lacks`: path, C, side, and the lines of C's added blocks in main's copy, or of C's removed blocks still in the candidate. scripts/commit hands that file to pre-push. The judge maps those lines to the declarations whose ranges hold them, using the parent's rows for an added block and the candidate's for a removed one. An added block is explained when each such declaration is in the candidate as main has it (theorem: same statement; anything else: same type and value) or is named by the map. A removed block is explained when each such declaration is in the parent as the candidate has it. Otherwise: `stale declaration: NAME (P:a-b in main's copy): C changed it …`. A non-blank line in no declaration and no module doc keeps the text verdict (`stale path: P … outside every declaration`, `--reverts C`). This is what catches a reverted definition body, which check 1 cannot see.
4. **Where.** scripts/pre-push, both modes, the step `decls` right after the build (fast: after `lake build $targets`; full: after the census). Index mode only. A landing that changes no module prints `decls: ok (no module changed)`. `--no-build` with a changed `.lean` is RED: `decls: a changed module cannot be judged without a build`. An export that fails is `decls: NO VERDICT`: RED, or KILLED(load) when it names a signal (GATES-15/16).
5. **The parent's digest: a per-tree cache, composed.** A landing exports only its REACH: the changed modules and their importers in either tree, plus importers of a deleted module. That is what fast mode already builds. A module outside both reaches has the same source and imports, so the same declarations. A build input (lakefile, toolchain, manifest) makes the reach the whole tree. The candidate's whole digest is the parent's rows outside the reach plus its own export. It is written atomically to `$common/nanodregg-decls/<tree>-<exporter>.tsv.gz` (newest 64 kept: the judge's own files). After the compare-and-swap that file is main's. On a miss, the judge materializes the parent in its slot before the candidate's build, builds the libs, exports it whole and caches it. A miss happens on the first landing after this one, and after any exporter change: the exporter's digest is in the key.
6. **Deleted:** rebase.py's `active_lean_statement`, `added_theorem_statement`, `retained_added_theorem` and `missing_added_theorem`, `holds`'s call to the third, the missing-statement branches of `lacks` and of `stale`'s hunk printer, and the `.lean` refusal. `holds`/`lacks` are block containment again, now shared by `_blocks`, which also names the failing blocks for `--lean-lacks`.

**Plants.**
- **Standing.** `gates/decls_plants.py --synthetic {fresh}`, a `script:` row of gates/runs.tsv. It runs decls.py's own `judge` over hand-made export rows; only the Lean export is replaced. Its 23 cases each name the refusal they must read: moved; deleted, declared and not; restated, as RESTATES-MEANING and undeclared; RESTATES checked on the same name and refused at an unrelated name; RENAMES equal, unequal and undeclared; an unused line; an owned constructor, declared and not; a private declaration moved across modules; a module deleted undeclared, declared, and declared while still present; and the stale-copy lack over a reverted definition value, a held one, a non-blank line outside every declaration, and a blank one. Its `--harness-control` adds a case nothing meets and reads `decls-synthetic: RED (1): harness-control`. It writes no `__pycache__` (GATES-20s's shared-scratch RED).
- **Historical**, by hand. `gates/decls_plants.py --repo … --work … --cache …` over real commits, with the maps pinned in gates/decls-plants.tsv. It runs the real `rebase.py stale --lean-lacks`, then the candidate is built and `decls.py judge` runs. Every plant asserts its refusal NAMES, and its mutation is checked to be in the candidate before the verdict is read. Whole outputs: hbox logs/guard/plants-all.out and logs/guard/plantwork/plants.log.
  - **H4** 832a815 on its parent (a 10-20 restatement today's 20p refuses), its 22-line map: `PLANT H4 GREEN (decls: ok — 87 module(s) exported, 3624 parent declaration(s) in the reach, 22 map line(s), 21 declared change(s) of meaning)`. **H4-** without `RESTATES-MEANING: Nanodregg.Host.Cli.import_genesis_iff`: `decls: undeclared restatement: Nanodregg.Host.Cli.import_genesis_iff (Host.Proofs.Cli:36-52)`, with the diff.
  - **H1** P7 (d7989d9 on fe89edf), its 111-line map, which names no `escrow_link_bites`. `stale` forwards the lack (`Ledger/Proofs/EscrowWitness.lean e86f237e0533 … add 229-253`), and the judge explains it by the declaration: `PLANT H1 GREEN (… 278 module(s) exported, 10663 parent declaration(s) …, 111 map line(s), 83 declared change(s) of meaning)`.
  - **R2** (pinned, R-0034 (3)), H1's negative control: GATES-20p's removal of `escrow_link_bites` from the real P7 file (d7989d9's blob; its docstring goes with it, since a docstring left before `end` does not parse). The plant reads `decls: undeclared deletion: Nanodregg.Ledger.Proofs.escrow_link_bites (theorem, Ledger.Proofs.EscrowWitness:229-252)` AND `decls: stale declaration: Nanodregg.Ledger.Proofs.escrow_link_bites (Ledger/Proofs/EscrowWitness.lean:229-252 in main's copy): e86f237e0533 …`.
  - **H3** S9 (6c31cab on ac34521), the declaration-PRICE fixture (it never bit), its 27-line map: GREEN. The 27 match IMPACT-S9's census count of user theorems changing type. **H3-** without `runHoleGuard_cost`: `undeclared restatement: Nanodregg.Lang.runHoleGuard_cost`.
  - **H2** E1 (4916f3a on f8d04ac), its FULL 66-line map (48 RESTATES-MEANING, 18 DELETES), with no `--reverts d7989d94af13`: GREEN. **H2-** without `RESTATES-MEANING: Nanodregg.Lang.selectHole_origin`: `undeclared restatement: Nanodregg.Lang.selectHole_origin (Lang.Proofs.LiveHoles:47-62)`.
  - **C0**, the control, H2 plus `DELETES: Nanodregg.GatesPlant.nothing`: `unused map line: DELETES: Nanodregg.GatesPlant.nothing`.
  - **R1** (pinned) GATES-20b's V1, a1ca640's `launcher/tests/members.rs` plus one lane line on 4916f3a: `stale path: launcher/tests/members.rs: the landing would revert 0cd046c8b944's change …` (the text half, unchanged).
  - **R3**, a stale `Emit/Rust.lean` (0856ca3^'s copy plus one lane line, on 4916f3a), whose statements are all intact: `stale declaration: Nanodregg.Emit.Rust.bounds (Emit/Rust.lean:91-103 in main's copy): 0856ca311754 …`. Check 1 alone would pass it.

  Run 1 (logs/guard/plants-all-1.out) read every plant as above except R2. That run judged R2 under a plant subject, so the text half refused H1's `--reverts 42c261b` as cross-layer. The plant now carries P7's own message, and R2 was re-run (logs/guard/plants-R2.out). Between the two runs decls.py changed only how it prints a suggested line.
- **End to end**, this worktree's scripts/pre-push `--fast` in a real judge slot (logs/guard/e2e.sh, e2e/out-*). It runs after the new `stale --lean-lacks`, on main plus one planted file:
  - red, `writer_keeps_all` deleted: `decls: the parent's declarations are not cached … built in this slot and exported whole`, `build: ok`, `decls: undeclared deletion: Nanodregg.Ops.Units.writer_keeps_all …`, `decls: when it is the point, add the line: DELETES: Nanodregg.Ops.Units.writer_keeps_all`;
  - green, the theorem moved to the end: `decls: ok — 1 module(s) exported …`, `PRE-PUSH FAST GREEN`, 30 s for the whole fast judge;
  - stale, 0856ca3^'s Emit/Rust.lean: stale forwards both sides of the lack, and the verdict is `decls: stale declaration: Nanodregg.Emit.Rust.bounds` twice (main's copy, and the landing's copy).

**Price** (hbox, swarm-build, LEAN_NUM_THREADS=2, the plants' own wall times):
- The judge's step (the reach's export plus the diff): 8.5 s at 87 modules, 11.8 s at 217, 12.4–16.7 s at 218, 14.0 s at 278, 6.9 s at 4. In the end-to-end fast judge of one leaf module, the whole judge took 30 s, 21 s of it the source gates it already ran.
- Bootstrap (cache miss: the first landing after this one, or an exporter change): one parent build delta in the slot, plus a whole export of 15.7–19.1 s at 1.5–1.6 GB RSS (20,577 rows at f8d04ac). The kernel printer's statement text costs 3 s of that. `ppExpr` cost 37 s, so it is not used.
- Cache: about 2.0 MB per tree, gzipped; 64 kept, about 130 MB in `$common/nanodregg-decls`.
- The standing synthetic row: under 1 s, no build.

**What breaks.**
- Every landing that changes a `.lean` module runs `decls`.
- Every deleted declaration, removed module and change of a theorem's meaning is a message line. Each refusal prints the lines; E1 would have carried 66 and P7 111.
- `--no-build` with a changed `.lean` is refused.
- The first landing after this one bootstraps the parent's digest in its slot.
- scripts/commit and pre-push gain `--lean-lacks`, and `stale` gains it.
- Nothing re-emits; no wire or store format moves.
- A lander that relied on `--reverts C` for a `.lean` restatement no longer needs it: the restatement is a map line instead.

**Critique.**
- (a) The text detector still finds the `.lean` lack, so a lack whose replay CONFLICTS is "neither" and check 2 never sees it. Check 1 then catches a vanished or restated declaration. It does not catch a definition body reverted inside a conflicting merge. GATES-20b's (b) is unchanged for `.lean`.
- (b) Lines outside every declaration (`--` comments, `open`, `import`, `variable`) remain a text verdict. A moved theorem carrying a plain comment above it costs one `--reverts`.
- (c) The cache is trusted. A composed entry is exactly the parent's rows outside the reach plus the candidate's export, and nothing re-exports a cached tree whole to check that. A convergence-side check is a follow-up (cv task), and the cross-family read asked that it not enter the landing path.
- (d) Generated declarations are judged only through their owner, and a declaration without a range is not judged at all.
- (e) The statement digest is exact up to binder names. A restatement that only renames a bound variable is not a restatement. One that only changes `{x}` to `(x)` is.
- (f) The map lines can be long. They are the price, printed for pasting.

**Meta-critique.** The bias is shaping the rule to pass the cases at hand. GATES-20p did it: the regex was cut to P7's theorem, and it then refused E1 and the 10-20 trio. I did it too. My first map had an unchecked `RESTATES: OLD → NEW` so that a historical landing's map would be short, and a free pass for a removed module so that the fold's deletions would not need lines. Both were exactly the lies the guard exists to catch, and the cross-family read (R-0034) caught both. My plant set also kept S9 among the "false positives" after my own replay showed it never bit. The read made me label it for what it is.
