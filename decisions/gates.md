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
