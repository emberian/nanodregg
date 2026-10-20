> record copy of redregg/work/GATES-19-DESIGN.md, 2026-10-18; the lane logs stay in redregg

# GATES-19 design: a FIFO landing queue, an incremental re-judge after a re-base, and no stale verdict

GATES-6, 2026-10-19. This is a design for ROOT to read before it is built. "Measured" means it was read from the hbox
logs: `logs/gates6-attempts.py` covers every scripts/commit log modified in the last 36 h.

## 1. What the logs say (measured)

- **Attempts per landing within one scripts/commit run** (CAS retries), over 216 distinct landings: 1 attempt: 153;
  2: 45; 3: 10; 4: 7; 5: 1. One run gave up after 5. **90 judges read GREEN and then lost the CAS**, so their work
  was thrown away. Worst cases: kernel8-land32 (5), host-commit12, protocol14-c2, host8-commit3, host6-c27,
  hosting-commit8, transport-commit-oneply and kernel19-land3 (4 each).
- **Between runs**, a lander that lost the CAS often cannot even retry. main changed one of the files it was
  editing, so the next run is refused `worktree behind main on F` and the edit has to be re-applied by hand. There
  were 19 such logs. The files: gates/runs.tsv 7, lakefile.lean 3, gates/waste.tsv 3, Host/Loop.lean 3,
  decisions/host.md 2, Ops/Units.lean 2, deploy/units/EXITS.md 2, and 8 single files.
- **HOST-52 (da0593e) took six runs.** The first was red on fmt. Then: behind on runs.tsv; 2 GREEN judges lost the
  CAS, then behind on host.md; 3 GREEN lost, then behind on host.md; 1 GREEN lost, then behind on runs.tsv and
  lakefile; and the sixth landed. **Seven GREEN judges were thrown away for one commit**, and five re-applications
  were done by hand. Every one of those losses came from a commit that touched none of HOST-52's Lean modules.

There are two separate costs. (a) Every loss re-runs the whole judge, although what landed in between rarely touches
the loser's inputs. (b) A shared file that both sides changed (runs.tsv, lakefile, waste.tsv, decisions/*.md) costs
a manual round trip, even when the edits are different lines.

## 2. The design

### 2a. A FIFO ticket queue: judging stays parallel, landing is in order

- When a lander enters scripts/commit it takes a ticket: `<common>/nanodregg-queue/<seq>.<pid>`. seq comes from a
  counter kept under one flock. The owner holds a flock on its own ticket file for as long as it lives, so a dead
  or killed lander's ticket is released by the kernel. There is no stale-ticket logic; this is the same reasoning
  as the slot locks.
- Judging stays in the four slots, in parallel, against the main the lander read.
- **Only the head of the queue may land.** The head is the lowest seq whose flock is still held. A lander whose
  judge has finished waits, with a deadline, until it is the head. A later ticket can never CAS ahead of an earlier
  one, so the earlier one cannot lose a race to it.
- The head lands only if main is still the base it judged against (the CAS stays, as the proof). If main moved,
  because a lander ahead of it landed, it does the re-base of 2b. It never re-runs the whole judge for that.
- Head-of-line blocking: a fast lander waits behind a slow judge that is ahead of it. That wait is bounded by the
  judge's own deadlines (the 30-minute slot wait and the run deadlines), and it is exactly what "not raced" means.
  The alternative, letting a later lander pass when its paths are disjoint, is the race ROOT ruled out, so it is
  not proposed.

### 2b. A re-base that re-runs only the units whose inputs changed

Notation:
- B0 = the base it judged against; C0 = the candidate it judged (GREEN);
- B1 = main now; D = diff(B0, B1), the paths that landed in between;
- P = its own paths; C1 = B1 + its changes = the candidate it would land.

1. **Shared files.** For a path in P ∩ D, run a 3-way `git merge-file` with base = B0's copy, ours = the lander's
   copy, theirs = B1's copy. A clean merge goes into C1 and counts as a changed input. A conflict refuses that file
   by name and prints the conflicting hunks, as `behind main` does today. The same merge replaces today's `behind
   main` refusal at entry, against the worktree's HEAD, so a stale worktree copy merges instead of refusing. It
   still never takes the stale copy whole, which is the 051a8cc incident that refusal was built for.
2. **A judged unit** is one of: the source gates (check.py), the build, the census, a generated-file check, a cargo
   step for a crate, or one run of runs.tsv (with its control). For each unit we recorded its **input key** when C0
   was judged (2c).
3. In C1, every unit that the parent B1 selects (the normal selection for P) is either:
   - **re-run**, if its input key in C1 differs from its key in C0. This is ROOT's rule: a re-base that changes
     any judged input re-judges that input. Or
   - **reused**, verdict and WASTE lines alike, if the key is byte-identical.
   A unit selected in C1 but not in C0 is new, so it runs.
4. **Always re-run, because they are cheap and tree-wide:** check.py (closure, refusals, size against B1, owners,
   tcb, vectors, paths), SIZE.md regenerated, and the generated checks. **The build always runs** (`lake build` is
   incremental in the slot, so it is a no-op for unchanged modules). It must exist so that binaries can be keyed.
5. Any red in a re-run unit sends the commit through the ordinary red path: the parent B1 is judged, and
   PRE-EXISTING is judged line by line. A lander never reuses a red. GATES-16 timeouts still mean NOT JUDGED.

### 2c. Input keys: a verdict is attached to its exact inputs, so a stale one cannot be read

A key is a SHA-256 over what the unit actually reads. Where we cannot list what it reads, we over-approximate:

| unit | key covers |
|---|---|
| a runs.tsv run | the runner (runs.py, tree.py), its runs.tsv row, waste.tsv, the exe binary's bytes and every binary it drives (`{host}`), and **every tree path that is neither a `.lean` source nor in the doc allow-list** (data files a run reads at run time: world/*.ob, deploy/, gates/*.tsv) |
| a cargo row | the same, plus the crate's tree and Cargo.lock |
| a cargo check/clippy/fmt step | the crate's tree, root Cargo.toml/lock, and the generated .rs |
| census | every .lean, plus Census/ and the allow tables |

- **The doc allow-list** holds the paths no unit reads at run time. It starts as `decisions/**` and nothing else.
  A gate checks that it holds: `rebase.py --check` fails if any tree file outside `decisions/` names a `decisions/`
  path as a string literal. Every other non-source path is in every run's key. So a landing that touches only
  decision prose reuses everything, and a landing that touches a .tsv or a data file re-runs every selected run.
- Keying on binary bytes rather than on the import closure is the conservative choice. A Lean rebuild that is not
  byte-reproducible only costs a re-run (a false mismatch), never a false reuse. Keying on bytes also catches a
  module whose bytes did not change but whose importer's inlining did.
- **The CAS stays the last word.** The commit has tree C1 and parent B1, and `update-ref main NEW B1` refuses
  unless main == B1. A verdict record, `<common>/nanodregg-verdicts/<C-tree>.tsv` (unit, key, verdict), is written
  by the judge. The lander's final step re-computes every key on C1 and refuses `stale verdict: <unit>` if a
  reused key does not match the C1 key. That makes the reuse itself checked rather than trusted.

### 2d. What stays exactly as it is

These are unchanged: pre-push's verdicts; a crash, ABSENT, or no verdict line is red; PRE-EXISTING per line; the
parent's gates with GATE-CHANGE; owners against the parent's OWNERS (re-run on C1, since GATES-18 reads the message
and the paths); a judge change lands under the old judge.

The re-base never relaxes a check. It only decides which byte-identical verdicts may be carried. Anything it cannot
key falls into the over-approximation, and the over-approximation re-runs.

## 3. Plants (built before landing; each must read RED by name, plus controls)

All of them go through `scripts/plant`, which gains `--rebase B0`: judge C0 = B0 + mutation, then re-base onto
main, all without landing.

1. **stale-verdict-cannot-land (end to end).** B0 = main~k, where main~k..main changes a module inside the import
   closure of an exe that the candidate's change also reaches, in a way that breaks the candidate's run. The
   mutation is a semantic conflict with no textual overlap. C0 must be GREEN on B0. After the re-base, that exe
   must be listed `re-run (key changed)` and read RED, with `PRE-PUSH RED`. If any build reused its verdict, the
   plant fails.
2. **forged reuse.** Tamper with the verdict record so that a re-run unit's key claims C0's key. The final step must
   refuse with `stale verdict: run X …`.
3. **data path re-runs.** D touches only a world/*.ob file. Every selected run must be re-run, by the
   over-approximation.
4. **doc-only reuses (control).** D touches only decisions/*.md. Every run must be reused, the commit lands, and the
   re-judge is check.py alone.
5. **merge conflict refused.** P and D change the same runs.tsv line. Expect `REFUSED — merge conflict in
   gates/runs.tsv` with the hunks. **Merge clean (control):** different lines; C1 holds both, and runs.tsv in D
   re-runs every selected run.
6. **FIFO.** Two plant judges, A with ticket 1 (slow: a sleeping exe row) and B with ticket 2 (fast). B's GREEN
   must wait: the log shows `queue: waiting for ticket 1`, and A lands first. Then **a dead head:** a judge holding
   ticket 1 that dies is skipped, because its flock is released.
7. **doc allow-list check.** A file outside `decisions/` that names a `decisions/` path makes `rebase.py --check`
   go red.

## 4. Costs and what I am unsure of

- **Measured:** 90 GREEN judges thrown away out of 216 landings; a full judge is minutes (build, then runs).
- **Assumed by me:** that most D's are disjoint from P's closure, so most re-bases reuse most runs. The replay in
  §5 measures that before anything is built.
- **A design fork for ROOT.** The 3-way merge of shared files changes `behind main` from a refusal into an
  automatic textual merge whose result is judged. I think it is right: it is what the refusal was protecting
  against, done correctly, and anything it gets semantically wrong is caught by the re-judge. But it is a change in
  what the tool does to a lander's edit without asking. The alternative is to keep refusing and only add the queue
  and the key reuse.
- Strict FIFO makes a 2-minute lander wait behind a 20-minute judge. Today that lander usually wins the race and the
  20-minute judge loses. The proposal deliberately reverses who pays.

## 5. Build order

1. Replay first. Over today's logs and git history, compute for each lost CAS what D was and what the re-base would
   have re-run, and quote the reuse rate. This tells us whether 2b is worth its code before any of it exists.
2. Write `gates/rebase.py` (keys, record, decision, the `--check` for the allow-list) as a pure function, with
   plants 2, 3, 4 and 7 run against real commits.
3. Change scripts/commit: the queue (2a), the merge (2b.1) and the re-base loop. scripts/plant gains `--rebase`.
   Then plants 1, 5 and 6.
4. Land it as one `gates:` commit under the old judge, saying what the new one would have done with HOST-52's six
   runs.

## 6. ROOT's rulings (10-19) and the replay

**Rulings.**
- (1) The 3-way merge: YES. The merged RESULT is judged, a conflict is refused by name and never resolved by the
  tool, and the keys and the final C1 re-check see the merged tree.
- (2) The queue is ordered by VERDICT READINESS with an AGE BOUND, not by arrival. The head is the lander whose
  verdict is green and whose keys are current on main. A lander still judging does not block a ready one. A ready
  lander that loses the head to a later one re-bases by key reuse. After TWO such displacements it becomes head
  regardless. The dead-head release by flock stays.
- 2c stands as written.
- An extra plant: a lander displaced twice is head on its third pass.

**Replay** (logs/gates6-reuse2.py, reuse3.py, reuse4.py). Each landing of main's last 150 first-parent commits was
re-based over the commit that landed just before it. The module graph is today's, so this approximates older pairs.
- 1288 selected runs in all.
- Static key (§2c as written: every non-.lean, non-decisions path is in every run's key): 736 re-run, **reuse 42.9%**.
  27 re-bases re-run nothing; 93 re-run everything. Why everything: a Lean module of D in every selected exe's
  closure 42; deploy/units or deploy/live 28; the runner (runs.py, lakefile, bar.sh, Host/c) 12; world/ 4; runs.tsv 2.
- No Lean source names `deploy/units` or `deploy/live`; `world/` is named by Hosting/Sim, Lang/Journey, Lang/Print
  and Kernel/Receive/Call. With the key taken from what a run actually opens (traced: §7) instead of every non-source
  path, deploy/ drops out: 533 re-run, **reuse 58.6%**, 32 re-run nothing, 72 everything (49 of those because of a
  Lean module in the closure, which no key can avoid).

**Predicted against measured** (the last 36 h: 216 landings; attempts 153/45/10/7/1, one gave up; 90 GREEN judges
thrown away; 19 behind-main runs):
- Full judges: 306 today (216 landings + 90 thrown away), **216 predicted**, one per landing; a red re-judges as today.
- Re-bases replace the 90 thrown-away judges. Each re-runs about 41–57% of a judge's runs (plus check.py, which takes
  seconds, and an incremental build). Re-base windows are short, so fewer of them will be displaced again; that part
  is assumed, not measured.
- The tail goes away: under the age bound no landing takes more than 3 passes. Today: 4 attempts ×7, 5 ×1, gave up ×1.
- Behind-main: 19 manual round trips become merges. Conflicts are expected rare: the files were runs.tsv,
  waste.tsv and lakefile rows, and host.md sections. The build measures that number.
- **Verdict: it pays.** It saves about 50 full-judge equivalents per 36 h on the judge side, removes every manual
  re-apply, and bounds the tail. The key-reuse half is moderate (43% static, 59% traced). Most of the win is the
  merge and the bound, so if code size has to be cut, the traced read-set is the piece to defer.

## 7. Traced read-sets (to reach the 59%)

- Each run executes under `strace -f -qq -e trace=openat,open,execve -o <slot>/trace/<unit>`.
- The key covers every tree path the run opened, plus the hash of the listing of every tree directory it opened, on
  top of the binary, runner and row parts.
- If there is no trace, it exits non-zero or it does not parse, the key falls back to the static over-approximation
  (fail closed).
- Soundness: the exes are deterministic given their inputs and seed. If every file a run opened is unchanged and its
  binary is unchanged, it opens the same files and reads the same bytes. A run that reads the clock or randomness
  for its verdict is already a defect under the no-wall-clock rule. Its scratch directory names (IO.rand) are under
  .lake/runs and are excluded.
- Plant: a run whose traced read-set includes world/x.ob, with D touching world/x.ob, must re-run; and the same with
  strace made unavailable must fall back to static and re-run.

## 8. Handoff

GATES-6 is near its context ceiling, so the build goes to a successor. GATES-7 starts from this file and
GATES-LOG `## GATES-6`. Build order is §5 steps 2–4, with §6's queue rule and §7's traced keys. Plants: §3 plus the
age-bound plant and §7's two.
