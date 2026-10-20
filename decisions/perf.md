# decisions/perf.md — BUILD-PERF (format: decisions/README.md)

PERF is a measurement lane, not a decision layer (CHARTER row, ASSEMBLY-perf.md §4): it owns
`Bench/`, `scripts/bar.sh`, `gates/bar.tsv` and this file, and decides nothing a deployed path
runs. The entries below decide only HOW a number is taken and what it is allowed to be called.

## PERF-1 · THE BAR over sockets: real processes, one clock per `nd`, judged only when quiet (2026-10-17)

**Decision.** `scripts/bar.sh [--records N] [--record]` runs THE BAR through the deployed stack and
nothing else: two members, each with its own `nd` workspace, custody holding and `host follow`
Store, both confined by `nd-supervise`; ONE writer (`host serve`, confined) whose socket both
members' `host.sock` symlinks reach (one writer per Store; CLIENT-2's invocation, a1bd695). N
records = N/2 `nd create` per member, the two concurrently. Each `nd` invocation is timed by its
spawner from exec to exit, so a write's latency includes follow paging to the tip, custody's sign,
the writer's admit + `F_FULLFSYNC`, and follow's rendering. The writer is then stopped BY ITS PID
FILE (its confined child seen to exit, so the Store's lock is free), and the cold reopen is a new
supervisor + host process: spawn → the first reply to one `read` frame. Lines: `BAR write-p99-ms V
limit L`, `BAR reopen-ms V limit L`, p50/max, the segment bytes reopened, device, sha, load before
and after, `BAR verdict PASS | RED … | UNJUDGED …`. Limits are `gates/bar.tsv` `limit` rows (5000,
60000) × `BAR_LIMIT_SCALE`.
- A broken run (a failed or 60 s-silent `nd`, a writer that never binds or never answers the
  reopen, fewer records than asked) is RED by name, at any load.
- A limit is judged only when load1 < 2 before AND after; otherwise the verdict is UNJUDGED and
  names any limit it would have exceeded. Never PASS under load.
- The plant: `BAR_LIMIT_SCALE=0.0001` must be RED; under the plant the load rule is skipped,
  because the plant tests the comparator, not the machine. Ran 10-17 at a53bffc, load 120:
  `BAR verdict RED write-p99-ms 99.007 > 0.5; reopen-ms 23.906 > 6`.
- `--record` appends a `run` row (date, sha, device, load, both numbers, verdict). The history
  is a trend, never a ratchet (GATES-9: wall time is not a waste row).

**Alternatives.** (a) PROTOCOL's in-process bar (`rows --times 1000 bar`): it runs the deployed
loop but over the toy digest/FNV/toySign (`Protocol.Rows.Sim`) and the in-memory disk, so it sees
neither the sandbox, the sockets, Ed25519, nor fsync — and it is the reason the sandbox hang
(a53bffc) went unseen. (b) A purpose-built load client (P1's `p1-load`) — a Rust mirror of Lean
encodings: a twin (law 11), discarded. (c) A cross-process clock join for follow lag (P1's
`lag.py`): measures a design we do not have.

**Why.** The only number that answers THE BAR is the one the deployed processes produce. Timing
each `nd` from its spawner is one clock per sample with no cooperation from the code under test.

**CRITIQUE.** (1) Process spawn of `nd` (~ms) is inside every sample; a member running a resident
client would not pay it. That inflates write latency, in the safe direction. (2) Two members
closed-loop is not "two friends + hosted Hermes": no hosted resident verb exists, and the script
says so on a `BAR scope` line rather than pretending. (3) The reopen is a process-cold, OS-cache-
WARM reopen of the Store the run left — not the worst cut (tail at `tailMax`); the worst cut is a
Bench number (ID-8), and calling this one "the cold reopen" overstates it. `purge` needs root.
(4) Limits are 50–2000× above measured values on this Mac, so the gate mostly proves the pipeline
runs; the plant is what proves the comparator can fail. (5) `load1 < 2` is a Mac rule; on a
32-core Linux box it is either too strict or meaningless.

**META-CRITIQUE.** I lifted P1's run.sh lifecycle shape because the evaluator told me to, and the
"one clock per sample" argument may be a rationalisation for not instrumenting `nd`. I also chose
`create` as THE record because PROTOCOL's in-process row does: the journeys' records are
births and writes, and I did not check that a write-heavy mix behaves the same.

**Status.** superseded by PERF-2 (2026-10-18): the Linux path, a third actor, the standing row, and counts in place of a clock in the gate.

## PERF-2 · THE BAR runs on Linux, in standing, and gates counts, never a clock (2026-10-18)

**Decision.**
- **The Linux path runs.** `scripts/bar.sh` names the program to the sandbox (`--exec HOST`), because the Linux
  bwrap floor refuses a program outside every path. The Stores go in a fresh directory under `--root` (the gate
  passes its `{fresh}` scratch, which runs.py removes, GATES-6). A RAM file system there makes every fsync free,
  and bar.sh goes RED by name; hbox's `/tmp` is tmpfs. The custody workspaces, sockets and logs (KB) go in a
  fresh directory under `$HOME`. Custody refuses a key under any directory a group or other can write (sshd's
  StrictModes), and every path under /tank/dregg-build is 775, so bar.sh checks that chain and goes RED by name.
- **Three actors, and the workload uses each other's work.** The actors are two friends (`nd --init`, separate
  holding) and the hosted-resident STAND-IN (`nd --init-hosted`, one-record custody, driven by `nd` argv). The
  stand-in has no model and no `nd --stdio` wire; HOSTING-8's resident replaces it. N records are N write
  commands. First each actor creates one object and grants it `anyone mutate` (6 records). Then come N−6
  writes, round robin over the actors, each actor alternating its own object and the next actor's object
  through the grant.
  - `host check`'s `use=` must be exactly 3 (PROTOCOL-43, cv 01a14e19-a82f).
  - Every follow must be at the writer's step count, and the writer must hold each follow's head
    (`host check W --anchor`).
  - A write refused `stale` is re-run after one `nd sync`, at most 8 times, and counted.
- **Two modes.** Full (default) is concurrent: THE BAR's clock, release binaries, limits judged only when
  load1 < 2. `--standing` runs one command at a time on the dev profile, judges counts only, and reports the
  clock. In serial order every count is a function of N alone.
- **Counts, from the deployed binaries.** All count lines print as `BAR count …`; in `--standing` the pinned
  ones also print as `WASTE bar <metric> <ratio>`, which gates/waste.tsv pins (ceilings only fall).
  - The writer Store's `host check` STATUS, before and after: steps, records and seg_bytes per command. These
    are pinned.
  - The open fds each nd-supervise holds once every connection has closed (settled within 5 s), minus at
    start. These are pinned at 0. They were 2.200 and 0.733, a leak this bar found (cv 01a14ed9-8c59), until
    CLIENT-28 (cf79591) fixed it.
  - The writer's /proc io (read/write syscalls and bytes per command). These are reported, not pinned: they
    drift by one between identical runs.
  - The reopen's tail (steps and bytes past the base).
- **The standing row.** `gates/runs.tsv`: `script:scripts/bar.sh  --records 60 --standing --root {fresh}  BAR
  verdict PASS  --records 60 --standing --root {fresh} --harness-control`. runs.py drops ND_BIN from the row's
  environment, so bar.sh always builds the candidate's client (GATES-6). gates/runs.py gains the `script:` row kind (cross-layer, GATES-6).
  The row is selected on every judge and takes about 16 s.
- **The control (`--harness-control`).** Each of the three comparators gets one expectation nothing meets:
  limits 0 (GATES-6: any measured time is over, so the control cannot depend on the box's speed; it replaces the old BAR_LIMIT_SCALE plant, and a gate now runs it), use must be 4 of 3, and the follow must
  be one step past the writer.
  - The control reads RED naming `harness-control` only when all three fired.
  - If any one stays quiet, it prints the pass line, and runs.py refuses the row.
  - Each disabled comparator was mutation-proven on hbox ("a planted expectation stayed quiet: use / at-tip /
    limit").
- **gates/bar.tsv** keeps the two `limit` rows. Its `run` rows are the trend (date, sha, device, mode, N, load,
  clock numbers, use, steps/cmd, seg-bytes/cmd, writer fds/cmd, verdict), never a ratchet.

**Alternatives.**
- (a) Pin counts in gates/bar.tsv with bar.sh as their judge, as the brief said. Refused: that is a second
  ratchet beside waste.py, with its own raise rule and its own "pinned but unmeasured" rule. Law 1.
- (b) Gate the clock on a quiet box. Refused: Ember, no wall-clock benchmarks. A limit is a liveness deadline.
  Full mode still judges it, but only on a quiet box, and the standing row never does.
- (c) Make the standing row concurrent. Refused: group commit makes records and bytes per command depend on
  timing. The serial run gives exact counts, and ceilings pinned from it hold for the concurrent run too,
  because batching only lowers them.
- (d) Raise the soft fd limit to get through 1000. Refused: it hides the leak the bar found.

**Why.** The only number that answers THE BAR is one the deployed processes produce. On a box that is never
quiet, the part of it a gate can hold is the deterministic counts. The first day of running it found two
defects nothing else could have seen:
- nd-supervise leaks ~2 fds and a thread per connection, so at 1000 records connections are dropped silently
  (cv 01a14ed9-8c59, CLIENT-7).
- An honest stale re-run spends the refusal budget (KERNEL-19, PROTOCOL-13; work/PERF-LOG.md FINDING 2).

**CRITIQUE.**
- (1) The "resident" is a third member with hosted custody. It shares the CLI path, and no model chooses its
  writes.
- (2) One box, no ssh, a warm OS cache. These are C2's gaps, and they remain.
- (3) Hashes and verifies are not counted: the deployed path has no counter (PERF-3). Verifies per reopen are 0
  by design (HOST-22). A follow verifies every step it absorbs. The at-tip check already fixes that number to
  steps per command, so it has no row of its own: a second row would be a twin of steps-per-command.
- (4) seg-bytes-per-command depends on N (745.9 at 30, 757.7 at 60). It is pinned at the row's N, so a change
  to the workload re-pins it.
- (5) A fd row at 0 sees a leak only of fds held after the connections close. A supervisor that leaks while
  connections are open and frees on close is CLIENT-28's 71-fd bound's business, not this row's.

**META-CRITIQUE.**
- I kept bar.sh's one-file shape (python in a heredoc) because PERF owns only that path. A reader pays for that.
- I chose writes to make use=3 because writes need no package text. A Lang mirror of the counter package in
  bash would be a twin. So invokes (the counter's `add`) are not in THE BAR's mix.
- The serial standing row measures a workload no friend produces. It holds counts, and it says nothing about
  contention.

- **First runs at 1000 (b9cd50f, hbox, noisy box).** Two full runs, both UNJUDGED (load1 15–17 on 24 cpus):

  | run | write p50 / p99 / max (ms) | writer reopen (ms) | follow reopen (ms) | use | steps/cmd | records/cmd | stale re-runs |
  |---|---|---|---|---|---|---|---|
  | 1 | 55.9 / 136.6 / 182.2 | 110.1 | 110.6 | 3 | 1.015 | 0.603 | 15 |
  | 2 | 42.8 / 75.2 / 89.7 | 105.2 | 106.7 | 3 | 1.000 | 0.531 | 0 |

  Both are inside the limits (5000, 60000) by 37–570x. This is the baseline THE BAR v2 is measured against.
  Before cf79591, every 1000-record run was RED at 8–12 s.

**Status.** open (GATES-6 agreed 2026-10-18: the `script:` row kind, conditions 1–3 met).

## PERF-3 · PROPOSED to ROOT: deployed-parameter counts from THE BAR's own Store (swap 10, C4/C5) (2026-10-18)

**Decision (proposed).** A PERF tool exe, `bench-count STORE`, in `Bench/Count.lean`.
- It opens a Store the deployed host wrote: bar.sh's writer Store, kept for it by a `--keep-store` flag.
- It opens it read-only, through `Host.Check.openClean` (the open `check` uses).
- It re-folds every record of the segment with the deployed definitions (`Record.step Codec.Deployed.digestCodec
  (World.step E) (World.roots E)`). E is `Kernel.Sim.Gen.countingEnv X.env`: the deployed Env, with every
  trie-domain hash marked. Signature verifies are counted through the same mark on the verify the receive path
  calls.
- It prints `WASTE bar hashes-per-step`, `WASTE bar hashes-per-touched-cell` and `WASTE bar verifies-per-step`.
  These come from the deployed digest (cSHAKE256, 32 bytes), deployed Bounds and Ed25519, over THE BAR's
  workload. bar.sh's standing row runs it on the Store it just made.
- The host-sim/kernel-sim WASTE rows keep their toy-scale role. The same metric at deployed scale gets its own
  row. A toy row that disagrees by more than its stated factor is a finding, not a re-pin.

**Price.**
- Premises on landed theorems: none. No deployed module changes, and the exe imports Host.Deployed and
  Kernel.Sim.Gen; it is imported by nothing.
- Bytes: one lean_exe (~150 lines, Bench/ is PERF's), plus its runs.tsv row (`-`: run by bar.sh, which owns
  its verdict), plus ~1 s per judge.
- `countingEnv` moves from Sim-only to a second consumer. That is KERNEL-36's instrument used as written, not a
  copy.

**Alternatives.**
- (a) A counter inside the host process, printed in STATUS (`hashes=H verifies=V`). The deployed Env would need
  an IO effect inside a pure hash: dbgTrace or an unsafe ref, inside the TCB. Refused as priced: it weakens
  what the TCB is (CLAUDE.md pause item 2), to count something the replay counts exactly.
- (b) Thread a work tally through World.step. Every World.step theorem would gain a component. That is the
  premise spread minted-price-premises-not-only-cost warns about.
- (c) `perf stat --no-scale` instructions per command on the writer. Deterministic only to a few percent, and
  it counts the runtime, not the kernel's work. Useful as a report, not as a ceiling.

**CRITIQUE.**
- The replay is the deployed DEFINITIONS at deployed parameters, not the deployed PROCESS. A regression in the
  process's own path (a second fold on serve, re-hashing in the pager) is invisible to it. PERF-2's /proc and
  fd counts are what see that side.
- dbgTrace-to-stderr counting costs ~1 write per hash: fine for 60 records, slow at 1000.

**META-CRITIQUE.** I priced (a) out partly because I cannot land it (KERNEL/HOST own those paths). If ROOT
wants the process itself to count, the honest version is a HOST-owned `host check --count` that runs this same
replay inside the deployed binary. It would add no premise either. That is the real alternative to this one.

**Status.** ruled by ROOT 2026-10-18: the PERF exe, not `host check --count` (the deployed binary counts
nothing, law 3), on four conditions. Built as follows.
- **(i) The count is of the real workload.** `Record.step` checks every replayed record's stated roots, and
  the final World must equal the host's own reopen (`foldStep`) in steps, chain and roots digest. Anything
  else is `FAIL replay …`.
- **(ii) Pinned rows are ceilings that only fall, with the reason.** `bar audit-verifies-per-step` 1.000.
- **(iii) A toy Store is refused by name.** Before counting, `bench-count` writes SCRATCH/toy by the Sim's toy
  genesis and opens it the counting way. It reads `PLANT toy-store refused shapeMismatch`; if it opened, that
  would be `FAIL plant toy-store`.
- **(iv) `--harness-control`.** The replayed chain must equal the host's chain with one bit flipped, which
  reads `FAIL harness-control`. bar.sh's control passes it as its fourth comparator, mutation-proven
  ("stayed quiet: count").

One condition is NOT met as ruled: trie hashes per step are counted (15.1–16.0 over five runs at 60 records)
but are not pinned. The trie's shape follows the ids. The ids follow each signed call's bytes, and those
follow the run's random custody keys and genesis nonce, so the ratio moves by about 0.5 between identical
runs. A ceiling pinned at one run's value would go red on a later honest run.
Resolved by ROOT on the same day.
- **No seeded custody.** The deployed client has no mode that makes keys predictable (PROTOCOL-32's rule
  applied to key material).
- **The row.** `bar trie-hashes-per-step` is pinned as a DRAW-DEPENDENT gross-regression ceiling of 19.5:
  mean + 6 sd over 17 identical runs (14.37–16.96, mean 15.475, sd 0.663).
- **Why not tighter.** A max-observed ceiling (16.1, or 17.0) would read red on about one honest run in 18.
  kernel-sim's draw-dependent rows are fixed seeds; bar.sh draws fresh keys on every judge.
- **How it moves.** It is never re-pinned upward, and a run above it is red. It is lowered only by decision,
  or when KERNEL's draw-independent instrument (cv 01a14afe-7380, now noted with this consumer) replaces it.
- **Visibility.** The exact per-run count is still printed, so drift inside the ceiling stays visible.

## PERF-4 · C6: THE BAR seals a base at its midpoint; the reopen reads base + tail (2026-10-18)

**Decision.**
- At the midpoint of the writes every actor waits. The writer is stopped by its PID file (its confined child
  seen to exit, so the lock is free), `host seal W` runs (HOST-43: the writer's own open and checkpoint,
  inline; exit 0 and `sealed steps=S` are required), and the writer is started again.
- The final STATUS must have base_steps = S, else RED.
- The reopen then reads that base plus the second half's tail. `bar reopen-tail-bytes-per-command` (350.300
  at 60 records) is pinned. bench-count replays exactly that tail.
- HOST-13 agreed: no cadence knob. Cadence.deployed is the one table, and a bar-only cadence would be a
  second shape.

**Alternatives.**
- (a) A smaller sealMinBytes for the bar. Refused, as a second shape (law 1).
- (b) Run past 1 MiB so the writer seals on its own: about 1400 records. Refused: THE BAR is 1000, and
  cadence-dependent seal points move with every record-size change.
- (c) Seal the follow Stores too. Not done: the follower reopen measured is still a genesis base plus the
  whole tail.

**Why.** Every reopen THE BAR ran before this folded the whole history from genesis, so the open's
base-plus-tail path, the one law 5 is about, never ran in it.

**CRITIQUE.**
- This is not the worst cut. The tailMax cut (~18.9 MB since HOST-47's derived recordBytesMax, ~25k records
  of THE BAR's mix) is a Bench case that is still unmeasured.
- The stop and seal pause sits between two halves, not inside any timed command, so the clock never sees a
  seal.
- On tank (ZFS), serial writes measured p50 543 ms, against 32 ms on ext4/nvme: the device dominates, and
  bar.sh's device line says which one was used.

**META-CRITIQUE.** I chose the midpoint because it halves the tail visibly, not because a midpoint is
anyone's worst case.

**Status.** open.

## PERF-5 · THE BAR's reopen at the true worst cut: a sized, standing-only bench row (2026-10-18)

**Decision.** `bench-worstcut SCRATCH [--harness-control]` (Bench/WorstCut.lean) builds a Store on the
deployed path:
- `Receive.genesis` and `Receive.submit` under Host.Deployed.X, then `Host.genesis`, `openWriter`, and
  `commitBatch`, each frame committed only with `withinTail`'s proof;
- one founder births one data object, and `sealNow` seals a base over it;
- the tail is filled with one-slot writes, `recordTurnsMax` per record, until `withinTail` refuses the next
  frame. That is the most a reopen can ever fold past its base, in the smallest Turns, so the most steps.

The calls are signed by `Kernel.Sim.Deployed.params` (Ed25519 from a Sim tag's seed). That is a bench's
fixed identity, not a custody mode, so every count is a function of the code. The Store's random key moves
MAC bytes only.

Counted, each run required to reach the uncounted reopen's World:
- the reopen, `foldStep` under countingEnv with a counted verify (HOST-22's path);
- the follower re-derivation, `auditStep`.

The tail must fill at least 99 % of tailMax, else `FAIL not the worst cut`. That is a floor, so it is the
exe's own check; `withinTail` is the ceiling, by proof.

Measured (deterministic, two runs equal):
- the cut: 28,928 steps, 452 records, 18,850,208 bytes of tailMax 18,876,520 (0.999), over a 588-byte base;
- reopen: 20.374 trie hashes and 0.000 verifies per step;
- re-derivation: 20.374 trie hashes and 1.000 verifies per step;
- cost: 2 min 16 s and 87 MB on hbox.

It is a `standing:` row (GATES-17), never run by pre-push (ROOT: 4.5 min per judge with its control is too
much on shared slots). Its 4 WASTE rows (op `worstcut`) are gated in standing and never re-pinned upward.
The control requires the cut to exceed tailMax, which `withinTail` forbids, and reads
`FAIL harness-control`.

**Alternatives.**
- (a) A bar run of 25k records over sockets: about 17 minutes of socket work per measure, for counts the
  bench gives exactly.
- (b) The parked b616a8d drivers (wall-clock medians): refused by the no-wall-clock rule, and stale against
  today's API.
- (c) Big births to fill the tail in fewer steps: the fewest steps is the best case for the fold, not the
  worst.

**Why.** THE BAR's 60 s reopen is the one limit not checked at its worst case. Its counts at the cut are what
a deployed restart pays at most.

**CRITIQUE.**
- One object and one founder: the World is tiny (588 B base), so this is the worst TAIL. The worst World
  (`worldBytesMax`, 256 MiB base) is a different axis, and still unmeasured.
- 20.374 hashes per step is mostly the journal's window. It is pinned as measured, without a model of it.
- The tail ratio of 0.999 depends on frame sizes, so it is checked as a floor rather than pinned.

**META-CRITIQUE.** I picked writes to one object because they are the smallest Turn I could make. I did not
prove they are the most expensive per step for the fold. A tail of births grows the trie and may cost more
hashes per step.

**Status.** open.

## PERF-6 · The worst cut, measured in three tail shapes: the costliest is pinned, not assumed (2026-10-18)

**Decision.** `bench-worstcut SCRATCH` builds three deployed Stores, one per tail shape, each filled to the
same cut as PERF-5 (`withinTail` refuses the next frame; ≥ 99 % of tailMax or `FAIL not the worst cut`):
- `writes`: one-slot writes to one object (PERF-5's tail);
- `births`: one-slot data-object creates, so the World gains a cell per step;
- `retires`: `revoke`s, one grant tombstoned per step. The grants are born before the base: a revoke
  record is sampled on the World, and the grant count is re-derived from the sealed base's own tailMax
  until it covers the tail (sealing whenever the pre-base tail is full), so the base the tail folds onto
  holds every grant it retires.

Per shape, the reopen (`foldStep`) and the follower re-derivation (`auditStep`) are counted, and each must
reach the uncounted reopen's World. Each WASTE row pins the WORST shape (an exact cross-multiplied
comparison), and the bench prints all three with `WORSTCUT worst <metric> …`. A refusal before the cut (an
allowance or any other bound binding first) fails by name, and each shape prints the allowance it left, so
"tailMax binds first" is printed from the run rather than assumed.

The three Stores build at once, one dedicated task each. They share nothing but the process. The counts run
one at a time, because each captures the process's stderr. `--harness-control` runs the full path and
judges its impossible expectation (the cut exceeds tailMax) on the LAST shape counted (GATES-6). It reads
red only once every shape is built and the count loop has reached its end: `FAIL retires: harness-control …`.

Measured (deterministic: runs 2 and 3 identical in every count; hbox):

| shape | base world bytes | tailMax | tail bytes | steps | reopen hashes/step | audit hashes/step | verifies/step (reopen, audit) | allowance left |
|---|---|---|---|---|---|---|---|---|
| writes | 588 | 18,876,520 | 18,850,208 | 28,928 | 20.374 | 20.374 | 0.000, 1.000 | 116,339,575 |
| births | 588 | 18,876,520 | 18,847,752 | 33,088 | 33.031 | 33.031 | 0.000, 1.000 | 113,272,391 |
| retires | 5,764,172 (32,384 grants) | 19,661,454 | 19,631,808 | 32,256 | **33.959** | **33.959** | 0.000, 1.000 | 93,469,319 |

- tailMax binds first in every shape: the allowance (allowanceMax 134,217,728) is never close.
- The two trie-hash rows rise once, 20.374 → 33.959. This is the first measurement of these tails (ROOT
  2026-10-18: the one legitimate upward move, never again). Verifies are unchanged (0 and 1 in every shape).
- Cost: 4 min 39 s and 168 MB for the honest run, and 4 min 38 s and 164 MB for the control (load1 11–12 on
  24 cpus). Serially the honest run was 8 min 03 s. PERF-5's row was about 2 min 16 s per run.

**Alternatives.**
- (a) Three exes or three runs.tsv rows: three times the process start and the same total build, with no way
  to name the worst in one place.
- (b) Pin each shape in its own rows (12 rows): a regression in a cheaper shape would be pinned too. That is
  more coverage, but the bar is the worst a restart pays, and each shape's figure is printed beside the row.
- (c) Serial builds: 8 min instead of 4.5 min of standing, for nothing.

**Why.** PERF-5's META-CRITIQUE: writes were the smallest Turn, never shown to be the costliest per step. They
are not. A trie that grows (births), or that is already larger and is trimmed (retires), costs about 13 more
hashes per step.

**CRITIQUE.**
- Trie hashes per step follow the World's size (the depth of the cells trie). Retires measure 33.959 over a
  32,384-cell base sized to exactly what the tail retires. A base with more cells would cost more per step in
  every shape. So this is the worst over shapes at the smallest World each shape needs, not the worst over
  Worlds. The worst-World axis (a base at allowance exhaustion) is next, and it compounds this one.
- Each shape is one kind of Turn. A tail that mixes them, or Turns touching several cells, is not measured;
  a one-cell Turn has the most steps per byte, which is why it was chosen.
- The concurrent build saves wall time on a shared box by using three cores at once.

**META-CRITIQUE.** "The worst of three" is still a choice of three. I chose the kernel's three cell acts
(write, birth, retire), and that is a reason. It is not a proof that no fourth shape (a row insert, a value
transfer touching two cells) costs more per step.

**Status.** open.

## PERF-7 · bar.sh measures only binaries that are this tree's, by lake's and cargo's own reports (2026-10-18, ROOT)

**Decision.** Before anything runs, bar.sh proves the four binaries it will measure are built from the tree it
names:
- **Lean.** The bin directory must be this tree's `.lake/build/bin`, either as ND_LEAN_BIN (which is how
  runs.py passes it) or built here. Any other directory is `RED binaries-foreign`. Then
  `lake build --no-build host bench-count` must succeed: lake's own trace check, which exits non-zero when
  a target would rebuild. Otherwise `RED binaries-stale`.
- **cargo.** After the build, `cargo build --message-format=json` must report nd and nd-supervise as
  `fresh`, at exactly the paths that run. Otherwise `RED binaries-stale`, naming which.
- **What it prints.** The build no longer goes to `/dev/null`: `BAR built lean: N targets rebuilt`, then
  `BAR binaries` with each binary's SHA-256 prefix, the tree's sha, and its count of dirty tracked paths.
  `--record` on a dirty tree is `RED dirty-tree`, because its sha would name another tree.
- **bench-count.** It marks each recorded refusal it re-judges and prints `COUNT kinds turns T refusals R`,
  so a verify count is read against its kinds and not inferred.

**Why.** PERF-1's 506 verifies over 502 steps on c18e028 most likely came from a bench-count not rebuilt
from that Kernel: the build output went to /dev/null, and the worktree held uncommitted edits. KERNEL-20
measured 503/503 and 510/510. That is the stale-binary class: a number from a binary other than the one
claimed.

**Plants (by hand, all at a18d6ea + this change):**
- a comment appended to Bench/Count.lean, with ND_LEAN_BIN set (no rebuild): `RED binaries-stale: lake
  reports host or bench-count out of date`;
- ND_LEAN_BIN an empty directory elsewhere: `RED binaries-foreign`;
- a comment appended to client/src/attempt.rs, with ND_BIN prebuilt: `RED binaries-stale: nd: not fresh;
  nd-supervise: not fresh`.
The standing form still reads PASS, and its control still fires all four expectations.

**Measured with it** (full mode, clean tree a18d6ea except this change; load1 14–57, so the clock is
UNJUDGED and only counts are read):
- `count steps 217 … verifies 217` with `kinds turns 198 refusals 19`;
- `205 … 205` with `198 + 7`.
So one verify per step, refusals included, and `bar audit-verifies-per-step` stays 1.000 with its text
corrected. Two runs at 800 and 1000 records ended `RED resident nd write exit 53: declined refusalBudget`.
That is PROTOCOL-13's open contention finding (cv 01a14edf-6f12), and on a box at load1 34–49 it is now
reached below 1000 records.

**CRITIQUE.**
- `--no-build` trusts lake's traces. A binary edited in place after a build, with the sources unchanged,
  passes. The SHA-256 line makes that visible, but nothing refuses it.
- The cargo check runs a second (no-op) build. When it is not a no-op, it rebuilds the binaries and then
  refuses, so a re-run would pass. That is right: the re-run measures the rebuilt binaries.

**META-CRITIQUE.** I assert freshness, not identity with the commit. A dirty tree's binaries are that dirty
tree's, which is why only `--record` refuses dirt.

**Status.** landed with this entry.

## PERF-8 · The worst World is the reader's bound: a synthetic base at worldBytesMax, scaled into standing (2026-10-18, ROOT)

**Decision.** `worldBytesMax` bounds what a base FILE may hold, whatever the genesis allowance. So the reopen's
worst World is an adversarially sized base, not an honest history (ROOT). `bench-worstworld` (Bench/WorstWorld.lean)
has two modes, both on the deployed path (`Host.genesis`'s seal and MAC, `openFollower`):
- `SCRATCH synthetic N` (standing, N = 200000): N tombstones, the smallest cell entry at 35 B, at hashed ids
  in the genesis trie. They are written as a Store's base and reopened, and the reopen must reach the
  written roots. The base decode is counted under countingEnv. WASTE `worstworld
  decode-trie-hashes-per-entry` 2.000 is scale-free, and the total derived at worldBytesMax is printed beside it.
- `SCRATCH honest [STATE_BYTES]` (by hand): births until `submit` refuses, then the final base's reopen and
  decode counted.

`--harness-control` (either mode) requires the decoded roots to equal the written roots with their first
byte flipped. A non-number argument gets the usage line and exit 2.

**Measured.**

| run | entries | base bytes | decode hashes (per entry) | reopen | build | RSS | load1 (24 cpus) |
|---|---|---|---|---|---|---|---|
| synthetic 200k (the row) | 200,002 | 7,000,416 | 400,003 (2.000) | 2.2 s | 13 s | 178 MB | 10.5–12 |
| **synthetic at 2^28 (by hand; past the derived bound since HOST-57, PERF-10)** | 7,669,002 | 268,415,416 (1.000) | 15,338,003 (2.000) | **120.7 s** | 13.8 min | 10.1 GB | 12–15 |
| honest, 16-byte births (by hand) | 204,288 births | 22,247,840 (0.083) | — | 2.3 s | 11 min | 547 MB | 10–14 |
| honest, 60 KB births (by hand) | 743 births | 44,702,268 (0.167) | — | 0.78 s | 27 s | 793 MB | ~11 |

- The 200k row derives 7,669,574 entries and 15,339,110 hashes at worldBytesMax. The by-hand run at
  7,669,000 entries measured 15,338,003.
- Both honest runs end `rejected overAllowance`. Turn.weight = logWeight + growth, so a create's bytes are
  paid three times (event, logged creates, growth), and the allowance (134,217,728) buys at most about a
  third of itself as World. Encoded/weight is 1.001.
- A reader-bound base reopens at 2× THE BAR's 60 s limit on this box. It goes to KERNEL-21 and HOST-14
  (KERNEL-55) as evidence for option B: worldBytesMax derived to the allowance-implied ~84–87 MB. By my
  estimate (not measured), that also meets the reopen limit, which needs below ~128 MiB of small entries
  here. Once the bound is set, the row text names it and the derived total is re-pinned there.
- The full 256 MiB run and the honest run stay by hand (ROOT): 60 minutes of standing would buy a number
  the scaled row already derives.

**Alternatives.**
- (a) The full run in standing: 18 min and 10 GB each.
- (b) An honest-history row only: it cannot reach the bound that the reader actually faces.
- (c) Tombstones at sequential ids, an adversarial trie shape: not measured. Hashed ids give the honest
  shape. Decode is 2 hashes per entry at both scales, so the shape seems not to matter for decode;
  this is an inference.

**CRITIQUE.**
- The row pins hashes, not time. The 120.7 s is a clock on a loaded box, reported and never gated.
- Decode is two hashes per entry, but the reopen's time is not all hashing: allocation and the trie
  build are uncounted.
- Tombstones are the smallest entry, but not the costliest per byte to decode if a live cell's decode
  does more work. Spent nullifiers (also 32 B ids) were not tried.

**META-CRITIQUE.** I first measured honest Worlds, because I read "worst World" as "worst history". ROOT's
reframing to the reader's bound came from my own numbers, but I did not draw it.

**Status.** open (re-pin at KERNEL-55's bound).

## PERF-9 · A fourth worst-cut shape: the deployed Bell queue's rows tail (2026-10-18, ROOT; LANG-58 96179fb)

**Decision.** `bench-worstcut` gains the `rows` shape. With LANG-58, THE BAR's resident round is row-only
Turns. A ring is 2 inserts; an answer is 1 insert and 1 retract; the owner's retire of an answered ring is
2 retracts. So a rows tail is now a deployed case. Its Store:
- has a second founder, the resident;
- installs the Bell from `world/resident/Bell.ob` (the file the journey and HOSTING read), creates a bell
  whose resident is the second founder, and grants it `answer` and `ring`, all in the first record;
- seals the base over that;
- fills the tail with ring, answer, retire cycles to the same ≥ 99 % cut. The cycles keep `pending` under
  its 64 and `rings` under its 1024 for the whole tail; a tail of rings alone would meet `relationFull` at
  64.
Each ring's key is its own signed notBefore and the ringer. The answer and the retire pin the rows they
consume, as `derivePins` would (Lang.Journey's `pinRow`). The control is judged on the last shape counted,
which is now `rows` (GATES-6's rule).

**Measured** (at 96179fb, hbox load1 8.5–12 on 24 cpus):

| shape | base world B | steps | reopen h/step | audit h/step | verifies (reopen, audit) |
|---|---|---|---|---|---|
| writes | 588 | 28,928 | 20.382 | 20.382 | 0, 1.000 |
| births | 588 | 33,088 | 33.036 | 33.036 | 0, 1.000 |
| retires | 5,764,172 | 32,256 | **33.938** | **33.938** | 0, 1.000 |
| rows | 26,670 | 16,128 | 28.804 | 28.804 | 0, 1.000 |

- Rows cost less per step than retires, so the worst is still retires and nothing rises.
- The kernel changes between 2d2189e and 96179fb moved retires 33.959 → 33.938 (writes 20.374 → 20.382,
  births 33.031 → 33.036). The two hash ceilings fall to the measured 33.938.
- A rows Turn is about 1.17 KB (16,128 steps in 18.8 MB), twice a write's, so the tail holds half the steps.
- Cost: 7 min 08 s and 170 MB for the honest run (four concurrent builds). The control costs the same.

**CRITIQUE.**
- One ringer and one bell. Two friends ringing concurrently, as v2 does, put two rings per round; that is
  the same Turn shape and not measured separately.
- Per-step hashes: rows (28.8) sit between writes and births. Per reopen, the rows tail does fewer hashes
  in total (464,558 against retires' 1,095,392), because its Turns are larger.

**META-CRITIQUE.** I added the shape because it is now deployed, not because I expected it to be the worst,
and it is not. The worst-cut rows now cover the three cell acts (write, birth, retire) and the row acts (insert,
retract). A value transfer, which touches two cells, enrol and install are not measured as tails.

**Status.** landed da63f5b.

## PERF-10 · The worst World at the derived bound; the worst cut after the shared empty digest (2026-10-20, PERF-3; HOST-57 359e9e8, KERNEL-22 16f3b9f, LANG-59 c100be5)

**Decision.** Three measures on main 359e9e8, each with its control, and the rows they move.
- `worstworld decode-trie-hashes-per-entry` stays 2.000. Its text names the bound HOST-57 derived:
  `worldBytesMax = worldBytesDerived = 91,914,346 B` (Host/Proofs/Size.lean `worldBytesDerived_eq`;
  `reached_size_le`: every World the deployed writer reaches encodes within it; open refuses a base file past
  `Log.frameMax` of `baseRecordMax` 91,914,458, `baseTooLarge`; 91,914,474 since HOST-64 eb7028d, two u64 fields in the base record). The derived total is re-pinned there.
- The two worst-cut hash ceilings fall 33.938 → 32.938.
- THE BAR's `bar trie-hashes-per-required` reads 1.000 on a clean standing run. Its four controls fire.

**Measured** (hbox, main 359e9e8, a clean tree, binaries the tree's; load1 12–18 on 24 cpus, so no clock
here is a number):

Worst World:

| run | entries | base bytes | decode hashes | reopen | total | RSS |
|---|---|---|---|---|---|---|
| synthetic 200000 (the row) | 200,002 | 7,000,418 | 400,003 (2.000) | 4.9 s | 40 s | 773 MB |
| synthetic 2626112 (by hand, at the bound) | 2,626,114 | 91,914,338 | 5,252,227 (2.000) | **56.3 s** | 5:36 | 2.9 GB |
| synthetic 2626113 (by hand, one past) | — | — | — | — | — | — |

- One tombstone past the bound is refused at the seal: `FAIL Host.genesis worldTooLarge`. The bound is exact
  at the writer, so the reader's `baseTooLarge` is reached only by a base the writer did not write.
- The 200k row derives 2,626,114 entries and 5,252,215 hashes at the bound. The at-bound run measured
  5,252,227. Decode is 2·entries − 1 exactly at all three sizes measured (200,002; 2,626,114; 7,669,002), so
  the proportional derivation reads 12 low.
- PERF-8's 256 MiB run (7,669,002 entries, reopen 120.7 s) was at the old literal 2^28. It is now a base PAST
  the bound: 2.9× the World the deployed reader accepts.
- The reopen at the bound took 56.3 s against THE BAR's 60 s, while hbox ran bench-worstcut beside it at
  load1 ~13. A quiet box should be well below that, but this was not measured here. The decode alone was
  40.7 s of it.

Worst cut (bench-worstcut, honest run 7:59, 751 MB):

| shape | base world B | steps | reopen h/step | audit h/step | verifies (reopen, audit) |
|---|---|---|---|---|---|
| writes | 591 | 28,928 | 19.382 | 19.382 | 0, 1.000 |
| births | 591 | 33,088 | 32.036 | 32.036 | 0, 1.000 |
| retires | 5,812,239 | 32,320 | **32.938** | **32.938** | 0, 1.000 |
| rows | 23,467 | 16,448 | 24.892 | 24.892 | 0, 1.000 |

- The three cell shapes fall by exactly 1.000 hash per step: 16f3b9f's `rootsOf` shares one empty digest,
  and these tails' refusals and rows roots are both empty. The rows tail is unchanged by it, since its rows
  root is never empty. Its 28.804 → 24.892 is LANG-59 (c100be5), as LANG-19 measured by hand; this run
  agrees with it. LANG-19's "the worst stays 33.938" predates 16f3b9f.
- Both hash ceilings fall 33.938 → 32.938. The verify rows stay 0.000 and 1.000.

THE BAR, standing form (`scripts/bar.sh --records 60 --standing`), clean tree at 359e9e8:
- PASS. bench-count: 27 steps past the base at step 33, trie-hashes 402, required 402, verifies 27, so
  `trie-hashes-per-required 1.000` and `audit-verifies-per-step 1.000`. Hashes per step were 14.889; that
  figure depends on the draw and is reported only. The other WASTE bar lines equal their rows.
- `--harness-control`: RED by name with all four planted expectations fired: limit (each clock against 0),
  use (3, want 4), at-tip (each follow at 60, want 61) and `bench-count harness-control`.
- The instrument (KERNEL-22, 3467955 / 16f3b9f, cv 01a14afe-7380): the denominator is the hashes the design
  requires for the tries the run built (`Kernel.Sim.Required.step` per step, plus `Required.emptyRoots` for
  the record's roots check). The numerator is the trie-domain hashes counted under `countingEnv`. A
  requirement refused, or a count below it, is `FAIL required`. Before 16f3b9f the excess was exactly one
  hash per step (World.roots' second empty digest), so the row read 1 + steps/required. It now reads 1.000,
  and one extra hash anywhere in a 60-record run reads 1.003 or more.

**Alternatives.**
- Derive the worstworld total as `dh + 2·(max − entries)`, which is exact here. Not taken: it states the
  per-entry marginal instead of measuring it, and the at-bound run already records the exact figure.
- Put the at-bound run in standing: 5.6 min and 2.9 GB, for a ratio the 40 s row already pins.

**CRITIQUE.**
- 56.3 s at the bound sits within 7 % of THE BAR's 60 s reopen limit on a loaded box. The limit belongs to a
  quiet box (v2), so this is a margin I could not measure, not a pass. If v2's cold-cache reopen at the bound
  is slower, the bound is the knob, and the derivation says what it would cost.
- The worst World is still tombstones at hashed ids. Live cells and spent nullifiers were not tried at the
  bound (PERF-8's critique stands).
- The two bench controls, re-run by hand at 359e9e8, fire by name. bench-worstworld: `FAIL harness-control: the decoded
  roots are not the planted ones`. bench-worstcut, on the last shape: `FAIL rows: harness-control: the cut fills 18815944
  of tailMax 18876520, and the control expects more than tailMax`. Both are controls, not tests of the bound itself.

**META-CRITIQUE.** LANG-19's message said the worst cut "still retires 33.938". I measured instead of
relaying it, and the ceiling moved under it. The same applies to every row text I quote from another layer:
it was true when measured, at that sha.

**Status.** landed with this entry.

## PERF-11 · The worst cut after the one-pass commit (2026-10-21, PERF-4; KERNEL-23 258c273)

**Decision.** KERNEL-23's 258c273 commits a turn's cells, births and nullifiers as one batch per trie on a
dirty overlay sealed once, so a path node two of the turn's keys pass through is hashed once. The four
worst-cut shapes were re-measured on it, with worstworld and THE BAR's standing form beside them.
- The two worst-cut hash ceilings fall 32.938 → 32.217 (retires is still the worst shape). The verify rows
  stay 0.000 and 1.000.
- `worstworld decode-trie-hashes-per-entry` stays 2.000. The genesis decode does not go through a turn's commit.
- `bar trie-hashes-per-required` stays 1.000 exact. KERNEL-23 re-derived Required with the kernel
  (`Required.batchReq`); this run is the measure on main.

**Measured** (hbox, main 258c273, a clean tree, binaries the tree's; the load is beside each clock, so no
clock here is a number):

Worst cut (bench-worstcut, honest run 11:14, 746 MB, load1 13.6 → 29.3; control 9:15):

| shape | steps | reopen h/step 359e9e8 → 258c273 | audit h/step | trie hashes (258c273) | verifies (reopen, audit) |
|---|---|---|---|---|---|
| writes | 28,928 | 19.382 → 18.661 | 18.661 | 539,816 | 0, 1.000 |
| births | 33,088 | 32.036 → 30.595 | 30.595 | 1,012,318 | 0, 1.000 |
| retires | 32,320 | 32.938 → **32.217** | **32.217** | 1,041,249 | 0, 1.000 |
| rows (base 23,647 B) | 16,448 | 24.892 → 23.516 | 23.516 | 386,789 | 0, 1.000 |

- Steps, records and tail bytes are the same as PERF-10's in every shape. The rows base grew 23,467 →
  23,647 B (the installed Bell; 359e9e8..258c273 holds 1e90c0b's package version byte and 7c09186's rows key
  encoding), so its allowance moves 540 B. The honest run and the control printed the same counts in every
  shape they both reached.
- Attribution: of the 31 commits in 359e9e8..258c273, 258c273 is the one that changes how many trie hashes a
  commit makes, and its own admission count fell the same way (61851 → 60448). I did not run 258c273^ to
  separate it. The rows shape also carries 7c09186's key change, so its −1.376 is not KERNEL-23's alone.
- Every shape falls. births (−1.441/step) and retires (−0.721) gain most: a birth adds a cell and a nullifier
  key, so the batch shares more path nodes.

Worst World: synthetic 200000 → 400,003 / 200,002 = 2.000 (18.7 s, load1 5.7 → 6.5). The derived total at
91,914,346 B is unchanged: 2,626,114 entries, 5,252,215 hashes.

THE BAR, standing form (`scripts/bar.sh --records 60 --standing`), clean tree at 258c273: PASS. bench-count:
27 steps past the base at step 33, trie-hashes 365, required 365, verifies 27 (402/402 at 359e9e8; KERNEL-23
measured 374/374 on its own run). Hashes per step were 13.519, which depends on the draw and is reported only.
Load1 7.7 → 8.1, write-p99 220 ms, reopen 12.3 ms. The writer's Store is now under `$HOME` on nvme0n1p4, not
tank, so these clocks are not comparable to PERF-10's.

Controls (all fire by name, at 258c273):
- bench-worstcut `--harness-control`: `FAIL rows: harness-control: the cut fills 18815944 of tailMax 18876520,
  and the control expects more than tailMax`.
- bench-worstworld `--harness-control`: `FAIL harness-control: the decoded roots are not the planted ones`.
- bar.sh `--harness-control`: RED by name with all four fired (limits 0; follow 60, want 61; use 3, want 4;
  `bench-count harness-control`).

**Alternatives.** Leave the ceiling at 32.938 as headroom. Not taken: a ceiling above the measured worst would
let a 0.7 hash/step regression in the deployed reopen go unseen. These counts are deterministic: seeded
identities, and the Store key moves only MAC bytes.

**CRITIQUE.** The worst cut is still the worst of four hand-chosen shapes. A mixed tail (births interleaved
with retires of the cells just born) was not tried, and the batch could share fewer nodes there than in any
pure shape. That could put the real worst above 32.217.

**META-CRITIQUE.** The brief named the before-numbers and said "re-measure". I took them from PERF-10's run
log and re-ran on main 258c273 instead of on the brief's text.

**Status.** landed with this entry.

## PERF-12 · The worst cut, one bench per shape: every judged run bounded under the deadline (2026-10-21, PERF-5, landed by PERF-6; GATES-9's benchtrace)

**Decision.** `bench-worstcut` is split into four exes, `bench-worstcut-writes`, `-births`, `-retires` and `-rows`,
each with its own standing row `standing:bench-worstcut-<shape>`. Each builds and counts only its own Store and
tail. The old exe, its row and Bench/WorstCutMain.lean are deleted.
- Bench/WorstCut.lean is the shared harness. It holds the build, the count, the controls and a `Shape` record.
  Bench/WorstCut<Shape>.lean gives one `Shape`, and Bench/WorstCut<Shape>Main.lean is the exe root, declaring
  only `main` (closure C7). A change to one shape's module selects that shape's row only, by the static closure rule (plant below). A change to the harness selects all four, and
  bench-worstworld, which imports it.
- Each row has its own `--harness-control`: the impossible expectation (more than tailMax) on its own shape,
  judged after its Store is built and both counted opens agree. All four fire by name. The honest run of the
  same binary, without the flag, passes.
- WASTE: each shape pins its own four rows, `worstcut-<shape> <metric>` (16 rows). The four existing `worstcut`
  rows stay as the worst-over-shapes ceilings. Each bench prints its value on both its own row and the shared
  row. gates/waste.py judges a row at the largest value the runs printed. So standing judges the worst of the
  four against 32.217, and a pre-push run of one selected shape judges that shape against it too. I chose this
  over a fifth row that reads the four. A row runs alone, so a reader row would need the four runs' outputs
  (runs.py has no cross-row input) or would re-run them (the cost this removes).
- The bench signer derives each member's Ed25519 key once (`Signer`): the scalar, the prefix and the public key.
  It then signs with one base multiplication instead of three (`P.pub` per call, plus `sign`'s own re-derived
  `pk`). The bytes are proven equal to `P.pub` and `P.sign` (`Signer.pk_eq`, `Signer.sign_eq`, in the proof-module
  Bench/Proofs/WorstCut.lean, closure C3). This is test tooling; nothing deployed signs.
- The host's uncounted reopen runs beside the counted opens. It marks nothing, and a follower open locks and
  writes nothing.
- Each bench prints `WORSTCUT <shape> wall ms (reported, never judged)`: build, reopen, counted reopen and
  re-derivation.

**Measured** (hbox, `SWARM_MEM_MAX=6G LEAN_NUM_THREADS=2 swarm-build`, the four running at once, binaries the
tree's). PERF-5 measured on main e86f237 plus this change (logs/perf5-*). PERF-6 rebased it onto main c8ebb06 and
re-ran the four once, honest then control (logs/perf6-*). The counts are deterministic and identical in both runs:
steps, records, tail bytes, hashes and verifies. Every clock has its load beside it and none is a number.

| shape | steps | trie hashes | h/step (reopen = audit) | verifies (reopen, audit) | honest wall (load1) | control wall (load1) | build / reopen / counted / re-derivation (s) |
|---|---|---|---|---|---|---|---|
| writes | 28,928 | 539,816 | 18.661 | 0, 1.000 | 123 s (23.4 → 19.7) | 236 s (18.4 → 31.2) | 80.6 / 6.7 / 6.7 / 35.3 |
| births | 33,088 | 1,012,318 | 30.595 | 0, 1.000 | 147 s (23.4 → 19.6) | 286 s (18.4 → 21.2) | 95.8 / 9.5 / 9.5 / 41.5 |
| retires | 32,320 | 1,041,249 | **32.217** | 0, 1.000 | 280 s (23.4 → 25.3) | 383 s (18.4 → 15.9) | 213.9 / 12.0 / 12.6 / 53.2 |
| rows | 16,448 | 342,925 | 20.849 | 0, 1.000 | 380 s (23.4 → 26.5) | 404 s (18.4 → 13.3) | 157.5 / 25.9 / 26.4 / 196.7 |

On c8ebb06 (PERF-6, logs/perf6-honest1-*, perf6-control1-*), the same counts. Clocks:

| shape | honest wall (load1) | control wall (load1) | build / reopen / counted / re-derivation (s) | max RSS |
|---|---|---|---|---|
| writes | 117 s (11.5 → 13.4) | 142 s (17.1 → 17.8) | 93.2 / 3.9 / 3.9 / 19.8 | 153 MB |
| births | 132 s (11.5 → 12.5) | 164 s (17.1 → 15.9) | 102.6 / 5.5 / 5.2 / 24.2 | 184 MB |
| retires | 232 s (11.5 → 13.9) | 273 s (17.1 → 13.7) | 187.0 / 11.8 / 11.4 / 33.5 | 191 MB |
| rows | 283 s (11.5 → 17.1) | 306 s (17.1 → 12.1) | 134.6 / 16.8 / 17.0 / 130.5 | 139 MB |

Every control fired by name (`FAIL <shape>: harness-control: the cut fills … of tailMax …, and the control expects
more than tailMax`), and every honest run read `BENCH-WORSTCUT <shape> PASS`.

- writes, births and retires are PERF-11's counts at 258c273, unchanged: steps, records, tail bytes and hashes.
  rows fell 23.516 → 20.849 (386,789 → 342,925 hashes) at KERNEL-23 R2 5e33878, where a turn's row and head writes
  are one batch. On c15487e it fell again, 20.849 → 20.182 (342,925 → 331,960 hashes; PERF-6, logs/perf6-honest2-*):
  in range c8ebb06..c15487e, c15487e (a retract joins the rows batch) is the commit that touches row retracts, not
  separated. Its rows are pinned at 20.182, and the worst ceilings stay 32.217 (retires). writes, births and retires
  are unchanged on c15487e. Clocks there (load1 11.0 → 13.1, honest only): 111 / 128 / 234 / 239 s; rows'
  re-derivation 106.2 s.
- RSS is under 190 MB per shape. The 746 MB was four Stores in one process.
- The signer is measured on build time only, at loads that differ (honest2 load1 18.0 → 30.0, honest3 23.4 → 26.5):
  writes 103.8 → 80.6 s, births 123.8 → 95.8, retires 281.4 → 213.9, rows 179.3 → 157.5.
- Profile (perf record -F 49, logs/perf5-prof-*): retires is Ed25519-bound (Fe.mul 25 %, with the allocator
  around it). rows is spread over the allocator, refcounts, Codec.Tree, Stream, Hash and Lang.Wire, and Ed25519
  is 5.6 %.

**Derived totals.**
- The longest judged unit was the whole bench: 7:08 honest and 11:14 under load (PERF-4). It is now rows:
  283-404 s at load1 11-27, 47-67 % of the 600 s deadline. Next are retires (232-383 s), births (132-286 s) and
  writes (117-236 s).
- rows is bounded by deployed work. 16,448 invokes are judged twice: once at admission (~8-9.6 ms/step in its
  build) and once in the re-derivation (~8-12 ms/step). The bench cannot remove either one.
- ROOT ruled (2026-10-21) that this is deployed cost, not bench cost. `packages-checked-per-call` is 1.000: every
  invoke re-checks the Bell package. A follower catching up on a worst rows tail spends 130-197 s in
  re-derivation alone, against THE BAR's 60 s follow limit. The fix is LANG's design: the package check cached per
  (package id, call) within a run. Filed for LANG as cv task 01a1558a-1644. PERF re-pins the rows clocks and
  `packages-checked-per-call` when it lands.
- Standing cost: runs.py runs rows one at a time, so the four rows (control plus honest) sum to about 2,240 s
  at this load. The old row was 16-20 min (one process with four build tasks). In four parallel slots the cost
  would be max(rows) ≈ 13 min. The parallel slots the brief assumed do not exist in runs.py. Standing's length is
  a cost, not a hole. ROOT ruled (2026-10-21): land the split with standing serial (about 37 min at load1 13-27,
  about 28 min at load1 11-17 on c8ebb06), and GATES-10 builds concurrent standing rows (GATES-20g) behind it,
  priced against the deadline: concurrent benches raise the load, and load is what pushes a row past it.
- A pre-push run of one shape's change costs that row's control plus honest, 4-13 min. A harness change, or
  any module in every bench's closure (Kernel, Host, Codec) when no traced read-set is valid, costs all four in
  sequence.

**Plants** (logs/perf5-plants.py, function-level over this tree's gates):
- Selection: changed `Bench/WorstCutWrites.lean` selects only `standing:bench-worstcut-writes`, and likewise
  for births, retires and rows. `Bench/WorstCut.lean` selects all four and bench-worstworld. `gates/waste.tsv` is
  a data path under the static rule and selects every row. Traced, it selects none: waste.tsv is the
  comparator, not a read. It waits for GATES-20e, which selects by the WASTE rows a read-set measured.
  Under that rule a raised `worstcut-<shape>` ceiling selects that shape's row alone, and a raised `worstcut`
  ceiling selects all four. GATES-20e landed at c8ebb06. These four rows have no read-set yet, so the first
  judge runs them by the static rule. The W selection is planted by GATES (logs/gates9-20e.*), not here.
  PERF-6 re-ran the plants below on c8ebb06 against its own runs (logs/perf6-plants.out): the same verdicts.
- The worst check: with births planted at 32.300 and its own ceiling raised to 32.300, the four runs' lines are
  RED `waste worstcut reopen-trie-hashes-per-step: measured 32.3 > ceiling 32.217`. Births' lines alone (a
  pre-push run of its row) are RED the same way. writes planted at 18.700 is RED against its own 18.661 while
  the worst stays under its ceiling. The real four runs' lines are ok, with nothing unpinned.
- A shape that stops running is RED in standing's full check: each of its four pinned rows reads `pinned …
  but nothing measured it`.

**Alternatives.**
- (a) Keep one exe and pass the shape as an argument. Not taken: the binary is one read-set input (X), so a
  change to one shape would re-run every shape.
- (b) Shorten the tails. Not taken: the cut must fill tailMax by definition.
- (c) Build the retires grants into a synthetic genesis base, as bench-worstworld does with tombstones. Not
  taken: the grant cells would be bytes the bench composes, not bytes admission produced, to save about 100 s
  on a row that is not the longest.

**CRITIQUE.**
- rows at half to two thirds of the deadline is still a row that can go UNREAD on a bad day. The split takes the
  margin from about 0 to about 1.5-2x, not to "well under". The rest is in the deployed invoke:
  `packages-checked-per-call` is 1.000, so every invoke re-checks the Bell package (LANG, cv 01a1558a-1644).
- The standing total got worse under the serial runner: about 37 min against 16-20. I traded that for a
  bounded per-run clock, because a run that times out is UNREAD and a long standing is only slow.

**META-CRITIQUE.**
- The brief said each shape takes about 2 min. Measured, that holds for writes and births only. I measured
  before I wrote the rows.
- The signer is a factorization of CODEC's `sign` in PERF's tree, held equal by two theorems. CODEC could
  expose `sign` in that shape itself, and then the copy goes.

**Status.** Landed with this entry.
