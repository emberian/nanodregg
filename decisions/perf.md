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
