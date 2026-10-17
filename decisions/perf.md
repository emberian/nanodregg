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

**Status.** open (GATES: the standing hook + plant, ID-9).
