> record copy of redregg/work/GATES-20-DESIGN.md, 2026-10-19; the lane logs stay in redregg

# GATES-20 design: traced read-sets select the runs and key the reuse

GATES-8, 2026-10-19. This is for ROOT to read before it is built. "Measured" means read from the hbox
artifacts named here. GATES-20a (the fail-open fix this measurement found) is a separate commit; this
design assumes it has landed.

## 1. Measured

**How it was measured.**
- `logs/gates8-trace.py` runs the tree's own `gates/runs.py --standing` on the standing tree at 1a6163b,
  with each verdict run's argv prefixed by `strace -f -qq --seccomp-bpf -e trace=%file,execve -e signal=none`.
  That gives 53 traces, controls included, in `logs/gates8-traces` (16 MB). Under tracing the run read
  `runs: ok (57 runs of 43 exes)`, the same verdict as without it. Every row stayed inside its 600 s
  deadline.
- `logs/gates8-replay2.py` replays main's last 150 first-parent landings. Each one is re-based over the
  landing just before it, the same pairs as gates6/7. Output: `logs/gates8-replay2.out`.

**Results.** The replay compares three things:

| | selected runs | re-run on a re-base | reuse |
|---|---|---|---|
| GATES-19 as landed (static key: every non-.lean path, every binary) | 2994 | ~90% | **10.4%** (gates7-reuse.py) |
| traced (this design) | **1672** (−44%) | 779 | **53.4%** |

- Why the traced re-runs happen: a .lean module in the closure of a binary the run executes, 512; a
  changed path whose bytes the run read, 154; the runner (runs.py, tree.py), 72; an added or deleted path
  the run stat'ed, 34; an add or delete in a directory the run listed, 7.
- The 512 closure re-runs are the floor for any key built on binary bytes.
- In 15 pairs the traced rule selects a row that GATES-19's rule did not. Those are the fail-opens that
  GATES-20a closes (store-plants, rows), plus standing benches the replay's GATES-19 side did not model.

**What the traces showed, beyond the numbers:**
- **A stat is not a read.** cargo's fingerprint check stats sources and does not open them.
  `cargo:devtools:workspace` stats 772 tree entries, decisions/ included. If only `openat` were traced,
  both would be missed. A stat depends on a path's existence, kind and mode, not its bytes: an edit to a
  stat'ed file does not move the run, but an add or a delete does.
- **A failed probe is a read of absence.** An `ENOENT` open means adding that file can change the run.
  The trace records the probe, and the key holds "absent".
- **Execs agree with what the code says.** Each row's traced execve set equals 20a's derived drives:
  `rows` runs lang-journey, `store-plants` runs host, and the resident rows run hosting-residents. No
  traced exec fell outside what 20a's reach and declared drives say.
- **Reads outside the tree.** 634K syscalls touched paths outside the tree, almost all toolchain:
  `~/.elan`, `~/.cargo`, `/usr`. 15 cargo rows touch `/tmp`, at 9 to 315 calls each (tempdirs). Neither
  static key covers those, and this design does not either (§5).

## 2. The design

**A trace.**
- Every run, in every judge and in standing, executes under the strace line above.
- The trace is reduced to a **read-set**:
  - C = the tree paths opened or exec'd (content);
  - M = the tree paths stat'ed, accessed or readlink'd (metadata);
  - L = the tree directories listed;
  - X = the binaries exec'd under `.lake/build/bin`.
- Each path is kept only once its result is known (found or ENOENT).
- `.lake/runs/` (the run's own scratch) and `.lake/cargo-target/` are excluded. The cargo target is
  derived: a source change reaches it only through C or M, which cargo stats.

**A traced key** is computed on any tree T from `ls-tree` alone, with nothing re-run:

  `H(row line, runner blobs, for p in C: blob(p) or ABSENT, for p in M: mode(p) or ABSENT,
     for d in L: sorted names in d, for b in X: bytes of b)`

**Validity, which is the soundness core.**
- A read-set recorded on tree S is **valid for** tree T iff `tracedkey(T) == tracedkey(S)`.
- Argument: every exe is deterministic given its inputs and seed (the no-wall-clock rule). If every byte,
  existence and listing the run consulted is the same, it consults the same things and reaches the same
  verdict. So it has the same read-set, and the key reproduces itself.
- A run that reads the clock or randomness for its verdict is already a defect.
- No valid read-set means the static rules: the data-path rule selects every row, and the key is the
  static one. That fallback is fail-closed.

**Selection.** For a candidate with parent B and changed paths P, a row is selected iff any of:
1. its 20a reach meets P's modules (the closure of every binary it may run, so X is never trusted
   narrower than reach); or
2. it has no read-set valid for B; or
3. its valid read-set meets P: p ∈ C, or p added, deleted or mode-changed with p ∈ M, or such a p sits in
   a directory in L.

**Reuse on a re-base.** GATES-19's rule stands: carry a verdict only under a byte-identical key. The
candidate's run key is the traced key whenever the lander's own C0 trace is valid on C1; otherwise it is
the static key. `rebase.py verify` re-computes it on C1 exactly as today. The trace used is the judge's
own: a run's trace on C0 is the read-set of the very verdict being carried.

**Where read-sets live.**
- Path: `<common>/nanodregg-traces/<row>/<tracedkey>.tsv`, written by the judge or standing that ran the
  row. They are content-addressed by their own key.
- Selection uses any stored read-set valid for B. The newest is cheapest to find: try the parent's own
  judge record first.

**Trust.** A forged or narrowed read-set selects too little. The defence is a check, not trust:
- **Re-trace consistency (standing).** Each standing run re-traces every row. If a stored read-set is
  valid for the standing tree, the fresh trace must equal it. A mismatch is RED `trace: <row> read X that
  its recorded read-set (key K) omits`.
- That one check catches a forged trace, a nondeterministic run, and an untraced input channel.
- It also checks 20a in the wild: a traced exec outside the row's reach or declared drives is RED.

## 3. Plants (each must read RED by name, plus controls)

1. **Content.** A run whose C holds world/x.ob, with P touching world/x.ob, must be selected; it re-runs
   on the re-base. Control: a P that touches only a path no row reads selects only by closure.
2. **Absence.** A row that probed `deploy/foo` (ENOENT): adding `deploy/foo` must select it.
3. **Listing.** A file added to a directory in L selects the row. Control: an edit to a file the row only
   stat'ed does not.
4. **No strace.** With strace made unavailable, every run carries the static key and the data-path rule
   selects every row.
5. **Unparsable trace.** The same: static.
6. **Stale read-set.** S differs from B on a path in C, so the read-set is invalid, so the static rules
   apply.
7. **Forged read-set.** A stored read-set with C narrowed by one path that the run does read: standing's
   re-trace check reads RED naming that path, and the selection plant built on it is caught there.
8. **Nondeterminism control.** Two traces of the same row on the same tree must be identical (measured
   first; if any row is not, it is listed and keeps the static key until fixed).

## 4. Costs

- **Measured:** 16 MB of traces per full row set; no row outside its deadline under seccomp-filtered
  strace; selection −44%; reuse from 10.4% to 53.4%.
- **Code:** a trace reducer (about 80 lines, the parsing in gates8-replay2.py), a traced-key function
  beside `rebase.compute`, a read-set store, and selection and verify reading them. Plus the re-trace
  check in standing.
- **Assumed by me:** that seccomp-filtered strace overhead stays small for the benches as they grow (no
  wall-clock claim made). That the 512 closure re-runs cannot be cut without a finer key than binary
  bytes; a per-module key would need a deterministic link map, which is not proposed.

## 5. Forks for ROOT

- **(F1) Trace in every judge, or in standing only?** I recommend every judge. Reuse needs the trace of
  the verdict being carried, and only C0's own run has it. Standing-only would make the re-base reuse
  rest on a read-set from another tree. That is sound only through the validity check, and the check
  would fail more often.
- **(F2) Reads outside the tree** (toolchain, `/tmp`).
  - Today neither key covers them, beyond the rustc and python versions.
  - Proposal: the reducer records a trace's outside-tree paths by prefix class.
  - A read under `/tmp` or `$HOME` outside the toolchain prefixes and outside a directory the run itself
    created is reported in standing as `outside: <row> <path>`. It is not RED until the census is clean,
    because 15 cargo rows touch /tmp today, and their tempdirs need sorting from real reads.
  - This is the one place the design stays an over-approximation by fiat. The other choice is to key
    every outside path's bytes, which would re-run on every toolchain file touch.

## 6. Build order

1. GATES-20a (landing now).
2. The reducer plus the traced key, as pure functions, with plants 1, 2, 3, 5 and 6 against real traces.
3. Tracing in runs.py (every run), the store, then selection and verify. Plants 4 and 7.
4. The standing re-trace check, plus plant 8 measured over two standings.
5. Land as one `gates:` commit under the old judge. Its message says what the new selection would have
   picked for its own landing.
