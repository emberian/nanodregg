> record copy of redregg/work/CYCLE-TIME-20261016.md, 2026-10-16; the lane logs stay in redregg

# CYCLE-TIME 2026-10-16: why one Mini iteration takes hours, and what to cut

Scholar: CYCLE-TIME (Claude, read-only). Tree: GitHub main **2c27b08b**, read from the detached worktree
`…/b3795e84-…/scratchpad/mini-main` (paths below are relative to it unless absolute). Nothing was built.
Tags: **[M]** measured from a log or transcript, **[D]** derived from code or arithmetic, **[A]** assumed by me
and not checked.

Sources and the short names used for them:
- **cv**: the lane transcripts of root b3795e84, mined by a sub-agent. Citations are `agent#record`. The scratch
  is in `…/scratchpad/cycle-cv/` (`desc/`, `tl/`, `agg.json`, `complaints.txt`).
- **hb**: hbox `/tank/dregg-build/pipeline` and `/tank/dregg-build/claude-lanes`, read-only, mined by a sub-agent.
  Fetched copies and `an.py` are in `…/scratchpad/cycle-hbox/`.
- **Mac logs**: `/Users/ember/dev/redregg/work/*-LOG.md`, FOLLIES-20261014.md, RETRO-20261008.md.
- **Import graph**: I parsed every `.lean` header with the repo's own `scripts/lean_imports.py`. The script is
  `…/scratchpad/graph2.py` and its output is `graph2.json`.
- **Patch-id census**: 160 non-merge commits since 10-12 that are reachable from `gh/lane/*`, `gh/main` and
  `gh/next` and not from 7dea0626 (`…/scratchpad/allc.tsv`, `pids.txt`).

---

## 0. The answer in five lines

1. **Waiting, not compiling.** 61% of 222 lane-hours sat in foreground wait loops. 83% sat in stretches of 5 min
   or more with no activity [M cv totals]. Lanes landed **0.86 commits per lane-hour** [M cv].
2. **The candidate builder throws the box's parallelism away.** `build-native-host.sh` runs **one Lean process
   at a time at 2 threads**, and in non-umbrella mode runs **one `lake build` process per module** (775 of
   them). It then compiles about 776 project C files at **-P 2** with no cache. A host step that compiles zero
   Lean modules still takes **895 s** [M hb `warm-7dea0626/native-out/build.log:12`]. About 634–661 s of a
   fully warm host build is per-module `lake` startup: 1 s × 775 [M hb `perf-fix/p3/cand-cand-B-host.log`].
3. **hbox runs with no shared Lean cache.** `--no-lake-shim` is set (docs/PIPELINE-HBOX.md:33,37). Every lane
   clone recompiles every module another lane already compiled from identical inputs. Two private lane trees
   have link count 1 on every olean, and one of them rebuilt 823 modules in **8,046 s** [M hb §8, §1].
4. **The import graph is a deep chain.** Host.Main's closure is 776 modules with depth 87. Its critical path is
   65k of 321k lines, so the most parallelism you can get is about 4.9× [D graph]. Kernel/Compiler hubs
   rebuild 400–930 modules per edit [D graph]. Lake's own parallelism is the cheap win, and the module system
   is the deeper one.
5. **Branch-per-lane makes umbrellas twice.** About 25 of about 68 umbrella-scale builds (**37%**) were
   duplicates after a rebase or re-merge [M cv]. At least 25 extra commit copies appear in the patch-id census
   [M]. Merge reds show up only at the integrator's umbrella, hours later: b5fd9ee1 took 917 s and failed on a
   `Loaded.mk` field-count conflict between two lanes that were each green alone (INTEGRATOR-LOG.md:105;
   RETRO-20261008.md:223 "3 of 3 lanes were green alone and red together").

---

## 1. The cycle, measured

### 1a. One lane's iteration (hbox loaded, load 17–60 on 24 threads)

| step | median | worst | source | burst4 idle (16c/32t, 187 GB) |
|---|---|---|---|---|
| edit, then check one file (`lake env lean` / lane-check) | seconds to minutes when imports are fresh. If an import is stale it becomes a slot-queued closure build. | "b3 never got a slot (1h37)" | TURN-LOG-LOG.md:92 | seconds [A] |
| targeted `lake build` of touched modules | 40–70 min slot wait plus build | e1 70 min, e2 1h20 waiting (ae091d02#499). The old slot queue cost about 4 h (#1023). | STATE-AT-LOG.md:145-146 [M] | no queue after FIFO 6×4 (ae091d02#1023) [M] |
| **umbrella** (`Minidregg +Host.Main:leanArts ObjectiveProofs`), runs that compiled something | **2,692 s (45 min)** (n=11) | 8,046 s (823 built). census-review 14,253 s, failed. | hb §1 [M] | cold full build **1,017 s** (BURST4-UP-LOG.md:8) [M] |
| slot wait before the umbrella | 40–76 min typical | **3h10** (FLOORS a43abb6a#1424), **2h51** (PERF-MEMO ae32fc1b#765), about 3 h (HYP a789f694#794) | cv [M]. At least 20 h stated in total. | about 0 after FIFO |
| candidate **host** | **about 1,906 s (32 min)**: median of 14 elapsed values, 1,040–4,856 s | 4,856 s (state-at). Zero-Lean floor 895 s. | hb §3 [M] | FLOORS candidate 60 min (cv). The burst4 publish chain was 490 s (INTEGRATOR-LOG.md:93). |
| candidate **consent** | 156 s (n=11) | 2,750 s | hb §3 [M] | – |
| candidate **rust** | about 270 s (263, 272, 300) | 300 s. A warm target dir takes 7 s (af9f469a). | hb §3, cv a90cef32#457 [M] | – |
| candidate pack | about 10 s | – | cv a90cef32#488 [M] | – |
| relaunch after a busy-seat refusal (rc 75) | 3–6 relaunches per lane on burst4 | HP-1 #1061–#1141, CODEC-SHAPES #1108–#1161 | cv [M] | – (fixed by 2c27b08b's seat wait) |
| lane **rows** (run serially by the lane harness) | 522–1,119 s. Journey 200–437 s. | growth about 55 min (ad14561a#827→#902). Its verdict follows load (PERF-FIX-LOG.md:127-129). | hb §4, cv [M] | – |
| merge gate (lane self-check, rarely run) | see 1b | – | – | – |
| push | seconds since 10-15, with a deploy key on hbox and burst4 | about 8 relays a day through the Mac before that (FOLLIES I8) | SAFETY-BLOCK.txt:4,6 | – |
| **rebase onto a moving `next`, then another umbrella** | one more umbrella, about 45 min plus wait | FLOORS u4 72 min plus u5 queued 3h10; PERF-MEMO 3 duplicates and **never measured** | cv patterns 1 [M] | – |

**One lane iteration on loaded hbox: about 2.5–6 h [D].** That is the sum of the medians above: targeted build
with wait (about 1 h), then umbrella with wait (about 1.5 h), then candidate (about 40 min), then rows (about
15 min). With a rebase in the cycle, add another umbrella and wait (37% of cases). This matches the measured
**0.86 commits per lane-hour** (cv; WIP commits included).

### 1b. The integrator's / landing cycle

| step | measured | source |
|---|---|---|
| merge the next train | minutes, plus conflicts in hot files: build-native-host.sh, merge-gate-checks.sh, TokenCensus/Table.lean, ClientConsentCore, `Loaded.mk` | INTEGRATOR-LOG.md:67,77,90,105 |
| integrator umbrella at threads=4 | 560 / 1,435 (red) / 1,649 / 2,692 / 2,814 / 3,527 / 3,606 (red) / 917 (red) s. A warm no-op is 77 s. | hb §1, `integrator-next/logs/chain-*.status` |
| fixture re-emit after a world-root change | umbrella red on Assurance.NativeAcceptedFixture only → build a candidate → `objective-native-acceptance.py` → umbrella again, 2,692 s | INTEGRATOR-LOG.md:55-56. Main stalled 77–83 min three times on fixtures (RETRO:81). |
| objective draft/pin | 199 s, and 4,052 s before follies(a) | hb `chain-c81ad0cb.status:3`, `chain-c3b667b4.status:13` |
| merge gate, serial | 2,992 / 4,845 / **5,271** s, and 17,456 s on a loaded box | hb §2. Wall equals the sum of checks. |
| merge gate, parallel (c955f6a9, on main) | **658 s** (built=0, load1 15, burst4), and about 31.5 min with built=550 | INTEGRATOR-LOG.md:84,97 (burst4 logs are gone with the box; not on hbox) |
| inside the gate: token-census | 1,437 / 1,840 / 2,123 s, and TIMEOUT at 7,200. This is AxiomCensusResearch (730–4,079) plus TokenCensus (622–1,065). | hb §2 |
| hyp-ledger | 633 / 1,576 / 1,882 s serial, 587 s at 4 jobs | hb §2, INTEGRATOR-LOG.md:28 |
| exe-roots (7,531 jobs) | 402–970 s | hb §2 |
| publish-artifacts | 655 / 728 / 1,074 / 1,087 s (host 352–617, consent 48–170, rust 138–279) | hb §3, FOLLIES §0/F5 |
| standing journey run (8 parallel) | 2,782 / 3,602 / 5,947 s. Growth (2,436 / 3,076 / 5,401 timeout) is the critical path. | hb §4 |
| **landing total** | **1 h 51 m / 2 h 46 m / 3 h 28 m** | FOLLIES §0, cv a0c38853 |

The landing work done inside one landing lane amounts to about three builds of umbrella size: the umbrella
replay, exe-roots at 7,531 jobs and token-census at 9,796 jobs. Publish then rebuilds the Host closure in a
fresh clone-warm. [D hb §7]

---

## 2. Dominant terms, derived from the code

### T1. The native builder serializes Lean, and its per-module loop costs about 11 min of overhead **[D, M]**
- `scripts/build-native-host.sh:333-336` accepts `MINIDREGG_LEAN_THREADS` of 1 or 2 and `MINIDREGG_NATIVE_JOBS`
  of 1 or 2, and nothing higher.
- **Umbrella mode** (`--umbrella`, used by publish-artifacts:104) builds a fake sysroot whose `bin/lean` takes
  **one** `flock` (`:1416-1417`) before it execs the real compiler with `-j $LEAN_NUM_THREADS` (`:1431`). Its
  manifest asserts `max_concurrent_real_lean=1` (`:1509`).
- The stated reason is the comment at `:1391-1394` ("Lake 5 has no scheduler-width field … no CLI jobs flag")
  and docs/DEVELOPING.md:149-151 ("`LEAN_NUM_THREADS` alone does not limit Lake's process fanout"). The bound
  dates from 01e64487, 09-26, "Bound native builds on Linux and macOS". It is a laptop-era guard against Lake
  starting one `lean` per ready module.
- **Non-umbrella mode**, which lanes use through `deploy/candidate/lane-build.sh:33-35` at THREADS=2, runs
  `lake build "+$module:leanArts"` **once per module in topological order** (`:1369`). Each call starts Lake,
  reloads the workspace and re-hashes the closure.
  - Measured floor: replayed modules log 0–1 s each, so a fully warm loop costs **634–661 s** (hb, perf-fix p3
    772 of 775 replayed). Every lane candidate pays it before any real compilation.
  - On top of that, real compiles run one at a time. state-at's loop summed to 4,423 s (hb §3).
- **C phase**: every project `.c` file (about 776) is compiled with `clang -O3` through
  `xargs -P "$native_jobs"` at 2 (`:1561`), with **no cache on main**. elapsed minus the Lean sum is
  **333–1,300 s** [M hb §3]. The zero-Lean warm build took 895 s, almost all of it C [M/D].
  a20cbc39 (content-keyed object cache, `MINIDREGG_NATIVE_OBJECT_CACHE`) exists on lane/v4-next and is
  **unlanded**. Its own message measures the cost: "449 s on 7ffd6524; 2,196 s for v3 af9f469a … where only
  Assurance data changed".
- What breaks at more threads or more processes: memory. The only recorded figure is lake-slot:8, "a closure
  build dies at 24G (the slice guards the box)". **No log records per-Lean-process RSS** (hb §6). That missing
  measurement is why the 1|2 cap has never been re-priced. The wrapper already wraps every Lean exec and could
  record maxrss for free.

### T2. hbox has no shared olean cache, and lanes on hbox rebuild each other's work **[M, D]**
- The cache machinery exists and is correct:
  - `lakefile.toml:7` sets `restoreAllArtifacts = true`.
  - `scripts/pipeline/lake-shim/lake:27-31` exports `LAKE_CACHE_DIR=/srv/lake-cache LAKE_ARTIFACT_CACHE=true`.
  - lake-cache-audit is the guard against the burst2-b "79 poisoned .c" incident (build-native-host.sh:1360-1366).
- hbox's box.env is written with **`--no-lake-shim`** (docs/PIPELINE-HBOX.md:33,37). The reason given is
  protocol 7 ("an installed-copy path waiting for someone to plant a file"), not a technical problem. So on hbox:
  - Base sharing is only `cp -al` from one warm base. warm-base, land-30a5009a and land-19e9fe30 share inodes
    with link count 5–6 [M hb §8].
  - Anything compiled after the base froze is compiled again by every lane that needs it: integrator-next and
    land-perffix4 are fully private (link count 1), and perffix4 rebuilt 823 modules in 8,046 s [M].
  - The SAFETY-BLOCK recipe (SAFETY-BLOCK.txt:1) clones lanes from `warm-7dea0626`, which had only the Host
    closure. Its verify probe compiled 533 umbrella modules (LAND-HBOX-LOG.md:6), and every lane cloned from it
    pays those 533 again [D].
- The burst boxes did run the shim, but burst4 was torn down 10-15 (INTEGRATOR-LOG.md:95).

### T3. Lake's parallelism is capped by slots, and slots sat behind starvation **[M]**
- `slots/with-lean-slot` on hbox gives 3 box-wide slots at THREADS=2 by default, first come first served, with a
  4 h deadline and no wait records [M hb §8]. SAFETY-BLOCK.txt:2 says 2 slots × THREADS=4.
- Before about 03:13 10-15, blocked waiters bound to lean-1.lock only (TURN-LOG-2 afdbf9a2#121: "the box runs
  effectively one queued umbrella at a time"). There was no priority (INTEGRATOR #543, FOLLIES I7).
- Polling winners starved older waiters (PERF-MEMO #765: "waited 2 h 51 min, while waiters started 5–20 min ago
  got slots").
- Meanwhile hbox's load was 40–60 on 24 CPUs with swap 7G of 7G full [M hb §8; INTEGRATOR #428]. Builds ran
  IO-bound: GUARDS-LOG.md:22 "ZFS iowait 67% … lean procs 8 s CPU in 33 min", HYP-INSTANCES-LOG.md:35
  "Selvage.lean umbrella took 7,052 s under IO pressure", CONSENT-MODEL-LOG.md:241 "27 min … at ~1% CPU". The
  box was oversubscribed by non-Lean work (rows, Rust, workloads) as much as by Lean [A: which processes, not
  censused].

### T4. Import fan-in: one edit rebuilds hundreds of modules, and the Host closure is a 87-deep chain **[D graph]**
- The tree has 1,623 `.lean` files and 586k lines.
- Closures:

| root | modules | lines |
|---|---|---|
| Minidregg | 1,306 | 540k |
| Deployed | 940 | 378k |
| Host.Main | 776 | 321k |
| ub.sh set | 992 | 384k |

- What each edit rebuilds, within the research umbrella (`graph2.py` reverse closures):

| edited module | modules rebuilt | inside Host.Main | proof/research only |
|---|---|---|---|
| Theory.IndexedProgram | 929 | 624 | 305 |
| Compiler.BabyBear | 826 | 571 | 255 |
| Theory.Sp800185Cshake256Fast | 781 | 585 | 196 |
| Compiler.CanonicalCellRegistry | 539 | 453 | 86 |
| Kernel.World | 516 | 436 | 80 |
| Compiler.DurableReceiverCore (PERF-FIX's file) | 497 | 424 | 73 |
| Kernel.ObjectiveActivity | 391 | 344 | 47 |
| Kernel.NativeHostReplay | 157 | 131 | 26 |
| Host.Json | 22 | – | – |
| Host.Main | 4 | – | – |

- **Consequence:** for the edits lanes actually make, **80–85% of the rebuild is inside the Host closure**.
  Moving proof modules out of the umbrella saves only 15–20% of an edit's rebuild. The big levers are
  parallelism (T1, T3), caching (T2) and not rebuilding dependents when only a proof or body changed (fix F7).
- The critical path of Host.Main is 87 modules and 65k lines: Host.Main (9,163) ← Host.Json (6,374) ← … ←
  Kernel.NativeHost (3,351) ← Kernel.NativeHostReplay (4,590) ← … ← Kernel.DeclaredResourceController (2,514) ←
  … ← Compiler.DurableReceiverCore (1,736) ← … ← Compiler.CanonicalCellRegistry (1,513). Total over critical
  path is about 4.9× for Host.Main, 5.8× for Deployed and 8.3× for Minidregg. One umbrella cannot use 24
  threads well by itself, so a box should run several builds at once, which is a memory question (T1).
- Selvage leaks into the "deployed" Host closure through two edges: `Compiler.Tower256CshakeMerkleController →
  Selvage.BinaryLookup` and `Compiler.AuthenticatedColumnPlan → Selvage.Commitment`. That puts 12 Selvage modules
  in Host.Main [D].
- **Unit tests run inside compilation.** There are 4,265 `#guard`, 4,136 `#assert_axioms`, 2,790 `by decide` and
  279 `native_decide` lines in deployed directories [D grep]. They re-run on every rebuild of their module.
  Kernel/World.lean has 97 `#guard` and Kernel/Job.lean has 91, and both are hub-adjacent. Job took 471 s
  (hb §6).

### T5. Heavy modules, named **[M hb §6, loaded box unless noted]**

| module | seconds | what it is |
|---|---|---|
| Kernel.PayEnrolProofs | **8,715** | 588 lines of `simp [Legs.writes, …planWrites, Loaded.writes …]` over concrete plans. Not in Host.Main, but in Deployed. |
| Kernel.PayEnrolV2Legs | **7,311** | in Host.Main |
| Kernel.PayEnrolV2Receiver | 480–1,889 | – |
| PayClaimDecision | 1,713 | – |
| PayEnrolReceiver | 401–877 | – |
| `Assurance` root (an import-only file, 130 imports) | **4,583 / 2,292 / 852** s, and killed at 2,979 s (deploy3 wrapper TSV L919) | An import-only module should take seconds; this is environment load under memory/IO pressure [D/A]. |
| `Selvage` root (150 imports) | 1,045–1,290 s | same pattern |
| Assurance.NativeAcceptedFixture | 573–886 s | a generated fixture; reds on every world-root change (INTEGRATOR-LOG.md:55) |
| EvmStage0NativeDeployment | 569–930 s | – |
| Compiler.DurableIndex | 884 s | – |
| Kernel.Job | 471 s | – |

Consent closure: NativeClientConsent 653, NativeThinConsent 347, DeployedMaterializerWitness 287,
MaterializerCardinality 279 s. Host loop: ObjectiveActivityJson 329, ApplicationShareIssueAuthoring 302,
CapacityJson 217 s.

The census-review lane put it this way: "the PayEnrol proof modules alone take about 2 h" (a6187405#780).

### T6. Ratchets scan everything on every gate **[M, D]**
- **token-census** (1,437–2,123 s) is a full research-umbrella build (AxiomCensusResearch, 730–4,079 s) plus
  six scans of every constant and 401 planted forgeries (FOLLIES F2). It re-elaborates everything even when
  TokenCensus.lean is unchanged.
- **hyp-ledger** is 8 elaborations over AxiomCensusResearch, 7 of them self-tests of an unchanged instrument
  (FOLLIES F3). FOLLIES (a), which runs the self-tests only on instrument change, is in v4 and unlanded
  (INTEGRATOR-LOG.md:78).
- **objective-proofs** scans all 600 modules' declarations every run (scripts/check-objective-proofs.sh:4-26).
  The content-addressed ledger landed (decisions file 4,524 lines on main, against 112,619 on 10-14), but the
  scan is still whole-tree.
- All three are functions of a module's built environment, so their per-module output can be keyed by the
  module's Lake trace hash and only changed modules rescanned [D].

### T7. The candidate is rebuilt per lane and per landing **[M, D]**
- publish-artifacts:71,94-105 re-clones (clone-warm) and re-runs host, consent, prime and rust even on a tree
  the gate just built (FOLLIES F5: host 352–617 s, consent 48–170 s, rust 138–279 s). F5's fix, "pack from the
  gate lane", is in v4 and unlanded.
- lane-build.sh already computes the compiled-input set (`compiled=(…)`, lane-build.sh:39-41). Nothing reuses a
  candidate across lanes or tips when that set's closure is unchanged (FOLLIES I9: a scripts-only merge rebuilds
  host+consent+rust, about 25 min).
- I3: build-native-host refuses an existing output dir, so every second candidate in a lane dies with rc 73
  until someone moves the dirs by hand. PERF-FIX did this 4 times.

### T8. Rust **[D]**
- Each role is its own `cargo build --release -j 4` (lane-build.sh:76-78), 14 sequential invocations, with
  `CARGO_INCREMENTAL=0` and a per-lane `CARGO_TARGET_DIR`.
- RUSTFLAGS embed the lane's absolute path (`--remap-path-prefix=$src=…`, lane-build.sh:71). Even the box's
  sccache (publish only, publish-artifacts:89) cannot hit across lanes, because sccache hashes RUSTFLAGS [A:
  sccache keys on the full argument list, which I believe is so].
- A warm per-tree target takes 7 s (af9f469a rust step), so Rust is a cold-target cost (about 270 s) and not a
  structural one.
- 20 crates in total: 13 workspace members plus 7 with their own lockfiles (Cargo.toml, `native/*/Cargo.lock`).

### T9. Fixture re-emits are a cycle through the candidate **[M]**
- Assurance.NativeAcceptedFixture can only be regenerated from built binaries. A world-root change makes it red
  at the umbrella, and fixing it takes candidate → acceptance run → umbrella again: c3b667b4 spent 3,606 s red,
  then a candidate, then 2,692 s (INTEGRATOR-LOG.md:55-56).
- The fixture's generator row `objective` is UNCONFIGURED on 4 of 4 standing runs (FOLLIES F8). So this
  happens by hand, in whichever lane trips it.

### T10. Coordination: branch-per-lane multiplies all of the above **[M]**
- About 68 umbrella launches, about 25 of them duplicates (cv). The patch-id census since 10-12 found **160
  distinct commits, 21 groups of identical patches holding 46 commits**, so at least 25 rebased or cherry-picked
  copies. This is a lower bound: a conflict-resolved rebase changes the patch-id.
- 29 of the 160 subjects are bookkeeping (re-pin, ledger, manifest, fixture, census). RETRO-20261008 row 6
  counted 108 of 330 commits. build-surfaces had 128 json commits and "65 re-pin … for the batch" since 10-01
  (FOLLIES F6).
- Semantic conflicts appear only when the integrator merges. Each costs an integrator umbrella of 917–3,606 s,
  then a fix, then another umbrella.
- The integrator itself rebuilt v2 and v4 each time the merge set changed. That accounts for 3 of its 6
  umbrellas, plus 1 of INTEGRATOR-2's 4 (cv).
- Hot shared files guarantee conflicts. Host/Main.lean has 9,163 lines. Generated pins (host-closure.pin,
  lean-build-surfaces.json, TokenCensus/Table.lean, objective manifests) are committed by every lane.

---

## 3. Fixes, ranked by minutes saved per cycle ÷ effort

| # | fix | saves per cycle | effort | ratio |
|---|---|---|---|---|
| F1 | lake cache ON on hbox | 30–120 min per lane umbrella | 1 line in box.env | highest |
| F2 | native builder: one parallel Lake call plus N seats | 11–60 min per candidate | about 40 lines in one script | very high |
| F3 | land a20cbc39 C object cache at -P N | 5–20 min per candidate | merge plus a box.env line | very high |
| F4 | continuous tip service and one shared main (§4) | 37% of umbrellas, plus integrator rounds, plus hours of rebase latency | protocol plus 2 scripts | very high |
| F5 | slot discipline: priority FIFO and memory-sized seats, hbox decongested | 40–190 min of waiting | small script | high |
| F6 | candidate reuse by compiled-input closure hash; pack from the gate tree | 15–40 min per landing or scripts-only merge | medium | high |
| F7 | `module` system and proof splitting on hub modules | 50–80% of rebuild per body-only edit [A] | large, incremental | high, needs a spike |
| F8 | incremental ratchets keyed by trace hash; self-tests on instrument change | 20–40 min per gate | medium | medium-high |
| F9 | heavy-proof surgery: PayEnrol, Job, fixture out of the gating lib | 2+ h of loaded-box CPU per cold umbrella | medium | medium |
| F10 | THREADS and seat tuning from measured RSS | sizes F2/F5 | tiny to measure | enabler |
| F11 | Rust: persistent per-tree target, one cargo call, fixed build root | about 4 min per cold candidate | small | medium |
| F12 | rows in parallel in lanes; growth off the critical path | 10–50 min per lane row run | small | medium |

### F1. Turn the shared Lake artifact cache on for hbox (and every box)
- **Mechanism:** Lake's own content-addressed cache. A module compiled once from identical inputs is
  hard-linked into every other lane's `.lake/build`. This is the "olean object cache" in its existing form:
  a20cbc39 extended content-addressing to `.o` files, and Lake already does it for `.olean`, `.ilean` and `.c`.
- **Evidence:**
  - The hbox lanes that did not share rebuilt 533 modules (warm-7dea0626 verify), 823 modules / 8,046 s
    (perffix4) and 516 modules / 923 s (perf-fix p4) [M hb].
  - Each lane umbrella after the first on a given tip should replay at 5–17 s, the gate replays [M hb §1].
  - A cache hit costs no more than a `cp -al` hard link [D].
- **Risk:** the poisoning class (a non-Lake compile writing under unchanged traces, burst2-b 79 `.c`). The guards
  are in place: build-native-host compiles through Lake (`:1360-1366`), and lake-shim runs lake-cache-audit
  before every fetch.
- **First step:** in hbox box.env, put `export LAKE_CACHE_DIR=/tank/dregg-build/pipeline/lake-cache
  LAKE_ARTIFACT_CACHE=true` directly, with no installed shim. This sidesteps the protocol-7 objection that
  produced `--no-lake-shim`. Better: change `box-env --no-lake-shim` to emit those two variables, and have
  `lane-check` and `lake-slot` call the TIP tree's own `scripts/pipeline/lake-cache-audit` before building.
  Re-make the hbox warm base at the current tip so its oleans seed the cache.

### F2. Native builder: one parallel `lake build` and N seats, instead of a 775-process loop at 1 Lean
- **Mechanism:**
  1. In non-umbrella mode, replace the per-module loop (`:1335-1380`) with one
     `lake build +Host.Main:leanArts` and the companion root's leanArts. The loop's per-module evidence (source
     and artifact hashes) is computed afterwards from the same files; the manifest code already does that for
     umbrella mode.
  2. Bound Lake's fanout with **N** seats, not 1: the fake-sysroot `bin/lean` takes the first free of N lock
     files, as `try_seat` already does for host seats (`:383-397`).
  3. Lift the 1|2 caps (`:335-336`) to a box.env value.
- **Evidence:**
  - The loop floor is 634–661 s of pure Lake startup per candidate [M hb], and a Lake replay of the same closure
    takes 5–17 s [M hb §1].
  - Real compiles in the loop run serially: state-at took 4,423 s of Lean, against a parallel Host closure with
    parallelism ≤4.9 [D].
  - The burst4 cold full build (1,306 modules) took 1,017 s with Lake parallel [M].
- **Risk:** memory, which is unmeasured (F10). The cgroup (`swarm-build`, MemoryMax) is the hard bound and N
  seats the soft one; the fake sysroot already guarantees the seat stays held while the compiler runs.
- **First step:** `scripts/build-native-host.sh`:
  - the wrapper heredoc (`:1407-1440`) flocks `${MINIDREGG_LEAN_LOCK}.$k` for the first free k ≤
    `$MINIDREGG_LEAN_PARALLEL`;
  - the `case` at `:335-336` accepts 1–32;
  - the non-umbrella loop becomes the umbrella path with `--umbrella-target Host.Main`, which already exists.
  - Keep `max_concurrent_real_lean=N` in the manifest.

### F3. Land the C object cache (a20cbc39) and compile C at `-P nproc`
- **Mechanism:** content-keyed `.o` reuse. Most candidates change a handful of modules' C.
- **Evidence:**
  - The C phase is 333–1,300 s per host build. A zero-Lean host build takes 895 s, almost all of it C [M hb §3].
  - a20cbc39 measured a hit as byte-identical to a miss.
  - At -P 2 on a 24–32 thread box, a cold C phase alone could run about 8× faster [D].
- **Risk:** a stale-cache oddity. a20cbc39's own note says to "suspect it first", and check-reproducible runs
  nightly without the cache.
- **First step:** merge lane/v4-next's a20cbc39 into main. Set `MINIDREGG_NATIVE_OBJECT_CACHE` in hbox and burst
  box.env. Raise `native_jobs` with F2's cap change.

### F4. A continuous tip service and one shared main (full design in §4)
- **Mechanism:** the tip is built once, continuously, and every lane builds on that. Lanes do not each rebase,
  re-umbrella and wait for an integrator.
- **Evidence:**
  - 37% duplicate umbrellas [M cv].
  - At least 25 rebased copies since 10-12 [M patch-id].
  - Integrator rebuilds at 917–3,606 s each [M].
  - Landing wall of 1 h 51 m to 3 h 28 m spent per batch [M].
- **Risk:** see §4. A bad commit reaches everyone's next build.
- **First step:** the protocol paragraph in §4e, plus `scripts/pipeline/tip-service` (a loop around
  run-gate-burst on `main`).

### F5. Slots: priority FIFO, memory-sized, and decongest hbox
- **Mechanism:**
  - with-lean-slot becomes a real ticket queue: a monotone ticket file, served in ticket order. The service and
    integrator get a reserved slot (the `build-slot-mk` idea, slot-mk.sh).
  - The slot count is sized from measured RSS (F10), not set at 2 or 3.
  - Rows, Rust and workloads get their own budget (a second cgroup) so Lean does not run at 1% CPU behind them.
- **Evidence:** at least 20 h of stated slot waits, with 3h10 and 2h51 cases where newer waiters won [M cv], and
  Lean at 1% CPU or 8 s CPU in 33 min under iowait [M Mac logs].
- **Risk:** a reserved slot idles while lanes wait. Let lanes borrow it while the service is idle.
- **First step:** rewrite `/tank/dregg-build/pipeline/slots/with-lean-slot` as a tracked repo script
  (`scripts/pipeline/with-lean-slot`, tip-tree copy) with tickets and a waiters directory. Record each wait as
  `ticket, enqueued, granted, released` lines so the next scholar can measure it.

### F6. Candidate reuse by closure hash; pack from the gate tree
- **Mechanism:**
  - Key a candidate by `sha256(git ls-tree HEAD -- <lane-build compiled globs>)` plus the toolchains.
  - If the key equals an existing READY set's key, the "candidate" is a symlink to it and the rows run on it
    (FOLLIES I9).
  - publish-artifacts packs from the gated lane tree when the gate says built=0 (FOLLIES F5, v4 unlanded).
  - Commit-stamped output dirs replace the rc 73 refusal (FOLLIES I3).
- **Evidence:**
  - Publish rebuild is 655–1,087 s per landing, 352–617 s of it Lean host [M].
  - A scripts-only merge rebuilds about 25 min [M FOLLIES I9].
  - Lanes moved artifacts aside by hand 4 times or more (PERF-FIX-LOG.md:61,79,121,164).
- **Risk:** a compiled input missing from the globs. Mitigate by having the key list be `lane-build.sh`'s
  `compiled` array, the one already trusted for `unchanged_since`.
- **First step:** in `deploy/candidate/lane-build.sh`, add a `key` step that prints that hash. publish-artifacts
  then looks up `$ARTIFACT_ROOT/by-key/<hash>` before building.

### F7. Import-graph surgery: stop dependents rebuilding on body-only edits; split the hubs
- **Mechanism:**
  - Lean's module system (`module` header; definitions without `@[expose]` keep bodies out of the public
    interface). 49 files already use it [D grep].
  - The [A] premise: with Lake 4.30, a dependent is not rebuilt when only private parts change. **I have not
    checked this. The first step is the spike that checks it.**
  - Independently of the module system:
    1. Split Host.Main (9,163 lines) and Host.Json (6,374), the critical-path tail.
    2. Cut the two Selvage edges out of the Host closure.
    3. Move proof-only files out of the import path of executables, so that Kernel.PayEnrolProofs-style theorem
       modules are leaves.
- **Evidence:**
  - Typical lane edits rebuild 400–520 modules, 80–85% of them in Host.Main [D graph].
  - DurableReceiverCore (PERF-FIX's file) rebuilds 497 modules and 162k lines.
- **Risk:** `@[expose]` audit work. The objective ledger's content closures read bodies, and with the module
  system those live in the private olean, so check that the scanner still sees them.
- **First step (spike, one hour on an idle box):**
  1. Add `module` to Compiler/DurableReceiverCore.lean and one importer.
  2. Change a proof body.
  3. Run `lake build Host.Main --no-build` and count "out-of-date".
  If it is 1, convert the hubs in reverse-closure order (the hub table in §2 T4).

### F8. Incremental ratchets
- **Mechanism:**
  - The objective scan, the token census and the hyp-ledger real run emit rows per module. Cache each module's
    rows keyed by its `.lake/build/lib/lean/<M>.trace` hash, which already covers its whole import closure, and
    rescan only modules whose trace changed.
  - Plants and self-tests run only when the instrument's files change (FOLLIES (a), v4).
  - TokenCensus's AxiomCensusResearch build disappears once the umbrella builds it, or once it is in the shared
    cache (F1).
- **Evidence:** token-census 1,437–2,123 s, hyp-ledger 633–1,882 s, objective 84–339 s per gate [M hb §2]. A
    typical edit changes the traces of about 500 of 1,300 modules [D], so this saves about 60% of scan time on
    top of the skipped self-tests.
- **Risk:** an instrument that reads cross-module facts (the token census's "minted only in its home module").
  Key such a module's rows by the closure of every module that could mint, or keep that check whole-tree. It is
  the cheap part.
- **First step:** land v4's follies(a). Then in `scripts/objective-manifest.py`, store
  `build-logs/objective/cache/<trace-hash>.tsv` and skip the scan for hits.

### F9. Heavy-proof surgery
- **Mechanism:**
  - Profile Kernel.PayEnrolProofs and PayEnrolV2Legs (`set_option profiler true` in `lake env lean`).
  - Replace the `simp [planWrites, Loaded.writes …]` unfoldings with stated equation lemmas on the concrete plan.
    These are whnf through big concrete definitions, the reduction-bomb class.
  - Move Assurance.NativeAcceptedFixture into its own lib, built after the candidate by the tip service (F4), so
    a world-root change is not an umbrella red.
  - Convert `#guard` in the hub-adjacent Kernel/World.lean (97) and Kernel/Job.lean (91) per GUARD-DISCIPLINE
    into named theorems in a sibling test module, so the hub's dependents do not pay for them.
- **Evidence:** PayEnrolProofs 8,715 s and PayEnrolV2Legs 7,311 s on a loaded box; fixture 573–886 s per
  umbrella plus a candidate round per world-root change [M].
- **Risk:** none to soundness, since only proof terms change. Do not convert to `native_decide`: that trades
  time for trust (CLAUDE.md).
- **First step:** a 20-minute profile of PayEnrolProofs on an idle box, `lake env lean -Dprofiler=true
  Kernel/PayEnrolProofs.lean`.

### F10. Measure RSS, then size THREADS and seats
- **Mechanism:**
  - In the fake-sysroot wrapper (`:1431`), run the real lean under `/usr/bin/time -f '%M'`, append maxrss to the
    wrapper TSV, and do the same in lake-slot.
  - Then set `seats = floor(cgroup_mem / p95_rss)` and `threads = nproc / seats`.
- **Evidence:** no RSS anywhere on hbox (hb §6). The only bound in the record is "a closure build dies at 24G"
  (lake-slot:8). burst4 ran 6×4 within 158G (BURST4-UP-LOG.md:4,7) [M].
- **First step:** a 3-line edit to the wrapper heredoc.

### F11. Rust
- **Mechanism:**
  - One persistent target dir per tree, never deleted between candidates (7 s warm, M).
  - One `cargo build --release --bins` per workspace instead of 14 sequential calls.
  - Build candidates under a fixed path per box (`/srv/candidate-root` bind-mounted to the lane), so RUSTFLAGS,
    and therefore sccache keys, match across lanes.
  - `-j nproc` under the cgroup.
- **Evidence:** rust 263–300 s cold versus 7 s warm [M].
- **Risk:** I5 (count differences from a target shared across trees). Keep it one target per tree, as here.
- **First step:** in lane-build.sh's rust step (`:76-80`), loop per workspace rather than per role.

### F12. Rows
- **Mechanism:**
  - Lane harness rows (journey, call, send, objectrecord, seats, fleetsign) run in parallel. The standing
    runner already does (journey-runner:186-192).
  - Growth and the births soak move to nightly (FOLLIES F1). Required rows finish in minutes.
- **Evidence:** lane rows serial at 522–1,119 s, with journey alone 251–437 s [M hb §4]. Growth is 2,436–5,401 s
  on the landing critical path [M].
- **First step:** the integrator's `rows-*.sh` uses `journey-runner --rows journey,call,…` instead of a serial
  loop.

**What the cycle becomes [D, idle box, after F1–F6].**

| step | time |
|---|---|
| check one file | seconds |
| import-closure build of an edit | cache hits plus about 500 modules over 4.9× parallelism: about 5–10 min cold, about 0 for modules others compiled |
| umbrella | 10–17 min for the 1,017 s cold worst case, about 1 min warm |
| candidate | about 2–4 min: Lake replay plus cached C plus warm cargo |
| rows | about 7 min (parallel; journey 200–437 s) |

Total: about **25–40 min per iteration, against 2.5–6 h**.

---

## 4. One shared tree

### 4a. Shape
- **Per box:** one bare shared repo, `/srv/git/minidregg.git` (burst) or the hbox mirror, with remote `github`.
  One **shared Lake artifact cache** (F1), one object cache (F3), one sccache.
- **Per lane:** a `git worktree` (or a cheap `clone --shared`) on **`main`**, not on a branch. Its `.lake/build`
  is materialized by Lake from the shared cache (restoreAllArtifacts hard links), so "warming" a lane is a
  replay. The cp -al and unlink scripts are no longer needed because Lake never writes through a cache link:
  it replaces outputs (build-native-host.sh:1366 states this).
- **Why not one working directory for everyone:** two `lake build`s in one workspace write `.trace` and `.ilean`
  in place and must not overlap (merge-gate-checks.sh:27-31). Separate worktrees with a shared content cache
  give "side by side on the same work-in-flight" without that hazard.

### 4b. How a lane commits
1. `git pull --rebase` (a few commits, seconds), then edit.
2. `lane-check FILE` for the touched file.
3. Before every push, the **import-closure build**: `lake build` of the touched modules and their in-tree
   reverse closure within Deployed, plus `+Host.Main:leanArts` if the Host closure is touched. Everything
   untouched is a cache hit. That is about 5–10 min cold for a hub edit and seconds for a leaf [D].
4. Push to `main` (fast-forward). If the push is rejected, pull --rebase and repeat step 3; the rebuild is cache
   hits for others' modules.
- Small and often: **one logical change per commit**, so a revert is surgical.
- **Generated pins are not committed by lanes:** host-closure.pin, lean-build-surfaces.json, objective manifests,
  TokenCensus rows. The tip service regenerates them and commits them as one `pins:` commit per cycle. FOLLIES F6
  and F7 (delete the source pins) remove most of them.

### 4c. The standing tip service (replaces the integrator, `next` and per-lane landing)
- One box (§5 box A) loops on `main`'s tip:
  1. umbrella and exe-roots, at full Lake width;
  2. the parallel merge gate;
  3. candidate, reusing by closure hash (F6) with the C cache;
  4. the required rows in parallel;
  5. the BAR rows when the box is quiet.
- Each stage publishes `results/<sha>/` and moves a `green` label. Landing means the service passed at that sha.
  **Deploy follows `green`.**
- **A red becomes a known-red line** naming the first red sha, the module and the last committer of that
  module. The tip service posts it to the dashboard and to that lane by role. Fix forward: the owner's next
  commit.
- Fixture re-emit (T9) is a service stage. After a candidate, run `objective-native-acceptance.py`; if the
  fixture moved, the service commits the re-emit (`fixtures:` commit). No lane ever trips over it.

### 4d. What it replaces
| today | shared main |
|---|---|
| "rebase onto next", then re-umbrella | `pull --rebase` of a few commits; cache-hit rebuild |
| INTEGRATOR merge rounds (v1–v4) and their umbrellas | none; the service builds the tip once per cycle |
| per-lane candidates | the service's candidate at the tip, plus a lane candidate only for perf measurement, reused by closure hash |
| batch landing from `next` (1 h 51 m to 3 h 28 m) | continuous; `green` moves each service cycle |
| per-lane pin and ledger commits that conflict | one service `pins:` commit per cycle |

**Ownership:**
- `work/ROLES.txt` gains a module-ownership column with directory globs per lane, such as
  `Compiler/Durable*` or `Host/Client*`. Two lanes that need one file talk first, as already ruled 10-05
  ("parallel lanes converge forward").
- Hot files get split, not locked: Host/Main.lean (9,163 lines) and Host/Json.lean (6,374) split by route family
  (F7). That also shortens the critical path.

### 4e. Draft protocol text (to replace SAFETY-BLOCK's branch rules: line 1 "Lanes: clone from …", "Base your lane on refs/heads/next …", and the INTEGRATOR priority clause of line 2)

> **One main, side by side (gen 2).** Every lane works on `main` in its own worktree of the box's shared repo
> (`git worktree add /srv/lanes/<name> main`); `.lake` comes from the box's shared Lake cache, never copied by
> hand. Commit one logical change at a time. Before every push run the import-closure build
> (`scripts/pipeline/closure-build`: the touched modules and everything in Deployed that imports them, plus
> `+Host.Main:leanArts` if the Host closure is touched) and push only if it is green; then `git push shared
> HEAD:main` and `git push github HEAD:main`. A rejected push is `git pull --rebase` and the closure build again.
> Never commit generated pins (host-closure, build-surfaces, objective manifests, TokenCensus rows): the tip
> service writes them. The tip service builds, gates and rows every new tip; its red is a known-red line naming
> the module and the committer, and that lane's next commit is the fix. Any agent may `git revert` a commit the
> service has shown red for one full service cycle with no fix pushed, saying so in the revert message. There is
> no `next`, no integrator and no lane branch; `lane/<name>` refs exist only for perf experiments that must not
> reach main.

### 4f. What gets worse, and what guards it
- **A bad commit reaches everyone's next pull.**
  - Type errors cannot land, because each push ran its own import-closure build.
  - What can land is a **semantic interaction** between two concurrent pushes (the `Loaded.mk` 24-versus-23
    field class) or a red below the closure (gate, rows).
  - Exposure: one service cycle. That is about 1–17 min of umbrella on an idle box (77 s warm, 1,017 s cold
    worst) [M], about 11 min of gate (658 s) [M] and about 7 min of rows [D], so **about 20–35 min from push to
    known red**.
  - Today the same red is found at the integrator's merge, typically **hours** later (b5fd9ee1: two lanes'
    commits from v3 and v4, found at 917 s of a v4 umbrella).
- **Pulling a red tip blocks a lane's closure build in unrelated modules only if the red is in their import
  closure.** Guard: `git revert` by anyone after one cycle, and lanes may pull `green` instead of `main` while
  the tip is red.
- **Concurrent pushes to `main` race.** Fast-forward-only pushes serialize them. The loser rebases and rebuilds
  from cache, a cost of minutes.
- **No place for a long-lived experiment.** Perf experiments keep `lane/<name>` refs and are never merged as
  branches; a result lands as small commits on main.

---

## 5. Burst plan: two boxes

### Box A, the tip service (one box, about 32 threads, 128 GB or more)
- **Runs:** §4c's loop. One umbrella at full width (`LEAN_NUM_THREADS = nproc`, N seats per F10). The parallel
  gate (its builders job is one `.lake` writer; readers and ledger run beside it). Candidate with the object
  cache and reuse. Rows at `PIPELINE_JOURNEY_JOBS=8`. Nightly: growth, births soak, check-reproducible (no cache).
- **Sizing [M/D]:** burst4 at 16c/32t and 187 GB built cold in 1,017 s and ran a 658 s gate. Allow 64 GB for the
  build cgroup (gate default 64G, run-gate-burst.sh:9) and 32 GB for rows and candidates (publish 16–32G,
  publish-artifacts comments).
- **Install:** the warm base at main; `box.env` with `LAKE_ARTIFACT_CACHE`/`LAKE_CACHE_DIR` (F1),
  `MINIDREGG_NATIVE_OBJECT_CACHE` (F3), `MINIDREGG_LEAN_SEATS`/parallel seats (F2/F10), sccache.env;
  `PIPELINE_LANES`, `PIPELINE_JOURNEY_JOBS=8`, PYTHONPATH pylib; journey units; `perf` (for the BAR rows, with
  `--no-scale` per PERF-FIX-LOG.md:111); the GitHub **deploy key** (SAFETY-BLOCK.txt:6); the hbox peer key; the
  absent-inputs declarations; earlyoom and swarm-build.

### Box B, lane builds (one box, about 32 threads, 187 GB)
- **Runs:** lane worktrees on main (§4a), the shared Lake cache, the ticket-FIFO with-lean-slot (F5). Lane
  candidates only for perf measurement.
- **Sizing:** before F10 measures RSS, use burst4's proven 6 slots × THREADS=4 within a 158G slice
  (BURST4-UP-LOG.md:4,7) [M]. After F10, use `slots = floor(150G / p95 closure-build RSS)`. The only datum,
  "dies at 24G" (lake-slot:8), suggests 5–6 slots at 24–28G [D].
- **Install:** the same box.env items as box A, without journey units. `MINIDREGG_LEAN_SEATS` equal to the slot
  count (SAFETY-BLOCK.txt:7). Deploy key.

### hbox
- **Role:** stays a lane box (or box B, if only one burst box exists).
- **Changes:**
  - Turn F1 on: shared cache under `/tank/dregg-build/pipeline/lake-cache`.
  - Cap non-Lean load. Rows and workloads go in their own cgroup; Lean at 1% CPU under iowait is the measured
    failure.
  - Re-freeze the warm base at main so the cache is seeded.
- **Fix `free`-style misreads:** swap 7G of 7G was full at the snapshot [M hb §8]. Look at what holds it before
  adding slots (`/proc/spl/kstat/zfs/arcstats` size; `ps -eo rss --sort=-rss`).

### Bring-up order
1. Box A: warm base, F1 and F3 env, deploy key, tip-service loop.
2. Box B: shared repo plus worktree script plus with-lean-slot tickets.
3. Merge F2's builder change (one script) and F6's key step before the first service candidate, so the first
   candidate already avoids the 11-minute per-module loop.

---

## 6. Gaps (what I could not measure)
- **Per-Lean-process peak RSS:** not recorded anywhere (hb §6). F10 is the instrument.
- **The 658 s parallel gate:** the burst4 logs are gone (INTEGRATOR-LOG.md:84 is the only record). hbox has no
  parallel-gate run.
- **The brief's "hyp-ledger 569 s" and "token-census 474 s"** appear nowhere on hbox (hb §2). "Growth 1,253 s"
  is the burst2-a journey wall (`claude-lanes/bundles/P3-JOURNEYS-table-pass2.txt:2`), not a growth row.
- **Whether Lake 4.30 skips dependents on private-only changes** under `module`: [A], so F7's spike comes first.
- **Composition of hbox's load 40–60:** not censused.
- **Leftover processes:** the hbox miner left a read-only remote grep (PIDs 1263652/1263698, parent 1) without a
  PID file. It ends by itself; Ember may kill it by PID.
