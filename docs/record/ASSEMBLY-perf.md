> record copy of redregg/work/nanodregg-scout/ASSEMBLY-perf.md, 2026-10-16; the lane logs stay in redregg

# ASSEMBLY-perf — the Opus evaluation of scouts P1–P3 (area: perf), 2026-10-16

Evaluator: Opus, one pass. I read CHARTER.md, decisions/{host,lang,gates}.md and the code the
scouts cite, at main `d1f483e`. I read the code from a `git archive main` copy, because the primary
checkout's working tree is far behind HEAD and its index has staged deletions (`D Codec/Hash.lean`,
`D Codec/Deployed.lean`, …). I also read `~/dev/nanodregg-wt/host`, which is at d1f483e plus
BUILD-HOST's uncommitted `Host/Follow.lean`, `Loop.lean` and `Cli.lean`, but did not change it. I
did not modify nanodregg or any scout directory. My benches and repros live in my scratchpad. One
repro is copied next to this file for the builder: `perf-sandbox-hang-repro.py`.

Tags: **[read]** = read in code or docs at the cited place. **[ran]** = I ran it this session.
**[scout-ran]** = the scout says it ran it and I did not re-run it. **[assumed]** = my inference;
nothing executed it.

## 0. Five facts the scouts did not have, which change the assembly

1. **All three scouts built against the stale primary checkout.** [read]
   - P1 reports "no host exe" and "no Lean follow". At HEAD, `943cab7` (22:59, two minutes before
     P1 wrote SCOUT.md) has `lean_exe host` (lakefile.lean:77), `Host/Cli.lean` (`genesis`,
     `serve`) and `Host/Open.lean`, whose `openLog`/`openWith` is "the one open for writer and
     follower". `Host.Follow` is being written now, uncommitted, in wt/host.
   - So P1's interfaces (2) "a real host exe", (3) "one Host.open" and (4) "follow-step" already
     exist or are in flight. Its (4) "stale IR for Host/Sim/Run (tagGenesis)" belongs to the stale
     `.lake` and is moot at HEAD.
2. **The BAR's real cold reopen is a base plus a tail, and P1 measured neither.** [read] HOST-14 has
   landed. Open reads one sealed `base.world` and then at most `tailMax` of `seg.log`
   (Host/Bounds.lean, `tailMax c b = 2 * cadence b + Log.frameMax c.recordBytesMax`). P1's "cold
   reopen 30 ms" is a fold-from-genesis of a 91 KB toy log in the old `seg-0.log` layout.
3. **LANG-16 changed `Lang.load` after P2 proved things about it.** [read][ran] At HEAD `load` is a
   mutual `load`/`loadAll` (Lang/Program.lean:96,115). It calls `admitPackage` (:83), which
   **re-runs `Package.checkWith` on every closure member on every load**. P2 proved against the old
   single `foldlM` `load`. When I check P2's `LoadMemo.lean` against the HEAD oleans in wt/host, it
   fails at :94: `rfl` cannot see through `loadAll … admitPackage`. LANG-16's own critique names the
   fix: "a Host memo keyed by package id … not dropping the check." P2 is that memo. It is needed
   more at HEAD than when P2 measured it, but its proof has to be redone.
4. **The real `host` exe spawns two dedicated Tasks**: the stdin `pump` (Cli.lean `stdioPort`) and
   the seal (`Loop.spawnSeal`). So P1's sandbox finding is about the deployed binary, not about a
   scout harness. I reproduced it on the HEAD `host` (§2, row 1).
5. **HOST-14 already says what P3 calls a correction.** [read] The table header there reads "one
   append + `F_FULLFSYNC`". HOST-14 also has measured numbers that P3 extrapolated. The encode at
   29 MB is 102–122 ms measured, not P3's "18 ms assumed linear". `Base.file` is 570 ms at 29 MB and
   3.7 s at 87 MB.

## 1. Per-scout verdicts

### P1 — THE BAR over sockets (verdict: needs-rework. Keep one finding, one shape and one number. Discard the code.)

**Keep**
- **K1.1 The sandbox hang** (the most valuable finding in this area). [ran] Under the macOS profile
  that `sandbox/src/lib.rs:93-98` (FLOOR) and `:181-221` (`platform`) build, the HEAD `host serve`
  answers no frame. It still exits 0 on EOF, so an exit-code check sees nothing wrong. Every
  existing confinement plant runs a Python child (`client/tests/supervise.rs:12`) or `/bin/cat`
  (`sandbox/tests/confine.rs`), never a Lean exe [read]. That is why it was not caught. My
  bisection goes further than P1's (§2): one sysctl name, `hw.ncpu`, is enough, and so is
  `LEAN_NUM_THREADS=4` with the profile unchanged. I adopt the env fix, not P1's blanket
  `(allow sysctl-read)` (ID-1).
- **K1.2 The run.sh lifecycle shape.** [read] Start the supervisor and write a PID file; run two
  concurrent writers; stop by PID; restart, and that restart is the cold reopen. This is the
  skeleton of the BAR script (ID-9). Only the shape is lifted, not the file: run.sh drives `p1-sup`
  and `p1-load`, and both are discarded.
- **K1.3 Where the write time goes, as a hypothesis to re-measure on the real path.** [scout-ran]
  - `F_FULLFSYNC` is 88.6% of loop time, at about 5.5 ms per sync.
  - Two closed-loop clients make 975 batches for 1000 writes, so group commit barely groups.
  - p50 is about two syncs, because a request that arrives during a sync waits for it.
  - This is consistent with P3's syncbench (F_FULLFSYNC 5.2–5.3 ms flat) and with HOST-14.

**Discard**
- `HostScout.lean`. It is a second open, reopen and follower loop. Law 1 and law 11: HEAD has
  `Host.openWith`/`openWriter`/`openFollower` (Host/Open.lean, Host/Store.lean:95,108), and
  `Host.Follow` is being written.
- `load/src/main.rs` (`p1-load`). It hand-mirrors `Sim.turnBytes` and `Turn.weight` in Rust, which
  is a twin of Lean encodings and breaks law 2. The BAR client is the real `nd` (ID-9).
- `load/src/sup.rs` (`p1-sup`). It is a second supervisor with the sandbox removed, which is a
  twin and weakens a check.
- `build.sh` and `gen_*.c`. They work around a stale IR that HEAD does not have.
- `lag.py` and the CLOCK_MONOTONIC_RAW join. In the HEAD design the follower is driven by `nd`
  (HOST-9 → PROTOCOL steps; `Host.Follow` docstring), so `nd` sees both the submit ack and the
  follow step that absorbs that height, in one process on one clock. A cross-process clock join
  measures a design we do not have (a follower that tails the writer's segment). The clock fact is
  also mislabelled in the code: the constant is named `CLOCK_UPTIME_RAW` but holds 4, which is
  `CLOCK_MONOTONIC_RAW`. [read]
- **Every P1 number as a BAR figure.** The digests are toy FNV, there are no signatures, cells or
  events, the timing is warm-cache, there is no base, and the store is capped at height 1000 by the
  toy `validUntil` 1024. P1 says this itself.

### P2 — the load memo (verdict: assemble the DESIGN; the PROOF needs rework against HEAD)

**Keep**
- **K2.1 The certificate-carrying `Entry`** (LoadMemo.lean). An entry carries the root, `L`, `g`,
  the witnessed bytes and a Prop `cert`, and only `learn` can build one, so `memoLoad_eq` holds for
  EVERY memo, including garbage. Soundness then needs no hash premise and no invariant on the
  HashMap. That is the right shape under law 6. [read]
- **K2.2 The hit re-witnesses every closure member's bytes in THIS call's pinned view.**
  [read][ran] When I re-run P2's bench, the row "unpinned closure member" refuses `unpinned` under
  both programs, and the plant "hit check removed" is admitted. So the re-witness is what keeps the
  `unpinned` refusal. Lift the row and the plant verbatim (Bench.lean).
- **K2.3 `programM_eq : programM m = program`.** The memoised `Program` is equal *as a value*, so
  `receive_congr`, the follower, audit and every row carry over with no new theorem. That is the
  architectural payoff. [read]
- **K2.4 "Invalidate on install" is a non-event.** ROM cells cannot be written or retired
  (Kernel/World.lean `romWrite`/`romRetire`). Every hit is re-checked against the call's view. The
  memo is volatile (a restart empties it, which is correct) and bounded (`memoMax`). [read]
- **K2.5 The Host contract.** The memo lives outside the receive path. Each batch gets a snapshot
  in `Ctx`. `learn` runs after an admitted install or create. ID-3 restates this generically.
- **K2.6 The equality trap.** A memo hit that compares bytes with `decide (a = b)` costs as much as
  the load it replaces. I re-measured this more broadly (§2, rows 4–5). It also hits `Digest`'s
  `Ord`/`DecidableEq` (ID-4).

**Rework**
- `load_replay` must be re-proved for the mutual `load`/`loadAll` + `admitPackage` (fails at
  LoadMemo.lean:94 against HEAD [ran]). The statement should carry over: `admitPackage` is a pure
  function of `(idb, p, acc, gis)`, and `readPackage` is still the only read of the World [read].
  P2's own critique suggests writing `load` as explicit structural recursion so the replay proof
  does not chase `foldlM`. HEAD already has that shape, so the new proof should be shorter.
- The cited line numbers are stale. At HEAD they are `judgeOne` :189, `judge` :209, `runMethod`
  :214 and `program` :242, and `load` is inlined at :192 and :217 [read].
- **P2's numbers undersell the memo at HEAD.** Its "fresh" path predates LANG-16, so it has no
  re-check. A fresh invoke now type-checks every closure member as well [read; not re-measured].

**Discard**
- `MemoProgram.lean`'s copies `judgeOneL`/`judgeL`/`runMethodL`. The refactor (ID-2) replaces
  them. Keep only `programM` and `programM_eq`.
- The `bytes_eq.c` memcmp extern, *for now* (ID-4, measured). Its allow row would go in
  `gates/native-allow.tsv`, not `axioms-allow.tsv` as P2 wrote. native-allow is the table that
  lists which modules may declare `@[extern]`, and today it lists only `Host.File` [read].

### P3 — base MAC at scale (verdict: idea. Keep two facts and one obligation. Discard the table and the waste row.)

**Keep**
- **K3.1 Plain `fsync` versus `F_FULLFSYNC`.** [scout-ran] On Darwin, plain fsync is 0.03–0.11 ms
  and does not flush the drive. `F_FULLFSYNC` is a flat 5.2–6.6 ms whatever the size. This matters
  for hbox and Linux, where `Host/c/file.c` uses `fdatasync`: the BAR's write figure is a
  per-device constant and must be measured on each device.
- **K3.2 The sink-forcing pattern.** Route the input through an `IO.Ref` and force the result
  before reading the clock. P3's first bench let the compiler sink the pure MAC and reported
  0.00004 ms. Every `Bench/` exe uses this pattern (ID-8). I hit the same hoisting with `decide`
  in my own bench (§2, row 4, first run). [ran]
- **K3.3 The inline `makeRoom` seal stalls the loop, and the bound must be stated.** P3 raised it
  and I sharpened it from the code (ID-7). The stall is reachable in fewer cases than P3 assumed,
  but at `worldBytesMax` it can exceed the 5 s write BAR.
- **K3.4 A parts MAC** (`Hash.macParts`), kept for RSS rather than time (ID-6).

**Discard**
- **The "correction to HOST-14".** HOST-14 already labels that column F_FULLFSYNC [read].
- **The 29 MB / 256 MiB cadence table.** Its encode figure is extrapolated, and HOST-14 has the
  measured one, which is 6× larger. Its cold-open column uses `tailMax ≈ 2.1 MiB` and forgets the
  `frameMax recordBytesMax` term. With that term `tailMax` is about 34 MiB at THE BAR (ID-8).
- **"seal MAC MB/s" as a `gates/waste.tsv` row.** GATES-9 pins deterministic ratios of logical
  work under the seeded sims. A wall-clock MB/s on a shared laptop varies 2× from run to run (P2:
  6514 vs 2519 µs for one cell). It would be a ratchet that goes red on noise, so it belongs in the
  bench output and the BAR history (ID-9).
- **The MAC throughput number itself.** P3 measured 135–171 MB/s, CODEC 184 MB/s and HOST
  ~320 MB/s on the base. That is three hand builds with a 2.4× spread. The one number to keep is
  the one the in-tree, lake-built bench prints (ID-8).
- `src/Codec/*`, which are copies of 17c0307. They are measurement copies and must never land.
- Agreed and recorded as a law, not a new decision: **no native Keccak.** That would put a digest
  decision in C (law 2).

## 2. What I measured (every row [ran], Apple M2 Max, load average 137–186)

| # | what | result |
|---|---|---|
| 1 | HEAD `host serve` (wt/host build of d1f483e, copied to scratch) under the lib.rs macOS profile, two 5-byte frames, 3 s wait each | **no reply** (rc 0 at EOF) |
| 1a | same + `(allow sysctl-read)` | reply in 4.5 ms |
| 1b | same + `(allow sysctl-read (sysctl-name "hw.ncpu"))` only | reply in 0.5 ms (`hw.activecpu` or `hw.logicalcpu` alone: no reply) |
| 1c | FLOOR unchanged, env `LEAN_NUM_THREADS=4` | reply in 0.2 ms |
| 2 | P2's `LoadMemo.lean` against the HEAD oleans | **error** at :94 (`rfl` through `loadAll`/`admitPackage`) |
| 3 | P2's built bench, `./out/bench 20 250`, closure 8 (pre-LANG-16 `load`) | fresh 3104 µs, memo 145 µs per invoke; micro pin re-check 112 µs; unpinned row refuses under both; plant admitted |
| 4 | ByteArray equality, compiled `-O3`, equal contents, distinct objects, inputs via `IO.Ref` (n = 32 B / 9 KB / 72 KB) | `decide (a = b)` 318 ns / 78 µs / **2.85 ms**; derived `==` 98 ns / 25 µs / 186 µs; Lean `USize` loop with `uget` 35 ns / 7.3 µs / 62 µs; memcmp extern 10 ns / 0.25 µs / 2.1 µs |
| 5 | 32-byte compare as `Codec.Digest`'s `Ord` does it (`compare a.bytes.data b.bytes.data`, Codec/Digest.lean:44) | **250–335 ns**; Lean `USize` loop 48–66 ns; memcmp 13–15 ns |

(The bench sources for rows 4–5 are in my scratchpad and use `decreasing_by sorry`. They are
measurement scaffolding, are not copied here, and must not be lifted. The in-tree versions prove
termination.)

## 3. Interface decisions (owner · real signature · both critiques)

### ID-1 · CLIENT (sandbox + nd-supervise): a Lean child gets a static thread count; the plant is a Lean child

**Decision.** `nd-supervise` launches every confined Lean exe with `LEAN_NUM_THREADS=<n>`. `n` is a
Host bound emitted into the generated Rust table (law 2: Rust reads generated constants). On Linux,
bwrap runs `--clearenv` (lib.rs:235), so the variable goes in with `--setenv`. The macOS profile is
NOT widened. The plant comes first: in `sandbox/tests` (or `client/tests/supervise.rs`), run the
real `host` (or the smallest lake-built Lean exe that spawns a `.dedicated` Task and answers one
frame) under `command(&Policy)` and assert a reply within 3 s. It is red at HEAD (row 1).

**Alternatives.**
- (a) `(allow sysctl-read (sysctl-name "hw.ncpu"))` in the profile (row 1b).
- (b) P1's blanket `(allow sysctl-read)` (row 1a).

**Why.** Under law 4, a thread count is a static bound, not a probe of the hardware. The env fix
reads nothing new from the kernel. Of the two, (a) is the narrow one; (b) widens the sandbox to
every sysctl.

**Critique.** `LEAN_NUM_THREADS` is the Lean 4.30 runtime's own variable, not ours. If a toolchain
bump renames it or stops reading it, the hang comes back, and the hang is silent with rc 0. Only
the plant notices, so the plant is not optional. (a) does not depend on the runtime's env contract.
If (b)'s plant ever goes red after a toolchain bump, switch to (a) rather than chase the new name.

**Meta-critique.** I preferred the fix that does not touch the sandbox profile, because "anything
that weakens a check" is on the pause list. One sysctl name is barely a weakening, and I may be
paying a fragility cost to avoid a word.

**Status.** Proposed to CLIENT, which owns `sandbox/` and `client/`. Ship the plant and the fix
together.

### ID-2 · LANG (Lang/Program.lean): the loader is a parameter; the memo is a Program equal to `program`

```lean
abbrev Loader (D : Type) := Pinned D → ByteArray → Except (Refusal D) (Loaded × Nat)
def fresh : Loader D := fun look b => load digestOf look closureDepthMax b ⟨[], [], []⟩
def judgeOne (ld : Loader D) (look : Pinned D) (law : D) (old new : Slots) (r : Req D) : Except (Refusal D) Unit   -- :189, `load …` at :192 becomes `ld look (bytesOf law)`
def judge    (ld : Loader D) (look : Pinned D) (pkg : Option D) (laws : List D) (old new : Slots) (r : Req D) : Except (Refusal D) Unit   -- :209
def runMethod (ld : Loader D) (look : Pinned D) (pkg : D) (state : Slots) (method : Nat) (args : ByteArray) (r : Req D) (budget : Nat) : Except (Refusal D) Slots   -- :214, :217
def programWith (ld : Loader D) : Program D
def program (bytesOf …) (digestOf …) : Program D := programWith (fresh …)           -- :242, unchanged as a value
structure Memo (D) …; def learn …; def memoLoad (m : Memo D) : Loader D
theorem load_replay …   -- re-proved over mutual load/loadAll/admitPackage
theorem memoLoad_eq (m : Memo D) : memoLoad m = fresh
theorem programM_eq (m : Memo D) : programWith (memoLoad m) = program bytesOf digestOf
```

`Kernel.Receive.Program`/`Ctx` (Kernel/Receive/Call.lean:172,185) do not change [read].

**Alternatives.**
- (a) Load once per CALL and share the result. Today an invoke loads the package closure at least
  twice: once in `runMethod` and again in `judgeOne` for the same package, plus once per extra law
  [read :209-217]. A per-call share needs `Program` to expose "load, then run and judge", which is
  a KERNEL interface change.
- (b) Drop LANG-16's re-check. That makes `run`'s soundness a World invariant no theorem states.
  LANG refused it, and so do I.

**Why.** The memo removes repeated loads within a call and across calls, with no KERNEL change,
and `programM_eq` makes it invisible to every theorem.

**Critique.**
- The re-witness on a hit costs O(closure bytes), so a hit is not O(1).
- Entries can only come from `learn`, so nobody can seed the memo cheaply.
- `load_replay` is tied to the shape of `load`, and a later change to `load` reopens it. It has
  already happened once (row 2).

**Meta-critique.** I follow P2 and LANG-16's own named fix. Both are anchored on "memo keyed by
id", and I did not explore P2's untried idea of a structural, per-package cache that assembles a
closure from its parts.

**Status.** Proposed to LANG.

### ID-3 · HOST (Host/Loop.lean): the Resident carries a volatile auxiliary state; the Machine is built per batch

```lean
structure Resident (W A : Type) where … aux : A          -- Loop.lean:94 gains `aux`
def serve (mk : A → Machine W T R Frame) (learn : A → W → Array T → A) (rec : Recorder W T) … : Nat → Resident W A → Option Frame → IO (Exit × Resident W A)
-- Host.Deployed: A := Lang.Memo D; mk m := machine (X.withProgram (programWith (memoLoad m))); learn = Lang.learn over each admitted install/create
```

`learn` runs after `commitBatch` returns, outside `admitBatch`, so the receive path stays a pure
function of `(World, aux snapshot)`. `Host.Follow`'s audit path uses the same `aux`.

**Alternatives.** Hide the memo inside `X` as an `IO.Ref`. That makes `Ctx` impure and breaks
`receive_congr`'s premise. Or keep the memo in the World. The World is consensus state, and a memo
is not.

**Critique.**
- `Loop` grows a type parameter and a second function argument for one client.
- If a second volatile cache ever appears, `A` becomes a product nobody owns.
- Building the Machine per batch costs a closure allocation per batch, which is negligible next to
  one fsync [assumed].

**Meta-critique.** I kept HOST's Loop generic in `W T R` because HOST built it that way. A
deployed-only Loop would be simpler, but the simulation runs the same Loop.

**Status.** Proposed to HOST, after ID-2.

### ID-4 · CODEC (Codec/Digest.lean:19,44 + a `Codec.Bytes`): byte equality and order without `.data`

```lean
def Bytes.eq (a b : @& ByteArray) : Bool          -- USize loop with uget; theorem Bytes.eq_iff : Bytes.eq a b = true ↔ a = b
def Bytes.cmp (a b : @& ByteArray) : Ordering     -- theorem Bytes.cmp_eq : Bytes.cmp a b = compare a.data b.data
instance : DecidableEq Digest := … Bytes.eq …       -- :19
instance : Ord Digest := ⟨fun a b => Bytes.cmp a.bytes b.bytes⟩   -- :44; Std.TransOrd/LawfulEqOrd re-proved through cmp_eq
```

The memo's re-witness (ID-2) and `Log.frameAt`'s tag compare (`s.tag (prev ++ r) = t`,
Host/Log.lean:104) use `Bytes.eq`.

**Why.** Every World `TreeMap` lookup is keyed by `Digest`. Today each compare materialises two
boxed `Array UInt8` (250–335 ns; row 5). Equality through `ext_iff` costs 39 ns per byte (row 4).
The Lean loop is 5× faster at 32 B and 46× faster at 72 KB, and it has a real theorem and no
extern.

**Alternative.** The memcmp extern (P2's `bytes_eq.c`) is about 4× faster again at 32 B and 30× at
72 KB. That is 60 µs per memo hit at closure 8, against 145 µs.

**Critique.**
- I am leaving a measured 4–30× on the table for a principle.
- At a deep closure the hit is 0.8 ns/B against 0.03 ns/B. If a row shows the memo hit dominating
  an invoke, the extern is right, with its spec body and a `native-allow.tsv` row.
- Byte equality is a "decision" only in the thinnest sense.

**Meta-critique.** A law-2 purist bias: no C that decides. And the rows that would justify the
extern do not exist yet, which conveniently means I don't have to argue for it.

**Status.** Proposed to CODEC. The extern is held back until a measured row asks for it.

### ID-5 · KERNEL (Kernel/World.lean:113 `pinOf`, :257-260 `touchCheck`): a pin check that does not re-hash the cell — PROPOSAL, KERNEL rules

Every pin becomes a touch (`touchesOf`, Call.lean:275) [read]. `touchCheck` then re-encodes and
re-hashes the whole cell for each one (`pinOf E cur = x.seen`). With the memo in place, this
re-check is 112 µs of the 145 µs invoke at closure 8 (row 3; toy FNV, and a real KMAC costs more).
The writer's open fold (`foldStep` → `World.admit`) pays it again for every Turn in the tail.

**Options.**
- (a) Each live entry carries its pin digest, computed when the entry is born or written. That is
  O(touched), and the pin check becomes O(1). Representation invariant:
  `entry_pin : e.pin = pinOf E (some e.cell)`, unrepresentable otherwise.
- (b) A ROM cell's pin is its id, because the id is its content digest and ROM never changes.

**Lean.** (a): one pin semantics (law 1), and it also covers mutable cells that are pinned but not
written.

**Critique.**
- (a) puts derived data into consensus state, 32 B per cell.
- The base either serialises the digest (and `Base.read` trusts a MAC'd cache) or re-derives it
  at decode, which is an O(store) hash at open of about 1 s at 256 MiB [assumed, from HOST's MAC
  rate].
- (b) touches only ROM and adds a second pin rule.

**Meta-critique.** Kernel state is outside the perf area. I am proposing it because the scout
measured it, and a perf lane that "fixes" the kernel is how twins start.

**Status.** Open, for KERNEL.

### ID-6 · CODEC + HOST: a MAC over parts; the Sealer tags (prev, record) without concatenating

```lean
def Hash.macParts (key : Digest) (domain : String) (parts : Array ByteArray) : Digest   -- CODEC
theorem Hash.mac_eq_parts : Hash.mac k d m = Hash.macParts k d #[m]
theorem Hash.macParts_append : Hash.macParts k d ps = Hash.mac k d (ps.foldl (· ++ ·) .empty)
structure Log.Sealer where tag : ByteArray → ByteArray → ByteArray; tag_size : ∀ p r, (tag p r).size = tagBytes   -- HOST, Host/Log.lean
```

`Log.frame` (Host/Log.lean:60-61) writes `len`, `r` and the tag as three `File.writeAll` calls and
one sync. `frameAt` (:104) and `Base.file` (Host/Base.lean:97) stop building `prev ++ r`.

**Why.** It is about RSS, not time. HOST measured 1.66 GB RSS at an 87 MB base [read, HOST-14
table]. A base record is up to `2·worldBytesMax` (`baseRecordMax`), and today it is copied once
into `prev ++ r` for the tag and again into the frame. That is two extra copies of up to 512 MiB at
the size the Store allows.

**Alternative.** A streaming World encoder, which removes the last full copy. That is a much larger
change for CODEC, and it should wait for a measured need.

**Critique.**
- A memcpy is fast (P3: 0.6 ms at 29 MB), so at THE BAR this buys nothing.
- Three write(2) calls per frame instead of one.
- A second public entry to the hash. `mac := macParts #[m]` keeps it one function.

**Meta-critique.** I am accepting a RSS argument whose large figure (~5 GB at 256 MiB) is
extrapolated, not measured.

**Status.** Proposed. It lands only after ID-8 measures RSS at `worldBytesMax`.

### ID-7 · HOST (Host/Loop.lean `makeRoom`, Host/Bounds.lean): the write-stall bound is a theorem and `worldBytesMax` answers to it

**Derived from the code** [read; assumed, not run]:
- `shouldSeal` spawns a seal only when `pos − sealed.offset ≥ cadence` and nothing is pending.
- So when the in-flight seal lands at `p0`, the tail behind it is at most
  `tailMax_old − cadence_old ≤ cadence_old + frameMax`.
- That fits in `tailMax_new = 2·cadence_new + frameMax` whenever `2·cadence_new ≥ cadence_old`.
- So `makeRoom`'s INLINE seal is reachable only when the base shrank by more than half between two
  seals. In every other case the worst write stall is one `settle` of the in-flight seal plus one
  fsync.

**Decision.**
- (1) State it: `within_after_settle : 2 * c.cadence new ≥ c.cadence old → withinTail …` beside
  `within_after_seal` (Host.Proofs.Base).
- (2) The worst write latency is ≤ seal(base) + fsync outside the shrink corner, and
  ≤ 2·seal(base) + fsync inside it.
- (3) Set `worldBytesMax` so that `2·seal(worldBytesMax) + fsync ≤ 5 s` on the measured bench
  (ID-8).
- HOST measured 3.7 s at 87 MB. Linear [assumed] gives about 11 s at 256 MiB, so today's
  `worldBytesMax` (1 <<< 28) probably breaks the write BAR in the corner and when appends outrun
  seals.

**Alternative.** Keep 256 MiB and declare the write BAR as holding below a stated World size, with
`worldTooLarge` already a named refusal.

**Critique.**
- Cutting `worldBytesMax` to about 64 MiB caps a Store at about 200 BAR-sized Worlds.
- The stall needs a sustained append rate of roughly `cadence + frameMax` per seal time, about
  9 MB/s at 256 MiB, which two friends and a Hermes resident will never produce.

**Meta-critique.** I am applying the BAR at a scale the BAR does not name. Law 4's "a static bound
on everything" says the bound must be stated, but not that it must be the BAR.

**Status.** Proposed to HOST. Part (1) can land now. Part (3) waits on ID-8's number.

### ID-8 · PERF (new `Bench/`): one in-tree, lake-built bench of the deployed code — measures the worst cut, not the average

```
lean_exe «bench-host» where root := `Bench.Host.Main      -- tooling (C9: no deployed module imports Bench/)
```

It prints `BENCH <op> <size> <metric> <value>` for:
- encode, MAC, `Base.file` seal, base open, and **worst-cut reopen**, at 1k / 10k / 100k records
  and at `worldBytesMax`;
- RSS at each size;
- Ed25519 verify per call;
- the memo hit and fresh invoke at closure 1 and 8;
- Digest compare.

The worst-cut reopen is a Store with the tail exactly at `tailMax`. At the deployed cadence and
THE BAR's 290 KB base that is `2·1 MiB + (4 + 2^25 + 32)` ≈ **34 MiB** of real batch records,
folded with `Deployed.foldStep` [read; nobody has measured it]. Use Kernel.Sim.Gen under the
deployed Ctx, or any generator of real signed Turns, never a toy encoding.

All Bench code calls the deployed definitions and copies none of them. It forces inputs and outputs
through `IO.Ref` (K3.2) and reports the median of N together with the machine's load average.

It replaces the out-of-tree `~/dev/redregg/work/host-bench/{K1,Base}.lean` and P3's hand-built
`bench`. Every later HOST-14 re-read quotes this exe.

**Alternative.** Keep each layer's bench outside the tree. That gives three hand builds with a
2.4× spread on a single number (P3 vs CODEC vs HOST).

**Critique.**
- A bench in the tree is code that must keep building and adds to SIZE.
- Wall time on this laptop under load 100+ is ±2×.

**Meta-critique.** I want one number badly enough to build a directory for it.

**Status.** It is the PERF lane's own first deliverable (§4).

### ID-9 · GATES (standing) + PERF: THE BAR as a wall-clock gate through the real stack, provably able to go red

`scripts/bar.sh` (PERF) does the following:
- genesis with two founders;
- start the real `nd-supervise` (confined, ID-1) over the real `host serve`, PID file;
- two members write 500 records each through the real `nd` (submit until `nd command` and
  `Host.Follow` land, then the command path — and it says which it ran);
- stop by PID;
- produce a worst-cut Store (ID-8) and cold-reopen it;
- print `BAR write_p99_ms <v> limit 5000`, `BAR reopen_ms <v> limit 60000`,
  `BAR follow_lag_p99_ms <v>` (measured inside `nd`, one clock), `BAR path submit|command`, and
  `BAR device <fs/fsync kind>`.

`standing.sh` (GATES) marks a BAR line over its limit as RED. **The gate's plant:** run it once with
`BAR_LIMIT_SCALE=0.0001` and assert it goes RED, so a comparator that cannot fail is caught. The
history goes to `gates/bar.tsv` as a trend, not a ratchet.

**Alternatives.** A waste-style ratchet on wall time, which goes red on noise. Or a rows-style
in-process run, which cannot see the sandbox, the sockets or fsync.

**Critique.**
- Limits 200–2000× above measured values almost never go red, so the gate mostly proves the
  pipeline runs.
- The device term makes laptop and hbox numbers incomparable.
- A command-path BAR depends on two lanes that have not landed.

**Meta-critique.** GATES-9 says wall time is what THE BAR uses and that the waste ratchet does not
see it. This gate closes that gap. I may be over-valuing a gate that mostly passes, because
"measured end to end" feels like progress.

**Status.** Proposed to GATES. PERF writes the script.

## 4. Charter rows

| layer | owner | owns | must never | first deliverable |
|---|---|---|---|---|
| PERF (a lane, not a decision layer) | BUILD-PERF (Opus) | `Bench/` (lake exes measuring the deployed code; C9 tooling: no deployed module imports it), `scripts/bar.sh`, `gates/bar.tsv` rows, `decisions/perf.md` | decide anything (no `def` that a deployed path calls); copy a deployed definition (law 11; a bench that re-implements an encoder measures the copy); quote a toy, warm-average or extrapolated number as THE BAR; add a wall-clock row to `gates/waste.tsv`; commit another layer's file without `--cross-layer <OWNER>` and that owner's agreement | the ID-1 plant, red at HEAD then green with CLIENT's fix; then `bench-host` with the worst-cut reopen at THE BAR's base |
| CLIENT (amended row) | BUILD-CLIENT | + the confinement plant runs a **Lean** child | treat rc 0 at EOF as "the child worked" | ID-1 |
| LANG (new deliverable) | BUILD-LANG | the memo (ID-2) | key a hit on an id or hash without re-witnessing bytes in the call's pinned view; add "invalidate on install" | `load_replay` over HEAD's mutual `load`, then `programM_eq` |
| HOST (new deliverable) | BUILD-HOST | `Resident.aux` + per-batch Machine (ID-3); `within_after_settle` (ID-7) | let `learn` run inside `admitBatch` | `within_after_settle` |
| CODEC (new deliverable) | BUILD-CODEC | `Codec.Bytes.eq/cmp` (ID-4); `Hash.macParts` (ID-6, after ID-8) | add an `@[extern]` without a measured row and a native-allow row | `Digest`'s `Ord`/`DecidableEq` through `Bytes.cmp/eq`, laws re-proved |
| GATES (new deliverable) | BUILD-GATES | the BAR verdict in standing + its plant (ID-9) | ratchet wall time | standing reads `BAR … limit …` lines, red over the limit, plant-checked |

## 5. Risks (what gets worse)

- **The sandbox fix rides on a runtime env var** (ID-1). Without the plant, a toolchain bump could
  bring the silent hang back.
- **The memo adds a second path to the same value.** It is safe only through `memoLoad_eq` and
  `programM_eq`. Its memory: `memoMax` entries × closure bytes, about 256 × 8 × 9 KB ≈ 18 MB at
  P2's synthetic closures, and up to about 1 GiB for pathological ones (P2's estimate) [assumed].
  It needs a byte bound, not only an entry count.
- **The memo re-opens the proof whenever `load` changes.** This has already happened once (row 2).
- **The worst-cut reopen may be the first BAR number that is not 1000× inside its limit.** Its tail
  is about 34 MiB because `recordBytesMax` is 32 MiB. If it is slow, the fix is a smaller
  `recordBytesMax` (HOST/KERNEL `weightMax`), and that changes what a single batch can carry.
- **Cutting `worldBytesMax`** (ID-7) shrinks the largest Store and halves HOST-15's thin-member base
  ceiling.
- **Ed25519 is 381 µs per verify in pure Lean** (CODEC b0d576a) on the single loop thread [read].
  That caps the writer at about 2600 submits/s, and a follower's first audit pays it per event. It
  is fine at THE BAR. Parallel verification in pure Tasks is possible later and is not proposed
  now.
- **Pipelining** (admit the next batch while the previous one fsyncs) would roughly halve p50, per
  P1's "two syncs" finding. It was declined: replies must follow their own fsync, and a speculative
  World complicates crash semantics, for a gain THE BAR does not need. Recorded here so that nobody
  rediscovers it as new.
- **hbox and Linux fsync are unmeasured.** Ember's box is off-limits until ROOT says, so every BAR
  figure is Darwin-only and says so (`BAR device`).

## 6. FIRST BUILDER BRIEF — BUILD-PERF (Opus)

You are BUILD-PERF for nanodregg (`~/dev/nanodregg`, main only). Read, in order:
1. `~/dev/nanodregg/CHARTER.md` (all of it; laws 2, 4, 5, 6, 10, 11 bind you hardest);
2. this file, `~/dev/redregg/work/nanodregg-scout/ASSEMBLY-perf.md`;
3. `decisions/host.md` HOST-14 and HOST-17, `decisions/lang.md` LANG-16, and `decisions/gates.md`
   GATES-7, GATES-8 and GATES-9, **as of HEAD**: `git -C ~/dev/nanodregg show main:decisions/host.md`;
4. `~/dev/redregg/work/HOST-LOG.md`, for the commit and build commands.

**The primary checkout is stale. Measured 10-16: its working tree is thousands of lines behind main
and its index stages deletions.** Never read code from `~/dev/nanodregg/<path>` without checking
`git -C ~/dev/nanodregg diff main -- <path>` first. Read HEAD with `git show main:<path>`, or
extract it with `git archive main | tar -x -C <your scratch>`. Build in your own worktree via
`scripts/worktree` (GATES), never the primary checkout. Commit ONLY with
`scripts/commit -F MSGFILE [--cross-layer OWNER] PATH...`, subject prefix `perf:`. Never use the
shared index, never `git add -A`, never `git stash`.

**What you own:** `Bench/`, `scripts/bar.sh`, `gates/bar.tsv`, `decisions/perf.md` (add an OWNERS
row and a lakefile `lean_exe` in your first commit). For everything else, write the change, message
the owner (SendMessage: CLIENT, LANG, HOST, CODEC, GATES), and land it with `--cross-layer` only
with their agreement. Usually they land it themselves.

**Order of work:**
1. **ID-1, the silent sandbox hang.** Repro:
   - `python3 -I ~/dev/redregg/work/nanodregg-scout/perf-sandbox-hang-repro.py DIR floor`, after
     `cp <lake-built host> DIR/host && DIR/host genesis DIR/store toy`;
   - expect `NO REPLY`; with `LEAN_NUM_THREADS=4` in the environment, expect a reply.
   - Write the plant in `sandbox/tests` or `client/tests/supervise.rs`: a lake-built Lean exe that
     spawns a `.dedicated` Task, launched through `command(&Policy)` / `nd-supervise`, asserting a
     reply within 3 s.
   - It must be red at HEAD. Paste the red run into the commit.
   - Then CLIENT's fix (`LEAN_NUM_THREADS` from a generated Host bound; `--setenv` on bwrap), and
     paste the green run.
2. **ID-8, `Bench/Host/Main.lean` → `lake exe bench-host`.**
   - Deployed definitions only (`Host.Deployed`, `Codec.Deployed`, `Host.Base`, `Host.openWith`).
   - Real signed Turns from the Kernel's generator under the deployed Ctx.
   - Sink-forcing: inputs through `IO.Ref`, results forced before the clock.
   - Report the median of N, plus `sysctl -n vm.loadavg`.
   - FIRST number to publish: the **worst-cut reopen** at THE BAR's base (tail = `tailMax` ≈ 34
     MiB). Then seal, open and RSS at 1k / 10k / 100k / `worldBytesMax`. Then Ed25519 per verify,
     and Digest compare.
   - Write the results into `decisions/perf.md`, with both critiques, and message HOST with the
     HOST-14 re-read numbers.
3. **Hand ID-7 (1)** `within_after_settle` to HOST. Then use ID-8's seal number to propose
   `worldBytesMax`.
4. **ID-4 with CODEC.** `Codec.Bytes.eq/cmp` as `USize` loops with `uget`, `Digest`'s instances
   through them, and `Codec.Proofs.Digest`'s laws re-proved. Add a bench row before and after.
5. **ID-2 + ID-3 with LANG and HOST.** Lift from `/Users/ember/dev/nanodregg-scout/P2/`:
   - `LoadMemo.lean`: the `Entry`/`cert`/`learn`/`memoLoad` design and the statements of
     `load_replay`, `memoLoad_eq` and `programM_eq`. The proof bodies must be redone, because
     `load` is now mutual with `admitPackage` (it fails at :94 against HEAD).
   - `Bench.lean`: the unpinned-closure ROW and the hit-check-removed PLANT, verbatim in intent.
   - `MemoProgram.lean`: only `programM` and `programM_eq`.
   - Every theorem statement is read by a second agent before it lands (law 6 vacuity check).
6. **ID-9.** `scripts/bar.sh` through the real `nd-supervise` + `host serve` + `nd`, with
   `BAR path` stated. Do it after BUILD-HOST lands `Host.Follow` (uncommitted in
   `~/dev/nanodregg-wt/host` as of 23:05). Hand GATES the standing hook and the
   `BAR_LIMIT_SCALE` plant.
7. **ID-6** only if ID-8's RSS at `worldBytesMax` says so.

**Lift:**
- `P2/LoadMemo.lean`: design and statements.
- `P2/Bench.lean`: row and plant.
- `P2/MemoProgram.lean`: `programM`/`programM_eq` only.
- The lifecycle *shape* of `P1/run.sh`.
- The sink-forcing *pattern* of `P3/src/Bench.lean`.
- `P3/sync.c`'s numbers, as reference (fsync 0.03–0.11 ms vs F_FULLFSYNC 5.2–6.6 ms on Darwin).

**Ignore:**
- `P1/HostScout.lean`: a twin of Host.Open/serve.
- `P1/load/`: `p1-load` mirrors toy Lean encodings in Rust; `p1-sup` is an unsandboxed second
  supervisor.
- `P1/build.sh`, `P1/gen_*.c`: a stale-IR workaround.
- `P1/lag.py`: a cross-process clock join; measure lag inside `nd`.
- Every P1 BAR number.
- `P2/bytes_eq.c`: not adopted until a measured row asks.
- `P2`'s line numbers.
- `P3/src/Codec/*`: copies of 17c0307.
- P3's cadence table, its "correction", and its waste-row proposal.

**Laws for you in particular:**
- A bench that re-implements what it measures is a twin.
- A number without its device, load and N is not a number.
- Say the worst cut, not the average.
- A gate that cannot go red is not a gate. Plant it.

**Box safety.** No hbox and no box builds until ROOT says. Never run an unfiltered `-p <crate>` or
`cargo test` suite: filter with `--test <name>` to what exercises your change. The Mac data volume
is nearly full: no fixtures over 1 MB in the tree, and worst-cut Stores (34 MiB+) live in your
scratchpad and are deleted by you when you finish (only files you created). Disk pressure is
Ember's: stop, `df`, report, wait; delete nothing else. Every loop sleeps and has a deadline.

> ## Stopping processes: PID file or nothing (incident 2026-10-10)
>
> A subagent ran `pkill -f "cat" -u ember` to clear its own stuck `cat`. `-f` matches the whole
> command line, every app lives under `/Appli**cat**ions`, and 44 of my apps and agents got SIGTERM.
> - **Never kill by pattern.** No `pkill -f <anything>`, no `pkill -x <bare word>`, no `killall`, no `kill -u`.
> - **A process you started is stopped by the PID in its PID file**, and only that. Every detached job
>   writes one (`nohup ... & echo $! > job.pid`). No PID file, no kill: tell me instead.
> - If you must look first, `pgrep -fl` and read the list; it is never the argument to a kill.
> - Every subagent brief you write quotes this block verbatim.

Report to ROOT on events only: plant red, plant green, the first worst-cut number, a decision
another layer must answer, handoff. Write `~/dev/redregg/work/PERF-LOG.md` as your continuation
before 350K tokens.
