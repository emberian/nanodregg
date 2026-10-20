> record copy of redregg/work/nanodregg-scout/ASSEMBLY-ops.md, 2026-10-16; the lane logs stay in redregg

# ASSEMBLY-ops — the Opus evaluation of scouts O1–O5 (area: ops), 2026-10-16

Evaluator: Opus, one pass. I read CHARTER.md, decisions/{host,gates,client}.md, and the parts of
protocol.md and kernel.md that ops touches. I also read the real code at main 24d0f79, extracted with
`git archive` to a scratch copy, because the primary checkout's working tree is ~5,400 lines behind
HEAD. Main has since moved to 43c4d58, and HOST-3's uncommitted worktree `~/dev/nanodregg-wt/host` was
read but not changed. I did not modify nanodregg or any scout directory.

Each claim carries a tag: **[read]** means I read it in code or docs at the cited place; **[ran]**
means I ran it myself this session; **[assumed]** means it is my inference and nothing executed it;
**[scout-ran]** means the scout reports running it and I did not re-run it.

## 0. Three facts the scouts did not have, which change the assembly

1. **HOST-3 is building the `host` exe right now.** [read] The uncommitted files
   `~/dev/nanodregg-wt/host/Host/{Main,Cli,Deployed,Page}.lean` contain the verbs `genesis STORE NAME
   [KEY_HEX NEXT_HEX]…`, `serve STORE` and (in the usage text) `follow STORE MEMBER_HEX GRANT_HEX`. The
   exit codes are `0 eof · 2 usage/refused · 3 uncertain · 4 fuel · 5 sealFailed · 6 recordTooLarge`
   (`Cli.exitCode`), with `fuelBatches = 1 <<< 24`. O1 and O5 both say "no host exe"; that is true at
   HEAD and false within hours. Every ops item that needs the exe is therefore an ASK to HOST-3, not
   something to build beside it.
2. **The scouts read three different trees.** [read]
   - O3 built against the stale primary checkout, which has `seg-*.log`, `ckpt-<h>.world` and
     `Log.recover` at :148. HEAD has ONE `seg.log`, ONE `base.world` and `STORE/key`
     (Host/Store.lean:25-28), `recover` at Host/Log.lean:143, and domain-separated sealers already
     (Host/Keys.lean:17-24, `domSegment`/`domBase`). So O3's interfaces (1) "chain across segments",
     (3) "a domain argument on Sealer.tag" and (5) "pick ckpt vs base" are moot at HEAD.
   - O4 used wt/kernel at 424163c; O5 used bc0460d; O2 used the primary `.lake` at 1e43a54.
   - The O1, O4 and O5 citations I checked hold at HEAD: `Policy` sandbox/src/lib.rs:27, `command`
     :171, `--unshare-all`/`--disable-userns` :231-232, `--clearenv` :235, "NEVER RUN" :15,
     `withTempDir` Host/Sim/File.lean:67,112, `| 0, r, _ => finish .fuel r` Host/Loop.lean:187,
     nd-supervise exits 2/70/child status at :86,:117-119.
3. **Cross-World replay is open today.** [read; not ran] This is what turns O2's "replay immunity is
   accidental" into a defect.
   - `Receive.genesis X name allowance founders` (Kernel/Receive/Follow.lean:48) places founder i at
     `founderId X name i`, a function of the NAME and the INDEX, not of the key.
   - `Unsigned` (Kernel/Receive/Call.lean:65-73) carries `member key notBefore validUntil pins
     maxCharge body`. Nothing in it names the World. `worldId X = hash domWorld ByteArray.empty`
     (Call.lean:251) is the same constant in every World.
   - `validUntil` is a height, and a re-genesis restarts height at 0.
   - So: re-genesis with the same NAME and the same founder keys, which is the flag-day default when
     the operator types the same `host genesis STORE NAME K N…` line. Then a call signed in the old
     World, whose pins name only founder cells (the same ids, the same digests), is admissible again
     at every new height ≤ its `validUntil`. The journal that refused it as `replayed` is gone.
   - The Sims and Loopback all use a constant `Sim.worldName` (Kernel/Sim.lean:532,
     Protocol/Rows/Loopback.lean:445), so no row can see this.

## 1. Per-scout verdicts

### O1 — units, genesis, runbook (verdict: needs-rework; keep three ideas, discard the rest)

**Keep.**
- **K-O1a. The exit contract as data with a disjointness theorem.** Restate `restartable`/`fatal`
  (Deploy.lean:154-158, `restart_fatal_disjoint` by `decide`) over HOST's real `Exit` and
  `StoreFault`, not O1's invented 64/65 [read: Deploy.lean says it invented them]. HOST owns the table
  (D5 below).
- **K-O1b. A unit renderer in Lean, emitted with `--check` and a `gates/generated.tsv` row**, the
  same pattern as `emit-rust`. What to keep is the systemd text shape: `RestartForceExitStatus`,
  `RestartPreventExitStatus`, `UMask=0077`, `NoNewPrivileges`, `TimeoutStopSec`. [read]
- **K-O1c. The live launchd row** (`O1/live/`: bootstrap, bounded wait, bootout), with the REAL
  `host serve` as the child once HOST-3 lands it. O1's stub-run facts are [scout-ran]: launchd restarts
  on every non-zero exit; a `#!/bin/sh` child dies under the sandbox; bootout leaves a stale
  `host.sock` that nd-supervise's bind replaces. I checked that no `software.ember.nd-*` job is still
  loaded: `launchctl list` shows none [ran].

**Discard.**
- **`Node.exposure`, `Node.structural`, `Node.nameable` and the `plant_*` theorems over them.** They
  are a second copy of CLIENT-9's `Exposed` check (sandbox/src/lib.rs), which already runs at launch
  and is the one that gates the child. Law 1 says one check. The Lean copy can only drift: O1 proves
  shapes ("list overlap") that the Rust check decides independently. A policy that the Rust check
  refuses fails loudly at first start with nd-supervise exit 2, which belongs in the fatal class.
- **The `follow` unit on the writer's node reading the writer's Store**, and `only_serve_writes`.
  CLIENT-12 B, with PROTOCOL's answer, puts each member's follow on the member's machine, catching up
  through `host(log)` steps relayed by nd [read]. HOST-14's retraction records ROOT's ruling that "the
  follower reopens from its own sealed base", so a follower WRITES its own Store [read]. O1's
  follower is read-only on the writer's Store, which is the node attesting to itself (O1 says so in
  its own critique).
- **"Exit 0 on a fatal refusal on macOS."** An exit status is a verdict (law 7): 0 must mean eof and
  nothing else. On macOS the operator accepts the throttled loop: a fatal open refuses again every
  `ThrottleInterval` seconds, truncates nothing, and logs its name each time. The laptop is a member
  machine, not the writer's node.
- **`ThrottleInterval 10` as a bare literal.** If it stays, it is a named constant beside the exit
  table.

### O2 — world-carry (verdict: discard as a deliverable; keep two findings, routed)

**Discard the carry.** Law 1 says "Old shapes refuse to load; **nothing migrates**; re-genesis is
free." `carry` renames every id, rewrites slots by role, and needs custody-supplied precommits. That
is a migration with its own id derivation (`freshId`, a second one beside `cellIdOf`/`romIdOf`), its
own role table (a twin of the Call.lean slot constants), and its own heuristic state rewriting
(`substitute`, measured quadratic and wrong for ids held as data) [read SCOUT.md + Carry.lean
header]. It also cannot carry history, which O2 states itself. I did not re-run `./run.sh`: it
rebuilds `Carry.olean` inside the scout directory, which this task forbids modifying.

**What would make the discard wrong:** the first deployment where friends' data must survive a flag
day. Then "carry or lose it" is a product decision for Ember (pause item 4), and O2's
`carry`/`verify`/ids-receipt contract is the starting point. KERNEL-15's own text concedes the cost
("free here, not free in a deployment with friends' data") [read].

**Keep, routed.**
- **K-O2a. Old shapes must refuse to load.** Today the Store does not stamp its shapes: no
  `Tag.of` call exists outside Codec/ [read; grep]. CODEC's Tag.lean header promises the mechanism
  ("A Store stamped with the tags of the codecs that wrote it refuses to open"), but nothing applies
  it. → D2.
- **K-O2b. Signed bytes must bind the World.** O2's interface 2 turned out to be the cross-World
  replay defect in §0.3. → D3.

**Do not route:** the `Layout`/Role KERNEL export, `Ty.id` in LANG, and an epoch-independent
`nextKeyDigest`. Each is needed only by the carry.

### O3 — backup/restore (verdict: needs-rework; keep the finding and the plant table, discard the manifest)

**Keep.**
- **K-O3a. "`recover` = clean" does not mean "complete".** A copy cut at a frame boundary is a valid,
  shorter log [scout-ran; also derivable from Host/Log.lean, `recover` returns `Tail.clean` on any
  frame-aligned prefix — read]. At HEAD's shape, a cut below the base's offset is refused
  (`segmentShort`, Host/Base.lean:109) [read]. A cut at or above it opens silently at a lower height.
- **K-O3b. The refusal table and the verify order, restated for HEAD's three-file Store:** key size
  (`badKey`), base MAC (`baseCorrupt`), segment ≥ base offset (`segmentShort`), tail ≤ `tailMax`, tail
  fold with the chain asserted, then **anchor comparison** (`behindAnchor`, `chainMismatch`). The
  plants that still apply at HEAD: truncate at a frame boundary (refused with an anchor, silent
  without), truncate mid-frame (torn, then the anchor), splice from another history under the same
  key (corrupt), flip a byte (corrupt), wrong key (`baseCorrupt`), rollback to an older complete copy
  (`behindAnchor`).
- **K-O3c. The rule for copying a live Store:** a torn tail is the writer's unsynced frame and is never
  shipped; corruption is refused, never laundered into a copy.

**Discard.**
- **The MANIFEST.** It is a second authenticated inventory of what the base already partly binds
  (offset + tag). Its job, catching truncation, is the same job as an external anchor. Without an
  anchor, the manifest still accepts a rollback to an older complete backup (O3's own undecidable
  row). Under HOST-16 the MAC key sits in the Store, so anyone holding the backup medium can forge
  the manifest [read HOST-16]. So the anchor is the only real check. One check, law 1.
- **Multi-segment chaining and the `Manifest.encode` with toy le64.** Moot at HEAD, and the scout
  itself says not to lift it.
- **"The key is not in the backup."** HOST-16 rules that the key protects nothing an attacker wants.
  A backup without its key cannot open at all: the base fails its MAC, so it is `baseCorrupt` [read
  Base.read]. The key travels with the copy.

### O4 — observability (verdict: assemble, with three changes)

**Keep.**
- **K-O4a. F1 is a real defect.** [ran] `obsrun mem 200 3 st.txt 200` printed `UNANSWERED=11 …
  FAIL counters`. `obsrun mem 200 1000` printed `unanswered=0 … ALL PASS`. The code is
  Host/Loop.lean:187 `| 0, r, _ => finish .fuel r`, which discards `carried` [read]. It is wider
  than O4 says. HOST-3's Cli exits the PROCESS on fuel (exit 4) [read], and nd-supervise "exits when
  the child does" (nd-supervise.rs:6) [read]. So at every fuel restart, every frame queued in the
  channel and the stdin pipe is lost, and every client connection drops. That is not just one carried
  frame. → D4.
- **K-O4b. `Tally` + `record_total` + `record_names_bounded`, as decorators over `Store`/`Port`**, and
  the `requests = replies` identity as a host-sim check (`FAIL unanswered`). The theorem-shaped
  identity found F1; the timing found nothing. `Obs.lean` axioms: propext/Classical.choice/Quot.sound
  [scout-ran].
- **K-O4c. The BAR line, as a standing field that is pass/fail against THE BAR's absolute numbers**
  (≤ 5 s write, ≤ 60 s cold reopen), never a ratchet. [ran] `TMPDIR=<scratch> obsrun bar 1000`
  printed `BAR n=1000 store=file write_max_us<=16384(<=5000000) reopen_ms=7.8(<=60000) => PASS`. It
  ran over `World Nat`, toy digests and no signature verification, so it is NOT the deployed BAR: the
  deployed fold verifies Ed25519 at 381 µs/Turn [read HOST-14].

**Discard / change.**
- **The `<store>/status` file rewritten at each fuel return.** At HOST-3's `fuelBatches = 2^24`,
  fuel never returns in practice, so the file would always read STALE. It also adds a second write
  path into STORE. Replace it with `host check STORE` (D6), which opens from disk, is authoritative,
  and works while the writer is down, plus one `STATUS` line on stderr at each seal and at exit
  (which reaches the service manager's log).
- **Latency histograms anywhere in a ratchet.** O4 agrees, and GATES-9 already forbids it [read].
- **`ObsRun`'s `drive`.** It is a stand-in supervisor; HOST-3's Cli is the real one.

### O5 — Linux standing + bwrap (verdict: assemble the fix list; one item rejected)

**Keep.**
- **K-O5a. `--unshare-user` before `--disable-userns`.** [scout-ran on burst5-a: confine 3/3 and
  supervise 2/2 after the patch, red before it] The code at :231-232 has no `--unshare-user` [read].
- **K-O5b. Ban `IO.FS.createTempFile`/`createTempDir`/`withTempDir`.** [ran] On THIS Mac, a
  four-line `try … createTempFile … catch` under `TMPDIR=/nonexistent lean --run` exits **139 with no
  output**. So it is not Linux-only. Lean v4.30.0 kills the process below any theorem: law 7 broken
  by the toolchain. Host/Sim/File.lean:67,112 call `withTempDir` [read].
- **K-O5c. A named `ConfineError` for "bwrap present, userns not permitted"** (AppArmor
  `restrict_unprivileged_userns=1`, the stock Ubuntu 24.04 default). `MechanismMissing` covers only a
  missing binary [read lib.rs].
- **K-O5d. `standing.sh` refuses a parentless commit by name.** Today `base=… || echo "$empty_tree"`
  (standing.sh:21) turns it into a wall of owner reds [read].
- **K-O5e. The `linux-standing.sh` shape** (a `--depth 2` clone so HEAD^ exists, a warm cache
  preserved, `timeout` + `time -v`, a DEST allowlist), for the day ROOT allows boxes. Numbers
  [scout-ran]: cold 2:52, warm 9.1 s, max RSS 9.6 GB.

**Reject: `Policy.env`.** The Host's one input is its argv (STORE). With temp dirs banned, nothing
I can find needs an environment variable [assumed: O5's sims needed only `TMPDIR`, for `withTempDir`].
An env field is a second input channel beside argv (law 1), and it is exactly where hidden couplings
live. Fix the real disagreement instead: on macOS a variable set on the returned `Command` reaches
the child, and on Linux `--clearenv` erases it [scout-ran]. Make "the child's environment is empty"
true on both platforms, with a plant (the caller sets `X=1` on the returned Command; the child must
not see it). CLIENT chooses how, for example by returning a wrapper that does not expose `.env`.

**Process note.** O5 ran on burst5-a, but the charter's working rules say "No box builds until ROOT
says" [read]. Its facts stand. The builder below runs nothing on any box.

## 2. Interface decisions (owner · real signature · both critiques)

**D1 — No world-carry; flag day = re-genesis (ROOT/charter law 1, no code).**
- *Critique:* once friends hold data, a flag day destroys it, and "re-genesis is free" stops being
  true in the product sense.
- *Meta-critique:* I am applying the law as written because it is the law. The scout spent its effort
  on the hard part I am declining. The day a deployment holds data that matters, this is Ember's call,
  and O2 is the starting point.

**D2 — The Store refuses to load an old shape (HOST owns; CODEC supplies `Tag.of`).**
- *Shape:* genesis writes, and every base carries, `shapes : Digest :=
  Hash.digest "nanodregg/host/shapes/v1" (Tag.of "world" world ‖ Tag.of "record" recordCodec ‖
  Tag.of "base" (Base.codec world))`. Open compares it with the running build's value before
  decoding anything: `StoreFault.shapeMismatch (stored running : Digest)`, by name, nothing truncated.
- *Signature change:* `Base` gains `shapes : Digest` (Host/Base.lean:30), checked in `Base.read`
  before `Base.codec.decode`.
- *Plant:* edit one field of the World codec, so its Shape changes, then open a Store written before
  the edit: `shapeMismatch`. Without the stamp, the same plant should show `baseUndecodable` or a
  silent misdecode [assumed: not ran].
- *Critique:* a kernel SEMANTICS change with no shape change (a new admit rule) is not caught. The
  base loads and the tail folds under new rules. The follower's `eventMismatch` is the only detector.
  A hand-bumped semantic epoch would catch it, but that is the version literal Codec/Tag.lean
  deliberately abolished.
- *Meta-critique:* I chose the mechanism CODEC already built because it exists, and I declared the
  semantic case absent rather than design for it.

**D3 — Signed calls bind the World they were signed for (KERNEL owns; CODEC the call codec; PROTOCOL the row; HOST's genesis verb).**
- *Proposed:* `structure Unsigned (D) where world : D; member : D; …` (Call.lean:65). `world` is the
  World's GENESIS chain, `E.hash domGenesis name` (World.lean:147), kept in a new field
  `World.origin : D` because `chain` moves.
  - Derive refuses `.wrongWorld` by name before the signature check. `Refusal.name` gains it, with
    `name_injective`.
  - `host genesis` draws 32 OS-random bytes into NAME (`name := operatorLabel ‖ nonce`). Then two
    Stores on one box, and two genesis runs of one Store, never share founder ids or origin.
  - Row: a call admitted in World A, replayed into World B (same label, same founders, a re-genesis)
    → `wrongWorld`. Plant: delete the check → the row admits it.
- *Alternative:* only a random NAME, with no signed field. Founder ids then differ, so every old call
  names an `unknownKey` member. That is the "accidental" immunity O2 observed. It needs no wire
  change, but it holds only while every member id stays name-derived. A later change to
  `id = H(key)` would reopen replay silently, and nothing would go red. That is the minted class "a
  hardening commit disarms a guard".
- *Critique of the signed field:* 32 bytes per call, a call-codec change, and a re-emit of every
  row's fixture calls. A **genuine fork**: KERNEL decides, and ROOT rules if KERNEL prefers the
  property plus a theorem (`replay_other_world : w₁.origin ≠ w₂.origin → …`).
- *Meta-critique:* I found this by reading genesis for the ops flag day, not by attacking the
  kernel. I have NOT run it. The first thing the builder does is turn it into a red row (brief, step 2).

**D4 — Fuel restart is in-process; no frame is ever dropped (HOST owns).**
- *Signature:* `Exit.fuel (carry : Option Frame)`. `serve`'s base case becomes
  `| 0, r, carried => finish (.fuel carried) r` (Host/Loop.lean:187).
- *`host serve` main:* `loop: openWriter-or-reopen → serve fuelBatches r carry → on .fuel c: reopen
  from disk through the SAME `openAt` (lock held: the lock IS the append handle, Store.lean:7) and
  continue with the same channel and carry c`. The process exits only on a restart-class or fatal
  exit. This is the "resident's top-level fuel-and-restart loop" of law 4, in Lean.
- *With it:* fuelBatches can drop to, say, 2^12, so reopen really "runs routinely" (Loop.lean:17) and
  no connection notices.
- *Host-sim obligation:* `requests = replies` at every fuel return. O4's run with fuel 3 is the plant.
- *Alternative:* keep the process exit and teach nd-supervise to respawn the child while holding the
  sockets. *Critique of that:* Rust would then hold a restart policy (law 2 pressure), the frames in
  the dead child's pipe are still lost, and the supervisor gains state.
- *Critique of D4:* an in-process reopen exercises the open path but not a fresh process, so leaks or
  fragmentation are never reset by fuel. The reader task outlives the restart, so a bug in `pump`
  persists.
- *Meta-critique:* I prefer it because it keeps Rust dumb, a value I hold strongly. I have not
  measured reopen time under load.

**D5 — The exit table is Lean data with classes, emitted (HOST owns the table; OPS renders units from it; CLIENT's nd-supervise passes statuses through).**
- *Signature:* `inductive ExitClass | done | restart | fatal`, `def Exit.code : Exit → UInt8`,
  `def Exit.cls : Exit → ExitClass`, the open refusals (`StoreFault.code/cls`), and
  `theorem code_injective` and `theorem restart_fatal_disjoint`.
- *Classes:* `restart` = {uncertain, sealFailed .io}. `fatal` = {usage, every open refusal (corrupt,
  baseCorrupt, badKey, locked, shapeMismatch, exists), sealFailed .worldTooLarge, recordTooLarge}.
  KERNEL-18's `fold_world_weight` and batchBytesMax should make the last two unreachable, so if they
  fire it is a defect, not load.
- *Change asked of HOST-3:* split today's single `5 sealFailed` by fault, and drop `4 fuel` (D4).
  nd-supervise's own 2 (refusal) and 70 (child malformed) are CLIENT's and are fatal. They join the
  table as CLIENT rows, emitted into generated.rs, so the units read one table.
- *Critique:* launchd cannot honor `fatal`, so the table is only half-enforced on macOS (accepted
  above).
- *Meta-critique:* one more emitted table for two consumers. It earns its place only because systemd
  needs exact numbers and a hand-copied list is a twin.

**D6 — `host check STORE [--anchor HEIGHT:CHAIN_HEX]` (HOST owns the verb; OPS owns the runbook use).**
- *Signature:* `openFollower` (Store.lean:104) with the writer's `foldStep`, writing nothing, then
  ONE line `STATUS height=… chain=… base_offset=… base_height=… seg_bytes=… torn=…`. With an anchor:
  `behindAnchor (height anchor)` if height < anchor; `chainMismatch` if the height is reached but the
  chain at that height differs. That second check needs the chain at a past height, which the HOST-17
  index carries (`Entry` = height, offset, chain) [read, HOST-3 worktree].
- *Exits:* fatal class on refusal, 0 otherwise.
- *What it replaces:* O3's restore verifier, O4's status file and O4's status reader. It is the same
  open the writer runs, not a second shape.
- *Critique:* it trusts the base, because it re-derives nothing, unlike `host follow`'s audit. So it
  certifies integrity and height, not that the history was lawful; that is the follower's job. An
  anchor is only as good as its source. Without one, a rollback to an older complete copy passes,
  and the output must say `anchor=none` rather than imply completeness.
- *Meta-critique:* merging status into check is parsimony I like. An operator may still want live
  in-memory counters, which only the stderr STATUS line gives.

**D7 — Backup = an ordered copy of the three files; restore = copy back + `host check --anchor` (OPS documents and plants it; no new code beyond D6).**
- *Order:* `key`, then `base.world`, then `seg.log`.
- *Why the order is safe:* the base is replaced by rename (Store.lean:58-72), so a reader holding the
  old inode keeps a consistent old base. The segment is append-only, so a later copy of it is a
  superset of every base's offset. A torn last frame in the copy is the writer's unsynced frame, and
  opening the copy treats it as torn [read; the live-copy race itself assumed, not ran].
- *Anchor:* comes from a member's follower (its own fold's head) or from the highest receipt a
  client holds.
- *Not covered:* rebuilding a Store from a follower's records under a new key. That is a declared
  absence, and HOST-4a already calls media failure "replication, not the Store" [read].
- *Critique:* the copy is plain `cp`. A copy tool that reorders or sparse-copies breaks the argument,
  and only the plant (copy during a live `host-file-sim` run, then `host check`) can show the argument
  holds.
- *Meta-critique:* I removed O3's manifest because HOST-16 makes it forgeable. That would be wrong if
  ROOT ever moves the Store key out of STORE.

**D8 — Observability (HOST: Tally decorator, `unanswered` sim check, stderr STATUS at seal/exit; GATES: `bar=` standing field; OPS: the BAR driver).**
- *BAR driver:* runs the REAL `host serve STORE` with the deployed `Ctx`, over its stdin/stdout in
  `Host.Wire` frames, with N signed submits built by PROTOCOL's row harness (imported, not copied).
  It measures the max reply latency and the `host check` cold open, and prints
  `BAR n=1000 write_max_ms=… reopen_ms=… => PASS|FAIL`.
- *Critique:* it measures the loop and the disk, not two friends over ssh. The 5 s bar is ~150× above
  O4's toy measurement, so the field will be green for a long time and may hide a 10× regression.
  That is why it is a BAR check and not a ratchet; WASTE stays the ratchet.
- *Meta-critique:* the tally exists because the scout built it, and the one useful thing it found
  (F1) needed only the `requests = replies` count.

**D9 — Sandbox and toolchain (CLIENT: `--unshare-user`, `ConfineError::UsernsDenied`, the empty-env plant; GATES: the temp-dir ban rule; HOST: Host/Sim/File.lean takes its directory as an argument).**
- *Ban rule:* `gates/refusals.py` refuses the three names tree-wide, and a plant (add one call) goes
  red by name.
- *Upstream:* filing the 139 reproducer with Lean is a public act (pause item 3). That is Ember's.
- *Critique:* banning names does not stop another runtime abort path, and seccomp is still absent
  (O5).
- *Meta-critique:* I rejected `Policy.env` on a search I could not complete. If some child needs a
  variable, CLIENT will reopen this with the variable's name.

**D10 — Unit topology (OPS renders; CLIENT-12 B decides the bridge).**
- *Writer's node:* `nd-supervise /run/nd/host.sock --write STORE --hide … -- /opt/nd/bin/host serve
  STORE`, plus one `nd-attach` forced-command line per friend key, once CLIENT builds it.
- *Member machine:* `nd-supervise ~/.nd/ws/follow.sock --write ~/.nd/follow-store --hide ~/.nd/ws
  … -- host follow ~/.nd/follow-store MEMBER GRANT`.
- *Hosted resident (Hermes):* a member on the writer's box, with its own custody, its own follow
  unit and its own Store.
- *Critique:* nothing here has run on Linux or under systemd (systemd-analyze is absent on this Mac).
- *Meta-critique:* this follows CLIENT-12 B, which I did not re-argue.

**D11 — `standing.sh` refuses a parentless commit by name (GATES).**
- *Change:* replace the `|| echo "$empty_tree"` fallback with `STANDING <sha> => REFUSED(noParent)`.
- *Critique:* the root commit of a fresh clone can no longer be judged at all. That is correct: no
  delta gate can judge it.
- *Meta-critique:* this only bit a scout. It is cheap, so it is cheap to be wrong about.

## 3. Charter rows

**New lane: OPS (BUILD-OPS).**
- *Owns:* `Ops/` (Lean: the unit renderer, the Node values, the BAR driver, and their `Ops/Proofs/`);
  `ops/` (the generated units, `ops/RUNBOOK.md`, `ops/live/` scripts); `decisions/ops.md`; the
  `emit-units` and `bar` lean_exes.
- *Must never:*
  - decide anything that HOST, KERNEL or CLIENT decides: no second Exposed check, no restart
    policy of its own (it renders HOST's table), no Store parsing outside `host check`;
  - touch a service manager or any box beyond `ops/live/` in a scratch directory on this Mac;
  - hold, generate or copy key material;
  - delete a Store.
- *First deliverable:* the cross-World replay row as a RED reproduction, handed to KERNEL/PROTOCOL.
  Then `Ops/Units.lean` + `emit-units --check` + a generated.tsv row rendering the writer and member
  units from HOST's exit table. Then `ops/RUNBOOK.md` (genesis, start, backup, restore, re-genesis,
  what refuses and why).
- *Needed from GATES first:* add `ops` to `scripts/worktree`'s layer list, and `Ops/`, `ops/`,
  `decisions/ops.md` → OPS rows to gates/OWNERS.

**New deliverables on existing rows.**
- **HOST:** D2, D4, D5, D6, the D8 tally/STATUS work, and the D9 `File.lean` directory argument.
- **KERNEL:** D3, the signed `world` field and `World.origin`, or the theorem alternative.
- **CODEC:** the call-codec field for D3, and `Tag.of` consumers for D2. The code exists.
- **PROTOCOL:** the `wrongWorld` row and its plant, and the re-emit of fixture calls.
- **CLIENT:** D9's `--unshare-user`, `UsernsDenied`, the empty-env plant and the "NEVER RUN" line;
  nd-supervise's 2/70 joining the emitted exit table.
- **GATES:** D9's ban rule, D11, the `bar=` standing field, a generated.tsv row for `emit-units`, and
  (when ROOT allows boxes) a Linux confine stage running `cargo test --test confine --test supervise`.

## 4. Risks (what gets worse)

- **D3 is a flag day:** every signed fixture in the rows and sims changes and must be re-emitted. If
  KERNEL takes the theorem route instead, the guard is a property nobody watches until a theorem
  pins it.
- **D4 moves the restart into Lean:** a hang in the in-process reopen now wedges the resident with
  its socket held open, where a process restart would have shown up as a service-manager restart.
  The stderr STATUS line is the only sign.
- **D7 rests on `cp` semantics and one untested race.** Until the live-copy plant runs, "backup is
  three files" is an argument, not a fact.
- **D6 without an anchor** looks like a verification and is only integrity. A runbook that omits the
  anchor step teaches operators to trust a rollback.
- **One more emitted table (D5) and one more lane (OPS):** more surface for the size ratchet and one
  more writer in a seven-agent tree. OPS's owned surface must stay small, or it becomes the "ops
  utilities" hub minidregg had.
- **HOST-3 is mid-build on exactly these files** (Cli.lean, Loop.lean, Store.lean). D4, D5 and D6
  land on its desk at the moment it is busiest. Routing them through OPS as CROSS-LAYER commits
  would collide, which is why the brief routes them as asks.
- **macOS remains half-supervised** (launchd restarts fatal exits). Anyone who tests only on the Mac
  never sees systemd's `RestartPreventExitStatus` behavior.
- **BAR=PASS for a long time** may read as "performance is fine" while the deployed path (ssh, mux,
  Ed25519, ML-DSA if CLIENT-11's hybrid lands) is unmeasured.

## 5. FIRST BUILDER BRIEF — BUILD-OPS (Opus)

You are BUILD-OPS for nanodregg. Your job is the operator's path: genesis, units, backup/restore,
status, the BAR measurement. Almost all of it consumes other layers' decisions; you decide almost
nothing. Read, in this order: `~/dev/nanodregg/CHARTER.md` (whole);
`~/dev/redregg/work/nanodregg-scout/ASSEMBLY-ops.md` (this file, whole: your decisions D1–D11 and
the reasons); `decisions/host.md` HOST-4a, HOST-8, HOST-12, HOST-14, HOST-16, HOST-17;
`decisions/client.md` CLIENT-9, CLIENT-12; `decisions/gates.md` GATES-7, GATES-8, GATES-9;
`Host/DESIGN.md`.

**Repo rules.**
- Repo `~/dev/nanodregg`, main only. Read the code with `git show main:<path>`. The primary
  checkout's working tree is STALE (thousands of lines behind main): never read it, never build in
  it.
- Once GATES adds `ops` to scripts/worktree, work ONLY in `~/dev/nanodregg-wt/ops`. Until then, ask
  ROOT for the charter row and GATES for the OWNERS rows (`Ops/`, `ops/`, `decisions/ops.md` →
  OPS), and build in a private scratch clone (`git clone --no-local ~/dev/nanodregg <your
  scratchpad>/nd`), never in someone's worktree.
- Commit ONLY with `scripts/commit -F MSGFILE PATH...`, subject `ops: …`. Write the message with a
  quoted heredoc (`<<'EOF'`). Add a `SIZE: <exact metric>: <why>` line per risen metric. Add your
  `lean_lib Ops` entry in the same commit as your first `.lean` file.
- Decisions go in `decisions/ops.md`, each with both critiques (law 10).
- Build your closure with `lake build Ops` (and `lake build host` once HOST-3 lands it). Run named
  exes only. No unfiltered test suites, no `cargo test` without `--test <name>`.

**Box safety (verbatim from the user's standing rules).**

> ## Stopping processes: PID file or nothing (incident 2026-10-10)
>
> A subagent ran `pkill -f "cat" -u ember` to clear its own stuck `cat`. `-f` matches the whole
> command line, every app lives under `/Appli**cat**ions`, and 44 of my apps and agents got SIGTERM.
> - **Never kill by pattern.** No `pkill -f <anything>`, no `pkill -x <bare word>`, no `killall`, no `kill -u`.
> - **A process you started is stopped by the PID in its PID file**, and only that. Every detached job
>   writes one (`nohup ... & echo $! > job.pid`). No PID file, no kill: tell me instead.
> - If you must look first, `pgrep -fl` and read the list; it is never the argument to a kill.
> - Every subagent brief you write quotes this block verbatim.

- No box builds of any kind (burst*, hbox, persvati) until ROOT says.
- Disk pressure is Ember's: stop, report a ranked `du`, delete nothing.
- launchd jobs you bootstrap are labelled `software.ember.nd-ops-*`, booted out by label at the end
  of every run, and listed in your log.
- Never put a real seed in `ops/live/`.

**Step 1 — talk before you build.** Send these asks, each in the owner's own words, citing this
file's section:
- HOST-3 (it is building `Host/Cli.lean` right now): D4 (Exit.fuel carries the frame; in-process
  fuel restart; no exit 4), D5 (the exit table as data with classes + `code_injective` +
  `restart_fatal_disjoint`; split sealFailed), D6 (`host check`), D2 (the shape stamp), D8 (Tally
  decorator + `FAIL unanswered` in host-sim + stderr STATUS at seal/exit), and D9's
  Host/Sim/File.lean directory argument.
- KERNEL: D3, with the fork stated.
- CLIENT: D9.
- GATES: D9 ban rule, D11, `bar=`, the OWNERS/worktree rows.
- PROTOCOL: the `wrongWorld` row.

Reachable ids, which may be stale (route through ROOT = `main` if they fail): CODEC
`aca5ce91ec8e30814`, GATES `ab554f1302ac0f14d`, CLIENT-2 `a1612c507f0ff2b93`, PROTOCOL
`a45ff664477fefd42`. KERNEL and HOST-3: via ROOT.

**Step 2 — the first deliverable: make §0.3 red.** In your scratch clone, write a Lean driver
OUTSIDE the tree that:
1. builds `Receive.genesis X "w" A founders` twice with the same name and founder keys, using the
   deployed `Codec.Deployed.ctx` and the signing the rows use (PROTOCOL's Loopback harness;
   import it, do not copy it);
2. signs and admits one `create` pinned only on a founder cell in World 1;
3. submits the SAME call bytes to World 2.

If it admits, you have the reproduction: send it to KERNEL and PROTOCOL as the row text plus your
driver path. If it refuses, report the refusal name and retract §0.3 in this file's successor. Do
not land a fix in Kernel/; it is KERNEL's.

**Step 3 — `Ops/Units.lean` + `Ops/Proofs/Units.lean` + `lean_exe «emit-units»` (root `Ops.Main`, main only).**
- Input: a `Node` (platform, user, bin, store, sockDir, hidden), HOST's exit table (until it is
  data, a PENDING line, never a copied list), and nd-supervise's argv grammar.
- Output: `ops/units/linux/nd-host-serve.service`, `ops/units/linux/nd-host-follow.service`
  (member machine), and `ops/units/darwin/*.plist`.
- `emit-units --check DIR` and a `gates/generated.tsv` row.
- Theorems: the rendered `RestartPreventExitStatus` list = the table's fatal codes; the rendered
  argv = nd-supervise's grammar applied to the node; restart and fatal are disjoint. These are
  statements over the table, not over hand lists.

**Step 4 — `ops/live/launchd-row.sh`** (lift O1/live's shape: bootstrap, bounded wait with a
deadline, bootout, PID file), run against the REAL `host serve` once HOST-3 lands it. It must report:
- whether the deny-by-default sandbox floor (CLIENT-9) suffices for the real Lean resident (O1 could
  not tell, because it used a C stub);
- that exit 3 is restarted;
- that a fatal exit is throttled and logged by name.

**Step 5 — `ops/RUNBOOK.md`:**
- genesis (with D3's nonce);
- start;
- backup (D7's order);
- restore + `host check --anchor`;
- re-genesis (stop units; the operator moves the old Store aside by hand; genesis again);
- the full refusal table with each name and what the operator does about it.
Every command in it must have been run by you, or be marked PENDING with the owner.

**Step 6 — `Ops/Bar.lean` + `lean_exe «bar»`:** D8's driver over the real `host serve` with deployed
signing. Then ask GATES to add `bar=` to standing.

**Lift from the scouts (restate, do not copy verbatim into the tree):**
- O1 `Deploy.lean`: the systemd/launchd text in `systemd`/`launchd`, the `xml` escaper, and the
  exit-table idea + `restart_fatal_disjoint`.
- O1 `live/`: the harness shape.
- O3 `Backup.lean`'s plant LIST, rewritten against HEAD's three-file Store as `host check` rows.
- O4 `Obs.lean`: `Tally`, `record_total`, `record_names_bounded`, `plant_badName`. This is for HOST
  to lift; offer it.
- O4's `obsrun mem 200 3 … 200` as F1's reproduction.
- O5 `sandbox-linux.patch` hunk 4 only (`--unshare-user`), for CLIENT.
- O5 `Tmp.lean` (the 139 reproducer), for GATES' ban plant.
- O5 `linux-standing.sh` (shape), for later.

**Ignore:**
- O1's `Node.exposure`/`structural`/`nameable`/`plant_*`, `only_serve_writes`, the
  follow-on-the-writer's-Store topology, the invented codes 64/65, and "exit 0 on fatal".
- All of O2 (Carry.lean, Demo.lean, Perf*.lean), except the two findings already routed as D2/D3.
- O3's Manifest, multi-segment chaining, the toy `keyed` sealer, and "key outside the backup".
- O4's `drive`, the status file, and the latency histogram as anything but a stderr field.
- O5's `Policy.env` hunks and its `TMPDIR = first --write` convention.

**Report to ROOT on events only:**
- §0.3 reproduced or refuted;
- the units emitted and gated;
- the launchd row against the real `host serve`;
- the RUNBOOK's first fully-run path;
- your handoff (`~/dev/redregg/work/OPS-LOG.md`, before 350K tokens).
