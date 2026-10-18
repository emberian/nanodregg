# decisions/host.md — BUILD-HOST

HOST-1..7 are in the frozen top-level DECISIONS.md (status: HOST-1 gap ruled into CHARTER; HOST-2 provisional; HOST-3, HOST-4, HOST-7 accepted; LAW-4 amended, all by ROOT 2026-10-16). Moved here from DECISIONS.md, where a17339d added them after the freeze (fix forward):

## HOST-4a · what SQLite gave for free that the flat log now owns (BUILD-HOST, 2026-10-16, per ROOT's ruling)
ROOT accepted HOST-4 with the torn-tail theorem and the recover-from-any-prefix plant as the landing
condition. These are the things SQLite did for us, and who does each now:
- **Page/record checksums.** SQLite (WAL frames) checksums every frame. Ours: every record carries a
  32-byte MAC chained over the previous tag, so a flipped bit is a named refusal and so is a
  reordered or spliced frame. Cost: one MAC per batch, not per Turn.
- **Atomic replace.** SQLite's journal/WAL makes a transaction all-or-nothing. Ours: a batch is one frame;
  a frame either verifies or is the torn tail; the checkpoint is tmp → fsync → rename → fsync(dir),
  and open never trusts a checkpoint whose MAC fails (it falls back to the previous one and its segments).
- **Concurrent readers during writes.** SQLite's WAL gives readers a snapshot. Ours: segments are
  append-only, so a reader (the follower, `host follow`) reads up to the last complete verifying frame
  and treats an incomplete last frame as *not yet written*. It never truncates; only the lock holder may.
- **fsync discipline per platform.** SQLite knows `F_FULLFSYNC` on Darwin and directory fsync on Linux.
  Ours: `Host/c/file.c` uses `fcntl(F_FULLFSYNC)` on Darwin, `fdatasync` elsewhere, and fsyncs the
  directory after create and rename.
- **Single-writer locking.** SQLite's file locks. Ours: `flock(LOCK)` held for the writer's lifetime.
- **Not owned by anyone (absent in both):** media failure (a dead disk). That is replication, not the Store.
**Status.** ruled by ROOT 2026-10-16 (HOST-4 accepted with this list required).

## HOST-7a · thin consent is a DECLARED ABSENCE, not a deletion (per ROOT, pending Ember's product ruling)
Members who cannot follow the log (no read access to the segments, or too little CPU to fold them) have
no consent path in nanodregg today. That is recorded as an absence in the spec. `host follow` is the
only consent code; if Ember rules thin members in, their path must be a client of `host follow` run
somewhere they trust, not a second verifier.
**Status.** open (product ruling: Ember).

## HOST-8 · lookup answers `absent`; resubmitting the same bytes is idempotent (BUILD-HOST, answering proposals/client.md §3)
**Decision.** Reply status byte: `0 ok · 1 refused · 2 uncertain · 3 absent`. `lookup txId` answers `ok`
with the receipt if the txId is in the World's journal, `absent` otherwise. The Host keeps no record of
refusals, so `lookup` never answers `refused`. A `submit` whose txId is already journaled is answered
`ok` with the original receipt, not admitted twice. That is KERNEL's journal theorem (`admit` refuses a
journaled txId by name, `Reject.replayed`, and the World is unchanged). The loop maps `replayed` to the
original receipt; the loop adds nothing.
**Two facts the client must not over-read.**
1. *`absent` is not final.* Across connections the supervisor does not order frames, so a send that was
   still queued can commit after a lookup said `absent`. Resending the same bytes is safe because of the
   theorem above. Sending *different* bytes for the same intent is what custody must never do (CLIENT-3).
2. *`absent` becomes final only by expiry.* Once `World.height > t.validUntil` and the txId is not
   journaled, no later `admit` can journal it. **Asked of KERNEL:** `theorem absent_final : w.height >
   t.validUntil → t.txId ∉ w.journal → ∀ w' reachable from w, t.txId ∉ w'.journal ∨ …` with the shape
   KERNEL prefers. The loop then answers `absent` together with the World height, so the client can tell
   "absent, may still commit" from "absent forever".
**Batch ordering.** Two identical submits in one batch: the first is staged, the second gets `replayed`
against the staged World, and both replies wait for the same fsync. Identical bytes can never be
admitted twice, whatever the batch boundaries.
**Critique.** Keeping no record of refusals means a client whose submit was refused, and whose reply was
lost, sees `absent` until the call expires, when it could have been told `refused` at once. Remembering
refusals is state outside the World, unbounded unless it is capped, and not replayable by the follower,
so it stays out. The cost is latency only on the rare lost-reply path.
**Meta-critique.** "The World is the only state" is a rule I hold strongly. Here it decides a UX question
I have not measured.
**Status.** open.

## HOST-9 · the step protocol between `host follow` and `nd` (with PROTOCOL; answering CLIENT-2)
**Decision.** `nd` sends `command(argv)`. `host follow` answers one step:
`done(exit, stdout, stderr) | sign(message) | host(op, payload) | submit(call)`, each carrying a
continuation `k`. `nd` executes the step and sends `resume(k, result)`, where the result is a signature,
the Host's reply frame, or the attempt outcome. Follow is stateless between steps: `k` is a
CODEC-encoded `Follow.State` (≤ `continuationBytesMax`, one canonical decoder, refused by name past the
bound), so a command survives a follow restart and a reconnect. The step tags and the bounds are rows in
PROTOCOL's generated table, and Rust reads them from the generated file.
**No MAC on `k`.** `k` travels only between follow and the member's own custody. A party that can forge
`k` holds the seed already. Follow also never trusts `k` for a fact it can read from its own World: `k`
names *where* the command is (which step, which plan digest), and every plan is re-derived at resume.
Theorem target (follow's): `resume_rederives`: the `sign` step follow emits after a resume is a function
of follow's World and the command alone, never of `k`'s payload bytes beyond the step index.
**Critique.** This adds a round trip per signature, which the client already flagged on the BAR path. If
`resume_rederives` holds, `k` only carries a step index and a digest, and a fixed generated sequence per
command would do the same job with no continuation codec. That would be fewer moving parts. The
continuation earns its place only for commands whose step sequence depends on what the Host says.
**Meta-critique.** I adopted CLIENT's framing because ROOT endorsed it. I have not shown that any command
in the journey rows actually needs a data-dependent step sequence.
**Status.** superseded by PROTOCOL-0..7 (Protocol/Table.lean: the step tags, statuses and client bounds are PROTOCOL's table; Host consumes them and defines none). `resume_rederives` stays an obligation, now of PROTOCOL-4 (`Receive.rederive`).

## HOST-10 · checkpoints are incremental: a base plus delta records in the same framed log (BUILD-HOST, per K1 / 617bb3a)
**Decision.** A segment holds two kinds of record under the one `Host.Log` frame and tag chain:
`batch` (the batch's Turns) and `delta` (for every cell touched since the previous delta: its post bytes or
"retired", plus the system cell, at a height). The loop emits a delta when the batch bytes since the last
delta reach `deltaEveryBytes`. That costs O(cells touched), from a touched-set the loop accumulates out of
each admitted Turn's `creates`, `legs` and `retires`. A **base** (`base-<h>.world`, the whole World,
encoded by CODEC) is written by a background Task over the immutable World value once the delta bytes
since the last base exceed the base's own size. The base is never written on the loop. Its cost is O(store)
once per O(store) bytes appended, which is amortised O(touched). **Recovery:** take the newest base whose
MAC verifies; apply the delta records after it in order (overwrites, no re-execution); then fold the
batches after the last delta with `World.admit`. The torn-tail theorems (`recover_torn`,
`encodeAll_recover`) cover delta records with no extra work, because `Host.Log` frames opaque records:
the delta/batch tag sits inside the record and is CODEC's encoding. **Obligations:**
`Delta.apply (World at h) (Delta.of w w') = w'` (KERNEL/CODEC: the delta is the exact difference), and a
pair assertion at the follower: the follower recomputes each delta from its own fold and refuses the
segment by name if the bytes differ.
**Alternatives.** (a) The whole World re-encoded at a cadence `max(sealMin, worldBytes/4)`, which was
DESIGN §5 before K1. That is already amortised O(appended) and runs in a Task, so its real costs are
memory (two Worlds alive during the encode) and an open time bounded by one cadence of Turns. (b) No
checkpoint at all: open folds the whole log, which breaks the BAR's cold reopen at scale. (c) Deltas only,
compacted by rewriting segments (an LSM). That means rewrite IO and a compaction scheduler.
**Why.** K1 forbids O(store) work per batch, and (a) would also have kept two Worlds in memory at every
seal. Deltas make open O(base + deltas + ≤ `deltaEveryBytes` of Turns) and keep the base rare.
**Critique.** Every changed cell is written twice: as a Turn, and in post-state form inside a delta. That
is write amplification ≤ 2× on the hot cells. A delta written by a buggy Host is MAC'd, so the Host would
recover into its own bug, faster than it would by re-execution. Only the follower's pair assertion
catches that, and only when a follower runs. Recovery now has two code paths, delta-apply and admit-fold,
where (a) had one. That is a second shape of "advance the World", which law 1 frowns on. It is justified
only because the delta theorem ties delta-apply to admit, and only once that theorem exists.
**Meta-critique.** I proposed (a) and was overruled by a principle ("O(touched) per batch") that (a)
already met on average. I may now be over-engineering to comply, building LSM machinery for a store that
at THE BAR's 1000 records fits a whole-World encode in milliseconds. The honest test: measure the encode
of a BAR-sized World. If it is under one fsync, (a) is the simpler correct design, and K1 should be
re-argued with that number.
**Status.** open; HOST-14 (the measurement this meta-critique asked for) proposes withdrawing it.

## HOST-11 · how the loop gates `log` and `read` on a follow grant, O(touched) (2026-10-16, answering PROTOCOL-3)
**Decision.** A `log` or `read` request carries a signed envelope: `(key, op, fromHeight or view, validUntil,
signature)`. The signature is over the op byte, the request body and `validUntil`, under the request
domain tag. For each such request, inside `admitBatch` and in arrival order, the loop does three things:
(1) refuses `expired` if `World.height > validUntil`; (2) verifies the signature with the one verifier
(CODEC's; O(1)); (3) looks up the key's grant in the World (`Kernel.Receive.grantOf w key`, a `TreeMap`
lookup, O(log n)), and refuses `noGrant` by name if none is live. Only then does it serve. The check runs
against the World as the batch has advanced it, so a revocation earlier in the same batch already
applies. Serving `log`: the loop keeps an in-memory index `height → (segment, offset)`, one entry per batch
record, appended when the batch's fsync returns. It serves the records from `fromHeight`, read with
`read_at` and bounded by `frameBytesMax` per reply. The follower pages by asking again from the next
height. It serves record bytes, not the frame tags. The tags are the Store key's at-rest integrity check,
which a follower cannot verify. The follower checks the content by folding: chain, roots, and PROTOCOL-4's
`Receive.rederive` of every event. Nothing outside the lookup and the requested bytes is touched.
**Alternatives.** (a) Gate in the supervisor (Rust) by an allowlist file. That is a Rust decision, so law 2
forbids it. (b) A session: authenticate once per connection, then stream. That needs per-connection state
in the loop and a revocation check per frame anyway. (c) No signature on reads, with the socket
permissions as the gate. That makes ssh access the grant and ignores KERNEL's grant receiver.
**Why.** The grant lives in the World, so checking it there is the only check that revocation reaches,
and every term above is O(1) or O(log n), never O(store).
**Critique.** A signature verification per page of `log` is the dominant cost of a cold follow (~10³ pages
for a large log). A one-batch session token would be cheaper. Without a nonce, a replay of a captured
request (same key, same height) inside its `validUntil` window returns the same bytes to the replayer. The
socket is the member's own forwarded stream, so the replayer must already sit on that path; the window
should be short (Bounds). Re-reading served bytes from disk costs one `pread` per page (page cache in
practice).
**Meta-critique.** I took the per-request signature because it needs no state, and I like stateless
loops. I have not measured whether verification dominates a cold follow at THE BAR's scale.
**Status.** open (KERNEL: `grantOf`'s name and shape; CODEC: the verifier and request domain tag).

## HOST-12 · torn vs corrupt is decided by a forward scan, not by size (2026-10-16; found by plant-flip-byte)
**Decision.** Bad bytes after the last verifying frame count as the torn tail only if (a) there are at most
`frameMax` of them and (b) no frame verifies at any later offset. A frame verifies at offset `o` when it
checks against the 32 bytes before `o`; every frame except a segment's first is preceded on disk by the
tag it chains from, so the check does not need the bad frame. Anything else is `corrupt`: the Host refuses
to open and truncates nothing.
**How it was found.** The first rule was "bad region ≤ frameMax ⇒ torn". `frameMax` is ~256 KiB (the
record bound) and the simulated log is 9.4 KB. So `plant-flip-byte`, a single flipped byte in the FIRST
of 59 frames, came back `torn`, and the rule would have truncated 58 acknowledged batches without a word.
The torn-tail theorem stayed true throughout, because it only speaks about cuts of the last frame. The
plant is what caught it.
**Cost.** On the failure path only: per candidate offset one length check, plus one tag over at most
`recordMax` bytes when the length is sane. `recover_torn` gains a premise, `NoFrameInside` (no frame
verifies inside the cut). An unforgeable tag discharges it, and the plants check it on every cut.
**Critique.** The undecidable case remains, and it is stated. A flip inside the LAST frame reads as torn
(`plant-flip-last-frame` asserts exactly this). The data loss is bounded to one batch and is detectable by
receipt holders and followers, but the Host itself cannot tell. Only an out-of-band durable length closes
it, at the price of a second fsync per batch.
**Meta-critique.** I wrote the first rule from the crash model ("at most one unsynced frame") and forgot
that corruption does not follow the crash model. That is the familiar mistake of testing only the failure
you designed for.
**Status.** open.

## HOST-13 · a def-module structure with a proof field proves its instances' witnesses privately (2026-10-16; accepted as cost by ROOT)
**Decision.** `Log.Sealer` carries `tag_size : ∀ b, (tag b).size = tagBytes`, and an instance in a def-module
(`Host.Sim.Toy.sealer`) proves it with a `private theorem` (`size_le64`). The closure gate's C3 rule ("a
def-module exports no theorems") allows private helpers. Do not "fix" this by moving the witness into a
Proofs module: C4 forbids a def-module importing a proof-module, and the instance needs the witness.
**Alternatives.** Drop the proof field and carry the size as a premise of every theorem, which spreads
the obligation to every caller. Or carve an exception into C3 for structure-instance witnesses, which
makes the gate weaker.
**Critique.** Private lemmas cannot be reused across modules, so two instances may prove the same fact
twice. **Meta-critique.** None worth recording: this is a gate's cost, written down so nobody re-litigates it.
**Status.** ruled by ROOT 2026-10-16 (accepted as cost).

## HOST-14 · K1 re-argued with the number: a whole-World base in a Task, no deltas (2026-10-16, HOST-2; ROOT to rule)
**The measurement** (Apple M2 Max, compiled Lean v4.30.0, `~/dev/redregg/work/host-bench/K1.lean` +
`fsync.py`; best of 20 encodes / 30 appends). A BAR World: 1000 data objects (owner digest + one
128-byte state slot) and 1000 journal entries, encoded whole with the `Codec.Stream` combinators into
one buffer:

| records | base bytes | whole-World encode | one append + `F_FULLFSYNC` |
|---|---|---|---|
| 1 000 (THE BAR) | 290 KB | **0.18 ms** | best 3.9 ms, median 6.4 ms (100 B); 4.3 / 7.1 ms (290 KB) |
| 10 000 | 2.9 MB | 2.1 ms | — |
| 100 000 | 29 MB | 40 ms | — |

At THE BAR the whole-World encode is about 25 to 35 times cheaper than the one fsync every batch
already pays. Not measured: the MAC over the base, because CODEC's Keccak is not on main. ESTIMATE, not
a measurement: 290 KB is about 2 100 Keccak-f permutations, which at minidregg's measured ~17 k
instructions per permutation (HP-7) is ~10 ms at BAR, ~1 s at 100×. The MAC, not the encode, is the
dominant term, and it is a cost a delta design pays too, per delta byte.
**Decision (proposed).** Withdraw HOST-10's deltas and keep DESIGN §5 (a): the loop seals when the
bytes appended since the last base reach `max(sealMinBytes, baseBytes / 4)`. It hands the immutable
World value to a Task, which encodes it with CODEC's World codec, MACs it, and writes
`base-<h>.world` (tmp → fsync → rename → fsync dir). Open takes the newest base that verifies, then
folds the batches after it with `World.admit`, and nothing else. There is one way to advance a World
(law 1), no `Delta` type, no `Delta.apply` theorem, and no write amplification.
**Why this meets laws 4 and 5 as they are meant.** No REQUEST does O(store) work. The loop's own cost per
seal is one pointer handoff. The Task's cost is O(store) once per Ω(store) appended bytes, which
amortises to ≤ 4 encoded bytes per appended byte. The one cost that K1's critique ("two Worlds alive
during the encode") named is smaller than it said: the World is a persistent `TreeMap`, so while the
Task holds the sealed value the loop's inserts copy only O(log n) path nodes per touched key. The memory
held beside the live World is O(touched since the seal) plus the transient encode buffer (290 KB at
BAR). Open costs O(base) to decode plus a fold over ≤ baseBytes/4 of Turns.
**Alternatives.** HOST-10 (base plus deltas, as ruled under K1): open is bounded by base, deltas and
≤ `deltaEveryBytes`, but it needs a `Delta` type, a second World-advance path tied to admit by a
theorem nobody has written, ≤ 2× write amplification on hot cells, and a follower pair-assertion to
catch a buggy delta. Or no base at all: open folds the whole log. That fails the 60 s cold reopen only
at a scale far beyond THE BAR, but it fails without bound.
**Critique.** The numbers are THE BAR's. Linear growth means 10⁶ records is a 290 MB transient
buffer and a multi-second MAC per seal: still amortised, still off the loop, but a memory spike that
deltas would not have. My encoder is a stand-in for CODEC's (the same combinators; CODEC's will add
framing and tags, which costs a few percent). The MAC number is an estimate from another system's
Keccak. If CODEC's Lean Keccak is much slower than 17 k instructions per permutation, the Task can
fall behind its cadence at large stores. The design then has to say what happens, and it does: the
next seal waits for the previous Task, and open folds a longer tail. That is correct but slower.
**Meta-critique.** This is the design I proposed first and was overruled on, so I went looking for the
number that vindicates it. The measurement was chosen at THE BAR's scale because the BAR is the spec,
but that choice also happens to be the one that favours (a). The honest residue: (a) is simpler at
every scale and cheaper at the spec's scale; deltas win only past ~10⁵ records, a scale no row exercises.
**Status.** ACCEPTED by ROOT 2026-10-16; HOST-10 withdrawn. Conditions, each to land as code: (1) the
cadence (`sealMinBytes`, the 1/4 ratio) in Bounds, with the amortisation as a theorem or a pinned WASTE
row `seal bytes-per-appended-byte`; (2) `worldBytesMax`, the size at which this design must change, as
a refusal by name with a plant; (3) the MAC measured once CODEC's Keccak lands, and HOST-14 re-read
with it; (4) open reads one base + at most one cadence of log, as a theorem on the open path. Law 5
amended by ROOT: O(store) work is forbidden on the request path; off-loop sealing amortised to
O(appended bytes) with a named cadence Bound is allowed.
**Condition (3), the MAC, re-read (2026-10-16).** CODEC measured `Codec.Hash.mac` (KMAC256, 17c0307) on this
Mac, compiled, one core: 184 MB/s at 1 MiB, and 2.2 µs for a 200-byte message. That makes the base MAC
≈ 1.6 ms at THE BAR (290 KB), ≈ 16 ms at 10^4 and ≈ 160 ms at 10^5 records, and with encode the
whole seal is ≈ 1.8 ms / 18 ms / 200 ms. My estimate from minidregg (≈ 10 ms at THE BAR) was about 6×
pessimistic. The MAC is about one fsync at THE BAR and stays inside the cadence budget at 10^5
(≈ 200 ms of Task time per ≥ 7 MB appended). The decision stands. The number is CODEC's measurement,
not mine. HOST-3 re-measures it against the real base file once the World codec lands.
**Landed (HOST-3, 2026-10-16), with the number on the real base.** The four conditions as code:
(1) `Host.Cadence` (Host/Bounds.lean): `cadence b = max sealMinBytes (b / 4)`, deployed
`sealMinBytes` 1 MiB; pinned WASTE row `seal bytes-per-appended-byte` (host-sim, toy cadence 2 KiB).
(2) `worldBytesMax` 256 MiB: the seal refuses `SealFault.worldTooLarge` by name before encoding
(`Base.file`), the loop stops `sealFailed worldTooLarge` (plant-world-too-large), and open refuses a
base file past one base frame `baseTooLarge` before reading it. The genesis allowance is half of it
(`Host.allowanceMax`), by KERNEL-18. (3) the MAC, measured: below. (4) AMENDED, and here is why: open
reads one base and at most `tailMax b = 2 · cadence b + frameMax`, which is two cadences, not one.
A seal runs in a Task while the loop keeps appending, so when it lands the tail behind the newest
durable base is up to one cadence (the one being sealed) plus whatever arrived meanwhile. Keeping
the tail to ONE cadence would mean blocking the loop on every seal. Instead the loop blocks only when
a frame would cross `tailMax`: it waits for the seal in flight, then seals inline if it must
(`Loop.makeRoom`). `commitBatch` takes `WithinTail` as a proof argument, so no append can happen
without the bound. Theorems (`Host.Proofs.Base`): `openWith_reads` (the one open asks for exactly
`[base offset, segment size)`, at most `tailMax`, and opens to a position inside it), `tailRead_ok`,
`within_after_seal` (after an inline seal any frame fits, so `makeRoom` always makes room).
A base that does not verify is refused `baseCorrupt` and never falls back to an older base or a
whole-log fold. Bases are replaced atomically (tmp → sync → rename → sync dir), so a bad base is
corruption, not a crash.
**The base measured** (Apple M2 Max, compiled, one core, best of 3–10; `~/dev/redregg/work/host-bench/Base.lean`:
`Codec.Deployed.world`, `Host.Base.file` under `Keys.ofKey`, `Base.read`):

| records | base | encode | KMAC256 | seal (Base.file) | open (MAC + decode) |
|---|---|---|---|---|---|
| 1 000 (THE BAR) | 290 KB | 0.78 ms | 0.91 ms | 1.6 ms | 4.1 ms |
| 10 000 | 2.9 MB | 5.2 ms | 9.0 ms | 18 ms | 51 ms |
| 100 000 | 29 MB | 122 ms | 129 ms | 570 ms | 2.6 s |
| 300 000 | 87 MB | 1.5 s | 1.1 s | 3.7 s | 7.0 s (RSS 1.66 GB) |

The MAC runs at ~320 MB/s on the base, better than CODEC's 184 MB/s at 1 MiB. At THE BAR a seal is
about half of one fsync, and a cold open of the base is 4 ms. The decision stands. **What this table
says against it.** RETRACTED (CODEC-14 addendum): I reported encode as superlinear (×12 from 29 to 87 MB).
CODEC re-ran it, one process per size, and it is linear: 0.40 ms / 102 ms / 263 ms. My 3·10^5 row was
first-touch of a fresh 128 MB buffer plus cache variance in one long-running process. The term that
matters is decode, ~20 ns/B (`ofList` rebuilds): 1.57 s at 87 MB, so about 5 s for a 256 MiB base. That
is inside THE BAR's 60 s cold reopen for the WRITER (base + tail; ROOT: that is the bar). A
follower's first audit is O(history) by definition; after it, the follower reopens from its own
sealed base like the writer (ROOT's ruling), so no follower cadence ceiling is needed.

## HOST-15 · thin consent: a member that does not fold the whole log (2026-10-16; Ember ruled IN "if we can get away with it"; with PROTOCOL-14)
**Decision (option A, one code path).** A thin member holds ONE base it trusts and folds only the
log after it, with the same absorb `host follow` runs (every event re-derived, PROTOCOL-4). What it
trusts is the World part of a base: exactly `Codec.Deployed.world`'s bytes at height h. Their digest,
`Hash.digest "nanodregg/host/base/v1"` of those bytes, is a function of the World's contents
(`world_bytes_equiv`), so any full follower can compute it and countersign it. The Store MAC is NOT
part of what a thin member checks: it is the writer's at-rest key (HOST-16). `host serve` answers `read`
(PROTOCOL's read envelope, `Envelope.check`: live member, current key, signature, `validUntil`,
`mayFollow`) with pages of the newest base: `(height, total, digest, bytes[start, start + chunk))`,
with the envelope's `start` read as a byte offset. Each page is one pread, O(chunk). A new seal
between pages changes the stated height and digest, and the member restarts its download. After the base, the member pages
`log` from h like any follower, and asserts height and chain at each page.
**What it trusts.** That the base digest it pins came from a fold it trusts: its own earlier full
fold, or a full follower's countersignature over (h, digest, chain). **What it cannot detect.** Any
history before h: a writer that withheld or rewrote a valid prefix and got a base digest
countersigned. It also cannot detect a countersigner that lies, which is the trust it chose. A
forged cell in the served base is caught (`baseMismatch`, PROTOCOL's plant), because the digest is
over the exact canonical bytes.
**Alternatives.** (B) a Merkle trie over cells with a root per Turn and per-cell inclusion paths.
That is a second state commitment and a second verification path (law 1), and it needs a root in
every Turn that nothing has today.
**Critique.** A thin member downloads the whole base (290 KB at THE BAR, 256 MiB at the top) to read
one cell. For THE BAR that is nothing; past ~10^5 records an inclusion proof is far cheaper, and (B)
becomes the right design. **Meta-critique.** (A) won because the base already exists and I built
it; "one code path" is a law I can cite for the option I prefer anyway.
**Status.** open (PROTOCOL-14 owns the page layout and the `baseMismatch` row; HOST serves it).

## HOST-16 · the Store key is an integrity-at-rest key (2026-10-16; ROOT ruled the custody)
**Decision (ruled by ROOT).** `host genesis` writes `STORE/key`: 32 bytes from the OS random source
(`IO.getRandomBytes`), 0600, created exclusively. `serve` and `follow` read it once at open, refusing
`badKey` unless it is exactly 32 bytes. Segment frames and the base are KMAC256 under it in two domains
(`Host.Keys`: `nanodregg/host/segment/v1`, `nanodregg/host/base/v1`).
**Threat model, exactly.** It protects against corruption, against splicing and reordering frames,
and against frames or bases copied from another Store (plant-foreign-key: a Store under another key
is `baseCorrupt`; plant-foreign-frame: a frame re-tagged under another key is `corrupt`). It does NOT
protect against anyone who can write STORE, because the key is in STORE.
**Law.** Nothing ever derives authority, consent or a member's identity from this key, or from a
tag it made. Authority comes from signatures checked by `Ctx.verify`; consent comes from a
follower's own fold.
**Alternative refused.** A key held by custody (the nd seed) and handed to the child at spawn: that
puts a secret in a log-parsing process (CLIENT-1).
**Critique.** A key that only checks integrity could be a plain hash, but keying it is what makes a
frame from another Store refuse. A key that sits beside the data it protects is easy to mistake
for a security boundary, which is why the law above exists. **Meta-critique.** I proposed the
cheapest custody. It is right only because the key protects nothing an attacker wants.
**Status.** ruled by ROOT 2026-10-16.

## HOST-17 · `log` pages from an index the base carries (2026-10-16, HOST-3)
**Decision.** Serving `log` from any height must not read the segment from offset 0 (law 4: O(page),
never O(store)). The index is one `Entry` per record: (height before, frame offset, chain before).
The loop appends an entry per commit, the base carries every entry before its offset, and open
rebuilds the tail's entries during its own fold (`Open.indexed`). A page is located by binary search,
read frame by frame with each frame's MAC verified (`corrupt` by name, never served), and the
chain is advanced Turn by Turn from the entry's chain. So a page may end inside a record and still
state the exact chain after its last event (PROTOCOL's pair assertion). The page is built after
the batch's sync, so it holds durable records only. `log` is gated by `Envelope.check` against the
in-batch World, so a revocation earlier in the batch applies.
**Alternatives.** (a) A sidecar index file appended per batch: a second durable artifact with its own
crash story. (b) Heights in the frame header and a scan: O(store) per cold page. (c) Re-derive the
index at open by scanning every frame header: O(records) preads at open, breaking HOST-14 (4).
**Critique.** The index is re-encoded whole in every base: the WASTE row `seal bytes-per-appended-byte`
rose 1.287 → 1.715 at toy scale. At THE BAR it is ~52 bytes per batch beside ~290 bytes per record of
World, so ≤ 1.2× the base. It grows with batches, not with the World, and a long-lived Store with
tiny batches pays it on every seal. An index that is itself a persistent structure (only new entries
written) would remove that, at the price of (a)'s second artifact.
**Meta-critique.** I put it in the base because the base was already atomic and MAC'd, which is
reusing what I just built. That is a convenience argument, not a design argument.
**Status.** open; measured as a count and answered by HOST-30 (2026-10-17).

## HOST-18 · a segment is bound to its base by the tag already on disk: `foreignSegment` (2026-10-17, BUILD-TRANSPORT; ASSEMBLY-transport-consent, with HOST-4)
**The defect.** Open read the segment only from the base's offset and judged what it found with
`Log.recover`. A segment from ANOTHER Store under this Store's base therefore verified no frame,
and `badTail` classified up to `frameMax` bytes of it as the one torn frame: the writer
TRUNCATED it. Measured at 87c721e (plant-foreign-segment.lean): A's 1750-byte segment under B's
genesis base opened `records=0 torn=1750` and the writer cut it to 0; under B's base at offset 5
it was cut to 215. With deployed `recordBytesMax` = 32 MiB, any foreign tail up to 33,554,468
bytes is silently destroyed.
**Decision.** Every base sits after a frame of its own segment, so the 32 bytes before a base's
offset are, on disk, the base's own `tag` (every frame ends with its tag, `Log.frame`; the base
records the chain tag at its offset). `genesisImage` makes this true from height 0: seg.log starts
with ONE origin frame, `Log.frame keys.segment segmentInitial (mark w₀).2` (the genesis chain:
the Store's identity at height 0, so the frame binds the origin once KERNEL/HOST-4 commit the
origin nonce into it), and the genesis base sits at its end. `openWith` reads
`[offset - 32, size)` in its ONE read and refuses `.base .foreignSegment` unless the head is the
base's tag (a base at offset < 32, the pre-HOST-18 shape, refuses the same way: old shapes do not
load). Nothing is truncated on a refusal. Theorems (`Host.Proofs.Base`): `openWith_reads`
(re-stated: exactly one range, `[offset - 32, size)`, tail ≤ `tailMax`), `openWith_anchored` (an
open that succeeds read the base's tag right before its offset), `openWith_foreign` (the plant's
statement over the real `openWith`). Plants: host-sim `plant-foreign-segment` (genesis base and
newest base, offset > 0) and host-file-sim `plant-foreign-segment` (another Store's seg.log copied
over; the writer refuses and the file size is unchanged); both go red with the check removed
(seen: 2 FAILED / 1 FAILED). `Page.frameOf`'s offset-0 branch is deleted: no record is at 0.
**Alternatives.** (a) A clear-text segment header naming the Store, read before the MAC (scout
T1): once a base is sealed open never reads offset 0, so the header goes unread, and decoding
unverified bytes into a refusal brushes law 7. (b) A durable out-of-band segment length: a second
fsync per batch (HOST-12's critique). (c) A per-Store `segmentInitial`: foreign frames ALREADY
fail to verify; the defect is the torn-vs-corrupt classification, which (c) does not change.
**Critique.** It catches a FOREIGN file, not our own segment from a divergent copy (a backup
restored past the base offset): its bytes match up to the offset, and bad bytes after it still read
as torn when ≤ frameMax. HOST-12's undecidable last-frame window stays, and at 32 MiB it is wide;
nobody has questioned the 32 MiB `recordBytesMax`, and the torn window is exactly that bound. The
origin frame's RECORD is never re-verified on open (only its trailing tag is compared), so a flip
inside the origin record goes unseen; it carries no data the open uses. Open now copies the tail
once (`extract` after the single read) to keep `openLog`'s offsets relative; at THE BAR that is a
memcpy of ≤ `tailMax`. Genesis is two durable steps (seg.log, then base); a crash between them
leaves a directory that opens `noBase` and that genesis refuses `exists`: the operator removes it.
**Meta-critique.** I like it because it is small and reuses a tag already on disk (law 1
comfort); that is also why I did not look for a stronger binding (e.g. the base carrying a MAC of
the whole frame before it). The plant came from the evaluator, so the hole it tests is the one
someone already imagined; the divergent-own-copy case above is the one nobody has planted.
**Status.** landed (this commit). Re-genesis: every Store; a pre-HOST-18 base refuses `foreignSegment`.

## HOST-19 · the fuel restart reopens in process; the loop holds no frame between batches; the resident is never silent (2026-10-17, HOST-4; OPS D4 + D8's startup half)
**The defect.** `| 0, r, _ => finish .fuel r` discarded the frame `drain` had carried, and `fuel` exited
the PROCESS (code 4). Every frame queued in the reader's channel and every client connection through
nd-supervise died with it, at a routine restart. The pump's own budget was `fuelBatches` FRAMES and it
reported `eof` when spent, so after 2^24 frames the Host stopped reading and exited 0, silently. Under
the macOS floor without `hw.ncpu` a `.dedicated` task ran inline, so the reader read stdin to its end
before the loop answered anything, and the process exited 0 (PERF's repro).
**Decision.** (1) The carry is deleted. `Port.unread` puts the frame that does not fit back into the port,
so `serve` holds nothing between batches: its signature has no frame argument, and a round can end at
any batch boundary. `drainM` is generic in the monad, and `Host.Proofs.Loop.drainM_conserves` states,
over a list model of the port, `batch ++ port' = first :: port` with a non-empty batch of at most
`max 1 batchMax` frames (OPS's law-6 read asked for the bound: without it a cut could take everything
and still conserve). `Host.Follow.loop`'s base download in progress moved from a recursion argument
into a reference the caller owns, for the same reason: it is volatile state that must outlive a round. (2)
`Host.restarts` is the resident's one fuel-and-restart loop (law 4). On `fuel`, it reopens the Store in
process through `reopenAt` (the one `openAt`, with a fresh read handle; the locked append handle stays
the lock). It refuses `reopenDiverged` unless the reopened (height, chain), segment position, tag and
index length equal what the loop held, and a torn tail at reopen is also `reopenDiverged`. Then it
continues on the same port. `fuelBatches` drops 2^24 → 2^12, so every 4096 batches the open path is
re-checked against the live state. That is a pair assertion that runs for real, not at the next crash.
(3) The bounds are stated. The reader reads `lifetimeFrames` = 2^48 frames and stops `Stop.lifetime`.
`restartsMax = lifetimeFrames / fuelBatches + 1`, because a round that ends `fuel` consumed ≥ fuelBatches
frames, so `Exit.lifetime` cannot come first. The exhaustion case is a theorem, `Host.Proofs.Loop.restarts_spent : restarts round reopen mark 0 r =
pure (.lifetime, r)`: a spent top loop runs no round and exits by name (`lifetime`, class restart, never
silent). This nested bound IS the shape law 4 sanctions (ROOT, 10-17). (4) Never silent. `threadsLive` compares `IO.getTID` of
the main thread with that of a `.dedicated` task and refuses `noThreads` by name (rc 2). Measured under
PERF's floor profile: `refused noThreads`, rc 2, where HEAD hung. One `STATUS serve|follow height= chain=
offset= base_offset= base_height=` line goes to stderr at open and one `STATUS … exit=NAME
refused_queued=N …` at exit. A reader that stopped `truncated`/`badLength`/`readFailed`/`lifetime`
ends `Exit.stream` by name, never `eof`. (5) At every exit, every frame still queued is answered
`refused stopped` (FrameRefusal.stopped: not admitted, safe to resend) after the channel is closed.
**Exit table** (OPS's D5, Host/Exit.lean): reopenFailed 38, reopenDiverged 39 and noThreads 42 are
fatal; lifetime 40 and stream 41 restart (nd-supervise exits with the child, so a restart re-pairs
the pipe). `Status.fuel` (4) stays a constructor because `Exit.fuel` is a round's end, but `host`
never exits with it. `Exit.stream .eof` maps to `stream`, not `eof`, so `Exit.name_of_status` stays true.
**Plants** (host-sim, seeds 1–3): `requests = replies at every fuel return` (a named FAIL line per
round, which is OPS's F1 check); `fuel restarts` (rounds of 3 batches with batches cut by bytes, so
frames go back into the port at round ends: ~30 in-process reopens, the same 200 replies in the same
order as the run without restarts, the same chain); `plant-drop-unread` (a port that drops the put-back
frame loses replies, e.g. 173 of 200, so the check can see a dropped frame); `plant-reopen-diverged`
(a reopen missing the last synced byte stops the resident `reopenDiverged`). host-file-sim runs every
serve in rounds of 5 batches through the real `reopenAt` over the files, and its second writer run
goes through the DEPLOYED `channelPort` (closeable channel + the `unread` slot) with byte-cut batches,
so the code the theorem's model stands for is the code under test, with one reply per request.
**Alternatives.** (a) Keep the process exit and have nd-supervise respawn the child while holding the
sockets. That puts a restart policy in Rust (law 2), and the frames in the dead child's pipe are still
lost. (b) Keep the carry and pass it through `Exit.fuel (carry)`, as OPS's D4 sketch had it. That works,
but the invariant is then a parameter every exit path must remember, and the uncertain/sealFailed
exits dropped it too. With `unread`, holding nothing is a fact of the signature. (c) `repeat` for the
top loop: `partial` in disguise, which the gate cannot see.
**Critique.** An in-process reopen re-checks the open path, but it resets no process state, so leaks
and fragmentation persist, and so does a bug in the reader task, which outlives every round. The reopen
costs one base decode + tail fold per 4096 batches (~4 ms at THE BAR, ~5 s at worldBytesMax): at
the top of the range that is a 5 s write stall every 4096 batches, and it must be measured before
worldBytesMax is believed (ASSEMBLY-perf ID-7). Residue: at a process-ending exit, the one frame the
reader has read but not yet queued is unanswered, because its send fails on the closed channel. Its
connection's close is the only signal. `threadsLive` depends on `IO.getTID` naming OS threads. The
theorem is over a list model of the port: that `channelPort` IS that model (one slot, popped before
the channel) is code, not proof.
**Meta-critique.** I deleted the carry because I like invariants that live in types, and the type
fact is what I can prove. The restart reads as a self-check, and that may be making a 5 s stall at
size look like a virtue.
**Status.** landed (written by HOST-4, compiled, fixed and landed by HOST-5 on hbox).

## HOST-20 · the shape stamp: a base names the codec shapes it was written under, and an old shape refuses by name (2026-10-17, HOST-5; D2, agreed with CODEC-2)
**The defect.** Nothing on disk said which codecs wrote a Store. A binary with another World, base
or batch codec opened an old Store and either decoded it into garbage that might still decode
(the codecs are canonical, not self-describing) or refused it `baseUndecodable`, which is a parse
failure. Law 1 asks for an old shape that REFUSES TO LOAD, by name. KERNEL-23 (the cell root) and
KERNEL-24 (the origin) both change the World codec, so this had to land before them.
**Decision.** Each base record starts with 32 bytes, `Base.shapeStamp world record =
Hash.digest "nanodregg/host/shapes/v1" (Tag.of "host/base" (Base.codec world) ‖ Tag.of "host/batch"
record)`. These are CODEC's content-addressed tags (`Codec.Tag`), so the stamp is computed from the
codecs and never written as a literal. `Codec.Proofs.Tag.Tag.of_eq` says equal tags mean equal labels
and shapes. The deployed stamp is the closed def `Host.Deployed.shapes`; the toy one is
`Host.Sim.shapes`, the same function over the toy codecs. It travels in `Keys.shapes`, because
`Keys` is already everything that judges a Store's bytes on disk. `Base.read` checks the base MAC
first, then compares the stamp, then decodes. A mismatch refuses
`BaseFault.shapeMismatch stored running` (exit `shapeMismatch` 43, fatal), and none of the
base's bytes after the stamp is ever decoded. `worldStart` moves 4 → 36, and `Page.basePage` reads
from it. **The premise:** no segment byte is read without its base. `openWith` reads the base and
then the segment only from the base's offset. The stamp covers the batch codec, so the base also
vouches for the records after it. The base shape contains the World and index-entry shapes, so
CODEC-2's separate `Tag.of "host/world"` term would add nothing. I dropped it and told CODEC-2.
Theorems (`Host.Proofs.Base`): `read_stamped` (a base that reads carries the running stamp under a
verified frame) and `read_shapeMismatch` (a verified base with another stamp is refused with both
stamps). Plant (host-sim, seeds 1–3): `plant-old-shape` re-seals the newest base, byte for byte,
with the stamp of a batch codec that admits one more Turn. The binary that wrote it opens it, and
the running one refuses it `shapeMismatch`. With the compare replaced by `false` the plant goes red
(`FAIL plant-old-shape: the running binary refuses …`, seen) and the old shape OPENS.
**Alternatives.** (a) A version number in the base: someone has to remember to bump it, and
nothing checks that they did (the CODEC-5 lesson). (b) A stamp per segment frame: 32 bytes per
batch to re-state what the base already states, with no reader that needs it under the premise. (c)
A clear-text stamp outside the MAC, read first: it decodes unverified bytes into a refusal (law 7),
and a flipped stamp byte would read as `shapeMismatch` rather than `baseCorrupt`.
**Critique.** The stamp sees SHAPES, not meanings. A kernel change that keeps every codec shape and
changes what the bytes mean (a new hash domain, a new fold rule) passes it, and a refine's name is
the only thing that sees inside a function (CODEC-5). Those changes show up as a chain mismatch at
the first audit, or not at all. Log framing (`u32 ‖ record ‖ tag`) is not a Stream, so a framing
change refuses `baseCorrupt` (by name, but the wrong name). `Keys` now holds an unkeyed constant
beside the sealers, so its name lies a little. The stamp costs one cSHAKE256 over two 32-byte tags,
once per process.
**Meta-critique.** I took CODEC-2's agreed shape and trimmed it. The trim (dropping the World tag)
rests on reading `Base.codec`'s structure, and that is exactly the kind of fact that drifts. If the
base ever stops embedding the World codec's shape, the World's own term has to come back. The
"semantic change" hole in the critique is one I do not know how to close without a kernel-side
epoch, and I did not look hard.
**Flag day.** Every base re-encodes (stamp first). An older Store's base frame still verifies (the
key and framing have not changed), but its record starts with World bytes. The new `Base.read`
reads the first 32 of those as the stamp and refuses `shapeMismatch`. Re-genesis every Store.
**Status.** landed (this commit).

## HOST-21 · `lookup` of a dead call answers `refused expired`, final by `absent_final`; adopt's genesis check is PROTOCOL's and suffices (2026-10-17, HOST-5; closes HOST-8's debt and HOST-3's adopt ask)
**The defect.** `lookup` answered `absent` for every call not in the journal, including one whose
signed window had already ended. Such a call can never be admitted, because admission needs
`w.height + 1 ≤ validUntil`. The client was left to work out finality itself, by comparing a height
the Host did not send against its own `validUntil` (KERNEL-13's suggestion). An `absent` that can
never change into anything else is a verdict wearing the clothes of an "uncertain" (law 7).
**Decision.** In `Host.handle`'s `lookup` arm, if the call is not journaled and
`c.unsigned.validUntil ≤ w.height`, answer `refused expired` (`FrameRefusal.expired`, name only).
Otherwise answer `absent` as before. The finality is KERNEL's theorem, not a Host assumption:
`Host.Proofs.Serve.lookup_expired_final` restates `Kernel.absent_final` for this case. Over any
admitted log from that World, the call's txId is journaled only by a Turn whose window ends strictly
AFTER the call's own. `receive` copies the call's window into its Turn, so that Turn belongs to
another call with the same `txIdOf`, which is a collision. `handle_lookup_expired` states the arm
itself. Plant (host-sim, seeds 1–3), through the real `Host.handle` over the kernel-sim Ctx (CODEC's
call codec): `plant-lookup-expired: a dead call's lookup answers refused expired, not absent`, plus
its `absent` twin at `validUntil = height + 1`. With the comparison replaced by `false`, the first
goes red (seen).
**Adopt (HOST-3's ask).** PROTOCOL-4 already refuses `thin notAtGenesis` in `Command.start`'s
adopt (`Protocol/Command/Machine.lean`: `w.height ≠ 0`), and follow's World is the Store's World. In
`Host.Follow.loop`, `.turns []` never appends and every record holds at least one Turn, so height
0 means no record after the genesis image. That makes "measured against the image's end" the same
fact as "height 0". A second Host-side check of it would be one fact checked twice (law 1), so none
is added.
**Alternatives.** (a) Send the height with `absent` and let the client decide (KERNEL-13): every
client re-derives a kernel fact, and a client that forgets waits forever. (b) A typed lookup reply
(`absent | expired | ok`) as a Status code: `expired` is a refusal of the request's purpose, and the
Status table is PROTOCOL's to grow. The name rides in `refused` the way every other refusal does.
**Critique.** `expired` is decided against the World at the start of the batch's step, not the
durable one. A lookup in the same batch as an admission at the boundary height answers against
the advanced World, which is still correct, because a window that ended stays ended. The name
`expired` is also `ReadRefusal.expired`'s name. Both mean "your signed window is behind this
World", but the read one carries the writer's height (PROTOCOL-19) and this one carries nothing,
since a lookup has no re-sign to do: a dead call is dead. The CLIENT must treat `refused expired`
on lookup as final (not retry-safe-unknown). It relays bytes, so the decision is in the rows.
**Meta-critique.** I closed the adopt item by argument rather than by code. The argument rests on
an IO fact (`.turns []` is never appended) that no theorem states. If someone makes follow append
an empty record (a heartbeat, say), the two facts come apart silently.
**Status.** landed (this commit).

## HOST-22 · the unsealed tail is bounded in TURNS: a turn cadence beside the byte cadence; open refuses `tailTooManyTurns` (2026-10-17, HOST-5; PERF's verifies-per-open)
**The defect.** HOST-14 bounds the tail after the newest base in BYTES (`tailMax` = two cadences
and a frame). An open folds every Turn of that tail, and a follower's fold re-derives each one,
which includes one Ed25519 verify (`Receive.audit`). At `worldBytesMax` a tail of small Turns is
~90k births, about 36 s of verifies by PERF's arithmetic: the first term of THE BAR's cold reopen
that is not far inside its limit, and one the code decides, so it can be bounded rather than timed.
**Decision.** `Cadence.sealTurns` (deployed 2^13) is a second seal trigger. `shouldSeal` fires at
the byte cadence OR when `sealTurns` Turns have been admitted since the newest durable base
(`height - sealed.height`, from the recorder's mark). `withinTail` (the proof argument
`commitBatch` takes) also requires `height' - sealed.height ≤ tailTurnsMax = 2·sealTurns +
recordTurnsMax`, and `makeRoom` waits for, or forces, a seal exactly as it does for bytes. `openWith`
refuses `BaseFault.tailTooManyTurns turns max` (exit 44, fatal) when the tail it folded exceeds
the bound. Deployed: at most 16448 verifies per follower open (~6.6 s at ~0.4 ms), against ~90k.
Theorems (`Host.Proofs.Base`): `openWith_turns` (an open that succeeds reached at most
`tailTurnsMax` above its base's height, whatever segment it was handed) and `within_after_seal`
(re-stated: right after a seal at the loop's position, any frame within the record bound adding
at most a record's Turns fits, in bytes and in Turns). Plants (host-sim seeds 1–3):
`plant-tail-too-many-turns` (a Store written with neither cadence firing, reopened under a turn
cadence its tail exceeds: refused by name; red when open's check is replaced by `false`, and red
when the loop's turn conjunct and trigger are deleted, both seen) and `open verifies` (a run where
the turn cadence is the only trigger: 15–16 bases, every reopen at most `tailTurnsMax`). WASTE
row: `open verifies-per-turn-cadence` (the most Turns any reopen folded ÷ `sealTurns`, measured
where the turn cadence binds), pinned at 0.875. The fuel reopen runs after `finish` settles the
seal, so it sees at most one cadence. A crash mid-seal can see two plus a record; the theorem
covers that case.
**Alternatives.** (a) Do not re-audit the follower's own segment at reopen (fold it with
`World.fold`, since every Turn was audited before it was appended). Its base is trusted on its MAC
alone, so re-auditing the tail defends against an adversary who could forge the base anyway. That
is a real argument that the re-audit is the wrong check, but dropping it WEAKENS a check (the
pause list). It goes to ROOT, not into this commit. (b) Scale the turn cadence with the base
(`baseBytes / k`). At 256 MiB that is 2^13 for k = 2^15 anyway, and at small Worlds the floor
binds, so a constant is the same bound with one fewer moving part. (c) Count Turns at open BEFORE
folding (a pre-check like `tailRead`): it needs the records decoded, which is the fold.
**Critique.** The turn cadence trades verifies at open for seal bytes. At `worldBytesMax` a
256 MiB base every 8192 small Turns (~3 MB appended) is ~85 sealed bytes per appended byte, far
above HOST-14's ≤ 4 + floor. The byte ratio no longer bounds the seal's write amplification at the
top of the range, and nothing pins it there: the toy WASTE row only sees toy scale. Open's check
runs AFTER the fold, so a hostile Store costs up to the byte bound in verifies before it is
refused. The bound is a guarantee about Stores this loop wrote, and a named refusal for others.
**Meta-critique.** I bounded the cost PERF named and kept the check that produces it, because
removing a check needs a ruling. That is the right order, and also the comfortable one: alternative (a)
may make this whole decision unnecessary, and I have priced it in prose, not measured it.
**Status.** landed (5582991); SUPERSEDED by the amendment below. Alternative (a) is raised with ROOT.
**Amendment: ROOT ruled alternative (a) on 2026-10-17 (a pause item: it removes a check).** A
follower reopens its own Store EXACTLY as the writer does: the one `openWriter`/`openWith`, folding with
`World.fold` (`Deployed.foldStep`), with no signature verified at reopen. `Deployed.auditStep` is DELETED,
not switched off. The turn cadence goes with it: `sealTurns`, `tailTurnsMax`, `tailTooManyTurns` (exit 44),
`openWith_turns`, `plant-tail-too-many-turns` and the WASTE row `open verifies-per-turn-cadence` are all
deleted. Once no open verifies, the byte bound bounds open work (O(touched) map operations per Turn,
KERNEL's `fold work-per-turn`), and no theorem needed the turn bound for anything else. Exit code 44 is
retired. `recordTurnsMax` stays in Bounds, where it moved in 5582991.
**Why it is sound.** Base and tail rest under one MAC and key. Anyone who can forge a tail record can
forge the base, which the reopen already trusts on the MAC alone, so the reopen re-audit distinguished
nothing. A follower-only reopen would also be a second shape of open (law 1). The premise that makes
the fold sound is that follow appends only Turns its own `World.admit` accepted, at follow time, before
the append. That is `Protocol.Command.step_persists_admitted` (with `absorb_admits` / `absorbPage_admits`),
which PROTOCOL-5 lands. The reopen theorems are then the writer's own, over the one open
(`open_sound`, `open_encodeAll`, `open_torn`, `openWith_reads`/`anchored`/`foreign`, `read_stamped`), and
host-file-sim's in-process reopen plants cover the shared path. Torn tails and MAC failures keep their
names (`torn`, `corrupt`, `baseCorrupt`).
**What this does NOT change.** Follow-time verification is untouched. A follower still re-derives every
Turn from the writer's logged signed request (`Command.absorb` → `Receive.submit`) and refuses the log by
name: `eventMismatch` for a flipped served event, `chainMismatch` for an omitted one. The tooth is the rows'
`audit` row, whose plant `Mutation.followVerifyAll` (a follower that accepts any signature) is caught at
line 13. That plant still runs and still goes red with the follow-time check removed.

## HOST-23 · a follower tail over the one open: `Host.Tail` (2026-10-17, HOST-5; HOSTING-7's ask)
**The ask.** The hosting controller, a per-Store exe run by the operator, needs the World at open
and then, for each newly appended batch, the World after it and what the batch did. It must never
write, never truncate, and never become a second replayer.
**Decision.** `Host/Tail.lean`:
- `Tail.open` is THE open (`openAt` over a fresh read handle: no lock, no truncation), with the
  open's step being `Prod.fst` of the tail's step.
- `Tail.next` makes one read of at most `Log.frameMax recordBytesMax` bytes at the tail's position.
  The read is O(appended bytes) and bounded.
- `Tail.absorb` (pure) runs the same `Log.recover`, chained from the tail's tag, and the same
  per-record step, collecting each record's output.
- `Tail.await` polls `next` with `tailPollMs` (a named Bound, 50 ms) between empty reads, for at
  most `rounds` reads. There is no notify primitive.
- The deployed step is `Deployed.tailStep = Record.stepTurns digestCodec (World.fold X.env)`, the
  writer's own fold. The controller reads the writer's own files, so it trusts what the writer's
  reopen trusts. `Record.step` is now `stepTurns`'s World, which keeps the decode and the chain
  check in one definition.
- Refusals, by name: `corrupt` at an absolute offset (bad bytes with a verifying frame after
  them, or a full frame bound holding no whole frame), `record i f`, `shortRead`, `tagWidth`. A
  cut last frame is the writer mid-append and stays for the next call.
- Theorems (`Host.Proofs.Tail`): `absorbRecords_ok` (the fold is `foldlM`, outputs in order) and
  `absorb_encodeAll` (absorbing a clean run of frames written after the tail's position reaches
  the fold of exactly those records and stands where a writer would chain the next frame).
- Plant (host-sim, seeds 1–3): `plant-tail` reaches the writer's World from genesis in 3 bounded
  reads, with every Turn reported once. A flipped byte is refused `corrupt`. With the corrupt arm
  answering "nothing new", the plant goes red (seen).
**Alternatives.** (a) The controller as a `host follow` client over the socket (log pages): it
needs a member key and a follow grant, and the controller must hold no key (HOSTING). (b) Reopen
per poll: O(store) per poll. (c) inotify/kqueue notification: platform plumbing for a 50 ms
latency nobody has asked for.
**Critique.** The tail does not follow base replacement: it reads the segment only, which is
append-only (the writer truncates a torn frame at its own reopen, never past a synced frame, and
the tail never stands inside one). A future segment rotation would break this silently, so the
tail must re-open on any rotation once one exists. `absorb_encodeAll` covers clean runs. A
mid-append cut is covered by `open_torn`'s analogue only through the plant, not a theorem.
**Meta-critique.** I gave the shape HOSTING proposed, and that is the comfortable answer. The test
is whether a second reader of a Store's files should exist at all, given law 5's "the follower is
the only replayer". It folds with the writer's fold, from the writer's bytes, so it replays nothing
the writer did not, but it IS a second process folding.
**Status.** landed (this commit).

## HOST-24 · D8 on the Host side: STATUS at open, seal and exit; no Tally (2026-10-17, HOST-5)
**Decision.** `fileCheckpoint` writes one `STATUS seal height= offset= index= base_bytes= world_bytes=` line,
or `refused=NAME`, per seal. Together with HOST-19's STATUS at open and exit, every durable change that is
not a batch is named on stderr. D8's Tally decorator is not built: what it found (F1) is the
`requests = replies` check at every fuel return (HOST-19), and a counter beside it would be a second account
of one fact (law 1).
**Alternatives.** A Tally in the loop with a STATUS dump at exit: it counts what the replies already say.
A seal hook argument threaded through `serve`: the Checkpoint IS the seal's IO, so the line belongs there.
**Critique.** The seal line has no in-process plant, because it is printed from the seal Task's thread
and stderr capture is per-thread. OPS's live harness, which reads the real stderr, is the plant's home.
Interleaving with the main thread's lines is possible in principle; each line is one `eprintln`.
**Meta-critique.** I dropped the Tally partly on OPS's word. If an operator asks "how many refusals of
each name today", the answer is the log, not a counter, and that is a choice nobody has tested on an
operator.
**Status.** landed (this commit).

## HOST-25 · open binds the segment's ORIGIN frame to the base's World: `corrupt` at 0, `foreignOrigin` (2026-10-17, HOST-6; OPS's `corrupt history` finding, built after KERNEL-24)
**The defect (OPS, on D4/D6).** `seg.log` starts with the origin frame, `Log.frame keys.segment
segmentInitial (mark w₀).2` (HOST-18). No open reads it. `openWith` reads the base and
`[offset - 32, size)`, so a flipped byte inside the origin record opens clean, and so does an origin
frame from another World under the same key. Only `host check`'s `historyClean`, which is O(segment)
and off every serving path, refuses it as `corrupt history`. But the origin frame is what a
follower's page from height 0 chains from, and it is the one place where a Store's file says which
World it belongs to. HOST-18's critique already named the hole ("the origin frame's RECORD is never
re-verified on open").
**What KERNEL-24 gives.** `World.origin : D` is set by genesis and never written again
(`admit_origin`, `fold_origin`). The genesis chain is `H(domGenesis, bytes origin)`. So once it lands,
the origin frame's record (the genesis chain) is a function of the base World's own `origin`, at
every height, and not only at genesis.
**Decision.** `openWith` takes one more argument, `originChain : W → ByteArray`: the genesis chain
of `w`'s origin. The deployed value is KERNEL's own definition (`Env.bytes` of the genesis-chain
function KERNEL-24 names; HOST restates no hash). After the base reads, `tailRead` passes and the
foreignSegment check passes (that order keeps HOST-18's names for a foreign file), open makes ONE
more bounded read, `[0, min (Log.frameMax chainBytesMax) b.offset)`, and requires:
- `Log.frameAt keys.segment chainBytesMax origin 0 segmentInitial = some r`. Otherwise it refuses
  `.log (.corrupt 0)`, which is HOST-12's own fact: bad bytes at offset 0 with verifying frames after
  them. The name is `corrupt`, the same name OPS's `check` prints, and no new Status is added for it;
- `r.record = originChain b.world`. Otherwise it refuses `.base .foreignOrigin`, a new BaseFault and
  Status `foreignOrigin`, code 30, fatal. This is a frame that verifies under this Store's key but
  states another World's genesis: two Stores that share a key file, with one's origin frame spliced
  over the other's.

`openLog`'s `corrupt off` becomes ABSOLUTE (`b.offset + off`) in the same commit, as `Host.Tail`'s
already is. Today the open's offset is relative to the base, so `corrupt 0` would be ambiguous
between the origin frame and the first record after the genesis base. The host-sim plants that
match `isCorrupt … 0` move to `origin.offset`.
**Cost.** One pread of ≤ 100 bytes and one KMAC256 per open: O(1), independent of the Store. Every
open pays it (writer, follower, fuel reopen, `Tail.open`, `check`), so the check is not a mode. It is
the one open.
**Theorems (`Host.Proofs.Base`).**
- `openWith_reads`, re-stated: exactly two ranges, `[0, min (frameMax chainBytesMax) offset)` and
  `[offset - 32, size)`, with the tail ≤ `tailMax`.
- `openWith_origin`: an open that succeeds read, at offset 0, a frame that verifies from
  `segmentInitial` whose record is `originChain b.world`.
- `openWith_originCorrupt` and `openWith_foreignOrigin`: the plants' statements over the real
  `openWith` (given a base that reads, a tail in bounds and an anchored tag: a non-verifying origin
  refuses `corrupt 0`, and a verifying one with another record refuses `foreignOrigin`).
- Completeness, so that the check cannot refuse the Stores this Host writes: `genesisImage_origin`
  (the image genesis writes passes the check, given `originChain w₀ = (mark w₀).2`, which is
  KERNEL's genesis-chain equation), and, over the deployed World, `originChain` is invariant under
  `foldStep` (from KERNEL's `fold_origin`). Then every later base's World states the same origin
  as the frame at 0.
**Plants.** In host-sim, seeds 1–3, over a Store that has a sealed base past the first record:
`plant-origin-flip` flips the byte at `originSize/2` and expects `corrupt` at 0. Without the check
it opens clean: that is OPS's finding, and the red run will be shown. `plant-foreign-origin`
overwrites `[0, originSize)` with another genesis's origin frame under the SAME key (same founders and
name, another nonce) and expects `foreignOrigin`. With the record compare replaced by `true` it
opens clean, and that red run will be shown too. OPS's store-plant `flip-byte-origin-frame-before-base`
keeps its expected `corrupt`, but it now comes from the open, not from `historyClean`. OPS-2 is
asked to add the same flip through `serve` (the open path of the real exe), plus a
`foreign-origin` row. `Ops.Units.hostAction` gains the `foreignOrigin` arm, cross-layer, as OPS-2
agreed in advance.
**What it does NOT do.** It binds frame 0 to the base. It does not bind the frames BETWEEN the origin
and the base's offset: those are chained by their tags, and only `historyClean` (`check`) and paging
(frame by frame) verify them. A flip there still opens clean and is refused when a page or a check
reaches it. Making open O(1) in that range is the point, and a whole-prefix check at open is
O(segment) on the request path's restart (law 5). This is also not a second copy of KERNEL-24's
`wrongWorld` (law 1): that check binds a CALL to a World, and this one binds a Store's FILES to
each other.
**Alternatives.** (a) Leave it to `check` (status quo): a damaged origin frame then serves pages from
0 until someone runs a backup check. (b) Put the origin in the base and delete the origin frame: the
frame exists so that every base sits after a frame (HOST-18's anchor), and the base already
carries the World's origin, so a second field would be a second copy. (c) Compare only the
origin frame's TAG, not its record: the tag comes from the record, but a tag that verifies says
nothing about which World it names, which is the second refusal's whole point. (d) Store the origin
frame's expected tag in the base: it says the same thing as the record compare, one step removed
from the kernel's definition.
**Critique.** The second refusal needs two Stores sharing a key. Store keys are drawn per genesis, so
`foreignOrigin` is an operator's copy error, not an attack: anyone who holds the key can forge both
the base and the frame (HOST-16). The flip refusal is the one that will actually fire, and the
damage it catches is 68 bytes out of a whole file. The completeness theorems depend on KERNEL
keeping `origin` constant under every Turn kind. A future "re-root" Turn would turn every Store
written after it into a fatal `foreignOrigin`, which is loud, but a fatal open is a harsh way to
learn it. The absolute-offset change alters printed offsets, and nothing persisted holds them.
**Meta-critique.** OPS found this and named it `corrupt history`, and I chose to reuse `corrupt`
for the flip half. That is law-1 comfort: one name for one fact. But it also means an operator
cannot tell from the exit code whether the damage is in the origin or in the tail. The offset on
stderr is the only thing that tells them apart. I also designed this before KERNEL-24 exists, against
its decision text (`fold_origin`, the genesis chain formula), not its code. Exactly that move built
mirrors elsewhere, so the build waits for the real signatures.
**Flag day.** None of its own. Genesis already writes this frame (`genesisImage`), and the bytes do
not change. It lands right after KERNEL-24, whose flag day re-geneses every Store (the D2 stamp
refuses the old ones `shapeMismatch` before this check is reached). After it, a Store whose origin
frame does not match its base refuses to open, by name, where before it opened.
**Status.** designed (51515fa); landed after KERNEL-24 (9e91ede) as specified, with these facts
from the build. KERNEL-24 names the function `World.genesisChain E origin = H(domGenesis, bytes
origin)`, and `Deployed.originChain w = (World.genesisChain X.env w.origin).bytes` is `mark`'s
projection of it, so `genesisImage_origin`'s premise holds by `rfl` (KERNEL's `genesis_chain`). The
completeness theorem past genesis is `Record.step_origin` (from `fold_origin`); it is stated per
record, and the open's fold is a fold of records. In host-sim (seeds 1–3), the origin flip is at
offset 5, inside the RECORD: a flip at `originSize/2` lands in the toy frame's tag, which under
the genesis base is HOST-18's anchor and is refused `foreignSegment` first. Under the genesis base,
`plant-foreign-origin` is also `foreignSegment`, for the same reason, and a check pins that order.
Mutations (seed 1): the record compare replaced by `true` gives 1 FAILED (foreign-origin under the
newest base), and `originFault` answering `none` gives 3 FAILED (both flips and foreign-origin). The
existing flip plants' `isCorrupt` offsets moved from 0 to `origin.offset` (now absolute). The design's
`openWith_originCorrupt` / `openWith_foreignOrigin` landed as ONE theorem over `openWith`,
`openWith_originFault` (any verdict of `originFault`), with `originFault_corrupt` /
`originFault_foreign` naming the two verdicts. The completeness half is discharged at the deployed
instance in `Host.Proofs.Deployed` (the law-6 reader found it stated only generically):
`originChain_genesis`, `genesis_origin_passes`, and `foldStep_originChain`.

## HOST-26 · the pinned base digest has its own customization string (2026-10-17, BUILD-TRANSPORT; scout C1's finding)
**Decision.** `Keys.worldDigest` (the unkeyed cSHAKE256 of a base's World bytes, which a thin member
pins and `read` pages state, HOST-15) is `Hash.digest "nanodregg/host/base-digest/v1"`, no longer
the base MAC's string `nanodregg/host/base/v1`.
**Alternatives.** Keep the shared string: KMAC256 is cSHAKE256 with function name "KMAC", so the
two outputs are already separated by the function name; nothing collides today.
**Critique.** It is hygiene, not a hole: the old sharing was safe by KMAC's construction. Every pin
taken before this commit no longer matches (a thin `adopt` with an old digest refuses
`baseMismatch`); nothing deployed holds one.
**Meta-critique.** I took it because the assembly listed it and it is two lines; "one string, one
purpose" is an aesthetic I am applying, not a measured failure.
**Status.** landed. Re-emit: every pin (out of band).

## HOST-27 · `host` ignores SIGXFSZ, so a write past the file-size limit is `uncertain`, never a signal death (2026-10-17, HOST-6; OPS-2's live finding)
**The defect (OPS-2, measured on hbox and burst5-a with the real `host` under nd-supervise).** If an
append passes `RLIMIT_FSIZE` (`ulimit -f`, systemd `LimitFSIZE=`), the kernel sends SIGXFSZ. Its
default action killed `host serve`: signal 25, exit 153 through bwrap, with no name and no reply (the
client saw a closed socket). The exit table puts a failed append in class restart (`uncertain`, 3). The
Store stayed sound (a torn tail that the next open truncates), so only the exit was wrong. But a
process that dies unnamed breaks law 7 and the never-silent rule of HOST-19.
**Decision.** `Host.ignoreFileSizeSignal` (`nd_ignore_sigxfsz` in Host/c/file.c) sets SIGXFSZ to
`SIG_IGN` (`signal`), as the first act of `host`'s `main`, before any verb runs. With it ignored,
`write` returns `EFBIG`. `nd_file_write_all` returns that as an IO error naming the call and errno, and
the loop's append path answers the batch `uncertain` and exits `uncertain` (3, restart). If
`signal` itself fails, that is the existing `io` refusal (exit 13): the program refuses to start
rather than run with the default disposition. A write that crosses the limit can be SHORT first
(it writes up to the limit); `nd_file_write_all` already loops on short writes, so the next call
is the one that fails EFBIG, and the batch is `uncertain` either way (GATES-2's ask, read in the C;
the live plant sets the limit just past the Store's current size, so it crosses mid-frame).
**Plant.** OPS-2's `deploy/live` LimitFSIZE unit (e31b4ee) recorded `153`. After this commit it must
record `exit 3`, then a restart. It runs on a systemd user manager, not in-process. An in-repo plant
would need a `setrlimit` FFI used only by a test, a second copy of the platform's behaviour, and that
is what the live harness already exercises for real.
**Alternatives.** (a) Block SIGXFSZ around each write only: same effect, more FFI calls per batch, and a
window outside writes where nothing is written anyway. (b) Check the file size against the limit
before writing: a second, racy copy of the kernel's own check. (c) Treat the death as a restart in the
unit (`RestartForceExitStatus=153`): it names a signal death as a verdict, and it relies on bwrap's
128+N encoding.
**Critique.** A process-wide disposition is inherited across `exec`. `host` execs nothing, but a
future child would start with SIGXFSZ ignored. A partial write before EFBIG leaves a torn tail of up to
one frame. That is exactly HOST-12's torn case, and the writer's reopen truncates it. Under a
persistent limit, every restart fails the same way: a restart loop that systemd's start limit stops,
loudly, with `uncertain` in the journal each time.
**Meta-critique.** I took OPS-2's proposed fix as given. It is the textbook answer, which is also the
reason to doubt it. The case I did not test myself is a limit hit inside the seal's `base.tmp` write
(a Task thread). The disposition is process-wide, so the same EFBIG reaches the seal's own IO error
(`sealIo`, restart). By reading, that holds, but nothing has measured it.
**Status.** landed (this commit).

## HOST-28 · HOST's answer to OPS-P1 (state carry): ACCEPT the two verbs, AMENDED: one stamped artifact, a required digest, the one genesis path; the carried shape is stamped, not promised stable (2026-10-17, HOST-6)
**Accepted.** `host export STORE OUT` and `host import STORE NAME IN [--nonce HEX32]`, on the one
open and the one genesis path. Export opens as `check` does (`openFollower`: no lock, nothing
written in STORE) and requires `historyClean`. Export is off every request path, so O(store) is
fine there.
**Amendments.**
1. **One artifact, not a directory.** `OUT` is one file, `carried = stamp32 ‖ from ‖ height ‖
   chain ‖ CODEC carried bytes`. `stamp32` is `Hash.digest "nanodregg/host/carried/v1" (Tag.of
   "host/carried" (carried codec))`, the D2 discipline applied to the export. `from` is the exported
   World's origin, and `height ‖ chain` is the anchor it was taken at. Two files would let a
   lineage line drift from the bytes it describes.
2. **A digest, required at import.** Export prints `carried <hex>` (`Hash.digest` of the whole
   file), `from <hex>` and `anchor H:C`. Import takes `--digest HEX` and refuses `carryMismatch`
   unless the file hashes to it. The export file is not MAC'd: no Store key crosses a flag day, and
   the old Store's key must not authenticate the new one (HOST-16). Without the digest, OPS-P1's
   "carried bytes equal after reopen" check only shows that import was faithful to `IN`, not that
   `IN` was faithful to the old Store. A flipped cell byte in transit would import cleanly, as a
   plausible World. The digest is the operator's out-of-band link (RUNBOOK §6: export prints it,
   and the operator copies it into the import line). This fails closed: no `--digest`, no import
   (`usage digest`).
3. **The one genesis path.** Import builds `w₀ := Receive.carry X name nonce from carried` (nonce from
   the OS, or `--nonce`, exactly as `genesis`) and writes it with `Host.genesis`. That is the same
   `genesisImage`, the same origin frame (HOST-25 holds unchanged: KERNEL's carry chain is
   `H(domGenesis, origin)`), and the same `exists` refusal. Then `openWriter` reopens it and compares
   `World.carried`'s CODEC bytes with the file's. Unequal is `carryMismatch`. That comparison is a
   pair assertion on the base codec's round trip, not a separate trust step.
4. **Names.** `carryMismatch` is one new Status (fatal) covering both the digest and the reopen
   compare; stderr says which (`refused carryMismatch digest` / `… reopen`). A carried file under
   another stamp is `shapeMismatch` (43): it is the same fact as D2 (bytes written under other shapes),
   and the operator action is the same (use the binary that matches). It needs no third name. A file
   that does not decode after its stamp matches is `carryUndecodable`? No: that is `carryMismatch`'s
   territory as well, since a canonical decoder that refuses bytes it wrote is a codec defect, named
   `carryMismatch decode`.
**The fork (whose rule the carried codec's stability is). My answer: nobody promises it.** OPS-P1 proposes
a carried codec "versioned on its own and changed only by an explicit carry-codec flag day, rarer than
World codec changes". That is an estimate wearing the clothes of a rule. KERNEL-23's trie, LEDGER's cell
kinds and any Entry change all alter what `cells` encodes to, and each of them would have to choose
between breaking the carry and keeping an old Entry shape alive. With the stamp, nobody has to keep
anything. A flag day that leaves the carried shape alone can carry state: the old binary exports, the
new one imports, and the stamps agree. A flag day that changes it cannot carry, and the new binary
refuses the old file `shapeMismatch` by name, never by reinterpretation (law 1: no second reader).
Crossing such a day is either a fresh genesis, or a migration function that law 1 forbids. If a carry
across a shape change is ever wanted, the honest way is an export by the old binary into the NEW
shape (old binary + new codec module). That is a build-time question for that flag day, not a runtime
second reader.
**What is carried is KERNEL's, not HOST's.** PROTOCOL-30 (97a2b11) amends OPS-P1: the carry
keeps the journal entries still inside their window, so a `lookup` of a call committed just before the
export answers committed, not `absent` then `wrongWorld` (KERNEL-29). HOST's verbs do not depend on
the choice: `carried` is whatever `World.carried` returns, its bytes are CODEC's, and the stamp covers
its shape.
**What HOST needs from others.** KERNEL-6: `World.carried`, `Receive.carry` with `carry_carried` and
`carry_origin_ne` as OPS-P1 states them, and `carry_chain : (carry …).chain = World.genesisChain X.env (carry …).origin`
(HOST-25's premise for carried Stores). CODEC-2: `Codec.Kernel.carried` with its canonicity theorem.
PROTOCOL-6 answers the member side.
**Critique.** The digest moves trust onto the operator's copy-paste, and an operator who exports and
imports on the same compromised box can forge both. That is inherent: the old World's members never
signed its state as a whole. A member-countersigned carry (each member signs `carried`'s digest)
would be the real answer, and it is PROTOCOL's to want. Export through `openFollower` races a live
writer exactly as `check` does: it reads a consistent base plus the tail that verifies, so a carry
should be taken from a stopped writer, and RUNBOOK §6 must say so.
**Meta-critique.** I accepted OPS's verbs and amended them toward what HOST already has (the stamp, the
one genesis), which is the comfortable direction. The "nobody promises stability" answer also removes a
hard question rather than answering it: it may mean that in practice no carry ever crosses a real flag
day, which makes the feature mostly theoretical until the kernel stops changing.
**Status.** proposed answer to OPS-P1. HOST builds the verbs once KERNEL-6 and CODEC-2 land `carried`.

## HOST-29 · a batch record states each Turn's ROOT: `List (Turn × root)`, no end chain; open checks every root by admission (2026-10-17, HOST-6; KERNEL-23's World port, with KERNEL-6/7, CODEC-2/3, PROTOCOL-6)
**The defect the port creates.** KERNEL-23 makes `chainNext E prev t root'` commit the World's root
after each Turn (the phone's per-head `(prev, turnDigest, root')`). `Host.Page.walkTurns` advanced
the chain from a record's Turns alone, so it could no longer state the chain after an event without
admitting, and a page reader has the index entry's chain but not the World at that height.
**Decision (KERNEL-6's option (a), amended).**
- A batch record is CODEC's `batch max dc : Stream (List (Turn D × D))`: each Turn with `World.root`
  after it. The record's separate end chain is DELETED: it is `chainOf E w.chain pairs`
  (`Kernel.RootedFold.chain`), so stating it too would be a second copy of one fact (law 1).
- The loop gets the roots for free. `Host.Machine` gains `note : W → N` (deployed: `World.root E`,
  O(1), the trie's cached digest), and `Machine.step` stages `(t, note w')` at admission.
  `Recorder.encode` writes the staged pairs.
- Follow persists pairs from PROTOCOL's `absorb`, which pushes `(t, World.root X.env w')` (agreed
  with PROTOCOL-6).
- Open runs each record with `Record.runRooted`: it admits each Turn with `World.admit` and requires
  the stated root to be `World.root` of the World reached. Otherwise it refuses
  `Record.Fault.rootMismatch i`, which replaces `chainMismatch` (there is no stated chain left to
  mismatch). So every root on disk is checked against the reopening writer's own admission, and the
  page walk trusts only roots that this check (or the writer that staged them) produced.
- The page walk advances `chainNext E c t root` from the stated pairs: O(page bytes), no admission.
**Theorems.** Kernel (KERNEL-7 agreed): `Kernel.Rooted admit note w l w'` (generic: every step accepted,
every note the one reached), `World.RootedFold E := Rooted (World.admit E) (World.root E)`, and in
`Kernel.Proofs.RootedFold` `Rooted.snoc`, `RootedFold.fold` (a rooted fold IS a fold of its Turns)
and `RootedFold.chain` (its chain is `chainOf` over its pairs). Host: `Machine.staged_rooted`
(replaces `staged_foldlM`: the staged pairs are a rooted run from the batch's World to the World
kept), `Record.runRooted_ok` / `Record.step_rooted` (a record that opens is a rooted run of the pairs
it decodes to), `Record.step_origin` re-proved through them. Protocol (statements reviewed by
PROTOCOL-6, at its condition that the roots be stated, not dropped): `absorb_admits`,
`absorbPage_admits` and `step_persists_admitted` now conclude `RootedFold`, and
`step_persists_folds` is the plain-fold corollary HOST-22's reopen argument cites.
**Plant.** In host-sim, seeds 1–3, `plant-flip-root` re-encodes the first record with the root beside
its first Turn changed, re-seals the segment after the origin frame so every tag verifies, and
expects open to refuse `record 0 (rootMismatch 0)`. With the compare replaced by `true`, it is the
one FAILED (seen). The page checks compare against roots recomputed by admitting the logged Turns
from genesis, never against the roots the records state.
**WASTE.** `submit bytes-per-turn` rises 1.419 → 1.492 (toy digest: 8 root bytes per Turn; deployed:
32 per ~290-byte Turn, ≈ +11 %), less one chain per record. That is the price of a page that does
not admit. Re-pinned with its reason.
**Alternatives.** (b) A page reader re-admits: it has no World at the entry's height, so this would
need a World per index entry, O(store). (c) Check only record-boundary chains: that breaks pages that
end mid-record (PROTOCOL's pair assertion) and the phone's per-head root. Keeping the stated end
chain beside the roots: one fact twice. Checking stated roots only through the end chain (one hash
compare): that would rest on chain injectivity, a collision assumption, where the per-Turn compare
is exact and costs one O(1) root read per Turn.
**Critique.** Records grow by a digest per Turn forever, and a Store of tiny Turns pays the most. A
root is also a fact about the WHOLE World, so a stated root is unverifiable by any reader that does
not hold the World: pages pass roots on the writer's word (MAC'd at rest, checked by the writer's
own reopen, re-derived by every follower). A phone trusting a head trusts it for exactly this
reason. The `note` parameter generalises Machine for one use.
**Meta-critique.** I took KERNEL-6's lean (a) and improved it by deletion, which is my favourite
move, so I should be suspicious that the deletion (the end chain) is right. It is right because
`RootedFold.chain` proves it derivable. I did not measure the deployed byte cost at THE BAR, only
priced it.
**Flag day.** It is part of KERNEL-23's kernel! commit. The batch codec changes (the D2 stamp
flips), so every Store re-geneses (the port re-geneses them anyway) and an old Store refuses
`shapeMismatch`.
**Status.** built against main 4777611 + kernel7-r4 + CODEC-2's codec2-trie-r3. host-sim and
host-file-sim 1–3, hosting-sim 1–3, kernel-sim 64 seeds, store-plants, lang-journey: ALL PASS;
rows INCOMPLETE 3 pending, no FAIL. Lands in KERNEL-7's flag-day commit.

## HOST-30 · the index is its own append-only file, one page per seal: a seal writes only the entries since the last base (2026-10-17, HOST-7; HOST-17's count defect, ROOT's framing)
**The count.** A seal re-encodes the WHOLE index: `Base.codec` holds `rawList indexMax Entry.codec`, one
`Entry` (u64 height, u64 offset, u32-length chain: 52 bytes deployed, 28 in the toy) per record ever
written. host-sim measures, at the LAST seal of a run of n fresh Turns (seeded splits, toy cadence
2 KiB), the index bytes that base holds ÷ the segment bytes appended since the base before it
(`WASTE seal index-bytes-per-appended-byte-at-n`, seeds 1–3):

| n Turns | seals | index ÷ appended (min–max over seeds) |
|---|---|---|
| 100 | 3 | 0.320 – 0.540 |
| 200 | 7 | 0.796 – 0.943 |
| 400 | 13 | 1.205 – 1.329 |
| 800 | 19 | 1.228 – 1.251 |

**Why it grows, and why it stops growing.** The appended side is one cadence, `max(sealMin, world/4)`;
the index side is every batch so far. While `world/4 < sealMin` the denominator is fixed and the term
grows linearly in seals (rows 100 → 400). Past that the denominator is the World, and the World also
grows with history, because every Turn adds a journal entry and the journal is never pruned (its
life is bounded by the genesis allowance, KERNEL-18). So the term levels off at 4 · (index bytes per
log byte) ÷ (World bytes per log byte): about 1.25 in the toy. Deployed, with one-Turn batches, it is
at most 4 · 52 / 72 ≈ 2.9, where 72 is a journal entry's weight (`journalWeight`), and nullifiers and
cells only lower it. A deployed World reaches `world/4 > sealMin` at 4 MiB, about 14 BAR Worlds, so
every Store THE BAR describes is in the growing regime. Three consequences follow. HOST-14's
"at most 4 + the floor" is false by this term. The base is O(history), not O(World). And the level-off
is an accident of KERNEL's journal: if the journal is ever pruned, the term grows without bound. Read
off the runtime and not measured: `spawnSeal` hands the Task the loop's own `Array Entry`, so while the
Task holds it (up to its `toList`), every `r.index.push` on the loop copies the whole array, since
`lean_array_push` copies a shared array. That is O(records) work on the request path (law 5).
**Why not under store-plants' live writer.** It writes 48 records of 48 KiB, which is 48 entries
(2.5 KB) against a 1 MiB cadence, a term of 0.002. The defect scales with the BATCH COUNT, which
host-sim drives with the deployed loop and seal policy. HOST-14-at-size (counts under the live writer)
is a separate row.
**Decision (proposed; ROOT to rule, it changes the base).** STORE gains `index.log`, an append-only file of
Log frames under a third sealer domain (`nanodregg/host/index/v1`), chained from 32 zero bytes like
seg.log. A seal first appends ONE frame, whose record is the entries written since the previous base
(`rawList`), and syncs it. Then it writes the base, which no longer holds entries: it names
`(indexOffset, indexTag)`, the index.log prefix that is its World's index, the same way
`(offset, tag)` name the segment prefix. Open reads the base and refuses `indexShort` unless
index.log is at least `indexOffset` long. It then recovers `[0, indexOffset)`, and every frame must
verify and the chain must end at `indexTag` exactly at `indexOffset`; otherwise it refuses
`indexCorrupt`. The entries are the pages in order, and the tail's entries are rebuilt by the fold as
today. Bytes past `indexOffset` are an ORPHAN page, left by a seal that crashed between the page's
sync and the base's rename. The writer truncates them, as it truncates a torn segment tail; a
follower ignores them. The seal checks `indexOffset + page frame ≤ worldBytesMax`, else
`indexTooLarge`. That is the same lifetime bound the whole index has today, now checked in O(1). The
Task is handed only the new entries (`extract` before the spawn), so the loop's Array is never shared.
**Crash story** (each case a plant): a crash before the page's sync leaves a torn index tail past the
old base's `indexOffset`, which is truncated. A crash after the sync and before the rename leaves an
orphan page, which is truncated; the next seal writes those entries again, because its page starts
at the base's count. A crash after the rename leaves the new base and its page, which are
consistent. The base still names the segment by `(offset, tag)` and the origin frame (HOST-25), so
nothing about the segment's story changes.
**The count after.** Each seal writes one page of `e · (batches since the last base)` bytes plus one
frame header, so the index term is `e ÷ (bytes per batch frame)`, whatever the length. The four rows
should come out level, and they are re-pinned at the built value. The whole-seal row
`seal bytes-per-appended-byte` falls by the index share.
**Alternatives.** (a) Count the index into the cadence, `max(sealMin, (world + index)/4)`. That gives
back "≤ 4" with no new file. But `tailMax` would then grow with HISTORY, so every open folds a longer
tail, the base stays O(history), and the shared-Array copy stays. (b) Index pages as segment frames:
the batch record becomes a sum, and every segment reader (open, follow, tail, page, check) has to skip
them. Finding the pages takes a walk back through the chain, O(seals) preads. (c) A sparse index (one
entry per base) plus a forward scan: a page then costs O(cadence), which breaks law 4's O(page). (d)
Leave it: the term is bounded only by the accident above.
**Critique.** It adds a third file and a second crash story. That story is a copy of the segment's, but
it is new code with new plants. Open now reads four ranges (base, index prefix, origin, tail). The
resident still holds every entry in memory, so its RAM is O(records). Open still reads the whole
index; that read moved from one file to another and did not shrink. A lost index.log makes a Store
whose World is intact refuse to open (`indexShort`), even though the index is derived data that a
segment scan could rebuild. That rebuild (an operator verb, O(segment)) is not built. The backup
procedure changes: RUNBOOK and store-plants copy `index.log` after `base.world`, like seg.log (OPS-2).
**Meta-critique.** ROOT framed this as growth with batches. The measurement shows growth and then a
level-off, and I am still choosing the larger design. The reason is that the level-off belongs to
KERNEL's journal, not to anything the Host guarantees, and that a base whose size carries history
contradicts HOST-14's own claim. (a) is the cheaper fix, and its cost (a history-length tail) is the
one HOST-14 was built to avoid. The residue I cannot argue away: the in-memory index is O(records) of
RAM, and this decision does not touch it.
**Flag day.** The base shape changes: the entry list goes and `u64 indexOffset ‖ indexTag` comes. So the
shape stamp changes, and every existing Store refuses `shapeMismatch` (43); re-genesis. Two new fatal
Statuses, `indexShort` and `indexCorrupt`, each with its `Ops.Units.hostAction` arm and deploy/units
re-rendered. Genesis writes an empty index.log.
**Status.** RULED BUILD by ROOT (2026-10-17, six conditions) and BUILT (HOST-7). What is in the tree:
`Base` holds `(indexOffset, indexTag)` instead of entries. `Base.page` checks `indexTooLarge` in O(1).
`Base.seal` is the one function both checkpoints call: World size first, then page, then base.
`indexEntries` reads the index. `Host.sealEntries` hands a Task only the new entries.
`openWith` reads a third range and reports `orphan`. `openWriter` truncates the orphan.
`Host.Store.layout` / `backupOrder` are the layout as data (OPS-2 renders STORE.md from them).
Statuses `indexShort` 45 and `indexCorrupt` 46 are fatal, with OPS-2's hostAction sentences.
Theorems (Host/Proofs/Base):
- `openWith_reads`: exactly three ranges, the index prefix ≤ worldBytesMax, `indexOffset + orphan = indexSize`. So the writer's truncation drops only bytes past the prefix the base names.
- `indexEntries_encodeAll`: every page a sequence of seals wrote reads back in order (no page lost).
- `backupOrder_appendOnly_after_base` and `backupOrder_covers`.
Plants (host-sim):
- crash-before-rename at every seal now opens the older base with the newer page as an orphan of the exact size, to the same World and the same index size;
- plant-index-short;
- plant-index-flip;
- plant-index-other-key;
- the reopened index equals the loop's, entry for entry.
The counts after, max over seeds 1–3:
- the four rows are FLAT at 0.181 / 0.147 / 0.131 / 0.161 (100 → 800 Turns; they were 0.540 → 1.251);
- `seal bytes-per-appended-byte` 1.723 → 1.448;
- new `seal entries-handed-per-entry` 1.000 (the law-5 row);
- `open bytes-read-per-record` 1.006 → 1.033: one frame header per page, about 36 bytes per seal against a 2 KiB toy cadence and ~0.003% at a 1 MiB deployed one.
Condition 1 (land the law-5 fix separately) could not be met. A Task handed only new entries has
nowhere to write them while the base must hold the whole index, so the fix is the index file and
lands with it. Owed: OPS-2's live-copy orderings (orphan with a stale base; index.log before
base.world); a theorem over `Follow.loop` (HOST-21's open edge, unchanged); and the O(records)
in-memory index (this decision's residue).

## HOST-31 · a page reads back as written, and a seal appends where its page is framed: `entryUnfit`, `indexMoved` (2026-10-18, HOST-8; HOST-30's law-6 read, items (a) and (b))
**Context.** HOST-30's law-6 read rated two statements WEAK. (a) `indexEntries_encodeAll` took the page
codec round trip as a premise. Its discharge needs every entry inside `Entry.codec`'s domain: a u64
height and offset, and a chain of at most `chainBytesMax` (64) bytes. `Base.page` checked none of this.
The deployed chain is 32 bytes, so the gap is latent. A wider chain would have written a page that does
not read back, and the next open would refuse `indexCorrupt` about a page the writer had just written.
(b) `fileCheckpoint` appends the page at the file's end but frames it (the length, the tag chain, the
offset the base names) at `ipos`, the newest base's prefix. Nothing tied the two together. They agree
only while nothing else has written to index.log, and no theorem says so (an IO fact).
**Decision.** Two checks, each named, both in the one pure `Base.seal`/`Base.page` that both
checkpoints call:
- `Base.page` refuses an entry outside `Entry.fits` with `entryUnfit i` (the first such entry), and a
  page of more than `indexMax` entries with `indexTooLarge`. The checks run before encoding and are
  O(entries), which the encode costs anyway.
- `Base.seal` takes the index file's size (`File.size` on the append handle, an fstat; `Bases.index.size`
  in memory). It refuses `indexMoved size offset` unless the size equals `ipos.offset`. This check is
  first, before anything is encoded or written.

Two new Statuses, each with its OPS hostAction arm (pre-agreed coupling) and deploy/units re-rendered:
- `entryUnfit` 47, fatal: a defect.
- `indexMoved` 48, restart: the restart's `openWriter` truncates an orphan, or refuses `indexShort` when
  the file was cut, so a restart either heals or stops by name, and never loops.

Theorems (Host/Proofs/Base):
- `Entry.codec_lawfulOn` and `Entry.page_lawfulOn`;
- `page_ok` and its tooth `page_entryUnfit`;
- `pages_encodeAll`;
- `indexEntries_pages`: the bytes successive seals append from an empty index.log (`Base.pages`)
  read back as every entry handed to them, in order, and the position they end at is the file's size.
  It has no codec premise. Its one premise, `worldBytesMax < 2^32`, is discharged at Deployed
  (`Deployed.indexEntries_pages`);
- `seal_at_end`: a seal that succeeds was handed exactly `ipos.offset` bytes, wrote `Base.page`'s page,
  and names the size after the append. Its tooth is `seal_indexMoved`.

`indexEntries_encodeAll` now takes `Entry.fits` and discharges the round trip itself.
Plants (host-sim):
- plant-index-moved: one byte appended to index.log stops the first seal `sealFailed indexMoved`, and
  no base is installed;
- plant-entry-unfit: a 65-byte chain is refused `entryUnfit 1`, with a 64-byte control that is written.

**Critique.** `seal_at_end` and `indexEntries_pages` together say the index file is `Base.pages` from
genesis. That holds only if `File.writeAll` appends exactly its bytes at the end, which is the FFI's
contract (Host/c/file.c) and is not proved. What is proved: no seal frames its page anywhere but the
current end. Mapping `indexMoved` to restart trusts the reopen to judge, and a third process that keeps
writing index.log would make the writer restart repeatedly. `lifetime` bounds that, and the sentence
says to find the other writer. The fit check in `Base.page` cannot fire at the deployed digest, so its
only plant is a direct call. No loop plant exists, because no World in the tree has a 65-byte chain.
**Meta-critique.** I discharged (b) by refusing, not by proving. Proving it would need a model of the
file, which the Host does not have. The check costs one fstat per seal, and it turns a silent
misframing, which would show up only at the NEXT open as `indexCorrupt` against a base the writer had
already installed, into a stop at the seal that caused it. Is restart the right class? `indexShort`
and `indexCorrupt` are fatal because they come from an open, where no writer is left to blame.
`indexMoved` happens while the writer is live, and its own reopen can tell an orphan from a cut. No
re-genesis: no shape changed (the base and entry codecs are untouched, the stamp is the same). The
unit files' restart and prevent lists gain 48 and 47.
**Law-6 read (a spawned reader, before landing).** Nothing vacuous. One statement is WEAK against its
docstring. `indexEntries_pages` had said "exactly the bytes `fileCheckpoint` appends", and that is only
half proved. Each seal frames its own page where it appends it (`seal_at_end`). That seal k+1 is framed
at seal k's returned position is read off Loop.lean (`spawnSeal` passes `sealed.index`, `settle` stores
the returned one), not proved. The docstring now says so. The reader also found that a restart heals
after `indexMoved` was unplanted, so a check was added: the plant's Store reopens to genesis with the
stray byte as a 1-byte orphan. Residue named by the reader:
- an in-place overwrite that keeps the size passes `indexMoved`, and only the next open's
  `indexCorrupt` catches it;
- `fileCheckpoint`'s fstat has no plant, only `memCheckpoint`'s size does;
- the `indexMax` count check is unreachable at deployed sizes, and its payload is the byte count.

**KERNEL-33's Host arm (KERNEL-8, 17e2d3f): law-6 read by HOST-8.** `handle_lookup_forgotten` and
`handle_lookup_expired` (now with `journalForgets = false`) are OK. `step_submit` is unchanged in
statement. One gap: Serve.lean's prose said `expired` means "never committed (`Kernel.fold_answers`)",
but no Host theorem said it. It is now `lookup_expired_never_committed`. It is stated from the ANSWER
(`handle … = refused expired`), not from the arm's guards: if a Turn that `receive` derived from the
call had been admitted at any earlier World, and any admitted log led on to this one, that is False.
There was no Host plant for the forgotten arm, only kernel-sim and PROTOCOL's row. plant-lookup-forgotten
covers it in host-sim: the same dead call at height 2·windowMax − 1 answers `refused expired`, and at
2·windowMax it answers `uncertain forgotten`.

## HOST-32 · what a live backup in `backupOrder` guarantees: it opens to its base with at least the live records, or refuses by name (2026-10-18, HOST-8; HOST-30's law-6 read, item (c))
**Context.** `backupOrder_appendOnly_after_base` was only an ORDER fact over the layout data. It did
not say what a backup taken in that order gets you.
**Decision.** State it, and prove it over the one open (Host/Proofs/Backup.lean). The model:
- `file`, `I` and `S` are base.world, index.log and seg.log as they stood when the backup copied
  base.world;
- the Store opened at that instant (the writer's invariant, which host-sim's crash plants test at
  every seal and every cut);
- the backup holds that `file`, plus `I ++ x` and `S ++ y`. The append-only files are copied after
  the base, so each copy is the file then plus whatever the writer appended since.

`openWith_backup`: the backup's open either
- opens to the SAME base, with `records = live records + more.length`, a World and index that are the
  live ones advanced by the extra records' fold (`foldRecords` from the live state), and a position no
  earlier; or
- refuses by name: `tailTooLong` (the writer sealed and kept appending while the copy ran), `corrupt`,
  or `record j` with j ≥ the live record count.

It never opens to fewer records. It never refuses `indexShort`, `indexCorrupt`, `foreignSegment`,
`foreignOrigin`, `tagWidth` or `shortRead`, because the prefixes the base names were in the files
when the base was copied. The extra records fold from the live state at the live position and end at the backup's
position, so their index entries name their true offsets. A `corrupt` refusal names bytes at or
past the live position. Lemmas:
- `recover_append`: appending bytes never loses a recovered frame (`frameAt_append`, `step_append`,
  `go_append`);
- `openLog_append`;
- `openWith_seg_ok`: the one open over bytes, its success decomposed into each check it passed.

Plants (host-sim):
- plant-backup: for every base k before the last, the live Store is base k at the instant before base
  k+1 was renamed in. That is a non-empty tail with base k+1's page as an orphan, which
  crash-before-rename shows opens. The backup (base k, then the files as they stand at the end)
  opens to base k with at least the live records and EXACTLY the frames `recover` finds past base k's
  offset (an independent count), or refuses `tailTooLong`. It fires on at least two live Stores with
  a non-empty tail. HOST-8's law-6 reader found that the first cut (the live Store at the install,
  an empty tail) could not see a short read; this is the fix;
- plant-backup-wrong-order: seg.log copied as it stood one base earlier, under a later base, is
  refused `segmentShort`, never opened short.

**Critique.** The theorem assumes the copies are the files then, plus appended bytes. Three live-writer
behaviours fall outside that:
- a restarting writer that TRUNCATES a torn tail or an orphan page between two copies. The copy can
  then hold the truncated file, which is a prefix of S, not an extension of it. The open of a prefix of
  S that still reaches the base's offset is the open of fewer records, so it is not covered here.
  RUNBOOK §6 already says to copy from a stopped writer or under no restart;
- a writer that installs a NEWER base between copying base.world and copying index.log. That is
  covered: the copied base is still one the writer installed, and its prefixes are still in the files;
- copying a file while bytes are being written into it. A torn last frame is `torn` (the open folds the
  frames before it).

The writer's invariant (the live Store opens at every instant) is a premise, not a theorem. No IO model
proves it. host-sim checks it at every seal (crash-before-rename) and every cut (restart-at-every-cut).
**Meta-critique.** I proved the theorem over the Id open with in-memory readers, not over `openAt`'s
IO. The two are the same `openWith` code with different readers, which `openWith_reads` already relies
on. Restricting to readers that return the file's bytes (`segReader`) is the honest model of a copy,
and what a copy cannot model (concurrent truncation) is named above. No refusal is new, no shape
changed, no re-genesis.

## HOST-33 · HOST-14 at size, as counts: the seal bound holds once stated correctly; open reads O(history) of index.log, so open must stop reading it (2026-10-18, HOST-8; ROOT's framing of HOST-14's re-check: counts, no timing) — RULED BUILD by ROOT (five conditions), BUILT by HOST-9
**Context.** ROOT asked for HOST-14 re-checked at size as counts. The questions: do seal bytes stay
within HOST-14's claimed bound now that HOST-30 removed the index term, and does reopen read at most one
base plus the index pages plus the tail? host-sim `sizeRows` measures them under `sizeCadence`: the
toy Store, with a 256-byte seal floor, so it seals in the base/4 regime a deployed Store enters past a
4 MiB World. Two workloads:
- `grow`: every Turn spends a fresh nullifier, so the World grows with history;
- `steady`: Turns touch nothing and spend nothing, in a moving window. The World plateaus (the journal
  is pruned to the window, KERNEL-33) while the log and the index keep growing.

Max over seeds 1–3:

| count | grow @1000 | steady @1000 | @4000 | @8000 |
|---|---|---|---|---|
| seals | 32–36 | 38–42 | 55–60 | 74 (seed 1) |
| base bytes | 31–32 K | 23–24 K | 68–70 K | 69 K (plateau) |
| index.log bytes | 9.9–10.6 K | 10.4–11.0 K | 38–40 K | 78 K |
| seal bytes ÷ appended | **4.032** | 4.134 | 4.212 | 4.185 |
| (seal − pages − base growth) ÷ appended | **3.489** | 3.633 | 3.819 | **3.921** |
| open reads ÷ (base + index prefix + origin + tailMax) | 0.792 | 0.768 | 0.798 | 0.795 |
| open index bytes ÷ base bytes | 0.331 | 0.473 | **0.569** | **1.179** |
| bytes hashed ÷ appended | **5.012** | 5.113 | 5.192 | 5.165 |

Findings:
- **HOST-14's "≤ 4 + floor" is FALSE as written.** It is broken by 4.032 at 1000 records of a growing
  World and by 4.21 in the steady runs. The correct bound telescopes. Seal i writes `B_i`, and fires
  after `a_i ≥ max(sealMin, B_{i−1}/4)` appended bytes. So `B_{i−1} ≤ 4·a_i`, and
  `Σ B_i ≤ 4·Σ a_i + (B_last − B_genesis)`. Seal bytes ≤ 4·appended + the World's growth over the run
  + every page. Net of growth and pages, the measured ratio is 3.49–3.92, under 4 everywhere. The
  design holds, and the claim was misstated. The pinned row is the net one; the raw ratio is pinned
  beside it.
- **Open reads O(history) of index.log.** In a World that has stopped growing, the index is 0.47 of the
  base at 1000 records, 0.57 at 4000, and 1.18 at 8000. It is linear in records: 52 deployed bytes per
  record, 80 with the frame share. Open reads and MAC-verifies all of it, and holds it in memory as one
  Array entry per record (HOST-30's named residue). The only bound is the lifetime `indexTooLarge` at
  `worldBytesMax` (256 MiB, about 5·10⁶ records). HOST-14's claim that open reads one base and a tail
  therefore holds only for the base and tail. With the index it is O(store-history), the very shape
  HOST-14 was built to avoid, bounded only by law 4's static ceiling. Before HOST-30 the same term
  sat inside the base. HOST-30 moved it and did not cure it.
- The open-reads ratio (≤ 0.80) is `openWith_reads`'s bound seen from a run; it cannot pass 1.
- Bytes hashed are about 5 per appended byte: one for the frames themselves, about 4 for the seals.
  The 32-byte prev of every frame adds a little.

**Proposal (not built).** `index.log` becomes fixed-width, individually MAC'd entries, and open stops
reading it:
- entry k is `u64 height ‖ u64 offset ‖ chain32 ‖ tag32`, 80 bytes, at byte k·80. Its tag is keyed
  over the index domain and `(k, height, offset, chain)`, so an entry cannot be moved, reordered or
  spliced across positions or Stores;
- the base names `indexCount` (no offset or tag). Open checks `index.log.size ≥ indexCount·80`
  (`indexShort` otherwise), verifies ONE entry (the last named), and truncates bytes past the count
  (orphans, as now);
- the loop holds in memory only the entries since the last base (bounded by the tail);
- `Page.build`'s `locate` becomes a binary search over on-disk entries: O(log records) 80-byte reads,
  each MAC-checked, refused `badIndex` by name on failure. The walk then reads one contiguous range of
  entries.

Open becomes base + 1 entry + origin + tail (HOST-14's claim, honestly). RAM becomes O(tail). The
`chain` is a Digest, so `entryUnfit` loses its chain arm. The flag day: the base shape changes and so
does the stamp, so every Store refuses `shapeMismatch` and re-geneses; `indexCorrupt` keeps its name
for the one entry open reads.

**Critique (of the proposal).**
- **It MOVES a check, which is a pause item.** Today an open refuses `indexCorrupt` if ANY index byte
  is wrong. Afterwards a corrupt middle entry is found only when a `log` request reads it (`badIndex`
  on that request, never wrong data served), or by `host check`, which would verify every entry.
  Corruption of derived data stops failing loudly at open and starts failing loudly at use. That is
  a weaker open, so it goes to ROOT, not into a commit.
- **Bigger index.** 80 bytes per record against today's ~56: +43%. Measured against appended bytes it
  stays flat, about 0.2.
- **A MAC per log request per probe.** log₂(5·10⁶) ≈ 23 tag computations. That is O(log) on the
  request path, which law 5 allows.

**Alternatives.**
- (a) Keep the chained pages, and have open verify only the newest page against `indexTag`. That does
  not work: a chain is verified from its start or not at all.
- (b) Put a page DIRECTORY in the base, one entry per seal. The base then grows with seals: O(history ÷
  cadence), smaller but still history in the base, which HOST-30 just removed.
- (c) Accept O(history) open as law 4's static bound. That is what the tree does now, and this
  measurement argues against it.

**Meta-critique.** The steady workload is the honest one for an always-on Store: Worlds plateau,
histories do not. Both HOST-17's count and this one see the index grow only when the World does not
outgrow it. If I had measured only `grow` (the existing scenario), I would have reported 0.33 as
flat and stopped. The seal finding is a misstated claim, not a defect. I am pinning the corrected
statement, not changing the cadence.

**Ruling (ROOT, 2026-10-18).** BUILD, after HOST-28, with five conditions:
1. `host check` still verifies EVERY entry;
2. theorems: never-served, open_verifies_named, page reads O(log indexCount) entries as a pinned
   WASTE row, the loop's resident entries bounded by the since-last-base count, HOST-32 restated
   over fixed entries;
3. plants: a corrupt middle entry (open ok, page `badIndex`, check refuses), a wrong index size
   (open refuses by name), and the crash-before-rename orphan and wrong-order backups still red;
4. the flag day stated, including whether `indexTooLarge` survives;
5. the critique says exactly what moved.

**Built (HOST-9).** The format:
- `index.log` is fixed entries, entry k at byte `k · entryBytes`: `u64 height ‖ u64 offset ‖ chain ‖
  tag32`. The tag is the index sealer over `origin chain ‖ u64 k ‖ height ‖ offset ‖ chain`, under
  `Keys.forStore keys sid`. Here `sid` is the genesis chain of the World's origin, which the origin
  frame states (HOST-25). `entryBytes` is 80 deployed (`Keys.chainBytes` = 32); in the toy it is 56.
- Why the Store is in the tag: HOST-9's law-6 reader found that a tag over the position alone does
  not bind an entry to its Store. HOST-30's chained pages did, because one chain of tags ran over
  every page. Under a shared key file (HOST-25's case), another Store's entry spliced into the middle
  would have passed both `entryAt` and `check`. Every user binds the Store: openWith with
  `origin b.world`, the checkpoints with `origin w` (fileCheckpoint and memCheckpoint take `origin`),
  and the pagers and check with `originChain` of the World.
- `Entry.read keys k b` re-spells the entry it decodes and accepts it only if `Entry.bytes keys k`
  of it is exactly `b`. So a read never returns an entry whose tag failed, or bytes that are not
  that entry's one spelling.
- The base names `IndexAt = (indexCount, indexLast)`. `indexLast` is the tag of entry
  `indexCount − 1`, or `Digest.zero` at 0. It binds the count to the one entry open reads, so a
  correctly-tagged entry from a rolled-back index cannot stand in for the last one.

The open, a page, the loop and `host check`:
- **Open** checks `indexCount ≤ indexMax` and `index.log ≥ count · entryBytes` (`indexShort`). It
  reads ONE entry (`lastAt`) and requires it to read back at its position with the base's
  `indexLast` (`indexNamed`, `indexCorrupt`). It folds the tail from an empty Array.
- **A page**: `Page.locate` binary-searches entries through `Page.entryAt`, which reads a disk
  entry and checks it at its position, else `badIndex k`. Past the disk entries it uses the loop's
  own. It reads at most 1 + ⌈log₂ count⌉ entries. `Page.walk` then reads frames BY OFFSET from that
  one entry, so the walk reads no further entry.
- **The loop** holds only the entries since its newest base (`Resident.install` drops the counted
  ones when a seal settles). `sealEntries` hands the Task a copy of them.
- **`host check`** (`openClean`) reads every counted entry. It requires each to read back at its
  position, name the offset of its own record frame in the recovered history, and keep heights
  non-decreasing; the count must equal the history's records (`indexClean`). Otherwise
  `indexCorrupt` (46), with `refused indexCorrupt entry K` (or `count N`).

Theorems: Host/Proofs/Index (new), Host/Proofs/Page, Host/Proofs/Base, Host/Proofs/Backup.
- **Never-served**: `build_never_served`, with `locate_got`, `entryAt_ok`, `build_located` and the
  tooth `build_badIndex`. A served page after `start` is `walk` of the segment from ONE entry `e`
  at position `k`, whose disk bytes are exactly `Entry.bytes keys k e` (`Entry.read_sound`). The
  tooth: an unreadable entry 0 refuses the page `badIndex 0`.
- **Open verifies the named entry**: `openWith_verifies_named`.
- **Entries read back by position**: `run_read` / `entriesSeq_read`. Successive seals from genesis
  read back by position, and the open check passes on them, with no premise. This replaces
  `indexEntries_pages`. Also `Entry.read_bytes`, `Entry.read_other` (an entry cannot be moved), and
  `entries_ok` with its teeth `entries_entryUnfit` / `entries_indexTooLarge`.
- **The seal**: `seal_at_end` with its tooth `seal_indexMoved`.
- **The check**: `indexClean_none`. Check reads every entry: the count equals the history's records,
  the bytes are exactly that many entries, each reads back and names its frame's offset, and
  heights never fall (`indexClean_go_rise`). Its teeth are `indexClean_unread` and
  `indexClean_count`.
- **The base binding**: `indexNamed_otherLast` (the tooth for a last entry that reads back but is
  not the base's `indexLast`) and `indexNamed_unread`.
- **Resident entries**: `openWith_tail_entries` (an open holds one entry per tail record).
- **Deployed**: `Deployed.mark_chain_width` (the deployed chain is the entry's width, so
  `entryUnfit`'s chain arm cannot fire there).
- **HOST-32 restated**: `openWith_backup` and `openWith_seg_ok` are restated over the fixed
  entries. The index part is simpler: `count · entryBytes ≤ I.size` and the last entry's bytes are a
  prefix extract, unchanged by an append.
- **`Base.codec_lawfulOn`** now covers `indexCount`.

Plants (host-sim `entryPlants`; `entryRows` at 100/200/400/800):
- a control: `indexClean` is clean on the run's own index;
- index-short: one byte short refuses `indexShort`;
- index-last-flip refuses `indexCorrupt`;
- index-other-key: the same entries re-tagged under another key refuse `indexCorrupt`;
- index-other-store: the same entries tagged for another Store under the SAME key. Spliced whole,
  open refuses `indexCorrupt`. One spliced into the middle still opens, and `indexClean` refuses it
  at its position;
- index-swap: entries 0 and 1 swapped as bytes, and re-tagged at the new positions; `indexClean`
  refuses both at 0;
- **index-middle-flip**, the ruled move: every counted entry is flipped in turn, and the plant
  checks three things:
  - every one but the last still opens;
  - `indexClean` refuses each at its own position;
  - over a page from every fifth height, every page is either refused `badIndex` at the flipped
    position or byte for byte the honest page. Hundreds of pages are refused per seed, and none is
    built from the flipped entry;
- entry-unfit: a chain one byte wider than the Store's, with a control at the Store's width;
- index-too-large: a seal past `indexMax`;
- index-moved, crash-before-rename (orphan entries of the exact size, the same count + tail as the
  newer base), backup and backup-wrong-order: all still red by name.

store-plants (OPS-2's byte-level rows) all pass. index-moved-restart-truncates truncates a 1-byte
partial entry, because the writer truncates every byte past `count · entryBytes`. host-file-sim
caught a real defect in the harness, now fixed: it ran the toy World (8-byte chains) under
`Keys.ofKey`'s deployed width, and every seal refused `entryUnfit`. `Sim.File.fileKeys` gives the
toy width.

The counts (host-sim, max over seeds 1–3):

| row | before | after |
|---|---|---|
| `open bytes-read-per-record` | 1.033 | 1.007 |
| `open index-bytes-per-base-byte-steady-at-4000` | 0.569 | 0.001 |
| `open index-bytes-per-base-byte-steady-at-8000` | 1.179 | 0.001 |
| `open bytes-read-per-allowed-byte-grow-at-1000` | 0.792 | 0.752 |
| `seal bytes-per-appended-byte` | 1.448 | 1.566 |
| `seal bytes-per-appended-byte-grow-at-1000` (raw; the net row, 3.489, is unchanged) | 4.032 | 4.131 |
| `seal hashed-bytes-per-appended-byte-grow-at-1000` | 5.012 | 5.046 (each entry's tag also hashes the origin chain) |
| the four `seal index-bytes-per-appended-byte-at-n` | 0.181 / 0.147 / 0.131 / 0.161 | 0.323 / 0.261 / 0.236 / 0.308 (flat in history) |

New rows:
- `page index-entries-read-per-log-bound-at-{100,200,400,800}` = 1.000. This is the entries read ÷
  (1 + ⌈log₂ entries⌉), so 6–7 / 7–8 / 9 / 10 entries read absolute. GATES-3 asked for the ratio,
  not the count, because the count rises with honest growth;
- `loop resident-entries-per-record-past-base-at-n` = 1.000.

**Flag day.**
- The base's last two fields change meaning: `u64 indexOffset ‖ indexTag32` becomes
  `u64 indexCount ‖ indexLast32`.
- `index.log` changes from frames of pages to fixed entries.
- The shape stamp gains `entryLayout` by name, so the stamp flips: every existing Store refuses
  `shapeMismatch` (43) and re-geneses.
- No Status is added or removed. The `indexShort`, `indexCorrupt`, `indexMoved`, `entryUnfit` and
  `badIndex` operator sentences change (OPS-2 agreed). `Store.layout`'s text changes. `emit-units
  deploy/units` re-emits EXITS.md and STORE.md.
- `Keys` gains `chainBytes`.
- `Page.build` takes a getter, a count and the durable end in place of an Array. PROTOCOL-6 agreed
  the Rows writer's adaptation.
- `indexTooLarge` SURVIVES as a bound on `indexCount`: at most `indexMax` = 2³² − 1 entries, a
  Store's lifetime in records. The search is then at most 33 entry reads, and the index file at
  most 320 GiB deployed.

**Critique.** A corrupt middle entry was refused at open; it is now refused at first read or by
check.
- Exactly that moved. Open verifies the last entry against the base's `indexLast`, so corruption of
  the newest seal's entries still stops the open.
- An entry before the last is checked only when a page reads it, `badIndex` on that one request
  (proved never served), or by `host check`. A Store with a damaged entry nobody pages through
  serves for as long as nobody runs `check`.
- An offset or height lie inside a correctly-tagged entry cannot occur without the key, so the tag
  is the whole defence. `check` also cross-checks offsets against the segment.
- `indexTooLarge`'s bound rose from `worldBytesMax` of index bytes (about 3.3·10⁶ deployed
  entries) to 2³² − 1 entries. The old bound existed because open read the whole index, and open no
  longer does. A static bound remains (law 4), and the search depth is what it bounds now.
- The index is 54% larger per record deployed (80 against 52 bytes), visible in the four seal
  index rows, which rose from HOST-30's values and stay flat.
- A page reads about 1 + log₂ n entries and verifies a MAC per probe: about 23 MACs at 5·10⁶
  records. That is O(log), which law 5 allows.

**Law-6 read (a spawned reader, before landing).** The reader rated nothing vacuous. It found one
check dropped beyond the ruling: an entry was not bound to its Store. That is fixed above
(`Keys.forStore`, plant index-other-store, `entryLayout` v2). It rated four statements WEAK.
Fixed:
- `indexClean_none` now states the heights and the count, which moved into the pure check;
- `indexNamed` has its binding tooth.
Open and named:
- `build_badIndex` has a tooth only at entry 0. index-middle-flip covers every other position;
- the resident bound is proved at open (`openWith_tail_entries`). `Resident.install`'s keeping of
  "count + held = total" is measured by the WASTE row `loop resident-entries-per-record-past-base`,
  not proved;
- `mark_chain_width` discharges only the chain arm of `entryUnfit`. The u64 height and offset arm
  is unreachable below 2⁶⁴ and is not discharged.

**Meta-critique.** The never-served theorem is stated in `Id` over a pure reader. `Host.Deployed.pager`
runs the same `build` in `IO` over the files, so the IO read is the unproved step, as for every
open theorem here. `walk` reads frames by offset instead of by entry. That is not in ROOT's text,
but it is what makes "page reads O(log) entries" true: walking by entry would read one entry per
frame.

## HOST-34 · HOST-28 BUILT: `host export` / `host import --digest` (2026-10-18, HOST-8; after KERNEL-29 b8e0f82 and CODEC-22's carried codec 28b4a38)
**What was built, as HOST-28 decided, with these exact shapes:**
- The file. Host/Carry.lean: `stamp32 ‖ head ‖ carried`. `head = from ‖ u64 height ‖ chain` is its own
  codec `host/carried-head`. `carried` is CODEC's `Codec.Kernel.carried`. `stamp` is
  `Hash.digest "nanodregg/host/carried/v1"` over the Tags of the head codec and the carried codec. It is
  computed from the codecs and never written as a literal. `digestOf` has its own domain
  (`nanodregg/host/carried-file/v1`). The file is not MAC'd.
- `Carry.read`. It checks, in this order: the digest (`digest`), the stamp (`shapeMismatch`), the
  decode of head and carried (`decode`), and that the anchor height is the carried height (`anchor`,
  a check HOST-28 did not name: the head's height is redundant with the carried height, so it is
  checked rather than trusted). Import then calls KERNEL's ONE carry (`Carry.world` =
  `Receive.carry X name nonce from carried`). A name or nonce past its bound is `usage`; any other
  `CarryRefusal` is `carryMismatch carry <name>`. Next comes the one genesis (`Host.genesis`), then
  `openWriter`, whose World's carried bytes must be the file's (`carryMismatch reopen`, the only
  refusal that leaves a directory behind).
- `export` uses `check`'s read-only open (`Check.openClean`, factored out of `Check.run`: key,
  `openFollower`, `historyClean`) and `Carry.exportFile`. That function re-reads its own file under its
  own digest and refuses `carryMismatch export` unless the file gives back the World's carried bytes and
  height. It writes OUT only, never over an existing file (`exists out`), and prints `carried`, `from`
  and `anchor`.
- One new Status, `carryMismatch` 49, fatal, with its OPS hostAction arm. stderr says
  `refused carryMismatch digest|decode|anchor|reopen|export|tooLarge|carry <kernel name>`. A file
  under another stamp is `shapeMismatch` (43).

**Theorems** (Host/Proofs/Carry; Deployed instances in Host/Proofs/Deployed):
- `read_ok`: an accepted file hashes to the digest, carries the stamp, and its carried bytes are
  exactly its tail (CODEC's canonical decode);
- `read_digest` and `read_stamp`, the teeth;
- `world_carried` and `Deployed.import_carried`: the imported World holds exactly the file's carried
  bytes at the anchor height (KERNEL's `carry_carried`), so the reopen compare is a pair assertion
  on the base codec;
- `exportFile_reads` and `Deployed.export_reads`: what export writes, import reads back;
- `exportFile_ok`: completeness. Export refuses no World whose carried state fits the codec. Its
  premises are `Carried.CodecFits` and the origin, chain and height fitting. They are NOT discharged at
  Deployed for an opened World: that needs `World.CodecFits` of an opened World, which comes from
  CODEC's decode plus the fold. This is a named gap. Soundness does not rest on it, because export
  re-reads its file at runtime.

Plants:
- host-sim carryPlants (toy Ctx, the deployed functions):
  - export→import keeps the carried bytes and the height under a new origin;
  - two nonces give two Worlds;
  - a flipped byte under the original digest gives `digest`;
  - another stamp gives `shapeMismatch`;
  - a lying head height gives `anchor`;
  - control: the file reads back.
- Live smoke on the real `host` binary (hbox logs/host8-carry-smoke, 11 KB):
  - genesis → export → import → check prints the carried height;
  - no digest gives `usage digest` (8);
  - a wrong digest and a flipped byte give `carryMismatch digest` (49), with no Store directory left;
  - export over an existing OUT gives `exists out` (17).
- OPS-2's store-plants rows (drafted against this contract) are the live plants.

**Critique.** Import writes the Store only after every pure check passed. That ordering is read off
`importVerb`; no theorem states it, because it is IO. Export reads a live Store the way `check` does,
so take it from a stopped writer (RUNBOOK §6). The carried state is KERNEL's choice (journal inside its
window, PROTOCOL-30). **Flag day:** none. A new verb pair and one new Status: deploy/units
re-renders, the restart/prevent lists gain 49, nothing re-geneses.
**Law-6 read (a spawned reader).** Nothing is vacuous. Its WEAK findings, and what each now is:
- `exportFile_reads` stated only the carried bytes and the height. Export now also checks the head's
  origin and chain, and the theorem states `r.head = ⟨w.origin, w.height, w.chain⟩`. That covers the
  lineage HOST-28 needs, not only the code's construction.
- `openWith_world` did not tie its records to the segment. It now states that they re-encode to the
  bytes after the base, from the base's tag.
- The "one refusal that leaves a directory" docstring was wrong. Any refusal from genesis on (genesis,
  openWriter, the reopen, an IO error mid-write) can leave a Store. Every refusal before genesis leaves
  nothing, and that is read off `importVerb`, not proved.
- The reopen compare is only HALF a pair assertion. `world_carried` gives the World's bytes. That
  `genesisImage` followed by `openWriter` gives back that World up to Equiv is not proved (the base
  codec round trip over `genesisImage`), and no plant reaches `carryMismatch reopen`.
- `exportFile_ok` is not discharged at Deployed. It needs `World.CodecFits` of an opened World, and
  KERNEL's journal bound is strict (`<`) where `CodecFits` allows `≤`. Named in its docstring.
- The plants use the toy Ctx. The verbs' IO (ordering, `exists`, `tooLarge`, the reopen) has only the
  live smoke and OPS-2's store-plants rows. There is no plant for a decode refusal or a kernel carry
  refusal.

## HOST-35 · a Store file absent from an existing STORE directory is `missing FILE`, refused before any handle opens; no open or append creates a Store file, no sync acknowledges bytes in an unlinked one (2026-10-17, HOST-10; HOST-9's named gap, law 7 on the real path; OPS-3 agreed the sentence and the plants)

**The defect (read off df425e4).**
- A Store whose `index.log` or `seg.log` was deleted ended in an `IO.Error` from `File.open`. `host`
  caught it as `io` 13 (Cli.main), and hosting-broker and hosting-controller as their own `io`. That
  status is named, but the name says only "some IO call failed". The file is not named in the code,
  only in the errno text.
- Worse, `openWriter` opened `seg.log` with `O_WRONLY|O_APPEND|O_CREAT` before any check. A deleted
  seg.log was silently RE-CREATED empty, and only then did the open refuse (`segmentShort`). The writer
  wrote into a damaged Store before it knew the Store was damaged, which destroys the evidence.
- Two names covered parts of the same class: `noBase` 20 (a missing base.world) and `badKey 0` (a missing
  key, 4e95dc8).

**Decision.**
- One StoreFault `missing (file : StorePart)` with Status `missing`, code 20, fatal.
  - `StorePart` is key | seg.log | index.log | base.world. It lives in Host/Base.lean beside
    `Store.layout`, and `Store.backupOrder` is now spelled from it.
  - It REPLACES `noBase` (BaseFault.noBase and Status.noBase deleted; the base case keeps code 20) and
    the 0 case of `badKey`. `badKey` now means only "not 32 bytes".
- Where it is checked:
  - `readKey` checks the key when the directory exists. An ABSENT STORE directory stays `io` 13: a
    wrong path is a different operator situation (store-plants' missing-store, unchanged).
  - `openAt` checks seg.log, index.log and base.world before its first handle, and now opens the segment
    read handle itself, returning it (Tail.open uses it).
  - `openWriter` checks all four before the append handle.
- Append mode no longer has `O_CREAT` (Host/c/file.c). No open or append creates a Store file: genesis's
  `createNew` creates them, and a seal replaces base.world by rename. A file removed between the check
  and the open cannot be re-created; that race ends in the open's ENOENT, which is `io`.
- **A file removed while the writer runs** (the law-6 reader's REAL finding). The append handles,
  the pager handles and the follower's handles are open descriptors, which an unlink does not affect.
  So before this, a seg.log deleted mid-service kept receiving appends, syncs and ACKNOWLEDGED records
  into a nameless inode, lost at the next open. Now `File.sync` fstats after the fsync and fails
  (ENOENT) when `st_nlink = 0`, i.e. unlinked or renamed over. The batch's sync failing is `uncertain`
  (HOST-4: the loop stops without acknowledging), and the restart's open refuses `missing seg.log`.
  An index.log sync failing in a seal is `sealIo` → restart → `missing index.log`.
- A seal checks that base.world is present before its rename; absent, it refuses `sealIo`, which
  restarts into `missing base.world`. A seal never re-creates a base.world that was removed under the
  writer.
- The file names are spelled once: `keyPath`/`segmentPath`/`indexPath`/`basePath` and the
  `Store.layout` rows are spelled from `StorePart.name`.
- stderr reads `refused missing index.log`. `StoreFault.name` stays `missing`, one code and one name
  (`status_iff_name` holds). `StoreFault.text` adds the file and is what `host` prints. hosting-broker and
  hosting-controller print `missing` and still end `store` 76, the pass-through convention of
  HOSTING-6 (unchanged code, broker test comment updated).

**Why not `indexShort 0` (HOST-9's guess) or a per-file name.**
- `indexShort` means "a copy cut short". An absent file is a different operator act: something deleted
  it, so restore all the files from one backup.
- At index count 0, `indexShort` cannot fire at all (0 ≥ 0). A deleted index.log in a fresh Store would
  then open clean.
- Per-file names (`indexMissing`, `segmentMissing`, …) are four statuses for one sentence. The file is a
  detail of the refusal, not its class.

**The sweep: every IO call in the deployed exes (host, hosting-broker, hosting-controller) that can throw
on a missing or unreadable file, and the status it ends as.**

| site | missing file | other IO failure (EACCES, EIO, race) |
|---|---|---|
| `readKey` (every verb, broker, controller) | `missing key` 20 / broker+controller `store` 76 | `io` 13 / their `io` |
| `openAt` (`openFollower`, `check`, `export`, `Tail.open`) | `missing seg.log`/`index.log`/`base.world` 20 | `io` 13 / their `io` |
| `openWriter` (`serve`, `follow`, `import`) | `missing FILE` 20, before the append handle; never created | `io` 13 |
| `reopenAt` (fuel restart, inside `serving`) | `reopenFailed` 38 (stderr `reopenFailed missing`) | `ioServing` 6 (restart; the fresh open refuses `missing`) |
| `serve` pager handles (seg/index, opened in `serving`) | at the open: `ioServing` 6 → restart → `missing` 20; removed after the open: the descriptor still reads the old inode, and the writer's next sync refuses (row below) | `ioServing` 6 |
| `File.sync` of the writer's seg.log append handle (every batch) | removed mid-service: the sync fails (`st_nlink = 0`) → `uncertain` 3 (nothing acknowledged) → restart → `missing seg.log` 20 | `uncertain` 3 |
| `pager` `.read` base per page | `ioServing` 6 → restart → `missing base.world` 20 | `ioServing` 6 (a page's IO error restarts the writer, not that page: an open edge; CLOSED by HOST-48: that page is refused `pageIo`, the writer serves on) |
| `fileCheckpoint` (seal) | index.log removed: its sync fails → `sealIo` 5 → restart → `missing index.log`; base.world removed: refused before the rename → `sealIo` 5 → `missing base.world` | `sealIo` 5 |
| `Check.openClean` re-reads, `chainAt` | race only (just checked present) | `io` 13 |
| `genesis` (`createDirAll`, `writeNew`) | n/a (creates) | `io` 13; a directory left behind opens `missing` |
| `import` IN, `export` OUT | IN absent: `io` 13 (not a Store file) | `io` 13 |
| `Tail.next` (broker, controller) | an open handle; an unlink does not affect it; the writer's next sync refuses, and the reader catches up to the last acknowledged record | their `io` |

No site ends as the runtime's exit 1. `Cli.main` and both hosting mains catch everything, and
`Status.code_reserved` keeps 1 unused.

**Theorems (Host/Proofs/Names.lean):**
- `StorePart.name_injective`;
- `StorePart.mem_all`, `StorePart.mem_layout` (every part is a row of `Store.layout`), and
  `StorePart.covers_layout` (every non-transient row is a part, so `openWriter`'s check over
  `StorePart.all` checks every file an open reads);
- `StoreFault.text_missing_injective`: two `missing` refusals that print the same text name the same
  file;
- `name_injective` and `status_iff_name`, re-proved over the new constructor set.

The check itself is IO (`missingOf`), so it is planted, not proved.

**Plants:**
- host-file-sim `missingPlants`: for each of the four files, a fresh genesis Store at count 0 (the case
  where an absent index.log was never "short") with the file removed. The removal is asserted first.
  - `readKey` (for the key) or `openFollower` refuses `missing FILE`;
  - `openWriter` refuses the same, and the file is still absent afterwards.
  - `plant-append-never-creates`: `File.open .append` on an absent path in an existing directory
    (both asserted), with no check in front of it, fails and creates nothing. This is the tooth for
    the O_CREAT removal itself; the plants above stop at `missingOf` before the open is reached.
  - `plant-sync-unlinked`: the same append handle syncs while its file is named (the control), and
    its sync fails once the file is unlinked.
  - `plant-seal-missing-base`: a writer opened over a fresh Store whose base.world is then removed:
    the seal refuses `io` (`sealIo`), and base.world stays absent.
- store-plants `missingPlants`, through the real `host` exe over copies of the sealed intact Store:
  - `missing-key`, `missing-base`, `missing-index` and `missing-segment`: `host check` exits 20 and
    stderr names the file;
  - `missing-index-serve` and `missing-segment-serve`: `host serve` exits 20, names the file, and the
    file is still absent after (seg.log is the file O_CREAT used to re-create).
  - These rows are counted in the run's failure total, not in `plants.length`, like the other plant
    groups.

**Flag day.** Status `noBase` is deleted and code 20 is now `missing`. `badKey` no longer covers an
absent key. deploy/units re-renders through emit-units: EXITS.md loses the noBase row and gains
missing, and badKey's sentence changes. No Store re-geneses: no byte on disk changed. What refuses
that did not refuse before: a writer over a Store missing seg.log, which used to re-create seg.log
empty and then refuse `segmentShort`.

**Critique.**
- The check is `pathExists` before the open: a TOCTOU window. A file removed inside it ends `io`, not
  `missing`. It is still named, and with O_CREAT gone it is never re-created.
- `missing` cannot tell "deleted" from "never written by a genesis that crashed". The sentence covers
  both: move the directory aside by hand.
- A page's IO error (an unreadable base.world mid-service) restarts the whole writer (`ioServing`)
  rather than refusing that one page. That is named in the table, not fixed here.
- A file removed mid-service is seen at the next sync, not at once. A `log` page read between the
  unlink and that sync reads the old inode: bytes that were durable and acknowledged, never a lie.
- `StorePart.mem_layout` and `covers_layout` are facts about data. That `missingOf` really checks
  those paths is planted (the four store-plants rows and the host-file-sim plants), not proved.

**Meta-critique.** Folding `noBase` and `badKey 0` into `missing` removes two names the operator
already had. The argument is the doctrine's "prefer one shape": all three were the same act (a Store
file absent), and the operator's action is the same. Had they differed (if a missing key meant
"never a Store" while a missing base meant "damaged"), one status would hide that difference. They do
not: genesis writes the key first, so a missing key with the other files present is damage. A
directory with nothing in it is a crashed genesis or a wrong path, and the sentence says to check
the path. The test of this decision is
store-plants: four files, one status, stderr naming each.

## HOST-36 · `host import` writes no Store path before every check passed: a theorem over the one decision function (2026-10-17, HOST-10; HOST-28's first named gap)

**The gap (HOST-34's law-6 read).** Import refuses before it writes. That was read off `importVerb`'s
IO and stated by no theorem.

**Decision.**
- `importVerb` is now `importWith` at `IO`. `importWith` is `host import`'s decision, generic in the
  monad, over a record of its effects, `ImportFx`: nonce, readIn, key, genesis, reopen, refuse and
  report.
- Two effects write: `genesis` (`Host.genesis`) creates the Store's paths, and `reopen`
  (`openWriter`) locks, truncates and syncs them. The others read IN or the OS random source, or print.
- The theorem runs the SAME function at `Except (Option (Digest × World D))`. Each effect answers a
  given result; `genesis` throws `some (key, World)` and `reopen` throws `none`. So the run ends
  `.error (some (k, w))` exactly when genesis was the FIRST writing effect reached, with `k` and `w`.

**Theorem (Host/Proofs/Cli.lean).** `import_genesis_iff`: genesis is the first writing effect,
reached with `k` and `w` ⇔
- the digest parsed;
- the nonce effect answered a nonce;
- the IN effect answered bytes;
- `Carry.importWorld` accepted them under that digest, making `w` (the stamp, the decode, the
  anchor and KERNEL's carry);
- the key effect answered `k`.

The bound on IN (`readBounded … carriedMax`) and the 32-byte key (`Digest.ofBytes?`) are the IO
instance's, not the theorem's.

The → half is the refuse-before-write claim. The ← half is its tooth: a passing import reaches
genesis before `reopen`, with the drawn key. So the statement is false of a function that never
writes, that writes first through `reopen`, or that writes before a check. Moving `fx.genesis` above
`Carry.importWorld` would need a World it does not yet have (a dummy), and the → half then fails
for it. Moving `fx.reopen` before `genesis` makes a passing run end `.error none`, so the ← half fails.

**Plants.** No new plant. OPS-2's 13 store-plants carry rows (6bfd534) already run the real exe, and
assert that every refusal before genesis leaves no Store file; they exercise this exact code at IO
and stay green.

**Critique.**
- The theorem is about the decision function. That the IO instance's effects are what their names
  say is code, not a theorem: `ImportFx.genesis` is `Host.genesis`, `readIn` is `readBounded`
  (read-only), and `key` is `IO.getRandomBytes`.
- An IO exception from an effect aborts the run. Before genesis that writes nothing, which the
  plants show.
- The two other HOST-28 gaps are sequenced after KERNEL-41 (a′), which deletes `World.Equiv`, moves
  the journal into the trie and flips the stamps. Proving them now over the old journal would be
  done twice:
  - the reopen pair (`genesisImage` → `openWriter` gives back the imported World): after KERNEL-41
    the World codec should read back exactly (`=`), not up to Equiv;
  - `exportFile_ok` for an opened World, which needs `World.CodecFits` of a decoded-and-folded World,
    whose journal clause changes in the flag day.

**Meta-critique.** "Generic in the monad, proved at Except" is a known pattern. Its weak point is
that an effect record can hide an extra write inside an effect that is not `genesis`. That is why the
record's docstring names genesis as the only Store writer, and why the IO instance sits beside it in
the same file, where a reader can check the claim in one screen.

## HOST-37 · a backup across a writer restart: what HOST-32 left uncovered, proved (2026-10-17, HOST-10; HOST-32's critique, item 1)

**The gap.** `openWith_backup` (HOST-32) models each copy of an append-only file as "the file when
base.world was copied, plus appended bytes" (`S ++ y`, `I ++ x`). A writer that RESTARTS between two
copies breaks that model: `openWriter` truncates a torn seg.log tail to its open's valid end, and
index.log orphans to its base's count. The later copy is then a cut of the file followed by new
appends, not the file plus appends.

**Decision.** Restate the backup over the cut and prove it (Host/Proofs/Backup.lean):
- `openWith_cut`: if the live files open to `o`, then the files cut at `o.pos.offset` (seg.log) and
  at `o.sealed.index.count · entryBytes` (index.log) open to exactly `o` with `torn = 0` and
  `orphan = 0`. Every read of the open (the base tag, the origin range, the one named entry) lies
  inside the cut, and the tail is `encodeAll` of the same records (`open_sound_bounded`, then
  `open_encodeAll`).
- `openWith_backup_restart`: a backup whose copies are `S.extract 0 o.pos.offset ++ y` and
  `I.extract 0 (count · eb) ++ x` opens as `openWith_backup` says. Either it gives the same base with
  at least the live records, folded on from the live state, or it refuses `tailTooLong`, `corrupt`
  at or past the live end, or `record j` past the live records. It is `openWith_cut` composed with
  `openWith_backup` over the cut files, and it strictly generalizes `openWith_backup`
  (`S ++ y = S.extract 0 pos ++ (S.extract pos S.size ++ y)`).

**The premise, named (the writer's invariant; a law-6 reader corrected its first wording).** It is
about bytes:
- `seg.log[0, o.pos.offset)` and `index.log[0, count · eb)` were durable when the backup copied
  base.world, and are never rewritten;
- a restart (`openWriter`) cuts only past its own open's valid end and count, which are at or past
  these (a later base sits at or past the live valid end and counts at least the live entries).

The live open must have read only synced bytes, which the writer's own opens do. A follower that read
page-cache bytes never synced, followed by a power loss, can see seg.log shrink below
`o.pos.offset` with no restart at all; that case is outside the premise.

So any number of restarts, seals and appends between the copies leaves copies of the stated shape.
This is read off `openWriter` and the loop, not proved over IO. host-file-sim's plant checks it on a
real Store.

**Plant (host-file-sim `restartPlants`, seeds 1–3).**
- Serve with sealing, then three more frames, so the live tail holds records. The live state is taken
  from a follower open.
- Copy base.world. Tear half a frame onto seg.log, and append half an index entry onto index.log
  (both asserted: the file grew). Restart with `openWriter`, which truncates; it is asserted to cut
  seg.log back to the live valid end and index.log back to `count · entryBytes`, and its lock is
  asserted released. Serve on until the writer seals again (asserted: its base moved past the
  copied one).
- A second order, `after-newer-base`: after the copy, the writer seals a newer base (asserted)
  BEFORE the tear and the restart.
- The backup is the key, the copied base, and the later index.log and seg.log. It is asserted to be
  the cut plus appends, not the torn file plus appends. It opens to the copied base with at least
  the live records, asserted alone with no `tailTooLong` escape. Seed 1: 22 records (20 in the
  newer-base order) against 2 live; seed 2: 25 and 27 against 1; seed 3: 33 and 35 against 4.
- Control: seg.log as the restart left it, minus its last whole frame (below the live valid end). It
  opens with FEWER than the live records (seeds 1–3: 1 of 2, 0 of 1, 3 of 4), so the plant tells
  the two apart. Seventeen restart checks per seed, all PASS.

**Critique.**
- The premise is the writer's behaviour, over IO. It would fail for a writer that truncated below its
  valid end, which `openWriter` does not do: it truncates only `0 < torn` bytes past `o.pos.offset`
  and orphans past `count · eb`. A defect there is caught by this plant and by host-sim's
  restart-at-every-cut.
- Copying a file while it is mid-truncate is still a torn read. The open reads it as a shorter or
  torn tail and refuses or folds by name, as HOST-32 states.

**Meta-critique.** The question was "prove what a backup gets, or refuse by name at open". Refusing at
open is impossible: a backup does not record when it straddled a restart, and a cut-plus-appends
file is byte-identical to a file a writer appended to without a restart. So the theorem is the
answer. The plant's control is what keeps "at least the live records" from being true of every
copy.

## HOST-38 · KERNEL-41 (a′), HOST's half: a record states BOTH roots after each Turn; the journal's invariant holds at every World the writer holds (2026-10-17, HOST-11; with KERNEL-12, CODEC-7, PROTOCOL-7 in ONE kernel! landing)

**What changed under HOST.** KERNEL-41 (a′) makes the journal a second trie with its own root, and
`chainNext` commits `(prev, turnDigest, cellsRoot′, journalRoot′)`. HOST-29's record stated the
one root after each Turn so a page could advance the chain without admitting. With two roots in the
link, one root per Turn no longer determines the next head.

**Decision.**
- A record is CODEC's `batch`: `List (Turn × (D × D))`, each Turn with `World.roots` after it (the
  cells' root, then the journal's). The writer's note is `World.roots`. `Record.runRooted` compares the
  PAIR, so a stated journal root that is not the admission's is `rootMismatch i` by name, exactly as
  a stated cells root is. `Page.walkTurnsAt` advances `chainNext E c t roots`. The follower's
  absorb (Protocol/Command/Machine.lean) and the rows' writer carry the same pairs: HOST carries those
  sites, as KERNEL-12 ruled (PROTOCOL-7 told).
- Serve's `submit`/`lookup`/`onReject` read the journal through `World.journalAt` (the trie's `get`).
- `lookup_expired_never_committed` and `lookup_expired_final` take `JournalCanon` of the World they
  start from: KERNEL's `fold_answers` / `absent_final` read after a prune, and `Trie.get_retainAt` is
  exact only on a canonical trie. It is discharged at Deployed, not left open:
  - `Host.Record.foldlM_journalOk` (Host/Proofs/Base.lean): the writer's reopen step keeps
    `JournalOk` (each record that opens is admitted Turns, `fold_journalOk`);
  - `Host.Deployed.openWith_journalOk` (Host/Proofs/Deployed.lean): the World the deployed open
    returns is `JournalOk`, from `Codec.Deployed.world_get_journalOk` (CODEC-7, on HOST's ask) at the
    base record's offset and the lemma above;
  - `Host.admitBatch_journalOk` (Host/Proofs/Serve.lean): a batch of the writer's machine keeps it
    (`staged_rooted`, `RootedFold.fold`, `fold_journalOk`).
  So every World the loop answers a lookup from is `JournalOk`, hence `JournalCanon` (`.1`).
- The reopen theorems (openWith family, the three-range open, the follower's reopen, HOST-32/37's
  backups) are generic in the World and the step: they re-verify unchanged. Nothing in them mentions
  the journal.

**Flag day.**
- Shape: the batch record's codec tag moves (a second digest per Turn), and CODEC-31 moves the World
  (`kernel/journal-order`), `kernel/world`, `kernel/carried` and `host/base/index-count` tags. So
  `Base.shapeStamp` flips: every existing Store refuses `shapeMismatch` 43 at open and at `host check`
  (checked by hand: a HOST-10 store-plants Store, `refused shapeMismatch`, rc 43; a fresh one opens).
- Re-genesis: every Store. Re-export: every carried file (its stamp moves with `kernel/carried`).
- Bytes: +1 digest per logged Turn (8 bytes in the toy, 32 deployed). WASTE rows re-pinned with the
  reason (gates/waste.tsv): `submit bytes-per-turn` 1.492 → 1.635; `seal bytes-per-appended-byte`
  1.566 → 1.689 and `index-bytes…at-200` 0.261 → 0.284 rise because the same Turns cross the toy
  seal cadence at other points (seeds 1–2 seal once more over the same 143 / 130 Turns);
  `base-bytes-net-of-growth…grow-at-1000` 3.489 → 3.520 because the same 1000 Turns append 8000
  more bytes and CODEC-31's World codec moves the base sizes (seed 1's final base 31196 → 32386 B),
  so the base/4 seal points move (35/38/39 seals at seeds 1–3, was 32/35/36); the other seven
  moved rows fell.

**Plants.** host-sim `plant-flip-root-cells` and `plant-flip-root-journal` (seeds 1–3): the first
record re-encoded with ONE of the two stated roots changed and re-sealed; each is refused
`rootMismatch 0` at record 0. A reopen that compared only the cells' root goes red by the journal
arm's name. All verdicts green on the assembled tree: host-sim ×3, host-file-sim ×3, hosting-sim ×3,
rows 21/21, store-plants, cargo launcher broker and isolation.

**Critique.**
- 32 deployed bytes per Turn for a root the reader could recompute only by admitting. The
  alternative, a record stating the journal root once at its end, makes a page that ends inside a
  record unable to state the exact chain after its last event, which is HOST-29's whole point. A
  head link that committed the journal root only at multiples of W would change KERNEL's chain, not
  HOST's: KERNEL ruled the 4-input link.
- `openWith_journalOk` is stated for the WRITER's step (`foldStep`). The tail's step
  (`tailStep`, HOSTING) is the same `Record.stepTurns` and `Hosting.Proofs.Open.open_world_canon`
  covers its cells Canon; the tail's journal is not consulted by a lookup, so no theorem is owed
  there today. Likewise the follower's `.adopt w′` (Host/Follow.lean) installs a World decoded from
  the writer's base with no `JournalOk` theorem of its own: the follower serves no `lookup`
  (`journalAt` is read only in Host/Serve.lean), so nothing rests on it; a follower that answered
  lookups would owe it (the deployed decode gives it: `Codec.Deployed.world_get_journalOk`).
- The loop's World between batches is `JournalOk` by composing three theorems; the composition is
  read off `Loop.serve` (the resident World is only ever the open's World or `admitBatch`'s), not
  proved over IO. Same standing as `staged_rooted`'s use.

**Meta-critique.** The danger in a port like this is the premise that quietly moves from "true of every
World" to "true of a canonical one" and is left at the theorem's head for a reader to discharge.
Each premise this port added is discharged at Deployed above; none is left at the theorem's head.
The WASTE rises are a cadence artifact over identical Turns, not more work per Turn: same turns,
same batches, +8 bytes per Turn, the seal points moved. The reader caught my first wording of the
grow-at-1000 reason ("one more seal at seeds 1–2"), which was false: there are three more seals per
seed, and the base sizes moved too. The reason was corrected from the logs. Found by the same
reader and filed, not fixed here: `resident-entries-per-record-past-base` prints 0 on seeds whose
run ends with no record past the base, and the max over seeds hides that.

## HOST-39 · HOST-28's reopen pair, proved: the open of what genesis (or import) writes is the World it was given; and the base bound that omitted the stamp (2026-10-17, HOST-11; HOST-28's second named gap; proof lane a5a9c62bf7f200e53)

**Defect found by the proof.** `Cadence.baseRecordMax` was `worldBytesMax + 2·(8 + tagBytes)`. The base
record is `stamp32 ‖ World ‖ u64 ‖ tag32 ‖ u64 ‖ tag32`, so the bound left out the 32-byte shape stamp.
`Base.file` (seal, genesis, import) admits any World of at most `worldBytesMax` bytes. A World within
32 bytes of the cap was therefore WRITTEN, and every open (`openWith`, `Store.lean`'s
`readBounded`) then refused it `baseTooLarge`: a Store that bricks itself at its own cap. The
generic statement of `genesisImage_opens` is false without a room premise. That is how the proof
found the defect.

**Decision.**
- `stampBytes` moves to Host/Bounds.lean, and `baseRecordMax := worldBytesMax + stampBytes +
  2·(8 + tagBytes)`: the bound states the record it bounds.
- The World cap (`worldTooLarge`) is unchanged. The open accepts exactly the largest base the writer
  can write, and nothing larger. Rejected alternative: keep the bound and have `Base.file` refuse by
  RECORD size. That makes the effective World cap `worldBytesMax − 32`, and then `worldBytesMax`
  lies about what it caps. (Asked of ROOT as a pause item: it raises an open-side byte bound by 32.)
- Theorems:
  - Host/Proofs/Genesis.lean (new): `genesisImage_opens` (generic: under `LawfulOn P world`,
    `P w₀`, the origin chain fitting, `origin w₀ = (mark w₀).2` and `baseRecordMax < 2^32`, the one
    open over exactly the genesis image returns `w₀` itself, 0 records, torn 0, at the segment's
    end). Lemmas `genesisImage_ok`, `Base.record_size`, `Base.read_file` (a base `Base.file` writes
    reads back as exactly that base; the room comes from `Base.file`'s own check), `tailRead_self`,
    `indexNamed_zero`, `openLog_empty`.
  - Host/Proofs/Deployed.lean: `genesisImage_opens_deployed` (premises `World.CodecFits` and
    `chain = genesisChain origin`). It is discharged on both real paths:
    - `genesis_reopens`: no premise beyond `Receive.genesis` succeeding (`genesisWorld_codecFits`,
      `genesis_chain_eq`).
    - `import_reopens`: no premise beyond `Carry.importWorld` succeeding (`importWorld_codecFits`,
      `read_carried_fits`, `importWorld_chain_eq`). It also concludes that the reopened World's
      carried bytes ARE the file's, so `importWith`'s `carryMismatch reopen` compare is unreachable
      whenever genesis writes the image. HOST-28's reopen pair is closed: the theorem is exact `=`,
      since KERNEL-41 deleted World.Equiv.
- `genesisImage` itself refuses only `worldTooLarge`, and both corollaries take its success as a
  premise. That refusal comes before any write (`Store.genesis`).

**Second defect found by the same proof, fixed upstream.** `import_reopens` first needed a premise
`journalFits carried.height carried.journal`. Neither CODEC's carried codec nor KERNEL's `checkCarry`
refused a carried journal outside its height's window; the World codec did. So `host import` of
such a file genesis-wrote a Store whose open refused `baseUndecodable`. CODEC-7 added
`kernel/carried-journal` to the carried codec (in the KERNEL-41 landing 5eb9b30) and folded
`journalFits` into `Carried.CodecFits`, so the premise is gone.

**Plant.** host-sim `plant-world-at-cap` (seeds 1–3): a cadence whose `worldBytesMax` is EXACTLY
the genesis World's encoded size (asserted equal). The World is written through the sim's genesis
path and reopened with the same cadence. It must open to the same World bytes, with 0 records and
torn 0. It was RED with the old formula (`FAIL plant-world-at-cap … (baseTooLarge)`, 1 FAILED) and is
GREEN with the fix. All verdicts green: host-sim ×3, host-file-sim ×3, hosting-sim ×3, rows,
store-plants, cargo launcher broker and isolation.

**Flag day.** None. No byte layout changed. A Store that holds a World below `worldBytesMax − 32`
opens as before. One that holds a World within 32 bytes of the cap did not open before and does now.

**Critique.**
- The plant covers the genesis path at the cap, not a seal mid-run at the cap. The bound is one
  formula shared by every writer (`Base.file`) and every reader (`openWith`, `readBounded`), and
  `Base.read_file` is stated over `Base.file`, so the seal path is the same theorem. It is still not
  run at the cap.
- `genesisImage_opens` is stated over `segReader` (in-memory bytes), like every open theorem.
  `Store.genesis` writes these exact bytes to files, and the open over files is `openWith` at IO.
  That is code, not a theorem: the standing gap HOST-38 names too.
- `hcap` (`baseRecordMax < 2^32`, the u32 frame length) is `decide` at Deployed. A Cadence with a
  larger cap would make the theorem's premise false rather than the Store silently broken. The
  premise is named, so that is visible.

**Meta-critique.** Both defects were invisible to every plant and sim: they live at a boundary no
run reaches (the size cap) or at an input no honest exporter writes (a mis-windowed carried
journal). Both fell out of trying to state "what genesis writes, opens" with no premise. A premise
the proof could not discharge was the signal both times. The tempting move was to leave
`hroom`/`hj` at the theorem's head as "named premises". That would have been an honest label on
a broken writer.

## HOST-40 · HOST-28's last gap: `host export` refuses no World the deployed open returns, with the two facts it cannot have named (2026-10-17, HOST-11; proof lane a5a9c62bf7f200e53)

**Gap.** `Carry.exportFile_ok` (export refuses no World whose carried state fits the codec) was
stated generically. Its docstring said it was NOT discharged at Deployed, because an opened World's
`World.CodecFits` needed a theorem about a decoded base folded by admission.

**Decision.** `Host.Deployed.openWith_exportFile_ok`: for every `o` the deployed open returns,
`Carry.exportFile X.env digestCodec o.opened.world = .ok (Carry.file … o.opened.world)`, with ONE
premise, `hallow`.
- `Kept w` is the part of `World.CodecFits` that admission keeps: trie Canon, Slotted, every live
  cell fits, `JournalOk` and height < 2^64.
  - `kept_admit` preserves it (KERNEL's admit_canon, admit_slotted, admit_cellsFit,
    admit_journalOk, admit_height_lt).
  - `Record.foldlM_kept` carries it over records.
  - `openWith_kept`: the base World has it because the deployed codec read it
    (`world_get_fits`).
- The cell listing ≤ worldMax is DERIVED: `openWith_listing_lt` shows every World the deployed open
  returns lists < 2^24 leaves. Its three lemmas:
  - `world_size_listing`: each listed leaf costs ≥ 33 bytes of the World's encoding;
  - `admit_listing`: an admitted Turn adds at most one leaf per touch, created cell or nullifier,
    each costing ≥ 32 bytes of its logWeight;
  - `record_turns_le`: a record's bytes ≥ its Turns' logWeight.
  Over the base bound (`baseRecordMax`) and `tailMax`, this gives 32·L < 2^29. A first draft
  carried it as "a codec limit"; the reader showed that the open's byte bounds imply it.
- `fits_of_kept` assembles `World.CodecFits` (`journal_bounded`, `journalFits_of_ok`), and then
  `carried_fits` and `exportFile_ok` finish.
- `hallow` (allowance < 2^64) is a REAL KERNEL defect, cv 01a14ba9-cbf4, reachable through
  `host import`.
  - Import a carried allowance of 2^64−1 (CarryFits allows it) holding a live heavy cell, then
    submit a light Turn that retires that cell. The retire credits the full weight, and the
    allowance passes 2^64.
  - The next seal then writes a World whose nat64 does not read back, and export refuses.
  - `host genesis` cannot reach it (allowanceMax 2^27, `fold_conserves`).
  - Fix (KERNEL/CODEC): GenesisFits, CarryFits and World.CodecFits bound weight + allowance
    < 2^64. ROOT is told.
- `exportFile_ok`'s docstring now says what Deployed proves and names the one open premise.

**Plant.** None new. export/import plants exist (host-sim carryPlants, store-plants). A theorem of
completeness has no runtime refusal to plant. Its tooth is the existing
`exportCheck` refusal of a World outside the codec (CODEC's carried teeth).

**Critique.** One premise remains on a theorem stated at Deployed: a missing upstream bound with a cv.
The theorem is still worth landing. It is the first statement that the opened World meets every
OTHER conjunct, so the cv's fix is the whole remaining distance. The listing bound is stated at the
deployed numbers (2^24 against 2^32 − 1) and rests on them. A Cadence with a far larger base would
have to re-prove it, and the theorem would not silently cover it.

**Meta-critique.** The lane wanted `hallow` dischargeable and found it was not. The cause is a
genesis predicate that bounds a field instead of the invariant `fold_conserves` actually carries.
The first draft also called `hcount` terminal. It was transmutable, and the reader caught it. A
label of "limit" on a premise is a claim, and it is checked like any other.

## HOST-42 · KERNEL-44/47, HOST's half: the Host commits through `Receive.judge`, a recorded refusal is a step of the log, and a log position is a STEP count (2026-10-18, HOST-12; with KERNEL-14/15, CODEC-8, PROTOCOL-8 in ONE kernel! landing). Retires HOST-8's "the Host keeps no record of refusals".

**Decision.**
- **One judgement per submit.** `Host.handle` decodes the call. A journaled call answers `ok` with its original receipt (KERNEL-7, unchanged). An unrecorded call past `journalForgets` answers `uncertain forgotten` (KERNEL-33, unchanged; it consults the record FIRST). Otherwise the Host calls `Receive.judge X w c` ONCE and commits exactly what it returns:
  - `admitted t w'` commits `.turn t` (`ok`, the receipt);
  - `recorded v r w'` commits `.refusal r`: the refusal is a step of the log, final within the window (`judge_recorded_final`);
  - `declined v` commits nothing.
  The status of every refusal is PROTOCOL's one rule, `Protocol.Settle.verdictReply`: `refused` when final (recorded now, recorded before with the RECORDED name `codeName code`, or late), `declined` (status 5) when not. An undecodable submit is `declined`; `unknownOp` stays `refused` (it names no op, so it carries no attempt).
- **The loop takes no second step.** `Answer.admit` (the loop re-ran `World.admit`) is REPLACED by `Answer.commit step w' status payload`: the handler already took the step through `judge`, and a loop-side re-admit would double every Turn's hashes. `Machine` loses its `admit`/`refuse` fields and its refusal type. `staged_rooted` takes the transition and a law as arguments, `Machine.Commits m step` ("every committed step is `step`'s"), and `machine_commits X` discharges it at `World.step`. `onReject` is deleted: `judge` reads the journal of the World the batch has advanced, so an identical call earlier in the batch is answered by the journal arm.
- **`lookup`**: journaled → `ok`; recorded (`refusedAnswer`) → `refused NAME` (the recorded code's name); `journalForgets` → `uncertain forgotten`; window ended → `refused expired`; otherwise `absent`. PROTOCOL-33's shape.
- **The log is `List (Step D × D)`.** `Record.codec` is CODEC's batch: each step with the ONE roots digest (`World.roots`, KERNEL-47 amendment 3) after it. `runRooted`/`stepTurns`/`step` take `World.step` (`Record.Fault.turn` → `.step`, name "step"). The writer's and the follower's reopen, the tail, `host check` and every backup fold steps: a recorded refusal is checked at every open as a Turn is (bounds, window, budget, the stated roots). A carry carries no refusals.
- **A log position is a STEP count** (KERNEL-47 amendment 1; refusals do not advance height, so two records can begin at one height, never at one step count): `Recorder.mark w := (w.steps, chain)`; the index entry's u64 is steps (`entryLayout` v3, the shape stamp moves); `Sealed.steps`/`Pending.steps`; `log`'s `start` and a page's position are steps; a page is `(events, steps, chain, tipSteps, tipHeight)` with each event a TAGGED step (`0 ‖ call` a Turn, `1 ‖ call` a recorded refusal, PROTOCOL-8); the `read` page states the base's steps (PROTOCOL-8 renamed the field, its Thin pins count steps; `Host.Follow` hands Thin `World.steps`); the fuel-restart compare (`agrees`, the Host's own follower of itself) compares (steps, chain); `host check --anchor STEPS:CHAIN`, STATUS gains `steps=` and `base_height` becomes `base_steps` (OPS's Plants re-keyed; no Protocol row parses them).
- **Export** builds `Carried.CodecFits` directly from `Kept` (`carriedFits_of_kept`: cells, budget, height, journal). A carry carries no refusals, so `openWith_exportFile_ok` keeps its no-premise statement without a refusals listing bound or `stepsLt`. `Kept` gains nothing; `kept_refuse` (a refusal moves none of its parts, `refuse_frame`) and `kept_fold` over steps (`fold_keeps`).
- **No new Status.** Nothing in the Host's exit table changes: a refusal step is a step, and its faults are the existing `log`/`record` refusals.

**Theorems (restated or new).**
- New: `machine_commits` (through PROTOCOL's `Settle.judge_admitted`); `judge_journaled` (a journaled call is never admitted nor recorded); `step_submit` RESTATED from `Receive.submit` to `judge`: the step keeps `judge`'s World and stages exactly its step, except the forgotten arm, which changes nothing (no premise beyond the frame's op and decode, as before); `handle_lookup_refused`; `lookup_recorded_answers` (a call `judge` recorded is answered `refused v.name` by lookup on every later World below `journalForgets`; through KERNEL's `refused_answers` and `codeName_code`); `recordedName_ne_expired`; `admitBatch_refusalsOk`, `Record.foldlM_refusalsOk` and `openWith_refusalsOk` (so `lookup_recorded_answers`' `RefusalsCanon` premise is discharged at every World the writer holds, as `openWith_journalOk` does the journal's); `recorder_mark`; `kept_refuse`; `carriedFits_of_kept` (replaces `fits_of_kept`).
- Premise ADDED, named: `handle_lookup_expired` / `handle_lookup_forgotten` gain `refusedAnswer X w c = none` (KERNEL-47's "not journaled" becomes "neither journaled nor recorded"; a recorded call answers `refused NAME` first).
- Shape only (`List Turn` → `List Step`, two roots → one digest): `staged_rooted`/`run_rooted`/`step_rooted` (+ `hm`), `Record.runRooted_ok`, `Record.step_rooted`, `Record.step_origin`, `Record.foldlM_journalOk`, `lookup_expired_never_committed`, `lookup_expired_final` (conclusion over `Step.turns l`), `fold_listing`/`record_steps_le` (renamed from `record_turns_le`; over `stepWeight`), `kept_fold`, `build_located`/`build_never_served` (Acc.steps), the Index proofs (`Entry.steps`), `Anchor.verdict_*` (`a.steps`); Hosting's `update_tracks`/`absorb_tracks` (over `Step.turns`), `runRooted_fold`, `stepTurns_fold`, `absorbRecords_fold`, `tail_absorb_fold`. The backup theorems (HOST-32/37) are generic in the record step and needed no change: they hold of the step fold.

**One `mark`.** `Record.mark E w := (w.steps, E.bytes w.chain)` is the position every Store reads; the deployed recorder and the toy one both ARE it (`recorder_mark`), so `plant-steps-differ` tests the deployed definition, not a copy (the law-6 reader's finding).

**Plants (host-sim `refusalPlants`).** `plant-refusal-survives-reopen` (three refusals among thirty Turns, across fuel restarts, are in the reopened World at their ids, steps 33, height 30); `plant-steps-differ` (a reopen one step off is refused `reopenDiverged`; judged by (height, chain), the position before this day, the same reopen PASSES, the tooth); `plant-lookup-recorded` (`refused stale` where the World without the record answers `absent`, the code before this day; past `journalForgets` still `refused stale` while kept; after the prune at 3·windowMax, `uncertain forgotten`). The toy machine's frames now carry CODEC's step codec and commit through `World.step`; `plant-flip-root` flips the one digest.

**Law-6 read (read-only reader): LAND.** Its WEAKs, fixed before staging: no open-side `RefusalsOk` (now `openWith_refusalsOk`); the steps plant tested a toy copy of `mark` (now one `Record.mark`); the refusal reply count could not tell a recorded refusal from a rejected one (now also checks the recorded code's payload); `judge_admitted` re-proved PROTOCOL's (deleted; `machine_commits` uses `Settle.judge_admitted`); `record_turns_le` renamed. Left, named: no sim plant drives `Host.handle`'s submit through `judge` (the toy machine commits steps directly; the recorded/declined submit arms are covered by `step_submit` and `machine_commits`, and by PROTOCOL's rows, which run `Host.handle`, e.g. its `refused` row).

**WASTE.** Re-pinned with reasons (gates/waste.tsv): `submit bytes-per-turn` 1.635 → 1.510 and `seal bytes-per-appended-byte` 1.689 → 1.534 fall (one digest + a tag byte per step where two roots were); nine seal/open rows RISE because their denominator (appended bytes) fell by 7 B per step while seals and entries did not; every bounded row stays under its bound (net ≤ 4, open ≤ 1).

**Flag day.** The batch record (steps, one digest), the World codec (refusals, steps) and the index entry (v3) move the shape stamp: every Store re-geneses, and an old base refuses `shapeMismatch` before any byte is decoded. `--anchor` and STATUS fields re-keyed to steps.

**Critique.**
- `step_submit` now has an exception arm (forgotten) where it had none: past `journalForgets`, a call `judge` WOULD record (an authenticated call with an over-wide window still inside it) is answered `uncertain forgotten` and not recorded. Not a lie (uncertain is never final), but the Host is not exactly `judge` there, and the theorem says so rather than hiding it.
- `plant-steps-differ` doctors a World's counter; a real lost refusal also changes the chain and would be refused by either compare. The plant shows the compare reads steps, not that steps catch something the chain does not; that is `chain_binds`'s job (KERNEL).
- Nine WASTE ceilings rise. Each is a denominator fall, argued per row, but a ceiling that rises on argument is exactly what the gate exists to make loud.

**Meta-critique.** The deepest change here, positions in steps, came from asking what the follower must compare, not from the refusal record itself: KERNEL-47's step counter forced it into every place the Host names a point in the log (index, pages, read pages, anchors, restarts). I found the read page's height only because the thin pin was PROTOCOL's to rename; a position number defined in one layer and read in another is the shape to grep for next time.

## HOST-41 · a follower wrote records its own reopen refuses: a page holds at most one record's steps, and no writer encodes a count its decode refuses (2026-10-17, HOST-11; found by reading, confirmed red by lane a53d31d238840be6e; rebased over the refusals day 38d94e1 by HOST-12, landed after HOST-42)

**Defect (REAL, confirmed red).**
- A batch record's codec is `batch recordTurnsMax dc`, a `rawList 64`. Its `put` writes any length; its
  `get` refuses a count above 64.
- The writer stages at most `batchMax = recordTurnsMax` Turns per record, so it was safe.
- The FOLLOWER (`Follow.loop`) appends all Turns absorbed from ONE `log` page as ONE record, and a page
  was bounded only by bytes (~255 KiB of events, hundreds of small events).
- So a follower catching up on more than 64 Turns in one page wrote a record its own reopen refused
  (`record j`), and the Store never opened again.
- host-file-sim `plant-follow-wide-page`, red on main 71379a1: a 100-Turn writer log, one page of 100
  events, the deployed `Host.append` returned ok, and `openFollower` refused `record`.
- No row or sim drove the follower's append and then a reopen across more than 64 Turns. The Loopback
  rows keep follow state in memory and never append.

**Decision.**
- `Page.walkTurnsAt` stops a page at `recordTurnsMax` events: it is full when the 64th is pushed.
  So a page never holds more Turns than one record may. A catch-up takes ⌈n/64⌉ pages instead of
  ⌈bytes/budget⌉.
- `Record.encode` returns `Option`: `none` above `recordTurnsMax`. A writer cannot encode a count
  its decode refuses (law: what is written reads back).
- `Host.append` takes the staged pairs and encodes them itself, so the writer and the follower share
  ONE guarded path. A follower handed a page over the cap (a writer that does not obey it) is refused
  `recordTooLarge` by name and writes nothing. It is the existing Exit, now carrying
  `(turns, bytes?)`: no new Status and no Ops sentence.
- Theorems:
  - `Page.build_events_le`: every page `build` returns holds at most recordTurnsMax events.
  - `Record.encode_eq_some`, `encode_none`, `Record.encode_decode`: under `LawfulOn PD dc` and the
    pairs' fit, what encode returns decodes to exactly the pairs.
  - `Record.step_encode`.
  - At Deployed: `runRooted_fits` (pairs a rooted run admitted fit the codec: `admit` checks
    bounds first), `limits_batchMax`, `recorder_encode_none` (deleted in HOST-50), and `foldStep_recorder_encode`. The
    last says a record encoded from admitted pairs reopens to the World the run reached, with no
    premise beyond the admission.

**The fork, stated (a reader asked).**
- (a) CHOSEN: the page holds at most one record's Turns. One invariant, a theorem, and no new
  write-path state.
- (b) Rejected: keep pages byte-bounded and have the follower split one page into ⌈n/64⌉ records
  inside `append`. Each chunk needs its own `makeRoom` (else several frames land between seal
  checks and the tail can pass `tailMax`, which open refuses `tailTooLong`), and a seal mid-page
  needs the intermediate World, which absorb does not return. That is more state on the write path
  for a throughput gain.
- The price of (a): catch-up per command becomes `pagesPerCommandMax` (28) × 64 = 1792 Turns, where
  it was thousands of small events per page. A member further behind takes several commands and is
  `behind` meanwhile.
- The writer itself stages at most 64 Turns per batch, so one page per writer record matches its
  granularity. If 1792 is too low, the knob is PROTOCOL's `pagesPerCommandMax`, not the page.
- PROTOCOL-7 AGREED: `behind` is its own restart-class exit (CommandExit 51), so a timer re-runs it; pagesPerCommandMax rises only with a measured reason. An over-cap page is refused at the reader as `pageTooLong` (Protocol, beside chainMismatch), and append's guard stays as the backstop.

**Plants.**
- host-file-sim `plant-follow-wide-page` (over real files, the real `Host.append` and
  `openFollower`): pages [100] → [64, 36], and the follower Store reopens to the writer World.
- `plant-follow-wide-page-refused`: an over-cap append is refused `recordTooLarge`, seg.log is
  unchanged (44 → 44), and the Store still opens. It was red before the fix: appended 44 → 7284,
  and the reopen refused `record`.
- The plant uses the deployed `recordBytesMax`, so the byte check cannot pre-empt the count.
- host-sim's deployed-budget page check is restated: it holds exactly min(64, remaining) events and
  states the chain at its last height.
- All verdicts green (host-sim, host-file-sim and hosting-sim ×3, rows, store-plants; whole tree
  460 jobs). WASTE: no row moved. Page counts are not a WASTE metric.

**Rebased over the refusals day (HOST-12, on 38d94e1).** A page's events and a record's pairs are
STEPS now (HOST-42), so the cap is on steps: a page holds at most `recordTurnsMax` steps, `Record.encode`
refuses more than that many `(Step, roots)` pairs, and `Persist.steps` is the follower's batch. The
Deployed theorems take `World.step`: `step_fits` (a Turn by `checkBounds_fits`, a refusal by CODEC's
`checkRefusedBounds_fits`), `runRooted_fits`, `foldStep_recorder_encode`. The file-sim plant pages by
steps. Verdicts on 38d94e1 + this: host-sim, host-file-sim, hosting-sim ×3 and store-plants ALL PASS
(`plant-follow-wide-page` pages [64, 36]; `-refused` seg.log 44 → 44). The reader-side `pageTooLong`
is PROTOCOL-9's to restate over the new absorb (PROTOCOL-8's handoff item 0); it lands in the same commit.
Law-6 read of the rebase (read-only reader): LAND. Fixed: `limits_batchMax`'s docstring claimed a
staged bound no theorem stated; `Machine.staged_size_le` (at most one staged pair per request) now
states it. Left, named: `foldStep_recorder_encode` takes the rooted run as a premise (the writer's is
`Machine.staged_rooted`, the follower's `Protocol.Command.step_persists_admitted`; no single theorem
from `append` to reopen); `recorder_encode_none` (deleted in HOST-50) is `Record.encode_none` at the deployed recorder,
an instance, not new evidence; a foreign page over the cap stops the follower `recordTooLarge`
(safe: nothing written) until PROTOCOL's `pageTooLong` refuses it at the reader.

**Flag day.** None in bytes (record and base layouts unchanged). A follower Store that already holds a
record over 64 Turns still refuses `record` at open. None exists: every Store re-genesised at 5eb9b30
today. Consumers that page (`Command.step`, the phone, Thin) see shorter pages. Each already pages
"until its height reaches tip", and rows stay 21/21.

**Critique.**
- `Follow.loop` is fixed to the deployed Digest and reached only through Host/Cli. The plant drives
  its exact `append` call and the follower's open, with the follower's admission stood in by
  `runRooted` over the writer's records, because toy events are empty and cannot be re-derived from
  page bytes. The CLI loop around that call is read off, not run at more than 64 Turns.
- 32 MiB `recordBytesMax` vs the real largest record (4 + 64·(weightMax + 64) ≈ 16.0 MiB) is now
  a question with a precise answer: every record is ≤ that by construction. Shrinking the bound
  (and with it the torn window) is the next item.

**Meta-critique.** This is the third instance today of the same class: a writer that can write what
its own reader refuses (HOST-39's base bound, the carried journal window, this). Every one was
invisible to green plants. The cheap general check is now law in Host: every encode on a write path
returns `Option`/`Except` over the SAME bound its decode enforces, and a theorem ties the two.

## HOST-44 · KERNEL-46/48 (rows), HOST's half: the carried state and the base carry rows; `host export` stays complete with no premise (2026-10-18, HOST-12; with KERNEL-17, CODEC-9/10, LANG-14 in ONE kernel! landing)

**Decision.**
- **No Host code moves.** The base is CODEC's World codec and the batch record CODEC's step codec; the rows trie rides inside both, so the shape stamp flips through the World and carried tags (CODEC-9) and every Store re-geneses; an old base refuses `shapeMismatch`, an old carried export refuses by its stamp. `Carry` reads the new `Carried` (rows last) unchanged.
- **`Kept` becomes a structure** (named fields, so a later part moves no projection) and gains `rowsCanon` (what `admit_conserves` now reads, the weight being cells + rows) and `rowsOk` (KERNEL-17's `World.RowsOk`: every entry fits, every head sums its rows, every relation's parent is live). `kept_admit` takes them through `admit_rowsCanon` and `admit_rowsOk` (at `Receive.deployed_lawful`), `kept_refuse` through `refuse_rowsCanon`/`refuse_rowsOk` (a refusal moves no row); `kept_of_fits` reads them off the decoded base (`RowsCodecFits`).
- **Export completeness keeps its statement.** `carriedFits_of_kept` fills `Carried.CodecFits.rows` by CODEC-10's `Deployed.rowsCodecFits_of_ok` from `rowsCanon`, `rowsOk` and the rows listing's length; that length is DERIVED, never a premise: `world_size_listing` now counts 33 bytes of the World's encoding per cell leaf AND per rows entry (`rows_entry_size`), `admit_listing` bounds cells and rows together (a rows entry per row touch, KERNEL's `admit_rows_listing`, each touch ≥ 32 bytes of the log weight), so `openWith_listing_lt` states cells + rows < 2^24 for every World the deployed open returns. `openWith_exportFile_ok` is unchanged in statement and premise-free (ROOT ruled option 2, a premise on it, out).
- `genesisWorld_codecFits` / `importWorld_codecFits` fill the new `rows` field (genesis: the empty trie; import: the carried rows).

**Theorems (restated or new).** New: `rows_entry_size`, `admit_cells_listing` (the cells-only part, stronger than before: bounded by the touches/creates/nullifiers parts of the log weight). Restated over cells + rows, no new premise: `world_size_listing`, `admit_listing` (+ `RowsCanon`, which `Kept` carries), `fold_listing`, `Record.foldlM_listing`, `openWith_listing_lt` (the sum). `carriedFits_of_kept` takes the rows count where it took the cells count (both discharged at Deployed by `openWith_listing_lt`). `kept_*`/`Kept` as above.

**Plants (host-sim `rowsPlants`).** `plant-rows-survive-reopen`: a parent with a declared relation and one row, served as two Turns through the toy loop under a cadence that seals every batch, is in the World the open reaches from the sealed base with no record replayed (same listing, same rows root, the head counting its row). `plant-rows-carry`: a World holding rows exports and imports through the real carry codec (Kernel.Sim's ctx) with its rows; the tooth: the same World with its rows emptied exports different carried bytes, so a carry that dropped rows is caught.

**Law-6 read (read-only reader): LAND.** No tautology, no collapse; the only added premises are `RowsCanon` on the listing lemmas (carried by `Kept`) and the rows count on `carriedFits_of_kept` (discharged at the deployed open); `openWith_exportFile_ok` byte-identical in statement. Its WEAK (the reopen plant could pass by replay alone) is fixed above.

**WASTE.** Re-pinned (gates/waste.tsv): nine rows fall; two rise, each still under its bound: `seal bytes-per-appended-byte` 1.534 → 1.676 (seed 1's seal points moved: one more base crosses the toy cadence; each base now carries the rows trie) and `seal base-bytes-net-of-growth-per-appended-byte-steady-at-8000` 3.905 → 3.912 (≤ 4).

**Flag day.** World and carried codecs (CODEC-9) move the stamp: every Store re-geneses; old bases refuse `shapeMismatch`; old carried exports refuse by stamp.

**Critique.**
- The listing bound is stated for cells + rows TOGETHER (< 2^24) and split to each ≤ worldMax; a deployment with a far larger base would have to re-prove it, as before.
- The trust point is that KERNEL's `World.RowsOk` says what the codec's rows checks say (`rowsCodecFits_of_ok` is that bridge, proved by CODEC-10); were they to drift, the export's own `exportCheck` still decodes what it writes, so a drift surfaces as a refusal, never as a bad file.
- The reopen plant runs under a cadence that seals every batch, so it reads the rows from a sealed base (the World codec) with no record replayed; a reopen that only replayed records would have hidden a base codec that dropped rows (the law-6 reader's finding).

**Meta-critique.** The one place the rows day reached HOST's theorems was a length nobody bounds statically (parents are not bounded): CODEC-10 said so plainly, and the open's byte bounds were again the answer. The open is the Host's one source of every size fact; a new trie in the World should be met by asking what the open's byte bounds say about it first.

## HOST-43 · an operator's seal: `host seal STORE` on a stopped writer, the one act the rows' checkpoint and a thin member's adopt both use (2026-10-18, HOST-12; CLIENT-5's finding via ROOT; PROTOCOL-9/10/11 co-sign the rows side; APPROVED by ROOT as proposed, with three conditions, built here).

**The gap (CLIENT-5, measured through the real host).** A thin member adopts a base by its pin (steps, digest). The deployed writer seals only at its cadence (`max(sealMin, base/4)`, HOST-14), so the base an inviter can name is whatever the last cadence seal happened to be; `adopt INVITE KEY` answers `baseMoved` unless the inviter's tip IS that base. The rows pass only because `Protocol.Rows.Writer.checkpoint` seals on demand: a harness act the deployed host does not have, i.e. a twin (law 1).

**Decision.**
- **`host seal STORE`**, a CLI verb on the Store's path (the operator's filesystem access, never a socket op): `openWriter` (it takes the Store's flock, so a RUNNING writer refuses it `locked` by name: the verb is stopped-writer-only by construction, no new state), then ONE seal of the opened World at its position through the writer's own `Checkpoint.write` and `installBase` (the same entries-since-base, sync, rename, sync-dir path as a cadence seal), then exit 0 printing `sealed steps=S chain=C digest=D` (what an inviter pins). At a Store whose newest base is already at its tip it seals nothing and prints the same line (idempotent).
- **Operator-only, and why.** A seal writes the whole World (up to `worldBytesMax`) and hashes it; a member able to trigger one could force O(World) work per request, a DoS surface the cadence exists to bound. So no op on host.sock or follow.sock seals: a member's frame asking for one names no op in PROTOCOL's table and is refused `unknownOp` by name, as any unknown op is. The verb needs the STORE path, which only the operator (and the supervisor's unit) holds.
- **One act (law 1).** The verb's core is `Loop.sealNow (ck : Checkpoint W) (mark) (r : Resident W)`, generic in the Store's effects through `Checkpoint` (the file checkpoint for the verb, `memCheckpoint` for the sim and the rows), and the loop's own inline seal (`makeRoom`) IS it; `Protocol.Rows.Writer.checkpoint` is to call that same function over its in-memory Store (stop, `sealNow`, restart), so the harness and the deployed host share one act. NOT YET in this landing: `Protocol/Rows/Loopback.lean`'s `restart sealFirst` still calls the checkpoint's `write` directly (no tip guard, no settle): the twin this decision names, removed by PROTOCOL-11's re-cut under ROOT's condition (1), this landing's next.
- **No new Status.** Its refusals are the open's (`locked`, `missing`, `shapeMismatch`, …) and the seal's (`sealFailed worldTooLarge`, …), already in the exit table; no Ops sentence changes. RUNBOOK gains the inviter's step: stop the writer, `host seal STORE`, start it, `nd invite` with the printed pin. STORE.md unchanged (no layout change).

**PROTOCOL-10's co-sign, with two amendments (taken).** (1) `sealNow` is generic in the Store's effects so the rows' in-memory Store (Protocol/Rows/Loopback's Writer) instantiates it with NO adapter (a shim would be the twin); its signature is shown to PROTOCOL before it is built. (2) Each thin row gains a line that adopts against an unsealed tip and must read `baseMoved`; the plant `sealIgnored` (the rows' `.seal` skips `sealNow`) turns that line and the next adopt line red by name. `plant-member-seal` (`unknownOp`) is the HOST-side tooth and is not duplicated in the rows.

**As built.** `Loop.settlePending` and `Loop.sealNow` (makeRoom now calls it); `Cli.SealFx` / `sealWith` (the verb's decision over its effects: key, the writer's open, the one write, refusal, report) and `sealVerb` over the files; the verb prints `sealed steps=S chain=C digest=D` (`Sealed.steps`, the base World's chain, `Keys.worldDigest` of its bytes: the digest the `read` header states and a thin pin matches). Smoke on the built binary: genesis, `host seal` prints the genesis base's pin, a second `host seal` leaves base.world byte-identical, a missing STORE is `io` (13).

**`makeRoom` changed by one guard.** It settles the seal in flight, checks the tail, and seals through `sealNow` as before; `sealNow`'s own guard (no seal when the newest base is already at the position) can fire there only for a frame larger than `frameMax` (`within_after_seal`), where the old code rewrote an identical base and the new skips it; both then stop `recordTooLarge`. `Host.Follow`'s adopt keeps its own settle-then-seal of the ADOPTED World (a different World at a reset index: not `sealNow`'s act).

**The bridge, named.** `sealed_opens` is about `Base.seal`; that `sealNow` calls exactly it (through `memCheckpoint`/`fileCheckpoint`'s `write`) is read off the two checkpoints, not a theorem (the checkpoints are IO).

**ROOT's conditions.** (1) PROTOCOL-11 re-cuts the thin rows (thin, thinStale, invite's thin half) and CLIENT-26's adopt plant against `sealNow`, with the invite base-pin fix (follow records its own digest at each writer-stated base; `invite` pins the newest base it verified; `baseMismatch` / `noBase`), in this landing or the next. (2) OPS-4 re-renders nothing (no Status, no layout change) and writes RUNBOOK's inviter paragraph and three store-plants rows (`seal-live-writer-locked`, `seal-base-is-the-pin`, `seal-again-idempotent`) after this lands. (3) The live-writer seal stays deferred; its TRIGGER is a measured inviter downtime on a real deployment (the cold reopen a stopped-writer seal costs, against THE BAR's 60 s) that an operator reports as too long.

**Theorems.** `seal_writes_iff` (Host/Proofs/Cli.lean): the seal effect, the one that writes, is reached with the opened Store EXACTLY when the key read and the writer's open succeeded (refuse-before-write; its ← half the tooth). `sealed_opens` (Host/Proofs/Seal.lean, a proof lane): for ANY open `o` of a Store, `Base.seal` of `o`'s World at `o.pos` (what `sealNow` does through a checkpoint) gives a Store whose one open, over the segment as the writer cut it, is EXACTLY `o`'s World, no record replayed, no torn byte, the same position, and the very `Sealed` that `settle`/`install` build; `sealed_opens_clean` (a clean segment, `S.size = o.pos.offset`); the tooth `sealed_unindexed_refused` (the base installed without its index page is refused `indexShort` by name: the crash-before-index order matters); `sealed_opens_deployed`. Generic premises discharged at Deployed: the World codec's lawfulness, `foldStep_originChain`, the cap. Two premises of the Deployed instance are NAMED GAPS, cv 01a14e33-3911: `hfit` (the opened World is in the World codec's domain: an `openWith_codecFits` still owes the refusals listing bound, stepsLt, refusalsDisjoint, height ≤ steps beyond what `Kept` + `openWith_listing_lt` give) and `hpos` (the position below 2^64).

**Plants.** host-sim `sealPlants`: `plant-seal-verb` (a Store with a 186-byte tail past its base; after `sealNow` the newest base is at the tip and the one open replays no record to the same World and position); `plant-seal-again` (a second seal writes nothing: no base, no entry, no byte); `plant-member-seal` (the member op table is pinned to its six ops, none a seal, so a new op reds the plant until HOST re-reads it; and all 249 codes naming no op are refused `unknownOp` and stage nothing). The live-writer `locked` case is OPS-4's store-plants row over the real binary (two processes). PROTOCOL-10's thin rows re-cut against `sealNow` (their tooth: an adopt against an unsealed tip still refuses `baseMoved`).

**Alternatives weighed.** (b) a member-gated seal op on host.sock: refused, the DoS surface above. (c) the inviter pins the writer's newest CADENCE base (follow notes base digests at the writer's stated base steps): PROTOCOL's to build, no Host change, and it avoids downtime; but an inviter must have folded past a base first, so a fresh World cannot invite until a cadence seal. Proposed: (a) now; (c) remains open as PROTOCOL's improvement. A LIVE-writer seal (an operator socket) avoids the inviter's downtime (one cold reopen, ≤ THE BAR's 60 s); not proposed until downtime is measured to matter.

**Law-6 read (read-only reader): LAND after fixes, taken:** the decision said the rows already call `sealNow` (they do not yet: Loopback:607 still writes directly; now stated as pending); `makeRoom`'s one-guard change is now stated; `plant-member-seal` had no tooth against a future seal op (the op table is now pinned).

**Critique.** A stopped-writer verb puts the inviter's writer down for a reopen; frequent invitations make that real downtime. The verb also gives the operator a way to grow the base series faster than the cadence (each seal a whole-World write): operator-chosen, bounded by their own patience, not a member's.

**Meta-critique.** The rows passed with a seal the deployed host could not perform; a harness act with no deployed twin is the same "test passes, product cannot" shape as a cfg-test twin. The cure is the same: one function both call.

## HOST-45 · KERNEL-49 (a), path compression in the one trie, HOST's half: no Host code moves; every reopen, backup, seal and export theorem re-verified (2026-10-18, HOST-12; with KERNEL-18, CODEC-11, PROTOCOL-12 in ONE kernel! landing)

**Decision.** Host passes no empty-digest argument and states nothing about a trie node's shape: it reads the tries through KERNEL's lemmas (`toList_insert_perm`, `mem_toList`, `Canon`, `insertAll_*`), whose names and statements the trie day keeps. So HOST's half is a re-verifying build, not an edit: on 66815ff + kernel18-joint2 (md5 2cf778dc) every Host module and proof builds unchanged (Host/Proofs/{Base,Backup,Deployed,Genesis,Seal,Serve,Index,Page,Cli} included), and host-sim, host-file-sim, hosting-sim (seeds 1–3), store-plants and rows are ALL PASS. The one Host line that moves is PROTOCOL-12's `dc` pass-through in `Host.Follow.answer` (HOST agreed).

**WASTE.** All 24 HOST rows measure EXACTLY their pinned values: they are byte ratios of records, bases and index entries, and the trie day keeps listings (hence base bytes) byte-identical; only roots change.

**Flag day.** Every root changes, so the World and carried tags move (CODEC-11) and every Store re-geneses: an old base refuses `shapeMismatch`, an old carried export refuses by stamp. No Host layout, Status or codec of HOST's moves.

**Critique.** "No code moved" is evidence that Host reads the trie only through KERNEL's lemma surface, which is the intended boundary; it is also evidence that no Host theorem says anything about a root's VALUE (they compare roots for equality, never compute one), so a root-function change cannot reach them. If a Host theorem ever states a root, the next trie change will.

**Meta-critique.** A day whose Host half is a build is still a day: the checks are the re-verification, and the WASTE equality is the measurement that listings stayed byte-identical, which the ruling asserted and nothing else in HOST's checks would have caught had it been false.

## HOST-46 · every World the deployed open returns is in the World codec's domain (`openWith_codecFits`), and a base never names a position it cannot spell (`positionUnfit`) (2026-10-18, HOST-12; cv 01a14e33-3911, HOST-43's two named gaps; proof lane)

**Decision.**
- **`openWith_codecFits`**, no premise: the World any deployed open returns satisfies `World.CodecFits` (cells, journal, refusals, rows, height, steps, chain, budget, origin, the window fits, refusals disjoint, height ≤ steps). `Kept` gains `refusalsOk`, `disjoint`, `steps`, `stepsLt`, each kept by every step (`kept_admit`/`kept_refuse`) and read off the decoded base (`kept_of_fits`); `codecFits_of_kept` assembles the structure (it replaces `carriedFits_of_kept`; `openWith_exportFile_ok` now goes through `carried_fits (openWith_codecFits h)`, its statement unchanged). The one new bound, the refusals LISTING, is DERIVED like the cells and rows: `world_size_listing` counts 33 bytes per refusals entry (`refusals_entry_size`), a refusal step adds at most 2 entries (`refuse_refusals_listing`; its tooth `refuse_refusals_listing_two`: the +2 is attained) and weighs 64 bytes of its record (`stepWeight`), admission only prunes (`admit_refusals_listing`), so `openWith_listing_lt` states cells + rows + refusals < 2^24.
- **`positionUnfit`** (REAL gap, unreachable at any real size): `Base.file` encoded the segment position as a u64 without checking it, so a position ≥ 2^64 would be written into a base no open reads back: the writer-writes-what-its-reader-refuses class HOST-41 made law. `Base.file` now refuses it, before encoding, as `SealFault.positionUnfit`, mapped to a NEW fatal Status `positionUnfit` (56) with its Ops sentence and re-emitted units (OPS's standing agreement; told OPS-4). A first cut mapped it to the existing `entryUnfit` status; that made `StoreFault.status_iff_name` (one code, one name) false, and weakening that law-7 check is a pause item, so the Status is new instead. Tooth: `file_positionUnfit`.
- `sealed_opens_deployed` loses BOTH premises: `hfit` by `openWith_codecFits h`, `hpos` by `Base.file_offset_lt` from the seal's own success. `Base.read_file` loses its `hoff` premise likewise (derived), so `genesisImage_opens` keeps its statement.

**Theorems.** New: `openWith_codecFits`, `codecFits_of_kept`, `admit_refusals_listing`, `refuse_refusals_listing`, `refuse_refusals_listing_two`, `refusals_entry_size`, `Base.file_offset_lt`, `file_positionUnfit`. Restated (stronger or fewer premises, none added): `world_size_listing`, `fold_listing`/`Record.foldlM_listing` (take `Kept`, which carries the canon facts they took), `openWith_listing_lt` (the three-way sum), `Base.read_file` (−`hoff`), `sealed_opens*` (−`hpos`), `sealed_opens_deployed` (−`hfit`, −`hpos`). Deleted: `carriedFits_of_kept` (subsumed).

**Law-6 read (read-only reader): LAND.** No collapse, no added premise (premises only removed, or `(Canon, RowsCanon)` widened to `Kept`, which carries them), `openWith_exportFile_ok` unchanged, the Status unique and fatal with its arm and units. WEAK, named: `refuse_refusals_listing_two` is conditional on a refusal succeeding from an empty refusals trie; its witness is the runtime one (host-sim `plant-lookup-recorded` records a refusal on a genesis World), not a closed theorem instance; `positionUnfit` has no runtime witness beyond `file_positionUnfit` (unreachable by design).

**Flag day.** None in bytes: no layout, codec or stamp moves; no Store re-geneses. One new Status (56) and its unit lines.

**Critique.** `positionUnfit` guards a position no Store will reach (2^64 bytes); it exists because the law is "the writer refuses over the reader's bound", not because the case is likely. The Status is a code an operator will never see; the alternative (a shared status) would have bent a law-7 theorem to save one line.

**Meta-critique.** HOST-43's deployed theorem shipped with two named gaps and a cv; closing them took one lane and found a fourth instance of the writer/reader bound class. Named gaps are cheap to close when the name is precise.


## HOST-47 · the record bound is DERIVED, not picked: `recordBytesMax` = 16,779,332 (was 32 MiB), and the torn-tail window halves with it (2026-10-19, HOST-13; HOST-41's critique, HOST-18's "nobody has questioned the 32 MiB")

**The defect.** `Cadence.deployed.recordBytesMax := 1 <<< 25` was a number with a comment ("64 turns of at most `weightMax` each, with room"), not a derivation. It was about twice the largest record the writer can produce. The bound is the torn-tail window (`Log.badTail`: up to `frameMax recordBytesMax` bytes of non-verifying tail are read as the one unsynced frame and TRUNCATED by the writer), `Tail.next`'s one read, and `tailMax`'s frame term. So every byte of slack was a byte of acknowledged-looking data the writer may cut without refusing, and a byte the open may read.

**Decision.**
- `Host/Bounds.lean` derives the bound from the bounds that make a record. A record is CODEC's `batch recordTurnsMax digestCodec`: a `u32` count, then at most `recordTurnsMax` (64) pairs. Each pair is a step plus the 32-byte roots digest (`digestBytes`). A step is CODEC's choice byte plus one of two things:
  - a Turn, whose bytes ARE its log weight (`turn_size_logWeight`), ≤ its weight ≤ `weightMax` once admitted (`admit_weight`);
  - a recorded refusal (`refusedBytesMax` = two digests, three u64s, a u32 length and at most `callMax` bytes, which `checkRefusedBounds` enforces).
  So `stepBytesMax = 1 + max weightMax refusedBytesMax` and `recordBytesDerived = 4 + 64·(stepBytesMax + 32)` = **16,779,332**, and `Cadence.deployed.recordBytesMax := recordBytesDerived`.
- Theorems (`Host.Proofs.Deployed`; `Record.runRooted_of_rooted` in `Host.Proofs.Base`):
  - `step_size_le`: every step `World.step` takes is ≤ `stepBytesMax` on the wire.
  - `runRooted_size_le`: every pair of a rooted run is ≤ `stepBytesMax + digestBytes`.
  - **`recorder_encode_size_le`**: a record the deployed recorder returns, of pairs a rooted run of `World.step` took, is ≤ `c.recordBytesMax`. So `Host.append`'s byte check never fires on admitted work at the deployed instance, and every frame the loop writes passes the reader's `frameAt` length gate at the same number. The writer and the reader share ONE bound, and a theorem ties it to the kernel's (HOST-41's law).
  - `recordBytesMax_deployed`: the value, pinned.
  - `openWith_listing_lt`'s numeric step re-pins `tailMax` to the new frame term. Its statement is unchanged and now holds with more room.
- What refuses, by name, at exactly the derived number (host-file-sim `boundPlants`, both sides, each with an at-the-bound control):
  - `plant-record-over-bound`: one never-judged refusal whose call makes the record bound+1 bytes is refused `recordTooLarge` by the real `append`, and seg.log is unchanged (44 → 44). The control at exactly the bound is appended as one frame.
  - `plant-frame-over-bound`: a frame that VERIFIES under the Store key, over a bound+1-byte record, is refused `corrupt` by the writer's open, and seg.log is unchanged. Past the length gate it is more than one frame's worth, so it is never a torn tail. The control at the bound passes the length gate and is refused `record` (undecodable).
  - Seen RED with the deployed cadence put back to 32 MiB: `2 FAILED` (the over-bound record was appended 44 → 16779413; the over-bound frame read as `record`, not `corrupt`). The plants size from `recordBytesDerived`, not from the cadence field, so they read red if the cadence stops being the derived number.

**Torn window.** `Log.frameMax c.recordBytesMax`: 33,554,468 → 16,779,368 bytes. This halves three things: the most a writer's open may truncate as "the one unsynced frame", `Tail.next`'s single read, and `tailMax`'s frame term. HOST-12's undecidable last-frame case (a corruption inside the last frame looks like a tear) is unchanged in kind and halved in reach.

**Alternatives.**
- (a) A per-batch byte budget in the loop (stage until the record would pass some smaller number). That changes batching, not the bound: the reader's gate must still admit the largest record the writer CAN write. That is the derived number unless the kernel bounds shrink.
- (b) Shrink `weightMax`. That is KERNEL's bound, and it prices Turns, not frames. Not Host's to move.
- (c) Keep 32 MiB as headroom for a future step kind. A future step kind moves `stepBytesMax` through this derivation, and `step_size_le` goes red at the new constructor. Headroom that is not derived is exactly the slack this removes.

**Flag day.** None in bytes: no layout, codec or stamp moves, and no Store re-geneses. A Store holding a frame between 16,779,332 and 32 MiB now refuses `corrupt` (or reads it as torn when it is the last frame). By `recorder_encode_size_le` no deployed writer could have written one. Consumers of `Cadence.deployed.recordBytesMax` move with it: Host's pager and check, PROTOCOL's rows writer (`Protocol/Rows/Writer.lean`, toy digests, records far smaller), and host-file-sim's `wide`.

**Law-6 read (read-only reader): LAND.** No `P → P`, no collapse. The bound in the theorem is the `c.recordBytesMax` that `append` and every reader (`openLog`, the pager, `host check`) use, and the derivation matches the wire byte for byte. If it undercounted, the proof would not close. Fixed: the theorem's premise was a successful `Record.runRooted`, which neither the writer nor the follower states (they state `Kernel.Rooted` / `World.RootedFold`), and only the runRooted → Rooted direction existed. `Record.runRooted_of_rooted` (the converse) now exists, and `recorder_encode_size_le` takes `World.RootedFold` directly. Left, named:
- the writer plant's record is a toy-codec refusal far over `callMax`. The byte gate does not depend on the codec, so it tests the number, not an admissible record;
- the bound is not shown tight (below).

**Critique.**
- `recorder_encode_size_le` takes the rooted run (`World.RootedFold`) as a premise. The writer's is `Machine.staged_rooted` and the follower's is `Protocol.Command.step_persists_admitted`. No single theorem runs from `Host.append`'s call site, inside IO, to the bound, so the byte check stays in `append` as a live refusal (the plant exercises it), not as dead code.
- The bound is proved SOUND (every record fits), not TIGHT. A Turn reaches its log weight ≈ `weightMax` only with no World growth, e.g. four 64 KiB slot overwrites. That is plausible, but no closed instance shows a 16 MiB record of admitted Turns. If one is far from reachable, the window is still looser than it needs to be. That is a measurement nobody has made, and it is named here.
- `digestBytes = 32` is a Host constant restating the deployed digest codec's width. `step_size_le` checks it against `digestCodec.size` (`fun _ => rfl`), so a different width breaks the proof, not silently the bound.

**Meta-critique.** HOST-18 wrote "nobody has questioned the 32 MiB" and HOST-41 wrote the exact formula, and it still took two successors to change one line. The number was cheap to fix and expensive to leave, because it was the torn window. The pattern to watch: a bound with a prose justification in its docstring and no theorem. `Cadence.deployed.worldBytesMax` (2^28, "~900 BAR stores") and `sealMinBytes` are still that kind. `worldBytesMax` at least has a refusal on both sides (`worldTooLarge`, the base frame's bound).

## HOST-48 · a page's IO error refuses THAT page `pageIo`; the writer serves on (2026-10-19, HOST-13; HOST-35's named edge)

**The defect.** `fillPages` ran the pager with no handler, so an IO error while building a deferred `log` or `read` page escaped `serve`. Examples: `base.world` unreadable when the `read` arm opens it, or a `readAt` on seg.log or index.log failing. `Cli.serving` caught it as `ioServing` (exit 6, restart). One failed read of one request stopped the writer for every member: its queued frames were answered `refused stopped`, its connections dropped, and a restart followed. HOST-35's table recorded this as the open edge `pager .read base per page → ioServing`.

**Decision.**
- `Loop.pageOrRefuse` builds each deferred page under `try`. On an IO error it answers that page `refused pageIo` (`pageIoReply`) and writes one `STATUS page refused=pageIo error="…"` line on stderr, with the error last. `fillPages` builds every page through it.
- That covers both of `serve`'s page paths: a batch that staged nothing, and a batch after its sync. It covers every pager, deployed (`Host.Deployed.pager`) and simulated alike, because the guard is in the loop, not in each pager.
- A page only reads. Nothing the loop holds or the disk has depends on it, so its failure is that request's failure.
- **Exit table unchanged.** `ioServing` (6, restart) stays for an IO error that does escape the loop: the pager's handles opened in `serving`, the port, the channel. Its sentence ("an IO error after the open: check the disk") still holds. No new Status: `pageIo` is a refusal name on the existing `refused` status.
- The client: a log page answered `refused` goes to PROTOCOL's `envelopeRefused`, which prints any name it does not special-case as `refused host pageIo` (CommandExit refused). At that phase nothing has been submitted, so no attempt settles on it. No Protocol change.
- `pageIoName_fresh` (`Host.Proofs.Names`, law 7): `pageIo` is none of the names a page reply otherwise carries. Those are a page fault's (`Page.Fault.name`, what the pager's `named f.name` sends), an envelope refusal's (`ReadRefusal.name`) and a frame refusal's (`FrameRefusal.name`). So the client can never read it as another refusal.

**Plant.** host-sim `plant-page-io`:
- What it runs: the real `serve` and `restarts` over the in-memory Store. The plant machine defers every `log` frame, as `Host.handle` does after the envelope check. Its pager's FIRST page throws an IO error.
- Checks:
  - (fires) the pager was asked twice and its first page threw;
  - the first log page is `refused pageIo`, and the second is served;
  - the loop ends `eof` with one reply per request (14 of 14);
  - every other reply, and the World, are identical to a control run whose pager never throws.
- Seen RED with the `try` removed: `FAIL plant-page-io: the writer serves on (the IO error escaped the loop (plant: base.world unreadable))`.

**Alternatives.**
- (a) A per-arm handler inside `Host.Deployed.pager`. It covers only the deployed pager. A sim pager, or a future third arm, would be unguarded, and the plant would test a twin.
- (b) A new Status (`pageFailed`, restart-class for the client), so clients would retry automatically. Rejected for now: the command fails by name and the member runs it again. Whether `refused host pageIo` should instead be a restart-class CommandExit is PROTOCOL's call, and it is asked (below). A Status would be a wire flag day for one transient case.
- (c) Retry the read in the loop. That hides a disk that is failing, and the loop has no business sleeping.

**Asked of PROTOCOL.** Should a log or read page `refused pageIo` map to a restart-class CommandExit (like `behind`) rather than `refused`? Until they answer, it is `refused host pageIo` (exit 1).

**Flag day.** None. No byte on disk, no wire layout and no exit code changes. The new stderr line is `STATUS page refused=pageIo error="…"`; OPS-5 is told for the RUNBOOK. HOST-35's table row `pager .read base per page` is annotated CLOSED by HOST-48.

**Critique.**
- The plant drives the loop's guard with a sim pager. That `Host.Deployed.pager`'s file reads are guarded is read off from `serve` (every pager goes through `fillPages`), not planted at file level. No store-plants row removes base.world mid-service and asks for a page. That would be OPS's row to add, and it needs a signed `read` envelope.
- `try … catch` catches every `IO.Error` the pager raises, including a programming error that throws (an index out of range in IO code would panic, not throw, so it is not caught). A pager bug that throws would read as `pageIo` forever, with the writer otherwise healthy. The stderr line names the error, so it is visible, not silent.
- A disk that keeps failing now yields a stream of `pageIo` refusals instead of a restart loop. Writes still sync, and a sync failure still stops the writer (`uncertain`), so a dead disk still stops it. Only a disk whose reads fail and whose writes succeed keeps the writer up, answering pages `pageIo`. That is the correct answer for that disk.

**Law-6 read (read-only reader): LAND.** `pageIoName_fresh` is a real case split over the three refusal types. Every payload a `log`/`read` reply can carry from the Host was enumerated (the pager's page faults, `handle`'s envelope refusals, `refuseQueued`'s `stopped`; `uncertainAll` carries another status). Both page paths of `serve` go through `fillPages`, and `Follow` has no pager. The client ends `refused (host pageIo)` before any submit (`envelopeRefused_ne_submit`), and the thin `read` path keeps its download. WEAK, named:
- the theorem compares NAMES. `ReadRefusal.expired`'s payload is its name plus a height, still not `pageIo`, and the client reads it by name, but no payload-level conjunct states that;
- which of `serve`'s two page paths the plant's throwing page lands in depends on the seeded split and is not pinned;
- host-sim's `run` was at the elaborator's depth; the seed-only plant calls moved into `laterPlants` (a `set_option maxRecDepth` was refused by the set_option budget, rightly).

**Meta-critique.** This took five lines of code and stood open for three decisions because it was filed as an "edge" in a table row. The table was the right place to find it and the wrong place to leave it. Every "an open edge" cell in decisions/host.md is a cv task or a fix, not a note.

## HOST-49 · HOST-21's adopt argument is a theorem: the reader refuses a record of no steps (`emptyRecord`), so a Store at step 0 holds no record past a base at step 0 (2026-10-19, HOST-13; HOST-21's meta-critique, HOST-11's edge)

**The defect.** PROTOCOL's adopt runs only when follow's World is at step 0. It refuses `notAtGenesis` otherwise; the measure was `w.height ≠ 0` at HOST-21 and is `w.steps ≠ 0` since the refusals day. Adopt then seals the adopted base with an EMPTY index (`Follow.loop`, `indexStart`). That is sound only if a Store at step 0 holds no record past its base. HOST-21 argued it from IO: "`Follow.loop` never appends `.steps []`, and every record holds at least one Turn". No theorem stated it, and the reader accepted a record of no steps: it opened as one record that moved nothing. The two facts could come apart silently, as HOST-21's meta-critique feared: a Store at step 0 holding a record, which adopt's measure cannot see.

**Decision.** Make "every record advances the step count" a property of the one reader and the one writer, then prove the adopt fact from it.
- Reader: `Record.stepTurns` refuses a record that decodes to no steps, as `Record.Fault.empty` ("emptyRecord"). Both opens, the tail and the follower's absorb go through it.
- Writer: `Record.encode` returns `none` for an empty batch (`encode_empty`; the writer never writes what its reader refuses, HOST-41's law). `Host.append` writes nothing for an empty batch and returns the resident unchanged. Both callers already skipped the call (serve's `isEmpty`, Follow's `.steps []` arm); now the append path itself guarantees it.
- Theorems:
  - `Record.step_nonempty` (`Host.Proofs.Base`): a record that opens is a NONEMPTY rooted run. `step_rooted` now goes through it.
  - `Record.step_empty` (`Host.Proofs.Page`, the tooth): the codec's own bytes of `[]` are refused `empty`.
  - `Host.Proofs.Deployed`:
    - `rooted_steps`: a rooted run moves `steps` by exactly its length, by KERNEL's `step_steps`;
    - `foldStep_steps`: every folded record strictly advances `steps`;
    - `foldlM_steps`;
    - `openWith_steps_records`: base steps + records ≤ the opened World's steps;
    - **`openWith_steps_zero`**: a Store the deployed open opens at step 0 has no record past its base, holds no index entry after it (`openWith_tail_entries`), and its base is at step 0. That is HOST-21's argument, as a theorem of the deployed open with no IO premise.

**Plants.** host-file-sim `emptyPlants`:
- `plant-empty-record`: a frame that VERIFIES under the Store key, holding the codec bytes of no steps, appended to a fresh Store, is refused `record 0 emptyRecord` by both the follower and the writer opens, and seg.log is unchanged.
- `-writer`: the real `append` of an empty batch writes nothing and leaves the resident unchanged.
- `-writer-control`: one step appends one frame.
- Seen RED with the three changes reverted: `2 FAILED`. The reader plant read `opened, opened`; the writer plant appended 44 → 84.

**Cross-layer.** `Hosting/Proofs/Allowance.lean` `stepTurns_fold` gains one `· cases h` arm for the new match arm. Its statement is unchanged. HOSTING-8 agreed.

**Flag day.** None in bytes. No layout, codec or stamp moves, and no Store re-geneses. What refuses now that did not: a Store holding a record of no steps, as `record N emptyRecord`. No deployed writer wrote one (both callers skipped empty batches), so none exists.

**Alternatives.**
- (a) A Host-side check at adopt ("the segment past the base is empty"). That checks one fact twice (HOST-21's law-1 argument) and still leaves the reader accepting a record that advances nothing.
- (b) A nonempty list in CODEC's batch codec. That is the same refusal at a lower layer, and CODEC's to make. The Host reader is where "a record" means "a step of the log". If CODEC wants it, this moves down and `Fault.empty` is deleted.
- (c) Name the gap and stop. The fix was a refusal, three proofs and a plant.

**Critique.**
- `openWith_steps_zero` says the base is at step 0. It does not say the base's index COUNT is 0. That follows from "every index entry a base counts is a record before it, and every record advances the steps", but no theorem ties a base's count to the steps before it. At step 0 the only bases are genesis's (count 0) and a seal of a step-0 World, whose count is its predecessor's plus `r.index.size` = 0 (this theorem), so it holds by induction over seals that no theorem states. Named, not closed.
- The theorem is about the moment of OPENING; adopt checks follow's live World later. Two links between them are theorems:
  - Follow's `.steps []` arm keeps the World: `step_persists_admitted` at `ts = []` gives `RootedFold w [] w'`, so `w' = w`.
  - Every append moves `steps` by its batch's length (`rooted_steps` over the run `append` is handed).

  So a live follower at step 0 has appended nothing since its open. The sequencing of those facts inside the IO loop is read off, not proved (law 6's usual IO edge).
- Adopt itself (PROTOCOL's `notAtGenesis` and Follow's seal of `w'` with an empty index) is read off too, not run against a Store at step 0 with a record. With the reader refusal no such Store opens.
- Two other decoders of a record do not go through `stepTurns`: `Page.walk` (a page) and `Check.turnsOf` (`host check`). An empty record would walk there as zero events. That is unreachable today: open refuses such a Store, and both run only on an opened one. (Corrected by HOST-54: both also read records BEFORE the base, which no open folds, so it was reachable; both now refuse it.) Still, it is a second reader whose acceptance differs. Named.
- These are theorems of the pure `openWith` over `segReader`, like every open theorem here. The IO `openAt` is the same generic code instantiated over files.

**Law-6 read (read-only reader): LAND.** No vacuity and no collapse: the open is the one Cli uses (`Cadence.deployed`, `Deployed.foldStep`), the premise is met at genesis, and `encode_eq_some`'s restatement only strengthens its `.mp` uses. Fixed: two docstrings (`encode_eq_some`, `Fault.empty`). Its WEAKs are in the critique above: the open-versus-live-World edge, the base-count gap (cv 01a14f2a-8c82), the second decoders, and pure versus IO.

**Meta-critique.** HOST-21 closed this "by argument rather than by code" and said so. The honest label sat for two days because it read as finished. It was one refusal away from a theorem the whole time.

## HOST-50 · the readers' named WEAKs of HOST-33..46, each closed or given its trigger (2026-10-19, HOST-13; ROOT's queue item 4)

A WEAK that only sits in a decision is a dropped obligation. Each one below is either closed here, or given the condition under which it would become a defect (its trigger) and the check that would see it.

**Closed.**
- *HOST-41: `foldStep_recorder_encode` took a `Record.runRooted` premise no caller states.* It now takes `World.RootedFold`, which the writer's `Machine.staged_rooted` and the follower's `step_persists_admitted` both state, via HOST-47's `Record.runRooted_of_rooted`. Same conclusion, a premise the callers have.
- *HOST-41: `recorder_encode_none` is `Record.encode_none` at the deployed recorder, an instance, not evidence.* DELETED. It had no users. The general theorem stands.
- *HOST-33: `Resident.install`'s "count + held = total" was measured (WASTE `loop resident-entries-per-record-past-base`), not proved.* `install_total` (`Host.Proofs.Loop`) proves it: installing a base whose count is the old count plus `n ≤ held` keeps count + held unchanged, and drops exactly the first `n` held entries. Its premise is now enforced by code. `Pending.indexCount` (the count `spawnSeal` hands the Task) was never read, a dead field the reader found. `settle` now refuses, as `io` (sealIo, a restart), any base whose returned count is not that one. So every `Sealed` the loop installs meets the premise. What remains read off: `r.index` only grows (by `append`'s push) between the spawn and the install. The WASTE row stays as the measurement. Plant: host-sim `plant-seal-count` uses a checkpoint whose base counts one entry more than it was handed. It is refused `sealFailed io` ("seal returned index count …"); its honest control seals 6 times and ends `eof`. With the assertion removed the lie was still caught, but LATER and under another name (a later seal's `sealFailed`, not the count). The plant reads red on the name.
- *HOST-35 critique, TRANSPORT's served_conns IO gap (a reply lost between staging and send).* The pager was the IO step that could throw between them for a reason other than the client's pipe. Since HOST-48 `fillPages` cannot throw out of a page. A failing `port.send` (stdout to nd-supervise gone) still escapes to `ioServing` and drops the rest of that batch's replies. That is not silent: the writer restarts, and every client recovers by lookup. `served_conns`/`uncertain_conns` cover both paths' connections. What remains is a process killed between sync and send, which the client recovers by lookup; `served_conns`' docstring already says so.

**Kept, with the trigger.**
- *HOST-33: `build_badIndex`'s tooth is at entry 0 only.* Every other position is planted (host-sim `plant-index-middle-flip`: every page that reads a flipped entry is refused `badIndex` at its position). Trigger: a change to `Page.locate`'s probe order. Then the plant's coverage is the check, and it reads every position by construction.
- *HOST-33: `mark_chain_width` discharges only the chain arm of `entryUnfit`.* The steps and offset arms (`< 2^64`) are unreachable below 2^64 steps or bytes, and if crossed they REFUSE by name (`entryUnfit`, fatal): a named stop, not a hole. Trigger: any loop World past 2^64 steps. `Kept.stepsLt` already bounds every OPENED World, and a loop-level `Kept` would close the arm. Not built: it buys a theorem about an unreachable number.
- *HOST-42: no sim plant drives `Host.handle`'s submit through `judge`.* The toy machine commits steps directly. The deployed arms are covered by `step_submit`/`machine_commits` (theorems) and by PROTOCOL's rows, which run the real `Host.handle` (the `refused` row among them). Trigger: a `Host.handle` change the rows do not exercise. The rows are the check.
- *HOST-43: that `sealNow` calls exactly `Base.seal` (through `memCheckpoint`/`fileCheckpoint`'s `write`) is read off, not proved.* The checkpoints are IO. The host-sim `sealPlants` and store-plants' three seal rows run it end to end. Trigger: a third checkpoint.
- *HOST-46 W1: `refuse_refusals_listing_two` (the +2 is attained) has no closed theorem instance.* Its witness is the runtime one (host-sim `plant-lookup-recorded` records a refusal on a genesis World). A closed instance at the deployed `X` would have to run the deployed hash under `decide`, a reduction bomb (minted 10-18). At the toy Ctx it would be an instance of a different `X`. Trigger: none needed. The theorem is an upper bound, the +2 is its tightness note, and nothing consumes the tightness.
- *HOST-46: `positionUnfit` has no runtime witness beyond `file_positionUnfit`.* It is unreachable by design (2^64 bytes). The theorem is the witness.
- *HOST-23 / decisions line ~640: the Tail does not follow a segment rotation.* No rotation exists: seg.log is append-only, and the writer's only truncation is the never-synced torn tail at open, which a tail never read past. Trigger: the first change that rewrites seg.log other than by append (rotation, compaction). That change must make `Tail` reopen at a base. A frame chained from another initial would not verify (HOST-18), so a tail would stop `corrupt` rather than read wrong. The silent case is a SHORTER rewritten segment, which a tail would see as "nothing new" forever.

**Law-6 read (read-only reader): LAND.** `install_total` is non-vacuous and its premises match `spawnSeal`'s arithmetic. The restated `foldStep_recorder_encode` is equivalent in strength, its premise now the callers'. Deleting the instance loses nothing. Fixed:
- the dead `Pending.indexCount`, now `settle`'s pair assertion (above);
- the served_conns claim, which ignored a failing `port.send` (corrected above);
- two older mentions of `recorder_encode_none`, now marked deleted.

**Flag day.** None in bytes. One theorem deleted (an instance), one premise restated to what callers state, one theorem added. `settle` gains a pair assertion. A checkpoint whose base counts other than it was handed now ends `sealFailed io` (restart) instead of installing.

**Critique.** Most of the "kept" items are kept because their only closure is an IO theorem this repo does not write. That is the same edge every open theorem here has, so naming it per item is repetitive. The repetition is the point: each says WHICH IO step and WHICH check sees it.

**Meta-critique.** The reader of each landing names WEAKs and the decision records them. Nothing collected them until a queue item made someone. Next time a reader's WEAK is neither fixed nor triggered in its own landing, it becomes a cv task that same day.

## HOST-51 · two of HOST-50's kept WEAKs get teeth: host-sim drives the deployed submit through `judge`, and `positionUnfit` has a runtime witness (2026-10-19, HOST-13; ROOT's ask on a2996f7)

**Decision.**
- **plant-judge-submit** (host-sim `judgePlant`; HOST-42's named WEAK "no sim plant drives `Host.handle`'s submit through `judge`").
  - Setup: the DEPLOYED `Host.machine` over Kernel.Sim's ctx (toy signatures, CODEC's call codec, the real `Receive.genesis` with one founder), run by the loop's own `Machine.admitBatch`. Every batch's staged steps are re-run by the follower's fold (`Record.runRooted` of `World.step`, what both reopens and `host follow` run).
  - An admissible call (`install`) commits ONE Turn through `judge`, and the fold reaches exactly the writer's World.
  - A call whose transaction id holds a recorded refusal answers `refused stale` and stages no Turn.
  - The tooth: a writer that ADMITS the recorded call (submitted on its World with the refusals forgotten, then put back: KERNEL-44's A→B→A defect, the same lie as PROTOCOL's rows `admitsRecorded`) stages it as a Turn ("fires": 1 staged). The follower's fold refuses that batch by name (`step`). So the Host layer's own sim now shows the honest arm and catches the lie, without going through PROTOCOL's rows.
- **plant-position-unfit** (host-file-sim `positionPlant`; HOST-46's "`positionUnfit` has no runtime witness").
  - The deployed file checkpoint (`fileCheckpoint`: `Base.seal` → base.tmp → sync → rename) is asked to seal at segment position 2^64. It refuses `positionUnfit` (offset 2^64) before writing: base.world and index.log are byte-identical afterwards, and the Store still opens. Its control, the same seal at the real position, installs.
  - Seen RED with `Base.file`'s check removed: the base INSTALLED, its u64 position wrapped, and the next open refused `foreignSegment`. So the refusal is the only thing between a 2^64 position and a Store that does not reopen.
  - An open cannot be shown such a base, because the layout has no spelling for it. That is exactly why the writer refuses first (HOST-41's law). The witness is therefore on the write side, through the real checkpoint and files.

**The other five of HOST-50's kept WEAKs** stay named with their triggers there:
- `build_badIndex` covers entry 0 only;
- `mark_chain_width`'s steps/offset arms;
- the sealNow/Base.seal bridge;
- `refuse_refusals_listing_two` has no closed instance;
- the Tail does not follow a rotation.

**Law-6 read (read-only reader): LAND.** Both plants run the deployed code they claim. The recorded call takes the recorded-refusal path: `submit` answers `refusedFinal` before the signature check, `World.refuse` declines to record twice, and `verdictReply` names the recorded code `stale`. The liar's Turn is refused at `World.admit`'s `checkJournal` (`refusedFinal`). Its WEAKs are fixed: the plant now asserts the admissible reply's status `ok`, the recorded reply's name `stale`, and the fold's refusal as `step 0 refusedFinal` (not any error). Left: plant-position-unfit has no standing "fires" beyond its specific match and the red run above.

No theorem changed. Both are plants over deployed code. The vacuity question is whether each plant's verdict can go red: plant-position-unfit was SEEN red with the check removed; plant-judge-submit's "fires" check asserts that the mutation (a staged Turn for a recorded call) happened before the fold verdict is read.

**Flag day.** None.

**Critique.**
- plant-judge-submit records the refusal with `World.refuse` directly (as `plant-lookup-recorded` does), not by an earlier submit that `judge` recorded. The recording arm of `judge` (`.recorded`) is exercised by the kernel's own sim and by PROTOCOL's rows, not by this plant.
- The liar is a function in the plant, not a mutation of `Host.handle`. It shows the fold catches the lie. It does not show that `Host.handle` can never tell it, which is `machine_commits`' job as a theorem.

**Meta-critique.** Both teeth took a few dozen lines once someone asked. HOST-50 kept them as "kept, with a trigger" because each had a covering check elsewhere (PROTOCOL's rows; a theorem). "Covered elsewhere" was true and was still the wrong reason: the layer's own sim is where a later Host change is first judged.

## HOST-53 · open's one index check also requires that the base's last entry began before the base's World, so a base at step 0 counts no entry (2026-10-19, HOST-14; HOST-49's named gap, cv 01a14f2a-8c82)

**The gap.** HOST-49's `openWith_steps_zero` proved that a Store the deployed open opens at step 0 has no record past its base and that its base is at step 0. It did not prove that the base counts no `index.log` entry. Adopt seals the adopted base with an EMPTY index (`indexStart`). That drops nothing only if the old base counted nothing. HOST-49 argued this by an induction over seals that no theorem states. Open checked the base's last entry for its position and its tag. It never checked the entry against the base it belongs to. A base at step 0 naming an entry with a verifying tag (for example, a writer bug that hands a seal the wrong `IndexAt`) opened.

**Decision.** `indexNamed` (the one check open makes over the one entry it reads, HOST-33) takes the base World's step count `before` (`(mark b.world).1`). At count > 0 it refuses `indexCorrupt` unless the entry's `steps < before`. The entry's `steps` is the World's step count BEFORE its record (`Open.indexed`), and every record moves the step count (HOST-49, `foldStep_steps`). So an honest base's last entry is always strictly before it, and nothing is strictly before step 0.
- Theorems:
  - `Host.Deployed.openWith_steps_zero` gains `o.sealed.index.count = 0`. The whole adopt fact is now a theorem of the deployed open.
  - `indexNamed_none` states the new conjunct.
  - `indexNamed_notBefore` is the tooth: an entry that reads back with the base's `indexLast` but whose step count is ≥ `before` is refused, so at `before = 0` every entry is refused.
  - `indexNamed_mono`: a later base passes wherever an earlier one did.
  - `openWith_verifies_named` states the step bound.
  - `Backup.indexed_foldlM_steps`: every entry an indexed fold holds is below the World it reached, and the World's step count never falls.
- Completeness (no honest Store is refused):
  - `seal_facts` / `sealed_opens` / `sealed_opens_clean` / `sealed_unindexed_refused` gain the premise `hmono` (a fold step strictly moves the mark's step count), discharged at the deployed instance by `foldStep_steps` in `sealed_opens_deployed`. The new base's last entry is either the old base's (strictly below the old World, which is ≤ the new) or the newest tail record's (strictly below the World after it).
  - `entries_named` / `entriesSeq_named` / `entriesSeq_read` take the step count of the base being opened, with the premise that every entry is below it. A base is sealed after the records its entries index.

**Plant.** host-sim `plant-index-ahead`:
- The newest base is re-sealed (real `Base.file` under the Store keys), naming a last entry re-tagged with a step count at the base's own and at one past it. Every tag verifies, and both are refused `indexCorrupt`.
- Controls through the same forging path: the honest step count and the base's step count less one both open.
- Seeds 1, 2 and 3: ALL PASS. RED with the condition made vacuous (`e.steps < before ∨ True`): `FAIL plant-index-ahead`, `1 FAILED`.

**Flag day.** None in bytes. No layout, codec, stamp or exit code moves. What refuses now that did not: a base whose last counted entry does not begin before its World, as `indexCorrupt` (exit 46, fatal, the same remedy: restore from this Store's own backup). No deployed writer writes one; the completeness theorems above say so of the pure seal.

**Alternatives.**
- (a) A separate check beside `indexNamed` over the same bytes. Rejected: two checks of one entry, and about a dozen `unfold openWith` proofs would gain a case. The one check grew a conjunct instead.
- (b) A new fault name (`indexAhead`). Rejected for now: the remedy and exit class are `indexCorrupt`'s, and a new name moves the exit table and OPS's units text for no new operator action. If an operator ever needs to tell the two apart, the trigger is a support case that restored the wrong file.
- (c) Prove the induction over seals instead of checking. There is no "reachable Store" predicate to state it over, and the theorem would cover only Stores this binary wrote. The check covers any bytes.
- (d) Also check the entry's offset against the base's offset. That is the same class: an entry naming a record at or past its base. Not taken here. Trigger: a page or `host check` finding an entry past its base. `indexClean` already ties every entry's offset to its record's frame.

**Critique.**
- The completeness theorems are about the pure seal of a pure open (`Base.seal` after `openWith` over bytes). That the loop's seals are exactly these is read off Host/Loop.lean (spawnSeal hands `sealed.index`; settle stores the returned one), as HOST-33 said of `entriesSeq_read`.
- The bound checks the LAST entry only. Entries before it are checked by a page as it reads them and by `host check` (`indexClean`: offsets match the records, steps never fall). Since steps never fall and the last is below the base, every counted entry is below the base once `host check` has passed. The open alone does not see a middle entry.
- `entriesSeq_read`'s `before` is free: the theorem holds for any step count past every entry, and does not itself tie the check to a sealed World. That tie is `sealed_opens`, which uses the open's own `(mark o.opened.world).1` (second-agent read).
- The live loop pushes an entry as `⟨(mark r.world).1, …⟩` just before the World moves, and writes nothing for an empty batch, so the loop's seals meet `hmono`'s shape. This is read off Host/Loop.lean and relies on the Machine advancing `steps` for a non-empty batch (KERNEL's `step_steps`), not proved over the IO loop.
- Checked while reading adopt (Follow's `.adopt`): it seals with `indexStart` and `#[]`, and `Base.seal` refuses `indexMoved` unless `index.log` is empty. At step 0 that holds now. The base counts nothing (this decision), and orphan entries come only from a seal whose base never landed, which leaves records past the old base, so the open would not be at step 0. A hand-placed foreign `index.log` would fail adopt with `sealFailed indexMoved`, named and not silent.
- `hmono` is strict increase, true at the deployed instance because every record holds at least one step (HOST-49's `emptyRecord`). Without HOST-49 this decision would refuse a Store holding an empty record as its last before a base. That is the right refusal, but it shows how this rests on HOST-49.

**Law-6 read (second agent, read-only): LAND-WITH-FIXES.**
- No vacuity: `openWith_steps_zero`'s new conjunct comes from the entry bound and `b.world.steps = 0`; the tooth's premises are satisfiable; the `#[]` start of `indexed_foldlM_steps` is met.
- `hmono` is met by `foldStep_steps` through `recorder_mark` (rfl).
- No writer seals a base past its last entry: the loop, adopt (`indexStart`), genesis, join/import (through genesis); every other `Base.file` call is a sim plant.
- The plant changes only `steps`, and its controls take the same path.
- Fixed: three docstrings (Proofs/Deployed's "`entriesSeq_read` has no premise", and Index's header ×2).

**Meta-critique.** HOST-49 named this gap as "follows by an induction no theorem states". The cheaper move was a one-conjunct check that turns the induction into a local fact, and the check also covers a Store this binary did not write. The pattern: when a theorem needs a history argument, look for a check at the read that makes it local.

## HOST-54 · the page walker and `host check` refuse a record of no steps, as the open does (2026-10-19, HOST-14; HOST-49's named second readers)

**The defect.** HOST-49 made the open's reader (`Record.stepTurns`) refuse a record that decodes to no steps (`empty`). Two other decoders of a record did not:
- `Page.walk` (a `log` page);
- `Check.turnsOf` (`host check`'s use count).

HOST-49 called that unreachable, because open refuses such a Store and both run only on an opened one. That was wrong. Both read records BEFORE the base, which no open folds. So an empty record in a frame that verifies under the Store key, sitting before the base, passed the open. A page then walked it as zero events, and `check` read it as zero Turns. Two readers accepted what the third refused.

**Decision.** Each gains the `.ok []` arm `stepTurns` has:
- `walk` refuses `corrupt off`;
- `turnsOf` refuses `.error i` (`corrupt use-record i`).

They keep the faults their callers already name. They do not share a decoder function with `stepTurns`. Changing `stepTurns`' body would move HOSTING's `stepTurns_fold` proof for no new refusal. If a fourth record decoder appears, that is the trigger to factor out one `Record.steps?`.

**Theorems.**
- `Check.turnsOf_empty`: the codec's own bytes of `[]` are refused at their position. Its statement is false without the arm.
- `Page.walk_events_le` gains the one case.

**Plant.** host-file-sim `plant-empty-record-page`. The real `Page.walk` is run over a frame that verifies under the Store key, holding the record of no steps, and refuses it `corrupt 44`. Its control is the same frame holding one step, which walks. Seeds 1–3: ALL PASS. RED with the walk arm removed: it read "walked".

**Flag day.** None in bytes. What refuses now: a page or `host check` over a Store holding an empty record before its base. No writer writes one: `encode` refuses it and `append` skips it (HOST-49).

**Critique.**
- `turnsOf`'s tooth is a theorem, not a run over a real Store. `host check` over a hand-built Store holding an empty record before its base is not planted. The run plant covers the pager.
- The two arms copy one line of `stepTurns`. That is three places stating "a record has at least one step", agreeing today.

**Law-6 read (second agent, read-only): LAND-WITH-FIXES.** `turnsOf_empty` is not vacuous: its input is concrete, and without the arm it is `.ok []`. The plant goes through the real `walk`, and its control takes the same path. No other record decoder exists in Host, Hosting, Ops, Protocol, Ledger, launcher or client, and nothing in Rust decodes a Store record. Fixed: HOST-49's "unreachable" sentence now points here, and Check.lean's header names the empty arm.

**Meta-critique.** HOST-49's "unreachable" rested on "every reader runs only on an opened Store". It forgot that an open validates the tail, not the history. A reader of history needs its own refusals, whatever the open checked.

## HOST-52 · `Host.Sock`: THE client end of a Unix stream socket, 156 lines of C beside the Store's, every call bounded, every failure named (2026-10-19, HOSTING-10 for HOSTING-27's resident; HOST-13 agreed with conditions, HOST-14 read the diff; ROOT ruling 10-19)

**The gap.** HOSTING-27's resident is a Lean executable (ROOT, 10-19: a Rust resident would be three twins). It must talk to two Unix sockets: its member socket (`nd --stdio`) and its broker socket (keybroker). Lean 4.30's Std has TCP and UDP but no AF_UNIX. `Host.File`'s `pread` fails ESPIPE on a socket. A Rust stdio relay was refused: it would be a second process, plus a rule about what may exec inside the grain.

**Decision.**
- `Host/c/sock.c` gives three externs, declared in `Host/Sock.lean`:
  - `nd_unix_connect PATH MS`: a non-blocking AF_UNIX connect (atomic SOCK_CLOEXEC|SOCK_NONBLOCK on Linux; fcntl on Darwin).
  - `nd_conn_write_all`: send with MSG_NOSIGNAL until every byte is out.
  - `nd_conn_read MAX`: recv, 1..MAX bytes, or empty exactly at end of stream.
- An opaque handle carries the fd and its timeout. The finalizer is the only close of a live handle. `Conn.stream` makes it an `IO.FS.Stream`, so `Host.readExact` reads it unchanged. A `timeout` is an IO exception that escapes `readExact`, not a `none`, so a caller catches it and names it. The resident does, in `Resident.Sockets`.
- HOST-13's conditions, each met:
  1. **Bounded.** Every call runs under the connection's timeout as a CLOCK_MONOTONIC deadline, with `poll` before each syscall. Connect is non-blocking: an AF_UNIX connect on Linux never answers EINPROGRESS, and a full backlog answers EAGAIN at once. The EINPROGRESS arm (poll POLLOUT, then SO_ERROR) is for platforms that answer it. A zero timeout is refused `timeoutZero` at connect; without that, every later call would answer `timeout` at once.
  2. **EINTR** (and EAGAIN after a poll) is retried on what is left of the deadline, never reported.
  3. **`max` = 0 is refused** `readMaxZero`, so an empty read means only EOF. Above 16 MiB is refused `readMaxPastBound` before any allocation. The largest legal frame is 262,148 bytes.
  4. **The path is checked before any copy**: `pathEmpty`, `pathNul` (a NUL that `lean_string_cstr` would cut), and `pathTooLong` at sizeof(sun_path) = 108 bytes. 107 bytes connects.
  5. **SIGPIPE.** MSG_NOSIGNAL on every send (SO_NOSIGPIPE on Darwin). HOST-14 measured that Lean's runtime already ignores SIGPIPE (SigIgn 0x1000) before any of our code runs. So the mid-write plant pins the composite (EPIPE named, the process lives) and is NOT a tooth for the flag. The flag stays so this file does not rest on a runtime internal.
  6. **One tcb row** (`extern:Host.Sock`), one native-allow row, and named contract tests. `cargo:launcher:sock` drives the Lean `host-sock-probe` against a peer it holds:
     - EOF is an empty read;
     - timeout is bounded;
     - EINTR: signal 33, glibc's SIGSETXID, which every Lean exe catches, is sent to every thread every 200 ms during a 1500 ms read. It ends exactly `timeout`, in [1500, 2500) ms;
     - readMaxZero and readMaxPastBound;
     - pathEmpty, pathNul, pathTooLong at 108 bytes with nothing created, and 107 connecting;
     - timeoutZero;
     - a peer that shuts its reading side mid-write gives exactly `send: Broken pipe (errno 32)`, and the probe exits 0;
     - an absent path;
     - a full backlog (a backlog-1 listener that never accepts) gives `connect: … (errno 11)` at once, after at least one queued connect;
     - an echo control.
  - **Mutations, run once by hand** (logs/hosting10-sock-m1.c, -m2.c). Reporting EINTR turns the row red: `r16 err poll: Interrupted system call (errno 4)`. Restarting the deadline per retry turns it red too: `the deadline did not hold across retries: 2.739148561s`.
- Every other failure is the call and its errno, written one way. `file.c`'s `io_errno` became the library's shared `nd_io_errno` (a rename, no behaviour change). sock.c restates its prototype; a third C file means a header.
- This is THE socket client. Host's own serving goes through nd-supervise's pipes today. If Host ever serves or connects to a socket itself, it extends `sock.c` (an accept beside the connect, under the same deadline, names and tcb row), never a second socket C file.

**Flag day.** None. A new extern, a new exe and a new row (plus a rustix dev-dependency edge in Cargo.lock; rustix is already in the build through the sandbox, with the same pin and feature). No Store, wire or theorem change.

**Critique.**
- The error is a string, so a Lean caller that wants to branch on it compares text. The resident only logs these and decides by which step failed, so nothing branches on the text today. A typed error (an `Except` of a named inductive across the FFI) is the right next shape if anything ever does.
- The deadline is per call, not per exchange. A peer that drips one byte per (timeout − ε) holds a `readExact` for up to n × timeout. Every frame the resident reads is bounded, so the bound is finite and stated rather than tight.
- 156 lines against the ruling's "~70". The difference is the EINPROGRESS arm, the path, size and timeout checks HOST-14 asked for, and comments. It is not a second mechanism.
- The external class is registered lazily without a lock, as in file.c. Two racing first connects would register two identical classes, which is harmless.

**Meta-critique.** Both of my "argued from code" claims rested on a claim about the runtime that I never measured: "these exes install no signal handler". The runtime catches 7, 11 and 33, and ignores SIGPIPE. That turned my SIGPIPE plant into a check of Lean's runtime and made EINTR plantable after all. HOST-14 measured it from /proc in minutes. Before calling a test a tooth for a C property, read the process's signal state and run the mutation once. Both are done here.

**Co-signed.** HOST-14, on the final 789-line diff (built in wt/host at c18e028; cargo:launcher:sock green; m1 re-run red by HOST-14), on fixes F1–F6 (all taken; see above), after reading the final diff.

- **Read.** The C is correct where it counts:
  - socket/fcntl/setsockopt/connect each close the fd on failure, and none closes twice;
  - poll's -1 keeps its errno to the caller;
  - the deadline is one CLOCK_MONOTONIC sum per call (uint32 ms in int64, no overflow), and a retry re-polls on the remainder;
  - send continues partial writes;
  - recv's 0 is EOF only because max = 0 is refused;
  - the finalizer is the only close of a live handle.
- **Measured** (hbox, the built probe, /proc and strace; logs/host14-sigign.py, logs/host14-eintr.py):
  - (a) The probe IGNORES SIGPIPE before any of our code runs: SigIgn 0x1000, set by Lean's runtime, under a parent that restored SIG_DFL. MSG_NOSIGNAL stays, so the C does not rest on a runtime internal. But the mid-write plant cannot redden when it is removed, and every text that says "the process lives, so no SIGPIPE killed it" must say that instead.
  - (b) The exe CATCHES signals 7 (SIGBUS), 11 (SIGSEGV) and 33 (SigCgt 0x100000440); 33 is glibc's SIGSETXID. Its handler returns at once for a sender that is not the process itself. kill(tid, 33) aimed at the reading thread interrupted poll three times (ERESTART_RESTARTBLOCK). sock.c re-polled on 1496, 1196, then 895 ms, and the read ended `timeout` at 2.01 s against 2000. So "EINTR cannot be made to happen in these executables" is FALSE; it is plantable.
- **Critique (HOST-14's).**
  - The Lean-side contract has one trap the C cannot see: `timeout` is an IO exception that escapes Host.readExact. It is not `none`, so a caller that reads frames from a Conn must catch it and name it (Wire.Stop.readFailed exists).
  - The per-call deadline does not bound a frame, as HOSTING-10's critique says. Today's largest socket frame is 262,148 bytes (Protocol.Bounds.frameBytesMax + 4), against ND_READ_MAX = 16 MiB, so the read bound never bites a legal frame.
  - The external class is registered lazily without a lock: two racing first connects register two identical classes. That is harmless, and it is the same as file.c.
  - nd_io_errno's prototype is restated in sock.c, not shared through a header. A signature drift would link silently; with two files this is acceptable, but a third C file means a header.
- **Meta-critique.**
  - Both of HOSTING-10's "argued from code" claims rested on a claim about the runtime that nobody measured: "these exes install no signal handler". The runtime does install handlers, and it also ignores SIGPIPE, which turned the SIGPIPE plant into a check of Lean's runtime rather than of sock.c.
  - The lesson for every extern row: before a test is called a tooth for a C property, read the process's signal state (/proc/PID/status) and run the mutation once.
- **Host's serve.** This is the client end of a Unix stream socket, and it is THE one: every Lean process in the repo that connects to a Unix socket uses Host.Sock. Host's own serving goes through nd-supervise's pipes today. If Host ever serves or connects to a socket itself, it extends Host/c/sock.c (an accept beside the connect, under the same deadline, the same names and the same tcb row). It does not add a second socket C file, so this is not a second implementation and must not become one.
