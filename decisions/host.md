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

## HOST-33 · HOST-14 at size, as counts: the seal bound holds once stated correctly; open reads O(history) of index.log, so open must stop reading it (2026-10-18, HOST-8; ROOT's framing of HOST-14's re-check: counts, no timing) — PROPOSED, needs ROOT's ruling (it moves a check)
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
