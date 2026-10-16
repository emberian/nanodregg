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
  Ours: `Host/native/file.c` uses `fcntl(F_FULLFSYNC)` on Darwin, `fdatasync` elsewhere, and fsyncs the
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
**Status.** open.

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
