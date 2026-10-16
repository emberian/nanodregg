# DECISIONS

Every design decision: decision · alternatives · why · CRITIQUE (what would make it wrong) · META-CRITIQUE (what bias produced it). Append-only, one heading per decision, owner and date in the heading.

## HOST-1 · the Host row itself (BUILD-HOST, 2026-10-16)
**Decision.** Keep HOST as a layer, but as the IO shell only: when bytes move, which bytes reach the
disk, what may be said after a failure. It owns no decision function: request → Turn is a receiver
(KERNEL), op → receiver is the table (PROTOCOL). The consent provider and the follower are not
layers or executables: they are `host follow`, the same fold.
**Alternatives.** (a) Charter as written (Host also "the durable Store", Kernel also "the Store model")
— two owners of one thing. (b) Fold Host into Kernel (the loop is a fold of `admit`). (c) Split Store
into its own layer.
**Why.** (b) puts IO and an FFI file into the layer whose job is to be proved; (c) makes a layer of
~400 lines. Cut instead along *pure vs IO*: KERNEL owns what a log MEANS (`fold`), HOST owns the
bytes and their crash behaviour (`Log.recover`), and the theorem joining them is HOST's
(`recover` returns a prefix of what was appended, which `fold` then means).
**Critique.** The charter has a hole this exposes: no row owns the receivers — the decision mass
that was ~400 modules in minidregg. If nobody owns it, it lands in `Host` by gravity (it did in
minidregg: `Host/Main.lean`'s 152-op inline closure). ROOT must give it a row.
**Meta-critique.** "IO shell only" is the shape I wish minidregg's Host had had; I am reacting to
`Main.lean`, and may be under-scoping work that is genuinely the Host's (admission ordering under
contention, per-connection fairness).

## HOST-2 · one Lean process per Store, a byte-moving supervisor owns the socket
**Decision.** `host serve STORE` reads request frames `(conn, op, payload)` on stdin and writes reply
frames on stdout; the Rust supervisor (CLIENT layer) accepts Unix-socket connections and muxes them.
**Alternatives.** (a) Lean owns the socket through `Std.Internal.UV` (TCP only, internal API, no Unix
sockets). (b) A C socket shim in Host (accept/epoll in C). (c) minidregg's shape: one stdio session
per client.
**Why.** (c) serialises clients and so kills batching; (a) is not available; (b) is an event loop in C
— the most bug-prone code in the system, in the layer that should be smallest. The supervisor moves
bytes only (law 2): it parses no payload, so it decides nothing.
**Critique.** A second process in the request path: its crash drops every in-flight reply (clients
recover by `lookup`, so this is latency, not safety), and its accept order becomes the arrival order
(not a semantic decision — nothing in `admit` may depend on order beyond "one at a time" — but a
fairness one). If Lean ships Unix sockets, (a) deletes a process.
**Meta-critique.** Familiarity: minidregg's `mini serve` already supervises a Host child. And "Rust moves
bytes" makes any Rust look acceptable if it is labelled transport.

## HOST-3 · group commit with no timer
**Decision.** Block for one frame, then drain what is already queued (≤ `batchMax`, ≤ `batchBytesMax`);
one append, one fsync per batch. No `batchWaitMs`.
**Alternatives.** HP-DESIGN §0.2's drain-until-count-or-timeout; fixed client-side batches (TigerBeetle).
**Why.** A timer adds its wait to every request at low load and changes nothing at high load, where the
queue already fills during the previous fsync. Without the timer the loop has no clock input at all,
so the simulation needs no virtual time.
**Critique.** Under a load of exactly one request per fsync-time, batches stay at size 1 and throughput
is fsync-bound (~1/fsync); a short wait would double it. If THE BAR's load sits there, measure and add
the timer back as a bound, not a default.
**Meta-critique.** I may be choosing this because it is simpler to prove (no time), and calling simplicity
a performance argument.

## HOST-4 · the Store is flat append-only segments, not SQLite
**Decision.** `seg-<h>.log` (batch frames, append-only, fsync per batch), `ckpt-<h>.world` (World, one
MAC, tmp → fsync → rename → fsync dir), `LOCK` (flock). Physical IO is one C file (`Host/native/file.c`).
**Alternatives.** (a) SQLite (minidregg's choice, through a helper process). (b) SQLite linked in-process.
(c) A log-structured KV (LMDB/RocksDB).
**Why.** The Host is the only writer and all indexes live in the World (KERNEL: indexes are not state),
so a database's concurrency, transactions and query engine buy nothing; what is left is append +
fsync + read, which is ~120 lines of POSIX. Open is O(one cadence) (checkpoint + its segment); a torn
tail is bounded by one batch because every batch is fsynced before the next is written, so recovery can
tell torn (≤ `frameBytesMax` at the end of the last segment) from corrupt (anything else) and refuse the
second by name.
**Critique of the flat log.** We now own crash consistency that SQLite has tested for twenty years: short
writes, fsync semantics per filesystem (ext4 vs ZFS vs APFS: on macOS `fsync` does not flush the drive
cache, `F_FULLFSYNC` does), directory fsync after rename, sector tearing inside one frame. A bug here is
silent data loss. Mitigation is the plant set (DESIGN §7) and `F_FULLFSYNC` on Darwin — but plants test
our model of the disk, not the disk.
**Critique of SQLite.** Its WAL mode fsyncs per transaction anyway; it would hold the same bytes twice
(our framed Turns as blobs plus its pages); in-process it needs a C binding of ~40 functions vs our ~9;
through a helper (minidregg) it cost an exec per call (W13). It is also a second notion of "committed"
(its transaction) beside ours (the batch tag).
**Meta-critique.** Two biases: minidregg's helper-process pain makes SQLite look guilty when the helper was
the problem (choice (b) has no helper); and "120 lines of POSIX" is an estimate — fsync correctness is
famously larger than it looks.

## HOST-5 · log framing before CODEC exists
**Decision.** `Host/Log` writes its frame with two private little-endian helpers (u32, u64) until
`Codec` commits its primitives; then they are deleted and the frame is a `Codec`.
**Why.** The append/recover protocol and its torn-tail theorem do not depend on the codec family; waiting
blocks the crash plants.
**Critique.** This is a twin by definition (law 1) with a promised expiry — exactly the shape the charter
forbids. If CODEC lands its primitives first, there is no excuse; check before every Host commit.
**Meta-critique.** "Temporary" is how every minidregg twin began.

## HOST-6 · the infinite loop is fuel-bounded, not `partial`
**Decision.** `serve (fuel : Nat)` recurses structurally; at fuel 0 the process exits 0 and the
supervisor restarts it. Fuel = `batchesPerProcessMax` (proposed 2^20).
**Alternatives.** One `partial def` (HP-DESIGN §5 kept exactly one); `repeat`/`while` (themselves
`partial` underneath via `Loop.forIn`).
**Why.** Law 4, and it makes restart a routine path rather than a rare one: the reopen code runs every
2^20 batches, so a reopen bug cannot hide for months.
**Critique.** A large fuel is a fake bound; a small one costs a reopen (O(cadence)) every few minutes at
peak. The real value is the second argument, which is an argument for *rejuvenation*, not for the law.
**Meta-critique.** I am obeying a law and then finding a reason the obedience is good; see LAW-4 below.

## HOST-7 · the consent provider is `host follow`
**Decision.** No consent executable, no consent frames as a separate protocol. A member runs
`host follow STORE`: read-only open, the same `World.admit` fold, and the table's `read` and plan ops
answered from its own World. Custody signs a plan only if `host follow` returns the same bytes the Host
proposed.
**Alternatives.** minidregg's 12-frame provider (`ClientConsentCore`, two executables, thin consent,
anchors) — a second verifier with its own frames.
**Why.** "Re-derive before signing" is exactly "compute the plan yourself"; computing it with the same
handler on your own fold of the same log is the only version that cannot drift.
**Critique.** The member needs read access to the Store's segments (ssh/sftp or a read-only stream from
the supervisor) and the CPU to fold them; minidregg's thin consent existed for members without the Store.
Thin consent becomes "trust the Host" by another name, and should be deleted rather than ported — but that
is a product decision about members who cannot follow.
**Meta-critique.** Elegance pull: "one code path" is so attractive that I may be undercounting the member
who is on a phone.

## LAW-4 (argued by BUILD-HOST) · "no `partial def` in deployed code" is right; "no unbounded recursion" needs a carve-out it does not state
**Claim.** Every server has one loop that is meant to run forever. Law 4 forbids writing it honestly.
The fuel workaround (HOST-6) satisfies the letter. Proposal: keep the law; name the one sanctioned
shape — "a fuel-bounded top-level loop whose fuel exhaustion is a clean exit the supervisor restarts" —
so nobody reaches for `repeat` (which is `partial` in disguise) and believes the law holds.
**Critique.** A carve-out invites more. **Meta-critique.** I want the law to bless my HOST-6.
