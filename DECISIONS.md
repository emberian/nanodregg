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

## CLIENT-1 · should a Rust client exist at all? (BUILD-CLIENT, 2026-10-16)
**Decision.** Yes, and only as custody + transport: a seed holder, a frozen-attempt store and a frame
mover over two Unix sockets (`client/`, ceiling 2,000 lines). Everything a command MEANS — parsing the
argv, deriving the request, the plan, the challenge, assembling the call, rendering any reply — is done
by `host follow` (Lean), which drives `nd` through five step tags (CLIENT-2).
**Alternatives.** (a) A Lean client: `nd` is a Lean executable over the same codecs, custody through an
FFI signer. (b) minidregg's shape: a Rust client that parses commands, encodes requests and decodes
outcomes (113,757 lines for `mini`; dossier §1). (c) No separate client: the member talks to `host
follow` directly and follow holds the seed.
**Why.** For (a): Lean 4.34's standard library has no Unix-domain sockets (READ: `Std/Internal/UV/` holds
TCP, UDP, DNS, Signal, Timer, System, Loop only) — the reason HOST-2 needs a supervisor — and no
constant-time signature code, so a Lean client still needs native code for both halves of its job; what
it would remove is ~600 lines of byte moving. Its startup is a Lean runtime init plus the codec closure's
module initializers per command (minidregg W5: 0.38 G instructions for a codec child). For (c): the seed
would sit in the heap of the one process that parses untrusted log bytes; keeping custody in a separate,
small, memory-safe process with no parser is the isolation that makes "follow decides, custody signs"
meaningful. Against (b): every Rust struct mirroring a Lean shape is a twin, and in minidregg the Rust
client became the place features went because it was the easiest place to write them.
**Critique (of keeping Rust).** Two languages remain. The step encoding (§2 of proposals/client.md) is a
small codec the Rust side must read: a twin unless CODEC generates the reader too. Custody signs what
follow hands it, so a compromised follow can get anything signed — the isolation protects the key's
bytes, not its use. The supervisor (HOST-2) is a second process in every request path.
**Critique (of the Lean alternative, so the comparison is fair).** If Lean gains Unix sockets and a
verified signer (e.g. a Lean-callable libsodium or an extracted HACL* via FFI), (a) becomes one language
end to end and the step protocol disappears into function calls — strictly fewer moving parts. The
socket gap is a library gap, not a design reason.
**Meta-critique.** I am the Rust owner arguing Rust should exist. I also arrived from a dossier of Rust
bloat and may be over-correcting into a client too thin to be convenient (every rendering a round trip).
The ceiling is the honesty check: if `client/src` passes 2,000 lines, re-argue (a).

## CLIENT-2 · follow drives, the client executes steps
**Decision.** `nd` sends its raw argv to follow (`command`) and loops: `done | sign | host | submit`,
each with an opaque continuation it echoes back (`resume`). The order challenge → prepare → assemble →
submit → lookup is follow's; Rust holds no op sequence except submit/lookup inside an attempt.
**Alternatives.** (a) The charter's literal reading: Rust performs the five ops itself in a fixed order.
(b) Follow connects to the Host itself and Rust only signs.
**Why.** (a) puts the choreography — protocol knowledge — in Rust and needs a Rust request encoder per
command; (b) needs follow to open a socket, which Lean cannot (CLIENT-1). Stateless continuations let a
command survive a follow restart and keep follow's per-connection state at zero.
**Critique.** A round trip per step costs latency on the BAR path (two socket hops per signature);
continuations must be authenticated or bounded by follow, or a client can replay a stale one (harmless
— follow re-derives — but it is follow's theorem to state). If one command needs many signatures, the
step loop is the hot path.
**Meta-critique.** The pull of "Rust knows nothing" may be making the protocol chattier than a fixed,
generated op sequence would be.

## CLIENT-3 · attempts are custody, frozen on disk, state by file presence
**Decision.** As `client/src/attempt.rs`: `call` written once; `sent.<n>` before every send; one
settlement file. Lost reply ⇒ `Uncertain` ⇒ lookup only; `absent` ⇒ resend the same bytes ≤ `sendsMax`.
**Alternatives.** An append-only attempt log with records; SQLite; keeping attempts in follow (Lean).
**Why.** File presence needs no format and so no parser; O_EXCL makes "one call per attempt" and "one
settlement" a property of the file system, not of code. Attempts belong to custody because the key
holder is the party that must never sign two variants of one intent and must never resend different bytes.
**Critique.** File-presence state is still a format (names, ordering of markers) — an implicit one.
Per-attempt directories grow without bound unless settled ones are pruned (nobody prunes yet). On APFS
`sync_all` is `F_FULLFSYNC` (correct, slow: one per marker); the marker fsync is on the latency path.
**Meta-critique.** Format-aversion after minidregg's twin census may be driving me to a cleverness (state
in directory listings) that a reader finds less obvious than a tagged record.

## CLIENT-4 · the workspace is a directory with no config file; remote is OpenSSH stream forwarding
**Decision.** `seed`, `host.sock`, `follow.sock`, `attempts/`. A remote Host is reached by
`ssh -N -o StreamLocalBindUnlink=yes -L ws/host.sock:/srv/nd/host.sock friend@box`; `nd` cannot tell.
No Rust ssh client, no socket proxy, no `ssh:DEST` addresses, no host-image pin.
**Alternatives.** minidregg's `ssh:DEST` relayed by a forced-command `mini socket-proxy`; a JSON workspace.
**Why.** OpenSSH already authenticates both ends and refuses unknown/planted host keys and unauthorised
keys by name (the sshe2e row's checks). The host-image pin protected `mini` exec-ing a Host locally; with
sockets only, the member's trust anchor is its own follow, not the Host binary.
**Critique.** sshd cannot restrict which socket path a key may forward to (no `permitopen` for stream
local), so the per-friend restriction becomes filesystem permission on the Host socket (group-readable
by members) plus `Match User` forwarding policy; a forced-command relay restricts more precisely. A
long-lived `ssh -N` is one more thing the member must run.
**Meta-critique.** Minimalism bias; I have not run the sshe2e row's refusals against this shape.

## CLIENT-5 · Ed25519 custody until KERNEL names the scheme
**Decision.** Custody signs with Ed25519 from the 32-byte seed; no hybrid yet.
**Critique.** minidregg signed hybrid Ed25519 + ML-DSA-65; retrofitting changes `sign`'s return type and
the seed derivation (one seed, two keys, domain-separated KDF). **Meta-critique.** Doing the easy half first.

## CLIENT-6 · no binary until the generated table exists
**Decision.** `client/` is a library (frames, custody, attempts) until CODEC emits `generated.rs`; the
binaries `nd` and `nd-supervise` land with it. Tests use test-chosen bounds, never protocol values.
**Critique.** Delays the first end-to-end. If CODEC slips, a JSON-at-build-time reader of the Lean table
(`build.rs`) is the fallback, not hand-copied constants. **Meta-critique.** Law-following can be a way to
postpone the integration risk; the round trip is the real test and it is blocked on two other layers.

## CLIENT-7 · the CLIENT row attacked: sandbox/ is a different trust domain, and grain-runtime dies
**Decision (proposed to ROOT).** Keep `sandbox/` with this owner but as a separate crate from `client/`.
A hosted Hermes (or any resident agent) is a MEMBER: it runs `nd` inside one bwrap shape with its own
seed; `sandbox/` is only the launcher (bwrap argv from a Lean-decided profile, fds, cgroup limits, uid
mapping) and the SPK broker's physical verbs. minidregg's grain-runtime (55,896 lines: an agent
controller with its own control socket, credentials and provider logic) has no counterpart.
**Critique.** The agent needs model-provider egress and BYOK credentials; something must hold those
keys and meter calls, and "a member with a seed" does not cover provider custody. That is a second
custody (provider keys) and may deserve its own small component. **Meta-critique.** I want the biggest
deletion to be mine to announce.

## K0 · KERNEL attacks its own row (BUILD-KERNEL, 2026-10-16)

**Decision.** Keep KERNEL, but re-cut three edges of the row:
1. *Store model.* KERNEL owns the MEANING of the Store and nothing physical: a log is a `List Turn` whose
   `fold` from genesis is the World; a checkpoint is a `World` at a height; the root is a function of the
   World. HOST owns bytes on disk, the append, fsync and the crash protocol; CODEC owns the checkpoint and
   Turn encodings. HOST may not define its own replay: reopen = decode checkpoint + `Kernel.fold` suffix.
2. *Sim.* KERNEL owns the seeded generator (turns + the verdict each one must get) and the follower oracle
   (`fold`). The side-by-side check against the REAL Host loop belongs to HOST's loop plugging into
   `Kernel/Sim.lean`'s driver; until that loop exists the Sim's "Host side" is incremental `admit` with
   restarts from a prefix fold (a stand-in named as one, deleted when HOST lands).
3. *The missing layer.* The table has no home for **receiving**: signed call → `Turn` (signature via an
   injected verifier, capability/authority, Objective Bend law evaluation, the price shown to consent).
   In minidregg that is ~400 receiver modules — the bulk of the system — and `World.admit` decides none of
   it (by design: it is mechanical). Proposal: a seventh row `Law/` (OB core + ONE `receive : World →
   Call → Except Refusal (Turn D)`), consumed by HOST and by the consent provider (same code, second
   process). KERNEL will not grow it; ROOT must assign it.

**Alternatives.** (a) KERNEL also owns receiving (one owner for "what is admitted"): rejected — `admit`
must stay small enough to be read whole, and authority/law is a different kind of decision. (b) HOST owns
receiving: rejected — HOST is the loop and IO; putting OB evaluation there recreates `Host/Main.lean`.

**Critique.** Splitting receive from admit recreates minidregg's K1 twin (receiver builds a DataIntent,
engine executes it) if `receive` produces anything but a `Turn`. The guard: `receive`'s codomain is
exactly `Kernel.Turn`, and the Host's commit is `World.admit (receive w call)` — no intermediate type.
**Meta-critique.** I am the kernel owner arguing that the hard, bulky layer belongs to someone else; the
bias is to keep my row clean. Counter-check: if ROOT folds `Law/` into KERNEL, the def/proof split and
module-size law still hold, so the cost is ownership load, not shape.

## K1 · The laws, attacked (BUILD-KERNEL, 2026-10-16)

- **Law 4 "an assertion for every invariant a theorem states".** In Lean a proved invariant of a total
  definition cannot fail at run time except through the compiler or an `@[extern]`; asserting it re-checks
  the compiler (the cost of `native_decide` without the name). Restate: *an assertion for every PREMISE a
  theorem assumes that the types do not carry* — decoded bytes, disk reads, extern/FFI results, the
  hash's collision-freedom where it is observable (e.g. a reopened root equals the sealed one). Critique:
  minidregg had 0 runtime assertions and silent divergence between live and reopened state (WASTE/HP-5);
  my restatement still catches that, because reopen reads disk (a premise). Meta: I prefer theorems to
  assertions because I write theorems; the restatement keeps every assertion that can actually fire.
- **Law 4/5 "O(touched), never O(store)" vs "checkpoint = World".** A checkpoint that re-encodes the
  World is O(store) every N turns, and the journal and spent set grow forever. Either the checkpoint is
  incremental (node-level persistence of the authenticated map, HOST/CODEC), or the law needs "amortized
  O(touched)". I hold the law and push the burden to HOST: checkpoint = the World's map nodes written
  since the last seal. Kernel contribution: bounded windows (`validUntil - notBefore ≤ windowMax`) so the
  journal can later be pruned to txIds whose window is still open (a theorem, not a v0 feature).
- **Law 1 "one digest type" vs a kernel generic over `D`.** The kernel is generic over the digest and
  hash (`Env`) so proofs state collision as an explicit disjunct and the Sim can run toy parameters. That
  is NOT a second shape: there is one `admit`; only parameters vary (memory: toy parameters in the real
  pipeline, never toy code beside it). Critique: a generic parameter is where a deployed/toy divergence
  hides; the deployed `Env` must be ONE definition (CODEC's `Digest256` + cSHAKE) and the Sim must also
  run under it once it exists. Meta: genericity is my habit for proof convenience; I keep it only because
  the collision disjunct is the honest statement.
- **Law 6 `#assert_axioms`** is a minidregg command, not core Lean. CLOSURE must provide it (or a gate
  over `#print axioms`); until then KERNEL theorems are axiom-checked by CLOSURE's census.
- **Law 8 def/proof split.** Kept, with the one unavoidable exception: proofs that are part of a
  definition's TYPE (subtype fields, termination) live with the definition.

## K0a · ROOT ruled: receivers are KERNEL's (`Kernel/Receive/`) (BUILD-KERNEL, 2026-10-16)
Accepted. Shape: one `receive` per operation KIND whose codomain is exactly `Except Refusal (Turn D)`;
the Host commits `World.admit (receive w req)`. No intermediate intent type exists anywhere (that is
minidregg's K1 twin: receiver → DataIntent → execute). `install`/`invoke` signatures first, for LANG.

## K2 · The World and the Turn (BUILD-KERNEL, 2026-10-16)
**Decision.** (a) A cell is `{kind, discipline : rom | appendOnly | ram, slots : ascending (Nat × ByteArray)}`,
bounded, untyped bytes; `=` on cells is extensional. (b) Cell ids are derived: the i-th cell a turn
creates is `hash(tag ‖ txId ‖ le32 i)`; no allocator, no `duplicateCreate`. (c) Retirement leaves a
tombstone in the ONE cells map (no separate retired set); a tombstoned id is `idTaken` forever. (d) The
Turn carries `pins : List (cell, digest)` — the intent's observation, `pinOf none` for asserted absence —
and the pin check is the one staleness refusal (no `absent` list, no guard legs: TURN-LOG a0/guards,
done right from the start). (e) `charge` is one number, the turn's storage weight, refused unless
exactly `Turn.weight`; the World's `allowance` falls by it. (f) The turn carries its `event` (the ingress
bytes) — the log alone is the audit trail; no archive beside it. (g) Legs write only cells live in the
pre-state; created cells carry their whole initial content; every check reads only the pre-state,
so `commit` is total. (h) Check order: bounds → journal → shape → window → pins → nullifiers → charge
→ ids → retires → legs; an exact retry is `replayed h` before anything state-dependent. (i) No parent
namespace: a room's parent is a ROM slot of the child, decided by `receive`. (j) Generic over `D` with
`[Ord D]`; maps are `Std.TreeMap` (O(log n) per touched id).
**Alternatives.** Typed cell layouts (minidregg's `Registry`/`Layout`); allocator ids; Turn = intent
+ post bytes (minidregg IntentRecord); a 10-lane meter; an ingress archive (TURN-LOG step 2); a separate
`retired` and `parent` system space.
**Why.** Every alternative is a second representation of something already present: typed layouts
duplicate the codec (the deployed path encoded to bytes anyway); post bytes duplicate what legs compute;
the archive duplicates the log; a retired set duplicates the cells map; a parent space duplicates a slot.
Charge = weight makes "what the log grows by" and "what the turn pays" one number (log growth is the
permanent cost). Derived ids remove coordination and a refusal.
**Critique.** (a) Untyped slots move all value typing to `receive` + CODEC: a receiver bug can write a
mistyped value the kernel happily stores — the kernel's theorems say nothing about meaning. (b) Derived
ids make cells unaddressable until the txId is known; a client must compute ids (it can: txId is the
signed call's digest). (e) One lane cannot charge compute (OB fuel): compute must be paid as an ordinary
debit of a resource cell decided by `receive`, which the kernel cannot check — and there is no `credit`
yet, so a World's storage budget only falls: refills need a design (open, K-OPEN-1). (f) Logging the event
stores signatures forever (log size); minidregg measured the turn log 3.48× the record log before digest
guards — here legs carry only ops, so measure at the first Sim/BAR run. (j) A `Std.TreeMap` is not
canonical (shape depends on history): two Worlds equal in content are not `=`. The determinism theorem
that matters is `admit` respecting extensional equality (a reopened World decides like the live one):
K-NEXT, not yet proved.
**Meta-critique.** Much of this is "TURN-LOG's end state, minus the transition": I have read minidregg's
plan and may be adopting its destination uncritically (e.g. pins as the guard mechanism came from there).
Check: pins were chosen because they are the only guard that needs no pre-image in the turn, which holds
independent of minidregg. The "no archive" call reverses TURN-LOG's step 2; its reason there (keep the
log small) is weaker when legs carry no post bytes — but it is a size bet to be measured, not assumed.

## CLIENT-8 · the isolation invariant: no process that parses log bytes can read the seed (BUILD-CLIENT, 2026-10-16, ROOT ruling on CLIENT-1)
**Invariant.** The seed file is readable only by `nd` (custody). `host follow` and `host serve` —
the processes that decode Store or wire bytes — cannot open it: not by permission of the code, by the
operating system. Same-uid 0600 is NOT enough (follow runs as the member's uid).
**Mechanism.** The supervisor never execs its child with the member's ambient file view: on Linux the
child runs in the one sandbox shape (`sandbox/`: bwrap with only the Store segments bound read-only and
its stdio; no home, no workspace); on macOS, where bwrap does not exist, under a `sandbox-exec` profile
denying `file-read*` of the workspace directory. The supervisor refuses to start a child it cannot
confine (no "unconfined fallback").
**Plant.** `nd-supervise --plant-read-seed`: the supervisor launches, in place of the Lean child, a
probe that tries to open the workspace seed; the row is green only if the probe reports EACCES/ENOENT,
red by name (`isolation: child read the seed`) if it read a byte. Runs on Linux and macOS.
**Alternatives.** (a) A separate custody uid (`nd-custody` user, seed owned by it, nd setuid or a
custody daemon): strongest, heaviest on a laptop. (b) Seed in the OS keychain (macOS Keychain, Linux
secret service): the parser process of the same uid can still ask the keychain unless the keychain ACL
names the `nd` binary. (c) Trust same-uid 0600: rejected by the ruling.
**Critique.** Confinement is per-platform code (two mechanisms) and `sandbox-exec` is deprecated by Apple;
a confinement bug is silent unless the plant runs on every platform every landing. It also does not
protect against a compromised `nd` itself, which by design holds the seed.
**Meta-critique.** I picked the mechanism that reuses the sandbox crate I own; (a) may be the honest
answer and I priced it as "heavy" without measuring.

## KEY-CUSTODY · who holds a hosted resident's model-provider keys? (BUILD-CLIENT, 2026-10-16) — OPEN, for Ember
A hosted Hermes is a member: its own seed, running `nd` inside the one bwrap shape (CLIENT-7). It also
needs provider credentials (API keys, BYOK) to call a model, and something must meter those calls. Not
decided here; ROOT takes it to Ember.
**Option A — the operator holds them.** A provider broker outside the sandbox holds the keys; the
resident gets a socket that forwards requests and meters them (minidregg's `mini-keys` relay shape).
*Critique:* the operator can spend or read a BYOK key the member brought; the broker is a second
custody service with its own authorization logic, which minidregg decided in Rust under a Rust-only
domain (`mini/member-provider-action/v1`) — that decision would have to move to Lean. *Meta:* familiar
because minidregg did it.
**Option B — the resident holds them in its sandbox.** The key is a file in the resident's own
workspace, like its seed; the sandbox allows egress to the provider only. *Critique:* the resident's
process also parses model output (untrusted text) and tool results — exactly the "parser reads a
secret" shape CLIENT-8 forbids for the seed; metering becomes the resident's word unless the provider's
own usage is the meter. *Meta:* symmetry with seeds is attractive, not argued.
**Option C — split.** The member's key stays with the member (BYOK held by the friend's own `nd`
custody, which signs a short-lived provider grant), the operator holds only operator-paid keys, and a
broker enforces grants that a Lean receiver issued (the authorization is a Lean decision, the broker
only checks a signature and moves bytes). *Critique:* the most moving parts; providers do not accept
signed grants, so the broker must still hold a real key at the moment of the call. *Meta:* it is the
"everyone gets what they want" option, which is how minidregg grew.
