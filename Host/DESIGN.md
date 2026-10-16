# Host — design (BUILD-HOST, 2026-10-16)

The Host is the IO shell around one pure function. Everything it decides is the Kernel's
`World.admit` and PROTOCOL's operation table; what the Host owns is *when* bytes move, *which*
bytes reach the disk, and *what the process may say* after a failure. Decisions with both
critiques are in `DECISIONS.md` (HOST-1 … HOST-9); this file is the shape.

Measured from minidregg (main 2c27b08b, `~/dev/redregg/work/DELETE-HOST-20261016.md`): one
9,163-line `Host/Main.lean`, five routing tables and two framing loops for one opcode space, 126
CLI verbs (63 of them one-shot twins of session ops, each a cold open), three verified openings
of the same Store held per session (`Opened`, `Light`, `Walked`) re-validated after every
request, a store-helper process per call, six executables. None of it survives.

## 1. Processes

```
 clients ──unix socket──▶ supervisor (Rust, CLIENT layer) ──stdin: Request frames──▶ host serve STORE
                                     ◀──stdout: Reply frames────────────────────────
 member's machine:  host follow STORE   (the consent provider = the follower; same binary, same fold)
```

- **One Lean process per Store, one writer.** `host serve STORE` takes an exclusive `flock` on
  `STORE/LOCK`; a second writer refuses by name (`storeLocked`).
- **The supervisor owns the socket**, accepts connections, and writes each request as one frame
  `(conn : UInt32, op : UInt8, payload)` onto the Host's stdin; it routes each reply frame back by
  `conn`. It decides nothing: it does not parse payloads, and a reply it cannot route is dropped
  (the client's recovery is `lookup`). Lean's standard library has no Unix-domain sockets; this
  is the cheapest correct place for one.
- **`host follow STORE` is the follower and the consent provider.** It opens the Store read-only
  (no lock), folds the segments with the *same* `World.admit`, and answers the read and plan
  operations of the table against its own World. It never appends. Consent = "this plan is what
  my own fold of the log says", computed by the same handler the writer runs. There is no second
  implementation to drift.
- Executables: `host` (verbs `serve`, `follow`, `genesis`, `sim`). Nothing else. Operator
  one-shots are client operations over the socket.

## 2. The loop

```
serve(fuel):                                  -- structural recursion on fuel; no partial def
  batch  ← take ≥1 frame (blocking), then every frame already queued, up to batchMax   (§3)
  for r in batch (arrival order):
     dispatch table r world  →  .read reply | .refused name | .write turn
     .write turn: World.admit world turn → ok world' (stage turn, reply pending) | error reject
  if staged ≠ ∅:  append one batch frame; fsync                                           (§4)
     ok  → reply every request of the batch
     err → reply `uncertain` to every staged request; exit 3 (supervisor restarts; open recovers)
  seal? (cadence by suffix bytes) → hand the World value to a Task                        (§5)
  serve(fuel-1)
```

`admitBatch : World → Array Request → World × Array Pending` is pure; `take`, `append` and
`reply` are the only IO. Reads in a batch see the World *after* the admitted writes before them
(arrival order), but their replies leave only after the fsync, so no reply ever reports a state
that a crash could take back.

**Batch boundaries do not change the state** (theorem target `HostProofs.admitBatches_flatten`:
folding requests in any split equals folding them in one pass, given `admit` is a function of
`(World, Turn)`). The simulation drives the same `admitBatch` with seeded splits.

## 3. Batching: group commit with no timer

The reader Task frames stdin into a bounded channel. The loop blocks for the first frame, then
drains whatever is already queued (≤ `batchMax`, ≤ `batchBytesMax`). While one fsync runs,
requests queue; they become the next batch. At low load a batch is one request and its latency
is one fsync; at high load batches grow to the bound. No `batchWaitMs`: a timer would add latency
at low load and buys nothing at high load (HP-DESIGN §0.2 proposed one; HOST-3 argues it away).

## 4. The Store on disk (flat segments; no SQLite)

```
STORE/LOCK                  flock'd by the writer
STORE/ckpt-<h>.world        World at height h, one MAC; written tmp → fsync → rename → fsync dir
STORE/seg-<h>.log           batch frames for heights > h, append-only
```

Batch frame: `u32 bodyLen ‖ body ‖ tag32`, `body = u64 firstHeight ‖ u16 count ‖ (u32 len ‖ turnBytes)*
‖ chain32`; `tag = MAC(key, prevTag ‖ body)` (the chain of tags binds order; the World's own chain
binds Turns). Ingress bytes travel inside the turn record (KERNEL decides what a Turn carries).

- **Append protocol:** encode the frame in memory; assert `decode (encode b) = b` on those bytes
  (the pair of `Log.decode_encode`); `writeAll`; `fsync`. A failed write or fsync makes every
  reply of the batch `uncertain` and the process exits: after a failed fsync the kernel may have
  dropped dirty pages, so retrying it is a lie (PostgreSQL fsyncgate, 2018).
- **Open/recover:** the newest checkpoint whose MAC verifies (absent/torn checkpoints are skipped,
  never trusted), then every segment from it, frame by frame. The first frame that is incomplete
  or fails its tag ends the log. Because a batch is fsynced before the next is written, only the
  LAST frame can be torn: the bad bytes are truncated as a torn tail only if they are ≤ `frameMax`
  AND no frame verifies anywhere after them (each frame is preceded on disk by the tag it chains
  from, so a forward scan can check candidates without the bad frame). A verifying frame after
  bad bytes means acknowledged data follows: refuse by name (`storeCorrupt`), never truncate.
  The one case no format decides: a corruption inside the last frame reads as torn; the client
  holding its receipt and the follower that folded it both see the height go back.
- **Physical IO** is one C file, `Host/native/file.c` (~120 lines: `open`, `write_all`, `fsync`,
  `fsync_dir`, `read_at`, `size`, `truncate`, `flock`, `rename`): Lean's `IO.FS.Handle` is a
  `FILE*` with no `fsync`, no positioned read and no truncate-to-length.

## 5. Checkpoint = World

Seal when the bytes appended since the last seal reach `max(sealMinBytes, worldBytes / 4)` (a
function of the log, so every process computes the same heights). Sealing starts the next segment
at the sealed height *immediately*; a Task encodes and writes the checkpoint in the background.
If the process dies before the checkpoint lands, open uses the previous checkpoint and both
segments: correctness never waits on the Task. Segments are never deleted (the follower may
start from genesis); retention is an operator decision outside the loop.

## 6. Dispatch

One table, PROTOCOL's. The Host's only dispatch is `table.find? op`; every entry declares its
bound and its kind (`read | write | pure`). A frame past its op's bound, an unknown op, or a
payload the op's decoder refuses is answered with a named refusal and the loop continues. No
special-cased streamed ops: an op whose reply is large has a large declared bound.

## 7. Crash plants (each must go red by name)

| plant | where | expected |
|---|---|---|
| `plant-torn-tail K` | truncate the last segment K bytes into its last frame | open truncates, reports `tornTail K`, height = previous batch |
| `plant-flip-byte N` | flip one byte (body or length header) inside a non-last frame | open refuses `storeCorrupt` |
| `plant-flip-last-frame` | flip a byte of the last frame | reads as torn: the stated undecidable case |
| `plant-fsync-fail` | the shim returns EIO on the next fsync | every reply of that batch is `uncertain`; exit 3; reopen height ∈ {before, after} |
| `plant-kill-at P` | `kill -9` at each of {after write, after fsync, after reply} | reopen root = follower fold root |

## 8. What the Host never does

Re-execute its own history after open; spawn a process per request; hold a second opening of the
Store; parse a payload outside the op's own decoder; answer before the fsync; retry an fsync.
