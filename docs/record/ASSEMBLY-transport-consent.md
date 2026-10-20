> record copy of redregg/work/nanodregg-scout/ASSEMBLY-transport-consent.md, 2026-10-16; the lane logs stay in redregg

# ASSEMBLY — transport-consent (Opus evaluator, 2026-10-16)

Scouts: T1 (many Stores per host), T2 (remote mux), C1 (thin consent from a sealed base), C2 (per-cell blinding).
Tags: **[read]** = I read it at the cited place; **[ran]** = I ran it this session and saw the output;
**[assumed]** = my inference, not checked. Every decision carries a CRITIQUE and a META-CRITIQUE (law 10).

---

## 0. Ground truth, and the finding that changes three of the four scouts

**The primary checkout `~/dev/nanodregg` is not main.** HEAD and `refs/heads/main` are both f11caa2, but its
working tree and index are stale and dirty (`git status`: `D Codec/Deployed.lean`, `D Codec/Hash.lean`,
`D Codec/Kernel.lean` …; `Host/` has no `Base.lean`, `Open.lean`, `Keys.lean`, `Serve.lean`, `Store.lean`;
`decisions/host.md` ends at HOST-13; `CHARTER.md` lacks the 10-16 amendments to laws 2, 4, 5) **[read]**.
The charter itself says it is "nobody's editing surface". I took ground truth from `git archive main`
(f11caa2) into my scratchpad and checked every quoted signature there. The Host, Kernel/Receive and
Protocol/Envelope files are unchanged between 1e43a54 and f11caa2 (`git diff --stat` empty) **[ran]**.

Which scouts built against what:

| scout | built against | effect |
|---|---|---|
| T1 | `cd ~/dev/nanodregg && lake env lean` (stale `.lake`, 19:26 oleans) | "HOST-16 does not exist" is **false** at main (decisions/host.md:308, Host/Keys.lean) **[read]**. Its segment design assumes open reads from offset 0 with `initial = empty`; at main open reads from the **base's offset** (`Host/Open.lean openWith`, `Host/Store.lean openAt`) **[read]**. Line numbers drift (Unsigned is Call.lean:65 at main, not :62; `recover` Log.lean:143, `badTail` :115). |
| T2 | Rust dep `path = ~/dev/nanodregg/client` (stale tree) and a Lean child under the stale `.lake` | `mux.rs`, `frame.rs`, `table.rs` are byte-identical to main, so the Rust findings hold **[ran: diff]**. "idleMsMax does not exist" is half-false: it exists at `Protocol/Table.lean:225` (PROTOCOL-12) but is **not** in `Emit/Rust.lean:31-36 bounds`, so Rust never sees it **[read]**. T2 designs for CLIENT-4 (`ssh -L`); CLIENT-12 chose option **B** (forced-command `nd-attach`) and PROTOCOL answered B **[read: decisions/client.md CLIENT-12]**. |
| C1 | `git archive` of 1e43a54, private oleans | Correct ground truth. One drift: `absorbPage` now returns `World × List Turn` (424163c), so `Thin.follow` no longer type-checks at main **[read: Protocol/Command/Machine.lean:223]**. |
| C2 | `cd ~/dev/nanodregg && lake env lean` (stale) | "No deployed cSHAKE Env exists" is **false**: `Codec/Deployed.lean:23 def env : Env Digest` and `Codec/Hash.lean` (KMAC256, `Hash.mac`) are on main **[read]**. |

**Lesson for every brief from here:** a lane that runs `lake env` in `~/dev/nanodregg` builds a mirror of a
tree that no longer exists. The builder works only in its own worktree at main.

---

## 1. Per-scout verdicts

### T1 — many Stores per host, cross-store refusal: KEEP the findings, REWORK both mechanisms

**What I re-checked.**
- The request hole is real at main: `structure Unsigned` (Call.lean:65-73) has no Store field; `Envelope`
  (Protocol/Envelope.lean:19-25) has none; `World` (Kernel/World.lean:89-99) has no identity field after
  height 0. `World.genesis` puts `E.hash domGenesis name` into `chain` only (World.lean:145-147).
  `founderId X name i = H(domFounder, name ‖ i)` (Follow.lean:39) does not depend on the founder keys, so two
  Stores with the same name have the same founder member ids, and `worldId X` is the same constant in every
  Store (Call.lean:251) **[read]**. A call is therefore admitted by any Store with the same name, the same
  founder keys and matching pins. T1's plant shows exactly that **[ran: T1 Plants.lean ALL PASS, against the
  stale tree; the receive path it exercises is unchanged at main]**.
- The segment hole is real at main, and it is **128× bigger than T1 said**. I wrote a plant against main's
  `openWith` (Host files identical to main), using C1's 1e43a54 oleans, at
  `/Users/ember/dev/redregg/work/nanodregg-scout/plant-foreign-segment.lean` (copied from my scratchpad; run with C1's oleans: `cd /Users/ember/dev/nanodregg-scout/C1 && source env.sh && LEAN_PATH=$PWD/olean:$($L --print-prefix)/lib/lean $L --run /Users/ember/dev/redregg/work/nanodregg-scout/plant-foreign-segment.lean`) **[ran]**:
  ```
  A's segment under B's genesis base (offset 0): OPENS records=0 torn=1750 (writer truncates to 0 of 1750)
  A's segment under B's base at offset 5:         OPENS records=0 torn=1535 (writer truncates to 215 of 1750)
  ```
  The deployed `recordBytesMax` is 32 MiB (`Host/Bounds.lean deployed`), so `frameMax` = 33,554,468 bytes:
  **any foreign tail up to 32 MiB reads as a torn tail, and the writer truncates it** **[read + ran]**. T1's
  "≤ 256 KiB" was the stale tree's number.

**Keep.**
1. The finding that nothing binds a request to a Store, and its baseline plant (clone admitted, cross-store
   call refused under the wrong name `unknownKey`). Restate the plant against main.
2. The shape of the theorems `foreign_never_admitted` / `admit_names_this_store`: they speak about the
   function the loop actually runs, so they are not vacuous. Restate them over `Receive.receive`.
3. The routing answer: **no router**. `nd-supervise` already binds one socket to one child
   (client/src/bin/nd-supervise.rs:1-7) **[read]**, so one supervisor pair per Store per socket is the status
   quo. Keep T1's router demo shape (kill one resident, the other still answers) as a plant **[ran by T1, not by
   me; I did not rebuild router/]**.
4. The stated limit: a copied Store directory is the same Store (a fork). No request binding can see a fork.

**Discard.**
- The Store NAME as identity (`Unsigned.store : ByteArray ≤ 64`, `Ctx.store`). A name is a local label. T1
  itself shows the clone hole it leaves, and its fix (`label ‖ 16 random bytes`) puts a random identity
  into a filesystem path. Replaced by D1/D2 (the World's genesis digest). Laws: 1 (one digest type for
  identities), 2 (the check reads data in the World, not a config value the follower must also be given).
- The clear-text segment header read before the MAC (`peekName`, `openSegment`). At main, open never
  reads offset 0 once a base has been sealed, so the header goes unread after the first seal. The pre-MAC
  decode also renders unverified bytes into a refusal (`foreignStore ampha`), which brushes law 7.
  Replaced by D4 (the tag already on disk before the base offset).
- `register`/`route`/`duplicateStore`: `Host.genesis` already refuses an existing directory (`.exists`,
  Host/Store.lean:110-122) **[read]**. A second registry would twin it (law 1). Keep only label validity as a
  path component, at the `host genesis` argv.
- The `bound : Bool` / envelope scaffolding (T1 says so itself; law 1).

### T2 — the remote mux: KEEP the mux fixes and the tests, REWORK the frame (B, not -L) and the definitions

**What I re-checked.** I copied T2 into my scratchpad, pointed its `nanodregg-client` dep at **main's**
`client/`, and ran the four Rust tests (the Lean-child test needs main's `.lake`, which I did not build)
**[ran]**:
```
STOCK: well-behaved client B after 3.001060125s: STARVED (timeout)
REMOTE: client B answered in 3.620792ms (200000 bytes)
4th connection with connectionsMax=3: Err("frame: closed")
idle_closes_silent_connection_but_not_one_awaiting_a_slow_reply ... ok
test result: ok. 4 passed
```
(T2's own socket path is too long for `SUN_LEN` from the scratchpad. I used a relative `r/` dir. That
changes only where the test is run from.) The head-of-line block can also be read off the code: `route`
calls `frame::write` synchronously, per reply, on the one routing thread (client/src/mux.rs:149-178) **[read]**.

**Keep.**
1. The one-slot per-connection writer (`sync_channel(1)` + `try_send`; a full slot closes that connection).
   It kills the measured HOL starvation.
2. The idle rule: silent **at a frame boundary AND zero requests in flight**, plus a deadline on a frame
   once it has started. Main's `idleMsMax` docstring says "no frame in either direction" (Table.lean:222-225)
   **[read]**, and that rule kills a client that is waiting on a slow reply. T2's test proves it.
3. The five test shapes: stalled reader, slow-loris header, slow reply survives, connection over the bound,
   and a real `Host.Wire` Lean child behind a proxy.
4. The finding that every mux-side close is nameless to the peer (law 7), and the reason enum.
5. The finding that `conn` is a counter, never an identity.

**Discard / rework.**
- The `ssh -L` framing. The chosen remote shape is CLIENT-12 B, where each friend's `authorized_keys` line
  runs `nd-attach`. The HOL fix matters *more* under B. A sleeping friend's `nd-attach` stops draining its
  host.sock connections. Today's box-side `route` then blocks on that write and starves every friend
  **[assumed: derived from mux.rs route + CLIENT-12 B's shape; not run]**.
- "Prove one reply per request": `Machine.replies_size` already says that, for the batch machine
  (`(m.admitBatch w qs).2.replies.size = qs.length`, Host/Proofs/Batch.lean:65) **[read]**. What is still owed
  is the Loop-level statement that each reply carries its request's `conn`, including on the
  failed-sync/`uncertain` path **[assumed missing; not checked]**.
- The copy of mux.rs as a second mux (T2 says so: law 1). The builder edits `client/src/mux.rs`.
- "Per-friend identity" as a mux question: under B, the forced-command line can name the peer for **DoS
  accounting only** (D6). It is never authority.

### C1 — thin consent via a sealed base: KEEP (conditional on PROTOCOL-14's ruling), small REWORK

**What I re-checked.** `lean --run Demo.lean` → 24/24 PASS **[ran]**. `Host/Serve.lean:74-75` refuses `read`
and `log` `notServed` **[read]**. `Op.reserved` marks `read` **[read: Table.lean:92-95]**. `Envelope.check`
exists with the cited shape **[read]**. `Host/Keys.lean domBase = "nanodregg/host/base/v1"` is the KMAC
customization **[read]**, and HOST-15 proposes the same string for the pin's `Hash.digest` **[read]**. C1's
domain-collision finding is right. The base record is `world ‖ u64 offset ‖ tag32` and `Base.read` returns
the World's byte size (Base.lean) **[read]**, so a page is one pread with no re-encode.

**Keep.**
1. `follow = foldlM absorbPage` from a different start World: one fold, no second consent path. Update it to
   the `(World × Turns)` return.
2. `serveBasePage` = `Envelope.check`, then a slice of the existing base file's World bytes, with the client
   half's refusals `pageMoved / pageDigest / pageTotal / pageGap`.
3. The pin as (height, digest) under its **own** domain (`nanodregg/host/base-digest/v1`).
4. The two findings no decision file states:
   - The journal inside the base answers `lookup` for txIds from before the base.
   - At THE BAR, thin downloads about as much as full follow, because `tailMax = 2·cadence + frameMax` and
     the cadence floor is 1 MiB, which is the same order as the whole BAR log. Thin wins only on churny stores.
5. The UNDETECTED plant: a pinned World whose history a full audit refuses is accepted by thin. It is the
   honest statement of what thin trusts.

**Rework.**
- `thinOpen` must be the decode half of `openWith`/`Base.read`, factored out, not a copy (C1 says so).
- The attestation binds `name`. It must bind the **origin** (D1).
- Where a pin comes from: see D7. Use the invite, signed by the sponsor, with a cross-check against the
  decoded World.

### C2 — per-cell blinding: DISCARD for this assembly (declared absence); keep three facts for Ember

**Why discard.** PROTOCOL-3, as ruled by ROOT 2026-10-16, makes per-cell hiding from members a **declared
absence for v1**, tied to the blinding-key custody question that is open with Ember **[read]**. Key custody
is on CLAUDE.md's short pause list (item 1). C2's own verdict is "idea". A codec with no row and no custody
decision would be code that nothing reaches. I did not run C2. It was built against the stale tree, and
its demo uses a toy hash.

**Keep, as input to Ember's KEY-CUSTODY decision (not as code):**
1. Ciphertext as opaque slot bytes needs zero change to `pinOf`, `Cell.weight`, discipline or the journal
   (C2's demo; consistent with Cell.lean's opaque slots **[read]**).
2. The price is now stated, not avoided. For a law that reads blinded state, a keyless follower cannot
   `rederive` (PROTOCOL-4), so its consent weakens to structure plus pins.
3. If it is ever built, these are required corrections **[read: C2's own critique + main's Codec.Hash]**:
   - the PRF is `Codec.Hash.mac` (KMAC256), not `H(key ‖ …)`;
   - encryption and tag keys are split;
   - `pre` is derived in Lean, never chosen by the caller;
   - the Host never holds the key (C2's "must not", which I endorse: that is the minidregg codec-child hole).

---

## 2. The assembled system, in one paragraph

A Store's identity is its **origin**: the digest of its genesis descriptor, including 32 bytes of OS
randomness, held in the World and never changed. Every signed call and every read envelope names the
origin it is for. `receive` and `Envelope.check` refuse any other origin by name (`wrongStore`) before
anything else, and a follower's `rederive` refuses a foreign event at its index for free.

A Store's **segment** is bound to its base by the tag already on disk. Open refuses a segment whose 32
bytes before the base offset are not the base's tag (`foreignSegment`), so a foreign file is never
truncated as a torn tail. Genesis writes one origin frame, so the base offset is never 0.

Transport stays one `nd-supervise` per Store per socket. Its mux gives each connection a one-slot writer,
idles a connection only when it is silent at a frame boundary with nothing in flight, bounds a started
frame and a reply write, and tells the peer why it closed (`Status.closed` + a Lean-named `CloseReason`).

Friends reach the box through CLIENT-12 B's `nd-attach`, which caps its own connections per peer.

Thin members (if PROTOCOL-14 rules "thin in time") page the newest base through `read` (envelope-gated),
check it against a pin carried in their invite and signed by their sponsor, and then run the same
`absorbPage` fold as every follower.

Blinding is absent until Ember rules custody.

---

## 3. Interface decisions (real signatures, owner, both critiques)

### D1 · KERNEL (+CODEC) — `World.origin`: a Store is its genesis digest, with entropy

```lean
-- Kernel/World.lean
structure World (D : Type) [Ord D] where
  cells : Std.TreeMap D Entry compare
  journal : Std.TreeMap D (Nat × D) compare
  spent : Std.TreeSet D compare
  height : Nat
  chain : D
  allowance : Nat
  /-- the Store's identity: `hash domGenesis descriptor`; set by genesis, never changed by `admit` -/
  origin : D

def World.genesis (E : Env D) (descriptor : ByteArray) (allowance : Nat) : World D :=
  let o := E.hash domGenesis descriptor
  { cells := {}, journal := {}, spent := {}, height := 0, chain := o, origin := o, allowance }

-- Kernel/Proofs/…
theorem admit_origin : World.admit E w t = .ok w' → w'.origin = w.origin
theorem fold_origin  : World.fold E w ts = .ok w' → w'.origin = w.origin

-- Kernel/Receive/Follow.lean: descriptor = CODEC's canonical (name, nonce32, allowance, founders);
-- founder ids are derived from the origin, not the name
def genesis (X : Ctx D) (name nonce : ByteArray) (allowance : Nat) (founders : List (ByteArray × D)) : World D
def founderId (X : Ctx D) (origin : D) (i : Nat) : D := X.env.hash domFounder (X.env.bytes origin ++ index32 i)
```
`host genesis` draws the nonce with `IO.getRandomBytes 32` (Host/Sim/File.lean:30 already does this for the
key) **[read]**. The Sim uses a seeded nonce. The CODEC World codec (CODEC-14) gains the field. The
descriptor codec is new.

- **Alternatives.** (a) T1's name in `Ctx` and in `Unsigned`. (b) `label ‖ 16 random bytes` as the name.
  (c) An id derived from the Store key: refused, because HOST-16's law says nothing derives identity from
  that key. (d) No field; recompute the origin from height-0 data every time (the chain moves, so this
  cannot be done).
- **Why.** The identity is data inside the World, so `receive`, `rederive` and the thin pin all check it
  with no configuration. It is content-addressed (law 3), it is one digest type (law 1), and its entropy
  comes from genesis, not from a naming ceremony.
- **CRITIQUE.** The origin needs a channel to the member. A member who learns it from the Host it is
  connecting to (trust on first use) is protected against mis-routing but not against a hostile Host
  serving another Store. The invite has to carry it, and no invite format exists yet. A copied Store
  directory keeps its origin, so it is a fork the binding cannot see: only followers comparing chains can.
  Re-keying founder ids by origin changes every founder id in every row and fixture.
- **META-CRITIQUE.** I prefer it because it turns a config check into a data check, which is law 2's
  aesthetic. I have not priced the invite, and that is where the cost went. I also discarded T1's name
  partly because it was the scout's and not mine.

### D2 · KERNEL (+CODEC) — `Unsigned.store`, checked first, refused by name

```lean
-- Kernel/Receive/Call.lean
structure Unsigned (D : Type) where
  store : D                 -- the origin this call is for; inside unsignedBytes, so signed
  member : D
  key : ByteArray
  notBefore : Nat
  validUntil : Nat
  pins : List (D × D)
  maxCharge : Nat
  body : Body D

inductive Refusal (D : Type)
  | wrongStore (declared : D)          -- NEW; name "wrongStore"
  | badSignature
  …

-- Kernel/Receive/Derive.lean (receiveWith stays pin-only, KERNEL-4)
def receive (X : Ctx D) (w : World D) (c : Call D) : Except (Refusal D) (Turn D) := do
  req (c.unsigned.store = w.origin) (.wrongStore c.unsigned.store)
  receiveWith X (pinned w c.unsigned.pins) c

theorem receive_store   : receive X w c = .ok t → c.unsigned.store = w.origin
theorem receive_foreign : c.unsigned.store ≠ w.origin → receive X w c = .error (.wrongStore c.unsigned.store)
```
`Codec/Kernel.lean`'s `unsigned` codec (line 156) gains the field first **[read: it is CODEC's file]**.
`txIdOf = H(domTx, callBytes c)` (Call.lean:248) then differs across Stores automatically **[read]**.

- **Plant (non-vacuity).** T1's clone baseline restated: same name, same founder keys, different nonce.
  Before D1/D2 the call is admitted; after, it is `wrongStore`. Plus `audit` over a log with one foreign
  event, which must be refused at that index.
- **Alternatives.** (a) The origin in the signed message but not on the wire: no bytes added, but a
  cross-store call becomes `badSignature`, a wrong name (law 7, and the minted "refusal renders as the
  expected verdict" class). (b) `Turn.store` checked by `admit`: a second place for the same fact (law 1),
  when `rederive` already covers the follower. (c) `Ctx.store` (T1): config the follower must be handed.
- **Why.** One signed field gives the right refusal name and is covered by the existing signature.
  Checking it first, in `receive`, keeps `receiveWith` over pins only.
- **CRITIQUE.** Every event grows by 32 bytes. At deployed Ed25519 call sizes (~250 B) that is ~13% more log
  and more `tailMax` churn **[assumed size; C1's toy events are ~146 B]**. Checking `wrongStore` before the
  signature lets an unauthenticated prober confirm an origin guess. The origin is not secret and socket
  access is the real gate, but it is an oracle. It is a flag day across KERNEL, CODEC, the Sim, every row
  and every fixture.
- **META-CRITIQUE.** I am paying 32 B per call for a refusal name. `badSignature` would be equally safe.
  Law 7 is the law I cite, and I might cite a different one if the bytes were scarce.

### D3 · PROTOCOL — the read envelope names its Store

```lean
-- Protocol/Envelope.lean
structure Envelope (D : Type) where
  store : D
  member : D
  grant : D
  start : Nat
  validUntil : Nat
  key : ByteArray
  signature : ByteArray

inductive ReadRefusal | wrongStore | badEnvelope | unknownKey | badSignature | expired | noFollowGrant

def Envelope.message (X : Ctx D) (store member grant : D) (start validUntil : Nat) : ByteArray :=
  domEnvelope ++ X.env.bytes store ++ X.env.bytes member ++ X.env.bytes grant ++ Text.u64 start ++ Text.u64 validUntil

def Envelope.check (X : Ctx D) (w : World D) (e : Envelope D) : Except ReadRefusal Unit := do
  req (e.store = w.origin) .wrongStore
  …                                     -- unchanged after this line
```
`envelopeLayout` (Table.lean) and `envelopeFrame` (Frames.lean) gain the field. `check_ok_iff` gains the
conjunct. `name_injective` is re-proved.

- **Alternatives.** Leave reads unbound (a captured envelope replays against a clone within `validUntil`),
  or bind the store implicitly (`badSignature`).
- **CRITIQUE.** It is the same oracle as D2, and PROTOCOL-12 already notes that the refusal names leak
  membership. It is one more field in a layout that is still read by hand on the Rust side (CLIENT-10).
- **META-CRITIQUE.** Symmetry with D2 is doing most of the arguing. A read replayed against a clone leaks
  only what that clone holds, and on that reading the binding is cheap insurance, not a closed hole.

### D4 · HOST — a segment is bound to its base by the tag already on disk

```lean
-- Host/Base.lean
inductive BaseFault
  | … | foreignSegment       -- the 32 bytes before the base offset are not the base's tag

-- Host/Open.lean, in openWith, after tailRead: read [b.offset - tagBytes, size) in the ONE readTail call
--   (b.offset ≥ tagBytes always, see genesis), require head = b.tag.bytes, else .base .foreignSegment,
--   then openLog on the rest exactly as today.
theorem openWith_foreign : seg.extract (b.offset - Log.tagBytes) b.offset ≠ b.tag.bytes →
    openWith … = .error (.base .foreignSegment)
theorem openWith_reads   -- re-stated: open reads [b.offset - tagBytes, size), at most tailMax + tagBytes

-- Host/Store.lean genesis: write ONE frame `Log.frame keys.segment segmentInitial (E.bytes w₀.origin)`,
--   sync, then seal the base at offset = that frame's size, tag = its tag.
```
This works because every frame ends with its own tag (`frame prev r = len ‖ r ‖ tag (prev ‖ r)`,
Log.lean:60) and the base stores the chain tag at its offset (Base.lean header) **[read]**. Cost: 32 extra
bytes in the one read open already makes **[read: openWith has a single readTail]**.

- **Plant.** Foreign.lean (above) restated in `host-sim` as `plant-foreign-segment`: A's segment under B's
  base at both offset cases must be `foreignSegment`, and nothing is truncated. host-file-sim also checks
  the file size is unchanged.
- **Alternatives.** (a) T1's clear-text header at record 0, MAC'd and read on open. At main it goes unread
  once a base is sealed. (b) An out-of-band durable segment length (HOST-12's critique: a second fsync per
  batch). (c) A per-Store `segmentInitial`: foreign frames already fail to verify, so the problem is the
  torn-vs-corrupt classification, which this does not change.
- **Why.** It reuses a value already on disk, adds no record type, and costs 32 bytes per open.
- **CRITIQUE.** It catches a foreign file. It does not catch our *own* segment from a divergent copy (a
  backup restored past the base offset) whose bytes match up to the offset. Bad bytes after that still
  read as torn when ≤ frameMax. HOST-12's undecidable class remains, and with `frameMax` at 32 MiB it is
  wide. Genesis becomes two writes (the frame, then the base). A crash between them leaves a directory
  that `genesis` refuses as `.exists`, so the operator must remove it. That has to be stated in the
  refusal text.
- **META-CRITIQUE.** I like it because it is small and reuses a tag (law 1 comfort). I built the plant for
  the hole, not yet for the fix. The 32 MiB `frameMax` is the bigger issue: it makes the HOST-12 "torn"
  window huge, and nobody has questioned it.

### D5 · PROTOCOL + CODEC + CLIENT — the mux: named closes, idle with nothing in flight, one-slot writers

```lean
-- Protocol/Table.lean
inductive Status | ok | refused | uncertain | absent | closed      -- closed = 4: the supervisor closed
                                                                   -- this connection; payload = CloseReason.name
inductive CloseReason | idle | frameStalled | replyBacklog | replyWriteFailed | frameRefused | full
def CloseReason.name : CloseReason → String           -- with name_injective
namespace Bounds
/-- Closed when silent AT A FRAME BOUNDARY with NO request in flight (the old "no frame either way"
rule closed a client awaiting a slow reply). -/
def idleMsMax : Nat := 300000
def frameMsMax : Nat := …          -- a started frame must complete within this
def replyWriteMsMax : Nat := …     -- one reply write to a peer must complete within this
```
```rust
// Emit/Rust.lean (CODEC): bounds += IDLE_MS_MAX, FRAME_MS_MAX, REPLY_WRITE_MS_MAX; emit a close_reason module
// client/src/mux.rs (CLIENT)
pub struct MuxLimits { pub frame: Limits, pub connections_max: u32,
                       pub idle: Duration, pub frame_deadline: Duration, pub reply_write: Duration }
// one writer thread + sync_channel(1) per connection; `route` only try_sends; Full => close(ReplyBacklog);
// forward counts in-flight; every close writes `Status::Closed ‖ reason name` best-effort, then shuts down,
// including the over-the-bound accept (`full`).
```
- **Relied-on theorem.** `Machine.replies_size` (exists). Owed: the Loop-level "every request frame gets
  exactly one reply with its own conn, or the child exits", including the `uncertain` path. The in-flight
  counter is correct only if it holds.
- **Alternatives.** (a) A single-threaded epoll loop: a smaller bound, but more Rust. (b) Close silently
  and log the reason on stderr only (law 7 fails for the peer). (c) Keep `idleMsMax` as "no bytes".
  Refuted by T2's test.
- **CRITIQUE.** The mux now originates a frame and decides when to close. The vocabulary and the numbers
  are Lean's, but the timing judgement is Rust's: a stretch of law 2 that exists only because the Lean
  child cannot see time. A best-effort close frame can race a reply the child already sent; the client's
  answer is the existing `lookup` recovery. The one-slot writer closes a pipelining client (`nd` is
  sequential, but nothing enforces it). There are now two threads per connection (≤ 128 + accept). None
  of the three deadlines has been measured over a real sshd. A slow WAN link can make a healthy friend
  hit `replyWriteFailed`.
- **META-CRITIQUE.** I accept T2's fix because the HOL is readable in `route` (derive what the code
  decides), not because of a macOS-buffer measurement. That reading is also a reason to under-test it.

### D6 · CLIENT — the remote side is CLIENT-12 B, with a per-peer cap in `nd-attach`

```rust
// sandbox/ or client/src/bin/nd-attach.rs (CLIENT): authorized_keys line
//   restrict,command="nd-attach /srv/nd/stores/<label>/host.sock <peer-label>"
// conn-tagged frames on stdin <-> one host.sock connection per conn; at most PEER_CONNECTIONS_MAX
// (a Protocol.Bounds row, emitted), the next one answered `closed full`; exits on EOF.
```
- **Alternatives.** CLIENT-4's `ssh -L` (T2's frame): zero code, but the filesystem is the authorization
  and there is no per-peer anything. A TCP listener: refused in CLIENT-12.
- **CRITIQUE.** The peer label is a Rust-held name used for quota. It is never authority, but it is an
  identity in Rust. A friend who opens several ssh sessions gets several caps. The only cross-session
  levers are sshd's `MaxSessions`/`MaxStartups`, so "one friend cannot take all 64 slots" still does
  not hold. There is new code on the box's attack surface.
- **META-CRITIQUE.** CLIENT-12 already chose B. I am ratifying a sibling's decision and adding a number to
  it, not re-deriving it.

### D7 · HOST + PROTOCOL — `read` serves the base; the pin travels in the invite (gated on PROTOCOL-14)

```lean
-- Protocol/Table.lean: Op.reserved .read := false; readReplyLayout = (height u64, total u64, digest, chunk)
-- Host/Keys.lean (or Host/Base.lean): a distinct domain
def domBaseDigest : String := "nanodregg/host/base-digest/v1"
def baseDigest (worldBytes : ByteArray) : Digest := Hash.digest domBaseDigest worldBytes
-- Host loop: the seal Task returns SealedBase { height, digest, worldBytes : Nat } with the base it wrote
-- Host/Serve.lean
| some .read => match Envelope.check X w e with
    | .error r => refuse r.name
    | .ok () => page sealed e.start          -- one pread at 4 + start of base.world, ≤ frameBytesMax
-- Host/Base.lean: factor `Base.decodeWorld` out of Base.read; thinOpen = pin check + decodeWorld (no copy)
-- Protocol (follow side)
structure Pin (D) where origin : D; height : Nat; digest : Digest
def thinOpen (c : Cadence) (pin : Pin D) (bytes : ByteArray) : Except ThinFault (World D)
-- invite: (origin, height, digest) signed by the sponsor's member key; after decoding, the sponsor's
-- key must be the current key of a live member of the decoded World (`attesterNotMember`)
```
- **Alternatives.** (a) PROTOCOL-14 option B: a Merkle state root with per-cell paths, which means a
  second commitment and a second verifier. (b) A standalone attester key (C1). (c) A World cell holding a
  countersignature (circular; C1's analysis).
- **Why.** It is one fold. The pin rides on the one artifact a joining member already trusts (its
  invite). The cross-check against the decoded World is a pair assertion, not trust.
- **CRITIQUE.** At THE BAR it saves nothing (C1's tailMax arithmetic **[read; derived, not measured]**).
  Thin is thin in time, not in space, so a phone that cannot hold the World still has nothing. The pin's
  trust is the sponsor, a person. It turns a reserved op into a live one (5 live → 6 live). If
  `thinOpen` is written as a copy, it is a second start-state path (law 1).
- **META-CRITIQUE.** I am recommending it because Ember said "if we can get away with it" and C1 showed
  that we can. *Can* is not *should*. And the invite-carried pin is my idea, so I have not attacked it
  the way I attacked the scouts'.
- **Gate.** Build it only after ROOT/Ember rule PROTOCOL-14 "thin = time". If they rule "space", D7 is
  wrong and option B is the work.

### D8 · (no code) — the blinding key is a custody question for Ember

This is C2's option 2 plus the corrections in §1 C2, written as a KEY-CUSTODY entry in decisions/client.md
by CLIENT, not built.
- **CRITIQUE.** Not building it leaves PROTOCOL-3's per-cell confidentiality absent, and J5/K10/KH are met
  only by gating the whole log.
- **META-CRITIQUE.** "It's on the pause list" is a comfortable reason to drop the hardest piece. The test
  is whether a custody ruling arrives. If it does not arrive within a week, the absence has become a
  deferral, and per the repo doctrine a deferral is the failure mode.

---

## 4. Charter rows

No new permanent layer. Every deliverable lands in an existing owner's paths (gates/OWNERS). One
**temporary** lane executes the list and dissolves when it lands.

| row | owner | owns | must never | first deliverable |
|---|---|---|---|---|
| **TRANSPORT** (temporary lane) | BUILD-TRANSPORT (Opus) | nothing permanently. Drives D1–D7 into the owners' paths; every commit carries that owner's subject prefix; `CROSS-LAYER:` only for the D1+D2 flag day | build its own copy of an owner's thing; keep a name-only or config-only Store identity; ship a mux close without a name; hold or design any key; edit in `~/dev/nanodregg` | D4: `foreignSegment` + genesis origin frame + `plant-foreign-segment` in host-sim and host-file-sim |
| KERNEL (new deliverable) | KERNEL | `World.origin`, `Unsigned.store`, `Refusal.wrongStore`, origin-keyed founder ids | derive identity from the Store key (HOST-16 law) | `admit_origin`, `fold_origin`, `receive_store`, `receive_foreign` + the clone plant |
| CODEC (new deliverable) | CODEC | descriptor codec; the World codec and call codec fields; emitted `IDLE/FRAME/REPLY_WRITE_MS_MAX`, `PEER_CONNECTIONS_MAX`, `close_reason` | hand-copy a constant into Rust | the codecs with `*_lawful` re-proved; `emit-rust` regenerating generated.rs |
| HOST (new deliverable) | HOST | `foreignSegment`; the genesis origin frame; `SealedBase` with `baseDigest`; `read` base pages; a measured compiled `host serve` idle RSS | fall back to an older base or a whole-log fold on `foreignSegment` | `openWith_foreign`; then a WASTE row `read bytes-per-page` |
| PROTOCOL (new deliverable) | PROTOCOL | `Envelope.store`; `Status.closed`; `CloseReason`; the redefined `idleMsMax`, `frameMsMax`, `replyWriteMsMax`, `peerConnectionsMax`; rows `wrongStore`, `foreignSegment`, `muxClose`, `thin` (after PROTOCOL-14) | let a row claim `read` before the reservation flips | Envelope.store + `check_ok_iff` + a cross-store envelope plant |
| CLIENT (new deliverable) | CLIENT | the mux.rs rework (D5) and `nd-attach` (D6) | infer identity from `conn`; keep a second mux | the mux rework with T2's five tests ported into client/tests |

The builder must also ask GATES to add `transport` to `scripts/worktree`'s layer list
(scripts/worktree:9) **[read]**, or create the worktree with
`git -C ~/dev/nanodregg worktree add --detach ~/dev/nanodregg-wt/transport refs/heads/main`.

---

## 5. Risks (what gets worse)

1. **The D1+D2 flag day** touches the call codec, the World codec, the Sim, every row, every fixture and
   founder ids. Every lane mid-flight on those files goes red at once. ROOT must announce it. Re-emit:
   the World codec and base (every Store re-genesised), generated.rs. Refuse to load: any base without
   `origin`, and any call without `store`.
2. **Trust on first use until invites exist.** D1/D2 stop mis-routing and clones. They do not stop a hostile
   Host from serving a different Store to a member who learned the origin from that Host.
3. **Log growth** of +32 B per event (~13%, assumed size). The cadence is in bytes, so seals come sooner.
4. **The mux grows** from 1 to 2 threads per connection. It now makes timing decisions in Rust and
   originates frames. All three deadlines are unmeasured on real ssh, and healthy slow friends may be
   closed.
5. **D4 covers foreign files only.** Divergent copies of our own segment still fall into the HOST-12 torn
   window, which is **32 MiB** at deployed bounds.
6. **D7 adds a live op and a trust input** (the sponsor). At THE BAR it buys nothing. A copied `thinOpen` would
   be a second start path.
7. **Store count per box is unmeasured.** T1's 470 MB is the interpreter, and each Store's mux bound is
   32 MiB. N Stores is a product number nobody has.
8. **Stale-checkout mirrors.** Any future scout or lane that compiles in `~/dev/nanodregg` repeats T1/T2/C2's
   ground-truth errors. GATES could make `lake` refuse to run there, which would be a structural fix.
9. **Blinding stays absent.** If Ember's custody ruling does not come, PROTOCOL-3's confidentiality rows stay
   "gate the whole log" indefinitely.

---

## 6. FIRST BUILDER BRIEF — BUILD-TRANSPORT (Opus)

**You are BUILD-TRANSPORT**, a temporary nanodregg lane. You land six decisions (D1–D7 of
`~/dev/redregg/work/nanodregg-scout/ASSEMBLY-transport-consent.md`, read it whole first) into the OWNERS'
paths, in this order: **D4 → D1+D2+D3 → D5 → D6 → D7 (only after PROTOCOL-14 is ruled "thin = time")**. D8
is not code. You own no path permanently. You dissolve when the list lands.

**Ground truth, read first, in this order.**
1. `~/dev/nanodregg/CHARTER.md` **at main**: `git -C ~/dev/nanodregg show main:CHARTER.md`. The primary
   checkout's working tree is STALE (§0). Never read, build or `lake env` there.
2. `decisions/host.md` HOST-11, 12, 14, 15, 16; `decisions/protocol.md` PROTOCOL-3, 4, 8, 12, 13, 14;
   `decisions/client.md` CLIENT-12, 13; `decisions/kernel.md` KERNEL-4, 13 (all from your worktree).
3. `~/dev/redregg/work/HOST-LOG.md` (the commit and sim commands; the people).
4. The real signatures: `Kernel/World.lean:89-147`, `Kernel/Receive/Call.lean:65-121,185-194,248-251`,
   `Kernel/Receive/Derive.lean:283-290`, `Kernel/Receive/Follow.lean`, `Codec/Kernel.lean:156-172`,
   `Host/{Log,Base,Open,Store,Keys,Serve}.lean`, `Protocol/Envelope.lean`, `Protocol/Table.lean:105-130,205-225`,
   `Emit/Rust.lean:30-36`, `client/src/mux.rs`, `client/src/bin/nd-supervise.rs`.

**Worktree.** Ask GATES to add `transport` to `scripts/worktree` (line 9), or run
`git -C ~/dev/nanodregg worktree add --detach ~/dev/nanodregg-wt/transport refs/heads/main`. Work ONLY in
`~/dev/nanodregg-wt/transport`. Commit ONLY with `scripts/commit -F MSG PATH...` (a quoted heredoc for the
message). The subject prefix is the owner of the paths (`host:`, `kernel:`, `protocol:`, `client:`, `codec:`).
Each SIZE rise gets a `SIZE: <metric>: <why>` line. `CROSS-LAYER: <reason>` is allowed only on the D1+D2
flag-day commit. Never the shared index, never `git add -A`, never `git stash`. Before each commit, `git show
--stat HEAD` must list only your paths. Tell the owner (SendMessage; ids in HOST-LOG "People"; KERNEL via
ROOT) before you touch their layer, and land through their review if they are mid-edit on that file.

**Step 1: D4 (HOST paths only; first commit).**
- Lift the plant from
  `/Users/ember/dev/redregg/work/nanodregg-scout/plant-foreign-segment.lean`
  (it ran against main's `openWith`: a foreign segment opens `torn` and the writer truncates it). Restate it
  as `plant-foreign-segment` in `Host/Sim/Run.lean` (MemStore) and in host-file-sim (real file; assert the
  file size is unchanged).
- Add `BaseFault.foreignSegment` with its name. In `openWith`, read `[b.offset - tagBytes, size)` in the
  existing single `readTail` and require the head to equal `b.tag.bytes`. `genesis` writes one origin
  frame (today: `E.bytes w₀.chain`, which becomes `w₀.origin` after step 2), then the base at that frame's
  end.
- Re-state `openWith_reads` (one read, ≤ `tailMax + tagBytes`) and prove `openWith_foreign`.
- Build: `cd ~/dev/nanodregg-wt/transport && lake build Host host-sim host-file-sim`; then
  `for s in 1 2 3; do lake exe host-sim $s | tail -1; .lake/build/bin/host-file-sim $s | tail -1; done`, which must
  print ALL PASS ×6, with the new plant named in the output.
- Write HOST-17 in `decisions/host.md` with both critiques (copy D4's and sharpen them).

**Step 2: D1+D2+D3 (the flag day; one CROSS-LAYER commit if the build forces it, otherwise one commit per layer in
dependency order).**
- KERNEL: `World.origin`, `World.genesis E descriptor allowance`, origin-keyed `founderId`/`founderGrantId`,
  `Unsigned.store` first, `Refusal.wrongStore`, the check in `receive` (NOT in `receiveWith`), and the
  theorems `admit_origin`, `fold_origin`, `receive_store`, `receive_foreign`.
- CODEC: the descriptor codec, `unsigned` with the field, and the World codec with the field, with
  `*_lawful` re-proved.
- PROTOCOL: `Envelope.store`, `ReadRefusal.wrongStore`, `check_ok_iff`, `name_injective`.
- Plants:
  - the clone (same name, same founder keys, different nonce): admitted before, `wrongStore` after;
  - `audit` over a log with one foreign event, refused at its index;
  - a cross-store envelope.
- The commit message says what re-emits (World codec, every base, generated.rs, every fixture), what
  refuses to load (a base without `origin`, a call without `store`), and that every Store re-genesises.
- Gates that must stay green: kernel-sim over its seeds, `lake exe rows`, host-sim. Run them filtered to
  what they are; never an unfiltered suite.
- Decisions: KERNEL-22 (origin) in `decisions/kernel.md`, written by you only if KERNEL agrees, otherwise
  KERNEL writes it; PROTOCOL-17 (envelope store).

**Step 3: D5 (PROTOCOL table + CODEC emit + CLIENT mux).**
- `Status.closed` (code 4), `CloseReason` + `name_injective`. Redefine `idleMsMax` (boundary-silent with
  nothing in flight). Add `frameMsMax` and `replyWriteMsMax`, and emit all three plus `close_reason` via
  `Emit/Rust.lean`, then regenerate `client/src/generated.rs` with `lake exe emit-rust` (CODEC's file).
- Rework `client/src/mux.rs` in place. Lift from `/Users/ember/dev/nanodregg-scout/T2/src/lib.rs`: the
  one-slot writer, the in-flight counter and the boundary wait. Add a named close frame on every close,
  including over-the-bound accept.
- Port T2's five tests from `/Users/ember/dev/nanodregg-scout/T2/tests/remote.rs` into `client/tests/mux.rs`,
  with socket paths short enough for `SUN_LEN`. The Lean child is built from YOUR worktree's `.lake`, not
  `~/dev/nanodregg`.
- Prove or name as owed: the Loop statement "one reply per request frame, with its conn, including
  `uncertain`" (with HOST).
- `cargo test --offline --test mux` only, never the whole crate suite.

**Step 4: D6.** Write `nd-attach` per CLIENT-12 B with `PEER_CONNECTIONS_MAX` from the table. Test it with
two pipes standing in for sshd, as CLIENT-12 proposed. State in decisions/client.md that the cross-session cap
is absent.

**Step 5: D7, only after the PROTOCOL-14 ruling.**
- Lift from `/Users/ember/dev/nanodregg-scout/C1/Thin.lean`: `serveBasePage`, `assemble` and its four page
  refusals, and `Pin`.
- Replace `thinOpen` by a factored `Base.decodeWorld` (no copy). Use `domBaseDigest =
  "nanodregg/host/base-digest/v1"`. Bind the attestation to `origin` and carry it in the invite, signed by
  the sponsor, with the `attesterNotMember` cross-check. Update `follow` to the `(World × Turns)` return of
  `absorbPage`.
- Keep C1's UNDETECTED plant and its pre-base `lookup` plant in the `thin` row. Flip `Op.reserved .read`.

**Lift / ignore.**
- **Lift:** `/Users/ember/dev/redregg/work/nanodregg-scout/plant-foreign-segment.lean` (my plant); T1's theorem shapes `foreign_never_admitted` / `admit_names_this_store`
  (restated over `receive`); T1's router kill-one-resident demo as a plant shape
  (`/Users/ember/dev/nanodregg-scout/T1/router/src/main.rs`); T2's `src/lib.rs` mechanisms and `tests/remote.rs`
  shapes; C1's `Thin.lean` page and assembly code and `Demo.lean`'s plant list.
- **Ignore:**
  - T1's `Multi.lean` request envelope, `bound : Bool`, `Ctx.store`, the name identity,
    `header`/`peekName`/`openSegment`, and `register`/`route`;
  - T1's and T2's line numbers (stale tree);
  - T2's `ssh -L` proxy as the deployment shape;
  - C1's `checkAttestation` by a standalone key, and C1's `baseDomain` string (it collides with
    `Host/Keys.lean domBase`);
  - all of C2 as code (`Blind.lean`, `All.lean`): it is input to Ember's KEY-CUSTODY decision only.

**Box safety (verbatim from the operator's rules).**
- NEVER run an unfiltered `-p <crate>` / bare `cargo test` / whole suite. Run the narrowest thing that could
  refute you, and state your control separately (counts unchanged, bytes identical).
- No hbox, no box builds. Mac only; the Mac data volume is ~98% full: no artifacts over 1 MB, keep `.lake`
  small, delete nothing that is not yours. Under disk pressure: stop, measure, report, wait.
- Stopping processes: PID file or nothing (incident 2026-10-10):
  "A subagent ran `pkill -f "cat" -u ember` to clear its own stuck `cat`. `-f` matches the whole
  command line, every app lives under `/Appli**cat**ions`, and 44 of my apps and agents got SIGTERM.
  - **Never kill by pattern.** No `pkill -f <anything>`, no `pkill -x <bare word>`, no `killall`, no `kill -u`.
  - **A process you started is stopped by the PID in its PID file**, and only that. Every detached job
    writes one (`nohup ... & echo $! > job.pid`). No PID file, no kill: tell me instead.
  - If you must look first, `pgrep -fl` and read the list; it is never the argument to a kill.
  - Every subagent brief you write quotes this block verbatim."
- Foreground-wait builds; never background a build and wait for a notification.

**Verdicts come from artifacts.**
- A theorem statement is read by a second agent before it lands (law 6). In particular `receive_foreign`
  and `openWith_foreign` must be about the functions the loop runs, not about a restated copy.
- A plant must be shown to FIRE before its verdict is read: assert the mutation happened.
- `ALL PASS` from a sim you did not build from main plus your paths is not evidence.

**Report to ROOT on events only:**
- D4 landed (sha + plant line);
- the flag day announced BEFORE you land it, and then landed;
- the mux close vocabulary landed;
- PROTOCOL-14 needed;
- your handoff in `~/dev/redregg/work/TRANSPORT-LOG.md` before 350K tokens, in HOST-LOG's shape (Landed /
  Exact commands / Next, in order / Open decisions / People).

**Critique of this brief.**
- One lane crossing five owners risks the stale-index and caller-committed-callee-not classes. The
  alternative is to hand D4/D7 to HOST's veteran lane, D1/D2 to KERNEL's, and D5 to CLIENT's, which is
  cheaper in context; ROOT may prefer that.
- The order puts the smallest data-loss fix first because it has no dependencies, not because it matters
  most. The identity flag day matters most and has the widest blast radius.

**Meta-critique of this brief.** I wrote the order I could defend from the code I read. I did not ask the
owner lanes what they are mid-way through, and the flag day's real cost is what it interrupts.
