# decisions/protocol.md — BUILD-PROTOCOL

Reach table this layer is built from: `~/dev/redregg/work/DELETE-PROTOCOL-20261016.md` (minidregg main
2c27b08b: 186 opcodes, 86 reached by a landing row, 43 by nothing; 116 Host CLI verbs, 30 by nothing;
127 `mini` verbs, 56 by nothing; 12 consent frames, 3 a thin twin).

## PROTOCOL-0 · the row attacked (2026-10-16)
**Decision.** Keep PROTOCOL as a layer, but it is small and it owns three things only: the operation
table (`Protocol/Table.lean`), the one command language that `host follow` parses (`Protocol/Command`,
next), and the conformance rows (`Protocol/Rows.lean`). It owns no receiver (KERNEL `Kernel/Receive`,
ROOT ruling on HOST-1), no codec (CODEC generates the Rust copy of the table), no loop (HOST).
**Alternatives.** (a) Fold the table into CODEC (it is "just bytes") and the rows into GATES (they are
"just tests"). (b) The charter as written, with consent frames and broker verbs as protocol surface.
**Why.** (a) puts the deletion rule — no op without a row — in two layers that would each see half of it;
the theorem `every_op_has_a_row` needs the table and the rows in one place. (b) is dead: consent is
`host follow` (HOST-7), and broker verbs are sandbox plumbing over Lean-decided policy (CLIENT-7) with
no Lean wire of their own.
**Critique.** A six-op table and a row list is maybe 600 lines; a layer that small may be overhead, and
the command language is the part with real mass — it could equally be LANG's (it is a language) or
HOST's (follow runs it). If it grows a second parser (one for argv, one for row specs), that is a twin.
**Meta-critique.** I am the protocol owner arguing the protocol layer should exist; my evidence for it is
one theorem.
**Status.** open.

## PROTOCOL-1 · six operations on two sockets (2026-10-16)
**Decision.** host.sock: `submit` (the one write), `lookup`, `read`, `log`; follow.sock: `command`,
`resume`. Codes 1–6, globally distinct. Status ok/refused/uncertain/absent (0–3). Step tags
done/sign/host/submit (0–3).
**What each deleted minidregg op became.** Every family `*_PLAN` (26 ops) → a step of the follow machine
(follow derives the plan from its own fold); every `*_ASSEMBLE` and ops 7–11 (author, inspect,
signatures, observe-assemble, call-assemble) → follow steps (Lean builds the bytes; custody signs);
every `*_SUBMIT` incl. streamed 34/164, 46, 76 (≈28) → `submit` with a call KIND (KERNEL `Receive`);
every `*_LOOKUP` (≈25) → `lookup`; every view (pay/clock/key-status/certify/activity/seat/fleet/current
birth/route inspect/dispatch ready, ≈20) and describe/profile → `read` kinds; challenge (4) → gone: a
read is either answered by the member's own follow, or signed with its own window like a Turn
(PROTOCOL-3); dry-run (130) → follow computes `World.admit` on its own World, no op; law-sat (150) →
a LANG query run by follow, no op; certify (170–173) → the Host's own checkpoint seal; fn
poll/ack/outbox (12–19, 40–43, 60–65) → absent from the spec (no landing row reaches them) until a row
does; consent frames 220–233 → `host follow` (HOST-7).
**Alternatives.** (a) One op per call kind (~10, still small). (b) Keep plan/assemble on the Host for
members who cannot follow (thin). (c) A single op with a sub-tag (the table would then be the sub-tag).
**Why.** (a) puts the kind in two places (opcode and payload) and invites the 34-beside-164 twin; (b) is
the thin consent path, a declared absence (HOST-7a); (c) is the same table with worse names.
**Critique.** `read` exists only for members who do not follow and for the operator's describe. If every
member follows, `read` is dead weight; if reads must be authorized (J5, K10, KH), following leaks every
cell to every follower (PROTOCOL-3), and `read` is the only confidential path. `log` serves frames over
the socket so follow needs no file access; that makes the writer serve O(log) bytes to a cold follower.
**Meta-critique.** "Six" is attractive because it is small; I have not yet written the command language
that must carry everything the deleted ops did, so the mass may have moved, not vanished.
**Status.** open.

## PROTOCOL-2 · "every op names exactly one receiver" is a vacuous statement; the table proves two that are not (2026-10-16)
**Decision.** I did not state ROOT's "each op names exactly one receiver, as a theorem" literally: for a
total function `Op → Receiver` it is true by definition (an identity carrier). The table proves instead:
(1) `Op.receiver_injective` — no two ops name the same receiver (no function has two wires: the twin
class minidregg kept, 34/164, family ops beside op 2); (2) `Op.effect_write_iff` — exactly one op may
append (one admission path); and (3) `every_op_has_a_row` — no op without a row.
**Critique.** (1) is over names (strings) until KERNEL/HOST commit the declarations; two different
strings could name one function through an alias. The pending gate resolves each name in the
environment and compares the resolved constants, not the strings.
**Meta-critique.** Refusing the literal ask can be a way to avoid the hard version; the hard version is the
call-kind level (each `Receive.Call` kind derived by exactly one receiver arm), which is KERNEL's
exhaustive match, also structural. I believe no non-vacuous form of it exists below the injectivity above.
**Status.** ruled by ROOT 2026-10-16: ACCEPTED (receiver injectivity + single-writer replace the one-receiver statement).

## PROTOCOL-3 · consent-by-follow vs authorized reads: a conflict in the spec (2026-10-16)
**Finding.** HOST-7 makes consent = `host follow`, which folds the WHOLE log. Rows J5 ("a key with no
grant: read refused"), K10 ("outsiders refused"), KH ("covered entries open, the rest are sealed
leaves") require that a member NOT see cells it holds no grant on. A follower sees every cell's bytes.
So either (a) followers are only members trusted with the whole Store (the operator gives `log` access
as a capability), and other members read through `read` with authorization — and then those members'
consent is thin, i.e. trusts the Host; or (b) confidentiality is by encryption only (sealed leaves,
private-room ciphertext) and "read refused" becomes "read yields ciphertext"; or (c) the log a follower
receives is a per-member projection (redacted frames + proofs), which is a proof system (memory:
no proof system in admission) and a second log shape.
**Decision (proposed).** (a) for v0: `log` is served only to keys holding a `follow` grant; every other
read is `read` with the same authority check as a write's derivation. Rows J5/K10 keep their refusal
for `read`; the `audit` row is run by a follower.
**Critique.** (a) means the member most in need of consent (the outsider on a phone) has none; that is
HOST-7a's declared absence made explicit. (b) is cleaner but turns every confidentiality row into a
cryptography row. **Meta-critique.** I found this by reading rows against a decision another layer
made; I may be wrong about how much a follower must see if KERNEL's `Pinned` view lets consent run on
the pinned cells only (consent needs only the pinned cells + a proof they are current — again (c)).
**Status.** ruled by ROOT 2026-10-16: ACCEPTED for v0. `log` and `read` are served only to keys holding a FOLLOW GRANT; membership gates the whole log; per-cell hiding/blinding from members is a DECLARED ABSENCE for v1, tied to the blinding-key custody question open with Ember. J5/K10/KH hold: a key without a grant is refused at `log`/`read` by name.

## PROTOCOL-4 · follow must re-run the receiver on every logged event (2026-10-16)
**Finding.** `World.fold` admits Turns; `World.admit` decides no authority ("`admit` decides none of
them"). A follower that only folds Turns trusts the writer's receivers: a Host that logs a Turn no signed
call derives (a forged write) is folded happily. minidregg's audit re-admitted every ingress for exactly
this reason (JAUDIT). So `host follow`'s fold must be `fold (fun w t => do let t' ← receive w (decode
t.event); require t' = t; admit w t)` — consent and audit both depend on it.
**Ask.** KERNEL: `Receive.rederive : World → Turn → Except Refusal Unit` with the theorem
`rederive w t = .ok () ↔ ∃ call, decode t.event = some call ∧ receive w call = .ok t`. HOST: `follow`
uses it. The `audit` row's plant is exactly this ("follow folds without re-running the receiver").
**Critique.** It doubles the follower's CPU (receive + admit per Turn) and makes LANG's programs part of
replay (determinism of every installed law becomes a replay obligation — it already is, for consent).
**Meta-critique.** I take minidregg's audit as the spec; nanodregg could instead make receivers
themselves logged-and-checked-by-construction, but I see no way without signatures over Turns.
**Status.** ruled by ROOT 2026-10-16: ACCEPTED; KERNEL told (Receive.rederive).

## PROTOCOL-5 · rows are Lean data, not scripts or Markdown (2026-10-16)
**Decision.** `Protocol/Rows.lean`: each row = actor, argv, expected outcome by refusal NAME, the ops and
kinds it reaches, its plant and the verdict the plant must produce. A runner (next: `rows run NAME`,
driving `nd` against a fresh deployment) executes them; the reach table and the size ratchet read the
same data.
**Alternatives.** minidregg's shell/Python drivers (~150 scripts, reach knowable only by scanning their
text — DELETE-PROTOCOL's whole method); Markdown specs beside a runner (two shapes of each row).
**Why.** One shape, checked by the build: the deletion rule is a theorem over it.
**Critique.** A row's `ops`/`kinds` are DECLARED, not observed; a row can claim an op it never drives.
The runner must record the ops each command actually sent (the supervisor sees every frame) and refuse a
row whose observed ops differ from its declared ones — until then the theorem is over a claim (vacuity
by declaration). Refusal names are strings until KERNEL's `Refusal`/`Reject` and LANG's program names
are committed; then a gate resolves each.
**Meta-critique.** Data rows feel rigorous; the hard part — a runner that makes them executable — is not
written, and I chose the part I could prove.
**Status.** open.

## PROTOCOL-6 · the client bounds live in the protocol table (2026-10-16)
**Decision.** frameBytesMax 262144, argvBytesMax 65536, stepsPerCommandMax 64, sendsMax 8, in
`Protocol.Bounds` (ROOT: the client's list belongs in the table). `argv_fits_frame` proved.
**Critique.** `Kernel.Bounds` is "one table"; these are a second bounds namespace. They bound the wire,
not a Turn, and `submit`'s payload (a call, which becomes the Turn's `event`) must satisfy BOTH
`frameBytesMax` and `Kernel.Bounds.eventBytesMax` (65536 today): the theorem
`eventBytesMax + 1 ≤ frameBytesMax` is owed as soon as Kernel/Bounds is importable from a committed tree.
262144 is minidregg's frame headroom, not a derivation. **Meta-critique.** Numbers copied from
minidregg are exactly law 11's worry; each should be derived from the largest row payload.
**Status.** open.

## PROTOCOL-7 · laws attacked (2026-10-16)
- **Law 11 "no twins of minidregg"** vs rows: a conformance row MUST restate minidregg's journey; that
  is the spec, not a twin. Restated per row with what it no longer checks (codec child, host pin, socket
  filters).
- **Law 6 "every theorem statement read by a second agent"**: my four theorems are small; the vacuity
  risk is PROTOCOL-2/5 (declared reach). Asking ROOT to assign the reader.
- **Charter's "target ≤ 40 ops"** is the wrong ratchet unit: minidregg's mass was in call kinds and CLI
  verbs, not opcodes. The ratchet should count (ops, call kinds, command verbs, refusal constructors).
**Status.** ruled by ROOT 2026-10-16: the ≤40-ops ceiling becomes four ratchet rows in SIZE.md (ops,
call kinds, command verbs, refusal constructors); law 11 gets the carve-out: conformance rows RESTATE
the minidregg journeys because the journeys are the spec.

## PROTOCOL-8 · connectionsMax = 64 (2026-10-16)
**Decision.** `Protocol.Bounds.connectionsMax := 64`: the connections one `nd-supervise` holds open at
once, per socket. With one buffered frame per connection per direction the mux holds ≤ 2·64·256 KiB =
32 MiB (`mux_buffers_bounded`). Past the bound the supervisor stops accepting (back-pressure, no queue).
**Alternatives.** Unbounded accept (minidregg's `mini serve`); one per member key (needs the supervisor to
know keys: it parses nothing, so no); a much larger bound for public ingress.
**Why.** A deployment is friends plus their agents and followers; 64 is generous for that and makes the
memory bound a theorem.
**Critique.** A hosted operator serving many grains, or a BAR load generator with many concurrent clients,
could hit 64 and see refused connects that look like an outage; a slow-loris peer holds a slot (the
supervisor needs a per-connection idle deadline, CLIENT's). 64 is a chosen number, not derived from a row.
**Meta-critique.** The number was picked to make the 32 MiB theorem round; the bound that matters may be
file descriptors or the Lean child's queue, not supervisor memory.
**Status.** open.

## PROTOCOL-9 · review of CODEC-8 (f81e093: the follow payloads as layout data), landed CROSS-LAYER in Protocol/ (2026-10-16)
**Verdict.** ACCEPTED: Protocol/Table.lean's `Step.layout`/`commandLayout`/`resumeLayout`,
Protocol/Frames.lean and Protocol/Proofs/Frames.lean are PROTOCOL's files from now on, and PROTOCOL
maintains them. Making every field self-delimiting is the right call: "k = the rest of the payload"
was not a prefix codec, and with it gone `Step.frame_lawful` falls out of the combinator theorems
with no new proof. The Table importing `Codec.Layout` (data) is the right dependency direction.
**Findings, each with an owner.**
1. *A `host` step's `op` is a raw byte* (CODEC-8's own critique, and it is a safety hole, not a
   nicety): a follow that emits `host(op = submit, …)` gets a call sent to host.sock OUTSIDE the
   attempt store, so a lost reply could be answered by a fresh signature: the double-submit class
   CLIENT-3 exists to prevent. The relayable ops are exactly `lookup`, `read`, `log`. Asked of CODEC:
   a field kind `oneOf (name) (codes : List UInt8)` (a byte refused as `badTag` unless listed), so
   `Step.layout host = [.oneOf "op" relayable, …]` is checked by the Lean codec AND the emitted Rust
   reader. PROTOCOL supplies `Op.relayable` in the table.
2. *`argvBytesMax` is no longer enforced as a total.* `.list "argv"` bounds the item COUNT and each
   item by 65536, so a 200 KiB argv of small items decodes; client/src/wire.rs checked the total and
   is about to be deleted. Owner: PROTOCOL. `Command.parse` refuses `argvPastBound` on the total, in
   Lean, where the decision belongs (law 2); the Rust encoder needs no copy.
3. *`Codec.Shape` lost `DecidableEq`* (the nested `List (UInt8 × Shape)` defeats the deriving).
   Nothing compares shapes today; if a gate ever detects "the accepted set changed" by comparing
   shapes it needs a hand instance. CODEC's to keep in mind; no action now.
**Critique.** Accepting a change into my layer that I did not write, without re-deriving the Rust
reader's byte-for-byte claim, trusts CODEC's scratch `cargo test`; the emitted reader has no
differential against the Lean codec in the tree. **Meta-critique.** I was at ceiling when it landed,
so the review happened after the fact; "accept, with findings" is the cheap verdict to give a
landed change, and finding 1 would have been a reason to hold it.
**Status.** open (finding 1 asked of CODEC).

## PROTOCOL-10 · rows/run: the runner is Lean, judging is a pure function, and a row with no driver is PENDING, never PASS (2026-10-16)
**Decision.** `rows/run` = `lake exe rows` (Protocol/Rows/Run.lean). A row is driven one of two ways
(`Row.drive`): `exe NAME ARGS LAST`, a Lean executable of the tree that drives the real receivers in
process (lang-journey, kernel-sim seed 1, host-sim seed 1, by ROOT's ruling), passing on exit 0 and
last line LAST; or `members LINES`, member argv through the one command language. The runner prints
`ROW <name> PASS|FAIL <why>|PENDING <why>` and `ALL PASS` (0) / `FAIL n of m` (1) /
`INCOMPLETE n pending` (3); standing.sh maps 3 to INCOMPLETE. `Protocol.Rows.Judge.judge` decides;
`judge_members_pass_iff`: a member row passes iff every line got its declared outcome AND the
operations seen on the wire are exactly the declared ones, so the day a member driver reports ops,
`every_op_has_a_row` is over observations, not claims. Children run under a deadline (300 s, polled
every 50 ms) and are killed through the handle the runner holds (the process it started).
**Alternatives.** (a) A Rust harness under client/tests (my predecessor's lean): it moves processes,
which is Rust's job, but the verdict would then be Rust's, against law 2. (b) A shell runner reading
a JSON emitted from Rows.lean: a second reader of the row data. (c) Count PENDING rows as RED: the
standing line would be red until HOST-2 lands, and red-as-steady-state hides every new red.
**Why.** One reader of the data (Lean), one judge (a pure function with its iff), and an honest third
state between pass and fail.
**Critique.** The exe rows are judged by one line their own authors print: `ALL PASS` is a claim
made by the executable about itself, and a sim that prints it unconditionally passes. Each exe's
plant is internal to it, so this runner cannot see whether the plant ran. kernel-sim and host-sim are
now judged twice, by the sim stage (seeds 1 2 3) and here (seed 1): two judges of one thing (law 1);
they are rows only because ROOT ruled so, and the cost is 2 s. **Meta-critique.** I built the
part that is green today (exe rows) first and left eleven member rows PENDING behind a driver I have
not written; PENDING is honest only while the member driver is the very next commit.
**Status.** open.
**Ruled by ROOT 2026-10-16:** judge theorems accepted; the pushback WINS: kernel-sim and host-sim are
not rows (standing's sim stage is their one judge); the "call kinds" metric counts `Receive.Body`
(10) with ceiling 10. PROTOCOL-9 findings 1 (oneOf, CODEC told) and 2 (argv total in Command.parse)
endorsed.

## PROTOCOL-11 · Protocol.Command: eleven verbs, one parser, a five-phase machine that re-derives at every step (2026-10-16)
**Decision.** `Protocol/Command/Verb.lean`: `Verb` (init enroll follow install create write law
invoke grant revoke read; 11 against a ceiling of 20, `Verb.at_most_twenty`), `Cmd`, and THE parser
`parse : List ByteArray → Except ParseRefusal (Cmd D)` (the argv total refused as `argvPastBound`,
`parse_past_bound`; every other refusal by name). `Protocol/Command/Machine.lean`: `start`/`step` over
`k = (argv, phase, acc)`. A write: sign(envelope) → host(log, envelope) → absorb (every logged event
re-derived by `Receive.submit` on follow's World, a failure is `eventMismatch h`) → `plan` → sign
(unsignedBytes u) → re-plan and compare bytes (`planMoved`) → submit(callBytes) → done(receipt). `read`
stops after the catch-up; `init` signs twice and prints a join token. `plan` discovers pins by
deriving and adding each `unpinned` cell (≤ touchesMax), prices at the derived charge + 4096, and
returns `u` only if follow's own `World.admit` accepts the Turn. Theorems: `plan_admits` and
`step_submit_planned` (consent: the only call `step` ever hands the client to submit is
`callBytes ⟨u, sig⟩` for a `u` that `plan` produced on follow's World, hence derived and admitted
there). Custody's sign result is `signResultLayout` = key, NEXT key, signature (the next key's
digest is what a sponsor/rotation commits to). Ids are hex; petnames are not in the language.
**Alternatives.** (a) Follow keeps per-command state server-side (then a follow restart loses
commands, and `k` would need a MAC). (b) A fixed generated step sequence per verb (HOST-9's critique):
the catch-up length depends on the log, so the sequence is data-dependent. (c) Petnames in the World
(an index nobody else needs) or in follow (state outside the World).
**Critique.** Signing an envelope costs one more custody round trip per command, on THE BAR path.
`maxCharge` = charge + 4096 is a ceiling the member signs without seeing; a Host that charges up to
it is within the signature. The rotate and retry verbs are absent: rotation needs custody to sign
with the NEXT key and then advance (a custody step CLIENT has not designed), and retry is the
attempt store's (Rust) — both rows stay PENDING. Refusal names come from derived `Repr` (`ctorName`),
which is exact for constructors but would silently change if someone hand-wrote a `Repr`.
**Meta-critique.** I proved the consent property at `plan` and `step` because those proofs were
reachable; the stronger statement (the Host derives the SAME Turn from the signed call) needs the
signature-independence of `dispatch`, which I did not attempt.
**Status.** open.

## PROTOCOL-12 · the READ ENVELOPE (HOST-11's gate as data) and Bounds.idleMsMax (2026-10-16)
**Decision.** `envelopeLayout` (member, grant, from, validUntil, key, signature; digests as
`Env.bytes`, heights u64le) in Protocol/Table.lean, `envelopeFrame` + `envelopeFrame_lawful` in
Frames, and `Protocol.Envelope.check` (Protocol/Envelope.lean): current key of a live member
(`unknownKey`), signature over `Envelope.message` (`badSignature`), `height ≤ validUntil`
(`expired`), `mayFollow` (`noFollowGrant`); undecodable is `badEnvelope`. `logReplyLayout` = the
signed calls from the height: a follower re-derives every Turn (PROTOCOL-4), so the log serves events,
not Turns. `idleMsMax = 300000` for remote connections (CLIENT-12's ask; PROTOCOL-8 named it).
**Critique.** Heights as `.bytes` holding u64le are untyped fields (a `u64` field kind would let the
codec refuse a 7-byte height); a stranger and a revoked member are told apart (`unknownKey` vs
`noFollowGrant`), which leaks membership to anyone who can reach host.sock; a reply larger than a
frame is HOST's to split. **Meta-critique.** "Serve events, not Turns" is the cheaper wire and it
makes the follower's CPU the audit; I chose it partly because there is no Turn codec yet.
**Status.** open.

## PROTOCOL-13 · ROOT rulings: `read` is RESERVED; each owner names its refusals with `name_injective` (2026-10-16)
**Decision.** (1) `Op.reserved` (Protocol/Table.lean) marks `read` as a declared absence tied to
Ember's thin-consent ruling (HOST-7a). If thin members are out, `read` is deleted (6 → 5); if they are
in, a thin-member row sends it. No row declares `read` any more. `every_op_has_a_row` ranges over
non-reserved ops, and `no_row_claims_reserved` says no row claims a reserved op, so the theorem
states what is true today. (2) The derived Repr is not a wire name. PROTOCOL names its own:
`ReadRefusal.name` (`name_injective`, as values), `ParseRefusal.name` (`name_injective`: equal names ⇒
the same constructor tag), and `Command.Refusal.name`'s own arms. The `receive`/`reject` arms still
go through `ctorName` until KERNEL's `Receive.Refusal.name`/`Reject.name` land; those two arms are
then replaced. Also `Envelope.check_ok_iff`.
**Critique.** `name_injective` up to the tag says nothing about arguments: two `eventMismatch` at
different heights render alike on the wire, which is a choice (names, not values) that the row
judge relies on. **Meta-critique.** Reserving an op instead of deleting it keeps a dead entry
alive for a ruling that may take weeks; the reservation is honest only while the ruling is open.
**Status.** ruled by ROOT 2026-10-16.

## PROTOCOL-14 · thin consent: what a member that cannot fold the whole log verifies (2026-10-16, DRAFT with HOST-3; Ember ruled thin IN "if we can get away with it")
**What exists to verify against (read, not assumed).** The World commits to its log by `chain` (one
digest per height, `chainNext`); it commits to its CELLS by nothing: there is no state root. CODEC-14's
`world dc` gives a canonical byte string for a whole World, so a whole World has a digest; a single
cell has no inclusion proof against anything.
**Option A — ONE code path: `host follow` folding from a verified BASE instead of genesis.** `read`
serves a base: the World codec bytes at a height `h` with the writer's chain at `h` (paged; HOST-14's
base IS this). The thin member accepts the base only if `H(world bytes)` equals a base digest it
already trusts — one it folded itself earlier, or one a FULL follower it trusts countersigned out of
band (a friend's `host follow`). From there it runs the same `absorb` (re-derive every event, PROTOCOL-4)
over the suffix, and the same `absorbPage` chain assertion. Verifies: every transition after the base
(full consent from `h` on), the chain from `h`. Trusts: the base's transitions (whoever attested the
digest). Cannot detect: a withheld-but-valid suffix (the writer serves height `h' < tip`: consistent,
just stale — a thin member that never talks to another follower cannot tell), and anything before the
base. Cost: O(World) bytes once per base, O(suffix) per sync; no new verifier, no proof format.
Plant: a base whose bytes do not hash to the trusted digest is refused `baseMismatch`; a forged CELL in
the served base is exactly that (the "forged inclusion" of ROOT's ask).
**Option B — a SECOND code path: per-cell inclusion against a state root.** KERNEL keeps an
authenticated map over cells (a Merkle trie, O(log n) per touched cell, law 4 holds), the Turn or the
chain commits its root, CODEC defines a path format, and the thin member verifies `(cell, path, root,
chain)` without folding. Verifies: that the cell is in the state the chain names. Trusts: every
transition (it re-derives nothing: a forged write by the writer is invisible) — genuinely "thin".
Cannot detect: forged transitions, withheld suffixes. Cost: a root update on every admitted Turn on
THE BAR path, a second verifier (law 1's "one admission path" is not broken, but "one consent path"
is), a proof format CODEC must make canonical.
**Proposed.** A for v0: it is the same function a full follower runs, from a later start, so it costs
the code that exists plus a base op; `read` comes off the reserved list as "serve the base at a height"
(envelope-gated, PROTOCOL-3) and row `thin` ships with the `baseMismatch` plant. B is a declared absence
until a row needs O(log n) single-cell reads (a phone that cannot hold the World).
**Critique.** A does not fit a phone if the World is large: "thin" in A is thin in TIME (no fold of the
prefix) not in SPACE (the whole World is held). If Ember's phone means "cannot hold the World", A
does not answer it and B is required. The trusted base digest is a new trust input with no channel:
who countersigns, and how a member learns it, is a custody/identity question (pause list item 1).
**Meta-critique.** I prefer A because it keeps one consent path, which is the law I can cite; B is the
design the word "thin" usually means, and I may be redefining the requirement to fit the code.
**Status.** ruled by ROOT 2026-10-16: build A for v0 (HOST-3 agreed: `read` serves the World part
of HOST-14's base, `Codec.Deployed.world` bytes, digest `Hash.digest "nanodregg/host/base/v1"`, paged
`(height, total, digest, bytes[start, start+chunk))` with the envelope's `start` read as a byte
offset; HOST-15 holds the layout and PROTOCOL proposes it in Protocol.Table). B (thin in SPACE: the
phone that cannot hold the World) and the trusted-digest channel (who countersigns a base digest) go
to Ember as the "phone" question; B stays unbuilt. Row `thin` ships with `read` unreserved and the
`baseMismatch` plant.

## PROTOCOL-15 · the member rows run in process against HOST's loop; plants are mutations of the parameters, judged by line and outcome (2026-10-16)
**Decision.** `Protocol/Rows/Loopback.lean` runs every member row against a fresh writer
(`Protocol/Rows/Writer.lean`: `Host.serve` itself, on a dedicated thread, over the in-memory segment
and base, reopened by `Host.openWith`) and per actor an in-process client: follow's machine on the
actor's own World, custody (toy keys by generation; precommit/signNext; advance only on its own
settlement of the armed attempt), the attempt store (a lost reply is settled by `lookup` of the same
bytes, never re-signed). Every step crosses the wire codecs (`commandFrame`, `Reply.bytes`/`ofBytes`,
`resumeFrame`) and the call codec is CODEC's (`Codec.Kernel`, `Stream.u64` digest). The driver
records every op it sends and the receiver kind of every call it freezes; the judge requires both
to equal the row's declared ones (`judge_members_pass_iff`, now with kinds). A passing row is run
again under its plant (`Mutation`: openLog, skipJudge, followVerifyAll, forgetJournal, resendFresh,
zeroDeadline, advanceOnSend), and must be caught: the lines before the plant's line keep their
outcomes and that line gets the planted outcome (`caught`; `plants_differ` says that outcome is
never the declared one). A row whose system piece does not exist is PENDING by name (`blockedOn`,
with its owner), never PASS, never a red that hides the others.
**Alternatives.** (a) Wait for HOST-3's exe and CLIENT's nd and run rows over sockets only.
(b) Plants as patched source trees (minidregg's scripts/plants). (c) Rows blocked on missing
packages as FAIL.
**Why.** (a) leaves the whole spec unexecuted for another day, and the socket run adds transport,
not decisions: every decision is in the Lean this driver runs. (b) costs a build per plant; a
mutation of the parameters (Ctx, the writer's gate, custody's rule) is the same pipeline with one
part swapped, and the plant check is a pure function. (c) makes standing RED for absences, and
red-as-steady-state hides the next real red.
**Critique.** The driver IS a second client: its custody and attempt store restate CLIENT's rules
in Lean (a twin of Rust policy; law 2 says those rules belong in Lean anyway, so the honest end is
CLIENT driving a Lean attempt-store decision, not two). The `log` arm is not HOST's yet (Writer
documents it and deletes it when HOST-3 lands). Plants mutate what the driver can reach: a receiver
mutation (KERNEL's dispatch) is out of reach, so "the receiver skips the grant check" is not a
plant here; kernel-sim owns that class. Timings are in-process: no socket, no ssh, no fsync.
**Meta-critique.** Everything went green on the first full run but four plant targets: I wrote the
rows and the driver in one pass, so they can share a misconception (they did twice: a plant line
index off by one, and custody arming the wrong attempt); the kinds check found two rows declaring
less than they drove.
**Status.** open.

## PROTOCOL-16 · KERNEL-20: the verb `follow` is DELETED; `grant world MEMBER observe --via G` says it (2026-10-16)
**Decision.** With one grant kind and the World a grant target, "let MEMBER follow" is `grant` of
`observe` on the World, attenuated from the signer's World grant. The command language says exactly
that: `grant TARGET MEMBER RIGHTS [--via PARENT]`, TARGET an object or `world`; `enroll:N` is a right;
`enroll TOKEN` spends the signer's World grant (`me.grant`). Verbs 12 → 11 (rotate added).
**Alternatives.** Keep `follow MEMBER` as sugar for the same Body.
**Why.** Sugar adds no code path but a second spelling of one call; a row or a member reading
`follow` then has to know it is a grant, and `grant` could not otherwise name the World or a parent
at all (its parent was hard-wired `none`, so attenuation was unreachable from the language).
**Critique.** `--via @me.grant` is boilerplate on every follow grant; members must know their own
World grant's id (they do: it was bound when they were granted). **Meta-critique.** Deleting a verb
lowers a SIZE count, which I am rewarded for; the test is whether any row reads worse, and none does.
**Status.** open.

**PROTOCOL-15 ruling (ROOT 2026-10-16).** PENDING-by-name (`blockedOn`) ACCEPTED: never PASS, never
RED; standing stays INCOMPLETE while any row is blocked. pay/well/bounty: packages are LANG's, the
receivers they need (nullifiers/spent, accounts, wells) are a new LEDGER layer; blocked on both.
WASTE: print `invoke ticks-per-call` (CEK ticks, exact by run_exact/run_minimal) and
`invoke packages-checked-per-call` (LANG-16's closure size); pin both once the bar row has an invoke.

## PROTOCOL-17 · the attempt-store decision is a Lean function nd calls (2026-10-16, ROOT: open)
**Decision.** After a submit's reply (or its absence), "resubmit the same bytes vs lookup vs done"
is a decision (law 2), so it is a Lean function (`Protocol.Attempt.next : State → Settlement →
Action`, with the theorem that it never asks for a second signature for one frozen call), which
CLIENT's nd calls through the generated table or follow, and which the loopback calls too, instead
of restating CLIENT-3's Rust rule. **Critique.** It moves a step across the follow socket per
settlement, or needs a Lean runtime in nd. **Meta-critique.** I found this because my loopback had
to restate it; a twin I wrote is the evidence. **Status.** open; CLIENT-3 implements when spawned.
**Built (2026-10-17, PROTOCOL-4).** `Protocol/Attempt.lean`: `next (sendsLeft : Bool) (last :
Option (Request × Seen)) : Action` over `Seen` = committed | refused | unknown | absent | lost (no
reply: a dropped connection, a crash, `replyMsMax`) and `Action` = submit | lookup | committed |
refused | absent | badReply | uncertain. Never sent ⇒ submit; committed/refused ⇒ over; a submit
unknown or lost ⇒ lookup (never a second submit: the first may still be queued); a lookup absent ⇒
submit while sends remain, else over `absent`; absent to a submit ⇒ `badReply`; a lookup unknown or
lost ⇒ the run ends `uncertain`, the attempt unsettled on disk for the next run (CLIENT-2's
objection: an unbounded lookup loop; `next_after_lookup` bounds a run at two requests per send). `Attempt.table` is the
decision as 22 rows of data for CODEC to emit; `table_complete` + `inputs_nodup` say the table IS
the function. Theorems: `next_submit` (a submit only for a never-sent call or after a lookup said
absent with a send left), `next_after_unknown`, `next_committed`, `next_no_send_left`. The rows'
attempt store (`Loopback.drive`) now runs `next` for every request; `neverForward` drops every
submit, so the rotation that never reached the writer ends `absent` after `sendsMax` sends.
**Critique of the built shape.** `absent` is not final: a lookup cannot tell "not yet" from "never"
until the Host answers a dead call (past its `validUntil`, not journaled) as refused `expired`,
which needs KERNEL's `absent_final` (HOST-8's ask, routed through ROOT). Until then a call dead by
window is resent up to `sendsMax` times and ends `absent`, not `expired`. `sendsLeft` is computed
by the client (`sends < Bounds.sendsMax`): a comparison, not a decision, but it is Rust.

## PROTOCOL-20 · `Bounds.replyMsMax` = 120000: the client's per-request reply deadline (2026-10-17, ROOT's ask for CLIENT-2)
**Decision.** One request (a frame on either socket) waits at most `replyMsMax` for its reply; past
it the client reports `timeout` by name, and a request carrying a frozen call is `Attempt.Seen.lost`
(uncertain: the attempt goes on by lookup), never refused. 120 s: above a writer's worst
legitimate wait (an inline seal before an append, plus a supervisor restart whose cold reopen THE
BAR bounds at 60 s) and below `idleMsMax` (`Bounds.reply_within_idle`), so the supervisor never
closes a connection a client still waits on.
**Alternatives.** A per-op deadline (submit longer than lookup); no deadline (the hang ROOT found);
the BAR's 5 s (a correct writer mid-seal would read as dead).
**Critique.** One number for both sockets: a follow step that absorbs a full page of events (each
re-derived, LANG laws included) or hashes a 256 MiB base on its last adopt page may legitimately
take seconds; 120 s covers it, but nothing measures it. A timeout that fires on a slow but alive
writer only costs a lookup. **Meta-critique.** The number is the BAR's 60 s doubled, not measured.
**Status.** open.

## PROTOCOL-21 · custody results are `status ‖ payload` with named refusals (2026-10-17, CLIENT-2's ask)
**Decision.** Every step result is `u8 status ‖ payload`: the Host's for `host`/`submit`; custody's
for `sign`/`signNext`/`precommit` is `ok ‖ signResultLayout|precommitResultLayout` or `refused ‖
custodyRefusalLayout` (one `oneOf` byte of `CustodyRefusal`: fileRefused exists shape holdingAbsent
noPending rotationInFlight mismatch io — CLIENT-2's CustodyError, its `Mismatch` detail dropped).
Follow unwraps it at every custody phase (`custodyPhase`, `custodyResult`) and ends the command
`refused NAME`; an undecodable custody result is `badResult`. `CustodyRefusal.name_injective`,
`code_injective`, `custodyRefusalFrame_lawful`. client/src/run.rs prefixes `status::OK` to custody's
answer (`Outcome::result`); CLIENT-2 maps its errors to the refused form once CODEC emits the codes.
**Alternatives.** Refusal names as UTF-8 (the Host's form): an open set, so a typo is a new name.
**Critique.** `mismatch`'s detail (which key disagreed) is lost on the wire; it stays in nd's
stderr. No row drives a custody refusal yet (the loopback's custody never refuses).
**Meta-critique.** The set is CLIENT's enum read today; a custody refusal CLIENT adds later needs
a table row here first, which is the point.
**Status.** open.


## PROTOCOL-18 · thin consent BUILT (option A): `adopt HEIGHT DIGEST`, `Protocol.Thin.accept`, follow's state holds the download (2026-10-16)
**Decision.** `read` is unreserved (and `Op.reserved` deleted: a function that is always false is a
no-op kept for compatibility). A thin member runs `nd adopt HEIGHT DIGEST`: follow pages the
writer's newest base with `read` (one signed envelope per page, `start` = byte offset,
`validUntil` = HEIGHT + window), and `Protocol.Thin.accept` decides each page: the stated height
must be the pin's (`baseMoved`), the stated digest the pin's (`baseMismatch`), each page must
continue the download (`pageMismatch`), and the assembled bytes must hash to the pin BEFORE they
are decoded, then decode to a World at the pin's height (`baseMismatch`/`baseUndecodable`).
`accept_done`: an adopted World's canonical bytes hash to the pin, at the pin's height, whatever the
pages stated. The partial download cannot live in `k` (bounded by a frame) so it lives in follow's
state: the machine's state is `Follow D = { world, download }` and a step returns `Persist D`
(`turns ts` | `adopt w`), so `host follow` appends Turns or seals its own base from the adopted
World before it answers (Host/Follow.lean, with HOST-3). The digest is the writer's
`Keys.worldDigest` (a `Thin.Base` parameter: deployed cSHAKE256 "nanodregg/host/base/v1", the Sim's
a toy). Row `thin`: the full follower catches up, the operator seals at the tip, the follower
attests its own World's pin (`Act.attest`: the out-of-band channel, Ember's, as a row act), the thin
member adopts, re-derives the suffix, writes, reads; a member with the pin after a newer seal is
`baseMoved`. Plant `forgeBase` (one World byte flipped, honest digest stated) caught at the adopt
line: `baseMismatch`. The rows now drive `Host.Follow.answer` itself (one code path).
**Alternatives.** The download in `k` (impossible past one frame); the download in the client
(Rust would decide when the bytes are complete: law 2); adopt as a `host follow` start flag (follow
cannot reach custody to sign envelopes except through steps).
**Critique.** Thin in TIME only (PROTOCOL-14): the whole World is held. A pin is stale after the
next seal, so a thin member must get a fresh pin per cadence, from a channel that does not exist.
A download costs one custody signature per page: `pagesPerCommandMax` 28 pages ≈ 7 MiB per
command, so a large base takes several `adopt` runs (`incomplete`, kept in memory). The download is
lost on a follow restart. **Meta-critique.** The attest act makes the row green by giving the thin
member a pin from a process the row controls; the trust question (who countersigns) is untouched.
**Status.** open.

## PROTOCOL-19 · log paging; a defect found: `expired` makes a cold catch-up impossible (2026-10-16)
**Decision.** `logReplyLayout` carries `tip`; follow pages from each page's height until it reaches
it, at most `pagesPerCommandMax` (28) pages a command, else `behind` (absorbed kept; run again);
an empty page short of the tip is `badResult`. Row `paging`, plant `lieTip`.
**Defect (open, to fix next).** `Envelope.check` refuses `expired` when the WRITER's height is past
the envelope's `validUntil`, and follow can only sign `validUntil` = (its own height) + window. A
member more than a window behind the tip (a cold follower; a thin member whose pin is older than a
window) is refused on its first page and never learns the tip. The rows never see it (heights stay
under 128). Proposed fix: check the signature and the follow grant BEFORE expiry, and let the
`expired` refusal carry the writer's height, so an authenticated member re-signs once with
`validUntil` = that height + window; a replayer of a captured envelope learns only a height.
**Critique.** A refusal carrying a number is a new wire shape (names only, so far). **Meta-critique.**
I found it by reasoning, not by a row; the row that would show it needs a log past 128 heights.
**Status.** envelope half BUILT (PROTOCOL-5, 2026-10-17), below.

**Built (2026-10-17, PROTOCOL-5; the envelope half, the Host arm agreed with HOST-5).**
`Envelope.check` = key, signature, follow grant, THEN expiry; `ReadRefusal.expired (height)` states
the World's height, and `Envelope.check_expired_authenticated` says it reaches only the current key
of a live member that signed the envelope and whose follow grant is live (a stranger, a forger, a
revoked member learn nothing). Wire: `expiredRefusalLayout` = [.bytes "refusal" ("expired"),
.u64 "height"] as the `refused` payload (`ReadRefusal.payload`; every other refusal stays its UTF-8
name); `expiredHeight?` reads it back (`expiredHeight?_payload`, canonical: `expiredHeight?_eq_some`),
and no name is mistaken for it (`expiredHeight?_of_head`: a payload whose first byte is not 7 states
no height; `expiredHeight?_name` for ReadRefusal's own names; HOST-5's ask). Host/Serve renders
`r.payload` for `log` and `read` (two arms, CROSS-LAYER). Follow: the first envelope covers its own
height + window, every later page's envelope the TIP the previous page stated + window, and an
`expired` is re-signed ONCE a command for the stated height + window (`Command.reSign`:
`reSign_tried`, `reSign_ok`; a stated height the refused envelope already covered, or a second
`expired`, ends the command `refused expired`). `adopt` does the same from the pin's height. Row
`coldCatchUp`: 210 writes (window 100), a follower cold from genesis reads at the tip; plant
`unstatedExpiry` (the writer states the name alone, the old shape) caught at line 10: `refused expired`.
**Alternatives.** Drop expiry for authenticated readers (a captured envelope at the tip page then
reads every new event until revocation); sign `validUntil` relative to `start` (the same question:
the member does not know how far the tip is); a status `retryAt` (a second refusal vocabulary).
**Critique of the built shape.** The stated height is the writer's word, unauthenticated: an active
man in the middle on the member's path can inflate it and so obtain an envelope valid until a far
height (replayable, for that member's reads only, until its grant is revoked or its key rotated;
`mayFollow` and the key are checked BEFORE expiry, so revocation still ends it). A member cannot
bound the jump without knowing the tip. No row drives a thin member whose pin is older than a
window (the adopt arm is the same `reSign`, but unexercised). **Meta-critique.** "One retry" is
the ruling's word; I chose per COMMAND, not per page, because tip-based envelopes make every later
page fresh, so a per-page retry would only buy signatures for a writer that outruns a window inside
one command. The plant tests the HEIGHT on the wire, not the check ORDER: a writer that checks
expiry first would still state the height (and leak it to strangers) and the row stays green; the
order is held by `check_expired_authenticated`, a theorem, not by a row.

## PROTOCOL-22 · every connection close is named: `Status.closed` + `CloseReason`; the idle rule waits for nothing in flight (2026-10-17, BUILD-TRANSPORT; ASSEMBLY-transport-consent D5, scout T2)
**Decision.** The supervisor's mux (and `nd-attach`, the box end of a friend's ssh channel) ends a
connection only for a reason in `CloseReason` (idle, frameStalled, frameRefused, replyBacklog,
replyWriteFailed, replyTimeout, full, ended, unreachable), and tells the peer with one last frame
`Status.closed (4) ‖ name` before shutting the stream. `idleMsMax` is redefined: silent AT A FRAME
BOUNDARY with NO request in flight (the old "no frame in either direction" closed a client waiting
on a slow reply: T2 measured it). New bounds: `frameMsMax` 30 s (a started frame), `replyWriteMsMax`
30 s (one write to the peer), `peerConnectionsMax` 8 (one `nd-attach` process = one ssh session),
and `replyMsMax` (PROTOCOL-20) doubles as the mux's backstop for a request with no reply
(`replyTimeout`), because the in-flight counter relies on a Loop-level "one reply per request, with
its conn, including `uncertain`" that is owed (HOST), not proved (`Machine.replies_size` covers
the batch only). All of it is emitted (`emit-rust`: the bounds, `status::CLOSED`, `CloseReason` with
`name()`), never hand-copied. A `closed` is never a verdict on a request: the attempt store reads
it as a lost reply (`Attempt.Seen.lost` ⇒ lookup), follow's settlement refuses it `badResult`
(a client settles a closed connection by lookup before it resumes follow), and the rows render it
`uncertain`. Theorems: `CloseReason.name_injective`, `CloseReason.mem_all`,
`Bounds.peer_below_connections`, `Bounds.frame_within_idle`.
**Alternatives.** (a) Close silently and log the reason on stderr (law 7 fails for the peer).
(b) Keep `idleMsMax` as "no bytes either way": refuted by T2's slow-reply test. (c) A close code
per reason instead of a name payload: the payload convention for refusals is the NAME (PROTOCOL-2),
and one status byte with a named payload keeps `Status` small.
**Critique.** The mux now ORIGINATES a frame and decides WHEN to close: the vocabulary and the
numbers are Lean's, the timing judgement is Rust's, a stretch of law 2 that exists only because the
Lean child cannot see time. The close frame is best effort and can race a reply the child already
sent; the client's answer is lookup. `replyBacklog` closes a pipelining client (nd is sequential;
nothing enforces it). None of the three new deadlines has been measured over a real sshd on a slow
link; a healthy friend on a bad WAN may hit `replyWriteFailed`. `peerConnectionsMax` is per ssh
session: a friend with several sessions has several caps (only sshd's MaxSessions binds across).
**Meta-critique.** I accepted T2's fix because the head-of-line block is readable in `route`, not
because of a measurement on a deployed box; the numbers (30 s, 8) are round guesses I priced from
`frameBytesMax` and the friend count, and the vocabulary has two `nd-attach`-only names (`ended`,
`unreachable`) that I added while writing it rather than from a row that needs them.
**Status.** landed (vocabulary); the mux and `nd-attach` land under `client:`.

## PROTOCOL-23 · the child wire's hang-up: the supervisor tells its child a connection ended, and the child acknowledges it by name (2026-10-17, BUILD-TRANSPORT; shape by PROTOCOL-5, ROOT's ruling)
**Decision.** Toward a supervisor's child, a frame's byte after the connection id is an `Op.code`
(a request) or `hangupCode` = 255 (connection `conn` ended; payload = its `CloseReason` name, the
same name-as-payload convention as PROTOCOL-22's `closed`). `ChildKind` / `childKindOf?` decode it;
a hang-up is NOT an `Op` (it has no receiver in the op table, so `every_op_has_a_row` and receiver
uniqueness stay non-vacuous). The child answers it `Status.closed ‖ the same name` (`ack`;
`ackReason?_ack`). New reason `peerLeft`: the client ended its stream (an end with no name was a
law-7 defect). The supervisor sends a hang-up for every connection it ends (except one the child
itself closed); `nd-attach` releases the upstream connection and its per-session slot on it.
Theorems: `hangup_not_op`, `childKindOf?_hangup`, `childKindOf?_op`, `ackReason?_ack`,
`CloseReason.ofBytes?_name` (which rests on `CloseReason.name_injective`, PROTOCOL-22).
No conformance row: the rows do not model the mux; the plants live in host-sim (plant-hangup)
and the mux / attach tests.
**Alternatives.** (a) A reserved `Op` whose receiver is "the wire" (refused: a vacuous receiver,
the kind PROTOCOL-2 removed) plus a `.child` socket (a second shape for one entry). (b) A 4-byte
body (`conn`, no byte) the Host ignores (refused by ROOT: a frame nobody acknowledges by name).
(c) No signal: `nd-attach` leaks a slot per ended connection until the box's idle close.
**Critique (PROTOCOL-5's).** The child learns of the close one frame late; a child that never acks
is bounded by the mux only because the mux has already closed the connection. The ack goes to a
connection that no longer exists, so the supervisor drops it: its value is the theorem and the
plant (the child's dispatch is total over the wire bytes), not a message anyone reads.
**Meta-critique (PROTOCOL-5's).** The hang-up/op split could be read as taste; the reason is that
receiver uniqueness has to stay a non-vacuous theorem.
**Status.** landed.

## PROTOCOL-24 · programmed objects from the command language: `create --pkg PKG STATE`, `invoke` reads ARGS as TEXT; rows grain and THE BAR's invoke (2026-10-17, PROTOCOL-5)
**Decision.** `create --pkg PKG STATE LAW…` births an object programmed by PKG; `invoke OBJ METHOD
ARGS` carries ARGS as TEXT. Neither is read by the parser (which has no World): `Machine.body`
reads them on follow's World when the call is planned, by LANG's readers (`Lang.seedOf`,
`Lang.argsOf`, LANG-22) through `worldLook w` (follow's whole World as a pinned view; the call's
pins are discovered afterwards by `derivePins`). `body` is `Except`: a text that does not read is
`refused` with LANG's `program` reason, an invoke of a data object is the receiver's own `noMethods`,
a missing object `missingCell`. Rows: `grain` now drives the SHIPPED `world/grain/Lifecycle` (a row
argument `<PATH` is the file's text; `{@NAME}` substitutes a binding inside a text) through
create/start/second start/stranger stop/grant-to-start/stop, plant skipJudge @6 → ok (the second
start admitted). THE BAR installs `counter` (method `add`, law `bounded`), creates one, and invokes
`add 1` 64 times within 5 s each (`add 999999` after them is refused `lawDenied`, so the adds
landed). `reqTy`/`verdictTy` are printed from LANG's types (`Lang.Read.showTy`). The rows' page budget
is 16384 (it must hold every event the rows log, HOST's `budget_fits_event` premise; the grain
install broke 4096 as `badResult`), and `paging` writes 100 times to keep paging.
**Alternatives.** Parse-time reading (the parser would need the World: a second reader of it);
args as raw hex (the member signs bytes it cannot read); the package text inlined in Rows from
`Hosting.Text` (tests the generator, not the file a member installs).
**Critique.** `body` reads the package from follow's World, the receiver from the call's pins: a
package not yet in follow's World is `missingCell`/`unpinned` at plan time, the right refusal, but
by a different name than the writer would give. The rows' page budget is a parameter that must
dominate the rows' largest event, and nothing checks that statically. **Meta-critique.** The `<PATH`
and `{@NAME}` substitutions make the rows a little shell; I chose them over a Lean import because the
row should exercise the bytes a member actually pastes.
**Status.** landed. The WASTE lines of THE BAR's invokes wait on KERNEL-5's `invokeRun` (one
derivation of the run's inputs, after KERNEL-25).

## PROTOCOL-25 · THE BAR's invokes are measured, not timed: `WASTE invoke …` pinned; a missed deadline is `hang`, a non-verdict (2026-10-17, PROTOCOL-5; ROOT's correction)
**Decision.** Each invoke a rows client freezes is measured on the World it was planned on:
KERNEL's `invokeRun` (the receiver's own inputs, factored out of `invoke` with KERNEL-5's
agreement, so nothing is restated) then LANG's `runMeasured` (whose first component IS
`Program.run`). The bar row prints `WASTE invoke ticks-per-call 30.000` and `WASTE invoke
packages-checked-per-call 1.000`, pinned in gates/waste.tsv (ceiling = first measurement). The
`withinMs` deadlines are LIVENESS deadlines: a run past one is `Expect.hang`, and a row whose first
differing line hung is `Verdict.hang` (`ROW x HANG … not a verdict`; the runner ends INCOMPLETE,
exit 3), never FAIL and never a PASS on speed (Ember: no wall-clock judgement until the end on a
quiet box; THE BAR's ≤ 5 s is PERF's `scripts/bar.sh`). Plant `zeroDeadline` now expects `hang`.
**Alternatives.** A cost field in the Turn (KERNEL-5: a separate decision); measuring in the
Host (the Host decides nothing and would need LANG's measured run); keeping `overTime` as a refusal
(a speed verdict in a refusal's clothes).
**Critique.** ticks-per-call counts the method's run and extraction, not the laws' ticks (judge
runs under `lawTicks` and is not measured); a law-heavy workload's cost is invisible to this
line. The measure is taken on the actor's follow World, which equals the writer's only when the
actor is caught up (true in the bar row, one actor; not asserted). **Meta-critique.** The number
30 is a property of the counter package, so the ratchet guards the evaluator and the closure
loader against regressions on ONE program; a second workload would make it a measure of the
machine rather than of a fixture.
**Status.** landed.

## PROTOCOL-26 · `grant TARGET anyone RIGHTS`: a public object in the command language (KERNEL-26) (2026-10-17, PROTOCOL-5)
**Decision.** The grantee word `anyone` is the World as grantee (`Cmd.grant`'s grantee `none` ↦
`worldId X` in `body`, as the target word `world` already is): every enrolled member, members
enrolled later included. Row `journey` gains the tooth: the owner grants `anyone` observe,mutate;
a member enrolled AFTER the grant is refused `noGrant` without it and writes through it.
**Alternatives.** `--public` as a flag (a second grammar for one grantee); the World's hex id typed
by the member (a digest nobody can read as "everyone").
**Critique.** `anyone` reads as "any key at all"; it is any ENROLLED member (strangers are still
`unknownKey` at the log), which the verb's docstring says and the word does not. The row tests the
positive path through `write`; the bounty row (invoke by a hunter) still waits on LEDGER's escrow.
**Meta-critique.** I put the tooth in `journey` rather than a new row because no existing mutation
reaches KERNEL's link walk; the row would have had a borrowed plant.
**Status.** landed.

## PROTOCOL-27 · an envelope's life is a window of heights, whatever the writer states: `notBefore`, `notYet`, `wideWindow` (2026-10-17, PROTOCOL-6; PROTOCOL-19's open critique)
**The question.** PROTOCOL-19 lets `expired` state the writer's height, and follow re-signs for that
height + window. Every later page's envelope is likewise signed for the `tip` the previous page
stated + window. Both numbers are the writer's word, unauthenticated, so a man in the middle on the
member's socket can inflate either. Today the envelope signs only `validUntil`, and `check` bounds
it from one side (`w.height ≤ validUntil`). An inflated stated height H therefore buys an envelope
the Host accepts at EVERY height up to H + window: a bearer credential for the member's reads, usable
off the path, long after the member stopped reading, until its grant is revoked or its key rotates.
**Option rejected: take the height from the follower.** The follower's own height is verified, but
the only reason `expired` states a height is that a cold follower (or a thin pin older than a window)
is more than a window behind and CANNOT sign for the tip from what it knows. Signing from its own
height is PROTOCOL-19's defect, back. No verified upper bound on the tip exists at the member.
**Option rejected: "the writer's word is enough".** The arguments for it: the client decides nothing
on the stated height, every reply is unauthenticated anyway, and the MITM already sees every page the
member reads. The first two are true and beside the point. The harm is not a wrong decision, it is a
LONGER-LIVED SIGNATURE the member gives out. The third is only true while the member keeps reading
on that path; the inflated envelope keeps working after it stops. A credential whose lifetime the
attacker chooses is a widened check (CLAUDE.md's short list, item 2), not a cosmetic one.
**Decision.** Bound the envelope from both sides, and bound the gap, at the CHECKER:
- `Envelope.notBefore : Nat`, signed (`Envelope.message` gains it after `start`; layout
  `[member, grant, from, notBefore, validUntil, key, signature]`; domain
  `nanodregg/protocol/read-envelope/v2`).
- `Envelope.check`: FIRST `validUntil ≤ notBefore + Kernel.Bounds.windowMax` else `wideWindow` (the
  kernel's own window bound for calls, `World.admit`'s `overBound .window`: one notion of a window);
  then key, signature, follow grant as before; then `notBefore ≤ w.height` else `notYet`; then
  expiry, last, stating the height.
- Follow signs every envelope as `[base, base + window]` for the height it signs from: its own
  height (first page), the stated tip (later pages), the stated `expired` height (re-sign), the pin's
  height (adopt). `notBefore = upTo - window` is computed at the one place that builds an envelope.
So an inflated H gives `[H, H + window]`: refused `notYet` now, and when the World does reach H it is
a credential of ONE window, the same an honest capture gives. A deflated H is refused `expired`
again and the command ends `expired`: a denial of service, which a MITM has anyway.
**Theorems.** `Envelope.check_ok_within`: an accepted envelope has `notBefore ≤ w.height ≤
validUntil ≤ notBefore + windowMax`, so the heights at which any one signature reads are at most
`windowMax + 1` (writer-side, whatever the client did). `check_ok_iff` restated with both new
conjuncts; `check_expired_authenticated` and `check_notYet_authenticated` (the order: a stranger or
forger learns neither) with the converse `check_notYet_of` (an authenticated reader above the
World is refused by that name, no other); `check_wideWindow` (width first, whoever signed);
`message_heights_inj` (the signature binds `start`, `notBefore`, `validUntil`: one window's
signature is not another's); `ReadRefusal.name_injective` over the two new names. A second agent
read the statements for vacuity; its findings (no injectivity of the message in `notBefore`, no
precedence for the width check, one-directional `notYet`) are the last three theorems. The last gap
from that read (nothing tied `Host.Follow.window`, 128, to `windowMax`, 1024) is closed by HOST-6's
`Host.Follow.window_le_windowMax` (79f5860).
**Row.** `inflatedHeight` (its own row, so its plant runs): 110 writes (the rows' window is 100),
then the auditor reads cold with the transport fault `inflateExpired 1000000`, which adds a million to
the height an `expired` states. Expected `refused notYet`. Plant `ignoreNotBefore` (the writer's gate
skips the lower bound, the shape before this decision), caught at line 10: the inflated envelope is
served and the read is `ok`. Rows: 13 PASS, 4 PENDING.
**Flag day.** The envelope frame and its signed message change (v2 domain); nothing persisted holds
an envelope (they live one command). No Rust reads or writes envelopes (follow signs through custody's
byte-signing step), so CODEC emits nothing new. Old-shape envelopes do not decode: `badEnvelope`.
**Alternatives.** A per-member window in the envelope with no checker bound (the client's honesty
would be the bound). A `retryAt` hint signed by the writer (writers have no signing key on this
socket; the base MAC is the Store's, not a reply key). Authenticating replies: that is the
channel's job (TRANSPORT), and the envelope must stay bounded even when the channel is not.
**Critique.** The stated height can still be inflated; what changed is what the inflation buys.
A MITM can still MOVE an envelope's window into the future and hold it until the World gets there,
where an honest capture would be a window of the present. That is the same length of credential at
a time of the attacker's choosing, and a member that keeps a grant open accepts exactly that risk
for any capture. `notYet` is terminal (no re-sign): an honest writer never states a height above
its own, so a `notYet` is always a liar or a clock of a different World, and a retry would only buy
the liar another signature. `wideWindow` reuses the kernel's 1024: a deployed `Host.Follow.window`
past it would refuse every read, loudly, by name.
**Meta-critique.** My predecessor framed it as "take the height from the follower, or the writer's
word is enough". Both answers accept that the envelope's lifetime is whatever the number says; the
fix lives in neither the follower nor the writer's word but in the checker's bound. I am
also adding a second refusal name (`wideWindow`) where `badEnvelope` would have done: law 7 says one
condition one name, and "too wide" is not "undecodable". TRANSPORT's planned world field (v2 by its
own plan) now lands as v3, or folds into this flag day if it lands first; either way one shape at a
time and the old one refuses.
**Status.** BUILT (this commit).

## PROTOCOL-28 · row wrongWorld: the writer's whole log, replayed into a Store that differs only in its nonce, is refused `wrongWorld` call by call; the same nonce is a restore (2026-10-17, PROTOCOL-6; KERNEL-24 at 9e91ede)
**Decision.** The act `replayElsewhere` (the actor's last call into a second genesis) is replaced by
`replayLog (sameNonce : Bool)`: every call the attempt store settled as committed (`St.committed`,
in order) is submitted byte-identical to a second writer whose genesis has the same name,
allowance and founders, and either the same nonce or the rows' nonce with its last byte flipped. The
outcome is the one EVERY call got (`refused mixed:I:OUTCOME` if two differ). Line 7: another nonce,
`refused wrongWorld`. Line 8: the same nonce, `ok`. Plant `nonceRepeats` (the second genesis draws
the first one's nonce), caught at line 7: `ok`. Theorem cited: `Kernel.Receive.admitted_elsewhere_refused`.
**Why a whole log, not one call.** One call into a fresh genesis is refused for unrelated reasons
(its member was enrolled by an earlier call that is not there), so the old act could not tell
"bound to another World" from "a stranger". With the whole log the same-nonce Store re-admits
every call, so line 7's refusal can only come from the origin. HOST-6 pointed out that the old act
would have PASSED the replay after KERNEL-24 (same genesis = same origin).
**Why no "binding removed" plant.** It needs a switch in `Receive.receive`, which is deployed code;
I will not add a test knob there. Removing the check is already caught by NAME: founder ids are keyed
by the origin, so the replay without the check answers `unknownKey`, not `wrongWorld`. The plant
covers the other half of the fact, the origin's dependence on the nonce.
**Critique.** The row checks the call binding only. The read envelope's binding (TRANSPORT's v3,
`ReadRefusal.wrongWorld`) is not in it yet. `nonceRepeats` is a mutation of the rows' own genesis
parameters, not of HOST's nonce draw (`host genesis` reads `--nonce` or the OS): a Host that drew a
constant nonce would pass this row, and only HOST's own test of the draw can catch that.
**Meta-critique.** "Every call got the same outcome" is stricter than the claim (the first call
refused would do) and that is deliberate: a partial binding (say, only `create` carried the world)
would show up as `mixed`.
**Status.** BUILT (this commit). Rows 14 PASS, 3 PENDING (pay well bounty).

## PROTOCOL-29 · the read envelope names its World; a member signs for the World it was invited to (2026-10-17, BUILD-TRANSPORT; ASSEMBLY D3, KERNEL-24; shape with PROTOCOL-6)
**Decision.** `Envelope.world` (the World's genesis origin, `World.origin`, KERNEL-24) is the first
field, inside the signed message (domain `read-envelope/v3`); `Envelope.check` refuses
`wrongWorld` FIRST, before the window, key or signature (`check_wrongWorld`), so a read replayed
against another World — a clone with the same name and founders, or another Store on the same box
— is refused by its own name, never `unknownKey`/`badSignature`. `Command.Self.world` is the World
the member was invited to, taken from the member's own Store (its genesis, built from the
invitation), never from the Host it talks to; every envelope and every call follow plans names it
(replacing KERNEL-24's `w.origin` placeholder in `plan`), and follow's own `receive` refuses a call
for another World. A thin member asserts `adopted.origin = me.world` after `Thin.accept`
(`Thin.Refusal.wrongWorld`): the pin's digest already binds the World's bytes, origin included;
the assertion names the case.
**Alternatives.** (a) Bind the World implicitly (the signature over a message that includes it,
but no field): a cross-World read then refuses `badSignature`, the wrong name (law 7). (b) Leave
reads unbound: a captured envelope re-reads a clone within its window. (c) `Self.world` from the
Host's first answer: trust on first use, which is exactly the mis-routing the binding exists for.
**Critique.** `wrongWorld` before the signature is an oracle: an unauthenticated prober confirms an
origin guess. The origin is not secret, and socket access is the real gate, but it is one bit more
than before. That the signature binds the world BYTES was named here as a gap (it needs `Env.bytes` injective and of one width). It is CLOSED (PROTOCOL-6, after KERNEL-37 stated `Env.Lawful`): `Envelope.message_inj` (under `X.env.Lawful n`, equal messages have equal world, member, grant, start, notBefore, validUntil) and `Envelope.deployed_message_inj` (no premise, by `Receive.deployed_lawful`). A copied Store directory keeps its origin, so a fork is the same World to this check;
only followers comparing chains see it. The invitation that carries the origin to a new member
does not exist yet (HOST-4's `host genesis --nonce` reproduces a writer's genesis; the founder
copies label, nonce and founders to the member by hand).
**Meta-critique.** Symmetry with KERNEL-24's call binding is doing much of the arguing; the read
replayed against a clone leaks only what that clone holds, so the binding is cheap insurance as
much as a closed hole.
**Status.** landed (this commit); the cross-World envelope line in row wrongWorld follows
PROTOCOL-6's rebuild of that row.

## PROTOCOL-30 · a carry (OPS-P1) must keep the live journal, or the attempt store calls a committed call refused (2026-10-17, PROTOCOL-6; answers OPS-P1's question to PROTOCOL)
**The question.** After a carry (re-genesis under a new origin, carried cells, no history), does a
client need a refusal `worldChanged`, or is `wrongWorld` on the first call enough?
**Finding.** The name is enough. The danger is in the attempt store. An attempt whose reply was lost,
for a call the old World committed just before the export, settles against the new Store as
`lookup absent` (empty journal), then `submit refused wrongWorld`, so it ends REFUSED. The call's
effect is in the carried cells. nd reports a lie, and a retrying user acts twice.
**Decision (asked of OPS and KERNEL).** (A) The carry keeps every journal entry still inside its
window (at most `windowMax` heights): `lookup` in the new World answers committed for those calls.
Then `wrongWorld` on a resubmit is a true final verdict: a call the old World never committed can
land nowhere, because the carry ends the old World. Fallback (B), if the journal cannot be carried:
`Attempt` classifies a `wrongWorld` reply to a frozen attempt as not a verdict and ends `uncertain`
(a new `Seen`), with a row of a frozen attempt across a carry. (B) is strictly worse: every
attempt in flight at a carry stays uncertain forever.
Members re-pin by `adopt` or a re-invite. TRANSPORT's v3 envelope names the invited origin, so the
first read after a carry is `refused wrongWorld` before anything is signed.
**Critique.** (A) makes a carried Store hold another World's txIds, a second meaning for "journal"
(receipts of calls that name another origin). `lookup` must not check the call's world against the
origin, or (A) silently becomes (B). That is a premise the carry row must test, not assume.
**Meta-critique.** "Is the name enough" was the wrong question to be asked. The right one is "what
verdict does the client reach", and a name cannot answer it: the verdict comes from the order
lookup-then-submit, and only the journal decides what lookup says.
**Status.** (A) agreed by OPS-2 and taken by KERNEL-6 as KERNEL-29: the carried World keeps the old
height and the journal entries admitted above height - windowMax (theorem carry_lookup), with a
fresh chain and an origin over the carried contents. Consequence for PROTOCOL: height 0 no longer
means genesis. adopt notAtGenesis and follow from a carried Store must be re-read against
KERNEL-29 when it lands. A carry row is built then.

## PROTOCOL-32 · the ledger verbs `issue`, `account`, `transfer`, `credit`; rows `well` and `pay` on the receivers; a hostile client is a row act (2026-10-17, PROTOCOL-6; LEDGER-2's D5 at c3c7aa3, LEDGER-6 (f), LEDGER-7)
**Decision.** Four verbs (16 of 20): `issue CAP`, `account ASSET [--owner OWNER]` (default: the
signer), `transfer SRC DST AMOUNT [--via GRANT] [--once HEX]`, `credit WELL ACCT AMOUNT [--via GRANT]`,
with an account named `well:ASSET` or `of:OWNER:ASSET` (`AcctRef`, resolved by the receiver). Flags
come after the positionals, in any order, each at most once (`usage` otherwise). Two new parse
refusals: `badAccount` and `badOnce`. `Machine.body` maps each verb to its `Body` constructor one to
one. The pins of the resolved account ids come from `derivePins` through `unpinned`, as LEDGER-2 said.
`plan` is factored as `planUnchecked` (derive, pins, price) followed by follow's own `World.admit`
(`planUnchecked_derives`; `plan_admits` keeps its statement).
**Rows.** `well`: issue 100; an account opened for another owner; that owner's own `account` is
`idTaken`; the issuer's own account; a mint of 10; a mint of 1000 `belowFloor`; a credit of 5; an
owner's transfer; a non-owner's `noGrant`; a burn into the well. Plant `accountByAsset` (the keyed id
ignores its owner, for the writer and every follower), caught at line 3: `refused idTaken`. `pay`:
transfer `--once 6b31` ok; the same key again `spent` (follow's own admission); the same key from a
HOSTILE client (act `forge`: parse, body, `planUnchecked`, signed, submitted, with no admission of
its own) `spent` from the WRITER; another key ok. Plant `writerForgetsSpent` (the writer admits
against its World with the spent set removed), caught at line 4: `ok`.
**Why `forge`.** Every value refusal a client meets is first met by follow's OWN admission, before
anything is signed. A writer-side plant is therefore invisible to an honest client, and LEDGER's
proposed `skipJudge` plant does nothing at all: belowFloor and spent are kernel admission, not laws.
The property that matters on the wire is that the writer refuses a client that does not check, and
`forge` is that client, built from the deployed functions only.
**Critique.** The floor (`belowFloor`), the authority (`noGrant`) and the credit line are held by
name in the rows. No row plant removes the check, because the check is `World.admit`, shared by the
writer and every client, and making it a parameter would put a mode into deployed admission. Those
checks are held by KERNEL's sim plants (`belowFloor`, `noGrant` are in `Sim.planted`). `forge` plans
on the actor's follow World as its last command left it, so a forged line straight after another
actor's write would be refused as stale, not by the rule under test: put a forged line after the
same actor's command. `escrow`/bounty is still pending on LEDGER's escrow package.
**Meta-critique.** I came close to accepting the proposed `skipJudge` plant because it came with the
row text. Running the row was what refuted it (a plant that does nothing would have read as "not
caught" and turned the row red). The real question was where the refusal is decided, and the answer
(the client first) dictated the hostile-client act.
**Status.** BUILT (this commit). Rows 17 PASS, 1 PENDING (bounty).

## PROTOCOL-33 · row forgotten: past KERNEL-33's prune a lookup is `uncertain forgotten`, never `refused`; `Expect.unsettled` names why (2026-10-17, PROTOCOL-6; KERNEL-33 at 17e2d3f, HOST's arm)
**Decision.** `Expect.unsettled (why)`: the Host's reply was `uncertain` and stated a name. The rows'
`statusOutcome` reads an `uncertain` with a payload as `unsettled NAME` (an empty one stays
`uncertain`), so a line can expect `forgotten` BY NAME. Row `forgotten`:
- a committed call whose reply was lost (newcomer, settled by lookup), and a never-forwarded one
  (sponsor, `absent`);
- 110 heights later the never-forwarded call is `refused expired` (true: the journal still
  answers, `notBefore + 2·windowMax > height`, `Kernel.fold_answers`), and the committed one is
  `ok`;
- 3100 heights later both are `uncertain forgotten`. The committed one is NEVER `refused`.
Plant `forgottenRefused` (the writer sends `forgotten` as a refusal, the shape PROTOCOL-6 asked
KERNEL-8 and HOST-7 not to take), caught at line 13: `refused forgotten`.
**Why the status, not the name.** The attempt store decides by the status byte (`classify`), and
`Attempt.next` after a lookup that is `unknown` ends `uncertain` with no resubmit
(`next_after_lookup`). A `refused forgotten` would end the attempt REFUSED for a call that may have
committed. That is the false verdict the plant shows.
**Critique.** 3100 heights is chosen to pass the prune that drops a committed entry (entries kept
under `3·windowMax`, pruned every `windowMax`), not just `journalForgets` (2·windowMax). Between
those two, a committed call can still be answered `ok` from a not-yet-pruned entry, which is true,
so the row checks the far end only. The counts are heights, so `rows --times` scaling would break
the row; the docstring says so, and the standing run does not scale. The client's Rust attempt store
is CODEC's emitted `attempt::next` over the same statuses, so it inherits the rule; no Rust change.
**Meta-critique.** The new Expect constructor exists because a status-only expectation could not
tell `forgotten` from any other uncertain answer. That is the same move as `expired` stating its
height: an outcome a client acts on must be named on the wire and in the row.
**Status.** BUILT (this commit). Rows 18 PASS, 1 PENDING (bounty), re-run after KERNEL-33's charge change.

## PROTOCOL-34 · row bounty on LEDGER's escrow; `grant` takes a value account as its target (2026-10-17, PROTOCOL-6; LEDGER-10 at 7c6c7e1)
**Decision.** `grant TARGET MEMBER RIGHTS`: TARGET may now be a value account by name (`well:ASSET`
| `of:OWNER:ASSET`, `Command.GrantTarget.account`, resolved to `accountId` in `Machine.body`),
beside an object id and `world`. LEDGER-6's deposit needs it: the depositor lends its account to
the escrow object by a mutate grant over that account, and a member cannot compute `accountId`
by hand. Row bounty on `<world/escrow/Escrow`, LEDGER-3's lines:
- the sponsor (depositor) issues, opens and funds its account;
- the poster (arbiter, the escrow's owner) installs, creates the escrow over 30 for the hunter, and
  opens the escrow's and the hunter's accounts top-level (the pinned view forbids a birth in the
  deposit's tree);
- the poster grants the depositor `invoke:0`, and the depositor lends its account to the object;
- a deposit through the wrong grant is `grantTarget`, the real deposit is ok, the arbiter's release
  is ok, and a second release is `lawDenied` (escrow: settled).
Plant `skipJudge`, caught at line 18: `refused belowFloor`.
**What the plant shows (ROOT's ruling).** The tooth is the NAME. The law refuses the second payout
by its own name (`lawDenied`, `escrow: settled`) before the kernel has to. Skip the law and the
kernel still refuses it, but by a different name. Measured: `belowFloor`, because the escrow account
is empty after the first payout and the floor is checked before nullifiers. If someone topped the
account up, the payout's shared `once` key would refuse it `spent` (LEDGER-6: the floor bounds what
leaves, not how often). So the kernel is the second and third line of defence the law stands in
front of. The law's job is to refuse by its own name first, with a reason a person can read. No mode
is added to deployed admission (PROTOCOL-32's ruling).
**Critique.** The row does not cover refund, or a party other than the arbiter, because
`ledger-sim`'s E1..E14 cover them over the same package (LEDGER-3). An account grant target is
resolved by the client. A member who names the wrong owner gets a grant over an empty or foreign
account, which the kernel's authority check refuses at use, not at grant.
**Status.** BUILT (this commit). Rows: ALL PASS, 19 rows.

## PROTOCOL-35 · row carry: export, import by digest, the carried World answers the old journal, an old-origin call is `wrongWorld` (2026-10-17, PROTOCOL-6; KERNEL-29 b8e0f82, CODEC-5 28b4a38, HOST-28 6b89d6f)
**Decision.** Act `carry (rightDigest)`: the operator stops the writer, exports its World
(`Host.Carry.exportFile`), and imports it through `Host.Carry.importWorld`. That is the ONE
decision `host import` makes (HOST-8 factored it out for this row), under the rows' name and
another nonce. The digest is the file's own, or that digest with its last bit flipped. A refused
import leaves the old writer serving. A successful one must answer at the exported height with the
exported journal (else `carryMismatch`'s sibling `carryMoved`, a row check), and the carried World
becomes the writer through `Writer.genesisStore`. This is the first in-memory genesis of a carried
World (HOST-25's origin frame passes, as HOST-8 predicted). Act `rejoin`: the actor is re-invited,
its `Self.world` set to the new origin and its follow started from the carried World. Row carry:
- a committed call (reply lost);
- a wrong-digest import is `refused carryMismatch`, and the old writer still serves a write;
- the right import is ok, and the last committed call is still `ok` by lookup (the carried journal,
  PROTOCOL-30);
- a NEW call signed for the old origin (a forge from a member's stale follow) is `wrongWorld`;
- the newcomer, re-invited, writes and reads its write on the carried cells.
Plant `importTrustsFile` (the import is handed the file's own digest), caught at line 7: ok.
**Critique.** An exact resubmit of a call committed before the carry answers from the carried
journal (ok), not `wrongWorld`: the journal holds the old txIds by design (PROTOCOL-30). Only an
un-journaled old-origin call is refused by origin. The digest is the only link from the old Store
to the bytes imported, and it travels out of band; the plant shows the import trusts nothing else.
`rejoin` stands in for an invitation, which does not exist yet: the member is handed the new origin
and the carried World by the row, as a founder would by hand.
**Status.** BUILT (this commit). Rows: ALL PASS, 20 rows.

## PROTOCOL-36 · carried member ids are names (KERNEL-40, opacity); the rows key founders by the lineage's first origin (2026-10-17, PROTOCOL-6)
**Decision.** PROTOCOL agrees to KERNEL-10's opacity. An id is a name minted at the lineage's first
genesis, a carry keeps it, and nothing may recompute an id from a carried World's origin.
Enumerating Protocol's readers of an origin found one LATENT defect, in the rows. `freshActor`
derived a founder's id from `st.genesis.origin`, and the carry act moves `st.genesis` to the
carried World. A founder whose first act came after a carry would therefore have been a stranger
(`unknownKey`). The carry row never had such a founder, so it passed. Fixed: `St.lineage` (the
first genesis's origin) keys founder ids; `st.genesis` stays the World follows start from.
`Self.world` is still the CURRENT origin, as `rejoin` sets it.
Tooth: row carry's last two lines have the operator act for the first time after the carry
(`rejoin`, then `create`). A manual plant run with the old derivation gives `ROW carry FAIL line 16:
got refused unknownKey, expected ok`. The client's command machine and envelope take member ids
from `Self` (set from the invitation) and never derive them, so the client needs no change.
**Critique.** The standing plant of row carry is still `importTrustsFile`; this tooth is held by
the line's expectation and was shown red by a manual code plant, not a standing mutation.
**Status.** BUILT (this commit). Rows ALL PASS, 20.

## PROTOCOL-37 · row thinStale: a thin member adopts a pin more than a window old; the rows' `window` act (2026-10-17, PROTOCOL-7)
**Decision.** This closes a PROTOCOL-4 leftover: adopt's `reSign` arm (Machine step 7, `.refused`
with a stated height) had never been run. In row `thinStale` the thin member's client signs for a
window of 5 heights (new act `window n`: it sets the actor's `Self.window`, a client's own setting
that the writer's read gate bounds by `Bounds.windowMax`). The operator seals and attests, then 12
writes run past the pin. `adopt @pin.h @pin` signs its first envelope for pin.h + 5. The writer
refuses it `expired` at its own height, follow re-signs ONCE for that height + 5, and pages the
unmoved base. The member's first write then catches up from the base's height (12 behind a window
of 5, so by the arithmetic it re-signs by the same rule). That line is held by its expectation only:
the plant stops the row at 15, so the write's own reSign is not shown red. Plant `unstatedExpiry` (the writer states no height) turns line 15,
the adopt, into `refused expired`. Because the plant changes that line's outcome, it is the evidence
that the honest run did go through the expired → reSign arm there.
**Alternatives.** (1) Keep window 100 and run 110 writes. Tried first: the rows' seal cadence
(sealMinBytes 8192) seals a newer base inside 110 writes, and the adopt is `baseMoved`, an honest
refusal of a different case. (2) Raise the rows' seal cadence for one row: a writer knob for one
row's convenience. A short client window is a real client choice, and it leaves the writer exactly
as every other row has it.
**Critique.** The case depends on the seal cadence outlasting the window. With the rows' cadence that
holds only because 12 writes stay under 8192 bytes. If turns grow (a fatter Turn codec), the row
turns `baseMoved` at line 15, red by that name and not silent, and the fix is fewer writes or a
smaller window. A deployed writer whose cadence is shorter than its members' window never produces
this case at all: then every stale pin is `baseMoved`, and the reSign arm is reachable only by a pin
under one seal of age. Whether that is true of the deployed cadence is HOST's number, not
established here.
**Meta-critique.** The first draft copied coldCatchUp's "110 writes" without asking what else 110
writes do to the writer. Familiarity with a sibling row's numbers is how a row tests a different case
than its docstring names. The `baseMoved` red caught it only because the expectation was by name.
**Status.** BUILT (this commit). Rows ALL PASS, 21.
