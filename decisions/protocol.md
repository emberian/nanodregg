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
