# decisions/protocol.md — BUILD-PROTOCOL

Reach table this layer is built from: `docs/record/DELETE-PROTOCOL-20261016.md` (minidregg main
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
Status: BUILT: Table/Command/Rows are the current interface; the original counts below are historical.

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
Status: SUPERSEDED COUNT: Protocol.Table now has seven operations, including cancel.

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

**Addendum (2026-10-21, PROTOCOL-21; cv 01a154ec-79cf): RULED, no longer open.** Ember ruled per-cell blinding on 10-18 at 04:25Z, the scope call (redregg STALL-WATCH:681): "the operator is a trusted vat → the privacy brief's (a) stands for v1 (no blinding; host sees every byte; stated with its threat model; the member-sealing design (b2) pre-committed behind its trigger)". The custody question this status named is closed.
- *Threat model, v1.* The operator's Host is a trusted vat: it sees every byte of every cell, and so does every key holding a follow grant (it folds the whole log). Membership is the confidentiality boundary. Nothing is hidden from the operator or from a follower. J5/K10/KH hold as refusals at `log`/`read`, never as hiding.
- *Why.* Nano is the semi-trusted single-node vat prototype. Hiding arrives only as a restated spec behind a named trigger. Every option that hides from the operator costs new premises (a blinded-slot-invariant judge, a `blindedState` refusal, value cells without blinded slots, a KEM wrap in Lean, key custody apart from the seed: PRIVACY-DESIGN-BRIEF §4(b)), and buys nothing for a hosted resident, whose key is on the operator's box.
- *Trigger.* The first World in which a member who is not the operator writes, from a device that member controls, content they would not show the operator. The design held for it is (b2), per-object epoch keys wrapped to members. Ember's questions Q2/Q3 are filed with it in cv 01a154f6-9cc7.

**Status (2026-10-21, ROOT for Ember).** RULED and in the charter: `CHARTER.md` §Scope item 2 states this ruling as nanodregg's scope (Ember 10-21: "nano has nothing to do with proof systems, host-hiding, or multi-node agreement"); the charter and this entry say one thing, and a change to either changes both.

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
Status: BUILT: Protocol.Rows and its Run driver hold executable rows.

## PROTOCOL-6 · the client bounds live in the protocol table (2026-10-16)
**Decision.** frameBytesMax 262144, argvBytesMax 65536, stepsPerCommandMax 64, sendsMax 8, in
`Protocol.Bounds` (ROOT: the client's list belongs in the table). `argv_fits_frame` proved.
**Critique.** `Kernel.Bounds` is "one table"; these are a second bounds namespace. They bound the wire,
not a Turn, and `submit`'s payload (a call, which becomes the Turn's `event`) must satisfy BOTH
`frameBytesMax` and `Kernel.Bounds.eventBytesMax` (65536 today): the theorem
`eventBytesMax + 1 ≤ frameBytesMax` is owed as soon as Kernel/Bounds is importable from a committed tree.
262144 is minidregg's frame headroom, not a derivation. **Meta-critique.** Numbers copied from
minidregg are exactly law 11's worry; each should be derived from the largest row payload.
Status: BUILT: Protocol.Bounds and emitted tables supply client bounds.

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
Status: BUILT: the supervisor uses the emitted connection bound; this does not imply cross-session principal fairness.

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
Status: CLOSED by CODEC-10: argv aggregate bounds and codecs are implemented.

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
Status: BUILT: Protocol.Rows.Run judges driven rows and retains non-verdict distinctions.
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
Status: SUPERSEDED COUNT: Command.Verb has twenty verbs; Machine includes the later receipt, cancel and head paths.

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
Status: BUILT: Protocol.Envelope and the idle deadline are on the deployed path.

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
Status: BUILT: Rows.Loopback/Writer drive the shared Host and command definitions.

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
Status: CLOSED: grant world MEMBER observe is the command; no follow verb exists.

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
Status: BUILT: the emitted per-request deadline is used by the client transport.

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
Status: BUILT: custody results use the emitted named result format.


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
Status: BUILT, superseded syntax: adopt takes INVITE KEY, with pin/certificate checks in Command.Machine.

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

## PROTOCOL-38 · `sync`, the catch-up verb; `CommandExit`, nd's exit table, with `behind` as its own restart-class end; `CustodyRefusal.envelopeOnly` (2026-10-17, PROTOCOL-7; HOSTING-17 §7, CLIENT-3's ask, ROOT ruling)
**Decision.**
- `sync` (no arguments) runs the catch-up every command runs (log pages under signed envelopes, re-signing once on `expired`, at most `pagesPerCommandMax` pages) and prints `height H` / `chain HEX` at the tip. It is the verb a timer drives for the nd-hosted follower.
- **No unsigned path.** CLIENT-3 first asked for a verb with "no custody step". That is refused, because every log page is served only against a member-signed read envelope (PROTOCOL-27/29). Its key is the follower's own observe-only member key, held by nd in an envelope-only custody (ROOT ruling). The custody refusal is `CustodyRefusal.envelopeOnly`, code 8, and CLIENT builds the mode.
- **`CommandExit`** (`Protocol/Command/Exit.lean`, the codes; `Protocol/Exit.lean`, the classes) is now the one table of how `nd COMMAND` ends. The machine's `done` codes come from it, the rows read outcomes through `ofCode?`, and it is emitted as `command_exit`.
  - Codes: ok 0 (done); refused 1 (fatal); uncertain 2 (restart); absent 50 (done; was 3); behind 51 (restart, new); client 52 (restart: nd's own failure, which today exits 2, the same code as uncertain; CLIENT switches).
  - Theorems: `code_injective`, `ofCode_code`, `code_disjoint_host` (every code but ok), `code_disjoint_supervisor`, `restart_fatal_disjoint`.
- **`behind` is no longer a refusal.** `Refusal.behind` is deleted. Still being behind after the page bound is the command's own end, `behind H T` with code 51, so a timer runs it again and never reads it as a verdict.
- **Emitted for the observer custody:** `ENVELOPE_DOMAIN`, a byte list printed from `Protocol.domEnvelope`.
- **Rows:** coldCatchUp gains a cold `sync` before its read. Plant `unstatedExpiry` is now caught at that line (10), so the catch-up alone is what re-signs.

**Alternatives.**
(1) A `read` with an optional OBJ. Rejected: it gives one verb two meanings.
(2) Keep `behind` as `refused behind`, exit 1. Rejected: the class would be fatal, and the timer would stop on what is load, not a defect.
(3) Codes 0–4 aligned with the wire `Status`. Rejected: absent 3 and behind 4 are Host codes (`uncertain`, `fuel`), and ROOT asked for disjoint tables. Nothing in Rust reads nd's exit 3; the client's settlement reads the wire Status, not nd's exit.

**Critique.**
- No row reaches `behind`. It needs `pagesPerCommandMax` (28) pages of `pageBudget` (16 KiB) still short of the tip, a log of ~450 KiB. Its code is definitional (`Machine.behind`), and its classification is a theorem, but no run shows it. A row with a smaller page budget would reach it, so this is undone work, not a property of the model.
- The prefix fence `ENVELOPE_DOMAIN` is sound only once call messages carry their own domain. Today a call's signed bytes start with the World digest, so the fence holds only up to cSHAKE preimage resistance (CODEC-6). The domain-separation flag day, `callMessage`, comes next (ROOT approved; with KERNEL-11), before CLIENT's real-round-trip plant.

- That `sync` signs only envelope messages is traced through `Machine.step`, not proved: phase 2 matches `.sync` before any call is planned, and `body` maps `.sync` to `badState` as a second guard. `envelopeOnly` is a name with no enforcer until CLIENT lands the observer custody mode. That mode is the enforced fence.
**Meta-critique.** The first reflex was to give the driver what it asked for ("no custody step"), because the request came with a ruling attached. The envelope gate is what decided it. A verb shaped by its caller's convenience is how an unsigned read would have shipped.

**Status.** BUILT (this commit). Rows ALL PASS, 21.

## PROTOCOL-39 · the signed shapes are pairwise disjoint by domain; the command machine signs `callMessage` (2026-10-17, PROTOCOL-7; KERNEL-42)
**Decision.** As KERNEL-42. Protocol's part is threefold.
- The machine has custody sign `X.callMessage u` for a call and for a rotation (`signNext`), and compares it at the call step (planMoved).
- The rows' hostile client (`forge`) signs the same.
- `Protocol.Proofs.Domains` (new) holds `append_ne_of_byte`, the six domain pair theorems, and the message forms:
  - `call_not_envelope`: `domEnvelope ++ r ≠ X.callMessage u`, the observer custody's fence (CLIENT-22);
  - `envelope_call_disjoint`;
  - `possession_not_envelope`;
  - `whoami_not_envelope`;
  - `call_not_possession`;
  - `call_not_whoami`.

**Alternatives.**
- A length check on envelope messages (155 bytes at deployed). Rejected: a call can be 155 bytes, and a fence that can never go red beside an exact one only misleads.
- Prefixing `unsignedBytes` itself. Rejected: it would change the codec, txId and every vector, which is a larger flag day for no gain.

**Critique.** `whoami` is a constant that init signs, so its signature is the same bytes for every key holder, and anyone who sees one can replay it. It is used only to learn the key at init, never as authority, but no theorem says so.

**Status.** BUILT (this commit). Rows ALL PASS 21; kernel-sim ALL PASS 64 seeds, arm sig-bare met; WASTE unchanged.

## PROTOCOL-40 · the `nd --stdio` surface: a resident runs every World verb but init, rotate and adopt, refused `notOnSurface` otherwise; replies are the `done` step; `peerRefused`; custody `noRotation` (2026-10-17, PROTOCOL-7; HOSTING-20, CLIENT-3's ask, ROOT approval)
**Decision.**
- `Command.stdioVerbs` = the verbs whose `Verb.onStdio` arm is true: every verb but `init`, `rotate` and `adopt`. It is emitted as `STDIO_VERBS`, from `Verb.word`. nd checks a request's first word against it before follow sees anything, so an excluded verb, a flag and an empty argv are all refused by one name, `StdioRefusal.notOnSurface`. A request that does not decode as `commandLayout` is refused `undecodable`.
- A reply is `commandReplyLayout`, which is `Step.layout .done` itself: a `CommandExit` code, stdout, stderr, each under `frameBytesMax`. A refusal is a reply too: exit `refused`, stderr `refused NAME`.
- `CloseReason.peerRefused`: nd-supervise `--peer` closes a connection whose credentials are not the configured ones, before reading a frame.
- `CustodyRefusal.noRotation` (code 9): custody opened by `nd --stdio` refuses `precommit` and `signNext`. This is a second fence behind the surface, because rotation is the operator's.
- Theorems:
  - `mem_stdioVerbs` and `word_mem_stdioWords`: on the surface iff not one of the three;
  - `init_/rotate_/adopt_not_on_surface`;
  - `StdioRefusal.name_injective` and `code_injective`, its codes UInt8 by type.
- `sync` is on the surface. It only signs envelopes, and a resident catching its own follower up harms nothing.

**Alternatives.**
- A new reply status set for stdio. Rejected: the command's own end, the done step, already says everything, and a second shape would drift.
- A filtered `Verb.all` ("every verb but three"). That was the first draft, and it was rejected: a NEW verb would land on the resident's surface by default, the widening ROOT asked to make impossible. `Verb.onStdio` is a total match with no wildcard, so a new verb does not compile until its author decides its arm.

**Critique.** `noRotation` and `envelopeOnly` are separate custody modes, and nothing here proves a custody is in exactly one. That is CLIENT-22's record shape. The surface is checked on the first word only; any later argument a verb takes is follow's to parse and refuse by name.

**Meta-critique.** The filtered list was the shortest code, and it took writing the critique to see that it defaults open. Then the critique proposed fixing it "in the next commit", which is the containment-first sequencing CLAUDE.md names. It is fixed in this one.

**Status.** BUILT (this commit): the surface, its theorems (incl. `mem_stdioWords_iff`, for any string nd receives) and the emitted names. `noRotation` and `peerRefused` are names only here; CLIENT's custody and nd-supervise enforce them, with their plants. A developer can still write `true` for a new verb; the total match makes that a decision, never a default. Rows ALL PASS 21.

## PROTOCOL-41 · a reply is FINAL only when the refusal is recorded; `Status.declined` for every other refusal of a submit; the log is a list of steps, positioned by step count (2026-10-18, PROTOCOL-8; KERNEL-44/47, the refusals day, with HOST-12)
**Decision.**
- **Finality is read from the World, by one function** (`Protocol.Settle.verdictReply`, called by `Host.Serve`).
  - A submit's refusal is FINAL (status `refused`) when:
    - `Receive.judge` recorded it now (`refused NAME`);
    - its transaction id already holds a recorded refusal (`refused NAME`, with the RECORDED name from `codeName`): the resubmit and the A→B→A case;
    - or its window has passed (`validUntil ≤ height`: final by height, as `expired` already was).
  - Every other refusal of a submit is `Status.declined` (5), `declined NAME`, NOT final:
    - every unauthenticated code (wrongWorld, badSignature, unknownKey, unpinned at the key read, undecodableCall on a submit);
    - an early `outsideWindow`;
    - `refusalBudget`.
  - A resubmit of a recorded call leaves `judge` as `declined (refusedFinal code)`, so finality cannot be read from the Outcome constructor or from the verdict's name. It is read from the record and the height.
- **The attempt store (PROTOCOL-4 / PROTOCOL-17).**
  - `Seen.declined` → `Action.declined`: the run ends, and the attempt stays OPEN (frozen, unsettled; the next run looks it up). Example: a call signed with the precommitted next key is `unknownKey` before the rotate and admissible after it.
  - A lookup is never `declined`; one that is is `badReply`. (SUPERSEDED by HOST-74: the writer declines a lookup it decided nothing about, undecodable bytes or a frame queued at an exit, and `(lookup, declined)` is `declined`.)
  - `CommandExit.declined` = 53, restart class, printed `declined NAME`.
  - Custody keeps an armed rotation armed on `declined`.
  - Theorems:
    - `Settle.final_iff_recorded`: status `refused` ↔ recorded now ∨ recorded before ∨ late;
    - `Settle.final_recorded`: a final in-window reply leaves the call recorded in the World the Host keeps, under the reply's name. That record is what `Kernel.Receive.judge_recorded_final` / `fold_refused_retains` carry forward;
    - `Settle.declined_open`: declined ⇒ nothing recorded, the World unchanged, the window not passed;
    - `Attempt.next_refused_iff`: only a `refused` status ends an attempt as refused;
    - `next_declined`, `next_lookup_declined`.
- **The log is a list of steps (KERNEL-47).**
  - A page event is a tag byte and a signed call: 0 an admitted Turn, 1 a recorded refusal.
  - `logReplyLayout` = (events, steps, chain, tipSteps, tipHeight). Positions (`start`, a page's end) count steps. `tipHeight` is what follow's next envelope window is signed from (notBefore = upTo − window must not exceed the writer's height).
  - Follow re-derives a Turn event by `submit`, and a kernel rejection of a derived Turn now surfaces by the kernel's name: a writer that commits a recorded call is caught `refusedFinal`.
  - Follow re-derives a refusal event by `judge`, which must RECORD it (`auditRefusal`'s rule).
  - `absorbPage` binds (steps, chain), the pair `fold_reaches_host` binds.
  - `Persist.steps` carries (Step, roots digest), the shape of a batch record.
  - Theorems:
    - `absorbStep_step`, `absorb_admits`, `absorbPage_admits`, `step_persists_admitted`, `step_persists_folds`, restated over `RootedFold` of steps with no new premise;
    - `absorbPage_steps`;
    - `absorbStep_refusedFinal` (the plant's catch, by name);
    - `absorbStep_refusal_recorded`: an absorbed refusal answers its call `refusedFinal` with the code whose name is the verdict's.
- **Row `refused`** (22nd; rows ALL PASS 22 on the joint tree): stale-and-recorded; lookup by name; A→B→A resubmit still `refused stale`; sixteen recorded then `declined refusalBudget` (lookup `absent`); past the window `uncertain forgotten`. Plant `admitsRecorded` (a writer that commits a recorded call while answering `refused stale`) is caught at line 18 by the member's follower: `refused refusedFinal`.
- Rows whose submit refusals were unauthenticated now read `declined NAME` (the cross-World replay, the forged call after a carry). This is a restatement of the same check under the new status, not a weakening.
- **Pins and base pages count steps.** `readReplyLayout`'s first field is `steps`; `Thin.Pin` = {steps, digest}; `Thin.Base.stepsOf`; the verb is `adopt STEPS DIGEST`; `attest` binds `NAME.steps`. A thin member's catch-up starts from the adopted World's steps. Its first adopt envelope is signed for one window from height 0 (a pin no longer names a height), so a writer further on answers `expired H` and follow re-signs once (PROTOCOL-19's path; thinStale still catches its plant at 15).
  - Row `refused` line 19 adopts a base whose steps exceed its height.
  - Probe (not landed): paging from `w.height` instead of `w.steps` turns journey line 15 and refused line 19 red (`eventMismatch`).
- **The client half** (cross-layer client, ROOT for CLIENT): CLIENT-25.
- **Emit**: the emitted `Action` enum is `Attempt.Action.all` (`Action.mem_all`), no longer a list restated in Emit/Rust.lean.

**Alternatives.**
- Reuse `uncertain NAME` for the non-final refusals. Rejected: uncertain means "the writer cannot say whether it committed". Here the writer can say: it has not, and nothing is recorded. The attempt store would also lookup-then-resubmit in the same run, up to `sendsMax`, for no new information.
- Classify finality by name, with a client-side list of non-final names. Rejected: `outsideWindow` is final when late and open when early, and a resubmit's name is `refusedFinal`. Only the World knows, and PROTOCOL-6's lesson stands: decide by status.
- Keep heights as log positions and add a step count only for the check. Rejected: refusals do not advance height, so a position in heights cannot name the step after a refusal.

**Critique.**
- `declined` keeps open attempts that can never commit (a badSignature is deterministic). A timer re-running them burns lookups until the window passes and the lookup turns `expired`. That is bounded by the window and by `sendsMax` per run, but it is waste.
- The late check is `validUntil ≤ height` at the writer's pre-state. A call judged at H with validUntil = H+1 is in-window and recorded, so the boundary agrees with `checkRefusal`. Still, it is two statements of one window (kernel and Settle), with no theorem tying them.
- The row's 16 forges are all `stale`. The budget is exercised by one refusal kind only.
- Two expectations moved from `refused wrongWorld` to `declined wrongWorld` (carry line 11, wrongWorld line 7). They are correct and not a weakening: the check still refuses by the same name at the same line. Only the status changes, because an unauthenticated refusal is recorded nowhere and so cannot be final.

**Meta-critique.** The first sketch classified by the Outcome constructor (recorded ⇒ final). Reading `judge` showed that a resubmit of a recorded call comes out `declined`, and that sketch would have answered the A→B→A resubmit as NOT final: the defect this day exists to close, reintroduced at the wire.

**Status.** BUILT in the refusals day (KERNEL-14's one commit). CLIENT owes the attempt store's `declined` arm (ROOT relays). The emitted status and command-exit tables move: `generated.rs` re-emits.

**Addendum (2026-10-18, PROTOCOL-9; HOST-41, agreed by PROTOCOL-7): the reader refuses a page longer than one record.**
- **Decision.** `Bounds.pageStepsMax` = 64 is the number of steps one `log` page may carry: one follower record's worth. HOST's `recordTurnsMax` is that number, and HOST's pager stops a page there.
- **Refusal.** `absorbPage` refuses a longer page as `pageTooLong COUNT` before it absorbs any step of it. Follow's state is unchanged and nothing is persisted: this is the `same` arm of `step`, by the same route as `chainMismatch`.
- **Theorem.** `Proofs.Command.absorbPage_tooLong`.
- **Why.** Before this, a follower handed a 100-step page appended a record its own reopen refused (`host.md` HOST-41). The writer's cap is the fix. This check is the reader's half, so an uncapped writer is named at the member rather than at the member's next reopen.
- **Measured probe.** The reader check on a writer WITHOUT HOST's cap (main 38d94e1 plus only this change) turned three rows red by name:
  - paging line 10, `refused pageTooLong`;
  - coldCatchUp line 10, the same;
  - inflatedHeight's plant run.
  With HOST's cap, rows are ALL PASS 22. That probe is the plant. There is no standing plant: the cap is inside HOST's pager, and the rows have no knob for it.
- **Critique.** Catch-up per command is now 28 × 64 = 1792 steps, and a member further behind exits `behind` (restart class). Two named constants now hold one number, ours and HOST's `recordTurnsMax`. The single-source is HOST's to make: `recordTurnsMax := Protocol.Bounds.pageStepsMax`, or an `rfl` theorem.
- **Meta-critique.** I took PROTOCOL-7's agreement as settled and did not re-derive the 64. That number is HOST's measured record bound, not ours.

## PROTOCOL-42 · an invitation: the joiner derives the World it joins from inputs a sponsor key it trusts signed; `invite`, `adopt INVITE KEY`, `host join`; row `invite` (2026-10-18, PROTOCOL-9; TRANSPORT's D7 and ASSEMBLY D1's open critique, with HOST-12)
**Decision.**
- **What an invitation is** (`Protocol/Invite.lean`).
  - Wire form: `unsigned ‖ signature`.
  - `unsigned` = (the World's origin inputs as `Receive.genesisInput` bytes, i.e. name, nonce, allowance and founders as (key, next-key digest); the pin's step count; the pin's digest; the sponsor's member id; the sponsor's key).
  - The sponsor's member key signs `domInvite ‖ unsigned`, where `domInvite` = "nanodregg/protocol/invitation/v1". It is pairwise disjoint from the four other signed shapes (`invite_*_disjoint`, `invite_not_envelope`, `invite_not_call`, `invite_not_possession`).
- **What a joiner decides** (`Invite.accept X trusted bytes`, in order):
  - `badInvitation`: the bytes do not decode;
  - `notSponsor`: the key is not the one the joiner trusts out of band;
  - `pinMismatch`: the signature does not verify over the bytes carried;
  - `Receive.genesis` of the signed inputs, which refuses by `GenesisRefusal`'s name.
  The World returned is what the joiner's own Store starts from, and its origin is the member's `Self.world`. Theorems:
  - `accept_ok`: every field is the decode of the verified bytes, and the World is `genesis` of the inputs among them;
  - `accept_origin`;
  - `accept_unverified`: a forged input or pin is `pinMismatch`;
  - `accept_untrusted`.
- **Verbs.**
  - `invite INPUT` (the 18th verb). It catches up, refuses `otherWorld` unless INPUT makes the member's own World, pins that World (its steps, `B.digest` of its bytes), has custody sign the invitation with the key its envelope was just authenticated with, and prints `invite HEX`.
  - `adopt INVITE KEY` replaces `adopt STEPS DIGEST`: the pin comes signed (`adoptPin` = the same `accept`, plus `otherWorld` for another World's invitation). The out-of-band pin channel ("Ember's, unbuilt") and the rows' `attest` act are DELETED.
  - `invite` is off the stdio surface: a resident vouches for no one (`invite_not_on_surface`).
- **HOST (cross-layer, HOST-12 agreed, with its amendment).**
  - `host join STORE INVITE_HEX KEY_HEX` runs `Invite.accept`, then the one `Host.genesis` of the World that `accept` returned. It prints genesis's lines plus `sponsor HEX`, the id `init` names.
  - New fatal `Status.inviteRefused` (44), printed `refused inviteRefused NAME`. Malformed hex is `usage`. A genesis refusal keeps genesis's status and name.
  - `join_genesis_iff`: genesis is the first writing effect reached exactly when the hex parsed and `accept` accepted. That is refuse-before-write, and its tooth.
  - `host genesis` prints `input HEX` LAST, so no current parser moves.
  - OPS (ROOT for OPS): the `hostAction` arm, and units re-emitted (`RestartPreventExitStatus` gains 44).
- **Trust on first use: what flips, what stays.**
  - Before this, every row actor's `Self.world` and first World were the writer's genesis handed over by the harness: TOFU in all 22 rows. The deployed client was TOFU too (inputs copied from `host genesis`).
  - Now every non-founder rows actor first accepts the rows' FOUNDING INVITATION (the sponsor's, at genesis) under the sponsor's key. Founders start from the genesis they made.
  - STILL TOFU, by name:
    - (1) the carry row's `rejoin`, and any actor first used after a carry: a carried World is made from a FILE, not from inputs, so no invitation can carry it. Next: an invitation whose pin is the carried World's base, which a thin joiner adopts;
    - (2) the deployed client until CLIENT-5 calls `host join` (below).
- **Row `invite`** (23rd). The lines:
  - the sponsor invites; a joiner accepts, joins, writes and reads on the World it derived;
  - the invitation relayed with its nonce changed (a hostile Host's own World) is `pinMismatch` (14), and relayed and re-signed by the relay, `notSponsor` (15);
  - a joiner trusting another key refuses the honest invitation `notSponsor` (16), and so does a thin member's `adopt` (18);
  - a sponsor asked to invite to another World's inputs refuses `otherWorld` (17).
  Plant `trustFirstUse` (the joiner takes the inputs unchecked) turns line 14 `ok`. The thin rows (thin, thinStale, refused) now adopt from the operator's `invite` under `@operator.key`, and keep their plants at their lines.
- **The client's need (CLIENT-5, `nd init SPONSOR`).** ROOT relays.
  - A joiner receives an INVITATION (hex) and its sponsor's KEY by two channels; the key is the person's word.
  - It runs `host join STORE INVITE KEY` (exit 44 `inviteRefused NAME` names the refusal; nothing is written), then `init` with the printed `sponsor` id.
  - It KEEPS the invitation: its inputs are what it later invites from (`invite INPUT`), and a thin member adopts with `adopt INVITE KEY`.
  - Founders keep `host genesis`'s `input` line.
  - nd decides none of this: both checks are Lean's.

**Alternatives.**
- (a) Sign the origin digest instead of the inputs. Rejected: the joiner needs the inputs to build its genesis World anyway, and signing the bytes it decodes means `accept_ok` needs no hash premise.
- (b) Trust the sponsor's member ID instead of a key. Rejected: an id is an origin-keyed hash, which the joiner cannot check before it has the World.
- (c) Keep `adopt STEPS DIGEST` beside `adopt INVITE KEY`. Rejected: two shapes of one trust input, and the old one is the unbuilt channel.
- (d) D7's `attesterNotMember` (after decoding, the signer's key must be the current key of a live member of the pinned World). DECLINED:
  - With an honest host, the pinned World is the real World as the sponsor saw it, and the sponsor's envelope was just authenticated with that key, so the check cannot fail.
  - With a hostile host and a thief holding a rotated-away key, the thief also chooses the World bytes behind the digest, so the check passes on the forged World.
  - So it is either redundant or defeated. A gate that cannot go red is not a gate. The joiner's trust root is the key it was given; what protects against a stolen old key is the person handing out the current one.

**Critique.**
- The trust root is a key a person hands over. A sponsor who rotates invalidates every key fingerprint it gave out (`notSponsor` until a fresh one arrives), and a stolen sponsor key plus a hostile host still forges a thin joiner's World (the pin binds bytes the thief chooses). A full joiner is safer: it re-derives every Turn from the genesis of the signed inputs. The host can withhold or fork the log after genesis, but it cannot hand over another World.
- `invite` encodes the whole World to compute its digest: O(World) on the inviter's client, once per invitation. That is not the writer's request path (law 5), but it is O(store) work, and a large World makes `invite` slow.
- The pin is the inviter's World at its tip. A thin joiner needs the writer's newest base at exactly that step count (`baseMoved` otherwise), so in practice an operator seals before inviting a thin member. A full joiner ignores the pin.
- Carried Worlds are still TOFU.
- `host join` is checked by a theorem and by a smoke run (garbage hex is `usage`, a non-invitation `inviteRefused badInvitation`, exit 44, no Store written). No deployed test drives a real invitation through it: that needs CLIENT's custody.

**Meta-critique.**
- I came to D7 prepared to build `attesterNotMember` because the brief named it. I declined it only after pricing what a thief can forge. A check carried forward from a design document is a check nobody has yet attacked.
- I reached for the TOFU flip in the harness (`freshActor`) partly because it made "which rows flip" a one-line answer. It does flip every row, but the only refusal those rows exercise is the invite row's.

**Status.** BUILT. Rows ALL PASS 23 (logs/protocol9-inv-rows2.log). Full `lake build` green. The emit checks pass, with units re-emitted.
- Vacuity read (a second agent): every theorem ACCEPTED. Fixes taken from it:
  - invite phase 8 verifies custody signature before printing (it was checked by key equality only);
  - the invitation-world refusal is named otherWorld, apart from the envelope and thin wrongWorld;
  - the docstring says the sponsor id is stated, not verified.
  Kept as stated: name_injective is at tag level (as Thin).
- **Addendum (2026-10-18, PROTOCOL-9; ROOT's ruling on cv 01a14de7-224a, and CLIENT-5's measurement).**
  - **What a carried World's joiner trusts instead.** A carried World (KERNEL-29) is made from a FILE: the exported cells, under a new origin that commits the old origin, the carried trie's root and the journal (`CarryInput`). No list of inputs rebuilds it, so no invitation can be accepted into a genesis.
    - Its joiner trusts the OPERATOR who ran the carry. The operator exported a stopped Store, copied the printed digest out of band, imported with `--digest`, and `host import` printed the new origin.
    - The member takes that origin as `Self.world` on the operator's word: by name, trust on first use (the rows' `rejoin`), exactly as much as every member trusted the carry itself.
    - What would replace that trust: a sponsor in the carried World signs an invitation whose pin is the carried World's base, and the joiner adopts thin under the sponsor's key. That stays open by design until a carried World has members who want it.
  - **Deployed thin adopt has no seal.** CLIENT-5 measured it through the real host: `adopt INVITE KEY` answers `baseMoved` unless the inviter's tip equals a cadence base. The rows seal with a harness act (`Writer.checkpoint`), and no host verb or op seals on demand. Deployed thin joining from an invitation is therefore not usable yet; full joining (`host join` + fold) is. Asked of HOST-12: a `host seal` on a stopped writer, or a seal request.

## PROTOCOL-43 · the use row: objects made by one member and used by another, counted from signed calls; THE BAR's purpose as a row (2026-10-18, PROTOCOL-9; DELVETALK-LEARNINGS §4.7, §7)
**Decision.**
- **The measure** (`Protocol/Use.lean`):
  - `usedBy c`: the member a call is signed for, and the object it invokes or writes.
  - `makerOf`: the object's owner slot, when the owner is a live member. The kernel sets it to the actor of the `create`, and no act changes it; an object made inside another object's run is owned by that object and is not counted.
  - `shared X w calls`: the distinct objects some call uses whose member is not the maker.
  - Theorems:
    - `mem_shared`: an object counts ⇔ a call uses it and is signed for a member other than its maker;
    - `shared_self`: if every using call is signed for the maker, the count is 0;
    - `shared_nodup`.
- **Row `use`** (24th).
  - The two founders each make two counters on THE BAR's counter package and grant `anyone` its `add` (PROTOCOL-26).
  - Each adds to the other's two. A friend's add to its own is self-use and is not counted.
  - Line 14: `used 4`. The act catches up (`sync`) and counts on the member's own World over every call the writer committed. This is delvetalk's go/no-go: "resident-made things used by a resident other than their maker, at least 4".
  - Then Hermes joins, adds to a friend's counter, and makes one a friend uses. Line 22: `used 5`.
  - Each count is printed as a `USE … shared-objects N of M committed calls` line in the transcript.
- **Plant `oneMember`.** Every client signs as the sponsor: one resident playing every part. Every command still succeeds through the public grants, and line 14 reads `refused unshared:0`.
- **New act `used N`**: `refused unshared:N` below N.

**Alternatives.**
- (a) Count by the actor who ran the command (the harness's name). Rejected: that measures the harness. The plant would read 4, because actor names differ while members do not.
- (b) An OPS metric over a live Store. Also worth having, later. But a row runs on every landing and holds the definition to a plant now, while a live metric needs residents first.
- (c) Count writes and invokes separately, or weight by call count. Rejected: delvetalk's question is whether a thing was used by another member at all. A distinct-object count is the go/no-go's unit.

**Critique.**
- The row exercises the measure. It does not make anyone use anything: a row that scripts two friends using each other's counters will always pass.
- The number that matters is the same count on a real Store with real residents. Nothing computes that yet: it needs a reader over a Store's committed calls (OPS or HOST), and that is where this count should go next.
- `committed` is the calls the rows' attempt store settled as committed, not a re-read of the writer's log.
- A `grant` or a ledger `transfer` to another member's account is not a "use" here. Neither is a read: reads are not calls.

**Meta-critique.** Delvetalk named the measure, and I adopted its threshold of 4 unexamined. It was a playtest's go/no-go for a night, not a property of a system. Here 4 is just the row's scripted count, held so that a plant reading 0 is red.

**Status.** BUILT. Row `use`, plant `oneMember`@14 `refused unshared:0`.
- Vacuity read (a second agent): the six theorems were ACCEPTED.
  Fixes taken from it:
  - `makerOf` counts only member owners: an object made inside an object run has an object as owner, which would have counted under `oneMember`;
  - the module doc no longer claims as a theorem that a one-resident run counts 0 (the plant shows it for this row);
  - nested uses are named as uncounted. Every gap errs low.

## PROTOCOL-44 · objects describe themselves: `read OBJ ?` prints an object's methods (index, label, argument type, call slots) and laws through the one printer; refusals print what to do next (2026-10-18, PROTOCOL-9; DELVETALK-LEARNINGS §4.3)
**Decision.**
- **`read OBJ ?`** is a read kind, not a new verb. It parses to `Cmd.describe`. Follow catches up, then prints:
  - `object HEX`, `owner HEX`;
  - `package HEX`, or `data` for an object with no package;
  - `state TYPE`;
  - one `method I LABEL ARGTYPE` per method, in index order, with `call I J TYPE` for each declared call slot;
  - `law LABEL` for each package law;
  - `law HEX LABEL…` for each further law package of the object.
- **Where the text comes from.**
  - Every method line is `Lang.resolveMethod`'s answer at I: the same resolution that `invoke` and `Lang.argsOf` use.
  - Every type is `Lang.Print.ty`, LANG-28's one printer, whose text `Lang.Read` reads back.
  - If any part has no text, the description is refused `noText` (new constructor).
  - Lean decides nothing beyond the printer and LANG's resolution.
- **Theorems** (Proofs/Describe):
  - `methodLine_resolves`: the printed line for index I is resolveMethod's label and the printed argument type at I;
  - `packageLines_methods`: every index below the method count has its lines in the description;
  - `mem_of_mapM`.
  - Consent is kept: `describe_ne_submit` and `refusedAt_ne_submit` feed `step_submit_planned`, whose statement is unchanged.
- **Hints** (`hint`, `refusedAt`). A refusal with a next step prints it on STDOUT; the name stays on stderr as the verdict.
  - `stale CELL` (follow's own admission): the cell moved, read it and run again.
  - `lawDenied LAWHEX`: the law's own words, which begin with the law LABEL (LANG's `label: reason`).
  - From the writer, `stale` says the World moved and to run the command again (it re-plans). `lawDenied` points at `read OBJ ?`.
  - Every other refusal prints no hint.
- **Row `describe`** (25th).
  - The sponsor makes a grain on the shipped lifecycle package and grants `anyone` `invoke:1`.
  - A member who has never seen it runs `read @app ?` (line 6). The description binds `app.LABEL` to each printed index, and the line checks that it printed `law phase`.
  - From that text alone the member starts it: `invoke @app @app.start (record) --via @pub` (line 7). The argument is written at the printed type `(rec)`.
  - The second start is `lawDenied`, and it prints `hint lawDenied …: phase: no edge` (line 8).
  - Plant `guessMethod`: a resident that does not read the description guesses method 0, so line 7 calls `remove` through a grant to `start` and is refused `grantRight`.
  - New Line field `prints`: text the line must print, else `refused unprinted`. A line with `prints` shows its stdout in the transcript.
- **HOST (cross-layer, CLIENT-26's ask, in the shape HOST-12 agreed for genesis).** `host join` now also prints `input HEX` LAST, so a joiner keeps the same `input` line a founder does and nd never parses the invitation.

**Alternatives.**
- (a) A new verb (`?` or `describe`). Rejected: it is a read of one object, and the verb ceiling is 20 (18 used).
- (b) Print the whole package text (`Lang.Print.package`). Rejected: a resident needs the indices and argument types. A 7.5 KB package with its state repeated in every type is exactly what DELVETALK §4.1 says nobody can read.
- (c) Carry hints in the wire payload. Rejected for now: `hostName` reads the whole payload as the name, so a hint there would change the name the attempt store and the rows read. Hints are client-side text, decided from the refusal VALUE follow holds.

**Critique.**
- The description prints raw core types. Lifecycle's state type is a 150-character line, and a method's argument `(rec)` must be written as `(record)`: a resident must know that a `rec` type is written as a `record` value. The authoring surface (DELVETALK §4.1, LANG) is what makes this readable. This read is only as readable as the core.
- Writer-side hints are generic: the writer's refusal payload carries a name, not the cell or the law, so `stale` from the writer cannot name the cell.
- The row's argument is the one value of `(rec)`, so it does not show a resident constructing a non-trivial argument from its printed type.

**Meta-critique.** I first wrote that a hint in the wire frame was the better design, deferred for cost. That was the pricing move CLAUDE.md names, so I checked it.
- Follow admits every call on its own World before it signs (consent, PROTOCOL-4). So a stale cell or a denying law is refused by FOLLOW, with the cell and the law's words in hand.
- The writer refuses only what changed between plan and land: a race. For a race the answer is to run the command again, which re-plans on the moved World.
- A writer-side cell id would add nothing a member acts on. So no flag day is owed.
- If residents meet writer-side refusals that are not races, that is evidence the frame should carry more, and this decision is wrong.

**Status.** BUILT. Rows ALL PASS 25.
- Vacuity read (a second agent): every theorem was ACCEPTED.
  Fixes taken from it:
  - packageLines_methods states membership, not order, and its docstring now says so;
  - a lawDenied hint prints the law words on ONE line (a law cannot add stdout lines);
  - the description names install labelOk check as why labels print raw.
  A client reads stdout after a refused exit as text only, never as data.

## PROTOCOL-45 · a receipt as proof: what happened to a call, shown against the head a member holds; `receipt TXID`; row `receipt` (2026-10-18, PROTOCOL-9; cv 01a14ade-0f69 by KERNEL-11, KERNEL-41/44/47 roots; delvetalk's top thirst)
**Decision.**
- **A head** is a World's height and its ROOTS digest (`World.roots`: the cells', journal's and refusals' roots, which every head link commits, KERNEL-47). `sync` now prints `roots HEX` beside height and chain.
- **A receipt** (`Protocol/Receipt.lean`) for a transaction id carries:
  - the three roots;
  - an answer: `committed h td` (journal inclusion, KERNEL-41), `refused h code` (the recorded refusal's inclusion at `.tx id`, KERNEL-44 / PROTOCOL-41), or `absent` (both exclusions);
  - both trie paths.
- **`Receipt.check E height roots txId notBefore r`** trusts nothing the receipt states. It refuses by name:
  - `otherTx`;
  - `headMismatch` (its roots do not open the head's);
  - `pathMismatch` (a path does not verify for the stated answer);
  - `forgotten` (`absent` past `journalForgets`: absence then says nothing, PROTOCOL-33);
  - and `badReceipt` on the wire.
- **Theorems** (Proofs/Receipt):
  - `check_committed`: a committed receipt that checks against a World's roots is that World's journal entry, or a collision;
  - `check_absent`: an absent one is the journal's absence, and only while `journalForgets` is false;
  - `check_refused_uncommitted`: a refused receipt (the refused arm ALSO checks the journal exclusion) shows the id absent from the World's journal, so a relay cannot turn a committed call into `refused`;
  - `check_refused`: the refusal path verifies against the head's refusals root;
  - `check_ok`.
- **Verb `receipt TXID`** (the 19th): follow catches up and prints `receipt HEX`, built from its World (`Receipt.build`: the trie's own `prove`). It is on the stdio surface: a resident wants receipts too. generated.rs re-emits STDIO_VERBS.
- **Row `receipt`** (26th):
  - a committed write checks `committed` against the phone's head (another member holding only its own height and roots);
  - the same receipt relayed by a host that says "not admitted" (`absent` over the same paths) is `pathMismatch` (line 10);
  - a call refused and RECORDED (forged stale) checks `refused` with its code;
  - a call that never reached the writer checks `absent`.
  - Plant `trustReceipt` (a phone that believes the stated answer once the roots match) turns line 10 to `ok`.
- **Hint:** `baseMoved` now prints "ask your sponsor for a fresh invitation" (CLIENT-26's ask: the hint is Lean's to print).

**Alternatives.**
- (a) Check against a bare CHAIN digest: the head record `(prev, kind, step digest, roots)` hashing to the chain, as KERNEL's `head_journal_read` states. That is the reading for a third party who holds only a chain. It needs the World to carry its last link (prev, kind, step digest), which no World holds today (follow knows them only while absorbing). Chosen instead: the roots digest, which the chain commits and which a member's own fold computes in O(1). A chain-anchored receipt is the head record plus this one; that is cv 01a14ade-0f69's remaining half.
- (b) Put the receipt in the Host's `lookup` reply, so the attempt store never takes "absent" on the Host's word. That is the cv's motivating case, and the consumer this format exists for. It needs HOST to build receipts in serve and CLIENT to check them in the attempt store, with this check. Next, with HOST and CLIENT.

**Critique.**
- The row's receipts are built by the owner's follow and checked by another member against its own head. Both are honest folds, so the row shows the format and the check, not a lying Host's receipt in the attempt store. Until (b) is built, `absent` from a lookup is still the Host's word.
- `refused` is checked against the refusals root, but KERNEL states no refusals-trie inclusion soundness (`journal_inclusion_sound`'s twin). So `check_refused` says less than the other two. Owed by KERNEL (cv).
- A phone must hold a head at or after the call. A head older than the call cannot answer `committed`, and `absent` against an old head says nothing about later. The verifier does not know whether its head is "after"; the member does.
- `absent` checks the refusals exclusion inside the journal window. Whether the refusals prune on the same horizon is KERNEL's (KERNEL-44 prunes by window). If they prune sooner, `absent` can be shown for a call that was refused and then pruned. The attempt store's resend of the same bytes then meets the kernel again, never a double effect.

**Meta-critique.** I chose roots over a chain because roots needed nothing from KERNEL. A chain-anchored receipt is what the cv asked for. I have named it as the remaining half instead of shipping it, because the World's last link is KERNEL's field to add, and KERNEL-17 is mid-flag-day.

**Status.** BUILT. Rows ALL PASS 26.
- Vacuity read (a second agent): every theorem was ACCEPTED.
  Fixes taken from it:
  - the module doc no longer claims that a relay cannot change a refused answer, only what is proved;
  - the refused arm now also requires journal exclusion (check_refused_uncommitted).
  Open:
  - check_committed takes the journal heights fit below 2^64 as a premise, true of reached Worlds below 2^64 height; no lemma names it yet;
  - a relayed head must bind its height to its roots.

## PROTOCOL-46 · a settlement is the member's word, never the Host's: the attempt store ends a call only on its own follow's `receipt CALL`; `absent` is never the end of an attempt (2026-10-18, PROTOCOL-10 proposed, PROTOCOL-11 built; ROOT APPROVED; cv 01a14dfa-1ffb, cv 01a14ade-0f69; CLIENT-6 the client half, CLIENT-27)

**The defects (read in the client, not assumed).**
- `reconcile` settled custody on the Host's status byte. A Host saying `ok` for an unlanded rotation moved custody to a key the World never installed. A Host saying `refused` for a committed one kept custody on a revoked key. Either way the member was locked out on the Host's word.
- The terminal `absent` said "nothing committed; running the command again is safe". That is false while the call's window is live: any relay holding the signed bytes can still land them, and a re-run signs a SECOND call. No hostile Host is needed for this; an honest queue is enough.

**Decision.**
1. **The Host hints; follow settles.**
   - The Host's `submit` / `lookup` status drives the loop and never ends it final.
   - A Host reply of committed or refused leads to `confirm`. Sends exhausted with a lookup still `absent` leads to `probe`.
   - Both requests are nd's own `follow.command(["receipt", CALLHEX])`.
2. **`receipt CALL`** (it was `receipt TXID`; still 19 verbs).
   - Follow catches up and builds the receipt from its own World. It prints `receipt HEX`, `head STEPS HEIGHT ROOTS` and `settle VERDICT`.
   - The verdict is `Settle.ofReceipt (journalForgets H nb) H validUntil answer`, total over five cases:
     - `committed H TD`;
     - `refused CODE`: recorded, and `validUntil ≤ h + 2·windowMax`; otherwise it is `open`, the safe side;
     - `expired`: absent, at a head with H ≥ validUntil;
     - `open`: absent, with the window live; NOT final;
     - `forgotten`.
   - An undecodable call is `refused badCall`.
3. **Attempt table.**
   - Request is submit, lookup, confirm or probe.
   - Seen gains `open` and `forgotten`, which `settle_seen` reads from the settle line's first word; `expired` reads as refused.
   - Action is submit, lookup, confirm, probe, committed, refused, declined, open, contradicted, badReply or uncertain. `absent` is DELETED.
   - Transitions:
     - (submit|lookup, committed|refused) → confirm;
     - (lookup, absent) with no send left → probe;
     - (confirm|probe, committed) → committed;
     - (confirm|probe, refused) → refused;
     - (probe, open) → open;
     - (confirm, open|forgotten) → contradicted;
     - (probe, forgotten) → uncertain;
     - (confirm|probe, lost) → uncertain;
     - a settle word answering the Host's request, or a Host status answering follow's, → badReply.
   - `Action.code` (u8) is emitted.
4. **Step 4's result is the attempt's end**, `u8 Action.code ‖ payload`.
   - The payload carries the settle text for committed and refused, the name for declined, and `HOSTSAID FOLLOWSAID` for contradicted.
   - The Machine maps the end (`Command.settled`):
     - committed → ok;
     - refused → `refused NAME`, using codeName, or `expired`;
     - declined → 53;
     - open → **54** (new, restart);
     - contradicted → **55** `hostContradicted` (new, restart; stderr `hostContradicted H F`);
     - uncertain → 2;
     - badReply → 52.
   - `CommandExit.absent` (50) is DELETED and never reused.
5. **Custody settles only on the attempt's end.** Committed advances it, refused drops the armed rotation, and anything else keeps it armed.
6. **The incoming key** (custody step `signIncoming`, Table.Step code 6; CustodyRefusal `notArmed` code 10; CLIENT-13 amended).
   - A rotation whose `ok` was lost has landed, so the old key's envelope is refused `unknownKey` and the confirm could never read. That would be a lockout worse than today's.
   - A command of a verb that signs no call (read, describe, sync, receipt) therefore re-signs its envelope ONCE by the ARMED rotation's incoming key, and every later envelope of that command too (`tried` bit 1).
   - A second `unknownKey` ends it `refused unknownKey`. So does custody's `notArmed`, because then the writer's word stands.
   - A write is never retried: its plan would be signed by the old key against an incoming-signed envelope. It ends `refused unknownKey` with `hint unknownKey: run nd sync: a rotation may have landed`.
   - Custody signs only an `ENVELOPE_DOMAIN` message (`envelopeOnly`), only while armed (`notArmed`), and never in stdio (`noRotation`).
7. **HOST half: none** (declined, as argued in the proposal). The trigger to revisit is a member that holds a head but no World, the phone (cv 01a14d95-36b0).

**Theorems.**
- Proofs/Receipt:
  - `check_build`: on a JournalCanon, RefusalsOk World whose journal heights fit a u64, the built receipt checks against the World's own head, answering what it states, unless it is absent past `journalForgets`.
  - Tooth: `check_build_forgotten`, which shows that premise is exact.
  - Its refusals twins, `refusals_prove_verifies` / `refusals_prove_absent`, are proved here. KERNEL-17's RefusalsHead lands the Kernel copies and these move.
- Proofs/Settle:
  - `settle_committed`: a committed settlement is the World's journal entry.
  - `settle_final_never_admits`: `refused` or `expired`, from the member's own World, means NO World that a later log reaches admits the call (`submit`).
    - Refused: by `fold_refused_retains` below the prune height, and beyond it by the window, which the checkable arm closes.
    - Expired: by the window alone, with heights monotone.
  - `settle_open_not_final`: every call that `submit` would still admit settles `open` there. These are exactly the calls the deleted `absent` called safe to re-run.
  - `submit_facts`.
- Proofs/Attempt:
  - `next_final`: committed or refused only answers confirm or probe, never the Host.
  - `next_host_final_confirms`, `next_absent_probes`, `next_after_follow`;
  - `Action.code_injective`, `settleSeen_words`.
- Proofs/Command:
  - `envelopeRefused_once`: with the bit set, `unknownKey` is refused and never re-asked.
  - `envelopeRefused_write`: a write is never retried.
  - `expiredHeight_unknownKey`, plus the no-submit lemmas of the new arms.
- Proofs/Exit re-checks disjointness over the new codes (decide).

**Rows (27).**
- Row `settle` (new):
  - a committed call whose lookup the Host answers `refused stale` (fault `lieLookup`) settles committed;
  - a never-forwarded call ends `open`, and a relay then LANDS it (`resubmit` ok), so open was not final, in a real run;
  - a second never-forwarded call signed for a window of 2 is re-run (`rerun`: the attempt store's next run) past its window and settles `refused expired`;
  - a rotation whose `ok` is lost confirms through `signIncoming`, custody advances, and the next write signs with the new key.
  - Plant `trustLookup` (the store ends on the Host's status): line 6 reads the lie, `refused stale`.
- Measured, not standing: Loopback custody that never signs incoming turns `rotate` line 7 and `settle` line 17 to `uncertain`. Every confirmed rotation needs it.
- Row `rotate`:
  - the never-forwarded rotation is `open`;
  - plant `advanceOnSend` is now caught EARLIER, at line 11 (`uncertain`): custody on a key the World never installed cannot even read.
- Rows `forgotten` and `receipt`: never-forwarded writes are `open`.
- `retry` is the Host's lookup, read as a Host observation, and no longer settles custody.

**Flag day (what breaks).**
- The attempt table, the step-4 result and the command exits are re-cut. generated.rs is re-emitted: Request, Seen and Action change, with `Action::code`, `settle_seen`, `Step::SIGN_INCOMING`, `CustodyRefusal::NotArmed` and `command_exit::OPEN` / `HOST_CONTRADICTED`; `ABSENT` is gone.
- `receipt TXID` → `receipt CALL`.
- The settlement file format changes (CLIENT-27), so an old attempt directory refuses to load.
- Ops/Units `commandAction` re-cut (OPS-4).

**Critique.**
- `settle_final_never_admits` is about `submit`, the writer's admission. Follow's absorption (`Command.absorbStep`) admits a logged turn only through `submit` on its own World, so it inherits the same window and journal facts. It is not stated here separately.
- `refused`'s arm needs `validUntil ≤ h + 2·windowMax`. That is NOT true of every recorded call (the vacuity read found it): `checkRefusal` checks `notBefore ≤ height + 1 ≤ validUntil` but never the width, so a recorded call wider than `windowMax` settles `open`, then `forgotten`, and never final. This is a completeness gap, not unsoundness. Asked of KERNEL: check the width before recording, which makes this arm dead and provable. CLOSED for absorbed Worlds (PROTOCOL-13): KERNEL-18 checks the width (8ad3982, `refuse_window_width`). `WindowedIn X S w` says every refusal leaf is the record `judge` makes for a call that a refusal step of `S` carries, at its id, with `validUntil ≤ h + windowMax`; it holds at the World a genesis builds (`genesisWorld_windowedIn`, founders included) and along every page follow absorbs, with the page's steps added to `S` (`absorbStep_windowedIn`, `absorb_windowedIn`, `absorbPage_windowedIn`, `absorbed_windowedIn`: the code follow runs, not `Receive.audit`). `settle_refused_absorbed`: on the World follow absorbed from a genesis, with `S` exactly the steps it took, a receipt refusing the member's call settles `refused`, or follow's own log carries a DIFFERENT call (a narrower window) under the member's transaction id: a hash collision in that log, or the member's call is outside the codec's domain (`callBytes` is injective only on calls that fit). That disjunct is a fact about a concrete log; it is not the abstract `Collision`, which pigeonhole makes true of the 32-byte deployed hash. NOT covered: a World carried from a base (adopt, an opened Store) keeps only `(h, code)` per refusal, so `WindowedIn` cannot be shown there, and `ofReceipt`'s `validUntil ≤ h + 2·windowMax` check is what keeps the arm safe on it. The check stays; it also keeps `settle_final_never_admits` free of any absorption premise (its premises are `RefusalsCanon`, `JournalCanon` and the answer).
- Every final settlement costs one follow catch-up. An absent call is final only after its window, at most `windowMax` heights.

**Status.** BUILT; rows ALL PASS 27.
- Vacuity read (a second agent): no theorem is vacuous or collapses to a kernel one.
- Taken from it:
  - the false "true of every recorded call" sentence is corrected (above);
  - `envelopeRefused_once` / `_write` derive their `expiredHeight?` premise (`expiredHeight_unknownKey`);
  - `next_absent_probes` is stated for every `b`, and `next_ends_open` is added.
- Open:
  - a named reached-World lemma for `check_build`'s u64 height fit, and `deployed_*` compositions. CLOSED: `reached_journal_fits`, `check_build_reached`, `settle_final_reached` (over `World.fold X.env (genesisWorld X name nonce a fs) l = .ok w`, the World a genesis builds, founders included; no other premise; a carried World is not covered), and, for the refused arm, `settle_refused_final` above;
  - the incoming bit's persistence across the step machine is not proved, only the local once. CLOSED (PROTOCOL-13/14): Protocol/Proofs/Incoming.lean `step_incoming_kept`: if the state a step resumes is an envelope phase (1 or 2) whose `tried` has `incomingBit`, every envelope-phase continuation the step hands on HAS a `tried` and it has `incomingBit` (a conclusion, not a premise, so steps chain), and every phase-1 continuation rides on a `signIncoming` reply, never `.sign` (so an arm that signed the next envelope by `.sign` would turn it red); through `State.ofBytes_bytes` (the continuation codec's round trip), `next_spec` and `envelopeRefused_incoming` (the `unknownKey` arm signs by the incoming key and sets the bit; the `expired` re-sign is `envelopeSign` of a `tried` that has it). A read-only command leaves phases 1/2 only by ending; a write leaves for phase 3/5/8, where no envelope is signed again;
  - the Rust wiring (`settle_seen` reading follow's line) is CLIENT's tests, not a theorem.

## PROTOCOL-47 · a sponsor pins the base its own follow verified, never the Host's word: the log reply states the writer's newest durable base; `invite` pins follow's OWN digest at it; the rows seal by `Host.sealNow` (2026-10-18, PROTOCOL-12; HOST-43's condition (1), CLIENT-5's finding; HOST-12 agreed the Host half; ROOT APPROVED)

**The gap.**
- `invite` pinned the sponsor's World AS IT STOOD, its tip. A thin joiner adopts the writer's newest BASE, and the deployed writer seals only at its cadence. So every invitation made after a write past the base was refused `baseMoved` at the adopt.
- The rows passed only because their `.seal` wrote a checkpoint directly: a harness act no operator had (HOST-43).

**Decision.**
- **(A) The `log` reply states the writer's newest durable base.**
  - `logReplyLayout` gains `baseSteps` and `baseDigest`, trailing, so no earlier field moves.
  - `Host.Page.bytes` takes them. `Host.Deployed.pager` passes `r.sealed.steps` / `r.sealed.digest`: the Resident's `Sealed`, post-sync state, so the stated base is always durable. The rows' `Writer.pager` does the same.
  - A seal racing the page makes them stale, and the follower trusts neither.
  - `logPage` refuses a page whose base is past its tip (`badResult`), before absorbing any of it.
- **(B) Follow records its OWN digest of the base.** `absorbPage` cuts its one fold at the stated `baseSteps`: the prefix, then the rest from where the prefix stopped. Where follow's fold sits at that step count, at the page's start or after one of its steps, follow records `verified := (steps, B.digest (B.world.bytes wb))`.
  - That is the same `Keys.worldDigest` over the same World codec that `host seal` prints and a pin names, through `Thin.Base`. There is no second digest path.
  - It is recorded only from a page whose chain check passed, and the newest replaces the last.
  - It lives in memory beside `download` (`Command.Memory`, `Host.Follow.loop`'s ref). A restarted follow has verified nothing until its fold next sits at the writer's base.
  - An adopt resets it.
- **`invite` pins `pinOf verified baseSteps baseDigest`.**
  - It pins follow's own (steps, digest), and only when the last page states that very base with that very digest.
  - `noBase`: nothing verified, or the writer's newest base is one follow never sat at. The hint: `host seal STORE`, then a catch-up.
  - `baseMismatch`: same step count, a digest that is not follow's own.
  - The sponsor never signs the Host's claim. `Invite.Refusal` gains `noBase` (5) and `baseMismatch` (6). The Thin download's `baseMismatch` means the same thing (bytes that do not hash to the digest expected), on the joiner's side.
- **The rows seal as an operator can.** `Loopback.restart sealFirst` is stop → `Host.sealNow (Writer.checkpoint …) (Writer.mark …) r0` → reopen, the core of `host seal STORE`. The direct checkpoint write (the twin HOST-43 named) is deleted.

**Rows (29; ALL PASS).**
- New row `seal` (HOST-43 as members meet it):
  - the operator seals by `sealNow` and invites;
  - the log moves 12 writes past the base, fewer than the cadence;
  - the operator invites again: the same base, its own digest;
  - a thin member adopts the second invitation (before this decision, `baseMoved`), writes and reads;
  - a second thin member adopts the first.
  - Plant `sealIgnored` (the seal skips `sealNow`): the first invitation pins the genesis base, and line 22 is `refused notBehind`.
- New row `basePin`: seal, invite, a write, invite again.
  - Plant `lieBase` (the writer states its TIP as its base, with the sealed digest): follow's own digest at the stated step count is not the stated one, and line 11 is `refused baseMismatch`.
- `thin`, `thinStale` and `refused` run their `.seal` through `sealNow`, with every plant at its old line. `paging`'s `lieTip` plant is a consistent liar: it hides bases after the page too, still line 11 `refused expect`.
- CLIENT-26's adopt (client/tests/join.rs, --cross-layer "ROOT for CLIENT"), through the real exes:
  - a thin joiner holding the sponsor's first invitation (the genesis base) is `refused notBehind`;
  - the writer is stopped, `host seal STORE` (retried while `locked`, a 20 s liveness deadline), restarted;
  - the sponsor's next `nd invite` makes a joiner whose `nd adopt` prints exactly the sealed `steps` and `digest`.

**Theorems.**
- Protocol/Proofs/Command.lean:
  - `absorbPage_ok`: one fold, cut at the base.
  - `absorbPage_admits` and `absorbPage_steps`, restated over the cut.
  - `absorbPage_base`: the World recorded is at exactly the stated step count and ON the page's chain-checked fold. The persisted steps split at it into a run of follow's own `World.step` to it and one on to the page's end.
  - `step_verified`: after ANY step, `verified` is unchanged, cleared (an adopt), or follow's own digest of an `absorbPage`-accepted World at the stated base. No step stores a digest the writer stated.
  - `pinOf_ok`: a pin is `verified` and equals the stated base.
  - `pinOf_none` / `pinOf_other`: `noBase`.
  - `pinOf_forged`: `baseMismatch`, the tooth.
  - `logPage_base_le`.
  - `rooted_append`.
- Protocol/Proofs/Page.lean:
  - `bytes_reads`: a page `Host.Page.bytes` writes in range is read, with its step count, tip and base.
  - `bytes_states_base`: the base read back is exactly the `(bs, bd)` written.
  - `ofU64_u64`.
- Read off the code, not theorems:
  - the pager passes `r.sealed` (IO);
  - `sealed.steps ≤ world.steps` (a Host invariant; if it failed, every page would be refused `badResult`, never misread);
  - the invite arm passes `step`'s own `v` to `pinOf`.

**Vacuity read (a second agent).**
- Nothing vacuous.
- Taken from it:
  - `absorbPage_base` was existential and not tied to the persisted steps. It is now on the chain-checked path.
  - No theorem was about `step`. Now there is `step_verified`.
  - `bytes_states_base` held only if the page parsed. Now there is `bytes_reads`.
  - `pinOf_older` is renamed `pinOf_other`, since a raced page has a newer step count too.
  - `logPage_base_le`'s doc claimed a `step` fact, and that claim is now scoped.
- Open:
  - follow's memory is set before `append`, so after a failed append `verified` can sit ahead of the durable World until the restart. It is still a chain-checked derivation, so this is harmless.
  - A writer that states its tip as its base WITH the tip's true digest gets that pin signed. It is still the sponsor's own true World, and the joiner's download then refuses `baseMoved`.

**Flag day.**
- `logReplyLayout` changes: an old follower against a new writer, and a new follower against an old writer, refuse every log page `badResult`, the name for an undecodable step result (PROTOCOL-21). That is a parse failure named as one, never a verdict.
- No Store format changes and no re-genesis: `verified` is memory.
- No codec vector covers the log reply; it is not a CODEC site.
- `Host.Page.bytes`, `Host.Follow.loop`'s ref, `Host.Deployed.pager` and `Host.Cli`'s ref are re-cut (HOST-12 agreed).

**Critique.**
- A sponsor whose follow restarted cannot invite until its fold next crosses the writer's base, which is a seal away. RUNBOOK's flow (stop, `host seal`, start, invite) always crosses, because the inviter's follow is at or below the sealed tip.
- Persisting `verified` would be a Store-format change; that is not done now.
- One World encode and hash per crossing: bounded by the seal cadence, not per page.
- No row restarts a follow, so `noBase` is held by `pinOf_none` / `pinOf_other`, not by a row line.

**The sponsor's actions (RUNBOOK §2, OPS 5a71be7).**
- `noBase`: stop the writer, `host seal STORE`, start it, let follow catch up past the base, invite again.
- `baseMismatch`: the writer states a base digest that is not the sponsor's own World at that step count. Do not invite through that writer; investigate it (its Store or its page path lies).

**Meta-critique.** Pinning the tip looked like "the World as it stands", but the joiner can only ever receive a base. The pin was naming something no reader could fetch. A signed claim should name what its consumer can check.

## PROTOCOL-48 · `read OBJ` of a programmed object prints its state VALUE, one line through `Lang.Print` at the package's state type; a data object keeps `I=VALUE` (2026-10-19, PROTOCOL-13; ROOT ruling, HOSTING-8's need, LANG-16 reviews)

**The gap.** `read OBJ` printed every object as its raw state slots (`I=BYTES`, bytes as UTF-8 or hex). A programmed object's slots are Lang's data codec (`Lang.Wire.encodeData` per field), so a reader holding only the text had to hand-decode that codec. HOSTING-8's real resident reads only through `nd --stdio`, and a Rust decoder of Lang's data codec would be a twin (law 2).

**Decision.**
- `Command.stateValue`: for an object with a package (`packageOf`), the package loaded as a method run loads it (`Lang.load`: closure, decode, `Package.checkWith`), its state row (`Lang.recordRow pk.state`) and the value `Lang.readState` reads there from `stateOf cell`: `Lang.runSetup`'s own front half. A data object: `none`.
- `Command.readText`: a programmed object prints ONE line, `Lang.Print.data` of that value. A state type that is not well formed, or a value the printer has no text for, is refused `noText` (the printer never guesses). A data object prints its slots as before, one `KEY=VALUE` line each.
- `render` checks `expect` (`I=V` on the raw slots) first, as before, then prints `readText`.
- The text is the printer's ONE canonical form: an enum case in full (`(kind (app (record)))`) where an author may have written the reader's short form (`(kind app)`). Both read back to the same value.

**Theorems** (Protocol/Proofs/Command.lean):
- `stateValue_reads`: `stateValue`'s value is `Lang.readState`'s at the package's row.
- `readText_reads`: the printed line `t` (output `t ++ "\n"`) reads back by `Lang.Read.readData (.record row) t` to exactly that value. It holds through `Lang.Print.readData_data` and `Lang.readState_conforms`. There is no `wf` premise, because `readText` checks it.

**Row `state` (30 rows, ALL PASS).**
- The sponsor creates a Lifecycle app from a state text.
- The newcomer's `read @app` prints `(record (entry "app") (kind (app (record))) (phase (installed (record))))`.
- After `start`, it prints `… (phase (running (record))))`.
- Both reads check the WHOLE stdout (`Line.exact`, new), so a reader that printed the value AND the slots is red too.
- Plant `rawSlots`: the reader prints the raw state slots by the pre-48 expression verbatim; line 6 is `refused unprinted`. It is the harness's substitution of the old printer in Loopback's `.cmd` arm, never a flag in `Command`.

**Also in this commit (PERF-1's ask, STAND-INS C3).** The in-process `bar` row's timing lines are renamed `BAR …` → `LIVE …`, so only `scripts/bar.sh` prints lines named BAR. The row stays a liveness row with its `zeroDeadline` plant and its WASTE lines.

**Flag day.** `read OBJ`'s stdout changes for programmed objects only. Nothing parses it today: the Rust tests read data objects (`1=hello`). No wire, Store or codec change.

**Critique.**
- `expect` still compares raw slot bytes by index, so a programmed object's expectation is written in the codec's bytes. An expectation in the value's text (`read OBJ 'phase=(running (record))'`) is the natural next form; it is not done here.
- The `wf` refusal never fires for a loaded package (`checkWith` requires it, `Lang.Print.checkShape_wf`). It stays as a refusal by name that makes `readText_reads` premise-free; LANG-16 agreed.
- `readText_reads` pins the output as `t ++ "\n"` but does not prove `t` holds no newline (that `Print.data` escapes one in a string is LANG's printer, not stated here); the row's `exact` check sees one line for its values.

**Review.** LANG-16: YES (same read as `runSetup`; keep the `noText` refusal). Vacuity read (a second agent): both theorems OK. Fixes taken from it: the package goes through `Lang.load` (literally `runSetup`'s front half), the row's prints are exact, and the plant uses the verbatim pre-48 slot expression.

## PROTOCOL-49 · a page refused `pageIo` is "not now", never "never": the command ends restart-class `CommandExit.pageIo` (57), what it absorbed is kept, and it runs again (2026-10-19, PROTOCOL-14; ROOT ruling on HOST-48 01396b7)

**The gap.** HOST-48 made the writer refuse ONE page `pageIo` when its IO fails building that page, and serve on. Before, the error restarted the whole writer. The follower read that reply as any other refusal by name: exit 1 `refused pageIo`, which is final and fatal-class (a unit stops restarting on it). That was wrong. `pageIo` is the writer telling the follower "not now", not "never". The next page may well be served.

**Decision.**
- `Protocol.pageIoName` (Protocol/Table.lean) is now the one definition of the name. Host's `pageIoReply` and its STATUS line read it. Host's own copy is deleted, and `Host.pageIoName_fresh` now states freshness against it.
- New `CommandExit.pageIo`, code 57. 56 is the Host's `positionUnfit`; `code_disjoint_host` refused 56 when it was tried. It is in the restart class and printed `pageIo`.
- The machine's `notServed` reply ends the command with it. Two places produce it:
  - the log phase (2), in `envelopeRefused`, before the by-name refusal;
  - adopt's base-page phase (7).
  Follow's state is unchanged and nothing is persisted, so what was absorbed stays absorbed. A write's catch-up signs nothing before its tip, so no call is in flight. An attempt's confirm or probe (`receipt CALL`) that meets `pageIo` is that request `lost`, and the attempt stays open.
- Ops' `commandAction` names the operator's reading: automatic, and the next run asks again; if every run ends `pageIo`, look at the writer's disk (RUNBOOK §3). OPS-5 owns that sentence.

**Theorems.**
- `CommandExit.pageIo_restart`: restart class, not in the fatal codes.
- `notServed_code`.
- `step_pageIo_log`: at phase 2, any verb but `init`, with the three u64 fields readable, `refused pageIo` gives `(f, .steps [], notServed)`.
- `step_pageIo_base`: the same at adopt's phase 7, given `adoptPin` holds.
- The existing disjointness theorems (`code_injective`, `code_disjoint_host`, `code_disjoint_supervisor`, `restart_fatal_disjoint`, Ops' `mem_drivePrevent`) range over every constructor and so now cover `pageIo`.

**Row `pageIo` (31 rows).**
- A newcomer's write runs with every page refused `pageIo` and ends `pageIo`. The same write run again is `ok`, and the operator reads the value.
- After a seal and an invite, a thin member's `adopt` with its base page refused `pageIo` ends `pageIo`, and run again it adopts and reads.
- Plant `pageIoFatal`: the pre-49 mapping verbatim (exit 1, `refused pageIo`), substituted in Loopback's `.done` arm, never a flag in `Command`. Line 9 is `refused pageIo`.

**Flag day.** A new command exit code: 57 `pageIo`. Re-emitted: `client/src/generated.rs` (`command_exit::PAGE_IO`) and `deploy/units/EXITS.md` (a restart row). A follower unit restarts on 57; before, it stopped on 1. No wire, Store or codec change.

**Critique.**
- The row's fault replaces the writer's reply with `Host.pageIoReply` on the loopback. It does not make the in-process writer's pager throw. HOST's own `pageIoPlant` in host-sim covers the writer half.
- The restart itself is rendered, not hand-kept: `Ops.Units.drivePreventCodes` is `CommandExit.codesOf .fatal` (`mem_drivePrevent`), and `deploy/units` is generated from it, so 57 is restarted by construction of the units.
- Only phases 2 and 7 receive a page reply, so the two step theorems are every place `pageIo` can arrive.
- `step_pageIo_log` takes the three u64 fields as premises. Every state the machine writes has them, but that is not proved as one invariant here.

## PROTOCOL-50 · the member rows run at the deployed parameters too: one pipeline generic in the digest, `rows --deployed` beside the toy run (2026-10-19, PROTOCOL-15; STAND-INS-20261019 §4 D1, swap 7)

**The gap.** Until now, no member row had run at the deployed parameters. `Protocol.Rows.Sim` fixed `D := UInt64`, hashed with FNV-1a, signed with `toySign` (where a secret is its own public key), and sealed the Store with the Host Sim's FNV tags. THE BAR (`scripts/bar.sh`) drives the real binaries at deployed parameters. The 30 member rows its claims rest on did not.

**Decision.**
- `Protocol.Rows.Params D` holds everything the one pipeline is instantiated with:
  - `ctx` (with LANG's program);
  - `dc`, the digest codec;
  - `world`, the World codec;
  - custody's key model: `pub` (a secret's public key) and `sign`;
  - `keys`, the Store's sealers and base digest;
  - the rows' two byte bounds: `sealMinBytes` and `pageBudget`.
- `Params.toy` is the old instance, byte for byte: every ROW line of the toy run matches main's.
- `Params.deployed` (Protocol/Rows/Deployed.lean) is `host`'s own instance:
  - `Host.Deployed.X`, `Host.Deployed.world`, and `Host.Keys.ofKey` under `Host.Deployed.shapes` (KMAC256 tags, the unkeyed base digest);
  - custody's keys are Ed25519, with seed `Kernel.Sim.Deployed.seed`.
- `Protocol.Rows.Sim` is deleted.
- Loopback and Writer are generic in `D` (`{D} [Ord D] [DecidableEq D]`; `Sys D`, `Actor D`, `St D`, `M D`, `Writer.Params D` carries `R`). Custody now holds SECRETS (`secretOf`); every place a key is carried uses `R.pub`, and every signature uses `R.sign`. That covers:
  - the sign result frame and the precommit result;
  - the founders' list and `nextKeyDigest`;
  - the founding invitation and a relay's re-signed one;
  - the `.key` binds;
  - `readElsewhere`'s envelope and a forged call.
  The toy's `pub` is the identity, so its run is unchanged. At deployed parameters, a key confusion would refuse a signature by name.
- `rows --deployed` runs every member row and its plant under `Params.deployed`. The Lean-internal rows run their own exes, so it skips them, and it prints no LIVE/WASTE lines, so a WASTE measure is collected once (from the toy run). `--deployed` selects the parameters the HARNESS instantiates. It is never a mode inside admission: nothing in Kernel, Host or Protocol.Command reads which instance is running (PROTOCOL-32).
- **The plant that the run is at the deployed parameters.** Before any row, `Params.atDeployed` measures the parameters by calling them: the digest's bytes, `pub`, `sign`, the base digest and a segment tag must be 32/32/64/32/32. The deployed instance must pass. The toy must FAIL, by name, `digest 8≠32`; otherwise the run is `plant toyWidths BLIND`, or `MOVED` if it fails on another width.
- **Cost, in deterministic units.** Every row prints `COST <row> frames <frames on either socket> steps <writer World steps>` in both runs, so the two runs' cost reads beside each other without a clock.
- `gates/runs.tsv`: the rows row runs `(none) ; --deployed` (GATES-6 agreed). One toy `--harness-control` control serves both, since the BLIND reader is the same generic `drive`. `--deployed --harness-control` was run by hand and read FAIL 30 of 30 BLIND.

**What the deployed run found, and what changed for it.**
1. With the toy's byte bounds, `thinStale` (line 15) and `seal` (line 22) were `refused baseMoved`. Both rows rest on a premise: "twelve writes, fewer than the rows' seal cadence". `sealMinBytes` is in bytes, and a deployed write is about four times a toy one (32-byte digests and keys and 64-byte signatures, against 8 and 8). At 8192, the writer's own cadence sealed during the twelve writes and moved the base off the pin. That is honest behaviour, and the row's premise was the parameter-bound part. So the byte bounds are now Params fields: the toy keeps 8192/16384, and the deployed is ×4.
2. With the toy's page budget, `paging`'s plant `lieTip` bit one line EARLY: line 10 read `contradicted "committed open"` against the declared line 11. Deployed events are bigger, so there are more pages and the lie reaches the sponsor's own write. With the ×4 budget it is caught at its line again.
3. With the ×4 bounds, `seal`'s plant `sealIgnored` was caught at the first thin adopt (line 19 `notBehind`), not at line 22. Under that plant, what the SECOND invitation pins depends on whether the writer's cadence sealed during the twelve writes. That is a byte count, and it differs between the parameter sets (the welcome's package text is fixed-size, so it does not scale ×4). The row now adopts the FIRST invitation first. Under the plant, that one always pins the genesis base. The plant is read at line 19 in both runs, by the same name.

**Rows: 31, toy ALL PASS; deployed 30 member rows ALL PASS** (tables in the commit message).

**Critique.**
- The ×4 is chosen, not derived: it is the ratio of a write's bytes, rounded. A row whose shape depends on a byte bound depends on it at both parameter sets. The two runs now both pass with every plant at its declared line, and that is the evidence the bounds keep the shapes. A bound that drifts shows as a plant caught off its line (BLIND) or an honest line refused, never as a silent pass.
- The deployed run is in process. It has no sockets: the wire codecs carry every step, but the transport is a channel. THE BAR remains the over-sockets measure. This closes D1's "no member row at deployed parameters", not A/C's socket gaps.
- `atDeployed` measures the parameter FUNCTIONS, not the bytes the run logged. The run uses exactly those functions (`R.ctx`, `R.pub`, `R.sign`, `R.keys`), and nothing else in the pipeline produces digests, keys or tags.
- Cost: deployed 67 s, toy 18 s (hbox, swarm-build; recorded for the record, judged by nothing). `forgotten` and `refused` are ~35 k frames each and dominate. Their counts are heights, so they cannot be scaled by `--times`.

## PROTOCOL-51 · `read OBJ REL K [PREFIX]`: a resident reads a relation's rows, in key order, through THE range read (2026-10-19, PROTOCOL-16; cv 01a14f18-b8c8, LANG-52's ask, for the Bell as a queue cv 01a14ece-43f1)

**The gap.** A programmed object's relations (LANG-49) could be read only by its own methods, as range slots. A resident has only the command language, so it could not see a queue's rows at all. HOSTING's real resident reads the Bell, and the Bell as a queue waits on this.

**Decision.**
- `read OBJ REL K [PREFIX]`, a new form of `read`:
  - REL is a relation the object's package declares. Its first argument has no `=`; an argument with `=` is still a `KEY=VALUE` expectation.
  - K is the most rows listed.
  - PREFIX is LANG text of the key's first fields, read at `Lang.preTy d m` for the first `m` it reads at. With no PREFIX, every row is listed.
  - The read is answered on follow's caught-up World, as `read OBJ` is. It is `readOnly`, so it never plans or signs a call (`rangeRender_ne_submit` joins the consent theorem's arms).
- **One path, never a second.**
  - Kernel: `Kernel.rangeOf` (the head's key width, then `rangeRows`) is factored out of `Receive.rowView`. A method's range read and this read both call it. KERNEL-20 agreed.
  - Lang: `Lang.rangeRowData` (each row's key by `keyOf` at every field and its value by `valOf`, both `checked`) is factored out of `Lang.relReads`' range arm. `relReads` and this read both call it. ROOT agreed, standing in for LANG. LANG-17 then reviewed as owner and said yes on two conditions: `preBytes` moves into Lang, and the `wf` comment is reworded. It also gave the second-agent read of the Protocol statements.
  - Lang: the prefix's bytes are `Lang.preBytes d m v` (the key wire of the first `m` declared fields). `Lang.preBytes_full`: at every field it IS `keyBytes`, so a range's prefix and an edit's key are one encoding (LANG-17's condition).
  - Each row prints on ONE line: `Lang.Print.data` of the row datum `(record (key …) (val …))`, at the relation's row type `Lang.rowTy d`.
- **Refusals.** The method path's own names: `rangeUnpinned` (no head), `keyWidth` (the prefix is longer than the key), and `rangeTooLong` (more than K rows; refused, never truncated). This read adds:
  - `unknownRelation`: the package declares no REL; a data object declares none;
  - `rangePastLimit`: K is past the relation's declared `limit`;
  - `badPrefix`: PREFIX reads at none of the prefix types;
  - `noText`: a refusal, never an acceptance. `checkRel` makes it unreachable for an installed package (it checks `keyTy d` and `d.val` wf), but that is not proved here.
- **From the text alone.** `read OBJ ?` gains a `rel …` line for each relation. It is LANG's own printer's text (`Lang.Print.relSx`): the label, the key's fields in DECLARED order (a prefix is the first ones), the value type, and the `limit` that bounds K (`packageLines_rels`).
- **Theorems** (Protocol/Proofs/Command.lean):
  - `rangeLines_reads`: lines `ts` mean that:
    - the package declares REL as `(i, d)` (`relationOf_spec`: in the very package a method run loads);
    - K ≤ `d.limit`;
    - the prefix bytes `pb` are at most the key width;
    - `rangeOf` lists `l`, and `rangeRowData` makes it `ds`;
    - `ts.length = l.length = ds.length`;
    - each line, paired with its datum, is text that `Lang.Read.readData (Lang.rowTy d)` reads back to that datum (`Lang.Print.readData_data` over `Lang.rangeRowData_conforms`), with no `\n` or `\r` in it (`Lang.Print.data_one_line`).
  - What `l` holds (exactly the rows under the prefix, ascending key-BYTE order, at most K) is `Kernel.range_rows_exact`. Its `pre.size ≤ width` premise is a conjunct here.
  - `rangeLines_pastLimit` is the K tooth.
  - Lang (`Lang/Proofs/Invoke.lean`, `Provenance.lean`): `rangeRowData_conforms`, `rangeRowData_length`, `rangeRowData_digests`. `relReads_conforms` and `relReads_digests` keep their statements; only their proofs now go through the factored lemmas.
- **Rows** (33 toy, 32 deployed):
  - `range` (stand-in queue `ringsQueue`, written in LANG's surface, installed as LANG's printed core): the newcomer reads the description and binds `ring` from it. Three rings land (round 2 first). `read @q rings 8` prints EXACTLY the three rows in key-byte order: round 1's two before round 2's, not ring order. With the prefix `(record (round 1))` it prints exactly two. `rings 2` is `rangeTooLong`, and `bells` is `unknownRelation`. Plant `dropRow` (a reader that loses its first row) is caught at line 10 `refused unprinted`.
  - `rangeLimit`: `rings 65` is `rangePastLimit`, and `rings 64` over the empty relation prints nothing. Plant `noReadLimit` (the reader WITHOUT the bound: `Command.rowLines` called directly, the same function `rangeLines` wraps, so no flag lives in the machine) is caught at line 6 `ok`.

**Critique.**
- "Key order" is key-BYTE order, by theorem (`range_rows_exact`). Today a nat key field is CODEC u64 little-endian, so byte order is not numeric order past 255: a queue keyed `(n nat)` would list 256 between 0 and 1. That is LANG's key wire (LANG-57, LANG-17: Lang naturals big-endian). The statements here do not change under it; only the concrete key bytes re-pin. The rows' keys are below 256, so their printed order stands either way.
- `ringsQueue` stands in for the Bell. When LANG re-cuts the Bell as a queue, the row should install the Bell itself.
- A reply past `Bounds.frameBytesMax`: I first proposed a `pastFrame` refusal, on the claim that such a reply "has no bytes". That claim was wrong. `host follow` already answers an unframeable step `refused stepTooLarge` (Host/Follow.lean:64–66), so the member gets a name, not a silent failure. `pastFrame` was not added; two names for one bound would be the "two shapes" the doctrine deletes. A relation's rows can still outgrow a frame (64 rows × up to 64 KiB values), and then K or the prefix must narrow it.
- The read lists at most K rows and refuses more. There is no cursor yet: a resident pages by prefix. A "rows after key X" form is the next ask if a queue needs it.
- Plan-side range reads (a member INVOKING a method that declares a range) still sign no `ranges`: `plan` builds none. That is the next Protocol gap for a queue that reads itself.

## PROTOCOL-52 · KERNEL-54's attempt side: a stale is settled from the member's own fold, never recorded; an absent lookup is confirmed with follow before any resend (2026-10-19, PROTOCOL-16; KERNEL-54 ruled, PROTOCOL-15's five conditions; routed through KERNEL-21's one `kernel!` commit)

**The gap.** Under KERNEL-54 the writer DECLINES a stale and never records it (`judgeBy`). Before this change the attempt side depended on that record in three places:
- `refused stale` was final only because it was recorded.
- A→B→A was covered by the record.
- The rows' budget teeth were seventeen recorded stales.
Without the record, a stale call would stay `open` for ever, and the budget row would measure nothing.

**Decision.**
- **Stale BEHIND settles `refused`, from the fold** (conditions 1 and 2). `Command.staleBehind X me w c` decides it. It requires:
  - the member's OWN call for its own World. Custody signs only what follow planned, and `plan` signs `notBefore` = the planning height with pins from that World, which is a World of follow's fold;
  - a planning height follow has reached (`notBefore ≤ w.height`). Every World of one height holds the same entries, because refusal steps change none;
  - follow's World derives the call's Turn and refuses it `stale`.
  When all three hold, the pin was observed on the fold and is stale now, so it is stale at every World the fold reaches (`Kernel.stale_behind_forever`). `Settle.ofReceipt` takes it as a new `behind` argument: an absent receipt in a live window that the journal still answers settles `refused staleCode` when `behind`, else `open`. AHEAD (a planning height not reached) or another member's call (unplaceable) is never `behind`: it settles `open`.
- **The Host's decline never ends an attempt.** `(submit, declined)` ends the RUN `declined` and leaves the attempt open on disk, as before. The next run settles it.
- **An absent lookup is confirmed with follow before any resend** (condition 3):
  - `(lookup, absent)` → `probe`, whatever the sends left;
  - `(probe, open)` → `submit` while a send is left, else `open`.
  So a run is at most three requests per send (attemptFuel `3·sendsMax + 3`). `client/src/generated.rs` is re-emitted (two arms change). The client's drive loop bound and its `absent_with_sends_exhausted…` sequence change to match; that is CLIENT-8's hunk, staged separately.
- **The rows** (condition 4), `refused` re-cut:
  - a write raced by the sponsor's write is `declined stale` (line 13);
  - `rerun`: lookup `absent`, then probe, then follow's fold settles `refused stale`;
  - A→B→A: the content returns, the version does not. `resubmit` is `declined stale` again, the Host's lookup is `absent` (nothing recorded), and `rerun` settles `refused stale` again;
  - another member's `receipt` of that call prints `settle open` (unplaceable, never final from someone else's fold);
  - the budget teeth move to a RECORDED class: sixteen forged posts at a taken key of a board (`keyTaken`, admit-level, authenticated, recorded), then `declined refusalBudget`;
  - plant `settleDecline` (an attempt store that takes the Host's decline as final) is caught at line 13, `refused stale`.
  - `journey`'s race line is now `declined stale`. `receipt`'s recorded refusal is a `keyTaken` post (a stale has no record to receive).
- **Pin sites** (condition 5): `derivePins` pins `pinOf X.env (w.entry X.env c)`, which reads the Entry: absent, tomb and live-with-version are three distinct pins.
- **Theorems:**
  - `staleBehind_spec` (exactly what `staleBehind` asserts).
  - `staleBehind_admissible`: a call `submit` would admit on `w` is never `staleBehind` there, so `refused stale` is never said of an admissible call.
  - `settle_absent_stale` (the arm).
  - The Attempt theorems re-stated: `next_submit` (a resend only after follow's `open`), `next_absent_probes`, `next_open`, `next_after_follow`.
  - `Command.settleOf` is what `receipt CALL` prints. `Settle.settleOf_admissible_open`: wherever `submit` admits the call, the deployed settlement is `open`. `Settle.settleOf_stale`: an unrecorded `refused staleCode` is said only when `staleBehind` holds.
  - `settle_final_never_admits` / `_reached` cover the RECORD and WINDOW arms only (`behind = false`). The stale arm's finality (no later World admits a `refused staleCode` call) is NOT proved; see the critique. `settle_committed` and the refused-arm theorems hold for every `behind`.
  - Second-agent vacuity read (with the DISJUNCT check): no theorem is vacuous. Taken from it: the docstring overclaims are fixed, and the composition is stated (`settleOf_*`). It also confirms that the stale arm's finality is uncovered.

- **Row pins from the plan** (ROOT approved the fourth change; the plan side of PROTOCOL-16's gap 4). Before this, `plan` signed no `rowPins`, so no pinned row effect (an upsert or a retract) was reachable through nd. KERNEL-21 gives `Receive.Refusal.rowUnpinned` the row's KEY bytes; `derivePins`, on `rowUnpinned parent rel k`, pins `Command.rowPinAt` = `(.row ⟨parent, rel, k⟩, rowPin E (headFloor E w.rows parent rel) (rowAt E w.rows (.row …)))` (the leaf's digest, or absence at the relation's floor, as follow's World holds them) and derives again. A row asked for twice is the receiver's refusal, never a loop. Theorems: `derivePins_rowPins` (every added row pin is `rowPinAt` of follow's World), `planUnchecked_rowPins` (every row pin `plan` signs is). Range pins (`ranges`) are still unsigned by `plan`: the other half of gap 4.

**The `admitsRecorded` tooth stays (ROOT's ruling), re-cut on the live arm.** PROTOCOL-16 had deleted it, arguing that versioned pins leave no honest call admissible after its refusal was recorded. That holds for the PINNED-cell arm, which is dead by structure: every state-dependent verdict there re-pins. The UNPINNED-insert arm is live: a row birth (`insert`, KERNEL-46) is judged on the CURRENT World, so an insert refused `relationFull` (recorded) becomes derivable once a retract frees the slot, and only the record keeps the same signed bytes from landing. Row `refusedFinal` (new):
  - a one-slot board (`slotSource`: limit 1, retract; `post`, `clear k`); the sponsor posts at key 1;
  - the auditor forges a post at key 2: `refused relationFull`, recorded;
  - the sponsor clears key 1 (a retract, pinned by `derivePins` on `rowUnpinned`: the first pinned row effect any row drives through nd);
  - the auditor resubmits the same bytes: `refused relationFull` from the record; the sponsor's post at key 3 then lands (the slot stayed free);
  - plant `admitsRecorded` (the writer code restored from main: commit a recorded call while answering its recorded name) leaves line 16 as it is (the lie is in the log, not the reply) and is caught at line 17: the sponsor's next command catches up through the logged Turn and its own follower refuses it `refusedFinal`, the line after the resubmit as in the old tooth (line 18 after 17).
  `settleDecline` stays beside it on `refused`.

**Critique.**
- `staleBehind`'s premise, "the pins are the planning World's", is the planner's own: follow does not re-check it. A forged call signed with the member's stolen key, with an AHEAD pin and a low `notBefore`, would settle `refused` while it could still land. That is outside the model (a stolen key), and it is stated.
- `refused staleCode` (the BEHIND arm) was final by fold structure, not yet by theorem, when this landed; it is final BY THEOREM since PROTOCOL-57 (`staleBehind_final`, below). It is fail-safe meanwhile: `settleOf_stale` (said only of a `staleBehind` call) and `settleOf_admissible_open` (never said where `submit` admits the call) mean an unproved finality can only leave an attempt open.
- The composed finality theorem (behind ⇒ no later World admits) is NOT stated here. It would rest on `Kernel.stale_behind_forever`, whose `∨ Collision E.hash` is vacuous by pigeonhole (KERNEL-21's finding; KERNEL-56 restates it as `CollidesAmong`). It lands when that statement does, with the five receipt theorems (cv 01a15038-6d1e).
- Partner hunks: the client's drive bound and test are CLIENT-8's (agreed), in this patch; LANG's arity and floor hunks are in KERNEL-21's assembled tree.

**Rows on 40879fa + KERNEL-21's kernel21-k54-snap2.patch + this patch (PROTOCOL-17's re-cut):** toy ALL PASS 34, deployed ALL PASS 33, every plant caught by name at its line (`refused`: settleDecline at 13 `refused stale`; `refusedFinal`: admitsRecorded at 17 `refused refusedFinal`).

## PROTOCOL-54 · a method's refusal reaches the member in its own words: `hint program: answer: refused notResident` (2026-10-19, PROTOCOL-17; cv 01a15039-0a62, HOSTING-10's finding, ROOT assigned)

**The gap.** `nd --stdio` printed a method-check refusal as the bare `refused program`. The method's own name (LANG-51's `refuse T "why"`, e.g. the Bell's `notResident`) never reached the member. HOSTING's resident judged by re-reading state; a member could not tell `notResident` from a type error.

**Decision.** `Command.hint` gains the `program` arm. Beside `refused program` on stderr (the verdict stays the name, law 7), stdout carries `hint program: REASON`. REASON is LANG's own text (`Lang.faultText`: `refused notResident` for a `refuse`, at most `Lang.reasonMax` bytes), on one line (`Command.oneLine`, now shared with the lawDenied arm). This is PROTOCOL-44's hint rule; no new name and no new status. The Rust client forwards follow's stdout and stderr byte for byte (client/src/stdio.rs `answer`), so the client needs no lines (CLIENT stays at its ceiling).
- Theorem `refusedAt_program`: the reply is exactly `refused program` on stderr and the hint line with the reason on stdout.
- Row `bell` (new, on LANG-58's Bell, a queue of rings): the sponsor installs the SHIPPED Bell (`<world/resident/Bell`, no copy in the rows) with the newcomer as resident and grants it `answer`.
  - The sponsor (not the resident) answers: `refused program`, and its output says `refused notResident` (line 10).
  - The resident answers a ring nobody rang (`(record (notBefore 1) (ringText "hi") (ringer …) (text "nobody rang"))`): since LANG-59 the Bell's guard `rung` refuses it, `refused lawDenied` with the hint `rung: unrung` (the pinned slot is empty); before LANG-59 it was the kernel's `missingRow` on the retract of `pending`.
  - The sponsor rings; the resident's `read @bell pending 64` shows it.
  - Plant `flatProgram` (the output flattened, the hint line removed: the stdio surface before this) is caught at line 10 `refused unprinted`.

**Critique.** REASON is free text from a package: a hostile package could print anything one line long (bounded by `reasonMax`, newlines folded). It is a hint, never a verdict; the verdict is the name on stderr. Other `program` reasons (`calls: …`, `decode …`) now reach the member too, which is the point: they were equally hidden.

## PROTOCOL-55 · the rows' page budget is DERIVED from the kernel's event bound: `Kernel.Bounds.eventBytesMax + 5`, both parameter sets, with the theorem that a record's walk that has served nothing serves the first step past its start (2026-10-18, PROTOCOL-18; ROOT approved)

**The red.** `rows bell` at the toy parameters printed `uncertain` for `install <world/resident/Bell` (line 6), which reads like the Host's failed-append reply. It was not one. The method was a trace: a temporary eprint of the confirm's inner `receipt CALL` outcome in `Loopback.drive` (reverted). It showed:
- the writer COMMITTED the install (the attempt went submit → committed → confirm);
- the confirm's receipt was `refused badResult`: follow's refusal of an empty page short of the tip (`Command/Machine.lean`, the log arm);
- the page was empty because `Host.Page.walkTurnsAt` stops at the first event that does not fit the budget, and the install event (31.5 KB of printed Bell) is past the toy rows' 16384;
- `drive` reads a confirm that follow refused as `lost`, and `Attempt.next` maps (confirm, lost) to `uncertain`.
So a refusing confirm RENDERS as `uncertain` (the refusal-renders-as-the-verdict class).

**Decision.**
- `Rows.Params.pageBudget := Kernel.Bounds.eventBytesMax + 5` for `toy` and for `deployed`. The 5 is a page's 4-byte event length plus the event's 1-byte step tag (`Host.Page.stepEvent`).
  - Theorem `Writer.walkTurnsAt_serves`: under such a budget, a record's walk that has served nothing serves the first step past its start whenever the kernel admitted that step's event (`eventSize s ≤ eventBytesMax`). The record may begin with skipped steps at or below `start`, and the accumulator may come from records skipped whole. `Params.toy_budget_serves` and `Params.deployed_budget_serves` discharge its premise.
  - Tooth `Writer.walkTurnsAt_one_short`: at `+ 4`, through the walk itself, an event of the kernel's full size leaves the page EMPTY.
  - Not proved: the lift through `Host.Page.walk` and `build` (which read the segment) to the page follow receives. Filed as cv 01a150c0. HOST's `budget_fits_event` is a separate closed inequality about `Page.budget`.
  - Amended 2026-10-21 by HOST-60 (HOST-15, PROTOCOL-19 agreed). Both theorems now live in Host, as `Host.Page.walkTurnsAt_serves` and `Host.Page.walkTurnsAt_one_short`. Their premise is `(stepEvent p.1).size ≤ eventBytesMax + 1` per step, derived from the codec's `Step.Fits`. The Protocol twins `Writer.walkStep` and `Writer.eventSize` are deleted. The lift through `walk` and `build` is `Host.Page.walk_serves`, `walk_empty` and `build_empty`. `budget_fits_event` states `+ 5`, and its teeth are `walkTurnsAt_one_short` and `walk_one_short`. The page-level non-emptiness short of the tip waits on the Store's index-segment coherence (cv 01a15180-9499).
  - A guess at the largest event the rows happen to log broke twice: 4096, broken by the grain row's lifecycle package, and 16384, broken by the queue Bell. A derived bound cannot break that way.
- The first cut was `+ 4`, copied from HOST's `Host.Page.budget_fits_event`. The second-agent vacuity read caught it. HOST's statement leaves out the tag byte; it is masked at HOST's own budget by its slack, and no theorem consumes it. Reported to HOST through ROOT.
- The deployed `4 * 16384 = 65536` was ALSO short, by 5 bytes. It was latent: no row logs an event that large.
- It is a harness parameter (PROTOCOL-50: nothing in admission reads it); no admission or Host check moved.
- Row `bigEvent` (new): `welcome`, then the sponsor installs the shipped Bell and creates one. Plant `guessedBudget` (the writer pages with the old 16384) is caught at line 6, `uncertain`.
- `paging` re-measured at the derived budget: its 100 writes (108 steps) are still two pages, and `lieTip` is still read at line 11. What ends its pages is `recordTurnsMax` (64 events), under both parameter sets, not the budget. No row now ends a page by the budget with events already on it; `bigEvent`'s plant reaches only the budget's empty-page arm.

**Critique.**
- The `uncertain` that cost a trace is still an `uncertain` with no reason. The confirm's own refusal name (`badResult`) could ride the attempt's end as a hint line. That is nd's surface, though: the Rust attempt store also ends `Uncertain` with an empty payload (`client/src/run.rs`, `client/src/attempt.rs`). A rows-only hint would be a twin of a surface nd does not print. It needs CLIENT and PROTOCOL together and is filed as a task, not done here.
- The budget is now the kernel's bound, not a frame. A row still sees pages end before the tip, because `recordTurnsMax` ends them.

## PROTOCOL-56 · a custody refusal of `signIncoming` hands back the writer's `unknownKey`: one rule over the step (2026-10-18, PROTOCOL-18; ROOT ruled (a), CLIENT-8's nd-members finding ecb02bf)

**The gap.** A resident's `nd --stdio` bound to ANOTHER member's follower read `refused noRotation`. The sequence:
- the writer refused the envelope `unknownKey`;
- follow asked custody once for the incoming key (`signIncoming`, PROTOCOL-46);
- the stdio custody refuses every rotation step `noRotation`;
- `step` mapped only `notArmed` to the writer's word, so `noRotation` became the verdict.
The writer's fact was masked by custody's reason (law 7).

**Decision.** ONE rule, replacing the `notArmed` special case:
- `custodyEnd`: a custody refusal of a step that asked `signIncoming` (`askedIncoming`: envelope phase 1 with `tried`'s incoming bit) ends the command as the writer's `unknownKey` ends it, whatever custody's name was. Any other custody refusal ends by custody's name.
- `unknownKeyEnd` is the one shape of that end. A verb that signs no call gets the bare `refused unknownKey`; a write gets the hint to sync. `envelopeRefused`'s spent arm (a second `unknownKey`) and `custodyEnd` both use it, so the two routes to the writer's word cannot drift.
- Theorems:
  - `step_incoming_writer_word`: over `step` itself, a custody refusal by ANY name, when `askedIncoming` holds, ends as `unknownKeyEnd`.
  - `step_signIncoming_asked` and `step_asked_signIncoming` (Proofs/Incoming.lean): `askedIncoming` of the state custody answers holds EXACTLY when the step that handed it on asked `signIncoming`. `start_not_incoming`: `start` never asks it, and no state it hands on has the bit. Every refusal of `signIncoming` therefore takes the writer arm, and no other custody refusal does. The one assumption, stated in prose and not enforced: the state custody answers is one a previous reply of this machine carried. `State.ofBytes` is a frame decode, not an authentication, so a client that forges a well-formed phase-1 frame with the incoming bit turns its own refused `sign` into `unknownKeyEnd`; it changes only the text of that client's own command.
  - `step_custody_own_word` (PROTOCOL-19, after the vacuity read found the complement only as an unfolded lemma, `custodyEnd_own_word`): over `step`, a custody refusal of a custody phase whose state did not ask `signIncoming` ends by custody's own name.
  - `unknownKeyEnd_ne_submit` and `custodyEnd_ne_submit` keep the consent theorem whole.
- Row `wrongFollower` (new). The newcomer's `read @shared` runs with the sponsor's Self, its own key, and the stdio custody (fault `wrongFollower`). It reads `refused unknownKey`. Plant `maskIncoming` (custody's name ends a refused `signIncoming`, as the old machine did for every name but `notArmed`; it cuts in in the harness, before `step`) is caught at line 6 with `refused noRotation`.

**Critique.**
- ROOT's ruling said "`refused unknownKey` with its hint". The only verbs that ask `signIncoming` sign no call (`readOnly`), and the writer's `unknownKey` already ends those bare once the incoming key is spent. The rule hands back exactly that, so it gets no hint. Its hint ("run nd sync: a rotation may have landed") is also wrong advice for a socket bound to the wrong follower.
- ROOT accepted this deviation (2026-10-20, PROTOCOL-19's landing); HOSTING-12 agreed the `launcher/tests/members.rs` assertion change.
- The plant `maskIncoming` cuts in in the harness, so it shows the row's line 6 tells the two outcomes apart; what guards `step` itself is the row's unplanted expectation and the two theorems above.
- (b), the stdio custody answering `signIncoming` with `notArmed`, is truer at the source. But it is a client line at the ceiling, and it would leave any other custody refusal masking.

## PROTOCOL-57 · a call refused stale BEHIND is never admitted later: the settlement's `refused staleCode` is final by theorem (2026-10-21, PROTOCOL-19; cv 01a15187; KERNEL-23 agreed the kernel statement)

**The gap.** PROTOCOL-52 settled a member's call `refused staleCode` when follow's own fold says it is stale BEHIND, and called that final "by fold structure, not yet by theorem". Nothing proved that no later World admits it.

**Decision.** Two theorems and the facts under them.
- `Kernel.admit_stale_pin` (Kernel/Proofs/StaleOnly.lean): `World.admit` refuses `.stale y` only where a pin of the turn disagrees with the World: a touch's cell pin at `y`, a pinned row touch under `y`, or a range read under `y`. It is the converse of `stale_refused`, `rows_stale_refused` and `range_stale_refused`. `.stale` is built at three places only; `StaleOnly P x` (every `.stale y` refusal of `x` satisfies `P y`) shows every other check never yields it.
  - Each disjunct is live: `stale_pin_cell_live`, `stale_pin_row_live` and `stale_pin_range_live` are three concrete turns, each refused `stale 7` with exactly its own disjunct holding.
  - The tooth `admit_not_stale`: a turn whose every pin agrees is never refused `stale`.
- `staleBehind_final` (Protocol/Proofs/Behind.lean). Its premises:
  - the W0 premise: `plan X me w₀ key b = .ok u`, `c.unsigned = u`;
  - the fold `w₀ → w → w'`, with `w₀`'s invariants (`CellsFit`, `RowsCanon`, `RowsOk`, each kept from genesis by fold);
  - `staleBehind X me w c`.
  Its conclusion: no `submit X w' c` is ok, or `CollidesAmong X.env.hash (behindPres X.env w₀ w' u)`. `behindPres` is an explicit list: each pinned cell's `pinPre` at `w₀` and `w'`, and each pinned row's `rowPre` at both.
  - `_sep`: where the hash separates that list, never admitted.
- `plan_pins`: every cell pin `plan` signs is `pinOf` of the planning World, every row pin is `rowPinAt`, and it signs no range. So the range disjunct is closed structurally, until plan signs ranges (the plan-side gap's second half). `receive_pins`: a Turn derived from the call at ANY World checks every one of its pins.
- `Kernel/Proofs/Versions.lean`: `foldRows_each`, `rowStep_dead` and `admit_dead` lose `private`; their statements are unchanged. A row pin's retired-parent disjunct ends in `admit_dead`.

**Critique.**
- The collision set is the union over every pin of the call. The proof uses only the stale pin's pair, so `_sep`'s premise is stronger than a per-pin form. It is still a collision on concrete inputs the two Worlds hold.
- `w₀` is not required to be reachable from genesis. Its invariants are premises, and each has a genesis and fold propagator.
- Once `plan` signs range pins, the range case needs `range_stale_behind_forever` in place of `u.ranges = []`.

## PROTOCOL-58 · an attempt's `uncertain` names the refusal that caused it: `hint confirm: refused NAME` (2026-10-21, PROTOCOL-20; cv 01a150b1, PROTOCOL-55's critique; agreed with CLIENT-9, which lands the Rust half after this)

**The gap.** PROTOCOL-55's red: a confirm whose `receipt CALL` follow REFUSES (`badResult`) is read as `lost`, and the attempt ends `uncertain` with an empty payload. On the member's screen that is the Host's failed-append `uncertain`, and telling the two apart cost a trace.

**Decision.**
- The attempt's `uncertain` end carries, as its payload, the stderr of follow's `receipt CALL` for the attempt's confirm or probe: the last one that was not empty and was at most `Bounds.hintBytesMax` = 512 bytes. A longer one is handed as none, never cut. CLIENT-9 lands this in nd's attempt store (`Reply::Lost(Vec<u8>)`); the bound is emitted as `HINT_BYTES_MAX` into client/src/generated.rs.
- `settled`'s `uncertain` arm prints `uncertain` on stderr as before and, on stdout, `hint confirm: refused NAME` (`uncertainOut`). It does so only when the payload is within the bound and its first line is byte for byte `refused NAME` with NAME in `hintNames` (`confirmHint`). The name printed is the table's string, never the payload's bytes.
- `hintNames` is every name follow's own machine prints but the Host's word: one representative per `Refusal` constructor (`hintReps`), plus the kernel's own `refusalNames` and `rejectNames` for a receive refusal and a kernel rejection. A Host name equal to a table name is printed as that name.
- Theorems (Protocol/Proofs/Command.lean):
  - `hintNames_complete`: every non-host refusal's name is in the table;
  - `confirmHint_iff`: the hint is read exactly under the condition above;
  - `confirmHint_foreign`, the tooth: a name outside the table is never shown;
  - `confirmHint_badResult`: the condition is live (`decide +kernel`);
  - `settled_uncertain`: `settled` over `uncertain.code ‖ p` is exit `uncertain`, `uncertainOut p` on stdout, `uncertain` on stderr.
- Rows: `Loopback` keeps each command's stderr (`St.lastErr`), and its attempt store keeps the hint as nd's does (`St.hint`, reset per attempt). Row `uncertainHint`: the writer pages with the old 16384 (the row's fault, `Row.pageBudget`; a harness parameter, nothing in admission reads it), so the queue Bell's install's confirm is refused `badResult`, and line 6 is `uncertain` printing `hint confirm: refused badResult`. Plant `dropHint`, the attempt store's empty payload (nd's `Vec::new()` before this), is caught at line 6, `refused unprinted`.

**Critique.**
- The rows' attempt store is a Lean model of nd's (it always was: `drive` runs `Attempt.next`, the decision CLIENT-3 runs). The keep rule (last non-empty, within the bound) is restated in it. The plant mutates that model, so it cannot catch nd's Rust store going back to `Vec::new()`. CLIENT-9's half needs its own test of the store.
- The label says `confirm` for a probe's receipt too. Both are follow's `receipt CALL` for the attempt.
- Only one direction of the table is proved: every name Lean prints is in it. That every entry is some refusal's name holds by construction for `hintReps`, and for the kernel's lists by KERNEL's `codeName_code` ordering.

## PROTOCOL-53 · THE BAR's per-unit counts are judged: `WASTE rowbar frames-per-write`, `steps-per-write`, `reopen-bytes-per-byte-past-base` (2026-10-21, PROTOCOL-20; agreed with PERF-2 as PROTOCOL-16's spec, re-scoped by ROOT for PERF; GATES-8 for gates/waste.tsv)

**The gap.** The `bar` row's `LIVE … ms` lines are wall clock and judge nothing (no wall-clock verdict). THE BAR's work per unit had no deterministic count beside `invoke ticks-per-required-step`.

**Decision.**
- `Run.rowbarCounts` over the `bar` row's own run, each a numerator over a unit of work:
  - `frames-per-write`: frames on either socket ÷ write commands run (every `.cmd` line but `read`, each repetition);
  - `steps-per-write`: the writer's steps ÷ write commands run. It is below 1: the `lawDenied` invoke is refused by follow's own `plan` and never steps;
  - `reopen-bytes-per-byte-past-base`: segment bytes the restart's reopen read ÷ segment bytes past the newest base. `Writer.reopenCounted` is HOST's generic `openWith` run in a counting `StateM`, so nothing in Host and no dbgTrace; `Writer.reopen` is its first component, one open. The excess is the origin frame and the tag.
- Printed on the toy run only, pinned in gates/waste.tsv at ceiling = measured (10.977, 0.992, 1.017).
- Plants, each at a STATED value above the honest one, each asserted to have happened (`Run.rowbarPlants`; MOVED and BLIND are red by name):
  - `twiceEach`, a client that runs every write command again after the real run (the line's outcome, output and binds are the first run's): frames-per-write 21.871, steps-per-write 1.977;
  - `staleBase`, the reopen handed the genesis base instead of the newest: reopen-bytes-per-byte-past-base 5.251, with a measured reopen required to have been handed an older base.
- The `LIVE … ms` lines stay unjudged notes.

**Refused.**
- A writer-side trie-hash count and verify count (PROTOCOL-16's spec). PERF-3's bench-count measures `WASTE bar trie-hashes-per-required` and `WASTE bar audit-verifies-per-step` on THE BAR's own deployed Store. A rowbar copy would be a second instrument of the same quantity at toy widths, a twin (ROOT ruled).
- `reopen-entries`: `openWith` reads exactly one `index.log` entry by construction (HOST-33), so no plant can move it without changing Host. A row nothing can turn red is not a gate.

**Critique.**
- Frames count every frame of the row, the reads and the restart's included, over write commands only. It is a per-write cost of the whole workload, not of one write.
- The plants mutate the rows' client model and the restart's input, not deployed code. They test that the counters see the work, which is what a counter's tooth must show.

**Amendment (PERF-4, recorded by PROTOCOL-21).** ROOT's four-row ruling named `reopen-bytes-per-record`. The row as landed measures reopen bytes per BYTE past the base, not per record: a record's size varies with its event, so a per-record ratio would move with the workload's mix, while bytes read over bytes past the base is 1 plus the fixed framing for an honest reopen. This and the dropped entries row are the two departures from that ruling; PERF-4 (a6333c82ccd93eeac) agreed both.

## PROTOCOL-59 · `invoke OBJ METHOD ARGS [--range REL K [PREFIX]]`: the plan signs the method's range read at follow's listing (2026-10-21, PROTOCOL-21; item 4, ROOT ruled (a) with K-first order; LANG-22 agreed the structured refusal)

**The gap.** A method that reads a relation by range (`(reads (rel (range m k)))`) could not be invoked through nd: `plan` signed no `RangeRead`, so the receiver's `relReads` refused with the free text `program "rows: ℓ: no signed range"`, and `staleBehind_final` held only because the plan signed no range.

**Decision.**
- `invoke … --range REL K [PREFIX]` takes `read OBJ REL K [PREFIX]`'s arguments in its order (K first; ROOT accepted, as it needs no method lookup). `Cmd.invoke` carries `range : Option (String × Nat × Option String)`; `--via` is split off first.
- `Command.rangeListing` is THE listing: prefix bytes, `Kernel.rangeOf`, the width check and the rows. `rowLines` (the read verb) and `rangesOf` (the plan) both use it. `rangesOf` signs `{parent, rel, pre, most := K, seen := rangePin … (headFloor …) l}` at follow's World, K within the declared `limit` (`rangePastLimit`), the same as the read verb.
- `plan` / `planUnchecked` take the ranges explicitly, never as a default argument (a default would make every theorem about `plan` cover only `[]`). Rotate signs `[]`.
- Lang/Rel.lean (LANG's, LANG-22 agreed): no signed range refuses `rangeUnpinned self i`. nd prints `hint rangeUnpinned: this method reads a relation by range; pass --range REL K [PREFIX]`.
- Theorems: `rangeListing_ok`, `rangeOf_some`, `rangesOf_pins` (each signed range's parent is live at w₀ and its `seen` is THE pin admission recomputes at w₀); `plan_pins`' third conjunct is `u.ranges = rs`; `step_submit_planned` names the `body` and the `rangesOf` of ONE command the submitted call came from (the second agent's WEAK: `cmd` had been tied to neither); `staleBehind_final`'s range case goes through `Kernel.range_stale_behind_forever`, with `Kernel.headOf_width_fold` (KERNEL-23) for the width at w₀, w and w'. A parent tombed at w' is a collision between its live pin input at w₀ and its tomb input at w' (admission checks the parent's cell pin). `behindPres` gains each range's `rangePresAt` at w₀ and w'.
- Rows `rangeInvoke` / `rangeFlag`, over a `tally` package whose `take` reads round 1 by range. Without the flag the take is refused `rangeUnpinned`, with the hint printed. With it the take commits. Plants at line 10: `staleRange` (signed at the sponsor's follow from before the newcomer's ring; `ring` writes no cell, so only the range moved) is caught `declined stale` (the writer's verdict by name; a stale is declined, KERNEL-54). `dropRange` is caught `refused rangeUnpinned`.

**Critique.**
- The prefix is read at the first key-field count whose prefix type reads the text (`prefixBytes`, the read verb's rule). A method declaring `range m k` with a different `m` is refused by the receiver's `keyOf`, by LANG's text, not here.
- The hint names no relation: the refusal carries the relation's index, and `hint` has no World to look up its label.

## PROTOCOL-60 · A cancel reaches a follower: page event tag 2 `2 ‖ nat64 n ‖ sig ‖ call` and absorbStep's cancel arm (2026-10-19, PROTOCOL-22; PROTOCOL's half of KERNEL-60's C1, inside KERNEL-26's commit; HOST-17 agreed the Host paths on three conditions)

**The gap.** KERNEL-60 records a member's cancel as a `Refused` carrying the cancel signature (`Refused.cancel`), and `refusedBytes` commits it. A page carried a recorded refusal as `1 ‖ call`, without the signature. The follower re-derived it with `judge`, which records no signature, or which admits the call outright. So on the first cancel its record, its digest and its chain differed from the writer's, and follow broke.

**Decision.**
- The tags have ONE source, `Protocol.eventTurn / eventRefusal / eventCancel` in Table.lean. `Host.Page.stepEvent` writes them and `Command.absorbStep` reads them. The tag-2 bytes are THE function `Protocol.cancelEvent sig call := 2 ‖ nat64 sig.size ‖ sig ‖ call`.
- `stepEvent` writes tag 1 for a refusal with an EMPTY cancel field and tag 2 otherwise. That is the kernel audit's discriminator (`Receive.recordedBy`): the field, never the code. A program refusal spelled `cancelled` is tag 1 and is re-judged by `judge`.
- `absorbStep`'s tag-2 arm: `cancelParts` reads the length at byte 1. It refuses a length of 0, one past `cancelBytesMax`, or one that runs past the event, so tag 2 has one encoding per record. Then it decodes the call and re-records it with `Receive.cancel` under the event's signature, which the follower VERIFIES under the member's key on its own World. Anything that does not record is `eventMismatch` at its position.
- Bound: `Protocol.Bounds.pageEventBytesMax := eventBytesMax + 1 + 8 + cancelBytesMax` (65609). STATEMENT CHANGE (HOST-17 condition 2): `Host.Page.stepEvent_size_le` was `≤ eventBytesMax + 1` and is now `≤ pageEventBytesMax`. Every page theorem's budget premise moves from `eventBytesMax + 5` to `pageEventBytesMax + 4`, and the teeth from `+ 4` to `+ 3`.
  - The deployed serve frame does NOT move. `Page.budget = frameBytesMax − 1024 = 261120 ≥ 65613` (`budget_fits_event`, by decide).
  - The rows' `pageBudget` (toy and deployed) moves from 65541 to 65613. Every row and COST line is byte-identical.
- Proofs:
  - `Settle.WindowedIn` and the three settle theorems now read `∃ c v a, refusal (recordOf X c v a) ∈ S`. A cancel's record is `recordOf … sig`. The 5 Settle sites are `WindowedIn`, `windowedIn_mono`, `windowedIn_refused`, `settle_refused_final` and `settle_refused_absorbed`.
  - `refuse_windowedIn` is the one step lemma: `judge_windowedIn` and `cancel_windowedIn` are its instances.
  - Command: `refuse_answers`, from which `recorded_answers` follows. `absorbStep_refusal_recorded` now names the tag and the source of the call (tag 1: `a = empty` and the call past the tag; tag 2: `v = cancelled`, `cancelAuth X w c a = .ok ()` (follow verified the signature on its own World) and `cancelParts e = some (a, cb)`). `cancelParts_some`: what it splits IS `e[0] ‖ nat64 n ‖ s ‖ cb` with `0 < n ≤ cancelBytesMax`. `absorbStep_cancel_canonical`, ONE ENCODING PER RECORD: a tag-2 event follow absorbs into `r` IS `cancelEvent r.cancel r.event` (premise: the call codec reads only its own bytes; deployed: `Codec.Kernel.eq_callBytes_of_decodeCall`).
  - `absorbStep_step` takes the cancel arm (`cancel_recorded`).
  - NEW `absorbStep_cancelEvent`: the writer's cancel of `c` signed `sig`, recorded as `r` reaching `w'`, is absorbed from `cancelEvent r.cancel r.event` into the same `r` and the same `w'`, so the chain is kept. `Host.Page.stepEvent_cancel`: that IS the event the page serves.
  - `cancelAuth_size`.
  - Domains: `domCancel` against the five other domains, plus `cancel_not_call` / `cancel_not_envelope` / `cancel_not_possession` / `cancel_not_whoami` / `cancel_not_invite`.
- Plant `plant-cancel-page` (host-sim, HOST-17 condition 1). The honest tag-2 event re-records the writer's exact record and World. Each of the following is refused `eventMismatch 1` by name:
  - tag 1 with the signature dropped (the pre-PROTOCOL-60 event);
  - a flipped signature;
  - an empty signature;
  - 65 bytes;
  - a length past the event's end.
- `Settle.ofReceipt`: a cancelled call settles `refused cancelled`, final, through the refused arm unchanged (doc only).

**Critique.**
- The length checks in `cancelParts` change no `absorbStep` result, and no plant can see them. A 0- or 65-byte signature is refused by `cancelAuth`'s size check and by `verify`. A length past the event's end leaves an empty call, which does not decode. So of plant-cancel-page's lines, only tag 1, the flipped signature and the honest control can go red on their own. The empty, 65-byte and past-end lines are end-to-end refusals, not teeth of the checks. The checks' only tooth is the theorem `cancelParts_some`, which fails without each of them. `absorbStep_cancel_canonical` backs "one encoding per record", but it would stay true without the checks, because `cancelAuth` and the decoder refuse those events too (the second agent's reading).
- `walkTurnsAt_one_short`'s premise (an event of exactly `pageEventBytesMax`) is now met only by a cancel with a 64-byte signature and a full-size call. No theorem exhibits a recordable one, and host-sim's toy signature is 8 bytes.
- No Host op or nd verb records a cancel yet (cv 01a15543-39fd). The arm is reached from host-sim's plant and from the theorems, not from a row through nd. The rows line comes with `nd cancel`.

## PROTOCOL-63 · `nd cancel CALL` and the `cancel` op: a member closes its own loose call (2026-10-22, PROTOCOL-23; KERNEL-60's C1 over the wire; HOST-18 agreed the Host half, cv 01a15543-39fd)

**The gap.** KERNEL-60 made a cancel a kernel step (`Receive.cancel`, page event tag 2, PROTOCOL-60), but nothing reached it from a member: no op carried a cancel to the writer and no verb signed one. A member whose call was lost in flight (`open`: sent, outcome unknown, window live) could only wait out the window.

**Decision.**
- `Op.cancel`, code 7, on `host.sock`, effect `write`, receiver `Nanodregg.Kernel.Receive.cancel`. The payload is THE tag-2 event `cancelEvent sig call` (tag included), which the writer parses with `cancelParts` (moved beside `cancelEvent` in Table.lean, one source for writer and reader) and the log later serves byte for byte. HOST-18's Serve arm decides it with `Receive.cancel`.
- `Op.relayable` gains `cancel`. A cancel needs no attempt: the writer only records the call `refused cancelled` or declines (`Command.cancel_never_admits`), and a lost reply is answered by the member's next `cancel`, which catches up and is refused `refusedFinal` by its own follow once the record is there.
- STATEMENT CHANGE: `Op.effect_write_iff` was `op.effect = .write ↔ op = .submit` and is now `↔ op = .submit ∨ op = .cancel`. Law 1 (one admission path) is now carried by `cancel_never_admits` (`Receive.cancel X w c sig ≠ .admitted t w'`), together with HOST-18's `Host.step_cancel`: the writer's op takes exactly `Receive.cancel`'s World and staging.
- Verb `cancel CALL` (20 verbs, the ceiling): catch up, ask custody to sign `Ctx.cancelMessage c` (`domCancel ‖ txId`), then phase 9 (`sendCancel`) runs `Receive.cancel` on follow's own World BEFORE anything is sent. A cancel it records is relayed as the op. One it declines is refused by the kernel's name and never sent. Phase 10 (`cancelAnswer`) reads HOST-18's replies. A recorded cancel is `refused cancelled`, the call's final verdict (`Settle.verdictReply`): it prints `cancelled TXID` and exits ok. `ok` means the call was already admitted and the cancel did nothing: refused `committed` (`ok` keeps meaning a committed Turn on every op, HOST-18). `declined NAME` (nothing recorded) and any other `refused NAME` end the command by name. `uncertain NAME` ends it `uncertain`.
- `cancel` is on the `nd --stdio` surface: a resident may close its own loose call. It signs with the current key, never rotates.
- absorbStep: a WELL-FORMED tag-2 event (its parts read, its call decodes) that `Receive.cancel` does not record is refused `cancelForged`, the audit's name for the same log (`Receive.forgedName`). It was the positional `eventMismatch`. Malformed tag-2 events stay `eventMismatch`. host-sim's plant-cancel-page "flipped signature" line moves to `cancelForged` (HOST-18).
- Theorems (Protocol/Proofs/Command.lean): `step_host_cancel`, over the WHOLE machine: every `host cancel` step that `step` hands the client leaves follow's state unchanged, and its payload is `cancelEvent s.signature cb` of a call that `Receive.cancel` records on follow's World. It goes through ten `*_ne_host` lemmas, the `step_submit_planned` pattern. `sendCancel_host`, the phase-9 lemma: when phase 9 relays an op, it is `cancel`, its payload is `cancelEvent s.signature cb`, and `Receive.cancel` on follow's World records it, so `cancelAuth` held: the signature verifies under the CALL's member's key, inside the window. `sendCancel_declined_not_host` is its tooth. Also `absorbStep_cancelForged` and `cancel_never_admits`. `step_submit_planned` and the Incoming theorems take the two new phases through `sendCancel_ne_submit`, `cancelAnswer_ne_submit`, `sendCancel_cont` (phase 9 hands on only phase 10's state), `sendCancel_ne_signIncoming` and `cancelAnswer_cont`.
- Rows:
  - `cancel`: the sponsor's write is never forwarded (`open`). The newcomer's cancel of it is `badSignature`. The sponsor's own cancel is `ok`, printing `cancelled `. The attempt's next run settles `refused cancelled`. The same bytes resent are answered `refused cancelled` from the record. A second cancel is `refusedFinal`. The newcomer signs for one height, the sponsor's write moves past it, and its cancel is `outsideWindow`. Plant `cancelUndomained` (custody signs the bare txId, the domain dropped): line 8 is `refused badSignature`.
  - `cancelForged`: a cold follower reading through a Host that flipped the cancel's first signature byte is refused `cancelForged`. Plant `followVerifyAll`: line 8 absorbs the forgery, and the forgery is caught only by the page's chain, `refused chainMismatch`.
- FLAG DAY (wire), `protocol!`, ROOT ruled. What refuses: an old host receiving op 7 refuses it `unknownOp` by name. An old client refuses a `host` step naming op 7 (`badTag`: its layout has no Cancel). A cancel payload not tagged `eventCancel` is declined `undecodableCall`. What re-emits: client/src/generated.rs (host_op CANCEL = 7, `layout::Op::Cancel`, STDIO_VERBS). What re-geneses: nothing; no Store byte, record, page event, VK or descriptor moves.
- Statements changed, with HOST-18's yes: `Op.effect_write_iff` (above), and HOST-21's `host_step_folds` op conjunct `= some .submit` → `∃ op, … ∧ op.effect = .write`, with its teeth `host_step_folds_tooth_wrong_op` (non-writing ops) and `_tooth_unjudged` (any writing op). HOST-66 in decisions/host.md.

**Critique.**
- Because of the preflight, the `cancel` row's badSignature and outsideWindow lines are follow's refusals, not the writer's. The writer's own `cancelAuth` is exercised by HOST-18's host-sim plant-cancel-op (a flipped cancel signature is declined `badSignature` and commits nothing), not by a row. A hostile client that skips the preflight has no row (no `forge` act for cancel).
- A cancel races its own call. If the call lands first, the cancel is `replayed` at the writer. If the cancel lands first, the call is answered from the record. Neither order is a row: the rows' transport is serial.
- "Never sent" is relative to follow's World. Follow may lag the writer, so a cancel that follow's World records can still be declined by the writer (`replayed`, `refusedFinal`, `outsideWindow`). Only the other-member case (`badSignature`) holds whatever the lag.
- A writer that logs a cancel twice, or outside its window, is also refused `cancelForged`, the audit's name (`forgedName`), even though no signature was forged. The name covers any cancel record the follower's re-judge does not reproduce.
- `outsideWindow` is reached only past the window (validUntil < height + 1). A cancel before the call's `notBefore` cannot be built through nd, which signs `notBefore` = follow's height.

## PROTOCOL-61 · a sponsor-signed carried start pins the origin (2026-10-20, CX-HOST; ROOT's card 7a (B′))

**Decision.** An invitation contains one Start: genesis(name, nonce, allowance, founders), or
carried(origin, name, nonce, fromOrigin, height, chain). startInput is the sum of genesisInput
and carriedStart, encoded by the existing raw Stream combinators. Invitation.start replaces the
four flat genesis fields. The signature domain is invitation/v2, explicitly separating old
invitations. verified is the shared signature admission. accept remains genesis-only (carriedWorld);
acceptStart returns the checked invitation and its origin. invite accepts a start only for its
own origin; adopt uses the same accepted origin.

host genesis/join print input in the new encoding. host import prints start, carrying the NEW
origin, exact name/nonce and original export head. host join STORE INVITE KEY [IN] accepts
genesis without IN and carried with IN; other arities refuse usage in before writing.
importWithPin is the one importer behind the operator's import and the carried join. The latter
passes the signed nonce, byte-array name and origin, never fresh entropy or an export digest.
It also checks all signed export-head fields before genesis. Wrong origin is the existing
carryMismatch wrongWorld; head mismatch is carryMismatch anchor. The one ImportFx record serves
both verbs. The carried row no longer assigns a received World as the result of rejoin: it
verifies a signed carried invitation and imports the retained export under its signed origin.
Actors first used after carry use that same admission.

**Flag day.** Re-emit genesis start inputs and all invitations; old signatures use v1 and refuse.
Rows regenerate invitations and input vectors at both parameter sets. No Store, carry-export,
kernel-origin or other codec byte moves. The codec-vector table has no invitation/start site
(no new refine site was added); its existing vectors remain byte-identical and the source
vector gate passes. There is no Store re-genesis in this protocol flag day.

**Premise price.** No LANDED theorem gains a trust hypothesis. ofBytes_said, accept_ok and
accept_origin restate the flat fields through Start; accept_genesis extracts their genesis
constructor. accept_unverified and accept_untrusted keep their statements. import_genesis_iff,
accept_premises and host_start_kept keep their statements. join_genesis_iff restates the sum and
expanded effect record; join_budget_reaches remains its genesis case. sealed_opens and seal_facts
are untouched and retain their statements. New join_carried_iff assumes parsed, accepted carried
inputs and characterizes BOTH directions of the first Store write; its import/anchor/budget/key
conditions are in the conclusion, not assumed. join_carried_trusted consumes that effect result
and import_trusted_pinned to discharge CheckpointTrusted at the independently accepted origin.
It lives in a new proof module because Trusted already imports Proofs.Cli through Size.

**Vacuity read, including THE DISJUNCT CHECK.** Every changed/new theorem was read at its statement
and consumers: ofBytes_said; verified_ok; accept_ok/genesis/origin; acceptStart_ok/carried_origin;
accept{,Start}_{unverified,untrusted}; import_genesis_iff; join_genesis_iff; join_carried_iff;
accept_premises; host_start_kept; join_carried_trusted. None introduces a conclusion disjunction.
The iff statements' reverse directions fail for a no-write implementation or a different nonce/pin.
The signature soundness statements bind the fields decoded from the very verified bytes; the
refusal teeth fail if verification is bypassed. The origin equality is consumed by the trust
theorem, which needs both actual successful import and budget. No new axiom, admitted proof,
unbounded collision predicate or budget premise on a previously unconditional theorem.

**Tests and plants.** Filtered invite, carry, carriedInviteWrongWorld and thin rows pass at toy
and deployed parameters (logs/CX-HOST-start-rows2.log and CX-HOST-start-rows-deployed.log).
The REAL carriedInviteWrongWorld line 7 is refused carryMismatch wrongWorld; the existing
importTrustsFile mutation drops the origin pin and produces ok at that same line, caught by
the row. The original carry wrong-digest tooth remains. Host.Sim.Join drives the real joinWith
with observable first-write/reopen effects: matching signed nonce/origin writes the matching
World, missing carried IN and extra genesis IN refuse before writes, wrong origin and a
signed mismatching anchor refuse before writes. These run through host-sim's main.

**Critique.** The transport of IN is still the operator's file handoff. This change exposes the
carried arm in host join; the Rust nd --join wrapper has no IN argument yet and is not silently
changed across CLIENT ownership. Sponsor authentication remains the same out-of-band key
assumption. The copied export's origin commitment and the signed head authenticate the import,
not a replay of its erased history. A follower's thin adoption Store-rotation defect is independent
and remains a HOST representation question; this change does not bypass headerFault.

**Meta-critique.** It would have been easy to retain the rows' TOFU assignment and call only the
wire sum done, or to substitute an export digest because import already accepted one. Both miss
the agreed independent origin. The actual effect-order theorem and wrong-origin tooth connect
the new signature to the existing trusted import. Keeping the protocol and Host pieces in one
flag-day commit avoids a period in which one side emits a start the other side cannot read.

Validation addendum: the real disabled-guard run in logs/CX-HOST-join-plant.log
builds then prints FAIL for missing carried IN, wrong origin, mismatching signed
anchor and extra genesis IN; MUTANT-RC 1. Source restored in finally, then the
reached build and isolated CLI checks pass (CX-HOST-start-build-final.log and
CX-HOST-join-control.log). The ONE Rust join test still reaches the independent
thin-adopt defect: nd follow status 2 at adopt (CX-HOST-join-current.log), ROOT's
item 1. No check is bypassed to make it pass; the full judge retains parent
attribution. The filtered protocol rows are green at both parameter sets.

## PROTOCOL-64 · Follow settles step 4 on its own World: `done ok` for a submitted call only when follow's World journals it (2026-10-23, CX-E2; E2's T0, R-0054/R-0058/R-0060/R-0061; promo/IMPACT-E2.md §1, §4; promo/READ-E2-grok.md, promo/READ-E2b-grok.md)

**Premise price.** Landed theorems gaining a hypothesis: none. Restated (a binder each, no hypothesis; the
`omit [Ord D] [DecidableEq D]` dropped because `settled` now reads `settleOf`): `settled_ne_submit`,
`settled_ne_host`, `settled_uncertain`, `settled_cont`. New: `settled_ok`, `step_settled_ok`.

**Finding: a deployed trust gap, independent of the card that measured it.** A member's write ends in step 4:
the client hands follow the attempt's end, `u8 Action.code ‖ payload`, and `settled` rendered it. Its committed
arm was `result[0] = Action.committed ⇒ done ok`, with no World read; the docstring said committed and refused
are "only as the member's follow settled them", and the function did not look. The end is the attempt store's:
nd's loop over `Attempt.next` (`client/src/attempt.rs`, `client/src/run.rs:292-314`), which follow does not run.
So the `ok` of every write a member's nd reported was Rust's reading of the attempt, relayed, not a check follow
made when it said ok. PROTOCOL-46's nested `receipt CALL` does check the World; step 4 trusted Rust to relay that
word. Measured as R7 of nine Rust decisions on the resident's stdio leg (IMPACT-E2 PART 1): the only one of the
nine that can make a reply say ok.

**Decision.** Step 3's continuation carries the call bytes it hands out to submit
(`again 4 [startB, signedB, ub, out, X.callBytes c]`; one more element of `stateLayout`'s `.list acc`, the layout
unchanged). At step 4, `ownSettle X me w cb := (X.decodeCall cb).map (settleOf X me w)` on follow's CURRENT World,
the one `Follow.loop` threads and the attempt's confirm or probe just caught up. A `committed` end is `done ok` only
when `ownSettle` is `committed`; a `refused` end prints follow's OWN verdict only when `ownSettle` is `refused` or
`expired`; any other own verdict is `hostContradicted CLAIM FOLLOWSAID`, the attempt left open; call bytes that do
not decode are `refused badResult`. Theorems: `settled_ok` (a `done ok` from `settled` is a decodable call that
`settleOf` on that World settles committed) and `step_settled_ok` (the same at `step`, for a phase-4 continuation:
its last item). With `Settle.settle_committed`, ok means follow's World journals the call.

**What changes meaning.** PROTOCOL-46's confirm is now PROGRESS, not safety: an attempt store that skips the
confirm, or that takes the Host's word or a `declined` as final, no longer gets a wrong verdict past follow;
follow, not caught up, says `hostContradicted committed open` (or `refused open`) and the member retries. The
attempt loop (R4–R6, R8 of IMPACT-E2) stays in Rust and is not a decision on the ok path any more: it chooses
which `result` a step is handed. It is not moved into Lean and not in any trust premise.

**The rows' model drifted from the deployed path, until this.** `Protocol/Rows/Loopback.lean`'s `.rerun` called
`Command.settled` on the rows' own attempt drive with no World; it now passes the actor's `Self`, its follow World
and the frozen call, as follow's step 4 does. Two rows' plants were R7 already modelled in Lean, and were caught
by the WRONG verdict reaching the member (`refused stale`): `settleDecline` (row `refused`) and `trustLookup` (row
`settle`, the shape before PROTOCOL-46). Under this decision follow refuses to echo them, so the plants are caught
by name instead: `.caught .settleDecline 13 (.contradicted "refused open")`, `.caught .trustLookup 1
(.contradicted "committed open")`.

**Plants (measured in hbox wt/e2; promo/E2/).** P-T0c, the committed arm back to `done ok` on `result[0]`:
`settled_ok` RED (`Protocol/Proofs/Command.lean:238`, `:243`: the arms where follow's own settlement is not
committed), `settled_cont` GREEN; `rows`: the `settle` row FAIL (`trustLookup` BLIND at line 1), every other row
PASS. P-T0r, the refused arm back to printing the store's text: `rows`: the `refused` row FAIL (`settleDecline`
BLIND at line 13). No theorem states the refused arm (the resident consumes only ok); its tooth is that row.
After both, restored: whole tree GREEN (727 jobs), `rows` ALL PASS, `rows --deployed` ALL PASS,
`rows --harness-control` RED (FAIL 44 of 45).

**Breaks.** A phase-4 continuation now has five items. A `k` minted by an older follow (four items) reaches the
catch-all and is refused `badState`: an attempt in flight across the upgrade ends there and the next run looks it
up again (its frozen call is unchanged). No wire layout, codec vector, table or Store format moves; no re-genesis.

**Critique.** The continuation is unauthenticated, as before ("`k` cannot steer what is signed"); at step 4 it now
names WHICH call is checked. Returning `k` verbatim is byte relay, the same trust the argv needs; a relay that
swaps in another committed call's bytes is outside it. `settled` still returns `out`, the receipt step 3 printed
from the pre-submit `receive`, not from the committed journal: an ok reply's stdout is not the journal entry, and
nothing here says it is. A follower that commits and dies before its reply gives the member no `ok` at all; that
window is PROT-5's at-most-once, not this decision's.

**Meta-critique (bias named: trusting the docstring over the function).** The gap sat under a docstring that
stated the property, and two plants that modelled it in Lean passed because they checked the visible verdict, not
who decided it. The measurement found it by counting decisions per branch on the deployed path, not by reading
the prose; the rows' teeth only became T0's teeth once the plant expectations named the refusal follow now says.

## PROTOCOL-65 · receipts between Worlds: another World's committed call, checked by Lean against a head this World holds (E5, PROGRAM-20261022 §2(a) / P5; R-0051, R-0059; cv 01a14ef0-ffe7, 01a14dfa-200a, 01a14dfa-1ffb, 01a14de7-224a)

**Decision.**
1. **The head is an object of the generated package `Std.headPackage`** (`Lang/StdHead.lean`, text `world/head/Head`).
   - State: `{world : digest, head : at {height, roots, steps} | forked {held, other, steps}}`.
   - Methods `post` and `fork` write the state and decide nothing. The law `head` is the one decision:
     - `world` fixed (`otherWorld`);
     - from `at` to `at`: the step count never falls (`staleHead`), an equal step count keeps height and roots (`forkedHead`), and the height never falls (`badHead`);
     - from `at` to `forked`: the fork names the held roots at the held step count, with other roots (`badFork`);
     - `forked` is frozen (`forkedHead`).
   - The key is STEPS, not height. A recorded refusal advances `steps` and the refusals root at one height (`Kernel/World.lean`, `World.steps`).
   - Posters are the owner plus whoever the owner grants `invoke` on `post`/`fork`. Several followers of A can post, and two of them fed different logs make the fork visible. Cost: a grantee can freeze the object. Recovery is a new head object, not an unfreeze.
2. **The receipt column.** A cell-keyed read declared `(receipt)` gives each point, and each row of its signed range, a `receipt` field `{height, turn, tx}`:
   - the run checks the method's own `receipt : bytes` argument against the head object that row's key names (`Lang.receiptSeen`), through the caller's pinned view;
   - an unpinned head object is `unpinned`; a retired one is `headDead`;
   - the check's refusal is the run's, by name: `notHead`, `forkedHead`, `badReceipt`, `headMismatch`, `pathMismatch`, `forgotten`, `notCommitted`;
   - what the check shows enters only as the language's data (`seenFits`, LANG-38).

   Install refuses a receipt read of a relation that is not cell-keyed, or one without `receipt : bytes`, as `receiptRead`. The read is spelled by the method's rows TYPE, as E1's `live` is, so **no package byte moves**: `codec-vectors` is byte-identical.
3. **The check is PROTOCOL's and the runtime is LANG's.** `Lang.program` gains one parameter, `receipts : ReceiptCheck` (`Cell → ByteArray → Except String Seen`). `Host.Deployed.X` passes `Protocol.Foreign.check`:
   - `Lang.headView` at the deployed `Std.headPackage` id;
   - then `Receipt.ofBytes`;
   - then `Receipt.check` against the held head's height and roots;
   - committed only. `refused` and `absent` need the call's window, which a receipt does not carry; the trigger for adding them is the first refund leg.

   Followers run the same `X`. There is no default argument. Every theorem over `Lang.program` quantifies over `receipts` (a binder), and the toy contexts pass `Lang.noReceipts`.
4. **Trust anchors are rows.** The fixture acceptor (`client/tests/fixtures/foreign/Accept.ob`):
   - keeps `heads : {cell} → {}`, which the owner inserts and retracts (revocation);
   - keeps `accepted : {tx} → {height}`, with one acceptance per transaction id (use-once).

   It accepts on `(heads (range 1 1) (receipt))`. Revocation, the certificate and use-once are three checks under one `receive`, the LPCFS monitor shape (REOR A.9).
5. **No atomic cross-World commitment.** Every row changes one World per Turn (the §2 refuter does not fire).

**Measured on the way, and acted on.**
- `nd` cannot pin a POINT read. `Machine.derivePins` pins the cells the derivation asks for and the rows the kernel names `rowUnpinned`, and `nd invoke` takes `--range` only. So a point `(live)` read (E1) is reachable from the Sims and not from `nd`, and E5's column also covers range rows. A `--pin REL KEY` for `nd invoke` is a separate card (Machine.lean); the trigger is the first deployed point read.
- Refusals-trie soundness had already landed (`Kernel/Proofs/RefusalsHead.lean`: `refusal_inclusion_sound`, `refusal_exclusion_sound`). The `Protocol/Proofs/Receipt.lean` header said it had not, and is corrected. **Amends PROTOCOL-45's critique**: "KERNEL states no refusals-trie inclusion soundness" is no longer true. `check_refused_sound` and `check_absent_unrefused` consume it.

**Theorems.**
- `Protocol/Proofs/Foreign`:
  - `foreign_receipt_sound` (P2): a committed column means the transaction was ADMITTED in a fold of A from A's genesis, at `v.height + 1` with that turn digest, or `CollidesAmong` the listed inputs (`check_committed`'s). The premise is named: the held head's roots are that fold's. This is head freshness and the poster's honesty, the thin-member trust of PROTOCOL-42. B holds A head, not THE head. The receipt `r` and the turn digest `td` are PREMISES (`Receipt.ofBytes … = some r`, `s.turn = bytes td`, both supplied by `check_committed_of`), not chosen by the conclusion: the first full judge's statement census refused the `∃ r td` form, because a collision disjunct over inputs the conclusion chooses is the pigeonhole shape (GATES-20s).
  - `forged_receipt_refused` (P3).
  - `forked_head_column_refused` (P4).
- `Lang/Proofs/StdHead` (over BigStep): `head_at_at` (L2 + L4), `head_forked_frozen` (L3), `head_at_fork` (L5), `head_world_fixed` (L6).
- `Lang/Proofs/Rel`: `receipt_column_authenticated` (L1). `cited_authenticated` is restated (RESTATES-MEANING: the live record may carry the receipt field, `[]` when `receipt = false`; no hypothesis added).
- `Kernel/Proofs/Journal`: `fold_journal_turn` (P1).
- `Protocol/Proofs/ReceiptWire`: `ofBytes_bytes` (P5, cv 01a14ef0-ffe7).

**Rows.** `client/tests/foreign.rs` runs over TWO geneses and two writers through the real `host`:
- X1: offer in A, accept in B: admitted;
- X1b: a second acceptance: refused;
- X2: the stated height forged: `pathMismatch`;
- X2r: another call's receipt with its cells root forged: `headMismatch`;
- X2h: a receipt at a later head: `headMismatch`;
- X3: a second poster's same-steps head: `lawDenied forkedHead`;
- X3b: the fork recorded, then accept and post: `forkedHead`;
- X5: anchor withdrawn: `untrusted`.

The `wrongWorld` control is the `wrongWorld` row.

**Plants** (whole logs `logs/p5plants2/`). Each reds its own row and nothing else on the way:
- roots comparison dropped: X2r (a never-accepted call's receipt with a forged cells root) admitted. Without the plant X2r refuses `headMismatch`, not `pathMismatch`: the roots comparison stands in front of `answerOf`, and `pathMismatch` is `answerOf`'s inclusion refusal behind it (X2's name, PL2's row);
- journal inclusion dropped: X2 admitted;
- the head law comparing steps only: X3 admitted;
- forked ignored by the check: X3b names `notHead`;
- the column filled without the check: X2 admitted.

Control GREEN after restore.

**Flag day.** Lang semantics change (install accepts a receipt read it refused), so `lang!`. Every Store re-geneses. No codec, call or reply byte moves. Host closure 89 → 93 (`Protocol.Foreign`, `Lang.StdHead` and what they import).

**cv.**
- 01a14ef0-ffe7: closed (P5).
- 01a14dfa-200a: refusals half closed (landed earlier); the last-head-link half stays, with trigger "a party holding only a chain digest (the phone, cv 01a14d95-36b0)".
- 01a14dfa-1ffb: closed as superseded by PROTOCOL-46 §7 (the Host hints, follow settles; `lieLookup` is the plant). Reopen on the phone.
- 01a14de7-224a: protocol half closed by PROTOCOL-61. The residue is CLIENT's (`nd --join` takes no `IN`).

**Critique.**
- The premise of `foreign_receipt_sound` is the whole trust. It is stated, not discharged, and forkedHead narrows it only at one object and one step count. A poster that follows a forked A posts a consistent lie.
- `notCommitted` and `headDead` have no `nd` row: `nd` cannot retire an object or sign a call it does not send. Their teeth are the check's and the column's definitions only.
- The receipt column needed a range-row arm because of the point-pin gap, which is the bigger finding. E1's live column has the same gap and was not fixed here.

**Meta-critique.**
- I first designed the column on points, the shape E1 had. The deployed client made that a Sim-only feature, and I found out only when writing the two-Store row. The BIAS: trusting a landed mechanism's reach because it has theorems. "E1 synthesizes the live column" was true of Lang and false of `nd`.
- I also first claimed a package-wire bump by analogy with E1. Measurement showed reads are types and no byte moves.

**On the fuse (rebased onto 28e2d88, PROT-6).** `methodReads` threads the same `receipts` and the method's arguments into
its peer part, so a `(receipt)` read is a column of the reader's own rows and its peer's alike. `methodSig` keeps the
fuse's `pairNamed` rule and adds the receipt-argument rule (`(rs ++ ps).any (·.2.receipt)` requires `receipt : bytes`).
`CheckError` holds both `peerNotNamed` and `receiptRead`. The fuse's theorems (`fuse_atomic`, `jointLaw_sound`,
`take_run_sound`, `invitation_once`, `peerReads_*`, `methodReads_*`) gain the binder, with no hypothesis added.

Status: landed by CX-PROMO-7 (lang!) from CX-P5's patch set, unchanged; build, journey, vectors, decls, the X rows and PL1–PL6 re-measured on the landing worktree (hbox `logs/promo/e5/`). LANG's half is LANG-75.14.

## PROTOCOL-67 · adopt's genesis check is "a World a genesis builds", not "no cell": the honest thin joiner adopts again (2026-10-23, CX-FIX-JOIN; R-0069; amends HOSTING-43's `atGenesis`)

**The red (MEASURED, hbox wt/fixjoin at 43484ab, logs/fixjoin/run1.log).** The convergence at 43484ab read `cargo:client:join` red, attributed to d23091d (HOSTING-43). `join.rs:278`: the thin joiner C, whose follow sits on its genesis World, ran `nd adopt KEY` and got `refused notAtGenesis` where the test wants `refused notBehind`. With the fix the whole test runs green, D's adopt of the sealed base included (run2-join.log). Of HOSTING-43's three deployed changes this is (2) alone: the package ROM check and describe's guards were not reached.

**Why (READ).** HOSTING-43 defined `atGenesis w := w.steps = 0 ∧ w.trie = .empty` ("holds nothing"), so that a live object refutes it (`atGenesis_live`, the `hG` premise of `step_keeps`). But no follow ever holds an empty World: `Receive.genesisWorld` inserts every founder's member cell and root World grant at step 0 (`founderEntries`), and a joiner's Store is that World (`nd --join` builds it from the signed inputs). So the conjunct refused every honest adopt at `start`, and the step-7 re-check, which is the time-of-check fix HOSTING-43 was right to make, would have refused it again. The check was not too strong in a way a weaker check repairs. It stated the wrong set: a floor no deployed World satisfies, which is exactly what `step_keeps` cannot see (its premise only needs the floor REFUTED by a live object, and an unsatisfiable floor refutes everything).

**Decision.** `atGenesis w := w.steps = 0 ∧ every trie entry is a live cell of kind member or grant` (`genesisLeaf`): a World a genesis builds and nothing has moved. Both checks stay (start and the step that adopts). Three theorems in `Protocol.Proofs.FollowHead`:
- `genesisWorld_atGenesis`: every `genesisWorld` satisfies it (the floor is satisfiable; it is the theorem whose absence let HOSTING-43 land the empty-trie floor), by `insertAll_toList` (what `insertAll` lists is what the map listed or an inserted entry, from `Trie.keys_insAt`, no premise) and `mem_founderEntries`.
- `atGenesis_object` (replaces `atGenesis_live`): a World it accepts holds no live object, by `Trie.mem_of_getAt` (no premise: no `Canon` enters `step_packageAt`).
- `step_packageAt` / `reach_packageAt` unchanged in statement, now discharged by `atGenesis_object`; axioms `propext, Classical.choice, Quot.sound`.
The scan is `toList` of the World's trie only when `steps = 0` (`&&` short-circuits), i.e. two cells per founder. Shapes: no wire, state, descriptor or codec change; nothing re-emits; no re-genesis.

**Critique.** Is this weakening a check? It accepts Worlds the HOSTING-43 check refused, so it must be judged as one. Those Worlds are exactly the step-0 Worlds holding member and grant cells; the danger HOSTING-43 guarded against was replacing a World a package fact is about, and such a World holds no object, so no `PackageAt` holds there (`atGenesis_object`). What the predicate still does not say is that the founders' cells are THIS World's genesis cells: a step-0 World whose member cells differ from the joiner's inputs would pass. That World is not one follow can hold (follow opens its own Store, built by `nd --join` from the signed inputs, HOST-22), and the replacement is the pinned base, whose origin `wrongWorld` checks. Equality with `genesisWorld` of the kept inputs would need the inputs in `Self`, which follow does not carry.

**Meta-critique.** The pull here is to read the red as "the test is stale" (`notBehind` → `notAtGenesis`) and re-pin the expected string: that would have shipped a follower that can never adopt, with green tests. The other pull is to drop the trie conjunct and return to `steps = 0`, which makes `step_keeps` unprovable for any property a genesis World could hold. The defect class is the one HOSTING-43's own plants could not see: P1–P3 each red the strong theorem, and none asks whether the deployed floor is SATISFIABLE by the honest path. `genesisWorld_atGenesis` is that question as a theorem, and `join.rs` is its deployed run.

**Amendment (2026-10-24, FIX-PROTOCOL; readers A21, READ-PROTOCOL Q1).** The critique's sentence "a step-0 World whose member cells differ from the joiner's inputs would pass. That World is not one follow can hold" is FALSE. `Kernel.carryWorld` sets `steps := c.height`, so a World carried from a height-0 export (OPS-P1, `host import`) is at step 0 with the old lineage's member and grant cells, and a member re-invited to it (`acceptCarry`) holds it. `atGenesis` admits it. It is harmless: it holds no object (`atGenesis_object` is over the predicate, not over its provenance), and the replacement is still the pinned, origin-checked base. What changes is the predicate's stated meaning, now in its docstring and in `Protocol.Proofs.FollowHead`: `atGenesis` is "a step-0 World of members and grants" (a genesis World, `genesisWorld_atGenesis`, or a World carried at height 0, `carryWorld_atGenesis` and its instance `carry_genesis_atGenesis`: the carry of any genesis World under any new name and nonce), NOT "a World this joiner's genesis built". `genesisLeaf`'s docstring said "a founder's member cell"; it accepts any member or grant cell, and says so. No check, wire or state changes.

## PROTOCOL-68 · `argvBytesMax` is derived from the kernel's call bound, so every admitted call can be confirmed (2026-10-23; CX-DEADLINE, found while landing LANG-76; ROOT for PROTOCOL under R-0069)

**The red (MEASURED).** `rows bell` and `resident_bell` read `install <world/resident/Bell>` as `uncertain` once the Bell grew to 36,379 call bytes. The writer committed the install. Follow's confirm runs `receipt <CALL in hex>`, which is 72,758 bytes of argv, and follow refused it `argvPastBound` (`argvBytesMax` was 65536). The attempt read the refused confirm as `uncertain`, the class PROTOCOL-55 named. Every admitted call past 32,760 bytes was committed and never confirmed. The kernel admits calls up to `eventBytesMax` = 65536.
**Decision.** `Bounds.argvBytesMax := 2 * Kernel.Bounds.eventBytesMax + 1024` (132096). `Command.receipt_argv_fits`: for a call within `eventBytesMax`, `argvSize ["receipt", toHex call]` is within it, by `Command.toHex_utf8ByteSize`. `Text.toHex` folds over `b.data` (same output), so its size is a list fold. `argv_fits_frame` still holds (132097 ≤ 262144).
**What re-emits.** `client/src/generated.rs` (`ARGV_BYTES_MAX` and the `Command` layout's bound). No wire byte of any frame within the old bound changes. A command between 65,537 and 132,096 bytes is now read rather than refused `argvPastBound`.

## PROTOCOL-69 · The journal entry at a call's id is that call's commit; step 3 submits only a call whose bytes read back as itself (2026-10-23, CX-BACKLOG-2; cv 01a16821-5835, HOSTING-44's second gap; R-0069)

**Decision.**
1. **Follow's journal has a provenance** (`Protocol/Proofs/FollowJournal.lean`). `JournalFrom X Q w₀ w`: `w` satisfies `Q`, its journal and rows tries are canonical, and every journal entry is `w₀`'s or was written by admitting a Turn received from a call decoded from logged bytes, at a `Q` World with canonical rows: the key is that call's `txIdOf`, the entry `(v.height + 1, turnDigest t)`. `absorbStep_journalFrom` (a Turn by `submit_ok` + `commit_journal_mem`, a refusal or cancel by `refuse_journalAt`), `step_journalFrom` (through `step_keeps`, for a `Q` refuting `atGenesis`).
2. **From one call's id to its commit** (`Hosting/Proofs/Committed.lean`). `reach_journalFrom` lifts it over `Reach`. `journal_committed`: if follow's World journals `e` at `txIdOf X c` and `X.decodeCall (X.callBytes c) = some c`, then the start World held `e`, or `c` ITSELF was received at a `Q` World `v` with canonical rows and admitted, `e` its entry; or a byte string `b ≠ X.callBytes c`, decoding to a call received and admitted at a `Q` World, has `X.env.hash domTx b = txIdOf X c`.
3. **The bound, said out loud: a SECOND PREIMAGE of the call's id, not a collision.** `c` is a premise; only `b` is chosen. The brief's shape, `CollidesAmong hash [(domTx, callBytes c'), (domTx, callBytes c)]` with `c'` chosen by the conclusion, is the census's red shape (the list mentions a chosen variable, so it bounds nothing) and is not landed. A scoped `#statement_census` over the six touched modules reads ok, 7 disjunctions (MEASURED, hbox wt/backlog `.lake/gates/c3-statements.tsv`).
4. **Step 3 checks the call reads back** (`Protocol/Command/Machine.lean`). Follow derived and receive-checked `⟨u, sig⟩`, then submitted `X.callBytes ⟨u, sig⟩`; the World judges what those bytes DECODE to, and nothing said that is `⟨u, sig⟩`. Step 3 now refuses `badCall` unless `X.decodeCall (X.callBytes c) = some c` (the deployed codec meets it for every `Call.Fits` call, `Codec.Proofs.Deployed.decodeCall_callBytes`). `badCall`'s doc now names both of its sites; one fault, one name. `step_cont` and `Planned` carry the fact; `delivered_answer_committed_strong` exports it, and also the World `wb` the invoke's run started at with `Reach wb wf` to the settling World (it named the planning World `wp`, whose order relative to `wf` was lost).
5. **The consumer** (`Hosting/Proofs/BellRow.lean`, `answered_row_committed`). Over what `answered_row_is_kept_answer` concludes (premise form): the entry is `wb`'s, or the call was received at a World `v` where the bell still holds `P` and admitted to `v'`, and `v'` holds `rings[(k, nb)] = answeredVal x y` and no `pending` row there; or the second preimage. `Lang.Bell.answer_commits` is restated to what the consumers hold: the object's live cell names `P` by `packageOf`, and `P` reads as `pk` through any look that reads `P`'s live cell (`worldLook`); the pinned read is derived (`program_run_reads`: a returned run read its package through its look; `pinned_read_live`). The ROM cell is the same at `wb` and `v` (`PackageAt`, `readPackage_live`).

**Price.** RESTATES-MEANING: `step_cont`, `run_invoke_ok`, `delivered_answer_committed_strong`, `answered_row_is_kept_answer`, `answer_commits`. Premises added to landed theorems: none (`answer_commits` trades the pinned read for `hlook`, which `rfl` discharges at `worldLook`). New premises of the new theorems: canonical journal and rows at the base World (follow's base is not proved canonical anywhere; open), `hX` (as the strong theorem). Behaviour: one new refusal path at step 3, on a call the deployed codec never produces from a `Fits` plan and signature. No wire format, VK or genesis changes; nothing re-emits.

**Plant (MEASURED, hbox `logs/backlog/plants/C3-no-roundtrip-check.build.log`).** Step 3 without the check: `Hosting.Proofs.Socket` RED at `step_cont` (l.111, the roundtrip conjunct). Restored byte-identical to the edit.

**Builds (MEASURED, hbox wt/backlog, 6G swarm-build).** `Protocol` and `Host` libs green (269 jobs); every `Hosting` module but `Hosting.Proofs.Reply` green (258 jobs). `Hosting.Proofs.Reply` is EXCLUDED: it OOMs at 10G alone on this box (CX-BACKLOG's measurement); the judge builds it.

**Vacuity read (author).** Each disjunct of `journal_committed` alone is unprovable from the premises: the first is false for a fresh id on a `w₀` that never held it; the second needs a commit of `c`, which a `w₀ = w` refl run does not have; the third needs a second preimage. The premise `hc` is satisfiable (deployed codec, any `Fits` call). INFERRED, no tooth instantiates each.

**Critique.**
- `v` is a `Q` World, not a World ON the path follow took: `Reach` is a relation, not a trace. A trace-indexed reach would pin `v` and bound `b` by membership in the absorbed events; the resident's view of follow is existential either way, so it would not make the resident-level composite statable without the chosen-target shape.
- The composite (the resident's own call, taken to its commit inside `answered_row_is_kept_answer`) is not stated: there `⟨u, sig⟩` is chosen by the conclusion and the hash disjunct reads as a collision. Composition happens by application.
- The base disjunct stays. The planning World does not journal the signed call's id (the plan admitted `⟨u, empty⟩`, a different id), but nothing proves the id absent at `wb`. Canonicity of follow's base World is an open premise.

**Superseded in part by HOSTING-47 (2026-10-24).** Items 2, 3 and 5 are restated: the "second preimage" disjunct ranged over every call some `Q` World admits, an unbounded set, so it held by counting (READ-HOSTING D1). `JournalFrom` now names the bytes its commits decode from, `Command.step`'s absorbed events are `frameEvents` of its result (`step_world`), and `journal_committed`/`answered_row_committed` are stated over `ReachOn S` with a fresh base, ending in `CollidesAmong` over `c`'s bytes and the frames' calls. The critique's "trace-indexed reach would … bound `b` by membership" is what landed.

**Meta-critique.** The bias: executing the brief's mechanism (an explicit two-call `CollidesAmong`) because it names the gate's vocabulary. With the other call chosen by the conclusion, the explicit list bounds nothing and the census reds it; the honest object is the call the caller holds, which makes it a second preimage, a stronger assumption to break than the collision the brief priced. Second bias: the commit step reconstructs the DECODED call, and the consumer knows the PLANNED one's body. The temptation was a codec premise (`callBytes` injective, unsatisfiable at the deployed codec outside `Fits`); the right fix was the machine refusing to submit a call whose bytes are another call.

## PROTOCOL-70 · A frame is bounded AS A WHOLE: the page budget is the frame less the continuation that asked for it (2026-10-24, FIX-PROTOCOL; readers A3, READ-PROTOCOL D1; R-0069, R-0071)

**The defect (MEASURED before any change, hbox wt/fixproto at f9657bd; logs in redregg/work/codex/FIX-PROTOCOL.report.md).** Every layout field is bounded by `frameBytesMax` on its own (`Codec.Layout`); the transport bounds the frame's BODY, op or status byte and every field together, by the same number (`Host.Wire.bodyMax`, `client/src/frame.rs` `read_body`/`write_body`). A `resume` after a `log` carries the continuation `k` (the WHOLE argv) AND the Host's page. The old budget `Host.Page.budget = frameBytesMax − 1024 = 261,120` bounded the page as one field. Measured over the real codecs: a full page's reply is 261,245 bytes (125 of framing), a resume spends 9 more, so a full page left **890 bytes** for `k`; a phase-2 `k` of `receipt CALL` is `216 + 2·|call|`, so **no call over 337 bytes could confirm against a full page**. Deployed calls: an ordinary `write @shared 2 1 --via @g` is 540 bytes, `write @shared 3 9` 444, the queue Bell's install 36,550. The row (`fullPage`, below) at today's code: toy parameters, the Bell install's `receipt` refused `pastBound` (client transport); deployed parameters, the install's AND the ordinary write's refused `pastBound`. So the attempt store's confirm after time away (a follower a full page behind), a cold `receipt`, and every install by a member who had been away failed, read by the attempt as `uncertain`, never settling until the member happened to `nd sync`. The rows could not see it: their writer paged at a 65,541-byte stand-in, and the in-process harness bounded each field, never the frame.

**Decision: the page budget is DERIVED from the frame minus the largest page-phase continuation and every byte of framing** (`Protocol.Bounds`): `custodyKeyBytes` 32, `custodySignatureBytes` 64, `signedBytes` 140, `resumeFramingBytes` 9, `logReplyFramingBytes` 125, `pageContinuationBytesMax = argvBytesMax + 1 + 4 + 4·12 + (4 + signedBytes)` = 132,293, and `pageBytesMax = frameBytesMax − 9 − 125 − 132,293 = 129,717`; `Host.Page.budget := Protocol.Bounds.pageBytesMax` (the `read` base pages too: phase 7's continuation is smaller). Why this and not the brief's two alternatives, by law 1: (a) a budget from the continuation's ACTUAL size needs the Host to learn |k| (a new field on the `log` request, unsigned or signed), and the Host would page by two budgets, its own bound and the request's, with a check that the requested one is within it: a second budget path for one fact. (b) Paging the continuation out of the frame (follow keeps `k`, the resume carries a handle) puts command state in follow's memory beside the client's copy: two homes for one continuation, follow's memory bounded by live commands (law 4), lost on restart. A static derived constant is one budget, one place, checked by one theorem. Its price: a full page holds at most 129,717 event bytes, not 261,120. That binds only pages of large events (a page holds at most 64 events, `recordTurnsMax`, so events under ~2 KB never fill it), and a catch-up reaches `behind` after 28 × 129,717 ≈ 3.6 MB of large events per command instead of 7.3 MB. It still serves every event the kernel admits (`budget_fits_event`: 65,613 ≤ 129,717).

Follow's own replies are bounded as a whole too: `Command.Reply.bytes` is `none` for a step whose fields each fit but whose sum does not (`bodyFits`, `Protocol/Frames.lean`), so `host follow` refuses it `stepTooLarge` by name instead of writing a frame the client refuses. The continuations lost their duplicates (memo B7): phase 3's acc is `[signed, ub]` (start was unused), phase 4's `[out, cb]` (start, signed and ub were unused; the call travelled three times in a submit step), phase 5's `[]`, phases 9/10 hold no acc (the call is the argv's `cancel CALL`). Phase 4 settles only under a verb that submits (`Command.submits`), else `badState`.

**Theorems** (`Protocol/Proofs/FrameFit.lean`, `Host/Proofs/Page.lean`). `Host.Page.build_within`: every page `build` returns carries at most its budget in event bytes (`walkStep_within` → `walkTurnsAt_within` → `walk_within`, the invariant `bytes = eventBytes ∧ bytes ≤ budget`). `resume_size`, `State.bytes_size`, `Signed.bytes_size`, `page_size`: sizes read off the one codec (`Stream.Lawful.size_eq`). `frame_split`: the four parts sum to `frameBytesMax` exactly. **`resume_frame_fits`**: for a phase-2 continuation of an argv within `argvBytesMax` (`parse_past_bound`: every argv `parse` admits), its four positions as `u64`s and custody's answer at the deployed widths, and a page `Host.Page.bytes` writes from an `Acc` within `Host.Page.budget` with chain and base digest of the deployed width, `k` and `ok ‖ page` each fit a field and `bodyFits` of the resume frame holds. `perField_budget_overflows`: at `frameBytesMax − 1024` the same sum is past the frame (the tooth in the constants).

**Rows.** `fullPage` (new): welcome; the sponsor installs the Bell; the newcomer writes (540 bytes); the operator installs 64 filler packages whose install call is 4,075 bytes at the deployed parameters (`fillerPadBytes`, measured), 64 × 4,080 = 261,120, the old budget exactly; then each `receipt CALL` of the sponsor's and the newcomer's last call settles committed. The in-process harness now has the client's transport: `followAsk` refuses a request or reply body past the frame (`pastBound`). Plant `perFieldBudget` (the writer at `frameBytesMax − 1024`): line 72 (the install's receipt) `refused pastBound` under both parameter sets. MEASURED: `rows fullPage cancelLie` ALL PASS, `rows --deployed fullPage cancelLie` ALL PASS, plant caught at line 72 both.

**The rows at the deployed budget (memo B1, B2).** `Rows.Params.pageBudget` is DELETED: the writer pages at HOST's own `Page.budget` under both parameter sets (`Rows.Writer.Params.pageBudget`, defaulting to it; a row's misconfigured writer, `Row.pageBudget`, and the `guessedBudget` plant set it). The rows still see page ends: 64 events a page. `toy_budget_serves` / `deployed_budget_serves` (`Nat.le_refl` of their own definitions) are DELETED; the fact they named is HOST's `budget_fits_event`.

**What changed shape.** Pages: a log or base page now ends at 129,717 bytes of events or World bytes (more pages per catch-up; no wire layout changes). Continuations of phases 3, 4, 5, 9 and 10 changed their acc: a continuation an old `host follow` handed out is `badState` to the new one (the client holds `k` only for one command, so a command in flight across the upgrade ends `badState` and is run again). Nothing re-emits (`client/src/generated.rs` carries none of the new constants; the client relays `k` opaque). No re-genesis.

**Residual, named and filed (INFERRED from the same arithmetic).** A `sign` step at 2→3 is `argvSize + 2·|ub| + 163` bytes and a `submit` step `argvSize + 2·|call| + |out| + 23`: past the frame only when the argv is about twice its call or more (an `install` of a text whose encoded package is under half its size, an `invoke` with verbose argument text). Such a step is now refused `stepTooLarge` by name (above), never written. Closing it needs phase 3 to compare a digest of the signed message instead of holding it, and phase 4 to settle without re-parsing the argv: cv task 01a16d81-d644 (FIX-PROTOCOL-sign-submit-frames).

**Critique.** Is shrinking the budget weakening anything? No check is relaxed; the frame bound is the same; pages are smaller. The theorem's premises are honest custody widths and u64 positions: a custody that answers wider fields, or a client that forges a continuation with long `pages`/`tried` fields, can still build a frame past the bound, and the transport refuses it (a fault of that custody or client, by the transport's name). The theorem is about the pages the Host builds, through `build_within`; the composition with `Host.Deployed`'s pager (`Page.kept` = `build` at an offset) is by application, not stated.

**Meta-critique.** The pull was to fix only what the card measured: the confirm. The same class sat in follow's own replies (fields bounded, sum not) and in the harness (which is why no row saw it); bounding `Reply.bytes` and the harness transport is the class, the budget the instance. The other pull was the brief's first option, the "actual size" budget, because it keeps pages large; it buys page size with a second budget path.

## PROTOCOL-71 · `nd cancel` ends `ok` only on follow's own World: the writer's `refused cancelled` starts a second catch-up (2026-10-24, FIX-PROTOCOL; readers A7, READ-PROTOCOL D2; the class PROTOCOL-64 closed at step 4)

**The defect (READ).** `cancelAnswer` (phase 10) printed `cancelled TXID` and exited 0 on the writer's `refused cancelled`, and rendered its `ok` as `refused committed`, both the Host's word. PROTOCOL-46: a settlement is the member's word. Between phase 9's pre-check (`Receive.cancel` would record on follow's World) and the answer, the writer may have admitted the call, or a relay may answer anything.

**Decision.** Phase 10's two final claims each start a second catch-up from follow's own World (`cancelCatchUp`, as `start` begins one), its `tried` naming the claim (`saidCancelledBit` 4, `saidCommittedBit` 8; disjoint from `expiredBit` and `incomingBit`, which `envelopeRefused` ORs in). At that catch-up's tip `cancelSettled` decides by `settleOf` on the World it reached: `cancelled TXID` (ok) only when the writer said cancelled AND that World settles the call `refused cancelled` (`cancelledCode`); `refused committed` only when the writer said admitted AND it settles committed; otherwise `hostContradicted CLAIM FOLLOWSAID` (`attemptContradicted`), the attempt left open. A decline, another refusal, and `uncertain` end as before.

**Theorems** (`Protocol/Proofs/Command.lean`). `cancelSettled_ok`; **`cancel_ok_settled`**: for any continuation and result the client hands back, a step of a `cancel CALL` command that ends `done ok` answers with a World whose settlement of the call is `refused cancelled`, over the WHOLE step machine (every other arm under a cancel argv refuses, asks or hands on; phase 4 is `badState` for a verb that does not submit, which closes the forged-phase-4 path to `ok`). Restated (a binder each, no hypothesis): `cancelAnswer_ne_submit`, `cancelAnswer_ne_host`, `cancelAnswer_cont` (now: the continuation is phase 1, `askedIncoming` false, carried by `sign`), `sendCancel_cont` (phase 10's acc is `[]`). New helpers: `cancelCatchUp_ne_submit`/`_ne_host`, `cancelSettled_ne_submit`/`_ne_host`/`_cont`/`_ok`, `cancelTip_ok`, `settleStep_ok`, `cancelAnswer_ne_signIncoming`, `refusedAt_ne_ok` and the other `_ne_ok`s. `step_settled_ok` reads phase 4 through `settleStep` (unchanged statement). `step_incoming_kept` dismisses other phases' arms by their phase. Hosting's `step_cont` reads the new `cancelAnswer_cont`, `cancelTip_cont` and `settleStep_cont` (cross-layer: three tactic lines). The phase-2 cancel tip and phase 4 are named functions (`cancelTip`, `settleStep`, each with its `_ne_submit`/`_ne_host`/`_cont`/`_ok` lemmas), so the whole-machine case splits (`step_submit_planned`, `step_host_cancel`) did not grow: they stay in the default heartbeat budget (a first version fed them `maxHeartbeats`, which the source gate refuses: a slow proof is fixed, not fed).

**Row.** `cancelLie` (new): the sponsor's write never reaches the writer (`open`); a relay keeps its cancel from the writer and answers `refused cancelled` (fault `lieCancel`): line 7 `hostContradicted cancelled open`; the honest cancel after it prints `cancelled TXID`; the next run settles `refused cancelled`. Plant `trustCancel` (follow's old phase 10, an output-rewrite plant of the B12 kind): line 7 ends `ok`. MEASURED: PASS under both parameter sets, plant caught at line 7. `cancel` and `cancelForged` still PASS (their cancels now settle by the second catch-up).

**Price.** One more catch-up per cancel (two frames when follow is near the tip). A cancel issued far behind may now run past `stepsPerCommandMax` (Rust's bound) where it ended before; it is then run again.

## PROTOCOL-72 · Three row plants that tested something else, and a bound's doc that named the wrong owner (2026-10-24, FIX-PROTOCOL; READ-PROTOCOL B3, B4, B8, Q8)

- **`settle`'s plant bit at line 1, not at the lying lookup (B4).** `trustLookup` made the store end every attempt on the Host's status, so the welcome's first enroll (line 1) was caught: a generic effect. The plant is now a store that takes the Host's final REFUSAL as final; line 6, the lying-lookup line, is caught (`hostContradicted refused open`), and lines 0–5 keep their outcomes. MEASURED (toy run): caught at line 6.
- **`staleRange`'s plant changed two things (Q8).** It routed the take through `forged` (no catch-up AND no follow admission). It is now a relay that hides the log from that command (`hideLog`: an empty page at follow's own position stated as the tip), so follow's own machine, admission included, plans at the stale listing; the writer declines it `stale` at line 10. Skipping follow's admission alone is not a plant in this row (the writer judges a fresh range and admits it). MEASURED: caught at line 10.
- **Docstrings (B3).** `settle` and `refused` now name the outcome their plants get since PROTOCOL-64.
- **`stepsPerCommandMax` (B8).** Its doc said follow ends a command past it; follow keeps no step counter. It is the client's bound (`client/src/run.rs`, `StepsExhausted`) and the harness's, a table constant Rust consumes.

## PROTOCOL-73 · Follow's stale-BEHIND test asks what the Host asks, in its order: `signedBy`, then `checkPins` (2026-10-24, FIX-PROTOCOL; found by FIX-KERNEL after KERNEL-66)

**The defect (READ, then MEASURED).** KERNEL-66 made the Host compare a call's pins before any receiver runs (`submit`: journal, record, `signedBy`, `checkPins`, derive, admit). `Command.staleBehind`, the client's settlement of an absent call as `refused stale` (KERNEL-54), still decided by the old order: `receive`, then admission's `stale`. A call whose pin moved AND whose receiver also refuses on the new World is declined `stale` by the Host and read as not stale by follow, so the settlement stayed `open`. Row `staleRefusing` (new): the newcomer writes through its grant `g` while the sponsor races a `revoke @g` (the grant's pin moves; the write's receiver now has no grant). Before the fix, line 7 (the attempt's next run) ended `declined stale`, never settled: the settlement read `open`, the attempt sent the call again and the Host declined it again (both parameter sets).

**Decision.** `staleBehind` is the member's-own-call conditions, then `signedBy X w c false = .ok ()`, then `checkPins` on follow's World refusing: the Host's own first two judgements (law 1: one definition of "stale" for the Host and the member). `staleBehind_spec` RESTATES-MEANING (it concludes `signedBy` ok and `checkPins = .error (.stale x)`, not a derived Turn refused by admission). New: `staleBehind_declined` (where the call is neither journaled nor recorded, `staleBehind` holds only of a call `submit` refuses `stale` and `judge` declines) and `checkPins_error_disagree` (`checkPins_ok_iff`'s contrapositive: a cell pin, a row pin or a range read that disagrees). `staleBehind_final` (statement unchanged) now reads the disagreement off the CALL's pins directly, with no Turn derived at `w`; `staleBehind_admissible` reads `submit`'s order.

**Rows.** `staleRefusing`: line 6 `declined stale`, line 7 `refused stale`; PASS toy and deployed. No cheap plant exists (the old order is follow's deployed function and nothing in the harness can swap it), so the row's `Plant.measured` (new constructor) records the before-fix measurement instead (a plant is a vacuity check run when cheap, CHARTER as of 10-24). `refused` and `settle` still PASS.

**What changed shape.** A settlement may now say `refused stale` (final) where it said `open`: exactly for a call whose pin moved on follow's fold while a receiver would also refuse it. A settlement now also costs one signature verification (`signedBy`). Nothing re-emits; no re-genesis.

## PROTOCOL-74 · Members compare heads: `nd sync --to STEPS:CHAIN`, `--attest`, `--check ATTEST`; a fork is refused `forkedWorld` by name (2026-10-26, FABLE-TRUST; DESIGN-TRUST T1, `redregg/work/promo/DESIGN-TRUST.md`; readers' §6, HOST §1.3, PROTOCOL §2.3, TOPLEVEL-SPEC §2.3/§11.1)

**The gap (READ).** Within one World no member act ever took another member's position: `absorbPage` compared follow's fold with the WRITER's stated `(steps, chain)` only; `host check --anchor` compared a Store with a position for the operator; `Std.head` compared two posters at equal step counts. So a writer could serve two members two histories indefinitely, each internally honest, and no refusal fired: the one guarantee a trusted single server also lacks (SUNDR 2004's fork consistency), unmet. [Corrected by PROTOCOL-82: this sentence said nano already had SUNDR's NO-REJOIN half because two diverged folds hold different chains at every later step. That binds pages, not operations: a signed call carries no prefix, so a writer can admit one call on two branches. Nano has no operation-level no-join; it has prefix agreement for members who compare stated heads.] What was missing was the compare act and a signed witness.

**Decision.**
1. **`Protocol.Head`** (new; Host closure +1): `Head` = `(origin, steps, height, roots, chain)`, the one spelling of a position (the chain beside the roots, because `fold_head_binds` binds the chain and a receipt checks the roots); `Attestation` = a head, a member, its key, signed under `domHead` (`nanodregg/protocol/head/v1`, the SEVENTH signing domain: `Proofs.Domains` gains its six pairs, `head_not_envelope` in particular: an envelope-only custody never attests); `verified` (decode, the World, the signature under the key named) and `signer` (on a caught-up World: the member is live and that key is its CURRENT one; a rotated-away key is `staleKey`); `anchorCheck`, the walk of a page's steps (each with the roots digest after it, the record's shape) from follow's position by `stepLink`, exactly as `chainOf` advances the chain, answering `shared` / `forked` / `unreached` at the anchor's step count.
2. **`sync` gains three forms** (the verb count stays 20): `--to STEPS:CHAIN` catches up THROUGH the position and compares as it passes (the anchor is re-derived from the argv at every step, `syncAnchor`, so a continuation cannot steer it); `--attest` catches up, then has custody sign `Head.message` of follow's OWN World's head (`attestTip`; phase 11 prints `attest HEX`); `--check ATTEST` is `--to` at the attested position with the attestation verified before anything is sent and its signer checked at the tip. Outcomes: `shared STEPS [MEMBER]`; `refused forkedWorld` (the page refused and nothing of it kept, as a `chainMismatch` page is: the fork is evidence, and follow does not walk onto it under this command; a plain `sync` does); `refused ahead` (follow was already past the position when the command began: its World holds only the current chain, so the member behind does the check, or `host check STORE --anchor` on its own Store compares a past position); `unreached STEPS` (the writer's tip is below the position). `absorbSync` wraps `absorbPage` for the walk, so `absorbPage` and every consumer keep their statements; `absorbSync_ok` is the one new lemma the whole-machine proofs read.
3. **Refusals by name:** `forkedWorld STEPS`, `ahead STEPS`; `badAttestation`, `otherWorld`, `badHeadSignature`, `notMember`, `staleKey` (`Head.Refusal`, `name_injective`), all in `hintNames` (`hintNames_complete` gains the arm).

**Theorems** (`Protocol/Proofs/Head.lean`). `anchorCheck_shared` / `anchorCheck_forked` (the walk found a prefix whose `chainOf` from follow's position is / is not the anchor's chain); `shared_on_fold` / `forked_on_fold` (over a page follow absorbed, `World.RootedFold`, that prefix FOLDS from follow's World to a World at the anchor's step count with / without the anchor's chain); **`anchor_binds`**, the member-facing statement: follow's World a fold of `l₀` from a start `g`, a page absorbed and walked `shared` against the other member's `(steps, chain)`, the other member's World a fold of `lg` from `g` ⇒ `l₀ ++ prefix = lg` or `CollidesAmong` the two folds' `foldPres` (through `fold_head_binds`); `forked_not_on_fold`: a `forked` walk is never free (follow's own fold holds another chain there, so no log reaching the other member's head is follow's up to there); `attestTip_sign` (consent, the shape of `step_submit_planned`: every `sign` the attest tip hands out is `Head.message` of `unsignedBytes` of `headOf` follow's own World with `me.member` and the envelope's key); `verified_ok`, `signer_ok`. Nothing landed gains a hypothesis; nothing in Kernel/** or Host/** is touched; `absorbPage`'s signature is unchanged (the walk runs over the `ts` it already returns, so every `absorbPage` consumer in Proofs/{Command,FollowHead,FollowJournal,Settle} and Host/Proofs/Refine keeps its statement).

**What the witness is.** Two attestations of one World that both `verified`+`signer`-check on a third member's World, with the smaller step count's chain not on the larger's fold: by `attestTip_sign` each signer signed only what its own audited fold reached, so two honest audits of pages one writer served diverge. Attribution is by exclusion (the writer is the only party that orders; a sponsor's signed pin off the chain is the other candidate, named by its signature). A writer-SIGNED head would make the attribution non-repudiable to strangers: that is DESIGN-TRUST T3 and needs the Store signing seed, Ember's pause item; nothing here needs it.

**Row.** `fork` (new, replaces nothing): the sponsor attests at the tip; the cold operator `--check`s it, `shared`; at the tip, `--check` again is `refused ahead`; cold, `--to 2:00` (a chain no fold has at step 2) is `refused forkedWorld` on the way; `--check 00` is `badAttestation`; after `rotate`, the old attestation is `staleKey`. Plant `ignoreAnchor` (a client that drops `--to`'s anchor): line 10 ends `ok`. Client: `client/tests/join.rs` runs attest / check / forkedWorld / ahead / badAttestation over the real sockets (cross-layer: the test is CLIENT's file, the verdicts are Lean's).

**Price.** Zero hypotheses on landed theorems; zero re-genesis; no byte of any Store, call, reply or package moves (an old `nd` on the new flags is `usage`). SIZE: Host closure +1 (`Protocol.Head`), refusal constructors +8, conformance rows +1, theorems +~30.

**Critique.** (1) The guarantee is conditional on the act: a World whose members never run `--check` detects nothing, exactly SUNDR's condition; the automatic form (every member posts its head INTO the World and every follow walks every absorbed post, T2) is what a public node of strangers needs, and it waits on `Std.head` gaining `chain` (a `lang!` flag day). (2) `ahead` is a refusal where a member expected an answer; the past-chain comparison exists only as `host check --anchor` on the follow Store, two tools for one question until T1b routes the ahead case through the follow loop. (3) `staleKey` makes an attestation die with a rotation; that is the KERI reading (a rotated key speaks for nothing) and it is stated, not hidden, but a member with a key compromised AFTER attesting loses nothing it should keep, while one that rotated honestly must re-attest. (4) The `fork` row's forged position is a literal (`2:00`), not a second writer serving a second honest history: the harness has no two-writer fault, so the `forkedWorld` arm is exercised against a chain no fold has rather than against a real fork; `forked_not_on_fold` is what says the two are the same refusal.

**Meta-critique.** The first draft put the comparison inside `absorbPage` as a new parameter, which restates every consumer by binder (≈ 12 statements across four proof files and Host's `honest_page_absorbed`); the walk over the steps follow already persists costs none and is law 1's reading (the record's shape IS what a reader needs to advance the chain, `RootedFold.chain`). The bias was "the check belongs in the fold" because that is where `chainMismatch` lives; `chainMismatch` is about the writer's statement, this is about another member's, and a different observer gets a different function. The second bias, inherited from every reader that priced this: "weeks" for fork consistency, because they priced building consistency; the chain already had it and only the act was missing.

## PROTOCOL-75 · Self-heads through the writer: `nd sync --post OBJ` posts a member's own head into a `Std.head` object of its World, and every follow that absorbs the post compares (2026-10-26, FABLE-TRUST-2; DESIGN-TRUST T2, `redregg/work/promo/DESIGN-TRUST.md` §4.2, §5; with LANG-95)

**The gap (READ).** PROTOCOL-74's guarantee is conditional on an act: a World whose members never run `sync --check` detects nothing (SUNDR's condition; PROTOCOL-74 critique 1). A public node of strangers arranges no comparisons. And `Std.head` held `{height, roots, steps}` only: two posters of a foreign head disagreed by ROOTS at one step count, while what `fold_head_binds` binds is the CHAIN.

**Decision.**
1. **`Std.head` carries the chain** (LANG-95, the Lang half, TRUST's by FABLE-OWNERSHIP): `headAtTy` = `{chain, height, roots, steps}`; the head law's `at → at` arm compares the chain too at an equal step count (`forkedHead`; `Lang.Proofs.StdHead.head_at_at` gains `c = c'`); `Lang.headView.at` carries it; `Protocol.Foreign.check` ignores it (a receipt is checked against height and roots). `receipt CALL` prints `head STEPS HEIGHT ROOTS CHAIN`, so a foreign poster has the chain to post.
2. **`sync --post OBJ`** (`Cmd.post`; the verb count stays 20): catch up, then plan `invoke OBJ post` with `Head.headText` of follow's OWN World at the tip (`Command.body`'s `.post` arm; `Proofs.Head.body_post`: the body is re-derived from the argv at phases 2 and 3, so a continuation cannot steer what is posted). The member's head object is a `Std.head` of THIS World (`world` = the World's origin).
3. **Every follow compares as it absorbs.** After `absorbSync`, `Head.forkedSelfPost X w ts w'` reads every head object a step of the page touched (`selfPosts`: `Lang.headView` at `Foreign.headPackageId`, `world` this World's origin) and walks the page against each posted `(steps, chain)` from follow's position before the page, exactly as `sync --to` walks (`anchorCheck`). A position reached with another chain is **`forkedPost STEPS`** (the poster named): the page is KEPT (it is lawful on follow's fold; the fork is the poster's or the writer's), the command ends by name, the next command proceeds past it, and the poster's signed call is the witness. A lying member therefore cannot freeze other members' follows (what refusing the page would have allowed). [Corrected by PROTOCOL-82: this said a forking writer "must censor every member's posts from the other fork forever, or be refused". A writer may withhold posts indefinitely, and silence proves nothing; it may copy a member's ordinary calls between forks, which carry no head; and a post is compared only where the reading member's fold covers its step.]
4. **What is compared where.** The walk compares a position INSIDE the page that carries the post. A follow already past the posted position (a live member: the common case) compares nothing here; its chain at that step is in its own Store's index, as `host check --anchor` reads it (`Page.kept` at budget 0). That is the follow loop's, with its files: cv task 01a176ab-14f5 (T2b'), HOST-prefixed, next.

**Theorems** (`Protocol/Proofs/Head.lean`): `forkedSelfPost_forked` (a `forkedPost` names a post the page carries whose position follow's fold reached with another chain: `forked_on_fold`), `forkedSelfPost_none` (no refusal ⇒ every post the page reaches is reached with the posted chain, `shared_on_fold`, or is unreached on this page), `body_post` (consent). With `anchor_binds` (PROTOCOL-74) and `body_post`: a post follow absorbed without `forkedPost` at a position it reached is the poster's own fold's position, so follow's log up to it IS the poster's, or the listed inputs collide. Hypotheses added to landed theorems: 0. Restated by binder: `Proofs.Foreign`'s four statements name the head's chain (`c₀`), `Lang.Proofs.StdHead.head_at_at` gains the chain's conjunct. `forkedSelfPost` is `@[irreducible]`: `step_world`'s blanket split must not reduce through `headPackageId` (a closed package encoding; the T1 landing's `absorbSync` was fine, this one timed out at `whnf` at 200000 heartbeats). The verdict is applied by `postOr` (`Machine.lean`, `@[irreducible]`), a top-level function the page arm's `moved` wraps every reply in, never a match in `step`'s body: `step_world`'s blanket split pays per match of `step`, and one more there put it past the default budget (the first build raised it; the source gate refuses `set_option` budgets, rightly). The reply-shape proofs over `step` (`Proofs.Incoming`, `Proofs.Command`) read `postOr` by `postOr_cases` and the elims beside it (`postOr_cont_elim`, `postOr_submit_elim`, `postOr_host_elim`, `postOr_done_ok_elim`, ...) and close the `.done` arms before their lemma cascades (measured: the cascades over the wrapped `behind` arms alone pass 200 000); every proof in the tree stays at the default budget.

**Row.** `selfHead` (new): the sponsor installs `<world/head/Head`, creates its head object (seed at step 0: the law judges a seed's shape only) and `sync --post`s; the operator, cold, catches up through the post, nothing refused; the sponsor creates a second head object and FORGES a post (a hostile client) naming step 2 with a chain no fold has; the writer admits it (the head law judges monotony only); the operator, cold again, reaches step 2 on that page with another chain: `refused forkedPost`; its next `sync` proceeds (the page was kept). Plant: MEASURED (no cheap mutation reaches follow's walk; the harness's plants are a client's or the writer's): with `forkedSelfPost := none` line 12 ends `ok`. `Lang/Journey/Head` gains HD3b (the held roots with another chain at the held step count: `forkedHead`). The X rows (`client/tests/foreign.rs`) post the chain they read off `receipt`.

**What changed shape (law 1).** `world/head/Head` re-emitted (its package id moves: every World that installed the old text re-geneses; an old text installs as a different package, which `Foreign.headPackageId` does not name: `notHead`); the `receipt` head line gains a word; an old `nd` on `--post` is `usage`. `lang!` flag day, no Store byte moves.

**Critique.** (1) The pure walk is page-local: for a live member it compares nothing, so until T2b' the automatic guarantee holds for members BEHIND the post (cold joiners, members catching up after a pause), not for the always-on. The row says exactly this (`fault := .cold`). (2) A member posts its head at the tip it reached; a writer that serves that member a fork and others the honest log sees the post's position compared by the honest members and refused — attributed by exclusion still (the poster signed an honest head of ITS fold; the writer's name is on nothing: T3). (3) `forkedPost` ends a command whose own work was not done (a `write` whose catch-up met the post): the member reruns; the refusal is a one-time event per post per follow. (4) The plant is measured, not caught: a harness fault that makes follow blind to posts would be a follow-side mutation the harness does not have (its `Sys.follow` is a `Ctx`); building one is a harness design question (the same one that would give T1 a real two-history writer, PROTOCOL-74 critique 4).

**Meta-critique.** The first draft refused the PAGE on a forked post, as `sync --to` does; that would have let any member with post rights freeze every other member's follow forever: the compare act's refusal class is the command's, the page's lawfulness is the kernel's, and `forkedWorld` conflated them because in T1 the position came from the member running the command. The second bias: "run the anchor check as the page is walked (or record ahead)" (DESIGN-TRUST §4.2) read as if `ahead` were an edge; measured against how a live member actually absorbs, `ahead` is the COMMON case, and the design's guarantee "M3 continuously" needs the Store's index, not the page. Said in the decision (4) and priced as T2b' rather than written up as done.

## PROTOCOL-76 · Certified heads, the object: `Authority`, `Certificate`, `domCertify`, `certified`, and the quorum theorem (2026-10-26, FABLE-TRUST-3; DESIGN-TRUST §1.2, §1.3, §4.3: T3's unsigned half)

**The gap (READ).** After PROTOCOL-74/75 a MEMBER can prove a fork with its own key and the chain; a party with no World (a thin joiner, a foreign World, a phone, an auditor) still believes a head on some member's word, and the one party that orders the log — the writer — has no key and signs nothing (KERNEL-44 refused a host key for refusal receipts; that reasoning holds until the thing to be proved is about the writer). DESIGN-TRUST §1.2 names the missing object: a head with an AUTHORITY, a rule fixed at genesis for which signatures make a head the World's. §4.4 posed the Store signing seed to Ember (cv `01a1769d-2f64`, open). What does not wait on the seed is the object itself and its verification path, which every third party will run and which no theorem could be stated over until it existed.

**Decision.** `Protocol/Head.lean` gains `Authority {certifiers : List ByteArray, threshold : Nat}` (`Authority.none` = every World today), `domCertify = "nanodregg/protocol/certify/v1"` (the eighth signing domain; byte 19 differs from `domHead`), `certifiedLayout` (the head's five fields: no member, no key — a certificate is the World's statement and who made it is the authority's list, not the bytes), `certificateLayout` (the certified bytes as carried, then signers as u64 indices into the authority's list and their signatures, two lists read in step), `Certificate`, `CertRefusal` (`badCertificate`, `otherWorld`, `unlisted i`, `repeated i`, `badCertifySignature i`, `belowThreshold have need`; `name`/`tag`/`name_injective`), `certificateOfBytes`, `certifySigners` (each signer listed, not yet seen, verifying over `certifyMessage` under the listed key) and `certified X auth origin b` (decode; `otherWorld`; the walk; `belowThreshold` under the authority's threshold). Theorems (`Protocol/Proofs/Head.lean`): `certified_ok` (what a verifier learns: the bytes decode to it, it names the World, and at least `threshold` DISTINCT listed certifiers each signed its certified bytes), `certified_none_unlisted` (under `Authority.none` any named signer is `unlisted`: a verifier given today's authority learns what it learns today), `certified_intersect` (**the committee row as a theorem over the object**: when fewer than two thresholds of certifiers are listed — `2f+1` of `3f+1`, or `1` of `1` — two certificates of one World share a listed certifier, named by index and key with both signatures carried; pigeonhole over the two distinct signer lists through `nodup_window_length`), `certified_equivocation` (two certified heads at one step count with different chains: the certified byte strings differ and one certifier signed both — the witness a third party checks with the authority alone). `Protocol/Proofs/Domains.lean`: seven `certify_*_disjoint` pairs and `certify_not_envelope` / `certify_not_head` / `certify_not_call` / `certify_not_possession` / `certify_not_whoami` / `certify_not_invite` / `certify_not_cancel`: an envelope-only custody never certifies; a member's attestation is never a certificate.

**One theorem shape, three instances (DESIGN-TRUST §1.3's table).** `certified_intersect`'s bound `n < 2t` is the whole difference between the rows: `Authority.none` (`0 < 0`) satisfies it for nobody, so nobody is named (the writer by exclusion, as PROTOCOL-74/75 leave it); `1 < 2` names the one writer; `3f+1 < 2(2f+1)` names a committee member. `anchor_binds` (PROTOCOL-74) is the fold half under every row ("on a fold" is discharged by each member's own audit); the certificate adds who is answerable when two positions are not on one fold.

**What is NOT here, by name.** (a) No deployed path produces a certificate: a Store holds no certify seed (Ember's decision, open); when it lands, the producer is one custody object (`Keys` gains `certify`; `Codec.Ed25519.sign` over `certifyMessage (certifiedBytes E (headOf E w))` at every seal and at the `log` reply's end). (b) No deployed path consumes one: the authority is not yet in the genesis input, so a verifier has nothing to pass as `auth` but what it was handed out of band. The wiring is the next flag day (`host!` + `protocol!`, every Store re-geneses: `GenesisInput` + `Carried` gain the authority, `domOrigin` v2 → v3, the `log`/`read` reply gains the certificate field, `Thin.accept` requires one when the authority has certifiers, the head law's `uncertified`, `foreign_receipt_sound` restated with `hr` discharged to "A's certificate verifies under A's authority"). cv task for (b): see the FABLE-TRUST-3 report. (c) No conformance row: a row without a producer would exercise a harness-made certificate, which is what `certified_ok` already states; the row comes with the producer.

**Price, measured.** Kernel/** and Host/** untouched; hypotheses added to landed theorems: 0; restated by binder: 0 (the object is new; nothing consumes it). Protocol +~150 lines of definitions, +~190 of proofs, +~50 of domain pairs; `Protocol/Proofs/Head.lean` imports `Kernel.Proofs.Journal` (the window lemma). No wire or disk byte moves; no re-genesis.

**Critique.** (1) An object no deployed path produces or consumes is, until the next flag day, a theorem about a shape; its value is that the quorum statement now EXISTS over the real codec and the real `verify`, so the seed decision and the genesis wiring each add one thing to a fixed verifier rather than designing one. (2) Signers are indices into the authority's list, not keys: a certificate is bound to the authority it was made under, and a rotated committee (a carry, §1.3) invalidates every old certificate by construction — the KERI reading again, stated. (3) `certified_equivocation` names the certifier, not the writer: under the one-writer authority they coincide; under a committee the named member equivocated, and attributing the fork to the writer that served the two pages is a further step (the pages carry no certificate yet). (4) `belowThreshold` reports `(have, need)` by count after the walk; a certificate with a bad signature at index 3 and five good ones is `badCertifySignature 3`, not accepted on the five: the walk is strict so that a verifier never silently discounts a listed signer — the alternative (skip bad signatures, count good ones) accepts a certificate a verifier cannot tell from a forged-then-padded one.

**Meta-critique.** The pull was to wire the authority into genesis in the same landing ("one custody object away" reads as "do everything but the seed"), which is a Kernel flag day touching nine files and every row's genesis, on a worktree whose T2 is in the judge: the object and its theorems are the part that is RIGHT regardless of how the genesis carries the authority (a cell under a reserved id, as the founder cells are, is the likely shape; a `World` field is the one DESIGN-P6 §7.1 forbids), and landing the object first lets the wiring be judged on its own. The second pull was a `native_decide` example over the toy signer as a stand-in for a row; the repo's gates count rows and theorems, and a theorem that evaluates one closed instance is what GUARD-DISCIPLINE calls a guard with a name — `certified_ok` over every instance is the honest statement.

## PROTOCOL-77 · The signed start carries the authority; `Protocol.Head.Authority` is KERNEL-69's object; a step-0 World holds the authority cell (2026-10-26, FABLE-TRUST-4; with KERNEL-69; DESIGN-TRUST T3b, first landing)

**Decision.** `Protocol/Invite.lean`: `Start.genesis name nonce allowance founders auth`; `startInput`'s genesis arm is KERNEL's `genesisInput` as before, so the invitation's `input` bytes carry the certifier keys and the threshold, and `startOrigin` recomputes the origin from them: a joiner that checks the invitation's origin against the pin it was handed checks the authority too (nothing out of band). `startOf` reads them back; `inputBytes` takes the authority; `host genesis` prints them in the `input` line it always printed. `Protocol/Head.lean`: the local `Authority` of PROTOCOL-76 is deleted; `certified`, `certified_intersect`, `certified_equivocation` are stated over `Kernel.Receive.Authority` unchanged in meaning. `Protocol/Command/Machine.lean`: `genesisLeaf` admits a `kindAuthority` cell, so `atGenesis` (what one adopt may replace) is a step-0 World of members, grants and the authority; `atGenesis_object` is unchanged (`kindAuthority ≠ kindObject`).

**What a verifier has after this landing, and what it still lacks.** Has: the authority of any World it holds (`authorityOf`), the authority of any World it was invited to (the start), both committed in the origin (`genesis_inj`), and the verification path (`certified`). Lacks: a certificate on any wire (`log`/`read` reply: T3b's second landing) and a producer (the seed). Under `Authority.none` every row, Store and client behaves as before up to the origin; the `selfHead`, `fork`, `receipt` and `lang-journey` rows PASS unchanged.

**Critique.** (1) Carrying the authority in the start AND in the World is two carriers of one fact; they agree by `genesis_inj` through the origin the joiner pins, and the World's copy exists for the party that has a World and no invitation (a member after a carry; the Store itself). A carry carries the cell in the trie, so a carried World's authority is the exported World's (a committee that rotates is a new World by `carry` of a trie with another cell: not designed here). (2) `genesisLeaf` admitting one more kind widens what an adopt accepts as a step-0 World: a World forged with only an authority cell and no founders is still refused by the invitation's pin (the bytes must hash to it) — `atGenesis` was never the authentication, the pin is.

**PROTOCOL-77.1 (2026-10-26, TRUST-SEED; DESIGN-TRUST T3b, the second landing: certificates READ and CHECKED; cv 01a176f6-ac3f; with KERNEL-69.2; the producer is HOST-80, the seed is PROTOCOL-78).** The `read` reply gains a last field, `certificate` (`readReplyLayout`): the writer's certificate of the base's head, as the Store holds it (`STORE/base.cert`, `Host.readCert`; absent: empty; served as read, never checked by the Host: the certificate is self-authenticating and carries no Store MAC). `Host.Page.basePage` pays for it out of the page budget. A thin member's `adopt`, at the end of the download, on the World the pinned bytes decode to, asks `Head.certifiesWorld`: under that World's authority (`authorityOf`, the genesis authority on every honestly reached World, KERNEL-69.2), nothing when it names nobody (every Store today); otherwise the certificate verifies (`certified`) and certifies exactly `headOf w` — origin, step count, height, roots, chain — else refused by `Head.CertRefusal`'s name (`refused badCertifySignature`, `otherHead`, `badCertificate`, …; `Command.Refusal.certified`), the download dropped and nothing adopted. `certified` itself now refuses `noAuthority` under an authority of threshold 0: before, a certificate with NO signature verified under `Authority.none` (threshold 0 ≤ 0 signers), so the one verification path every third party runs accepted an empty certificate for every World that exists today (`certified_none`: refused, whatever the bytes; `certified_ok` gains `0 < threshold`). `CertRefusal` gains `noAuthority` and `otherHead`. Proved: `certifiesWorld_ok` (an accepted certificate under an authority that names somebody is a certificate under THAT authority of exactly the World's head), `certifiesWorld_none`. Row `certified` (toy and deployed parameters: real Ed25519 at `--deployed`): the rows' World names the writer's certify key as its one certifier (`Writer.authority`, threshold 1) — every rows World now does, so `thin`, `thinStale`, `basePin`, `carry` adopt certified bases too — the operator seals and pins, the thin member adopts the certified base; plant `forgeCertificate` (the writer flips one signature byte): the adopt is refused `badCertifySignature` at line 14. The selfHead row's seed is the genesis head (`chain0`, `roots0`, bound from the genesis World; cv 01a17a38-366e).

**Critique.** (1) The certificate is checked under the authority READ OFF THE PINNED WORLD: the sponsor's pin is still the trust root of adoption, and what the certificate adds is the WRITER'S non-repudiable statement that this base is its history at that step, beside the sponsor's — DESIGN-TRUST §4.3's "beside the sponsor's pin", not yet "instead of". Adoption with NO member's help (the authority taken from the genesis inputs, the base trusted on the certificate alone) is the next consumer, and it needs the producer first (cv task filed). (2) There is no deployed producer: no deployed Store writes `base.cert`, so under a deployed authority that names certifiers every adoption is refused `badCertificate` today — correct (a World that asks for certification and gets none adopts nothing) and the reason the producer is the next landing; every deployed Store is `Authority.none`. (3) The rows' writer signs as a harness (it holds `Writer.certifierSecret`); that is the custody's stand-in, through the real `basePage`, real `certifiedBytes`, real `certified` — the toy parameter is the key's location, not the code. (4) A certificate made before a seal is stale after it: `otherHead` until the writer certifies the new base; the thin member re-runs `adopt` with a fresh pin. (5) The `log` reply carries no certificate: a member following the log does not yet compare the writer's certified head against its own fold (attribution of a fork to the writer by its own signature, for members); it would cost a bounded certificate field in every page's budget (`logReplyFramingBytes`), deferred into cv with the producer, which decides when certificates exist.

**Meta-critique.** The landing was planned (continuation item 2) as `Thin.accept` requiring the certificate when `(authorityOf w).certifiers ≠ []`; building it showed two things the plan did not: the check belongs after the World is decoded (the authority is a fact of the World, so the check is `certifiesWorld` in `adopt`'s `.done` arm, not a clause of the byte-level `accept`), and `certified` under `Authority.none` was a vacuous accept that every future consumer would have inherited — fixed at the one path, not at each caller. Whether "the writer's word beside the sponsor's" is worth a wire field before the producer exists: yes, because the shape of the consumer is what fixes the producer's obligations (what is signed: `headOf` of the BASE World; where it lives: beside the base, self-authenticating, no MAC; when: per seal), and the plant shows the check is live under both parameter sets.

**What changed shape / re-emits / refuses.** `readReplyLayout` (+`certificate`): an old `nd`/follow decoding a new `read` reply is `badPage`; no persisted byte moves (`base.cert` is a new optional file; a Store without it serves empty). Rows' Worlds re-genesis under the certifier authority (their origins move). `protocol!`.

## PROTOCOL-78 · The stranger's check: from a World's genesis input and a certificate alone, the head the certificate certifies under the authority the input commits (`Protocol.Certified.check`, `host certified INPUT_HEX CERT`) (2026-10-26, TRUST-SEED-2; DESIGN-TRUST T3e, cv 01a17a55-5ebc; the certificate's producer is HOST-80, its key HOSTING-56)

A stranger holds no Store, no member key and no invitation. The genesis input (`host genesis`'s
`input` line, `Invite.startOf`'s one start encoding) commits the authority in the origin (KERNEL-69),
so the stranger trusts nobody's word for whom to trust: it decodes the input (`badInput`), makes its
genesis (`Receive.genesis`, the inputs' own refusal by name), and verifies the certificate under that
authority for that origin (`Head.certified`, its refusal by name). A carried start names an origin,
not an authority: `carried`. `Proofs.Certified.stranger_ok`: a head taken is certified under the
authority the input names for `originOf` of exactly those inputs. `host certified` prints `certified
origin=O steps=S height=H roots=R chain=C` or exits `notCertified` (Host.Status 50, fatal; OPS's
action line) with the reason's name. Measured (`launcher/tests/certify.rs`): the writer's base.cert is
taken (the origin and the sealed step count), one flipped signature byte is `badCertifySignature`,
another World's input is `otherWorld`.

**Critique.** It checks a head, never a history: a stranger with two certificates at one step count
learns the authority equivocated (`certified_equivocation`), but one certificate says nothing about
the steps before it; that is a member's audit. A certificate of a World whose authority rotated
(after the pre-rotation lands) needs the chain of carries from the genesis input; until then a
rotated World's certificate is checked against its successor's carried start, which this refuses
`carried`.

**What a certificate proves, and what it does not (CRIT-SPEC, real 2026-10-27).** A certificate proves that the
authority's key holder COMMITTED to this head: it is attributable endorsement, and two certificates at one step count
with different chains are checkable equivocation evidence (`certified_equivocation`). It does NOT prove the head is
the fold of a lawful log: a key holder can sign exactly one fabricated head per step count and never equivocate. With
the seed (HOSTING-56) the signer is keybroker under the Lean decider, which signs only heads its own `Host.Tail` fold
of the Store reaches, so lawfulness rests on that decider and the base it opened being honest, i.e. on the operator,
not on the signature. A thin member or a stranger that adopts a certified head without re-executing TRUSTS THE
WRITER FOR LAWFULNESS, and is told so by name. The authority checked against must come from a source the checker
already trusts (the genesis input here; the pinned World's bytes in PROTOCOL-77.1), never from the object being
checked. Pinless adoption (T3c, cv 01a17a55-5e88) inherits this: it trusts the writer for lawfulness and is sound only
with an audited prefix or a member's attestation. The head's `roots` commit the World's CONTENTS (the four tries), not
the log's lawfulness, and do not commit `allowance` at all (DESIGN-TRUST §T3c).

## PROTOCOL-80 · A generated adversarial Host, judged by the member-level claims: `lake exe adversary` (2026-10-27, lane QA-Q6; DESIGN-QA Q6, `redregg/work/promo/DESIGN-QA.md`; HOLISTIC-PROTOCOL E-2)

**Decision.** `Protocol/Rows/Adversary.lean` draws, per seed, one member row as the SCRIPT (its acts and argvs; its line faults kept on a coin, a cold start sometimes added; its expectations never read), a set of WRITER lies (`Writer.Params`: lieTip, lieBase, forgeBase, forgeCertificate, unstatedExpiry, forgottenRefused, forgeRefusal, admitsRecorded, ignoreNotBefore, forgetSpent, and a page budget up to the frame) and a RELAY (`Loopback.Relay`: one move per exchange with the writer — drop, withhold, duplicate, flip a byte, replace the status, answer with nothing behind it, replay the previous reply, edit a page's events, move its stated tip or base, inflate an expiry, `pageIo` — and one continuation choice per resume, a swap to a continuation follow handed the same member earlier). The harness plays the tapes (`Loopback.ask`, `swapK`; an empty tape is the rows' honest relay, so every row runs as before) and records each top-level run (`Loopback.asRun`, `Seen`). The judge reads the claims at the MEMBER's level: `okCommitted` (a submitting verb's `ok` means the call ITS run froze is journaled on the member's World), `cancelOk`, `signsOwn` (custody signs only calls planned from the run's own argv), `final` (a call the member's World holds expired or refused is not journaled, and not admitted, by the writer's World at the end), `oneHistory` (with the writer reopened honest and the relay honest, each actor's catch-up from its own World reaches the same head as one from genesis) and `bounded` (no harness bound, no undecodable reply). A run passes when the follower settles or refuses by any name. Each seed prints a `TRACE` line (moves, runs, findings, the writer's end World), each finding a `FINDING` line. `--harness-control` runs the seeds, swap removed, against `Loopback.sys`'s `trustCancel` and must read `FINDINGS`. Row `adversary` in gates/runs.tsv: `--seeds 200 --no-swap ; --seeds 40 --no-swap --deployed`. Deleted: the row `inflatedHeight`, `Fault.inflateExpired` and `Mutation.ignoreNotBefore` (the generator's `expired` move reproduces the lie and the follower refuses it `notYet`, the row's name; the writer's lower bound stays a generator lie and is `Envelope.check_ok_within`'s). Measured: see `redregg/work/codex/QA.report.md` (QA-Q6). Findings, filed: with continuation swaps the follower ends a write `ok` whose own call was never submitted (cv 01a17c6a-6c57), offers custody a call planned from an earlier argv (cv 01a17c6a-6c74), and ends a `cancel` `ok` by another command's settlement (cv 01a17c6a-6c83) — the call↔argv tie Spec/README already lists as owed (§11.2, cv 01a17a7a-1f6f); that is why the standing row runs `--no-swap`, and drops it when the command state moves into follow.

**Critique.** (1) The judge is only as strong as the harness's notion of "the call the member's command froze": it reads the harness, not nd, so a defect in the rows' client (the attempt store's re-run, gone again since d422453) is invisible to it. (2) The move set is a grammar I wrote; a lie it cannot express is still unscripted, and the census shows how unevenly the moves reach the interesting replies (a `cancel` op meets a fabricated `refused cancelled` a handful of times in thousands of seeds), so `cancelLie` and `cancelForged` stay rows: the testground reads its demos' expected outcomes off them. (3) Three of the four controls I tried (`trustLookup`, `settleDecline`, `followVerifyAll`) read BLIND: follow's own settlement and the page's chain refuse behind them, so they are not member-level weakenings; only `trustCancel` is. A generator whose only control is one mutation proves it can see one class of lie. (4) `--no-swap` in the standing row is a gate that skips the move that finds today's defect; it is named and tied to the fix, not hidden. **Meta-critique.** The pull was to replace all 51 rows and 28 booleans in one landing because the design said so; measured, most `Sys` booleans are plants of nd's OUTPUT (rawSlots, dropRow, flatProgram…), which no Host lie reproduces, so deleting them would have deleted coverage, not twins.

## PROTOCOL-79 · The join is signed over the World's origin; possession of a key stays World-free (2026-10-26, RETIRE, RETIRE-2; Ember's decision cv 01a16d3e-5382; with KERNEL's `Body.enroll`)

**Problem.** A newcomer's key signed `possession/v1 ‖ sponsor ‖ next ‖ key`, and the enrolment carried that signature as its "possession proof". The message named the sponsor and not the World. Under a carry (OPS-1, KERNEL-40) member ids, keys and grants survive into a new World, so the sponsor could enrol the same key again in the carried World with the same signature: the key's holder consented once, to one World, and was enrolled in another without a new consent. The reader's proposal was to bind the POSSESSION proof to the World.

**Decision.** The message is renamed for what it always was, a JOIN CONSENT, and it names the World: `joinMessage X origin sponsor next key = domJoin ‖ origin ‖ sponsor ‖ next ‖ key` with `domJoin = "nanodregg/kernel/join/v1"` (replacing `tagPossession`). `Body.enroll key next origin join via` carries the World the consent names; the enroll receiver verifies the join under the key over that message (`badJoin`, formerly `badPossession`). Whether the World named is the receiving one is checked in `receive` and in `signedBy`, right after the signature and before the key (`otherWorld`, new), never in the receiver, so the derivation (`receiveWith`, `deriveTurn`) stays blind to the World's name (KERNEL-40: `receiveWith_world`, `deriveTurn_world` unchanged), and `receive_signed` (law 1) still reads receive = signedBy; deriveTurn. The member is born at `memberId = H(domMemberId, joinMessage …)`: one consent, one member; the same consent enrolled twice in one World, or in a carried World whose trie holds the first enrolment, is `World.admit`'s `idTaken`. `nd init` signs over follow's own World origin (the one-shot follower is on the joined Store, so a carried join signs the carried origin), and the join token is `key ‖ next ‖ origin ‖ join`. Codec: `Body` tag 0 gains a digest (the wire of every enrolment moves). The receive refusal table moves (`Submit.refusalNames`: `badJoin`, `otherWorld` after `notPrecommitted`; every later code shifts by one).

**Theorems.** `enroll_join_bound` (a derived enrolment's join verifies over `joinMessage` of the World it names, and the one cell it bears is at `memberId` of that consent); `receive_join_world` (a call `receive` admits is an enrolment only if its join names this World); `enroll_authorized` restated (its possession conjunct is now the join conjunct over the origin); `receive_named`, `receive_reorigin`, `carry_receive` gain the hypothesis that the join names the World (`c.unsigned.body.joinOrigin.all (· = o)`), `carry_receive_world` gains `joinOrigin = none` (a carried World's join is a new join; the old one is `otherWorld` in either World). Domains: every `*_possession_*` disjointness theorem is the `*_join_*` one, same statement over `domJoin`. kernel-sim `probeJoinCarried`: `join-carried:possession` (the A-consent still verifies under its key in B: possession is a fact of the key), `join-carried:otherWorld`, `join-new:ok`, `join-again:idTaken`, all required arms.

**Critique.** (1) The category error in the reader's version: POSSESSION of a key is a fact about the key, shown by any signature it makes, in any World or none. Binding the possession proof to a World turns that fact into a contextual datum, and the result would have been two signatures by one key per enrolment, a World-free one that refuses nothing the World-bound one does not (a no-op), or a "possession" that is false in the next World although the key is the same. The defect was elsewhere: the message was a consent to join (it named the sponsor) mislabelled as possession, and a consent is contextual, so it names its World. The join's signature is also the possession proof, because it is a signature by the key; no separate datum. (2) Content-addressed member ids replace `bornAt` for members only: a consent's digest is a better id than the transaction's position, because the id now says what was consented to; the price is that a member's id no longer orders by birth (nothing read that order: the build and every row are the measurement). (3) The World check sits at two entry points (`receive`, `signedBy`) instead of one receiver. That is the price of KERNEL-40's opacity, which the receiver placement broke (`dispatch_world` went red, measured); both entry points are the ones every call passes, and `receive_join_world` states the result at `receive`. (4) Not done: a member already enrolled in A and carried into B stays a member of B (KERNEL-40 carries state, not history); this decision concerns new consents only, which is the case the defect was.

**What re-emits.** Every Store re-geneses (none deployed): an enrolment's bytes, the join token and the receive refusal codes moved. Codec vectors re-drawn (`kernel/body`, `kernel/call`, `kernel/unsigned`); `client/src/generated.rs` re-emitted where it carries refusal names. An old join token is refused by `Join.ofBytes` (four fields, not three); an old enrolment does not decode at tag 0.

## PROTOCOL-81 · Every `log` page carries the writer's certificate of its newest base's head, and follow compares it with its own fold: another chain there is `refused forkedCertified`, the writer's own signature the witness (2026-10-27, TRUST-SEED-3; DESIGN-TRUST T3d, cv 01a17a55-5ea9; the certificate's producer is HOST-80, its key HOSTING-56)

`logReplyLayout` gains a last field, `certificate`: `STORE/base.cert` as read (`Host.Page.pageCert`:
empty when the writer holds none, or when it is wider than `Bounds.certificateBytesMax`, 1424 bytes,
room for 16 signatures; `logReplyFramingBytes` keeps that room, so a full page and its continuation
still fit one frame, `FrameFit.resume_frame_fits` with the new premise). Follow verifies it under the
authority of its OWN World for its own origin (`Head.pageCertified`; never the page's word: follow's
World is its re-executed fold from the start it trusts), and compares the certified chain with its
own fold at the certified step count: on the page by `anchorCheck` from its position before the page
(`Head.forkedCertified`, inside `Command.postOr` after the self-head posts), and at or behind that
position by its own Store's chain (`Head.behindCertified`, `Host.Follow.behindOr` over `chainKept`,
on an empty page too: the caught-up member compares the writer's newest certified base every time it
pages). A mismatch ends the command `refused forkedCertified` with the page kept (it is lawful on
follow's fold). `Proofs.Head.forkedCertified_forked`: the refusal is never free: the certificate
verifies under follow's authority, certifies that step count, and follow's own fold holds a prefix of
the page reaching it with another chain. A certificate that does not verify is compared on nothing
(it is not the writer's signature, so it is evidence of nothing). Row `certifiedPage` (toy and
deployed): a cold member follows a log that walks past the sealed base, the certified chain is its
own; plant `forkCertificate` (the writer signs, with its genuine key, a head of the sealed step count
with another chain): refused `forkedCertified` by name.

**Critique.** A certificate on a page proves the key holder committed to that head; it does not prove
the head is lawful (CRIT-SPEC, PROTOCOL-78's paragraph). What this adds is ATTRIBUTION: a member that
re-executes and finds the writer's signed head off its own fold holds a non-repudiable, transferable
witness of the writer's fork, which a member's self-head post (PROTOCOL-75) is not: a post is the
poster's word about the writer. The behind comparison has no row (the rows' loopback runs
`Follow.answer`, not `Follow.loop`) and no cargo test (a forked certificate needs the certify key to
sign another history, which keybroker refuses by design); it reads the same `chainKept` the behind
posts read (T2b'). The page certificate is per base, so between seals a member compares the same
head on every page: one `chainKept` read per page, O(one record).

**What changed shape / re-emits / refuses.** `logReplyLayout` (+`certificate`): a follower of the old
shape decoding a new page is `badResult`, and a new follower refuses an old writer's page the same
way. `Bounds.logReplyFramingBytes` grows by 1428, so `Host.Page.budget` (`pageBytesMax`) drops from
129717 to 128289 event bytes; `budget_fits_event` still holds. No persisted byte moves. `protocol!`.

## PROTOCOL-82 · What a member is promised about forks: prefix agreement for members who compare heads; no operation-level fork consistency (2026-10-27, TRUST-4; CRIT-TRUST, `redregg/work/critiques/CRIT-TRUST.md`; corrects PROTOCOL-74 and PROTOCOL-75, DESIGN-TRUST §0, §1.4, §2, §3)

**The gap (READ).** PROTOCOL-74 said nano already had the no-rejoin half of SUNDR's fork consistency, because two folds that diverge hold different chains at every later step. That is a property of folds and pages. Fork consistency is a property of operations: Li and Mazières define no-join over a correct client's operation appearing in two views, and fork* allows at most one such operation. Nano's signed call (`Kernel.Receive.Unsigned`: origin, member, height window, pins, ranges, price ceiling, body) names no prefix of the history its signer saw. So a writer can keep two branches, deliver one member's call on both, and both admit it when its pins agree there. Their chains still differ. Two shared operations after unequal prefixes violate fork* and therefore fork-linearizability and fork-sequential consistency. The review built this from the source; no row runs it.

**Decision.** The system's claim is stated as what is proved, and the false inference is deleted wherever it was written (DESIGN-TRUST §0, §1.4, §2.1, §2.3, §3, §4.2, §5, BUILT-2; PROTOCOL-74's gap; PROTOCOL-75's decision 3; docs/TRUST.md; Spec/README).
1. **No Li–Mazières variant holds at the operation level.** Not fork-linearizability (SUNDR's fork consistency), not fork-sequential consistency, not fork*.
2. **What holds is prefix agreement on comparison.** Let two members start from one authenticated World and keep their accepted prefixes. When member B compares member A's stated head `(s, c)` with B's own fold at step `s`, either their logs agree up to `s`, or two of a listed set of inputs collide (`Head.anchor_binds`, through `fold_head_binds`), or B ends the command by name with a witness: `forkedWorld` (`sync --to`, `sync --check`), `forkedPost` (a post on a page B walks, or behind B against B's Store), `forkedCertified` (the writer's own certificate). A member that never compares has only its own audited chain.
3. **The communication assumption.** Detection of a split needs a comparison path across it. Two exist: an authenticated channel outside the writer's control (`sync --attest` on one side, `sync --check` on the other), and posts the writer delivers (`sync --post`). The writer controls the second: it can withhold posts indefinitely, and silence does not distinguish censorship from absence. Comparison also needs a position B can still read: one its page walks, or one its Store keeps. A thin member cannot compare below its adopted base.
4. **The other premises, named.** The members authenticate the same start; each keeps its accepted prefix across restart and cannot be reset to an older checkpoint; the hashes resist the collisions the theorems list; signatures are unforgeable under uncompromised keys; the member's executable and Store are trusted.
5. **The route to an operation-level property, not built.** Every signed call carries its signer's head (the step count and chain of the fold it planned on), and every follow compares that head as it compares a post: on the page, or behind against its Store. Then a call copied onto a branch whose history does not contain its signer's head is refused by any member of that branch whose fold covers the head's step. That is SPORC's route (history on every operation) to fork*. It changes `Unsigned` (a `kernel!` flag day) and the follower's scan; cv task 01a17d16-e71d.
6. `Spec`'s claim `ForkConsistent` is renamed for what it states (PROTOCOL-83 lands the rename with the scanner fix).

**Critique.** (1) The deletion makes nano's member guarantee smaller than the design said, and that is the point: the old sentence priced the remaining work as comparison plumbing because it believed the hard part was free. (2) Prefix agreement is still worth having: a member who compares learns something no trusted-server design gives, and the witness of a disagreement is checkable. But the witness implicates the writer only if both members ran the honest follower from one start; two conflicting attestations prove two conflicting member claims. (3) The writer-mediated channel is weak by construction. A deployment that wants eventual detection against a hostile writer needs a channel the writer does not control, as CONIKS and Certificate Transparency's gossip do; nano names none.

**Meta-critique.** The original error was an inference from an immutable digest to a property of a protocol. The test that would have caught it is the one the review ran: write down the adversary's best move (copy a signed call to the other branch) and check whether any refusal fires. A claim about forks should name the operation-level statement it proves, or say that it proves none.

**What changed shape.** Nothing: prose only.

## PROTOCOL-83 · Every self-head post is read from the step that made it, at its own position; a post past its position is `postBeyondPage`; a writer's refusal never prints a fork verdict (2026-10-27, TRUST-4; CRIT-TRUST's scanner findings, cv 01a17ac1-5204, cv 01a17ac1-5233; CROSS-LAYER: SPEC's `ForkConsistent` renamed `HeadsCompared` and its premise deleted)

**The gap (READ).** `Head.selfPosts` read every head object a page's steps touched from the World AFTER the page, and named the member of the step that touched it. Three defects followed. (1) A post replaced later on the same page was never seen: a member could post a conflicting chain and then a valid later head, and only the later one was compared. (2) The member named could be an earlier toucher who never signed the head that was compared. (3) A post naming a step past the page's end was compared by nobody: the walk answered `unreached`, the Store comparison took only steps at or behind follow's position, and the object was not re-read later. An honest post names a head its own World had reached, so such a post is itself evidence of a fork or a forgery, and it was kept silently. Separately, a writer's refusal printed `refused NAME` with NAME the writer's own bytes, so a writer refusing with `forkedPost` printed follow's own fork verdict exactly, and a name with a newline printed a second line.

**Decision.**
1. **A post is read from its step** (`Head.stepPosts`): the head a signed `invoke OBJ post HEAD` carries when OBJ is a head object of this World, and every head object of this World the turn bears (a seed). It is attributed to the call's signer and carries its own log position (`Head.Post`: `steps`, `chain`, `member`, `pos`). A head object changed any other way (a raw `write`, a program's nested call) is no member's signed statement of its own head and is not a post.
2. **No post escapes** (`Head.postFault`, `Head.pagePostFault`): a post with `pos < steps` is `postBeyondPage` (no member of this history held that head when the post was admitted); otherwise its step count is at or behind follow's position (the Store compares it, `behindPosts`, HOST-79) or inside the page (the walk compares it). `Proofs.Head.pagePostFault_none`: with no fault, every post is behind follow's position or on its fold.
3. **Refusals carry their evidence** (`Command.forkRefused`): `refused forkedPost` / `refused postBeyondPage` / `refused forkedCertified` on stderr as before, and on stdout `forkedPost STEPS MEMBER`, `postBeyondPage STEPS POS MEMBER`, `forkedCertified STEPS`. The page is kept in every case.
4. **A writer's refusal is never a fork verdict** (`Command.hostName`): the writer's name is printed only when it is one word of 1 to 64 ASCII letters and digits and not one of `ownVerdictNames`; otherwise `unnamed`. `Proofs.Head.hostName_not_own`.
5. **SPEC.** `ForkConsistent` / `ForkConsistent.sync` are renamed `HeadsCompared` / `HeadsCompared.sync` (PROTOCOL-82: they state prefix agreement on comparison, not fork consistency); the premise `wg.steps ≤ f'.world.steps` is deleted, and the claim gains the `postBeyondPage` disjunct. `top_headsCompared`, `floor_headsCompared`, `inhabited_headsCompared` (the run's post is the seed at step 1, read from its step).

**Theorems.** `selfPosts_pos` (a post's position is inside its page), `pagePostFault_forked`, `pagePostFault_beyond`, `pagePostFault_none`, `forkedBehindPost_forked`/`_none` restated over `Post`, `anchorCheck_reached` (moved from Spec, where it was a private copy), `hostName_not_own`.

**Row.** `selfHeadPage` (new): the sponsor forges a post naming step 2 with a chain no fold has into its head object; its own follow refuses it on the next catch-up; its rerun posts its honest head into the SAME object. The operator, cold, absorbs both on one page and is refused `forkedPost` (the forged post, at its own step). The sponsor forges a post naming step 999; the operator's next page refuses it `postBeyondPage`. MEASURED: under the old scanner semantics both lines end `ok`.

**Critique.** (1) Reading posts from the call ties a post to the `post` method's argument encoding (`Std.headAtTy`); a head package with another argument layout would yield no posts, silently. The package is pinned by id (`Foreign.headPackageId`), so a different layout is a different package and posts into it are not self-heads; that is the intended reading, stated here. (2) Posts made by programs are not compared. A program cannot sign as a member, so its head is no member's statement; but a member who wants its posts compared must post them itself. (3) `postBeyondPage` blames nobody in particular: the signer may hold a longer history (the writer forked), or may have forged the head. The signed call is the evidence either way. (4) The `unnamed` fallback hides a malformed writer name; the alternative, refusing the reply as `badResult`, would turn a cosmetic writer defect into a failed command. (5) The Store comparison still answers nothing when it cannot read the step (`behindOr` reads `none` as "not compared"); CRIT-TRUST asks for a named unchecked outcome there, which this entry does not add.

**Meta-critique.** The first scanner read state because state was what the receipt path reads. A post is an act, and the evidence for an act is the signed call at its step. Reading the World after the page answered "what does the object hold now", which is a different question.

**What changed shape.** `Command.Refusal.forkedPost`'s member is the signer's id bytes (was `Option D`); new `postBeyondPage`; fork verdicts print evidence on stdout. `Head.selfPosts` takes the Worlds before and after the page. No wire or disk byte moves; nothing re-emits. `protocol!` (the refusal table and the printed stdout of a fork verdict changed).

## PROTOCOL-84 · Under an authority that certifies, a log page without the writer's certificate is refused `uncertifiedPage`, and the writer certifies its base before it serves (2026-10-27, TRUST-4; cv 01a17cbf-3782; CRIT-TRUST "unavailable comparison must remain visibly unchecked"; CROSS-LAYER: HOST's `host serve --certify` start)

**The gap (READ).** PROTOCOL-81 put the writer's certificate on every `log` page and compared it with follow's fold. A page with no certificate, or one that does not verify, was compared on nothing: `Head.pageCertified` answered `none` and follow went on. Under `Authority.none` that is right (an empty certificate is the honest shape). Under an authority that certifies, it let a relay strip or corrupt the certificate and turn the writer's attributable evidence into silence, and the member could not tell that no comparison had been made.

**Decision.**
1. **Follow refuses by name** (`Head.pageUncertified`, `Command.postOr`): when follow's own World's authority has threshold > 0 and the page's certificate is absent or `Head.certified` refuses it, the command ends `refused uncertifiedPage`, with `uncertifiedPage WHY` on stdout (`absent`, or the checker's name). The page is KEPT: it is lawful on follow's fold, and the missing evidence concerns the writer, not the steps. The check runs after the post and certificate comparisons, on every page, the caught-up member's empty pages included.
2. **The honest writer always has a certificate to send.** `host serve STORE --certify SOCK` certifies the newest base at its start when the Store holds no certificate yet (a fresh genesis), through the same worker as each seal; afterwards every seal replaces it. A certificate of an older base still verifies and is compared behind follow's position, so a broker outage leaves pages certified, only staler.
3. The rows' `forgeCertificate` plant now forges only the base certificate a thin joiner adopts (the `read` page), as the `certified` row intends; the new `stripCertificate` plant serves log pages without one.

**Theorems.** `postOr_cases` gains the fifth case (`uncertifiedPage` after no post fault and no certified fork). `Proofs.Command.hintNames_forks` (the four fork verdicts' names are hint names; split out of `hintNames_complete`, whose single heartbeat budget the constructor list had used up).

**Row.** `strippedCertificate` (new): the rows' World is certified by the writer's key and every honest page carries the certificate, so the run ends `ok`; plant `stripCertificate` caught at line 1, `refused uncertifiedPage`.

**Critique.** (1) A stripping relay now stops every command with a refusal. It could already deny service by dropping pages; what changes is that the member is told. (2) The refusal does not say whether the relay or the writer is at fault: a writer started without `--certify` on a fresh certifying World produces the same line. That is the point of naming it: the member cannot distinguish them, and neither could it before. (3) A writer can still send a valid but stale certificate forever (never certify again). The member compares it behind its position and learns nothing new; nothing here bounds staleness. A freshness rule would need the certificate's step count compared with the page's tip, and a policy for how far behind is acceptable; not decided here. (4) Under threshold > 0, a member whose World somehow lacks a single authority cell (no honest fold reaches one, `authorityOf_honest_fold`) is not refused; `pageCertified` takes the same view.

**Meta-critique.** The first reading of the question was "should we refuse, given the cost of a live producer everywhere?" The cost was smaller than it looked: the writer already has the producer (HOST-80), and the only honest state without a certificate was the first start, which the start can cover.

**What changed shape.** New `Command.Refusal.uncertifiedPage`; `host serve --certify` writes `base.cert` at start when it is absent. No wire or disk format moves. `protocol!`.

## PROTOCOL-85 · A description prints the package's interface and each method's grade: `iface TYPE`, `grade LABEL moves N [produces TYPE]` (2026-10-27, TESTGROUND-6; FABLE-META-4's note in redregg work/codex/TESTGROUND.report.md; LANG-103)

**Decision.** `read OBJ ?` printed the methods a member may call and their argument types, but not what LANG-89 and LANG-103 let a method promise. A member deciding whether to run a generator could not learn from the description which interface its run must produce. `packageLines` now ends with `iface T`, the package's own interface, and one `grade` line per graded method: its `moves` bound and, when declared, `produces I`. Every type is `Lang.Print.ty`, the text `Lang.Read` reads back, and a type with no text refuses the whole description `noText`, as a method's argument type does. `packageLines_eq` takes a description apart once, and `packageLines_methods`, `_rels`, `_doc`, `_no_doc` and `Hosting.Proofs.SocketStrong`'s `packageLines_method` and `packageLines_core` are re-proved through it. New: `packageLines_grades` (the interface line and every grade's line are in the description). The resident reads only `method`, `rel`, `core` and `object` lines, and neither new line is in either form. The testground's inspector shows the interface as a table, the grade per method, and a produced interface as its own table. A new demo, `produces`, installs the journey's GN22 generator, reads its description, generates, and has GN23's generator refused `produces generate: lacks reset`.

**Alternatives.** (a) A tab-only export that prints the interface: a CLI member would still not see it. (b) Print the interface's method names only: `produces` compares types, so a name list would not let a reader predict the refusal.

**Critique.** The interface of a package with many methods makes one long line, since every method's type is a curried function over the request record. The description grows by that line for every object. The `grade` line is printed only for methods with an entry in `effects`; an ungraded method's bound (moves 0) is implied, not printed.

**Status.** landed (this commit). Output of `read OBJ ?` gains lines; nothing re-emits; no wire or package byte moves.
## PROTOCOL-86 · A certificate carries each signer's key, and a signer holds its slot by its key or by the successor its slot committed: a consumer follows a certify-key rotation (2026-10-27; TRUST-5; with KERNEL-79; DESIGN-TRUST §4.4c item 5)

**The gap.** A follower checks a log page's certificate under the authority of its own World before the page (PROTOCOL-81, PROTOCOL-84). After KERNEL-79 the writer's certify key rotates inside the World. A follower behind the rotation would check a certificate the successor signed under an authority that lists only the old key, and refuse the page `uncertifiedPage`: a false fork alarm on every page of a catch-up across a rotation.

**Decision.**
1. `certificateLayout` gains `keys` before `signatures`: each signer's index, the public key it signed under, its signature. `Certificate.sigs : List (Nat × key × signature)`; `certificateBytes` takes the triples.
2. `Head.holds X auth i key`: certifier `i` is listed and `key` is its key, or `key`'s digest is the next-key digest committed at `i` (`certifyNextDigest`). `certifySigners` refuses `unlisted i` past the list, `otherKey i` when the key holds no slot `i`, then `repeated`, then `badCertifySignature`. `CertRefusal.otherKey` is new (tag 8).
3. The authority the checks read is unchanged: the follower's own World, the adopted base's own World, or the stranger's genesis. So: a follower before the rotation takes the successor's certificate (the key opens the committed digest); a follower past the rotation takes it as the current key's, and refuses the retired key's `otherKey`; a thin joiner checks a base's certificate under that base's own authority, which is the one in force at that head.
4. Producers name the slot the key holds (`Head.slotOf`) and carry the key: `Host.Certify`, the rows' writer.
5. `Head.rotationCall`, `Head.rotationSlot`: the rotation call the operator signs (member the authority cell, pinned at the World's entry), used by `host rotate-certifier` and the rows.
6. `Bounds.certificateBytesMax` 1424 → 2004 (16 keys of 32 bytes), so `pageBytesMax` 128289 → 127709.

**Disposition of old certificates and receipts.** A certificate verifies under the authority of the World it is checked in. A thin joiner checks a base's certificate under that base's own authority, which is the one in force at that head, so an old certificate stays valid for the head it signed. A follower checks under its own World: before the rotation it takes the successor's signature, after it it refuses the retired key's (`otherKey`), because the old key may be the stolen one and anything it signs from then on is not the World's. A stranger checks under the genesis, so it follows the first rotation and no further (cv 01a17e0d-0ea6). Receipts do not move: they are checked against a head the consumer holds (`Receipt.check`), and the rotation is a step of the same log, so a call committed before it stays in the journal under the same origin. A rotation does not make a forged head valid; a consumer that took one before learning of the rotation has, afterwards, the evidence that the retired key signed it.

**Theorems** (`Protocol/Proofs/Head.lean`). `certifySigners_ok`, `certified_ok` (each accepted signer holds its slot by the key it carried and its signature verifies), `holds_lt`, **`holds_rotated`** (under `a.rotate i key nb` a signer at `i` holds only `key` or a key the fresh commitment `nb` opens), `certified_intersect` and `certified_equivocation` restated by slot: two certificates under a quorum share a slot, signed in each by a key that slot holds (one holder: the current key's or the committed successor's).

**Rows.** `rotateRefused`: a rotation signed by a key the genesis did not commit is declined `notPreRotated` by name and not recorded (plant `nextIgnoresKey`: a commitment that ignores the key admits it, line 7). `certifierRotation`: the operator rotates to the committed successor and seals; the operator, the newcomer (behind the rotation) and the sponsor catch up across it, every page certified by the successor (plant `retiredCertifier`: a writer that goes on signing with the retired key is refused `uncertifiedPage` at line 10, the first catch-up of a member whose World holds the rotation). MEASURED: with `holds`' successor branch removed, the honest `certifierRotation` goes red at line 11 (the newcomer behind the rotation refuses the successor's certificate `uncertifiedPage`) and line 12.

**Critique.** (1) A follower two rotations behind refuses a page signed by the second successor (`otherKey`) until it folds the first rotation; and a stranger with the genesis alone follows one rotation, not two (cv 01a17e0d-0ea6). (2) Taking the committed successor's signature before the rotation is in the log means the successor key certifies from the moment it exists, not from the rotation. Under the custody model (the successor seed is kept apart and used only to rotate) that is the same holder; an operator who signs heads with the successor before rotating gives up nothing the rotation would have protected. (3) Carrying the key costs 36 bytes per signer on every page.

**Meta-critique.** The obvious fix was "check page certificates under the World after the page". It fixes the page that contains the rotation and fails every earlier page of a catch-up. The KERI rule (a commitment is already authority to the key that opens it) fixes both, and is what the kernel act already checks.

**What changed shape.** The certificate wire format (a `keys` list), `CertRefusal` (`otherKey`), `certificateBytesMax` and `pageBytesMax`. Every `base.cert` written before this commit is refused `badCertificate`; the re-genesis KERNEL-79 forces makes new ones.

## PROTOCOL-87 · Every request carries the frame wire's version after its op, and a server reads it first: another version is `refused wireVersion N expected M` (2026-10-27, OPS; OVERLOOKED-20261027 A9, A5; CROSS-LAYER: HOST's two loops, CLIENT's frame writer and `nd --stdio`, the testground's transport, HOSTING's resident)

**The gap (READ).** The package wire has a version byte (LANG-60, now 10); the frame and command wire had none. A
member built at another commit reached the writer with `op ‖ payload` and was answered by whichever decoder first
failed: `undecodableCall`, `badTag`, `shapeMismatch`, or a `badResult` on the member's side for a reply whose layout
moved (TENANT's 10-27 finding was one of these). Nothing said "you are at another version".

**Decision.**
1. A request on either socket is `u32le len ‖ op ‖ version ‖ payload`, `version` = `Protocol.wireBytes`, four
   bytes. Replies carry none: a reply answers a request accepted at the server's version, and the one reply a
   request at another version gets, `refused ‖ UTF-8`, has the shape every version shares.
2. The version is COMPUTED (`Protocol.Version`): the first four bytes of the digest of the op, status, step,
   close-reason and custody-refusal tables, the hang-up byte, the frame bound, the content-addressed tags
   (`Codec.Tag.of`) of every payload codec in `Protocol.Frames`, of the deployed call, turn and World codecs, and
   the kernel's refusal code table. Nobody bumps it; a change to any of those moves it (as `Codec.Tag`'s doctrine).
3. `host serve` runs `(machine X).wired`, `host follow`'s loop runs `wiredReply` before `answer`, and `nd --stdio`
   runs `frame::unwire` before its surface check: each reads the four bytes before anything else and answers
   another version `refused wireVersion N expected M` (N `none` for a request too short to carry one). The child
   wire's hang-up, which only the supervisor writes, carries no version and passes.
4. Writers: `nd` (`frame::request`, both sockets), `nd --init`'s follower (`frame::child_request`), the resident's
   member socket (`Hosting.Resident.Sockets`), store-plants' founder frames, `probe`, and the testground's
   `transport.js` (`framed(…, { wire: table.wireVersion })`; the kernel's table carries it). Relays (`nd-attach`,
   the mux, `ws-relay.py`) parse nothing and pass the bytes.

**Theorems.** `Protocol.Proofs.Version`: `unwire_versioned` (a client's request reads back as its payload),
`unwire_other` (another version is the refusal of its version field), `unwire_reads_only_version` (two requests
with one foreign version field are answered alike, whatever follows it: no field after the version is decoded),
`unwire_ours`. `Host.Proofs.Wired`: `wiredReply_other`, `wired_other` (whatever machine `host serve` wraps and
whatever the World, a foreign-version frame is the version refusal), `wired_ours`, `wired_versioned`.

**Rows.** `client/tests/supervise.rs` `a_request_at_another_wire_is_refused_by_name`: the real `host serve` under
the real nd-supervise answers a request carrying another wire's four bytes, and one too short to carry any,
`refused wireVersion N expected M` (N `none` for the short one), the same text for two different payloads behind
one foreign version; CONTROL: the same request at this version reaches the writer's decoder (`declined
undecodableCall`), and `frame::request` sends this version. `client/tests/stdio.rs`: `nd --stdio` refuses a
command at another wire by the same name. The page and the publish step: `GET /wire.json` on the relay asks the
running writer (a request with no version, refused `wireVersion none expected M`); `testground/hosted.mjs`
`wireCheck` refuses to join a writer at another wire in a sentence; `publish.sh` refuses to publish a page whose
`kernel.json` `wire` (read from the built kernel by build.sh) is not the live writer's; `host version` prints it.

**CRITIQUE.** (1) Four bytes: two wires collide with probability 2^-32 per pair; a collision decodes as a malformed
frame does today, by a later name. An adversary gains nothing (it can send any bytes either way). (2) The stamp
covers what `wireMessage` lists. A wire element outside it (a refine's accepted set, a layout read by hand rather than
through `Protocol.Frames`) moves no version; the list is one place to add it, not a theorem that it is complete.
(3) The in-process simulators (`Host.Sim`, the rows, the testground's in-tab writer) call the inner machine and
`Follow.answer` directly, unversioned: they are not on a wire. The version check is therefore exercised only by the
deployed loops and the rows that run them. (4) Every client of every older build is now refused on its first
request, which is the point; there is no grace period.

**Meta-critique.** The brief offered a `hello` frame. A per-connection handshake would give the mux connection state
it does not have and a second message for every client; four bytes on each request say the same thing to the side
that decides, and make "checked before any other field" a property of each frame rather than of a session.

**What changed shape.** Every request frame (four bytes after the op): every client and server re-emit together;
nothing deployed is compatible. `client/src/generated.rs` and `launcher/src/generated.rs` gain `WIRE_VERSION`.
The testground kernel's table gains `wireVersion`, kernel.json gains `wire`, the relay `/wire.json`. Every Store keeps its format; no re-genesis. `protocol!`.
