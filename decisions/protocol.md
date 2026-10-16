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
**Status.** open; ROOT to rule.

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
**Status.** open; needs HOST and ROOT; maybe Ember (product: who may consent).

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
**Status.** open; KERNEL and HOST to answer.

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
**Status.** open.
