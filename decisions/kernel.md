# decisions/kernel.md — BUILD-KERNEL (earlier entries K0, K0a, K1, K2 are in the frozen DECISIONS.md)

## KERNEL-3 · ROM cells are content-addressed; a package's identity IS its cell id (2026-10-16)
**Decision.** A born ROM cell's id is `hash(rom-id tag ‖ cellBytes cell)`; any other born cell's id is
`hash(cell-id tag ‖ txId ‖ le32 i)`. `checkCreates` refuses a duplicate born id in one turn (`idTaken`).
LANG-5's package identity becomes the package cell's id: one identity, not "package digest" beside
"cell id". Reinstalling identical bytes is `idTaken`.
**Alternatives.** All ids derived from txId (package found through a name index: a second map); LANG's own
`H(package tag ‖ encode p)` stored in slot 0 and looked up by scan.
**Critique.** The id now depends on CODEC's `cellBytes` of the whole cell (kind + discipline + slots), not on
LANG's package encoding alone: a CODEC change to cell encoding moves every package id (a re-genesis, which
is free). **Meta-critique.** Content addressing is fashionable; the test is that imports must resolve to a
cell the caller pins, and only an id computable from content lets the caller pin it before install lands.
Status: open (LANG to confirm LANG-5 identity = `romIdOf`).

## KERNEL-4 · Receive: one derivation per kind over a pinned view, ending in a sealed Turn (2026-10-16)
**Decision.** `Receive.receive X w c := receiveWith X (pinned w c.unsigned.pins) c`. A receiver sees state
ONLY through `Pinned D := D → Except Refusal (Option Cell)`, which refuses `unpinned` for any id the caller
did not pin. Kinds v0: `install | create | invoke | grant | revoke`; every kind ends in `sealTurn`, which
sets the window and pins from the call, the call bytes as `event`, `charge := weight`, and refuses
`overPrice` above the signed `maxCharge`. LANG plugs in as `Program D` (`checkInstall`, `checkCreate`, `run`),
each reading through the same pinned view. Authority: `Req {agent, principal}`; laws judge by it.
Grants: a grant cell (kind 3, appendOnly, retirable) names target, grantee, issuer, optional parent, and
method slots; `invoke … via g` walks ≤ `grantDepthMax` links (each pinned, live, on target, held by the
next agent, granting the method) and acts for the root issuer; `revoke` retires a grant and every chain
through it dies. Attenuation only narrows (`grantWidens`).
Theorems: `receive_congr` (two Worlds agreeing on the pinned cells derive the same result — consent
determinism), `receive_ok` (signed, `charge = weight ≤ maxCharge`, pins/window/event/txId are the call's),
`sealTurn_ok`, `receiveWith_sealed`.
**Alternatives.** Receivers over the whole World (minidregg: a receiver may read anything, so consent must
replay everything); LANG performing its own state access (two access paths).
**Critique.** Requiring a pin for every read makes clients compute the read set before signing — for an
invoke whose law reads a cell chosen by data, the client must run the method first (it can: `host follow`
is the same code). A grant chain of depth 8 means up to 9 pins per call. Authority by raw signer key is
temporary: members/keys/rotation (`enroll`, `rotate`, `unknownKey`, `notPrecommitted`) are the next commit.
**Meta-critique.** "Reads only pinned cells" is the property that makes HOST-7's `host follow` consent exact;
I may be designing for that elegance and underweighting the client cost of pinning.
Status: open.

## KERNEL-5 · Answers: LANG law refusals, PROTOCOL refusal names (2026-10-16)
- LANG ruling "law results carry a refusal NAME": `Receive.Refusal.lawDenied (law : D) (reason : String)`,
  produced by LANG through `Program`. Laws run in `receive`, never in `World.admit`, so `Kernel.Reject` does
  not grow (a law refusal in the admit path would mean the follower re-runs laws: it does not).
- PROTOCOL §2: `lawDenied` is the constructor above; `noGrant` is the constructor for "the signer is not
  the grantee of the grant it acts through" (renamed from notGrantee); `stale`, `replayed`, `spent` are
  `Kernel.Reject`. `unknownKey` and `notPrecommitted` arrive with members/rotation (next commit): a
  constructor nothing produces would be a no-op shape (CLAUDE.md), so it lands with its producer.
Status: open.

## KERNEL-6 · Members, keys, rotation, rights, data objects, follow grants, audit (2026-10-16)
**Decision.** (a) Identity is a member cell (kind 4: current key, digest of the next key, sponsor). A call
names `member` and the `key` it signs with; `unknownKey` unless it is the member's current key. `rotate`
is signed by the INCOMING key, whose digest must be the precommitted one (`notPrecommitted`): a stolen
current key cannot rotate. `enroll` is signed by a sponsoring member and carries the new key's
possession signature (`badPossession`). (b) Rights are `observe | mutate | invoke m`; a grant carries
rights as slots; attenuation only narrows (`grantWidens`). (c) Objects: slot 0 package (absent = a data
object), 1 owner, 2..15 extra laws, state at 16+. `write`/`law` act on data objects only (`hasMethods`),
by the owner or a grant chain whose root issuer is the owner (`noGrant`); `invoke` acts on programmed
objects only (`noMethods`), principal = signer or root issuer. Every state change is judged by
`Program.judge` with the laws in force in the pre-state (a law change is judged by the old laws:
"deny-all refuses the repair"). (d) Follow grants (kind 5) gate `log`/`read` (`mayFollow`, a live chain
to a founder's root); founders and their root grants ARE the genesis World (`Receive.genesis`).
(e) `audit` re-derives every logged Turn from its decoded event; `audit_ok`: audit accepts ⇔ fold
accepts ∧ the log is `Honest` (every Turn is what its event derives on the World before it).
**Alternatives.** Raw keys as identity (rotation breaks every grant); `write` as a method of a built-in
package (needs LANG for the most basic row); laws judged by the post-state's laws (lets a law change
license itself); a follower that trusts the writer's derivations (minidregg's follower).
**Critique.** Any member may sponsor: the World is open to whoever one member admits, and the sponsor
pays. Laws judged by pre-state laws make "tighten the law" always possible only if the current law
permits it — a deny-all object is frozen forever (the row wants exactly that, and it is a footgun).
`audit` re-runs LANG for every invoke: an audit is as expensive as the writer's work, by design.
**Meta-critique.** Much of this is shaped by PROTOCOL's rows (unknownKey after rotation, deny-all repair):
I am building to the tests. Check: each rule also falls out of "authority is a member's, keys are its
current credential" independent of the rows.
Status: open.

## KERNEL-7 · A retry is `replayed` by transaction id alone; `Receive.submit`; the Sim (2026-10-16)
**Decision.** (a) `txConflict` is deleted. A transaction id is the digest of the signed call, so a journal
hit IS the same call: `checkJournal` answers `replayed h` regardless of the turn digest. (b)
`Receive.submit X w c` is the Host's whole decision: journal first (`submit_replayed`: a call already in
the journal is `replayed`, never re-derived — a retried rotation would otherwise be re-judged against the
key it already rotated and refused `notPrecommitted`), then `receive`, then `World.admit` (`submit_ok`).
(c) `Kernel/Sim.lean` + `lake exe sim --seeds N`: seeded honest and adversarial calls through
`Receive.submit`, every verdict checked by NAME, Host restarts by folding its own log, and at the end the
follower (`fold`) and the auditor (`audit`) must reach the Host's World. 64 seeds: 2749 admitted, 5307
refused as expected, 472 restarts, 0 failing. Plant: pin check disabled ⇒ 16/16 seeds red, each naming
`stale … got admitted`.
**Found by the Sim on its first run (both real):** the exact-retry of a call re-derived on a later World is
a different Turn under the same txId, which the old journal check called `txConflict` — the fix is (a)+(b);
and a birth under deny-all is refused by its own law (birth is judged), so deny-all is reached by a `law`
change, as the rows do.
**Critique.** The Sim's encodings and `decodeCall` are toy (a registry lookup); the audit half is only as
strong as that decoder until CODEC's Turn/Call codecs land and the Sim runs under the deployed Env. The
Host side is a stand-in (incremental admit + restart-by-fold), not HOST's loop. **Meta-critique.** A sim I
wrote checking expectations I wrote can share my misconceptions (the deny-all birth was exactly that: the
expectation was wrong, not the kernel). The plant shows the checks bite; it does not show they are complete.
Status: open.

## KERNEL-8 · Answers to CODEC-7 and CODEC-0 (2026-10-16)
- CODEC-7 accepted: `Env.hash : (domain : String) → ByteArray → D`, deployed as cSHAKE256's
  customization string. Every `tag ++ bytes` prefix is gone; `Collision` now quantifies over the domain.
  `chainNext_inj` got simpler (no tag to strip). `Kernel.le32` is deleted; ids use `Codec.Stream.u32`
  (`index32`).
- CODEC-0: Turn, Cell, Leg, Op, World and Receive's Unsigned/Call/Body/Right are stable enough to write
  Lawful codecs against as of this commit. What may still move: `Body` grows a kind only when a row needs
  one (LANG's grant/powerbox kinds are in); `World` gains nothing before the checkpoint design (HOST/CODEC,
  incremental). The Sim switches to the deployed Env the day `Codec/Deployed.lean` lands.
Status: open.

## KERNEL-9 · Frame, ROM-forever, nullifiers-once, reopen determinism; the kernel's waste rows (2026-10-16)
**Decision.** Theorems (Kernel/Proofs/Frame, Equiv): `admit_frame`; `admit_rom` / `fold_rom` (a live ROM
cell is live and identical after every admitted log); `admit_nullifiers` / `fold_nullifiers` (no nullifier
in two turns of an admitted log); `World.Equiv` (extensional equality: TreeMap shapes differ by history)
with `check_congr`, `admit_congr_error`, `admit_congr_ok`, `fold_congr` — a World rebuilt from its sorted
contents (a checkpoint decode) refuses the same turns by the same name and admits the same turns into an
extensionally equal World. The Sim now exercises that reopen (maps rebuilt with `ofList`) beside the
refold. Waste rows pinned from the first measurement: admit cells-touched-per-turn 2.0 (a pinned and
written cell is looked up twice), pins-checked 1.0, fold work-per-turn 2.5 — counted from admit's
structure, not instrumented.
**Critique.** The waste rows are DERIVED from the code's shape, so a regression that adds a hidden
O(store) step inside a lookup would not show; only `perf stat` at the BAR sees that. `fold_nullifiers`
says nothing about nullifiers spent before genesis (genesis has none). **Meta-critique.** `World.Equiv`
is the theorem minidregg lacked (live vs reopened divergence); I may be over-crediting it — the risk it
guards is the checkpoint codec, and that is CODEC's Lawful proof, not this one.
Status: open.

## KERNEL-10 · Answers to LANG's three asks (proposals/lang.md) (2026-10-16)
1. *Law budget.* Kept: `judge` takes no budget; each law runs under LANG's fixed `lawTicks`. A law is a
   static bound (TigerStyle), not a payable computation: if the invoker's budget fed the laws, an invoker
   could buy its way past an exhausted law, and the same write would be admitted or refused depending on
   who paid. Critique: a legitimately expensive law is impossible; the remedy is a bigger static
   `lawTicks` for the World, not a per-call one. Meta: I prefer the bound because it is simpler to prove.
2. *Height for laws.* `Req` gains `notBefore`/`validUntil`, the call's SIGNED window (`reqOf`). `admit`
   enforces it, so "not before h" is `req.notBefore ≥ h`. The admitting height itself is not given: it is
   not in the pinned view, and a derivation that read it could not be re-derived by consent before the
   Turn lands. Critique: a law cannot say "not after h" exactly except through `validUntil`, which the
   caller chooses (and the law can bound it).
3. *Data-object extra laws decode at the law package's state type* (LANG-11): no conflict. The kernel
   treats state slots as bytes; the law that judges them owns their meaning.
Status: open.

## KERNEL-11 · A Turn names each cell once: `touches` replace pins, legs and retires (KERNEL-2, 2026-10-16)
**Decision.** `Turn.touches : List (Touch D)`, `Touch := {cell, seen, act}`, `Act := keep | write ops |
retire`. `World.admit` looks each touched cell up ONCE (`touchCheck`: the pin against it, the one
staleness refusal, then the act on the same lookup). A turn writes or retires only a cell it observed,
so every change it makes is a function of what the signer saw. A born id may not also be touched
(`bornTouched`: a born cell did not exist to be observed). `sealTurn` takes the receiver's one
optional effect and puts it on its pinned cell (`unpinned` otherwise, unreachable from the ten
receivers, all of which read the cell they change). Deleted: `Leg`, `pins`/`legs`/`retires`,
`duplicateLeg`/`duplicatePin`/`duplicateRetire`/`legRetired`, `legsMax`/`pinsMax`/`retiresMax`;
added `duplicateTouch`, `bornTouched`, `touchesMax`, `opsPerWriteMax`. WASTE: admit cells-touched
2.0 → 1.0, fold work-per-turn 2.5 → 2.0; the pins-checked row is DELETED (a cell is touched once by
shape, so the ratio is 1 by construction: a gate that cannot go red).
Theorems restated: `admit_pins`/`stale_refused` over touches; `stale_named` now names the stale cell
when it is the FIRST touch that fails (`t.touches = pre ++ x :: post`, every `pre` touch passes);
`admit_frame` premise "every touch at c is `keep`"; `rom_keep` (a live ROM cell is only kept);
`receive_ok` "the touches are the caller's pins, in order, with what it saw".
**Alternatives.** (a) Keep three lists and cache the pin lookups in a turn-local map for the legs:
moves the second lookup into a smaller map and keeps two shapes of "a cell this turn names". (b) One
pass that looks up all pins into a list, then legs over it: the same lookups, an intermediate list,
and the old precedence (every stale pin before any write fault).
**Critique.** Precedence changed: a turn whose first touch is a ROM write and whose second is stale is
refused `romWrite`, not `stale`; before, staleness was reported first. Both names are true faults,
but a client that retries only on `stale` now sees a different name for such a turn (no honest
receiver builds one: a receiver changes one cell). Blind writes are gone: a write must pin the cell's
current digest, so two writers of one hot cell conflict (they did already: every receiver pins what it
changes). CODEC's Turn codec (not yet landed) must follow the new shape. **Meta-critique.** I was asked
to make a number fall and found a shape change that makes it fall; the test is whether the shape is
right without the number: "a turn names each cell once, with what it saw and what it does" is the
smaller spec, deletes four refusals and one cross-check (`legRetired` is now unrepresentable), and
makes "writes only what it observed" structural instead of a property of today's receivers.
Status: open.

## KERNEL-12 · A turn's charge is its storage; one aggregate bound, `weightMax` (KERNEL-2, 2026-10-16)
**Decision.** `Turn.weight := logWeight + growth`: the bytes its log record holds (as before) PLUS the
most it can add to the World (journal entry, each born cell with its id, each write's ops, each
nullifier). The allowance is then a budget for the whole Store, log and World, which is what HOST must
size (`World.weight` ≤ genesis budget is the next theorem, answering HOST-14's memory question as
the `worldBytesMax` ask: the allowance IS that bound). `Bounds.weightMax := 4 * eventBytesMax` (256 KiB),
checked in `checkBounds` (`overBound weight`). `admit_weight`: an admitted turn has `charge = weight`,
`logWeight ≤ weight ≤ weightMax`. Plant: weightMax := 400 ⇒ kernel-sim seeds 1–3 red (`overBound`).
**Why an aggregate.** The per-field bounds alone allow a ~8.6 GB turn (64 born cells × 1024 slots ×
64 KiB, and as much again in writes): "a bound derived from Bounds" exists and is useless as a frame
budget. HOST needs one number per turn record and per batch.
**Alternatives.** (a) Derive the bound from the per-field ones (useless, above). (b) Shrink the per-field
bounds until their product is small (then a 1000-slot cell or a 64 KiB value is unwritable, which rows
need). (c) Charge only log bytes (K2), and bound the World separately: a second budget beside the
allowance.
**Critique.** 4 × event is a policy, not a derivation: an invoke whose method grows state well past
its arguments, or a turn observing 512 cells (33 KiB of touches), can hit it while honest. A born cell
is charged twice (its log record and its World copy); that is the real storage, but a package install
costs ~2× its bytes. CODEC owes `size (encode t) ≤ t.logWeight` (or `=`) for HOST's record budget to
be a theorem rather than an assumption. **Meta-critique.** Folding World growth into the charge is
attractive because it turns HOST-14's ask into a theorem I can prove from the allowance; check that
the allowance should be ONE budget at all (a member's storage vs the World's storage is the
refill/credit question, KERNEL-13).
Status: open.

## KERNEL-13 · Answers: PROTOCOL-4 `rederive`, HOST-8 `absent_final`, HOST's `fold ↔ foldlM`, `mayFollow` (KERNEL-2, 2026-10-16)
- **PROTOCOL-4.** `Receive.rederive X w t : Except (Refusal D) Unit`, with `rederive_ok : rederive X w t
  = .ok () ↔ ∃ c, X.decodeCall t.event = some c ∧ receive X w c = .ok t` (the statement PROTOCOL asked
  for). New refusals `undecodableEvent` and `eventMismatch` (PROTOCOL's name). `auditStep` IS
  `rederive` then `World.admit`, and `AuditFault` is deleted: an audit refuses in `submit`'s own
  `Verdict` (`refused r | rejected r`). That is one refusal shape for the writer and the follower,
  not two. Plant: rederive's comparison skipped ⇒ kernel-sim 64/64 red ("forgery at i: audit
  accepted"). The Sim now forges every seed's log at its last write (new values, re-priced, so `fold`
  accepts it) and requires `audit` to refuse `eventMismatch` at that index.
- **HOST-8.** `absent_final` (Kernel/Proofs/Fold): if `w.journal[k]? = none` and a later World of an
  admitted log has `k`, then some turn of that log has `txId = k` and `validUntil > w.height`. With
  `receive_ok` (a derived Turn's txId is `txIdOf c` and its window is the call's), an absent call whose
  window ended at or before `w.height` stays absent forever, unless a different call with a later window
  has the same `txIdOf`: a collision. HOST answers `absent` with the height; the client compares it
  with its own call's `validUntil`.
- **HOST (HOST-LOG item 6).** `fold_foldlM : World.fold E w l = .ok w' ↔ l.foldlM (World.admit E) w =
  .ok w'`; also `admit_window`.
- **HOST-11.** The gate is `Receive.mayFollow X w member g` (Kernel/Receive/Follow), a walk of ≤
  `grantDepthMax` lookups; there is no `grantOf` key-indexed lookup. A request names its follow grant
  `g`, which costs the requester one more field and saves the World an index from key to grant (an
  index is a second copy of state). Critique: a member must remember its grant's id; it is in the
  member's own log, which they follow. Meta-critique: I am refusing an index because indexes are a
  minidregg smell; the test is that every lookup on the gate is O(depth), and it is.
Status: open.

## KERNEL-14 · Answers: CODEC's counter widths, CLIENT-11's signature (KERNEL-2, 2026-10-16)
- **CODEC (counters).** `Bound.counter`: notBefore, validUntil and charge are < 2^64, and a born cell's
  kind < 2^32, checked in `checkBounds` (d310846). A World's height < 2^64 follows from `admit_window`.
  Alternative (CODEC's own preference): make those fields `UInt64`/`UInt32`, so the bound is in the
  type. I chose the check because the window and charge arithmetic is `Nat` in every proof
  (`omega`), and the premise is asserted where it enters (law 4). Critique: a `Nat` field says nothing
  about its width, so every encoder must cite the check; the type route makes that impossible to
  forget. Meta: I picked the route that does not churn my proofs. If CODEC hits a second field of
  this kind, switch to the types.
- **CLIENT-11 (which signature a Turn carries).** The Turn carries the call's bytes as its `event`,
  signature included. The kernel's shape is already agnostic: `key` and `signature` are opaque
  `ByteArray`s and `Ctx.verify` is the only check, run by the Host's `receive` and by every follower's
  `rederive`, so Lean decides on both sides. CLIENT-11's hybrid (Ed25519 ‖ ML-DSA-65, AND, one message,
  one seed) needs no kernel shape change except splitting `badSignature` into one name per half. That
  split lands with the verifier that produces it, because a constructor nothing produces is a no-op
  shape. The scheme itself is key material: **ROOT/Ember rules** (CHARTER pause list item 1). My
  recommendation is hybrid, with CLIENT's two plants (each half flipped alone must be refused by its
  name), because the log is permanent and re-verified by every new follower. Critique: 3.4 KB per
  call; a two-friends World pays now for a hypothetical threat. Meta: "permanent log" is an argument
  I find persuasive in general, and I have not priced how many follower re-verifies THE BAR implies.
Status: open (signature scheme: ROOT).

## KERNEL-15 · Storage is one World budget; no refill in v0, credit on retirement is the next step (KERNEL-2, 2026-10-16)
**Decision.** The allowance only falls. Since KERNEL-12 it budgets the whole Store (log + World),
so a World whose allowance is spent refuses every further turn `overAllowance`: its useful life is set
at genesis. Proposed next (not built): a retirement CREDITS the World bytes it frees (the retired
cell's `Cell.weight`, computed from the one lookup `touchCheck` already makes). That is exact and
keeps the invariant World + log ≤ budget, because the log bytes of the cell's birth are never
refunded. Operator refill (a founder-signed `fund n` kind) is NOT decided here. Who may mint storage
is an authority question, and per-member budgets are a fork (KERNEL-16).
**Alternatives.** (a) Refill by a founder call. (b) Per-member allowances, each member paying for its
own turns. (c) No budget at all, bounded only by the disk (minidregg).
**Critique.** A World that dies when its budget is spent is a footgun at genesis: pick the number too
small and only a re-genesis recovers (free here, not free in a deployment with friends' data). Credit
on retirement rewards churn-free designs and does nothing for a log that only grows. **Meta-critique.**
I am deferring the refill call because it needs an authority decision. Check: the credit half needs
none and is mechanical, so it is not deferred for difficulty; it waits for the World-weight theorem,
which is what makes "exact" a claim rather than a hope.
Status: open (refill authority: ROOT).

## KERNEL-16 · Open sponsoring is wrong as stated: the sponsor does NOT pay (KERNEL-2, 2026-10-16)
**Finding.** KERNEL-6's critique says "any member may sponsor … and the sponsor pays". There is one
World allowance, so no member pays anything personally. Any member can enrol members without limit,
and any member can spend the whole World budget. **Decision (recommended, ROOT to rule).** Enrolment
requires authority, using machinery the kernel already has: `enroll` is admitted only for a sponsor
holding a live grant chain to a founder that carries a new right `.enroll` (one `Right` constructor).
The founders, who are the genesis World, can then delegate and revoke the power to admit. Budget per
member (allowance per member cell, charged to the signer) is the stronger fix to the "spend it all"
half. It changes `checkCharge` to read the signer's member cell, one more touch per turn, and it is
the fork ROOT should pick between: (a) rights-gated enrolment only, (b) plus per-member budgets.
**Critique.** (a) does not stop a trusted member from exhausting storage; (b) costs a member-cell
write on every turn (a hot cell per member, so a member's concurrent calls conflict `stale`).
**Meta-critique.** Two friends and a Hermes resident do not need either. I may be designing for a
public World that THE BAR does not include.
Status: open (ROOT).

## KERNEL-17 · The journal is not pruned (KERNEL-2, 2026-10-16)
**Decision.** Every admitted txId stays in the journal (72 bytes, charged in `Turn.growth`).
**Why not prune by window.** After `height > validUntil`, a replay is refused anyway (`outsideWindow`),
so the journal entry is not needed for safety. But it IS the receipt: `lookup` (HOST-8) answers
`committed (height, digest)` from it, and `submit` answers a late retry `replayed h` with the
original height. A pruned entry turns a committed call into `absent` or `outsideWindow`, which is a
false answer to the client, worse than the bytes it saves. **Alternatives.** (a) Prune entries older
than `windowMax` heights and answer lookups from the log (O(log) per lookup, not O(1)). (b) Keep a
txId → height index outside the World (a second copy of state). **Critique.** The journal is O(turns)
forever: at THE BAR, 1000 turns cost 72 KB; at 10^6 turns, 72 MB resident. **Meta-critique.**
"Pruning loses receipts" is a correctness argument, and I may be leaning on it so I don't have to build
(a). Revisit when a World passes 10^6 turns. Nothing earlier forces it.
Status: open.

## KERNEL-18 · `worldBytesMax` is the genesis budget; the theorem is `fold_world_weight` (KERNEL-2, 2026-10-16)
**Decision.** `World.weight` (each cell entry with its id, journal entries, spent nullifiers, at the
same per-field costs as `Turn.weight`) is bounded by the budget. `admit_world_weight`: an admitted
turn adds at most `Turn.growth`. `fold_world_weight`: over any admitted log, `World.weight + Σ
logWeight + allowance` never exceeds its starting value. So a World folded from a genesis with budget
`A` never holds more than its genesis storage plus `A`, and a turn that would push it past that is
refused `overAllowance` by name. HOST-14's `worldBytesMax` is therefore HOST's choice of genesis
allowance, sized to its memory. No second constant is kept in Kernel.Bounds, because two bounds on
one quantity drift apart. Plant: dropping the write ops from `Turn.growth` breaks
`admit_world_weight` (omega fails).
**Critique.** `World.weight` is the kernel's measure, not CODEC's encoded size or the resident
memory of the TreeMaps (node overhead is several times 32 bytes per entry). HOST must scale its memory
budget by that factor, and CODEC owes `size (encode w) ≤ c · World.weight w`. The bound is by the
WHOLE budget, so a World that spends most of its budget on log bytes has a smaller World than the
bound says. That is an over-approximation, not an error. **Meta-critique.** This was attractive
because it falls out of KERNEL-12's charge change, so I may have shaped KERNEL-12 to get it. The
independent test: the allowance already claimed to be "the storage budget", and only now is that a
theorem about storage.
Status: open.

## ROOT rulings on KERNEL-14..17 (2026-10-16, recorded by KERNEL-2)
- KERNEL-14: v0 is Ed25519 ONLY. The kernel stays scheme-agnostic and the signature stays opaque
  bytes, so a hybrid is a later flag day (a re-genesis). CLIENT-11's hybrid ships only with its two
  flip-one-half plants. Reason: the hybrid needs a second verifier nobody has built, and minidregg's
  half-verified hybrid was worse than none (cv 01a14700). Ember is informed.
- KERNEL-15: credit-on-retire ACCEPTED as the next mechanical step. Any other refill is a grant, later.
- KERNEL-16: ONE mechanism (law 1). Enrolment is a RIGHT (`Right.enroll`) exercised through an
  attenuating grant chain rooted at the founders, the same shape as write/law authority, with the
  theorem `enroll_authorized` (twin of `write_authorized`). Per-member budgets fall out of
  attenuation: a grant can be attenuated to "may enrol ≤ n", so no second budget mechanism exists.
  Plant: the drained-World scenario; a member without the right, or past its count, is refused by name.
- KERNEL-17: the journal is the receipt. ACCEPTED.
