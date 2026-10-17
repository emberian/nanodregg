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
Status: credit BUILT as KERNEL-19 (exact; writes too). Refill: a grant, later (ROOT).

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
Status: RULED (one mechanism) and BUILT as KERNEL-20.

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

## KERNEL-19 · Credit on retirement, exact: storage is CONSERVED (KERNEL-3, 2026-10-16)
**Decision.** ROOT's KERNEL-15 ruling, built: `touchCheck` returns a `Post {cell, entry, freed}`
computed from its one lookup. `freed` is what the touch was charged for and does not hold: a
retired cell's whole `Cell.weight` (its id stays as a tombstone, so `idTaken` still holds, and the
id is not refunded), and a write's ops weight minus what the cell actually grew (≥ 0 by
`postWrite_weight`). `credit posts` is their sum; `checkCharge` requires `charge ≤ allowance +
credit` (a drained World can still retire a cell heavier than the retirement); `commit` sets
`allowance + credit − charge`. Theorems (Kernel/Proofs/Weight): `admit_world_weight` is now an
EQUALITY (`w'.weight + credit = w.weight + growth`); `admit_conserves`: `w'.weight + logWeight +
w'.allowance = w.weight + w.allowance`; `fold_conserves` over a log; `fold_world_weight` (the World
never exceeds its start's storage plus budget) as its corollary; `admit_retire`: a turn that only
keeps and retires leaves `allowance + charge = allowance before + Σ retired cells' weight`.
`admit_charge` restated with the credit; `fold_charge` keeps only "each charge is its weight".
Sim: grants, revokes (a non-issuer refused `notIssuer`), writes through a grant and through a
revoked one (`missingCell`); every revoke must hand back exactly the grant cell's weight. Plant:
credit dropped from `commit` ⇒ kernel-sim 63/64 red ("revoke: allowance … ≠ …") and
`admit_charge` / `admit_conserves` no longer build.
**Why the write refund too.** ROOT ruled the retire credit; the write slack is the same quantity
for the same reason (the charge is an upper bound on growth, settled against the one lookup), and
with it the budget identity is an equality instead of an inequality: no byte is lost or minted.
Without it a value overwritten in place cost its size again on every write, forever.
**Alternatives.** Retire-only credit (inequality kept, overwrites leak budget); recomputing the
freed weight with a second lookup (cells-touched would rise to 2.0 on retiring turns); charging
net instead of gross (the signer could no longer state its own price before the lookup).
**Critique.** The charge the signer signs is gross; what it actually costs depends on the World
(how big the cell it retires is), so a client cannot read its net cost off its `maxCharge`.
`Cell.weight` is O(cell) and now runs twice per written touch (bounded by `slotsPerCellMax`, still
O(touched)). Credit rewards deleting state, which is the intent, and invites retire-and-recreate
churn, which costs log bytes that are never refunded, so it cannot be farmed.
**Meta-critique.** I widened ROOT's ruling (writes as well as retires) because the equality is
prettier. Independent test: the inequality version leaves an unexplained gap between the World's
storage and its budget that grows with every overwrite; the equality has no such gap to explain.
Status: built (ROOT may narrow it to retires only by deleting one term).

## KERNEL-20 · Enrolment is a right; one grant kind; the World is a grant target (KERNEL-3, 2026-10-16)
**Decision.** ROOT's KERNEL-16 ruling, built. (a) `Right.enroll (count)`: may enrol ≤ count members,
directly or through grants carved from this one. (b) The World is a grant TARGET (`worldId X`, a
hashed id no cell is born at). A World grant carries `observe` (follow the log) and/or `enroll n`.
The separate follow-grant kind (kind 5), `Body.follow`, `followChain`, and `readGrantLike` are
DELETED. `mayFollow` is `walk` for `observe` on the World over the whole World. Law 1: one grant
shape, one chain walker. (c) `Body.enroll … (via : D)`: the sponsor's own World grant. `enroll`
walks the chain for `enroll` to a root, then SPENDS one from `via`. (d) The count lives in the grant
as an append-only LEDGER: slot `enrollBase + i` holds the count left after the i-th spend. The grant
stays `appendOnly` (making it `ram` to allow a decrement would weaken a kernel check), so the count
can only fall, and the kernel's discipline enforces that, not only the receivers. Each spend takes at
least one, and a count is at most `enrollMax` (256), so the ledger fits its key range. (e) A grant
carrying `enroll n` carves n from its parent: the parent's ledger write is the grant turn's one
effect, and it is refused `grantWidens` past what the parent has left. (f) `unrooted`: no call issues a
parentless grant on the World or one carrying `enroll`. The only roots are genesis's: each founder
gets one World grant (observe, enroll 256, id `founderGrantId`). Key layout: rights 16/17, the enroll
ledger 1024…1280, invoke m at 4096 + m, all disjoint by construction.
Theorems (Kernel/Proofs/Authority): `enroll_authorized` (a derived enrolment has a `Chain` for
`enroll` on the World from `via` to the signer, `via` had `left > 0`, and the Turn's effect appends
`left − 1` to its ledger); `grant_rooted` (a derived World or enroll grant has a parent);
`grant_carves` (its count is a successful `spendEnroll` of the parent's); `spendEnroll_ok`.
New refusals `unrooted`, `enrollSpent` (name_injective holds by `cases`).
Sim: the founders hold genesis grants; sponsors enrol through their own grant (`enrollSpent` once
their count is drained, `grantRight` through an observe-only grant, `noGrant` through another
member's); members delegate World grants with counts 0..2 or observe-only (`grantWidens` past the
parent's count; a parentless World grant `unrooted`). The Sim keeps its OWN model of every count
(`Holding`), not the kernel's ledger. kernel-sim now FAILS when a run of ≥ 16 seeds never meets one of
the 12 planted refusal names. Plants: the count check off ⇒ 45/64 seeds red ("expected enrollSpent,
got admitted") and `enrollSpent` never met; the walk off ⇒ 63/64 red ("expected noGrant, got
admitted"); the unrooted check off ⇒ 59/64 red.
**Alternatives.** A separate enrol-grant kind beside follow grants (a third grant shape); `ram`
grants with a decremented counter (weakens the append-only check); counting at every chain link on
each enrolment (up to 8 writes per turn, and `sealTurn`'s one effect becomes a list); a per-member
budget cell (KERNEL-16's option (b): a second mechanism).
**Critique.** A founder can enrol at most 256 members in total, including through delegation, so a
World's membership is ≤ 256 × founders until a refill grant exists. Revoking a carved grant does not
give its unspent count back to the parent (the credit is storage only). Reading the count left is
O(ledger) per enrolment (≤ 257 slots). A grant carrying several `enroll` rights stores their sum. The
claim that "every World chain ends at a founder" rests on two receiver theorems and on genesis.
The World-level invariant ("every live World grant has a parent or is a genesis root") is
proved in KERNEL-21. Protocol: `follow MEMBER` is now `grant World MEMBER
[observe] via me.grant`, and `enroll TOKEN` spends `me.grant`; PROTOCOL still has to parse an
`enroll:N` right.
**Meta-critique.** Deleting the follow kind was the move I wanted (law 1). Check that it is not
ornament: before it, Protocol's enrol had no grant id to name, and the fix would have been a second
id in `Self`. With it, a member's one World grant is its whole membership credential. The 256 is an
estimate dressed as a bound; it is a constant, and a re-genesis changes it.
Status: built.

## KERNEL-21 · Every World grant is rooted at genesis, as a fold invariant (KERNEL-3, 2026-10-16)
**Decision.** ROOT asked for the open half of KERNEL-20 to be proved. Kernel/Proofs/Rooted:
`WorldRooted X R w` says every live grant cell is append-only and names a target, and a grant whose
target is the World has a parent or is in `R`. The kernel half is `admit_rooted`. Whatever turn is
admitted, given rooted births, the World stays rooted, because `postWrite_keeps` says an
append-only cell never loses or changes a slot. So no receiver, honest or buggy, can strip a parent
or retarget a grant. The receive half is `dispatch_born`: of every receiver, only `grant` bears a
grant cell, and on the World only with a parent (`grant_rooted`). Then `step_rooted`,
`submit_rooted`, `audit_rooted` (the follower's World), and `genesis_rooted` with
`R = GenesisRoot` (the founders' grant ids). `chain_rooted`: through a rooted World, a chain for a
World right ends at a live root grant in `R` whose issuer is the chain's principal. With their
premises (digest bytes injective, decoder canonical) discharged by CODEC's
`Codec.Proofs.Deployed`, Kernel/Proofs/RootedDeployed gives `deployed_audit_rooted` and
`deployed_enroll_founder`: on an audited World, every enrolment acts for a founder, through that
founder's own genesis grant. Plant: the `unrooted` check off ⇒ `grant_rooted` (and everything
above it) no longer builds; kernel-sim 59/64 red (KERNEL-20).
**Alternatives.** The Sim plant ROOT offered as the fallback (an audit refusing a forged log); it
would test one forgery where the theorem covers every log.
**Critique.** `WorldRooted` talks about raw slot bytes (`get grantTarget = some (bytes worldId)`).
Its link to what `walk` reads goes through the two digest premises, so a generic `Ctx` with a
non-canonical decoder gets no `chain_rooted`. The invariant says nothing about object grants (a
root object grant is legitimate: its issuer must be the owner, checked by `ownerAuthority`).
`audit_rooted` covers the audited log; a Host World is the same World by `submit_rooted`.
**Meta-critique.** It was cheaper than I expected because the append-only discipline carried the
write half. That is evidence the KERNEL-20 choice (keep grants append-only, ledger the count) was
right, not only prettier.
Status: built.

## KERNEL-22 · Tooling is not deployed: SIZE.md's deployed row excludes it, and C9 keeps it out of deployed imports (KERNEL-4, 2026-10-16)
**Decision.** ROOT's item (GATES retired, so a CROSS-LAYER commit). `tree.Module.is_tooling`: a
module of a tooling lib (`Census`, `Emit`) or one with a tooling path component below its lib
(`Sim`, `Rows`, `Journey`). "Lean lines (deployed)" counts definitions that are neither proofs nor
tooling; a new informational row "Lean lines (tooling: Sim, Rows, Journey, Census, Emit)" counts
the tooling. Closure C9: a deployed def-module importing a tooling module is red, so naming a
directory `Sim` cannot launder deployed code out of the count (plant: `Kernel.World` importing
`Kernel.Sim.Gen` ⇒ `C9 Kernel.World (deployed) imports tooling module Kernel.Sim.Gen`).
**Why wider than asked.** The brief named `Sim`, Host/Sim and Protocol/Rows. `Lang/Journey` is the
same thing (the `lang-journey` exe's scenario); `Census` (the axiom census command) and `Emit` (the
Rust table generator) are build tooling no deployment runs. A row called "deployed" that counts any
of them is false.
**Alternatives.** Deployed = the import closure of the deployed exe (exact, and the right end state,
but there is no `nanodregg-host` exe yet, so the closure is empty today); a per-lib exclusion list
(misses Kernel/Sim inside the Kernel lib); a marker comment per file (a convention nothing checks).
**Critique.** Path-component classification is a naming convention; C9 makes it sound in one
direction only (deployed never imports tooling), not the other (a tooling module that the deployed
exe should have been built from). When the Host exe exists, deployed should become its closure and
this rule its cross-check. `Emit` produces deployed Rust; its Lean is still tooling, and the emitted
Rust has its own row.
**Meta-critique.** I own the biggest tooling module (Kernel/Sim/Gen, 561 lines) and the rule lowers
my layer's deployed count; the test is that every module it moves is reached only from a test or
build exe, which C9 now enforces.
Status: built.

## KERNEL-23 · An authenticated cell root: the World's cell map IS a canonical binary Merkle trie, and the chain commits its root (KERNEL-4, 2026-10-16; DESIGN, not yet built)
**Why.** Ember ruled phones in scope, thin in SPACE (ROOT, 10-16). A phone that holds no World
must check one cell against a head it trusts. That needs a root over the cells, kept up to date
in O(touched) per admitted turn and bound into the chain. The same structure later serves
per-cell hiding (a leaf commits a commitment instead of a digest) and a cheap `read` for everyone
(a cell plus its path, not the World).
**Decision.**
(a) *One structure.* `World.cells` stops being a `Std.TreeMap` and becomes `Trie D`: a persistent,
path-compressed BINARY trie over the bits of `E.bytes id`. Its shape is a function of its key set
alone: a leaf sits at the shortest prefix that tells it apart, and an internal node branches at
the first bit where its subtree's keys differ. So the trie is history-independent, and two
Worlds with the same contents have the same root, whatever order the turns ran in. Every node
caches its hash. Lookup, insert and tombstoning walk one path. The trie is the cell map, not an
index beside one, because two maps over one key set are two shapes that would one day disagree
(law 1). The kernel's 30 `.cells` uses go through `live` / `insertAll` / `contains`, and their
TreeMap lemmas are restated for the trie: get_insert_self, get_insert_ne, contains_iff, and
toList sorted and duplicate-free. CODEC's 3 uses go through the World codec.
(b) *What a leaf commits.* `leaf = H(domLeaf, bytes id ‖ bytes (entryDigest e))`, where
`entryDigest (.live c) = pinOf E (some c)` (the existing pin digest of the cell bytes) and
`entryDigest .tomb = H(domTomb, ∅)`. Internal: `node = H(domNode, u16 bit ‖ bytes l ‖ bytes r)`.
The branching bit is committed, so an EXCLUSION proof is sound as well: following the id's bits
ends at a leaf with a different key, or at an empty side. Owner and law are not committed
separately: they are slots of the cell, so the cell digest already commits them, and a second
encoding of them would be a twin. The root of the empty trie is `H(domEmpty, ∅)`.
(c) *Proofs.* `Proof D := {leaf : Option (D × D), path : List (Nat × D)}` (bit, sibling), from
the leaf up. `verifyInclusion E root id d p : Bool` and `verifyExclusion E root id p : Bool` are
both total and bounded by the key's bit width. `World.prove w id : Proof D` returns a path of
length ≤ depth.
(d) *Chain.* `chainNext E prev t root' := H(domChain, bytes prev ‖ bytes (turnDigest t) ‖ bytes root')`,
where root' is the root after the turn. The root goes INTO the chain, not beside it: a phone then
trusts ONE digest (a chain head), receives (prev, turnDigest, root'), checks the hash, and from
then on verifies cells against root'. With the root beside the chain, a countersigner would have
to sign two things, and a head and a root could be paired that were never one state.
(e) *Turn unchanged.* The root is computed by `commit`, never carried in the Turn. A receiver
cannot know the post-root before admission (it does not hold the World), and a Turn field that
admit fills in would make the Turn's digest depend on admission. So the Turn codec does NOT
change. I am departing from ROOT's "the Turn codec" here: the root lives in the World codec and,
for a phone, in the head record PROTOCOL serves, (height, prev, turnDigest, root).
(f) *Theorems.*
- `root_congr`: `World.Equiv` worlds have equal roots.
- `admit_root`: `w'.root = rootOf w'.cells`, where `rootOf` is a specification by recursion over
  the sorted key list, and the incremental trie computes exactly it.
- `prove_verifies`: `verifyInclusion E w.root id (entryDigest e) (w.prove id)` when
  `w.cells.get? id = some e`, and `verifyExclusion …` when it is absent.
- THE soundness statement, `inclusion_sound`: `verifyInclusion E w.root id d p = true →
  w.cells.get? id = some e ∧ entryDigest e = d ∨ Collision E.hash`, given `E.bytes` injective
  (the premise CODEC already discharges for `Digest`). `exclusion_sound` is the twin with
  `get? id = none`.
- `chain_binds_root`: equal chain heads after equal-length logs give equal roots, or a collision.
  Collision is the existing `Collision` (two inputs, one digest, under any domain), so "a forged
  proof fails unless a hash collision" is a disjunction with an exhibited witness, not prose.
(g) *Sim and plants.* After every admitted turn the Sim proves and verifies every touched cell
and one untouched cell against the Host's root, and verifies them again against the follower's
root. Then it forges: it flips one sibling, swaps the leaf digest, and claims a tombstone live;
each must fail by name (`verifyInclusion = false`). Plants: drop the bit from the node hash ⇒
`exclusion_sound` no longer builds; leave a touched path unrehashed ⇒ the Sim's
follower/Host root check goes red; keep the root out of `chainNext` ⇒ `chain_binds_root` no
longer builds.
(h) *WASTE.* `cells-touched-per-turn` stays 1.0: the trie walk IS the lookup. A new row,
`admit hashes-per-touched-cell`, counts node rehashes ÷ cells changed. It is pinned at the
measured value with a ceiling of ⌈log₂(cells)⌉ + 2. Estimate, not a measurement: the Sim's
Worlds hold ~50–150 cells, so ~8 hashes per changed cell; at the bar's 1000 records, ~11. A batch
that touches k cells shares the top of their paths, so the honest count is |⋃ paths| and not
k·depth. I will build the batched rehash (rehash the union once) only if the measured ratio
shows the sequential version paying for the shared top twice.
**Alternatives.**
- Fixed-depth sparse Merkle tree over all 256 bits: 256 hashes per touch and 8 KiB proofs. Rejected.
- Radix-16 (Ethereum MPT / Jellyfish): fewer levels, but 15 siblings per level, so proofs ~7×
  larger. That is the wrong trade for a phone, whose scarce resource is bytes, not hashes.
- A TreeMap plus a separate Merkle index kept equal by an invariant: two structures, law 1.
- A root carried beside the chain: (d).
- A root field in the Turn: (e).
- Committing digest + owner + law in the leaf: (b).
- A Merkle mountain range over the log instead: it authenticates history, not current state, so
  a phone would replay to read one cell.
**Critique.**
- Every changed cell now costs ~log₂ n cSHAKE256 calls on admit. At 1000 records that is ~11 per
  cell, against today's single pin hash. The 5 s write bar has room, but this is a real constant,
  and the follower pays it too (it recomputes the root; it must, or it trusts the writer).
- The trie's lemmas are ours, not Std's: an extra proof surface of maybe 400–600 lines, plus a
  rewrite of Frame/Equiv/Weight/Rooted proofs from TreeMap lemmas to trie lemmas.
- The proofs are on keys hashed through `E.bytes`. The toy's 8-byte digests give 64-bit keys, so
  the Sim's trie is shallow and adversarially weak, which is fine because the toy is not where
  soundness is claimed.
- The spent set and the journal are NOT authenticated. A phone cannot verify "this nullifier is
  unspent" or "this txId landed", and LEDGER's pay on a phone will need the first.
  Recommendation: spent nullifiers become leaves of the SAME trie under a domain-separated key
  (`H(domNullifier, n)`), so one authenticated map holds both. That moves `spent` into `cells`,
  which is LEDGER's call when it is spawned, and is a ruling for ROOT now: is v0 cells only, or
  cells + nullifiers?
- History-independence holds only if the canonical-shape invariant is proved (`Trie.WF`), not
  assumed. A trie built by a buggy insert that is still a valid map would give a different root
  for the same contents, and the follower would disagree with the Host by root only.
  `admit_root` against the specification `rootOf` is what closes that.
**Meta-critique.**
- Binary path-compressed Merkle tries are the textbook answer (Diem's JMF, Aptos, Celestia's
  NMT), and I chose the textbook. The independent test is the phone's budget: proof bytes =
  32·log₂ n, the minimum for any hash-based tree with fan-out 2, and fan-out 2 minimises proof
  size for a fixed hash.
- Making the trie the map rather than an index is the law-1 move I like, and it is also the more
  expensive one: it rewrites proofs that are green today. The cost estimate ("a rewrite of four
  proof files") is not a reason to keep two maps (CLAUDE.md: an estimate is not a constraint).
- I am departing from ROOT on the Turn codec on the grounds that the root is post-state. Check:
  if someone wanted a Turn to state the root it expects (an optimistic check), that would be a
  pin on the whole World, and every concurrent turn would be stale. So no.
Status: proposed (ROOT to rule on (e) and the nullifier question before the flag day).
**Flag day when built.**
- `World` gains the trie in place of the TreeMap, and its codec changes (CODEC-14 checkpoint
  base). A base written before refuses to load, through the base's schema epoch.
- Every chain head changes (`chainNext` takes the root). A log is still a list of the same Turns,
  so it refolds, but a stored base's chain no longer matches, so Stores re-genesis.
- The Turn codec is unchanged. PROTOCOL gains a head record (height, prev, turnDigest, root) and
  the `read` reply gains a `Proof`.

LEDGER-1..5 (written here while LEDGER built under KERNEL's prefix) moved to decisions/ledger.md on 2026-10-17.

## KERNEL-24 · A call names its World: `Unsigned.world` = the World's genesis ORIGIN, refused `wrongWorld` before anything else; genesis commits to everything it was made from (KERNEL-4, 2026-10-17; DESIGN, ROOT's D3, not yet built)
**Defect (measured by OPS on 87c721e, with the real `host` exe).** The SAME signed `create` frame was
admitted by two Stores both named "w": nothing in `Unsigned` binds a call to a World. And CLIENT-2's
round trip found that `host genesis` prints the same genesis `chain` for different founder keys under one
name, because the genesis chain commits to the name alone.
**Decision.**
(a) `World.genesis X.env (name) (nonce : ByteArray) (allowance) (founders)` takes the nonce as a SEPARATE
argument, not folded into the name. HOST draws it: 32 OS-random bytes. `origin := H(domOrigin, blob name
‖ blob nonce ‖ u64 allowance ‖ Σ (blob key ‖ bytes nextDigest))` over the founders in order, and the
genesis chain is `H(domGenesis, bytes origin)`. So the chain commits to the name, the nonce, the
founders' keys and next-key digests, and the allowance.
(b) `World.origin : D`, set by genesis and never written again. Theorems `admit_origin` (`w'.origin =
w.origin`) and `fold_origin`.
(c) Founder ids and founder-grant ids are keyed by the ORIGIN, not the name (`founderId X origin i`), so
two Stores with the same name share no member id.
(d) `Unsigned.world : D` is signed, and the call codec changes (CODEC). In `receive`, the FIRST check,
before the key, the signature or any pinned read: `req (u.world = w.origin) .wrongWorld`.
`Receive.Refusal.wrongWorld` gets a name arm, and `name_injective` is kept. A cross-World call is never
`badSignature` or `unknownKey`, whatever else is wrong with it. `Receive.submit` checks the journal
first, and a cross-World txId is not in this journal, so `wrongWorld` is what it answers.
(e) ONE field and ONE refusal. TRANSPORT's read envelope compares `e.world = w.origin` against the same
accessor. HOST adds no check of its own: an old base, which has no origin, refuses by the World codec's
tag change (HOST-20's `shapeMismatch` stamp, derived from the codec shapes).
**Theorems.**
- `receive_wrongWorld`: `c.unsigned.world ≠ w.origin → receive X w c = .error (.wrongWorld)`.
- `admitted_elsewhere_refused`: a call `submit` admits on W₁ is refused `wrongWorld` by every W₂ with
  `W₂.origin ≠ W₁.origin`.
- `genesis_inj`: two geneses with equal origins have equal (name, nonce, allowance, founders), or a
  collision. Therefore equal chains imply equal inputs, or a collision.
**Sim plant.** Replay a seed's whole log into a second genesis with another nonce: every call must be
refused `wrongWorld` at turn 1. Also: genesis with the founders' keys swapped must give a different
chain. Both are in the generator and both are named in `planted`.
**Flag day.** The call codec changes, so every signed call re-signs. Origins and founder ids change.
Every Store re-genesises. The Turn codec is unchanged, but a Turn's event (the call bytes) carries the
world field.
**Alternatives.** The nonce inside the name: it conflates the label people read with the entropy, and a
Store relabelled by its operator would change identity. Distinct names giving disjoint member ids: the
names are chosen by people and collide; OPS reproduced exactly that. A Host-side check: a second check of
one fact, law 1.
**Critique.** The origin is only as unique as HOST's randomness. Two Stores with the SAME nonce, name and
founders are the same World, by design, and admit each other's calls: a restore from backup is that
case, and is intended. A phone needs the origin out of band, from the invitation, to know which World it
is joining.
**Meta-critique.** "Bind the call to its domain" is the textbook anti-replay answer, and here it is also
the measured defect. The fork worth checking: should the origin be the genesis CHAIN? It should not.
The chain advances, and a call must be bound to the World, not to a height. That is the window's job.
Status: BUILT (KERNEL-5, 10-17). As built: the origin is H(domOrigin, CODEC raw bytes of (name, nonce,
allowance u64, [(key, bytes next)])) with every length ≤ Bounds.eventBytesMax; `World.genesisChain`
(HOST-6's ask) is the chain genesis starts at; founder ids are domain v2, keyed by bytes origin.
Theorems (Kernel/Proofs/Origin): admit_origin, fold_origin, genesis_origin, genesis_chain, genesis_inj
(equal origins ⇒ equal inputs ∨ HashColl domOrigin, given GenesisFits and an injective digest
encoding), genesis_chain_inj, admitted_elsewhere_refused (refused `wrongWorld`, or `replayed` if the
other journal holds the txId: never admitted); Proofs/Receive: receive_wrongWorld, receive_ok_with;
receive_congr now also needs equal origins. `host genesis STORE NAME [--nonce HEX32] …` (HOST-5's
spec): OS draw (refused `entropy`), `--nonce` for a member's own Store, `origin`/`nonce` lines,
NAME past the bound refused `usage name`. Plants: World check skipped ⇒ the replay-elsewhere arm
reads `unknownKey`, red; origin ignoring founders ⇒ swapped founders give the same chain, red.

## KERNEL-25 · `invoke` is authorized like write: the owner, or a chain for `invoke m` rooted at the owner (KERNEL-4, 2026-10-17; ROOT's ruling on HOSTING-4, not yet built)
**Defect (HOSTING, measured in hosting-sim).** `Derive.invoke` computes the principal with
`principalOf` and never compares it to the owner. With `via = none`, any member could invoke any method
of any programmed object, and every package had to carry its own owner law. That contradicts
`write_authorized`.
**Decision.** In `invoke`, `principalOf X look u obj (.invoke method) via` becomes `ownerAuthority X look
u obj cell (.invoke method) via`. That is ONE line. A stranger with no grant is refused `noGrant obj`,
the same constructor as write's identical case. I am departing from ROOT's suggested name
`unauthorized`: one condition gets one refusal name, law 7, and the condition is exactly the one
`noGrant` names for write and law.
Theorem `invoke_authorized`, the twin of `write_authorized`: a derived invoke has principal = owner, and
either via = none and signer = owner, or a `Chain` for `invoke m` from `via` to the signer rooted at the
owner. Laws then only REFINE: they run after this check.
Sim plant: a non-owner without a grant invokes a method and is refused `noGrant` (already a planted
name; the plant goes in the invoke arm). Rows that relied on open invoke (pay/well/bounty, where
non-owners invoke) must grant explicitly. That is LANG and PROTOCOL's flag day.
**Critique.** Owner-gated invoke makes shared objects (a well anyone may draw from) need a broad grant per
member, where before they needed nothing. A "public method" would be a grant to the World, which needs
a grantee-is-anyone form we do not have. Until a row needs that, the explicit grant is the honest
shape.
**Meta-critique.** I left invoke open in KERNEL-6 because LANG's laws could check the principal. That is
"a check exists somewhere" reasoning, and the default every package author inherits was OPEN. The kernel
should decide authority once, and laws should narrow it.
Status: BUILT (KERNEL-5): invoke via ownerAuthority, theorem invoke_authorized; Sim arms invoke-owner:ok, invoke-no-grant:noGrant; plant principalOf in invoke ⇒ 56/64 seeds red.

## KERNEL-26 · Public objects: a grant whose grantee is the World means "any enrolled member" (KERNEL-4, 2026-10-17; ROOT ruled, not yet built)
**Decision.** Under KERNEL-25 a non-owner invokes only through a grant chain. A public object (any hunter
may claim a bounty) is the owner issuing a grant for `invoke m` whose GRANTEE is `worldId X`. `walk`
accepts such a link for any signer whose member cell is live. Strangers are already refused
`unknownKey` before that. One mechanism: the World is already a grant TARGET (KERNEL-20) and now also a
grantee meaning. LANG-3's `Authority.anyone` is this grant. Theorem: `invoke_authorized` covers it
(the chain's root issuer is still the owner).
**Alternatives.** Open invoke (KERNEL-25 ruled it out); a per-package "public" flag (a second authority
mechanism); one grant per member (does not scale, and misses members enrolled later).
**Critique.** A World grant is still revocable and attenuable like any other: revoking it closes the
object to everyone at once, and a carved child grant may narrow it (fewer methods) but never widen it.
"Any enrolled member" includes members enrolled AFTER the grant, which is the intent for a public object
and a surprise for anyone who reads it as a snapshot.
**Meta-critique.** Reusing `worldId` as a grantee is the economical move; the test is that `walk`'s
grantee check gains exactly one disjunct and no other code learns about it.
Status: BUILT (KERNEL-5): granteeHolds in walk (one disjunct), checkGrantee in grant, theorem granteeHolds_ok; Sim arms invoke-public:ok, invoke-public-method-1:grantRight; plant World disjunct off ⇒ red. A public grant is USED, never re-delegated: `walk` honours a World grantee only at the FIRST link (`pub`), and `checkParent` keeps requiring the parent grantee = the signer exactly, so the two agree on one shape (ROOT/review 10-17 named the disagreement; I chose the narrow side because the wide one let any member carve a public enrol pool into a private grant). Sim arm carve-public:noGrant. A public ENROL pool (a World-grantee grant carrying enroll n) is possible and is stated on enroll_authorized. Theorems added after review: invoke_stranger_noGrant (the refusal BY NAME), ownerAuthority_program_free (the laws only refine: the gate never reads the program).

## ROOT rulings on KERNEL-24..26 and LANG-19 (2026-10-17, recorded by KERNEL-4)
- KERNEL-25: `noGrant` stands for a stranger's invoke (one condition, one name).
- KERNEL-26: ACCEPTED as written.
- LANG-19 (cv 01a14805-3d5a): ACCEPTED. `law` also judges the NEW laws over old = new with occasion
  `relaw laws'`: a law that would deny its own current state cannot be installed; the install is
  governed by what it installs.
- Order for KERNEL-5 (hbox): LEDGER D2 → LANG-3 Occasion → KERNEL-25 → KERNEL-24 → the World port.

## KERNEL-27 · LANG-19 as built: `law` judges the incoming laws over the state as `.adopt`, a fifth Occasion. ROOT's LANG-19 wording was overruled by KERNEL-5's finding, and `.adopt` was chosen over the `.birth` conflation (KERNEL-5, 2026-10-17; ROOT ruled `.adopt` the same day)
**Finding.** ROOT ruled that LANG-19 judges `laws'` with occasion `relaw laws'`. That wording makes every law that refuses `relaw` refuse its own adoption, so LANG's `Frozen` can never be installed. Measured: lang-journey L10d went red with "frozen: laws are frozen".
**First build (be98647): the incoming laws judged the state as `.birth`.** That build was superseded within the day. ROOT's critique, which my own critique had already stated: a law then cannot tell adoption from birth. Quorum's birth arm, which demands an empty state, would refuse adopting quorum onto a populated object. Nobody could write "no adoption onto a non-empty state" or "adopt freely, never relaw" as distinct rules. Calling `adopt` "the fix if one ever needs it" was a deferral of a defect already found.
**Decision.** `Occasion` gains `adopt (laws : List D)`, the whole incoming list, encoded in Lang exactly as relaw is (LANG-4: quorum's adopt arm is its relaw arm, and it checks that the state's proposal names exactly the incoming ids). In `law`, the laws in force judge the change as `relaw laws'`: the authority to change laws, unchanged. Each incoming law then judges the resulting (unchanged) state as `.adopt laws'`. Frozen accepts adopt and refuses relaw. Quorum's adopt arm is its relaw arm (k of the members approve), not its birth arm. LANG-4 owns the Std arms and the lang-journey rows, and L10d goes green BY NAME. In kernel-sim's stub, `freeze` admits adopt and deny-all refuses it (arm `law-self:lawDenied`). PROTOCOL's `sealedLaw` admits adopt and birth.
**Flag day.** LANG's occasion sum gains an arm, so every law package's bytes change. Every package re-ids, and the World re-genesises. This sits on top of LANG-19's behaviour change.
**Alternatives.** `.birth` (the conflation above). `relaw laws'` (ROOT's wording: self-defeating). `adopt` with no payload: quorum's adopt arm could not check its pre-approved law set (LANG-4).
**Critique.** Every law author now writes one more arm, and a sum arm a law forgets is a type error (good: exhaustive), not a silent admit. Adoption and birth are now separate. A law that wants them equal says so by writing the same arm twice.
**Meta-critique.** My first build picked the existing constructor partly because it touched no other layer: a cost estimate deciding a design, which this file forbids. ROOT caught it.
Status: built with the LANG half (LANG-4).
Amended (LANG-4, 2026-10-17, agreed by KERNEL-5): second judge: ADDED laws only (LANG-4, the forged-approvals adoption). `law` runs the incoming laws' `adopt` on `laws'.filter (· ∉ laws)`. A kept law already judged the change as `relaw laws'`, and re-judging it on `adopt` refused every relaw that keeps a quorum, once quorum's adopt arm became its birth clause.

## KERNEL-28 · KERNEL's answer to LEDGER-5 (with LANG-4's LANG-23 asks): (a)(b)(c) ACCEPTED, (d) AMENDED to keyed account ids (KERNEL-5, 2026-10-17)
**(a) Effects are `Body`.** Accepted, as LANG-4 restated it.
`Program.run : Pinned D → (pkg : D) → Slots → (method : Nat) → ByteArray → Req D → (budget : Nat) →
Except (Refusal D) (Slots × List (Body D))`.
`Refusal.notCallable kind` stays as the kernel's own assertion, placed where the program's calls enter
(law 4). `Program` is abstract to the kernel. LANG's `callsOf_callable` makes it unreachable for
`Lang.program`, and the plant is a stub program that returns a `create`. The allowed kinds are
`invoke`, `transfer`, `account`, `credit` and `grant`.
**(b) Derived for the calling object.** Accepted. Every receiver takes the ACTOR, the id whose
authority it spends, instead of reading `c.unsigned.member`. The top-level call passes the signer.
An effect passes the calling object. `Req.agent` stays the signer, and `principal` is the object.
Signature and key checks run once, for the top-level call only. Consequence, stated: an object is
not a member. So the public-grant disjunct (KERNEL-26, first link, member cell live) never holds for
an object. An object acts only through grants that name it, or through what it owns.
**(c) One seal per call.** Accepted. `Draft D := {creates, effects, nullifiers}`; `receive` seals
once. A tree that writes one cell twice is `duplicateEffect`, a repeated nullifier is
`duplicateNullifier`, and re-entry into an object already visited is refused (`visit_distinct` is
KERNEL's, since the visitor lives in Derive). Bounds in Kernel.Bounds, for LANG to read:
`callsMax 8`, `callDepthMax 4`, and `treeTicksMax`. The tree's tick budget is ONE budget, the
signed `budget` of the top-level invoke, and it is capped at `treeTicksMax`. That cap is sized from
LANG's runMeasured on the BAR rows; a measured number, never a guess.
**(d) AMENDED: an account's id is keyed, `accountId X owner asset = H(domAccount, owner ‖ asset)`.**
Anyone may open the account of any (owner, asset). A second open is `idTaken`, so there is one
account per pair and no littering. An object computes its own account id with no cell read. That
closes LANG-4's gap (ii): "the escrow's account is the escrow's" becomes a theorem, not a convention.
To carry it, `Turn.creates` holds EXPLICIT ids, `List (D × Cell)`. Receivers compute them: a fresh
birth is still `bornId txId i`, and an account is `accountId`. `World.admit` checks `idTaken` per
id, as it does today. That is ONE birth shape in the Turn (law 1), not a second rule beside
`bornId`. Audit re-derives, so a writer cannot choose ids the receiver did not.
**LANG-4's gap (i), the deposit.** For v0, the depositor grants the escrow object `mutate` on the
depositor's account. The escrow's `deposit` effect is then `transfer src=depositorAcct via grant`,
with principal = the escrow, rooted at the depositor. An AMOUNT-bounded right is the correct
attenuation, and it is opened as cv task KERNEL-28-amount-right. The whole-balance grant is labeled
as the v0 shape in the escrow package.
**Order.** KERNEL-24 first, by me, now. Then D5 (this decision plus LEDGER-5) is built by LEDGER-2
as `kernel:` in its own worktree, rebased on KERNEL-24. I review every theorem statement in it.
The World port is mine and runs in parallel with D5; the two converge forward. The flag day comes
with D5: Turn codec (explicit create ids), call codec unchanged beyond KERNEL-24, `Program.run`
shape (LANG's `lang!` flag day after it), re-genesis.
**Critique.** Keyed accounts forbid two accounts per (owner, asset), which a budgeting owner might
want. Today that is a sub-ledger inside one object, which is not worse. Actor-as-parameter widens
every receiver signature by one argument. Explicit create ids put 32 bytes per birth into every
Turn, measured in the WASTE line of the D5 commit.
**Meta-critique.** I took the amendment that makes LANG-4's binding a theorem instead of the
convention LEDGER proposed, because convention-bound authority is exactly how D6's law-removal hole
happened. The order puts my own KERNEL-24 first. Its justification is that three layers (PROTOCOL's
wrongWorld row, TRANSPORT's envelope, CODEC's call codec) already wait on it, and it touches
receive's first line, which D5 also rewrites.

## KERNEL-30 · KERNEL-23 part 2 as built: the World IS one trie of cells and nullifiers; the root after each turn is in the chain (KERNEL-6, 2026-10-17)
**Decision.** `World := {trie : Cells D, journal, height, chain, allowance, origin}`, where
`Cells D = Trie.T (Slot D) Leaf D`, `Slot = cell id | nullifier n`, `Leaf = entry Entry | spent`. The
fields `cells` and `spent` are DELETED (law 1: one authenticated map, not a map plus an index). The
trie parameters are `trieSpec E`: bit 0 is the slot kind, bit i+1 is bit i of `E.bytes id`
(MSB-first, `false` past the end), depth `Bounds.trieDepth = 257`, node hash `E.hash domTrie`, and the
leaf value digest is `E.hash domLeaf (kind byte ‖ cellBytes)`. Every reader takes E:
`w.entry/live/taken/isSpent E`, `pinned E w pins`. `chainNext E prev t root'` commits the root after
the turn, `chainOf` folds `(turn, root)` pairs, and `genesisChain` is unchanged (the empty trie's
root is a constant). `World.Equiv`'s trie component is `=`. The journal stays a TreeMap and is not
authenticated (KERNEL-23's critique still stands).
Theorems (Kernel/Proofs/{TrieMap,Cells,Fold,Equiv,Frame}): `World.Canon` holds at genesis
(`genesis_canon`, `receive_genesis_canon`), and admit and fold keep it (`admit_canon`, `fold_canon`).
`eq_of_get_eq`/`trie_ext` give history independence over CONTENTS, via `build_perm` on separated
keys; `slots_separate` discharges separation for fixed-size injective digests, n ≤ 32.
`slot_inclusion_sound`, `slot_exclusion_sound`, `live_inclusion_sound` and `unspent_sound` give
`… ∨ Collision E.hash`. `prove_verifies` and `prove_absent` say the World proves what it holds and
what it does not. `head_read_sound` is the phone's read: a head record that hashes to an admitted
World's chain, plus a proof against the record's root, shows that World's slot, or a collision.
`chain_binds` now binds `(turn, root)` lists, and `fold_reaches_host` says a follower at the host's
(height, chain) holds the host's World, or a collision.
Sim (the theorems' teeth). Every admitted turn replays its inserts from the pre-trie, and the
replay must reach the admitted root (an unrehashed path goes red). The Sim proves and verifies
every changed slot and one untouched one, plus each nullifier as absent BEFORE its turn. It forges
four proofs, each of which must fail: arms `proof-sibling`, `proof-leaf`, `proof-tomb-live`,
`proof-spent-unspent`, all in plantedArms. The Host's proofs verify at the follower's root. A
checkpoint reopen rebuilds the trie by `Trie.build` from its listing and must equal the trie
(listing and root).
WASTE (deterministic counts): `admit hashes-per-touched-cell` 9.985 and `admit
hashes-per-nullifier` 2.695 (kernel-sim --seeds 64, deployed). Of the 9.985, 1.92 is EMPTY-sibling
hashes: `Trie.emptyHash` is recomputed at every node with an empty child, not cached. That is
waste, not design, and it is the next cut (a cached empty digest in the Spec, with its premise in
the soundness proofs). The rest is the uncompressed path (log₂ n + ~1.3 levels at ~100 slots) plus
the sequential top-of-path repeats KERNEL-23 (h) predicted.
**Alternatives.** Keep `spent` beside the trie (ROOT ruled cells + nullifiers, KERNEL-23).
`World E`-indexed types, so that `w.live c` keeps its arity: 214 signature sites against ~60 reader
sites, and it ties a World's TYPE to one Env. A pin digest as the leaf (KERNEL-23 (b) as written):
pin-cell vs tomb vs spent would be three domains, and a cross-domain equality is not a `Collision`,
so the soundness statement would need a weaker collision notion.
**Critique.** World.Canon is a premise every World theorem now carries. It is proved for every
World the kernel constructs. A decoder must establish it (CODEC: `world_decode_canon`), or it builds a trie
whose proofs the kernel's theorems do not cover. The uncompressed trie pays ~log₂ n + 2 hashes per
change. A path-compressed trie halves that only at sizes far beyond THE BAR, and costs a second
shape argument. `Leaf.fits` (a cell slot holds an entry, a nullifier slot holds `spent`) is
enforced by construction in commit, not by type, so a decoder must refuse a mismatched pair by
name.
**Meta-critique.** I took the trie as CODEC-2 and KERNEL-4 shaped it rather than re-deriving
compression. The independent test is the phone's bytes (32 per level), which compression does not
change. The single-domain leaf digest departs from KERNEL-23 (b). The pull towards keeping (b) was
that it was already written; the soundness statement is what decides, and it decides for one
domain.
**Flag day.** The World codec becomes `kernel/world/v3` (CODEC-2, in the same landing), and every
v2 base refuses to load through HOST's shape stamp. Every chain head after height 0 changes, so
every Store re-geneses. The Turn and Call codecs are unchanged. PROTOCOL gains the head record
(height, prev, turnDigest, root) and a Proof in `read`.
**As landed (KERNEL-7).** Three amendments to the text above:
(a) *The turn-bytes premise is restated over bounded turns.* `chainNext_inj`, `chain_binds`,
`fold_head_binds` and `fold_reaches_host` used to assume `Function.Injective E.turnBytes`. That is
FALSE at the deployed codec: `nat64` truncates a counter past 2^64, so two turns that differ only
there share their bytes. They now take `TurnBytesInjOn E`, which says injective on the turns
`checkBounds` passes, and is exactly what CODEC proves (`Codec.Proofs.Deployed.turnBytes_injective`).
`chain_binds` takes a bounded-turn premise for each log. The fold theorems discharge it with
`fold_bounded`, since an admitted turn is bounded (`admit_bounded`).
`Receive.deployed_fold_reaches_host` is the instance with every premise discharged at the deployed
codec, so the follower theorem is proved at Deployed.env, not only stated. Closes cv 01a1498e-8530.
(b) *CLOSED by KERNEL-31 (was: OPEN GAP, `CellsFit` is not yet discharged).* The read theorems (`slot_inclusion_sound`,
`live_inclusion_sound`, `head_read_sound`) take `InjOn F E` and `w.CellsFit F E`. At the deployed
codec `F` must be `Cell.Fits`, because `cellBytes` is injective only on fitting cells. No theorem
yet shows that genesis, admit and fold keep `CellsFit Cell.Fits`. So these theorems are true
statements about a World whose cells are known to fit, but they are NOT yet proved for the Worlds
the deployed kernel builds. The premise is explicit in each statement, never a section variable.
The proof (`admit_cellsFit`: postWrite's slot-count check, plus `checkBounds` for births; and a
deployed instance theorem) lands with KERNEL-31 (cv 01a1498e-853e). Until then, nothing may cite
these three theorems as proved at Deployed.env.
(c) *HOST-29's per-turn roots.* A batch record is `List (Turn D × D)`, each Turn paired with the root
after it. The separate end chain is deleted, and open refuses a stated root that disagrees, by
name (`rootMismatch i`; host-sim plant `plant-flip-root`). The kernel gains one generic definition,
`Rooted admit note` (with the roots inside the definition), and `World.RootedFold E`. Host's batch
machine and Protocol's absorb both use these two, so no layer keeps its own copy.
`Kernel/Proofs/RootedFold.lean` holds `Rooted.snoc`, `RootedFold.fold` and `RootedFold.chain`.
Numbering: the carry (OPS-P1) is KERNEL-29, as proposals/ops.md and decisions/protocol.md already
cite it. This port is KERNEL-30, and the genesisFits refusal is KERNEL-31.

## KERNEL-31 · genesis refuses by name outside `GenesisFits`, and every kernel World's cells fit

**Decision.** (A) `Receive.genesis` is no longer total. It returns `Except GenesisRefusal (World D)`
and is the only entry point. `GenesisRefusal` has one constructor per clause of `GenesisFits`, in
the same order: `nameTooLong`, `nonceTooLong`, `allowanceTooLarge`, `tooManyFounders`,
`founderKeyTooLong i`, `founderNextTooLong i`. `.name` is the constructor's name
(`GenesisRefusal.name_injective`). `checkGenesis` checks the clauses in order, and
`checkGenesis_ok` proves that its `.ok` is exactly `GenesisFits`. The unchecked builder is
`genesisWorld`, and every theorem about the genesis World (`genesis_origin`, `genesis_chain`,
`genesis_rooted`, `genesis_romContent`, `receive_genesis_canon`, `receive_genesis_slotted`) is over
it. `genesis_ok : genesis … = .ok w ↔ GenesisFits … ∧ w = genesisWorld …` connects the two, so
`genesis_inj`'s premises hold for every genesis that returned. Before this, an oversize founder
key was truncated by `rawBytes` on the way into the origin, which gave an origin collision with no
hash collision. `host genesis` now prints `refused <name>` and exits with the usage code for any
refusal; its own NAME check is deleted, because the kernel's check covers it. Tooth: kernel-sim
`probeGenesis`, arm `genesis-founder-key:founderKeyTooLong` (in `plantedArms`, with
`founderKeyTooLong` in `planted`). It adds a third founder whose key is `Bounds.eventBytesMax + 1`
bytes, and it must be refused by that name at that founder's index. The control is the run's own
genesis, which is admitted.
(B) `Kernel/Proofs/CellsFit.lean` proves `genesis_cellsFit` (premises `GenesisFits` and
`∀ d, (X.env.bytes d).size ≤ Bounds.valueBytesMax`), `admit_cellsFit` and `fold_cellsFit` for
CODEC's own `Cell.Fits`, with no kernel twin. A born cell fits by `checkBounds_fits`. A written
cell fits by `mem_applyOps` (each slot is an old slot or a `set` op's pair), the op bounds, and
`postWrite_ok` (the post-write slot-count check). `RootedDeployed` gains `deployed_injOn`,
`deployed_bytes_fit`, `deployed_reach` (Canon and CellsFit for every World a checked genesis and a
fold reach), `deployed_slot_inclusion_sound`, `deployed_live_inclusion_sound`,
`deployed_head_read_sound`, and `deployed_head_read_sound_from`, which covers any canonical,
fitting World, so a reopened base (CODEC's `world_decode_canon` and `world_decode_cellsFit`) is
covered too.
**Alternatives.** Keep `genesis` total and add `GenesisFits` as a premise wherever `genesis_inj`
is cited. That is a premise nothing on the request path discharges, which is the gap this closes.
Clamp or hash oversize keys instead of refusing them: a silent reinterpretation (law 7). Define a
kernel `CellFits` and prove it equivalent to CODEC's: that is two shapes where one will do, and
`Codec.Proofs.Kernel` sits below `Kernel.Proofs` in the import graph with no cycle.
**Critique.** `genesis_cellsFit` takes a bound on every digest's bytes, not only on the digests a
genesis uses. That bound is a fact about the Env (32 at the deployed codec), so the strength it
gives up is nothing a real Env needs. The read theorems still take `hlf : leaf.CellFit Cell.Fits`
for the CLAIMED leaf. That premise is genuinely needed, because a non-fitting cell can share bytes
with a fitting one. A phone that decodes the leaf with CODEC's cell codec gets it from
`cell_lawfulOn` (whatever decodes fits), but no theorem here ties the phone's decoder to it.
Every Sim, Ops and Protocol caller now matches the refusal. Their inputs are constants that fit,
so the error arm is dead code there, but it is a named failure, never a fallback World. The Sim's
failure State uses an empty World only so that it can carry the failure.
**Meta-critique.** The pull was towards proving `GenesisFits` once in Host (where the name was
already checked) and leaving the kernel total. The kernel is the receive path, though, and HOST's
check only ever covered the NAME. A founder key from any other caller was unchecked, which is why
the refusal belongs in Kernel. I took CODEC's `Cell.Fits` as the predicate without checking
whether a weaker one would serve the read theorems. It is exactly where `cellBytes` is injective,
so a weaker one would not.
**Flag day.** `Receive.genesis`'s type changes, so every caller breaks loudly and is ported
(Host/Cli, Ops/Founder, Ops/LiveCalls, Ops/Plants, Protocol/Rows/Loopback, Kernel/Sim/Gen,
Lang/Journey, Hosting/Sim/Journey). `Ops.Founder.create` loses its `name` argument, because the
founder's id is read from `w.origin`. `host genesis NAME` with a name past `Bounds.eventBytesMax`
now prints `refused nameTooLong`, not `refused name`. Nothing persisted changes: no codec, no
chain head, and no Store needs a re-genesis.

## KERNEL-32 · A turn's weights are the codec's byte counts: `Turn.logWeight` is the record's size, `Cell.weight` a cell's bytes (KERNEL-8, 2026-10-17)
**Decision.** The per-field costs follow `Codec.Kernel` at the deployed 32-byte digest.
`Cell.weight = 9 + Slots.weight`: kind u32, discipline u8, and the slot count u32. It was 8, which
missed the count. `Op.weight`: `set` is `9 + v.size` and `erase` is `5`, because the tag byte was
missing. `Act.logWeight` is new: a 1-byte tag, plus for a write the ops list header (4) and its
ops. `Touch.weight = 2·digestWeight + act.logWeight`. `Turn.logWeight` gains one `headerWeight`
(4) for each of the touches, creates and nullifiers lists and for the event's length, so +16.
`Turn.growth` keeps `opsWeight` without the list header, because the header is log bytes, not
World growth. Admit.lean's docblock no longer claims `size ≤ logWeight` as if it were proved. It
names the equality as CODEC's theorem, owed by CODEC-4 on this sha.
**Tooth.** `Gen.checkLogWeight`: under every instance whose digest is `digestWeight` bytes (the
deployed sim, the default), each admitted turn's `(env.turnBytes t).size` must equal
`t.logWeight`, or the seed fails naming both numbers. The report prints
`record bytes = Turn.logWeight on N of M admitted turns` and fails unless N = M at the deployed
width. kernel-sim --seeds 64 (on D5c, c3c7aa3) reports 3883 of 3883. Mutation: with `headerWeight := 3` the check
fails every turn of seeds 0 and 1 (0 of 117; first `the record is 467 bytes, Turn.logWeight says 463`).
**Alternatives.** (a) Keep the hand-picked costs and have CODEC prove `≤`. That leaves a charge
that is not the price of the bytes, and an inequality is satisfiable by any over-estimate, so it
is not a check. (b) Compute the charge as `(E.turnBytes t).size` inside `World.admit`. That would
encode every turn on the request path a second time, and `Env` would then decide prices, which
is a codec dependency in the kernel's arithmetic. The static table plus CODEC's equality keeps
admit pure arithmetic and makes the equality checkable once.
**Critique.** `digestWeight = 32` is a constant, so at the toy 8-byte digest logWeight is not the
record size, and the sim skips the comparison there (`weighed` makes the skip visible: 0 of M).
The equality is not yet a theorem: the sim compares every admitted turn of 64 seeds, which is
evidence, not proof, until CODEC-4 lands `(turn dc).size t = t.logWeight`. The World's storage
weight now counts a cell as its codec bytes. Leaf and journal weights (`digestWeight + …`,
`journalWeight`) are NOT claimed equal to the World codec's trie bytes, and nothing here says
they are.
**Meta-critique.** The pull was to fold the +4 write header into `Op.weight` or into growth so as
to touch fewer definitions. Either would have made growth over-charge a write by 4 forever, or
made `Op.weight` stop being an op's bytes. A new `Act.logWeight` is one more name, but each name
now equals one codec value. I did not check the World codec's leaf layout against `Leaf.weight`.
That is the next place a hand cost and a byte count can disagree, and the Critique says so
rather than implying coverage.
**Flag day.** Every turn's charge changes (`Turn.weight` rises by 16 + 1 per born cell + 1 per op
+ 4 per write + 1 per born cell in growth). An old log replays with `chargeMismatch` at its first
turn, so every Store re-geneses. A World's storage weight rises by 1 per live cell. No codec
layout changes, nothing re-emits, and no VK or descriptor exists. kernel-sim --seeds 64 ALL PASS
admitted=3883 refused-as-expected=25113 restarts=975, and the WASTE rows (9.838 / 3.634) equal LEDGER-2's
D5c measurement. On 7c43273-era main the counts were unchanged by this change (3050 / 20992 / 954).
