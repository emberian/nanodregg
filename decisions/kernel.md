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
Status: SUPERSEDED by KERNEL-33 (the journal IS pruned to the window: `kept`, `pruneJournal`; a call's
entry answers below `notBefore + 2·windowMax`, and past `journalForgets` absence is `forgotten`, never a
false answer; a journal entry is not growth, `Turn.lean`). Marked here by KERNEL-67.

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

## KERNEL-23 · An authenticated cell root: the World's cell map IS a canonical binary Merkle trie, and the chain commits its root (KERNEL-4, 2026-10-16; DESIGN, BUILT as KERNEL-30)
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
Status: BUILT as KERNEL-30 (the World is one canonical trie of cells and nullifiers, its root in the
chain); marked here by KERNEL-67.
**Flag day when built.**
- `World` gains the trie in place of the TreeMap, and its codec changes (CODEC-14 checkpoint
  base). A base written before refuses to load, through the base's schema epoch.
- Every chain head changes (`chainNext` takes the root). A log is still a list of the same Turns,
  so it refolds, but a stored base's chain no longer matches, so Stores re-genesis.
- The Turn codec is unchanged. PROTOCOL gains a head record (height, prev, turnDigest, root) and
  the `read` reply gains a `Proof`.

LEDGER-1..5 (written here while LEDGER built under KERNEL's prefix) moved to decisions/ledger.md on 2026-10-17.

## KERNEL-24 · A call names its World: `Unsigned.world` = the World's genesis ORIGIN, refused `wrongWorld` before anything else; genesis commits to everything it was made from (KERNEL-4, 2026-10-17; DESIGN, ROOT's D3, BUILT: `Receive.receive`'s first check, `receive_wrongWorld`)
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

## KERNEL-25 · `invoke` is authorized like write: the owner, or a chain for `invoke m` rooted at the owner (KERNEL-4, 2026-10-17; ROOT's ruling on HOSTING-4, BUILT: `Receive.invoke` through `ownerAuthority … (.invoke m)`)
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

## KERNEL-26 · Public objects: a grant whose grantee is the World means "any enrolled member" (KERNEL-4, 2026-10-17; ROOT ruled, BUILT: the World grantee in `Authority.lean`, kernel-sim `invoke-public:ok`)
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

## KERNEL-33 · The journal is pruned to the window: bounded, every answer it gives true, and a call admitted at most once (KERNEL-8, 2026-10-17; ROOT-approved, from HOST-7's HOST-17 measurement)
**Defect.** `commit` inserted one journal entry per Turn and nothing removed one. So the World, its
seal cadence and its base were O(history): 72 deployed bytes per Turn, forever, which breaks law 4.
**Decision.** (1) At every multiple of `Bounds.windowMax` (W), `commit` filters the journal to the
`kept` entries, those with `H < h + 2W` (`pruneJournal`). This is one structure, with no second
by-height index that would have to agree with it. (2) `check` runs the window before the journal.
An expired retry is then `outsideWindow` whether or not its entry survives, so pruning changes no
verdict. (3) The journal leaves `World.weight` and `Turn.growth`. It is a bounded overhead of
every World (< 3W entries), not storage a Turn buys, so weight conservation stays an equality.
(4) `journalForgets H nb := nb + 2W ≤ H` names the height past which absence says nothing. HOST
answers there `uncertain forgotten` (on lookup, and on submit of an un-journaled call), never
`refused expired` and never `absent`.
**Theorems** (Kernel/Proofs/Journal.lean; every premise is discharged on the deployed path except
`admit_prune_verdict`'s window premise, see Critique):
`journal_bounded` (JournalOk ⇒ size < 3W) and `reach_journal_bounded` (every World a genesis
reaches, with no premise); `admit_retains`, `fold_retains`, and `fold_answers` (an admitted turn is
journaled at every later height where `journalForgets` is false, which is what keeps HOST's
`expired` true); `admit_spacing` (at bare `World.admit`, two admissions of one txId are more than
2W apart); `admit_twice_window` (never twice under one window); `submit_once` (through
`Receive.submit` a CALL is admitted at most once ever, with no premise and no collision disjunct,
since one call has one digest and one window); `submit_forgotten` (past `journalForgets` the
kernel refuses by window); `admit_prune_verdict` (pruning at any `H ≤ height` changes no refusal of
a turn whose window ends by its entry height + W, i.e. every call-derived retry). Host:
`handle_lookup_forgotten`; `handle_lookup_expired` now takes `journalForgets = false`;
`step_submit` still states the step is `Receive.submit`'s.
**Bare admit vs Receive (ROOT's ruling).** Bare `World.admit` cannot know that a txId is a call's
digest, so its honest statement is the spacing `admit_spacing`, and the sim arm `journal-reuse:ok`
admits a pruned txId under a fresh window. Every deployed path reaches `admit` through `receive`:
the writer through `Receive.submit` (`submit_ok`; HOST's `step_submit`), the follower through the
audit (`audit_ok`, `Honest`: every logged turn is `receive` of its own event). Two turns derived
from one call carry its digest and its window (`receive_ok`), so `admit_twice_window` refuses the
second on both paths: `submit_once` states it for the writer, `derived_once` for any log whose
turns are `receive` of their calls (the follower's `Honest` log).
**Teeth.** kernel-sim seed 0 `probeJournal` runs 3W+2 one-turn-per-height admissions. Every World
stays < 3W, and every id not past `journalForgets` is still journaled. The arms are
`journal-expired:outsideWindow`, `journal-window-first:outsideWindow` (entry present, window
first), `journal-kept:replayed` and `journal-reuse:ok`. Mutations, each run on seed 0: checking
the journal before the window fails `journal-window-first` (got `replayed`); a no-op prune fails
with "journal holds 3072 entries at height 3072". WASTE rows: `admit journal-entries-per-window`
2.999 (the static bound is 3) and `admit journal-scanned-per-turn` 1.998 (amortized prune burst).
**Alternatives.** (a) Prune every turn by a scan: O(W) per turn, which is waste. (b) A by-height
index beside the journal: O(log) per turn, but two shapes kept in agreement by an invariant. (c)
Keep `H < h + W`, the least a retry needs. Then a lookup just after a call's window ends could
already find its entry pruned, and `expired` would lie at once. 2W gives at least W heights of
truthful `expired` after every window. (d) Keep the journal-first order and prune. Then an expired
retry's verdict (`replayed` or `outsideWindow`) depends on prune timing, which is a verdict that
history decides.
**Critique.** The bound is 3W, not W, which is the price of the amortized prune plus the 2W grace.
At W = 1024 that is ~3072 × ~72 bytes, about 220 KB per World: constant, but not small for a
phone-sized World. Pruning is a bounded burst on the request path (up to 3W map operations every
W heights), and it is measured as an amortized row, not hidden. `forgotten` is a weaker answer
than the old `ok receipt`: a client that waits more than ~2W heights must resolve its call from
the log (PROTOCOL-6 owns the row). `admit_prune_verdict`'s window premise is discharged by
call-derivation but not proved over a fold's provenance, and it compares ONE prune against the
unpruned World. The deployed World was pruned at every multiple of W; that all past prunes
equal one prune at the latest multiple (`kept` is monotone in H) is not yet a lemma (that
sentence closed by KERNEL-38: `fold_journal_filter` along the real fold, `fold_prune_check`; the
window premise over a fold's provenance stays open, KERNEL-38 Critique).
`submit_once`, `derived_once` and `admit_twice_window` carry the content that matters.
`reach_journal_bounded` covers Worlds a fold reaches from genesis; a World decoded from a base
is covered only through the fold that wrote it (no codec theorem carries `JournalOk`; closed by
KERNEL-39 + CODEC 9dd1e8c: the decoder refuses `kernel/journal`, `Codec.Deployed.world_decode_journalOk`). HOST's
`expired` truth is `fold_answers` + `receive_ok`, not yet chained in a Host theorem (offered to
HOST-8). `World.weight` no longer counts the journal: total storage is weight plus at most 3W
journal entries (~220 KB), bounded only by `journal_bounded`, with no single theorem summing the two.
Second-agent vacuity read done before landing (no vacuity; these gaps are its findings).
**Meta-critique.** The pull was to state "pruning changes no verdict" for every Turn. That is
false at bare admit (a recycled txId under a fresh window), and writing the spacing theorem plus
the reuse arm says so instead of hiding it behind a premise. ROOT's wording was "up to a hash
collision", but per call no collision is needed, so the theorem is stronger than asked. It covers
only the same call: two different calls with one digest are still a collision, outside every
statement here.
**Flag day.** (1) Every charge falls by `journalWeight` (72), since growth no longer counts the
journal entry. Every Store re-geneses, and an old log refuses at its first turn with
`chargeMismatch`. (2) The check order changed, so an expired exact retry is `outsideWindow`, no
longer `replayed`. (3) World codec: unchanged in layout. A reopened base's journal is whatever was
written, pruned or not. A base sealed before this change holds an unpruned journal and refuses
anyway with the charge flag day. (4) Host wire: a lookup or submit of an un-journaled call past
`notBefore + 2W` now answers `uncertain`/`forgotten` (HOST-7's arm, built here under
--cross-layer at its invitation). Nothing re-emits.

## KERNEL-29 as built · carry state by re-genesis: `Carried`, `Receive.carry`, one tagged origin (KERNEL-8, 2026-10-17; OPS-P1 as agreed by OPS-2, PROTOCOL-6, HOST-6, CODEC-2/3; after KERNEL-33)
**Decision.** `Carried D := {trie, allowance, height, journal}` (Kernel/World.lean) and
`World.carried w`. The trie is every cell and every spent nullifier, so spent is state: a carried
value cell whose nullifier was spent cannot be spent again. The journal is carried WHOLE. It is
bounded by KERNEL-33 (< 3·windowMax, `Bounds.journalMax`), so nothing needs filtering, and
PROTOCOL-29's rule holds: a call committed just before the export is answered `replayed` after it,
never re-run. The height carries because journal entries expire by it.
`Receive.carry X name nonce fromOrigin c` refuses by name outside `CarryFits` (`CarryRefusal`:
nameTooLong, nonceTooLong, allowanceTooLarge, heightTooLarge, journalTooLong, entryTooLarge, one
constructor per clause, as for genesis, KERNEL-31). Otherwise it returns `carryWorld`: the carried
state, origin `carryOriginOf`, chain `genesisChain origin`. There are no founders. The members are
the carried member cells, and their keys sign the new World's calls.
**One origin domain, tagged.** `domOrigin` is now v2, and `originOf` (genesis) and
`carryOriginOf` both hash `originInput = Stream.sum genesisInput carryInput`. That is one domain,
with the case in the first byte (KERNEL-6's "one domain with a kind byte"). `carryInput` is name ‖
nonce ‖ fromOrigin bytes ‖ root(trie) bytes ‖ u64 allowance ‖ u64 height ‖ the journal listing
(id bytes ‖ u64 height ‖ digest bytes, ascending, at most journalMax). The trie enters by its
root, O(1), with no second encoding.
**Theorems** (Kernel/Proofs/Carry.lean): `checkCarry_ok`, `carry_ok`; `carry_carried` (the new
World carries exactly `c`) and `carry_of_carried` (export then carry: same trie, allowance, height
and journal; only chain and origin are new); `carry_origin_ne_genesis` (equal origins ⇒ `HashColl`
under domOrigin, whose preimages differ in their first byte by `sum_inl_ne_inr`); `carry_inj`
(equal carry origins ⇒ equal name, nonce, exported origin, trie ROOT, allowance, height and journal
up to `Equiv`, or a collision); `carry_canon`, `carry_cellsFit`, `carry_journalOk` (the read and
journal invariants survive the carry); `carry_journal_fits` and `carry_fold_journal_bounded` (a
reached World always fits a carry's `journalTooLong`, and so does every World folded from a carry,
so a second carry passes: a vacuity reader's finding, closed here); `carry_replayed` (an exported journaled call is
`replayed` at its height on the carried World). Origin.lean: `genesis_inj` reproved through the
tag (`ba_append_cancel`, `sum_bytes_inl_on`), with the same statement.
**Teeth.** kernel-sim, every seed: `probeCarry` carries the Host's World under a new nonce. It
requires the same root, allowance, height and journal listing and a different origin. Arms:
`carry-old-call:replayed` (the last logged call), `carry-old-world:wrongWorld` (a fresh call
signed for the old World), `carry-new:ok` (the same call signed for the new World is admitted),
and `carry-name:nameTooLong`. The old-call arm checks the replayed HEIGHT against the exported
journal's. Mutation: a carry that drops the journal fails every seed ("the
carried World differs").
**Alternatives.** (a) Two domains, domCarry and domOrigin. Then "never a genesis origin" needs a
domain-separation assumption about the hash, while one domain with a tag reduces it to an
ordinary collision. (b) Hash the trie listing into the origin, which is an O(state) second
encoding of what the root already commits to. (c) Filter the journal to the window at carry
time. That was the shape before KERNEL-33. A filtered TreeMap equals nothing structurally, and an
unbounded listing would have needed its own bound.
**Critique.** `carry_inj` binds the trie through its ROOT. Two different tries with one root are
a collision of the trie hash, which is outside this theorem. `carry_canon`, `carry_cellsFit` and
`carry_journalOk` are true by construction (the carried World holds the same trie, journal and
height), so they state that nothing was lost, not a new fact. Carried member and grant ids keep
their old, old-origin-keyed values, which is acceptable only while ids are opaque (OPS-1 CRITIQUE).
The kernel does not check that `fromOrigin` is the origin of the World whose state `c` is. HOST's
import binds the bytes to the old Store by `--digest` (HOST-28). The WASTE counts moved
(hashes-per-touched-cell 9.838 → 9.715, hashes-per-nullifier 3.634 → 3.451), because the origin
v2 changes every founder id and so the trie paths. The ceilings stay where they are: the counts
are below them, and the move is caused by the ids, not by the code.
The `chain` field now says what it is after a carry (`genesisChain origin` at the carried height,
then one link per turn): a carried Store's audit starts from `carryWorld`, not from genesis
(HOST-28). Second-agent vacuity read done: no vacuity; its two gaps are closed above.
**Meta-critique.** The agreed text said `Carried = {trie, allowance}`, with the height and the
in-window journal added by PROTOCOL-6's and OPS-2's answers. I put all four into the one
structure, so that byte equality of `Carried` is the whole import check (CODEC-22), with no side
file field filled in by interpretation. The pull was to keep genesis's origin input untouched and
add a separate carry domain. I did not, because a fact that holds only under an unstated hash
assumption is the kind of premise this repo names and then forgets.
**Flag day.** domOrigin v2: every genesis origin changes, so every founder id, every chain and
every World changes, and every Store re-geneses (also due under KERNEL-33's charges). Nothing
re-emits. A call signed for an old origin is `wrongWorld`. CODEC-22's carried codec (CODEC-5) and
HOST-28's export and import (HOST-8) build on this.

## KERNEL-34 · The phone's read takes the leaf's bytes: KERNEL-31's last premise, discharged by CODEC's leaf decoder (KERNEL-8, 2026-10-17; CLIENT-16, ROOT-accepted)
**Decision.** `deployed_head_read_sound_bytes` (from a reached World) and
`deployed_head_read_sound_decoded_bytes` (from a reopened base) take the served leaf BYTES and
`Codec.Kernel.leaf.decode b = .ok lf` in place of `hlf : lf.CellFit Cell.Fits`.
`Codec.Kernel.leaf_decode_cellFit` (CODEC-4, ee49de8) supplies the fit, so no premise about the leaf
is left. KERNEL-31's open premise (the claimed leaf's fit, routed to CLIENT-3 and then CLIENT-16) is
closed on the Lean side. The phone must show only what Lean's leaf decoder returns (CLIENT-16's
condition; no Rust parse).
**Tooth.** CODEC's `leaf_decode_refuses_misfit` (a misfit leaf never decodes) and its sim plant
`kernel/leaf-fit`. These theorems compose existing ones, and the decoder premise is what makes
them stronger than the `hlf` forms they keep.
**Critique.** No head-read path exists in the client yet (PROTOCOL-14 option B, pending Ember's
phone ruling), so these theorems state what that path must call. The old `hlf` forms stay,
because the bytes forms are corollaries of them, not a second shape.
**Meta-critique.** I considered deleting the `hlf` forms. They are the general statement (any
fitting leaf), and the bytes forms only specialize them, so keeping both keeps one fact at two
strengths, not two shapes.
**Flag day.** None. Nothing refuses, nothing re-geneses, nothing re-emits.

## KERNEL-35 · The empty subtree's digest is hashed at most once per turn: one lazy copy handed down the mutation path (KERNEL-9, 2026-10-18; cv 01a1498e, KERNEL-8's handoff item 1)
**Decision.** `Trie.T.hashOf`, `mkNode`, `build`, `insAt`, `proveAt`, `T.insert` and `T.prove` take a
trailing `e : EmptyDigest D := Thunk.mk fun _ => emptyHash S` (`EmptyDigest D := Thunk D`), and
`.empty` hashes to `e.get`. `World.insertAll` and `spendAll` take the same trailing `e`. `commitTrie`
makes ONE lazy copy (`let e := Thunk.mk fun _ => Trie.emptyHash (trieSpec E)`) and passes it to every
insert of the turn, so the empty digest is hashed at most once per admitted turn, and only if some
new path has an empty sibling. Before this, `T.hashOf .empty` recomputed `S.hash (tagged 0 [])` once
per empty sibling (1.44 per touched cell). A decoded trie (`Codec.World`'s `Trie.build`) and a served
proof (`T.prove`) get the same at most one by default, because the recursion passes its one copy down.
**Wire.** None. The empty digest is the same `H(0)` and every node hash is unchanged. Nothing
re-geneses or re-emits, and nothing refuses to load.
**The two designs (KERNEL-8's handoff).** (a) A `Spec` field `empty : D`, with a proof-side
hypothesis `S.empty = S.hash (tagged 0 [])` threaded like `hL hN`. (b) Thread `e` computed once per
`commitTrie`. I chose (b), as an optional trailing argument, for three reasons. First, Lean is strict:
a `Spec` field is computed every time a `trieSpec E` is built, which happens on every
`get`/`insert`/`root` (there are 182 `trieSpec` sites). Under (a) a lookup that never meets an
empty subtree would START paying one hash, and inserts would pay once each unless every caller
bound `S` once. Second, (a) adds a premise to every generic soundness theorem (Canon preserved,
inclusion and exclusion sound, climb_sound, build_toList), which changes their statements. Third,
under (b) every statement elaborates to exactly what it said before: `t.hashOf S` now means
`T.hashOf S t (Thunk.mk fun _ => emptyHash S)`, and its unfolding is defeq. Not one proof line
changed in Kernel/, Codec/ or anywhere else (403 jobs green).
**Strict or lazy.** Measured both. With a strict `e` (one hash per turn, met or not), the row came
to 9.166 = 8.275 path + 0.891. With the lazy `Thunk`, it came to 8.915 = 8.275 + 0.640, because about
28% of turns meet no empty sibling. Lazy is the exact design (pay iff needed), and it cost no proof.
**Tooth.** (1) The WASTE rows re-pinned DOWN: `admit hashes-per-touched-cell` 9.715 -> 8.915 and
`hashes-per-nullifier` 3.451 -> 3.211 (ceilings 9.985 / 3.634 -> the measured values). The sim's
`insertHashes` now counts what the code does: path nodes + leaf + split + 1 for the first insert
of the turn whose new path has an empty sibling. Its replay in `checkRoot` shares one lazy copy,
as `commitTrie` does. (2) Mutation: `commitTrie`'s `e := H(tagged 9 [])` (a wrong empty digest)
makes kernel-sim 64/64 seeds FAIL "replaying the turn's inserts does not reach the admitted root",
and makes Kernel.Proofs.Frame stop compiling (commitTrie_cell, spendAll_spent_of_spent: the
theorems are stated at the default, and the `let`-reduced commitTrie IS the default form, so a
wrong `e` is not a World any theorem describes). (3) The existing forged-proof arms (proof-sibling,
proof-leaf, proof-stale) all PASS.
**Critique.** The WASTE row is a MODEL of the hash count read off the tries (`insertHashes`), not
an instrument on the hash calls. If someone dropped the `e` argument from `commitTrie` (back to
one default per insert), the row would stay at 8.915 and only the code would regress. Only a
counting hash could see that, and a pure `Env.hash` cannot count its own calls (GATES-9's critique,
in this instance). The remaining 0.640 per cell is one hash per turn of a value that is constant
per Env. Caching it across turns needs a field in the Env (an `Env.Lawful` obligation on a
trie-internal value) or in the World (a cached field with an invariant on every decoded base).
Both would put a derived copy into an interface in exchange for 7% of this row, and I took
neither.
**Meta-critique.** "Not one proof changed" is evidence that the refactor is invisible to the
theorems, and that could also mean they do not see the new argument. Mutation (2) is the check:
the proofs DO see a wrong `e`. The optional-argument form also lets any caller pass a wrong `e`
and get a non-WF trie. That is allowed by the types and refused by the proofs (no theorem holds of
it), the same position as any caller building a `T.node` by hand.

## KERNEL-36 · The trie hash rows are INSTRUMENTS: kernel-sim counts the calls the real admission makes (KERNEL-9, 2026-10-18; ROOT ruling on KERNEL-35's critique)
**Decision.** `Kernel.Sim.Gen.countingEnv E` is `E` with every trie-domain (`domTrie`) hash
marked. It writes one `#` through core's `dbgTrace`, which is `never_extract`, so the compiler
neither shares nor hoists a marked call, and then returns `E`'s digest unchanged. For every
admitted turn, `countTurn` runs the REAL `World.admit` (bracket `<A`), the REAL `commitTrie` with
the turn's nullifiers dropped (`<C`, the cell share), and the plant (`<P`) under it. Each result is
checked against the uncounted call ("the counter changed the computation" otherwise). `report`
captures stderr per seed (`IO.setStderr` onto a buffer, the run forced by `IO.lazyPure`) and
computes cell = C, nullifier = A - C. Sim.insertHashes, the model, is DELETED. Sim-only: no
deployed module names countingEnv.
**Why not an IO.Ref.** ROOT's wording was "one IO.Ref or a counting Env". A pure `Env.hash` can
bump a ref only through `unsafeBaseIO` (law 4 refuses `unsafe`) or an `@[extern]` C counter (a
gates/native-allow.tsv row and a C file in the sim). `dbgTrace` is core, safe and already compiled.
A probe on hbox (logs/kernel9-probe) showed that it lands in a buffer installed by `IO.setStderr`
and that `h i + h i` counts 2.
**Measured.** 8.915 / 3.211. These are exactly the values KERNEL-35's model gave, so the model was
right, and from now on the code is what is counted.
**Tooth.** (1) Plant `plantCommitPerInsert`: the same map, with the empty digest per insert. It must
count MORE than the real admission in every 16+-seed run, or arm `hash-count:empty-per-insert` is
unmet and the sim FAILS (it is in plantedArms). (2) Mutation of the REAL code: World.insertAll and
spendAll ignoring the shared `e` (per-insert recomputation) => hashes-per-touched-cell 9.006 >
8.915 (standing RED) AND kernel-sim FAIL "planted refusals never met: [hash-count:empty-per-insert]",
because the plant then equals the code. This catches exactly what KERNEL-35's "wrong e" tooth
could not: a recomputed but CORRECT e.
**Critique.** `never_extract` makes the counted Env a slight upper bound: if the deployed compiler
ever shared two identical `E.hash` calls in one body, the counted run would still count both.
There are none on the trie path today. The rows count the trie domain only, and a hash added
under another domain on the admission path is invisible to them. stderr is now the counter's
channel during a run: if any future pure code in the sim writes there, its `#`s would be counted
(none does; the bracket parse counts only `#`).
**Meta-critique.** I measured A for the turn and C as the cell share. A turn's lazy empty digest
lands in C if a cell insert forces it, else in A - C. That is the same attribution the model used,
and it is a choice: the floor is per turn, and the rows are per slot.
**Flag day.** None. Nothing refuses, nothing re-geneses, nothing re-emits.

## KERNEL-37 · `Env.Lawful`: what the kernel's theorems assume of an `Env`, in one premise, proved at the deployed codec (KERNEL-9, 2026-10-18; agreed CODEC-3 / KERNEL-7, KERNEL-8's handoff item 2)
**Decision.** `Kernel/Proofs/Lawful.lean` defines `structure Env.Lawful [Ord D] (E : Env D) (n : Nat) :
Prop` with the fields `size`, `n_le` (n ≤ 32), `bytes_inj`, `turnBytes_injOn` (TurnBytesInjOn E) and
`cellBytes_injOn` (InjOn Codec.Kernel.Cell.Fits E). `TurnBytesInjOn` (from Fold) and `InjOn` (from
Cells) move there unchanged. Every Kernel/ theorem that took a loose Env premise takes
`hE : E.Lawful n` instead:
- Fold: chainNext_inj, chain_binds, fold_head_binds, fold_reaches_host (hsz hb ht).
- Cells: slots_separate (hn too), slotBytes_inj, dbytes_pair_inj, leafBody_size, leafBody_inj,
  slot_inclusion_sound, slot_exclusion_sound, live_inclusion_sound, unspent_sound, trie_ext (hn
  too), head_root, head_read_sound, head_absent_sound (hsz hb hcb).
- Rooted: derive_born, step_rooted, submit_rooted, audit_rooted (pointwise hinj).
- Origin: genesis_inj, genesis_chain_inj. Carry: carry_inj (pointwise hb).

The World-level inclusion theorems fix `F := Cell.Fits` instead of taking a generic `F` with
`InjOn F E`. The two lemmas about any `F` (leafBytes_inj, leafDigest_inj) stay generic, because they
are facts about `InjOn F`, not about the Env. `Receive.deployed_lawful : env.Lawful 32` is proved in
RootedDeployed from CODEC's d.size_eq, bytes_injective, turnBytes_injective and
cellBytes_injective, and every deployed_* theorem now passes it. Their statements are unchanged.
**CODEC's side.** The handoff planned CODEC-5's `env_lawful : env.Lawful 32`. Every fact it needs is
already a CODEC theorem, and RootedDeployed already imports Codec.Proofs.Deployed, so I proved it
here in eight lines. CODEC-5 has nothing to write, and a second copy in Codec/ would be a twin.
**What it closes.** PROTOCOL's named gap (decisions/protocol.md, "No theorem says the signature
binds the world BYTES ... needs `Env.bytes` injective, a property of the Ctx that no Ctx states
yet"). The property is now stated (`Env.Lawful.bytes_eq`) and discharged at Deployed
(`deployed_lawful`). PROTOCOL-6 is told.
**Tooth.** The premise is SATISFIABLE (`deployed_lawful`, from CODEC's non-vacuous codec theorems)
and REFUTABLE (`Env.Lawful.refutable`: an Env whose digests share their bytes is lawful at no size).
So no theorem taking it is vacuous at Deployed, and it is not a premise any Env meets for free. The
statements' content is unchanged, and the existing teeth of each theorem (follower forge arms,
proof-forgery arms, carry and genesis arms) are untouched (kernel-sim ALL PASS). Second-agent vacuity read (before landing): no vacuous theorem, no conclusion changed, deployed_* statements byte-identical, every Lawful field from a non-vacuous CODEC theorem; WEAKENED at the generic level only (theorems that used bytes_inj alone now take all of Lawful, and [Ord D] is required where it was omitted), harmless at Deployed (the Critique below); a docstring overclaim fixed.
**Critique.** A theorem that needed only `bytes_inj` (genesis_inj, the rooted chain) now asks for
all five fields, so it no longer applies to an Env that is injective but not, say, 32-bounded (the
toy UInt64 Env has no Lawful proof, and no theorem is applied to it). That narrows generality on
purpose: one premise that the deployed Env meets, instead of five shapes. LEDGER-3's
Kernel/Proofs/Value.lean (3 theorems) and Ledger.lean (account_keyed) still take the pointwise form.
They are LEDGER's files, so I asked LEDGER-3 to convert them.
**Meta-critique.** I considered keeping the pointwise theorems' minimal premise, on the grounds that
"assume less" is the better theorem. That would mean keeping two shapes of one fact (pointwise and
bundled) and leaving every caller to pick, and that drift is exactly what this structure exists to
end. The deployed instance is the only consumer.
**Flag day.** None. Nothing refuses, nothing re-geneses, nothing re-emits.

## KERNEL-38 · All the prunes of a history are one prune of the journal that never forgot: `fold_journal_filter`, and pruning changed no check in a real fold (KERNEL-10, 2026-10-18; KERNEL-33's Critique, KERNEL-9's handoff item 1)
**Defect.** KERNEL-33's `admit_prune_verdict` compares ONE prune of a World's journal against that
same journal unpruned. A real fold inserts and prunes at every turn, so that theorem never
described a World any history reaches. KERNEL-9's first attempt, a list of prunes of one fixed
journal, collapses to one prune (`kept` is antitone in H) and still never matches a real fold, so
it was rejected unlanded (hbox logs/kernel9-k38-rejected.patch).
**Decision.** (1) A specification, `Kernel.Sim.Shadow` (tooling: no deployed path computes it):
`shadowJournal E h J l` is the journal the log `l` leaves from `J` at height `h` if nothing is
ever removed, each turn's entry inserted at its height exactly as `commit` inserts it. `lastPrune h`
is the last multiple of `windowMax` at or below `h`. The shadow is a journal along the REAL fold,
not a second fold. A second fold reading its own unpruned journal would refuse a recycled txId
`replayed` (the `journal-reuse` arm), so it would not follow the log, and any theorem about it would
need the conclusion as a premise. (2) `fold_journal_filter`: from any World whose journal is `J`
filtered at its last prune (`journalFiltered_self`: every `JournalOk` World with `J` its own
journal, so every genesis and every World a fold reaches), the World a fold reaches holds, at every
txId, exactly the shadow's entry filtered by `kept (lastPrune w'.height)`. Proof: one commit step
(`commit_filtered`), at a multiple of W by `filter_kept_anti` (filtering at H then at H' ≥ H is
filtering at H'), and between multiples `lastPrune` does not move and the new entry is kept. (3)
`check_prune` (the check-level core of `admit_prune_verdict`, which is now its corollary) and
`check_journal_congr` (`check` reads the journal only at the turn's txId). Together they give
`fold_prune_check`: the World a fold reaches checks a turn EXACTLY as the same World with the
never-pruned journal (the same refusal or the same posts), for every turn whose window ends by its
txId's never-pruned entry height + W. `Receive.reach_prune_check` states it from genesis with every
premise but that window discharged.
**Teeth.** kernel-sim seed 0's journal probe now folds its 3W+2 turns into the shadow with the
spec's own definitions. Arms: `journal-shadow:filtered` (the real journal's listing equals the
shadow's filtered at `lastPrune`), `journal-shadow-kept:replayed` (a windowed retry whose entry the
shadow holds: the World carrying the never-pruned journal gives the real verdict), and
`journal-shadow-reuse:replayed`: the
fresh-window reuse, outside the window premise, is `ok` on the real World and `replayed` on the
shadow, so the premise does work. All are in `plantedArms`. Mutations, each run on seed 0 and then
restored: (a) pruning at EVERY height (`if True`): the existing KERNEL-33 probes stay green (the
journal is still bounded, and every id below `journalForgets` is still answered), and only
`journal-shadow:filtered` refuses ("the journal at height 3074 is not the never-pruned one filtered at
3072"). This is the mutation KERNEL-33's teeth were blind to. The proofs refuse as well (Admit's
`pruneJournal_get` stops compiling). (b) A prune that drops live entries (`kept (H + W)`): the
proofs refuse, and the sim fails at `fold_answers`' probe. kernel-sim --seeds 64 ALL PASS, and no
WASTE row moves (8.915 / 3.211 / 2.999 / 1.998).
**Alternatives.** (a) A second fold `World.foldNoPrune` that admits with its own journal. That
diverges at the first recycled txId, so a theorem relating it to the real fold must assume that no
turn ever hits a pruned entry, which is the content in question. (b) KERNEL-9's composition of
prunes of one journal: rejected (see Defect). (c) Proving `fold_prune_check` with the window premise
discharged on every `Honest` log. The shadow's entry for a txId is its LATEST admission. On a
receive-derived log that admission is the same call as the retry unless two different calls share
a digest (`submit_once`/`derived_once` exclude the same call twice), so the discharge needs a
digest-collision disjunct over the call codec. That is a further theorem, not a weaker form of this
one, and it is named below (cv task 01a14a8a-7364).
**Critique.** The window premise `hv` is stated on the SHADOW journal, not discharged. It holds
for every retry of the call that wrote the latest entry under that txId. A log that recycled a txId
under a fresh window (bare admit only; `journal-reuse`) is exactly where it fails, and the arm shows
the two Worlds then disagree, so the premise cannot be dropped. Discharging it for `Honest` logs is
alternative (c). `shadowJournal` sits in a tooling module because a proof-module may not export a
non-Prop def (closure C3) and the sim, a def-module, may not import a proof-module (C4). One
definition serves the proof and the probe, at the cost of `Kernel.Proofs.Journal` importing a
`Sim` module (allowed: C9 constrains deployed def-modules only). The equality is pointwise
(`JournalFiltered`, at every txId), not `=` of TreeMaps, because two maps built by different
insert/erase orders need not be structurally equal. `check` reads the journal pointwise, so nothing
consumes more.
Second-agent vacuity read (before landing): every statement OK, `hv` does not contain the
conclusion, `fold_journal_filter` is over the real interleaved fold; three docstring overclaims
fixed (the shadow decides nothing; it is the same World carrying the never-pruned journal, not a
World a never-pruning node reaches; a recycled id keeps only its latest entry); two arms whose
window fails on both sides (expired, window-first on the shadow) dropped as distinguishing nothing.
**Meta-critique.** The pull was to call KERNEL-33's critique "closed" by the first statement with
"fold" in its name. KERNEL-9's rule (a theorem that never matches a real run is not landed) is what
forced the shadow to be a journal along the real fold rather than a fold of its own. The other pull
was to discharge `hv` by putting it in a convenient premise of the corollary. It stays a visible
premise with its refuting arm instead.
**Flag day.** None. No definition on the deployed path changed. Nothing re-geneses, re-emits or
refuses to load. `admit_prune_verdict`'s statement is unchanged; it is now proved from `check_prune`.

## KERNEL-39 · A decoded base carries `JournalOk`: `journalFits`, the kernel's half of CODEC's `kernel/journal` refusal (KERNEL-10, 2026-10-18; KERNEL-33 Critique (b), agreed with CODEC-6)
**Defect.** `reach_journal_bounded` covers Worlds that a fold reaches. A World decoded from a base
holds whatever journal was written, and the World codec bounds that listing only by `worldMax`
(2^32 − 1); `journalMax` bounds only the carried codec. A base can therefore hold an entry above its
height. That entry is never pruned (`kept H e` holds while H < e.1 + 2W), so it answers `replayed`
forever to a call that never ran. A base can also hold more than 3W entries, or two entries at one
height. None of these is a state that any fold reaches, and nothing refuses it.
**Decision.** (1) Kernel/World.lean (deployed): `journalFits height l : Bool`. Every entry satisfies
`e.1 ≤ height ∧ height < e.1 + 2W + height % W`, and the heights are pairwise distinct. The
distinctness check sorts the heights (`mergeSort`) and checks that the result is strictly
ascending (`ascendingNat`): O(n log n) with n < 3W, run once per decode, never on the request path.
(2) Kernel/Proofs/Journal.lean: `journalOk_of_fits` (a listing that fits is a `JournalOk`
journal) and `journalFits_of_ok` (every `JournalOk` journal fits). Together these say the check is
EXACTLY the invariant, so it refuses no base that a fold wrote (`fold_journalOk`). (3) CODEC-6
(agreed, its half lands next): the World's shape gains the named refinement `kernel/journal`, and
its decoder refuses `rejected i "kernel/journal"` when `journalFits` fails. The journal list is
bounded by `Bounds.journalMax` (refused `pastBound`), and `World.CodecFits` gains `journalFits` as a
conjunct, which `journalFits_of_ok` discharges for the round trip. CODEC writes
`world_decode_journalOk` and its deployed corollary. A Kernel-side `deployed_base_journalOk` would be
a twin, so there is none.
**Teeth.** `journalFits_future` (an entry at height + 1), `journalFits_stale` (an entry past due
for pruning at the last prune) and `journalFits_twice` (two entries at one height) are named
refutations, one per clause, so no clause is `true`. kernel-sim arm `journal-fits:misfit`: at the
end of the journal probe, the reached World's listing fits, and a listing with one future entry,
one stale entry, or a second entry at a journaled height, does not. Mutation
(the distinctness half replaced by `true`): kernel-sim seed 0 FAILs "a future or a doubled entry
fits", and `journalOk_of_fits` / `journalFits_of_ok` stop compiling. CODEC's WorldTooth plants
the bytes-level refusals. kernel-sim --seeds 64 ALL PASS, and no WASTE row moves.
Second-agent vacuity read (before landing): LAND; the characterization is exact (an iff on
`w.journal.toList`); the stale clause lacked a refutation (added). CODEC's obligation, named to
CODEC-6: the list `journalFits` reads at decode must be provably the decoded map's own `toList` (the
decoder already refuses keys that are not strictly ascending, so `toList_ofList_of_sorted` gives it).
**Alternatives.** (a) A kernel check at HOST's reopen: a second place where a decoded World becomes
trusted, outside the one decoder. Every reader of World bytes would have to remember to call it.
(b) Refuse only future entries, the cheap half. Two entries at one height break
`journal_bounded`'s counting, so that half is needed. (c) Prune a decoded journal on read instead of
refusing it. That reinterprets bytes nobody wrote, which law 1 forbids ("old shapes refuse").
**Critique.** The check costs a sort per decode (< 3072 heights). A base is decoded once per open,
so this is not request-path work, and it is not measured as a WASTE row. `journalFits` reads
heights only. A journal entry's digest is still whatever the base says, and nothing checks it
against a turn. That is the same trust every base field gets: the base seal and HOST's audit
answer for it, not the decoder. The carried codec does not call `journalFits`, because
`Receive.carry` already refuses outside `CarryFits`. That leaves two places stating journal
bounds, CarryFits for a carry and journalFits for a base. They state different facts: a carry's
height is the carried one, while a base's entries must also be distinct and within the window.
**Meta-critique.** The pull was to put the check where the defect was noticed, at the kernel, as a
reopen assertion. The premise enters at decode (law 4: an assertion where the premise crosses the
boundary), so the decoder is where it belongs, and the kernel supplies only the predicate and its
exactness.
**Flag day.** Kernel side: none (a new definition with no consumer yet). CODEC-6's half moves the
World's tag (`kernel/world` gains the `kernel/journal` node), so every Store base re-seals or
re-geneses, and an old base refuses `shapeMismatch`. CODEC states this in its commit.

## KERNEL-40 · Ids are names: a carried World keeps its members' ids, and a carry changes no authority (KERNEL-10, 2026-10-18; ROOT's item from OPS-2's OPS-1 critique, agreed with PROTOCOL-6)
**Question.** A carry (KERNEL-29) keeps every cell at its id. Member and founder-grant ids were
derived at genesis from the World's origin (`founderId X origin i`, KERNEL-24), so after a carry
they are keyed by the OLD origin. There are two ways to handle that: (a) the carry re-keys every id
under the new origin, or (b) ids are opaque names, with a theorem that nothing in receive derives
meaning from an id's origin.
**Decision: (b), opacity.** An id is a name. Its derivation at genesis is a fresh-name generator,
which makes ids unique across Worlds. A lineage's ids are namespaced by its FIRST origin, and every
carried origin commits to that one through `fromOrigin`. Nothing may recompute an id from the
CURRENT origin. A consumer that needs founder ids after a carry reads them from the World (the
member cells) or from the lineage's genesis.
**Enumeration** (main f6b6b60). In deployed Kernel code `founderId`/`founderGrantId` are computed
only in Receive.Follow's genesis. `receive` reads `w.origin` exactly once (Derive.lean,
`req (c.unsigned.world = w.origin) .wrongWorld`). A World-targeted grant names `worldId X`, a Ctx
constant. Admission (`check`) never reads the origin or the chain. Consumers that recompute an id
from a World's current origin: Ops/Founder.create (its docstring already says to use `createAs` with
the old id after a carry, and Ops/Plants does), Host/Cli's founder print (a genesis World only),
Lang/Journey (genesis), and Protocol/Rows/Loopback.freshActor. That last one was a LATENT DEFECT:
after the carry act it derived a founder's id from the carried origin, so a founder acting first
after a carry would have been `unknownKey`. PROTOCOL-6 fixed it in 4147b9b (PROTOCOL-36:
`St.lineage` keys founder ids, and row carry gains a first act after the carry). The client takes
member ids from its invitation and never derives them.
**Theorems.** Kernel/Proofs/Carry.lean: `receive_reorigin` (give a World any new origin and chain:
a call naming the new origin is derived through the OLD World's pinned view, so `receive` reads the
origin and chain only in the World check), `receive_named` (a call
that names its World is derived from the pinned state alone), `carry_receive` (the carried World
derives every call that names it through the exported World's own pinned view: the same members,
keys, grants and cells at the same ids; a corollary of `receive_reorigin`), `check_origin_blind`
and `carry_check` (the carried World
checks every turn as the exported one). Kernel/Proofs/CarryRooted.lean (new): `carry_rooted` (a
carry keeps `WorldRooted` with the SAME roots) and `deployed_carry_rooted`. On a World audited from
genesis, carried, and audited again, every World grant is rooted at the FIRST genesis's founder
grants, with no premise beyond the two audits and the carry.
**Teeth.** Mutation: a carry that drops the trie (`trie := .empty` in carryWorld). `carry_receive`
and `carry_check` stop compiling, as do carry_carried and carry_canon, and kernel-sim seed 0 FAILs
"probe carry: the carried World differs". The standing arm `carry-new:ok` (an old member's fresh
call for the new World is admitted) is the runtime form of `carry_receive`. PROTOCOL's row carry now
runs a founder's first act after a carry; with the old derivation it fails "got refused
unknownKey".
**Alternatives.** (a) Re-key at carry. That rewrites every member cell id, every grant's
grantee/issuer/parent slot, and every keyed ledger account (KERNEL-28). The carried trie would no
longer be the exported trie, which breaks law 1's check (canonical World bytes equal up to the
epoch header), `carry_inj`'s binding of the trie by root, and HOST-28's `--digest`. It is also a
second state transform beside the fold, with an authority-preservation theorem to prove over every
id-bearing slot. (b′) Opacity with no theorem. That leaves "nothing reads an origin out of an id"
as prose, which is exactly what Loopback.freshActor violated unnoticed.
**Critique.** `carry_rooted` is true by construction (the trie is copied), and an empty trie is
also rooted. The content that a carry KEEPS the members is `carry_receive` and `carry_carried`, not
`carry_rooted`. The rule "never recompute an id from the current origin" is enforced by no gate, so
a new consumer can repeat Loopback's mistake. Its guard is a row or plant that acts after a carry,
as row carry now does. "Nothing reads an origin out of an id" is PROVED for the World's origin
(`receive_reorigin`, `check_origin_blind`: `pinned` and `check` read neither origin nor chain). It is
only ENUMERATED for the call's own `c.unsigned.world`: after a carry that field is the new origin,
and a `receiveWith` that recomputed an id from it (Loopback's mistake, inside the kernel) would pass
every theorem here, since both sides of `carry_receive` take the same call. Derive.lean reads
`.world` only in the World check today; the statement that closes it is cv task 01a14aa3-ca32. A lineage's first origin is not a field of the World. It is reachable only
through the chain of carry inputs (`fromOrigin`), so a consumer must carry it (PROTOCOL's
`St.lineage`, HOST's export file).
Second-agent vacuity read (before landing): LAND after two edits, both made. The first draft's
`receive_origin_blind` (an iff premise) compared nothing past the World check and was replaced by
`receive_reorigin`. `carry_receive`'s docstring overclaimed (on the old World the same call is
`wrongWorld`). The call-field gap above is the reader's finding.
**Meta-critique.** The pull toward re-keying was aesthetic: ids that "belong" to the current World.
Ids belonging to their lineage is the same property one level up, and it is the one that keeps
state carried by bytes. The enumeration was what decided it. It found one reader, and that reader
was a defect in a consumer, not a reason to re-key.
**Flag day.** None. No definition changed. Nothing re-geneses, re-emits or refuses to load.

## KERNEL-41 · The journal is the trie's third slot kind: one authenticated map, canonical by construction, pruned by a canonical `retain` (KERNEL-11, 2026-10-17; cv 01a14ac8-1db6, GATES-3's law-6 read via CODEC-30; DESIGN, not yet built)
**Defect.** The World and the carried state hold the journal as a `Std.TreeMap`, whose internal
balancing depends on insertion history. So `decode ∘ bytes` is the identity only up to
`World.Equiv`/`CarriedEquiv` (CODEC-14/22), and two `gates/refines-allow.tsv` rows excuse it. A
World also holds two map structures, one authenticated (the trie) and one not. KERNEL-23's own
alternatives list rejects "a TreeMap plus a separate index" as two structures (law 1), and its
Critique ("the journal is NOT authenticated: a phone cannot verify this txId landed") has stood
since KERNEL-30 as a noted gap, with nothing scheduled to close it.
**Decision.**
(1) `Slot D := cell id | nullifier n | tx id`, `Leaf := entry e | spent | journal (height : Nat) (turn : D)`,
and `Leaf.fits` gains `tx`/`journal`. The routing is a prefix code over the kind: cell `0·id`,
nullifier `10·id`, tx `11·id` (`slotBit`), so cell paths keep today's length and the journal is the
subtree at path `[true, true]`. `Bounds.trieDepth` goes from 257 to 258. `slotBytes`' kind byte
gains 2. `leafBytes (.journal h d) = 3 ‖ u64 h ‖ bytes d`. The order the trie lists is
cell < nullifier < tx, then id bytes. That is CODEC-29's `SlotBefore` with a three-valued kind.
(2) The `World.journal` and `Carried.journal` fields are DELETED. The trie carries the journal, so
a carry moves it with no field of its own. The reader is `World.journalAt E w k : Option (Nat × D)`
(the `tx` slot's leaf), and `World.journalList w` is the listing of the `[true, true]` subtree,
O(journal) and never O(store). `checkJournal` reads `journalAt`. `journalFits`, `JournalOk`,
`kept`, `journalForgets` and the check order are unchanged in meaning.
(3) `commit` writes `(.tx txId) ↦ .journal (h+1) (turnDigest)` into the trie after the turn's
cells and nullifiers, then prunes. The root that `chainNext` commits is computed after both steps.
`pruneJournal H` is `if H % W = 0 then retainAt [true, true] (keptLeaf H) else id`. That makes one
prune per W heights, as before.
(4) Kernel/Trie.lean gains ONE generic operation, `retainAt path q`. It walks `path`, and in the
subtree it reaches it keeps the entries satisfying `q`. Under the path, a subtree with nothing
dropped is returned as it is, with no hash. The nodes ON the path are always re-joined, which costs
about 2 hashes per prune at `[true, true]` and is counted in the prune row. A node whose children
now hold at most one key between them collapses through `join`: to empty, or to the remaining
single leaf, reusing that leaf's cached hash, since a leaf's hash does not depend on its depth.
The only leaf re-hashed is a full-depth leaf that keeps some of its several entries. So the result
is the canonical trie of the filtered contents. Theorems (Proofs/Trie, before the port): `get_retainAt` (get is
the filtered get for keys under the path, unchanged elsewhere), `canon_retainAt` (Canon is
preserved), and `retainAt_eq_build` (the result equals `build` of the filtered listing, so
history-independence carries over through `eq_of_toList_eq`). Tooth: a kernel-sim arm comparing
`retainAt` against `build` of the filtered listing on generated tries, plus a planted `join`
without collapse, which must fail `canon_retainAt` and the arm. This is the canonical erase that
CODEC-7's note asks for.
(5) `World.Equiv` and `Kernel/Proofs/Equiv.lean` are DELETED. Equivalence up to the journal's tree
shape is now `=`: the `trie` component already was, and the journal has no other shape left. Every
`*_congr` consumer takes `=`.
(6) Every journal theorem keeps its name and its content, restated over `journalAt E` and
`journalList` in place of `journal[k]?` and `journal.size`: journal_bounded, reach_journal_bounded,
admit_retains, fold_retains, fold_answers, admit_spacing, admit_twice_window, check_prune,
admit_prune_verdict, fold_journal_filter, fold_prune_check, journalOk_of_fits / journalFits_of_ok,
submit_once, derived_once, submit_forgotten, admit_journal, carry_journalOk, carry_journal_fits,
carry_fold_journal_bounded. The sim
arms stay red under the same names. New: `journalAt_frame`. Cell, nullifier, weight and value
readers are blind to `tx` slots: `Leaf.weight (.journal) = 0` and `Leaf.sumOf` adds nothing, so
`World.weight`, the value sums and `cellIds` are unchanged by a journal write or prune. That is
stated as a theorem, so it is not a convention.
**What the phone's head proof now covers.** `chainNext` commits the root after the turn, and that
root now commits the journal. A phone that trusts one head can verify `txId ↦ (h, turnDigest)` with
one inclusion proof of about log₂(3W) + 2 siblings, where today it needs up to 2W chain links.
While `journalForgets` is false it can also verify NON-admission with an exclusion proof. Today
"not admitted" is the Host's word, and a Host that lies "not admitted" makes a member sign the same
intent again under a new txId. No consumer verifies either proof yet: cv task 01a14ade-0f69
(PROTOCOL/CLIENT) filed with this decision. Cell proofs are unchanged in length. Nullifier proofs gain one sibling.
**WASTE (predicted; the instrument is KERNEL-36's counted hashes; re-pinned with the reason on
landing).**
- `hashes-per-touched-cell` 8.915: unchanged. The cell share brackets `commitTrie` without the
  nullifiers, and cell paths are unchanged.
- `hashes-per-nullifier` 3.211 → ~4.2: +1 prefix node per nullifier path. This RAISES a ceiling,
  and ceilings only fall, so it needs a ROOT ruling. It is the price of a three-kind prefix code at
  the least-used kind.
- NEW `admit hashes-per-journal-entry`, counted over the journal probe (3W+2 one-turn heights):
  about 17 for the insert (2 prefix nodes, ~log₂ 2.5W ≈ 11.3 path nodes, a split, the leaf and its
  value digest) plus about 3 amortized for the prune (the nodes above dropped leaves, once per W
  heights). Total ≈ 20.
- `journal-entries-per-window` 2.999 and `journal-scanned-per-turn` 1.998: unchanged (the same
  pass, over the subtree's listing).
- `fold work-per-turn` 2.0: unchanged.
The prune is a bounded burst of about 3000 hashes on one request every W heights. It is O(W), a
static bound, never O(store), and the follower pays the same.
**Alternatives.**
(b) A sorted-list journal: canonical by construction, but the lookup is a linear scan of up to 3W
entries on every admission. `journal-scanned-per-turn` would go from 1.998 to about 2000, which is
O(W) per request. The height-ordered variant prunes in O(dropped) but has the same lookup. Refused.
(c) Keep the TreeMap and add a canonical-listing theorem: `=` stays unprovable, the allow rows
stay, and the defect remains. Refused.
(d) `Std.ExtTreeMap`, the quotient TreeMap whose `=` is content equality (`ext_toList`). It makes
both rows plain `=` with no wire change and no hashing, so it is the cheapest. It still leaves two
maps in the World (KERNEL-23 rejected that shape) and leaves KERNEL-23's authentication gap open.
It would be the right answer only if the journal should stay unauthenticated, and no argument says
it should; cheapness is not an argument. Refused.
(e) Journal entries under nullifier slots by a domain-separated key: no routing change, but the
prune can find expired entries only by scanning the spent set, which grows forever. That is
O(store), against law 5. Refused.
(f) Erase each expired key: about W erases × ~14 path hashes per prune (~14 per turn, amortized).
`retainAt` re-hashes only the union of those paths, and no leaf (~3 per turn). Refused for
`retainAt`.
(g) Rebuild the subtree from its filtered listing (`build`): re-hashes every kept leaf and its
value digest (~7 per turn). `retainAt` is proved equal to it, and is cheaper.
**Critique.** What the port DELETES, findable here: `World.journal`, `Carried.journal`, `World.Equiv`, `Kernel/Proofs/Equiv.lean` (and CODEC's `kernel/journal` list site and both refines-allow rows). `trieDepth` 257 → 258 and the routing change alter EVERY root, so every chain and every Store changes. The phone claim, exactly: inclusion (`txId ↦ (height, turnDigest)`) always; exclusion is a proof of NON-admission only while `journalForgets` is false (past it absence says nothing, as today). ROOT ruling (2026-10-17): (a) approved; the nullifier ceiling may rise with the reason "a three-kind prefix code, paid at the least-used kind; buys plain = canonicity, one structure (law 1), and the phone's inclusion/exclusion of txIds"; the prune burst gets its own pinned row (hashes per prune); the prefix-code theorem (`slots_separate` over three kinds + `slot_prefix`, with a tooth) lands in the port commit, since the three-kind Slot exists only from the flag day (a step-1 copy would be a twin). Per-turn trie hashing rises by about 20 (roughly double for a two-cell turn), and the
follower pays it too. At about 1 µs per cSHAKE256 that is far below one fsync, but it is a real
constant, and the counted rows will show it. One ratchet ceiling rises (the nullifier row). The
proof surface grows: `retainAt`/`join` Canon proofs, a `tx`-blind lemma for every cell reader, and
a port of Journal.lean (612 lines) from TreeMap lemmas to trie lemmas. Every journal theorem now
takes `E`, because a lookup routes through `E.bytes`, which is the same as every cell reader. The
authentication benefit is LATENT until a client verifies a journal proof (gating defaults to
silence). Canonicity and law 1 carry the decision without it, but if no consumer appears the cv
task is the record. A turn's root now moves with journal churn, so two Worlds with the same cells
and different journals have different roots. That is correct, since they answer `replayed`
differently, but every root-equality test that ignored the journal now sees it.
**Meta-critique.** KERNEL-10's lead was (a), and I may be anchoring on it. I found (d) on my own,
and it pulled hard precisely because it is cheap and needs no flag day. That is the substitution
the charter names (a cost estimate becomes the constraint), so I priced it last and argued it on
law 1 and KERNEL-23. The textbook bias is real too: "everything in one authenticated state tree" is
Ethereum's receipts trie. The independent test is the standing KERNEL-23 critique, which a design
that leaves it open would have to re-justify. The prefix code favouring cells is a guess at the
kind frequencies. The counted rows check it, and if nullifiers outnumber touched cells in real
use, it is the wrong prefix.
**Flag day (one cross-layer landing).** Slot routing, the leaf bytes and `trieDepth` change, so
every root and every chain changes. The World and Carried shapes lose their journal, so the
`kernel/world` and carried tags move. Every Store re-geneses, and an old base refuses
`shapeMismatch`. CODEC (CODEC-7) re-proves `bitLt_trieSpec_iff` over the three-valued kind, adds
the `tx`/`journal` arms to `kernel/slot` and `kernel/leaf-fit` with lawfulness theorems and
vectors, deletes the `kernel/journal` list site (the decoder runs `journalFits` on
`journalList`), proves plain lawfulness in place of BOTH refines-allow rows and deletes them, and
re-pins the vectors. HOST (HOST-10) flips the base stamp, re-verifies the reopen theorems, moves
Serve's lookups to `journalAt`, and moves the carry export off the journal list. PROTOCOL
(PROTOCOL-7) moves its rows' journal reads (Loopback's carried-journal compare, Writer's
`forgetJournal` plant). Kernel's half is built first and staged as a patch on hbox, and the other
halves build on it. Because every importer must build, it lands as ONE commit.
**Step 1 as built (KERNEL-11).** Kernel/Trie.lean adds `join`, `retainAll` and `retainAt`, with no
consumer yet. Kernel/Proofs/TrieRetain.lean proves:
- `toList_join`, `retainAll_unchanged`, `toList_retainAll`;
- `canon_join` (two canonical children routed by bit `d` join canonically, including the collapse to
  one leaf or to `empty`) and `canon_retainAll`;
- `toList_retainAt` (the listing filtered in order, given that `q` drops only keys `Under` the path);
- `canon_retainAt`;
- `retainAt_eq_build` (= `build S S.depth 0` of the filtered listing);
- `get_retainAt` (`get` is the old `get` filtered by `q`).

The premise "`q` drops only keys under the path" is satisfiable. The kernel's `q` keeps every
non-`tx` slot, so it holds by `slot_prefix` (port commit). It is not provable for an arbitrary
`q`: a `q` that drops an off-path key gets no theorem. That is exactly the case the operation does
not handle.

Teeth:
- kernel-sim `probeRetain` runs every seed. It builds a trie of 0–4 tombstoned cells and 1–6 spent
  nullifiers, then runs `retainAt [true]` dropping a seed-dependent set (on some seeds, all but
  one). The arm `retain:canonical` requires the same root and the same listing as `build` of the
  filtered listing, and no dropped key readable. The arm `retain-plant:refuted` requires the
  non-collapsing plant `plantRetainAll` to reach another root on some seed.
- Mutation: `join` with no collapse arms. `Kernel.Proofs.TrieRetain` fails with 5 errors, and
  kernel-sim seeds 1–4 FAIL "retainAt … is not build of the filtered listing".

kernel-sim --seeds 64 ALL PASS. No WASTE row moves (nothing calls `retainAt` on the request path
yet). Flag day: none (new definitions, no consumer).
Second-agent vacuity read of step 1 (a2d21fe78ee402a3b): LAND. No statement is vacuous or collapsed.
The premise is the exact one, and `retainAt_eq_build` is a corollary but not a collapse: it is
false under the no-collapse mutation. The two cost sentences in (4) were corrected as the reader
asked. The sim covers path `[true]`, and the port journal probe's real prune at `[true, true]`
becomes the runtime tooth.

### KERNEL-41 AMENDED (KERNEL-11, 2026-10-17; ROOT ruled (a′) the same day): the journal is a second instance of the one trie type, and the head commits both roots
**Finding that overturned (a).** A canonical prune collapses nodes. In ONE shared trie it collapses
across kinds: when the journal side is pruned to a single leaf and the cell side is empty, that
leaf moves up to the root. From then on a cell lookup is correct only if the trie is Routed.
- I checked the bound is tight: in an unrouted trie, a misrouted key really is found after the
  collapse, so no canonical collapse avoids the premise.
- Today `get_insert` has no premise, so no cell reader after an admission has one (admit_frame,
  admit_rom, admit_nullifiers, admit_live, the Value/Weight/Ledger sums, Rooted: about 150
  theorems).
- Under (a), every one of them would gain `hw : w.Canon E`. That is discharged at Deployed, but it
  is a premise spread across the whole kernel that the journal has no right to cause.
So (a) is REJECTED for the premise spread.
**Decision (a′), replacing (1)–(3) of KERNEL-41.**
(1) `World.journal : Trie.T D (Nat × D) D`, and `Carried.journal` the same.
- The spec `journalSpec E`: bit = `byteBit (E.bytes k)`; depth 256; node hash `E.hash domTrie`;
  value digest `E.hash domJournal (nat64 h ‖ bytes d)`, where `domJournal` is a new leaf domain.
- The reader is `World.journalAt E w k := w.journal.get (journalSpec E) k`.
- `commit` inserts `(txId ↦ (h+1, turnDigest))`, then `pruneJournal H` = `retainAll (keptLeaf H)`
  at multiples of W (step 1's `retainAt` with path `[]`, whose `Under` premise is `True`).
(2) The root commitment is ONE link over both roots:
`chainNext E prev t cellsRoot′ journalRoot′ = H(domChain, prev ‖ turnDigest ‖ cellsRoot′ ‖ journalRoot′)`.
- A phone that trusts a head checks cells against `cellsRoot′`, as today; cell proofs are
  unchanged in bytes.
- It checks journal entries against `journalRoot′`. Inclusion (`txId ↦ (height, turnDigest)`)
  always; exclusion is a proof of NON-admission only while `journalForgets` is false
  (cv 01a14ade-0f69).
(3) Unchanged from KERNEL-41:
- canonicity is `=`, via `build_toList` on the journal trie, so both refines-allow rows become
  lawfulness theorems;
- `World.Equiv` and `Kernel/Proofs/Equiv.lean` are DELETED;
- every journal theorem keeps its name and content;
- WASTE: NEW `admit hashes-per-journal-entry` ≈ 15 (no prefix nodes) and a pinned prune row (hashes
  per prune, ≈ 3 per turn amortized). Both are pinned on landing.
(4) What does NOT change, against (a):
- no Slot/Leaf constructor, no routing change, `trieDepth` stays 257;
- the cell trie's root is unchanged in bytes, and `bitLt_trieSpec_iff` is untouched;
- `hashes-per-touched-cell` and `hashes-per-nullifier` are unchanged; the requested ceiling rise is
  WITHDRAWN.
(5) The premise moves to where it belongs. JournalOk absorbs `Trie.Routed (journalSpec E) 0 w.journal`.
- Genesis gives it (the trie is empty); insert (`routed_insert`) and `canon_retainAt` preserve it,
  each as a theorem.
- The journal theorems that read after a prune take JournalOk, as most already do.
- `submit_once`, `derived_once` and `admit_spacing` gain `hw₀` at the generic level; their
  deployed / reached corollaries stay premise-free (reach_*: genesis plus the fold).
**Law 1.** These are two instances of one type for two different things: the World's state, and a
pruned replay index. Nothing ties their contents together, and no invariant keeps one equal to the
other. That is not the "TreeMap plus a separate Merkle index kept equal by an invariant" that
KERNEL-23 rejected. It is one map type and one root commitment, the link.
**Critique.** The link hashes four digests instead of three, one more 32-byte block per turn
inside one cSHAKE call. A journal entry is no longer a slot of the World map, so a phone reading a
cell and a txId takes two proofs against two roots of one link. Carried keeps a journal field (now
a trie), so carry still moves two maps.
**Meta-critique.** I priced hashes, not premises. The design pass counted hash calls per turn, row
by row, and never asked what the prune's collapse does to the correctness of every OTHER reader of
the shared structure. That cost does not appear in any WASTE row. It shows up only when you try to
state `admit_frame` over the new commit. The cheaper-looking shape on paper ((a): one trie, one
root) was the more expensive one in theorems.
**Flag day (one cross-layer kernel! landing, after PROTOCOL-7's KERNEL-42 domain day).**
- The link changes (four inputs), so every chain changes.
- The World and Carried shapes change (the journal becomes a trie, rebuilt canonically from an
  ascending listing), so both tags move.
- Every Store re-geneses, and an old base refuses `shapeMismatch`.
- CODEC (CODEC-7): the journal's wire stays a strictly ascending listing, rebuilt by `build`. It
  proves plain lawfulness for World and Carried, deletes both allow rows, and re-pins the vectors.
- HOST (HOST-10): stamp, reopen theorems, Serve's reads through `journalAt`.
- PROTOCOL (PROTOCOL-7): rows' journal reads.

### KERNEL-41 PORTED (KERNEL-12, 2026-10-17): what (a′) became in code, and what it cost in premises
**Built.**
- `Journal D := Trie.T D (Nat × D) D` and `journalSpec E` (bit `byteBit (E.bytes k)`, depth
  `Bounds.journalDepth` = 256, nodes `E.hash domTrie`, leaves
  `journalDigest E e = E.hash domJournal (nat64 e.1 ‖ bytes e.2)`).
- `World.journalAt`, `World.journalRoot`, `World.roots E w := (root, journalRoot)`.
- `headLink E prev td root' jroot'`, with `chainNext E prev t (roots' : D × D)` over it; `chainOf`
  and `RootedFold` run over `(Turn, (root, jroot))`.
- `pruneJournal E H j` is `Trie.retainAt … [] j` at multiples of W. `commitJournal` inserts, then
  prunes, with ONE lazy empty digest for both (KERNEL-35's rule, per trie).
- `World.Equiv` and `Kernel/Proofs/Equiv.lean` are DELETED. `carry_inj` concludes listing equality,
  and `carry_inj_canon` concludes `=` under both journals' Canon.
**Premise spread, enumerated (the price ruled in (5)).**
- (a′) said Routed. The port takes `World.JournalCanon E w` (Trie.Canon at the root), because
  `get_retainAt` and `canon_retainAt` are stated at Canon. `JournalOk E w` = JournalCanon ∧
  heights ∧ distinct.
- These gain `hc : w.JournalCanon E` at the generic level: admit_retains, fold_retains,
  fold_answers, admit_spacing, admit_twice_window, submit_once, derived_once, check_prune,
  admit_prune_verdict, commit_filtered, fold_journal_filter, fold_prune_check, absent_final (moved
  from Fold to Journal; HOST's lookup_expired_final inherits it), commit_journal_mem, and
  admit_journaled (split from admit_journal; admit_new stays premise-free).
- journalOk_of_fits gains the canonicity premise, which CODEC's decoder supplies by `build`.
- `JournalOk` takes `E`.
- NO cell reader gained anything: the spread stops at the journal, as (a′) intended.
- Premise-free corollaries: reach_journalOk, reach_journal_bounded, reach_submit_once,
  reach_derived_once, reach_admit_spacing, reach_prune_check (from genesisWorld and a fold), and
  RootedDeployed's deployed_reach_journalOk.
- New premise on the phone's journal soundness: `0 < n`. At n = 0 the leaf bodies of `[]` and
  `[x]` are both empty, so `journalBody_inj` is false there. The cells' slot kind byte hides this
  for cells. Deployed n = 32: discharged by `decide`.
**The phone's head read** (`Kernel.Proofs.JournalHead`, deployed forms in RootedDeployed):
- `head_roots`: a head record names both roots, or a collision;
- `head_journal_read`: inclusion, whose one premise left is the claimed height < 2^64 (a u64 on the
  wire; every reached World's heights are, by `admit_height_lt`);
- `head_journal_absent`: exclusion, sound about the journal;
- `head_absent_admitted`: an admitted turn, below `notBefore + 2·windowMax`, has no exclusion proof
  against any later head but by a collision. That is "exclusion while journalForgets is false",
  stated exactly.
- `journal_prove_verifies` / `journal_prove_absent`: completeness.
**Teeth.**
- Every journal arm keeps its name.
- `journal-shadow:filtered` now also compares the reached journal's ROOT with `build` of the
  filtered never-pruned listing. Its reference is `build`, not `retainAt`, so the arm is
  independent of the code it checks.
- Mutation, prune never fires: seed 0 is red with "journal holds 3072 entries"; 8 journal arms are
  unmet.
- Mutation, retainAll without collapse (`mkNode` for `join`): journal-shadow:filtered is red by its
  root at height 3074, and retain:canonical is red on every seed.
- Both mutations were reverted. Logs: hbox logs/kernel12-mut1.log, kernel12-mut2.log.
**WASTE (kernel-sim --seeds 64, COUNTED).**
- `hashes-per-touched-cell` 8.969 and `hashes-per-nullifier` 3.336 are UNCHANGED, because the
  journal write is bracketed apart (`<J`) and subtracted from the nullifier share.
- NEW `admit hashes-per-journal-entry` 13.672, counted in the journal probe at the window's steady
  state (up to 3·W entries; `<K`).
- NEW `admit hashes-per-prune` 539.333 (`<R`; 3 prunes over 3·W+2 heights), ≈ 0.53 per turn
  amortized.
- Together ≈ 14.2 per turn against (a′)'s ≈ 15.
**Critique.**
- The journal row is measured on seed 0's one-turn-per-height probe, not on the generated runs: their
  journals hold ≲ 120 entries and read 8.0, which is the draw, not the steady state.
- The two tries share `domTrie` for nodes. A journal root and a cells root are told apart by their
  position in the link, not by the hash domain. Every soundness theorem is per root, so nothing
  rests on more, but a domain per trie would cost nothing.
- `World` keeps `[Ord D]`: `checkShape`'s `firstDup` still uses it. The structure no longer needs
  it, and dropping it touches every layer's `variable` lines: left for a quieter day, not done.
**Meta-critique.** The (a′) text said "Routed". I built against what the trie's theorems state
(Canon), not what the design prose said. That is one more conjunct, and it was invisible from the
ruling. A design that names a premise should name it at the granularity the lemmas it cites
actually take.

## KERNEL-42 · Every message a member key signs begins with its own domain: a call's signature is over `callMessage = domCall ‖ unsignedBytes` (PROTOCOL-7 for KERNEL-11, 2026-10-17; CODEC-6's finding, ROOT ruling)
**Decision.** `Receive.domCall` ("nanodregg/kernel/call-signature") and `Ctx.callMessage X u := domCall ++ X.unsignedBytes u`.
- `checkSignature` (Derive) verifies `callMessage`.
- Every signer signs it: Sim/Gen's `signed`, Ops' founder calls, and Protocol's command machine for both `sign` and `signNext`, where planMoved compares callMessage.
- `unsignedBytes`, the call codec, txId and every tag are unchanged.
- `receiveWith_sealed` and `receive_ok` keep their conclusions over the new message term.
- `Protocol.Proofs.Domains` proves the four signed shapes pairwise disjoint (call, possession, envelope, whoami: six pairs), whatever follows each domain, with no hash premise.

**Why.** Before this, a call's signed bytes began with the World digest. A signature over them could equal one over a read envelope (35 ASCII domain bytes) only if an origin matched those bytes, so the separation held only up to cSHAKE256 preimage resistance. That is a cross-protocol signature confusion by construction, under one key. It became load-bearing when ROOT ruled an envelope-only custody for observer keys (HOSTING-17 §7).

**Teeth.**
- kernel-sim arm `sig-bare:badSignature`: the same fresh call signed over its bare unsigned bytes is refused at Derive's verify. Its domain-signed twin is not submitted again, since every call the generator signs is that twin and an extra admission would move the WASTE hash counts; `carry-new:ok` is the nearest.
- Each of the six pair theorems fails to build when one domain is mutated to share the other's byte at the compared index (a scratch run of six mutants, six errors).

**Critique.**
- The domains share the prefix `nanodregg/`, and disjointness rests on ONE byte per pair (index 10, 17 or 19). That is exact, but a new signed shape must pick a domain differing from all four at a byte both hold, and nothing forces a new shape to be added to the theorem set.
- The census does not know "a member key signs this", so a fifth shape, an unprefixed one, would be invisible until someone reads the signers.

**Meta-critique.** The call message was left bare because the envelope came later and added its own domain, a familiar pattern: the newer protocol is careful, and the older one is assumed safe because it was first.

**Flag day.** Every signed call changes, and so does every rotation (signNext). No codec, tag or vector moves. Rows and kernel-sim re-run, and every Store re-geneses, because a log of old-signed calls re-verifies `badSignature` on replay and at audit.

## KERNEL-43 · What bounds the allowance is storage PLUS allowance: genesis, carry and the World codec check the sum, and every reached World keeps it below 2^64 (KERNEL-13, 2026-10-18; cv 01a14ba9-cbf4, HOST-11's proof lane, ROOT ruling)
**Defect.** `commit` sets `allowance := allowance + credit − charge`, and a retirement credits the retired cell's whole weight. `GenesisFits` and `CarryFits` bounded only `allowance < 2^64`. So `host import` of a carried file with allowance 2^64 − 1 beside a heavy live cell, followed by one light turn retiring that cell, left the allowance at 2^64 or past it. That is outside the World codec's `u64`: the next seal writes a base that does not read back, and export refuses. kernel-sim measured it at the deployed parameters: arm `carry-budget-plant:overflow` builds that carry unchecked (`carryWorld`) and reaches the overflow with one forged retire on every seed. `host genesis` was safe, since `allowanceMax` is 2^27.

**Decision.**
- `GenesisFits`: `(genesisWorld …).weight + allowance < 2^64`, refused `allowanceTooLarge`. It is the LAST clause and the last check (its constructor moved to the end), so the World is weighed only after every founder is within bounds.
- `CarryFits`: `cellsWeight c.trie + c.allowance < 2^64`, refused `allowanceTooLarge`.
- CODEC's `World.CodecFits`: `w.weight + w.allowance < 2^64`. The World refine, renamed `kernel/world` → `kernel/world-budget` (its tag moves), refuses a World whose sum is over, by name.
- In each, the sum REPLACES the old allowance-only clause, which it implies. There is one clause, not two.
- `Kernel.Proofs.Budget`:
  - `fold_budget_lt` (from `fold_conserves`), `genesis_budget`, `carry_budget`, `genesis_fold_budget_lt` (no premise);
  - `carry_fold_budget_lt` (premises: the carried trie Canon and Slotted, which the carried codec gives on import);
  - `deployed_budget_lt`: every World reached from a genesis, or from a carry of a World a genesis reached, with no premise.
- HOST's `Kept` gains the sum, kept by `admit_conserves`, so `openWith_exportFile_ok` loses `hallow` and has no premise.

**Teeth.**
- kernel-sim, in plantedArms:
  - `carry-budget:allowanceTooLarge`: the crafted carry is refused;
  - `carry-budget-edge:ok`: at sum 2^64 − 1 the carry is admitted, at least one light retire on it is admitted, and every one stays below 2^64 (the "stays below" half is `admit_conserves` of the same code and cannot go red alone; the arm's tooth is the boundary admission);
  - `carry-budget-plant:overflow`: the unchecked carry overflows, so the probe fails unless the defect is real at these parameters.
- Mutation (checkCarry back to allowance-only): 64/64 seeds FAIL with `probe carry-budget: an allowance of 2^64 - 1 beside live cells was carried`.
- Codec vectors `kernel/world-budget` 2 and 3: a World at sum exactly 2^64 − 1 reads back, and the same World one past it is `refused … "kernel/world-budget"`, though every counter in it fits its `u64`.
- `Codec.Kernel.world_decode_wire_overBudget` states the refusal for every wire value.

**Critique.**
- `checkGenesis` builds the genesis World to weigh it, and `genesis` builds it again to return it. That is O(founders) hashing, once per World, and it is named, not hidden. The alternative was a founder-weight formula proved ≥ the built World's weight: a second shape of one number.
- `allowanceTooLarge` now means "the allowance is too large for this storage". The meaning widened under the same wire name. A new name (`budgetTooLarge`) would have been more exact, at the cost of a new name in every refusal table, for a clause that replaced the old one.
- The first draft kept the `kernel/world` tag, calling the change "a narrowing, not a relabel", and planned that nothing would re-genesis. The vectors gate refused it: the two boundary vectors were "added under its unchanged tag". The gate was right. Bytes that decoded `ok` now decode `refused`, a change of meaning under the same bytes, and CODEC-28's rule is that this bumps the label. So the refinement was renamed `kernel/world-budget` and every Store re-geneses. That sentence is the gate earning its keep.
- The decoder now computes `cellsWeight`: O(store) on a base read, which is already O(store).
- The kernel's deployed theorem covers the lineage carry. The import of an arbitrary file reaches the bound through HOST's `Kept`, from the carried codec's canonicity. `checkCarry` itself does not check Canon, because the codec does.

- Second-agent vacuity read (read-only reviewer): LAND on every theorem and arm. Its two findings are taken: the genesis budget check moved after the founder checks, and the edge arm now requires an admitted retire.

**Meta-critique.** Every Fits predicate was written from the CODEC's shape: one `u64`, one clause, `x < 2^64`. The dynamics need a SUM, and nothing derived the bounds from what admission does to the fields. The same reading should be run on every counter admission moves. `height` is covered: one per turn, and `admit_height_lt` checks it. `charge` is checked per turn.

**Flag day (`kernel!`).**
- Statements change: `GenesisFits`, `CarryFits` and `World.CodecFits`, one clause each, replaced. `GenesisRefusal.allowanceTooLarge` moves last.
- The World refine is renamed `kernel/world-budget`. Its tag moves, and so does every tag that embeds the World codec (`host/base/index-count`). Re-emitted: their codec vectors, with the boundary pair.
- Refuses to load: every old Store base (its stamp names the old shape: `shapeMismatch`). Every Store re-geneses.
- Also refused: a genesis or carry whose storage plus allowance is ≥ 2^64 (`allowanceTooLarge`), and a base World whose sum is ≥ 2^64 (`kernel/world-budget`).
- WASTE rows unchanged.

## KERNEL-44 PROPOSED · A refusal is a recorded system interaction, bounded per member per window; replay is bounded by a checkpoint rule (KERNEL-13, 2026-10-18; Ember's call (8) of 10-17: "they WERE system interactions", "the amount of replay is too damn high"). DESIGN ONLY until ROOT rules; the HOST half is for HOST-12.

### Part 1 · Refusals

**Today.** A refused frame is answered `refused NAME` and leaves no trace: not in the log, the World, the journal or the chain (`Host.Serve.handle`, every `.error r => refuse (named r.name)`). A lost reply makes a later `lookup` of that call answer `absent`. A resubmit is derived AGAIN against a moved World. Because the call's pins fix its view and a pin can return to an old value (a write A→B→A), the same call can later be ADMITTED, after the client's attempt store has ended it REFUSED. That is a false final verdict. The refusal is a system interaction the system forgot, and the forgetting is a correctness gap, not just a missing feature.

**Two classes, split at the line the kernel already draws** (`receive` = `wrongWorld` → `checkSignature` → `keyRule` → derive → `World.admit`):
- **(U) unauthenticated.** The frame is refused before a live member's key verified the call: `undecodableCall`, `unknownOp`, `wrongWorld`, `badSignature`, `unknownKey`, and `unpinned` at the key read. No member can be charged, so it is answered and NOT stored. Its cost to the host is a decode plus at most one signature verify, the same as today, and nothing persists. A client can recompute every (U) verdict itself (decode, the World digest, the signature and the key it signed with), so a host attestation would add nothing a client cannot check.
- **(A) authenticated.** Every refusal after `keyRule` passed: a derive refusal (`noGrant`, `grantRight`, `lawDenied`, `callTooDeep`, …) or an admit refusal (`stale`, `outsideWindow`, `overBound`, `notConserved`, `spent`, …). The member's current key signed exactly this call, so the refusal is charged to that member and RECORDED.

**The record (the kernel's).**
- A third instance of the one trie type: `World.refusals : Trie.T D D RefusalLeaf D`, under `refusalSpec E`.
  - Leaf `refused h code` sits at key `txId`: refused at height `h`, `code` its refusal's index.
  - Leaf `count win n` sits at key `H(domRefusalCount ‖ member ‖ u64 win)`.
  - Both key kinds are digests from disjoint hash domains, so no prefix code is needed. The cross-kind collapse that sank KERNEL-41 (a) does not arise, because every reader of this trie already takes its Canon, as journal readers do.
- `recordRefusal` runs ONLY on (A):
  - Refused `refusalBudget` (by name) when the member's count for window `win = h / W` has reached `Bounds.refusalsPerWindow` (proposed 16). The call is then answered like (U), unstored.
  - Otherwise it inserts `refused` and bumps `count`.
- Pruned with the journal, by the same `retainAt` at multiples of W: `refused h _` is kept while `h + 2W > H` (KERNEL-33's kept rule), and `count win _` while `win = H / W`.
- Bounded: at most members × refusalsPerWindow × 3 live `refused` leaves. A member cannot exceed its slots; a non-member pays nothing and stores nothing.

**Finality (the semantic change, the point of the record).**
- `submit` of a txId found `refused h code` answers `refused NAME` WITHOUT re-deriving. This is the twin of `replayed`, and makes a recorded refusal final for that txId within the window.
- `lookup` answers:
  - `refused NAME` (status `refused`, payload the name) while the record is kept;
  - `uncertain forgotten` past `journalForgets`, the PROTOCOL-33 row shape unchanged;
  - `absent` / `expired` as today for a txId never seen.
- PROTOCOL-33's rule holds: past the window, nothing is answered `refused` that could have committed. A refused record and an admitted entry for one txId cannot both exist: a txId is admitted at most once (`submit_once`), and a recorded refusal short-circuits every later submit.

**The receipt.** For (A), the receipt is the record's inclusion proof against the head, by the same machinery as the journal (KERNEL-41's `head_journal_read`). No host signing key is needed.
- A host-SIGNED receipt for every refusal (the brief's sketch) needs a host identity key. That is custody (pause list 1) and → Ember. It buys nothing for (U), which the client recomputes, and nothing for (A), which the chain proves.
- So the proposal is NO host key. (U) replies stay unsigned and are flagged in the wire doc as recomputable.

**Commitment and replay.**
- The batch record gains the (A) refusals of the batch, as `(call bytes, code)` in arrival order.
- A follower re-derives each one: `receive` on the World where it arrived must refuse with the same code. This is an `auditRefusal` step, so a host that invents a refusal is caught exactly as one that invents a turn.
- A refusal does NOT advance `height`. Windows are in heights, so refusals cannot shorten anyone's window. That is the DoS argument for heights.
- The chain does advance. The head link gains a refusals root, `chainNext E prev t (cellsRoot′, journalRoot′, refusalRoot′)`, and a refusal step links by its own domain-separated `refusalLink prev callDigest refusalRoot′`.

**DoS argument.**
- (U) costs the host one decode plus one verify and zero bytes stored, as today.
- (A) costs a live member one of `refusalsPerWindow` slots per window. A record is ≤ `Bounds.callBytesMax` log bytes plus one trie insert (≈14 hashes, KERNEL-41's journal row).
- A flooding member burns its own slots and then degrades to (U) treatment. Other members are untouched.
- WASTE rows, pinned:
  - `admit hashes-per-refusal`, with a cap; the insert plus the count bump is ≈ 2 × 14;
  - `log bytes-per-refusal`;
  - `refusals-kept-per-member-window` ≤ 16;
  - a plant: a 17th authenticated refusal in one window is `refusalBudget` and is not stored.

**Price, in premises on landed theorems (the KERNEL-41 lesson; counts from grep at f1c5f01).**
- `World.fold` today folds `List (Turn D)`. With refusal steps it folds `List (Step D)` (`turn t | refusal c code`).
  - This is the expensive part: ~109 statement lines in 35 files name `World.fold`. Every one changes STATEMENT, though not premise: a fold over steps whose refusal steps are no-ops on cells and journal.
  - `fold_conserves`, `fold_canon`, `fold_slotted`, `fold_journalOk`, `fold_budget_lt` and `fold_answers` each gain one trivial case: a refusal step touches only `refusals` and `chain`.
  - `fold_reaches_host` / `fold_head_binds` / `chain_binds` gain the refusal-link case and a Collision disjunct for `refusalLink` vs `chainNext`. The domains are disjoint, so this is a domain-disjointness lemma, no new hash premise.
- `submit_once`, `derived_once`, `admit_spacing`: unchanged in statement. A refused record is not an admission.
  - NEW `submit_refused_final`: a recorded `refused` answers every resubmit of that txId within the window.
  - Its tooth is the A→B→A arm: the same stale call, resubmitted after the pin returns, is answered `refused stale`, never admitted.
- `lookup_expired_final` / `absent_final` (HOST): their "not journaled" premise becomes "neither journaled nor refused-recorded". One more conjunct, discharged by the same reached-World facts.
- Codec: a `kernel/refusal-order` trie listing, a `refusals` field in the World and carried wires (tags move: a re-genesis), and the batch record's refusal list.
- No cell reader gains a premise. `RefusalsCanon` falls only on refusal readers, as `JournalCanon` does.
- Alternative (A′), cheaper and refused here: a HOST-local `refusals.log` (MAC'd, pruned by window), consulted by lookup/submit, outside the World and the chain.
  - It costs no kernel theorem, gives the same finality on the writer, and survives a restart.
  - But it is unprovable to a phone or a follower, a host can forge or drop it undetected, and a backup without it silently loses finality.
  - It is the containment pattern CLAUDE.md names: the right shape is (A), with its price stated.

**Carry.** A carry carries NOTHING of `refusals`.
- Finality of a refusal is a window-scoped promise, the window is the World's, and a carry starts a new World under a new origin.
- A call refused in the old World is `wrongWorld` in the new one (KERNEL-24) anyway, so the record could never be consulted there.
- Carrying it would add a third trie to the carried codec for zero answers. `carry_replayed` (journaled calls answered) stays: an admitted call's receipt IS consulted across the carry, because it committed.

### Part 2 · Replay and checkpoints

**What already bounds replay:**
- The writer's open reads ONE sealed base, its last index entry and at most `tailMax = 2·cadence + frameMax` bytes of tail (`Host.Proofs.Base.openWith_reads`). Restart replay is bounded by the cadence, not by history.
- A member's follower reopens its own Store the same way.
- Thin consent (HOST-15, PROTOCOL-14 option A) catches up from a served base plus the tail.
- The journal is pruned to the window (KERNEL-33).

**What remains unbounded (all O(history), all reading seg.log/index.log, which are never pruned):**
- `host check` reads the whole segment from the origin frame (`historyClean`) and every index entry (`indexClean`).
- A backup copies the whole segment and index (`Store.backupOrder`).
- A NEW follower that audits from genesis pages and folds every record since height 0 (`log` from `start` = 0; `host follow`'s `Receive.audit`).
- Disk: seg.log + index.log grow by every batch forever.
Ember's "too damn high" is these four.

**The checkpoint rule.**
- A base IS a checkpoint. A Store keeps the newest `Bounds.retainBases` (proposed 4) sealed bases' worth of segment.
- Retention bound: segment bytes before the oldest retained base are DROPPED. The segment becomes a sequence of files `seg.<k>.log`, one per sealed base, each beginning with a `checkpoint` frame. Its record is the base's position triple `(height, chain, base digest)`, MAC'd, chaining from the previous file's last tag.
- `host check` verifies only what remains: the oldest retained file's checkpoint frame, then forward. It reports `retained_from=H`.
- A follower or backup older than the retention bound gets `log` refused `checkpointed H` (by name) and must start from a served base ≥ H.

**What the chain still binds.**
- Every head commits its predecessor (`chainNext`), so the retained suffix's first chain value binds the dropped prefix.
- Anyone who kept the dropped segment can prove it against the retained chain, and the origin frame's genesis chain still binds the lineage. A copy of the dropped prefix is checkable, not trusted.
- What is LOST is the ability of a fresh party to re-derive the dropped prefix from THIS Store. A follower starting from a checkpoint trusts that the base's World is the fold of what it no longer sees.
- That is the real price, named: auditability from genesis becomes "auditability from the oldest retained base, unless someone archived the prefix". (An archive role, the hosted follower keeping everything, recovers it. That is an OPS decision, not a kernel one.)

**Price in landed theorems.**
- `fold_reaches_host`: unchanged in statement. It is over a fold from `g`, so a follower starting from a checkpoint instantiates `g` := the checkpoint's World and needs `World.Rooted` facts of it. The reached-World theorems (`deployed_*`) then need a NEW "a base World is reached" premise, discharged by the base being sealed from a folded World on THIS writer, plus the MAC. For a received base it is NOT discharged: that is the trust above, stated as a premise (`CheckpointTrusted`).
- The backup theorems (`openWith_backup`, `openWith_cut`, `openWith_backup_restart`): restated over the file sequence, with the origin frame replaced by the oldest retained checkpoint frame. `historyClean` becomes "clean from the oldest checkpoint".
- The carry: unchanged. A carry already starts from one World with no history, which is the same move as a checkpoint, made by hand.
- Refuses by name: `log` before the retained range (`checkpointed H`); `host check` of a Store whose oldest checkpoint frame fails its MAC (`checkpointCorrupt`); open of a Store missing a retained file (`storeMissing`, HOST-35's shape).

**HOST half (for HOST-12, after ROOT rules).** Build `seg.<k>.log` rotation at seal and the retention drop:
- the drop is a `rename` to `dropped/`, then an unlink only after the next seal is durable;
- the checkpoint frame, `historyClean` from it, and `log`'s `checkpointed` refusal;
- the refusal record in the batch, and the refusal steps in the open's fold;
- lookup/submit consulting `refusals`.

**Critique.**
- (A) makes the World carry a third trie and every head commit a third root, for a feature whose only reader is lookup and finality. (A′) is a tenth of the cost. The argument for (A) is that a refusal you cannot prove is not a recorded interaction, and Ember's word was "recorded".
- `refusalsPerWindow` is a taste number. 16 per member per 1024 heights is generous for honest clients and makes a flood cost 16 records per member per window.
- Making refusals final per txId changes what a client may do after `refused stale`. It must re-sign (a new txId), which it already must, because the old pins are wrong.
- The checkpoint rule changes "a follower can audit from genesis" from a property of every Store into a property of an archive. That is a weakening of what a backup proves, and it is pause item 2 (weakens a check). Ember's call (8) asks for it explicitly, but ROOT should rule it as the weakening it is.

**Meta-critique.** Both parts are about forgetting. The system already forgets admitted calls on a schedule (the window) and remembers that it forgot (`forgotten`). Refusals were forgotten with no schedule and no memory of forgetting, and history was never forgotten at all. The design gives the three one rule: remember for the window, then say `forgotten`.

**Flag day (if built).** World, carried and batch codecs move tags; every Store re-geneses; the head link gains a root; the phone's journal proofs gain a sibling for refusals.

## KERNEL-45 PROPOSED · A Turn is the hyperedge for ONE signer; multi-signer and cross-World joint turns are DEFERRED with triggers (KERNEL-13, 2026-10-18; ROOT, from MINI-CONCEPTS-IN-NANO-20261018.md §4 and its closing half-page). Decision only; no code.

**What nano has.** Mini's hyperedge ("a single-cell action is ι = 1, a transfer ι = 2, an N-party joint turn ι = N") survives in nano for one signer:
- A Turn names many cells (`touches`, each pinned by `seen`), plus `creates` and `nullifiers`, all admitted atomically by `World.admit`.
- `balanced` is LEDGER's `checkValue` (`notConserved`).
- The invoke call tree (LANG-21/23/33) visits each object once, runs every visited object's laws, and seals ONE Turn, so the tree commits or fails whole.

**What was lost by omission, now decided:**
1. **A Turn is the hyperedge for one signer.** This is the kernel's turn model, stated: one `Call`, one member, one key, one signature (KERNEL-42's `callMessage`); any number of cells, atomic.
2. **Multi-signer atomic turns: DEFERRED.**
   - Trigger: the first row where two members must exchange value in one turn (A's asset for B's, atomically), where escrow plus two turns is not acceptable to that row's owner.
   - The price when triggered, from the report's §4(4) (theorem names read, counts not measured):
     - `Call` carries a list of `(member, key, signature)` over one `callMessage`;
     - `receive` checks each signer, and authority becomes "the signer who owns that cell";
     - `receive_ok`'s signed clause and `write_authorized` / `invoke_authorized` / `enroll_authorized` gain a signer index;
     - PROTOCOL-39's disjoint signed shapes gain one;
     - `stale_refused`, `admit_value` and the frame theorems are untouched (`World.admit` never sees signers);
     - CLIENT gains co-signature assembly (new protocol);
     - the call codec and every Store re-genesis.
   - Today's substitute: `Std.quorum` (sequential, not atomic) and the escrow.
3. **Joint laws across objects** (Mini's ObjectiveDomain): DEFERRED with the same trigger class: the first row whose invariant spans two objects changed in one turn. Price: a separate judge (as LANG-44's row guards are), so the 85 law theorems in Lang/Proofs/Receiver.lean keep their statements.
4. **Cross-World joint turns: DEFERRED behind "a second writer for one World".** KERNEL-24's `wrongWorld`, the FIRST check, stands: a call names one World. A joint turn across Worlds is agreement machinery, and nano has one writer per Store by charter.

**Critique.** A deferral with a trigger is only as good as the trigger's detector. Nothing in the gates notices "two members needed one turn". The detector is the row author choosing escrow, so every escrow row's decision entry should say whether it would have preferred one turn.
**Meta-critique.** The omission happened because nano was rebuilt from a charter of laws, and no law spoke about signers per turn. A rebuild inherits the old system's decisions only where someone re-decides them.

## KERNEL-46 · LANG-44's kernel half, CO-SIGNED with five amendments, and LANG-45's (ii) capped sum ACCEPTED into it (KERNEL-13, 2026-10-18; LANG-44 items 6–11 and (c), as ROOT approved them; LANG-45 (ii) for ROOT's ruling). Design; the kernel half is built after KERNEL-44's refusals day.

**Co-signed as written:**
- the rows as a third instance of the one trie (the (a′) pattern);
- `Turn.rows : List (RowTouch D)` with an exact pin or an unpinned birth;
- `keyTaken` / `relationFull` judged on the current World and binding;
- `upsert`/`retract` must pin;
- the parent touched (`rowParentUnpinned`) and live (`orphanRow`);
- `rowsRemain` on a parent's retire;
- retract REMOVES via `retainAt` (no tombstone: a relation forgets, storage is bounded by `limit`);
- row bytes are growth and weight;
- `RowsCanon` on rows readers only;
- `stale_refused` keeps its exact statement for cell pins, with a NEW sibling `rows_stale_refused` for row pins, the same conclusion;
- head born with the parent. Born-at-first-insert would make the insert carry `limit`/`width`, which is signer-supplied data the kernel would have to trust or re-check against a package, a Lang fact inside admission.

**Amendments (each a change to the LANG-44 text; argued):**
1. **The key encodes its own length:** `bytes parent ‖ u8 rel ‖ u8 tag ‖ u8 |k| ‖ k`.
   - LANG-44 says "width is fixed per relation (the head records it), so the key set is prefix-free with no World invariant". It is not.
   - The trie routes by bits up to a fixed depth. A row key `p‖r‖1‖a` and a longer `p‖r‖1‖a‖00…` route identically, so `Separates rowSpec` would hold only on Worlds where every row's width matches its head's: a World invariant that every rows theorem would carry as a premise.
   - With the length byte the encoding is injective and prefix-free by itself, and `rows_separate` is proved unconditionally, as `slots_separate` and `journal_separate` are.
   - Admission still refuses a key whose width differs from its head's (`keyWidth`), as a RULE, not as something a proof leans on.
   - Depth: 256 + 24 + 8·keyBytesMax.
2. **The heads are birthed by an act, not by `creates`:** `RowAct.declare (limit cap width : Nat) (retract : Bool)` with `seen = none`.
   - It is allowed only in the turn whose `creates` bears the parent (`declareLate` otherwise), and only by the create receiver.
   - `Turn.creates : List (D × Cell)` keeps its shape, and every theorem over `creates` keeps its statement.
3. **The head is never pinned by an insert, and that is a theorem.**
   - `admit_comm` cannot be "disjoint footprints" plain, because two inserts under one relation BOTH write the head (count, and with (ii) sum). The head update is ADDITIVE, and that is the commutation.
   - Statement: for t₁, t₂ admissible from w whose footprints are disjoint OUTSIDE heads, and whose head updates fit together (count₁+count₂ within `limit`, sum within `cap`), BOTH orders admit, and they reach equal cells and rows tries. The conclusion includes admission in both orders, not only equality-if-both-admit: the weaker form is true of a design that refuses the second order.
   - Plant: an insert that pins its head makes the second rain `stale`.
4. **One `Roots` digest in the head link.** KERNEL-44 adds `refusals` and this adds `rows`, so the link's arity would change twice.
   - Instead, `headLink E prev td rootsDigest` with `rootsDigest = H(domRoots ‖ cellsRoot ‖ journalRoot ‖ rowsRoot ‖ refusalsRoot)`.
   - The phone proves one extra hash, and a fifth trie changes `World.roots` and nothing in the chain lemmas.
   - KERNEL-44's day introduces it with three roots; this day adds `rows` to `World.roots`.
5. **The world's weight counts rows.** `World.weight = cellsWeight trie + rowsWeight rows`, so KERNEL-43's `weight + allowance < 2^64` covers them by `fold_conserves` with no new clause. CODEC's budget refine reads both, with the tag moved in this day.

**LANG-45 (ii), the capped sum: ACCEPTED as one head field, not a second rule.**
- The head is `head (count sum limit cap width : Nat) (retract : Bool)`. A row leaf is `row (amt : Nat) (val : ByteArray)`.
- `amt` is a KERNEL field beside the bytes: the kernel never parses Lang data. Lang guarantees `amt` = the declared column, by `rows_of_pins` / `editsOf`'s round trip.
- insert/upsert/retract move `sum` by +amt / (new − old) / −amt. `relationCapped` refuses on the CURRENT sum, binding like `relationFull`.
- Theorems:
  - `head_sum`: on every reached World, each head's `sum` = Σ `amt` over its rows and `count` = their number. This makes "only the kernel writes the head" a checkable fact rather than a prose rule.
  - `sum_le_cap`.
- A relation without a sum column declares `cap = 0` and `amt = 0` on every row.
- (i), an `Act.add` against a pin that masks a slot, stays REFUSED: it weakens a pin.

**Signatures (proposed; LANG writes against these, KERNEL commits them in the rows day):**
```lean
structure RowKey (D : Type) where parent : D; rel : Nat; k : ByteArray        -- rel < 256, k.size ≤ keyBytesMax
inductive RowSlot (D : Type) | head (parent : D) (rel : Nat) | row (key : RowKey D)
inductive RowLeaf | head (count sum limit cap width : Nat) (retract : Bool) | row (amt : Nat) (val : ByteArray)
abbrev Rows (D : Type) := Trie.T D (RowSlot D) RowLeaf D   -- (K V D order as Trie.T's)
def rowSpec (E : Env D) : Trie.Spec (RowSlot D) RowLeaf D  -- bit over parent ‖ rel ‖ tag ‖ u8 |k| ‖ k
inductive RowAct | keep | insert (amt : Nat) (v : ByteArray) | upsert (amt : Nat) (v : ByteArray) | retract
               | declare (limit cap width : Nat) (retract : Bool)
structure RowTouch (D : Type) where slot : RowSlot D; seen : Option D; act : RowAct
-- Turn gains  rows : List (RowTouch D);  World gains  rows : Rows D;  World.admit E w t keeps its type
def World.rowAt (E : Env D) (w : World D) (s : RowSlot D) : Option RowLeaf
def rowPin (E : Env D) : Option RowLeaf → D                -- the leaf digest, or the absent pin
-- Reject gains: keyTaken relationFull relationCapped rowParentUnpinned orphanRow rowsRemain keyWidth
--               noRelation retractForbidden declareLate
```
- Lang's methods return edits.
- The receiver turns each edit into a `RowTouch` with `seen := the signer's row pin` for upsert and retract, and `none` for insert.
- `declare` touches come only from the create receiver, one per `RelDecl`.

**Critique.**
- A rows day after KERNEL-44's means two flag days of the same shape (a new trie, a new root, a new carried listing). The `Roots` digest makes the second cheaper but not free.
- `amt` duplicates a value Lang also holds in `val`. The duplication is the price of a kernel that never parses Lang data, and `editsOf`'s round trip is the check that keeps the two equal. A Lang bug would show as a sum that disagrees with the rows' decoded columns, which a sim arm should recompute.
- With no tombstone a key can be re-inserted after a retract, so a row pin can see A→retract→A. That is the same content-addressed-pin behaviour cells have, and it is not new.

**Meta-critique.** LANG-44's "no World invariant" was believed because the precedent (the journal) has fixed-width keys. The check that caught it was asking what `Separates` needs, not whether the shape matches a landed one.

## KERNEL-47 · KERNEL-44's refusals as built: ONE fold over steps, a step counter, and seven amendments to the proposal (KERNEL-14, 2026-10-18; ROOT's question "World.fold over Step vs a second fold", settled before building)

**The question.** A recorded refusal changes the World (its refusals trie, its chain) without being a Turn. Either `World.fold` folds `List (Step D)` with `Step D := turn t | refusal r`, or `World.fold : List (Turn D)` stays and a `World.foldSteps` sits beside it.

**Chosen: ONE fold over steps.** `World.step E w : Step D → Except (Reject D) (World D)` (`.turn t` is `World.admit`, `.refusal r` is `World.refuse`); `World.fold` folds `List (Step D)`; `World.RootedFold` is the generic `Rooted` over `World.step` (its definition is already generic in the transition).

**Why not a second fold.**
- Law 1 ("one of everything; one admission path") forbids it in words.
- A theorem over a turn-only fold never matches a real run once one refusal is logged: the host's open, the follower's audit, the backups and `fold_reaches_host` all fold the REAL log. Every reached-World theorem would have to be restated over `foldSteps` anyway, and the turn-only theorems would survive as a special case nothing deployed instantiates: the vacuity reader's "never matches a real run".
- A projection lemma ("foldSteps of l reaches what fold of turns l reaches, refusals and chain erased") fails on the chain: every turn link commits the roots digest, which now includes the refusals root. Erasing it changes every later link.
- The churn of the one-fold choice is mechanical and premise-free: measured at 7679aac, `World.fold` is named on 149 lines in 35 files. Every one changes `List (Turn D)` to `List (Step D)`; none gains a premise; each induction gains one `refuse_*` case.

**Amendment 1 · a step counter, `World.steps`.** `chain_binds` needs the two logs to have equal length; today equal HEIGHT gives that. Refusals do not advance height (the DoS argument), so equal height no longer gives equal step counts, and a shorter log's chain equal to a longer one's is a hash CYCLE, not a `Collision`.
- So the World gains `steps : Nat` (every step, turn or refusal, adds one; every step is refused `overBound .counter` past `counterLimit`: `checkSteps`, LAST in `check` so no admit-refusal-naming theorem gains a premise, and SECOND in `checkRefusal` (after its bounds; no theorem names a `checkRefusal` error today, so none gains a premise; a later one must place it); tooth `checkSteps_refuses` / `admit_refused_at_step_ceiling` / `refuse_refused_at_step_ceiling`; `step_steps_lt` / `fold_steps_lt`; a carry starts it at the carried height, so `height ≤ steps` everywhere).
- `fold_head_binds`, `fold_reaches_host` and `deployed_fold_reaches_host`: the premise `follower.height = host.height` is REPLACED by `follower.steps = host.steps`. Replaced, not added. HOST's follower compares (steps, chain) where it compared (height, chain).
- `fold_height` becomes `w'.height = w.height + (Step.turns l).length`; new `fold_steps`: `w'.steps = w.steps + l.length`.

**Amendment 2 · one chain domain, a tag byte.** KERNEL-44 proposed a refusal link in its own domain. `Collision` is a same-domain collision; a turn link equal to a refusal link across two domains is not one, so `chain_binds` would gain a domain-separation premise. Instead both links are `domChain` with a tag byte first (`0` turn, `1` refusal), as `domLeaf` already does for leaf kinds: `headLink E prev tag d rootsDigest`. `chain_binds` keeps `Collision` as its only escape.

**Amendment 3 · the `Roots` digest (KERNEL-46 amendment 4) arrives now.** `rootsDigest = H(domRoots ‖ cellsRoot ‖ journalRoot ‖ refusalsRoot)`; the rows day adds one field. `World.roots` is that digest; every `RootedFold` note is one digest.

**Amendment 4 · the refusals trie's key needs no hash.** KERNEL-44 keyed counts by `H(domRefusalCount ‖ member ‖ win)` beside txIds and called the two "disjoint hash domains". A txId equal to a count key is a cross-domain equality, not a `Collision`, so `refusals_separate` would carry a premise. Instead `RefusalSlot D := tx (id : D) | count (member : D) (win : Nat)`, routed by a kind bit then the raw bytes (`count`: the member's 32 bytes, then `u64 win`). Fixed width per kind, so prefix-free by construction; `refusals_separate` is unconditional, as `slots_separate` is; and recording costs no key hash. Depth 1 + 256 + 64.

**Amendment 5 · only an IN-WINDOW refusal is recorded (a defect in KERNEL-44 as proposed AND as ROOT approved it).**
- As proposed, an early call (notBefore > H + 1, refused `outsideWindow`) would be recorded at h and pruned at h + 2W, while its window may open later (notBefore is bounded only by `counterLimit`). That is a final verdict later admitted, the A→B→A class again.
- Rule: a refusal is recorded iff the call is authenticated AND `notBefore ≤ H + 1 ≤ validUntil`. The leaf is `refused (H + 1) code`, so `kept` and `journalForgets` are KERNEL-33's arithmetic verbatim: validUntil ≤ notBefore + W ≤ H + 1 + W, inside the kept range, so the record outlives every height at which the call could be admitted.
- An EARLY call is answered `outsideWindow`, unrecorded and NOT final (it may be resubmitted in its window). A LATE call is final by monotone height and needs no record (`expired`, as today).

**Amendment 6 · finality is a check of `World.admit`, not a host behaviour.** `checkJournal` also refuses `refusedFinal code` when the refusals trie holds `tx txId`. Every follower's fold then refuses a host that admits a call it recorded refused. `submit` consults it up front (journal, then refusals) and answers the recorded name without re-deriving. `submit_refused_final` follows from admission, and the A→B→A arm is its tooth.
- `World.refuse` checks its own preconditions so a host cannot log garbage: in window, the txId neither journaled nor recorded, the member's count below `Bounds.refusalsPerWindow` (else `refusalBudget`), the step counter. It touches only `refusals`, `chain`, `steps`: not cells, journal, height, allowance or weight.
- The refusals prune runs in the turn commit beside the journal prune (one `retainAt` at multiples of W each): `tx` leaves by `kept`, `count` leaves while `win = H / W`.

**Amendment 7 · what is NOT final, named.** Authenticated means: the World matches, the signature verifies, and the key is the member's CURRENT key (`checkKey`), or for a rotate the PRECOMMITTED next key (KERNEL-44 said "after keyRule passes", but `keyRule` skips the key check for `rotate`: anyone could sign a rotate naming M with their own key and spend M's sixteen slots, so M's genuine refusals would become unrecorded). Non-final replies: every (U) code, an early `outsideWindow`, and `refusalBudget` ("not judged"). Example: a call signed with M's precommitted next key, sent before the rotate, is `unknownKey` now and admissible after the rotate. PROTOCOL/CLIENT's attempt store must keep these open; only a recorded refusal ends an attempt. That is a cross-layer item for ROOT.

**Price, as premises on landed theorems (enumerated; the vacuity read re-checks at landing).**
- Statement change, no premise: every theorem naming `World.fold`, `RootedFold`, `chainOf`, `chainNext`/`headLink` or `World.roots` (149 + 29 + 14 + 41 + 25 lines, ~40 files; most in Kernel/Proofs, plus Host/Proofs/{Deployed,Serve,Backup}, Protocol/Proofs/Command, the journeys).
- Premise REPLACED: `fold_head_binds` / `fold_reaches_host` / `deployed_fold_reaches_host` (height → steps).
- Conclusion gains a conjunct: `admit_ok`'s journal clause (no `tx txId` in refusals).
- `lookup_expired_final` / `absent_final`: "not journaled" becomes "neither journaled nor recorded", discharged by the same reached-World facts.
- Cell readers: NONE gains a premise. `refuse` leaves `trie` untouched, so `entry`/`live`/`taken`, the inclusion theorems and `CellsFit` read across it unchanged. `RefusalsCanon` falls only on refusal readers.
- Carry: `Carried` is unchanged; a carried World starts with empty refusals and `steps` = the carried height.

**Teeth (ROOT's conditions).** (1) Sim arm `refusal-aba`: a stale call refused, the pin restored, the call resubmitted. On 7679aac it is ADMITTED (red); here it is `refusedFinal stale`. (2) WASTE row `refusals-per-member-window` (max over seeds ≤ 16) plus plant `refusal-17`: the 17th authenticated in-window refusal is `refusalBudget` and is not stored. Also rows `admit hashes-per-refusal` and `log bytes-per-refusal`. (3) The cell-reader census at landing. (4) The early-window arm: an early call is refused and not recorded, then admitted in its window. Plant: recording it makes that admission `refusedFinal`, and the arm reds.

**As built (what the code says, beyond the amendments).**
- `World.step` / `World.refuse` / `checkRefusal` / `commitRefusal` in Kernel/World.lean. `Receive.judge` (admitted | recorded | declined), `authenticated`, `authKey`, `refusedOf`, `Verdict.code` / `codeName`, and `submit` consulting `refusedAnswer` after the journal: all in Kernel/Receive/Submit.lean. `auditRefusal` re-judges a logged refusal and requires the very same record.
- `commit` hands ONE empty-digest thunk to all three tries (KERNEL-35's rule, now per step across tries). Before this, an empty refusals trie cost its root one hash per turn, and `hashes-per-nullifier` read 7.567.
- `refusalsDisjoint` (CODEC-8's ask): no transaction id is both recorded refused and journaled. `fold_refusalsDisjoint` holds of every fold, and CODEC refuses a base without it.
- Theorems:
  - Kernel/Proofs/Refuse.lean: `refuse_frame`, `refuse_entry` / `refuse_live` / `refuse_isSpent` / `refuse_journalAt`, `step_*`, `fold_keeps`, `admit_refusedFinal`, `refuse_recorded`.
  - Kernel/Proofs/Refusals.lean: `RefusalsOk` (`refusalsOk_of_fits` / `refusalsFits_of_ok`, `fold_refusalsOk`), `refusalCount_le`, `fold_refused_retains`, `submit_refused_final`, `refused_answers` (PROTOCOL-33's shape), `judge_recorded_final`, `judge_recorded_authenticated`, `codeName_code`, `plant_refusals_unseparated`.
  - Kernel/Proofs/Fold.lean: `fold_steps`, `fold_steps_height`, `fold_height_le_steps`, `headLink_inj`, `refusedDigest_inj`, `stepLink_inj`.
  - Kernel/Proofs/Cells.lean: `refusals_separate` (unconditional), `rootsDigest_inj`.
  - Kernel/Proofs/RootedDeployed.lean: `deployed_reach_refusalsOk`, `deployed_judge_recorded_final`.
- Statements whose SHAPE changed, beyond `List Turn → List Step`:
  - `fold_head_binds` / `fold_reaches_host` / `deployed_fold_reaches_host`: height-equal is replaced by steps-equal.
  - `fold_height`: the height grows by `Step.turns l`.
  - `fold_charge`, `fold_conserves`, `fold_nullifiers`, `fold_floors`: over `Step.turns l`.
  - `absent_final`: `∃ t ∈ Step.turns l`.
  - `head_roots` / `head_root` / `head_read_sound` / `head_absent_sound`: over a Step, with the head record `headLink E prev tag td rd` and `(hrd : rootsDigest E root' jroot' rroot' = rd)`. The phone opens one more hash; that is the Roots digest's price, KERNEL-46 amendment 4.
  - `head_journal_read` / `head_journal_absent` / `head_absent_admitted` and the deployed forms: the same `hrd`.
  - `carry_check`: the carried World checks every turn as the exported one would `{ w with refusals := .empty, steps := w.height }`. That is exact: a carry carries no refusals and restarts the counter. `check_origin_blind` is no longer blind to steps (`checkSteps` reads it).
  - `admitted_elsewhere_refused`: gains a third disjunct, `refusedFinal`, for a second World whose refusals hold the id.
  - `receive_reorigin` / `check_origin_blind`: generalized over refusals/steps.
  - No cell reader gained a premise.
- Teeth (kernel-sim, every arm in plantedArms, 64/64 seeds ALL PASS):
  - `refusal-aba:refusedFinal`, with the PLANT `refusal-aba-plant:admitted`: the World without the record, i.e. the code before this, admits the A→B→A call.
  - `refusal-final-fold:refusedFinal`: the follower's fold refuses a Host that admits it, at that step's index.
  - `refusal-early:declined`, `refusal-early-kernel:outsideWindow`, `refusal-early-window:ok`, and the PLANT `refusal-early-plant:refusedFinal`.
  - `refusal-rotate-kept:declined`, and the PLANT `refusal-rotate-plant:authenticated`: by `keyRule`, a stranger takes a slot.
  - `refusal-budget:refusalBudget`: the 17th, unstored.
  - `refusal-forged-code:eventMismatch`: the audit names a forged code.
- WASTE rows:
  - refuse hashes-per-refusal 26.829 (two inserts);
  - refuse record-bytes-per-refusal 519.202;
  - refuse refusals-per-member-window 16.0;
  - admit hashes-per-touched-cell re-pinned 8.969 → 8.887 and hashes-per-nullifier 3.336 → 3.221, from the workload and the shared thunk.
- Vacuity read (second agent, read-only): HOLD on F1, `refusalCount_le` bounded the COUNTER, not the records (a `commitRefusals` writing `.count 1` kept every invariant). Closed: `refuse_refusalCount` / `admit_refusalCount`, `fold_member_refusals` (the count grows by exactly the log's refusals of that member within a window), `fold_member_refusals_le` (the DoS bound over the LOG). Also taken: F2 `submit_refused_never` / `judge_recorded_never` (a recorded call is never admitted, ever: below the prune height `refusedFinal`, past it its own window has ended); F5 `reach_height_le_steps`; F4/F6 docstrings (refusal records are rate-bounded, not budget-charged; an unlogged refusal is invisible to audit); F8 this entry's carry line. Filed: F3 refusal inclusion theorem (the phone's refusal receipt), the early plant's no-op shape. F7 (and CODEC-8's/HOST-12's same find) CLOSED by `checkSteps` on both arms. Re-read of the post-LAND deltas (checkSteps, Checked.steps, carry_check, check_origin_blind, refusalFits 1 ≤ h): LAND, no cell reader gained a premise; its (a) the checkRefusal placement is worded above, (b) the missing checkSteps tooth is added. CODEC-8's reviewer (B) taken: `refusalFits` requires `1 ≤ h` (a fold records `h = height + 1`). Its (C), counting invariants a decoded base could violate (tx leaves ≤ steps − height; counts = this window's tx leaves), is DEFERRED to a cv task: unreachable by any fold, a forged base is a trusted-input question, and the trie-cardinality lemmas it needs are real work; CODEC-32's critique names it.
- Found, not caused here: `kernel-sim --toy` reds `carry-budget-plant` on 9/16 seeds with this patch's refusal probe disabled too. At an 8-byte toy digest, no live cell outweighs a retire turn, which charges 32 per digest field, so the toy has no overflow to find. The toy run is not gated (gates/runs.tsv runs the deployed sim only), so this is a vacuous plant at toy parameters and not a red on main. It is filed as a cv task.

**Critique.**
- Amendment 5 corrects a defect ROOT approved in KERNEL-44: the proposal recorded early refusals, which a later window would have admitted. The approval read the proposal's DoS argument and its premise price. It did not read the window arithmetic, and neither did I until the kept rule was written down beside the window bound.
- The step counter is a fourth position number beside height, chain and the journal's heights. It exists only because heights must not count refusals and chain binding needs a length. The alternative, a separate refusals chain, would make two heads a phone must trust.
- Amendment 5 makes `outsideWindow` sometimes final (late) and sometimes not (early) under one name. Splitting it into `early` and `expired` would be clearer on the wire, but it changes a landed `Reject` constructor that LEDGER and PROTOCOL match; I keep one name and let the record decide finality.
- `refusedFinal` in `World.admit` costs one trie read per turn: a read, not a hash, so the hashes-per-turn WASTE rows do not move.

**Meta-critique.** Every amendment here came from asking what a landed theorem's proof would need, rather than whether the shape resembled a landed one. KERNEL-44 was written by the same method one step removed: it priced statement lines, not proof obligations. Amendments 1 and 2 are proof obligations it could not have seen without opening `chain_binds`.

**Flag day (on the one day with CODEC-8 and HOST-12).** The World, base and carried codecs gain `refusals` and `steps`; the head link changes (tag byte, roots digest); the batch record carries steps; every Store re-geneses; `kernel/world-budget` and the head tags move.

## KERNEL-48 · The rows day's signatures, in code and staged (KERNEL-15, 2026-10-18; KERNEL-46 as co-signed, LANG-44 (c) with ROOT's range-read conditions)
**In code** (staged in logs/kernel15-rows-sig.patch; it builds `Kernel.World`; nothing is wired yet):
- Kernel/Turn.lean: `RowKey`, `RowSlot` (head | row), `RowLeaf` (head count sum limit cap width retract | row amt val), `RowAct` (keep | insert | upsert | retract | declare limit cap width retract), `RowTouch` {slot, seen : Option D, act}, `RangeRead` {parent, rel, pre, most, seen}.
- Kernel/World.lean: `Rows`; `rowKeyBytes`, length-prefixed per amendment 1 (a head is `parent ‖ rel ‖ 0`, a row is `parent ‖ rel ‖ 1 ‖ |k| ‖ k`); `rowLeafBytes` / `rowDigest`; `rowSpec`; `RowLeaf.fits`; `rowAt`; `rowPin`, the first pin kind (a leaf digest, or a domain-separated absent pin); `under`, a prefix walk of the one trie (one path, then the entries returned); `rangeRows` (`none` = `rangeTooLong`, never truncated); `rangePin`, the second pin kind (the relation, width and prefix, the listing's length, then every row's key bytes and leaf digest in key order).
- Kernel/Bounds.lean: `keyBytesMax` 128 (LANG-44 said 64; a two-digest key is 66 bytes), `rowDepth` = 256 + 24 + 8·keyBytesMax, `rowsPerRelationMax` 4096.

**Planned next, the wiring (not in this patch):**
- `Turn.rows : List (RowTouch D)` and `Turn.ranges : List (RangeRead D)`; `World.rows : Rows D`.
- `rootsDigest` gains the rows root (amendment 4); `World.weight` counts rows (amendment 5).
- Reject gains keyTaken, relationFull, relationCapped, rowParentUnpinned, orphanRow, rowsRemain, keyWidth, noRelation, retractForbidden, declareLate, rangeTooLong. A range pin that moved is `stale parent`.
- Theorems:
  - rows_separate (unconditional);
  - rows_stale_refused;
  - range_stale_refused, with stale_refused's conclusion;
  - range_rows_exact: the supplied rows are exactly the keys under the pinned prefix, in key order. Its tooth: a listing with one row dropped has a different pin, and the dropped row's seal arg-max is refuted;
  - head_sum and sum_le_cap;
  - admit_comm: both orders admit, additive heads.
- WASTE `rows-read-per-range-read`.
- Bounds rowsMax and rangesMax per turn.

**Critique.** `under` lists the whole subtree before `rangeRows` compares its length with `most`. That is bounded by `rowsPerRelationMax` but is not an early stop; the wiring makes it stop at `most + 1`. `startsWith` re-checks a leaf's keys against the prefix, because a shallow leaf holds keys of any path.

**KERNEL-16 addendum (2026-10-18): rows are charged, carried, and pinned (wired, not yet landed).**
- *Charge* (amendment 5, done): `RowLeaf.weight` (head 1 + 5·8 + 1; row 1 + 8 + 4 + |v|), `rowEntryWeight (s, l) = s.weight + l.weight`, `World.weight = cellsWeight trie + rowsWeight rows`. `Turn.growth` adds `RowTouch.growth`: a declare its head entry, an insert or an upsert its whole row entry, else 0. An upsert of an existing row and a retract give back the entry they replace or remove (`rowFreed`, judged on the rows before the touch). `rowsRun` returns `(rows, freed)`; `rowsAfter` is its value after `check`; `commit` sets `allowance := allowance + credit posts + freed − charge`. A head write over a head costs nothing (its size does not depend on its counters).
- *Check order* (changed): `… checkNullifiers, checkRowsRemain, checkRanges, rowsRun, checkCharge (credit posts + freed), checkCreates, checkSteps`. Rows run before the charge because the charge needs their credit. A turn with no row touches and no ranges is refused exactly as before (every rows check passes on empty lists; `rowsRemain` fires only on a retired parent that holds rows).
- *Carry*: `Carried` gains `rows` (last field); `World.carried` and `carryWorld` carry them; the carry origin's input gains the rows root bytes after the cells root; `checkCarry`'s `allowanceTooLarge` bounds `cellsWeight + rowsWeight + allowance`, `entryTooLarge` bounds the rows-root bytes. Refusals are still not carried.
- *Premise spread* (priced): `admit_world_weight`, `admit_conserves`, `fold_conserves`, `fold_world_weight`, `fold_budget_lt`, `carry_fold_budget_lt` gain `w.RowsCanon E` (`Trie.Canon (rowSpec E) 0 w.rows`). It is discharged at Deployed (`genesis_fold_budget_lt`, `deployed_budget_lt`: `receive_genesis_rowsCanon`, `fold_rowsCanon`, `carry_rowsCanon`). No cell reader gains a premise: `World.Canon` is unchanged (cells only); the new premise sits only on theorems whose subject, `World.weight`, now includes the rows. `admit_retire`'s conclusion adds `(rowsAfter E w t).2` (0 for a turn with no row touches). `rootsDigest_inj`, `head_roots`, `head_root`, `head_read_sound`, `head_absent_sound` open four roots.
- *Theorems landed in `Kernel.Proofs.Rows`*: `rowStep_weight`, `rowsRun_weight`, `rowsAfter_weight`, `admit_rowsCanon`, `refuse_rows`, `fold_rowsCanon`, `admit_range_pins` / `range_stale_refused`, `admit_row_pins` / `rows_stale_refused` (slots distinct by `duplicateRow`, so no earlier touch moves a pinned row: `rowStep_get_other`). Still owed: `rows_separate` on the domain, `range_rows_exact` with its dropped-row tooth, `head_sum` / `sum_le_cap` and RowsOk (fits + headed) preservation for CODEC's refines, `admit_comm`, and the kernel-sim teeth (stale row pin, stale range pin, keyTaken, relationCapped plants) plus WASTE `rows-read-per-range-read`. [KERNEL-51: now `rowStep_get_out`, heads included]

**KERNEL-17 addendum (2026-10-18): five admission changes found while proving, all strengthening.**
1. *Same-turn orphan (a real hole).* `rowStep` checked the parent live in the PRE-state only, so one turn could retire p and insert a row under p (the retire touch also satisfied `rowParentUnpinned`), leaving a row under a tombstone. Now refused `orphanRow p`.
2. *Heads leave with their parent (`dropHeads`).* `checkRowsRemain` refused a retire while rows remained, but the heads stayed: garbage that counted in `World.weight` and was never credited back. `rowsRun` now ends by removing each retired parent's heads (one `retainAt` path each, ≤ 256 since `rel < 256`) and adds their `rowEntryWeight` to the freed total, so `fold_conserves` stays exact. This is what makes CODEC-9's `rowsParented` (every head's parent is live; over the parts `trie rows`, so the carried wire checks it too) true of every reached World.
3. *A range prefix no longer than the key.* `checkRanges` refuses `keyWidth` unless `q.pre.size ≤ width`. Without it a key SHORTER than the prefix, whose missing bits read as 0, routes into the subtree `under` lists whole, so the listing was not the filtered one and `range_rows_exact` was false.
4. *Bounded reads (the KERNEL-48 critique).* `under S pre n` returns at most n entries and stops walking (`takeList n` past the prefix); `rangeRows` reads `most + 1`; `checkRowsRemain` reads 257 and refuses a full listing (more than 256 entries under a parent means a row). WASTE `rows-read-per-range-read` measures it.
5. *Names.* `rejectNames` gains the 13 rows Rejects in constructor order and `refusalNames` LANG-14's 5 receive refusals: every recorded reject code shifts, so the vectors re-emit and old refusal records refuse by stamp.
Not changed: rows_separate stays CODEC's (`rows_separateOn`, tooth `rows_kindByte_needed`); no Kernel twin.

## KERNEL-49 PROPOSED · A row insert costs 564 hashes because the one trie is uncompressed, not because rows are in it: compress the one trie (K17-K49 for KERNEL-17, 2026-10-18; ROOT's ruling on WASTE `hashes-per-row-insert` 564.071). DESIGN ONLY until ROOT rules.

**The measurement (read at 42c261b).** `hashes-per-row-insert` 564.071 and `hashes-per-row-retract` 569.000, against `hashes-per-touched-cell` 8.900. `rowStep`'s insert is `setHead (r.insert … (.row key) …)`: two path rebuilds. Every key under one relation shares `parent ‖ rel ‖ 1 ‖ width` (280 bits), and its head shares the first 271 of them (tag byte 0 vs 1). An uncompressed trie hashes one node per shared bit, so ~282 per path, two paths.

**What the 564 is NOT bounded by.** ROOT's (c) names `rowsPerRelationMax` as the bound. That bounds the log2 term only. The path is bounded by the DEPTH: a row path is at most `rowDepth` + 1 = 1305 hashes, because Lang keys share bits too (two u64 counters share ~60 high bits; a 128-byte key with a common 127-byte stem shares 1016). The sim probe's keys are `"a0"`, `"a1"`, `"b0"` (16 bits, the first 14–15 shared). So the honest worst case is 2 · 1305 = 2610 per insert, × `rowsMax` 32 = 83,520 per turn. `dropHeads` adds up to 256 · 1305. (PREDICTED from the definitions; nothing ran.)

**The same defect, measured elsewhere.** `refusals` `count` keys share kind ‖ member across windows, and `hashes-per-prune` reads 539.333. Every instance pays ~1 unary node per path on random keys, plus the 0.640 empty-sibling floor (KERNEL-35). The rows only made it loud.

### (a) Path compression in the one trie type

**Shape.**
- `T.node (h : D) (b : Nat) (l r : T)`: `b` is the branching bit, the first bit `≥ d` where the subtree's keys differ.
- `nodeHash b l r = H(2 ‖ u16 b ‖ l ‖ r)`. The depth MUST be in the hash. Without it, a proof can claim other depths and steer `k`'s walk to a leaf that `getAt k` never reaches; an exclusion proof then forges.
- `Spec` gains `depth_lt : depth < 2^16`, a Prop field. Each of the four instances discharges it by `decide` (257, 256, 328, 1304).
- `build` skips the bits where every key agrees, so a node always has two non-empty children.
- `insAt` splits an edge at the first differing bit (one new node).
- `join l r`: an empty side returns the other side whole, a node with its own `b`. Its cached hash is reused, because a node's hash commits its own `b`, not its position.
- `getAt`, `proveAt`, `climb` and `retainAt` follow `b`, not `d + 1`.
- `Proof.sibs : List (Nat × D)`. `verifyInclusion`/`verifyExclusion` check that the `b`s strictly increase and are `< depth`, and climb by `bit k b`.
- `under` gains one representative-key check when a node's `b` jumps past the prefix end. The skipped bits are not on the path. That is one leaf read and no hash.
- DELETED: the `EmptyDigest` parameter on `mkNode`, `build`, `insAt`, `proveAt`, `join`, `retainAt`, `rowStep`, `setHead`, `rowsRun` and `dropHeads`. No inner node has an empty child, so only an empty ROOT hashes `emptyHash`. KERNEL-35's thunk survives at the four roots only.

**Premises first** (measured by grep at 42c261b; scripts in `logs/k49-spread.py` and `logs/k49-stmt.py`):
- *New premise on any landed theorem: NONE*, if the depth bound is the `Spec` field. As a premise instead, `S.depth < 2^16` would land on `climb_sound`, `inclusion_sound`, `exclusion_sound` and `prove_includes`/`prove_excludes`. It would then spread to every **cell reader** that opens a proof: Cells.lean 6, JournalHead.lean 5, RootedDeployed.lean 10, and Protocol/Proofs/Receipt's `check_*`. ⚑ So the field is the design, and the premise form is refused.
- *Definitions whose meaning changes, names kept*: `WF` (commits `b`), `Shape` (node `b` = first divergence, both children non-empty), `Shallow`, `Routed` (split at `b`), and so `Canon`. `World.Canon`, `JournalCanon`, `RefusalsCanon` and `RowsCanon` keep their text. Cell readers keep their premises by name, and the names now mean more.
- *Statements that change text (mechanical: the `e` argument dropped, or `build`/`join` re-specified; no premise added)*, as theorems whose statement names a trie internal:
  - Kernel/Proofs/Trie 20 of 46 (`getAt_build`, `getAt_insAt`, `build_split`, `shape_insAt`, `canon_build`, `build_toList`, `climb_proveAt`, `prove_includes`, `prove_excludes`, `length_insAt`, …);
  - TrieRetain 8 of 8 (`toList_join`, `canon_join`, `retainAt_eq_build`, `get_retainAt`, …);
  - TrieMap 1 (`build_perm`);
  - Codec TrieOrder 8 (`build_listing_iff`, `listing_check_iff`, …);
  - TrieOrderDeployed 7 (`trieOrder_iff` … `rowOrder_iff`);
  - SlotOrder 6;
  - RowOrder 2;
  - Rows 11, RowsRange 5 (`takeList_eq`, `under_eq`, `under_needs_long`, `under_rows`, `filter_pairwise`), RowsHead 14, RowsComm 15. Most of these 45 rows hits are only the `e` argument.
- *Proofs re-done, statements unchanged*: every theorem over `Canon`/`Routed` (Value 7, Weight 6, Cells 6, JournalHead 5, RootedDeployed 10). Their statements are text-identical. Whether their proofs survive depends on the `Canon` lemmas keeping their names: ASSUMED yes for the 34 that only cite `get_insert`/`canon_insert`/`mem_toList`.
- Total: ~97 statements re-proved in place, 0 premises added, and 0 cell-reader premises.

**Re-emits.**
- Every root changes: cells, journal, refusals and rows. So `rootsDigest`, every chain head, genesis, the carried origin (it hashes the roots' bytes), every vector carrying a root, and every Store re-geneses.
- The phone's proof wire changes. `Proof.sibs` gains a u16 per sibling, so Protocol/Receipt's `jsibs`/`rsibs` gain `jdepths`/`rdepths` (PROTOCOL re-cut), and an old receipt refuses on parse.
- UNCHANGED, byte for byte: the World and carried LISTINGS (the wire is `toList`, which keeps its order), cell pins, row pins and range pins (`rangePinBytes` reads the listing, not the trie).
- `Kernel/Trie.lean` is upstream of everything, so this is a serial day for KERNEL-17 alone, and the whole tree rebuilds once.

**Cost (PREDICTED).**
- *Row insert*, in the probe's rows trie (≤ 8 entries: 2 heads plus rows; branches at bit 263 (rel), 271 (head|rows) and ~294 (key)): the row path is ~3 nodes + 1 new node + 1 leaf, and `setHead` is 1 leaf + ~2 nodes. That gives **~8–10** (was 564.071).
- In general: 2·(log2 N + 0.33) + 2 for N entries in the rows trie, with **no term in key length**.
- *Retract*: the leaf goes, its node collapses for free (the sibling's hash is reused), plus ~2 ancestors and `setHead` ~3: **~6** (was 569.000).
- *Touched cell*: −~1.0 per path, the uncompressed trie's path constant (~1.33 for random keys) against a compressed one's (~0.33). ASSUMED: textbook digital-trie constants, random ids. A further −0.640, because the empty-sibling floor goes. **8.900 → ~7.3.**
- Nullifier, journal entry, refusal and prune all fall, by about one hash per path.
- *Range read*: 0 trie-domain hashes before and after; `rangePin` is 1 + m digests (m rows listed), unchanged. `rows-read-per-range-read` 2.400: +≤1 leaf read per skipped prefix.

**Effect on the rows theorems.**
- `range_rows_exact`: same statement; `under_eq` is re-proved with the representative check.
- `admit_comm` and `head_sum`: statements unchanged; they are stated over `rowAt`/`toList`.
- `rowsParented` and `carry`: unchanged; they read `toList` and roots.
- CODEC's refine sites (`listingAccept`, used by `cells`, `journalTrie`, `refusalsTrie` and `rowsTrie`): text unchanged. `build_listing_iff` is re-proved.

### (b) Two levels: each relation's rows in their own subtrie under its head

**Shape.**
- `Rows D := T (HeadSlot D) Head D` with `Head := {count sum limit cap width retract, sub : T ByteArray RowVal D}`.
- `relSpec` routes a row by `k ‖ u8 |k|`, with the length byte as a SUFFIX. That is injective under zero-padding, because the byte at position |k′| is 0 on the shorter key and ≥ 1 on the longer, so it is prefix-free with no World invariant (KERNEL-46 amendment 1 kept). Depth 8·(keyBytesMax + 1).
- A head's digest is `H(domRowHead ‖ fields ‖ sub.hashOf)`.
- `RowSlot`, `rowAt` and `rowPin` keep their API: two lookups.
- ⚑ **The top key must be `rel ‖ parent`, not `parent ‖ rel`.** With `parent ‖ rel`, two relations under one parent share 263 bits. The probe declares two (rel 0 and rel 1 under one parent), so the head write alone would still cost ~264. That is (b) as ROOT worded it: PREDICTED ~276 per insert, half of today.
- With `rel ‖ parent`, a parent's heads no longer sit under one prefix. `checkRowsRemain` and `dropHeads` become ≤ 256 point reads (`rel < 256`), not one prefix walk.

**Premises first.**
- No cell reader is touched, and `Kernel/Trie.lean` is unchanged.
- `RowsCanon` gains a conjunct (every head's `sub` is `Canon relSpec`). Its name is kept, and it lands on exactly KERNEL-16's six (`admit_world_weight`, `admit_conserves`, `fold_conserves`, `fold_world_weight`, `fold_budget_lt`, `carry_fold_budget_lt`).
- `WF` of the top no longer implies `WF` of a sub (the head digest reads a cached root). Any future rows inclusion theorem carries a nested `RowsWF`. No landed theorem opens a rows proof, so none gains it today.
- Statements rewritten (the `Rows` type changes), counted as theorems naming rows defs:
  - Rows 27, RowsHead 36 (`head_sum`, `fold_head_sum`, `rowsHeaded_iff`, `admit_rows_listing`: simpler, per head), RowsComm 21, RowsRange 24, RowsSep 5 (`rows_separateOn` splits into `heads_separate` and `relRows_separate`, both unconditional), RowsRangeDeployed 1;
  - Codec RowOrder 7, Rows 5, RowsReached 4, World 13, Carried 9, WorldTooth 21;
  - Host/Proofs/Deployed 10.
  - ~180, ASSUMED most mechanical.

**Re-emits.**
- The rows root, `rootsDigest`, chains, genesis, carried origin and vectors re-genesis.
- The cells, journal and refusals roots are unchanged.
- The listing wire can stay flat and byte-identical: a head sorts before its rows. The `rowsTrie` refine then groups, and `listingAccept` gains a two-level twin. Range pins can stay byte-identical (keep emitting `rowKeyBytes`).

**Cost (PREDICTED, `rel ‖ parent`, uncompressed).**
- The top path, with 2 heads diverging at bit 7: 7 unary nodes + 1 + leaf = 9.
- The sub path in the probe: 0 for a lone row, ~15 for "a0" against "a1": ~11 averaged, + leaf.
- **~20 per insert, ~20 per retract**; cells 8.900 unchanged.
- Key-structured relations keep paying: a u64-counter relation costs ~60 + 9. So (b) removes the 280-bit stem but not a key's own.

**Effect on the rows theorems.**
- `head_sum` becomes local, and orphan rows become UNREPRESENTABLE. `rowsHeaded`'s "a row needs its head" clause is deleted, not checked.
- `range_rows_exact` walks one sub with `pre` alone.
- `admit_comm_rows` needs one more `eq_of_get_eq` layer (sub canon) for root equality.
- `rowsParented` iterates over heads only.
- `Carried.rows` changes type; its wire does not.

### (c) Accept the cost

- Price: zero premises and zero re-emits.
- The bound is not `rowsPerRelationMax`: it is 2·(`rowDepth` + 1) = 2610 per insert (above). The WASTE row must say that bound, and an arm must show it.
- It keeps the 0.640 floor and the unary-path tax on every instance.

### Teeth and WASTE rows that land with each

- **(a)**
  - Re-pin downward: `hashes-per-row-insert`, `-row-retract`, `-touched-cell`, `-nullifier`, `-journal-entry`, `-prune`, `refuse hashes-per-refusal`.
  - NEW `hashes-per-row-insert-stem`: a probe relation of 64 u64-counter keys, PREDICTED ≈ the random-key figure.
  - NEW `proof bytes-per-inclusion`.
  - Plant `depth-unhashed`: `nodeHash` without `b`, with a forged exclusion that steers past `k`'s leaf. It must VERIFY under the plant and refuse at main.
  - Theorem `canon_no_empty_child`, with its negative: a unary node is not `Canon`.
- **(b)**
  - Re-pin row insert/retract.
  - NEW `hashes-per-row-insert-stem` (it will show ~70: the residual named).
  - Plant `head-sub-unbound`: the head digest without `sub.hashOf`, a row swapped under an unchanged rows root.
  - Plant `parent-major-heads`: the `parent ‖ rel` top key, whose WASTE row reds at ~276.
- **(c)**
  - `hashes-per-row-insert-worst`, a 128-byte stem relation, ceiling 2610.
  - The WASTE source text names the depth bound, not `rowsPerRelationMax`.

**Recommendation: (a).**
- The defect is the trie's: it taxes four instances, and the fifth will pay it too.
- (b) fixes one instance, only with a key order ROOT's wording did not have, and leaves each key's own stem.
- (a)'s price is ~97 re-proofs, zero added premises and zero cell-reader premises. Every root re-geneses, and the phone's proof wire is re-cut, which is a rebuild. It also DELETES KERNEL-35's per-node thunk plumbing.
- (b)'s structural wins (orphan rows unrepresentable, a local `head_sum`) are real and independent of cost. They deserve their own entry, not a ride on this one.

**Open question for ROOT, Q49:** is the Patricia node's depth committed as a fixed u16 under a `Spec` field `depth_lt` (zero theorem premises), rather than as a premise on the 21+ cell-reader inclusion theorems? And may KERNEL-17 alone edit `Kernel/Trie.lean` for one serial day, every other lane parked on the rebuild?

**Critique.**
- A cheaper containment exists and is NOT offered. Fusing the row's and the head's writes into one pass shares the ~271 common levels, which gives ~290 per insert. It still lands 30× over a cell, and it would become the reason (a) never happens.
- The cost figures are PREDICTED from definitions plus textbook trie constants; the probe is tiny (≤ 8 rows), so its figure flatters every option equally.
- The ~97 and ~180 counts are statements naming internals (a regex over statements), not proof obligations. As KERNEL-47's meta-critique warns, the proofs are where the price hides: (a)'s `Shape` must state "first divergence", and `build_toList`'s induction changes measure from depth to fuel-with-skips.
- (a) makes a node's hash 2 bytes longer: the hash count is unchanged, and the bytes hashed rise ~3%.

### KERNEL-49 RULED (a), and amendment 1 (KERNEL-18, 2026-10-18; ROOT accepted): a node keeps a representative key

**ROOT's ruling (10-18).** (a) is approved, Q49: the depth bound is a `Spec` FIELD. Conditions:
1. the reader lists every restated statement and asserts that no cell reader gained a premise;
2. the proof wire gains a u16 per sibling and the receipt is re-cut (PROTOCOL-11), while listings and the three pin kinds stay byte-identical, with a plant per pin kind;
3. KERNEL-35's per-node empty-digest plumbing is DELETED;
4. the WASTE rows are re-pinned DOWN with measured values;
5. (c)'s bound is stated: 2·(`rowDepth` + 1) = 2610 hashes per insert, × `rowsMax` 32 = 83,520 per turn, which is what option (c) would have had to print and an arm show;
plus the forgery tooth (plant `depth-unhashed`).

**Amendment 1: what the proposal missed.**
- In a path-compressed trie a node skips the bits its keys agree on. With a `getAt` that follows only the branching bits, `get` after `insert` is exact only on a ROUTED trie. That holds for a canonical tree; it fails for an arbitrary one.
- `get_insert` today has no premise. It is used about 60 times, in Frame (`admit_frame`, `admit_rom`, `fold_rom`, `admit_nullifiers` …), Value, Weight, CellsFit and Rows*, over arbitrary Worlds. Under the proposal's shape it would gain `Routed S 0 t`, which spreads as `World.Canon` premises onto those theorems.
- The proposal's "0 premises" counted statements that NAME trie internals; it never counted the theorems that USE `get_insert`. That is the error KERNEL-47's meta-critique warned of, now found in the proofs.

**The fix, which is forced: `T.node h b rep l r`.**
- `rep` is the subtree's first key in trie order. It is a cache of the bits every key below agrees on, and it is NOT hashed, so roots and the proof wire are unaffected.
- `getAt k d` checks `k` against `rep` on the skipped bits `[d, b)` (`diverge`). When they differ, `getAt` answers `none` before following bit `b`.
- `insAt` splits exactly where `diverge` says. `getAt` and `insAt` therefore consult the same datum, and `get_insert` holds on ANY tree, with no premise.
- Any design that lets `getAt` ignore the skipped bits makes `insAt`'s split depend on a key-set invariant that an arbitrary tree can violate. So a premise-free `get_insert` needs `getAt` to read what `insAt` reads.

**Its price, premises first** (the reader's list, K18-READER over the joint tree):
- `Trie.inclusion_sound` and `Trie.prove_excludes` gain `Routed S 0 t`, and `getAt_proveAt` gains `Routed S d t`. A malformed tree could hold a key in a leaf that `getAt`'s check refuses: such a proof's leaf holds `k`, yet `getAt` reads none. The premise-free direction is `getAt_some_proveAt`.
- Every caller holds the trie's `Canon` and passes `hc.1`: three `inclusion_sound` sites and three `prove_excludes` sites, in Cells, JournalHead and RefusalsHead. So no cell reader's statement changes: Cells, JournalHead, RefusalsHead, RootedDeployed, Value, Weight, Frame, CellsFit and Protocol/Proofs/Receipt keep their text.
- Inside the trie's own proofs:
  - `climb_sound` gains `ascends` (`u16` wraps at 2^16), which the verifier supplies;
  - `shape_insAt` gains `Routed`, which `canon_insert` passes;
  - `wf_mkNode` gains `b < depth`;
  - `canon_join` gains the agreement on `[d, b)`.
- In the rows readers:
  - `under_eq` gains `Shape`. Its agreement premise becomes "keys agree pairwise below d" (vacuous at d = 0, where every caller sits).
  - `under_rows`, `range_rows_none`, `range_rows_mem`, `range_rows_erase_not_exact` and RowsHead's `under_parent` go from `Routed` to `Canon`. This is forced (tooth `under_needs_shape`): `under` reads `rep`'s bytes, so `rep` must be a key of the subtree.
  - Every caller already held `Canon`. `range_rows_exact`, `admit_range_exact` and `fold_range_exact` keep their text.
  - `Rows.under_range` is restated at `d = 0` (`Under` now indexes the path absolutely, as `retainAt` reads `path[b]?`).
- `exclusion_sound` stays WF-only. When `getAt` answers `none` early, the exclusion claim is true; otherwise `getAt` and `proveAt` walk the same path.
- Work: one comparison of at most `depth` bits per `get`, spread along the path, and no hash.
- `rep` is canonical (a node's first key, `T.first`), so `build_toList` keeps `=`. `insAt` maintains it by `precedes` (k comes first in trie order) without walking.
- `under` reads `rep` for its one prefix check.

**What the day re-emits, re-geneses and refuses** (unchanged from the proposal):
- every root changes, so every Store re-geneses, and `rootsDigest`, every chain head, genesis, the carried origin and every vector carrying a root re-emit;
- `Proof.sibs : List (Nat × D)`, so the proof wire gains a u16 per sibling and the receipt is re-cut, and an old proof refuses on parse;
- listings, cell pins, row pins and range pins are byte-identical.

**Measured (kernel-sim --seeds 64, COUNTED; ROOT conditions 4 and 5).**
- Ceilings, every one falling:
  - `hashes-per-row-insert` 564.071 → 7.642;
  - `-row-retract` 569.000 → 6.000;
  - `-touched-cell` 8.900 → 6.757;
  - `-nullifier` 3.317 → 2.865;
  - `-journal-entry` 13.672 → 12.162;
  - `-prune` 539.333 → 418.333;
  - refuse `hashes-per-refusal` 26.829 → 11.410;
  - `hashes-per-turn-rows-root` 0.128 → 0.
- New rows:
  - `hashes-per-turn-empty-root` 1.000: the shared empty digest, moved out of the cell, nullifier and rows rows, not a new cost;
  - `hashes-per-row-insert-stem` 7.515: 64 u64-counter keys sharing 58 bits, ≈ the random-key figure as predicted;
  - `proof bytes-per-inclusion` 257.133 = 74 + 34n, n ≈ 5.39.
- (c)'s bound, as (c) would have had to print it: 2·(`rowDepth` + 1) = 2610 hashes per insert, × `rowsMax` 32 = 83,520 per turn. The worst single insert the stem probe measured under (a) is 11.
- Plants:
  - `depth-unhashed`: `b` dropped from the node hash, a forged exclusion VERIFIES under the plant and is refused by the deployed verifier;
  - `proof-bit:refused`;
  - one per pin kind (cell, row, range: the pins equal a trie-free reference, and a perturbed read is caught);
  - CODEC's six ListingPin plants: the pre-day listing bytes reproduced by the compressed trie.

## KERNEL-50 · A refusal's record names its member, and a World's window counts are a function of its records: `refusalsCounted` (KERNEL-19, 2026-10-19; cv 01a14da3-3e7a, CODEC-8's reviewer (C) deferred by KERNEL-14; ROOT ruled the per-member form)

**The defect.** A window count leaf (`count member win ↦ n`) is a cache: `checkRefusal` reads it in one lookup so as not to scan the records. Nothing tied the cache to what it caches. A fold keeps them equal (`fold_member_refusals`), but a decoded base is not a fold. A base could:
- lower a member's count, which resets its budget;
- move one member's charge to another;
- hold more records than its steps could have produced.
CODEC's `kernel/refusals` (`refusalsFits`) checks each leaf alone, and none of these is visible leaf by leaf.

**Why the member goes into the record.**
- The per-member equation "M's count = M's records this window" cannot be stated while a `refused` leaf does not say whom it charged.
- The cheaper form, Σ counts = this window's records, passes a base that moves a charge from M to N. That is a containment of the defect, not its fix, and ROOT refused it.
- ROOT's second reason, recorded here: a receipt that names WHO was charged is what lets the member the budget bites audit that budget. PROTOCOL's refused answer now carries the member.

**What it does not do.** The check makes the counts a function of the records. It does not authenticate the records. A forger who rewrites both a record's member and the counts passes it. Which member a record names is what the chain binds (the leaf digest commits it). The member's own receipt then shows a charge that is not theirs.

**As built.**
- `RefusalLeaf D`: `refused (h code : Nat) (member : D) | count (n : Nat)`.
- `refusalLeafBytes E` appends `E.bytes member` after the two u64 counters. `domRefusal` is now `…/refusal-leaf/v2`.
- `World.refuse` records `.refused (H + 1) r.code r.member`.
- `refusalsCounted E w : Bool` (Kernel/World.lean) checks three things:
  1. records + height ≤ steps;
  2. every count leaf equals the tally of its member's records this window;
  3. every member with a record this window has a count leaf.
- The tally (`refusalTally`) is one pass over the listing into a trie under `tallySpec`. That spec routes as the refusals do but hashes nothing (a constant `hash`, empty `kbytes`/`dbytes`), and `get` after `insert` is exact for any `Spec`. So the check costs O(n · path) with no hash. A plain per-count scan would be O(n²) on an untrusted listing of up to `worldMax` entries.
- A record of window w: its leaf holds `h = H + 1` for the height `H` it was recorded at, so the record belongs to window `(h − 1) / windowMax`.

**Theorems (Kernel/Proofs/RefusalsCounted.lean, new).**
- `World.CountedOk` (records + height ≤ steps; ∀ m, `refusalCount E w m` = Σ `refusedIn w.height m` over the listing).
- `refusalsCounted_iff (hw : w.RefusalsOk E)`: the Bool decides it.
- `refusalCount_eq_of_counted`: the reader a decoded base gets.
- Preservation: `admit_countedOk` / `refuse_countedOk` / `step_countedOk` / `fold_countedOk`, then `fold_refusalsCounted`, `Receive.reach_refusalsCounted`, and `Receive.deployed_reach_refusalsCounted` (no premise).
- Helpers: `tallyAt_foldl`, `tally_support`, `refusalTally_get`, `sumN_insert_count`, `refuse_sumN`, `refusalWindow_succ_ne` (consecutive windows have different UInt64 names: there is no wrap onto the predecessor, so no height premise).
- TOOTH `refusalsCounted_moved`: on a World that passes the check, lower m's count by one and raise m′'s by one. Every leaf still fits (`RefusalsOk`, so `refusalsFits` and every earlier wire refusal admit it), and `refusalsCounted` refuses it. `refusalsCounted_moved_sum` proves the sum of the counts unchanged, so the refused sum form would have passed it. `refusalsCounted_moved_exists` is conditional: it builds the moved World from any World meeting the premises. The concrete instance is CODEC's `world_reads_counted_charges` (a counted World, member 2 holding 2 and member 5 holding 1) paired with `world_refuses_moved_charge`, which also passes the journal, disjoint and steps sites.
- Sim arms (kernel-sim, in `plantedArms`): `refusals-counted:counted` (the Host's World passes) and the PLANT `refusals-counted-plant:refused` (the moved World passes `refusalsFits` and fails `refusalsCounted`).

**Price, in premises on landed theorems.**
- `refusalLeafBytes_inj` and `refusalDigest_inj` gain `hE : E.Lawful n`: the member's bytes must be injective. Every caller (`refusal_inclusion_sound` and its head/deployed forms) already held `hE`. No other theorem gains a premise.
- Statements that only gain the member variable: every statement naming `.refused h code` (`checkRefusal_facts`, `refuse_facts`, `World.RefusalsDisjoint`, `fold_refused_retains`, `admit_refusedFinal`, `admit_not_refused`, `refuse_recorded`, `refuse_refusalAt`, `head_refused_retained` and the deployed forms, `refusalDigest_wraps` / `refusal_inclusion_unbounded`).
- Cross-layer statement changes are listed in the commit.
- CODEC's `world_decode_wire_ok` / `_overBudget` / `_rowsRefused` / `_headedRefused` / `_parentedRefused` gain `hct : refusalsCounted E (ofWire x) = true`. Their wires now pass the new site, which sits before theirs.
- Protocol: `check_refused_uncommitted`, `check_refused_sound`, `check_refused` and `Settle.build_answer` gain the member as an implicit variable, with no premise.
- Host: `Kept` gains a field `counted` (discharged at genesis, at carry, and per step). `refusals_entry_size` changes only its type.
- Two structures gain a field, which every consumer then gets: `World.CodecFits.refusalsCounted` and Host's `Kept.counted`. Every constructor discharges it: `genesisWorld_codecFits`, `importWorld_codecFits`, `codecFits_of_kept`, `kept_admit`, `kept_refuse`, `kept_of_fits`.
- No cell reader and no journal reader is touched (the reader K19-READER checked this against the diff).
- A gap this day widens and does not close: the receipt wire now carries the member, and there is no `Receipt` bytes/ofBytes round-trip theorem (only `Reply.ofBytes_bytes`). It is filed for PROTOCOL as a cv task.

**Flag day (one `kernel!` commit).**
- The refusal leaf's wire gains the member, so its content-addressed tag moves, as do `kernel/refusal-order` and every World-wire tag.
- The refusal digest changes (domain v2), so every refusals root changes and every Store re-geneses.
- The receipt's refused answer gains the member: the receipt wire re-emits.
- CODEC's new site `kernel/refusals-counted` (`countedWire`, `CountedWireFits`, `countedWire_lawfulOn`) sits AFTER `kernel/steps`. records + height ≤ steps implies height ≤ steps, so a site placed before `kernel/steps` would leave that site unable to refuse anything. The chain is journal → refusals → refusals-disjoint → steps → refusals-counted → rows → ….
- `World.CodecFits` gains `refusalsCounted`. Decode direction: `world_decode_refusalsCounted`, `world_get_refusalsCounted`, the deployed twins, and `Host.Deployed.world_decode_countedOk`, which hands a decoded base `World.CountedOk`.
- WorldTooth teeth: `world_reads_counted_charges`, `world_refuses_moved_charge`, `world_refuses_lowered_charge`, and `world_refuses_records_past_steps`, where `kernel/steps` passes and the new site refuses.
- The vectors' drawn Worlds are counted. The boundary pair is a World with two charges for one member and one for another, then the same World with one charge moved; each is refused by its own site's name.
- Vector families that moved: refusal-leaf, refusal-order, journal, refusals, refusals-disjoint, steps, world-budget, rows, rows-headed, rows-parented, host/base/index-count, and the new refusals-counted.
- WASTE: no row moves. Refusal hash calls are counted calls, and the leaf is hashed once either way. `record-bytes-per-refusal` measures the log record, which is unchanged.

**Critique.**
- `kernel/steps` is now implied by `kernel/refusals-counted`: records + height ≤ steps gives height ≤ steps. It is kept on purpose. It is the earlier, cheaper check, and its name `steps` says exactly what a height-past-steps base got wrong. Under law 7 a refusal is answered by its own name, and `refusals-counted` would name the wrong thing. Both sites still refuse something: `world_refuses_height_past_steps` and `world_refuses_records_past_steps`.
- The count leaves are now provably redundant with the records. They are kept as the O(1) read `checkRefusal` needs. The alternative, deriving a count by scanning the records, would put a scan on every recorded refusal. The check above is what keeps two shapes of one fact from drifting apart.
- Vacuity read (K19-READER): LAND-WITH-FIXES, six items. Taken:
  - (1) the `_exists` wording above;
  - (2) `refusalsCounted_moved_sum`;
  - (3) the tooth's docstring now claims only `RefusalsOk`;
  - (4) the sim plant guards `f.id ≠ o`;
  - (5) the price list above;
  - (6) this critique's first bullet.

## KERNEL-51 (PROPOSED, then BUILT: see AS BUILT below, which corrects this text) · The frame rule as one scheme: `Kernel/Proofs/Logic/Frame.lean` (KERNEL-19, 2026-10-19; ROOT, from PROOF-TECHNIQUE-20261019.md §3–4). DESIGN ONLY until ROOT rules.

(Numbering: ROOT's message called this KERNEL-50. The refusalsCounted day took 50, so this is 51 and the head-read scheme is 52.)

**Shape.** One proof-module (closure C3: the footprints are Props, never computable lists).
- `inductive CellFoot (t : Turn D) : Slot D → Prop` with three constructors: `touched` (x ∈ t.touches, x.act ≠ .keep), `born` (c ∈ createdIds t), `spent` (n ∈ t.nullifiers).
- `inductive RowFoot (t : Turn D) : RowSlot D → Prop` with three constructors: `slot` (x ∈ t.rows), `head` (the head of a touched row, a shared counter, inside the footprint), `dropped` (the heads of a retired parent: `dropHeads`).
- `structure Frame E w w' t : Prop`:
  - `cells : ∀ s, ¬ CellFoot t s → w'.trie.get s = w.trie.get s`, with NO premise;
  - `rows : w.RowsCanon E → ∀ s, ¬ RowFoot t s → w'.rowAt E s = w.rowAt E s`;
  - `journal : w.JournalCanon E → ∀ k, k ≠ t.txId → …` (`commit_journalAt`'s other half);
  - `refusals : w.RefusalsCanon E → …` (the prune);
  - `origin`, `allowance` / `height` / `steps` as equations.
  Each trie-wide premise is a hypothesis of its own field, never of the structure: a flat conjunction would re-enact KERNEL-41 (a) one level up.
- `admit_Frame : World.admit E w t = .ok w' → Frame E w w' t`.
- `refuse_Frame`, with the empty cell and row footprints.
- `not_cellFoot_iff`: the old inline hypotheses (`∀ x ∈ t.touches, x.cell = c → x.act = .keep` and `c ∉ createdIds t`) ↔ `¬ CellFoot t (.cell c)`. This is the reader's evidence that the footprint is not larger than the hand statements' hypotheses.

**Verified, not assumed (read on main 8ad3982).**
- The cells field needs zero premises. `commitTrie_entry` (Frame.lean:55) takes only the two footprint facts. Its proof is `commitTrie_cell` + `insertAll_get_of_not_mem`, which rest on `Trie.get_insert`, and that is premise-free because of KERNEL-49 amendment 1's `rep` check. Nullifier monotonicity (`commitTrie_spent`) is premise-free too. [KERNEL-51: deleted; `Frame.cells` + `spendAll_spent_of_mem`]
- The rows field needs `Canon (rowSpec E) 0` exactly where the landed lemma takes it: `rowStep_get_other` (Rows.lean:449), because retract and `dropHeads` are `retainAt`. [KERNEL-51: now `rowStep_get_out`, heads included]
- The journal field: `commit_journalAt` (Admit.lean:230) takes `JournalCanon`.
- One correction to the scholar's sketch: `RowFoot.dropped` is right to name only heads, because `checkRowsRemain` refuses a retirement whose parent still holds a row. But that is a fact of `Checked`, so `admit_Frame` (which holds `Checked`) can use it, and a frame over bare `commit` could not.

**Instances (statements and premise counts unchanged).**
- Re-derived as one-liners from `admit_Frame`: `admit_frame`, `admit_rom`, `admit_nullifiers`.2 (0, 0, 0 invariants), and the ~22 hand restatements across Frame / RowsComm / RowsHead / Rows.
- DELETED: RowsComm's private twins `commit_cell_frame`, `commitTrie_out`, `view_row_out`, plus the privates they carried.
- `rowStep_get_other` stays as the per-step lemma the rows field is proved from. [KERNEL-51: now `rowStep_get_out`, heads included]

**Teeth.**
- `cellFoot_needs_born`: with `born` removed, `.cells` is false on a concrete create turn.
- `rowFoot_needs_head`: with `head` removed, `.rows` is false on a concrete insert.
- Each is stated as a counterexample to the smaller footprint.

**Price.**
- No premise is added to any landed statement. `Lean proof-modules` +1 (a SIZE line). Theorems: net fall (−4 twins, −~9 RowsComm privates, +~7).
- The module is a hub: it holds only the statements, the rule and the teeth, no corollaries, so that an edit to it rebuilds as little as possible.
- The reader's check: no cells-side field takes a trie-wide premise.

**Cost.** One lane, 1–2 days, serial.

## KERNEL-52 (PROPOSED, then BUILT: see AS BUILT below, which corrects this text) · The head-read family as ONE authenticated-map scheme over `Trie.Spec`, instantiated per trie (KERNEL-19, 2026-10-19; ROOT, PROOF-TECHNIQUE §4.1 item 3). DESIGN ONLY.

**Today.** The same chain of theorems is restated per trie:
- `*_inclusion_sound`, `*_exclusion_sound`, `*_prove_verifies`, `*_prove_absent`;
- `head_*_read`, `head_*_absent`, `*_coll_collision`, `*Digest_inj`;
  (Correction, KERNEL-56: the `*_coll_collision` lemmas are deleted with `Collision`, `Trie.Coll` and `HashColl`; every escape is now `CollidesAmong E.hash S` over the theorem's own inputs.)
- the `deployed_*` forms.

It appears in Cells.lean (cells), JournalHead.lean, RefusalsHead.lean (which calls itself "the twin of JournalHead"), RowsHead.lean, and RootedDeployed. The scholar counted three instances. There are FOUR: the rows' head reads in RowsHead.lean are the same chain.

**Shape.**
- `structure HeadInstance (E : Env D) where`:
  - `K V`, `spec : Trie.Spec K V D`;
  - `trieOf : World D → Trie.T K V D`;
  - `rootIdx`: which of the four `rootsDigest` slots;
  - `Fits : V → Prop`;
  - `body_inj` (needs `hE`);
  - `vdigest_inj : Fits v → Fits v' → vdigest v = vdigest v' → v = v' ∨ Collision`;
  - `canonOf : World D → Prop`.
- ONE family over it: inclusion/exclusion soundness at the World, prove_verifies / prove_absent, head read / head absent through `head_roots`, and the deployed forms through one `deployed_reach_*`.
- The four tries become four records. The per-instance premises (`0 < n` for the journal, `RefusalLeaf.Fits`, the cell `InjOn`) stay in each record at the same strength.

**Price.**
- Every landed statement keeps its text as a one-line corollary (consumers in Protocol / Host / Client name them), so no premise spreads.
- The theorem ratchet falls by roughly 45 → 8 + 4 records + the corollaries kept by name. The corollaries are a choice: deleting them moves every consumer's call site, which is a cross-layer day.
- The reader reads eight statements once and four records.

**Cost.** 2 lane-days. It should come AFTER KERNEL-51: both touch the head files and the hub metric.

### KERNEL-51 AS BUILT (KERNEL-19 / K19-F, 2026-10-19; ROOT approved with conditions)
- `Kernel/Proofs/Logic/Frame.lean` holds the following.
  - `CellFoot`: the cell of a non-`keep` touch, a born id, a spent nullifier.
  - `RowFoot`: tighter than the design. It holds the slot of a non-`keep` row touch, the head of a row it writes, and every head of a parent it retires.
  - `structure Frame`, with four fields: `cells` (NO premise), `rows` (`w.RowsCanon E →`), `journal` (`w.JournalCanon E →`), `refusals` (`w.RefusalsCanon E →`). Height, steps and origin are NOT fields. They are `admit_height`, `admit_steps` and `admit_origin`, which sit below the hub; restating them would be a twin.
  - `admit_Frame`.
  - **`not_cellFoot_iff` is the reader's evidence** (ROOT's condition): `¬ CellFoot t (.cell c) ↔ (∀ x ∈ t.touches, x.cell = c → x.act = .keep) ∧ c ∉ createdIds t`. That is exactly the two hypotheses the hand frames took.
  - Teeth, each a concrete turn whose admission is proved, so the smaller footprint's frame is false:
    - `cellFoot_needs_born`: a born RAM cell reads `none` before and the cell after.
    - `rowFoot_needs_head`: a `keep`-pinned parent with one insert has its head count go from 0 to 1.
- Re-derived from `admit_Frame`, with statements and premises unchanged: `admit_frame` (`.cells` + `not_cellFoot_iff`), `admit_nullifiers`.2, and RowsComm's `admit_comm` cell reads (four sites through `.cells`).
- DELETED:
  - RowsComm's twins `commit_cell_frame` and `commitTrie_out`, plus the privates `insertAll_get_base`, `commitTrie_base`, `bornEntries_fst`, `mem_postKeys`, `keys_disjoint`;
  - `commitTrie_spent`;
  - `rowStep_get_other`. It is replaced by `rowStep_get_out` (every slot, heads included). This corrects the PROPOSED text above, which said it stays.
- Kept: `view_row_out` (RowsComm). It is a lemma about RowsComm's private `view` model of inserts, never about `admit`, so the frame does not subsume it; the PROPOSED text's claim that it is deleted is withdrawn.
- Not built: `refuse_Frame` (a refusal keeps height and steps, so it cannot share a turn-shaped structure; `refuse_frame` stands), and the origin/allowance/height/steps fields (see above).
- Re-derived, in full: `admit_frame`, `admit_nullifiers`.2 and `admit_comm`'s cell reads. The PROPOSED text's "~22" was an overclaim.
- New on the rows side: `foldRows_get_out` and `dropHeads_get_out`. No `admit`-level rows frame existed before.
- The commit-map helpers moved down into Admit.lean / Rows.lean, so that the hub sits below Frame.lean's corollaries.
- Ratchet: `theorems` 3890 → 3891 (+1); `max dependents of a non-foundation module` 229 → 230 (`Codec.Raw` gains the new module as a dependent); `Lean proof-modules` +1.
- No premise is added anywhere. No definition changed. Nothing is re-emitted.

**Critique.**
- **The dropped-heads correction I gave ROOT was itself wrong.** `RowFoot.dropped` names only heads because `dropHeads` filters its listing to the retired cell's `.head` keys. That is a fact of the definition, not of `checkRowsRemain`, so a frame over bare `commit` could state it too; `dropHeads_get_out` uses no `Checked` fact. `checkRowsRemain` is what makes a retirement leave no orphan ROWS (`RowsOk`), which is a different claim. The scholar's sketch was right on this point, and my "correction" read a check where a definition was doing the work.
- **The ratchet did not fall.** The scholar counted "~22 hand restatements"; a grep finds only `admit_frame`, `admit_rom`, `admit_nullifiers` and the RowsComm twins. The "−9 RowsComm privates" belong to `check_local`, the locality half, which this commit does not build. Net +1: four for the hub and its teeth, three for the rows frame that had never been stated at `admit` level, against nine deleted.
- **`rowStep_get_other` was never the per-step lemma the rows field needs.** It covered rows only, so the heads frame had to be written.
- The reader's check: no field whose subject is the cells takes a premise.
- Locality (`check_local`, the RowsComm `touchCheck_congr` family) remains open. It is where the scholar's predicted fall actually is. Filed as a cv task.

### KERNEL-52 AS BUILT (KERNEL-19 / K19-H, 2026-10-19; ROOT approved)
- `Kernel/Proofs/Logic/HeadRead.lean` (94 lines; imports only Fold and TrieMap) holds `structure HeadSound (E) (S : Trie.Spec K V D) (Fits) : Prop`, with four fields: `body_inj`, `pair_inj`, `vdigest_inj` (up to `Collision`) and `coll`. It is Prop-valued, so closure C3 is green.
- The family over it:
  - `HeadSound.inclusion` and `.exclusion`, over any canonical trie;
  - `.head_read` and `.head_absent`. These take `head_roots`' conclusion and a selector `pick` of the four roots, so HeadRead sits below Cells and nothing moved for the cycle.
- Three records, each with its premises:
  - `cells_headSound (hE)`: the cell `InjOn` comes from `hE.cellBytes_injOn`;
  - `journal_headSound (hE) (hn : 0 < n)`;
  - `refusal_headSound (hE)`: `Fits` is `RefusalLeaf.Fits`.
- Twelve landed theorems are now one-line corollaries, with their statements unchanged (checked mechanically against HEAD over all 72 theorems of the three files): `slot_inclusion_sound`, `slot_exclusion_sound`, `head_read_sound`, `head_absent_sound`, `journal_inclusion_sound`, `journal_exclusion_sound`, `head_journal_read`, `head_journal_absent`, `refusal_inclusion_sound`, `refusal_exclusion_sound`, `head_refusal_read`, `head_refusal_absent`.
- `fold_head_roots` moved down to JournalHead, and `head_absent_admitted`'s 18-line inline copy of it was deleted.
- Not built:
  - Generic prove theorems: `Trie.prove_includes` and `prove_excludes` already are that statement.
  - Generic deployed forms: they were already one line each.
  - A rows instance: see the critique.
- Ratchet: theorems 3899 → 3906, hub 232 → 233, Kernel lines 22321 → 22385. No premise or statement changed. Nothing is re-emitted.

**Critique.**
- **The scheme did not pay on the ratchet.** The proposal predicted "~45 → 8 + 4", but with every landed name kept as a corollary (ROOT's condition 1) the count can only rise. Lines rose too: at three instances, the ~7 lines saved per instance do not cover a 94-line hub. What it buys is that the soundness argument exists once, and the next trie gets the whole family from a four-field record. It was still worth landing, but the prediction was wrong, and I wrote it.
- **There were three instances, not four.** I claimed RowsHead.lean was a fourth chain without grepping it. It is the `RowsOk` invariant and holds no head reads. This is the same failure as KERNEL-51's "~22": a count nobody grepped.
- **The rows cannot be an instance at all today.** `rowKeyBytes` writes the relation as `byte8 rel` and the key length as `byte8 k.size`, and both wrap at 256 (K19-READER3: `rel = 0` and `rel = 256` give one key), so `leafBody (rowSpec E)` is not injective and `Trie.inclusion_sound`'s unconditional `hL` is false for `rowSpec`. A rows phone read needs a key-predicate variant of the trie soundness theorems, and probably a verifier that refuses unfit keys. No deployed path verifies a rows proof today (reader K19-READER3: the receipt carries `rowsroot` only to rebuild `rootsDigest`, and range pins are re-executed), so this is not a live hole, and the encoding is fixed before the rows get a head read (cv task).
- Vacuity read K19-READER3: LAND. Its one amendment (the `rel` byte wraps too) is taken here and in HeadRead's docstring.

## KERNEL-53 · One signature verify per judgement: `judge` carries `submit`'s passing verify into the authentication (KERNEL-20, 2026-10-19; PERF-1 FINDING 3, routed by ROOT)

**The defect (measured).** A recorded refusal cost TWO Ed25519 verifies. `judge` ran `submit`, whose `receive` verifies the signature (`checkSignature`, Derive.lean), and on any error then ran `authenticated`, which verified the same signature over the same bytes again. Every follower's `auditRefusal` goes through `judge`, so the follower paid it too. PERF-1 saw it as 502 verifies over 500 steps with 2 stale refusals (`bench-count`). It is a law-5 cost on exactly the refusals the contention finding says honest writers produce.

**As built.**
- `Verdict.verified : Verdict D → Bool` (Kernel/Receive/Submit.lean): was `submit`'s verdict reached only past a signature that verified? `true` for every refusal `receive` made after its signature check and every rejection `World.admit` made; `false` for `wrongWorld`, `badSignature`, `replayed _`, `refusedFinal _`.
- `checkSignatureBy X c verified`: the signature check, or `.ok ()` when `verified`.
- `authenticatedBy X w c verified`: the world check, `checkSignatureBy`, `authKey`. `authenticated X w c` is now `authenticatedBy X w c false` (the same value; one definition, not two).
- `judgeBy X w c auth`: the one match (`submit`, then record when `auth v` and `World.refuse` takes it). `judge X w c := judgeBy X w c fun v => authenticatedBy X w c v.verified`. Nothing else changes; `auditRefusal` and `bench-count` inherit it.

**Theorems (Kernel/Proofs/Audit.lean).**
- `receive_checkSignature`: a `receive` that refused neither `wrongWorld` nor `badSignature` was reached through `checkSignature` passing.
- `submit_verified`: `submit X w c = .error v → v.verified = true → checkSignature X c = .ok ()`. **The carried bit is the same verify.**
- `authenticatedBy_verified`: for every verdict `submit` gives, `authenticatedBy X w c v.verified = authenticated X w c`.
- `judge_eq`: `judge X w c = judgeBy X w c fun _ => authenticated X w c`, the two-verify judge, for every call. `judge_recorded` now rewrites by it. Every other `judge` theorem keeps its statement. Two proofs elsewhere change one token each, `unfold judge` → `unfold judge judgeBy`: Protocol/Proofs/Settle.lean:30 (`judge_admitted`) and Host/Proofs/Serve.lean:54. These are CROSS-LAYER, with PROTOCOL-14 and HOST-13 asked.
- TOOTH `verified_eq_false_iff`: `v.verified = false` exactly for `wrongWorld`, `badSignature`, `replayed _`, `refusedFinal _`. A `verified` that were always `false` satisfies `judge_eq` and saves nothing; this refutes it, and it names the residue (below).
- TOOTH `authenticatedBy_verify_irrel`: with the bit carried, the authentication is the same under ANY `verify` (`rfl`): the carried check verifies nothing.

**Sim (kernel-sim).**
- `verifyingCtx X` marks every verify (`@`, through `dbgTrace`, the way `countingEnv` marks hashes).
- `record` re-judges each recorded refusal under it in bracket `<G`, before the `<F` hash bracket so that F's segment is unchanged. The PLANT `judgeTwice` runs in `<H`; it is `judgeBy … fun _ => authenticated …`, exactly `judge_eq`'s right side, not a hand copy. Both must record the same refusal.
- An exact check on every seed: `judge`'s verifies ≥ recorded refusals, and the plant's verifies = `judge`'s + the recorded refusals whose verdict carried the verify (`Verdict.verified`). This goes red both if `judge` verifies twice again and if it verifies zero times.
- Arm `verify-count:once` (in `plantedArms`): the plant counts more on a seed that recorded a refusal.
- MUTATION, proven by hand: with `judge` set to the two-verify form, seeds 0–3 each FAIL (e.g. "judge 90 and the plant 90 verifies over 45 recorded refusals, 45 carried"). The old judge cost exactly 2.000 per refusal.
- WASTE row `refuse verifies-per-refusal` = 1.000 (2640 recorded refusals over 64 seeds). It is new and pinned at 1.000.

**THE BAR.** `bench-count`'s `bar audit-verifies-per-step` stays 1.000. Its 60-record standing workload records no refusal, so it could not see this defect; PERF-1's 500-step run with 2 refusals now reads 500 verifies (by `judge_eq` + `submit_verified`: each recorded refusal makes exactly the verifies its `submit` made). PERF-1 is asked to re-measure with refusals present.

**Price, in premises on landed theorems.** None. No statement changes. `judge_recorded`'s proof changes one line (`unfold judge` → `rw [judge_eq]`). No cell, journal, refusals or rows reader is touched. No wire changes; nothing re-emits; nothing re-geneses.

**Critique.**
- *The residue is named, not hidden.* `badSignature` carries nothing. `Ctx.program` is a field (`checkInstall`, the law `judge`) that returns any `Refusal D`, so a `badSignature` verdict does not say that the signature verify failed, and `submit_verified` cannot be proved for it. Consequence: a call with a forged signature, which is DECLINED and never recorded, costs two verifies. It costs the Host a constant factor on spam, never a recorded step; `verified_eq_false_iff` is its exact boundary. The cure, if it is wanted, is a program-side refusal type that cannot spell the receive layer's names (so `badSignature` is attributable); filed as a cv task with the trigger "a measured forged-call flood", not done here.
- *Why not return the bit from `submit`.* `submit`'s result is named in about 20 theorem statements over 10 proof files (Kernel, Protocol, Host; grepped). Carrying the bit in its result would restate all of them to say what the verdict already says. The verdict is the carrier; `submit_verified` is the theorem that it is sound.
- *Why not hoist one verify before `submit`.* It would verify `wrongWorld` calls (now 0 verifies) and duplicate `submit`'s order in `judge`: a twin.
- Vacuity read (K20-READER): LAND-WITH-FIXES, with eight items. Items 1–6 confirmed the statements: `verified_eq_false_iff` refutes the always-false carry, `submit_verified` refutes the always-true one, `badSignature` is spellable by `Program` (Call.lean:292), and no pre-existing statement changed. Taken: (7) the exact per-seed check, since the arm alone was one-directional; (8) the single `judgeBy`, so the plant is the theorem's right side.
- *Meta-critique.* The first framing (in the queue) was "a `Verified` witness threaded from submit into authenticated". A witness type proves nothing the equation `judge_eq` does not, and costs a type change; the equation plus the iff is the smaller object that pins both halves (sound, and not vacuous).


## KERNEL-54 (PROPOSED) · Honest contention must not spend the spam budget: the shape of the refusal budget for `stale` (KERNEL-20, 2026-10-19; PERF-1 FINDING 2, cv 01a14edf-6f12; attempt-side meaning co-signed by PROTOCOL-15). DESIGN ONLY until ROOT rules.

**The defect (measured by PERF-1).** Concurrent writers on shared objects get `refused stale` on 0.75–4.25 % of writes (N=400, 3 actors, 3 runs). Each such refusal is recorded (it must be final: the A→B→A class, KERNEL-44), and each recorded refusal spends one of the member's `Bounds.refusalsPerWindow` = 16 per window of 1024 heights (`checkRefusal`'s last line). At N=1000 an honest member reached `declined refusalBudget`. Its next refusal, of ANY class, is then declined: not final, no receipt binds it, and the client can no longer tell a final refusal from a lost one. The budget exists against a flood (an authenticated member signing refused calls to grow the log), and honest optimistic concurrency is spending it.

**Why stale cannot simply be exempt.** A `stale` is any pin that does not match (`touchCheck`: `pinOf E cur = x.seen`, a content digest; rows: `rowPin`, `rangePin`). A member can pin any digest it likes, so stale is attacker-producible at will. Exempting it unbounded turns the flood bound into no bound. (Read: World.lean `touchCheck` :823, `pinOf` :306.)

### Option (A) · A second, separate contention budget for `stale`
- `RefusalSlot.count m win` gains a class (`spam | contention`), or a third key kind `.stale m win`. `checkRefusal` charges a stale record to the contention count (`< stalePerWindow`) and every other class to the spam count (`< refusalsPerWindow`).
- The kernel must know which records are stale. Either `Refused` gains a class bit derived by `refusedOf` from the verdict (so `auditRefusal`'s `r' = r` audits it), or the kernel fixes `staleCode` and Receive proves `Verdict.code (.rejected (.stale _)) = staleCode`. The bit is the smaller coupling.
- `stalePerWindow` is sized to contention. Honest stale per member per window ≤ the member's writes in the window × the contention rate. At 1024 heights per window and a measured 4.25 %, a member writing every height would see ~44 (ARITHMETIC, not measured); a hot object with many writers pushes the rate towards 1. Any constant moves the cliff and does not remove it.
- **Price, in premises (grepped).** No theorem gains a premise. These statements gain a class argument: `refusalCount` and with it `checkRefusal_facts`, `refuse_facts`, `refuse_refusalAt`, `refusalCount_le`, `refuse_refusalCount`, `admit_refusalCount`, `fold_member_refusals`, `fold_member_refusals_le` (the flood bound becomes 16 + S per member per window), `commitRefusal_refusals`; the KERNEL-50 family `refusedIn`, `CountedOk`, `refusalsCounted_iff`, `refusalCount_eq_of_counted`, `refusalsCounted_moved*`, and `refusalTally_get`/`tallyAt_*`; Codec `refusalFits` per class, plus the WorldTooth count teeth (`world_refuses_past_window_count`, `world_refuses_zero_count`, `world_refuses_misfit_count_key`). In all, 22 Kernel/Codec/Host statements (stmts grep, `refusalCount|refusalsPerWindow|refusedIn|CountedOk|refusalsCounted`). No cell, journal or rows reader is touched.
- Flag day `kernel!`: the refusal key wire (and the leaf if a class bit is added) moves; CODEC re-emits refusal-order, refusals, refusals-counted and every World tag; re-genesis.

### Option (B) · The spam budget counts only non-stale classes; stale is bounded by something structural
- Candidates for "structural": (B1) stale records per member per window ≤ k × the member's admitted turns in that window ("contention credit": an attacker pays with priced, admitted turns). This puts a per-member admitted-turn counter on EVERY admission: one more refusals-trie insert per admitted turn (~11 hashes at today's `hashes-per-refusal`) on the hot path, to save work on 1–4 % of writes. It is the wrong trade and I do not recommend it. (B2) Per (member, object, window): it does not bound a flood, because the attacker names any object.
- Price: the same statements as (A), and (B1) adds an admit-side count to `admit_*` frame statements (`admit_Frame`'s refusals field would no longer be "unchanged by admit"). That is a premise spread into KERNEL-51's frame. Refused on price.

### Option (C) · Make `stale` final WITHOUT a record: pins name a monotone version
- **Root cause.** A stale refusal is recorded only because a content pin can recur (A→B→A). If a pin names the cell's version (a counter bumped by every write, or the height of its last write) as well as its digest, a pin that is stale once is stale for ever: no reachable World has that version again. A stale refusal is then final by monotonicity. It need not be recorded. It costs no step, no 11 hashes, no 527 log bytes and no budget. The budget question disappears for the one class honest clients hit, and (A)'s cliff never exists. This is the version discipline of object-versioned ledgers (an input that names an old object version can never execute).
- What it touches (GREPPED counts; shape ASSUMED until a lane reads each site):
  - `Cell`, or `Entry.live`, gains a version, so `cellBytes` and `pinOf` change (pinOf: 40 lines in 12 files; cellBytes: 25 lines in 12 files). `postWrite` bumps it. A tomb already makes absence non-recurring after a birth.
  - Rows: a row can be inserted, retracted and re-inserted, and a range listing can return to an old value. Each relation head needs a mutation counter in the range pin (rowPin: 29 lines in 8 files; rangePin: 57 lines in 10 files). Theorem statements naming pinOf/rowPin/rangePin: 27 (Kernel Admit 5, Rows 6, RowsRange 5, RowsComm 2, RowsRangeDeployed 1; Codec Rows 4; Protocol Command 4).
  - `judge` declines `.stale` instead of recording it. Kernel `World.refuse`/`checkRefusal` are untouched, so no refusals theorem changes statement. The A→B→A tooth survives as a theorem: a call stale at a World is stale at every World its fold reaches (`stale_forever`, from version monotonicity).
  - PROTOCOL: an unrecorded stale is accountable only if the answer is self-certifying. The refused answer carries the pinned cell's inclusion proof against a served head, showing version > the pin's. The client checks it, and `stale_forever` makes it final. This is where PROTOCOL-15 must co-sign the attempt-side meaning: "refused stale, proven" is final like "recorded", without a record.
  - Cell readers: a version field must not put a premise on the ~150 cell theorems (the lesson of KERNEL-49's price). It is a field of the value, so `get_insert` and the Frame cells field are unaffected (ASSUMED; the first lane task is to measure it, by statement diff).
- Flag day `kernel!`: cell bytes, pins, the turn wire (touch.seen), rows head and range pins, CODEC vectors, PROTOCOL's refused answer, re-genesis.
- What it does NOT fix: refusals of other classes that depend on unpinned World state (allowance, relation fullness, birth ids, budget) are still recorded and budgeted. Their honest rate is not measured; PERF is asked to measure it by class.

### Recommendation: (C), and not (A) first
(A) is a containment that keeps a cliff: an honest member under heavy contention still reaches its stale budget, and the flood bound gets weaker (16 + S). (C) removes the reason stale is recorded at all, so it removes the cost along with the budget spend. By CLAUDE.md, the size of (C) (a re-genesis and a pin wire change) is not a reason to ship (A) first and call (C) a later phase. Order of work if ROOT rules (C): (1) a lane reads every pinOf/rowPin/rangePin statement and measures the premise spread of a versioned value, before any code; (2) KERNEL lands version + `stale_forever` + judge declining stale, `kernel!`; (3) PROTOCOL's proof-carrying stale answer, with CODEC's vectors.

**Questions for ROOT.** (i) (C) over (A)? (ii) The version as a per-cell write counter, or as last-write height? The counter is smaller on the wire; the height is already in the World and makes "how stale" readable. My lean is the counter. (iii) Should a stale answer carry its proof always, or only on request (a `lookup`)?

**Critique of this proposal.** The brief stated "a stale refusal MUST stay recorded". (C) disputes that premise instead of choosing within it, so it is marked here as a premise change, not smuggled in. Its risk is the unpriced half: the rows head counter and the proof-carrying answer are ASSUMED shapes. The measured parts are the defect, the call sites and the grep counts.

### KERNEL-54 STEP 1 · Measured (lane K20-MEASURE, read-only at main 9df02da; hbox logs/kernel20-measure.md, per-statement labels logs/k20m-class-full.txt)
- No cell or row leaf holds a height today (heights live only in journal and refusal leaves). Both shapes add a field.
- Premise spread over 356 statements (the 27 that name pinOf/rowPin/rangePin, plus every cell and row reader):

| Shape | unchanged | shape only | gains a premise |
|---|---|---|---|
| N, a per-cell counter | 286 | 70 | **0** |
| H′, last-write height with births at 0 | 283 | 70 | 3 |
| pure H | ≤281 | 70 | ≥5 |

- Why H costs premises:
  - It makes `touchCheck` depend on `w.height`. `admit_comm`'s cell conclusion then fails whenever a turn writes, and `check_after` and `touchCheck_congr` fail with it.
  - Pure H also breaks `rowsRun_comm` and the Sim gate `rows-two-rains:both`.
  - H needs a new World invariant (version ≤ height), its fold theorem, and a CODEC refusal.
- Unchanged in both shapes: Frame cells/rows, `get_insert`, `E.Lawful`, `cellBytes_injective` (the version is not in `cellBytes`), `Value.ofCell`, and every reader that goes only through `w.live`.
- WASTE:
  - Trie hashes per insert are unchanged.
  - A fixed 8-byte field breaks HOST-14's base-bytes bound: 3.912 → ~4.18, against a bound of 4 (arithmetic). A varint costs about +0.9%.
  - Each stale no longer recorded saves 527.2 B, 11.41 hashes, one step and one budget unit.

## KERNEL-54 RULED (ROOT, 2026-10-19, on the measurement): shape N as a varint, W0, all three amendments
**Ruling.** Shape N: a per-cell write counter, encoded as a VARINT.
- It lives in `Entry.live`, not in `Cell`: putting it in Cell would move `cellBytes`, `romIdOf`, the creates wire and `Value`.
- Every row leaf carries one too, and each rows head carries a floor.
- A version past the counter limit is refused by name (`ver + 1 < counterLimit`).

ROOT's prior was the last-write height. It loses on the measurement: 0 premises against 3–5, and pure H breaks `admit_comm` and `rows-two-rains`, which decides it.

**Amendments.**
1. **The pin reads the Entry.** Today `pinOf` reads `w.live`, which maps a tomb to `none`. So never born → born → retired reproduces the absent pin, an A→B→A that today only the stale record covers. With the pin reading the Entry, absent, tomb and live are three distinct pins. A tomb needs no version, since nothing removes a cell entry. TOOTH: exactly that sequence under the old `pinOf`.
2. **Stale splits into BEHIND (final) and AHEAD (not final).** My "stale for ever" was false as worded: a pin can name a future state, and the next version is predictable. It is stated in the W0 form: a pin observed at an earlier World of the same fold that is stale now is stale at every World the fold reaches (`stale_behind_forever`). Nothing changes on the wire; the follower judges against its own fold, which fits PROTOCOL-46 "follow settles" and KERNEL-44 "no host key". PROTOCOL-15 co-signs the attempt side: an AHEAD stale settles `open`, a BEHIND stale settles `refused`, both from the fold. W1 (the version in clear in the pin, so a party outside the fold could judge) is NOT built. It is filed as cv 01a14fc3-d848 with the trigger "a member holding a head but no World", linked to PROTOCOL-46's declined HOST half.
3. **Rows.** A relation head carries a monotone floor, bumped by retracts only, so inserts keep commuting. The absent-row pin and the range pin read it, from the World before the turn (`rowStep` sees rows the same turn already changed). World.lean:1022 is the retract of an absent row whose pin MATCHED, the one `.stale` that is not a pin mismatch; it is renamed to its honest name (`missingRow`). The two synthetic `.stale 0` records in Host/Sim/Run.lean change code.

**Receive.** `judge` DECLINES stale, which is never recorded. `auditRefusal` refuses a recorded stale by name.

**What stays recorded.** KERNEL-44's records REMAIN for every class that is not structurally final (lawDenied, noGrant, relationFull, the budget, …), and for Ember's reason: they were system interactions. (C) takes stale out of the record; it does not remove the record.

**Flag day (`kernel!`).** These move: the entry codec, the row-leaf codec and the range pin; every vector that embeds a pin (touch, turn, unsigned, call, refused, step); the carried and whole-World vectors. Every Store re-geneses. About 18 client pin sites switch to reading the Entry. Routing:
- CLIENT-8: the client half.
- ROOT for CODEC and LANG: the two table rules.
- PROTOCOL-15: the A→B→A journey rewrite in Protocol/Rows.lean (709–742) and the attempt side.
- HOST-14: the base bound and Host/Sim.

**WASTE.**
- The ±1% re-pins of hashes-per-touched-cell and the row hash rows, because every pin digest changes.
- The seal bytes rise, with the varint's cost stated.
- `refuse` rows fall as stale leaves the record.

**Process.** Stage the kernel half. The reader lists every changed statement, and 0 cell readers gain a premise (checked). Each partner's half routes before landing, as on the refusals and rows days.

## KERNEL-54 AS BUILT (KERNEL-20 phase 1 by K20-K; KERNEL-21 phase 2, 2026-10-18) · ROOT's further rulings, the partners' halves, and what the proofs changed
**ROOT's rulings on phase 1 (all taken).** (a) `live_inclusion_sound` and `deployed_live_inclusion_sound`: the claimed-leaf hypothesis Cell.Fits → `(Leaf.entry (.live cell v)).CellFit Cell.Fits` (= Cell.Fits ∧ v < 2^64), conclusion `w.entry = some (.live cell v)`: THE one cell-reader statement whose hypothesis changed, strengthened, not added. (b) private `setHead_inv` gains `hfl : floor' < counterLimit`. (c) the rows/range stale theorems carry a parent disjunct (sharpened below), with a tooth for the dropHeads reset; the measurement note "the floor never resets" was false as a pin value and is corrected here. Weight charges the BOUND (`counterWeight` = 8 B per version, law 4); disk carries the varint; the base-bytes rows measure the actual (HOST-14: 3.895 / 3.821 / 3.912 at seeds 1–3, under 4). The +1 rejection-code shift (missingRow appended; the receive refusal staleRecorded appended) and three WASTE rises are accepted, reason "the version field".
**PROTOCOL-15's five conditions (co-signed, PROTOCOL-16 built them):** BEHIND → refused / AHEAD → open, both from the member's own fold; an unplaceable planning World → open; an absent lookup is confirmed with follow before any resend; the rows budget teeth move to a recorded class (16 recorded keyTaken); Protocol's pin sites read the Entry, and Protocol/Rows.lean's A→B→A journey is rewritten (a raced write is declined stale, rerun settles refused stale from the fold). ROOT kept the admitsRecorded tooth on the unpinned row-birth instance (relationFull, retract frees the slot, the same signed call re-submitted).
**What the proofs found, and the owner's rulings (KERNEL-21).**
- `Collision E.hash` (∃ dom a b) is provable from `E.Lawful` by pigeonhole (logs/kernel21-ver-pigeon.lean), so a conclusion `… ∨ Collision E.hash` binds nothing (cv 01a1501e-d6bc; KERNEL-56 restates every site). KERNEL-54's new theorems therefore conclude `CollidesAmong E.hash S` (Kernel/Proofs/Versions.lean): a collision among an explicit list S of (domain, bytes) inputs built from the theorem's own Worlds (`pinPre`, `rowPre`, `leafPres`, `rangePre`, in Kernel/World.lean beside the pins they describe; `pinOf_eq_pre`, `rowPin_eq_pre` by rfl). A hash that separates S refutes the disjunct.
- As phase 1 stated them, `row_stale_behind_forever` and `range_stale_behind_forever` were FALSE: under an unlawful `Ord`, `[retire p, write p]` passes `checkShape` (firstDup needs a lawful compare), dropHeads resets the floor and p stays live (logs/kernel21-ver-ordcx.lean); with rel ≥ 256 `rowsPrefix` writes rel % 256 while the floor is read at rel (logs/kernel21-ver-relcx.lean). Both gain `[Std.TransOrd D] [Std.LawfulEqOrd D]`; the range one gains `rel < 256`, `pre.size ≤ width < 256` (what `checkRanges` admits). New statements only; no landed theorem gains a premise. The cell theorem dropped an unused `E.Lawful`.
- The parent disjunct is `w'.entry E parent = some .tomb` (the reader's sharpening of ROOT's `w'.live … = none`: an absent parent can still be born; a tombstone cannot).
**Statements (second-agent reader K21-READER: LAND-WITH-FIXES, every fix taken).** 73 changed theorem statements (72 from phase 1, none moved by the proof lanes, checked against the reconstructed phase-1 tree; `RowsRange.listed_key` private → public); 11 new public theorems. Class (c), beyond (a) and (b): private `RowsComm.touchCheck_congr` (`w'.live = w.live` → `w'.entry = w.entry`, forced: touchCheck reads the entry). Tightened by DEFINITION with unchanged text: `Leaf.CellFit` (+ v < 2^64: slot_inclusion_sound, head_read_sound, leafBytes_inj, leafDigest_inj, cells_headSound, the deployed head reads) and `rowFits` (+ floor, ver < counterLimit: admit_range_exact*, range_rows_*, listed_key, head_sum, admit_comm_rows, rows_ext …), all discharged by the existing fold invariants (fold_cellsFit, fold_rowsOk, through the new `overBound .version` checks) and by CODEC's decode. `admit_comm`, `rowsRun_comm`, `admit_comm_trie`, `admit_comm_rows` unchanged (inserts never move the floor).
**Teeth.** `pinOf_old_recurs` (the content pin recurs never-born → born → retired; pinOf does not); `rowPin_old_floor_recurs` (the dropHeads reset: the old absent-row pin recurs after the parent retires, its entry a tombstone, and every touch of the row is refused orphanRow / rowParentUnpinned, never admitted); `rangePin_floorless_recurs` (insert then retract under a LIVE parent: the floorless range pin returns to w₀'s, the real one does not); judge_stale_declined / judge_recorded_not_stale / auditRefusal_stale against the sim marks refusal-aba-declined, refusal-stale-audit; rows-aba-floor, rows-aba, rows-missingRow.
**Critique.** The proofs took one lane-day and found two false statements and a vacuous disjunct: phase 1's "final statements" were final in shape, not in truth, and the measurement that priced the day counted premises on landed theorems but could not see a missing premise on a new one. The concrete-collision form costs every new statement a preimage list; that is the price of a disjunct that can be refuted.
**Meta-critique.** I ruled the two premise additions myself as owner (new statements, no landed premise). The test of that ruling is ROOT's rule "a design's price includes every premise it adds to landed theorems": it adds none; the instance premises are what every rows theorem over a decision procedure already assumes (Budget, Ledger), and the shape premises are exactly checkRanges's admission. Had the counterexamples been against the kernel's behaviour instead of the statement, this would have been a HOLD.


## KERNEL-56 · Every hash escape names its inputs: `Collision`, `Trie.Coll` and `HashColl` are deleted, and every consumer concludes `CollidesAmong hash S` over a list S built from its own objects (KERNEL-21, 2026-10-18; found by the KERNEL-54 proof lane, cv 01a1501e-d6bc; ROOT-ruled)
**The defect.** `Collision hash := ∃ dom a b, a ≠ b ∧ hash dom a = hash dom b` (Kernel/Proofs/Fold.lean), `Trie.Coll` (the same over trie inputs) and `HashColl E dom` (Origin.lean, one domain) are each PROVABLE from `E.Lawful`: a lawful digest has a fixed size ≤ 32 with injective bytes, so `D` is finite, and infinitely many byte strings into a finite type collide (logs/kernel21-ver-pigeon.lean). Every theorem concluding `… ∨ Collision E.hash` was therefore true whatever the fold did: chain_binds, fold_head_binds, fold_reaches_host, the head-read, inclusion and exclusion results for cells, journal and refusals, their deployed corollaries, genesis/carry origin injectivity, account keying. None bound anything. This is the apex-vacuity class (memory: "Every instrument blind to the next wound"): the statements had been read for their arithmetic, never for whether their escape was satisfiable by itself. Protocol had noticed for its own receipts (decisions/protocol.md:1406) and stated a concrete disjunct; the kernel had not.
**The fix (ROOT's ruling).** One predicate, `CollidesAmong hash S := ∃ p ∈ S, ∃ q ∈ S, p ≠ q ∧ hash p.1 p.2 = hash q.1 q.2`, where S is a finite list of (domain, bytes) inputs the theorem itself builds: the bytes the presented proof hashes and the bytes the trie hashed along the key's path (`climbPres`, `pathPres`), a chain's link inputs along its steps (`chainPres`, `foldPres`, built with `World.step`), a head's roots inputs (`rootsPre`, `headPres`), a leaf's (`leafPre`, `journalPre`, `refusalPre`), an origin's (`originPre`, `carryOriginPre`, `World.genesisPre`), an account's (`accountPre`). A hash that separates S refutes the disjunct, so the theorem's other disjunct is what it says. Each family has a tooth: `Separates hash S` (the hash is injective on S) and `<theorem>_sep`, the binding fact with no escape (`hs.elim (main …)`); `Separates` is satisfiable (`separates_of_injective`, a toy injective hash). The S-builders are definitions and live in def modules beside what they describe (Kernel/Trie.lean, Kernel/World.lean, Kernel/Receive/Follow.lean, Kernel/Receive/Ledger.lean; closure C3); `CollidesAmong`, `Separates`, `Trie.CollAmong`, `HeadSound` are Props and stay in proof modules. `HeadSound` (the one authenticated-map scheme, KERNEL-52) is reshaped: its escape fields are replaced by `hash_eq`, `vdigest_eq`, `vpre_inj`, so an instance carries no escape.
**Premises.** None added. Conclusions changed only in the escape. Three refutation theorems whose conclusion WAS the escape (head_absent_admitted, head_refused_not_absent, deployed_head_absent_admitted) now have teeth stating the binding fact directly (the exclusion proof does not verify). Statements outside Kernel: Protocol/Proofs/Receipt.lean's five receipt checks, S = [the receipt's roots input, the World's roots input, the read's inputs]; LEDGER's account_keyed / deployed_account_keyed (ROOT for LEDGER).
**What it does not move.** No definition a node runs changes value, no wire, no hash input, no vector: nothing re-geneses, nothing re-emits.
**Critique.** The restatement doubles as the cheapest audit the kernel has had: every escape now has to name what it compares, and a theorem whose proof cannot name its colliding pair does not compile. Its cost is statement size (S lists, threaded through the trie helpers). **Meta-critique.** This was found because a proof lane tried to close a sorry honestly and noticed it could close it in one line. Green builds, census, and two earlier vacuity reads all passed these 61 statements; the reader rule ROOT added ("a disjunct provable from the premises alone, or from the instance, is vacuous") is the instrument that would have seen it, and it now runs on every reader brief.


## KERNEL-55 (PROPOSED; RULED and BUILT below, parts 1 and 2) · A create's bytes, and what `worldBytesMax` protects: one potential theorem, a derived bound, and two writer paths that reach it today (KERNEL-20 / K20-P55, 2026-10-19; PERF-2's item-2 lead, routed by ROOT; HOST-14 to co-sign). DESIGN ONLY until ROOT rules.

Tags: MEASURED = grepped or read at main a18d6ea (or read in a log); ARITH = computed from measured numbers or definitions; ASSUMED = not checked.

**The defect (measured by PERF-2, re-read here).**
- `bench-worstworld` (draft, wt/perf) births cells from one member until submit refuses. MEASURED (PERF-LOG.md, `logs/perf2-ww2.log`):
  - 60 KB cells: `overAllowance` after 743 births. World 44,702,268 B (0.167 of `worldBytesMax`), weight 44,646,433, allowance left 25,241.
  - 16-byte cells: `overAllowance` after 204,288 births. World 22,247,840 B (0.083), weight 21,450,546, allowance left 512, encoded/weight 1.037. The segment at the last seal is 119,636,228 B.
- Charge per birth (ARITH):
  - 60 KB: 180,609 B. The cell is 60,057 B (60,000 + 2 slot headers + the 32-byte owner slot + 9), and 3 × 60,057 = 180,171, plus 438 fixed.
  - 16 B: 657 B, against 105 B of World per birth. The World is 16 % of the charge.
- So `worldBytesMax` (2^28, Host/Bounds.lean:87) is never reached by these folds. Two docstrings state ratios that the code does not have (MEASURED):
  - Host/Bounds.lean:80: "256 MiB is ~900 BAR stores". ARITH: 2^28 / 290 KB = 925. That is a division, not a reason.
  - Host/Bounds.lean:92–95: `allowanceMax := worldBytesMax / 2`, "the other half is headroom for the encoding's per-entry overhead over `World.weight`". The measured overhead is 0.1 % (60 KB) to 3.7 % (16 B). The other half is in fact spent by the LOG half of the charge.
- Kernel/Proofs/Weight.lean:8 and :446 say "HOST-14's `worldBytesMax` is the genesis allowance", and KERNEL-18's title says the same. That is false too: `fold_world_weight` bounds `World.weight` by `w.weight + w.allowance`, which is not the encoded size, and `worldBytesMax` is twice the allowance.

**Two writer paths reach `worldBytesMax` today. It is NOT only the reader's bound.** ROOT's framing ("the reader's bound, not the writer's") holds for genesis Worlds and small founder sets only.
1. **Import.** MEASURED: `host import` (Host/Cli.lean:215 `importWith`) bounds the carried file by `carriedMax` and checks KERNEL's `CarryFits`. `CarryFits` (Kernel/Proofs/Carry.lean:37) bounds only `cellsWeight + rowsWeight + allowance < 2^64`. Nothing compares the carried allowance with `allowanceMax`. A carried World with allowance 2^40 imports, its members grow it past 2^28 by admitted, acknowledged turns, and the next seal refuses `worldTooLarge`. MEASURED (Host/Sim/Run.lean:25, plant-world-too-large): the loop then stops `sealFailed worldTooLarge`. ASSUMED, not run: every restart re-folds the tail and fails the seal again, so the Store is wedged, not refused by name. CHARTER law 5 asks for "a `worldBytesMax` bound that refuses by name where the design must change". A whole-Store stop after acknowledged turns is not that.
2. **The refusals trie is in the encoded World, but in neither `World.weight` nor the charge.**
   - MEASURED: `World.weight` is `cellsWeight + rowsWeight` only (World.lean:665). Recorded refusals are not charged (KERNEL-44: rate-limited instead). The trie keeps a refused call while `H < h + 2·windowMax`, pruned at window multiples (`keptRefusal`, World.lean:1214), so up to three windows' records. Each member records at most `refusalsPerWindow` = 16 per window (`checkRefusal`).
   - ARITH from Codec/World.lean's refusal wire: a tx entry is 1+32 + 1+8+8+32 = 82 B, and a count entry 1+32+8 + 1+8 = 50 B. That is ≤ 48·82 + 50 = **3,986 B per member**, uncharged.
   - Membership is ≤ 257 × founders (KERNEL-20's critique, decisions/kernel.md:396). That is prose, not a theorem (grepped: no statement names `enrollMax`). `GenesisFits` allows founders up to 65,536.
   - At 64 founders the term is 16,448 × 3,986 = 65.6 MB (ARITH). ASSUMED, at ~900 B charged per enrolment: the allowance pays for ~149k members, so a World with ≥ ~580 founders can be driven past 2^28 by refusals alone, every turn admitted.
   - The kernel itself does not tie `r.member` to a member cell. It bounds per `D`, and `Receive.judge` authenticates. So no kernel-level fold theorem bounds this trie at all today.

### (a) Is the triple payment of a create intended? Yes. Each copy is bytes the Store holds. No copy is counted twice.

| Copy | Where it lives | What it pays for |
|---|---|---|
| `event.size` (in `Turn.logWeight`) | seg.log, forever. MEASURED: seg.log is append-only with no rotation or compaction (decisions/host.md:2344). | The signed call: the authority evidence every follower re-verifies and re-derives from (`rederive`, `eventMismatch`). The kernel never parses it. A data create's call carries the slots, so the bytes are there. ASSUMED in general: a method may create a large cell from a small call, so "×3" is the data-create case, not a kernel invariant. |
| `creates` (in `Turn.logWeight`) | seg.log, forever | The derived effect, so `World.admit` alone replays the log (the writer's reopen fold, thin consent) without running receivers or verifying. CODEC proves the record is exactly `logWeight` bytes (`turnBytes_size`, Codec/Proofs/Deployed.lean:66). |
| `Turn.growth` | the World, and every base file each seal rewrites | The resident copy. `admit_world_weight` proves the World grows by exactly `growth − credit`. |

- **Verdict.** The charge is what KERNEL-12 said it is: record bytes plus World bytes. `turnBytes_size` and `admit_conserves` already pin both halves as equalities, so there is no double count, and no defect tooth is owed for (a).
- **What IS wrong is the claim "the allowance budgets the whole Store".** It undercounts. It is never a double count:
  - **Record framing.** ARITH from perf2-ww2: segment 119,636,228 B over Σ`logWeight` 112,766,670 B is 1.061, or ~33.6 B per turn of step tag and root digest outside the turn's bytes.
  - **Recorded refusals.** Their log records are uncharged. Each is up to 2·32 + 3·8 + 4 + `callMax` (64 KiB) B, ≤ 16 per member per window. So seg.log growth from refusals is bounded per window of admitted turns, but not by the allowance.
  - **`index.log`.**
  - The fix is to say it right: "the allowance budgets turn records and `World.weight`". The refusal-log growth is KERNEL-44's / KERNEL-54's to price, and is raised as Q5 below, not decided here.
- **Do not de-duplicate the log by dropping `creates` or `event`.**
  - Dropping `creates` makes every reopen and every thin replay run receivers and verify one signature per step. That is HOST-14's cold-reopen budget, measured.
  - Dropping `event` deletes the signature, and with it the audit.
  - Restating a created cell's bytes only once would need the kernel to parse events (law: the event is opaque).

### (b) What `worldBytesMax` protects, and its honest value

**It has two jobs (MEASURED uses):**
- **Reader bound.** Before decoding an untrusted World, it bounds the memory a decode may take:
  - open refuses a base frame past `baseRecordMax` before reading (`Base.read_file`, Host/Proofs/Genesis.lean);
  - import reads at most `carriedMax` (Cli.lean:192);
  - the follower's download is bounded by it (Host/Follow.lean:100).
  - This job holds whatever any allowance says. A decoded base may claim anything up to it, so PERF-2's adversarial reopen must be benched at it.
- **Writer's last line.** The seal refuses `worldTooLarge` (`Base.file`, `Base.seal`; Host/Base.lean:225, :264). HOST-41's law keeps that refusal: every encode refuses over the bound its decode enforces. On the writer path it must be **provably unreachable**, because reaching it is a wedge. Today it is reachable (the two paths above).

**The theorem that makes it honest: a potential, not a ratio.**
- ARITH from the definitions in Kernel/Turn.lean. For every turn, **`61 · t.growth ≤ 76 · t.logWeight`**, term by term:
  - a create costs the same `digestWeight + cell.weight` in both;
  - a write's `opsWeight` is ≤ its `Act.logWeight` (+5);
  - a nullifier costs 32 in both;
  - an insert or upsert has growth = log − 1 (or −33);
  - **a declare** has growth `s + 42` against log `s + 27`, with `s = RowSlot.weight ≥ 34`, so 61(s+42) ≤ 76(s+27) ⟺ s ≥ 34. **Tight at a head.** The 15-byte gap is the head's `count` and `sum` counters, which the log does not carry. This is the one place a turn adds more World than log.
- Then **Φ = 137 · weight + 76 · allowance never rises over any fold**:
  - per turn, ΔΦ = 137(g − cr) + 76(cr − L − g) = 61g − 76L − 61cr ≤ 0, where `cr` is all credit back (`admit_world_weight`, `commitWith`);
  - a refusal step leaves weight and allowance unchanged (`refuse_frame`).
- Proposed statements, all NEW (Kernel/Proofs/Weight.lean):
  - `Turn.growth_le_logWeight : 61 * t.growth ≤ 76 * t.logWeight`;
  - `admit_potential` and `fold_potential : 137 * w'.weight + 76 * w'.allowance ≤ 137 * w.weight + 76 * w.allowance` (premises exactly `fold_conserves`'s: `Canon`, `Slotted`, `RowsCanon`);
  - corollary **`allowance_bounds_world : 137 * w'.weight ≤ 137 * w.weight + 76 * w.allowance`**, the form ROOT asked for, with f(A) = 76A/137 ≈ 0.5547·A.
  - The loose form, `fold_world_weight` (weight ≤ w.weight + A), stays: it is `fold_potential`'s weakening.

**The encoded size, as CODEC's owed equality** (KERNEL-18's critique and Host/Bounds.lean:95 both say "CODEC's `size ≤ c · weight` is not yet a theorem").
- ARITH from Codec/World.lean, ASSUMED one byte per `choice` tag:
  - a live cell entry is `weight + 3` on the wire (slot tag, leaf tag, entry tag);
  - a tomb is 35 against weight 32;
  - a spent nullifier is 34 against 32;
  - a rows entry is exactly its weight (`rowKeyBytes` / `rowLeafBytes`);
  - a journal entry is 72 B, ≤ 3·`windowMax` entries;
  - plus the refusals and a fixed tail (height, steps, chain, allowance, origin, four list headers).
- This agrees with both PERF-2 runs:
  - 60 KB: 743·3 + 743·72 + ~104 fixed = 55,829, against 55,835 measured;
  - 16 B: 612,864 + 2,048·72 = 760,320, against 797,294. **36,974 B (0.17 %) unexplained**, flagged.
- Proposed: `Codec.Kernel.world_size_eq` (an equality in entry counts, CODEC's style like `turn_size_logWeight`). Its corollary: `size ≤ 35·weight/32 + 72·journalMax + refusalsBytes + worldFixed`.

**The refusals term needs a bound before any f exists.** This is a fork (Q2):
- **(R1) A kernel-wide cap.** `Bounds.refusalsPerWindowMax` (C), checked in `checkRefusal` beside the per-member one, refused `refusalBudget`.
  - Bound: ≤ 3C tx entries + C counts, so refusalsBytes ≤ 3C·82 + C·50. At C = 16,384 that is 4.85 MB (ARITH).
  - It is a kernel fold theorem with no receive premise.
  - Cost: past C, one flood of colluding members leaves everyone's refusals unrecorded until the window turns. That is a liveness cost on refusal finality, never on admission.
- **(R2) Per member, as now.** Bound: 3,986 B × members-ever. It needs two theorems:
  - a Receive-level "a recorded refusal's member is an enrolled member", over audited logs, not `World.fold`;
  - the membership bound ≤ 257 × founders (prose today).
  - Plus a Host `foundersMax`. The term is 2.0 MB at 2 founders, 16.4 MB at 16, 65.6 MB at 64.
- KERNEL-54 (the stale budget) changes the per-member shape either way: whatever it rules, this term must follow it.

**The honest value (ARITH, deployed `allowanceMax` = 2^27, genesis weight ≈ 0, journal 221,184 B):**

| Route | World weight max | Encoded max | / 2^28 |
|---|---|---|---|
| loose (`fold_world_weight`), R2 at 2 founders | 134,217,728 | 149.1 MB | 0.555 |
| potential (Φ), R2 at 2 founders | 74,456,549 | 83.7 MB | 0.312 |
| potential, R2 at 16 founders | same | 98.0 MB | 0.365 |
| potential, R2 at 64 founders | same | 147.2 MB | 0.548 |
| potential, R1 (C = 16,384) | same | 86.5 MB | 0.322 |

The existing 2^28 happens to be sufficient for small founder sets even under the loose theorem, but for neither stated reason. The headroom it carries is not derived.

### Options
- **(A) Prose only.** Delete the two ratios and write the two jobs. Keep 2^28.
  - Leaves both writer paths (import, refusals), and the bound stays an undocumented 1.8–3.2× slack.
  - Rejected: a refusal that wedges the Store stays reachable.
- **(B) Derive `worldBytesMax` from the allowance.** Primary `allowanceMax` = 2^27 (the useful life KERNEL-15 set).
  - `worldWeightMax := genesisReserve + 76·allowanceMax/137`.
  - `worldBytesMax := 35·worldWeightMax/32 + 72·journalMax + refusalsBytesMax + worldFixed`, about 84–87 MB.
  - Host checks Φ at genesis AND import: `137·w.weight + 76·w.allowance ≤ 137·worldWeightMax`. Refused by name, as a Host refusal before `genesis` writes.
  - An exported World from any honest lineage passes, because Φ never rises. Only a forged or foreign budget is refused.
  - Theorem `reached_size_le`: every World the writer reaches encodes within `worldBytesMax`, so `worldTooLarge` is unreachable on the writer path.
  - The reader bound falls ~3×, and so does PERF-2's adversarial reopen.
- **(C) Derive the allowance from `worldBytesMax`.** Primary `worldBytesMax` = 2^28 (HOST-14's measured design ceiling: ~5 s decode at open, decisions/host.md:443).
  - `worldWeightMax := 32·(2^28 − journal − refusals − fixed)/35`, ≈ 240.8 MB with R1.
  - `allowanceMax := 137·(worldWeightMax − genesisReserve)/76`, ≈ 434 MB, about 3.2× today's useful life, at the reader bound HOST-14 already priced.
  - The same Φ check, and the same `reached_size_le`.

**Recommendation: (C), with R1, if HOST-14 co-signs that 2^28 is still the ceiling it wants. Otherwise (B).**
- Both carry the same theorems. They differ only in which constant is primary, and that is HOST-14's call: it owns memory and reopen.
- (C) gives honest Stores the memory the reader bound already pays for. (B) keeps the useful life and shrinks the worst reopen.
- In both:
  - delete Host/Bounds.lean:80's "~900 BAR stores" and :92–95's "other half is headroom" (no prose ratio replaces them; the def is the derivation);
  - correct Weight.lean:8 and :446 and amend KERNEL-18's title ("`worldBytesMax` is DERIVED from the allowance by `fold_potential` + `world_size_eq`", not "is the genesis budget");
  - correct KERNEL-12's and Turn.lean's "budget for the whole Store" to "turn records and World weight".
- **Teeth.**
  1. **Kernel.** Plant `RowLeaf.head` weight +16 (or drop the declare term from `Turn.logWeight`): `growth_le_logWeight` fails (omega), so the 76/137 is not decorative.
  2. **Host.** host-sim arm `import-over-budget`: a carried World with allowance 2^40 is refused by name before `genesis` writes. Its control is an exported honest World, which imports.
  3. **Host.** `plant-world-at-derived-cap`: `worldBytesMax := derived − 1` must make the max-World arm red. The arm is an adversarial World at the bound (all-declare or tomb-heavy plus a full refusals trie), built through admitted turns in host-sim at toy parameters. It catches a derivation whose f is too small.
  4. **PERF-2** benches the worst reopen as a decoded base at exactly `worldBytesMax`, and pins it.

### Price, in premises on landed theorems
Grepped with `kernel20-stmts.py` over `worldBytesMax, allowanceMax, baseRecordMax, carriedMax, fold_world_weight, CarryFits, GenesisFits, Turn.growth, refusalsPerWindow, Cadence.deployed`.
- **Kernel, potential and growth lemma.** New theorems only. `fold_world_weight` keeps its statement (re-proved as a corollary, or left as is). No statement names `Turn.growth` except `admit_world_weight`, which is unchanged.
- **Kernel, R1.** `checkRefusal` gains one `req`. `checkRefusal_facts` and `refuse_facts` (Kernel/Proofs/Refusals.lean) gain one conjunct each. `refusalCount_le`, `fold_member_refusals_le`, `refusalsCounted_moved` and `refusalsCounted_moved_exists` keep their statements, since the per-member bound is untouched. CODEC's `refusalsFits` gains the global count clause, so a decoded base over C is refused `kernel/refusals`. `world_decode_refusalsOk` keeps its statement, and its proof gains the clause.
- **Kernel, R2.** Two new theorem families at the Receive level, and `GenesisFits` gains a founders bound if Host's cap moves into the kernel. That changes `genesis_ok`, `checkFounders_ok`, `inputOf_fits`, `genesis_inj`, `genesis_cellsFit` and `genesisWorld_codecFits` (six statements that destructure or restate `GenesisFits`), or none if the cap stays a Host check. This is a reason for R1.
- **Host.**
  - `importWith` gains the Φ check, so `import_genesis_iff` (Host/Proofs/Cli.lean:27) gains one conjunct.
  - The genesis CLI gains the same check, with no landed statement over it (grepped).
  - Every `baseRecordMax` / `worldBytesMax` statement is parametric in `c : Cadence`, so the eight Seal, Base and Genesis theorems keep their statements.
  - The Deployed discharge of `worldBytesMax < 2^32` (decisions/host.md:1083) holds under (B) and (C).
  - `CarryFits` is untouched: the budget is Host's number (KERNEL-18: "HOST's choice"), so the check lives in Host.
- **CODEC.** `world_size_eq` is new.
- **Flag day.** Under (C), `allowanceMax` changes, so the genesis invite's input bytes (`Protocol.Invite.inputBytes … allowanceMax`) change, and every devnet Store re-geneses. Under (B), `Cadence.deployed.worldBytesMax` changes. A base over the new bound is refused `baseTooLarge`, and none exists (the largest measured is 44.7 MB). Bench/WorstCut, Ops/Founder and Ops/Plants read `allowanceMax` by name and re-run.

### Critique
- **f is loose where it matters least.** 76/137 is attained only by an all-declare World, and each declare needs a parent create in the same turn (ratio 1/2), so the reachable maximum lies between 0.5 and 0.5547 of the allowance. The 35/32 encoding factor is attained only by an all-tomb World. The two extremes cannot coexist. A joint bound is tighter, but it is a harder theorem for a few percent. I chose the separable one.
- **R1 trades fairness for a theorem.** A global cap lets ~1,000 colluding members suppress everyone's refusal records for up to three windows. R2 keeps KERNEL-44's per-member shape, but its bound rests on a membership theorem that does not exist and on a founders cap that `GenesisFits` does not impose. I lean R1 because the kernel then bounds what its own fold reaches. That is the place a bound should live.
- **The import wedge is ASSUMED past the first stop.** I read that the loop stops `sealFailed worldTooLarge`. I did not run a restart. If restart refuses at open instead, the defect is "an acknowledged Store that will not reopen", which is no better.
- **The membership arithmetic is ASSUMED** at ~900 B per enrolment. Hybrid keys (CLIENT-11) make enrolment heavier and the refusal path harder to reach. The import path does not depend on it.
- **36,974 B of the 16 B run are unexplained.** Until `world_size_eq` is proved, my accounting matches one run exactly and the other to 0.17 %.

### Meta-critique
- ROOT's item arrived framed as "the triple payment is probably a double count, and `worldBytesMax` is only the reader's". I was primed to find a defect in (a). Instead the accounting holds, by two equalities that already exist, and the defects are in (b) on paths the item did not name (import, refusals). Check that I did not invent (b)'s defects to have one:
  - the import path is two reads: `importWith` has no allowance check, and `CarryFits`' clause is `< 2^64`;
  - the refusal term is a codec read plus `keptRefusal`.
  - Both are measured code, not inference.
- I recommended (C) partly because "3.2× useful life at no new memory" is a satisfying number. The honest test is HOST-14's: is 2^28 still the size at which the design must change, now that a reopen at it has never been benched? PERF-2's bench decides that, so the recommendation is conditional on it, not on the arithmetic.

### Questions
- **ROOT, Q1.** (B) or (C): which constant is primary? Defer to HOST-14 on the ceiling.
- **ROOT, Q2.** R1 (global refusal cap, kernel theorem) or R2 (per member, membership theorem plus a founders cap)? This is a genuine fork (pause item 4). It interacts with KERNEL-54.
- **ROOT, Q3.** May the Φ check refuse an import whose lineage is foreign (a forged allowance)? It weakens nothing that exists. It is a new refusal on a path that today admits a wedge.
- **HOST-14, Q4.** Co-sign or reject 2^28 as the reader ceiling before PERF-2's worst-reopen bench, or after it? Do you want the seal's `worldTooLarge` kept as the encode-side twin (HOST-41), with `reached_size_le` proving it unreachable on the writer path?
- **ROOT, Q5.** Recorded refusals' LOG bytes are uncharged and not allowance-bounded (≤ 16 × ~64 KiB per member per window). KERNEL-44's checkpoint rule bounds replay, not disk. File as a cv task for KERNEL-44/54's owner, or fold it into this decision?
- **CODEC (FYI).** `world_size_eq`, an equality in entry counts, is the theorem KERNEL-18 has owed you since 10-16.

Status: PROPOSED.

## KERNEL-55 RULED (ROOT, 2026-10-19) and AS BUILT, part 1: the potential (KERNEL-21)
**Rulings.** Q1 = B: `allowanceMax` = 2^27 stays primary (KERNEL-15's useful life); `worldBytesMax` is DERIVED from `allowance_bounds_world` and CODEC's size equality (HOST-14's commit); both prose ratios ("~900 BAR stores", "the other half is headroom") are deleted, no ratio replaces them. Q2 = R1: `membersMax` is not a Bounds constant (Lang's `membersMax` = 63 is a quorum mask; Receive's `enrollMax` = 256 is per grant; no membership theorem exists), so the refusals trie is bounded by a kernel-wide cap per window (part 2). Q3 = YES: import refuses a carried allowance above `allowanceMax` by name, with a tooth (HOST-14's two arms: `allowancePastBound`, and `potentialPastBound`, since an allowance check alone still lets a weight-heavy carried World through). Q4: HOST-14 co-signed B and rejected 2^28 as the reader ceiling on PERF-2's measurement (a base at 2^28 reopened in 120.7 s, 2× THE BAR's 60 s). Q5: the refusals trie's bytes fold into the bound via R1; framing and index.log are HOST's theorem.
**KERNEL-54 moved the constant.** A head's floor and a row's version are World bytes the log does not carry, so the tight term (a pinless declare at a head, slot weight 34) is growth 34 + 50 = 84 against log 34 + 27 = 61: r = 84/61 (it was 76/61). Every other term is below it: a create (40 + w)/(32 + w), an insert or upsert at most 56/49, a write's ops below its act, a nullifier 1, keeps, retires, retracts and range reads 0. So the potential is Φ = 145 · weight + 84 · allowance and f = 84/145 ≈ 0.5793 (it was 76/137 ≈ 0.5547). At A = 2^27: 84 · 2^27 / 145 = 77,753,718 (post-54) against 76 · 2^27 / 137 = 74,456,549 (pre-54); PERF-2's bench row pins the post-54 figure, whatever HOST adds for genesis weight, journal, refusals and framing.
**Built (part 1).** Kernel/World.lean `potentialRatio := (84, 145)` and `potential w := 145 · w.weight + 84 · w.allowance` (HOST reads both by name). Kernel/Proofs/Weight.lean: `RowTouch.growth_le_weight`, `Turn.growth_le_logWeight` (61 · g ≤ 84 · L), `admit_potential`, `fold_potential` (premises exactly `fold_conserves`'s), `allowance_bounds_world` (145 · w'.weight ≤ potential w). TOOTH: `RowTouch.declare_growth_tight`, the equality 61 · 84 = 84 · 61 at a pinless declare, so 84/61 cannot be lowered. `fold_world_weight` keeps its statement as the weak form. The Weight header's "HOST-14's `worldBytesMax` is the genesis allowance" was false and is replaced: the allowance budgets turn records and World weight, not the whole Store (KERNEL-12's and KERNEL-18's wording is corrected by this entry).
**Critique.** The separable bound is loose where it matters least: 84/61 is attained only by an all-declare World, and every declare needs its parent created in the same turn, so the reachable maximum is below 84/145 of the allowance; a joint bound is a harder theorem for a few percent. **Meta-critique.** The constant was priced on the pre-54 Turn and would have been wired into HOST as a literal; the post-54 recomputation is what the names `potential`/`potentialRatio` are for: the next field that adds World bytes without log bytes moves them here, once.

## KERNEL-55 AS BUILT, part 2: the refusals trie is bounded by the kernel (R1; lane r1 of KERNEL-21/22)
**The cap.** `Bounds.refusalsPerWindowMax` = C = 16,384 recorded refusals per window, all members together. It is checked in `checkRefusal` after the per-member budget, `req (refusalTotal E w < C) .refusalsFull`. `Reject.refusalsFull` is appended last; `Receive.judgeBy` declines it as `rejected refusalsFull` and never records it (`judgeBy_refusalsFull`). The cost is a liveness cost on refusal finality and never one on admission: past C, one flood of colluding members leaves every refusal unrecorded until the window turns.
**The key and why.** The World's count per window is a third refusals key, `RefusalSlot.total (origin : D) (win : UInt64)`. Its bytes are `⟨#[2]⟩ ++ E.bytes origin ++ u64 win`. It holds the existing `count n` leaf, is bumped by `commitRefusals` (a third insert), is pruned like a member's count (current window only, `keptRefusal`), and is read by `refusalTotal`. The origin is a FILLER. Every refusals key is one kind byte, one digest and eight bytes; on that fixed width rest `refusalKeyBytes_size`, the leaf body's injectivity and CODEC's key order. A member-less key has no digest of its own: `D` carries no `Inhabited` and `Env` no width. Three alternatives were rejected:
- variable-width keys reopen those proofs and CODEC's order theorems;
- a hashed constant puts a hash in every routing bit;
- a scalar World field puts a new field on every `{w with ..}` frame proof and on the World header codec, which are more premises on landed theorems for no gain.

The origin is a real digest of the World, constant over its life, and `refusalsCounted` refuses a total under any other digest.
**What a decoded base must satisfy.** `refusalsCounted` (CODEC's `kernel/refusals-counted`) now also checks:
- the total leaf is at (origin, current window);
- it equals the window's record count, all members together;
- it is present when the window has a record;
- each of the two windows before holds at most C records.

`World.CountedOk` gains the same four conjuncts, `refusalsCounted_iff` decides them, and `fold_countedOk` keeps them. When a window turns, its total becomes the previous window's record count.
**The bound** (Kernel/Proofs/RefusalsBound.lean). `refusals_bounded (hw : RefusalsOk) (hc : CountedOk)` states, over the listing, records ≤ 3C ∧ member counts ≤ C ∧ totals ≤ 1 ∧ length = their sum. It comes in these forms:
- `fold_refusals_bounded`;
- `reach_refusals_bounded` and `deployed_reach_refusals_bounded`, with no premise;
- `refusals_bounded_of_counted`, for a decoded base;
- `refusals_length_le`, at most 4C + 1 entries.

Exactly three windows' records coexist (`refusal_window_range`), and three is tight (`refusal_window_three`): at the prune that opens window j, the last record of window j−2, refused at (j−1)·windowMax, is kept and fits, so two windows would be wrong. The member counts are bounded by the window's records, because each count leaf is a member with a record this window and the keys are distinct. At the deployed C the trie holds 49,152 records, 16,384 counts and 1 total. In bytes, refusals ≤ 82·3C + 50·(C+1) = 4,849,714 B, and with it the derived `worldBytesMax` pair is 91,914,347 B post-54 and 87,654,733 B pre-54. HOST-14 confirmed the pair, with CODEC-13's `world_size_le`.
**Teeth.**
- `refusalsOk_bounds_nothing`: for every n there is a `RefusalsOk` World holding n records, so the per-leaf check bounds nothing and the bound rests on `CountedOk`.
- `counted_world`: for every n ≤ C there is a `RefusalsOk ∧ CountedOk` World with members 0…n−1, one record and count each, total n, n steps, so the teeth stand on a World the fold reaches and the decoder admits.
- `checkRefusal_full` and `refusalsFull_independent`: on `counted_world` at C, every member charged once, the refusal is declined `refusalsFull`, so the cap binds where the per-member budget does not.
- `uncapped_overflows`: committed at C, as a kernel without the check would commit it, the total is C+1 and the World is not `RefusalsOk`.
- `refusalsCounted_total_lowered` (and `_exists`, premise-free on `counted_world` at 2): a total lowered to reset the World's budget still fits and is refused.
- kernel-sim: `refusals-full`, `refusals-full-control`, `refusals-full-plant`, `refusals-total-plant`.

The cap is not reached through `judge`, because C records need over a thousand enrolled members at 16 each; the probe builds the World at the cap.
**Statements moved.**
- One landed helper gained a premise, forced: `refuse_sumN` now requires `g` to be 0 on total keys (the old statement is false once a third key is inserted). Its only callers are in its own file, and they pass such a `g`.
- `checkRefusal_facts` and `refuse_facts` carry the total inside their sixth conjunct.
- `refuse_refusalAt` gains a first branch; `commitRefusal_refusals` gains the third insert.
- HOST's `refuse_refusals_listing` (+3) and `_two` (=3) follow HOST-14's patch. CODEC's slot codec gains arm 2 and its vectors re-emit (CODEC-13).
- WASTE `refuse hashes-per-refusal` moves 11.362 → 15.284 (the third insert, one shared path per window).

**Flag day.** The refusals key wire gains kind 2, the refusals root of every World with a record changes, and every devnet Store re-geneses. A base whose window has records but no total, or whose total disagrees with them, is refused `kernel/refusals-counted`.
**The price ROOT accepted in R1** (the reader's reading, K22-READER-R1). About C/16 = 1,024 members, each at its own per-member budget of 16, exhaust the World's window cap and stall refusal finality for every member until the window turns. Admission is unaffected, and each such member costs an enrollment. `refusalsFull_independent` is that World in Lean, at count 1 each: the cap binds where the per-member budget does not.
**Critique.** R1 trades fairness for a theorem: that thousand-member flood suppresses everyone's records for a window, where R2 kept KERNEL-44's per-member shape but rested on a membership theorem that does not exist. **Meta-critique.** The brief's `total (win)` key could not be fixed width; reading `refusalKeyBytes_size`'s consumers before writing the def is what surfaced the filler. Without that read, the variable-width route would have been the default, and it would have broken CODEC's order proofs silently in another layer.

## KERNEL-51 AS BUILT, the locality half: `check_local` (cv 01a14f65-48ec; K22-LOCAL, finished by KERNEL-23)
**The statement.** `Kernel.Proofs.Local.check_local (h : Agree E w w' t) : check E w' t = check E w t`. The read set lives in Kernel/Proofs/Logic/Frame.lean, beside the footprint (the frame's write half, KERNEL-51), and is all Props: `CellRead t` (every touch, a `keep` too, every birth and every spend), `RowRead E t` (every row touch, the head of each row a touch names, each range read's head, every key under its prefix at any width, and every key under a retiring parent), and `RowsAgree E w w' t`. `RowsAgree` has two constructors. `same` (the same rows trie) takes no premise. `read` (slot-wise agreement on `RowRead`) takes `E.Lawful n`, both `RowsCanon`, and `hf : ∀ s, rowAt E w.rows s ≠ none → RowSlotFits s`: `under` and `retainAt` walk the trie's shape, and two canonical tries with the same contents are equal only where keys separate (`rows_separateOn`, which needs ONE key in bounds since 7c09186). `rowSlotFits_of_held` turns `World.RowsOk`'s `rowFits` into `hf`. `Agree`'s cells field takes no premise.
**What it replaced.** `check_journal_congr` (public, Journal.lean) is deleted: `check_journal_filter` is now an instance of `check_local`. The five RowsComm privates (`live_of_get`, `entry_of_get`, `forEx_ok_of`, `mapEx_congr`, `touchCheck_congr`) are deleted too. `mapEx_congr` and `forEx_congr` now live in Check.lean.
**What it did not replace.** `check_after` proves ok-preservation across a commit, not equality, because the second World differs inside the read set (height, steps, allowance, head counts). Only its cell reads were local, and those five privates are what went. `receive_congr` is locality for `receive`, which is a different function. `commitTrie_congr` and `insertAll_congr` are commit-side, the frame's dual. No theorem fell: the change is +32 theorems net.
**`RowsAgree.read` lands, though nothing consumes it yet.** Without it, `check_local` says the rows are local only when they are identical. With it, ~22 private lemmas and ~300 lines give slot-wise rows locality, and the reader showed `read` is load-bearing. Tooth `check_unread_row`: a fitting row written at a slot the turn does not read changes no check, although the rows now differ.
**Teeth.** `check_local_outside` (an admitted pair that differs outside the read set); `check_reads_kept` and `check_reads_kept_sep` (a `keep`-pinned cell is read but not written, so the read set cannot shrink to the footprint; the escape is `CollidesAmong E.hash [pinPre E none, pinPre E (some (.live readCell 0))]` over that explicit list, and neither disjunct follows from the premises); `check_unread_row`.
**After 7c09186** (at the landing): `ranges_read` lost `hfit` and the `width < 256` block, `range_prefix_long` lost its `hw'`, and `RowsAgree.read`'s `hf` weakened from `rowFits` on every entry to `RowSlotFits` on every held slot. These are premises removed from new theorems. `RowSlotFits` moved from RowsSep.lean to Rows.lean, below Logic/Frame.lean, which needs it; its statement is unchanged.

## KERNEL-57 · KERNEL-6 CLOSED as built (option (a), KERNEL-27/LANG-24): `law_judged` names what adoption judges (KERNEL-24, 2026-10-21; ROOT ruled on SCHOLAR-COMPARE §1, docs/record/COMPARE-20261021.md)
**Decision.** A law holds from the turn that adds it. That turn's receiver runs two judges over the object's UNCHANGED state (`Kernel/Receive/Derive.lean:166-182`). The laws in force judge `relaw laws'`, which is the authority to change laws. Then every ADDED law judges `adopt laws'`, which is its base case: the state it is adopted over. A law that refuses that state is refused under its own name and is never installed. A kept law is not re-judged on `adopt`: LANG-4's amendment, since otherwise every relaw that keeps a quorum fails. There is no `since` height, because no theorem needs one. There is no grace window, because nothing in nano outlives a turn.
**Theorems** (`Kernel/Proofs/Authority.lean`, beside `law_authorized`):
- `law_judged`: a derived `law` turn had its object cell, no package, the owner authority, `checkLaws` of the incoming list, the laws in force, BOTH judge verdicts `.ok ()` (the exact lists and occasions the receiver uses, `stateOf cell` as old and new), and its one effect, the law-slot diff.
- `law_adopt_refused` (the tooth): past the authority and the laws in force, a refusal by the added laws on `adopt` IS the turn's refusal, verbatim. For LANG's program that refusal is `lawDenied <law> <reason>`. `Lang.Proofs.StdTeeth.bounded_adopt` (`bounded total ≤ 100` adopted over a total of 500, refused) is the state-violates-the-law instance. `quorum_adopt_forged_approvals` keeps LANG-24's vacuous forged-approvals case named.
- `Lang.Proofs.Receiver.judgeOne_admits` takes either verdict to `Std.Admits` for each law.
**Teeth on the run.** kernel-sim `law-self:lawDenied` (a standing `plantedArms` row) is the adoption refusal only. No object ever holds deny-all in force, because births under it and adoptions of it are both refused. So the laws in force always admit the `relaw`, and the refusal is the added law's own. The arm's comment now says so. `law:ok` (freeze adopted) satisfies `law_judged`'s premise.
**cv.** 01a14805-3d5a is closed as describing the pre-KERNEL-27 receiver. Its "cheap fix" (judge `laws'` on `relaw`) is the wording KERNEL-27 refuted: Frozen became uninstallable, and lang-journey L10d went red.
**Premises.** None on any landed theorem: two new theorems, no changed statement (second-agent read K24-READER-1, LAND-WITH-FIXES, both fixes taken: the `packageOf`/`checkLaws` conjuncts, and a dead sim branch removed). **Re-genesis:** none.
**Critique.** `law_judged` is a reading of the receiver. Its value is that later theorems, such as an object-history `Chain` of `Admits` (COMPARE §4.4), can start from a kernel fact rather than from `Derive.lean`'s text. **Meta-critique.** I almost shipped `law-self` with a dead `law-relaw` branch "for precision". A branch the generator cannot reach is a label that reads as coverage.

## KERNEL-58 AS BUILT · Q1, the receivers' contract and the call-level frame (KERNEL-27 lane, Ember 10-21 on PROOF-ENGINEERING-20261021 §2.1/§4)
**Ruling taken.** A receiver's contract is `Derived`, a Prop-structure. Its frame is `submit_frame` over `CallFoot`. There is no assertion language and no `∗`, and `unpinned` stays the receiver's refusal by name.
**What changed.**
- `receive_ok` (eight conjuncts) is DELETED. Its re-export is `structure Derived X c t : Prop` in `Kernel/Proofs/Receive.lean`, with fields `signed exact priced pinned event txId notBefore validUntil` (the same eight facts, the window split into two fields), proved by `receive_derived`. The consumers (`Kernel/Proofs/{Journal,Refusals}`, `Host/Proofs/Serve`, `Protocol/Proofs/{Behind,Settle}`) changed proof bodies only. Two `.2.2.2…` projections became `.pinned` and `.validUntil`.
- `Kernel/Proofs/Logic/Triple.lean` adds the following:
  - `CallFoot X c w`: a pinned cell, an id `w` has not taken, or a nullifier `w` has not spent. It is the call's footprint at the World it is derived against, read off the call and that World only.
  - `Triple X P c Q`: a definition over `receive` and `World.admit`.
  - `Indep X c R`.
  - `submit_derived`, `callFoot_of_turn` (every `CellFoot t s` of the derived Turn is a `CallFoot`), `call_frame`, `submit_frame`, `not_callFoot_live` (at a live cell the footprint is exactly "pinned"), and `indep_live`.
- Teeth, on a toy `Ctx` running the deployed receivers, seal and admission:
  - `callFoot_needs_born`: a `create` writes a cell it never pinned.
  - `submit_frame_needs_indep`: a `rotate` writes the member it pinned.
  - `derived_needs_receive`: admission takes a Turn with an empty event, and that Turn is `Derived` of no call.
**Where the Props live.** Closure C3 puts statements in PROOF modules (a def module exporting a Prop is red). The brief said "a def module", which was a misreading, so no def module was added.
**Premises.** No landed theorem gained a premise. One statement changed (`receive_ok` → `receive_derived`, equal strength). Every new theorem takes only `receive … = .ok t` and `World.admit … = .ok w'`. Second-agent read (K27-READER-1) found no blocker, and all three of its fixes were taken: the tooth above was strengthened from "not Derived of another call" to "Derived of no call"; the header's `Invokes.other` claim was narrowed to a call-derived Turn at a live object; and the over-approximation is now stated. The older entries' mentions of `receive_ok` are records and stay as written.
**Re-genesis / re-emit.** None. This is proof-side only.
**Critique.** `CallFoot` over-approximates births and spends as "anything fresh". It also counts a `keep` pin, which `CellFoot` leaves out. It is exact at what Q3 needs, a live object (`not_callFoot_live`). A footprint that is exact for births would have to read the derivation, which depends on the World through the pins.
**Meta-critique.** The brief's "zero premises on landed" claim was checked against the diff, not assumed. The brief's `bornIds` helper turned out to be unnecessary, because freshness is the World's own check (`checkCreates`, `checkNullifiers`).

## KERNEL-59 AS BUILT · Q3's kernel half: one object-history lift over every body kind (KERNEL-28 lane, PROOF-ENGINEERING-20261021 §2.3/§4 Q3)
**Ruling taken.** `Admits` stays existential; the lift is `object_history_chain`, proved once over every body kind, with the laws as its step lemmas; wp over the fold, sp over the law.
**What changed.**
- `write_judged` (Kernel/Proofs/Authority.lean), the twin of `law_judged`: a derived `write` read a data object, passed the owner authority, and the laws in force judged `old → applyEdits old edits`; its Draft is exactly the `diffOps` write. Tooth `write_law_refused`.
- FINDING (proof-only: no deployed check changed): `write` has no `checkState` of its new state (an invoke's run does), so its read-back needs the cell canonical. That held in every reachable World (births are checked `nonCanonicalCell`, `set`/`erase` keep the order) but was stated nowhere, and no theorem could use it. Kernel/Proofs/WriteNext.lean: `CellsCanon` (every live cell's slots strictly ascending) holds at genesis (`genesis_cellsCanon`) and every admit keeps it (`admit_cellsCanon`, `fold_cellsCanon`, `audit_cellsCanon`); `write_next_slots`, `law_next_slots` (law keys sit below `stateBase`, `checkLaws`' bound). Teeth `write_needs_canon` (a cell holding key 16 twice: the edit-free write re-sets the first entry, so the state left is not the state judged), `law_slots_need_bound`.
- THE TOTALITY (Kernel/Proofs/InvokeTree.lean, "not proved here" until now): `effect_at_object` (an effect at a cell the pins read as an object is the signed `write`/`law` of it or the own write of an invoke of it the walk `Dispatched`; every other receiver writes a cell it read as a grant, member or account, by its own `readKind`), `object_turn_cases` (a derived, admitted turn keeps a live object exactly — no write, law or dispatched invoke of it — or is one of those). Tooth `effect_at_object_needs_kind`.
- Kernel/Proofs/Logic/History.lean: `ObjectStep` (refusal, other, frame, keep, write, law, invoke, nested), `ObjectHistory`; `object_step_none/_some/_live`; `object_history_of_audit` (an audited log from a `CellsCanon` World is a history of every object live at its start); `object_history_runs`, `object_history_start`; `object_history_chain` (THE LIFT: for a `NoRef` law in force at every judged step, the history is `Std.Chain (Std.Step [] t)` from the object's state, step for step). Kernel/Proofs/Logic/HistoryWitness.lean: `object_history_chain_witnessed` (every premise, through `Lang.program`, conclusion a one-step chain), `write_history_witnessed`, tooth `object_history_needs_inForce`.
- F4 (KERNEL-25, cv 01a15554-cffd, read by K25-READER-F4) lands in the same commit, its text kept in the message: `Dispatched X w c n wk actor b`, the walk's own record; `invoke_tree_slots`/`invoke_tree_run` restated over it (actor, method, arguments, fuel pinned); `dispatched_of_invoked`, `dispatched_of_signed`; tooth `dispatched_pins_args`.
- `invoke_next_judged`'s conclusion now also gives `lawsOf X obj cell = .ok laws` (stronger, same premises); `readKind_pinned` public; `invoke_lift_witnessed` in InvokeWitness.
- Ledger (ROOT for LEDGER): `Invokes` and `invokes_runs` DELETED; `escrow_invokes_one_payout`/`_deployed` restated over `ObjectHistory` (+ `hpkg`, the readPackage `Invokes.invoke` carried) and now cover nested invokes, writes, law changes, keeps and refusals. `escrow_runs_one_payout` and `escrow_runs_after_payout` keep their statements and are re-proved by `runs_chain` + `Std.chain_count`/`chain_stops` (`payoutCalls_le_one` serves both).
**Premises.** No landed theorem gained a premise (`hpkg` re-carries `Invokes.invoke`'s readPackage). The lift takes `X.Lawful` (as 116 landed theorems do), `X.program = Lang.program …` (as `escrow_*`), the law in force and read as `p` per judged step, and a live start; no typing premise. `ObjectStep.write` carries its cell's canonicity and `ObjectStep.nested` the order laws (`invoke_tree_slots`' price); `object_history_of_audit` discharges both (`CellsCanon`, its instance arguments).
**The 47.** Of today's 93 never/once/first/after/mono-named theorems, one is an object-history fact: `escrow_runs_after_payout`, now a `chain_stops` corollary. The rest are journal/nullifier "once", rows/trie/order "mono"/"first", hosting loop clocks, protocol attempts, Lang `never_stuck`: not about one object's state under laws.
**Re-genesis / re-emit.** None. Proof-side only.
**Critique.** The lift needs the object live at the history's start; a history from birth splits the log at the birth. `effect_at_object_needs_kind` shows the check on one receiver (revoke), not wired into `dispatch`.

## KERNEL-60 · Counted value rights in the grant (KERNEL-28's amount right, with credit) and the CANCEL record (design C1), re-priced after KERNEL-54; `rotate_stales_outstanding` (KERNEL-24, 2026-10-21; ROOT ruled on SCHOLAR-COMPARE §2–3)
**(2) The amount right.**
- `Right` gains `transfer (cap)` and `credit (cap)`, the counted value rights. They are carved and spent exactly like `enroll (count)`, through ONE ledger mechanism: `ledgerLeft`, `spendAt` and `spendVia` in `Kernel/Receive/Authority.lean`. `enrollLeft` and `spendEnroll` are now its enrolment instance.
- Each ledger is an append-only slot series in the grant cell: `transferBase = 2048`, `creditBase = 2560`, at most `ledgerSpendsMax = enrollMax = 256` spends. The ranges are disjoint from 16, 17, 1024..1280 and 4096+m. A spend that would be written past the last slot the ledger reads is refused, never written.
- `transfer src dst amount (via := some g)` walks a chain for `.transfer _`. It then appends `left - amount` to g's ledger as the Turn's third effect. More than what is left is refused `transferSpent g`.
- `credit` works the same on a well's floor, refused `creditSpent g`.
- A derived grant carves its cap from its parent's ledger. A cap past the parent's is `grantWidens`.
- A root transfer or credit grant (no parent) is allowed: the owner is the root issuer the walk requires.
- `checkRights` (the ruled target typing) refuses `rightTarget`:
  - a grant carrying two counted kinds, so no carve can skip a ledger;
  - `enroll` anywhere but the World;
  - `transfer` or `credit` on the World.
- A total cap past `capMax` (2^63) is `overflow`.
- **`mutate` moves no value.** It authorises neither a transfer nor a credit line. ROOT refused to keep credit on mutate: it lent the whole floor headroom.
- These calls relied on mutate-for-transfer, and each was moved:
  - ledger-sim E7 now grants `transfer 30`.
  - Protocol/Rows.lean's bounty deposit grant is now `transfer:30`.
  - The escrow header and Verb.lean docs drop the v0 label.
  - There is no Rust caller.
- LEDGER-16 records the escrow side, with LEDGER-6's agreement.

**Theorems (2)** (`Kernel/Proofs/Authority.lean`, `Kernel/Proofs/Ledger.lean`):
- `spendAt_ok`: a spend is within what is left, and for a nonzero spend at a ledger index the ledger reads.
- `spendEnroll_ok`: the statement is unchanged, now derived from `spendAt_ok`.
- `spendVia_ok`.
- `transfer_ok`, `credit_ok`: every step the receiver passed.
- `transfer_authorized`, `effect_transfer_authorized`, `credit_authorized`: the chain is for `(.transfer 0)` / `(.credit 0)`, and through a grant the grant had at least `amount` left and the Turn appends the remainder.
- `transfer_exact`, `credit_exact`: through a grant, the grant's ledger after the turn holds the remainder. The frame excludes exactly that grant (`via ≠ some k`).
- `sealed_writes`, the n-write generalisation. `sealed_two_writes` is kept with an unchanged statement and is its instance.
- `grant_ne_account`, `admit_written_entry`.
- `checkRights_ok`: one counted kind, and the targets. This is why no carve skips a ledger.
- The carve twins `grant_carves_transfer` and `grant_carves_credit`: a child's cap is carved from the parent's remaining ledger, so the cap binds along the whole chain, not only at the leaf.

Teeth (kernel-sim `capArms`):
- transfer-via:ok and transfer-past-cap:transferSpent;
- transfer-mutate:grantRight;
- right-target:rightTarget;
- credit-via:ok and credit-past-cap:creditSpent.

Teeth (ledger-sim):
- short-cap: a grant one less than the deposit moves, which is the package asking for `amount + 1` of what it was lent, so E8 is refused `transferSpent`.
- skip-judge E9: a second deposit is refused `transferSpent`, because the cap refuses before the once key.

**(3) The cancel record (C1).**
- A member ends one of its outstanding calls by recording the refusal of THAT call.
- `recordOf X c v a` is the call's own transaction id, member, window and bytes. It generalises `refusedOf`, which is `recordOf … ByteArray.empty`. The code is `cancelled`.
- The ONE new field `Refused.cancel` holds the member's signature over `domCancel ‖ txId`, verified under the member's CURRENT key on the World it is recorded on (`cancelAuth`). The call's own signature is not needed.
- `World.refuse` judges it unchanged: inside the call's window only (an early cancel is `outsideWindow`), never once the call is journaled or already recorded, and charged to the member's `refusalsPerWindow` and the World's R1 total.
- **The budget class is SPAM, by decision.** A member that cancels sixteen calls in a window has its later records declined `refusalBudget` until the window turns. Measured: in kernel-sim's 16 seeds the cancelling member had already spent its 16 records in 7 of them (`cancel-budget:refusalBudget`), so its cancel was declined there. That is the stated cost of the class, not a defect.
- The audit re-judges a record with a non-empty cancel by `cancel` (`recordedBy`). A forged one is refused `cancelForged`.
- `judge` is unchanged (ROOT ruled (i)). The audit tells a member's cancel from a program-named `cancelled` by the FIELD, never by the code. A record carrying a cancel signature is re-verified as a cancel, `cancelForged` on failure. A record without one is a program refusal, re-judged by `judge` and never read as a member's act.
- C1 said "no new kernel check". That was wrong. `refusedBytes` must commit the field, or two records differing only in it share a digest and the chain binds neither. So `checkRefusedBounds` bounds it (`cancelBytesMax = 64`), and `refusedDigest_inj` covers it.
- A cancel reaches followers as page event tag 2, `[2] ‖ nat64 size ‖ sig ‖ call`. That is PROTOCOL-21's half, with HOST-17's yes. Tag 1 carries only the call, so without tag 2 every follower would break its chain on the first cancel.

**Theorems (3)** (`Kernel/Proofs/Audit.lean`, `Refusals.lean`):
- `cancel_recorded`, `recordedBy_recorded`.
- `audit_cancel_signed`: a cancel the audit accepts verifies under the member's live key, and the record IS `cancelOf` its own event.
- `audit_cancel_forged` (its tooth).
- `audit_unsigned_is_judged`: a record with no field passes exactly when `judge` records it.
- `audit_program_cancelled_forged`, ROOT's tooth: a program refusal spelled `cancelled` that carries a forged field is `cancelForged`.
- `cancel_early_declined`.
- `cancel_final`: after a recorded cancel, `submit` of the call is `refusedFinal cancelled` below the prune height.
- `refusedDigest_inj` covers the new field (length-prefixed in `refusedBytes`).

Teeth (kernel-sim): cancel:recorded, cancel-final:refusedFinal, cancel-other:badSignature, cancel-early:outsideWindow, cancel-forged:cancelForged.

**The free theorem.**
- `rotate_stales_outstanding` (`Kernel/Proofs/RotateStale.lean`) is breadstuffs' `SelfNonceBump` recovered. A call that pinned its member cell before a rotation of that member is never admitted at any World the fold reaches from the rotation, or the hash collides on the two pin inputs compared (`CollidesAmong` over exactly that pair).
- `_sep` is the binding form.
- The tooth is kernel-sim `rotate-stales:stale`: a call signed with the member's NEW key but pinning the pre-rotation member cell is declined `stale`.
- So a rotation after a key compromise ends every in-flight call the stolen key signed. That is a theorem of the fold, not only of the key check.
- Versions.lean's entry-order lemmas are now public (`EAdv`, `EStep`, `eAdv_trans`, `eStep_trans`, `fold_entryStep`, `VerFit`, `cellsFit_verFit`, `pinPre_adv_ne`). KERNEL-23 agreed.

**Flag day (`kernel!`).**
- What refuses now:
  - a transfer past its grant's cap (`transferSpent`) and a credit past its cap (`creditSpent`);
  - a transfer or credit through a `mutate` grant (`grantRight`);
  - a counted right off its target, or two counted kinds in one grant (`rightTarget`);
  - a forged cancel in a log (`cancelForged`);
  - a cancel outside its call's window (`outsideWindow`, declined).
- What moves on the wire:
  - Right codec tags 4 and 5.
  - The Refused/Step record gains the cancel bytes: rawBytes ≤ 64, plus 4 + 64 bytes in `Host.refusedBytesMax`.
  - Every receive refusal past `enrollSpent` shifts its code (three inserted names, two appended). Every reject code shifts by +5.
  - LANG's `rightTy` gains `credit` and `transfer`, so every package whose type embeds it re-ids.
- What re-geneses: every Store.
- What re-emits: `gates/codec-vectors.tsv` (`kernel/right` covers six tags; `kernel/refused` gains the cancel's boundary pair, 64 read back and 65 refused `pastBound`). CODEC is not live, so ROOT signs for CODEC on its two table rules: `right_lawfulOn`/`refused_lawfulOn` restated for the moved sites, and the boundary pair. `generated.rs` is unchanged: no refusal name is generated into Rust.

**Premises.** No landed theorem gained a premise. The second-agent read K24-READER-2 was LAND-WITH-FIXES, and every fix was taken.
- Changed statements, SHAPE:
  - `transfer_authorized`, `effect_transfer_authorized`, `credit_authorized`, `transfer_exact`, `credit_exact`. Each is no weaker, except for the forced exclusion of the grant cell, which its new conjunct describes (LEDGER-6's condition).
  - `auditRefusal_ok` and `Honest`: `judge` becomes `recordedBy`, which IS `judge` for a record with no field.
  - `refusedBounds_wide`: one more constructor argument.
- Tightened by DEFINITION, forced by the field:
  - `Refused.Fits` gains `cancel.size ≤ cancelBytesMax`. It sits behind Host's `Step.Fits` premises and is discharged by `checkRefusedBounds_fits`.
  - `checkRefusedBounds` gains the same bound. It sits behind `refusedDigest_inj`'s `hb` and is discharged by `World.refuse`.
- Versions.lean's entry lemmas lost `private`; their statements are unchanged.
**Not yet reached.** No Host op or client verb records a cancel yet: only kernel-sim reaches `Receive.cancel`. HOST-17 designs the op after HOST-63, starting from the shape `call bytes ‖ signature`. PROTOCOL-21 then adds the `nd cancel` verb and a rows line with a plant.
**Critique.**
- There are two counted value rights where the scholar named one. ROOT refused to keep `credit` on `mutate`, because it was the same unbounded-authority class.
- The cancel is spam-class, so an honest member who cancels a lot is throttled along with flooders. KERNEL-54's honest-contention exemption was for a structurally final class. A cancel is a member's act, not contention.
- `rotate_stales_outstanding` makes cancel-all free. That leaves C1 for exactly the call that pins nothing the member owns.
**Meta-critique.**
- My first cancel build had `judge` decline a program-named `cancelled`, so that the code alone would mean "signed". That put a premise on a landed theorem. The field, not the code, was always the right discriminator.
- I also nearly shipped C1's "no new kernel check" without reading what the chain commits.

**Addendum (LANG-75.2, CX-PROMO, 2026-10-22; GRANT R-0030; text only, no kernel source).** A method's live read
of a cell (`Lang.cellLive` at `pinned`, LANG-75.1) and the calls that run returns (`spendVia` included) are the
same Turn: `receive` takes one `pinned` view and `invoke` runs and derives under it. That is the pin check plus
one Turn; it is not a certificate the kernel consumes. In P8 the checked cell is the provider grant and the spent
cell is `cap` (two cells, one `look`). Across two Turns nothing is shared: a second Turn that spent without its
own live read would admit; the journey row "P8.2s two-Turn split" records that the deployed second Turn re-reads
and refuses `support0 dead`. (Morgenstern 2011, LPCFS p2, is the shape cited, not a claim this ledger implements.)

## KERNEL-61 AS BUILT · A counted right's cap provably falls: `LedgerContiguous`, the grant totality, and the read-back (KERNEL-30 lane, for LEDGER-7's `grant_moves_le_cap`, 2026-10-22)
**The finding (LEDGER-7).** Nothing proved a spend is READ BACK. `ledgerLeft base g` reads the LAST entry of the slots `base … base + ledgerSpendsMax` and names the next index as their COUNT, so a spend appends at `base + count`. If a grant's ledger had a gap, that write would land below the last key, `getLast?` would keep reading the old entry, and the cap would never fall. No theorem said a reachable World has no gap.
**Measured by the proof: the invariant HOLDS for every receiver.** No receiver writes a ledger slot out of order, so there is no kernel defect and no receiver change. Proof-only.
**What landed** (`Kernel/Proofs/LedgerNext.lean`, new; `Kernel/Proofs/InvokeTree.lean`):
- `GrantContiguous cell`: at each counted base, the ledger's keys are `List.range' base length`. `LedgerContiguous E w`: every live grant has it. Both are Prop definitions in the proof module.
- The totality at a grant, `effect_at_grant` (InvokeTree). An effect at a cell the pins read as a grant is either its revocation's retirement or ONE `spendAt` append (`LedgerSpend`: an enrolment, a transfer or credit through it, or a child carved from it). `write`, `law` and an invoke's own write land on cells read as objects. Every other receiver writes cells it read by its own kind. The private totality lemmas were strengthened to carry this (`OtherEffect`; `EffectsAt` now records the invoke's object read). `effect_at_object`'s statement is unchanged.
- `grant_turn_cell`: a derived, admitted turn keeps a live grant, retires it, or appends ONE entry `left - u` at index `i` of one ledger. The turn's act at a cell is ONE effect's (`actFor` takes the first). That it is the turn's only spend of the grant is `sealTurn`'s `duplicateEffect`, which the read-backs use (`effect_reads_back`): without it a second spend would be silently dropped. `admit_retired` is the retirement's forward lemma.
- `derive_born_grant`: only `grant` bears a grant, with one entry per counted kind, at its base.
- The invariant, from genesis, as `CellsCanon` was proved: `genesis_ledgerContiguous`, `step_ledgerContiguous`, `submit_ledgerContiguous`, and `audit_ledgerContiguous`, which carries `CellsCanon` along.
- The read-back:
  - `ledgerLeft_append` is the slot half. Over a canonical, contiguous cell, the append reads `(i + 1, left - u)`, the other ledgers are unchanged, and the cell stays canonical and contiguous.
  - `grant_turn_ledger`: what is left of every ledger of a live grant stays as it was, or ONE ledger falls by exactly the `u` it spent. This is the per-step form for a chain.
  - `spend_reads_back` (a signed transfer through `g`) and `spend_reads_back_dispatched` (a transfer the walk dispatched at any depth, `u` equal to its amount). Their credit twins are `credit_reads_back` and `credit_reads_back_dispatched`.
**Teeth.**
- `gap_never_falls`: a transfer ledger holding `transferBase` and `transferBase + 4` is not contiguous. Two spends of 10 are each within the 10 it reads as left. They write `+2` and `+3`, keys the cell lacks, so `appendOnly` admits both. The ledger still reads 10 left: two spends of 10, each admitted against a cap of 10.
- `gap_world_not_contiguous`.
- `two_spends_refused`: `actFor` keeps only the first of two spends, and `effectsPinned` refuses the pair `duplicateEffect`.
**Premises.** No landed theorem gained a premise. The invariant is a premise only on the new read-back theorems, and it is discharged from genesis. The World-level theorems take `Std.TransOrd`/`Std.LawfulEqOrd` (`admit_written`'s, as `transfer_exact`). Visibility only: `dispatched_ok`, `sealTurn_firstDup`, `actFor_of_nodup` (InvokeTree) and `mem_set`, `set_pairwise`, `slotsOf_ascending` (WriteNext) lost `private`, with statements unchanged.
**Re-genesis / re-emit.** None.
**Second-agent read.** K30-READER: LAND. No statement is vacuous. Each disjunct of `effect_at_grant`, `grant_turn_cell` and `grant_turn_ledger` was checked on its own, and none follows from the premises alone. No public statement changed. Its three label fixes were taken.
**Critique.** `grant_turn_ledger` names the spend's `u` existentially. Only the transfer and credit forms link `u` to the call's amount. An enrolment or a carve is the same append (`LedgerSpend`), but no `*_reads_back` names its count. LEDGER-7's Σ only needs that `u` is what left fell by, which `grant_turn_ledger` gives. A sum over carves would need a `checkParent` read-back.

## KERNEL-62 · Whole-trie root binding (CX-KERNEL, 2026-10-20; cv 01a15849-3ae0)

**Decision.** Equal roots bind canonical tries, or the hash collides among the explicit
`bindingPres S vpre t u`: every node input of both tries, and every value input of
both listings. The value inputs are essential: a leaf node commits value digests,
so a list of node inputs alone cannot bind the values.

`Trie.digests_eq_of_root` is induction on the actual deployed trie datatype and
hashing equations, using WF and byte-encoding injectivity. It binds the ordered
key/value-digest listing. `HeadSound.root_binds` uses the existing HeadSound
instance to bind values, then Canon to reconstruct exactly the trie, including
representative and digest caches. `HeadSound.root_binds_sep` gives equality with
no escape under separation of that same finite list. The deployed instances are
`Receive.deployed_trie_root_binds` and `Receive.deployed_rows_root_binds`.

**Premises.** LANDED theorems gaining a hypothesis: none. LANDED statements
restated: none. New statements use the existing Canon and leaf-codec Fits
invariants, with the latter stated over the two listings. No global hash
injectivity, unbounded collision existential, axiom, or new deployed check.

**Vacuity read (author).** Neither equality nor a collision among these explicit
inputs follows from Canon/Fits/HeadSound alone. Canonical tries can hold different
values; a finite input list can be separated. Root equality does real work in
the induction. The separation corollary removes the escape. The unconditional
helpers identify actual hashing/list membership and do not use an empty premise.
Independent reader CX-READER-KERNEL returned LAND on all 12 new statements,
with the disjunct check and both real mutation teeth read; required fixes: none.

**Tooth.** The compiled kernel-sim rows probe changes one live leaf to a tomb and
requires the deployed root to change (`trie-binding:one-leaf`). All 64 seeds
pass. A separate actual deployed-spec run, logs/cxkernel-binding-tooth.lean,
passes normally and exits 1 when the value-domain hash ignores its bytes:
logs/cxkernel-binding-tooth-red.log:1 is
`FAIL trie-binding:one-leaf: different leaves kept the root`.
Its entire output was read, not only the expected line.

CROSS-LAYER: HOST: no Host path edited. Host.Proofs.Trusted.start_carry_commits can
now replace its named-not-proved roots-to-tries line using the deployed cells and
rows binding theorems, discharging their Canon/Fits from the carried World and
extending its explicit collision list by the two bindingPres lists. This is the
KERNEL ingredient; the stronger HOST conclusion is not claimed landed here.

**Critique.** Listing all node/value inputs costs theorem statement and proof
bookkeeping. It is necessary to cover interior-node and value collisions. Canon
is necessary because representative keys are caches not committed by the hash;
the result is not true for arbitrary manually constructed tries.

**Meta-critique.** Reusing inclusion soundness key by key would hide the requested
hashing induction and make the finite list depend on a queried key. The whole-tree
induction exposes exactly what the root commits. A node-only input list would
look smaller while silently losing the value-binding obligation.

## KERNEL-63 · Retired heads join the rows overlay's seal (CX-KERNEL, 2026-10-20; cv 01a1553a-c095)

**Decision.** Add bounded `takeListU` and `underU`, remove retired parents'
heads with `dropHeadsU`, and seal after that step. The batch now hashes surviving
written nodes once across row touches and retired-head removals.

**Premise price.** LANDED theorems gaining hypotheses: none. LANDED statements
restated: none. `rowsRun_eq` is literally unchanged; its proof uses the new
unconditional `dropHeadsU_seal`, which preserves both the full trie and freed
weight. `takeListU_seal` and `underU_seal` are unconditional too. No Store byte,
root, refusal, or wire format moves, so this is kernel:, not kernel!; no re-genesis.

**Requirement and measurements.** Required.rowsReq now marks all row operations
and all retired-head removals, then counts surviving marked nodes once at the end.
The old row probe contained no retirement. Add a real admitted turn retiring a
parent with two relation heads while birthing a parent with eight heads. At seeds
0–63 the real compiled rows run counts 960 hashes and requires 960; the previous
seal-before-heads path counts 1088. The new WASTE
`admit retire-heads-hashes-per-required` is 1.000 versus 1.134 for the old path.
The two paths reach identical rows roots and freed weight, and the retired
parent's bounded prefix listing is empty. Existing rows insert/retract/stem counts
remain 4416/512/24576. All 64 seeds pass; every existing WASTE row is unchanged.
Measured output: logs/cxkernel-final-sim64.log:76 and :101.

**Real regression plant.** Restore only rowsRun's old
`dropHeads E t (acc.1.seal ..., acc.2)`, build kernel-sim, run seed 0. Whole
output read: exit 1, logs/cxkernel-plant-heads-red.log:2:
`FAIL seed 0: retirement rows counted 17, required 15`.
That run emits WASTE 1.134. The good source was restored after the plant.
No check was removed or relaxed.

**Worstcut retires.** The scoped real benchmark passes and measures 1,041,249
hashes / 32,320 steps = 32.217 for both reopen and audit, exactly the previously
measured logs/perf6-honest2-retires.out. The workload retires grants with no
relation heads, so it cannot show a drop from this optimization. No wall-clock
benchmark is evidence here. New output: logs/cxkernel-worstcut-retires.log.

**Vacuity read (author).** The four new overlay/fold commutation lemmas are
implementation/specification equalities on arbitrary inputs; no disjunction,
contradictory instance, or new invariant premise. The unchanged rowsRun_eq ties
them to deployed admission. CX-READER-KERNEL independently returned LAND,
with no required fixes.

**Critique.** The measured gain is specifically head-bearing retirement, not
the old headless-grant benchmark. The fallback retainAtU arm may seal malformed
out-of-depth shapes; canonical rows use bounded paths and never take it.
The generic old dropHeads stays as the proof specification and mutation plant.

**Meta-critique.** Expecting the old retire benchmark and retract row to fall was
an untested workload assumption. Adding the missing admitted shape provides a
real measurement; relabeling the old constant rows would not.

**Landing authorization (ROOT, real 2026-10-20).** The measured retirement WASTE
row (1088 to 960 hashes over 64 seeds) is approved as a tightening under GATES
ownership. Its 1.000 ceiling is added in this commit; no existing ceiling rises.
The separate emptyHash-cache task is closed as stale by ROOT; no cache edit.

CROSS-LAYER: GATES (ROOT approved the measured row, real 10-20)

### KERNEL-45 item 3 FIRED as two runs of one term (LANG-75.11, PROT-6, 2026-10-23; CX-PROMO-6; RELEASE R-0050 under grant R-0049). Decision text; kernel lines changed: 0

Item 3's trigger fired. The trigger was "the first row whose invariant spans two objects changed in one turn", and that row is Std.offer's fuse: two offer rows, under two objects, consumed in one Turn (`Lang/StdOffer.lean`). It fired at the price item 3 named, "a separate judge (as LANG-44's row guards are)", in this shape:
- A matcher object's `fuse` returns two invokes of `take`, one to each party. Both carry ONE byte string, the deal.
- Each `take` runs as its own object. It decodes those bytes, reads its own offer and its peer's (the declared peer read, LANG-75.11), evaluates the generated term `offerJoint` on the two pinned offers, and retracts only its own offer (law 4, `rowParent`).
- Both retracts sit in one Draft, and that Draft is sealed once. The tree commits or fails whole.

**What it is not.** It is not a joint law, and it is not one judge. Nothing in the Turn observes both offer rows, or both session rows, together. Two runs evaluate one term. They agree on θ because they decode one byte string, and that is the matcher's guarantee (`fuse_calls`), not the takes'. An owner may root-invoke its own `take` with no matcher at all, so one session row is not a fuse. `Program.judge`, `deriveTurn` and the 85 / 86 / 59 / 51 / 21 law theorems are untouched.

**K stays deferred.** K is a kernel judge over the sealed Draft. Its trigger: the first row whose invariant spans objects of two packages, or methods no generator wrote, or the owner-root `take` named as a defect by a row's owner.

## KERNEL-64 · An object's head is fixed under the follower's fold (CX-KERNEL, 2026-10-23; cv 01a166f9-c61c, HOSTING-42 trigger (ii))

**Decision.** State, once over every Body, the receivers-wide fact HOSTING-42's strong member-socket form names as its trigger (ii): a live object's package slot never changes while the follower's fold runs. Stated at its true width, the object's HEAD (slots below `stateBase`): Kernel/Proofs/ObjectHead.lean.
- `turn_object_head`: a call derived (`receive`) from `w` and admitted to `w'`, at an object live in `w`: live in `w'`, still `kindObject`, slots below `lawBase` (package 0, owner 1) unchanged; and if the cell holds a package, every slot below `stateBase` (the laws too) unchanged. `submit_object_head`: the same of `submit`.
- `auditStep_object_head`, `audit_object_head`: THE FOLD. Along any log `audit` accepts (each Turn re-derived from its own event, each refusal re-judged), the same from the log's first World to its last. Objects are also immortal there (no receiver retires one).
- `audit_package_fixed`: the card's statement: `slotPackage` bytes and `packageOf X obj` equal at every World the audited fold reaches. `fold_package_fixed`: the same over `World.fold` of an `Honest` log (`audit_ok`).
- Proof route: `effect_at_object` names who may have an effect at an object; each such effect is `writeOf`'s act with keys bounded: `write` at state keys (`applyEdits` sets/erases only `stateBase + i`), `law` at law keys `[lawBase, stateBase)` (and `law_judged`'s `packageOf = .ok none` excludes a programmed object), an invoke at state keys (`invoke_ok`'s `checkState`); a nested invoke's own effect is THE act at the object through `sealTurn`'s `firstDup` (the order laws, `invoke_tree_slots`' price). Made public for it: `foldCalls_effects`, `actFor_none` (InvokeTree), `get_applyOps_ne`, `diffOps_keys` (WriteNext); statements unchanged.

**Not claimed.** Over a bare `World.fold`: the writer's fold admits a hand-made Turn that writes slot 0 of an object or retires it (`touchCheck` checks the pin, `postWrite` of a RAM cell only its size: READ, not built as a tooth). The fact is the receivers', so it needs every step derived. Laws at `lawsOf`: the statement is slot-wise; two slot lists equal at every key are equal `lawsOf` only on canonical cells (`CellsCanon`). "At birth": an object born inside a log starts its theorem at the World after its creating turn.

**For HOSTING (a finding, not a fix).** Hosting/Proofs/Socket.lean's `FollowRun.step` advances follow's World by `World.fold X.env f.world l = .ok g.world` with `l` unconstrained. At that premise trigger (ii) is not true; the consumer needs `Honest X f.world l` per step (`fold_package_fixed`), or the follow loop's audit (`audit_package_fixed`).

**Plants, MEASURED on hbox wt/kernelpkg (every library module but Hosting.Proofs.Reply, which alone exceeds 10G and could not be built beside a running judge at 6G; logs /tank/dregg-build/nanodregg/logs/kernelpkg-*, scripts logs/kernelpkg-plants/).**
- Control: the same 480 modules GREEN (kernelpkg-libs-good.log, `Build completed successfully`).
- The brief's plant, verbatim (Derive `law` without `req pkg.isNone (.hasMethods obj)`): RED first at Kernel/Proofs/Authority.lean, three landed theorems: `law_judged` (206: its `packageOf X obj cell = .ok none` conjunct IS that check), `law_authorized` (173) and `law_adopt_refused` (231), which only re-pattern the `law` do-block. Everything downstream, this module included, is not reached.
- The same plant made CONSISTENT upstream (overlay_relaw.py: `law_judged` and `law_next_slots` lose the `packageOf … = .ok none` conjunct, the check's only content; proofs re-patterned positionally in Authority, Rooted, Ledger, LedgerNext, InvokeTree, History; this module's law-case `obtain` loses `hp`): the whole tree reds exactly ONE theorem, `turn_object_head` at ObjectHead.lean:186 (`Unknown identifier hp`: the programmed object's law case), and every module that builds without it stays green (kernelpkg-plant-relaw.log).
- Correction to the brief: the relaw plant does NOT falsify "the package slot is fixed". A law turn writes keys in `[lawBase, stateBase)` only, never slot 0; it falsifies the programmed-object half (the laws of a programmed object). The package-slot falsifier is an invoke without `checkState new` (a run returning a key below `stateBase` rewrites slot 0 through `diffOps`: INFERRED from the definitions); its one-line plant reds `invoke_ok` first (Kernel/Proofs/Tree.lean:42, kernelpkg-plant-nostate.log), where that conjunct is stated.

**Price.** Landed theorems gaining a hypothesis: none. Restated: none. Re-genesis / re-emit: none (proof-side only). New: one proof module, six theorems, nine private lemmas; four lemmas lose `private`.

**Vacuity read (author).** No disjunction. Premises are the derivation and admission of a real step (satisfied together by `object_history_chain_witnessed`'s signed invoke) and a live object. The conclusion is an existential over `w'.live`, not implied by the premises without the receivers: the consistent plant above makes it unprovable while every other theorem stands.

**Critique.** The theorem is only as wide as `effect_at_object`: a new Body that writes an object must extend that totality, and this proof then reds at the new case, which is the intent. The nested-invoke case pays the order laws through `firstDup`, though the statement does not need them (`revisited` already excludes a second invoke). Slot-wise equality is weaker than `lawsOf` equality; a consumer reading laws needs `CellsCanon` too.

**Meta-critique.** Bias: trusting a check's NAME for what it protects. The brief named the relaw plant as the package falsifier because the check is called `hasMethods` and sits next to `packageOf`. It guards the laws of a programmed object, not its package; building the named plant alone would have reported "red" for a conjunct the card did not ask about. Second bias: a plant that "reds this theorem by name" is easy to manufacture. The consistent overlay is my construction, so its meaning rests on its upstream restatements dropping only the conjunct the deleted check proves, which is checked by the overlay's diff (logs/kernelpkg-plants/relaw.diffstat), not by a second reader.

## KERNEL-65 · A written row reads back on the World that admits it (CX-BACKLOG, 2026-10-23; cv 01a16821-5828, HOSTING-44's first gap; method R-0069)

**Decision.** The rows had a read-back for a slot no touch names (`foldRows_get_out`) and none for the slot a touch WROTE. HOSTING-44's `answered_row_is_kept_answer` therefore stopped at the run: it could say what the answer call writes, never what the committing World holds. Added to `Kernel/Proofs/Rows.lean`:
- `foldRows_touch_get`: in a turn's fold (slots distinct), the touch at `.row key` decides the slot. The fold reached it at canonical rows `r0`, its step left `r1`, and the end holds at `.row key` what `r1` does.
- `admit_row_touch`: the same over `World.admit` (`dropHeads` removes heads, never a row).
- Per act: `rowStep_upsert_get` / `admit_upsert_row` (the leaf `.row amt v ver`, some version), `rowStep_insert_get` / `admit_insert_row`, and `rowStep_retract_absent` / `admit_retract_row` (the slot absent).
- `rowStep_retract_absent` moves here from `Lang.Proofs.DispatchRows`, where it was proved from outside the kernel. `Lang.DispatchRows.foldRows_retract_absent` is deleted: `foldRows_touch_get` is its general form. `Lang.admit_retract_absent` is now `admit_retract_row` under the name `StdOfferFuse` reads (FABLE-T's file). It is deleted when that file is next touched (cv 01a16821-581a).
- The consumer, `Lang.Bell.answer_commits` (`Lang/Proofs/BellCommit.lean`): a signed call invoking a Bell's `answer`, derived and admitted from canonical rows, leaves a World that holds `rings[(k, nb)] = answeredVal x y` and no `pending` row there. This is half of the HOSTING-44 join. The other half is card cv 01a16821-5835: the commit step behind `journalAt (txIdOf c)`.

**Plant (MEASURED, hbox `logs/backlog/plants/C2-upsert-drops-value.build.log`).** The upsert writes `.row amt ByteArray.empty ver` instead of `v`. `Kernel.Proofs.Rows` goes RED at `rowStep_upsert_get` (l.713), and at `rowStep_weight` (l.187: the stored size moved). Reverted byte-identical.

**Critique.**
- The version is existential. What `ver` is (the old version + 1, or the relation's floor for a fresh row) is in the step and not stated. Nothing reads it yet. A pin over the new row would need it.
- `answer_commits` premises the package read at the call's PINS (`pinned`), while `answered_row_is_kept_answer` reads it on follow's World (`worldLook`). The two agree only through the commit step that card 3 reconstructs.

**Meta-critique.** The gap was not hard. It was unstated because each consumer (`invitation_once`, the escrow) needed only the retract, and the retract got a Lang-side lemma beside its first use. The general lemma was one fold away. A twin at the consumer is how a kernel fact stays unwritten.

## KERNEL-66 · The pins are compared before the receivers: a stale call is declined `stale`, never judged on the World as it is now (FIX-KERNEL, 2026-10-24; COLLATION-20261024 A1, READ-KERNEL D1; method R-0069)

**Finding (READ-KERNEL D1).** `submit` ran `receive` on the Host's CURRENT cells and only then `World.admit`, whose `touchCheck`, `rowStep` and `checkRanges` compare the pins. `pinned` hands a receiver the live cell at a pinned id whatever the pin's digest says, so when a pinned cell had moved, any receiver or law that failed on the new state answered first (`lawDenied`, `program`, `missingCell`, `noGrant`, …). That verdict is authenticated, so `judge` RECORDED it: charged to the member's `refusalsPerWindow` and final for the txId. KERNEL-54 exists so that honest contention spends no budget; it was defeated for every receiver refusal. Two comments claimed otherwise (`Submit.lean` "an AHEAD stale is not final"; `Call.lean` "`World.admit`'s pin check refuses the Turn"). A call with garbage pins also paid a full derivation (up to `treeTicksMax` = 131072 ticks) before it was declined.

**Decision.** `submit`'s order is now: journal (`replayed`) → recorded refusals (`refusedFinal`) → `signedBy` (the World the call names, the signature, the member's key: what `authenticated` checks) → `checkPins` (every cell pin, row pin and range read against the Host's World: `stale`) → `deriveTurn` (the receivers, on the pinned view) → `World.admit`.
- `checkPins` (`Kernel/World.lean`) compares exactly the three disagreements `admit_stale_pin` says an admission `stale` is: a cell pin against its entry, a row pin at a row slot against its row and its relation's floor, a range read whose relation has a head and whose listing fits against that listing's pin. A head pin, a range on a relation with no head and a listing past its `most` are not pin disagreements and pass (admission names them `rowShape`, `noRelation`, `rangeTooLong`).
- The pins come AFTER `signedBy`, not before. Reading the log needs a live member, its key, its signature and a follow grant (READ `Protocol/Envelope.lean` `Envelope.check`), so cells are not public; a pin comparison answered to a party that holds no key of the member would be an oracle on them (a forged signature with a guessed pin would read `stale` or `badSignature` by whether the guess was right). A rotation's key check is its receiver's own (`authKey` runs `rotate`), so an outsider's self-signed rotation is answered `notPrecommitted` before any pin is read. A member could already learn a pin's agreement from admission, so nothing it can learn moves.
- `submit` no longer calls `receive`; it calls `signedBy` and `deriveTurn`, the two halves of `receive` (`receive_signed`: `receive = signedBy >>= deriveTurn`, with `keyRule_deriveTurn` for the rotation), so the derivation is one (law 1). `authenticatedBy` is `signedBy` passing (it was a second copy of the same three checks).
- `Verdict.verified` is unchanged: `stale` is decided past the one verify, as before.

**Theorems** (`Kernel/Proofs/Audit.lean`, `StaleOnly.lean`, `Receive.lean`).
- `stale_declined_before_receive`: a call neither journaled nor recorded, `authenticated`, whose `checkPins` fails, is `submit … = .error (.rejected (.stale y))` and `judge … = .declined (.rejected (.stale y))`. No premise names `receive` or `deriveTurn`: what any receiver would say is irrelevant.
- `receive_not_run_on_stale`: under the same premises, `submit { X with program := P } w c` is the same `stale` for EVERY `Program P`: no method tick and no law judgement is spent. The cost of a garbage-pinned authenticated call is its one verify, its key read and its pin lookups.
- `checkPins_error_never_admitted`: a call whose `checkPins` fails is one no order would admit (whatever `receive` derives, `World.admit` takes none of it), from `admit_pins`, `admit_row_pins`, `admit_range_pins`. So the reorder changes the NAME (and the record), never whether a call lands.
- `checkPins_ok_iff` (agreement, exactly `admit_not_stale`'s premises) and `checkPins_error_stale` (it refuses nothing else).
- KERNEL-54's `judge_stale_declined` / `judge_recorded_not_stale`: statements unchanged, proofs unchanged. `submit_ok`, `submit_verified`, `verified_eq_false_iff`, `authenticatedBy_verified`: statements unchanged, proofs re-run over the new order. RESTATES: none.

**Row and plant (MEASURED, hbox wt/fixkernel `.lake/fk/`).**
- `kernel-sim`'s `probeRace` (arms `race-loser:stale`, `race-loser-declined:declined`, `race-law:lawDenied`): a `grows` law (a write must lengthen the first state slot: it reads the OLD state), an object under it, two writes signed against ONE observation; the winner lands "aa", the loser "a" is `stale` and declined, and the tooth reads `receive` on the winner's World refusing the loser `lawDenied`. It runs on branch Worlds, so the Host's World and the WASTE populations do not move. Random arm 7 (a stale pin) no longer skips a lawed object. `kernel-sim --seeds 64`: ALL PASS (`sim4.out`).
- Plant: `submit` without the `checkPins` step (the old order): `FAIL seed N: probe race: the loser was refused lawDenied, not rejected stale` on 64 of 64 seeds, and `FAIL planted refusals never met: [race-loser:stale, race-loser-declined:declined]` (`plant2-sim.out`). Restored byte-identical.
- WASTE: `admit trie-hashes-per-turn` 14.087 → 14.092 (65370 hashes / the same 4639 turns; every hash required, 1.000): arm 7's trajectory, not waste. Every per-required row is unchanged.

**What re-emits: nothing.** No wire shape, cell, record or code changed: a stale verdict was already declined and unrecorded, and the refusal record format did not move. What changes is which calls are declined `stale` instead of recorded under a receiver's name. A log holding such a record (recorded under the old order) still FOLDS (`World.refuse` is unchanged), but the audit re-judges a record by `judge` on the World before it, which now declines the call `stale`, so that step no longer audits (INFERRED from `recordedBy`; not run). There is no deployed log to re-genesis.

**Residual (named, not fixed here).** A range read whose listing grew past its `most` since the call observed it is still `rangeTooLong`, recorded: the pin of a listing that cannot be computed is not compared. KERNEL-54's own unpinned-state refusals (allowance, relation fullness, birth ids, budget) are untouched.

**Critique.** (1) `submit` now composes `signedBy` and `deriveTurn` instead of calling `receive`; `receive_signed` keeps the two equal, but a future edit to `receive` that does not go through those halves would be invisible to `submit`. (2) The rotation's receiver runs twice on the Host path (once in `authKey`, once in `deriveTurn`); it reads one member cell. (3) A row pin on a relation that does not exist is compared against the floor-0 absent pin: a wrong digest there reads `stale` where admission would have said `noRelation`; both are refusals, and the first is declined.

**Meta-critique, naming a bias.** The first design put the pins before the signature (cheapest; "stale before anything") and it built green on all 755 jobs. That is a bias toward the cheapest refusal and toward the brief's wording ("before any receiver or law"), read as "before everything". Its cost was a confidentiality hole, found only by asking who may receive a `stale` answer. Build-green measured nothing about it, and no theorem here states it either: the oracle argument is prose. The second bias is to trust "one verify" (PERF-1) as a constraint rather than as a measurement; it held here, but it shaped the design before the oracle question was asked.

## KERNEL-75 · `install` is a call an object may make: a method's returned `install` is derived as the object through the one install receiver, checked as a member's (2026-10-26; FABLE-META; with LANG-86; CROSS-LAYER: LANG owns the generator, KERNEL the arm; design `redregg/work/promo/DESIGN-META.md`)

**What changed.** `Body.callable` admits `.install` (six callable kinds: `invoke`, `transfer`, `account`, `credit`, `grant`, `install`; the `notCallable` docstring names them). Nothing else in the kernel moves: `dispatch`'s `install` arm already ran at any actor (`install X look c ⟨actor, wk.born⟩ pkg`: `checkInstall`, then `bornAt` of a ROM package cell), it takes no authority from the actor and reads no owner, so an object installing is an act every member could already perform, with the same check, at the signer's pinned view.

**Why widening this assertion is sound (the pause the charter asks for at a weakened check).** The line between callable and not is "spends nobody's authority and changes no cell": `install` is the only receiver on that side besides `account`. What an object still may NOT do and why: `create` (the object would be owned by the signer through the object's choice: a confused deputy), `enroll`/`rotate`/`revoke`/`issue` (member or issuer authority), `write`/`law` (KERNEL-28: effects are derived as signed and spend the owner's authority).

**Theorems.** `Kernel/Proofs/Generated.lean`: `PackagesChecked X look d` (every package cell `d` bears holds bytes `checkInstall` accepted at `look`); `tree_package_checked`: every level of a call's tree below the signed call bears only checked package cells (`tree_all` with five callable cases; `install`'s is the receiver's own check). `tree_zeroBorn` (Ledger) gains the `install` case (a ROM cell is not a value cell). LANG's `callsOf_callable` still makes `notCallable` unreachable from `Lang.program`; the kernel keeps the assertion where calls enter (law 4).

**Floor.** The kernel whose nested `install` is `stepped wk (.ok ⟨bornAt …⟩)` without the check: `tree_package_checked` fails at its `install` case. The deployed run that reaches the check: `Lang.Journey.Gen` GN4 (a generator of bytes that are not a package is refused `program decode …` at the nested install, nothing born).

**What re-emits.** Nothing: no wire, no cell shape, no refusal code moves.

**Critique.** `tree_package_checked` is about the TREE below the signed call; the signed `install` itself is checked by the same receiver, and the composition over `derive` (thirteen cases) is not written: the new power is the nested one, and the theorem is about the new power. A generator cannot learn the id it bore (a nested call returns nothing), so "generate then create" is two Turns; DESIGN-META §6.3 names the `createOf` arm and its authority question rather than adding it.

## KERNEL-67 · The kernel memo's documentation debt: comments and decision entries that said the opposite of the code (FIX-KERNEL, 2026-10-24; READ-KERNEL B2, B3, B4, B7; method R-0069)

**Fixed (text only; no definition, statement or bytes change).**
- `Body.transfer` / `Body.credit` (`Call.lean`): the grant chain is for `transfer` / `credit`, whose cap the move spends; `mutate` moves no value (KERNEL-60; the code: `Ledger.lean` `ownerAuthority … (.transfer 0)`, `(.credit 0)`). They said `mutate`.
- `Refusal.duplicateEffect` (`Call.lean`), `planted` and `probeSeal` (`Sim/Gen.lean`): it IS reachable on the signed path (a method returning two transfers out of the object's own account; `Proofs/LedgerNext.lean` relies on it). They said no receiver produces it.
- `checkJournal` (`World.lean`), READ-KERNEL B7: its `replayed` and `refusedFinal` arms are unreachable from `submit`, which answers both before deriving. They are NOT deleted: they are the follower's (`World.fold`, the audit), which admits a log's Turns with nothing before them, and a fold without them would admit a replayed or a recorded txId. The docstring now says so. Neither "delete" nor "make reachable from submit": the arms are reachable where they are needed.
- `decisions/kernel.md`: KERNEL-17 (`Status: open`, "the journal is not pruned") marked SUPERSEDED by KERNEL-33; KERNEL-23 (`Status: proposed`) marked BUILT as KERNEL-30; the "not yet built" titles of KERNEL-23/24/25/26 name what built them; KERNEL-55's (PROPOSED) title points at its RULED/BUILT parts.

**Not done here, and why (each a card).**
- The twin read: `refusedAnswer` (submit) and `checkJournal`'s inner match (admission) are one KERNEL-44 read written twice. One function for both moves `submit`'s first two matches, which ~8 proofs across Kernel and Protocol unfold. Law-1 work, not a doc fix.
- Three duplicate detectors → one (B5): `firstDup` needs a lawful `Ord` (the premise the touch theorems carry); `dupBy` and `rowsRun`'s inline count are O(n²) with no order. One detector is a fork: `firstDup` everywhere puts the lawful-`Ord` premise on the row theorems; `dupBy` everywhere is O(n²) at `touchesMax` = 512. It needs its premise priced first.
- Refusals under the wrong name: `rowView`'s `rangeUnpinned` for a relation with no head (B8) and `spendAt`'s `short` reused as `grantWidens` for a full ledger (B10). Each needs a new `Refusal` constructor. `refusalNames`' order IS the recorded code, so every code after it moves (a record-code flag day, re-genesis). That is not a doc fix.
- A signed row for `duplicateEffect` (a two-transfer method in `lang-journey`).

**KERNEL-66 amendment (2026-10-24, FIX-KERNEL; lang-journey was RED on main since f1839ed).** Three journey rows expected the old order. LB8b (a second answer of one ring over the view the first answer moved) expected the guard's `rung: answered`; LH7b (a select over the view before a re-pin) expected the method's `support0 moved`; P8.2 (a plan signed before the revoke of its provider's grant) accepted either `support0 dead` or `rejected stale`. Each call's pin moved, so under KERNEL-66 each is `rejected stale`, declined before the guard or method runs. That is the name KERNEL-66 means: the refusal names the stale observation, not what a receiver says of the new state. The rows now expect exactly `rejected stale`; LB8 and LH7 still read the guard's and the method's own refusals on a current view. MEASURED (hbox wt/fixkernel on 0a299c8): lang-journey GREEN in both modes. THE BAR (`--records 60 --standing`) reads PASS, and its `--harness-control` reads RED harness-control with every comparator fired, so no `refused stale` appears (FIX-PROTOCOL's BAR line was INFERRED; it does not reproduce). Its expected word is `declined stale` (scripts/bar.sh `STALE`), unchanged. A different defect found while reading: `Protocol.Command.staleBehind` (Machine.lean) still classifies a call stale by the OLD order (`receive`, then `World.admit`'s `stale`). On follow's World, a call whose pin moved but whose receiver also refuses on the new state reads `false`, so its settlement stays `open` where the Host now declines it `stale`. Its twin-free form is `checkPins` on follow's World. `staleBehind_spec` and `Behind.lean`'s finality proofs restate with it. This is PROTOCOL's file; it is handed to FIX-PROTOCOL as a card.

## KERNEL-68 · The meter: a Turn names its member and its ticks, and the kernel counts a member's ticks per window as it counts refusals — the second KIND of one typed window trie (FABLE-OBS, FABLE-OBS-2, 2026-10-26/27; DESIGN-OBS §1, redregg/work/promo/DESIGN-OBS.md; FRONTIER-AXES axis 4)

**Decision.**
1. `Turn` gains `member : D` and `ticks : Nat` (`Kernel/Turn.lean`): who signed the call, and the ticks
   its whole tree of runs used (0 for every Body but an invoke). `Receive.sealTurn` sets both from the
   call and the Walk's pool (`deriveWithTicks`); every follower re-derives them from the event
   (`Receive.rederive`: a page carries the call, never the writer's Turn), so a writer that states another
   member or count is `eventMismatch`. The log record grows by 40 bytes (`logWeight`; `Codec.Kernel.turn`
   gains the two fields); `checkBounds` refuses `ticks` past `treeTicksMax` (`overBound .ticks`): a forged
   log cannot jump the meter.
2. The refusals trie is the WINDOW trie, and its key type is typed by kind: `WindowSlot D = refusal (k :
   RefusalSlot D) | meter (k : MeterSlot D)`, with `RefusalSlot` unchanged (`tx`, `count`, `total`) and
   `MeterSlot = ticks (member) (win)` (kind byte 3, one key width with the others, the existing `count`
   leaf). Two readers, each over its own kind: `refusalAt : RefusalSlot → Option RefusalLeaf` reads
   `.refusal k`; `meterAt : MeterSlot → Option Nat` reads `.meter k`. `World.admit` checks `ticksUsed +
   t.ticks ≤ Bounds.ticksPerWindow` (`checkTicks`, after the charge and the births; refused `ticksBudget
   member`, a class-(A) rejection `judge` records as it records `overAllowance`) and, for a Turn with
   ticks, writes the leaf at `.meter (.ticks t.member (refusalWindow (height + 1)))` — the window the Turn
   lands in, the journal's — before the window prune (`commitMeter`: one trie path per invoke, none for
   any other Body). `refusalFits` bounds the leaf (1 ≤ n ≤ `ticksPerWindow`, the current window);
   `keptRefusal` prunes it with the counts; `refusalsCounted` accepts its VALUE (critique 1) and bounds its
   COUNT: a new `CountedOk` clause, `Σ meterKeyOne ≤ height % windowMax + 1` (one leaf per invoking member per
   height of the current window; the meter's twin of the journal's bound), checked by `refusalsCounted` so a
   decoded base with more meter leaves than its window has heights is `kernel/refusals-counted`, and the
   refusals trie's size stays bounded by the check alone (`refusals_bounded` gains `+ Σ meterKeyOne ≤
   windowMax`; `refusals_length_le` is `4C + 1 + windowMax`; `Host.Bounds.refusalsBytesMax` + 50·windowMax, so
   `worldBytesDerived` 91,914,346 → **91,965,546** B and `baseRecordMax` 91,965,674).
3. `Bounds.ticksPerWindow := 16 * treeTicksMax` (2^21): sixteen full-budget trees per member per window,
   by analogy with `refusalsPerWindow = 16`; ~70,000 invokes of THE BAR's size.
4. Probes and rows: kernel-sim `probeTicks` (sixteen full trees admitted on a copy, the seventeenth
   `ticksBudget`, a tree past `treeTicksMax` `overBound`; planted names `ticksBudget`,
   `ticks-window:ticksBudget`); lang-journey M0 (B's meter reads back as the sum of the ticks of B's
   admitted Turns in the session log, and A's founder has none).

**Why.** A member may spend `treeTicksMax` ticks per call at every height it can get a call into, bounded
by nothing (READ `Derive.lean` `poolOf`); refusals were given a window budget (KERNEL-44) and admissions
were not. The honest self-measurements of a World are the functions of its log the kernel maintains and a
follower re-derives (DESIGN-OBS §1.2); the window trie is the one place the kernel already keeps a
per-window per-member counter under the chain, pruned on the schedule a meter wants, and readable by a
path against its root. A kernel-owned CELL would be touched by a Turn that did not name it (`admit_frame`,
`fold_potential`, every pin theorem) and a receiver-written one would serialise a member's calls on its pin
(KERNEL-54's reason refusal counts are not pins). A fifth trie is the cut HOLISTIC-KERNEL §2.2 judged
wrong. The member in the Turn rather than recovered from the event: the kernel never reads the event; a
decoder in `Env` would sit in `World.admit`'s hot path and in every kernel theorem's premises; `Refused`
carries `member` for the same reason (KERNEL-50).

**Why the key is TYPED (FABLE-OBS-2).** The first build (FABLE-OBS) put the meter in `RefusalSlot` as a
fourth constructor. Then every theorem that says "a Turn moves no refusal leaf" — `admit_refusalAt`,
`Frame.refusals` — was false at the meter key and gained `k ≠ .ticks t.member win`: a hypothesis on two
landed statements, to be discharged by every reader (`by simp` where `k` is a literal, a case split where
it is a variable — `admit_refusalsOk`, `admit_countedOk`, `Settle`). The memory rule
(minted-price-premises-not-only-cost): a design is priced in the premises it puts on theorems already
landed. The question asked of this lane: can the exclusion be by the DEFINITION of the refusal window —
its domain — rather than by a hypothesis? Yes: `refusalAt` over `RefusalSlot` cannot NAME a meter key,
so `commitMeter_get_refusal` holds by constructor disjointness with no hypothesis, and the two landed
statements are unchanged (law 1: one trie, two kinds, each theorem over its own kind). The meter's own
theorems are `admit_meterAt` (every meter leaf but the turn's own, which is in its footprint as its cells
are), `admit_meterAt_self` (the turn's own, bumped by what it spent, never pruned: it is keyed by the
window the prune keeps), and `Frame.meter`, a NEW clause. The wire is the same as the first build's.

**Alternatives.** (a) Bytes per member per window (Σ `charge`) first: cheaper and computed by the kernel
with no receive-layer trust; declined as the FIRST meter because bytes already have a global budget
(`allowance`) and ticks have none; it is the second constructor of `MeterSlot`, same leaf, same check
(DESIGN-OBS §1.4). (b) A `ticks` field in the journal entry so the meter is a tally of the journal
(KERNEL-50's property for refusals): restates the journal leaf, its injectivity and every `JournalHead`
theorem, for a check whose only reader is a base decode. Declined. (c) A member only on invoke Turns
(`Option D`): a forged-log probe shape on the wire. Declined; every Turn naming its signer is what B1
(authority confinement) wants. (d) The meter as a fourth `RefusalSlot` constructor (the first build):
declined for the two hypotheses above.

**Price — premises on landed theorems, enumerated (the honest table).**
| theorem | first build | as landed | why it cannot be 0 |
|---|---|---|---|
| `admit_refusalAt` | +1 (`k ≠` the meter key) | **0** (typed domain) | — |
| `Frame.refusals` | +1 premise | **0** (typed domain) | — |
| `Agree` (`check_local`'s premise) | +1 field `meter` | **+1 field** | `Agree` IS the read set of `check`, and `check` reads the meter; the only shape that keeps it is not checking |
| `admit_comm` | (pending) | `RefusalsCanon` → `RefusalsOk`; **+1** `hmeter` (same member → both spend ticks → `used + t₁ + t₂ ≤ ticksPerWindow`) | a theorem of the model: two turns of one member that together pass the window do not commute (the second is `ticksBudget`); `Ok` because a window boundary needs fits to know a future window's leaf is absent; guarded so zero-ticks turns owe nothing; NO consumer in any proof |
| `World.RefusalsOk` | — | RESTATED over the trie's keys (`refusals.get`, `WindowSlot`) | it must bound the meter leaf; through `refusalAt` it no longer would |
| `Checked` | +1 field `ticks` | +1 field | the record of `check`'s clauses |
| `World.CountedOk` | — | +1 clause (the meter's leaf count ≤ `height % windowMax + 1`) | an invariant, not a premise: `fold_countedOk` proves more, `refusals_bounded` needs it; a decoded base is refused by it |
| `Host.Proofs.Deployed.admit_listing` | — | **+1** `hf : w.RefusalsCanon X.env` (and the refusals listing in its statement) | the listing after an insert is known only on a routed trie (`toList_insert_perm`); discharged by `Kept` in `fold_listing`, every reached World's |
| `receiveWith_sealed`, `receive_of` | gain the ticks binder | the same | `derive` returns the Walk's pool |
Restated by binder: the Turn construction sites (MEASURED 26 in 18 files at the first build), `Codec.Kernel.turn`
and its size/injectivity theorems, the window families that case on the slot (`refusalFits`, `keptRefusal`,
`RefusalLeaf.fits`, `refusalKeyBytes`, `refusalsCounted`, `RefusalsBound`, `RefusalsHead`, the Codec slot
codec and `WorldSize`, `Receipt.rpath`'s key type). Flag day `kernel!`: the Turn record, the slot codec and
the refusal code table (`rejectNames` + `ticksBudget`) move, so every pre-meter Store is `shapeMismatch` and
re-geneses (none deployed); `codec-vectors` and `generated.rs` re-emit. Waste: `admit trie-hashes-per-turn`
rises by one path for invoke Turns only (the sim's `Required` counts it through `fresh`); `submit
bytes-per-turn` falls (40 bytes in numerator and denominator).

**Refuses.** `ticksBudget MEMBER` (recorded, final within the window), `overBound ticks`, `shapeMismatch`
for a pre-meter Store, `kernel/refusals` for a meter leaf outside its window or past `ticksPerWindow`.

**CRITIQUE.** (1) `refusalsCounted` cannot re-tally a meter leaf from the trie (the Turns are not in it), so
a decoded base with a forged meter passes the state check and is caught only by the trust a received base
already needs (`CheckpointTrusted`, a sponsor's pin). KERNEL-50's "a function of its records" holds for
refusals and not for the meter; the fold theorem (the meter at `(m, win)` along an audited log is the sum of
the window's Turns' ticks by `m`) is NOT yet written: the next step. (2) The cap is a taste number with no
OWNER: a member cannot buy or be granted more. If a row (the Bell's resident, an agent member) approaches
2^21 ticks in a window, the honest growth is `Right.ticks cap` as a counted right carved from a founder's
World grant, spent per invoke like `enroll n`. (3) 32 bytes of member on every record for a counter only
invokes need. (4) The trie's field and family are still named `refusals`/`refusal*` while the type says
`WindowSlot`: the rename (`World.window`, `windowSpec`, `WindowLeaf`…) is a card, not this landing — it is
a sed across ~16 proof files with no theorem behind it, and it would collide with every live lane.

**META-CRITIQUE.** The first build priced the meter at "0 hypotheses on landed theorems" (DESIGN-OBS §1.7)
and the build found four. The miss was the one the memory names: pricing hashes and binders, not premises —
the design said "a new key kind in an existing trie" and did not ask what every theorem quantified over
THAT TRIE'S KEYS would now have to say about the new kind. The typed key is what "a new kind" should have
meant from the start. The brief said "ticks per window per member is the obvious one"; the bytes meter is
cheaper and more honest and was nearly built first; ticks won only because it is the hole with no cousin.

**Status.** landed as `kernel!:` (FABLE-OBS.report.md holds the hash and the judge's map lines).
## KERNEL-69 · The authority is fixed at genesis: `Authority {certifiers, threshold}` is a genesis input, committed in the origin (`domOrigin` v3) and carried in the World as one ROM cell at its content id (2026-10-26; FABLE-TRUST-4; CROSS-LAYER: PROTOCOL owns the start codec and `genesisLeaf`, HOST the `host genesis` options; design `redregg/work/promo/DESIGN-TRUST.md` §1.2, §4.3, BUILT-4; with PROTOCOL-77)

**What changed.** `Kernel/Receive/Follow.lean`: `Authority {certifiers : List ByteArray, threshold : Nat}` with `Authority.none = ⟨[], 0⟩` (every World that names nobody); `GenesisInput` gains the certifier keys (a raw list) and the threshold (`nat64`) after the founders, so `inputOf`, `originOf`, `originPre`, `genesisWorld`, `checkGenesis` and `genesis` take `auth` after `founders` and `domOrigin` moves `v2 → v3` (a genesis under v2 is no genesis under v3: every Store re-geneses). `genesisWorld` inserts `genesisEntries` = the founders' entries then the authority cell: `authorityCell a` (kind `kindAuthority := 5`, discipline `.rom`, slots: the threshold at 0, the certifier count at 1, certifier `i`'s key at `2 + i`) at `authorityId X a = romIdOf X.env (authorityCell a)`. `authorityOf w` reads it back as the one live `kindAuthority` cell (two or none is `none`: a verifier handed such a World refuses rather than choose). `GenesisRefusal` gains `tooManyCertifiers` (more than `slotsPerCellMax - 2`), `certifierTooLong i`, `repeatedCertifier i` (a quorum counts distinct keys), `badThreshold` (zero with certifiers listed, or past their count: a quorum nobody, or nobody ever, meets); `checkGenesis` checks the lengths and the threshold first, then each founder and certifier, and weighs the World last. `Kernel/Receive/Call.lean`: `kindAuthority`, `slotThreshold`, `slotCertifierCount`, `certifierBase`. `Protocol.Head.Authority` (PROTOCOL-76) is this object; the Protocol copy is deleted.

**Why a ROM cell at its content id, and not a World field or a reserved id.** A `World` field is the shape DESIGN-P6 §7.1 forbids (every World fact is a cell or a root). A cell under an origin-derived id, as the founders' are, would be a ROM cell at a non-content id and contradict `RomContent` (every live ROM cell sits at `romIdOf` of itself: KERNEL-3, `admit` refuses any other ROM birth `notContentId`); a RAM cell would be immutable only by the absence of a receiver that names its kind, a belief and not a theorem. At its content id the cell satisfies `RomContent` by construction and `fold_rom` (ROM is forever) keeps it, unchanged, across every admitted log — the immutability a verifier needs is a landed kernel theorem, not a new invariant. The price of finding it by kind is one scan of the trie at adopt and genesis (`atGenesis` already scans there).

**Theorems.** `Kernel/Proofs/Origin.lean`: `Authority.Fits` (at most `slotsPerCellMax - 2` certifiers, each within the raw bound, no key twice, the threshold within the count and zero only for `none`); `checkCertifiers_ok`; `checkGenesis_ok` and `genesis_ok` restated over the six clauses; `genesisInput_lawfulOn` and `inputOf_fits` over the longer input; `genesis_inj` (and `_sep`) conclude `auth = auth'` too: **two geneses with one origin had one authority** or their inputs collide. `Kernel/Proofs/Rooted.lean`: `mem_genesisEntries`; `genesis_live` over `genesisEntries`; `genesis_rooted` (the authority cell is no grant); `genesis_romContent` now reads "genesis bears one ROM cell, the authority, at its content id". `Kernel/Proofs/CellsFit.lean`: `genesis_cellsFit` fits the authority cell under `Authority.Fits`. `Host/Proofs/Deployed.lean`: `genesisEntries_length = 2n + 1`, `genesisWorld_codecFits` over it. `Protocol/Proofs/FollowHead.lean`: `genesisWorld_atGenesis` with `genesisLeaf` admitting the authority cell; `atGenesis_object` still holds (`kindAuthority ≠ kindObject`). Hypotheses added to landed theorems: 0 (a binder `auth` on every statement over a genesis World; `Authority.none` at every deployed call site, so every row and Store behaves as before up to the origin).

**What is NOT here.** No producer of a certificate (the Store signing seed: Ember's, cv `01a1769d-2f64`) and no consumer beyond the carrier: the `log`/`read` reply field, `Thin.accept`'s requirement, the head law's `uncertified` and `foreign_receipt_sound`'s restatement are T3b's second landing (`protocol!`), each a consumer of `authorityOf` — stated so that every Store today, under `Authority.none`, carries an authority cell that says "nobody", and a World with a quorum refuses nothing yet.

**Floor.** The kernel whose `genesisWorld` inserts `founderEntries` only: `genesisWorld_atGenesis` still holds but `authorityOf (genesisWorld …) = none` for every genesis, and a verifier handed any World learns nothing (`authorityOf_genesis`, the next landing's first theorem, refutes it). The deployed run: `host genesis` prints `authority THRESHOLD COUNT` from the World it wrote, and `rows` genesis under `Authority.none` lists three entries per one-founder World.

**What re-emits / what refuses to load.** `domOrigin` v3: every origin moves, every Store re-geneses, every invitation's `input` bytes carry the authority (PROTOCOL-77: `Start.genesis` gains it; an invitation under the old start codec decodes as no start). No persisted schema epoch moves (the World codec is unchanged: the cell is an ordinary live entry).

**KERNEL-69.1 (2026-10-26, RELAND-TRUST; cv 01a177f3-2293): the carrier is honest.** `Kernel/Proofs/AuthorityOf.lean`: `authorityOf_genesisWorld` — on every genesis World `authorityOf = some auth` whenever the two counts fit a `u64`, with no hash premise (the authority is written last, so a founder id that equals its content id is overwritten by it, not the reverse; every other live cell is a founder's member or grant); `authorityOf_genesis` under `GenesisFits`; `authorityOfCell_authorityCell` (the cell decodes as the authority it was made from: its slot keys 0, 1, 2 + i are distinct); `fold_genesis_authority` (every World a fold reaches still holds the cell, live and unchanged, at `authorityId`: `fold_rom`). This refutes the floor named above. Still not a theorem: `authorityOf w' = some auth` on every reached World, which needs "no turn births a `kindAuthority` cell" (every receiver births a fixed kind and none is 5: read in `Kernel/Receive/Derive.lean` and `Ledger.lean`, not proved); cv `01a179ea-85e3`.

**KERNEL-69.2 (2026-10-26, TRUST-SEED; cv 01a179ea-85e3): every World an honest fold reaches carries the genesis authority.** `Kernel/Proofs/AuthorityOf.lean`: `derive_born_not_authority` (no receiver bears a `kindAuthority` cell anywhere in a call's tree: `enroll` a member, `install` a package, `create` an object, `grant` a grant, `issue`/`account` an account, the rest nothing; one case per `Body` arm, `derive_all`) and `receive_born_not_authority`; `AuthorityOnly X auth w` (every live `kindAuthority` cell is `authorityCell auth` at `authorityId`, every nullifier slot holds `spent`), kept by `admit` of a Turn bearing no such cell (a write of the authority cell is refused: ROM) and by every recorded refusal, so by every honest log (`honest_authorityOnly`); `authorityOf_of_only` (a canonical World where that holds and the cell is live answers `auth`); and the consumers' form, `authorityOf_honest_fold`: from a checked genesis, along any `Honest` log (the writer's and every follower's World), `authorityOf w' = some auth`. `authorityOf_genesisWorld` is now its zero-step instance through `authorityOf_of_only` (statement unchanged; its trie walk is not repeated). Hypotheses added to landed theorems: 0.

**Floor.** A receiver that bears a `kindAuthority` cell (say `issue` writing kind 5): one honest Turn leaves two live cells of the kind, `authorityOf` answers `none`, and every certified-head consumer refuses a World it should accept. `derive_born_not_authority` fails on that arm by name. Not covered, named: a DISHONEST log (a Turn no receiver derives) may bear such a cell; `admit` does not refuse it, and the consumers that need the authority of a World they did not re-derive read it at genesis or adoption, where `atGenesis` and the invitation pin already authenticate it.
