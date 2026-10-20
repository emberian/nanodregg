> record copy of redregg/work/nanodregg-scout/ASSEMBLY-ledger.md, 2026-10-16; the lane logs stay in redregg

# ASSEMBLY — ledger (Opus evaluator, 2026-10-16, nanodregg main d1f483e)

Scouts: L1 (per-account ledger as receivers), L2 (wells, caps, floors), L3 (pay as one LANG package),
L4 (escrow as data object + laws). Marks: **[read]** I read the code at the cited place; **[ran]** I
executed it and saw the output; **[assumed]** neither. Line numbers are main `d1f483e` unless marked
"stale" (the primary checkout's working tree, which is what the scouts read).

## 0. Ground truth first: the scouts built against a three-hour-stale tree

- [ran] `git -C ~/dev/nanodregg diff HEAD --stat`: the primary checkout's working tree is far behind main
  (41 Kernel/Lang files differ, 6814 lines). Its `.lake/build/lib/lean/Kernel/*.olean` are dated 18:41–19:38.
  The charter now says the primary checkout is "nobody's editing surface" and layers edit in
  `~/dev/nanodregg-wt/<layer>`; the scout harness pointed every scout at the primary checkout anyway.
  Every scout read and compiled against that tree; every quoted line number is of that tree.
- [read] What that changes at main:
  1. **KERNEL-11**: `Leg`, `pins`, `legs`, `retires` are deleted; a Turn is `touches : List (Touch D)`,
     `Touch := {cell, seen, act}`, `Act := keep | write ops | retire` (Kernel/Turn.lean:26-48). `sealTurn`
     takes ONE `effect : Option (D × Act)` (Kernel/Receive/Call.lean:287). Every scout's two-leg
     `sealTurn X c [] [l1, l2] []` and every `commit_live`/`commit_live_two` over `[(a,ca),(b,cb)]` is against
     a shape that no longer exists. A transfer (two cells change) is **not expressible** on main today.
  2. **KERNEL-10**: `Req` carries the signed window `notBefore`/`validUntil` (Call.lean:161-170) and LANG's
     `reqTy` does too (Lang/Package.lean:28). L3's interface 4 and L4's interface 2 are already landed;
     L4's `early_refund_exploit`/`late_release_exploit` are theorems about a superseded `Req`.
  3. **KERNEL-20**: `kindFollow` (5) and `Body.follow` are deleted; `Body.enroll` gained `via`. Kinds on
     main are 1–4 (Call.lean:198-201).
  4. **KERNEL-19**: storage is conserved (`admit_conserves`, Kernel/Proofs/Weight.lean). L1 looked for
     "KERNEL-19" and reported it absent; it is on main.
  5. Lemmas the scouts re-proved exist: `slots_get_set_eq`/`slots_get_set_ne` (Kernel/Proofs/Rooted.lean:23,37),
     `touchCheck_live` (:153), `admit_live` (:185), `readKind_ok` (:496), `admit_frame` (Frame.lean:66),
     `admit_nullifiers`/`fold_nullifiers` (Frame.lean:176,187). `countBytes`/`countOf` (Call.lean:254-256)
     is the u64 slot codec that L1 (`natBytes/natOf`) and L2 (`natBytes/natOf`) each re-wrote.
  6. `Kernel/Sim.lean` is now `Kernel/Sim/Gen.lean`, generic in its parameters, with a toy and a
     **deployed** instance (74556c1).
- [ran] I re-ran each scout's cheap claims against the same stale build they used (copies in my scratchpad,
  nothing written into the scout dirs): L1 `LedgerProofs` 0 errors (12 linter warnings); `LedgerSim --seeds 8`
  637 admitted, 0 failing; `--plant --seeds 8` 8/8 red with the quoted "sum of balances 6091 <> supply 6090 …
  audit refused at 76: mismatch". L2 `Ledger.lean` green (I appended a false theorem to a copy to confirm it
  really elaborates: it failed by name), `Demo` prints exactly the quoted lines, axioms as quoted. L3
  `PayMain honest` 52 rows 0 red, `nonce` 5 red, `notheft` 0 red. L4 `EJourney` GREEN.
- [assumed] None of the four compiles against main as written (all use `Leg`/two-leg `sealTurn`, or the
  old `Req`); I did not try, because the shapes are visibly gone (read).

**So: every scout result is true of the 19:38 kernel and is evidence about ideas, not code to lift.**

## 1. The system this area should be

**Value is a kernel discipline; authority is receivers'; policy is packages.**

1. KERNEL: a fourth cell `Discipline`, `.value`. A value cell carries a denomination (fixed at birth), a
   balance (signed) and a floor at kernel-reserved slots. `World.admit` refuses a turn after which, for some
   denomination, the sum of balances over the turn's touched and born value cells differs from before
   (`notConserved`), a value cell is below minus its floor (`belowFloor`), or a value cell's denomination
   changed or its numbers do not decode (`valueMalformed`). One check, O(touches), computed from
   `touchCheck`'s one lookup. Theorems of `World.admit` itself: per-denomination sum invariant over the whole
   World, floor invariant, outstanding ≤ sum of floors. This is KERNEL-19's shape (storage conserved by the
   kernel) for a second quantity.
2. RECEIVERS: `issue cap` (a ROM asset plus its WELL, a value cell whose floor is the cap), `open asset`,
   `transfer src dst amount via once`. No mint, no burn (L2): minting is a transfer out of the well, burning
   a transfer into it, so value is zero-sum from genesis forever. Authority is `ownerAuthority` on `src`
   (grants work unchanged). The receive half of the cap theorem: only `issue` births a value cell with a
   nonzero floor, and that floor is the signed cap (the KERNEL-21 pattern: `admit_rooted` + `dispatch_born`).
3. PACKAGES (v1): pay policy (tariff, routes, fees, holds), escrow and bounty are programmed objects whose
   methods post value out of value cells **the object owns**; the kernel's discipline holds whatever the
   package does, so no package needs its own conservation proof.

Rejected: money as a LANG package (`Protocol/Rows.lean` pay/well/bounty as written): a law sees one object's
`old → new`, cannot see a cross-object sum, and is optional (L3's `noguard` plant: one missing law turns 29
rows red) [ran]. Rejected as the primary mechanism: receiver-only conservation (L1/L2 as built): `rederive`
re-runs the same receiver and compares against its own output (Kernel/Receive/Audit.lean on main is
`rederive` then `admit`) [read], so a BUGGY receiver passes the audit; only a forged log fails it. L1 calls
its plant "the shape of a buggy receiver"; it is a forged log (the debit leg is dropped after derivation,
LedgerSim.lean `--plant` branch) [read], which is why the audit caught it. A real receiver bug would have
been invisible to both the audit and `fold`.

## 2. Per scout

### L1 — per-account ledger as receivers (verdict: idea; I agree)

KEEP
- [read][ran] The cell shape: an asset cell plus one account cell per (owner, asset), the balance in its own
  slot, the owner in `slotOwner` so `ownerAuthority` (Derive.lean:88) and grant chains work with zero change.
  A transfer observes {member, src, dst} and writes {src, dst} (3 touches, 2 writes; L1 measured 522 B on
  the stale shape). This is the correct answer to minidregg's monolithic Book plus the `accountCut` patch
  (L1's reading of Theory/CanonicalResourceKernel.lean and Compiler/CanonicalAccountView.lean; [assumed]: I
  did not re-read minidregg).
- [read] The statement shape of `transfer_conserves` (LedgerProofs.lean:268-279): the post-state is read back
  from `w'.live` after the real `World.admit`, plus a frame clause for every other id. Restate it on touches
  with main's `admit_live`/`touchCheck_live`; under D1 it becomes the receiver-level corollary of
  `admit_value`, still worth having because it states the exact amounts.
- [ran] The sim method: an independent model of every balance, a whole-World scan after every admitted turn
  (sim-only O(store)), a plant that must go red twice. Fold it into `Kernel/Sim/Gen.lean` as ledger arms (one
  sim, law 1), so it runs under the toy and the deployed parameters.
- [read] The finding that `World.admit` admits a credit-only Turn on main as well (no value check in `check`,
  World.lean:292-301).

DISCARD
- `LOp` inside `Body.invoke` and `LRefusal` wrapping `Refusal` (Ledger.lean:50-60, 145-192): a second shape of
  the call body and of the refusal type (laws 1, 7); the scout says so itself.
- `mint`/`burn` and the asset's `supply` slot (Ledger.lean:96-141): two posting forms plus a supply cell that a
  kernel zero-sum check would have to special-case. L2's well (one posting form) is strictly smaller.
- `natBytes`/`natOf`: twin of `countBytes`/`countOf` (Call.lean:254-256) (law 1).
- `get_set_self`/`get_set_ne`/`readKind_ok`/`postLeg_ok`/`commit_live` (LedgerProofs.lean:26-233): twins of
  main's Rooted.lean lemmas, or about the deleted `Leg`.
- The open "kind-7 cells are born only by `open_`" invariant: unnecessary under D1. A cell's discipline is
  fixed at birth by the kernel (postWrite never changes it, World.lean:232-244 [read]), and conservation
  counts born cells, so no birth path can smuggle value.

NEEDS REWORK: interface 5 (the helper lemmas) is already done on main; interface 1 becomes D3.

### L2 — wells, caps and floors (verdict: assemble; I say the design assembles, the code does not)

KEEP
- [read][ran] The single-predicate design: there is no mint and no burn, the well is an ordinary account whose
  floor is the issuance cap, `canDebit a n := -floor ≤ balance − n` is the only solvency rule, and
  `isIssuerMint` is gone. Demo [ran]: under cap 1000, 400 and then 600 are admitted, the well reaches −1000,
  and a further 1 is refused. This is the design D1 makes a kernel law.
- [read] `issue`'s one-Turn birth (Ledger.lean:292-307): the well's id is `cellIdOf tx 0`, the ROM asset names
  that id and is content-addressed, the well names `romIdOf asset`, so there is no cycle. Because the asset
  names a txId-derived well id, two issues with equal parameters still get distinct asset ids (no `idTaken`
  collision) [read: `bornId`, World.lean]. Keep it without the commons cell (the commons exists only for sweep).
- [read] The list arithmetic `outstanding_sub_debts`, `debts_le_floors`, `outstanding_le_sum_floors`,
  `outstanding_le_cap` (Ledger.lean:824-879) as the arithmetic core of the WORLD-level theorem D1 owes. The
  scout says correctly that its headline name flatters it: as written it is about a list.
- [read] The `ofCell_*` slot lemma pattern (decode after a single slot set).

DISCARD
- `balBytes`/`balOf` (biased u64, Ledger.lean:49-66): a local signed codec beside CODEC's family (law 3).
  CODEC supplies `i64` (D4).
- `LRefusal` and the `invoke (1000+op)` smuggling in Demo.lean (laws 1, 7).
- The receiver's `canDebit`/`overFloor` and `canSetFloor`/`floorUnderwater` checks: under D1 the kernel's
  `belowFloor` is the one solvency refusal, the way `stale` is the one staleness refusal (charter KERNEL row).
  If the receiver checked too, the same fact would have two names.
- `sweep`, `commons`, the per-asset period and rate (Ledger.lean:335-370): this gives the issuer a bounded
  power to seize from ANY holder, which pug did not ask for (pug asked for commons recycling). That is a
  taste fork and it weakens holders' guarantees (CLAUDE.md pause items 2 and 4), so it is Ember's call. Do not
  build it.
- `T1.lean`, `CodecProofsStream.lean` (a copy of a CODEC proof module), the `Leg`-based `transfer_world` and
  `commit_live_two`.
- Defs and proofs in one file (law 8).

NEEDS REWORK
- `FloorInv` as a receiver property moves into the kernel. That is D1, and L2's own TAKE asked for it.
- `setFloor` is the second deliverable, not the first. Its authority model is "the asset issuer extends
  credit", which equals issuance (minidregg FLOORS-LOG 13:30: "setFloor's verb = mintAsset … extending credit
  = issuing") [read], and it deserves its own decision entry.

### L3 — pay as one installed package (verdict: idea; I agree)

KEEP
- [read] The split: exactly-once observation and cross-object atomicity are kernel concerns; tariff, book
  assignment, credit rate, fee and route arithmetic, holds and the clock rule are package laws and methods.
- [read][ran] Nullifiers derived inside `receive`, namespaced by the cell whose authority the call exercises:
  `H(dom, obj ‖ key)` (PayRun.lean:46). A package can then spend only its own namespace. The `nonce` plant
  [ran: 5 red, replayed observation credited twice] shows why. The key must be PACKAGE-derived from the
  arguments (`once_<method> : Args → bytes`) when callers are untrusted: a caller-chosen key binds only an
  honest caller. That is D5. For the built-in `transfer` a caller key is an idempotency key (D3).
- [ran] Methods need a result Verdict (the `noguard` plant: 29 refusals commit their `err` code). LANG owns
  this (D5).
- [read] `PayDsl.lean` (HOAS levels, sorted rows, `letB`) as a seed for LANG's authoring tool. LANG owns it.
- [ran] The plant set `nonce`/`bug`/`noguard` as row plants for PROTOCOL's pay row.

DISCARD
- The flat n-row `Book` state (`selN`/`setN`): O(n) per access, capped at 8 rows by `valueBytesMax`
  (Bounds.lean:28) [read] (law 4). Note that the package-size numbers are from the stale LANG wire, before
  LANG-17 moved the tree to varint framing [read].
- The `conserve` law as the conservation mechanism: it is per-package and optional. Under D1 the kernel does
  it once for every writer. Laws keep pay's *policy* (tariff and route), not its arithmetic invariant.
- The watcher-reported `tip`/`clock` as time: `Req` carries the window on main.

NEEDS REWORK: the `receiveOnce` shim (a re-priced Turn built after `receive`) becomes `Program.run`'s
`once` output (D5), and the nullifiers go through `sealTurn` (D2).

### L4 — escrow as a data object plus laws (verdict: assemble; I say needs-rework, and it has a hole)

FINDING [ran]: **the escrow is not safe against its own depositor.** The escrow is a data object owned by the
depositor A. `law` (Derive.lean:182 on main, the same code on the stale tree) judges a law change as
`judge … (stateOf cell) (stateOf cell)`, the identity transition [read], and `lifecycle` accepts the identity.
So A may replace the escrow's laws with none and then write anything. I added this to a scratch copy of
EJourney, after E3:
```
ok   ATTACK A strips the escrow laws: admitted
ok   ATTACK A refunds early AND zeroes the frozen amount: admitted, phase = (some 2)
```
`never_released_and_refunded` quantifies over `Run`, which is built from `Step`, which is "both laws accept"
(Escrow.lean:164-170). The kernel permits transitions outside `Run`, so the theorem's model is narrower than
the kernel (an empty-premise class, not a false proof). This is a general KERNEL/LANG fact, not escrow's
alone: any non-deny-all law on a data object can be removed by its owner (D6).

KEEP
- [read] The lifecycle shape: an absorbing phase (held, released, refunded), frozen fields, `Spec` as a
  plain proposition, `Run` as the quantifier, and the paired plants (skipJudge and the mutant law) that flip
  the same row [ran]. It must live on a PROGRAMMED object (methods release and refund; `write`/`law`
  refuse `hasMethods`, Derive.lean:167-196 [read]), not on a data object.
- [read] `Frag`/`Apply`/`Law` adequacy as an idea: a first-order law's verdict is exactly its denotation.
  Restate it against LANG-18's reference semantics. `run_bigStep` (Lang/Proofs/Agree.lean:282) and
  `bigStep_run` (Lang/Proofs/Complete.lean:205) already tie the machine to `BigStep` [read], so the escrow
  side needs only `FE.den ⇒ BigStep`, a far smaller proof than re-deriving the machine trace. LANG owns it.

DISCARD
- `hi`/`lo` writer-claimed window fields and the two exploit theorems: main's `Req` carries the attested
  window. Delete the fields; do not keep the exploits as negative examples (they describe a `Req` that is gone).
- `NullOnce.lean`: a twin of main's `admit_nullifiers`/`fold_nullifiers` (Frame.lean:176,187).
- "Money" as a status field. Under D1 and D5 the escrow OWNS a value cell with floor 0, release and refund
  are postings out of it, and "never paid twice" is `admit_floor` plus zero-sum: the kernel refuses a second
  payout because the cell cannot go below 0. The phase theorem remains the lifecycle property, not the money
  property.

## 3. Interface decisions (the layer that owns each, as real signatures; both critiques each)

### D1 · KERNEL · `Discipline.value` and the conservation check in `World.admit`
```lean
-- Kernel/Cell.lean:17
inductive Discipline | rom | appendOnly | ram
  /-- a conserved quantity: denomination (fixed at birth), balance, floor at the kernel's value keys;
  every other slot is RAM -/
  | value
-- Kernel/Value.lean (new, def-module)
def Value.denomKey : Nat      -- three keys disjoint from every receive layout (Call.lean: 0–3, 16, 17,
def Value.balanceKey : Nat    -- 1024–1280, 4096+); suggest 8, 9, 10
def Value.floorKey : Nat
structure Value where denom : ByteArray; balance : Int; floor : Nat
def Value.ofCell (c : Cell) : Option Value          -- CODEC i64 for balance, u64 for floor, canonical
-- Kernel/World.lean:248
structure Post (D : Type) where
  cell : D; entry : Entry; freed : Nat
  flow : Option (ByteArray × Int)                    -- value cell: (denom, post balance − pre balance)
-- Kernel/World.lean:41, three constructors with Reject.name arms
  | valueMalformed (cell : D) | belowFloor (cell : D) | notConserved (denom : ByteArray)
def checkValue (posts : List (Post D)) (born : List Cell) : Except (Reject D) Unit
-- in `check`, after the touches (the posts) and before checkNullifiers/checkCharge
-- Kernel/Proofs/Value.lean (spec measure, O(store), never run on the request path)
def World.valueSum (w : World D) (d : ByteArray) : Int
def FloorOk (w : World D) : Prop                     -- every live .value cell: -floor ≤ balance
theorem admit_value : World.admit E w t = .ok w' → ∀ d, w'.valueSum d = w.valueSum d
theorem fold_value : (∀ d, w.valueSum d = 0) → World.fold E w l = .ok w' → ∀ d, w'.valueSum d = 0
theorem admit_floor : World.admit E w t = .ok w' → FloorOk w → FloorOk w'
theorem outstanding_le_floors : FloorOk w → w.valueSum d = 0 → w.positive d ≤ w.floors d
```
Rules: a write to a value cell may not touch `denomKey` (`valueMalformed`). A retire counts as flow
−balance. A born value cell counts as +balance. The post balance must decode. These rules alone close
relabelling (a cell moved from denomination X to Y) and closing an account into another
(retire A(10) + credit B 10 is conserved).
**Alternatives.** (a) Receiver-only conservation plus audit (L1/L2 as built). (b) Money as a LANG package with
a `conserve` law (L3). (c) A headroom encoding: store `balance + floor` as u64 so the floor invariant is
unrepresentable rather than checked (see D4).
**Why.** It covers every writer once: today's receivers, tomorrow's package postings, a forged log, and a
buggy receiver that the audit cannot see (§1). `fold` alone then enforces it: HOST's reopen and any
folder get value soundness without re-deriving. (PROTOCOL-14 option A re-derives anyway; option B folds
nothing, so this helps it no more than any other kernel check [read].) It is the KERNEL-19/KERNEL-21
pattern, which has already paid twice.
**CRITIQUE.** The kernel TCB learns a signed number, a floor and a denomination: money semantics, which the
Cell.lean header says the kernel does not do ("what the bytes mean (a balance …) is not the kernel's
business") [read]. That sentence must be amended, not ignored. There would be two conserved quantities with
two mechanisms (the storage allowance as a World field, value as a discipline). Per-denomination grouping
is O(t log t) by sort, or O(t²) by list (t ≤ touchesMax = 512); pick sort and pin a waste row. The sum
covers only touched and born cells, so the World-level theorem leans on `admit_frame` for the untouched
rest (true, Frame.lean:66). Three new `Reject` constructors.
**META-CRITIQUE.** Two scouts named this idea and neither priced it (L1 META, L2 TAKE), and an evaluator likes
to add the thing nobody built: I may be adopting it for novelty. The independent test is the buggy-receiver
argument (rederive compares a receiver with itself), plus the fact that LANG postings would multiply writers
past what per-receiver proofs can cover. The bigger attractor I am NOT deciding: the storage allowance could
itself be a denomination (member-held storage budgets, KERNEL-16's open fork). Ember or ROOT should see that.

### D2 · KERNEL · `sealTurn` takes a list of effects and the nullifiers
```lean
-- Kernel/Receive/Call.lean:287 (was: (effect : Option (D × Act)), nullifiers := [])
def sealTurn [DecidableEq D] (X : Ctx D) (c : Call D) (creates : List Cell)
    (effects : List (D × Act)) (nullifiers : List D) : Except (Refusal D) (Turn D)
def actFor [DecidableEq D] (effects : List (D × Act)) (cell : D) : Act   -- Call.lean:269
-- each effect on a pinned cell (`unpinned`), at most one per cell:
  | duplicateEffect (cell : D)                                            -- Refusal
```
Every existing receiver passes `[]`/`[e]` and `[]`. `sealTurn_ok`, `dispatch_sealed`, `dispatch_born`,
`grant_carves`, `receive_ok` and `enroll_authorized` restate.
**Alternatives.** A transfer as two turns (not atomic: a debit without its credit is observable). A
transfer-specific `sealTransfer` (a second seal, law 1). Effects as a map type, so a duplicate cannot be
written at all (no refusal needed, but a heavier type in every receiver).
**Why.** Two cells change in one transfer. `pay` is blockedOn exactly "no receiver puts a nullifier in a
Turn" (Protocol/Rows.lean on main) [read]. LANG-13 option (a) needs the same list.
**CRITIQUE.** KERNEL-11's "a receiver changes one cell" was structural, and this makes it a property again.
KERNEL-20 explicitly rejected a list effect for per-link enrolment carving (8 writes per turn); enrolment
stays single-effect, but the door is open. `duplicateEffect` names a state no honest receiver produces.
**META-CRITIQUE.** Shaped by transfer. The independent test is that the nullifier half was already owed by
PROTOCOL's pay row and by LANG-13, before any ledger existed.

### D3 · KERNEL (Receive) · three ledger kinds
```lean
-- Kernel/Receive/Call.lean:37 Body
  | issue (cap : Nat)                    -- births asset (kindAsset, ROM) + its well (.value, floor = cap)
  | open (asset : D)                     -- births an account (.value, owner = signer, balance 0, floor 0)
  | transfer (src dst : D) (amount : Nat) (via : Option D) (once : Option ByteArray)
-- second deliverable: | floor (acct : D) (floor : Nat) (via : Option D)   (asset issuer only)
def kindAsset : Nat := 6     -- slotOwner = issuer, then well id, cap (5 is free since KERNEL-20; skip it)
def kindAccount : Nat := 7   -- slotOwner = owner; the kernel's value keys
def domOnce : String := "nanodregg/kernel/once/v1"
def onceNullifier (X : Ctx D) (src : D) (key : ByteArray) : D := X.env.hash domOnce (X.env.bytes src ++ key)
-- Refusal (Call.lean:81): sameAccount | zeroAmount | assetMismatch (cell : D) | overflow (cell : D)
-- Kernel/Proofs/Ledger.lean
theorem transfer_authorized   -- twin of write_authorized (Authority.lean:71): src's owner is the chain's principal
theorem dispatch_value_born   -- only `issue` births a .value cell with floor > 0, and that floor = cap
theorem transfer_exact        -- L1's transfer_conserves on touches: post balances read from w'.live, frame
theorem deployed_outstanding_le_cap   -- on an audited World (RootedDeployed's premises)
```
A receiver reads an account only if its kind is `kindAccount` AND its discipline is `.value` (L2's `ofCell`
pattern) [read]. There is no `insufficient`/`overFloor` in the receiver: `belowFloor` (D1) is the name.
`overflow` stays because it is the receiver's encoding precondition: it must encode the post balance
in i64.
**Alternatives.** One `Body.ledger (op : LedgerOp D)` sub-tag (PROTOCOL-1 rejected sub-tags as "the same table
with worse names"). Open-on-first-credit instead of `open` (one receiver with two shapes). L1's
mint/burn/supply. Money as packages only.
**Why.** These are the three authority rules value needs: who may create a denomination and its cap, who
may hold, and who may debit.
**CRITIQUE.** Call kinds go 9 → 12 against a ceiling of 10 (SIZE.md on main), which needs `SIZE-CEILING:` with
this argument. Refusal constructors go +5 (with `duplicateEffect`), and Reject +3. A caller-chosen `once` key
binds only an honest signer (a hostile watcher picks fresh keys), so it is an idempotency key, not an
observation proof; that needs D5's package-derived keys. Mints all pin the well, so the well is a hot cell and
concurrent mints conflict `stale` (one watcher is sequential, which is fine; many minters are not).
**META-CRITIQUE.** I trimmed `floor`, `sweep` and `commons` as forks or later. That can be "a phase ordering
chosen to avoid a hard part" (law 10's own example). `floor` is pug's actual feature. The test is whether the
well row needs it: it does not (the cap is fixed at issue), so it goes second, not "later".

### D4 · CODEC · a signed fixed-width primitive
```lean
-- Codec/Stream.lean (beside u64 at :116)
def i64 : Stream Int64          -- 8 bytes LE two's complement; i64_lawful in Codec/Proofs/Stream.lean
-- plus the Body codec arms for issue/open/transfer and the new Reject/Refusal names in the generated table
```
**Alternatives.** The headroom encoding (store `balance + floor` and `floor` as u64; `belowFloor` becomes
unrepresentable; no CODEC change). L2's biased u64 (rejected, law 3).
**Why.** The slot then means what it says (the balance), and a floor change is one slot write.
**CRITIQUE.** It is a new primitive for one consumer, and CODEC carries the proof. Headroom makes the invariant
structural, which law 4's spirit prefers; the cost is that every reader subtracts. **META-CRITIQUE.**
"Means what it says" may be taste; I picked the encoding minidregg did not have.

### D5 · LANG + KERNEL (v1, second builder) · methods return a verdict, postings and once keys
```lean
-- Lang/Package.lean:37 (today: .fn S (.fn A (.fn reqTy S)))
def methodTy (S A : Ty) : Ty := .fn S (.fn A (.fn reqTy (outcomeTy S)))
  -- outcomeTy S = sum {ok : record {state : S, posts : list posting, once : list bytes}, refused : bytes}
-- Kernel/Receive/Call.lean:172 Program.run
structure Posting (D : Type) where src : D; dst : D; amount : Nat
structure Outcome (D : Type) where state : Slots; posts : List (Posting D); once : List ByteArray
run : Pinned D → (pkg : D) → (state : Slots) → (method : Nat) → (args : ByteArray) → Req D →
  (budget : Nat) → Except (Refusal D) (Outcome D)
```
The `invoke` arm: each posting's `src` is a pinned `.value` account whose owner slot is the OBJECT's id (else
`noGrant src`). The postings become effects. The nullifiers are `once.map (onceNullifier X obj ·)`. D1 judges
the sum.
**Alternatives.** LANG-13 (a), general synchronous cross-object calls. Value inside object state (L3's flat
Book).
**Why.** This is the narrowest cross-object power that unblocks pay, bounty and escrow: an object moves only
value it owns. A refused method cannot commit (L3 `noguard`).
**CRITIQUE.** Object ids become principals for value cells (`ownerAuthority` compares owner bytes with member
ids, so a human is refused on an object-owned cell, which is right, but the rule is new). LANG-13's general
fork stays open. A package-derived `once` key still trusts the package author's choice of key (L3 CRITIQUE 5).
**META-CRITIQUE.** It is chosen because it makes the rows pass, which is building to the rows.

### D6 · KERNEL + LANG (finding, routed, not the ledger's to fix) · a law change is judged as the identity
`law` calls `judge … (stateOf cell) (stateOf cell)` (Derive.lean:182-196), so every law that accepts the
identity transition permits its own removal. KERNEL-6's "a law change is judged by the old laws" therefore
binds only deny-all [ran: the attack in §2 L4]. Ledger consequence, adopted now: every object that holds an
obligation (escrow, a pay book, a bounty) is a PROGRAMMED object. A real fix (judge sees `old laws → new laws`,
or `law` is refused on objects whose laws say so) is KERNEL/LANG's.
**CRITIQUE.** Requiring programmed objects means a resident cannot build an escrow from a data object plus
laws, which is L4's whole simple shape. **META-CRITIQUE.** I found this by attacking the one scout that
claimed "any signers"; there may be more such gaps in the other data-object rows.

### D7 · PROTOCOL · re-cut the money rows
`well`: `issue 1000` → `open` → referee holds a `mutate` grant on the well from the issuer and
`transfer @well @newcomer 10 --via G` → non-grantee refused `noGrant` → over cap refused `belowFloor` → burn
= `transfer @acct @well` → auditor sees the sum 0 for the denomination. Plant: "the kernel's conservation
check is skipped" ⇒ the forged credit-only turn is folded (expected `notConserved`). `pay`: the
nullifier half runs on `transfer --once`; the tariff half stays blockedOn D5. `bounty`: blockedOn D5 plus D6.
**CRITIQUE.** The rows' expected names change (`lawDenied` → `belowFloor`); the rows are the spec, restated
under law 11's carve-out, and the names are nanodregg's. **META-CRITIQUE.** I am editing another layer's spec
from the ledger's needs; PROTOCOL must re-derive each name, not copy mine.

### D8 · KERNEL · one sum over cells
Generalise `cellsWeight` (World.lean:161) and its `cellsWeight_insert/overwrite/fresh` lemmas
(Weight.lean:76-101) into one sum `cellsSum (f : Entry → Int)`, with `World.weight` and `World.valueSum d`
as its two instances (law 1).
**CRITIQUE.** `weight` is a Nat and value is an Int, so the generalisation either casts or duplicates; it
also churns KERNEL-19's proofs. **META-CRITIQUE.** Generalising before a second instance exists would be
speculative. This deliverable IS the second instance.

## 4. Charter rows

| row | owner | owns | must never | first deliverable |
|---|---|---|---|---|
| LEDGER: a KERNEL deliverable run as its own lane (not a seventh layer) | BUILD-LEDGER (Opus), worktree `~/dev/nanodregg-wt/ledger`, subject prefix `kernel:` | new: `Kernel/Value.lean`, `Kernel/Proofs/Value.lean`, `Kernel/Receive/Ledger.lean`, `Kernel/Proofs/Ledger.lean`, the ledger arms of `Kernel/Sim/Gen.lean`; by agreement with KERNEL (SendMessage before each): `Kernel/Cell.lean` Discipline, `Kernel/World.lean` Post/check/Reject, `Kernel/Receive/Call.lean` Body/Refusal/sealTurn, `Kernel/Receive/Derive.lean` dispatch; entries `LEDGER-n` in `decisions/kernel.md` | hold a balance, floor or supply anywhere but a `.value` cell; add mint, burn or a second posting form; claim conservation from a receiver theorem alone; keep any scout transport (`LOp`, `LRefusal`, `invoke 1000+op`, biased u64); build sweep, decay or commons before Ember rules | D2 + D1 + D3 (`issue`/`open`/`transfer`) with `admit_value`, `fold_value`, `admit_floor`, `outstanding_le_floors`, `dispatch_value_born`, `transfer_authorized`, the ledger sim arms (toy and deployed) and three plants |
| ROOT action (precondition) | ROOT | add `ledger` to `scripts/worktree`'s layer list; the OWNERS row stays `Kernel/ → KERNEL` (the lane commits as `kernel:`); tell KERNEL that LEDGER edits four of its files | — | — |
| CODEC deliverable | BUILD-CODEC | `Stream.i64` + `i64_lawful`; Body codec arms for the three kinds; the new names in the generated table | a second signed encoding | `i64` with its Lawful theorem |
| LANG deliverable (v1) | BUILD-LANG | D5's `methodTy`/`outcomeTy`; L4's adequacy restated as `FE.den ⇒ BigStep`; the authoring layer seeded from L3's PayDsl | value in object state slots; a `conserve` law as the money mechanism | method Verdict, with L3's `noguard` plant turning from "29 commit" to "29 refused by name" |
| PROTOCOL deliverable | BUILD-PROTOCOL | D7's `well` row re-cut; the `pay` nullifier half; `bounty` blockedOn D5/D6 | expected names copied from this file without resolving them against the constructors | `well` row runnable against D3 |

## 5. Risks (what gets worse)

1. **The kernel TCB grows by money** (D1): a signed number, a floor, a denomination and three Reject names in
   `World.admit`, which every follower runs. A bug there is a consensus bug.
2. **Privacy is unchanged and now more visible**: every follower sees every balance (PROTOCOL-3 ruled
   followers see the whole log for v0). minidregg's `accountCut` was a privacy patch; per-account cells do
   not fix privacy, they only stop the O(book) re-encode. State it as a declared absence in the LEDGER entry.
3. **The well is a hot cell**: every mint and burn pins it. With many minters, conflicts arrive as `stale`. A
   multi-destination transfer (one turn, well → N, allowed by D2) is the later fix.
4. **SIZE ceilings**: call kinds 9 → 12 against ceiling 10; refusal constructors +5 and Reject +3. The
   SIZE.md row says refusals "may only fall without a row that needs the new one" [read], so a row or plant
   must reach every new name. (`gates/refusals.py` is the forbidden-constructs gate, not this one [read].)
5. **Range**: i64 balances with u64 floors ≤ 2^63. An issuer can set a cap near the bound, and amounts above
   `Bounds` must be refused by name (`overflow`, a `Bound` row generated for Rust).
6. **D6 is open in the kernel**: until KERNEL/LANG fix the identity-judged law change, any data-object law
   (not only escrow) is revocable by its owner. Rows that rely on data-object laws as guarantees are weaker
   than they read.
7. **Scout staleness is systemic**: all four ledger scouts (and probably other areas) read the primary
   checkout three hours behind main. Any assembly that lifts scout code verbatim builds a mirror of a dead
   shape. Builders must restate on main.
8. **The `once` key semantics** (D3/D5): caller keys are idempotency only, package keys trust the author's
   choice of key; no theorem pins "one observation, one key".
9. **sweep/decay** (pug's commons recycling) is deferred to Ember; the floors issue is half-answered until
   then.

## 6. FIRST BUILDER BRIEF — BUILD-LEDGER (Opus)

You are BUILD-LEDGER for nanodregg, a KERNEL deliverable run as its own lane. You hold value in the kernel:
a `.value` cell discipline that `World.admit` conserves, plus three receivers (`issue`, `open`,
`transfer`). Read `/Users/ember/dev/redregg/work/nanodregg-scout/ASSEMBLY-ledger.md` end to end first (this
file); §0 explains why you must not copy scout code.

**Repo and worktree.** Repo `~/dev/nanodregg`, main only. EDIT ONLY in `~/dev/nanodregg-wt/ledger` (ROOT
creates it with `scripts/worktree ledger` after adding `ledger` to its layer list; until then ask ROOT, and do
not edit in `~/dev/nanodregg`, whose working tree is stale). Refresh with `git checkout -q --detach main`.
Commit ONLY with `scripts/commit -F MSG PATHS…` from the worktree, subject prefix `kernel:`, plus
`--cross-layer REASON` for any non-Kernel path. Pass WHOLE files: rebase a shared file such as
`gates/waste.tsv` on `git show main:<file>` first. Add `SIZE:` lines for every risen metric and
`SIZE-CEILING: call kinds: …` for 9 → 12. Before editing `Kernel/Cell.lean`, `Kernel/World.lean`,
`Kernel/Receive/Call.lean` or `Kernel/Receive/Derive.lean`, SendMessage the KERNEL owner what you will
change; they own those files. Decisions go in `decisions/kernel.md` as `LEDGER-1…`, each with both
critiques.

**Ground truth (main d1f483e; read these files, not prose):**
- `Kernel/Cell.lean:17` `inductive Discipline | rom | appendOnly | ram`
- `Kernel/Turn.lean:26-48` `Act := keep | write ops | retire`, `Touch {cell, seen, act}`,
  `Turn {txId, notBefore, validUntil, touches, creates, nullifiers, charge, event}`
- `Kernel/World.lean:232` `postWrite`, `:248` `structure Post {cell, entry, freed}`, `:258` `touchCheck` (ONE
  lookup per touch; keep it one), `:292` `check` (bounds → journal → shape → window → touches → nullifiers →
  charge → creates), `:314` `commit`, `:323` `World.admit`, `:161` `cellsWeight`
- `Kernel/Receive/Call.lean:37` `Body` (9 kinds), `:81` `Refusal`, `:161` `Req {agent, principal, notBefore,
  validUntil}`, `:172` `Program`, `:254` `countBytes/countOf`, `:269` `actFor`, `:279` `effectPinned`,
  `:287` `sealTurn … (effect : Option (D × Act))` with `nullifiers := []`
- `Kernel/Receive/Derive.lean:88` `ownerAuthority`, `:167` `write`, `:265` `dispatch`
- Proof kit: `Kernel/Proofs/Rooted.lean` `slots_get_set_eq/ne` (:23,:37), `touchCheck_live` (:153),
  `admit_live` (:185), `admit_rooted` (:241), `dispatch_born` (:315), `readKind_ok` (:496);
  `Kernel/Proofs/Weight.lean` `cellsWeight_insert/overwrite/fresh` (:76-101), `admit_world_weight` (:342);
  `Kernel/Proofs/Frame.lean` `admit_frame` (:66), `admit_nullifiers`/`fold_nullifiers` (:176,:187);
  `Kernel/Proofs/Authority.lean` `write_authorized` (:71)
- Sim: `Kernel/Sim/Gen.lean` (generic; toy instance `Kernel.Sim`, deployed `Kernel.Sim.Deployed`)
- Decisions to read first: `decisions/kernel.md` KERNEL-11, -12, -19, -20, -21 (the kernel-half +
  receive-half pattern you are repeating); `~/dev/redregg/work/FLOORS-LOG.md` (minidregg's floors lane:
  setFloor = issuance, deregistration with a floor).

**Work, in order (each a small commit that builds its import closure):**
0. SendMessage CODEC: you need `Codec.Stream.i64` + `i64_lawful` (D4) and the Body codec arms later. While it
   is in flight, do 1 (it needs no codec).
1. D2: `sealTurn … (effects : List (D × Act)) (nullifiers : List D)`, `actFor` over the list,
   `duplicateEffect`. Every existing receiver passes `[]`/`[e]`, `[]`. Restate `sealTurn_ok`,
   `dispatch_sealed`, `dispatch_born`, `grant_carves`, `receive_ok`, `enroll_authorized`. CONTROL:
   `lake exe kernel-sim --seeds 64` prints the same admitted/refused counts as before (state them).
2. D1: `Discipline.value`, `Kernel/Value.lean`, `Post.flow` computed inside `touchCheck` (no second lookup:
   the waste row cells-touched stays 1.0), `checkValue` in `check`, the three `Reject` constructors and
   `Reject.name` arms. Amend the Cell.lean header sentence that says balances are not the kernel's business.
   Proofs in `Kernel/Proofs/Value.lean`: `admit_value`, `fold_value`, `admit_floor`, `outstanding_le_floors`
   (restate L2's list lemmas, `Ledger.lean:824-879`, at World level). Prefer D8 (one `cellsSum`) over a
   second copy of the cellsWeight lemmas; if you do it, tell KERNEL first, because it churns KERNEL-19.
3. D3: `issue`, `open`, `transfer` in `Kernel/Receive/Ledger.lean` and their `dispatch` arms; `kindAsset 6`,
   `kindAccount 7`; `onceNullifier`; refusals `sameAccount zeroAmount assetMismatch overflow`. NO receiver
   solvency check: `belowFloor` is the one name. Proofs in `Kernel/Proofs/Ledger.lean`:
   `transfer_authorized`, `transfer_exact` (L1's `transfer_conserves` statement on touches),
   `dispatch_value_born`, and `deployed_outstanding_le_cap` (with RootedDeployed's premises).
4. Sim arms in `Kernel/Sim/Gen.lean` (one sim, both instances): an independent model of every balance; after
   every admitted turn, a whole-World scan checks the per-denomination sum = 0 and every floor; honest
   transfers, overdraw (`belowFloor`), stranger spend (`noGrant`), self (`sameAccount`), stale pin, mint
   from the well to the cap, then one more (`belowFloor`), a replayed `once` (`spent`), an exact replay
   (`replayed`). The kernel-sim coverage gate must meet every new name in ≥ 16 seeds.
5. Plants (record each in its commit message, observed red, then reverted): (a) `checkValue` skipped ⇒ a
   forged credit-only turn is FOLDED, the sim goes red naming `notConserved`, and `admit_value` no longer
   builds; (b) the floor comparison off ⇒ overdraw admitted (expected `belowFloor`); (c) `issue` ignores
   `cap` ⇒ `dispatch_value_born` no longer builds and the over-cap mint is admitted; (d) `once` not hashed ⇒
   `spent` never met.
6. SendMessage PROTOCOL with D7 (the `well` row re-cut, the pay nullifier half). Do not edit `Protocol/`.
   Write `LEDGER-1…` entries. Second deliverable after landing: `Body.floor` (credit lines; issuer authority,
   its own decision entry).

**Lift (restate on main; never copy a file, law 11):** L2 `Ledger.lean:292-307` (issue's ROM asset + well,
without commons), `:824-879` (outstanding/debts/floors arithmetic), the `ofCell_*` lemma pattern; L1
`LedgerProofs.lean:268-279` (the statement of `transfer_conserves`: post-state from `w'.live`, frame for every
other id); L1 `LedgerSim.lean` (independent model + scan + plant, as Gen arms); L3 `PayRun.lean:46` (the
nullifier namespace `H(dom, cell ‖ key)`, idea only).
**Ignore:** L1 `Ledger.lean` (`LOp`, `LRefusal`, mint/burn/supply, `natBytes`) and its `get_set_*`/`commit_live`
(main has them, or they are about `Leg`); L2 `balBytes`, `LRefusal`, `Demo.lean`'s `invoke 1000+op`, sweep,
commons, `setFloor` (second deliverable, re-derive), `T1.lean`, `CodecProofsStream.lean`; L3 `PayBook.lean`'s
flat state and its `conserve` law; L4 entirely for this deliverable (`NullOnce` is main's `admit_nullifiers`;
the escrow waits for D5/D6).

**Forbidden and gates.** No `sorry`, no `#guard` (named theorems; census `gates/census.py`); def/proof split
by file (law 8); no `partial`. Every theorem statement is read by a second agent before it lands (law 6:
check for identity carriers and empty premises. `admit_value` must quantify over ANY admitted turn, not over
receiver-derived ones). Build the narrowest thing that could refute you: `lake build Kernel.Proofs.Value
Kernel.Proofs.Ledger` and `lake exe kernel-sim --seeds 64`. Never run an unfiltered test suite. After you
change `sealTurn`/`Post`/`Reject` (shared shapes), build the WHOLE tree once (`lake build`), because
downstream consumers (Host, Protocol, Lang) break silently otherwise. Mac only; hbox is Ember's: do not use it.
Disk pressure is Ember's: stop writing, report `df` and a ranked `du`, delete nothing.

## Stopping processes: PID file or nothing (incident 2026-10-10)

A subagent ran `pkill -f "cat" -u ember` to clear its own stuck `cat`. `-f` matches the whole
command line, every app lives under `/Appli**cat**ions`, and 44 of my apps and agents got SIGTERM.
- **Never kill by pattern.** No `pkill -f <anything>`, no `pkill -x <bare word>`, no `killall`, no `kill -u`.
- **A process you started is stopped by the PID in its PID file**, and only that. Every detached job
  writes one (`nohup ... & echo $! > job.pid`). No PID file, no kill: tell me instead.
- If you must look first, `pgrep -fl` and read the list; it is never the argument to a kill.
- Every subagent brief you write quotes this block verbatim.

**Report to ROOT on events only:** D2 landed (with the counts-unchanged control); first red→green plant; D1
theorems landed; the well row's kinds runnable; any KERNEL disagreement on the shared files; handoff (write
`~/dev/redregg/work/LEDGER-LOG.md` before 350K tokens, in KERNEL-LOG's shape).
