# decisions/ledger.md — the LEDGER layer (value, transfer, wells, floors, credit, escrow)

LEDGER-1..5 were written in `decisions/kernel.md` while LEDGER built under KERNEL's prefix; they
were moved here verbatim on 2026-10-17 (D5 landed), so every LEDGER decision is in this file. Format per
`decisions/README.md`: decision · alternatives · why · CRITIQUE · META-CRITIQUE · status.

## LEDGER-1 · `sealTurn` takes a list of effects and the receiver's nullifiers (BUILD-LEDGER, 2026-10-16)
**Decision.** The brief's D2. `sealTurn X c creates (effects : List (D × Act)) (nullifiers : List D)`.
`actFor` takes the effect on the cell (`find?`), `keep` otherwise; `effectsPinned` refuses an
effect on an unpinned cell (`unpinned`, as before) and two effects on one cell (new Refusal
`duplicateEffect`). Every existing receiver passes `[]` or `[e]` (`writeOf` and `spendEnroll`'s
option as `.toList`) and `[]` nullifiers. Restated: `sealTurn_ok` (now also `t.nullifiers = ns`),
`touchesOf_pins`, `dispatch_sealed`, `receiveWith_sealed`, `sealTurn_creates`, `enroll_authorized`,
`grant_carves`. `sealTurn` now needs `Ord D` (`firstDup`), so eleven receiver theorems lost their
`omit [Ord D]`. CONTROL: `kernel-sim --seeds 64` admitted=2554 restarts=929 unchanged, every
Turn byte-identical (refused-as-expected 5474 → 5979 only from the new probe). Plant: the
duplicate check off ⇒ 63/64 seeds red ("probe: two effects on one cell sealed").
**Alternatives.** A transfer as two turns (not atomic: a debit without its credit is observable).
A transfer-specific seal (two seals, law 1). Effects as `D → Act` (duplicates unrepresentable, but
an effect on an unpinned cell is then silently dropped: a buggy receiver loses a write without a
name). Building the touches from the effects so a duplicate becomes the kernel's `duplicateTouch`
(one name for one fact, but the touches would no longer be the caller's pins in the caller's
order, which `receive_ok` states and `stale_named`'s precedence relies on).
**Critique.** KERNEL-11's "a receiver changes one cell" was structural; it is now a property of
each receiver again. `duplicateEffect` names a state no honest receiver produces, so the Sim meets
it with a direct `sealTurn` probe (`probeSeal`), not through a signed call: a test of the seal,
not of any receiver. The door KERNEL-20 closed (a list effect for per-link enrolment carving) is
open again.
**Meta-critique.** Shaped by transfer, which is the deliverable I was handed. The independent test:
PROTOCOL's `pay` row was already blocked on "no receiver puts a nullifier in a Turn", and LANG-13's
option (a) needs the same list, before any ledger existed.
Status: built.

## LEDGER-2 · Value is a kernel discipline: balance AND floor conserved per denomination (BUILD-LEDGER, 2026-10-16)
**Decision.** (ROOT accepted attacks A and C of LEDGER-0 over the brief's D1.)
(a) `Discipline.value`: a cell whose slots are RAM, three of which the kernel reads
(`Value.denomKey 8`, `balanceKey 9`, `floorKey 10`: the denomination's bytes, CODEC `i64`, CODEC
`u64`; a denomination is at most `Bounds.denomBytesMax` = 64 bytes, so comparing two is O(1)).
`Value.ofCell` decodes them; a value cell a write leaves behind that does not decode is refused
`valueMalformed`, one whose balance is below minus its floor `belowFloor`. Both are judged by
`postWrite`'s `.value` branch (the discipline's own rule, beside append-only's), on the post-cell
of `touchCheck`'s one lookup, so cells-touched stays 1.0; a touch's `Post` carries its value FLOWS
(the pre-cell's balance and floor negated, the post-cell's added).
(b) `checkValue` (after the touches, before the nullifiers) adds the born value cells' flows and
accumulates per denomination into an association list, refused `overBound denoms` past
`Bounds.denomsMax = 8` distinct denominations in one turn (O(touches), not a sort). Every
denomination's balance flow must be 0 (`notConserved d`), and its floor flow 0
(`floorNotConserved d`) unless `d` is the bytes of an id this turn bears: the denomination's birth
is the only turn that sets its total floor.
(c) No mint and no burn: a relabelled denomination, an account closed into another
(retire A(10) + credit B 10), a born cell with a balance: all are the same arithmetic.
Theorems (Kernel/Proofs/Value.lean): `admit_value` (∀ d, `w'.valueSum d = w.valueSum d`, an
EQUALITY in KERNEL-19's style, for ANY admitted turn), `fold_value`, `admit_floors` (the floor
sum of every denomination the turn does not bear is unchanged), `admit_floorOk` (every live value
cell stays within its floor), `outstanding_le_floors` (Σ positive balances ≤ Σ floors on a World
whose value sum is 0), and the cap: before its birth turn a denomination's floor sum is 0
(given digest bytes injective), so its total floor is fixed at birth forever and outstanding ≤ it.
**Alternatives.** Receiver-only conservation plus the audit (`rederive` compares a receiver with
itself, so a buggy receiver passes). A LANG `conserve` law (per-package, optional). Balance only,
with the cap as a receiver theorem (`dispatch_value_born` alone: a LANG posting or a buggy receiver
births a floored cell). A sort-and-group check (O(t log t) and a sortedness proof) or an O(t²) one.
The headroom encoding (store `balance + floor` as u64: `belowFloor` unrepresentable, but the
solvency rule moves into every receiver's arithmetic, and a floor change rewrites two slots).
**Critique.** The kernel TCB learns money: a signed number, a floor, a denomination, four Reject
names, one Bound, a consensus-critical sum. Kernel/Cell.lean's header ("what the bytes mean (a
balance …) is not the kernel's business") is amended, not ignored. Two conserved quantities now
have two mechanisms (the storage allowance a World field, value a discipline). The value check
reads three slots of every touched value cell: O(cell), bounded. Eight denominations per turn is a
policy, not a derivation (a DvP swap needs 2; a fee in a third asset 3). Floors conserved means a
credit line can only be carved from the well's unissued headroom; an issuer who wants to raise a
cap must issue a new denomination. Every follower sees every balance (no privacy: declared absent).
**Meta-critique.** Two scouts named the idea and nobody priced it; I may like it for novelty. The
independent test is the buggy-receiver argument plus LANG postings multiplying writers past what
per-receiver proofs can cover. Conserving the floors too is the move I find prettiest, which is a
reason to check it: it is what makes pug's three rules (debit to minus the floor; capped well;
outstanding ≤ Σ floors) one kernel invariant instead of three receiver promises, and it deletes
the need for a separate setFloor authority (LEDGER-3).
Built: the theorems above, all of `World.admit`, plus `admit_not_born` + `fold_floors_held`
(once the well's id is held, no log moves its floor sum: the cap is fixed forever) and the genesis
lemmas `cellsSum_noValue`, `floorOk_noValue`. Sim: an independent model of every balance, a
whole-World scan after every step (each issued denomination sums to 0, its floor sum is its cap,
outstanding ≤ cap, every account within its floor and equal to the model), forged-turn probes
meeting `notConserved`, `floorNotConserved`, `valueMalformed`, `overBound` (nine denominations).
A finding the Sim made: the old charge probe re-identifies the last turn; when that is an `issue`,
the copy bears its well under a new id that still names the OLD denomination, a second issuance,
and the kernel refuses it `floorNotConserved` before `chargeMismatch`. Plants (observed red,
reverted): the balance check dropped ⇒ `checkValue_ok` no longer builds, kernel-sim 63/64 red
"probe credit-only: forged turn admitted (expected notConserved)"; `withinFloor` constant true ⇒
`entry_outstanding`/`outstanding_le_floors` no longer build, 44/64 red "expected belowFloor, got
admitted".
Second-agent statement review (law 6): no vacuous statement or identity carrier. It found that
"the cap is fixed forever" was not yet a theorem and genesis was never discharged (both closed
above), and named two scope facts, stated here: conservation is not OWNERSHIP (a forged log
moving A's balance to B is conserved and folds; authority is the receivers', and the audit's
re-derivation is what refuses the forgery); and after birth any writer may move floor between
cells of one denomination with the sum unchanged (no receiver does: `transfer` writes only the
balance key; the credit-line receiver will, under the issuer's authority).
Status: built.

## LEDGER-3 · Three ledger receivers; the well's own id is the denomination (BUILD-LEDGER, 2026-10-16)
**Decision.** (ROOT accepted attack B.) The receivers live in Kernel/Receive/Ledger.lean, below
Derive (which dispatches them); the authority rule they share with `write` (`walk`,
`principalOf`, `ownerAuthority`, and `slotsOf`) moved out of Derive into Kernel/Receive/Authority.lean
so both can import it. `Body.issue (cap)`: bears ONE cell, the WELL: kind
`kindAccount 6` (5 stays unused since KERNEL-20), `.value`, owner the signer, denomination the bytes of its own id
(`cellIdOf txId 0`: tx-derived, so no cycle), balance 0, floor `cap` (`overflow` past 2^63, where
`-cap` stops being an i64). `Body.account (asset)` (not `open`: a Lean keyword): bears an account (owner the signer, the
asset's denomination, balance 0, floor 0) WITHOUT reading the well, so opening never pins the hot
cell.
`Body.transfer (src dst amount via once)`: both pinned live accounts (`wrongKind` / `malformedCell`
otherwise), `ownerAuthority … .mutate via` on `src` (grants work unchanged), `sameAccount`,
`zeroAmount`, `assetMismatch dst`, `overflow` when a post balance leaves i64; two effects (each
balance slot set), and `once.map (onceNullifier X src)`: `H(domOnce, bytes src ‖ key)`, so a
signer can only spend its own source's namespace. Minting is a transfer out of the well, burning
one into it. There is NO receiver solvency check: `belowFloor` is the one name. A credit line
(the second deliverable) is a floor transfer out of the well, judged by the kernel's floor sum.
The asset ROM cell of the brief (`kindAsset`) does not exist: it held the issuer, the well id and
the cap, all of which the well holds.
**Alternatives.** The brief's asset ROM + well (two cells per issue, a content id naming a tx id).
Open-on-first-credit (one receiver, two shapes). Opening through the well (pins the hot cell:
every open conflicts with every mint). One `Body.ledger` sub-tag (PROTOCOL-1 rejected sub-tags).
**Critique.** Call kinds 9 → 12 against a ceiling of 10 (SIZE-CEILING with this argument). Refusal
constructors +4. An account can be opened for a denomination nobody has issued (junk, paid for by
its storage charge, and inert: floor 0, nothing can reach it). A caller-chosen `once` key binds
only an honest signer: it is an idempotency key, not an observation proof. The well is a hot cell:
every mint and burn pins it, so concurrent minters conflict `stale`.
**Meta-critique.** Deleting the asset cell is the law-1 move I wanted; the test is that nothing
reads it: `open` does not, `transfer` reads only accounts, and the cap is the kernel's floor sum.
Built: `transfer_authorized`, `transfer_once`, `dispatch_value_born`, `transfer_exact`
(Kernel/Proofs/Ledger.lean; `admit_written`, a written touch read forward, beside it). Sim arms:
issue (and `overflow` past the cap bound), account, transfer honest / overdrawn (`belowFloor`) /
by a stranger (`noGrant`) / to itself / of nothing / across denominations / with a once key fresh
or already spent (`spent`). Plants (observed red, reverted): `issue` bears its well with floor
`capMax` instead of `cap` ⇒ `dispatch_value_born` no longer builds, 64/64 red "value scan: floor
sum 9223372036854775808 ≠ cap 650"; the once nullifier dropped ⇒ `transfer_once` no longer
builds, 9/64 red "expected spent, got admitted".
Status: built. Next: a credit line (a floor transfer out of the well, issuer authority), its own entry.

## LEDGER-4 · A credit line is a floor transfer out of the well, under the issuer's authority (BUILD-LEDGER, 2026-10-17)
**Decision.** pug's floors issue asked that an account may go down to minus a floor its issuer
extends. `Body.credit (well acct : D) (amount : Nat) (via : Option D)`: both pinned live accounts;
`ownerAuthority … well … .mutate via` (the issuer, or a grantee of `mutate` on the well through a
chain rooted at the issuer); the source must be a WELL, an account whose denomination is its own
id (`notWell` otherwise, new Refusal); `sameAccount`, `zeroAmount`, `assetMismatch acct`;
`overflow well` past the well's whole floor (a Nat floor cannot go negative), `overflow acct` past
`capMax`. Two effects: the well's floor falls by `amount`, the account's rises by it. The kernel
judges the rest: the denomination's floor sum is unchanged (LEDGER-2), and a credit line past the
well's UNISSUED headroom (floor + balance) leaves the well below its own floor, `belowFloor`. So a
credit line cannot raise what may be outstanding: `outstanding_le_cap` + `fold_floors_held` already
say so, for every turn, which is why this entry needs no cap theorem of its own.
Theorems (Kernel/Proofs/Ledger.lean): `credit_authorized` (source is a well, signer has its
owner's authority), `credit_exact` (exactly `amount` of floor moves well → account, balances and
denominations unchanged, every other cell untouched), both through a new `sealed_two_writes` that
`transfer_exact` now shares (`ofCell_setFloor`, `ofCell_floor_lt` beside it). Sim: the issuer
credits a holder (admitted within the headroom, `belowFloor` past it, `overflow` past the well's
floor), a non-issuer is `noGrant`, a credit out of a non-well `notWell`; the model tracks every
account's floor and the scan checks it. Plants (observed red, reverted): the account half of the
credit dropped ⇒ `credit_exact` no longer builds, kernel-sim 39/64 red "credit: expected ok, got
rejected floorNotConserved" (the KERNEL refuses the buggy receiver); the `notWell` check dropped ⇒
`dispatch_born` no longer builds, 21/64 red "expected notWell, got refused overflow".
A second agent read the statements (law 6): none vacuous; on its findings `credit_exact` now
states `0 < amount ≤` the well floor (the Nat `-` does not truncate) and `credit_authorized` names
the destination account and its denomination.
**Alternatives.** (a) A `setFloor acct f` that sets a floor directly (minidregg's; with conserved
floors it cannot balance, so it would need a kernel exception). (b) Floor transfers between ANY two
accounts of a denomination, under the source's owner (holders could re-lend credit; the issuer
loses control of who is extended credit). (c) Credit as a negative balance on the well with no
per-account floor (then an overdraft has no per-holder limit).
**Critique.** One direction only: there is no receiver to reclaim unused credit. Reclaiming it is
a power over a holder's account (shrinking what they may borrow), so whose authority it is (the
holder's, the issuer's, both) is a taste fork, left to Ember; until then a credit line is
irrevocable, and an issuer who over-extends can only wait for holders to repay. Call kinds 12 → 13
against the ceiling 12 raised last commit (raised again here, with this argument). The well stays
the hot cell: every credit pins it like every mint.
**Meta-critique.** The receiver is small because LEDGER-2 already did the work; that is the test of
LEDGER-2's choice to conserve floors (without it, this entry would need its own cap proof and a
kernel exception), but it is also the choice I already liked, so I am not the right judge of it.
Status: built.

## LEDGER-5 · Methods move value: a method's effects are `Body` calls, derived for the calling object (BUILD-LEDGER, 2026-10-17; PROPOSAL to KERNEL-5 and LANG-3, answering LANG-21 by name)
**Proposal.** LANG-21 decided effects as DATA, visited depth first, each object once, re-entry refused,
callee principal = the calling object, and named LEDGER's first method-triggered receiver as its build
trigger. This is that trigger, and it narrows one choice of LANG-21's: the effect type.
(a) *One call language.* `Program.run … : Except (Refusal D) (Slots × List (Body D))`. An effect IS a
`Body` (LANG-21's `Effect {target, method, args, budget, via}` is exactly `Body.invoke`), restricted to
the kinds an object may exercise: `invoke`, `transfer`, `account`, `credit`, `grant`; every other kind is
refused `notCallable kind` (new Refusal). LANG's `methodTy S A := fn S (fn A (fn reqTy (rec {state : S,
calls : list body})))`, with `body` the generated Body codec's LANG type.
(b) *Derived for the object.* Each effect is derived by its OWN receiver over the same pinned view, with
`Req.agent` = the signer and `principal` = the calling object, so `ownerAuthority` compares an account's
owner slot with the OBJECT's id: an object moves only value it owns, and grants may name an object as
grantee. No receiver changes its authority rule; only who the principal is.
(c) *One seal per call.* Receivers return a `Draft D := {creates : List Cell, effects : List (D × Act),
nullifiers : List D}` and `receive` seals once. A receiver that needs its own born id (`issue`) is given its
draft's create offset. The visited drafts concatenate; one cell written twice in a tree is
`duplicateEffect` (already a name), a nullifier twice the kernel's `duplicateNullifier`. Bounds:
LANG-21's `callDepthMax 4`, `callsMax 8`, one consensus tick budget for the tree.
(d) *Accounts for objects.* `account (asset : D) (owner : Option D)`: anyone may open an account for any
owner (an empty account with floor 0 is harmless: only its owner can debit it, and it costs the opener
its storage), so a depositor opens the escrow's account and funds it in one tree, or an object opens its
own by effect.
(e) *Escrow on top* (the next deliverable, a LANG package + a PROTOCOL row): state {phase, depositor,
beneficiary, amount, acct}; `deposit` (the depositor's transfer into `acct` happens in the same tree),
`release` → `[transfer acct beneficiary amount]`, `refund` → `[transfer acct depositor amount]`, each
guarded by `phase = held` and moving to an absorbing phase. "Never paid twice" is then the kernel's
(acct's floor is 0: a second payout is `belowFloor`), and "never both released and refunded" is the
package's lifecycle theorem (L4's `Spec`/`Run`), on a PROGRAMMED object so D6's law-removal hole does
not apply.
**Theorems owed.** `visit_distinct` (each object once, LANG-21); `invoke_authorized` restated per visited
object; `effect_principal` (every effect's derivation has principal = its caller); `transfer_authorized`
already covers object-owned accounts unchanged; `admit_value` needs nothing (it is about every turn).
**Alternatives.** (1) LANG-21's own `Effect` record beside `Body` (two call shapes, law 1). (2) Postings
`{src, dst, amount}` as a third effect type (D5 of the brief): value only, so `account` and `grant` by an
object would each need another. (3) Value inside object state with a `conserve` law (rejected in LEDGER-2).
(4) `invokeAll` batches (rejected in LANG-21).
**Critique.** The Draft refactor touches every receiver and every `sealTurn`-shaped theorem (sealTurn_ok,
dispatch_sealed, dispatch_born, dispatch_value_born, enroll_authorized, grant_carves): a big diff in
KERNEL-5's files while KERNEL-24/25/26 and the World port queue behind it. Object-as-principal is the
confused-deputy LANG-21 names: a callee sees the calling object, not the signer, so a package that
forwards caller-supplied calls lends its own authority (the package's methods must not take raw `Body`
arguments, a LANG check). `account` for any owner lets anyone litter an owner's id with empty accounts
(bounded by storage charge). The client must pin the whole tree before signing.
**Meta-critique.** I picked `Body` as the effect type because LEDGER's receivers are Body arms and I own
them: the move most convenient to me. The independent test is law 1 (an `Effect` record would duplicate
`Body.invoke` field for field) and that the brief's posting type would have needed two more siblings.
**LANG-3's answer (2026-10-17, to be LANG-22):** (1) accepted, the effect type is `Body D`, restricted
as above, replacing LANG-21's `Effect`. (2) Amended: the core has no list or recursive type (LANG-1/3),
so `calls` is a FIXED-ARITY row `rec {c0 : opt, …, c7 : opt}`, `opt = sum {none, some : callTy}`
(`callsMax = 8` slots, label order, `none` skipped); `callTy` is GENERATED from KERNEL's Body codec
shape (one arm per allowed constructor), with a theorem that its data decodes to exactly the allowed
Bodies; `methodTy S A := fn S (fn A (fn reqTy (rec {calls : callsTy, state : S})))`; `Program.run`
still returns `Slots × List (Body D)`. (3) Amended: install refuses a method whose argument type
contains `callTy` or an arm of it (`forwardsCalls`). That check is PARTIAL by design: a method may
still assemble a call from caller-supplied fields (a target and an amount), which is ordinary
parameterisation. The confused-deputy guard is therefore (b) itself: the callee's principal is the
CALLING OBJECT and only its own authority is spent; the LANG check is a second line, never the guard.
Build order: KERNEL-5's Body codec + `Program.run` signature + Draft; then LANG's `callTy`, `methodTy`,
calls from `runMeasured`, `visit_distinct`; then LEDGER's escrow.
Status: LANG accepted with amendments; KERNEL-5's answer on (b)(c)(d) pending.

## LEDGER-5 · CLOSED against KERNEL-28 and LANG-23: what was accepted, what amended, what each side owes (LEDGER-2, 2026-10-17)
**Accepted as proposed.** (a) An effect is a `Body D` of a callable kind (`invoke`, `transfer`,
`account`, `credit`, `grant`); `Program.run : Pinned D → (pkg : D) → Slots → (method : Nat) →
ByteArray → Req D → (budget : Nat) → Except (Refusal D) (Slots × List (Body D))`;
`Refusal.notCallable kind` is the kernel's own assertion where the program's calls enter. (b)
Every receiver takes the ACTOR: the signer at top level, the calling object for an effect;
`Req.agent` = the signer, `principal` = the object. (c) `Draft D := {creates, effects,
nullifiers}`, sealed once by `receive`; a cell written twice in one tree is `duplicateEffect`, a
nullifier twice `duplicateNullifier`, re-entry into a visited object refused; `Bounds.callsMax 8`,
`callDepthMax 4`, `treeTicksMax` (one budget: the top-level invoke's signed `budget`, capped).
**Amended by KERNEL-28.** (d) `account (asset) (owner : Option D)` with a born id is replaced by a
KEYED id, `accountId X owner asset = H(domAccount, owner ‖ asset)`: anyone may open the account
of any (owner, asset), a second open is `idTaken`, and `Turn.creates : List (D × Cell)` carries
explicit ids (one birth shape). This is better than what I proposed: my critique "anyone may
litter an owner with empty accounts" is gone (one per pair), and the escrow's account binding is a
theorem rather than a convention (LANG-23 gap (ii)). Objects are not members, so KERNEL-26's public
disjunct never holds for an object: an object acts only through what it owns and grants naming it.
**Amended by LANG-23.** `calls` is the fixed-arity row `rec {c0 … c7 : optTy callTy}`, `callTy`
hand-stated with round-trip theorems against `Body` (not generated). **Withdrawn**: LANG-3's
`forwardsCalls` install refusal (ROOT ruling: withdrawn, not deferred). LEDGER-5's critique
sentence "the package's methods must not take raw `Body` arguments, a LANG check" and LANG-3's
"the LANG check is a second line" are both superseded: there is no LANG check. The confused-deputy
guard is `invoke_authorized` (KERNEL-25, owner-gated invoke, built) together with `effect_as_signed`
(D5, below): an effect spends exactly the authority the calling object would have as a signer of
the same `Body`, and no more.
**Owed, by whom.**
- LEDGER-2 builds D5 as `kernel:` (`--cross-layer`), rebased on KERNEL-24, every theorem statement
  reviewed by KERNEL-5 before landing: Draft; the actor argument in every receiver; the tree
  visitor in Derive; the Bounds; `accountId` and explicit create ids (Turn codec); `checkGrantee`
  admitting a live programmed object as grantee (KERNEL-28 (b) requires it: today it admits only a
  member or the World); the `Program.run` shape. Theorems: `effect_as_signed` (KERNEL-28's
  statement: an effect derived for `obj` is exactly the derivation of the same `Body` with `obj` as
  actor), `visit_distinct`, `draft_cells_distinct` (no cell twice in a sealed tree),
  `account_keyed` (an admitted account's id is `accountId` of its owner and denomination), the
  Draft restatements of `sealTurn_ok`/`dispatch_sealed`/`dispatch_born`/`dispatch_value_born`,
  and the stub-program plant for `notCallable`. LEDGER-5's owed `effect_principal` is subsumed by
  `effect_as_signed` and is not built separately; `invoke_authorized` per visited object follows
  from the two and is not restated.
- KERNEL-5: reviews D5's statements; owns the amount-bounded right (cv task 01a14938); the World
  port converges forward with D5.
- LANG-4: `callTy`, `methodTy`, `Lang/Call.lean` and its proofs, `runMeasured`'s counts (which size
  `treeTicksMax`), as one `lang!` flag day after D5; plus LEDGER-6's two asks (`Req.self`,
  `accountOf`).
- PROTOCOL-5: the `pay`/`well` re-cut (LEDGER-6 (f)) and the escrow row.
**Critique.** Closing a proposal by listing what others owe is a ledger of promises; the only ones
that bind are those with an owner and an order, which is why each line names one. The `checkGrantee`
widening is a check changing shape: it must stay a check (a LIVE object of the program kind, never
any id), or an object grant could name a cell that is not an actor at all.
**Meta-critique.** The amendment I am praising removed a convention I proposed. Calling it better is
cheap after the fact; the measurable reason is that it deletes a refusal-free failure (a mis-bound
escrow account that wedges silently) rather than documenting it.
Status: CLOSED. D5 build order: KERNEL-27 → KERNEL-24 → D5 (LEDGER-2) → LANG's `lang!`.

## LEDGER-6 · The escrow: its account is `accountId self asset`, funded through a v0 mutate grant in the same tree; the payout's guard is the kernel's `once`, not the floor (LEDGER-2, 2026-10-17)
**A correction first.** LEDGER-5 (e), and the brief, say "never paid twice is the kernel's floor 0:
a second payout is `belowFloor`". That is FALSE. Anyone may transfer into the escrow's account
(a transfer needs authority over its SOURCE only). After `release` pays `amount`, a top-up of
`amount` by anyone makes a second `release` (or a `refund`) solvent, and the floor admits it. The
floor bounds what leaves to what is there; it says nothing about how often. The plant below is that
top-up.
**Decision.**
(a) *The account.* The escrow's funds sit in `accountId X e asset`, where `e` is the escrow object.
Only `e` can debit it (`transfer_authorized`: the owner is `e`, `e` is not a member, so only an
effect of `e`'s own methods carries `e` as actor, by `effect_as_signed`; and only `e`'s grants could
delegate it, and the package issues none). The account is opened by anyone, before the deposit,
with a top-level `account asset (owner := e)`; it cannot be born in the deposit's own tree, because
the transfer reads its destination through the PINNED view.
(b) *Naming itself.* A method must name `accountId X e asset`, and today it can do neither half: it
does not know `e` (`Req.principal` in an invoke is the object's owner, KERNEL-25; in an effect the
caller) and it cannot hash. Two asks to LANG-4/KERNEL-5, in D5's flag day:
`Req.self : D` (the object the act is judged or run on; KERNEL sets it in the one place it builds a
`Req`, and a data object's law gains it too), and a LANG builtin `accountOf : bytes → bytes →
bytes` whose meaning theorem is `= X.env.bytes (accountId X owner asset)`. Nothing else in the
package is hashed.
(c) *Funding (LANG-23 gap (i), KERNEL-28's v0).* The depositor grants `e` `mutate` on its own
account, then invokes `deposit g`. `deposit` is guarded by `phase = open` and `agent = depositor`,
moves to `held`, and emits one call: `transfer (src := accountOf depositor asset) (dst :=
accountOf self asset) amount (via := some g) (once := some self)`. The transfer is in the same tree
as the phase change, so `held` is reached exactly when the funds moved (a refused transfer refuses
the whole call); there is no unfunded `held`. The once key `self` namespaces the depositor's source
per escrow, so a second deposit through the same grant is `spent` even under a package bug.
The grant is the WHOLE balance (v0, labelled in the package); the amount-bounded right is KERNEL's
(cv task 01a14938), and the depositor should revoke `g` after the deposit.
(d) *Payout.* `release` (agent ∈ {depositor, arbiter}) emits `transfer (accountOf self asset)
(accountOf beneficiary asset) amount none (once := some "payout")`; `refund` (agent ∈ {beneficiary,
arbiter}) emits the same with `dst := accountOf depositor asset`. Both from `held`, both to an
absorbing phase (`released`, `refunded`). Because both spend ONE nullifier,
`onceNullifier (accountId e asset) "payout"`, the kernel itself makes the escrow pay at most once
in its life, whichever way: never paid twice AND never both released and refunded, by
`transfer_once`, whatever the package's phase code says. The package's lifecycle theorem
(`escrow_absorbing`: from `released` or `refunded` every method refuses, by name `settled`; and
`escrow_one_payout`: along any run, at most one call emits a payout) is the package's own
statement, which refuses by NAME before the kernel would refuse `spent`.
(e) *Who may invoke.* KERNEL-25: the escrow's owner (its creator, say the arbiter) grants
`invoke deposit` to the depositor and `invoke release`/`invoke refund` to the parties; the
package's `agent` checks are the refinement. A public escrow is a World grant (KERNEL-26).
(f) *The `pay` and `well` rows.* `well` (K-WELL) is no longer a package: it is the ledger
receivers on the wire. Proposed lines for PROTOCOL-5: the referee `issue 100` (bind `@w`), a member
`account @w`, the referee `transfer @w ACCT 10`, a second `transfer @w ACCT 1000` refused
`belowFloor` (past the cap), and `credit @w ACCT 5`; plant: `.skipJudge` at the over-cap line. That
needs four verbs (`issue`, `account`, `transfer`, `credit`) in `Protocol.Command.Verb`, PROTOCOL's.
`pay` (JPAY) needs `spent`, which `transfer … --once KEY` now reaches: a second transfer with the
same key is `spent`; its `world/pay/Book` package is not needed for that row.
**Alternatives.** (1) Owner-addressed transfer fields (`transfer asset from to`), so nobody hashes:
breaks minting, because a well's id is the denomination, not `accountId issuer asset`. (2) `acct` as
a deposit argument: a depositor names its own account, the escrow cannot check it, and the escrow
wedges silently (LANG-23 (ii)). (3) Fund by a separate top-level transfer, then `deposit`: `held`
without funds, and a method cannot read the balance. (4) The floor as the double-pay guard: refuted
above. (5) Separate once keys for release and refund: never-paid-twice by the kernel, but
never-both only by the package.
**Critique.** `Req.self` and `accountOf` are two additions to other layers' surfaces for one
package; each must earn its place on its own (`self` does for any law that names its object;
`accountOf` is the one hash a package needs). The mutate grant lends the whole balance to package
code: the bound on what moves is the package's text, inspectable but not the kernel's. The shared
once key makes the payout's uniqueness depend on the package choosing one key for both arms, a
choice the lifecycle theorem proves it made; a package that chose two keys would still be
never-paid-twice by the kernel. The arbiter is trusted to pick; that is the escrow's meaning, not a
defect.
**Meta-critique.** The correction is the part I would most like to be wrong about, because it
contradicts my predecessor's text and ROOT's brief at once; it stands on a two-line counterexample,
which the sim plant reproduces. The `once` move makes my own layer's existing theorem carry the
package's hardest property: convenient for me, and checked by the plant that removes the phase
guard and still finds the second payout refused `spent`.
**Plants.** (1) Top-up: release, transfer `amount` into the account, release again: refused (`spent`
by the kernel, `settled` by the package); with the shared key replaced by two keys AND the phase
guard removed, the second payout is ADMITTED, so the sim goes red. (2) Unfunded deposit (no grant):
the whole call is refused (`noGrant`), the phase stays `open`.
Status: decided; (b) asked of LANG-4 and KERNEL-5 for D5's flag day; the package after `lang!`
(b) amended by LEDGER-7: no `accountOf`; accounts are `AcctRef` in Body.

## LEDGER-7 · Accounts are named by reference in `Body`: `AcctRef = well asset | of owner asset`; no LANG builtin (LEDGER-2, 2026-10-17; amends LEDGER-6 (b), LANG-4's counter-proposal, to be LANG-25)
**Decision.** LEDGER-6 (b)'s `accountOf` builtin is withdrawn. LANG-4 refused it: the term machine is
parametric in the digest, so the builtin would thread KERNEL's hash into Eval/BigStep and every meaning
proof; `decide +kernel` teeth on `runLaw` die under a real hash (the reduction bomb); and accountId would
be computed in two places. Accepted instead, with one narrowing: `transfer`'s `src`/`dst` and
`credit`'s `acct` take `AcctRef D := | well (asset : D) | of (owner asset : D)`, resolved by the
receiver: `.well a ↦ a` (the well's id IS the denomination; the cell must be a well, else `notWell`),
`.of o a ↦ accountId X o a`. Theorems `resolve_well`, `resolve_of`. LANG-4 proposed `.id (a : D)` for the
first arm; I take `.well` so every value cell has exactly ONE name in a Body (an ordinary account
cannot be named by its raw id), law 1 at the reference. Minting is `transfer (.well w) (.of o w)`,
burning the reverse. `credit (well) (.of o w)` keeps its well as a plain `D`. `Req.self` stays (LANG-4
accepted): the escrow writes `.of self asset`, `.of depositor asset`, `.of beneficiary asset` and hashes
nothing. LANG's `callTy` carries `acctRefTy = sum {of : rec {asset, owner : bytes}, well : bytes}`.
Clients address accounts the same way at top level (one Body shape). The receiver pins the RESOLVED id;
the client computes it to pin, as it computes born ids. Built in D5 (kernel half, KERNEL-5 reviews);
LANG's half in `lang!`; PROTOCOL's verbs take `of:OWNER:ASSET` / `well:ASSET` (PROTOCOL-5's spelling).
**Alternatives.** (1) The `accountOf` builtin (refused above). (2) LANG-4's `.id` arm: two names for
one cell. (3) Owner-only fields: breaks minting (LEDGER-6).
**Critique.** `.well` makes `transfer` read the source's kind to resolve it, one more refusal path
(`notWell`) on a hot receiver. A client must hash to pin, so a pin mismatch from a wrong client-side
`accountId` is `stale`/unpinned, not a named "wrong account": the name is the kernel's pin refusal.
**Meta-critique.** The counter-proposal came from the layer that would otherwise carry the cost, so I
checked it against the reason I rejected owner-addressing (minting) rather than against its author's
cost: the sum keeps minting, and removes the only hash a package needed.
Status: agreed with LANG-4; KERNEL-5 to review in D5's statements.

## LEDGER-8 · D5's three landings, and D5c's concrete shape: a Draft per receiver, an `At` (actor, born base), one tick pool returned by the run (LEDGER-2, 2026-10-17; builds KERNEL-28 + LEDGER-5/7, reviewed by KERNEL-6; asks LANG-5 one change)
**Order.** D5a (explicit create ids, `notContentId`: 5b87949). D5b (keyed `accountId`, `account
asset owner`, `AcctRef` in transfer/credit): written and green, HELD until KERNEL-6's World port
lands (ROOT's order D5a → port → D5b/D5c), then rebased. D5c last, as below.
**D5c decision.**
(a) *Draft.* `structure Draft D := {creates : List (D × Cell), effects : List (D × Act),
nullifiers : List D}`. Every receiver returns `Except (Refusal D) (Draft D)`; `receiveWith` seals
the tree's concatenated Draft ONCE (`sealTurn` keeps its checks: every effect pinned,
`duplicateEffect` for a cell written twice anywhere in the tree). A nullifier spent twice in one
tree is World.admit's `duplicateNullifier` (already a name, already checked); receive adds no
second check of it.
(b) *`At`.* `structure At D := {actor : D, base : Nat}`, passed to every receiver. `actor` is whose
authority it spends: `ownerAuthority`, `principalOf`, `walk`, `checkParent` and every
"`u.member`" in a receiver read `at.actor`; `Req.agent` stays `u.member` (the signer). `base` is
the number of fresh births before this receiver in the tree; `bornAt X c base cells` numbers
them from it, so two `grant` effects in one tree get distinct `bornId`s. Top level: `⟨u.member, 0⟩`.
(c) *Req.self.* `Req` gains `self : D`, the object judged or run on (create: the born id;
write/law: obj; invoke: obj). Set only where Derive builds a Req (`reqOf`).
(d) *The visitor.* In `invoke`, after the object's own run and judgement, each returned call is
derived depth-first by `deriveCall X look c ⟨obj, base'⟩ (depth + 1) visited body`, which (i)
refuses `notCallable kind` unless the body is `invoke`/`transfer`/`account`/`credit`/`grant`,
(ii) refuses `callTooDeep` past `Bounds.callDepthMax = 4`, (iii) refuses `revisited obj` for an
invoke of an object already on the path or already invoked in the tree (`visited`), and then
calls THE SAME receiver the top level calls (`dispatch` restricted to the callable arms) with the
object as actor. `tooManyCalls` past `Bounds.callsMax = 8` per run. No other path derives an
effect, which is what `effect_as_signed` states.
(e) *One tick pool.* The tree's budget is the top-level invoke's signed `budget`, refused
`overTicks` above `Bounds.treeTicksMax`. ASK to LANG-5: `Program.run` returns the ticks it used,
`Slots × List (Body D) × Nat`. LANG's `runMeasured` already counts them. The kernel asserts
`used ≤ budget` (law 4, `overTicks`), and each nested invoke runs with
`min(its declared budget, what the pool has left)`. Without the count, the kernel could only bound
the tree by the sum of declared budgets, at most `(callDepthMax + 1) ·` the signed one: a bound,
but not "one budget". `treeTicksMax` is pinned from runMeasured's counts on the BAR rows,
measured in the D5c commit, never guessed.
(f) *checkGrantee* admits a member, the World, or a LIVE cell of `kindObject` (KERNEL-6 accepted);
anything else is refused by its read's name, as now.
**Theorems (statements go to KERNEL-6 before landing).** `effect_as_signed`: every effect's
Draft in a derived tree is `dispatch` of its Body at `⟨obj, base⟩`, where obj is the invoking
object (the visitor has no other branch). Plant: derive the calls at `⟨u.member, base⟩` (the
invoker): kernel-sim's arm, where an object pays out of an account the object owns and the
invoker does not, goes red. `visit_distinct`: the invoked objects of a derived tree are pairwise
distinct (plant: drop the visited check, and an arm re-entering is admitted). `draft_cells_distinct`:
a sealed tree writes no cell twice (from `effectsPinned`). `transfer_authorized` restated at
`at.actor`. `invoke_authorized` per visited object follows from `effect_as_signed` and is not
restated. Draft restatements of `sealTurn_ok`, `dispatch_sealed`, `dispatch_born`,
`dispatch_value_born`. `notCallable` is unreachable for `Lang.program` (LANG's
`callsOf_callable`); its tooth is kernel-sim's stub program returning a `create`.
**Flag day (D5c).** `Program.run`'s shape (LANG's `lang!` day follows: `callTy`, `methodTy`,
`reqTy (self bytes)`, the tick count). The Turn and call codecs do not change in D5c. Every
package with a method re-ids in LANG's day, not mine. In D5c, Lang's glue returns no calls and its
ticks.
**Alternatives.** Receivers that keep returning a Turn and a merge of Turns: two seals and a
merge rule, where one seal is one rule. A per-tree id counter held in mutable state: there is
none in Lean, and `base` is that counter made explicit. Charging nested runs their declared
budgets (no tick count): rejected in (e).
**Critique.** `At` widens every receiver and every receiver theorem by one argument, as KERNEL-28
priced. The tick count is a premise from LANG: a lying `run` could report fewer ticks than it
used. The assertion only checks `used ≤ budget`, which bounds what the kernel grants; it cannot
check what LANG did with it. Pinned reads make a tree in which two calls touch one account
refuse `duplicateEffect`, even where a human would net them: a package must emit one transfer
per account pair.
**Meta-critique.** (e) adds an ask to LANG in its own flag day, to make a property true that
KERNEL-28 stated and nothing yet enforced. The test that this is not scope creep: without it,
"one budget" in KERNEL-28 is a sentence with no check behind it.
Status: decided by LEDGER-2. KERNEL-6 to review; LANG-5 asked (e).
