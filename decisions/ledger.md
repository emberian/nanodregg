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
(f) corrected by PROTOCOL-6 (PROTOCOL-32, 4669195): my `.skipJudge` plants did nothing, because
belowFloor and spent are kernel admission and follow's own admit meets them before anything is
signed. The rows' plants are now `accountByAsset` (caught as idTaken) and a hostile-client `forge`
(caught as the writer's spent under `writerForgetsSpent`). Rows well and pay PASS.
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

## LEDGER-9 · LEDGER owns `Ledger/` and `world/escrow/`, and commits under `ledger:` (ROOT ruling, recorded by LEDGER-2, 2026-10-17)
**Decision.** (1) A new prefix `Ledger/` is LEDGER's. `Ledger/Escrow.lean` holds the escrow
package as data and its generator; `Ledger/Proofs/Escrow.lean` holds `escrow_absorbing`,
`escrow_one_payout` and the lifecycle theorems; a `lean_lib Ledger` entry is added in the commit that
adds the first module (lakefile is SHARED). (2) `ledger:` is a subject prefix mapping to LEDGER
(gates/owners.py, GATES-2's file). From then on LEDGER commits ALL of its paths under it, including
its enumerated Kernel/ files (Kernel/Value.lean, Kernel/Proofs/Value.lean, Kernel/Receive/Ledger.lean,
Kernel/Proofs/Ledger.lean, decisions/ledger.md). `kernel:` stops covering LEDGER, so a LEDGER commit
can no longer touch the rest of Kernel/ without `--cross-layer`. (3) The SHIPPED package text does
not go under Ledger/: every shipped package text lives under `world/` (as world/grain/Lifecycle
does), and gates/OWNERS gains `world/escrow/	LEDGER`. Longest prefix wins, so one place holds every
shipped text and each text has narrow ownership. HOSTING-3 was informed.
**Alternatives.** The package under Lang/Std with proofs under Lang/Proofs, cross-layer with LANG's
review: the text would be LANG's to change while its theorems are LEDGER's. Keeping `kernel:` for
LEDGER: the subject would authorise every Kernel/ path for a layer that owns four of them.
**Critique.** A per-layer prefix is a third place where ownership can drift. LEDGER's paths are now
spread over Ledger/, enumerated Kernel/ files and world/escrow/. A reader asking "what is LEDGER's"
must read OWNERS, not the tree.
**Meta-critique.** What makes that safe is OWNERS' longest-prefix rule, checked on every commit by
gates/owners.py: drift between the three places is a red gate naming the path, not a convention.
I accepted the placement change because one place for shipped texts is the property a deployment
reader needs, and narrow rows keep it from costing ownership.
Status: ruled by ROOT 2026-10-17; owners.py and the OWNERS rows landed by GATES-2 in cb99f02.


## LEDGER-10 · The escrow package as built: Ledger/Escrow.lean, its law's theorems over all data, ledger-sim with three plants (LEDGER-3, 2026-10-18; builds LEDGER-6 on LANG-33)
**Decision.** The package is Lean data, `Ledger.Escrow.escrow = Std.pkgOf stateTy [("escrow", law)]
methods`; its shipped text `world/escrow/Escrow` is `Lang.Print.package escrow`, byte-compared and
read back by `ledger-sim` E0 and proved to read back (`escrow_text_reads`, LANG-29's
`readPackage_checked`). State `{amount, arbiter, asset, beneficiary, depositor, phase}`, phase over
`held | open | refunded | released`. Methods in `pkgOf`'s sorted order: **0 deposit, 1 refund,
2 release** (LEDGER-2's hand-off had release 1 / refund 2; the label sort decides, and
`escrow_indices` pins it). Each method has ONE call slot of `callOf ["transfer"]` and runs
unconditionally (deposit: `of depositor → of self`, via the argument grant, once `self`; refund /
release: `of self → of depositor / of beneficiary`, no via, once `"payout"`); the LAW decides:
(a) birth and adoption: the OLD and the new phase are `open` (`notOpen`). Checking the old phase too
is what makes settled absorbing under KERNEL-27's adopt (mutation M3 below); (b) write, relaw:
`frozen`; (c) invoke: from `released`/`refunded` `settled`; method 0 from `open` (`notOpen`) signed
by the depositor, 1 from `held` (`notHeld`) by the beneficiary or arbiter, 2 from `held` by the
depositor or arbiter (`notParty`); the new phase must be the target (`badPhase`); other indices
`noMethod`. "Signed by" is `req.agent`, the signing member: KERNEL's owner-gated invoke
(KERNEL-25) lets a grantee reach the law, the law narrows to the parties. The names beyond the four
agreed with LANG-7 (`badPhase`, `noMethod`, `frozen`) are the package's own; they reach the wire as
`lawDenied … "escrow: NAME"`.
**Theorems (Ledger/Proofs/Escrow.lean).** Over ANY request, old and new state as data
(`Std.Admits`; `escrow_judge_admits`: the receiver's `runLaw` of the loaded body's field gives it):
`escrow_invoke` (an admitted invoke is one of the three edges, signed by a named party),
`escrow_start`, `escrow_frozen`, `escrow_occasion`, `escrow_absorbing` (from settled nothing is
admitted), `escrow_law_payout_once` (along any `Chain` of law-admitted acts from any state, at most
one payout), `escrow_deposit_first` (from `open`, a deposit before any payout). `escrow_admits`: a
birth, deposit, refund and release are each admitted, so no premise is empty. For every value of
the terms, object id, grant, signer and phase (symbolic bytes, `rfl` over `Lang.eval`):
`escrow_calls_payout` (the transfer each method emits, field by field), `escrow_method_state` (terms
carried, phase the target); `escrow_slots` (one call slot per method, a transfer).
`escrow_one_payout`, the package's statement: along any chain of law-admitted ACTS on an escrow, at
most one act's call (the call of `escrow.methods[m]` for its invoke of `m`) spends the payout key
out of the escrow's own account (depositor ≠ self; a depositor that is the object is refused
`sameAccount` by KERNEL). `escrow_verdicts` (decide +kernel through `runLaw`, representative distinct
party bytes): every phase pair × method 0..3 × signer role gives the Lean spec's NAME.
`escrow_text_reads`, `escrow_decodes`. The kernel's second line is `transfer_once` on the one
nullifier `onceNullifier (accountId e asset) "payout"` (LEDGER-6 (d)).
**Teeth.** ledger-sim (standing runs it; gates/runs.tsv `ledger-sim 1 ALL PASS`), four modes each
asserting its own lines: honest (E0–E15: unfunded deposit refused `grantTarget` with phase `open`;
deposit moves 30; `notOpen`, `notParty`; release pays B; a TOP-UP of 30 into the escrow account is
admitted; then release and refund are `settled`; follower and auditor agree); skip-judge (no law:
the second deposit and the payouts after the top-up are the kernel's `spent`; a stranger's release
pays); two-keys + skip-judge (refund spends its own key AND no law: the escrow PAYS TWICE, the plant
LEDGER-6 named); drop-calls (calls never reach the kernel: the unfunded deposit is admitted, `held`
with nothing in it). Mutations run by hand and reverted, each red in Ledger.Proofs.Escrow: M1 refund
also by the depositor (escrow_invoke, escrow_verdicts); M2 refund spends its own key
(escrow_calls_payout); M3 adoption checks only the new phase (escrow_start, so escrow_absorbing);
M4 deposit pays from the escrow itself on the payout key (escrow_calls_payout, escrow_one_payout).
**Gaps at Deployed, named (module docstring).** (1) No slot-level restatement (`Lang.program`'s run
+ judge on the codec bytes, HOSTING's `invoke_slots` shape); ledger-sim exercises that path. (2)
The calls are read as `Val`s at 1000 ticks; the receiver's `extract`/`callsOf` into `Body D` at the
method budget, and `of self asset` → `accountId X e asset`, are LANG's/KERNEL's theorems, not composed
here. CORRECTION (LEDGER-3, after 7c6c7e1): this said "no fuel-monotonicity lemma exists"; that was
wrong. LANG's `run_stable` (Lang/Proofs/Run.lean) carries a final run to every larger budget, and
LANG-8's Lang/Proofs/CallLive.lean (c4e435a) takes a run's calls through `extract` into `callsOf`.
The gap is the composition: relating the field projections these theorems evaluate to the
extraction of the whole method result. (3) A programmed object changes only by its methods is
KERNEL's `hasMethods`; the chain theorems do not need it.
**Review.** Second-agent vacuity read (a fresh reviewer, 10-18) found no vacuous statement, and two
WEAK ones that this commit fixed before landing: the first `escrow_one_payout` was a conjunction
that never linked a chain step to the call it makes (now `spendCount` over the acts' own calls,
via `escrow.methods[m]`), and `escrow_verdicts` ran `eval`, not `runLaw` (now `runLaw`, and the
`ok` rows are `Admits` witnesses). Its other asks are in (2) above.
**Alternatives.** (1) `Std.machine` for the phase plus a separate party law: LANG's general
`machine_invoke` would carry the edge theorem, but refusals would read `phase: no edge`, not the
names the bounty row and a client need; and two laws judging one act split the spec across two
statements. (2) Methods that branch on the phase and make no call off-edge: a second copy of the
law in the method text; the law is the one place. (3) The law checking the terms unchanged: a twin
of the methods' text, which `escrow_method_state` already pins.
**Critique.** The verdict-NAME table is at representative party bytes (the admitted/refused facts
are general; the names are an instance). The calls theorem reads the reference evaluator's value of
each field, not `Lang.callsOf`'s `Body`; the bridge is LANG's `runMeasured_calls` /
`callData_bodyOf`. The deposit grant is still the whole balance (cv 01a14938).
**Meta-critique.** I chose the hand-written law over Std.machine partly because the names were
already agreed; the honest reason it is better is that `escrow_invoke` states edge AND party in one
theorem the chain argument consumes directly. The mutation M3 is the one I would have missed
without the chain proof forcing it: an adopt arm copied from Std.machine (`new` only) would have
let a relaw reopen a settled escrow.
**Re-emits.** None on chain or schema: a new package and text. A LANG re-id day re-emits
`world/escrow/Escrow` by `ledger-sim --write-text`.
Status: BUILT (this commit). The bounty row (PROTOCOL's) is re-cut by PROTOCOL-6 on this text.

## LEDGER-11 · On LANG's digest day the escrow's ids are `digest`, and the deposit's once key is a creator-set `nonce` (LEDGER-3, 2026-10-18; with LANG-11's lang! day, cv 01a14aab-adae (ii))
**Decision.** LANG gives ids their own type `digest` (`Ty.digest`, `Prim.deq`; reqTy's agent, principal,
self and callTy's id fields are digest; no prim converts between digest and bytes). The escrow
follows: arbiter, asset, beneficiary, depositor and deposit's `grant` are `digest`; `agentIs` is
`deq`; `via` is an optional digest. One consequence is a design change: LEDGER-6 (c)'s deposit once
key was `self`, so that a second deposit through the same grant is `spent` by the KERNEL even under
a package bug. `transfer.once` stays bytes (an opaque key) and `self` is now a digest with no bytes in
the core, so the key cannot be `self`. The state gains `nonce : bytes`, set by the creator at
birth and carried by every method, and the deposit spends `once := some nonce`.
**Why this and not the others.** (1) `once := none`: the kernel's second line against a second
deposit is gone, and only the law (`notOpen`) remains. That WEAKENS a check, a pause item, so no.
(2) A LANG prim digest → bytes: LANG-11's surface rules it out by design (ids are not byte
strings in the core). (3) `once` typed digest: callers' keys are byte strings (the pay row's
`--once 6b31`). (4) A constant key such as "deposit": its nullifier is namespaced by the source, so
a depositor could fund only ONE escrow per account, ever. With `nonce` the kernel guard is exactly
as strong as before for the property it served: two deposits through one escrow spend one key,
whatever the nonce. Uniqueness across escrows matters only for liveness. Two escrows a creator
gives the same nonce, funded from the same account, refuse the second deposit `spent`. That
fails closed.
**Critique.** A creator-chosen field is a convention a careless creator can break, though only
against itself, and only by liveness. The nonce costs one state field and one more ledger-sim
term.
**Meta-critique.** I looked first for a way to keep `self` and found none that does not reopen
LANG's ruling. The test of the replacement is the plant that already ran: skip-judge E9, where the
second deposit is the kernel's `spent`. It still holds with the nonce, which is the property
LEDGER-6 (c) bought.
**Re-emits.** world/escrow/Escrow (new state type, new id). The bounty row's seed gains
`(nonce …)` and its ids are digests (PROTOCOL-7's lines). Nothing on chain: a re-genesis is LANG's
day anyway.

## LEDGER-12 · The escrow says what it does: one doc line, in the surface source and the Lean package alike (LEDGER-4, 2026-10-19; on LANG-60's `doc`)
**Decision.** LANG-60 gave every package a one-line `doc` (`Bounds.docOk`: at most 256 bytes of doc
characters, printed `(doc "…")` and on `read OBJ ?`'s first line) and re-emitted world/escrow/Escrow
with an empty `(doc)`. The escrow now carries: "The depositor deposits amount of asset into an
account the escrow owns; release pays it to the beneficiary (the depositor or arbiter asks), refund
back to the depositor (the beneficiary or arbiter asks); exactly one payout." (223 bytes). It is
written twice, as `(doc …)` in world/escrow/Escrow.ob and as `escrowDoc` in Ledger/Escrow.lean
(`escrow := { pkgOf … with doc := escrowDoc.toUTF8 }`), and the core text is re-emitted by
`ledger-sim --write-text` from the surface source.
**Why the line says this.** Each clause is a checked fact of the package, not a hope: who may ask
for each method is the law's `notParty` arms (escrow_invoke's three cases); "an account the escrow
owns" is LEDGER-6's `accountId self asset`; "exactly one payout" is the law's `settled` plus the
kernel's `once "payout"` (escrow_one_payout, and the skip-judge plant's second release refused by the
kernel). The line names no parameter a creator may vary beyond the state's own fields.
**Critique.** Two copies of one string is the shape the doctrine warns about. They cannot drift
silently: E0 refuses a core text that is not `Print.package escrow`, and E0s refuses a surface
source that does not lower to the core byte for byte; with the core stale both read FAIL (measured:
ledger-sim RED (2) before the re-emit). A doc is never run or judged, so a wrong doc misleads a
reader without moving a verdict; nothing proves the sentence true of the methods.
**Meta-critique.** I considered leaving the Lean side to read the doc out of the .ob at build time
(one copy); the escrow's Lean value is what its theorems are about, and making it depend on a file
read would put IO under the proofs. The copy tied by two rows is the cheaper truth.
**Re-emits.** world/escrow/Escrow (the doc section; the package re-ids). The bounty row installs it
by path (`<world/escrow/Escrow`), pins no id, and passes (`rows bounty`). Nothing else holds the old
id.

## LEDGER-13 · The escrow's payout theorem is of what the receiver runs: `RunCalls` of every successful `runMeasured` of the escrow package (LEDGER-5, 2026-10-21; on LANG-61)
**Decision.** `Ledger.Proofs.EscrowRun.escrow_run_calls`: if `readPackage look pkg = .ok escrow` and
`∀ x, digestOf (bytesOf x) = some x`, then every `runMeasured bytesOf digestOf look rv pkg state method
args r budget = .ok (s, calls, rows, t, n)` satisfies `RunCalls digestOf state method args r.self calls`:
the state slots read (`readState`) as `stateOf amount arb asset ben dep nk p`, `digestOf asset = some a`,
and exactly one of: `method = 0` and the arguments decode to `{grant = gb}`, `digestOf gb = some gd`,
`digestOf dep = some d`, `calls = [transfer (of d a) (of r.self a) amount (some gd) (some nk)]`;
`method = 1`, `digestOf dep = some d`, `calls = [transfer (of r.self a) (of d a) amount none (some
"payout")]`; `method = 2`, the same to `digestOf ben`. `escrow_program_calls` states it at `invoke`'s
call `X.program.run` (premises `X.Lawful`, `X.program = Lang.program X.env.bytes X.digestOf`);
`escrow_run_deployed` at the node's `Ctx` (`Host.Deployed.X`) with only the package premise left.
KERNEL's `AcctRef.resolve` sends `of r.self a` to `accountId X r.self a` by definition, so a payout's
source is the account whose one `once "payout"` nullifier both payouts spend.
**The spec moved to the receiver's term.** `EscrowSpec.methodResult ℓ`: `apply4 0 ℓ` under
`[escrow.body]`, extracted WHOLE at `resultOf`, replaces `methodAt` (an inlined method term under
lib `[]`, which LANG-61 showed is not the receiver's value) and the fourteen projections
(`slotField`, `ownerOf`, `assetOf`, `someOf`, `valueOf`, `callOfMethod`, `stateOfMethod`).
`escrow_method_results` (one theorem, by `rfl`, for every term value, every other request field,
every argument of a payout and every rows record) replaces `escrow_calls_payout` and
`escrow_method_state`; the `of`/`none`/`some` tags are in the data. `spends` (over the result) replaces
`spendsB`; `callAt`, `spendCount`, `escrow_one_payout` count `methodResult`, statement unchanged.
**Proof.** `runMeasured_means` (LANG-61) gives the run's BigStep of `apply4 g ℓ` under `L.lib` and the
Means of the extracted result. `load_top` with the two premises gives `L.pkgs[g]? = some escrow` and
`L.lib[g]? = some (escrow.body.relocate f)`; `escrow_noRef` (proved here, LANG-61's named need) and
`relocate_noRef` make it `escrow.body`. `escrow_resolve`: the indices are 0, 1, 2 at `resultOf`, else
refused. `escrow_state_shape` (from `readState_conforms`) and `deposit_arg_shape` fix the data's
shape. `run_result`: `methodResult`'s eval is a BigStep under `[escrow.body]` (`run_bigStep`),
`relib_apply4` carries it to `L.lib`, `bigStep_deterministic` makes the two values one, a no-ref
meaning is lib-free (`means_relib`), and `means_deterministic` with `extract_means` makes the
receiver's result `methodResult`'s. `callsOf` then reads the transfer; each digest it needs is
either `r.self` (the round trip) or an existential pinned by `digestOf … = some …`.
**Premises, against the code.** (1) the round trip: `Ctx.Lawful.digestOf_bytes`; at the node
`Receive.deployed_ctx_lawful` (`Codec.Deployed.digestOf_bytes`), discharged in `escrow_run_deployed`.
(2) `X.program = Lang.program X.env.bytes X.digestOf`: `Host.Deployed.X`'s definition, `rfl`. (3)
`readPackage look pkg = .ok escrow`: the object's package cell holds install bytes of `escrow`
(`Wire.encodePackage escrow`, which decode to it: `escrow_decodes`); which package an object runs is
the statement's subject, so it stays a premise. (4) the run succeeded: `invoke`'s step
(`Kernel/Receive/Derive.lean`). No premise was added to any existing theorem.
**Teeth.** `run_calls_pins_payee` (for `escrow_run_calls`): over a decoder naming one id per bytes,
from a state whose beneficiary and depositor differ, a release paying the depositor is not
`RunCalls`. `run_result_needs_body`: a body differing in one field (`release` holding `refund`'s
term) means a different result (the depositor paid, `refunded`) than `methodResult "release"` (the
beneficiary, `released`), so `run_result`'s body premise bites. `escrow_run_spends` (for
`escrow_method_results` and the chain's count): `spends` is true of a release's result and false of
a deposit's (depositor ≠ escrow), so `escrow_one_payout` is not true by a constant count.
**Read.** Second-agent vacuity read with the disjunct check: nothing vacuous, nothing weaker than
HEAD. The three disjuncts carry `method = 0/1/2` (exclusive; none follows from the premises without
the run's `resolveMethod`); each `calls` equation binds the run's own output; every existential is
pinned (the seven terms by the `readState` equation, `stateOf` injective; `a`, `gd`, `d`, `b` by
`digestOf … = some …`; `gb` by the `decodeData` equation). `escrow_method_results` is strictly more
general than `escrow_calls_payout` (any request, any payout argument, any rows) and subsumes
`escrow_method_state`. Fixed from the read: the label of `escrow_run_spends` (it teeths the spec's
count, not the run theorem), and `run_calls_pins_payee` added as the run theorem's own tooth. The
reader's probe: `escrow.imports = []`, `escrow.body.digestLits = []` and `stateSlots` of a released
state is `some`, by `decide +kernel`; nothing in the premises is contradictory.
**Critique.** (a) No kernel-checked witness that the premises of `escrow_run_calls` hold together: a
`decide +kernel` of a concrete Sim run is stuck in `runSetup` (each piece reduces alone: load,
readPackage, readState, decodeData, resolveMethod, reqOk, readsData); `ledger-sim` runs the real
receiver on the escrow (E rows, ALL PASS), which is behavioural evidence only. (b) The state the run
WRITES is not in the theorem: `runMeasured_means` does not expose `stateSlots row ds 0 = some s`, so
the receiver-side twin of `escrow_method_results`' state half needs that conjunct (Lang's). (c) The
chain theorems still count `methodResult` over states `stateOf … phase`, not a chain of receiver runs
over the slots each wrote; (b) is its first step. (d) `means_relib` (a no-ref value's meaning is
lib-free) is a Lang fact proved privately here; it belongs beside `bigStep_relib` in
`Lang/Proofs/Extract.lean`. (e) Lang's parsimony remark, recorded and not acted on: `Means` walks the
same path as `Lang/Proofs/Need.lean`'s `Forces` (LANG-21); they stay apart, Lang's to merge or not.
**Meta-critique.** I first planned LANG-61's route literally: `means_get` twice, then invert sum
meanings down to base fields, each projection derived under `[body]` and carried by `Relib`. That
is seven projections deep per call and repeats the spec's own shape; extracting the whole result
under `[body]` by `rfl` and comparing meanings once is shorter and states more (the whole result,
state included). It cost one lemma Lang lacked (`means_relib`), which is the right trade: the lemma
is general, the projections were the escrow's. `RunCalls` is a named statement so the three
theorems (run, program, deployed) share one conclusion instead of three copies.
**Nothing moves.** No wire, vector, shipped text or package byte: world/escrow is untouched,
`escrow` is the same value.

## LEDGER-14 · The one-payout theorem is of the receiver's runs: a chain of committed runs, each reading the slots the last wrote, pays out at most once; two kernel-evaluated runs meet its premise (LEDGER-6, 2026-10-21; on LANG-62/63)
**Decision.** `Ledger.Proofs.EscrowRun.escrow_runs_one_payout`: under `∀ x, digestOf (bytesOf x) = some x`,
every `Runs (Lang.program bytesOf digestOf) pkg escrow state runs` has `payoutCalls runs ≤ 1`. `Runs prog
pkg p` is the sequence `invoke` commits on one object: each step, in its own pinned view `look` with
`readPackage look pkg = .ok p`, is `prog.run look rv pkg state method args r budget = .ok (s, calls,
rows, used)` with `prog.judge look (some pkg) laws state s r = .ok ()` (the package's law, then the
cell's laws, over the slots before and after), and the next step runs on any `next` with
`∀ k, next.get k = s.get k` (the cell `invoke`'s write leaves holds what the run wrote key by key,
not necessarily as the same list; `readState_get`: `readState` reads only by key); method, arguments,
request, budget, rows view and laws are free per step. `payoutCalls` counts the returned calls that
are a transfer through no grant (`isPayoutCall`: `via = none`). Forms: `escrow_program_one_payout`
(a lawful `Ctx` whose program is `Lang.program` over its own codec), `escrow_runs_deployed`
(`Host.Deployed.X`'s program; premise: the runs only, each carrying its package read).
`escrow_runs_after_payout`: a run that returns a payout is the last of every `Runs` it starts.
`escrow_judge_settled`: the judge refuses every transition out of slots that read `released` or
`refunded`. `RunCalls` gains the written slots: each method's case also says `readState … s = .ok
(stateOf … held|refunded|released)` (LANG-63's read-back conjunct of `runMeasured_means`).
**Deleted.** `escrow_one_payout`, `spends_is_payout`, `spendCount_le` (Proofs/Escrow) and `spends`,
`Act`, `argFor`, `stepsOf`, `callAt`, `spendCount` (EscrowSpec), and the tooth `escrow_run_spends`:
they counted `methodResult` over states `stateOf … phase` that the spec chose, not the slots a
run wrote. The run theorem needs no `dep ≠ self` premise (a deposit names its grant, so it is never
a payout call, whoever the depositor). `escrow_law_payout_once` (the law alone, over `Chain`) stays.
**(a) The witness, in the kernel.** `Ledger.Proofs.EscrowWitness.escrow_runs_witness`: on the node's
codec an object whose cell holds `encodePackage escrow`, born `open`, deposited into and then released
by its depositor, is a `Runs` of `Host.Deployed.X`'s program with `payoutCalls = 1`. Both runs and
both judges are evaluated by `decide +kernel`; no `native_decide`, no allow or tcb row. Why LEDGER-13's
probe stuck, corrected: `load`/`loadAll` are mutual well-founded recursion (`termination_by`), which
the kernel does not unfold, and `Wire.decodePackage` of the package bytes in the kernel exceeds a 6G
cap (LEDGER-5's "each piece reduces alone" was wrong: those probe runs were OOM-killed with no output,
exit 143). Route: `load` by its equation (`load_one`: one package, no imports), the package read from
its install bytes (`readPackage_installed`, no decode), `runSetup` assembled from its pieces
(`setup_eq`), and only the machine run, extraction, `stateSlots`, `callsOf` and the law left to the
kernel: the module checks in ~10 s, 2.7 GB.
**Teeth.** `escrow_second_release_refused` (deployed, kernel-evaluated): a third run, release again
from the `released` slots, succeeds and returns a payout; the judge refuses every transition out of
them. So the bound is the judge's, not the runs'. `escrow_judge_bites` (spec, all values): from
`released` the method still pays and the law admits nothing. `payout_call_tells`: a grant-named
transfer is not a payout, a grantless one is, so the count is not constant. `run_calls_pins_payee`,
`run_result_needs_body` kept.
**Critique.** (1) `Runs` omits checks `invoke` makes (`overTicks`, `rowParent`, `checkState`,
`tooManyCalls`, the derivation of the calls): each omission makes the theorem cover MORE sequences,
so it is stronger, not weaker; but it says nothing about whether the payout call then commits (that
is KERNEL's `transfer_once` on the one `"payout"` nullifier, a second, independent bound). (2) That
the slots `invoke` hands the next run hold, key by key, what this run wrote is `invoke`'s `writeOf
obj (diffOps old new)` and KERNEL's state reading, not composed here; KERNEL's `hasMethods` (state changes only
by methods) remains the named gap of LEDGER-10. (3) `isPayoutCall` counts grantless transfers, which
the kernel authorizes only out of the calling object's own account; the one escrow transfer out
of its own account it does not count is a deposit by the object itself (`of self` to `of self`,
through a grant), which KERNEL refuses `sameAccount` at derivation, outside `Runs`; counting by
source `of self` would need `DecidableEq D` and either `dep ≠ self` or a model of `deriveCalls`.
(4) `readState_get` is a Lang fact proved here; it belongs in Lang/Proofs beside `readState_conforms`.
**Meta-critique.** The first plan restated the spec chain with the run substituted per step; it would
have kept `spends`, `callAt` and `Act` beside the run and needed `dep ≠ self` and an occasion premise
linking the run's method to the law's. Reading `invoke` showed the judge already runs on the run's
own slots, so the chain needs only: a payout run writes a settled state (RunCalls' new conjunct) and
the judge refuses out of it. Both premises vanished, and so did the spec chain. The witness first
looked like it needed a Lang change (structural `load`); proving through `load`'s equation lemma
from the outside avoided touching Lang.
**Read.** Second-agent vacuity read with the disjunct check (probes logs/ledger6-vac-1.lean,
-vac-2.lean): nothing vacuous, nothing weaker than main. Each `RunCalls` disjunct carries its own
`method = 0/1/2` and pins `calls` and the written slots; `¬ RunCalls … []` holds; the witness makes
`Runs` satisfiable at length two with the bound attained; `escrow_judge_settled`'s premise is not
empty (the judge admits from `open` and `held`). Axioms of every new theorem: propext,
Classical.choice, Quot.sound. Against main's `escrow_one_payout`: no `hne` premise, and under `hne`
the counts agree on escrow outputs. Fixed from the read: `Runs` chained the written list itself to
the next step, which a real `invoke` sequence need not match (its cell's slot list may be ordered
differently); it now takes key-wise equal slots. Recorded, not acted on: the self-deposit (critique 3).
**Nothing moves.** No wire, vector, shipped text or package byte; `escrow` is the same value;
world/escrow untouched. ledger-sim 1 ALL PASS; --harness-control RED (1).

## LEDGER-15 · The one-payout theorem over the history the World admits: KERNEL's next-run link turns an admitted history around one object into a `Runs` (LEDGER-6, 2026-10-21; on KERNEL-23's 5807a47 and 628a8b9)
**Decision.** `Ledger.Proofs.EscrowInvokes.escrow_invokes_one_payout`: for a lawful `Ctx` whose program is
`Lang.program` over its own codec, every `Invokes X obj pkg escrow w invs` has `payoutCalls invs ≤ 1`;
`escrow_invokes_deployed` at `Host.Deployed.X`, premise only the history. `Invokes X obj pkg p w` is a
history of admitted turns around one object, each step one of:
- `invoke`: a signed top-level invoke of `obj`. Its premises are `receive X w c = .ok t`,
  `World.admit X.env w t = .ok w'`, `c.unsigned.body = .invoke obj …`, `invokeRun … = .ok (cell, pkg, r)`,
  `readPackage (pinned X.env w c.unsigned.pins) pkg = .ok p`, and the program's run on `stateOf cell` at
  `min budget (poolOf …)` returning `calls`, which are counted.
- `other`: any admitted turn that neither touches nor creates `obj` (`∀ x ∈ t.touches, x.cell ≠ obj`,
  `obj ∉ createdIds t`). It runs no method of `obj`, and nothing is counted.

`invokes_runs` shows such a history is a `Runs` (LEDGER-14) from the state the object holds. Each link
is a KERNEL lemma:
- `admit_frame`: an `other` turn leaves the object's entry;
- `invokeRun_live`: an invoke runs on the live cell;
- `invoke_next_judged`: the judge admitted the run;
- `invoke_next_slots`: the next live state holds the run's slots key by key.

This closes LEDGER-14 critique (2) for top-level invokes.
**Teeth** (EscrowWitness, node's program, kernel-evaluated):
- `escrow_link_bites`: the witness's release from `held` is a successful run that the judge admits and
  that returns a payout. Taken twice on the same `held` slots it would pay twice; only the next-state
  link rules that out (what it wrote differs from what it read at the phase key).
- `escrow_second_release_refused`: the judge's half of the same point.
**Read.** Second-agent vacuity read with the disjunct check: nothing vacuous; no new disjunctions;
axioms propext, Classical.choice, Quot.sound. It found and I fixed: the first draft allowed only
consecutive top-level invokes of `obj` (any interleaved turn broke the chain), so the `other` step was
added; the header named a tooth that did not exist. It flagged, and KERNEL-23 closed in 628a8b9
(Kernel/Proofs/InvokeWitness.lean): nothing showed `receive` + `World.admit` ever accept an invoke of
a programmed object, which `invoke_next_*`'s premises (and so `Invokes.invoke`'s) needed.
**Critique.**
(1) No escrow-specific `Invokes.invoke` witness. KERNEL's witness is the `counter` package. An admitted
escrow release needs its transfer derived (an account, a funded balance, the payout once key). It is
cv 01a1553b-2765, sequenced after KERNEL-28's amount right, which changes the grants and the
transfer's derivation. The `Runs` it reduces to is witnessed (`escrow_runs_witness`).
(2) A turn that touches `obj` other than as its top-level invoke is not a step. That includes an
invoke of `obj` nested in another object's call tree (KERNEL's cv 01a15430-0f62) and any other touch;
a history containing one is not an instance.
(3) `readPackage` per invoke stays a premise. Which package the object runs is the statement's
subject; that the package cell never changes is KERNEL's (ROM), not composed.
(4) The self-deposit remark of LEDGER-14 (3) stands.
**Nothing moves.** No wire, vector, shipped text or package byte. ledger-sim 1 ALL PASS; --harness-control
RED (1).
**Amended (FAERIE-DOCS 2026-10-27; KERNEL-59, 4442b43; READ-LEDGER B3).** `escrow_invokes_one_payout` is no longer over `Invokes X obj pkg escrow w invs`: it is over `ObjectHistory X obj w w' tr` plus `hpkg`, and the hand-rolled `Invokes` is deleted. Critique (2) is superseded: an invoke of `obj` nested in another object's call tree IS covered (`ObjectStep.nested`), and so is every other turn and recorded refusal.

## LEDGER-17 · Unspent credit sits: no sweep, no decay, no reclaim to a commons (ROOT for LEDGER, Ember's ruling 2026-10-21; closes LEDGER-4's taste fork)
**Decision.** A credit line, once extended (LEDGER-4), sits until the holder uses or repays it. No
receiver sweeps unused credit, none decays it over heights, none reclaims it to a commons or to the
issuer. Ember, 2026-10-21: "FINAL. Just let it sit there. It isn't a strong opinion, it's just for
simplicity's sake." Final for v1.
**Alternatives.** (a) Issuer reclaim of unused headroom (a power over a holder's account). (b) Decay
by height. (c) A sweep of idle credit to a commons. Each adds a receiver, a call kind and an
authority rule, and each was a taste fork with no row asking for it.
**Why.** Simplicity: the ledger keeps three authority rules and one direction for credit; LEDGER-4's
`credit_exact` stays the whole story of a floor moving.
**Critique.** An issuer who over-extends still can only wait for holders to repay; that is now the
design, not a gap. **Meta-critique.** Ember called it weak-opinion and final at once: the finality is
for v1's simplicity, so a reclaim arrives only as a new entry with a row that needs it, never as a
reinterpretation of this one.
**Status.** ruled by Ember 2026-10-21 (recorded by ROOT for LEDGER; no LEDGER lane live). Nothing moves:
no code, wire or package byte changes.

## LEDGER-16 · LEDGER-6 (c)'s v0 whole-balance grant is superseded by KERNEL-60's `transfer (cap)` (KERNEL-24 with LEDGER-6's agreement, 2026-10-21)
The depositor grants the escrow object `transfer amount` on its own account, no longer `mutate`. The kernel spends each transfer through the grant from the grant's ledger: `transferSpent` past the cap. So what a deposit can move is bounded by the grant, not by the package text. `mutate` moves no value at all now. The package bytes are unchanged (`escrowDoc` and the methods; E0 stays byte for byte). Only the Escrow header comment changed. ledger-sim: E7 grants `transfer 30`. In the skip-judge plants a second deposit is now refused by the spent cap (`transferSpent`) before the once key. The new plant short-cap grants 29 for a deposit of 30, so the package asks for `amount + 1` of what it was lent: E8 is refused `transferSpent`, and the escrow stays `open` and empty. `ledger-sim 1` ends ALL PASS. `ledger-sim --harness-control 1` reads RED.

## LEDGER-18 · The deposit's authority is exactly its amount: the cap is read off the escrow, and a deposit then a release are an admitted history (LEDGER-7, 2026-10-22; on KERNEL-60's `Right.transfer (cap)`, KERNEL-59's `ObjectHistory`; cv 01a1553b-2765)
**Decision.** The escrow's deposit is the first real user of `Right.transfer (cap)`. Its grant's cap
is the escrow's own `amount`, READ, not written beside it. `Escrow.amountOf` decodes the amount term
from an escrow's slots. ledger-sim's E7 depositor reads it off the live escrow cell and grants
`transfer amount`, and E7 also checks that the read equals the terms the escrow was born with. The
short-cap plant grants `amount - 1`. The deposit then moves `amount` through a grant with `amount - 1`
left, and it is refused `transferSpent` OF THAT GRANT, by its id (`spentOf`, which compares the whole
refusal, not its name); P keeps all 100. Skip-judge's E9 is pinned the same way. Kernel side:
`Ledger.Proofs.EscrowAdmitted`.
- `escrow_history_witnessed`: a signed deposit, then a signed release, of one escrow object. Each is
  derived by the REAL `receive` (the deposit's transfer through the grant, its ledger append and
  once nullifier; the release's payout) and admitted by `World.admit`, at a lawful `Ctx` running
  `Lang.program`. Together they are an `ObjectHistory` whose steps read the package as `escrow`, with
  `payoutCalls = 1`. So `escrow_invokes_one_payout`'s premises hold together and its bound is reached.
  This closes LEDGER-15 critique (1).
- `escrow_deposit_spends_cap`: at a lawful `Ctx` running the language, the deposit is an admitted
  `ObjectStep` of an object whose package reads as `escrow`, and its one call moves the `amount`
  its own old state holds (`amountOf`) through grant `g`. `g`'s ledger reads `(1, amount)`
  before and `(2, 0)` after. The source balance falls by exactly `amount`. On the World it left, the
  same transfer through `g` is `transferSpent g`.
- Tooth `escrow_short_cap_refused`: the same admitted deposit's transfer is `transferSpent g` when
  read in a view equal to its own pinned view except that `g` lends `amount - 1`.

**The instance** (KERNEL's `InvokeWitness` shape): one-byte digests, toy hash `64 + 8·b₀ + b₁`,
signatures accepted, a hand-built World (member, escrow object, package, three accounts, the grant),
not reached from a genesis. The witnessed theorems carry no reachability premise. The package is
read from its install bytes (`readPackage_installed`) and the closure through `load`'s equation
(`load_one`, now public in EscrowWitness). Everything else, both derivations, runs, judgements and
admissions, is `decide +kernel`, with no `native_decide`. The module checks in about 70 s of kernel
time. One pitfall, measured: a `decide +kernel` of `readKind … = .ok pkgCell` compares the package
literal and did not finish in 25 minutes; `rfl` closes it at once (KERNEL's c1_pkg route).

**Statements kept.** `escrow_runs_one_payout`, `escrow_runs_after_payout`, `escrow_invokes_one_payout`
and `escrow_invokes_deployed` keep their statements: the deposit's call shape (`via = some grant`)
did not change, only the grant's right did.

**Owner's read of KERNEL-60's five shape changes** (sent to ROOT first): no statement is weaker.
- transfer/effect_transfer/credit_authorized: the chain is over `.transfer 0` / `.credit 0`.
  `rightKey` ignores the cap, so the 0 is a kind marker. Each gains the leaf grant's spend
  conjuncts.
- transfer/credit_exact: the frame excludes only `via = some k`, and that `g` is described whole by
  the new conjunct.
- Disjunct check: neither authority disjunct follows from the premise or the instance alone.

FINDING: no theorem READS BACK a spend. ROOT ruled: KERNEL-30 proves `LedgerContiguous` over the fold
and `spend_reads_back`; LEDGER owns `grant_moves_le_cap` on top of it.

**Read.** Second-agent vacuity read with the disjunct check (LEDGER-7-READER; probe
logs/ledger7r-axioms.lean): LAND-WITH-FIXES, and every fix was taken. There are no disjuncts. Every
variable is tied: `amt` is both the call's amount and the old state's `amountOf`, and the ledger
reads are on the `g` the call names. `transferSpent` has the one source `spendVia`, and a missing
pin is `unpinned`, never `transferSpent`. `payoutCalls = 1` is attained. Axioms are propext,
Classical.choice and Quot.sound. Fixed from the read:
(1) `escrow_deposit_spends_cap` did not state that the program is the language, that the Ctx is
lawful, or that the package reads as `escrow`, so a made-up program met it. It now states all three.
(2) The short-cap tooth's amount and call were not tied to the escrow. It is now over the admitted
deposit step, in a view differing from its own only at `g`.
(3) ledger-sim's honest E8 compared the literals 30/70. It now compares `amt`/`100 - amt`.
`spentOf` was confirmed to compare the whole refusal, and so the grant id.

**Critique.** (1) The witness World is hand-built, as KERNEL's is. A genesis-reached instance
needs the toy Env to run ledger-sim's own births, which the kernel evaluator cannot do with FNV over
the codecs. (2) "Exactly its amount" is shown for this instance. Over every history it is
`grant_moves_le_cap`, which waits on KERNEL-30. (3) The self-deposit remark (LEDGER-14 (3)) stands.
The chain over receiver runs is KERNEL-59's `object_history_chain` (LEDGER-14 open (c), done).
**Meta-critique.** The brief asked for the Escrow package or method to change. Nothing in the
package can read a grant cell, and a package-side check would be a second, weaker statement of the
kernel's cap. So the package bytes stand and the derivation lives with the depositor, where the
grant is made.
**Nothing moves.** No wire, vector, shipped text or package byte. `escrow` is the same value, and E0
and E0s pass byte for byte. ledger-sim 1 ALL PASS; --harness-control RED (1).

## LEDGER-19 · A grant moves at most what it had left, over every audited history: `grant_moves_le_cap`, a `Std.chain_sum` instance over Worlds (LEDGER-7, 2026-10-22; on KERNEL-30's 1fe9f93; ROOT's ruling on LEDGER-18's finding)
**Decision.** `Ledger.Proofs.GrantCap.grant_moves_le_cap` takes a World `w` and a grant `g` such that:
- the cells are canonical and the grants' ledgers are contiguous (as at every World a follower
  reaches from genesis: `genesis_cellsCanon`, `genesis_ledgerContiguous`,
  `audit_ledgerContiguous`);
- `g` is a live grant whose transfer ledger has `left` left.

Then every audited log `audit X w l = .ok w'` is a `Std.Chain (GrantStep X g) w steps` (with
`steps.map Prod.fst = l`). Pick any amount per step that is either 0 or the amount of a transfer the
step dispatched through `g` (`MovesThrough`: the turn's own call, the one its event decodes to and
the audit re-derived, has `transfer src dst a (some g) once` anywhere in its tree, signed or called
by an object's run). Those amounts sum to at most `left`. So the cap binds over the history, not
only at one turn. `grant_credits_le_cap` is its credit twin, on the credit ledger, counting credit
lines (`CreditsThrough`, from `credit_reads_back_dispatched`). Both are instances of one private
scheme (`spends_le_left`) over the ledger base.

**Proof.** The chain is `audit_grant_chain`, the audit's own steps:
- `GrantStep` is `auditStep` from a World where `CellsCanon`, `LedgerContiguous` and `GrantOrTomb`
  hold;
- each step carries those three (`grant_step_keeps`: KERNEL-30's `step_ledgerContiguous`, KERNEL's
  `admit_cellsCanon`, `refuse_live`).

`Std.chain_sum` is applied with potential `2^64 - leftAt` and weight `leftAt o - leftAt n`:
- `left_falls`: what is left never rises. A turn keeps the grant, retires it, or appends one entry
  (`grant_turn_ledger`). A retired grant is a tombstone for ever (`fold_entryStep`: an entry never
  moves back, so no birth reuses the id).
- `move_weight`: a transfer through `g` weighs exactly its amount (`spend_reads_back_dispatched`,
  the call identified through `auditTurn_ok`'s `decodeCall`).

**Tooth.** `Ledger.Proofs.GrantCapTooth.grant_cap_needs_contiguous` (`decide +kernel`, through the
real `receive` and `World.admit`). Every premise of `grant_moves_le_cap` holds except
`LedgerContiguous`:
- `CellsCanon` (all 256 ids enumerated);
- a live grant with 10 left;
- `audit X w [t1, t2] = .ok w'`, its turns re-derived from their decoded calls;
- steps that are the audit's own, each `MovesThrough` 10.

Its grant is gapped (entries at `transferBase` and `+4`), and the amounts sum to 20 > 10, with the
balances going 100 → 80 / 20. So the bound fails exactly where that premise does. This is KERNEL-30's
`gap_never_falls`, lifted from one cell to an audited history.

**LANG, by ROOT for LANG** (no LANG lane live; a type parameter with the old default):
- `Lang/Proofs/Chain.lean`'s `Chain` is generalised over its request and state types,
  `Chain {Q St} (R : Q → St → St → Prop) : St → List (Q × St) → Prop`, and every scheme is made
  parametric.
- At `Q = St = Data` every statement is the old one: StdChain, History, HistoryWitness and the
  Escrow modules build with no text change.
- ROOT ruled against a hand induction over `audit` beside it, because two chain schemes drift.

**Not via ObjectHistory.** ROOT named `ObjectHistory`, but its steps are an object's. A turn that
writes a grant is not an `ObjectStep` of it: `other`/`keep`/`frame` exclude a touch, and
`write`/`law`/`invoke` read an object. So a grant's history is the audit's own chain instead.

**Read.** Second-agent vacuity read with the disjunct check (LEDGER-7-READER, probes
logs/ledger7r-grantcap.lean): the theorem is sound and not vacuous.
- `steps` is pinned by the log and the deterministic `auditStep`.
- The `amt x = 0` disjunct only skips a step.
- `MovesThrough` is tied to the audited call (`auditTurn_ok`'s `decodeCall`).
- The bound rests on `left_falls`: without it a 10→0→10→0 ledger would sum to 20.
- The tomb case is sound.
- The Chain generalisation moves no other file's text.
- Axioms: propext, Classical.choice, Quot.sound.

Fixed from the read:
- The first tooth's `Ctx` decoded nothing, so no audit hypothesis could hold and it refuted only the
  receive/admit fact. It now audits, proves `CellsCanon`, and refutes the sum itself, with the
  balances shown.
- A docstring's "so at most its cap" overclaimed. It now reads: what was left, which is the cap for
  an untouched grant.

The third read: LAND. Its optional fix was taken: the tooth states that its steps are a chain of the
audit's own `auditStep`s.

**Critique.**
(1) The bound is over transfers. A grant's transfer ledger also falls by carves (`checkParent`'s
`spendAt` when a child is granted from it). Those weigh their `u` in the sum but are not
`MovesThrough`, so they only tighten the bound. Including carves would need a `checkParent`
read-back (KERNEL-30 offered one).
(2) No CONTIGUOUS non-empty audited log is witnessed reaching the bound. The tooth's audited log is
gapped, and the bound is attained at one admitted step by LEDGER-18's `escrow_deposit_spends_cap`.
(4) The credit bound has no tooth of its own. Its mechanism is the transfer bound's parametric
`left_falls`, and a gapped credit ledger would mirror the transfer tooth.
(3) `left` is what was left at the start. That `left` is the grant's cap for a grant no spend has
touched is `grant`'s birth (`rightSlots`), and it is not restated here.

**Meta-critique.** The first shape counted a telescoping sum of what `leftAt` lost, which alone is
arithmetic (the sum of drops is the total drop). The content is in two step lemmas the chain
scheme takes as `hstep`: the drop is never negative (a gapped ledger or a reborn id would break
that), and a transfer's amount IS its step's drop. The tooth breaks the first of these.

**Nothing moves.** This is proof-side only: no wire, vector, package byte or kernel definition
changes.
