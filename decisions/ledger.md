# decisions/ledger.md — the LEDGER layer (value, transfer, wells, floors, credit, escrow)

LEDGER-1..5 were written in `decisions/kernel.md` while LEDGER built under KERNEL's prefix; they
stay there as written. From LEDGER-5's close on, LEDGER's decisions are here. Format per
`decisions/README.md`: decision · alternatives · why · CRITIQUE · META-CRITIQUE · status.

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
