/-
# Lang.StdOfferEscrow — an offer that moves value: the escrow instance of `Std.offer` (PROT-8)

`Std.offer` (PROT-6) fuses two offers into a session and moves nothing. An offer that moves value
needs its value to be LINEAR: it may not vanish with the row. Here an offer HOLDS its leg:

* `post {give, grant, n, payTo, role, terms}` inserts offer `n` with value `{give, payTo, role,
  terms}` and, in the same tree, ONE call: `transfer (of agent give.asset) (of self give.asset)
  give.amount (via := some grant)`. `grant` is the poster's grant to the object of `transfer` on its
  own account (KERNEL-60): the kernel spends it from the grant's cap. The row stands exactly when the
  leg moved in.
* `take {keys, pair, theta}` judges exactly as `Std.offer`'s take (its own pinned offer the one the
  deal names for it, `offerNotNamed`; `offerJoint` on the two pinned offers' `{role, terms}` and θ)
  and, on `ok`, retracts its own offer, inserts its session row and makes ONE
  call: `transfer (of self give.asset) (of peer.payTo give.asset) give.amount`, its own leg to the
  peer's `payTo`. Both takes run in the matcher's one tree, so both legs move or neither (KERNEL-45).
* `withdraw {}` reads its own pinned offer and retracts it, crediting its leg back: `transfer (of
  self give.asset) (of payTo give.asset) give.amount`.

So a standing offer's leg leaves the object only with its row, and only to the peer (take) or back
to its own `payTo` (withdraw): `offer_guard` admits a retract only from `take` or `withdraw`
(`notConsumer`), and each of them moves the leg in the same tree. That is the linear half of
PROT-8 (Nomos: a contract may not terminate holding linear assets); the kernel conserves every
denomination over the turn (`Kernel.Proofs.Value.admit_value`), so what leaves one account arrives
in another. The fuse, the guard, the judge and the session log are `Std.offer`'s.
-/
import Lang.StdOffer

namespace Nanodregg.Lang.Std

/-! ## Types -/

/-- An offer's leg: the amount of one denomination it holds. -/
def escrowLegTy : Ty := .record [("amount", .nat), ("asset", .digest)]

/-- An escrow offer row's value: its leg, where the counterparty's leg is paid, its role and box. -/
def escrowValTy (theta roles : List Label) : Ty :=
  .record [("give", escrowLegTy), ("payTo", .digest), ("role", offerRoleTy roles), ("terms", offerTermsTy theta)]

def escrowDecl (theta roles : List Label) (limit : Nat) : RelDecl :=
  ⟨offerKey, escrowValTy theta roles, limit, none, 0, true, some "offer_guard"⟩

def escrowRels (theta roles : List Label) (offerLimit sessionLimit : Nat) : List (Label × RelDecl) :=
  [("offer", escrowDecl theta roles offerLimit), ("session", offerSessionDecl theta sessionLimit)]

/-- Every escrow method's one call kind. -/
def escrowCallTy : Ty := callOf ["transfer"]

def escrowPostArg (theta roles : List Label) : Ty :=
  .record [("give", escrowLegTy), ("grant", .digest), ("n", .nat), ("payTo", .digest),
    ("role", offerRoleTy roles), ("terms", offerTermsTy theta)]

/-- `withdraw` reads its own offer point. -/
def escrowWithdrawRows (rels : List (Label × RelDecl)) : Ty := rowsTy rels offerRead []

/-! ## Terms -/

/-- The account of `owner` in denomination `asset`. -/
def escrowAcct (owner asset : Term) : Term :=
  .inj acctRefTy "of" (.record [("asset", asset), ("owner", owner)])

/-- `transfer src dst amount (via)`, no once key: the row edit in the same tree is what moves a
leg once. -/
def escrowTransfer (amount src dst via : Term) : Term :=
  .inj escrowCallTy "transfer" (.record [("amount", amount), ("dst", dst),
    ("once", .inj (optTy .bytes) "none" (.record [])), ("src", src), ("via", via)])

def escrowNoVia : Term := .inj (optTy .digest) "none" (.record [])

/-- Pay leg `give` (a value of `escrowLegTy`) from the object `self` to `to`. -/
def escrowPay (self to give : Term) : Term :=
  escrowTransfer (.get give "amount") (escrowAcct self (.get give "asset")) (escrowAcct to (.get give "asset"))
    escrowNoVia

/-- A result with one call and the given row edits. -/
def escrowResult (rels : List (Label × RelDecl)) (call state : Term) (edits : List Term) : Term :=
  resultT (callsT [someCallT escrowCallTy call]) state (.record ((slotLabels "e" edits.length).zip
    (edits.map fun t => someCallT (editTy rels) t)))

/-- **The post** (var 0 req, var 1 arg, var 2 state): insert the offer; move its leg in. -/
def escrowPostBody (rels : List (Label × RelDecl)) (od : RelDecl) : Term :=
  let a (l : Label) := Term.get (.var 1) l
  escrowResult rels
    (escrowTransfer (.get (a "give") "amount") (escrowAcct (.get (.var 0) "agent") (.get (a "give") "asset"))
      (escrowAcct (.get (.var 0) "self") (.get (a "give") "asset"))
      (.inj (optTy .digest) "some" (a "grant")))
    (.var 2)
    [activityEdit rels "offer" od "insert" (.record [("n", a "n")])
      (.record [("give", a "give"), ("payTo", a "payTo"), ("role", a "role"), ("terms", a "terms")])]

/-- The take's success (inside the verdict's `ok` arm: peerVal 1, ownVal 3, req 5, state 7): pay
its own leg to the peer's `payTo`; `Std.offer`'s two edits. -/
def escrowTakeDone (theta : List Label) (rels : List (Label × RelDecl)) (od sd : RelDecl) : Term :=
  escrowResult rels (escrowPay (.get (.var 5) "self") (.get (.var 1) "payTo") (.get (.var 3) "give"))
    (.var 7) (offerTakeEdits theta rels od sd)

/-- **The take**: `Std.offer`'s tree (`offerTakeTree`: refusals `offerUnpinned`, `noOffer`,
`peerRowUnpinned`, `noPeerOffer`, `offerNotNamed`, `sameRole`, `notCompliant`), the judge typed at
the escrow's value (it reads its `role` and `terms`), the leg paid to the peer on `ok`. -/
def escrowTakeBody (theta roles : List Label) (rels : List (Label × RelDecl)) (od sd : RelDecl) : Term :=
  offerTakeTree theta roles (resultTy offerStateTy [escrowCallTy] (editTy rels) 2) (escrowValTy theta roles)
    (escrowTakeDone theta rels od sd)

/-- The withdraw's success (inside the inner `some`: ownVal 0, ownPoint 1, req 2, state 4): pay the
pinned offer's leg back to its `payTo`; retract the offer. -/
def escrowWithdrawDone (rels : List (Label × RelDecl)) (od : RelDecl) : Term :=
  escrowResult rels (escrowPay (.get (.var 2) "self") (.get (.var 0) "payTo") (.get (.var 0) "give"))
    (.var 4) [activityEdit rels "offer" od "retract" (.get (.var 1) "key")]

/-- **The withdraw** (var 0 req, var 1 arg, var 2 state, var 3 rows): retract the pinned own offer
and credit its leg back to its `payTo`. Refusals: `offerUnpinned`, `noOffer`. -/
def escrowWithdrawBody (rels : List (Label × RelDecl)) (od : RelDecl) : Term :=
  let fail (why : String) := Term.refuse (resultTy offerStateTy [escrowCallTy] (editTy rels) 1) why.toUTF8
  -- inside the inner `some`: ownVal 0, ownPoint 1, req 2, arg 3, state 4, rows 5
  .case (.get (.get (.var 3) "offer") "p0") [
    ("none", fail "offerUnpinned"),
    ("some", .case (.get (.var 0) "val") [
      ("none", fail "noOffer"),
      ("some", escrowWithdrawDone rels od)])]

/-- The package, emitted directly, with `Std.offer`'s method names and indices. -/
def offerEscrowPackageOf (theta roles : List Label) (offerLimit sessionLimit budget : Nat) : Package :=
  let rels := escrowRels theta roles offerLimit sessionLimit
  let S := offerStateTy
  let E := editTy rels
  let T := escrowCallTy
  let od := escrowDecl theta roles offerLimit
  let sd := offerSessionDecl theta sessionLimit
  let fields : List (Label × Ty × Term) := [
    ("fuse", methodTy S offerFuseArg [offerCallTy, offerCallTy] (.record []) E 0,
      activityMethod S offerFuseArg (.record []) (offerFuseBody budget)),
    ("offer_guard", guardTy S od, offerGuard theta od),
    ("post", methodTy S (escrowPostArg theta roles) [T] (.record []) E 1,
      activityMethod S (escrowPostArg theta roles) (.record []) (escrowPostBody rels od)),
    ("session_waiting", guardTy S sd, activityWaiting S [offerSettlePlan theta] sd offerResumer),
    ("take", methodTy S (offerTakeArg theta) [T] (offerTakeRows rels) E 2,
      activityMethod S (offerTakeArg theta) (offerTakeRows rels) (escrowTakeBody theta roles rels od sd)),
    ("withdraw", methodTy S (.record []) [T] (escrowWithdrawRows rels) E 1,
      activityMethod S (.record []) (escrowWithdrawRows rels) (escrowWithdrawBody rels od))]
  { imports := [], state := S,
    iface := .record (fields.map fun (l, T, _) => (l, T)),
    body := .record (fields.map fun (l, _, t) => (l, t)),
    methods := offerMethods, laws := [], rels }

/-- **`Std.offer` with a value leg**: the checked escrow package over terms `theta` and roles
`roles` (`Std.offerPackage`'s refusals). -/
def offerEscrowPackage (theta roles : List Label) (offerLimit : Nat := 64) (sessionLimit : Nat := 1024)
    (budget : Nat := 100000) : Except OfferRefusal Package := do
  if roles.length < 2 then throw .tooFewRoles
  if !roles.Nodup then throw .duplicateRole
  if theta.isEmpty then throw .noTerms
  if !theta.Nodup then throw .duplicateTerm
  let pkg := offerEscrowPackageOf theta roles offerLimit sessionLimit budget
  match pkg.checkWith [] with
  | .error why => throw (.package why)
  | .ok () => pure pkg

end Nanodregg.Lang.Std
