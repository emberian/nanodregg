/-
# Spec.Sim.Exchange — the lazy exchange and the deployed exchange runs

The trivial system `Spec.Proofs.Exchange` refuses (`lazyExchange`: the exchange package whose judge
of the legs is `true`, P8j) and the inputs of two runs at the deployed `Ctx` from `wGenesis`: the
founder installs an exchange package, creates objects X and Y of it, issues denominations α and β,
opens four accounts, mints 20 of each to itself, grants X and Y the transfer of their legs, posts X's
offer (buyer [5,10], gives 5 α, wants 7 β) and Y's (seller [8,12], gives `give` β, wants 5 α),
grants X `invoke take` on Y, and signs X's fuse at price 9. `exUnfair` runs it under the lazy
package with Y giving 1 β (X's want unmet); `exFair` under the deployed package with Y giving 7 β.
Tooling (closure C9): what is computed of these is stated in `Spec.Proofs.Exchange`.
-/
import Spec.Sim.Run
import Lang.StdOfferEscrow

namespace Nanodregg.Spec

open Nanodregg.Kernel Nanodregg.Kernel.Receive Nanodregg.Protocol Nanodregg.Codec
open Nanodregg.Lang Nanodregg.Lang.Std

/-! ## The lazy exchange -/

/-- The exchange package with its legs' judge `fair` (`offerEscrowPackageOf`'s fields, the judge a
parameter; at `escrowFairT` it IS the deployed package, `escrowPackageWith_fair`). -/
def escrowPackageWith (fair : Term) (theta roles : List Label) (offerLimit sessionLimit sessionPatience budget : Nat) :
    Package :=
  let rels := escrowRels theta roles offerLimit sessionLimit
  let S := offerStateTy
  let E := editTy rels
  let T := escrowCallTy
  let od := escrowDecl theta roles offerLimit
  let sd := offerSessionDecl theta sessionLimit
  let fields : List (Label × Ty × Term) := [
    ("fuse", methodTy S (offerFuseArg theta) [T, offerCallTy theta] (offerTakeRows rels) E 2,
      activityMethod S (offerFuseArg theta) (offerTakeRows rels)
        (offerTakeTree theta roles (escrowValTy theta roles) (some fair) false (escrowFuseDone theta rels od sd budget))),
    ("offer_guard", guardTy S od, offerGuard theta od),
    ("post", methodTy S (escrowPostArg theta roles) [T] (.record []) E 1,
      activityMethod S (escrowPostArg theta roles) (.record []) (escrowPostBody rels od)),
    ("retire", activityRetireTy S rels sd "session" none, offerRetireBody rels sd),
    ("session_waiting", guardTy S sd, offerSessionGuard theta sd sessionPatience),
    ("take", methodTy S (offerTakeArg theta) [T] (offerTakeRows rels) E 2,
      activityMethod S (offerTakeArg theta) (offerTakeRows rels)
        (offerTakeTree theta roles (escrowValTy theta roles) (some fair) true (escrowTakeDone theta rels od sd))),
    ("withdraw", methodTy S (.record []) [T] (escrowWithdrawRows rels) E 1,
      activityMethod S (.record []) (escrowWithdrawRows rels) (escrowWithdrawBody rels od))]
  { imports := [], state := S,
    iface := .record (fields.map fun (l, T, _) => (l, T)),
    body := .record (fields.map fun (l, _, t) => (l, t)),
    methods := offerMethods, laws := [], rels, effects := escrowEffects }

/-- **The lazy exchange** (P8j): the judge of the legs replaced by `true`; every other check of the
take and the fuse (`offerTakeTree`'s naming, roles, terms, `offerJoint`) stands. -/
def lazyEscrowPackageOf : List Label → List Label → Nat → Nat → Nat → Nat → Package :=
  escrowPackageWith (.bool true)

/-- **The exchange whose judge ignores the legs.** -/
def lazyExchange (d : ByteArray → ByteArray) : System Digest :=
  { deployed d with exchange := lazyEscrowPackageOf }

/-! ## The runs -/

def eTheta : List Label := ["price"]
def eRoles : List Label := ["buyer", "seller"]
def eOd : RelDecl := escrowDecl eTheta eRoles 64

/-- The two packages at the runs' parameters. -/
def eLazy : Package := lazyEscrowPackageOf eTheta eRoles 64 1024 offerSessionPatience 100000
def eFairPkg : Package := offerEscrowPackageOf eTheta eRoles 64 1024 offerSessionPatience 100000

/-- A call of the founder (current key) against `w`, its window end `101 + i` (distinct calls of one
body stay distinct transactions), pinning `pins` and the row slots `rowPins`. -/
def eCall (w : World Digest) (i : Nat) (pins : List Digest) (rowPins : List (RowSlot Digest × Digest))
    (b : Body Digest) : Call Digest :=
  let u : Unsigned Digest :=
    { world := w.origin, member := wMember, key := wKey, notBefore := 0, validUntil := 101 + i,
      pins := (wMember :: pins).map fun c => (c, pinOf Xd.env (w.entry Xd.env c)), maxCharge := 1000000,
      body := b, rowPins }
  ⟨u, Ed25519.sign (wSeed "f0") (Xd.callMessage u)⟩

/-- The first cell a call bears, as the writer stages it. -/
def eIdOf (w : World Digest) (c : Call Digest) : Digest :=
  match submit Xd w c with
  | .ok (t, _) => (createdIds t).headD Digest.zero
  | .error _ => Digest.zero

def eAcct (o a : Digest) : Digest := accountId Xd o a

def ePostArg (n : Nat) (role : Label) (lo hi amount : Nat) (asset grant payTo : Digest) (wamount : Nat)
    (wasset : Digest) : ByteArray :=
  (Wire.encodeData (escrowPostArg eTheta eRoles)
    (.record [("give", .record [("amount", .nat amount), ("asset", .digest asset.bytes)]),
      ("grant", .digest grant.bytes), ("n", .nat n), ("payTo", .digest payTo.bytes),
      ("role", .inj role (.record [])),
      ("terms", .record [("price", .record [("hi", .nat hi), ("lo", .nat lo)])]),
      ("want", .record [("amount", .nat wamount), ("asset", .digest wasset.bytes)])])).getD .empty

def eOfferKey0 : ByteArray := (keyBytes eOd (.record [("n", .nat 0)])).getD .empty

/-- The row pin of `obj`'s offer 0 at `w`. -/
def ePinOffer (w : World Digest) (obj : Digest) : List (RowSlot Digest × Digest) :=
  let s : RowSlot Digest := .row ⟨obj, 0, eOfferKey0⟩
  [(s, rowPin Xd.env (headFloor Xd.env w.rows obj 0) (rowAt Xd.env w.rows s))]

/-- The fuser's deal: X's offer 0 and Y's offer 0, price 9, through Y's invitation `g`. -/
def eDeal (x y g : Digest) : Data :=
  .record [("keys", .record [("a", .nat 0), ("b", .nat 0)]),
    ("pair", .record [("a", .digest x.bytes), ("b", .digest y.bytes)]),
    ("theta", .record [("price", .nat 9)]), ("via", .inj "some" (.digest g.bytes))]

/-- A computed exchange run: its package, objects and invitation, the setup log, the fuse. -/
structure ExRun where
  pkg : Digest
  x : Digest
  y : Digest
  g : Digest
  log : List (Step Digest)
  fuseArg : ByteArray
  fuse : Call Digest

/-- The run under package `P`, Y's offer giving `give` β. -/
def exRun (P : Package) (give : Nat) : ExRun :=
  let c1 := eCall wGenesis 1 [] [] (.install ((Wire.encodePackage P).getD .empty))
  let pkg := eIdOf wGenesis c1
  let (w1, l1) := staged wGenesis c1
  let c2 := eCall w1 2 [pkg] [] (.create (some pkg) [] [])
  let x := eIdOf w1 c2
  let (w2, l2) := staged w1 c2
  let c3 := eCall w2 3 [pkg] [] (.create (some pkg) [] [])
  let y := eIdOf w2 c3
  let (w3, l3) := staged w2 c3
  let c4 := eCall w3 4 [] [] (.issue 100)
  let α := eIdOf w3 c4
  let (w4, l4) := staged w3 c4
  let c5 := eCall w4 5 [] [] (.issue 100)
  let β := eIdOf w4 c5
  let (w5, l5) := staged w4 c5
  let (w6, l6) := staged w5 (eCall w5 6 [α] [] (.account α wMember))
  let (w7, l7) := staged w6 (eCall w6 7 [α] [] (.account α x))
  let (w8, l8) := staged w7 (eCall w7 8 [β] [] (.account β wMember))
  let (w9, l9) := staged w8 (eCall w8 9 [β] [] (.account β y))
  let (w10, l10) := staged w9 (eCall w9 10 [α, eAcct wMember α] [] (.transfer (.well α) (.of wMember α) 20 none none))
  let (w11, l11) := staged w10 (eCall w10 11 [β, eAcct wMember β] [] (.transfer (.well β) (.of wMember β) 20 none none))
  let c12 := eCall w11 12 [x, eAcct wMember α] [] (.grant (eAcct wMember α) x [.transfer 5] none)
  let gA := eIdOf w11 c12
  let (w12, l12) := staged w11 c12
  let c13 := eCall w12 13 [y, eAcct wMember β] [] (.grant (eAcct wMember β) y [.transfer give] none)
  let gB := eIdOf w12 c13
  let (w13, l13) := staged w12 c13
  let (w14, l14) := staged w13 (eCall w13 14 [x, pkg, gA, α, eAcct wMember α, eAcct x α] []
    (.invoke x offerPostIx (ePostArg 0 "buyer" 5 10 5 α gA wMember 7 β) 100000 none))
  let (w15, l15) := staged w14 (eCall w14 15 [y, pkg, gB, β, eAcct wMember β, eAcct y β] []
    (.invoke y offerPostIx (ePostArg 0 "seller" 8 12 give β gB wMember 5 α) 100000 none))
  let c16 := eCall w15 16 [y, x] [] (.grant y x [.invoke offerTakeIx] none)
  let g := eIdOf w15 c16
  let (w16, l16) := staged w15 c16
  let fuseArg := (Wire.encodeData (offerFuseArg eTheta) (eDeal x y g)).getD .empty
  { pkg, x, y, g, fuseArg,
    log := l1 ++ l2 ++ l3 ++ l4 ++ l5 ++ l6 ++ l7 ++ l8 ++ l9 ++ l10 ++ l11 ++ l12 ++ l13 ++ l14 ++ l15 ++ l16,
    fuse := eCall w16 99 [pkg, x, y, g, α, β, eAcct x α, eAcct wMember α, eAcct y β, eAcct wMember β]
      (ePinOffer w16 x ++ ePinOffer w16 y) (.invoke x offerFuseIx fuseArg 1000000 none) }

/-- The unfair run (lazy package, Y gives 1 β where X wants 7 β) and the fair one (deployed package,
Y gives 7 β). -/
def exUnfair : ExRun := exRun eLazy 1
def exFair : ExRun := exRun eFairPkg 7

/-- Whether a result is `ok`, and its value (else `d`): the runs' facts read results through these,
so no proof cases on a concrete run's `match` (each such absurd branch was a kernel timeout). -/
def okB {ε α : Type} : Except ε α → Bool
  | .ok _ => true
  | .error _ => false

def getOk {ε α : Type} (e : Except ε α) (d : α) : α :=
  match e with
  | .ok a => a
  | .error _ => d

/-- The World a run's setup log folds to, the fuse's Turn there, and the World after it. -/
def exW (r : ExRun) : World Digest := getOk (World.fold Xd.env wGenesis r.log) wGenesis
def exT (r : ExRun) : Turn Digest := getOk (receive Xd (exW r) r.fuse) tMint
def exW' (r : ExRun) : World Digest := getOk (World.admit Xd.env (exW r) (exT r)) (exW r)

/-- An object of package `pkg`, live at `w`. -/
def eObjOf (w : World Digest) (pkg o : Digest) : Bool :=
  match w.live Xd.env o with
  | some cl => decide (cl.slots.get slotPackage = some (Xd.env.bytes pkg))
  | none => false

/-- The exchange claim's premises at a run, under package `P`: the setup log folds, the fuse is
derived and admitted, it is X's fuse on `eDeal`, its pinned package is `P`, X and Y are live
objects of it. -/
def exFacts (P : Package) (r : ExRun) : Bool :=
  okB (World.fold Xd.env wGenesis r.log) && okB (receive Xd (exW r) r.fuse) &&
    okB (World.admit Xd.env (exW r) (exT r)) &&
    decide (r.fuse.unsigned.body = .invoke r.x offerFuseIx r.fuseArg 1000000 none) &&
    decide (Wire.encodeData (offerFuseArg eTheta) (eDeal r.x r.y r.g) = some r.fuseArg) &&
    okB (readPackage (pinned Xd.env (exW r) r.fuse.unsigned.pins) r.pkg) &&
    decide (getOk (readPackage (pinned Xd.env (exW r) r.fuse.unsigned.pins) r.pkg) default = P) &&
    eObjOf (exW r) r.pkg r.x && eObjOf (exW r) r.pkg r.y

/-- Whether two offers' legs match (`LegsMatch` as a computation). -/
def legsMatchB (o q : Data) : Bool :=
  match o.field "give", o.field "want", q.field "give", q.field "want" with
  | some (.record [("amount", .nat ga), ("asset", .digest gb)]), some (.record [("amount", .nat wa), ("asset", .digest wb)]),
    some (.record [("amount", .nat qa), ("asset", .digest qb)]), some (.record [("amount", .nat va), ("asset", .digest vb)]) =>
      decide (qb = wb) && decide (wa ≤ qa) && decide (gb = vb) && decide (va ≤ ga)
  | _, _, _, _ => false

/-- Whether a method's rows read two offers whose legs match; `true` on any other shape (only the
two-offer shape can be refuted). -/
def readsFair {E : Type} : Except E Data → Bool
  | .ok (.record [("offer", .record [("p0", .inj "some" (.record [("key", _), ("val", .inj "some" o)]))]),
      ("peer", .record [("offer", .record [("p0", .inj "some" (.record [("key", _), ("val", .inj "some" q)]))])])]) =>
      legsMatchB o q
  | _ => true

/-- What X's fuse reads of the two offers at a run. -/
def exReads (r : ExRun) : Except (Refusal Digest) Data :=
  methodReads Xd.env.bytes Xd.digestOf (Protocol.Foreign.check Codec.Deployed.env Codec.Deployed.digestCodec) (pinned Xd.env (exW r) r.fuse.unsigned.pins) r.pkg
    (escrowRels eTheta eRoles 64 1024) (rowView Xd.env (exW r) r.fuse.unsigned) r.x (eDeal r.x r.y r.g)
    offerRead offerRead

end Nanodregg.Spec
