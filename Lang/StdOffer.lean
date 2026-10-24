/-
# Lang.StdOffer — an object's latent contract as an offer row, and the fuse of two (PROT-6, LANG-77)

An OFFER is a row of the object that makes it: a chooser role and an acceptance box over the deal's
terms θ (a record of naturals; each field a closed interval `lo ≤ θ.f ≤ hi`). Two offers FUSE when
their roles differ and θ is inside both boxes (`offerJoint`). The fuse is Bartoletti's [Fuse] rule
fired by EITHER party (LITP C.1's "a third or either object"; the third-object matcher of fork M
went with LANG-77, which let a method hand its peer a value it computed):

* `take {keys, pair, theta}`, run by a party as itself, reads its own offer and its PEER's (the
  member of `pair` that is not itself: `Lang.peerOf`, the declared peer read), refuses unless its
  own pinned offer is the one the deal NAMES for it (`keys.a` for `pair.a`, `keys.b` for `pair.b`:
  `offerNotNamed`), evaluates `offerJoint` on the two pinned offers and θ, and only on `ok`
  retracts its OWN offer and inserts its own `session` row capturing `{pair, theta}`. A run edits
  only its own object's rows (kernel law 4, `rowParent`), so each party consumes its own offer, and
  the deal, not the caller's pins, says which of its standing offers that is.
* `fuse {keys, pair, theta, via}`, run by a party as itself, IS a take that also invokes its peer's
  `take` on the very deal it judged, `{keys, pair, theta}` of its own argument, through the grant
  `via` the peer's owner gave it. The peer's take decodes the bytes the fuser's run ENCODED of that
  value (`Lang.callsOf`, LANG-77), so the two judges see one θ by construction: no third party
  holds the bytes, and no forwarding is trusted.

Both runs sit inside one call tree, so the Turn seals both retracts or neither (KERNEL-45: the tree
commits or fails whole), and `revisited` keeps a party from calling itself. An owner may still
root-invoke its own `take` with no fuse (a nested call's principal is the grant's issuer, so `take`
cannot tell: READ-PROT-6b condition 2): one session row is not a fuse; the fuse is the two.

A party invites its peer by granting it `[.invoke take]` on its own object; the grant is not spent
(KERNEL-25's `.invoke` is not a counted right), so an offer is consumed once per STANDING ROW: its
retract is what stops a second fuse, and a `post` at the same key afterwards is a new offer. The
session row is an activity log row (`Lang.Std.activityLog`, guarded by `activityWaiting`); this
package has no method that answers it (settlement moves value: PROT-8).
-/
import Lang.StdActivity

namespace Nanodregg.Lang.Std

/-! ## Types -/

/-- The deal's terms: one natural per label, labels ascending. -/
def offerThetaTy (theta : List Label) : Ty := .record (Row.sort (theta.map (·, Ty.nat)))

/-- The terms' labels, ascending (the order the judge and the guard walk them). -/
def offerLabels (theta : List Label) : List Label := (Row.sort (theta.map (·, ()))).map (·.1)

/-- One field's acceptance interval. -/
def offerBoxTy : Ty := .record [("hi", .nat), ("lo", .nat)]

/-- An offer's acceptance box: an interval per term. -/
def offerTermsTy (theta : List Label) : Ty := .record (Row.sort (theta.map (·, offerBoxTy)))

/-- The chooser roles, an enumeration. -/
def offerRoleTy (roles : List Label) : Ty := .sum (Row.sort (roles.map (·, Ty.record [])))

/-- An offer row's value: its chooser role and its box. -/
def offerValTy (theta roles : List Label) : Ty :=
  .record [("role", offerRoleTy roles), ("terms", offerTermsTy theta)]

/-- What a session row captures: the pair the deal names and its terms. -/
def offerCaptureTy (theta : List Label) : Ty := .record [("pair", pairTy), ("theta", offerThetaTy theta)]

/-- The session log's one plan. Its code is never run by this package (no method starts or resumes
it here: the take inserts the row itself); only its capture and response types are read. -/
def offerSettlePlan (theta : List Label) : ActivityPlan where
  name := "settle"
  captured := offerCaptureTy theta
  response := .record []
  precondition := .lam (.record []) (.lam (offerCaptureTy theta) (.lam reqTy (.bool false)))
  start := .lam (.record []) (.lam (offerCaptureTy theta) (.lam reqTy (.var 2)))
  resume := .lam (.record []) (.lam (offerCaptureTy theta) (.lam (.record []) (.lam reqTy (.var 3))))

/-- The object state: none; an object of this package holds its offers and sessions as rows. -/
def offerStateTy : Ty := .record []

/-- The method labels, ascending; a method's index is its position (`Package.methods`). -/
def offerMethods : List Label := ["fuse", "post", "take", "withdraw"]

def offerFuseIx : Nat := 0
def offerPostIx : Nat := 1
def offerTakeIx : Nat := 2
def offerWithdrawIx : Nat := 3

/-! ## The judge: one generated term -/

/-- `θ` is inside box `terms`, field by field (`fs` the labels). -/
def offerInBox : List Label → Term → Term → Term
  | [], _, _ => .bool true
  | f :: fs, terms, th =>
      andT (andT (.prim .le (.get (.get terms f) "lo") (.get th f))
          (.prim .le (.get th f) (.get (.get terms f) "hi")))
        (offerInBox fs terms th)

/-- Every interval of `terms` is non-empty (`lo ≤ hi`). -/
def offerTermsOk : List Label → Term → Term
  | [], _ => .bool true
  | f :: fs, terms => andT (.prim .le (.get (.get terms f) "lo") (.get (.get terms f) "hi")) (offerTermsOk fs terms)

/-- **The joint judge** `λ o q θ` over offer values of type `V` (any record with a `role` and a
`terms` field: `offerValTy`, or the escrow's value with its leg): `refused "sameRole"` when the two
chooser roles are equal, `refused "notCompliant"` unless θ is inside both boxes, else `ok`. Each
`take` evaluates it on its own offer, its peer's, and the θ it decoded. -/
def offerJoint (theta roles : List Label) (V : Ty) : Term :=
  let fs := offerLabels theta
  .lam V (.lam V (.lam (offerThetaTy theta)
    (.ite (eqData (offerRoleTy roles) (.get (.var 2) "role") (.get (.var 1) "role"))
      (refusedT "sameRole")
      (.ite (andT (offerInBox fs (.get (.var 2) "terms") (.var 0)) (offerInBox fs (.get (.var 1) "terms") (.var 0)))
        okT (refusedT "notCompliant")))))

/-! ## Relations and guards -/

def offerKey : List (Label × Ty) := [("n", .nat)]

def offerDecl (theta roles : List Label) (limit : Nat) : RelDecl :=
  ⟨offerKey, offerValTy theta roles, limit, none, 0, true, some "offer_guard"⟩

def offerSessionDecl (theta : List Label) (limit : Nat) : RelDecl :=
  activityLog [offerSettlePlan theta] limit "session_waiting"

def offerRels (theta roles : List Label) (offerLimit sessionLimit : Nat) : List (Label × RelDecl) :=
  [("offer", offerDecl theta roles offerLimit), ("session", offerSessionDecl theta sessionLimit)]

/-- The offer row's guard: an insert's box is well formed (`badTerms`); a retract is the run of
`fuse`, `take` or `withdraw` (`notConsumer`); an offer is never rewritten in place (`final`). -/
def offerGuard (theta : List Label) (d : RelDecl) : Term :=
  let fs := offerLabels theta
  -- inside the retract arm: var 0 the retracted key, var 1 the input, var 2 the request
  let consumer : Term := .case (.get (.var 2) "occasion") [
    ("adopt", refusedT "notConsumer"), ("birth", refusedT "notConsumer"),
    ("invoke", .ite (.prim .eq (.var 0) (.nat offerTakeIx)) okT
      (.ite (.prim .eq (.var 0) (.nat offerWithdrawIx)) okT
        (.ite (.prim .eq (.var 0) (.nat offerFuseIx)) okT (refusedT "notConsumer")))),
    ("relaw", refusedT "notConsumer"), ("write", refusedT "notConsumer")]
  .lam offerStateTy (.lam reqTy (.lam (guardInTy d) (.case (.get (.var 0) "edit") [
    ("insert", guard (offerTermsOk fs (.get (.get (.var 0) "val") "terms")) "badTerms" okT),
    ("retract", consumer),
    ("upsert", refusedT "final")])))

/-- The session log's resumer: nobody, in this package (no method answers a session row here). -/
def offerResumer : Term := .lam offerStateTy (.lam reqTy (.bool false))

/-! ## Methods -/

/-- The offer each party's take consumes, by its key `n`: `a` names `pair.a`'s, `b` names `pair.b`'s. -/
def offerKeysTy : Ty := .record [("a", .nat), ("b", .nat)]

/-- The deal: the offer each side consumes (`keys`), the pair, and the terms. -/
def offerTakeArg (theta : List Label) : Ty :=
  .record [("keys", offerKeysTy), ("pair", pairTy), ("theta", offerThetaTy theta)]

/-- The key `n` the deal `arg` names for the object `req.self`: `keys.a` when `self` is `pair.a`,
else `keys.b` (the run's peer read already refused a `self` that is neither: `peer: notParty`). -/
def offerNamedT (req arg : Term) : Term :=
  .ite (.prim .deq (.get req "self") (.get (.get arg "pair") "a"))
    (.get (.get arg "keys") "a") (.get (.get arg "keys") "b")

/-- The own pinned point's key is the one the deal names for `self`. -/
def offerNamedOkT (point req arg : Term) : Term :=
  .prim .eq (.get (.get point "key") "n") (offerNamedT req arg)

def offerRead : List (Label × RelRead) := [("offer", ⟨1, none, false, false⟩)]

/-- `take`'s rows argument: its own offer point and its peer's. -/
def offerTakeRows (rels : List (Label × RelDecl)) : Ty := rowsTy rels offerRead offerRead

/-- The fuse's argument: the deal (the take's argument, field for field) and the grant `via`
through which the fuser invokes its peer's `take`. -/
def offerFuseArg (theta : List Label) : Ty :=
  .record [("keys", offerKeysTy), ("pair", pairTy), ("theta", offerThetaTy theta), ("via", optTy .digest)]

def offerPostArg (theta roles : List Label) : Ty :=
  .record [("n", .nat), ("role", offerRoleTy roles), ("terms", offerTermsTy theta)]

def offerWithdrawArg : Ty := .record [("n", .nat)]

/-- A fuse's one call kind: an invoke of `take`, its argument a value of `offerTakeArg theta`. -/
def offerCallTy (theta : List Label) : Ty := invokeOf (offerTakeArg theta)

/-- `invoke obj take deal budget via`. -/
def offerTakeCall (theta : List Label) (budget : Nat) (obj via deal : Term) : Term :=
  .inj (offerCallTy theta) "invoke" (.record [("args", deal), ("budget", .nat budget),
    ("method", .nat offerTakeIx), ("obj", obj), ("via", via)])

/-- The other member of the argument's `pair`: `b` when `req.self` is `a`, else `a` (the run's peer
read already refused a `self` that is neither: `peer: notParty`). -/
def offerPeerT (req arg : Term) : Term :=
  .ite (.prim .deq (.get req "self") (.get (.get arg "pair") "a"))
    (.get (.get arg "pair") "b") (.get (.get arg "pair") "a")

/-- **The fuser's call**: its peer's `take` on the deal it judged, `{keys, pair, theta}` of its own
argument as a VALUE (the runtime encodes it, LANG-77), through `arg.via`. -/
def offerFuseCall (theta : List Label) (budget : Nat) (req arg : Term) : Term :=
  offerTakeCall theta budget (offerPeerT req arg) (.get arg "via")
    (.record [("keys", .get arg "keys"), ("pair", .get arg "pair"), ("theta", .get arg "theta")])

/-- The take's two row edits on `ok`: retract its own pinned offer, insert its session row capturing
`{pair, theta}` (inside the verdict's `ok` arm: its payload 0, peerVal 1, peerPoint 2, ownVal 3,
ownPoint 4, req 5, arg 6, state 7, rows 8). Shared by `Std.offer` and its escrow instance. -/
def offerTakeEdits (theta : List Label) (rels : List (Label × RelDecl)) (od sd : RelDecl) : List Term :=
  let C := activityCaptured [offerSettlePlan theta]
  let R := activityResponses [offerSettlePlan theta]
  [activityEdit rels "offer" od "retract" (.get (.var 4) "key"),
    activityEdit rels "session" sd "insert"
      (activityKeyTerm (.get (.var 5) "agent") (.get (.var 5) "notBefore"))
      (.record [("answered", noCallT R),
        ("captured", .inj C "settle" (.record [("pair", .get (.var 6) "pair"), ("theta", .get (.var 6) "theta")]))])]

/-- **The take's case tree** (var 0 req, var 1 arg, var 2 state, var 3 rows), shared by `Std.offer`
and its escrow instance: `V` is the offer value type the judge is typed at, `done` the term of the
verdict's `ok` arm, `R` the result type a refusal is typed at. Refusals, in order: its own offer slot
unpinned (`offerUnpinned`) or pinned absent (`noOffer`); the peer's offer slot unpinned
(`peerRowUnpinned`) or pinned absent (`noPeerOffer`); its own pinned offer is not the one the deal
names for it (`offerNotNamed`); the judge's `sameRole` / `notCompliant`. -/
def offerTakeTree (theta roles : List Label) (R V : Ty) (done : Term) : Term :=
  let fail (why : String) := Term.refuse R why.toUTF8
  .case (.get (.get (.var 3) "offer") "p0") [
    ("none", fail "offerUnpinned"),
    ("some", .case (.get (.var 0) "val") [
      ("none", fail "noOffer"),
      ("some", .case (.get (.get (.get (.var 5) "peer") "offer") "p0") [
        ("none", fail "peerRowUnpinned"),
        ("some", .case (.get (.var 0) "val") [
          ("none", fail "noPeerOffer"),
          -- peerVal 0, peerPoint 1, ownVal 2, ownPoint 3, req 4, arg 5
          ("some", .ite (offerNamedOkT (.var 3) (.var 4) (.var 5))
            (.case (activityApply (offerJoint theta roles V) [.var 2, .var 0, .get (.var 5) "theta"]) [
              ("ok", done),
              ("refused", .ite (.prim .beq (.var 0) (.bytes "sameRole".toUTF8))
                (fail "sameRole") (fail "notCompliant"))])
            (fail "offerNotNamed"))])])])]

/-- The take's success: its two edits, no call. -/
def offerTakeDone (theta : List Label) (rels : List (Label × RelDecl)) (od sd : RelDecl) : Term :=
  activityResult rels (.var 7) (offerTakeEdits theta rels od sd)

/-- **The take**: the shared tree over `Std.offer`'s values. -/
def offerTakeBody (theta roles : List Label) (rels : List (Label × RelDecl)) (od sd : RelDecl) : Term :=
  offerTakeTree theta roles (resultTy offerStateTy [] (editTy rels) 2) (offerValTy theta roles)
    (offerTakeDone theta rels od sd)

/-- The fuse's success (inside the verdict's `ok` arm: req 5, arg 6, state 7): the take's two edits
and the one call to the peer's `take`. Shared by `Std.offer` and its escrow instance's shape. -/
def offerFuseDone (theta : List Label) (rels : List (Label × RelDecl)) (od sd : RelDecl) (budget : Nat) : Term :=
  activityResultCalls rels (callsT [someCallT (offerCallTy theta) (offerFuseCall theta budget (.var 5) (.var 6))])
    (.var 7) (offerTakeEdits theta rels od sd)

/-- **The fuse**: the take's tree, its success also invoking the peer's `take` on the judged deal. -/
def offerFuseBody (theta roles : List Label) (rels : List (Label × RelDecl)) (od sd : RelDecl) (budget : Nat) : Term :=
  offerTakeTree theta roles (resultTy offerStateTy [offerCallTy theta] (editTy rels) 2) (offerValTy theta roles)
    (offerFuseDone theta rels od sd budget)

def offerPostBody (rels : List (Label × RelDecl)) (od : RelDecl) : Term :=
  activityResult rels (.var 2) [activityEdit rels "offer" od "insert"
    (.record [("n", .get (.var 1) "n")])
    (.record [("role", .get (.var 1) "role"), ("terms", .get (.var 1) "terms")])]

def offerWithdrawBody (rels : List (Label × RelDecl)) (od : RelDecl) : Term :=
  activityResult rels (.var 2) [activityEdit rels "offer" od "retract" (.record [("n", .get (.var 1) "n")])]

/-- The package, emitted directly (no `activityPackage`: it would add `start_settle`, a method that
inserts a session row without a take). `fuse` and `take` read the same rows (own offer, peer's offer)
and take the same deal; `fuse` also takes `via` and makes the one call. -/
def offerPackageOf (theta roles : List Label) (offerLimit sessionLimit budget : Nat) : Package :=
  let rels := offerRels theta roles offerLimit sessionLimit
  let S := offerStateTy
  let E := editTy rels
  let od := offerDecl theta roles offerLimit
  let sd := offerSessionDecl theta sessionLimit
  let fields : List (Label × Ty × Term) := [
    ("fuse", methodTy S (offerFuseArg theta) [offerCallTy theta] (offerTakeRows rels) E 2,
      activityMethod S (offerFuseArg theta) (offerTakeRows rels) (offerFuseBody theta roles rels od sd budget)),
    ("offer_guard", guardTy S od, offerGuard theta od),
    ("post", methodTy S (offerPostArg theta roles) [] (.record []) E 1,
      activityMethod S (offerPostArg theta roles) (.record []) (offerPostBody rels od)),
    ("session_waiting", guardTy S sd, activityWaiting S [offerSettlePlan theta] sd offerResumer),
    ("take", methodTy S (offerTakeArg theta) [] (offerTakeRows rels) E 2,
      activityMethod S (offerTakeArg theta) (offerTakeRows rels) (offerTakeBody theta roles rels od sd)),
    ("withdraw", methodTy S offerWithdrawArg [] (.record []) E 1,
      activityMethod S offerWithdrawArg (.record []) (offerWithdrawBody rels od))]
  { imports := [], state := S,
    iface := .record (fields.map fun (l, T, _) => (l, T)),
    body := .record (fields.map fun (l, _, t) => (l, t)),
    methods := offerMethods, laws := [], rels }

/-- Why the generator refuses its parameters (law 7). -/
inductive OfferRefusal
  /-- fewer than two chooser roles: no two offers could fuse -/
  | tooFewRoles
  | duplicateRole
  /-- no terms: every pair of boxes would agree on the one empty θ -/
  | noTerms
  | duplicateTerm
  | package (why : CheckError)

def OfferRefusal.name : OfferRefusal → String
  | .tooFewRoles => "tooFewRoles" | .duplicateRole => "duplicateRole"
  | .noTerms => "noTerms" | .duplicateTerm => "duplicateTerm"
  | .package why => why.text

/-- **`Std.offer`**: the checked package over terms `theta` and chooser roles `roles`. -/
def offerPackage (theta roles : List Label) (offerLimit : Nat := 64) (sessionLimit : Nat := 1024)
    (budget : Nat := 100000) : Except OfferRefusal Package := do
  if roles.length < 2 then throw .tooFewRoles
  if !roles.Nodup then throw .duplicateRole
  if theta.isEmpty then throw .noTerms
  if !theta.Nodup then throw .duplicateTerm
  let pkg := offerPackageOf theta roles offerLimit sessionLimit budget
  match pkg.checkWith [] with
  | .error why => throw (.package why)
  | .ok () => pure pkg

end Nanodregg.Lang.Std
