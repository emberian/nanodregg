/-
# Lang.Package — a package: a checked core term with its interface, state type, methods and laws

A package is what `install` puts in a ROM cell (DECISIONS LANG-5, LANG-9): its imports (the ids of
installed packages; `ref i` in the body is the `i`-th), its object STATE type, its INTERFACE type
(the type of `body`), and which interface fields are METHODS (`State → Args → Req → State`) and
which are LAWS (`State → State → Req → Verdict`). `checkWith ifaces p` is the whole install check,
given the imports' interfaces; the package's id is KERNEL's `romIdOf` of its cell, so it commits to
the import ids and through them to the whole closure.
-/
import Lang.Wire
import Lang.Check
import Lang.HoleWire
import Lang.Claim

namespace Nanodregg.Lang

/-- A relation an object of the package holds (LANG-49, LANG-44 as ruled): keyed, bounded rows
under the object, in the World's rows trie. A relation is a PLACE, never a value: no term has a
relation type, so no method holds a whole relation (law 5). Its key is fixed-width data, its
fields in DECLARED order (the key's bytes are the fields' data encodings in that order, so a
range's prefix is the first fields; the method sees the key as a record, labels ascending). -/
structure RelDecl where
  key : List (Label × Ty)
  val : Ty
  /-- at most this many rows (`relationFull`, kernel-checked on the current head) -/
  limit : Nat
  /-- the nat field of `val` the head sums (`relationCapped` past `cap`); none: no sum column -/
  sum : Option Label
  cap : Nat
  /-- rows may be retracted; `false`: insert-only by declaration (`retractForbidden`) -/
  retract : Bool
  /-- an interface field judging each edit, `fn S (fn reqTy (fn editTy verdictTy))` -/
  guard : Option Label
  /-- the field of `val` that is a LEG (`legTy`) the object holds for the row (LANG-90): a run that
  inserts such a row must move the leg's value into the object, a run that retracts it must move it out
  (`checkLegs`, `legUnfunded`/`legStranded`); none: the rows hold no value -/
  holds : Option Label := none
  deriving Inhabited, DecidableEq

/-- A method's GRADES (LANG-89): the quantities its row of effects is bounded by. The ROW (which call
kinds, which relations, which reads) is in the method's TYPE; the grade sits beside it, by the method's
label, because `Ty` carries no quantities (LANG-3). A method with no entry has the zero grade. -/
structure Effect where
  /-- the most one run may MOVE: the sum of `amount` over the `transfer` and `credit` calls it returns
  (`Lang.movesOf`); install refuses `effectExceeded` a value-moving arm under a grade of 0, the run
  refuses `effectExceeded` by name past it (`Lang.checkMoves`) -/
  moves : Nat := 0
  deriving Inhabited, DecidableEq, Repr

structure Package where
  /-- ids of installed packages, as the digest bytes the kernel uses -/
  imports : List ByteArray
  state : Ty
  iface : Ty
  body : Term
  methods : List Label
  laws : List Label
  /-- its relations, labels ascending; relation `i` is the `i`-th (LANG-49) -/
  rels : List (Label × RelDecl) := []
  /-- what the package says of itself, one line (LANG-60): `Bounds.docOk` bytes, printed as `(doc "…")`
  and on `read OBJ ?`'s `doc` line; never run, never judged -/
  doc : ByteArray := .empty
  /-- Live contextual declarations and candidate syntax committed by the ROM id. -/
  holes : List HoleROM := []
  /-- each method's grades (LANG-89), labels ascending, each a method's; absent: the zero grade -/
  effects : List (Label × Effect) := []
  /-- What the package claims of itself (LANG-93, `Lang.Claim`): sentences install refuses unless the
  body bears them (`checkClaims`), carried in the package's identity: a package cannot gain or lose a
  claim without becoming another package. -/
  claims : List Claim := []
  deriving Inhabited, DecidableEq

/-- Method `ℓ`'s grades: its entry, or the zero grade. -/
def Package.effectOf (p : Package) (ℓ : Label) : Effect := (Row.find? ℓ p.effects).getD {}

/-- Which act is judged (KERNEL's `Occasion`): a birth (the seed is `old = new`), a write, a law
replacement by the listed law ids (their digest bytes concatenated in order; the state is unchanged),
an invoke of method `i`, or a retirement (the object's end, judged over its last state, `old = new`;
a law that refuses it makes the object permanent). A law cases on it; the checker requires one arm per label, so a law
written with `case` has no default arm. -/
def occasionTy : Ty :=
  .sum [("adopt", .bytes), ("birth", .record []), ("invoke", .nat), ("relaw", .bytes),
    ("retire", .record []), ("write", .record [])]

/-- An optional `T`. -/
def optTy (T : Ty) : Ty := .sum [("none", .record []), ("some", T)]

/-- What a law and a method see of the call: the signing member, whose authority it uses, the
object judged or run on (`self`: a method names its own accounts by it, LANG-25), the call's
signed window (the Turn lands at a height in `[notBefore, validUntil]`, KERNEL-10), and the act
being judged. -/
def reqTy : Ty :=
  .record [("agent", .digest), ("caller", optTy .digest), ("notBefore", .nat), ("occasion", occasionTy),
    ("principal", .digest), ("self", .digest), ("validUntil", .nat)]

/-- A law's verdict: `ok`, or `refused` with the author's reason. -/
def verdictTy : Ty := .sum [("ok", .record []), ("refused", .bytes)]

def lawTy (S : Ty) : Ty := .fn S (.fn S (.fn reqTy verdictTy))

/-! ## Calls: what a method asks the kernel to do as the object (LANG-23, LANG-33)

The core has no lists, so a method returns its calls in a row of option SLOTS `c0 … c(k-1)`,
`k ≤ Kernel.Bounds.callsMax`. Each slot's type names the kinds of call it may carry: options over
a sub-sum of `callTy`, every arm at exactly its `callTy` type. `callTy` has one arm per kind an
object may exercise (KERNEL's `Body.callable`: account, credit, grant, install, invoke, transfer), its fields
the `Body` constructor's: a digest is `digest`, an `Option` is `optTy`, an `AcctRef` is
`acctRefTy`, a grant's rights the fixed-arity `rightsTy`. So a method's type says how many calls
it may make and of which kinds, and costs bytes only for those: a method that makes none has
`calls : rec {}`. `Lang.Call` reads the kernel's `Body` back out of such data. -/


/-- How a call names a value account (KERNEL's `AcctRef`): a well by its denomination, any other
account by its owner and denomination. -/
def acctRefTy : Ty := .sum [("of", .record [("asset", .digest), ("owner", .digest)]), ("well", .digest)]

/-- A right a granted call carries (KERNEL's `Right`). -/
def rightTy : Ty := .sum [("credit", .nat), ("enroll", .nat), ("invoke", .nat), ("mutate", .record []),
  ("observe", .record []), ("transfer", .nat)]

/-- The rights one granted call may carry. KERNEL's `Right` has six constructors, but a grant carries
at most one COUNTED kind (`enroll`, `transfer`, `credit`: KERNEL-60's `rightTarget` refuses two), so
four slots hold `observe`, `mutate`, an `invoke` and the one counted right; a grant naming one twice
says nothing more. -/
def rightsMax : Nat := 4

/-- The slot labels `r0 …` of `rightsTy` and `c0 …` of a calls row, in slot order. -/
def slotLabels (c : String) (n : Nat) : List Label := (List.range n).map fun i => c ++ toString i

def rightLabels : List Label := slotLabels "r" rightsMax

def rightsTy : Ty := .record (rightLabels.map fun l => (l, optTy rightTy))

/-! ### The call arms (LANG-23, LANG-77)

One arm per callable kind. The `invoke` arm is TYPED: its `args` is a VALUE of the slot's declared
argument type `A`, which the runtime encodes with the one data codec (`Wire.encodeData A`, the codec
the callee's `runSetupWith` inverts at its own argument type) when it reads the method's calls
(`Lang.callsOf`). So a method composes a nested call from values it computed, and its type says
what it sends. Before LANG-77 `args` was `bytes` and a method could only forward bytes it held
(LANG-23 (iii)). -/

def accountArm : Label × Ty := ("account", .record [("asset", .digest), ("owner", .digest)])
def creditArm : Label × Ty :=
  ("credit", .record [("acct", acctRefTy), ("amount", .nat), ("via", optTy .digest), ("well", .digest)])
def grantArm : Label × Ty :=
  ("grant", .record [("grantee", .digest), ("parent", optTy .digest), ("rights", rightsTy), ("target", .digest)])
def transferArm : Label × Ty :=
  ("transfer", .record [("amount", .nat), ("dst", acctRefTy), ("once", optTy .bytes), ("src", acctRefTy),
    ("via", optTy .digest)])
/-- `install`: the object installs the package these bytes encode (LANG-86, KERNEL-75: a generator).
The kernel checks the bytes exactly as a member's `install` (`checkInstall` at the signer's pins) and
bears the ROM cell `romIdOf`; a `bytes` value holds at most `Bounds.bytesMax`, so a package an object
installs is at most that long. -/
def installArm : Label × Ty := ("install", .record [("pkg", .bytes)])

/-- The `invoke` arm's record at argument type `A`. -/
def invokeArm (A : Ty) : Ty :=
  .record [("args", A), ("budget", .nat), ("method", .nat), ("obj", .digest), ("via", optTy .digest)]

/-- The `createOf` arm's record at state type `T` (LANG-96, KERNEL-77): the package bytes and the new
object's state, a VALUE of `T` (the record type the package's state is), which the runtime lays out
as the object's state slots with the one data codec (`Lang.stateSlots`, as a birth's seed is). The
kernel installs the bytes when the signer's view holds no cell at their content id, and bears an
object of that package owned by the SIGNER: a generator that generates and instantiates in one
Turn. An object's `createOf` names no extra laws (the package's own laws judge the object; a
generator writes its laws into the package). -/
def createOfArm (T : Ty) : Ty := .record [("pkg", .bytes), ("state", T)]

/-- The arms a call slot may hold, in canonical order: with an `invoke` arm at argument type `A`
(`some A`) or without one (`none`), and with a `createOf` arm at state type `T` (`some T`) or
without one (`none`). -/
def callArms (A : Option Ty) (T : Option Ty := none) : List (Label × Ty) :=
  match A, T with
  | some A, none => [accountArm, creditArm, grantArm, installArm, ("invoke", invokeArm A), transferArm]
  | none, none => [accountArm, creditArm, grantArm, installArm, transferArm]
  | some A, some T => [accountArm, ("createOf", createOfArm T), creditArm, grantArm, installArm,
      ("invoke", invokeArm A), transferArm]
  | none, some T => [accountArm, ("createOf", createOfArm T), creditArm, grantArm, installArm, transferArm]

/-- Any call an object may make, its invokes (if `A` names an argument type) carrying a value of `A`,
its `createOf`s (if `T` names a state type) a value of `T`. -/
def callTy (A : Option Ty) (T : Option Ty := none) : Ty := .sum (callArms A T)

/-- A slot of `kinds` other than `invoke`, in canonical order. `invoke` is not an arm here: a slot
that names only it is empty, and install refuses it `badMethod` (`callSlotOk`). -/
def callOf (kinds : List Label) : Ty := .sum ((callArms none).filter fun a => kinds.contains a.1)

/-- A slot that may invoke with an argument of type `A`, and may make the other `kinds`. -/
def invokeOf (A : Ty) (kinds : List Label := []) : Ty :=
  .sum ((callArms (some A)).filter fun a => a.1 == "invoke" || kinds.contains a.1)

/-- A slot that may `createOf` an object of state type `T`, and may make the other `kinds`
(`invoke` is not among them, as in `callOf`). -/
def createOfSlot (T : Ty) (kinds : List Label := []) : Ty :=
  .sum ((callArms none (some T)).filter fun a => a.1 == "createOf" || kinds.contains a.1)

/-- The state type of a `createOf` arm's record, if it has the arm's shape. -/
def createOfStateOf : Ty → Option Ty
  | .record [("pkg", .bytes), ("state", T)] => some T
  | _ => none

/-- The state type of a slot's `createOf` arm, if the slot has one of the arm's shape. -/
def slotCreateState : Ty → Option Ty
  | .sum arms => (Row.find? "createOf" arms).bind createOfStateOf
  | _ => none

/-- The argument type of an `invoke` arm's record, if it has the arm's shape. -/
def invokeArgOf : Ty → Option Ty
  | .record [("args", A), ("budget", .nat), ("method", .nat), ("obj", .digest), ("via", V)] =>
    if V = optTy .digest then some A else none
  | _ => none

/-- The argument type of a slot's `invoke` arm, if the slot has one of the arm's shape. -/
def slotInvokeArg : Ty → Option Ty
  | .sum arms => (Row.find? "invoke" arms).bind invokeArgOf
  | _ => none

/-- The calls row over slot call types `ks`: slot `ci` is `optTy (ks[i])`. -/
def callsTy (ks : List Ty) : Ty := .record ((slotLabels "c" ks.length).zip (ks.map optTy))

/-! ## Relations: what a method reads and edits (LANG-49)

A method's reads and edits are fixed-arity data, like its calls (LANG-23). It reads ROWS as its
first argument `R`: a record over the relations it reads (labels ascending), each a record of
point slots `p0 … p(n-1)` (the caller's row pins under that relation, in pin order: a key and the
row's value if present) and, when it declares one, a `range`: the signed prefix as the key's first
fields and slots `r0 … r(k-1)` holding the rows under it in key order. It returns its EDITS in
slots `e0 … e(m-1)` beside its calls, each an option over the package's one edit type. -/

/-- At most this many relations per package, point reads per relation, rows per range, edits per
method, fields per key. Each is ≤ 10, so the slot labels `p0 …`, `r0 …`, `e0 …` ascend. -/
def relsMax : Nat := 8
def pointsMax : Nat := 8
def rangeRowsMax : Nat := 8
def editsMax : Nat := 8
def keyFieldsMax : Nat := 8

/-- The key as a method sees it: a record over the key's fields, labels ascending. -/
def keyTy (d : RelDecl) : Ty := .record (Row.sort d.key)

/-- A range's prefix as a method sees it: the key's first `m` declared fields. -/
def preTy (d : RelDecl) (m : Nat) : Ty := .record (Row.sort (d.key.take m))

/-- What a receipt read shows of a foreign World's committed call (E5): the height it committed at,
its turn digest and its transaction id, as `Protocol.Foreign.check` verified them against the head
object the point's key names. -/
def seenTy : Ty := .record [("height", .nat), ("turn", .digest), ("tx", .digest)]

/-- A row: its key and its value. -/
def rowTy (d : RelDecl) : Ty := .record [("key", keyTy d), ("val", d.val)]

/-- A listed row of a range read: its key, its columns, and its value. The columns are a point's
(`pointRecTy`): on a live read (E1) its key's cell liveness, on a receipt read (E5) the receipt's
column, in label order (CLIENT-35: a range row of a live read carries `live` as a point does). -/
def rangeRowTy (d : RelDecl) (live receipt : Bool) : Ty :=
  .record ([("key", keyTy d)] ++ (if live then [("live", .bool)] else []) ++
    (if receipt then [("receipt", seenTy)] else []) ++ [("val", d.val)])

/-- A point read: the key the caller pinned, and the row's value if the row is there. -/
def pointTy (d : RelDecl) : Ty := optTy (.record [("key", keyTy d), ("val", optTy d.val)])

/-- One relation's edits: an insert (an unpinned birth at a free key), an upsert of a pinned row,
and, only where the relation allows it, a retract of a pinned row. -/
def relEditTy (d : RelDecl) : Ty :=
  .sum ([("insert", rowTy d)] ++ (if d.retract then [("retract", .record [("key", keyTy d)])] else []) ++
    [("upsert", rowTy d)])

/-- The package's one edit type: a relation's label, then that relation's edit. -/
def editTy (rels : List (Label × RelDecl)) : Ty := .sum (rels.map fun r => (r.1, relEditTy r.2))

/-- The edits row over `m` slots. -/
def editsTy (rels : List (Label × RelDecl)) (m : Nat) : Ty :=
  .record ((slotLabels "e" m).map fun l => (l, optTy (editTy rels)))


/-- A read point's record: its key, its key's cell liveness on a live read (E1), and the row's
value if the row is there. `optTy (pointRecTy d false)` is `pointTy d`. -/
def pointRecTy (d : RelDecl) (live : Bool) (receipt : Bool := false) : Ty :=
  .record ([("key", keyTy d)] ++ (if live then [("live", .bool)] else []) ++
    (if receipt then [("receipt", seenTy)] else []) ++ [("val", optTy d.val)])

/-- A relation whose key is exactly one digest field: its rows are keyed by a kernel cell id, so a
method may read each point with the cell's liveness (`livePointTy`, E1). -/
def RelDecl.cellKeyed (d : RelDecl) : Bool :=
  match d.key with
  | [(_, .digest)] => true
  | _ => false

/-- A point read of a cell-keyed relation with its key's kernel cell (E1, LANG-75.1): the key the
caller pinned, whether the cell that key names is LIVE in the caller's pinned view (the runtime
fills it from `Pinned`; no method writes it, and no edit type names it), and the row's value if
the row is there. -/
def livePointTy (d : RelDecl) : Ty := optTy (pointRecTy d true)

/-- What a method declares it reads of one relation: `points` point slots, and a range over the
key's first `pre` fields with `rows` slots, if any; `live`: the points carry their key's cell
liveness (a cell-keyed relation only). -/
structure RelRead where
  points : Nat
  range : Option (Nat × Nat)
  live : Bool
  /-- E5: each point carries the method argument `receipt` checked against the head object its key
  names (`seenTy`); a cell-keyed relation only, and the argument type has `receipt : bytes` -/
  receipt : Bool := false
  deriving DecidableEq, Repr

/-- The rows a method reads of relation `d`, as the record it receives. -/
def relReadTy (d : RelDecl) (x : RelRead) : Ty :=
  .record ((slotLabels "p" x.points).map (fun l => (l, optTy (pointRecTy d x.live x.receipt))) ++
    match x.range with
    | none => []
    | some (m, k) => [("range", .record [("pre", preTy d m),
        ("rows", .record ((slotLabels "r" k).map fun l => (l, optTy (rangeRowTy d x.live x.receipt))))])])

/-- A method's rows argument: the relations it reads (by label, ascending). -/
def readsTy (rels : List (Label × RelDecl)) (rs : List (Label × RelRead)) : Ty :=
  .record (rs.filterMap fun r => (Row.find? r.1 rels).map fun d => (r.1, relReadTy d r.2))

/-- What a method returns over state `S` with call slots `ks` and `es` edit slots of the edit
type `E`: the calls it makes as the object, its row edits, and the new state. -/
def resultTy (S : Ty) (ks : List Ty := []) (E : Ty := .sum []) (es : Nat := 0) : Ty :=
  .record [("calls", callsTy ks), ("edits", .record ((slotLabels "e" es).map fun l => (l, optTy E))),
    ("state", S)]

/-- A method's type: its rows argument `R` (`rec {}`: it reads none), then the state, its argument
type `A` and the request; it returns `resultTy S ks E es` (LANG-49: rows first, so a body's state,
argument and request keep their indices). -/
def methodTy (S A : Ty) (ks : List Ty := []) (R : Ty := .record []) (E : Ty := .sum []) (es : Nat := 0) : Ty :=
  .fn R (.fn S (.fn A (.fn reqTy (resultTy S ks E es))))

/-- An `invoke` arm's argument type is first-order data the wire can carry: `isData` as `methodSig`
asks of the method's own argument, `Wire.dataTy` (`wf && tyWire`) as `encodeData`/`decodeData`
refuse without. The theorems about a checked run take `callSlotOk` alone and get the encoder's
totality from it (`Lang.Proofs.CallLive`). -/
def invokeArgOk (A : Ty) : Bool := A.isData && Wire.dataTy A

/-- A `createOf` arm's state type is a record of first-order data the wire carries field by field,
so `stateSlots` lays out every value of it (LANG-96): what a birth's seed is. -/
def createStateOk : Ty → Bool
  | t@(.record row) => invokeArgOk t && row.all fun f => Wire.dataTy f.2
  | _ => false

/-- A slot's call type: a sum of at least one of the call arms (an empty sum would be a slot that
can never hold a call), each at its own type, the `invoke` arm at an argument type the wire can
carry (`invokeArgOk`), the `createOf` arm at a state type it can lay out (`createStateOk`). -/
def callSlotOk : Ty → Bool
  | .sum arms =>
    let A := (Row.find? "invoke" arms).bind invokeArgOf
    let T := (Row.find? "createOf" arms).bind createOfStateOf
    !arms.isEmpty && A.all invokeArgOk && T.all createStateOk &&
      arms.all fun a => decide (Row.find? a.1 (callArms A T) = some a.2)
  | _ => false

/-- A slot type's call type: the slot is an option over a call type. -/
def callSlotOf : Ty → Option Ty
  | .sum [("none", .record []), ("some", T)] => if callSlotOk T then some T else none
  | _ => none

/-- The call types of a calls row: at most `callsMax` slots, labelled `c0 …` in order, each an
option over a call type. -/
def callSlotsOf (row : List (Label × Ty)) : Option (List Ty) :=
  if row.length ≤ Kernel.Bounds.callsMax ∧ row.map (·.1) = slotLabels "c" row.length then
    row.mapM fun e => callSlotOf e.2
  else none

/-- The empty call slot of call type `T`. -/
def noCallT (T : Ty) : Term := .inj (optTy T) "none" (.record [])

/-- A call `t` in a slot of call type `T`. -/
def someCallT (T : Ty) (t : Term) : Term := .inj (optTy T) "some" t

/-- The calls row holding slot terms `slots` (each a `noCallT` or `someCallT`) in order. -/
def callsT (slots : List Term) : Term := .record ((slotLabels "c" slots.length).zip slots)

/-- What a method returns: `{calls, edits, state}` (no edits: `edits` is `record []`). -/
def resultT (calls state : Term) (edits : Term := .record []) : Term :=
  .record [("calls", calls), ("edits", edits), ("state", state)]

def importsMax : Nat := 16
def methodsMax : Nat := 64
def lawsMax : Nat := 16
def claimsMax : Nat := 16

/-- Why `install` refuses a package (as `Refusal.program` text on the wire). -/
inductive CheckError
  | tooManyImports | tooManyMethods | tooManyLaws | tooManyClaims
  | contextualSignature | importType
  | stateNotData | ifaceNotRecord
  /-- the body does not check at the interface: which rule, where (`TypeErr`) -/
  | illTyped (why : TypeErr)
  | noMethod (label : Label)
  | badMethod (label : Label)
  | noLaw (label : Label)
  | badLaw (label : Label)
  | tooManyRels
  /-- a relation's key is not fixed-width data within the bounds (LANG-49) -/
  | relKey (label : Label)
  /-- a relation's value, limit, sum column or guard is not what it must be -/
  | badRel (label : Label)
  /-- a method reads a relation that is not cell-keyed with its keys' cell liveness (E1) -/
  | liveNotCellKeyed (label : Label)
  /-- a method reads a peer's rows (PROT-6) and its argument names no `pair : rec {a, b : digest}` -/
  | peerNotNamed (label : Label)
  /-- a method reads a receipt column of a relation that is not cell-keyed, or has no
  `receipt : bytes` argument (E5) -/
  | receiptRead (label : Label)
  /-- a method's type names a value-moving call arm (`transfer`, `credit`) under a grade of 0 (LANG-89):
  the body, by its type, exceeds its declared effect -/
  | effectExceeded (label : Label)
  /-- an `effects` entry out of order or naming no method -/
  | badEffect (label : Label)
  /-- a claim names a law that is not one of the package's laws (LANG-93) -/
  | claimNotLaw (label : Label)
  /-- a claim's invariant is not an interface field of type `fn S bool` -/
  | claimNotInvariant (label : Label)
  /-- the body is not a record literal holding the invariant as `lam S _` and the law as a
  three-binder lambda at the state and request types: nothing to walk -/
  | claimShape (label : Label)
  /-- the law is not in certifying shape for the claim: an `ok` leaf the invariant's test does not
  dominate (`Term.guardedBy`) -/
  | claimUnproved (label : Label)
  deriving DecidableEq, Repr

/-- The refusal's name (law 7): its constructor's. -/
def CheckError.name : CheckError → String
  | .contextualSignature => "contextualSignature" | .importType => "importType"
  | .tooManyImports => "tooManyImports" | .tooManyMethods => "tooManyMethods"
  | .tooManyLaws => "tooManyLaws" | .tooManyClaims => "tooManyClaims" | .stateNotData => "stateNotData"
  | .ifaceNotRecord => "ifaceNotRecord" | .illTyped _ => "illTyped"
  | .noMethod _ => "noMethod" | .badMethod _ => "badMethod"
  | .noLaw _ => "noLaw" | .badLaw _ => "badLaw"
  | .tooManyRels => "tooManyRels" | .relKey _ => "relKey" | .badRel _ => "badRel"
  | .liveNotCellKeyed _ => "liveNotCellKeyed"
  | .peerNotNamed _ => "peerNotNamed" | .receiptRead _ => "receiptRead"
  | .effectExceeded _ => "effectExceeded" | .badEffect _ => "badEffect"
  | .claimNotLaw _ => "claimNotLaw" | .claimNotInvariant _ => "claimNotInvariant"
  | .claimShape _ => "claimShape" | .claimUnproved _ => "claimUnproved"

/-- What goes on the wire inside `Refusal.program`: the name, then the label it is about (for
`illTyped`, the failed rule and its path: `illTyped noField @body.f`). -/
def CheckError.wire : CheckError → String
  | e@(.noMethod ℓ) | e@(.badMethod ℓ) | e@(.noLaw ℓ) | e@(.badLaw ℓ) | e@(.relKey ℓ) | e@(.badRel ℓ)
  | e@(.liveNotCellKeyed ℓ) | e@(.peerNotNamed ℓ) | e@(.receiptRead ℓ) | e@(.effectExceeded ℓ)
  | e@(.badEffect ℓ) | e@(.claimNotLaw ℓ) | e@(.claimNotInvariant ℓ) | e@(.claimShape ℓ) | e@(.claimUnproved ℓ) =>
      s!"{e.name} {ℓ}"
  | e@(.illTyped why) => s!"{e.name} {why.text}"
  | e => e.name

/-- For a human reading a resident's check. -/
def CheckError.text : CheckError → String
  | .contextualSignature => "contextual signature requires live checking"
  | .importType => "import interface is not well formed"
  | .tooManyImports => "imports" | .tooManyMethods => "methods" | .tooManyLaws => "laws"
  | .tooManyClaims => "claims"
  | .stateNotData => "state type" | .ifaceNotRecord => "interface type"
  | .illTyped why => s!"body does not check at its interface: {why.text}"
  | .noMethod ℓ => s!"no method {ℓ}" | .badMethod ℓ => s!"method {ℓ} has the wrong type"
  | .noLaw ℓ => s!"no law {ℓ}" | .badLaw ℓ => s!"law {ℓ} has the wrong type"
  | .tooManyRels => "relations" | .relKey ℓ => s!"relation {ℓ} has no fixed-width key"
  | .badRel ℓ => s!"relation {ℓ} is malformed"
  | .liveNotCellKeyed ℓ => s!"method {ℓ} reads a relation that is not cell-keyed (live)"
  | .peerNotNamed ℓ => s!"method {ℓ} reads a peer's rows and its argument names no pair"
  | .receiptRead ℓ => s!"method {ℓ} reads a receipt column without a cell-keyed relation and a receipt argument"
  | .effectExceeded ℓ => s!"method {ℓ} may move value and declares no grade (effect (moves N))"
  | .badEffect ℓ => s!"effect {ℓ} names no method or is out of order"
  | .claimNotLaw ℓ => s!"claim names {ℓ}, which is not a law of the package"
  | .claimNotInvariant ℓ => s!"claim names {ℓ}, which is not an interface field of type fn S bool"
  | .claimShape ℓ => s!"claim on law {ℓ}: the body holds no literal invariant and law to walk"
  | .claimUnproved ℓ => s!"claim on law {ℓ}: an ok leaf the invariant does not dominate"

def isRecordData : Ty → Bool
  | t@(.record _) => t.wf && t.isData
  | _ => false

/-- What a method's type declares (LANG-23, LANG-49): its argument type, its call slots, the rows
it reads (by relation label, ascending), and how many edit slots it has. -/
structure Sig where
  arg : Ty
  calls : List Ty
  reads : List (Label × RelRead)
  edits : Nat
  deriving DecidableEq

/-- The edit slots of an edits row over the package's relations: at most `editsMax`, labelled
`e0 …` in order, each an option over `editTy rels`. -/
def editSlotsOf (rels : List (Label × RelDecl)) (row : List (Label × Ty)) : Option Nat :=
  if row.length ≤ editsMax ∧ row = (slotLabels "e" row.length).map (fun l => (l, optTy (editTy rels)))
  then some row.length else none

/-- The read a record type spells, whatever the relation (`relReadOf` adds the relation's rule). What one relation's read record declares: its point slots, and its range (the prefix's field
count and its row slots), read back by rebuilding the record and comparing. -/
def relReadShape (d : RelDecl) : Ty → Option RelRead
  | T@(.record fs) =>
    let n := (fs.filter (·.1 ≠ "range")).length
    let range : Option (Option (Nat × Nat)) :=
      match Row.find? "range" fs with
      | none => some none
      | some (.record [("pre", P), ("rows", .record rr)]) =>
          ((List.range (d.key.length + 1)).find? (fun m => preTy d m = P)).map fun m => some (m, rr.length)
      | some _ => none
    match range with
    | none => none
    | some r =>
      let ok (x : RelRead) := n ≤ pointsMax ∧ (r.all fun mk => 1 ≤ mk.2 ∧ mk.2 ≤ rangeRowsMax) ∧ relReadTy d x = T
      if ok ⟨n, r, false, false⟩ then some ⟨n, r, false, false⟩
      else if ok ⟨n, r, true, false⟩ then some ⟨n, r, true, false⟩
      else if ok ⟨n, r, false, true⟩ then some ⟨n, r, false, true⟩
      else if ok ⟨n, r, true, true⟩ then some ⟨n, r, true, true⟩
      else none
  | _ => none

/-- What one relation's read record declares; a `live` read only of a cell-keyed relation (E1). -/
def relReadOf (d : RelDecl) (T : Ty) : Option RelRead :=
  match relReadShape d T with
  | some x => if (x.live || x.receipt) && !d.cellKeyed then none else some x
  | none => none

/-- A method type whose rows argument asks a relation that is not cell-keyed for its keys' cell
liveness: refused `liveNotCellKeyed` by name at install (E1, law 7), not as a bad method. -/
def liveNotCellKeyed (rels : List (Label × RelDecl)) : Ty → Bool
  | .fn (.record row) _ =>
    row.any fun e => match Row.find? e.1 rels with
      | some d => !d.cellKeyed && (relReadShape d e.2).any (·.live)
      | none => false
  | _ => false

/-- The argument type a receipt read needs: a record with `receipt : bytes` (E5). -/
def receiptArg : Ty → Bool
  | .record r => Row.find? "receipt" r = some .bytes
  | _ => false

/-- A method type whose rows argument reads a receipt column of a relation that is not cell-keyed,
or whose argument has no `receipt : bytes`: refused `receiptRead` by name at install (E5, law 7). -/
def receiptReadBad (rels : List (Label × RelDecl)) : Ty → Bool
  | .fn (.record row) (.fn _ (.fn A _)) =>
    row.any fun e => match Row.find? e.1 rels with
      | some d => (relReadShape d e.2).any (fun x => x.receipt && (!d.cellKeyed || !receiptArg A))
      | none => false
  | _ => false

/-- What a method's rows argument declares, read back exactly (`readsTy rels rs = R`). -/
def readsOf (rels : List (Label × RelDecl)) : Ty → Option (List (Label × RelRead))
  | R@(.record row) =>
    match row.mapM (fun e => (Row.find? e.1 rels).bind fun d => (relReadOf d e.2).map (e.1, ·)) with
    | some rs => if readsTy rels rs = R then some rs else none
    | none => none
  | _ => none

/-- The reserved field of a method's rows record that holds a PEER read (PROT-6): reads of the
package's own relations under the other object of the argument's `pair`. No relation is labelled
`peer` (`checkRel`), so the field never shadows one. -/
def peerLabel : Label := "peer"

/-- The argument field a peer-reading method names its pair by: the reader is one of `a`, `b`, and
its peer is the other (`Lang.peerOf`). -/
def pairTy : Ty := .record [("a", .digest), ("b", .digest)]

/-- A method's rows argument: its own reads (`readsTy`), and when it declares peer reads `ps`, the
field `peer` holding them, in sorted position. -/
def rowsTy (rels : List (Label × RelDecl)) (rs ps : List (Label × RelRead)) : Ty :=
  match ps, readsTy rels rs with
  | [], R => R
  | _, .record fs => .record (Row.sort (fs ++ [(peerLabel, readsTy rels ps)]))
  | _, R => R

/-- A rows record read back as its own reads and its peer reads, exactly (`rowsTy rels rs ps = R`);
a record without a `peer` field is `readsOf`'s, with no peer reads. -/
def rowsOf (rels : List (Label × RelDecl)) : Ty → Option (List (Label × RelRead) × List (Label × RelRead))
  | R@(.record row) =>
    match Row.find? peerLabel row with
    | none => (readsOf rels R).map (·, [])
    | some P =>
      match readsOf rels (.record (row.filter (·.1 ≠ peerLabel))), readsOf rels P with
      | some rs, some ps => if !ps.isEmpty && rowsTy rels rs ps == R then some (rs, ps) else none
      | _, _ => none
  | _ => none

/-- The peer reads a method type declares (`[]`: none). -/
def methodPeer (rels : List (Label × RelDecl)) : Ty → List (Label × RelRead)
  | .fn R _ => ((rowsOf rels R).map (·.2)).getD []
  | _ => []

/-- A method type that reads a peer's rows names the pair in its argument record. -/
def pairNamed (A : Ty) (ps : List (Label × RelRead)) : Bool :=
  ps.isEmpty ||
    match A with
    | .record row => Row.find? "pair" row == some pairTy
    | _ => false

/-- A method type whose rows argument reads a peer while its argument names no pair: refused
`peerNotNamed` by name at install (law 7), not as a bad method. -/
def peerUnnamed (rels : List (Label × RelDecl)) : Ty → Bool
  | .fn R (.fn _ (.fn A _)) =>
    match rowsOf rels R with
    | some (_, ps) => !pairNamed A ps
    | none => false
  | _ => false

/-- The signature of a method field, if it has a method's shape over state `S` and relations
`rels`: `fn R (fn S (fn A (fn reqTy (rec {calls, edits, state})))))`. -/
def methodSig (S : Ty) (rels : List (Label × RelDecl)) : Ty → Option Sig
  | .fn R (.fn S' (.fn A (.fn Q (.record [("calls", .record row), ("edits", .record erow), ("state", S'')])))) =>
      if S' = S ∧ Q = reqTy ∧ S'' = S ∧ A.isData then
        match callSlotsOf row, editSlotsOf rels erow, rowsOf rels R with
        | some ks, some es, some (rs, ps) =>
          if pairNamed A ps && (!(rs ++ ps).any (·.2.receipt) || receiptArg A) then some ⟨A, ks, rs, es⟩ else none
        | _, _, _ => none
      else none
  | _ => none

/-- The argument type of a method field. -/
def methodArg (S : Ty) (rels : List (Label × RelDecl)) (t : Ty) : Option Ty := (methodSig S rels t).map (·.arg)

def checkMethods (S : Ty) (rels : List (Label × RelDecl)) (row : List (Label × Ty)) :
    List Label → Except CheckError Unit
  | [] => .ok ()
  | ℓ :: ms =>
      match Row.find? ℓ row with
      | none => .error (.noMethod ℓ)
      | some t =>
        if (methodArg S rels t).isSome then checkMethods S rels row ms
        else if liveNotCellKeyed rels t then .error (.liveNotCellKeyed ℓ)
        else if peerUnnamed rels t then .error (.peerNotNamed ℓ)
        else if receiptReadBad rels t then .error (.receiptRead ℓ)
        else .error (.badMethod ℓ)

mutual
/-- A key field's type is fixed-width data: a natural, a boolean, a digest, an enumeration (a sum
whose arms all carry `rec {}`), or a record of those. Bytes and functions are refused. -/
def keyFixed : Ty → Bool
  | .nat | .bool | .digest => true
  | .bytes | .fn _ _ => false
  | .record r => keyRowFixed r
  | .sum r => !r.isEmpty && r.all fun a => a.2 == .record []

def keyRowFixed : List (Label × Ty) → Bool
  | [] => true
  | (_, t) :: r => keyFixed t && keyRowFixed r
end

mutual
/-- The bytes a fixed-width key field takes in the data encoding, for digests of `dw` bytes: a
natural 8, a boolean 1, a digest its four length bytes and itself, an enumeration its tag byte,
a record its fields'. -/
def keyWidth (dw : Nat) : Ty → Nat
  | .nat => 8
  | .bool => 1
  | .digest => 4 + dw
  | .record r => keyRowWidth dw r
  | .sum _ => 1
  | _ => 0

def keyRowWidth (dw : Nat) : List (Label × Ty) → Nat
  | [] => 0
  | (_, t) :: r => keyWidth dw t + keyRowWidth dw r
end

/-- A relation's key width, for digests of `dw` bytes. -/
def RelDecl.width (d : RelDecl) (dw : Nat) : Nat := keyRowWidth dw d.key

/-- What a guard judges (LANG-59): one edit of the relation, and `old`, the row now at the slot the
caller pinned (`none` for a pinned-absent slot or an insert with no pin). -/
def guardInTy (d : RelDecl) : Ty := .record [("edit", relEditTy d), ("old", optTy d.val)]

/-- A guard's type: the object's state before, the request, one edit with its old row; a verdict. -/
def guardTy (S : Ty) (d : RelDecl) : Ty := .fn S (.fn reqTy (.fn (guardInTy d) verdictTy))

/-- A leg of value (LANG-90): `amount` of the denomination `asset`. What a `holds` field is. -/
def legTy : Ty := .record [("amount", .nat), ("asset", .digest)]

/-- The held field, if any, is a `legTy` field of the value record. -/
def RelDecl.holdsOk (d : RelDecl) : Bool :=
  match d.holds with
  | none => true
  | some f =>
      match d.val with
      | .record r => Row.find? f r == some legTy
      | _ => false

/-- The sum column is a natural field of the value record; `cap` is set exactly when it is. -/
def RelDecl.sumOk (d : RelDecl) : Bool :=
  match d.sum with
  | none => d.cap == 0
  | some f => decide (0 < d.cap) && decide (d.cap < Bounds.natLimit) &&
      match d.val with
      | .record r => Row.find? f r == some .nat
      | _ => false

/-- One relation: a fixed-width key of distinct fields (distinct because `keyTy d` is canonical: its
sorted labels strictly ascend, `Lang.Proofs.KeyOrder.checkRel_key_nodup`) within `keyBytesMax` at the
deployed digest width (`relKey`), and a data value, a limit within `rowsPerRelationMax`, a sum column and a guard of
the right type (`badRel`). -/
def checkRel (S : Ty) (row : List (Label × Ty)) (r : Label × RelDecl) : Except CheckError Unit := do
  let (ℓ, d) := r
  unless !d.key.isEmpty && decide (d.key.length ≤ keyFieldsMax) && d.key.all (fun f => Wire.labelOk f.1 && keyFixed f.2) &&
      (keyTy d).wf &&
      decide (d.width Bounds.digestBytesMax ≤ Kernel.Bounds.keyBytesMax) do throw (.relKey ℓ)
  unless d.val.wf && d.val.isData && Wire.tyWire d.val && decide (1 ≤ d.limit) &&
      decide (d.limit ≤ Kernel.Bounds.rowsPerRelationMax) && d.sumOk && d.holdsOk &&
      (match d.guard with
       | none => true
       | some g => Row.find? g row == some (guardTy S d)) do throw (.badRel ℓ)
  -- the label a method's rows record holds a peer read at (PROT-6) is never a relation's
  if ℓ = peerLabel then throw (.badRel ℓ)

def checkRels (S : Ty) (row : List (Label × Ty)) (rels : List (Label × RelDecl)) : Except CheckError Unit := do
  if rels.length > relsMax then throw .tooManyRels
  unless Row.ascending rels && rels.all (fun r => Wire.labelOk r.1) do
    throw (.badRel ((rels.head?.map (·.1)).getD ""))
  for r in rels do checkRel S row r

def checkLaws (S : Ty) (row : List (Label × Ty)) : List Label → Except CheckError Unit
  | [] => .ok ()
  | ℓ :: ls =>
      match Row.find? ℓ row with
      | none => .error (.noLaw ℓ)
      | some t => if t = lawTy S then checkLaws S row ls else .error (.badLaw ℓ)

/-! ## Grades against the type (LANG-89): what install decides of a method's effect -/

/-- The call arms that move value. -/
def movesArm (ℓ : Label) : Bool := ℓ == "transfer" || ℓ == "credit"

/-- A call slot type (`optTy` of a call sum) names a value-moving arm. -/
def slotMoves : Ty → Bool
  | .sum [("none", .record []), ("some", .sum arms)] => arms.any fun a => movesArm a.1
  | _ => false

/-- A method type's call slots name a value-moving arm: the body, by its type, may move value. -/
def methodMoves : Ty → Bool
  | .fn _ (.fn _ (.fn _ (.fn _ (.record [("calls", .record row), _, _])))) => row.any fun e => slotMoves e.2
  | _ => false

/-- The `effects` table is ascending and names methods only (`badEffect`), and every method whose
type may move value has a grade above 0 (`effectExceeded`): the one syntactic check of a grade. A
grade a type does not use is allowed, as a slot left `none` is. -/
def checkEffects (p : Package) (row : List (Label × Ty)) : Except CheckError Unit :=
  if !Row.ascending p.effects then .error (.badEffect ((p.effects.head?.map (·.1)).getD ""))
  else match p.effects.find? (fun e => !p.methods.contains e.1) with
    | some e => .error (.badEffect e.1)
    | none =>
      match p.methods.find? (fun ℓ => match Row.find? ℓ row with
          | some t => methodMoves t && (p.effectOf ℓ).moves == 0
          | none => false) with
      | some ℓ => .error (.effectExceeded ℓ)
      | none => .ok ()
/-! ## Claims (LANG-93, `Lang.Claim`): what the package says of itself, checked against its own term

A claim is checked at install beside the type, by the shape of the term: for `keeps inv law`, the
law named is one of the package's laws (`claimNotLaw`), the invariant is an interface field at
`fn S bool` (`claimNotInvariant`), the body is a record literal holding the invariant as the closed
literal `lam S ib` and the law as `lam S (lam S (lam reqTy b))` (`claimShape`: a layer's body is
`extend (ref 0) _`, so a layer cannot yet claim), and every `ok` leaf of `b` lies under the test
`app (lam S ib) new` (`Term.guardedBy`; else `claimUnproved`). The meaning of the sentence is
`Lang.Proofs.Claim.Keeps`; that a package the check admits bears it is `install_claims`; that every
object of such a package keeps it along every audited log is KERNEL-73's
`Kernel.Proofs.Logic.Claims.object_history_keeps`. The walk is O(|law|), unmetered as `checkE` is. -/

/-- One claim against the package's state type `S`, interface row `row`, law labels `laws` and body. -/
def checkClaim (S : Ty) (row : List (Label × Ty)) (laws : List Label) (body : Term) :
    Claim → Except CheckError Unit
  | .keeps inv law =>
    if law ∉ laws then .error (.claimNotLaw law)
    else if Row.find? inv row ≠ some (.fn S .bool) then .error (.claimNotInvariant inv)
    else match body with
      | .record fs =>
        match Row.find? inv fs, Row.find? law fs with
        | some (.lam A ib), some (.lam B (.lam C (.lam Q b))) =>
          if A = S ∧ B = S ∧ C = S ∧ Q = reqTy then
            match Term.guardedBy (.lam S ib) 1 0 b with
            | true => .ok ()
            | false => .error (.claimUnproved law)
          else .error (.claimShape law)
        | _, _ => .error (.claimShape law)
      | _ => .error (.claimShape law)

def checkClaims (S : Ty) (row : List (Label × Ty)) (laws : List Label) (body : Term) :
    List Claim → Except CheckError Unit
  | [] => .ok ()
  | c :: cs => do checkClaim S row laws body c; checkClaims S row laws body cs

/-- Everything about a package but its body: bounds, a data state, a canonical record interface. -/
def Package.checkShape (p : Package) : Except CheckError Unit := do
  if p.imports.length > importsMax then throw .tooManyImports
  if p.methods.length > methodsMax then throw .tooManyMethods
  if p.laws.length > lawsMax then throw .tooManyLaws
  if p.claims.length > claimsMax then throw .tooManyClaims
  unless isRecordData p.state do throw .stateNotData
  unless p.iface.wf do throw .ifaceNotRecord

/-- Its methods and laws are fields of its interface record at their shapes, and its claims are
borne by its body (`checkClaims`, LANG-93). -/
def Package.checkFields (p : Package) : Except CheckError Unit :=
  match p.iface with
  | .record row => do
      checkRels p.state row p.rels
      checkMethods p.state p.rels row p.methods
      checkEffects p row
      checkLaws p.state row p.laws
      checkClaims p.state row p.laws p.body p.claims
  | _ => .error .ifaceNotRecord

/-- The install check, given the interfaces of the imports in order: the shape, then the body
checks at its interface (`checkE`, which names the failed rule), then the fields. -/
def Package.checkWith (ifaces : List Ty) (p : Package) : Except CheckError Unit :=
  match p.checkShape, checkE ifaces p.body p.iface (Ω := []) with
  | .error e, _ => .error e
  | .ok (), .error why => .error (.illTyped why)
  | .ok (), .ok () =>
      if !p.holes.isEmpty then .error .contextualSignature
      else if !ifaces.all Ty.wf then .error .importType
      else p.checkFields

/-! ## Relocation: a body's `ref i` becomes the closure's global index -/

mutual
def Term.relocate (f : Nat → Nat) : Term → Term
  | .var i => .var i
  | .lam a b => .lam a (b.relocate f)
  | .app g a => .app (g.relocate f) (a.relocate f)
  | .fix t => .fix (t.relocate f)
  | .nat n => .nat n
  | .bool b => .bool b
  | .bytes s => .bytes s
  | .digest s => .digest s
  | .prim p a b => .prim p (a.relocate f) (b.relocate f)
  | .record fs => .record (Term.relocateRow f fs)
  | .get t ℓ => .get (t.relocate f) ℓ
  | .extend t fs => .extend (t.relocate f) (Term.relocateRow f fs)
  | .inj a ℓ t => .inj a ℓ (t.relocate f)
  | .case t arms => .case (t.relocate f) (Term.relocateRow f arms)
  | .ite c a b => .ite (c.relocate f) (a.relocate f) (b.relocate f)
  | .ref i => .ref (f i)
  | .hole n σ => .hole n (Term.relocateList f σ)
  | .refuse T w => .refuse T w

def Term.relocateList (f : Nat → Nat) : List Term → List Term
  | [] => []
  | t :: ts => t.relocate f :: Term.relocateList f ts

def Term.relocateRow (f : Nat → Nat) : List (Label × Term) → List (Label × Term)
  | [] => []
  | (ℓ, t) :: fs => (ℓ, t.relocate f) :: Term.relocateRow f fs
end

/-! ## Id literals: what install asks the World's `digestOf` about (LANG-38) -/

mutual
/-- The digest literals of a term, in order. -/
def Term.digestLits : Term → List ByteArray
  | .digest s => [s]
  | .hole _ σ => Term.listDigestLits σ
  | .var _ | .nat _ | .bool _ | .bytes _ | .ref _ | .refuse _ _ => []
  | .lam _ b | .fix b | .get b _ | .inj _ _ b => b.digestLits
  | .app f a | .prim _ f a => f.digestLits ++ a.digestLits
  | .record fs => Term.rowDigestLits fs
  | .extend t fs | .case t fs => t.digestLits ++ Term.rowDigestLits fs
  | .ite c a b => c.digestLits ++ a.digestLits ++ b.digestLits

def Term.listDigestLits : List Term → List ByteArray
  | [] => []
  | t :: ts => t.digestLits ++ Term.listDigestLits ts

def Term.rowDigestLits : List (Label × Term) → List ByteArray
  | [] => []
  | (_, t) :: fs => t.digestLits ++ Term.rowDigestLits fs
end

/-! ## Wire: a package is one `Codec.Tree` -/

namespace Wire
open Nanodregg.Codec

/-- The digest bytes an import id may have (the deployed digest is 32; the Sim's is 8). -/
def importBytesMax : Nat := Bounds.digestBytesMax

def labelLeaf (ℓ : Label) : Tree := .node 1 ℓ.toUTF8 []

def labelsOf : List Tree → Option (List Label)
  | [] => some []
  | .node 1 p [] :: ts =>
    match labelOf p, labelsOf ts with
    | some ℓ, some ls => some (ℓ :: ls)
    | _, _ => none
  | _ => none

def importsOf : List Tree → Option (List ByteArray)
  | [] => some []
  | .node 0 p [] :: ts =>
    if p.size ≤ importBytesMax then (importsOf ts).map (p :: ·) else none
  | _ => none

/-- An optional label: `node 0` empty, or `node 1 ℓ`. -/
def optLabelLeaf : Option Label → Tree
  | none => .node 0 .empty []
  | some ℓ => .node 1 ℓ.toUTF8 []

def optLabelOf : Tree → Option (Option Label)
  | .node 0 e [] => if e = .empty then some none else none
  | .node 1 p [] => (labelOf p).map some
  | _ => none

/-- A key's fields, in declared order: `field` nodes (the type's tag 6) under a `node 0`. -/
def keyFieldsOf : List Tree → Option (List (Label × Ty))
  | [] => some []
  | .node 6 p [t] :: ts =>
    match labelOf p, tyOf t, keyFieldsOf ts with
    | some ℓ, some T, some fs => some ((ℓ, T) :: fs)
    | _, _, _ => none
  | _ => none

/-- A relation: `node 0 ℓ [key val limit sum cap retract guard holds]` (LANG-49; `holds` LANG-90). -/
def relTree (r : Label × RelDecl) : Tree :=
  .node 0 r.1.toUTF8
    [.node 0 .empty (r.2.key.map fun f => .node 6 f.1.toUTF8 [tyTree f.2]), tyTree r.2.val,
     .node 0 (u64Bytes r.2.limit) [], optLabelLeaf r.2.sum, .node 0 (u64Bytes r.2.cap) [],
     .node (if r.2.retract then 1 else 0) .empty [], optLabelLeaf r.2.guard, optLabelLeaf r.2.holds]

def relOf : Tree → Option (Label × RelDecl)
  | .node 0 p [.node 0 ek ks, v, .node 0 lim [], su, .node 0 ca [], .node rt er [], gu, ho] =>
    if ek = .empty ∧ er = .empty ∧ (rt = 0 ∨ rt = 1) then
      match labelOf p, keyFieldsOf ks, tyOf v, u64Of lim, optLabelOf su, u64Of ca, optLabelOf gu, optLabelOf ho with
      | some ℓ, some key, some val, some limit, some sum, some cap, some guard, some holds =>
        some (ℓ, { key, val, limit, sum, cap, retract := rt = 1, guard, holds })
      | _, _, _, _, _, _, _, _ => none
    else none
  | _ => none

def relsOf : List Tree → Option (List (Label × RelDecl))
  | [] => some []
  | t :: ts =>
    match relOf t, relsOf ts with
    | some r, some rs => some (r :: rs)
    | _, _ => none

/-- A method's grades (LANG-89): `node 0 ℓ [node 0 u64 moves]`. -/
def effectTree (e : Label × Effect) : Tree := .node 0 e.1.toUTF8 [.node 0 (u64Bytes e.2.moves) []]

def effectOf : Tree → Option (Label × Effect)
  | .node 0 p [.node 0 m []] =>
    match labelOf p, u64Of m with
    | some ℓ, some moves => some (ℓ, { moves })
    | _, _ => none
  | _ => none

def effectsOf (ts : List Tree) : Option (List (Label × Effect)) := ts.mapM effectOf

def effectWire (e : Label × Effect) : Bool := labelOk e.1 && decide (e.2.moves < 2 ^ 64)

/-- A relation has a tree that reads back to it. -/
def relWire (r : Label × RelDecl) : Bool :=
  labelOk r.1 && r.2.key.all (fun f => labelOk f.1 && tyWire f.2) && tyWire r.2.val &&
    decide (r.2.limit < 2 ^ 64) && decide (r.2.cap < 2 ^ 64) && r.2.sum.all labelOk && r.2.guard.all labelOk &&
    r.2.holds.all labelOk

/-- A claim (LANG-93): `keeps inv law` is `node 0 [] [labelLeaf inv, labelLeaf law]`. -/
def claimTree : Claim → Tree
  | .keeps inv law => .node 0 .empty [labelLeaf inv, labelLeaf law]

def claimOf : Tree → Option Claim
  | .node 0 e [.node 1 pi [], .node 1 pl []] =>
    if e = .empty then
      match labelOf pi, labelOf pl with
      | some inv, some law => some (.keeps inv law)
      | _, _ => none
    else none
  | _ => none

/-- A claim has a tree that reads back to it. -/
def claimWire : Claim → Bool
  | .keeps inv law => labelOk inv && labelOk law

/-- `node 0 [imports state iface body methods laws rels doc holes effects claims]`; imports are `node 0 id`
leaves under a `node 0`, methods and laws `node 1 ℓ` leaves under a `node 1`, relations `relTree`s
under a `node 2`, the doc a `node 0` leaf whose payload is its bytes (LANG-60), the holes under a
`node 3`, the grades `effectTree`s under a `node 4` (LANG-89), the claims `claimTree`s under a
`node 5` (LANG-93). -/
def packageTree (p : Package) : Tree :=
  .node 0 .empty
    [.node 0 .empty (p.imports.map fun d => .node 0 d []), tyTree p.state, tyTree p.iface,
     termTree p.body, .node 1 .empty (p.methods.map labelLeaf), .node 1 .empty (p.laws.map labelLeaf),
     .node 2 .empty (p.rels.map relTree), .node 0 p.doc [],
     .node 3 .empty (p.holes.map holeROMTree), .node 4 .empty (p.effects.map effectTree),
     .node 5 .empty (p.claims.map claimTree)]

def packageOf : Tree → Option Package
  | .node 0 e [.node 0 ei is, s, i, b, .node 1 em ms, .node 1 el ls, .node 2 er rs, .node 0 doc [], .node 3 eh hs,
      .node 4 ee es, .node 5 ec cs] =>
    if e = .empty ∧ ei = .empty ∧ em = .empty ∧ el = .empty ∧ er = .empty ∧ eh = .empty ∧ ee = .empty ∧
        ec = .empty ∧ Bounds.docOk doc = true then
      match importsOf is, tyOf s, tyOf i, termOf b, labelsOf ms, labelsOf ls, relsOf rs, hs.mapM holeROMOf,
          effectsOf es, cs.mapM claimOf with
      | some imports, some state, some iface, some body, some methods, some laws, some rels, some holes,
          some effects, some claims =>
        some { imports, state, iface, body, methods, laws, rels, doc, holes, effects, claims }
      | _, _, _, _, _, _, _, _, _, _ => none
    else none
  | _ => none

/-- The package has a tree that reads back to it. -/
def packageWire (p : Package) : Bool :=
  Bounds.docOk p.doc && p.imports.all (fun d => decide (d.size ≤ importBytesMax)) && tyWire p.state &&
    tyWire p.iface && termWire p.body && p.methods.all labelOk && p.laws.all labelOk && p.rels.all relWire && p.holes.all holeROMWire &&
    p.effects.all effectWire && p.claims.all claimWire

/-- The package tree stream at the language's bounds. -/
def treeStream : Stream (Tree.Fitting nodeMax depthMax) := Stream.tree nodeMax depthMax (by decide)

/-- The version byte (LANG-60): exactly `Bounds.packageWireVersion`; any other byte is refused
`lang/package-version/10` by name, so bytes written at another version are never read as a package. -/
def packageVersion : Stream Unit :=
  Stream.refine "lang/package-version/10" Stream.u8
    (fun v => if v = Bounds.packageWireVersion then some () else none) (fun _ => Bounds.packageWireVersion)

/-- The one stream of a package: its version byte, then its tree. -/
def packageStream : Stream (Unit × Tree.Fitting nodeMax depthMax) := Stream.product packageVersion treeStream

/-- A package's tree as the tree stream's value: `packageTree p` when it fits the language's bounds.
The fallback (`.node 1 .empty []`, which `packageOf` refuses) is never written: `encodePackage` writes
only a package that is `packageWire` and fits, and `packageCodec_lawfulOn` is stated on exactly those. -/
def packageFit (p : Package) : Tree.Fitting nodeMax depthMax :=
  if h : (packageTree p).fits nodeMax depthMax then ⟨packageTree p, h⟩ else ⟨.node 1 .empty [], by decide⟩

/-- The package codec: the version byte and the tree stream, refined by `packageOf`, refused
`lang/package/10` by name (a refine site, so `gates/codec-vectors.tsv` pins what package bytes mean: a
new term, type or primitive tag turns a refused boundary row into a read one, and the version must
move, and with it this label, `lang/package/N` at version N: `Lang.Proofs.Wire.packageCodec_label`
fails the build otherwise; cv 01a14e58-1586, LANG-60). -/
def packageCodec : Stream Package :=
  Stream.refine "lang/package/10" packageStream (fun t => packageOf t.2.val) fun p => ((), packageFit p)

/-- The bytes of a package; `none` when it has no tree in bounds (a label, row, index or literal
past its bound, or nested deeper than `depthMax`). -/
def encodePackage (p : Package) : Option ByteArray :=
  if packageWire p then
    if (packageTree p).fits nodeMax depthMax then some (packageCodec.bytes p)
    else none
  else none

/-- The version byte (any other refused `lang/package-version/10`), then exactly one package tree, which reads as
a package. `packageCodec`'s reading, with the tree
stream's whole-input check (trailing bytes) made before `packageOf`, as it always was: the accepted
packages are `packageCodec.decode`'s exactly (`decodePackage_eq_codec`). -/
def decodePackage (b : ByteArray) : Except Refusal Package :=
  match packageStream.decode b with
  | .error e => .error e
  | .ok t =>
    match packageOf t.2.val with
    | some p => .ok p
    | none => .error (.rejected 0 "lang/package/10")

end Wire
end Nanodregg.Lang
