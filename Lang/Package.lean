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

namespace Nanodregg.Lang

structure Package where
  /-- ids of installed packages, as the digest bytes the kernel uses -/
  imports : List ByteArray
  state : Ty
  iface : Ty
  body : Term
  methods : List Label
  laws : List Label
  deriving Inhabited

/-- Which act is judged (KERNEL's `Occasion`): a birth (the seed is `old = new`), a write, a law
replacement by the listed law ids (their digest bytes concatenated in order; the state is unchanged),
or an invoke of method `i`. A law cases on it; the checker requires one arm per label, so a law
written with `case` has no default arm. -/
def occasionTy : Ty :=
  .sum [("adopt", .bytes), ("birth", .record []), ("invoke", .nat), ("relaw", .bytes), ("write", .record [])]

/-- What a law and a method see of the call: the signing member, whose authority it uses, the
object judged or run on (`self`: a method names its own accounts by it, LANG-25), the call's
signed window (the Turn lands at a height in `[notBefore, validUntil]`, KERNEL-10), and the act
being judged. -/
def reqTy : Ty :=
  .record [("agent", .digest), ("notBefore", .nat), ("occasion", occasionTy), ("principal", .digest),
    ("self", .digest), ("validUntil", .nat)]

/-- A law's verdict: `ok`, or `refused` with the author's reason. -/
def verdictTy : Ty := .sum [("ok", .record []), ("refused", .bytes)]

def lawTy (S : Ty) : Ty := .fn S (.fn S (.fn reqTy verdictTy))

/-! ## Calls: what a method asks the kernel to do as the object (LANG-23, LANG-33)

The core has no lists, so a method returns its calls in a row of option SLOTS `c0 … c(k-1)`,
`k ≤ Kernel.Bounds.callsMax`. Each slot's type names the kinds of call it may carry: options over
a sub-sum of `callTy`, every arm at exactly its `callTy` type. `callTy` has one arm per kind an
object may exercise (KERNEL's `Body.callable`: account, credit, grant, invoke, transfer), its fields
the `Body` constructor's: a digest is `digest`, an `Option` is `optTy`, an `AcctRef` is
`acctRefTy`, a grant's rights the fixed-arity `rightsTy`. So a method's type says how many calls
it may make and of which kinds, and costs bytes only for those: a method that makes none has
`calls : rec {}`. `Lang.Call` reads the kernel's `Body` back out of such data. -/

/-- An optional `T`. -/
def optTy (T : Ty) : Ty := .sum [("none", .record []), ("some", T)]

/-- How a call names a value account (KERNEL's `AcctRef`): a well by its denomination, any other
account by its owner and denomination. -/
def acctRefTy : Ty := .sum [("of", .record [("asset", .digest), ("owner", .digest)]), ("well", .digest)]

/-- A right a granted call carries (KERNEL's `Right`). -/
def rightTy : Ty := .sum [("enroll", .nat), ("invoke", .nat), ("mutate", .record []), ("observe", .record [])]

/-- The rights one granted call may carry: KERNEL's `Right` has four constructors, and a grant
naming one twice says nothing more. -/
def rightsMax : Nat := 4

/-- The slot labels `r0 …` of `rightsTy` and `c0 …` of a calls row, in slot order. -/
def slotLabels (c : String) (n : Nat) : List Label := (List.range n).map fun i => c ++ toString i

def rightLabels : List Label := slotLabels "r" rightsMax

def rightsTy : Ty := .record (rightLabels.map fun l => (l, optTy rightTy))

/-- The arms of `callTy`, one per callable kind, in canonical order. -/
def callArms : List (Label × Ty) :=
  [("account", .record [("asset", .digest), ("owner", .digest)]),
    ("credit", .record [("acct", acctRefTy), ("amount", .nat), ("via", optTy .digest), ("well", .digest)]),
    ("grant", .record [("grantee", .digest), ("parent", optTy .digest), ("rights", rightsTy),
      ("target", .digest)]),
    ("invoke", .record [("args", .bytes), ("budget", .nat), ("method", .nat), ("obj", .digest),
      ("via", optTy .digest)]),
    ("transfer", .record [("amount", .nat), ("dst", acctRefTy), ("once", optTy .bytes),
      ("src", acctRefTy), ("via", optTy .digest)])]

/-- Any call an object may make. -/
def callTy : Ty := .sum callArms

/-- A call of one of `kinds` (labels of `callArms`), in canonical order: a slot's call type. -/
def callOf (kinds : List Label) : Ty := .sum (callArms.filter fun a => kinds.contains a.1)

/-- The calls row over slot call types `ks`: slot `ci` is `optTy (ks[i])`. -/
def callsTy (ks : List Ty) : Ty := .record ((slotLabels "c" ks.length).zip (ks.map optTy))

/-- What a method returns over state `S` with call slots `ks`: the calls it makes as the object,
and the new state. -/
def resultTy (S : Ty) (ks : List Ty := []) : Ty := .record [("calls", callsTy ks), ("state", S)]

/-- A method's type for argument type `A` and call slots `ks` (none: it makes no calls). -/
def methodTy (S A : Ty) (ks : List Ty := []) : Ty := .fn S (.fn A (.fn reqTy (resultTy S ks)))

/-- A slot's call type: a sum of at least one of `callArms`, each at its own type (an empty sum
would be a slot that can never hold a call). -/
def callSlotOk : Ty → Bool
  | .sum arms => !arms.isEmpty && arms.all fun a => decide (Row.find? a.1 callArms = some a.2)
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

/-- What a method returns: `{calls, state}`. -/
def resultT (calls state : Term) : Term := .record [("calls", calls), ("state", state)]

def importsMax : Nat := 16
def methodsMax : Nat := 64
def lawsMax : Nat := 16

/-- Why `install` refuses a package (as `Refusal.program` text on the wire). -/
inductive CheckError
  | tooManyImports | tooManyMethods | tooManyLaws
  | stateNotData | ifaceNotRecord
  /-- the body does not check at the interface: which rule, where (`TypeErr`) -/
  | illTyped (why : TypeErr)
  | noMethod (label : Label)
  | badMethod (label : Label)
  | noLaw (label : Label)
  | badLaw (label : Label)
  deriving DecidableEq, Repr

/-- The refusal's name (law 7): its constructor's. -/
def CheckError.name : CheckError → String
  | .tooManyImports => "tooManyImports" | .tooManyMethods => "tooManyMethods"
  | .tooManyLaws => "tooManyLaws" | .stateNotData => "stateNotData"
  | .ifaceNotRecord => "ifaceNotRecord" | .illTyped _ => "illTyped"
  | .noMethod _ => "noMethod" | .badMethod _ => "badMethod"
  | .noLaw _ => "noLaw" | .badLaw _ => "badLaw"

/-- What goes on the wire inside `Refusal.program`: the name, then the label it is about (for
`illTyped`, the failed rule and its path: `illTyped noField @body.f`). -/
def CheckError.wire : CheckError → String
  | e@(.noMethod ℓ) | e@(.badMethod ℓ) | e@(.noLaw ℓ) | e@(.badLaw ℓ) => s!"{e.name} {ℓ}"
  | e@(.illTyped why) => s!"{e.name} {why.text}"
  | e => e.name

/-- For a human reading a resident's check. -/
def CheckError.text : CheckError → String
  | .tooManyImports => "imports" | .tooManyMethods => "methods" | .tooManyLaws => "laws"
  | .stateNotData => "state type" | .ifaceNotRecord => "interface type"
  | .illTyped why => s!"body does not check at its interface: {why.text}"
  | .noMethod ℓ => s!"no method {ℓ}" | .badMethod ℓ => s!"method {ℓ} has the wrong type"
  | .noLaw ℓ => s!"no law {ℓ}" | .badLaw ℓ => s!"law {ℓ} has the wrong type"

def isRecordData : Ty → Bool
  | t@(.record _) => t.wf && t.isData
  | _ => false

/-- The argument type and call slots of a method field, if it has a method's shape over state `S`. -/
def methodSig (S : Ty) : Ty → Option (Ty × List Ty)
  | .fn S' (.fn A (.fn R (.record [("calls", .record row), ("state", S'')]))) =>
      if S' = S ∧ R = reqTy ∧ S'' = S ∧ A.isData then (callSlotsOf row).map (A, ·) else none
  | _ => none

/-- The argument type of a method field. -/
def methodArg (S : Ty) (t : Ty) : Option Ty := (methodSig S t).map (·.1)

def checkMethods (S : Ty) (row : List (Label × Ty)) : List Label → Except CheckError Unit
  | [] => .ok ()
  | ℓ :: ms =>
      match Row.find? ℓ row with
      | none => .error (.noMethod ℓ)
      | some t => if (methodArg S t).isSome then checkMethods S row ms else .error (.badMethod ℓ)

def checkLaws (S : Ty) (row : List (Label × Ty)) : List Label → Except CheckError Unit
  | [] => .ok ()
  | ℓ :: ls =>
      match Row.find? ℓ row with
      | none => .error (.noLaw ℓ)
      | some t => if t = lawTy S then checkLaws S row ls else .error (.badLaw ℓ)

/-- Everything about a package but its body: bounds, a data state, a canonical record interface. -/
def Package.checkShape (p : Package) : Except CheckError Unit := do
  if p.imports.length > importsMax then throw .tooManyImports
  if p.methods.length > methodsMax then throw .tooManyMethods
  if p.laws.length > lawsMax then throw .tooManyLaws
  unless isRecordData p.state do throw .stateNotData
  unless p.iface.wf do throw .ifaceNotRecord

/-- Its methods and laws are fields of its interface record at their shapes. -/
def Package.checkFields (p : Package) : Except CheckError Unit :=
  match p.iface with
  | .record row => do
      checkMethods p.state row p.methods
      checkLaws p.state row p.laws
  | _ => .error .ifaceNotRecord

/-- The install check, given the interfaces of the imports in order: the shape, then the body
checks at its interface (`checkE`, which names the failed rule), then the fields. -/
def Package.checkWith (ifaces : List Ty) (p : Package) : Except CheckError Unit :=
  match p.checkShape, checkE ifaces p.body p.iface with
  | .error e, _ => .error e
  | .ok (), .error why => .error (.illTyped why)
  | .ok (), .ok () => p.checkFields

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

def Term.relocateRow (f : Nat → Nat) : List (Label × Term) → List (Label × Term)
  | [] => []
  | (ℓ, t) :: fs => (ℓ, t.relocate f) :: Term.relocateRow f fs
end

/-! ## Id literals: what install asks the World's `digestOf` about (LANG-38) -/

mutual
/-- The digest literals of a term, in order. -/
def Term.digestLits : Term → List ByteArray
  | .digest s => [s]
  | .var _ | .nat _ | .bool _ | .bytes _ | .ref _ => []
  | .lam _ b | .fix b | .get b _ | .inj _ _ b => b.digestLits
  | .app f a | .prim _ f a => f.digestLits ++ a.digestLits
  | .record fs => Term.rowDigestLits fs
  | .extend t fs | .case t fs => t.digestLits ++ Term.rowDigestLits fs
  | .ite c a b => c.digestLits ++ a.digestLits ++ b.digestLits

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

/-- `node 0 [imports state iface body methods laws]`; imports are `node 0 id` leaves under a
`node 0`, methods and laws `node 1 ℓ` leaves under a `node 1`. -/
def packageTree (p : Package) : Tree :=
  .node 0 .empty
    [.node 0 .empty (p.imports.map fun d => .node 0 d []), tyTree p.state, tyTree p.iface,
     termTree p.body, .node 1 .empty (p.methods.map labelLeaf), .node 1 .empty (p.laws.map labelLeaf)]

def packageOf : Tree → Option Package
  | .node 0 e [.node 0 ei is, s, i, b, .node 1 em ms, .node 1 el ls] =>
    if e = .empty ∧ ei = .empty ∧ em = .empty ∧ el = .empty then
      match importsOf is, tyOf s, tyOf i, termOf b, labelsOf ms, labelsOf ls with
      | some imports, some state, some iface, some body, some methods, some laws =>
        some { imports, state, iface, body, methods, laws }
      | _, _, _, _, _, _ => none
    else none
  | _ => none

/-- The package has a tree that reads back to it. -/
def packageWire (p : Package) : Bool :=
  p.imports.all (fun d => decide (d.size ≤ importBytesMax)) && tyWire p.state && tyWire p.iface &&
    termWire p.body && p.methods.all labelOk && p.laws.all labelOk

/-- The one codec of a package: the tree stream at the language's bounds. -/
def packageStream : Stream (Tree.Fitting nodeMax depthMax) := Stream.tree nodeMax depthMax (by decide)

/-- The bytes of a package; `none` when it has no tree in bounds (a label, row, index or literal
past its bound, or nested deeper than `depthMax`). -/
def encodePackage (p : Package) : Option ByteArray :=
  if packageWire p then
    if h : (packageTree p).fits nodeMax depthMax then some (packageStream.bytes ⟨packageTree p, h⟩)
    else none
  else none

/-- Exactly one package tree, which reads as a package. -/
def decodePackage (b : ByteArray) : Except Refusal Package :=
  match packageStream.decode b with
  | .error e => .error e
  | .ok t =>
    match packageOf t.val with
    | some p => .ok p
    | none => .error (.rejected 0 "lang/package")

end Wire
end Nanodregg.Lang
