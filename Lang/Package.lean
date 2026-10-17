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

/-- What a law and a method see of the call: the signing member and whose authority it uses. -/
def reqTy : Ty := .record [("agent", .bytes), ("principal", .bytes)]

/-- A law's verdict: `ok`, or `refused` with the author's reason. -/
def verdictTy : Ty := .sum [("ok", .record []), ("refused", .bytes)]

def lawTy (S : Ty) : Ty := .fn S (.fn S (.fn reqTy verdictTy))

/-- A method's type for argument type `A`. -/
def methodTy (S A : Ty) : Ty := .fn S (.fn A (.fn reqTy S))

def importsMax : Nat := 16
def methodsMax : Nat := 64
def lawsMax : Nat := 16

/-- Why `install` refuses a package (as `Refusal.program` text on the wire). -/
inductive CheckError
  | tooManyImports | tooManyMethods | tooManyLaws
  | stateNotData | ifaceNotRecord
  | illTyped
  | noMethod (label : Label)
  | badMethod (label : Label)
  | noLaw (label : Label)
  | badLaw (label : Label)
  deriving DecidableEq, Repr

def CheckError.text : CheckError → String
  | .tooManyImports => "imports" | .tooManyMethods => "methods" | .tooManyLaws => "laws"
  | .stateNotData => "state type" | .ifaceNotRecord => "interface type"
  | .illTyped => "body does not check at its interface"
  | .noMethod ℓ => s!"no method {ℓ}" | .badMethod ℓ => s!"method {ℓ} has the wrong type"
  | .noLaw ℓ => s!"no law {ℓ}" | .badLaw ℓ => s!"law {ℓ} has the wrong type"

def isRecordData : Ty → Bool
  | t@(.record _) => t.wf && t.isData
  | _ => false

/-- The argument type of a method field, if it has a method's shape over state `S`. -/
def methodArg (S : Ty) : Ty → Option Ty
  | .fn S' (.fn A (.fn R S'')) =>
      if S' = S ∧ R = reqTy ∧ S'' = S ∧ A.isData then some A else none
  | _ => none

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
checks at its interface (`check`), then the fields. -/
def Package.checkWith (ifaces : List Ty) (p : Package) : Except CheckError Unit :=
  match p.checkShape, check ifaces p.body p.iface with
  | .error e, _ => .error e
  | .ok (), false => .error .illTyped
  | .ok (), true => p.checkFields

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

/-! ## Wire -/

namespace Wire
open Nanodregg.Codec

def putLabels (ls : List Label) (buf : ByteArray) : ByteArray :=
  ls.foldl (fun b ℓ => putLabel ℓ b) (putU32 ls.length buf)

def getLabels (b : ByteArray) : Nat → Nat → Read (List Label)
  | 0, i => .ok ([], i)
  | n + 1, i =>
    match getLabel b i with
    | .error e => .error e
    | .ok (ℓ, j) => (getLabels b n j).map fun (ls, k) => (ℓ :: ls, k)

/-- Import ids: each its digest's bytes, length-prefixed (32 for the deployed digest; any
digest the kernel's `digestOf` accepts). -/
def getDigests (b : ByteArray) : Nat → Nat → Read (List ByteArray)
  | 0, i => .ok ([], i)
  | n + 1, i =>
    match getRaw 32 b i with
    | .error e => .error e
    | .ok (d, j) => (getDigests b n j).map fun (ds, k) => (d :: ds, k)

/-- `imports` (count, then each id length-prefixed), state, interface, body, methods, laws. -/
def encodePackage (p : Package) : ByteArray :=
  let b0 := p.imports.foldl (fun b d => putRaw d b) (putU32 p.imports.length ByteArray.empty)
  putLabels p.laws (putLabels p.methods (putTerm p.body (putTy p.iface (putTy p.state b0))))

def getPackage (b : ByteArray) (i : Nat) : Except Refusal (Package × Nat) := do
  let (n, i) ← getCount b i
  let (imports, i) ← getDigests b n i
  let (state, i) ← getTy b depthMax i
  let (iface, i) ← getTy b depthMax i
  let (body, i) ← getTerm b depthMax i
  let (nm, i) ← getCount b i
  let (methods, i) ← getLabels b nm i
  let (nl, i) ← getCount b i
  let (laws, i) ← getLabels b nl i
  pure ({ imports, state, iface, body, methods, laws }, i)

def decodePackage (b : ByteArray) : Except Refusal Package := whole (getPackage b 0) b

end Wire
end Nanodregg.Lang
