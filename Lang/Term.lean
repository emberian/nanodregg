/-
# Lang.Term — the core term language (DECISIONS LANG-1)

Fifteen constructors. De Bruijn variables; `lam` and `inj` carry their types so checking is a
function with no inference of annotations. `fix t` ties the record knot: `t : R → R` for a record
type `R`, and the knot is the final self of open recursion (`mix l u` is the lambda
`λself. λsuper. u self (l self super)`, which the authoring tool writes; it is not a constructor).
`ref i` is the `i`-th package of the closure being run (`Lang.Package`), so a package's identity
commits to its imports by digest while the term holds no digest.
-/
import Lang.Ty

namespace Nanodregg.Lang

/-- The strict binary primitives. Each is O(1) on bounded operands. -/
inductive Prim
  | add | sub | mul | div | mod
  | eq | lt | le
  | beq | cat
  deriving DecidableEq, Repr

/-- The operand and result types of a primitive. -/
def Prim.left : Prim → Ty
  | .beq | .cat => .bytes
  | _ => .nat

def Prim.right : Prim → Ty := Prim.left

def Prim.result : Prim → Ty
  | .add | .sub | .mul | .div | .mod => .nat
  | .eq | .lt | .le | .beq => .bool
  | .cat => .bytes

inductive Term
  | var (index : Nat)
  | lam (dom : Ty) (body : Term)
  | app (fn arg : Term)
  | fix (spec : Term)
  | nat (value : Nat)
  | bool (value : Bool)
  | bytes (value : ByteArray)
  | prim (p : Prim) (left right : Term)
  /-- A record of SUSPENDED fields: each is evaluated when selected, never before. -/
  | record (fields : List (Label × Term))
  | get (target : Term) (label : Label)
  /-- Override and extend a record; the new fields are suspended like a record's. -/
  | extend (target : Term) (fields : List (Label × Term))
  | inj (ty : Ty) (label : Label) (payload : Term)
  /-- Every arm binds the payload at index 0; arms follow the sum's labels exactly. -/
  | case (scrutinee : Term) (arms : List (Label × Term))
  | ite (cond whenTrue whenFalse : Term)
  | ref (index : Nat)
  deriving Inhabited

end Nanodregg.Lang
