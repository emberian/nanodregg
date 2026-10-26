/-
# Lang.Term — the core term language (DECISIONS LANG-1)

Eighteen constructors. De Bruijn variables; `lam` and `inj` carry their types so checking is a
function with no inference of annotations. `fix t` ties the record knot: `t : R → R` for a record
type `R`, and the knot is the final self of open recursion (`mix l u` is the lambda
`λself. λsuper. u self (l self super)`, which the authoring tool writes; it is not a constructor).
`ref i` is the `i`-th package of the closure being run (`Lang.Package`), so a package's identity
commits to its imports by digest while the term holds no import's digest.
-/
import Lang.Ty

namespace Nanodregg.Lang

/-- The strict binary primitives. Each is charged its `Lang.primTicks`: one tick, or one per word
of bytes it walks (`beq`, `deq`, `cat`; LANG-64). -/
inductive Prim
  | add | sub | mul | div | mod
  | eq | lt | le
  | beq | cat
  /-- digest equality: the one primitive that consumes ids (LANG-38) -/
  | deq
  /-- `a.size ≤ n` for bytes `a` and a natural `n`: the one byte length the core has, O(1)
  (LANG-51; a bounded text argument is checked by it) -/
  | lenLe
  /-- The three PAYLOAD WRITERS (LANG-87): each appends to its left operand, a byte string, the
  codec's spelling of its right, so a program can write the bytes of a package tree
  (`Lang.Quote`): `u64be buf n` a natural as a datum's eight big-endian bytes (`Stream.u64be`, a
  `nat` literal's payload); `sized buf s` bytes as a length-prefixed payload (`Stream.bytesV`: a
  `bytes` literal's, a label's, a refusal name's); `dsized buf d` an id as one (a `digest`
  literal's: an id's bytes enter a byte string only as a codec payload, never raw). Charged the
  bytes written, as `cat` is; a result past `bytesMax` is refused `tooLarge` and walks nothing. -/
  | u64be | sized | dsized
  deriving DecidableEq, Repr

/-- The operand and result types of a primitive. -/
def Prim.left : Prim → Ty
  | .beq | .cat | .lenLe | .u64be | .sized | .dsized => .bytes
  | .deq => .digest
  | _ => .nat

def Prim.right : Prim → Ty
  | .beq | .cat | .sized => .bytes
  | .deq | .dsized => .digest
  | _ => .nat

def Prim.result : Prim → Ty
  | .add | .sub | .mul | .div | .mod => .nat
  | .eq | .lt | .le | .beq | .deq | .lenLe => .bool
  | .cat | .u64be | .sized | .dsized => .bytes

inductive Term
  | var (index : Nat)
  | lam (dom : Ty) (body : Term)
  | app (fn arg : Term)
  | fix (spec : Term)
  | nat (value : Nat)
  | bool (value : Bool)
  | bytes (value : ByteArray)
  /-- An id literal (a member an allowlist names): checked a digest of the World at install and at
  every load (`Lang.digestLits`), never made from bytes at run time. -/
  | digest (value : ByteArray)
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
  /-- The run ends here, refused by the NAME `why` (LANG-51): a `Fault.refused why`. Typed at its
  annotation, like `inj`; the reason is a literal, so a refusal's name is fixed in the text (law 7). -/
  | refuse (ty : Ty) (why : ByteArray)
  /-- A contextual hole, instantiated by its explicit ordinary substitution. -/
  | hole (name : Nat) (subst : List Term)
  deriving Inhabited

end Nanodregg.Lang
