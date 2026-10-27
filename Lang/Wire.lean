/-
# Lang.Wire — types and terms as CODEC's one recursive codec (`Codec.Tree`, CODEC-9)

A type or a term is a `Codec.Tree`: one node per constructor, its tag byte, its scalar field as a
payload written with CODEC's ordinary codecs (an index as `u32`, a natural as `u64be` as Lang data's
is (LANG-59), a boolean as `bool`, a primitive's code as `u8`, a label or a byte literal as its raw
bytes), and its subterms as children. A row entry `(ℓ, x)` is a FIELD node: the label as payload,
`x` as its one child. The byte-level reading, the depth bound and the size bounds are
`Stream.tree`'s, proved once (`Codec.Stream.tree_lawful`); this module only maps constructors to nodes and back.

`tyOf`/`termOf` accept exactly the trees `tyTree`/`termTree` write for a REPRESENTABLE type or term
(`tyWire`, `termWire`: every label UTF-8 of at most `labelBytesMax` bytes, every row at most
`rowMax` entries, every index below `2^32`, every literal natural below `2^64`). Everything else is
refused (`none`), so one value has one tree and one tree has one value (`Lang.Proofs.Wire`).

Tags (a type's and a term's tag spaces are read at different positions, so they may overlap):

    type  nat 0 · bool 1 · bytes 2 · fn 3 [a c] · record 4 [field*] · sum 5 [field*] · field 6 ℓ [T]
          digest 7
    term  var 0 i · lam 1 [T b] · app 2 [f a] · fix 3 [t] · nat 4 n · bool 5 v · bytes 6 s
          prim 7 code [a b] · record 8 [field*] · get 9 ℓ [t] · extend 10 [t field*] · inj 11 ℓ [T t]
          case 12 [t field*] · ite 13 [c t e] · ref 14 i · field 15 ℓ [t] · digest 16 s
          refuse 17 why [T] · hole 18 i [substitution*]
    prim codes add 0 · sub 1 · mul 2 · div 3 · mod 4 · eq 5 · lt 6 · le 7 · beq 8 · cat 9 · deq 10
          lenLe 11 · u64be 12 · sized 13 · dsized 14
-/
import Codec.Tree
import Lang.Term
import Lang.Bounds

namespace Nanodregg.Lang.Wire

open Nanodregg.Codec

/-- The deepest tree a reader accepts (a package's own node included). -/
def depthMax : Nat := 1024
/-- A label is at most 64 bytes of UTF-8. -/
def labelBytesMax : Nat := 64
/-- At most 256 fields, arms or row entries per node. -/
def rowMax : Nat := 256
/-- The tree's payload and child-list bound: a byte literal fills one kernel slot. -/
def nodeMax : Nat := Bounds.bytesMax

/-! ## Leaves -/

/-- A label is one atom of the text (`labelAtom`) of at most `labelBytesMax` bytes of UTF-8: the one
label rule of the wire, the reader and the printer. -/
def labelOk (ℓ : Label) : Bool := labelAtom ℓ && decide (ℓ.toUTF8.size ≤ labelBytesMax)

def labelOf (p : ByteArray) : Option Label :=
  if p.size ≤ labelBytesMax then
    match String.fromUTF8? p with
    | some ℓ => if labelAtom ℓ then some ℓ else none
    | none => none
  else none

def u32Of (p : ByteArray) : Option Nat :=
  match Stream.u32.decode p with
  | .ok v => some v.toNat
  | .error _ => none

def u64Of (p : ByteArray) : Option Nat :=
  match Stream.u64be.decode p with
  | .ok v => some v.toNat
  | .error _ => none

def boolOf (p : ByteArray) : Option Bool :=
  match Stream.bool.decode p with
  | .ok v => some v
  | .error _ => none

def u32Bytes (n : Nat) : ByteArray := Stream.u32.bytes (UInt32.ofNat n)
def u64Bytes (n : Nat) : ByteArray := Stream.u64be.bytes (UInt64.ofNat n)

def primCode : Prim → UInt8
  | .add => 0 | .sub => 1 | .mul => 2 | .div => 3 | .mod => 4
  | .eq => 5 | .lt => 6 | .le => 7 | .beq => 8 | .cat => 9 | .deq => 10 | .lenLe => 11
  | .u64be => 12 | .sized => 13 | .dsized => 14

def primOf : UInt8 → Option Prim
  | 0 => some .add | 1 => some .sub | 2 => some .mul | 3 => some .div | 4 => some .mod
  | 5 => some .eq | 6 => some .lt | 7 => some .le | 8 => some .beq | 9 => some .cat
  | 10 => some .deq | 11 => some .lenLe | 12 => some .u64be | 13 => some .sized | 14 => some .dsized
  | _ => none

def primOfBytes (p : ByteArray) : Option Prim :=
  match Stream.u8.decode p with
  | .ok c => primOf c
  | .error _ => none

/-! ## Types -/

mutual
def tyTree : Ty → Tree
  | .nat => .node 0 .empty []
  | .bool => .node 1 .empty []
  | .bytes => .node 2 .empty []
  | .digest => .node 7 .empty []
  | .fn a c => .node 3 .empty [tyTree a, tyTree c]
  | .record r => .node 4 .empty (tyRowTree r)
  | .sum r => .node 5 .empty (tyRowTree r)

def tyRowTree : List (Label × Ty) → List Tree
  | [] => []
  | (ℓ, t) :: r => .node 6 ℓ.toUTF8 [tyTree t] :: tyRowTree r
end

mutual
/-- The type a tree writes, if it writes one. -/
def tyOf : Tree → Option Ty
  | .node 0 p [] => if p = .empty then some .nat else none
  | .node 1 p [] => if p = .empty then some .bool else none
  | .node 2 p [] => if p = .empty then some .bytes else none
  | .node 7 p [] => if p = .empty then some .digest else none
  | .node 3 p [a, c] =>
    if p = .empty then
      match tyOf a, tyOf c with
      | some a, some c => some (.fn a c)
      | _, _ => none
    else none
  | .node 4 p cs =>
    if p = .empty ∧ cs.length ≤ rowMax then (tyRowOf cs).map .record else none
  | .node 5 p cs =>
    if p = .empty ∧ cs.length ≤ rowMax then (tyRowOf cs).map .sum else none
  | _ => none

def tyRowOf : List Tree → Option (List (Label × Ty))
  | [] => some []
  | .node 6 p [c] :: cs =>
    match labelOf p, tyOf c, tyRowOf cs with
    | some ℓ, some t, some r => some ((ℓ, t) :: r)
    | _, _, _ => none
  | _ => none
end

mutual
/-- The type has a tree that reads back to it: labels and rows in bounds. -/
def tyWire : Ty → Bool
  | .nat | .bool | .bytes | .digest => true
  | .fn a c => tyWire a && tyWire c
  | .record r => decide (r.length ≤ rowMax) && tyRowWire r
  | .sum r => decide (r.length ≤ rowMax) && tyRowWire r

def tyRowWire : List (Label × Ty) → Bool
  | [] => true
  | (ℓ, t) :: r => labelOk ℓ && tyWire t && tyRowWire r
end

/-- A canonical type the wire can carry: its data codec (`Lang.Wire.Data`) exists and is canonical.
Read here, beside `tyWire`, by the install check of a call slot's argument type (`Lang.callSlotOk`)
and by the codec (`encodeData`/`decodeData`): one predicate (law 1). -/
def dataTy (T : Ty) : Bool := T.wf && tyWire T

/-! ## Terms -/

mutual
def termTree : Term → Tree
  | .var i => .node 0 (u32Bytes i) []
  | .lam a b => .node 1 .empty [tyTree a, termTree b]
  | .app f a => .node 2 .empty [termTree f, termTree a]
  | .fix t => .node 3 .empty [termTree t]
  | .nat n => .node 4 (u64Bytes n) []
  | .bool v => .node 5 (Stream.bool.bytes v) []
  | .bytes s => .node 6 s []
  | .digest s => .node 16 s []
  | .prim op a b => .node 7 (Stream.u8.bytes (primCode op)) [termTree a, termTree b]
  | .record fs => .node 8 .empty (fieldsTree fs)
  | .get t ℓ => .node 9 ℓ.toUTF8 [termTree t]
  | .extend t fs => .node 10 .empty (termTree t :: fieldsTree fs)
  | .inj a ℓ t => .node 11 ℓ.toUTF8 [tyTree a, termTree t]
  | .case t arms => .node 12 .empty (termTree t :: fieldsTree arms)
  | .ite c t e => .node 13 .empty [termTree c, termTree t, termTree e]
  | .ref i => .node 14 (u32Bytes i) []
  | .refuse T w => .node 17 w [tyTree T]
  | .hole n σ => .node 18 (u32Bytes n) (termsTree σ)

def termsTree : List Term → List Tree
  | [] => []
  | t :: ts => termTree t :: termsTree ts

def fieldsTree : List (Label × Term) → List Tree
  | [] => []
  | (ℓ, t) :: fs => .node 15 ℓ.toUTF8 [termTree t] :: fieldsTree fs
end

mutual
/-- The term a tree writes, if it writes one. -/
def termOf : Tree → Option Term
  | .node 0 p [] => (u32Of p).map .var
  | .node 1 p [a, b] =>
    if p = .empty then
      match tyOf a, termOf b with
      | some a, some b => some (.lam a b)
      | _, _ => none
    else none
  | .node 2 p [f, a] =>
    if p = .empty then
      match termOf f, termOf a with
      | some f, some a => some (.app f a)
      | _, _ => none
    else none
  | .node 3 p [t] => if p = .empty then (termOf t).map .fix else none
  | .node 4 p [] => (u64Of p).map .nat
  | .node 5 p [] => (boolOf p).map .bool
  | .node 6 p [] => some (.bytes p)
  | .node 16 p [] => some (.digest p)
  | .node 7 p [a, b] =>
    match primOfBytes p, termOf a, termOf b with
    | some op, some a, some b => some (.prim op a b)
    | _, _, _ => none
  | .node 8 p fs =>
    if p = .empty ∧ fs.length ≤ rowMax then (fieldsOf fs).map .record else none
  | .node 9 p [t] =>
    match labelOf p, termOf t with
    | some ℓ, some t => some (.get t ℓ)
    | _, _ => none
  | .node 10 p (t :: fs) =>
    if p = .empty ∧ fs.length ≤ rowMax then
      match termOf t, fieldsOf fs with
      | some t, some fs => some (.extend t fs)
      | _, _ => none
    else none
  | .node 11 p [a, t] =>
    match labelOf p, tyOf a, termOf t with
    | some ℓ, some a, some t => some (.inj a ℓ t)
    | _, _, _ => none
  | .node 12 p (t :: arms) =>
    if p = .empty ∧ arms.length ≤ rowMax then
      match termOf t, fieldsOf arms with
      | some t, some arms => some (.case t arms)
      | _, _ => none
    else none
  | .node 13 p [c, t, e] =>
    if p = .empty then
      match termOf c, termOf t, termOf e with
      | some c, some t, some e => some (.ite c t e)
      | _, _, _ => none
    else none
  | .node 14 p [] => (u32Of p).map .ref
  | .node 17 p [a] => (tyOf a).map (.refuse · p)
  | .node 18 p ts =>
    if ts.length ≤ rowMax then
      match u32Of p, termsOf ts with
      | some n, some σ => some (.hole n σ)
      | _, _ => none
    else none
  | _ => none

def termsOf : List Tree → Option (List Term)
  | [] => some []
  | t :: ts =>
    match termOf t, termsOf ts with
    | some t, some ts => some (t :: ts)
    | _, _ => none

def fieldsOf : List Tree → Option (List (Label × Term))
  | [] => some []
  | .node 15 p [t] :: fs =>
    match labelOf p, termOf t, fieldsOf fs with
    | some ℓ, some t, some fs => some ((ℓ, t) :: fs)
    | _, _, _ => none
  | _ => none
end

mutual
/-- The term has a tree that reads back to it: indices, literals, labels and rows in bounds. -/
def termWire : Term → Bool
  | .var i | .ref i => decide (i < 2 ^ 32)
  | .lam a b => tyWire a && termWire b
  | .app f a => termWire f && termWire a
  | .fix t => termWire t
  | .nat n => decide (n < 2 ^ 64)
  | .bool _ | .bytes _ | .digest _ => true
  | .prim _ a b => termWire a && termWire b
  | .record fs => decide (fs.length ≤ rowMax) && fieldsWire fs
  | .get t ℓ => labelOk ℓ && termWire t
  | .extend t fs => termWire t && decide (fs.length ≤ rowMax) && fieldsWire fs
  | .inj a ℓ t => tyWire a && labelOk ℓ && termWire t
  | .case t arms => termWire t && decide (arms.length ≤ rowMax) && fieldsWire arms
  | .ite c t e => termWire c && termWire t && termWire e
  | .refuse T _ => tyWire T
  | .hole n σ => decide (n < 2 ^ 32) && decide (σ.length ≤ rowMax) && termsWire σ

def termsWire : List Term → Bool
  | [] => true
  | t :: ts => termWire t && termsWire ts

def fieldsWire : List (Label × Term) → Bool
  | [] => true
  | (ℓ, t) :: fs => labelOk ℓ && termWire t && fieldsWire fs
end

end Nanodregg.Lang.Wire
