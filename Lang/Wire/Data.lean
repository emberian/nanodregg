/-
# Lang.Wire.Data — data at a type, as a CODEC stream built from the type

Data is written TYPE-DIRECTED and needs no recursive codec: the reader knows the type, and the type
is finite, so `dataStream T` is a composition of CODEC's ordinary combinators by recursion on `T`.
A natural is `u64`, a boolean `bool`, a byte string `bytesOf bytesMax`, a record the `product` of its
fields in row order (no labels), a sum the nested `sum` of its arms (arm `i` is `i` bytes of 1 and a
0, then the payload). A function type has no data. So the stream's `Shape` IS the type's structure,
and its canonicity is the combinators' (`Lang.Proofs.Data.dataStream_lawful`).

`DataAt T` is the stream's value type; `toData` names it as machine `Data` (the labels come from
`T`) and `ofData` reads machine `Data` back at `T`. Only a CANONICAL type (`Ty.wf`: ascending, hence
distinct labels) has a data codec: in a row with a repeated label, two arms would name the same
`Data`, so `decodeData`/`encodeData` refuse a non-canonical type.
-/
import Codec.Stream
import Lang.Data

namespace Nanodregg.Lang.Wire

open Nanodregg.Codec

mutual
/-- The values of data type `T`, shaped like `T`. -/
def DataAt : Ty → Type
  | .nat => UInt64
  | .bool => Bool
  | .bytes => Bytes Bounds.bytesMax
  | .fn _ _ => Empty
  | .record r => RowAt r
  | .sum r => ArmAt r

def RowAt : List (Label × Ty) → Type
  | [] => Unit
  | (_, t) :: r => DataAt t × RowAt r

def ArmAt : List (Label × Ty) → Type
  | [] => Empty
  | (_, t) :: r => DataAt t ⊕ ArmAt r
end

/-- The stream with no values: every input is refused. -/
def noData : Stream Empty := Stream.refine "lang/data: no value" Stream.unit (fun _ => none) Empty.elim

mutual
def dataStream : (T : Ty) → Stream (DataAt T)
  | .nat => Stream.u64
  | .bool => Stream.bool
  | .bytes => Stream.bytesOf Bounds.bytesMax (by decide)
  | .fn _ _ => noData
  | .record r => rowStream r
  | .sum r => armStream r

def rowStream : (r : List (Label × Ty)) → Stream (RowAt r)
  | [] => Stream.unit
  | (_, t) :: r => Stream.product (dataStream t) (rowStream r)

def armStream : (r : List (Label × Ty)) → Stream (ArmAt r)
  | [] => noData
  | (_, t) :: r => Stream.sum (dataStream t) (armStream r)
end

mutual
/-- A value of `T` as machine data. -/
def toData : (T : Ty) → DataAt T → Data
  | .nat, n => .nat n.toNat
  | .bool, b => .bool b
  | .bytes, s => .bytes s.val
  | .fn _ _, e => nomatch e
  | .record r, x => .record (rowToData r x)
  | .sum r, x => armToData r x

def rowToData : (r : List (Label × Ty)) → RowAt r → List (Label × Data)
  | [], () => []
  | (ℓ, t) :: r, (x, y) => (ℓ, toData t x) :: rowToData r y

def armToData : (r : List (Label × Ty)) → ArmAt r → Data
  | [], e => nomatch e
  | (ℓ, t) :: _, .inl x => .inj ℓ (toData t x)
  | _ :: r, .inr y => armToData r y
end

mutual
/-- Machine data read at `T`: `none` unless it has exactly `T`'s shape, labels and bounds. -/
def ofData : (T : Ty) → Data → Option (DataAt T)
  | .nat, .nat n => if h : n < 2 ^ 64 then some (UInt64.ofNatLT n h) else none
  | .bool, .bool b => some b
  | .bytes, .bytes s => if h : s.size ≤ Bounds.bytesMax then some ⟨s, h⟩ else none
  | .record r, .record fs => rowOfData r fs
  | .sum r, .inj ℓ d => armOfData r ℓ d
  | _, _ => none

def rowOfData : (r : List (Label × Ty)) → List (Label × Data) → Option (RowAt r)
  | [], [] => some ()
  | (ℓ, t) :: r, (k, d) :: fs =>
    if ℓ = k then
      match ofData t d, rowOfData r fs with
      | some x, some y => some (x, y)
      | _, _ => none
    else none
  | _, _ => none

def armOfData : (r : List (Label × Ty)) → Label → Data → Option (ArmAt r)
  | [], _, _ => none
  | (k, t) :: r, ℓ, d => if ℓ = k then (ofData t d).map .inl else (armOfData r ℓ d).map .inr
end

/-- The bytes of data `d` at canonical type `T`; `none` if `T` is not canonical or `d` is not a
value of `T`. -/
def encodeData (T : Ty) (d : Data) : Option ByteArray :=
  if T.wf then (ofData T d).map (dataStream T).bytes else none

/-- Exactly one value of canonical type `T`, nothing after it. -/
def decodeData (T : Ty) (b : ByteArray) : Except Refusal Data :=
  if T.wf then ((dataStream T).decode b).map (toData T) else .error (.rejected 0 "lang/data: type")

end Nanodregg.Lang.Wire
