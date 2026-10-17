/-
# Lang.Wire.Data — data at a type, as a CODEC stream built from the type

Data is written TYPE-DIRECTED and needs no recursive codec: the reader knows the type, and the type
is finite, so `dataStream T` is a composition of CODEC's ordinary combinators by recursion on `T`.
A natural is `u64`, a boolean `bool`, a byte string `bytesOf bytesMax`, a record the `product` of its
fields in row order (no labels), a sum CODEC's `choice` over its arms (one tag byte, the arm's
index, then the payload). A function type has no data. So the stream's `Shape` IS the type's structure,
and its canonicity is the combinators' (`Lang.Proofs.Data.dataStream_lawful`).

`DataAt T` is the stream's value type; `toData` names it as machine `Data` (the labels come from
`T`) and `ofData` reads machine `Data` back at `T`. Only a CANONICAL type the wire can carry
(`Ty.wf`: ascending, hence distinct labels; `tyWire`: at most 256 arms, so one tag byte) has a data
codec: in a row with a repeated label two arms would name the same `Data`, so
`decodeData`/`encodeData` refuse any other type.
-/
import Codec.Stream
import Lang.Data
import Lang.Wire

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
  | .sum r => (i : Fin r.length) × ArmAt r i

def RowAt : List (Label × Ty) → Type
  | [] => Unit
  | (_, t) :: r => DataAt t × RowAt r

/-- The payload type of arm `i`. -/
def ArmAt : (r : List (Label × Ty)) → Fin r.length → Type
  | [], i => Fin.elim0 i
  | (_, t) :: _, ⟨0, _⟩ => DataAt t
  | _ :: r, ⟨i + 1, h⟩ => ArmAt r ⟨i, Nat.lt_of_succ_lt_succ h⟩
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
  | .sum r => Stream.choice r.length (armStream r)

def rowStream : (r : List (Label × Ty)) → Stream (RowAt r)
  | [] => Stream.unit
  | (_, t) :: r => Stream.product (dataStream t) (rowStream r)

def armStream : (r : List (Label × Ty)) → (i : Fin r.length) → Stream (ArmAt r i)
  | [], i => Fin.elim0 i
  | (_, t) :: _, ⟨0, _⟩ => dataStream t
  | _ :: r, ⟨i + 1, h⟩ => armStream r ⟨i, Nat.lt_of_succ_lt_succ h⟩
end

mutual
/-- A value of `T` as machine data. -/
def toData : (T : Ty) → DataAt T → Data
  | .nat, n => .nat n.toNat
  | .bool, b => .bool b
  | .bytes, s => .bytes s.val
  | .fn _ _, e => nomatch e
  | .record r, x => .record (rowToData r x)
  | .sum r, ⟨i, x⟩ => armToData r i x

def rowToData : (r : List (Label × Ty)) → RowAt r → List (Label × Data)
  | [], () => []
  | (ℓ, t) :: r, (x, y) => (ℓ, toData t x) :: rowToData r y

def armToData : (r : List (Label × Ty)) → (i : Fin r.length) → ArmAt r i → Data
  | [], i, _ => Fin.elim0 i
  | (ℓ, t) :: _, ⟨0, _⟩, x => .inj ℓ (toData t x)
  | _ :: r, ⟨i + 1, h⟩, x => armToData r ⟨i, Nat.lt_of_succ_lt_succ h⟩ x
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

/-- The FIRST arm labelled `ℓ`, with `d` read at its type. -/
def armOfData : (r : List (Label × Ty)) → Label → Data → Option ((i : Fin r.length) × ArmAt r i)
  | [], _, _ => none
  | (k, t) :: r, ℓ, d =>
    if ℓ = k then (ofData t d).map fun x => ⟨⟨0, Nat.succ_pos _⟩, x⟩
    else (armOfData r ℓ d).map fun ⟨i, y⟩ => ⟨i.succ, y⟩
end

/-- A canonical type the wire can carry: its data codec exists and is canonical. -/
def dataTy (T : Ty) : Bool := T.wf && tyWire T

/-- The bytes of data `d` at type `T`; `none` unless `dataTy T` and `d` is a value of `T`. -/
def encodeData (T : Ty) (d : Data) : Option ByteArray :=
  if dataTy T then (ofData T d).map (dataStream T).bytes else none

/-- Exactly one value of type `T` (refused unless `dataTy T`), nothing after it. -/
def decodeData (T : Ty) (b : ByteArray) : Except Refusal Data :=
  if dataTy T then ((dataStream T).decode b).map (toData T) else .error (.rejected 0 "lang/data: type")

end Nanodregg.Lang.Wire
