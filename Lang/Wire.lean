/-
# Lang.Wire — the canonical bytes of types, terms and data (built on CODEC's primitives)

Prefix order, one tag byte per node; integers big-endian fixed width (`Codec.Stream.u8/u32/u64`);
labels and byte strings length-prefixed (`Codec.Stream.bytesOf`). Readers are one pass over the
input, never copy it, and are bounded: a term or type deeper than `depthMax` is refused by name
(`pastBound`), so decoding does bounded recursion (law 4). A label that is not UTF-8 is refused
(`rejected … "label"`).

Data is written TYPE-DIRECTED: the reader knows the type, so a record is its fields in row order
with no labels and a sum is its arm's index then the payload. A state slot holds exactly one
field's data.

The CODEC family has no recursive combinator yet (proposals/lang.md asks for one); until then
this module is the one recursive codec, written only from CODEC's primitives.
-/
import Codec.Stream
import Lang.Data

namespace Nanodregg.Lang.Wire

open Nanodregg.Codec

/-- The deepest type or term a reader accepts. -/
def depthMax : Nat := 1024
/-- A label is at most 64 bytes of UTF-8. -/
def labelBytesMax : Nat := 64
/-- At most 256 fields, arms or row entries per node. -/
def rowMax : Nat := 256

abbrev Read (α : Type) := Except Refusal (α × Nat)

/-! ## Leaves -/

def putU8 (v : Nat) (buf : ByteArray) : ByteArray := Stream.u8.put (UInt8.ofNat v) buf
def putU32 (v : Nat) (buf : ByteArray) : ByteArray := Stream.u32.put (UInt32.ofNat v) buf
def putU64 (v : Nat) (buf : ByteArray) : ByteArray := Stream.u64.put (UInt64.ofNat v) buf

def putRaw (s : ByteArray) (buf : ByteArray) : ByteArray :=
  Stream.u32.put (UInt32.ofNat s.size) buf ++ s

def putLabel (ℓ : Label) (buf : ByteArray) : ByteArray := putRaw ℓ.toUTF8 buf

def getU8 (b : ByteArray) (i : Nat) : Read Nat :=
  (Stream.u8.get b i).map fun (v, j) => (v.toNat, j)

def getU32 (b : ByteArray) (i : Nat) : Read Nat :=
  (Stream.u32.get b i).map fun (v, j) => (v.toNat, j)

def getU64 (b : ByteArray) (i : Nat) : Read Nat :=
  (Stream.u64.get b i).map fun (v, j) => (v.toNat, j)

def getRaw (max : Nat) (b : ByteArray) (i : Nat) : Read ByteArray :=
  match getU32 b i with
  | .error e => .error e
  | .ok (n, j) =>
    if n ≤ max then
      if j + n ≤ b.size then .ok (b.extract j (j + n), j + n) else .error (.truncated j n)
    else .error (.pastBound i max n)

def getLabel (b : ByteArray) (i : Nat) : Read Label :=
  match getRaw labelBytesMax b i with
  | .error e => .error e
  | .ok (s, j) =>
    match String.fromUTF8? s with
    | some ℓ => .ok (ℓ, j)
    | none => .error (.rejected i "label")

def getCount (b : ByteArray) (i : Nat) : Read Nat :=
  match getU32 b i with
  | .error e => .error e
  | .ok (n, j) => if n ≤ rowMax then .ok (n, j) else .error (.pastBound i rowMax n)

/-! ## Types -/

mutual
def putTy : Ty → ByteArray → ByteArray
  | .nat, buf => putU8 0 buf
  | .bool, buf => putU8 1 buf
  | .bytes, buf => putU8 2 buf
  | .fn a c, buf => putTy c (putTy a (putU8 3 buf))
  | .record r, buf => putTyRow r (putU32 r.length (putU8 4 buf))
  | .sum r, buf => putTyRow r (putU32 r.length (putU8 5 buf))

def putTyRow : List (Label × Ty) → ByteArray → ByteArray
  | [], buf => buf
  | (ℓ, t) :: r, buf => putTyRow r (putTy t (putLabel ℓ buf))
end

mutual
def getTy (b : ByteArray) : Nat → Nat → Read Ty
  | 0, i => .error (.pastBound i depthMax (depthMax + 1))
  | d + 1, i =>
    match getU8 b i with
    | .error e => .error e
    | .ok (0, j) => .ok (.nat, j)
    | .ok (1, j) => .ok (.bool, j)
    | .ok (2, j) => .ok (.bytes, j)
    | .ok (3, j) =>
      match getTy b d j with
      | .error e => .error e
      | .ok (a, k) =>
        match getTy b d k with
        | .error e => .error e
        | .ok (c, l) => .ok (.fn a c, l)
    | .ok (4, j) =>
      match getCount b j with
      | .error e => .error e
      | .ok (n, k) => (getTyRow b d n k).map fun (r, l) => (.record r, l)
    | .ok (5, j) =>
      match getCount b j with
      | .error e => .error e
      | .ok (n, k) => (getTyRow b d n k).map fun (r, l) => (.sum r, l)
    | .ok (t, _) => .error (.badTag i (UInt8.ofNat t))

def getTyRow (b : ByteArray) (d : Nat) : Nat → Nat → Read (List (Label × Ty))
  | 0, i => .ok ([], i)
  | n + 1, i =>
    match getLabel b i with
    | .error e => .error e
    | .ok (ℓ, j) =>
      match getTy b d j with
      | .error e => .error e
      | .ok (t, k) =>
        match getTyRow b d n k with
        | .error e => .error e
        | .ok (r, l) => .ok ((ℓ, t) :: r, l)
end

/-! ## Terms -/

def primCode : Prim → Nat
  | .add => 0 | .sub => 1 | .mul => 2 | .div => 3 | .mod => 4
  | .eq => 5 | .lt => 6 | .le => 7 | .beq => 8 | .cat => 9

def primOf : Nat → Option Prim
  | 0 => some .add | 1 => some .sub | 2 => some .mul | 3 => some .div | 4 => some .mod
  | 5 => some .eq | 6 => some .lt | 7 => some .le | 8 => some .beq | 9 => some .cat
  | _ => none

mutual
def putTerm : Term → ByteArray → ByteArray
  | .var i, buf => putU32 i (putU8 0 buf)
  | .lam a t, buf => putTerm t (putTy a (putU8 1 buf))
  | .app f a, buf => putTerm a (putTerm f (putU8 2 buf))
  | .fix t, buf => putTerm t (putU8 3 buf)
  | .nat n, buf => putU64 n (putU8 4 buf)
  | .bool v, buf => putU8 (if v then 1 else 0) (putU8 5 buf)
  | .bytes s, buf => putRaw s (putU8 6 buf)
  | .prim p a c, buf => putTerm c (putTerm a (putU8 (primCode p) (putU8 7 buf)))
  | .record fs, buf => putFields fs (putU32 fs.length (putU8 8 buf))
  | .get t ℓ, buf => putLabel ℓ (putTerm t (putU8 9 buf))
  | .extend t fs, buf => putFields fs (putU32 fs.length (putTerm t (putU8 10 buf)))
  | .inj a ℓ t, buf => putTerm t (putLabel ℓ (putTy a (putU8 11 buf)))
  | .case t arms, buf => putFields arms (putU32 arms.length (putTerm t (putU8 12 buf)))
  | .ite c t e, buf => putTerm e (putTerm t (putTerm c (putU8 13 buf)))
  | .ref i, buf => putU32 i (putU8 14 buf)

def putFields : List (Label × Term) → ByteArray → ByteArray
  | [], buf => buf
  | (ℓ, t) :: fs, buf => putFields fs (putTerm t (putLabel ℓ buf))
end

mutual
def getTerm (b : ByteArray) : Nat → Nat → Read Term
  | 0, i => .error (.pastBound i depthMax (depthMax + 1))
  | d + 1, i =>
    match getU8 b i with
    | .error e => .error e
    | .ok (0, j) => (getU32 b j).map fun (n, k) => (.var n, k)
    | .ok (1, j) =>
      match getTy b d j with
      | .error e => .error e
      | .ok (a, k) => (getTerm b d k).map fun (t, l) => (.lam a t, l)
    | .ok (2, j) =>
      match getTerm b d j with
      | .error e => .error e
      | .ok (f, k) => (getTerm b d k).map fun (a, l) => (.app f a, l)
    | .ok (3, j) => (getTerm b d j).map fun (t, k) => (.fix t, k)
    | .ok (4, j) => (getU64 b j).map fun (n, k) => (.nat n, k)
    | .ok (5, j) =>
      match getU8 b j with
      | .ok (0, k) => .ok (.bool false, k)
      | .ok (1, k) => .ok (.bool true, k)
      | .ok (t, _) => .error (.badTag j (UInt8.ofNat t))
      | .error e => .error e
    | .ok (6, j) => (getRaw Bounds.bytesMax b j).map fun (s, k) => (.bytes s, k)
    | .ok (7, j) =>
      match getU8 b j with
      | .error e => .error e
      | .ok (c, k) =>
        match primOf c with
        | none => .error (.badTag j (UInt8.ofNat c))
        | some p =>
          match getTerm b d k with
          | .error e => .error e
          | .ok (x, l) => (getTerm b d l).map fun (y, m) => (.prim p x y, m)
    | .ok (8, j) =>
      match getCount b j with
      | .error e => .error e
      | .ok (n, k) => (getFields b d n k).map fun (fs, l) => (.record fs, l)
    | .ok (9, j) =>
      match getTerm b d j with
      | .error e => .error e
      | .ok (t, k) => (getLabel b k).map fun (ℓ, l) => (.get t ℓ, l)
    | .ok (10, j) =>
      match getTerm b d j with
      | .error e => .error e
      | .ok (t, k) =>
        match getCount b k with
        | .error e => .error e
        | .ok (n, l) => (getFields b d n l).map fun (fs, m) => (.extend t fs, m)
    | .ok (11, j) =>
      match getTy b d j with
      | .error e => .error e
      | .ok (a, k) =>
        match getLabel b k with
        | .error e => .error e
        | .ok (ℓ, l) => (getTerm b d l).map fun (t, m) => (.inj a ℓ t, m)
    | .ok (12, j) =>
      match getTerm b d j with
      | .error e => .error e
      | .ok (t, k) =>
        match getCount b k with
        | .error e => .error e
        | .ok (n, l) => (getFields b d n l).map fun (arms, m) => (.case t arms, m)
    | .ok (13, j) =>
      match getTerm b d j with
      | .error e => .error e
      | .ok (c, k) =>
        match getTerm b d k with
        | .error e => .error e
        | .ok (t, l) => (getTerm b d l).map fun (e, m) => (.ite c t e, m)
    | .ok (14, j) => (getU32 b j).map fun (n, k) => (.ref n, k)
    | .ok (t, _) => .error (.badTag i (UInt8.ofNat t))

def getFields (b : ByteArray) (d : Nat) : Nat → Nat → Read (List (Label × Term))
  | 0, i => .ok ([], i)
  | n + 1, i =>
    match getLabel b i with
    | .error e => .error e
    | .ok (ℓ, j) =>
      match getTerm b d j with
      | .error e => .error e
      | .ok (t, k) =>
        match getFields b d n k with
        | .error e => .error e
        | .ok (fs, l) => .ok ((ℓ, t) :: fs, l)
end

/-! ## Data, type-directed -/

/-- The index of a label in a row. -/
def indexOf (ℓ : Label) : List (Label × Ty) → Nat
  | [] => 0
  | (k, _) :: r => if ℓ = k then 0 else indexOf ℓ r + 1

mutual
/-- Data at a type; data that does not fit the type writes nothing for the misfit part (the
writer is only ever given checked data: `Machine.extract` produced it at this type). -/
def putData : Ty → Data → ByteArray → ByteArray
  | .nat, .nat n, buf => putU64 n buf
  | .bool, .bool v, buf => putU8 (if v then 1 else 0) buf
  | .bytes, .bytes s, buf => putRaw s buf
  | .record r, .record fs, buf => putDataRow r fs buf
  | .sum r, .inj ℓ d, buf => putArm r ℓ d (putU32 (indexOf ℓ r) buf)
  | _, _, buf => buf

def putDataRow : List (Label × Ty) → List (Label × Data) → ByteArray → ByteArray
  | (_, t) :: r, (_, d) :: fs, buf => putDataRow r fs (putData t d buf)
  | _, _, buf => buf

def putArm : List (Label × Ty) → Label → Data → ByteArray → ByteArray
  | [], _, _, buf => buf
  | (k, t) :: r, ℓ, d, buf => if ℓ = k then putData t d buf else putArm r ℓ d buf
end

mutual
def getData (b : ByteArray) : Ty → Nat → Read Data
  | .nat, i => (getU64 b i).map fun (n, j) => (.nat n, j)
  | .bool, i =>
    match getU8 b i with
    | .ok (0, j) => .ok (.bool false, j)
    | .ok (1, j) => .ok (.bool true, j)
    | .ok (t, _) => .error (.badTag i (UInt8.ofNat t))
    | .error e => .error e
  | .bytes, i => (getRaw Bounds.bytesMax b i).map fun (s, j) => (.bytes s, j)
  | .record r, i => (getDataRow b r i).map fun (fs, j) => (.record fs, j)
  | .sum r, i =>
    match getU32 b i with
    | .error e => .error e
    | .ok (n, j) => getArm b r r n j
  | .fn _ _, i => .error (.rejected i "function in data")

def getDataRow (b : ByteArray) : List (Label × Ty) → Nat → Read (List (Label × Data))
  | [], i => .ok ([], i)
  | (ℓ, t) :: r, i =>
    match getData b t i with
    | .error e => .error e
    | .ok (d, j) => (getDataRow b r j).map fun (fs, k) => ((ℓ, d) :: fs, k)

/-- The arm at index `n` of `full`'s suffix; refused unless it is the FIRST arm with its label
(`rejected … "arm"`), so the label names the arm the machine's `case` will take. -/
def getArm (b : ByteArray) (full : List (Label × Ty)) : List (Label × Ty) → Nat → Nat → Read Data
  | [], n, i => .error (.badTag i (UInt8.ofNat n))
  | (ℓ, t) :: _, 0, i =>
    if Row.find? ℓ full = some t then (getData b t i).map fun (d, j) => (.inj ℓ d, j)
    else .error (.rejected i "arm")
  | _ :: r, n + 1, i => getArm b full r n i
end

/-- Exactly one value, nothing after it. -/
def whole {α : Type} (r : Read α) (b : ByteArray) : Except Refusal α :=
  match r with
  | .ok (v, j) => if j = b.size then .ok v else .error (.trailing j)
  | .error e => .error e

def encodeData (T : Ty) (d : Data) : ByteArray := putData T d ByteArray.empty
def decodeData (T : Ty) (b : ByteArray) : Except Refusal Data := whole (getData b T 0) b

end Nanodregg.Lang.Wire
