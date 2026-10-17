/-
# Kernel.Value — the kernel's one conserved quantity (LEDGER-2)

A `Discipline.value` cell holds, at three kernel keys, a DENOMINATION (the bytes of the id of the
cell that bore it), a BALANCE (CODEC `i64`) and a FLOOR (CODEC `u64`): the balance may go down to
minus the floor and no further. `World.admit` judges every value cell a turn writes, retires or
bears through the FLOWS it adds to its denomination's sums (the pre-cell's balance and floor
taken away, the post-cell's added), so value is conserved for every writer at once: a receiver,
a package, a forged log. There is no mint and no burn: a well is an account whose floor is its
issuance cap, and issuing is a transfer out of it.
-/
import Kernel.Cell
import Kernel.Bounds
import Codec.Stream

namespace Nanodregg.Kernel

/-- A denomination in a refusal's diagnostic text (`Reject` derives `Repr`): its bytes in hex. Not a
wire form: the wire carries `Reject.name`. -/
instance : Repr ByteArray where
  reprPrec b _ := .text (b.foldl (fun s x =>
    let d := fun (n : UInt8) => if n < 10 then Char.ofNat (48 + n.toNat) else Char.ofNat (87 + n.toNat)
    (s.push (d (x / 16))).push (d (x % 16))) "0x")

/-- What a value cell holds. -/
structure Value where
  denom : ByteArray
  balance : Int
  floor : Nat

namespace Value

/-- The kernel's keys in a value cell; every other slot is RAM. Disjoint from the receive layer's
account layout (owner at 1). -/
def denomKey : Nat := 8
def balanceKey : Nat := 9
def floorKey : Nat := 10

/-- A balance's slot bytes: CODEC's `i64` (the caller keeps the value within `Int64`). -/
def balanceBytes (b : Int) : ByteArray := Nanodregg.Codec.Stream.i64.bytes (Int64.ofInt b)

def balanceOf (b : ByteArray) : Option Int :=
  match Nanodregg.Codec.Stream.i64.decode b with
  | .ok v => some v.toInt
  | .error _ => none

/-- A floor's slot bytes: CODEC's `u64`. -/
def floorBytes (f : Nat) : ByteArray := Nanodregg.Codec.Stream.u64.bytes (UInt64.ofNat f)

def floorOf (b : ByteArray) : Option Nat :=
  match Nanodregg.Codec.Stream.u64.decode b with
  | .ok v => some v.toNat
  | .error _ => none

/-- A balance an `i64` can hold. -/
def fits (b : Int) : Bool := decide (-2 ^ 63 ≤ b ∧ b < 2 ^ 63)

/-- The value a cell holds: only a `value` cell holds one, and only when its three slots decode
and its denomination is within `Bounds.denomBytesMax`. -/
def ofCell (c : Cell) : Option Value :=
  if c.discipline = .value then
    match c.slots.get denomKey, (c.slots.get balanceKey).bind balanceOf,
        (c.slots.get floorKey).bind floorOf with
    | some d, some b, some f => if d.size ≤ Bounds.denomBytesMax then some ⟨d, b, f⟩ else none
    | _, _, _ => none
  else none

/-- Within its floor: the balance is at least minus the floor. -/
def withinFloor (v : Value) : Bool := decide (-(v.floor : Int) ≤ v.balance)

end Value

/-- What one cell adds to its denomination's two sums. -/
structure Flow where
  denom : ByteArray
  balance : Int
  floor : Int

def Value.flow (v : Value) : Flow := ⟨v.denom, v.balance, v.floor⟩

def Flow.neg (f : Flow) : Flow := ⟨f.denom, -f.balance, -f.floor⟩

/-- The flows of one cell changing from `pre` to `post` (`none`: absent or retired): its old value
taken away, its new value added. A cell that is not a value cell flows nothing. -/
def flowsOf (pre post : Option Cell) : List Flow :=
  ((pre.bind Value.ofCell).map fun v => v.flow.neg).toList ++
    ((post.bind Value.ofCell).map Value.flow).toList

/-- What flows `fs` add to denomination `d`'s sum of `g` (a flow's balance, or its floor). -/
def sumBy (g : Flow → Int) (d : ByteArray) (fs : List Flow) : Int :=
  (fs.map fun f => if f.denom = d then g f else 0).sum

/-- Add one flow into a per-denomination association list. -/
def addFlow : List Flow → Flow → List Flow
  | [], f => [f]
  | a :: rest, f =>
      if a.denom = f.denom then { a with balance := a.balance + f.balance, floor := a.floor + f.floor } :: rest
      else a :: addFlow rest f

/-- Accumulate flows into `acc`, or `none` once more than `Bounds.denomsMax` denominations are
in it: each step works on a list of at most that many, so the whole is O(flows). -/
def accumulateFrom (acc : List Flow) : List Flow → Option (List Flow)
  | [] => some acc
  | f :: fs =>
      let acc' := addFlow acc f
      if acc'.length ≤ Bounds.denomsMax then accumulateFrom acc' fs else none

/-- The per-denomination sums of a turn's flows (`none`: too many denominations). -/
def accumulate (fs : List Flow) : Option (List Flow) := accumulateFrom [] fs

end Nanodregg.Kernel
