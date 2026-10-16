/-
# Kernel.Cell — a cell is a small, bounded, canonical map from slot keys to bytes

A cell's slots are a list of `(key, value)` with strictly ascending keys, so two cells with
the same contents are the same value (`=` is extensional) and a cell's encoding is a function
of its contents. A cell is bounded (`Bounds.slotsPerCellMax`), so a list is the right
structure: every operation on a touched cell is O(its size), which is bounded.

What the bytes mean (a balance, a law, a package) is not the kernel's business: the receive
layer decodes slots. The kernel enforces only the cell's `Discipline`.
-/
import Kernel.Bounds

namespace Nanodregg.Kernel

/-- How a cell may change after its birth. -/
inductive Discipline
  /-- never written, never retired: immutable for the life of the World -/
  | rom
  /-- slots may only be added, never overwritten or erased -/
  | appendOnly
  /-- any slot may be set or erased -/
  | ram
  deriving DecidableEq, Repr

/-- One slot operation of a leg. -/
inductive Op
  | set (key : Nat) (value : ByteArray)
  | erase (key : Nat)
  deriving DecidableEq

def Op.key : Op → Nat
  | .set k _ => k
  | .erase k => k

abbrev Slots := List (Nat × ByteArray)

structure Cell where
  kind : Nat
  discipline : Discipline
  slots : Slots
  deriving DecidableEq

namespace Slots

/-- Strictly ascending keys: the canonical form. -/
def Ascending : Slots → Prop
  | [] => True
  | [_] => True
  | a :: b :: rest => a.1 < b.1 ∧ Ascending (b :: rest)

def ascending : Slots → Bool
  | [] => true
  | [_] => true
  | a :: b :: rest => decide (a.1 < b.1) && ascending (b :: rest)

def get (s : Slots) (k : Nat) : Option ByteArray := s.lookup k

/-- Insert or replace, keeping keys ascending. -/
def set (k : Nat) (v : ByteArray) : Slots → Slots
  | [] => [(k, v)]
  | (k', v') :: rest =>
      if k < k' then (k, v) :: (k', v') :: rest
      else if k = k' then (k, v) :: rest
      else (k', v') :: set k v rest

def erase (k : Nat) : Slots → Slots
  | [] => []
  | (k', v') :: rest => if k = k' then rest else (k', v') :: erase k rest

/-- Storage weight of a slot list: four bytes of key and four of length per slot, plus the value. -/
def weight (s : Slots) : Nat := (s.map fun p => 8 + p.2.size).sum

end Slots

/-- The weight of a whole cell: kind, discipline and the slots. -/
def Cell.weight (c : Cell) : Nat := 8 + Slots.weight c.slots

/-- The weight of one operation as written into the log. -/
def Op.weight : Op → Nat
  | .set _ v => 8 + v.size
  | .erase _ => 4

end Nanodregg.Kernel
