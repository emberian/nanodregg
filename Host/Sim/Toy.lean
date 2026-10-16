/-
# Host.Sim.Toy — toy parameters for driving the real loop through the real `World.admit`

Digests are `Nat` (64-bit FNV-1a), and the batch record is a minimal encoding of the turn shape the
simulation generates (txId, window, nullifiers, charge; no cells). These are PARAMETERS of the one
pipeline, not a second kernel: `World.admit`, `admitBatch`, `serve`, `Log.frame` and `recover` are
the deployed definitions. Replaced by CODEC's digest/turn codec and KERNEL's `Sim` generator when
those land.
-/
import Kernel.World
import Host.Log
import Codec.Stream

namespace Nanodregg.Host.Sim

open Nanodregg.Kernel

def fnv (b : ByteArray) : Nat :=
  (b.foldl (fun h x => ((h ^^^ x.toUInt64) * 1099511628211)) (14695981039346656037 : UInt64)).toNat

/-- CODEC's little-endian `u64` of `n mod 2^64`. -/
def le64 (n : Nat) : ByteArray := Codec.Stream.u64.bytes (UInt64.ofNat n)

private theorem size_le64 (n : Nat) : (le64 n).size = 8 := rfl

/-- The u64 at `off` (callers check the eight bytes are there; none reads as 0). -/
def ofLe64 (b : ByteArray) (off : Nat) : Nat :=
  match Codec.Stream.u64.get b off with
  | .ok (v, _) => v.toNat
  | .error _ => 0

/-- The simulated turn shape. -/
def turnBytes (t : Turn Nat) : ByteArray :=
  le64 t.txId ++ le64 t.notBefore ++ le64 t.validUntil ++ le64 t.nullifiers.length
    ++ t.nullifiers.foldl (fun acc n => acc ++ le64 n) ByteArray.empty ++ le64 t.charge

def env : Env Nat where
  hash := fun dom b => fnv (dom.toUTF8 ++ b)
  bytes := le64
  turnBytes := turnBytes
  cellBytes c := le64 c.weight

def mkTurn (txId notBefore validUntil : Nat) (nullifiers : List Nat) : Turn Nat :=
  let t : Turn Nat := { txId, notBefore, validUntil, pins := [], creates := [], legs := [],
                        retires := [], nullifiers, charge := 0, event := ByteArray.empty }
  { t with charge := t.weight }

/-- A batch record: the count, then each turn. -/
def record (_ : World Nat) (ts : Array (Turn Nat)) : ByteArray :=
  ts.foldl (fun acc t => acc ++ turnBytes t) (le64 ts.size)

/-- The inverse of `record` on the simulated shape (fuel = the record's size). -/
def decodeRecord (b : ByteArray) : Option (List (Turn Nat)) :=
  if b.size < 8 then none else go (ofLe64 b 0) 8 []
where
  go : Nat → Nat → List (Turn Nat) → Option (List (Turn Nat))
    | 0, off, acc => if off = b.size then some acc.reverse else none
    | k + 1, off, acc =>
      if b.size < off + 32 then none else
      let txId := ofLe64 b off
      let nb := ofLe64 b (off + 8)
      let vu := ofLe64 b (off + 16)
      let nn := ofLe64 b (off + 24)
      if 64 < nn ∨ b.size < off + 32 + 8 * nn + 8 then none else
      let ns := (List.range nn).map fun i => ofLe64 b (off + 32 + 8 * i)
      let t := mkTurn txId nb vu ns
      if ofLe64 b (off + 32 + 8 * nn) ≠ t.charge then none else
      go k (off + 32 + 8 * nn + 8) (t :: acc)

/-- A toy sealer: FNV of the input, as 32 bytes. -/
def sealer : Log.Sealer where
  tag b := le64 (fnv b) ++ le64 (fnv (b.push 1)) ++ le64 (fnv (b.push 2)) ++ le64 (fnv (b.push 3))
  tag_size _ := by simp [ByteArray.size_append, size_le64, Log.tagBytes]

end Nanodregg.Host.Sim
