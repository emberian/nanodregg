/-
# Host.Sim.Toy — toy parameters for driving the real loop through the real `World.admit`

Digests are `Nat` below `2^64` (64-bit FNV-1a), carried by CODEC's `nat64`; turns, cells and batch
records are CODEC's codecs over it. The tags are FNV, not a MAC. These are PARAMETERS of the one
pipeline, not a second kernel or a second codec: `World.admit`, `admitBatch`, `serve`, `Log.frame`,
`recover`, `Host.Record` and `Host.Base` are the deployed definitions.
-/
import Kernel.World
import Host.Base
import Host.Record
import Codec.Kernel
import Host.Loop

namespace Nanodregg.Host.Sim

open Nanodregg.Kernel

def fnv (b : ByteArray) : Nat :=
  (b.foldl (fun h x => ((h ^^^ x.toUInt64) * 1099511628211)) (14695981039346656037 : UInt64)).toNat

/-- CODEC's little-endian `u64` of `n mod 2^64`. -/
def le64 (n : Nat) : ByteArray := Codec.Stream.u64.bytes (UInt64.ofNat n)

private theorem size_le64 (n : Nat) : (le64 n).size = 8 := rfl

/-- The toy digest's codec. -/
abbrev dc : Codec.Stream Nat := Codec.Stream.nat64

def turnCodec : Codec.Stream (Turn Nat) := Codec.Kernel.turn dc

def env : Env Nat where
  hash := fun dom b => fnv (dom.toUTF8 ++ b)
  bytes := le64
  turnBytes := turnCodec.bytes
  cellBytes := Codec.Kernel.cellBytes

def mkTurn (txId notBefore validUntil : Nat) (nullifiers : List Nat) : Turn Nat :=
  let t : Turn Nat := { txId, notBefore, validUntil, touches := [], creates := [], nullifiers,
                        charge := 0, event := ByteArray.empty }
  { t with charge := t.weight }

/-- A toy tag: FNV of the input under a domain byte, as 32 bytes. -/
def fnvSealer (domain : UInt8) : Log.Sealer where
  tag b := let b := b.push domain
    le64 (fnv b) ++ le64 (fnv (b.push 1)) ++ le64 (fnv (b.push 2)) ++ le64 (fnv (b.push 3))
  tag_size _ := by simp [ByteArray.size_append, size_le64, Log.tagBytes]

def keys : Keys := ⟨fnvSealer 0, fnvSealer 1⟩

/-- Toy numbers: a seal every 2 KiB at least, so a 200-turn scenario seals several times, and a
record bound (4 KiB; a 16-turn batch record is ~1.3 KiB) small enough that `tailMax` is shorter
than the scenario's segment, so plant-tail-too-long can go red. -/
def cadence : Cadence where
  sealMinBytes := 2048
  worldBytesMax := 1 <<< 20
  recordBytesMax := 4096

def world : Codec.Stream (World Nat) := Codec.Kernel.world dc

/-- The toy digest's inverse of `env.bytes`. -/
def digestOf (b : ByteArray) : Option Nat :=
  match dc.decode b with
  | .ok d => some d
  | .error _ => none

/-- How the loop records and indexes a batch. -/
def recorder : Recorder (World Nat) (Turn Nat) where
  encode := Record.encode dc
  mark w := (w.height, env.bytes w.chain)

/-- One batch record folded into the World: what open does per record (the writer's fold). -/
def foldStep : World Nat → ByteArray → Except (Record.Fault (Reject Nat)) (World Nat) :=
  Record.step dc (World.fold env)

end Nanodregg.Host.Sim
