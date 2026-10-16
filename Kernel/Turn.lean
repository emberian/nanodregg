/-
# Kernel.Turn — the one log entry

A `Turn` is deterministic data: everything the follower needs to reproduce the World from the
log with `World.admit` alone, and nothing it would have to trust. It carries

* `pins` — the intent's observation: for each cell the turn depends on, the digest of what the
  signer saw (`pinOf (some cell)`, or `pinOf none` for "this cell does not exist"). The pin check
  is the one staleness refusal (`Reject.stale`).
* `creates` — cells born by this turn; a ROM cell's id is its content digest (a package's
  identity), any other's is derived from `txId` and the index: ids never need coordination.
* `legs` — slot operations on existing cells, at most one leg per cell, one op per key.
* `retires` — cells that die; a retired id is never live again.
* `nullifiers` — one-time tokens; each may be spent once in the life of the World.
* `charge` — what the turn pays, which must equal `Turn.weight` exactly: the bytes it adds to
  the log. The signer signs the price.
* `event` — the ingress bytes (the signed call), opaque to the kernel, kept in the log so the
  log alone is the audit trail. No archive beside it.
-/
import Kernel.Cell

namespace Nanodregg.Kernel

structure Leg (D : Type) where
  cell : D
  ops : List Op
  deriving DecidableEq

structure Turn (D : Type) where
  txId : D
  notBefore : Nat
  validUntil : Nat
  pins : List (D × D)
  creates : List Cell
  legs : List (Leg D)
  retires : List D
  nullifiers : List D
  charge : Nat
  event : ByteArray
  deriving DecidableEq

/-- Fixed per-field costs, in bytes, for a digest and a counter. -/
def digestWeight : Nat := 32
def counterWeight : Nat := 8

def Leg.weight {D : Type} (l : Leg D) : Nat :=
  digestWeight + (l.ops.map Op.weight).sum

/-- The exact charge of a turn: the bytes it adds to the log (fixed fields, pins, born cells,
legs, retirements, nullifiers, the charge itself and the event). Independent of the charge's
value, so a turn can state its own price. -/
def Turn.weight {D : Type} (t : Turn D) : Nat :=
  digestWeight + 2 * counterWeight
    + 2 * digestWeight * t.pins.length
    + (t.creates.map Cell.weight).sum
    + (t.legs.map Leg.weight).sum
    + digestWeight * t.retires.length
    + digestWeight * t.nullifiers.length
    + counterWeight
    + t.event.size

end Nanodregg.Kernel
