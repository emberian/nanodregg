/-
# Kernel.Turn — the one log entry

A `Turn` is deterministic data: everything the follower needs to reproduce the World from the
log with `World.admit` alone, and nothing it would have to trust. It carries

* `touches` — every existing (or pinned-absent) cell the turn names, each ONCE: the digest of
  what the signer saw (`pinOf (some cell)`, or `pinOf none` for "this cell does not exist") and
  what the turn does to it (`keep`, `write ops`, `retire`). The pin is the one staleness refusal
  (`Reject.stale`); a turn writes or retires only a cell it observed, so its effect on every cell
  it changes is a function of the observation, and admit looks each cell up exactly once.
* `creates` — cells born by this turn; a ROM cell's id is its content digest (a package's
  identity), any other's is derived from `txId` and the index: ids never need coordination.
  A born id is never also touched (`Reject.bornTouched`).
* `nullifiers` — one-time tokens; each may be spent once in the life of the World.
* `charge` — what the turn pays, which must equal `Turn.weight` exactly: the storage it costs,
  its log record plus everything it can add to the World (KERNEL-12). The signer signs the price.
* `event` — the ingress bytes (the signed call), opaque to the kernel, kept in the log so the
  log alone is the audit trail. No archive beside it.
-/
import Kernel.Cell

namespace Nanodregg.Kernel

/-- What a turn does to a cell it observed. -/
inductive Act
  | keep
  | write (ops : List Op)
  | retire
  deriving DecidableEq

/-- One observed cell: its id, the digest the signer saw, and what the turn does to it. -/
structure Touch (D : Type) where
  cell : D
  seen : D
  act : Act
  deriving DecidableEq

structure Turn (D : Type) where
  txId : D
  notBefore : Nat
  validUntil : Nat
  touches : List (Touch D)
  creates : List Cell
  nullifiers : List D
  charge : Nat
  event : ByteArray
  deriving DecidableEq

/-- Fixed per-field costs, in bytes, for a digest and a counter. -/
def digestWeight : Nat := 32
def counterWeight : Nat := 8

def Act.opsWeight : Act → Nat
  | .write ops => (ops.map Op.weight).sum
  | _ => 0

/-- A touch in the log: id, seen digest, a tag, and the ops of a write. -/
def Touch.weight {D : Type} (x : Touch D) : Nat := 2 * digestWeight + 1 + x.act.opsWeight

/-- What a turn's log record costs: fixed fields, touches, born cells, nullifiers, the charge
and the event. -/
def Turn.logWeight {D : Type} (t : Turn D) : Nat :=
  digestWeight + 2 * counterWeight
    + (t.touches.map Touch.weight).sum
    + (t.creates.map Cell.weight).sum
    + digestWeight * t.nullifiers.length
    + counterWeight
    + t.event.size

/-- A journal entry: transaction id, height, turn digest. -/
def journalWeight : Nat := 2 * digestWeight + counterWeight

/-- The most a turn can add to the World (`Kernel.Proofs.Weight.admit_world_weight`): its
journal entry, each born cell with its id, each write's ops, each spent nullifier. A retirement
and an overwrite only shrink or keep a cell. -/
def Turn.growth {D : Type} (t : Turn D) : Nat :=
  journalWeight
    + (t.creates.map fun c => digestWeight + c.weight).sum
    + (t.touches.map fun x => x.act.opsWeight).sum
    + digestWeight * t.nullifiers.length

/-- The exact charge of a turn: the storage it costs, its log record plus its World growth.
Independent of the charge's value, so a turn can state its own price. -/
def Turn.weight {D : Type} (t : Turn D) : Nat := t.logWeight + t.growth

end Nanodregg.Kernel
