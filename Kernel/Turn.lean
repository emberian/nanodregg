/-
# Kernel.Turn — the one log entry

A `Turn` is deterministic data: everything the follower needs to reproduce the World from the
log with `World.admit` alone, and nothing it would have to trust. It carries

* `touches` — every existing (or pinned-absent) cell the turn names, each ONCE: the digest of
  what the signer saw (`pinOf (some cell)`, or `pinOf none` for "this cell does not exist") and
  what the turn does to it (`keep`, `write ops`, `retire`). The pin is the one staleness refusal
  (`Reject.stale`); a turn writes or retires only a cell it observed, so its effect on every cell
  it changes is a function of the observation, and admit looks each cell up exactly once.
* `creates` — cells born by this turn, each with its id (D5, KERNEL-28: one birth shape). The
  receiver computes the id: a ROM cell's is its content digest (a package's identity, and
  `World.admit` checks it: `notContentId`), an account's is keyed by its owner and denomination,
  any other's is derived from `txId` and the index. A follower's audit re-derives the Turn, so a
  writer cannot choose an id its receiver did not. A born id is never also touched
  (`Reject.bornTouched`).
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
  creates : List (D × Cell)
  nullifiers : List D
  charge : Nat
  event : ByteArray
  deriving DecidableEq

/-- The cells a turn bears, without their ids. -/
def Turn.born {D : Type} (t : Turn D) : List Cell := t.creates.map Prod.snd

/-- Fixed per-field costs, in bytes: a digest (the deployed 32-byte digest), a counter (u64), and
the u32 header of a list or byte string. These are the codec's sizes (`Codec.Kernel`), so a turn's
log weight is its record's byte count. -/
def digestWeight : Nat := 32
def counterWeight : Nat := 8
def headerWeight : Nat := 4

def Act.opsWeight : Act → Nat
  | .write ops => (ops.map Op.weight).sum
  | _ => 0

/-- An act in the log (`Codec.Kernel.act`): a one-byte tag, and a write's op list (its header and
its ops). The header is log bytes only: it is not World growth. -/
def Act.logWeight : Act → Nat
  | .write ops => 1 + headerWeight + (ops.map Op.weight).sum
  | _ => 1

/-- A touch in the log: id, seen digest and the act. -/
def Touch.weight {D : Type} (x : Touch D) : Nat := 2 * digestWeight + x.act.logWeight

/-- What a turn's log record costs, field by field in the codec's order (`Codec.Kernel.turn`):
txId, the window, the touches, the born cells with their ids, the nullifiers (each list with its
header), the charge and the event (with its length). At the deployed digest this is the record's
byte count: CODEC proves `(Codec.Kernel.turn dc).size t = t.logWeight`. -/
def Turn.logWeight {D : Type} (t : Turn D) : Nat :=
  digestWeight + 2 * counterWeight
    + headerWeight + (t.touches.map Touch.weight).sum
    + headerWeight + (t.creates.map fun p => digestWeight + p.2.weight).sum
    + headerWeight + digestWeight * t.nullifiers.length
    + counterWeight
    + headerWeight + t.event.size

/-- The most a turn can add to the World (`Kernel.Proofs.Weight.admit_world_weight`): each born
cell with its id, each write's ops, each spent nullifier. A retirement and an overwrite only
shrink or keep a cell. Its journal entry is not growth: the journal is pruned to the window
(KERNEL-33), a bounded overhead of every World. -/
def Turn.growth {D : Type} (t : Turn D) : Nat :=
  (t.creates.map fun p => digestWeight + p.2.weight).sum
    + (t.touches.map fun x => x.act.opsWeight).sum
    + digestWeight * t.nullifiers.length

/-- The exact charge of a turn: the storage it costs, its log record plus its World growth.
Independent of the charge's value, so a turn can state its own price. -/
def Turn.weight {D : Type} (t : Turn D) : Nat := t.logWeight + t.growth

end Nanodregg.Kernel
