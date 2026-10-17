/-
# Kernel.World — the World, its one transition `World.admit`, and `fold`

`World.admit` IS the receive path (law 1): the Host commits exactly what it returns, the
follower and a reopening Host fold the log with it, and nothing else changes a World.

The kernel is generic over the digest `D` and the hash (`Env`) so that theorems can state a
hash collision as an explicit disjunct, and the simulation can run toy parameters through the
same `admit`. There is one deployed `Env` (CODEC's digest and hash).

Order of the checks (each refuses by name, nothing is written before all pass):
bounds → journal (an exact retry is `replayed` whatever else holds) → shape → window → touches
(ONE lookup per touched cell: its pin, the one staleness refusal, then its write or retirement)
→ nullifiers → charge → created ids.
-/
import Std.Data.TreeMap
import Std.Data.TreeSet
import Kernel.Check
import Kernel.Turn
import Codec.Stream

namespace Nanodregg.Kernel

/-- The hash and the canonical encodings the kernel digests. CODEC supplies the deployed one. -/
structure Env (D : Type) where
  /-- the hash under a domain (deployed: cSHAKE256 with the domain as customization string,
  CODEC-7), so domains are separated by the hash, not by byte prefixes -/
  hash : (domain : String) → ByteArray → D
  /-- the digest's canonical bytes (32 for the deployed digest) -/
  bytes : D → ByteArray
  turnBytes : Turn D → ByteArray
  cellBytes : Cell → ByteArray

/-- A cell id's slot in the World: a live cell, or the tombstone of a retired one. -/
inductive Entry
  | live (cell : Cell)
  | tomb
  deriving DecidableEq

/-- Every refusal, by name (law 7). -/
inductive Reject (D : Type)
  | overBound (which : Bound)
  /-- the transaction is already in the journal, admitted at `height` (an exact retry: the
  transaction id is the digest of the signed call, so the same id is the same call) -/
  | replayed (height : Nat)
  /-- a cell is touched twice in one turn -/
  | duplicateTouch (cell : D)
  | duplicateNullifier (nullifier : D)
  | duplicateKey (cell : D) (key : Nat)
  | nonCanonicalCell (index : Nat)
  | outsideWindow
  /-- the cell is not what the signer saw -/
  | stale (cell : D)
  | spent (nullifier : D)
  | chargeMismatch (expected : Nat)
  | overAllowance
  | idTaken (cell : D)
  /-- a born id is also touched: a born cell did not exist to be observed -/
  | bornTouched (cell : D)
  | missingCell (cell : D)
  | romWrite (cell : D)
  | romRetire (cell : D)
  | appendOnly (cell : D) (key : Nat)
  deriving DecidableEq, Repr

/-- The refusal's name on the wire (law 7): its constructor's, arguments dropped
(`Reject.name_injective`). -/
def Reject.name {D : Type} : Reject D → String
  | .overBound _ => "overBound"
  | .replayed _ => "replayed"
  | .duplicateTouch _ => "duplicateTouch"
  | .duplicateNullifier _ => "duplicateNullifier"
  | .duplicateKey _ _ => "duplicateKey"
  | .nonCanonicalCell _ => "nonCanonicalCell"
  | .outsideWindow => "outsideWindow"
  | .stale _ => "stale"
  | .spent _ => "spent"
  | .chargeMismatch _ => "chargeMismatch"
  | .overAllowance => "overAllowance"
  | .idTaken _ => "idTaken"
  | .bornTouched _ => "bornTouched"
  | .missingCell _ => "missingCell"
  | .romWrite _ => "romWrite"
  | .romRetire _ => "romRetire"
  | .appendOnly _ _ => "appendOnly"

variable {D : Type} [Ord D]

structure World (D : Type) [Ord D] where
  cells : Std.TreeMap D Entry compare
  /-- transaction id ↦ (height, turn digest): the replay index -/
  journal : Std.TreeMap D (Nat × D) compare
  spent : Std.TreeSet D compare
  height : Nat
  /-- the log chain after `height` turns -/
  chain : D
  /-- the storage budget left, in bytes -/
  allowance : Nat

/-- The kernel's hash domains. -/
def domGenesis : String := "nanodregg/kernel/genesis/v1"
def domAbsent : String := "nanodregg/kernel/pin-absent/v1"
def domCell : String := "nanodregg/kernel/pin-cell/v1"
def domTurn : String := "nanodregg/kernel/turn/v1"
def domChain : String := "nanodregg/kernel/chain/v1"
def domCellId : String := "nanodregg/kernel/cell-id/v1"
def domRomId : String := "nanodregg/kernel/rom-id/v1"

/-- An index as CODEC's four little-endian bytes (indexes are below `Bounds.createsMax`). -/
def index32 (n : Nat) : ByteArray := Nanodregg.Codec.Stream.u32.bytes (UInt32.ofNat n)

/-- What a pin asserts about a cell: its digest, or the digest of absence. -/
def pinOf (E : Env D) : Option Cell → D
  | none => E.hash domAbsent ByteArray.empty
  | some c => E.hash domCell (E.cellBytes c)

def turnDigest (E : Env D) (t : Turn D) : D := E.hash domTurn (E.turnBytes t)

def chainNext (E : Env D) (prev : D) (t : Turn D) : D :=
  E.hash domChain (E.bytes prev ++ E.bytes (turnDigest E t))

/-- The id of the `i`-th cell a transaction creates. -/
def cellIdOf (E : Env D) (txId : D) (i : Nat) : D :=
  E.hash domCellId (E.bytes txId ++ index32 i)

/-- A ROM cell's id is its content digest: the same immutable content is one cell, whoever
installs it (a package's identity IS its cell id). -/
def romIdOf (E : Env D) (c : Cell) : D := E.hash domRomId (E.cellBytes c)

/-- The id a turn gives its `i`-th born cell: content-addressed for ROM, else derived from the
transaction. -/
def bornId (E : Env D) (txId : D) (p : Cell × Nat) : D :=
  match p.1.discipline with
  | .rom => romIdOf E p.1
  | _ => cellIdOf E txId p.2

def createdIds (E : Env D) (t : Turn D) : List D :=
  t.creates.zipIdx.map (bornId E t.txId)

def createdPairs (E : Env D) (t : Turn D) : List (D × Cell) :=
  (createdIds E t).zip t.creates

namespace World

def genesis (E : Env D) (name : ByteArray) (allowance : Nat) : World D :=
  { cells := {}, journal := {}, spent := {}, height := 0,
    chain := E.hash domGenesis name, allowance }

/-- The live cell at an id, if any (a tombstone reads as absent). -/
def live (w : World D) (c : D) : Option Cell :=
  match w.cells[c]? with
  | some (.live cell) => some cell
  | _ => none

/-- What an entry costs in the World: a live cell its weight, a tombstone nothing beyond its id. -/
def _root_.Nanodregg.Kernel.Entry.weight : Entry → Nat
  | .live c => c.weight
  | .tomb => 0

/-- The weight of a cell map: each entry with its id. -/
def _root_.Nanodregg.Kernel.cellsWeight (m : Std.TreeMap D Entry compare) : Nat :=
  (m.toList.map fun p => digestWeight + p.2.weight).sum

/-- The storage a World holds, by the same per-field costs as `Turn.weight`: each cell entry with
its id, each journal entry, each spent nullifier. A specification measure (O(store)), never
computed on the request path; `Kernel.Proofs.Weight` bounds it by the budget spent. -/
def weight (w : World D) : Nat :=
  cellsWeight w.cells + journalWeight * w.journal.size + digestWeight * w.spent.size

end World

def applyOp (s : Slots) : Op → Slots
  | .set k v => s.set k v
  | .erase k => s.erase k

def applyOps (s : Slots) (ops : List Op) : Slots := ops.foldl applyOp s

def opKeys (ops : List Op) : List Nat := ops.map Op.key

def opValueSize : Op → Nat
  | .set _ v => v.size
  | .erase _ => 0

def Touch.ops {D : Type} (x : Touch D) : List Op :=
  match x.act with
  | .write ops => ops
  | _ => []

/-- Every number a turn carries is within `Bounds`. -/
def checkBounds (t : Turn D) : Except (Reject D) Unit := do
  req (t.touches.length ≤ Bounds.touchesMax) (.overBound .touches)
  req (t.touches.all fun x => x.ops.length ≤ Bounds.opsPerWriteMax) (.overBound .opsPerWrite)
  req (t.creates.length ≤ Bounds.createsMax) (.overBound .creates)
  req (t.nullifiers.length ≤ Bounds.nullifiersMax) (.overBound .nullifiers)
  req (t.event.size ≤ Bounds.eventBytesMax) (.overBound .event)
  req (t.creates.all fun c => c.slots.length ≤ Bounds.slotsPerCellMax) (.overBound .slotsPerCell)
  req ((t.creates.all fun c => c.slots.all fun p => p.1 < Bounds.slotKeyLimit) &&
       (t.touches.all fun x => x.ops.all fun o => o.key < Bounds.slotKeyLimit)) (.overBound .slotKey)
  req ((t.creates.all fun c => c.slots.all fun p => p.2.size ≤ Bounds.valueBytesMax) &&
       (t.touches.all fun x => x.ops.all fun o => opValueSize o ≤ Bounds.valueBytesMax))
    (.overBound .valueBytes)
  req (t.validUntil ≤ t.notBefore + Bounds.windowMax) (.overBound .window)
  req (t.weight ≤ Bounds.weightMax) (.overBound .weight)
  req (t.validUntil < Bounds.counterLimit && t.notBefore < Bounds.counterLimit &&
       t.charge < Bounds.counterLimit && t.creates.all fun c => c.kind < Bounds.kindLimit)
    (.overBound .counter)

variable [DecidableEq D]

/-- A transaction id is admitted at most once; a retry names the height it landed at. -/
def checkJournal (w : World D) (t : Turn D) : Except (Reject D) Unit :=
  match w.journal[t.txId]? with
  | none => .ok ()
  | some (h, _) => .error (.replayed h)

def noDup {α : Type} [Ord α] (l : List α) (e : α → Reject D) : Except (Reject D) Unit :=
  match firstDup l with
  | none => .ok ()
  | some a => .error (e a)

/-- One touch per cell, one op per key of a write, born cells in canonical form. -/
def checkShape (t : Turn D) : Except (Reject D) Unit := do
  noDup (t.touches.map Touch.cell) .duplicateTouch
  noDup t.nullifiers .duplicateNullifier
  forEx (fun x => noDup (opKeys x.ops) (.duplicateKey x.cell)) t.touches
  forEx (fun (c, i) => req (Slots.ascending c.slots) (.nonCanonicalCell i)) t.creates.zipIdx

def checkWindow (w : World D) (t : Turn D) : Except (Reject D) Unit :=
  req (t.notBefore ≤ w.height + 1 && w.height + 1 ≤ t.validUntil) .outsideWindow

/-- The cell a write leaves behind, or why it may not be written. -/
def postWrite (c : D) (cell : Cell) (ops : List Op) : Except (Reject D) Cell :=
  let post := { cell with slots := applyOps cell.slots ops }
  match cell.discipline with
  | .rom => .error (.romWrite c)
  | .appendOnly => do
      forEx (fun o => match o with
        | .set k _ => req (cell.slots.get k).isNone (.appendOnly c k)
        | .erase k => .error (.appendOnly c k)) ops
      req (post.slots.length ≤ Bounds.slotsPerCellMax) (.overBound .slotsPerCell)
      pure post
  | .ram => do
      req (post.slots.length ≤ Bounds.slotsPerCellMax) (.overBound .slotsPerCell)
      pure post

/-- What a touch leaves at its cell (`none`: unchanged), or why not. The cell is looked up ONCE:
the pin is checked against it (the one staleness refusal), then the act applies to it. -/
def touchCheck (E : Env D) (w : World D) (x : Touch D) : Except (Reject D) (Option (D × Entry)) := do
  let cur := w.live x.cell
  req (pinOf E cur = x.seen) (.stale x.cell)
  match x.act, cur with
  | .keep, _ => pure none
  | .write _, none => .error (.missingCell x.cell)
  | .write ops, some cell => do
      let post ← postWrite x.cell cell ops
      pure (some (x.cell, .live post))
  | .retire, none => .error (.missingCell x.cell)
  | .retire, some cell => do
      req (cell.discipline != .rom) (.romRetire x.cell)
      pure (some (x.cell, .tomb))

def checkNullifiers (w : World D) (t : Turn D) : Except (Reject D) Unit :=
  forEx (fun n => req (!w.spent.contains n) (.spent n)) t.nullifiers

/-- The turn pays exactly its weight, and can afford it. -/
def checkCharge (w : World D) (t : Turn D) : Except (Reject D) Unit := do
  req (t.charge = t.weight) (.chargeMismatch t.weight)
  req (t.charge ≤ w.allowance) .overAllowance

/-- Born ids are fresh: not in the World (live or tombstoned), not twice in the turn, and not
touched by it. -/
def checkCreates (E : Env D) (w : World D) (t : Turn D) : Except (Reject D) Unit := do
  noDup (createdIds E t) .idTaken
  noDup (t.touches.map Touch.cell ++ createdIds E t) .bornTouched
  forEx (fun c => req (!w.cells.contains c) (.idTaken c)) (createdIds E t)

/-- Every check, against the pre-state only; on success, what the touches leave behind. -/
def check (E : Env D) (w : World D) (t : Turn D) : Except (Reject D) (List (D × Entry)) := do
  checkBounds t
  checkJournal w t
  checkShape t
  checkWindow w t
  let posts ← mapEx (touchCheck E w) t.touches
  checkNullifiers w t
  checkCharge w t
  checkCreates E w t
  pure posts.reduceOption

def insertAll (m : Std.TreeMap D Entry compare) (ps : List (D × Entry)) :
    Std.TreeMap D Entry compare :=
  ps.foldl (fun m p => m.insert p.1 p.2) m

def spendAll (s : Std.TreeSet D compare) (ns : List D) : Std.TreeSet D compare :=
  ns.foldl (fun s n => s.insert n) s

def bornEntries (E : Env D) (t : Turn D) : List (D × Entry) :=
  (createdPairs E t).map fun p => (p.1, .live p.2)

/-- The World after a checked turn. Total: everything that can fail failed in `check`. -/
def commit (E : Env D) (w : World D) (t : Turn D) (posts : List (D × Entry)) : World D :=
  { cells := insertAll (insertAll w.cells posts) (bornEntries E t)
    journal := w.journal.insert t.txId (w.height + 1, turnDigest E t)
    spent := spendAll w.spent t.nullifiers
    height := w.height + 1
    chain := chainNext E w.chain t
    allowance := w.allowance - t.charge }

/-- THE transition. Fail-closed: a refusal returns no World. -/
def World.admit (E : Env D) (w : World D) (t : Turn D) : Except (Reject D) (World D) :=
  match check E w t with
  | .ok posts => .ok (commit E w t posts)
  | .error r => .error r

/-- The follower: a log means the World its fold reaches. A refusal names the turn's index. -/
def World.fold (E : Env D) (w : World D) : List (Turn D) → Except (Nat × Reject D) (World D)
  | [] => .ok w
  | t :: rest =>
      match World.admit E w t with
      | .ok w' =>
          match World.fold E w' rest with
          | .ok w'' => .ok w''
          | .error (i, r) => .error (i + 1, r)
      | .error r => .error (0, r)

/-- The chain a log reaches from `c`, without admitting it: what `World.fold` stamps. -/
def chainOf (E : Env D) (c : D) : List (Turn D) → D
  | [] => c
  | t :: rest => chainOf E (chainNext E c t) rest

end Nanodregg.Kernel
