/-
# Kernel.World — the World, its one transition `World.admit`, and `fold`

`World.admit` IS the receive path (law 1): the Host commits exactly what it returns, the
follower and a reopening Host fold the log with it, and nothing else changes a World.

The kernel is generic over the digest `D` and the hash (`Env`) so that theorems can state a
hash collision as an explicit disjunct, and the simulation can run toy parameters through the
same `admit`. There is one deployed `Env` (CODEC's digest and hash).

Order of the checks (each refuses by name, nothing is written before all pass):
bounds → journal (an exact retry is `replayed` whatever else holds) → shape → window → pins
(the one staleness refusal) → nullifiers → charge → created ids → retirements → legs.
-/
import Std.Data.TreeMap
import Std.Data.TreeSet
import Kernel.Check
import Kernel.Turn

namespace Nanodregg.Kernel

/-- The hash and the canonical encodings the kernel digests. CODEC supplies the deployed one. -/
structure Env (D : Type) where
  hash : ByteArray → D
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
  /-- the transaction is already in the journal with this turn's digest, at `height` -/
  | replayed (height : Nat)
  /-- the transaction id is in the journal with a different turn -/
  | txConflict (height : Nat)
  | duplicateLeg (cell : D)
  | duplicatePin (cell : D)
  | duplicateRetire (cell : D)
  | duplicateNullifier (nullifier : D)
  | duplicateKey (cell : D) (key : Nat)
  | legRetired (cell : D)
  | nonCanonicalCell (index : Nat)
  | outsideWindow
  /-- the cell is not what the signer saw -/
  | stale (cell : D)
  | spent (nullifier : D)
  | chargeMismatch (expected : Nat)
  | overAllowance
  | idTaken (cell : D)
  | missingCell (cell : D)
  | romWrite (cell : D)
  | romRetire (cell : D)
  | appendOnly (cell : D) (key : Nat)
  deriving DecidableEq, Repr

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

/-- Domain tags of the kernel's digests. -/
def tagGenesis : ByteArray := "nanodregg/kernel/genesis/v1".toUTF8
def tagAbsent : ByteArray := "nanodregg/kernel/pin-absent/v1".toUTF8
def tagCell : ByteArray := "nanodregg/kernel/pin-cell/v1".toUTF8
def tagTurn : ByteArray := "nanodregg/kernel/turn/v1".toUTF8
def tagChain : ByteArray := "nanodregg/kernel/chain/v1".toUTF8
def tagCellId : ByteArray := "nanodregg/kernel/cell-id/v1".toUTF8

/-- Four little-endian bytes (indexes are below `Bounds.createsMax`). -/
def le32 (n : Nat) : ByteArray :=
  ⟨#[(n % 256).toUInt8, (n / 256 % 256).toUInt8, (n / 65536 % 256).toUInt8,
     (n / 16777216 % 256).toUInt8]⟩

/-- What a pin asserts about a cell: its digest, or the digest of absence. -/
def pinOf (E : Env D) : Option Cell → D
  | none => E.hash tagAbsent
  | some c => E.hash (tagCell ++ E.cellBytes c)

def turnDigest (E : Env D) (t : Turn D) : D := E.hash (tagTurn ++ E.turnBytes t)

def chainNext (E : Env D) (prev : D) (t : Turn D) : D :=
  E.hash (tagChain ++ E.bytes prev ++ E.bytes (turnDigest E t))

/-- The id of the `i`-th cell a transaction creates. -/
def cellIdOf (E : Env D) (txId : D) (i : Nat) : D :=
  E.hash (tagCellId ++ E.bytes txId ++ le32 i)

def createdIds (E : Env D) (t : Turn D) : List D :=
  (List.range t.creates.length).map (cellIdOf E t.txId)

def createdPairs (E : Env D) (t : Turn D) : List (D × Cell) :=
  (createdIds E t).zip t.creates

namespace World

def genesis (E : Env D) (name : ByteArray) (allowance : Nat) : World D :=
  { cells := {}, journal := {}, spent := {}, height := 0,
    chain := E.hash (tagGenesis ++ name), allowance }

/-- The live cell at an id, if any (a tombstone reads as absent). -/
def live (w : World D) (c : D) : Option Cell :=
  match w.cells[c]? with
  | some (.live cell) => some cell
  | _ => none

end World

def applyOp (s : Slots) : Op → Slots
  | .set k v => s.set k v
  | .erase k => s.erase k

def applyOps (s : Slots) (ops : List Op) : Slots := ops.foldl applyOp s

def opKeys (ops : List Op) : List Nat := ops.map Op.key

def opValueSize : Op → Nat
  | .set _ v => v.size
  | .erase _ => 0

/-- Every number a turn carries is within `Bounds`. -/
def checkBounds (t : Turn D) : Except (Reject D) Unit := do
  req (t.legs.length ≤ Bounds.legsMax) (.overBound .legs)
  req (t.legs.all fun l => l.ops.length ≤ Bounds.opsPerLegMax) (.overBound .opsPerLeg)
  req (t.pins.length ≤ Bounds.pinsMax) (.overBound .pins)
  req (t.creates.length ≤ Bounds.createsMax) (.overBound .creates)
  req (t.retires.length ≤ Bounds.retiresMax) (.overBound .retires)
  req (t.nullifiers.length ≤ Bounds.nullifiersMax) (.overBound .nullifiers)
  req (t.event.size ≤ Bounds.eventBytesMax) (.overBound .event)
  req (t.creates.all fun c => c.slots.length ≤ Bounds.slotsPerCellMax) (.overBound .slotsPerCell)
  req ((t.creates.all fun c => c.slots.all fun p => p.1 < Bounds.slotKeyLimit) &&
       (t.legs.all fun l => l.ops.all fun o => o.key < Bounds.slotKeyLimit)) (.overBound .slotKey)
  req ((t.creates.all fun c => c.slots.all fun p => p.2.size ≤ Bounds.valueBytesMax) &&
       (t.legs.all fun l => l.ops.all fun o => opValueSize o ≤ Bounds.valueBytesMax))
    (.overBound .valueBytes)
  req (t.validUntil ≤ t.notBefore + Bounds.windowMax) (.overBound .window)

variable [DecidableEq D]

/-- A transaction id is admitted at most once; an exact retry names the height it landed at. -/
def checkJournal (E : Env D) (w : World D) (t : Turn D) : Except (Reject D) Unit :=
  match w.journal[t.txId]? with
  | none => .ok ()
  | some (h, d) => if d = turnDigest E t then .error (.replayed h) else .error (.txConflict h)

def noDup {α : Type} [Ord α] (l : List α) (e : α → Reject D) : Except (Reject D) Unit :=
  match firstDup l with
  | none => .ok ()
  | some a => .error (e a)

/-- One leg per cell, one pin per cell, one op per key, no leg on a retiring cell,
born cells in canonical form. -/
def checkShape (t : Turn D) : Except (Reject D) Unit := do
  noDup (t.legs.map Leg.cell) .duplicateLeg
  noDup (t.pins.map Prod.fst) .duplicatePin
  noDup t.retires .duplicateRetire
  noDup t.nullifiers .duplicateNullifier
  forEx (fun l => noDup (opKeys l.ops) (.duplicateKey l.cell)) t.legs
  forEx (fun l => req (!t.retires.contains l.cell) (.legRetired l.cell)) t.legs
  forEx (fun (c, i) => req (Slots.ascending c.slots) (.nonCanonicalCell i)) t.creates.zipIdx

def checkWindow (w : World D) (t : Turn D) : Except (Reject D) Unit :=
  req (t.notBefore ≤ w.height + 1 && w.height + 1 ≤ t.validUntil) .outsideWindow

/-- The one staleness refusal: every cell the signer observed is as observed. -/
def pinCheck (E : Env D) (w : World D) (p : D × D) : Except (Reject D) Unit :=
  req (pinOf E (w.live p.1) = p.2) (.stale p.1)

def checkPins (E : Env D) (w : World D) (t : Turn D) : Except (Reject D) Unit :=
  forEx (pinCheck E w) t.pins

def checkNullifiers (w : World D) (t : Turn D) : Except (Reject D) Unit :=
  forEx (fun n => req (!w.spent.contains n) (.spent n)) t.nullifiers

/-- The turn pays exactly its weight, and can afford it. -/
def checkCharge (w : World D) (t : Turn D) : Except (Reject D) Unit := do
  req (t.charge = t.weight) (.chargeMismatch t.weight)
  req (t.charge ≤ w.allowance) .overAllowance

def checkCreates (E : Env D) (w : World D) (t : Turn D) : Except (Reject D) Unit :=
  forEx (fun c => req (!w.cells.contains c) (.idTaken c)) (createdIds E t)

def checkRetire (w : World D) (c : D) : Except (Reject D) Unit :=
  match w.live c with
  | none => .error (.missingCell c)
  | some cell => req (cell.discipline != .rom) (.romRetire c)

/-- The cell a leg leaves behind, or why it may not be written. -/
def postLeg (w : World D) (l : Leg D) : Except (Reject D) (D × Cell) :=
  match w.live l.cell with
  | none => .error (.missingCell l.cell)
  | some cell =>
      let post := { cell with slots := applyOps cell.slots l.ops }
      match cell.discipline with
      | .rom => .error (.romWrite l.cell)
      | .appendOnly => do
          forEx (fun o => match o with
            | .set k _ => req (cell.slots.get k).isNone (.appendOnly l.cell k)
            | .erase k => .error (.appendOnly l.cell k)) l.ops
          req (post.slots.length ≤ Bounds.slotsPerCellMax) (.overBound .slotsPerCell)
          pure (l.cell, post)
      | .ram => do
          req (post.slots.length ≤ Bounds.slotsPerCellMax) (.overBound .slotsPerCell)
          pure (l.cell, post)

/-- Every check, against the pre-state only; on success, the post-cells of the legs. -/
def check (E : Env D) (w : World D) (t : Turn D) : Except (Reject D) (List (D × Cell)) := do
  checkBounds t
  checkJournal E w t
  checkShape t
  checkWindow w t
  checkPins E w t
  checkNullifiers w t
  checkCharge w t
  checkCreates E w t
  forEx (checkRetire w) t.retires
  mapEx (postLeg w) t.legs

def insertAll (m : Std.TreeMap D Entry compare) (ps : List (D × Cell)) :
    Std.TreeMap D Entry compare :=
  ps.foldl (fun m p => m.insert p.1 (.live p.2)) m

def tombAll (m : Std.TreeMap D Entry compare) (cs : List D) : Std.TreeMap D Entry compare :=
  cs.foldl (fun m c => m.insert c .tomb) m

def spendAll (s : Std.TreeSet D compare) (ns : List D) : Std.TreeSet D compare :=
  ns.foldl (fun s n => s.insert n) s

/-- The World after a checked turn. Total: everything that can fail failed in `check`. -/
def commit (E : Env D) (w : World D) (t : Turn D) (posts : List (D × Cell)) : World D :=
  { cells := insertAll (tombAll (insertAll w.cells posts) t.retires) (createdPairs E t)
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

end Nanodregg.Kernel
