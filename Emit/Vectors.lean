import Codec.World
import Codec.Layout
import Host.Base
import Host.Carry
import Lang.Wire.Data
import Lang.Package
import Lang.Rel
import Lang.Print
import Kernel.Sim

/-!
# Emit.Vectors — the codec vectors: a change of meaning under the same bytes bumps the label (CODEC-28 (d))

A content tag (`Tag.of`) sees a codec's shape and its refinements' NAMES, not the functions inside a
refinement. A relabelling (`accept` and `back` changed together: two same-typed fields or constructors
swapped) keeps the shape, the tag and every lawfulness theorem, and changes what stored bytes mean
(`Codec.Kernel.slot_relabel_unseen`). This is the detector for it.

`gates/codec-vectors.tsv` holds, for every refine site the refine census finds, a few vectors: bytes encoded
from values drawn deterministically from `Kernel.Sim`'s generator (seeded by the site's name), with the
site's tag and the decoded value as `print` shows it. The kernel codecs are taken at `Kernel.Sim`'s
parameters (`D = UInt64`, `dc = u64`, `Sim.env`).

* `--check PATH`: every site has rows under its CURRENT tag, and each such row's bytes decode to the
  pinned text. A row whose text changed under an unchanged tag is red by name: the bytes mean something
  else and the label did not move. Rename the refinement (its tag moves, and every stamp with it).
* `--write PATH`: keeps every row whose site's tag is unchanged VERBATIM (so re-running the generator
  can never launder a relabelling) and draws fresh rows for a site whose tag moved or is new. A tag
  change re-pins exactly that site's vectors; the commit says what re-geneses.

The printer is `print`: `ok ` and the value's `Repr` (field and constructor names, so a swap of two
equal-typed positions changes the text), or `refused ` and the refusal. A trie (the cells and, since
KERNEL-41, the journal) is printed as its listing, so a change of hash is not a change of meaning.
-/

namespace Nanodregg.Emit.Vectors

open Nanodregg.Kernel Nanodregg.Kernel.Receive Nanodregg.Codec Nanodregg.Codec.Kernel

deriving instance Repr for RowKey, RowSlot, RowLeaf, RowAct, RowTouch, RangeRead, Op, Cell, Entry, Slot, Leaf,
  Act, Touch, Turn, Right, AcctRef, Body, Unsigned, Call, Host.Entry, Host.Carry.Head, RefusalSlot, RefusalLeaf,
  Refused, Step, Trie.Proof, Lang.Term, Lang.SupportPin, Lang.HoleCode, Lang.HoleROM, Lang.RelDecl, Lang.Package

/-! ## Values, drawn from the simulation's generator -/

abbrev G := StateM Sim.Gen.Rng

def u64 : G UInt64 := modifyGet Sim.Gen.Rng.next
def below (n : Nat) : G Nat := modifyGet (Sim.Gen.Rng.below · n)
def nat64 : G Nat := (·.toNat) <$> u64
def nat32 : G Nat := (·.toNat % 2 ^ 32) <$> u64
def dig : G Sim.D := u64
def bytes (max : Nat) : G ByteArray := do
  let n ← below (max + 1)
  let mut b := ByteArray.empty
  for _ in [0:n] do
    b := b.push (← below 256).toUInt8
  return b
def list {α : Type} (max : Nat) (g : G α) : G (List α) := do
  let n ← below (max + 1)
  let mut l := []
  for _ in [0:n] do
    l := l ++ [← g]
  return l
/-- One to `max` values: a vector with an empty part pins nothing about that part. -/
def list1 {α : Type} (max : Nat) (g : G α) : G (List α) := do
  return (← g) :: (← list (max - 1) g)
def opt {α : Type} (g : G α) : G (Option α) := do
  if (← below 2) = 0 then return none else return some (← g)

/-- A version or a floor (KERNEL-54): one varint byte, two, three, or the whole u64 range (up to ten). -/
def version : G Nat := do
  match ← below 4 with
  | 0 => below 128
  | 1 => return 128 + (← below (2 ^ 14 - 128))
  | 2 => return 2 ^ 14 + (← below (2 ^ 21 - 2 ^ 14))
  | _ => nat64

def discipline : G Discipline := do
  match ← below 4 with | 0 => return .rom | 1 => return .appendOnly | 2 => return .ram | _ => return .value
def slots : G Slots := list 2 (do return (← nat32, ← bytes 4))
def cell : G Cell := do return ⟨← nat32, ← discipline, ← slots⟩
def op (k : Nat) : G Op := do
  if k = 0 then return .set (← nat32) (← bytes 4) else return .erase (← nat32)
def act (k : Nat) : G Act := do
  match k with
  | 0 => return .keep
  | 1 => return .write (← list 2 (do op (← below 2)))
  | _ => return .retire
def touch : G (Touch Sim.D) := do return ⟨← dig, ← dig, ← act (← below 3)⟩
/-! ### Rows (KERNEL-46/48) -/

/-- A byte string of exactly `n` drawn bytes. -/
def bytesN (n : Nat) : G ByteArray := do
  let mut b := ByteArray.empty
  for _ in [0:n] do
    b := b.push (← below 256).toUInt8
  return b
def rowSlot (k : Nat) : G (RowSlot Sim.D) := do
  if k = 0 then return .head (← dig) (← below 256)
  else return .row ⟨← dig, ← below 256, ← bytes 6⟩
def rowLeaf (k : Nat) : G RowLeaf := do
  if k = 0 then
    return .head (← below 9) (← below 900) (← below 4096) (← nat64) (← below 129) ((← below 2) = 0) (← version)
  else return .row (← nat64) (← bytes 6) (← version)
def rowAct (k : Nat) : G RowAct := do
  match k with
  | 0 => return .keep
  | 1 => return .insert (← nat64) (← bytes 4)
  | 2 => return .upsert (← nat64) (← bytes 4)
  | 3 => return .retract
  | _ => return .declare (← below 4097) (← nat64) (← below 129) ((← below 2) = 0)
def rowTouch : G (RowTouch Sim.D) := do return ⟨← rowSlot (← below 2), ← opt dig, ← rowAct (← below 5)⟩
def rangeRead : G (RangeRead Sim.D) := do return ⟨← dig, ← below 256, ← bytes 4, ← nat64, ← dig⟩

/-- A rows listing a World can hold (`rowsFits`, `rowsHeaded`, `rowsParented` over a trie whose live
cells are `ps`): one or two relations under parents drawn from `ps` (none if `ps` is empty), each a head
counting and summing its one to three rows, its keys of the head's width. -/
def rows (ps : List Sim.D) : G (List (RowSlot Sim.D × RowLeaf)) := do
  if ps.isEmpty then return []
  let nrel := (← below 2) + 1
  let mut out := []
  for _ in [0:nrel] do
    let p := ps.getD (← below ps.length) 0
    let rel ← below 256
    let width := (← below 8) + 1
    let n := (← below 3) + 1
    let mut keys : List ByteArray := []
    for _ in [0:n] do keys := keys ++ [← bytesN width]
    let uniq := keys.eraseDups
    let mut rs := []
    let mut sum := 0
    for k in uniq do
      let amt ← below 50
      sum := sum + amt
      rs := rs ++ [(RowSlot.row ⟨p, rel, k⟩, RowLeaf.row amt (← bytes 6) (← version))]
    let limit := uniq.length + (← below 3)
    let cap := sum + (← below 100)
    out := out ++ (RowSlot.head p rel, RowLeaf.head uniq.length sum limit cap width ((← below 2) = 0) (← version)) :: rs
  return out

/-- The canonical rows trie of a listing (KERNEL-48). -/
def rowsOf (l : List (RowSlot Sim.D × RowLeaf)) : Rows Sim.D :=
  Trie.build (rowSpec Sim.env) (rowSpec Sim.env).depth 0 l

def turn : G (Turn Sim.D) := do
  return ⟨← dig, ← nat64, ← nat64, ← list 2 touch, ← list 1 (do return (← dig, ← cell)), ← list 2 dig, ← nat64,
    ← bytes 8, ← list 2 rowTouch, ← list 1 rangeRead⟩
def right (k : Nat) : G Right := do
  match k with
  | 0 => return .observe
  | 1 => return .mutate
  | 2 => return .invoke (← nat64)
  | 3 => return .enroll (← nat64)
  | 4 => return .transfer (← nat64)
  | _ => return .credit (← nat64)
def acctRef (k : Nat) : G (AcctRef Sim.D) := do
  if k = 0 then return .well (← dig) else return .of (← dig) (← dig)
def body (k : Nat) : G (Body Sim.D) := do
  match k with
  | 0 => return .enroll (← bytes 4) (← dig) (← bytes 4) (← dig)
  | 1 => return .rotate (← bytes 4) (← dig)
  | 2 => return .install (← bytes 4)
  | 3 => return .create (← opt dig) (← list 2 dig) (← slots)
  | 4 => return .write (← dig) (← list 2 (do return (← nat32, ← opt (bytes 4)))) (← opt dig)
  | 5 => return .law (← dig) (← list 2 dig) (← opt dig)
  | 6 => return .invoke (← dig) (← nat64) (← bytes 4) (← nat64) (← opt dig)
  | 7 => return .grant (← dig) (← dig) (← list 3 (do right (← below 6))) (← opt dig)
  | 8 => return .revoke (← dig)
  | 9 => return .issue (← nat64)
  | 10 => return .account (← dig) (← dig)
  | 11 => return .transfer (← acctRef (← below 2)) (← acctRef (← below 2)) (← nat64) (← opt dig) (← opt (bytes 4))
  | _ => return .credit (← dig) (← acctRef (← below 2)) (← nat64) (← opt dig)
def unsigned (k : Nat) : G (Unsigned Sim.D) := do
  return ⟨← dig, ← dig, ← bytes 4, ← nat64, ← nat64, ← list 2 (do return (← dig, ← dig)), ← nat64, ← body k,
    ← list 1 (do return (← rowSlot (← below 2), ← dig)), ← list 1 rangeRead⟩

/-- A canonical trie of a few slots, each holding the leaf of its kind. -/
def trie : G (Cells Sim.D) := do
  let ks ← list1 3 (do
    if (← below 2) = 0 then
      let e : Entry ← if (← below 2) = 0 then (do return .live (← cell) (← version)) else pure .tomb
      return ((Slot.cell (← dig) : Slot Sim.D), Leaf.entry e)
    else return (.nullifier (← dig), Leaf.spent))
  return Trie.build (trieSpec Sim.env) (trieSpec Sim.env).depth 0 ks

/-- A journal listing of distinct transaction ids, each entry one height at or just below `h` (any order:
`build` is order-blind on distinct keys, `Trie.build_perm`). -/
def journal (h : Nat) : G (List (Sim.D × (Nat × Sim.D))) := do
  let n := (← below 2) + 2
  let mut drawn : List Sim.D := []
  for _ in [0:n] do drawn := drawn ++ [← dig]
  let ids := (drawn.mergeSort (· ≤ ·)).eraseDups
  let mut out := []
  for (i, k) in ids.zipIdx do
    out := out ++ [(i, (h - k, ← dig))]
  return out

/-- The canonical journal trie of a listing (KERNEL-41). -/
def journalOf (l : List (Sim.D × (Nat × Sim.D))) : Journal Sim.D :=
  Trie.build (journalSpec Sim.env) (journalSpec Sim.env).depth 0 l

/-- `kernel/proof`'s vectors (KERNEL-49 (a)), under the journal's spec: a drawn journal's proof for one of
its ids (a leaf's entry) and for a drawn id (absent), then the depth's boundary pair: a path whose one
sibling branches at bit `journalDepth - 1` (read back) and the same path at `journalDepth` (refused
`kernel/proof` by name: no node of the trie branches at or past its depth). -/
def proofVecs : G (List (Trie.Proof Sim.D Sim.D)) := do
  let l ← journal ((← below 1000) + 3)
  let t := journalOf l
  let k := (l.head?.map (·.1)).getD 0
  let s ← dig
  let deep (b : Nat) : Trie.Proof Sim.D Sim.D := ⟨some [(k, s)], [(b, s)]⟩
  return [t.prove (journalSpec Sim.env) k, t.prove (journalSpec Sim.env) (← dig),
    deep (Bounds.journalDepth - 1), deep Bounds.journalDepth]

/-- The count leaves a listing's records make at height `h` (KERNEL-50's `refusalsCounted`): one per
member with a record in the window of `h`, holding its number of them. -/
def countsOf (h : Nat) (l : List (RefusalSlot Sim.D × RefusalLeaf Sim.D)) : List (RefusalSlot Sim.D × RefusalLeaf Sim.D) :=
  let cur := l.filterMap fun p => match p with
    | (.tx _, .refused r _ m) => if (r - 1) / Bounds.windowMax = h / Bounds.windowMax then some m else none
    | _ => none
  cur.eraseDups.map fun m => (.count m (refusalWindow h), .count (cur.count m))

/-- The total leaf a listing's records make at height `h` under origin `o` (KERNEL-55 R1's
`refusalsCounted`): the number of records in the window of `h`, all members together, present iff
there is one. -/
def totalOf (h : Nat) (o : Sim.D) (l : List (RefusalSlot Sim.D × RefusalLeaf Sim.D)) :
    List (RefusalSlot Sim.D × RefusalLeaf Sim.D) :=
  let n := (l.map (refusedWin (h / Bounds.windowMax))).sum
  if n = 0 then [] else [(.total o (refusalWindow h), .count n)]

/-- A refusals listing a World at height `h` can hold (KERNEL-44, KERNEL-50): one to three refused
transaction ids, each refused at a height at or just below `h + 1` and charged to one of one or two
drawn members, and each charged member's count of its records in the current window (`refusalsFits`,
`refusalsCounted`). -/
def refusals (h : Nat) : G (List (RefusalSlot Sim.D × RefusalLeaf Sim.D)) := do
  let members ← list1 2 dig
  let txs ← list1 3 (do
    let m := members.getD (← below members.length) 0
    return (RefusalSlot.tx (← dig), RefusalLeaf.refused (h + 1 - (← below 3)) (← below 40) m))
  return txs ++ countsOf h txs

/-- The canonical refusals trie of a listing (KERNEL-44). -/
def refusalsOf (l : List (RefusalSlot Sim.D × RefusalLeaf Sim.D)) : Refusals Sim.D :=
  Trie.build (refusalSpec Sim.env) (refusalSpec Sim.env).depth 0 l

/-- The live cells of a cells trie: the parents a relation may sit under. -/
def liveIds (t : Cells Sim.D) : List Sim.D :=
  t.toList.filterMap fun p => match p with | (.cell c, .entry (.live _ _)) => some c | _ => none

/-- A cells trie with one more live cell, `p`. -/
def withLive (t : Cells Sim.D) (p : Sim.D) : Cells Sim.D :=
  Trie.build (trieSpec Sim.env) (trieSpec Sim.env).depth 0 (t.toList ++ [(.cell p, .entry (.live ⟨0, .ram, []⟩ 0))])

def world : G (World Sim.D) := do
  let h := (← below 1000) + 3
  let t ← trie
  let j ← journal h
  let r ← refusals h
  let rw ← rows (liveIds t)
  let extra ← below 5
  let chain ← dig
  let allowance ← below (2 ^ 40)
  let origin ← dig
  -- every recorded refusal cost a step that did not raise the height (`refusalsCounted`); the
  -- window's total is filed under the origin (KERNEL-55 R1)
  return { trie := t, journal := journalOf j, refusals := refusalsOf (r ++ totalOf h origin r),
           rows := rowsOf rw, height := h, steps := h + (r.map refusedOne).sum + extra,
           chain, allowance, origin }

/-- `w` with one more refusal recorded, transaction `k` charged to `m` at height `w.height + 1` (in
the current window), and the step it cost: the three inserts `commitRefusals` makes (the record, the
member's count, the World's total). -/
def addRecord (w : World Sim.D) (k m : Sim.D) (code : Nat) : World Sim.D :=
  { w with
    refusals := ((w.refusals.insert (refusalSpec Sim.env) (.tx k) (.refused (w.height + 1) code m)).insert
      (refusalSpec Sim.env) (.count m (refusalWindow w.height)) (.count (refusalCount Sim.env w m + 1))).insert
      (refusalSpec Sim.env) (.total w.origin (refusalWindow w.height)) (.count (refusalTotal Sim.env w + 1))
    steps := w.steps + 1 }

def refused : G (Refused Sim.D) := do
  return ⟨← dig, ← dig, ← nat64, ← nat64, ← below 40, ← bytes 8, ← bytes 64⟩

def step (k : Nat) : G (Step Sim.D) := do
  if k = 0 then return .turn (← turn) else return .refusal (← refused)

def carried : G (Carried Sim.D) := do
  let h := (← below 1000) + 3
  let t ← trie
  return { trie := t, allowance := ← nat64, height := h, journal := journalOf (← journal h),
           rows := rowsOf (← rows (liveIds t)) }

/-! ## The one printer -/

/-- `Repr` on one line: no width at which the formatter breaks. -/
def text {α : Type} [Repr α] (v : α) : String := (repr v).pretty 1000000

def printWorld (w : World Sim.D) : String :=
  s!"\{trie := {text w.trie.toList}, journal := {text w.journal.toList}, " ++
    s!"refusals := {text w.refusals.toList}, rows := {text w.rows.toList}, height := {w.height}, " ++
    s!"steps := {w.steps}, " ++
    s!"chain := {w.chain}, allowance := {w.allowance}, origin := {w.origin}}"

def printWire (x : WorldWire Sim.D) : String := printWorld (ofWire x)

def printCarried (c : Carried Sim.D) : String :=
  s!"\{trie := {text c.trie.toList}, allowance := {c.allowance}, height := {c.height}, " ++
    s!"journal := {text c.journal.toList}, rows := {text c.rows.toList}}"

def printCarriedWire (x : CarriedWire Sim.D) : String := printCarried (carriedOfWire x)

def printBase (b : Host.Base (World Sim.D)) : String :=
  s!"\{world := {printWorld b.world}, offset := {b.offset}, tag := {text b.tag}, " ++
    s!"indexCount := {b.indexCount}, indexLast := {text b.indexLast}, retainedFrom := {b.retainedFrom}, " ++
    s!"indexFrom := {b.indexFrom}}"

/-- One line: tabs and newlines would break the table. -/
def oneLine (s : String) : String := (s.replace "\n" " ").replace "\t" " "

def print {α : Type} (c : Stream α) (pr : α → String) (b : ByteArray) : String :=
  oneLine <| match c.decode b with
  | .ok v => "ok " ++ pr v
  | .error e => "refused " ++ text e

/-! ## The sites -/

structure Site where
  name : String
  tag : Digest
  /-- the vectors' bytes, drawn from the site's own seed -/
  draw : G (List ByteArray)
  print : ByteArray → String

def site {α : Type} (name : String) (c : Stream α) (vs : G (List α)) (pr : α → String) : Site :=
  ⟨name, Tag.of name c, (·.map c.bytes) <$> vs, print c pr⟩

def each {α : Type} (n : Nat) (g : Nat → G α) : G (List α) := (List.range n).mapM g

def pathMax : Nat := 255

def path : G (List ByteArray) := do
  let n := (← below 3) + 1
  let mut l := []
  for _ in [0:n] do
    let k := (← below 6) + 1
    let mut c := ByteArray.empty
    for _ in [0:k] do c := c.push (97 + (← below 26)).toUInt8
    l := l ++ [c]
  return l

def pathVecs : G (List (Field.PathTy pathMax)) := do
  let mut out := []
  for _ in [0:3] do
    let p ← path
    if h : Path.fits pathMax p = true then out := out ++ [⟨p, h⟩]
  return out

def digest : G Digest := do
  let mut b := ByteArray.empty
  for _ in [0:32] do b := b.push (← below 256).toUInt8
  return (Digest.ofBytes? b).getD Digest.zero

/-- `host/base/retained`'s vectors (HOST-64): two drawn bases keeping from the start of the log, then
the keep's boundary pairs: a base keeping the segment file at its own offset (read back) and one
past it (refused `host/base/retained` by name), and a base keeping from its own entry count (read
back) and one past it (refused by name). -/
def baseVecs : G (List (Host.Base (World Sim.D))) := do
  let drawn ← each 2 fun _ => do
    return (⟨← Vectors.world, (← nat64) % 2 ^ 63, ← digest, (← nat64) % 2 ^ 63, ← digest, 0, 0⟩ : Host.Base (World Sim.D))
  let b : Host.Base (World Sim.D) := ⟨← Vectors.world, (← nat64) % 2 ^ 63, ← digest, (← nat64) % 2 ^ 63, ← digest, 0, 0⟩
  return drawn ++ [{ b with retainedFrom := b.offset }, { b with retainedFrom := b.offset + 1 },
    { b with indexFrom := b.indexCount }, { b with indexFrom := b.indexCount + 1 }]

/-- `kernel/world-budget`'s vectors: two drawn Worlds, then a third at the budget's boundary (storage plus
allowance exactly 2^64 − 1, read back) and the same World one past it (refused `kernel/world-budget` by name,
cv 01a14ba9-cbf4). Every counter of the refused one still fits its `u64`: only the sum is over. -/
def worldVecs : G (List (World Sim.D)) := do
  let drawn ← each 2 fun _ => Vectors.world
  let w ← Vectors.world
  return drawn ++ [{ w with allowance := 2 ^ 64 - 1 - w.weight }, { w with allowance := 2 ^ 64 - w.weight }]

/-- `kernel/refusals`' vectors: two drawn Worlds, then the per-window budget's boundary pair (KERNEL-44):
a member charged exactly `Bounds.refusalsPerWindow` refusals this window, its records and its count
(read back), and the same World charged one more (refused `kernel/refusals` by name: the count is past
the budget); then the World cap's boundary pair (KERNEL-55 R1): a World whose window total is exactly
`Bounds.refusalsPerWindowMax` (read back) and one past it (refused `kernel/refusals` by name). The cap
pair is the listing check alone: whether the total is its records' is `kernel/refusals-counted`'s. -/
def refusalsVecs : G (List (WorldWire Sim.D)) := do
  let drawn ← each 2 fun _ => toWire <$> Vectors.world
  let w ← Vectors.world
  let m ← dig
  let ks ← each (Bounds.refusalsPerWindow + 1) fun _ => dig
  let at_ (n : Nat) : World Sim.D :=
    { w with
      refusals := refusalsOf (w.refusals.toList ++ (ks.take n).map (fun k => (.tx k, .refused (w.height + 1) 1 m)) ++
        [(.count m (refusalWindow w.height), .count n)])
      steps := w.steps + n }
  let w' ← Vectors.world
  let total (n : Nat) : World Sim.D :=
    { w' with
      refusals := refusalsOf (w'.refusals.toList.filter (fun p => match p.1 with | .total _ _ => false | _ => true) ++
        [(.total w'.origin (refusalWindow w'.height), .count n)]) }
  return drawn ++ [toWire (at_ Bounds.refusalsPerWindow), toWire (at_ (Bounds.refusalsPerWindow + 1)),
    toWire (total Bounds.refusalsPerWindowMax), toWire (total (Bounds.refusalsPerWindowMax + 1))]

/-- `kernel/steps`' vectors: two drawn Worlds, then the boundary pair over a World with no refusals
recorded (so its records cost no steps): a step count equal to the height (read back) and one less
(refused `kernel/steps` by name). -/
def stepsVecs : G (List (WorldWire Sim.D)) := do
  let drawn ← each 2 fun _ => toWire <$> Vectors.world
  let w ← Vectors.world
  let w₀ : World Sim.D := { w with refusals := .empty }
  return drawn ++ [toWire { w₀ with steps := w.height }, toWire { w₀ with steps := w.height - 1 }]

/-- `kernel/refusals-disjoint`'s vectors: two drawn Worlds, then the boundary pair: a World whose
refused transaction id is not journaled (read back), and the same World with that id journaled too
(refused `kernel/refusals-disjoint` by name). -/
def disjointVecs : G (List (WorldWire Sim.D)) := do
  let drawn ← each 2 fun _ => toWire <$> Vectors.world
  let w ← Vectors.world
  let k ← dig
  let base := addRecord w k (← dig) 1
  let both : World Sim.D :=
    { base with journal := journalOf (w.journal.toList ++ [(k, (w.height - 5, ← dig))]) }
  return drawn ++ [toWire base, toWire both]

/-- `kernel/refusals-counted`'s vectors (KERNEL-50): two drawn Worlds, then the boundary pair: a World
holding two refusals charged to `m` and one to `m'` this window, counted (read back), and the same
World with one of `m`'s charges moved to `m'`, counts only, the records untouched and the sum of the
counts unchanged (KERNEL-50 `refusalsCounted_moved`; refused `kernel/refusals-counted` by name); and
`w₁` with its window total one over its records (KERNEL-55 R1; refused `kernel/refusals-counted` by
name). -/
def countedVecs : G (List (WorldWire Sim.D)) := do
  let drawn ← each 2 fun _ => toWire <$> Vectors.world
  let w ← Vectors.world
  let m ← dig
  let m' ← dig
  let w₁ := addRecord (addRecord (addRecord w (← dig) m 1) (← dig) m 2) (← dig) m' 3
  let win := refusalWindow w₁.height
  let moved : World Sim.D :=
    { w₁ with
      refusals := (w₁.refusals.insert (refusalSpec Sim.env) (.count m win) (.count (refusalCount Sim.env w₁ m - 1))).insert
        (refusalSpec Sim.env) (.count m' win) (.count (refusalCount Sim.env w₁ m' + 1)) }
  let over : World Sim.D :=
    { w₁ with
      refusals := w₁.refusals.insert (refusalSpec Sim.env) (.total w₁.origin win) (.count (refusalTotal Sim.env w₁ + 1)) }
  return drawn ++ [toWire w₁, toWire moved, toWire over]

/-- `kernel/refused`'s vectors: two drawn, then the cancel signature's boundary pair (KERNEL-60): a
signature of exactly `Bounds.cancelBytesMax` (64) bytes reads back, one of 65 is refused by the codec
(`pastBound` at its length; `World.refuse`'s own refusal of a wider one is `overBound event`). -/
def refusedVecs : G (List (Refused Sim.D)) := do
  let drawn ← each 2 fun _ => refused
  let r ← refused
  return drawn ++ [{ r with cancel := ← bytesN Bounds.cancelBytesMax },
    { r with cancel := ← bytesN (Bounds.cancelBytesMax + 1) }]

/-- `kernel/row-key`'s vectors: a head and a drawn row, then the key width's boundary pair: a row key of
exactly `Bounds.keyBytesMax` (128) bytes reads back, one of 129 is refused by the codec (`pastBound` at
the length varint; admission's own refusal of a wider key is `overBound rows`, and of a key not at its
relation's width `keyWidth`); then the relation's varint edge, 127 in one byte and 128 in two (read
back, cv 01a14f7e), and the relation's boundary pair, 255 read back and 256 refused `kernel/row-key` by
name (under the one-byte relation 256 wrapped to 0). -/
def rowKeyVecs : G (List (RowSlot Sim.D)) := do
  let p ← dig
  let rel ← below 256
  return [← rowSlot 0, ← rowSlot 1, .row ⟨p, rel, ← bytesN Bounds.keyBytesMax⟩,
    .row ⟨p, rel, ← bytesN (Bounds.keyBytesMax + 1)⟩, .head p 127, .head p 128, .head p 255, .head p 256]

/-- `kernel/range-read`'s vectors: two drawn, then the prefix's boundary pair (128 bytes read back, 129
refused `pastBound`). -/
def rangeReadVecs : G (List (RangeRead Sim.D)) := do
  let drawn ← each 2 fun _ => rangeRead
  let q ← rangeRead
  return drawn ++ [{ q with pre := ← bytesN Bounds.keyBytesMax }, { q with pre := ← bytesN (Bounds.keyBytesMax + 1) }]

/-- A range pin's input over a drawn rows listing: a relation's rows under a prefix of their keys. -/
def rangePinVec : G (RangePinWire Sim.D) := do
  let l ← rows [← dig]
  match l with
  | (.head p rel, .head _ _ _ _ width _ floor) :: _ =>
    let rs := (rowsOf l).toList.filter fun q => match q.1 with
      | .row k => decide (k.parent = p) && decide (k.rel = rel) | _ => false
    return (p, rel, width, ByteArray.empty, floor, rs.map fun q => (q.1, rowDigest Sim.env q.2))
  | _ => return (← dig, 0, 0, ByteArray.empty, 0, [])

/-- `kernel/range-pin`'s vectors: two drawn, then the floor at its largest (2^64 − 1, KERNEL-54; the floor is
eight bytes in the preimage, so every eight bytes read back and the bound is the counter limit's), and the
same input one byte short, refused `truncated`; then the relation's and the width's boundary pairs
(cv 01a14f7e: each a varint, 255 read back, 256 refused `kernel/range-pin` by name). -/
def rangePinVecs : G (List ByteArray) := do
  let c := Codec.Kernel.rangePinWire Sim.dc
  let drawn ← each 2 fun _ => do return c.bytes (← rangePinVec)
  let (p, rel, w, pre, _, _) ← rangePinVec
  -- the floor last before an empty listing: cut into the listing's count, the input is `truncated`
  let top := c.bytes (p, rel, w, pre, 2 ^ 64 - 1, [])
  return drawn ++ [top, top.extract 0 (top.size - 1), c.bytes (p, 255, w, pre, 0, []), c.bytes (p, 256, w, pre, 0, []),
    c.bytes (p, rel, 255, pre, 0, []), c.bytes (p, rel, 256, pre, 0, [])]

/-- `kernel/rows`' vectors: two drawn Worlds, then the cap's boundary pair: a relation whose one row's amount
is exactly its cap, its head counting and summing it (read back), and the same World one past it (refused
`kernel/rows` by name). -/
def rowsVecs : G (List (WorldWire Sim.D)) := do
  let drawn ← each 2 fun _ => toWire <$> Vectors.world
  let w ← Vectors.world
  let p ← dig
  let k ← bytesN 2
  let at_ (sum : Nat) : World Sim.D :=
    { w with rows := rowsOf (w.rows.toList ++ [(.head p 7, .head 1 sum 4 40 2 true 0), (.row ⟨p, 7, k⟩, .row sum ByteArray.empty 0)]) }
  return drawn ++ [toWire (at_ 40), toWire (at_ 41)]

/-- `kernel/rows-headed`'s vectors: two drawn Worlds, then the count's boundary pair: a head counting
its one row (read back), and the same World with the head counting two (refused `kernel/rows-headed`). -/
def headedVecs : G (List (WorldWire Sim.D)) := do
  let drawn ← each 2 fun _ => toWire <$> Vectors.world
  let w ← Vectors.world
  let p ← dig
  let k ← bytesN 3
  let at_ (count : Nat) : World Sim.D :=
    { w with rows := rowsOf (w.rows.toList ++ [(.head p 9, .head count 5 4 40 3 true 0), (.row ⟨p, 9, k⟩, .row 5 ByteArray.empty 0)]) }
  return drawn ++ [toWire (at_ 1), toWire (at_ 2)]

/-- `kernel/carried-rows` / `-headed`: two drawn carried states, then the World vectors' boundary rows. -/
def carriedRowsVecs (forCap : Bool) : G (List (CarriedWire Sim.D)) := do
  let drawn ← each 2 fun _ => carriedToWire <$> Vectors.carried
  let c ← Vectors.carried
  let p ← dig
  let k ← bytesN 3
  let at_ (count sum : Nat) : Carried Sim.D :=
    { c with rows := rowsOf (c.rows.toList ++ [(.head p 9, .head count sum 4 40 3 true 0), (.row ⟨p, 9, k⟩, .row sum ByteArray.empty 0)]) }
  return drawn ++ (if forCap then [carriedToWire (at_ 1 40), carriedToWire (at_ 1 41)]
    else [carriedToWire (at_ 1 5), carriedToWire (at_ 2 5)])

/-- `kernel/rows-parented`'s vectors: two drawn Worlds, then the boundary pair: a relation under a live
parent cell (read back), and the same World without that cell (refused `kernel/rows-parented`). -/
def parentedVecs : G (List (WorldWire Sim.D)) := do
  let drawn ← each 2 fun _ => toWire <$> Vectors.world
  let w ← Vectors.world
  let p ← dig
  let k ← bytesN 3
  let r := rowsOf (w.rows.toList ++ [(.head p 9, .head 1 5 4 40 3 true 0), (.row ⟨p, 9, k⟩, .row 5 ByteArray.empty 0)])
  return drawn ++ [toWire { w with trie := withLive w.trie p, rows := r }, toWire { w with rows := r }]

/-- `kernel/carried-rows-parented`'s vectors: the same pair over a carried state. -/
def carriedParentedVecs : G (List (CarriedWire Sim.D)) := do
  let drawn ← each 2 fun _ => carriedToWire <$> Vectors.carried
  let c ← Vectors.carried
  let p ← dig
  let k ← bytesN 3
  let r := rowsOf (c.rows.toList ++ [(.head p 9, .head 1 5 4 40 3 true 0), (.row ⟨p, 9, k⟩, .row 5 ByteArray.empty 0)])
  return drawn ++ [carriedToWire { c with trie := withLive c.trie p, rows := r }, carriedToWire { c with rows := r }]

/-! ### A relation key (LANG-57)

A key's bytes are the data encoding of its fields in declared order (`Lang.keyBytes`), and the range
read lists rows in key-byte order, so the encoding IS the order (`Lang.Proofs.KeyOrder.keyBytes_compare`).
One fixed key `(n nat) (f bool) (d digest)`: naturals 0, 1, 255, 256 and 2^64 - 1 (the bytes ascend
with the numbers: big-endian), a 31-byte digest before a 32-byte one, `true` after `false`, and the
boundary row, a key cut one byte short, refused. A change of the natural's wire moves the shape, so
the tag, and every row is re-drawn. -/

open Lang in
def keyVecDecl : RelDecl :=
  { key := [("n", .nat), ("f", .bool), ("d", .digest)], val := .record [], limit := 1, sum := none, cap := 0,
    retract := false, guard := none }

open Lang in
def keyVecTy : Ty := keyWireTy keyVecDecl keyVecDecl.key.length

open Lang in
def keyVec (n : Nat) (f : Bool) (dlen : Nat) : ByteArray :=
  (keyBytes keyVecDecl (.record [("d", .digest ⟨Array.replicate dlen 0xab⟩), ("f", .bool f), ("n", .nat n)])).getD
    ByteArray.empty

def keyVecs : List ByteArray :=
  let full := keyVec 256 false 32
  [keyVec 0 false 32, keyVec 1 false 32, keyVec 255 false 32, full, keyVec (2 ^ 64 - 1) false 32,
    keyVec 1 false 31, keyVec 1 true 32, full.extract 0 (full.size - 1)]

/-! ### Versions and floors (KERNEL-54)

The u64 varint's own rows: 0, 127, 128 (the one-byte boundary pair), 2^64 − 1 (ten bytes, read back),
then refused by name: 2^64 (nine `80` then a tenth byte of 2, `pastBound`), an eleventh byte (`pastBound 10 11`), a
non-minimal spelling of 0 (`80 00`, `varint/overlong`) and a continuation with no next byte (`truncated`).
The entry and the World's row leaf each carry the boundary through their own codec: the largest
version (and floor) read back, and the same field spelled 2^64, eleven bytes long, or overlong refused. -/

def varint64Vecs : List ByteArray :=
  [Stream.varint64.bytes 0, Stream.varint64.bytes 127, Stream.varint64.bytes 128,
    Stream.varint64.bytes (2 ^ 64 - 1),
    ⟨#[0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x02]⟩,
    ⟨#[0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x81, 0x00]⟩,
    ⟨#[0x80, 0x00]⟩, ⟨#[0x80]⟩]

/-! ### A byte string behind a varint length (cv 01a14f7e)

`bytesV keyBytesMax`'s own rows: the empty string, 127 bytes (a one-byte length) and 128 (the widest,
a two-byte length `80 01`), read back; then refused: a length of 129 (`81 01`, `pastBound`), a
non-minimal length (`80 00`, `varint/overlong`), and a length of 3 over two bytes (`truncated`). -/

def bytesVVecs : List ByteArray :=
  let c := Stream.bytesV Bounds.keyBytesMax
  [c.bytes ByteArray.empty, c.bytes ⟨Array.replicate 127 7⟩, c.bytes ⟨Array.replicate 128 9⟩,
    ⟨#[0x81, 0x01]⟩ ++ ⟨Array.replicate 129 9⟩, ⟨#[0x80, 0x00]⟩, ⟨#[0x03, 0x01, 0x02]⟩]

/-- A live entry whose version is spelled `ver` (raw bytes), then `c`. -/
def rawLive (ver : ByteArray) (c : Cell) : ByteArray :=
  ⟨#[0]⟩ ++ ver ++ Codec.Kernel.cell.bytes c

def entryVecs : G (List ByteArray) := do
  let c ← cell
  return [Codec.Kernel.entry.bytes (.live (← cell) (← version)), Codec.Kernel.entry.bytes .tomb,
    Codec.Kernel.entry.bytes (.live c (2 ^ 64 - 1)),
    rawLive ⟨#[0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x02]⟩ c,
    rawLive ⟨#[0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x81, 0x00]⟩ c,
    rawLive ⟨#[0x80, 0x00]⟩ c]

def rowLeafVecs : G (List ByteArray) := do
  let drawn ← each 2 fun k => do return Codec.Kernel.rowLeaf.bytes (← Vectors.rowLeaf k)
  let amt ← nat64
  let v ← bytes 6
  let raw (ver : ByteArray) : ByteArray :=
    ⟨#[1]⟩ ++ Stream.nat64.bytes amt ++ ver ++ (Stream.rawBytes Bounds.valueBytesMax).bytes v
  let head := Codec.Kernel.rowLeaf.bytes (.head 1 2 3 4 5 true 0)
  let rawHead (floor : ByteArray) : ByteArray := head.extract 0 (head.size - 1) ++ floor
  return drawn ++ [Codec.Kernel.rowLeaf.bytes (.row amt v (2 ^ 64 - 1)),
    raw ⟨#[0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x02]⟩,
    raw ⟨#[0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x81, 0x00]⟩, raw ⟨#[0x80, 0x00]⟩,
    Codec.Kernel.rowLeaf.bytes (.head 1 2 3 4 5 true (2 ^ 64 - 1)),
    rawHead ⟨#[0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x02]⟩, rawHead ⟨#[0x80, 0x00]⟩]

/-- The row pin's preimage: two drawn, then the floor at its largest (2^64 − 1, all eight bytes) and the same
leaf one byte short (`truncated`: a fixed-width field has no larger value to refuse). -/
def rowLeafHashedVecs : G (List ByteArray) := do
  let drawn ← each 2 fun k => do return Codec.Kernel.rowLeafHashed.bytes (← Vectors.rowLeaf k)
  let top := Codec.Kernel.rowLeafHashed.bytes (.head 1 2 3 4 5 false (2 ^ 64 - 1))
  return drawn ++ [top, top.extract 0 (top.size - 1)]

/-! ### A package (cv 01a14e58-1586, LANG-15's set)

One row per term tag (0–18; tag 15, a record's field, rides in the record row), per type tag (0–7; tag
6, a row's field, rides in the record type), per primitive code (0–11), and per package section
(imports, a relation with every option and one with none, methods and laws, a doc). Then the boundary:
the first unused term tag (19), type tag (8) and primitive code (12), each refused `lang/package/5` by
name. A Lang change that gives one of them a meaning flips its row from refused to read under an
unchanged tag: the gate goes red, and `Bounds.packageWireVersion` moves (LANG-60). Then the doc's
bound (a doc of `docMax` bytes read, one byte past it refused `lang/package/5`, a doc holding `"`
refused, a doc holding a line feed and one that is not UTF-8 each refused), and the version: the current tree at the previous version byte, and a LANG-59-era
package's bytes as they were written (no version byte), each refused `lang/package-version/5`. -/

open Lang in
/-- The empty package around a body and a state type. -/
def pkgOf (body : Term) (state : Ty := .record []) : Package :=
  { imports := [], state, iface := .record [], body, methods := [], laws := [] }

open Lang in
/-- An operand of a primitive's operand type. -/
def operand : Ty → Term
  | .bytes => .bytes ⟨#[0x61]⟩
  | .digest => .digest ⟨#[0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08]⟩
  | .bool => .bool true
  | _ => .nat 1

open Lang in
def termRows : List Term :=
  [.var 0, .lam .nat (.var 0), .app (.var 0) (.nat 1), .fix (.var 0), .nat 7, .bool true, .bytes ⟨#[0x68, 0x69]⟩,
   .prim .add (.nat 1) (.nat 2), .record [("a", .nat 1)], .get (.var 0) "a", .extend (.var 0) [("b", .nat 2)],
   .inj (.sum [("a", .nat)]) "a" (.nat 1), .case (.var 0) [("a", .var 0)], .ite (.bool true) (.nat 1) (.nat 2),
   .ref 0, .digest ⟨#[0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08]⟩, .refuse .nat "too big".toUTF8, .hole 7 [.nat 3, .bool true]]

open Lang in
def tyRows : List Ty :=
  [.nat, .bool, .bytes, .fn .nat .bool, .record [("a", .nat)], .sum [("a", .nat), ("b", .record [])], .digest]

open Lang in
def primRows : List Term :=
  [.add, .sub, .mul, .div, .mod, .eq, .lt, .le, .beq, .cat, .deq, .lenLe].map fun p =>
    .prim p (operand p.left) (operand p.right)

open Lang in
def relAll : RelDecl :=
  { key := [("k", .nat)], val := .record [("n", .nat)], limit := 4, sum := some "n", cap := 10, retract := true,
    guard := some "g" }

open Lang in
def relNone : RelDecl :=
  { key := [("k", .nat)], val := .nat, limit := 1, sum := none, cap := 0, retract := false, guard := none }

open Lang in
def sectionRows : List Package :=
  [{ pkgOf (.record []) with imports := [⟨#[0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08]⟩] },
   { pkgOf (.record []) with rels := [("r", relAll)] },
   { pkgOf (.record []) with rels := [("r", relNone)] },
   { pkgOf (.record []) with methods := ["m"], laws := ["l"] },
   { pkgOf (.record []) with doc := "one line about the package".toUTF8 },
   { pkgOf (.hole 7 [.bool true, .nat 3]) with holes := [
     { name := 7, ctx := [.bool, .nat], ty := .nat,
       code := [⟨.var 1, [.row 2 ⟨#[0x11, 0x22]⟩ 9]⟩,
         ⟨.nat 5, [.cell ⟨#[0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08]⟩]⟩],
       selectionRel := 3, selectionKey := ⟨#[0x33, 0x44]⟩,
       hypotheses := [none, some (.row 4 ⟨#[0x55]⟩ 10)],
       guardPin := some (.row 5 ⟨#[0x66]⟩ 11), guard := .var 0 }] }]

open Lang Lang.Wire in
/-- A package tree with `body` and `state` as given trees (the boundary rows: a node no reader knows). -/
def rawPackage (body state : Tree) (doc : ByteArray := .empty) (version := Lang.Bounds.packageWireVersion) :
    ByteArray :=
  let t : Tree := .node 0 .empty [.node 0 .empty [], state, tyTree (.record []), body, .node 1 .empty [],
    .node 1 .empty [], .node 2 .empty [], .node 0 doc [], .node 3 .empty []]
  if h : t.fits nodeMax depthMax then ByteArray.mk #[version] ++ treeStream.bytes ⟨t, h⟩ else ByteArray.empty

/-- A LANG-59-era package as it was written (`lang/package/2`, no version byte): `pkgOf (.var 0)`, the
first row of that site's vectors. -/
def lang59Package : ByteArray :=
  ⟨#[0x00, 0x00, 0x07, 0x00, 0x00, 0x00, 0x04, 0x00, 0x00, 0x04, 0x00, 0x00, 0x00, 0x04, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x01, 0x00, 0x00, 0x01, 0x00, 0x00, 0x02, 0x00, 0x00]⟩

open Lang Lang.Wire in
def packageVecs : List ByteArray :=
  -- through `encodePackage`: a row whose package had no tree in bounds would be empty bytes, refused
  (termRows.map pkgOf ++ tyRows.map (pkgOf (.record []) ·) ++ primRows.map pkgOf ++ sectionRows).map
      (fun p => (encodePackage p).getD ByteArray.empty) ++
    [rawPackage (.node 19 .empty []) (tyTree (.record [])),
     rawPackage (.node 18 .empty []) (tyTree (.record [])),
     rawPackage (termTree (.record [])) (.node 8 .empty []),
     rawPackage (.node 7 (Stream.u8.bytes 12) [termTree (.nat 1), termTree (.nat 2)]) (tyTree (.record [])),
     rawPackage (termTree (.record [])) (tyTree (.record [])) ⟨Array.replicate Lang.Bounds.docMax 0x61⟩,
     rawPackage (termTree (.record [])) (tyTree (.record [])) ⟨Array.replicate (Lang.Bounds.docMax + 1) 0x61⟩,
     rawPackage (termTree (.record [])) (tyTree (.record [])) "a \"quoted\" doc".toUTF8,
     rawPackage (termTree (.record [])) (tyTree (.record [])) (version := Lang.Bounds.packageWireVersion - 1),
     rawPackage (termTree (.record [])) (tyTree (.record [])) ⟨#[0x61, 0x0a, 0x62]⟩,
     rawPackage (termTree (.record [])) (tyTree (.record [])) ⟨#[0x61, 0xff]⟩,
     lang59Package]

def sites : List Site :=
  [ site "i64" Stream.i64 (each 2 fun _ => (·.toInt64) <$> u64) text,
    site "bool" Stream.bool (pure [false, true]) text,
    site "kernel/discipline" Codec.Kernel.discipline (pure [.rom, .appendOnly, .ram, .value]) text,
    site "kernel/op" Codec.Kernel.op (each 2 Vectors.op) text,
    site "kernel/cell" Codec.Kernel.cell (each 2 fun _ => Vectors.cell) text,
    site "kernel/act" Codec.Kernel.act (each 3 Vectors.act) text,
    site "kernel/touch" (Codec.Kernel.touch Sim.dc) (each 2 fun _ => Vectors.touch) text,
    site "kernel/turn" (Codec.Kernel.turn Sim.dc) (each 2 fun _ => Vectors.turn) text,
    site "kernel/right" Codec.Kernel.right (each 6 Vectors.right) text,
    site "kernel/acct-ref" (Codec.Kernel.acctRef Sim.dc) (each 2 Vectors.acctRef) text,
    site "kernel/body" (Codec.Kernel.body Sim.dc) (each 13 Vectors.body) text,
    site "kernel/unsigned" (Codec.Kernel.unsigned Sim.dc) (each 2 fun k => Vectors.unsigned (k * 6)) text,
    site "kernel/call" (Codec.Kernel.call Sim.dc) (each 2 fun k => do return ⟨← Vectors.unsigned (k * 7), ← bytes 8⟩) text,
    ⟨"varint64", Tag.of "varint64" Stream.varint64, pure varint64Vecs, print Stream.varint64 text⟩,
    ⟨"bytesV", Tag.of "bytesV" (Stream.bytesV Bounds.keyBytesMax), pure bytesVVecs,
      print (Stream.bytesV Bounds.keyBytesMax) text⟩,
    ⟨"kernel/entry", Tag.of "kernel/entry" Codec.Kernel.entry, entryVecs, print Codec.Kernel.entry text⟩,
    site "kernel/slot" (Codec.Kernel.slot Sim.dc) (each 2 fun k => if k = 0 then do return .cell (← dig) else do return .nullifier (← dig))
      text,
    site "kernel/leaf" Codec.Kernel.leaf (each 3 fun k => match k with
      | 0 => do return .entry (.live (← Vectors.cell) (← version)) | 1 => pure (.entry .tomb) | _ => pure .spent) text,
    site "kernel/leaf-fit" (fitList Sim.dc) (each 2 fun _ => (·.toList) <$> trie) text,
    site "kernel/trie-order" (cells Sim.env Sim.dc) (each 2 fun _ => trie) (fun t => text t.toList),
    site "kernel/journal-order" (journalTrie Sim.env Sim.dc)
      (each 2 fun _ => do return journalOf (← journal ((← below 1000) + 3))) (fun t => text t.toList),
    site "kernel/proof" (proof (journalSpec Sim.env) Sim.dc Sim.dc) proofVecs text,
    site "kernel/refusal-slot" (refusalSlot Sim.dc)
      (each 3 fun k => match k with
        | 0 => do return .tx (← dig) | 1 => do return .count (← dig) (← u64) | _ => do return .total (← dig) (← u64)) text,
    site "kernel/refusal-leaf" (refusalLeaf Sim.dc)
      (each 2 fun k => if k = 0 then do return .refused (← nat64) (← nat64) (← dig) else do return .count (← nat64)) text,
    site "kernel/refusal-order" (refusalsTrie Sim.env Sim.dc)
      (each 2 fun _ => do
        let h := (← below 1000) + 3
        let r ← refusals h
        return refusalsOf (r ++ totalOf h (← dig) r)) (fun t => text t.toList),
    site "kernel/row-key" (Codec.Kernel.rowKey Sim.dc) rowKeyVecs text,
    ⟨"kernel/row-leaf", Tag.of "kernel/row-leaf" Codec.Kernel.rowLeaf, rowLeafVecs, print Codec.Kernel.rowLeaf text⟩,
    ⟨"kernel/row-leaf-hashed", Tag.of "kernel/row-leaf-hashed" Codec.Kernel.rowLeafHashed, rowLeafHashedVecs,
      print Codec.Kernel.rowLeafHashed text⟩,
    site "kernel/row-act" Codec.Kernel.rowAct (each 5 Vectors.rowAct) text,
    site "kernel/row-touch" (Codec.Kernel.rowTouch Sim.dc) (each 2 fun _ => Vectors.rowTouch) text,
    site "kernel/range-read" (Codec.Kernel.rangeRead Sim.dc) rangeReadVecs text,
    ⟨"kernel/range-pin", Tag.of "kernel/range-pin" (Codec.Kernel.rangePinWire Sim.dc), rangePinVecs,
      print (Codec.Kernel.rangePinWire Sim.dc) text⟩,
    site "kernel/row-order" (rowsTrie Sim.env Sim.dc) (each 2 fun _ => do return rowsOf (← rows [← dig]))
      (fun t => text t.toList),
    site "kernel/rows" (rowsWire Sim.env Sim.dc) rowsVecs printWire,
    site "kernel/rows-headed" (headedWire Sim.env Sim.dc) headedVecs printWire,
    site "kernel/rows-parented" (parentedWire Sim.env Sim.dc) parentedVecs printWire,
    site "kernel/journal" (journalWire Sim.env Sim.dc) (each 2 fun _ => toWire <$> Vectors.world) printWire,
    site "kernel/refusals" (refusalsWire Sim.env Sim.dc) refusalsVecs printWire,
    site "kernel/refusals-disjoint" (disjointWire Sim.env Sim.dc) disjointVecs printWire,
    site "kernel/steps" (stepsWire Sim.env Sim.dc) stepsVecs printWire,
    site "kernel/refusals-counted" (countedWire Sim.env Sim.dc) countedVecs printWire,
    site "kernel/refused" (Codec.Kernel.refused Sim.dc) Vectors.refusedVecs text,
    site "kernel/step" (Codec.Kernel.step Sim.dc) (each 2 Vectors.step) text,
    site "kernel/world-budget" (Codec.Kernel.world Sim.env Sim.dc) worldVecs printWorld,
    site "kernel/carried-journal" (carriedJournalWire Sim.env Sim.dc)
      (each 2 fun _ => carriedToWire <$> Vectors.carried) printCarriedWire,
    site "kernel/carried-rows" (carriedRowsWire Sim.env Sim.dc) (carriedRowsVecs true) printCarriedWire,
    site "kernel/carried-rows-headed" (carriedHeadedWire Sim.env Sim.dc) (carriedRowsVecs false) printCarriedWire,
    site "kernel/carried-rows-parented" (carriedParentedWire Sim.env Sim.dc) carriedParentedVecs printCarriedWire,
    site "kernel/carried" (Codec.Kernel.carried Sim.env Sim.dc) (each 2 fun _ => Vectors.carried) printCarried,
    site "path/badComponent" (Field.pathCodec pathMax (by decide)) pathVecs (fun p => text p.val),
    site "host/base/retained" (Host.Base.codec (Codec.Kernel.world Sim.env Sim.dc)) baseVecs printBase,
    site "host/carried-head" (Host.Carry.head Sim.dc) (each 2 fun _ => do return ⟨← dig, ← nat64, ← dig⟩) text,
    ⟨"lang/package/5", Tag.of "lang/package/5" Lang.Wire.packageCodec, pure packageVecs,
      print Lang.Wire.packageCodec text⟩,
    ⟨"lang/package-version/5", Tag.of "lang/package-version/5" Lang.Wire.packageVersion,
      pure [ByteArray.mk #[Lang.Bounds.packageWireVersion], ByteArray.mk #[Lang.Bounds.packageWireVersion - 1]],
      print Lang.Wire.packageVersion fun () => "()"⟩,
    ⟨"lang/key", Tag.of "lang/key" (Lang.Wire.dataStream keyVecTy), pure keyVecs,
      print (Lang.Wire.dataStream keyVecTy) fun v => (Lang.Print.data (Lang.Wire.toData keyVecTy v)).getD "?"⟩,
    ⟨"lang/data: no value", Tag.of "lang/data: no value" Lang.Wire.noData, pure [ByteArray.empty],
      print Lang.Wire.noData (fun e => nomatch e)⟩ ]

/-! ## The table -/

def hex (b : ByteArray) : String :=
  let digit (n : UInt8) : Char := if n < 10 then Char.ofNat (48 + n.toNat) else Char.ofNat (87 + n.toNat)
  b.foldl (fun s x => (s.push (digit (x >>> 4))).push (digit (x &&& 15))) ""

def unhex (s : String) : Option ByteArray :=
  let val (c : Char) : Option UInt8 :=
    if '0' ≤ c && c ≤ '9' then some (c.toNat - 48).toUInt8
    else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 87).toUInt8 else none
  let rec go : List Char → ByteArray → Option ByteArray
    | [], b => some b
    | h :: l :: rest, b => do go rest (b.push ((← val h) <<< 4 ||| (← val l)))
    | [_], _ => none
  go s.toList ByteArray.empty

structure Row where
  site : String
  index : Nat
  tag : String
  bytes : String
  text : String
  deriving BEq

def Row.line (r : Row) : String := s!"{r.site}\t{r.index}\t{r.tag}\t{r.bytes}\t{r.text}"

def header : String :=
  "# site\tvector\ttag\tbytes\tdecoded — GENERATED by `lake exe codec-vectors --write gates/codec-vectors.tsv` " ++
  "(Emit.Vectors, CODEC-28): a row is re-drawn only when its site's tag moves; under an unchanged tag the " ++
  "decoded text must not change (a change of meaning under the same bytes bumps the label).\n"

def parse (text : String) : Except String (List Row) :=
  text.splitOn "\n" |>.foldlM (init := []) fun acc line =>
    if line.isEmpty || line.startsWith "#" then pure acc
    else match line.splitOn "\t" with
      | [s, i, t, b, x] => match i.toNat? with
        | some n => pure (acc ++ [⟨s, n, t, b, x⟩])
        | none => throw s!"bad vector index: {line}"
      | _ => throw s!"a row is site<TAB>vector<TAB>tag<TAB>bytes<TAB>decoded: {line}"

/-- The site's own vectors, drawn from a seed of its name. -/
def fresh (s : Site) : List Row :=
  let (bs, _) := s.draw.run ⟨Sim.fnv s.name.toUTF8⟩
  bs.zipIdx.map fun (b, i) => ⟨s.name, i, s.tag.toHex, hex b, s.print b⟩

/-- Keep every row whose site's tag is unchanged, verbatim; draw the rest. -/
def write (old : List Row) : List Row :=
  sites.flatMap fun s =>
    match old.filter (fun r => r.site == s.name && r.tag == s.tag.toHex) with
    | [] => fresh s
    | kept => kept

def check (rows : List Row) : List String :=
  let perSite := sites.flatMap fun s =>
    let mine := rows.filter (·.site == s.name)
    let current := mine.filter (·.tag == s.tag.toHex)
    let moved := if current.isEmpty then
        [s!"{s.name}: no vector under its current tag {s.tag.toHex} (tag moved or new site): " ++
          "run `lake exe codec-vectors --write gates/codec-vectors.tsv`, and say in the commit what re-geneses"]
      else []
    let stale := (mine.filter (·.tag != s.tag.toHex)).map fun r =>
      s!"{s.name} vector {r.index}: stale tag {r.tag}: run --write"
    let meaning := current.filterMap fun r =>
      match unhex r.bytes with
      | none => some s!"{s.name} vector {r.index}: bytes are not hex"
      | some b =>
        let now := s.print b
        if now == r.text then none
        else some (s!"{s.name} vector {r.index}: MEANING CHANGED under the same tag {r.tag}: the same bytes " ++
          s!"decoded to `{r.text}` and now decode to `{now}`: rename the refinement (its tag moves, every " ++
          "stamp with it); --write never re-pins a row whose tag did not move")
    moved ++ stale ++ meaning
  let orphans := (rows.filter fun r => !(sites.any (·.name == r.site))).map fun r =>
    s!"{r.site} vector {r.index}: no such site"
  perSite ++ orphans

def run (args : List String) : IO UInt32 := do
  match args with
  | ["--write", path] =>
    let old ← if ← System.FilePath.pathExists path then
        match parse (← IO.FS.readFile path) with
        | .ok r => pure r
        | .error e => IO.eprintln e; return 1
      else pure []
    let rows := write old
    IO.FS.writeFile path (header ++ String.join (rows.map (·.line ++ "\n")))
    IO.println s!"codec-vectors: wrote {rows.length} vectors of {sites.length} sites"
    return 0
  | ["--check", path] =>
    match parse (← IO.FS.readFile path) with
    | .error e => IO.eprintln e; return 1
    | .ok rows =>
      match check rows with
      | [] => IO.println s!"codec-vectors: ok ({rows.length} vectors of {sites.length} sites)"; return 0
      | bad => for b in bad do IO.eprintln b
               IO.eprintln s!"codec-vectors: RED ({bad.length})"; return 1
  | _ => IO.eprintln "usage: codec-vectors (--write | --check) PATH"; return 2

end Nanodregg.Emit.Vectors
