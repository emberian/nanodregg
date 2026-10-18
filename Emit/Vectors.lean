import Codec.World
import Codec.Layout
import Host.Base
import Host.Carry
import Lang.Wire.Data
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
  Refused, Step, Trie.Proof

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
  if k = 0 then return .head (← below 9) (← below 900) (← below 4096) (← nat64) (← below 129) ((← below 2) = 0)
  else return .row (← nat64) (← bytes 6)
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
      rs := rs ++ [(RowSlot.row ⟨p, rel, k⟩, RowLeaf.row amt (← bytes 6))]
    let limit := uniq.length + (← below 3)
    let cap := sum + (← below 100)
    out := out ++ (RowSlot.head p rel, RowLeaf.head uniq.length sum limit cap width ((← below 2) = 0)) :: rs
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
  | _ => return .enroll (← nat64)
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
  | 7 => return .grant (← dig) (← dig) (← list 3 (do right (← below 4))) (← opt dig)
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
      let e : Entry ← if (← below 2) = 0 then (do return .live (← cell)) else pure .tomb
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

/-- A refusals listing a World at height `h` can hold (KERNEL-44): one to three refused transaction
ids, each refused at a height at or just below `h + 1`, and one to two members' counts for the current
window (`refusalsFits`). -/
def refusals (h : Nat) : G (List (RefusalSlot Sim.D × RefusalLeaf)) := do
  let txs ← list1 3 (do return (RefusalSlot.tx (← dig), RefusalLeaf.refused (h + 1 - (← below 3)) (← below 40)))
  let counts ← list1 2 (do
    return (RefusalSlot.count (← dig) (refusalWindow h), RefusalLeaf.count ((← below Bounds.refusalsPerWindow) + 1)))
  return txs ++ counts

/-- The canonical refusals trie of a listing (KERNEL-44). -/
def refusalsOf (l : List (RefusalSlot Sim.D × RefusalLeaf)) : Refusals Sim.D :=
  Trie.build (refusalSpec Sim.env) (refusalSpec Sim.env).depth 0 l

/-- The live cells of a cells trie: the parents a relation may sit under. -/
def liveIds (t : Cells Sim.D) : List Sim.D :=
  t.toList.filterMap fun p => match p with | (.cell c, .entry (.live _)) => some c | _ => none

/-- A cells trie with one more live cell, `p`. -/
def withLive (t : Cells Sim.D) (p : Sim.D) : Cells Sim.D :=
  Trie.build (trieSpec Sim.env) (trieSpec Sim.env).depth 0 (t.toList ++ [(.cell p, .entry (.live ⟨0, .ram, []⟩))])

def world : G (World Sim.D) := do
  let h := (← below 1000) + 3
  let t ← trie
  return { trie := t, journal := journalOf (← journal h), refusals := refusalsOf (← refusals h),
           rows := rowsOf (← rows (liveIds t)), height := h, steps := h + (← below 5), chain := ← dig, allowance := ← below (2 ^ 40),
           origin := ← dig }

def refused : G (Refused Sim.D) := do
  return ⟨← dig, ← dig, ← nat64, ← nat64, ← below 40, ← bytes 8⟩

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
    s!"indexCount := {b.indexCount}, indexLast := {text b.indexLast}}"

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

/-- `kernel/world-budget`'s vectors: two drawn Worlds, then a third at the budget's boundary (storage plus
allowance exactly 2^64 − 1, read back) and the same World one past it (refused `kernel/world-budget` by name,
cv 01a14ba9-cbf4). Every counter of the refused one still fits its `u64`: only the sum is over. -/
def worldVecs : G (List (World Sim.D)) := do
  let drawn ← each 2 fun _ => Vectors.world
  let w ← Vectors.world
  return drawn ++ [{ w with allowance := 2 ^ 64 - 1 - w.weight }, { w with allowance := 2 ^ 64 - w.weight }]

/-- `kernel/refusals`' vectors: two drawn Worlds, then the per-window budget's boundary pair (KERNEL-44):
a member's count at exactly `Bounds.refusalsPerWindow` (read back) and the same World at one more
(refused `kernel/refusals` by name). -/
def refusalsVecs : G (List (WorldWire Sim.D)) := do
  let drawn ← each 2 fun _ => toWire <$> Vectors.world
  let w ← Vectors.world
  let m ← dig
  let at_ (n : Nat) : World Sim.D :=
    { w with refusals := refusalsOf (w.refusals.toList ++ [(.count m (refusalWindow w.height), .count n)]) }
  return drawn ++ [toWire (at_ Bounds.refusalsPerWindow), toWire (at_ (Bounds.refusalsPerWindow + 1))]

/-- `kernel/steps`' vectors: two drawn Worlds, then the boundary pair: a step count equal to the height
(read back) and one less (refused `kernel/steps` by name). -/
def stepsVecs : G (List (WorldWire Sim.D)) := do
  let drawn ← each 2 fun _ => toWire <$> Vectors.world
  let w ← Vectors.world
  return drawn ++ [toWire { w with steps := w.height }, toWire { w with steps := w.height - 1 }]

/-- `kernel/refusals-disjoint`'s vectors: two drawn Worlds, then the boundary pair: a World whose
refused transaction id is not journaled (read back), and the same World with that id journaled too
(refused `kernel/refusals-disjoint` by name). -/
def disjointVecs : G (List (WorldWire Sim.D)) := do
  let drawn ← each 2 fun _ => toWire <$> Vectors.world
  let w ← Vectors.world
  let k ← dig
  let r := refusalsOf (w.refusals.toList ++ [(.tx k, .refused w.height 1)])
  let base : World Sim.D := { w with refusals := r }
  let both : World Sim.D :=
    { base with journal := journalOf (w.journal.toList ++ [(k, (w.height - 5, ← dig))]) }
  return drawn ++ [toWire base, toWire both]

/-- `kernel/row-key`'s vectors: a head and a drawn row, then the key width's boundary pair: a row key of
exactly `Bounds.keyBytesMax` (128) bytes reads back, one of 129 is refused by the codec (`pastBound` at
the length byte; admission's own refusal of a wider key is `overBound rows`, and of a key not at its
relation's width `keyWidth`). -/
def rowKeyVecs : G (List (RowSlot Sim.D)) := do
  let p ← dig
  let rel ← below 256
  return [← rowSlot 0, ← rowSlot 1, .row ⟨p, rel, ← bytesN Bounds.keyBytesMax⟩,
    .row ⟨p, rel, ← bytesN (Bounds.keyBytesMax + 1)⟩]

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
  | (.head p rel, .head _ _ _ _ width _) :: _ =>
    let rs := (rowsOf l).toList.filter fun q => match q.1 with
      | .row k => decide (k.parent = p) && decide (k.rel = rel) | _ => false
    return (p, rel, width, ByteArray.empty, rs.map fun q => (q.1, rowDigest Sim.env q.2))
  | _ => return (← dig, 0, 0, ByteArray.empty, [])

/-- `kernel/rows`' vectors: two drawn Worlds, then the cap's boundary pair: a relation whose one row's amount
is exactly its cap, its head counting and summing it (read back), and the same World one past it (refused
`kernel/rows` by name). -/
def rowsVecs : G (List (WorldWire Sim.D)) := do
  let drawn ← each 2 fun _ => toWire <$> Vectors.world
  let w ← Vectors.world
  let p ← dig
  let k ← bytesN 2
  let at_ (sum : Nat) : World Sim.D :=
    { w with rows := rowsOf (w.rows.toList ++ [(.head p 7, .head 1 sum 4 40 2 true), (.row ⟨p, 7, k⟩, .row sum ByteArray.empty)]) }
  return drawn ++ [toWire (at_ 40), toWire (at_ 41)]

/-- `kernel/rows-headed`'s vectors: two drawn Worlds, then the count's boundary pair: a head counting
its one row (read back), and the same World with the head counting two (refused `kernel/rows-headed`). -/
def headedVecs : G (List (WorldWire Sim.D)) := do
  let drawn ← each 2 fun _ => toWire <$> Vectors.world
  let w ← Vectors.world
  let p ← dig
  let k ← bytesN 3
  let at_ (count : Nat) : World Sim.D :=
    { w with rows := rowsOf (w.rows.toList ++ [(.head p 9, .head count 5 4 40 3 true), (.row ⟨p, 9, k⟩, .row 5 ByteArray.empty)]) }
  return drawn ++ [toWire (at_ 1), toWire (at_ 2)]

/-- `kernel/carried-rows` / `-headed`: two drawn carried states, then the World vectors' boundary rows. -/
def carriedRowsVecs (forCap : Bool) : G (List (CarriedWire Sim.D)) := do
  let drawn ← each 2 fun _ => carriedToWire <$> Vectors.carried
  let c ← Vectors.carried
  let p ← dig
  let k ← bytesN 3
  let at_ (count sum : Nat) : Carried Sim.D :=
    { c with rows := rowsOf (c.rows.toList ++ [(.head p 9, .head count sum 4 40 3 true), (.row ⟨p, 9, k⟩, .row sum ByteArray.empty)]) }
  return drawn ++ (if forCap then [carriedToWire (at_ 1 40), carriedToWire (at_ 1 41)]
    else [carriedToWire (at_ 1 5), carriedToWire (at_ 2 5)])

/-- `kernel/rows-parented`'s vectors: two drawn Worlds, then the boundary pair: a relation under a live
parent cell (read back), and the same World without that cell (refused `kernel/rows-parented`). -/
def parentedVecs : G (List (WorldWire Sim.D)) := do
  let drawn ← each 2 fun _ => toWire <$> Vectors.world
  let w ← Vectors.world
  let p ← dig
  let k ← bytesN 3
  let r := rowsOf (w.rows.toList ++ [(.head p 9, .head 1 5 4 40 3 true), (.row ⟨p, 9, k⟩, .row 5 ByteArray.empty)])
  return drawn ++ [toWire { w with trie := withLive w.trie p, rows := r }, toWire { w with rows := r }]

/-- `kernel/carried-rows-parented`'s vectors: the same pair over a carried state. -/
def carriedParentedVecs : G (List (CarriedWire Sim.D)) := do
  let drawn ← each 2 fun _ => carriedToWire <$> Vectors.carried
  let c ← Vectors.carried
  let p ← dig
  let k ← bytesN 3
  let r := rowsOf (c.rows.toList ++ [(.head p 9, .head 1 5 4 40 3 true), (.row ⟨p, 9, k⟩, .row 5 ByteArray.empty)])
  return drawn ++ [carriedToWire { c with trie := withLive c.trie p, rows := r }, carriedToWire { c with rows := r }]

def sites : List Site :=
  [ site "i64" Stream.i64 (each 2 fun _ => (·.toInt64) <$> u64) text,
    site "bool" Stream.bool (pure [false, true]) text,
    site "kernel/discipline" Codec.Kernel.discipline (pure [.rom, .appendOnly, .ram, .value]) text,
    site "kernel/op" Codec.Kernel.op (each 2 Vectors.op) text,
    site "kernel/cell" Codec.Kernel.cell (each 2 fun _ => Vectors.cell) text,
    site "kernel/act" Codec.Kernel.act (each 3 Vectors.act) text,
    site "kernel/touch" (Codec.Kernel.touch Sim.dc) (each 2 fun _ => Vectors.touch) text,
    site "kernel/turn" (Codec.Kernel.turn Sim.dc) (each 2 fun _ => Vectors.turn) text,
    site "kernel/right" Codec.Kernel.right (each 4 Vectors.right) text,
    site "kernel/acct-ref" (Codec.Kernel.acctRef Sim.dc) (each 2 Vectors.acctRef) text,
    site "kernel/body" (Codec.Kernel.body Sim.dc) (each 13 Vectors.body) text,
    site "kernel/unsigned" (Codec.Kernel.unsigned Sim.dc) (each 2 fun k => Vectors.unsigned (k * 6)) text,
    site "kernel/call" (Codec.Kernel.call Sim.dc) (each 2 fun k => do return ⟨← Vectors.unsigned (k * 7), ← bytes 8⟩) text,
    site "kernel/entry" Codec.Kernel.entry (each 2 fun k => if k = 0 then do return .live (← Vectors.cell) else pure .tomb) text,
    site "kernel/slot" (Codec.Kernel.slot Sim.dc) (each 2 fun k => if k = 0 then do return .cell (← dig) else do return .nullifier (← dig))
      text,
    site "kernel/leaf" Codec.Kernel.leaf (each 3 fun k => match k with
      | 0 => do return .entry (.live (← Vectors.cell)) | 1 => pure (.entry .tomb) | _ => pure .spent) text,
    site "kernel/leaf-fit" (fitList Sim.dc) (each 2 fun _ => (·.toList) <$> trie) text,
    site "kernel/trie-order" (cells Sim.env Sim.dc) (each 2 fun _ => trie) (fun t => text t.toList),
    site "kernel/journal-order" (journalTrie Sim.env Sim.dc)
      (each 2 fun _ => do return journalOf (← journal ((← below 1000) + 3))) (fun t => text t.toList),
    site "kernel/proof" (proof (journalSpec Sim.env) Sim.dc Sim.dc) proofVecs text,
    site "kernel/refusal-slot" (refusalSlot Sim.dc)
      (each 2 fun k => if k = 0 then do return .tx (← dig) else do return .count (← dig) (← u64)) text,
    site "kernel/refusal-leaf" refusalLeaf
      (each 2 fun k => if k = 0 then do return .refused (← nat64) (← nat64) else do return .count (← nat64)) text,
    site "kernel/refusal-order" (refusalsTrie Sim.env Sim.dc)
      (each 2 fun _ => do return refusalsOf (← refusals ((← below 1000) + 3))) (fun t => text t.toList),
    site "kernel/row-key" (Codec.Kernel.rowKey Sim.dc) rowKeyVecs text,
    site "kernel/row-leaf" Codec.Kernel.rowLeaf (each 2 Vectors.rowLeaf) text,
    site "kernel/row-act" Codec.Kernel.rowAct (each 5 Vectors.rowAct) text,
    site "kernel/row-touch" (Codec.Kernel.rowTouch Sim.dc) (each 2 fun _ => Vectors.rowTouch) text,
    site "kernel/range-read" (Codec.Kernel.rangeRead Sim.dc) rangeReadVecs text,
    site "kernel/range-pin" (Codec.Kernel.rangePinWire Sim.dc) (each 2 fun _ => rangePinVec) text,
    site "kernel/row-order" (rowsTrie Sim.env Sim.dc) (each 2 fun _ => do return rowsOf (← rows [← dig]))
      (fun t => text t.toList),
    site "kernel/rows" (rowsWire Sim.env Sim.dc) rowsVecs printWire,
    site "kernel/rows-headed" (headedWire Sim.env Sim.dc) headedVecs printWire,
    site "kernel/rows-parented" (parentedWire Sim.env Sim.dc) parentedVecs printWire,
    site "kernel/journal" (journalWire Sim.env Sim.dc) (each 2 fun _ => toWire <$> Vectors.world) printWire,
    site "kernel/refusals" (refusalsWire Sim.env Sim.dc) refusalsVecs printWire,
    site "kernel/refusals-disjoint" (disjointWire Sim.env Sim.dc) disjointVecs printWire,
    site "kernel/steps" (stepsWire Sim.env Sim.dc) stepsVecs printWire,
    site "kernel/refused" (Codec.Kernel.refused Sim.dc) (each 2 fun _ => Vectors.refused) text,
    site "kernel/step" (Codec.Kernel.step Sim.dc) (each 2 Vectors.step) text,
    site "kernel/world-budget" (Codec.Kernel.world Sim.env Sim.dc) worldVecs printWorld,
    site "kernel/carried-journal" (carriedJournalWire Sim.env Sim.dc)
      (each 2 fun _ => carriedToWire <$> Vectors.carried) printCarriedWire,
    site "kernel/carried-rows" (carriedRowsWire Sim.env Sim.dc) (carriedRowsVecs true) printCarriedWire,
    site "kernel/carried-rows-headed" (carriedHeadedWire Sim.env Sim.dc) (carriedRowsVecs false) printCarriedWire,
    site "kernel/carried-rows-parented" (carriedParentedWire Sim.env Sim.dc) carriedParentedVecs printCarriedWire,
    site "kernel/carried" (Codec.Kernel.carried Sim.env Sim.dc) (each 2 fun _ => Vectors.carried) printCarried,
    site "path/badComponent" (Field.pathCodec pathMax (by decide)) pathVecs (fun p => text p.val),
    site "host/base/index-count" (Host.Base.codec (Codec.Kernel.world Sim.env Sim.dc))
      (each 2 fun _ => do return ⟨← Vectors.world, ← nat64, ← digest, ← nat64, ← digest⟩) printBase,
    site "host/carried-head" (Host.Carry.head Sim.dc) (each 2 fun _ => do return ⟨← dig, ← nat64, ← dig⟩) text,
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
