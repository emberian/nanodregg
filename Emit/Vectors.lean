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

`gates/codec-vectors.tsv` holds, for every refine site (the census's 26), a few vectors: bytes encoded
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

deriving instance Repr for Op, Cell, Entry, Slot, Leaf, Act, Touch, Turn, Right, AcctRef, Body, Unsigned,
  Call, Host.Entry, Host.Carry.Head

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
def turn : G (Turn Sim.D) := do
  return ⟨← dig, ← nat64, ← nat64, ← list 2 touch, ← list 1 (do return (← dig, ← cell)), ← list 2 dig, ← nat64,
    ← bytes 8⟩
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
  return ⟨← dig, ← dig, ← bytes 4, ← nat64, ← nat64, ← list 2 (do return (← dig, ← dig)), ← nat64, ← body k⟩

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

def world : G (World Sim.D) := do
  let h := (← below 1000) + 3
  return ⟨← trie, journalOf (← journal h), h, ← dig, ← nat64, ← dig⟩

def carried : G (Carried Sim.D) := do
  let h := (← below 1000) + 3
  return ⟨← trie, ← nat64, h, journalOf (← journal h)⟩

/-! ## The one printer -/

/-- `Repr` on one line: no width at which the formatter breaks. -/
def text {α : Type} [Repr α] (v : α) : String := (repr v).pretty 1000000

def printWorld (w : World Sim.D) : String :=
  s!"\{trie := {text w.trie.toList}, journal := {text w.journal.toList}, height := {w.height}, " ++
    s!"chain := {w.chain}, allowance := {w.allowance}, origin := {w.origin}}"

def printWire (x : WorldWire Sim.D) : String := printWorld (ofWire x)

def printCarried (c : Carried Sim.D) : String :=
  s!"\{trie := {text c.trie.toList}, allowance := {c.allowance}, height := {c.height}, " ++
    s!"journal := {text c.journal.toList}}"

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
    site "kernel/journal" (journalWire Sim.env Sim.dc) (each 2 fun _ => toWire <$> Vectors.world) printWire,
    site "kernel/world-budget" (Codec.Kernel.world Sim.env Sim.dc) worldVecs printWorld,
    site "kernel/carried-journal" (carriedJournalWire Sim.env Sim.dc)
      (each 2 fun _ => carriedToWire <$> Vectors.carried) printCarriedWire,
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
