/-
# Kernel.World — the World, its one transition `World.step`, and `fold`

`World.admit` IS the receive path (law 1): the Host commits exactly what it returns. A log is a
list of steps (KERNEL-47): an admitted Turn, or a recorded refusal (`World.refuse`, KERNEL-44: an
authenticated, in-window refusal, charged to its member's window budget, final for its transaction
id). `World.step` is the one transition of a log; the follower and a reopening Host fold the log
with it, and nothing else changes a World.

The kernel is generic over the digest `D` and the hash (`Env`) so that theorems can state a
hash collision as an explicit disjunct, and the simulation can run toy parameters through the
same `admit`. There is one deployed `Env` (CODEC's digest and hash).

Order of the checks (each refuses by name, nothing is written before all pass):
bounds → window (an expired retry is `outsideWindow`, whether or not its entry was pruned:
KERNEL-33) → journal (an exact retry inside its window is `replayed`) → shape → touches
(ONE lookup per touched cell: its pin, the one staleness refusal, then its write or retirement,
and a written value cell's decoding and floor) → value (born value cells, then every
denomination's balance and floor sums: LEDGER-2) → nullifiers → charge → created ids.
-/
import Kernel.Check
import Kernel.Turn
import Kernel.Value
import Kernel.Trie
import Codec.Raw

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
  /-- a born ROM cell whose id is not its content digest (`romIdOf`): a package's identity IS its
  id (KERNEL-3), and the Turn carries ids explicitly (D5), so admit checks it -/
  | notContentId (cell : D)
  /-- a born id is also touched: a born cell did not exist to be observed -/
  | bornTouched (cell : D)
  | missingCell (cell : D)
  | romWrite (cell : D)
  | romRetire (cell : D)
  | appendOnly (cell : D) (key : Nat)
  /-- a value cell the turn leaves behind does not decode (`Value.ofCell`) -/
  | valueMalformed (cell : D)
  /-- a value cell the turn leaves behind is below minus its floor -/
  | belowFloor (cell : D)
  /-- the turn changes a denomination's balance sum -/
  | notConserved (denom : ByteArray)
  /-- the turn changes a denomination's floor sum, and does not bear the denomination -/
  | floorNotConserved (denom : ByteArray)
  /-- the transaction id holds a recorded refusal (KERNEL-44, KERNEL-47 amendment 6): a refused call
  is final within its window, so it is never admitted later (a pin returning A→B→A changes nothing);
  `code` is the recorded refusal's code -/
  | refusedFinal (code : Nat)
  /-- the member's authenticated, in-window refusals this window have reached
  `Bounds.refusalsPerWindow`: the refusal is not recorded (it is NOT a verdict on the call) -/
  | refusalBudget
  /-- an inserted row's key is taken, or a declared head exists (KERNEL-46; binding on the current World) -/
  | keyTaken (parent : D)
  /-- the relation holds `limit` rows -/
  | relationFull (parent : D)
  /-- the relation's `amt` sum would pass its `cap` (LANG-45 (ii)) -/
  | relationCapped (parent : D)
  /-- a row or range names a parent the turn does not pin -/
  | rowParentUnpinned (parent : D)
  /-- a row names a parent that is not live -/
  | orphanRow (parent : D)
  /-- a retired parent still holds rows -/
  | rowsRemain (parent : D)
  /-- a row key's width is not its relation's -/
  | keyWidth (parent : D)
  /-- no head: the relation was never declared -/
  | noRelation (parent : D)
  /-- a retract in a relation declared without retract -/
  | retractForbidden (parent : D)
  /-- a head declared outside the turn that bears its parent -/
  | declareLate (parent : D)
  /-- a range read's rows pass its `most` (refused, never truncated) -/
  | rangeTooLong (parent : D)
  /-- one row slot twice in a turn -/
  | duplicateRow (parent : D)
  /-- an act on the wrong slot kind, or a pin where none belongs or missing where one must be -/
  | rowShape (parent : D)
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
  | .notContentId _ => "notContentId"
  | .bornTouched _ => "bornTouched"
  | .missingCell _ => "missingCell"
  | .romWrite _ => "romWrite"
  | .romRetire _ => "romRetire"
  | .appendOnly _ _ => "appendOnly"
  | .valueMalformed _ => "valueMalformed"
  | .belowFloor _ => "belowFloor"
  | .notConserved _ => "notConserved"
  | .floorNotConserved _ => "floorNotConserved"
  | .refusedFinal _ => "refusedFinal"
  | .refusalBudget => "refusalBudget"
  | .keyTaken _ => "keyTaken"
  | .relationFull _ => "relationFull"
  | .relationCapped _ => "relationCapped"
  | .rowParentUnpinned _ => "rowParentUnpinned"
  | .orphanRow _ => "orphanRow"
  | .rowsRemain _ => "rowsRemain"
  | .keyWidth _ => "keyWidth"
  | .noRelation _ => "noRelation"
  | .retractForbidden _ => "retractForbidden"
  | .declareLate _ => "declareLate"
  | .rangeTooLong _ => "rangeTooLong"
  | .duplicateRow _ => "duplicateRow"
  | .rowShape _ => "rowShape"

variable {D : Type} [Ord D]

/-- A key of the World's one authenticated map (KERNEL-23): a cell id, or a spent nullifier. -/
inductive Slot (D : Type)
  | cell (id : D)
  | nullifier (n : D)
  deriving DecidableEq

/-- What the map holds at a slot: a cell's entry (at a `cell` slot), or `spent` (at a `nullifier`
slot). A decoder refuses any other pairing (`Leaf.fits`); `commit` only ever writes these two. -/
inductive Leaf
  | entry (e : Entry)
  | spent
  deriving DecidableEq

/-- The World's cells and spent nullifiers: one persistent binary Merkle trie (Kernel.Trie). -/
abbrev Cells (D : Type) := Trie.T (Slot D) Leaf D

/-- The World's journal (KERNEL-41): transaction id ↦ (height, turn digest), the SECOND instance of
the one trie type (`journalSpec`), routed by the id's bytes, under its own root. -/
abbrev Journal (D : Type) := Trie.T D (Nat × D) D

/-- A key of the World's refusals (KERNEL-44, KERNEL-47 amendment 4), the THIRD instance of the one
trie type: a refused transaction id, or a member's refusal count for one window (`windowMax`
heights). Routed by a kind byte and the raw bytes (`refusalKeyBytes`), fixed width, no hash. -/
inductive RefusalSlot (D : Type)
  | tx (id : D)
  | count (member : D) (win : UInt64)
  deriving DecidableEq

/-- What the refusals trie holds: at a `tx` key, the height the call was refused AT (the World's
height plus one, the height it would have been admitted at, as a journal entry's), the refusal's
code, and the member it was charged to (KERNEL-50: so a window's count is a function of its
records, `refusalsCounted`, and a receipt names WHO was charged); at a `count` key, how many
refusals the member has had recorded in that window. -/
inductive RefusalLeaf (D : Type)
  | refused (h code : Nat) (member : D)
  | count (n : Nat)
  deriving DecidableEq

abbrev Refusals (D : Type) := Trie.T (RefusalSlot D) (RefusalLeaf D) D

/-- The rows trie (KERNEL-46): heads and rows, under its own root. -/
abbrev Rows (D : Type) := Trie.T (RowSlot D) RowLeaf D

/-- A recorded refusal, as the log carries it (KERNEL-44): the call's transaction id, its signer,
its window, the refusal's code, and the signed call's bytes (the follower's audit decodes them and
re-derives the same refusal). -/
structure Refused (D : Type) where
  txId : D
  member : D
  notBefore : Nat
  validUntil : Nat
  code : Nat
  event : ByteArray
  deriving DecidableEq

/-- One step of a log (KERNEL-47): an admitted Turn, or a recorded refusal. -/
inductive Step (D : Type)
  | turn (t : Turn D)
  | refusal (r : Refused D)
  deriving DecidableEq

/-- The height a step reaches: one more after a Turn, the same after a refusal. -/
def Step.dheight {D : Type} : Step D → Nat
  | .turn _ => 1
  | .refusal _ => 0

/-- The Turns of a log, in order. -/
def Step.turns {D : Type} : List (Step D) → List (Turn D)
  | [] => []
  | .turn t :: l => t :: Step.turns l
  | .refusal _ :: l => Step.turns l

/-- The recorded refusals of a log, in order. -/
def Step.refusals {D : Type} : List (Step D) → List (Refused D)
  | [] => []
  | .turn _ :: l => Step.refusals l
  | .refusal r :: l => r :: Step.refusals l

structure World (D : Type) [Ord D] where
  /-- every cell entry (live or tombstone) and every spent nullifier, under one root -/
  trie : Cells D
  /-- transaction id ↦ (height, turn digest): the replay index, a trie with its own root, which the
  chain commits beside the cells' root (KERNEL-41) -/
  journal : Journal D
  /-- the recorded refusals (KERNEL-44): refused transaction ids and per-member window counts, a
  trie with its own root, committed beside the other two -/
  refusals : Refusals D
  /-- the relations' heads and rows (KERNEL-46/48), a trie with its own root -/
  rows : Rows D := .empty
  height : Nat
  /-- every step the World has taken (KERNEL-47 amendment 1): one per admitted Turn and one per
  recorded refusal. A refusal does not advance `height` (windows are in heights), so two logs of one
  height can differ in length; `steps` is the length the chain binds. A genesis starts it at 0, a
  carry at the carried height, so `height ≤ steps` everywhere. -/
  steps : Nat
  /-- the log chain: `genesisChain origin` at the World's start (a genesis at height 0, or a carry
  at the carried height, KERNEL-29), then one link per admitted turn -/
  chain : D
  /-- the storage budget left, in bytes -/
  allowance : Nat
  /-- the World's identity (KERNEL-24): the digest of everything its genesis was made from, set by
  genesis and never written again; every call names it (`Unsigned.world`) -/
  origin : D

/-- What a carry (KERNEL-29, law 1: state crosses a flag day by re-genesis) moves from one World
into a new one, and what the new World's origin commits to: the trie (every cell and every spent
nullifier: a spent nullifier is state, or a carried value cell could be spent again), the budget
left, the height and the journal. The journal is bounded by the window (KERNEL-33) and carried
whole, so a call committed just before the carry is answered `replayed` after it, never re-run;
the height is carried because journal entries expire by it; the rows (KERNEL-48) are state like
the cells, carried whole. Not carried: the chain, the origin (the new World's own) and the
refusals (they answer only within a window of the old World's log). -/
structure Carried (D : Type) [Ord D] where
  trie : Cells D
  allowance : Nat
  height : Nat
  journal : Journal D
  /-- the relations' heads and rows (KERNEL-48): state, carried whole -/
  rows : Rows D

/-- The kernel's hash domains. -/
def domGenesis : String := "nanodregg/kernel/genesis/v1"
def domAbsent : String := "nanodregg/kernel/pin-absent/v1"
def domCell : String := "nanodregg/kernel/pin-cell/v1"
def domTurn : String := "nanodregg/kernel/turn/v1"
def domChain : String := "nanodregg/kernel/chain/v1"
def domCellId : String := "nanodregg/kernel/cell-id/v1"
def domRomId : String := "nanodregg/kernel/rom-id/v1"
/-- The trie's node hash (`Trie.Spec.hash`: the shape tag byte, then the shape's bytes). -/
def domTrie : String := "nanodregg/kernel/trie/v1"
/-- A trie leaf's value digest: ONE domain, a kind byte first, so two different leaves have one
digest only by a collision in that domain (`Collision`), never across domains. -/
def domLeaf : String := "nanodregg/kernel/trie-leaf/v1"
/-- A journal leaf's value digest (`journalDigest`, KERNEL-41): its own domain, so a journal entry's
digest is never a cell leaf's but by a collision. -/
def domJournal : String := "nanodregg/kernel/journal-leaf/v1"
/-- A refusals leaf's value digest (`refusalDigest`, KERNEL-44): a kind byte first. -/
def domRefusal : String := "nanodregg/kernel/refusal-leaf/v2"
/-- A recorded refusal's digest in the chain (`refusedDigest`). -/
def domRefused : String := "nanodregg/kernel/refused/v1"
/-- The digest of a World's roots, the one value a head link commits of its state (KERNEL-46
amendment 4, KERNEL-47 amendment 3). -/
def domRoots : String := "nanodregg/kernel/roots/v1"

/-- An index as CODEC's four little-endian bytes (indexes are below `Bounds.createsMax`). -/
def index32 (n : Nat) : ByteArray := Nanodregg.Codec.Stream.u32.bytes (UInt32.ofNat n)

/-- What a pin asserts about a cell: its digest, or the digest of absence. -/
def pinOf (E : Env D) : Option Cell → D
  | none => E.hash domAbsent ByteArray.empty
  | some c => E.hash domCell (E.cellBytes c)

def turnDigest (E : Env D) (t : Turn D) : D := E.hash domTurn (E.turnBytes t)

/-- What a recorded refusal commits in the chain: every field, the counters as CODEC's eight
little-endian bytes (injective below 2^64, which `World.refuse` checks), the event last. -/
def refusedBytes (E : Env D) (r : Refused D) : ByteArray :=
  E.bytes r.txId ++ E.bytes r.member ++ Nanodregg.Codec.Stream.nat64.bytes r.notBefore ++
    Nanodregg.Codec.Stream.nat64.bytes r.validUntil ++ Nanodregg.Codec.Stream.nat64.bytes r.code ++ r.event

def refusedDigest (E : Env D) (r : Refused D) : D := E.hash domRefused (refusedBytes E r)

/-- The one digest of a World's roots after a step: the cells', the journal's, the refusals', the
rows' (KERNEL-48). -/
def rootsDigest (E : Env D) (root jroot rroot rowsroot : D) : D :=
  E.hash domRoots (E.bytes root ++ E.bytes jroot ++ E.bytes rroot ++ E.bytes rowsroot)

/-- The head link: a kind byte (0 a Turn, 1 a recorded refusal: one domain, so a turn link equal to
a refusal link is a `Collision`, KERNEL-47 amendment 2), the previous head, the step's digest, and
the roots digest after the step. -/
def headLink (E : Env D) (prev : D) (tag : UInt8) (d rd : D) : D :=
  E.hash domChain (⟨#[tag]⟩ ++ E.bytes prev ++ E.bytes d ++ E.bytes rd)

/-- The next chain head after an admitted Turn commits to the previous one, the Turn, and the ROOTS
AFTER it (KERNEL-23 (d), KERNEL-41, KERNEL-47): `rd` is `rootsDigest` of the cells', journal's and
refusals' roots. A phone that trusts one head checks `(prev, turnDigest, rd)` against it, opens `rd`
to the three roots, then verifies cells, transaction ids or refusals against them. -/
def chainNext (E : Env D) (prev : D) (t : Turn D) (rd : D) : D :=
  headLink E prev 0 (turnDigest E t) rd

/-- The next chain head after a recorded refusal (KERNEL-44): the same link, kind byte 1. -/
def refusalLink (E : Env D) (prev : D) (r : Refused D) (rd : D) : D :=
  headLink E prev 1 (refusedDigest E r) rd

/-! ## The trie's parameters: how a slot routes and what a leaf commits -/

/-- Bit `i` of a byte string, most significant bit of byte 0 first; `false` past its end. -/
def byteBit (b : ByteArray) (i : Nat) : Bool :=
  if h : i / 8 < b.size then (b[i / 8]'h).toNat.testBit (7 - i % 8) else false

def Slot.isNullifier {D : Type} : Slot D → Bool
  | .cell _ => false
  | .nullifier _ => true

def Slot.id {D : Type} : Slot D → D
  | .cell c => c
  | .nullifier n => n

/-- Bit 0 is the slot's kind (cells left, nullifiers right); bit `i + 1` is bit `i` of the id. -/
def slotBit (E : Env D) (s : Slot D) : Nat → Bool
  | 0 => s.isNullifier
  | i + 1 => byteBit (E.bytes s.id) i

/-- A slot's bytes in a leaf: its kind byte, then the id's bytes. -/
def slotBytes (E : Env D) (s : Slot D) : ByteArray :=
  ⟨#[if s.isNullifier then 1 else 0]⟩ ++ E.bytes s.id

/-- The bytes a leaf's value digest is taken over: a kind byte (live 0, tombstone 1, spent 2), then
a live cell's canonical bytes. -/
def leafBytes (E : Env D) : Leaf → ByteArray
  | .entry (.live c) => ⟨#[0]⟩ ++ E.cellBytes c
  | .entry .tomb => ⟨#[1]⟩
  | .spent => ⟨#[2]⟩

/-- What a leaf commits to of its value. -/
def leafDigest (E : Env D) (l : Leaf) : D := E.hash domLeaf (leafBytes E l)

/-- The deployed trie: depth `Bounds.trieDepth` (a kind bit and 256 id bits). -/
def trieSpec (E : Env D) : Trie.Spec (Slot D) Leaf D where
  bit := slotBit E
  depth := Bounds.trieDepth
  depth_lt := by decide
  hash := E.hash domTrie
  dbytes := E.bytes
  kbytes := slotBytes E
  vdigest := leafDigest E

/-- What a journal leaf commits to of an entry: its height as CODEC's eight little-endian bytes,
then the turn digest's bytes (injective on heights below 2^64, which every reached World's are). -/
def journalDigest (E : Env D) (e : Nat × D) : D :=
  E.hash domJournal (Nanodregg.Codec.Stream.nat64.bytes e.1 ++ E.bytes e.2)

/-- The journal trie (KERNEL-41): routed by the transaction id's bytes, most significant bit first,
depth `Bounds.journalDepth` (256 id bits, a 32-byte digest); nodes hashed in the one trie domain;
leaves digested by `journalDigest`. -/
def journalSpec (E : Env D) : Trie.Spec D (Nat × D) D where
  bit k := byteBit (E.bytes k)
  depth := Bounds.journalDepth
  depth_lt := by decide
  hash := E.hash domTrie
  dbytes := E.bytes
  kbytes := E.bytes
  vdigest := journalDigest E

/-- A refusals key's bytes (KERNEL-47 amendment 4): a kind byte, the id's (or member's) bytes, then
eight bytes (zero for `tx`, the window's little-endian for `count`). One width for both kinds, so
the keys are prefix-free with no hash and no World invariant (`refusals_separate`). -/
def refusalKeyBytes (E : Env D) : RefusalSlot D → ByteArray
  | .tx id => ⟨#[0]⟩ ++ E.bytes id ++ Nanodregg.Codec.Stream.nat64.bytes 0
  | .count m win => ⟨#[1]⟩ ++ E.bytes m ++ Nanodregg.Codec.Stream.u64.bytes win

/-- What a refusals leaf commits to: a kind byte (refused 0, count 1), then its counters as eight
little-endian bytes each, then (refused) the charged member's bytes. -/
def refusalLeafBytes (E : Env D) : RefusalLeaf D → ByteArray
  | .refused h code m => ⟨#[0]⟩ ++ Nanodregg.Codec.Stream.nat64.bytes h ++ Nanodregg.Codec.Stream.nat64.bytes code ++
      E.bytes m
  | .count n => ⟨#[1]⟩ ++ Nanodregg.Codec.Stream.nat64.bytes n

def refusalDigest (E : Env D) (l : RefusalLeaf D) : D := E.hash domRefusal (refusalLeafBytes E l)

/-- The refusals trie (KERNEL-44, KERNEL-47): routed by the key's bytes, most significant bit first,
depth `Bounds.refusalDepth` (41 bytes); nodes in the one trie domain; leaves by `refusalDigest`. -/
def refusalSpec (E : Env D) : Trie.Spec (RefusalSlot D) (RefusalLeaf D) D where
  bit k := byteBit (refusalKeyBytes E k)
  depth := Bounds.refusalDepth
  depth_lt := by decide
  hash := E.hash domTrie
  dbytes := E.bytes
  kbytes := refusalKeyBytes E
  vdigest := refusalDigest E

/-- A refusals key holds the leaf of its kind. -/
def RefusalLeaf.fits {D : Type} : RefusalSlot D → RefusalLeaf D → Bool
  | .tx _, .refused _ _ _ => true
  | .count _ _, .count _ => true
  | _, _ => false

/-! ## Rows (KERNEL-46, LANG-44): the fourth instance of the one trie, and its two pin kinds -/


def domRowLeaf : String := "nanodregg/kernel/row-leaf/v1"
def domRowAbsent : String := "nanodregg/kernel/row-pin-absent/v1"
def domRange : String := "nanodregg/kernel/range-pin/v1"

/-- One byte of a small number (callers bound it below 256: `rel`, a key's length). -/
def byte8 (n : Nat) : ByteArray := ⟨#[UInt8.ofNat n]⟩

/-- The bytes of a relation's rows, before the key's own bytes: the parent, the relation, the row
tag (1) and the key width. A range read's prefix is this followed by the key prefix. -/
def rowsPrefix (E : Env D) (parent : D) (rel width : Nat) : ByteArray :=
  E.bytes parent ++ byte8 rel ++ byte8 1 ++ byte8 width

/-- A rows key's bytes (KERNEL-46 amendment 1): a head is `parent ‖ rel ‖ 0`; a row is
`parent ‖ rel ‖ 1 ‖ |k| ‖ k`. The length byte makes the encoding prefix-free by itself, so
`rows_separate` needs no World invariant. -/
def rowKeyBytes (E : Env D) : RowSlot D → ByteArray
  | .head p rel => E.bytes p ++ byte8 rel ++ byte8 0
  | .row key => rowsPrefix E key.parent key.rel key.k.size ++ key.k

/-- What a rows leaf commits to: a kind byte (head 0, row 1), its counters as eight little-endian
bytes each, the retract flag as one byte, a row's value last. -/
def rowLeafBytes : RowLeaf → ByteArray
  | .head count sum limit cap width retract =>
      byte8 0 ++ Nanodregg.Codec.Stream.nat64.bytes count ++ Nanodregg.Codec.Stream.nat64.bytes sum ++
        Nanodregg.Codec.Stream.nat64.bytes limit ++ Nanodregg.Codec.Stream.nat64.bytes cap ++
        Nanodregg.Codec.Stream.nat64.bytes width ++ byte8 (if retract then 1 else 0)
  | .row amt val => byte8 1 ++ Nanodregg.Codec.Stream.nat64.bytes amt ++
      (Nanodregg.Codec.Stream.rawBytes Bounds.valueBytesMax).bytes val

def rowDigest (E : Env D) (l : RowLeaf) : D := E.hash domRowLeaf (rowLeafBytes l)

/-- The rows trie: routed by the key's bytes, most significant bit first, depth `Bounds.rowDepth`;
nodes in the one trie domain; leaves by `rowDigest`. -/
def rowSpec (E : Env D) : Trie.Spec (RowSlot D) RowLeaf D where
  bit k := byteBit (rowKeyBytes E k)
  depth := Bounds.rowDepth
  depth_lt := by decide
  hash := E.hash domTrie
  dbytes := E.bytes
  kbytes := rowKeyBytes E
  vdigest := rowDigest E

/-- A rows key holds the leaf of its kind. -/
def RowLeaf.fits {D : Type} : RowSlot D → RowLeaf → Bool
  | .head _ _, .head .. => true
  | .row _, .row .. => true
  | _, _ => false

/-- The leaf at a rows slot. -/
def rowAt [DecidableEq D] (E : Env D) (r : Rows D) (s : RowSlot D) : Option RowLeaf := r.get (rowSpec E) s

/-- What a row pin asserts (the first pin kind): the leaf's digest, or the digest of absence. -/
def rowPin (E : Env D) : Option RowLeaf → D
  | none => E.hash domRowAbsent ByteArray.empty
  | some l => rowDigest E l

/-- Whether `b` starts with the bytes `pre`. -/
def startsWith (pre b : ByteArray) : Bool := decide (b.extract 0 pre.size = pre)

/-- At most `n` entries of a subtree, in trie order (`T.toList` cut at `n`): it stops walking once
it holds `n`, so a bounded read pays for what it returns plus one path. -/
def takeList {K V : Type} (n : Nat) : Trie.T K V D → List (K × V)
  | .empty => []
  | .leaf _ kvs => kvs.take n
  | .node _ _ _ l r =>
      if n = 0 then [] else
        let a := takeList n l
        a ++ takeList (n - a.length) r

/-- At most `n` entries of a trie under a byte prefix, in trie order (left, the 0 bit, first):
descend by the prefix's bits at each node's branching bit; at the first node branching past them,
the subtree's first `n` (`takeList`) if its keys start with the prefix (one representative key read:
the path skipped bits) and none otherwise; at a leaf, the first `n` of those whose key bytes start
with the prefix. Work: one path plus the entries returned, and no hash. -/
def under {K V : Type} (S : Trie.Spec K V D) (pre : ByteArray) (n : Nat) : Trie.T K V D → List (K × V)
  | .empty => []
  | .leaf _ kvs => (kvs.filter fun p => startsWith pre (S.kbytes p.1)).take n
  | .node h b rep l r =>
      if b < 8 * pre.size then
        (if byteBit pre b then under S pre n r else under S pre n l)
      else
        -- every key of the subtree agrees with its `rep` on every bit below `b`, so on the whole
        -- prefix: the bits the path skipped are checked here, once, by one key's bytes
        if startsWith pre (S.kbytes rep) then takeList n (.node h b rep l r) else []

/-- A range read's rows (LANG-44 (c)): those of `rel` under `parent` whose key starts with `pre`,
in key order, given the relation's key `width`; `none` past `most` (`rangeTooLong`: refused, never
truncated). At most `most + 1` rows are read (KERNEL-48: the WASTE row rows-read-per-range-read). -/
def rangeRows (E : Env D) (r : Rows D) (parent : D) (rel width : Nat) (pre : ByteArray) (most : Nat) :
    Option (List (RowSlot D × RowLeaf)) :=
  let l := under (rowSpec E) (rowsPrefix E parent rel width ++ pre) (most + 1) r
  if l.length ≤ most then some l else none

/-- What a range pin asserts (the second pin kind): the relation, the width and the prefix, then
the listing's length and each row's key bytes and leaf digest, in key order. A row moving, landing
or leaving under the prefix changes it. -/
def rangePinBytes (E : Env D) (parent : D) (rel width : Nat) (pre : ByteArray)
    (l : List (RowSlot D × RowLeaf)) : ByteArray :=
  rowsPrefix E parent rel width ++ byte8 pre.size ++ pre ++
    Nanodregg.Codec.Stream.nat32.bytes l.length ++
    (l.foldl (fun acc p => acc ++ rowKeyBytes E p.1 ++ E.bytes (rowDigest E p.2)) ByteArray.empty)

def rangePin (E : Env D) (parent : D) (rel width : Nat) (pre : ByteArray)
    (l : List (RowSlot D × RowLeaf)) : D :=
  E.hash domRange (rangePinBytes E parent rel width pre l)

/-- The window a height counts refusals in. -/
def refusalWindow (H : Nat) : UInt64 := UInt64.ofNat (H / Bounds.windowMax)

/-- A slot holds the leaf of its kind. -/
def Leaf.fits {D : Type} : Slot D → Leaf → Bool
  | .cell _, .entry _ => true
  | .nullifier _, .spent => true
  | _, _ => false

/-- The id of the `i`-th cell a transaction creates. -/
def cellIdOf (E : Env D) (txId : D) (i : Nat) : D :=
  E.hash domCellId (E.bytes txId ++ index32 i)

/-- A ROM cell's id is its content digest: the same immutable content is one cell, whoever
installs it (a package's identity IS its cell id). -/
def romIdOf (E : Env D) (c : Cell) : D := E.hash domRomId (E.cellBytes c)

/-- The id a receiver gives the `i`-th cell its transaction bears fresh: content-addressed for
ROM, else derived from the transaction. (An account's id is keyed instead: D5b.) -/
def bornId (E : Env D) (txId : D) (p : Cell × Nat) : D :=
  match p.1.discipline with
  | .rom => romIdOf E p.1
  | _ => cellIdOf E txId p.2

/-- The ids a turn's births carry (explicit in the Turn, D5). -/
def createdIds (t : Turn D) : List D := t.creates.map Prod.fst

namespace World

/-- The chain a World with identity `origin` starts at (KERNEL-24): `H(domGenesis, origin)`. -/
def genesisChain (E : Env D) (origin : D) : D := E.hash domGenesis (E.bytes origin)

/-- An empty World with identity `origin`, its chain at `genesisChain`. -/
def genesis (E : Env D) (origin : D) (allowance : Nat) : World D :=
  { trie := .empty, journal := .empty, refusals := .empty, height := 0, steps := 0,
    chain := genesisChain E origin, allowance, origin }

/-- The root of the World's map: its trie's cached digest, O(1). -/
def root (E : Env D) (w : World D) : D := w.trie.hashOf (trieSpec E)

/-- The root of the World's journal, O(1). -/
def journalRoot (E : Env D) (w : World D) : D := w.journal.hashOf (journalSpec E)

/-- The root of the World's refusals, O(1). -/
def refusalsRoot (E : Env D) (w : World D) : D := w.refusals.hashOf (refusalSpec E)

/-- The root of the World's rows, O(1). -/
def rowsRoot (E : Env D) (w : World D) : D := w.rows.hashOf (rowSpec E)

/-- The one digest of the roots a head link commits (`chainNext`, `refusalLink`): the cells', the
journal's, the refusals' (KERNEL-47 amendment 3) and the rows' (KERNEL-48). -/
def roots (E : Env D) (w : World D) : D :=
  rootsDigest E (w.root E) (w.journalRoot E) (w.refusalsRoot E) (w.rowsRoot E)

/-- What a carry takes from this World (KERNEL-29). -/
def carried (w : World D) : Carried D := ⟨w.trie, w.allowance, w.height, w.journal, w.rows⟩

section
variable [DecidableEq D]

/-- The entry at a cell id, if any. -/
def entry (E : Env D) (w : World D) (c : D) : Option Entry :=
  match w.trie.get (trieSpec E) (.cell c) with
  | some (.entry e) => some e
  | _ => none

/-- The live cell at an id, if any (a tombstone reads as absent). -/
def live (E : Env D) (w : World D) (c : D) : Option Cell :=
  match w.entry E c with
  | some (.live cell) => some cell
  | _ => none

/-- Is the id taken (a live cell or a tombstone)? -/
def taken (E : Env D) (w : World D) (c : D) : Bool := (w.entry E c).isSome

/-- The journal entry at a transaction id, if any: its height and turn digest. -/
def journalAt (E : Env D) (w : World D) (k : D) : Option (Nat × D) := w.journal.get (journalSpec E) k

/-- The refusals leaf at a key, if any. -/
def refusalAt (E : Env D) (w : World D) (k : RefusalSlot D) : Option (RefusalLeaf D) :=
  w.refusals.get (refusalSpec E) k

/-- Has the nullifier been spent? -/
def isSpent (E : Env D) (w : World D) (n : D) : Bool :=
  (w.trie.get (trieSpec E) (.nullifier n)).isSome

/-- Every cell id the map holds (live or tombstone), in trie order: what `cells.keys` was before
KERNEL-23. Spent nullifiers are not cell ids and are left out. -/
def cellIds (w : World D) : List D :=
  w.trie.toList.filterMap fun p => match p.1 with
    | .cell c => some c
    | .nullifier _ => none

end

/-- What an entry costs in the World: a live cell its weight, a tombstone nothing beyond its id. -/
def _root_.Nanodregg.Kernel.Entry.weight : Entry → Nat
  | .live c => c.weight
  | .tomb => 0

/-- What a leaf costs: its slot's id, and a cell entry's weight. -/
def _root_.Nanodregg.Kernel.Leaf.weight : Leaf → Nat
  | .entry e => digestWeight + e.weight
  | .spent => digestWeight

/-- The weight of the map: each leaf with its id. -/
def _root_.Nanodregg.Kernel.cellsWeight (m : Cells D) : Nat :=
  (m.toList.map fun p => p.2.weight).sum

/-- What a rows entry costs in the World (KERNEL-46 amendment 5): its key as in the log, and its
leaf (`RowLeaf.weight`). -/
def _root_.Nanodregg.Kernel.rowEntryWeight (p : RowSlot D × RowLeaf) : Nat := p.1.weight + p.2.weight

/-- The weight of the rows: each entry with its key. -/
def _root_.Nanodregg.Kernel.rowsWeight (r : Rows D) : Nat := (r.toList.map rowEntryWeight).sum

/-- The storage a World holds, by the same per-field costs as `Turn.weight`: each cell entry with
its id, each spent nullifier, and each rows entry with its key (KERNEL-48). The journal is not in it: it is pruned to the window
(`pruneJournal`, KERNEL-33), so it is a bounded overhead (`journal_bounded`: fewer than
`3 * Bounds.windowMax` entries), not storage a turn buys. A specification measure (O(store)),
never computed on the request path; `Kernel.Proofs.Weight` bounds it by the budget spent. -/
def weight (w : World D) : Nat :=
  cellsWeight w.trie + rowsWeight w.rows

end World

/-- The cell an entry holds (a tombstone holds none). -/
def Entry.cell? : Entry → Option Cell
  | .live c => some c
  | .tomb => none

/-- What a leaf contributes to a sum over cell entries (a spent nullifier: nothing). -/
def Leaf.sumOf (f : Entry → Int) : Leaf → Int
  | .entry e => f e
  | .spent => 0

/-- A sum over the map's cell entries, of what each contributes. -/
def cellsSum (f : Entry → Int) (m : Cells D) : Int :=
  (m.toList.map fun p => p.2.sumOf f).sum

/-- What an entry contributes to denomination `d`'s sum of `g`: its value cell's, if any. -/
def entrySum (g : Flow → Int) (d : ByteArray) (e : Entry) : Int := sumBy g d (flowsOf none e.cell?)

namespace World

/-- Specification measures (O(store), never computed on the request path): the sum over every
live value cell of denomination `d` of its balance, of its floor, and of its positive balance
(what is outstanding). `Kernel.Proofs.Value` proves what `World.admit` does to them. -/
def sumOf (g : Flow → Int) (w : World D) (d : ByteArray) : Int := cellsSum (entrySum g d) w.trie
def valueSum (w : World D) (d : ByteArray) : Int := w.sumOf Flow.balance d
def floorSum (w : World D) (d : ByteArray) : Int := w.sumOf Flow.floor d
def outstanding (w : World D) (d : ByteArray) : Int := w.sumOf (fun f => max f.balance 0) d

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
  req (t.creates.all fun c => c.2.slots.length ≤ Bounds.slotsPerCellMax) (.overBound .slotsPerCell)
  req ((t.creates.all fun c => c.2.slots.all fun p => p.1 < Bounds.slotKeyLimit) &&
       (t.touches.all fun x => x.ops.all fun o => o.key < Bounds.slotKeyLimit)) (.overBound .slotKey)
  req ((t.creates.all fun c => c.2.slots.all fun p => p.2.size ≤ Bounds.valueBytesMax) &&
       (t.touches.all fun x => x.ops.all fun o => opValueSize o ≤ Bounds.valueBytesMax))
    (.overBound .valueBytes)
  req (t.validUntil ≤ t.notBefore + Bounds.windowMax) (.overBound .window)
  req (t.weight ≤ Bounds.weightMax) (.overBound .weight)
  req (t.validUntil < Bounds.counterLimit && t.notBefore < Bounds.counterLimit &&
       t.charge < Bounds.counterLimit && t.creates.all fun c => c.2.kind < Bounds.kindLimit)
    (.overBound .counter)
  -- the rows' and ranges' syntactic wire bounds (KERNEL-48, CODEC-9: `checkBounds_fits` reaches them)
  req (decide (t.rows.length ≤ Bounds.rowsMax) && decide (t.ranges.length ≤ Bounds.rangesMax) &&
       (t.rows.all fun x => (match x.slot with
          | .head _ rel => decide (rel < 256)
          | .row key => decide (key.rel < 256) && decide (key.k.size ≤ Bounds.keyBytesMax)) &&
        (match x.act with
          | .insert amt v | .upsert amt v => decide (amt < Bounds.counterLimit) && decide (v.size ≤ Bounds.valueBytesMax)
          | .declare limit cap width _ => decide (limit < Bounds.counterLimit) && decide (cap < Bounds.counterLimit) &&
              decide (width < Bounds.counterLimit)
          | _ => true)) &&
       (t.ranges.all fun q => decide (q.rel < 256) && decide (q.pre.size ≤ Bounds.keyBytesMax) &&
          decide (q.most < Bounds.counterLimit))) (.overBound .rows)

variable [DecidableEq D]

/-- A transaction id is admitted at most once; a retry names the height it landed at. -/
def checkJournal (E : Env D) (w : World D) (t : Turn D) : Except (Reject D) Unit :=
  match w.journalAt E t.txId with
  | some (h, _) => .error (.replayed h)
  | none =>
      match w.refusalAt E (.tx t.txId) with
      | some (.refused _ code _) => .error (.refusedFinal code)
      | _ => .ok ()

def noDup {α : Type} [Ord α] (l : List α) (e : α → Reject D) : Except (Reject D) Unit :=
  match firstDup l with
  | none => .ok ()
  | some a => .error (e a)

/-- One touch per cell, one op per key of a write, born cells in canonical form. -/
def checkShape (t : Turn D) : Except (Reject D) Unit := do
  noDup (t.touches.map Touch.cell) .duplicateTouch
  noDup t.nullifiers .duplicateNullifier
  forEx (fun x => noDup (opKeys x.ops) (.duplicateKey x.cell)) t.touches
  forEx (fun (c, i) => req (Slots.ascending c.2.slots) (.nonCanonicalCell i)) t.creates.zipIdx

def checkWindow (w : World D) (t : Turn D) : Except (Reject D) Unit :=
  req (t.notBefore ≤ w.height + 1 && w.height + 1 ≤ t.validUntil) .outsideWindow

/-- The step counter stays below `2^64` (KERNEL-47; every step, a Turn or a refusal, checks it), so
every reached World's `steps` fits CODEC's `u64`. -/
def checkSteps (w : World D) : Except (Reject D) Unit :=
  req (w.steps + 1 < Bounds.counterLimit) (.overBound .counter)

/-- A value cell a turn leaves behind decodes and is within its floor; any other cell passes. -/
def checkValueCell (c : D) (cell : Cell) : Except (Reject D) Unit :=
  if cell.discipline = .value then
    match Value.ofCell cell with
    | none => .error (.valueMalformed c)
    | some v => req v.withinFloor (.belowFloor c)
  else .ok ()

/-- The cell a write leaves behind, or why it may not be written: a ROM cell never, an
append-only cell only at new keys, a value cell only into a cell that decodes and is within its
floor (LEDGER-2). -/
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
  | .value => do
      req (post.slots.length ≤ Bounds.slotsPerCellMax) (.overBound .slotsPerCell)
      checkValueCell c post
      pure post

/-- What a touch leaves at its cell, the World storage it charged for but does not hold (a
retired cell's whole weight, a write's ops minus what the cell actually grew: KERNEL-15), and
what it moves of its denomination's value (`flowsOf` the cell before and after: LEDGER-2). -/
structure Post (D : Type) where
  cell : D
  entry : Entry
  freed : Nat
  flows : List Flow

def Post.pair {D : Type} (p : Post D) : D × Entry := (p.cell, p.entry)

/-- What a touch leaves at its cell (`none`: unchanged), or why not. The cell is looked up ONCE:
the pin is checked against it (the one staleness refusal), then the act applies to it, and what it
frees and the value it moves are computed from the same lookup. -/
def touchCheck (E : Env D) (w : World D) (x : Touch D) : Except (Reject D) (Option (Post D)) := do
  let cur := w.live E x.cell
  req (pinOf E cur = x.seen) (.stale x.cell)
  match x.act, cur with
  | .keep, _ => pure none
  | .write _, none => .error (.missingCell x.cell)
  | .write ops, some cell => do
      let post ← postWrite x.cell cell ops
      pure (some ⟨x.cell, .live post, cell.weight + (ops.map Op.weight).sum - post.weight,
        flowsOf (some cell) (some post)⟩)
  | .retire, none => .error (.missingCell x.cell)
  | .retire, some cell => do
      req (cell.discipline != .rom) (.romRetire x.cell)
      pure (some ⟨x.cell, .tomb, cell.weight, flowsOf (some cell) none⟩)

def checkNullifiers (E : Env D) (w : World D) (t : Turn D) : Except (Reject D) Unit :=
  forEx (fun n => req (!w.isSpent E n) (.spent n)) t.nullifiers

/-- The storage a turn's touches give back to the budget. -/
def credit (posts : List (Post D)) : Nat := (posts.map Post.freed).sum

/-- The turn pays exactly its weight, and can afford it with what its touches give back (so a
drained World can still retire a cell heavier than the retirement). -/
def checkCharge (w : World D) (t : Turn D) (back : Nat) : Except (Reject D) Unit := do
  req (t.charge = t.weight) (.chargeMismatch t.weight)
  req (t.charge ≤ w.allowance + back) .overAllowance

/-- Born ids are fresh: not in the World (live or tombstoned), not twice in the turn, and not
touched by it; and a born ROM cell sits at its content digest. -/
def checkCreates (E : Env D) (w : World D) (t : Turn D) : Except (Reject D) Unit := do
  forEx (fun p => req (p.2.discipline != .rom || decide (p.1 = romIdOf E p.2)) (.notContentId p.1))
    t.creates
  noDup (createdIds t) .idTaken
  noDup (t.touches.map Touch.cell ++ createdIds t) .bornTouched
  forEx (fun c => req (!w.taken E c) (.idTaken c)) (createdIds t)

/-- Every flow a turn moves: its touches', then its born cells'. -/
def valueFlows (t : Turn D) (posts : List (Post D)) : List Flow :=
  posts.flatMap Post.flows ++ t.creates.flatMap fun p => flowsOf none (some p.2)

/-- Value is conserved (LEDGER-2): every value cell the turn bears decodes and is within its
floor, and over the touches' and births' flows, at most `Bounds.denomsMax` denominations move,
each one's balance sum is unchanged, and so is its floor sum unless the turn bears it (the
denomination is the bytes of an id born here: its birth is the only turn that sets its floor). -/
def checkValue (E : Env D) (t : Turn D) (posts : List (Post D)) : Except (Reject D) Unit := do
  forEx (fun p => checkValueCell p.1 p.2) t.creates
  match accumulate (valueFlows t posts) with
  | none => .error (.overBound .denoms)
  | some acc =>
      let bornDenoms := (createdIds t).map E.bytes
      forEx (fun a => do
        req (decide (a.balance = 0)) (.notConserved a.denom)
        req (decide (a.floor = 0) || bornDenoms.any fun b => decide (b = a.denom))
          (.floorNotConserved a.denom)) acc

/-! ## The rows a decoded base may hold (KERNEL-48; CODEC-9 refines on `rowsFits` and `rowsHeaded`) -/

/-- Byte strings strictly ascending, lexicographically (the trie's order for prefix-free keys). -/
def ascendingBytes : List ByteArray → Bool
  | a :: b :: rest => decide (a.toList < b.toList) && ascendingBytes (b :: rest)
  | _ => true

/-- A rows key holds a leaf of its kind, within every bound admission keeps. -/
def rowFits : RowSlot D → RowLeaf → Bool
  | .head _ rel, .head count sum limit cap width _ =>
      decide (rel < 256) && decide (limit ≤ Bounds.rowsPerRelationMax) && decide (width ≤ Bounds.keyBytesMax) &&
        decide (count ≤ limit) && decide (sum ≤ cap) && decide (cap < Bounds.counterLimit)
  | .row key, .row amt val =>
      decide (key.rel < 256) && decide (key.k.size ≤ Bounds.keyBytesMax) && decide (amt < Bounds.counterLimit) &&
        decide (val.size ≤ Bounds.valueBytesMax)
  | _, _ => false

/-- A rows listing: strictly ascending by key bytes, every pair fitting. -/
def rowsFits (E : Env D) (l : List (RowSlot D × RowLeaf)) : Bool :=
  ascendingBytes (l.map fun p => rowKeyBytes E p.1) && l.all fun p => rowFits p.1 p.2

/-- Every row has its head, its key at the head's width, and every head's count and sum are its
rows' (the decode-side twin of `head_sum`). O(listing · heads) over a listing bounded by the limits. -/
def rowsHeaded (l : List (RowSlot D × RowLeaf)) [DecidableEq D] : Bool :=
  let heads := l.filterMap fun p => match p with
    | (.head parent rel, .head count sum _ _ width _) => some (parent, rel, count, sum, width)
    | _ => none
  let rowsOf (parent : D) (rel : Nat) := l.filterMap fun p => match p with
    | (.row key, .row amt _) => if decide (key.parent = parent) && decide (key.rel = rel) then some (key, amt) else none
    | _ => none
  (l.all fun p => match p with
    | (.row key, _) => heads.any fun h => decide (h.1 = key.parent) && decide (h.2.1 = key.rel) && decide (h.2.2.2.2 = key.k.size)
    | _ => true) &&
  heads.all fun h => let rs := rowsOf h.1 h.2.1
    decide (rs.length = h.2.2.1) && decide ((rs.map (·.2)).sum = h.2.2.2.1)

/-- Every head's parent is a live cell (CODEC-9's `kernel/rows-parented`): heads are declared only
by the turn that births their parent (`declareLate`), and leave with it (`dropHeads`); every row has
its head (`rowsHeaded`), so heads suffice.
Over the parts, so a carried file is judged as a World is (`rowsParented E w.trie w.rows`). -/
def rowsParented [DecidableEq D] (E : Env D) (trie : Cells D) (rows : Rows D) : Bool :=
  rows.toList.all fun p => match p.1 with
    | .head parent _ => (match trie.get (trieSpec E) (.cell parent) with
        | some (.entry (.live _)) => true
        | _ => false)
    | .row _ => true

/-! ## Rows admission (KERNEL-46/48): judged on the CURRENT rows, one slot at a time -/

/-- The bits of a rows key, as the path `retainAt` follows to remove it (a retract REMOVES: no
tombstone, KERNEL-46). -/
def rowPath (E : Env D) (s : RowSlot D) : List Bool :=
  (List.range Bounds.rowDepth).map ((rowSpec E).bit s)

/-- The head of a relation, as `(count, sum, limit, cap, width, retract)`. -/
def headOf (E : Env D) (r : Rows D) (parent : D) (rel : Nat) :
    Option (Nat × Nat × Nat × Nat × Nat × Bool) :=
  match rowAt E r (.head parent rel) with
  | some (.head count sum limit cap width retract) => some (count, sum, limit, cap, width, retract)
  | _ => none

/-- THE range read (LANG-44 (c)): relation `rel` under `parent`, its key width from its head, and
`rangeRows` at that width (`none` inside: past `most`, refused, never truncated); `none` when the
relation has no head. A method's range read (`Receive.rowView`) and a member's `read OBJ REL K`
(PROTOCOL-51) are both this one function. -/
def rangeOf (E : Env D) (r : Rows D) (parent : D) (rel : Nat) (pre : ByteArray) (most : Nat) :
    Option (Nat × Option (List (RowSlot D × RowLeaf))) :=
  match headOf E r parent rel with
  | none => none
  | some (_, _, _, _, width, _) => some (width, rangeRows E r parent rel width pre most)

/-- Whether a row touch inserts into relation `rel` of `p` (1) or not (0). -/
def insN1 (p : D) (rel : Nat) (x : RowTouch D) : Nat :=
  match x.slot, x.act with
  | .row k, .insert _ _ => if k.parent = p ∧ k.rel = rel then 1 else 0
  | _, _ => 0

/-- What a row touch adds to relation `rel` of `p`'s `amt` sum by inserting. -/
def insA1 (p : D) (rel : Nat) (x : RowTouch D) : Nat :=
  match x.slot, x.act with
  | .row k, .insert amt _ => if k.parent = p ∧ k.rel = rel then amt else 0
  | _, _ => 0

/-- How many rows a list of row touches inserts into relation `rel` of `p` (KERNEL-46 amendment 3:
the head's count moves by exactly this, `Kernel.Proofs.RowsComm.admit_comm`). -/
def insN (p : D) (rel : Nat) : List (RowTouch D) → Nat
  | [] => 0
  | x :: rest => insN1 p rel x + insN p rel rest

/-- The `amt` a list of row touches inserts into relation `rel` of `p` (the head's sum moves by it). -/
def insA (p : D) (rel : Nat) : List (RowTouch D) → Nat
  | [] => 0
  | x :: rest => insA1 p rel x + insA p rel rest

/-- Write a relation's head with a new count and sum, its declaration unchanged. -/
def setHead (E : Env D) (r : Rows D) (parent : D) (rel count sum limit cap width : Nat) (retract : Bool) : Rows D :=
  r.insert (rowSpec E) (.head parent rel) (.head count sum limit cap width retract)

/-- One row touch, judged on the rows written so far this turn (slots are distinct, so a row's pin
is judged against the pre-state; a head's count and sum accumulate: the head update is additive,
never pinned, KERNEL-46 amendment 3). The parent must be pinned by the turn (`rowParentUnpinned`)
and live (`orphanRow`), or, for `declare`, born by it (`declareLate`). -/
def rowStep (E : Env D) (w : World D) (t : Turn D) (r : Rows D)
    (x : RowTouch D) : Except (Reject D) (Rows D) := do
  match x.slot, x.act with
  | .head p rel, .declare limit cap width retract => do
      req (decide (rel < 256)) (.overBound .rows)
      -- a declare reads nothing, so it carries no pin (one encoding per effect)
      req x.seen.isNone (.rowShape p)
      req ((createdIds t).contains p) (.declareLate p)
      req (decide (limit ≤ Bounds.rowsPerRelationMax) && decide (width ≤ Bounds.keyBytesMax) &&
        decide (cap < Bounds.counterLimit)) (.overBound .rows)
      req (rowAt E r (.head p rel)).isNone (.keyTaken p)
      pure (setHead E r p rel 0 0 limit cap width retract)
  | .head p _, _ => .error (.rowShape p)
  | .row key, act => do
      let p := key.parent
      req (t.touches.any fun x => decide (x.cell = p)) (.rowParentUnpinned p)
      req (w.live E p).isSome (.orphanRow p)
      -- a parent the turn retires takes no row: its heads go with it (`dropHeads`)
      req (!(t.touches.any fun x => decide (x.cell = p) && decide (x.act = .retire))) (.orphanRow p)
      match headOf E r p key.rel with
      | none => .error (.noRelation p)
      | some (count, sum, limit, cap, width, retract) => do
          req (decide (key.k.size = width)) (.keyWidth p)
          let cur := rowAt E r (.row key)
          let pinned : Except (Reject D) Unit :=
            match x.seen with
            | some s => req (decide (rowPin E cur = s)) (.stale p)
            | none => .error (.rowShape p)
          match act with
          | .keep => do pinned; pure r
          | .insert amt v => do
              req x.seen.isNone (.rowShape p)
              req cur.isNone (.keyTaken p)
              req (decide (count < limit)) (.relationFull p)
              req (decide (sum + amt ≤ cap)) (.relationCapped p)
              req (decide (v.size ≤ Bounds.valueBytesMax)) (.overBound .valueBytes)
              pure (setHead E (r.insert (rowSpec E) (.row key) (.row amt v)) p key.rel (count + 1)
                (sum + amt) limit cap width retract)
          | .upsert amt v => do
              pinned
              req (decide (v.size ≤ Bounds.valueBytesMax)) (.overBound .valueBytes)
              let old := match cur with | some (.row a _) => a | _ => 0
              let fresh := cur.isNone
              req (!fresh || decide (count < limit)) (.relationFull p)
              req (decide (sum - old + amt ≤ cap)) (.relationCapped p)
              pure (setHead E (r.insert (rowSpec E) (.row key) (.row amt v)) p key.rel
                (if fresh then count + 1 else count) (sum - old + amt) limit cap width retract)
          | .retract => do
              pinned
              req retract (.retractForbidden p)
              match cur with
              | some (.row a _) =>
                  pure (setHead E (Trie.retainAt (rowSpec E) (fun k _ => decide (k ≠ .row key))
                    (rowPath E (.row key)) r) p key.rel (count - 1) (sum - a) limit cap width retract)
              | _ => .error (.stale p)
          | .declare .. => .error (.rowShape p)

/-- What a row touch gives back of its growth, judged on the rows before it: an upsert or a
retract the entry it replaces or removes (with its key); nothing otherwise. -/
def rowFreed (E : Env D) (r : Rows D) (x : RowTouch D) : Nat :=
  match x.act with
  | .upsert .. | .retract => ((rowAt E r x.slot).map fun l => rowEntryWeight (x.slot, l)).getD 0
  | _ => 0

/-- One row touch with what it gives back, accumulated. -/
def rowStepFreed (E : Env D) (w : World D) (t : Turn D) (acc : Rows D × Nat)
    (x : RowTouch D) : Except (Reject D) (Rows D × Nat) := do
  let r ← rowStep E w t acc.1 x
  pure (r, acc.2 + rowFreed E acc.1 x)

/-- A retired parent's heads leave with it, and give their weight back. `checkRowsRemain` refused a
retirement whose parent still holds a row, and `rowStep` refuses a row under a parent the turn
retires (`orphanRow`), so what is under a retired parent is its heads (at most 256, `rel < 256`).
Work: one path per head removed. -/
def dropHeads (E : Env D) (t : Turn D) (acc : Rows D × Nat) : Rows D × Nat :=
  t.touches.foldl (fun acc x => match x.act with
    | .retire =>
        ((under (rowSpec E) (E.bytes x.cell) 257 acc.1).filter fun p => match p.1 with
          | .head q _ => decide (q = x.cell)
          | .row _ => false).foldl (fun acc p =>
            (Trie.retainAt (rowSpec E) (fun k _ => decide (k ≠ p.1)) (rowPath E p.1) acc.1,
              acc.2 + rowEntryWeight p)) acc
    | _ => acc) acc

/-- Every row touch, in order, from the World's rows; slots distinct (`duplicateRow`). Returns the
rows after the turn and the storage its row touches give back (`rowFreed`, summed). -/
def rowsRun (E : Env D) (w : World D) (t : Turn D) :
    Except (Reject D) (Rows D × Nat) := do
  req (decide (t.rows.length ≤ Bounds.rowsMax) && decide (t.ranges.length ≤ Bounds.rangesMax)) (.overBound .rows)
  req (t.rows.all fun x => match x.slot with
    | .row key => decide (key.rel < 256) && decide (key.k.size ≤ Bounds.keyBytesMax)
    | .head _ rel => decide (rel < 256)) (.overBound .rows)
  match t.rows.find? (fun x => decide (1 < (t.rows.filter fun y => decide (y.slot = x.slot)).length)) with
  | some x => .error (.duplicateRow (match x.slot with | .head p _ => p | .row k => k.parent))
  | none => do
      let acc ← t.rows.foldlM (rowStepFreed E w t) (w.rows, 0)
      pure (dropHeads E t acc)

/-- The rows after a checked turn and what its row touches give back. `check` ran `rowsRun` to
`.ok`, so the fallback is unreachable after it. -/
def rowsAfter (E : Env D) (w : World D) (t : Turn D) : Rows D × Nat :=
  match rowsRun E w t with
  | .ok r => r
  | .error _ => (w.rows, 0)

/-- Every range read (the second pin kind): its relation exists, its rows fit `most`
(`rangeTooLong`, never truncated), and their listing's pin is the signer's (`stale parent`).
Judged on the PRE-state rows, as every pin is. -/
def checkRanges (E : Env D) (w : World D) (t : Turn D) : Except (Reject D) Unit :=
  forEx (fun q => do
    req (t.touches.any fun x => decide (x.cell = q.parent)) (.rowParentUnpinned q.parent)
    match headOf E w.rows q.parent q.rel with
    | none => .error (.noRelation q.parent)
    | some (_, _, _, _, width, _) => do
        -- a prefix longer than the relation's keys selects no key of it, and its bits would route
        -- shorter keys into the subtree `under` lists whole
        req (decide (q.pre.size ≤ width)) (.keyWidth q.parent)
        match rangeRows E w.rows q.parent q.rel width q.pre q.most with
        | none => .error (.rangeTooLong q.parent)
        | some l => req (decide (rangePin E q.parent q.rel width q.pre l = q.seen)) (.stale q.parent))
    t.ranges

/-- A parent retired by the turn holds no rows (`rowsRemain`): a relation is cleared before its
object goes. -/
def checkRowsRemain (E : Env D) (w : World D) (t : Turn D) : Except (Reject D) Unit :=
  forEx (fun x => match x.act with
    | .retire =>
        -- a parent holds at most 256 heads (`rel < 256`), so 257 entries under it include a row:
        -- the read stops there, and a full listing is refused as one
        let l := under (rowSpec E) (E.bytes x.cell) 257 w.rows
        req (decide (l.length ≤ 256) && l.all fun p =>
          match p.1 with | .row _ => false | .head .. => true) (.rowsRemain x.cell)
    | _ => .ok ()) t.touches

/-- Every check, against the pre-state only; on success, what the touches leave behind and the rows
`rowsRun` reached with what they give back (so `admitImpl` commits them without running the rows
twice). The one source of the check sequence: `check` is its first component. -/
def checkWith (E : Env D) (w : World D) (t : Turn D) : Except (Reject D) (List (Post D) × (Rows D × Nat)) := do
  checkBounds t
  checkWindow w t
  checkJournal E w t
  checkShape t
  let posts := (← mapEx (touchCheck E w) t.touches).reduceOption
  checkValue E t posts
  checkNullifiers E w t
  checkRowsRemain E w t
  checkRanges E w t
  let rr ← rowsRun E w t
  checkCharge w t (credit posts + rr.2)
  checkCreates E w t
  checkSteps w
  pure (posts, rr)

/-- Every check, against the pre-state only; on success, what the touches leave behind. -/
def check (E : Env D) (w : World D) (t : Turn D) : Except (Reject D) (List (Post D)) :=
  (checkWith E w t).map Prod.fst

def bornEntries (t : Turn D) : List (D × Entry) :=
  t.creates.map fun p => (p.1, .live p.2)

/-- Write cell entries into the map, one path each. -/
def insertAll (E : Env D) (m : Cells D) (ps : List (D × Entry)) : Cells D :=
  ps.foldl (fun m p => m.insert (trieSpec E) (.cell p.1) (.entry p.2)) m

/-- Mark nullifiers spent, one path each. -/
def spendAll (E : Env D) (m : Cells D) (ns : List D) : Cells D :=
  ns.foldl (fun m n => m.insert (trieSpec E) (.nullifier n) .spent) m

/-- The map after a checked turn: its touches' entries, its born cells, its nullifiers. No path
reads an empty digest (no node has an empty child, KERNEL-49 (a)); only an empty ROOT does, in
`commitWith` (`T.rootWith`, one lazy copy shared by the four roots). -/
def commitTrie (E : Env D) (w : World D) (t : Turn D) (posts : List (Post D)) : Cells D :=
  spendAll E (insertAll E (insertAll E w.trie (posts.map Post.pair)) (bornEntries t)) t.nullifiers


/-- A journal entry `(h, d)` is still kept at height `H`: fewer than `2 * Bounds.windowMax`
heights have passed since it was admitted (KERNEL-33). A call admitted at `h` has
`notBefore ≤ h`, so its entry answers every lookup at a height below `notBefore + 2 * windowMax`
(`journalForgets`): at least `windowMax` heights after its window ends. -/
def kept (H : Nat) (e : Nat × D) : Bool := decide (H < e.1 + 2 * Bounds.windowMax)

/-- The journal at height `H`: at every multiple of `Bounds.windowMax`, the entries no longer
`kept` are dropped (`Trie.retainAt` at the root: the canonical erase, a subtree that drops nothing
is kept with its hash, a node left with one side empty is replaced by the other side whole); between multiples it is
unchanged. One pass over at most `3 * Bounds.windowMax` entries once per `windowMax` heights, and one
structure (no second index by height). -/
def pruneJournal (E : Env D) (H : Nat) (j : Journal D) : Journal D :=
  if H % Bounds.windowMax = 0 then Trie.retainAt (journalSpec E) (fun _ x => kept H x) [] j else j

/-- Whether a World at height `H` can no longer answer for a call with window start `notBefore`:
its entry, if it was admitted, may have been pruned. Below this height an absent transaction id
was never admitted (`Kernel.Proofs.Journal.fold_retains`); at and past it, absence says nothing
(HOST answers `forgotten`, uncertain, never `expired`). -/
def journalForgets (H notBefore : Nat) : Bool := decide (notBefore + 2 * Bounds.windowMax ≤ H)

/-- Strictly ascending. -/
def ascendingNat : List Nat → Bool
  | a :: b :: l => decide (a < b) && ascendingNat (b :: l)
  | _ => true

/-- A journal listing a World at `height` can hold (KERNEL-39): every entry at most `height` and
not yet due for pruning (fewer than `2 * windowMax` heights behind the last prune), and no two
entries at one height. It is exactly `World.JournalOk` read off the listing
(`Kernel.Proofs.Journal.journalOk_of_fits`, `journalFits_of_ok`), so it holds of every World a fold
reaches and a decoded base is refused (`kernel/journal`, CODEC) unless it holds. Without it a base
could hold an entry above its height, which is never pruned and answers `replayed` forever. One
pass, and one sort of fewer than `3 * windowMax` heights. -/
def journalFits (height : Nat) (l : List (D × (Nat × D))) : Bool :=
  l.all (fun p => decide (p.2.1 ≤ height ∧
      height < p.2.1 + 2 * Bounds.windowMax + height % Bounds.windowMax)) &&
    ascendingNat ((l.map fun p => p.2.1).mergeSort)

/-- One refusals leaf a World at `height` can hold (KERNEL-47): a refused call refused at a height at
most `height + 1` and not yet due for pruning, a count of the current window between 1 and
`Bounds.refusalsPerWindow`, every counter below `2^64`, and no other pairing. -/
def refusalFits (height : Nat) : RefusalSlot D → RefusalLeaf D → Bool
  | .tx _, .refused h code _ => decide (1 ≤ h ∧ h ≤ height + 1 ∧
      height < h + 2 * Bounds.windowMax + height % Bounds.windowMax ∧ h < Bounds.counterLimit ∧
      code < Bounds.counterLimit)
  | .count _ win, .count n => decide (win = refusalWindow height ∧ 1 ≤ n ∧ n ≤ Bounds.refusalsPerWindow)
  | _, _ => false

/-- A refusals listing a World at `height` can hold (KERNEL-47; the twin of `journalFits`, for CODEC's
`kernel/refusals` refusal): every key holds the leaf of its kind; a refused call was refused at a
height at most `height + 1` (the World's height when it was recorded, plus one) and is not yet due
for pruning; a count is for the current window and between 1 and `Bounds.refusalsPerWindow`; every
counter below `2^64`. It holds of every World a fold reaches (`fold_refusalsOk`), so a decoded base
is refused unless it holds. One pass. -/
def refusalsFits (height : Nat) (l : List (RefusalSlot D × RefusalLeaf D)) : Bool :=
  l.all fun p => refusalFits height p.1 p.2

/-- No transaction id is both recorded refused and journaled (KERNEL-47; CODEC-8's ask): a fold never
reaches such a World (`fold_refusalsDisjoint`), so a decoded base is refused unless it holds. One
journal lookup per recorded refusal. -/
def refusalsDisjoint (E : Env D) (w : World D) : Bool :=
  w.refusals.toList.all fun p => match p.1, p.2 with
    | .tx id, .refused _ _ _ => (w.journalAt E id).isNone
    | _, _ => true

/-- The journal after a checked turn: the turn's entry inserted at the new height, then pruned if
that height is a multiple of `Bounds.windowMax`. -/
def commitJournal (E : Env D) (w : World D) (t : Turn D) : Journal D :=
  pruneJournal E (w.height + 1) (w.journal.insert (journalSpec E) t.txId (w.height + 1, turnDigest E t))

/-- Is a refusals leaf still kept at height `H` (KERNEL-44, KERNEL-47 amendment 5)? A refused call's
leaf while `kept` (KERNEL-33's rule: it was refused at `h` inside its window, so it outlives every
height it could be admitted at); a count only for the current window. -/
def keptRefusal (H : Nat) : RefusalSlot D → RefusalLeaf D → Bool
  | .count _ win, _ => decide (win = refusalWindow H)
  | _, .refused h _ _ => decide (H < h + 2 * Bounds.windowMax)
  | _, .count _ => false

/-- The refusals at height `H`: pruned with the journal, at every multiple of `Bounds.windowMax`, by
the same canonical `Trie.retainAt`; unchanged between multiples. -/
def pruneRefusals (E : Env D) (H : Nat) (r : Refusals D) : Refusals D :=
  if H % Bounds.windowMax = 0 then Trie.retainAt (refusalSpec E) (keptRefusal H) [] r else r

/-- The World after a checked turn, given the rows `rowsRun` reached (`rr`). Total: everything that
can fail failed in `checkWith`. -/
def commitWith (E : Env D) (w : World D) (t : Turn D) (posts : List (Post D)) (rr : Rows D × Nat) : World D :=
  -- ONE lazy copy of the empty trie's digest for the four roots (KERNEL-35, at the roots only): all
  -- four hash in `domTrie`, so their empty digest is one value
  let e : Thunk D := Thunk.mk fun _ => Trie.emptyHash (trieSpec E)
  let trie := commitTrie E w t posts
  let journal := commitJournal E w t
  let refusals := pruneRefusals E (w.height + 1) w.refusals
  let rows := rr.1
  { trie
    journal
    refusals
    rows
    height := w.height + 1
    steps := w.steps + 1
    chain := chainNext E w.chain t
      (rootsDigest E (trie.rootWith (trieSpec E) e) (journal.rootWith (journalSpec E) e)
        (refusals.rootWith (refusalSpec E) e) (rows.rootWith (rowSpec E) e))
    allowance := w.allowance + credit posts + rr.2 - t.charge
    origin := w.origin }

/-- The World after a checked turn: `commitWith` at the rows `rowsAfter` recomputes (the
specification; compiled callers run `World.admitImpl`, which commits the rows `checkWith` reached). -/
def commit (E : Env D) (w : World D) (t : Turn D) (posts : List (Post D)) : World D :=
  commitWith E w t posts (rowsAfter E w t)

/-- THE transition. Fail-closed: a refusal returns no World. -/
def World.admit (E : Env D) (w : World D) (t : Turn D) : Except (Reject D) (World D) :=
  match check E w t with
  | .ok posts => .ok (commit E w t posts)
  | .error r => .error r

/-- What compiled callers run for `World.admit` (`World.admit_eq_admitImpl`, `@[csimp]`): the checks
once, and the rows they reached committed as they are (no second `rowsRun`: KERNEL-48 WASTE). -/
def World.admitImpl (E : Env D) (w : World D) (t : Turn D) : Except (Reject D) (World D) :=
  match checkWith E w t with
  | .ok (posts, rr) => .ok (commitWith E w t posts rr)
  | .error r => .error r

private theorem bind_ok_iff {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {b : β} :
    (x >>= f) = .ok b ↔ ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x <;> simp [bind, Except.bind]

private theorem checkWith_rows {E : Env D} {w : World D} {t : Turn D} {posts : List (Post D)}
    {rr : Rows D × Nat} (h : checkWith E w t = .ok (posts, rr)) :
    rowsRun E w t = .ok rr := by
  unfold checkWith at h
  simp only [bind_ok_iff] at h
  obtain ⟨⟨⟩, -, ⟨⟩, -, ⟨⟩, -, ⟨⟩, -, raw, -, ⟨⟩, -, ⟨⟩, -, ⟨⟩, -, ⟨⟩, -, rr', hrw, ⟨⟩, -,
    ⟨⟩, -, ⟨⟩, -, h9⟩ := h
  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h9
  rw [← h9.2]; exact hrw

/-- **The compiled transition is the specified one**: `World.admit` (check, then `commit`, which
recomputes the rows) equals `World.admitImpl` (the rows `checkWith` reached, committed once). -/
@[csimp] private theorem World.admit_eq_admitImpl : @World.admit = @World.admitImpl := by
  funext D _ _ E w t
  unfold World.admit World.admitImpl check
  cases h : checkWith E w t with
  | error r => rfl
  | ok pr =>
      obtain ⟨posts, rr⟩ := pr
      show Except.ok (commit E w t posts) = Except.ok (commitWith E w t posts rr)
      unfold commit rowsAfter
      rw [checkWith_rows h]

/-- A recorded refusal's numbers are within `Bounds` (so `refusedBytes` is injective). -/
def checkRefusedBounds (r : Refused D) : Except (Reject D) Unit := do
  req (r.event.size ≤ Bounds.eventBytesMax) (.overBound .event)
  req (r.notBefore < Bounds.counterLimit && r.validUntil < Bounds.counterLimit &&
       r.code < Bounds.counterLimit) (.overBound .counter)
  -- a window no admissible call has (`checkBounds`) is not recorded: its refusal could never be
  -- final within the horizon a receipt reads (`refuse_window`; PROTOCOL's settle)
  req (r.validUntil ≤ r.notBefore + Bounds.windowMax) (.overBound .window)

/-- A member's recorded refusals in the window of height `H`. -/
def refusalCount (E : Env D) (w : World D) (m : D) : Nat :=
  match w.refusalAt E (.count m (refusalWindow w.height)) with
  | some (.count n) => n
  | _ => 0

/-! ### The counts are a function of the records (KERNEL-50, cv 01a14da3-3e7a)

A window's count leaves are a cache: what `checkRefusal` reads in one lookup instead of scanning
the records. `refusalsCounted` is the check that the cache agrees with what it caches, so a decoded
base cannot hold a count no history produces (a member's count lowered to reset its budget, or one
member's charge moved to another). Every reached World passes it (`fold_refusalsCounted`), and a
World that passes it has every count equal to its member's records this window
(`refusalCount_eq_of_counted`). It does not authenticate the records themselves: which member a
record names is what the chain binds, and what the member's receipt shows it. -/

/-- 1 at a recorded refusal's entry, else 0: summed over a listing, the records it holds. -/
def refusedOne : RefusalSlot D × RefusalLeaf D → Nat
  | (.tx _, .refused _ _ _) => 1
  | _ => 0

/-- 1 at a refusal of `m` recorded in the window of height `H`, else 0. A leaf holds `h`, the height
its World had plus one, so it was recorded in window `(h - 1) / windowMax`. -/
def refusedIn [DecidableEq D] (H : Nat) (m : D) : RefusalSlot D × RefusalLeaf D → Nat
  | (.tx _, .refused h _ m') =>
      if m' = m ∧ (h - 1) / Bounds.windowMax = H / Bounds.windowMax then 1 else 0
  | _ => 0

/-- The map `refusalTally` counts in: the refusals' routing (so a lookup is one path), and no hash,
no bytes (nothing reads its digests; `get` after `insert` is exact for any `Spec`). -/
def tallySpec (E : Env D) (seed : D) : Trie.Spec (RefusalSlot D) (RefusalLeaf D) D where
  bit := (refusalSpec E).bit
  depth := (refusalSpec E).depth
  depth_lt := (refusalSpec E).depth_lt
  hash := fun _ => seed
  dbytes := fun _ => ByteArray.empty
  kbytes := fun _ => ByteArray.empty
  vdigest := fun _ => seed

/-- The count a tally holds at a key (0 where it holds none). -/
def tallyAt [DecidableEq D] (E : Env D) (seed : D) (t : Refusals D) (k : RefusalSlot D) : Nat :=
  match t.get (tallySpec E seed) k with
  | some (.count n) => n
  | _ => 0

/-- One listed entry into the tally: a record of window `H / windowMax` bumps its member's count. -/
def tallyStep [DecidableEq D] (E : Env D) (seed : D) (H : Nat) (t : Refusals D)
    (p : RefusalSlot D × RefusalLeaf D) : Refusals D :=
  match p with
  | (.tx _, .refused h _ m) =>
      if (h - 1) / Bounds.windowMax = H / Bounds.windowMax then
        t.insert (tallySpec E seed) (.count m (refusalWindow H))
          (.count (tallyAt E seed t (.count m (refusalWindow H)) + 1))
      else t
  | _ => t

/-- Each member's records in the window of height `H`, counted from a listing: one pass, one path
per record, no hash. -/
def refusalTally [DecidableEq D] (E : Env D) (seed : D) (H : Nat) (l : List (RefusalSlot D × RefusalLeaf D)) :
    Refusals D :=
  l.foldl (tallyStep E seed H) .empty

/-- **A World's refusal counts are its records'** (KERNEL-50): every record cost a step that did not
raise the height (records + height ≤ steps); every count leaf is the tally of its member's records
this window; and every member with a record this window has a count leaf. One pass to tally, one
pass over the listing, one lookup per entry. CODEC's `kernel/refusals-counted` refusal. -/
def refusalsCounted [DecidableEq D] (E : Env D) (w : World D) : Bool :=
  let l := w.refusals.toList
  let tally := refusalTally E w.chain w.height l
  decide ((l.map refusedOne).sum + w.height ≤ w.steps) &&
    l.all fun p => match p with
      | (.count m win, .count n) => decide (tally.get (tallySpec E w.chain) (.count m win) = some (.count n))
      | (.tx _, .refused h _ m) =>
          !decide ((h - 1) / Bounds.windowMax = w.height / Bounds.windowMax) ||
            (w.refusalAt E (.count m (refusalWindow w.height))).isSome
      | _ => true

/-- Every check a refusal record must pass, against the pre-state (KERNEL-44, KERNEL-47): bounded;
the step counter below `2^64`; the call's window contains the height it would be admitted at (an
early call's refusal is not final and is not recorded, a late call's is final by height); the
transaction id neither journaled (`replayed`) nor already recorded (`refusedFinal`); the member's
count this window below `Bounds.refusalsPerWindow` (`refusalBudget`). Whether the call was
authenticated and refused with this code is the receive layer's (`Receive.judge`), re-derived by the
follower's audit; the kernel bounds what a log may record. -/
def checkRefusal (E : Env D) (w : World D) (r : Refused D) : Except (Reject D) Unit := do
  checkRefusedBounds r
  checkSteps w
  req (r.notBefore ≤ w.height + 1 && w.height + 1 ≤ r.validUntil) .outsideWindow
  match w.journalAt E r.txId with
  | some (h, _) => .error (.replayed h)
  | none =>
      match w.refusalAt E (.tx r.txId) with
      | some (.refused _ code _) => .error (.refusedFinal code)
      | _ => req (refusalCount E w r.member < Bounds.refusalsPerWindow) .refusalBudget

/-- The refusals after a checked refusal: its leaf at the transaction id, the member's count bumped.
Two paths. -/
def commitRefusals (E : Env D) (w : World D) (r : Refused D) : Refusals D :=
  (w.refusals.insert (refusalSpec E) (.tx r.txId) (.refused (w.height + 1) r.code r.member)).insert (refusalSpec E)
    (.count r.member (refusalWindow w.height)) (.count (refusalCount E w r.member + 1))

/-- The World after a checked refusal: only the refusals, the step counter and the chain move. The
cells, the journal, the height and the allowance are untouched (`refuse_frame`). -/
def commitRefusal (E : Env D) (w : World D) (r : Refused D) : World D :=
  let e : Thunk D := Thunk.mk fun _ => Trie.emptyHash (refusalSpec E)
  let refusals := commitRefusals E w r
  { w with
    refusals
    steps := w.steps + 1
    chain := refusalLink E w.chain r
      (rootsDigest E (w.trie.rootWith (trieSpec E) e) (w.journal.rootWith (journalSpec E) e)
        (refusals.rootWith (refusalSpec E) e) (w.rows.rootWith (rowSpec E) e)) }

/-- Record a refusal (KERNEL-44). Fail-closed like `World.admit`. -/
def World.refuse (E : Env D) (w : World D) (r : Refused D) : Except (Reject D) (World D) :=
  match checkRefusal E w r with
  | .ok () => .ok (commitRefusal E w r)
  | .error e => .error e

/-- THE transition of a log (KERNEL-47): a Turn is admitted, a refusal recorded. -/
def World.step (E : Env D) (w : World D) : Step D → Except (Reject D) (World D)
  | .turn t => World.admit E w t
  | .refusal r => World.refuse E w r

/-- The follower: a log means the World its fold reaches. A refusal names the step's index. -/
def World.fold (E : Env D) (w : World D) : List (Step D) → Except (Nat × Reject D) (World D)
  | [] => .ok w
  | t :: rest =>
      match World.step E w t with
      | .ok w' =>
          match World.fold E w' rest with
          | .ok w'' => .ok w''
          | .error (i, r) => .error (i + 1, r)
      | .error r => .error (0, r)

/-- The link a step adds to the chain `c`, given the roots digest after it. -/
def stepLink (E : Env D) (c : D) : Step D → D → D
  | .turn t => chainNext E c t
  | .refusal r => refusalLink E c r

/-- The chain a log reaches from `c`, each step paired with the roots digest after it
(`World.roots`), without admitting it: what `World.fold` stamps (`fold_chain`). -/
def chainOf (E : Env D) (c : D) : List (Step D × D) → D
  | [] => c
  | (t, r) :: rest => chainOf E (stepLink E c t r) rest

end Nanodregg.Kernel
