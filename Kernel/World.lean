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
height plus one, the height it would have been admitted at, as a journal entry's) and the
refusal's code; at a `count` key, how many refusals the member has had recorded in that window. -/
inductive RefusalLeaf
  | refused (h code : Nat)
  | count (n : Nat)
  deriving DecidableEq

abbrev Refusals (D : Type) := Trie.T (RefusalSlot D) RefusalLeaf D

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
the height is carried because journal entries expire by it. Not carried: the chain and the origin
(the new World's own). -/
structure Carried (D : Type) [Ord D] where
  trie : Cells D
  allowance : Nat
  height : Nat
  journal : Journal D

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
def domRefusal : String := "nanodregg/kernel/refusal-leaf/v1"
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

/-- The one digest of a World's roots after a step: the cells', the journal's, the refusals'. -/
def rootsDigest (E : Env D) (root jroot rroot : D) : D :=
  E.hash domRoots (E.bytes root ++ E.bytes jroot ++ E.bytes rroot)

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
little-endian bytes each. -/
def refusalLeafBytes : RefusalLeaf → ByteArray
  | .refused h code => ⟨#[0]⟩ ++ Nanodregg.Codec.Stream.nat64.bytes h ++ Nanodregg.Codec.Stream.nat64.bytes code
  | .count n => ⟨#[1]⟩ ++ Nanodregg.Codec.Stream.nat64.bytes n

def refusalDigest (E : Env D) (l : RefusalLeaf) : D := E.hash domRefusal (refusalLeafBytes l)

/-- The refusals trie (KERNEL-44, KERNEL-47): routed by the key's bytes, most significant bit first,
depth `Bounds.refusalDepth` (41 bytes); nodes in the one trie domain; leaves by `refusalDigest`. -/
def refusalSpec (E : Env D) : Trie.Spec (RefusalSlot D) RefusalLeaf D where
  bit k := byteBit (refusalKeyBytes E k)
  depth := Bounds.refusalDepth
  hash := E.hash domTrie
  dbytes := E.bytes
  kbytes := refusalKeyBytes E
  vdigest := refusalDigest E

/-- A refusals key holds the leaf of its kind. -/
def RefusalLeaf.fits {D : Type} : RefusalSlot D → RefusalLeaf → Bool
  | .tx _, .refused _ _ => true
  | .count _ _, .count _ => true
  | _, _ => false

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

/-- The one digest of the roots a head link commits (`chainNext`, `refusalLink`): the cells', the
journal's and the refusals' (KERNEL-47 amendment 3). -/
def roots (E : Env D) (w : World D) : D := rootsDigest E (w.root E) (w.journalRoot E) (w.refusalsRoot E)

/-- What a carry takes from this World (KERNEL-29). -/
def carried (w : World D) : Carried D := ⟨w.trie, w.allowance, w.height, w.journal⟩

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
def refusalAt (E : Env D) (w : World D) (k : RefusalSlot D) : Option RefusalLeaf :=
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

/-- The storage a World holds, by the same per-field costs as `Turn.weight`: each cell entry with
its id and each spent nullifier. The journal is not in it: it is pruned to the window
(`pruneJournal`, KERNEL-33), so it is a bounded overhead (`journal_bounded`: fewer than
`3 * Bounds.windowMax` entries), not storage a turn buys. A specification measure (O(store)),
never computed on the request path; `Kernel.Proofs.Weight` bounds it by the budget spent. -/
def weight (w : World D) : Nat :=
  cellsWeight w.trie

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

variable [DecidableEq D]

/-- A transaction id is admitted at most once; a retry names the height it landed at. -/
def checkJournal (E : Env D) (w : World D) (t : Turn D) : Except (Reject D) Unit :=
  match w.journalAt E t.txId with
  | some (h, _) => .error (.replayed h)
  | none =>
      match w.refusalAt E (.tx t.txId) with
      | some (.refused _ code) => .error (.refusedFinal code)
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

/-- Every check, against the pre-state only; on success, what the touches leave behind. -/
def check (E : Env D) (w : World D) (t : Turn D) : Except (Reject D) (List (Post D)) := do
  checkBounds t
  checkWindow w t
  checkJournal E w t
  checkShape t
  let posts := (← mapEx (touchCheck E w) t.touches).reduceOption
  checkValue E t posts
  checkNullifiers E w t
  checkCharge w t (credit posts)
  checkCreates E w t
  checkSteps w
  pure posts

def bornEntries (t : Turn D) : List (D × Entry) :=
  t.creates.map fun p => (p.1, .live p.2)

/-- Write cell entries into the map, one path each (`e`: the empty subtree's digest, as in
`Trie.T.hashOf`). -/
def insertAll (E : Env D) (m : Cells D) (ps : List (D × Entry))
    (e : Trie.EmptyDigest D := Thunk.mk fun _ => Trie.emptyHash (trieSpec E)) : Cells D :=
  ps.foldl (fun m p => m.insert (trieSpec E) (.cell p.1) (.entry p.2) e) m

/-- Mark nullifiers spent, one path each. -/
def spendAll (E : Env D) (m : Cells D) (ns : List D)
    (e : Trie.EmptyDigest D := Thunk.mk fun _ => Trie.emptyHash (trieSpec E)) : Cells D :=
  ns.foldl (fun m n => m.insert (trieSpec E) (.nullifier n) .spent e) m

/-- The map after a checked turn: its touches' entries, its born cells, its nullifiers. One lazy
copy of the empty subtree's digest is handed down every path, so it is hashed at most once per turn
and only if a path meets an empty sibling (KERNEL-35); `commit` hands it the one copy it shares with
the journal and the refusals (KERNEL-47). -/
def commitTrie (E : Env D) (w : World D) (t : Turn D) (posts : List (Post D))
    (e : Trie.EmptyDigest D := Thunk.mk fun _ => Trie.emptyHash (trieSpec E)) : Cells D :=
  spendAll E (insertAll E (insertAll E w.trie (posts.map Post.pair) e) (bornEntries t) e)
    t.nullifiers e


/-- A journal entry `(h, d)` is still kept at height `H`: fewer than `2 * Bounds.windowMax`
heights have passed since it was admitted (KERNEL-33). A call admitted at `h` has
`notBefore ≤ h`, so its entry answers every lookup at a height below `notBefore + 2 * windowMax`
(`journalForgets`): at least `windowMax` heights after its window ends. -/
def kept (H : Nat) (e : Nat × D) : Bool := decide (H < e.1 + 2 * Bounds.windowMax)

/-- The journal at height `H`: at every multiple of `Bounds.windowMax`, the entries no longer
`kept` are dropped (`Trie.retainAt` at the root: the canonical erase, a subtree that drops nothing
is kept with its hash, a node left with one key collapses to its leaf); between multiples it is
unchanged. One pass over at most `3 * Bounds.windowMax` entries once per `windowMax` heights, and one
structure (no second index by height). `e` as in `Trie.T.hashOf`. -/
def pruneJournal (E : Env D) (H : Nat) (j : Journal D)
    (e : Trie.EmptyDigest D := Thunk.mk fun _ => Trie.emptyHash (journalSpec E)) : Journal D :=
  if H % Bounds.windowMax = 0 then Trie.retainAt (journalSpec E) (fun _ x => kept H x) [] j e else j

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
def refusalFits (height : Nat) : RefusalSlot D → RefusalLeaf → Bool
  | .tx _, .refused h code => decide (1 ≤ h ∧ h ≤ height + 1 ∧
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
def refusalsFits (height : Nat) (l : List (RefusalSlot D × RefusalLeaf)) : Bool :=
  l.all fun p => refusalFits height p.1 p.2

/-- No transaction id is both recorded refused and journaled (KERNEL-47; CODEC-8's ask): a fold never
reaches such a World (`fold_refusalsDisjoint`), so a decoded base is refused unless it holds. One
journal lookup per recorded refusal. -/
def refusalsDisjoint (E : Env D) (w : World D) : Bool :=
  w.refusals.toList.all fun p => match p.1, p.2 with
    | .tx id, .refused _ _ => (w.journalAt E id).isNone
    | _, _ => true

/-- The journal after a checked turn: the turn's entry inserted at the new height, then pruned if
that height is a multiple of `Bounds.windowMax`. One lazy copy of the empty subtree's digest serves
the insert and the prune (KERNEL-35's rule); `commit` hands it the one copy of the turn. -/
def commitJournal (E : Env D) (w : World D) (t : Turn D)
    (e : Trie.EmptyDigest D := Thunk.mk fun _ => Trie.emptyHash (journalSpec E)) : Journal D :=
  pruneJournal E (w.height + 1) (w.journal.insert (journalSpec E) t.txId (w.height + 1, turnDigest E t) e) e

/-- Is a refusals leaf still kept at height `H` (KERNEL-44, KERNEL-47 amendment 5)? A refused call's
leaf while `kept` (KERNEL-33's rule: it was refused at `h` inside its window, so it outlives every
height it could be admitted at); a count only for the current window. -/
def keptRefusal (H : Nat) : RefusalSlot D → RefusalLeaf → Bool
  | .count _ win, _ => decide (win = refusalWindow H)
  | _, .refused h _ => decide (H < h + 2 * Bounds.windowMax)
  | _, .count _ => false

/-- The refusals at height `H`: pruned with the journal, at every multiple of `Bounds.windowMax`, by
the same canonical `Trie.retainAt`; unchanged between multiples. -/
def pruneRefusals (E : Env D) (H : Nat) (r : Refusals D)
    (e : Trie.EmptyDigest D := Thunk.mk fun _ => Trie.emptyHash (refusalSpec E)) : Refusals D :=
  if H % Bounds.windowMax = 0 then Trie.retainAt (refusalSpec E) (keptRefusal H) [] r e else r

/-- The World after a checked turn. Total: everything that can fail failed in `check`. -/
def commit (E : Env D) (w : World D) (t : Turn D) (posts : List (Post D)) : World D :=
  -- ONE lazy copy of the empty subtree's digest for the three tries (KERNEL-35's rule, per turn): all
  -- three hash nodes in `domTrie`, so their empty digest is one value
  let e : Trie.EmptyDigest D := Thunk.mk fun _ => Trie.emptyHash (trieSpec E)
  let trie := commitTrie E w t posts e
  let journal := commitJournal E w t e
  let refusals := pruneRefusals E (w.height + 1) w.refusals e
  { trie
    journal
    refusals
    height := w.height + 1
    steps := w.steps + 1
    chain := chainNext E w.chain t
      (rootsDigest E (trie.hashOf (trieSpec E) e) (journal.hashOf (journalSpec E) e) (refusals.hashOf (refusalSpec E) e))
    allowance := w.allowance + credit posts - t.charge
    origin := w.origin }

/-- THE transition. Fail-closed: a refusal returns no World. -/
def World.admit (E : Env D) (w : World D) (t : Turn D) : Except (Reject D) (World D) :=
  match check E w t with
  | .ok posts => .ok (commit E w t posts)
  | .error r => .error r

/-- A recorded refusal's numbers are within `Bounds` (so `refusedBytes` is injective). -/
def checkRefusedBounds (r : Refused D) : Except (Reject D) Unit := do
  req (r.event.size ≤ Bounds.eventBytesMax) (.overBound .event)
  req (r.notBefore < Bounds.counterLimit && r.validUntil < Bounds.counterLimit &&
       r.code < Bounds.counterLimit) (.overBound .counter)

/-- A member's recorded refusals in the window of height `H`. -/
def refusalCount (E : Env D) (w : World D) (m : D) : Nat :=
  match w.refusalAt E (.count m (refusalWindow w.height)) with
  | some (.count n) => n
  | _ => 0

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
      | some (.refused _ code) => .error (.refusedFinal code)
      | _ => req (refusalCount E w r.member < Bounds.refusalsPerWindow) .refusalBudget

/-- The refusals after a checked refusal: its leaf at the transaction id, the member's count bumped.
Two paths; one lazy empty digest as in `commitJournal`. -/
def commitRefusals (E : Env D) (w : World D) (r : Refused D)
    (e : Trie.EmptyDigest D := Thunk.mk fun _ => Trie.emptyHash (refusalSpec E)) : Refusals D :=
  (w.refusals.insert (refusalSpec E) (.tx r.txId) (.refused (w.height + 1) r.code) e).insert (refusalSpec E)
    (.count r.member (refusalWindow w.height)) (.count (refusalCount E w r.member + 1)) e

/-- The World after a checked refusal: only the refusals, the step counter and the chain move. The
cells, the journal, the height and the allowance are untouched (`refuse_frame`). -/
def commitRefusal (E : Env D) (w : World D) (r : Refused D) : World D :=
  let e : Trie.EmptyDigest D := Thunk.mk fun _ => Trie.emptyHash (refusalSpec E)
  let refusals := commitRefusals E w r e
  { w with
    refusals
    steps := w.steps + 1
    chain := refusalLink E w.chain r
      (rootsDigest E (w.trie.hashOf (trieSpec E) e) (w.journal.hashOf (journalSpec E) e) (refusals.hashOf (refusalSpec E) e)) }

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
