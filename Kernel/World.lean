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

Order of the checks `checkWith` makes (each refuses by name, nothing is written before all pass):
bounds → window (an expired retry is `outsideWindow`, whether or not its entry was pruned:
KERNEL-33) → journal (an exact retry inside its window is `replayed`) → shape → touches
(ONE lookup per touched cell: its cell pin (`stale`), then its write or retirement, and a written
value cell's decoding and floor) → value (born value cells, then every denomination's balance and
floor sums: LEDGER-2) → nullifiers → rows remain (a retired parent holds no row) → ranges (each range
read's relation, width, length and listing pin (`stale`)) → rows (each row touch in order, a pinned
row's pin (`stale`) among its checks, then a retired parent's heads) → charge → created ids →
member ticks → the step counter. On the Host's path `Receive.submit` has already compared every pin before deriving the
Turn (KERNEL-66, `checkPins`), so there a `stale` from admission is not reached; a log's Turn (the
follower's fold) meets these three comparisons here.
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

/-- A cell id's slot in the World: a live cell with its version, or the tombstone of a retired one.
The version (KERNEL-54) counts the cell's writes: 0 at its birth, one more per write (`touchCheck`),
refused past `Bounds.counterLimit` by name (`overBound .version`). A pin names it, so a pin observed on
the fold and stale now is BEHIND for ever: no World the fold reaches holds it again, up to a collision
on the pin inputs (`stale_behind_forever`). A pin naming a FUTURE version (AHEAD) is stale now and may
match later: it is not final.
A tomb carries none: it is terminal (an id is never reborn, `checkCreates`; nothing removes an entry). -/
inductive Entry
  | live (cell : Cell) (ver : Nat)
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
  /-- the cell is not what the signer saw: its entry's pin (`pinOf`, version included) differs. Never
  recorded (KERNEL-54): a pin observed on the fold and stale now (BEHIND) is stale at every World the
  fold reaches, up to a collision on the pin inputs (`stale_behind_forever`; for rows and ranges, or
  the parent is retired), so it is final without a record; a pin naming a future version (AHEAD) is
  declined too, and is not final -/
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
  /-- a retract of a row that is absent, pinned absent (KERNEL-54: its pin matched; it was `stale`) -/
  | missingRow (parent : D)
  /-- the World's authenticated, in-window refusals this window, all members together, have reached
  `Bounds.refusalsPerWindowMax` (KERNEL-55 R1): the refusal is not recorded (it is NOT a verdict on
  the call; a liveness cost on refusal finality until the window turns, never on admission) -/
  | refusalsFull
  /-- the member's admitted ticks this window, with this Turn's, would pass `Bounds.ticksPerWindow`
  (DESIGN-OBS §1.3, the meter): a rate limit on compute as `refusalBudget` is on refusals; recorded
  (class (A): the call was signed and its pins compared) and final within its window -/
  | ticksBudget (member : D)
  /-- the Turn's causal pin (KERNEL-79) names step `steps`, where this World's chain is another: the
  signer planned on another history. Never recorded: the chain at a passed step never changes along a
  fold, so the pin is forked at every World this one reaches (final without a record, like a `stale`
  pin BEHIND) -/
  | forkedPin (steps : Nat)
  /-- the causal pin names a step this World has not reached: the signer saw a longer history. Never
  recorded, and not final (a World can reach the step) -/
  | pinAhead (steps : Nat)
  /-- the causal pin names a step older than the ring of recent heads (`Bounds.pinWindow`): the World
  can no longer say whether it is its own. Never recorded; refused, never admitted unchecked -/
  | pinExpired (steps : Nat)
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
  | .missingRow _ => "missingRow"
  | .refusalsFull => "refusalsFull"
  | .ticksBudget _ => "ticksBudget"
  | .forkedPin _ => "forkedPin"
  | .pinAhead _ => "pinAhead"
  | .pinExpired _ => "pinExpired"

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
trie type: a refused transaction id, a member's refusal count for one window (`windowMax`
heights), or the World's refusal count for one window, all members together (KERNEL-55 R1). Routed
by a kind byte and the raw bytes (`refusalKeyBytes`), fixed width, no hash.

`total`'s digest is the World's `origin`, a FILLER: every key is one kind byte, one digest and eight
bytes, so the keys are fixed width (`refusalKeyBytes_size`, on which the leaf body's injectivity and
CODEC's key order rest). A member-less key has no digest of its own, the kernel has no digest
constant (`D` carries no `Inhabited`, `Env` no width), and a hashed constant would put a hash in every
routing bit. The origin is a real digest of the World, constant over its life; `refusalsCounted`
refuses a `total` leaf under any other digest. -/
inductive RefusalSlot (D : Type)
  | tx (id : D)
  | count (member : D) (win : UInt64)
  | total (origin : D) (win : UInt64)
  deriving DecidableEq

/-- A key of the meter (KERNEL-68, DESIGN-OBS §1.3): a member's admitted ticks for one window, a
`count` leaf `World.admit` bumps for every Turn with `ticks > 0` and prunes with the window's refusal
counts. The window trie's SECOND kind: `meterAt` reads it and `refusalAt` cannot name it. -/
inductive MeterSlot (D : Type)
  | ticks (member : D) (win : UInt64)
  deriving DecidableEq

/-- A key of the ring of recent chain heads (KERNEL-79): position `j` of the ring (`steps % pinWindow`).
`origin` is the World's, a FILLER, as `total`'s is: every window key is one kind byte, one digest and
eight bytes. The window trie's THIRD kind: `chainAt` reads it; `refusalAt` and `meterAt` cannot name it. -/
inductive ChainSlot (D : Type)
  | ring (origin : D) (j : UInt64)
  deriving DecidableEq

/-- A key of the window trie (the World's `refusals`): the refusal window's keys (KERNEL-44) or the
meter's (KERNEL-68) — two kinds of one trie under one root, routed by one key width (kind bytes 0–2
and 3, `refusalKeyBytes`), pruned together at the window's end. Each reader is typed by its kind
(`refusalAt` over `RefusalSlot`, `meterAt` over `MeterSlot`), so a theorem over the refusal window
excludes the meter by its DOMAIN and never by a hypothesis (`admit_refusalAt`, `Frame.refusals` keep
their statements; the meter has `admit_meterAt` and `Frame.meter` of its own). -/
inductive WindowSlot (D : Type)
  | refusal (k : RefusalSlot D)
  | meter (k : MeterSlot D)
  | chain (k : ChainSlot D)
  deriving DecidableEq

/-- What the refusals trie holds: at a `tx` key, the height the call was refused AT (the World's
height plus one, the height it would have been admitted at, as a journal entry's), the refusal's
code, and the member it was charged to (KERNEL-50: so a window's count is a function of its
records, `refusalsCounted`, and a receipt names WHO was charged); at a `count` key, how many
refusals the member has had recorded in that window; at a `total` key (a `count` leaf), how many
refusals the World has had recorded in that window. -/
inductive RefusalLeaf (D : Type)
  | refused (h code : Nat) (member : D)
  | count (n : Nat)
  /-- a ring leaf (KERNEL-79): the chain the World had at step `steps` -/
  | head (steps : Nat) (chain : D)
  deriving DecidableEq

abbrev Refusals (D : Type) := Trie.T (WindowSlot D) (RefusalLeaf D) D

/-- The rows trie (KERNEL-46): heads and rows, under its own root. -/
abbrev Rows (D : Type) := Trie.T (RowSlot D) RowLeaf D

/-- A recorded refusal, as the log carries it (KERNEL-44): the call's transaction id, its signer,
its window, the refusal's code, and the signed call's bytes (the follower decodes them and re-derives
the same refusal, `Receive.rederive`). -/
structure Refused (D : Type) where
  txId : D
  member : D
  notBefore : Nat
  validUntil : Nat
  code : Nat
  event : ByteArray
  /-- empty for a judged refusal; for a CANCEL (KERNEL-60, design C1: code `cancelled`, the event the
  cancelled call's own bytes), the member's signature over `domCancel ‖ txId`, which the follower
  re-verifies (`Receive.rederive`: `cancelForged`) -/
  cancel : ByteArray
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
  /-- the recorded refusals (KERNEL-44), a trie with its own root, committed beside the other
  three. It holds the refused transaction ids, the per-member window counts, the World's window
  totals (KERNEL-55) and the per-member tick meter (KERNEL-68) -/
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
/-- A live cell's pin: its version, then its canonical bytes (KERNEL-54: v2, the version added). -/
def domCell : String := "nanodregg/kernel/pin-cell/v2"
/-- A tombstone's pin (KERNEL-54): distinct from absence, so never born → born → retired does not
return the absent pin (`pinOf_old_recurs`, the tooth on the pin before KERNEL-54). -/
def domTomb : String := "nanodregg/kernel/pin-tomb/v1"
def domTurn : String := "nanodregg/kernel/turn/v1"
def domChain : String := "nanodregg/kernel/chain/v1"
def domCellId : String := "nanodregg/kernel/cell-id/v1"
def domRomId : String := "nanodregg/kernel/rom-id/v1"
/-- The trie's node hash (`Trie.Spec.hash`: the shape tag byte, then the shape's bytes). -/
def domTrie : String := "nanodregg/kernel/trie/v1"
/-- A trie leaf's value digest: ONE domain, a kind byte first, so two different leaves have one
digest only by a collision of their two inputs in that domain (`leafDigest_inj`), never across
domains. -/
def domLeaf : String := "nanodregg/kernel/trie-leaf/v2"
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

/-- What a pin asserts about a cell id's entry (KERNEL-54): absence, a tombstone, or a live cell's
version and bytes, three distinct digests (one domain each). -/
def pinOf (E : Env D) : Option Entry → D
  | none => E.hash domAbsent ByteArray.empty
  | some .tomb => E.hash domTomb ByteArray.empty
  | some (.live c v) => E.hash domCell (Nanodregg.Codec.Stream.nat64.bytes v ++ E.cellBytes c)

def turnDigest (E : Env D) (t : Turn D) : D := E.hash domTurn (E.turnBytes t)

/-- What a recorded refusal commits in the chain: every field, the counters as CODEC's eight
little-endian bytes (injective below 2^64, which `World.refuse` checks), the cancel signature after
its eight-byte length, the event last. -/
def refusedBytes (E : Env D) (r : Refused D) : ByteArray :=
  E.bytes r.txId ++ E.bytes r.member ++ Nanodregg.Codec.Stream.nat64.bytes r.notBefore ++
    Nanodregg.Codec.Stream.nat64.bytes r.validUntil ++ Nanodregg.Codec.Stream.nat64.bytes r.code ++
    Nanodregg.Codec.Stream.nat64.bytes r.cancel.size ++ r.cancel ++ r.event

def refusedDigest (E : Env D) (r : Refused D) : D := E.hash domRefused (refusedBytes E r)

/-- The one digest of a World's roots after a step: the cells', the journal's, the refusals', the
rows' (KERNEL-48). -/
def rootsDigest (E : Env D) (root jroot rroot rowsroot : D) : D :=
  E.hash domRoots (E.bytes root ++ E.bytes jroot ++ E.bytes rroot ++ E.bytes rowsroot)

/-- The head link: a kind byte (0 a Turn, 1 a recorded refusal: one domain, so a turn link equal to
a refusal link is a collision of the two links' inputs, `headLink_inj`, KERNEL-47 amendment 2), the
previous head, the step's digest, and the roots digest after the step. -/
def headLink (E : Env D) (prev : D) (tag : UInt8) (d rd : D) : D :=
  E.hash domChain (⟨#[tag]⟩ ++ E.bytes prev ++ E.bytes d ++ E.bytes rd)

omit [Ord D] in
/-- What `headLink` hashes. -/
def linkPre (E : Env D) (prev : D) (tag : UInt8) (d rd : D) : String × ByteArray :=
  (domChain, ⟨#[tag]⟩ ++ E.bytes prev ++ E.bytes d ++ E.bytes rd)

omit [Ord D] in
/-- What `rootsDigest` hashes. -/
def rootsPre (E : Env D) (a b c d : D) : String × ByteArray :=
  (domRoots, E.bytes a ++ E.bytes b ++ E.bytes c ++ E.bytes d)

omit [Ord D] in
/-- What `refusedDigest` hashes. -/
def refusedPre (E : Env D) (r : Refused D) : String × ByteArray := (domRefused, refusedBytes E r)

/-- The next chain head after an admitted Turn commits to the previous one, the Turn, and the ROOTS
AFTER it (KERNEL-23 (d), KERNEL-41, KERNEL-47): `rd` is `rootsOf` the four roots, the cells', the
journal's, the refusals' and the rows'. A phone that trusts one head checks `(prev, turnDigest, rd)`
against it, opens `rd` to the four roots, then verifies cells, transaction ids, refusals or rows
against them. -/
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
a live cell's version (eight little-endian bytes: injective below `Bounds.counterLimit`, which
admission keeps) and canonical bytes. -/
def leafBytes (E : Env D) : Leaf → ByteArray
  | .entry (.live c v) => ⟨#[0]⟩ ++ Nanodregg.Codec.Stream.nat64.bytes v ++ E.cellBytes c
  | .entry .tomb => ⟨#[1]⟩
  | .spent => ⟨#[2]⟩

/-- What a leaf commits to of its value. -/
def leafDigest (E : Env D) (l : Leaf) : D := E.hash domLeaf (leafBytes E l)

omit [Ord D] in
/-- What `leafDigest` hashes. -/
def leafPre (E : Env D) (l : Leaf) : String × ByteArray := (domLeaf, leafBytes E l)

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

omit [Ord D] in
/-- What `journalDigest` hashes. -/
def journalPre (E : Env D) (e : Nat × D) : String × ByteArray :=
  (domJournal, Nanodregg.Codec.Stream.nat64.bytes e.1 ++ E.bytes e.2)

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
eight bytes (zero for `tx`, the window's little-endian for `count` and `total`; `total`'s digest is
the World's origin, a filler: `RefusalSlot`). One width for both kinds, so
the keys are prefix-free with no hash and no World invariant (`refusals_separate`). -/
def refusalKeyBytes (E : Env D) : WindowSlot D → ByteArray
  | .refusal (.tx id) => ⟨#[0]⟩ ++ E.bytes id ++ Nanodregg.Codec.Stream.nat64.bytes 0
  | .refusal (.count m win) => ⟨#[1]⟩ ++ E.bytes m ++ Nanodregg.Codec.Stream.u64.bytes win
  | .refusal (.total o win) => ⟨#[2]⟩ ++ E.bytes o ++ Nanodregg.Codec.Stream.u64.bytes win
  | .meter (.ticks m win) => ⟨#[3]⟩ ++ E.bytes m ++ Nanodregg.Codec.Stream.u64.bytes win
  | .chain (.ring o j) => ⟨#[4]⟩ ++ E.bytes o ++ Nanodregg.Codec.Stream.u64.bytes j

/-- What a refusals leaf commits to: a kind byte (refused 0, count 1), then its counters as eight
little-endian bytes each, then (refused) the charged member's bytes. -/
def refusalLeafBytes (E : Env D) : RefusalLeaf D → ByteArray
  | .refused h code m => ⟨#[0]⟩ ++ Nanodregg.Codec.Stream.nat64.bytes h ++ Nanodregg.Codec.Stream.nat64.bytes code ++
      E.bytes m
  | .count n => ⟨#[1]⟩ ++ Nanodregg.Codec.Stream.nat64.bytes n
  | .head s c => ⟨#[2]⟩ ++ Nanodregg.Codec.Stream.nat64.bytes s ++ E.bytes c

def refusalDigest (E : Env D) (l : RefusalLeaf D) : D := E.hash domRefusal (refusalLeafBytes E l)

omit [Ord D] in
/-- What `refusalDigest` hashes. -/
def refusalPre (E : Env D) (v : RefusalLeaf D) : String × ByteArray := (domRefusal, refusalLeafBytes E v)

/-- The refusals trie (KERNEL-44, KERNEL-47): routed by the key's bytes, most significant bit first,
depth `Bounds.refusalDepth` (41 bytes); nodes in the one trie domain; leaves by `refusalDigest`. -/
def refusalSpec (E : Env D) : Trie.Spec (WindowSlot D) (RefusalLeaf D) D where
  bit k := byteBit (refusalKeyBytes E k)
  depth := Bounds.refusalDepth
  depth_lt := by decide
  hash := E.hash domTrie
  dbytes := E.bytes
  kbytes := refusalKeyBytes E
  vdigest := refusalDigest E

section Reads
variable {K V : Type} [DecidableEq K]

omit [Ord D] [DecidableEq K] in
/-- Trie-node bytes as the kernel's hash takes them: in `domTrie`. -/
def trieIn (L : List ByteArray) : List (String × ByteArray) := L.map fun b => (domTrie, b)

omit [Ord D] [DecidableEq K] in
/-- **What a read compares**, as the kernel's hash takes it: the trie-node bytes the presented proof
hashes for `k` and those the trie hashed along `k`'s path (`Trie.readPres`), in `domTrie`. -/
def readPres (S : Trie.Spec K V D) (k : K) (p : Trie.Proof K D) (t : Trie.T K V D) :
    List (String × ByteArray) :=
  trieIn (Trie.readPres S k p t)

omit [Ord D] in
/-- **What an inclusion read compares**: the claimed value's leaf input, the trie's value's at `k`
(if any), and `readPres`. -/
def inclPres (S : Trie.Spec K V D) (vpre : V → String × ByteArray) (k : K) (v : V)
    (p : Trie.Proof K D) (t : Trie.T K V D) : List (String × ByteArray) :=
  vpre v :: ((t.get S k).toList.map vpre ++ readPres S k p t)

end Reads

/-- A refusals key holds the leaf of its kind. -/
def RefusalLeaf.fits {D : Type} : WindowSlot D → RefusalLeaf D → Bool
  | .refusal (.tx _), .refused _ _ _ => true
  | .refusal (.count _ _), .count _ => true
  | .refusal (.total _ _), .count _ => true
  | .meter (.ticks _ _), .count _ => true
  | .chain (.ring _ _), .head _ _ => true
  | _, _ => false

/-! ## Rows (KERNEL-46, LANG-44): the fourth instance of the one trie, and its two pin kinds -/


def domRowLeaf : String := "nanodregg/kernel/row-leaf/v2"
def domRowAbsent : String := "nanodregg/kernel/row-pin-absent/v2"
def domRange : String := "nanodregg/kernel/range-pin/v2"

/-- One byte: a constant tag (a kind, a flag). Never a number that can reach 256: those are
`natBytes`. -/
def byte8 (n : Nat) : ByteArray := ⟨#[UInt8.ofNat n]⟩

/-- The bytes of a relation's rows, before the key's own bytes: the parent, the relation, the row
tag (1) and the key width. A range read's prefix is this followed by the key prefix. -/
def rowsPrefix (E : Env D) (parent : D) (rel width : Nat) : ByteArray :=
  E.bytes parent ++ natBytes rel ++ byte8 1 ++ natBytes width

/-- A rows key's bytes (KERNEL-46 amendment 1, cv 01a14f7e): a head is `parent ‖ rel ‖ 0`; a row is
`parent ‖ rel ‖ 1 ‖ |k| ‖ k`, the relation and the length as `natBytes`. The encoding is injective and
prefix-free for every key (`Kernel.Proofs.RowsSep.rowKeyBytes_append_inj`); only the trie's
separation within its depth needs the key bounds (`rows_separateOn`). -/
def rowKeyBytes (E : Env D) : RowSlot D → ByteArray
  | .head p rel => E.bytes p ++ natBytes rel ++ byte8 0
  | .row key => rowsPrefix E key.parent key.rel key.k.size ++ key.k

/-- What a rows leaf commits to: a kind byte (head 0, row 1), its counters as eight little-endian
bytes each, the retract flag as one byte, a head's floor and a row's version (KERNEL-54) as eight
bytes, a row's value last. -/
def rowLeafBytes : RowLeaf → ByteArray
  | .head count sum limit cap width retract floor =>
      byte8 0 ++ Nanodregg.Codec.Stream.nat64.bytes count ++ Nanodregg.Codec.Stream.nat64.bytes sum ++
        Nanodregg.Codec.Stream.nat64.bytes limit ++ Nanodregg.Codec.Stream.nat64.bytes cap ++
        Nanodregg.Codec.Stream.nat64.bytes width ++ byte8 (if retract then 1 else 0) ++
        Nanodregg.Codec.Stream.nat64.bytes floor
  | .row amt val ver => byte8 1 ++ Nanodregg.Codec.Stream.nat64.bytes amt ++
      Nanodregg.Codec.Stream.nat64.bytes ver ++ (Nanodregg.Codec.Stream.rawBytes Bounds.valueBytesMax).bytes val

def rowDigest (E : Env D) (l : RowLeaf) : D := E.hash domRowLeaf (rowLeafBytes l)

/-- What a rows leaf digest hashes (`rowDigest`): `rowLeafBytes` in `domRowLeaf`. -/
def rowLeafPre (l : RowLeaf) : String × ByteArray := (domRowLeaf, rowLeafBytes l)

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

/-- What a row pin asserts (the first pin kind): the leaf's digest (a row's version inside it), or
absence AT its relation's `floor` (KERNEL-54: a retract removes the row, so absence recurs; the floor,
which every retract raises past the row it removes, makes each absence a new pin). -/
def rowPin (E : Env D) (floor : Nat) : Option RowLeaf → D
  | none => E.hash domRowAbsent (Nanodregg.Codec.Stream.nat64.bytes floor)
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

/-- Bounded listing on the dirty overlay: no digest is read or computed. -/
def takeListU {K V : Type} (n : Nat) : Trie.U K V D → List (K × V)
  | .clean t => takeList n t
  | .leaf kvs => kvs.take n
  | .node _ _ l r =>
      if n = 0 then [] else
        let a := takeListU n l
        a ++ takeListU (n - a.length) r

/-- The prefix listing before seal, with exactly the sealed trie's bounded walk. -/
def underU {K V : Type} (S : Trie.Spec K V D) (pre : ByteArray) (n : Nat) :
    Trie.U K V D → List (K × V)
  | .clean t => under S pre n t
  | .leaf kvs => (kvs.filter fun p => startsWith pre (S.kbytes p.1)).take n
  | .node b rep l r =>
      if b < 8 * pre.size then
        (if byteBit pre b then underU S pre n r else underU S pre n l)
      else if startsWith pre (S.kbytes rep) then takeListU n (.node b rep l r) else []

/-- A range read's rows (LANG-44 (c)): those of `rel` under `parent` whose key starts with `pre`,
in key order, given the relation's key `width`; `none` past `most` (`rangeTooLong`: refused, never
truncated). At most `most + 1` rows are read (KERNEL-48: the WASTE row rows-read-per-range-read). -/
def rangeRows (E : Env D) (r : Rows D) (parent : D) (rel width : Nat) (pre : ByteArray) (most : Nat) :
    Option (List (RowSlot D × RowLeaf)) :=
  let l := under (rowSpec E) (rowsPrefix E parent rel width ++ pre) (most + 1) r
  if l.length ≤ most then some l else none

/-- What a range pin asserts (the second pin kind): the relation, the width and the prefix, the
relation's floor (KERNEL-54: a row leaving raises it, so a listing never returns to an old pin), then
the listing's length and each row's key bytes and leaf digest (its version inside), in key order. A
row moving, landing or leaving under the prefix changes it. -/
def rangePinBytes (E : Env D) (parent : D) (rel width : Nat) (pre : ByteArray) (floor : Nat)
    (l : List (RowSlot D × RowLeaf)) : ByteArray :=
  rowsPrefix E parent rel width ++ natBytes pre.size ++ pre ++ Nanodregg.Codec.Stream.nat64.bytes floor ++
    Nanodregg.Codec.Stream.nat32.bytes l.length ++
    (l.foldl (fun acc p => acc ++ rowKeyBytes E p.1 ++ E.bytes (rowDigest E p.2)) ByteArray.empty)

def rangePin (E : Env D) (parent : D) (rel width : Nat) (pre : ByteArray) (floor : Nat)
    (l : List (RowSlot D × RowLeaf)) : D :=
  E.hash domRange (rangePinBytes E parent rel width pre floor l)

/-! ### What each pin hashes (KERNEL-54/56): the (domain, bytes) input of `pinOf`, `rowPin`, a listing's
row digests and `rangePin`, so a theorem's hash escape names the concrete inputs it compares
(`Kernel.Proofs.Versions`: `pinOf_eq_pre`, `rowPin_eq_pre`, `CollidesAmong`). -/

/-- What `pinOf` hashes: the domain (absent, tombstone, live) and the bytes. -/
def pinPre (E : Env D) : Option Entry → String × ByteArray
  | none => (domAbsent, ByteArray.empty)
  | some .tomb => (domTomb, ByteArray.empty)
  | some (.live c v) => (domCell, Nanodregg.Codec.Stream.nat64.bytes v ++ E.cellBytes c)

/-- What `rowPin` hashes: an absent slot's floor (`domRowAbsent`) or the leaf's bytes (`domRowLeaf`). -/
def rowPre (floor : Nat) : Option RowLeaf → String × ByteArray
  | none => (domRowAbsent, Nanodregg.Codec.Stream.nat64.bytes floor)
  | some l => (domRowLeaf, rowLeafBytes l)

/-- The leaf inputs a listing embeds (each row's `rowDigest` input), in listing order. -/
def leafPres (l : List (RowSlot D × RowLeaf)) : List (String × ByteArray) :=
  l.map fun p => (domRowLeaf, rowLeafBytes p.2)

/-- What `rangePin` hashes. -/
def rangePre (E : Env D) (parent : D) (rel width : Nat) (pre : ByteArray) (floor : Nat)
    (l : List (RowSlot D × RowLeaf)) : String × ByteArray :=
  (domRange, rangePinBytes E parent rel width pre floor l)

/-- The window a height counts refusals in. -/
def refusalWindow (H : Nat) : UInt64 := UInt64.ofNat (H / Bounds.windowMax)

/-- The ring position of step `s` (KERNEL-79). -/
def ringSlot (s : Nat) : UInt64 := UInt64.ofNat (s % Bounds.pinWindow)

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
ROM, else derived from the transaction. An account's id is keyed instead (D5b). A member's id is
`Receive.memberId`, the digest of its join consent. -/
def bornId (E : Env D) (txId : D) (p : Cell × Nat) : D :=
  match p.1.discipline with
  | .rom => romIdOf E p.1
  | _ => cellIdOf E txId p.2

/-- The ids a turn's births carry (explicit in the Turn, D5). -/
def createdIds (t : Turn D) : List D := t.creates.map Prod.fst

/-- The roots digest of four tries, as a head commits it and as every read of it recomputes it: ONE
lazy copy of the empty trie's digest shared by the four (KERNEL-35 at the roots: all four tries hash
the empty tag in `domTrie`, so it is one value), so a roots digest costs at most one hash for its
empty tries. `commitWith`, `commitRefusal` and `World.roots` all take it (cv 01a15107-2272: the
read took each root's `hashOf`, one empty digest per empty trie, on every record check). -/
def rootsOf (E : Env D) (trie : Cells D) (journal : Journal D) (refusals : Refusals D) (rows : Rows D) : D :=
  let e : Thunk D := Thunk.mk fun _ => Trie.emptyHash (trieSpec E)
  rootsDigest E (trie.rootWith (trieSpec E) e) (journal.rootWith (journalSpec E) e)
    (refusals.rootWith (refusalSpec E) e) (rows.rootWith (rowSpec E) e)

namespace World

/-- The chain a World with identity `origin` starts at (KERNEL-24): `H(domGenesis, origin)`. -/
def genesisChain (E : Env D) (origin : D) : D := E.hash domGenesis (E.bytes origin)

/-- What `genesisChain` hashes. -/
def genesisPre (E : Env D) (origin : D) : String × ByteArray := (domGenesis, E.bytes origin)

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
def roots (E : Env D) (w : World D) : D := rootsOf E w.trie w.journal w.refusals w.rows

/-- What `w`'s roots digest hashes. -/
def rootsPre (E : Env D) (w : World D) : String × ByteArray :=
  Nanodregg.Kernel.rootsPre E (w.root E) (w.journalRoot E) (w.refusalsRoot E) (w.rowsRoot E)

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
  | some (.live cell _) => some cell
  | _ => none

/-- Is the id taken (a live cell or a tombstone)? -/
def taken (E : Env D) (w : World D) (c : D) : Bool := (w.entry E c).isSome

/-- The journal entry at a transaction id, if any: its height and turn digest. -/
def journalAt (E : Env D) (w : World D) (k : D) : Option (Nat × D) := w.journal.get (journalSpec E) k

/-- The refusals leaf at a key, if any. -/
def refusalAt (E : Env D) (w : World D) (k : RefusalSlot D) : Option (RefusalLeaf D) :=
  w.refusals.get (refusalSpec E) (.refusal k)

/-- The meter at a key (KERNEL-68): the count the window trie holds at the meter kind's key, if any.
Typed by its kind, as `refusalAt` is by its: the two readers of one trie never name each other's
leaves. -/
def meterAt (E : Env D) (w : World D) (k : MeterSlot D) : Option Nat :=
  match w.refusals.get (refusalSpec E) (.meter k) with
  | some (.count n) => some n
  | _ => none

/-- The chain this World had at step `s` (KERNEL-79): its own chain at its own step count, the ring's
leaf for one of the last `Bounds.pinWindow` steps before it, nothing for any other step. Typed by its
kind, as `refusalAt` and `meterAt` are by theirs. -/
def chainAt [DecidableEq D] (E : Env D) (w : World D) (s : Nat) : Option D :=
  if s = w.steps then some w.chain
  else match w.refusals.get (refusalSpec E) (.chain (.ring w.origin (ringSlot s))) with
    | some (.head s' c) => if s' = s then some c else none
    | _ => none

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

/-- What an entry costs in the World: a live cell its version (a counter, KERNEL-54) and its weight,
a tombstone nothing beyond its id. -/
def _root_.Nanodregg.Kernel.Entry.weight : Entry → Nat
  | .live c _ => counterWeight + c.weight
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

/-- The storage potential's ratio (KERNEL-55), `(numerator, denominator)` = `(84, 145)`. A turn adds
to the World at most `84/61` of its log record (`Turn.growth_le_logWeight`, tight at a pinless declare:
growth 84, log 61), so `145 · weight + 84 · allowance` never rises (`fold_potential`) and the allowance
bounds the World at `84/145` of itself (`allowance_bounds_world`). HOST is to read these two numbers
by name for its World bound (KERNEL-55 part 2, with CODEC's size equality). -/
def potentialRatio : Nat × Nat := (84, 145)

/-- The storage potential of a World (KERNEL-55): `145 · weight + 84 · allowance`. -/
def potential [DecidableEq D] (w : World D) : Nat :=
  potentialRatio.2 * w.weight + potentialRatio.1 * w.allowance

/-- The cell an entry holds (a tombstone holds none). -/
def Entry.cell? : Entry → Option Cell
  | .live c _ => some c
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
  req (t.ticks ≤ Bounds.treeTicksMax) (.overBound .ticks)
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
  -- the causal pin's step count is a `u64` (KERNEL-79)
  req (t.causal.all fun p => decide (p.steps < Bounds.counterLimit)) (.overBound .counter)

variable [DecidableEq D]

/-- A transaction id is admitted at most once; a retry names the height it landed at, and a recorded
refusal is final (`refusedFinal`, KERNEL-44). On the Host's path `Receive.submit` answers both before it
derives (its journal and `refusedAnswer` reads), so these two arms are not reached there; they are
a fold's (`World.fold`: a reopen, and every theorem over a log), which admits a log's Turns with
nothing before them, and are kept for it (KERNEL-67); the follower re-derives through `submit` too. -/
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

/-- The ticks a member's admitted Turns have spent in the window a Turn would land in (height + 1),
read off the meter leaf (DESIGN-OBS §1.3); 0 where there is none. -/
def ticksUsed (E : Env D) (w : World D) (m : D) : Nat :=
  (w.meterAt E (.ticks m (refusalWindow (w.height + 1)))).getD 0

/-- The meter (DESIGN-OBS §1.3): the member's ticks this window, with the Turn's, within
`Bounds.ticksPerWindow`; else `ticksBudget`, naming the member. A Turn with no ticks always passes.
Checked LAST but for the step counter (after the charge and the births): a stale, replayed, unfunded
or malformed call is refused by its own name first, and `ticksBudget` is the last word, as
`overAllowance` is for bytes. -/
def checkTicks (E : Env D) (w : World D) (t : Turn D) : Except (Reject D) Unit :=
  req (ticksUsed E w t.member + t.ticks ≤ Bounds.ticksPerWindow) (.ticksBudget t.member)

/-- The refusals after a checked Turn: the meter leaf bumped by the Turn's ticks when it spent any
(one path per invoke, none for any other Body), then pruned at the window's end with the journal. -/
def commitMeter (E : Env D) (w : World D) (t : Turn D) : Refusals D :=
  if t.ticks = 0 then w.refusals
  else w.refusals.insert (refusalSpec E) (.meter (.ticks t.member (refusalWindow (w.height + 1))))
    (.count (ticksUsed E w t.member + t.ticks))

/-- A causal pin against the World (KERNEL-79): none passes; a pin passes when the World's chain at its
step is the pin's (`chainAt`); otherwise it names the step: `pinAhead` past the World's steps,
`forkedPin` where the World holds another chain there, `pinExpired` where the ring no longer reaches. -/
def checkCausal [DecidableEq D] (E : Env D) (w : World D) : Option (CausalPin D) → Except (Reject D) Unit
  | none => .ok ()
  | some p =>
    if w.steps < p.steps then .error (.pinAhead p.steps)
    else match w.chainAt E p.steps with
      | some c => req (decide (c = p.chain)) (.forkedPin p.steps)
      | none => .error (.pinExpired p.steps)

/-- The ring after a step (KERNEL-79): the chain the World leaves, at the step it leaves, written at
that step's ring position (overwriting the leaf `Bounds.pinWindow` steps older). One path per step. -/
def ringPush (E : Env D) (w : World D) (r : Refusals D) : Refusals D :=
  r.insert (refusalSpec E) (.chain (.ring w.origin (ringSlot w.steps))) (.head w.steps w.chain)

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
the pin is checked against its ENTRY (the one staleness refusal: absent, tombstone and live are three
pins, and a live pin names the version, KERNEL-54), then the act applies to it, and what it frees and
the value it moves are computed from the same lookup. A write bumps the version, refused by name past
`Bounds.counterLimit` (`overBound .version`). -/
def touchCheck (E : Env D) (w : World D) (x : Touch D) : Except (Reject D) (Option (Post D)) := do
  let cur := w.entry E x.cell
  req (pinOf E cur = x.seen) (.stale x.cell)
  match x.act, cur with
  | .keep, _ => pure none
  | .write ops, some (.live cell ver) => do
      req (decide (ver + 1 < Bounds.counterLimit)) (.overBound .version)
      let post ← postWrite x.cell cell ops
      pure (some ⟨x.cell, .live post (ver + 1), cell.weight + (ops.map Op.weight).sum - post.weight,
        flowsOf (some cell) (some post)⟩)
  | .write _, _ => .error (.missingCell x.cell)
  | .retire, some (.live cell _) => do
      req (cell.discipline != .rom) (.romRetire x.cell)
      pure (some ⟨x.cell, .tomb, counterWeight + cell.weight, flowsOf (some cell) none⟩)
  | .retire, _ => .error (.missingCell x.cell)

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
  | .head _ rel, .head count sum limit cap width _ floor =>
      decide (rel < 256) && decide (limit ≤ Bounds.rowsPerRelationMax) && decide (width ≤ Bounds.keyBytesMax) &&
        decide (count ≤ limit) && decide (sum ≤ cap) && decide (cap < Bounds.counterLimit) &&
        decide (floor < Bounds.counterLimit)
  | .row key, .row amt val ver =>
      decide (key.rel < 256) && decide (key.k.size ≤ Bounds.keyBytesMax) && decide (amt < Bounds.counterLimit) &&
        decide (val.size ≤ Bounds.valueBytesMax) && decide (ver < Bounds.counterLimit)
  | _, _ => false

/-- A rows listing: strictly ascending by key bytes, every pair fitting. -/
def rowsFits (E : Env D) (l : List (RowSlot D × RowLeaf)) : Bool :=
  ascendingBytes (l.map fun p => rowKeyBytes E p.1) && l.all fun p => rowFits p.1 p.2

/-- Every row has its head, its key at the head's width, and every head's count and sum are its
rows' (the decode-side twin of `head_sum`). O(listing · heads) over a listing bounded by the limits. -/
def rowsHeaded (l : List (RowSlot D × RowLeaf)) [DecidableEq D] : Bool :=
  let heads := l.filterMap fun p => match p with
    | (.head parent rel, .head count sum _ _ width _ _) => some (parent, rel, count, sum, width)
    | _ => none
  let rowsOf (parent : D) (rel : Nat) := l.filterMap fun p => match p with
    | (.row key, .row amt _ _) => if decide (key.parent = parent) && decide (key.rel = rel) then some (key, amt) else none
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
        | some (.entry (.live _ _)) => true
        | _ => false)
    | .row _ => true

/-! ## Rows admission (KERNEL-46/48): judged on the CURRENT rows, one slot at a time -/

/-- The bits of a rows key, as the path `retainAt` follows to remove it (a retract REMOVES: no
tombstone, KERNEL-46). -/
def rowPath (E : Env D) (s : RowSlot D) : List Bool :=
  (List.range Bounds.rowDepth).map ((rowSpec E).bit s)

/-- The head of a relation, as `(count, sum, limit, cap, width, retract)` (its floor is `headFloor`). -/
def headOf (E : Env D) (r : Rows D) (parent : D) (rel : Nat) :
    Option (Nat × Nat × Nat × Nat × Nat × Bool) :=
  match rowAt E r (.head parent rel) with
  | some (.head count sum limit cap width retract _) => some (count, sum, limit, cap, width, retract)
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

/-- A relation's floor (KERNEL-54), 0 where it has no head: what an absent row's pin and a range
pin name besides the rows. Only a retract raises it. -/
def headFloor (E : Env D) (r : Rows D) (parent : D) (rel : Nat) : Nat :=
  match rowAt E r (.head parent rel) with
  | some (.head _ _ _ _ _ _ floor) => floor
  | _ => 0

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

/-- Write a relation's head with a new count, sum and floor, its declaration unchanged. -/
def setHead (E : Env D) (r : Rows D) (parent : D) (rel count sum limit cap width : Nat) (retract : Bool)
    (floor : Nat) : Rows D :=
  r.insert (rowSpec E) (.head parent rel) (.head count sum limit cap width retract floor)

/-- Where a turn's row touches read and write (cv 01a153a5-0e09): the rows as a `Trie.T` (`trieStore`,
the specification every rows theorem reads) or as the dirty overlay `Trie.U` (`uStore`, what `rowsRun`
runs: a turn's row and head writes hashed once, at the seal). `rowStepOn` is the ONE body of a row touch,
over either; `Kernel.Proofs.Admit.rowStepOn_map`: any map between stores that commutes with the three
operations commutes with it (no premise), so the overlay run sealed is the trie run (`rowsRun_eq`). -/
structure RowStore (D C : Type) where
  get : C → RowSlot D → Option RowLeaf
  ins : C → RowSlot D → RowLeaf → C
  /-- remove a key (`Trie.retainAt` along its `rowPath`) -/
  drop : C → RowSlot D → C

/-- `headOf` on a store. `@[inline]` (cv 01a1545b-1daf): a store is a record of closures over the
runtime `E`, so its uses at `trieStore` and `uStore` compile to direct calls only where the body is
inlined at the instance; a class would not close over `E`. -/
@[inline] def headOfOn {C : Type} (st : RowStore D C) (r : C) (parent : D) (rel : Nat) :
    Option (Nat × Nat × Nat × Nat × Nat × Bool) :=
  match st.get r (.head parent rel) with
  | some (.head count sum limit cap width retract _) => some (count, sum, limit, cap, width, retract)
  | _ => none

/-- `headFloor` on a store (`@[inline]`, as `headOfOn`). -/
@[inline] def headFloorOn {C : Type} (st : RowStore D C) (r : C) (parent : D) (rel : Nat) : Nat :=
  match st.get r (.head parent rel) with
  | some (.head _ _ _ _ _ _ floor) => floor
  | _ => 0

/-- `setHead` on a store (`@[inline]`, as `headOfOn`). -/
@[inline] def setHeadOn {C : Type} (st : RowStore D C) (r : C) (parent : D) (rel count sum limit cap width : Nat)
    (retract : Bool) (floor : Nat) : C :=
  st.ins r (.head parent rel) (.head count sum limit cap width retract floor)

/-- The rows as a trie: `rowAt`, `T.insert`, `retainAt` along the key's path. -/
abbrev trieStore (E : Env D) : RowStore D (Rows D) where
  get r s := rowAt E r s
  ins r k v := r.insert (rowSpec E) k v
  drop r k := Trie.retainAt (rowSpec E) (fun k' _ => decide (k' ≠ k)) (rowPath E k) r

/-- `uStore`'s read, write and removal as named functions (cv 01a1545b-1daf): the record's fields are
these, partly applied to `E`, so a touch inlined at `uStore` calls them directly. A lambda in the record
compiled to a closure the compiler floated out of `rowsRun`'s loop and applied (`lean_apply`), never
called. -/
def uGet (E : Env D) (u : Trie.U (RowSlot D) RowLeaf D) (s : RowSlot D) : Option RowLeaf :=
  Trie.U.getAt (rowSpec E) s 0 u

def uIns (E : Env D) (u : Trie.U (RowSlot D) RowLeaf D) (k : RowSlot D) (v : RowLeaf) :
    Trie.U (RowSlot D) RowLeaf D :=
  Trie.insU (rowSpec E) k v 0 u

def uDrop (E : Env D) (u : Trie.U (RowSlot D) RowLeaf D) (k : RowSlot D) : Trie.U (RowSlot D) RowLeaf D :=
  Trie.retainAtU (rowSpec E) (fun k' _ => decide (k' ≠ k)) (rowPath E k) u

/-- The rows as the dirty overlay (`@[inline]`, as `headOfOn`: `rowsRun`'s calls through it are
direct, `uGet`/`uIns`/`uDrop`): a read walks it (no hash), a write is unhashed (`Trie.insU`), a
removal re-joins the row's path unhashed (`Trie.retainAtU`, cv 01a15460-e096: a retract joins the
batch; before it, the removal sealed what was written and the batch split at every retract). -/
@[inline] def uStore (E : Env D) : RowStore D (Trie.U (RowSlot D) RowLeaf D) where
  get := uGet E
  ins := uIns E
  drop := uDrop E

/-- One row touch, judged on the rows written so far this turn, on any store (`RowStore`) (slots are distinct, so a row's pin
is judged against the pre-state; a head's count and sum accumulate: the head update is additive,
never pinned, KERNEL-46 amendment 3). The parent must be pinned by the turn (`rowParentUnpinned`)
and live (`orphanRow`), or, for `declare`, born by it (`declareLate`).
Versions (KERNEL-54): an absent row's pin names its relation's floor IN THE WORLD BEFORE THE TURN
(`w.rows`: an earlier retract of the same turn raises the floor in `r`, and must not stale a later
pin of the same turn); an insert takes the floor as its version (inserts leave the floor alone, so two
turns' inserts commute); an upsert bumps the row's version; a retract raises the floor past the
version of the row it removes. Each refused by name past `Bounds.counterLimit` (`overBound .version`). -/
@[inline] def rowStepOn {C : Type} (st : RowStore D C) (E : Env D) (w : World D) (t : Turn D) (r : C)
    (x : RowTouch D) : Except (Reject D) C := do
  match x.slot, x.act with
  | .head p rel, .declare limit cap width retract => do
      req (decide (rel < 256)) (.overBound .rows)
      -- a declare reads nothing, so it carries no pin (one encoding per effect)
      req x.seen.isNone (.rowShape p)
      req ((createdIds t).contains p) (.declareLate p)
      req (decide (limit ≤ Bounds.rowsPerRelationMax) && decide (width ≤ Bounds.keyBytesMax) &&
        decide (cap < Bounds.counterLimit)) (.overBound .rows)
      req (st.get r (.head p rel)).isNone (.keyTaken p)
      pure (setHeadOn st r p rel 0 0 limit cap width retract 0)
  | .head p _, _ => .error (.rowShape p)
  | .row key, act => do
      let p := key.parent
      req (t.touches.any fun x => decide (x.cell = p)) (.rowParentUnpinned p)
      req (w.live E p).isSome (.orphanRow p)
      -- a parent the turn retires takes no row: its heads go with it (`dropHeads`)
      req (!(t.touches.any fun x => decide (x.cell = p) && decide (x.act = .retire))) (.orphanRow p)
      match headOfOn st r p key.rel with
      | none => .error (.noRelation p)
      | some (count, sum, limit, cap, width, retract) => do
          req (decide (key.k.size = width)) (.keyWidth p)
          let cur := st.get r (.row key)
          let floor := headFloorOn st r p key.rel
          let pinned : Except (Reject D) Unit :=
            match x.seen with
            | some s => req (decide (rowPin E (headFloor E w.rows p key.rel) cur = s)) (.stale p)
            | none => .error (.rowShape p)
          match act with
          | .keep => do pinned; pure r
          | .insert amt v => do
              req x.seen.isNone (.rowShape p)
              req cur.isNone (.keyTaken p)
              req (decide (count < limit)) (.relationFull p)
              req (decide (sum + amt ≤ cap)) (.relationCapped p)
              req (decide (v.size ≤ Bounds.valueBytesMax)) (.overBound .valueBytes)
              pure (setHeadOn st (st.ins r (.row key) (.row amt v floor)) p key.rel (count + 1)
                (sum + amt) limit cap width retract floor)
          | .upsert amt v => do
              pinned
              req (decide (v.size ≤ Bounds.valueBytesMax)) (.overBound .valueBytes)
              let old := match cur with | some (.row a _ _) => a | _ => 0
              let ver := match cur with | some (.row _ _ u) => u + 1 | _ => floor
              req (decide (ver < Bounds.counterLimit)) (.overBound .version)
              let fresh := cur.isNone
              req (!fresh || decide (count < limit)) (.relationFull p)
              req (decide (sum - old + amt ≤ cap)) (.relationCapped p)
              pure (setHeadOn st (st.ins r (.row key) (.row amt v ver)) p key.rel
                (if fresh then count + 1 else count) (sum - old + amt) limit cap width retract floor)
          | .retract => do
              pinned
              req retract (.retractForbidden p)
              match cur with
              | some (.row a _ u) => do
                  req (decide (max floor u + 1 < Bounds.counterLimit)) (.overBound .version)
                  pure (setHeadOn st (st.drop r (.row key)) p key.rel (count - 1) (sum - a) limit cap width retract
                    (max floor u + 1))
              | _ => .error (.missingRow p)
          | .declare .. => .error (.rowShape p)

/-- One row touch on the rows as a trie: `rowStepOn` at `trieStore`, what every rows theorem reads. -/
def rowStep (E : Env D) (w : World D) (t : Turn D) (r : Rows D) (x : RowTouch D) : Except (Reject D) (Rows D) :=
  rowStepOn (trieStore E) E w t r x

/-- What a row touch gives back of its growth, judged on the rows before it: an upsert or a
retract the entry it replaces or removes (with its key); nothing otherwise. -/
def rowFreedOn {C : Type} (st : RowStore D C) (r : C) (x : RowTouch D) : Nat :=
  match x.act with
  | .upsert .. | .retract => ((st.get r x.slot).map fun l => rowEntryWeight (x.slot, l)).getD 0
  | _ => 0

/-- `rowFreedOn` on the rows as a trie. -/
def rowFreed (E : Env D) (r : Rows D) (x : RowTouch D) : Nat := rowFreedOn (trieStore E) r x

/-- One row touch with what it gives back, accumulated, on any store. -/
@[inline] def rowStepFreedOn {C : Type} (st : RowStore D C) (E : Env D) (w : World D) (t : Turn D) (acc : C × Nat)
    (x : RowTouch D) : Except (Reject D) (C × Nat) := do
  let r ← rowStepOn st E w t acc.1 x
  pure (r, acc.2 + rowFreedOn st acc.1 x)

/-- `rowStepFreedOn` on the rows as a trie. -/
def rowStepFreed (E : Env D) (w : World D) (t : Turn D) (acc : Rows D × Nat)
    (x : RowTouch D) : Except (Reject D) (Rows D × Nat) :=
  rowStepFreedOn (trieStore E) E w t acc x

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

/-- Head removals join the rows batch; on canonical rows, the prefix walk and retains hash nothing.
Sealing this result is exactly dropHeads of the sealed input, including freed weight. -/
def dropHeadsU (E : Env D) (t : Turn D) (acc : Trie.U (RowSlot D) RowLeaf D × Nat) :
    Trie.U (RowSlot D) RowLeaf D × Nat :=
  t.touches.foldl (fun acc x => match x.act with
    | .retire =>
        ((underU (rowSpec E) (E.bytes x.cell) 257 acc.1).filter fun p => match p.1 with
          | .head q _ => decide (q = x.cell)
          | .row _ => false).foldl (fun acc p =>
            (Trie.retainAtU (rowSpec E) (fun k _ => decide (k ≠ p.1)) (rowPath E p.1) acc.1,
              acc.2 + rowEntryWeight p)) acc
    | _ => acc) acc

/-- Every row touch, in order, from the World's rows; slots distinct (`duplicateRow`). Returns the
rows after the turn and the storage its row touches give back (`rowFreed`, summed). The touches run on
the dirty overlay (`uStore`, cv 01a153a5-0e09), sealed once after the retired parents' heads leave: a
node the turn's row and head writes and its retracts' re-joins share is hashed once (a retract joins
the batch since cv 01a15460-e096). The same rows as each touch on the trie in
turn (`Kernel.Proofs.Admit.rowsRun_eq`, no premise), which the proofs read. -/
def rowsRun (E : Env D) (w : World D) (t : Turn D) :
    Except (Reject D) (Rows D × Nat) := do
  req (decide (t.rows.length ≤ Bounds.rowsMax) && decide (t.ranges.length ≤ Bounds.rangesMax)) (.overBound .rows)
  req (t.rows.all fun x => match x.slot with
    | .row key => decide (key.rel < 256) && decide (key.k.size ≤ Bounds.keyBytesMax)
    | .head _ rel => decide (rel < 256)) (.overBound .rows)
  match t.rows.find? (fun x => decide (1 < (t.rows.filter fun y => decide (y.slot = x.slot)).length)) with
  | some x => .error (.duplicateRow (match x.slot with | .head p _ => p | .row k => k.parent))
  | none => do
      -- a saturated call, so the `@[inline]` touch body is inlined here at `uStore` (cv 01a1545b-1daf:
      -- passed as a value, `rowStepFreedOn (uStore E) E w t` compiled to the generic body and every
      -- store call to `lean_apply`)
      let acc ← t.rows.foldlM (fun acc x => rowStepFreedOn (uStore E) E w t acc x) (.clean w.rows, 0)
      let acc := dropHeadsU E t acc
      pure (acc.1.seal (rowSpec E), acc.2)

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
        | some l => req (decide (rangePin E q.parent q.rel width q.pre (headFloor E w.rows q.parent q.rel) l =
            q.seen)) (.stale q.parent))
    t.ranges

/-- The pins a signed call carries, against `w`, BEFORE anything is derived from it (KERNEL-66):
each cell pin against its cell's entry (`touchCheck`'s comparison), each row pin against its row and
its relation's floor (`rowStep`'s), each range read against its listing where the relation has a head
and the listing fits its `most` (`checkRanges`'s). The first that disagrees is `stale`, naming the cell
or the parent as admission names it: these are exactly the three disagreements
`Kernel.Proofs.StaleOnly.admit_stale_pin` says a `stale` refusal of admission is. A head pin, a range on
a relation with no head and a listing past its `most` are not disagreements of a pin with the World
(admission refuses them `rowShape`, `noRelation`, `rangeTooLong`), so they pass here. -/
def checkPins (E : Env D) (w : World D) (pins : List (D × D)) (rowPins : List (RowSlot D × D))
    (ranges : List (RangeRead D)) : Except (Reject D) Unit := do
  forEx (fun p => req (decide (pinOf E (w.entry E p.1) = p.2)) (.stale p.1)) pins
  forEx (fun p => match p.1 with
    | .row key => req (decide (rowPin E (headFloor E w.rows key.parent key.rel) (rowAt E w.rows (.row key)) = p.2))
        (.stale key.parent)
    | .head .. => .ok ()) rowPins
  forEx (fun q => match headOf E w.rows q.parent q.rel with
    | none => .ok ()
    | some (_, _, _, _, width, _) =>
        match rangeRows E w.rows q.parent q.rel width q.pre q.most with
        | none => .ok ()
        | some l => req (decide (rangePin E q.parent q.rel width q.pre (headFloor E w.rows q.parent q.rel) l =
            q.seen)) (.stale q.parent)) ranges

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
  checkCausal E w t.causal
  let posts := (← mapEx (touchCheck E w) t.touches).reduceOption
  checkValue E t posts
  checkNullifiers E w t
  checkRowsRemain E w t
  checkRanges E w t
  let rr ← rowsRun E w t
  checkCharge w t (credit posts + rr.2)
  checkCreates E w t
  checkTicks E w t
  checkSteps w
  pure (posts, rr)

/-- Every check, against the pre-state only; on success, what the touches leave behind. -/
def check (E : Env D) (w : World D) (t : Turn D) : Except (Reject D) (List (Post D)) :=
  (checkWith E w t).map Prod.fst

def bornEntries (t : Turn D) : List (D × Entry) :=
  t.creates.map fun p => (p.1, .live p.2 0)

/-- Write cell entries into the map, each key in turn, one path each: the proofs' shape of
`commitTrie` (`Kernel.Proofs.Admit.commitTrie_eq`), and the genesis founders' write. -/
def insertAll (E : Env D) (m : Cells D) (ps : List (D × Entry)) : Cells D :=
  ps.foldl (fun m p => m.insert (trieSpec E) (.cell p.1) (.entry p.2)) m

/-- Mark nullifiers spent, each in turn, one path each: the proofs' shape of `commitTrie`. -/
def spendAll (E : Env D) (m : Cells D) (ns : List D) : Cells D :=
  ns.foldl (fun m n => m.insert (trieSpec E) (.nullifier n) .spent) m

/-- The map after a checked turn: its touches' entries, its born cells, its nullifiers, ONE batch on
the dirty overlay (`Trie.insertAll`, cv 01a15107-2281): a node several of the turn's keys pass through
is hashed once, not once per key. The same trie as writing each in turn, `spendAll` over `insertAll`
over `insertAll` (`Kernel.Proofs.Admit.commitTrie_eq`, no premise), which the proofs read. No path
reads an empty digest (no node has an empty child, KERNEL-49 (a)); only an empty ROOT does, in
`commitWith` (`T.rootWith`, one lazy copy shared by the four roots). -/
def commitTrie (E : Env D) (w : World D) (t : Turn D) (posts : List (Post D)) : Cells D :=
  Trie.insertAll (trieSpec E) w.trie
    ((posts.map Post.pair ++ bornEntries t).map (fun p => (.cell p.1, .entry p.2)) ++
      t.nullifiers.map fun n => (.nullifier n, .spent))


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
`Bounds.refusalsPerWindow`, a total of the current window between 1 and `Bounds.refusalsPerWindowMax`,
every counter below `2^64`, and no other pairing. -/
def refusalFits (height : Nat) : WindowSlot D → RefusalLeaf D → Bool
  | .refusal (.tx _), .refused h code _ => decide (1 ≤ h ∧ h ≤ height + 1 ∧
      height < h + 2 * Bounds.windowMax + height % Bounds.windowMax ∧ h < Bounds.counterLimit ∧
      code < Bounds.counterLimit)
  | .refusal (.count _ win), .count n =>
      decide (win = refusalWindow height ∧ 1 ≤ n ∧ n ≤ Bounds.refusalsPerWindow)
  | .refusal (.total _ win), .count n =>
      decide (win = refusalWindow height ∧ 1 ≤ n ∧ n ≤ Bounds.refusalsPerWindowMax)
  | .meter (.ticks _ win), .count n => decide (win = refusalWindow height ∧ 1 ≤ n ∧ n ≤ Bounds.ticksPerWindow)
  | .chain (.ring _ j), .head s _ => decide (s < Bounds.counterLimit ∧ j = ringSlot s)
  | _, _ => false

/-- A refusals listing a World at `height` can hold (KERNEL-47; the twin of `journalFits`, for CODEC's
`kernel/refusals` refusal): every key holds the leaf of its kind; a refused call was refused at a
height at most `height + 1` (the World's height when it was recorded, plus one) and is not yet due
for pruning; a count is for the current window and between 1 and `Bounds.refusalsPerWindow`; every
counter below `2^64`. It holds of every World a fold reaches (`fold_refusalsOk`), so a decoded base
is refused unless it holds. One pass. -/
def refusalsFits (height : Nat) (l : List (WindowSlot D × RefusalLeaf D)) : Bool :=
  l.all fun p => refusalFits height p.1 p.2

/-- No transaction id is both recorded refused and journaled (KERNEL-47; CODEC-8's ask): a fold never
reaches such a World (`fold_refusalsDisjoint`), so a decoded base is refused unless it holds. One
journal lookup per recorded refusal. -/
def refusalsDisjoint (E : Env D) (w : World D) : Bool :=
  w.refusals.toList.all fun p => match p.1, p.2 with
    | .refusal (.tx id), .refused _ _ _ => (w.journalAt E id).isNone
    | _, _ => true

/-- The journal after a checked turn: the turn's entry inserted at the new height, then pruned if
that height is a multiple of `Bounds.windowMax`. -/
def commitJournal (E : Env D) (w : World D) (t : Turn D) : Journal D :=
  pruneJournal E (w.height + 1) (w.journal.insert (journalSpec E) t.txId (w.height + 1, turnDigest E t))

/-- Is a refusals leaf still kept at height `H` (KERNEL-44, KERNEL-47 amendment 5)? A refused call's
leaf while `kept` (KERNEL-33's rule: it was refused at `h` inside its window, so it outlives every
height it could be admitted at); a count or a total only for the current window. -/
def keptRefusal (H : Nat) : WindowSlot D → RefusalLeaf D → Bool
  | .chain _, _ => true
  | .refusal (.count _ win), _ => decide (win = refusalWindow H)
  | .refusal (.total _ win), _ => decide (win = refusalWindow H)
  | .meter (.ticks _ win), _ => decide (win = refusalWindow H)
  | _, .refused h _ _ => decide (H < h + 2 * Bounds.windowMax)
  | _, .count _ => false
  | _, .head _ _ => false

/-- The refusals at height `H`: pruned with the journal, at every multiple of `Bounds.windowMax`, by
the same canonical `Trie.retainAt`; unchanged between multiples. -/
def pruneRefusals (E : Env D) (H : Nat) (r : Refusals D) : Refusals D :=
  if H % Bounds.windowMax = 0 then Trie.retainAt (refusalSpec E) (keptRefusal H) [] r else r

/-- The World after a checked turn, given the rows `rowsRun` reached (`rr`). Total: everything that
can fail failed in `checkWith`. -/
def commitWith (E : Env D) (w : World D) (t : Turn D) (posts : List (Post D)) (rr : Rows D × Nat) : World D :=
  let trie := commitTrie E w t posts
  let journal := commitJournal E w t
  let refusals := ringPush E w (pruneRefusals E (w.height + 1) (commitMeter E w t))
  let rows := rr.1
  { trie
    journal
    refusals
    rows
    height := w.height + 1
    steps := w.steps + 1
    chain := chainNext E w.chain t (rootsOf E trie journal refusals rows)
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
  obtain ⟨⟨⟩, -, ⟨⟩, -, ⟨⟩, -, ⟨⟩, -, ⟨⟩, -, raw, -, ⟨⟩, -, ⟨⟩, -, ⟨⟩, -, ⟨⟩, -, rr', hrw, ⟨⟩, -,
    ⟨⟩, -, ⟨⟩, -, ⟨⟩, -, h9⟩ := h
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
  -- a cancel's signature (KERNEL-60): bounded, so `refusedBytes`' length prefix is injective
  req (r.cancel.size ≤ Bounds.cancelBytesMax) (.overBound .event)

/-- A member's recorded refusals in the window of the World's current height. -/
def refusalCount (E : Env D) (w : World D) (m : D) : Nat :=
  match w.refusalAt E (.count m (refusalWindow w.height)) with
  | some (.count n) => n
  | _ => 0

/-- The World's recorded refusals in the window of its current height, all members together (KERNEL-55 R1). -/
def refusalTotal (E : Env D) (w : World D) : Nat :=
  match w.refusalAt E (.total w.origin (refusalWindow w.height)) with
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
def refusedOne : WindowSlot D × RefusalLeaf D → Nat
  | (.refusal (.tx _), .refused _ _ _) => 1
  | _ => 0

/-- 1 at a refusal of `m` recorded in the window of height `H`, else 0. A leaf holds `h`, the height
its World had plus one, so it was recorded in window `(h - 1) / windowMax`. -/
def refusedIn [DecidableEq D] (H : Nat) (m : D) : WindowSlot D × RefusalLeaf D → Nat
  | (.refusal (.tx _), .refused h _ m') =>
      if m' = m ∧ (h - 1) / Bounds.windowMax = H / Bounds.windowMax then 1 else 0
  | _ => 0

/-- 1 at a member's window-count key, else 0 (KERNEL-55 R1: what the refusals bound counts). -/
def countKeyOne : WindowSlot D × RefusalLeaf D → Nat
  | (.refusal (.count _ _), _) => 1
  | _ => 0

/-- 1 at a window-total key, else 0 (KERNEL-55 R1). -/
def totalKeyOne : WindowSlot D × RefusalLeaf D → Nat
  | (.refusal (.total _ _), _) => 1
  | _ => 0

/-- 1 at a meter key, else 0 (KERNEL-68): what bounds the window trie's meter leaves. -/
def meterKeyOne : WindowSlot D × RefusalLeaf D → Nat
  | (.meter _, _) => 1
  | _ => 0

/-- 1 at a ring key, else 0 (KERNEL-79): what bounds the window trie's ring of recent heads. -/
def chainKeyOne : WindowSlot D × RefusalLeaf D → Nat
  | (.chain _, _) => 1
  | _ => 0

/-- 1 at a refusal recorded in window `k` (any member), else 0 (KERNEL-55 R1). -/
def refusedWin (k : Nat) : WindowSlot D × RefusalLeaf D → Nat
  | (.refusal (.tx _), .refused h _ _) => if (h - 1) / Bounds.windowMax = k then 1 else 0
  | _ => 0

/-- The map `refusalTally` counts in: the refusals' routing (so a lookup is one path), and no hash,
no bytes (nothing reads its digests; `get` after `insert` is exact for any `Spec`). -/
def tallySpec (E : Env D) (seed : D) : Trie.Spec (WindowSlot D) (RefusalLeaf D) D where
  bit := (refusalSpec E).bit
  depth := (refusalSpec E).depth
  depth_lt := (refusalSpec E).depth_lt
  hash := fun _ => seed
  dbytes := fun _ => ByteArray.empty
  kbytes := fun _ => ByteArray.empty
  vdigest := fun _ => seed

/-- The count a tally holds at a key (0 where it holds none). -/
def tallyAt [DecidableEq D] (E : Env D) (seed : D) (t : Refusals D) (k : RefusalSlot D) : Nat :=
  match t.get (tallySpec E seed) (.refusal k) with
  | some (.count n) => n
  | _ => 0

/-- One listed entry into the tally: a record of window `H / windowMax` bumps its member's count. -/
def tallyStep [DecidableEq D] (E : Env D) (seed : D) (H : Nat) (t : Refusals D)
    (p : WindowSlot D × RefusalLeaf D) : Refusals D :=
  match p with
  | (.refusal (.tx _), .refused h _ m) =>
      if (h - 1) / Bounds.windowMax = H / Bounds.windowMax then
        t.insert (tallySpec E seed) (.refusal (.count m (refusalWindow H)))
          (.count (tallyAt E seed t (.count m (refusalWindow H)) + 1))
      else t
  | _ => t

/-- Each member's records in the window of height `H`, counted from a listing: one pass, one path
per record, no hash. -/
def refusalTally [DecidableEq D] (E : Env D) (seed : D) (H : Nat) (l : List (WindowSlot D × RefusalLeaf D)) :
    Refusals D :=
  l.foldl (tallyStep E seed H) .empty

/-- **A World's refusal counts are its records'** (KERNEL-50): every record cost a step that did not
raise the height (records + height ≤ steps); every count leaf is the tally of its member's records
this window; and every member with a record this window has a count leaf. KERNEL-55 R1: the total
leaf is at `(origin, the current window)` and holds the window's records, all members together, and
it is present when one is; the two windows before hold at most `Bounds.refusalsPerWindowMax` records
each (the current one is bounded by its total, `refusalFits`), so the refusals trie's size is bounded
by the check alone (`refusals_bounded`). Below window 2 the two clauses truncate (`j - 1`, `j - 2` in
`Nat`) and re-read window 0 (or `j - 1`), which the total or the other clause already bounds; no
record can be of a window outside the three (`refusal_window_range`), so nothing is dropped. KERNEL-68: the
meter leaves are at most one more than the heights elapsed in the current window (`height % windowMax + 1`:
one Turn lands per height and writes at most one meter leaf; the window's start prunes the rest), so the
trie's size stays bounded with the meter in it (`refusals_bounded`). KERNEL-79: every ring key is
under the World's origin (a ring position is below `Bounds.pinWindow` by `refusalFits`), so the ring
holds at most `pinWindow` leaves. One pass to tally, one
pass over the listing, one lookup per entry. CODEC's `kernel/refusals-counted` refusal. -/
def refusalsCounted [DecidableEq D] (E : Env D) (w : World D) : Bool :=
  let l := w.refusals.toList
  let tally := refusalTally E w.chain w.height l
  let j := w.height / Bounds.windowMax
  let now := (l.map (refusedWin j)).sum
  decide ((l.map refusedOne).sum + w.height ≤ w.steps) &&
    decide ((l.map (refusedWin (j - 1))).sum ≤ Bounds.refusalsPerWindowMax ∧
      (l.map (refusedWin (j - 2))).sum ≤ Bounds.refusalsPerWindowMax) &&
    (l.all fun p => match p with
      | (.refusal (.count m win), .count n) =>
          decide (tally.get (tallySpec E w.chain) (.refusal (.count m win)) = some (.count n))
      | (.refusal (.total o win), .count n) => decide (o = w.origin ∧ win = refusalWindow w.height ∧ n = now)
      -- a meter leaf (KERNEL-68): the Turns that summed it are not in this trie, so the state check
      -- cannot re-tally it (the fold theorem is its truth; a received base trusts it as it trusts
      -- every cell); `refusalFits` bounds its value and window
      | (.meter _, _) => true
      -- a ring leaf (KERNEL-79): under the World's origin, so the ring has one key per position
      | (.chain (.ring o _), _) => decide (o = w.origin)
      | (.refusal (.tx _), .refused h _ m) =>
          !decide ((h - 1) / Bounds.windowMax = j) ||
            ((w.refusalAt E (.count m (refusalWindow w.height))).isSome &&
              (w.refusalAt E (.total w.origin (refusalWindow w.height))).isSome)
      | _ => true) &&
    decide ((l.map meterKeyOne).sum ≤ w.height % Bounds.windowMax + 1)

/-- Every check a refusal record must pass, against the pre-state (KERNEL-44, KERNEL-47): bounded;
the step counter below `2^64`; the call's window contains the height it would be admitted at (an
early call's refusal is not final and is not recorded, a late call's is final by height); the
transaction id neither journaled (`replayed`) nor already recorded (`refusedFinal`); the member's
count this window below `Bounds.refusalsPerWindow` (`refusalBudget`); the World's count this
window, all members together, below `Bounds.refusalsPerWindowMax` (`refusalsFull`, KERNEL-55 R1). Whether the call was
authenticated and refused with this code is the receive layer's (`Receive.judge`), re-derived by the
follower (`Receive.rederive`); the kernel bounds what a log may record. -/
def checkRefusal (E : Env D) (w : World D) (r : Refused D) : Except (Reject D) Unit := do
  checkRefusedBounds r
  checkSteps w
  req (r.notBefore ≤ w.height + 1 && w.height + 1 ≤ r.validUntil) .outsideWindow
  match w.journalAt E r.txId with
  | some (h, _) => .error (.replayed h)
  | none =>
      match w.refusalAt E (.tx r.txId) with
      | some (.refused _ code _) => .error (.refusedFinal code)
      | _ => do
          req (refusalCount E w r.member < Bounds.refusalsPerWindow) .refusalBudget
          req (refusalTotal E w < Bounds.refusalsPerWindowMax) .refusalsFull

/-- The refusals after a checked refusal: its leaf at the transaction id, the member's count bumped,
the World's total bumped. Three paths, one batch on the dirty overlay (`Trie.insertAll`, cv
01a15107-2281: the nodes the three paths share are hashed once); the same trie as the three inserts in
turn (`Kernel.Proofs.Refuse.commitRefusal_refusals`). -/
def commitRefusals (E : Env D) (w : World D) (r : Refused D) : Refusals D :=
  Trie.insertAll (refusalSpec E) w.refusals
    [(.refusal (.tx r.txId), .refused (w.height + 1) r.code r.member),
     (.refusal (.count r.member (refusalWindow w.height)), .count (refusalCount E w r.member + 1)),
     (.refusal (.total w.origin (refusalWindow w.height)), .count (refusalTotal E w + 1))]

/-- The World after a checked refusal: only the refusals, the step counter and the chain move. The
cells, the journal, the height and the allowance are untouched (`refuse_frame`). -/
def commitRefusal (E : Env D) (w : World D) (r : Refused D) : World D :=
  let refusals := ringPush E w (commitRefusals E w r)
  { w with
    refusals
    steps := w.steps + 1
    chain := refusalLink E w.chain r (rootsOf E w.trie w.journal refusals w.rows) }

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

/-! ## What a chain compares: the inputs each digest along a log takes (KERNEL-56) -/

omit [Ord D] [DecidableEq D] in
/-- A step's kind byte in its head link (a Turn 0, a recorded refusal 1). -/
def Step.tag : Step D → UInt8
  | .turn _ => 0
  | .refusal _ => 1

omit [Ord D] [DecidableEq D] in
/-- A step's digest in its head link. -/
def stepDigest (E : Env D) : Step D → D
  | .turn t => turnDigest E t
  | .refusal r => refusedDigest E r

omit [Ord D] [DecidableEq D] in
/-- What a step's digest hashes. -/
def stepPre (E : Env D) : Step D → String × ByteArray
  | .turn t => (domTurn, E.turnBytes t)
  | .refusal r => refusedPre E r

omit [Ord D] [DecidableEq D] in
/-- What the link a step adds to the chain `c` hashes. -/
def stepLinkPre (E : Env D) (c : D) (s : Step D) (rs : D) : String × ByteArray :=
  linkPre E c s.tag (stepDigest E s) rs

omit [Ord D] [DecidableEq D] in
/-- The inputs one chain step compares: its link's and its step digest's. -/
def stepPres (E : Env D) (c : D) (s : Step D) (rs : D) : List (String × ByteArray) :=
  [stepLinkPre E c s rs, stepPre E s]

omit [Ord D] [DecidableEq D] in
/-- The inputs a chain compares along a log from `c`: each step's (`stepPres`). -/
def chainPres (E : Env D) (c : D) : List (Step D × D) → List (String × ByteArray)
  | [] => []
  | (s, r) :: rest => stepPres E c s r ++ chainPres E (stepLink E c s r) rest

/-- The inputs the chain of a log compares, as `World.fold` runs it from `w`: each step's link and
step digest (`stepPres`), over the roots digest the step left. -/
def foldPres (E : Env D) : World D → List (Step D) → List (String × ByteArray)
  | _, [] => []
  | w, s :: rest =>
      match World.step E w s with
      | .ok w' => stepPres E w.chain s (w'.roots E) ++ foldPres E w' rest
      | .error _ => []

/-- The links a log adds to the chain, as `World.fold` runs it from `w` (`stepLinkPre`). -/
def foldLinks (E : Env D) : World D → List (Step D) → List (String × ByteArray)
  | _, [] => []
  | w, s :: rest =>
      match World.step E w s with
      | .ok w' => stepLinkPre E w.chain s (w'.roots E) :: foldLinks E w' rest
      | .error _ => []

/-- **What opening a head record compares** (`head_roots`, `fold_head_roots`): the record's link
input and roots input, the roots input of the World `w₂` the steps `l` reach from `w`, and the links
`l` adds to the chain (`foldLinks`). -/
def headPres (E : Env D) (w : World D) (l : List (Step D)) (w₂ : World D) (prev : D) (g : UInt8)
    (td rd root' jroot' rroot' wroot' : D) : List (String × ByteArray) :=
  linkPre E prev g td rd :: rootsPre E root' jroot' rroot' wroot' :: w₂.rootsPre E :: foldLinks E w l

/-- What a log carries of a step for a follower to re-derive it from (`Receive.rederive`): the
signed call's bytes, and for a recorded cancel the member's signature. A page writes it behind a
tag (`Protocol.eventBytes`); the writer's own record is not on it. -/
inductive Event
  /-- an admitted Turn: its call -/
  | turn (call : ByteArray)
  /-- a judged refusal: its call -/
  | refusal (call : ByteArray)
  /-- a member's cancel (KERNEL-60): its signature and the cancelled call -/
  | cancel (sig call : ByteArray)
  deriving DecidableEq

/-- A step's event: a recorded refusal is a cancel exactly when it carries a cancel signature (the
FIELD, never the code: a program refusal spelled `cancelled` is judged). The one place a step's
kind of re-derivation is decided. -/
def Step.event {D : Type} : Step D → Event
  | .turn t => .turn t.event
  | .refusal r => if r.cancel.size = 0 then .refusal r.event else .cancel r.cancel r.event

end Nanodregg.Kernel
