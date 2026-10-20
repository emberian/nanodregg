import Codec.Kernel

/-!
# Codec.World — the canonical bytes of a whole World (the checkpoint, HOST-14's base)

`trie ‖ journal ‖ refusals ‖ rows ‖ height u64 ‖ steps u64 ‖ chain ‖ allowance u64 ‖ origin`. The World's four maps are tries
(KERNEL-23 cells and spent nullifiers; KERNEL-41 the journal, under `journalSpec`; KERNEL-44 the
refusals, under `refusalSpec`; KERNEL-48 the rows, under `rowSpec`), and each is written
as its listing (`Trie.T.toList`, left to right by key bits) and read back by `Trie.build` over that
listing (`listingAccept`): every node hash is recomputed, none is ever read from the wire (CODEC-19), and
a listing is refused by name unless it is exactly the rebuilt trie's own (no key twice in a leaf).
The cells' listing is refused `kernel/leaf-fit` unless every slot holds the leaf of its kind, and
`kernel/trie-order` unless it is the canonical trie's; the journal's is refused
`kernel/journal-order` unless it is the canonical journal trie's (at the deployed digest: strictly
ascending by transaction id, `Codec.Deployed.journalOrder_iff`); the refusals' `kernel/refusal-order`
likewise. So every map reads back EXACTLY
(`build_toList`), decode ∘ bytes is the identity (`world_lawfulOn`), and the bytes are a function of
the contents. The World is refused `kernel/journal` unless its journal is the window's (KERNEL-39's
`journalFits`, every entry at or below the height and inside the window, one entry per height), so a
decoded base carries `World.JournalOk` (`world_decode_journalOk`); `kernel/refusals` unless its refusals
are the window's (KERNEL-47's `refusalsFits`), so it carries `World.RefusalsOk`
(`world_decode_refusalsOk`); `kernel/steps` unless its height is at most its step count; and
`kernel/rows` / `kernel/rows-headed` / `kernel/rows-parented` unless its rows fit, every head counts its
rows and every relation's parent is live (KERNEL-48).
`world.size w` is the encoded length, computed from the entries without encoding (HOST's
`worldBytesMax`).
-/

namespace Nanodregg.Codec.Kernel

open Nanodregg.Kernel Nanodregg.Codec.Stream

variable {D : Type} [Ord D]

abbrev EntryF : Fin 2 → Type
  | 0 => Nat × Cell
  | 1 => Unit

def entryWire : (s : Fin 2) → Stream (EntryF s)
  | 0 => product varint64 cell
  | 1 => unit

/-- A cell entry on the World wire: live (0) with its version (a u64 varint, KERNEL-54: one byte below
128 writes, at most ten) then its cell, or a tombstone (1). The order is `leafBytes`'s (kind, version,
cell); the leaf's hash preimage writes the version as eight bytes. -/
def entry : Stream Entry :=
  refine "kernel/entry" (choice 2 entryWire)
    (fun | ⟨0, (v, c)⟩ => some (.live c v) | ⟨1, ()⟩ => some .tomb)
    (fun | .live c v => ⟨0, (v, c)⟩ | .tomb => ⟨1, ()⟩)

/-- A trie key: its kind (0 cell, 1 nullifier, as in `slotBytes`), then the id. -/
def slot (dc : Stream D) : Stream (Slot D) :=
  refine "kernel/slot" (choice 2 fun _ => dc)
    (fun | ⟨0, c⟩ => some (.cell c) | ⟨1, n⟩ => some (.nullifier n))
    (fun | .cell c => ⟨0, c⟩ | .nullifier n => ⟨1, n⟩)

abbrev LeafF : Fin 2 → Type
  | 0 => Entry
  | 1 => Unit

def leafWire : (s : Fin 2) → Stream (LeafF s)
  | 0 => entry
  | 1 => unit

def leaf : Stream Leaf :=
  refine "kernel/leaf" (choice 2 leafWire)
    (fun | ⟨0, e⟩ => some (.entry e) | ⟨1, ()⟩ => some .spent)
    (fun | .entry e => ⟨0, e⟩ | .spent => ⟨1, ()⟩)

/-- The most entries one map of a World holds on the wire. -/
def worldMax : Nat := 2 ^ 32 - 1

/-- Does every leaf hold each key once? (Above `depth` a leaf holds one entry; at `depth`, keys
whose bits all agree, which for the deployed fixed-width ids means one key.) -/
def leavesNodup {K V D' : Type} [DecidableEq K] : Trie.T K V D' → Bool
  | .empty => true
  | .leaf _ kvs => decide (kvs.map Prod.fst).Nodup
  | .node _ _ _ l r => leavesNodup l && leavesNodup r

/-- The trie's listing, each slot holding the leaf of its kind. -/
def fitList [DecidableEq D] (dc : Stream D) : Stream (List (Slot D × Leaf)) :=
  refine "kernel/leaf-fit" (rawList worldMax (product (slot dc) leaf))
    (fun l => if l.all (fun p => Leaf.fits p.1 p.2) then some l else none) id

/-- What a trie-listing refinement accepts: the trie `build` makes of the listing, if that trie lists
exactly the listing back (the same entries in the same order) and no leaf holds a key twice. The cells'
`kernel/trie-order` and the journal's `kernel/journal-order` are both `refine name c (listingAccept S)
Trie.T.toList`: one accept function, two named sites. -/
def listingAccept {K V : Type} [DecidableEq K] [DecidableEq V] (S : Trie.Spec K V D) (l : List (K × V)) :
    Option (Trie.T K V D) :=
  let t := Trie.build S S.depth 0 l
  if t.toList == l && leavesNodup t then some t else none

/-! ## A trie's proof (KERNEL-49 (a): the phone's path wire) -/

/-- A sibling on a proof's path: the bit its node branches on, then the sibling's digest. The bit is a
`nat16` (two bytes, little-endian, as every codec integer); the node hash commits the same number in its
own big-endian `Trie.u16`, so the two spellings differ and each is injective below `2 ^ 16`. -/
def sibling (dc : Stream D) : Stream (Nat × D) := product nat16 dc

/-- A trie proof as written, its path not yet checked: what the path ends at (`none`: the empty trie;
`some`: a leaf's entries as key and value digest, at most `worldMax`), then the siblings from the root
down, at most `depth`. -/
def proofWire {K : Type} (depth : Nat) (kc : Stream K) (dc : Stream D) :
    Stream (Option (List (K × D)) × List (Nat × D)) :=
  product (option (rawList worldMax (product kc dc))) (rawList depth (sibling dc))

/-- Is `x` a path a trie can show: its siblings' bits ascend below `S.depth` (`Trie.ascends S 0`, the
check `verifyInclusion` / `verifyExclusion` make before hashing), and it ends at a leaf's entries (at
least one: no leaf is empty) or at the empty trie with no sibling (only a whole trie is empty). -/
def proofShaped {K V : Type} [DecidableEq K] (S : Trie.Spec K V D) (x : Option (List (K × D)) × List (Nat × D)) :
    Bool :=
  Trie.ascends S 0 x.2 && match x.1 with
    | none => x.2.isEmpty
    | some kds => !kds.isEmpty

/-- A trie proof under `S` (`Trie.Proof`), read back only when it is `proofShaped`, refused
`kernel/proof` otherwise: a bit out of order or at or past the depth, an empty leaf, or siblings above
an empty trie is no path of a trie. The bits are on the wire because the node hash commits them
(KERNEL-49 (a)); a proof that claimed other bits would climb to another root. -/
def proof {K V : Type} [DecidableEq K] (S : Trie.Spec K V D) (kc : Stream K) (dc : Stream D) :
    Stream (Trie.Proof K D) :=
  refine "kernel/proof" (proofWire S.depth kc dc)
    (fun x => if proofShaped S x = true then some ⟨x.1, x.2⟩ else none) (fun p => (p.term, p.sibs))

/-- The cells' trie, as its listing (`kernel/trie-order`). -/
def cells [DecidableEq D] (E : Env D) (dc : Stream D) : Stream (Cells D) :=
  refine "kernel/trie-order" (fitList dc) (listingAccept (trieSpec E)) Trie.T.toList

/-- The journal's trie (KERNEL-41), as its listing of (transaction id, height, turn digest), at most
`Bounds.journalMax` entries (`kernel/journal-order`). -/
def journalTrie [DecidableEq D] (E : Env D) (dc : Stream D) : Stream (Journal D) :=
  refine "kernel/journal-order" (rawList Bounds.journalMax (product dc (product nat64 dc)))
    (listingAccept (journalSpec E)) Trie.T.toList

/-! ## The refusals (KERNEL-44, KERNEL-47)

The third trie: a refused transaction id (`tx`) holding the height and code it was refused at, a
member's refusal count for one window (`count`), or the World's refusal count for one window, all
members together (`total`, KERNEL-55 R1, a `count` leaf under the World's origin; at most
`Bounds.refusalsPerWindowMax`, which `kernel/refusals` checks). Written as its listing and read back by `build`, as
the other two (`kernel/refusal-order`); which key holds which leaf, and the window facts, are the
World's `kernel/refusals` refusal (KERNEL's `refusalsFits`, which refuses a misfit pairing). -/

abbrev RefusalSlotF (D : Type) : Fin 3 → Type
  | 0 => D
  | 1 => D × UInt64
  | 2 => D × UInt64

def refusalSlotWire (dc : Stream D) : (s : Fin 3) → Stream (RefusalSlotF D s)
  | 0 => dc
  | 1 => product dc u64
  | 2 => product dc u64

/-- A refusals key: its kind (0 a refused transaction id, 1 a member's window count, 2 the World's
window total, as in `refusalKeyBytes`), then the id, or the member and the window, or the origin
and the window. The kind byte leads the key bytes, so a listing holds every `tx`, then every
`count`, then the `total` (`Codec.Proofs.SlotOrder.refusalKeyBytes_kind_lt`). -/
def refusalSlot (dc : Stream D) : Stream (RefusalSlot D) :=
  refine "kernel/refusal-slot" (choice 3 (refusalSlotWire dc))
    (fun | ⟨0, i⟩ => some (.tx i) | ⟨1, (m, w)⟩ => some (.count m w) | ⟨2, (o, w)⟩ => some (.total o w))
    (fun | .tx i => ⟨0, i⟩ | .count m w => ⟨1, (m, w)⟩ | .total o w => ⟨2, (o, w)⟩)

/-- A refusals key's kind: the wire's choice tag and the key bytes' first byte (`refusalKeyBytes`): 0 a
refused transaction id, 1 a member's window count, 2 the World's window total (KERNEL-55 R1). -/
def refusalKind {K : Type} : RefusalSlot K → Nat
  | .tx _ => 0
  | .count _ _ => 1
  | .total _ _ => 2

abbrev RefusalLeafF (D : Type) : Fin 2 → Type
  | 0 => Nat × Nat × D
  | 1 => Nat

def refusalLeafWire (dc : Stream D) : (s : Fin 2) → Stream (RefusalLeafF D s)
  | 0 => product nat64 (product nat64 dc)
  | 1 => nat64

/-- A refusals leaf: `refused h code member` (0: its counters as u64, then the charged member,
KERNEL-50) or `count n` (1). -/
def refusalLeaf (dc : Stream D) : Stream (RefusalLeaf D) :=
  refine "kernel/refusal-leaf" (choice 2 (refusalLeafWire dc))
    (fun | ⟨0, (h, c, m)⟩ => some (.refused h c m) | ⟨1, n⟩ => some (.count n))
    (fun | .refused h c m => ⟨0, (h, c, m)⟩ | .count n => ⟨1, n⟩)

/-- The refusals' trie, as its listing (`kernel/refusal-order`): at most `worldMax` entries on the wire
(a reached World holds at most `Bounds.refusalsPerWindow` per member per window, three windows kept,
and one count per member: KERNEL-44's bound, which the wire does not restate). -/
def refusalsTrie [DecidableEq D] (E : Env D) (dc : Stream D) : Stream (Refusals D) :=
  refine "kernel/refusal-order" (rawList worldMax (product (refusalSlot dc) (refusalLeaf dc)))
    (listingAccept (refusalSpec E)) Trie.T.toList

/-! ## The rows (KERNEL-46/48)

The fourth trie: relations' heads and rows under their parents, keyed by `rowKey` (whose bytes are
KERNEL's `rowKeyBytes`) and leafed by `rowLeaf`, the leaf with its floor and version as u64 varints
(KERNEL-54); the row pin hashes the same leaf as `rowLeafHashed`, KERNEL's `rowLeafBytes`
(`Codec.Proofs.Rows`). Written as
its listing and read back by `build` (`kernel/row-order`); which key holds which leaf, the bounds and the
heads' counts are the World's `kernel/rows` and `kernel/rows-headed` refusals. -/

/-- The rows listing codec the World and carried wires read (`rowsTrie` refines it). -/
abbrev rowsListing (dc : Stream D) : Stream (List (RowSlot D × RowLeaf)) :=
  rawList worldMax (product (rowKey dc) rowLeaf)

/-- The rows' trie, as its listing (`kernel/row-order`): at most `worldMax` entries on the wire (a
reached World holds at most `Bounds.rowsPerRelationMax` rows per relation, 256 relations per live
parent: the parents are not statically bounded, so the wire bound is the map bound, as the refusals'). -/
def rowsTrie [DecidableEq D] (E : Env D) (dc : Stream D) : Stream (Rows D) :=
  refine "kernel/row-order" (rowsListing dc) (listingAccept (rowSpec E)) Trie.T.toList

/-- The World's contents, in canonical order: the four tries, the height, the step count, the
chain, the allowance, the origin. Every check below reads them through `ofWire`, by name, so a part
added later moves no check. -/
abbrev WorldWire (D : Type) := Cells D × Journal D × Refusals D × Rows D × Nat × Nat × D × Nat × D

def worldWire [DecidableEq D] (E : Env D) (dc : Stream D) : Stream (WorldWire D) :=
  product (cells E dc) (product (journalTrie E dc) (product (refusalsTrie E dc) (product (rowsTrie E dc)
    (product nat64 (product nat64 (product dc (product nat64 dc)))))))

def toWire (w : World D) : WorldWire D :=
  (w.trie, w.journal, w.refusals, w.rows, w.height, w.steps, w.chain, w.allowance, w.origin)

def ofWire (x : WorldWire D) : World D :=
  { trie := x.1, journal := x.2.1, refusals := x.2.2.1, rows := x.2.2.2.1, height := x.2.2.2.2.1,
    steps := x.2.2.2.2.2.1, chain := x.2.2.2.2.2.2.1, allowance := x.2.2.2.2.2.2.2.1, origin := x.2.2.2.2.2.2.2.2 }

/-- The World's contents, refused by name unless the journal is the window's (KERNEL-39). -/
def journalWire [DecidableEq D] (E : Env D) (dc : Stream D) : Stream (WorldWire D) :=
  refine "kernel/journal" (worldWire E dc)
    (fun x => if journalFits (ofWire x).height (ofWire x).journal.toList then some x else none) id

/-- The World's contents, refused by name unless its refusals are the window's (KERNEL-47's
`refusalsFits`: each key holds the leaf of its kind, refused calls inside their kept window, counts for
the current window and within `Bounds.refusalsPerWindow`, the window total (KERNEL-55 R1) for the
current window and within `Bounds.refusalsPerWindowMax`). -/
def refusalsWire [DecidableEq D] (E : Env D) (dc : Stream D) : Stream (WorldWire D) :=
  refine "kernel/refusals" (journalWire E dc)
    (fun x => if refusalsFits (ofWire x).height (ofWire x).refusals.toList then some x else none) id

/-- The World's contents, refused by name unless no transaction id is both recorded refused and
journaled (KERNEL's `refusalsDisjoint`; a fold never reaches such a World, `fold_refusalsDisjoint`):
one journal lookup per recorded refusal. -/
def disjointWire [DecidableEq D] (E : Env D) (dc : Stream D) : Stream (WorldWire D) :=
  refine "kernel/refusals-disjoint" (refusalsWire E dc)
    (fun x => if refusalsDisjoint E (ofWire x) then some x else none) id

/-- The World's contents, refused by name unless the World has taken at least as many steps as its
height (KERNEL's `fold_height_le_steps`: every admitted Turn is a step, a refusal a step that does not
advance the height; genesis starts both at 0, a carry both at the carried height). -/
def stepsWire [DecidableEq D] (E : Env D) (dc : Stream D) : Stream (WorldWire D) :=
  refine "kernel/steps" (disjointWire E dc)
    (fun x => if (ofWire x).height ≤ (ofWire x).steps then some x else none) id

/-- The World's contents, refused by name unless its refusal counts are its records' (KERNEL-50's
`refusalsCounted`: records plus height at most the step count, every count leaf the tally of its
member's records this window, every member with a record this window counted; KERNEL-55 R1: the window
total filed under the World's origin, equal to the window's records and present when one is, and each of
the two windows before holding at most `Bounds.refusalsPerWindowMax` records; a fold never reaches
another World, `fold_refusalsCounted`), so a decoded base cannot hold a lowered or moved charge, nor a
lowered, raised or stray total. -/
def countedWire [DecidableEq D] (E : Env D) (dc : Stream D) : Stream (WorldWire D) :=
  refine "kernel/refusals-counted" (stepsWire E dc)
    (fun x => if refusalsCounted E (ofWire x) then some x else none) id

/-- The World's contents, refused by name unless every rows entry fits (KERNEL-48's `rowsFits`: each
key holds the leaf of its kind, a relation below 256, a key of at most `Bounds.keyBytesMax` bytes, a
head's limit at most `Bounds.rowsPerRelationMax`, its width at most `Bounds.keyBytesMax`, its count at
most its limit, its sum at most its cap below 2^64, a row's amount below 2^64 and its value at most
`Bounds.valueBytesMax`; the listing strictly ascending by `rowKeyBytes`). -/
def rowsWire [DecidableEq D] (E : Env D) (dc : Stream D) : Stream (WorldWire D) :=
  refine "kernel/rows" (countedWire E dc)
    (fun x => if rowsFits E (ofWire x).rows.toList then some x else none) id

/-- The World's contents, refused by name unless every row has its head, at the head's width, and
every head counts and sums exactly its rows (KERNEL-48's `rowsHeaded`, the decode-side twin of
`head_sum`). -/
def headedWire [DecidableEq D] (E : Env D) (dc : Stream D) : Stream (WorldWire D) :=
  refine "kernel/rows-headed" (rowsWire E dc)
    (fun x => if rowsHeaded (ofWire x).rows.toList then some x else none) id

/-- The World's contents, refused by name unless every relation's parent is a live cell (KERNEL-48's
`rowsParented`: a head is born only under a parent its turn creates, a parent's heads go when it is
retired, so no fold reaches a relation under an absent or retired parent; rows need their head, so the
heads suffice). -/
def parentedWire [DecidableEq D] (E : Env D) (dc : Stream D) : Stream (WorldWire D) :=
  refine "kernel/rows-parented" (headedWire E dc)
    (fun x => if rowsParented E (ofWire x).trie (ofWire x).rows then some x else none) id

/-- The checkpoint: the World's parts, in canonical order, refused `kernel/journal` unless its journal
is the window's, `kernel/refusals` unless its refusals are, `kernel/refusals-disjoint` unless no
transaction id is both refused and journaled, `kernel/steps` unless its height is at most
its step count, `kernel/refusals-counted` unless its refusal counts are its records', `kernel/rows` unless every rows entry fits, `kernel/rows-headed` unless every head
counts its rows, `kernel/rows-parented` unless every relation's parent is live, and `kernel/world-budget` unless its storage (cells and rows, `World.weight`) plus
allowance is below 2^64 (the bound genesis and carry check and admission conserves, KERNEL's
`fold_budget_lt`; past it a retirement's credit would carry the allowance out of its `u64`, cv
01a14ba9-cbf4). -/
def world [DecidableEq D] (E : Env D) (dc : Stream D) : Stream (World D) :=
  refine "kernel/world-budget" (parentedWire E dc)
    (fun x => if (ofWire x).weight + (ofWire x).allowance < 2 ^ 64 then some (ofWire x) else none) toWire

/-- A recorded refusal as the log carries it (KERNEL-44): transaction id, signer, window, code, the
signed call's bytes (at most `callMax`, KERNEL's `checkRefusedBounds`), which the follower decodes and
re-derives, and a cancel's signature (at most `cancelBytesMax`, empty for a judged refusal, KERNEL-60). -/
def refused (dc : Stream D) : Stream (Refused D) :=
  refine "kernel/refused"
    (product dc (product dc (product nat64 (product nat64 (product nat64 (product (rawBytes callMax)
      (rawBytes Bounds.cancelBytesMax)))))))
    (fun (i, m, nb, vu, c, e, a) => some ⟨i, m, nb, vu, c, e, a⟩)
    (fun r => (r.txId, r.member, r.notBefore, r.validUntil, r.code, r.event, r.cancel))

abbrev StepF (D : Type) : Fin 2 → Type
  | 0 => Turn D
  | 1 => Refused D

def stepWire (dc : Stream D) : (s : Fin 2) → Stream (StepF D s)
  | 0 => turn dc
  | 1 => refused dc

/-- One step of a log (KERNEL-47): an admitted Turn (0) or a recorded refusal (1). -/
def step (dc : Stream D) : Stream (Step D) :=
  refine "kernel/step" (choice 2 (stepWire dc))
    (fun | ⟨0, t⟩ => some (.turn t) | ⟨1, r⟩ => some (.refusal r))
    (fun | .turn t => ⟨0, t⟩ | .refusal r => ⟨1, r⟩)

/-- A log segment's batch record: at most `max` steps, each with the roots digest after it
(`World.roots`, KERNEL-47: `chainNext` and `refusalLink` commit it, so the record's end chain is
derivable and not written). -/
def batch (max : Nat) (dc : Stream D) : Stream (List (Step D × D)) :=
  rawList max (product (step dc) dc)

/-! ## The carried state (CODEC-22, KERNEL-29, KERNEL-48)

`trie ‖ allowance u64 ‖ height u64 ‖ journal ‖ rows`: the three tries as their listings (the cells'
`kernel/leaf-fit` and `kernel/trie-order` refusals, the journal's `kernel/journal-order`, the rows'
`kernel/row-order`), refused `kernel/carried-journal` unless the journal is the window's at the carried
height, `kernel/carried-rows` unless every rows entry fits, `kernel/carried-rows-headed` unless every
head counts its rows, and `kernel/carried-rows-parented` unless every relation's parent is a live cell. An export stamps the shape's tag; the import compares it before decoding. -/

/-- The carried state's contents, in canonical order. -/
abbrev CarriedWire (D : Type) := Cells D × Nat × Nat × Journal D × Rows D

def carriedWire [DecidableEq D] (E : Env D) (dc : Stream D) : Stream (CarriedWire D) :=
  product (cells E dc) (product nat64 (product nat64 (product (journalTrie E dc) (rowsTrie E dc))))

def carriedToWire (c : Carried D) : CarriedWire D := (c.trie, c.allowance, c.height, c.journal, c.rows)

def carriedOfWire (x : CarriedWire D) : Carried D :=
  { trie := x.1, allowance := x.2.1, height := x.2.2.1, journal := x.2.2.2.1, rows := x.2.2.2.2 }

/-- The carried state's contents, refused by name unless the journal is the window's at the carried
height (KERNEL-39's `journalFits`, as the World's `kernel/journal`; HOST-11's find): a carried file with
a future or stale entry never reaches `importWorld`. -/
def carriedJournalWire [DecidableEq D] (E : Env D) (dc : Stream D) : Stream (CarriedWire D) :=
  refine "kernel/carried-journal" (carriedWire E dc)
    (fun x => if journalFits (carriedOfWire x).height (carriedOfWire x).journal.toList then some x else none) id

/-- The carried state's contents, refused by name unless every rows entry fits (`rowsFits`, as the
World's `kernel/rows`). -/
def carriedRowsWire [DecidableEq D] (E : Env D) (dc : Stream D) : Stream (CarriedWire D) :=
  refine "kernel/carried-rows" (carriedJournalWire E dc)
    (fun x => if rowsFits E (carriedOfWire x).rows.toList then some x else none) id

/-- The carried state's contents, refused by name unless every head counts its rows (`rowsHeaded`,
as the World's `kernel/rows-headed`). -/
def carriedHeadedWire [DecidableEq D] (E : Env D) (dc : Stream D) : Stream (CarriedWire D) :=
  refine "kernel/carried-rows-headed" (carriedRowsWire E dc)
    (fun x => if rowsHeaded (carriedOfWire x).rows.toList then some x else none) id

/-- The carried state's contents, refused by name unless every relation's parent is a live carried
cell (`rowsParented`, as the World's `kernel/rows-parented`). -/
def carriedParentedWire [DecidableEq D] (E : Env D) (dc : Stream D) : Stream (CarriedWire D) :=
  refine "kernel/carried-rows-parented" (carriedHeadedWire E dc)
    (fun x => if rowsParented E (carriedOfWire x).trie (carriedOfWire x).rows then some x else none) id

/-- The carried state (KERNEL-48: it carries the rows, so its shape and tag moved; an export of the
old shape refuses by its stamp). -/
def carried [DecidableEq D] (E : Env D) (dc : Stream D) : Stream (Carried D) :=
  refine "kernel/carried" (carriedParentedWire E dc) (fun x => some (carriedOfWire x)) carriedToWire

end Nanodregg.Codec.Kernel
