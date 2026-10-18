import Codec.Kernel

/-!
# Codec.World — the canonical bytes of a whole World (the checkpoint, HOST-14's base)

`trie ‖ journal ‖ refusals ‖ height u64 ‖ steps u64 ‖ chain ‖ allowance u64 ‖ origin`. The World's three maps are tries
(KERNEL-23 cells and spent nullifiers; KERNEL-41 the journal, under `journalSpec`; KERNEL-44 the
refusals, under `refusalSpec`), and each is written
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
(`world_decode_refusalsOk`); and `kernel/steps` unless its height is at most its step count.
`world.size w` is the encoded length, computed from the entries without encoding (HOST's
`worldBytesMax`).
-/

namespace Nanodregg.Codec.Kernel

open Nanodregg.Kernel Nanodregg.Codec.Stream

variable {D : Type} [Ord D]

abbrev EntryF : Fin 2 → Type
  | 0 => Cell
  | 1 => Unit

def entryWire : (s : Fin 2) → Stream (EntryF s)
  | 0 => cell
  | 1 => unit

def entry : Stream Entry :=
  refine "kernel/entry" (choice 2 entryWire)
    (fun | ⟨0, c⟩ => some (.live c) | ⟨1, ()⟩ => some .tomb)
    (fun | .live c => ⟨0, c⟩ | .tomb => ⟨1, ()⟩)

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
  | .node _ l r => leavesNodup l && leavesNodup r

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

/-- The cells' trie, as its listing (`kernel/trie-order`). -/
def cells [DecidableEq D] (E : Env D) (dc : Stream D) : Stream (Cells D) :=
  refine "kernel/trie-order" (fitList dc) (listingAccept (trieSpec E)) Trie.T.toList

/-- The journal's trie (KERNEL-41), as its listing of (transaction id, height, turn digest), at most
`Bounds.journalMax` entries (`kernel/journal-order`). -/
def journalTrie [DecidableEq D] (E : Env D) (dc : Stream D) : Stream (Journal D) :=
  refine "kernel/journal-order" (rawList Bounds.journalMax (product dc (product nat64 dc)))
    (listingAccept (journalSpec E)) Trie.T.toList

/-! ## The refusals (KERNEL-44, KERNEL-47)

The third trie: a refused transaction id (`tx`) holding the height and code it was refused at, or a
member's refusal count for one window (`count`). Written as its listing and read back by `build`, as
the other two (`kernel/refusal-order`); which key holds which leaf, and the window facts, are the
World's `kernel/refusals` refusal (KERNEL's `refusalsFits`, which refuses a misfit pairing). -/

abbrev RefusalSlotF (D : Type) : Fin 2 → Type
  | 0 => D
  | 1 => D × UInt64

def refusalSlotWire (dc : Stream D) : (s : Fin 2) → Stream (RefusalSlotF D s)
  | 0 => dc
  | 1 => product dc u64

/-- A refusals key: its kind (0 a refused transaction id, 1 a member's window count, as in
`refusalKeyBytes`), then the id, or the member and the window. -/
def refusalSlot (dc : Stream D) : Stream (RefusalSlot D) :=
  refine "kernel/refusal-slot" (choice 2 (refusalSlotWire dc))
    (fun | ⟨0, i⟩ => some (.tx i) | ⟨1, (m, w)⟩ => some (.count m w))
    (fun | .tx i => ⟨0, i⟩ | .count m w => ⟨1, (m, w)⟩)

abbrev RefusalLeafF : Fin 2 → Type
  | 0 => Nat × Nat
  | 1 => Nat

def refusalLeafWire : (s : Fin 2) → Stream (RefusalLeafF s)
  | 0 => product nat64 nat64
  | 1 => nat64

/-- A refusals leaf: `refused h code` (0) or `count n` (1), its counters as u64. -/
def refusalLeaf : Stream RefusalLeaf :=
  refine "kernel/refusal-leaf" (choice 2 refusalLeafWire)
    (fun | ⟨0, (h, c)⟩ => some (.refused h c) | ⟨1, n⟩ => some (.count n))
    (fun | .refused h c => ⟨0, (h, c)⟩ | .count n => ⟨1, n⟩)

/-- The refusals' trie, as its listing (`kernel/refusal-order`): at most `worldMax` entries on the wire
(a reached World holds at most `Bounds.refusalsPerWindow` per member per window, three windows kept,
and one count per member: KERNEL-44's bound, which the wire does not restate). -/
def refusalsTrie [DecidableEq D] (E : Env D) (dc : Stream D) : Stream (Refusals D) :=
  refine "kernel/refusal-order" (rawList worldMax (product (refusalSlot dc) refusalLeaf))
    (listingAccept (refusalSpec E)) Trie.T.toList

/-- The World's contents, in canonical order: the three tries, the height, the step count, the
chain, the allowance, the origin. -/
abbrev WorldWire (D : Type) := Cells D × Journal D × Refusals D × Nat × Nat × D × Nat × D

def worldWire [DecidableEq D] (E : Env D) (dc : Stream D) : Stream (WorldWire D) :=
  product (cells E dc) (product (journalTrie E dc) (product (refusalsTrie E dc)
    (product nat64 (product nat64 (product dc (product nat64 dc))))))

/-- The World's contents, refused by name unless the journal is the window's (KERNEL-39). -/
def journalWire [DecidableEq D] (E : Env D) (dc : Stream D) : Stream (WorldWire D) :=
  refine "kernel/journal" (worldWire E dc)
    (fun x => if journalFits x.2.2.2.1 x.2.1.toList then some x else none) id

/-- The World's contents, refused by name unless its refusals are the window's (KERNEL-47's
`refusalsFits`: each key holds the leaf of its kind, refused calls inside their kept window, counts for
the current window and within `Bounds.refusalsPerWindow`). -/
def refusalsWire [DecidableEq D] (E : Env D) (dc : Stream D) : Stream (WorldWire D) :=
  refine "kernel/refusals" (journalWire E dc)
    (fun x => if refusalsFits x.2.2.2.1 x.2.2.1.toList then some x else none) id

def toWire (w : World D) : WorldWire D :=
  (w.trie, w.journal, w.refusals, w.height, w.steps, w.chain, w.allowance, w.origin)

def ofWire (x : WorldWire D) : World D :=
  ⟨x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2⟩

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
    (fun x => if x.2.2.2.1 ≤ x.2.2.2.2.1 then some x else none) id


/-- The checkpoint: the World's parts, in canonical order, refused `kernel/journal` unless its journal
is the window's, `kernel/refusals` unless its refusals are, `kernel/refusals-disjoint` unless no
transaction id is both refused and journaled, `kernel/steps` unless its height is at most
its step count, and `kernel/world-budget` unless its storage plus allowance is below 2^64 (the bound genesis
and carry check and admission conserves, KERNEL's `fold_budget_lt`; past it a retirement's credit
would carry the allowance out of its `u64`, cv 01a14ba9-cbf4). -/
def world [DecidableEq D] (E : Env D) (dc : Stream D) : Stream (World D) :=
  refine "kernel/world-budget" (stepsWire E dc)
    (fun x => if cellsWeight x.1 + x.2.2.2.2.2.2.1 < 2 ^ 64 then some (ofWire x) else none) toWire

/-- A recorded refusal as the log carries it (KERNEL-44): transaction id, signer, window, code, and the
signed call's bytes (at most `callMax`, KERNEL's `checkRefusedBounds`), which the follower decodes and
re-derives. -/
def refused (dc : Stream D) : Stream (Refused D) :=
  refine "kernel/refused"
    (product dc (product dc (product nat64 (product nat64 (product nat64 (rawBytes callMax))))))
    (fun (i, m, nb, vu, c, e) => some ⟨i, m, nb, vu, c, e⟩)
    (fun r => (r.txId, r.member, r.notBefore, r.validUntil, r.code, r.event))

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

/-! ## The carried state (CODEC-22, KERNEL-29)

`trie ‖ allowance u64 ‖ height u64 ‖ journal`: both tries as their listings (the cells' `kernel/leaf-fit`
and `kernel/trie-order` refusals, the journal's `kernel/journal-order`), refused `kernel/carried-journal`
unless the journal is the window's at the carried height. An export stamps the shape's
tag; the import compares it before decoding. -/

/-- The carried state's contents, in canonical order. -/
abbrev CarriedWire (D : Type) := Cells D × Nat × Nat × Journal D

def carriedWire [DecidableEq D] (E : Env D) (dc : Stream D) : Stream (CarriedWire D) :=
  product (cells E dc) (product nat64 (product nat64 (journalTrie E dc)))

def carriedToWire (c : Carried D) : CarriedWire D := (c.trie, c.allowance, c.height, c.journal)

def carriedOfWire (x : CarriedWire D) : Carried D := ⟨x.1, x.2.1, x.2.2.1, x.2.2.2⟩

/-- The carried state's contents, refused by name unless the journal is the window's at the carried
height (KERNEL-39's `journalFits`, as the World's `kernel/journal`; HOST-11's find): a carried file with
a future or stale entry never reaches `importWorld`. -/
def carriedJournalWire [DecidableEq D] (E : Env D) (dc : Stream D) : Stream (CarriedWire D) :=
  refine "kernel/carried-journal" (carriedWire E dc)
    (fun x => if journalFits x.2.2.1 x.2.2.2.toList then some x else none) id

def carried [DecidableEq D] (E : Env D) (dc : Stream D) : Stream (Carried D) :=
  refine "kernel/carried" (carriedJournalWire E dc) (fun x => some (carriedOfWire x)) carriedToWire

end Nanodregg.Codec.Kernel
