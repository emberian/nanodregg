import Codec.Kernel

/-!
# Codec.World — the canonical bytes of a whole World (the checkpoint, HOST-14's base)

`trie ‖ journal ‖ height u64 ‖ chain ‖ allowance u64 ‖ origin`. Both of the World's maps are tries
(KERNEL-23 cells and spent nullifiers; KERNEL-41 the journal, under `journalSpec`), and each is written
as its listing (`Trie.T.toList`, left to right by key bits) and read back by `Trie.build` over that
listing (`listingAccept`): every node hash is recomputed, none is ever read from the wire (CODEC-19), and
a listing is refused by name unless it is exactly the rebuilt trie's own (no key twice in a leaf).
The cells' listing is refused `kernel/leaf-fit` unless every slot holds the leaf of its kind, and
`kernel/trie-order` unless it is the canonical trie's; the journal's is refused
`kernel/journal-order` unless it is the canonical journal trie's (at the deployed digest: strictly
ascending by transaction id, `Codec.Deployed.journalOrder_iff`). So both maps read back EXACTLY
(`build_toList`), decode ∘ bytes is the identity (`world_lawfulOn`), and the bytes are a function of
the contents. The World is refused `kernel/journal` unless its journal is the window's (KERNEL-39's
`journalFits`, every entry at or below the height and inside the window, one entry per height), so a
decoded base carries `World.JournalOk` (`world_decode_journalOk`).
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

/-- The World's contents, in canonical order. -/
abbrev WorldWire (D : Type) := Cells D × Journal D × Nat × D × Nat × D

def worldWire [DecidableEq D] (E : Env D) (dc : Stream D) : Stream (WorldWire D) :=
  product (cells E dc) (product (journalTrie E dc) (product nat64 (product dc (product nat64 dc))))

/-- The World's contents, refused by name unless the journal is the window's (KERNEL-39). -/
def journalWire [DecidableEq D] (E : Env D) (dc : Stream D) : Stream (WorldWire D) :=
  refine "kernel/journal" (worldWire E dc) (fun x => if journalFits x.2.2.1 x.2.1.toList then some x else none) id

def toWire (w : World D) : WorldWire D :=
  (w.trie, w.journal, w.height, w.chain, w.allowance, w.origin)

def ofWire (x : WorldWire D) : World D := ⟨x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2⟩

/-- The checkpoint: the World's parts, in canonical order, refused `kernel/journal` unless its journal
is the window's. -/
def world [DecidableEq D] (E : Env D) (dc : Stream D) : Stream (World D) :=
  refine "kernel/world" (journalWire E dc) (fun x => some (ofWire x)) toWire

/-- A log segment's batch record: at most `max` turns, each with the two roots after it, the cells' and
the journal's (HOST-29, KERNEL-41: `chainNext` commits both, so the record's end chain is derivable and
not written). -/
def batch (max : Nat) (dc : Stream D) : Stream (List (Turn D × (D × D))) :=
  rawList max (product (turn dc) (product dc dc))

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
