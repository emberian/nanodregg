import Codec.Kernel

/-!
# Codec.World — the canonical bytes of a whole World (the checkpoint, HOST-14's base)

`trie ‖ journal ‖ height u64 ‖ chain ‖ allowance u64 ‖ origin` (KERNEL-23: cells and spent nullifiers
are one authenticated trie). The trie is written as its listing (`Trie.T.toList`, left to right by
key bits) and read back by `Trie.build` over that listing: every node hash is recomputed, none is ever
read from the wire (CODEC-19). A listing is refused by name unless every slot holds the leaf of its
kind (`kernel/leaf-fit`) and the listing is exactly the canonical trie's own (`kernel/trie-order`:
the rebuilt trie lists the same entries in the same order, and no leaf holds a key twice). So the
trie part reads back EXACTLY (`build_toList`), and the bytes are a function of the contents. The
journal is still a `TreeMap` written in ascending key order (at most `Bounds.journalMax` entries), read
back up to `Equiv`, and refused by name unless it is the window's (`kernel/journal`: KERNEL-39's
`journalFits`, every entry at or below the height and inside the window, one entry per height), so a
decoded base carries `World.JournalOk` (`world_decode_journalOk`).
`world.size w` is the encoded length, computed from the entries without encoding (HOST's
`worldBytesMax`).
-/

namespace Nanodregg.Codec.Kernel

open Nanodregg.Kernel Nanodregg.Codec.Stream

variable {D : Type} [Ord D]

/-- Keys strictly ascending (each adjacent pair). -/
def ascendingBy {β : Type} (f : β → D) : List β → Bool
  | a :: b :: rest => compare (f a) (f b) == .lt && ascendingBy f (b :: rest)
  | _ => true

/-- A list of at most `max` values whose keys strictly ascend; any other order is refused. -/
def ascendingList {β : Type} (max : Nat) (f : β → D) (c : Stream β) : Stream (List β) :=
  refine "kernel/ascending" (rawList max c) (fun l => if ascendingBy f l then some l else none) id

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

/-- The trie, as its listing; read back by `build`, refused unless the listing is the rebuilt
trie's own. -/
def cells [DecidableEq D] (E : Env D) (dc : Stream D) : Stream (Cells D) :=
  refine "kernel/trie-order" (fitList dc)
    (fun l =>
      let t := Trie.build (trieSpec E) (trieSpec E).depth 0 l
      if t.toList == l && leavesNodup t then some t else none)
    Trie.T.toList

/-- The World's contents, in canonical order. -/
abbrev WorldWire (D : Type) := Cells D × List (D × (Nat × D)) × Nat × D × Nat × D

def worldWire [DecidableEq D] (E : Env D) (dc : Stream D) : Stream (WorldWire D) :=
  product (cells E dc)
    (product (ascendingList Bounds.journalMax Prod.fst (product dc (product nat64 dc)))
      (product nat64 (product dc (product nat64 dc))))

/-- The World's contents, refused by name unless the journal is the window's (KERNEL-39). -/
def journalWire [DecidableEq D] (E : Env D) (dc : Stream D) : Stream (WorldWire D) :=
  refine "kernel/journal" (worldWire E dc) (fun x => if journalFits x.2.2.1 x.2.1 then some x else none) id

def toWire (w : World D) : WorldWire D :=
  (w.trie, w.journal.toList, w.height, w.chain, w.allowance, w.origin)

def ofWire (x : WorldWire D) : World D :=
  ⟨x.1, Std.TreeMap.ofList x.2.1 compare, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2⟩

def world [DecidableEq D] (E : Env D) (dc : Stream D) : Stream (World D) where
  shape := .refine "kernel/world" (journalWire E dc).shape
  size w := (journalWire E dc).size (toWire w)
  put w buf := (journalWire E dc).put (toWire w) buf
  get b i :=
    match (journalWire E dc).get b i with
    | .ok (x, j) => .ok (ofWire x, j)
    | .error e => .error e

/-- A log segment's batch record: at most `max` turns, each with the trie root after it (HOST-29:
`chainNext` commits each root, so the record's end chain is derivable and not written). -/
def batch (max : Nat) (dc : Stream D) : Stream (List (Turn D × D)) :=
  rawList max (product (turn dc) dc)

/-! ## The carried state (CODEC-22, KERNEL-29)

`trie ‖ allowance u64 ‖ height u64 ‖ journal`: the trie as the World codec's listing (its `kernel/leaf-fit` and
`kernel/trie-order` refusals), the journal strictly ascending by transaction id and at most
`Bounds.journalMax` entries (every reached World holds fewer: `Kernel.reach_journal_bounded`). An export
stamps the shape's tag; the import compares it before decoding. -/

/-- The carried state's contents, in canonical order. -/
abbrev CarriedWire (D : Type) := Cells D × Nat × Nat × List (D × (Nat × D))

def carriedWire [DecidableEq D] (E : Env D) (dc : Stream D) : Stream (CarriedWire D) :=
  product (cells E dc) (product nat64 (product nat64
    (ascendingList Bounds.journalMax Prod.fst (product dc (product nat64 dc)))))

def carriedToWire (c : Carried D) : CarriedWire D := (c.trie, c.allowance, c.height, c.journal.toList)

def carriedOfWire (x : CarriedWire D) : Carried D :=
  ⟨x.1, x.2.1, x.2.2.1, Std.TreeMap.ofList x.2.2.2 compare⟩

def carried [DecidableEq D] (E : Env D) (dc : Stream D) : Stream (Carried D) where
  shape := .refine "kernel/carried" (carriedWire E dc).shape
  size c := (carriedWire E dc).size (carriedToWire c)
  put c buf := (carriedWire E dc).put (carriedToWire c) buf
  get b i :=
    match (carriedWire E dc).get b i with
    | .ok (x, j) => .ok (carriedOfWire x, j)
    | .error e => .error e

end Nanodregg.Codec.Kernel
