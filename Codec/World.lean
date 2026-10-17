import Codec.Kernel

/-!
# Codec.World — the canonical bytes of a whole World (the checkpoint, HOST-14's base)

`cells ‖ journal ‖ spent ‖ height u64 ‖ chain ‖ allowance u64`. Each map is written as its entries in
ascending key order (`TreeMap.toList`) and read back only if strictly ascending, so the bytes are a
function of the World's contents, not of its trees' shapes. A `TreeMap` rebuilt from its entries is
extensionally equal to the original (`Kernel.World.Equiv`), not `=`. So the read-back law is stated up
to `Equiv`, while canonicity is exact (`Codec.Proofs.World`). `world.size w` is the encoded length,
computed from the entries without encoding (HOST's `worldBytesMax`).
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

/-- The most entries one map of a World holds on the wire. -/
def worldMax : Nat := 2 ^ 32 - 1

/-- The World's contents, in canonical order. -/
abbrev WorldWire (D : Type) :=
  List (D × Entry) × List (D × (Nat × D)) × List D × Nat × D × Nat

def worldWire (dc : Stream D) : Stream (WorldWire D) :=
  product (ascendingList worldMax Prod.fst (product dc entry))
    (product (ascendingList worldMax Prod.fst (product dc (product nat64 dc)))
      (product (ascendingList worldMax id dc) (product nat64 (product dc nat64))))

def toWire (w : World D) : WorldWire D :=
  (w.cells.toList, w.journal.toList, w.spent.toList, w.height, w.chain, w.allowance)

def ofWire (x : WorldWire D) : World D :=
  ⟨Std.TreeMap.ofList x.1 compare, Std.TreeMap.ofList x.2.1 compare, Std.TreeSet.ofList x.2.2.1 compare,
    x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2⟩

def world (dc : Stream D) : Stream (World D) where
  shape := .refine "kernel/world" (worldWire dc).shape
  size w := (worldWire dc).size (toWire w)
  put w buf := (worldWire dc).put (toWire w) buf
  get b i :=
    match (worldWire dc).get b i with
    | .ok (x, j) => .ok (ofWire x, j)
    | .error e => .error e

/-- A log segment's batch record: at most `max` turns, then the chain after them. -/
def batch (max : Nat) (dc : Stream D) : Stream (List (Turn D) × D) :=
  product (rawList max (turn dc)) dc

end Nanodregg.Codec.Kernel
