import Codec.World
import Codec.Proofs.Kernel
import Kernel.Proofs.Cells
import Kernel.Proofs.Trie
import Kernel.Proofs.Journal

/-!
# The World codec: canonical, both tries read back exactly, decode ∘ bytes the identity

* `trieListing_lawfulOn`: a trie written as its listing and read back by `build` is lawful on the
  canonical tries whose listing the inner codec admits; whatever decodes is such a trie
  (`Trie.Canon`), rebuilt from its listing. `cells_lawfulOn` (the cells, `kernel/trie-order`) and
  `journalTrie_lawfulOn` (the journal, `kernel/journal-order`, KERNEL-41) are its two instances.
* `world_lawfulOn`: the World codec is lawful on `World.CodecFits`, so `decode b = .ok w ↔ b = bytes w`
  EXACTLY (`world_decode_iff`): with the journal a trie, no part of a World has a shape beyond its
  contents (the `World.Equiv` of CODEC-14 is gone with KERNEL-41).
* `world_decode_canon` / `world_decode_slotted` / `world_decode_cellsFit` / `world_decode_journalOk`
  (and `world_get_canon` / `world_get_journalOk` at any offset): a decoded World satisfies the kernel's
  invariants, so every kernel theorem that takes them applies to a reopened base.
-/

namespace Nanodregg.Codec.Kernel

open Nanodregg.Kernel Nanodregg.Codec.Stream

/-! ## The wire's parts -/

variable {D : Type} [Ord D]

def Entry.Fits : Entry → Prop
  | .live c => Cell.Fits c
  | .tomb => True

abbrev EntryWireFits : (s : Fin 2) → EntryF s → Prop
  | 0 => Cell.Fits
  | 1 => fun _ => True

theorem entryWire_lawfulOn : ∀ s, LawfulOn (EntryWireFits s) (entryWire s)
  | 0 => cell_lawfulOn
  | 1 => unit_lawful.on

theorem entry_lawfulOn : LawfulOn Entry.Fits entry := by
  unfold entry
  refine (refine_lawfulOn (choice_lawfulOn 2 (by decide) entryWire_lawfulOn) "kernel/entry" ?_ ?_).mono ?_ ?_
  · intro y _; cases y <;> rfl
  · intro x y h
    obtain ⟨s, v⟩ := x
    match s, v, h with
    | 0, c, h => simp at h; subst h; rfl
    | 1, (), h => simp at h; subst h; rfl
  · intro y h; cases y with
    | live c => exact h
    | tomb => trivial
  · intro y h; cases y with
    | live c => exact h
    | tomb => exact trivial

omit [Ord D] in
theorem batch_lawfulOn {PD : D → Prop} {dc : Stream D} (hd : LawfulOn PD dc) (max : Nat) (fits : max < 2 ^ 32) :
    LawfulOn (fun v => v.length ≤ max ∧ ∀ p ∈ v, Turn.Fits PD p.1 ∧ PD p.2.1 ∧ PD p.2.2) (batch max dc) :=
  rawList_lawfulOn (product_lawfulOn (turn_lawfulOn hd) (product_lawfulOn hd hd)) max fits

/-! ## The trie's listing -/

def Leaf.Fits : Leaf → Prop
  | .entry e => Entry.Fits e
  | .spent => True

omit [Ord D] in
theorem slot_lawfulOn {PD : D → Prop} {dc : Stream D} (hd : LawfulOn PD dc) :
    LawfulOn (fun s : Slot D => PD s.id) (slot dc) := by
  unfold slot
  refine (refine_lawfulOn (choice_lawfulOn 2 (by decide) (P := fun _ v => PD v) (fun _ => hd)) "kernel/slot"
    ?_ ?_).mono ?_ ?_
  · intro y _; cases y <;> rfl
  · intro x y h
    obtain ⟨s, v⟩ := x
    match s, v, h with
    | 0, c, h => simp at h; subst h; rfl
    | 1, n, h => simp at h; subst h; rfl
  · intro y h; cases y <;> exact h
  · intro y h; cases y <;> exact h

abbrev LeafWireFits : (s : Fin 2) → LeafF s → Prop
  | 0 => Entry.Fits
  | 1 => fun _ => True

theorem leafWire_lawfulOn : ∀ s, LawfulOn (LeafWireFits s) (leafWire s)
  | 0 => entry_lawfulOn
  | 1 => unit_lawful.on

theorem leaf_lawfulOn : LawfulOn Leaf.Fits leaf := by
  unfold leaf
  refine (refine_lawfulOn (choice_lawfulOn 2 (by decide) leafWire_lawfulOn) "kernel/leaf" ?_ ?_).mono ?_ ?_
  · intro y _; cases y <;> rfl
  · intro x y h
    obtain ⟨s, v⟩ := x
    match s, v, h with
    | 0, e, h => simp at h; subst h; rfl
    | 1, (), h => simp at h; subst h; rfl
  · intro y h; cases y with
    | entry e => exact h
    | spent => trivial
  · intro y h; cases y with
    | entry e => exact h
    | spent => exact trivial

/-- A leaf in the leaf codec's domain holds, if a live cell, a cell in the cell codec's domain. -/
theorem leaf_fits_cellFit : ∀ {l : Leaf}, Leaf.Fits l → l.CellFit Cell.Fits
  | .entry (.live _), h => h
  | .entry .tomb, _ => trivial
  | .spent, _ => trivial

/-- Every leaf Lean's leaf decoder returns is `CellFit Cell.Fits`, and is the decoding of exactly those
bytes: a read over leaf BYTES needs no premise about the leaf (CLIENT-16; KERNEL's phone read). -/
theorem leaf_decode_cellFit {b : ByteArray} {l : Leaf} (h : leaf.decode b = .ok l) :
    l.CellFit Cell.Fits ∧ b = leaf.bytes l :=
  let ⟨hf, hb⟩ := leaf_lawfulOn.eq_bytes_of_decode h
  ⟨leaf_fits_cellFit hf, hb⟩

/-- Tooth: `CellFit Cell.Fits` excludes something — no bytes decode to a leaf holding a cell of kind
`2^32` (outside the cell codec's domain), so `leaf_decode_cellFit` is not `True`. -/
theorem leaf_decode_refuses_misfit (b : ByteArray) :
    leaf.decode b ≠ .ok (.entry (.live ⟨2 ^ 32, .ram, []⟩)) := fun h =>
  absurd (leaf_decode_cellFit h).1.1 (by decide)

section Leaves
variable {K V D' : Type} [DecidableEq K] (S : Trie.Spec K V D')

theorem leavesNodup_of_routed : ∀ (d : Nat) (t : Trie.T K V D'), Trie.Routed S d t → leavesNodup t = true
  | _, .empty, _ => rfl
  | _, .leaf _ _, h => by simpa [leavesNodup] using h
  | d, .node _ l r, h => by
      simp only [leavesNodup, Bool.and_eq_true]
      exact ⟨leavesNodup_of_routed (d + 1) l h.2.2.1, leavesNodup_of_routed (d + 1) r h.2.2.2⟩

/-- A rebuilt trie whose leaves hold each key once came from a listing that holds each key once. -/
theorem nodup_of_leavesNodup_build : ∀ (f d : Nat) (l : List (K × V)),
    leavesNodup (Trie.build S f d l) = true → (l.map Prod.fst).Nodup
  | _, _, [], _ => by simp
  | _, _, [_], _ => by simp
  | 0, _, a :: b :: rest, h => by simpa [Trie.build, Trie.mkLeaf, leavesNodup] using h
  | f + 1, d, a :: b :: rest, h => by
      simp only [Trie.build, Trie.mkNode, leavesNodup, Bool.and_eq_true] at h
      have hl := nodup_of_leavesNodup_build f (d + 1) _ h.1
      have hr := nodup_of_leavesNodup_build f (d + 1) _ h.2
      have hp := List.filter_append_perm (fun p : K × V => !S.bit p.1 d) (a :: b :: rest)
      simp only [Bool.not_not] at hp
      refine (hp.map Prod.fst).nodup_iff.mp ?_
      rw [List.map_append, List.nodup_append]
      refine ⟨hl, hr, ?_⟩
      intro x hx y hy hxy
      subst hxy
      obtain ⟨p, hp1, rfl⟩ := List.mem_map.mp hx
      obtain ⟨q, hq1, hq⟩ := List.mem_map.mp hy
      have h1 := (List.mem_filter.mp hp1).2
      have h2 := (List.mem_filter.mp hq1).2
      rw [hq] at h2
      simp_all

end Leaves

variable [DecidableEq D]

/-- The listing's domain: within the wire's bound, every id in the digest codec's domain, every
leaf in the leaf codec's. -/
def TrieListFits (PD : D → Prop) (l : List (Slot D × Leaf)) : Prop :=
  l.length ≤ worldMax ∧ ∀ p ∈ l, PD p.1.id ∧ Leaf.Fits p.2

omit [Ord D] in
theorem fitList_lawfulOn {PD : D → Prop} {dc : Stream D} (hd : LawfulOn PD dc) :
    LawfulOn (fun l => TrieListFits PD l ∧ ∀ p ∈ l, Leaf.fits p.1 p.2 = true) (fitList dc) := by
  unfold fitList
  refine (refine_lawfulOn_where ((rawList_lawfulOn (product_lawfulOn (slot_lawfulOn hd) leaf_lawfulOn)
    worldMax (by decide))) "kernel/leaf-fit" (Q := fun l : List (Slot D × Leaf) => ∀ p ∈ l, Leaf.fits p.1 p.2 = true)
    ?_ ?_ ?_).mono (fun _ h => h) (fun _ h => h)
  · intro y _ hq; simp [List.all_eq_true.mpr hq]
  · intro x y h; split at h <;> simp_all
  · intro x y h; split at h
    · rename_i ha; cases h; exact List.all_eq_true.mp ha
    · cases h

section Listing
variable {K V : Type} [DecidableEq K] [DecidableEq V]

omit [Ord D] [DecidableEq D] in
/-- **A trie read back from its listing is canonical, and exactly the trie written.** If the inner
codec is lawful on `P`, the listing codec is lawful on the canonical tries whose listing is in `P`. -/
theorem trieListing_lawfulOn (S : Trie.Spec K V D) {P : List (K × V) → Prop} {c : Stream (List (K × V))}
    (hc : LawfulOn P c) (name : String) :
    LawfulOn (fun t => P t.toList ∧ Trie.Canon S 0 t) (refine name c (listingAccept S) Trie.T.toList) := by
  refine (refine_lawfulOn_where hc name (Q := fun t : Trie.T K V D => Trie.Canon S 0 t) ?_ ?_ ?_).mono
    (fun _ h => h) (fun _ h => h)
  · intro y _ hq
    have hb : Trie.build S S.depth 0 y.toList = y := by simpa using Trie.build_toList S 0 y hq
    simp only [listingAccept, hb, beq_self_eq_true, leavesNodup_of_routed S 0 y hq.1, Bool.and_self, if_true]
  · intro x y h
    simp only [listingAccept] at h
    split at h
    · rename_i hc; cases h; simp only [Bool.and_eq_true, beq_iff_eq] at hc; exact hc.1
    · cases h
  · intro x y h
    simp only [listingAccept] at h
    split at h
    · rename_i hc; cases h
      simp only [Bool.and_eq_true] at hc
      simpa using Trie.canon_build S 0 x (nodup_of_leavesNodup_build S _ 0 x hc.2)
    · cases h

end Listing

/-- The trie codec's domain: a canonical trie whose listing fits and whose slots hold the leaves of
their kinds. -/
def CellsFits (E : Env D) (PD : D → Prop) (t : Cells D) : Prop :=
  (TrieListFits PD t.toList ∧ ∀ p ∈ t.toList, Leaf.fits p.1 p.2 = true) ∧ Trie.Canon (trieSpec E) 0 t

omit [Ord D] in
theorem cells_lawfulOn (E : Env D) {PD : D → Prop} {dc : Stream D} (hd : LawfulOn PD dc) :
    LawfulOn (CellsFits E PD) (cells E dc) :=
  trieListing_lawfulOn (trieSpec E) (fitList_lawfulOn hd) "kernel/trie-order"

/-- The journal listing's domain: within `Bounds.journalMax`, every digest in the digest codec's domain,
every height below 2^64. -/
def JournalListFits (PD : D → Prop) (l : List (D × (Nat × D))) : Prop :=
  l.length ≤ Bounds.journalMax ∧ ∀ p ∈ l, PD p.1 ∧ p.2.1 < 2 ^ 64 ∧ PD p.2.2

/-- The journal codec's domain: a canonical journal trie whose listing fits (KERNEL-41). -/
def JournalTrieFits (E : Env D) (PD : D → Prop) (j : Journal D) : Prop :=
  JournalListFits PD j.toList ∧ Trie.Canon (journalSpec E) 0 j

omit [Ord D] in
theorem journalTrie_lawfulOn (E : Env D) {PD : D → Prop} {dc : Stream D} (hd : LawfulOn PD dc) :
    LawfulOn (JournalTrieFits E PD) (journalTrie E dc) :=
  trieListing_lawfulOn (journalSpec E)
    ((rawList_lawfulOn (product_lawfulOn hd (product_lawfulOn nat64_lawfulOn hd)) _ (by decide)).mono
      (fun _ h => h) (fun _ h => h)) "kernel/journal-order"

/-! ## The World -/

/-- The wire's domain, as the product of its parts. -/
def WireFits (E : Env D) (PD : D → Prop) (x : WorldWire D) : Prop :=
  CellsFits E PD x.1 ∧ JournalTrieFits E PD x.2.1 ∧
  x.2.2.1 < 2 ^ 64 ∧ PD x.2.2.2.1 ∧ x.2.2.2.2.1 < 2 ^ 64 ∧ PD x.2.2.2.2.2

omit [Ord D] in
theorem worldWire_lawfulOn (E : Env D) {PD : D → Prop} {dc : Stream D} (hd : LawfulOn PD dc) :
    LawfulOn (WireFits E PD) (worldWire E dc) :=
  (product_lawfulOn (cells_lawfulOn E hd)
    (product_lawfulOn (journalTrie_lawfulOn E hd)
      (product_lawfulOn nat64_lawfulOn (product_lawfulOn hd (product_lawfulOn nat64_lawfulOn hd))))).mono
    (fun _ h => h) (fun _ h => h)

/-- The refined wire's domain: the wire's, and a journal that is the window's. -/
def JournalWireFits (E : Env D) (PD : D → Prop) (x : WorldWire D) : Prop :=
  WireFits E PD x ∧ journalFits x.2.2.1 x.2.1.toList = true

omit [Ord D] in
/-- **`kernel/journal` is lawful on exactly the journals `journalFits` admits.** -/
theorem journalWire_lawfulOn (E : Env D) {PD : D → Prop} {dc : Stream D} (hd : LawfulOn PD dc) :
    LawfulOn (JournalWireFits E PD) (journalWire E dc) := by
  unfold journalWire
  refine (refine_lawfulOn_where (worldWire_lawfulOn E hd) "kernel/journal"
    (Q := fun x : WorldWire D => journalFits x.2.2.1 x.2.1.toList = true) ?_ ?_ ?_).mono
    (fun _ h => h) (fun _ h => h)
  · intro y _ hq; simp [hq]
  · intro x y h; split at h <;> simp_all
  · intro x y h; split at h
    · rename_i hq; cases h; exact hq
    · cases h

/-- A World within the wire's bounds and the kernel's invariants: a canonical cells trie whose slots
hold the leaves of their kinds, a canonical journal trie of at most `Bounds.journalMax` entries,
every digest in the digest codec's domain, the height below 2^64, storage plus allowance below 2^64
(so the allowance is, and admission keeps it: KERNEL's `fold_budget_lt`), and a journal that is the
window's (`journalFits`; every reached World's, by KERNEL's `journalFits_of_ok`). -/
def World.CodecFits (E : Env D) (PD : D → Prop) (w : World D) : Prop :=
  CellsFits E PD w.trie ∧ JournalTrieFits E PD w.journal ∧
  w.height < 2 ^ 64 ∧ PD w.chain ∧ w.weight + w.allowance < 2 ^ 64 ∧ PD w.origin ∧
  journalFits w.height w.journal.toList = true

/-- **The World codec is lawful on `World.CodecFits`**: decode ∘ bytes is the identity, and whatever
decodes is exactly its bytes. -/
theorem world_lawfulOn (E : Env D) {PD : D → Prop} {dc : Stream D} (hd : LawfulOn PD dc) :
    LawfulOn (World.CodecFits E PD) (world E dc) := by
  unfold world
  refine (refine_lawfulOn_where (journalWire_lawfulOn E hd) "kernel/world-budget"
    (Q := fun w : World D => w.weight + w.allowance < 2 ^ 64) ?_ ?_ ?_).mono ?_ ?_
  · intro y _ hq
    show (if cellsWeight y.trie + y.allowance < 2 ^ 64 then some (ofWire (toWire y)) else none) = some y
    rw [if_pos (show cellsWeight y.trie + y.allowance < 2 ^ 64 from hq)]; rfl
  · intro x y h
    split at h
    · cases h; rfl
    · cases h
  · intro x y h
    split at h
    · rename_i hq; cases h; exact hq
    · cases h
  · intro w h; exact ⟨h.1.1.1, h.1.1.2.1, h.1.1.2.2.1, h.1.1.2.2.2.1, h.2, h.1.1.2.2.2.2.2, h.1.2⟩
  · intro w h
    exact ⟨⟨⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, Nat.lt_of_le_of_lt (Nat.le_add_left _ _) h.2.2.2.2.1,
      h.2.2.2.2.2.1⟩, h.2.2.2.2.2.2⟩, h.2.2.2.2.1⟩

theorem world_bytes (E : Env D) (dc : Stream D) (w : World D) :
    (world E dc).bytes w = (journalWire E dc).bytes (toWire w) := rfl

/-- A fitting World reads back from its bytes, exactly. -/
theorem world_decode_bytes {E : Env D} {PD : D → Prop} {dc : Stream D} (hd : LawfulOn PD dc) {w : World D}
    (hw : World.CodecFits E PD w) : (world E dc).decode ((world E dc).bytes w) = .ok w :=
  (world_lawfulOn E hd).decode_bytes hw

/-- Canonicity: whatever decodes to `w` is exactly `w`'s bytes. -/
theorem eq_bytes_of_world_decode {E : Env D} {PD : D → Prop} {dc : Stream D} (hd : LawfulOn PD dc)
    {b : ByteArray} {w : World D} (h : (world E dc).decode b = .ok w) : b = (world E dc).bytes w :=
  ((world_lawfulOn E hd).eq_bytes_of_decode h).2

/-- **Canonicity, exactly**: for a fitting `w`, `b` decodes to `w` iff `b` is `w`'s bytes. -/
theorem world_decode_iff {E : Env D} {PD : D → Prop} {dc : Stream D} (hd : LawfulOn PD dc)
    {b : ByteArray} {w : World D} (hw : World.CodecFits E PD w) :
    (world E dc).decode b = .ok w ↔ b = (world E dc).bytes w :=
  ⟨eq_bytes_of_world_decode hd, fun h => h ▸ world_decode_bytes hd hw⟩

/-- What a World read returns at any offset (the World as a COMPONENT of a larger record, HOST's base)
is in the codec's domain. -/
theorem world_get_fits {E : Env D} {PD : D → Prop} {dc : Stream D} (hd : LawfulOn PD dc)
    {b : ByteArray} {i j : Nat} {w : World D} (h : (world E dc).get b i = .ok (w, j)) :
    World.CodecFits E PD w :=
  ((world_lawfulOn E hd).occurs_of_get h).1

theorem world_decode_fits {E : Env D} {PD : D → Prop} {dc : Stream D} (hd : LawfulOn PD dc)
    {b : ByteArray} {w : World D} (h : (world E dc).decode b = .ok w) : World.CodecFits E PD w :=
  ((world_lawfulOn E hd).eq_bytes_of_decode h).1

/-- A World read at any offset satisfies the kernel's trie invariant, and every slot holds the leaf of
its kind. -/
theorem world_get_canon {E : Env D} {PD : D → Prop} {dc : Stream D} (hd : LawfulOn PD dc)
    {b : ByteArray} {i j : Nat} {w : World D} (h : (world E dc).get b i = .ok (w, j)) :
    w.Canon E ∧ ∀ p ∈ w.trie.toList, Leaf.fits p.1 p.2 = true :=
  let hf := world_get_fits hd h
  ⟨hf.1.2, hf.1.1.2⟩

/-- A decoded World satisfies the kernel's trie invariant, and every slot holds the leaf of its kind. -/
theorem world_decode_canon {E : Env D} {PD : D → Prop} {dc : Stream D} (hd : LawfulOn PD dc)
    {b : ByteArray} {w : World D} (h : (world E dc).decode b = .ok w) :
    w.Canon E ∧ ∀ p ∈ w.trie.toList, Leaf.fits p.1 p.2 = true :=
  let hf := world_decode_fits hd h
  ⟨hf.1.2, hf.1.1.2⟩

/-- A decoded World has every slot holding the leaf of its kind (the kernel's `World.Slotted`). -/
theorem world_decode_slotted {E : Env D} {PD : D → Prop} {dc : Stream D} (hd : LawfulOn PD dc)
    {b : ByteArray} {w : World D} (h : (world E dc).decode b = .ok w) : w.Slotted E := by
  obtain ⟨hc, hf⟩ := world_decode_canon hd h
  intro s l hg
  exact hf (s, l) ((Trie.mem_toList (trieSpec E) 0 w.trie hc.1 s l).mpr hg)

/-- Every live cell of a decoded World is in the cell codec's domain (`Cell.Fits`): a reopened base
carries the kernel's `World.CellsFit` from the codec, so only admission has to keep it (KERNEL-31). -/
theorem world_decode_cellsFit {E : Env D} {PD : D → Prop} {dc : Stream D} (hd : LawfulOn PD dc)
    {b : ByteArray} {w : World D} (h : (world E dc).decode b = .ok w) : w.CellsFit Cell.Fits E := by
  have hf := world_decode_fits hd h
  intro s l hg
  have hm := (Trie.mem_toList (trieSpec E) 0 w.trie hf.1.2.1 s l).mpr hg
  have hl := (hf.1.1.1.2 (s, l) hm).2
  cases l with
  | entry e =>
    cases e with
    | live c => exact hl
    | tomb => trivial
  | spent => trivial

/-- **A World read at any offset carries `World.JournalOk`** (KERNEL-39, KERNEL-41): its journal trie is
canonical (the decoder rebuilt it by `build`) and the decoder refused `kernel/journal` unless
`journalFits` holds of that trie's own listing. -/
theorem world_get_journalOk {E : Env D} {PD : D → Prop} {dc : Stream D} (hd : LawfulOn PD dc)
    {b : ByteArray} {i j : Nat} {w : World D} (h : (world E dc).get b i = .ok (w, j)) : w.JournalOk E :=
  let hf := world_get_fits hd h
  journalOk_of_fits hf.2.1.2 hf.2.2.2.2.2.2

/-- **A decoded World carries `World.JournalOk`.** -/
theorem world_decode_journalOk {E : Env D} {PD : D → Prop} {dc : Stream D} (hd : LawfulOn PD dc)
    {b : ByteArray} {w : World D} (h : (world E dc).decode b = .ok w) : w.JournalOk E :=
  let hf := world_decode_fits hd h
  journalOk_of_fits hf.2.1.2 hf.2.2.2.2.2.2

/-- A wire value in the wire's domain whose journal is the window's and whose storage plus allowance is
below 2^64 decodes to its World. -/
theorem world_decode_wire_ok {E : Env D} {PD : D → Prop} {dc : Stream D} (hd : LawfulOn PD dc)
    {x : WorldWire D} (hx : WireFits E PD x) (hj : journalFits x.2.2.1 x.2.1.toList = true)
    (hw : cellsWeight x.1 + x.2.2.2.2.1 < 2 ^ 64) :
    (world E dc).decode ((worldWire E dc).bytes x) = .ok (ofWire x) := by
  have hb : (worldWire E dc).bytes x = (world E dc).bytes (ofWire x) := rfl
  rw [hb]
  exact world_decode_bytes hd ⟨hx.1, hx.2.1, hx.2.2.1, hx.2.2.2.1, hw, hx.2.2.2.2.2, hj⟩

/-- **The budget refusal** (cv 01a14ba9-cbf4): a wire value in the wire's domain, its journal the
window's, whose storage plus allowance is 2^64 or more, is refused `kernel/world-budget` by name, at offset 0,
although every counter in it fits its `u64`. -/
theorem world_decode_wire_overBudget {E : Env D} {PD : D → Prop} {dc : Stream D} (hd : LawfulOn PD dc)
    {x : WorldWire D} (hx : WireFits E PD x) (hj : journalFits x.2.2.1 x.2.1.toList = true)
    (hw : ¬ cellsWeight x.1 + x.2.2.2.2.1 < 2 ^ 64) :
    (world E dc).decode ((worldWire E dc).bytes x) = .error (.rejected 0 "kernel/world-budget") := by
  have hg := (worldWire_lawfulOn E hd).get_of_occurs x ((worldWire E dc).bytes x) 0 hx (occursAt_self _)
  simp only [world, decode, journalWire, refine, hg, hj, ite_true, if_neg hw]

/-- **The refusal**: the same wire value with a journal that is not the window's is refused
`kernel/journal` by name, at offset 0. -/
theorem world_decode_wire_refused {E : Env D} {PD : D → Prop} {dc : Stream D} (hd : LawfulOn PD dc)
    {x : WorldWire D} (hx : WireFits E PD x) (hj : journalFits x.2.2.1 x.2.1.toList = false) :
    (world E dc).decode ((worldWire E dc).bytes x) = .error (.rejected 0 "kernel/journal") := by
  have hg := (worldWire_lawfulOn E hd).get_of_occurs x ((worldWire E dc).bytes x) 0 hx (occursAt_self _)
  simp only [world, decode, journalWire, refine, hg, hj]
  rfl

end Nanodregg.Codec.Kernel
