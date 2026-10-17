import Codec.World
import Codec.Proofs.Kernel
import Kernel.Proofs.Equiv
import Kernel.Proofs.Cells
import Kernel.Proofs.Trie
import Std.Data.TreeMap

/-!
# The World codec (v3): canonical, the trie read back exactly, the journal up to `Equiv`

* `cells_lawfulOn`: the trie's listing is lawful on canonical tries whose every slot holds the leaf
  of its kind; whatever decodes is such a trie (`Trie.Canon`), rebuilt by `build` from its listing.
* `world_decode_bytes`: a fitting World decodes from its bytes to a World `Equiv` to it — the SAME
  trie (`=`), an `Equiv` journal, the same counters and origin.
* `eq_bytes_of_world_decode`: whatever decodes IS the encoding of what it decoded to.
* `world_decode_canon` / `world_decode_slotted` / `world_decode_cellsFit`: a decoded World satisfies the
  kernel's invariants (`World.Canon`, `World.Slotted`, `World.CellsFit Cell.Fits`), so every kernel
  theorem that takes them applies to a reopened base.
* `world_bytes_equiv`: `Equiv` Worlds have the same bytes.
-/

namespace Nanodregg.Codec.Kernel

open Nanodregg.Kernel Nanodregg.Codec.Stream Std

/-! ## Sorted lists and maps -/

section Sorted
variable {α β : Type} [Ord α] [TransOrd α] [LawfulEqOrd α]

theorem eq_of_sorted_of_mem_iff {f : β → α} :
    ∀ {l₁ l₂ : List β}, l₁.Pairwise (fun a b => compare (f a) (f b) = .lt) →
      l₂.Pairwise (fun a b => compare (f a) (f b) = .lt) → (∀ x, x ∈ l₁ ↔ x ∈ l₂) → l₁ = l₂
  | [], [], _, _, _ => rfl
  | [], b :: _, _, _, h => by simpa using (h b).mpr (List.mem_cons_self ..)
  | a :: _, [], _, _, h => by simpa using (h a).mp (List.mem_cons_self ..)
  | a :: l₁, b :: l₂, h₁, h₂, h => by
    rw [List.pairwise_cons] at h₁ h₂
    have lt_irrefl : ∀ x : β, compare (f x) (f x) ≠ .lt := fun x => by simp [compare_self]
    have hab : a = b := by
      have am := (h a).mp (List.mem_cons_self ..)
      have bm := (h b).mpr (List.mem_cons_self ..)
      rcases List.mem_cons.mp am with e | am
      · exact e
      rcases List.mem_cons.mp bm with e | bm
      · exact e.symm
      have x := h₂.1 a am
      have y := h₁.1 b bm
      exact absurd (OrientedCmp.gt_iff_lt.mpr y) (by rw [x]; decide)
    subst hab
    congr 1
    apply eq_of_sorted_of_mem_iff h₁.2 h₂.2
    intro x
    constructor
    · intro hx
      have := (h x).mp (List.mem_cons_of_mem _ hx)
      rcases List.mem_cons.mp this with e | e
      · subst e; exact absurd (h₁.1 x hx) (lt_irrefl x)
      · exact e
    · intro hx
      have := (h x).mpr (List.mem_cons_of_mem _ hx)
      rcases List.mem_cons.mp this with e | e
      · subst e; exact absurd (h₂.1 x hx) (lt_irrefl x)
      · exact e

theorem toList_ofList_of_sorted [DecidableEq α] (l : List (α × β))
    (h : l.Pairwise (fun a b => compare a.1 b.1 = .lt)) : (TreeMap.ofList l compare).toList = l := by
  have distinct : l.Pairwise (fun a b => ¬ compare a.1 b.1 = .eq) :=
    h.imp (fun hab => by rw [hab]; decide)
  apply eq_of_sorted_of_mem_iff (f := Prod.fst) TreeMap.ordered_keys_toList h
  intro ⟨k, v⟩
  rw [TreeMap.mem_toList_iff_getElem?_eq_some]
  constructor
  · intro hv
    by_cases hk : (l.map Prod.fst).contains k = true
    · obtain ⟨⟨k', v'⟩, hm, hk'⟩ : ∃ p ∈ l, p.1 = k := by simpa using hk
      simp only at hk'; subst hk'
      rw [TreeMap.getElem?_ofList_of_mem (k := k') compare_self distinct hm] at hv
      cases hv; exact hm
    · rw [TreeMap.getElem?_ofList_of_contains_eq_false (by simpa using hk)] at hv
      cases hv
  · intro hm
    exact TreeMap.getElem?_ofList_of_mem compare_self distinct hm

omit [LawfulEqOrd α] in
theorem ascendingBy_iff {f : β → α} :
    ∀ {l : List β}, ascendingBy f l = true ↔ l.Pairwise (fun a b => compare (f a) (f b) = .lt)
  | [] => by simp [ascendingBy]
  | [a] => by simp [ascendingBy]
  | a :: b :: rest => by
    rw [ascendingBy, Bool.and_eq_true, ascendingBy_iff, beq_iff_eq]
    constructor
    · rintro ⟨hab, hr⟩
      refine List.pairwise_cons.mpr ⟨fun x hx => ?_, hr⟩
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hab
      · exact TransCmp.lt_trans hab (List.pairwise_cons.mp hr |>.1 x hx)
    · intro h
      exact ⟨List.pairwise_cons.mp h |>.1 b (List.mem_cons_self ..), List.pairwise_cons.mp h |>.2⟩

end Sorted

/-! ## The wire's parts -/

variable {D : Type} [Ord D]

theorem ascendingList_lawfulOn {β : Type} {P : β → Prop} {c : Stream β} (hc : LawfulOn P c) (max : Nat)
    (fits : max < 2 ^ 32) (f : β → D) :
    LawfulOn (fun l => (l.length ≤ max ∧ ∀ x ∈ l, P x) ∧ ascendingBy f l = true) (ascendingList max f c) := by
  unfold ascendingList
  refine refine_lawfulOn_where (rawList_lawfulOn hc max fits) "kernel/ascending" ?_ ?_ ?_
  · intro y _ hq; simp [hq]
  · intro x y h; split at h <;> simp_all
  · intro x y h; split at h <;> simp_all

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
    LawfulOn (fun v => v.length ≤ max ∧ ∀ p ∈ v, Turn.Fits PD p.1 ∧ PD p.2) (batch max dc) :=
  rawList_lawfulOn (product_lawfulOn (turn_lawfulOn hd) hd) max fits

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

/-- The trie codec's domain: a canonical trie whose listing fits and whose slots hold the leaves of
their kinds. -/
def CellsFits (E : Env D) (PD : D → Prop) (t : Cells D) : Prop :=
  (TrieListFits PD t.toList ∧ ∀ p ∈ t.toList, Leaf.fits p.1 p.2 = true) ∧ Trie.Canon (trieSpec E) 0 t

omit [Ord D] in
theorem cells_lawfulOn (E : Env D) {PD : D → Prop} {dc : Stream D} (hd : LawfulOn PD dc) :
    LawfulOn (CellsFits E PD) (cells E dc) := by
  unfold cells
  refine (refine_lawfulOn_where (fitList_lawfulOn hd) "kernel/trie-order"
    (Q := fun t : Cells D => Trie.Canon (trieSpec E) 0 t) ?_ ?_ ?_).mono (fun _ h => h) (fun _ h => h)
  · intro y _ hq
    have hb : Trie.build (trieSpec E) (trieSpec E).depth 0 y.toList = y := by
      simpa using Trie.build_toList (trieSpec E) 0 y hq
    simp only [hb, beq_self_eq_true, leavesNodup_of_routed (trieSpec E) 0 y hq.1, Bool.and_self, if_true]
  · intro x y h
    simp only at h
    split at h
    · rename_i hc; cases h; simp only [Bool.and_eq_true, beq_iff_eq] at hc; exact hc.1
    · cases h
  · intro x y h
    simp only at h
    split at h
    · rename_i hc; cases h
      simp only [Bool.and_eq_true] at hc
      simpa using Trie.canon_build (trieSpec E) 0 x
        (nodup_of_leavesNodup_build (trieSpec E) _ 0 x hc.2)
    · cases h

/-! ## The World -/

/-- The wire's domain, as the product of its parts. -/
def WireFits (E : Env D) (PD : D → Prop) (x : WorldWire D) : Prop :=
  CellsFits E PD x.1 ∧
  ((x.2.1.length ≤ worldMax ∧ ∀ p ∈ x.2.1, PD p.1 ∧ p.2.1 < 2 ^ 64 ∧ PD p.2.2) ∧ ascendingBy Prod.fst x.2.1 = true) ∧
  x.2.2.1 < 2 ^ 64 ∧ PD x.2.2.2.1 ∧ x.2.2.2.2.1 < 2 ^ 64 ∧ PD x.2.2.2.2.2

theorem worldWire_lawfulOn (E : Env D) {PD : D → Prop} {dc : Stream D} (hd : LawfulOn PD dc) :
    LawfulOn (WireFits E PD) (worldWire E dc) :=
  (product_lawfulOn (cells_lawfulOn E hd)
    (product_lawfulOn (ascendingList_lawfulOn (product_lawfulOn hd (product_lawfulOn nat64_lawfulOn hd)) _
      (by decide) _)
      (product_lawfulOn nat64_lawfulOn (product_lawfulOn hd (product_lawfulOn nat64_lawfulOn hd))))).mono
    (fun _ h => h) (fun _ h => h)

/-- A World within the wire's bounds and the kernel's invariant: a canonical trie whose slots hold
the leaves of their kinds, at most `worldMax` entries per map, every digest in the digest codec's
domain, every counter below 2^64. -/
def World.CodecFits (E : Env D) (PD : D → Prop) (w : World D) : Prop :=
  CellsFits E PD w.trie ∧
  (w.journal.toList.length ≤ worldMax ∧ ∀ p ∈ w.journal.toList, PD p.1 ∧ p.2.1 < 2 ^ 64 ∧ PD p.2.2) ∧
  w.height < 2 ^ 64 ∧ PD w.chain ∧ w.allowance < 2 ^ 64 ∧ PD w.origin

theorem world_bytes (E : Env D) (dc : Stream D) (w : World D) :
    (world E dc).bytes w = (worldWire E dc).bytes (toWire w) := rfl

theorem world_decode (E : Env D) (dc : Stream D) (b : ByteArray) :
    (world E dc).decode b = match (worldWire E dc).decode b with
      | .ok x => .ok (ofWire x)
      | .error e => .error e := by
  unfold decode
  simp only [world]
  split <;> rename_i h <;> split at h <;> simp_all <;> split <;> simp_all

variable [TransOrd D] [LawfulEqOrd D]

omit [LawfulEqOrd D] [DecidableEq D] in
theorem toWire_fits {E : Env D} {PD : D → Prop} {w : World D} (hw : World.CodecFits E PD w) :
    WireFits E PD (toWire w) :=
  ⟨hw.1, ⟨hw.2.1, ascendingBy_iff.mpr TreeMap.ordered_keys_toList⟩, hw.2.2⟩

theorem ofWire_toWire_equiv (w : World D) : (ofWire (toWire w)).Equiv w :=
  ⟨rfl, TreeMap.equiv_iff_toList_eq.mpr (toList_ofList_of_sorted _ TreeMap.ordered_keys_toList),
   rfl, rfl, rfl, rfl⟩

theorem toWire_ofWire {E : Env D} {PD : D → Prop} {x : WorldWire D} (hx : WireFits E PD x) :
    toWire (ofWire x) = x := by
  obtain ⟨c, j, h, ch, a, o⟩ := x
  simp only [toWire, ofWire]
  rw [toList_ofList_of_sorted _ (ascendingBy_iff.mp hx.2.1.2)]

/-- A fitting World reads back from its bytes: the same trie, an `Equiv` journal. -/
theorem world_decode_bytes {E : Env D} {PD : D → Prop} {dc : Stream D} (hd : LawfulOn PD dc) {w : World D}
    (hw : World.CodecFits E PD w) : ∃ w', (world E dc).decode ((world E dc).bytes w) = .ok w' ∧ w'.Equiv w := by
  refine ⟨ofWire (toWire w), ?_, ofWire_toWire_equiv w⟩
  rw [world_decode, world_bytes, (worldWire_lawfulOn E hd).decode_bytes (toWire_fits hw)]

/-- Canonicity: whatever decodes to `w` is exactly `w`'s bytes. -/
theorem eq_bytes_of_world_decode {E : Env D} {PD : D → Prop} {dc : Stream D} (hd : LawfulOn PD dc)
    {b : ByteArray} {w : World D} (h : (world E dc).decode b = .ok w) : b = (world E dc).bytes w := by
  rw [world_decode] at h
  split at h
  · rename_i x hx
    cases h
    obtain ⟨hf, rfl⟩ := (worldWire_lawfulOn E hd).eq_bytes_of_decode hx
    rw [world_bytes, toWire_ofWire hf]
  · cases h

omit [TransOrd D] [LawfulEqOrd D] in
/-- A decoded World satisfies the kernel's invariant, and every slot holds the leaf of its kind. -/
theorem world_decode_canon {E : Env D} {PD : D → Prop} {dc : Stream D} (hd : LawfulOn PD dc)
    {b : ByteArray} {w : World D} (h : (world E dc).decode b = .ok w) :
    w.Canon E ∧ ∀ p ∈ w.trie.toList, Leaf.fits p.1 p.2 = true := by
  rw [world_decode] at h
  split at h
  · rename_i x hx
    cases h
    obtain ⟨hf, _⟩ := (worldWire_lawfulOn E hd).eq_bytes_of_decode hx
    exact ⟨hf.1.2, hf.1.1.2⟩
  · cases h

omit [TransOrd D] [LawfulEqOrd D] in
/-- What a World read returns at any offset — the World as a COMPONENT of a larger record (HOST's base) —
satisfies the kernel's trie invariant, and every slot holds the leaf of its kind. -/
theorem world_get_canon {E : Env D} {PD : D → Prop} {dc : Stream D} (hd : LawfulOn PD dc)
    {b : ByteArray} {i j : Nat} {w : World D} (h : (world E dc).get b i = .ok (w, j)) :
    w.Canon E ∧ ∀ p ∈ w.trie.toList, Leaf.fits p.1 p.2 = true := by
  simp only [world] at h
  split at h
  · rename_i x j' hx
    cases h
    obtain ⟨hf, _⟩ := (worldWire_lawfulOn E hd).occurs_of_get hx
    exact ⟨hf.1.2, hf.1.1.2⟩
  · cases h

omit [TransOrd D] [LawfulEqOrd D] in
/-- A decoded World has every slot holding the leaf of its kind (the kernel's `World.Slotted`). -/
theorem world_decode_slotted {E : Env D} {PD : D → Prop} {dc : Stream D} (hd : LawfulOn PD dc)
    {b : ByteArray} {w : World D} (h : (world E dc).decode b = .ok w) : w.Slotted E := by
  obtain ⟨hc, hf⟩ := world_decode_canon hd h
  intro s l hg
  exact hf (s, l) ((Trie.mem_toList (trieSpec E) 0 w.trie hc.1 s l).mpr hg)

omit [TransOrd D] [LawfulEqOrd D] in
/-- Every live cell of a decoded World is in the cell codec's domain (`Cell.Fits`): a reopened base
carries the kernel's `World.CellsFit` from the codec, so only admission has to keep it (KERNEL-31). -/
theorem world_decode_cellsFit {E : Env D} {PD : D → Prop} {dc : Stream D} (hd : LawfulOn PD dc)
    {b : ByteArray} {w : World D} (h : (world E dc).decode b = .ok w) : w.CellsFit Cell.Fits E := by
  rw [world_decode] at h
  split at h
  · rename_i x hx
    cases h
    obtain ⟨hf, _⟩ := (worldWire_lawfulOn E hd).eq_bytes_of_decode hx
    intro s l hg
    have hm := (Trie.mem_toList (trieSpec E) 0 x.1 hf.1.2.1 s l).mpr hg
    have hl := (hf.1.1.1.2 (s, l) hm).2
    cases l with
    | entry e =>
      cases e with
      | live c => exact hl
      | tomb => trivial
    | spent => trivial
  · cases h

omit [LawfulEqOrd D] in
/-- Extensionally equal Worlds have the same bytes: a checkpoint is a function of the contents. -/
theorem world_bytes_equiv (E : Env D) (dc : Stream D) {w w' : World D} (h : w.Equiv w') :
    (world E dc).bytes w = (world E dc).bytes w' := by
  obtain ⟨ht, hj, hh, hch, ha, ho⟩ := h
  rw [world_bytes, world_bytes]
  simp only [toWire, ht, hj.toList_eq, hh, hch, ha, ho]

end Nanodregg.Codec.Kernel
