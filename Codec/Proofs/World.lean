import Codec.World
import Codec.Proofs.Kernel
import Kernel.Proofs.Equiv
import Std.Data.TreeMap
import Std.Data.TreeSet

/-!
# The World codec: canonical, and read back up to extensional equality

* `world_decode_bytes`: a World within the wire's bounds decodes from its bytes to a World
  `Equiv` to it (same cells, journal, spent set, height, chain and allowance).
* `eq_bytes_of_world_decode`: whatever decodes IS the encoding of what it decoded to, so a base file
  has exactly one spelling.
* `world_bytes_equiv`: `Equiv` Worlds have the same bytes, so a checkpoint's digest is a function
  of the World's contents.
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

theorem toList_ofList_set_of_sorted [DecidableEq α] (l : List α)
    (h : l.Pairwise (fun a b => compare a b = .lt)) : (TreeSet.ofList l compare).toList = l := by
  have h1 : (TreeSet.ofList l compare).toList.Pairwise (fun a b => compare a b = .lt) :=
    TreeSet.ordered_toList
  refine eq_of_sorted_of_mem_iff (f := fun x => x) h1 h ?_
  intro x
  rw [TreeSet.mem_toList]
  simp [TreeSet.mem_ofList]

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
    LawfulOn (fun v => (v.1.length ≤ max ∧ ∀ t ∈ v.1, Turn.Fits PD t) ∧ PD v.2) (batch max dc) :=
  product_lawfulOn (rawList_lawfulOn (turn_lawfulOn hd) max fits) hd

/-! ## The World -/

/-- The wire's domain, as the product of its parts. -/
def WireFits (PD : D → Prop) (x : WorldWire D) : Prop :=
  ((x.1.length ≤ worldMax ∧ ∀ p ∈ x.1, PD p.1 ∧ Entry.Fits p.2) ∧ ascendingBy Prod.fst x.1 = true) ∧
  ((x.2.1.length ≤ worldMax ∧ ∀ p ∈ x.2.1, PD p.1 ∧ p.2.1 < 2 ^ 64 ∧ PD p.2.2) ∧ ascendingBy Prod.fst x.2.1 = true) ∧
  ((x.2.2.1.length ≤ worldMax ∧ ∀ d ∈ x.2.2.1, PD d) ∧ ascendingBy id x.2.2.1 = true) ∧
  x.2.2.2.1 < 2 ^ 64 ∧ PD x.2.2.2.2.1 ∧ x.2.2.2.2.2 < 2 ^ 64

theorem worldWire_lawfulOn {PD : D → Prop} {dc : Stream D} (hd : LawfulOn PD dc) :
    LawfulOn (WireFits PD) (worldWire dc) :=
  (product_lawfulOn (ascendingList_lawfulOn (product_lawfulOn hd entry_lawfulOn) _ (by decide) _)
    (product_lawfulOn (ascendingList_lawfulOn (product_lawfulOn hd (product_lawfulOn nat64_lawfulOn hd)) _
      (by decide) _)
      (product_lawfulOn (ascendingList_lawfulOn hd _ (by decide) _)
        (product_lawfulOn nat64_lawfulOn (product_lawfulOn hd nat64_lawfulOn))))).mono
    (fun _ h => h) (fun _ h => h)

/-- A World within the wire's bounds: at most `worldMax` entries per map, every digest in the
digest codec's domain, every counter below 2^64. -/
def World.Fits (PD : D → Prop) (w : World D) : Prop :=
  (w.cells.toList.length ≤ worldMax ∧ ∀ p ∈ w.cells.toList, PD p.1 ∧ Entry.Fits p.2) ∧
  (w.journal.toList.length ≤ worldMax ∧ ∀ p ∈ w.journal.toList, PD p.1 ∧ p.2.1 < 2 ^ 64 ∧ PD p.2.2) ∧
  (w.spent.toList.length ≤ worldMax ∧ ∀ d ∈ w.spent.toList, PD d) ∧
  w.height < 2 ^ 64 ∧ PD w.chain ∧ w.allowance < 2 ^ 64

theorem world_bytes (dc : Stream D) (w : World D) : (world dc).bytes w = (worldWire dc).bytes (toWire w) := rfl

theorem world_decode (dc : Stream D) (b : ByteArray) :
    (world dc).decode b = match (worldWire dc).decode b with
      | .ok x => .ok (ofWire x)
      | .error e => .error e := by
  unfold decode
  simp only [world]
  split <;> rename_i h <;> split at h <;> simp_all <;> split <;> simp_all

variable [TransOrd D] [LawfulEqOrd D] [DecidableEq D]

omit [LawfulEqOrd D] [DecidableEq D] in
theorem toWire_fits {PD : D → Prop} {w : World D} (hw : World.Fits PD w) : WireFits PD (toWire w) :=
  ⟨⟨hw.1, ascendingBy_iff.mpr TreeMap.ordered_keys_toList⟩,
   ⟨hw.2.1, ascendingBy_iff.mpr TreeMap.ordered_keys_toList⟩,
   ⟨hw.2.2.1, ascendingBy_iff.mpr (show w.spent.toList.Pairwise (fun a b => compare a b = .lt) from
      TreeSet.ordered_toList)⟩, hw.2.2.2⟩

theorem ofWire_toWire_equiv (w : World D) : (ofWire (toWire w)).Equiv w :=
  ⟨TreeMap.equiv_iff_toList_eq.mpr (toList_ofList_of_sorted _ TreeMap.ordered_keys_toList),
   TreeMap.equiv_iff_toList_eq.mpr (toList_ofList_of_sorted _ TreeMap.ordered_keys_toList),
   TreeSet.equiv_iff_toList_eq.mpr (toList_ofList_set_of_sorted _ TreeSet.ordered_toList),
   rfl, rfl, rfl⟩

theorem toWire_ofWire {PD : D → Prop} {x : WorldWire D} (hx : WireFits PD x) : toWire (ofWire x) = x := by
  obtain ⟨c, j, sp, h, ch, a⟩ := x
  simp only [toWire, ofWire]
  rw [toList_ofList_of_sorted _ (ascendingBy_iff.mp hx.1.2), toList_ofList_of_sorted _ (ascendingBy_iff.mp hx.2.1.2),
    toList_ofList_set_of_sorted _ (ascendingBy_iff.mp hx.2.2.1.2)]

/-- A fitting World reads back from its bytes, up to extensional equality. -/
theorem world_decode_bytes {PD : D → Prop} {dc : Stream D} (hd : LawfulOn PD dc) {w : World D}
    (hw : World.Fits PD w) : ∃ w', (world dc).decode ((world dc).bytes w) = .ok w' ∧ w'.Equiv w := by
  refine ⟨ofWire (toWire w), ?_, ofWire_toWire_equiv w⟩
  rw [world_decode, world_bytes, (worldWire_lawfulOn hd).decode_bytes (toWire_fits hw)]

/-- Canonicity: whatever decodes to `w` is exactly `w`'s bytes. -/
theorem eq_bytes_of_world_decode {PD : D → Prop} {dc : Stream D} (hd : LawfulOn PD dc) {b : ByteArray}
    {w : World D} (h : (world dc).decode b = .ok w) : b = (world dc).bytes w := by
  rw [world_decode] at h
  split at h
  · rename_i x hx
    cases h
    obtain ⟨hf, rfl⟩ := (worldWire_lawfulOn hd).eq_bytes_of_decode hx
    rw [world_bytes, toWire_ofWire hf]
  · cases h

omit [LawfulEqOrd D] [DecidableEq D] in
/-- Extensionally equal Worlds have the same bytes: a checkpoint is a function of the contents. -/
theorem world_bytes_equiv (dc : Stream D) {w w' : World D} (h : w.Equiv w') :
    (world dc).bytes w = (world dc).bytes w' := by
  obtain ⟨hc, hj, hs, hh, hch, ha⟩ := h
  rw [world_bytes, world_bytes]
  simp only [toWire, hc.toList_eq, hj.toList_eq, hs.toList_eq, hh, hch, ha]

end Nanodregg.Codec.Kernel
