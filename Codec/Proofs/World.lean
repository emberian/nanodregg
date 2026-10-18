import Codec.World
import Codec.Proofs.Kernel
import Codec.Proofs.Varint
import Kernel.Proofs.Cells
import Kernel.Proofs.Trie
import Kernel.Proofs.Journal
import Kernel.Proofs.Refusals

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
  | .live c v => Cell.Fits c ∧ v < 2 ^ 64
  | .tomb => True

abbrev EntryWireFits : (s : Fin 2) → EntryF s → Prop
  | 0 => fun x => x.1 < 2 ^ 64 ∧ Cell.Fits x.2
  | 1 => fun _ => True

theorem entryWire_lawfulOn : ∀ s, LawfulOn (EntryWireFits s) (entryWire s)
  | 0 => product_lawfulOn varint64_lawfulOn cell_lawfulOn
  | 1 => unit_lawful.on

/-- **The entry codec is lawful on the entries within bounds** (a cell in the cell codec's domain, a
version below 2^64), so a decoded entry has exactly one spelling: its version's varint is the shortest. -/
theorem entry_lawfulOn : LawfulOn Entry.Fits entry := by
  unfold entry
  refine (refine_lawfulOn (choice_lawfulOn 2 (by decide) entryWire_lawfulOn) "kernel/entry" ?_ ?_).mono ?_ ?_
  · intro y _; cases y <;> rfl
  · intro x y h
    obtain ⟨s, v⟩ := x
    match s, v, h with
    | 0, (_, _), h => simp at h; subst h; rfl
    | 1, (), h => simp at h; subst h; rfl
  · intro y h; cases y with
    | live c v => exact ⟨h.2, h.1⟩
    | tomb => trivial
  · intro y h; cases y with
    | live c v => exact ⟨h.2, h.1⟩
    | tomb => exact trivial

/-- **Canonicity, exact**: bytes decode to an entry iff the entry is within bounds and the bytes are
its one spelling (so a live entry whose version is written in a non-minimal varint is refused). -/
theorem entry_decode_iff {b : ByteArray} {e : Entry} : entry.decode b = .ok e ↔ Entry.Fits e ∧ b = entry.bytes e :=
  entry_lawfulOn.decode_eq_ok_iff

omit [Ord D] in

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
  | .entry (.live _ _), h => h
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
    leaf.decode b ≠ .ok (.entry (.live ⟨2 ^ 32, .ram, []⟩ 0)) := fun h =>
  absurd (leaf_decode_cellFit h).1.1.1 (by decide)

/-- Tooth: the version is bounded too — no bytes decode to a live leaf at version 2^64 (past the
counter limit), so `CellFit`'s version conjunct is not `True` either. -/
theorem leaf_decode_refuses_version (b : ByteArray) :
    leaf.decode b ≠ .ok (.entry (.live ⟨0, .ram, []⟩ (2 ^ 64))) := fun h =>
  absurd (leaf_decode_cellFit h).1.2 (by decide)

section Leaves
variable {K V D' : Type} [DecidableEq K] (S : Trie.Spec K V D')

theorem leavesNodup_of_routed : ∀ (d : Nat) (t : Trie.T K V D'), Trie.Routed S d t → leavesNodup t = true
  | _, .empty, _ => rfl
  | _, .leaf _ _, h => by simpa [leavesNodup] using h
  | _, .node _ b _ l r, h => by
      simp only [leavesNodup, Bool.and_eq_true]
      exact ⟨leavesNodup_of_routed (b + 1) l h.2.2.2.2.1, leavesNodup_of_routed (b + 1) r h.2.2.2.2.2⟩

/-- A rebuilt trie whose leaves hold each key once came from a listing that holds each key once. -/
theorem nodup_of_leavesNodup_build : ∀ (f d : Nat) (l : List (K × V)),
    leavesNodup (Trie.build S f d l) = true → (l.map Prod.fst).Nodup
  | _, _, [], _ => by simp
  | _, _, [_], _ => by simp
  | 0, _, a :: b :: rest, h => by simpa [Trie.build, Trie.mkLeaf, leavesNodup] using h
  | f + 1, d, a :: b :: rest, h => by
      cases hsb : Trie.splitBit S d (a :: b :: rest) with
      | none => simpa [Trie.build, hsb, Trie.mkLeaf, leavesNodup] using h
      | some c =>
      simp only [Trie.build, hsb, Trie.mkNode, leavesNodup, Bool.and_eq_true] at h
      have hl := nodup_of_leavesNodup_build f (c + 1) _ h.1
      have hr := nodup_of_leavesNodup_build f (c + 1) _ h.2
      have hp := List.filter_append_perm (fun p : K × V => !S.bit p.1 c) (a :: b :: rest)
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

/-! ## The refusals' keys and leaves (KERNEL-44) -/

/-- A refusals key in the digest codec's domain: its id, its member, or (a total, KERNEL-55 R1) the
origin it is filed under. -/
def RefusalSlot.Fits (PD : D → Prop) : RefusalSlot D → Prop
  | .tx i => PD i
  | .count m _ => PD m
  | .total o _ => PD o

abbrev RefusalSlotWireFits (PD : D → Prop) : (s : Fin 3) → RefusalSlotF D s → Prop
  | 0 => PD
  | 1 => fun p => PD p.1 ∧ True
  | 2 => fun p => PD p.1 ∧ True

omit [Ord D] in
theorem refusalSlotWire_lawfulOn {PD : D → Prop} {dc : Stream D} (hd : LawfulOn PD dc) :
    ∀ s, LawfulOn (RefusalSlotWireFits PD s) (refusalSlotWire dc s)
  | 0 => hd
  | 1 => product_lawfulOn hd u64_lawful.on
  | 2 => product_lawfulOn hd u64_lawful.on

omit [Ord D] in
theorem refusalSlot_lawfulOn {PD : D → Prop} {dc : Stream D} (hd : LawfulOn PD dc) :
    LawfulOn (RefusalSlot.Fits PD) (refusalSlot dc) := by
  unfold refusalSlot
  refine (refine_lawfulOn (choice_lawfulOn 3 (by decide) (refusalSlotWire_lawfulOn hd)) "kernel/refusal-slot"
    ?_ ?_).mono ?_ ?_
  · intro y _; cases y <;> rfl
  · intro x y h
    obtain ⟨s, v⟩ := x
    match s, v, h with
    | 0, i, h => simp at h; subst h; rfl
    | 1, (m, w), h => simp at h; subst h; rfl
    | 2, (o, w), h => simp at h; subst h; rfl
  · intro y h; cases y with
    | tx i => exact h
    | count m w => exact h.1
    | total o w => exact h.1
  · intro y h; cases y with
    | tx i => exact h
    | count m w => exact ⟨h, trivial⟩
    | total o w => exact ⟨h, trivial⟩

/-- A refusals leaf's counters below 2^64 (what the leaf digest needs to be injective,
`refusalDigest_inj`). -/
def RefusalLeaf.Fits : RefusalLeaf D → Prop
  | .refused h c _ => h < 2 ^ 64 ∧ c < 2 ^ 64
  | .count n => n < 2 ^ 64

/-- A refusals leaf in the leaf codec's domain: its counters below 2^64, and a refused leaf's member
in the digest codec's. -/
def RefusalLeaf.WireFits (PD : D → Prop) : RefusalLeaf D → Prop
  | .refused h c m => (h < 2 ^ 64 ∧ c < 2 ^ 64) ∧ PD m
  | .count n => n < 2 ^ 64

omit [Ord D] in
/-- A leaf whose counters fit is in the leaf codec's domain wherever every digest is in the digest
codec's (the deployed codec's, `fun _ => True`). -/
theorem RefusalLeaf.wireFits_of_fits {PD : D → Prop} (hpd : ∀ d, PD d) :
    ∀ {l : RefusalLeaf D}, RefusalLeaf.Fits l → RefusalLeaf.WireFits PD l
  | .refused _ _ m, h => ⟨h, hpd m⟩
  | .count _, h => h

abbrev RefusalLeafWireFits (PD : D → Prop) : (s : Fin 2) → RefusalLeafF D s → Prop
  | 0 => fun p => p.1 < 2 ^ 64 ∧ p.2.1 < 2 ^ 64 ∧ PD p.2.2
  | 1 => fun n => n < 2 ^ 64

omit [Ord D] in
theorem refusalLeafWire_lawfulOn {PD : D → Prop} {dc : Stream D} (hd : LawfulOn PD dc) :
    ∀ s, LawfulOn (RefusalLeafWireFits PD s) (refusalLeafWire dc s)
  | 0 => product_lawfulOn nat64_lawfulOn (product_lawfulOn nat64_lawfulOn hd)
  | 1 => nat64_lawfulOn

omit [Ord D] in
theorem refusalLeaf_lawfulOn {PD : D → Prop} {dc : Stream D} (hd : LawfulOn PD dc) :
    LawfulOn (RefusalLeaf.WireFits PD) (refusalLeaf dc) := by
  unfold refusalLeaf
  refine (refine_lawfulOn (choice_lawfulOn 2 (by decide) (refusalLeafWire_lawfulOn hd)) "kernel/refusal-leaf"
    ?_ ?_).mono ?_ ?_
  · intro y _; cases y <;> rfl
  · intro x y h
    obtain ⟨s, v⟩ := x
    match s, v, h with
    | 0, (a, c, m), h => simp at h; subst h; rfl
    | 1, n, h => simp at h; subst h; rfl
  · intro y h; cases y with
    | refused a c m => exact ⟨⟨h.1, h.2.1⟩, h.2.2⟩
    | count n => exact h
  · intro y h; cases y with
    | refused a c m => exact ⟨h.1.1, h.1.2, h.2⟩
    | count n => exact h

/-! ## The log's steps (KERNEL-47) -/

/-- A recorded refusal in the codec's domain: both digests in the digest codec's, every counter below
2^64, the call's bytes at most `callMax` (what KERNEL's `checkRefusedBounds` checks). -/
def Refused.Fits (PD : D → Prop) (r : Refused D) : Prop :=
  PD r.txId ∧ PD r.member ∧ r.notBefore < 2 ^ 64 ∧ r.validUntil < 2 ^ 64 ∧ r.code < 2 ^ 64 ∧
    r.event.size ≤ callMax

omit [Ord D] in
theorem refused_lawfulOn {PD : D → Prop} {dc : Stream D} (hd : LawfulOn PD dc) :
    LawfulOn (Refused.Fits PD) (refused dc) := by
  unfold refused
  refine (refine_lawfulOn
    (product_lawfulOn hd (product_lawfulOn hd (product_lawfulOn nat64_lawfulOn (product_lawfulOn nat64_lawfulOn
      (product_lawfulOn nat64_lawfulOn (rawBytes_lawfulOn _ (by decide)))))))
    "kernel/refused" ?_ ?_).mono ?_ ?_
  · intro y _; rfl
  · intro x y h; simp at h; subst h; rfl
  · intro y h; exact h
  · intro y h; exact h

omit [Ord D] in
/-- Every refusal KERNEL records is in the codec's domain (at any digest codec total on `PD`). -/
theorem checkRefusedBounds_fits (r : Refused D) (h : checkRefusedBounds r = .ok ()) :
    Refused.Fits (fun _ => True) r := by
  simp only [checkRefusedBounds, req, decide_eq_true_eq] at h
  simp only [bind_req, ite_req, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hE, ⟨⟨hN, hV⟩, hC⟩, -⟩ := h
  exact ⟨trivial, trivial, by simpa [Bounds.counterLimit] using hN, by simpa [Bounds.counterLimit] using hV,
    by simpa [Bounds.counterLimit] using hC, hE⟩

def Step.Fits (PD : D → Prop) : Step D → Prop
  | .turn t => Turn.Fits PD t
  | .refusal r => Refused.Fits PD r

abbrev StepWireFits (PD : D → Prop) : (s : Fin 2) → StepF D s → Prop
  | 0 => Turn.Fits PD
  | 1 => Refused.Fits PD

omit [Ord D] in
theorem stepWire_lawfulOn {PD : D → Prop} {dc : Stream D} (hd : LawfulOn PD dc) :
    ∀ s, LawfulOn (StepWireFits PD s) (stepWire dc s)
  | 0 => turn_lawfulOn hd
  | 1 => refused_lawfulOn hd

omit [Ord D] in
theorem step_lawfulOn {PD : D → Prop} {dc : Stream D} (hd : LawfulOn PD dc) :
    LawfulOn (Step.Fits PD) (step dc) := by
  unfold step
  refine (refine_lawfulOn (choice_lawfulOn 2 (by decide) (stepWire_lawfulOn hd)) "kernel/step" ?_ ?_).mono ?_ ?_
  · intro y _; cases y <;> rfl
  · intro x y h
    obtain ⟨s, v⟩ := x
    match s, v, h with
    | 0, t, h => simp at h; subst h; rfl
    | 1, r, h => simp at h; subst h; rfl
  · intro y h; cases y <;> exact h
  · intro y h; cases y <;> exact h

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

omit [Ord D] [DecidableEq D] in
/-- A batch record: at most `max` steps, each in the step codec's domain, each roots digest in the
digest codec's. -/
theorem batch_lawfulOn {PD : D → Prop} {dc : Stream D} (hd : LawfulOn PD dc) (max : Nat) (fits : max < 2 ^ 32) :
    LawfulOn (fun v => v.length ≤ max ∧ ∀ p ∈ v, Step.Fits PD p.1 ∧ PD p.2) (batch max dc) :=
  rawList_lawfulOn (product_lawfulOn (step_lawfulOn hd) hd) max fits

/-- The refusals listing's domain: within the wire's bound, every key and leaf in its codec's domain. -/
def RefusalListFits (PD : D → Prop) (l : List (RefusalSlot D × RefusalLeaf D)) : Prop :=
  l.length ≤ worldMax ∧ ∀ p ∈ l, RefusalSlot.Fits PD p.1 ∧ RefusalLeaf.WireFits PD p.2

/-- The refusals codec's domain: a canonical refusals trie whose listing fits (KERNEL-44). -/
def RefusalsTrieFits (E : Env D) (PD : D → Prop) (r : Refusals D) : Prop :=
  RefusalListFits PD r.toList ∧ Trie.Canon (refusalSpec E) 0 r

omit [Ord D] [DecidableEq D] in
/-- Every leaf of a refusals listing `refusalsFits` admits is in the leaf codec's domain: the window
check bounds every counter, so a reached World's refusals (KERNEL's `fold_refusalsOk`) need only the
listing's length for the wire. -/
theorem refusalLeaf_fits_of_refusalsFits {H : Nat} {l : List (RefusalSlot D × RefusalLeaf D)}
    (h : refusalsFits H l = true) : ∀ p ∈ l, RefusalLeaf.Fits p.2 := by
  intro p hp
  have hq := List.all_eq_true.mp h p hp
  obtain ⟨k, v⟩ := p
  cases k <;> cases v <;> simp_all [RefusalLeaf.Fits, refusalFits, Bounds.counterLimit, Bounds.refusalsPerWindow, Bounds.refusalsPerWindowMax] <;>
    omega

omit [Ord D] in
theorem refusalsTrie_lawfulOn (E : Env D) {PD : D → Prop} {dc : Stream D} (hd : LawfulOn PD dc) :
    LawfulOn (RefusalsTrieFits E PD) (refusalsTrie E dc) :=
  trieListing_lawfulOn (refusalSpec E)
    ((rawList_lawfulOn (product_lawfulOn (refusalSlot_lawfulOn hd) (refusalLeaf_lawfulOn hd)) _ (by decide)).mono
      (fun _ h => h) (fun _ h => h)) "kernel/refusal-order"

/-! ## The rows (KERNEL-46/48) -/

/-- The rows listing's domain: within the wire's bound, every key and leaf in its codec's domain. -/
def RowListFits (PD : D → Prop) (l : List (RowSlot D × RowLeaf)) : Prop :=
  l.length ≤ worldMax ∧ ∀ p ∈ l, RowSlot.Fits PD p.1 ∧ RowLeaf.Fits p.2

/-- The rows codec's domain: a canonical rows trie whose listing fits. -/
def RowsTrieFits (E : Env D) (PD : D → Prop) (r : Rows D) : Prop :=
  RowListFits PD r.toList ∧ Trie.Canon (rowSpec E) 0 r

omit [Ord D] in
theorem rowsTrie_lawfulOn (E : Env D) {PD : D → Prop} {dc : Stream D} (hd : LawfulOn PD dc) :
    LawfulOn (RowsTrieFits E PD) (rowsTrie E dc) :=
  trieListing_lawfulOn (rowSpec E)
    ((rawList_lawfulOn (product_lawfulOn (rowKey_lawfulOn hd) rowLeaf_lawfulOn) _ (by decide)).mono
      (fun _ h => h) (fun _ h => h)) "kernel/row-order"

omit [Ord D] [DecidableEq D] in
/-- Every leaf of a rows listing `rowsFits` admits is in the leaf codec's domain: the kernel's bounds
bound every counter, so a reached World's rows need only the listing's length for the wire. -/
theorem rowLeaf_fits_of_rowsFits {E : Env D} {l : List (RowSlot D × RowLeaf)}
    (h : rowsFits E l = true) : ∀ p ∈ l, RowLeaf.Fits p.2 := by
  intro p hp
  have hq := List.all_eq_true.mp (Bool.and_eq_true _ _ |>.mp h).2 p hp
  obtain ⟨k, v⟩ := p
  cases k <;> cases v <;> simp_all [RowLeaf.Fits, rowFits, Bounds.counterLimit, Bounds.rowsPerRelationMax,
    Bounds.keyBytesMax] <;> omega

/-- A World's rows in the codec's domain (KERNEL-48), one field of `World.CodecFits` with a field per
site (the World's sites named; the carried state's are `kernel/carried-rows`, `-headed`, `-parented`). -/
structure RowsCodecFits (E : Env D) (PD : D → Prop) (t : Cells D) (r : Rows D) : Prop where
  /-- a canonical rows trie whose listing fits the wire (kernel/row-key, kernel/row-leaf,
  kernel/row-order) -/
  listing : RowsTrieFits E PD r
  /-- every entry within KERNEL's bounds, the listing ascending by key bytes (kernel/rows) -/
  fits : rowsFits E r.toList = true
  /-- every row has its head at the head's width, every head counts and sums its rows
  (kernel/rows-headed) -/
  headed : rowsHeaded r.toList = true
  /-- every relation's parent is a live cell of `t` (kernel/rows-parented) -/
  parented : rowsParented E t r = true

/-! ## The World -/

/-- The wire's domain, as the product of its parts. -/
def WireFits (E : Env D) (PD : D → Prop) (x : WorldWire D) : Prop :=
  CellsFits E PD x.1 ∧ JournalTrieFits E PD x.2.1 ∧ RefusalsTrieFits E PD x.2.2.1 ∧ RowsTrieFits E PD x.2.2.2.1 ∧
  x.2.2.2.2.1 < 2 ^ 64 ∧ x.2.2.2.2.2.1 < 2 ^ 64 ∧ PD x.2.2.2.2.2.2.1 ∧ x.2.2.2.2.2.2.2.1 < 2 ^ 64 ∧
  PD x.2.2.2.2.2.2.2.2

omit [Ord D] in
theorem worldWire_lawfulOn (E : Env D) {PD : D → Prop} {dc : Stream D} (hd : LawfulOn PD dc) :
    LawfulOn (WireFits E PD) (worldWire E dc) :=
  (product_lawfulOn (cells_lawfulOn E hd)
    (product_lawfulOn (journalTrie_lawfulOn E hd)
      (product_lawfulOn (refusalsTrie_lawfulOn E hd)
        (product_lawfulOn (rowsTrie_lawfulOn E hd)
          (product_lawfulOn nat64_lawfulOn (product_lawfulOn nat64_lawfulOn
            (product_lawfulOn hd (product_lawfulOn nat64_lawfulOn hd)))))))).mono
    (fun _ h => h) (fun _ h => h)

/-- `refine name c (if q x then some x else none) id` is lawful on `c`'s domain where `q` holds: the
shape of `kernel/journal`, `kernel/refusals` and `kernel/steps`, three checks over the World wire. -/
theorem refineIf_lawfulOn {α : Type} {P : α → Prop} {c : Stream α} (hc : LawfulOn P c) (name : String)
    (q : α → Prop) [DecidablePred q] :
    LawfulOn (fun x => P x ∧ q x) (refine name c (fun x => if q x then some x else none) id) := by
  refine (refine_lawfulOn_where hc name (Q := q) ?_ ?_ ?_).mono (fun _ h => h) (fun _ h => h)
  · intro y _ hq; simp [hq]
  · intro x y h; split at h <;> simp_all
  · intro x y h; split at h
    · rename_i hq; cases h; exact hq
    · cases h

/-- The journal-checked wire's domain: the wire's, and a journal that is the window's. -/
def JournalWireFits (E : Env D) (PD : D → Prop) (x : WorldWire D) : Prop :=
  WireFits E PD x ∧ journalFits (ofWire x).height (ofWire x).journal.toList = true

/-- **`kernel/journal` is lawful on exactly the journals `journalFits` admits.** -/
theorem journalWire_lawfulOn (E : Env D) {PD : D → Prop} {dc : Stream D} (hd : LawfulOn PD dc) :
    LawfulOn (JournalWireFits E PD) (journalWire E dc) :=
  refineIf_lawfulOn (worldWire_lawfulOn E hd) "kernel/journal" (fun x => journalFits (ofWire x).height (ofWire x).journal.toList = true)

/-- The refusals-checked wire's domain: the journal-checked one's, and refusals that are the window's. -/
def RefusalsWireFits (E : Env D) (PD : D → Prop) (x : WorldWire D) : Prop :=
  JournalWireFits E PD x ∧ refusalsFits (ofWire x).height (ofWire x).refusals.toList = true

/-- **`kernel/refusals` is lawful on exactly the refusals `refusalsFits` admits.** -/
theorem refusalsWire_lawfulOn (E : Env D) {PD : D → Prop} {dc : Stream D} (hd : LawfulOn PD dc) :
    LawfulOn (RefusalsWireFits E PD) (refusalsWire E dc) :=
  refineIf_lawfulOn (journalWire_lawfulOn E hd) "kernel/refusals" (fun x => refusalsFits (ofWire x).height (ofWire x).refusals.toList = true)

/-- The disjointness-checked wire's domain: the refusals-checked one's, and no transaction id both
refused and journaled. -/
def DisjointWireFits (E : Env D) (PD : D → Prop) (x : WorldWire D) : Prop :=
  RefusalsWireFits E PD x ∧ refusalsDisjoint E (ofWire x) = true

/-- **`kernel/refusals-disjoint` is lawful on exactly the wires `refusalsDisjoint` admits.** -/
theorem disjointWire_lawfulOn (E : Env D) {PD : D → Prop} {dc : Stream D} (hd : LawfulOn PD dc) :
    LawfulOn (DisjointWireFits E PD) (disjointWire E dc) :=
  refineIf_lawfulOn (refusalsWire_lawfulOn E hd) "kernel/refusals-disjoint"
    (fun x => refusalsDisjoint E (ofWire x) = true)

/-- The steps-checked wire's domain: the disjointness-checked one's, and a height at most the step
count. -/
def StepsWireFits (E : Env D) (PD : D → Prop) (x : WorldWire D) : Prop :=
  DisjointWireFits E PD x ∧ (ofWire x).height ≤ (ofWire x).steps

/-- **`kernel/steps` is lawful on exactly the wires whose height is at most their step count.** -/
theorem stepsWire_lawfulOn (E : Env D) {PD : D → Prop} {dc : Stream D} (hd : LawfulOn PD dc) :
    LawfulOn (StepsWireFits E PD) (stepsWire E dc) :=
  refineIf_lawfulOn (disjointWire_lawfulOn E hd) "kernel/steps" (fun x => (ofWire x).height ≤ (ofWire x).steps)

/-- The counts-checked wire's domain: the steps-checked one's, and refusal counts that are the
records' (KERNEL-50). -/
def CountedWireFits (E : Env D) (PD : D → Prop) (x : WorldWire D) : Prop :=
  StepsWireFits E PD x ∧ refusalsCounted E (ofWire x) = true

/-- **`kernel/refusals-counted` is lawful on exactly the wires `refusalsCounted` admits.** -/
theorem countedWire_lawfulOn (E : Env D) {PD : D → Prop} {dc : Stream D} (hd : LawfulOn PD dc) :
    LawfulOn (CountedWireFits E PD) (countedWire E dc) :=
  refineIf_lawfulOn (stepsWire_lawfulOn E hd) "kernel/refusals-counted"
    (fun x => refusalsCounted E (ofWire x) = true)

/-- The rows-checked wire's domain: the counts-checked one's, and rows that fit (KERNEL-48). -/
def RowsWireFits (E : Env D) (PD : D → Prop) (x : WorldWire D) : Prop :=
  CountedWireFits E PD x ∧ rowsFits E (ofWire x).rows.toList = true

/-- **`kernel/rows` is lawful on exactly the wires whose rows `rowsFits` admits.** -/
theorem rowsWire_lawfulOn (E : Env D) {PD : D → Prop} {dc : Stream D} (hd : LawfulOn PD dc) :
    LawfulOn (RowsWireFits E PD) (rowsWire E dc) :=
  refineIf_lawfulOn (countedWire_lawfulOn E hd) "kernel/rows" (fun x => rowsFits E (ofWire x).rows.toList = true)

/-- The heads-checked wire's domain: the rows-checked one's, and every head counting its rows. -/
def HeadedWireFits (E : Env D) (PD : D → Prop) (x : WorldWire D) : Prop :=
  RowsWireFits E PD x ∧ rowsHeaded (ofWire x).rows.toList = true

/-- **`kernel/rows-headed` is lawful on exactly the wires whose rows `rowsHeaded` admits.** -/
theorem headedWire_lawfulOn (E : Env D) {PD : D → Prop} {dc : Stream D} (hd : LawfulOn PD dc) :
    LawfulOn (HeadedWireFits E PD) (headedWire E dc) :=
  refineIf_lawfulOn (rowsWire_lawfulOn E hd) "kernel/rows-headed" (fun x => rowsHeaded (ofWire x).rows.toList = true)

/-- The parent-checked wire's domain: the heads-checked one's, and every relation's parent live. -/
def ParentedWireFits (E : Env D) (PD : D → Prop) (x : WorldWire D) : Prop :=
  HeadedWireFits E PD x ∧ rowsParented E (ofWire x).trie (ofWire x).rows = true

/-- **`kernel/rows-parented` is lawful on exactly the wires whose relations' parents are live.** -/
theorem parentedWire_lawfulOn (E : Env D) {PD : D → Prop} {dc : Stream D} (hd : LawfulOn PD dc) :
    LawfulOn (ParentedWireFits E PD) (parentedWire E dc) :=
  refineIf_lawfulOn (headedWire_lawfulOn E hd) "kernel/rows-parented"
    (fun x => rowsParented E (ofWire x).trie (ofWire x).rows = true)

/-- A World within the wire's bounds and the kernel's invariants. Named fields, so a further part adds
a field and moves no projection. -/
structure World.CodecFits (E : Env D) (PD : D → Prop) (w : World D) : Prop where
  /-- a canonical cells trie whose slots hold the leaves of their kinds, its listing within bounds -/
  cells : CellsFits E PD w.trie
  /-- a canonical journal trie of at most `Bounds.journalMax` entries -/
  journal : JournalTrieFits E PD w.journal
  /-- a canonical refusals trie whose listing fits the wire (KERNEL-44) -/
  refusals : RefusalsTrieFits E PD w.refusals
  height : w.height < 2 ^ 64
  stepsLt : w.steps < 2 ^ 64
  chain : PD w.chain
  /-- storage (cells and rows, `World.weight`) plus allowance below 2^64 (so the allowance is, and
  admission keeps it: KERNEL's `fold_budget_lt`) -/
  budget : w.weight + w.allowance < 2 ^ 64
  origin : PD w.origin
  /-- the journal is the window's (every reached World's, by KERNEL's `journalFits_of_ok`) -/
  journalFits : journalFits w.height w.journal.toList = true
  /-- the refusals are the window's (every reached World's, KERNEL's `fold_refusalsOk`) -/
  refusalsFits : refusalsFits w.height w.refusals.toList = true
  /-- no transaction id both refused and journaled (every reached World's, KERNEL's
  `fold_refusalsDisjoint`) -/
  refusalsDisjoint : refusalsDisjoint E w = true
  /-- the height is at most the step count (KERNEL's `fold_height_le_steps`; site `kernel/steps`) -/
  steps : w.height ≤ w.steps
  /-- every refusal count is its member's records this window (every reached World's, KERNEL's
  `fold_refusalsCounted`; site `kernel/refusals-counted`) -/
  refusalsCounted : refusalsCounted E w = true
  /-- the rows (KERNEL-48): a canonical trie within the wire's bounds, every entry fitting, every head
  counting its rows, every relation's parent live (sites kernel/row-order, kernel/rows,
  kernel/rows-headed, kernel/rows-parented) -/
  rows : RowsCodecFits E PD w.trie w.rows

/-- **The World codec is lawful on `World.CodecFits`**: decode ∘ bytes is the identity, and whatever
decodes is exactly its bytes. -/
theorem world_lawfulOn (E : Env D) {PD : D → Prop} {dc : Stream D} (hd : LawfulOn PD dc) :
    LawfulOn (World.CodecFits E PD) (world E dc) := by
  unfold world
  refine (refine_lawfulOn_where (parentedWire_lawfulOn E hd) "kernel/world-budget"
    (Q := fun w : World D => w.weight + w.allowance < 2 ^ 64) ?_ ?_ ?_).mono ?_ ?_
  · intro y _ hq
    have e : ofWire (toWire y) = y := rfl
    show (if (ofWire (toWire y)).weight + (ofWire (toWire y)).allowance < 2 ^ 64 then some (ofWire (toWire y))
      else none) = some y
    rw [e, if_pos hq]
  · intro x y h
    split at h
    · cases h; rfl
    · cases h
  · intro x y h
    split at h
    · rename_i hq; cases h; exact hq
    · cases h
  · intro w ⟨⟨⟨⟨⟨⟨⟨⟨⟨hx, hj⟩, hr⟩, hdj⟩, hs⟩, hct⟩, hrf⟩, hrh⟩, hrp⟩, hb⟩
    obtain ⟨hc, hjt, hrt, hrw, hh, hst, hch, ha, ho⟩ := hx
    exact ⟨hc, hjt, hrt, hh, hst, hch, hb, ho, hj, hr, hdj, hs, hct, ⟨hrw, hrf, hrh, hrp⟩⟩
  · intro w h
    exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h.cells, h.journal, h.refusals, h.rows.listing, h.height, h.stepsLt, h.chain,
      Nat.lt_of_le_of_lt (Nat.le_add_left _ _) h.budget, h.origin⟩, h.journalFits⟩, h.refusalsFits⟩,
      h.refusalsDisjoint⟩, h.steps⟩, h.refusalsCounted⟩, h.rows.fits⟩, h.rows.headed⟩, h.rows.parented⟩, h.budget⟩

theorem world_bytes (E : Env D) (dc : Stream D) (w : World D) :
    (world E dc).bytes w = (worldWire E dc).bytes (toWire w) := rfl

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
  ⟨hf.cells.2, hf.cells.1.2⟩

/-- A decoded World satisfies the kernel's trie invariant, and every slot holds the leaf of its kind. -/
theorem world_decode_canon {E : Env D} {PD : D → Prop} {dc : Stream D} (hd : LawfulOn PD dc)
    {b : ByteArray} {w : World D} (h : (world E dc).decode b = .ok w) :
    w.Canon E ∧ ∀ p ∈ w.trie.toList, Leaf.fits p.1 p.2 = true :=
  let hf := world_decode_fits hd h
  ⟨hf.cells.2, hf.cells.1.2⟩

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
  have hm := (Trie.mem_toList (trieSpec E) 0 w.trie hf.cells.2.1 s l).mpr hg
  have hl := (hf.cells.1.1.2 (s, l) hm).2
  cases l with
  | entry e =>
    cases e with
    | live c v => exact hl
    | tomb => trivial
  | spent => trivial

/-- **A World read at any offset carries `World.JournalOk`** (KERNEL-39, KERNEL-41): its journal trie is
canonical (the decoder rebuilt it by `build`) and the decoder refused `kernel/journal` unless
`journalFits` holds of that trie's own listing. -/
theorem world_get_journalOk {E : Env D} {PD : D → Prop} {dc : Stream D} (hd : LawfulOn PD dc)
    {b : ByteArray} {i j : Nat} {w : World D} (h : (world E dc).get b i = .ok (w, j)) : w.JournalOk E :=
  let hf := world_get_fits hd h
  journalOk_of_fits hf.journal.2 hf.journalFits

/-- **A decoded World carries `World.JournalOk`.** -/
theorem world_decode_journalOk {E : Env D} {PD : D → Prop} {dc : Stream D} (hd : LawfulOn PD dc)
    {b : ByteArray} {w : World D} (h : (world E dc).decode b = .ok w) : w.JournalOk E :=
  let hf := world_decode_fits hd h
  journalOk_of_fits hf.journal.2 hf.journalFits

/-- **A World read at any offset carries `World.RefusalsOk`** (KERNEL-44, KERNEL-47): its refusals trie
is canonical (rebuilt by `build`) and the decoder refused `kernel/refusals` unless `refusalsFits`
holds of that trie's own listing. -/
theorem world_get_refusalsOk {E : Env D} {PD : D → Prop} {dc : Stream D} (hd : LawfulOn PD dc)
    {b : ByteArray} {i j : Nat} {w : World D} (h : (world E dc).get b i = .ok (w, j)) : w.RefusalsOk E :=
  let hf := world_get_fits hd h
  refusalsOk_of_fits hf.refusals.2 hf.refusalsFits

/-- **A decoded World carries `World.RefusalsOk`.** -/
theorem world_decode_refusalsOk {E : Env D} {PD : D → Prop} {dc : Stream D} (hd : LawfulOn PD dc)
    {b : ByteArray} {w : World D} (h : (world E dc).decode b = .ok w) : w.RefusalsOk E :=
  let hf := world_decode_fits hd h
  refusalsOk_of_fits hf.refusals.2 hf.refusalsFits

/-- **A decoded World holds no transaction id both refused and journaled** (KERNEL's
`World.RefusalsDisjoint`, from `kernel/refusals-disjoint` over the rebuilt, canonical refusals trie). -/
theorem world_decode_refusalsDisjoint {E : Env D} {PD : D → Prop} {dc : Stream D} (hd : LawfulOn PD dc)
    {b : ByteArray} {w : World D} (h : (world E dc).decode b = .ok w) : w.RefusalsDisjoint E :=
  let hf := world_decode_fits hd h
  (refusalsDisjoint_iff hf.refusals.2).mp hf.refusalsDisjoint

/-- **A World read at any offset holds no transaction id both refused and journaled.** -/
theorem world_get_refusalsDisjoint {E : Env D} {PD : D → Prop} {dc : Stream D} (hd : LawfulOn PD dc)
    {b : ByteArray} {i j : Nat} {w : World D} (h : (world E dc).get b i = .ok (w, j)) : w.RefusalsDisjoint E :=
  let hf := world_get_fits hd h
  (refusalsDisjoint_iff hf.refusals.2).mp hf.refusalsDisjoint

/-- **A decoded World's refusal counts are its records'** (KERNEL-50, from `kernel/refusals-counted`;
with `refusalsOk`, KERNEL's `refusalsCounted_iff` reads it as `World.CountedOk`). -/
theorem world_decode_refusalsCounted {E : Env D} {PD : D → Prop} {dc : Stream D} (hd : LawfulOn PD dc)
    {b : ByteArray} {w : World D} (h : (world E dc).decode b = .ok w) : refusalsCounted E w = true :=
  (world_decode_fits hd h).refusalsCounted

/-- **A World read at any offset has refusal counts that are its records'.** -/
theorem world_get_refusalsCounted {E : Env D} {PD : D → Prop} {dc : Stream D} (hd : LawfulOn PD dc)
    {b : ByteArray} {i j : Nat} {w : World D} (h : (world E dc).get b i = .ok (w, j)) : refusalsCounted E w = true :=
  (world_get_fits hd h).refusalsCounted

/-- **A World read at any offset has height at most its step count.** -/
theorem world_get_height_le_steps {E : Env D} {PD : D → Prop} {dc : Stream D} (hd : LawfulOn PD dc)
    {b : ByteArray} {i j : Nat} {w : World D} (h : (world E dc).get b i = .ok (w, j)) : w.height ≤ w.steps :=
  (world_get_fits hd h).steps

/-- **A decoded World's height is at most its step count** (the premise of KERNEL's
`fold_height_le_steps`). -/
theorem world_decode_height_le_steps {E : Env D} {PD : D → Prop} {dc : Stream D} (hd : LawfulOn PD dc)
    {b : ByteArray} {w : World D} (h : (world E dc).decode b = .ok w) : w.height ≤ w.steps :=
  (world_decode_fits hd h).steps

omit [Ord D] in
/-- The decoder's prefix: a wire value in the wire's domain reaches the World refinement's own check
with every inner refusal decided by its predicate. -/
private theorem world_decode_wire {E : Env D} {PD : D → Prop} {dc : Stream D} (hd : LawfulOn PD dc)
    {x : WorldWire D} (hx : WireFits E PD x) :
    (worldWire E dc).get ((worldWire E dc).bytes x) 0 = .ok (x, ((worldWire E dc).bytes x).size) := by
  simpa using (worldWire_lawfulOn E hd).get_of_occurs x ((worldWire E dc).bytes x) 0 hx (occursAt_self _)

/-- The rows a World read at any offset holds: a canonical trie, every entry within KERNEL's bounds
(`rowsFits`), every head counting its rows (`rowsHeaded`), every key in the rows codec's domain. -/
theorem world_get_rows {E : Env D} {PD : D → Prop} {dc : Stream D} (hd : LawfulOn PD dc)
    {b : ByteArray} {i j : Nat} {w : World D} (h : (world E dc).get b i = .ok (w, j)) :
    RowsCodecFits E PD w.trie w.rows :=
  (world_get_fits hd h).rows

/-- **A decoded World's rows fit and every head counts its rows** (KERNEL-48). -/
theorem world_decode_rows {E : Env D} {PD : D → Prop} {dc : Stream D} (hd : LawfulOn PD dc)
    {b : ByteArray} {w : World D} (h : (world E dc).decode b = .ok w) : RowsCodecFits E PD w.trie w.rows :=
  (world_decode_fits hd h).rows

/-- A wire value in the wire's domain that passes every check decodes to its World. -/
theorem world_decode_wire_ok {E : Env D} {PD : D → Prop} {dc : Stream D} (hd : LawfulOn PD dc)
    {x : WorldWire D} (hx : WireFits E PD x) (hj : journalFits (ofWire x).height (ofWire x).journal.toList = true)
    (hr : refusalsFits (ofWire x).height (ofWire x).refusals.toList = true) (hdj : refusalsDisjoint E (ofWire x) = true)
    (hs : (ofWire x).height ≤ (ofWire x).steps) (hct : refusalsCounted E (ofWire x) = true) (hrf : rowsFits E (ofWire x).rows.toList = true)
    (hrh : rowsHeaded (ofWire x).rows.toList = true) (hrp : rowsParented E (ofWire x).trie (ofWire x).rows = true)
    (hw : (ofWire x).weight + (ofWire x).allowance < 2 ^ 64) :
    (world E dc).decode ((worldWire E dc).bytes x) = .ok (ofWire x) := by
  have hb : (worldWire E dc).bytes x = (world E dc).bytes (ofWire x) := rfl
  rw [hb]
  obtain ⟨hc, hjt, hrt, hrw, hh, hst, hch, ha, ho⟩ := hx
  exact world_decode_bytes hd ⟨hc, hjt, hrt, hh, hst, hch, hw, ho, hj, hr, hdj, hs, hct, ⟨hrw, hrf, hrh, hrp⟩⟩

/-- **The budget refusal** (cv 01a14ba9-cbf4): a wire value in the wire's domain that passes every
other check, whose storage (cells and rows) plus allowance is 2^64 or more, is refused
`kernel/world-budget` by name, at offset 0, although every counter in it fits its `u64`. -/
theorem world_decode_wire_overBudget {E : Env D} {PD : D → Prop} {dc : Stream D} (hd : LawfulOn PD dc)
    {x : WorldWire D} (hx : WireFits E PD x) (hj : journalFits (ofWire x).height (ofWire x).journal.toList = true)
    (hr : refusalsFits (ofWire x).height (ofWire x).refusals.toList = true) (hdj : refusalsDisjoint E (ofWire x) = true)
    (hs : (ofWire x).height ≤ (ofWire x).steps) (hct : refusalsCounted E (ofWire x) = true) (hrf : rowsFits E (ofWire x).rows.toList = true)
    (hrh : rowsHeaded (ofWire x).rows.toList = true) (hrp : rowsParented E (ofWire x).trie (ofWire x).rows = true)
    (hw : ¬ (ofWire x).weight + (ofWire x).allowance < 2 ^ 64) :
    (world E dc).decode ((worldWire E dc).bytes x) = .error (.rejected 0 "kernel/world-budget") := by
  have hg := world_decode_wire hd hx
  simp only [world, decode, parentedWire, headedWire, rowsWire, stepsWire, countedWire, disjointWire, refusalsWire, journalWire, refine, hg, hj, hr, hdj, hct, hrf, hrh, hrp, ite_true, if_pos hs]
  simp [if_neg hw]

/-- **The journal refusal**: a wire value in the wire's domain whose journal is not the window's is
refused `kernel/journal` by name, at offset 0. -/
theorem world_decode_wire_refused {E : Env D} {PD : D → Prop} {dc : Stream D} (hd : LawfulOn PD dc)
    {x : WorldWire D} (hx : WireFits E PD x) (hj : journalFits (ofWire x).height (ofWire x).journal.toList = false) :
    (world E dc).decode ((worldWire E dc).bytes x) = .error (.rejected 0 "kernel/journal") := by
  have hg := world_decode_wire hd hx
  simp only [world, decode, parentedWire, headedWire, rowsWire, stepsWire, countedWire, disjointWire, refusalsWire, journalWire, refine, hg, hj]
  rfl

/-- **The refusals refusal**: a wire value in the wire's domain whose journal is the window's and whose
refusals are not is refused `kernel/refusals` by name, at offset 0. -/
theorem world_decode_wire_refusalsRefused {E : Env D} {PD : D → Prop} {dc : Stream D} (hd : LawfulOn PD dc)
    {x : WorldWire D} (hx : WireFits E PD x) (hj : journalFits (ofWire x).height (ofWire x).journal.toList = true)
    (hr : refusalsFits (ofWire x).height (ofWire x).refusals.toList = false) :
    (world E dc).decode ((worldWire E dc).bytes x) = .error (.rejected 0 "kernel/refusals") := by
  have hg := world_decode_wire hd hx
  simp only [world, decode, parentedWire, headedWire, rowsWire, stepsWire, countedWire, disjointWire, refusalsWire, journalWire, refine, hg, hj, hr, ite_true]
  rfl

/-- **The steps refusal**: a wire value that passes the journal and refusals checks but whose height
exceeds its step count is refused `kernel/steps` by name, at offset 0. -/
theorem world_decode_wire_stepsRefused {E : Env D} {PD : D → Prop} {dc : Stream D} (hd : LawfulOn PD dc)
    {x : WorldWire D} (hx : WireFits E PD x) (hj : journalFits (ofWire x).height (ofWire x).journal.toList = true)
    (hr : refusalsFits (ofWire x).height (ofWire x).refusals.toList = true) (hdj : refusalsDisjoint E (ofWire x) = true)
    (hs : ¬ (ofWire x).height ≤ (ofWire x).steps) :
    (world E dc).decode ((worldWire E dc).bytes x) = .error (.rejected 0 "kernel/steps") := by
  have hg := world_decode_wire hd hx
  simp only [world, decode, parentedWire, headedWire, rowsWire, stepsWire, countedWire, disjointWire, refusalsWire, journalWire, refine, hg, hj, hr, hdj, ite_true, if_neg hs]

/-- **The disjointness refusal**: a wire value that passes the journal and refusals checks but holds a
transaction id both refused and journaled is refused `kernel/refusals-disjoint` by name, at offset 0. -/
theorem world_decode_wire_disjointRefused {E : Env D} {PD : D → Prop} {dc : Stream D} (hd : LawfulOn PD dc)
    {x : WorldWire D} (hx : WireFits E PD x) (hj : journalFits (ofWire x).height (ofWire x).journal.toList = true)
    (hr : refusalsFits (ofWire x).height (ofWire x).refusals.toList = true) (hdj : refusalsDisjoint E (ofWire x) = false) :
    (world E dc).decode ((worldWire E dc).bytes x) = .error (.rejected 0 "kernel/refusals-disjoint") := by
  have hg := world_decode_wire hd hx
  simp only [world, decode, parentedWire, headedWire, rowsWire, stepsWire, countedWire, disjointWire, refusalsWire, journalWire, refine, hg, hj, hr, hdj, ite_true]
  rfl

/-- **The counts refusal** (KERNEL-50): a wire value that passes the journal, refusals,
disjointness and steps checks but holds a refusal count that is not its member's records this window (a charge
lowered or moved) is refused `kernel/refusals-counted` by name, at offset 0. -/
theorem world_decode_wire_countedRefused {E : Env D} {PD : D → Prop} {dc : Stream D} (hd : LawfulOn PD dc)
    {x : WorldWire D} (hx : WireFits E PD x) (hj : journalFits (ofWire x).height (ofWire x).journal.toList = true)
    (hr : refusalsFits (ofWire x).height (ofWire x).refusals.toList = true) (hdj : refusalsDisjoint E (ofWire x) = true)
    (hs : (ofWire x).height ≤ (ofWire x).steps) (hct : refusalsCounted E (ofWire x) = false) :
    (world E dc).decode ((worldWire E dc).bytes x) = .error (.rejected 0 "kernel/refusals-counted") := by
  have hg := world_decode_wire hd hx
  simp only [world, decode, parentedWire, headedWire, rowsWire, stepsWire, countedWire, disjointWire, refusalsWire, journalWire, refine, hg, hj, hr, hdj, hct, ite_true, if_pos hs]
  rfl

/-- **The rows refusal** (KERNEL-48): a wire value that passes every earlier check but holds a rows
entry outside KERNEL's bounds (or a listing not ascending by key bytes) is refused `kernel/rows` by
name, at offset 0. -/
theorem world_decode_wire_rowsRefused {E : Env D} {PD : D → Prop} {dc : Stream D} (hd : LawfulOn PD dc)
    {x : WorldWire D} (hx : WireFits E PD x) (hj : journalFits (ofWire x).height (ofWire x).journal.toList = true)
    (hr : refusalsFits (ofWire x).height (ofWire x).refusals.toList = true) (hdj : refusalsDisjoint E (ofWire x) = true)
    (hs : (ofWire x).height ≤ (ofWire x).steps) (hct : refusalsCounted E (ofWire x) = true) (hrf : rowsFits E (ofWire x).rows.toList = false) :
    (world E dc).decode ((worldWire E dc).bytes x) = .error (.rejected 0 "kernel/rows") := by
  have hg := world_decode_wire hd hx
  simp only [world, decode, parentedWire, headedWire, rowsWire, stepsWire, countedWire, disjointWire, refusalsWire, journalWire, refine, hg, hj, hr, hdj, hct, hrf, ite_true, if_pos hs]
  rfl

/-- **The heads refusal** (KERNEL-48): a wire value that passes every earlier check but holds a row
without its head, at another width, or a head whose count or sum is not its rows', is refused
`kernel/rows-headed` by name, at offset 0. -/
theorem world_decode_wire_headedRefused {E : Env D} {PD : D → Prop} {dc : Stream D} (hd : LawfulOn PD dc)
    {x : WorldWire D} (hx : WireFits E PD x) (hj : journalFits (ofWire x).height (ofWire x).journal.toList = true)
    (hr : refusalsFits (ofWire x).height (ofWire x).refusals.toList = true) (hdj : refusalsDisjoint E (ofWire x) = true)
    (hs : (ofWire x).height ≤ (ofWire x).steps) (hct : refusalsCounted E (ofWire x) = true) (hrf : rowsFits E (ofWire x).rows.toList = true)
    (hrh : rowsHeaded (ofWire x).rows.toList = false) :
    (world E dc).decode ((worldWire E dc).bytes x) = .error (.rejected 0 "kernel/rows-headed") := by
  have hg := world_decode_wire hd hx
  simp only [world, decode, parentedWire, headedWire, rowsWire, stepsWire, countedWire, disjointWire, refusalsWire, journalWire, refine, hg, hj, hr, hdj, hct, hrf, hrh, ite_true, if_pos hs]
  rfl

/-- **The parents refusal** (KERNEL-48): a wire value that passes every earlier check but holds a
relation whose parent is not a live cell is refused `kernel/rows-parented` by name, at offset 0. -/
theorem world_decode_wire_parentedRefused {E : Env D} {PD : D → Prop} {dc : Stream D} (hd : LawfulOn PD dc)
    {x : WorldWire D} (hx : WireFits E PD x) (hj : journalFits (ofWire x).height (ofWire x).journal.toList = true)
    (hr : refusalsFits (ofWire x).height (ofWire x).refusals.toList = true) (hdj : refusalsDisjoint E (ofWire x) = true)
    (hs : (ofWire x).height ≤ (ofWire x).steps) (hct : refusalsCounted E (ofWire x) = true) (hrf : rowsFits E (ofWire x).rows.toList = true)
    (hrh : rowsHeaded (ofWire x).rows.toList = true) (hrp : rowsParented E (ofWire x).trie (ofWire x).rows = false) :
    (world E dc).decode ((worldWire E dc).bytes x) = .error (.rejected 0 "kernel/rows-parented") := by
  have hg := world_decode_wire hd hx
  simp only [world, decode, parentedWire, headedWire, rowsWire, stepsWire, countedWire, disjointWire, refusalsWire, journalWire, refine, hg, hj, hr, hdj, hct, hrf, hrh, hrp, ite_true, if_pos hs]
  rfl

end Nanodregg.Codec.Kernel
