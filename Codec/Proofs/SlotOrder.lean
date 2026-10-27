import Codec.Proofs.TrieOrder
import Kernel.Proofs.Cells

/-!
# The trie's bit order is the order of the bytes (CODEC-28 step 2, the bytes half)

`SlotBefore E s s'` is stated with no trie in it: cells before nullifiers, then the ids' bytes in
`compare` order (lexicographic on the byte arrays, the order `Codec.Digest` is ordered by).
`bitLt_trieSpec_iff`: over a lawful `Env`, a slot routes before another in the deployed trie
(`BitLt (trieSpec E) 0`, KERNEL's `slotBit`: the kind bit, then each id byte most significant bit
first) exactly when it is `SlotBefore`. So a routing change in KERNEL (the kind bit moved, a byte
read low bit first, a depth that drops an id bit) breaks this theorem instead of silently changing
what the World codec's listing must look like.
* `compare_lt_iff_bits`: two byte strings of one size are in `compare` order exactly when, at the
  first bit where they differ (`byteBit`, most significant bit of byte 0 first), the first one's is
  clear.
* `cells_get_ok_slotBefore` / `cells_get_refused_slotBefore`: the World codec's trie part,
  restated in bytes.
* `bitLt_journalSpec_iff` / `journalTrie_get_ok` / `_refused` / `_ordered` (KERNEL-41): the journal
  trie routes by its ids' bytes alone, so its listing is accepted exactly when strictly ascending by
  `compare` on the id bytes (`JournalBefore`), and refused `kernel/journal-order` otherwise.
* `bitLt_refusalSpec_iff` / `refusalsTrie_get_ok` / `_refused` / `_ordered` (KERNEL-44): the same for
  the refusals trie over `refusalKeyBytes` (`RefusalBefore`), refused `kernel/refusal-order` otherwise.
-/

namespace Nanodregg.Codec.Kernel

open Nanodregg.Kernel Nanodregg.Codec.Stream

/-! ## Bits and bytes -/

-- `byteBit` at an index, `nat_lt_of_testBit`, `compareLex_lt`, `compare_lt_of_bits_at` and
-- `compare_lt_of_bits` are `Kernel.Proofs.Bytes`'s.

/-- Two different byte strings of one size differ at a first bit. -/
theorem first_bit_diff {a b : ByteArray} (hs : a.size = b.size) (hne : a ≠ b) :
    ∃ k, byteBit a k ≠ byteBit b k ∧ ∀ j, j < k → byteBit a j = byteBit b j := by
  have hex : ∃ k, byteBit a k ≠ byteBit b k := Classical.byContradiction fun hno =>
    hne (byteBit_ext hs fun i _ => Classical.byContradiction fun h => hno ⟨i, h⟩)
  obtain ⟨k, hk⟩ := hex
  induction k using Nat.strongRecOn with
  | ind k ih =>
    by_cases h : ∀ j, j < k → byteBit a j = byteBit b j
    · exact ⟨k, hk, h⟩
    · simp only [Classical.not_forall] at h
      obtain ⟨j, hj, hjne⟩ := h
      exact ih j hj hjne

/-- **`compare` on two byte strings of one size is the order of their first differing bit**, most
significant bit of byte 0 first. -/
theorem compare_lt_iff_bits {a b : ByteArray} (hs : a.size = b.size) :
    compare a.data b.data = .lt ↔
      ∃ k, (∀ j, j < k → byteBit a j = byteBit b j) ∧ byteBit a k = false ∧ byteBit b k = true := by
  constructor
  · intro h
    have hne : a ≠ b := by
      rintro rfl; rw [Std.ReflCmp.compare_self (cmp := compare)] at h; cases h
    obtain ⟨k, hk, hpre⟩ := first_bit_diff hs hne
    cases ha : byteBit a k
    · refine ⟨k, hpre, ha, ?_⟩
      cases hb : byteBit b k
      · rw [ha, hb] at hk; exact absurd rfl hk
      · rfl
    · cases hb : byteBit b k
      · have h' := compare_lt_of_bits hs.symm (fun j hj => (hpre j hj).symm) hb ha
        rw [Std.OrientedCmp.eq_swap (cmp := compare), h] at h'; cases h'
      · rw [ha, hb] at hk; exact absurd rfl hk
  · rintro ⟨k, hpre, ha, hb⟩
    exact compare_lt_of_bits hs hpre ha hb

/-! ## Slots -/

variable {D : Type} [Ord D] [DecidableEq D]

/-- **The World listing's order, in bytes**: cells before nullifiers, then the ids' bytes in
`compare` order. No trie in it. -/
def SlotBefore (E : Env D) (s s' : Slot D) : Prop :=
  (s.isNullifier = false ∧ s'.isNullifier = true) ∨
    (s.isNullifier = s'.isNullifier ∧ compare (E.bytes s.id).data (E.bytes s'.id).data = .lt)

omit [DecidableEq D] in
/-- **KERNEL's routing is the order of the bytes.** Over a lawful `Env`, a slot routes before another
in the deployed trie exactly when it is `SlotBefore`. -/
theorem bitLt_trieSpec_iff {E : Env D} {n : Nat} (hE : E.Lawful n) (s s' : Slot D) :
    BitLt (trieSpec E) 0 s s' ↔ SlotBefore E s s' := by
  have hs : (E.bytes s.id).size = (E.bytes s'.id).size := by rw [hE.size, hE.size]
  have hn := hE.n_le
  constructor
  · rintro ⟨i, _, hi, hpre, h1, h2⟩
    cases i with
    | zero => exact Or.inl ⟨h1, h2⟩
    | succ k =>
      refine Or.inr ⟨hpre 0 (Nat.le_refl 0) (by omega), (compare_lt_iff_bits hs).mpr ⟨k, ?_, h1, h2⟩⟩
      intro j hj
      exact hpre (j + 1) (by omega) (by omega)
  · rintro (⟨h1, h2⟩ | ⟨hk, hc⟩)
    · exact ⟨0, Nat.le_refl 0, by show 0 < Bounds.trieDepth; decide, fun _ _ h => absurd h (by omega), h1, h2⟩
    · obtain ⟨k, hpre, h1, h2⟩ := (compare_lt_iff_bits hs).mp hc
      have hk8 := lt_size_of_byteBit h2
      rw [hE.size] at hk8
      refine ⟨k + 1, by omega, by show k + 1 < Bounds.trieDepth; unfold Bounds.trieDepth; omega,
        fun j _ hj => ?_, h1, h2⟩
      cases j with
      | zero => exact hk
      | succ j => exact hpre j (by omega)

omit [DecidableEq D] in
theorem pairwise_bitLt_iff {E : Env D} {n : Nat} (hE : E.Lawful n) (l : List (Slot D × Leaf)) :
    l.Pairwise (fun p q => BitLt (trieSpec E) 0 p.1 q.1) ↔ l.Pairwise (fun p q => SlotBefore E p.1 q.1) :=
  ⟨List.Pairwise.imp fun h => (bitLt_trieSpec_iff hE _ _).mp h,
   List.Pairwise.imp fun h => (bitLt_trieSpec_iff hE _ _).mpr h⟩

/-- **The trie part accepts a listing that is strictly ascending by (kind, id bytes)**, as the trie
`build` makes of it. -/
theorem cells_get_ok_slotBefore {E : Env D} {n : Nat} (hE : E.Lawful n) {dc : Stream D} {b : ByteArray}
    {i j : Nat} {l : List (Slot D × Leaf)} (h : (fitList dc).get b i = .ok (l, j))
    (ho : l.Pairwise (fun p q => SlotBefore E p.1 q.1)) :
    (cells E dc).get b i = .ok (Trie.build (trieSpec E) (trieSpec E).depth 0 l, j) :=
  cells_get_ok E (slots_separate hE) h ((pairwise_bitLt_iff hE l).mpr ho)

/-- **Every other listing is refused `kernel/trie-order` by name.** -/
theorem cells_get_refused_slotBefore {E : Env D} {n : Nat} (hE : E.Lawful n) {dc : Stream D}
    {b : ByteArray} {i j : Nat} {l : List (Slot D × Leaf)} (h : (fitList dc).get b i = .ok (l, j))
    (ho : ¬ l.Pairwise (fun p q => SlotBefore E p.1 q.1)) :
    (cells E dc).get b i = .error (.rejected i "kernel/trie-order") :=
  cells_get_refused E (slots_separate hE) h fun h' => ho ((pairwise_bitLt_iff hE l).mp h')

/-- What the trie part accepts was strictly ascending by (kind, id bytes). -/
theorem cells_get_slotBefore {E : Env D} {n : Nat} (hE : E.Lawful n) {dc : Stream D} {b : ByteArray}
    {i j : Nat} {t : Cells D} (h : (cells E dc).get b i = .ok (t, j)) :
    ∃ l, (fitList dc).get b i = .ok (l, j) ∧ l.Pairwise (fun p q => SlotBefore E p.1 q.1) ∧
      t = Trie.build (trieSpec E) (trieSpec E).depth 0 l := by
  obtain ⟨l, hg, ho, ht⟩ := cells_get_ordered E (slots_separate hE) h
  exact ⟨l, hg, (pairwise_bitLt_iff hE l).mp ho, ht⟩

/-! ## The journal (KERNEL-41) -/

omit [DecidableEq D] in
/-- **The journal trie's routing is the order of the id bytes.** Over a lawful `Env`, a transaction id
routes before another in the journal trie exactly when its bytes are below the other's in `compare`. -/
theorem bitLt_journalSpec_iff {E : Env D} {n : Nat} (hE : E.Lawful n) (k k' : D) :
    BitLt (journalSpec E) 0 k k' ↔ compare (E.bytes k).data (E.bytes k').data = .lt := by
  have hs : (E.bytes k).size = (E.bytes k').size := by rw [hE.size, hE.size]
  have hn := hE.n_le
  rw [compare_lt_iff_bits hs]
  constructor
  · rintro ⟨i, _, _, hpre, h1, h2⟩
    exact ⟨i, fun j hj => hpre j (Nat.zero_le j) hj, h1, h2⟩
  · rintro ⟨i, hpre, h1, h2⟩
    have hk8 := lt_size_of_byteBit h2
    rw [hE.size] at hk8
    exact ⟨i, Nat.zero_le i, by show i < Bounds.journalDepth; unfold Bounds.journalDepth; omega,
      fun j _ hj => hpre j hj, h1, h2⟩

/-- The journal's id order, in bytes. -/
def JournalBefore (E : Env D) (p q : D × (Nat × D)) : Prop :=
  compare (E.bytes p.1).data (E.bytes q.1).data = .lt

/-- **The journal part accepts a listing strictly ascending by id bytes**, as the trie `build` makes of it. -/
theorem journalTrie_get_ok {E : Env D} {n : Nat} (hE : E.Lawful n) {dc : Stream D} {b : ByteArray}
    {i j : Nat} {l : List (D × (Nat × D))}
    (h : (rawList Bounds.journalMax (product dc (product nat64 dc))).get b i = .ok (l, j))
    (ho : l.Pairwise (JournalBefore E)) :
    (journalTrie E dc).get b i = .ok (Trie.build (journalSpec E) (journalSpec E).depth 0 l, j) :=
  trieListing_get_ok _ (journal_separate hE) h
    (ho.imp fun hpq => (bitLt_journalSpec_iff hE _ _).mpr hpq)

/-- **Every other journal listing is refused `kernel/journal-order` by name.** -/
theorem journalTrie_get_refused {E : Env D} {n : Nat} (hE : E.Lawful n) {dc : Stream D} {b : ByteArray}
    {i j : Nat} {l : List (D × (Nat × D))}
    (h : (rawList Bounds.journalMax (product dc (product nat64 dc))).get b i = .ok (l, j))
    (ho : ¬ l.Pairwise (JournalBefore E)) :
    (journalTrie E dc).get b i = .error (.rejected i "kernel/journal-order") :=
  trieListing_get_refused _ (journal_separate hE) h fun h' =>
    ho (h'.imp fun hpq => (bitLt_journalSpec_iff hE _ _).mp hpq)

/-- What the journal part accepts was strictly ascending by id bytes. -/
theorem journalTrie_get_ordered {E : Env D} {n : Nat} (hE : E.Lawful n) {dc : Stream D} {b : ByteArray}
    {i j : Nat} {t : Journal D} (h : (journalTrie E dc).get b i = .ok (t, j)) :
    ∃ l, (rawList Bounds.journalMax (product dc (product nat64 dc))).get b i = .ok (l, j) ∧
      l.Pairwise (JournalBefore E) ∧ t = Trie.build (journalSpec E) (journalSpec E).depth 0 l := by
  obtain ⟨l, hg, ho, ht⟩ := trieListing_get_ordered _ (journal_separate hE) h
  exact ⟨l, hg, ho.imp fun hpq => (bitLt_journalSpec_iff hE _ _).mp hpq, ht⟩

/-! ## The refusals (KERNEL-44) -/

omit [DecidableEq D] in
/-- **The refusals trie's routing is the order of the key bytes.** Over a lawful `Env`, a refusals key
routes before another exactly when its bytes (`refusalKeyBytes`: the kind, then the id or the member,
then the window's eight little-endian bytes) are below the other's in `compare`. -/
theorem bitLt_refusalSpec_iff {E : Env D} {n : Nat} (hE : E.Lawful n) (k k' : WindowSlot D) :
    BitLt (refusalSpec E) 0 k k' ↔ compare (refusalKeyBytes E k).data (refusalKeyBytes E k').data = .lt := by
  have hs : (refusalKeyBytes E k).size = (refusalKeyBytes E k').size := by
    rw [refusalKeyBytes_size hE, refusalKeyBytes_size hE]
  have hn := hE.n_le
  rw [compare_lt_iff_bits hs]
  constructor
  · rintro ⟨i, _, _, hpre, h1, h2⟩
    exact ⟨i, fun j hj => hpre j (Nat.zero_le j) hj, h1, h2⟩
  · rintro ⟨i, hpre, h1, h2⟩
    have hk8 := lt_size_of_byteBit h2
    rw [refusalKeyBytes_size hE] at hk8
    exact ⟨i, Nat.zero_le i, by show i < Bounds.refusalDepth; unfold Bounds.refusalDepth; omega,
      fun j _ hj => hpre j hj, h1, h2⟩

omit [Ord D] [DecidableEq D] in
/-- **The kind leads the refusals' key order** (KERNEL-55 R1's three kinds): a key of a lower kind is
below one of a higher kind whatever their digests and windows, at any `Env` (the kind byte is byte 0).
So a canonical refusals listing holds its `tx` keys, then its `count` keys, then its `total`. -/
theorem refusalKeyBytes_kind_lt (E : Env D) {k k' : WindowSlot D} (h : refusalKind k < refusalKind k') :
    compare (refusalKeyBytes E k).data (refusalKeyBytes E k').data = .lt := by
  rcases k with k | k | k <;> rcases k' with k' | k' | k' <;> cases k <;> cases k' <;> simp only [refusalKind] at h <;>
    (try omega) <;>
    simp [refusalKeyBytes, Array.compare_eq_compare_toList] <;> rfl

/-- The refusals' key order, in bytes. -/
def RefusalBefore (E : Env D) (p q : WindowSlot D × RefusalLeaf D) : Prop :=
  compare (refusalKeyBytes E p.1).data (refusalKeyBytes E q.1).data = .lt

/-- **The refusals part accepts a listing strictly ascending by key bytes**, as `build` makes of it. -/
theorem refusalsTrie_get_ok {E : Env D} {n : Nat} (hE : E.Lawful n) {dc : Stream D} {b : ByteArray}
    {i j : Nat} {l : List (WindowSlot D × RefusalLeaf D)}
    (h : (rawList worldMax (product (refusalSlot dc) (refusalLeaf dc))).get b i = .ok (l, j))
    (ho : l.Pairwise (RefusalBefore E)) :
    (refusalsTrie E dc).get b i = .ok (Trie.build (refusalSpec E) (refusalSpec E).depth 0 l, j) :=
  trieListing_get_ok _ (refusals_separate hE) h
    (ho.imp fun hpq => (bitLt_refusalSpec_iff hE _ _).mpr hpq)

/-- **Every other refusals listing is refused `kernel/refusal-order` by name.** -/
theorem refusalsTrie_get_refused {E : Env D} {n : Nat} (hE : E.Lawful n) {dc : Stream D} {b : ByteArray}
    {i j : Nat} {l : List (WindowSlot D × RefusalLeaf D)}
    (h : (rawList worldMax (product (refusalSlot dc) (refusalLeaf dc))).get b i = .ok (l, j))
    (ho : ¬ l.Pairwise (RefusalBefore E)) :
    (refusalsTrie E dc).get b i = .error (.rejected i "kernel/refusal-order") :=
  trieListing_get_refused _ (refusals_separate hE) h fun h' =>
    ho (h'.imp fun hpq => (bitLt_refusalSpec_iff hE _ _).mp hpq)

/-- What the refusals part accepts was strictly ascending by key bytes. -/
theorem refusalsTrie_get_ordered {E : Env D} {n : Nat} (hE : E.Lawful n) {dc : Stream D} {b : ByteArray}
    {i j : Nat} {t : Refusals D} (h : (refusalsTrie E dc).get b i = .ok (t, j)) :
    ∃ l, (rawList worldMax (product (refusalSlot dc) (refusalLeaf dc))).get b i = .ok (l, j) ∧
      l.Pairwise (RefusalBefore E) ∧ t = Trie.build (refusalSpec E) (refusalSpec E).depth 0 l := by
  obtain ⟨l, hg, ho, ht⟩ := trieListing_get_ordered _ (refusals_separate hE) h
  exact ⟨l, hg, ho.imp fun hpq => (bitLt_refusalSpec_iff hE _ _).mp hpq, ht⟩

end Nanodregg.Codec.Kernel
