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

/-- At the most significant bit where two naturals differ, the smaller one's is clear. -/
theorem nat_lt_of_testBit {x y i : Nat} (hx : x.testBit i = false) (hy : y.testBit i = true)
    (h : ∀ j, i < j → x.testBit j = y.testBit j) : x < y := by
  have hq : x / 2 ^ (i + 1) = y / 2 ^ (i + 1) := Nat.eq_of_testBit_eq fun j => by
    rw [Nat.testBit_div_two_pow, Nat.testBit_div_two_pow]; exact h _ (by omega)
  have hrx : x % 2 ^ (i + 1) < 2 ^ i := Nat.lt_pow_two_of_testBit _ fun j hj => by
    rw [Nat.testBit_mod_two_pow]
    rcases Nat.lt_or_eq_of_le hj with hlt | rfl
    · have : ¬ j < i + 1 := by omega
      simp [this]
    · simp [hx]
  have hry : 2 ^ i ≤ y % 2 ^ (i + 1) :=
    Nat.ge_two_pow_of_testBit (by rw [Nat.testBit_mod_two_pow]; simp [hy])
  have ex := Nat.div_add_mod x (2 ^ (i + 1))
  have ey := Nat.div_add_mod y (2 ^ (i + 1))
  rw [hq] at ex
  generalize 2 ^ (i + 1) * (y / 2 ^ (i + 1)) = q at ex ey
  omega

/-- `byteBit` at an index inside the string. -/
theorem byteBit_of_lt {b : ByteArray} {k : Nat} (hk : k / 8 < b.size) :
    byteBit b k = (b[k / 8]'hk).toNat.testBit (7 - k % 8) := by
  unfold byteBit; simp [hk]

theorem byteBit_of_ge {b : ByteArray} {k : Nat} (hk : b.size ≤ k / 8) : byteBit b k = false := by
  unfold byteBit; simp [Nat.not_lt.mpr hk]

theorem lt_size_of_byteBit {b : ByteArray} {k : Nat} (h : byteBit b k = true) : k / 8 < b.size :=
  Nat.lt_of_not_le fun hk => by rw [byteBit_of_ge hk] at h; cases h

private theorem compareLex_lt {α : Type} [Ord α] [Std.ReflOrd α] :
    ∀ (m : Nat) (xs ys : List α) (hx : m < xs.length) (hy : m < ys.length),
      (∀ j (h1 : j < xs.length) (h2 : j < ys.length), j < m → xs[j] = ys[j]) →
      compare xs[m] ys[m] = .lt → List.compareLex compare xs ys = .lt
  | 0, x :: xs, y :: ys, _, _, _, h => by
      simp only [List.getElem_cons_zero] at h
      simp [List.compareLex_cons_cons, h]
  | m + 1, x :: xs, y :: ys, hx, hy, he, h => by
      have h0 : x = y := he 0 (by simp) (by simp) (by omega)
      subst h0
      rw [List.compareLex_cons_cons, Std.ReflCmp.compare_self (cmp := compare)]
      exact compareLex_lt m xs ys (by simpa using hx) (by simpa using hy)
        (fun j h1 h2 hj => by simpa using he (j + 1) (by simpa using h1) (by simpa using h2) (by omega))
        (by simpa using h)

/-- The first differing bit decides `compare` (one direction). -/
theorem compare_lt_of_bits {a b : ByteArray} (hs : a.size = b.size) {k : Nat}
    (hpre : ∀ j, j < k → byteBit a j = byteBit b j) (ha : byteBit a k = false) (hb : byteBit b k = true) :
    compare a.data b.data = .lt := by
  have hkb := lt_size_of_byteBit hb
  have hka : k / 8 < a.size := hs ▸ hkb
  -- bytes before byte k/8 agree
  have hbyte : ∀ m (h1 : m < a.size) (h2 : m < b.size), m < k / 8 → a[m] = b[m] := by
    intro m h1 h2 hm
    apply UInt8.toNat_inj.mp
    apply Nat.eq_of_testBit_eq
    intro t
    by_cases ht : t < 8
    · have hi := hpre (8 * m + (7 - t)) (by omega)
      have e1 : (8 * m + (7 - t)) / 8 = m := by omega
      have e2 : 7 - (8 * m + (7 - t)) % 8 = t := by omega
      rw [byteBit_of_lt (by rw [e1]; exact h1), byteBit_of_lt (by rw [e1]; exact h2)] at hi
      simp only [e1, e2] at hi
      exact hi
    · rw [testBit_byte (by omega), testBit_byte (by omega)]
  -- byte k/8 of a is below byte k/8 of b
  have hlt : a[k / 8] < b[k / 8] := by
    rw [UInt8.lt_iff_toNat_lt]
    rw [byteBit_of_lt hka] at ha
    rw [byteBit_of_lt hkb] at hb
    refine nat_lt_of_testBit ha hb fun j hj => ?_
    by_cases hj8 : j < 8
    · have hi := hpre (8 * (k / 8) + (7 - j)) (by omega)
      have e1 : (8 * (k / 8) + (7 - j)) / 8 = k / 8 := by omega
      have e2 : 7 - (8 * (k / 8) + (7 - j)) % 8 = j := by omega
      rw [byteBit_of_lt (by rw [e1]; exact hka), byteBit_of_lt (by rw [e1]; exact hkb)] at hi
      simp only [e1, e2] at hi
      exact hi
    · rw [testBit_byte (by omega), testBit_byte (by omega)]
  rw [Array.compare_eq_compare_toList]
  exact compareLex_lt (k / 8) a.data.toList b.data.toList (by simpa using hka) (by simpa using hkb)
    (fun j h1 h2 hj => by simpa using hbyte j (by simpa using h1) (by simpa using h2) hj)
    (by simp only [Array.getElem_toList]; exact compareOfLessAndEq_eq_lt.mpr hlt)

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
theorem bitLt_refusalSpec_iff {E : Env D} {n : Nat} (hE : E.Lawful n) (k k' : RefusalSlot D) :
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

/-- The refusals' key order, in bytes. -/
def RefusalBefore (E : Env D) (p q : RefusalSlot D × RefusalLeaf) : Prop :=
  compare (refusalKeyBytes E p.1).data (refusalKeyBytes E q.1).data = .lt

/-- **The refusals part accepts a listing strictly ascending by key bytes**, as `build` makes of it. -/
theorem refusalsTrie_get_ok {E : Env D} {n : Nat} (hE : E.Lawful n) {dc : Stream D} {b : ByteArray}
    {i j : Nat} {l : List (RefusalSlot D × RefusalLeaf)}
    (h : (rawList worldMax (product (refusalSlot dc) refusalLeaf)).get b i = .ok (l, j))
    (ho : l.Pairwise (RefusalBefore E)) :
    (refusalsTrie E dc).get b i = .ok (Trie.build (refusalSpec E) (refusalSpec E).depth 0 l, j) :=
  trieListing_get_ok _ (refusals_separate hE) h
    (ho.imp fun hpq => (bitLt_refusalSpec_iff hE _ _).mpr hpq)

/-- **Every other refusals listing is refused `kernel/refusal-order` by name.** -/
theorem refusalsTrie_get_refused {E : Env D} {n : Nat} (hE : E.Lawful n) {dc : Stream D} {b : ByteArray}
    {i j : Nat} {l : List (RefusalSlot D × RefusalLeaf)}
    (h : (rawList worldMax (product (refusalSlot dc) refusalLeaf)).get b i = .ok (l, j))
    (ho : ¬ l.Pairwise (RefusalBefore E)) :
    (refusalsTrie E dc).get b i = .error (.rejected i "kernel/refusal-order") :=
  trieListing_get_refused _ (refusals_separate hE) h fun h' =>
    ho (h'.imp fun hpq => (bitLt_refusalSpec_iff hE _ _).mp hpq)

/-- What the refusals part accepts was strictly ascending by key bytes. -/
theorem refusalsTrie_get_ordered {E : Env D} {n : Nat} (hE : E.Lawful n) {dc : Stream D} {b : ByteArray}
    {i j : Nat} {t : Refusals D} (h : (refusalsTrie E dc).get b i = .ok (t, j)) :
    ∃ l, (rawList worldMax (product (refusalSlot dc) refusalLeaf)).get b i = .ok (l, j) ∧
      l.Pairwise (RefusalBefore E) ∧ t = Trie.build (refusalSpec E) (refusalSpec E).depth 0 l := by
  obtain ⟨l, hg, ho, ht⟩ := trieListing_get_ordered _ (refusals_separate hE) h
  exact ⟨l, hg, ho.imp fun hpq => (bitLt_refusalSpec_iff hE _ _).mp hpq, ht⟩

end Nanodregg.Codec.Kernel
