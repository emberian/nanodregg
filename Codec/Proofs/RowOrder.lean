import Codec.Proofs.SlotOrder
import Codec.Proofs.Rows
import Kernel.Proofs.RowsSep

/-!
# The rows trie's bit order is the order of its keys' bytes (KERNEL-46/48, CODEC-33)

A rows key's bytes are of VARIABLE width (a head is `parent ‖ rel ‖ 0`, a row
`parent ‖ rel ‖ 1 ‖ |k| ‖ k`), so `compare_lt_iff_bits` (one size) does not apply. What replaces
equal sizes is that the rows key codec is prefix-free: two different keys within bounds differ at a
byte inside both (`rowKeyBytes_differIn`, from `rowKey_lawfulOn`: a key's bytes read back as that key
at any offset, so no key's bytes begin another's).

* `compare_lt_iff_bits_differIn`: for two byte strings that differ at a byte inside both, `compare`
  is the order of the first differing bit, and that bit's byte is inside both.
* `rows_sepAt`: a listing of rows keys within bounds is separated, from KERNEL's `rows_separateOn`
  (on the keys' domain: outside it `byte8` truncates and no separation holds).
* `bitLt_rowSpec_iff`: over a lawful `Env` and a digest codec writing its bytes, a key routes before
  another in the rows trie exactly when its `rowKeyBytes` are below the other's in `compare`.
* `rowsTrie_get_ok` / `_refused` / `_ordered`: the World codec's rows part accepts a listing strictly
  ascending by key bytes (`RowBefore`) and refuses every other `kernel/row-order`.
-/

namespace Nanodregg.Codec.Kernel

open Nanodregg.Kernel Nanodregg.Codec.Stream

/-! ## Byte strings of different sizes -/

/-- Two byte strings differ at a byte inside both. -/
def DifferIn (a b : ByteArray) : Prop := ∃ m, ∃ (ha : m < a.size) (hb : m < b.size), a[m] ≠ b[m]

theorem differIn_symm {a b : ByteArray} (h : DifferIn a b) : DifferIn b a :=
  let ⟨m, ha, hb, hne⟩ := h; ⟨m, hb, ha, fun e => hne e.symm⟩

/-- A differing byte has a differing bit. -/
theorem bit_of_byte_ne {a b : ByteArray} {m : Nat} (ha : m < a.size) (hb : m < b.size) (h : a[m] ≠ b[m]) :
    ∃ k, k / 8 = m ∧ byteBit a k ≠ byteBit b k := by
  have hn : a[m].toNat ≠ b[m].toNat := fun e => h (UInt8.toNat_inj.mp e)
  have ht : ∃ t, a[m].toNat.testBit t ≠ b[m].toNat.testBit t :=
    Classical.byContradiction fun hno => hn (Nat.eq_of_testBit_eq fun t =>
      Classical.byContradiction fun hne => hno ⟨t, hne⟩)
  obtain ⟨t, htb⟩ := ht
  have t8 : t < 8 := by
    refine Nat.lt_of_not_le fun h8 => htb ?_
    rw [testBit_byte h8, testBit_byte h8]
  have e1 : (8 * m + (7 - t)) / 8 = m := by omega
  have e2 : 7 - (8 * m + (7 - t)) % 8 = t := by omega
  refine ⟨8 * m + (7 - t), e1, ?_⟩
  rw [byteBit_of_lt (by rw [e1]; exact ha), byteBit_of_lt (by rw [e1]; exact hb)]
  simp only [e1, e2]
  exact htb

/-- **Two byte strings that differ at a byte inside both differ at a first bit, inside both.** -/
theorem first_bit_of_differIn {a b : ByteArray} (h : DifferIn a b) :
    ∃ k, k / 8 < a.size ∧ k / 8 < b.size ∧ byteBit a k ≠ byteBit b k ∧
      ∀ j, j < k → byteBit a j = byteBit b j := by
  obtain ⟨m, ha, hb, hne⟩ := h
  obtain ⟨k0, hk0, hd0⟩ := bit_of_byte_ne ha hb hne
  have key : ∀ k, k / 8 ≤ m → byteBit a k ≠ byteBit b k →
      ∃ k', k' / 8 ≤ m ∧ byteBit a k' ≠ byteBit b k' ∧ ∀ j, j < k' → byteBit a j = byteBit b j := by
    intro k
    induction k using Nat.strongRecOn with
    | ind k ih =>
      intro hk hd
      by_cases hp : ∀ j, j < k → byteBit a j = byteBit b j
      · exact ⟨k, hk, hd, hp⟩
      · simp only [Classical.not_forall] at hp
        obtain ⟨j, hj, hjne⟩ := hp
        exact ih j hj (by omega) hjne
  obtain ⟨k, hk, hd, hp⟩ := key k0 (by omega) hd0
  exact ⟨k, by omega, by omega, hd, hp⟩

/-- Two first differing bits are one bit. -/
theorem first_bit_unique {a b : ByteArray} {i k : Nat} (hi : byteBit a i ≠ byteBit b i)
    (hpi : ∀ j, j < i → byteBit a j = byteBit b j) (hk : byteBit a k ≠ byteBit b k)
    (hpk : ∀ j, j < k → byteBit a j = byteBit b j) : i = k := by
  rcases Nat.lt_trichotomy i k with h | h | h
  · exact absurd (hpk i h) hi
  · exact h
  · exact absurd (hpi k h) hk

/-- **`compare` on two byte strings that differ inside both is the order of their first differing
bit**, and that bit's byte is inside both. -/
theorem compare_lt_iff_bits_differIn {a b : ByteArray} (h : DifferIn a b) :
    compare a.data b.data = .lt ↔
      ∃ k, k / 8 < a.size ∧ (∀ j, j < k → byteBit a j = byteBit b j) ∧ byteBit a k = false ∧
        byteBit b k = true := by
  obtain ⟨k, hka, hkb, hd, hp⟩ := first_bit_of_differIn h
  constructor
  · intro hc
    cases ha : byteBit a k
    · cases hb : byteBit b k
      · rw [ha, hb] at hd; exact absurd rfl hd
      · exact ⟨k, hka, hp, ha, hb⟩
    · cases hb : byteBit b k
      · have h' := compare_lt_of_bits_at hkb (fun j hj => (hp j hj).symm) hb ha
        rw [Std.OrientedCmp.eq_swap (cmp := compare), hc] at h'; cases h'
      · rw [ha, hb] at hd; exact absurd rfl hd
  · rintro ⟨k', hk', hp', ha', hb'⟩
    exact compare_lt_of_bits_at hk' hp' ha' hb'

/-! ## Rows keys -/

variable {D : Type} [Ord D]

omit [Ord D] in
/-- A rows key within bounds is at most `n + 5 + Bounds.keyBytesMax` bytes, at a digest of `n` (the
relation and the length are LEB128 below 256: at most two bytes each, cv 01a14f7e). -/
theorem rowKeyBytes_size_le {PD : D → Prop} {E : Env D} {n : Nat} (hs : ∀ d, (E.bytes d).size = n)
    {s : RowSlot D} (hf : RowSlot.Fits PD s) : (rowKeyBytes E s).size ≤ n + 5 + Bounds.keyBytesMax := by
  have hkb : Bounds.keyBytesMax = 128 := rfl
  cases s with
  | head p rel =>
    have := natBytes_size_le_two hf.2
    simp only [rowKeyBytes, ByteArray.size_append, hs, byte8_size]; omega
  | row key =>
    have h1 := natBytes_size_le_two hf.2.1
    have h2 := natBytes_size_le_two (r := key.k.size) (by have := hf.2.2; omega)
    have := hf.2.2
    simp only [rowKeyBytes, rowsPrefix, ByteArray.size_append, hs, byte8_size]; omega

omit [Ord D] in
/-- **Two different rows keys within bounds differ at a byte inside both**: the rows key codec is
lawful, so no key's bytes begin with another key's. -/
theorem rowKeyBytes_differIn {PD : D → Prop} {dc : Stream D} (hd : LawfulOn PD dc) {E : Env D}
    (hb : ∀ d, dc.bytes d = E.bytes d) {s s' : RowSlot D} (hs : RowSlot.Fits PD s) (hs' : RowSlot.Fits PD s')
    (hne : s ≠ s') : DifferIn (rowKeyBytes E s) (rowKeyBytes E s') := by
  have hk := rowKey_lawfulOn hd
  -- a key's bytes beginning another's read back as both keys
  have pre : ∀ {t t' : RowSlot D}, RowSlot.Fits PD t → RowSlot.Fits PD t' →
      (rowKeyBytes E t).size ≤ (rowKeyBytes E t').size →
      (∀ m (h1 : m < (rowKeyBytes E t).size) (h2 : m < (rowKeyBytes E t').size),
        (rowKeyBytes E t)[m] = (rowKeyBytes E t')[m]) → t = t' := by
    intro t t' ht ht' hle hagree
    rw [rowKeyBytes_eq hb, rowKeyBytes_eq hb] at hle hagree
    have hocc : OccursAt ((rowKey dc).bytes t') 0 ((rowKey dc).bytes t) :=
      occursAt_iff_getElem.mpr ⟨by omega, fun k hk' => by
        simpa using (hagree k hk' (by omega)).symm⟩
    have g1 := hk.get_of_occurs t _ 0 ht hocc
    have g2 := hk.get_of_occurs t' _ 0 ht' (occursAt_self _)
    rw [g1] at g2
    simp only [Except.ok.injEq, Prod.mk.injEq] at g2
    exact g2.1
  refine Classical.byContradiction fun hno => hne ?_
  have hagree : ∀ m (h1 : m < (rowKeyBytes E s).size) (h2 : m < (rowKeyBytes E s').size),
      (rowKeyBytes E s)[m] = (rowKeyBytes E s')[m] :=
    fun m h1 h2 => Classical.byContradiction fun h => hno ⟨m, h1, h2, h⟩
  rcases Nat.le_total (rowKeyBytes E s).size (rowKeyBytes E s').size with hle | hle
  · exact pre hs hs' hle hagree
  · exact (pre hs' hs hle fun m h1 h2 => (hagree m h2 h1).symm).symm

theorem rowDepth_bound {k n : Nat} (hn : n ≤ 32) (hk : k / 8 < n + 5 + Bounds.keyBytesMax) : k < Bounds.rowDepth := by
  unfold Bounds.rowDepth Bounds.keyBytesMax at *; omega

omit [Ord D] in
/-- A key in the key codec's domain is within KERNEL's bounds (`RowSlotFits`, the domain of
KERNEL's `rows_separateOn`). -/
theorem rowSlotFits_of_fits {PD : D → Prop} {s : RowSlot D} (h : RowSlot.Fits PD s) : RowSlotFits s := by
  cases s <;> simp_all [RowSlot.Fits, RowSlotFits]

/-- A rows listing whose keys are within bounds is separated (`Trie.SepAt` from depth 0), by KERNEL's
`rows_separateOn`. -/
theorem rows_sepAt {E : Env D} {n : Nat} (hE : E.Lawful n) {l : List (RowSlot D × RowLeaf)}
    (hl : ∀ p ∈ l, RowSlotFits p.1) : Trie.SepAt (rowSpec E) 0 l :=
  fun p hp _ _ hne =>
    let ⟨i, hi, h⟩ := rows_separateOn hE (hl p hp) hne
    ⟨i, Nat.zero_le i, hi, h⟩

/-- **The rows trie's routing is the order of the key bytes.** Over a lawful `Env` and a digest codec
writing its bytes, a rows key within bounds routes before another exactly when its `rowKeyBytes` are
below the other's in `compare`. -/
theorem bitLt_rowSpec_iff {PD : D → Prop} {dc : Stream D} (hd : LawfulOn PD dc) {E : Env D} {n : Nat}
    (hE : E.Lawful n) (hb : ∀ d, dc.bytes d = E.bytes d) {s s' : RowSlot D} (hs : RowSlot.Fits PD s)
    (hs' : RowSlot.Fits PD s') :
    BitLt (rowSpec E) 0 s s' ↔ compare (rowKeyBytes E s).data (rowKeyBytes E s').data = .lt := by
  by_cases he : s = s'
  · subst he
    rw [Std.ReflCmp.compare_self (cmp := compare)]
    exact ⟨fun h => absurd h (bitLt_irrefl _), fun h => by cases h⟩
  have hdi := rowKeyBytes_differIn hd hb hs hs' he
  rw [compare_lt_iff_bits_differIn hdi]
  obtain ⟨k, hka, hkb, hdk, hpk⟩ := first_bit_of_differIn hdi
  constructor
  · rintro ⟨i, _, _, hpre, h1, h2⟩
    have hpre' : ∀ j, j < i → byteBit (rowKeyBytes E s) j = byteBit (rowKeyBytes E s') j :=
      fun j hj => hpre j (Nat.zero_le j) hj
    have hdi' : byteBit (rowKeyBytes E s) i ≠ byteBit (rowKeyBytes E s') i := by
      show (rowSpec E).bit s i ≠ (rowSpec E).bit s' i
      rw [h1, h2]; decide
    have := first_bit_unique hdi' hpre' hdk hpk
    subst this
    exact ⟨i, hka, hpre', h1, h2⟩
  · rintro ⟨i, hia, hpre, h1, h2⟩
    exact ⟨i, Nat.zero_le i, rowDepth_bound hE.n_le (Nat.lt_of_lt_of_le hia (rowKeyBytes_size_le hE.size hs)),
      fun j _ hj => hpre j hj, h1, h2⟩

/-- The rows' key order, in bytes. -/
def RowBefore (E : Env D) (p q : RowSlot D × RowLeaf) : Prop :=
  compare (rowKeyBytes E p.1).data (rowKeyBytes E q.1).data = .lt

omit [Ord D] in
private theorem rowsListing_keys {PD : D → Prop} {dc : Stream D} (hd : LawfulOn PD dc) {b : ByteArray}
    {i j : Nat} {l : List (RowSlot D × RowLeaf)} (h : (rowsListing dc).get b i = .ok (l, j)) :
    ∀ p ∈ l, RowSlot.Fits PD p.1 :=
  fun p hp => (((rawList_lawfulOn (product_lawfulOn (rowKey_lawfulOn hd) rowLeaf_lawfulOn) worldMax
    (by decide)).occurs_of_get h).1.2 p hp).1

private theorem pairwise_rowBefore_iff {PD : D → Prop} {dc : Stream D} (hd : LawfulOn PD dc) {E : Env D} {n : Nat}
    (hE : E.Lawful n) (hb : ∀ d, dc.bytes d = E.bytes d) {l : List (RowSlot D × RowLeaf)}
    (hl : ∀ p ∈ l, RowSlot.Fits PD p.1) :
    l.Pairwise (fun p q => BitLt (rowSpec E) 0 p.1 q.1) ↔ l.Pairwise (RowBefore E) := by
  constructor
  · intro h
    exact List.Pairwise.imp_of_mem (fun hp hq hpq => (bitLt_rowSpec_iff hd hE hb (hl _ hp) (hl _ hq)).mp hpq) h
  · intro h
    exact List.Pairwise.imp_of_mem (fun hp hq hpq => (bitLt_rowSpec_iff hd hE hb (hl _ hp) (hl _ hq)).mpr hpq) h

variable [DecidableEq D]

/-- **The rows part accepts a listing strictly ascending by key bytes**, as `build` makes of it. -/
theorem rowsTrie_get_ok {PD : D → Prop} {dc : Stream D} (hd : LawfulOn PD dc) {E : Env D} {n : Nat}
    (hE : E.Lawful n) (hb : ∀ d, dc.bytes d = E.bytes d) {b : ByteArray} {i j : Nat}
    {l : List (RowSlot D × RowLeaf)} (h : (rowsListing dc).get b i = .ok (l, j)) (ho : l.Pairwise (RowBefore E)) :
    (rowsTrie E dc).get b i = .ok (Trie.build (rowSpec E) (rowSpec E).depth 0 l, j) :=
  trieListing_get_ok_sep _ h (rows_sepAt hE fun p hp => rowSlotFits_of_fits (rowsListing_keys hd h p hp))
    ((pairwise_rowBefore_iff hd hE hb (rowsListing_keys hd h)).mpr ho)

/-- **Every other rows listing is refused `kernel/row-order` by name.** -/
theorem rowsTrie_get_refused {PD : D → Prop} {dc : Stream D} (hd : LawfulOn PD dc) {E : Env D} {n : Nat}
    (hE : E.Lawful n) (hb : ∀ d, dc.bytes d = E.bytes d) {b : ByteArray} {i j : Nat}
    {l : List (RowSlot D × RowLeaf)} (h : (rowsListing dc).get b i = .ok (l, j)) (ho : ¬ l.Pairwise (RowBefore E)) :
    (rowsTrie E dc).get b i = .error (.rejected i "kernel/row-order") :=
  trieListing_get_refused_sep _ h (rows_sepAt hE fun p hp => rowSlotFits_of_fits (rowsListing_keys hd h p hp))
    fun h' => ho ((pairwise_rowBefore_iff hd hE hb (rowsListing_keys hd h)).mp h')

/-- What the rows part accepts was strictly ascending by key bytes. -/
theorem rowsTrie_get_ordered {PD : D → Prop} {dc : Stream D} (hd : LawfulOn PD dc) {E : Env D} {n : Nat}
    (hE : E.Lawful n) (hb : ∀ d, dc.bytes d = E.bytes d) {b : ByteArray} {i j : Nat} {t : Rows D}
    (h : (rowsTrie E dc).get b i = .ok (t, j)) :
    ∃ l, (rowsListing dc).get b i = .ok (l, j) ∧ l.Pairwise (RowBefore E) ∧
      t = Trie.build (rowSpec E) (rowSpec E).depth 0 l := by
  obtain ⟨l, hg, ho, ht⟩ := trieListing_get_ordered_sep _
    (fun l j hg => rows_sepAt hE fun p hp => rowSlotFits_of_fits (rowsListing_keys hd hg p hp)) h
  exact ⟨l, hg, (pairwise_rowBefore_iff hd hE hb (rowsListing_keys hd hg)).mp ho, ht⟩

end Nanodregg.Codec.Kernel
