/-
# Kernel.Proofs.RowsSep — the rows key encoding is injective; the trie separates its keys within bounds

A rows key's bytes are `parent ‖ rel ‖ tag` (a head) or `parent ‖ rel ‖ tag ‖ |k| ‖ k` (a row), the
relation and the length as `natBytes` (LEB128, cv 01a14f7e). On a lawful `Env` (fixed-width, injective
digest bytes) the encoding is prefix-free and injective for EVERY key (`rowKeyBytes_append_inj`,
`rowKeyBytes_injective`; teeth `rowKeyBytes_rel_wrap_ne`, `rowKeyBytes_len_wrap_ne`: the one-byte
encoding before it wrapped both at 256). Within bounds (`RowSlotFits`: `rel < 256`,
`|k| ≤ Bounds.keyBytesMax`) a key is at most `n + 5 + Bounds.keyBytesMax` bytes, so two different keys
differ at a bit below `Bounds.rowDepth` (`rows_separateOn`): the bound is the trie's depth, not the
encoding's. With it, two canonical rows tries holding one leaf at every slot are one trie
(`rows_ext`): one rows root.
-/
import Kernel.Proofs.Cells

namespace Nanodregg.Kernel

variable {D : Type} [Ord D] [DecidableEq D]

omit [Ord D] [DecidableEq D] in
theorem rowSlotFits_of_rowFits {s : RowSlot D} {l : RowLeaf} (h : rowFits s l = true) : RowSlotFits s := by
  cases s with
  | head p rel =>
      cases l with
      | head _ _ _ _ _ _ _ =>
          simp only [rowFits, Bool.and_eq_true, decide_eq_true_eq] at h
          exact h.1.1.1.1.1.1
      | row _ _ _ => simp [rowFits] at h
  | row key =>
      cases l with
      | head _ _ _ _ _ _ _ => simp [rowFits] at h
      | row _ _ _ =>
          simp only [rowFits, Bool.and_eq_true, decide_eq_true_eq] at h
          exact ⟨h.1.1.1.1, h.1.1.1.2⟩

/-! ## The rows key encoding is prefix-free and injective, for every key (cv 01a14f7e) -/

private theorem toList_length (a : ByteArray) : a.data.toList.length = a.size := by
  exact Array.length_toList

private theorem ofNat_inj {r r' : Nat} (hr : r < 256) (hr' : r' < 256) (h : UInt8.ofNat r = UInt8.ofNat r') :
    r = r' := by
  have := congrArg UInt8.toNat h
  rw [UInt8.toNat_ofNat_of_lt' (by unfold UInt8.size; omega), UInt8.toNat_ofNat_of_lt' (by unfold UInt8.size; omega)] at this
  exact this

private theorem byte8_append_inj {a b : Nat} {x y : ByteArray} (ha : a < 256) (hb : b < 256)
    (h : byte8 a ++ x = byte8 b ++ y) : a = b ∧ x = y := by
  obtain ⟨h1, h2⟩ := Nanodregg.Codec.head_inj h
  exact ⟨ofNat_inj ha hb h1, h2⟩

omit [DecidableEq D] in
/-- **The rows key encoding is prefix-free and injective, for every key** (cv 01a14f7e): on a lawful
`Env`, two keys whose bytes, each followed by anything, are equal are one key, and the remainders are
equal. No bound on the relation or the key's length: both are `natBytes` (LEB128), prefix-free over
all of `Nat` (`natBytes_append_inj`); the parent's bytes have one size, the tag is one byte, and the
length then fixes the key's bytes. -/
theorem rowKeyBytes_append_inj {E : Env D} {n : Nat} (hE : E.Lawful n) {s s' : RowSlot D}
    {x y : ByteArray} (h : rowKeyBytes E s ++ x = rowKeyBytes E s' ++ y) : s = s' ∧ x = y := by
  have par : ∀ {p p' : D} {X Y : ByteArray}, E.bytes p ++ X = E.bytes p' ++ Y → p = p' ∧ X = Y :=
    fun h => by
      obtain ⟨h1, h2⟩ := bytes_append_inj h (by rw [hE.size, hE.size])
      exact ⟨hE.bytes_inj h1, h2⟩
  cases s with
  | head p rel =>
      cases s' with
      | head p' rel' =>
          simp only [rowKeyBytes, ByteArray.append_assoc] at h
          obtain ⟨hp, h1⟩ := par h
          obtain ⟨hr, h2⟩ := natBytes_append_inj h1
          exact ⟨by rw [hp, hr], (byte8_append_inj (by decide) (by decide) h2).2⟩
      | row key' =>
          simp only [rowKeyBytes, rowsPrefix, ByteArray.append_assoc] at h
          obtain ⟨-, h1⟩ := par h
          obtain ⟨-, h2⟩ := natBytes_append_inj h1
          exact absurd (byte8_append_inj (by decide) (by decide) h2).1 (by decide)
  | row key =>
      cases s' with
      | head p' rel' =>
          simp only [rowKeyBytes, rowsPrefix, ByteArray.append_assoc] at h
          obtain ⟨-, h1⟩ := par h
          obtain ⟨-, h2⟩ := natBytes_append_inj h1
          exact absurd (byte8_append_inj (by decide) (by decide) h2).1 (by decide)
      | row key' =>
          obtain ⟨p, r, k⟩ := key
          obtain ⟨p', r', k'⟩ := key'
          simp only [rowKeyBytes, rowsPrefix, ByteArray.append_assoc] at h
          obtain ⟨hp, h1⟩ := par h
          obtain ⟨hr, h2⟩ := natBytes_append_inj h1
          obtain ⟨-, h3⟩ := byte8_append_inj (by decide) (by decide) h2
          obtain ⟨hl, h4⟩ := natBytes_append_inj h3
          obtain ⟨hk, h5⟩ := bytes_append_inj h4 hl
          exact ⟨by rw [hp, hr, hk], h5⟩

omit [DecidableEq D] in
/-- **The rows key bytes determine the key, for every key** (cv 01a14f7e). -/
theorem rowKeyBytes_injective {E : Env D} {n : Nat} (hE : E.Lawful n) {s s' : RowSlot D}
    (h : rowKeyBytes E s = rowKeyBytes E s') : s = s' :=
  (rowKeyBytes_append_inj hE (x := ByteArray.empty) (y := ByteArray.empty)
    (by rw [ByteArray.append_empty, ByteArray.append_empty, h])).1

omit [DecidableEq D] in
/-- TOOTH (`rowKeyBytes_injective`, the defect cv 01a14f7e closed): relation 256 and relation 0
under one parent are two keys of the rows trie. Under the one-byte relation they were one. -/
theorem rowKeyBytes_rel_wrap_ne {E : Env D} {n : Nat} (hE : E.Lawful n) (p : D) :
    rowKeyBytes E (.head p 256) ≠ rowKeyBytes E (.head p 0) :=
  fun h => absurd (rowKeyBytes_injective hE h) (by simp)

omit [DecidableEq D] in
/-- TOOTH (`rowKeyBytes_append_inj`, its length half): the bytes of a 256-byte key are no continuation
of the empty key's, one relation, whatever follows. Under the one-byte length both read
`parent ‖ rel ‖ 1 ‖ 0`, so the empty key's bytes followed by 256 zero bytes WERE the long key's. -/
theorem rowKeyBytes_len_wrap_ne {E : Env D} {n : Nat} (hE : E.Lawful n) (p : D) (rel : Nat) (X : ByteArray) :
    rowKeyBytes E (.row ⟨p, rel, ByteArray.empty⟩) ++ X ≠ rowKeyBytes E (.row ⟨p, rel, ⟨Array.replicate 256 0⟩⟩) := by
  intro h
  have h' : rowKeyBytes E (.row ⟨p, rel, ByteArray.empty⟩) ++ X =
      rowKeyBytes E (.row ⟨p, rel, ⟨Array.replicate 256 0⟩⟩) ++ ByteArray.empty := by
    rw [ByteArray.append_empty]; exact h
  have := congrArg (fun s => match s with | RowSlot.row k => k.k.size | _ => 0) (rowKeyBytes_append_inj hE h').1
  simp at this

/-- Two lists neither of which begins the other differ at an index inside both. -/
private theorem exists_ne_of_not_prefix {α : Type} [DecidableEq α] :
    ∀ (l₁ l₂ : List α), ¬ l₁ <+: l₂ → ¬ l₂ <+: l₁ →
      ∃ m, ∃ (h1 : m < l₁.length) (h2 : m < l₂.length), l₁[m] ≠ l₂[m]
  | [], _, h, _ => absurd (List.nil_prefix) h
  | _ :: _, [], _, h => absurd (List.nil_prefix) h
  | a :: as, b :: bs, h, h' => by
      by_cases hab : a = b
      · subst hab
        obtain ⟨m, h1, h2, hm⟩ := exists_ne_of_not_prefix as bs
          (fun hp => h (List.prefix_cons_inj a |>.mpr hp)) (fun hp => h' (List.prefix_cons_inj a |>.mpr hp))
        exact ⟨m + 1, by simp; omega, by simp; omega, by simpa using hm⟩
      · exact ⟨0, by simp, by simp, by simpa using hab⟩

omit [DecidableEq D] in
/-- No key's bytes begin another's (the list form `rows_separateOn` reads), for every key. -/
private theorem rowKey_prefix {E : Env D} {n : Nat} (hE : E.Lawful n) {s s' : RowSlot D}
    (hp : (rowKeyBytes E s).data.toList <+: (rowKeyBytes E s').data.toList) : s = s' := by
  obtain ⟨t, ht⟩ := hp
  refine (rowKeyBytes_append_inj hE (x := ⟨t.toArray⟩) (y := ByteArray.empty) (ba_eq_of_toList ?_)).1
  simpa [ByteArray.data_append] using ht

omit [DecidableEq D] in
/-- A rows key within bounds is at most `n + 5 + Bounds.keyBytesMax` bytes. -/
theorem rowKeyBytes_size_bound {E : Env D} {n : Nat} (hE : E.Lawful n) {s : RowSlot D} (hs : RowSlotFits s) :
    (rowKeyBytes E s).size ≤ n + 5 + Bounds.keyBytesMax := by
  have hkb : Bounds.keyBytesMax = 128 := rfl
  cases s with
  | head p rel =>
      have := natBytes_size_le_two (r := rel) hs
      simp only [rowKeyBytes, ByteArray.size_append, hE.size, byte8_size]
      omega
  | row key =>
      have h1 := natBytes_size_le_two (r := key.rel) hs.1
      have h2 := natBytes_size_le_two (r := key.k.size) (by have := hs.2; omega)
      have h3 := hs.2
      simp only [rowKeyBytes, rowsPrefix, ByteArray.size_append, hE.size, byte8_size]
      omega

/-- A byte that differs gives a bit that differs, in that byte. -/
private theorem bit_of_byte_ne {a b : ByteArray} {m : Nat} (ha : m < a.size) (hb : m < b.size)
    (hne : a[m] ≠ b[m]) : ∃ i, i < 8 * (m + 1) ∧ byteBit a i ≠ byteBit b i := by
  refine Classical.byContradiction fun hno => hne ?_
  have hall : ∀ i, i < 8 * (m + 1) → byteBit a i = byteBit b i :=
    fun i hi => Classical.byContradiction fun h => hno ⟨i, hi, h⟩
  apply UInt8.toNat_inj.mp
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < 8
  · have e := hall (8 * m + (7 - j)) (by omega)
    have e1 : (8 * m + (7 - j)) / 8 = m := by omega
    have e2 : 7 - (8 * m + (7 - j)) % 8 = j := by omega
    unfold byteBit at e
    simp only [e1, e2, ha, hb, dite_true] at e
    exact e
  · rw [testBit_byte (by omega), testBit_byte (by omega)]

omit [DecidableEq D] in
/-- **The rows trie separates its keys within bounds**: on a lawful `Env`, a rows key within bounds
and any other key are told apart at a bit below `Bounds.rowDepth` (the other key needs no bound: the
encoding is prefix-free for every key, so they differ inside the bounded key's bytes). -/
theorem rows_separateOn {E : Env D} {n : Nat} (hE : E.Lawful n) {s s' : RowSlot D} (hs : RowSlotFits s)
    (hne : s ≠ s') :
    ∃ i, i < (rowSpec E).depth ∧ (rowSpec E).bit s i ≠ (rowSpec E).bit s' i := by
  obtain ⟨m, h1, h2, hm⟩ := exists_ne_of_not_prefix _ _ (fun hp => hne (rowKey_prefix hE hp))
    (fun hp => hne (rowKey_prefix hE hp).symm)
  rw [toList_length] at h1 h2
  have hb : (rowKeyBytes E s)[m] ≠ (rowKeyBytes E s')[m] := by
    simpa [ByteArray.getElem_eq_getElem_data, Array.getElem_toList] using hm
  obtain ⟨i, hi, hbit⟩ := bit_of_byte_ne h1 h2 hb
  have hsize := rowKeyBytes_size_bound hE hs
  have hn := hE.n_le
  refine ⟨i, ?_, hbit⟩
  show i < Bounds.rowDepth
  have hkb : Bounds.keyBytesMax = 128 := rfl
  have hrd : Bounds.rowDepth = 256 + 40 + 8 * 128 := rfl
  omega

omit [Ord D] [DecidableEq D] in
/-- **Contents determine the trie, on a separated domain**: two canonical tries that hold the same value
at every key are equal, when the bit function separates the keys the first holds. -/
theorem Trie.eq_of_get_eq_on {K V : Type} [DecidableEq K] (S : Trie.Spec K V D) (P : K → Prop)
    (hsep : ∀ k k', P k → P k' → k ≠ k' → ∃ i, i < S.depth ∧ S.bit k i ≠ S.bit k' i)
    {t t' : Trie.T K V D} (h : Trie.Canon S 0 t) (h' : Trie.Canon S 0 t') (hP : ∀ p ∈ t.toList, P p.1)
    (he : ∀ k, t.get S k = t'.get S k) : t = t' := by
  have hp : t.toList.Perm t'.toList :=
    Trie.perm_of_nodup_mem (Trie.nodup_of_map_fst (Trie.toList_nodup S 0 t h.1))
      (Trie.nodup_of_map_fst (Trie.toList_nodup S 0 t' h'.1)) fun p => by
        rw [Trie.mem_toList S 0 t h.1 p.1 p.2, Trie.mem_toList S 0 t' h'.1 p.1 p.2]
        exact iff_of_eq (congrArg (· = some p.2) (he p.1))
  have hs : Trie.SepAt S 0 t.toList := fun p hp' q hq hne => by
    obtain ⟨i, hi, hb⟩ := hsep p.1 q.1 (hP p hp') (hP q hq) hne; exact ⟨i, Nat.zero_le _, hi, hb⟩
  rw [← Trie.build_toList S 0 t h, ← Trie.build_toList S 0 t' h',
    Trie.build_perm S _ 0 _ _ hp (Trie.toList_nodup S 0 t h.1) rfl hs]

/-- **One rows trie, so one rows root**: two canonical rows tries, the first's entries fitting, that
read the same at every slot are equal. -/
theorem rows_ext {E : Env D} {n : Nat} (hE : E.Lawful n) {r r' : Rows D} (hc : Trie.Canon (rowSpec E) 0 r)
    (hc' : Trie.Canon (rowSpec E) 0 r') (hok : ∀ p ∈ r.toList, rowFits p.1 p.2 = true)
    (he : ∀ s, r.get (rowSpec E) s = r'.get (rowSpec E) s) : r = r' :=
  Trie.eq_of_get_eq_on (rowSpec E) RowSlotFits (fun _ _ hs _ hne => rows_separateOn hE hs hne) hc hc'
    (fun p hp => rowSlotFits_of_rowFits (hok p hp)) he

end Nanodregg.Kernel
