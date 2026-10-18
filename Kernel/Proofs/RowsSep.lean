/-
# Kernel.Proofs.RowsSep — the rows trie separates its keys within bounds (KERNEL-48 `rows_separateOn`)

A rows key's bytes are `parent ‖ rel ‖ tag` (a head) or `parent ‖ rel ‖ tag ‖ |k| ‖ k` (a row). On a
lawful `Env` (fixed-width, injective digest bytes) and keys within bounds (`RowSlotFits`: `rel < 256`,
`|k| ≤ Bounds.keyBytesMax`), no key's bytes begin another's, so two different keys differ at a byte
inside both, hence at a bit below `Bounds.rowDepth` (`rows_separateOn`). With it, two canonical rows
tries holding one leaf at every slot are one trie (`rows_ext`): one rows root.
-/
import Kernel.Proofs.Cells

namespace Nanodregg.Kernel

variable {D : Type} [Ord D] [DecidableEq D]

/-- A rows key within the bounds admission keeps (`rowFits`' key half). -/
def RowSlotFits {D : Type} : RowSlot D → Prop
  | .head _ rel => rel < 256
  | .row key => key.rel < 256 ∧ key.k.size ≤ Bounds.keyBytesMax

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

/-! ## Byte lists -/

private theorem toList_length (a : ByteArray) : a.data.toList.length = a.size := by
  exact Array.length_toList

private theorem ba_eq_of_toList {a b : ByteArray} (h : a.data.toList = b.data.toList) : a = b := by
  cases a; cases b
  simp only [ByteArray.mk.injEq]
  exact Array.toList_inj.mp h

private theorem ofNat_inj {r r' : Nat} (hr : r < 256) (hr' : r' < 256) (h : UInt8.ofNat r = UInt8.ofNat r') :
    r = r' := by
  have := congrArg UInt8.toNat h
  rw [UInt8.toNat_ofNat_of_lt' (by unfold UInt8.size; omega), UInt8.toNat_ofNat_of_lt' (by unfold UInt8.size; omega)] at this
  exact this

omit [Ord D] [DecidableEq D] in
private theorem toList_head (E : Env D) (p : D) (rel : Nat) :
    (rowKeyBytes E (.head p rel)).data.toList = (E.bytes p).data.toList ++ [UInt8.ofNat rel, UInt8.ofNat 0] := by
  simp [rowKeyBytes, byte8]

omit [Ord D] [DecidableEq D] in
private theorem toList_row (E : Env D) (key : RowKey D) :
    (rowKeyBytes E (.row key)).data.toList = (E.bytes key.parent).data.toList ++
      ([UInt8.ofNat key.rel, UInt8.ofNat 1, UInt8.ofNat key.k.size] ++ key.k.data.toList) := by
  simp [rowKeyBytes, rowsPrefix, byte8]

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
/-- No key within bounds has bytes beginning another's (the rows key encoding is prefix-free). -/
private theorem rowKey_prefix {E : Env D} {n : Nat} (hE : E.Lawful n) {s s' : RowSlot D} (hs : RowSlotFits s)
    (hs' : RowSlotFits s') (hp : (rowKeyBytes E s).data.toList <+: (rowKeyBytes E s').data.toList) : s = s' := by
  obtain ⟨t, ht⟩ := hp
  have hlen : ∀ p : D, (E.bytes p).data.toList.length = n := fun p => by rw [toList_length, hE.size]
  have split : ∀ {p p' : D} {X Y : List UInt8}, (E.bytes p).data.toList ++ X ++ t = (E.bytes p').data.toList ++ Y →
      p = p' ∧ X ++ t = Y := by
    intro p p' X Y h
    rw [List.append_assoc] at h
    obtain ⟨h1, h2⟩ := List.append_inj h (by rw [hlen, hlen])
    exact ⟨hE.bytes_inj (ba_eq_of_toList h1), h2⟩
  cases s with
  | head p rel =>
      cases s' with
      | head p' rel' =>
          rw [toList_head, toList_head] at ht
          obtain ⟨rfl, h⟩ := split ht
          simp only [List.cons_append, List.nil_append, List.cons.injEq] at h
          rw [ofNat_inj hs hs' h.1]
      | row key' =>
          rw [toList_head, toList_row] at ht
          obtain ⟨-, h⟩ := split ht
          simp only [List.cons_append, List.nil_append, List.cons.injEq] at h
          exact absurd h.2.1 (by decide)
  | row key =>
      cases s' with
      | head p' rel' =>
          rw [toList_row, toList_head] at ht
          obtain ⟨-, h⟩ := split ht
          simp only [List.cons_append, List.nil_append, List.cons.injEq] at h
          exact absurd h.2.1 (by decide)
      | row key' =>
          rw [toList_row, toList_row] at ht
          obtain ⟨hpp, h⟩ := split ht
          simp only [List.cons_append, List.nil_append, List.cons.injEq] at h
          obtain ⟨hr, -, hl, hk⟩ := h
          have hrel := ofNat_inj hs.1 hs'.1 hr
          have hk1 := hs.2
          have hk2 := hs'.2
          have hkb : Bounds.keyBytesMax = 128 := rfl
          have hsz := ofNat_inj (by omega) (by omega) hl
          have hlk := congrArg List.length hk
          rw [List.length_append, toList_length, toList_length, hsz] at hlk
          have ht0 : t = [] := List.eq_nil_of_length_eq_zero (by omega)
          rw [ht0, List.append_nil] at hk
          obtain ⟨p, r, k⟩ := key
          obtain ⟨p', r', k'⟩ := key'
          simp only at hpp hrel hk
          subst hpp hrel
          rw [ba_eq_of_toList hk]

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
/-- **The rows trie separates its keys within bounds**: on a lawful `Env`, two different rows keys
within bounds are told apart at a bit below `Bounds.rowDepth`. -/
theorem rows_separateOn {E : Env D} {n : Nat} (hE : E.Lawful n) {s s' : RowSlot D} (hs : RowSlotFits s)
    (hs' : RowSlotFits s') (hne : s ≠ s') :
    ∃ i, i < (rowSpec E).depth ∧ (rowSpec E).bit s i ≠ (rowSpec E).bit s' i := by
  obtain ⟨m, h1, h2, hm⟩ := exists_ne_of_not_prefix _ _ (fun hp => hne (rowKey_prefix hE hs hs' hp))
    (fun hp => hne (rowKey_prefix hE hs' hs hp).symm)
  rw [toList_length] at h1 h2
  have hb : (rowKeyBytes E s)[m] ≠ (rowKeyBytes E s')[m] := by
    simpa [ByteArray.getElem_eq_getElem_data, Array.getElem_toList] using hm
  obtain ⟨i, hi, hbit⟩ := bit_of_byte_ne h1 h2 hb
  have hsize : (rowKeyBytes E s).size ≤ n + 3 + Bounds.keyBytesMax := by
    rw [← toList_length]
    cases s with
    | head p rel =>
        rw [toList_head]; simp only [List.length_append, toList_length, hE.size, List.length_cons,
          List.length_nil]; omega
    | row key =>
        rw [toList_row]; simp only [List.length_append, toList_length, hE.size, List.length_cons,
          List.length_nil]
        have := hs.2; omega
  have hn := hE.n_le
  refine ⟨i, ?_, hbit⟩
  show i < Bounds.rowDepth
  have hkb : Bounds.keyBytesMax = 128 := rfl
  have hrd : Bounds.rowDepth = 256 + 24 + 8 * 128 := rfl
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
  Trie.eq_of_get_eq_on (rowSpec E) RowSlotFits (fun _ _ hs hs' hne => rows_separateOn hE hs hs' hne) hc hc'
    (fun p hp => rowSlotFits_of_rowFits (hok p hp)) he

end Nanodregg.Kernel
