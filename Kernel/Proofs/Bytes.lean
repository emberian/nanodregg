/-
# Kernel.Proofs.Bytes — byte strings: concatenation, bits, and `compare`

* `bytes_append_inj`: when two concatenations are equal.
* `byteBit` at an index (`byteBit_of_lt`, `byteBit_of_ge`, `lt_size_of_byteBit`), a byte from its
  eight bits (`byte_eq_of_bits`, `byteBit_ext`).
* The first differing bit decides `compare` on the bytes (`compare_lt_of_bits_at`, at any sizes when
  the bit's byte is inside both; `compare_lt_of_bits`, one size). The codec's order proofs
  (`Codec.Proofs.SlotOrder`, `Codec.Proofs.RowOrder`) and the range read's
  (`Kernel.Proofs.RowsRange`) cite these.
-/
import Kernel.World

namespace Nanodregg.Kernel

theorem bytes_append_inj {x y x' y' : ByteArray} (h : x ++ y = x' ++ y') (hs : x.size = x'.size) :
    x = x' ∧ y = y' := by
  have hd : x.data ++ y.data = x'.data ++ y'.data := by
    rw [← ByteArray.data_append, ← ByteArray.data_append, h]
  obtain ⟨h₁, h₂⟩ := Array.append_inj hd hs
  exact ⟨ByteArray.ext h₁, ByteArray.ext h₂⟩

/-! ## Bits -/

theorem testBit_byte {x : UInt8} {k : Nat} (hk : 8 ≤ k) : x.toNat.testBit k = false :=
  Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le x.toNat_lt (Nat.pow_le_pow_right (by decide) hk))

/-- `byteBit` at an index inside the string. -/
theorem byteBit_of_lt {b : ByteArray} {k : Nat} (hk : k / 8 < b.size) :
    byteBit b k = (b[k / 8]'hk).toNat.testBit (7 - k % 8) := by
  unfold byteBit; simp [hk]

theorem byteBit_of_ge {b : ByteArray} {k : Nat} (hk : b.size ≤ k / 8) : byteBit b k = false := by
  unfold byteBit; simp [Nat.not_lt.mpr hk]

theorem lt_size_of_byteBit {b : ByteArray} {k : Nat} (h : byteBit b k = true) : k / 8 < b.size :=
  Nat.lt_of_not_le fun hk => by rw [byteBit_of_ge hk] at h; cases h

/-- Byte `j` of two strings is equal when its eight bits are. -/
theorem byte_eq_of_bits {a b : ByteArray} {j : Nat} (ha : j < a.size) (hb : j < b.size)
    (h : ∀ t, t < 8 → byteBit a (8 * j + t) = byteBit b (8 * j + t)) : a[j] = b[j] := by
  apply UInt8.toNat_inj.mp
  apply Nat.eq_of_testBit_eq
  intro t
  by_cases ht : t < 8
  · have hi := h (7 - t) (by omega)
    have e1 : (8 * j + (7 - t)) / 8 = j := by omega
    have e2 : 7 - (8 * j + (7 - t)) % 8 = t := by omega
    rw [byteBit_of_lt (by rw [e1]; exact ha), byteBit_of_lt (by rw [e1]; exact hb)] at hi
    simp only [e1, e2] at hi
    exact hi
  · rw [testBit_byte (by omega), testBit_byte (by omega)]

/-- Two byte strings of one size with the same bits are equal. -/
theorem byteBit_ext {a b : ByteArray} (hs : a.size = b.size)
    (h : ∀ i, i < 8 * a.size → byteBit a i = byteBit b i) : a = b := by
  apply ByteArray.ext; apply Array.ext (by simpa using hs)
  intro j hja hjb
  have := byte_eq_of_bits (a := a) (b := b) (j := j) hja (hs ▸ hja) fun t ht => h _ (by
    have : j < a.size := hja
    omega)
  simpa [ByteArray.getElem_eq_getElem_data] using this

/-! ## `compare` -/

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

/-- Lexicographic `compare` is decided at the first differing position. -/
theorem compareLex_lt {α : Type} [Ord α] [Std.ReflOrd α] :
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

/-- The first differing bit decides `compare` (one direction), at any sizes, when the bit's byte lies
inside both strings. -/
theorem compare_lt_of_bits_at {a b : ByteArray} {k : Nat} (hka : k / 8 < a.size)
    (hpre : ∀ j, j < k → byteBit a j = byteBit b j) (ha : byteBit a k = false) (hb : byteBit b k = true) :
    compare a.data b.data = .lt := by
  have hkb := lt_size_of_byteBit hb
  have hbyte : ∀ m (h1 : m < a.size) (h2 : m < b.size), m < k / 8 → a[m] = b[m] :=
    fun m h1 h2 hm => byte_eq_of_bits h1 h2 fun t ht => hpre _ (by omega)
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

/-- The first differing bit decides `compare` (one direction). -/
theorem compare_lt_of_bits {a b : ByteArray} (hs : a.size = b.size) {k : Nat}
    (hpre : ∀ j, j < k → byteBit a j = byteBit b j) (ha : byteBit a k = false) (hb : byteBit b k = true) :
    compare a.data b.data = .lt :=
  compare_lt_of_bits_at (hs ▸ lt_size_of_byteBit hb) hpre ha hb

end Nanodregg.Kernel
