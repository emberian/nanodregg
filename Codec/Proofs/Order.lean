import Codec.Proofs.Stream

/-!
# Codec.Proofs.Order — `u64be` writes numbers in the order of their bytes (LANG-57)

* `compare_append`: two byte lists of one length, each followed by anything, compare as the two
  lists and then the rest (lexicographic order cuts at a common length).
* `u64be_compare`: the bytes of two `u64be` values compare (lexicographically, as `compare` on the
  arrays) exactly as the numbers do. Tooth: `u64_misorders` — under the little-endian `u64`, 256's
  bytes come BEFORE 1's, so the same statement is false for `u64`.
-/

namespace Nanodregg.Codec.Stream

theorem nat_compare_ite (a b : Nat) : compare a b = if a < b then .lt else if a = b then .eq else .gt := by
  simp [compare, compareOfLessAndEq]

theorem u8_compare_toNat (x y : UInt8) : compare x y = compare x.toNat y.toNat := by
  simp [compare, compareOfLessAndEq, UInt8.lt_iff_toNat_lt, ← UInt8.toNat_inj]

theorem u64_compare_toNat (x y : UInt64) : compare x y = compare x.toNat y.toNat := by
  simp [compare, compareOfLessAndEq, UInt64.lt_iff_toNat_lt, ← UInt64.toNat_inj]

theorem then_assoc (a b c : Ordering) : (a.then b).then c = a.then (b.then c) := by
  cases a <;> rfl

theorem then_eq_right (a : Ordering) : a.then .eq = a := by
  cases a <;> rfl

theorem then_of_ne {a : Ordering} (h : a ≠ .eq) (b : Ordering) : a.then b = a := by
  cases a <;> first | rfl | exact absurd rfl h

/-- Lexicographic order cuts at a common length. -/
theorem compare_append {α : Type} [Ord α] [Std.ReflCmp (compare : α → α → Ordering)] {a b s t : List α}
    (h : a.length = b.length) : compare (a ++ s) (b ++ t) = (compare a b).then (compare s t) := by
  induction a generalizing b with
  | nil => cases b with
    | nil => simp [Ordering.then]
    | cons => simp at h
  | cons x a ih => cases b with
    | nil => simp at h
    | cons y b =>
      simp only [List.cons_append, List.compare_cons_cons]
      rw [ih (by simpa using h), then_assoc]

theorem nat_compare_digits {a b u v K : Nat} (hu : u < K) (hv : v < K) :
    compare (a * K + u) (b * K + v) = (compare a b).then (compare u v) := by
  rw [nat_compare_ite, nat_compare_ite a b, nat_compare_ite u v]
  rcases Nat.lt_trichotomy a b with h | rfl | h
  · have : a * K + u < b * K + v := by
      have := Nat.mul_le_mul_right K (Nat.succ_le_of_lt h); rw [Nat.succ_mul] at this; omega
    simp [h, this, Ordering.then]
  · by_cases h1 : u < v
    · simp [h1, Ordering.then]
    · by_cases h2 : u = v
      · simp [h2, Ordering.then]
      · simp [h1, h2, Ordering.then]
  · have : b * K + v < a * K + u := by
      have := Nat.mul_le_mul_right K (Nat.succ_le_of_lt h); rw [Nat.succ_mul] at this; omega
    have h' : ¬ a < b := by omega
    have h'' : a ≠ b := by omega
    have h3 : ¬ (a * K + u < b * K + v) := by omega
    have h4 : a * K + u ≠ b * K + v := by omega
    simp [h', h'', h3, h4, Ordering.then]

/-- The base-256 digits of `n` below `256 ^ k`, most significant first. -/
private def beDigits : Nat → Nat → List Nat
  | 0, _ => []
  | k + 1, n => (n / 256 ^ k % 256) :: beDigits k n

private theorem beDigits_compare : ∀ k a b, compare (beDigits k a) (beDigits k b) = compare (a % 256 ^ k) (b % 256 ^ k)
  | 0, a, b => by simp [beDigits, Nat.mod_one]
  | k + 1, a, b => by
    have ea : a % 256 ^ (k + 1) = (a / 256 ^ k % 256) * 256 ^ k + a % 256 ^ k := by
      rw [Nat.pow_succ, Nat.mod_mul, Nat.mul_comm (256 ^ k) _, Nat.add_comm]
    have eb : b % 256 ^ (k + 1) = (b / 256 ^ k % 256) * 256 ^ k + b % 256 ^ k := by
      rw [Nat.pow_succ, Nat.mod_mul, Nat.mul_comm (256 ^ k) _, Nat.add_comm]
    have hp : 0 < 256 ^ k := Nat.pow_pos (by decide)
    rw [ea, eb, nat_compare_digits (Nat.mod_lt _ hp) (Nat.mod_lt _ hp), ← beDigits_compare k a b]
    simp only [beDigits, List.compare_cons_cons]

theorem u8_list_compare : ∀ (l l' : List UInt8), compare l l' = compare (l.map UInt8.toNat) (l'.map UInt8.toNat)
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | x :: l, y :: l' => by
    simp only [List.map_cons, List.compare_cons_cons, u8_compare_toNat, u8_list_compare l l']

private theorem u64be_digits (v : UInt64) : (u64be.bytes v).data.toList.map UInt8.toNat = beDigits 8 v.toNat := by
  simp only [u64be_bytes, List.map_cons, List.map_nil, beDigits, UInt64.toNat_toUInt8, UInt64.toNat_shiftRight]
  simp [Nat.shiftRight_eq_div_pow]

/-- **`u64be` is order-preserving**: two values' bytes compare as the values do. -/
theorem u64be_compare (x y : UInt64) : compare (u64be.bytes x).data (u64be.bytes y).data = compare x y := by
  rw [Array.compare_eq_compare_toList, u8_list_compare, u64be_digits, u64be_digits, beDigits_compare,
    u64_compare_toNat, Nat.mod_eq_of_lt x.toNat_lt_size, Nat.mod_eq_of_lt y.toNat_lt_size]

theorem u64be_length (v : UInt64) : (u64be.bytes v).data.toList.length = 8 := by simp

/-- Tooth: under the little-endian `u64`, 256 is written BEFORE 1, so `u64be_compare` fails for `u64`. -/
theorem u64_misorders : compare (u64.bytes 256).data (u64.bytes 1).data = .lt ∧ compare (256 : UInt64) 1 = .gt := by
  refine ⟨?_, by decide⟩
  rw [Array.compare_eq_compare_toList, u8_list_compare]
  decide

/-- Its twin: under `u64be`, 1 is written before 256. -/
theorem u64be_orders_1_256 : compare (u64be.bytes 1).data (u64be.bytes 256).data = .lt := by
  rw [u64be_compare]; decide

end Nanodregg.Codec.Stream
