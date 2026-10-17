import Codec.Ed25519

/-!
# The little-endian byte reads of Ed25519 invert `le32Bytes` (CODEC-23, signature correctness)

`leNat b off n` is the number the `n` bytes of `b` from `off` spell, least significant first; `le32Bytes`
writes `n < 2^256` as 32 such bytes. `leNat_le32Bytes`: reading them back is `n mod 2^256`. `leNat_lt`:
`n` bytes spell a number below `2^(8n)`. `leNat_append_left` / `leNat_append_right`: a read inside one half
of `a ++ b` is the read of that half. These are the byte facts `sign`/`verify` and `encodePoint`/
`decodePoint` meet at; no curve arithmetic is involved.
-/

namespace Nanodregg.Codec.Ed25519

theorem leNat_zero (b : ByteArray) (off : Nat) : leNat b off 0 = 0 := rfl

theorem leNat_succ (b : ByteArray) (off k : Nat) :
    leNat b off (k + 1) = leNat b (off + 1) k * 256 + (b.get! off).toNat := by
  unfold leNat
  rw [List.range_succ_eq_map, List.foldr_cons, List.foldr_map, Nat.add_zero]
  congr 2
  congr 1
  funext i acc
  rw [Nat.succ_eq_add_one, Nat.add_comm i 1, Nat.add_assoc]

/-- A read depends only on the bytes it reads. -/
theorem leNat_congr {b c : ByteArray} {off off' : Nat} :
    ∀ k, (∀ i < k, b.get! (off + i) = c.get! (off' + i)) → leNat b off k = leNat c off' k
  | 0, _ => rfl
  | k + 1, h => by
    rw [leNat_succ, leNat_succ, leNat_congr (off := off + 1) (off' := off' + 1) k (fun i hi => by
      rw [Nat.add_assoc, Nat.add_assoc, Nat.add_comm 1 i]; exact h (i + 1) (by omega))]
    have e := h 0 (by omega)
    rw [Nat.add_zero, Nat.add_zero] at e
    rw [e]

theorem leNat_lt (b : ByteArray) : ∀ (off k : Nat), leNat b off k < 2 ^ (8 * k)
  | _, 0 => by rw [leNat_zero]; decide
  | off, k + 1 => by
    rw [leNat_succ]
    have h := leNat_lt b (off + 1) k
    have hb := (b.get! off).toNat_lt
    rw [show 8 * (k + 1) = 8 * k + 8 from rfl, Nat.pow_add]
    have : (2 : Nat) ^ 8 = 256 := rfl
    rw [this]
    omega

private theorem get!_data (c : ByteArray) (i : Nat) : c.get! i = c.data[i]! := by
  cases c; rfl

theorem get!_append_left {a b : ByteArray} {i : Nat} (h : i < a.size) : (a ++ b).get! i = a.get! i := by
  rw [get!_data, get!_data, ByteArray.data_append, getElem!_pos (a.data ++ b.data) i
    (by rw [Array.size_append]; exact Nat.lt_of_lt_of_le h (Nat.le_add_right _ _)),
    getElem!_pos a.data i h, Array.getElem_append_left h]

theorem get!_append_right {a b : ByteArray} {i : Nat} (h : i < b.size) :
    (a ++ b).get! (a.size + i) = b.get! i := by
  rw [get!_data, get!_data, ByteArray.data_append, getElem!_pos (a.data ++ b.data) (a.size + i)
    (by rw [Array.size_append]; exact Nat.add_lt_add_left h _), getElem!_pos b.data i h,
    Array.getElem_append_right (by exact Nat.le_add_right _ _)]
  simp only [ByteArray.size_data, Nat.add_sub_cancel_left]
  rfl

theorem leNat_append_left {a b : ByteArray} {off k : Nat} (h : off + k ≤ a.size) :
    leNat (a ++ b) off k = leNat a off k :=
  leNat_congr k fun i hi => get!_append_left (by omega)

theorem leNat_append_right {a b : ByteArray} {k : Nat} (h : k ≤ b.size) :
    leNat (a ++ b) a.size k = leNat b 0 k :=
  leNat_congr k fun i hi => by rw [Nat.zero_add]; exact get!_append_right (by omega)

theorem le32Bytes_size (n : Nat) : (le32Bytes n).size = 32 := by
  unfold le32Bytes
  rw [ByteArray.size, Array.size_ofFn]

theorem le32Bytes_get! (n : Nat) {i : Nat} (h : i < 32) :
    (le32Bytes n).get! i = ((n >>> (8 * i)) % 256).toUInt8 := by
  rw [get!_data]
  unfold le32Bytes
  dsimp only
  rw [getElem!_pos _ i (by rw [Array.size_ofFn]; exact h), Array.getElem_ofFn]

private theorem le32_read (n : Nat) : ∀ k j, j + k ≤ 32 →
    leNat (le32Bytes n) j k = (n >>> (8 * j)) % 2 ^ (8 * k)
  | 0, j, _ => by rw [leNat_zero, Nat.mul_zero, Nat.pow_zero, Nat.mod_one]
  | k + 1, j, h => by
    rw [leNat_succ, le32_read n k (j + 1) (by omega), le32Bytes_get! n (by omega)]
    have t : (((n >>> (8 * j)) % 256).toUInt8).toNat = (n >>> (8 * j)) % 256 := by
      rw [Nat.toUInt8, UInt8.toNat_ofNat', Nat.mod_mod_of_dvd _ (by decide : 2 ^ 8 ∣ 256)]
    rw [t, show 8 * (j + 1) = 8 * j + 8 by omega, Nat.shiftRight_add, Nat.shiftRight_eq_div_pow _ 8,
      show 8 * (k + 1) = 8 + 8 * k by omega, Nat.pow_add, Nat.mod_mul]
    have : (2 : Nat) ^ 8 = 256 := rfl
    rw [this]
    omega

/-- Reading `le32Bytes n` back gives `n mod 2^256`. -/
theorem leNat_le32Bytes (n : Nat) : leNat (le32Bytes n) 0 32 = n % 2 ^ 256 := by
  rw [le32_read n 32 0 (by omega)]
  rfl

end Nanodregg.Codec.Ed25519
