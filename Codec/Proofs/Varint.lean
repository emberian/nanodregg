import Codec.Varint
import Codec.Proofs.Raw

/-! # LEB128 is canonical: one spelling per value, overlong spellings refused

Below 2^32 in at most five bytes (`varint_lawfulOn`) and below 2^64 in at most ten (`varint64_lawfulOn`,
KERNEL-54), one reader `getVarint width limit` proved once for every width whose bytes reach the
limit (`limit ≤ 128 ^ width`). -/

namespace Nanodregg.Codec.Stream

theorem putVarint_eq (n : Nat) (buf : ByteArray) : putVarint n buf = buf ++ putVarint n ByteArray.empty := by
  induction n using Nat.strongRecOn generalizing buf with
  | _ n ih =>
    rw [putVarint.eq_1 n buf, putVarint.eq_1 n ByteArray.empty]
    by_cases h : n < 128
    · simp only [h, ↓reduceIte, push_eq_append, ByteArray.empty_append]
    · simp only [h, ↓reduceIte]
      rw [ih _ (by omega), ih (n / 128) (by omega) (ByteArray.empty.push _), push_eq_append, push_eq_append,
        ByteArray.empty_append, ByteArray.append_assoc]

theorem varint_bytes_small {n : Nat} (h : n < 128) : varint.bytes n = ⟨#[n.toUInt8]⟩ := by
  show putVarint n ByteArray.empty = _
  rw [putVarint.eq_1, if_pos h, push_eq_append, ByteArray.empty_append]

theorem varint_bytes_large {n : Nat} (h : ¬ n < 128) :
    varint.bytes n = ⟨#[(n % 128 + 128).toUInt8]⟩ ++ varint.bytes (n / 128) := by
  show putVarint n ByteArray.empty = _ ++ putVarint (n / 128) ByteArray.empty
  rw [putVarint.eq_1, if_neg h, putVarint_eq, push_eq_append, ByteArray.empty_append]

theorem varintSize_eq (n : Nat) : varintSize n = (varint.bytes n).size := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    rw [varintSize]
    split
    · rename_i h; rw [varint_bytes_small h]; rfl
    · rename_i h; rw [varint_bytes_large h, ByteArray.size_append, ← ih _ (by omega)]; simp

theorem varint_size_le (n : Nat) (m : Nat) (h : n < 128 ^ (m + 1)) : (varint.bytes n).size ≤ m + 1 := by
  induction m generalizing n with
  | zero => rw [varint_bytes_small (by simpa using h)]; simp
  | succ m ih =>
    by_cases hs : n < 128
    · rw [varint_bytes_small hs]; simp
    · rw [varint_bytes_large hs, ByteArray.size_append]
      have := ih (n / 128) (by rw [Nat.pow_succ] at h; omega)
      simp; omega

/-- A value of at least `128 ^ m` takes more than `m` bytes (the lower twin of `varint_size_le`). -/
theorem varint_size_ge (n : Nat) (m : Nat) (h : 128 ^ m ≤ n) : m + 1 ≤ (varint.bytes n).size := by
  induction m generalizing n with
  | zero =>
    by_cases hs : n < 128
    · rw [varint_bytes_small hs]; simp
    · rw [varint_bytes_large hs, ByteArray.size_append]; simp
  | succ m ih =>
    have hs : ¬ n < 128 := by
      have : 128 ≤ 128 ^ (m + 1) := Nat.le_self_pow (by omega) _
      omega
    rw [varint_bytes_large hs, ByteArray.size_append]
    have := ih (n / 128) (by
      rw [Nat.pow_succ] at h
      exact (Nat.le_div_iff_mul_le (by decide)).mpr h)
    simp; omega

theorem getVarint_of_occurs (width limit : Nat) (b : ByteArray) (start : Nat) :
    ∀ (fuel n i k acc : Nat), (varint.bytes n).size ≤ fuel → (k > 0 → n > 0) → acc + n * 128 ^ k < limit →
      OccursAt b i (varint.bytes n) →
      getVarint width limit b start fuel i k acc = .ok (acc + n * 128 ^ k, i + (varint.bytes n).size)
  | 0, n, i, k, acc, hf, _, _, _ => by
    have : 0 < (varint.bytes n).size := by
      by_cases h : n < 128
      · rw [varint_bytes_small h]; simp
      · rw [varint_bytes_large h, ByteArray.size_append]; show 0 < 1 + _; omega
    omega
  | fuel + 1, n, i, k, acc, hf, hk, hv, ho => by
    obtain ⟨hs, he⟩ := occursAt_iff_getElem.mp ho
    by_cases h : n < 128
    · have hsz : (varint.bytes n).size = 1 := by rw [varint_bytes_small h]; rfl
      have hb : b[i]'(by omega) = n.toUInt8 := by
        have := he 0 (by omega)
        simp only [Nat.add_zero] at this
        rw [this]; simp only [varint_bytes_small h]; rfl
      have hx : (b[i]'(by omega)).toNat = n := by rw [hb]; exact UInt8.toNat_ofNat_of_lt' (by simp [UInt8.size]; omega)
      rw [getVarint, dif_pos (by omega)]
      simp only [hx, h, ↓reduceIte, hsz]
      have : ¬ (n = 0 ∧ k > 0) := fun ⟨h0, h1⟩ => by have := hk h1; omega
      simp [this, hv]
    · have hsz := varint_bytes_large h
      rw [hsz] at ho hf ⊢
      obtain ⟨o1, o2⟩ := occursAt_append.mp ho
      have hb : b[i]'(by have := o1.1; simp at this; omega) = (n % 128 + 128).toUInt8 := by
        have := (occursAt_iff_getElem.mp o1).2 0 (by simp)
        simpa using this
      have hx : (b[i]'(by have := o1.1; simp at this; omega)).toNat = n % 128 + 128 := by
        rw [hb]; exact UInt8.toNat_ofNat_of_lt' (by simp [UInt8.size]; omega)
      simp only [ByteArray.size_append] at hf ⊢
      have s1 : (ByteArray.mk #[(n % 128 + 128).toUInt8]).size = 1 := rfl
      rw [s1] at hf o2 ⊢
      rw [getVarint, dif_pos (by have := o1.1; simp at this; omega)]
      simp only [hx, show ¬ (n % 128 + 128 < 128) by omega, ↓reduceIte, show n % 128 + 128 - 128 = n % 128 by omega]
      have key : acc + n % 128 * 128 ^ k + n / 128 * 128 ^ (k + 1) = acc + n * 128 ^ k := by
        have e : n * 128 ^ k = n % 128 * 128 ^ k + n / 128 * 128 ^ (k + 1) :=
          calc n * 128 ^ k = (n % 128 + 128 * (n / 128)) * 128 ^ k := by rw [Nat.mod_add_div]
            _ = n % 128 * 128 ^ k + n / 128 * 128 ^ (k + 1) := by
              rw [Nat.add_mul, Nat.pow_succ, Nat.mul_comm 128 (n / 128), Nat.mul_assoc,
                Nat.mul_comm 128 (128 ^ k)]
        omega
      rw [getVarint_of_occurs width limit b start fuel (n / 128) (i + 1) (k + 1) _ (by omega) (fun _ => by omega)
        (by rw [key]; exact hv) o2, key]
      congr 2
      omega

theorem occurs_of_getVarint (width limit : Nat) (b : ByteArray) (start : Nat) :
    ∀ (fuel i k acc v j : Nat), getVarint width limit b start fuel i k acc = .ok (v, j) →
      ∃ n, v = acc + n * 128 ^ k ∧ (k > 0 → n > 0) ∧ v < limit ∧ j = i + (varint.bytes n).size ∧
        OccursAt b i (varint.bytes n)
  | 0, _, _, _, _, _, h => by simp [getVarint] at h
  | fuel + 1, i, k, acc, v, j, h => by
    rw [getVarint] at h
    split at h
    · rename_i hi
      have hx := (b[i]'hi).toNat_lt
      dsimp only at h
      split at h
      · rename_i hlt
        split at h
        · cases h
        · rename_i hz
          split at h
          · rename_i hv
            cases h
            refine ⟨(b[i]'hi).toNat, rfl, fun hk => by omega, hv, ?_, ?_⟩
            · rw [varint_bytes_small hlt]; rfl
            · rw [varint_bytes_small hlt]
              refine occursAt_iff_getElem.mpr ⟨by show i + 1 ≤ b.size; omega, fun m hm => ?_⟩
              have : m = 0 := by have : m < 1 := hm; omega
              subst this
              simp
          · cases h
      · rename_i hge
        obtain ⟨n', hv, hk', hv32, hj, ho⟩ := occurs_of_getVarint width limit b start fuel (i + 1) (k + 1) _ v j h
        have hn'0 : n' > 0 := hk' (by omega)
        let n := ((b[i]'hi).toNat - 128) + 128 * n'
        have hn : ¬ n < 128 := by omega
        have hmod : n % 128 = (b[i]'hi).toNat - 128 := by omega
        have hdiv : n / 128 = n' := by omega
        refine ⟨n, ?_, fun _ => by omega, hv32, ?_, ?_⟩
        · rw [hv, Nat.pow_succ]
          show acc + ((b[i]'hi).toNat - 128) * 128 ^ k + n' * (128 ^ k * 128) =
            acc + (((b[i]'hi).toNat - 128) + 128 * n') * 128 ^ k
          rw [Nat.add_mul, Nat.mul_comm 128 n', Nat.mul_assoc n' 128, Nat.mul_comm 128 (128 ^ k), Nat.add_assoc]
        · rw [varint_bytes_large hn, ByteArray.size_append, hdiv, hj]; show _ = i + (1 + _); omega
        · rw [varint_bytes_large hn, hdiv]
          refine occursAt_append.mpr ⟨occursAt_iff_getElem.mpr ⟨by show i + 1 ≤ b.size; omega, fun m hm => ?_⟩, ho⟩
          have : m = 0 := by have : m < 1 := hm; omega
          subst this
          simp only [Nat.add_zero]
          show b[i] = (n % 128 + 128).toUInt8
          rw [hmod, show (b[i]'hi).toNat - 128 + 128 = (b[i]'hi).toNat by omega]
          simp
    · cases h

/-- The reader of width `width` and limit `limit` is lawful below the limit when every value below it
fits the width (`limit ≤ 128 ^ width`, a width of at least one byte): the one proof behind `varint` and `varint64`. -/
theorem varintOf_lawfulOn {m limit : Nat} (hw : limit ≤ 128 ^ (m + 1)) (sh : Shape) :
    LawfulOn (· < limit) (varintOf (m + 1) limit sh) where
  put_eq n buf := putVarint_eq n buf
  size_eq n := varintSize_eq n
  get_of_occurs n b i hn ho := by
    have hs : (varint.bytes n).size ≤ m + 1 := varint_size_le n m (by omega)
    have := getVarint_of_occurs (m + 1) limit b i (m + 1) n i 0 0 hs (fun h => by omega) (by simpa using hn) ho
    simpa using this
  occurs_of_get {b i v j} h := by
    obtain ⟨n, hv, _, hvl, hj, ho⟩ := occurs_of_getVarint (m + 1) limit b i (m + 1) i 0 0 v j h
    simp only [Nat.pow_zero, Nat.mul_one, Nat.zero_add] at hv
    subst hv
    exact ⟨hvl, hj, ho⟩

theorem varint_lawfulOn : LawfulOn (· < 2 ^ 32) varint := varintOf_lawfulOn (by decide) _

/-- **The u64 varint is lawful below 2^64** (KERNEL-54's versions and floors). -/
theorem varint64_lawfulOn : LawfulOn (· < 2 ^ 64) varint64 := varintOf_lawfulOn (by decide) _

/-- `varint64` writes `varint`'s digits: the two differ only in where the reader stops. -/
theorem varint64_bytes (n : Nat) : varint64.bytes n = varint.bytes n := rfl

/-- **Canonicity, exact**: an input decodes to `v` iff `v` is below 2^64 and the input is `v`'s one
spelling. So a non-minimal varint is refused: there is one encoding per value. -/
theorem varint64_decode_iff {b : ByteArray} {v : Nat} :
    varint64.decode b = .ok v ↔ v < 2 ^ 64 ∧ b = varint64.bytes v :=
  varint64_lawfulOn.decode_eq_ok_iff

/-- **The widest u64 varint is ten bytes** (KERNEL-55's `worldBytesMax` reads this width): a version
costs at most ten bytes on the World wire, against the eight its weight charges, so the World's bytes
are bounded by its weight plus two bytes per version, not by its weight. -/
theorem varint64_size_le {v : Nat} (h : v < 2 ^ 64) : (varint64.bytes v).size ≤ 10 :=
  varint_size_le v 9 (by omega)

/-- And the size the codec reports is that width. -/
theorem varint64_size_eq (v : Nat) : varint64.size v = (varint64.bytes v).size := varintSize_eq v

/-- **2^64 − 1 is exactly ten bytes, so the bound is reached**: the width is tight. -/
theorem varint64_size_max : (varint64.bytes (2 ^ 64 - 1)).size = 10 :=
  Nat.le_antisymm (varint64_size_le (by decide)) (varint_size_ge _ 9 (by decide))

/-! ## A byte string behind a LEB128 length (cv 01a14f7e) -/

theorem bytesV_bytes (max : Nat) (v : ByteArray) : (bytesV max).bytes v = varint.bytes v.size ++ v := rfl

/-- **`bytesV` is lawful on the strings of at most `max` bytes.** -/
theorem bytesV_lawfulOn (max : Nat) (fits : max < 2 ^ 32) : LawfulOn (·.size ≤ max) (bytesV max) where
  put_eq v buf := by
    rw [bytesV_bytes]
    show putVarint v.size buf ++ v = _
    rw [putVarint_eq, ByteArray.append_assoc]; rfl
  size_eq v := by rw [bytesV_bytes, ByteArray.size_append, ← varintSize_eq]; rfl
  get_of_occurs v b i hv h := by
    rw [bytesV_bytes] at h ⊢
    obtain ⟨h1, ⟨hs, he⟩⟩ := occursAt_append.mp h
    have hget := varint_lawfulOn.get_of_occurs _ _ _ (by omega) h1
    simp only [bytesV, hget, hv, ↓reduceIte, hs, ByteArray.size_append, ← Nat.add_assoc, he]
  occurs_of_get {b i v j} h := by
    simp only [bytesV] at h
    split at h
    · cases h
    · rename_i n k hk
      split at h
      · rename_i hmax
        split at h
        · rename_i hb
          cases h
          obtain ⟨-, rfl, o1⟩ := varint_lawfulOn.occurs_of_get hk
          have hsz : (b.extract (i + (varint.bytes n).size) (i + (varint.bytes n).size + n)).size = n := by
            rw [ByteArray.size_extract]; omega
          rw [bytesV_bytes, hsz]
          refine ⟨by omega, by simp only [ByteArray.size_append, hsz]; omega, occursAt_append.mpr ⟨o1, ?_⟩⟩
          exact ⟨by rw [hsz]; exact hb, by rw [hsz]⟩
        · cases h
      · cases h

end Nanodregg.Codec.Stream
