import Codec.Varint
import Codec.Proofs.Raw

/-! # LEB128 is canonical below 2^32: one spelling per value, overlong spellings refused -/

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

theorem getVarint_of_occurs (b : ByteArray) (start : Nat) :
    ∀ (fuel n i k acc : Nat), (varint.bytes n).size ≤ fuel → (k > 0 → n > 0) → acc + n * 128 ^ k < 2 ^ 32 →
      OccursAt b i (varint.bytes n) →
      getVarint b start fuel i k acc = .ok (acc + n * 128 ^ k, i + (varint.bytes n).size)
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
      rw [getVarint_of_occurs b start fuel (n / 128) (i + 1) (k + 1) _ (by omega) (fun _ => by omega)
        (by rw [key]; exact hv) o2, key]
      congr 2
      omega

theorem occurs_of_getVarint (b : ByteArray) (start : Nat) :
    ∀ (fuel i k acc v j : Nat), getVarint b start fuel i k acc = .ok (v, j) →
      ∃ n, v = acc + n * 128 ^ k ∧ (k > 0 → n > 0) ∧ v < 2 ^ 32 ∧ j = i + (varint.bytes n).size ∧
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
        obtain ⟨n', hv, hk', hv32, hj, ho⟩ := occurs_of_getVarint b start fuel (i + 1) (k + 1) _ v j h
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

theorem varint_lawfulOn : LawfulOn (· < 2 ^ 32) varint where
  put_eq n buf := putVarint_eq n buf
  size_eq n := varintSize_eq n
  get_of_occurs n b i hn ho := by
    have := getVarint_of_occurs b i 5 n i 0 0 (varint_size_le n 4 (by omega)) (fun h => by omega)
      (by simpa using hn) ho
    simpa using this
  occurs_of_get {b i v j} h := by
    obtain ⟨n, hv, _, hv32, hj, ho⟩ := occurs_of_getVarint b i 5 i 0 0 v j h
    simp only [Nat.pow_zero, Nat.mul_one, Nat.zero_add] at hv
    subst hv
    exact ⟨hv32, hj, ho⟩

end Nanodregg.Codec.Stream
