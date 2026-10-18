/-
# Kernel.Proofs.TrieOrder — the trie's routing order (`BitLt`)

`BitLt S d k k'`: from depth `d`, at the first bit in `[d, depth)` where `k` and `k'` differ, `k`'s
is clear and `k'`'s set. The codec's listing-order proofs (`Codec.Proofs.TrieOrder`,
`SlotOrder`, `RowOrder`) and the range read's (`Kernel.Proofs.RowsRange.range_rows_sorted`) state
their orders in it.
-/
import Kernel.Trie

namespace Nanodregg.Kernel

section Bits
variable {K V D' : Type} (S : Trie.Spec K V D')

/-- `k` routes before `k'` from depth `d`: at the first bit in `[d, depth)` where they differ, the
bit of `k` is clear and the bit of `k'` is set. -/
def BitLt (d : Nat) (k k' : K) : Prop :=
  ∃ i, d ≤ i ∧ i < S.depth ∧ (∀ j, d ≤ j → j < i → S.bit k j = S.bit k' j) ∧
    S.bit k i = false ∧ S.bit k' i = true

theorem bitLt_irrefl {d : Nat} {k : K} : ¬ BitLt S d k k := fun ⟨_, _, _, _, h1, h2⟩ => by
  rw [h1] at h2; cases h2

theorem bitLt_asymm {d : Nat} {k k' : K} (h : BitLt S d k k') : ¬ BitLt S d k' k := by
  rintro ⟨i', hd', _, hpre', h1', h2'⟩
  obtain ⟨i, hd, _, hpre, h1, h2⟩ := h
  rcases Nat.lt_trichotomy i i' with hlt | rfl | hgt
  · have := hpre' i hd hlt; rw [h1, h2] at this; cases this
  · rw [h1] at h2'; cases h2'
  · have := hpre i' hd' hgt; rw [h1', h2'] at this; cases this

/-- Two keys parted at `d` the other way round are not in `BitLt` order from `d`. -/
theorem not_bitLt_of_bit {d : Nat} {k k' : K} (hk : S.bit k d = true) (hk' : S.bit k' d = false) :
    ¬ BitLt S d k k' := by
  rintro ⟨i, hd, _, hpre, h1, _⟩
  rcases Nat.lt_or_eq_of_le hd with hlt | rfl
  · have := hpre d (Nat.le_refl d) hlt; rw [hk, hk'] at this; cases this
  · rw [hk] at h1; cases h1

theorem bitLt_at {d : Nat} {k k' : K} (hd : d < S.depth) (hk : S.bit k d = false)
    (hk' : S.bit k' d = true) : BitLt S d k k' :=
  ⟨d, Nat.le_refl d, hd, fun _ hj hji => absurd hji (by omega), hk, hk'⟩

theorem not_bitLt_deep {d : Nat} {k k' : K} (hd : S.depth ≤ d) : ¬ BitLt S d k k' :=
  fun ⟨_, h1, h2, _⟩ => by omega

theorem bitLt_of_succ {d : Nat} {k k' : K} (h : BitLt S (d + 1) k k') (he : S.bit k d = S.bit k' d) :
    BitLt S d k k' := by
  obtain ⟨i, hd, hi, hpre, h1, h2⟩ := h
  refine ⟨i, by omega, hi, fun j hj hji => ?_, h1, h2⟩
  rcases Nat.lt_or_eq_of_le hj with hlt | rfl
  · exact hpre j hlt hji
  · exact he

theorem bitLt_succ {d : Nat} {k k' : K} (h : BitLt S d k k') (he : S.bit k d = S.bit k' d) :
    BitLt S (d + 1) k k' := by
  obtain ⟨i, hd, hi, hpre, h1, h2⟩ := h
  refine ⟨i, ?_, hi, fun j hj hji => hpre j (by omega) hji, h1, h2⟩
  rcases Nat.lt_or_eq_of_le hd with hlt | rfl
  · exact hlt
  · rw [h1, h2] at he; cases he

end Bits

end Nanodregg.Kernel
