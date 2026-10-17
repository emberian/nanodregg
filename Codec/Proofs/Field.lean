import Codec.Ed25519

/-!
# The field arithmetic is correct (CODEC-11's owed theorems)

`Fe.mul`, `Fe.add`, `Fe.sub` and `Fe.ofNat` compute in `ℤ/p` exactly: for CARRIED inputs (`Fe.Carried`,
the limb bounds every one of these operations returns), each result is carried again and its value
`toNat` is the field operation on the inputs' values. So no intermediate wraps 2^64: the 100-term
product stays below `267 · 2^52 < 2^61`, and every carry step below `2^63 + 2^38`. The schoolbook
identity (`mul_identity`: the product of the two limb sums IS the folded sum plus `p` times the
folded-away part) is a ring identity, generated from `Fe.mul`'s own text with every coefficient
checked against the limb positions, and closed by `grind`.
`mul_needs_carried` is the tooth: without the limb bounds the statement is false (a witness whose
limbs overflow), so `Fe.Carried` is not an empty or a vacuous premise.
-/

namespace Nanodregg.Codec.Ed25519

private theorem mask26 (h : UInt64) : (h &&& 67108863).toNat = h.toNat % 2 ^ 26 := by
  rw [UInt64.toNat_and, show (67108863 : UInt64).toNat = 2 ^ 26 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
private theorem mask25 (h : UInt64) : (h &&& 33554431).toNat = h.toNat % 2 ^ 25 := by
  rw [UInt64.toNat_and, show (33554431 : UInt64).toNat = 2 ^ 25 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
private theorem shr26 (h : UInt64) : (h >>> 26).toNat = h.toNat / 2 ^ 26 := by
  rw [UInt64.toNat_shiftRight]; simp [Nat.shiftRight_eq_div_pow]
private theorem shr25 (h : UInt64) : (h >>> 25).toNat = h.toNat / 2 ^ 25 := by
  rw [UInt64.toNat_shiftRight]; simp [Nat.shiftRight_eq_div_pow]
private theorem mod64 {a : Nat} (h : a < 2 ^ 64) : a % 2 ^ 64 = a := Nat.mod_eq_of_lt h

/-- Carried limbs: what every `Fe` operation returns (limbs 0, 1, 2, 4, 6, 8 below `2^26`, limbs 3,
5, 7, 9 below `2^25`). Any two carried elements may be multiplied, added or subtracted. -/
structure Fe.Carried (f : Fe) : Prop where
  l0 : f.l0.toNat < 2 ^ 26
  l1 : f.l1.toNat < 2 ^ 26
  l2 : f.l2.toNat < 2 ^ 26
  l3 : f.l3.toNat < 2 ^ 25
  l4 : f.l4.toNat < 2 ^ 26
  l5 : f.l5.toNat < 2 ^ 25
  l6 : f.l6.toNat < 2 ^ 26
  l7 : f.l7.toNat < 2 ^ 25
  l8 : f.l8.toNat < 2 ^ 26
  l9 : f.l9.toNat < 2 ^ 25

/-- The same bounds as a conjunction, for `simp` to unfold; `Fe.Carried` is a structure so that
elaboration never unfolds it into the limbs of a symbolic product. -/
private def CarriedP (f : Fe) : Prop :=
  f.l0.toNat < 2 ^ 26 ∧ f.l1.toNat < 2 ^ 26 ∧ f.l2.toNat < 2 ^ 26 ∧ f.l3.toNat < 2 ^ 25 ∧
  f.l4.toNat < 2 ^ 26 ∧ f.l5.toNat < 2 ^ 25 ∧ f.l6.toNat < 2 ^ 26 ∧ f.l7.toNat < 2 ^ 25 ∧
  f.l8.toNat < 2 ^ 26 ∧ f.l9.toNat < 2 ^ 25

private theorem Carried.ofP {f : Fe} (h : CarriedP f) : f.Carried :=
  let ⟨a, b, c, d, e, g, i, j, k, l⟩ := h; ⟨a, b, c, d, e, g, i, j, k, l⟩

private theorem Carried.lt {f : Fe} (h : f.Carried) :
    f.l0.toNat < 2 ^ 26 ∧ f.l1.toNat < 2 ^ 26 ∧ f.l2.toNat < 2 ^ 26 ∧ f.l3.toNat < 2 ^ 26 ∧
    f.l4.toNat < 2 ^ 26 ∧ f.l5.toNat < 2 ^ 26 ∧ f.l6.toNat < 2 ^ 26 ∧ f.l7.toNat < 2 ^ 26 ∧
    f.l8.toNat < 2 ^ 26 ∧ f.l9.toNat < 2 ^ 26 := by
  obtain ⟨a, b, c, d, e, f, g, h, i, j⟩ := h; omega

/-- A carry keeps the value mod `p`, for any limbs below `2^63`. -/
theorem carry_toNat (h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 : UInt64)
    (b0 : h0.toNat < 2 ^ 63) (b1 : h1.toNat < 2 ^ 63) (b2 : h2.toNat < 2 ^ 63) (b3 : h3.toNat < 2 ^ 63)
    (b4 : h4.toNat < 2 ^ 63) (b5 : h5.toNat < 2 ^ 63) (b6 : h6.toNat < 2 ^ 63) (b7 : h7.toNat < 2 ^ 63)
    (b8 : h8.toNat < 2 ^ 63) (b9 : h9.toNat < 2 ^ 63) :
    (Fe.carry h0 h1 h2 h3 h4 h5 h6 h7 h8 h9).toNat = (h0.toNat + h1.toNat * 2 ^ 26 + h2.toNat * 2 ^ 51 + h3.toNat * 2 ^ 77 + h4.toNat * 2 ^ 102 + h5.toNat * 2 ^ 128 + h6.toNat * 2 ^ 153 + h7.toNat * 2 ^ 179 + h8.toNat * 2 ^ 204 + h9.toNat * 2 ^ 230) % p := by
  simp only [Fe.carry, Fe.toNat, p, Nat.shiftLeft_eq, mask26, mask25, shr26, shr25, UInt64.toNat_add,
    UInt64.toNat_mul, UInt64.reduceToNat]
  simp (disch := omega) only [mod64]
  omega

/-- A carry returns carried limbs, for any limbs below `2^63`. -/
theorem carry_carried (h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 : UInt64)
    (b0 : h0.toNat < 2 ^ 63) (b1 : h1.toNat < 2 ^ 63) (b2 : h2.toNat < 2 ^ 63) (b3 : h3.toNat < 2 ^ 63)
    (b4 : h4.toNat < 2 ^ 63) (b5 : h5.toNat < 2 ^ 63) (b6 : h6.toNat < 2 ^ 63) (b7 : h7.toNat < 2 ^ 63)
    (b8 : h8.toNat < 2 ^ 63) (b9 : h9.toNat < 2 ^ 63) :
    (Fe.carry h0 h1 h2 h3 h4 h5 h6 h7 h8 h9).Carried := by
  apply Carried.ofP
  simp only [Fe.carry, CarriedP, mask26, mask25, shr26, shr25, UInt64.toNat_add,
    UInt64.toNat_mul, UInt64.reduceToNat]
  simp (disch := omega) only [mod64]
  omega

/-- The schoolbook product, as numbers: the folded sum plus `p` times the folded-away part. -/
private theorem mul_identity (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 : Nat) :
    (x0 + x1 * 2 ^ 26 + x2 * 2 ^ 51 + x3 * 2 ^ 77 + x4 * 2 ^ 102 + x5 * 2 ^ 128 + x6 * 2 ^ 153 + x7 * 2 ^ 179 + x8 * 2 ^ 204 + x9 * 2 ^ 230) * (y0 + y1 * 2 ^ 26 + y2 * 2 ^ 51 + y3 * 2 ^ 77 + y4 * 2 ^ 102 + y5 * 2 ^ 128 + y6 * 2 ^ 153 + y7 * 2 ^ 179 + y8 * 2 ^ 204 + y9 * 2 ^ 230) =
      x0 * y0 + 38 * (x1 * y9) + 19 * (x2 * y8) + 38 * (x3 * y7) + 19 * (x4 * y6) + 38 * (x5 * y5) + 19 * (x6 * y4) + 38 * (x7 * y3) + 19 * (x8 * y2) + 38 * (x9 * y1) + (x0 * y1 + x1 * y0 + 19 * (x2 * y9) + 19 * (x3 * y8) + 19 * (x4 * y7) + 19 * (x5 * y6) + 19 * (x6 * y5) + 19 * (x7 * y4) + 19 * (x8 * y3) + 19 * (x9 * y2)) * 2 ^ 26 + (x0 * y2 + 2 * (x1 * y1) + x2 * y0 + 38 * (x3 * y9) + 19 * (x4 * y8) + 38 * (x5 * y7) + 19 * (x6 * y6) + 38 * (x7 * y5) + 19 * (x8 * y4) + 38 * (x9 * y3)) * 2 ^ 51 + (x0 * y3 + x1 * y2 + x2 * y1 + x3 * y0 + 19 * (x4 * y9) + 19 * (x5 * y8) + 19 * (x6 * y7) + 19 * (x7 * y6) + 19 * (x8 * y5) + 19 * (x9 * y4)) * 2 ^ 77 + (x0 * y4 + 2 * (x1 * y3) + x2 * y2 + 2 * (x3 * y1) + x4 * y0 + 38 * (x5 * y9) + 19 * (x6 * y8) + 38 * (x7 * y7) + 19 * (x8 * y6) + 38 * (x9 * y5)) * 2 ^ 102 + (x0 * y5 + x1 * y4 + x2 * y3 + x3 * y2 + x4 * y1 + x5 * y0 + 19 * (x6 * y9) + 19 * (x7 * y8) + 19 * (x8 * y7) + 19 * (x9 * y6)) * 2 ^ 128 + (x0 * y6 + 2 * (x1 * y5) + x2 * y4 + 2 * (x3 * y3) + x4 * y2 + 2 * (x5 * y1) + x6 * y0 + 38 * (x7 * y9) + 19 * (x8 * y8) + 38 * (x9 * y7)) * 2 ^ 153 + (x0 * y7 + x1 * y6 + x2 * y5 + x3 * y4 + x4 * y3 + x5 * y2 + x6 * y1 + x7 * y0 + 19 * (x8 * y9) + 19 * (x9 * y8)) * 2 ^ 179 + (x0 * y8 + 2 * (x1 * y7) + x2 * y6 + 2 * (x3 * y5) + x4 * y4 + 2 * (x5 * y3) + x6 * y2 + 2 * (x7 * y1) + x8 * y0 + 38 * (x9 * y9)) * 2 ^ 204 + (x0 * y9 + x1 * y8 + x2 * y7 + x3 * y6 + x4 * y5 + x5 * y4 + x6 * y3 + x7 * y2 + x8 * y1 + x9 * y0) * 2 ^ 230 +
      (2 ^ 255 - 19) * (x1 * y9 * 2 ^ 1 + x2 * y8 * 2 ^ 0 + x3 * y7 * 2 ^ 1 + x4 * y6 * 2 ^ 0 + x5 * y5 * 2 ^ 1 + x6 * y4 * 2 ^ 0 + x7 * y3 * 2 ^ 1 + x8 * y2 * 2 ^ 0 + x9 * y1 * 2 ^ 1 + x2 * y9 * 2 ^ 26 + x3 * y8 * 2 ^ 26 + x4 * y7 * 2 ^ 26 + x5 * y6 * 2 ^ 26 + x6 * y5 * 2 ^ 26 + x7 * y4 * 2 ^ 26 + x8 * y3 * 2 ^ 26 + x9 * y2 * 2 ^ 26 + x3 * y9 * 2 ^ 52 + x4 * y8 * 2 ^ 51 + x5 * y7 * 2 ^ 52 + x6 * y6 * 2 ^ 51 + x7 * y5 * 2 ^ 52 + x8 * y4 * 2 ^ 51 + x9 * y3 * 2 ^ 52 + x4 * y9 * 2 ^ 77 + x5 * y8 * 2 ^ 77 + x6 * y7 * 2 ^ 77 + x7 * y6 * 2 ^ 77 + x8 * y5 * 2 ^ 77 + x9 * y4 * 2 ^ 77 + x5 * y9 * 2 ^ 103 + x6 * y8 * 2 ^ 102 + x7 * y7 * 2 ^ 103 + x8 * y6 * 2 ^ 102 + x9 * y5 * 2 ^ 103 + x6 * y9 * 2 ^ 128 + x7 * y8 * 2 ^ 128 + x8 * y7 * 2 ^ 128 + x9 * y6 * 2 ^ 128 + x7 * y9 * 2 ^ 154 + x8 * y8 * 2 ^ 153 + x9 * y7 * 2 ^ 154 + x8 * y9 * 2 ^ 179 + x9 * y8 * 2 ^ 179 + x9 * y9 * 2 ^ 205) := by
  grind

private theorem mul_spec {f g : Fe} (hf : f.Carried) (hg : g.Carried) :
    (f.mul g).Carried ∧ (f.mul g).toNat = f.toNat * g.toNat % p := by
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8, f9⟩ := f
  obtain ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9⟩ := g
  obtain ⟨hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9⟩ := Carried.lt hf
  obtain ⟨hg0, hg1, hg2, hg3, hg4, hg5, hg6, hg7, hg8, hg9⟩ := Carried.lt hg
  dsimp only at hf0 hf1 hf2 hf3 hf4 hf5 hf6 hf7 hf8 hf9 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9
  have e0 : (f0 * g0 + 38 * f1 * g9 + 19 * f2 * g8 + 38 * f3 * g7 + 19 * f4 * g6 + 38 * f5 * g5 + 19 * f6 * g4 + 38 * f7 * g3 + 19 * f8 * g2 + 38 * f9 * g1).toNat = f0.toNat * g0.toNat + 38 * (f1.toNat * g9.toNat) + 19 * (f2.toNat * g8.toNat) + 38 * (f3.toNat * g7.toNat) + 19 * (f4.toNat * g6.toNat) + 38 * (f5.toNat * g5.toNat) + 19 * (f6.toNat * g4.toNat) + 38 * (f7.toNat * g3.toNat) + 19 * (f8.toNat * g2.toNat) + 38 * (f9.toNat * g1.toNat) ∧ f0.toNat * g0.toNat + 38 * (f1.toNat * g9.toNat) + 19 * (f2.toNat * g8.toNat) + 38 * (f3.toNat * g7.toNat) + 19 * (f4.toNat * g6.toNat) + 38 * (f5.toNat * g5.toNat) + 19 * (f6.toNat * g4.toNat) + 38 * (f7.toNat * g3.toNat) + 19 * (f8.toNat * g2.toNat) + 38 * (f9.toNat * g1.toNat) < 2 ^ 63 := by
    have := Nat.mul_lt_mul'' hf0 hg0
    have := Nat.mul_lt_mul'' hf1 hg9
    have := Nat.mul_lt_mul'' hf2 hg8
    have := Nat.mul_lt_mul'' hf3 hg7
    have := Nat.mul_lt_mul'' hf4 hg6
    have := Nat.mul_lt_mul'' hf5 hg5
    have := Nat.mul_lt_mul'' hf6 hg4
    have := Nat.mul_lt_mul'' hf7 hg3
    have := Nat.mul_lt_mul'' hf8 hg2
    have := Nat.mul_lt_mul'' hf9 hg1
    simp only [UInt64.toNat_add, UInt64.toNat_mul, UInt64.reduceToNat]
    simp (disch := omega) only [mod64, Nat.mul_assoc, true_and]
    omega
  have e1 : (f0 * g1 + f1 * g0 + 19 * f2 * g9 + 19 * f3 * g8 + 19 * f4 * g7 + 19 * f5 * g6 + 19 * f6 * g5 + 19 * f7 * g4 + 19 * f8 * g3 + 19 * f9 * g2).toNat = f0.toNat * g1.toNat + f1.toNat * g0.toNat + 19 * (f2.toNat * g9.toNat) + 19 * (f3.toNat * g8.toNat) + 19 * (f4.toNat * g7.toNat) + 19 * (f5.toNat * g6.toNat) + 19 * (f6.toNat * g5.toNat) + 19 * (f7.toNat * g4.toNat) + 19 * (f8.toNat * g3.toNat) + 19 * (f9.toNat * g2.toNat) ∧ f0.toNat * g1.toNat + f1.toNat * g0.toNat + 19 * (f2.toNat * g9.toNat) + 19 * (f3.toNat * g8.toNat) + 19 * (f4.toNat * g7.toNat) + 19 * (f5.toNat * g6.toNat) + 19 * (f6.toNat * g5.toNat) + 19 * (f7.toNat * g4.toNat) + 19 * (f8.toNat * g3.toNat) + 19 * (f9.toNat * g2.toNat) < 2 ^ 63 := by
    have := Nat.mul_lt_mul'' hf0 hg1
    have := Nat.mul_lt_mul'' hf1 hg0
    have := Nat.mul_lt_mul'' hf2 hg9
    have := Nat.mul_lt_mul'' hf3 hg8
    have := Nat.mul_lt_mul'' hf4 hg7
    have := Nat.mul_lt_mul'' hf5 hg6
    have := Nat.mul_lt_mul'' hf6 hg5
    have := Nat.mul_lt_mul'' hf7 hg4
    have := Nat.mul_lt_mul'' hf8 hg3
    have := Nat.mul_lt_mul'' hf9 hg2
    simp only [UInt64.toNat_add, UInt64.toNat_mul, UInt64.reduceToNat]
    simp (disch := omega) only [mod64, Nat.mul_assoc, true_and]
    omega
  have e2 : (f0 * g2 + 2 * f1 * g1 + f2 * g0 + 38 * f3 * g9 + 19 * f4 * g8 + 38 * f5 * g7 + 19 * f6 * g6 + 38 * f7 * g5 + 19 * f8 * g4 + 38 * f9 * g3).toNat = f0.toNat * g2.toNat + 2 * (f1.toNat * g1.toNat) + f2.toNat * g0.toNat + 38 * (f3.toNat * g9.toNat) + 19 * (f4.toNat * g8.toNat) + 38 * (f5.toNat * g7.toNat) + 19 * (f6.toNat * g6.toNat) + 38 * (f7.toNat * g5.toNat) + 19 * (f8.toNat * g4.toNat) + 38 * (f9.toNat * g3.toNat) ∧ f0.toNat * g2.toNat + 2 * (f1.toNat * g1.toNat) + f2.toNat * g0.toNat + 38 * (f3.toNat * g9.toNat) + 19 * (f4.toNat * g8.toNat) + 38 * (f5.toNat * g7.toNat) + 19 * (f6.toNat * g6.toNat) + 38 * (f7.toNat * g5.toNat) + 19 * (f8.toNat * g4.toNat) + 38 * (f9.toNat * g3.toNat) < 2 ^ 63 := by
    have := Nat.mul_lt_mul'' hf0 hg2
    have := Nat.mul_lt_mul'' hf1 hg1
    have := Nat.mul_lt_mul'' hf2 hg0
    have := Nat.mul_lt_mul'' hf3 hg9
    have := Nat.mul_lt_mul'' hf4 hg8
    have := Nat.mul_lt_mul'' hf5 hg7
    have := Nat.mul_lt_mul'' hf6 hg6
    have := Nat.mul_lt_mul'' hf7 hg5
    have := Nat.mul_lt_mul'' hf8 hg4
    have := Nat.mul_lt_mul'' hf9 hg3
    simp only [UInt64.toNat_add, UInt64.toNat_mul, UInt64.reduceToNat]
    simp (disch := omega) only [mod64, Nat.mul_assoc, true_and]
    omega
  have e3 : (f0 * g3 + f1 * g2 + f2 * g1 + f3 * g0 + 19 * f4 * g9 + 19 * f5 * g8 + 19 * f6 * g7 + 19 * f7 * g6 + 19 * f8 * g5 + 19 * f9 * g4).toNat = f0.toNat * g3.toNat + f1.toNat * g2.toNat + f2.toNat * g1.toNat + f3.toNat * g0.toNat + 19 * (f4.toNat * g9.toNat) + 19 * (f5.toNat * g8.toNat) + 19 * (f6.toNat * g7.toNat) + 19 * (f7.toNat * g6.toNat) + 19 * (f8.toNat * g5.toNat) + 19 * (f9.toNat * g4.toNat) ∧ f0.toNat * g3.toNat + f1.toNat * g2.toNat + f2.toNat * g1.toNat + f3.toNat * g0.toNat + 19 * (f4.toNat * g9.toNat) + 19 * (f5.toNat * g8.toNat) + 19 * (f6.toNat * g7.toNat) + 19 * (f7.toNat * g6.toNat) + 19 * (f8.toNat * g5.toNat) + 19 * (f9.toNat * g4.toNat) < 2 ^ 63 := by
    have := Nat.mul_lt_mul'' hf0 hg3
    have := Nat.mul_lt_mul'' hf1 hg2
    have := Nat.mul_lt_mul'' hf2 hg1
    have := Nat.mul_lt_mul'' hf3 hg0
    have := Nat.mul_lt_mul'' hf4 hg9
    have := Nat.mul_lt_mul'' hf5 hg8
    have := Nat.mul_lt_mul'' hf6 hg7
    have := Nat.mul_lt_mul'' hf7 hg6
    have := Nat.mul_lt_mul'' hf8 hg5
    have := Nat.mul_lt_mul'' hf9 hg4
    simp only [UInt64.toNat_add, UInt64.toNat_mul, UInt64.reduceToNat]
    simp (disch := omega) only [mod64, Nat.mul_assoc, true_and]
    omega
  have e4 : (f0 * g4 + 2 * f1 * g3 + f2 * g2 + 2 * f3 * g1 + f4 * g0 + 38 * f5 * g9 + 19 * f6 * g8 + 38 * f7 * g7 + 19 * f8 * g6 + 38 * f9 * g5).toNat = f0.toNat * g4.toNat + 2 * (f1.toNat * g3.toNat) + f2.toNat * g2.toNat + 2 * (f3.toNat * g1.toNat) + f4.toNat * g0.toNat + 38 * (f5.toNat * g9.toNat) + 19 * (f6.toNat * g8.toNat) + 38 * (f7.toNat * g7.toNat) + 19 * (f8.toNat * g6.toNat) + 38 * (f9.toNat * g5.toNat) ∧ f0.toNat * g4.toNat + 2 * (f1.toNat * g3.toNat) + f2.toNat * g2.toNat + 2 * (f3.toNat * g1.toNat) + f4.toNat * g0.toNat + 38 * (f5.toNat * g9.toNat) + 19 * (f6.toNat * g8.toNat) + 38 * (f7.toNat * g7.toNat) + 19 * (f8.toNat * g6.toNat) + 38 * (f9.toNat * g5.toNat) < 2 ^ 63 := by
    have := Nat.mul_lt_mul'' hf0 hg4
    have := Nat.mul_lt_mul'' hf1 hg3
    have := Nat.mul_lt_mul'' hf2 hg2
    have := Nat.mul_lt_mul'' hf3 hg1
    have := Nat.mul_lt_mul'' hf4 hg0
    have := Nat.mul_lt_mul'' hf5 hg9
    have := Nat.mul_lt_mul'' hf6 hg8
    have := Nat.mul_lt_mul'' hf7 hg7
    have := Nat.mul_lt_mul'' hf8 hg6
    have := Nat.mul_lt_mul'' hf9 hg5
    simp only [UInt64.toNat_add, UInt64.toNat_mul, UInt64.reduceToNat]
    simp (disch := omega) only [mod64, Nat.mul_assoc, true_and]
    omega
  have e5 : (f0 * g5 + f1 * g4 + f2 * g3 + f3 * g2 + f4 * g1 + f5 * g0 + 19 * f6 * g9 + 19 * f7 * g8 + 19 * f8 * g7 + 19 * f9 * g6).toNat = f0.toNat * g5.toNat + f1.toNat * g4.toNat + f2.toNat * g3.toNat + f3.toNat * g2.toNat + f4.toNat * g1.toNat + f5.toNat * g0.toNat + 19 * (f6.toNat * g9.toNat) + 19 * (f7.toNat * g8.toNat) + 19 * (f8.toNat * g7.toNat) + 19 * (f9.toNat * g6.toNat) ∧ f0.toNat * g5.toNat + f1.toNat * g4.toNat + f2.toNat * g3.toNat + f3.toNat * g2.toNat + f4.toNat * g1.toNat + f5.toNat * g0.toNat + 19 * (f6.toNat * g9.toNat) + 19 * (f7.toNat * g8.toNat) + 19 * (f8.toNat * g7.toNat) + 19 * (f9.toNat * g6.toNat) < 2 ^ 63 := by
    have := Nat.mul_lt_mul'' hf0 hg5
    have := Nat.mul_lt_mul'' hf1 hg4
    have := Nat.mul_lt_mul'' hf2 hg3
    have := Nat.mul_lt_mul'' hf3 hg2
    have := Nat.mul_lt_mul'' hf4 hg1
    have := Nat.mul_lt_mul'' hf5 hg0
    have := Nat.mul_lt_mul'' hf6 hg9
    have := Nat.mul_lt_mul'' hf7 hg8
    have := Nat.mul_lt_mul'' hf8 hg7
    have := Nat.mul_lt_mul'' hf9 hg6
    simp only [UInt64.toNat_add, UInt64.toNat_mul, UInt64.reduceToNat]
    simp (disch := omega) only [mod64, Nat.mul_assoc, true_and]
    omega
  have e6 : (f0 * g6 + 2 * f1 * g5 + f2 * g4 + 2 * f3 * g3 + f4 * g2 + 2 * f5 * g1 + f6 * g0 + 38 * f7 * g9 + 19 * f8 * g8 + 38 * f9 * g7).toNat = f0.toNat * g6.toNat + 2 * (f1.toNat * g5.toNat) + f2.toNat * g4.toNat + 2 * (f3.toNat * g3.toNat) + f4.toNat * g2.toNat + 2 * (f5.toNat * g1.toNat) + f6.toNat * g0.toNat + 38 * (f7.toNat * g9.toNat) + 19 * (f8.toNat * g8.toNat) + 38 * (f9.toNat * g7.toNat) ∧ f0.toNat * g6.toNat + 2 * (f1.toNat * g5.toNat) + f2.toNat * g4.toNat + 2 * (f3.toNat * g3.toNat) + f4.toNat * g2.toNat + 2 * (f5.toNat * g1.toNat) + f6.toNat * g0.toNat + 38 * (f7.toNat * g9.toNat) + 19 * (f8.toNat * g8.toNat) + 38 * (f9.toNat * g7.toNat) < 2 ^ 63 := by
    have := Nat.mul_lt_mul'' hf0 hg6
    have := Nat.mul_lt_mul'' hf1 hg5
    have := Nat.mul_lt_mul'' hf2 hg4
    have := Nat.mul_lt_mul'' hf3 hg3
    have := Nat.mul_lt_mul'' hf4 hg2
    have := Nat.mul_lt_mul'' hf5 hg1
    have := Nat.mul_lt_mul'' hf6 hg0
    have := Nat.mul_lt_mul'' hf7 hg9
    have := Nat.mul_lt_mul'' hf8 hg8
    have := Nat.mul_lt_mul'' hf9 hg7
    simp only [UInt64.toNat_add, UInt64.toNat_mul, UInt64.reduceToNat]
    simp (disch := omega) only [mod64, Nat.mul_assoc, true_and]
    omega
  have e7 : (f0 * g7 + f1 * g6 + f2 * g5 + f3 * g4 + f4 * g3 + f5 * g2 + f6 * g1 + f7 * g0 + 19 * f8 * g9 + 19 * f9 * g8).toNat = f0.toNat * g7.toNat + f1.toNat * g6.toNat + f2.toNat * g5.toNat + f3.toNat * g4.toNat + f4.toNat * g3.toNat + f5.toNat * g2.toNat + f6.toNat * g1.toNat + f7.toNat * g0.toNat + 19 * (f8.toNat * g9.toNat) + 19 * (f9.toNat * g8.toNat) ∧ f0.toNat * g7.toNat + f1.toNat * g6.toNat + f2.toNat * g5.toNat + f3.toNat * g4.toNat + f4.toNat * g3.toNat + f5.toNat * g2.toNat + f6.toNat * g1.toNat + f7.toNat * g0.toNat + 19 * (f8.toNat * g9.toNat) + 19 * (f9.toNat * g8.toNat) < 2 ^ 63 := by
    have := Nat.mul_lt_mul'' hf0 hg7
    have := Nat.mul_lt_mul'' hf1 hg6
    have := Nat.mul_lt_mul'' hf2 hg5
    have := Nat.mul_lt_mul'' hf3 hg4
    have := Nat.mul_lt_mul'' hf4 hg3
    have := Nat.mul_lt_mul'' hf5 hg2
    have := Nat.mul_lt_mul'' hf6 hg1
    have := Nat.mul_lt_mul'' hf7 hg0
    have := Nat.mul_lt_mul'' hf8 hg9
    have := Nat.mul_lt_mul'' hf9 hg8
    simp only [UInt64.toNat_add, UInt64.toNat_mul, UInt64.reduceToNat]
    simp (disch := omega) only [mod64, Nat.mul_assoc, true_and]
    omega
  have e8 : (f0 * g8 + 2 * f1 * g7 + f2 * g6 + 2 * f3 * g5 + f4 * g4 + 2 * f5 * g3 + f6 * g2 + 2 * f7 * g1 + f8 * g0 + 38 * f9 * g9).toNat = f0.toNat * g8.toNat + 2 * (f1.toNat * g7.toNat) + f2.toNat * g6.toNat + 2 * (f3.toNat * g5.toNat) + f4.toNat * g4.toNat + 2 * (f5.toNat * g3.toNat) + f6.toNat * g2.toNat + 2 * (f7.toNat * g1.toNat) + f8.toNat * g0.toNat + 38 * (f9.toNat * g9.toNat) ∧ f0.toNat * g8.toNat + 2 * (f1.toNat * g7.toNat) + f2.toNat * g6.toNat + 2 * (f3.toNat * g5.toNat) + f4.toNat * g4.toNat + 2 * (f5.toNat * g3.toNat) + f6.toNat * g2.toNat + 2 * (f7.toNat * g1.toNat) + f8.toNat * g0.toNat + 38 * (f9.toNat * g9.toNat) < 2 ^ 63 := by
    have := Nat.mul_lt_mul'' hf0 hg8
    have := Nat.mul_lt_mul'' hf1 hg7
    have := Nat.mul_lt_mul'' hf2 hg6
    have := Nat.mul_lt_mul'' hf3 hg5
    have := Nat.mul_lt_mul'' hf4 hg4
    have := Nat.mul_lt_mul'' hf5 hg3
    have := Nat.mul_lt_mul'' hf6 hg2
    have := Nat.mul_lt_mul'' hf7 hg1
    have := Nat.mul_lt_mul'' hf8 hg0
    have := Nat.mul_lt_mul'' hf9 hg9
    simp only [UInt64.toNat_add, UInt64.toNat_mul, UInt64.reduceToNat]
    simp (disch := omega) only [mod64, Nat.mul_assoc, true_and]
    omega
  have e9 : (f0 * g9 + f1 * g8 + f2 * g7 + f3 * g6 + f4 * g5 + f5 * g4 + f6 * g3 + f7 * g2 + f8 * g1 + f9 * g0).toNat = f0.toNat * g9.toNat + f1.toNat * g8.toNat + f2.toNat * g7.toNat + f3.toNat * g6.toNat + f4.toNat * g5.toNat + f5.toNat * g4.toNat + f6.toNat * g3.toNat + f7.toNat * g2.toNat + f8.toNat * g1.toNat + f9.toNat * g0.toNat ∧ f0.toNat * g9.toNat + f1.toNat * g8.toNat + f2.toNat * g7.toNat + f3.toNat * g6.toNat + f4.toNat * g5.toNat + f5.toNat * g4.toNat + f6.toNat * g3.toNat + f7.toNat * g2.toNat + f8.toNat * g1.toNat + f9.toNat * g0.toNat < 2 ^ 63 := by
    have := Nat.mul_lt_mul'' hf0 hg9
    have := Nat.mul_lt_mul'' hf1 hg8
    have := Nat.mul_lt_mul'' hf2 hg7
    have := Nat.mul_lt_mul'' hf3 hg6
    have := Nat.mul_lt_mul'' hf4 hg5
    have := Nat.mul_lt_mul'' hf5 hg4
    have := Nat.mul_lt_mul'' hf6 hg3
    have := Nat.mul_lt_mul'' hf7 hg2
    have := Nat.mul_lt_mul'' hf8 hg1
    have := Nat.mul_lt_mul'' hf9 hg0
    simp only [UInt64.toNat_add, UInt64.toNat_mul]
    simp (disch := omega) only [mod64, true_and]
    omega
  simp only [Fe.mul]
  refine ⟨carry_carried _ _ _ _ _ _ _ _ _ _ (e0.1 ▸ e0.2) (e1.1 ▸ e1.2) (e2.1 ▸ e2.2) (e3.1 ▸ e3.2) (e4.1 ▸ e4.2)
    (e5.1 ▸ e5.2) (e6.1 ▸ e6.2) (e7.1 ▸ e7.2) (e8.1 ▸ e8.2) (e9.1 ▸ e9.2), ?_⟩
  rw [carry_toNat _ _ _ _ _ _ _ _ _ _ (e0.1 ▸ e0.2) (e1.1 ▸ e1.2) (e2.1 ▸ e2.2) (e3.1 ▸ e3.2) (e4.1 ▸ e4.2)
    (e5.1 ▸ e5.2) (e6.1 ▸ e6.2) (e7.1 ▸ e7.2) (e8.1 ▸ e8.2) (e9.1 ▸ e9.2),
    e0.1, e1.1, e2.1, e3.1, e4.1, e5.1, e6.1, e7.1, e8.1, e9.1]
  rw [Fe.toNat, Fe.toNat, ← Nat.mul_mod]
  simp only [Nat.shiftLeft_eq]
  rw [mul_identity f0.toNat f1.toNat f2.toNat f3.toNat f4.toNat f5.toNat f6.toNat f7.toNat f8.toNat f9.toNat g0.toNat g1.toNat g2.toNat g3.toNat g4.toNat g5.toNat g6.toNat g7.toNat g8.toNat g9.toNat, p, Nat.add_mul_mod_self_left]

/-- `Fe.mul` computes the product in the field. -/
theorem mul_toNat {f g : Fe} (hf : f.Carried) (hg : g.Carried) : (f.mul g).toNat = f.toNat * g.toNat % p :=
  (mul_spec hf hg).2

theorem mul_carried {f g : Fe} (hf : f.Carried) (hg : g.Carried) : (f.mul g).Carried := (mul_spec hf hg).1

theorem sq_toNat {f : Fe} (hf : f.Carried) : f.sq.toNat = f.toNat * f.toNat % p := mul_toNat hf hf
theorem sq_carried {f : Fe} (hf : f.Carried) : f.sq.Carried := mul_carried hf hf

private theorem add_spec {f g : Fe} (hf : f.Carried) (hg : g.Carried) :
    (f.add g).Carried ∧ (f.add g).toNat = (f.toNat + g.toNat) % p := by
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8, f9⟩ := f
  obtain ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9⟩ := g
  obtain ⟨hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9⟩ := Carried.lt hf
  obtain ⟨hg0, hg1, hg2, hg3, hg4, hg5, hg6, hg7, hg8, hg9⟩ := Carried.lt hg
  dsimp only at hf0 hf1 hf2 hf3 hf4 hf5 hf6 hf7 hf8 hf9 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9
  have s : ∀ a b : UInt64, a.toNat < 2 ^ 26 → b.toNat < 2 ^ 26 → (a + b).toNat = a.toNat + b.toNat := by
    intro a b ha hb; rw [UInt64.toNat_add]; exact mod64 (by omega)
  simp only [Fe.add]
  refine ⟨carry_carried _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_, ?_⟩
  all_goals (try rw [carry_toNat])
  all_goals (simp only [s _ _ hf0 hg0, s _ _ hf1 hg1, s _ _ hf2 hg2, s _ _ hf3 hg3, s _ _ hf4 hg4, s _ _ hf5 hg5,
    s _ _ hf6 hg6, s _ _ hf7 hg7, s _ _ hf8 hg8, s _ _ hf9 hg9, Fe.toNat, Nat.shiftLeft_eq, p]; try omega)

theorem add_toNat {f g : Fe} (hf : f.Carried) (hg : g.Carried) : (f.add g).toNat = (f.toNat + g.toNat) % p :=
  (add_spec hf hg).2
theorem add_carried {f g : Fe} (hf : f.Carried) (hg : g.Carried) : (f.add g).Carried := (add_spec hf hg).1

private theorem sub_spec {f g : Fe} (hf : f.Carried) (hg : g.Carried) :
    (f.sub g).Carried ∧ (f.sub g).toNat = (f.toNat + p - g.toNat) % p := by
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8, f9⟩ := f
  obtain ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9⟩ := g
  obtain ⟨hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9⟩ := Carried.lt hf
  obtain ⟨hg0, hg1, hg2, hg3, hg4, hg5, hg6, hg7, hg8, hg9⟩ := Carried.lt hg
  dsimp only at hf0 hf1 hf2 hf3 hf4 hf5 hf6 hf7 hf8 hf9 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9
  have s : ∀ a c b : UInt64, a.toNat < 2 ^ 26 → b.toNat < 2 ^ 26 → 2 ^ 26 ≤ c.toNat → c.toNat < 2 ^ 29 →
      (a + c - b).toNat = a.toNat + c.toNat - b.toNat := by
    intro a c b ha hb hc hc'
    have hac : (a + c).toNat = a.toNat + c.toNat := by rw [UInt64.toNat_add]; exact mod64 (by omega)
    rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, hac]; omega), hac]
  simp only [Fe.sub]
  refine ⟨carry_carried _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_, ?_⟩
  all_goals (try rw [carry_toNat])
  all_goals (simp only [s _ 268435380 _ hf0 hg0 (by decide) (by decide), s _ 134217724 _ hf1 hg1 (by decide) (by decide),
    s _ 268435452 _ hf2 hg2 (by decide) (by decide), s _ 134217724 _ hf3 hg3 (by decide) (by decide),
    s _ 268435452 _ hf4 hg4 (by decide) (by decide), s _ 134217724 _ hf5 hg5 (by decide) (by decide),
    s _ 268435452 _ hf6 hg6 (by decide) (by decide), s _ 134217724 _ hf7 hg7 (by decide) (by decide),
    s _ 268435452 _ hf8 hg8 (by decide) (by decide), s _ 134217724 _ hf9 hg9 (by decide) (by decide),
    UInt64.reduceToNat, Fe.toNat, Nat.shiftLeft_eq, p]; try omega)

/-- `Fe.sub` computes the difference in the field (as `f + p - g`, the value in `[0, 2p)`). -/
theorem sub_toNat {f g : Fe} (hf : f.Carried) (hg : g.Carried) : (f.sub g).toNat = (f.toNat + p - g.toNat) % p :=
  (sub_spec hf hg).2
theorem sub_carried {f g : Fe} (hf : f.Carried) (hg : g.Carried) : (f.sub g).Carried := (sub_spec hf hg).1

private theorem small (x n : Nat) (h : x < 2 ^ n) (hn : n ≤ 64 := by decide) : x.toUInt64.toNat = x := by
  rw [Nat.toUInt64_eq, UInt64.toNat_ofNat']; exact Nat.mod_eq_of_lt (by have := Nat.pow_le_pow_right (by decide : 0 < 2) hn; omega)

/-- `Fe.ofNat x` is carried, and its value is `x mod p`, for every `x < 2^255`. -/
private theorem ofNat_specP {x : Nat} (hx : x < 2 ^ 255) : CarriedP (Fe.ofNat x) ∧ (Fe.ofNat x).toNat = x % p := by
  simp only [Fe.ofNat, CarriedP, Fe.toNat, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, p]
  rw [small _ 26 (Nat.mod_lt _ (by decide)), small _ 25 (Nat.mod_lt _ (by decide)),
    small _ 26 (Nat.mod_lt _ (by decide)), small _ 25 (Nat.mod_lt _ (by decide)),
    small _ 26 (Nat.mod_lt _ (by decide)), small _ 25 (Nat.mod_lt _ (by decide)),
    small _ 26 (Nat.mod_lt _ (by decide)), small _ 25 (Nat.mod_lt _ (by decide)),
    small _ 26 (Nat.mod_lt _ (by decide)), small _ 25 (Nat.mod_lt _ (by decide))]
  have := Nat.mod_add_div x (2 ^ 26)
  have := Nat.mod_add_div (x / 2 ^ 26) (2 ^ 25)
  have : x / 2 ^ 26 / 2 ^ 25 = x / 2 ^ 51 := by rw [Nat.div_div_eq_div_mul, ← Nat.pow_add]
  have := Nat.mod_add_div (x / 2 ^ 51) (2 ^ 26)
  have : x / 2 ^ 51 / 2 ^ 26 = x / 2 ^ 77 := by rw [Nat.div_div_eq_div_mul, ← Nat.pow_add]
  have := Nat.mod_add_div (x / 2 ^ 77) (2 ^ 25)
  have : x / 2 ^ 77 / 2 ^ 25 = x / 2 ^ 102 := by rw [Nat.div_div_eq_div_mul, ← Nat.pow_add]
  have := Nat.mod_add_div (x / 2 ^ 102) (2 ^ 26)
  have : x / 2 ^ 102 / 2 ^ 26 = x / 2 ^ 128 := by rw [Nat.div_div_eq_div_mul, ← Nat.pow_add]
  have := Nat.mod_add_div (x / 2 ^ 128) (2 ^ 25)
  have : x / 2 ^ 128 / 2 ^ 25 = x / 2 ^ 153 := by rw [Nat.div_div_eq_div_mul, ← Nat.pow_add]
  have := Nat.mod_add_div (x / 2 ^ 153) (2 ^ 26)
  have : x / 2 ^ 153 / 2 ^ 26 = x / 2 ^ 179 := by rw [Nat.div_div_eq_div_mul, ← Nat.pow_add]
  have := Nat.mod_add_div (x / 2 ^ 179) (2 ^ 25)
  have : x / 2 ^ 179 / 2 ^ 25 = x / 2 ^ 204 := by rw [Nat.div_div_eq_div_mul, ← Nat.pow_add]
  have := Nat.mod_add_div (x / 2 ^ 204) (2 ^ 26)
  have : x / 2 ^ 204 / 2 ^ 26 = x / 2 ^ 230 := by rw [Nat.div_div_eq_div_mul, ← Nat.pow_add]
  have := Nat.mod_add_div (x / 2 ^ 230) (2 ^ 25)
  have : x / 2 ^ 230 / 2 ^ 25 = x / 2 ^ 255 := by rw [Nat.div_div_eq_div_mul, ← Nat.pow_add]
  have : x / 2 ^ 255 = 0 := Nat.div_eq_of_lt hx
  omega

theorem ofNat_spec {x : Nat} (hx : x < 2 ^ 255) : (Fe.ofNat x).Carried ∧ (Fe.ofNat x).toNat = x % p :=
  ⟨Carried.ofP (ofNat_specP hx).1, (ofNat_specP hx).2⟩

theorem zero_carried : Fe.zero.Carried := (ofNat_spec (by decide)).1
theorem one_carried : Fe.one.Carried := (ofNat_spec (by decide)).1
theorem zero_toNat : Fe.zero.toNat = 0 := (ofNat_spec (by decide)).2
theorem one_toNat : Fe.one.toNat = 1 := (ofNat_spec (by decide)).2

/-- `Fe.eq` decides equality of field values. -/
theorem eq_iff {f g : Fe} : f.eq g = true ↔ f.toNat = g.toNat := by simp [Fe.eq]

/-- An element whose limbs are past the carried bounds. -/
private def wide : Fe := ⟨2 ^ 40, 2 ^ 40, 2 ^ 40, 2 ^ 40, 2 ^ 40, 2 ^ 40, 2 ^ 40, 2 ^ 40, 2 ^ 40, 2 ^ 40⟩

/-- The tooth: `mul_toNat` is false without its premise (products of 2^40-limbs wrap 2^64), so
`Fe.Carried` carries content. -/
theorem mul_needs_carried : (wide.mul wide).toNat ≠ wide.toNat * wide.toNat % p := by decide +kernel

/-! ## Every element the verifier computes is carried

So the premises above hold for every `Fe` that `verify` and the point operations produce: the field
theorems apply to the whole computation, not to hand-picked inputs. -/

structure Point.Carried (P : Point) : Prop where
  X : P.X.Carried
  Y : P.Y.Carried
  Z : P.Z.Carried
  T : P.T.Carried

private theorem ofNat_carried {x : Nat} (hx : x < 2 ^ 255) : (Fe.ofNat x).Carried := (ofNat_spec hx).1

theorem d_carried : d.Carried := ofNat_carried (by decide)
theorem d2_carried : d2.Carried := ofNat_carried (by decide)
theorem sqrtM1_carried : sqrtM1.Carried := ofNat_carried (by decide)

theorem pow_carried {f : Fe} (hf : f.Carried) (e : Nat) : ∀ n, (f.pow e n).Carried
  | 0 => one_carried
  | n + 1 => by
    simp only [Fe.pow]
    have := sq_carried (pow_carried hf (e >>> 1) n)
    split
    · exact mul_carried this hf
    · exact this

theorem point_add_carried {P Q : Point} (hP : P.Carried) (hQ : Q.Carried) : (P.add Q).Carried := by
  obtain ⟨px, py, pz, pt⟩ := hP; obtain ⟨qx, qy, qz, qt⟩ := hQ
  have a := mul_carried (sub_carried py px) (sub_carried qy qx)
  have b := mul_carried (add_carried py px) (add_carried qy qx)
  have c := mul_carried (mul_carried pt d2_carried) qt
  have dd := mul_carried (add_carried pz pz) qz
  unfold Point.add
  dsimp only
  refine Point.Carried.mk ?_ ?_ ?_ ?_ <;> dsimp only
  · exact mul_carried (sub_carried b a) (sub_carried dd c)
  · exact mul_carried (add_carried dd c) (add_carried b a)
  · exact mul_carried (sub_carried dd c) (add_carried dd c)
  · exact mul_carried (sub_carried b a) (add_carried b a)

theorem point_double_carried {P : Point} (hP : P.Carried) : P.double.Carried := by
  obtain ⟨px, py, pz, _⟩ := hP
  have a := sq_carried px
  have b := sq_carried py
  have z := sq_carried pz
  have sc := sq_carried (add_carried px py)
  have H := add_carried a b
  have E := sub_carried H sc
  have G := sub_carried a b
  have F := add_carried (add_carried z z) G
  unfold Point.double
  dsimp only
  refine Point.Carried.mk ?_ ?_ ?_ ?_ <;> dsimp only
  · exact mul_carried E F
  · exact mul_carried G H
  · exact mul_carried F G
  · exact mul_carried E H

theorem point_neg_carried {P : Point} (hP : P.Carried) : P.neg.Carried := by
  unfold Point.neg
  exact ⟨sub_carried zero_carried hP.X, hP.Y, hP.Z, sub_carried zero_carried hP.T⟩

theorem point_zero_carried : Point.zero.Carried := by
  unfold Point.zero
  exact ⟨zero_carried, one_carried, one_carried, zero_carried⟩

theorem step_carried {P Q PQ R : Point} (hP : P.Carried) (hQ : Q.Carried) (hPQ : PQ.Carried)
    (hR : R.Carried) (a b : Nat) : (Point.step P Q PQ R a b).Carried := by
  have hd := point_double_carried hR
  simp only [Point.step]
  split
  · exact point_add_carried hd hPQ
  · exact point_add_carried hd hP
  · exact point_add_carried hd hQ
  · exact hd

theorem ladder_carried {P Q PQ R : Point} (hP : P.Carried) (hQ : Q.Carried) (hPQ : PQ.Carried)
    (hR : R.Carried) : ∀ (a b n : Nat), (Point.ladder P Q PQ R a b n).Carried
  | _, _, 0 => hR
  | a, b, n + 1 => step_carried hP hQ hPQ (ladder_carried hP hQ hPQ hR (a >>> 1) (b >>> 1) n) a b

theorem mul2_carried {P Q PQ : Point} (hP : P.Carried) (hQ : Q.Carried) (hPQ : PQ.Carried)
    (a b n : Nat) : (Point.mul2 P Q PQ a b n).Carried :=
  ladder_carried hP hQ hPQ point_zero_carried a b n

theorem B_carried : B.Carried := by
  have hx := ofNat_carried (x := 15112221349535400772501151409588531511454012693041857206046113283949847762202) (by decide)
  have hy := ofNat_carried (x := 46316835694926478169428394003475163141307993866256225615783033603165251855960) (by decide)
  unfold B
  refine Point.Carried.mk ?_ ?_ ?_ ?_ <;> dsimp only
  · exact hx
  · exact hy
  · exact one_carried
  · exact mul_carried hx hy

theorem candidateFrom_carried {u v v3 : Fe} (hu : u.Carried) (hv : v.Carried) (hv3 : v3.Carried) :
    (candidateFrom u v v3).Carried := by
  unfold candidateFrom
  exact mul_carried (mul_carried hu hv3) (pow_carried (mul_carried hu (mul_carried (sq_carried hv3) hv)) _ _)

theorem rootCheck_carried {u v x r : Fe} (hx : x.Carried) (h : rootCheck u v x = some r) : r.Carried := by
  unfold rootCheck at h
  dsimp only at h
  split at h
  · cases h; exact hx
  · split at h
    · cases h; exact mul_carried hx sqrtM1_carried
    · cases h

theorem recoverX_carried {y x : Fe} (hy : y.Carried) (h : recoverX y = some x) : x.Carried := by
  unfold recoverX sqrtRatio at h
  have hu := sub_carried (sq_carried hy) one_carried
  have hv := add_carried (mul_carried d_carried (sq_carried hy)) one_carried
  exact rootCheck_carried (candidateFrom_carried hu hv (mul_carried (sq_carried hv) hv)) h

theorem signed_carried {x y : Fe} {sign : Nat} {P : Point} (hx : x.Carried) (hy : y.Carried)
    (h : signed x y sign = some P) : P.Carried := by
  unfold signed at h
  split at h
  · cases h
  · have cs : (if (x.toNat % 2 == sign) = true then x else Fe.zero.sub x).Carried := by
      split
      · exact hx
      · exact sub_carried zero_carried hx
    rw [← Option.some.inj h]
    refine Point.Carried.mk ?_ ?_ ?_ ?_ <;> dsimp only
    · exact cs
    · exact hy
    · exact one_carried
    · exact mul_carried cs hy

/-- Every point `decodePoint` returns is carried, so the field theorems apply to `verify`'s inputs. -/
theorem decodePoint_carried {b : ByteArray} {off : Nat} {P : Point} (h : decodePoint b off = some P) :
    P.Carried := by
  unfold decodePoint at h
  dsimp only at h
  split at h
  · cases h
  · have hy := ofNat_carried (x := leNat b off 32 % 2 ^ 255) (Nat.mod_lt _ (by decide))
    split at h
    · cases h
    · rename_i x hx
      exact signed_carried (recoverX_carried hy hx) hy h

end Nanodregg.Codec.Ed25519
