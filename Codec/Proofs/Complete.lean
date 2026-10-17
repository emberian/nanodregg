import Codec.Proofs.Curve
import Codec.Proofs.Prime

/-!
# Completeness: the Ed25519 formulas never divide by zero (CODEC-23 part 2)

`Codec.Proofs.Curve` proved that every point `verify` computes is on the curve and that `add`/`double`
are the Edwards law cross-multiplied — which would hold trivially if a result had `Z = 0`
(`onCurve_admits_degenerate`: `(0, 0, 0, 0)` satisfies the curve equations and sums to `Z = 0`). This
module closes that: `p` is prime (`Prime.p_prime`), so `Fin p` is a field (`fin_inv`, from Fermat);
`d` is not a square (`d_nonsquare`, Euler's criterion computed by `powMod`); `√−1² = −1`. Then on the
curve `(d x₁x₂y₁y₂)² ≠ 1` (`complete_affineR`, Bernstein–Lange), so a PROPER point (`Point.Proper`: on
the curve, `Z ≠ 0`) added to or doubled with a proper point is proper (`point_add_proper`,
`point_double_proper`), and so is every point `verify` computes (`B_proper`, `decodePoint_proper`,
`mul2_proper`). For proper points the cross-multiplied laws are the affine Edwards law.
-/

namespace Nanodregg.Codec.Ed25519

open Fin.NatCast

private theorem val_cast (a : Nat) : ((a : Fin p) : Nat) = a % p := rfl


/-! ## Over any commutative ring with inverses -/

section Complete
variable {R : Type} [Lean.Grind.CommRing R]

theorem domain_of_invR (inv : ∀ a : R, a ≠ 0 → ∃ b, a * b = 1) : ∀ a b : R, a * b = 0 → a = 0 ∨ b = 0 := by
  intro a b h
  apply Classical.byContradiction
  intro hn
  have ha : a ≠ 0 := fun e => hn (Or.inl e)
  have hb : b ≠ 0 := fun e => hn (Or.inr e)
  obtain ⟨c, hc⟩ := inv a ha
  apply hb
  have : c * (a * b) = b := by grind
  rw [h] at this; grind

theorem mul_ne_zeroR (inv : ∀ a : R, a ≠ 0 → ∃ b, a * b = 1) {a b : R} (ha : a ≠ 0) (hb : b ≠ 0) :
    a * b ≠ 0 := fun h => (domain_of_invR inv a b h).elim ha hb

/-- Bernstein–Lange: on `−x² + y² = 1 + d x² y²` with `d` a non-square and `−1 = i²`, the addition
denominators never vanish: `(d x₁x₂y₁y₂)² ≠ 1`. -/
theorem complete_affineR {d i x1 y1 x2 y2 : R} (inv : ∀ a : R, a ≠ 0 → ∃ b, a * b = 1)
    (ns : ∀ s : R, s * s ≠ d) (hi : i * i = 0 - 1) (h2 : (2 : R) ≠ 0) (h10 : (1 : R) ≠ 0)
    (c1 : y1 * y1 - x1 * x1 = 1 + d * (x1 * x1) * (y1 * y1))
    (c2 : y2 * y2 - x2 * x2 = 1 + d * (x2 * x2) * (y2 * y2)) :
    (d * x1 * x2 * y1 * y2) * (d * x1 * x2 * y1 * y2) ≠ 1 := by
  intro he
  have hx2 : x2 ≠ 0 := fun h => h10 (by rw [← he, h]; grind)
  have hy2 : y2 ≠ 0 := fun h => h10 (by rw [← he, h]; grind)
  have hi0 : i ≠ 0 := fun h => h10 (by have := hi; rw [h] at this; grind)
  have kp : (i * x1 + y1) * (i * x1 + y1) * (d * (x2 * y2) * (x2 * y2)) =
      (i * x2 + d * x1 * x2 * y1 * y2 * y2) * (i * x2 + d * x1 * x2 * y1 * y2 * y2) := by grind
  have km : (i * x1 - y1) * (i * x1 - y1) * (d * (x2 * y2) * (x2 * y2)) =
      (i * x2 - d * x1 * x2 * y1 * y2 * y2) * (i * x2 - d * x1 * x2 * y1 * y2 * y2) := by grind
  have hsum : (i * x2 + d * x1 * x2 * y1 * y2 * y2) + (i * x2 - d * x1 * x2 * y1 * y2 * y2) =
      2 * (i * x2) := by grind
  have h2ix : 2 * (i * x2) ≠ 0 := mul_ne_zeroR inv h2 (mul_ne_zeroR inv hi0 hx2)
  -- the square root of `d`, from either sign
  have root : ∀ {w u : R}, w * w * (d * (x2 * y2) * (x2 * y2)) = u * u → u ≠ 0 → False := by
    intro w u hk hu
    have huu : u * u ≠ 0 := mul_ne_zeroR inv hu hu
    have hw : w ≠ 0 := fun h => huu (by rw [← hk, h]; grind)
    obtain ⟨k, hk'⟩ := inv (w * x2 * y2) (mul_ne_zeroR inv (mul_ne_zeroR inv hw hx2) hy2)
    exact ns (u * k) (by grind)
  by_cases hp : i * x2 + d * x1 * x2 * y1 * y2 * y2 = 0
  · have hm : i * x2 - d * x1 * x2 * y1 * y2 * y2 ≠ 0 := fun h => h2ix (by rw [← hsum, hp, h]; grind)
    exact root km hm
  · exact root kp hp

/-- Projective completeness for addition: two proper points on the curve give `F G ≠ 0`, the `Z` of
their sum. -/
theorem add_properR {d i X1 Y1 Z1 T1 X2 Y2 Z2 T2 : R} (inv : ∀ a : R, a ≠ 0 → ∃ b, a * b = 1)
    (ns : ∀ s : R, s * s ≠ d) (hi : i * i = 0 - 1) (h2 : (2 : R) ≠ 0) (h10 : (1 : R) ≠ 0)
    (h1 : OnCurveR d X1 Y1 Z1 T1) (h2' : OnCurveR d X2 Y2 Z2 T2) (hz1 : Z1 ≠ 0) (hz2 : Z2 ≠ 0) :
    ((Z1 + Z1) * Z2 - T1 * (2 * d) * T2) * ((Z1 + Z1) * Z2 + T1 * (2 * d) * T2) ≠ 0 := by
  obtain ⟨e1, c1⟩ := h1; obtain ⟨e2, c2⟩ := h2'
  obtain ⟨u1, hu1⟩ := inv Z1 hz1
  obtain ⟨u2, hu2⟩ := inv Z2 hz2
  have a1 : (Y1 * u1) * (Y1 * u1) - (X1 * u1) * (X1 * u1) =
      1 + d * ((X1 * u1) * (X1 * u1)) * ((Y1 * u1) * (Y1 * u1)) := by grind
  have a2 : (Y2 * u2) * (Y2 * u2) - (X2 * u2) * (X2 * u2) =
      1 + d * ((X2 * u2) * (X2 * u2)) * ((Y2 * u2) * (Y2 * u2)) := by grind
  have hc := complete_affineR inv ns hi h2 h10 a1 a2
  have hne : 1 - (d * (X1 * u1) * (X2 * u2) * (Y1 * u1) * (Y2 * u2)) * (d * (X1 * u1) * (X2 * u2) * (Y1 * u1) * (Y2 * u2)) ≠ 0 :=
    fun h => hc (by grind)
  have eq : ((Z1 + Z1) * Z2 - T1 * (2 * d) * T2) * ((Z1 + Z1) * Z2 + T1 * (2 * d) * T2) =
      (2 * 2) * ((Z1 * Z1) * (Z2 * Z2)) *
        (1 - (d * (X1 * u1) * (X2 * u2) * (Y1 * u1) * (Y2 * u2)) * (d * (X1 * u1) * (X2 * u2) * (Y1 * u1) * (Y2 * u2))) := by
    grind
  rw [eq]
  exact mul_ne_zeroR inv (mul_ne_zeroR inv (mul_ne_zeroR inv h2 h2)
    (mul_ne_zeroR inv (mul_ne_zeroR inv hz1 hz1) (mul_ne_zeroR inv hz2 hz2))) hne

/-- Projective completeness for doubling. -/
theorem double_properR {d i X Y Z T : R} (inv : ∀ a : R, a ≠ 0 → ∃ b, a * b = 1)
    (ns : ∀ s : R, s * s ≠ d) (hi : i * i = 0 - 1) (h2 : (2 : R) ≠ 0) (h10 : (1 : R) ≠ 0)
    (h : OnCurveR d X Y Z T) (hz : Z ≠ 0) :
    (Z * Z + Z * Z + (X * X - Y * Y)) * (X * X - Y * Y) ≠ 0 := by
  obtain ⟨e, c⟩ := h
  obtain ⟨u, hu⟩ := inv Z hz
  have a : (Y * u) * (Y * u) - (X * u) * (X * u) = 1 + d * ((X * u) * (X * u)) * ((Y * u) * (Y * u)) := by grind
  have hc := complete_affineR inv ns hi h2 h10 a a
  have hne : 1 - (d * (X * u) * (X * u) * (Y * u) * (Y * u)) * (d * (X * u) * (X * u) * (Y * u) * (Y * u)) ≠ 0 :=
    fun h => hc (by grind)
  have eq : (Z * Z + Z * Z + (X * X - Y * Y)) * (X * X - Y * Y) =
      (0 - 1) * ((Z * Z) * (Z * Z)) *
        (1 - (d * (X * u) * (X * u) * (Y * u) * (Y * u)) * (d * (X * u) * (X * u) * (Y * u) * (Y * u))) := by
    grind
  rw [eq]
  have hm1 : (0 - 1 : R) ≠ 0 := fun h => h10 (by grind)
  exact mul_ne_zeroR inv (mul_ne_zeroR inv hm1 (mul_ne_zeroR inv (mul_ne_zeroR inv hz hz)
    (mul_ne_zeroR inv hz hz))) hne

end Complete

/-! ## `Fin p` is a field, `d` is not a square, `√−1` squares to `−1` -/

theorem p_eq : p = 57896044618658097711785492504343953926634992332820282019728792003956564819949 := by
  decide +kernel

theorem fin_one_ne_zero : (1 : Fin p) ≠ 0 := by decide +kernel
theorem fin_two_ne_zero : (2 : Fin p) ≠ 0 := by decide +kernel

theorem fin_fermat : ∀ x, x % p ≠ 0 → x ^ (p - 1) % p = 1 := by
  have hf := Prime.p_fermat
  rw [← p_eq] at hf
  exact hf

theorem fin_inv : ∀ a : Fin p, a ≠ 0 → ∃ b, a * b = 1 := by
  intro a ha
  refine ⟨((a.val ^ (p - 2) : Nat) : Fin p), ?_⟩
  have hav : a.val % p ≠ 0 := by rw [Nat.mod_eq_of_lt a.isLt]; exact fun h => ha (Fin.ext h)
  have hs : p - 2 + 1 = p - 1 := by rw [p_eq]
  apply Fin.ext
  rw [Fin.val_mul, val_cast, Nat.mul_mod_mod, ← Nat.pow_succ', Nat.succ_eq_add_one, hs, fin_fermat _ hav]
  rfl

theorem sqrtM1_sq : (sqrtM1.toNat : Fin p) * (sqrtM1.toNat : Fin p) = 0 - 1 := by
  unfold sqrtM1
  rw [(ofNat_spec (by decide +kernel)).2]
  decide +kernel

/-- Euler's criterion, one direction: `d^((p−1)/2) ≡ −1`, so `d` is not a square mod `p`. -/
theorem d_nonsquare : ∀ s : Fin p, s * s ≠ (d.toNat : Fin p) := by
  intro s hs
  have hD : d.toNat = 37095705934669439343138083508754565189542113879843219016388785533085940283555 % p := by
    unfold d; exact (ofNat_spec (by decide +kernel)).2
  have hE : Prime.powMod d.toNat ((p - 1) / 2) p 256 = p - 1 := by rw [hD]; decide +kernel
  rw [Prime.powMod_spec _ _ 256 _ (by rw [p_eq]; decide +kernel)] at hE
  have hv := congrArg Fin.val hs
  rw [Fin.val_mul, val_cast, Nat.mod_eq_of_lt (toNat_lt d)] at hv
  have hs0 : s.val % p ≠ 0 := by
    rw [Nat.mod_eq_of_lt s.isLt]
    intro h
    rw [h, Nat.zero_mul, Nat.zero_mod, hD] at hv
    exact absurd hv.symm (by decide +kernel)
  have h2 : 2 * ((p - 1) / 2) = p - 1 := by rw [p_eq]
  rw [← hv, ← Nat.pow_mod, ← Nat.pow_two, ← Nat.pow_mul, h2, fin_fermat _ hs0] at hE
  have : p - 1 ≠ 1 := by rw [p_eq]; decide
  exact this hE.symm

/-! ## Proper points: on the curve with `Z ≠ 0`, kept by every step -/

/-- A point on the curve whose `Z` is a unit: it names the affine point `(X/Z, Y/Z)`. -/
structure Point.Proper (P : Point) : Prop where
  on : P.OnCurve
  z : (P.Z.toNat : Fin p) ≠ 0

theorem point_add_proper {P Q : Point} (hP : P.Proper) (hQ : Q.Proper) : (P.add Q).Proper := by
  refine ⟨point_add_onCurve hP.on hQ.on, ?_⟩
  rw [(point_add_vals hP.on.carried hQ.on.carried).2.2.1]
  exact add_properR fin_inv d_nonsquare sqrtM1_sq fin_two_ne_zero fin_one_ne_zero hP.on.on hQ.on.on hP.z hQ.z

theorem point_double_proper {P : Point} (hP : P.Proper) : P.double.Proper := by
  refine ⟨point_double_onCurve hP.on, ?_⟩
  rw [(point_double_vals hP.on.carried).2.2.1]
  exact double_properR fin_inv d_nonsquare sqrtM1_sq fin_two_ne_zero fin_one_ne_zero hP.on.on hP.z

theorem point_neg_proper {P : Point} (hP : P.Proper) : P.neg.Proper :=
  ⟨point_neg_onCurve hP.on, by unfold Point.neg; dsimp only; exact hP.z⟩

theorem point_zero_proper : Point.zero.Proper :=
  ⟨point_zero_onCurve, by unfold Point.zero; dsimp only; rw [val_one]; exact fin_one_ne_zero⟩

theorem step_proper {P Q PQ R : Point} (hP : P.Proper) (hQ : Q.Proper) (hPQ : PQ.Proper)
    (hR : R.Proper) (a b : Nat) : (Point.step P Q PQ R a b).Proper := by
  have hd := point_double_proper hR
  simp only [Point.step]
  split
  · exact point_add_proper hd hPQ
  · exact point_add_proper hd hP
  · exact point_add_proper hd hQ
  · exact hd

theorem ladder_proper {P Q PQ R : Point} (hP : P.Proper) (hQ : Q.Proper) (hPQ : PQ.Proper)
    (hR : R.Proper) : ∀ (a b n : Nat), (Point.ladder P Q PQ R a b n).Proper
  | _, _, 0 => hR
  | a, b, n + 1 => step_proper hP hQ hPQ (ladder_proper hP hQ hPQ hR (a >>> 1) (b >>> 1) n) a b

theorem mul2_proper {P Q PQ : Point} (hP : P.Proper) (hQ : Q.Proper) (hPQ : PQ.Proper)
    (a b n : Nat) : (Point.mul2 P Q PQ a b n).Proper :=
  ladder_proper hP hQ hPQ point_zero_proper a b n

theorem B_proper : B.Proper :=
  ⟨B_onCurve, by unfold B; dsimp only; rw [val_one]; exact fin_one_ne_zero⟩

theorem decodePoint_proper {b : ByteArray} {off : Nat} {P : Point} (h : decodePoint b off = some P) :
    P.Proper := by
  refine ⟨decodePoint_onCurve h, ?_⟩
  unfold decodePoint at h
  dsimp only at h
  split at h
  · cases h
  · split at h
    · cases h
    · unfold signed at h
      split at h
      · cases h
      · rw [← Option.some.inj h]; dsimp only; rw [val_one]; exact fin_one_ne_zero

/-! ## The tooth -/

/-- `OnCurve` alone admits the degenerate `(0, 0, 0, 0)`, whose sum with itself has `Z = 0`: the laws
of `Codec.Proofs.Curve` hold for it vacuously, so `Proper`'s `Z ≠ 0` is load-bearing. -/
theorem onCurve_admits_degenerate {R : Type} [Lean.Grind.CommRing R] (d : R) :
    OnCurveR d 0 0 0 0 ∧
      ((0 + 0) * (0 : R) - 0 * (2 * d) * 0) * ((0 + 0) * (0 : R) + 0 * (2 * d) * 0) = 0 :=
  ⟨⟨by grind, by grind⟩, by grind⟩

end Nanodregg.Codec.Ed25519
