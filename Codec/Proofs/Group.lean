import Codec.Proofs.Complete

/-!
# The group: `Point.add` is a commutative group law on proper points (CODEC-23 part 3)

`Codec.Proofs.Complete` proved that every point `verify` computes is PROPER (on the curve, `Z ≠ 0`) and
that `add`/`double` are the Edwards law cross-multiplied. This module turns that into the group the RFC
speaks of, up to projective equality.

* `Point.Affine P x y`: `P` is proper and names the affine point `(x, y)` (`X = x Z`, `Y = y Z`). Every
  proper point names exactly one (`affine_exists`, `affine_unique`), on `−x² + y² = 1 + d x² y²`
  (`affine_curve`); `add`/`double` of named points name the affine Edwards sum (`add_affine`,
  `double_affine`), whose denominators never vanish (`affine_dens`).
* `Point.Same P Q`: both proper and `P.eq Q` — the deployed projective equality — holds. It is an
  equivalence (`same_refl`, `same_symm`, `same_trans`), `add` respects it (`same_add_left`,
  `same_add_right`), and on it `add` is commutative (`same_add_comm`), ASSOCIATIVE (`same_add_assoc`), has
  `Point.zero` as identity (`same_add_zero`) and `neg` as inverse (`same_neg_add`), and `double` is
  `add` of a point to itself (`same_double`).
* Associativity is one ring identity with the denominators cleared (`assoc_polyR`, 48 monomials of degree
  18 after expansion), closed by `grind` from the three curve equations alone; `assoc_affR` turns it into
  equality of the affine coordinates. Tooth: `assoc_needs_curve` — off the curve the identity is false.
-/

namespace Nanodregg.Codec.Ed25519

open Fin.NatCast

/-! ## Over any commutative ring with inverses -/

section Ring
variable {R : Type} [Lean.Grind.CommRing R]

theorem cancelR (inv : ∀ a : R, a ≠ 0 → ∃ b, a * b = 1) {a x y : R} (ha : a ≠ 0)
    (h : x * a = y * a) : x = y := by
  obtain ⟨b, hb⟩ := inv a ha
  have e : x * a * b = y * a * b := by rw [h]
  grind

/-- Associativity of the affine Edwards law with every denominator cleared: `(P₁ + P₂) + P₃` has `x`
numerator/denominator `lxn/lxd` (with `P₁ + P₂ = (nx/a, ny/b)`), `P₁ + (P₂ + P₃)` has `rxn/rxd`, and the
cross products agree on the curve. Likewise `y`. -/
theorem assoc_polyR (d x1 y1 x2 y2 x3 y3 a b nx ny a' b' nx' ny' : R)
    (ha : a = 1 + d * x1 * x2 * y1 * y2) (hb : b = 1 - d * x1 * x2 * y1 * y2)
    (hnx : nx = x1 * y2 + y1 * x2) (hny : ny = y1 * y2 + x1 * x2)
    (ha' : a' = 1 + d * x2 * x3 * y2 * y3) (hb' : b' = 1 - d * x2 * x3 * y2 * y3)
    (hnx' : nx' = x2 * y3 + y2 * x3) (hny' : ny' = y2 * y3 + x2 * x3)
    (c1 : y1 * y1 - x1 * x1 = 1 + d * (x1 * x1) * (y1 * y1))
    (c2 : y2 * y2 - x2 * x2 = 1 + d * (x2 * x2) * (y2 * y2))
    (c3 : y3 * y3 - x3 * x3 = 1 + d * (x3 * x3) * (y3 * y3)) :
    (nx * b * y3 + ny * a * x3) * (a' * b' + d * x1 * y1 * nx' * ny') =
        (x1 * ny' * a' + y1 * nx' * b') * (a * b + d * nx * ny * x3 * y3) ∧
      (ny * a * y3 + nx * b * x3) * (a' * b' - d * x1 * y1 * nx' * ny') =
        (y1 * ny' * a' + x1 * nx' * b') * (a * b - d * nx * ny * x3 * y3) := by
  subst ha hb hnx hny ha' hb' hnx' hny'
  constructor <;> grind

theorem outer_xR {d a b nx ny x12 y12 x3 y3 xL : R} (hx : a * x12 = nx) (hy : b * y12 = ny)
    (h : (1 + d * x12 * x3 * y12 * y3) * xL = x12 * y3 + y12 * x3) :
    xL * (a * b + d * nx * ny * x3 * y3) = nx * b * y3 + ny * a * x3 := by
  subst hx hy; grind

theorem outer_yR {d a b nx ny x12 y12 x3 y3 yL : R} (hx : a * x12 = nx) (hy : b * y12 = ny)
    (h : (1 - d * x12 * x3 * y12 * y3) * yL = y12 * y3 + x12 * x3) :
    yL * (a * b - d * nx * ny * x3 * y3) = ny * a * y3 + nx * b * x3 := by
  subst hx hy; grind

theorem inner_xR {d a b nx ny x1 y1 x23 y23 xR : R} (hx : a * x23 = nx) (hy : b * y23 = ny)
    (h : (1 + d * x1 * x23 * y1 * y23) * xR = x1 * y23 + y1 * x23) :
    xR * (a * b + d * x1 * y1 * nx * ny) = x1 * ny * a + y1 * nx * b := by
  subst hx hy; grind

theorem inner_yR {d a b nx ny x1 y1 x23 y23 yR : R} (hx : a * x23 = nx) (hy : b * y23 = ny)
    (h : (1 - d * x1 * x23 * y1 * y23) * yR = y1 * y23 + x1 * x23) :
    yR * (a * b - d * x1 * y1 * nx * ny) = y1 * ny * a + x1 * nx * b := by
  subst hx hy; grind

theorem outer_denR (inv : ∀ a : R, a ≠ 0 → ∃ b, a * b = 1) {d a b nx ny x12 y12 x3 y3 : R}
    (hx : a * x12 = nx) (hy : b * y12 = ny) (na : a ≠ 0) (nb : b ≠ 0)
    (np : 1 + d * x12 * x3 * y12 * y3 ≠ 0) (nm : 1 - d * x12 * x3 * y12 * y3 ≠ 0) :
    a * b + d * nx * ny * x3 * y3 ≠ 0 ∧ a * b - d * nx * ny * x3 * y3 ≠ 0 := by
  subst hx hy
  have ep : a * b + d * (a * x12) * (b * y12) * x3 * y3 = a * b * (1 + d * x12 * x3 * y12 * y3) := by grind
  have em : a * b - d * (a * x12) * (b * y12) * x3 * y3 = a * b * (1 - d * x12 * x3 * y12 * y3) := by grind
  rw [ep, em]
  exact ⟨mul_ne_zeroR inv (mul_ne_zeroR inv na nb) np, mul_ne_zeroR inv (mul_ne_zeroR inv na nb) nm⟩

theorem inner_denR (inv : ∀ a : R, a ≠ 0 → ∃ b, a * b = 1) {d a b nx ny x1 y1 x23 y23 : R}
    (hx : a * x23 = nx) (hy : b * y23 = ny) (na : a ≠ 0) (nb : b ≠ 0)
    (np : 1 + d * x1 * x23 * y1 * y23 ≠ 0) (nm : 1 - d * x1 * x23 * y1 * y23 ≠ 0) :
    a * b + d * x1 * y1 * nx * ny ≠ 0 ∧ a * b - d * x1 * y1 * nx * ny ≠ 0 := by
  subst hx hy
  have ep : a * b + d * x1 * y1 * (a * x23) * (b * y23) = a * b * (1 + d * x1 * x23 * y1 * y23) := by grind
  have em : a * b - d * x1 * y1 * (a * x23) * (b * y23) = a * b * (1 - d * x1 * x23 * y1 * y23) := by grind
  rw [ep, em]
  exact ⟨mul_ne_zeroR inv (mul_ne_zeroR inv na nb) np, mul_ne_zeroR inv (mul_ne_zeroR inv na nb) nm⟩

theorem cross_cancelR (inv : ∀ a : R, a ≠ 0 → ∃ b, a * b = 1) {xL xR ln ld rn rd : R}
    (h1 : xL * ld = ln) (h2 : xR * rd = rn) (h : ln * rd = rn * ld) (n1 : ld ≠ 0) (n2 : rd ≠ 0) :
    xL = xR := by
  apply cancelR inv (mul_ne_zeroR inv n1 n2)
  rw [← h1, ← h2] at h
  grind

/-- Affine associativity: on the curve, wherever the four sums' denominators are units,
`(P₁ + P₂) + P₃ = P₁ + (P₂ + P₃)`. -/
theorem assoc_affR (inv : ∀ a : R, a ≠ 0 → ∃ b, a * b = 1)
    {d x1 y1 x2 y2 x3 y3 x12 y12 x23 y23 xL yL xR yR : R}
    (c1 : y1 * y1 - x1 * x1 = 1 + d * (x1 * x1) * (y1 * y1))
    (c2 : y2 * y2 - x2 * x2 = 1 + d * (x2 * x2) * (y2 * y2))
    (c3 : y3 * y3 - x3 * x3 = 1 + d * (x3 * x3) * (y3 * y3))
    (s12x : (1 + d * x1 * x2 * y1 * y2) * x12 = x1 * y2 + y1 * x2)
    (s12y : (1 - d * x1 * x2 * y1 * y2) * y12 = y1 * y2 + x1 * x2)
    (s23x : (1 + d * x2 * x3 * y2 * y3) * x23 = x2 * y3 + y2 * x3)
    (s23y : (1 - d * x2 * x3 * y2 * y3) * y23 = y2 * y3 + x2 * x3)
    (sLx : (1 + d * x12 * x3 * y12 * y3) * xL = x12 * y3 + y12 * x3)
    (sLy : (1 - d * x12 * x3 * y12 * y3) * yL = y12 * y3 + x12 * x3)
    (sRx : (1 + d * x1 * x23 * y1 * y23) * xR = x1 * y23 + y1 * x23)
    (sRy : (1 - d * x1 * x23 * y1 * y23) * yR = y1 * y23 + x1 * x23)
    (n12x : 1 + d * x1 * x2 * y1 * y2 ≠ 0) (n12y : 1 - d * x1 * x2 * y1 * y2 ≠ 0)
    (n23x : 1 + d * x2 * x3 * y2 * y3 ≠ 0) (n23y : 1 - d * x2 * x3 * y2 * y3 ≠ 0)
    (nLx : 1 + d * x12 * x3 * y12 * y3 ≠ 0) (nLy : 1 - d * x12 * x3 * y12 * y3 ≠ 0)
    (nRx : 1 + d * x1 * x23 * y1 * y23 ≠ 0) (nRy : 1 - d * x1 * x23 * y1 * y23 ≠ 0) :
    xL = xR ∧ yL = yR := by
  obtain ⟨px, py⟩ := assoc_polyR d x1 y1 x2 y2 x3 y3 _ _ _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl rfl rfl c1 c2 c3
  obtain ⟨dLx, dLy⟩ := outer_denR inv s12x s12y n12x n12y nLx nLy
  obtain ⟨dRx, dRy⟩ := inner_denR inv s23x s23y n23x n23y nRx nRy
  exact ⟨cross_cancelR inv (outer_xR s12x s12y sLx) (inner_xR s23x s23y sRx) px dLx dRx,
    cross_cancelR inv (outer_yR s12x s12y sLy) (inner_yR s23x s23y sRy) py dLy dRy⟩

/-- The six ring identities `add_affineR` chains through (stated apart, so `grind` sees no hypothesis). -/
theorem add_affine_idsR (d Z1 Z2 X3 Y3 Z3 x1 y1 x2 y2 x3 y3 : R) :
    X3 * (1 + d * x1 * x2 * y1 * y2) * (Z1 * Z1 * Z2 * Z2) =
      X3 * (Z1 * Z1 * Z2 * Z2 + d * (x1 * Z1) * (x2 * Z2) * (y1 * Z1) * (y2 * Z2)) ∧
    Z3 * ((x1 * Z1 * (y2 * Z2) + x2 * Z2 * (y1 * Z1)) * Z1 * Z2) =
      Z3 * (Z1 * Z1 * Z2 * Z2) * (x1 * y2 + y1 * x2) ∧
    x3 * Z3 * (1 + d * x1 * x2 * y1 * y2) * (Z1 * Z1 * Z2 * Z2) =
      Z3 * (Z1 * Z1 * Z2 * Z2) * ((1 + d * x1 * x2 * y1 * y2) * x3) ∧
    Y3 * (1 - d * x1 * x2 * y1 * y2) * (Z1 * Z1 * Z2 * Z2) =
      Y3 * (Z1 * Z1 * Z2 * Z2 - d * (x1 * Z1) * (x2 * Z2) * (y1 * Z1) * (y2 * Z2)) ∧
    Z3 * ((y1 * Z1 * (y2 * Z2) + x1 * Z1 * (x2 * Z2)) * Z1 * Z2) =
      Z3 * (Z1 * Z1 * Z2 * Z2) * (y1 * y2 + x1 * x2) ∧
    y3 * Z3 * (1 - d * x1 * x2 * y1 * y2) * (Z1 * Z1 * Z2 * Z2) =
      Z3 * (Z1 * Z1 * Z2 * Z2) * ((1 - d * x1 * x2 * y1 * y2) * y3) :=
  ⟨by grind, by grind, by grind, by grind, by grind, by grind⟩

/-- The projective law, read in affine coordinates: if `Pᵢ = (xᵢ Zᵢ, yᵢ Zᵢ, Zᵢ)` and `P₃`'s coordinates
satisfy the cross-multiplied law, then `P₃` names the affine sum `(x₃, y₃)`. -/
theorem add_affineR (inv : ∀ a : R, a ≠ 0 → ∃ b, a * b = 1)
    {d X1 Y1 Z1 X2 Y2 Z2 X3 Y3 Z3 x1 y1 x2 y2 x3 y3 : R}
    (hx1 : X1 = x1 * Z1) (hy1 : Y1 = y1 * Z1) (hx2 : X2 = x2 * Z2) (hy2 : Y2 = y2 * Z2)
    (z1 : Z1 ≠ 0) (z2 : Z2 ≠ 0)
    (lx : X3 * (Z1 * Z1 * Z2 * Z2 + d * X1 * X2 * Y1 * Y2) = Z3 * ((X1 * Y2 + X2 * Y1) * Z1 * Z2))
    (ly : Y3 * (Z1 * Z1 * Z2 * Z2 - d * X1 * X2 * Y1 * Y2) = Z3 * ((Y1 * Y2 + X1 * X2) * Z1 * Z2))
    (sx : (1 + d * x1 * x2 * y1 * y2) * x3 = x1 * y2 + y1 * x2)
    (sy : (1 - d * x1 * x2 * y1 * y2) * y3 = y1 * y2 + x1 * x2)
    (nx : 1 + d * x1 * x2 * y1 * y2 ≠ 0) (ny : 1 - d * x1 * x2 * y1 * y2 ≠ 0) :
    X3 = x3 * Z3 ∧ Y3 = y3 * Z3 := by
  subst hx1 hy1 hx2 hy2
  have zz := mul_ne_zeroR inv (mul_ne_zeroR inv (mul_ne_zeroR inv z1 z1) z2) z2
  obtain ⟨ax, bx, cx, ay, by', cy⟩ := add_affine_idsR d Z1 Z2 X3 Y3 Z3 x1 y1 x2 y2 x3 y3
  exact ⟨cancelR inv nx (cancelR inv zz (ax.trans (lx.trans (bx.trans
      ((congrArg (fun t => Z3 * (Z1 * Z1 * Z2 * Z2) * t) sx.symm).trans cx.symm))))),
    cancelR inv ny (cancelR inv zz (ay.trans (ly.trans (by'.trans
      ((congrArg (fun t => Z3 * (Z1 * Z1 * Z2 * Z2) * t) sy.symm).trans cy.symm)))))⟩

/-- A proper point's affine coordinates are on the affine curve. -/
theorem affine_curveR (inv : ∀ a : R, a ≠ 0 → ∃ b, a * b = 1) {d X Y Z T x y : R}
    (h : OnCurveR d X Y Z T) (hx : X = x * Z) (hy : Y = y * Z) (z : Z ≠ 0) :
    y * y - x * x = 1 + d * (x * x) * (y * y) := by
  obtain ⟨e, c⟩ := h
  subst hx hy
  have hT : T = x * y * Z := cancelR inv z (by grind)
  subst hT
  exact cancelR inv (mul_ne_zeroR inv z z) (by grind)

theorem dens_neR {e : R} (h : e * e ≠ 1) : 1 + e ≠ 0 ∧ 1 - e ≠ 0 :=
  ⟨fun h0 => h (by grind), fun h0 => h (by grind)⟩

theorem inv_coordR {X Z u : R} (hu : Z * u = 1) : X = X * u * Z := by grind

theorem cross_coordR {XP XQ ZP ZQ x : R} (h1 : XP = x * ZP) (h2 : XQ = x * ZQ) : XP * ZQ = XQ * ZP := by
  subst h1 h2; grind

theorem coord_of_crossR (inv : ∀ a : R, a ≠ 0 → ∃ b, a * b = 1) {XP XQ ZP ZQ x : R} (zP : ZP ≠ 0)
    (h1 : XP = x * ZP) (h : XP * ZQ = XQ * ZP) : XQ = x * ZQ := by
  subst h1
  exact cancelR inv zP (by grind)

theorem solveR {a n u : R} (h : a * u = 1) : a * (n * u) = n := by grind

theorem neg_coordR {X x Z : R} (h : X = x * Z) : 0 - X = (0 - x) * Z := by subst h; grind

theorem sum_commR {d x1 y1 x2 y2 x3 y3 : R} (sx : (1 + d * x1 * x2 * y1 * y2) * x3 = x1 * y2 + y1 * x2)
    (sy : (1 - d * x1 * x2 * y1 * y2) * y3 = y1 * y2 + x1 * x2) :
    (1 + d * x2 * x1 * y2 * y1) * x3 = x2 * y1 + y2 * x1 ∧ (1 - d * x2 * x1 * y2 * y1) * y3 = y2 * y1 + x2 * x1 :=
  ⟨by grind, by grind⟩

theorem sum_zeroR (d x y : R) :
    (1 + d * x * 0 * y * 1) * x = x * 1 + y * 0 ∧ (1 - d * x * 0 * y * 1) * y = y * 1 + x * 0 :=
  ⟨by grind, by grind⟩

theorem sum_negR {d x y : R} (c : y * y - x * x = 1 + d * (x * x) * (y * y)) :
    (1 + d * (0 - x) * x * y * y) * 0 = (0 - x) * y + y * x ∧
      (1 - d * (0 - x) * x * y * y) * 1 = y * y + (0 - x) * x :=
  ⟨by grind, by grind⟩

end Ring

/-! ## Affine names of proper points -/

private theorem val_cast (a : Nat) : ((a : Fin p) : Nat) = a % p := rfl

theorem fe_cast_eq {f g : Fe} : f.toNat = g.toNat ↔ (f.toNat : Fin p) = (g.toNat : Fin p) := by
  constructor
  · intro h; rw [h]
  · intro h
    have e := congrArg Fin.val h
    rwa [val_cast, val_cast, Nat.mod_eq_of_lt (toNat_lt f), Nat.mod_eq_of_lt (toNat_lt g)] at e

/-- The deployed projective equality, as ring equations. -/
theorem point_eq_iff {P Q : Point} (hP : P.Carried) (hQ : Q.Carried) :
    P.eq Q = true ↔ (P.X.toNat : Fin p) * (Q.Z.toNat : Fin p) = (Q.X.toNat : Fin p) * (P.Z.toNat : Fin p) ∧
      (P.Y.toNat : Fin p) * (Q.Z.toNat : Fin p) = (Q.Y.toNat : Fin p) * (P.Z.toNat : Fin p) := by
  unfold Point.eq
  rw [Bool.and_eq_true, eq_iff, eq_iff, fe_cast_eq, fe_cast_eq, val_mul hP.X hQ.Z, val_mul hQ.X hP.Z,
    val_mul hP.Y hQ.Z, val_mul hQ.Y hP.Z]

/-- `P` is proper and names the affine point `(x, y)`. -/
structure Point.Affine (P : Point) (x y : Fin p) : Prop where
  proper : P.Proper
  hx : (P.X.toNat : Fin p) = x * (P.Z.toNat : Fin p)
  hy : (P.Y.toNat : Fin p) = y * (P.Z.toNat : Fin p)

theorem affine_exists {P : Point} (h : P.Proper) : ∃ x y, P.Affine x y := by
  obtain ⟨u, hu⟩ := fin_inv _ h.z
  exact ⟨_, _, h, inv_coordR hu, inv_coordR hu⟩

theorem affine_unique {P : Point} {x y x' y' : Fin p} (h : P.Affine x y) (h' : P.Affine x' y') :
    x = x' ∧ y = y' :=
  ⟨cancelR fin_inv h.proper.z (h.hx.symm.trans h'.hx), cancelR fin_inv h.proper.z (h.hy.symm.trans h'.hy)⟩

theorem affine_curve {P : Point} {x y : Fin p} (h : P.Affine x y) :
    y * y - x * x = 1 + (d.toNat : Fin p) * (x * x) * (y * y) :=
  affine_curveR fin_inv h.proper.on.on h.hx h.hy h.proper.z

/-- The addition denominators of two named points are units (completeness). -/
theorem affine_dens {P Q : Point} {x1 y1 x2 y2 : Fin p} (hP : P.Affine x1 y1) (hQ : Q.Affine x2 y2) :
    1 + (d.toNat : Fin p) * x1 * x2 * y1 * y2 ≠ 0 ∧ 1 - (d.toNat : Fin p) * x1 * x2 * y1 * y2 ≠ 0 :=
  dens_neR (complete_affineR fin_inv d_nonsquare sqrtM1_sq fin_two_ne_zero fin_one_ne_zero
    (affine_curve hP) (affine_curve hQ))

/-- `P.add Q` names the affine Edwards sum of what `P` and `Q` name. -/
theorem add_affine {P Q : Point} {x1 y1 x2 y2 x3 y3 : Fin p} (hP : P.Affine x1 y1) (hQ : Q.Affine x2 y2)
    (sx : (1 + (d.toNat : Fin p) * x1 * x2 * y1 * y2) * x3 = x1 * y2 + y1 * x2)
    (sy : (1 - (d.toNat : Fin p) * x1 * x2 * y1 * y2) * y3 = y1 * y2 + x1 * x2) :
    (P.add Q).Affine x3 y3 := by
  obtain ⟨nx, ny⟩ := affine_dens hP hQ
  obtain ⟨lx, ly⟩ := point_add_law hP.proper.on hQ.proper.on
  obtain ⟨ex, ey⟩ := add_affineR fin_inv hP.hx hP.hy hQ.hx hQ.hy hP.proper.z hQ.proper.z lx ly sx sy nx ny
  exact ⟨point_add_proper hP.proper hQ.proper, ex, ey⟩

theorem add_affine_exists {P Q : Point} {x1 y1 x2 y2 : Fin p} (hP : P.Affine x1 y1) (hQ : Q.Affine x2 y2) :
    ∃ x3 y3, (P.add Q).Affine x3 y3 ∧
      (1 + (d.toNat : Fin p) * x1 * x2 * y1 * y2) * x3 = x1 * y2 + y1 * x2 ∧
      (1 - (d.toNat : Fin p) * x1 * x2 * y1 * y2) * y3 = y1 * y2 + x1 * x2 := by
  obtain ⟨nx, ny⟩ := affine_dens hP hQ
  obtain ⟨u, hu⟩ := fin_inv _ nx
  obtain ⟨v, hv⟩ := fin_inv _ ny
  exact ⟨_, _, add_affine hP hQ (solveR hu) (solveR hv), solveR hu, solveR hv⟩

/-- `P.double` names the affine Edwards sum of `P`'s name with itself. -/
theorem double_affine {P : Point} {x y x3 y3 : Fin p} (hP : P.Affine x y)
    (sx : (1 + (d.toNat : Fin p) * x * x * y * y) * x3 = x * y + y * x)
    (sy : (1 - (d.toNat : Fin p) * x * x * y * y) * y3 = y * y + x * x) :
    P.double.Affine x3 y3 := by
  obtain ⟨nx, ny⟩ := affine_dens hP hP
  obtain ⟨lx, ly⟩ := point_double_law hP.proper.on
  obtain ⟨ex, ey⟩ := add_affineR fin_inv hP.hx hP.hy hP.hx hP.hy hP.proper.z hP.proper.z lx ly sx sy nx ny
  exact ⟨point_double_proper hP.proper, ex, ey⟩

theorem zero_affine : Point.zero.Affine 0 1 := by
  refine ⟨point_zero_proper, ?_, ?_⟩
  · unfold Point.zero; dsimp only; rw [val_zero, val_one]; exact (sum_zeroR 0 0 0).1.symm.trans (by grind)
  · unfold Point.zero; dsimp only; rw [val_one]; grind

theorem neg_affine {P : Point} {x y : Fin p} (h : P.Affine x y) : P.neg.Affine (0 - x) y := by
  refine ⟨point_neg_proper h.proper, ?_, ?_⟩
  · unfold Point.neg; dsimp only
    rw [val_sub zero_carried h.proper.on.carried.X, val_zero]
    exact neg_coordR h.hx
  · unfold Point.neg; dsimp only; exact h.hy

/-! ## Projective equality of proper points -/

/-- `P` and `Q` are proper and projectively equal (`Point.eq`, the deployed check). -/
structure Point.Same (P Q : Point) : Prop where
  left : P.Proper
  right : Q.Proper
  eq : P.eq Q = true

theorem affine_same {P Q : Point} {x y : Fin p} (hP : P.Affine x y) (hQ : Q.Affine x y) : Point.Same P Q :=
  ⟨hP.proper, hQ.proper, (point_eq_iff hP.proper.on.carried hQ.proper.on.carried).2
    ⟨cross_coordR hP.hx hQ.hx, cross_coordR hP.hy hQ.hy⟩⟩

theorem same_affine {P Q : Point} {x y : Fin p} (h : Point.Same P Q) (hP : P.Affine x y) : Q.Affine x y := by
  obtain ⟨ex, ey⟩ := (point_eq_iff h.left.on.carried h.right.on.carried).1 h.eq
  exact ⟨h.right, coord_of_crossR fin_inv h.left.z hP.hx ex, coord_of_crossR fin_inv h.left.z hP.hy ey⟩

theorem same_refl {P : Point} (h : P.Proper) : Point.Same P P := by
  obtain ⟨x, y, a⟩ := affine_exists h
  exact affine_same a a

theorem same_symm {P Q : Point} (h : Point.Same P Q) : Point.Same Q P := by
  obtain ⟨x, y, a⟩ := affine_exists h.left
  exact affine_same (same_affine h a) a

theorem same_trans {P Q S : Point} (h1 : Point.Same P Q) (h2 : Point.Same Q S) : Point.Same P S := by
  obtain ⟨x, y, a⟩ := affine_exists h1.left
  exact affine_same a (same_affine h2 (same_affine h1 a))

/-! ## The group laws -/

theorem same_add_left {P P' Q : Point} (h : Point.Same P P') (hQ : Q.Proper) :
    Point.Same (P.add Q) (P'.add Q) := by
  obtain ⟨x1, y1, a1⟩ := affine_exists h.left
  obtain ⟨x2, y2, a2⟩ := affine_exists hQ
  obtain ⟨x3, y3, a3, sx, sy⟩ := add_affine_exists a1 a2
  exact affine_same a3 (add_affine (same_affine h a1) a2 sx sy)

theorem same_add_right {P Q Q' : Point} (hP : P.Proper) (h : Point.Same Q Q') :
    Point.Same (P.add Q) (P.add Q') := by
  obtain ⟨x1, y1, a1⟩ := affine_exists hP
  obtain ⟨x2, y2, a2⟩ := affine_exists h.left
  obtain ⟨x3, y3, a3, sx, sy⟩ := add_affine_exists a1 a2
  exact affine_same a3 (add_affine a1 (same_affine h a2) sx sy)

theorem same_add_comm {P Q : Point} (hP : P.Proper) (hQ : Q.Proper) : Point.Same (P.add Q) (Q.add P) := by
  obtain ⟨x1, y1, a1⟩ := affine_exists hP
  obtain ⟨x2, y2, a2⟩ := affine_exists hQ
  obtain ⟨x3, y3, a3, sx, sy⟩ := add_affine_exists a1 a2
  obtain ⟨sx', sy'⟩ := sum_commR sx sy
  exact affine_same a3 (add_affine a2 a1 sx' sy')

theorem same_add_zero {P : Point} (hP : P.Proper) : Point.Same (P.add Point.zero) P := by
  obtain ⟨x, y, a⟩ := affine_exists hP
  obtain ⟨sx, sy⟩ := sum_zeroR (d.toNat : Fin p) x y
  exact affine_same (add_affine a zero_affine sx sy) a

theorem same_neg_add {P : Point} (hP : P.Proper) : Point.Same (P.neg.add P) Point.zero := by
  obtain ⟨x, y, a⟩ := affine_exists hP
  obtain ⟨sx, sy⟩ := sum_negR (affine_curve a)
  exact affine_same (add_affine (neg_affine a) a sx sy) zero_affine

theorem same_double {P : Point} (hP : P.Proper) : Point.Same P.double (P.add P) := by
  obtain ⟨x, y, a⟩ := affine_exists hP
  obtain ⟨x3, y3, a3, sx, sy⟩ := add_affine_exists a a
  exact affine_same (double_affine a sx sy) a3

/-- Associativity of the deployed addition, up to projective equality. -/
theorem same_add_assoc {P Q S : Point} (hP : P.Proper) (hQ : Q.Proper) (hS : S.Proper) :
    Point.Same ((P.add Q).add S) (P.add (Q.add S)) := by
  obtain ⟨x1, y1, a1⟩ := affine_exists hP
  obtain ⟨x2, y2, a2⟩ := affine_exists hQ
  obtain ⟨x3, y3, a3⟩ := affine_exists hS
  obtain ⟨x12, y12, a12, s12x, s12y⟩ := add_affine_exists a1 a2
  obtain ⟨x23, y23, a23, s23x, s23y⟩ := add_affine_exists a2 a3
  obtain ⟨xL, yL, aL, sLx, sLy⟩ := add_affine_exists a12 a3
  obtain ⟨xR, yR, aR, sRx, sRy⟩ := add_affine_exists a1 a23
  obtain ⟨n12x, n12y⟩ := affine_dens a1 a2
  obtain ⟨n23x, n23y⟩ := affine_dens a2 a3
  obtain ⟨nLx, nLy⟩ := affine_dens a12 a3
  obtain ⟨nRx, nRy⟩ := affine_dens a1 a23
  obtain ⟨ex, ey⟩ := assoc_affR fin_inv (affine_curve a1) (affine_curve a2) (affine_curve a3)
    s12x s12y s23x s23y sLx sLy sRx sRy n12x n12y n23x n23y nLx nLy nRx nRy
  rw [ex, ey] at aL
  exact affine_same aL aR

/-! ## The tooth -/

/-- The curve equations are load-bearing in `assoc_polyR`: at `(1, 2), (3, 4), (5, 6)` in `ℤ/p` (off the
curve) the cleared associativity identity for `x` is false. -/
theorem assoc_needs_curve :
    let d : Fin p := Fin.ofNat p 37095705934669439343138083508754565189542113879843219016388785533085940283555
    let x1 : Fin p := 1; let y1 : Fin p := 2; let x2 : Fin p := 3; let y2 : Fin p := 4
    let x3 : Fin p := 5; let y3 : Fin p := 6
    let a := 1 + d * x1 * x2 * y1 * y2; let b := 1 - d * x1 * x2 * y1 * y2
    let nx := x1 * y2 + y1 * x2; let ny := y1 * y2 + x1 * x2
    let a' := 1 + d * x2 * x3 * y2 * y3; let b' := 1 - d * x2 * x3 * y2 * y3
    let nx' := x2 * y3 + y2 * x3; let ny' := y2 * y3 + x2 * x3
    (nx * b * y3 + ny * a * x3) * (a' * b' + d * x1 * y1 * nx' * ny') ≠
      (x1 * ny' * a' + y1 * nx' * b') * (a * b + d * nx * ny * x3 * y3) := by
  decide +kernel

end Nanodregg.Codec.Ed25519
