import Codec.Proofs.Field

/-!
# The curve: every point the verifier computes lies on edwards25519 (CODEC-23)

`Codec.Proofs.Field` proved the FIELD: `Fe.mul`/`add`/`sub` compute in `ℤ/p` for carried inputs. This
module proves the CURVE formulas over it, in `Fin p` (the value `(f.toNat : Fin p)`, `f.toNat` cast into
`ℤ/p`, so `val_mul` / `val_add` / `val_sub` turn every carried `Fe` expression into ring arithmetic).

* `Point.OnCurve P`: `P` is a point of the extended twisted Edwards curve `−X² + Y² = Z² + d T²` with
  `X Y = Z T` (RFC 8032 §5.1.4; `a = −1`). In these coordinates the curve is closed under the RFC's
  formulas with no division, so the statements need no field and no `Z ≠ 0`.
* `point_add_onCurve`, `point_double_onCurve`, `point_neg_onCurve`, `point_zero_onCurve`,
  `B_onCurve`, `decodePoint_onCurve`, `mul2_onCurve`: every point `verify` computes is on the curve.
* `point_add_law_x` / `_y`, `point_double_law_x` / `_y`: the result IS the Edwards sum, cross-multiplied:
  `X₃ (Z₁²Z₂² + d X₁X₂Y₁Y₂) = Z₃ (X₁Y₂ + X₂Y₁) Z₁Z₂` and `Y₃ (Z₁²Z₂² − d X₁X₂Y₁Y₂) = Z₃ (Y₁Y₂ + X₁X₂) Z₁Z₂`,
  i.e. `x₃ = (x₁y₂ + x₂y₁)/(1 + d x₁x₂y₁y₂)`, `y₃ = (y₁y₂ + x₁x₂)/(1 − d x₁x₂y₁y₂)` wherever the
  denominators are units.
The ring identities are proved once over any commutative ring (`grind`), then instantiated at `Fin p`.
Tooth: `onCurve_needs_ext` — a curve point with a wrong `T` is not `OnCurve`, and the addition law
fails for it (`decide +kernel` on the deployed arithmetic), so `ext` carries content.
-/

namespace Nanodregg.Codec.Ed25519

open Fin.NatCast

@[instance] theorem p_neZero : NeZero p := ⟨by decide⟩

/-! ## The value map is a ring map on carried elements -/

private theorem val_cast (a : Nat) : ((a : Fin p) : Nat) = a % p := rfl

theorem toNat_lt (f : Fe) : f.toNat < p := Nat.mod_lt _ (by decide)

theorem val_mul {f g : Fe} (hf : f.Carried) (hg : g.Carried) : ((f.mul g).toNat : Fin p) = (f.toNat : Fin p) * (g.toNat : Fin p) := by
  apply Fin.ext
  simp only [val_cast, Fin.val_mul, mul_toNat hf hg, Nat.mod_mod, Nat.mod_eq_of_lt (toNat_lt f),
    Nat.mod_eq_of_lt (toNat_lt g)]

theorem val_add {f g : Fe} (hf : f.Carried) (hg : g.Carried) : ((f.add g).toNat : Fin p) = (f.toNat : Fin p) + (g.toNat : Fin p) := by
  apply Fin.ext
  simp only [val_cast, Fin.val_add, add_toNat hf hg, Nat.mod_mod, Nat.mod_eq_of_lt (toNat_lt f),
    Nat.mod_eq_of_lt (toNat_lt g)]

theorem val_sub {f g : Fe} (hf : f.Carried) (hg : g.Carried) : ((f.sub g).toNat : Fin p) = (f.toNat : Fin p) - (g.toNat : Fin p) := by
  apply Fin.ext
  have hg' := toNat_lt g
  simp only [val_cast, Fin.sub_def, sub_toNat hf hg, Nat.mod_mod, Nat.mod_eq_of_lt (toNat_lt f),
    Nat.mod_eq_of_lt hg']
  rw [Nat.add_sub_assoc (Nat.le_of_lt hg'), Nat.add_comm]

theorem val_sq {f : Fe} (hf : f.Carried) : (f.sq.toNat : Fin p) = (f.toNat : Fin p) * (f.toNat : Fin p) := val_mul hf hf

theorem val_d2 : (d2.toNat : Fin p) = 2 * (d.toNat : Fin p) := by
  unfold d2 d
  rw [(ofNat_spec (by decide +kernel)).2, (ofNat_spec (by decide +kernel)).2]
  decide +kernel

/-! ## The ring identities, over any commutative ring -/

section Ring
variable {R : Type} [Lean.Grind.CommRing R]

/-- Extended coordinates on the curve, as ring equations. -/
structure OnCurveR (d X Y Z T : R) : Prop where
  ext : X * Y = Z * T
  curve : Y * Y - X * X = Z * Z + d * T * T

/-- The RFC's addition, on ring values. -/
theorem add_onCurveR {d X1 Y1 Z1 T1 X2 Y2 Z2 T2 : R} (h1 : OnCurveR d X1 Y1 Z1 T1)
    (h2 : OnCurveR d X2 Y2 Z2 T2) :
    OnCurveR d (((Y1 + X1) * (Y2 + X2) - (Y1 - X1) * (Y2 - X2)) * ((Z1 + Z1) * Z2 - T1 * (2 * d) * T2))
      (((Z1 + Z1) * Z2 + T1 * (2 * d) * T2) * ((Y1 + X1) * (Y2 + X2) + (Y1 - X1) * (Y2 - X2)))
      (((Z1 + Z1) * Z2 - T1 * (2 * d) * T2) * ((Z1 + Z1) * Z2 + T1 * (2 * d) * T2))
      (((Y1 + X1) * (Y2 + X2) - (Y1 - X1) * (Y2 - X2)) * ((Y1 + X1) * (Y2 + X2) + (Y1 - X1) * (Y2 - X2))) := by
  obtain ⟨e1, c1⟩ := h1; obtain ⟨e2, c2⟩ := h2
  constructor <;> grind

theorem add_lawR {d X1 Y1 Z1 T1 X2 Y2 Z2 T2 : R} (h1 : OnCurveR d X1 Y1 Z1 T1)
    (h2 : OnCurveR d X2 Y2 Z2 T2) :
    (((Y1 + X1) * (Y2 + X2) - (Y1 - X1) * (Y2 - X2)) * ((Z1 + Z1) * Z2 - T1 * (2 * d) * T2)) *
        (Z1 * Z1 * Z2 * Z2 + d * X1 * X2 * Y1 * Y2) =
      (((Z1 + Z1) * Z2 - T1 * (2 * d) * T2) * ((Z1 + Z1) * Z2 + T1 * (2 * d) * T2)) * ((X1 * Y2 + X2 * Y1) * Z1 * Z2) ∧
    (((Z1 + Z1) * Z2 + T1 * (2 * d) * T2) * ((Y1 + X1) * (Y2 + X2) + (Y1 - X1) * (Y2 - X2))) *
        (Z1 * Z1 * Z2 * Z2 - d * X1 * X2 * Y1 * Y2) =
      (((Z1 + Z1) * Z2 - T1 * (2 * d) * T2) * ((Z1 + Z1) * Z2 + T1 * (2 * d) * T2)) * ((Y1 * Y2 + X1 * X2) * Z1 * Z2) := by
  obtain ⟨e1, _⟩ := h1; obtain ⟨e2, _⟩ := h2
  constructor <;> grind

/-- The RFC's doubling, on ring values. -/
theorem double_onCurveR {d X Y Z T : R} (h : OnCurveR d X Y Z T) :
    OnCurveR d ((X * X + Y * Y - (X + Y) * (X + Y)) * (Z * Z + Z * Z + (X * X - Y * Y)))
      ((X * X - Y * Y) * (X * X + Y * Y))
      ((Z * Z + Z * Z + (X * X - Y * Y)) * (X * X - Y * Y))
      ((X * X + Y * Y - (X + Y) * (X + Y)) * (X * X + Y * Y)) := by
  obtain ⟨e, c⟩ := h
  constructor <;> grind

theorem double_lawR {d X Y Z T : R} (h : OnCurveR d X Y Z T) :
    ((X * X + Y * Y - (X + Y) * (X + Y)) * (Z * Z + Z * Z + (X * X - Y * Y))) * (Z * Z * Z * Z + d * X * X * Y * Y) =
      ((Z * Z + Z * Z + (X * X - Y * Y)) * (X * X - Y * Y)) * ((X * Y + X * Y) * Z * Z) ∧
    ((X * X - Y * Y) * (X * X + Y * Y)) * (Z * Z * Z * Z - d * X * X * Y * Y) =
      ((Z * Z + Z * Z + (X * X - Y * Y)) * (X * X - Y * Y)) * ((Y * Y + X * X) * Z * Z) := by
  obtain ⟨e, c⟩ := h
  constructor <;> grind

theorem neg_onCurveR {d X Y Z T : R} (h : OnCurveR d X Y Z T) : OnCurveR d (0 - X) Y Z (0 - T) := by
  obtain ⟨e, c⟩ := h
  constructor <;> grind

theorem zero_onCurveR (d : R) : OnCurveR d 0 1 1 0 := by
  constructor <;> grind

/-- A point `(x, y, 1, x y)` whose `x` solves `(d y² + 1) x² = y² − 1` is on the curve. -/
theorem affine_onCurveR {d x y : R} (h : (d * (y * y) + 1) * (x * x) = y * y - 1) :
    OnCurveR d x y 1 (x * y) := by
  constructor <;> grind

theorem root_timesR {v x i u : R} (e : v * (x * x) = 0 - u) (hi : i * i = 0 - 1) :
    v * ((x * i) * (x * i)) = u := by
  grind

theorem neg_rootR {v x u : R} (e : v * (x * x) = u) : v * ((0 - x) * (0 - x)) = u := by
  grind

end Ring

/-! ## The deployed points -/

/-- `P` is a carried point of edwards25519 in extended coordinates. -/
structure Point.OnCurve (P : Point) : Prop where
  carried : P.Carried
  on : OnCurveR (d.toNat : Fin p) (P.X.toNat : Fin p) (P.Y.toNat : Fin p) (P.Z.toNat : Fin p) (P.T.toNat : Fin p)

theorem val_zero : (Fe.zero.toNat : Fin p) = 0 := by rw [zero_toNat]; rfl
theorem val_one : (Fe.one.toNat : Fin p) = 1 := by rw [one_toNat]; rfl

/-- The four coordinates of `P.add Q`, as ring values. -/
theorem point_add_vals {P Q : Point} (hP : P.Carried) (hQ : Q.Carried) :
    (((P.add Q).X).toNat : Fin p) = (((P.Y.toNat : Fin p) + (P.X.toNat : Fin p)) * ((Q.Y.toNat : Fin p) + (Q.X.toNat : Fin p)) - ((P.Y.toNat : Fin p) - (P.X.toNat : Fin p)) * ((Q.Y.toNat : Fin p) - (Q.X.toNat : Fin p))) *
        (((P.Z.toNat : Fin p) + (P.Z.toNat : Fin p)) * (Q.Z.toNat : Fin p) - (P.T.toNat : Fin p) * (2 * (d.toNat : Fin p)) * (Q.T.toNat : Fin p)) ∧
    (((P.add Q).Y).toNat : Fin p) = (((P.Z.toNat : Fin p) + (P.Z.toNat : Fin p)) * (Q.Z.toNat : Fin p) + (P.T.toNat : Fin p) * (2 * (d.toNat : Fin p)) * (Q.T.toNat : Fin p)) *
        (((P.Y.toNat : Fin p) + (P.X.toNat : Fin p)) * ((Q.Y.toNat : Fin p) + (Q.X.toNat : Fin p)) + ((P.Y.toNat : Fin p) - (P.X.toNat : Fin p)) * ((Q.Y.toNat : Fin p) - (Q.X.toNat : Fin p))) ∧
    (((P.add Q).Z).toNat : Fin p) = (((P.Z.toNat : Fin p) + (P.Z.toNat : Fin p)) * (Q.Z.toNat : Fin p) - (P.T.toNat : Fin p) * (2 * (d.toNat : Fin p)) * (Q.T.toNat : Fin p)) *
        (((P.Z.toNat : Fin p) + (P.Z.toNat : Fin p)) * (Q.Z.toNat : Fin p) + (P.T.toNat : Fin p) * (2 * (d.toNat : Fin p)) * (Q.T.toNat : Fin p)) ∧
    (((P.add Q).T).toNat : Fin p) = (((P.Y.toNat : Fin p) + (P.X.toNat : Fin p)) * ((Q.Y.toNat : Fin p) + (Q.X.toNat : Fin p)) - ((P.Y.toNat : Fin p) - (P.X.toNat : Fin p)) * ((Q.Y.toNat : Fin p) - (Q.X.toNat : Fin p))) *
        (((P.Y.toNat : Fin p) + (P.X.toNat : Fin p)) * ((Q.Y.toNat : Fin p) + (Q.X.toNat : Fin p)) + ((P.Y.toNat : Fin p) - (P.X.toNat : Fin p)) * ((Q.Y.toNat : Fin p) - (Q.X.toNat : Fin p))) := by
  obtain ⟨px, py, pz, pt⟩ := hP; obtain ⟨qx, qy, qz, qt⟩ := hQ
  have a := mul_carried (sub_carried py px) (sub_carried qy qx)
  have va : (((P.Y.sub P.X).mul (Q.Y.sub Q.X)).toNat : Fin p) = ((P.Y.toNat : Fin p) - (P.X.toNat : Fin p)) * ((Q.Y.toNat : Fin p) - (Q.X.toNat : Fin p)) := by
    rw [val_mul (sub_carried py px) (sub_carried qy qx), val_sub py px, val_sub qy qx]
  have b := mul_carried (add_carried py px) (add_carried qy qx)
  have vb : (((P.Y.add P.X).mul (Q.Y.add Q.X)).toNat : Fin p) = ((P.Y.toNat : Fin p) + (P.X.toNat : Fin p)) * ((Q.Y.toNat : Fin p) + (Q.X.toNat : Fin p)) := by
    rw [val_mul (add_carried py px) (add_carried qy qx), val_add py px, val_add qy qx]
  have c := mul_carried (mul_carried pt d2_carried) qt
  have vc : (((P.T.mul d2).mul Q.T).toNat : Fin p) = (P.T.toNat : Fin p) * (2 * (d.toNat : Fin p)) * (Q.T.toNat : Fin p) := by
    rw [val_mul (mul_carried pt d2_carried) qt, val_mul pt d2_carried, val_d2]
  have dd := mul_carried (add_carried pz pz) qz
  have vd : (((P.Z.add P.Z).mul Q.Z).toNat : Fin p) = ((P.Z.toNat : Fin p) + (P.Z.toNat : Fin p)) * (Q.Z.toNat : Fin p) := by
    rw [val_mul (add_carried pz pz) qz, val_add pz pz]
  unfold Point.add
  dsimp only
  generalize (P.Y.sub P.X).mul (Q.Y.sub Q.X) = A at a va ⊢
  generalize (P.Y.add P.X).mul (Q.Y.add Q.X) = B at b vb ⊢
  generalize (P.T.mul d2).mul Q.T = C at c vc ⊢
  generalize (P.Z.add P.Z).mul Q.Z = D at dd vd ⊢
  rw [val_mul (sub_carried b a) (sub_carried dd c), val_mul (add_carried dd c) (add_carried b a),
    val_mul (sub_carried dd c) (add_carried dd c), val_mul (sub_carried b a) (add_carried b a),
    val_sub b a, val_sub dd c, val_add dd c, val_add b a, va, vb, vc, vd]
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- The four coordinates of `P.double`, as ring values. -/
theorem point_double_vals {P : Point} (hP : P.Carried) :
    (P.double.X.toNat : Fin p) = ((P.X.toNat : Fin p) * (P.X.toNat : Fin p) + (P.Y.toNat : Fin p) * (P.Y.toNat : Fin p) - ((P.X.toNat : Fin p) + (P.Y.toNat : Fin p)) * ((P.X.toNat : Fin p) + (P.Y.toNat : Fin p))) *
        ((P.Z.toNat : Fin p) * (P.Z.toNat : Fin p) + (P.Z.toNat : Fin p) * (P.Z.toNat : Fin p) + ((P.X.toNat : Fin p) * (P.X.toNat : Fin p) - (P.Y.toNat : Fin p) * (P.Y.toNat : Fin p))) ∧
    (P.double.Y.toNat : Fin p) = ((P.X.toNat : Fin p) * (P.X.toNat : Fin p) - (P.Y.toNat : Fin p) * (P.Y.toNat : Fin p)) * ((P.X.toNat : Fin p) * (P.X.toNat : Fin p) + (P.Y.toNat : Fin p) * (P.Y.toNat : Fin p)) ∧
    (P.double.Z.toNat : Fin p) = ((P.Z.toNat : Fin p) * (P.Z.toNat : Fin p) + (P.Z.toNat : Fin p) * (P.Z.toNat : Fin p) + ((P.X.toNat : Fin p) * (P.X.toNat : Fin p) - (P.Y.toNat : Fin p) * (P.Y.toNat : Fin p))) *
        ((P.X.toNat : Fin p) * (P.X.toNat : Fin p) - (P.Y.toNat : Fin p) * (P.Y.toNat : Fin p)) ∧
    (P.double.T.toNat : Fin p) = ((P.X.toNat : Fin p) * (P.X.toNat : Fin p) + (P.Y.toNat : Fin p) * (P.Y.toNat : Fin p) - ((P.X.toNat : Fin p) + (P.Y.toNat : Fin p)) * ((P.X.toNat : Fin p) + (P.Y.toNat : Fin p))) *
        ((P.X.toNat : Fin p) * (P.X.toNat : Fin p) + (P.Y.toNat : Fin p) * (P.Y.toNat : Fin p)) := by
  obtain ⟨px, py, pz, _⟩ := hP
  have a := sq_carried px
  have va : (P.X.sq.toNat : Fin p) = (P.X.toNat : Fin p) * (P.X.toNat : Fin p) := val_mul px px
  have b := sq_carried py
  have vb : (P.Y.sq.toNat : Fin p) = (P.Y.toNat : Fin p) * (P.Y.toNat : Fin p) := val_mul py py
  have z := sq_carried pz
  have vz : (P.Z.sq.toNat : Fin p) = (P.Z.toNat : Fin p) * (P.Z.toNat : Fin p) := val_mul pz pz
  have s := sq_carried (add_carried px py)
  have vs : (((P.X.add P.Y).sq).toNat : Fin p) = ((P.X.toNat : Fin p) + (P.Y.toNat : Fin p)) * ((P.X.toNat : Fin p) + (P.Y.toNat : Fin p)) := by
    rw [show (P.X.add P.Y).sq = (P.X.add P.Y).mul (P.X.add P.Y) from rfl,
      val_mul (add_carried px py) (add_carried px py), val_add px py]
  unfold Point.double
  dsimp only
  generalize P.X.sq = A at a va ⊢
  generalize P.Y.sq = B at b vb ⊢
  generalize P.Z.sq = Z2 at z vz ⊢
  generalize (P.X.add P.Y).sq = S at s vs ⊢
  have H := add_carried a b
  have G := sub_carried a b
  have E := sub_carried H s
  have F := add_carried (add_carried z z) G
  rw [val_mul E F, val_mul G H, val_mul F G, val_mul E H, val_sub H s, val_add (add_carried z z) G,
    val_add z z, val_sub a b, val_add a b, va, vb, vz, vs]
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem point_add_onCurve {P Q : Point} (hP : P.OnCurve) (hQ : Q.OnCurve) : (P.add Q).OnCurve := by
  refine ⟨point_add_carried hP.carried hQ.carried, ?_⟩
  obtain ⟨hx, hy, hz, ht⟩ := point_add_vals hP.carried hQ.carried
  rw [hx, hy, hz, ht]
  exact add_onCurveR hP.on hQ.on

/-- The addition law: `P.add Q` is the Edwards sum of `P` and `Q` (cross-multiplied, in `ℤ/p`). -/
theorem point_add_law {P Q : Point} (hP : P.OnCurve) (hQ : Q.OnCurve) :
    (((P.add Q).X).toNat : Fin p) * ((P.Z.toNat : Fin p) * (P.Z.toNat : Fin p) * (Q.Z.toNat : Fin p) * (Q.Z.toNat : Fin p) + (d.toNat : Fin p) * (P.X.toNat : Fin p) * (Q.X.toNat : Fin p) * (P.Y.toNat : Fin p) * (Q.Y.toNat : Fin p)) =
      (((P.add Q).Z).toNat : Fin p) * (((P.X.toNat : Fin p) * (Q.Y.toNat : Fin p) + (Q.X.toNat : Fin p) * (P.Y.toNat : Fin p)) * (P.Z.toNat : Fin p) * (Q.Z.toNat : Fin p)) ∧
    (((P.add Q).Y).toNat : Fin p) * ((P.Z.toNat : Fin p) * (P.Z.toNat : Fin p) * (Q.Z.toNat : Fin p) * (Q.Z.toNat : Fin p) - (d.toNat : Fin p) * (P.X.toNat : Fin p) * (Q.X.toNat : Fin p) * (P.Y.toNat : Fin p) * (Q.Y.toNat : Fin p)) =
      (((P.add Q).Z).toNat : Fin p) * (((P.Y.toNat : Fin p) * (Q.Y.toNat : Fin p) + (P.X.toNat : Fin p) * (Q.X.toNat : Fin p)) * (P.Z.toNat : Fin p) * (Q.Z.toNat : Fin p)) := by
  obtain ⟨hx, hy, hz, _⟩ := point_add_vals hP.carried hQ.carried
  rw [hx, hy, hz]
  exact add_lawR hP.on hQ.on

theorem point_double_onCurve {P : Point} (hP : P.OnCurve) : P.double.OnCurve := by
  refine ⟨point_double_carried hP.carried, ?_⟩
  obtain ⟨hx, hy, hz, ht⟩ := point_double_vals hP.carried
  rw [hx, hy, hz, ht]
  exact double_onCurveR hP.on

/-- The doubling law: `P.double` is the Edwards sum `P + P` (cross-multiplied, in `ℤ/p`). -/
theorem point_double_law {P : Point} (hP : P.OnCurve) :
    (P.double.X.toNat : Fin p) * ((P.Z.toNat : Fin p) * (P.Z.toNat : Fin p) * (P.Z.toNat : Fin p) * (P.Z.toNat : Fin p) + (d.toNat : Fin p) * (P.X.toNat : Fin p) * (P.X.toNat : Fin p) * (P.Y.toNat : Fin p) * (P.Y.toNat : Fin p)) =
      (P.double.Z.toNat : Fin p) * (((P.X.toNat : Fin p) * (P.Y.toNat : Fin p) + (P.X.toNat : Fin p) * (P.Y.toNat : Fin p)) * (P.Z.toNat : Fin p) * (P.Z.toNat : Fin p)) ∧
    (P.double.Y.toNat : Fin p) * ((P.Z.toNat : Fin p) * (P.Z.toNat : Fin p) * (P.Z.toNat : Fin p) * (P.Z.toNat : Fin p) - (d.toNat : Fin p) * (P.X.toNat : Fin p) * (P.X.toNat : Fin p) * (P.Y.toNat : Fin p) * (P.Y.toNat : Fin p)) =
      (P.double.Z.toNat : Fin p) * (((P.Y.toNat : Fin p) * (P.Y.toNat : Fin p) + (P.X.toNat : Fin p) * (P.X.toNat : Fin p)) * (P.Z.toNat : Fin p) * (P.Z.toNat : Fin p)) := by
  obtain ⟨hx, hy, hz, _⟩ := point_double_vals hP.carried
  rw [hx, hy, hz]
  exact double_lawR hP.on

theorem point_neg_onCurve {P : Point} (hP : P.OnCurve) : P.neg.OnCurve := by
  refine ⟨point_neg_carried hP.carried, ?_⟩
  obtain ⟨⟨px, _, _, pt⟩, o⟩ := hP
  unfold Point.neg
  dsimp only
  rw [val_sub zero_carried px, val_sub zero_carried pt, val_zero]
  exact neg_onCurveR o

theorem point_zero_onCurve : Point.zero.OnCurve := by
  refine ⟨point_zero_carried, ?_⟩
  unfold Point.zero
  dsimp only
  rw [val_zero, val_one]
  exact zero_onCurveR _

theorem step_onCurve {P Q PQ R : Point} (hP : P.OnCurve) (hQ : Q.OnCurve) (hPQ : PQ.OnCurve)
    (hR : R.OnCurve) (a b : Nat) : (Point.step P Q PQ R a b).OnCurve := by
  have hd := point_double_onCurve hR
  simp only [Point.step]
  split
  · exact point_add_onCurve hd hPQ
  · exact point_add_onCurve hd hP
  · exact point_add_onCurve hd hQ
  · exact hd

theorem ladder_onCurve {P Q PQ R : Point} (hP : P.OnCurve) (hQ : Q.OnCurve) (hPQ : PQ.OnCurve)
    (hR : R.OnCurve) : ∀ (a b n : Nat), (Point.ladder P Q PQ R a b n).OnCurve
  | _, _, 0 => hR
  | a, b, n + 1 => step_onCurve hP hQ hPQ (ladder_onCurve hP hQ hPQ hR (a >>> 1) (b >>> 1) n) a b

theorem mul2_onCurve {P Q PQ : Point} (hP : P.OnCurve) (hQ : Q.OnCurve) (hPQ : PQ.OnCurve)
    (a b n : Nat) : (Point.mul2 P Q PQ a b n).OnCurve :=
  ladder_onCurve hP hQ hPQ point_zero_onCurve a b n

theorem B_onCurve : B.OnCurve := by
  refine ⟨B_carried, ?_⟩
  have hx := ofNat_spec (x := 15112221349535400772501151409588531511454012693041857206046113283949847762202) (by decide +kernel)
  have hy := ofNat_spec (x := 46316835694926478169428394003475163141307993866256225615783033603165251855960) (by decide +kernel)
  unfold B
  dsimp only
  rw [val_mul hx.1 hy.1, val_one, hx.2, hy.2]
  apply affine_onCurveR
  decide +kernel

/-- What `rootCheck` returns solves `v r² = u`. -/
theorem rootCheck_solves {u v x r : Fe} (hu : u.Carried) (hv : v.Carried) (hx : x.Carried)
    (h : rootCheck u v x = some r) : (v.toNat : Fin p) * ((r.toNat : Fin p) * (r.toNat : Fin p)) = (u.toNat : Fin p) := by
  have hi : (sqrtM1.toNat : Fin p) * (sqrtM1.toNat : Fin p) = 0 - 1 := by
    unfold sqrtM1
    rw [(ofNat_spec (by decide +kernel)).2]
    decide +kernel
  have vxx : ((v.mul x.sq).toNat : Fin p) = (v.toNat : Fin p) * ((x.toNat : Fin p) * (x.toNat : Fin p)) := by
    rw [val_mul hv (sq_carried hx), show x.sq = x.mul x from rfl, val_mul hx hx]
  have toFin : ∀ {f g : Fe}, f.eq g = true → (f.toNat : Fin p) = (g.toNat : Fin p) := fun h => by rw [eq_iff.mp h]
  unfold rootCheck at h
  dsimp only at h
  split at h
  · rename_i he; cases h; rw [← vxx]; exact toFin he
  · split at h
    · rename_i _ he; cases h
      have e := toFin he
      rw [vxx, val_sub zero_carried hu, val_zero] at e
      rw [val_mul hx sqrtM1_carried]
      exact root_timesR e hi
    · cases h

theorem signed_onCurve {x y : Fe} {sign : Nat} {P : Point} (hx : x.Carried) (hy : y.Carried)
    (hs : ((d.toNat : Fin p) * ((y.toNat : Fin p) * (y.toNat : Fin p)) + 1) * ((x.toNat : Fin p) * (x.toNat : Fin p)) = (y.toNat : Fin p) * (y.toNat : Fin p) - 1)
    (h : signed x y sign = some P) : P.OnCurve := by
  refine ⟨signed_carried hx hy h, ?_⟩
  unfold signed at h
  split at h
  · cases h
  · rw [← Option.some.inj h]
    dsimp only
    split
    · rw [val_mul hx hy, val_one]
      exact affine_onCurveR hs
    · rw [val_mul (sub_carried zero_carried hx) hy, val_one, val_sub zero_carried hx, val_zero]
      exact affine_onCurveR (neg_rootR hs)

/-- Every point `decodePoint` returns is on the curve. -/
theorem decodePoint_onCurve {b : ByteArray} {off : Nat} {P : Point} (h : decodePoint b off = some P) :
    P.OnCurve := by
  unfold decodePoint at h
  dsimp only at h
  split at h
  · cases h
  · have hy := (ofNat_spec (x := leNat b off 32 % 2 ^ 255) (Nat.mod_lt _ (by decide))).1
    split at h
    · cases h
    · rename_i x hx
      refine signed_onCurve (recoverX_carried hy hx) hy ?_ h
      unfold recoverX sqrtRatio at hx
      have hu := sub_carried (sq_carried hy) one_carried
      have hv := add_carried (mul_carried d_carried (sq_carried hy)) one_carried
      have e := rootCheck_solves hu hv (candidateFrom_carried hu hv (mul_carried (sq_carried hv) hv)) hx
      rw [val_add (mul_carried d_carried (sq_carried hy)) one_carried, val_mul d_carried (sq_carried hy),
        val_sub (sq_carried hy) one_carried, val_one, val_sq hy] at e
      exact e

/-! ## The tooth -/

/-- `ext` (`X Y = Z T`) is not decoration: `(4, 5, 3, 0)` satisfies the curve equation's other half
`Y² − X² = Z² + d T²` in `ℤ/p` but not `X Y = Z T`, and for it the addition law's `x` equation is false. -/
theorem add_law_needs_ext :
    let X : Fin p := 4; let Y : Fin p := 5; let Z : Fin p := 3; let T : Fin p := 0
    let dd : Fin p := Fin.ofNat p 37095705934669439343138083508754565189542113879843219016388785533085940283555
    Y * Y - X * X = Z * Z + dd * T * T ∧ X * Y ≠ Z * T ∧
    (((Y + X) * (Y + X) - (Y - X) * (Y - X)) * ((Z + Z) * Z - T * (2 * dd) * T)) *
        (Z * Z * Z * Z + dd * X * X * Y * Y) ≠
      (((Z + Z) * Z - T * (2 * dd) * T) * ((Z + Z) * Z + T * (2 * dd) * T)) * ((X * Y + X * Y) * Z * Z) := by
  decide +kernel

end Nanodregg.Codec.Ed25519
