import Codec.Proofs.Group
import Codec.Proofs.Ed25519.Bytes

/-!
# Decompression is RFC 8032 §5.1.3 (CODEC-23, signature correctness)

`decodePoint b off` reads `n = leNat b off 32`, `y = n mod 2^255`, the sign bit `n >>> 255`, and recovers
`x` by `sqrtRatio`. Proved here, for EVERY input:

* `sqrtRatio_some` / `recoverX_root`: when `u = v x²` with `v ≠ 0`, the candidate `u v³ (u v⁷)^((p−5)/8)` (or
  it times `√−1`) passes `rootCheck`, and what `recoverX` returns is `x` or `−x` — Euler's criterion, through
  `x^((p−1)/2) = ±1` (Fermat over the prime `p`); `v = d y² + 1` is never 0 because `d` is not a square.
* `decodePoint_affine`: what decode returns names an affine point `(x, y)` with `y = n mod 2^255 < p`, on the
  curve, whose `x` has the parity of the sign bit.
* `decodePoint_some`: conversely, for every such `(x, y)` decode returns a point naming it.
So decode accepts exactly the RFC's encodings and returns the RFC's point: the root is the one of the right
parity, `x = 0` with sign 1 is refused (no `x` of value 0 is odd), `y ≥ p` is refused.
-/

namespace Nanodregg.Codec.Ed25519

open Fin.NatCast

private theorem val_cast (a : Nat) : ((a : Fin p) : Nat) = a % p := rfl

/-! ## Over any commutative ring with inverses -/

section Ring
variable {R : Type} [Lean.Grind.CommRing R]

theorem sq_oneR (inv : ∀ a : R, a ≠ 0 → ∃ b, a * b = 1) {t : R} (h : t * t = 1) : t = 1 ∨ t = 0 - 1 := by
  rcases domain_of_invR inv (t - 1) (t + 1) (by grind) with e | e
  · left; grind
  · right; grind

theorem sq_eqR (inv : ∀ a : R, a ≠ 0 → ∃ b, a * b = 1) {r x : R} (h : r * r = x * x) : r = x ∨ r = 0 - x := by
  rcases domain_of_invR inv (r - x) (r + x) (by grind) with e | e
  · left; grind
  · right; grind

/-- `d y² + 1 ≠ 0` when `d` is not a square and `−1` is: else `d = (i / y)²`. -/
theorem den_neR (inv : ∀ a : R, a ≠ 0 → ∃ b, a * b = 1) {d i : R} (hi : i * i = 0 - 1)
    (hd : ∀ s : R, s * s ≠ d) (h10 : (1 : R) ≠ 0) (y : R) : d * (y * y) + 1 ≠ 0 := by
  intro h
  by_cases hy : y = 0
  · subst hy; exact h10 (by grind)
  · obtain ⟨w, hw⟩ := inv y hy
    apply hd (i * w)
    have e1 : d = d * (y * w) * (y * w) := by rw [hw]; grind
    have e2 : d * (y * w) * (y * w) = (d * (y * y)) * (w * w) := by grind
    have e3 : d * (y * y) = 0 - 1 := by grind
    rw [e1, e2, e3, ← hi]
    grind

theorem neg_oneR (a b : R) : a * (b * (0 - 1)) = 0 - a * b := by grind
theorem one_rR (a b : R) : a * (b * 1) = a * b := by grind
theorem mul_oneR (a : R) : a = a * 1 := by grind
theorem zero_subR : (0 : R) - 0 = 0 * 1 := by grind
theorem neg_negR (x : R) : 0 - (0 - x) = x * 1 := by grind

end Ring

/-! ## Powers in `ℤ/p` through `Nat` (never `Fin`'s unary `npow`) -/

private def pw (a : Fin p) (e : Nat) : Fin p := ((a.val ^ e : Nat) : Fin p)

theorem fin_cast_val (a : Fin p) : ((a.val : Nat) : Fin p) = a :=
  Fin.ext (by rw [val_cast, Nat.mod_eq_of_lt a.isLt])

private theorem cast_mul (a b : Nat) : ((a * b : Nat) : Fin p) = (a : Fin p) * (b : Fin p) := by
  apply Fin.ext; rw [Fin.val_mul, val_cast, val_cast, val_cast, Nat.mul_mod]

theorem fin_cast_mod (a : Nat) : ((a % p : Nat) : Fin p) = (a : Fin p) := by
  apply Fin.ext; rw [val_cast, val_cast, Nat.mod_mod]

private theorem cast_pow_mod (a e : Nat) : (((a % p) ^ e : Nat) : Fin p) = ((a ^ e : Nat) : Fin p) := by
  apply Fin.ext; rw [val_cast, val_cast, ← Nat.pow_mod]

private theorem cast_one : ((1 : Nat) : Fin p) = 1 := rfl

private theorem pw_zero (a : Fin p) : pw a 0 = 1 := by unfold pw; rw [Nat.pow_zero]; rfl

private theorem pw_succ (a : Fin p) (e : Nat) : pw a (e + 1) = pw a e * a := by
  unfold pw; rw [Nat.pow_succ, cast_mul, fin_cast_val]

private theorem pw_add (a : Fin p) (m n : Nat) : pw a (m + n) = pw a m * pw a n := by
  unfold pw; rw [Nat.pow_add, cast_mul]

private theorem pw_mul_base (a b : Fin p) (e : Nat) : pw (a * b) e = pw a e * pw b e := by
  unfold pw; rw [Fin.val_mul, cast_pow_mod, Nat.mul_pow, cast_mul]

private theorem pw_pw (a : Fin p) (m n : Nat) : pw (pw a m) n = pw a (m * n) := by
  unfold pw; rw [val_cast, cast_pow_mod, ← Nat.pow_mul]

private theorem pw_fermat {a : Fin p} (h : a ≠ 0) : pw a (p - 1) = 1 := by
  have hav : a.val % p ≠ 0 := by rw [Nat.mod_eq_of_lt a.isLt]; exact fun e => h (Fin.ext e)
  unfold pw
  rw [← fin_cast_mod, fin_fermat _ hav, cast_one]

private theorem pw_zero_base (e : Nat) : pw 0 (e + 1) = 0 := by
  rw [pw_succ]; grind

/-! ## `Fe.pow` and `Fe.inv` -/

private theorem low_bit (a n : Nat) : a % 2 ^ (n + 1) = (a >>> 1) % 2 ^ n + (a >>> 1) % 2 ^ n + a % 2 := by
  rw [Nat.shiftRight_eq_div_pow, Nat.pow_one, Nat.pow_succ, Nat.mul_comm, Nat.mod_mul]
  omega

/-- `Fe.pow` is the power of the value, the exponent read mod `2^n`. -/
theorem pow_toNat {f : Fe} (hf : f.Carried) : ∀ (n e : Nat), (f.pow e n).toNat = f.toNat ^ (e % 2 ^ n) % p
  | 0, e => by
    simp only [Fe.pow]
    rw [one_toNat, Nat.pow_zero, Nat.mod_one, Nat.pow_zero]
    exact (Nat.mod_eq_of_lt (by decide)).symm
  | n + 1, e => by
    simp only [Fe.pow]
    have hc := pow_carried hf (e >>> 1) n
    have hs : (f.pow (e >>> 1) n).sq.toNat = f.toNat ^ ((e >>> 1) % 2 ^ n) * f.toNat ^ ((e >>> 1) % 2 ^ n) % p := by
      rw [sq_toNat hc, pow_toNat hf n (e >>> 1), Nat.mod_mul_mod, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]
    rw [low_bit e n]
    split
    · rename_i hb
      have h1 : e % 2 = 1 := by rw [← Nat.and_one_is_mod]; exact beq_iff_eq.mp hb
      rw [mul_toNat (sq_carried hc) hf, hs, Nat.mod_mul_mod, h1, Nat.pow_succ, Nat.pow_add]
    · rename_i hb
      have h0 : e % 2 = 0 := by
        rw [← Nat.and_one_is_mod]
        have := Nat.and_one_is_mod e ▸ Nat.mod_lt e (by decide : 0 < 2)
        have hne : e &&& 1 ≠ 1 := fun h => hb (beq_iff_eq.mpr h)
        omega
      rw [hs, h0, Nat.add_zero, Nat.pow_add]

theorem pow_val {f : Fe} (hf : f.Carried) {e n : Nat} (he : e < 2 ^ n) :
    ((f.pow e n).toNat : Fin p) = pw (f.toNat : Fin p) e := by
  unfold pw
  rw [pow_toNat hf, Nat.mod_eq_of_lt he, fin_cast_mod, val_cast, cast_pow_mod]

/-- `Fe.inv` inverts every unit (Fermat: `f · f^(p−2) = f^(p−1) = 1`). -/
theorem inv_val {f : Fe} (hf : f.Carried) (h : (f.toNat : Fin p) ≠ 0) :
    (f.toNat : Fin p) * (f.inv.toNat : Fin p) = 1 := by
  unfold Fe.inv
  have hs : p - 2 + 1 = p - 1 := by rw [p_eq]
  rw [pow_val hf (by rw [p_eq]; decide), Fin.mul_comm, ← pw_succ, hs, pw_fermat h]

/-! ## The square root (RFC 8032 §5.1.3) -/

/-- The candidate is `x^((p+3)/4)` when `u = v x²`: `u v³ (u v⁷)^e = x^(2e+2) v^(8e+4)`, and `v^(p−1) = 1`. -/
private theorem cand_alg {v x : Fin p} {e : Nat} (hv : v ≠ 0) (he : 8 * e + 4 = p - 1) :
    v * (x * x) * (v * v * v) * pw (v * (x * x) * (v * v * v * (v * v * v) * v)) e = pw x (2 * e + 2) := by
  have h1 : v * (x * x) * (v * v * v * (v * v * v) * v) = pw v 8 * pw x 2 := by
    simp only [pw_succ, pw_zero]; grind
  have h4 : v * v * v * v = pw v 4 := by simp only [pw_succ, pw_zero]; grind
  have h2 : x * x = pw x 2 := by simp only [pw_succ, pw_zero]; grind
  have hv1 : pw v (8 * e) * pw v 4 = 1 := by rw [← pw_add, he, pw_fermat hv]
  have hx1 : pw x (2 * e) * pw x 2 = pw x (2 * e + 2) := by rw [← pw_add]
  rw [h1, pw_mul_base, pw_pw, pw_pw, Nat.mul_comm 8 e, Nat.mul_comm 2 e]
  rw [Nat.mul_comm 8 e] at hv1
  rw [Nat.mul_comm 2 e] at hx1
  have re : ∀ a b c d : Fin p, a * c * (b * d) = (b * a) * (d * c) * 1 := fun a b c d => by grind
  rw [show v * (x * x) * (v * v * v) = (v * v * v * v) * (x * x) by grind, h4, h2, re, hv1, hx1]
  grind

/-- Euler's criterion on the candidate: `v c² = ±u`. -/
private theorem root_alg {u v c x : Fin p} {e : Nat} (he : 8 * e + 4 = p - 1)
    (hu : u = v * (x * x)) (hc : c = pw x (2 * e + 2)) : v * (c * c) = u ∨ v * (c * c) = 0 - u := by
  by_cases hx : x = 0
  · left; subst hx hc hu; rw [pw_zero_base]
  · have hcc : c * c = x * x * pw x (4 * e + 2) := by
      rw [hc, ← pw_add, show x * x = pw x 2 by simp only [pw_succ, pw_zero]; grind, ← pw_add]
      congr 1; omega
    have ht : pw x (4 * e + 2) * pw x (4 * e + 2) = 1 := by
      rw [← pw_add, show 4 * e + 2 + (4 * e + 2) = p - 1 by omega, pw_fermat hx]
    rw [hcc, hu]
    rcases sq_oneR fin_inv ht with t | t
    · left; rw [t]; exact one_rR _ _
    · right; rw [t]; exact neg_oneR _ _

theorem rootCheck_some {u v x : Fe} (hu : u.Carried) (hv : v.Carried) (hx : x.Carried)
    (h : (v.toNat : Fin p) * ((x.toNat : Fin p) * (x.toNat : Fin p)) = (u.toNat : Fin p) ∨
      (v.toNat : Fin p) * ((x.toNat : Fin p) * (x.toNat : Fin p)) = 0 - (u.toNat : Fin p)) :
    ∃ r, rootCheck u v x = some r := by
  have vxx : ((v.mul x.sq).toNat : Fin p) = (v.toNat : Fin p) * ((x.toNat : Fin p) * (x.toNat : Fin p)) := by
    rw [val_mul hv (sq_carried hx), show x.sq = x.mul x from rfl, val_mul hx hx]
  unfold rootCheck
  dsimp only
  split
  · exact ⟨_, rfl⟩
  · rename_i h1
    split
    · exact ⟨_, rfl⟩
    · rename_i h2
      exfalso
      rcases h with e | e
      · exact h1 (eq_iff.mpr (fe_cast_eq.mpr (vxx.trans e)))
      · exact h2 (eq_iff.mpr (fe_cast_eq.mpr (by rw [vxx, val_sub zero_carried hu, val_zero]; exact e)))

theorem sqrtRatio_some {u v : Fe} (hu : u.Carried) (hv : v.Carried) (hv0 : (v.toNat : Fin p) ≠ 0) {x : Fin p}
    (hux : (u.toNat : Fin p) = (v.toNat : Fin p) * (x * x)) : ∃ r, sqrtRatio u v = some r := by
  have hv3 := mul_carried (sq_carried hv) hv
  have he : 8 * ((p - 5) / 8) + 4 = p - 1 := by rw [p_eq]
  unfold sqrtRatio
  apply rootCheck_some hu hv (candidateFrom_carried hu hv hv3)
  apply root_alg he hux
  unfold candidateFrom
  rw [val_mul (mul_carried hu hv3) (pow_carried (mul_carried hu (mul_carried (sq_carried hv3) hv)) _ _),
    val_mul hu hv3, pow_val (mul_carried hu (mul_carried (sq_carried hv3) hv)) (by rw [p_eq]; decide),
    val_mul hu (mul_carried (sq_carried hv3) hv), val_mul (sq_carried hv3) hv, val_sq hv3,
    val_mul (sq_carried hv) hv, val_sq hv, hux]
  exact cand_alg hv0 he

/-- `d y² + 1` is never 0: else `d = (√−1 / y)²`, and `d` is not a square. -/
theorem den_ne_zero (y : Fin p) : (d.toNat : Fin p) * (y * y) + 1 ≠ 0 :=
  den_neR fin_inv sqrtM1_sq d_nonsquare fin_one_ne_zero y

/-- On the curve, `recoverX` finds `x` up to sign. -/
theorem recoverX_root {y : Fe} (hy : y.Carried) {x : Fin p}
    (hc : (y.toNat : Fin p) * (y.toNat : Fin p) - x * x = 1 + (d.toNat : Fin p) * (x * x) * ((y.toNat : Fin p) * (y.toNat : Fin p))) :
    ∃ r, recoverX y = some r ∧ ((r.toNat : Fin p) = x ∨ (r.toNat : Fin p) = 0 - x) := by
  have hu := sub_carried (sq_carried hy) one_carried
  have hv := add_carried (mul_carried d_carried (sq_carried hy)) one_carried
  have uval : ((y.sq.sub Fe.one).toNat : Fin p) = (y.toNat : Fin p) * (y.toNat : Fin p) - 1 := by
    rw [val_sub (sq_carried hy) one_carried, val_sq hy, val_one]
  have vval : (((d.mul y.sq).add Fe.one).toNat : Fin p) = (d.toNat : Fin p) * ((y.toNat : Fin p) * (y.toNat : Fin p)) + 1 := by
    rw [val_add (mul_carried d_carried (sq_carried hy)) one_carried, val_mul d_carried (sq_carried hy), val_sq hy, val_one]
  have hv0 : (((d.mul y.sq).add Fe.one).toNat : Fin p) ≠ 0 := by rw [vval]; exact den_ne_zero _
  have hux : ((y.sq.sub Fe.one).toNat : Fin p) = (((d.mul y.sq).add Fe.one).toNat : Fin p) * (x * x) := by
    rw [uval, vval]; grind
  obtain ⟨r, hr⟩ := sqrtRatio_some hu hv hv0 hux
  refine ⟨r, hr, ?_⟩
  unfold sqrtRatio at hr
  have s := rootCheck_solves hu hv (candidateFrom_carried hu hv (mul_carried (sq_carried hv) hv)) hr
  rw [hux, Fin.mul_comm, Fin.mul_comm _ (x * x)] at s
  exact sq_eqR fin_inv (cancelR fin_inv hv0 s)

/-! ## The sign rule -/

theorem p_odd : p % 2 = 1 := by rw [p_eq]

/-- The value of `0 − x` is `p − x` for `x ≠ 0`, so its parity flips (`q` is `p`, kept abstract for `omega`). -/
theorem neg_parity {q R X : Nat} (hq : q % 2 = 1) (hX : X < q) (hR : R = (q - X + 0) % q) :
    (X = 0 ∧ R = 0) ∨ (X ≠ 0 ∧ R = q - X ∧ R % 2 ≠ X % 2) := by
  by_cases h : X = 0
  · left; subst h; rw [Nat.sub_zero, Nat.add_zero, Nat.mod_self] at hR; exact ⟨rfl, hR⟩
  · right
    rw [Nat.add_zero, Nat.mod_eq_of_lt (by omega)] at hR
    exact ⟨h, hR, by omega⟩

private theorem toNat_of_val {f : Fe} {x : Fin p} (h : (f.toNat : Fin p) = x) : f.toNat = x.val := by
  rw [← h, val_cast, Nat.mod_eq_of_lt (toNat_lt f)]

private theorem val_neg_toNat {f : Fe} {x : Fin p} (h : (f.toNat : Fin p) = 0 - x) :
    f.toNat = (p - x.val + 0) % p := by
  rw [toNat_of_val h, Fin.val_sub]; rfl

/-- `signed` picks the root of the sign bit's parity. -/
theorem signed_some {r y : Fe} {x : Fin p} {s : Nat} (hrx : (r.toNat : Fin p) = x ∨ (r.toNat : Fin p) = 0 - x)
    (hr : r.Carried) (hs : x.val % 2 = s) :
    ∃ Q, signed r y s = some Q ∧ (Q.X.toNat : Fin p) = x * (Q.Z.toNat : Fin p) ∧
      (Q.Y.toNat : Fin p) = (y.toNat : Fin p) * (Q.Z.toNat : Fin p) := by
  have hx := x.isLt
  unfold signed
  split
  · rename_i h
    exfalso
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    rcases hrx with e | e
    · rw [toNat_of_val e] at h; omega
    · rcases neg_parity p_odd hx (val_neg_toNat e) with ⟨h0, -⟩ | ⟨h0, h1, -⟩
      · omega
      · omega
  · refine ⟨_, rfl, ?_, ?_⟩ <;> dsimp only <;> rw [val_one]
    · split
      · rename_i hp
        have hp : r.toNat % 2 = s := beq_iff_eq.mp hp
        rcases hrx with e | e
        · rw [e]; exact mul_oneR _
        · rcases neg_parity p_odd hx (val_neg_toNat e) with ⟨h0, h1⟩ | ⟨h0, h1, h2⟩
          · have : x = 0 := Fin.ext h0
            rw [e, this]; exact zero_subR
          · omega
      · rename_i hp
        have hp : r.toNat % 2 ≠ s := fun h => hp (beq_iff_eq.mpr h)
        rw [val_sub zero_carried hr, val_zero]
        rcases hrx with e | e
        · rw [toNat_of_val e] at hp; omega
        · rw [e]; exact neg_negR _
    · exact mul_oneR _

/-! ## What decode returns, and that it returns -/

/-- **Decode is the RFC's**: what `decodePoint` returns names the affine `(x, y)` with `y = n mod 2^255 < p`,
on the curve, `x` of the sign bit's parity (`n` = the 32 bytes read little-endian). -/
theorem decodePoint_affine {b : ByteArray} {off : Nat} {Q : Point} (h : decodePoint b off = some Q) :
    leNat b off 32 % 2 ^ 255 < p ∧ ∃ x : Fin p, Q.Affine x ((leNat b off 32 % 2 ^ 255 : Nat) : Fin p) ∧
      x.val % 2 = leNat b off 32 >>> 255 := by
  have hP := decodePoint_proper h
  have hn := leNat_lt b off 32
  have hsb : leNat b off 32 >>> 255 < 2 := by
    rw [Nat.shiftRight_eq_div_pow]; exact Nat.div_lt_of_lt_mul (by rw [show 2 ^ 255 * 2 = 2 ^ (8 * 32) by decide]; exact hn)
  have hyv := (ofNat_spec (x := leNat b off 32 % 2 ^ 255) (Nat.mod_lt _ (by decide)))
  unfold decodePoint at h
  dsimp only at h
  split at h
  · cases h
  · rename_i hlt
    refine ⟨Nat.lt_of_not_le hlt, ?_⟩
    split at h
    · cases h
    · rename_i r hr
      have hrc := recoverX_carried hyv.1 hr
      unfold signed at h
      split at h
      · cases h
      · rename_i hz
        have hQ := h
        rw [← Option.some.inj hQ] at hP ⊢
        refine ⟨((if (r.toNat % 2 == leNat b off 32 >>> 255) = true then r else Fe.zero.sub r).toNat : Fin p),
          ⟨hP, ?_, ?_⟩, ?_⟩ <;> dsimp only
        · rw [val_one]; exact mul_oneR _
        · rw [val_one, hyv.2, fin_cast_mod]; exact mul_oneR _
        · rw [val_cast, Nat.mod_eq_of_lt (toNat_lt _)]
          simp only [Bool.and_eq_true, beq_iff_eq, not_and] at hz
          split
          · rename_i hp; exact beq_iff_eq.mp hp
          · rename_i hp
            have hp : r.toNat % 2 ≠ leNat b off 32 >>> 255 := fun e => hp (beq_iff_eq.mpr e)
            rw [sub_toNat zero_carried hrc, zero_toNat, Nat.zero_add]
            have hr := toNat_lt r
            have q := neg_parity (R := (p - r.toNat + 0) % p) p_odd hr rfl
            rw [Nat.add_zero] at q
            omega

/-- **Decode accepts every RFC encoding**: for `y = n mod 2^255 < p` and any `x` on the curve with the sign
bit's parity, `decodePoint` returns a point naming `(x, y)`. -/
theorem decodePoint_some {b : ByteArray} {off : Nat} {x : Fin p} (hy : leNat b off 32 % 2 ^ 255 < p)
    (hc : ((leNat b off 32 % 2 ^ 255 : Nat) : Fin p) * ((leNat b off 32 % 2 ^ 255 : Nat) : Fin p) - x * x =
      1 + (d.toNat : Fin p) * (x * x) * (((leNat b off 32 % 2 ^ 255 : Nat) : Fin p) * ((leNat b off 32 % 2 ^ 255 : Nat) : Fin p)))
    (hs : x.val % 2 = leNat b off 32 >>> 255) :
    ∃ Q, decodePoint b off = some Q ∧ Q.Affine x ((leNat b off 32 % 2 ^ 255 : Nat) : Fin p) := by
  have hyv := (ofNat_spec (x := leNat b off 32 % 2 ^ 255) (Nat.mod_lt _ (by decide)))
  have yv : ((Fe.ofNat (leNat b off 32 % 2 ^ 255)).toNat : Fin p) = ((leNat b off 32 % 2 ^ 255 : Nat) : Fin p) := by
    rw [hyv.2, fin_cast_mod]
  rw [← yv] at hc
  obtain ⟨r, hr, hrx⟩ := recoverX_root hyv.1 hc
  obtain ⟨Q, hQ, ex, ey⟩ := signed_some (y := Fe.ofNat (leNat b off 32 % 2 ^ 255)) hrx (recoverX_carried hyv.1 hr) hs
  have hd : decodePoint b off = some Q := by
    unfold decodePoint
    dsimp only
    rw [if_neg (Nat.not_le.mpr hy), hr]
    exact hQ
  rw [yv] at ey
  exact ⟨Q, hd, decodePoint_proper hd, ex, ey⟩

end Nanodregg.Codec.Ed25519
