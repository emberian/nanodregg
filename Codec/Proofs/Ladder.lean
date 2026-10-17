import Codec.Proofs.Group

/-!
# The ladder is scalar multiplication, and `verify` is the RFC 8032 equation (CODEC-23 part 3)

`[m] P` is `Nat.repeat (·.add P) m Point.zero`: `m` deployed additions of `P` to the identity (no new
definition; the spec is the deployed `add`). On it, with the group laws of `Codec.Proofs.Group`:

* `mul2_spec`: for proper `P`, `Q` and `PQ` projectively equal to `P.add Q`, and `a, b < 2^n`,
  `Point.mul2 P Q PQ a b n` is `[a] P + [b] Q` (Shamir's ladder, one doubling per bit). The general form is
  `ladder_spec`: the ladder computes `[a mod 2^n] P + [b mod 2^n] Q`.
* `verify_iff`: `verify pk msg sig = true` exactly when `pk` is 32 bytes, `sig` 64, `S < L`, both points
  decode, and `[8][S]B = [8]R + [8][k]A` projectively, `k = SHA-512(R ‖ A ‖ msg) mod L` — RFC 8032
  §5.1.7's cofactored check, read as the group equation it states.
* Tooth: `mul2_needs_bound` — with `n = 0` the ladder returns the identity, which is not `[1] B`, so the
  bound on the scalars is load-bearing.
-/

namespace Nanodregg.Codec.Ed25519

/-! ## `[m] P` -/

theorem rep_proper {P : Point} (hP : P.Proper) : ∀ m, (Nat.repeat (·.add P) m Point.zero).Proper
  | 0 => point_zero_proper
  | m + 1 => point_add_proper (rep_proper hP m) hP

theorem rep_add {P : Point} (hP : P.Proper) : ∀ m k, Point.Same (Nat.repeat (·.add P) (m + k) Point.zero)
    ((Nat.repeat (·.add P) m Point.zero).add (Nat.repeat (·.add P) k Point.zero))
  | m, 0 => same_symm (same_add_zero (rep_proper hP m))
  | m, k + 1 => same_trans (same_add_left (rep_add hP m k) hP)
      (same_add_assoc (rep_proper hP m) (rep_proper hP k) hP)

theorem rep_congr {P Q : Point} (h : Point.Same P Q) : ∀ m, Point.Same (Nat.repeat (·.add P) m Point.zero)
    (Nat.repeat (·.add Q) m Point.zero) := by
  intro m
  induction m with
  | zero => simp only [Nat.repeat]; exact same_refl point_zero_proper
  | succ m ih =>
    simp only [Nat.repeat]
    exact same_trans (same_add_left ih h.left) (same_add_right (rep_proper h.right m) h)

theorem rep_zero : ∀ m, Point.Same (Nat.repeat (·.add Point.zero) m Point.zero) Point.zero
  | 0 => same_refl point_zero_proper
  | m + 1 => same_trans (same_add_zero (rep_proper point_zero_proper m)) (rep_zero m)

theorem rep_one {P : Point} (hP : P.Proper) : Point.Same (Nat.repeat (·.add P) 1 Point.zero) P := by
  simp only [Nat.repeat]
  exact same_trans (same_add_comm point_zero_proper hP) (same_add_zero hP)

theorem same_double_congr {P Q : Point} (h : Point.Same P Q) : Point.Same P.double Q.double :=
  same_trans (same_double h.left) (same_trans (same_add_left h h.left)
    (same_trans (same_add_right h.right h) (same_symm (same_double h.right))))

/-- `(A + B) + (C + D) = (A + C) + (B + D)`. -/
theorem same_interchange {A B C D : Point} (hA : A.Proper) (hB : B.Proper) (hC : C.Proper) (hD : D.Proper) :
    Point.Same ((A.add B).add (C.add D)) ((A.add C).add (B.add D)) := by
  have hCD := point_add_proper hC hD
  have hBD := point_add_proper hB hD
  have s1 := same_add_assoc hA hB hCD
  have s2 := same_symm (same_add_assoc hB hC hD)
  have s3 := same_add_left (same_add_comm hB hC) hD
  have s4 := same_add_assoc hC hB hD
  have s5 := same_add_right hA (same_trans s2 (same_trans s3 s4))
  have s6 := same_symm (same_add_assoc hA hC hBD)
  exact same_trans s1 (same_trans s5 s6)

theorem rep_distrib {P Q : Point} (hP : P.Proper) (hQ : Q.Proper) : ∀ m,
    Point.Same (Nat.repeat (·.add (P.add Q)) m Point.zero)
      ((Nat.repeat (·.add P) m Point.zero).add (Nat.repeat (·.add Q) m Point.zero)) := by
  intro m
  induction m with
  | zero =>
    simp only [Nat.repeat]
    exact same_symm (same_add_zero point_zero_proper)
  | succ m ih =>
    simp only [Nat.repeat]
    exact same_trans (same_add_left ih (point_add_proper hP hQ))
      (same_interchange (rep_proper hP m) (rep_proper hQ m) hP hQ)

/-- `[8] X` is three doublings. -/
theorem same_d3 {X : Point} (hX : X.Proper) :
    Point.Same X.double.double.double (Nat.repeat (·.add X) 8 Point.zero) := by
  have dr : ∀ m, Point.Same (Nat.repeat (·.add X) m Point.zero).double (Nat.repeat (·.add X) (m + m) Point.zero) :=
    fun m => same_trans (same_double (rep_proper hX m)) (same_symm (rep_add hX m m))
  have d1 : Point.Same X.double (Nat.repeat (·.add X) 2 Point.zero) :=
    same_trans (same_double_congr (same_symm (rep_one hX))) (dr 1)
  have d2 : Point.Same X.double.double (Nat.repeat (·.add X) 4 Point.zero) :=
    same_trans (same_double_congr d1) (dr 2)
  exact same_trans (same_double_congr d2) (dr 4)

/-! ## The ladder -/

private theorem low_bit (a n : Nat) : a % 2 ^ (n + 1) = (a >>> 1) % 2 ^ n + (a >>> 1) % 2 ^ n + a % 2 := by
  rw [Nat.shiftRight_eq_div_pow, Nat.pow_one, Nat.pow_succ, Nat.mul_comm, Nat.mod_mul]
  omega

/-- The doubling step on `[a'] P + [b'] Q`. -/
theorem same_double_sum {P Q L : Point} (hP : P.Proper) (hQ : Q.Proper) {a' b' : Nat}
    (h : Point.Same L ((Nat.repeat (·.add P) a' Point.zero).add (Nat.repeat (·.add Q) b' Point.zero))) :
    Point.Same L.double
      ((Nat.repeat (·.add P) (a' + a') Point.zero).add (Nat.repeat (·.add Q) (b' + b') Point.zero)) := by
  have hA := rep_proper hP a'
  have hB := rep_proper hQ b'
  have s1 := same_trans (same_double_congr h) (same_double (point_add_proper hA hB))
  have s2 := same_interchange hA hB hA hB
  have s3 := same_trans (same_add_left (same_symm (rep_add hP a' a')) (point_add_proper hB hB))
    (same_add_right (rep_proper hP (a' + a')) (same_symm (rep_add hQ b' b')))
  exact same_trans s1 (same_trans s2 s3)

/-- The ladder from the identity computes `[a mod 2^n] P + [b mod 2^n] Q`. -/
theorem ladder_spec {P Q PQ : Point} (hP : P.Proper) (hQ : Q.Proper) (hPQ : Point.Same PQ (P.add Q)) :
    ∀ (a b n : Nat), Point.Same (Point.ladder P Q PQ Point.zero a b n)
      ((Nat.repeat (·.add P) (a % 2 ^ n) Point.zero).add (Nat.repeat (·.add Q) (b % 2 ^ n) Point.zero))
  | a, b, 0 => by
    rw [Nat.pow_zero, Nat.mod_one, Nat.mod_one]
    exact same_symm (same_add_zero point_zero_proper)
  | a, b, n + 1 => by
    rw [low_bit a n, low_bit b n]
    have hd := same_double_sum hP hQ (ladder_spec hP hQ hPQ (a >>> 1) (b >>> 1) n)
    show Point.Same (Point.step P Q PQ (Point.ladder P Q PQ Point.zero (a >>> 1) (b >>> 1) n) a b) _
    generalize Point.ladder P Q PQ Point.zero (a >>> 1) (b >>> 1) n = Lr at hd ⊢
    generalize (a >>> 1) % 2 ^ n = a' at hd ⊢
    generalize (b >>> 1) % 2 ^ n = b' at hd ⊢
    have hA := rep_proper hP (a' + a')
    have hB := rep_proper hQ (b' + b')
    unfold Point.step
    rcases Nat.mod_two_eq_zero_or_one a with ha | ha <;> rcases Nat.mod_two_eq_zero_or_one b with hb | hb <;>
      simp only [Nat.and_one_is_mod, ha, hb, Nat.add_zero, Nat.repeat]
    · exact hd
    · exact same_trans (same_add_left hd hQ) (same_add_assoc hA hB hQ)
    · exact same_trans (same_add_left hd hP) (same_trans (same_add_assoc hA hB hP)
        (same_trans (same_add_right hA (same_add_comm hB hP)) (same_symm (same_add_assoc hA hP hB))))
    · exact same_trans (same_trans (same_add_left hd hPQ.left) (same_add_right (point_add_proper hA hB) hPQ))
        (same_interchange hA hB hP hQ)

/-- **Shamir's ladder is `[a] P + [b] Q`** for scalars below `2^n`. -/
theorem mul2_spec {P Q PQ : Point} (hP : P.Proper) (hQ : Q.Proper) (hPQ : Point.Same PQ (P.add Q))
    {a b n : Nat} (ha : a < 2 ^ n) (hb : b < 2 ^ n) :
    Point.Same (Point.mul2 P Q PQ a b n)
      ((Nat.repeat (·.add P) a Point.zero).add (Nat.repeat (·.add Q) b Point.zero)) := by
  have h := ladder_spec hP hQ hPQ a b n
  rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h

/-! ## `verify` is the RFC equation -/

theorem same_congr_iff {X X' Y Y' : Point} (h1 : Point.Same X X') (h2 : Point.Same Y Y') :
    Point.Same X Y ↔ Point.Same X' Y' :=
  ⟨fun h => same_trans (same_symm h1) (same_trans h h2), fun h => same_trans h1 (same_trans h (same_symm h2))⟩

/-- Cancellation: if `V + W = 0`, then `U + V = R ↔ U = R + W`. -/
theorem same_cancel {U V W S : Point} (hU : U.Proper) (hV : V.Proper) (hW : W.Proper) (hS : S.Proper)
    (hVW : Point.Same (V.add W) Point.zero) : Point.Same (U.add V) S ↔ Point.Same U (S.add W) := by
  constructor
  · intro h
    exact same_symm (same_trans (same_add_left (same_symm h) hW) (same_trans (same_add_assoc hU hV hW)
      (same_trans (same_add_right hU hVW) (same_add_zero hU))))
  · intro h
    exact same_trans (same_add_left h hV) (same_trans (same_add_assoc hS hW hV)
      (same_trans (same_add_right hS (same_trans (same_add_comm hW hV) hVW)) (same_add_zero hS)))

/-- The core of `verify`: the cofactored projective check on `[S]B + [k](−A)` is the group equation
`[8][S]B = [8]R + [8][k]A`. -/
theorem rfc_iff {A R : Point} (hA : A.Proper) (hR : R.Proper) {S k : Nat} (hS : S < 2 ^ 253)
    (hk : k < 2 ^ 253) :
    (Point.mul2 B A.neg (B.add A.neg) S k 253).double.double.double.eq R.double.double.double = true ↔
      Point.Same (Nat.repeat (·.add (Nat.repeat (·.add B) S Point.zero)) 8 Point.zero)
        ((Nat.repeat (·.add R) 8 Point.zero).add
          (Nat.repeat (·.add (Nat.repeat (·.add A) k Point.zero)) 8 Point.zero)) := by
  have hN := point_neg_proper hA
  have hBN := point_add_proper B_proper hN
  have hM := mul2_proper B_proper hN hBN S k 253
  have m := mul2_spec B_proper hN (same_refl hBN) hS hk
  have p3 : ∀ {X : Point}, X.Proper → X.double.double.double.Proper := fun h =>
    point_double_proper (point_double_proper (point_double_proper h))
  have e : (Point.mul2 B A.neg (B.add A.neg) S k 253).double.double.double.eq R.double.double.double = true ↔
      Point.Same (Point.mul2 B A.neg (B.add A.neg) S k 253).double.double.double R.double.double.double :=
    ⟨fun h => ⟨p3 hM, p3 hR, h⟩, fun h => h.eq⟩
  have hSB := rep_proper B_proper S
  have hkN := rep_proper hN k
  have hkA := rep_proper hA k
  have c1 := same_trans (same_d3 hM) (same_trans (rep_congr m 8) (rep_distrib hSB hkN 8))
  have c2 := same_d3 hR
  have hVW := same_trans (same_symm (rep_distrib hkN hkA 8))
    (same_trans (rep_congr (same_symm (rep_distrib hN hA k)) 8)
      (same_trans (rep_congr (rep_congr (same_neg_add hA) k) 8)
        (same_trans (rep_congr (rep_zero k) 8) (rep_zero 8))))
  rw [e, same_congr_iff c1 c2]
  exact same_cancel (rep_proper hSB 8) (rep_proper hkN 8) (rep_proper hkA 8) (rep_proper hR 8) hVW

theorem L_lt : L < 2 ^ 253 := by decide

/-- **`verify` is RFC 8032 §5.1.7's cofactored equation**: it accepts exactly when the key is 32 bytes,
the signature 64, `S < L`, both points decode, and `[8][S]B = [8]R + [8][k]A` with
`k = SHA-512(R ‖ A ‖ msg) mod L`. -/
theorem verify_iff (pk msg sig : ByteArray) :
    verify pk msg sig = true ↔ pk.size = 32 ∧ sig.size = 64 ∧ leNat sig 32 32 < L ∧
      ∃ A R, decodePoint pk 0 = some A ∧ decodePoint sig 0 = some R ∧
        Point.Same (Nat.repeat (·.add (Nat.repeat (·.add B) (leNat sig 32 32) Point.zero)) 8 Point.zero)
          ((Nat.repeat (·.add R) 8 Point.zero).add (Nat.repeat (·.add (Nat.repeat (·.add A)
            (leNat (Sha512.hash (sig.extract 0 32 ++ pk ++ msg)).val 0 64 % L) Point.zero)) 8 Point.zero)) := by
  unfold verify
  split
  · rename_i h
    simp only [Bool.false_eq_true, false_iff]
    rintro ⟨h1, h2, -⟩
    simp [h1, h2] at h
  · rename_i h
    have hs : pk.size = 32 ∧ sig.size = 64 := by simpa using h
    dsimp only
    split
    · rename_i hS
      simp only [Bool.false_eq_true, false_iff]
      rintro ⟨-, -, hl, -⟩
      omega
    · rename_i hS
      split
      · rename_i A R hA hR
        rw [rfc_iff (decodePoint_proper hA) (decodePoint_proper hR) (Nat.lt_trans (by omega) L_lt)
          (Nat.lt_trans (Nat.mod_lt _ (by decide)) L_lt)]
        constructor
        · intro e
          exact ⟨hs.1, hs.2, by omega, A, R, hA, hR, e⟩
        · rintro ⟨-, -, -, A', R', hA', hR', e⟩
          rw [hA] at hA'; rw [hR] at hR'
          cases hA'; cases hR'
          exact e
      · rename_i hn
        simp only [Bool.false_eq_true, false_iff]
        rintro ⟨-, -, -, A, R, hA, hR, -⟩
        exact hn A R hA hR

/-! ## The tooth -/

theorem zero_mulR {R : Type} [Lean.Grind.CommRing R] (z : R) : 0 * z = 0 := by grind

/-- The scalar bound is load-bearing: with `n = 0` the ladder returns the identity, which is not
`[1] B + [0] B` (`B`'s `x` is not 0). -/
theorem mul2_needs_bound :
    ¬ Point.Same (Point.mul2 B B (B.add B) 1 0 0)
      ((Nat.repeat (·.add B) 1 Point.zero).add (Nat.repeat (·.add B) 0 Point.zero)) := by
  intro h
  have s : Point.Same Point.zero B :=
    same_trans h (same_trans (same_add_zero (rep_proper B_proper 1)) (rep_one B_proper))
  have hx := (same_affine s zero_affine).hx
  have bx : B.X.toNat = 15112221349535400772501151409588531511454012693041857206046113283949847762202 % p := by
    unfold B; dsimp only; exact (ofNat_spec (by decide +kernel)).2
  rw [bx, zero_mulR] at hx
  exact absurd hx (by decide +kernel)

end Nanodregg.Codec.Ed25519
