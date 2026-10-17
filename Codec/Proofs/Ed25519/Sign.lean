import Codec.Proofs.Ed25519.Decode
import Codec.Proofs.Ed25519.Order

/-!
# Every signature `sign` makes verifies (CODEC-23 complete)

* `encode_affine`: `encodePoint P` writes the affine `(x, y)` that a proper `P` names (`Fe.inv` inverts `Z`).
* `decode_encode`: an honestly encoded proper point decodes to itself (projectively), whatever bytes follow
  it — the sign bit and the square root agree (`Codec.Proofs.Ed25519.Decode`).
* `baseMul_same`: `baseMul k` is `[k] B`; `rep_mul`, `rep_mod_L`: `[m n] P = [m][n] P` and, by `B_order`,
  `[m] B = [m mod L] B`.
* `sign_verifies`: `verify (publicKey seed) msg (sign seed msg) = true` for EVERY seed and message.
* Tooth `decode_flipped_sign` / `B_sign_bit_needed`: with the sign bit flipped, a point with `x ≠ 0` decodes to
  its negation, which is not the point — for `B` concretely — so the sign rule is load-bearing and
  `decode_encode` is not decode ignoring a bit.
-/

namespace Nanodregg.Codec.Ed25519

open Fin.NatCast

private theorem val_cast (a : Nat) : ((a : Fin p) : Nat) = a % p := rfl

theorem inv_carried {f : Fe} (hf : f.Carried) : f.inv.Carried := pow_carried hf _ _

/-! ## Encoding -/

/-- A proper point names the affine point `encodePoint` writes. -/
theorem encode_affine {P : Point} (hP : P.Proper) :
    P.Affine ((P.X.mul P.Z.inv).toNat : Fin p) ((P.Y.mul P.Z.inv).toNat : Fin p) := by
  have c := hP.on.carried
  have hz := inv_val c.Z hP.z
  refine ⟨hP, ?_, ?_⟩
  · rw [val_mul c.X (inv_carried c.Z)]; exact inv_coordR hz
  · rw [val_mul c.Y (inv_carried c.Z)]; exact inv_coordR hz

theorem encodePoint_eq (P : Point) : encodePoint P =
    le32Bytes ((P.Y.mul P.Z.inv).toNat + (P.X.mul P.Z.inv).toNat % 2 * 2 ^ 255) := rfl

theorem encodePoint_size (P : Point) : (encodePoint P).size = 32 := le32Bytes_size _

private theorem p_lt : p < 2 ^ 255 := by decide

private theorem enc_mod {y s : Nat} (hy : y < 2 ^ 255) : (y + s * 2 ^ 255) % 2 ^ 255 = y := by
  rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hy]

private theorem enc_shr {y s : Nat} (hy : y < 2 ^ 255) : (y + s * 2 ^ 255) >>> 255 = s := by
  rw [Nat.shiftRight_eq_div_pow, Nat.add_mul_div_right _ _ (by decide), Nat.div_eq_of_lt hy, Nat.zero_add]

private theorem enc_lt {y s : Nat} (hy : y < 2 ^ 255) (hs : s < 2) : y + s * 2 ^ 255 < 2 ^ 256 := by
  have : s * 2 ^ 255 ≤ 1 * 2 ^ 255 := Nat.mul_le_mul_right _ (by omega)
  have e : (2 : Nat) ^ 256 = 2 ^ 255 + 1 * 2 ^ 255 := by decide
  omega

/-- The 32 bytes `le32Bytes (y + s·2^255)` decode to `(x, y)` when `x` is on the curve with parity `s`. -/
theorem decode_le32 {x y : Fin p} {s : Nat} (rest : ByteArray) (hs : x.val % 2 = s)
    (hc : y * y - x * x = 1 + (d.toNat : Fin p) * (x * x) * (y * y)) :
    ∃ Q, decodePoint (le32Bytes (y.val + s * 2 ^ 255) ++ rest) 0 = some Q ∧ Q.Affine x y := by
  have hy : y.val < 2 ^ 255 := Nat.lt_trans y.isLt p_lt
  have hs2 : s < 2 := by rw [← hs]; exact Nat.mod_lt _ (by decide)
  have hn : leNat (le32Bytes (y.val + s * 2 ^ 255) ++ rest) 0 32 = y.val + s * 2 ^ 255 := by
    rw [leNat_append_left (by rw [le32Bytes_size]; omega), leNat_le32Bytes, Nat.mod_eq_of_lt (enc_lt hy hs2)]
  have hyv : (((y.val + s * 2 ^ 255) % 2 ^ 255 : Nat) : Fin p) = y := by rw [enc_mod hy, fin_cast_val]
  obtain ⟨Q, hQ, ha⟩ := decodePoint_some (b := le32Bytes (y.val + s * 2 ^ 255) ++ rest) (off := 0) (x := x)
    (by rw [hn, enc_mod hy]; exact y.isLt) (by rw [hn, hyv]; exact hc) (by rw [hn, enc_shr hy]; exact hs)
  rw [hn, hyv] at ha
  exact ⟨Q, hQ, ha⟩

/-- **decode ∘ encode**: an honestly encoded proper point decodes to itself, whatever bytes follow it. -/
theorem decode_encode {P : Point} (hP : P.Proper) (rest : ByteArray) :
    ∃ Q, decodePoint (encodePoint P ++ rest) 0 = some Q ∧ Point.Same Q P := by
  have ha := encode_affine hP
  have hv : ((((P.X.mul P.Z.inv).toNat : Nat) : Fin p)).val = (P.X.mul P.Z.inv).toNat := by
    rw [val_cast, Nat.mod_eq_of_lt (toNat_lt _)]
  have hw : ((((P.Y.mul P.Z.inv).toNat : Nat) : Fin p)).val = (P.Y.mul P.Z.inv).toNat := by
    rw [val_cast, Nat.mod_eq_of_lt (toNat_lt _)]
  obtain ⟨Q, hQ, hQa⟩ := decode_le32 (s := (P.X.mul P.Z.inv).toNat % 2) rest (by rw [hv]) (affine_curve ha)
  rw [hw] at hQ
  exact ⟨Q, hQ, affine_same hQa ha⟩

/-! ## Scalar multiples of `B` -/

theorem baseMul_proper (k : Nat) : (baseMul k).Proper :=
  mul2_proper B_proper B_proper (point_add_proper B_proper B_proper) k 0 256

/-- `baseMul k` is `[k] B`. -/
theorem baseMul_same {k : Nat} (hk : k < 2 ^ 256) :
    Point.Same (baseMul k) (Nat.repeat (·.add B) k Point.zero) := by
  have m := mul2_spec B_proper B_proper (same_refl (point_add_proper B_proper B_proper)) hk
    (show 0 < 2 ^ 256 by decide)
  rw [show Nat.repeat (·.add B) 0 Point.zero = Point.zero from rfl] at m
  exact same_trans m (same_add_zero (rep_proper B_proper k))

/-- `[m n] P = [m] [n] P`. -/
theorem rep_mul {P : Point} (hP : P.Proper) : ∀ m n, Point.Same (Nat.repeat (·.add P) (m * n) Point.zero)
    (Nat.repeat (·.add (Nat.repeat (·.add P) n Point.zero)) m Point.zero)
  | 0, n => by rw [Nat.zero_mul]; simp only [Nat.repeat]; exact same_refl point_zero_proper
  | m + 1, n => by
    have e := same_trans (rep_add hP (m * n) n) (same_add_left (rep_mul hP m n) (rep_proper hP n))
    rw [Nat.succ_mul]
    simp only [Nat.repeat] at e ⊢
    exact e

/-- `[q L + s] B = [s] B`. -/
theorem rep_qL (q s : Nat) : Point.Same (Nat.repeat (·.add B) (q * L + s) Point.zero)
    (Nat.repeat (·.add B) s Point.zero) := by
  have z : Point.Same (Nat.repeat (·.add B) (q * L) Point.zero) Point.zero :=
    same_trans (rep_mul B_proper q L) (same_trans (rep_congr B_order q) (rep_zero q))
  have hs := rep_proper B_proper s
  exact same_trans (rep_add B_proper (q * L) s) (same_trans (same_add_left z hs)
    (same_trans (same_add_comm point_zero_proper hs) (same_add_zero hs)))

/-- `[m] B = [m mod L] B`: the scalar is read mod the order of `B`. -/
theorem rep_mod_L (m : Nat) : Point.Same (Nat.repeat (·.add B) m Point.zero)
    (Nat.repeat (·.add B) (m % L) Point.zero) := by
  have h := rep_qL (m / L) (m % L)
  rwa [Nat.div_add_mod'] at h

/-! ## Signature correctness -/

private theorem expand_lt (seed : ByteArray) : (expand seed).1 < 2 ^ 255 := by
  unfold expand
  dsimp only
  have := Nat.mod_lt (leNat (Sha512.hash seed).val 0 32 - leNat (Sha512.hash seed).val 0 32 % 8)
    (show 0 < 2 ^ 254 by decide)
  have e : (2 : Nat) ^ 255 = 2 ^ 254 + 2 ^ 254 := by decide
  omega

private theorem L_lt256 : L < 2 ^ 256 := Nat.lt_trans L_lt (by decide)

/-- The group equation `verify` checks holds for `R = [r] B`, `A = [a] B`, `S = (r + k a) mod L`. -/
theorem rfc_holds {A R : Point} {a r k : Nat} (hA : Point.Same A (Nat.repeat (·.add B) a Point.zero))
    (hR : Point.Same R (Nat.repeat (·.add B) r Point.zero)) :
    Point.Same (Nat.repeat (·.add (Nat.repeat (·.add B) ((r + k * a) % L) Point.zero)) 8 Point.zero)
      ((Nat.repeat (·.add R) 8 Point.zero).add
        (Nat.repeat (·.add (Nat.repeat (·.add A) k Point.zero)) 8 Point.zero)) := by
  have hrB := rep_proper B_proper r
  have haB := rep_proper B_proper a
  have hkaB := rep_proper haB k
  have c1 := same_trans (same_add_left (rep_congr hR 8) (rep_proper (rep_proper hA.left k) 8))
    (same_add_right (rep_proper hrB 8) (rep_congr (rep_congr hA k) 8))
  have c2 := same_symm (rep_distrib hrB hkaB 8)
  have c3 := same_add_right hrB (same_symm (rep_mul B_proper k a))
  have c4 := same_symm (rep_add B_proper r (k * a))
  have c5 := rep_mod_L (r + k * a)
  exact same_symm (same_trans c1 (same_trans c2 (rep_congr (same_trans c3 (same_trans c4 c5)) 8)))

/-- **Signature correctness**: every signature `sign` makes verifies under the seed's public key, for every
seed and every message. -/
theorem sign_verifies (seed msg : ByteArray) : verify (publicKey seed) msg (sign seed msg) = true := by
  have ha := expand_lt seed
  unfold sign publicKey
  generalize expand seed = E at ha ⊢
  obtain ⟨a, pre⟩ := E
  dsimp only at ha ⊢
  generalize hr : leNat (Sha512.hash (pre ++ msg)).val 0 64 % L = r
  generalize hk : leNat (Sha512.hash (encodePoint (baseMul r) ++ encodePoint (baseMul a) ++ msg)).val 0 64 % L = k
  have hrL : r < L := by rw [← hr]; exact Nat.mod_lt _ (by decide)
  have hsL : (r + k * a) % L < L := Nat.mod_lt _ (by decide)
  have hRs := encodePoint_size (baseMul r)
  have hS : leNat (encodePoint (baseMul r) ++ le32Bytes ((r + k * a) % L)) 32 32 = (r + k * a) % L := by
    have h := leNat_append_right (a := encodePoint (baseMul r)) (b := le32Bytes ((r + k * a) % L)) (k := 32)
      (by rw [le32Bytes_size]; omega)
    rw [hRs] at h
    rw [h, leNat_le32Bytes, Nat.mod_eq_of_lt (Nat.lt_trans hsL L_lt256)]
  have hX : (encodePoint (baseMul r) ++ le32Bytes ((r + k * a) % L)).extract 0 32 = encodePoint (baseMul r) :=
    ByteArray.extract_append_eq_left hRs.symm
  obtain ⟨A, hA, sA⟩ := decode_encode (baseMul_proper a) ByteArray.empty
  rw [ByteArray.append_empty] at hA
  obtain ⟨R, hR, sR⟩ := decode_encode (baseMul_proper r) (le32Bytes ((r + k * a) % L))
  rw [verify_iff, hS, hX, hk]
  refine ⟨encodePoint_size _, by rw [ByteArray.size_append, hRs, le32Bytes_size], hsL, A, R, hA, hR, ?_⟩
  exact rfc_holds (same_trans sA (baseMul_same (Nat.lt_trans ha (by decide))))
    (same_trans sR (baseMul_same (Nat.lt_trans hrL L_lt256)))

/-! ## The tooth: the sign bit is load-bearing -/

section Ring
variable {R : Type} [Lean.Grind.CommRing R]

theorem neg_sqR (x : R) : (0 - x) * (0 - x) = x * x := by grind

theorem two_cancelR (inv : ∀ a : R, a ≠ 0 → ∃ b, a * b = 1) (h2 : (2 : R) ≠ 0) {x : R} (h : x = 0 - x) :
    x = 0 := by
  rcases domain_of_invR inv 2 x (by grind) with e | e
  · exact absurd e h2
  · exact e

end Ring

/-- With the sign bit flipped, a point with `x ≠ 0` decodes to its negation, which is not the point. -/
theorem decode_flipped_sign {P : Point} {x y : Fin p} (hP : P.Affine x y) (hx : x ≠ 0) (rest : ByteArray) :
    ∃ Q, decodePoint (le32Bytes (y.val + (1 - x.val % 2) * 2 ^ 255) ++ rest) 0 = some Q ∧ ¬ Point.Same Q P := by
  have hxv : x.val ≠ 0 := fun h => hx (Fin.ext h)
  have hneg : (0 - x).val % 2 = 1 - x.val % 2 := by
    rcases neg_parity p_odd x.isLt (Fin.val_sub 0 x) with ⟨h0, -⟩ | ⟨-, -, h2⟩
    · exact absurd h0 hxv
    · omega
  have hc := affine_curve hP
  rw [← neg_sqR x] at hc
  obtain ⟨Q, hQ, hQa⟩ := decode_le32 rest hneg hc
  refine ⟨Q, hQ, fun h => hx ?_⟩
  exact two_cancelR fin_inv fin_two_ne_zero (affine_unique hP (same_affine h hQa)).1

theorem B_affine : B.Affine (B.X.toNat : Fin p) (B.Y.toNat : Fin p) := by
  refine ⟨B_proper, ?_, ?_⟩ <;> (unfold B; dsimp only; rw [val_one]; exact mul_oneR _)

theorem B_x_ne_zero : (B.X.toNat : Fin p) ≠ 0 := by
  have bx : B.X.toNat = 15112221349535400772501151409588531511454012693041857206046113283949847762202 % p := by
    unfold B; dsimp only; exact (ofNat_spec (by decide +kernel)).2
  rw [bx]
  decide +kernel

/-- Tooth, concretely: `B` encoded with its sign bit flipped decodes, and not to `B`. -/
theorem B_sign_bit_needed : ∃ Q, decodePoint (le32Bytes ((B.Y.toNat : Fin p).val +
    (1 - (B.X.toNat : Fin p).val % 2) * 2 ^ 255)) 0 = some Q ∧ ¬ Point.Same Q B := by
  have h := decode_flipped_sign B_affine B_x_ne_zero ByteArray.empty
  rwa [ByteArray.append_empty] at h

end Nanodregg.Codec.Ed25519
