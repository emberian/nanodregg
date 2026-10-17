import Codec.Ed25519

/-!
# Staging the RFC 8032 checks, so the kernel never holds a whole verification at once

`decide +kernel` of a whole `verify` peaked at 9.2 GB in one declaration (CODEC-20, measured on
hbox). These lemmas cut the computation where its value is small: the double-scalar ladder is
`Point.ladder` from a given point, so 253 (or 256) bits are four chunks each started from the
previous chunk's result (`mul2_of_chunks`), and `verify_eq` names what `verify` reduces to once
the sizes, `S` and both decompressions are known. Each vector module then states its theorem
exactly as before and proves it through literal intermediate points, one chunk per declaration.
-/

namespace Nanodregg.Codec.Ed25519

/-- Running the ladder over `n + k` bits is running it over the top `n`, then the low `k`. -/
theorem ladder_add (P Q PQ R : Point) : ∀ (a b n k : Nat),
    Point.ladder P Q PQ R a b (n + k) =
      Point.ladder P Q PQ (Point.ladder P Q PQ R (a >>> k) (b >>> k) n) a b k
  | a, b, n, 0 => by simp [Point.ladder]
  | a, b, n, k + 1 => by
      have e : ∀ x : Nat, x >>> 1 >>> k = x >>> (k + 1) := fun x => by
        rw [← Nat.shiftRight_add, Nat.add_comm]
      rw [← Nat.add_assoc, Point.ladder, ladder_add P Q PQ R (a >>> 1) (b >>> 1) n k, e, e, Point.ladder]

/-- A 4-chunk ladder: the top `n` bits, then three chunks of 64. -/
theorem mul2_of_chunks {P Q PQ : Point} {a b n N : Nat} {R1 R2 R3 R4 : Point} (hN : N = n + 192)
    (h1 : Point.ladder P Q PQ Point.zero (a >>> 192) (b >>> 192) n = R1)
    (h2 : Point.ladder P Q PQ R1 (a >>> 128) (b >>> 128) 64 = R2)
    (h3 : Point.ladder P Q PQ R2 (a >>> 64) (b >>> 64) 64 = R3)
    (h4 : Point.ladder P Q PQ R3 a b 64 = R4) : Point.mul2 P Q PQ a b N = R4 := by
  rw [Point.mul2, hN, show n + 192 = n + 64 + 64 + 64 by omega, ladder_add, ladder_add, ladder_add]
  simp only [← Nat.shiftRight_add, Nat.reduceAdd]
  rw [h1, h2, h3, h4]

/-- What `verify` reduces to once the sizes, `S` and both decompressions are known. -/
theorem verify_eq {pk msg sig : ByteArray} {A R : Point} (hpk : pk.size = 32) (hsig : sig.size = 64)
    (hS : leNat sig 32 32 < L) (hA : decodePoint pk 0 = some A) (hR : decodePoint sig 0 = some R) :
    verify pk msg sig =
      (Point.mul2 B A.neg (B.add A.neg) (leNat sig 32 32)
        (leNat (Sha512.hash (sig.extract 0 32 ++ pk ++ msg)).val 0 64 % L) 253).double.double.double.eq
        R.double.double.double := by
  have hS' : ¬ L ≤ leNat sig 32 32 := Nat.not_le.mpr hS
  simp only [verify, hpk, hsig, hA, hR, hS', bne_self_eq_false, Bool.or_self, Bool.false_eq_true,
    if_false]

theorem publicKey_eq {seed : ByteArray} {a : Nat} {pre : ByteArray} (he : expand seed = (a, pre)) :
    publicKey seed = encodePoint (baseMul a) := by
  simp only [publicKey, he]

/-- What `sign` computes once `expand` is known, stated symbolically, so the kernel checks the
unfolding once for every seed instead of beside a concrete computation. -/
theorem sign_eq {seed msg : ByteArray} {a : Nat} {pre : ByteArray} (he : expand seed = (a, pre)) :
    sign seed msg =
      encodePoint (baseMul (leNat (Sha512.hash (pre ++ msg)).val 0 64 % L)) ++
        le32Bytes ((leNat (Sha512.hash (pre ++ msg)).val 0 64 % L +
          leNat (Sha512.hash (encodePoint (baseMul (leNat (Sha512.hash (pre ++ msg)).val 0 64 % L)) ++
            encodePoint (baseMul a) ++ msg)).val 0 64 % L * a) % L) := by
  simp only [sign, he]

end Nanodregg.Codec.Ed25519
