/-!
# Codec.Prime — modular exponentiation, for primality certificates (CODEC-23)

`powMod b e m n` is `b ^ e % m` for `e < 2 ^ n`, by square-and-multiply. It is structural on `n`, so the
kernel reduces it on literals: a Pratt certificate for the Ed25519 field prime `2^255 − 19` checks by
`decide +kernel` (`Codec.Proofs.Prime`).
-/

namespace Nanodregg.Codec.Prime

/-- `b ^ e % m` for `e < 2 ^ n`: square-and-multiply from bit `n - 1` down. -/
def powMod (b e m : Nat) : (n : Nat) → Nat
  | 0 => 1 % m
  | n + 1 =>
    let r := powMod b (e >>> 1) m n
    if e % 2 = 1 then r * r % m * b % m else r * r % m

end Nanodregg.Codec.Prime
