import Codec.Sha512

/-!
# Ed25519 — signature verification (RFC 8032 §5.1.7), cofactored

Field elements are ten unboxed `UInt64` limbs (radix 2^25.5). The product is generated
schoolbook arithmetic, folded by `2^255 ≡ 19`, and no intermediate exceeds 2^63. Points are
extended twisted-Edwards coordinates (RFC 8032 §5.1.4). Verification computes `[S]B - [k]A` in one
double-and-add pass (Shamir's trick) and checks `[8]([S]B - [k]A) = [8]R`. It refuses a
non-canonical `S` (≥ L), a point encoding with `y ≥ p`, and a point that does not decompress. Every
loop is structural on a bit count. RFC 8032 vectors: `Codec.Proofs.Ed25519.{Test1, Test2, Tampered}`.
-/

namespace Nanodregg.Codec.Ed25519

def p : Nat := 2 ^ 255 - 19
def L : Nat := 2 ^ 252 + 27742317777372353535851937790883648493

/-- A field element: ten unboxed limbs, limb `i` at bit `⌈25.5 i⌉` (26, 25, 26, … bits). Every
operation returns carried limbs (each below `2^26 + 2^7`), so any two may be multiplied. -/
structure Fe where
  l0 : UInt64
  l1 : UInt64
  l2 : UInt64
  l3 : UInt64
  l4 : UInt64
  l5 : UInt64
  l6 : UInt64
  l7 : UInt64
  l8 : UInt64
  l9 : UInt64
  deriving DecidableEq

/-- Propagate carries: every limb back below its width, the top carry folded in by `2^255 ≡ 19`. -/
@[inline] def Fe.carry (h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 : UInt64) : Fe :=
  let c0 := h0 >>> 26
  let h0 := h0 &&& 67108863
  let h1 := h1 + c0
  let c1 := h1 >>> 25
  let h1 := h1 &&& 33554431
  let h2 := h2 + c1
  let c2 := h2 >>> 26
  let h2 := h2 &&& 67108863
  let h3 := h3 + c2
  let c3 := h3 >>> 25
  let h3 := h3 &&& 33554431
  let h4 := h4 + c3
  let c4 := h4 >>> 26
  let h4 := h4 &&& 67108863
  let h5 := h5 + c4
  let c5 := h5 >>> 25
  let h5 := h5 &&& 33554431
  let h6 := h6 + c5
  let c6 := h6 >>> 26
  let h6 := h6 &&& 67108863
  let h7 := h7 + c6
  let c7 := h7 >>> 25
  let h7 := h7 &&& 33554431
  let h8 := h8 + c7
  let c8 := h8 >>> 26
  let h8 := h8 &&& 67108863
  let h9 := h9 + c8
  let c9 := h9 >>> 25
  let h9 := h9 &&& 33554431
  let h0 := h0 + 19 * c9
  let c := h0 >>> 26
  ⟨h0 &&& 67108863, h1 + c, h2, h3, h4, h5, h6, h7, h8, h9⟩

/-- Schoolbook product of ten limbs by ten, folded mod `2^255 - 19` (generated). -/
def Fe.mul (f g : Fe) : Fe :=
  let ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8, f9⟩ := f
  let ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9⟩ := g
  let h0 := f0 * g0 + 38 * f1 * g9 + 19 * f2 * g8 + 38 * f3 * g7 + 19 * f4 * g6 + 38 * f5 * g5 + 19 * f6 * g4 + 38 * f7 * g3 + 19 * f8 * g2 + 38 * f9 * g1
  let h1 := f0 * g1 + f1 * g0 + 19 * f2 * g9 + 19 * f3 * g8 + 19 * f4 * g7 + 19 * f5 * g6 + 19 * f6 * g5 + 19 * f7 * g4 + 19 * f8 * g3 + 19 * f9 * g2
  let h2 := f0 * g2 + 2 * f1 * g1 + f2 * g0 + 38 * f3 * g9 + 19 * f4 * g8 + 38 * f5 * g7 + 19 * f6 * g6 + 38 * f7 * g5 + 19 * f8 * g4 + 38 * f9 * g3
  let h3 := f0 * g3 + f1 * g2 + f2 * g1 + f3 * g0 + 19 * f4 * g9 + 19 * f5 * g8 + 19 * f6 * g7 + 19 * f7 * g6 + 19 * f8 * g5 + 19 * f9 * g4
  let h4 := f0 * g4 + 2 * f1 * g3 + f2 * g2 + 2 * f3 * g1 + f4 * g0 + 38 * f5 * g9 + 19 * f6 * g8 + 38 * f7 * g7 + 19 * f8 * g6 + 38 * f9 * g5
  let h5 := f0 * g5 + f1 * g4 + f2 * g3 + f3 * g2 + f4 * g1 + f5 * g0 + 19 * f6 * g9 + 19 * f7 * g8 + 19 * f8 * g7 + 19 * f9 * g6
  let h6 := f0 * g6 + 2 * f1 * g5 + f2 * g4 + 2 * f3 * g3 + f4 * g2 + 2 * f5 * g1 + f6 * g0 + 38 * f7 * g9 + 19 * f8 * g8 + 38 * f9 * g7
  let h7 := f0 * g7 + f1 * g6 + f2 * g5 + f3 * g4 + f4 * g3 + f5 * g2 + f6 * g1 + f7 * g0 + 19 * f8 * g9 + 19 * f9 * g8
  let h8 := f0 * g8 + 2 * f1 * g7 + f2 * g6 + 2 * f3 * g5 + f4 * g4 + 2 * f5 * g3 + f6 * g2 + 2 * f7 * g1 + f8 * g0 + 38 * f9 * g9
  let h9 := f0 * g9 + f1 * g8 + f2 * g7 + f3 * g6 + f4 * g5 + f5 * g4 + f6 * g3 + f7 * g2 + f8 * g1 + f9 * g0
  Fe.carry h0 h1 h2 h3 h4 h5 h6 h7 h8 h9

def Fe.add (f g : Fe) : Fe :=
  Fe.carry (f.l0 + g.l0) (f.l1 + g.l1) (f.l2 + g.l2) (f.l3 + g.l3) (f.l4 + g.l4) (f.l5 + g.l5) (f.l6 + g.l6) (f.l7 + g.l7) (f.l8 + g.l8) (f.l9 + g.l9)

/-- `f - g`, as `f + 4p - g` limb by limb (each limb of `4p` exceeds any carried limb of `g`). -/
def Fe.sub (f g : Fe) : Fe :=
  Fe.carry (f.l0 + 268435380 - g.l0) (f.l1 + 134217724 - g.l1) (f.l2 + 268435452 - g.l2) (f.l3 + 134217724 - g.l3) (f.l4 + 268435452 - g.l4) (f.l5 + 134217724 - g.l5) (f.l6 + 268435452 - g.l6) (f.l7 + 134217724 - g.l7) (f.l8 + 268435452 - g.l8) (f.l9 + 134217724 - g.l9)


/-- The limbs of `x < 2^255`. -/
def Fe.ofNat (x : Nat) : Fe :=
  ⟨(x % 2 ^ 26).toUInt64, ((x >>> 26) % 2 ^ 25).toUInt64, ((x >>> 51) % 2 ^ 26).toUInt64,
   ((x >>> 77) % 2 ^ 25).toUInt64, ((x >>> 102) % 2 ^ 26).toUInt64, ((x >>> 128) % 2 ^ 25).toUInt64,
   ((x >>> 153) % 2 ^ 26).toUInt64, ((x >>> 179) % 2 ^ 25).toUInt64, ((x >>> 204) % 2 ^ 26).toUInt64,
   ((x >>> 230) % 2 ^ 25).toUInt64⟩

/-- The canonical value in `[0, p)`. -/
def Fe.toNat (f : Fe) : Nat :=
  (f.l0.toNat + (f.l1.toNat <<< 26) + (f.l2.toNat <<< 51) + (f.l3.toNat <<< 77) + (f.l4.toNat <<< 102) +
    (f.l5.toNat <<< 128) + (f.l6.toNat <<< 153) + (f.l7.toNat <<< 179) + (f.l8.toNat <<< 204) +
    (f.l9.toNat <<< 230)) % p

def Fe.zero : Fe := Fe.ofNat 0
def Fe.one : Fe := Fe.ofNat 1
@[inline] def Fe.sq (f : Fe) : Fe := f.mul f
def Fe.eq (f g : Fe) : Bool := f.toNat == g.toNat

/-- `f ^ e` for `e < 2 ^ n`: square-and-multiply from bit `n - 1` down. -/
def Fe.pow (f : Fe) (e : Nat) : (n : Nat) → Fe
  | 0 => Fe.one
  | n + 1 =>
    let r := (Fe.pow f (e >>> 1) n).sq
    if e &&& 1 == 1 then r.mul f else r

def d : Fe := Fe.ofNat 37095705934669439343138083508754565189542113879843219016388785533085940283555
def d2 : Fe := Fe.ofNat (2 * 37095705934669439343138083508754565189542113879843219016388785533085940283555 % p)
def sqrtM1 : Fe := Fe.ofNat 19681161376707505956807079304988542015446066515923890162744021073123829784752

/-- A point in extended coordinates: `x = X/Z`, `y = Y/Z`, `x y = T/Z`. -/
structure Point where
  X : Fe
  Y : Fe
  Z : Fe
  T : Fe
  deriving DecidableEq

def Point.zero : Point := ⟨Fe.zero, Fe.one, Fe.one, Fe.zero⟩

/-- RFC 8032 §5.1.4 addition (complete for `a = -1`). -/
def Point.add (P Q : Point) : Point :=
  let A := (P.Y.sub P.X).mul (Q.Y.sub Q.X)
  let B := (P.Y.add P.X).mul (Q.Y.add Q.X)
  let C := (P.T.mul d2).mul Q.T
  let D := (P.Z.add P.Z).mul Q.Z
  let E := B.sub A
  let F := D.sub C
  let G := D.add C
  let H := B.add A
  ⟨E.mul F, G.mul H, F.mul G, E.mul H⟩

/-- RFC 8032 §5.1.4 doubling. -/
def Point.double (P : Point) : Point :=
  let A := P.X.sq
  let B := P.Y.sq
  let zz := P.Z.sq
  let C := zz.add zz
  let H := A.add B
  let E := H.sub (P.X.add P.Y).sq
  let G := A.sub B
  let F := C.add G
  ⟨E.mul F, G.mul H, F.mul G, E.mul H⟩

def Point.neg (P : Point) : Point := ⟨Fe.zero.sub P.X, P.Y, P.Z, Fe.zero.sub P.T⟩

/-- Projective equality. -/
def Point.eq (P Q : Point) : Bool := (P.X.mul Q.Z).eq (Q.X.mul P.Z) && (P.Y.mul Q.Z).eq (Q.Y.mul P.Z)

/-- One Shamir step: double `R`, then add `P`, `Q` or `P + Q` by the low bits of `a` and `b`. -/
def Point.step (P Q PQ R : Point) (a b : Nat) : Point :=
  let R := R.double
  match a &&& 1 == 1, b &&& 1 == 1 with
  | true, true => R.add PQ
  | true, false => R.add P
  | false, true => R.add Q
  | false, false => R

/-- From `R`, one `step` per bit of `a, b < 2 ^ n`, from bit `n - 1` down. -/
def Point.ladder (P Q PQ R : Point) (a b : Nat) : (n : Nat) → Point
  | 0 => R
  | n + 1 => Point.step P Q PQ (Point.ladder P Q PQ R (a >>> 1) (b >>> 1) n) a b

/-- `[a] P + [b] Q` for `a, b < 2 ^ n`, one doubling per bit (Shamir), with `PQ = P + Q`. -/
def Point.mul2 (P Q PQ : Point) (a b n : Nat) : Point := Point.ladder P Q PQ Point.zero a b n

/-- The base point B (RFC 8032 §5.1). -/
def B : Point :=
  let x := Fe.ofNat 15112221349535400772501151409588531511454012693041857206046113283949847762202
  let y := Fe.ofNat 46316835694926478169428394003475163141307993866256225615783033603165251855960
  ⟨x, y, Fe.one, x.mul y⟩

/-- The little-endian number of bytes `[off, off + n)`. -/
def leNat (b : ByteArray) (off n : Nat) : Nat :=
  (List.range n).foldr (fun i acc => acc * 256 + (b.get! (off + i)).toNat) 0

/-- The candidate root of `u/v` (RFC 8032 §5.1.3): `u v³ (u v⁷)^((p − 5)/8)`, given `v3 = v³`. -/
def candidateFrom (u v v3 : Fe) : Fe := (u.mul v3).mul ((u.mul (v3.sq.mul v)).pow ((p - 5) / 8) 252)

/-- `x` if `v x² = u`, `x √−1` if `v x² = −u`, otherwise no root. -/
def rootCheck (u v x : Fe) : Option Fe :=
  let vxx := v.mul x.sq
  if vxx.eq u then some x else if vxx.eq (Fe.zero.sub u) then some (x.mul sqrtM1) else none

/-- A square root of `u/v`, if one exists. -/
def sqrtRatio (u v : Fe) : Option Fe := rootCheck u v (candidateFrom u v (v.sq.mul v))

/-- The x of a point with this y: a root of `(y² − 1)/(d y² + 1)`, if one exists. -/
def recoverX (y : Fe) : Option Fe := sqrtRatio (y.sq.sub Fe.one) ((d.mul y.sq).add Fe.one)

/-- The point from a root `x`, the sign bit and `y`: refused when `x = 0` and the sign is 1. -/
def signed (x y : Fe) (sign : Nat) : Option Point :=
  if x.toNat == 0 && sign == 1 then none else
  let x := if x.toNat % 2 == sign then x else Fe.zero.sub x
  some ⟨x, y, Fe.one, x.mul y⟩

/-- RFC 8032 §5.1.3: decode a 32-byte point, or refuse. -/
def decodePoint (b : ByteArray) (off : Nat) : Option Point :=
  let n := leNat b off 32
  let yn := n % 2 ^ 255
  if yn ≥ p then none else
  let y := Fe.ofNat yn
  match recoverX y with
  | none => none
  | some x => signed x y (n >>> 255)

/-- An Ed25519 public key's size: what `verify` accepts as `pk` (`Codec.Ed25519.verify_pk_size`), and
the width of every key a client record holds (`Protocol.rotationLayout`). -/
def publicKeyBytes : Nat := 32

/-- RFC 8032 §5.1.7, cofactored: does `sig` sign `msg` under the 32-byte public key `pk`? Every
malformed input is `false`. -/
def verify (pk msg sig : ByteArray) : Bool :=
  if pk.size != 32 || sig.size != 64 then false else
  let S := leNat sig 32 32
  if S ≥ L then false else
  match decodePoint pk 0, decodePoint sig 0 with
  | some A, some R =>
    let h := (Sha512.hash (sig.extract 0 32 ++ pk ++ msg)).val
    let k := leNat h 0 64 % L
    let nA := A.neg
    let sbka := Point.mul2 B nA (B.add nA) S k 253
    sbka.double.double.double.eq R.double.double.double
  | _, _ => false

/-! ## Key derivation and signing (RFC 8032 §5.1.5–5.1.6)

Test tooling and the reference for custody: the simulation signs with these. The deployed
signer is custody's, in Rust, and nothing deployed calls `sign`. Not constant time. -/

def Fe.inv (f : Fe) : Fe := f.pow (p - 2) 255

/-- The 32 little-endian bytes of `n < 2^256`. -/
def le32Bytes (n : Nat) : ByteArray := ⟨Array.ofFn fun i : Fin 32 => ((n >>> (8 * i.val)) % 256).toUInt8⟩

/-- RFC 8032 §5.1.2: `y` little-endian with the sign of `x` in the top bit. -/
def encodePoint (P : Point) : ByteArray :=
  let zi := P.Z.inv
  let x := (P.X.mul zi).toNat
  let y := (P.Y.mul zi).toNat
  le32Bytes (y + (x % 2) * 2 ^ 255)

/-- `[k] B` for `k < 2^256`. -/
def baseMul (k : Nat) : Point := Point.mul2 B B (B.add B) k 0 256

/-- The secret scalar and the prefix of a 32-byte seed (§5.1.5). -/
def expand (seed : ByteArray) : Nat × ByteArray :=
  let h := (Sha512.hash seed).val
  let a := leNat h 0 32
  let a := (a - a % 8) % 2 ^ 254 + 2 ^ 254
  (a, h.extract 32 64)

/-- The public key of a 32-byte seed. -/
def publicKey (seed : ByteArray) : ByteArray := encodePoint (baseMul (expand seed).1)

/-- The RFC 8032 signature of `msg` under the 32-byte `seed`. -/
def sign (seed msg : ByteArray) : ByteArray :=
  let (a, pre) := expand seed
  let pk := encodePoint (baseMul a)
  let r := leNat (Sha512.hash (pre ++ msg)).val 0 64 % L
  let R := encodePoint (baseMul r)
  let k := leNat (Sha512.hash (R ++ pk ++ msg)).val 0 64 % L
  R ++ le32Bytes ((r + k * a) % L)

end Nanodregg.Codec.Ed25519
