/-!
# Sha512 — SHA-512 (FIPS 180-4), for Ed25519 (RFC 8032)

Eight unboxed `UInt64` working variables in a structure; the 80-word schedule of one block is a
`Vector`; every loop is structural on a block or round count. Vectors: `Codec.Proofs.Sha512`.
-/

namespace Nanodregg.Codec.Sha512

def K : Vector UInt64 80 := #v[
  0x428a2f98d728ae22, 0x7137449123ef65cd, 0xb5c0fbcfec4d3b2f, 0xe9b5dba58189dbbc,
  0x3956c25bf348b538, 0x59f111f1b605d019, 0x923f82a4af194f9b, 0xab1c5ed5da6d8118,
  0xd807aa98a3030242, 0x12835b0145706fbe, 0x243185be4ee4b28c, 0x550c7dc3d5ffb4e2,
  0x72be5d74f27b896f, 0x80deb1fe3b1696b1, 0x9bdc06a725c71235, 0xc19bf174cf692694,
  0xe49b69c19ef14ad2, 0xefbe4786384f25e3, 0x0fc19dc68b8cd5b5, 0x240ca1cc77ac9c65,
  0x2de92c6f592b0275, 0x4a7484aa6ea6e483, 0x5cb0a9dcbd41fbd4, 0x76f988da831153b5,
  0x983e5152ee66dfab, 0xa831c66d2db43210, 0xb00327c898fb213f, 0xbf597fc7beef0ee4,
  0xc6e00bf33da88fc2, 0xd5a79147930aa725, 0x06ca6351e003826f, 0x142929670a0e6e70,
  0x27b70a8546d22ffc, 0x2e1b21385c26c926, 0x4d2c6dfc5ac42aed, 0x53380d139d95b3df,
  0x650a73548baf63de, 0x766a0abb3c77b2a8, 0x81c2c92e47edaee6, 0x92722c851482353b,
  0xa2bfe8a14cf10364, 0xa81a664bbc423001, 0xc24b8b70d0f89791, 0xc76c51a30654be30,
  0xd192e819d6ef5218, 0xd69906245565a910, 0xf40e35855771202a, 0x106aa07032bbd1b8,
  0x19a4c116b8d2d0c8, 0x1e376c085141ab53, 0x2748774cdf8eeb99, 0x34b0bcb5e19b48a8,
  0x391c0cb3c5c95a63, 0x4ed8aa4ae3418acb, 0x5b9cca4f7763e373, 0x682e6ff3d6b2b8a3,
  0x748f82ee5defb2fc, 0x78a5636f43172f60, 0x84c87814a1f0ab72, 0x8cc702081a6439ec,
  0x90befffa23631e28, 0xa4506cebde82bde9, 0xbef9a3f7b2c67915, 0xc67178f2e372532b,
  0xca273eceea26619c, 0xd186b8c721c0c207, 0xeada7dd6cde0eb1e, 0xf57d4f7fee6ed178,
  0x06f067aa72176fba, 0x0a637dc5a2c898a6, 0x113f9804bef90dae, 0x1b710b35131c471b,
  0x28db77f523047d84, 0x32caab7b40c72493, 0x3c9ebe0a15c9bebc, 0x431d67c49c100d4c,
  0x4cc5d4becb3e42b6, 0x597f299cfc657e2a, 0x5fcb6fab3ad6faec, 0x6c44198c4a475817]

structure H where
  a : UInt64
  b : UInt64
  c : UInt64
  d : UInt64
  e : UInt64
  f : UInt64
  g : UInt64
  h : UInt64

def H.init : H := ⟨0x6a09e667f3bcc908, 0xbb67ae8584caa73b, 0x3c6ef372fe94f82b, 0xa54ff53a5f1d36f1, 0x510e527fade682d1, 0x9b05688c2b3e6c1f, 0x1f83d9abfb41bd6b, 0x5be0cd19137e2179⟩

@[inline] def rotr (x : UInt64) (n : UInt64) : UInt64 := (x >>> n) ||| (x <<< (64 - n))

/-- The big-endian word at byte `off` of `m`; `off + 8 ≤ m.size` at every call. -/
@[inline] def word (m : ByteArray) (off : Nat) : UInt64 :=
  if h : off + 8 ≤ m.size then
    (m[off].toUInt64 <<< 56) ||| (m[off + 1].toUInt64 <<< 48) ||| (m[off + 2].toUInt64 <<< 40) |||
    (m[off + 3].toUInt64 <<< 32) ||| (m[off + 4].toUInt64 <<< 24) ||| (m[off + 5].toUInt64 <<< 16) |||
    (m[off + 6].toUInt64 <<< 8) ||| m[off + 7].toUInt64
  else 0

/-- The 80-word message schedule of the block at `off`. -/
def schedule (m : ByteArray) (off : Nat) : Array UInt64 :=
  let w := (List.range 16).foldl (fun a i => a.push (word m (off + 8 * i))) (Array.emptyWithCapacity 80)
  (List.range 64).foldl (fun w j =>
    let t := j + 16
    let x := w[t - 15]!
    let y := w[t - 2]!
    let s0 := rotr x 1 ^^^ rotr x 8 ^^^ (x >>> 7)
    let s1 := rotr y 19 ^^^ rotr y 61 ^^^ (y >>> 6)
    w.push (w[t - 16]! + s0 + w[t - 7]! + s1)) w

/-- Compress one block into the state. -/
def compress (s : H) (m : ByteArray) (off : Nat) : H :=
  let w := schedule m off
  let r := (List.finRange 80).foldl (fun (v : H) (i : Fin 80) =>
    let S1 := rotr v.e 14 ^^^ rotr v.e 18 ^^^ rotr v.e 41
    let ch := (v.e &&& v.f) ^^^ (~~~v.e &&& v.g)
    let t1 := v.h + S1 + ch + K[i] + w[i.val]!
    let S0 := rotr v.a 28 ^^^ rotr v.a 34 ^^^ rotr v.a 39
    let maj := (v.a &&& v.b) ^^^ (v.a &&& v.c) ^^^ (v.b &&& v.c)
    ⟨t1 + S0 + maj, v.a, v.b, v.c, v.d + t1, v.e, v.f, v.g⟩) s
  ⟨s.a + r.a, s.b + r.b, s.c + r.c, s.d + r.d, s.e + r.e, s.f + r.f, s.g + r.g, s.h + r.h⟩

def compressAll (m : ByteArray) : Nat → Nat → H → H
  | 0, _, s => s
  | n + 1, off, s => compressAll m n (off + 128) (compress s m off)

/-- `msg ‖ 0x80 ‖ 0* ‖ len·8 (128-bit big-endian)`, a whole number of 128-byte blocks. -/
def padded (msg : ByteArray) : ByteArray :=
  let zeros := (239 - msg.size % 128) % 128
  let bits := 8 * msg.size
  let len : ByteArray := ⟨Array.ofFn fun i : Fin 16 => (bits >>> (8 * (15 - i.val))).toUInt8⟩
  (msg.push 0x80) ++ ⟨Array.replicate zeros 0⟩ ++ len

/-- SHA-512: 64 bytes. -/
def hash (msg : ByteArray) : { b : ByteArray // b.size = 64 } :=
  let m := padded msg
  let s := compressAll m (m.size / 128) 0 H.init
  let ws : Vector UInt64 8 := #v[s.a, s.b, s.c, s.d, s.e, s.f, s.g, s.h]
  ⟨⟨Array.ofFn fun i : Fin 64 => (ws[i.val / 8] >>> (8 * (7 - (i.val % 8))).toUInt64).toUInt8⟩,
   by simp [ByteArray.size]⟩

end Nanodregg.Codec.Sha512
