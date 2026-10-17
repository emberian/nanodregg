import Codec.Digest
import Codec.Stream

/-!
# Hash — Keccak-f[1600], SHA3-256, cSHAKE256 and KMAC256 (FIPS 202, NIST SP 800-185)

The one hash family. `Hash.digest domain msg` is cSHAKE256 with `domain` as the customization
string: every digest the system forms is domain-separated by construction, because SP 800-185
encodes the customization with its length (`encodeString`), so no domain is a prefix of another.
`Hash.mac key domain msg` is KMAC256 with a 32-byte key: the Host's log and base seal.

The permutation works on 25 unboxed `UInt64` lanes of a structure, one round unrolled (generated from
the FIPS 202 ρ and π tables): no array access can fail, no lane is boxed, and there is no `partial def`. Every loop is structural on a block count. The conformance
vectors (FIPS 202 and SP 800-185 samples) are theorems in `Codec.Proofs.Hash`.
-/

namespace Nanodregg.Codec.Hash

def roundConstants : Vector UInt64 24 := #v[
  0x0000000000000001, 0x0000000000008082, 0x800000000000808a, 0x8000000080008000,
  0x000000000000808b, 0x0000000080000001, 0x8000000080008081, 0x8000000000008009,
  0x000000000000008a, 0x0000000000000088, 0x0000000080008009, 0x000000008000000a,
  0x000000008000808b, 0x800000000000008b, 0x8000000000008089, 0x8000000000008003,
  0x8000000000008002, 0x8000000000000080, 0x000000000000800a, 0x800000008000000a,
  0x8000000080008081, 0x8000000000008080, 0x0000000080000001, 0x8000000080008008]

@[inline] def rotl (v n : UInt64) : UInt64 := (v <<< n) ||| (v >>> (64 - n))

/-- The Keccak state: 25 unboxed lanes, lane `x + 5 y` is `a<x+5y>`. -/
structure State where
  a0 : UInt64
  a1 : UInt64
  a2 : UInt64
  a3 : UInt64
  a4 : UInt64
  a5 : UInt64
  a6 : UInt64
  a7 : UInt64
  a8 : UInt64
  a9 : UInt64
  a10 : UInt64
  a11 : UInt64
  a12 : UInt64
  a13 : UInt64
  a14 : UInt64
  a15 : UInt64
  a16 : UInt64
  a17 : UInt64
  a18 : UInt64
  a19 : UInt64
  a20 : UInt64
  a21 : UInt64
  a22 : UInt64
  a23 : UInt64
  a24 : UInt64

def State.zero : State := ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

/-- Lane `i`. -/
def State.lane (s : State) : Fin 25 → UInt64
  | ⟨0, _⟩ => s.a0
  | ⟨1, _⟩ => s.a1
  | ⟨2, _⟩ => s.a2
  | ⟨3, _⟩ => s.a3
  | ⟨4, _⟩ => s.a4
  | ⟨5, _⟩ => s.a5
  | ⟨6, _⟩ => s.a6
  | ⟨7, _⟩ => s.a7
  | ⟨8, _⟩ => s.a8
  | ⟨9, _⟩ => s.a9
  | ⟨10, _⟩ => s.a10
  | ⟨11, _⟩ => s.a11
  | ⟨12, _⟩ => s.a12
  | ⟨13, _⟩ => s.a13
  | ⟨14, _⟩ => s.a14
  | ⟨15, _⟩ => s.a15
  | ⟨16, _⟩ => s.a16
  | ⟨17, _⟩ => s.a17
  | ⟨18, _⟩ => s.a18
  | ⟨19, _⟩ => s.a19
  | ⟨20, _⟩ => s.a20
  | ⟨21, _⟩ => s.a21
  | ⟨22, _⟩ => s.a22
  | ⟨23, _⟩ => s.a23
  | ⟨24, _⟩ => s.a24
  | ⟨n + 25, h⟩ => absurd h (by omega)

/-- One round: θ, ρ and π, χ, ι, unrolled over named lanes. -/
@[inline] def round (s : State) (rc : UInt64) : State :=
  let ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24⟩ := s
  let c0 := a0 ^^^ a5 ^^^ a10 ^^^ a15 ^^^ a20
  let c1 := a1 ^^^ a6 ^^^ a11 ^^^ a16 ^^^ a21
  let c2 := a2 ^^^ a7 ^^^ a12 ^^^ a17 ^^^ a22
  let c3 := a3 ^^^ a8 ^^^ a13 ^^^ a18 ^^^ a23
  let c4 := a4 ^^^ a9 ^^^ a14 ^^^ a19 ^^^ a24
  let d0 := c4 ^^^ rotl c1 1
  let d1 := c0 ^^^ rotl c2 1
  let d2 := c1 ^^^ rotl c3 1
  let d3 := c2 ^^^ rotl c4 1
  let d4 := c3 ^^^ rotl c0 1
  let b0 := (a0 ^^^ d0)
  let b1 := rotl (a6 ^^^ d1) 44
  let b2 := rotl (a12 ^^^ d2) 43
  let b3 := rotl (a18 ^^^ d3) 21
  let b4 := rotl (a24 ^^^ d4) 14
  let b5 := rotl (a3 ^^^ d3) 28
  let b6 := rotl (a9 ^^^ d4) 20
  let b7 := rotl (a10 ^^^ d0) 3
  let b8 := rotl (a16 ^^^ d1) 45
  let b9 := rotl (a22 ^^^ d2) 61
  let b10 := rotl (a1 ^^^ d1) 1
  let b11 := rotl (a7 ^^^ d2) 6
  let b12 := rotl (a13 ^^^ d3) 25
  let b13 := rotl (a19 ^^^ d4) 8
  let b14 := rotl (a20 ^^^ d0) 18
  let b15 := rotl (a4 ^^^ d4) 27
  let b16 := rotl (a5 ^^^ d0) 36
  let b17 := rotl (a11 ^^^ d1) 10
  let b18 := rotl (a17 ^^^ d2) 15
  let b19 := rotl (a23 ^^^ d3) 56
  let b20 := rotl (a2 ^^^ d2) 62
  let b21 := rotl (a8 ^^^ d3) 55
  let b22 := rotl (a14 ^^^ d4) 39
  let b23 := rotl (a15 ^^^ d0) 41
  let b24 := rotl (a21 ^^^ d1) 2
  ⟨(b0 ^^^ (~~~b1 &&& b2)) ^^^ rc,
   b1 ^^^ (~~~b2 &&& b3),
   b2 ^^^ (~~~b3 &&& b4),
   b3 ^^^ (~~~b4 &&& b0),
   b4 ^^^ (~~~b0 &&& b1),
   b5 ^^^ (~~~b6 &&& b7),
   b6 ^^^ (~~~b7 &&& b8),
   b7 ^^^ (~~~b8 &&& b9),
   b8 ^^^ (~~~b9 &&& b5),
   b9 ^^^ (~~~b5 &&& b6),
   b10 ^^^ (~~~b11 &&& b12),
   b11 ^^^ (~~~b12 &&& b13),
   b12 ^^^ (~~~b13 &&& b14),
   b13 ^^^ (~~~b14 &&& b10),
   b14 ^^^ (~~~b10 &&& b11),
   b15 ^^^ (~~~b16 &&& b17),
   b16 ^^^ (~~~b17 &&& b18),
   b17 ^^^ (~~~b18 &&& b19),
   b18 ^^^ (~~~b19 &&& b15),
   b19 ^^^ (~~~b15 &&& b16),
   b20 ^^^ (~~~b21 &&& b22),
   b21 ^^^ (~~~b22 &&& b23),
   b22 ^^^ (~~~b23 &&& b24),
   b23 ^^^ (~~~b24 &&& b20),
   b24 ^^^ (~~~b20 &&& b21)⟩

/-- Keccak-f[1600]: 24 rounds. -/
def permute (s : State) : State := roundConstants.foldl round s

/-- The rate of cSHAKE256/SHA3-256/KMAC256, in bytes (capacity 512 bits). -/
abbrev rate : Nat := 136

/-- The little-endian lane at byte `off` of a block; `off + 8 ≤ m.size` holds at every call. -/
@[inline] def loadLane (m : ByteArray) (off : Nat) : UInt64 :=
  if h : off + 8 ≤ m.size then
    Stream.ofLE64 m[off] m[off + 1] m[off + 2] m[off + 3] m[off + 4] m[off + 5] m[off + 6] m[off + 7]
  else 0

/-- XOR one 136-byte block at `off` into the first 17 lanes, then permute. -/
def absorbBlock (s : State) (m : ByteArray) (off : Nat) : State :=
  permute ⟨s.a0 ^^^ loadLane m (off + 0),
    s.a1 ^^^ loadLane m (off + 8),
    s.a2 ^^^ loadLane m (off + 16),
    s.a3 ^^^ loadLane m (off + 24),
    s.a4 ^^^ loadLane m (off + 32),
    s.a5 ^^^ loadLane m (off + 40),
    s.a6 ^^^ loadLane m (off + 48),
    s.a7 ^^^ loadLane m (off + 56),
    s.a8 ^^^ loadLane m (off + 64),
    s.a9 ^^^ loadLane m (off + 72),
    s.a10 ^^^ loadLane m (off + 80),
    s.a11 ^^^ loadLane m (off + 88),
    s.a12 ^^^ loadLane m (off + 96),
    s.a13 ^^^ loadLane m (off + 104),
    s.a14 ^^^ loadLane m (off + 112),
    s.a15 ^^^ loadLane m (off + 120),
    s.a16 ^^^ loadLane m (off + 128),
    s.a17,
    s.a18,
    s.a19,
    s.a20,
    s.a21,
    s.a22,
    s.a23,
    s.a24⟩

/-- Absorb `n` whole blocks of `m` starting at `off`. -/
def absorb (m : ByteArray) : Nat → Nat → State → State
  | 0, _, s => s
  | n + 1, off, s => absorb m n (off + rate) (absorbBlock s m off)

/-- The final block: the bytes after the last whole block, the domain byte, `pad10*1`. -/
def lastBlock (msg : ByteArray) (dsByte : UInt8) : ByteArray :=
  let tail := msg.extract (msg.size / rate * rate) msg.size
  let body := (tail.push dsByte) ++ ⟨Array.replicate (rate - 1 - tail.size) 0⟩
  body.set! (rate - 1) (body[rate - 1]! ||| 0x80)

/-- Keccak[512](msg ‖ domain bits, L) for `L ≤ 136` output bytes: one squeeze. -/
def keccak (msg : ByteArray) (dsByte : UInt8) (L : Nat) (hL : L ≤ rate) : { b : ByteArray // b.size = L } :=
  let s := absorb msg (msg.size / rate) 0 State.zero
  let s := absorbBlock s (lastBlock msg dsByte) 0
  ⟨⟨Array.ofFn fun i : Fin L =>
    (s.lane ⟨i.val / 8, by have : L ≤ 136 := hL; omega⟩ >>> (8 * (i.val % 8)).toUInt64).toUInt8⟩,
   by simp [ByteArray.size]⟩

/-- The big-endian bytes of `x`, at least one (SP 800-185's `left_encode` body). -/
def natBytes (x : Nat) : ByteArray :=
  let n := x.log2 / 8 + 1
  ⟨Array.ofFn fun i : Fin n => (x >>> (8 * (n - 1 - i.val))).toUInt8⟩

def leftEncode (x : Nat) : ByteArray := (ByteArray.empty.push (natBytes x).size.toUInt8) ++ natBytes x
def rightEncode (x : Nat) : ByteArray := (natBytes x).push (natBytes x).size.toUInt8
def encodeString (s : ByteArray) : ByteArray := leftEncode (8 * s.size) ++ s
def bytepad (x : ByteArray) (w : Nat) : ByteArray :=
  let z := leftEncode w ++ x
  z ++ ⟨Array.replicate ((w - z.size % w) % w) 0⟩

def sha3_256 (msg : ByteArray) : ByteArray := (keccak msg 0x06 32 (by decide)).val

/-- cSHAKE256(X, L, N, S) for `L ≤ 136` bytes. -/
def cshake256 (name custom msg : ByteArray) (L : Nat) (hL : L ≤ rate) : { b : ByteArray // b.size = L } :=
  if name.isEmpty && custom.isEmpty then keccak msg 0x1F L hL
  else keccak (bytepad (encodeString name ++ encodeString custom) rate ++ msg) 0x04 L hL

/-- KMAC256(K, X, L, S) for `L ≤ 136` bytes. -/
def kmac256 (key msg : ByteArray) (L : Nat) (hL : L ≤ rate) (custom : ByteArray) : { b : ByteArray // b.size = L } :=
  cshake256 "KMAC".toUTF8 custom (bytepad (encodeString key) rate ++ msg ++ rightEncode (8 * L)) L hL

end Nanodregg.Codec.Hash

namespace Nanodregg.Codec

/-- The digest of `msg` in `domain`: cSHAKE256 with `domain` as its customization string. -/
def Hash.digest (domain : String) (msg : ByteArray) : Digest :=
  let h := Hash.cshake256 ByteArray.empty domain.toUTF8 msg 32 (by decide)
  ⟨h.val, h.property⟩

/-- KMAC256 under a 32-byte key, in `domain`. -/
def Hash.mac (key : Digest) (domain : String) (msg : ByteArray) : Digest :=
  let h := Hash.kmac256 key.bytes msg 32 (by decide) domain.toUTF8
  ⟨h.val, h.property⟩

end Nanodregg.Codec
