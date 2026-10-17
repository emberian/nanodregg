import Codec.Stream

/-!
# Varint — LEB128 naturals, shortest form only

A natural below 2^32 as base-128 digits, least significant first, each byte's top bit set when
another byte follows: 0–127 is one byte, below 2^14 two, and at most five. A decoder refuses an
overlong spelling (a last byte of 0 after a continuation, which a shorter spelling would have
omitted), a sixth byte, and a value of 2^32 or more. So every value has exactly one spelling
(`Codec.Proofs.Varint`).
-/

namespace Nanodregg.Codec.Stream

/-- The LEB128 bytes of `n`, appended to `buf`. -/
def putVarint (n : Nat) (buf : ByteArray) : ByteArray :=
  if n < 128 then buf.push n.toUInt8
  else putVarint (n / 128) (buf.push (n % 128 + 128).toUInt8)
termination_by n
decreasing_by omega

/-- Read the rest of a varint at `i`, having read `k` bytes worth `acc` so far. -/
def getVarint (b : ByteArray) (start : Nat) : (fuel : Nat) → (i k acc : Nat) → Except Refusal (Nat × Nat)
  | 0, i, _, _ => .error (.pastBound start 5 6)
  | fuel + 1, i, k, acc =>
    if h : i < b.size then
      let x := b[i].toNat
      if x < 128 then
        if x = 0 ∧ k > 0 then .error (.rejected start "varint/overlong")
        else
          let v := acc + x * 128 ^ k
          if v < 2 ^ 32 then .ok (v, i + 1) else .error (.pastBound start (2 ^ 32 - 1) v)
      else getVarint b start fuel (i + 1) (k + 1) (acc + (x - 128) * 128 ^ k)
    else .error (.truncated i 1)

/-- The number of bytes `putVarint n` appends. -/
def varintSize (n : Nat) : Nat :=
  if n < 128 then 1 else 1 + varintSize (n / 128)
termination_by n
decreasing_by omega

/-- A natural below 2^32 in one to five bytes. -/
def varint : Stream Nat where
  shape := .varint
  size := varintSize
  put := putVarint
  get b i := getVarint b i 5 i 0 0

end Nanodregg.Codec.Stream
