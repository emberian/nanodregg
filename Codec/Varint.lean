import Codec.Stream

/-!
# Varint — LEB128 naturals, shortest form only

A natural as base-128 digits, least significant first, each byte's top bit set when another byte
follows: 0–127 is one byte, below 2^14 two. Two widths share one reader (`getVarint width limit`):
`varint`, below 2^32 in at most five bytes (lengths, counts), and `varint64`, below 2^64 in at most
ten (KERNEL-54's per-cell versions and rows floors on the World wire). A decoder refuses an overlong
spelling (a last byte of 0 after a continuation, which a shorter spelling would have omitted), a byte
past the width, and a value at or past the limit. So every value has exactly one spelling
(`Codec.Proofs.Varint`).
-/

namespace Nanodregg.Codec.Stream

/-- The LEB128 bytes of `n`, appended to `buf`. -/
def putVarint (n : Nat) (buf : ByteArray) : ByteArray :=
  if n < 128 then buf.push n.toUInt8
  else putVarint (n / 128) (buf.push (n % 128 + 128).toUInt8)
termination_by n
decreasing_by omega

/-- Read the rest of a varint of at most `width` bytes, below `limit`, at `i`, having read `k` bytes worth
`acc` so far. -/
def getVarint (width limit : Nat) (b : ByteArray) (start : Nat) :
    (fuel : Nat) → (i k acc : Nat) → Except Refusal (Nat × Nat)
  | 0, _, _, _ => .error (.pastBound start width (width + 1))
  | fuel + 1, i, k, acc =>
    if h : i < b.size then
      let x := b[i].toNat
      if x < 128 then
        if x = 0 ∧ k > 0 then .error (.rejected start "varint/overlong")
        else
          let v := acc + x * 128 ^ k
          if v < limit then .ok (v, i + 1) else .error (.pastBound start (limit - 1) v)
      else getVarint width limit b start fuel (i + 1) (k + 1) (acc + (x - 128) * 128 ^ k)
    else .error (.truncated i 1)

/-- The number of bytes `putVarint n` appends. -/
def varintSize (n : Nat) : Nat :=
  if n < 128 then 1 else 1 + varintSize (n / 128)
termination_by n
decreasing_by omega

/-- LEB128 naturals below `limit` in at most `width` bytes, under the shape `sh`. -/
def varintOf (width limit : Nat) (sh : Shape) : Stream Nat where
  shape := sh
  size := varintSize
  put := putVarint
  get b i := getVarint width limit b i width i 0 0

/-- A natural below 2^32 in one to five bytes. -/
def varint : Stream Nat := varintOf 5 (2 ^ 32) .varint

/-- A natural below 2^64 in one to ten bytes (KERNEL-54: a cell's version, a row's version, a relation's
floor, each below `Bounds.counterLimit`). The tenth byte carries bit 63 alone, so a tenth byte of 2 or
more is a value past 2^64 − 1 and refused `pastBound`; an eleventh byte is refused `pastBound 10 11`. -/
def varint64 : Stream Nat := varintOf 10 (2 ^ 64) .varint64

end Nanodregg.Codec.Stream
