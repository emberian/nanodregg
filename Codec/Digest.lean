/-! # Digest — the one digest type

A digest is exactly 32 bytes. It is never a natural number: ordering, trie index
bits and equality are read off the bytes. Hash functions produce it
(`Codec.Hash`); codecs carry it as 32 raw bytes (`Codec.Stream.digest`). -/

namespace Nanodregg.Codec

/-- A 256-bit digest: exactly 32 bytes. -/
structure Digest where
  bytes : ByteArray
  size_eq : bytes.size = 32

namespace Digest

/-- The width of every digest, in bytes. -/
abbrev width : Nat := 32

instance : DecidableEq Digest := fun a b =>
  if h : a.bytes = b.bytes then
    .isTrue (by cases a; cases b; cases h; rfl)
  else
    .isFalse (fun e => h (by cases e; rfl))

instance : Hashable Digest := ⟨fun d => hash d.bytes⟩

/-- A digest from exactly 32 bytes; any other size has none. -/
def ofBytes? (b : ByteArray) : Option Digest :=
  if h : b.size = 32 then some ⟨b, h⟩ else none

/-- The all-zero digest (the empty trie's root is defined by the trie, not by this). -/
def zero : Digest := ⟨⟨Array.replicate 32 0⟩, by simp [ByteArray.size]⟩

/-- Byte `k` of the digest. -/
@[inline] def byte (d : Digest) (k : Fin 32) : UInt8 := d.bytes[k.val]'(by rw [d.size_eq]; exact k.isLt)

/-- Bit `k`, most significant first: bit 0 is the top bit of byte 0. A trie walks
these 256 bits; no natural number is formed. -/
@[inline] def bit (d : Digest) (k : Fin 256) : Bool :=
  (d.byte ⟨k.val / 8, by omega⟩ >>> (7 - (k.val % 8)).toUInt8) &&& 1 == 1

/-- Lexicographic order on the 32 bytes (= numeric order of the big-endian value). Its laws
(`Std.TransOrd`, `Std.LawfulEqOrd`, which the World's maps need) are `Codec.Proofs.Digest`. -/
instance : Ord Digest := ⟨fun a b => compare a.bytes.data b.bytes.data⟩

/-- Lowercase hex, 64 characters. -/
def toHex (d : Digest) : String :=
  let digit (n : UInt8) : Char := if n < 10 then Char.ofNat (48 + n.toNat) else Char.ofNat (87 + n.toNat)
  d.bytes.foldl (fun s x => (s.push (digit (x >>> 4))).push (digit (x &&& 15))) ""

instance : Repr Digest := ⟨fun d _ => "Digest " ++ d.toHex⟩

end Digest
end Nanodregg.Codec
