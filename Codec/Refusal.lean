/-! # Codec refusals

Every way a decoder refuses, by name, with the byte offset at which it refused.
A refusal is never a value: a decoder returns `Except Refusal`, and the layer that
answers a request embeds `Refusal` in its own named refusal. -/

namespace Nanodregg.Codec

/-- Why a decoder refused, and where (`offset` is the offset into the input). -/
inductive Refusal where
  /-- Fewer than `need` bytes remained at `offset`. -/
  | truncated (offset need : Nat)
  /-- A top-level decode consumed up to `offset` and bytes remained after it. -/
  | trailing (offset : Nat)
  /-- A length or count `got` exceeded the declared `limit`. -/
  | pastBound (offset limit got : Nat)
  /-- A tag byte the decoder does not know: not 0 or 1 for a sum or option, not one of the listed codes for `oneOf`, `tagged` and `choice`. -/
  | badTag (offset : Nat) (tag : UInt8)
  /-- A frame's 32-byte tag was not the tag this decoder reads. -/
  | wrongFrame (offset : Nat)
  /-- A refinement named `name` rejected the wire value decoded at `offset`. -/
  | rejected (offset : Nat) (name : String)
  /-- A tree nested deeper than its declared depth `limit`. -/
  | tooDeep (offset limit : Nat)
  deriving DecidableEq, Repr

end Nanodregg.Codec
