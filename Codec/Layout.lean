import Codec.Stream

/-! # Layout — a frame's fields, as data

A `Layout` is a list of named fields. It is data, so the protocol table can carry it, the Rust
emitter can print a reader and writer for it, and `Layout.codec` turns it into the one `Stream`
that Lean speaks. Every byte-string field shares one bound `max`, the frame bound: a field cannot
be longer than the frame that carries it. -/

namespace Nanodregg.Codec

/-- One field of a frame. -/
inductive Field where
  /-- one byte -/
  | byte (name : String)
  /-- eight bytes, little-endian -/
  | u64 (name : String)
  /-- `u32 len ‖ bytes`, at most `max` bytes -/
  | bytes (name : String)
  /-- `u32 count ‖ (u32 len ‖ bytes)*`, at most `max` items of at most `max` bytes each -/
  | list (name : String)
  /-- one byte, one of the named `cases` (name, code); any other byte is refused as `badTag` -/
  | oneOf (name : String) (cases : List (String × UInt8))
  deriving DecidableEq, Repr

namespace Field

def name : Field → String
  | byte n | u64 n | bytes n | list n | oneOf n _ => n

/-- The Lean value of a field. -/
abbrev Ty (max : Nat) : Field → Type
  | byte _ => UInt8
  | u64 _ => UInt64
  | bytes _ => Bytes max
  | list _ => Bounded max (Bytes max)
  | oneOf _ cases => { b : UInt8 // (cases.map Prod.snd).toArray.contains b = true }

def codec (max : Nat) (fits : max < 2 ^ 32) : (f : Field) → Stream (f.Ty max)
  | byte _ => Stream.u8
  | u64 _ => Stream.u64
  | bytes _ => Stream.bytesOf max fits
  | list _ => Stream.array max (Stream.bytesOf max fits) fits
  | oneOf _ cases => Stream.oneOf (cases.map Prod.snd).toArray

end Field

/-- A frame's fields, in order. -/
abbrev Layout := List Field

namespace Layout

/-- The Lean value of a layout: its fields' values, nested pairs ending in `Unit`. -/
abbrev Ty (max : Nat) : Layout → Type
  | [] => Unit
  | f :: fs => f.Ty max × Ty max fs

def codec (max : Nat) (fits : max < 2 ^ 32) : (l : Layout) → Stream (l.Ty max)
  | [] => Stream.unit
  | f :: fs => Stream.product (f.codec max fits) (codec max fits fs)

end Layout
end Nanodregg.Codec
