import Codec.Stream
import Codec.Path

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
  /-- four bytes, little-endian -/
  | u32 (name : String)
  /-- a sandbox path (`Codec.Path`): `u32 len ‖ bytes`, its clean components joined by `/`, at most
  `max` bytes; a spelling with an unclean component is refused `rejected … "path/badComponent"` -/
  | path (name : String)
  /-- `u32 count ‖ path*`, at most `max` paths -/
  | paths (name : String)
  deriving DecidableEq, Repr

namespace Field

def name : Field → String
  | byte n | u64 n | bytes n | list n | oneOf n _ | u32 n | path n | paths n => n

/-- A path value: clean components whose join fits `max`. -/
abbrev PathTy (max : Nat) := { p : List ByteArray // Path.fits max p = true }

private theorem join_fits {max : Nat} {p : List ByteArray} (h : Path.fits max p = true) :
    (Path.join p).size ≤ max := by
  simp only [Path.fits, Bool.and_eq_true, decide_eq_true_eq] at h; exact h.2

/-- A path on the wire: the joined bytes, read back by `split` and refused unless clean. -/
def pathCodec (max : Nat) (fits : max < 2 ^ 32) : Stream (PathTy max) :=
  Stream.refine "path/badComponent" (Stream.bytesOf max fits)
    (fun b => if h : Path.fits max (Path.split b.val) = true then some ⟨Path.split b.val, h⟩ else none)
    (fun p => ⟨Path.join p.val, join_fits p.property⟩)

/-- The Lean value of a field. -/
abbrev Ty (max : Nat) : Field → Type
  | byte _ => UInt8
  | u64 _ => UInt64
  | bytes _ => Bytes max
  | list _ => Bounded max (Bytes max)
  | oneOf _ cases => { b : UInt8 // (cases.map Prod.snd).toArray.contains b = true }
  | u32 _ => UInt32
  | path _ => PathTy max
  | paths _ => Bounded max (PathTy max)

def codec (max : Nat) (fits : max < 2 ^ 32) : (f : Field) → Stream (f.Ty max)
  | byte _ => Stream.u8
  | u64 _ => Stream.u64
  | bytes _ => Stream.bytesOf max fits
  | list _ => Stream.array max (Stream.bytesOf max fits) fits
  | oneOf _ cases => Stream.oneOf (cases.map Prod.snd).toArray
  | u32 _ => Stream.u32
  | path _ => pathCodec max fits
  | paths _ => Stream.array max (pathCodec max fits) fits

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

/-- A tagged frame: one tag byte naming a case, then that case's layout. Each case is
(name, code, layout); codes are distinct (`Tagged.codec_lawful` takes it as its premise). -/
abbrev Tagged := List (String × UInt8 × Layout)

namespace Tagged

def code (cases : Tagged) (s : Fin cases.length) : UInt8 := (cases.get s).2.1

def ofCode? (cases : Tagged) (t : UInt8) : Option (Fin cases.length) :=
  (List.finRange cases.length).find? fun s => code cases s == t

/-- The Lean value of a tagged frame: which case, and that case's fields. -/
abbrev Ty (max : Nat) (cases : Tagged) := (s : Fin cases.length) × Layout.Ty max (cases.get s).2.2

def codec (max : Nat) (fits : max < 2 ^ 32) (cases : Tagged) : Stream (Ty max cases) :=
  Stream.tagged (List.finRange cases.length) (code cases) (ofCode? cases)
    fun s => Layout.codec max fits (cases.get s).2.2

end Tagged
end Nanodregg.Codec
