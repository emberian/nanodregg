import Codec.Hash
import Codec.Varint

/-!
# Tag — content-addressed codec identities

A codec's tag is the digest of a label and the codec's `Shape`: `Tag.of label c =
Hash.digest "nanodregg/codec/tag/v1" (label ‖ shape bytes)`. Change a codec's structure and its
tag changes with it. Nobody edits a version literal, no census lists the tags, and no fingerprint is
pinned. A Store stamped with the tags of the codecs that wrote it refuses to open under codecs
with other tags: an old shape refuses, it is never reinterpreted. A `refine`'s name is the one part
the shape takes on trust: the shape cannot see inside a function. Its accepted set is pinned by its
lawfulness theorem (the refine census) and its meaning by the codec vectors, which go red when a
meaning changes under an unchanged tag (CODEC-28).
-/

namespace Nanodregg.Codec

mutual
/-- The canonical bytes of a shape: one tag byte per constructor, then its fields; every number and
length an (unbounded) LEB128 varint, so the encoding is prefix-free for every shape. -/
def Shape.put : Shape → ByteArray → ByteArray
  | .unit, b => b.push 0
  | .u8, b => b.push 1
  | .u32, b => b.push 2
  | .u64, b => b.push 3
  | .varint, b => b.push 4
  | .digest, b => b.push 5
  | .bytes max, b => Stream.putVarint max (b.push 6)
  | .option s, b => s.put (b.push 7)
  | .product x y, b => y.put (x.put (b.push 8))
  | .sum x y, b => y.put (x.put (b.push 9))
  | .array max s, b => s.put (Stream.putVarint max (b.push 10))
  | .refine name s, b =>
    s.put (Stream.putVarint name.toUTF8.size (b.push 11) ++ name.toUTF8)
  | .framed tag s, b => s.put (b.push 12 ++ tag.bytes)
  | .tagged cases, b => Shape.putCases cases (Stream.putVarint cases.length (b.push 13))
  | .tree max depth, b => Stream.putVarint depth (Stream.putVarint max (b.push 14))
  | .oneOf codes, b => Stream.putVarint codes.size (b.push 15) ++ ⟨codes⟩
  | .within limit s, b => s.put (Stream.putVarint limit (b.push 16))
  | .bytes8 max, b => Stream.putVarint max (b.push 17)
  | .u16, b => b.push 18

/-- Each case's code byte and shape, in order. -/
def Shape.putCases : List (UInt8 × Shape) → ByteArray → ByteArray
  | [], b => b
  | (code, s) :: rest, b => Shape.putCases rest (s.put (b.push code))
end

/-- What a tag hashes: the label (length-prefixed) and the shape's bytes. -/
def Tag.message (label : String) (shape : Shape) : ByteArray :=
  shape.put (Stream.putVarint label.toUTF8.size ByteArray.empty ++ label.toUTF8)

/-- A codec's identity: the digest of its label and its shape. -/
def Tag.of {α : Type} (label : String) (c : Stream α) : Digest :=
  Hash.digest "nanodregg/codec/tag/v1" (Tag.message label c.shape)

end Nanodregg.Codec
