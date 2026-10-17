import Codec.Layout
import Codec.Proofs.Stream

/-! # Every layout's codec is lawful (hence canonical: `Stream.decode_eq_ok_iff`). -/

namespace Nanodregg.Codec

theorem Field.codec_lawful (max : Nat) (fits : max < 2 ^ 32) :
    (f : Field) → Stream.Lawful (f.codec max fits)
  | .byte _ => Stream.u8_lawful
  | .bytes _ => Stream.bytesOf_lawful max fits
  | .list _ => Stream.array_lawful (Stream.bytesOf_lawful max fits) max fits

theorem Layout.codec_lawful (max : Nat) (fits : max < 2 ^ 32) :
    (l : Layout) → Stream.Lawful (Layout.codec max fits l)
  | [] => Stream.unit_lawful
  | f :: fs => Stream.product_lawful (f.codec_lawful max fits) (Layout.codec_lawful max fits fs)

end Nanodregg.Codec
