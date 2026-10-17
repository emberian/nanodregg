import Protocol.Frames
import Protocol.Proofs.Table
import Codec.Proofs.Layout

/-!
# Protocol.Proofs.Frames — every follow payload is decoded canonically

With `Codec.Stream.decode_eq_ok_iff`: a step, command or resume payload decodes to `v` exactly when it
IS `bytes v`. No second spelling is accepted, so the client and follow cannot disagree about a
frame both of them accept.
-/

namespace Nanodregg.Protocol

open Nanodregg.Codec

theorem Step.frame_lawful : Stream.Lawful Step.frame :=
  Stream.tagged_lawful Step.all (fun s => Layout.codec_lawful _ _ s.layout) Step.ofCode?_code
    (fun _ _ h => Step.code_of_ofCode? h)

theorem commandFrame_lawful : Stream.Lawful commandFrame :=
  Stream.within_lawful (Layout.codec_lawful _ _ _) _

theorem resumeFrame_lawful : Stream.Lawful resumeFrame := Layout.codec_lawful _ _ _

end Nanodregg.Protocol
