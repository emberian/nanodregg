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

theorem signResultFrame_lawful : Stream.Lawful signResultFrame := Layout.codec_lawful _ _ _

theorem precommitResultFrame_lawful : Stream.Lawful precommitResultFrame := Layout.codec_lawful _ _ _

theorem envelopeFrame_lawful : Stream.Lawful envelopeFrame := Layout.codec_lawful _ _ _

theorem logReplyFrame_lawful : Stream.Lawful logReplyFrame := Layout.codec_lawful _ _ _

theorem custodyRefusalFrame_lawful : Stream.Lawful custodyRefusalFrame := Layout.codec_lawful _ _ _

theorem readReplyFrame_lawful : Stream.Lawful readReplyFrame := Layout.codec_lawful _ _ _

end Nanodregg.Protocol
