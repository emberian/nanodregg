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

theorem expiredRefusalFrame_lawful : Stream.Lawful expiredRefusalFrame := Layout.codec_lawful _ _ _

theorem readReplyFrame_lawful : Stream.Lawful readReplyFrame := Layout.codec_lawful _ _ _

theorem socketFrame_lawful : Stream.Lawful socketFrame := Stream.bytesOf_lawful _ _

theorem rotationFrame_lawful : Stream.Lawful rotationFrame := Layout.codec_lawful _ _ _

/-- The widths the Rust frame and mux read (`FRAME_LEN_BYTES`, `CONN_BYTES`): a `u32`'s. -/
theorem frameLenBytes_eq : Bounds.frameLenBytes = 4 := rfl
theorem connBytes_eq : Bounds.connBytes = 4 := rfl

/-- A socket frame is its length prefix, then its body. -/
theorem socketFrame_size (v : Bytes Bounds.frameBytesMax) :
    socketFrame.size v = Bounds.frameLenBytes + v.val.size := rfl

/-- A body that is an op byte and a payload says exactly that. -/
theorem bodyParts?_push (op : UInt8) (p : ByteArray) :
    bodyParts? (ByteArray.mk #[op] ++ p) = some (op, p) := by
  have hs : (ByteArray.mk #[op] ++ p).size = 1 + p.size := by simp [ByteArray.size_append]
  unfold bodyParts?
  rw [dif_pos (by omega)]
  have h1 : (ByteArray.mk #[op] ++ p).extract 1 (ByteArray.mk #[op] ++ p).size = p :=
    ByteArray.extract_append_eq_right rfl hs
  rw [h1]
  simp

/-- A record whose keys are whole public keys is `rotationBytes` long (80). -/
theorem rotationFrame_size (v : Layout.Ty Ed25519.publicKeyBytes rotationLayout)
    (hi : v.2.1.val.size = Ed25519.publicKeyBytes) (hp : v.2.2.1.val.size = Ed25519.publicKeyBytes) :
    rotationFrame.size v = rotationBytes := by
  obtain ⟨a, i, p, u⟩ := v
  simp only at hi hp
  simp [rotationFrame, rotationLayout, Layout.codec, Field.codec, Stream.product, Stream.bytesOf,
    Stream.u64, Stream.u32, Stream.unit, rotationBytes, hi, hp]
  omega

/-- `verify` accepts only a key of `publicKeyBytes`: the record's width is the verifier's. -/
theorem _root_.Nanodregg.Codec.Ed25519.verify_pk_size {pk msg sig : ByteArray}
    (h : Ed25519.verify pk msg sig = true) : pk.size = Ed25519.publicKeyBytes := by
  unfold Ed25519.verify at h
  by_cases hs : pk.size = 32
  · exact hs
  · simp [hs] at h

theorem rotationBytes_eq : rotationBytes = 80 := rfl

end Nanodregg.Protocol
