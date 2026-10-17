/-
# Protocol.Proofs.Wire — a follow step reads back as the step that was written

`ofBytes_bytes`: whatever bytes `host follow` writes for a reply, the client's one reader returns
that reply. With `Step.frame_lawful`, the bytes are also the only spelling of it.
-/
import Protocol.Command.Wire
import Protocol.Proofs.Frames
import Protocol.Proofs.Table

namespace Nanodregg.Protocol.Command

open Nanodregg.Codec

theorem fit_val {max : Nat} {b : ByteArray} {x : Bytes max} (h : Text.fit max b = some x) : x.1 = b := by
  unfold Text.fit at h
  split at h
  · cases h; rfl
  · cases h

theorem relayCode_val {op : Op} {c} (h : relayCode op = some c) : c.1 = op.code := by
  unfold relayCode at h
  split at h
  · cases h; rfl
  · cases h

theorem Reply.ofFrame_frame {r : Reply} {f : Step.Frame} (h : r.frame = some f) :
    Reply.ofFrame f = some r := by
  cases r with
  | done e o er =>
      cases hx : Text.fit Bounds.frameBytesMax o <;> cases hy : Text.fit Bounds.frameBytesMax er <;>
        simp [Reply.frame, hx, hy] at h
      subst h; simp [Reply.ofFrame, fit_val hx, fit_val hy]
  | sign m k =>
      cases hx : Text.fit Bounds.frameBytesMax m <;> cases hy : Text.fit Bounds.frameBytesMax k <;>
        simp [Reply.frame, hx, hy] at h
      subst h; simp [Reply.ofFrame, fit_val hx, fit_val hy]
  | host op p k =>
      cases hc : relayCode op <;> cases hx : Text.fit Bounds.frameBytesMax p <;>
        cases hy : Text.fit Bounds.frameBytesMax k <;> simp [Reply.frame, hc, hx, hy] at h
      subst h; simp [Reply.ofFrame, relayCode_val hc, Op.ofCode?_code, fit_val hx, fit_val hy]
  | submit c k =>
      cases hx : Text.fit Bounds.frameBytesMax c <;> cases hy : Text.fit Bounds.frameBytesMax k <;>
        simp [Reply.frame, hx, hy] at h
      subst h; simp [Reply.ofFrame, fit_val hx, fit_val hy]
  | precommit k =>
      cases hx : Text.fit Bounds.frameBytesMax k <;> simp [Reply.frame, hx] at h
      subst h; simp [Reply.ofFrame, fit_val hx]
  | signNext m k =>
      cases hx : Text.fit Bounds.frameBytesMax m <;> cases hy : Text.fit Bounds.frameBytesMax k <;>
        simp [Reply.frame, hx, hy] at h
      subst h; simp [Reply.ofFrame, fit_val hx, fit_val hy]

theorem Reply.ofBytes_bytes {r : Reply} {b : ByteArray} (h : r.bytes = some b) :
    Reply.ofBytes b = some r := by
  unfold Reply.bytes at h
  cases hf : r.frame with
  | none => simp [hf] at h
  | some f =>
      simp only [hf, Option.map_some, Option.some.injEq] at h
      subst h
      simp [Reply.ofBytes, Stream.decode_bytes Step.frame_lawful, Reply.ofFrame_frame hf]

end Nanodregg.Protocol.Command
