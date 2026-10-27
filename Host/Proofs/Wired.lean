/-
# Host.Proofs.Wired — `host serve` and `host follow` read a request's version before anything else
-/
import Host.Wire
import Protocol.Proofs.Version

namespace Nanodregg.Host

open Nanodregg.Protocol (versionOf? wireBytes wireRefusal unwire versionBytes)

/-- **A request at another wire is answered by name from its op and version alone** (PROTOCOL-87):
a frame that is not the supervisor's own (a hang-up or a ping) and whose bytes after the op do not begin with this wire's version is
the reply `refused wireVersion N expected M` to its own connection, N its four bytes. -/
theorem wiredReply_other (f : Frame) (hk : Protocol.childKindOf? f.op = some .request ∨ Protocol.childKindOf? f.op = none)
    (hv : versionOf? f.payload ≠ some wireBytes) :
    wiredReply f = .error ⟨f.conn, Protocol.Status.refused.code, (wireRefusal (versionOf? f.payload)).toUTF8⟩ := by
  rcases hk with hk | hk <;> simp only [wiredReply, hk, Protocol.unwire_other f.payload hv]

/-- **The writer's machine never sees a request at another wire**: whatever machine `host serve`
wraps, its answer to such a frame is the version refusal, the same for every machine and every
World, so no field after the version (no call, no envelope, not the op's meaning) is decoded. -/
theorem wired_other {W T N : Type} (m : Machine W T Frame N) (w : W) (f : Frame)
    (hk : Protocol.childKindOf? f.op = some .request ∨ Protocol.childKindOf? f.op = none) (hv : versionOf? f.payload ≠ some wireBytes) :
    m.wired.handle w f = .reply Protocol.Status.refused.code (wireRefusal (versionOf? f.payload)).toUTF8 := by
  simp only [Machine.wired, wiredReply_other f hk hv]

/-- At this wire's version the wrapped machine answers the frame with the version taken off. -/
theorem wired_ours {W T N : Type} (m : Machine W T Frame N) (w : W) (f : Frame)
    (hk : Protocol.childKindOf? f.op = some .request ∨ Protocol.childKindOf? f.op = none) (hv : versionOf? f.payload = some wireBytes) :
    m.wired.handle w f = m.handle w { f with payload := f.payload.extract versionBytes f.payload.size } := by
  rcases hk with hk | hk <;> simp only [Machine.wired, wiredReply, hk, Protocol.unwire_ours f.payload hv]

/-- A client's frame, `versioned`, reaches the wrapped machine as the payload it sent. -/
theorem wired_versioned {W T N : Type} (m : Machine W T Frame N) (w : W) (conn : UInt32) (op : UInt8)
    (p : ByteArray) (hk : Protocol.childKindOf? op = some .request ∨ Protocol.childKindOf? op = none) :
    m.wired.handle w ⟨conn, op, Protocol.versioned p⟩ = m.handle w ⟨conn, op, p⟩ := by
  rcases hk with hk | hk <;> simp only [Machine.wired, wiredReply, hk, Protocol.unwire_versioned]

end Nanodregg.Host
