import Codec.Deployed
import Codec.Proofs.Kernel
import Codec.Proofs.World
import Codec.Proofs.Digest

/-! # The deployed instance satisfies what the kernel's theorems assume -/

namespace Nanodregg.Codec.Deployed

open Nanodregg.Kernel Nanodregg.Kernel.Receive Nanodregg.Codec.Kernel

theorem digestCodec_lawful : Stream.Lawful digestCodec := Stream.digest_lawful

theorem bytes_injective {a b : Digest} (h : env.bytes a = env.bytes b) : a = b := by
  obtain ⟨x, hx⟩ := a
  obtain ⟨y, hy⟩ := b
  simp only [env] at h
  subst h
  rfl

theorem digestOf_bytes (d : Digest) : Digest.ofBytes? (env.bytes d) = some d := by
  simp [Digest.ofBytes?, env, d.size_eq]

theorem bytes_of_digestOf {b : ByteArray} {d : Digest} (h : Digest.ofBytes? b = some d) : env.bytes d = b := by
  unfold Digest.ofBytes? at h
  split at h
  · cases h; rfl
  · cases h

/-- Admitted turns with equal bytes are equal. -/
theorem turnBytes_injective {t t' : Turn Digest} (ht : checkBounds t = .ok ()) (ht' : checkBounds t' = .ok ())
    (h : env.turnBytes t = env.turnBytes t') : t = t' :=
  Nanodregg.Codec.Kernel.turnBytes_injective digestCodec_lawful ht ht' h

theorem decodeCall_callBytes (program : Program Digest) {c : Call Digest} (hc : Call.Fits (fun _ => True) c) :
    (ctx program).decodeCall ((ctx program).callBytes c) = some c :=
  Nanodregg.Codec.Kernel.decodeCall_callBytes digestCodec_lawful.on hc

theorem eq_callBytes_of_decodeCall (program : Program Digest) {b : ByteArray} {c : Call Digest}
    (h : (ctx program).decodeCall b = some c) : Call.Fits (fun _ => True) c ∧ b = (ctx program).callBytes c :=
  Nanodregg.Codec.Kernel.eq_callBytes_of_decodeCall digestCodec_lawful.on h

theorem world_decode_bytes {w : World Digest} (hw : Nanodregg.Codec.Kernel.World.CodecFits env (fun _ => True) w) :
    ∃ w', world.decode (world.bytes w) = .ok w' ∧ w'.Equiv w :=
  Nanodregg.Codec.Kernel.world_decode_bytes digestCodec_lawful.on hw

theorem eq_bytes_of_world_decode {b : ByteArray} {w : World Digest} (h : world.decode b = .ok w) :
    b = world.bytes w :=
  Nanodregg.Codec.Kernel.eq_bytes_of_world_decode digestCodec_lawful.on h

/-- A reopened base satisfies the kernel's trie invariant, so every kernel theorem applies to it. -/
theorem world_decode_canon {b : ByteArray} {w : World Digest} (h : world.decode b = .ok w) :
    w.Canon env ∧ ∀ p ∈ w.trie.toList, Leaf.fits p.1 p.2 = true :=
  Nanodregg.Codec.Kernel.world_decode_canon digestCodec_lawful.on h

theorem world_decode_slotted {b : ByteArray} {w : World Digest} (h : world.decode b = .ok w) : w.Slotted env :=
  Nanodregg.Codec.Kernel.world_decode_slotted digestCodec_lawful.on h

/-- A reopened base's live cells are in the cell codec's domain (the kernel's `World.CellsFit`). -/
theorem world_decode_cellsFit {b : ByteArray} {w : World Digest} (h : world.decode b = .ok w) :
    w.CellsFit Nanodregg.Codec.Kernel.Cell.Fits env :=
  Nanodregg.Codec.Kernel.world_decode_cellsFit digestCodec_lawful.on h

/-- **A deployed turn's record is `Turn.logWeight` bytes**: the charge KERNEL computes for the log is the
log's byte count (KERNEL-32). -/
theorem turnBytes_size (t : Turn Digest) : (env.turnBytes t).size = t.logWeight := by
  show ((turn digestCodec).bytes t).size = t.logWeight
  rw [← (turn_lawfulOn digestCodec_lawful.on).size_eq, turn_size_logWeight (fun _ => rfl)]

end Nanodregg.Codec.Deployed
