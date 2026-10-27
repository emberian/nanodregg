import Codec.Deployed
import Codec.Proofs.Kernel
import Codec.Proofs.World
import Codec.Proofs.Digest

/-! # Codec laws and decoded-World invariants for the deployed instance

These proofs discharge the codec and decoded-state premises they name. Cryptographic faithfulness
and the other premises of the composed claims remain explicit in `Spec`. -/

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
    world.decode (world.bytes w) = .ok w :=
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

/-- A World read as a component of a larger record (HOST's base) satisfies the kernel's trie invariant. -/
theorem world_get_canon {b : ByteArray} {i j : Nat} {w : World Digest} (h : world.get b i = .ok (w, j)) :
    w.Canon env ∧ ∀ p ∈ w.trie.toList, Leaf.fits p.1 p.2 = true :=
  Nanodregg.Codec.Kernel.world_get_canon digestCodec_lawful.on h

/-- **Canonicity, exactly**: a fitting World decodes from `b` iff `b` is its bytes. -/
theorem world_decode_iff {b : ByteArray} {w : World Digest}
    (hw : Nanodregg.Codec.Kernel.World.CodecFits env (fun _ => True) w) : world.decode b = .ok w ↔ b = world.bytes w :=
  Nanodregg.Codec.Kernel.world_decode_iff digestCodec_lawful.on hw

/-- **Every deployed decoded base carries `World.JournalOk`** (KERNEL-39, KERNEL-41): no premise. -/
theorem world_decode_journalOk {b : ByteArray} {w : World Digest} (h : world.decode b = .ok w) : w.JournalOk env :=
  Nanodregg.Codec.Kernel.world_decode_journalOk digestCodec_lawful.on h

/-- **A World the deployed codec reads at any offset carries `World.JournalOk`** (HOST's base record). -/
theorem world_get_journalOk {b : ByteArray} {i j : Nat} {w : World Digest} (h : world.get b i = .ok (w, j)) :
    w.JournalOk env :=
  Nanodregg.Codec.Kernel.world_get_journalOk digestCodec_lawful.on h

/-- **Every deployed decoded base carries `World.RefusalsOk`** (KERNEL-44, KERNEL-47): no premise. -/
theorem world_decode_refusalsOk {b : ByteArray} {w : World Digest} (h : world.decode b = .ok w) :
    w.RefusalsOk env :=
  Nanodregg.Codec.Kernel.world_decode_refusalsOk digestCodec_lawful.on h

/-- **A World the deployed codec reads at any offset carries `World.RefusalsOk`** (HOST's base record). -/
theorem world_get_refusalsOk {b : ByteArray} {i j : Nat} {w : World Digest} (h : world.get b i = .ok (w, j)) :
    w.RefusalsOk env :=
  Nanodregg.Codec.Kernel.world_get_refusalsOk digestCodec_lawful.on h

/-- **No deployed decoded base holds a transaction id both refused and journaled** (KERNEL-47). -/
theorem world_decode_refusalsDisjoint {b : ByteArray} {w : World Digest} (h : world.decode b = .ok w) :
    w.RefusalsDisjoint env :=
  Nanodregg.Codec.Kernel.world_decode_refusalsDisjoint digestCodec_lawful.on h

/-- **A World the deployed codec reads at any offset holds no transaction id both refused and
journaled.** -/
theorem world_get_refusalsDisjoint {b : ByteArray} {i j : Nat} {w : World Digest}
    (h : world.get b i = .ok (w, j)) : w.RefusalsDisjoint env :=
  Nanodregg.Codec.Kernel.world_get_refusalsDisjoint digestCodec_lawful.on h

/-- **A deployed decoded base's refusal counts are its records'** (KERNEL-50, `kernel/refusals-counted`;
`Host.Proofs.Deployed.world_decode_countedOk` reads it as KERNEL's `World.CountedOk`). -/
theorem world_decode_refusalsCounted {b : ByteArray} {w : World Digest} (h : world.decode b = .ok w) :
    refusalsCounted env w = true :=
  Nanodregg.Codec.Kernel.world_decode_refusalsCounted digestCodec_lawful.on h

/-- **A World the deployed codec reads at any offset has refusal counts that are its records'.** -/
theorem world_get_refusalsCounted {b : ByteArray} {i j : Nat} {w : World Digest}
    (h : world.get b i = .ok (w, j)) : refusalsCounted env w = true :=
  Nanodregg.Codec.Kernel.world_get_refusalsCounted digestCodec_lawful.on h

/-- **A deployed decoded base has height at most its step count** (KERNEL's `fold_height_le_steps`'
premise). -/
theorem world_decode_height_le_steps {b : ByteArray} {w : World Digest} (h : world.decode b = .ok w) :
    w.height ≤ w.steps :=
  Nanodregg.Codec.Kernel.world_decode_height_le_steps digestCodec_lawful.on h

/-- **A World the deployed codec reads at any offset has height at most its step count.** -/
theorem world_get_height_le_steps {b : ByteArray} {i j : Nat} {w : World Digest}
    (h : world.get b i = .ok (w, j)) : w.height ≤ w.steps :=
  Nanodregg.Codec.Kernel.world_get_height_le_steps digestCodec_lawful.on h

/-- **A reopened base's rows fit and every head counts its rows** (KERNEL-48). -/
theorem world_decode_rows {b : ByteArray} {w : World Digest} (h : world.decode b = .ok w) :
    RowsCodecFits env (fun _ => True) w.trie w.rows :=
  Nanodregg.Codec.Kernel.world_decode_rows digestCodec_lawful.on h

theorem world_get_rows {b : ByteArray} {i j : Nat} {w : World Digest} (h : world.get b i = .ok (w, j)) :
    RowsCodecFits env (fun _ => True) w.trie w.rows :=
  Nanodregg.Codec.Kernel.world_get_rows digestCodec_lawful.on h

end Nanodregg.Codec.Deployed
