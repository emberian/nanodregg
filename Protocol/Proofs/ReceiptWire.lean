/-
# Protocol.Proofs.ReceiptWire — a receipt reads back as the receipt that was written (cv 01a14ef0-ffe7)

`ofBytes_bytes`: whatever bytes `Receipt.bytes` writes, `Receipt.ofBytes` returns that receipt, the
refused answer's member included (it rides in the `turn` field since KERNEL-50). The premises are
the wire's domain: the digest codec lawful, both paths in the proof codec's domain (`ProofFits`,
which every path a canonical trie proves is in: `Codec.Kernel.prove_fits`), and the answer's
counters below 2^64 (the u64 fields).
-/
import Protocol.Receipt
import Protocol.Proofs.Wire
import Codec.Proofs.TrieProof
import Codec.Proofs.World
import Codec.Deployed

namespace Nanodregg.Protocol.Receipt

open Nanodregg.Codec Nanodregg.Codec.Kernel Nanodregg.Codec.Stream Nanodregg.Kernel

variable {D : Type} [Ord D] [DecidableEq D]

/-- The answer's counters fit the wire's u64 fields. -/
def Answer.Fits : Answer D → Prop
  | .committed h _ => h < 2 ^ 64
  | .refused h code _ => h < 2 ^ 64 ∧ code < 2 ^ 64
  | .absent => True

/-- A receipt on the wire's domain: its answer's counters fit, and both paths are proofs the proof
codec reads back. -/
structure Fits (E : Env D) (r : Receipt D) : Prop where
  answer : r.answer.Fits
  jpath : ProofFits (journalSpec E) (fun _ => True) (fun _ => True) r.jpath
  rpath : ProofFits (refusalSpec E) (RefusalSlot.Fits fun _ => True) (fun _ => True) r.rpath

theorem frame_lawful : Stream.Lawful frame := Layout.codec_lawful _ _ _

omit [Ord D] in
theorem jproof_lawfulOn {E : Env D} {dc : Stream D} (hd : Stream.Lawful dc) :
    LawfulOn (ProofFits (journalSpec E) (fun _ => True) (fun _ => True)) (jproof E dc) :=
  proof_lawfulOn (journalSpec E) hd.on hd.on

omit [Ord D] in
theorem rproof_lawfulOn {E : Env D} {dc : Stream D} (hd : Stream.Lawful dc) :
    LawfulOn (ProofFits (refusalSpec E) (RefusalSlot.Fits fun _ => True) (fun _ => True)) (rproof E dc) :=
  proof_lawfulOn (refusalSpec E) (refusalSlot_lawfulOn hd.on) hd.on

theorem toNat_toUInt64 {n : Nat} (h : n < 2 ^ 64) : n.toUInt64.toNat = n := by
  simp [Nat.toUInt64, Nat.mod_eq_of_lt h]

omit [Ord D] in
/-- **A receipt reads back as the receipt that was written.** -/
theorem ofBytes_bytes {E : Env D} {dc : Stream D} (hd : Stream.Lawful dc) {r : Receipt D} {b : ByteArray}
    (hf : Fits E r) (h : bytes E dc r = some b) : ofBytes E dc b = some r := by
  obtain ⟨txId, root, jroot, rroot, rowsroot, answer, jpath, rpath⟩ := r
  obtain ⟨ha, hj, hr⟩ := hf
  have hjd := (jproof_lawfulOn (E := E) hd).decode_bytes hj
  have hrd := (rproof_lawfulOn (E := E) hd).decode_bytes hr
  simp only at ha hjd hrd
  unfold bytes at h
  cases answer with
  | committed hh td =>
    simp only [Answer.Fits] at ha
    cases h1 : Text.fit Protocol.Bounds.frameBytesMax (dc.bytes td) <;>
    cases h2 : Text.fit Protocol.Bounds.frameBytesMax (dc.bytes txId) <;>
    cases h3 : Text.fit Protocol.Bounds.frameBytesMax (dc.bytes root) <;>
    cases h4 : Text.fit Protocol.Bounds.frameBytesMax (dc.bytes jroot) <;>
    cases h5 : Text.fit Protocol.Bounds.frameBytesMax (dc.bytes rroot) <;>
    cases h6 : Text.fit Protocol.Bounds.frameBytesMax (dc.bytes rowsroot) <;>
    cases h7 : Text.fit Protocol.Bounds.frameBytesMax ((jproof E dc).bytes jpath) <;>
    cases h8 : Text.fit Protocol.Bounds.frameBytesMax ((rproof E dc).bytes rpath) <;>
    simp [h1, h2, h3, h4, h5, h6, h7, h8] at h
    subst h
    simp [ofBytes, Stream.decode_bytes frame_lawful, Command.fit_val h1, Command.fit_val h2,
      Command.fit_val h3, Command.fit_val h4, Command.fit_val h5, Command.fit_val h6,
      Command.fit_val h7, Command.fit_val h8, Stream.decode_bytes hd, hjd, hrd, Except.toOption, toNat_toUInt64 ha]
  | refused hh code m =>
    simp only [Answer.Fits] at ha
    cases h1 : Text.fit Protocol.Bounds.frameBytesMax (dc.bytes m) <;>
    cases h2 : Text.fit Protocol.Bounds.frameBytesMax (dc.bytes txId) <;>
    cases h3 : Text.fit Protocol.Bounds.frameBytesMax (dc.bytes root) <;>
    cases h4 : Text.fit Protocol.Bounds.frameBytesMax (dc.bytes jroot) <;>
    cases h5 : Text.fit Protocol.Bounds.frameBytesMax (dc.bytes rroot) <;>
    cases h6 : Text.fit Protocol.Bounds.frameBytesMax (dc.bytes rowsroot) <;>
    cases h7 : Text.fit Protocol.Bounds.frameBytesMax ((jproof E dc).bytes jpath) <;>
    cases h8 : Text.fit Protocol.Bounds.frameBytesMax ((rproof E dc).bytes rpath) <;>
    simp [h1, h2, h3, h4, h5, h6, h7, h8] at h
    subst h
    simp [ofBytes, Stream.decode_bytes frame_lawful, Command.fit_val h1, Command.fit_val h2,
      Command.fit_val h3, Command.fit_val h4, Command.fit_val h5, Command.fit_val h6,
      Command.fit_val h7, Command.fit_val h8, Stream.decode_bytes hd, hjd, hrd, Except.toOption, toNat_toUInt64 ha.1,
      toNat_toUInt64 ha.2]
  | absent =>
    cases h1 : Text.fit Protocol.Bounds.frameBytesMax ByteArray.empty <;>
    cases h2 : Text.fit Protocol.Bounds.frameBytesMax (dc.bytes txId) <;>
    cases h3 : Text.fit Protocol.Bounds.frameBytesMax (dc.bytes root) <;>
    cases h4 : Text.fit Protocol.Bounds.frameBytesMax (dc.bytes jroot) <;>
    cases h5 : Text.fit Protocol.Bounds.frameBytesMax (dc.bytes rroot) <;>
    cases h6 : Text.fit Protocol.Bounds.frameBytesMax (dc.bytes rowsroot) <;>
    cases h7 : Text.fit Protocol.Bounds.frameBytesMax ((jproof E dc).bytes jpath) <;>
    cases h8 : Text.fit Protocol.Bounds.frameBytesMax ((rproof E dc).bytes rpath) <;>
    simp [h1, h2, h3, h4, h5, h6, h7, h8] at h
    subst h
    simp [ofBytes, Stream.decode_bytes frame_lawful, Command.fit_val h2,
      Command.fit_val h3, Command.fit_val h4, Command.fit_val h5, Command.fit_val h6,
      Command.fit_val h7, Command.fit_val h8, Stream.decode_bytes hd, hjd, hrd, Except.toOption]


/-! ## The tooth: the refused answer's member rides in the wire (KERNEL-50)

A deployed `refused` receipt (digests of seven bytes 7, empty paths) reads back; the same bytes with
the member field one byte short (its length prefix 31, its last byte gone) do not: `ofBytes`
decodes the member at the digest codec, which takes exactly 32 bytes. A reader that skipped the
member would read the short frame. -/

/-- Control: a deployed refused receipt (digests of 32 bytes `7`, empty paths) reads back. -/
theorem receipt_tooth_reads :
    let d : Codec.Digest := ⟨⟨(List.replicate 32 (7 : UInt8)).toArray⟩, by decide⟩
    let r : Receipt Codec.Digest :=
      { txId := d, root := d, jroot := d, rroot := d, rowsroot := d, answer := .refused 3 4 d,
        jpath := { term := none, sibs := [] }, rpath := { term := none, sibs := [] } }
    ((bytes Codec.Deployed.env Codec.Deployed.digestCodec r).bind
      (ofBytes Codec.Deployed.env Codec.Deployed.digestCodec)).isSome = true := by decide +kernel

/-- **TOOTH (cv 01a14ef0-ffe7)**: the same receipt with its member (the `turn` field, after the
answer byte and two u64s) one byte short, its length prefix 31, refuses. -/
theorem receipt_member_dropped :
    let d : Codec.Digest := ⟨⟨(List.replicate 32 (7 : UInt8)).toArray⟩, by decide⟩
    let r : Receipt Codec.Digest :=
      { txId := d, root := d, jroot := d, rroot := d, rowsroot := d, answer := .refused 3 4 d,
        jpath := { term := none, sibs := [] }, rpath := { term := none, sibs := [] } }
    (((bytes Codec.Deployed.env Codec.Deployed.digestCodec r).map fun b =>
        b.extract 0 17 ++ ⟨#[31, 0, 0, 0]⟩ ++ b.extract 21 52 ++ b.extract 53 b.size).bind
      (ofBytes Codec.Deployed.env Codec.Deployed.digestCodec)).isNone = true := by decide +kernel

end Nanodregg.Protocol.Receipt
