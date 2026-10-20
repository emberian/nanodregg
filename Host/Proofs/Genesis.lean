/-
# Host.Proofs.Genesis — the open of what genesis writes is the World genesis was given (one start path)

`genesisImage keys c world mark w₀` is the Store genesis writes (the origin frame, the base of
`w₀` after it, an empty the index file). `genesisImage_opens`: the one open (`openWith`) over exactly
those bytes succeeds, and returns `w₀` itself, no records, no torn tail, positioned at the
segment's end. So the loop's start state after `host genesis` is the World it was given.

* `Base.read_file` — a base `Base.file` writes reads back, under `Base.read`, as exactly the base
  it was written from, given the World codec reads that World back (`P`) and its u64 fields fit:
  the base record (stamp, World, two u64 and two tags) of a World `Base.file` admits
  (`world.size w ≤ c.worldBytesMax`) is within `c.baseRecordMax` (`Cadence.baseRecordMax` counts
  each part), and `c.baseRecordMax` fits the frame's u32 length field (`hcap`); the offset's u64
  bound is the writer's own refusal (`Base.file_offset_lt`, `positionUnfit`);
* `openLog_empty` — an empty tail opens clean, to the base's World, with no record;
* `tailRead_self`, `indexNamed_zero` — the genesis base's tail is empty and it names no entry;
* `genesisImage_header` (`Host.Proofs.Base`) — its file's checkpoint header passes the open's check.

`genesisImage` itself refuses `worldTooLarge` (a World over `c.worldBytesMax`) and, unreachably for
an origin frame, `positionUnfit`; every image
it returns of a World the World codec reads back opens (`genesisImage_opens`). host-sim's `plant-world-at-cap` opens a World of exactly `worldBytesMax` bytes.
-/
import Host.Proofs.Backup

namespace Nanodregg.Host

open Nanodregg.Host.Log ByteArray

variable {W F : Type}

/-- What a genesis image is: the origin frame of `(mark w₀).2`, the base file `Base.file` writes
for `w₀` at that frame's end chained from its tag (counting no entry), and an empty index. -/
theorem genesisImage_ok {keys : Keys} {c : Cadence} {world : Codec.Stream W}
    {mark : W → Nat × ByteArray} {w₀ : W} {img : Image}
    (h : genesisImage keys c world mark w₀ = .ok img) :
    ∃ file, Base.file keys c world w₀ ⟨(frame keys.segment segmentInitial (mark w₀).2).size,
        tagDigest keys.segment (segmentInitial ++ (mark w₀).2)⟩ indexStart Keep.all = .ok file ∧
      img = ⟨frame keys.segment segmentInitial (mark w₀).2, file, ByteArray.empty,
        Header.bytes keys (Header.at ⟨0, Codec.Digest.zero⟩ (mark w₀) 0 0 (mark w₀).2),
        Header.bytes keys (Header.at ⟨(frame keys.segment segmentInitial (mark w₀).2).size,
          tagDigest keys.segment (segmentInitial ++ (mark w₀).2)⟩ (mark w₀) 0 0 (mark w₀).2)⟩ := by
  unfold genesisImage at h
  dsimp only at h
  split at h
  · cases h
  · rename_i file hf
    cases h
    exact ⟨file, hf, rfl⟩

/-- The bytes of a base record `Base.file` writes for `w` (the stamp, the World, two u64 and two
tags, and the two u64 of what it keeps). -/
theorem Base.record_size {P : W → Prop} {world : Codec.Stream W} (hw : Codec.Stream.LawfulOn P world)
    (shapes : Codec.Digest) (b : Base W) :
    (shapes.bytes ++ (Base.codec world).bytes b).size = stampBytes + world.size b.world + 2 * (8 + tagBytes) + 2 * 8 := by
  rw [size_append, shapes.size_eq, ← (Base.codec_lawfulOn hw).size_eq]
  show 32 + (world.size b.world + (8 + (32 + (8 + (32 + (8 + 8)))))) =
    stampBytes + world.size b.world + 2 * (8 + tagBytes) + 2 * 8
  unfold stampBytes tagBytes; omega

/-- **A base `Base.file` writes names a u64 position**: it refuses any other (`positionUnfit`). -/
theorem Base.file_offset_lt {keys : Keys} {c : Cadence} {world : Codec.Stream W} {w : W} {seg : Position}
    {ix : IndexAt} {keep : Keep} {file : ByteArray} (h : Base.file keys c world w seg ix keep = .ok file) :
    seg.offset < 2 ^ 64 := by
  unfold Base.file at h
  split at h
  · cases h
  split at h
  · cases h
  rename_i hoff
  omega

/-- **A base `Base.file` writes keeps no file past its own and no entry past its count** (HOST-64):
it refuses any other keep (`positionUnfit`). -/
theorem Base.file_keep_le {keys : Keys} {c : Cadence} {world : Codec.Stream W} {w : W} {seg : Position}
    {ix : IndexAt} {keep : Keep} {file : ByteArray} (h : Base.file keys c world w seg ix keep = .ok file) :
    keep.retainedFrom ≤ seg.offset ∧ keep.indexFrom ≤ ix.count := by
  unfold Base.file at h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · cases h
  rename_i hk
  omega

/-- **A base file reads back as the base it was written from.** -/
theorem Base.read_file {P : W → Prop} {keys : Keys} {c : Cadence} {world : Codec.Stream W}
    (hw : Codec.Stream.LawfulOn P world) {w : W} {seg : Position} {ix : IndexAt} {keep : Keep} {file : ByteArray}
    (h : Base.file keys c world w seg ix keep = .ok file) (hP : P w)
    (hcount : ix.count < 2 ^ 64) (hcap : c.baseRecordMax < 2 ^ 32) :
    file.size ≤ frameMax c.baseRecordMax ∧
      Base.read keys c world file = .ok (⟨w, seg.offset, seg.tag, ix.count, ix.last, keep.retainedFrom,
        keep.indexFrom⟩, world.size w, keys.worldDigest (worldBytesOf file (world.size w))) := by
  have hoff := Base.file_offset_lt h
  have ⟨hk1, hk2⟩ := Base.file_keep_le h
  unfold Base.file at h
  split at h
  · cases h
  rename_i hfit
  rw [if_neg (by omega), if_neg (by omega)] at h
  cases h
  have hroom : stampBytes + world.size w + 2 * (8 + tagBytes) + 2 * 8 ≤ c.baseRecordMax := by
    unfold Cadence.baseRecordMax; omega
  have hrs := Base.record_size hw keys.shapes ⟨w, seg.offset, seg.tag, ix.count, ix.last, keep.retainedFrom, keep.indexFrom⟩
  simp only at hrs
  generalize hrec : keys.shapes.bytes ++ (Base.codec world).bytes ⟨w, seg.offset, seg.tag, ix.count, ix.last, keep.retainedFrom, keep.indexFrom⟩ = rec at hrs
  have hfs := size_frame keys.base baseInitial rec
  have hle : (frame keys.base baseInitial rec).size ≤ frameMax c.baseRecordMax := by
    rw [hfs]; unfold frameMax; omega
  refine ⟨hle, ?_⟩
  have hr := frameAt_frame keys.base (recordMax := c.baseRecordMax) ByteArray.empty baseInitial rec
    ByteArray.empty (by omega) (by omega)
  simp only [ByteArray.empty_append, ByteArray.append_empty, ByteArray.size_empty, Nat.zero_add] at hr
  have hss : keys.shapes.bytes.size = stampBytes := keys.shapes.size_eq
  have hstamp : rec.extract 0 stampBytes = keys.shapes.bytes := by
    rw [← hrec]; exact extract_append_eq_left hss.symm
  have hbody : rec.extract stampBytes rec.size =
      (Base.codec world).bytes ⟨w, seg.offset, seg.tag, ix.count, ix.last, keep.retainedFrom, keep.indexFrom⟩ := by
    rw [← hrec]; exact extract_append_eq_right hss.symm (by rw [size_append, hss])
  have hdec := (Base.codec_lawfulOn hw).decode_bytes
    (v := (⟨w, seg.offset, seg.tag, ix.count, ix.last, keep.retainedFrom, keep.indexFrom⟩ : Base W))
    ⟨hP, hoff, hcount, hk1, hk2⟩
  unfold Base.read
  rw [if_neg (by omega), hr]
  simp only [ne_eq, not_true_eq_false, if_false, hstamp, hbody, hdec]

/-- The genesis base's tail is empty: the segment ends at the base's offset. -/
theorem tailRead_self (c : Cadence) (baseBytes size : Nat) : tailRead c baseBytes size size = .ok 0 := by
  unfold tailRead; simp

/-- A base that counts no entry and names `Digest.zero` passes the index check. -/
theorem indexNamed_zero (keys : Keys) (before : Nat) (b : ByteArray) :
    indexNamed keys 0 Codec.Digest.zero before b = none := by
  unfold indexNamed; simp

/-- **An empty tail opens clean**: to the base's World, no record, nothing valid, nothing torn, and
the chain still at `initial`. -/
theorem openLog_empty (s : Sealer) (recordMax : Nat) (step : W → ByteArray → Except F W) (w₀ : W)
    (initial log : ByteArray) (hl : log.size = 0) :
    openLog s recordMax step w₀ initial log = .ok ⟨w₀, 0, 0, initial, 0⟩ := by
  unfold openLog recover
  rw [hl]
  simp only [go, Log.step, hl, Nat.le_refl, if_true, List.reverse_nil, foldRecords, List.length_nil, tornOf]

/-- **The open of what genesis writes is the World genesis was given** (one start path): the one
open over exactly the genesis image's bytes succeeds, to `w₀` itself, no records, no torn tail,
positioned at the segment's end.

Premises: `hw`/`hP`, the World codec reads `w₀` back; `hsize`, the genesis chain is the Store's
chain width (below 2^32) and its step count a u64 (the checkpoint header's layout, HOST-64); `ho`,
`origin` names the chain `mark` writes at genesis (KERNEL's `genesisChain` equation); `hcap`, the
base record bound fits the u32 length field. -/
theorem genesisImage_opens (keys : Keys) (c : Cadence) (world : Codec.Stream W)
    (mark : W → Nat × ByteArray) (origin : W → ByteArray) (step : W → ByteArray → Except F W)
    {P : W → Prop} (hw : Codec.Stream.LawfulOn P world) {w₀ : W} (hP : P w₀) {img : Image}
    (h : genesisImage keys c world mark w₀ = .ok img)
    (hsize : (mark w₀).2.size = keys.chainBytes) (hcb : keys.chainBytes < 2 ^ 32) (hst : (mark w₀).1 < 2 ^ 64)
    (ho : origin w₀ = (mark w₀).2) (hcap : c.baseRecordMax < 2 ^ 32) :
    ∃ o, Id.run (openWith keys c world mark origin step img.base img.header img.segment.size img.index.size
        (segReader img.index) (segReader img.segment)) = .ok o ∧
      o.opened.world = w₀ ∧ o.opened.records = 0 ∧ o.opened.torn = 0 ∧ o.pos.offset = img.segment.size := by
  have hor := genesisImage_header keys c world mark origin w₀ h hsize hcb hst ho
  obtain ⟨file, hf, rfl⟩ := genesisImage_ok h
  simp only at hor ⊢
  generalize Header.bytes keys (Header.at ⟨(frame keys.segment segmentInitial (mark w₀).2).size,
    tagDigest keys.segment (segmentInitial ++ (mark w₀).2)⟩ (mark w₀) 0 0 (mark w₀).2) = hdr at hor ⊢
  generalize Header.bytes keys (Header.at ⟨0, Codec.Digest.zero⟩ (mark w₀) 0 0 (mark w₀).2) = hdr0 at hor ⊢
  generalize hch : (mark w₀).2 = ch at hf hor hsize
  generalize hseg : frame keys.segment segmentInitial ch = seg at hf hor
  have hss : seg.size = 4 + ch.size + tagBytes := by rw [← hseg, size_frame]
  obtain ⟨hfs, hb⟩ := Base.read_file hw hf hP (by simp [indexStart]) hcap
  simp only [indexStart] at hb
  -- the 32 bytes before the base's offset are the origin frame's tag
  have htag : seg.extract (seg.size - tagBytes) (seg.size - tagBytes + (tagBytes + 0)) =
      (tagDigest keys.segment (segmentInitial ++ ch)).bytes := by
    have := (frame_fields keys.segment segmentInitial ch ByteArray.empty).2.2
    rw [ByteArray.append_empty, hseg] at this
    rw [show seg.size - tagBytes = 4 + ch.size by omega,
      show 4 + ch.size + (tagBytes + 0) = 4 + ch.size + tagBytes by omega, this]
    rfl
  have htsz : (tagDigest keys.segment (segmentInitial ++ ch)).bytes.size = tagBytes :=
    keys.segment.tag_size _
  have hofs : Codec.Digest.ofBytes? (tagDigest keys.segment (segmentInitial ++ ch)).bytes =
      some (tagDigest keys.segment (segmentInitial ++ ch)) := by
    unfold Codec.Digest.ofBytes?
    rw [dif_pos (by rw [htsz]; rfl)]
  have hol := openLog_empty keys.segment c.recordBytesMax (indexed mark step) (w₀, #[], seg.size)
    (tagDigest keys.segment (segmentInitial ++ ch)).bytes
    ((tagDigest keys.segment (segmentInitial ++ ch)).bytes.extract tagBytes tagBytes) (by simp)
  have hext : (tagDigest keys.segment (segmentInitial ++ ch)).bytes.extract 0 tagBytes =
      (tagDigest keys.segment (segmentInitial ++ ch)).bytes := by
    rw [← htsz, extract_zero_size]
  have hoe : seg.size = frameSize (origin w₀) := by rw [ho, hch, hss]; rfl
  unfold openWith
  simp only [show ¬ frameMax c.baseRecordMax < (file).size by omega, if_false, hb, tailRead_self,
    show ¬ seg.size < tagBytes by omega, segReader, pure_bind, htag]
  simp only [htsz, Nat.add_zero, ne_eq, not_true_eq_false, if_false]
  rw [hor]
  simp only [lastAt, if_true, ByteArray.size_empty, Nat.zero_mul,
    Nat.lt_irrefl, if_false, indexNamed_zero]
  simp only [hext, hol, hofs, not_true_eq_false, ByteArray.size_extract,
    ByteArray.size_empty, Nat.zero_add, Nat.min_self, Nat.sub_self, lastEntry, lastFrameFault, eq_true hoe,
    ↓reduceIte]
  exact ⟨_, rfl, rfl, rfl, rfl, Nat.add_zero _⟩

end Nanodregg.Host
