/-
# Host.Proofs.Base — open reads one base and at most `tailMax` of log (HOST-14 condition 4)

* `recover_validLen_le` — recovery never ends past the bytes it was given;
* `tailRead_ok` — open reads exactly the segment after the base, and only if it is at most
  `tailMax` long;
* `openWith_reads` — the one open (`openWith`, generic in its monad: `IO` over the file for the
  Store, `Id` over bytes for the simulation, and here a reader that records its calls and answers
  anything) reads a base file of at most one base frame and asks for EXACTLY two ranges of segment,
  `[base offset - 32, size)` (the base's tag and a tail of at most `tailMax` bytes) and
  `[0, originLen offset)` (the origin frame, at most `originMax` bytes, HOST-25); the position it
  opens to is within the tail (a short read is refused inside `openWith`, so no reader can bypass
  the bound);
* `openWith_origin` / `openWith_originFault` (HOST-25) — an open that succeeds read a frame at 0
  that verifies from `segmentInitial` and states `origin b.world`; a segment whose origin frame
  fails is refused `corrupt 0` (`originFault_corrupt`) or `foreignOrigin` (`originFault_foreign`);
  `genesisImage_origin` and `Record.step_origin` say the check refuses no Store this Host writes
  (at genesis, and past it: a record keeps the World's origin, KERNEL's `fold_origin`);
* `openWith_anchored` / `openWith_foreign` (HOST-18) — an open that succeeds found the base's own
  tag in the 32 bytes before the base's offset; a segment without it is refused `foreignSegment`
  (never read as a torn tail, so the writer truncates nothing);
* `read_stamped` / `read_shapeMismatch` (D2, HOST-20) — a base that reads carries the running
  shape stamp at the head of its verified record; a verified base whose head is another stamp is
  refused `shapeMismatch` with both stamps, before its bytes are decoded;
* `within_after_seal` — once the newest durable base sits at the loop's position, every frame up to
  the record bound fits. NOT proved: that `Loop.makeRoom`'s inline seal leaves the base there (it
  is IO over `Checkpoint.write`); the loop's `else` branch after `makeRoom` is therefore a named
  stop (`recordTooLarge`), not an assumption.
-/
import Host.Open
import Host.Loop
import Host.Proofs.Log
import Host.Record
import Kernel.Proofs.Origin
import Kernel.Proofs.RootedFold
import Kernel.Proofs.Journal
import Kernel.Proofs.Refusals
import Codec.Proofs.Raw
import Host.Proofs.Index

namespace Nanodregg.Host

open Nanodregg.Host.Log

theorem go_validLen_le (s : Sealer) (recordMax : Nat) (log : ByteArray) :
    ∀ (fuel off : Nat) (prev : ByteArray) (acc : List ByteArray), off ≤ log.size →
      (go s recordMax log fuel off prev acc).validLen ≤ log.size := by
  intro fuel
  induction fuel with
  | zero => intro off prev acc h; exact h
  | succ fuel ih =>
    intro off prev acc hoff
    simp only [go]
    split
    · exact hoff
    · rename_i r o t hstep
      exact ih o t (r :: acc) (step_next hstep).2.1

theorem recover_validLen_le (s : Sealer) (recordMax : Nat) (initial log : ByteArray) :
    (recover s recordMax initial log).validLen ≤ log.size :=
  go_validLen_le s recordMax log _ 0 initial [] (Nat.zero_le _)

theorem openLog_validLen_le {W F : Type} {s : Sealer} {recordMax : Nat} {step : W → ByteArray → Except F W}
    {w₀ : W} {initial log : ByteArray} {o : Opened W} (h : openLog s recordMax step w₀ initial log = .ok o) :
    o.validLen ≤ log.size := by
  have hv := recover_validLen_le s recordMax initial log
  unfold openLog at h
  generalize recover s recordMax initial log = rv at h hv
  simp only at h
  split at h
  · cases h
  · split at h
    · cases h; exact hv
    · cases h

theorem tailRead_ok {c : Cadence} {baseBytes offset size n : Nat}
    (h : tailRead c baseBytes offset size = .ok n) : offset + n = size ∧ n ≤ c.tailMax baseBytes := by
  unfold tailRead at h
  split at h
  · cases h
  · split at h
    · cases h
    · cases h; omega

/-- The one open reads a base file of at most one base frame, and asks its readers for EXACTLY
three ranges, in order: of the segment `[base offset - 32, size)`, the base's tag on disk and the
tail after it, the tail at most `tailMax` long; then `[0, originLen offset)`, the origin frame
(HOST-25); then of `index.log` the ONE entry the base names last (`lastAt`: `entryBytes` bytes,
none at count 0), with the count at most `indexMax` and every counted entry within the file
(HOST-33: open reads one entry, not the index). The position it opens to lies in the tail, and
the orphan bytes it reports are exactly the file's bytes past the counted entries, so the writer's
truncation (`openWriter`) never drops a byte of an entry the base counts. Stated over
readers that record every range they are asked for (in one log) and answer with arbitrary bytes
`answer off len` / `answerI off len`, of any length (a short read is `openWith`'s to refuse). -/
theorem openWith_reads {W F : Type} (keys : Keys) (c : Cadence) (world : Codec.Stream W)
    (mark : W → Nat × ByteArray) (origin : W → ByteArray) (step : W → ByteArray → Except F W) (file : ByteArray) (size indexSize : Nat) (answer answerI : Nat → Nat → ByteArray)
    {o : Opening W} {log : List (Nat × Nat)}
    (h : (openWith keys c world mark origin step file size indexSize (m := StateM (List (Nat × Nat)))
      (fun off len => modifyGet fun l => (.ok (answerI off len), l ++ [(off, len)]))
      (fun off len => modifyGet fun l => (.ok (answer off len), l ++ [(off, len)]))).run [] = (.ok o, log)) :
    file.size ≤ Log.frameMax c.baseRecordMax ∧ Log.tagBytes ≤ o.sealed.offset ∧
    ∃ len, log = [(o.sealed.offset - Log.tagBytes, Log.tagBytes + len), (0, originLen o.sealed.offset),
        lastAt keys o.sealed.index.count] ∧
      o.sealed.offset + len = size ∧
      len ≤ c.tailMax o.sealed.bytes ∧
      o.sealed.offset ≤ o.pos.offset ∧ o.pos.offset ≤ o.sealed.offset + len ∧
      o.sealed.index.count ≤ indexMax ∧
      o.sealed.index.count * entryBytes keys + o.orphan = indexSize := by
  simp only [openWith] at h
  split at h
  · simp only [StateT.run, StateT.pure, pure] at h; injection h with h1; cases h1
  · rename_i hfile
    split at h
    · simp only [StateT.run, StateT.pure, pure] at h; injection h with h1; cases h1
    · rename_i b bb dg hb
      split at h
      · simp only [StateT.run, StateT.pure, pure] at h; injection h with h1; cases h1
      · rename_i len hlen
        obtain ⟨hs, hle⟩ := tailRead_ok hlen
        split at h
        · simp only [StateT.run, StateT.pure, pure] at h; injection h with h1; cases h1
        · rename_i hoff
          simp only [bind, modifyGet, MonadStateOf.modifyGet, StateT.run, StateT.bind,
            StateT.modifyGet, List.nil_append] at h
          split at h
          · simp only [StateT.pure, pure] at h; injection h with h1; cases h1
          · rename_i hsz
            split at h
            · simp only [StateT.pure, pure] at h; injection h with h1; cases h1
            · simp only [bind, StateT.bind, StateT.modifyGet, List.singleton_append] at h
              by_cases hq : (answer 0 (originLen b.offset)).size ≠ originLen b.offset
              · rw [if_pos hq] at h
                simp only [StateT.pure, pure] at h; injection h with h1; cases h1
              rw [if_neg hq] at h
              cases hof : originFault (F := F) keys.segment (answer 0 (originLen b.offset)) (origin b.world) with
              | some e => rw [hof] at h; simp only [StateT.pure, pure] at h; injection h with h1; cases h1
              | none =>
              rw [hof] at h
              simp only at h
              by_cases hw : indexMax < b.indexCount
              · rw [if_pos hw] at h; simp only [StateT.pure, pure] at h; injection h with h1; cases h1
              rw [if_neg hw] at h
              by_cases hi : indexSize < b.indexCount * entryBytes keys
              · rw [if_pos hi] at h; simp only [StateT.pure, pure] at h; injection h with h1; cases h1
              rw [if_neg hi] at h
              simp only [bind, StateT.bind, StateT.modifyGet] at h
              by_cases hq2 : (answerI (lastAt keys b.indexCount).1 (lastAt keys b.indexCount).2).size ≠
                  (lastAt keys b.indexCount).2
              · rw [if_pos hq2] at h
                simp only [StateT.pure, pure] at h; injection h with h1; cases h1
              rw [if_neg hq2] at h
              cases hix : indexNamed (keys.forStore (origin b.world)) b.indexCount b.indexLast
                  (answerI (lastAt keys b.indexCount).1 (lastAt keys b.indexCount).2) with
              | some e => rw [hix] at h; simp only [StateT.pure, pure] at h; injection h with h1; cases h1
              | none =>
              rw [hix] at h
              simp only at h
              generalize hop : openLog keys.segment c.recordBytesMax (indexed mark step)
                (b.world, #[], b.offset) b.tag.bytes
                ((answer (b.offset - Log.tagBytes) (Log.tagBytes + len)).extract Log.tagBytes
                  (answer (b.offset - Log.tagBytes) (Log.tagBytes + len)).size) = res at h
              cases res with
              | error e => simp only [StateT.pure, pure] at h; injection h with h1; cases h1
              | ok op =>
                simp only at h
                cases htag : Codec.Digest.ofBytes? op.lastTag with
                | none => rw [htag] at h; simp only [StateT.pure, pure] at h; injection h with h1; cases h1
                | some tag =>
                  rw [htag] at h
                  simp only [StateT.pure, pure] at h
                  obtain ⟨rfl, rfl⟩ := h
                  have hv := openLog_validLen_le hop
                  have hsz' : (answer (b.offset - Log.tagBytes) (Log.tagBytes + len)).size = Log.tagBytes + len := by
                    simpa using hsz
                  refine ⟨by omega, show Log.tagBytes ≤ b.offset by omega, len, by simp, hs, hle,
                    Nat.le_add_right _ _, ?_, show b.indexCount ≤ indexMax by omega,
                    show b.indexCount * entryBytes keys + (indexSize - b.indexCount * entryBytes keys) = indexSize by omega⟩
                  show b.offset + op.validLen ≤ b.offset + len
                  simp only [ByteArray.size_extract, hsz'] at hv
                  omega

/-- An open that SUCCEEDS found the base's own tag on disk right before the base's offset: whatever
segment it was handed, the 32 bytes before the offset are the tag of the base it decoded (HOST-18). -/
theorem openWith_anchored {W F : Type} (keys : Keys) (c : Cadence) (world : Codec.Stream W)
    (mark : W → Nat × ByteArray) (origin : W → ByteArray) (step : W → ByteArray → Except F W) (file idx seg : ByteArray)
    {o : Opening W}
    (h : Id.run (openWith keys c world mark origin step file seg.size idx.size (segReader idx) (segReader seg)) = .ok o) :
    ∃ b bb d, Base.read keys c world file = .ok (b, bb, d) ∧ Log.tagBytes ≤ b.offset ∧
      seg.extract (b.offset - Log.tagBytes) b.offset = b.tag.bytes := by
  unfold openWith at h
  split at h
  · cases h
  · rename_i hfile
    split at h
    · cases h
    · rename_i b bb dg hb
      split at h
      · cases h
      · rename_i len hlen
        obtain ⟨hs, _⟩ := tailRead_ok hlen
        split at h
        · cases h
        · rename_i hoff
          refine ⟨b, bb, dg, hb, by omega, ?_⟩
          simp only [segReader, pure_bind] at h
          split at h
          · cases h
          · rename_i hhead
            have e : (seg.extract (b.offset - Log.tagBytes) (b.offset - Log.tagBytes + (Log.tagBytes + len))).extract 0 Log.tagBytes
                = seg.extract (b.offset - Log.tagBytes) b.offset := by
              rw [ByteArray.extract_extract, Nat.add_zero,
                show min (b.offset - Log.tagBytes + Log.tagBytes) (b.offset - Log.tagBytes + (Log.tagBytes + len))
                  = b.offset by omega]
            split at h
            · cases h
            · rename_i hh
              rw [← e]; exact Classical.not_not.mp hh

/-- The foreign-segment plant's theorem: when the base reads and its tail is within bounds, a
segment whose 32 bytes before the base's offset are not the base's tag is refused
`foreignSegment`, by the same `openWith` every Store runs (never read as a torn tail). -/
theorem openWith_foreign {W F : Type} (keys : Keys) (c : Cadence) (world : Codec.Stream W)
    (mark : W → Nat × ByteArray) (origin : W → ByteArray) (step : W → ByteArray → Except F W) (file idx seg : ByteArray)
    {b : Base W} {bb : Nat} {d : ByteArray} {len : Nat}
    (hfile : file.size ≤ Log.frameMax c.baseRecordMax)
    (hb : Base.read keys c world file = .ok (b, bb, d))
    (hlen : tailRead c bb b.offset seg.size = .ok len)
    (hf : seg.extract (b.offset - Log.tagBytes) b.offset ≠ b.tag.bytes) :
    Id.run (openWith keys c world mark origin step file seg.size idx.size (segReader idx) (segReader seg)) = .error (.base .foreignSegment) := by
  obtain ⟨hs, _⟩ := tailRead_ok hlen
  unfold openWith
  simp only [show ¬ Log.frameMax c.baseRecordMax < file.size by omega, if_false, hb, hlen]
  by_cases hoff : b.offset < Log.tagBytes
  · simp only [hoff, if_true]; rfl
  · simp only [hoff, if_false, segReader, pure_bind]
    have e : (seg.extract (b.offset - Log.tagBytes) (b.offset - Log.tagBytes + (Log.tagBytes + len))).extract 0 Log.tagBytes
        = seg.extract (b.offset - Log.tagBytes) b.offset := by
      rw [ByteArray.extract_extract, Nat.add_zero,
        show min (b.offset - Log.tagBytes + Log.tagBytes) (b.offset - Log.tagBytes + (Log.tagBytes + len))
          = b.offset by omega]
    have hsz : (seg.extract (b.offset - Log.tagBytes) (b.offset - Log.tagBytes + (Log.tagBytes + len))).size
        = Log.tagBytes + len := by
      rw [ByteArray.size_extract]; omega
    rw [if_neg (by rw [hsz]; exact fun h => h rfl), e, if_pos hf]
    rfl
/-- **D2: a base that reads was written under the running shapes.** Its frame verified under the
Store's base sealer, and the first `stampBytes` of its record are `keys.shapes`. -/
theorem read_stamped {W : Type} (keys : Keys) (c : Cadence) (world : Codec.Stream W) (file : ByteArray)
    {b : Base W} {bb : Nat} {d : ByteArray} (h : Base.read keys c world file = .ok (b, bb, d)) :
    ∃ r, Log.frameAt keys.base c.baseRecordMax file 0 baseInitial = some r ∧
      r.record.extract 0 stampBytes = keys.shapes.bytes := by
  unfold Base.read at h
  split at h
  · cases h
  · split at h
    · cases h
    · rename_i r hr
      refine ⟨r, hr, ?_⟩
      by_cases hs : r.record.extract 0 stampBytes = keys.shapes.bytes
      · exact hs
      · exfalso
        split at h
        · cases h
        · simp only [ne_eq, hs, not_false_eq_true, if_true] at h
          cases h

/-- **D2: an old shape refuses by name.** A base file that verifies, but whose record starts with
another stamp, is refused `shapeMismatch stored running`, and nothing after the stamp is decoded. -/
theorem read_shapeMismatch {W : Type} (keys : Keys) (c : Cadence) (world : Codec.Stream W)
    (file : ByteArray) (r : Log.Read)
    (hsize : file.size ≤ Log.frameMax c.baseRecordMax)
    (hr : Log.frameAt keys.base c.baseRecordMax file 0 baseInitial = some r)
    (hn : r.next = file.size)
    (hs : r.record.extract 0 stampBytes ≠ keys.shapes.bytes) :
    Base.read keys c world file =
      .error (.shapeMismatch (r.record.extract 0 stampBytes).data keys.shapes.bytes.data) := by
  unfold Base.read
  simp only [show ¬ Log.frameMax c.baseRecordMax < file.size by omega, if_false, hr, hn,
    ne_eq, not_true_eq_false]
  rw [if_pos hs]

/-! ## The base codec -/

/-- The base record's codec reads back every base whose World its World codec reads back (`P`)
and whose two u64 fields are below 2^64; the two tags are digests, read back whole. Generic in
the World codec; at the deployed one (`Codec.Kernel.world_lawfulOn`, exact since KERNEL-41 deleted
`World.Equiv`) `P` is `World.CodecFits`. -/
theorem Base.codec_lawfulOn {W : Type} {P : W → Prop} {world : Codec.Stream W}
    (hw : Codec.Stream.LawfulOn P world) :
    Codec.Stream.LawfulOn (fun b : Base W => P b.world ∧ b.offset < 2 ^ 64 ∧ b.indexCount < 2 ^ 64)
      (Base.codec world) := by
  have h := Codec.Stream.refine_lawfulOn
    (Codec.Stream.product_lawfulOn hw (Codec.Stream.product_lawfulOn Codec.Stream.nat64_lawfulOn
      (Codec.Stream.product_lawfulOn Codec.Stream.digest_lawful.on
        (Codec.Stream.product_lawfulOn Codec.Stream.nat64_lawfulOn Codec.Stream.digest_lawful.on))))
    "host/base/index-count" (accept := fun (w, o, t, io, it) => some (⟨w, o, t, io, it⟩ : Base W))
    (back := fun b => (b.world, b.offset, b.tag, b.indexCount, b.indexLast))
    (fun _ _ => rfl) (fun x y hxy => by obtain ⟨a, b, c, d, e⟩ := x; cases hxy; rfl)
  exact h.mono (fun _ hv => ⟨hv.1, hv.2.1, hv.2.2.2.1⟩) (fun _ hv => ⟨hv.1, hv.2.1, trivial, hv.2.2, trivial⟩)

/-- **The backup order (HOST-30).** Every append-only file of the layout is copied after
`base.world` in `backupOrder` (an ORDER fact over the data; that a backup in this order then holds
each prefix the copied base names rests on those files being append-only and the page being synced
before `installBase`, which `fileCheckpoint` does and no theorem states). -/
theorem backupOrder_appendOnly_after_base :
    ∀ f ∈ Store.layout, f.kind = .appendOnly →
      f.name ∈ Store.backupOrder ∧ Store.backupOrder.idxOf "base.world" < Store.backupOrder.idxOf f.name := by
  decide

theorem backupOrder_covers : ∀ f ∈ Store.layout, f.kind ≠ .transient → f.name ∈ Store.backupOrder := by
  decide

theorem within_after_seal (c : Cadence) (sealed : Sealed) (n : Nat) (hn : n ≤ Log.frameMax c.recordBytesMax) :
    withinTail c sealed sealed.offset n = true := by
  unfold withinTail Cadence.tailMax
  simp only [decide_eq_true_eq]
  omega

/-! ## The origin frame (HOST-25) -/

/-- `originFault` passes exactly when the frame at 0 verifies from `segmentInitial` and states
`expected`. -/
theorem originFault_none_iff {F : Type} (s : Sealer) (head expected : ByteArray) :
    originFault (F := F) s head expected = none ↔
      ∃ r, frameAt s chainBytesMax head 0 segmentInitial = some r ∧ r.record = expected := by
  unfold originFault
  split
  · rename_i hr; simp [hr]
  · rename_i r hr
    by_cases he : r.record = expected
    · simp [he, hr]
    · simp [he, hr]

/-- **HOST-25: an open that SUCCEEDS read the base World's own origin at offset 0.** Whatever
segment it was handed, the frame at 0 verifies from `segmentInitial` under the segment sealer and
its record is `origin b.world`, the genesis chain of the decoded base World's origin. -/
theorem openWith_origin {W F : Type} (keys : Keys) (c : Cadence) (world : Codec.Stream W)
    (mark : W → Nat × ByteArray) (origin : W → ByteArray) (step : W → ByteArray → Except F W)
    (file idx seg : ByteArray) {o : Opening W}
    (h : Id.run (openWith keys c world mark origin step file seg.size idx.size (segReader idx) (segReader seg)) = .ok o) :
    ∃ b bb d r, Base.read keys c world file = .ok (b, bb, d) ∧
      frameAt keys.segment chainBytesMax (seg.extract 0 (originLen b.offset)) 0 segmentInitial = some r ∧
      r.record = origin b.world := by
  unfold openWith at h
  split at h
  · cases h
  · split at h
    · cases h
    · rename_i b bb dg hb
      split at h
      · cases h
      · split at h
        · cases h
        · simp only [segReader, pure_bind] at h
          split at h
          · cases h
          · split at h
            · cases h
            · simp only [Nat.zero_add] at h
              split at h
              · cases h
              · split at h
                · cases h
                · rename_i hnone
                  obtain ⟨r, hr, he⟩ := (originFault_none_iff _ _ _).mp hnone
                  exact ⟨b, bb, dg, r, hb, hr, he⟩

/-- **An open that succeeds verified the entry the base names** (HOST-33 condition 2,
`open_verifies_named`). Whatever `index.log` it was handed: the file holds every entry the opened
base counts, and either the base counts none and names no last tag, or the bytes at the last
counted entry read back as an entry AT THAT POSITION (its tag verified there, `Entry.read_sound`)
whose tag is the `indexLast` the base names, both under the keys of THIS Store (`Keys.forStore`
of the decoded base World's origin chain, which the origin frame states: HOST-25). That binds the
base's count to an entry the writer of this Store sealed. It says nothing about the entries before it: a page checks each one it reads
(`Host.Proofs.Page.build_located`), and `host check` checks all of them (`indexClean_none`). -/
theorem openWith_verifies_named {W F : Type} (keys : Keys) (c : Cadence) (world : Codec.Stream W)
    (mark : W → Nat × ByteArray) (origin : W → ByteArray) (step : W → ByteArray → Except F W)
    (file idx seg : ByteArray) {o : Opening W}
    (h : Id.run (openWith keys c world mark origin step file seg.size idx.size (segReader idx) (segReader seg)) = .ok o) :
    ∃ b bb d, Base.read keys c world file = .ok (b, bb, d) ∧
    o.sealed.index.count * entryBytes keys ≤ idx.size ∧
      ((o.sealed.index.count = 0 ∧ o.sealed.index.last = Codec.Digest.zero) ∨
        (0 < o.sealed.index.count ∧ ∃ e,
          Entry.read (keys.forStore (origin b.world)) (o.sealed.index.count - 1)
            (idx.extract ((o.sealed.index.count - 1) * entryBytes keys)
              ((o.sealed.index.count - 1) * entryBytes keys + entryBytes keys)) = some e ∧
          e.tag (keys.forStore (origin b.world)) (o.sealed.index.count - 1) = o.sealed.index.last)) := by
  unfold openWith at h
  split at h
  · cases h
  · split at h
    · cases h
    · rename_i b bb dg hb
      split at h
      · cases h
      · split at h
        · cases h
        · simp only [segReader, pure_bind] at h
          split at h
          · cases h
          · split at h
            · cases h
            · simp only [Nat.zero_add] at h
              split at h
              · cases h
              · split at h
                · cases h
                · split at h
                  · cases h
                  · split at h
                    · cases h
                    · rename_i hshort
                      split at h
                      · cases h
                      · split at h
                        · cases h
                        · rename_i hnamed
                          split at h
                          · cases h
                          · split at h
                            · cases h
                            · cases h
                              refine ⟨b, bb, dg, hb, by simpa using hshort, ?_⟩
                              rcases indexNamed_none hnamed with ⟨h0, hl⟩ | ⟨hpos, e, he, ht⟩
                              · exact Or.inl ⟨h0, hl⟩
                              · refine Or.inr ⟨hpos, e, ?_, ht⟩
                                rw [lastAt_read keys _ hpos] at he
                                exact he

/-- **HOST-25, the plants' statement over the real `openWith`.** When the base reads, its tail is
within bounds and its tag sits before its offset, a segment whose origin frame fails the check is
refused with `originFault`'s verdict: `corrupt 0` when the frame at 0 does not verify,
`foreignOrigin` when it verifies but states another chain. -/
theorem openWith_originFault {W F : Type} (keys : Keys) (c : Cadence) (world : Codec.Stream W)
    (mark : W → Nat × ByteArray) (origin : W → ByteArray) (step : W → ByteArray → Except F W)
    (file idx seg : ByteArray) {b : Base W} {bb : Nat} {d : ByteArray} {len : Nat} {f : StoreFault F}
    (hfile : file.size ≤ Log.frameMax c.baseRecordMax)
    (hb : Base.read keys c world file = .ok (b, bb, d))
    (hlen : tailRead c bb b.offset seg.size = .ok len)
    (hoff : Log.tagBytes ≤ b.offset)
    (hanchor : seg.extract (b.offset - Log.tagBytes) b.offset = b.tag.bytes)
    (hf : originFault keys.segment (seg.extract 0 (originLen b.offset)) (origin b.world) = some f) :
    Id.run (openWith keys c world mark origin step file seg.size idx.size (segReader idx) (segReader seg)) = .error f := by
  obtain ⟨hs, _⟩ := tailRead_ok hlen
  unfold openWith
  simp only [show ¬ Log.frameMax c.baseRecordMax < file.size by omega, if_false, hb, hlen,
    show ¬ b.offset < Log.tagBytes by omega, segReader, pure_bind, Nat.zero_add]
  have e : (seg.extract (b.offset - Log.tagBytes) (b.offset - Log.tagBytes + (Log.tagBytes + len))).extract 0 Log.tagBytes
      = seg.extract (b.offset - Log.tagBytes) b.offset := by
    rw [ByteArray.extract_extract, Nat.add_zero,
      show min (b.offset - Log.tagBytes + Log.tagBytes) (b.offset - Log.tagBytes + (Log.tagBytes + len))
        = b.offset by omega]
  have hsz : (seg.extract (b.offset - Log.tagBytes) (b.offset - Log.tagBytes + (Log.tagBytes + len))).size
      = Log.tagBytes + len := by
    rw [ByteArray.size_extract]; omega
  have hsz0 : (seg.extract 0 (originLen b.offset)).size = originLen b.offset := by
    rw [ByteArray.size_extract]; unfold originLen; omega
  rw [if_neg (by rw [hsz]; exact fun h => h rfl), e, if_neg (by rw [hanchor]; exact fun h => h rfl),
    if_neg (by rw [hsz0]; exact fun h => h rfl), hf]
  rfl

/-- `corrupt 0` is the verdict on an origin frame that does not verify. -/
theorem originFault_corrupt {F : Type} (s : Sealer) (head expected : ByteArray)
    (h : frameAt s chainBytesMax head 0 segmentInitial = none) :
    originFault (F := F) s head expected = some (.log (.corrupt 0)) := by
  unfold originFault; rw [h]

/-- `foreignOrigin` is the verdict on an origin frame that verifies and states another chain. -/
theorem originFault_foreign {F : Type} (s : Sealer) (head expected : ByteArray) (r : Read)
    (h : frameAt s chainBytesMax head 0 segmentInitial = some r) (he : r.record ≠ expected) :
    originFault (F := F) s head expected = some (.base .foreignOrigin) := by
  unfold originFault; rw [h]; simp [he]

/-- **HOST-25, completeness at genesis.** The segment genesis writes passes the origin check of
the open that reads its genesis base (at offset `segment.size`), given that `origin` is the
chain `mark` writes at genesis (KERNEL's `World.genesisChain` equation, `genesis_chain`) and that
the chain fits `chainBytesMax`. -/
theorem genesisImage_origin {W F : Type} (keys : Keys) (c : Cadence) (world : Codec.Stream W)
    (mark : W → Nat × ByteArray) (origin : W → ByteArray) (w₀ : W) {img : Image}
    (h : genesisImage keys c world mark w₀ = .ok img)
    (hsize : (mark w₀).2.size ≤ chainBytesMax) (ho : origin w₀ = (mark w₀).2) :
    originFault (F := F) keys.segment (img.segment.extract 0 (originLen img.segment.size)) (origin w₀) = none := by
  unfold genesisImage at h
  dsimp only at h
  split at h
  · cases h
  · cases h
    have hfs := size_frame keys.segment segmentInitial (mark w₀).2
    have hlen : originLen (frame keys.segment segmentInitial (mark w₀).2).size
        = (frame keys.segment segmentInitial (mark w₀).2).size := by
      unfold originLen originMax Log.frameMax; rw [hfs]; omega
    have hx : (frame keys.segment segmentInitial (mark w₀).2).extract 0
        (frame keys.segment segmentInitial (mark w₀).2).size = frame keys.segment segmentInitial (mark w₀).2 := by
      simp
    have hr := frameAt_frame keys.segment (recordMax := chainBytesMax) ByteArray.empty segmentInitial
      (mark w₀).2 ByteArray.empty hsize (by unfold chainBytesMax at hsize; omega)
    simp only [ByteArray.empty_append, ByteArray.append_empty, ByteArray.size_empty] at hr
    rw [hlen, hx, originFault_none_iff]
    exact ⟨_, hr, ho.symm⟩

/-- A record's run (`Record.runRooted`) that succeeds is a `Kernel.Rooted` run: every step
taken, every stated roots digest the one the step reached (HOST-29). -/
theorem Record.runRooted_ok {D F : Type} [Ord D] [DecidableEq D]
    {admit : Kernel.World D → Kernel.Step D → Except F (Kernel.World D)} {root : Kernel.World D → D} :
    ∀ {i : Nat} {w w' : Kernel.World D} {ps : List (Kernel.Step D × D)},
      Record.runRooted admit root i w ps = .ok w' → Kernel.Rooted admit root w ps w'
  | i, w, w', [], h => by
      simp only [Record.runRooted] at h; cases h; rfl
  | i, w, w', (t, r) :: rest, h => by
      unfold Record.runRooted at h
      split at h
      · cases h
      · rename_i w₁ ha
        split at h
        · rename_i hr
          exact ⟨w₁, ha, hr.symm, Record.runRooted_ok h⟩
        · cases h

/-- **HOST-29: a record that opens is a rooted run of the pairs it decodes to.** -/
theorem Record.step_rooted {D F : Type} [Ord D] [DecidableEq D] {dc : Codec.Stream D}
    {admit : Kernel.World D → Kernel.Step D → Except F (Kernel.World D)} {root : Kernel.World D → D}
    {w w' : Kernel.World D} {r : ByteArray} (h : Record.step dc admit root w r = .ok w') :
    ∃ ps, (Record.codec dc).decode r = .ok ps ∧ Kernel.Rooted admit root w ps w' := by
  unfold Record.step Record.stepTurns at h
  split at h
  · cases h
  · rename_i ps hd
    split at h
    · cases h
    · rename_i w₁ hr
      simp only [Except.map, Except.ok.injEq] at h
      subst h
      exact ⟨ps, hd, Record.runRooted_ok hr⟩

/-- **HOST-25, completeness past genesis.** A record the writer's reopen accepts keeps the World's
origin (`Record.step_rooted`, then KERNEL's `fold_origin`), so every later base's World states the
same origin as the genesis World whose chain the origin frame holds. -/
theorem Record.step_origin {D : Type} [Ord D] [DecidableEq D] {dc : Codec.Stream D}
    {E : Kernel.Env D} {w w' : Kernel.World D} {r : ByteArray}
    (h : Record.step dc (Kernel.World.step E) (Kernel.World.roots E) w r = .ok w') : w'.origin = w.origin := by
  obtain ⟨_, _, hr⟩ := Record.step_rooted h
  exact Kernel.Receive.fold_origin (Kernel.RootedFold.fold hr)


/-- **The writer's reopen keeps the journal's invariant (KERNEL-41).** Folding records with the
writer's step (`Record.step` over `World.step` and `World.roots`) from a World whose journal is
`JournalOk` (a canonical trie, every entry inside its window, heights distinct) reaches a World
whose journal is `JournalOk`: every record that opens is steps taken (`Record.step_rooted`,
`RootedFold.fold`), and KERNEL's `fold_journalOk` carries it. What the Host's journal lookups
(`Host.Proofs.Serve`) rest on after an open. -/
theorem Record.foldlM_journalOk {D : Type} [Ord D] [DecidableEq D] {dc : Codec.Stream D}
    {E : Kernel.Env D} :
    ∀ {w w' : Kernel.World D} {rs : List ByteArray}, w.JournalOk E →
      rs.foldlM (Record.step dc (Kernel.World.step E) (Kernel.World.roots E)) w = .ok w' → w'.JournalOk E
  | w, w', [], hw, h => by
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h
    exact h ▸ hw
  | w, w', r :: rs, hw, h => by
    simp only [List.foldlM_cons, bind, Except.bind] at h
    split at h
    · cases h
    · rename_i w₁ h₁
      obtain ⟨_, _, hr⟩ := Record.step_rooted h₁
      exact Record.foldlM_journalOk (Kernel.fold_journalOk hw (Kernel.RootedFold.fold hr)) h

/-- **The writer's reopen keeps the refusals' invariant (KERNEL-44)**, as `Record.foldlM_journalOk`
keeps the journal's: every record that opens is steps taken, and KERNEL's `fold_refusalsOk` carries
`RefusalsOk` (a canonical refusals trie, every leaf the window's). -/
theorem Record.foldlM_refusalsOk {D : Type} [Ord D] [DecidableEq D] {dc : Codec.Stream D}
    {E : Kernel.Env D} :
    ∀ {w w' : Kernel.World D} {rs : List ByteArray}, w.RefusalsOk E →
      rs.foldlM (Record.step dc (Kernel.World.step E) (Kernel.World.roots E)) w = .ok w' → w'.RefusalsOk E
  | w, w', [], hw, h => by
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h
    exact h ▸ hw
  | w, w', r :: rs, hw, h => by
    simp only [List.foldlM_cons, bind, Except.bind] at h
    split at h
    · cases h
    · rename_i w₁ h₁
      obtain ⟨_, _, hr⟩ := Record.step_rooted h₁
      exact Record.foldlM_refusalsOk (Kernel.fold_refusalsOk hw (Kernel.RootedFold.fold hr)) h

end Nanodregg.Host
