/-
# Host.Proofs.Base — open reads one base and at most `tailMax` of log (HOST-14 condition 4)

* `recover_validLen_le` — recovery never ends past the bytes it was given;
* `tailRead_ok` — open reads exactly the segment after the base, and only if it is at most
  `tailMax` long;
* `openWith_reads` — the one open (`openWith`, generic in its monad: `IO` over the file for the
  Store, `Id` over bytes for the simulation, and here a reader that records its calls and answers
  anything) reads a base file of at most one base frame and asks for one range of segment,
  `[base offset - 32, size)` (the base's tag and a tail of at most `tailMax` bytes), one index entry,
  and at most one more, the record the base's last entry names, ending at the base's offset (HOST-63); the position it
  opens to is within the tail (a short read is refused inside `openWith`, so no reader can bypass
  the bound);
* `openWith_header` / `openWith_headerFault` (HOST-64, carrying HOST-25) — an open that succeeds
  was handed a checkpoint header for the base's own file that verifies under the Store's checkpoint
  sealer and states `origin b.world` and the base's position (offset, tag, steps, chain, entry
  count); a header that fails is refused `checkpointCorrupt` (`headerFault_corrupt`),
  `foreignOrigin` (`headerFault_foreignOrigin`) or `foreignSegment` (`headerFault_foreignSegment`);
  `headerFault_bytes`, `genesisImage_header` and `Record.step_origin` say the check refuses no
  header this Host writes (each header reads back at its own place; a record keeps the World's
  origin, KERNEL's `fold_origin`);
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

theorem lastRange_some {rm B a len : Nat} {e : Entry} (h : lastRange rm B e = some (a, len)) :
    Log.tagBytes ≤ e.offset ∧ e.offset < B ∧ B - e.offset ≤ Log.frameMax rm ∧ a = e.offset - Log.tagBytes ∧
      len = B - e.offset + Log.tagBytes := by
  unfold lastRange at h
  split at h
  · rename_i hc; cases h; exact ⟨hc.1, hc.2.1, hc.2.2, rfl, rfl⟩
  · cases h

/-- The last-entry check (HOST-63) reads only bytes before the base's offset. -/
theorem lastFrameFault_congr {F : Type} {s : Log.Sealer} {rm B : Nat} {S S' : ByteArray} (e? : Option Entry)
    (hS : ∀ i j, j ≤ B → S.extract i j = S'.extract i j) :
    Id.run (lastFrameFault (F := F) s rm B e? (segReader S)) =
      Id.run (lastFrameFault (F := F) s rm B e? (segReader S')) := by
  cases e? with
  | none => rfl
  | some e =>
    simp only [lastFrameFault, segReader, bind, pure]
    split
    · rfl
    · rename_i a len hlr
      obtain ⟨h32, hlt, -, rfl, rfl⟩ := lastRange_some hlr
      rw [hS _ _ (by omega)]

/-- The last-entry check (HOST-63) asks for at most ONE range, ending at the base's offset and at
most a frame and a tag long, over a reader that records its calls. -/
theorem lastFrameFault_reads {F : Type} (s : Log.Sealer) (rm B : Nat) (e? : Option Entry)
    (answer : Nat → Nat → ByteArray) (st : List (Nat × Nat)) :
    ∃ v extra, (lastFrameFault (F := F) (m := StateM (List (Nat × Nat))) s rm B e?
        (fun off len => StateT.modifyGet fun l => (Except.ok (answer off len), l ++ [(off, len)]))) st =
        (v, st ++ extra) ∧ extra.length ≤ 1 ∧
      ∀ p ∈ extra, p.1 + p.2 = B ∧ p.2 ≤ Log.frameMax rm + Log.tagBytes := by
  cases e? with
  | none => exact ⟨none, [], by simp [lastFrameFault, pure, StateT.pure], by simp, by simp⟩
  | some e =>
    cases hlr : lastRange rm B e with
    | none => exact ⟨some (.base .indexCorrupt), [], by simp [lastFrameFault, hlr, pure, StateT.pure], by simp, by simp⟩
    | some p =>
      obtain ⟨a, len⟩ := p
      obtain ⟨h32, hlt, hmax, rfl, rfl⟩ := lastRange_some hlr
      refine ⟨if (answer (e.offset - Log.tagBytes) (B - e.offset + Log.tagBytes)).size ≠ B - e.offset + Log.tagBytes
          then some (.shortRead (answer (e.offset - Log.tagBytes) (B - e.offset + Log.tagBytes)).size
            (B - e.offset + Log.tagBytes))
          else (lastFrame s rm (answer (e.offset - Log.tagBytes) (B - e.offset + Log.tagBytes))).map .base,
        [(e.offset - Log.tagBytes, B - e.offset + Log.tagBytes)], ?_, by simp, ?_⟩
      · simp only [lastFrameFault, hlr, bind, StateT.bind, StateT.modifyGet, pure]
        split <;> rfl
      · intro q hq
        simp only [List.mem_singleton] at hq
        subst hq
        constructor <;> simp only <;> omega

/-- The one open reads a base file of at most one base frame, and asks its readers for
two ranges, in order, and at most one more: of the segment `[base offset - 32, size)`, the base's tag on disk and the
tail after it, the tail at most `tailMax` long (the checkpoint header is handed in whole, HOST-64);
then of the index file the ONE entry the base names last (`lastAt`: `entryBytes` bytes,
none at count 0), with the count at most `indexMax` and every counted entry within the file
(HOST-33: open reads one entry, not the index); then, for that entry, at most one more range of the
segment, ending at the base's offset and at most a frame and a tag long (its record, HOST-63). The position it opens to lies in the tail, and
the orphan bytes it reports are exactly the file's bytes past the counted entries, so the writer's
truncation (`openWriter`) never drops a byte of an entry the base counts. Stated over
readers that record every range they are asked for (in one log) and answer with arbitrary bytes
`answer off len` / `answerI off len`, of any length (a short read is `openWith`'s to refuse). -/
theorem openWith_reads {W F : Type} (keys : Keys) (c : Cadence) (world : Codec.Stream W)
    (mark : W → Nat × ByteArray) (origin : W → ByteArray) (step : W → ByteArray → Except F W) (file header : ByteArray) (size indexSize : Nat) (answer answerI : Nat → Nat → ByteArray)
    {o : Opening W} {log : List (Nat × Nat)}
    (h : (openWith keys c world mark origin step file header size indexSize (m := StateM (List (Nat × Nat)))
      (fun off len => modifyGet fun l => (.ok (answerI off len), l ++ [(off, len)]))
      (fun off len => modifyGet fun l => (.ok (answer off len), l ++ [(off, len)]))).run [] = (.ok o, log)) :
    file.size ≤ Log.frameMax c.baseRecordMax ∧ Log.tagBytes ≤ o.sealed.offset ∧
    ∃ len extra, log = [(o.sealed.offset - Log.tagBytes, Log.tagBytes + len),
        lastAt keys o.sealed.index.count] ++ extra ∧ extra.length ≤ 1 ∧
      (∀ p ∈ extra, p.1 + p.2 = o.sealed.offset ∧ p.2 ≤ Log.frameMax c.recordBytesMax + Log.tagBytes) ∧
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
            · cases hhf : headerFault keys header (origin b.world) b.offset b.tag (mark b.world) b.indexCount with
              | some e => rw [hhf] at h; simp only [StateT.pure, pure] at h; injection h with h1; cases h1
              | none =>
              rw [hhf] at h
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
              cases hix : indexNamed (keys.forStore (origin b.world)) b.indexCount b.indexLast (mark b.world).1
                  (answerI (lastAt keys b.indexCount).1 (lastAt keys b.indexCount).2) with
              | some e => rw [hix] at h; simp only [StateT.pure, pure] at h; injection h with h1; cases h1
              | none =>
              rw [hix] at h
              simp only at h
              obtain ⟨v, extra, hrun, hx1, hx2⟩ := lastFrameFault_reads (F := F) keys.segment c.recordBytesMax
                b.offset (lastEntry (keys.forStore (origin b.world)) b.indexCount
                  (answerI (lastAt keys b.indexCount).1 (lastAt keys b.indexCount).2)) answer
                ([(b.offset - Log.tagBytes, Log.tagBytes + len)] ++
                  [((lastAt keys b.indexCount).1, (lastAt keys b.indexCount).2)])
              simp only [StateT.bind, hrun] at h
              cases v with
              | some f => simp only [pure] at h; injection h with h1; cases h1
              | none =>
              generalize hop : openLog keys.segment c.recordBytesMax (indexed mark step)
                (b.world, #[], b.offset) b.tag.bytes
                ((answer (b.offset - Log.tagBytes) (Log.tagBytes + len)).extract Log.tagBytes
                  (answer (b.offset - Log.tagBytes) (Log.tagBytes + len)).size) = res at h
              cases res with
              | error e => simp only [pure] at h; injection h with h1; cases h1
              | ok op =>
                simp only at h
                cases htag : Codec.Digest.ofBytes? op.lastTag with
                | none => rw [htag] at h; simp only [pure] at h; injection h with h1; cases h1
                | some tag =>
                  rw [htag] at h
                  simp only [pure] at h
                  obtain ⟨rfl, rfl⟩ := h
                  have hv := openLog_validLen_le hop
                  have hsz' : (answer (b.offset - Log.tagBytes) (Log.tagBytes + len)).size = Log.tagBytes + len := by
                    simpa using hsz
                  refine ⟨by omega, show Log.tagBytes ≤ b.offset by omega, len, extra, by simp, hx1, hx2, hs, hle,
                    Nat.le_add_right _ _, ?_, show b.indexCount ≤ indexMax by omega,
                    show b.indexCount * entryBytes keys + (indexSize - b.indexCount * entryBytes keys) = indexSize by omega⟩
                  show b.offset + op.validLen ≤ b.offset + len
                  simp only [ByteArray.size_extract, hsz'] at hv
                  omega

/-- An open that SUCCEEDS found the base's own tag on disk right before the base's offset: whatever
segment it was handed, the 32 bytes before the offset are the tag of the base it decoded (HOST-18). -/
theorem openWith_anchored {W F : Type} (keys : Keys) (c : Cadence) (world : Codec.Stream W)
    (mark : W → Nat × ByteArray) (origin : W → ByteArray) (step : W → ByteArray → Except F W) (file header idx seg : ByteArray)
    {o : Opening W}
    (h : Id.run (openWith keys c world mark origin step file header seg.size idx.size (segReader idx) (segReader seg)) = .ok o) :
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
    (mark : W → Nat × ByteArray) (origin : W → ByteArray) (step : W → ByteArray → Except F W) (file header idx seg : ByteArray)
    {b : Base W} {bb : Nat} {d : ByteArray} {len : Nat}
    (hfile : file.size ≤ Log.frameMax c.baseRecordMax)
    (hb : Base.read keys c world file = .ok (b, bb, d))
    (hlen : tailRead c bb b.offset seg.size = .ok len)
    (hf : seg.extract (b.offset - Log.tagBytes) b.offset ≠ b.tag.bytes) :
    Id.run (openWith keys c world mark origin step file header seg.size idx.size (segReader idx) (segReader seg)) = .error (.base .foreignSegment) := by
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
    Codec.Stream.LawfulOn (fun b : Base W => P b.world ∧ b.offset < 2 ^ 64 ∧ b.indexCount < 2 ^ 64 ∧
        b.retainedFrom ≤ b.offset ∧ b.indexFrom ≤ b.indexCount)
      (Base.codec world) := by
  have h := Codec.Stream.refine_lawfulOn_where
    (Q := fun b : Base W => b.retainedFrom ≤ b.offset ∧ b.indexFrom ≤ b.indexCount)
    (Codec.Stream.product_lawfulOn hw (Codec.Stream.product_lawfulOn Codec.Stream.nat64_lawfulOn
      (Codec.Stream.product_lawfulOn Codec.Stream.digest_lawful.on
        (Codec.Stream.product_lawfulOn Codec.Stream.nat64_lawfulOn (Codec.Stream.product_lawfulOn
          Codec.Stream.digest_lawful.on (Codec.Stream.product_lawfulOn Codec.Stream.nat64_lawfulOn
            Codec.Stream.nat64_lawfulOn))))))
    "host/base/retained"
    (accept := fun (w, o, t, io, it, rf, k0) =>
      if rf ≤ o ∧ k0 ≤ io then some (⟨w, o, t, io, it, rf, k0⟩ : Base W) else none)
    (back := fun b => (b.world, b.offset, b.tag, b.indexCount, b.indexLast, b.retainedFrom, b.indexFrom))
    (fun y _ hq => by simp only [if_pos hq])
    (fun x y hxy => by
      obtain ⟨a, b, c, d, e, f, g⟩ := x
      simp only at hxy
      split at hxy
      · cases hxy; rfl
      · cases hxy)
    (fun x y hxy => by
      obtain ⟨a, b, c, d, e, f, g⟩ := x
      simp only at hxy
      split at hxy
      · rename_i hc; cases hxy; exact hc
      · cases hxy)
  exact h.mono (fun _ hv => ⟨hv.1.1, hv.1.2.1, hv.1.2.2.2.1, hv.2.1, hv.2.2⟩)
    (fun _ hv => ⟨⟨hv.1, hv.2.1, trivial, hv.2.2.1, trivial, Nat.lt_of_le_of_lt hv.2.2.2.1 hv.2.1,
      Nat.lt_of_le_of_lt hv.2.2.2.2 hv.2.2.1⟩, hv.2.2.2.1, hv.2.2.2.2⟩)

/-- **A base that decodes keeps only what precedes it** (HOST-64): its oldest kept segment file
starts at or before its own offset, and its first kept entry is at or before its count. The codec
refuses any other by its label (`Base.codec`), so no open reads a base that names files after it. -/
theorem Base.codec_decode_keep {W : Type} {world : Codec.Stream W} {bs : ByteArray} {b : Base W}
    (h : (Base.codec world).decode bs = .ok b) : b.retainedFrom ≤ b.offset ∧ b.indexFrom ≤ b.indexCount := by
  unfold Codec.Stream.decode at h
  split at h
  · rename_i v j hg
    split at h
    · cases h
      simp only [Base.codec, Codec.Stream.refine] at hg
      split at hg
      · cases hg
      · rename_i x k _
        obtain ⟨a, o, t, ic, il, rf, k0⟩ := x
        simp only at hg
        split at hg
        · rename_i y hy
          cases hg
          split at hy
          · rename_i hc; cases hy; exact hc
          · cases hy
        · cases hg
    · cases h
  · cases h

/-- **A base that reads keeps only what precedes it** (`Base.codec_decode_keep` through `Base.read`). -/
theorem Base.read_keep {W : Type} {keys : Keys} {c : Cadence} {world : Codec.Stream W} {file : ByteArray}
    {b : Base W} {n : Nat} {d : ByteArray} (h : Base.read keys c world file = .ok (b, n, d)) :
    b.retainedFrom ≤ b.offset ∧ b.indexFrom ≤ b.indexCount := by
  unfold Base.read at h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · cases h
  dsimp only at h
  split at h
  · cases h
  split at h
  · cases h
  · rename_i b' hd
    cases h
    exact Base.codec_decode_keep hd

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

/-! ## The checkpoint header of the base's own segment file (HOST-64; HOST-25's origin check) -/

theorem Header.fits_iff (w : Nat) (h : Header) :
    h.fits w = true ↔ h.start < 2 ^ 64 ∧ h.steps < 2 ^ 64 ∧ h.indexCount < 2 ^ 64 ∧ h.prev < 2 ^ 64 ∧
      h.origin.size = w ∧ h.chain.size = w := by
  simp [Header.fits, Bool.and_eq_true, decide_eq_true_eq, and_assoc]

/-- Skip a prefix of known size in an extract. -/
theorem extract_skip {a b : ByteArray} {k : Nat} (ha : a.size = k) (i j : Nat) :
    (a ++ b).extract (k + i) (k + j) = b.extract i j :=
  ByteArray.extract_append_size_add' ha.symm

/-- **The writer's headers pass the check** (completeness): a header the layout holds at the Store's
chain width reads back as itself. -/
theorem Header.read_bytes (keys : Keys) (h : Header) (hf : h.fits keys.chainBytes = true) :
    Header.read keys (Header.bytes keys h) = some h := by
  obtain ⟨hs, hst, hic, hp, ho, hc⟩ := (Header.fits_iff _ h).mp hf
  obtain ⟨s, st, ic, p, t, o, ch⟩ := h
  simp only at hs hst hic hp ho hc
  have n8 := nat64_size
  have ht : t.bytes.size = 32 := t.size_eq
  -- the bytes, right-associated
  have hB : Header.bytes keys ⟨s, st, ic, p, t, o, ch⟩ =
      Codec.Stream.nat64.bytes s ++ (Codec.Stream.nat64.bytes st ++ (Codec.Stream.nat64.bytes ic ++ (Codec.Stream.nat64.bytes p ++
        (t.bytes ++ (o ++ (ch ++ (tagDigest keys.checkpoint (Header.body ⟨s, st, ic, p, t, o, ch⟩)).bytes)))))) := by
    simp only [Header.bytes, Header.body, ByteArray.append_assoc]
  have e1 : (Header.bytes keys ⟨s, st, ic, p, t, o, ch⟩).extract 0 8 = Codec.Stream.nat64.bytes s := by
    rw [hB]; exact ByteArray.extract_append_eq_left (n8 s).symm
  have e2 : (Header.bytes keys ⟨s, st, ic, p, t, o, ch⟩).extract 8 16 = Codec.Stream.nat64.bytes st := by
    rw [hB, show (8 : Nat) = 8 + 0 from rfl, show (16 : Nat) = 8 + 8 from rfl, extract_skip (n8 s)]
    exact ByteArray.extract_append_eq_left (n8 st).symm
  have e3 : (Header.bytes keys ⟨s, st, ic, p, t, o, ch⟩).extract 16 24 = Codec.Stream.nat64.bytes ic := by
    rw [hB, show (16 : Nat) = 8 + 8 from rfl, show (24 : Nat) = 8 + 16 from rfl, extract_skip (n8 s),
      show (8 : Nat) = 8 + 0 from rfl, show (16 : Nat) = 8 + 8 from rfl, extract_skip (n8 st)]
    exact ByteArray.extract_append_eq_left (n8 ic).symm
  have e4 : (Header.bytes keys ⟨s, st, ic, p, t, o, ch⟩).extract 24 32 = Codec.Stream.nat64.bytes p := by
    rw [hB, show (24 : Nat) = 8 + 16 from rfl, show (32 : Nat) = 8 + 24 from rfl, extract_skip (n8 s),
      show (16 : Nat) = 8 + 8 from rfl, show (24 : Nat) = 8 + 16 from rfl, extract_skip (n8 st),
      show (8 : Nat) = 8 + 0 from rfl, show (16 : Nat) = 8 + 8 from rfl, extract_skip (n8 ic)]
    exact ByteArray.extract_append_eq_left (n8 p).symm
  have hpre : (Codec.Stream.nat64.bytes s ++ Codec.Stream.nat64.bytes st ++ Codec.Stream.nat64.bytes ic ++ Codec.Stream.nat64.bytes p).size = 32 := by
    simp only [ByteArray.size_append, n8]
  have hB' : Header.bytes keys ⟨s, st, ic, p, t, o, ch⟩ =
      (Codec.Stream.nat64.bytes s ++ Codec.Stream.nat64.bytes st ++ Codec.Stream.nat64.bytes ic ++ Codec.Stream.nat64.bytes p) ++
        (t.bytes ++ (o ++ (ch ++ (tagDigest keys.checkpoint (Header.body ⟨s, st, ic, p, t, o, ch⟩)).bytes))) := by
    rw [hB]; simp only [ByteArray.append_assoc]
  have e5 : (Header.bytes keys ⟨s, st, ic, p, t, o, ch⟩).extract 32 64 = t.bytes := by
    rw [hB', show (32 : Nat) = 32 + 0 from rfl, show (64 : Nat) = 32 + 32 from rfl, extract_skip hpre]
    exact ByteArray.extract_append_eq_left ht.symm
  have e6 : (Header.bytes keys ⟨s, st, ic, p, t, o, ch⟩).extract 64 (64 + keys.chainBytes) = o := by
    rw [hB', show (64 : Nat) = 32 + 32 from rfl, show 32 + 32 + keys.chainBytes = 32 + (32 + keys.chainBytes) by omega,
      extract_skip hpre, show (32 : Nat) = 32 + 0 from rfl, extract_skip ht]
    exact ByteArray.extract_append_eq_left ho.symm
  have e7 : (Header.bytes keys ⟨s, st, ic, p, t, o, ch⟩).extract (64 + keys.chainBytes) (64 + 2 * keys.chainBytes) = ch := by
    rw [hB', show 64 + keys.chainBytes = 32 + (32 + (keys.chainBytes + 0)) by omega,
      show 64 + 2 * keys.chainBytes = 32 + (32 + (keys.chainBytes + keys.chainBytes)) by omega,
      extract_skip hpre, extract_skip ht, extract_skip ho]
    exact ByteArray.extract_append_eq_left hc.symm
  have hd : Codec.Digest.ofBytes? t.bytes = some t := by
    simp [Codec.Digest.ofBytes?, t.size_eq]
  unfold Header.read
  rw [e1, e2, e3, e4, e5, Codec.Stream.nat64_lawfulOn.decode_bytes hs, Codec.Stream.nat64_lawfulOn.decode_bytes hst,
    Codec.Stream.nat64_lawfulOn.decode_bytes hic, Codec.Stream.nat64_lawfulOn.decode_bytes hp, hd]
  simp only [e6, e7, if_true]

/-- A header that reads was handed exactly its own bytes: its fields and the checkpoint sealer's tag
over them. -/
theorem Header.read_sound {keys : Keys} {b : ByteArray} {h : Header} (hr : Header.read keys b = some h) :
    Header.bytes keys h = b := by
  unfold Header.read at hr
  split at hr
  · simp only at hr
    split at hr
    · cases hr; assumption
    · cases hr
  · cases hr

/-- `headerFault` passes exactly when the header verifies, states `origin`, and states the base's
own position: its offset, tag, step count and chain, and the entries it counts. -/
theorem headerFault_none_iff (keys : Keys) (b origin : ByteArray) (offset : Nat) (tag : Codec.Digest)
    (mark : Nat × ByteArray) (count : Nat) :
    headerFault keys b origin offset tag mark count = none ↔
      ∃ h, Header.read keys b = some h ∧ h.origin = origin ∧ h.start = offset ∧ h.tag = tag ∧
        h.steps = mark.1 ∧ h.chain = mark.2 ∧ h.indexCount = count := by
  unfold headerFault
  cases hr : Header.read keys b with
  | none => simp
  | some h =>
    simp only [Option.some.injEq, exists_eq_left']
    by_cases ho : h.origin = origin
    · by_cases hp : h.start = offset ∧ h.tag = tag ∧ h.steps = mark.1 ∧ h.chain = mark.2 ∧ h.indexCount = count
      · simp [ho, hp]
      · simp only [ho, ne_eq, not_true_eq_false, if_false, if_neg hp, reduceCtorEq, false_iff, true_and]
        exact hp
    · simp [ho]

/-- `checkpointCorrupt` is the verdict on a header that does not verify. -/
theorem headerFault_corrupt (keys : Keys) {b : ByteArray} (origin : ByteArray) (offset : Nat) (tag : Codec.Digest)
    (mark : Nat × ByteArray) (count : Nat) (h : Header.read keys b = none) :
    headerFault keys b origin offset tag mark count = some .checkpointCorrupt := by
  unfold headerFault; rw [h]

/-- `foreignOrigin` is the verdict on a header that verifies and states another Store's origin. -/
theorem headerFault_foreignOrigin (keys : Keys) {b origin : ByteArray} {hd : Header} (offset : Nat)
    (tag : Codec.Digest) (mark : Nat × ByteArray) (count : Nat) (h : Header.read keys b = some hd)
    (ho : hd.origin ≠ origin) :
    headerFault keys b origin offset tag mark count = some .foreignOrigin := by
  unfold headerFault; rw [h]; simp [ho]

/-- `foreignSegment` is the verdict on a header that verifies, states the Store's origin, and names
another position than the base's. -/
theorem headerFault_foreignSegment (keys : Keys) {b origin : ByteArray} {hd : Header} {offset : Nat}
    {tag : Codec.Digest} {mark : Nat × ByteArray} {count : Nat} (h : Header.read keys b = some hd)
    (ho : hd.origin = origin)
    (hp : ¬ (hd.start = offset ∧ hd.tag = tag ∧ hd.steps = mark.1 ∧ hd.chain = mark.2 ∧ hd.indexCount = count)) :
    headerFault keys b origin offset tag mark count = some .foreignSegment := by
  unfold headerFault; rw [h]; simp only [ho, ne_eq, not_true_eq_false, if_false, if_neg hp]

/-- **HOST-64 (and HOST-25): an open that SUCCEEDS read the base's own checkpoint header.** Whatever
header it was handed, it verifies under the Store's checkpoint sealer, states the genesis chain of
the decoded base World's origin (`origin b.world`: HOST-25's identity, which the origin frame at 0
stated before a Store could drop it), and states the base's position: its offset, tag, World's step
count and chain, and its entry count; and the base keeps no file past its own and no entry past its
count. -/
theorem openWith_header {W F : Type} (keys : Keys) (c : Cadence) (world : Codec.Stream W)
    (mark : W → Nat × ByteArray) (origin : W → ByteArray) (step : W → ByteArray → Except F W)
    (file header idx seg : ByteArray) {o : Opening W}
    (h : Id.run (openWith keys c world mark origin step file header seg.size idx.size (segReader idx) (segReader seg)) = .ok o) :
    ∃ b bb d hd, Base.read keys c world file = .ok (b, bb, d) ∧ Header.read keys header = some hd ∧
      hd.origin = origin b.world ∧ hd.start = b.offset ∧ hd.tag = b.tag ∧ hd.steps = (mark b.world).1 ∧
      hd.chain = (mark b.world).2 ∧ hd.indexCount = b.indexCount ∧
      b.retainedFrom ≤ b.offset ∧ b.indexFrom ≤ b.indexCount := by
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
            · split at h
              · cases h
              · rename_i hnone
                obtain ⟨hd, hr, ho, hs, ht, hst, hc, hi⟩ := (headerFault_none_iff _ _ _ _ _ _ _).mp hnone
                have hk := Base.read_keep hb
                exact ⟨b, bb, dg, hd, hb, hr, ho, hs, ht, hst, hc, hi, hk.1, hk.2⟩

/-- **The header tooth over the real `openWith`.** When the base reads, its tail is within bounds and
its tag sits before its offset, a header that fails the check is refused with `headerFault`'s
verdict: `checkpointCorrupt` when it does not verify, `foreignOrigin` when it states another
Store's origin, `foreignSegment` when it names another position. -/
theorem openWith_headerFault {W F : Type} (keys : Keys) (c : Cadence) (world : Codec.Stream W)
    (mark : W → Nat × ByteArray) (origin : W → ByteArray) (step : W → ByteArray → Except F W)
    (file header idx seg : ByteArray) {b : Base W} {bb : Nat} {d : ByteArray} {len : Nat} {f : BaseFault}
    (hfile : file.size ≤ Log.frameMax c.baseRecordMax)
    (hb : Base.read keys c world file = .ok (b, bb, d))
    (hlen : tailRead c bb b.offset seg.size = .ok len)
    (hoff : Log.tagBytes ≤ b.offset)
    (hanchor : seg.extract (b.offset - Log.tagBytes) b.offset = b.tag.bytes)
    (hf : headerFault keys header (origin b.world) b.offset b.tag (mark b.world) b.indexCount = some f) :
    Id.run (openWith keys c world mark origin step file header seg.size idx.size (segReader idx) (segReader seg)) =
      .error (.base f) := by
  obtain ⟨hs, _⟩ := tailRead_ok hlen
  unfold openWith
  simp only [show ¬ Log.frameMax c.baseRecordMax < file.size by omega, if_false, hb, hlen,
    show ¬ b.offset < Log.tagBytes by omega, segReader, pure_bind]
  have e : (seg.extract (b.offset - Log.tagBytes) (b.offset - Log.tagBytes + (Log.tagBytes + len))).extract 0 Log.tagBytes
      = seg.extract (b.offset - Log.tagBytes) b.offset := by
    rw [ByteArray.extract_extract, Nat.add_zero,
      show min (b.offset - Log.tagBytes + Log.tagBytes) (b.offset - Log.tagBytes + (Log.tagBytes + len))
        = b.offset by omega]
  have hsz : (seg.extract (b.offset - Log.tagBytes) (b.offset - Log.tagBytes + (Log.tagBytes + len))).size
      = Log.tagBytes + len := by
    rw [ByteArray.size_extract]; omega
  rw [if_neg (by rw [hsz]; exact fun h => h rfl), e, if_neg (by rw [hanchor]; exact fun h => h rfl), hf]
  rfl

/-- **HOST-64, completeness: every header the layout holds passes the check at its own place**: the
header the writer writes for a file (genesis, `Checkpoint.rotate`) is accepted by the open of a base
at the file's start, with the World's mark and the count the header states. -/
theorem headerFault_bytes (keys : Keys) (h : Header) (hf : h.fits keys.chainBytes = true) :
    headerFault keys (Header.bytes keys h) h.origin h.start h.tag (h.steps, h.chain) h.indexCount = none :=
  (headerFault_none_iff _ _ _ _ _ _ _).mpr
    ⟨h, Header.read_bytes keys h hf, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **HOST-64, completeness at genesis.** The header genesis writes for its base's own file passes
the check of the open that reads its genesis base (at offset `segment.size`, after no entry), given
that `origin` is the chain `mark` writes at genesis (KERNEL's `genesis_chain`), that the chain is the
Store's width (below 2^32) and the step count a u64. -/
theorem genesisImage_header {W : Type} (keys : Keys) (c : Cadence) (world : Codec.Stream W)
    (mark : W → Nat × ByteArray) (origin : W → ByteArray) (w₀ : W) {img : Image}
    (h : genesisImage keys c world mark w₀ = .ok img)
    (hw : (mark w₀).2.size = keys.chainBytes) (hcb : keys.chainBytes < 2 ^ 32) (hs : (mark w₀).1 < 2 ^ 64)
    (ho : origin w₀ = (mark w₀).2) :
    headerFault keys img.header (origin w₀) img.segment.size
      (tagDigest keys.segment (segmentInitial ++ (mark w₀).2)) (mark w₀) 0 = none := by
  unfold genesisImage at h
  dsimp only at h
  split at h
  · cases h
  · cases h
    have hpos := size_frame keys.segment segmentInitial (mark w₀).2
    have hfit : (Header.at ⟨(frame keys.segment segmentInitial (mark w₀).2).size,
        tagDigest keys.segment (segmentInitial ++ (mark w₀).2)⟩ (mark w₀) 0 0 (mark w₀).2).fits keys.chainBytes = true := by
      rw [Header.fits_iff]
      simp only [Header.at]
      refine ⟨?_, hs, by decide, by decide, hw, hw⟩
      rw [hpos, hw]; unfold Log.tagBytes; omega
    have := headerFault_bytes keys _ hfit
    simp only [Header.at, Prod.eta] at this
    rw [ho]
    exact this

/-- **An open that succeeds verified the entry the base names** (HOST-33 condition 2,
`open_verifies_named`). Whatever the index file it was handed: the file holds every entry the opened
base counts, and either the base counts none and names no last tag, or the bytes at the last
counted entry read back as an entry AT THAT POSITION (its tag verified there, `Entry.read_sound`)
whose tag is the `indexLast` the base names and whose record began before the base's World (its step
count is below the base's, HOST-53), both under the keys of THIS Store (`Keys.forStore`
of the decoded base World's origin chain, which its file's header states: HOST-25, HOST-64). That binds the
base's count to an entry the writer of this Store sealed. It says nothing about the entries before it: a page checks each one it reads
(`Host.Proofs.Page.build_located`), and `host check` checks all of them (`indexClean_none`). -/
theorem openWith_verifies_named {W F : Type} (keys : Keys) (c : Cadence) (world : Codec.Stream W)
    (mark : W → Nat × ByteArray) (origin : W → ByteArray) (step : W → ByteArray → Except F W)
    (file header idx seg : ByteArray) {o : Opening W}
    (h : Id.run (openWith keys c world mark origin step file header seg.size idx.size (segReader idx) (segReader seg)) = .ok o) :
    ∃ b bb d, Base.read keys c world file = .ok (b, bb, d) ∧
    o.sealed.index.count * entryBytes keys ≤ idx.size ∧
      ((o.sealed.index.count = 0 ∧ o.sealed.index.last = Codec.Digest.zero) ∨
        (0 < o.sealed.index.count ∧ ∃ e,
          Entry.read (keys.forStore (origin b.world)) (o.sealed.index.count - 1)
            (idx.extract ((o.sealed.index.count - 1) * entryBytes keys)
              ((o.sealed.index.count - 1) * entryBytes keys + entryBytes keys)) = some e ∧
          e.tag (keys.forStore (origin b.world)) (o.sealed.index.count - 1) = o.sealed.index.last ∧
          e.steps < (mark b.world).1)) := by
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
                        cases hlf : lastFrameFault keys.segment c.recordBytesMax b.offset
                            (lastEntry (keys.forStore (origin b.world)) b.indexCount
                              (idx.extract (lastAt keys b.indexCount).1
                                ((lastAt keys b.indexCount).1 + (lastAt keys b.indexCount).2)))
                            (segReader seg) with
                        | some f => rw [hlf] at h; cases h
                        | none =>
                          rw [hlf] at h
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

/-- The converse of `Record.runRooted_ok` (HOST-47): a `Kernel.Rooted` run is one `Record.runRooted`
accepts, from any index. So a premise stated over `runRooted` is discharged by the writer's
`Machine.staged_rooted` and the follower's `World.RootedFold` alike. -/
theorem Record.runRooted_of_rooted {D F : Type} [Ord D] [DecidableEq D]
    {admit : Kernel.World D → Kernel.Step D → Except F (Kernel.World D)} {root : Kernel.World D → D} :
    ∀ {i : Nat} {w w' : Kernel.World D} {ps : List (Kernel.Step D × D)},
      Kernel.Rooted admit root w ps w' → Record.runRooted admit root i w ps = .ok w'
  | i, w, w', [], h => by
      simp only [Kernel.Rooted] at h; subst h; rfl
  | i, w, w', (t, r) :: rest, h => by
      obtain ⟨w₁, ha, hr, hrest⟩ := h
      unfold Record.runRooted
      rw [ha]
      simp only [← hr, if_true]
      exact Record.runRooted_of_rooted hrest

/-- A record that opens is a NONEMPTY rooted run (HOST-49: the reader refuses an empty record
`empty`). -/
theorem Record.step_nonempty {D F : Type} [Ord D] [DecidableEq D] {dc : Codec.Stream D}
    {admit : Kernel.World D → Kernel.Step D → Except F (Kernel.World D)} {root : Kernel.World D → D}
    {w w' : Kernel.World D} {r : ByteArray} (h : Record.step dc admit root w r = .ok w') :
    ∃ ps, (Record.codec dc).decode r = .ok ps ∧ ps ≠ [] ∧ Kernel.Rooted admit root w ps w' := by
  unfold Record.step Record.stepTurns at h
  split at h
  · cases h
  · cases h
  · rename_i ps hne hd
    split at h
    · cases h
    · rename_i w₁ hr
      simp only [Except.map, Except.ok.injEq] at h
      subst h
      exact ⟨ps, hd, fun he => hne he, Record.runRooted_ok hr⟩

/-- **HOST-29: a record that opens is a rooted run of the pairs it decodes to.** -/
theorem Record.step_rooted {D F : Type} [Ord D] [DecidableEq D] {dc : Codec.Stream D}
    {admit : Kernel.World D → Kernel.Step D → Except F (Kernel.World D)} {root : Kernel.World D → D}
    {w w' : Kernel.World D} {r : ByteArray} (h : Record.step dc admit root w r = .ok w') :
    ∃ ps, (Record.codec dc).decode r = .ok ps ∧ Kernel.Rooted admit root w ps w' := by
  obtain ⟨ps, hd, -, hr⟩ := Record.step_nonempty h
  exact ⟨ps, hd, hr⟩


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
