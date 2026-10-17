/-
# Host.Proofs.Base — open reads one base and at most `tailMax` of log (HOST-14 condition 4)

* `recover_validLen_le` — recovery never ends past the bytes it was given;
* `tailRead_ok` — open reads exactly the segment after the base, and only if it is at most
  `tailMax` long;
* `openWith_reads` — the one open (`openWith`, generic in its monad: `IO` over the file for the
  Store, `Id` over bytes for the simulation, and here a reader that records its calls and answers
  anything) reads a base file of at most one base frame and asks for EXACTLY one range of segment,
  `[base offset - 32, size)`: the base's tag and a tail of at most `tailMax` bytes; the position it
  opens to is within the tail (a short read is refused inside `openWith`, so no reader can bypass
  the bound);
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

/-- The one open reads a base file of at most one base frame, and asks its reader for EXACTLY one
range of segment, `[base offset - 32, size)`: the base's tag on disk and the tail after it, the
tail at most `tailMax` long; the position it opens to lies in the tail. Stated over a reader that
records every range it is asked for and answers with arbitrary bytes `answer off len`, of any
length (a short read is `openWith`'s to refuse). -/
theorem openWith_reads {W F : Type} (keys : Keys) (c : Cadence) (world : Codec.Stream W)
    (mark : W → Nat × ByteArray) (step : W → ByteArray → Except F W) (file : ByteArray) (size : Nat) (answer : Nat → Nat → ByteArray)
    {o : Opening W} {log : List (Nat × Nat)}
    (h : (openWith keys c world mark step file size (m := StateM (List (Nat × Nat))) fun off len =>
      modifyGet fun l => (.ok (answer off len), l ++ [(off, len)])).run [] = (.ok o, log)) :
    file.size ≤ Log.frameMax c.baseRecordMax ∧ Log.tagBytes ≤ o.sealed.offset ∧
    ∃ len, log = [(o.sealed.offset - Log.tagBytes, Log.tagBytes + len)] ∧ o.sealed.offset + len = size ∧
      len ≤ c.tailMax o.sealed.bytes ∧
      o.sealed.offset ≤ o.pos.offset ∧ o.pos.offset ≤ o.sealed.offset + len := by
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
            · generalize hop : openLog keys.segment c.recordBytesMax (indexed mark step)
                (b.world, b.index.toArray, b.offset) b.tag.bytes
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
                  refine ⟨by omega, show Log.tagBytes ≤ b.offset by omega, len, rfl, hs, hle,
                    Nat.le_add_right _ _, ?_⟩
                  show b.offset + op.validLen ≤ b.offset + len
                  simp only [ByteArray.size_extract, hsz'] at hv
                  omega

/-- An open that SUCCEEDS found the base's own tag on disk right before the base's offset: whatever
segment it was handed, the 32 bytes before the offset are the tag of the base it decoded (HOST-18). -/
theorem openWith_anchored {W F : Type} (keys : Keys) (c : Cadence) (world : Codec.Stream W)
    (mark : W → Nat × ByteArray) (step : W → ByteArray → Except F W) (file seg : ByteArray)
    {o : Opening W}
    (h : Id.run (openWith keys c world mark step file seg.size (segReader seg)) = .ok o) :
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
    (mark : W → Nat × ByteArray) (step : W → ByteArray → Except F W) (file seg : ByteArray)
    {b : Base W} {bb : Nat} {d : ByteArray} {len : Nat}
    (hfile : file.size ≤ Log.frameMax c.baseRecordMax)
    (hb : Base.read keys c world file = .ok (b, bb, d))
    (hlen : tailRead c bb b.offset seg.size = .ok len)
    (hf : seg.extract (b.offset - Log.tagBytes) b.offset ≠ b.tag.bytes) :
    Id.run (openWith keys c world mark step file seg.size (segReader seg)) = .error (.base .foreignSegment) := by
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

theorem within_after_seal (c : Cadence) (sealed : Sealed) (n : Nat) (hn : n ≤ Log.frameMax c.recordBytesMax) :
    withinTail c sealed sealed.offset n = true := by
  unfold withinTail Cadence.tailMax
  simp only [decide_eq_true_eq]
  omega

end Nanodregg.Host
