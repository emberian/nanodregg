/-
# Host.Proofs.Base — open reads one base and at most `tailMax` of log (HOST-14 condition 4)

* `recover_validLen_le` — recovery never ends past the bytes it was given;
* `tailRead_ok` — open reads exactly the segment after the base, and only if it is at most
  `tailMax` long;
* `openWith_reads` — the one open (`openWith`, generic in its monad: `IO` over the file for the
  Store, `Id` over bytes for the simulation, and here a reader that records its calls and answers
  anything) reads a base file of at most one base frame and asks for EXACTLY one range of segment,
  `[base offset, size)`, of at most `tailMax` bytes; the position it opens to is within that range
  (a short read is refused inside `openWith`, so no reader can bypass the bound);
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
range of segment, `[base offset, size)`, at most `tailMax` long; the position it opens to lies in
that range. Stated over a reader that records every range it is asked for and answers with
arbitrary bytes `answer off len`, of any length (a short read is `openWith`'s to refuse). -/
theorem openWith_reads {W F : Type} (keys : Keys) (c : Cadence) (world : Codec.Stream W)
    (mark : W → Nat × ByteArray) (step : W → ByteArray → Except F W) (file : ByteArray) (size : Nat) (answer : Nat → Nat → ByteArray)
    {o : Opening W} {log : List (Nat × Nat)}
    (h : (openWith keys c world mark step file size (m := StateM (List (Nat × Nat))) fun off len =>
      modifyGet fun l => (.ok (answer off len), l ++ [(off, len)])).run [] = (.ok o, log)) :
    file.size ≤ Log.frameMax c.baseRecordMax ∧
    ∃ len, log = [(o.sealed.offset, len)] ∧ o.sealed.offset + len = size ∧
      len ≤ c.tailMax o.sealed.bytes ∧
      o.sealed.offset ≤ o.pos.offset ∧ o.pos.offset ≤ o.sealed.offset + len := by
  simp only [openWith] at h
  split at h
  · simp only [StateT.run, StateT.pure, pure] at h; injection h with h1; cases h1
  · rename_i hfile
    refine ⟨by omega, ?_⟩
    split at h
    · simp only [StateT.run, StateT.pure, pure] at h; injection h with h1; cases h1
    · rename_i b bb hb
      split at h
      · simp only [StateT.run, StateT.pure, pure] at h; injection h with h1; cases h1
      · rename_i len hlen
        obtain ⟨hs, hle⟩ := tailRead_ok hlen
        simp only [bind, modifyGet, MonadStateOf.modifyGet, StateT.run, StateT.bind,
          StateT.modifyGet, List.nil_append] at h
        split at h
        · simp only [StateT.pure, pure] at h; injection h with h1; cases h1
        · rename_i hsz
          generalize hop : openLog keys.segment c.recordBytesMax (indexed mark step)
            (b.world, b.index.toArray, b.offset) b.tag.bytes (answer b.offset len) = res at h
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
              have hsz' : (answer b.offset len).size = len := by simpa using hsz
              refine ⟨len, rfl, hs, hle, Nat.le_add_right _ _, ?_⟩
              show b.offset + op.validLen ≤ b.offset + len
              omega

theorem within_after_seal (c : Cadence) (pos bytes n : Nat) (hn : n ≤ Log.frameMax c.recordBytesMax) :
    withinTail c ⟨pos, bytes⟩ pos n = true := by
  unfold withinTail Cadence.tailMax
  simp only [decide_eq_true_eq]
  omega

end Nanodregg.Host
