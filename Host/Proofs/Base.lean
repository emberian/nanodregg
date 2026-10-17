/-
# Host.Proofs.Base — open reads one base and at most `tailMax` of log (HOST-14 condition 4)

* `recover_validLen_le` — recovery never ends past the bytes it was given;
* `tailRead_ok` — open reads exactly the segment after the base, and only if it is at most
  `tailMax` long;
* `openWith_reads` — the one open (`openWith`, in `Id`, the simulation's and the theorem's
  instance; `IO` runs the same definition over the file) asks its reader for exactly one range,
  `[base offset, segment size)`, of at most `tailMax` bytes, and the position it opens to is within
  that range: one base, at most two cadences and a frame of log;
* `within_after_seal` — once the newest durable base sits at the loop's position, every frame up to
  the record bound fits (`Host.Loop.makeRoom`'s last step always makes room, so the loop never
  refuses a batch for want of a seal).
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

/-- The one open reads one range of segment, `[offset, size)`, at most `tailMax` long, and opens
to a position inside it. -/
theorem openWith_reads {W F : Type} (keys : Keys) (c : Cadence) (world : Codec.Stream W)
    (step : W → ByteArray → Except F W) (file seg : ByteArray) {o : Opening W}
    (h : Id.run (openWith keys c world step file seg.size
      fun off len => pure (.ok (seg.extract off (off + len)))) = .ok o) :
    ∃ len, o.sealed.offset + len = seg.size ∧ len ≤ c.tailMax o.sealed.bytes ∧
      o.sealed.offset ≤ o.pos.offset ∧ o.pos.offset ≤ o.sealed.offset + len := by
  simp only [openWith, Id.run, bind, pure] at h
  split at h
  · cases h
  · rename_i b bb hb
    split at h
    · cases h
    · rename_i len hlen
      obtain ⟨hs, hle⟩ := tailRead_ok hlen
      split at h
      · cases h
      · rename_i op hop
        split at h
        · cases h
        · rename_i tag
          cases h
          have hv := openLog_validLen_le hop
          have hsz : (seg.extract b.offset (b.offset + len)).size = len := by
            simp [ByteArray.size_extract]; omega
          exact ⟨len, hs, hle, Nat.le_add_right _ _, by show b.offset + op.validLen ≤ b.offset + len; omega⟩

theorem within_after_seal (c : Cadence) (pos bytes n : Nat) (hn : n ≤ Log.frameMax c.recordBytesMax) :
    withinTail c ⟨pos, bytes⟩ pos n = true := by
  unfold withinTail Cadence.tailMax
  simp only [decide_eq_true_eq]
  omega

end Nanodregg.Host
