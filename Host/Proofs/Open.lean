/-
# Host.Proofs.Open — what `Host.openLog` guarantees

* `foldRecords_ok` — open's fold is `List.foldlM step` (the index only names a refusal);
* `open_encodeAll` — a clean segment opens to the fold of exactly the records written;
* `open_torn` — cut the next frame anywhere short of its end (a crash before its fsync): the
  segment opens to the fold of the frames before it, with `torn` = the cut length;
* `open_sound` — for ANY bytes, the opened World is the fold of a record list whose encoding is
  literally the bytes before `validLen`, and `lastTag` is that list's chain tag: open never
  invents, skips or reorders a record.
-/
import Host.Open
import Host.Proofs.Log

namespace Nanodregg.Host

open Nanodregg.Host.Log

variable {W F : Type}

theorem foldRecords_ok (step : W → ByteArray → Except F W) (rs : List ByteArray) :
    ∀ (w w' : W) (i : Nat), foldRecords step w i rs = .ok w' ↔ rs.foldlM step w = .ok w' := by
  induction rs with
  | nil => intro w w' i; simp [foldRecords, List.foldlM, pure, Except.pure]
  | cons r rs ih =>
    intro w w' i
    simp only [foldRecords, List.foldlM]
    cases h : step w r with
    | ok v => simpa [bind, Except.bind] using ih v w' (i + 1)
    | error f => simp [bind, Except.bind]

theorem open_encodeAll (s : Sealer) {recordMax : Nat} (step : W → ByteArray → Except F W) (w₀ w : W)
    (initial : ByteArray) (rs : List ByteArray) (hrs : ∀ r ∈ rs, r.size ≤ recordMax ∧ r.size < 2 ^ 32)
    (hfold : rs.foldlM step w₀ = .ok w) :
    openLog s recordMax step w₀ initial (encodeAll s initial rs) =
      .ok ⟨w, rs.length, (encodeAll s initial rs).size, lastTag s initial rs, 0⟩ := by
  unfold openLog
  rw [recover_encodeAll s initial rs hrs]
  simp only
  rw [(foldRecords_ok step rs w₀ w 0).mpr hfold]
  rfl

theorem open_torn (s : Sealer) {recordMax : Nat} (step : W → ByteArray → Except F W) (w₀ w : W)
    (initial : ByteArray) (rs : List ByteArray) (hrs : ∀ r ∈ rs, r.size ≤ recordMax ∧ r.size < 2 ^ 32)
    (r p q : ByteArray) (hr : r.size ≤ recordMax ∧ r.size < 2 ^ 32)
    (hcut : p ++ q = frame s (lastTag s initial rs) r) (hq : 0 < q.size) (hp : 0 < p.size)
    (hin : NoFrameInside s recordMax (encodeAll s initial rs) p)
    (hfold : rs.foldlM step w₀ = .ok w) :
    openLog s recordMax step w₀ initial (encodeAll s initial rs ++ p) =
      .ok ⟨w, rs.length, (encodeAll s initial rs).size, lastTag s initial rs, p.size⟩ := by
  unfold openLog
  rw [recover_torn s initial rs hrs r p q hr hcut hq hin, if_neg (by omega)]
  simp only
  rw [(foldRecords_ok step rs w₀ w 0).mpr hfold]
  rfl

theorem open_sound (s : Sealer) {recordMax : Nat} (step : W → ByteArray → Except F W) (w₀ : W)
    (initial log : ByteArray) {o : Opened W} (h : openLog s recordMax step w₀ initial log = .ok o) :
    ∃ rs : List ByteArray, log.extract 0 o.validLen = encodeAll s initial rs ∧
      rs.foldlM step w₀ = .ok o.world ∧ o.lastTag = lastTag s initial rs ∧ o.records = rs.length := by
  obtain ⟨he, ht⟩ := encodeAll_recover s recordMax initial log
  unfold openLog at h
  generalize hrv : recover s recordMax initial log = rv at h he ht
  simp only at h
  split at h
  · cases h
  · split at h
    · rename_i w hw
      cases h
      exact ⟨rv.records, he, (foldRecords_ok step rv.records w₀ w 0).mp hw, ht, rfl⟩
    · cases h

end Nanodregg.Host
