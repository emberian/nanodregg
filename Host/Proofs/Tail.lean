/-
# Host.Proofs.Tail — a tail folds what a reopen folds

* `absorbRecords_ok` — the tail's fold is `List.foldlM` of the step, each record's output pushed
  in order (the index only names a refusal);
* `absorb_encodeAll` — absorbing a clean run of frames written after the tail's position, chained
  from its tag, reaches the fold of exactly those records, with every record's output in order, and
  stands after the last of them with the chain tag a writer would chain the next frame from. Since
  `Tail.open` is the open and the step is the open's step (`Prod.fst` of the tail's), the tail is
  not a second replayer: it runs the open's recovery and fold, one stretch at a time.
-/
import Host.Tail
import Host.Proofs.Log

namespace Nanodregg.Host

open Nanodregg.Host.Log

variable {W F O : Type}

/-- One record of the tail's fold, as a `foldlM` step: the World advanced, the output pushed. -/
private def collect (step : W → ByteArray → Except F (W × O)) (p : W × Array O) (r : ByteArray) :
    Except F (W × Array O) :=
  match step p.1 r with
  | .ok (w', o) => .ok (w', p.2.push o)
  | .error f => .error f

theorem absorbRecords_ok (step : W → ByteArray → Except F (W × O)) (rs : List ByteArray) :
    ∀ (w : W) (os : Array O) (w' : W) (os' : Array O) (i : Nat),
      absorbRecords step w os i rs = .ok (w', os') ↔ rs.foldlM (collect step) (w, os) = .ok (w', os') := by
  induction rs with
  | nil => intro w os w' os' i; simp [absorbRecords, List.foldlM, pure, Except.pure]
  | cons r rs ih =>
    intro w os w' os' i
    simp only [absorbRecords, List.foldlM, collect]
    cases h : step w r with
    | ok v => simpa [bind, Except.bind] using ih v.1 (os.push v.2) w' os' (i + 1)
    | error f => simp [bind, Except.bind]

theorem lastTag_size (s : Sealer) (prev : ByteArray) (rs : List ByteArray) (h : prev.size = tagBytes) :
    (lastTag s prev rs).size = tagBytes := by
  induction rs generalizing prev with
  | nil => simpa [lastTag] using h
  | cons r rs ih => exact ih _ (s.tag_size _)

/-- **A tail absorbs what was written.** -/
theorem absorb_encodeAll (s : Sealer) {recordMax : Nat} (step : W → ByteArray → Except F (W × O))
    (t : Tail W) (rs : List ByteArray) (hrs : ∀ r ∈ rs, r.size ≤ recordMax ∧ r.size < 2 ^ 32)
    {w : W} {os : Array O} (hfold : rs.foldlM (collect step) (t.world, #[]) = .ok (w, os))
    (capped : Bool) (hc : capped = true → rs ≠ []) :
    ∃ tag : Codec.Digest, tag.bytes = lastTag s t.pos.tag.bytes rs ∧
      Tail.absorb s recordMax step t (encodeAll s t.pos.tag.bytes rs) capped =
        .ok (⟨w, ⟨t.pos.offset + (encodeAll s t.pos.tag.bytes rs).size, tag⟩⟩, os) := by
  have hsz : (lastTag s t.pos.tag.bytes rs).size = 32 := lastTag_size s _ rs t.pos.tag.size_eq
  refine ⟨⟨lastTag s t.pos.tag.bytes rs, hsz⟩, rfl, ?_⟩
  unfold Tail.absorb
  rw [recover_encodeAll s t.pos.tag.bytes rs hrs]
  simp only
  have hne : ¬ (capped && rs.isEmpty) = true := by
    cases capped
    · simp
    · simp only [Bool.true_and, List.isEmpty_iff]; exact hc rfl
  rw [if_neg hne, (absorbRecords_ok step rs t.world #[] w os 0).mpr hfold]
  simp only [Codec.Digest.ofBytes?, hsz, dif_pos]

end Nanodregg.Host
