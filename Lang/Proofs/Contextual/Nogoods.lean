/- Recorded nogoods: consistency, provenance, repairs, refutations and selection. -/
import Lang.Contextual.Nogoods
import Lang.Proofs.Contextual.ProvenanceRepairs

namespace Nanodregg.Lang.Contextual.P9

variable {D : CalculusData} {E : Type}

/-- de Kleer pp144–145: a returned conflict core is actually recorded and contained in the support. -/
theorem findNogood_sound {ngs : List (List Token)} {supports ng : List Token}
    (h : findNogood ngs supports = some ng) :
    ng ∈ ngs ∧ ∀ t ∈ ng, t ∈ supports := by
  exact ⟨List.mem_of_find?_eq_some h, by
    simpa [List.all_eq_true] using (List.find?_some h)⟩

/-- de Kleer pp144–145: every recorded inconsistent support is found; empty nogoods count too. -/
theorem findNogood_complete {ngs : List (List Token)} {supports ng : List Token}
    (hm : ng ∈ ngs) (hs : ∀ t ∈ ng, t ∈ supports) :
    ∃ core, findNogood ngs supports = some core := by
  cases hf : findNogood ngs supports with
  | some core => exact ⟨core, rfl⟩
  | none =>
    have hn := List.find?_eq_none.mp hf ng hm
    have ht : (ng.all fun t => decide (t ∈ supports)) = true := by
      simpa [List.all_eq_true] using hs
    rw [ht] at hn
    exact False.elim (hn rfl)

/-- de Kleer p145: a support containing a nogood is a conflict with a recorded core,
even if every support is missing; it is never merely suspended. -/
theorem judge_respects_nogoods {cl : RecordedClosure D E} {I : Iface D E}
    {w : World E} {c : Candidate D} {ng : List Token}
    (hm : ng ∈ cl.nogoods) (hs : ∀ t ∈ ng, t ∈ effSupports I c) :
    ∃ core, judgeRecorded cl I w c = ⟨.conflict .guardFails, some core⟩ ∧
      core ∈ cl.nogoods ∧ ∀ t ∈ core, t ∈ effSupports I c := by
  obtain ⟨core, hc⟩ := findNogood_complete hm hs
  exact ⟨core, by simp [judgeRecorded, hc], findNogood_sound hc⟩

/-- de Kleer p145: recorded inconsistency never masquerades as missing support. -/
theorem nogood_never_suspended {cl : RecordedClosure D E} {I : Iface D E}
    {w : World E} {c : Candidate D} {ng : List Token} (hm : ng ∈ cl.nogoods)
    (hs : ∀ t ∈ ng, t ∈ effSupports I c) (missing : List Token) :
    (judgeRecorded cl I w c).status ≠ .suspended missing := by
  obtain ⟨core, hc, _⟩ := judge_respects_nogoods (w := w) hm hs
  simp [hc]

/-- de Kleer p145: successful judgment means original verification AND no recorded inconsistent subset. -/
theorem judgeRecorded_verified {cl : RecordedClosure D E} {I : Iface D E}
    {w : World E} {c : Candidate D} :
    (judgeRecorded cl I w c).status = .verified ↔
      findNogood cl.nogoods (effSupports I c) = none ∧ judge I w c = .verified := by
  cases h : findNogood cl.nogoods (effSupports I c) <;> simp [judgeRecorded, h]

/-- de Kleer pp144–145 / Grädel–Tannen p19: the complete all-env label under recorded consistency. -/
theorem recordedLabel_iff {cl : RecordedClosure D E} {I : Iface D E}
    {w : World E} {cs : List (Candidate D)} :
    (∃ c ∈ cs, (judgeRecorded cl I w c).status = .verified) ↔
      ∃ m ∈ recordedLabel cl I cs, m.eval I w = true := by
  rw [recordedLabel, ← label_iff]
  simp only [eligibleCandidates, List.mem_filter, judgeRecorded_verified]
  constructor
  · rintro ⟨c, hc, hn, hv⟩
    exact ⟨c, ⟨hc, by simp [hn]⟩, hv⟩
  · rintro ⟨c, ⟨hc, hn⟩, hv⟩
    exact ⟨c, hc, by simpa using hn, hv⟩

/-- Grädel–Tannen Prop16 p23: computed repairs survive the SAME nogood-aware judge. -/
theorem recordedRepairs_sound {cl : RecordedClosure D E} {I : Iface D E}
    {w : World E} {cs : List (Candidate D)} {ts : List Token}
    (h : ts ∈ recordedRepairPlans cl I w cs) :
    ∃ c ∈ cs, (judgeRecorded cl I (applyAll (tokenEdits w ts) w) c).status = .verified := by
  obtain ⟨c, hc, hv⟩ := repairPlans_sound h
  obtain ⟨hc, hn⟩ := List.mem_filter.mp hc
  exact ⟨c, hc, judgeRecorded_verified.mpr ⟨by simpa using hn, hv⟩⟩

/-- de Kleer p145: P5's refuted value is justified by a retained nogood, and
rules out this candidate in EVERY world. It is relative to the recorded database,
not a proof that arbitrary token propositions logically imply False. -/
theorem recorded_refuted {cl : RecordedClosure D E} {I : Iface D E}
    {w : World E} {c : Candidate D} {ng : List Token}
    (h : classifyRecorded cl I w c = .refuted ng) :
    ng ∈ cl.nogoods ∧ (∀ t ∈ ng, t ∈ effSupports I c) ∧
      ∀ v : World E, (judgeRecorded cl I v c).status ≠ .verified := by
  unfold classifyRecorded judgeRecorded at h
  cases hf : findNogood cl.nogoods (effSupports I c) with
  | none =>
    simp only [hf] at h
    split at h <;> cases h
  | some core =>
    simp only [hf] at h
    cases h
    obtain ⟨hm, hs⟩ := findNogood_sound hf
    exact ⟨hm, hs, fun v => by simp [judgeRecorded, hf]⟩

/-- de Kleer p145: the closure policy has an operational consumer; a recorded nogood
prevents selection even when the original judge would verify the candidate. -/
theorem select_respects_nogoods {cl : RecordedClosure D E} {I : Iface D E}
    {w : World E} {c : Candidate D} {u i : Nat} {ng : List Token}
    (hI : cl.toClosure.find u = some I) (hc : (cl.slot u).cands[i]? = some c)
    (hm : ng ∈ cl.nogoods) (hs : ∀ t ∈ ng, t ∈ effSupports I c) (p : Party) :
    selectRecorded cl w p u i = .error (.notVerified (.conflict .guardFails)) := by
  obtain ⟨core, hn⟩ := findNogood_complete hm hs
  simp [selectRecorded, hI, hc, hn]

end Nanodregg.Lang.Contextual.P9
