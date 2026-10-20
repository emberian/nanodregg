/- Executable teeth for real CMTT candidates and checked complete observations. -/
import Lang.Contextual.TraceExamples
import Lang.Proofs.Contextual.Trace

namespace Nanodregg.Lang.Contextual.Trace.Examples

/-- No rejudgment for an unrelated environment edit; Mokhov et al. 2018, Def.2.1 p.79:3. -/
theorem unrelated_environment : (run (envEdit 99 0)).rejudged = [] := by decide

/-- A same-value write is clean; Mokhov et al. 2018, §4.2.2 p.79:14. -/
theorem equal_value_write : (run (envEdit 0 1)).rejudged = [] := by decide

/-- Real input change with the same result: rejudged once, no downstream dirty hole.
Mokhov et al. 2018, early cutoff §2.3 p.79:5. -/
theorem unchanged_status_cutoff :
    (run (envEdit 0 2)).rejudged = [0] ∧
    dirtyReaders (run (envEdit 0 2)) [(7, 0), (8, 1)] = [] := by decide

/-- An equal-output rebuild still refreshes its trace; otherwise it rebuilds forever.
Mokhov et al. 2018, §4.2.2 p.79:15. -/
theorem updated_trace_stays_clean :
    (repair guard iface (envEdit 0 2) (run (envEdit 0 2)).entries 0).rejudged = [] := by decide

/-- A guard failure changes the actual cached verdict and dirties only its reader.
Mokhov et al. 2018, Def.3.1 p.79:11 and §4.2.2 p.79:15. -/
theorem guard_change_propagates :
    ((run (envEdit 0 0)).entries.map fun c => c.candidate.status) =
      [.conflict .guardFails, .verified] ∧
    dirtyReaders (run (envEdit 0 0)) [(7, 0), (8, 1)] = [7] := by decide

/-- Declared positive support withdrawal is observed; Mokhov et al. 2018, §4.2.2 p.79:14. -/
theorem support_withdrawal :
    ((run (world.set ⟨1, 0⟩ false)).entries.map fun c => c.candidate.status) =
      [.suspended [⟨1, 0⟩], .verified] := by decide

/-- Used context hypotheses are reads even when not explicitly listed by the candidate.
Mokhov et al. 2018, §4.2.2 p.79:14. -/
theorem hypothesis_withdrawal :
    ((run (world.set ⟨2, 0⟩ false)).entries.map fun c => c.candidate.status) =
      [.suspended [⟨2, 0⟩], .verified] := by decide

/-- A blocker becoming live prunes, rather than leaving a cached success.
Mokhov et al. 2018, §4.2.2 p.79:14. -/
theorem blocker_assertion :
    ((run (world.set ⟨3, 0⟩ true)).entries.map fun c => c.candidate.status) =
      [.pruned [⟨3, 0⟩], .verified] := by decide

/-- Omitted blocker observation refuses before judging: the bridge HIGH's missing read.
Mokhov et al. 2018, §4.2.2 p.79:14. -/
theorem omitted_blocker_refused :
    checkedJudge guard iface (candidate 0) (fun k => some (world.env k))
      (fun t => if t = ⟨3, 0⟩ then none else some (world.live t)) =
        .error (.token ⟨3, 0⟩) := by rfl

/-- An explicitly observed absent blocker is accepted; omitted and absent differ.
Mokhov et al. 2018, §4.2.2 p.79:14. -/
theorem observed_absence_accepted :
    checkedJudge guard iface (candidate 0) (fun k => some (world.env k))
      (fun t => some (world.live t)) = .ok .verified := by rfl

/-- Omitted environment observation is also refused; Mokhov et al. 2018, §4.2.2 p.79:14. -/
theorem omitted_environment_refused :
    checkedJudge guard iface (candidate 0) (fun _ => none)
      (fun t => some (world.live t)) = .error (.environment 0) := by rfl

/-- A failing guard cannot hide incomplete negative observations.
Mokhov et al. 2018, §4.2.2 p.79:14. -/
theorem failing_guard_still_requires_coverage :
    checkedJudge guard iface (candidate 0) (fun _ => some 0)
      (fun t => if t = ⟨3, 0⟩ then none else some (world.live t)) =
        .error (.token ⟨3, 0⟩) := by rfl

/-- Repeated fillings have distinct work indices, each executed once.
Mokhov et al. 2018, Def.2.1 p.79:3. -/
theorem repeated_fillings_once :
    (repair guard iface (envEdit 0 2)
      [seed guard iface world (candidate 0), seed guard iface world (candidate 0)] 0).rejudged =
      [0, 1] := by decide

/-- The concrete cache inhabits the generic consistency premise.
Mokhov et al. 2018, Def.3.1 p.79:11. -/
theorem cached_valid : ∀ c ∈ cached, Valid guard iface c := by
  intro c hc
  simp only [cached, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> exact seed_valid _ _ _ _

end Nanodregg.Lang.Contextual.Trace.Examples
