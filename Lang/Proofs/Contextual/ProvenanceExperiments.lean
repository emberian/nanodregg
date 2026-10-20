/- P9 teeth on the actual CMTT checker; no bespoke calculus laws. -/
import Lang.Proofs.Contextual.Nogoods
import Lang.Proofs.Contextual.ProvenanceTeeth

namespace Nanodregg.Lang.Contextual.P9.Experiments

private def a : Token := ⟨1, 0⟩
private def b : Token := ⟨2, 0⟩
private def c : Token := ⟨3, 0⟩
private def I : Iface cmttData Bool :=
  ⟨0, [], .arr .base .base, [], by simp, fun env _ => env, 3, 1, 2⟩
private def cand (ss bs : List Token) (cost : Nat := 1) : Candidate cmttData :=
  ⟨.lam .base (.var 0), ss, bs, cost, 3, .verified⟩
private def cs : List (Candidate cmttData) :=
  [cand [a] [b], cand [c] [], cand [a, c] [b], cand [a] [a], cand [] [] 4]
private def w : World Bool := ⟨fun t => t == b, true⟩
private def tpl : Template cmttData Bool :=
  ⟨[], .arr .base .base, .mvar 0 [], [I], by simp [I]⟩
private def cl : RecordedClosure cmttData Bool :=
  { toClosure := fromScratch w tpl fun _ => cs, nogoods := [[a]] }

/-- Grädel–Tannen p19: all five candidates retain their environmental literals,
including a currently impossible budget; specializing a guard edit resurrects the branch. -/
theorem environment_literals_retained :
    (provenance I cs).length = 5 ∧
    (specialize I false (provenance I cs)) = [] ∧
    (specialize I true (provenance I cs)).length = 4 := by decide

/-- Grädel–Tannen Prop16 p23: two alternatives, one insertion plus one deletion or
one insertion; contradictory, over-budget and strictly larger plans are absent. -/
theorem computed_minimal_repairs :
    repairPlans I w cs = [[a, b], [c]] := by decide

/-- Grädel–Tannen Prop16 p23: both computed alternatives execute to verification
via the actual primitive edit interpreter; all unedited blockers stay meaningful. -/
theorem computed_repairs_execute :
    judge I (applyAll (tokenEdits w [a, b]) w) (cand [a] [b]) = .verified ∧
    judge I (applyAll (tokenEdits w [c]) w) (cand [c] []) = .verified ∧
    judge I (applyAll (tokenEdits w [a]) w) (cand [a] [b]) = .pruned [b] := by decide

/-- Grädel–Tannen §6 p19 / Prop16 p23: token-only repairs cannot invent a guard or
buy a larger budget. In particular a guard-failing residual has no token plan. -/
theorem token_repairs_respect_environment :
    repairPlans I ⟨w.live, false⟩ cs = [] ∧
    repairPlans I w [cand [] [] 4] = [] := by decide

/-- de Kleer p145: absorption removes a genuinely larger explanation, and the
complementary product is dead before any world is chosen (Grädel–Tannen Def4 p9). -/
theorem absorption_and_complements :
    label I [cand [a] [b], cand [a, c] [b], cand [a] [a]] =
      [monomial I (cand [a] [b])] := by decide

/-- de Kleer pp144–145: a missing support in a recorded nogood is a conflict, with
its recorded core; the original candidate judge would merely suspend. -/
theorem nogood_beats_missing :
    judge I ⟨fun _ => false, true⟩ (cand [a] []) = .suspended [a] ∧
    judgeRecorded cl I ⟨fun _ => false, true⟩ (cand [a] []) =
      ⟨.conflict .guardFails, some [a]⟩ := by decide

/-- de Kleer pp144–145 / Prop16 p23: the nogood database changes the computed
repair alternatives, and supplies the exact evidence of P5's refuted constructor. -/
theorem recorded_repairs_and_refutation :
    recordedRepairPlans cl I w cs = [[c]] ∧
    classifyRecorded cl I w (cand [a] []) = .refuted [a] ∧
    classifyRecorded cl I w (cand [c] []) = .open .admission [] := by exact ⟨by decide, rfl, rfl⟩

/-- de Kleer p145: recording the empty nogood makes every support inconsistent,
while a database containing an unrelated token must not exclude it. -/
theorem nogood_matching :
    findNogood [[]] [] = some [] ∧
    findNogood [[b]] [a] = none := by decide

/-- de Kleer p145: recorded consistency reaches a real selection consumer even
after the ordinary candidate judge verifies the repaired candidate. -/
theorem recorded_selection_refused :
    (Nanodregg.Lang.Contextual.select (applyAll (tokenEdits w [a, b]) w)
      1 0 0 cl.toClosure).isOk = true ∧
    (selectRecorded cl (applyAll (tokenEdits w [a, b]) w) 1 0 0).isOk = false := by decide

/-- de Kleer p145: effective supports include used context hypotheses, not only
the candidate's explicit IN list (Doyle's justification). -/
theorem nogood_checks_hypotheses :
    let J : Iface cmttData Bool :=
      ⟨0, [.base], .base, [(0, a)], by decide, fun _ _ => true, 3, 1, 2⟩
    let d : Candidate cmttData := ⟨.var 0, [], [], 1, 3, .verified⟩
    judgeRecorded cl J w d = ⟨.conflict .guardFails, some [a]⟩ := by decide

/-- Prop16 p23: a P4 residual is consumed directly, retaining its actual problem;
an unknown hole is not confused with an empty repair set. -/
theorem residual_computes_repairs :
    residualRepairPlans (⟨w, cl.toClosure, []⟩ : RepairObjects.Residual cmttData Bool) 0 =
      some [[a, b], [c]] ∧
    residualRepairPlans (⟨w, cl.toClosure, []⟩ : RepairObjects.Residual cmttData Bool) 9 =
      none := by decide

/-- Grädel–Tannen p19: typing alone is immutable and may be prefiltered;
ill-typed terms never enter the symbolic polynomial or repair enumeration. -/
theorem typing_stays_checked :
    provenance I [{ cand [] [] with filling := .var 0 }] = [] ∧
    repairPlans I w [{ cand [] [] with filling := .var 0 }] = [] := by decide

/-- de Kleer p145: absorption must compare negative and environmental literals
as well as positive supports; equal supports alone do not justify absorption. -/
theorem absorption_reads_all_literals :
    minimal [monomial I (cand [a] []), monomial I (cand [a] [b])] =
      [monomial I (cand [a] [])] ∧
    minimal [monomial I (cand [a] [] 4), monomial I (cand [a] [] 1)] =
      [monomial I (cand [a] [] 4), monomial I (cand [a] [] 1)] ∧
    findNogood [[a, b]] [a] = none := by decide

end Nanodregg.Lang.Contextual.P9.Experiments
