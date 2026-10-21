/- The generated hole's decision gate against the landed contextual judgment. -/
import Lang.Contextual.HoleModel
import Lang.Proofs.Contextual.Judge
import Lang.Proofs.Contextual.LangInstance
import Lang.Proofs.StdHoleCoverage

namespace Nanodregg.Lang.Contextual

variable {E : Type}

open Std

/-- Every generated interface inhabits the landed closed-hole Lang instance.
This is the empty-context specialization of the live contextual signature. -/
theorem holeModelTemplate_typed (V : Lang.Ty) (guard : E → Term → Bool)
    (chooser acceptor : Party) :
    Template.Typed (holeModelTemplate V guard chooser acceptor) LangHasTy := by
  exact .hole (d := ⟨0, [], V⟩) rfl .nil

/-- In the deployed closed fragment, checker/guard/support/blocker observations
characterise verified judgment. Historical row status contributes no premise. -/
theorem holeModel_verified_iff (I : Iface langData E) (w : World E)
    (value : Term) (s0 s1 blocker : Option Token) (by_ : Party) (recorded : Status)
    (hctx : I.ctx = []) (hhyps : I.hyps = [])
    (htyped : Lang.infer [] [] value = some I.ty) :
    judge I w (holeModelCandidate value s0 s1 blocker by_ recorded) = .verified ↔
      I.guard w.env value = true ∧ holeBlocked w blocker = false ∧
        holeLive w s0 = true ∧ holeLive w s1 = true := by
  rw [judge_verified_iff]
  have hc : langData.check I.ctx value I.ty = true := by
    simp [langData, hctx, htyped]
  cases s0 <;> cases s1 <;> cases blocker <;>
    simp [holeModelCandidate, effSupports, hhyps, holeLive, holeBlocked, hc]

/-- The generated decision label is verified exactly for the same observations.
Probe codes distinguish moved from withdrawn for reporting; both are non-live. -/
theorem holeDecision_verified_iff (allowed blocked : Bool) (s0 s1 : Nat) :
    holeVerdictLabel allowed blocked s0 s1 = "verified" ↔
      allowed = true ∧ blocked = false ∧ s0 = 1 ∧ s1 = 1 := by
  cases allowed <;> cases blocked <;>
    by_cases h0 : s0 = 1 <;> by_cases h1 : s1 = 1 <;>
    by_cases h2 : s0 = 2 <;> by_cases h3 : s1 = 2 <;>
    simp [holeVerdictLabel, *]

theorem holeDecision_label (allowed blocked : Bool) (s0 s1 : Nat) :
    holeVerdictLabel allowed blocked s0 s1 ∈
      ["conflict", "pruned", "support0Moved", "support0Withdrawn",
        "support1Moved", "support1Withdrawn", "verified"] := by
  cases allowed <;> cases blocked <;>
    by_cases h0 : s0 = 1 <;> by_cases h1 : s1 = 1 <;>
    by_cases h2 : s0 = 2 <;> by_cases h3 : s1 = 2 <;>
    simp [holeVerdictLabel, *]

/-- Actual admission-code evaluation agrees with the existing Lang closure
judgment. Observation premises describe the pinned support probes; neither
admission nor verified judgment is assumed. -/
theorem holeAdmission_judge_iff (I : Iface langData E) (w : World E)
    (value : Term) (s0 s1 blocker : Option Token) (by_ : Party) (recorded : Status)
    (hctx : I.ctx = []) (hhyps : I.hyps = [])
    (htyped : Lang.infer [] [] value = some I.ty)
    (p0 p1 : Nat)
    (hp0 : p0 = 1 ↔ holeLive w s0 = true)
    (hp1 : p1 = 1 ↔ holeLive w s1 = true)
    (lib : List Term) (env : Env) :
    (∃ v, BigStep lib
      (.inj (holeVerdictLabel (I.guard w.env value) (holeBlocked w blocker) p0 p1)
        (.record []) :: env)
      (.app holeVerdictCheck (.var 0)) (.ok v)) ↔
      judge I w (holeModelCandidate value s0 s1 blocker by_ recorded) = .verified := by
  rw [holeVerdictCheck_admits_iff _ (holeDecision_label ..),
    holeDecision_verified_iff,
    holeModel_verified_iff I w value s0 s1 blocker by_ recorded hctx hhyps htyped,
    hp0, hp1]


/-- Raw decision correspondence, useful beneath the checked receive wrapper.
The deployed wrapper additionally requires complete declared observations. -/
theorem holeJudge_fixed_observations (I : Iface langData E) (w : World E)
    (value : Term) (s0 s1 blocker : Option Token) (by_ : Party) (recorded : Status)
    (hctx : I.ctx = []) (hhyps : I.hyps = [])
    (htyped : Lang.infer [] [] value = some I.ty)
    (clause : Term) (lib : List Term) (env : Env)
    (state candidate rows : Val) (ts tc tr : Term)
    (hs : BigStep lib env ts (.ok state))
    (hc : BigStep lib env tc (.ok candidate))
    (hr : BigStep lib env tr (.ok rows))
    (p0 p1 : Nat)
    (hp0 : p0 = 1 ↔ holeLive w s0 = true)
    (hp1 : p1 = 1 ↔ holeLive w s1 = true)
    (ha : BigStep lib (holeJudgeEnv rows candidate state env)
      (holeObservation clause 0) (.ok (.bool (I.guard w.env value))))
    (hb : BigStep lib (holeJudgeEnv rows candidate state env)
      (holeObservation clause 1) (.ok (.bool (holeBlocked w blocker))))
    (h0 : BigStep lib (holeJudgeEnv rows candidate state env)
      (holeObservation clause 2) (.ok (.nat p0)))
    (h1 : BigStep lib (holeJudgeEnv rows candidate state env)
      (holeObservation clause 3) (.ok (.nat p1))) :
    (∃ v, BigStep lib env
      (.app holeVerdictCheck (activityApply (holeJudge I.ty clause) [ts, tc, tr])) (.ok v)) ↔
      judge I w (holeModelCandidate value s0 s1 blocker by_ recorded) = .verified := by
  have hj := holeJudge_application I.ty clause lib env state candidate rows ts tc tr
    hs hc hr (I.guard w.env value) (holeBlocked w blocker) p0 p1 ha hb h0 h1
  rw [holeVerdictCheck_evaluated_iff _ (holeDecision_label ..) lib env _ hj,
    holeDecision_verified_iff,
    holeModel_verified_iff I w value s0 s1 blocker by_ recorded hctx hhyps htyped,
    hp0, hp1]

/-- Deployed judgment-segment admission: collection must finish AND the current
contextual judgment must verify. Completeness is not a premise. Only provided
observations are authenticated; omissions refuse before a verdict, including
before rejudge can record a status. Authority/existence/window checks precede
this segment, and kernel staleness/resource checks follow it. -/
theorem hole_judgment_admission_bridge (I : Iface langData E) (w : World E)
    (value : Term) (s0 s1 blocker : Option Token) (by_ : Party) (recorded : Status)
    (hctx : I.ctx = []) (hhyps : I.hyps = [])
    (htyped : Lang.infer [] [] value = some I.ty)
    (clause : Term) (lib : List Term) (env : Env)
    (state candidate rows : Val) (ts tc tr : Term)
    (hs : BigStep lib env ts (.ok state))
    (hc : BigStep lib env tc (.ok candidate))
    (hr : BigStep lib env tr (.ok rows))
    (c0 c1 cb blocked : Bool) (p0 p1 : Nat)
    (hp0 : c0 = true → (p0 = 1 ↔ holeLive w s0 = true))
    (hp1 : c1 = true → (p1 = 1 ↔ holeLive w s1 = true))
    (hpb : cb = true → blocked = holeBlocked w blocker)
    (hc0 : BigStep lib (holeCoverageEnv rows candidate state env)
      (holeCoverageObservation 0) (.ok (.bool c0)))
    (hc1 : BigStep lib (holeCoverageEnv rows candidate state env)
      (holeCoverageObservation 1) (.ok (.bool c1)))
    (hcb : BigStep lib (holeCoverageEnv rows candidate state env)
      (holeCoverageObservation 2) (.ok (.bool cb)))
    (ha : BigStep lib (holeJudgeEnv rows candidate state (holeCheckedEnv rows candidate state env))
      (holeObservation clause 0) (.ok (.bool (I.guard w.env value))))
    (hb : BigStep lib (holeJudgeEnv rows candidate state (holeCheckedEnv rows candidate state env))
      (holeObservation clause 1) (.ok (.bool blocked)))
    (h0 : BigStep lib (holeJudgeEnv rows candidate state (holeCheckedEnv rows candidate state env))
      (holeObservation clause 2) (.ok (.nat p0)))
    (h1 : BigStep lib (holeJudgeEnv rows candidate state (holeCheckedEnv rows candidate state env))
      (holeObservation clause 3) (.ok (.nat p1))) :
    (∃ v, BigStep lib env
      (.app holeVerdictCheck (activityApply (holeCheckedJudge I.ty clause) [ts, tc, tr])) (.ok v)) ↔
      (∃ v, holeCoverageOutcome c0 c1 cb = .ok v) ∧
      judge I w (holeModelCandidate value s0 s1 blocker by_ recorded) = .verified := by
  have hj := holeCheckedJudge_application I.ty clause lib env state candidate rows ts tc tr
    hs hc hr c0 c1 cb (I.guard w.env value) blocked p0 p1 hc0 hc1 hcb ha hb h0 h1
  rw [holeCheckedAdmission_evaluated_iff _ _ _ _ (holeDecision_label ..) lib env _ hj,
    holeCoverageOutcome_ok_iff]
  constructor
  · rintro ⟨hcov0, hcov1, hcovb, hv⟩
    refine ⟨⟨hcov0, hcov1, hcovb⟩, ?_⟩
    rw [holeModel_verified_iff I w value s0 s1 blocker by_ recorded hctx hhyps htyped]
    rw [holeDecision_verified_iff] at hv
    exact ⟨hv.1, (hpb hcovb) ▸ hv.2.1, (hp0 hcov0).mp hv.2.2.1,
      (hp1 hcov1).mp hv.2.2.2⟩
  · rintro ⟨⟨hcov0,hcov1,hcovb⟩, hv⟩
    refine ⟨hcov0,hcov1,hcovb, ?_⟩
    rw [holeDecision_verified_iff, hpb hcovb, hp0 hcov0, hp1 hcov1]
    exact (holeModel_verified_iff I w value s0 s1 blocker by_ recorded hctx hhyps htyped).mp hv

/-- Fixed complete observations recover the previous correspondence as a
corollary of the deployed collector. This logical specialization is not a
caller precondition: the generated coverage expressions enforce it. -/
theorem hole_judgment_admission_fixed_observations (I : Iface langData E) (w : World E)
    (value : Term) (s0 s1 blocker : Option Token) (by_ : Party) (recorded : Status)
    (hctx : I.ctx = []) (hhyps : I.hyps = [])
    (htyped : Lang.infer [] [] value = some I.ty)
    (clause : Term) (lib : List Term) (env : Env)
    (state candidate rows : Val) (ts tc tr : Term)
    (hs : BigStep lib env ts (.ok state))
    (hc : BigStep lib env tc (.ok candidate))
    (hr : BigStep lib env tr (.ok rows))
    (p0 p1 : Nat)
    (hp0 : p0 = 1 ↔ holeLive w s0 = true)
    (hp1 : p1 = 1 ↔ holeLive w s1 = true)
    (hc0 : BigStep lib (holeCoverageEnv rows candidate state env)
      (holeCoverageObservation 0) (.ok (.bool true)))
    (hc1 : BigStep lib (holeCoverageEnv rows candidate state env)
      (holeCoverageObservation 1) (.ok (.bool true)))
    (hcb : BigStep lib (holeCoverageEnv rows candidate state env)
      (holeCoverageObservation 2) (.ok (.bool true)))
    (ha : BigStep lib (holeJudgeEnv rows candidate state (holeCheckedEnv rows candidate state env))
      (holeObservation clause 0) (.ok (.bool (I.guard w.env value))))
    (hb : BigStep lib (holeJudgeEnv rows candidate state (holeCheckedEnv rows candidate state env))
      (holeObservation clause 1) (.ok (.bool (holeBlocked w blocker))))
    (h0 : BigStep lib (holeJudgeEnv rows candidate state (holeCheckedEnv rows candidate state env))
      (holeObservation clause 2) (.ok (.nat p0)))
    (h1 : BigStep lib (holeJudgeEnv rows candidate state (holeCheckedEnv rows candidate state env))
      (holeObservation clause 3) (.ok (.nat p1))) :
    (∃ v, BigStep lib env
      (.app holeVerdictCheck (activityApply (holeCheckedJudge I.ty clause) [ts, tc, tr])) (.ok v)) ↔
      judge I w (holeModelCandidate value s0 s1 blocker by_ recorded) = .verified := by
  have h := hole_judgment_admission_bridge I w value s0 s1 blocker by_ recorded
    hctx hhyps htyped clause lib env state candidate rows ts tc tr hs hc hr
    true true true (holeBlocked w blocker) p0 p1 (fun _ => hp0) (fun _ => hp1) (fun _ => rfl)
    hc0 hc1 hcb ha hb h0 h1
  simpa only [holeCoverageOutcome_ok_iff, true_and] using h

/-- Once the independent chooser and existence checks hold, select succeeds
precisely when the current judgment is verified. -/
theorem hole_select_iff (I : Iface langData E) (w : World E)
    (cl : Closure langData E) (u i : Nat) (c : Candidate langData)
    (hf : cl.find u = some I) (hc : (cl.slot u).cands[i]? = some c)
    (ha : (cl.slot u).accepted = false) :
    (∃ cl', select w I.chooser u i cl = .ok cl') ↔ judge I w c = .verified := by
  simp only [select, hf, ne_eq, not_true_eq_false, ↓reduceIte, ha,
    Bool.false_eq_true, hc]
  split <;> simp_all

/-- Fill recomputes the new candidate's judgment after proposal, without trusting
its supplied recorded status. Its acceptance criterion is the same as select. -/
theorem hole_fill_iff (I : Iface langData E) (w : World E)
    (cl : Closure langData E) (u : Nat) (c : Candidate langData)
    (hf : cl.find u = some I) (ha : (cl.slot u).accepted = false) :
    (∃ cl', fill w I.chooser u c cl = .ok cl') ↔ judge I w c = .verified := by
  simp only [fill, propose, hf]
  have hfind : ∀ slot owed hist,
      (Closure.mk cl.tpl slot owed hist).find u = some I := fun _ _ _ => hf
  simp only [select, hfind, ne_eq, not_true_eq_false, ↓reduceIte,
    Closure.update, ha, Bool.false_eq_true]
  simp only [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self,
    List.getElem?_cons_zero]
  have hj : judge I w { c with status := judge I w c } = judge I w c := rfl
  rw [hj]
  split <;> simp_all

/-- A present row's rejudged status is exactly the current judgment, including
conflict/suspended/pruned. There is no refusal branch and no history append. -/
theorem hole_rejudge_status (I : Iface langData E) (w : World E)
    (cl : Closure langData E) (u i : Nat) (c : Candidate langData)
    (hf : cl.find u = some I) (hc : (cl.slot u).cands[i]? = some c) :
    ((rejudge w u i cl).slot u).cands[i]? = some { c with status := judge I w c } := by
  simp only [rejudge, hf, hc, Closure.update, ↓reduceIte]
  exact List.getElem?_set_self (List.getElem?_eq_some_iff.mp hc).1

end Nanodregg.Lang.Contextual

