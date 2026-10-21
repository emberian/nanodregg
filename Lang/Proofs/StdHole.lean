/- Semantics of the generated hole's decision code. -/
import Lang.StdHoleModel
import Lang.Proofs.StdActivity

namespace Nanodregg.Lang.Std


private theorem nat_eq_step (lib : List Term) (env : Env) (i n m : Nat)
    (hi : env[i]? = some (.nat n)) :
    BigStep lib env (.prim .eq (.var i) (.nat m)) (.ok (.bool (decide (n = m)))) :=
  .prim (.var hi) .nat (by simp [primEval])

/-- Every combination of clause, blocker and support observations computes a
specific judgment. Negative observations are retained as statuses by rejudge;
select and fill turn the same nonverified judgment into a named refusal. -/
theorem holeDecision_application (allowed blocked : Bool) (s0 s1 : Nat)
    (lib : List Term) (env : Env) (a b x y : Term)
    (ha : BigStep lib env a (.ok (.bool allowed)))
    (hb : BigStep lib env b (.ok (.bool blocked)))
    (hx : BigStep lib env x (.ok (.nat s0)))
    (hy : BigStep lib env y (.ok (.nat s1))) :
    BigStep lib env (activityApply holeDecision [a, b, x, y])
      (.ok (.inj (holeVerdictLabel allowed blocked s0 s1) (.record []))) := by
  apply BigStep.app
    (BigStep.app (BigStep.app (BigStep.app .lam ha .lam) hb .lam) hx .lam) hy
  cases allowed with
  | false => exact .iteF (.var rfl) (.inj .record)
  | true =>
    apply BigStep.iteT (.var rfl)
    cases blocked with
    | true => exact .iteT (.var rfl) (.inj .record)
    | false =>
      apply BigStep.iteF (.var rfl)
      let e : Env := .nat s1 :: .nat s0 :: .bool false :: .bool true :: env
      have eq0 (m : Nat) := nat_eq_step lib e 1 s0 m rfl
      have eq1 (m : Nat) := nat_eq_step lib e 0 s1 m rfl
      by_cases h0 : s0 = 1
      · apply BigStep.iteT (by simpa [e, *] using eq0 1)
        by_cases h1 : s1 = 1
        · simp only [holeVerdictLabel, Bool.not_true, Bool.false_eq_true,
            ↓reduceIte, h0, h1, bne_self_eq_false]
          exact .iteT (by simpa [e, *] using eq1 1) (.inj .record)
        · apply BigStep.iteF (by simpa [e, *] using eq1 1)
          by_cases h2 : s1 = 2
          · simp [holeVerdictLabel, *]
            exact .iteT (by simpa [e, *] using eq1 2) (.inj .record)
          · simp [holeVerdictLabel, *]
            exact .iteF (by simpa [e, *] using eq1 2) (.inj .record)
      · apply BigStep.iteF (by simpa [e, *] using eq0 1)
        by_cases h2 : s0 = 2
        · simp [holeVerdictLabel, *]
          exact .iteT (by simpa [e, *] using eq0 2) (.inj .record)
        · simp [holeVerdictLabel, *]
          exact .iteF (by simpa [e, *] using eq0 2) (.inj .record)


theorem holeDecision_meaning (allowed blocked : Bool) (s0 s1 : Nat)
    (lib : List Term) (env : Env) :
    BigStep lib (.nat s1 :: .nat s0 :: .bool blocked :: .bool allowed :: env)
      (activityApply holeDecision [.var 3, .var 2, .var 1, .var 0])
      (.ok (.inj (holeVerdictLabel allowed blocked s0 s1) (.record []))) :=
  holeDecision_application allowed blocked s0 s1 lib _ _ _ _ _
    (.var rfl) (.var rfl) (.var rfl) (.var rfl)

/-- Compose the actual clause and pinned probe evaluations through the generated
judge. The four premises evaluate individual observations, never the judgment
being proved; the candidate's recorded status is not an observation. -/
theorem holeJudge_application (V : Ty) (clause : Term)
    (lib : List Term) (env : Env) (state candidate rows : Val)
    (ts tc tr : Term)
    (hs : BigStep lib env ts (.ok state))
    (hc : BigStep lib env tc (.ok candidate))
    (hr : BigStep lib env tr (.ok rows))
    (allowed blocked : Bool) (s0 s1 : Nat)
    (ha : BigStep lib (holeJudgeEnv rows candidate state env)
      (holeObservation clause 0) (.ok (.bool allowed)))
    (hb : BigStep lib (holeJudgeEnv rows candidate state env)
      (holeObservation clause 1) (.ok (.bool blocked)))
    (h0 : BigStep lib (holeJudgeEnv rows candidate state env)
      (holeObservation clause 2) (.ok (.nat s0)))
    (h1 : BigStep lib (holeJudgeEnv rows candidate state env)
      (holeObservation clause 3) (.ok (.nat s1))) :
    BigStep lib env (activityApply (holeJudge V clause) [ts, tc, tr])
      (.ok (.inj (holeVerdictLabel allowed blocked s0 s1) (.record []))) := by
  apply BigStep.app (BigStep.app (BigStep.app .lam hs .lam) hc .lam) hr
  apply BigStep.app .lam .lam
  exact holeDecision_application allowed blocked s0 s1 lib _ _ _ _ _ ha hb h0 h1

/-- Each well-formed judgment reaches exactly its named refusal or success.
This is the actual shared gate invoked by select/fill/accept. -/
theorem holeVerdictCheck_application (l : Label)
    (hl : l ∈ ["conflict", "pruned", "support0Moved", "support0Withdrawn",
      "support1Moved", "support1Withdrawn", "verified"])
    (lib : List Term) (env : Env) (t : Term)
    (ht : BigStep lib env t (.ok (.inj l (.record [])))) :
    BigStep lib env (.app holeVerdictCheck t) (holeAdmission l) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with h | h | h | h | h | h | h <;> subst l
  all_goals
    apply BigStep.app .lam ht
    apply BigStep.case (.var rfl) rfl
    first | exact .refuse | exact .bool

theorem holeVerdictCheck_meaning (l : Label)
    (hl : l ∈ ["conflict", "pruned", "support0Moved", "support0Withdrawn",
      "support1Moved", "support1Withdrawn", "verified"])
    (lib : List Term) (env : Env) :
    BigStep lib (.inj l (.record []) :: env)
      (.app holeVerdictCheck (.var 0)) (holeAdmission l) :=
  holeVerdictCheck_application l hl lib _ _ (.var rfl)

/-- The checked gate admits precisely the verified branch; arbitrary alternative
evaluations cannot turn a refusal into a success. -/
theorem holeVerdictCheck_admits_iff (l : Label)
    (hl : l ∈ ["conflict", "pruned", "support0Moved", "support0Withdrawn",
      "support1Moved", "support1Withdrawn", "verified"])
    (lib : List Term) (env : Env) :
    (∃ v, BigStep lib (.inj l (.record []) :: env)
      (.app holeVerdictCheck (.var 0)) (.ok v)) ↔ l = "verified" := by
  constructor
  · rintro ⟨v, hv⟩
    have he := bigStep_deterministic (holeVerdictCheck_meaning l hl lib env) hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with h | h | h | h | h | h | h <;> subst l <;>
      simp [holeAdmission] at he ⊢
  · intro he
    subst l
    exact ⟨.bool true, holeVerdictCheck_meaning _ hl lib env⟩


/-- Gate equivalence for an evaluated judgment expression, including the
generated holeJudge application, rather than only a literal verdict. -/
theorem holeVerdictCheck_evaluated_iff (l : Label)
    (hl : l ∈ ["conflict", "pruned", "support0Moved", "support0Withdrawn",
      "support1Moved", "support1Withdrawn", "verified"])
    (lib : List Term) (env : Env) (t : Term)
    (ht : BigStep lib env t (.ok (.inj l (.record [])))) :
    (∃ v, BigStep lib env (.app holeVerdictCheck t) (.ok v)) ↔ l = "verified" := by
  constructor
  · rintro ⟨v, hv⟩
    have he := bigStep_deterministic (holeVerdictCheck_application l hl lib env t ht) hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with h | h | h | h | h | h | h <;> subst l <;>
      simp [holeAdmission] at he ⊢
  · intro he
    subst l
    exact ⟨.bool true, holeVerdictCheck_application _ hl lib env t ht⟩

/-- Rejudge's renderer records every negative judgment, including the retained
pruning reason; it does not convert a negative judgment into an evaluation fault. -/
theorem holeStatusOf_application (l : Label) (reason : ByteArray)
    (hl : l ∈ ["conflict", "pruned", "support0Moved", "support0Withdrawn",
      "support1Moved", "support1Withdrawn", "verified"])
    (lib : List Term) (env : Env) (rt vt : Term)
    (hr : BigStep lib env rt (.ok (.bytes reason)))
    (hv : BigStep lib env vt (.ok (.inj l (.record [])))) :
    BigStep lib env (activityApply holeStatusOf [rt, vt])
      (.ok (holeRecordedStatus l reason).toVal) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with h | h | h | h | h | h | h <;> subst l
  all_goals
    apply BigStep.app (BigStep.app .lam hr .lam) hv
    apply BigStep.case (.var rfl) rfl
    first | exact .inj .bytes | exact .inj (.var rfl) | exact .inj .record


theorem holeStatusOf_meaning (l : Label) (reason : ByteArray)
    (hl : l ∈ ["conflict", "pruned", "support0Moved", "support0Withdrawn",
      "support1Moved", "support1Withdrawn", "verified"])
    (lib : List Term) (env : Env) :
    BigStep lib (.inj l (.record []) :: .bytes reason :: env)
      (activityApply holeStatusOf [.var 1, .var 0])
      (.ok (holeRecordedStatus l reason).toVal) :=
  holeStatusOf_application l reason hl lib _ _ _ (.var rfl) (.var rfl)

end Nanodregg.Lang.Std



