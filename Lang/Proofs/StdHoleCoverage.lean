/- The emitted observation collector refines P10's complete finite collection. -/
import Lang.Proofs.StdHoleLookup

namespace Nanodregg.Lang.Std

/-- Successful collection establishes coverage and exact values, assuming only that PROVIDED
observations are authentic. Completeness is the conclusion. Mokhov et al. 2018, §4.2.2 p.79:14. -/
theorem collect_sound {A B R : Type} (missing : A → R) (read : A → Option B)
    (f : A → B) (agree : ∀ k v, read k = some v → v = f k)
    (ks : List A) (vs : List B) (h : collect missing read ks = .ok vs) :
    vs = ks.map f ∧ ∀ k ∈ ks, read k = some (f k) := by
  induction ks generalizing vs with
  | nil => simp [collect] at h; subst vs; simp
  | cons k ks ih =>
    cases hk : read k with
    | none => simp [collect, hk] at h
    | some v =>
      cases hr : collect missing read ks with
      | error e => simp [collect, hk, hr] at h
      | ok rest =>
        simp [collect, hk, hr] at h
        subst vs
        obtain ⟨rfl, hrest⟩ := ih _ hr
        have hv := agree k v hk
        subst v
        exact ⟨rfl, by simpa [hk] using hrest⟩

/-- Honest total observations always collect; this supplies the success-side inhabitant.
Mokhov et al. 2018, §4.2.2 p.79:14. -/
theorem collect_total {A B R : Type} (missing : A → R) (f : A → B) (ks : List A) :
    collect missing (fun k => some (f k)) ks = .ok (ks.map f) := by
  induction ks with
  | nil => rfl
  | cons k ks ih => simp [collect, ih]

/-- An omitted declared key prevents success, including negative/blocker reads.
Mokhov et al. 2018, §4.2.2 p.79:14. -/
theorem collect_missing {A B R : Type} (missing : A → R) (read : A → Option B)
    (ks : List A) (k : A) (hk : k ∈ ks) (hn : read k = none) :
    ∀ vs, collect missing read ks ≠ .ok vs := by
  induction ks with
  | nil => cases hk
  | cons a ks ih =>
    intro vs h
    cases ha : read a with
    | none => simp [collect, ha] at h
    | some v =>
      rcases List.mem_cons.1 hk with rfl | hk
      · rw [ha] at hn; cases hn
      · cases hr : collect missing read ks with
        | error e => simp [collect, ha, hr] at h
        | ok rest => exact ih hk rest hr

/-- The actual emitted check equals P10 collect on all eight coverage cases.
In particular, missing a blocker cannot be interpreted as observed absence. -/
theorem holeCoverageCheck_application (c0 c1 cb : Bool)
    (lib : List Term) (env : Env) (a b c : Term)
    (ha : BigStep lib env a (.ok (.bool c0)))
    (hb : BigStep lib env b (.ok (.bool c1)))
    (hc : BigStep lib env c (.ok (.bool cb))) :
    BigStep lib env (activityApply holeCoverageCheck [a,b,c])
      (holeCoverageOutcome c0 c1 cb) := by
  apply BigStep.app (BigStep.app (BigStep.app .lam ha .lam) hb .lam) hc
  cases c0
  · exact .iteF (.var rfl) .refuse
  · apply BigStep.iteT (.var rfl)
    cases c1
    · exact .iteF (.var rfl) .refuse
    · apply BigStep.iteT (.var rfl)
      cases cb
      · exact .iteF (.var rfl) .refuse
      · exact .iteT (.var rfl) .bool

/-- Successful emitted collection establishes all three observations. -/
theorem holeCoverageOutcome_ok_iff (c0 c1 cb : Bool) :
    (∃ v, holeCoverageOutcome c0 c1 cb = .ok v) ↔
      c0 = true ∧ c1 = true ∧ cb = true := by
  cases c0 <;> cases c1 <;> cases cb <;> simp [holeCoverageOutcome,
    collect, Except.map]

/-- **A missing observation is refused `unpinned`, by role, and by nothing else** (LANG-79, law 7):
the collector's only refusals are `unpinned support0`, `unpinned support1` and `unpinned blocker`,
never a verdict's name (`support0 withdrawn`, `pruned`, …), so a client that derives its pins from
the refusal is told it forgot a pin, not that a fact is gone. -/
theorem holeCoverageOutcome_unpinned (c0 c1 cb : Bool) (e : Fault)
    (h : holeCoverageOutcome c0 c1 cb = .error e) :
    e = .refused "unpinned support0".toUTF8 ∨ e = .refused "unpinned support1".toUTF8 ∨
      e = .refused "unpinned blocker".toUTF8 := by
  cases c0 <;> cases c1 <;> cases cb <;> simp [holeCoverageOutcome, collect, Except.map] at h <;>
    (subst h; simp)

/-- The actual self-row key comparison proves presence, independent of whether
the observed value is absent or has a different version. -/
theorem holePointCovered_meaning (cell pin : ByteArray) (point : Option HolePoint)
    (lib : List Term) (env : Env) :
    BigStep lib ((holePointData point).toVal :: (holeSupportData cell pin).toVal :: env)
      (activityApply holePointCovered [.var 1, .var 0])
      (.ok (.bool (point.any fun p => decide (p.cell = cell)))) := by
  apply BigStep.app (BigStep.app .lam (.var rfl) .lam) (.var rfl)
  cases point with
  | none => exact .case (.var rfl) rfl .bool
  | some p =>
    apply BigStep.case (.var rfl) rfl
    have he : BigStep lib
        ((match holePointData (some p) with | .inj _ d => d | _ => .record []).toVal ::
          (holePointData (some p)).toVal :: (holeSupportData cell pin).toVal ::
          (holePointData (some p)).toVal :: (holeSupportData cell pin).toVal :: env)
        (.prim .deq (.get (.get (.var 0) "key") "cell") (.get (.var 2) "cell"))
        (.ok (.bool (decide (p.cell = cell)))) :=
      .prim (p := .deq) (x := .digest p.cell) (y := .digest cell) (.get (.get (.var rfl) (.field rfl (.var rfl))) (.field rfl (.var rfl)))
        (.get (.var rfl) (.field rfl (.var rfl))) (by simp [primEval])
    simpa only [Option.any_some, beq_iff_eq] using he


/-- Composition through the production wrapper. Observation premises are local
expression evaluations; no successful judgment or complete read set is assumed. -/
theorem holeCheckedJudge_application (V : Ty) (clause : Term)
    (lib : List Term) (env : Env) (state candidate rows : Val)
    (ts tc tr : Term)
    (hs : BigStep lib env ts (.ok state))
    (hc : BigStep lib env tc (.ok candidate))
    (hr : BigStep lib env tr (.ok rows))
    (c0 c1 cb allowed blocked : Bool) (p0 p1 : Nat)
    (hc0 : BigStep lib (holeCoverageEnv rows candidate state env)
      (holeCoverageObservation 0) (.ok (.bool c0)))
    (hc1 : BigStep lib (holeCoverageEnv rows candidate state env)
      (holeCoverageObservation 1) (.ok (.bool c1)))
    (hcb : BigStep lib (holeCoverageEnv rows candidate state env)
      (holeCoverageObservation 2) (.ok (.bool cb)))
    (ha : BigStep lib (holeJudgeEnv rows candidate state (holeCheckedEnv rows candidate state env))
      (holeObservation clause 0) (.ok (.bool allowed)))
    (hb : BigStep lib (holeJudgeEnv rows candidate state (holeCheckedEnv rows candidate state env))
      (holeObservation clause 1) (.ok (.bool blocked)))
    (h0 : BigStep lib (holeJudgeEnv rows candidate state (holeCheckedEnv rows candidate state env))
      (holeObservation clause 2) (.ok (.nat p0)))
    (h1 : BigStep lib (holeJudgeEnv rows candidate state (holeCheckedEnv rows candidate state env))
      (holeObservation clause 3) (.ok (.nat p1))) :
    BigStep lib env (activityApply (holeCheckedJudge V clause) [ts, tc, tr])
      (holeCheckedOutcome c0 c1 cb (holeVerdictLabel allowed blocked p0 p1)) := by
  apply BigStep.app (BigStep.app (BigStep.app .lam hs .lam) hc .lam) hr
  apply BigStep.app .lam .lam
  have hcov := holeCoverageCheck_application c0 c1 cb lib
    (holeCoverageEnv rows candidate state env) _ _ _ hc0 hc1 hcb
  cases c0 <;> cases c1 <;> cases cb
  all_goals first
    | exact BigStep.appA .lam hcov
    | apply BigStep.app .lam hcov
      exact holeJudge_application V clause lib (holeCheckedEnv rows candidate state env)
        state candidate rows _ _ _ (.var rfl) (.var rfl) (.var rfl)
        allowed blocked p0 p1 ha hb h0 h1

/-- The ordinary admission gate preserves collection refusals. Successful
execution is exactly complete observation plus a verified current judgment. -/
theorem holeCheckedAdmission_evaluated_iff (c0 c1 cb : Bool) (l : Label)
    (hl : l ∈ ["conflict", "pruned", "support0Dead", "support0Moved", "support0Withdrawn",
      "support1Dead", "support1Moved", "support1Withdrawn", "verified"])
    (lib : List Term) (env : Env) (t : Term)
    (ht : BigStep lib env t (holeCheckedOutcome c0 c1 cb l)) :
    (∃ v, BigStep lib env (.app holeVerdictCheck t) (.ok v)) ↔
      c0 = true ∧ c1 = true ∧ cb = true ∧ l = "verified" := by
  cases c0 <;> cases c1 <;> cases cb
  all_goals first
    | simpa using holeVerdictCheck_evaluated_iff l hl lib env t ht
    | constructor
      · rintro ⟨v, hv⟩
        have hbad : BigStep lib env (.app holeVerdictCheck t) (.error _) :=
          BigStep.appA .lam ht
        have he := bigStep_deterministic hbad hv
        cases he
      · simp

end Nanodregg.Lang.Std
