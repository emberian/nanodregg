/-
# Lang.Proofs.Run — the tick budget: exact, monotone, and the outcome does not depend on it

`run` reports the steps it took (`used`). A run that ended for any reason other than running out
of ticks ends the same way, with the same `used`, under every larger budget (`run_stable`); so two
executors that both finish agree on the value and the cost, whatever budgets they were given
(`run_agree`) — the statement re-execution checking needs. `used` is the exact price: the run
fits in `used` ticks (`run_exact`) and not in one fewer (`run_minimal`).
-/
import Lang.Eval

namespace Nanodregg.Lang

/-- An outcome that is not "out of ticks". -/
def Outcome.Final : Outcome → Prop
  | .value _ _ => True
  | .fault f _ => f ≠ .ticks

private def Outcome.shift (u : Nat) : Outcome → Outcome
  | .value v k => .value v (k + u)
  | .fault f k => .fault f (k + u)

variable {lib : List Term} {cap : Nat}

theorem run_shift : ∀ (n u : Nat) (s : State),
    run lib cap n u s = (run lib cap n 0 s).shift u
  | 0, u, s => by simp [run, Outcome.shift]
  | n + 1, u, s => by
    simp only [run]
    split
    · simp [Outcome.shift, Nat.add_comm]
    · simp [Outcome.shift, Nat.add_comm]
    · split
      · simp [Outcome.shift, Nat.add_comm]
      · rw [run_shift n (u + 1), run_shift n 1]
        cases run lib cap n 0 _ <;> simp [Outcome.shift] <;> omega

theorem run_used_le : ∀ (n : Nat) (s : State), (run lib cap n 0 s).used ≤ n
  | 0, s => by simp [run, Outcome.used]
  | n + 1, s => by
    simp only [run]
    split
    · simp [Outcome.used]
    · simp [Outcome.used]
    · split
      · simp [Outcome.used]
      · rw [run_shift n 1]
        have := run_used_le n ‹_›
        revert this
        cases run lib cap n 0 _ <;> simp [Outcome.shift, Outcome.used] <;> omega

/-- One step of a run, with the rest shifted by that step. -/
private def after (lib : List Term) (cap : Nat) (rest : State → Outcome) (s : State) : Outcome :=
  match step lib s with
  | .halt v => .value v 1
  | .fault f => .fault f 1
  | .next s' => if cap < s'.depth then .fault .stack 1 else (rest s').shift 1

theorem run_succ (n : Nat) (s : State) :
    run lib cap (n + 1) 0 s = after lib cap (run lib cap n 0) s := by
  unfold after
  cases hs : step lib s with
  | halt v => simp [run, hs]
  | fault f => simp [run, hs]
  | next s' =>
    by_cases h : cap < s'.depth
    · simp [run, hs, h]
    · simp only [run, hs, h, if_false]; exact run_shift n 1 s'

theorem Outcome.shift_final {o : Outcome} : (o.shift 1).Final ↔ o.Final := by
  cases o <;> simp [Outcome.shift, Outcome.Final]

theorem Outcome.shift_used {o : Outcome} : (o.shift 1).used = o.used + 1 := by
  cases o <;> simp [Outcome.shift, Outcome.used]

/-- One more tick changes nothing about a run that ended for a reason other than ticks. -/
theorem run_succ_final : ∀ (n : Nat) (s : State), (run lib cap n 0 s).Final →
    run lib cap (n + 1) 0 s = run lib cap n 0 s
  | 0, s, h => by simp [run, Outcome.Final] at h
  | n + 1, s, h => by
    rw [run_succ (n + 1), run_succ n]
    rw [run_succ n] at h
    unfold after at h ⊢
    split
    · rfl
    · rfl
    · rename_i s' hstep
      rw [hstep] at h
      split
      · rfl
      · rename_i hcap
        simp only [hcap, if_false, Outcome.shift_final] at h
        rw [run_succ_final n s' h]

theorem run_stable {n m : Nat} {s : State} (h : (run lib cap n 0 s).Final) (hnm : n ≤ m) :
    run lib cap m 0 s = run lib cap n 0 s := by
  induction m with
  | zero =>
    have : n = 0 := by omega
    subst this; rfl
  | succ m ih =>
    rcases Nat.lt_or_ge n (m + 1) with hlt | hge
    · have ih' := ih (by omega)
      rw [run_succ_final m s (by rw [ih']; exact h), ih']
    · have : n = m + 1 := by omega
      subst this; rfl

/-- Two executors that both reach a final outcome agree on it, value and cost, whatever budgets
they were given. -/
theorem run_agree {n m : Nat} {s : State}
    (hn : (run lib cap n 0 s).Final) (hm : (run lib cap m 0 s).Final) :
    run lib cap n 0 s = run lib cap m 0 s := by
  rcases Nat.le_total n m with h | h
  · exact (run_stable hn h).symm
  · exact run_stable hm h

theorem final_used_pos : ∀ (n : Nat) (s : State), (run lib cap n 0 s).Final →
    1 ≤ (run lib cap n 0 s).used
  | 0, s, h => by simp [run, Outcome.Final] at h
  | n + 1, s, _ => by
    rw [run_succ n]; unfold after
    split
    · simp [Outcome.used]
    · simp [Outcome.used]
    · split
      · simp [Outcome.used]
      · rw [Outcome.shift_used]; omega

/-- The run fits in exactly the ticks it reports. -/
theorem run_exact : ∀ (n : Nat) (s : State), (run lib cap n 0 s).Final →
    run lib cap (run lib cap n 0 s).used 0 s = run lib cap n 0 s
  | 0, s, h => by simp [run, Outcome.Final] at h
  | n + 1, s, h => by
    rw [run_succ n] at h ⊢
    unfold after at h ⊢
    split
    · simp [Outcome.used, run_succ, after, *]
    · simp [Outcome.used, run_succ, after, *]
    · rename_i s' hstep
      rw [hstep] at h
      split
      · simp [Outcome.used, run_succ, after, *]
      · rename_i hcap
        simp only [hcap, if_false, Outcome.shift_final] at h
        rw [Outcome.shift_used, run_succ, after, hstep]
        simp only [hcap, if_false]
        rw [run_exact n s' h]

/-- One tick fewer than reported is not enough: `used` is the minimal budget. -/
theorem run_minimal : ∀ (n : Nat) (s : State), (run lib cap n 0 s).Final →
    run lib cap ((run lib cap n 0 s).used - 1) 0 s =
      .fault .ticks ((run lib cap n 0 s).used - 1)
  | 0, s, h => by simp [run, Outcome.Final] at h
  | n + 1, s, h => by
    rw [run_succ n] at h ⊢
    unfold after at h ⊢
    split
    · simp [Outcome.used, run]
    · simp [Outcome.used, run]
    · rename_i s' hstep
      rw [hstep] at h
      split
      · simp [Outcome.used, run]
      · rename_i hcap
        simp only [hcap, if_false, Outcome.shift_final] at h
        have hpos := final_used_pos n s' h
        have e := run_minimal n s' h
        rw [Outcome.shift_used, Nat.add_sub_cancel]
        obtain ⟨j, hj⟩ : ∃ j, (run lib cap n 0 s').used = j + 1 :=
          ⟨(run lib cap n 0 s').used - 1, by omega⟩
        rw [hj] at e ⊢
        rw [run_succ, after, hstep]
        simp only [hcap, if_false, Nat.add_sub_cancel] at e ⊢
        rw [e]; simp [Outcome.shift]

end Nanodregg.Lang
