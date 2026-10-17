/-
# Host.Proofs.Batch — batches change latency, never meaning

* `run_append` — running `a ++ b` is running `a` then `b`: where the batch boundary falls does not
  change the World, the staged Turns or the replies.
* `staged_foldlM` — folding the staged Turns with `admit` from the World the batch started at
  reaches exactly the World the Host keeps. The follower folds the log; this is why its root is
  the Host's.
* `replies_size` — every request gets exactly one reply.
-/
import Host.Batch

namespace Nanodregg.Host

variable {W T R Q : Type}

theorem Machine.run_append (m : Machine W T R Q) (acc : W × Out T) (a b : List (Request Q)) :
    m.run acc (a ++ b) = m.run (m.run acc a) b := by
  simp [Machine.run, List.foldl_append]

/-- The step invariant: the staged Turns, folded from the batch's starting World, reach the World
the step holds. -/
theorem Machine.step_foldlM (m : Machine W T R Q) (w₀ : W) (acc : W × Out T) (q : Request Q)
    (h : acc.2.staged.toList.foldlM m.admit w₀ = .ok acc.1) :
    (m.step acc q).2.staged.toList.foldlM m.admit w₀ = .ok (m.step acc q).1 := by
  obtain ⟨w, out⟩ := acc
  unfold Machine.step
  simp only
  split
  · exact h
  · exact h
  · rename_i t receipt _
    split
    · rename_i w' hw
      simp only [Array.toList_push, List.foldlM_append, List.foldlM_cons, List.foldlM_nil]
      rw [h]
      simp only [bind, Except.bind, hw]
      rfl
    · exact h

theorem Machine.run_foldlM (m : Machine W T R Q) (w₀ : W) (qs : List (Request Q)) :
    ∀ acc : W × Out T, acc.2.staged.toList.foldlM m.admit w₀ = .ok acc.1 →
      (m.run acc qs).2.staged.toList.foldlM m.admit w₀ = .ok (m.run acc qs).1 := by
  induction qs with
  | nil => intro acc h; exact h
  | cons q qs ih =>
    intro acc h
    exact ih (m.step acc q) (m.step_foldlM w₀ acc q h)

/-- What the Host logs means what the Host holds. -/
theorem Machine.staged_foldlM (m : Machine W T R Q) (w : W) (qs : List (Request Q)) :
    (m.admitBatch w qs).2.staged.toList.foldlM m.admit w = .ok (m.admitBatch w qs).1 :=
  m.run_foldlM w qs (w, {}) rfl

theorem Machine.step_replies (m : Machine W T R Q) (acc : W × Out T) (q : Request Q) :
    (m.step acc q).2.replies.size = acc.2.replies.size + 1 := by
  obtain ⟨w, out⟩ := acc
  unfold Machine.step
  simp only
  split
  · simp
  · simp
  · split
    · simp
    · simp

theorem Machine.replies_size (m : Machine W T R Q) (w : W) (qs : List (Request Q)) :
    (m.admitBatch w qs).2.replies.size = qs.length := by
  suffices ∀ acc : W × Out T, (m.run acc qs).2.replies.size = acc.2.replies.size + qs.length by
    simpa using this (w, {})
  induction qs with
  | nil => intro acc; simp [Machine.run]
  | cons q qs ih =>
    intro acc
    show (m.run (m.step acc q) qs).2.replies.size = _
    rw [ih, m.step_replies]; simp; omega

end Nanodregg.Host
