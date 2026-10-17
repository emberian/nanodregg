/-
# Host.Proofs.Batch — batches change latency, never meaning

* `run_append` — running `a ++ b` is running `a` then `b`: where the batch boundary falls does not
  change the World, the staged Turns or the replies.
* `staged_rooted` — the staged (Turn, note) pairs are a `Kernel.Rooted` run of `admit` from the
  World the batch started at to exactly the World the Host keeps, each note the one `note` gives
  the World right after its Turn (HOST-29). The follower folds the log; this is why its root is
  the Host's, and why every root the record states is the one admission reached.
* `replies_size` — every request gets exactly one reply.
* `replies_conns` — and the replies' connections are the requests', in order: reply `i` is request
  `i`'s (the mux's in-flight count per connection relies on it).
-/
import Host.Batch
import Kernel.Proofs.RootedFold

namespace Nanodregg.Host

variable {W T R Q N : Type}

open Nanodregg.Kernel

theorem Machine.run_append (m : Machine W T R Q N) (acc : W × Out (T × N)) (a b : List (Request Q)) :
    m.run acc (a ++ b) = m.run (m.run acc a) b := by
  simp [Machine.run, List.foldl_append]

/-- The step invariant: the staged pairs are a rooted run from the batch's starting World to the
World the step holds. -/
theorem Machine.step_rooted (m : Machine W T R Q N) (w₀ : W) (acc : W × Out (T × N)) (q : Request Q)
    (h : Rooted m.admit m.note w₀ acc.2.staged.toList acc.1) :
    Rooted m.admit m.note w₀ (m.step acc q).2.staged.toList (m.step acc q).1 := by
  obtain ⟨w, out⟩ := acc
  unfold Machine.step
  simp only
  split
  · exact h
  · exact h
  · rename_i t receipt _
    split
    · rename_i w' hw
      simp only [Array.toList_push]
      exact Rooted.snoc h hw
    · exact h

theorem Machine.run_rooted (m : Machine W T R Q N) (w₀ : W) (qs : List (Request Q)) :
    ∀ acc : W × Out (T × N), Rooted m.admit m.note w₀ acc.2.staged.toList acc.1 →
      Rooted m.admit m.note w₀ (m.run acc qs).2.staged.toList (m.run acc qs).1 := by
  induction qs with
  | nil => intro acc h; exact h
  | cons q qs ih =>
    intro acc h
    exact ih (m.step acc q) (m.step_rooted w₀ acc q h)

/-- What the Host logs means what the Host holds: every staged Turn admits in order from the
batch's World, every staged note is the World's note right after its Turn, and the run ends at the
World the Host keeps. -/
theorem Machine.staged_rooted (m : Machine W T R Q N) (w : W) (qs : List (Request Q)) :
    Rooted m.admit m.note w (m.admitBatch w qs).2.staged.toList (m.admitBatch w qs).1 :=
  m.run_rooted w qs (w, {}) rfl

theorem Machine.step_replies (m : Machine W T R Q N) (acc : W × Out (T × N)) (q : Request Q) :
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

theorem Machine.replies_size (m : Machine W T R Q N) (w : W) (qs : List (Request Q)) :
    (m.admitBatch w qs).2.replies.size = qs.length := by
  suffices ∀ acc : W × Out (T × N), (m.run acc qs).2.replies.size = acc.2.replies.size + qs.length by
    simpa using this (w, {})
  induction qs with
  | nil => intro acc; simp [Machine.run]
  | cons q qs ih =>
    intro acc
    show (m.run (m.step acc q) qs).2.replies.size = _
    rw [ih, m.step_replies]; simp; omega

theorem Machine.step_conns (m : Machine W T R Q N) (acc : W × Out (T × N)) (q : Request Q) :
    (m.step acc q).2.replies.toList.map (·.conn) = acc.2.replies.toList.map (·.conn) ++ [q.conn] := by
  obtain ⟨w, out⟩ := acc
  unfold Machine.step
  simp only
  split
  · simp
  · simp
  · split
    · simp
    · simp

theorem Machine.replies_conns (m : Machine W T R Q N) (w : W) (qs : List (Request Q)) :
    (m.admitBatch w qs).2.replies.toList.map (·.conn) = qs.map (·.conn) := by
  suffices ∀ acc : W × Out (T × N),
      (m.run acc qs).2.replies.toList.map (·.conn) = acc.2.replies.toList.map (·.conn) ++ qs.map (·.conn) by
    simpa using this (w, {})
  induction qs with
  | nil => intro acc; simp [Machine.run]
  | cons q qs ih =>
    intro acc
    show (m.run (m.step acc q) qs).2.replies.toList.map (·.conn) = _
    rw [ih, m.step_conns]; simp

end Nanodregg.Host
