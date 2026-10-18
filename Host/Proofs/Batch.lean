/-
# Host.Proofs.Batch — batches change latency, never meaning

* `run_append` — running `a ++ b` is running `a` then `b`: where the batch boundary falls does not
  change the World, the staged Turns or the replies.
* `staged_rooted` — for a transition `step` that every step the handler commits agrees with
  (`Commits`: the handler's World after a committed step is `step`'s), the staged (step, note)
  pairs are a `Kernel.Rooted` run of `step` from the World the batch started at to exactly the
  World the Host keeps, each note the one `note` gives the World right after its step (HOST-29).
  The follower folds the log; this is why its root is the Host's, and why every root the record
  states is the one the step reached. The Host's machine commits through `World.step`
  (`Host.Proofs.Serve.machine_commits`).
* `replies_size` — every request gets exactly one reply.
* `replies_conns` — and the replies' connections are the requests', in order: reply `i` is request
  `i`'s (the mux's in-flight count per connection relies on it).
-/
import Host.Batch
import Kernel.Proofs.RootedFold

namespace Nanodregg.Host

variable {W T R Q N : Type}

open Nanodregg.Kernel

/-- The handler commits only steps `step` takes to the very World it states. -/
def Machine.Commits (m : Machine W T Q N) (step : W → T → Except R W) : Prop :=
  ∀ w q s w' st p, m.handle w q = .commit s w' st p → step w s = .ok w'

theorem Machine.run_append (m : Machine W T Q N) (acc : W × Out (T × N)) (a b : List (Request Q)) :
    m.run acc (a ++ b) = m.run (m.run acc a) b := by
  simp [Machine.run, List.foldl_append]

/-- The step invariant: the staged pairs are a rooted run from the batch's starting World to the
World the step holds. -/
theorem Machine.step_rooted (m : Machine W T Q N) {step : W → T → Except R W} (hm : m.Commits step)
    (w₀ : W) (acc : W × Out (T × N)) (q : Request Q)
    (h : Rooted step m.note w₀ acc.2.staged.toList acc.1) :
    Rooted step m.note w₀ (m.step acc q).2.staged.toList (m.step acc q).1 := by
  obtain ⟨w, out⟩ := acc
  unfold Machine.step
  simp only
  split
  · exact h
  · exact h
  · rename_i t w' st p hq
    simp only [Array.toList_push]
    exact Rooted.snoc h (hm _ _ _ _ _ _ hq)

theorem Machine.run_rooted (m : Machine W T Q N) {step : W → T → Except R W} (hm : m.Commits step)
    (w₀ : W) (qs : List (Request Q)) :
    ∀ acc : W × Out (T × N), Rooted step m.note w₀ acc.2.staged.toList acc.1 →
      Rooted step m.note w₀ (m.run acc qs).2.staged.toList (m.run acc qs).1 := by
  induction qs with
  | nil => intro acc h; exact h
  | cons q qs ih =>
    intro acc h
    exact ih (m.step acc q) (m.step_rooted hm w₀ acc q h)

/-- What the Host logs means what the Host holds: every staged step is taken by `step` in order
from the batch's World, every staged note is the World's note right after its step, and the run
ends at the World the Host keeps. -/
theorem Machine.staged_rooted (m : Machine W T Q N) {step : W → T → Except R W} (hm : m.Commits step)
    (w : W) (qs : List (Request Q)) :
    Rooted step m.note w (m.admitBatch w qs).2.staged.toList (m.admitBatch w qs).1 :=
  m.run_rooted hm w qs (w, {}) rfl

/-- A step stages at most one pair. -/
theorem Machine.step_staged (m : Machine W T Q N) (acc : W × Out (T × N)) (q : Request Q) :
    (m.step acc q).2.staged.size ≤ acc.2.staged.size + 1 := by
  obtain ⟨w, out⟩ := acc
  unfold Machine.step
  simp only
  split <;> simp

/-- **A batch stages at most one pair per request** (HOST-41): with the loop's `drain` bound on the
requests (`limits.batchMax = recordTurnsMax`), the writer never stages more than one record holds. -/
theorem Machine.staged_size_le (m : Machine W T Q N) (w : W) (qs : List (Request Q)) :
    (m.admitBatch w qs).2.staged.size ≤ qs.length := by
  suffices ∀ acc : W × Out (T × N), (m.run acc qs).2.staged.size ≤ acc.2.staged.size + qs.length by
    simpa using this (w, {})
  induction qs with
  | nil => intro acc; simp [Machine.run]
  | cons q qs ih =>
    intro acc
    show (m.run (m.step acc q) qs).2.staged.size ≤ _
    have := ih (m.step acc q)
    have := m.step_staged acc q
    simp only [List.length_cons]
    omega

theorem Machine.step_replies (m : Machine W T Q N) (acc : W × Out (T × N)) (q : Request Q) :
    (m.step acc q).2.replies.size = acc.2.replies.size + 1 := by
  obtain ⟨w, out⟩ := acc
  unfold Machine.step
  simp only
  split
  · simp
  · simp
  · simp

theorem Machine.replies_size (m : Machine W T Q N) (w : W) (qs : List (Request Q)) :
    (m.admitBatch w qs).2.replies.size = qs.length := by
  suffices ∀ acc : W × Out (T × N), (m.run acc qs).2.replies.size = acc.2.replies.size + qs.length by
    simpa using this (w, {})
  induction qs with
  | nil => intro acc; simp [Machine.run]
  | cons q qs ih =>
    intro acc
    show (m.run (m.step acc q) qs).2.replies.size = _
    rw [ih, m.step_replies]; simp; omega

theorem Machine.step_conns (m : Machine W T Q N) (acc : W × Out (T × N)) (q : Request Q) :
    (m.step acc q).2.replies.toList.map (·.conn) = acc.2.replies.toList.map (·.conn) ++ [q.conn] := by
  obtain ⟨w, out⟩ := acc
  unfold Machine.step
  simp only
  split
  · simp
  · simp
  · simp

theorem Machine.replies_conns (m : Machine W T Q N) (w : W) (qs : List (Request Q)) :
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
