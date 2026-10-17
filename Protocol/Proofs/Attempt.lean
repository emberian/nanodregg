/-
# Protocol.Proofs.Attempt — the attempt store never sends a frozen call blind

The three properties CLIENT-3's double-submit class needs, about `Attempt.next`, plus that the
emitted table is the function (so the client reading the table reads the rule).
-/
import Protocol.Attempt

namespace Nanodregg.Protocol.Attempt

/-- A submit is decided only for a call never sent, or after a lookup said `absent` with a send
left: never after a submit whose outcome is unknown. -/
theorem next_submit {b : Bool} {l : Option (Request × Seen)} (h : next b l = .submit) :
    l = none ∨ (l = some (.lookup, .absent) ∧ b = true) := by
  match l, b with
  | none, _ => exact .inl rfl
  | some (.lookup, .absent), true => exact .inr ⟨rfl, rfl⟩
  | some (.lookup, .absent), false => simp [next] at h
  | some (.submit, s), _ => cases s <;> simp [next] at h
  | some (.lookup, .committed), _ | some (.lookup, .refused), _ | some (.lookup, .unknown), _
  | some (.lookup, .lost), _ => simp [next] at h

/-- After a submit whose reply was lost or `uncertain`, the next request is a lookup. -/
theorem next_after_unknown (b : Bool) (s : Seen) (hs : s = .unknown ∨ s = .lost) :
    next b (some (.submit, s)) = .lookup := by
  rcases hs with rfl | rfl <;> rfl

/-- A reply that says committed ends the attempt as committed, whichever request it answered. -/
theorem next_committed (b : Bool) (r : Request) : next b (some (r, .committed)) = .committed := by
  cases r <;> rfl

/-- A lookup is only ever decided right after a submit: a lookup that settles nothing ends the
run, so one run's requests are at most two per send. -/
theorem next_after_lookup (b : Bool) (s : Seen) : next b (some (.lookup, s)) ≠ .lookup := by
  cases s <;> cases b <;> simp [next]

/-- With no send left, no submit is ever decided. -/
theorem next_no_send_left (l : Option (Request × Seen)) (h : l ≠ none) : next false l ≠ .submit := by
  intro hn
  rcases next_submit hn with h' | ⟨_, h'⟩
  · exact h h'
  · cases h'

/-- The emitted table covers every input exactly once and agrees with `next`. -/
theorem table_complete (b : Bool) (l : Option (Request × Seen)) : ((b, l), next b l) ∈ table := by
  cases b <;> rcases l with _ | ⟨r, s⟩ <;> (try cases r) <;> (try cases s) <;> decide

theorem inputs_nodup : inputs.Nodup := by decide

theorem Action.name_injective (a b : Action) (h : a.name = b.name) : a = b := by
  cases a <;> cases b <;> simp_all [Action.name]

end Nanodregg.Protocol.Attempt
