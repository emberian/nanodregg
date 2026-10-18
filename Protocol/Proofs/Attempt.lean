/-
# Protocol.Proofs.Attempt — the attempt store never sends a frozen call blind, and only follow settles

The properties CLIENT-3's double-submit class and PROTOCOL-46 need, about `Attempt.next`, plus that
the emitted table is the function (so the client reading the table reads the rule).
-/
import Protocol.Attempt

namespace Nanodregg.Protocol.Attempt

/-- A submit is decided only for a call never sent, or after the member's OWN follow said `open`
to a probe with a send left (KERNEL-54, PROTOCOL-15's condition 3): never after a submit whose
outcome is unknown, and never on the Host's `absent` alone. -/
theorem next_submit {b : Bool} {l : Option (Request × Seen)} (h : next b l = .submit) :
    l = none ∨ (l = some (.probe, .open) ∧ b = true) := by
  rcases l with _ | ⟨r, s⟩
  · exact .inl rfl
  · cases r <;> cases s <;> cases b <;> simp [next] at h ⊢

/-- After a submit whose reply was lost or `uncertain`, the next request is a lookup. -/
theorem next_after_unknown (b : Bool) (s : Seen) (hs : s = .unknown ∨ s = .lost) :
    next b (some (.submit, s)) = .lookup := by
  rcases hs with rfl | rfl <;> rfl

/-- **The Host never settles an attempt** (PROTOCOL-46): an attempt ends `committed` or `refused`
only on a reply to `confirm` or `probe`, the member's own follow answering from its own World. -/
theorem next_final {b : Bool} {l : Option (Request × Seen)}
    (h : next b l = .committed ∨ next b l = .refused) :
    ∃ r s, l = some (r, s) ∧ (r = .confirm ∨ r = .probe) := by
  rcases l with _ | ⟨r, s⟩
  · simp [next] at h
  · refine ⟨r, s, rfl, ?_⟩
    cases r <;> cases s <;> cases b <;> simp [next] at h ⊢

/-- A Host reply saying committed or refused is confirmed by follow, whichever request it answered. -/
theorem next_host_final_confirms (b : Bool) (r : Request) (s : Seen)
    (hr : r = .submit ∨ r = .lookup) (hs : s = .committed ∨ s = .refused) :
    next b (some (r, s)) = .confirm := by
  rcases hr with rfl | rfl <;> rcases hs with rfl | rfl <;> rfl

/-- **An absent lookup is confirmed with follow before any resend** (KERNEL-54, PROTOCOL-15's
condition 3): a lookup's `absent` asks follow (`probe`) whatever the sends left; `absent` never ends
an attempt and never resends on the Host's word. -/
theorem next_absent_probes (b : Bool) : next b (some (.lookup, .absent)) = .probe := by cases b <;> rfl

/-- **No end of an attempt says the call did not land**: every final action is follow's word on a
confirm or probe (`next_final`), and the ends a run may stop on without it (declined, open,
contradicted, uncertain, badReply) all leave the attempt open on disk. -/
theorem next_ends_open {b : Bool} {l : Option (Request × Seen)}
    (h : next b l ≠ .submit ∧ next b l ≠ .lookup ∧ next b l ≠ .confirm ∧ next b l ≠ .probe) :
    next b l = .committed ∨ next b l = .refused ∨ next b l = .declined ∨ next b l = .open ∨
      next b l = .contradicted ∨ next b l = .uncertain ∨ next b l = .badReply := by
  generalize next b l = a at h ⊢
  cases a <;> simp_all

/-- Follow's `open` to a probe sends the same bytes again while a send is left, else ends the run
open; to a confirm (the Host said final), contradicted. -/
theorem next_open (b : Bool) :
    next b (some (.probe, .open)) = (if b then .submit else .open) ∧
      next b (some (.confirm, .open)) = .contradicted := by
  cases b <;> exact ⟨rfl, rfl⟩

/-- A lookup is only ever decided right after a submit: a lookup that settles nothing ends the
run, so one run's requests are at most two per send, plus one confirm or probe. -/
theorem next_after_lookup (b : Bool) (s : Seen) : next b (some (.lookup, s)) ≠ .lookup := by
  cases s <;> cases b <;> simp [next]

/-- After follow's answer the only request to the writer is the resend a probe's `open` allows:
a confirm or a probe never leads to a lookup, a confirm or a probe, and to a submit only from
`(probe, open)` with a send left (`next_submit`). -/
theorem next_after_follow (b : Bool) (r : Request) (s : Seen) (hr : r = .confirm ∨ r = .probe) :
    (next b (some (r, s)) = .submit → r = .probe ∧ s = .open ∧ b = true) ∧
      next b (some (r, s)) ≠ .lookup ∧ next b (some (r, s)) ≠ .confirm ∧
      next b (some (r, s)) ≠ .probe := by
  rcases hr with rfl | rfl <;> cases s <;> cases b <;> simp [next]

/-- With no send left, no submit is ever decided. -/
theorem next_no_send_left (l : Option (Request × Seen)) (h : l ≠ none) : next false l ≠ .submit := by
  intro hn
  rcases next_submit hn with h' | ⟨_, h'⟩
  · exact h h'
  · cases h'

/-- The emitted table covers every input exactly once and agrees with `next`. -/
theorem table_complete (b : Bool) (l : Option (Request × Seen)) : ((b, l), next b l) ∈ table := by
  cases b <;> rcases l with _ | ⟨r, s⟩ <;> (try cases r) <;> (try cases s) <;> decide

/-- **A declined submit ends the run `declined`**, never `refused` (so the client writes no
settlement: its plant is client/tests/attempt.rs `declined_leaves_the_attempt_open_and_the_next_run_looks_up`). -/
theorem next_declined (b : Bool) : next b (some (.submit, .declined)) = .declined := rfl

/-- A lookup is never answered `declined` (only a submit is judged): such a reply is `badReply`. -/
theorem next_lookup_declined (b : Bool) : next b (some (.lookup, .declined)) = .badReply := rfl

/-- `settleSeen` reads exactly the settle words, and none of them is a Host-only status. -/
theorem settleSeen_words (w : String) : (settleSeen w).isSome = true ↔ w ∈ settleWords := by
  unfold settleSeen settleWords
  split <;> simp_all

/-- The emitted `Action` enum is every action (a new one cannot be left out of the client's `match`). -/
theorem Action.mem_all (a : Action) : a ∈ Action.all := by cases a <;> decide

theorem inputs_nodup : inputs.Nodup := by decide

theorem Action.name_injective (a b : Action) (h : a.name = b.name) : a = b := by
  cases a <;> cases b <;> simp_all [Action.name]

theorem Action.code_injective (a b : Action) (h : a.code = b.code) : a = b := by
  cases a <;> cases b <;> first | rfl | (simp [Action.code] at h)

theorem Seen.name_injective (a b : Seen) (h : a.name = b.name) : a = b := by
  cases a <;> cases b <;> simp_all [Seen.name]

end Nanodregg.Protocol.Attempt
