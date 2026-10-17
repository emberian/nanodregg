/-
# Protocol.Proofs.Exit — the supervisor's codes are its own, one per exit, and fit an exit byte
-/
import Protocol.Exit
import Host.Proofs.Exit

namespace Nanodregg.Protocol.SupervisorExit

theorem mem_all (s : SupervisorExit) : s ∈ all := by cases s <;> decide

/-- Distinct supervisor exits have distinct codes, so the code alone names the exit. -/
theorem code_injective (a b : SupervisorExit) (h : a.code = b.code) : a = b := by
  cases a <;> cases b <;> first | rfl | (simp [code] at h)

/-- No supervisor code is a Host code: a passed-through child status and the supervisor's own
never read alike. -/
theorem code_disjoint_host (s : SupervisorExit) (h : Host.Status) : s.code ≠ h.code := by
  cases s <;> cases h <;> decide

/-- Every code is a process exit status (one byte) and none is 0 (success). -/
theorem code_pos_lt (s : SupervisorExit) : 0 < s.code ∧ s.code < 256 := by cases s <;> decide

/-- No code is both restarted and prevented from restarting. -/
theorem restart_fatal_disjoint : ∀ c ∈ codesOf .restart, c ∉ codesOf .fatal := by decide

end Nanodregg.Protocol.SupervisorExit

namespace Nanodregg.Protocol.CommandExit

theorem mem_all (c : CommandExit) : c ∈ all := by cases c <;> decide

/-- Distinct command ends have distinct codes. -/
theorem code_injective (a b : CommandExit) (h : a.code = b.code) : a = b := by
  cases a <;> cases b <;> first | rfl | (simp [code] at h)

/-- `ofCode?` reads back every code. -/
theorem ofCode_code (c : CommandExit) : ofCode? c.code = some c := by cases c <;> decide

/-- No command end but `ok` shares a code with a Host exit (whose 0 is its own `done`). -/
theorem code_disjoint_host (c : CommandExit) (hc : c ≠ .ok) (h : Host.Status) : c.code ≠ h.code := by
  cases c <;> cases h <;> first | exact absurd rfl hc | decide

/-- No command end shares a code with the supervisor's own. -/
theorem code_disjoint_supervisor (c : CommandExit) (s : SupervisorExit) : c.code ≠ s.code := by
  cases c <;> cases s <;> decide

/-- Every code fits an exit byte, and only `ok` is 0. -/
theorem code_lt (c : CommandExit) : c.code < 256 := by cases c <;> decide

theorem code_zero_iff (c : CommandExit) : c.code = 0 ↔ c = .ok := by cases c <;> decide

/-- No code is both restarted and prevented from restarting. -/
theorem restart_fatal_disjoint : ∀ c ∈ codesOf .restart, c ∉ codesOf .fatal := by decide

end Nanodregg.Protocol.CommandExit
