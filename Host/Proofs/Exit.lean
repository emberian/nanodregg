/-
# Host.Proofs.Exit — the exit table is a function of the status, and its classes do not overlap
-/
import Host.Exit

namespace Nanodregg.Host

namespace Status

theorem mem_all (s : Status) : s ∈ all := by cases s <;> decide

theorem all_nodup : all.Nodup := by decide

/-- Distinct statuses exit with distinct codes, so the code alone names the status. -/
theorem code_injective (a b : Status) (h : a.code = b.code) : a = b := by
  cases a <;> cases b <;> first | rfl | (simp [code] at h)

/-- Exit 0 means the stream ended and nothing else. -/
theorem code_zero_iff (s : Status) : s.code = 0 ↔ s = .eof := by
  cases s <;> decide

theorem code_zero_iff_done (s : Status) : s.code = 0 ↔ s.cls = .done := by
  cases s <;> decide

/-- No code is both restarted and prevented from restarting. -/
theorem restart_fatal_disjoint : ∀ c ∈ codesOf .restart, c ∉ codesOf .fatal := by decide

/-- A code is in the list of its own class, and in no other class's list. -/
theorem mem_codesOf_iff (s : Status) (k : ExitClass) : s.code ∈ codesOf k ↔ s.cls = k := by
  cases s <;> cases k <;> decide

/-- Codes stay clear of 1 (an uncaught exception) and 2 (misuse), and below nd-supervise's 64–66. -/
theorem code_reserved (s : Status) : s.code ≠ 1 ∧ s.code ≠ 2 ∧ s.code < 64 := by
  cases s <;> decide

end Status

/-- The exit status determines the refusal's printed name: one code, one name. -/
theorem StoreFault.status_iff_name {F : Type} (a b : StoreFault F) :
    a.status = b.status ↔ a.name = b.name := by
  rcases a with _ | _ | _ | _ | (_ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _) | (_ | _) | (_ | _ | _ | _ | _) | _ <;>
  rcases b with _ | _ | _ | _ | (_ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _) | (_ | _) | (_ | _ | _ | _ | _) | _ <;>
  simp [StoreFault.status, StoreFault.name, BaseFault.status, BaseFault.name, SealFault.status,
    SealFault.name]

/-- The status refines the `Exit`'s own name: equal statuses, equal names, so the stderr line
(`exit NAME`, from the status) and `Exit.name` cannot disagree about which exit it was. -/
theorem Exit.name_of_status (a b : Exit) (h : a.status = b.status) : a.name = b.name := by
  rcases a with _ | _ | _ | (_ | _ | _ | _ | _) | _ | _ | _ | _ | _ <;>
  rcases b with _ | _ | _ | (_ | _ | _ | _ | _) | _ | _ | _ | _ | _ <;>
  simp_all [Exit.status, SealFault.status, Exit.name]

end Nanodregg.Host
