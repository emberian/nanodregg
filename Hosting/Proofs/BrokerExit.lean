/-
# Hosting.Proofs.BrokerExit — keybroker's code space is one table, apart from the Host's
-/
import Hosting.BrokerExit
import Protocol.Exit

namespace Nanodregg.Hosting.Proofs.BrokerExit

open Nanodregg.Hosting
open Nanodregg.Host (ExitClass Status)
open Nanodregg.Protocol (SupervisorExit)

theorem decider_mem_all (e : DeciderExit) : e ∈ DeciderExit.all := by cases e <;> decide
theorem keybroker_mem_all (e : KeybrokerExit) : e ∈ KeybrokerExit.all := by cases e <;> decide

/-- One code per end, in each table and across the two (the unit sees both). -/
theorem codes_nodup :
    (DeciderExit.all.map DeciderExit.code ++ KeybrokerExit.all.map KeybrokerExit.code).Nodup := by decide

/-- Neither table reuses a Host or nd-supervise code, over the lists the emitter and `Ops.Units`
read; 0 is the decider's normal end alone. -/
theorem codes_disjoint :
    (∀ a ∈ KeybrokerExit.all, ∀ s ∈ Status.all, a.code ≠ s.code) ∧
    (∀ a ∈ KeybrokerExit.all, ∀ s ∈ SupervisorExit.all, a.code ≠ s.code) ∧
    (∀ a ∈ DeciderExit.all, ∀ s ∈ Status.all, a.code ≠ s.code ∨ a = .keybrokerGone) ∧
    (∀ a ∈ DeciderExit.all, ∀ s ∈ SupervisorExit.all, a.code ≠ s.code) := by decide

/-- No code is 1 or 2, none of keybroker's is 101 (the exit of a Rust panic), every code fits an exit
status, and 0 is exactly `done`. -/
theorem codes_reserved :
    (∀ a ∈ KeybrokerExit.all, a.code ≠ 1 ∧ a.code ≠ 2 ∧ a.code ≠ 101 ∧ 0 < a.code ∧ a.code < 256) ∧
    (∀ a ∈ DeciderExit.all, a.code ≠ 1 ∧ a.code ≠ 2 ∧ a.code < 256 ∧ (a.code = 0 ↔ a.cls = .done)) := by
  decide

/-- A code is restarted or prevented, never both: the unit's two lists are disjoint. -/
theorem restart_fatal_disjoint :
    ∀ c ∈ DeciderExit.codesOf .restart ++ KeybrokerExit.codesOf .restart,
      c ∉ DeciderExit.codesOf .fatal ++ KeybrokerExit.codesOf .fatal := by decide

/-- Every custody and anchor refusal stops the unit; only a signalled decider is restarted. -/
theorem keybroker_fatal_iff (e : KeybrokerExit) : e.cls = .fatal ↔ e ≠ .deciderSignaled := by
  cases e <;> decide

/-- The decider restarts only on its own lifetime and on falling behind the writer; a Store refusal,
an IO error and every defect stop the unit. -/
theorem decider_restart_iff (e : DeciderExit) : e.cls = .restart ↔ e = .lifetime ∨ e = .behind := by
  cases e <;> decide

theorem members_mem_all (e : MembersExit) : e ∈ MembersExit.all := by cases e <;> decide

/-- nd-members' unit sees its own table and its decider's: one code per end across the two, and
none of keybroker's (the two broker-family tables never share a code). -/
theorem members_codes_nodup :
    (DeciderExit.all.map DeciderExit.code ++ MembersExit.all.map MembersExit.code ++
      KeybrokerExit.all.map KeybrokerExit.code).Nodup := by decide

/-- No code of nd-members is a Host, nd-supervise or decider code (over the lists the emitter and
`Ops.Units` read). -/
theorem members_codes_disjoint :
    (∀ a ∈ MembersExit.all, ∀ s ∈ Status.all, a.code ≠ s.code) ∧
    (∀ a ∈ MembersExit.all, ∀ s ∈ SupervisorExit.all, a.code ≠ s.code) ∧
    (∀ a ∈ MembersExit.all, ∀ d ∈ DeciderExit.all, a.code ≠ d.code) := by decide

/-- None is 0, 1, 2 or 101 (a Rust panic), and every code fits an exit status. -/
theorem members_codes_reserved :
    ∀ a ∈ MembersExit.all, a.code ≠ 1 ∧ a.code ≠ 2 ∧ a.code ≠ 101 ∧ 0 < a.code ∧ a.code < 256 := by
  decide

/-- The unit's restart and prevent lists are disjoint. -/
theorem members_restart_fatal_disjoint :
    ∀ c ∈ DeciderExit.codesOf .restart ++ MembersExit.codesOf .restart,
      c ∉ DeciderExit.codesOf .fatal ++ MembersExit.codesOf .fatal := by decide

/-- Only a signalled decider is restarted; every root, limit and mechanism end stops the unit. -/
theorem members_fatal_iff (e : MembersExit) : e.cls = .fatal ↔ e ≠ .deciderSignaled := by
  cases e <;> decide

/-- The World past the resident bound ends nd-members with the decider's own code for that fact. -/
theorem members_past_bound_code : DeciderExit.residentsPastBound.code = 7 ∧
    DeciderExit.residentsPastBound.cls = .fatal := by decide

end Nanodregg.Hosting.Proofs.BrokerExit
