/-
# Hosting.Proofs.LaunchExit — grain-launch's code space is one table, apart from every other
-/
import Hosting.LaunchExit
import Hosting.BrokerExit
import Protocol.Exit

namespace Nanodregg.Hosting.Proofs.LaunchExit

open Nanodregg.Hosting
open Nanodregg.Host (ExitClass Status)
open Nanodregg.Protocol (SupervisorExit)

theorem controller_mem_all (e : ControllerExit) : e ∈ ControllerExit.all := by cases e <;> decide
theorem launch_mem_all (e : LaunchExit) : e ∈ LaunchExit.all := by cases e <;> decide

/-- One code per end, across both tables (the grain-launch unit sees both). -/
theorem codes_nodup :
    (ControllerExit.all.map ControllerExit.code ++ LaunchExit.all.map LaunchExit.code).Nodup := by decide

/-- No code but the controller's normal end is a Host, nd-supervise, decider or keybroker code, over
the lists the emitters and `Ops.Units` read. -/
theorem codes_disjoint :
    (∀ a ∈ LaunchExit.all, ∀ s ∈ Status.all, a.code ≠ s.code) ∧
    (∀ a ∈ LaunchExit.all, ∀ s ∈ SupervisorExit.all, a.code ≠ s.code) ∧
    (∀ a ∈ LaunchExit.all, ∀ d ∈ DeciderExit.all, a.code ≠ d.code) ∧
    (∀ a ∈ LaunchExit.all, ∀ k ∈ KeybrokerExit.all, a.code ≠ k.code) ∧
    (∀ a ∈ ControllerExit.all, a = .launcherGone ∨
      ((∀ s ∈ Status.all, a.code ≠ s.code) ∧ (∀ s ∈ SupervisorExit.all, a.code ≠ s.code) ∧
       (∀ d ∈ DeciderExit.all, a.code ≠ d.code) ∧ (∀ k ∈ KeybrokerExit.all, a.code ≠ k.code))) := by
  decide

/-- No code is 1, 2 or 101 (an uncaught exception, a shell's misuse, a Rust panic), every code is
below 128 (a shell reads 128 or more as a signal), and 0 is exactly `done`. -/
theorem codes_reserved :
    (∀ a ∈ LaunchExit.all, a.code ≠ 1 ∧ a.code ≠ 2 ∧ a.code ≠ 101 ∧ 0 < a.code ∧ a.code < 128) ∧
    (∀ a ∈ ControllerExit.all, a.code ≠ 1 ∧ a.code ≠ 2 ∧ a.code ≠ 101 ∧ a.code < 128 ∧
      (a.code = 0 ↔ a.cls = .done)) := by
  decide

/-- A code is restarted or prevented, never both. -/
theorem restart_fatal_disjoint :
    ∀ c ∈ ControllerExit.codesOf .restart ++ LaunchExit.codesOf .restart,
      c ∉ ControllerExit.codesOf .fatal ++ LaunchExit.codesOf .fatal := by decide

/-- grain-launch restarts only when its controller is gone (the report pipe, a signal) or on its own
lifetime; every defect, the roots, the sandbox's refusal and a lost `wait` stop the unit. -/
theorem launch_restart_iff (e : LaunchExit) :
    e.cls = .restart ↔ e = .reportPipe ∨ e = .lifetime ∨ e = .controllerSignaled := by
  cases e <;> decide

/-- The controller restarts only on its lifetime. -/
theorem controller_restart_iff (e : ControllerExit) : e.cls = .restart ↔ e = .lifetime := by
  cases e <;> decide

end Nanodregg.Hosting.Proofs.LaunchExit
