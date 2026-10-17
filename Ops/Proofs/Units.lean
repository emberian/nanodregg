/-
# Ops.Proofs.Units — a rendered unit is confined, and restarts exactly the restart classes of
both exit tables (the child's `Host.Status`, nd-supervise's own `SupervisorExit`)
-/
import Ops.Units
import Host.Proofs.Exit
import Protocol.Proofs.Exit

namespace Nanodregg.Ops.Units

open Nanodregg.Host
open Nanodregg.Protocol (SupervisorExit)

/-- A unit exists only for a node that hides something. -/
theorem ofNode_hidden (n : Node) (u : Service) (h : Service.ofNode n = .ok u) : n.hide ≠ [] := by
  intro he
  simp [Service.ofNode, he] at h

/-- A rendered unit's command line starts with nd-supervise: the host is never run unconfined. -/
theorem ofNode_supervised (n : Node) (u : Service) (h : Service.ofNode n = .ok u) :
    u.exec.head? = some (.lit (supervisor n)) := by
  unfold Service.ofNode at h
  split at h
  · cases h
  · split at h
    · cases h
    · cases h; simp [Node.exec]

/-- Every rendered unit prevents exactly `preventCodes`. -/
theorem ofNode_prevent_eq (n : Node) (u : Service) (h : Service.ofNode n = .ok u) :
    u.prevent = preventCodes := by
  unfold Service.ofNode at h
  split at h
  · cases h
  · split at h
    · cases h
    · cases h; rfl

/-- A Host status is in the prevent list iff HOST's table calls it fatal: the supervisor's half
adds no Host code (`code_disjoint_host`). -/
theorem mem_preventCodes_host (s : Status) : s.code ∈ preventCodes ↔ s.cls = .fatal := by
  unfold preventCodes
  rw [List.mem_append, Status.mem_codesOf_iff]
  constructor
  · rintro (h | h)
    · exact h
    · exfalso
      simp only [SupervisorExit.codesOf, List.mem_map] at h
      obtain ⟨e, _, he⟩ := h
      exact SupervisorExit.code_disjoint_host e s he
  · exact Or.inl

/-- A supervisor exit is in the prevent list iff CLIENT's table calls it fatal. -/
theorem mem_preventCodes_supervisor (e : SupervisorExit) : e.code ∈ preventCodes ↔ e.cls = .fatal := by
  cases e <;> decide

/-- The prevented codes are exactly the fatal class of the Host's table: a Host status is
prevented from restarting iff it is fatal. -/
theorem ofNode_prevent (n : Node) (u : Service) (h : Service.ofNode n = .ok u) (s : Status) :
    s.code ∈ u.prevent ↔ s.cls = .fatal := by
  rw [ofNode_prevent_eq n u h]; exact mem_preventCodes_host s

/-- ... and of the supervisor's: nd-supervise's own exit is prevented iff it is fatal. -/
theorem ofNode_prevent_supervisor (n : Node) (u : Service) (h : Service.ofNode n = .ok u)
    (e : SupervisorExit) : e.code ∈ u.prevent ↔ e.cls = .fatal := by
  rw [ofNode_prevent_eq n u h]; exact mem_preventCodes_supervisor e

/-- No restart-class or done status is prevented: `uncertain`, a seal's IO and eof are never
mistaken for fatal. -/
theorem ofNode_restart_not_prevented (n : Node) (u : Service) (h : Service.ofNode n = .ok u)
    (s : Status) (hs : s.cls ≠ .fatal) : s.code ∉ u.prevent := by
  rw [ofNode_prevent n u h s]; exact hs

/-- The tooth of the supervisor half: a child killed by a signal (66) is restarted, a launch
refusal (64) is not. Removing the supervisor's codes from `preventCodes` falsifies the second. -/
theorem preventCodes_supervisor_split :
    SupervisorExit.childSignaled.code ∉ preventCodes ∧
    SupervisorExit.refusedAtLaunch.code ∈ preventCodes := by decide

/-- The planted node: nothing hidden → refused by name, never rendered. -/
theorem plant_nothing_hidden : Service.ofNode { writer with hide := [] } = .error .nothingHidden := by
  simp [Service.ofNode]

end Nanodregg.Ops.Units
