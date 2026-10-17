/-
# Ops.Proofs.Units — a rendered unit is confined, and restarts exactly HOST's restart class
-/
import Ops.Units
import Host.Proofs.Exit

namespace Nanodregg.Ops.Units

open Nanodregg.Host

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

/-- The prevented codes are exactly HOST's fatal class: a status is prevented from restarting iff
the table calls it fatal. -/
theorem ofNode_prevent (n : Node) (u : Service) (h : Service.ofNode n = .ok u) (s : Status) :
    s.code ∈ u.prevent ↔ s.cls = .fatal := by
  unfold Service.ofNode at h
  split at h
  · cases h
  · split at h
    · cases h
    · cases h; exact Status.mem_codesOf_iff s .fatal

/-- No restart-class or done status is prevented: `uncertain`, a seal's IO and eof are never
mistaken for fatal. -/
theorem ofNode_restart_not_prevented (n : Node) (u : Service) (h : Service.ofNode n = .ok u)
    (s : Status) (hs : s.cls ≠ .fatal) : s.code ∉ u.prevent := by
  rw [ofNode_prevent n u h s]; exact hs

/-- The planted node: nothing hidden → refused by name, never rendered. -/
theorem plant_nothing_hidden : Service.ofNode { writer with hide := [] } = .error .nothingHidden := by
  simp [Service.ofNode]

end Nanodregg.Ops.Units
