/- Concrete CMTT trace sessions. All fixtures use the landed calculus, not a toy checker. -/
import Lang.Contextual.Trace
import Lang.Contextual.CoreCalculus

namespace Nanodregg.Lang.Contextual.Trace.Examples

/-- A guard reading exactly the filling's variable key; Mokhov et al. 2018, §4.2.2 p.79:14. -/
def guard : Guard cmttData Nat Nat where
  reads := fun t => match t with | .var i => [i] | _ => []
  run := fun _ vs => vs.all (fun n => n > 0)

/-- Two real context hypotheses, one token-backed; Mokhov et al. 2018, §4.2.2 p.79:14. -/
def iface : Iface cmttData (Nat → Nat) where
  name := 10
  ctx := [.base, .base]
  ty := .base
  hyps := [(0, ⟨2, 0⟩)]
  hyps_real := by intro h hh; simp at hh; subst h; rfl
  guard := fun _ _ => true
  budget := 3
  chooser := 0
  acceptor := 1

/-- Positive, negative, and implicit hypothesis dependencies; Mokhov et al. 2018, §4.2.2 p.79:14. -/
def candidate (i : Nat) : Candidate cmttData :=
  ⟨.var i, if i = 0 then [⟨1, 0⟩] else [], if i = 0 then [⟨3, 0⟩] else [],
   1, 0, .conflict .illTyped⟩

/-- A complete initial world; Mokhov et al. 2018, §4.2.2 p.79:14. -/
def world : World (Nat → Nat) := ⟨fun t => t.id == 1 || t.id == 2, fun _ => 1⟩

/-- Change one environment key; Mokhov et al. 2018, Def.2.1 p.79:3. -/
def envEdit (k v : Nat) : World (Nat → Nat) :=
  { world with env := fun j => if j = k then v else world.env j }

/-- Two initialized candidate traces; Mokhov et al. 2018, §4.2.2 p.79:15. -/
def cached : List (Cached cmttData Nat) :=
  [seed guard iface world (candidate 0), seed guard iface world (candidate 1)]

/-- One pass at a new world; Mokhov et al. 2018, Def.2.1 p.79:3. -/
def run (w : World (Nat → Nat)) : Pass cmttData Nat := repair guard iface w cached 0

end Nanodregg.Lang.Contextual.Trace.Examples
