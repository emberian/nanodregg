/- Repair observations as change structures, Cai et al. (2013), Defs 2.1–2.4 p2.
The full residual history is deliberately not quotiented by final observation. -/
import Lang.Contextual.RepairObjects

namespace Nanodregg.Lang.Contextual.RepairChanges

/-- Change-structure data; the update/difference law lives in Proofs (Cai et al. Def 2.1 p2). -/
structure ChangeData (A : Type) where
  Delta : A → Type
  update : (a : A) → Delta a → A
  difference : (new old : A) → Delta old

/-- Nil is the self-difference (Cai et al. Def 2.2 p2). -/
def ChangeData.nil {A : Type} (C : ChangeData A) (a : A) : C.Delta a :=
  C.difference a a

/-- Replacement changes with an explicit nil, lawful for arbitrary decidable observations.
Changes need not have a unique representation (Cai et al. p2). -/
def replacement (A : Type) [DecidableEq A] : ChangeData A where
  Delta _ := Option A
  update a d := d.getD a
  difference new old := if new = old then none else some new

/-- Compose replacement changes; the later non-nil change wins (Cai et al. p2). -/
def compose {A : Type} (first second : Option A) : Option A :=
  match second with | none => first | some a => some a

/-- The observed derivative is computed by the actual repair interpreter; from-scratch
consistency proves its derivative law (Cai et al. Def 2.4 p2). -/
def derivative {D : CalculusData} {E : Type} {w v : World E}
    {e : RepairObjects.Change E w v} (r : RepairObjects.Repair D e)
    (s : RepairObjects.State D w) : Option (List (List Status)) :=
  (replacement _).difference (observe (r.run s).state.closure) (observe s.closure)

end Nanodregg.Lang.Contextual.RepairChanges
