/- Reverse provenance: executable token repairs, Grädel–Tannen Prop16 p23.
All token versions remain distinct. Reissue does not implement AGM recovery:
the landed reissue_never_reenables deliberately keeps the old version dead. -/
import Lang.Contextual.Provenance
import Lang.Contextual.RepairObjects

namespace Nanodregg.Lang.Contextual.P9

variable {D : CalculusData} {E : Type}

/-- Prop16 p23: each listed token changes polarity relative to the original world.
Repeated tokens assign the SAME new value; this represents a set of updates, not repeated toggles. -/
def tokenEdits (w : World E) (ts : List Token) : List (Edit E) :=
  ts.map fun t => if w.live t then .withdraw t else .assert t

/-- Prop16 p23: only literals false in the original world need editing. -/
def changes (w : World E) (m : Monomial D) : List Token :=
  ((m.supports.filter fun t => !w.live t) ++ (m.blockers.filter w.live)).eraseDups

/-- Prop16 p23: token repairs cannot change guard environments or budgets.
Specialize those literals NOW, and remove impossible complementary products. -/
def repairTerms (I : Iface D E) (env : E) (cs : List (Candidate D)) : List (Monomial D) :=
  (provenance I cs).filter fun m => m.envOK I env && m.consistent

/-- Prop16 p23: reuse label absorption for edit sets (no negative or env literals here). -/
def planMonomial (w : World E) (m : Monomial D) : Monomial D :=
  ⟨changes w m, [], []⟩

/-- The computed minimal alternatives of token edits. Reuse the same proved absorption
algorithm on change sets, where fewer edits means inclusion, never a guessed cost. -/
def repairPlans (I : Iface D E) (w : World E) (cs : List (Candidate D)) : List (List Token) :=
  (minimal ((repairTerms I w.env cs).map (planMonomial w))).map Monomial.supports

/-- Prop16 p23: P4's actual residual becomes a computed family of repair alternatives.
Unknown holes are distinct from a known hole with no token-only repair. -/
def residualRepairPlans (r : RepairObjects.Residual D E) (u : Nat) :
    Option (List (List Token)) :=
  (r.closure.find u).map fun I => repairPlans I r.world (r.closure.slot u).cands

end Nanodregg.Lang.Contextual.P9
