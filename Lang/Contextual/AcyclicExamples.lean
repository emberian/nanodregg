/- Finite adapter witnesses and adversarial graphs; no change to Worlds semantics. -/
import Lang.Contextual.Acyclic

namespace Nanodregg.Lang.Contextual.Acyclic

/-- Hole 1 requires hole 0 jointly with its own local provenance. -/
def chain (dependency consumer : Polynomial) : Graph 2 where
  body i := if i.val = 0 then .tokens dependency else .joint (.tokens consumer) (.hole 0)
  rank i := i.val

def seed : Polynomial := [([⟨10, 0⟩], [⟨11, 0⟩]), ([⟨12, 0⟩], [])]
def localCondition : Polynomial := [([⟨13, 0⟩], [⟨14, 0⟩])]

/-- The seed does not license treating the recursive branch as an absent alternative. -/
def selfDependent : Graph 1 where
  body _ := .alt (.tokens seed) (.hole 0)
  rank _ := 0

def mutualCycle : Graph 2 where
  body i := if i.val = 0 then .hole 1 else .hole 0
  rank i := i.val

/-- A cycle in an undemanded hole must still be reported for the supplied graph. -/
def hiddenCycle : Graph 2 where
  body i := if i.val = 0 then .tokens seed else .hole 1
  rank i := i.val

/-- Even a zero product must not erase an unsupported dependency before validation. -/
def zeroMaskedCycle : Graph 1 where
  body _ := .joint (.tokens []) (.hole 0)
  rank _ := 0

def badWitness : Graph 2 :=
  { chain seed localCondition with rank := fun _ => 0 }

end Nanodregg.Lang.Contextual.Acyclic
