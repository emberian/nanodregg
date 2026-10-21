/- Meanings of the cyclic-rule filling actually installed by the signed journey. -/
import Lang.Journey.ContextualCycle
import Lang.Proofs.BigStep

namespace Nanodregg.Lang
open Journey

/-- The least solution for p follows its external grounding, not its old value.
With no grounding, mutual p/q support cannot make either one true. -/
theorem deployed_cycle_p (lib : List Term) (a u : Bool) :
    BigStep lib [.bool a, .bool u] (.get cycleTerm "p") (.ok (.bool a)) := by
  apply BigStep.get BigStep.record
  apply Sel.field (by rfl)
  cases a
  · exact .iteF (.var rfl) (.iteF (.var rfl) .bool)
  · exact .iteT (.var rfl) .bool

theorem deployed_cycle_q (lib : List Term) (a u : Bool) :
    BigStep lib [.bool a, .bool u] (.get cycleTerm "q") (.ok (.bool a)) := by
  apply BigStep.get BigStep.record
  apply Sel.field (by rfl)
  cases a
  · exact .iteF (.var rfl) .bool
  · exact .iteT (.var rfl) .bool

/-- Withdrawing the p/q grounding leaves the independent branch's value intact. -/
theorem deployed_cycle_independent (lib : List Term) (a u : Bool) :
    BigStep lib [.bool a, .bool u] (.get cycleTerm "r") (.ok (.bool u)) := by
  exact .get .record (.field rfl (.var rfl))

end Nanodregg.Lang
