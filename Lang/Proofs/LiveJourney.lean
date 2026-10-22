/-
# Lang.Proofs.LiveJourney — the contextual ROM the signed journey installs

Closed facts over `Std.contextualHole`, the ROM generator the signed receive journey installs (`generated_signature`,
`linked_signature`, `selected_uses_context`, `used_hypothesis_suspends`), and the meanings of the cyclic-rule filling
it installs (`deployed_cycle_*`). Leaf module.
-/
import Lang.Proofs.LiveHoles
import Lang.Journey.Contextual
import Lang.Journey.ContextualCycle
import Lang.Proofs.BigStep

namespace Nanodregg.Lang

/-! ## From `Lang.Proofs.Contextual.Deployed`: Contextual strengthening and the five reachable resolutions in deployed Lang. -/
section

namespace DeployedContextual
open Journey.Contextual

/-- Successful generation preserves the declared context and candidate code in
the installed root's signature. Linking changes only import identities. -/
theorem generated_signature {A : Ty} {d : HoleROM} {σ : List Term} {clause : Term}
    {b : Std.HoleBundle} (hb : Std.contextualHole A d σ clause = .ok b) :
    ∃ h, b.layout.holes = [h] ∧ h.ctx = d.ctx ∧ h.ty = d.ty ∧ h.code = d.code ∧
      h.hypotheses = d.hypotheses ∧ h.guardPin = d.guardPin ∧ h.guard = d.guard := by
  unfold Std.contextualHole at hb
  simp only [bind, Except.bind, pure, Except.pure] at hb
  repeat' split at hb
  all_goals first | (simp at hb; done) | skip
  cases hb
  exact ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem linked_signature {b : Std.HoleBundle} {ids : List ByteArray} {p : Package}
    (hp : b.linkContextual ids = .ok p) : p.holes = b.layout.holes := by
  unfold Std.HoleBundle.linkContextual at hp
  simp only [bind, Except.bind, pure, Except.pure] at hp
  repeat' split at hp
  all_goals first | (simp at hp; done) | skip
  cases hp
  rfl

/-- The selected ROM filling actually uses hypothesis 1. This is the nonempty
context that the old langTemplate_no_hyps boundary made unreachable. -/
theorem selected_uses_context :
    (selectHole (view (some 0) (some 1)) (3 : Kernel.Sim.D)
      { declaration with selectionRel := 5, selectionKey := key }).map
        (fun s => (s.context, Term.usesVar 1 s.body)) = .ok ([.bool, .nat], true) := by
  rfl

/-- Dropping the unused bool produces a typed open nat filling, with the
embedding reconstructing the original open term. No closed witness is invented. -/
theorem strengthening_factor :
    (selectHole (view (some 0) none) (3 : Kernel.Sim.D)
      { declaration with selectionRel := 5, selectionKey := key }).map
        (fun s => (s.context, s.filling, s.body, inferE [] s.context s.filling (Ω := []))) =
      .ok ([.nat], .var 0, .var 1, .ok .nat) := by
  change Except.ok (ε := HoleRefusal) ([Ty.nat], Term.var 0, Term.var 1, inferE [] [.nat] (.var 0) (Ω := [])) = _
  rw [inferE_complete (HasType.var rfl)]

/-- For every supplied nat, capture-avoiding contextual instantiation returns
that nat after the deployed factorization. -/
theorem strengthening_uses_argument (n : Nat) :
    (selectHole (view (some 0) none) (3 : Kernel.Sim.D)
      { declaration with selectionRel := 5, selectionKey := key }).map
        (fun s => Term.substList [.bool true, .nat n] s.body) = .ok (.nat n) := by
  rfl

theorem kept_context :
    (selectHole (view (some 0) (some 1)) (3 : Kernel.Sim.D)
      { declaration with selectionRel := 5, selectionKey := key }).map
        (fun s => (s.index, s.strengthened, s.body)) = .ok (0, [], .var 1) := by
  rfl

/-- Changing only the authenticated selected derivation preserves its filling
after the first route's support is withdrawn. -/
theorem alternative_same_filling :
    (selectHole (view (some 1) (some 1) (left := none)) (3 : Kernel.Sim.D)
      { declaration with selectionRel := 5, selectionKey := key }).map
        (fun s => (s.index, s.body)) = .ok (1, .var 1) := by
  rfl

/-- The chooser can select retained code with a different filling; the new
constant is checked at the declaration's original contextual type. -/
theorem replacement_filling :
    (selectHole (view (some 2) none (used := none)) (3 : Kernel.Sim.D)
      { declaration with selectionRel := 5, selectionKey := key }).map
        (fun s => (s.index, s.context, s.body)) = .ok (2, [], .nat 9) := by
  rfl

/-- A used withdrawn hypothesis suspends this very filling, by its exact name.
It cannot be strengthened as though the variable were unused. -/
theorem used_hypothesis_suspends :
    selectHole (view (some 0) (some 1) (used := none)) (3 : Kernel.Sim.D)
      { declaration with selectionRel := 5, selectionKey := key } =
      .error (.supportMoved 0 1) := by
  rfl

end DeployedContextual

end

/-! ## From `Lang.Proofs.Contextual.DeployedCycle`: Meanings of the cyclic-rule filling actually installed by the signed journey. -/
section

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

end

end Nanodregg.Lang
