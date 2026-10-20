import Lang.Contextual.RepairChanges
import Lang.Proofs.Contextual.RepairObjects

namespace Nanodregg.Lang.Contextual.RepairChanges

/-- Update after difference recovers the new value (Cai et al. Def 2.1(e) p2). -/
structure Laws {A : Type} (C : ChangeData A) : Prop where
  update_difference : ∀ new old, C.update old (C.difference new old) = new

/-- The replacement representation satisfies the change-structure law
(Cai et al. Def 2.1 p2); no invertibility of changes is claimed. -/
theorem replacement_laws (A : Type) [DecidableEq A] : Laws (replacement A) := by
  constructor
  intro new old
  by_cases h : new = old <;> simp [replacement, h]

/-- Nil changes keep values, derived from the difference law (Cai et al. Lemma 2.3 p2). -/
theorem nil_kept {A : Type} {C : ChangeData A} (h : Laws C) (a : A) :
    C.update a (C.nil a) = a := h.update_difference a a

/-- Sequential changes agree with composed changes (Cai et al. pp2–3). -/
theorem update_compose {A : Type} [DecidableEq A] (a : A) (d e : Option A) :
    (replacement A).update a (compose d e) =
      (replacement A).update ((replacement A).update a d) e := by
  cases e <;> rfl

/-- Associativity includes nil (Cai et al. pp2–3, replacement instance). -/
theorem compose_assoc {A : Type} (a b c : Option A) :
    compose (compose a b) c = compose a (compose b c) := by
  cases c <;> rfl

/-- The actual first-class identity repair keeps its entire state and emits no inspections
or residuals; this is the nil/kept case, not a recheck (Cai et al. Lemma 2.3 p2). -/
theorem identity_kept {D : CalculusData} {E : Type} {w : World E}
    (s : RepairObjects.State D w) :
    (RepairObjects.Repair.identity w).run s = ⟨s, [], [], []⟩ := rfl

/-- Identity repair has a nil observed derivative (Cai et al. Def 2.2 p2). -/
theorem identity_derivative {D : CalculusData} {E : Type} {w : World E}
    (s : RepairObjects.State D w) :
    derivative (RepairObjects.Repair.identity w) s = none := by
  simp [derivative, RepairObjects.Repair.identity, replacement]

/-- From-scratch consistency supplies the derivative equation for actual Repair values,
rather than assuming the desired equation as a law (Cai et al. Def 2.4 p2). -/
theorem repair_derivative {D : CalculusData} {E : Type} {w v : World E}
    {e : RepairObjects.Change E w v} {r : RepairObjects.Repair D e}
    (hr : r.Sound) (s : RepairObjects.State D w) (hc : Coherent w s.closure) :
    (replacement _).update (observe s.closure) (derivative r s) =
      RepairObjects.analyze v s.closure := by
  unfold derivative
  rw [(replacement_laws _).update_difference]
  exact RepairObjects.repair_correctness hr s hc

/-- Composition preserves the same derivative law for the original retained problem
(Cai et al. Lemma 2.8 p3). No landed compose_sound premise changes. -/
theorem composed_derivative {D : CalculusData} {E : Type} {w v z : World E}
    {e : RepairObjects.Change E w v} {f : RepairObjects.Change E v z}
    {r : RepairObjects.Repair D e} {s : RepairObjects.Repair D f}
    (hr : r.Sound) (hs : s.Sound) (st : RepairObjects.State D w)
    (hc : Coherent w st.closure) :
    (replacement _).update (observe st.closure) (derivative (r.compose s) st) =
      RepairObjects.analyze z st.closure :=
  repair_derivative (RepairObjects.compose_sound hr hs) st hc

/-- Repair composition is associative INCLUDING residuals, inspected candidates and refusals,
not just final observations (Cai et al. pp2–3, path action instance). -/
theorem repair_compose_assoc {D : CalculusData} {E : Type} {w v z q : World E}
    {e : RepairObjects.Change E w v} {f : RepairObjects.Change E v z}
    {g : RepairObjects.Change E z q}
    (r : RepairObjects.Repair D e) (s : RepairObjects.Repair D f)
    (t : RepairObjects.Repair D g) (st : RepairObjects.State D w) :
    ((r.compose s).compose t).run st = (r.compose (s.compose t)).run st := by
  simp [RepairObjects.Repair.compose, List.append_assoc]

/-- Both identity sides preserve complete result records (Cai et al. Lemma 2.3 p2). -/
theorem repair_identity_sides {D : CalculusData} {E : Type} {w v : World E}
    {e : RepairObjects.Change E w v} (r : RepairObjects.Repair D e)
    (st : RepairObjects.State D w) :
    ((RepairObjects.Repair.identity w).compose r).run st = r.run st ∧
      (r.compose (RepairObjects.Repair.identity v)).run st = r.run st := by
  simp [RepairObjects.Repair.compose, RepairObjects.Repair.identity]

end Nanodregg.Lang.Contextual.RepairChanges
