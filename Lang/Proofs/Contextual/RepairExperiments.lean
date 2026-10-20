/- Concrete sessions for P4. World repair uses the real CMTT instance.
Transport has a separate, explicitly data-only representation checker (no CalculusLaws claim):
a payload tagged old/new. Its certificate proves an equivalence for ALL Nat payloads. -/
import Lang.Proofs.Contextual.RepairObjects
import Lang.Contextual.CoreCalculus

namespace Nanodregg.Lang.Contextual.RepairObjects.Experiments

private def token : Token := ⟨7, 0⟩
private def w : World Unit := ⟨fun t => t == token, ()⟩
private def I : Iface cmttData Unit :=
  ⟨0, [], .arr .base .base, [], by simp, fun _ _ => true, 10, 1, 2⟩
private def tpl : Template cmttData Unit :=
  ⟨[], .arr .base .base, .mvar 0 [], [I], by simp [I]⟩
private def c (cost : Nat) (party : Nat := 3) : Candidate cmttData :=
  ⟨.lam .base (.var 0), [token], [], cost, party, .verified⟩
private def start : Closure cmttData Unit := fromScratch w tpl fun _ => []

private def initial : Except Refusal (World Unit × Closure cmttData Unit) :=
  Session.run [.propose 0 (c 5), .propose 0 (c 2 4), .select 1 0 0] (w, start)

private def project {α : Type} (f : World Unit → Closure cmttData Unit → α)
    (session : Except Refusal (World Unit × Closure cmttData Unit)) : Option α :=
  match session with
  | .error _ => none
  | .ok (world, cl) => some (f world cl)

private def withdrawal (world : World Unit) (cl : Closure cmttData Unit) :=
  (Repair.atomic world (.withdraw token)).run ⟨cl⟩

private def composed (world : World Unit) (cl : Closure cmttData Unit) :=
  ((Repair.atomic world (.withdraw token)).compose
    (Repair.atomic ((Edit.withdraw token).apply world) (.assert token))).run ⟨cl⟩

/-- A real propose/select session loses both candidates, retains named residuals, then
resumes without re-proposing. Composition exposes the now-resolved intermediate obligation. -/
theorem withdraw_resume_session :
    project (fun world cl => observe (withdrawal world cl).state.closure) initial =
      some [[.suspended [token], .suspended [token]]] ∧
    project (fun world cl => (withdrawal world cl).residuals.flatMap Residual.obligations) initial =
      some [.support 0 0 token, .refill 0, .support 0 1 token] ∧
    project (fun world cl => observe (composed world cl).state.closure) initial =
      some [[.verified, .verified]] ∧
    project (fun world cl => (composed world cl).residuals.map Residual.obligations) initial =
      some [[.support 0 0 token, .refill 0, .support 0 1 token], []] := by decide

private def selected (policy : Policy cmttData) (p : Party := 1)
    (accepted : Bool := false) : Option (Option Nat) :=
  project (fun world cl =>
    match RepairObjects.select policy world p 0
        { cl with slot := fun u => { cl.slot u with accepted := accepted } } with
    | .ok (_, i) => some i
    | .error _ => none) initial

private def ours : Policy cmttData := ⟨fun c => c.by_ == 3, Candidate.cost⟩

/-- Policy changes the chosen index; it cannot waive the chooser or accepted-prefix checks. -/
theorem policy_session :
    selected .cheapest = some (some 1) ∧ selected ours = some (some 0) ∧
    selected .cheapest 9 = some none ∧ selected .cheapest 1 true = some none := by decide

private def overBudget : Except Refusal (World Unit × Closure cmttData Unit) :=
  Session.run [.propose 0 (c 11)] (w, start)

/-- Even a policy assigning zero cost cannot make the hard-budget failure selectable. -/
theorem preference_cannot_waive_budget :
    project (fun world cl =>
      match RepairObjects.select ⟨fun _ => true, fun _ => 0⟩ world 1 0 cl with
      | .ok _ => true
      | .error _ => false) overBudget = some false := by decide

/-- Data-only representation checker, not a claimed contextual language instance. -/
private def repData : CalculusData where
  Ty := Bool
  Ctx := Unit
  Tm := Nat × Bool
  tmEq := inferInstance
  msubst _ t := t
  check _ t ty := t.2 == ty
  uses _ _ := false
  drop _ _ := ()
  strengthen _ t := t
  weaken _ t := t
  var x := (x, false)
  lookup _ _ := none

private def source : Iface repData Unit :=
  ⟨0, (), false, [], by simp, fun _ _ => true, 10, 1, 2⟩
private def target : Iface repData Unit :=
  ⟨1, (), true, [], by simp, fun _ c => c.1 < 10, 10, 1, 2⟩
private def swap (t : Nat × Bool) : Nat × Bool := (t.1, !t.2)
private def q : Correspondence repData Unit := ⟨source, target, swap, swap⟩
private def registry : Registry repData Unit := fun n => if n = 17 then some q else none
private def original (n : Nat := 7) : Candidate repData :=
  ⟨(n, false), [token], [], 1, 3, .verified⟩

/-- This registry contains a checked two-sided equivalence on ALL payloads, not a lookup
table containing only the single filling exercised below. -/
theorem representation_equivalence : q.Checked := by
  constructor
  · intro t ht
    cases t with
    | mk n b => cases b <;> simp_all [repData, q, source, target, swap]
  · intro t ht
    cases t with
    | mk n b => cases b <;> simp_all [repData, q, source, target, swap]
  · intro t _
    cases t with
    | mk n b => cases b <;> rfl
  · intro t _
    cases t with
    | mk n b => cases b <;> rfl

theorem registry_checked : registry.Sound := by
  intro n q' h
  unfold registry at h
  split at h
  · cases h; exact representation_equivalence
  · cases h

private inductive TransportView where
  | ok (kind : OutcomeKind) (payload : Nat) (source target : Bool)
  | error (reason : TransportRefusal)
deriving DecidableEq

private def transportView (r : Except TransportRefusal (RepairObjects.Outcome repData Unit)) :
    TransportView :=
  match r with
  | .error e => .error e
  | .ok out => match out with
    | .existing _ => .ok out.kind 0 false false
    | .transported ev =>
        .ok out.kind ev.image.filling.1 ev.correspondence.source.ty ev.correspondence.target.ty

/-- The proposition/type changes false→true, the payload is preserved, and transport has
its own outcome, not replacement. Destination guard, support, cost and certificate matter. -/
theorem transport_session :
    transportView (transport registry 17 w (original 7) 2) =
      .ok .transported 7 false true ∧
    transportView (transport registry 99 w (original 7) 2) =
      .error .unknownCertificate ∧
    transportView (transport registry 17 w (original 12) 2) =
      .error (.destination (.conflict .guardFails)) ∧
    transportView (transport registry 17 ((Edit.withdraw token).apply w) (original 7) 2) =
      .error (.destination (.suspended [token])) ∧
    transportView (transport registry 17 w (original 7) 11) =
      .error (.destination (.uncovered 11 10)) ∧
    transportView (transport registry 17 w { original 7 with filling := (7, true) } 2) =
      .error .sourceIllTyped := by decide

/-- An arbitrary replacement that forgets the representation conversion is ill typed.
The certificate's forward map is necessary, even though the payload value is unchanged. -/
theorem identity_transport_fails :
    judge target w (original 7) = .conflict .illTyped ∧
    judge target w (q.image (original 7) 2) = .verified := by decide


private def representationTemplate : Template repData Unit :=
  ⟨(), true, (0, true), [target], by simp [target]⟩
private def representationState : State repData w :=
  ⟨fromScratch w representationTemplate fun _ => []⟩

/-- Transport is part of the first-class repair result, including refused offers by name.
It does not silently select the new term or overwrite an old template. -/
theorem transport_in_repair_result :
    (((Repair.identity w).withTransport registry 17 (original 7) 2).run
      representationState).residuals.flatMap (fun r => r.outcomes.map RepairObjects.Outcome.kind) =
        [.transported] ∧
    (((Repair.identity w).withTransport registry 99 (original 7) 2).run
      representationState).transportRefusals = [.unknownCertificate] ∧
    (((Repair.identity w).withTransport registry 17 (original 7) 2).run
      representationState).state.closure.sigma 1 = none := by decide

/-- Coherence is inhabited by this concrete session, so repair_correctness is applicable
to the actual experiment, not merely to a hypothetical invariant. -/
theorem initial_coherent :
    ∃ world cl, initial = .ok (world, cl) ∧ Coherent world cl := by
  cases h : initial with
  | error r =>
    have hok : project (fun _ _ => true) initial = some true := by decide
    rw [h] at hok
    cases hok
  | ok st =>
    exact ⟨st.1, st.2, rfl, session_preserves_coherent _
      (fromScratch_coherent w tpl _) h⟩


private def transportedSession : Option (Nat × Bool) :=
  match transport registry 17 w (original 7) 2 with
  | .ok (.transported ev) =>
    match Session.run [.propose 1 ev.image, .select 1 1 0] (w, representationState.closure) with
    | .ok (_, cl) => cl.sigma 1
    | .error _ => none
  | _ => none

/-- The transported filling reaches the ordinary propose/select consumer in the new template,
rather than remaining an isolated correspondence result. -/
theorem transported_filling_selects : transportedSession = some (7, true) := by decide

end Nanodregg.Lang.Contextual.RepairObjects.Experiments
