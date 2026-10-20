/- Concrete consumers for P11b; each check has a mutation probe in lane scratch. -/
import Lang.Proofs.Contextual.Material
import Lang.Proofs.Contextual.ModalBoundary
import Lang.Proofs.Contextual.TransportKinds
import Lang.Proofs.Contextual.RepairChanges
import Lang.Proofs.Contextual.ContextMorphisms

namespace Nanodregg.Lang.Contextual.P11bExperiments

private def tests (_ : Bool) : List (Material.Test Nat) :=
  [⟨0, [], fun n => n == 7⟩]

private def visited (_ : Bool) : P1.Nullable.Handler → Material.Filling Nat
  | .unchecked => .gaveUp
  | _ => .answer 7

/-- The legacy judge accepted unchecked at a non-null world; the visited give-up now
refuses it while an answered interaction still verifies (Fouquere–Quatrini pp24–26). -/
theorem material_candidate_check :
    judge P1.Nullable.iface P1.Nullable.world (P1.Nullable.candidate .unchecked) = .verified ∧
    (Material.inspectCandidate P1.Nullable.iface tests visited P1.Nullable.world
      (P1.Nullable.candidate .unchecked)).1 = .conflict .guardFails ∧
    (Material.inspectCandidate P1.Nullable.iface tests visited P1.Nullable.world
      (P1.Nullable.candidate .tolerate)).1 = .verified := by decide

/-- Material admission also retains the old guard: completing a test cannot make the
null-unsafe candidate admissible after withdrawing non-nullness (Fouquere–Quatrini p24). -/
theorem material_keeps_old_guard :
    (Material.inspectCandidate P1.Nullable.iface tests (fun _ _ => .answer 7)
      ⟨fun _ => false, false⟩ (P1.Nullable.candidate .unchecked)).1 =
      .conflict .guardFails := by decide

private def token : Token := ⟨37, 0⟩
private def world : World Unit := ⟨fun t => t == token, ()⟩
private def iface : Iface cmttData Unit :=
  ⟨0, [], .arr .base .base, [], by simp, fun _ _ => true, 2, 1, 2⟩
private def filling : Candidate cmttData :=
  ⟨.lam .base (.var 0), [token], [], 1, 3, .verified⟩
private def template : Template cmttData Unit :=
  ⟨[], .arr .base .base, .mvar 0 [], [iface], by decide⟩
private def state : RepairObjects.State cmttData world :=
  ⟨fromScratch world template fun _ => [filling]⟩
private def correspondence : RepairObjects.Correspondence cmttData Unit :=
  ⟨iface, iface, id, id⟩
private def registry : RepairObjects.Registry cmttData Unit :=
  fun n => if n = 1 then some correspondence else none

/-- Withdrawal creates a non-nil observed derivative with the actual suspended obligation
(Cai et al. Def 2.4 p2). -/
theorem withdrawal_derivative :
    RepairChanges.derivative (RepairObjects.Repair.atomic world (.withdraw token)) state =
      some [[.suspended [token]]] := by decide

/-- Applying the observed change reconstructs the recomputed answer; self-difference
is kept (Cai et al. Def 2.1(e), Lemma 2.3 p2). -/
theorem difference_update_computes :
    (RepairChanges.replacement Nat).update 7
      ((RepairChanges.replacement Nat).difference 9 7) = 9 ∧
    (RepairChanges.replacement Nat).difference 7 7 = none := by exact ⟨rfl, rfl⟩

/-- The wrapper must forward the actual requested cost to the destination recheck
(Ringer et al. p7). -/
theorem recheck_cost_refusal :
    (match TransportKinds.recheck registry 1 world filling 3 with
      | .error (.destination (.uncovered 3 2)) => true
      | _ => false) = true := by decide

/-- Rechecked evidence is emitted on success, and remains distinguishable from the
internally proved form (Ringer p7; Viola pp1–2). -/
theorem recheck_emits_rechecked :
    (match TransportKinds.recheck registry 1 world filling 1 with
      | .ok (.rechecked ev) => isVerified (judge ev.correspondence.target world ev.image)
      | _ => false) = true := by decide

private def extensionalIface : Iface cmttData Unit :=
  { (ModalBoundary.boundary [.base] .base .isApplication ModalBoundary.betaObservation).iface
      with guard := fun _ _ => true }

/-- A real CMTT beta change supplies internal evidence through quotient equality and
a value guard, without running the new guard. The required checker/support/cost equalities
are inhabited by the same concrete candidates (Viola pp1–2; Kavvos p1). -/
theorem internal_beta_transport :
    TransportKinds.Valid extensionalIface ModalBoundary.world ModalBoundary.betaObservation
      (.internal (ModalBoundary.candidate ModalBoundary.redex)
        (ModalBoundary.candidate ModalBoundary.reduced)) := by
  apply TransportKinds.internal_from_quotient ModalBoundary.betaObservation
    (I := extensionalIface)
  · exact ⟨fun _ _ => true, fun _ _ => rfl⟩
  · exact Quot.sound rfl
  · decide
  · decide
  · rfl
  · rfl
  · rfl

/-- Quotient transport is an actual equivalence for all representatives, not only
a Boolean example: discarding/adding a flag are mutually inverse on quotients
(Viola et al. p2). -/
theorem flag_quotient_equivalence :
    (∀ q : TransportKinds.Observed (Nat × Bool) Nat Prod.fst,
      TransportKinds.liftMap id Prod.fst (fun n => (n, false)) (fun _ => rfl)
        (TransportKinds.liftMap Prod.fst id Prod.fst (fun _ => rfl) q) = q) ∧
    (∀ q : TransportKinds.Observed Nat Nat id,
      TransportKinds.liftMap Prod.fst id Prod.fst (fun _ => rfl)
        (TransportKinds.liftMap id Prod.fst (fun n => (n, false)) (fun _ => rfl) q) = q) := by
  constructor
  · exact TransportKinds.quotient_inverse Prod.fst id Prod.fst (fun n => (n, false))
      (fun _ => rfl) (fun _ => rfl)
  · exact TransportKinds.quotient_inverse id Prod.fst (fun n => (n, false)) Prod.fst
      (fun _ => rfl) (fun _ => rfl)


/-- An internally justified destination is consumable by the ordinary chooser; the
existing propose/select checks remain authoritative (Viola pp1–2). -/
theorem internal_offer_selects :
    (let claim : TransportKinds.Claim cmttData Unit :=
        .internal (ModalBoundary.candidate ModalBoundary.redex)
          (ModalBoundary.candidate ModalBoundary.reduced)
     let tpl : Template cmttData Unit :=
        ⟨[.base], .base, .mvar 0 [.var 0], [extensionalIface], by decide⟩
     let initial := fromScratch ModalBoundary.world tpl (fun _ => [])
     match Session.run [.propose 0 claim.destination, .select 1 0 0]
         (ModalBoundary.world, initial) with
     | .ok (_, cl) => cl.sigma 0
     | .error _ => none) = some (.var 0) := by decide

end Nanodregg.Lang.Contextual.P11bExperiments
