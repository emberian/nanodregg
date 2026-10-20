import Lang.Contextual.TransportKinds
import Lang.Proofs.Contextual.RepairObjects
import Lang.Proofs.Contextual.Stability

namespace Nanodregg.Lang.Contextual.TransportKinds

/-- Evidence is indexed by the actual evidence form; internal evidence includes a relation
and preserved proposition, while rechecked evidence names the destination judgment
(Ringer p7; Viola pp1–2). -/
inductive Valid {D : CalculusData} {E V : Type} (I : Iface D E) (w : World E)
    (value : D.Tm → V) : Claim D E → Prop where
  | rechecked {ev : RepairObjects.TransportEvidence D E} :
      ev.correspondence.target = I → judge I w ev.image = .verified →
      Valid I w value (.rechecked ev)
  | internal {source target : Candidate D} :
      value source.filling = value target.filling →
      judge I w target = .verified → Valid I w value (.internal source target)

/-- Successful translation validation really rejudges the returned destination term;
the claim does not inherit validity from its tag (Ringer et al. p7). -/
theorem recheck_sound {D : CalculusData} {E : Type}
    {registry : RepairObjects.Registry D E} (hr : registry.Sound)
    {n : Nat} {w : World E} {c : Candidate D} {cost : Nat}
    {ev : RepairObjects.TransportEvidence D E}
    (h : recheck registry n w c cost = .ok (.rechecked ev)) :
    judge ev.correspondence.target w ev.image = .verified := by
  unfold recheck at h
  split at h
  · cases h
  · rename_i ev' he
    cases h
    exact (RepairObjects.transport_sound hr he).2.2.2.2.1
  · cases h

/-- Representation maps commute with observations on every quotient element
(Viola et al. p2, internally proved in Lean). -/
theorem lift_observation {A B V : Type} (a : A → V) (b : B → V) (f : A → B)
    (h : ∀ x, b (f x) = a x) (q : Observed A V a) :
    observation b (liftMap a b f h q) = observation a q := by
  induction q using Quot.ind with
  | _ x => exact h x

/-- Two observation-preserving maps are inverse on quotients, although concrete
representatives need not be equal (Viola et al. p2). -/
theorem quotient_inverse {A B V : Type} (a : A → V) (b : B → V)
    (f : A → B) (g : B → A)
    (hf : ∀ x, b (f x) = a x) (hg : ∀ y, a (g y) = b y)
    (q : Observed A V a) :
    liftMap b a g hg (liftMap a b f hf q) = q := by
  induction q using Quot.ind with
  | _ x =>
    apply Quot.sound
    exact (hg (f x)).trans (hf x)

/-- An extensional predicate transports internally along the quotient map; no fresh
execution of the predicate is required (Viola et al. pp1–2). -/
theorem quotient_predicate_transport {A B V : Type} (a : A → V) (b : B → V)
    (f : A → B) (hf : ∀ x, b (f x) = a x) (P : V → Prop)
    (q : Observed A V a) (h : P (observation a q)) :
    P (observation b (liftMap a b f hf q)) := by
  rw [lift_observation]
  exact h

/-- The two evidence forms cannot be confused by a consumer (Ringer p7; Viola p1). -/
theorem evidence_forms_distinct {D : CalculusData} {E : Type}
    (ev : RepairObjects.TransportEvidence D E) (s t : Candidate D) :
    Claim.rechecked ev ≠ .internal s t := by
  intro h
  cases h

/-- Forgetting a representation flag is many-to-one, yet quotient-invertible
(Viola et al. p2, analogous to their multiple queue representatives). -/
theorem redundant_flag_quotient :
    Quot.mk (fun x y : Nat × Bool => x.1 = y.1) (7, false) =
      Quot.mk (fun x y : Nat × Bool => x.1 = y.1) (7, true) ∧
    (7, false) ≠ (7, true) := by
  exact ⟨Quot.sound rfl, by decide⟩


/-- A quotient relation plus a value guard derives destination validity internally.
Typing, dependencies and cost remain independent obligations: quotient equality does
not erase them (Viola et al. pp1–2; Kavvos p1). -/
theorem internal_from_quotient {D : CalculusData} {E V : Type}
    (value : D.Tm → V) {I : Iface D E} (hg : ValueGuard value I.guard)
    {w : World E} {s t : Candidate D}
    (hq : (Quot.mk _ s.filling : Observed D.Tm V value) = Quot.mk _ t.filling)
    (hs : judge I w s = .verified)
    (hchk : D.check I.ctx t.filling I.ty = D.check I.ctx s.filling I.ty)
    (hb : t.blockers = s.blockers) (hdeps : effSupports I t = effSupports I s)
    (hcost : t.cost = s.cost) :
    Valid I w value (.internal s t) := by
  have hv : value s.filling = value t.filling :=
    congrArg (observation value) hq
  exact .internal hv ((judge_stable value hg hv.symm hchk hb hdeps hcost).trans hs)

/-- Both evidence forms deliver admission of their actual destination; the internal form
also carries an observable equality (Ringer p7; Viola pp1–2). -/
theorem internal_valid_destination {D : CalculusData} {E V : Type}
    {I : Iface D E} {w : World E} {value : D.Tm → V} {s t : Candidate D}
    (h : Valid I w value (.internal s t)) :
    value s.filling = value t.filling ∧ judge I w t = .verified := by
  cases h with
  | internal hv hj => exact ⟨hv, hj⟩

/-- Rechecking constructs the matching validity judgment (Ringer et al. p7). -/
theorem recheck_valid {D : CalculusData} {E V : Type} (value : D.Tm → V)
    {registry : RepairObjects.Registry D E} (hr : registry.Sound)
    {n : Nat} {w : World E} {c : Candidate D} {cost : Nat}
    {ev : RepairObjects.TransportEvidence D E}
    (h : recheck registry n w c cost = .ok (.rechecked ev)) :
    Valid ev.correspondence.target w value (.rechecked ev) :=
  .rechecked rfl (recheck_sound hr h)

end Nanodregg.Lang.Contextual.TransportKinds
