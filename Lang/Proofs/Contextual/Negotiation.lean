/-
# Lang.Proofs.Contextual.Negotiation — the integration experiment (lane PROTOCOL)

The proposal's document 3 first integration experiment: two parties negotiate a ONE-USE capability
with ALTERNATIVE providers, a DEADLINE and a CANCELLATION path. The open protocol
(`Negotiation.template`: reserve the deposit, then a provider hole the buyer (`.me`) chooses) is judged once, under
hypotheses (`Γ₀`: both providers' authority, the deadline); each candidate (`plan p1`, `plan p2`,
`cancelPlan`) is a filling checked against the hole's interface.
What stays here: the open protocol judged and filled, the cancellation path
(`cancel_path_refunds_obligation`), the re-plan guard's teeth on a lost reply and an answered call
(`lost_reply_blocks_replan`,
`answered_blocks_replan`, `guard_stricter_than_wf`, `guarded_replan_after_dispatch_is_noop`)
against the free re-plan before dispatch (`replan_before_dispatch`). The scalar matchers and the
private Negotiation `World` (with its update, revocation, representation, replay, deadline and
shared-parameter theorems) went with PROT-6, replaced by Std.offer's deployed fuse
(`Lang/StdOffer.lean`). The private delivery model (`External`, `Internal`, `Consistent`,
`internal_once_not_external_once`, `exactly_once_needs_reply_and_dedupe`) and
`lost_reply_keeps_obligation` went with PROT-5: the deployed objects state the failures
(`Lang.Proofs.Contextual.Failures`: `submit_at_most_once`, `lost_ask_keeps_obligation`,
`lost_reply_policy`).
-/
import Lang.Proofs.Contextual.Protocol

namespace Nanodregg.Lang.Contextual.Protocol.Negotiation

/-! ## The open protocol is judged; every candidate fills the hole -/

/-- The template is judged: `Ω; Γ₀; [cap] ⊢ template : Protocol(idle, True) ⊣ Φ₀`. -/
theorem template_hasProt : HasProt spec Ω Γ₀ (fun _ _ => True) Φ₀ Δ₀ template :=
  .call (S := sig) Op.reserve _ rfl (by simp [spec]) (by simp [spec, Φ₀])
    fun _ => .hole () iface rfl rfl (by simp [iface, Γ₀]) (SubBag.refl _) (fun _ _ _ => trivial)
      (by simp [iface, Φ₀])

/-- Each provider's plan satisfies the hole's interface (spends the capability once, uses that
provider's authority and the deadline, owes that provider's payment). -/
theorem plan_fills (p : Provider) : Fills spec Ω iface (plan p) := by
  refine ⟨.spend (S := sig) (Op.commit p) _ .cap rfl (by simp [iface]) ?_ ?_
    fun _ => .ret _ trivial, trivial⟩
  · cases p <;> simp [spec, iface]
  · cases p <;> simp [spec, iface]

/-- The cancellation path satisfies the hole's interface. -/
theorem cancel_fills : Fills spec Ω iface cancelPlan :=
  ⟨.call (S := sig) Op.cancel _ rfl (by simp [spec]) (by simp [spec, iface])
    fun _ => .ret _ trivial, trivial⟩

theorem choose_ok {f : P .reserved} (hf : Fills spec Ω iface f) : SubstOK spec Ω (choose f) := by
  intro i h g hs
  cases i with
  | idle => exact nomatch h
  | done => exact nomatch h
  | reserved =>
    cases h
    cases hs
    exact ⟨iface, rfl, rfl, hf⟩

/-- Family 1, instance: every candidate's instantiation is judged at the template's judgment. -/
theorem instantiations_hasProt :
    (∀ p, HasProt spec Ω Γ₀ (fun _ _ => True) Φ₀ Δ₀ (fill Ω (choose (plan p)) template)) ∧
      HasProt spec Ω Γ₀ (fun _ _ => True) Φ₀ Δ₀ (fill Ω (choose cancelPlan) template) :=
  ⟨fun p => fill_preserves_hasProt (choose_ok (plan_fills p)) template_hasProt,
    fill_preserves_hasProt (choose_ok cancel_fills) template_hasProt⟩

/-- Family 2, instance: running the instantiation against a delivering provider is running the
template with the choice in the environment; both compute the same outcome. -/
theorem interpret_instance :
    interpret (env true) (subst (choose (plan .p1)) template) 0 =
        interpretUnder (env true) (choose (plan .p1)) template 0 ∧
      (match interpret (env true) (subst (choose (plan .p1)) template) 0 with
        | .done j a n => decide (j = .done) && a && decide (n = 2)
        | .stuck _ _ _ => false) = true :=
  ⟨by rw [interpret_fill], rfl⟩

/-- The open protocol has exactly one hole, the provider; every instantiation has none. -/
theorem holes_instance :
    (holes finite template).length = 1 ∧ Occurs template .reserved () ∧
      (∀ p, holes finite (fill Ω (choose (plan p)) template) = []) ∧
      holes finite (fill Ω (choose cancelPlan) template) = [] := by
  refine ⟨rfl, (mem_holes_iff finite template .reserved ()).mp
      (by simp [holes, template, finite]; exact ⟨rfl, HEq.rfl⟩),
    fun p => ?_, rfl⟩
  cases p <;> rfl

/-! ## The cancellation path -/

/-- **The cancellation path refunds**: every complete run of the plan with the cancellation
chosen establishes exactly the deposit and its refund, and no payment. -/
theorem cancel_path_refunds_obligation {t : Trace sig} {j : Phase} {a : Res j}
    (h : Runs (fill Ω (choose cancelPlan) template) t j a) :
    established spec t = [.holdDeposit, .refund] := by
  change Runs (Prot.call (S := sig) Op.reserve fun _ => cancelPlan) t j a at h
  cases h with
  | call r h =>
    cases h with
    | call r' h =>
      cases h
      rfl

/-- The contrast: every complete run with `p` chosen establishes the deposit and `p`'s payment,
and no refund. -/
theorem commit_path_pays (p : Provider) {t : Trace sig} {j : Phase} {a : Res j}
    (h : Runs (fill Ω (choose (plan p)) template) t j a) :
    established spec t = [.holdDeposit, .pay p] := by
  change Runs (Prot.call (S := sig) Op.reserve fun _ => plan p) t j a at h
  cases h with
  | call r h =>
    cases h with
    | call r' h =>
      cases h
      rfl

/-! ## The lost reply -/

theorem reach_reserved (f : P .reserved) :
    Reach (fill Ω (choose f) template) [reserved] ⟨Phase.reserved, f⟩ :=
  Reach.call (S := sig) (op := Op.reserve) (k := fun _ => f) () (Reach.here _)

theorem reach_hole : Reach template [reserved] ⟨Phase.reserved, .hole ()⟩ :=
  Reach.call (S := sig) (op := Op.reserve)
    (k := fun _ => Prot.hole (S := sig) (Hole := HoleN) (A := Res) (i := Phase.reserved) ()) () (Reach.here _)

theorem started_lost (p : Provider) : Started (fill Ω (choose (plan p)) template) (lost p) :=
  Started.uncertain (S := sig) (k := fun ok => .ret ok) (reach_reserved (plan p))

theorem dispatched_lost (p : Provider) : Dispatched template (lost p) .reserved () :=
  ⟨[reserved], [], rfl, reach_hole, .inr rfl⟩

/-- With the commitment to `p1` in flight, neither the other provider's plan nor the cancellation
has that history. -/
theorem lost_reply_not_started :
    ¬ Started (fill Ω (choose (plan .p2)) template) (lost .p1) ∧
      ¬ Started (fill Ω (choose cancelPlan) template) (lost .p1) := by
  constructor
  · intro h
    obtain ⟨R, hr, hc⟩ := started_some_iff.mp h
    change Reach (Prot.call (S := sig) Op.reserve fun _ => plan .p2) [reserved] R at hr
    cases hr with
    | call r hr =>
      cases hr
      cases hc
  · intro h
    obtain ⟨R, hr, hc⟩ := started_some_iff.mp h
    change Reach (Prot.call (S := sig) Op.reserve fun _ => cancelPlan) [reserved] R at hr
    cases hr with
    | call r hr =>
      cases hr
      cases hc

/-- **Uncertain is not a license to re-plan**: with the commitment to `p1` in flight, the guard
`Replan` refuses switching to `p2` or to the cancellation, and dropping the guard would produce an
object that is not well-formed (its history is no history of the new protocol). The guard is
SUFFICIENT (`Open.resubst_wf`); it is also STRICTER than well-formedness needs
(`guard_stricter_than_wf`). -/
theorem lost_reply_blocks_replan :
    ¬ (obj (plan .p1) (lost .p1)).Replan (choose (plan .p2)) ∧
      ¬ ((obj (plan .p1) (lost .p1)).replan (choose (plan .p2))).WF spec ∧
      ¬ (obj (plan .p1) (lost .p1)).Replan (choose cancelPlan) ∧
      ¬ ((obj (plan .p1) (lost .p1)).replan (choose cancelPlan)).WF spec := by
  refine ⟨fun g => ?_, fun hw => lost_reply_not_started.1 hw.started,
    fun g => ?_, fun hw => lost_reply_not_started.2 hw.started⟩
  · have := g .reserved () (dispatched_lost .p1)
    simp [obj, Subst.mine, Ω, iface, choose, plan] at this
    obtain ⟨h, _⟩ := this
    injection h with h
    cases h
  · have := g .reserved () (dispatched_lost .p1)
    simp [obj, Subst.mine, Ω, iface, choose, plan, cancelPlan] at this

/-- The provider hole counts as entered once the commitment is ANSWERED too. -/
theorem dispatched_answered (p : Provider) (b : Bool) :
    Dispatched template (answeredH p b) .reserved () :=
  ⟨[reserved], [⟨.reserved, Op.commit p, b⟩], rfl, reach_hole, .inl (by simp)⟩

/-- **The answered half**: after the commitment to `p1` is answered (the history extends past the
hole by a performed call), the object is well-formed; the guard refuses switching to `p2`, and
dropping it fails well-formedness. -/
theorem answered_blocks_replan (b : Bool) :
    (obj (plan .p1) (answeredH .p1 b)).WF spec ∧
      ¬ (obj (plan .p1) (answeredH .p1 b)).Replan (choose (plan .p2)) ∧
      ¬ ((obj (plan .p1) (answeredH .p1 b)).replan (choose (plan .p2))).WF spec := by
  refine ⟨⟨template_hasProt, choose_ok (plan_fills .p1), ?_⟩, fun g => ?_, fun hw => ?_⟩
  · have h2 : Reach (plan .p1) [⟨.reserved, Op.commit .p1, b⟩] ⟨Phase.done, .ret b⟩ :=
      Reach.call (S := sig) (op := Op.commit .p1) (k := fun ok => Prot.ret (S := sig) (Hole := HoleN)
        (A := Res) (i := Phase.done) ok) b (Reach.here _)
    exact Started.settled (reach_append (reach_reserved (plan .p1)) h2)
  · have := g .reserved () (dispatched_answered .p1 b)
    simp [obj, Subst.mine, Ω, iface, choose, plan] at this
    obtain ⟨h, _⟩ := this
    injection h with h
    cases h
  · have h := hw.started
    change Started (Prot.call (S := sig) Op.reserve fun _ => plan .p2) (answeredH .p1 b) at h
    cases h with
    | settled hr =>
      cases hr with
      | call r hr => cases hr

theorem planFlip_fills (p : Provider) : Fills spec Ω iface (planFlip p) := by
  refine ⟨.spend (S := sig) (Op.commit p) _ .cap rfl (by simp [iface]) ?_ ?_
    fun _ => .ret _ trivial, trivial⟩
  · cases p <;> simp [spec, iface]
  · cases p <;> simp [spec, iface]

/-- **The guard is stricter than well-formedness**: re-planning the in-flight `p1` commitment to
`planFlip p1` (the SAME first call, a different continuation) yields a well-formed object (the
history is still a history of it), yet `Replan` refuses it, because the guard compares fillings,
not the parts the history has performed. -/
theorem guard_stricter_than_wf :
    ((obj (plan .p1) (lost .p1)).replan (choose (planFlip .p1))).WF spec ∧
      ¬ (obj (plan .p1) (lost .p1)).Replan (choose (planFlip .p1)) := by
  refine ⟨⟨template_hasProt, choose_ok (planFlip_fills .p1),
    Started.uncertain (S := sig) (k := fun ok => .ret (!ok)) (reach_reserved (planFlip .p1))⟩,
    fun g => ?_⟩
  have := g .reserved () (dispatched_lost .p1)
  simp [obj, Subst.mine, Ω, iface, choose, plan, planFlip] at this
  have := congrFun this true
  simp at this

/-- So every GUARDED re-plan after the dispatch leaves the current protocol exactly as it was. -/
theorem guarded_replan_after_dispatch_is_noop (p : Provider) (σ' : Subst sig HoleN Res)
    (g : (obj (plan p) (lost p)).Replan σ') :
    ((obj (plan p) (lost p)).replan σ').current = (obj (plan p) (lost p)).current := by
  have e : σ'.mine Ω Phase.reserved () = (choose (plan p)).mine Ω Phase.reserved () :=
    g .reserved () (dispatched_lost p)
  show Prot.call (S := sig) Op.reserve (fun _ => subst (σ'.mine Ω) (.hole (i := Phase.reserved) ())) =
    Prot.call (S := sig) Op.reserve (fun _ => subst ((choose (plan p)).mine Ω) (.hole (i := Phase.reserved) ()))
  congr 1
  funext x
  have e' : σ'.mine Ω (sig.next Op.reserve x) () =
      (choose (plan p)).mine Ω (sig.next Op.reserve x) () := e
  simp only [subst]
  rw [e']

/-- **Before dispatch, re-planning is a free substitution**: reserved but nothing dispatched, the
provider hole is not entered; the object re-planned from `p1` to `p2` (or to the cancellation) is
well-formed with the same history. -/
theorem replan_before_dispatch (f : P .reserved) (hf : Fills spec Ω iface f) :
    ¬ Dispatched template H₀ .reserved () ∧
      (obj (plan .p1) H₀).Replan (choose f) ∧ ((obj (plan .p1) H₀).replan (choose f)).WF spec ∧
        ((obj (plan .p1) H₀).replan (choose f)).hist = H₀ := by
  have hnd : ∀ j h, ¬ Dispatched template H₀ j h := by
    rintro j h ⟨t₁, t₂, ht, hr, hne⟩
    cases t₁ with
    | nil => cases hr
    | cons e t₁ =>
      simp only [H₀, List.cons_append, List.cons.injEq] at ht
      obtain ⟨rfl, ht⟩ := ht
      have h1 : t₁ = [] := (List.append_eq_nil_iff.mp ht.symm).1
      have h2 : t₂ = [] := (List.append_eq_nil_iff.mp ht.symm).2
      subst h1 h2
      rcases hne with hne | hne
      · exact hne rfl
      · cases hne
  have hwf : (obj (plan .p1) H₀).WF spec :=
    ⟨template_hasProt, choose_ok (plan_fills .p1), Started.settled (reach_reserved (plan .p1))⟩
  refine ⟨hnd _ _, fun j h hd => (hnd j h hd).elim, ?_⟩
  obtain ⟨hw, hh, _⟩ := Open.resubst_wf hwf (choose_ok hf) (fun j h hd => (hnd j h hd).elim)
  exact ⟨hw, hh⟩

end Nanodregg.Lang.Contextual.Protocol.Negotiation
