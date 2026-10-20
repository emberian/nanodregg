/- First-class repair laws: composition, residuals, selection and transport. -/
import Lang.Contextual.RepairObjects
import Lang.Proofs.Contextual.History

namespace Nanodregg.Lang.Contextual.RepairObjects

variable {D : CalculusData} {E : Type}

/-- The implementation must restore coherent judgments and conserve the retained analysis
problem at EVERY world, not merely make the current statuses agree with themselves. -/
structure Repair.Sound {w v : World E} {e : Change E w v} (r : Repair D e) : Prop where
  coherent : ∀ st, Coherent w st.closure → Coherent v (r.run st).state.closure
  problem : ∀ st z, analyze z (r.run st).state.closure = analyze z st.closure

theorem analyze_eq (w : World E) (cl : Closure D E) :
    analyze w cl = cl.tpl.Ω.map (fun I => (cl.slot I.name).cands.map (judge I w)) := by
  unfold analyze observe
  apply List.map_congr_left
  intro I hI
  simp [fromScratch, find_name_self cl.tpl.names hI, List.map_map]

theorem coherent_observe {w : World E} {cl : Closure D E} (hc : Coherent w cl) :
    observe cl = analyze w cl := by
  rw [analyze_eq]
  unfold observe
  apply List.map_congr_left
  intro I hI
  exact List.map_congr_left (hc I hI)

theorem repair_preserves_problem (w z : World E) (e : Edit E) (cl : Closure D E) :
    analyze z (repair w e cl).1 = analyze z cl := by
  rw [analyze_eq, analyze_eq]
  apply List.map_congr_left
  intro I hI
  rw [repair_slot (w := w) (e := e) (cl := cl) hI, repairHole_cands, repairCands_map, List.map_map]
  apply List.map_congr_left
  intro c _
  dsimp
  split <;> rfl

theorem atomic_sound (w : World E) (e : Edit E) :
    (Repair.atomic (D := D) w e).Sound :=
  ⟨fun _ hc => repair_coherent hc, fun _ z => repair_preserves_problem w z e _⟩

theorem identity_sound (w : World E) : (Repair.identity (D := D) w).Sound :=
  ⟨fun _ hc => hc, fun _ _ => rfl⟩

/-- Composition of sound repair values is sound; no hypothesis is added to landed theorems. -/
theorem compose_sound {w v z : World E} {e : Change E w v} {f : Change E v z}
    {r : Repair D e} {s : Repair D f} (hr : r.Sound) (hs : s.Sound) :
    (r.compose s).Sound := by
  constructor
  · intro st hc
    exact hs.coherent _ (hr.coherent st hc)
  · intro st q
    exact (hs.problem _ q).trans (hr.problem st q)

theorem ofChange_sound {w v : World E} (e : Change E w v) :
    (Repair.ofChange (D := D) e).Sound := by
  induction e with
  | stay w => exact identity_sound w
  | edit w e => exact atomic_sound w e
  | «then» e f ih₁ ih₂ => exact compose_sound ih₁ ih₂

/-- Repair correctness remains distinct from soundness and locality: composed execution
equals a single from-scratch analysis of the ORIGINAL retained problem at the final world. -/
theorem repair_correctness {w v : World E} {e : Change E w v} {r : Repair D e}
    (hr : r.Sound) (st : State D w) (hc : Coherent w st.closure) :
    observe (r.run st).state.closure = analyze v st.closure :=
  (coherent_observe (hr.coherent st hc)).trans (hr.problem st v)

/-- Intermediate residual obligations survive composition even if later edits settle them. -/
theorem compose_keeps_obligation {w v z : World E} {e : Change E w v} {f : Change E v z}
    (r : Repair D e) (s : Repair D f) (st : State D w) {res : Residual D E}
    (hres : res ∈ (r.run st).residuals) {o : Obligation} (ho : o ∈ res.obligations) :
    o ∈ ((r.compose s).run st).residuals.flatMap Residual.obligations := by
  apply List.mem_flatMap.2
  exact ⟨res, List.mem_append_left _ hres, ho⟩

/-- Locality is inherited from the exact work log, rather than deduced from correctness. -/
theorem atomic_locality {w : World E} {e : Edit E} (st : State D w)
    {I : Iface D E} (hI : I ∈ st.closure.tpl.Ω) (k : Nat) :
    (I.name, k) ∈ ((Repair.atomic w e).run st).inspected ↔
      ∃ c, (st.closure.slot I.name).cands[k]? = some c ∧ touches e I c = true :=
  repair_rejudged_eq_touched hI k

/-- The retained residual really resumes with a coherent final-world judgment. -/
theorem resume_coherent (r : Residual D E) (e : Edit E) (hc : Coherent r.world r.closure) :
    Coherent (e.apply r.world) (r.resume e).state.closure :=
  repair_coherent hc

theorem choose_sound (policy : Policy D) (I : Iface D E) (w : World E) :
    ∀ (cs : List (Candidate D)) (n : Nat) {c : Candidate D} {i : Nat},
      choose policy I w cs n = some (c, i) →
      c ∈ cs ∧ policy.eligible c = true ∧ judge I w c = .verified
  | [], _, _, _, h => by simp [choose] at h
  | d :: ds, n, c, i, h => by
    unfold choose at h
    dsimp only at h
    split at h
    · rename_i hd
      have hd' : policy.eligible d = true ∧ judge I w d = .verified := by
        simpa [isVerified_iff] using hd
      split at h
      · cases h; exact ⟨List.mem_cons_self, hd'⟩
      · rename_i x j hx
        split at h
        · cases h; exact ⟨List.mem_cons_self, hd'⟩
        · cases h
          obtain ⟨hm, he, hv⟩ := choose_sound policy I w ds (n + 1) hx
          exact ⟨List.mem_cons_of_mem _ hm, he, hv⟩
    · obtain ⟨hm, he, hv⟩ := choose_sound policy I w ds (n + 1) h
      exact ⟨List.mem_cons_of_mem _ hm, he, hv⟩

theorem choose_none (policy : Policy D) (I : Iface D E) (w : World E) :
    ∀ (cs : List (Candidate D)) (n : Nat), choose policy I w cs n = none →
      ∀ c ∈ cs, policy.eligible c = true → judge I w c ≠ .verified
  | [], _, _, _, hm, _, _ => by cases hm
  | d :: ds, n, h, c, hm, he, hv => by
    unfold choose at h
    dsimp only at h
    split at h
    · split at h
      · cases h
      · split at h <;> cases h
    · rename_i hd
      rcases List.mem_cons.1 hm with rfl | hm
      · simp [he, hv, isVerified] at hd
      · exact choose_none policy I w ds (n + 1) h c hm he hv

/-- Regardless of policy, successful selection passes the original authority/history gate. -/
theorem select_authorized {policy : Policy D} {w : World E} {p u i : Nat}
    {cl cl' : Closure D E} (h : select policy w p u cl = .ok (cl', i)) :
    Nanodregg.Lang.Contextual.select w p u i cl = .ok cl' := by
  unfold select at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · rename_i hbase
        cases h
        exact hbase

/-- Conditional soundness of a policy-selected filling follows from the existing judge,
including hard cost bounds: preference cannot make an unavailable candidate admissible. -/
theorem select_sound {policy : Policy D} {w : World E} {p u i : Nat}
    {cl cl' : Closure D E} (h : select policy w p u cl = .ok (cl', i)) :
    ∃ I c, cl.find u = some I ∧ p = I.chooser ∧ (cl.slot u).accepted = false ∧
      (cl.slot u).cands[i]? = some c ∧ judge I w c = .verified ∧
      (∀ t ∈ effSupports I c, w.live t = true) ∧ cl'.sigma u = some c.filling :=
  select_requires_available (select_authorized h)

/-- An equivalence of checker-accepted fillings, not merely a function that finds replacements. -/
structure Correspondence.Checked (q : Correspondence D E) : Prop where
  forward : ∀ t, D.check q.source.ctx t q.source.ty = true →
    D.check q.target.ctx (q.forward t) q.target.ty = true
  backward : ∀ t, D.check q.target.ctx t q.target.ty = true →
    D.check q.source.ctx (q.backward t) q.source.ty = true
  leftInverse : ∀ t, D.check q.source.ctx t q.source.ty = true →
    q.backward (q.forward t) = t
  rightInverse : ∀ t, D.check q.target.ctx t q.target.ty = true →
    q.forward (q.backward t) = t

/-- Certificate acceptance is accountable to a theorem about every registry entry. -/
def Registry.Sound (registry : Registry D E) : Prop :=
  ∀ n q, registry n = some q → q.Checked

/-- A successful transport names the checked equivalence, relates the actual fillings, and
rechecks destination admission. Source typing alone cannot satisfy the destination guard. -/
theorem transport_sound {registry : Registry D E} (hreg : registry.Sound)
    {n : Nat} {w : World E} {c : Candidate D} {cost : Nat} {ev : TransportEvidence D E}
    (h : transport registry n w c cost = .ok (.transported ev)) :
    ev.correspondence.Checked ∧ ev.original = c ∧
      ev.image.filling = ev.correspondence.forward c.filling ∧
      ev.correspondence.backward ev.image.filling = c.filling ∧
      judge ev.correspondence.target w ev.image = .verified ∧
      (∀ t ∈ effSupports ev.correspondence.source c,
        t ∈ effSupports ev.correspondence.target ev.image) ∧
      ev.certificate = n ∧ registry ev.certificate = some ev.correspondence := by
  unfold transport at h
  dsimp only at h
  split at h
  · cases h
  · rename_i q hq
    split at h
    · cases h
    · rename_i hsrc
      have ht : D.check q.source.ctx c.filling q.source.ty = true := by
        simpa using hsrc
      split at h
      · rename_i hv
        cases h
        refine ⟨hreg n q hq, rfl, rfl, (hreg n q hq).leftInverse _ ht, hv, ?_, rfl, hq⟩
        intro t hm
        exact List.mem_append_left _ hm
      · cases h

/-- Checked equivalence carries a derivation to the changed proposition independently of
whether this world's guards/supports currently permit selecting the result. -/
theorem transport_typing {HasTy : List (HoleDecl D.Ctx D.Ty) → D.Ctx → D.Tm → D.Ty → Prop}
    (laws : CalculusLaws D HasTy) {q : Correspondence D E} (hq : q.Checked)
    {t : D.Tm} (ht : HasTy [] q.source.ctx t q.source.ty) :
    HasTy [] q.target.ctx (q.forward t) q.target.ty :=
  laws.check_sound (hq.forward t (laws.check_complete ht))

/-- The sixth outcome cannot be mistaken for an offered replacement. -/
theorem transported_not_replacement (ev : TransportEvidence D E) (u j : Nat) (t : D.Tm) :
    Outcome.transported ev ≠ .existing (.replacement u j t) := by
  intro h
  cases h


/-- The choice index refers to the actual retained candidate, not merely an equal-cost one. -/
theorem choose_index (policy : Policy D) (I : Iface D E) (w : World E) :
    ∀ (cs : List (Candidate D)) (n : Nat) {c : Candidate D} {i : Nat},
      choose policy I w cs n = some (c, i) →
      n ≤ i ∧ cs[i - n]? = some c
  | [], _, _, _, h => by simp [choose] at h
  | d :: ds, n, c, i, h => by
    have tail : choose policy I w ds (n + 1) = some (c, i) →
        n ≤ i ∧ (d :: ds)[i - n]? = some c := by
      intro ht
      obtain ⟨hle, hg⟩ := choose_index policy I w ds (n + 1) ht
      refine ⟨by omega, ?_⟩
      have hi : i - n = (i - (n + 1)) + 1 := by omega
      rw [hi]
      exact hg
    unfold choose at h
    dsimp only at h
    split at h
    · split at h
      · cases h; simp
      · rename_i x j hx
        split at h
        · cases h; simp
        · cases h; exact tail hx
    · exact tail h

/-- Preference really minimizes the policy's cost over all eligible, currently verified
candidates. Admissibility remains independent of this ordering. -/
theorem choose_minimal (policy : Policy D) (I : Iface D E) (w : World E) :
    ∀ (cs : List (Candidate D)) (n : Nat) {c : Candidate D} {i : Nat},
      choose policy I w cs n = some (c, i) →
      ∀ d ∈ cs, policy.eligible d = true → judge I w d = .verified →
        policy.cost c ≤ policy.cost d
  | [], _, _, _, h => by simp [choose] at h
  | a :: as, n, c, i, h => by
    unfold choose at h
    dsimp only at h
    split at h
    · split at h
      · rename_i hn
        cases h
        intro d hd he hv
        rcases List.mem_cons.1 hd with rfl | hd
        · exact Nat.le_refl _
        · exact False.elim (choose_none policy I w as (n + 1) hn d hd he hv)
      · rename_i b j hb
        split at h
        · rename_i hab
          cases h
          intro d hd he hv
          rcases List.mem_cons.1 hd with rfl | hd
          · exact Nat.le_refl _
          · exact Nat.le_trans hab (choose_minimal policy I w as (n + 1) hb d hd he hv)
        · rename_i hab
          cases h
          intro d hd he hv
          rcases List.mem_cons.1 hd with rfl | hd
          · omega
          · exact choose_minimal policy I w as (n + 1) hb d hd he hv
    · rename_i ha
      intro d hd he hv
      rcases List.mem_cons.1 hd with rfl | hd
      · simp [he, hv, isVerified] at ha
      · exact choose_minimal policy I w as (n + 1) h d hd he hv

/-- Conditional soundness remains its own result, over a repaired candidate rather than
over the definition of the observation used for repair correctness. -/
theorem conditional_soundness {HasTy : List (HoleDecl D.Ctx D.Ty) → D.Ctx → D.Tm → D.Ty → Prop}
    (laws : CalculusLaws D HasTy) {w v : World E} {e : Change E w v} {r : Repair D e}
    (hr : r.Sound) (st : State D w) (hc : Coherent w st.closure)
    {I : Iface D E} (hI : I ∈ (r.run st).state.closure.tpl.Ω)
    {c : Candidate D} (hcm : c ∈ ((r.run st).state.closure.slot I.name).cands)
    (hv : c.status = .verified) :
    HasTy [] I.ctx c.filling I.ty ∧ I.guard v.env c.filling = true ∧
      (∀ b ∈ c.blockers, v.live b = false) ∧
      (∀ t ∈ effSupports I c, v.live t = true) ∧ c.cost ≤ I.budget :=
  Nanodregg.Lang.Contextual.conditional_soundness laws (hr.coherent st hc) hI hcm hv

/-- Adding transport offers keeps the repair's state semantics. Admission of each offer
is separately covered by transport_sound and the registry's checked-equivalence law. -/
theorem withTransport_sound {w v : World E} {e : Change E w v} {r : Repair D e}
    (hr : r.Sound) (registry : Registry D E) (n : Nat) (c : Candidate D) (cost : Nat) :
    (r.withTransport registry n c cost).Sound := by
  constructor
  · intro st hc
    unfold Repair.withTransport
    dsimp only
    split <;> exact hr.coherent st hc
  · intro st z
    unfold Repair.withTransport
    dsimp only
    split <;> exact hr.problem st z


/-- The selected retained index satisfies the policy and is cheapest among the candidates
which satisfy that policy and the independent current-world judgment. -/
theorem select_preference {policy : Policy D} {w : World E} {p u i : Nat}
    {cl cl' : Closure D E} (h : select policy w p u cl = .ok (cl', i)) :
    ∃ I c, cl.find u = some I ∧ (cl.slot u).cands[i]? = some c ∧
      policy.eligible c = true ∧
      ∀ d ∈ (cl.slot u).cands, policy.eligible d = true → judge I w d = .verified →
        policy.cost c ≤ policy.cost d := by
  unfold select at h
  split at h
  · cases h
  · rename_i I hI
    split at h
    · cases h
    · rename_i c j hj
      split at h
      · cases h
      · cases h
        have hg := (choose_index policy I w _ 0 hj).2
        exact ⟨I, c, hI, by simpa using hg, (choose_sound policy I w _ 0 hj).2.1,
          choose_minimal policy I w _ 0 hj⟩

end Nanodregg.Lang.Contextual.RepairObjects
