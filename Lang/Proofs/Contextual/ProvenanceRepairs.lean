/- Reverse provenance's two directions, through actual Edit.apply/applyAll. -/
import Lang.Contextual.ProvenanceRepairs
import Lang.Proofs.Contextual.Provenance

namespace Nanodregg.Lang.Contextual.P9

variable {D : CalculusData} {E : Type}

/-- Grädel–Tannen Prop16 p23: semantics of a set of updates, even for repeated input tokens. -/
theorem tokenEdits_live (w v : World E) (ts : List Token) (t : Token) :
    (applyAll (tokenEdits w ts) v).live t =
      if t ∈ ts then !w.live t else v.live t := by
  induction ts generalizing v with
  | nil => simp [tokenEdits, applyAll]
  | cons a ts ih =>
    simp only [tokenEdits, List.map_cons, applyAll]
    rw [show List.map (fun t => if w.live t then Edit.withdraw t else Edit.assert t) ts =
      tokenEdits w ts from rfl, ih]
    by_cases ht : t ∈ ts
    · simp [ht]
    · cases ha : w.live a <;> by_cases he : t = a <;>
        simp [ht, he, ha, Edit.apply, World.set]

/-- Prop16 p23: token-only repairs preserve the environment they were computed for. -/
theorem tokenEdits_env (w v : World E) (ts : List Token) :
    (applyAll (tokenEdits w ts) v).env = v.env := by
  induction ts generalizing v with
  | nil => rfl
  | cons a ts ih =>
    cases ha : w.live a <;>
      simpa [tokenEdits, applyAll, ha, Edit.apply, World.set] using
        ih ((if w.live a then Edit.withdraw a else Edit.assert a).apply v)

/-- Prop16 p23: computed changes are exactly the currently false signed literals. -/
theorem mem_changes {w : World E} {m : Monomial D} {t : Token} :
    t ∈ changes w m ↔
      (t ∈ m.supports ∧ w.live t = false) ∨ (t ∈ m.blockers ∧ w.live t = true) := by
  simp [changes]

/-- Prop16 p23: correcting those literals makes the product true; consistency is
essential because one token cannot simultaneously become live and absent. -/
theorem changes_satisfy {I : Iface D E} {w : World E} {m : Monomial D}
    (he : m.envOK I w.env = true) (hc : m.consistent = true) :
    m.eval I (applyAll (tokenEdits w (changes w m)) w) = true := by
  have hd : ∀ t ∈ m.supports, t ∉ m.blockers := by
    simpa [Monomial.consistent] using hc
  simp only [Monomial.eval, Bool.and_eq_true, List.all_eq_true]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · simpa [Monomial.envOK, tokenEdits_env] using he
  · intro t ht
    rw [tokenEdits_live]
    cases hl : w.live t
    · have hm := mem_changes.mpr (Or.inl ⟨ht, hl⟩)
      simp [hm]
    · have hm : t ∉ changes w m := by simp [mem_changes, hl, hd t ht]
      simp [hm]
  · intro t ht
    rw [tokenEdits_live]
    cases hl : w.live t
    · have hp : t ∉ m.supports := fun hp => hd t hp ht
      have hm : t ∉ changes w m := by simp [mem_changes, hl, hp]
      simp [hm]
    · have hm := mem_changes.mpr (Or.inr ⟨ht, hl⟩)
      simp [hm]

/-- Grädel–Tannen Prop16 p23: every repairable monomial computes an actual verifying
sequence of primitive edits, with a retained candidate as witness. -/
theorem repairs_of_provenance {I : Iface D E} {w : World E} {cs : List (Candidate D)}
    {m : Monomial D} (hm : m ∈ repairTerms I w.env cs) :
    ∃ c ∈ cs, judge I (applyAll (tokenEdits w (changes w m)) w) c = .verified := by
  obtain ⟨hm, he⟩ := List.mem_filter.mp hm
  have hh : m.envOK I w.env = true ∧ m.consistent = true := by simpa using he
  exact provenance_iff.mpr ⟨m, hm, changes_satisfy hh.1 hh.2⟩

/-- Prop16 p23: every successful update contains the edits required by its witnessing product. -/
theorem changes_necessary {I : Iface D E} {w : World E} {m : Monomial D} {ts : List Token}
    (h : m.eval I (applyAll (tokenEdits w ts) w) = true) :
    ∀ t ∈ changes w m, t ∈ ts := by
  simp only [Monomial.eval, Bool.and_eq_true, List.all_eq_true] at h
  intro t ht
  by_cases hn : t ∈ ts
  · exact hn
  exfalso
  rcases mem_changes.mp ht with ⟨hp, hl⟩ | ⟨hp, hl⟩
  · have hv := h.1.2 t hp
    simp [tokenEdits_live, hn, hl] at hv
  · have hv := h.2 t hp
    simp [tokenEdits_live, hn, hl] at hv

/-- Prop16 p23: converse for every repair, not only a preselected candidate.
The resulting monomial computes a subrepair of the supplied update. -/
theorem provenance_of_repair {I : Iface D E} {w : World E} {cs : List (Candidate D)}
    {ts : List Token}
    (h : ∃ c ∈ cs, judge I (applyAll (tokenEdits w ts) w) c = .verified) :
    ∃ m ∈ repairTerms I w.env cs, ∀ t ∈ changes w m, t ∈ ts := by
  obtain ⟨m, hm, hv⟩ := provenance_iff.mp h
  have he : m.envOK I w.env = true := by
    have he := hv
    simp only [Monomial.eval, Bool.and_eq_true] at he
    simpa [tokenEdits_env] using he.1.1
  exact ⟨m, List.mem_filter.mpr ⟨hm, by simp [he, eval_consistent hv]⟩,
    changes_necessary hv⟩

/-- Prop16 p23: minimality is inclusion among all successful token updates, not list length. -/
def MinimalRepair (I : Iface D E) (w : World E) (cs : List (Candidate D))
    (ts : List Token) : Prop :=
  (∃ c ∈ cs, judge I (applyAll (tokenEdits w ts) w) c = .verified) ∧
  ∀ us : List Token,
    (∃ c ∈ cs, judge I (applyAll (tokenEdits w us) w) c = .verified) →
    (∀ t ∈ us, t ∈ ts) → ∀ t ∈ ts, t ∈ us

/-- Prop16 p23: every minimal repair equals a monomial's computed edit set.
Equality is set equality: duplicate input entries do not create a second repair. -/
theorem minimal_repairs_of_provenance {I : Iface D E} {w : World E}
    {cs : List (Candidate D)} {ts : List Token} (h : MinimalRepair I w cs ts) :
    ∃ m ∈ repairTerms I w.env cs, ∀ t, t ∈ changes w m ↔ t ∈ ts := by
  obtain ⟨m, hm, hs⟩ := provenance_of_repair h.1
  have hr := h.2 (changes w m) (repairs_of_provenance hm) hs
  exact ⟨m, hm, fun t => ⟨hs t, hr t⟩⟩

/-- Prop16 p23: every returned plan really verifies a retained candidate. -/
theorem repairPlans_sound {I : Iface D E} {w : World E} {cs : List (Candidate D)}
    {ts : List Token} (ht : ts ∈ repairPlans I w cs) :
    ∃ c ∈ cs, judge I (applyAll (tokenEdits w ts) w) c = .verified := by
  obtain ⟨n, hn, rfl⟩ := List.mem_map.mp ht
  obtain ⟨m, hm, rfl⟩ := List.mem_map.mp (minimal_subset hn)
  exact repairs_of_provenance hm

/-- Prop16 p23: every successful update contains one of the COMPUTED repair alternatives. -/
theorem repairPlans_cover {I : Iface D E} {w : World E} {cs : List (Candidate D)}
    {us : List Token}
    (hu : ∃ c ∈ cs, judge I (applyAll (tokenEdits w us) w) c = .verified) :
    ∃ ts ∈ repairPlans I w cs, ∀ t ∈ ts, t ∈ us := by
  obtain ⟨m, hm, hs⟩ := provenance_of_repair hu
  obtain ⟨n, hn, hsub⟩ := minimal_covers
    ((repairTerms I w.env cs).map (planMonomial w)) (List.mem_map.mpr ⟨m, hm, rfl⟩)
  exact ⟨n.supports, List.mem_map.mpr ⟨n, hn, rfl⟩,
    fun t ht => hs t ((subsumes_iff.mp hsub).1 t ht)⟩

/-- de Kleer p145 / Prop16 p23: no computed repair strictly contains another computed repair. -/
theorem repairPlans_antichain {I : Iface D E} {w : World E} {cs : List (Candidate D)}
    {ts us : List Token} (ht : ts ∈ repairPlans I w cs) (hu : us ∈ repairPlans I w cs)
    (hsub : ∀ t ∈ ts, t ∈ us) : ∀ t ∈ us, t ∈ ts := by
  obtain ⟨n, hn, rfl⟩ := List.mem_map.mp ht
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hu
  have hns := minimal_subset hn
  have hks := minimal_subset hk
  obtain ⟨m, _, rfl⟩ := List.mem_map.mp hns
  obtain ⟨q, _, rfl⟩ := List.mem_map.mp hks
  have hnk : (planMonomial w m).subsumes (planMonomial w q) = true :=
    subsumes_iff.mpr ⟨hsub, by simp [planMonomial], by simp [planMonomial]⟩
  exact (subsumes_iff.mp (provenance_minimal _ _ hn _ hk hnk)).1

/-- Grädel–Tannen Prop16 p23: every computed plan is globally inclusion-minimal,
not merely minimal among the list before filtering. -/
theorem repairPlans_minimal {I : Iface D E} {w : World E} {cs : List (Candidate D)}
    {ts : List Token} (ht : ts ∈ repairPlans I w cs) : MinimalRepair I w cs ts := by
  refine ⟨repairPlans_sound ht, ?_⟩
  intro us hu hus
  obtain ⟨vs, hv, hvs⟩ := repairPlans_cover hu
  have hvt : ∀ t ∈ vs, t ∈ ts := fun t hh => hus t (hvs t hh)
  have htv := repairPlans_antichain hv ht hvt
  exact fun t hh => hvs t (htv t hh)

/-- Grädel–Tannen Prop16 p23: every minimal repair appears in the computed answer,
up to order and duplicate token entries. -/
theorem repairPlans_complete {I : Iface D E} {w : World E} {cs : List (Candidate D)}
    {ts : List Token} (ht : MinimalRepair I w cs ts) :
    ∃ us ∈ repairPlans I w cs, ∀ t, t ∈ us ↔ t ∈ ts := by
  obtain ⟨us, hu, hs⟩ := repairPlans_cover ht.1
  have hr := ht.2 us (repairPlans_sound hu) hs
  exact ⟨us, hu, fun t => ⟨hs t, hr t⟩⟩

/-- Grädel–Tannen Prop16 p23, consuming P4's retained residual: every returned plan
is a globally minimal repair of its own saved world and candidate problem. -/
theorem residualRepairPlans_minimal {r : RepairObjects.Residual D E} {u : Nat}
    {plans : List (List Token)} {ts : List Token}
    (hr : residualRepairPlans r u = some plans) (ht : ts ∈ plans) :
    ∃ I, r.closure.find u = some I ∧
      MinimalRepair I r.world (r.closure.slot u).cands ts := by
  unfold residualRepairPlans at hr
  cases hf : r.closure.find u with
  | none => simp [hf] at hr
  | some I =>
    simp only [hf, Option.map_some, Option.some.injEq] at hr
    subst plans
    exact ⟨I, rfl, repairPlans_minimal ht⟩

end Nanodregg.Lang.Contextual.P9
