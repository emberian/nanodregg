/- Guarded contextual closure: Soundness. Moved without statement changes from Closure. -/
import Lang.Proofs.Contextual.Outcomes
import Lang.Proofs.Contextual.Operations

namespace Nanodregg.Lang.Contextual

variable {D : CalculusData} {E : Type}
  {HasTy : List (HoleDecl D.Ctx D.Ty) → D.Ctx → D.Tm → D.Ty → Prop}


/-! ## Conditional soundness -/

/-- **CONDITIONAL SOUNDNESS, per candidate.** In a coherent closure every `verified` candidate
types at its hole, passes the hole's guard in the current environment, has every support live and
no blocker live, and is within budget. -/
theorem conditional_soundness (L : CalculusLaws D HasTy) {w : World E} {cl : Closure D E} (hc : Coherent w cl)
    {I : Iface D E} (hI : I ∈ cl.tpl.Ω) {c : Candidate D} (hcm : c ∈ (cl.slot I.name).cands)
    (hv : c.status = .verified) :
    HasTy [] I.ctx c.filling I.ty ∧ I.guard w.env c.filling = true ∧
      (∀ b ∈ c.blockers, w.live b = false) ∧ (∀ t ∈ effSupports I c, w.live t = true) ∧
      c.cost ≤ I.budget := by
  rw [hc I hI c hcm] at hv
  obtain ⟨h1, h2, h3, h4, h5⟩ := judge_verified_iff.1 hv
  exact ⟨L.check_sound h1, h2, h3, h4, h5⟩

/-- Derivability is the meta-substitution lemma applied to checked selections. -/
theorem derivable_of_wellFilled (L : CalculusLaws D HasTy) {cl : Closure D E}
    (ht : cl.tpl.Typed HasTy) (h : WellFilled cl) : Derivable HasTy cl := by
  unfold Derivable
  apply L.msubst_lemma _ ht
  intro d hd M hM
  obtain ⟨I, hI, rfl⟩ := List.mem_map.1 hd
  simp only [Iface.decl, Closure.sigma, Closure.selectedCand] at hM ⊢
  split at hM
  · rename_i i hsel
    obtain ⟨c, hc, hchk⟩ := h I hI i hsel
    rw [hc] at hM
    simp only [Option.map_some, Option.some.injEq] at hM
    subst hM
    exact L.check_sound hchk
  · simp at hM

/-- **CONDITIONAL SOUNDNESS, for the closure.** A coherent, settled closure is available (every
support of every selection is live) and derivable (the template under `σ` types). -/
theorem conditional_soundness_closure (L : CalculusLaws D HasTy) {w : World E} {cl : Closure D E}
    (ht : cl.tpl.Typed HasTy) (hc : Coherent w cl) (hs : Settled cl) :
    Available w cl ∧ WellFilled cl ∧ Derivable HasTy cl := by
  have hwf : WellFilled cl := by
    intro I hI i hsel
    obtain ⟨c, hci, hv⟩ := hs I hI i hsel
    exact ⟨c, hci, by
      rw [hc I hI c (List.mem_of_getElem? hci)] at hv
      exact (judge_verified_iff.1 hv).1⟩
  refine ⟨?_, hwf, derivable_of_wellFilled L ht hwf⟩
  intro I hI c hsc
  simp only [Closure.selectedCand] at hsc
  split at hsc
  · rename_i i hsel
    obtain ⟨c', hci, hv⟩ := hs I hI i hsel
    rw [hci, Option.some.injEq] at hsc
    subst hsc
    rw [hc I hI c' (List.mem_of_getElem? hci)] at hv
    exact (judge_verified_iff.1 hv).2.2.2.1
  · simp at hsc

/-! ## Invariants preserved by every operation -/

theorem find_eq_of_mem {cl : Closure D E} {u : Nat} {I J : Iface D E} (hf : cl.find u = some J)
    (hI : I ∈ cl.tpl.Ω) (hn : I.name = u) : J = I := by
  rw [← hn, find_self hI] at hf
  exact (Option.some.inj hf).symm

/-- A per-hole property survives an update of the one slot the operation names. -/
theorem update_preserves {P : Iface D E → Slot D → Prop} {cl cl' : Closure D E} {u : Nat}
    {J : Iface D E} {s' : Slot D} (hf : cl.find u = some J) (ht : cl'.tpl = cl.tpl)
    (hs : cl'.slot = cl.update u s') (hold : ∀ I ∈ cl.tpl.Ω, P I (cl.slot I.name))
    (hnew : P J s') : ∀ I ∈ cl'.tpl.Ω, P I (cl'.slot I.name) := by
  intro I hI
  rw [ht] at hI
  rw [hs, update_at]
  split
  · rename_i hn
    rw [← find_eq_of_mem hf hI hn]
    exact hnew
  · exact hold I hI

theorem slotFilled_set {I : Iface D E} {s : Slot D} (h : SlotFilled I s) {i : Nat}
    {c x : Candidate D} (hc : s.cands[i]? = some c) (hx : x.filling = c.filling) :
    SlotFilled I ⟨s.cands.set i x, s.selected, s.accepted⟩ := by
  intro k hk
  obtain ⟨c0, hc0, hchk⟩ := h k hk
  by_cases hik : i = k
  · subst hik
    rw [hc] at hc0
    cases hc0
    refine ⟨x, List.getElem?_set_self (List.getElem?_eq_some_iff.1 hc).1, ?_⟩
    rw [hx]; exact hchk
  · exact ⟨c0, by rw [List.getElem?_set_ne hik]; exact hc0, hchk⟩

theorem repairCands_getElem? {w' : World E} {e : Edit E} {I : Iface D E} {cs : List (Candidate D)}
    {k : Nat} {d : Candidate D} (h : (repairCands w' e I cs)[k]? = some d) :
    ∃ d0, cs[k]? = some d0 ∧ d.filling = d0.filling := by
  rw [repairCands_map, List.getElem?_map] at h
  cases hd : cs[k]? with
  | none => simp [hd] at h
  | some d0 =>
    simp only [hd, Option.map_some, Option.some.injEq] at h
    refine ⟨d0, rfl, ?_⟩
    rw [← h]; split <;> rfl

theorem repairHole_slotFilled {w' : World E} {e : Edit E} {I : Iface D E} {s : Slot D}
    (h : SlotFilled I s) : SlotFilled I (repairHole w' e I s).1 := by
  unfold repairHole
  split
  · exact h
  split
  · rename_i hn
    intro i hi; simp only [hn] at hi; cases hi
  rename_i i hsel
  obtain ⟨c, hc, hchk⟩ := h i hsel
  have fill_ok' : ∀ (k : Nat) (d : Candidate D), (repairCands w' e I s.cands)[k]? = some d →
      ∀ c', (repairCands w' e I s.cands)[i]? = some c' → d.filling = c'.filling →
        D.check I.ctx d.filling I.ty = true := by
    intro k d _ c' hc' hdc
    obtain ⟨c0, hc0, hf0⟩ := repairCands_getElem? hc'
    rw [hc] at hc0; cases hc0
    rw [hdc, hf0]; exact hchk
  intro i' hi'
  simp only at hi' ⊢
  unfold repairSelected at hi'
  split at hi'
  · rename_i hnone
    have hlen : i < s.cands.length := (List.getElem?_eq_some_iff.1 hc).1
    have : i < (repairCands w' e I s.cands).length := by simp [repairCands_map, hlen]
    rw [List.getElem?_eq_none_iff] at hnone
    omega
  rename_i c' hc'
  split at hi'
  · simp only [Option.some.injEq] at hi'
    subst hi'
    exact ⟨c', hc', fill_ok' _ _ hc' c' hc' rfl⟩
  split at hi'
  · simp only [Option.some.injEq] at hi'
    subst hi'
    exact ⟨c', hc', fill_ok' _ _ hc' c' hc' rfl⟩
  unfold reselect at hi'
  split at hi'
  · rename_i d j hf
    simp only [Option.some.injEq] at hi'
    subst hi'
    obtain ⟨hp, -, hget⟩ := findIx_some hf
    simp only [Nat.sub_zero] at hget
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
    exact ⟨d, hget, fill_ok' _ _ hget c' hc' hp.2⟩
  · split at hi' <;>
    · simp only [Option.some.injEq] at hi'
      subst hi'
      exact ⟨c', hc', fill_ok' _ _ hc' c' hc' rfl⟩

theorem repair_wellFilled {w : World E} {e : Edit E} {cl : Closure D E} (h : WellFilled cl) :
    WellFilled (repair w e cl).1 := by
  intro I hI
  have hI' : I ∈ cl.tpl.Ω := hI
  rw [repair_slot hI']
  exact repairHole_slotFilled (h I hI')

theorem propose_wellFilled {w : World E} {u : Nat} {c : Candidate D} {cl : Closure D E}
    {r : Closure D E × Nat} (hw : WellFilled cl) (h : propose w u c cl = .ok r) : WellFilled r.1 := by
  obtain ⟨J, hf, -, ht, -, -, hs⟩ := propose_ok h
  refine update_preserves (P := SlotFilled) hf ht hs hw ?_
  obtain ⟨hJ, rfl⟩ := find_some hf
  intro k hk
  obtain ⟨c0, hc0, hchk⟩ := hw J hJ k hk
  exact ⟨c0, by rw [List.getElem?_append_left (List.getElem?_eq_some_iff.1 hc0).1]; exact hc0, hchk⟩

theorem select_wellFilled {w : World E} {p : Party} {u i : Nat} {cl cl' : Closure D E}
    (hw : WellFilled cl) (h : select w p u i cl = .ok cl') : WellFilled cl' := by
  obtain ⟨J, c, hf, -, -, hc, hv, ht, -, -, hs⟩ := select_ok h
  refine update_preserves (P := SlotFilled) hf ht hs hw ?_
  intro k hk
  simp only [Option.some.injEq] at hk
  subst hk
  exact ⟨_, List.getElem?_set_self (List.getElem?_eq_some_iff.1 hc).1, (judge_verified_iff.1 hv).1⟩

/-- **Every operation keeps every selection checked.** -/
theorem op_preserves_wellFilled {w : World E} {op : Op D E} {cl cl' : Closure D E}
    (hw : WellFilled cl) (h : op.run w cl = .ok cl') : WellFilled cl' := by
  cases op with
  | propose u c =>
    simp only [Op.run] at h
    cases hp : propose w u c cl with
    | error r => rw [hp] at h; simp [Except.map] at h
    | ok r =>
      rw [hp] at h
      simp only [Except.map, Except.ok.injEq] at h
      subst h
      exact propose_wellFilled hw hp
  | select p u i => exact select_wellFilled hw h
  | fill p u c =>
    obtain ⟨cl₁, i, hp, hs⟩ := fill_ok h
    exact select_wellFilled (propose_wellFilled (r := (cl₁, i)) hw hp) hs
  | deselect p u =>
    obtain ⟨J, hf, -, -, ht, -, -, hs⟩ := deselect_ok h
    refine update_preserves (P := SlotFilled) hf ht hs hw ?_
    intro k hk; simp at hk
  | accept p u =>
    obtain ⟨J, i, c, hf, -, -, -, -, -, ht, -, -, hs⟩ := accept_ok h
    refine update_preserves (P := SlotFilled) hf ht hs hw ?_
    obtain ⟨hJ, rfl⟩ := find_some hf
    exact hw J hJ
  | prune p u i r =>
    obtain ⟨J, c, hf, -, -, hc, ht, -, -, hs⟩ := prune_ok h
    refine update_preserves (P := SlotFilled) hf ht hs hw ?_
    obtain ⟨hJ, rfl⟩ := find_some hf
    exact slotFilled_set (hw J hJ) hc rfl
  | rejudge u i =>
    simp only [Op.run, Except.ok.injEq] at h
    subst h
    rcases rejudge_eq w u i cl with h | ⟨J, c, hf, hc, ht, -, -, hs⟩
    · rw [h]; exact hw
    · refine update_preserves (P := SlotFilled) hf ht hs hw ?_
      obtain ⟨hJ, rfl⟩ := find_some hf
      exact slotFilled_set (hw J hJ) hc rfl
  | edit e =>
    simp only [Op.run, Except.ok.injEq] at h
    subst h
    exact repair_wellFilled hw

/-- **fill preserves derivability**: a well-filled closure stays well filled through `fill`, and
is therefore derivable (the meta-substitution lemma over checked selections). -/
theorem fill_preserves_derivable (L : CalculusLaws D HasTy) {w : World E} {p : Party} {u : Nat}
    {c : Candidate D} {cl cl' : Closure D E} (ht : cl.tpl.Typed HasTy) (hw : WellFilled cl)
    (h : fill w p u c cl = .ok cl') :
    WellFilled cl' ∧ Derivable HasTy cl' ∧ cl'.sigma u = some c.filling := by
  have hw' := op_preserves_wellFilled (op := .fill p u c) hw h
  have ht' : cl'.tpl.Typed HasTy := by rw [(history_is_prefix (op := .fill p u c) h).tpl]; exact ht
  refine ⟨hw', derivable_of_wellFilled L ht' hw', ?_⟩
  obtain ⟨cl₁, i, hp, hs⟩ := fill_ok h
  obtain ⟨J, hf, hi, -, -, -, hs1⟩ := propose_ok hp
  obtain ⟨J', c', -, -, -, hc', -, -, -, -, hs2⟩ := select_ok hs
  simp only at hi
  subst hi
  rw [hs1, update_at] at hc'
  simp only [if_true, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self,
    List.getElem?_cons_zero, Option.some.injEq] at hc'
  subst hc'
  simp only [Closure.sigma, Closure.selectedCand, hs2, update_at, if_true]
  rw [List.getElem?_set_self]
  · rfl
  · rw [hs1, update_at]; simp

/-- Coherence is kept by every operation at its world (`edit e` moves to `e.apply w`). -/
theorem op_preserves_coherent {w : World E} {op : Op D E} {cl cl' : Closure D E}
    (hc : Coherent w cl) (h : op.run w cl = .ok cl') :
    Coherent (op.next w) cl' := by
  have propose_c : ∀ {u c} {r : Closure D E × Nat}, Coherent w cl → propose w u c cl = .ok r →
      Coherent w r.1 := by
    intro u c r hc h
    obtain ⟨J, hf, -, ht, -, -, hs⟩ := propose_ok h
    refine update_preserves (P := fun I s => ∀ c ∈ s.cands, c.status = judge I w c) hf ht hs hc ?_
    obtain ⟨hJ, rfl⟩ := find_some hf
    intro d hd
    rcases List.mem_append.1 hd with hd | hd
    · exact hc J hJ d hd
    · simp only [List.mem_singleton] at hd; subst hd; rfl
  have select_c : ∀ {cl cl' : Closure D E} {p u i}, Coherent w cl → select w p u i cl = .ok cl' →
      Coherent w cl' := by
    intro cl cl' p u i hc h
    obtain ⟨J, c, hf, -, -, -, hv, ht, -, -, hs⟩ := select_ok h
    refine update_preserves (P := fun I s => ∀ c ∈ s.cands, c.status = judge I w c) hf ht hs hc ?_
    obtain ⟨hJ, rfl⟩ := find_some hf
    intro d hd
    rcases List.mem_or_eq_of_mem_set hd with hd | hd
    · exact hc J hJ d hd
    · subst hd; exact hv.symm
  cases op with
  | propose u c =>
    simp only [Op.run] at h
    cases hp : propose w u c cl with
    | error r => rw [hp] at h; simp [Except.map] at h
    | ok r =>
      rw [hp] at h
      simp only [Except.map, Except.ok.injEq] at h
      subst h
      exact propose_c hc hp
  | select p u i => exact select_c hc h
  | fill p u c =>
    obtain ⟨cl₁, i, hp, hs⟩ := fill_ok h
    exact select_c (propose_c (r := (cl₁, i)) hc hp) hs
  | deselect p u =>
    obtain ⟨J, hf, -, -, ht, -, -, hs⟩ := deselect_ok h
    refine update_preserves (P := fun I s => ∀ c ∈ s.cands, c.status = judge I w c) hf ht hs hc ?_
    obtain ⟨hJ, rfl⟩ := find_some hf
    exact hc J hJ
  | accept p u =>
    obtain ⟨J, i, c, hf, -, -, -, -, -, ht, -, -, hs⟩ := accept_ok h
    refine update_preserves (P := fun I s => ∀ c ∈ s.cands, c.status = judge I w c) hf ht hs hc ?_
    obtain ⟨hJ, rfl⟩ := find_some hf
    exact hc J hJ
  | prune p u i r =>
    obtain ⟨J, c, hf, -, -, -, ht, -, -, hs⟩ := prune_ok h
    refine update_preserves (P := fun I s => ∀ c ∈ s.cands, c.status = judge I w c) hf ht hs hc ?_
    obtain ⟨hJ, rfl⟩ := find_some hf
    intro d hd
    rcases List.mem_or_eq_of_mem_set hd with hd | hd
    · exact hc J hJ d hd
    · subst hd; rfl
  | rejudge u i =>
    simp only [Op.run, Except.ok.injEq] at h
    subst h
    rcases rejudge_eq w u i cl with h | ⟨J, c, hf, -, ht, -, -, hs⟩
    · rw [h]; exact hc
    · refine update_preserves (P := fun I s => ∀ c ∈ s.cands, c.status = judge I w c) hf ht hs hc ?_
      obtain ⟨hJ, rfl⟩ := find_some hf
      intro d hd
      rcases List.mem_or_eq_of_mem_set hd with hd | hd
      · exact hc J hJ d hd
      · subst hd; rfl
  | edit e =>
    simp only [Op.run, Except.ok.injEq] at h
    subst h
    exact repair_coherent hc


end Nanodregg.Lang.Contextual
