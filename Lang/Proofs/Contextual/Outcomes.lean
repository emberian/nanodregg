/- Guarded contextual closure: Outcomes. Moved without statement changes from Closure. -/
import Lang.Proofs.Contextual.Repair

namespace Nanodregg.Lang.Contextual

variable {D : CalculusData} {E : Type}
  {HasTy : List (HoleDecl D.Ctx D.Ty) → D.Ctx → D.Tm → D.Ty → Prop}


/-! ## The repair outcomes, each sound -/

theorem findIx_some {α : Type} {p : α → Bool} :
    ∀ {l : List α} {n : Nat} {a : α} {j : Nat}, findIx p l n = some (a, j) →
      p a = true ∧ n ≤ j ∧ l[j - n]? = some a
  | [], _, _, _, h => by simp [findIx] at h
  | b :: l, n, a, j, h => by
    unfold findIx at h
    split at h
    · rename_i hb
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp [hb]
    · obtain ⟨hp, hle, hget⟩ := findIx_some h
      refine ⟨hp, by omega, ?_⟩
      have : j - n = (j - (n + 1)) + 1 := by omega
      rw [this]; simpa using hget

theorem findIx_none {α : Type} {p : α → Bool} :
    ∀ {l : List α} {n : Nat}, findIx p l n = none → ∀ a ∈ l, p a = false
  | [], _, _, _, ha => by cases ha
  | b :: l, n, h, a, ha => by
    unfold findIx at h
    split at h
    · cases h
    · rename_i hb
      rcases List.mem_cons.1 ha with rfl | ha
      · simpa using hb
      · exact findIx_none h a ha

theorem isVerified_iff {st : Status} : isVerified st = true ↔ st = .verified := by
  simp [isVerified]

theorem repairHole_accepted (w' : World E) (e : Edit E) (I : Iface D E) (s : Slot D) :
    (repairHole w' e I s).1.accepted = s.accepted := by
  unfold repairHole
  split
  · rfl
  · split <;> rfl

theorem repairSelected_accepted {e : Edit E} {I : Iface D E} {i : Nat} {cs : List (Candidate D)} :
    (repairSelected e I true i cs).1 = some i := by
  unfold repairSelected
  split
  · rfl
  · split <;> simp

/-- **The executed prefix does not move under repair.** An accepted hole's selection is never
changed by a repair, whatever the edit. -/
theorem repair_keeps_accepted (w' : World E) (e : Edit E) (I : Iface D E) (s : Slot D)
    (ha : s.accepted = true) : (repairHole w' e I s).1.selected = s.selected := by
  unfold repairHole
  split
  · rfl
  · split
    · rfl
    · rename_i i hsel
      simp only [ha, repairSelected_accepted, hsel]

/-- What a reported outcome of `repairHole` comes from: a touched hole with a selection. -/
theorem repairHole_some {w' : World E} {e : Edit E} {I : Iface D E} {s s' : Slot D} {o : Outcome D}
    (h : repairHole w' e I s = (s', some o)) :
    ∃ i, s.selected = some i ∧ s'.cands = repairCands w' e I s.cands ∧
      repairSelected e I s.accepted i (repairCands w' e I s.cands) = (s'.selected, some o) := by
  unfold repairHole at h
  split at h
  · simp at h
  split at h
  · simp at h
  rename_i i hsel
  simp only [Prod.mk.injEq] at h
  obtain ⟨rfl, ho⟩ := h
  exact ⟨i, hsel, rfl, by rw [← ho]⟩

/-- The re-judged list, read at an index. -/
theorem rejudged_get {w' : World E} {I : Iface D E} {cs : List (Candidate D)} {k : Nat}
    {d : Candidate D}
    (h : (cs.map fun c => { c with status := judge I w' c })[k]? = some d) :
    ∃ d0, cs[k]? = some d0 ∧ d = { d0 with status := judge I w' d0 } := by
  rw [List.getElem?_map] at h
  cases hd : cs[k]? with
  | none => simp [hd] at h
  | some d0 => simp only [hd, Option.map_some, Option.some.injEq] at h; exact ⟨d0, rfl, h.symm⟩

/-- `alternative`: the selected candidate lost its justification, and repair switched the
derivation `D` to another candidate with THE SAME filling (`σ` unchanged) that judges `verified`. -/
theorem alternative_sound {w : World E} {e : Edit E} {I : Iface D E} {s : Slot D}
    (hs : ∀ c ∈ s.cands, c.status = judge I w c) {s' : Slot D} {u j : Nat}
    (h : repairHole (e.apply w) e I s = (s', some (.alternative u j))) :
    ∃ i c d, s.selected = some i ∧ s.cands[i]? = some c ∧ judge I (e.apply w) c ≠ .verified ∧
      s.accepted = false ∧ s'.selected = some j ∧ s.cands[j]? = some d ∧
      judge I (e.apply w) d = .verified ∧ d.filling = c.filling := by
  obtain ⟨i, hsel, -, hr⟩ := repairHole_some h
  rw [repairCands_eq hs] at hr
  unfold repairSelected at hr
  split at hr
  · simp at hr
  rename_i c hc
  obtain ⟨c0, hc0, rfl⟩ := rejudged_get hc
  split at hr
  · simp [keptOutcome] at hr; split at hr <;> simp at hr
  rename_i hnv
  split at hr
  · simp at hr
  rename_i hacc
  unfold reselect at hr
  split at hr
  · rename_i d j' hf
    simp only [Prod.mk.injEq, Option.some.injEq, Outcome.alternative.injEq] at hr
    obtain ⟨hsj, -, rfl⟩ := hr
    obtain ⟨hp, -, hget⟩ := findIx_some hf
    simp only [Nat.sub_zero] at hget
    obtain ⟨d0, hd0, rfl⟩ := rejudged_get hget
    simp only [Bool.and_eq_true, isVerified_iff, decide_eq_true_eq] at hp
    refine ⟨i, c0, d0, hsel, hc0, ?_, by simpa using hacc, hsj.symm, hd0, hp.1, hp.2⟩
    simpa [isVerified_iff] using hnv
  · split at hr <;> simp at hr

/-- `replacement`: the selected candidate lost its justification, NO verified candidate has its
filling, and repair OFFERS a verified candidate with a different filling; the selection is left
to the chooser (polarity: `σ` changes only by `select`). -/
theorem replacement_sound {w : World E} {e : Edit E} {I : Iface D E} {s : Slot D}
    (hs : ∀ c ∈ s.cands, c.status = judge I w c) {s' : Slot D} {u j : Nat} {M : D.Tm}
    (h : repairHole (e.apply w) e I s = (s', some (.replacement u j M))) :
    ∃ i c d, s.selected = some i ∧ s.cands[i]? = some c ∧ judge I (e.apply w) c ≠ .verified ∧
      s'.selected = s.selected ∧ s.cands[j]? = some d ∧ d.filling = M ∧
      judge I (e.apply w) d = .verified ∧
      ∀ d' ∈ s.cands, judge I (e.apply w) d' = .verified → d'.filling ≠ c.filling := by
  obtain ⟨i, hsel, -, hr⟩ := repairHole_some h
  rw [repairCands_eq hs] at hr
  unfold repairSelected at hr
  split at hr
  · simp at hr
  rename_i c hc
  obtain ⟨c0, hc0, rfl⟩ := rejudged_get hc
  split at hr
  · simp [keptOutcome] at hr; split at hr <;> simp at hr
  rename_i hnv
  split at hr
  · simp at hr
  unfold reselect at hr
  split at hr
  · simp at hr
  rename_i hnone
  split at hr
  · rename_i d j' hf
    simp only [Prod.mk.injEq, Option.some.injEq, Outcome.replacement.injEq] at hr
    obtain ⟨hsj, -, rfl, rfl⟩ := hr
    obtain ⟨hp, -, hget⟩ := findIx_some hf
    simp only [Nat.sub_zero] at hget
    obtain ⟨d0, hd0, rfl⟩ := rejudged_get hget
    refine ⟨i, c0, d0, hsel, hc0, ?_, by rw [hsel, hsj], hd0, rfl, ?_, ?_⟩
    · simpa [isVerified_iff] using hnv
    · simpa [isVerified_iff] using hp
    · intro d' hd' hv heq
      have := findIx_none hnone _ (List.mem_map.2 ⟨d', hd', rfl⟩)
      simp [isVerified, hv, heq] at this
  · simp at hr

/-- `strengthening`: the edit withdrew the token behind hypothesis `x` of the hole's context, and
the selected filling did not use `x`: it factors as `t₀[π]` with `t₀` typed in the smaller context.
(The converse is the obstruction: a filling that USES `x` lost a support and is not verified.) -/
theorem strengthening_sound (L : CalculusLaws D HasTy) {w : World E} {e : Edit E} {I : Iface D E} {s : Slot D}
    (hs : ∀ c ∈ s.cands, c.status = judge I w c) {s' : Slot D} {u x : Nat} {t₀ : D.Tm}
    (h : repairHole (e.apply w) e I s = (s', some (.strengthening u x t₀))) :
    HasTy [] (D.drop I.ctx x) t₀ I.ty ∧ D.uses (D.weaken x t₀) x = false ∧
      ∃ i c, s.selected = some i ∧ s.cands[i]? = some c ∧ D.uses c.filling x = false ∧
        D.weaken x t₀ = c.filling := by
  obtain ⟨i, hsel, -, hr⟩ := repairHole_some h
  rw [repairCands_eq hs] at hr
  unfold repairSelected at hr
  split at hr
  · simp at hr
  rename_i c hc
  obtain ⟨c0, hc0, rfl⟩ := rejudged_get hc
  split at hr
  · rename_i hv
    simp only [Prod.mk.injEq, Option.some.injEq, keptOutcome] at hr
    obtain ⟨-, hr⟩ := hr
    split at hr
    · rename_i x' hx
      simp only [Outcome.strengthening.injEq] at hr
      obtain ⟨-, rfl, rfl⟩ := hr
      have hv' : judge I (e.apply w) c0 = .verified := by simpa [isVerified_iff] using hv
      obtain ⟨hchk, -, -, hsup, -⟩ := judge_verified_iff.1 hv'
      cases e with
      | withdraw t =>
        simp only [hypOf, Option.map_eq_some_iff] at hx
        obtain ⟨⟨x0, t0⟩, hfind, rfl⟩ := hx
        have hmem := List.mem_of_find?_eq_some hfind
        have ht0 : t0 = t := by simpa using List.find?_some hfind
        subst ht0
        have huse : D.uses c0.filling x0 = false := by
          cases hu : D.uses c0.filling x0
          · rfl
          · have hin : t0 ∈ effSupports I c0 := by
              simp only [effSupports, List.mem_append, List.mem_map, List.mem_filter]
              exact Or.inr ⟨(x0, t0), ⟨hmem, hu⟩, rfl⟩
            have := hsup t0 hin
            simp [Edit.apply, World.set] at this
        have hty := L.strengthen_lemma (L.check_sound hchk) huse
        exact ⟨hty, L.weaken_avoids hty, i, c0, hsel, hc0, huse, L.strengthen_factor huse⟩
      | assert t => simp [hypOf] at hx
      | setEnv _ => simp [hypOf] at hx
    · simp at hr
  split at hr
  · simp at hr
  unfold reselect at hr
  split at hr
  · simp at hr
  split at hr <;> simp at hr

/-- `suspended`: either the hole's selection was EXECUTED (accepted) and lost its justification,
which owes a reconciliation and keeps the selection; or no retained candidate judges `verified` at
the new world. Never a refutation of the hole. -/
theorem suspended_sound {w : World E} {e : Edit E} {I : Iface D E} {s : Slot D}
    (hs : ∀ c ∈ s.cands, c.status = judge I w c) {s' : Slot D} {u : Nat} {Φ : List Obligation}
    (h : repairHole (e.apply w) e I s = (s', some (.suspended u Φ))) :
    (s.accepted = true ∧ ∃ i, Φ = [.reconcile I.name i] ∧ s'.selected = some i ∧ s.selected = some i) ∨
      (s.accepted = false ∧ s'.selected = s.selected ∧ .refill I.name ∈ Φ ∧
        ∀ d ∈ s.cands, judge I (e.apply w) d ≠ .verified) := by
  obtain ⟨i, hsel, -, hr⟩ := repairHole_some h
  rw [repairCands_eq hs] at hr
  unfold repairSelected at hr
  split at hr
  · simp at hr
  split at hr
  · simp [keptOutcome] at hr; split at hr <;> simp at hr
  split at hr
  · rename_i hacc
    simp only [Prod.mk.injEq, Option.some.injEq, Outcome.suspended.injEq] at hr
    obtain ⟨hsj, -, rfl⟩ := hr
    exact Or.inl ⟨hacc, i, rfl, hsj.symm, hsel⟩
  rename_i hacc
  unfold reselect at hr
  split at hr
  · simp at hr
  split at hr
  · simp at hr
  rename_i hnone
  simp only [Prod.mk.injEq, Option.some.injEq, Outcome.suspended.injEq] at hr
  obtain ⟨hsj, -, rfl⟩ := hr
  refine Or.inr ⟨by simpa using hacc, by rw [hsel, hsj], by simp [suspendObligations], ?_⟩
  intro d hd hv
  have := findIx_none hnone _ (List.mem_map.2 ⟨d, hd, rfl⟩)
  simp [isVerified, hv] at this


end Nanodregg.Lang.Contextual
