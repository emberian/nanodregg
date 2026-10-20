import Lang.Contextual.Material
import Lang.Proofs.Contextual.Judge

namespace Nanodregg.Lang.Contextual.Material

/-- The fragment consists exactly of actual visits, never supplied metadata
(Fouquere–Quatrini Def 5.1 p24). -/
theorem material_mem {A : Type} {tests : List (Test A)} {c : Filling A}
    {cell : List Bool × Stop A} :
    cell ∈ material tests c ↔ ∃ t ∈ tests, visit c t.path = cell := by
  simp [material]

/-- A successful receipt has the exact scope/material and every test completes
(Fouquere–Quatrini pp24–26; completion is additional to materiality). -/
theorem verified_scope {A : Type} {tests : List (Test A)} {c : Filling A}
    {r : Receipt A} (h : inspect tests c = .verified r) :
    r.against = tests ∧ r.fragment = material tests c ∧
      ∀ t ∈ tests, complete t c = true := by
  unfold inspect at h
  split at h
  · cases h
  · split at h
    · rename_i hg
      cases h
      refine ⟨rfl, rfl, ?_⟩
      simpa [P1.guard, List.all_map, interaction] using hg
    · cases h

/-- Any visited give-up forces partial, independently of the answer predicates
(Fouquere–Quatrini Def 5.5 p26; no materiality-implies-winning claim). -/
theorem visited_gaveUp_partial {A : Type} {tests : List (Test A)} {c : Filling A}
    {t : Test A} (ht : t ∈ tests) (h : (visit c t.path).2 = .gaveUp) :
    inspect tests c = .incomplete := by
  unfold inspect
  have hm : visit c t.path ∈ material tests c := material_mem.2 ⟨t, ht, rfl⟩
  have ha : (material tests c).any (fun cell => match cell.2 with
      | .answer _ => false | _ => true) = true :=
    List.any_eq_true.2 ⟨_, hm, by simp [h]⟩
  exact if_pos ha

/-- A visited daimon can never obtain a verified receipt (Fouquere–Quatrini p26). -/
theorem visited_gaveUp_never_verified {A : Type} {tests : List (Test A)}
    {c : Filling A} {t : Test A} (ht : t ∈ tests)
    (h : (visit c t.path).2 = .gaveUp) (r : Receipt A) :
    inspect tests c ≠ .verified r := by
  rw [visited_gaveUp_partial ht h]
  intro e
  cases e

/-- Enlarging the tests extends actual material (Fouquere–Quatrini Def 5.1 p24). -/
theorem material_mono {A : Type} {s t : List (Test A)}
    (h : ∀ x ∈ s, x ∈ t) (c : Filling A) :
    ∀ cell ∈ material s c, cell ∈ material t c := by
  intro cell hc
  obtain ⟨x, hx, hv⟩ := material_mem.1 hc
  exact material_mem.2 ⟨x, h x hx, hv⟩

/-- The unused daimon is absent from the tested fragment; requiring it exposes partiality
(Fouquere–Quatrini Defs 5.1/5.5 pp24/26). -/
theorem required_exposes_giveUp :
    material [left] sample = [([false], .answer 7)] ∧
    inspect [left] sample = .verified ⟨[left], [([false], .answer 7)]⟩ ∧
    inspect [left, right] sample = .incomplete := by
  exact ⟨rfl, rfl, rfl⟩

/-- An answered but rejected interaction is distinct from incomplete material
(Fouquere–Quatrini p24, successful interaction requirement). -/
theorem bad_answer_rejected :
    inspect [left] (.fork (.answer 8) .gaveUp) = .rejected := by rfl


/-- Material-aware verification preserves original admission and checks every completed
interaction, while recording its exact scope and fragment (Fouquere–Quatrini pp24–26). -/
theorem candidate_verified {D : CalculusData} {E A : Type} {I : Iface D E}
    {tests : E → List (Test A)} {project : E → D.Tm → Filling A}
    {w : World E} {c : Candidate D}
    (h : (inspectCandidate I tests project w c).1 = .verified) :
    judge I w c = .verified ∧
    (inspectCandidate I tests project w c).2.against = tests w.env ∧
    (inspectCandidate I tests project w c).2.fragment =
      material (tests w.env) (project w.env c.filling) ∧
    ∀ t ∈ tests w.env, complete t (project w.env c.filling) = true := by
  obtain ⟨ht, hg, hb, hs, hc⟩ := judge_verified_iff.1 h
  have hguard : I.guard w.env c.filling = true ∧
      P1.guard ((tests w.env).map interaction) (project w.env c.filling) = true :=
    by simpa only [withMaterial, Bool.and_eq_true] using hg
  refine ⟨judge_verified_iff.2 ⟨ht, hguard.1, hb, hs, hc⟩, rfl, rfl, ?_⟩
  simpa [P1.guard, List.all_map, interaction] using hguard.2

/-- A visited give-up cannot be admitted by the actual candidate judge, even if the
original guard accepted it (Fouquere–Quatrini p26, separate completion policy). -/
theorem candidate_gaveUp_refused {D : CalculusData} {E A : Type} {I : Iface D E}
    {tests : E → List (Test A)} {project : E → D.Tm → Filling A}
    {w : World E} {c : Candidate D} {t : Test A} (ht : t ∈ tests w.env)
    (hu : (visit (project w.env c.filling) t.path).2 = .gaveUp) :
    (inspectCandidate I tests project w c).1 ≠ .verified := by
  intro h
  have := (candidate_verified h).2.2.2 t ht
  simp [complete, hu] at this

end Nanodregg.Lang.Contextual.Material
