/- Guarded contextual closure: History. Moved without statement changes from Closure. -/
import Lang.Proofs.Contextual.Soundness

namespace Nanodregg.Lang.Contextual

variable {D : CalculusData} {E : Type}
  {HasTy : List (HoleDecl D.Ctx D.Ty) → D.Ctx → D.Tm → D.Ty → Prop}


/-! ## Selection, acceptance, the executed prefix -/

/-- **select requires availability.** An admitted `select` was made by the hole's chooser, before
acceptance, of a retained candidate that judges `verified` AT THE CURRENT WORLD (every support
live), and `σ` now maps the hole to that candidate's filling. -/
theorem select_requires_available {w : World E} {p : Party} {u i : Nat} {cl cl' : Closure D E}
    (h : select w p u i cl = .ok cl') :
    ∃ I c, cl.find u = some I ∧ p = I.chooser ∧ (cl.slot u).accepted = false ∧
      (cl.slot u).cands[i]? = some c ∧ judge I w c = .verified ∧
      (∀ t ∈ effSupports I c, w.live t = true) ∧ cl'.sigma u = some c.filling := by
  obtain ⟨I, c, hf, hp, hacc, hc, hv, -, -, -, hs⟩ := select_ok h
  refine ⟨I, c, hf, hp, hacc, hc, hv, (judge_verified_iff.1 hv).2.2.2.1, ?_⟩
  simp only [Closure.sigma, Closure.selectedCand, hs, update_at, if_true]
  rw [List.getElem?_set_self (List.getElem?_eq_some_iff.1 hc).1]
  rfl

/-- A token re-issued at a new version no longer supports anything: a candidate citing the old
version does not judge `verified` after the re-issue. -/
theorem reissued_support_unverified {w : World E} {I : Iface D E} {c : Candidate D}
    {id old new : Nat} (hne : old ≠ new) (hcite : ⟨id, old⟩ ∈ effSupports I c) :
    judge I (applyAll (reissue id old new) w) c ≠ .verified := by
  intro hv
  have := (judge_verified_iff.1 hv).2.2.2.1 _ hcite
  rw [reissue_never_reenables w id old new hne] at this
  cases this

/-- **An executed prefix blocks re-planning.** After `accept` of hole `u`: no `select` and no
`deselect` of `u` is admitted at any world by anyone; no repair moves `u`'s selection; the
settlement it owes is recorded and survives every later operation; and a `select` of ANOTHER hole
(an unexecuted component) leaves `u`'s slot, the owed obligations and the history prefix as they
were. -/
theorem executed_prefix_blocks_replan {w : World E} {p : Party} {u : Nat} {cl cl₁ : Closure D E}
    (ha : accept w p u cl = .ok cl₁) :
    (∀ (w' : World E) q j cl₂, select w' q u j cl₁ ≠ .ok cl₂) ∧
    (∀ q cl₂, deselect q u cl₁ ≠ .ok cl₂) ∧
    (∀ (w' : World E) (e : Edit E), ((repair w' e cl₁).1.slot u).selected = (cl₁.slot u).selected) ∧
    (∃ i, (cl₁.slot u).selected = some i ∧ Obligation.settle u i ∈ cl₁.owed ∧
      (∀ (w' : World E) q (r : Token) cl₂, prune w' q u i r cl₁ ≠ .ok cl₂) ∧
      ∀ (w' : World E) (op : Op D E) cl₂, op.run w' cl₁ = .ok cl₂ → Obligation.settle u i ∈ cl₂.owed) ∧
    (∀ (w' : World E) q v j cl₂, v ≠ u → select w' q v j cl₁ = .ok cl₂ →
      cl₂.slot u = cl₁.slot u ∧ cl₂.owed = cl₁.owed ∧ cl₂.hist = cl₁.hist ++ [.selected v j]) := by
  obtain ⟨I, i, c, hf, -, -, hsel, -, -, ht, ho, -, hs⟩ := accept_ok ha
  have hacc : (cl₁.slot u).accepted = true := by rw [hs, update_at]; simp
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro w' q j cl₂ h
    obtain ⟨-, -, -, -, h', -⟩ := select_ok h
    rw [hacc] at h'; cases h'
  · intro q cl₂ h
    obtain ⟨-, -, -, h', -⟩ := deselect_ok h
    rw [hacc] at h'; cases h'
  · intro w' e
    simp only [repair]
    split
    · rename_i J hJ
      exact repair_keeps_accepted _ _ _ _ hacc
    · rfl
  · have hsel₁ : (cl₁.slot u).selected = some i := by rw [hs, update_at]; simp [hsel]
    refine ⟨i, hsel₁, by rw [ho]; simp, ?_, ?_⟩
    · intro w' q r cl₂ h
      obtain ⟨-, -, -, -, h', -⟩ := prune_ok h
      exact h' ⟨hacc, hsel₁⟩
    intro w' op cl₂ h
    obtain ⟨-, -, ⟨sfx, hsfx⟩⟩ := history_is_prefix h
    rw [hsfx, ho]; simp
  · intro w' q v j cl₂ hne h
    obtain ⟨J2, c2, -, -, -, -, -, -, ho2, hh2, hs2⟩ := select_ok h
    refine ⟨?_, ho2, hh2⟩
    rw [hs2, update_at]
    simp [Ne.symm hne]

/-! ## Boundaries -/

/-- **The boundary theorem for a consumer.** A consumer that relies on a hole only through an
exported projection gives the same verdict on any two closures whose selected fillings agree on
that projection: candidate identity, supports, history are invisible to it. -/
theorem consumer_boundary {V : Type} (k : Consumer D V) {cl cl' : Closure D E}
    (h : (cl.sigma k.hole).map k.proj = (cl'.sigma k.hole).map k.proj) : k.holds cl = k.holds cl' := by
  unfold Consumer.holds
  cases h1 : cl.sigma k.hole <;> cases h2 : cl'.sigma k.hole <;> rw [h1, h2] at h <;>
    simp_all

/-! ## Sessions -/

/-- Coherence holds along a session (the world threaded through every edit). -/
theorem session_preserves_coherent :
    ∀ (ops : List (Op D E)) {w w' : World E} {cl cl' : Closure D E},
      Coherent w cl → Session.run ops (w, cl) = .ok (w', cl') → Coherent w' cl'
  | [], _, _, _, _, hc, h => by
    simp only [Session.run, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; exact hc
  | op :: ops, w, w', cl, cl', hc, h => by
    simp only [Session.run] at h
    split at h
    · cases h
    · rename_i cl₁ h₁
      exact session_preserves_coherent ops (op_preserves_coherent hc h₁) h

/-- A session never rewrites the template. -/
theorem session_preserves_tpl :
    ∀ (ops : List (Op D E)) {w w' : World E} {cl cl' : Closure D E},
      Session.run ops (w, cl) = .ok (w', cl') → cl'.tpl = cl.tpl
  | [], _, _, _, _, h => by
    simp only [Session.run, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; rfl
  | op :: ops, w, w', cl, cl', h => by
    simp only [Session.run] at h
    split at h
    · cases h
    · rename_i cl₁ h₁
      rw [session_preserves_tpl ops h, (history_is_prefix h₁).tpl]

/-- Well-filledness (hence derivability) holds along a session. -/
theorem session_preserves_wellFilled :
    ∀ (ops : List (Op D E)) {w w' : World E} {cl cl' : Closure D E},
      WellFilled cl → Session.run ops (w, cl) = .ok (w', cl') → WellFilled cl'
  | [], _, _, _, _, hc, h => by
    simp only [Session.run, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; exact hc
  | op :: ops, w, w', cl, cl', hc, h => by
    simp only [Session.run] at h
    split at h
    · cases h
    · rename_i cl₁ h₁
      exact session_preserves_wellFilled ops (op_preserves_wellFilled hc h₁) h

theorem fromScratch_wellFilled (w : World E) (tpl : Template D E) (cands : Nat → List (Candidate D)) :
    WellFilled (fromScratch w tpl cands) := by
  intro I hI i hi
  simp only [fromScratch, find_name_self tpl.names hI] at hi
  cases hi


end Nanodregg.Lang.Contextual
