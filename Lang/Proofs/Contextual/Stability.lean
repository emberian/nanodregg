/- Guarded contextual closure: Stability. Moved without statement changes from Closure. -/
import Lang.Proofs.Contextual.Judge

namespace Nanodregg.Lang.Contextual

variable {D : CalculusData} {E : Type}
  {HasTy : List (HoleDecl D.Ctx D.Ty) → D.Ctx → D.Tm → D.Ty → Prop}


/-! ## Stability class -/

/-- **A guard is a value guard iff its verdict is invariant under every value-preserving
replacement of the filling.** -/
theorem valueGuard_iff {V : Type} (value : D.Tm → V) (g : E → D.Tm → Bool) :
    ValueGuard value g ↔ ∀ e t t', value t = value t' → g e t = g e t' := by
  constructor
  · rintro ⟨g', hg⟩ e t t' hv
    rw [hg, hg, hv]
  · intro h
    refine ⟨fun e v => @dite _ (∃ t, value t = v) (Classical.propDecidable _)
      (fun hv => g e (Classical.choose hv)) (fun _ => false), ?_⟩
    intro e t
    have hex : ∃ t', value t' = value t := ⟨t, rfl⟩
    simp only [dif_pos hex]
    exact h e t _ (Classical.choose_spec hex).symm

/-- **Stability class** (Hu–Pientka–Schöpp: which substitutions is a result stable under). A
value guard's verdict is stable under every term map that preserves the value. -/
theorem stability_class {V : Type} (value : D.Tm → V) {g : E → D.Tm → Bool}
    (hg : ValueGuard value g) {s : D.Tm → D.Tm} (hs : ∀ t, value (s t) = value t) :
    StableUnder g s :=
  fun e t => (valueGuard_iff value g).1 hg e (s t) t (hs t)

/-- A value guard's hole judges a filling and its value-preserving image alike, provided the
checker and supports agree (the guard is the only place the filling's VALUE is read). -/
theorem judge_stable {V : Type} (value : D.Tm → V) {I : Iface D E} (hg : ValueGuard value I.guard)
    {w : World E} {c c' : Candidate D} (hv : value c'.filling = value c.filling)
    (hchk : D.check I.ctx c'.filling I.ty = D.check I.ctx c.filling I.ty)
    (hb : c'.blockers = c.blockers) (hsup : effSupports I c' = effSupports I c)
    (hcost : c'.cost = c.cost) : judge I w c' = judge I w c := by
  have hgd : I.guard w.env c'.filling = I.guard w.env c.filling :=
    (valueGuard_iff value I.guard).1 hg _ _ _ hv
  unfold judge
  rw [hchk, hgd, hb, hsup, hcost]

/-! ## Grounding: least fixpoint -/

theorem lfpIter_sound {R : List Rule} {F : Nat → Bool} :
    ∀ (n x : Nat), lfpIter R F n x = true → Derives R F x
  | 0, x, h => .fact h
  | n + 1, x, h => by
    simp only [lfpIter, Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true, beq_iff_eq,
      List.all_eq_true] at h
    rcases h with h | ⟨r, hr, hx, hb⟩
    · exact lfpIter_sound n x h
    · subst hx
      exact .rule hr fun y hy => lfpIter_sound n y (hb y hy)

/-- **Grounding is well-founded.** With no live fact and every rule needing a premise, nothing is
derivable, however the rules cycle. -/
theorem no_facts_no_derivation {R : List Rule} {F : Nat → Bool} (hF : ∀ x, F x = false)
    (hR : ∀ r ∈ R, r.body ≠ []) {x : Nat} : ¬ Derives R F x := by
  intro h
  induction h with
  | fact hx => rw [hF] at hx; cases hx
  | @rule r hr _ ih =>
    obtain ⟨y, hy⟩ := List.exists_mem_of_ne_nil _ (hR r hr)
    exact ih y hy

/-! ## Grounding: unfounded sets -/

/-- **Unfounded sets are not grounded.** A set `S` of atoms with no live fact, every rule for an
atom of `S` needing some atom of `S`, contains no derivable atom, however other facts and rules
stand (the least-fixpoint reading; `no_facts_no_derivation` is its empty-world special case). -/
theorem unfounded_not_derivable {R : List Rule} {F : Nat → Bool} {S : Nat → Prop}
    (hF : ∀ x, S x → F x = false) (hR : ∀ r ∈ R, S r.head → ∃ y ∈ r.body, S y) {x : Nat}
    (hx : S x) : ¬ Derives R F x := by
  intro h
  induction h with
  | fact hf => rw [hF _ hx] at hf; cases hf
  | @rule r hr _ ih =>
    obtain ⟨y, hy, hS⟩ := hR r hr hx
    exact ih y hy hS


end Nanodregg.Lang.Contextual
