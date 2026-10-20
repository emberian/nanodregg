/- Guarded contextual closure: Judge. Moved without statement changes from Closure. -/
import Lang.Proofs.Contextual.ClosureStatements

namespace Nanodregg.Lang.Contextual

variable {D : CalculusData} {E : Type}
  {HasTy : List (HoleDecl D.Ctx D.Ty) → D.Ctx → D.Tm → D.Ty → Prop}


/-! ## Tokens -/

theorem set_live (w : World E) (t t' : Token) (b : Bool) :
    (w.set t b).live t' = if t' = t then b else w.live t' := rfl

/-- **Immutable versioned tokens.** Re-issuing an id at a new version never re-enables the old
token: whatever was live before, the old version is dead afterwards. -/
theorem reissue_never_reenables (w : World E) (id old new : Nat) (h : old ≠ new) :
    (applyAll (reissue id old new) w).live ⟨id, old⟩ = false := by
  simp [reissue, applyAll, Edit.apply, World.set, h]

/-! ## The judgment -/

theorem judge_congr {I : Iface D E} {w w' : World E} {c : Candidate D} (he : w.env = w'.env)
    (hl : ∀ t ∈ deps I c, w.live t = w'.live t) : judge I w c = judge I w' c := by
  have hb : c.blockers.filter w.live = c.blockers.filter w'.live :=
    List.filter_congr fun t ht => hl t (by simp [deps, ht])
  have hs : (effSupports I c).filter (fun t => !w.live t) =
      (effSupports I c).filter (fun t => !w'.live t) :=
    List.filter_congr fun t ht => by rw [hl t (by simp [deps, ht])]
  simp only [judge, he, hb, hs]

/-- **The boundary lemma.** An edit that does not touch a candidate leaves its judgment unchanged:
the dependency sets are sufficient. -/
theorem judge_frame {I : Iface D E} {w : World E} {c : Candidate D} {e : Edit E}
    (h : touches e I c = false) : judge I (e.apply w) c = judge I w c := by
  cases e with
  | withdraw t =>
    simp only [touches, decide_eq_false_iff_not] at h
    exact judge_congr rfl fun t' ht' => by
      have : t' ≠ t := fun he => h (he ▸ ht')
      simp [Edit.apply, World.set, this]
  | assert t =>
    simp only [touches, decide_eq_false_iff_not] at h
    exact judge_congr rfl fun t' ht' => by
      have : t' ≠ t := fun he => h (he ▸ ht')
      simp [Edit.apply, World.set, this]
  | setEnv _ => simp [touches] at h

theorem blockers_empty_iff {w : World E} {bs : List Token} :
    (bs.filter w.live).isEmpty = true ↔ ∀ b ∈ bs, w.live b = false := by
  rw [List.isEmpty_iff, List.filter_eq_nil_iff]; simp

theorem missing_empty_iff {w : World E} {ts : List Token} :
    (ts.filter fun t => !w.live t).isEmpty = true ↔ ∀ t ∈ ts, w.live t = true := by
  rw [List.isEmpty_iff, List.filter_eq_nil_iff]; simp

theorem judge_verified_iff {I : Iface D E} {w : World E} {c : Candidate D} :
    judge I w c = .verified ↔
      D.check I.ctx c.filling I.ty = true ∧ I.guard w.env c.filling = true ∧
      (∀ b ∈ c.blockers, w.live b = false) ∧ (∀ t ∈ effSupports I c, w.live t = true) ∧
      c.cost ≤ I.budget := by
  rw [← blockers_empty_iff, ← missing_empty_iff]
  unfold judge
  cases h1 : D.check I.ctx c.filling I.ty <;>
  cases h2 : I.guard w.env c.filling <;>
  cases h3 : (c.blockers.filter w.live).isEmpty <;>
  cases h4 : ((effSupports I c).filter fun t => !w.live t).isEmpty <;>
  by_cases h5 : c.cost ≤ I.budget <;> simp [h5]

/-- `conflict` is decided by the checker and the guard alone: it reads no token. Its `illTyped`
arm is a refutation of typing (`conflict_illTyped_refutes`, by `check_complete`), its `guardFails`
arm a checked guard failure in the current environment. -/
theorem judge_conflict_iff {I : Iface D E} {w : World E} {c : Candidate D} {ev : Evidence} :
    judge I w c = .conflict ev ↔
      (D.check I.ctx c.filling I.ty = false ∧ ev = .illTyped) ∨
      (D.check I.ctx c.filling I.ty = true ∧ I.guard w.env c.filling = false ∧ ev = .guardFails) := by
  unfold judge
  cases h1 : D.check I.ctx c.filling I.ty <;>
  cases h2 : I.guard w.env c.filling <;>
  cases h3 : (c.blockers.filter w.live).isEmpty <;>
  cases h4 : ((effSupports I c).filter fun t => !w.live t).isEmpty <;>
  by_cases h5 : c.cost ≤ I.budget <;> cases ev <;> simp [h5]

/-- **`illTyped` is a refutation.** With a complete checker, a candidate judged `conflict illTyped`
does not type at its hole: checked contrary evidence, not a missing proof. -/
theorem conflict_illTyped_refutes (L : CalculusLaws D HasTy) {I : Iface D E} {w : World E}
    {c : Candidate D} (h : judge I w c = .conflict .illTyped) : ¬ HasTy [] I.ctx c.filling I.ty := by
  intro hty
  rcases judge_conflict_iff.1 h with ⟨hc, -⟩ | ⟨-, -, hev⟩
  · rw [L.check_complete hty] at hc; cases hc
  · cases hev

/-- `pruned` names exactly the live blockers, and there is at least one. -/
theorem judge_pruned {I : Iface D E} {w : World E} {c : Candidate D} {bs : List Token}
    (h : judge I w c = .pruned bs) :
    D.check I.ctx c.filling I.ty = true ∧ I.guard w.env c.filling = true ∧
      bs = c.blockers.filter w.live ∧ (c.blockers.filter w.live).isEmpty = false := by
  unfold judge at h
  revert h
  cases h1 : D.check I.ctx c.filling I.ty <;>
  cases h2 : I.guard w.env c.filling <;>
  cases h3 : (c.blockers.filter w.live).isEmpty <;>
  cases h4 : ((effSupports I c).filter fun t => !w.live t).isEmpty <;>
  by_cases h5 : c.cost ≤ I.budget <;> simp [h5, eq_comm]

/-- **The provenance bridge.** `provenance I env cs` is a polynomial over tokens computed from the
environment alone (it reads no liveness): one monomial per candidate that passes the checker, the
guard and the budget, its supports as positive literals and its blockers as negative literals. A
hole has a verified candidate at `w` iff some monomial holds in `w` (sum = alternatives, product =
joint requirements, negation = an exclusion reason). This is the bridge to `judge_verified_iff`: the
token part of the judgment IS the evaluation of a world-independent polynomial. -/
theorem provenance_iff {I : Iface D E} {w : World E} {cs : List (Candidate D)} :
    (∃ c ∈ cs, judge I w c = .verified) ↔
      ∃ m ∈ provenance I w.env cs, Monomial.holds w m := by
  constructor
  · rintro ⟨c, hc, hv⟩
    obtain ⟨h1, h2, h3, h4, h5⟩ := judge_verified_iff.1 hv
    refine ⟨(effSupports I c, c.blockers), ?_, h4, h3⟩
    simp only [provenance, List.mem_map, List.mem_filter]
    exact ⟨c, ⟨hc, by simp [h1, h2, h5]⟩, rfl⟩
  · rintro ⟨m, hm, hl, hb⟩
    simp only [provenance, List.mem_map, List.mem_filter, Bool.and_eq_true, decide_eq_true_eq] at hm
    obtain ⟨c, ⟨hc, ⟨⟨h1, h2⟩, h5⟩⟩, rfl⟩ := hm
    exact ⟨c, hc, judge_verified_iff.2 ⟨h1, h2, hb, hl, h5⟩⟩

/-- **The obstruction is real.** For every token-backed hypothesis `(x, t)` of a hole, the bare
variable `x` types at the type the context gives it and cites `t`: a filling that uses `x` depends on
`t`, so `uses ≡ false` cannot hide the obstruction. -/
theorem hyp_var_cites (L : CalculusLaws D HasTy) {I : Iface D E} {x : Nat} {t : Token} (h : (x, t) ∈ I.hyps)
    (c : Candidate D) (hc : c.filling = D.var x) :
    (∃ A, D.lookup I.ctx x = some A ∧ HasTy [] I.ctx c.filling A) ∧ t ∈ effSupports I c := by
  refine ⟨?_, ?_⟩
  · have := I.hyps_real _ h
    cases hA : D.lookup I.ctx x with
    | none => rw [hA] at this; cases this
    | some A => exact ⟨A, rfl, hc ▸ L.hasTy_var hA⟩
  · simp only [effSupports, List.mem_append, List.mem_map, List.mem_filter]
    exact Or.inr ⟨(x, t), ⟨h, by rw [hc]; exact L.uses_var⟩, rfl⟩

/-- **Weakening never produces the dropped variable.** No term typed in `drop Ψ x`, weakened back,
is the variable `x`: the general form, which bites for every calculus (de Bruijn included). -/
theorem weaken_never_var (L : CalculusLaws D HasTy) {Ψ : D.Ctx} {M : D.Tm} {A : D.Ty} {x : Nat}
    (h : HasTy [] (D.drop Ψ x) M A) : D.weaken x M ≠ D.var x := by
  intro he
  have := L.weaken_avoids h
  rw [he, L.uses_var] at this
  cases this

/-- **`drop` removes the hypothesis, for weakenings that fix the variable.** If weakening fixes
`var x` (named-variable calculi such as the toy, or the degenerate `weaken = id`), then `var x` does
not type in `drop Ψ x`, so `drop = id` with `weaken = id` is refuted. It does NOT cover a de Bruijn
weakening (CMTT's `shiftAt` sends `var x` to `var (x+1)`, so the premise is false there); the
general statement is `weaken_never_var`. -/
theorem drop_removes (L : CalculusLaws D HasTy) {Ψ : D.Ctx} {x : Nat} {A : D.Ty}
    (hw : D.weaken x (D.var x) = D.var x) : ¬ HasTy [] (D.drop Ψ x) (D.var x) A :=
  fun h => weaken_never_var L h hw

/-! ## Withdrawal never refutes -/

/-- **Losing a justification does not establish its negation.** A withdrawal neither creates nor
removes a `conflict`, with the same evidence. -/
theorem withdraw_never_refutes {I : Iface D E} {w : World E} {c : Candidate D} {t : Token}
    {ev : Evidence} :
    judge I ((Edit.withdraw t).apply w) c = .conflict ev ↔ judge I w c = .conflict ev := by
  rw [judge_conflict_iff, judge_conflict_iff]; rfl

/-- Any token edit (withdraw or assert) leaves `conflict` exactly as it was: only an environment
change (or a different filling) can produce or remove checked contrary evidence. -/
theorem token_edit_conflict_iff {I : Iface D E} {w : World E} {c : Candidate D} {e : Edit E}
    {t : Token} (he : e = .withdraw t ∨ e = .assert t) {ev : Evidence} :
    judge I (e.apply w) c = .conflict ev ↔ judge I w c = .conflict ev := by
  rcases he with rfl | rfl <;> (rw [judge_conflict_iff, judge_conflict_iff]; rfl)

/-- A withdrawal never creates a pruning: it only removes liveness. -/
theorem withdraw_never_prunes {I : Iface D E} {w : World E} {c : Candidate D} {t : Token}
    {bs : List Token} (h : judge I ((Edit.withdraw t).apply w) c = .pruned bs) :
    ∃ bs', judge I w c = .pruned bs' := by
  obtain ⟨h1, h2, _, h3⟩ := judge_pruned h
  have h3' : (c.blockers.filter w.live).isEmpty = false := by
    cases hx : (c.blockers.filter w.live).isEmpty
    · rfl
    · have hall := blockers_empty_iff.1 hx
      have : (c.blockers.filter ((Edit.withdraw t).apply w).live).isEmpty = true := by
        apply blockers_empty_iff.2
        intro b hb
        simp only [Edit.apply, World.set]
        split
        · rfl
        · exact hall b hb
      rw [this] at h3; cases h3
  refine ⟨c.blockers.filter w.live, ?_⟩
  have h2' : I.guard w.env c.filling = true := h2
  unfold judge
  simp [h1, h2', h3']

/-! ## Lookup -/

theorem find_name_self {Ω : List (Iface D E)} (hn : (Ω.map Iface.name).Nodup) {I : Iface D E}
    (hI : I ∈ Ω) : Ω.find? (fun J => J.name == I.name) = some I := by
  induction Ω with
  | nil => cases hI
  | cons J rest ih =>
    rw [List.map_cons, List.nodup_cons] at hn
    rw [List.find?_cons]
    rcases List.mem_cons.1 hI with rfl | h
    · simp
    · have hne : J.name ≠ I.name := fun he => hn.1 (he ▸ List.mem_map.2 ⟨I, h, rfl⟩)
      have hb : (J.name == I.name) = false := by simp [hne]
      simp [hb, ih hn.2 h]

theorem find_self {cl : Closure D E} {I : Iface D E} (hI : I ∈ cl.tpl.Ω) : cl.find I.name = some I :=
  find_name_self cl.tpl.names hI

theorem find_some {cl : Closure D E} {u : Nat} {I : Iface D E} (h : cl.find u = some I) :
    I ∈ cl.tpl.Ω ∧ I.name = u := by
  unfold Closure.find at h
  exact ⟨List.mem_of_find?_eq_some h, by simpa using List.find?_some h⟩


end Nanodregg.Lang.Contextual

/-- Immutable versioned premises: reissuing an identifier never revives its old token.
This deliberately rejects recovery BY IDENTIFIER: Alchourrón–Gärdenfors–Makinson,
On the Logic of Theory Change (1985), p.513, postulate (−6), recovers an old theory after
re-adding the SAME proposition. A new token version is a different premise, so this is a
boundary of that analogy, not a counterexample to AGM's theorem. -/
add_decl_doc Nanodregg.Lang.Contextual.reissue_never_reenables
