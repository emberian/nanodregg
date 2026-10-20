/-
# Lang.Proofs.Contextual.Closure — the three theorem families of the guarded contextual closure

Over every calculus: its data `CalculusData` (`Lang.Contextual.Closure`) and its laws
`CalculusLaws` (here), with the statements over closures (`Derivable`, `Coherent`, …):

* tokens: `reissue_never_reenables`;
* the judgment: `judge_congr` (a status reads only the environment and its dependencies),
  `judge_frame`, `judge_verified_iff`, `judge_conflict_iff`, `provenance_iff` (the bridge from the
  world-free token polynomial to `judge_verified_iff`); the obstruction: `hyp_var_cites`,
  `drop_removes`;
* CONDITIONAL SOUNDNESS: `conditional_soundness`, `derivable_of_wellFilled`,
  `fill_preserves_derivable`, `op_preserves_wellFilled`, `select_requires_available`;
* withdrawal: `withdraw_never_refutes`, `withdraw_never_prunes`, `withdraw_never_refutes_closure`;
* REPAIR CORRECTNESS: `repair_agrees_from_scratch`, `repair_coherent`, `strengthening_sound`,
  `alternative_sound`, `replacement_sound`;
* LOCALITY: `repair_carries_untouched`, `locality`, `repair_rejudged_eq_touched`;
* history: `history_is_prefix` (`Grows`: template fixed, history and owed obligations append-only),
  `executed_prefix_blocks_replan`, `repair_keeps_accepted`;
* the repair log: `repair_rejudged_eq_touched`; sessions: `session_preserves_coherent`,
  `session_preserves_wellFilled`, `fromScratch_wellFilled`;
* boundaries and stability: `consumer_boundary`, `valueGuard_iff`, `stability_class`;
* grounding: `lfpIter_sound`, `unfounded_not_derivable`, `no_facts_no_derivation`.
-/
import Lang.Contextual.Closure

namespace Nanodregg.Lang.Contextual

variable {D : CalculusData} {E : Type}
  {HasTy : List (HoleDecl D.Ctx D.Ty) → D.Ctx → D.Tm → D.Ty → Prop}

/-! ## The laws of a calculus, and the statements over closures -/

/-- The LAWS of a contextual calculus over its data `D` and a typing relation `HasTy`
(`HasTy Ω Ψ M A` is `Ω; Ψ ⊢ M : A`, meta-context `Ω`), each named after the CMTT fact it stands for. -/
structure CalculusLaws (D : CalculusData)
    (HasTy : List (HoleDecl D.Ctx D.Ty) → D.Ctx → D.Tm → D.Ty → Prop) : Prop where
  /-- CMTT's meta-substitution lemma, partial form: the filled holes leave the meta-context. -/
  msubst_lemma : ∀ {Ω : List (HoleDecl D.Ctx D.Ty)} {Γ : D.Ctx} {P : D.Tm} {T : D.Ty}
    (σ : Nat → Option D.Tm), HasTy Ω Γ P T →
    (∀ d ∈ Ω, ∀ M, σ d.name = some M → HasTy [] d.ctx M d.ty) →
    HasTy (Ω.filter fun d => (σ d.name).isNone) Γ (D.msubst σ P) T
  check_sound : ∀ {Ψ : D.Ctx} {M : D.Tm} {A : D.Ty}, D.check Ψ M A = true → HasTy [] Ψ M A
  /-- The checker is complete: a `false` verdict is a refutation of typing, not an omission. -/
  check_complete : ∀ {Ψ : D.Ctx} {M : D.Tm} {A : D.Ty}, HasTy [] Ψ M A → D.check Ψ M A = true
  strengthen_lemma : ∀ {Ψ : D.Ctx} {M : D.Tm} {A : D.Ty} {x : Nat}, HasTy [] Ψ M A →
    D.uses M x = false → HasTy [] (D.drop Ψ x) (D.strengthen x M) A
  strengthen_factor : ∀ {M : D.Tm} {x : Nat}, D.uses M x = false → D.weaken x (D.strengthen x M) = M
  /-- Non-degeneracy of `drop`/`weaken`: a term typed WITHOUT `x`, weakened back, does not use `x`.
  With `hasTy_var`/`uses_var` it refutes both degenerate choices: `uses ≡ false` (refuted by
  `uses_var`) and `drop Ψ _ = Ψ` with `weaken = id` (`drop_removes`). -/
  weaken_avoids : ∀ {Ψ : D.Ctx} {M : D.Tm} {A : D.Ty} {x : Nat}, HasTy [] (D.drop Ψ x) M A →
    D.uses (D.weaken x M) x = false
  /-- The variable rule. -/
  hasTy_var : ∀ {Ψ : D.Ctx} {x : Nat} {A : D.Ty}, D.lookup Ψ x = some A → HasTy [] Ψ (D.var x) A
  /-- A variable uses itself. -/
  uses_var : ∀ {x : Nat}, D.uses (D.var x) x = true

/-- The template types at its closed type under the open interface of its holes. -/
def Template.Typed (tpl : Template D E)
    (HasTy : List (HoleDecl D.Ctx D.Ty) → D.Ctx → D.Tm → D.Ty → Prop) : Prop :=
  HasTy (tpl.Ω.map Iface.decl) tpl.Γ tpl.P tpl.T

/-- A monomial holds in a world: its positive literals live, its negative literals dead. -/
def Monomial.holds (w : World E) (m : List Token × List Token) : Prop :=
  (∀ t ∈ m.1, w.live t = true) ∧ (∀ b ∈ m.2, w.live b = false)

/-- DERIVABILITY: the template with the selected fillings types at its closed type, under the
meta-context of the holes still unfilled. -/
def Derivable (HasTy : List (HoleDecl D.Ctx D.Ty) → D.Ctx → D.Tm → D.Ty → Prop) (cl : Closure D E) :
    Prop :=
  HasTy ((cl.tpl.Ω.map Iface.decl).filter fun d => (cl.sigma d.name).isNone)
    cl.tpl.Γ (D.msubst cl.sigma cl.tpl.P) cl.tpl.T

/-- A hole's selection names a retained candidate whose filling passes the hole's checker. -/
def SlotFilled (I : Iface D E) (s : Slot D) : Prop :=
  ∀ i, s.selected = some i → ∃ c, s.cands[i]? = some c ∧ D.check I.ctx c.filling I.ty = true

/-- Every selection is well filled. -/
def WellFilled (cl : Closure D E) : Prop :=
  ∀ I ∈ cl.tpl.Ω, SlotFilled I (cl.slot I.name)

/-- Every selected candidate's RECORDED status is `verified` (nothing awaits repair). -/
def Settled (cl : Closure D E) : Prop :=
  ∀ I ∈ cl.tpl.Ω, ∀ i, (cl.slot I.name).selected = some i →
    ∃ c, (cl.slot I.name).cands[i]? = some c ∧ c.status = .verified

/-- AVAILABILITY: every support of every selected candidate is live in `w`. -/
def Available (w : World E) (cl : Closure D E) : Prop :=
  ∀ I ∈ cl.tpl.Ω, ∀ c, cl.selectedCand I.name = some c → ∀ t ∈ effSupports I c, w.live t = true

/-- The recorded statuses are the judgment at `w`. -/
def Coherent (w : World E) (cl : Closure D E) : Prop :=
  ∀ I ∈ cl.tpl.Ω, ∀ c ∈ (cl.slot I.name).cands, c.status = judge I w c

/-- The guard is a function of the filling's VALUE only. -/
def ValueGuard {V : Type} (value : D.Tm → V) (g : E → D.Tm → Bool) : Prop :=
  ∃ g' : E → V → Bool, ∀ e t, g e t = g' e (value t)

/-- The guard's verdict is stable under the term map `s`. -/
def StableUnder (g : E → D.Tm → Bool) (s : D.Tm → D.Tm) : Prop :=
  ∀ e t, g e (s t) = g e t

/-- Least-fixpoint grounding: an atom holds iff a well-founded derivation from live facts exists. -/
inductive Derives (R : List Rule) (F : Nat → Bool) : Nat → Prop where
  | fact {x : Nat} : F x = true → Derives R F x
  | rule {r : Rule} : r ∈ R → (∀ y ∈ r.body, Derives R F y) → Derives R F r.head


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

/-- **`drop` removes the hypothesis.** If `x` is a hypothesis of `Ψ` and weakening fixes the
variable `x`, then `x` does not type in `drop Ψ x` (so `drop = id` with `weaken = id` is refuted). -/
theorem drop_removes (L : CalculusLaws D HasTy) {Ψ : D.Ctx} {x : Nat} {A : D.Ty} (hw : D.weaken x (D.var x) = D.var x) :
    ¬ HasTy [] (D.drop Ψ x) (D.var x) A := by
  intro h
  have := L.weaken_avoids h
  rw [hw, L.uses_var] at this
  cases this

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

/-! ## Repair, candidate by candidate -/

theorem judge_restatus {I : Iface D E} {w : World E} {c : Candidate D} {st : Status} :
    judge I w { c with status := st } = judge I w c := rfl

theorem restatus_self (c : Candidate D) : { c with status := c.status } = c := by cases c; rfl

theorem repairPass_fst (w' : World E) (e : Edit E) (I : Iface D E) :
    ∀ (cs : List (Candidate D)) (n : Nat), (repairPass w' e I cs n).1 =
      cs.map fun c => if touches e I c then { c with status := judge I w' c } else c
  | [], _ => rfl
  | c :: cs, n => by
    unfold repairPass
    cases ht : touches e I c <;> simp [ht, repairPass_fst w' e I cs (n + 1)]

theorem repairCands_map (w' : World E) (e : Edit E) (I : Iface D E) (cs : List (Candidate D)) :
    repairCands w' e I cs =
      cs.map fun c => if touches e I c then { c with status := judge I w' c } else c :=
  repairPass_fst w' e I cs 0

/-- The pass's log is exactly the touched indices (offset `n`). -/
theorem repairPass_snd (w' : World E) (e : Edit E) (I : Iface D E) :
    ∀ (cs : List (Candidate D)) (n k : Nat), k ∈ (repairPass w' e I cs n).2 ↔
      n ≤ k ∧ ∃ c, cs[k - n]? = some c ∧ touches e I c = true
  | [], n, k => by simp [repairPass]
  | c :: cs, n, k => by
    have ih := repairPass_snd w' e I cs (n + 1) k
    unfold repairPass
    by_cases hkn : k = n
    · subst hkn
      cases ht : touches e I c
      · simp only [Bool.false_eq_true, if_false, ih]
        constructor
        · rintro ⟨h, -⟩; omega
        · rintro ⟨-, c', hc', ht'⟩
          simp at hc'; subst hc'; rw [ht] at ht'; cases ht'
      · simp [ht]
    · have hsh : ∀ (P : Prop), (n ≤ k ∧ P) ↔ (n + 1 ≤ k ∧ P) := by
        intro P; constructor <;> rintro ⟨h, hp⟩ <;> exact ⟨by omega, hp⟩
      cases ht : touches e I c
      · simp only [Bool.false_eq_true, if_false, ih]
        constructor
        · rintro ⟨h, c', hc', ht'⟩
          refine ⟨by omega, c', ?_, ht'⟩
          have : k - n = (k - (n + 1)) + 1 := by omega
          rw [this]; simpa using hc'
        · rintro ⟨h, c', hc', ht'⟩
          have h' : n + 1 ≤ k := by omega
          refine ⟨h', c', ?_, ht'⟩
          have : k - n = (k - (n + 1)) + 1 := by omega
          rw [this] at hc'; simpa using hc'
      · simp only [if_true, List.mem_cons, ih]
        constructor
        · rintro (h | ⟨h, c', hc', ht'⟩)
          · exact absurd h hkn
          · refine ⟨by omega, c', ?_, ht'⟩
            have : k - n = (k - (n + 1)) + 1 := by omega
            rw [this]; simpa using hc'
        · rintro ⟨h, c', hc', ht'⟩
          refine Or.inr ⟨by omega, c', ?_, ht'⟩
          have : k - n = (k - (n + 1)) + 1 := by omega
          rw [this] at hc'; simpa using hc'

/-- **Incremental = from scratch, at the candidate list.** On a coherent hole, re-judging only the
touched candidates gives exactly the list with EVERY candidate re-judged at the new world. -/
theorem repairCands_eq {I : Iface D E} {w : World E} {e : Edit E} {cs : List (Candidate D)}
    (hs : ∀ c ∈ cs, c.status = judge I w c) :
    repairCands (e.apply w) e I cs = cs.map fun c => { c with status := judge I (e.apply w) c } := by
  rw [repairCands_map]
  apply List.map_congr_left
  intro c hc
  cases ht : touches e I c
  · simp only [Bool.false_eq_true, if_false]
    rw [judge_frame ht, ← hs c hc]
  · rfl

theorem repairHole_cands (w' : World E) (e : Edit E) (I : Iface D E) (s : Slot D) :
    (repairHole w' e I s).1.cands = repairCands w' e I s.cands := by
  unfold repairHole
  cases hT : holeTouched e I s
  · simp only [if_true]
    have hno : ∀ c ∈ s.cands, touches e I c = false := by
      intro c hc
      cases ht : touches e I c
      · rfl
      · simp only [holeTouched, Bool.or_eq_false_iff, List.any_eq_false] at hT
        exact absurd ht (hT.2 c hc)
    rw [repairCands_map]
    conv => lhs; rw [← List.map_id s.cands]
    apply List.map_congr_left
    intro c hc; simp [hno c hc]
  · simp only [Bool.true_eq_false, if_false]
    split <;> rfl

theorem repair_slot {w : World E} {e : Edit E} {cl : Closure D E} {I : Iface D E}
    (hI : I ∈ cl.tpl.Ω) :
    (repair w e cl).1.slot I.name = (repairHole (e.apply w) e I (cl.slot I.name)).1 := by
  simp [repair, find_self hI]

/-- **REPAIR CORRECTNESS.** On a coherent closure, the observable after `repair e` (every retained
candidate's status, hole by hole, in order) equals the from-scratch analysis of the template and
the same retained candidates at the new world. -/
theorem repair_agrees_from_scratch {w : World E} {e : Edit E} {cl : Closure D E}
    (hc : Coherent w cl) :
    observe (repair w e cl).1 =
      observe (fromScratch (e.apply w) cl.tpl fun u => (cl.slot u).cands) := by
  unfold observe
  apply List.map_congr_left
  intro I hI
  have hI' : I ∈ cl.tpl.Ω := hI
  rw [repair_slot (w := w) (e := e) hI', repairHole_cands, repairCands_eq (hc I hI')]
  simp [fromScratch, find_name_self cl.tpl.names hI']

/-- Repair re-establishes coherence at the new world. -/
theorem repair_coherent {w : World E} {e : Edit E} {cl : Closure D E} (hc : Coherent w cl) :
    Coherent (e.apply w) (repair w e cl).1 := by
  intro I hI c hc'
  have hI' : I ∈ cl.tpl.Ω := hI
  rw [repair_slot (w := w) (e := e) hI', repairHole_cands, repairCands_eq (hc I hI')] at hc'
  obtain ⟨c0, _, rfl⟩ := List.mem_map.1 hc'
  rfl

theorem fromScratch_coherent (w : World E) (tpl : Template D E) (cands : Nat → List (Candidate D)) :
    Coherent w (fromScratch w tpl cands) := by
  intro I hI c hc
  simp only [fromScratch, find_name_self tpl.names hI] at hc
  obtain ⟨c0, _, rfl⟩ := List.mem_map.1 hc
  rfl

/-- **LOCALITY, candidate by candidate.** Repair carries an untouched candidate unchanged (the same
record, status included): it is not re-judged. -/
theorem repair_carries_untouched {w : World E} {e : Edit E} {cl : Closure D E} {I : Iface D E}
    (hI : I ∈ cl.tpl.Ω) {i : Nat} {c : Candidate D} (hci : (cl.slot I.name).cands[i]? = some c)
    (ht : touches e I c = false) : ((repair w e cl).1.slot I.name).cands[i]? = some c := by
  rw [repair_slot hI, repairHole_cands]
  simp [repairCands_map, List.getElem?_map, hci, ht]

/-- **LOCALITY, the boundary theorem.** A token edit whose token is no dependency of any retained
candidate and backs no hole hypothesis leaves the closure exactly as it was, with no outcome and an
empty repair log (the log is emitted by the same branch of `repairPass` that re-judges). -/
theorem locality {w : World E} {t : Token} {e : Edit E} (he : e = .withdraw t ∨ e = .assert t)
    {cl : Closure D E}
    (hfree : ∀ I ∈ cl.tpl.Ω, (∀ h ∈ I.hyps, h.2 ≠ t) ∧ ∀ c ∈ (cl.slot I.name).cands, t ∉ deps I c) :
    (repair w e cl).1 = cl ∧ (repair w e cl).2.1 = [] ∧ (repair w e cl).2.2 = [] := by
  have hT : ∀ I ∈ cl.tpl.Ω, holeTouched e I (cl.slot I.name) = false := by
    intro I hI
    obtain ⟨hh, hd⟩ := hfree I hI
    simp only [holeTouched, Bool.or_eq_false_iff, List.any_eq_false]
    refine ⟨?_, ?_⟩
    · rcases he with rfl | rfl
      · simp only [hypOf, Option.isSome_map, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none,
          List.find?_eq_none, decide_eq_true_eq]
        exact fun h hm => hh h hm
      · rfl
    · intro c hc
      rcases he with rfl | rfl <;> simp [touches, hd c hc]
  have hR : ∀ I ∈ cl.tpl.Ω, repairHole (e.apply w) e I (cl.slot I.name) = (cl.slot I.name, none) := by
    intro I hI; simp [repairHole, hT I hI]
  have houts : (repair w e cl).2.1 = [] := by
    simp only [repair, List.filterMap_eq_nil_iff]
    intro I hI; simp [hR I hI]
  have hlog : (repair w e cl).2.2 = [] := by
    simp only [repair, List.flatMap_eq_nil_iff, List.map_eq_nil_iff]
    intro I hI; simp [rejudgedIn, hT I hI]
  refine ⟨?_, houts, hlog⟩
  have hslot : (repair w e cl).1.slot = cl.slot := by
    funext u
    simp only [repair]
    split
    · rename_i I hf
      obtain ⟨hI, rfl⟩ := find_some hf
      rw [hR I hI]
    · rfl
  have hhist : (repair w e cl).1.hist = cl.hist := by
    have : (repair w e cl).1.hist = cl.hist ++ (repair w e cl).2.1.filterMap Outcome.event := rfl
    rw [this, houts]; simp
  cases cl
  simp only [repair] at hslot hhist ⊢
  simp only [hslot] at *
  congr

/-- Withdrawal, at the closure: after a withdrawal and repair, a `conflict` in a coherent closure
was already a `conflict`, with the same evidence, at the same index. -/
theorem withdraw_never_refutes_closure {w : World E} {t : Token} {cl : Closure D E}
    (hc : Coherent w cl) {I : Iface D E} (hI : I ∈ cl.tpl.Ω) {i : Nat} {c' : Candidate D}
    {ev : Evidence} (h : ((withdraw w t cl).1.slot I.name).cands[i]? = some c')
    (hev : c'.status = .conflict ev) :
    ∃ c, (cl.slot I.name).cands[i]? = some c ∧ c.status = .conflict ev := by
  unfold withdraw at h
  rw [repair_slot hI, repairHole_cands, repairCands_eq (hc I hI), List.getElem?_map] at h
  cases hci : (cl.slot I.name).cands[i]? with
  | none => simp [hci] at h
  | some c =>
    simp only [hci, Option.map_some, Option.some.injEq] at h
    subst h
    refine ⟨c, rfl, ?_⟩
    rw [hc I hI c (List.mem_of_getElem? hci)]
    exact withdraw_never_refutes.1 hev

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

/-! ## The operations: frames -/

theorem update_at {cl : Closure D E} {u v : Nat} {s : Slot D} :
    cl.update u s v = if v = u then s else cl.slot v := rfl

theorem propose_ok {w : World E} {u : Nat} {c : Candidate D} {cl : Closure D E}
    {r : Closure D E × Nat} (h : propose w u c cl = .ok r) :
    ∃ I, cl.find u = some I ∧ r.2 = (cl.slot u).cands.length ∧ r.1.tpl = cl.tpl ∧
      r.1.owed = cl.owed ∧ r.1.hist = cl.hist ++ [.proposed u (cl.slot u).cands.length] ∧
      r.1.slot = cl.update u ⟨(cl.slot u).cands ++ [{ c with status := judge I w c }],
        (cl.slot u).selected, (cl.slot u).accepted⟩ := by
  unfold propose at h
  dsimp only at h
  split at h
  · simp at h
  · rename_i I hf
    simp only [Except.ok.injEq] at h
    subst h
    exact ⟨I, hf, rfl, rfl, rfl, rfl, rfl⟩

theorem select_ok {w : World E} {p : Party} {u i : Nat} {cl cl' : Closure D E}
    (h : select w p u i cl = .ok cl') :
    ∃ I c, cl.find u = some I ∧ p = I.chooser ∧ (cl.slot u).accepted = false ∧
      (cl.slot u).cands[i]? = some c ∧ judge I w c = .verified ∧
      cl'.tpl = cl.tpl ∧ cl'.owed = cl.owed ∧ cl'.hist = cl.hist ++ [.selected u i] ∧
      cl'.slot = cl.update u ⟨(cl.slot u).cands.set i { c with status := .verified },
        some i, (cl.slot u).accepted⟩ := by
  unfold select at h
  dsimp only at h
  split at h
  · simp at h
  rename_i I hf
  split at h
  · simp at h
  rename_i hp
  split at h
  · simp at h
  rename_i hacc
  split at h
  · simp at h
  rename_i c hc
  split at h
  · rename_i hv
    simp only [Except.ok.injEq] at h
    subst h
    refine ⟨I, c, hf, by simpa using hp, by simpa using hacc, hc, hv, rfl, rfl, rfl, ?_⟩
    simp only [hv]
  · simp at h

theorem deselect_ok {p : Party} {u : Nat} {cl cl' : Closure D E} (h : deselect p u cl = .ok cl') :
    ∃ I, cl.find u = some I ∧ p = I.chooser ∧ (cl.slot u).accepted = false ∧
      cl'.tpl = cl.tpl ∧ cl'.owed = cl.owed ∧ cl'.hist = cl.hist ++ [.deselected u] ∧
      cl'.slot = cl.update u ⟨(cl.slot u).cands, none, (cl.slot u).accepted⟩ := by
  unfold deselect at h
  dsimp only at h
  split at h
  · simp at h
  rename_i I hf
  split at h
  · simp at h
  rename_i hp
  split at h
  · simp at h
  rename_i hacc
  simp only [Except.ok.injEq] at h
  subst h
  exact ⟨I, hf, by simpa using hp, by simpa using hacc, rfl, rfl, rfl, rfl⟩

theorem accept_ok {w : World E} {p : Party} {u : Nat} {cl cl' : Closure D E}
    (h : accept w p u cl = .ok cl') :
    ∃ I i c, cl.find u = some I ∧ p = I.acceptor ∧ (cl.slot u).accepted = false ∧
      (cl.slot u).selected = some i ∧ (cl.slot u).cands[i]? = some c ∧ judge I w c = .verified ∧
      cl'.tpl = cl.tpl ∧ cl'.owed = cl.owed ++ [.settle u i] ∧
      cl'.hist = cl.hist ++ [.accepted u i] ∧
      cl'.slot = cl.update u ⟨(cl.slot u).cands, (cl.slot u).selected, true⟩ := by
  unfold accept at h
  dsimp only at h
  split at h
  · simp at h
  rename_i I hf
  split at h
  · simp at h
  rename_i hp
  split at h
  · simp at h
  rename_i hacc
  split at h
  · simp at h
  rename_i i hsel
  split at h
  · simp at h
  rename_i c hc
  split at h
  · rename_i hv
    simp only [Except.ok.injEq] at h
    subst h
    exact ⟨I, i, c, hf, by simpa using hp, by simpa using hacc, hsel, hc, hv, rfl, rfl, rfl, rfl⟩
  · simp at h

theorem prune_ok {w : World E} {p : Party} {u i : Nat} {r : Token} {cl cl' : Closure D E}
    (h : prune w p u i r cl = .ok cl') :
    ∃ I c, cl.find u = some I ∧ p = I.chooser ∧
      ¬ ((cl.slot u).accepted = true ∧ (cl.slot u).selected = some i) ∧
      (cl.slot u).cands[i]? = some c ∧
      cl'.tpl = cl.tpl ∧ cl'.owed = cl.owed ∧ cl'.hist = cl.hist ++ [.pruned u i] ∧
      cl'.slot = cl.update u ⟨(cl.slot u).cands.set i
          { c with blockers := c.blockers ++ [r],
                   status := judge I w { c with blockers := c.blockers ++ [r] } },
        (cl.slot u).selected, (cl.slot u).accepted⟩ := by
  unfold prune at h
  dsimp only at h
  split at h
  · simp at h
  rename_i I hf
  split at h
  · simp at h
  rename_i hp
  split at h
  · simp at h
  rename_i hacc
  split at h
  · simp at h
  rename_i c hc
  simp only [Except.ok.injEq] at h
  subst h
  exact ⟨I, c, hf, by simpa using hp, hacc, hc, rfl, rfl, rfl, rfl⟩

theorem rejudge_eq (w : World E) (u i : Nat) (cl : Closure D E) :
    rejudge w u i cl = cl ∨ ∃ I c, cl.find u = some I ∧ (cl.slot u).cands[i]? = some c ∧
      (rejudge w u i cl).tpl = cl.tpl ∧ (rejudge w u i cl).owed = cl.owed ∧
      (rejudge w u i cl).hist = cl.hist ∧
      (rejudge w u i cl).slot = cl.update u ⟨(cl.slot u).cands.set i { c with status := judge I w c },
        (cl.slot u).selected, (cl.slot u).accepted⟩ := by
  unfold rejudge
  split
  · exact Or.inl rfl
  · rename_i I hf
    dsimp only
    split
    · exact Or.inl rfl
    · rename_i c hc
      exact Or.inr ⟨I, c, hf, hc, rfl, rfl, rfl, rfl⟩

theorem fill_ok {w : World E} {p : Party} {u : Nat} {c : Candidate D} {cl cl' : Closure D E}
    (h : fill w p u c cl = .ok cl') :
    ∃ cl₁ i, propose w u c cl = .ok (cl₁, i) ∧ select w p u i cl₁ = .ok cl' := by
  unfold fill at h
  split at h
  · simp at h
  · rename_i cl₁ i hp
    exact ⟨cl₁, i, hp, h⟩

/-- The common frame of every operation: the template never changes, the history and the owed
obligations only grow at the end. -/
structure Grows (cl cl' : Closure D E) : Prop where
  tpl : cl'.tpl = cl.tpl
  hist : ∃ sfx, cl'.hist = cl.hist ++ sfx
  owed : ∃ sfx, cl'.owed = cl.owed ++ sfx

theorem Grows.trans {a b c : Closure D E} (h₁ : Grows a b) (h₂ : Grows b c) : Grows a c := by
  obtain ⟨t1, ⟨s1, h1⟩, ⟨o1, p1⟩⟩ := h₁
  obtain ⟨t2, ⟨s2, h2⟩, ⟨o2, p2⟩⟩ := h₂
  exact ⟨t2.trans t1, ⟨s1 ++ s2, by rw [h2, h1, List.append_assoc]⟩,
    ⟨o1 ++ o2, by rw [p2, p1, List.append_assoc]⟩⟩

theorem repair_grows (w : World E) (e : Edit E) (cl : Closure D E) : Grows cl (repair w e cl).1 :=
  ⟨rfl, ⟨_, rfl⟩, ⟨[], by simp [repair]⟩⟩

theorem propose_grows {w : World E} {u : Nat} {c : Candidate D} {cl : Closure D E}
    {r : Closure D E × Nat} (h : propose w u c cl = .ok r) : Grows cl r.1 := by
  obtain ⟨I, -, -, ht, ho, hh, -⟩ := propose_ok h
  exact ⟨ht, ⟨_, hh⟩, ⟨[], by simp [ho]⟩⟩

theorem select_grows {w : World E} {p : Party} {u i : Nat} {cl cl' : Closure D E}
    (h : select w p u i cl = .ok cl') : Grows cl cl' := by
  obtain ⟨I, c, -, -, -, -, -, ht, ho, hh, -⟩ := select_ok h
  exact ⟨ht, ⟨_, hh⟩, ⟨[], by simp [ho]⟩⟩

/-- **The history is a prefix.** Every operation appends to the accepted history and to the owed
obligations; nothing earlier moves; the template is never rewritten. -/
theorem history_is_prefix {w : World E} {op : Op D E} {cl cl' : Closure D E}
    (h : op.run w cl = .ok cl') : Grows cl cl' := by
  cases op with
  | propose u c =>
    simp only [Op.run] at h
    cases hp : propose w u c cl with
    | error r => rw [hp] at h; simp [Except.map] at h
    | ok r =>
      rw [hp] at h
      simp only [Except.map, Except.ok.injEq] at h
      subst h
      exact propose_grows hp
  | select p u i => exact select_grows h
  | fill p u c =>
    obtain ⟨cl₁, i, hp, hs⟩ := fill_ok h
    exact (propose_grows hp).trans (select_grows hs)
  | deselect p u =>
    obtain ⟨I, -, -, -, ht, ho, hh, -⟩ := deselect_ok h
    exact ⟨ht, ⟨_, hh⟩, ⟨[], by simp [ho]⟩⟩
  | accept p u =>
    obtain ⟨I, i, c, -, -, -, -, -, -, ht, ho, hh, -⟩ := accept_ok h
    exact ⟨ht, ⟨_, hh⟩, ⟨_, ho⟩⟩
  | prune p u i r =>
    obtain ⟨I, c, -, -, -, -, ht, ho, hh, -⟩ := prune_ok h
    exact ⟨ht, ⟨_, hh⟩, ⟨[], by simp [ho]⟩⟩
  | rejudge u i =>
    simp only [Op.run, Except.ok.injEq] at h
    subst h
    rcases rejudge_eq w u i cl with h | ⟨I, c, -, -, ht, ho, hh, -⟩
    · rw [h]; exact ⟨rfl, ⟨[], by simp⟩, ⟨[], by simp⟩⟩
    · exact ⟨ht, ⟨[], by simp [hh]⟩, ⟨[], by simp [ho]⟩⟩
  | edit e =>
    simp only [Op.run, Except.ok.injEq] at h
    subst h
    exact repair_grows w e cl

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

/-! ## The repair log -/

theorem iface_eq_of_name {cl : Closure D E} {I J : Iface D E} (hI : I ∈ cl.tpl.Ω)
    (hJ : J ∈ cl.tpl.Ω) (hn : J.name = I.name) : J = I := by
  have h1 := find_self (cl := cl) hI
  have h2 := find_self (cl := cl) hJ
  rw [hn, h1] at h2
  exact (Option.some.inj h2).symm

/-- **LOCALITY, as work done.** The repair log names exactly the touched candidates of the closure:
`(I.name, k)` is logged iff candidate `k` of hole `I` is touched by the edit. An untouched candidate
is never re-judged (a recompute-all repair logs every candidate and fails this). -/
theorem repair_rejudged_eq_touched {w : World E} {e : Edit E} {cl : Closure D E} {I : Iface D E}
    (hI : I ∈ cl.tpl.Ω) (k : Nat) :
    (I.name, k) ∈ (repair w e cl).2.2 ↔
      ∃ c, (cl.slot I.name).cands[k]? = some c ∧ touches e I c = true := by
  simp only [repair, List.mem_flatMap, List.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨J, hJ, k', hk', hn, rfl⟩
    obtain rfl := iface_eq_of_name hI hJ hn
    unfold rejudgedIn at hk'
    split at hk'
    · cases hk'
    · simpa using (repairPass_snd _ e J _ 0 k').1 hk'
  · rintro ⟨c, hc, ht⟩
    refine ⟨I, hI, k, ?_, rfl, rfl⟩
    unfold rejudgedIn
    have hT : holeTouched e I (cl.slot I.name) = true := by
      simp only [holeTouched, Bool.or_eq_true, List.any_eq_true]
      exact Or.inr ⟨c, List.mem_of_getElem? hc, ht⟩
    simp only [hT, Bool.true_eq_false, if_false]
    exact (repairPass_snd _ e I _ 0 k).2 ⟨Nat.zero_le _, c, by simpa using hc, ht⟩

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
