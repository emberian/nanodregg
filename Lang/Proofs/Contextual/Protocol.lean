/-
# Lang.Proofs.Contextual.Protocol — the theory of open protocols (lane PROTOCOL)

The four theorem families of the proposal's document 2 section 9, over `Lang.Contextual.Protocol`:

* CONTEXTUAL COMPLETION: `fill_preserves_hasProt` (a filling satisfying the hole's interface:
  index, context, tokens, result, obligations, chooser, acceptance; preserves the judgment);
  `fill_skips_others`, `others_hole_untypable` (DESIGN RULES, stated as theorems so they are
  checked: `fill` restricts to `.me` holes by definition and the hole rule requires `.me`).
* INTERPRETATION OF SUBSTITUTION: `fold_fusion`, `fold_subst`, `interpret_fill` (interpreting
  `P[σ]` IS interpreting the template with `σ` in the environment), via fusion.
* SELECTIVE REPAIR: `locality`, `repair_agrees_from_scratch`, `repair_residual`, `repair_reuses`.
* ADMISSION AND HISTORY PRESERVATION: `hasProt_reach` (subject reduction: the AFFINE token account
  and the obligations of every prefix; `at_most_once`), `resubst_preserves_started` /
  `Open.resubst_wf` (re-substituting an unentered hole preserves the accepted history and its
  obligations), `admits_local`, `commit_once`; the teeth for the guard are in the negotiation
  (`Negotiation.lost_reply_blocks_replan`, `answered_blocks_replan`, `guard_stricter_than_wf`).

And document 2 sections 4 and 5: `Coin.foresight_iff_names_separate` (a hole separates from an
interaction exactly when its NAME does not depend on the response: a naming discipline, not a fact
of the calculus), `Coin.no_foresight`, `Coin.response_indexed_names_have_foresight`,
`Coin.response_dependent_succeeds`; the scalar illustration `separate_witnesses_bounded`. The scalar
matchers and the private Negotiation `World` went with PROT-6, replaced by Std.offer's deployed fuse
(`Lang/StdOffer.lean`). The relation to nano's own
free program over effects: `nano_runs_iff`, `nano_interp_agrees`, `nano_interp_runs`.
-/
import Lang.Proofs.Contextual.ProtocolTyping

namespace Nanodregg.Lang.Contextual.Protocol

section
variable {Ix : Type} {S : Sig Ix} {Hole : Ix → Type} {A : Ix → Type}
variable {Tok Fact Ob : Type}

/-! ## Bags -/

theorem SubBag.refl [DecidableEq Tok] (Δ : List Tok) : SubBag Δ Δ := fun _ => Nat.le_refl _

theorem SubBag.trans [DecidableEq Tok] {Δ₁ Δ₂ Δ₃ : List Tok} (h₁ : SubBag Δ₁ Δ₂)
    (h₂ : SubBag Δ₂ Δ₃) : SubBag Δ₁ Δ₃ := fun t => Nat.le_trans (h₁ t) (h₂ t)

theorem SubBag.mem [DecidableEq Tok] {Δ₁ Δ₂ : List Tok} (h : SubBag Δ₁ Δ₂) {t : Tok}
    (ht : t ∈ Δ₁) : t ∈ Δ₂ :=
  List.count_pos_iff.mp (Nat.lt_of_lt_of_le (List.count_pos_iff.mpr ht) (h t))

theorem SubBag.erase [DecidableEq Tok] {Δ₁ Δ₂ : List Tok} (h : SubBag Δ₁ Δ₂) (t : Tok) :
    SubBag (Δ₁.erase t) (Δ₂.erase t) := by
  intro a
  rw [List.count_erase, List.count_erase]
  exact Nat.sub_le_sub_right (h a) _

/-! ## Contextual completion -/

/-- Weakening: more facts, a weaker postcondition, more permitted obligations, more tokens. -/
theorem HasProt.weaken [DecidableEq Tok] {sp : Spec S Tok Fact Ob}
    {Ω : Ctx S Hole A Tok Fact Ob} {Γ Γ' : List Fact} {Q Q' : (j : Ix) → A j → Prop}
    {Φ Φ' : List Ob} (hΓ : ∀ f ∈ Γ, f ∈ Γ') (hQ : ∀ j a, Q j a → Q' j a)
    (hΦ : ∀ o ∈ Φ, o ∈ Φ') {Δ Δ' : List Tok} {i : Ix} {P : Prot S Hole A i}
    (h : HasProt sp Ω Γ Q Φ Δ P) (hΔ : SubBag Δ Δ') : HasProt sp Ω Γ' Q' Φ' Δ' P := by
  induction h generalizing Δ' with
  | ret a hq => exact .ret a (hQ _ _ hq)
  | call op k hc hr he _ ih =>
    exact .call op k hc (fun f hf => hΓ f (hr f hf)) (fun o ho => hΦ o (he o ho))
      (fun r => ih r hΔ)
  | spend op k t hc ht hr he _ ih =>
    exact .spend op k t hc (hΔ.mem ht) (fun f hf => hΓ f (hr f hf)) (fun o ho => hΦ o (he o ho))
      (fun r => ih r (hΔ.erase t))
  | hole h I hI hp hctx hneed hpost howes =>
    exact .hole h I hI hp (fun f hf => hΓ f (hctx f hf)) (hneed.trans hΔ)
      (fun j a ha => hQ j a (hpost j a ha)) (fun o ho => hΦ o (howes o ho))

/-- Substituting an interface-respecting substitution preserves the judgment. -/
theorem subst_preserves_hasProt [DecidableEq Tok] {sp : Spec S Tok Fact Ob}
    {Ω : Ctx S Hole A Tok Fact Ob} {σ : Subst S Hole A} (hσ : SubstOK sp Ω σ)
    {Γ : List Fact} {Q : (j : Ix) → A j → Prop} {Φ : List Ob} {Δ : List Tok} {i : Ix}
    {P : Prot S Hole A i} (h : HasProt sp Ω Γ Q Φ Δ P) : HasProt sp Ω Γ Q Φ Δ (subst σ P) := by
  induction h with
  | ret a hq => exact .ret a hq
  | call op k hc hr he _ ih => exact .call op _ hc hr he ih
  | spend op k t hc ht hr he _ ih => exact .spend op _ t hc ht hr he ih
  | @hole Δ i h I hI hp hctx hneed hpost howes =>
    show HasProt sp Ω Γ Q Φ Δ (match σ i h with | some f => f | none => .hole h)
    cases hs : σ i h with
    | none => exact .hole h I hI hp hctx hneed hpost howes
    | some f =>
      obtain ⟨I', hI', _, hf, _⟩ := hσ i h f hs
      rw [hI] at hI'
      cases hI'
      exact hf.weaken hctx hpost howes hneed

/-- Restricting to the `.me` holes keeps a substitution interface-respecting. -/
theorem SubstOK.mine [DecidableEq Tok] {sp : Spec S Tok Fact Ob} {Ω : Ctx S Hole A Tok Fact Ob}
    {σ : Subst S Hole A} (hσ : SubstOK sp Ω σ) : SubstOK sp Ω (σ.mine Ω) := by
  intro i h f hs
  unfold Subst.mine at hs
  split at hs
  · split at hs
    · exact hσ i h f hs
    · cases hs
  · cases hs

/-- **Contextual completion** (family 1): filling the holes of a judged protocol with fillings that
satisfy their interfaces preserves the protocol's judgment, at the same facts, tokens, result
contract and obligation bound. -/
theorem fill_preserves_hasProt [DecidableEq Tok] {sp : Spec S Tok Fact Ob}
    {Ω : Ctx S Hole A Tok Fact Ob} {σ : Subst S Hole A} (hσ : SubstOK sp Ω σ)
    {Γ : List Fact} {Q : (j : Ix) → A j → Prop} {Φ : List Ob} {Δ : List Tok} {i : Ix}
    {P : Prot S Hole A i} (h : HasProt sp Ω Γ Q Φ Δ P) :
    HasProt sp Ω Γ Q Φ Δ (fill Ω σ P) :=
  subst_preserves_hasProt hσ.mine h

/-- **Chooser, a design rule**: `fill` never fills a hole `Ω` declares chosen by `.other`, whatever `σ`
offers. True by the definition of `Subst.mine`; stated so the rule is checked, not as a finding. -/
theorem fill_skips_others {Ω : Ctx S Hole A Tok Fact Ob} (σ : Subst S Hole A) {i : Ix}
    {h : Hole i} {I : Iface S Hole A Tok Fact Ob i} (hI : Ω i h = some I)
    (hp : I.chooser = .other) : fill Ω σ (.hole h) = .hole h := by
  simp [fill, subst, Subst.mine, hI, hp]

/-- **Chooser, a design rule**: an `.other` hole is not a judged protocol, because the `hole` rule
of `HasProt` requires `.me`. Stated so the rule is checked, not as a finding. -/
theorem others_hole_untypable [DecidableEq Tok] {sp : Spec S Tok Fact Ob}
    {Ω : Ctx S Hole A Tok Fact Ob} {Γ : List Fact} {Q : (j : Ix) → A j → Prop} {Φ : List Ob}
    {Δ : List Tok} {i : Ix} {h : Hole i} {I : Iface S Hole A Tok Fact Ob i}
    (hI : Ω i h = some I) (hp : I.chooser = .other) : ¬ HasProt sp Ω Γ Q Φ Δ (.hole h) := by
  intro hh
  cases hh with
  | hole _ I' hI' hp' =>
    rw [hI] at hI'
    cases hI'
    rw [hp] at hp'
    cases hp'

/-- On interface-respecting substitutions `fill` is plain substitution. -/
theorem fill_eq_subst [DecidableEq Tok] {sp : Spec S Tok Fact Ob} {Ω : Ctx S Hole A Tok Fact Ob}
    {σ : Subst S Hole A} (hσ : SubstOK sp Ω σ) {i : Ix} (P : Prot S Hole A i) :
    fill Ω σ P = subst σ P := by
  have : σ.mine Ω = σ := by
    funext j h
    unfold Subst.mine
    cases hs : σ j h with
    | none => split <;> (try split) <;> rfl
    | some f =>
      obtain ⟨I, hI, hp, _⟩ := hσ j h f hs
      simp [hI, hp]
  simp [fill, this]

/-! ## Holes -/

/-- `holes` computes exactly the holes that occur. -/
theorem mem_holes_iff (fin : Finite S) {i : Ix} (P : Prot S Hole A i) (j : Ix) (h : Hole j) :
    (⟨j, h⟩ : Σ j, Hole j) ∈ holes fin P ↔ Occurs P j h := by
  induction P with
  | ret a =>
    simp only [holes, List.not_mem_nil, false_iff]
    intro ho; cases ho
  | call op k ih =>
    simp only [holes, List.mem_flatMap, List.mem_attach, true_and]
    constructor
    · rintro ⟨⟨r, _⟩, hm⟩
      exact .call r ((ih r).mp hm)
    · intro ho
      cases ho with
      | call r ho => exact ⟨⟨r, fin.complete op r⟩, (ih r).mpr ho⟩
  | @hole i h' =>
    simp only [holes, List.mem_singleton]
    constructor
    · intro he
      cases he
      exact .here h
    · intro ho
      cases ho
      rfl

/-- A substitution that fills no occurring hole leaves the protocol alone. -/
theorem subst_away {σ : Subst S Hole A} {i : Ix} (P : Prot S Hole A i)
    (hσ : ∀ j h, Occurs P j h → σ j h = none) : subst σ P = P := by
  induction P with
  | ret a => rfl
  | call op k ih =>
    show Prot.call op (fun r => subst σ (k r)) = _
    congr 1
    funext r
    exact ih r fun j h ho => hσ j h (.call r ho)
  | @hole i h =>
    show (match σ i h with | some f => f | none => .hole h) = _
    rw [hσ i h (.here h)]

/-! ## Interpretation of substitution -/

/-- **Fold fusion**: an algebra morphism commutes with the fold (the carriers may differ). -/
theorem fold_fusion {C D : Ix → Type} {src : Algebra S Hole A C} {dst : Algebra S Hole A D}
    {φ : (i : Ix) → C i → D i} (hφ : AlgebraHom src dst φ) {i : Ix} (P : Prot S Hole A i) :
    φ i (fold src P) = fold dst P := by
  induction P with
  | ret a => exact hφ.ret a
  | call op k ih =>
    show φ _ (src.call op fun r => fold src (k r)) = dst.call op fun r => fold dst (k r)
    rw [hφ.call]
    congr 1
    funext r
    exact ih r
  | hole h => exact hφ.hole h

/-- Substitution is the fold of the substitution algebra. -/
theorem subst_eq_fold (σ : Subst S Hole A) {i : Ix} (P : Prot S Hole A i) :
    subst σ P = fold (substAlg σ) P := by
  induction P with
  | ret a => rfl
  | call op k ih =>
    show Prot.call op (fun r => subst σ (k r)) = Prot.call op (fun r => fold (substAlg σ) (k r))
    congr 1
    funext r
    exact ih r
  | hole h => rfl

/-- Reading a substituted protocol is a morphism from the substitution algebra to the template's
reading under the environment. -/
theorem underHom {C : Ix → Type} (alg : Algebra S Hole A C) (σ : Subst S Hole A) :
    AlgebraHom (substAlg σ) (underAlg alg σ) (fun _ P => fold alg P) where
  ret := fun _ => rfl
  call := fun _ _ => rfl
  hole := fun {i} h => by
    show fold alg (match σ i h with | some f => f | none => .hole h) =
      (match σ i h with | some f => fold alg f | none => alg.hole h)
    cases σ i h <;> rfl

/-- **The substitution lemma for readings**: reading `P[σ]` is reading the template `P` with
`σ` bound in the environment. Proved by fusion. -/
theorem fold_subst {C : Ix → Type} (alg : Algebra S Hole A C) (σ : Subst S Hole A) {i : Ix}
    (P : Prot S Hole A i) : fold alg (subst σ P) = fold (underAlg alg σ) P := by
  rw [subst_eq_fold]
  exact fold_fusion (underHom alg σ) P

/-- **Interpretation of substitution** (family 2): running the instantiated protocol against an
environment is running its template with the substitution in the environment. -/
theorem interpret_fill {St : Ix → Type} (H : Handler S St) (σ : Subst S Hole A) {i : Ix}
    (P : Prot S Hole A i) : interpret H (subst σ P) = interpretUnder H σ P :=
  fold_subst (execAlgebra H) σ P

/-! ## Paths and prefixes -/

theorem runs_reach {i : Ix} {P : Prot S Hole A i} {t : Trace S} {j : Ix} {a : A j}
    (h : Runs P t j a) : Reach P t ⟨j, .ret a⟩ := by
  induction h with
  | ret a => exact .here _
  | call r _ ih => exact .call r ih

theorem reach_append {i : Ix} {P : Prot S Hole A i} {t₁ t₂ : Trace S}
    {R₀ R : Σ j, Prot S Hole A j} (h₁ : Reach P t₁ R₀) (h₂ : Reach R₀.2 t₂ R) :
    Reach P (t₁ ++ t₂) R := by
  induction h₁ with
  | here => exact h₂
  | call r _ ih => exact .call r (ih h₂)

/-- A prefix of the template is a prefix of every instance, leaving the instance's residual. -/
theorem reach_subst (σ : Subst S Hole A) {i : Ix} {P : Prot S Hole A i} {t : Trace S}
    {R : Σ j, Prot S Hole A j} (h : Reach P t R) : Reach (subst σ P) t ⟨R.1, subst σ R.2⟩ := by
  induction h with
  | here => exact .here _
  | call r _ ih => exact .call r ih

/-- A path that enters a filled hole: the template's prefix to the hole, then the filling's. -/
theorem reach_through_hole {σ : Subst S Hole A} {i : Ix} {P : Prot S Hole A i} {t₁ t₂ : Trace S}
    {j : Ix} {h : Hole j} {f : Prot S Hole A j} {R : Σ j, Prot S Hole A j}
    (h₁ : Reach P t₁ ⟨j, .hole h⟩) (hs : σ j h = some f) (h₂ : Reach f t₂ R) :
    Reach (subst σ P) (t₁ ++ t₂) R := by
  have := reach_subst σ h₁
  have e : subst σ (Prot.hole (S := S) (A := A) h) = f := by simp [subst, hs]
  exact reach_append this (by simpa [e] using h₂)

/-- Every prefix of an instance either stays in the template or enters a filled hole and goes on. -/
theorem reach_subst_cases {σ : Subst S Hole A} {i : Ix} {P : Prot S Hole A i} {t : Trace S}
    {R : Σ j, Prot S Hole A j} (hr : Reach (subst σ P) t R) :
    (∃ R₀ : Σ j, Prot S Hole A j, Reach P t R₀ ∧ R = ⟨R₀.1, subst σ R₀.2⟩) ∨
    (∃ t₁ t₂ j, ∃ h : Hole j, ∃ f, t = t₁ ++ t₂ ∧ t₂ ≠ [] ∧ Reach P t₁ ⟨j, .hole h⟩ ∧
      σ j h = some f ∧ Reach f t₂ R) := by
  induction P generalizing t with
  | ret a =>
    cases hr
    exact .inl ⟨_, .here _, rfl⟩
  | call op k ih =>
    cases hr with
    | here => exact .inl ⟨_, .here _, rfl⟩
    | call r hr =>
      rcases ih r hr with ⟨R₀, h0, e⟩ | ⟨t₁, t₂, j, h, f, ht, hne, h1, hs, h2⟩
      · exact .inl ⟨R₀, .call r h0, e⟩
      · exact .inr ⟨_ :: t₁, t₂, j, h, f, by simp [ht], hne, .call r h1, hs, h2⟩
  | @hole i h =>
    change Reach (match σ i h with | some f => f | none => .hole h) t R at hr
    cases hs : σ i h with
    | none =>
      rw [hs] at hr
      cases hr
      exact .inl ⟨_, .here _, by simp [subst, hs]⟩
    | some f =>
      rw [hs] at hr
      cases t with
      | nil =>
        cases hr
        exact .inl ⟨_, .here _, by simp [subst, hs]⟩
      | cons e t => exact .inr ⟨[], e :: t, i, h, f, rfl, by simp, .here _, hs, hr⟩

/-! ## Subject reduction: the linear account and the obligations of a prefix -/

theorem consumed_cons (sp : Spec S Tok Fact Ob) (e : Entry S) (t : Trace S) :
    consumed sp (e :: t) = (match sp.consumes e.2.1 with | some x => [x] | none => []) ++
      consumed sp t := by
  simp only [consumed, List.filterMap_cons]
  cases sp.consumes e.2.1 <;> rfl

/-- **Subject reduction along a prefix**: every prefix of a judged protocol spends tokens within
`Δ` (as a bag: each token at most as often as `Δ` holds it, together with what the residual still
holds), establishes only obligations within `Φ`, and leaves a residual judged at the remaining
tokens. -/
theorem hasProt_reach [DecidableEq Tok] {sp : Spec S Tok Fact Ob} {Ω : Ctx S Hole A Tok Fact Ob}
    {Γ : List Fact} {Q : (j : Ix) → A j → Prop} {Φ : List Ob} {Δ : List Tok} {i : Ix}
    {P : Prot S Hole A i} {t : Trace S} {R : Σ j, Prot S Hole A j}
    (h : HasProt sp Ω Γ Q Φ Δ P) (hr : Reach P t R) :
    ∃ Δ', HasProt sp Ω Γ Q Φ Δ' R.2 ∧
      (∀ x, (consumed sp t).count x + Δ'.count x ≤ Δ.count x) ∧
      ∀ o ∈ established sp t, o ∈ Φ := by
  induction hr generalizing Δ with
  | here => exact ⟨Δ, h, by simp [consumed], by simp [established]⟩
  | @call i op k tr R r _ ih =>
    cases h with
    | call _ _ hc _ he hk =>
      obtain ⟨Δ', h', hcount, hob⟩ := ih (hk r)
      refine ⟨Δ', h', ?_, ?_⟩
      · intro x
        rw [consumed_cons]
        simp only [hc, List.nil_append]
        exact hcount x
      · intro o ho
        simp only [established, List.flatMap_cons, List.mem_append] at ho
        rcases ho with ho | ho
        · exact he o ho
        · exact hob o ho
    | spend _ _ t₀ hc ht _ he hk =>
      obtain ⟨Δ', h', hcount, hob⟩ := ih (hk r)
      refine ⟨Δ', h', ?_, ?_⟩
      · intro x
        rw [consumed_cons]
        simp only [hc, List.singleton_append, List.count_cons]
        have hx := hcount x
        rw [List.count_erase] at hx
        have hpos : 0 < Δ.count t₀ := List.count_pos_iff.mpr ht
        by_cases hxt : t₀ = x
        · subst hxt
          simp at hx ⊢
          omega
        · have : (t₀ == x) = false := by simpa using hxt
          simp [this] at hx ⊢
          omega
      · intro o ho
        simp only [established, List.flatMap_cons, List.mem_append] at ho
        rcases ho with ho | ho
        · exact he o ho
        · exact hob o ho

/-- **At most once** (the discipline is AFFINE: `ret` accepts any leftover `Δ`, so a token may also
go unspent): a token `Δ` holds once is spent at most once on any path of a judged protocol. -/
theorem at_most_once [DecidableEq Tok] {sp : Spec S Tok Fact Ob} {Ω : Ctx S Hole A Tok Fact Ob}
    {Γ : List Fact} {Q : (j : Ix) → A j → Prop} {Φ : List Ob} {Δ : List Tok} {i : Ix}
    {P : Prot S Hole A i} {t : Trace S} {R : Σ j, Prot S Hole A j} {x : Tok}
    (h : HasProt sp Ω Γ Q Φ Δ P) (hr : Reach P t R) (hx : Δ.count x ≤ 1) :
    (consumed sp t).count x ≤ 1 := by
  obtain ⟨Δ', _, hc, _⟩ := hasProt_reach h hr
  have := hc x
  omega

/-- A complete path of a judged protocol ends in a result within `Q`. -/
theorem hasProt_runs [DecidableEq Tok] {sp : Spec S Tok Fact Ob} {Ω : Ctx S Hole A Tok Fact Ob}
    {Γ : List Fact} {Q : (j : Ix) → A j → Prop} {Φ : List Ob} {Δ : List Tok} {i : Ix}
    {P : Prot S Hole A i} {t : Trace S} {j : Ix} {a : A j}
    (h : HasProt sp Ω Γ Q Φ Δ P) (hr : Runs P t j a) : Q j a := by
  obtain ⟨Δ', h', _, _⟩ := hasProt_reach h (runs_reach hr)
  cases h' with
  | ret _ hq => exact hq

/-! ## History preservation under re-substitution -/

/-- The residual is a call of `o`. -/
def IsCall : (Σ j, Prot S Hole A j) → (Σ j, S.Op j) → Prop
  | ⟨j, .call op _⟩, o => o = ⟨j, op⟩
  | _, _ => False

theorem started_some_iff {i : Ix} {P : Prot S Hole A i} {t : Trace S} {o : Σ j, S.Op j} :
    Started P ⟨t, some o⟩ ↔ ∃ R, Reach P t R ∧ IsCall R o := by
  constructor
  · intro h
    cases h with
    | uncertain hr => exact ⟨_, hr, rfl⟩
  · rintro ⟨⟨j, R⟩, hr, hc⟩
    cases R with
    | ret => exact hc.elim
    | hole => exact hc.elim
    | call op k =>
      cases hc
      exact .uncertain hr

/-- **History preservation** (doc 2 section 8): replacing the filling of every hole the history has
NOT entered preserves the accepted history, answered calls and the in-flight call alike. -/
theorem resubst_preserves_started {σ σ' : Subst S Hole A} {i : Ix} {P : Prot S Hole A i}
    {H : Hist S} (hs : Started (subst σ P) H)
    (hg : ∀ j h, Dispatched P H j h → σ' j h = σ j h) : Started (subst σ' P) H := by
  obtain ⟨t, o⟩ := H
  cases o with
  | none =>
    cases hs with
    | settled hr =>
      rcases reach_subst_cases hr with ⟨R₀, h0, _⟩ | ⟨t₁, t₂, j, h, f, ht, hne, h1, hsf, h2⟩
      · exact .settled (reach_subst σ' h0)
      · have hd : Dispatched P ⟨t, none⟩ j h := ⟨t₁, t₂, ht, h1, .inl hne⟩
        rw [ht]
        exact .settled (reach_through_hole h1 ((hg j h hd).trans hsf) h2)
  | some o =>
    obtain ⟨R, hr, hc⟩ := started_some_iff.mp hs
    apply started_some_iff.mpr
    rcases reach_subst_cases hr with ⟨⟨j, R₀⟩, h0, e⟩ | ⟨t₁, t₂, j, h, f, ht, hne, h1, hsf, h2⟩
    · subst e
      cases R₀ with
      | ret a => exact hc.elim
      | call op k => exact ⟨_, reach_subst σ' h0, hc⟩
      | hole h =>
        have hd : Dispatched P ⟨t, some o⟩ j h := ⟨t, [], by simp, h0, .inr rfl⟩
        refine ⟨_, reach_subst σ' h0, ?_⟩
        have e : subst σ' (Prot.hole (S := S) (A := A) h) = subst σ (Prot.hole h) := by
          simp [subst, hg j h hd]
        simpa [e] using hc
    · have hd : Dispatched P ⟨t, some o⟩ j h := ⟨t₁, t₂, ht, h1, .inl hne⟩
      rw [show t = t₁ ++ t₂ from ht]
      exact ⟨R, reach_through_hole h1 ((hg j h hd).trans hsf) h2, hc⟩

/-- The obligations a history of a judged protocol established, the in-flight call's included,
are within `Φ`. -/
theorem started_obligations [DecidableEq Tok] {sp : Spec S Tok Fact Ob}
    {Ω : Ctx S Hole A Tok Fact Ob} {Γ : List Fact} {Q : (j : Ix) → A j → Prop} {Φ : List Ob}
    {Δ : List Tok} {i : Ix} {P : Prot S Hole A i} {H : Hist S}
    (h : HasProt sp Ω Γ Q Φ Δ P) (hs : Started P H) : ∀ o ∈ H.established sp, o ∈ Φ := by
  cases hs with
  | settled hr =>
    obtain ⟨_, _, _, hob⟩ := hasProt_reach h hr
    simpa [Hist.established] using hob
  | uncertain hr =>
    obtain ⟨_, h', _, hob⟩ := hasProt_reach h hr
    intro o ho
    simp only [Hist.established, List.mem_append] at ho
    rcases ho with ho | ho
    · exact hob o ho
    · cases h' with
      | call _ _ _ _ he _ => exact he o ho
      | spend _ _ _ _ _ _ he _ => exact he o ho

/-- **Admission and history preservation for the open object**: a guarded re-substitution of a
well-formed object by an interface-respecting substitution is well-formed, keeps the accepted
history (answered and in flight), and every obligation that history established stays within the
object's bound. -/
theorem Open.resubst_wf [DecidableEq Tok] {sp : Spec S Tok Fact Ob} {i : Ix}
    {O : Open S Hole A Tok Fact Ob i} (hO : O.WF sp) {σ' : Subst S Hole A}
    (hσ' : SubstOK sp O.Ω σ')
    (g : O.Replan σ') :
    (O.replan σ').WF sp ∧ (O.replan σ').hist = O.hist ∧
      ∀ o ∈ (O.replan σ').hist.established sp, o ∈ O.Φ := by
  have hst : Started (O.replan σ').current O.hist :=
    resubst_preserves_started (σ := O.σ.mine O.Ω) hO.started g
  have hwf : (O.replan σ').WF sp := ⟨hO.typed, hσ', hst⟩
  exact ⟨hwf, rfl, started_obligations (fill_preserves_hasProt hσ' hO.typed) hst⟩

/-! ## The recording interpreter performs exactly a path -/

/-- **`interpret` performs exactly a path** (nano's `interp_runs`, for open protocols): at the
recording environment, a run that ends appends to the trace exactly a complete path ending in its
result; a run that stops at a hole appends exactly a prefix reaching that hole. -/
theorem interpret_record {St : Ix → Type} (H : Handler S St) {i : Ix} (P : Prot S Hole A i)
    (s : St i) (tr₀ : Trace S) :
    match interpret (record H) P (s, tr₀) with
    | .done j a p => ∃ tr, p.2 = tr₀ ++ tr ∧ Runs P tr j a
    | .stuck j h p => ∃ tr, p.2 = tr₀ ++ tr ∧ Reach P tr ⟨j, .hole h⟩ := by
  obtain ⟨handle⟩ := H
  induction P generalizing tr₀ with
  | ret a => exact ⟨[], by simp, .ret a⟩
  | @call i op k ih =>
    rcases hh : handle op s with ⟨r, s'⟩
    have e : interpret (record ⟨handle⟩) (Prot.call op k) (s, tr₀) =
        interpret (record ⟨handle⟩) (k r) (s', tr₀ ++ [⟨i, op, r⟩]) := by
      simp only [interpret, fold, execAlgebra, record]
      rw [hh]
    rw [e]
    have := ih r s' (tr₀ ++ [⟨i, op, r⟩])
    revert this
    cases interpret (record ⟨handle⟩) (k r) (s', tr₀ ++ [⟨i, op, r⟩]) with
    | done j a p =>
      rintro ⟨tr, htr, hrun⟩
      exact ⟨_ :: tr, by simp [htr], .call r hrun⟩
    | stuck j h p =>
      rintro ⟨tr, htr, hrun⟩
      exact ⟨_ :: tr, by simp [htr], .call r hrun⟩
  | hole h => exact ⟨[], by simp, .here _⟩

/-! ## Admission: current evidence -/

theorem all_congr' {α : Type} {g g' : α → Bool} :
    ∀ l : List α, (∀ x ∈ l, g x = g' x) → l.all g = l.all g'
  | [], _ => rfl
  | x :: l, h => by
    simp only [List.all_cons]
    rw [h x (by simp), all_congr' l (fun y hy => h y (by simp [hy]))]

/-- **Locality of admission**: an effect's admission reads only its support. -/
theorem admits_local {sp : Spec S Tok Fact Ob} {i : Ix} (op : S.Op i)
    {w₁ w₂ : Fact ⊕ Tok → Bool} (hw : ∀ k ∈ opSupport sp op, w₁ k = w₂ k) :
    admitOp sp (View.ofStore w₁) op = admitOp sp (View.ofStore w₂) op := by
  unfold admitOp View.ofStore
  rw [all_congr' (sp.requires op) (fun f hf => hw (.inl f) (by simp [opSupport, hf]))]
  congr 1
  cases hc : sp.consumes op with
  | none => rfl
  | some t => exact hw (.inr t) (by simp [opSupport, hc])

/-- An admission fragment declares a sufficient support. -/
theorem admitFrag_readsOnly {Name : Type} (sp : Spec S Tok Fact Ob) (name : Name) {i : Ix}
    (op : S.Op i) : (admitFrag sp name op).ReadsOnly :=
  fun _ _ hw => admits_local op hw

/-- What an admitted call establishes: its facts hold now, its token is unspent now. -/
theorem admitOp_sound {sp : Spec S Tok Fact Ob} {v : View Tok Fact} {i : Ix} {op : S.Op i}
    (h : admitOp sp v op = true) :
    (∀ f ∈ sp.requires op, v.holds f = true) ∧ ∀ t, sp.consumes op = some t → v.live t = true := by
  unfold admitOp at h
  simp only [Bool.and_eq_true, List.all_eq_true] at h
  refine ⟨h.1, fun t ht => ?_⟩
  have := h.2
  rw [ht] at this
  exact this

/-- **Durable consumption**: once an effect spending `t` commits, no effect spending `t` commits
again from the resulting view: a replayed or competing commitment is refused. -/
theorem commit_once [DecidableEq Tok] {sp : Spec S Tok Fact Ob} {v v' : View Tok Fact} {i : Ix}
    {op : S.Op i} {t : Tok} (h : commit sp v op = some v') (ht : sp.consumes op = some t)
    {j : Ix} (op' : S.Op j) (ht' : sp.consumes op' = some t) : commit sp v' op' = none := by
  unfold commit at h
  split at h
  · simp only [ht, Option.some.injEq] at h
    subst h
    unfold commit admitOp
    simp [ht', View.spend]
  · cases h

/-! ## Selective repair -/

theorem Frag.unaffected {Name Key V : Type} [DecidableEq Key] {f : Frag Name Key V}
    {changed : List Key} (h : f.affected changed = false) : ∀ k ∈ f.support, k ∉ changed := by
  intro k hk hc
  have : f.affected changed = true := List.any_eq_true.mpr ⟨k, hk, by simp [hc]⟩
  rw [h] at this
  cases this

/-- **Locality** (family 3): a change outside a fragment's support leaves its verdict. -/
theorem locality {Name Key V : Type} [DecidableEq Key] {f : Frag Name Key V} (hf : f.ReadsOnly)
    {changed : List Key} {w₁ w₂ : Key → V} (hout : ∀ k, k ∉ changed → w₁ k = w₂ k)
    (hna : f.affected changed = false) : f.check w₁ = f.check w₂ :=
  hf w₁ w₂ fun k hk => hout k (Frag.unaffected hna k hk)

/-- **Selective repair agrees with checking from scratch** (family 3): from correct verdicts for
`w₁`, re-checking only the fragments a change of `changed` affects gives exactly the verdicts a
full re-check of `w₂` gives. -/
theorem repair_agrees_from_scratch {Name Key V : Type} [DecidableEq Key]
    (fs : List (Frag Name Key V)) (hfs : ∀ f ∈ fs, f.ReadsOnly) {changed : List Key}
    {w₁ w₂ : Key → V} (hout : ∀ k, k ∉ changed → w₁ k = w₂ k) :
    repair fs (fromScratch fs w₁) changed w₂ = fromScratch fs w₂ := by
  induction fs with
  | nil => rfl
  | cons f fs ih =>
    simp only [fromScratch, List.map_cons, repair]
    have ih' := ih (fun g hg => hfs g (by simp [hg]))
    simp only [fromScratch] at ih'
    rw [ih']
    congr 1
    cases ha : f.affected changed with
    | true => rfl
    | false => exact locality (hfs f (by simp)) hout ha

/-- The explicit residual obligations of a repair are those of a full re-check. -/
theorem repair_residual {Name Key V : Type} [DecidableEq Key]
    (fs : List (Frag Name Key V)) (hfs : ∀ f ∈ fs, f.ReadsOnly) {changed : List Key}
    {w₁ w₂ : Key → V} (hout : ∀ k, k ∉ changed → w₁ k = w₂ k) :
    residual fs (repair fs (fromScratch fs w₁) changed w₂) = residual fs (fromScratch fs w₂) := by
  rw [repair_agrees_from_scratch fs hfs hout]

/-- **Repair reads only the affected fragments**: two new worlds on which every AFFECTED fragment
checks alike yield the same repair; the unaffected verdicts are reused, never recomputed. -/
theorem repair_reuses {Name Key V : Type} [DecidableEq Key] (fs : List (Frag Name Key V))
    (cache : List Bool) (hlen : cache.length = fs.length) (changed : List Key) {w w' : Key → V}
    (h : ∀ f ∈ fs, f.affected changed = true → f.check w = f.check w') :
    repair fs cache changed w = repair fs cache changed w' := by
  induction fs generalizing cache with
  | nil => rfl
  | cons f fs ih =>
    have ih' := fun c hc => ih c hc (fun g hg => h g (by simp [hg]))
    cases cache with
    | nil => cases hlen
    | cons c cs =>
      simp only [repair]
      rw [ih' cs (by simpa using hlen)]
      congr 1
      cases ha : f.affected changed with
      | true => simp [h f (by simp) ha]
      | false => rfl

/-! ## Representation change -/

theorem count_map_inj {α β : Type} [DecidableEq α] [DecidableEq β] {e : α → β} {e' : β → α}
    (h₁ : ∀ a, e' (e a) = a) (l : List α) (a : α) : (l.map e).count (e a) = l.count a := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    simp only [List.map_cons, List.count_cons, ih]
    by_cases hx : x = a
    · subst hx; simp
    · have hex : e x ≠ e a := fun h => hx (by rw [← h₁ x, h, h₁])
      simp [hx, hex]

/-- Renaming along a map with a left inverse (injective) preserves bag inclusion. -/
theorem SubBag.map [DecidableEq Tok] {Tok' : Type} [DecidableEq Tok'] {e : Tok → Tok'}
    {e' : Tok' → Tok} (h₁ : ∀ a, e' (e a) = a) {Δ₁ Δ₂ : List Tok} (h : SubBag Δ₁ Δ₂) :
    SubBag (Δ₁.map e) (Δ₂.map e) := by
  intro b
  by_cases hb : ∃ a, e a = b
  · obtain ⟨a, rfl⟩ := hb
    rw [count_map_inj h₁, count_map_inj h₁]
    exact h a
  · have hn : b ∉ Δ₁.map e := fun hm => hb (by
      obtain ⟨a, _, ha⟩ := List.mem_map.mp hm
      exact ⟨a, ha⟩)
    rw [List.count_eq_zero.mpr hn]
    exact Nat.zero_le _

theorem map_erase_bij {α β : Type} [DecidableEq α] [DecidableEq β] {e : α → β} {e' : β → α}
    (h₁ : ∀ a, e' (e a) = a) (l : List α) (a : α) : (l.erase a).map e = (l.map e).erase (e a) := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    by_cases hx : x = a
    · subst hx; simp
    · have hex : e x ≠ e a := fun h => hx (by rw [← h₁ x, h, h₁])
      simp [hx, hex, ih]

/-- **Representation change transports the judgment**: renaming every token along a checked
correspondence (a map with a left inverse, so possibly PARTIAL on the new side: stale
representations need not name anything) carries a judged protocol to a judged protocol over the
new representation, its tokens renamed. -/
theorem hasProt_mapTok {Tok' : Type} [DecidableEq Tok] [DecidableEq Tok']
    {e : Tok → Tok'} {e' : Tok' → Tok} (h₁ : ∀ a, e' (e a) = a)
    {sp : Spec S Tok Fact Ob} {Ω : Ctx S Hole A Tok Fact Ob} {Γ : List Fact}
    {Q : (j : Ix) → A j → Prop} {Φ : List Ob} {Δ : List Tok} {i : Ix} {P : Prot S Hole A i}
    (h : HasProt sp Ω Γ Q Φ Δ P) : HasProt (sp.mapTok e) (Ω.mapTok e) Γ Q Φ (Δ.map e) P := by
  induction h with
  | ret a hq => exact .ret a hq
  | call op k hc hr he _ ih =>
    exact .call op k (by simp [Spec.mapTok, hc]) hr he ih
  | @spend Δ i op k t hc ht hr he _ ih =>
    refine .spend op k (e t) (by simp [Spec.mapTok, hc]) (List.mem_map_of_mem ht) hr he ?_
    intro r
    have := ih r
    rwa [map_erase_bij h₁] at this
  | hole h I hI hp hctx hneed hpost howes =>
    refine .hole h (I.mapTok e) (by simp [Ctx.mapTok, hI]) hp hctx ?_ hpost howes
    exact SubBag.map h₁ hneed

/-- **Representation change transports admission**: an effect is admissible over the renamed
tokens, against the view read back through the correspondence, exactly when it was before. -/
theorem admitOp_mapTok {Tok' : Type} {e : Tok → Tok'} {e' : Tok' → Tok}
    (h₁ : ∀ a, e' (e a) = a) (sp : Spec S Tok Fact Ob) (v : View Tok Fact) {i : Ix}
    (op : S.Op i) :
    admitOp (sp.mapTok e) ⟨v.holds, fun b => v.live (e' b)⟩ op = admitOp sp v op := by
  unfold admitOp Spec.mapTok
  cases hc : sp.consumes op <;> simp [hc, h₁]

end

/-! ## Shared parameters -/

/-- **Separate witnesses are insufficient** (doc 2 section 4), a SCALAR ILLUSTRATION over a bounded
price range: each party's condition has a witness, and no price meets both. -/
theorem separate_witnesses_bounded :
    (∃ x : Fin 20, x.val ≤ 5) ∧ (∃ x : Fin 20, 7 ≤ x.val) ∧ ¬ ∃ x : Fin 20, x.val ≤ 5 ∧ 7 ≤ x.val := by
  decide

/-! ## A hole is not an interaction (doc 2 section 5) -/

namespace Coin

/-- Running the open plan under a filling: the filling's answer, compared with the peer's bit. -/
theorem wins_planHole (θ : Subst sig HoleN Res) (b : Bool) :
    wins b (subst θ planHole) () =
      match θ .revealed () with
      | some (.ret c) => c == b
      | _ => false := by
  have e : wins b (subst θ planHole) () =
      wins b (subst θ (Prot.hole (S := sig) (A := Res) (i := Phase.revealed) ())) () := rfl
  rw [e]
  cases hθ : θ .revealed () with
  | none => simp only [subst, hθ]; rfl
  | some f =>
    cases f with
    | ret c => simp only [subst, hθ]; rfl
    | call op k => exact nomatch op
    | hole h => simp only [subst, hθ]; rfl

/-- **No foresight, for a response-free naming**: `planHole` names its hole `()` in BOTH branches of
the peer's bit. For every environment SOME filling wins (`∀ E ∃ θ, Success (P[θ], E)`), but no
single filling wins against every environment (`¬ ∃ θ ∀ E`): the "commit a bit before you reveal
yours" game. This holds BECAUSE of the naming: with names that depend on the response the opposite
holds (`response_indexed_names_have_foresight`), and `foresight_iff_names_separate` is the exact
condition. Scope (one filling into every branch unchanged) is a naming discipline, not a fact of
the calculus. -/
theorem no_foresight :
    (∀ b, ∃ θ, wins b (subst θ planHole) () = true) ∧
      ¬ ∃ θ, ∀ b, wins b (subst θ planHole) () = true := by
  refine ⟨fun b => ⟨answer b, by rw [wins_planHole]; cases b <;> rfl⟩, ?_⟩
  rintro ⟨θ, hθ⟩
  have h0 := hθ false
  have h1 := hθ true
  rw [wins_planHole] at h0 h1
  cases hr : θ .revealed () with
  | none => simp [hr] at h0
  | some f =>
    cases f with
    | ret c => cases c <;> simp [hr] at h0 h1
    | call op k => exact nomatch op
    | hole h => simp [hr] at h0

/-- **The response-dependent continuation succeeds**: the same game with the answer written as
the continuation of the `call` (a family over the response) wins against every environment. -/
theorem response_dependent_succeeds : ∀ b, wins b planCall () = true := by
  intro b; cases b <;> rfl

/-- Running a named template under a filling: the filling of branch `b`'s hole, compared with `b`. -/
theorem wins_planNamed {Hn : Phase → Type} (name : Bool → Hn .revealed) (θ : Subst sig Hn Res)
    (b : Bool) :
    wins b (subst θ (planNamed name)) () =
      match θ .revealed (name b) with
      | some (.ret c) => c == b
      | _ => false := by
  have e : wins b (subst θ (planNamed name)) () =
      wins b (subst θ (Prot.hole (S := sig) (A := Res) (i := Phase.revealed) (name b))) () := rfl
  rw [e]
  cases hθ : θ .revealed (name b) with
  | none => simp only [subst, hθ]; rfl
  | some f =>
    cases f with
    | ret c => simp only [subst, hθ]; rfl
    | call op k => exact nomatch op
    | hole h => simp only [subst, hθ]; rfl

/-- **Foresight exactly when the names separate**: a single filling chosen before the reveal wins
against every bit iff the template gives the two branches DIFFERENT hole names. A response-free
naming (`name true = name false`) leaves no causal strategy; a response-indexed one is a filling
per response. -/
theorem foresight_iff_names_separate {Hn : Phase → Type} [DecidableEq (Hn .revealed)]
    (name : Bool → Hn .revealed) :
    (∃ θ : Subst sig Hn Res, ∀ b, wins b (subst θ (planNamed name)) () = true) ↔
      name true ≠ name false := by
  constructor
  · rintro ⟨θ, hθ⟩ heq
    have h0 := hθ false
    have h1 := hθ true
    rw [wins_planNamed] at h0 h1
    rw [heq] at h1
    cases hr : θ .revealed (name false) with
    | none => simp [hr] at h0
    | some f =>
      cases f with
      | ret c => cases c <;> simp [hr] at h0 h1
      | call op k => exact nomatch op
      | hole h => simp [hr] at h0
  · intro hne
    refine ⟨fun i => match i with
      | .waiting => fun _ => none
      | .revealed => fun n => some (.ret (decide (n = name true))), fun b => ?_⟩
    rw [wins_planNamed]
    cases b with
    | true => simp
    | false => simp [Ne.symm hne]

/-- **Response-indexed names have foresight**: `call recv (fun b => hole b)` (one hole name per bit,
well typed) admits ONE filling that wins against every environment. A hole whose name depends on the
response is a family over the response, exactly like a `call` continuation. -/
theorem response_indexed_names_have_foresight :
    ∃ θ : Subst sig HoleB Res, ∀ b, wins b (subst θ (planNamed (Hn := HoleB) fun b => b)) () = true :=
  (@foresight_iff_names_separate HoleB (inferInstanceAs (DecidableEq Bool)) fun b => b).mpr
    (by intro h; cases h)

/-- `planHole` is the response-free naming. -/
theorem planHole_named : planHole = planNamed (Hn := HoleN) fun _ => () := rfl

/-- **An `.other` hole is never planned**: declared chosen by `.other`, the hole is never filled by our plan, so
every run of the open plan stops at the hole. It "loses" only because `wins` scores a stuck run as
`false`: the theorem says the planner cannot win by filling, not that the peer wins. -/
theorem peer_hole_never_planned (σ : Subst sig HoleN Res) (b : Bool) :
    wins b (fill (ctxOf .other) σ planHole) () = false := by
  unfold fill
  rw [wins_planHole]
  simp [Subst.mine, ctxOf, iface]

end Coin

end Nanodregg.Lang.Contextual.Protocol

/-- From-scratch consistency of fragment verdicts under declared read-set locality.
Stein–Chang–Sridharan, Demanded Abstract Interpretation (2021), Thm.6.1, PDF p.10;
Mokhov–Mitchell–Peyton Jones, Build Systems à la Carte (2018), Def.3.1 p.79:11.
This original protocol result assumes Frag.ReadsOnly and agreement outside changed keys;
the new Trace guard constructs its finite observation instead. No premise or name changed. -/
add_decl_doc Nanodregg.Lang.Contextual.Protocol.repair_agrees_from_scratch
