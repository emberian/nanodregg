/-
# Lang.Proofs.Contextual.Experiments — the eight experiments of ACTIVITIES-PROPOSAL doc 1 §9

A tiny concrete calculus (`ToyCalc` data, `toyHasTy` typing, `toyLaws`: terms are `lit n | var x | hole u | add a b`, contexts are
lists of variable names, one type, typing = scoping), so every closure computes by `decide`. Each
experiment is a named theorem over a concrete session, next to the general theorem it instances.

1. `withdraw_one_of_two_supports` (provenance `ab + c`; `alternative_sound`), `rejudged_only_touched`
   (`repair_rejudged_eq_touched`), `s1_coherent` (`session_preserves_coherent`)
2. `withdraw_last_support` (`withdraw_never_refutes`, `suspended_sound`)
3. `withdraw_pruning_reason` (`judge_pruned`, `withdraw_never_prunes`)
4. `cycle_loses_grounding` + `counting_keeps_cycle` (`unfounded_not_derivable`, `lfpIter_sound`):
   NOT in the closure (a cycle is not expressible with one-level supports); a separate rule model
5. `dependent_context_change` (`judge_conflict_iff`, `replacement_sound`)
6. `replace_filling_preserving_contract` (`consumer_boundary`)
7. `correct_but_cost_lost` (`judge_verified_iff`)
8. `reapply_earlier_filling` (`reissue_never_reenables`, `reissued_support_unverified`)

and beside them: `withdraw_hypothesis_strengthens` / `withdraw_used_hypothesis_obstructs`
(`strengthening_sound`: the proposal's obstruction, `a : A ⊢ a` with `a` withdrawn),
`unchecked_select_underivable` (the tooth of `fill_preserves_derivable`), and
`value_guard_stable` / `syntactic_guard_not_stable` (`stability_class`).
-/
import Lang.Proofs.Contextual.Closure

namespace Nanodregg.Lang.Contextual.Toy

open Nanodregg.Lang.Contextual

/-! ## The toy calculus -/

private inductive Tm where
  | lit (n : Nat)
  | var (x : Nat)
  | hole (u : Nat)
  | add (a b : Tm)
deriving DecidableEq, Repr

private abbrev Decl := HoleDecl (List Nat) Unit

/-- Scoping: variables in the context, holes declared with a context inside it. -/
private def wf (Ω : List Decl) (Γ : List Nat) : Tm → Bool
  | .lit _ => true
  | .var x => Γ.contains x
  | .hole u => Ω.any fun d => d.name == u && d.ctx.all Γ.contains
  | .add a b => wf Ω Γ a && wf Ω Γ b

private def msubst (σ : Nat → Option Tm) : Tm → Tm
  | .lit n => .lit n
  | .var x => .var x
  | .hole u => (σ u).getD (.hole u)
  | .add a b => .add (msubst σ a) (msubst σ b)

private def vars : Tm → List Nat
  | .lit _ => []
  | .var x => [x]
  | .hole _ => []
  | .add a b => vars a ++ vars b

private def eval : Tm → Option Nat
  | .lit n => some n
  | .var _ => none
  | .hole _ => none
  | .add a b => match eval a, eval b with
    | some x, some y => some (x + y)
    | _, _ => none

theorem wf_closed_mono {Ω : List Decl} {Ψ Γ : List Nat} (hsub : ∀ x ∈ Ψ, x ∈ Γ) :
    ∀ M, wf [] Ψ M = true → wf Ω Γ M = true
  | .lit _, _ => rfl
  | .var x, h => by
    simp only [wf, List.contains_iff_mem] at h ⊢
    exact hsub x h
  | .hole _, h => by simp [wf] at h
  | .add a b, h => by
    simp only [wf, Bool.and_eq_true] at h ⊢
    exact ⟨wf_closed_mono hsub a h.1, wf_closed_mono hsub b h.2⟩

theorem msubst_lemma {Ω : List Decl} {Γ : List Nat} (σ : Nat → Option Tm)
    (hσ : ∀ d ∈ Ω, ∀ M, σ d.name = some M → wf [] d.ctx M = true) :
    ∀ P, wf Ω Γ P = true → wf (Ω.filter fun d => (σ d.name).isNone) Γ (msubst σ P) = true
  | .lit _, _ => rfl
  | .var _, h => h
  | .hole u, h => by
    simp only [wf, List.any_eq_true, Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
      List.contains_iff_mem] at h
    obtain ⟨d, hd, rfl, hctx⟩ := h
    cases hs : σ d.name with
    | some M =>
      simp only [msubst, hs, Option.getD_some]
      exact wf_closed_mono hctx M (hσ d hd M hs)
    | none =>
      simp only [msubst, hs, Option.getD_none, wf, List.any_eq_true, List.mem_filter,
        Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.contains_iff_mem]
      exact ⟨d, ⟨hd, by simp [hs]⟩, rfl, hctx⟩
  | .add a b, h => by
    simp only [wf, Bool.and_eq_true, msubst] at h ⊢
    exact ⟨msubst_lemma σ hσ a h.1, msubst_lemma σ hσ b h.2⟩

theorem strengthen_lemma {Ψ : List Nat} {x : Nat} :
    ∀ M, wf [] Ψ M = true → (vars M).contains x = false → wf [] (Ψ.filter (· != x)) M = true
  | .lit _, _, _ => rfl
  | .var y, h, hx => by
    simp only [wf, List.contains_iff_mem, vars, List.contains_cons, List.contains_nil,
      Bool.or_false, beq_eq_false_iff_ne] at h hx ⊢
    simp only [List.mem_filter, bne_iff_ne]
    exact ⟨h, fun he => hx (he ▸ rfl)⟩
  | .hole _, h, _ => by simp [wf] at h
  | .add a b, h, hx => by
    simp only [wf, Bool.and_eq_true, vars, List.contains_append, Bool.or_eq_false_iff] at h hx ⊢
    exact ⟨strengthen_lemma a h.1 hx.1, strengthen_lemma b h.2 hx.2⟩

theorem wf_vars {Ψ : List Nat} : ∀ M, wf [] Ψ M = true → ∀ y ∈ vars M, y ∈ Ψ
  | .lit _, _, _, hy => by simp [vars] at hy
  | .var x, h, y, hy => by
    simp only [vars, List.mem_singleton] at hy; subst hy
    simpa [wf] using h
  | .hole _, h, _, _ => by simp [wf] at h
  | .add a b, h, y, hy => by
    simp only [wf, Bool.and_eq_true] at h
    simp only [vars, List.mem_append] at hy
    rcases hy with hy | hy
    · exact wf_vars a h.1 y hy
    · exact wf_vars b h.2 y hy

theorem weaken_avoids {Ψ : List Nat} {x : Nat} :
    ∀ M, wf [] (Ψ.filter (· != x)) M = true → (vars M).contains x = false := by
  intro M h
  cases hc : (vars M).contains x
  · rfl
  · have := wf_vars M h x (by simpa using hc)
    simp at this

/-- The toy's data. Named variables: strengthening is the identity on syntax (`π = id`). -/
private abbrev ToyCalc : CalculusData where
  Ty := Unit
  Ctx := List Nat
  Tm := Tm
  tmEq := inferInstance
  msubst := msubst
  check Ψ M _ := wf [] Ψ M
  uses M x := (vars M).contains x
  drop Ψ x := Ψ.filter (· != x)
  strengthen _ M := M
  weaken _ M := M
  var := Tm.var
  lookup Ψ x := if x ∈ Ψ then some () else none

/-- The toy's typing: scoping. -/
def toyHasTy (Ω : List Decl) (Γ : List Nat) (M : Tm) (_ : Unit) : Prop := wf Ω Γ M = true

/-- The toy satisfies every law. -/
theorem toyLaws : CalculusLaws ToyCalc toyHasTy where
  msubst_lemma σ h hσ := msubst_lemma σ hσ _ h
  check_sound h := h
  check_complete h := h
  strengthen_lemma h hx := strengthen_lemma _ h hx
  strengthen_factor _ := rfl
  weaken_avoids h := weaken_avoids _ h
  hasTy_var {Ψ x _} h := by
    show (Ψ.contains x) = true
    by_cases hx : x ∈ Ψ
    · simpa using hx
    · simp [ToyCalc, hx] at h
  uses_var := by intro x; show [x].contains x = true; simp

/-! ## Fixtures: one hole `0 :: [· ⊢ ()]` in the template `0 + 1`, guard "value below n" -/

private abbrev W := World Nat
private abbrev Cl := Closure ToyCalc Nat

private def tA : Token := ⟨1, 0⟩
private def tB : Token := ⟨2, 0⟩
private def tC : Token := ⟨3, 0⟩
private def tK : Token := ⟨4, 0⟩
private def tH : Token := ⟨5, 0⟩

/-- The hole's guard: the filling has a value, below the environment's bound `n`. -/
private def valueBelow (n : Nat) (M : Tm) : Bool :=
  match eval M with
  | some v => decide (v < n)
  | none => false

private def hole0 : Iface ToyCalc Nat :=
  { name := 0, ctx := ([] : List Nat), ty := (), hyps := [], hyps_real := by simp,
    guard := valueBelow, budget := 100, chooser := 1, acceptor := 2 }

private def tpl0 : Template ToyCalc Nat where
  Γ := ([] : List Nat)
  T := ()
  P := Tm.add (.hole 0) (.lit 1)
  Ω := [hole0]
  names := List.nodup_cons.2 ⟨by simp, List.nodup_nil⟩

/-- Tokens A, B, C, K live; bound 10. -/
private def w0 : W := ⟨fun t => t == tA || t == tB || t == tC || t == tK, 10⟩

private def cand (M : Tm) (sup : List Token) (cost : Nat := 1) : Candidate ToyCalc :=
  { filling := M, supports := sup, blockers := [], cost := cost, by_ := 3, status := .verified }

private def start (tpl : Template ToyCalc Nat) (w : W) : Cl := fromScratch w tpl fun _ => []

/-! ## Observation helpers (Bool/Option views, so sessions decide) -/

private def obs : Except Refusal (W × Cl) → Option (List (List Status))
  | .ok st => some (observe st.2)
  | .error _ => none

private def sel (u : Nat) : Except Refusal (W × Cl) → Option (Option Nat)
  | .ok st => some (st.2.slot u).selected
  | .error _ => none

private def refusal : Except Refusal (W × Cl) → Option Refusal
  | .ok _ => none
  | .error r => some r

/-- An outcome's shape: (kind, hole, index or hypothesis). -/
private def code : Outcome ToyCalc → Nat × Nat × Nat
  | .kept u => (0, u, 0)
  | .replacement u j _ => (1, u, j)
  | .strengthening u x _ => (2, u, x)
  | .alternative u j => (3, u, j)
  | .suspended u _ => (4, u, 0)

private def outs (e : Edit Nat) : Except Refusal (W × Cl) → Option (List (Nat × Nat × Nat))
  | .ok st => some ((repair st.1 e st.2).2.1.map code)
  | .error _ => none

private def obligations (e : Edit Nat) : Except Refusal (W × Cl) → Option (List Obligation)
  | .ok st => some ((repair st.1 e st.2).2.1.flatMap fun o => match o with
      | .suspended _ Φ => Φ
      | _ => [])
  | .error _ => none

/-- Availability as a Boolean check. -/
private def availB {D : CalculusData} {E : Type} (w : World E) (cl : Closure D E) : Bool :=
  cl.tpl.Ω.all fun I => match cl.selectedCand I.name with
    | some c => (effSupports I c).all w.live
    | none => true

theorem available_of_availB {D : CalculusData} {E : Type} {w : World E} {cl : Closure D E}
    (h : availB w cl = true) : Available w cl := by
  intro I hI c hc t ht
  simp only [availB, List.all_eq_true] at h
  have := h I hI
  rw [hc] at this
  simp only [List.all_eq_true] at this
  exact this t ht

theorem not_available_of_availB {D : CalculusData} {E : Type} {w : World E} {cl : Closure D E}
    (h : availB w cl = false) : ¬ Available w cl := by
  intro ha
  simp only [availB, List.all_eq_false] at h
  obtain ⟨I, hI, hI'⟩ := h
  split at hI'
  · rename_i c hc
    simp only [List.all_eq_true] at hI'
    exact hI' (ha I hI c hc)
  · simp at hI'

private def availS : Except Refusal (W × Cl) → Option Bool
  | .ok st => some (availB st.1 st.2)
  | .error _ => none

/-! ## Experiment 1: withdraw one of two supports (provenance `ab + c`) -/

/-- Two derivations of ONE filling: `c1 = 5` under `A·B`, `c2 = 5` under `C`; `c1` selected. -/
private def s1 : Except Refusal (W × Cl) :=
  Session.run [.propose 0 (cand (.lit 5) [tA, tB]), .propose 0 (cand (.lit 5) [tC]), .select 1 0 0]
    (w0, start tpl0 w0)

private def s1a : Except Refusal (W × Cl) := s1.bind fun st => Session.run [.edit (.withdraw tA)] st

private def s1r : Except Refusal (W × Cl) := s1a.bind fun st => Session.run [.edit (.assert tA)] st

/-- **Experiment 1.** Withdrawing `A` kills the route `A·B` and the judgment survives through `C`:
repair reports `alternative` (the same `σ`, another `D`) and switches to it; the closure stays
available. Re-asserting `A` (the SAME immutable token) restores the first route without any
re-proposal. -/
theorem withdraw_one_of_two_supports :
    obs s1 = some [[.verified, .verified]] ∧ sel 0 s1 = some (some 0) ∧
    outs (.withdraw tA) s1 = some [(3, 0, 1)] ∧
    obs s1a = some [[.suspended [tA], .verified]] ∧ sel 0 s1a = some (some 1) ∧
    availS s1a = some true ∧
    obs s1r = some [[.verified, .verified]] := by
  decide

theorem available_of_availS {r : Except Refusal (W × Cl)} (h : availS r = some true) :
    ∃ st, r = .ok st ∧ Available st.1 st.2 := by
  cases r with
  | error _ => simp [availS] at h
  | ok st =>
    simp only [availS, Option.some.injEq] at h
    exact ⟨st, rfl, available_of_availB h⟩

theorem not_available_of_availS {r : Except Refusal (W × Cl)} (h : availS r = some false) :
    ∃ st, r = .ok st ∧ ¬ Available st.1 st.2 := by
  cases r with
  | error _ => simp [availS] at h
  | ok st =>
    simp only [availS, Option.some.injEq] at h
    exact ⟨st, rfl, not_available_of_availB h⟩

private def phiS : Except Refusal (W × Cl) → Option (List Obligation)
  | .ok st => some st.2.Φ
  | .error _ => none

theorem withdraw_one_of_two_supports_available : ∃ st, s1a = .ok st ∧ Available st.1 st.2 :=
  available_of_availS withdraw_one_of_two_supports.2.2.2.2.2.1

/-! ## Experiment 2: withdraw the last known support -/

private def s2 : Except Refusal (W × Cl) := s1a.bind fun st => Session.run [.edit (.withdraw tC)] st

/-- **Experiment 2.** Withdrawing `C` too leaves no route: both candidates `suspended` with the
missing token named, the outcome is `suspended` with its obligations, the closure is unavailable,
and NO `conflict` appears anywhere (losing the justification establishes no negation). -/
theorem withdraw_last_support :
    outs (.withdraw tC) s1a = some [(4, 0, 0)] ∧
    obligations (.withdraw tC) s1a =
      some [.refill 0, .support 0 0 tA, .support 0 1 tC] ∧
    obs s2 = some [[.suspended [tA], .suspended [tC]]] ∧
    sel 0 s2 = some (some 1) ∧
    phiS s2 = some [.support 0 1 tC] ∧
    availS s2 = some false := by
  decide

theorem withdraw_last_support_unavailable : ∃ st, s2 = .ok st ∧ ¬ Available st.1 st.2 :=
  not_available_of_availS withdraw_last_support.2.2.2.2.2

/-! ## Experiment 3: withdraw the reason a branch was pruned -/

/-- `c3 = 7` pruned by the chooser BECAUSE token `K` (the exclusion argument, kept as a token). -/
private def s3 : Except Refusal (W × Cl) :=
  Session.run [.propose 0 (cand (.lit 7) []), .prune 1 0 0 tK] (w0, start tpl0 w0)

private def s3sel : Except Refusal (W × Cl) := s3.bind fun st => Session.run [.select 1 0 0] st

private def s3w : Except Refusal (W × Cl) := s3.bind fun st => Session.run [.edit (.withdraw tK), .select 1 0 0] st

/-- A prune whose reason is not a live token has no effect: the exclusion needs a live reason. -/
private def s3dead : Except Refusal (W × Cl) :=
  Session.run [.propose 0 (cand (.lit 7) []), .prune 1 0 0 tH] (w0, start tpl0 w0)

/-- **Experiment 3.** The pruned branch carries its reason; `select` is refused naming it; when
`K` is withdrawn the repair re-judges exactly that candidate and it becomes selectable, with no
re-proposal. -/
theorem withdraw_pruning_reason :
    obs s3 = some [[.pruned [tK]]] ∧
    refusal s3sel = some (.notVerified (.pruned [tK])) ∧
    obs s3w = some [[.verified]] ∧ sel 0 s3w = some (some 0) ∧
    obs s3dead = some [[.verified]] := by
  decide

/-- Only the pruning chooser may prune. -/
theorem prune_needs_chooser :
    refusal (Session.run [.propose 0 (cand (.lit 7) []), .prune 2 0 0 tK] (w0, start tpl0 w0)) =
      some .notChooser := by
  decide

/-! ## Experiment 4: a positive cycle losing its grounding

The cycle is NOT expressible in the one-level closure (a support is a token, never another hole's
selection): this is a separate rule model, the semantics a multi-level extension would have to use.
The withdrawal world is not empty: an unrelated fact `5` and rule `6 :- 5` stay live and grounded. -/

/-- `p :- a.  p :- q.  q :- p.` with `a = 0`, `p = 1`, `q = 2`, beside the unrelated `6 :- 5`. -/
private def cycleRules : List Rule := [⟨1, [0]⟩, ⟨1, [2]⟩, ⟨2, [1]⟩, ⟨6, [5]⟩]

/-- Before: facts `a` and `5`. After withdrawing `a`: only `5`. -/
private def factsA : Nat → Bool := fun x => x == 0 || x == 5
private def factsNoA : Nat → Bool := fun x => x == 5
/-- The alive set before the withdrawal: `a`, `p`, `q`, `5`, `6`. -/
private def aliveBefore : Nat → Bool := fun x => x == 0 || x == 1 || x == 2 || x == 5 || x == 6

theorem cycle_grounded : Derives cycleRules factsA 1 ∧ Derives cycleRules factsA 2 :=
  ⟨lfpIter_sound 1 1 (by decide), lfpIter_sound 2 2 (by decide)⟩

/-- **Experiment 4, the least-fixpoint model.** Withdraw `a` (with `5` still live): `6` stays
grounded, neither `p` nor `q` is (`{a, p, q}` is an unfounded set). -/
theorem cycle_loses_grounding :
    Derives cycleRules factsNoA 6 ∧ ¬ Derives cycleRules factsNoA 1 ∧ ¬ Derives cycleRules factsNoA 2 := by
  have hF : ∀ x, (x = 0 ∨ x = 1 ∨ x = 2) → factsNoA x = false := by
    rintro x (rfl | rfl | rfl) <;> rfl
  have hR : ∀ r ∈ cycleRules, (r.head = 0 ∨ r.head = 1 ∨ r.head = 2) →
      ∃ y ∈ r.body, (y = 0 ∨ y = 1 ∨ y = 2) := by
    intro r hr hh
    simp only [cycleRules, List.mem_cons, List.mem_nil_iff, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> simp at hh ⊢
  exact ⟨lfpIter_sound 1 6 (by decide), unfounded_not_derivable hF hR (by simp),
    unfounded_not_derivable hF hR (by simp)⟩

/-- **Experiment 4, the tooth.** Naive COUNTING maintenance keeps `p` and `q` alive forever after
`a` is withdrawn: each still counts the other as a support. -/
theorem counting_keeps_cycle :
    ∀ n, countRun cycleRules factsNoA aliveBefore n 1 = true ∧
      countRun cycleRules factsNoA aliveBefore n 2 = true := by
  intro n
  induction n with
  | zero => exact ⟨rfl, rfl⟩
  | succ n ih =>
    obtain ⟨h1, h2⟩ := ih
    have hp : 0 < supportCount cycleRules factsNoA (countRun cycleRules factsNoA aliveBefore n) 1 := by
      unfold supportCount
      apply Nat.lt_of_lt_of_le _ (Nat.le_add_left _ _)
      apply List.length_pos_of_mem (a := ⟨1, [2]⟩)
      rw [List.mem_filter]
      exact ⟨by simp [cycleRules], by simp [h2]⟩
    have hq : 0 < supportCount cycleRules factsNoA (countRun cycleRules factsNoA aliveBefore n) 2 := by
      unfold supportCount
      apply Nat.lt_of_lt_of_le _ (Nat.le_add_left _ _)
      apply List.length_pos_of_mem (a := ⟨2, [1]⟩)
      rw [List.mem_filter]
      exact ⟨by simp [cycleRules], by simp [h1]⟩
    simp only [countRun, h1, h2, hp, hq, decide_true, Bool.and_self, and_self]

/-- Counting disagrees with the from-scratch least fixpoint: it is not a correct repair. -/
theorem counting_disagrees_with_lfp :
    countRun cycleRules factsNoA aliveBefore 7 1 = true ∧ ¬ Derives cycleRules factsNoA 1 :=
  ⟨(counting_keeps_cycle 7).1, cycle_loses_grounding.2.1⟩

/-! ## Experiment 5: a dependent-context change -/

/-- `d1 = 2`, `d2 = 5` under bound 10; `d2` selected. -/
private def s5 : Except Refusal (W × Cl) :=
  Session.run [.propose 0 (cand (.lit 2) []), .propose 0 (cand (.lit 5) []), .select 1 0 1]
    (w0, start tpl0 w0)

private def s5e : Except Refusal (W × Cl) := s5.bind fun st => Session.run [.edit (.setEnv 4)] st

private def s5only : Except Refusal (W × Cl) :=
  Session.run [.propose 0 (cand (.lit 5) []), .select 1 0 0] (w0, start tpl0 w0)

/-- **Experiment 5.** Lowering the bound to 4 makes the selected filling (index 5 ≥ 4) a checked
`conflict` (the guard cannot make it valid), exposes the obligation `refill 0` in `Φ`, and offers
the replacement `d1` without selecting it (the chooser's act); with no alternative the hole is
suspended. -/
theorem dependent_context_change :
    outs (.setEnv 4) s5 = some [(1, 0, 0)] ∧
    obs s5e = some [[.verified, .conflict .guardFails]] ∧
    sel 0 s5e = some (some 1) ∧
    phiS s5e = some [.refill 0] ∧
    phiS (s5e.bind fun st => Session.run [.select 1 0 0] st) = some [] ∧
    outs (.setEnv 4) s5only = some [(4, 0, 0)] := by
  decide

/-! ## Experiment 6: replace a filling preserving its exported contract -/

private def s6 : Except Refusal (W × Cl) :=
  Session.run [.propose 0 (cand (.lit 5) []), .propose 0 (cand (.add (.lit 2) (.lit 3)) []),
    .propose 0 (cand (.lit 7) []), .select 1 0 0] (w0, start tpl0 w0)

private def s6b : Except Refusal (W × Cl) := s6.bind fun st => Session.run [.select 1 0 1] st
private def s6c : Except Refusal (W × Cl) := s6.bind fun st => Session.run [.select 1 0 2] st

private def clOf : Except Refusal (W × Cl) → Cl
  | .ok st => st.2
  | .error _ => start tpl0 w0

/-- A consumer relying on the hole's VALUE, and one relying on its syntax (identity). -/
private def kVal (ok : Option Nat → Bool) : Consumer ToyCalc (Option Nat) := ⟨0, eval, ok⟩
private def kSyn : Consumer ToyCalc Tm := ⟨0, id, fun M => M == .lit 5⟩

/-- **Experiment 6.** Replacing `5` by `2 + 3` changes `σ` but not the exported value: EVERY
value consumer is unchanged (by `consumer_boundary`), while the syntax consumer breaks; replacing
it by `7` changes the value consumer. -/
theorem replace_filling_preserving_contract :
    (clOf s6).sigma 0 = some (.lit 5) ∧ (clOf s6b).sigma 0 = some (.add (.lit 2) (.lit 3)) ∧
    (∀ ok, (kVal ok).holds (clOf s6) = (kVal ok).holds (clOf s6b)) ∧
    kSyn.holds (clOf s6) = true ∧ kSyn.holds (clOf s6b) = false ∧
    (kVal fun v => v == some 5).holds (clOf s6c) = false := by
  refine ⟨by decide, by decide, fun ok => consumer_boundary _ (by simp only [kVal]; decide), by decide, by decide,
    by decide⟩

/-! ## Experiment 7: correct, but the cost guarantee is lost -/

private def s7 : Except Refusal (W × Cl) :=
  Session.run [.propose 0 (cand (.lit 3) [] 200), .propose 0 (cand (.lit 50) []),
    .propose 0 (cand (.lit 3) [])] (w0, start tpl0 w0)

/-- **Experiment 7.** A candidate whose guard holds but whose cost exceeds the budget is
`uncovered`: distinct from `verified` and from `conflict`, and not selectable. -/
theorem correct_but_cost_lost :
    obs s7 = some [[.uncovered 200 100, .conflict .guardFails, .verified]] ∧
    refusal (s7.bind fun st => Session.run [.select 1 0 0] st) =
      some (.notVerified (.uncovered 200 100)) ∧
    sel 0 (s7.bind fun st => Session.run [.select 1 0 2] st) = some (some 2) := by
  decide

/-! ## Experiment 8: re-apply an earlier filling -/

/-- `f1 = 5` under `A`, `f2 = 6` under `B`; `f1` selected; `A` withdrawn; the replacement `f2`
selected by the chooser after deselecting. -/
private def s8 : Except Refusal (W × Cl) :=
  Session.run [.propose 0 (cand (.lit 5) [tA]), .propose 0 (cand (.lit 6) [tB]), .select 1 0 0,
    .edit (.withdraw tA), .deselect 1 0, .select 1 0 1] (w0, start tpl0 w0)

private def s8back : Except Refusal (W × Cl) := s8.bind fun st => Session.run [.edit (.assert tA), .select 1 0 0] st

private def s8reissued : Except Refusal (W × Cl) :=
  s8.bind fun st => Session.run ((reissue 1 0 1).map Op.edit ++ [.select 1 0 0]) st

private def ncands : Except Refusal (W × Cl) → Option Nat
  | .ok st => some (st.2.slot 0).cands.length
  | .error _ => none

/-- **Experiment 8.** Candidates are retained across deselect; when `A` (the same immutable token)
is live again, the earlier filling is re-selected without re-proposal; when `A`'s id is re-issued
at a NEW version, the old candidate stays unusable. -/
theorem reapply_earlier_filling :
    outs (.withdraw tA) (Session.run [.propose 0 (cand (.lit 5) [tA]), .propose 0 (cand (.lit 6) [tB]),
      .select 1 0 0] (w0, start tpl0 w0)) = some [(1, 0, 1)] ∧
    sel 0 s8 = some (some 1) ∧ ncands s8 = some 2 ∧
    sel 0 s8back = some (some 0) ∧ ncands s8back = some 2 ∧
    refusal s8reissued = some (.notVerified (.suspended [tA])) := by
  decide

/-- The tooth of the token theorem: under a world keyed by id alone (versions ignored), the
re-issued id WOULD re-enable the old candidate. -/
private def unversioned (w : W) : W := { w with live := fun t => w.live ⟨t.id, 0⟩ || w.live ⟨t.id, 1⟩ }

theorem unversioned_reissue_reenables :
    judge hole0 (applyAll (reissue 1 0 1) w0) (cand (.lit 5) [tA]) ≠ .verified ∧
    judge hole0 (unversioned (applyAll (reissue 1 0 1) w0)) (cand (.lit 5) [tA]) = .verified :=
  ⟨reissued_support_unverified (by decide) (by decide), by decide⟩

/-! ## Strengthening: the proposal's obstruction, `a : A ⊢ a` with `a` withdrawn -/

/-- A hole with one hypothesis `x = 7` in its context, backed by token `H`. -/
private def holeH : Iface ToyCalc Nat :=
  { name := 0, ctx := ([7] : List Nat), ty := (), hyps := [(7, tH)], hyps_real := by decide,
    guard := fun _ _ => true, budget := 100, chooser := 1, acceptor := 2 }

private def tplH : Template ToyCalc Nat where
  Γ := ([7] : List Nat)
  T := ()
  P := Tm.hole 0
  Ω := [holeH]
  names := List.nodup_cons.2 ⟨by simp, List.nodup_nil⟩

private def wH : W := ⟨fun t => t == tH, 0⟩

/-- `g1 = x` (uses the hypothesis), `g2 = 3` (does not). -/
private def sH (i : Nat) : Except Refusal (W × Cl) :=
  Session.run [.propose 0 (cand (.var 7) []), .propose 0 (cand (.lit 3) []), .select 1 0 i]
    (wH, start tplH wH)

/-- Withdrawing `H` with `3` selected: the filling factors through the smaller context
(`strengthening`). With `x` selected: it loses its support (`suspended [H]`, no closed witness
of the hypothesis is invented) and `3` is offered as a replacement. -/
theorem withdraw_hypothesis_strengthens :
    outs (.withdraw tH) (sH 1) = some [(2, 0, 7)] ∧
    obs ((sH 1).bind fun st => Session.run [.edit (.withdraw tH)] st) =
      some [[.suspended [tH], .verified]] := by
  decide

theorem withdraw_used_hypothesis_obstructs :
    outs (.withdraw tH) (sH 0) = some [(1, 0, 1)] ∧
    sel 0 ((sH 0).bind fun st => Session.run [.edit (.withdraw tH)] st) = some (some 0) := by
  decide

/-! ## The tooth of derivability: an unchecked selection -/

/-- A closure that selects `x` in the empty context, bypassing `select`. -/
private def clBad : Cl :=
  { start tpl0 w0 with slot := fun _ => ⟨[cand (.var 9) []], some 0, false⟩ }

theorem unchecked_select_underivable :
    ¬ Derivable toyHasTy clBad ∧ ¬ WellFilled clBad ∧
    refusal (Session.run [.propose 0 (cand (.var 9) []), .select 1 0 0] (w0, start tpl0 w0)) =
      some (.notVerified (.conflict .illTyped)) := by
  refine ⟨by unfold Derivable toyHasTy; decide, fun h => ?_, by decide⟩
  obtain ⟨c, hc, hchk⟩ := h hole0 (List.mem_singleton.2 rfl) 0 rfl
  simp only [clBad, List.getElem?_cons_zero, Option.some.injEq] at hc
  subst hc
  revert hchk; decide

/-! ## Stability class -/

/-- A value-preserving rewrite: `5 ↦ 2 + 3`. -/
private def five : Tm → Tm := fun t => if t = .lit 5 then .add (.lit 2) (.lit 3) else t

theorem five_preserves_value : ∀ t, eval (five t) = eval t := by
  intro t
  unfold five
  split
  · rename_i h; subst h; rfl
  · rfl

private def isLit (_ : Nat) : Tm → Bool
  | .lit _ => true
  | _ => false

theorem valueBelow_valueGuard : ValueGuard (D := ToyCalc) eval valueBelow :=
  ⟨fun n v => match v with | some v => decide (v < n) | none => false, fun _ _ => rfl⟩

/-- The hole's value guard is stable under the value-preserving rewrite. -/
theorem value_guard_stable : StableUnder (D := ToyCalc) valueBelow five :=
  stability_class eval valueBelow_valueGuard five_preserves_value

/-- A guard that inspects syntax is NOT stable under the same rewrite, hence is not a value guard. -/
theorem syntactic_guard_not_stable :
    ¬ StableUnder (D := ToyCalc) isLit five ∧ ¬ ValueGuard (D := ToyCalc) eval isLit := by
  have h : ¬ StableUnder (D := ToyCalc) isLit five := fun h => by
    have := h 0 (.lit 5)
    revert this; decide
  exact ⟨h, fun hv => h (stability_class eval hv five_preserves_value)⟩

/-! ## Locality instance: an unrelated state update -/

/-- **Locality, instanced.** Withdrawing `K`, which no candidate of experiment 1 cites, leaves the
closure exactly as it was and reports nothing (the plan stays usable without being looked at). -/
theorem unrelated_withdraw_is_frame :
    (repair w0 (.withdraw tK) (clOf s1)).1 = clOf s1 ∧ (repair w0 (.withdraw tK) (clOf s1)).2.1 = [] ∧
      (repair w0 (.withdraw tK) (clOf s1)).2.2 = [] :=
  locality (t := tK) (Or.inl rfl) (by decide)

/-! ## The executed prefix, instanced -/

/-- `5` under `A` selected and ACCEPTED (executed); `6` under `B` retained. -/
private def s9 : Except Refusal (W × Cl) :=
  Session.run [.propose 0 (cand (.lit 5) [tA]), .propose 0 (cand (.lit 6) [tB]), .select 1 0 0,
    .accept 2 0] (w0, start tpl0 w0)

/-- After acceptance: re-selection is refused by name; the acceptance owes a settlement; a
withdrawal of the executed candidate's support does NOT re-plan (no replacement is offered even
though `6` is verified): the hole is suspended with `reconcile`, and the selection stands. Only the
acceptor accepts. -/
theorem executed_prefix_instance :
    refusal (s9.bind fun st => Session.run [.select 1 0 1] st) = some .accepted ∧
    phiS s9 = some [.settle 0 0] ∧
    outs (.withdraw tA) s9 = some [(4, 0, 0)] ∧
    obligations (.withdraw tA) s9 = some [.reconcile 0 0] ∧
    sel 0 (s9.bind fun st => Session.run [.edit (.withdraw tA)] st) = some (some 0) ∧
    refusal (Session.run [.propose 0 (cand (.lit 5) [tA]), .select 1 0 0, .accept 1 0]
      (w0, start tpl0 w0)) = some .notAcceptor := by
  decide

/-! ## Coherence and the repair log on an experiment state -/

theorem start_coherent (tpl : Template ToyCalc Nat) (w : W) : Coherent w (start tpl w) :=
  fromScratch_coherent w tpl _

/-- Experiment 1's state is coherent and well filled, by the session theorems (not by evaluation). -/
theorem s1_coherent : ∃ st, s1 = .ok st ∧ Coherent st.1 st.2 ∧ WellFilled st.2 := by
  cases h : s1 with
  | error r =>
    have hs : refusal s1 = none := by decide
    rw [h] at hs; cases hs
  | ok st =>
    refine ⟨st, rfl, ?_, ?_⟩
    · exact session_preserves_coherent _ (start_coherent tpl0 w0) h
    · exact session_preserves_wellFilled _ (fromScratch_wellFilled w0 tpl0 _) h

/-- Withdrawing `A` in experiment 1 re-judges candidate 0 (it cites `A`) and NOT candidate 1. -/
theorem rejudged_only_touched : (repair w0 (.withdraw tA) (clOf s1)).2.2 = [(0, 0)] := by
  decide

end Nanodregg.Lang.Contextual.Toy
