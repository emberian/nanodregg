/-
P11a: independent winning/losing derivations and sound draw certificates.
Köhler–Ludäscher–Zinn, First-Order Provenance Games (2013), PDF pp3–4.
No claim that arbitrary outsideThisProcedure limits imply a semantic draw.
-/
import Lang.Contextual.Games

namespace Nanodregg.Lang.Contextual.P5.Games

/-- Köhler et al., PDF p4, backward induction: win by moving to a loss; lose if
every successor is won. The latter includes sinks. These finite derivations are
independent of checkDraw and may be used in any finitely branching arena. -/
inductive Solved {V : Type} (moves : V → List V) : Bool → V → Prop where
  | win {x y} : y ∈ moves x → Solved moves false y → Solved moves true x
  | lose {x} : (∀ y ∈ moves x, Solved moves true y) → Solved moves false x

/-- Köhler et al., PDF p4: draw means neither won nor lost, rather than an empty
search result or an operational timeout. -/
def Draw {V : Type} (moves : V → List V) (x : V) : Prop :=
  ¬ Solved moves true x ∧ ¬ Solved moves false x

/-- Köhler et al., PDF p4: winning and losing evidence are incompatible, by
induction on their independent backward-induction derivations. -/
theorem solved_exclusive {V : Type} {moves : V → List V} {b : Bool} {x : V}
    (h : Solved moves b x) : ¬ Solved moves (!b) x := by
  induction h with
  | win hm _ ih =>
    intro hl
    cases hl with
    | lose hs => exact ih (hs _ hm)
  | lose _ ih =>
    intro hw
    cases hw with
    | win hm hl => exact ih _ hm hl

/-- Köhler et al., PDF pp3–4: a closed region without sinks has no finite
winning or losing derivation. Both certificate checks are needed in the induction. -/
theorem trap_unsolved {V : Type} {moves : V → List V} {region : List V}
    (hstep : ∀ x ∈ region, ∃ y, y ∈ moves x)
    (hclosed : ∀ x ∈ region, ∀ y ∈ moves x, y ∈ region)
    {b : Bool} {x : V} (hx : x ∈ region) : ¬ Solved moves b x := by
  intro hs
  induction hs with
  | win hm _ ih => exact ih (hclosed _ hx _ hm)
  | lose _ ih =>
    obtain ⟨y, hy⟩ := hstep _ hx
    exact ih y hy (hclosed _ hx y hy)

/-- Köhler et al., PDF p4: a checked finite trap proves a semantic draw.
Nonemptiness, successor closure and root coverage are replayed, not assumed. -/
theorem checkDraw_sound {moves : Nat → List Nat} {root : Nat} {region : List Nat}
    (h : checkDraw moves root region = true) : Draw moves root := by
  simp only [checkDraw, Bool.and_eq_true, List.contains_iff_mem, List.all_eq_true,
    Bool.not_eq_true'] at h
  have hstep : ∀ x ∈ region, ∃ y, y ∈ moves x := by
    intro x hx
    have hn : moves x ≠ [] := by
      intro he
      have := (h.2 x hx).1
      simp [he] at this
    exact List.exists_mem_of_ne_nil _ hn
  have hclosed : ∀ x ∈ region, ∀ y ∈ moves x, y ∈ region := by
    intro x hx y hy
    simpa using (h.2 x hx).2 y hy
  exact ⟨trap_unsolved hstep hclosed h.1, trap_unsolved hstep hclosed h.1⟩

/-- Köhler et al., PDF p4: returned outside/drawn carries a replayed certificate
and proves neither win nor loss; unlike a procedureLimit it is semantic evidence. -/
theorem outside_draw_sound {moves : Nat → List Nat} {root : Nat}
    {region reported : List Nat}
    (h : judgeDraw moves root region = .outsideThisProcedure (.drawn reported)) :
    reported = region ∧ checkDraw moves root region = true ∧ Draw moves root := by
  unfold judgeDraw at h
  split at h
  · rename_i hc
    cases h
    exact ⟨rfl, hc, checkDraw_sound hc⟩
  · cases h

/-- Köhler et al., PDF p3: a self-loop certifies indefinite play; the result is
produced by the checker and has the independent neither-won-nor-lost meaning. -/
theorem loop_is_draw :
    judgeDraw loopMoves 0 [0] = .outsideThisProcedure (.drawn [0]) ∧ Draw loopMoves 0 :=
  ⟨by decide, checkDraw_sound (region := [0]) (by decide)⟩

/-- Köhler et al., PDF p3: a sink is a genuine loss and must never certify draw. -/
theorem sink_is_not_draw :
    judgeDraw (fun _ => []) 0 [0] = .open .invalidRefutation [] ∧
      Solved (fun _ => []) false 0 := by
  refine ⟨by decide, .lose ?_⟩
  intro y hy
  cases hy

/-- Köhler et al., PDF p4: a loop with an escape to a losing sink is won, not drawn.
Dropping successor closure from the certificate makes this real case fail. -/
theorem escape_is_not_draw :
    judgeDraw (fun x => if x = 0 then [0, 1] else []) 0 [0] =
      .open .invalidRefutation [] ∧
    Solved (fun x => if x = 0 then [0, 1] else []) true 0 := by
  refine ⟨by decide, .win (y := 1) (by simp) (.lose ?_)⟩
  intro y hy
  simp at hy

/-- Köhler et al., PDF p4: a valid trap elsewhere says nothing about a losing
root. Dropping root coverage would falsely turn this sink into a draw. -/
theorem unrelated_loop_is_not_draw :
    judgeDraw (fun x => if x = 1 then [1] else []) 0 [1] =
      .open .invalidRefutation [] ∧
    Solved (fun x => if x = 1 then [1] else []) false 0 := by
  refine ⟨by decide, .lose ?_⟩
  intro y hy
  simp at hy

end Nanodregg.Lang.Contextual.P5.Games
