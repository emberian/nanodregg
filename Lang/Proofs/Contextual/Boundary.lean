/- Boundary declarations: the lattice, reuse licenses, dependent types, and concrete sessions. -/
import Lang.Contextual.Boundary
import Lang.Proofs.Contextual.Judge

namespace Nanodregg.Lang.Contextual
-- Lean's finite default maxHeartbeats cap applies; no local budget override.

def Declaration.Le (a b : Declaration) : Prop := ∀ o, a o = true → b o = true

theorem Declaration.le_refl (a : Declaration) : a.Le a := fun _ h => h

theorem Declaration.le_trans {a b c : Declaration} (hab : a.Le b) (hbc : b.Le c) :
    a.Le c := fun o ho => hbc o (hab o ho)

theorem Declaration.le_antisymm {a b : Declaration} (hab : a.Le b) (hba : b.Le a) :
    a = b := by
  funext o
  cases ha : a o <;> cases hb : b o <;> simp_all [Declaration.Le]

theorem Declaration.meet_glb (a b c : Declaration) :
    c.Le (a.meet b) ↔ c.Le a ∧ c.Le b := by
  simp only [Declaration.Le, Declaration.meet, Bool.and_eq_true]
  constructor
  · intro h; exact ⟨fun o ho => (h o ho).1, fun o ho => (h o ho).2⟩
  · rintro ⟨ha, hb⟩ o ho; exact ⟨ha o ho, hb o ho⟩

theorem Declaration.join_lub (a b c : Declaration) :
    (a.join b).Le c ↔ a.Le c ∧ b.Le c := by
  simp only [Declaration.Le, Declaration.join, Bool.or_eq_true]
  constructor
  · intro h; exact ⟨fun o ho => h o (Or.inl ho), fun o ho => h o (Or.inr ho)⟩
  · rintro ⟨ha, hb⟩ o (ho | ho)
    · exact ha o ho
    · exact hb o ho

theorem Declaration.bounds (a : Declaration) :
    Declaration.bottom.Le a ∧ a.Le Declaration.top := by
  simp [Declaration.Le, Declaration.bottom, Declaration.top]

/-- Cost and behavior are incomparable declarations, not adjacent rungs of a chain. -/
theorem Declaration.cost_behavior_independent :
    ¬ Declaration.Le (fun o => decide (o = Observation.costGuarantee))
      (fun o => decide (o = Observation.observableBehavior)) ∧
    ¬ Declaration.Le (fun o => decide (o = Observation.observableBehavior))
      (fun o => decide (o = Observation.costGuarantee)) := by
  constructor
  · intro h; have := h .costGuarantee (by decide); contradiction
  · intro h; have := h .observableBehavior (by decide); contradiction

variable {D : CalculusData} {E V : Type}

/-- A declaration is a promise, not itself a proof that the promise was met. -/
def preserves (b : Boundary D E V) (o : Observation) : Prop := b.declares o = true

def Boundary.Reestablished (b : Boundary D E V) (w w' : World E)
    (c c' : Candidate D) : Prop :=
  ∀ o, preserves b o → b.read w c o = b.read w' c' o

theorem Boundary.failure_iff [DecidableEq V] (b : Boundary D E V)
    (w w' : World E) (c c' : Candidate D) (o : Observation) :
    o ∈ b.failures w w' c c' ↔
      preserves b o ∧ b.read w c o ≠ b.read w' c' o := by
  have ho : o ∈ Observation.all := by cases o <;> simp [Observation.all]
  simp [Boundary.failures, ho, preserves]

/-- Per-observation evidence remains usable even when some OTHER observation failed. -/
theorem Boundary.read_eq_of_not_failed [DecidableEq V] {b : Boundary D E V}
    {w w' : World E} {c c' : Candidate D} {o : Observation}
    (hd : preserves b o) (hn : o ∉ b.failures w w' c c') :
    b.read w c o = b.read w' c' o := by
  by_cases he : b.read w c o = b.read w' c' o
  · exact he
  · exact False.elim (hn ((b.failure_iff w w' c c' o).2 ⟨hd, he⟩))

/-- Exact coverage: an empty obligation list means every declared observation was preserved.
This is checked against the old reference; it cannot be made true by dropping the failed entry. -/
theorem Boundary.failures_nil_iff [DecidableEq V] (b : Boundary D E V)
    (w w' : World E) (c c' : Candidate D) :
    b.failures w w' c c' = [] ↔ b.Reestablished w w' c c' := by
  constructor
  · intro h o ho
    by_cases he : b.read w c o = b.read w' c' o
    · exact he
    · have := (b.failure_iff w w' c c' o).2 ⟨ho, he⟩
      rw [h] at this; cases this
  · intro h
    apply List.eq_nil_iff_forall_not_mem.2
    intro o ho
    obtain ⟨hd, hn⟩ := (b.failure_iff w w' c c' o).1 ho
    exact hn (h o hd)

/-- If a declaration is NOT re-established, a particular observation must travel beyond
the boundary. No disjunction with a vacuously true success arm. -/
theorem Boundary.failed_obligation [DecidableEq V] {b : Boundary D E V}
    {w w' : World E} {c c' : Candidate D} {cl cl' : Closure D E}
    (hsel : cl.selectedCand b.iface.name = some c)
    (hsel' : cl'.selectedCand b.iface.name = some c')
    {o : Observation} (hd : preserves b o)
    (hn : b.read w c o ≠ b.read w' c' o) :
    (b.iface.name, o) ∈ b.obligations w w' cl cl' := by
  simp only [Boundary.obligations, hsel, hsel']
  exact List.mem_map.2 ⟨o, (b.failure_iff w w' c c' o).2 ⟨hd, hn⟩, rfl⟩

/-- Declaring more observations cannot remove an already exposed failure. -/
theorem Boundary.failures_mono [DecidableEq V] (b : Boundary D E V)
    {a a' : Declaration} (hle : a.Le a') (w w' : World E) (c c' : Candidate D) :
    ∀ o ∈ ({ b with declares := a }).failures w w' c c',
      o ∈ ({ b with declares := a' }).failures w w' c c' := by
  intro o ho
  obtain ⟨hd, hn⟩ := (Boundary.failure_iff _ _ _ _ _ _).1 ho
  exact (Boundary.failure_iff _ _ _ _ _ _).2 ⟨hle o hd, hn⟩

/-- Typing reuse is the calculus's meta-substitution lemma on a client template,
not an equality of status labels. The client may inspect the hole only through its declaration. -/
theorem Boundary.reuse_client_typing [DecidableEq V]
    {HasTy : List (HoleDecl D.Ctx D.Ty) → D.Ctx → D.Tm → D.Ty → Prop}
    (L : CalculusLaws D HasTy) {b : Boundary D E V} {w w' : World E}
    {c c' : Candidate D} (hr : .typingInterface ∉ b.failures w w' c c')
    (hd : preserves b .typingInterface)
    (hold : HasTy [] b.iface.ctx c.filling b.iface.ty)
    {Γ : D.Ctx} {P : D.Tm} {T : D.Ty}
    (client : HasTy [b.iface.decl] Γ P T) :
    HasTy [] Γ
      (D.msubst (fun u => if u = b.iface.name then some c'.filling else none) P) T := by
  have hc : HasTy [] b.iface.ctx c'.filling b.iface.ty :=
    L.check_sound ((Boundary.read_eq_of_not_failed hd hr).symm.trans (L.check_complete hold))
  have h := L.msubst_lemma
    (fun u => if u = b.iface.name then some c'.filling else none) client
    (by
      intro d hd M hM
      simp only [List.mem_singleton] at hd
      subst d
      simp only [Iface.decl, if_true, Option.some.injEq] at hM
      subst M
      exact hc)
  simpa [Iface.decl] using h

/-- A client's proof depending solely on the declared Boolean contract can be carried.
The old contract must actually hold; preserving two failures establishes nothing. -/
theorem Boundary.reuse_client_contract [DecidableEq V] {b : Boundary D E V} {w w' : World E}
    {c c' : Candidate D} (hr : .logicalContract ∉ b.failures w w' c c')
    (hd : preserves b .logicalContract) (hold : b.iface.guard w.env c.filling = true)
    {Q : E → D.Tm → Prop}
    (client : ∀ env term, b.iface.guard env term = true → Q env term) :
    Q w'.env c'.filling := by
  exact client _ _ ((Boundary.read_eq_of_not_failed hd hr).symm.trans hold)

/-- Every downstream observation factoring through the declared behavior has the same cache
key/result, including non-Boolean observations. -/
theorem Boundary.reuse_cached_observation [DecidableEq V] {b : Boundary D E V} {w w' : World E}
    {c c' : Candidate D} (hr : .observableBehavior ∉ b.failures w w' c c')
    (hd : preserves b .observableBehavior) {R : Type} (client : V → R) :
    client (b.behavior w.env c.filling) = client (b.behavior w'.env c'.filling) :=
  congrArg client (Boundary.read_eq_of_not_failed hd hr)

/-- A scheduler's overhead can be composed with the promised cost bound. This uses the
candidate's cost field; an instance must connect that field to its cost semantics. -/
theorem Boundary.reuse_cost_bound [DecidableEq V] {b : Boundary D E V} {w w' : World E}
    {c c' : Candidate D} (hr : .costGuarantee ∉ b.failures w w' c c')
    (hd : preserves b .costGuarantee) (hold : c.cost ≤ b.costBound) (overhead : Nat) :
    c'.cost + overhead ≤ b.costBound + overhead := by
  have h : decide (c'.cost ≤ b.costBound) = true :=
    (Boundary.read_eq_of_not_failed hd hr).symm.trans (decide_eq_true hold)
  exact Nat.add_le_add_right (of_decide_eq_true h) overhead

/-- Same carrier type (Nat) is insufficient: changing 1 to 0 destroys a dependent Fin fiber. -/
theorem dependent_inhabitants_change_types :
    Nonempty (Fin 1) ∧ ¬ Nonempty (Fin 0) := by
  exact ⟨⟨⟨0, by decide⟩⟩, fun ⟨i⟩ => Nat.not_lt_zero i.val i.isLt⟩

/-- Thus there is no generic local replacement of dependent data from the inhabitant's
carrier type alone. -/
theorem no_unconditional_dependent_reuse :
    ¬ (∀ n m : Nat, Nonempty (Fin n) → Nonempty (Fin m)) := by
  intro h
  exact dependent_inhabitants_change_types.2
    (h 1 0 dependent_inhabitants_change_types.1)

/-- Abstraction gives the needed transport: a dependent client's type mentions only the
preserved behavior. Equality of that behavior transports its inhabitant. -/
theorem Boundary.reuse_abstract_dependent_client [DecidableEq V] {b : Boundary D E V} {w w' : World E}
    {c c' : Candidate D} (hr : .observableBehavior ∉ b.failures w w' c c')
    (hd : preserves b .observableBehavior) (F : V → Type)
    (old : Nonempty (F (b.behavior w.env c.filling))) :
    Nonempty (F (b.behavior w'.env c'.filling)) := by
  have he : b.behavior w.env c.filling = b.behavior w'.env c'.filling :=
    Boundary.read_eq_of_not_failed hd hr
  rw [← he]
  exact old

/-- An entire retained region reopens when its sole exclusion argument is withdrawn.
The region is explicit and finite; no successful answer's trace appears in the premises. -/
theorem pruning_explanation_reopens_region {I : Iface D E} {w : World E} {t : Token}
    (region : List (Candidate D)) (hlive : w.live t = true)
    (hregion : ∀ c ∈ region,
      D.check I.ctx c.filling I.ty = true ∧ I.guard w.env c.filling = true ∧
      c.blockers = [t] ∧ (∀ s ∈ effSupports I c, w.live s = true ∧ s ≠ t) ∧
      c.cost ≤ I.budget) :
    ∀ c ∈ region, judge I w c = .pruned [t] ∧
      judge I ((Edit.withdraw t).apply w) c = .verified := by
  intro c hc
  obtain ⟨ht, hg, hb, hs, hcost⟩ := hregion c hc
  refine ⟨by simp [judge, ht, hg, hb, hlive], judge_verified_iff.2 ?_⟩
  refine ⟨ht, hg, ?_, ?_, hcost⟩
  · intro s hmem
    rw [hb] at hmem
    simp only [List.mem_singleton] at hmem
    subst s
    simp [Edit.apply, World.set]
  · intro s hmem
    obtain ⟨hl, hne⟩ := hs s hmem
    simp [Edit.apply, World.set, hne, hl]

namespace BoundarySearch

/-- These costs are computed by the search algorithms, not manually labelled candidates. -/
theorem search_probe_measurement :
    run input .binary = some (true, 3) ∧ run input .linear = some (true, 8) := by decide

/-- Withdrawal opens binary's sortedness obligation; linear is selected through the existing
chooser operation, preserving membership. Both candidate statuses and the selection compute. -/
theorem binary_to_linear_session :
    observations before = some ([[.verified, .verified]], some 0, some true) ∧
    observations after = some ([[.suspended [sortedToken], .verified]], some 1, some true) := by
  decide

/-- Membership and behavior survive; the four-probe logarithmic promise is the EXACT propagated
obligation, despite the fallback remaining admissible under the original eight-probe budget. -/
theorem binary_to_linear_boundary :
    boundaryReport = some [(0, .costGuarantee)] := by decide

/-- All queries in this concrete domain exercise positive and negative membership answers. -/
theorem search_membership_domain :
    (List.range 10).all (fun key =>
      membership ⟨input.xs, key⟩ .binary && membership ⟨input.xs, key⟩ .linear) = true := by
  decide

/-- Removing sortedness is not evidence of unsortedness. But actually changing the input to an
unsorted one demonstrates why binary's precondition cannot be erased. -/
theorem unsorted_binary_tooth :
    membership ⟨[2, 0, 1], 2⟩ .binary = false ∧
    membership ⟨[2, 0, 1], 2⟩ .linear = true := by decide

/-- The selected answer has no token dependencies. Nonetheless withdrawing the exclusion
reason re-judges exactly the alternative and reopens it. -/
theorem pruning_beyond_selected_trace :
    pruningReport = some ([], [(0, 1)], [[.verified, .verified]]) := by decide

/-- Every observation check is live: an unbound variable is ill typed, fails the contract,
has no behavior, and exceeds the declared bound through the failed-run cost. -/
theorem all_observation_checks_exercised :
    boundary.failures world world (candidate .binary [sortedToken]) (candidate (.var 0) []) =
      [.typingInterface, .logicalContract, .observableBehavior, .costGuarantee] := by decide

/-- Missing selections are not a vacuous success, even when both sides are missing. -/
theorem unfilled_boundary_obligations :
    boundary.obligations world world start start =
      [(0, .typingInterface), (0, .logicalContract), (0, .observableBehavior), (0, .costGuarantee)] := by
  decide

/-- The general cache-reuse license applies to this swap despite its reported cost failure. -/
theorem membership_clients_survive_cost_failure {R : Type} (client : Option Bool → R) :
    client (boundary.behavior world.env (candidate .binary [sortedToken]).filling) =
      client (boundary.behavior ((Edit.withdraw sortedToken).apply world).env
        (candidate .linear []).filling) :=
  Boundary.reuse_cached_observation (b := boundary) (w := world)
    (w' := (Edit.withdraw sortedToken).apply world)
    (c := candidate .binary [sortedToken]) (c' := candidate .linear [])
    (by decide) (by rfl) client

end BoundarySearch
end Nanodregg.Lang.Contextual
