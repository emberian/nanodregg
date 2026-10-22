/- Live preparation is charged from its committed ROM, including blocked holes. -/
import Lang.Proofs.Contextual.LiveHoles

namespace Nanodregg.Lang

theorem factor_fold_nodes (xs : List Nat) (Γ : List Ty) (t : Term) :
    Term.nodes ((xs.foldl (fun (a : List Ty × Term) x =>
      (a.1.eraseIdx x, Term.renameVar (lowerIdx x) a.2)) (Γ, t)).2) = Term.nodes t := by
  induction xs generalizing Γ t with
  | nil => rfl
  | cons x xs ih =>
    rw [List.foldl_cons, ih, renameVar_nodes]

theorem factorHole_nodes (h : HoleROM) (c : HoleCode) (removed : List Nat) :
    Term.nodes (factorHole h c removed).2.1 = Term.nodes c.body :=
  factor_fold_nodes removed.reverse h.ctx c.body

theorem selectHole_nodes {D : Type} {rv : Kernel.Receive.RowView D} {self : D}
    {h : HoleROM} {s : HoleSelection} (hs : selectHole rv self h = .ok s) :
    Term.nodes s.body = Term.nodes s.original := by
  unfold selectHole at hs
  simp only [bind, Except.bind, pure, Except.pure] at hs
  repeat' split at hs
  all_goals first | (simp at hs; done) | skip
  simp only [Except.ok.injEq] at hs
  subst s
  rw [renameVar_nodes]
  exact factorHole_nodes _ _ _

theorem foldMax_start {α : Type} (f : α → Nat) (xs : List α) (n : Nat) :
    n ≤ xs.foldl (fun n a => max n (f a)) n := by
  induction xs generalizing n with
  | nil => exact Nat.le_refl n
  | cons x xs ih => exact Nat.le_trans (Nat.le_max_left _ _) (ih _)

theorem foldMax_member {α : Type} (f : α → Nat) (xs : List α) (n : Nat)
    (a : α) (ha : a ∈ xs) : f a ≤ xs.foldl (fun n a => max n (f a)) n := by
  induction xs generalizing n with
  | nil => simp at ha
  | cons x xs ih =>
    simp only [List.mem_cons] at ha
    rcases ha with rfl | ha
    · exact Nat.le_trans (Nat.le_max_right _ _) (foldMax_start f xs _)
    · exact ih _ ha

theorem foldMax_le {α : Type} (f : α → Nat) (xs : List α) (n m : Nat)
    (hn : n ≤ m) (hx : ∀ a ∈ xs, f a ≤ m) :
    xs.foldl (fun n a => max n (f a)) n ≤ m := by
  induction xs generalizing n with
  | nil => exact hn
  | cons x xs ih =>
    exact ih _ (Nat.max_le.mpr ⟨hn, hx x (by simp)⟩)
      (fun a ha => hx a (by simp [ha]))

/-- Selected code retains the ROM candidate's size through strengthening;
a blocked refusal has one node. Both fit the same committed maximum. -/
theorem resolutionMax_committed {D : Type} (rv : Kernel.Receive.RowView D) (self : D)
    (hs : List HoleROM) :
    resolutionMax (hs.map (resolveHole rv self)) ≤
      (hs.flatMap (fun h => h.code)).foldl (fun n c => max n (Term.nodes c.body)) 1 := by
  apply foldMax_le
  · exact foldMax_start _ _ _
  · intro r hr
    obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hr
    cases he : selectHole rv self h with
    | error why =>
      simp only [resolveHole, he, HoleResolution.body, Term.nodes]
      exact foldMax_start _ _ _
    | ok s =>
      simp only [resolveHole, he, HoleResolution.body]
      rw [selectHole_nodes he]
      obtain ⟨c, _, _, _, _, hc, horig, _⟩ := selectHole_origin he
      rw [horig]
      exact foldMax_member (fun c : HoleCode => Term.nodes c.body) _ 1 c (List.mem_flatMap.mpr
        ⟨h, hh, List.mem_of_getElem? hc⟩)

/-- The actual selected/blocked expansion and all signature-guard allowances
fit the preparation charged by the deployed loader from the original ROM. -/
theorem instantiateHoles_cost {D : Type} {rv : Kernel.Receive.RowView D} {self : D}
    {Δ : List Ty} {p : Package} {i : HoleInstance}
    (h : instantiateHoles rv self Δ p = .ok i) :
    i.cost ≤ p.preparationCost := by
  have hc : i.cost = if p.holes.isEmpty then 0 else
      Term.nodes p.body * (resolutionMax (p.holes.map (resolveHole rv self)) + 1) +
        256 * p.holes.length := by
    unfold instantiateHoles at h
    simp only [bind, Except.bind, pure, Except.pure] at h
    repeat' split at h
    all_goals first | (simp at h; done) | skip
    all_goals
      simp only [Except.ok.injEq] at h
      subst i
      simp_all
  rw [hc, Package.preparationCost]
  split
  · exact Nat.le_refl 0
  · have hm := resolutionMax_committed rv self p.holes
    have hmul := Nat.mul_le_mul_left (Term.nodes p.body) (Nat.add_le_add_right hm 1)
    simpa only [Nat.add_comm] using Nat.add_le_add_right hmul (256 * p.holes.length)

end Nanodregg.Lang
