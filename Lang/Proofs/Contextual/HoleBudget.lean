/- Exact expansion counts, checked before live contextual filling allocates syntax. -/
import Lang.HoleBudget
import Lang.Proofs.Contextual.LangFilling

namespace Nanodregg.Lang.Contextual

mutual
theorem renameVar_nodes (ρ : Nat → Nat) : ∀ t : Term,
    Term.nodes (Term.renameVar ρ t) = Term.nodes t
  | .var i => by simp only [Term.renameVar, Term.nodes]
  | .nat n => by simp only [Term.renameVar, Term.nodes]
  | .bool b => by simp only [Term.renameVar, Term.nodes]
  | .bytes b => by simp only [Term.renameVar, Term.nodes]
  | .digest b => by simp only [Term.renameVar, Term.nodes]
  | .ref n => by simp only [Term.renameVar, Term.nodes]
  | .refuse A w => by simp only [Term.renameVar, Term.nodes]
  | .lam A b => by simp only [Term.renameVar, Term.nodes, renameVar_nodes (upR ρ) b]
  | .fix t => by simp only [Term.renameVar, Term.nodes, renameVar_nodes ρ t]
  | .get t l => by simp only [Term.renameVar, Term.nodes, renameVar_nodes ρ t]
  | .inj A l t => by simp only [Term.renameVar, Term.nodes, renameVar_nodes ρ t]
  | .app a b => by simp only [Term.renameVar, Term.nodes, renameVar_nodes ρ a, renameVar_nodes ρ b]
  | .prim p a b => by simp only [Term.renameVar, Term.nodes, renameVar_nodes ρ a, renameVar_nodes ρ b]
  | .record fs => by simp only [Term.renameVar, Term.nodes, renameVarRow_nodes ρ fs]
  | .extend t fs => by simp only [Term.renameVar, Term.nodes, renameVar_nodes ρ t, renameVarRow_nodes ρ fs]
  | .case t fs => by simp only [Term.renameVar, Term.nodes, renameVar_nodes ρ t, renameVarArms_nodes ρ fs]
  | .ite c a b => by simp only [Term.renameVar, Term.nodes, renameVar_nodes ρ c, renameVar_nodes ρ a, renameVar_nodes ρ b]
  | .hole n ts => by simp only [Term.renameVar, Term.nodes, renameVarList_nodes ρ ts]

theorem renameVarRow_nodes (ρ : Nat → Nat) : ∀ ts : List (Label × Term),
    Term.rowNodes (Term.renameVarRow ρ ts) = Term.rowNodes ts
  | [] => rfl
  | (_, t) :: ts => by simp only [Term.renameVarRow, Term.rowNodes, renameVar_nodes ρ t, renameVarRow_nodes ρ ts]

theorem renameVarArms_nodes (ρ : Nat → Nat) : ∀ ts : List (Label × Term),
    Term.rowNodes (Term.renameVarArms ρ ts) = Term.rowNodes ts
  | [] => rfl
  | (_, t) :: ts => by simp only [Term.renameVarArms, Term.rowNodes, renameVar_nodes (upR ρ) t, renameVarArms_nodes ρ ts]

theorem renameVarList_nodes (ρ : Nat → Nat) : ∀ ts : List Term,
    Term.listNodes (Term.renameVarList ρ ts) = Term.listNodes ts
  | [] => rfl
  | t :: ts => by simp only [Term.renameVarList, Term.listNodes, renameVar_nodes ρ t, renameVarList_nodes ρ ts]
end

theorem upVarSubst_nodes (σ : Nat → Term) :
    (fun i => Term.nodes (Term.upVarSubst σ i)) = upNodeSubst (fun i => Term.nodes (σ i)) := by
  funext i
  cases i with
  | zero => rfl
  | succ i => exact renameVar_nodes Nat.succ (σ i)

mutual
theorem substVar_nodes (σ : Nat → Term) : ∀ t : Term,
    Term.nodes (Term.substVar σ t) = Term.substNodes (fun i => Term.nodes (σ i)) t
  | .var i => by simp only [Term.substVar, Term.substNodes]
  | .nat n => by simp only [Term.substVar, Term.nodes, Term.substNodes]
  | .bool b => by simp only [Term.substVar, Term.nodes, Term.substNodes]
  | .bytes b => by simp only [Term.substVar, Term.nodes, Term.substNodes]
  | .digest b => by simp only [Term.substVar, Term.nodes, Term.substNodes]
  | .ref n => by simp only [Term.substVar, Term.nodes, Term.substNodes]
  | .refuse A w => by simp only [Term.substVar, Term.nodes, Term.substNodes]
  | .lam A b => by simp only [Term.substVar, Term.nodes, Term.substNodes, substVar_nodes (Term.upVarSubst σ) b, upVarSubst_nodes]
  | .fix t => by simp only [Term.substVar, Term.nodes, Term.substNodes, substVar_nodes σ t]
  | .get t l => by simp only [Term.substVar, Term.nodes, Term.substNodes, substVar_nodes σ t]
  | .inj A l t => by simp only [Term.substVar, Term.nodes, Term.substNodes, substVar_nodes σ t]
  | .app a b => by simp only [Term.substVar, Term.nodes, Term.substNodes, substVar_nodes σ a, substVar_nodes σ b]
  | .prim p a b => by simp only [Term.substVar, Term.nodes, Term.substNodes, substVar_nodes σ a, substVar_nodes σ b]
  | .record fs => by simp only [Term.substVar, Term.nodes, Term.substNodes, substVarRow_nodes σ fs]
  | .extend t fs => by simp only [Term.substVar, Term.nodes, Term.substNodes, substVar_nodes σ t, substVarRow_nodes σ fs]
  | .case t fs => by simp only [Term.substVar, Term.nodes, Term.substNodes, substVar_nodes σ t, substVarArms_nodes σ fs]
  | .ite c a b => by simp only [Term.substVar, Term.nodes, Term.substNodes, substVar_nodes σ c, substVar_nodes σ a, substVar_nodes σ b]
  | .hole n ts => by simp only [Term.substVar, Term.nodes, Term.substNodes, substVarList_nodes σ ts]

theorem substVarRow_nodes (σ : Nat → Term) : ∀ ts : List (Label × Term),
    Term.rowNodes (Term.substVarRow σ ts) = Term.substRowNodes (fun i => Term.nodes (σ i)) ts
  | [] => rfl
  | (_, t) :: ts => by
      simp only [Term.substVarRow, Term.rowNodes, Term.substRowNodes,
        substVar_nodes σ t, substVarRow_nodes σ ts]

theorem substVarArms_nodes (σ : Nat → Term) : ∀ ts : List (Label × Term),
    Term.rowNodes (Term.substVarArms σ ts) = Term.substArmsNodes (fun i => Term.nodes (σ i)) ts
  | [] => rfl
  | (_, t) :: ts => by
      simp only [Term.substVarArms, Term.rowNodes, Term.substArmsNodes,
        substVar_nodes (Term.upVarSubst σ) t, substVarArms_nodes σ ts, upVarSubst_nodes]

theorem substVarList_nodes (σ : Nat → Term) : ∀ ts : List Term,
    Term.listNodes (Term.substVarList σ ts) = Term.substListNodes (fun i => Term.nodes (σ i)) ts
  | [] => rfl
  | t :: ts => by
      simp only [Term.substVarList, Term.listNodes, Term.substListNodes,
        substVar_nodes σ t, substVarList_nodes σ ts]
end

theorem substListFn_nodes : ∀ (ts : List Term) (i : Nat),
    Term.nodes (Term.substListFn ts i) = nodeListFn (ts.map Term.nodes) i
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: ts, i + 1 => substListFn_nodes ts i

theorem substList_nodes (ts : List Term) (t : Term) :
    Term.nodes (Term.substList ts t) = Term.substNodes (nodeListFn (ts.map Term.nodes)) t := by
  rw [Term.substList, substVar_nodes]
  congr 1
  funext i
  exact substListFn_nodes ts i

theorem listNodes_fold : ∀ ts : List Term,
    Term.listNodes ts = (ts.map Term.nodes).foldr (fun n r => 1 + n + r) 0
  | [] => rfl
  | t :: ts => by simp only [Term.listNodes, List.map_cons, List.foldr_cons, listNodes_fold ts]

mutual
theorem fillRefs_nodes (σ : Nat → Option Term) : ∀ t : Term,
    Term.nodes (Term.fillRefs σ t) = Term.fillNodes σ t
  | .var i => by simp only [Term.fillRefs, Term.nodes, Term.fillNodes]
  | .nat n => by simp only [Term.fillRefs, Term.nodes, Term.fillNodes]
  | .bool b => by simp only [Term.fillRefs, Term.nodes, Term.fillNodes]
  | .bytes b => by simp only [Term.fillRefs, Term.nodes, Term.fillNodes]
  | .digest b => by simp only [Term.fillRefs, Term.nodes, Term.fillNodes]
  | .ref n => by simp only [Term.fillRefs, Term.nodes, Term.fillNodes]
  | .refuse A w => by simp only [Term.fillRefs, Term.nodes, Term.fillNodes]
  | .lam A b => by simp only [Term.fillRefs, Term.nodes, Term.fillNodes, fillRefs_nodes σ b]
  | .fix t => by simp only [Term.fillRefs, Term.nodes, Term.fillNodes, fillRefs_nodes σ t]
  | .get t l => by simp only [Term.fillRefs, Term.nodes, Term.fillNodes, fillRefs_nodes σ t]
  | .inj A l t => by simp only [Term.fillRefs, Term.nodes, Term.fillNodes, fillRefs_nodes σ t]
  | .app a b => by simp only [Term.fillRefs, Term.nodes, Term.fillNodes, fillRefs_nodes σ a, fillRefs_nodes σ b]
  | .prim p a b => by simp only [Term.fillRefs, Term.nodes, Term.fillNodes, fillRefs_nodes σ a, fillRefs_nodes σ b]
  | .record fs => by simp only [Term.fillRefs, Term.nodes, Term.fillNodes, fillRefsRow_nodes σ fs]
  | .extend t fs => by simp only [Term.fillRefs, Term.nodes, Term.fillNodes, fillRefs_nodes σ t, fillRefsRow_nodes σ fs]
  | .case t fs => by simp only [Term.fillRefs, Term.nodes, Term.fillNodes, fillRefs_nodes σ t, fillRefsRow_nodes σ fs]
  | .ite c a b => by simp only [Term.fillRefs, Term.nodes, Term.fillNodes, fillRefs_nodes σ c, fillRefs_nodes σ a, fillRefs_nodes σ b]
  | .hole n ts => by
      cases hs : σ n with
      | none => simp only [Term.fillRefs, Term.fillNodes, hs, Term.nodes, listNodes_fold, fillRefsList_nodes]
      | some t => simp only [Term.fillRefs, Term.fillNodes, hs, substList_nodes, fillRefsList_nodes]

theorem fillRefsRow_nodes (σ : Nat → Option Term) : ∀ ts : List (Label × Term),
    Term.rowNodes (Term.fillRefsRow σ ts) = Term.fillRowNodes σ ts
  | [] => rfl
  | (_, t) :: ts => by
      simp only [Term.fillRefsRow, Term.rowNodes, Term.fillRowNodes, fillRefs_nodes σ t, fillRefsRow_nodes σ ts]

theorem fillRefsList_nodes (σ : Nat → Option Term) : ∀ ts : List Term,
    (Term.fillRefsList σ ts).map Term.nodes = Term.fillArgNodes σ ts
  | [] => rfl
  | t :: ts => by
      simp only [Term.fillRefsList, List.map_cons, Term.fillArgNodes, fillRefs_nodes σ t, fillRefsList_nodes σ ts]
end

/-- Successful bounded expansion has the measured output bound and the work bound.
Neither inequality is assumed of the result. -/
theorem fillBounded_bounds {limit candidateMax : Nat} {σ : Nat → Option Term} {t result : Term}
    (h : Term.fillBounded limit candidateMax σ t = .ok result) :
    Term.nodes result ≤ limit ∧ Term.nodes t * (candidateMax + 1) ≤ limit := by
  unfold Term.fillBounded at h
  split at h
  · cases h
  · rename_i hw
    split at h
    · cases h
    · rename_i hs
      cases h
      rw [fillRefs_nodes]
      exact ⟨Nat.le_of_not_gt hs, Nat.le_of_not_gt hw⟩

end Nanodregg.Lang.Contextual
