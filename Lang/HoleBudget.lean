/- Bound contextual expansion before allocating its resulting syntax.
Counts are syntax nodes, including row/substitution cons cells. -/
import Lang.Subst

namespace Nanodregg.Lang

mutual
def Term.nodes : Term → Nat
  | .var _ | .nat _ | .bool _ | .bytes _ | .digest _ | .ref _ | .refuse _ _ => 1
  | .lam _ b | .fix b | .get b _ | .inj _ _ b => 1 + Term.nodes b
  | .app a b | .prim _ a b => 1 + Term.nodes a + Term.nodes b
  | .record fs => 1 + Term.rowNodes fs
  | .extend t fs | .case t fs => 1 + Term.nodes t + Term.rowNodes fs
  | .ite c a b => 1 + Term.nodes c + Term.nodes a + Term.nodes b
  | .hole _ ts => 1 + Term.listNodes ts
def Term.rowNodes : List (Label × Term) → Nat
  | [] => 0
  | (_, t) :: ts => 1 + Term.nodes t + Term.rowNodes ts
def Term.listNodes : List Term → Nat
  | [] => 0
  | t :: ts => 1 + Term.nodes t + Term.listNodes ts
end

def upNodeSubst (σ : Nat → Nat) : Nat → Nat
  | 0 => 1
  | i + 1 => σ i

mutual
/-- Exact output size of ordinary substitution; binders preserve one new variable. -/
def Term.substNodes (σ : Nat → Nat) : Term → Nat
  | .var i => σ i
  | .nat _ | .bool _ | .bytes _ | .digest _ | .ref _ | .refuse _ _ => 1
  | .lam _ b => 1 + Term.substNodes (upNodeSubst σ) b
  | .fix b | .get b _ | .inj _ _ b => 1 + Term.substNodes σ b
  | .app a b | .prim _ a b => 1 + Term.substNodes σ a + Term.substNodes σ b
  | .record fs => 1 + Term.substRowNodes σ fs
  | .extend t fs => 1 + Term.substNodes σ t + Term.substRowNodes σ fs
  | .case t fs => 1 + Term.substNodes σ t + Term.substArmsNodes σ fs
  | .ite c a b => 1 + Term.substNodes σ c + Term.substNodes σ a + Term.substNodes σ b
  | .hole _ ts => 1 + Term.substListNodes σ ts
def Term.substRowNodes (σ : Nat → Nat) : List (Label × Term) → Nat
  | [] => 0
  | (_, t) :: ts => 1 + Term.substNodes σ t + Term.substRowNodes σ ts
def Term.substArmsNodes (σ : Nat → Nat) : List (Label × Term) → Nat
  | [] => 0
  | (_, t) :: ts => 1 + Term.substNodes (upNodeSubst σ) t + Term.substArmsNodes σ ts
def Term.substListNodes (σ : Nat → Nat) : List Term → Nat
  | [] => 0
  | t :: ts => 1 + Term.substNodes σ t + Term.substListNodes σ ts
end

/-- Missing list entries remain variables, exactly as substListFn. -/
def nodeListFn : List Nat → Nat → Nat
  | [], _ => 1
  | n :: _, 0 => n
  | _ :: ns, i + 1 => nodeListFn ns i

mutual
/-- Compute the output count using only input syntax and integers, before filling. -/
def Term.fillNodes (σ : Nat → Option Term) : Term → Nat
  | .var _ | .nat _ | .bool _ | .bytes _ | .digest _ | .ref _ | .refuse _ _ => 1
  | .lam _ b | .fix b | .get b _ | .inj _ _ b => 1 + Term.fillNodes σ b
  | .app a b | .prim _ a b => 1 + Term.fillNodes σ a + Term.fillNodes σ b
  | .record fs => 1 + Term.fillRowNodes σ fs
  | .extend t fs | .case t fs => 1 + Term.fillNodes σ t + Term.fillRowNodes σ fs
  | .ite c a b => 1 + Term.fillNodes σ c + Term.fillNodes σ a + Term.fillNodes σ b
  | .hole n ts =>
      let ns := Term.fillArgNodes σ ts
      match σ n with
      | none => 1 + ns.foldr (fun n r => 1 + n + r) 0
      | some t => Term.substNodes (nodeListFn ns) t
def Term.fillRowNodes (σ : Nat → Option Term) : List (Label × Term) → Nat
  | [] => 0
  | (_, t) :: ts => 1 + Term.fillNodes σ t + Term.fillRowNodes σ ts
def Term.fillArgNodes (σ : Nat → Option Term) : List Term → List Nat
  | [] => []
  | t :: ts => Term.fillNodes σ t :: Term.fillArgNodes σ ts
end

/-- The two expansion bounds `fillBounded` refuses by name. -/
inductive ExpansionBound where
  | work
  | size
  deriving DecidableEq, Repr

/-- Refuse oversized expansion before constructing it. The second input bounds
the structural work (template nodes times the largest candidate), independently
of whether the resulting term happens to be small. -/
def Term.fillBounded (limit candidateMax : Nat) (σ : Nat → Option Term) (t : Term) : Except ExpansionBound Term :=
  if Term.nodes t * (candidateMax + 1) > limit then .error .work
  else if Term.fillNodes σ t > limit then .error .size
  else .ok (Term.fillRefs σ t)

end Nanodregg.Lang
