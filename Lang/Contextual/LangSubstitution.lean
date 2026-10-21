/- Capture-avoiding ordinary substitution for the deployed Lang terms.
This is the common substitution operation needed by a contextual hole occurrence.
The hole signature and installed candidate representation are separate decisions. -/
import Lang.Check
import Lang.Contextual.Core

namespace Nanodregg.Lang.Contextual

mutual
/-- Rename the free variables (`lam` and every `case` arm bind one more). -/
def Term.renameVar (ρ : Nat → Nat) : Term → Term
  | .var i => .var (ρ i)
  | .lam a b => .lam a (Term.renameVar (upR ρ) b)
  | .app f a => .app (Term.renameVar ρ f) (Term.renameVar ρ a)
  | .fix t => .fix (Term.renameVar ρ t)
  | .nat n => .nat n
  | .bool b => .bool b
  | .bytes s => .bytes s
  | .digest s => .digest s
  | .prim p a b => .prim p (Term.renameVar ρ a) (Term.renameVar ρ b)
  | .record fs => .record (Term.renameVarRow ρ fs)
  | .get t ℓ => .get (Term.renameVar ρ t) ℓ
  | .extend t fs => .extend (Term.renameVar ρ t) (Term.renameVarRow ρ fs)
  | .inj a ℓ t => .inj a ℓ (Term.renameVar ρ t)
  | .case t arms => .case (Term.renameVar ρ t) (Term.renameVarArms ρ arms)
  | .ite c a b => .ite (Term.renameVar ρ c) (Term.renameVar ρ a) (Term.renameVar ρ b)
  | .ref i => .ref i
  | .hole n σ => .hole n (Term.renameVarList ρ σ)
  | .refuse T w => .refuse T w
def Term.renameVarList (ρ : Nat → Nat) : List Term → List Term
  | [] => []
  | t :: ts => Term.renameVar ρ t :: Term.renameVarList ρ ts
/-- Fields bind nothing. -/
def Term.renameVarRow (ρ : Nat → Nat) : List (Label × Term) → List (Label × Term)
  | [] => []
  | (ℓ, t) :: fs => (ℓ, Term.renameVar ρ t) :: Term.renameVarRow ρ fs
/-- Every arm binds its payload at index 0. -/
def Term.renameVarArms (ρ : Nat → Nat) : List (Label × Term) → List (Label × Term)
  | [] => []
  | (ℓ, t) :: as => (ℓ, Term.renameVar (upR ρ) t) :: Term.renameVarArms ρ as
end


/-- Extend a substitution under one ordinary binder: preserve its new variable,
and shift every substituted free variable past it. -/
def Term.upVarSubst (σ : Nat → Term) : Nat → Term
  | 0 => .var 0
  | i + 1 => Term.renameVar Nat.succ (σ i)

mutual
/-- Simultaneous, capture-avoiding substitution of ordinary variables.
Package references are constants; case payloads bind exactly like lambdas. -/
def Term.substVar (σ : Nat → Term) : Term → Term
  | .var i => σ i
  | .lam A b => .lam A (Term.substVar (Term.upVarSubst σ) b)
  | .app f a => .app (Term.substVar σ f) (Term.substVar σ a)
  | .fix t => .fix (Term.substVar σ t)
  | .nat n => .nat n
  | .bool b => .bool b
  | .bytes s => .bytes s
  | .digest s => .digest s
  | .prim p a b => .prim p (Term.substVar σ a) (Term.substVar σ b)
  | .record fs => .record (Term.substVarRow σ fs)
  | .get t l => .get (Term.substVar σ t) l
  | .extend t fs => .extend (Term.substVar σ t) (Term.substVarRow σ fs)
  | .inj A l t => .inj A l (Term.substVar σ t)
  | .case t arms => .case (Term.substVar σ t) (Term.substVarArms σ arms)
  | .ite c a b => .ite (Term.substVar σ c) (Term.substVar σ a) (Term.substVar σ b)
  | .ref n => .ref n
  | .hole n ts => .hole n (Term.substVarList σ ts)
  | .refuse A why => .refuse A why
def Term.substVarList (σ : Nat → Term) : List Term → List Term
  | [] => []
  | t :: ts => Term.substVar σ t :: Term.substVarList σ ts
def Term.substVarRow (σ : Nat → Term) : List (Label × Term) → List (Label × Term)
  | [] => []
  | (l, t) :: fs => (l, Term.substVar σ t) :: Term.substVarRow σ fs
def Term.substVarArms (σ : Nat → Term) : List (Label × Term) → List (Label × Term)
  | [] => []
  | (l, t) :: arms =>
      (l, Term.substVar (Term.upVarSubst σ) t) :: Term.substVarArms σ arms
end

/-- A list supplies the first variables; beyond the list, indices are lowered
by its length. Thus a singleton gives ordinary beta substitution. -/
def Term.substListFn : List Term → Nat → Term
  | [], i => .var i
  | t :: _, 0 => t
  | _ :: ts, i + 1 => Term.substListFn ts i

/-- Instantiate a term in its declared context by an explicit substitution. -/
def Term.substList (σ : List Term) (t : Term) : Term :=
  Term.substVar (Term.substListFn σ) t

end Nanodregg.Lang.Contextual
