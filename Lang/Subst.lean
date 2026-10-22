/-
# Lang.Subst — the deployed term operations over `Lang.Term`

Capture-avoiding renaming and substitution of ordinary variables (`renameVar`, `substVar`, `substList`), the
contextual-hole filling `fillRefs` (a substituted hole `hole n σ` carries explicit arguments for its declared
local context; the selected open filling is instantiated at `σ` without capture; ordinary `ref` terms remain
imports), the occurrence tests `usesVar`/`usesRef`, decidable equality, and a hole's declared type `holeTy`.
The Host runs these (through `Lang.HoleBudget`, `Lang.HoleROM`, `Lang.LiveHoles`); their typing facts are in
`Lang.Proofs.Subst` and `Lang.Proofs.Fill`, and the deployed
language as a closure calculus is `Lang.Contextual.LangInstance`.

Binders: `lam` binds one variable, every `case` arm binds its payload at index 0; record and
extend fields bind nothing.
-/
import Lang.Check
import Lang.Index

namespace Nanodregg.Lang

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


/-! ## Decidable equality of terms -/

mutual
/-- Decide equality of terms: structural, every verdict carrying its proof (no `deriving` for
the nested rows in v4.30.0). -/
def Term.decEq : (a b : Term) → Decidable (a = b)
  | .var a0, .var b0 =>
    match _root_.decEq a0 b0 with
    | isFalse h0 => isFalse (by intro e; injection e with e0; exact h0 e0)
    | isTrue h0 =>
      isTrue (by subst h0; rfl)
  | .lam a0 a1, .lam b0 b1 =>
    match _root_.decEq a0 b0 with
    | isFalse h0 => isFalse (by intro e; injection e with e0 e1; exact h0 e0)
    | isTrue h0 =>
      match Term.decEq a1 b1 with
      | isFalse h1 => isFalse (by intro e; injection e with e0 e1; exact h1 e1)
      | isTrue h1 =>
        isTrue (by subst h0; subst h1; rfl)
  | .app a0 a1, .app b0 b1 =>
    match Term.decEq a0 b0 with
    | isFalse h0 => isFalse (by intro e; injection e with e0 e1; exact h0 e0)
    | isTrue h0 =>
      match Term.decEq a1 b1 with
      | isFalse h1 => isFalse (by intro e; injection e with e0 e1; exact h1 e1)
      | isTrue h1 =>
        isTrue (by subst h0; subst h1; rfl)
  | .fix a0, .fix b0 =>
    match Term.decEq a0 b0 with
    | isFalse h0 => isFalse (by intro e; injection e with e0; exact h0 e0)
    | isTrue h0 =>
      isTrue (by subst h0; rfl)
  | .nat a0, .nat b0 =>
    match _root_.decEq a0 b0 with
    | isFalse h0 => isFalse (by intro e; injection e with e0; exact h0 e0)
    | isTrue h0 =>
      isTrue (by subst h0; rfl)
  | .bool a0, .bool b0 =>
    match _root_.decEq a0 b0 with
    | isFalse h0 => isFalse (by intro e; injection e with e0; exact h0 e0)
    | isTrue h0 =>
      isTrue (by subst h0; rfl)
  | .bytes a0, .bytes b0 =>
    match _root_.decEq a0 b0 with
    | isFalse h0 => isFalse (by intro e; injection e with e0; exact h0 e0)
    | isTrue h0 =>
      isTrue (by subst h0; rfl)
  | .digest a0, .digest b0 =>
    match _root_.decEq a0 b0 with
    | isFalse h0 => isFalse (by intro e; injection e with e0; exact h0 e0)
    | isTrue h0 =>
      isTrue (by subst h0; rfl)
  | .prim a0 a1 a2, .prim b0 b1 b2 =>
    match _root_.decEq a0 b0 with
    | isFalse h0 => isFalse (by intro e; injection e with e0 e1 e2; exact h0 e0)
    | isTrue h0 =>
      match Term.decEq a1 b1 with
      | isFalse h1 => isFalse (by intro e; injection e with e0 e1 e2; exact h1 e1)
      | isTrue h1 =>
        match Term.decEq a2 b2 with
        | isFalse h2 => isFalse (by intro e; injection e with e0 e1 e2; exact h2 e2)
        | isTrue h2 =>
          isTrue (by subst h0; subst h1; subst h2; rfl)
  | .record a0, .record b0 =>
    match Term.decEqRow a0 b0 with
    | isFalse h0 => isFalse (by intro e; injection e with e0; exact h0 e0)
    | isTrue h0 =>
      isTrue (by subst h0; rfl)
  | .get a0 a1, .get b0 b1 =>
    match Term.decEq a0 b0 with
    | isFalse h0 => isFalse (by intro e; injection e with e0 e1; exact h0 e0)
    | isTrue h0 =>
      match _root_.decEq a1 b1 with
      | isFalse h1 => isFalse (by intro e; injection e with e0 e1; exact h1 e1)
      | isTrue h1 =>
        isTrue (by subst h0; subst h1; rfl)
  | .extend a0 a1, .extend b0 b1 =>
    match Term.decEq a0 b0 with
    | isFalse h0 => isFalse (by intro e; injection e with e0 e1; exact h0 e0)
    | isTrue h0 =>
      match Term.decEqRow a1 b1 with
      | isFalse h1 => isFalse (by intro e; injection e with e0 e1; exact h1 e1)
      | isTrue h1 =>
        isTrue (by subst h0; subst h1; rfl)
  | .inj a0 a1 a2, .inj b0 b1 b2 =>
    match _root_.decEq a0 b0 with
    | isFalse h0 => isFalse (by intro e; injection e with e0 e1 e2; exact h0 e0)
    | isTrue h0 =>
      match _root_.decEq a1 b1 with
      | isFalse h1 => isFalse (by intro e; injection e with e0 e1 e2; exact h1 e1)
      | isTrue h1 =>
        match Term.decEq a2 b2 with
        | isFalse h2 => isFalse (by intro e; injection e with e0 e1 e2; exact h2 e2)
        | isTrue h2 =>
          isTrue (by subst h0; subst h1; subst h2; rfl)
  | .case a0 a1, .case b0 b1 =>
    match Term.decEq a0 b0 with
    | isFalse h0 => isFalse (by intro e; injection e with e0 e1; exact h0 e0)
    | isTrue h0 =>
      match Term.decEqRow a1 b1 with
      | isFalse h1 => isFalse (by intro e; injection e with e0 e1; exact h1 e1)
      | isTrue h1 =>
        isTrue (by subst h0; subst h1; rfl)
  | .ite a0 a1 a2, .ite b0 b1 b2 =>
    match Term.decEq a0 b0 with
    | isFalse h0 => isFalse (by intro e; injection e with e0 e1 e2; exact h0 e0)
    | isTrue h0 =>
      match Term.decEq a1 b1 with
      | isFalse h1 => isFalse (by intro e; injection e with e0 e1 e2; exact h1 e1)
      | isTrue h1 =>
        match Term.decEq a2 b2 with
        | isFalse h2 => isFalse (by intro e; injection e with e0 e1 e2; exact h2 e2)
        | isTrue h2 =>
          isTrue (by subst h0; subst h1; subst h2; rfl)
  | .ref a0, .ref b0 =>
    match _root_.decEq a0 b0 with
    | isFalse h0 => isFalse (by intro e; injection e with e0; exact h0 e0)
    | isTrue h0 =>
      isTrue (by subst h0; rfl)
  | .hole n ts, .hole m us =>
    match _root_.decEq n m with
    | isFalse h => isFalse (by intro e; injection e with e; exact h e)
    | isTrue h =>
      match Term.decEqList ts us with
      | isFalse h2 => isFalse (by intro e; injection e with _ e; exact h2 e)
      | isTrue h2 => isTrue (by subst h; subst h2; rfl)
  | .refuse a0 a1, .refuse b0 b1 =>
    match _root_.decEq a0 b0 with
    | isFalse h0 => isFalse (by intro e; injection e with e0 e1; exact h0 e0)
    | isTrue h0 =>
      match _root_.decEq a1 b1 with
      | isFalse h1 => isFalse (by intro e; injection e with e0 e1; exact h1 e1)
      | isTrue h1 =>
        isTrue (by subst h0; subst h1; rfl)
  | .var _, .lam _ _
  | .var _, .app _ _
  | .var _, .fix _
  | .var _, .nat _
  | .var _, .bool _
  | .var _, .bytes _
  | .var _, .digest _
  | .var _, .prim _ _ _
  | .var _, .record _
  | .var _, .get _ _
  | .var _, .extend _ _
  | .var _, .inj _ _ _
  | .var _, .case _ _
  | .var _, .ite _ _ _
  | .var _, .ref _
  | .var _, .refuse _ _ => isFalse (by intro e; cases e)
  | .lam _ _, .var _
  | .lam _ _, .app _ _
  | .lam _ _, .fix _
  | .lam _ _, .nat _
  | .lam _ _, .bool _
  | .lam _ _, .bytes _
  | .lam _ _, .digest _
  | .lam _ _, .prim _ _ _
  | .lam _ _, .record _
  | .lam _ _, .get _ _
  | .lam _ _, .extend _ _
  | .lam _ _, .inj _ _ _
  | .lam _ _, .case _ _
  | .lam _ _, .ite _ _ _
  | .lam _ _, .ref _
  | .lam _ _, .refuse _ _ => isFalse (by intro e; cases e)
  | .app _ _, .var _
  | .app _ _, .lam _ _
  | .app _ _, .fix _
  | .app _ _, .nat _
  | .app _ _, .bool _
  | .app _ _, .bytes _
  | .app _ _, .digest _
  | .app _ _, .prim _ _ _
  | .app _ _, .record _
  | .app _ _, .get _ _
  | .app _ _, .extend _ _
  | .app _ _, .inj _ _ _
  | .app _ _, .case _ _
  | .app _ _, .ite _ _ _
  | .app _ _, .ref _
  | .app _ _, .refuse _ _ => isFalse (by intro e; cases e)
  | .fix _, .var _
  | .fix _, .lam _ _
  | .fix _, .app _ _
  | .fix _, .nat _
  | .fix _, .bool _
  | .fix _, .bytes _
  | .fix _, .digest _
  | .fix _, .prim _ _ _
  | .fix _, .record _
  | .fix _, .get _ _
  | .fix _, .extend _ _
  | .fix _, .inj _ _ _
  | .fix _, .case _ _
  | .fix _, .ite _ _ _
  | .fix _, .ref _
  | .fix _, .refuse _ _ => isFalse (by intro e; cases e)
  | .nat _, .var _
  | .nat _, .lam _ _
  | .nat _, .app _ _
  | .nat _, .fix _
  | .nat _, .bool _
  | .nat _, .bytes _
  | .nat _, .digest _
  | .nat _, .prim _ _ _
  | .nat _, .record _
  | .nat _, .get _ _
  | .nat _, .extend _ _
  | .nat _, .inj _ _ _
  | .nat _, .case _ _
  | .nat _, .ite _ _ _
  | .nat _, .ref _
  | .nat _, .refuse _ _ => isFalse (by intro e; cases e)
  | .bool _, .var _
  | .bool _, .lam _ _
  | .bool _, .app _ _
  | .bool _, .fix _
  | .bool _, .nat _
  | .bool _, .bytes _
  | .bool _, .digest _
  | .bool _, .prim _ _ _
  | .bool _, .record _
  | .bool _, .get _ _
  | .bool _, .extend _ _
  | .bool _, .inj _ _ _
  | .bool _, .case _ _
  | .bool _, .ite _ _ _
  | .bool _, .ref _
  | .bool _, .refuse _ _ => isFalse (by intro e; cases e)
  | .bytes _, .var _
  | .bytes _, .lam _ _
  | .bytes _, .app _ _
  | .bytes _, .fix _
  | .bytes _, .nat _
  | .bytes _, .bool _
  | .bytes _, .digest _
  | .bytes _, .prim _ _ _
  | .bytes _, .record _
  | .bytes _, .get _ _
  | .bytes _, .extend _ _
  | .bytes _, .inj _ _ _
  | .bytes _, .case _ _
  | .bytes _, .ite _ _ _
  | .bytes _, .ref _
  | .bytes _, .refuse _ _ => isFalse (by intro e; cases e)
  | .digest _, .var _
  | .digest _, .lam _ _
  | .digest _, .app _ _
  | .digest _, .fix _
  | .digest _, .nat _
  | .digest _, .bool _
  | .digest _, .bytes _
  | .digest _, .prim _ _ _
  | .digest _, .record _
  | .digest _, .get _ _
  | .digest _, .extend _ _
  | .digest _, .inj _ _ _
  | .digest _, .case _ _
  | .digest _, .ite _ _ _
  | .digest _, .ref _
  | .digest _, .refuse _ _ => isFalse (by intro e; cases e)
  | .prim _ _ _, .var _
  | .prim _ _ _, .lam _ _
  | .prim _ _ _, .app _ _
  | .prim _ _ _, .fix _
  | .prim _ _ _, .nat _
  | .prim _ _ _, .bool _
  | .prim _ _ _, .bytes _
  | .prim _ _ _, .digest _
  | .prim _ _ _, .record _
  | .prim _ _ _, .get _ _
  | .prim _ _ _, .extend _ _
  | .prim _ _ _, .inj _ _ _
  | .prim _ _ _, .case _ _
  | .prim _ _ _, .ite _ _ _
  | .prim _ _ _, .ref _
  | .prim _ _ _, .refuse _ _ => isFalse (by intro e; cases e)
  | .record _, .var _
  | .record _, .lam _ _
  | .record _, .app _ _
  | .record _, .fix _
  | .record _, .nat _
  | .record _, .bool _
  | .record _, .bytes _
  | .record _, .digest _
  | .record _, .prim _ _ _
  | .record _, .get _ _
  | .record _, .extend _ _
  | .record _, .inj _ _ _
  | .record _, .case _ _
  | .record _, .ite _ _ _
  | .record _, .ref _
  | .record _, .refuse _ _ => isFalse (by intro e; cases e)
  | .get _ _, .var _
  | .get _ _, .lam _ _
  | .get _ _, .app _ _
  | .get _ _, .fix _
  | .get _ _, .nat _
  | .get _ _, .bool _
  | .get _ _, .bytes _
  | .get _ _, .digest _
  | .get _ _, .prim _ _ _
  | .get _ _, .record _
  | .get _ _, .extend _ _
  | .get _ _, .inj _ _ _
  | .get _ _, .case _ _
  | .get _ _, .ite _ _ _
  | .get _ _, .ref _
  | .get _ _, .refuse _ _ => isFalse (by intro e; cases e)
  | .extend _ _, .var _
  | .extend _ _, .lam _ _
  | .extend _ _, .app _ _
  | .extend _ _, .fix _
  | .extend _ _, .nat _
  | .extend _ _, .bool _
  | .extend _ _, .bytes _
  | .extend _ _, .digest _
  | .extend _ _, .prim _ _ _
  | .extend _ _, .record _
  | .extend _ _, .get _ _
  | .extend _ _, .inj _ _ _
  | .extend _ _, .case _ _
  | .extend _ _, .ite _ _ _
  | .extend _ _, .ref _
  | .extend _ _, .refuse _ _ => isFalse (by intro e; cases e)
  | .inj _ _ _, .var _
  | .inj _ _ _, .lam _ _
  | .inj _ _ _, .app _ _
  | .inj _ _ _, .fix _
  | .inj _ _ _, .nat _
  | .inj _ _ _, .bool _
  | .inj _ _ _, .bytes _
  | .inj _ _ _, .digest _
  | .inj _ _ _, .prim _ _ _
  | .inj _ _ _, .record _
  | .inj _ _ _, .get _ _
  | .inj _ _ _, .extend _ _
  | .inj _ _ _, .case _ _
  | .inj _ _ _, .ite _ _ _
  | .inj _ _ _, .ref _
  | .inj _ _ _, .refuse _ _ => isFalse (by intro e; cases e)
  | .case _ _, .var _
  | .case _ _, .lam _ _
  | .case _ _, .app _ _
  | .case _ _, .fix _
  | .case _ _, .nat _
  | .case _ _, .bool _
  | .case _ _, .bytes _
  | .case _ _, .digest _
  | .case _ _, .prim _ _ _
  | .case _ _, .record _
  | .case _ _, .get _ _
  | .case _ _, .extend _ _
  | .case _ _, .inj _ _ _
  | .case _ _, .ite _ _ _
  | .case _ _, .ref _
  | .case _ _, .refuse _ _ => isFalse (by intro e; cases e)
  | .ite _ _ _, .var _
  | .ite _ _ _, .lam _ _
  | .ite _ _ _, .app _ _
  | .ite _ _ _, .fix _
  | .ite _ _ _, .nat _
  | .ite _ _ _, .bool _
  | .ite _ _ _, .bytes _
  | .ite _ _ _, .digest _
  | .ite _ _ _, .prim _ _ _
  | .ite _ _ _, .record _
  | .ite _ _ _, .get _ _
  | .ite _ _ _, .extend _ _
  | .ite _ _ _, .inj _ _ _
  | .ite _ _ _, .case _ _
  | .ite _ _ _, .ref _
  | .ite _ _ _, .refuse _ _ => isFalse (by intro e; cases e)
  | .ref _, .var _
  | .ref _, .lam _ _
  | .ref _, .app _ _
  | .ref _, .fix _
  | .ref _, .nat _
  | .ref _, .bool _
  | .ref _, .bytes _
  | .ref _, .digest _
  | .ref _, .prim _ _ _
  | .ref _, .record _
  | .ref _, .get _ _
  | .ref _, .extend _ _
  | .ref _, .inj _ _ _
  | .ref _, .case _ _
  | .ref _, .ite _ _ _
  | .ref _, .refuse _ _ => isFalse (by intro e; cases e)
  | .refuse _ _, .var _
  | .refuse _ _, .lam _ _
  | .refuse _ _, .app _ _
  | .refuse _ _, .fix _
  | .refuse _ _, .nat _
  | .refuse _ _, .bool _
  | .refuse _ _, .bytes _
  | .refuse _ _, .digest _
  | .refuse _ _, .prim _ _ _
  | .refuse _ _, .record _
  | .refuse _ _, .get _ _
  | .refuse _ _, .extend _ _
  | .refuse _ _, .inj _ _ _
  | .refuse _ _, .case _ _
  | .refuse _ _, .ite _ _ _
  | .refuse _ _, .ref _ => isFalse (by intro e; cases e)
  | .hole _ _, .var _
  | .var _, .hole _ _
  | .hole _ _, .lam _ _
  | .lam _ _, .hole _ _
  | .hole _ _, .app _ _
  | .app _ _, .hole _ _
  | .hole _ _, .fix _
  | .fix _, .hole _ _
  | .hole _ _, .nat _
  | .nat _, .hole _ _
  | .hole _ _, .bool _
  | .bool _, .hole _ _
  | .hole _ _, .bytes _
  | .bytes _, .hole _ _
  | .hole _ _, .digest _
  | .digest _, .hole _ _
  | .hole _ _, .prim _ _ _
  | .prim _ _ _, .hole _ _
  | .hole _ _, .record _
  | .record _, .hole _ _
  | .hole _ _, .get _ _
  | .get _ _, .hole _ _
  | .hole _ _, .extend _ _
  | .extend _ _, .hole _ _
  | .hole _ _, .inj _ _ _
  | .inj _ _ _, .hole _ _
  | .hole _ _, .case _ _
  | .case _ _, .hole _ _
  | .hole _ _, .ite _ _ _
  | .ite _ _ _, .hole _ _
  | .hole _ _, .ref _
  | .ref _, .hole _ _
  | .hole _ _, .refuse _ _
  | .refuse _ _, .hole _ _ => isFalse (by intro e; cases e)
def Term.decEqList : (ts us : List Term) → Decidable (ts = us)
  | [], [] => isTrue rfl
  | t :: ts, u :: us =>
    match Term.decEq t u with
    | isFalse h => isFalse (by intro e; exact h (List.cons.inj e).1)
    | isTrue h =>
      match Term.decEqList ts us with
      | isFalse h2 => isFalse (by intro e; exact h2 (List.cons.inj e).2)
      | isTrue h2 => isTrue (by subst h; subst h2; rfl)
  | [], _ :: _ | _ :: _, [] => isFalse (by intro e; cases e)
/-- Decide equality of rows (record fields, case arms). -/
def Term.decEqRow : (fs gs : List (Label × Term)) → Decidable (fs = gs)
  | [], [] => isTrue rfl
  | (l, t) :: fs, (m, s) :: gs =>
    match _root_.decEq l m with
    | isFalse h0 => isFalse (by intro e; injection e with e0 e1; injection e0 with e0 e2; exact h0 e0)
    | isTrue h0 =>
      match Term.decEq t s with
      | isFalse h1 => isFalse (by intro e; injection e with e0 e1; injection e0 with e0 e2; exact h1 e2)
      | isTrue h1 =>
        match Term.decEqRow fs gs with
        | isFalse h2 => isFalse (by intro e; injection e with e0 e1; exact h2 e1)
        | isTrue h2 => isTrue (by subst h0; subst h1; subst h2; rfl)
  | [], _ :: _ | _ :: _, [] => isFalse (by intro e; cases e)
end

instance Term.instDecEq : DecidableEq Term := Term.decEq

/-! ## Variables: renaming and occurrence -/


mutual
/-- Does the term use the free variable `k`? -/
def Term.usesVar (k : Nat) : Term → Bool
  | .var i => i == k
  | .hole _ σ => Term.usesVarList k σ
  | .lam _ b => Term.usesVar (k + 1) b
  | .app f a => Term.usesVar k f || Term.usesVar k a
  | .fix t => Term.usesVar k t
  | .nat _ | .bool _ | .bytes _ | .digest _ | .ref _ | .refuse _ _ => false
  | .prim _ a b => Term.usesVar k a || Term.usesVar k b
  | .record fs => Term.usesVarRow k fs
  | .get t _ => Term.usesVar k t
  | .extend t fs => Term.usesVar k t || Term.usesVarRow k fs
  | .inj _ _ t => Term.usesVar k t
  | .case t arms => Term.usesVar k t || Term.usesVarArms k arms
  | .ite c a b => Term.usesVar k c || Term.usesVar k a || Term.usesVar k b
def Term.usesVarList (k : Nat) : List Term → Bool
  | [] => false
  | t :: ts => Term.usesVar k t || Term.usesVarList k ts
def Term.usesVarRow (k : Nat) : List (Label × Term) → Bool
  | [] => false
  | (_, t) :: fs => Term.usesVar k t || Term.usesVarRow k fs
def Term.usesVarArms (k : Nat) : List (Label × Term) → Bool
  | [] => false
  | (_, t) :: as => Term.usesVar (k + 1) t || Term.usesVarArms k as
end

/-! ## Named contextual holes (ordinary imports are excluded) -/

mutual
/-- Does the term contain contextual hole `n`, including in its substitutions? -/
def Term.usesRef (n : Nat) : Term → Bool
  | .ref _ => false
  | .hole i σ => i == n || Term.usesRefList n σ
  | .var _ | .nat _ | .bool _ | .bytes _ | .digest _ | .refuse _ _ => false
  | .lam _ b | .fix b | .get b _ | .inj _ _ b => Term.usesRef n b
  | .app f a | .prim _ f a => Term.usesRef n f || Term.usesRef n a
  | .record fs => Term.usesRefRow n fs
  | .extend t fs | .case t fs => Term.usesRef n t || Term.usesRefRow n fs
  | .ite c a b => Term.usesRef n c || Term.usesRef n a || Term.usesRef n b
def Term.usesRefList (n : Nat) : List Term → Bool
  | [] => false
  | t :: ts => Term.usesRef n t || Term.usesRefList n ts
def Term.usesRefRow (n : Nat) : List (Label × Term) → Bool
  | [] => false
  | (_, t) :: fs => Term.usesRef n t || Term.usesRefRow n fs
end

mutual
/-- Fill the holes: `ref n` becomes `σ n` where that is given. Fillings are closed terms, so
nothing is shifted under binders. -/
def Term.fillRefs (σ : Nat → Option Term) : Term → Term
  | .var i => .var i
  | .lam a b => .lam a (Term.fillRefs σ b)
  | .app f a => .app (Term.fillRefs σ f) (Term.fillRefs σ a)
  | .fix t => .fix (Term.fillRefs σ t)
  | .nat n => .nat n
  | .bool b => .bool b
  | .bytes s => .bytes s
  | .digest s => .digest s
  | .prim p a b => .prim p (Term.fillRefs σ a) (Term.fillRefs σ b)
  | .record fs => .record (Term.fillRefsRow σ fs)
  | .get t ℓ => .get (Term.fillRefs σ t) ℓ
  | .extend t fs => .extend (Term.fillRefs σ t) (Term.fillRefsRow σ fs)
  | .inj a ℓ t => .inj a ℓ (Term.fillRefs σ t)
  | .case t arms => .case (Term.fillRefs σ t) (Term.fillRefsRow σ arms)
  | .ite c a b => .ite (Term.fillRefs σ c) (Term.fillRefs σ a) (Term.fillRefs σ b)
  | .ref n => .ref n
  | .hole n ts =>
      let ts' := Term.fillRefsList σ ts
      match σ n with
      | none => .hole n ts'
      | some t => Term.substList ts' t
  | .refuse T w => .refuse T w
def Term.fillRefsList (σ : Nat → Option Term) : List Term → List Term
  | [] => []
  | t :: ts => Term.fillRefs σ t :: Term.fillRefsList σ ts
def Term.fillRefsRow (σ : Nat → Option Term) : List (Label × Term) → List (Label × Term)
  | [] => []
  | (ℓ, t) :: fs => (ℓ, Term.fillRefs σ t) :: Term.fillRefsRow σ fs
end

/-- The declared type of hole `n`: its first declaration's. -/
def holeTy (Ω : List (HoleDecl (List Lang.Ty) Lang.Ty)) (n : Nat) : Option Lang.Ty :=
  (Ω.find? (·.name == n)).map (·.ty)

end Nanodregg.Lang
