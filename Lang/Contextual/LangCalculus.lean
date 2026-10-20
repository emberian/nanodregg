/-
# Lang.Contextual.LangCalculus — the DEPLOYED term language as a `CalculusData` (ACTIVITIES-2)

The data half of an instance of CLOSURE's abstract calculus (`Lang.Contextual.Closure`) over
`Lang.Term`: a template's holes are its `ref`s (`ref n` is the hole named `n`; fillings are
CLOSED terms, so filling shifts nothing), a hole's local context is a `List Ty` of ordinary
variables, strengthening and weakening are variable renamings at a position (CMTT-CORE's
`lowerIdx`/`liftIdx`). The laws are `Lang.Proofs.Contextual.LangInstance.langLaws`, over
`LangHasTy`, which requires every hole's context to be EMPTY: the measurement this instance makes
is what that costs (`langHasTy_closed_holes`).

Binders: `lam` binds one variable, every `case` arm binds its payload at index 0; record and
extend fields bind nothing.
-/
import Lang.Check
import Lang.Contextual.Core
import Lang.Contextual.Closure

namespace Nanodregg.Lang.Contextual

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
  | .refuse T w => .refuse T w
/-- Fields bind nothing. -/
def Term.renameVarRow (ρ : Nat → Nat) : List (Label × Term) → List (Label × Term)
  | [] => []
  | (ℓ, t) :: fs => (ℓ, Term.renameVar ρ t) :: Term.renameVarRow ρ fs
/-- Every arm binds its payload at index 0. -/
def Term.renameVarArms (ρ : Nat → Nat) : List (Label × Term) → List (Label × Term)
  | [] => []
  | (ℓ, t) :: as => (ℓ, Term.renameVar (upR ρ) t) :: Term.renameVarArms ρ as
end

mutual
/-- Does the term use the free variable `k`? -/
def Term.usesVar (k : Nat) : Term → Bool
  | .var i => i == k
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
def Term.usesVarRow (k : Nat) : List (Label × Term) → Bool
  | [] => false
  | (_, t) :: fs => Term.usesVar k t || Term.usesVarRow k fs
def Term.usesVarArms (k : Nat) : List (Label × Term) → Bool
  | [] => false
  | (_, t) :: as => Term.usesVar (k + 1) t || Term.usesVarArms k as
end

/-! ## Holes: the `ref`s -/

mutual
/-- Does the term use the hole (`ref`) `n`? -/
def Term.usesRef (n : Nat) : Term → Bool
  | .ref i => i == n
  | .var _ | .nat _ | .bool _ | .bytes _ | .digest _ | .refuse _ _ => false
  | .lam _ b | .fix b | .get b _ | .inj _ _ b => Term.usesRef n b
  | .app f a | .prim _ f a => Term.usesRef n f || Term.usesRef n a
  | .record fs => Term.usesRefRow n fs
  | .extend t fs | .case t fs => Term.usesRef n t || Term.usesRefRow n fs
  | .ite c a b => Term.usesRef n c || Term.usesRef n a || Term.usesRef n b
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
  | .ref n => (σ n).getD (.ref n)
  | .refuse T w => .refuse T w
def Term.fillRefsRow (σ : Nat → Option Term) : List (Label × Term) → List (Label × Term)
  | [] => []
  | (ℓ, t) :: fs => (ℓ, Term.fillRefs σ t) :: Term.fillRefsRow σ fs
end

/-- The declared type of hole `n`: its first declaration's. -/
def tyOf (Ω : List (HoleDecl (List Lang.Ty) Lang.Ty)) (n : Nat) : Option Lang.Ty :=
  (Ω.find? (·.name == n)).map (·.ty)

/-- One past the largest hole name. -/
def holeBound (Ω : List (HoleDecl (List Lang.Ty) Lang.Ty)) : Nat :=
  Ω.foldr (fun d m => max (d.name + 1) m) 0

/-- The package types the holes stand at: `ref n` has hole `n`'s type. The `.nat` placeholder at
an undeclared name makes no theorem true: `LangHasTy`'s `RefsDeclared` conjunct supplies `tyOf Ω n`
for every `ref` a template uses, and a `ref` surviving `fillRefs` was used before and unfilled, never
born inside a filling (`usesRef_fillRefs` with `refsDeclared_nil` on the closed filling), so
`ΔOf_getElem?` is only ever applied at a declared name. -/
def ΔOf (Ω : List (HoleDecl (List Lang.Ty) Lang.Ty)) : List Lang.Ty :=
  (List.range (holeBound Ω)).map fun n => (tyOf Ω n).getD .nat

/-- `Lang.Term` as a `CalculusData`. -/
def langData : CalculusData where
  Ty := Lang.Ty
  Ctx := List Lang.Ty
  Tm := Term
  tmEq := Term.decEq
  msubst := Term.fillRefs
  check Ψ M A := decide (Lang.infer [] Ψ M = some A)
  uses M x := Term.usesVar x M
  drop Ψ x := Ψ.eraseIdx x
  strengthen x := Term.renameVar (lowerIdx x)
  weaken x := Term.renameVar (liftIdx x)
  var := Term.var
  lookup Ψ x := Ψ[x]?

end Nanodregg.Lang.Contextual
