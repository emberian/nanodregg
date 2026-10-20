/-
# Lang.Contextual.Core — contextual modal type theory, simply typed (lane CMTT-CORE)

The simply-typed fragment of Nanevski–Pfenning–Pientka, *Contextual Modal Type Theory* (TOCL
2008), with explicit simultaneous substitutions, de Bruijn indices for both kinds of variable.

* `Ty`: `base`, `arr A B`, and the contextual type `box Ψ A` (`[Ψ ⊢ A]`).
* `Ctx := List Ty` (ordinary variables; index 0 is the most recent binding) and the modal
  environment `MEnv := Nat → Option (Ctx × Ty)` (`Δ u = some (Ψ, A)` declares `u :: (Ψ ⊢ A)`;
  index 0 is the most recent `letbox`; the free metavariables of a template — its holes — are
  the indices past the bound ones, so a hole's NAME is its index at depth 0).
* `Tm`: `var i`, `lam A t`, `app t s`, `box Ψ t` (closes `t` over `Ψ`: `t`'s ordinary variables
  are `Ψ`'s and nothing else), `letbox t s` (binds one metavariable in `s`), and `mvar u σ`, the
  occurrence `u[σ]` carrying a simultaneous substitution `σ` for `u`'s local context.

Ordinary substitution is defined once over functions (`substFn f`, the instantiation of every
variable `i` by `f i`); a list `σ` denotes the function `ofList σ`, which is `σ` on its first
`σ.length` indices and the identity shifted down by `σ.length` after them (so `subst [s] t` is
β's `t[s/0]`, and `comp τ σ = σ.map (subst τ) ++ τ` is the composition exactly). `box` is opaque
to ordinary substitution and renaming: its body has no ordinary free variable of the ambient
context to rename. Metavariable renaming `mren` and metavariable substitution `msubst` go
inside `box`.

The judgments (`HasTy`, `HasSubst`, `Step`) are statements, so they live in the proof module
`Lang.Proofs.Contextual.Typing` (gate C3); this module is data only.
-/

namespace Nanodregg.Lang.Contextual

/-- Simple types with the contextual box `[Ψ ⊢ A]`. -/
inductive Ty
  | base
  | arr (dom cod : Ty)
  | box (ctx : List Ty) (ty : Ty)
  deriving Repr

/-- Ordinary contexts: index 0 is the most recently bound variable. -/
abbrev Ctx := List Ty

/-- Modal environments: `Δ u = some (Ψ, A)` is the declaration `u :: (Ψ ⊢ A)`. A function rather
than a list, so a PARTIAL metavariable substitution (`msubstP`) removes the filled declarations
and leaves every other one at its index: a list has no gaps. -/
abbrev MEnv := Nat → Option (Ctx × Ty)

/-- The empty modal environment. -/
def MEnv.nil : MEnv := fun _ => none

/-- Bind one more metavariable, at index 0 (what `letbox` does). -/
def MEnv.cons (P : Ctx × Ty) (Δ : MEnv) : MEnv
  | 0 => some P
  | v + 1 => Δ v

/-- Declare `P` at index `k`, moving the declarations at `k` and above up by one. -/
def MEnv.insert (k : Nat) (P : Ctx × Ty) (Δ : MEnv) : MEnv := fun v =>
  if v < k then Δ v else if v = k then some P else Δ (v - 1)

inductive Tm
  | var (i : Nat)
  | lam (dom : Ty) (body : Tm)
  | app (fn arg : Tm)
  /-- `box Ψ t`: the body is typed under `Ψ` alone. -/
  | box (ctx : Ctx) (body : Tm)
  /-- `letbox t s`: `t : [Ψ ⊢ A]`, and `s` sees one more metavariable, at index 0. -/
  | letbox (scrut body : Tm)
  /-- `mvar u σ`: the occurrence `u[σ]`, `σ` a substitution for `u`'s local context. -/
  | mvar (u : Nat) (σ : List Tm)
  deriving Repr

/-! ## Renaming of ordinary variables -/

/-- A renaming under one more ordinary binder. -/
def upR (ρ : Nat → Nat) : Nat → Nat
  | 0 => 0
  | i + 1 => ρ i + 1

mutual
/-- Rename the ordinary free variables of a term (not inside `box`: a box body is closed over the
ambient context). -/
def rename (ρ : Nat → Nat) : Tm → Tm
  | .var i => .var (ρ i)
  | .lam A t => .lam A (rename (upR ρ) t)
  | .app t s => .app (rename ρ t) (rename ρ s)
  | .box Ψ t => .box Ψ t
  | .letbox t s => .letbox (rename ρ t) (rename ρ s)
  | .mvar u σ => .mvar u (renameL ρ σ)
def renameL (ρ : Nat → Nat) : List Tm → List Tm
  | [] => []
  | t :: σ => rename ρ t :: renameL ρ σ
end

/-! ## Renaming of metavariables -/

mutual
/-- Rename the metavariables of a term (everywhere, `box` bodies included). -/
def mren (ρ : Nat → Nat) : Tm → Tm
  | .var i => .var i
  | .lam A t => .lam A (mren ρ t)
  | .app t s => .app (mren ρ t) (mren ρ s)
  | .box Ψ t => .box Ψ (mren ρ t)
  | .letbox t s => .letbox (mren ρ t) (mren (upR ρ) s)
  | .mvar u σ => .mvar (ρ u) (mrenL ρ σ)
def mrenL (ρ : Nat → Nat) : List Tm → List Tm
  | [] => []
  | t :: σ => mren ρ t :: mrenL ρ σ
end

/-- Modal weakening by one: every metavariable index moves up by one. -/
def mshift (t : Tm) : Tm := mren Nat.succ t

/-! ## Simultaneous substitution of ordinary variables -/

/-- A substitution under one more ordinary binder. -/
def upS (f : Nat → Tm) : Nat → Tm
  | 0 => .var 0
  | i + 1 => rename Nat.succ (f i)

/-- A substitution under one more metavariable binder (`letbox`). -/
def mshiftS (f : Nat → Tm) : Nat → Tm := fun i => mshift (f i)

mutual
/-- Instantiate every ordinary variable `i` by `f i`. -/
def substFn (f : Nat → Tm) : Tm → Tm
  | .var i => f i
  | .lam A t => .lam A (substFn (upS f) t)
  | .app t s => .app (substFn f t) (substFn f s)
  | .box Ψ t => .box Ψ t
  | .letbox t s => .letbox (substFn f t) (substFn (mshiftS f) s)
  | .mvar u σ => .mvar u (substFnL f σ)
def substFnL (f : Nat → Tm) : List Tm → List Tm
  | [] => []
  | t :: σ => substFn f t :: substFnL f σ
end

/-- The function a list substitution denotes: `σ` on its first `σ.length` indices, then the
identity shifted down by `σ.length`. -/
def ofList : List Tm → Nat → Tm
  | [], i => .var i
  | t :: _, 0 => t
  | _ :: σ, i + 1 => ofList σ i

/-- Simultaneous substitution by a list. -/
def subst (σ : List Tm) (t : Tm) : Tm := substFn (ofList σ) t

/-- Composition: `subst (comp τ σ) = subst τ ∘ subst σ` (`Lang.Proofs.Contextual.Core.subst_comp`). -/
def comp (τ σ : List Tm) : List Tm := σ.map (subst τ) ++ τ

/-- `[var k, var (k+1), …, var (k+n-1)]`. -/
def shiftSub (k : Nat) : Nat → List Tm
  | 0 => []
  | n + 1 => .var k :: shiftSub (k + 1) n

/-- The identity substitution for a context of length `n`. -/
def idSub (n : Nat) : List Tm := shiftSub 0 n

/-- The projection (weakening) substitution `Γ', A ⊢ π : Γ'` for `Γ'` of length `n`. -/
def proj (n : Nat) : List Tm := shiftSub 1 n

/-! ## Metavariable substitution -/

mutual
/-- `msubst s u t`: replace every occurrence `mvar u σ` of `t` by `subst σ' s` (`σ'` the
substituted `σ`), and rename every later metavariable down by one. `s` is typed under the local
context `Ψ` of `u`, so it has no ordinary free variable the ambient context could capture; under a
`letbox` it is modally weakened. -/
def msubst (s : Tm) (u : Nat) : Tm → Tm
  | .var i => .var i
  | .lam A t => .lam A (msubst s u t)
  | .app t₁ t₂ => .app (msubst s u t₁) (msubst s u t₂)
  | .box Ψ t => .box Ψ (msubst s u t)
  | .letbox t₁ t₂ => .letbox (msubst s u t₁) (msubst (mshift s) (u + 1) t₂)
  | .mvar v σ =>
    if v = u then subst (msubstL s u σ) s
    else if v < u then .mvar v (msubstL s u σ)
    else .mvar (v - 1) (msubstL s u σ)
def msubstL (s : Tm) (u : Nat) : List Tm → List Tm
  | [] => []
  | t :: σ => msubst s u t :: msubstL s u σ
end

/-! ## Variable occurrence and blocked heads -/

mutual
/-- Does `t` use the ordinary variable `k` (free)? A `box` body uses none of the ambient ones. -/
def uses (k : Nat) : Tm → Bool
  | .var i => i == k
  | .lam _ t => uses (k + 1) t
  | .app t s => uses k t || uses k s
  | .box _ _ => false
  | .letbox t s => uses k t || uses k s
  | .mvar _ σ => usesL k σ
def usesL (k : Nat) : List Tm → Bool
  | [] => false
  | t :: σ => uses k t || usesL k σ
end

/-- Is the head of `t` known? False exactly on a metavariable occurrence: inspection of the
term is blocked there until a metavariable substitution arrives (Hu–Pientka, Layered MTT, ESOP
2024 §5.2). -/
def headKnown : Tm → Bool
  | .mvar _ _ => false
  | _ => true

/-! ## Decidable equality, by hand (no `deriving` for nested inductives in v4.30.0)

Structural recursion over the nested inductives, every verdict carrying its proof term; there is
no separate Boolean equality to relate. -/

mutual
/-- Decide equality of types. -/
def Ty.decEq : (a b : Ty) → Decidable (a = b)
  | .base, .base => isTrue rfl
  | .arr a₁ a₂, .arr b₁ b₂ =>
    match Ty.decEq a₁ b₁, Ty.decEq a₂ b₂ with
    | isTrue h₁, isTrue h₂ => isTrue (by subst h₁; subst h₂; rfl)
    | isFalse h, _ => isFalse (by intro e; injection e with e₁ e₂; exact h e₁)
    | _, isFalse h => isFalse (by intro e; injection e with e₁ e₂; exact h e₂)
  | .box Ψ a, .box Φ b =>
    match Ty.decEqL Ψ Φ, Ty.decEq a b with
    | isTrue h₁, isTrue h₂ => isTrue (by subst h₁; subst h₂; rfl)
    | isFalse h, _ => isFalse (by intro e; injection e with e₁ e₂; exact h e₁)
    | _, isFalse h => isFalse (by intro e; injection e with e₁ e₂; exact h e₂)
  | .base, .arr _ _ => isFalse (by intro e; cases e)
  | .base, .box _ _ => isFalse (by intro e; cases e)
  | .arr _ _, .base => isFalse (by intro e; cases e)
  | .arr _ _, .box _ _ => isFalse (by intro e; cases e)
  | .box _ _, .base => isFalse (by intro e; cases e)
  | .box _ _, .arr _ _ => isFalse (by intro e; cases e)
/-- Decide equality of type lists. -/
def Ty.decEqL : (as bs : List Ty) → Decidable (as = bs)
  | [], [] => isTrue rfl
  | a :: as, b :: bs =>
    match Ty.decEq a b, Ty.decEqL as bs with
    | isTrue h₁, isTrue h₂ => isTrue (by subst h₁; subst h₂; rfl)
    | isFalse h, _ => isFalse (by intro e; injection e with e₁ e₂; exact h e₁)
    | _, isFalse h => isFalse (by intro e; injection e with e₁ e₂; exact h e₂)
  | [], _ :: _ => isFalse (by intro e; cases e)
  | _ :: _, [] => isFalse (by intro e; cases e)
end

instance Ty.instDecEq : DecidableEq Ty := Ty.decEq

mutual
/-- Decide equality of terms. -/
def Tm.decEq : (a b : Tm) → Decidable (a = b)
  | .var i, .var j =>
    if h : i = j then isTrue (by subst h; rfl)
    else isFalse (by intro e; injection e with e₁; exact h e₁)
  | .lam A t, .lam B s =>
    match Ty.decEq A B, Tm.decEq t s with
    | isTrue h₁, isTrue h₂ => isTrue (by subst h₁; subst h₂; rfl)
    | isFalse h, _ => isFalse (by intro e; injection e with e₁ e₂; exact h e₁)
    | _, isFalse h => isFalse (by intro e; injection e with e₁ e₂; exact h e₂)
  | .app t₁ t₂, .app s₁ s₂ =>
    match Tm.decEq t₁ s₁, Tm.decEq t₂ s₂ with
    | isTrue h₁, isTrue h₂ => isTrue (by subst h₁; subst h₂; rfl)
    | isFalse h, _ => isFalse (by intro e; injection e with e₁ e₂; exact h e₁)
    | _, isFalse h => isFalse (by intro e; injection e with e₁ e₂; exact h e₂)
  | .box Ψ t, .box Φ s =>
    match Ty.decEqL Ψ Φ, Tm.decEq t s with
    | isTrue h₁, isTrue h₂ => isTrue (by subst h₁; subst h₂; rfl)
    | isFalse h, _ => isFalse (by intro e; injection e with e₁ e₂; exact h e₁)
    | _, isFalse h => isFalse (by intro e; injection e with e₁ e₂; exact h e₂)
  | .letbox t₁ t₂, .letbox s₁ s₂ =>
    match Tm.decEq t₁ s₁, Tm.decEq t₂ s₂ with
    | isTrue h₁, isTrue h₂ => isTrue (by subst h₁; subst h₂; rfl)
    | isFalse h, _ => isFalse (by intro e; injection e with e₁ e₂; exact h e₁)
    | _, isFalse h => isFalse (by intro e; injection e with e₁ e₂; exact h e₂)
  | .mvar u σ, .mvar v τ =>
    if h : u = v then
      match Tm.decEqL σ τ with
      | isTrue h₂ => isTrue (by subst h; subst h₂; rfl)
      | isFalse h₂ => isFalse (by intro e; injection e with e₁ e₂; exact h₂ e₂)
    else isFalse (by intro e; injection e with e₁ e₂; exact h e₁)
  | .var _, .lam _ _ => isFalse (by intro e; cases e)
  | .var _, .app _ _ => isFalse (by intro e; cases e)
  | .var _, .box _ _ => isFalse (by intro e; cases e)
  | .var _, .letbox _ _ => isFalse (by intro e; cases e)
  | .var _, .mvar _ _ => isFalse (by intro e; cases e)
  | .lam _ _, .var _ => isFalse (by intro e; cases e)
  | .lam _ _, .app _ _ => isFalse (by intro e; cases e)
  | .lam _ _, .box _ _ => isFalse (by intro e; cases e)
  | .lam _ _, .letbox _ _ => isFalse (by intro e; cases e)
  | .lam _ _, .mvar _ _ => isFalse (by intro e; cases e)
  | .app _ _, .var _ => isFalse (by intro e; cases e)
  | .app _ _, .lam _ _ => isFalse (by intro e; cases e)
  | .app _ _, .box _ _ => isFalse (by intro e; cases e)
  | .app _ _, .letbox _ _ => isFalse (by intro e; cases e)
  | .app _ _, .mvar _ _ => isFalse (by intro e; cases e)
  | .box _ _, .var _ => isFalse (by intro e; cases e)
  | .box _ _, .lam _ _ => isFalse (by intro e; cases e)
  | .box _ _, .app _ _ => isFalse (by intro e; cases e)
  | .box _ _, .letbox _ _ => isFalse (by intro e; cases e)
  | .box _ _, .mvar _ _ => isFalse (by intro e; cases e)
  | .letbox _ _, .var _ => isFalse (by intro e; cases e)
  | .letbox _ _, .lam _ _ => isFalse (by intro e; cases e)
  | .letbox _ _, .app _ _ => isFalse (by intro e; cases e)
  | .letbox _ _, .box _ _ => isFalse (by intro e; cases e)
  | .letbox _ _, .mvar _ _ => isFalse (by intro e; cases e)
  | .mvar _ _, .var _ => isFalse (by intro e; cases e)
  | .mvar _ _, .lam _ _ => isFalse (by intro e; cases e)
  | .mvar _ _, .app _ _ => isFalse (by intro e; cases e)
  | .mvar _ _, .box _ _ => isFalse (by intro e; cases e)
  | .mvar _ _, .letbox _ _ => isFalse (by intro e; cases e)
/-- Decide equality of term lists. -/
def Tm.decEqL : (as bs : List Tm) → Decidable (as = bs)
  | [], [] => isTrue rfl
  | a :: as, b :: bs =>
    match Tm.decEq a b, Tm.decEqL as bs with
    | isTrue h₁, isTrue h₂ => isTrue (by subst h₁; subst h₂; rfl)
    | isFalse h, _ => isFalse (by intro e; injection e with e₁ e₂; exact h e₁)
    | _, isFalse h => isFalse (by intro e; injection e with e₁ e₂; exact h e₂)
  | [], _ :: _ => isFalse (by intro e; cases e)
  | _ :: _, [] => isFalse (by intro e; cases e)
end

instance Tm.instDecEq : DecidableEq Tm := Tm.decEq

/-! ## The type checker -/

mutual
/-- Type inference, total and structural. A `box Ψ t` is checked under `Ψ` with the SAME `Δ` and
the ambient `Γ` dropped; `mvar u σ` checks `σ` pointwise against `u`'s declared context. -/
def infer (Δ : MEnv) (Γ : Ctx) : Tm → Option Ty
  | .var i => Γ[i]?
  | .lam A t => (infer Δ (A :: Γ) t).map (.arr A)
  | .app t s =>
    match infer Δ Γ t, infer Δ Γ s with
    | some (.arr A B), some A' => if A = A' then some B else none
    | _, _ => none
  | .box Ψ t => (infer Δ Ψ t).map (.box Ψ)
  | .letbox t s =>
    match infer Δ Γ t with
    | some (.box Ψ A) => infer (MEnv.cons (Ψ, A) Δ) Γ s
    | _ => none
  | .mvar u σ =>
    match Δ u, inferL Δ Γ σ with
    | some (Ψ, A), some Ψ' => if Ψ' = Ψ then some A else none
    | _, _ => none
/-- The types of a list of terms, pointwise. -/
def inferL (Δ : MEnv) (Γ : Ctx) : List Tm → Option (List Ty)
  | [] => some []
  | t :: σ =>
    match infer Δ Γ t, inferL Δ Γ σ with
    | some A, some As => some (A :: As)
    | _, _ => none
end

/-- The checker: `t : A` under `Γ` in the empty modal environment. -/
def check (Γ : Ctx) (t : Tm) (A : Ty) : Bool :=
  match infer MEnv.nil Γ t with
  | some B => decide (B = A)
  | none => false

/-! ## Strengthening at any position -/

/-- The index map of weakening at `x`: indices from `x` up move up by one. -/
def liftIdx (x i : Nat) : Nat := if i < x then i else i + 1

/-- Its inverse away from `x`: indices above `x` move down by one. -/
def lowerIdx (x i : Nat) : Nat := if i < x then i else i - 1

/-- Weakening at `x` (the projection `π` that forgets hypothesis `x`), as a term map. -/
def shiftAt (x : Nat) (t : Tm) : Tm := rename (liftIdx x) t

/-- Strengthening at `x`: meaningful when `uses x t = false`, where `shiftAt x (unshiftAt x t) = t`
(`Lang.Proofs.Contextual.Core.shiftAt_unshiftAt`). -/
def unshiftAt (x : Nat) (t : Tm) : Tm := rename (lowerIdx x) t

/-! ## Partial simultaneous metavariable substitution (hole filling) -/

mutual
/-- `msubstP θ d t`: at binder depth `d`, every occurrence of the FREE metavariable `n` (index
`n + d`) with `θ n = some M` becomes `[σ'](M shifted past the d bound ones)`; unfilled holes keep
their index. This is the hole filling of a template; `msubst` is CMTT's single substitution that
also removes the bound declaration. -/
def msubstP (θ : Nat → Option Tm) (d : Nat) : Tm → Tm
  | .var i => .var i
  | .lam A t => .lam A (msubstP θ d t)
  | .app t s => .app (msubstP θ d t) (msubstP θ d s)
  | .box Ψ t => .box Ψ (msubstP θ d t)
  | .letbox t s => .letbox (msubstP θ d t) (msubstP θ (d + 1) s)
  | .mvar v σ =>
    if d ≤ v then
      match θ (v - d) with
      | some M => subst (msubstPL θ d σ) (mren (· + d) M)
      | none => .mvar v (msubstPL θ d σ)
    else .mvar v (msubstPL θ d σ)
def msubstPL (θ : Nat → Option Tm) (d : Nat) : List Tm → List Tm
  | [] => []
  | t :: σ => msubstP θ d t :: msubstPL θ d σ
end

end Nanodregg.Lang.Contextual
