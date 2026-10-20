/- Typed syntax-reading guards and extensional boundaries: Kavvos (2020) p1;
Jang et al., Moebius (2021), pp1–2. Simply-typed contextual fragment only. -/
import Lang.Contextual.Boundary
import Lang.Contextual.CoreCalculus

namespace Nanodregg.Lang.Contextual.ModalBoundary

/-- Intrinsically scoped variables (Moebius p2, contextual code). -/
inductive Var : Ctx → Ty → Type where
  | here {Γ : Ctx} {A : Ty} : Var (A :: Γ) A
  | there {Γ : Ctx} {A B : Ty} : Var Γ A → Var (B :: Γ) A

/-- Contextual code carries its context and result type. This STLC fragment supports
typed syntax analysis, not the full polymorphic Moebius calculus (Moebius pp1–2). -/
inductive Code : Ctx → Ty → Type where
  | var {Γ : Ctx} {A : Ty} : Var Γ A → Code Γ A
  | lam {Γ : Ctx} (A : Ty) {B : Ty} : Code (A :: Γ) B → Code Γ (.arr A B)
  | app {Γ : Ctx} {A B : Ty} : Code Γ (.arr A B) → Code Γ A → Code Γ B

/-- Scoped variables erase to the existing CMTT indices (Moebius p2). -/
def Var.index {Γ : Ctx} {A : Ty} : Var Γ A → Nat
  | .here => 0
  | .there v => v.index + 1

/-- Typed code erases to the LANDED term language, not a new operational semantics
(Moebius p2). -/
def Code.erase {Γ : Ctx} {A : Ty} : Code Γ A → Tm
  | .var v => .var v.index
  | .lam A body => .lam A body.erase
  | .app f a => .app f.erase a.erase

/-- Syntax-reading guards are typed patterns; lambda inspection requires an arrow
contextual type (Moebius pp1–2). -/
inductive Guard (Γ : Ctx) : Ty → Type where
  | isVariable {A : Ty} : Guard Γ A
  | isApplication {A : Ty} : Guard Γ A
  | isLambda {A B : Ty} : Guard Γ (.arr A B)

/-- Evaluate the pattern on well-scoped code (Moebius pp1–2). -/
def Guard.run {Γ : Ctx} {A : Ty} (g : Guard Γ A) (c : Code Γ A) : Bool :=
  match g, c with
  | .isVariable, .var _ => true
  | .isApplication, .app _ _ => true
  | .isLambda, .lam _ _ => true
  | _, _ => false

/-- The raw extension is consumed ONLY through the existing typed candidate judge;
raw_erase proves agreement on code (Moebius pp1–2). -/
def Guard.raw {Γ : Ctx} {A : Ty} (g : Guard Γ A) (t : Tm) : Bool :=
  match g, t with
  | .isVariable, .var _ => true
  | .isApplication, .app _ _ => true
  | .isLambda, .lam _ _ => true
  | _, _ => false

/-- Install a typed syntax pattern at an existing CMTT boundary; the original checker,
support checks and budget still apply (Kavvos p1; Moebius p2). -/
def boundary {V : Type} (Γ : Ctx) (A : Ty) (g : Guard Γ A)
    (behavior : Tm → V) : Boundary cmttData Unit V where
  iface := {
    name := 0, ctx := Γ, ty := A, hyps := [], hyps_real := by simp,
    guard := fun _ t => g.raw t, budget := 1, chooser := 1, acceptor := 2 }
  declares := Declaration.top
  behavior := fun _ t => behavior t
  costBound := 1

/-- Candidate construction consumes typed contextual code (Moebius p2). -/
def candidate {Γ : Ctx} {A : Ty} (c : Code Γ A) : Candidate cmttData :=
  ⟨c.erase, [], [], 1, 1, .verified⟩

/-- One explicit beta contraction as a boundary observation; no normalization claim
(Kavvos p1, values versus descriptions). -/
def betaObservation : Tm → Tm
  | .app (.lam _ body) arg => subst [arg] body
  | t => t

/-- A typed contextual beta redex (Moebius p2). -/
def redex : Code [.base] .base := .app (.lam .base (.var .here)) (.var .here)

/-- The redex's contextual result (Moebius p2). -/
def reduced : Code [.base] .base := .var .here

/-- A world without token prerequisites for the boundary demonstration (Kavvos p1). -/
def world : World Unit := ⟨fun _ => false, ()⟩

end Nanodregg.Lang.Contextual.ModalBoundary
