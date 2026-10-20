/- Context-morphism values, not token edits: Cave–Pientka (2013), pp1–2. -/
import Lang.Contextual.Core

namespace Nanodregg.Lang.Contextual.ContextMorphisms

/-- First-class substitution data scoped by domain and codomain; Valid lives in Proofs
(Cave–Pientka p1). Phantom indices alone are not typing evidence. -/
structure Morphism (source target : Ctx) where
  term : Nat → Tm

/-- Identity context morphism (Cave–Pientka p2, substitution equations). -/
def identity (Γ : Ctx) : Morphism Γ Γ := ⟨Tm.var⟩

/-- Apply a first-class context morphism, using the landed capture-avoiding substitution
(Cave–Pientka pp1–2). -/
def apply {Γ Ψ : Ctx} (s : Morphism Γ Ψ) (t : Tm) : Tm := substFn s.term t

/-- Compose scoped substitutions; token withdrawal has no constructor here
(Cave–Pientka pp1–2). -/
def compose {Γ Ψ Φ : Ctx} (s : Morphism Γ Ψ) (t : Morphism Ψ Φ) : Morphism Γ Φ :=
  ⟨fun i => apply t (s.term i)⟩

/-- Weakening is a morphism into the extended context (Cave–Pientka p1). -/
def weakening (Γ : Ctx) (A : Ty) : Morphism Γ (A :: Γ) := ⟨fun i => .var (i + 1)⟩

/-- Exchange the first two variables (Cave–Pientka p1). -/
def exchange (Γ : Ctx) (A B : Ty) : Morphism (A :: B :: Γ) (B :: A :: Γ) :=
  ⟨fun | 0 => .var 1 | 1 => .var 0 | i + 2 => .var (i + 2)⟩

/-- Strengthening offers the lower-context term only if the removed variable is unused.
This is a partial inverse of weakening, not a total map of the removed variable
(Cave–Pientka p1; landed CMTT strengthening). -/
def strengthen (x : Nat) (t : Tm) : Option Tm :=
  if uses x t then none else some (unshiftAt x t)

end Nanodregg.Lang.Contextual.ContextMorphisms
