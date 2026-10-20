import Lang.Contextual.ModalBoundary
import Lang.Proofs.Contextual.Boundary
import Lang.Proofs.Contextual.Core

namespace Nanodregg.Lang.Contextual.ModalBoundary

/-- Scoped indices really refer to their carried type (Moebius p2). -/
theorem Var.lookup {Γ : Ctx} {A : Ty} (v : Var Γ A) : Γ[v.index]? = some A := by
  induction v with
  | here => rfl
  | there v ih => exact ih

/-- Every typed pattern input has a derivation in the landed CMTT calculus
(Moebius pp1–2). -/
theorem Code.typed {Γ : Ctx} {A : Ty} (c : Code Γ A) :
    HasTy MEnv.nil Γ c.erase A := by
  induction c with
  | var v => exact .var v.lookup
  | lam A body ih => exact .lam ih
  | app f a ihf iha => exact .app ihf iha

/-- The raw extension used by Boundary agrees with typed pattern evaluation
(Moebius pp1–2). -/
theorem Guard.raw_erase {Γ : Ctx} {A : Ty} (g : Guard Γ A) (c : Code Γ A) :
    g.raw c.erase = g.run c := by
  cases g <;> cases c <;> rfl

/-- Typed syntax patterns feed the actual existing candidate judge, not only a detached
Boolean demonstration (Moebius p2). -/
theorem typed_guard_judge {V : Type} {Γ : Ctx} {A : Ty}
    (g : Guard Γ A) (behavior : Tm → V) (c : Code Γ A) :
    judge (boundary Γ A g behavior).iface world (candidate c) = .verified ↔
      g.run c = true := by
  rw [judge_verified_iff]
  have hc : cmttData.check Γ c.erase A = true := check_complete c.typed
  simp [boundary, candidate, hc, effSupports, Guard.raw_erase]

/-- Extensional consumers of a boundary's preserved behavior retain their observation
(Kavvos p1). This is the extensional side of the same split as the syntax counterexample. -/
theorem extensional_locality {D : CalculusData} {E V R : Type}
    (b : Boundary D E V) {w w' : World E} {c c' : Candidate D}
    (h : b.behavior w.env c.filling = b.behavior w'.env c'.filling) (consumer : V → R) :
    consumer (b.behavior w.env c.filling) = consumer (b.behavior w'.env c'.filling) :=
  congrArg consumer h

/-- Equal boundary observations do not license syntax-guard reuse. Exactly the logical
contract reopens; typing, beta observation and cost stay preserved (Kavvos p1; Moebius p2). -/
theorem intensional_boundary_breaks :
    (boundary [.base] .base .isApplication betaObservation).failures
      world world (candidate redex) (candidate reduced) = [.logicalContract] := by decide

/-- This is a real typed beta step, not two arbitrarily equated values (Moebius p2). -/
theorem typed_beta_witness :
    HasTy MEnv.nil [.base] redex.erase .base ∧
    HasTy MEnv.nil [.base] reduced.erase .base ∧ Step redex.erase reduced.erase := by
  exact ⟨redex.typed, reduced.typed, .beta⟩

/-- The same repair is admitted by the application pattern before reduction and refused
after it; typed syntax inspection is intentionally intensional (Kavvos p1; Moebius p2). -/
theorem intensional_judge_breaks :
    judge (boundary [.base] .base .isApplication betaObservation).iface world
      (candidate redex) = .verified ∧
    judge (boundary [.base] .base .isApplication betaObservation).iface world
      (candidate reduced) = .conflict .guardFails := by decide

end Nanodregg.Lang.Contextual.ModalBoundary
