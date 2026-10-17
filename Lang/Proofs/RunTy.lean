/-
# Lang.Proofs.RunTy — typing of the machine's runtime: values, environments, suspended fields,
the stack and the state

A value is typed by how it was made: a closure by its body's typing under its environment, a knot
by its body at `R → R`, a record by its suspended fields. `StateTy Δ s T` says `s` is a machine
state that, run to the end, produces a `T`. `LibTy Δ lib` says the closure's package bodies have
the types `ref` gives them. These are the invariants of `Lang.Proofs.Sound`; nothing deployed
runs them.
-/
import Lang.Eval
import Lang.Proofs.Typing

namespace Nanodregg.Lang

mutual
inductive ValTy (Δ : List Ty) : Val → Ty → Prop
  | nat {n : Nat} : n < Bounds.natLimit → ValTy Δ (.nat n) .nat
  | bool {b : Bool} : ValTy Δ (.bool b) .bool
  | bytes {s : ByteArray} : s.size ≤ Bounds.bytesMax → ValTy Δ (.bytes s) .bytes
  | digest {s : ByteArray} : s.size ≤ Bounds.digestBytesMax → ValTy Δ (.digest s) .digest
  | clo {b env Γ A B} : EnvTy Δ env Γ → HasType Δ (A :: Γ) b B → ValTy Δ (.clo b env) (.fn A B)
  | knot {b env Γ r} : EnvTy Δ env Γ → HasType Δ (.record r :: Γ) b (.record r) →
      ValTy Δ (.knot b env) (.record r)
  | record {fs r} : ThunksTy Δ fs r → ValTy Δ (.record fs) (.record r)
  | inj {r ℓ A v} : Row.find? ℓ r = some A → ValTy Δ v A → ValTy Δ (.inj ℓ v) (.sum r)

inductive EnvTy (Δ : List Ty) : List Val → List Ty → Prop
  | nil : EnvTy Δ [] []
  | cons {v vs T Ts} : ValTy Δ v T → EnvTy Δ vs Ts → EnvTy Δ (v :: vs) (T :: Ts)

/-- Suspended fields and their row: each field's term types under its own environment. -/
inductive ThunksTy (Δ : List Ty) : List (Label × (Term × List Val)) → List (Label × Ty) → Prop
  | nil : ThunksTy Δ [] []
  | cons {ℓ t env Γ T fs r} : EnvTy Δ env Γ → HasType Δ Γ t T → ThunksTy Δ fs r →
      ThunksTy Δ ((ℓ, (t, env)) :: fs) ((ℓ, T) :: r)
end

/-- One suspended field at a type. -/
inductive ThunkTy (Δ : List Ty) : Term × List Val → Ty → Prop
  | mk {t env Γ T} : EnvTy Δ env Γ → HasType Δ Γ t T → ThunkTy Δ (t, env) T

/-- `StackTy Δ k A T`: the stack `k` takes a value of type `A` to a final value of type `T`. -/
inductive StackTy (Δ : List Ty) : List Frame → Ty → Ty → Prop
  | nil {T} : StackTy Δ [] T T
  | appL {a env Γ A B k T} : EnvTy Δ env Γ → HasType Δ Γ a A → StackTy Δ k B T →
      StackTy Δ (.appL a env :: k) (.fn A B) T
  | appR {f A B k T} : ValTy Δ f (.fn A B) → StackTy Δ k B T → StackTy Δ (.appR f :: k) A T
  | fix {r k T} : StackTy Δ k (.record r) T →
      StackTy Δ (.fix :: k) (.fn (.record r) (.record r)) T
  | primL {p b env Γ k T} : EnvTy Δ env Γ → HasType Δ Γ b p.right → StackTy Δ k p.result T →
      StackTy Δ (.primL p b env :: k) p.left T
  | primR {p a k T} : ValTy Δ a p.left → StackTy Δ k p.result T →
      StackTy Δ (.primR p a :: k) p.right T
  | get {ℓ r A k T} : Row.find? ℓ r = some A → StackTy Δ k A T →
      StackTy Δ (.get ℓ :: k) (.record r) T
  | extend {fs env Γ r r2 k T} : EnvTy Δ env Γ → FieldsTy Δ Γ fs r2 →
      StackTy Δ k (.record (Row.merge r r2)) T → StackTy Δ (.extend fs env :: k) (.record r) T
  | inj {ℓ r A k T} : Row.find? ℓ r = some A → StackTy Δ k (.sum r) T →
      StackTy Δ (.inj ℓ :: k) A T
  | case {arms env Γ r B k T} : EnvTy Δ env Γ → ArmsTy Δ Γ arms r B → StackTy Δ k B T →
      StackTy Δ (.case arms env :: k) (.sum r) T
  | ite {a b env Γ B k T} : EnvTy Δ env Γ → HasType Δ Γ a B → HasType Δ Γ b B →
      StackTy Δ k B T → StackTy Δ (.ite a b env :: k) .bool T

/-- A machine state that, run to the end, produces a `T`. -/
inductive StateTy (Δ : List Ty) : State → Ty → Prop
  | eval {t env Γ A k d T} : EnvTy Δ env Γ → HasType Δ Γ t A → StackTy Δ k A T →
      StateTy Δ ⟨.eval t env, k, d⟩ T
  | ret {v A k d T} : ValTy Δ v A → StackTy Δ k A T → StateTy Δ ⟨.ret v, k, d⟩ T

/-- The closure's bodies have the types `ref` gives them, each closed. -/
def LibTy (Δ : List Ty) (lib : List Term) : Prop :=
  ∀ (i : Nat) (T : Ty), Δ[i]? = some T → ∃ t, lib[i]? = some t ∧ HasType Δ [] t T

/-- What one step of a typed state may do: continue typed, halt with a typed value, or fault by a
name that is not `stuck`. -/
inductive StepOK (Δ : List Ty) (T : Ty) : Step → Prop
  | next {s} : StateTy Δ s T → StepOK Δ T (.next s)
  | halt {v} : ValTy Δ v T → StepOK Δ T (.halt v)
  | fault {f} : f ≠ .stuck → StepOK Δ T (.fault f)

/-- The depth counter is the stack's length. -/
def DepthOK (s : State) : Prop := s.depth = s.stack.length

end Nanodregg.Lang
