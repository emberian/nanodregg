/-
# Lang.Proofs.Typing — the typing relation, the specification `Lang.infer` decides

`HasType (Ω := Ω) Δ Γ t T`: under the closure's package types `Δ` and local types `Γ`, `t` has type `T`.
One rule per constructor, read off the language's meaning; `Lang.Proofs.Check` proves `infer`
returns exactly the `T` this relation allows. Nothing deployed runs this relation.
-/
import Lang.Check

namespace Nanodregg.Lang

mutual
inductive HasType (Δ : List Ty) : List Ty → Term → Ty → (Ω : optParam HoleSignature []) → Prop
  | var {Ω Γ i T} : Γ[i]? = some T → HasType (Ω := Ω) Δ Γ (.var i) T
  | lam {Ω Γ A b B} : A.wf = true → HasType (Ω := Ω) Δ (A :: Γ) b B → HasType (Ω := Ω) Δ Γ (.lam A b) (.fn A B)
  | app {Ω Γ f a A B} : HasType (Ω := Ω) Δ Γ f (.fn A B) → HasType (Ω := Ω) Δ Γ a A → HasType (Ω := Ω) Δ Γ (.app f a) B
  | fix {Ω Γ t r} : HasType (Ω := Ω) Δ Γ t (.fn (.record r) (.record r)) → HasType (Ω := Ω) Δ Γ (.fix t) (.record r)
  | nat {Ω Γ n} : n < Bounds.natLimit → HasType (Ω := Ω) Δ Γ (.nat n) .nat
  | bool {Ω Γ b} : HasType (Ω := Ω) Δ Γ (.bool b) .bool
  | bytes {Ω Γ s} : s.size ≤ Bounds.bytesMax → HasType (Ω := Ω) Δ Γ (.bytes s) .bytes
  | digest {Ω Γ s} : s.size ≤ Bounds.digestBytesMax → HasType (Ω := Ω) Δ Γ (.digest s) .digest
  | prim {Ω Γ p a b} : HasType (Ω := Ω) Δ Γ a p.left → HasType (Ω := Ω) Δ Γ b p.right →
      HasType (Ω := Ω) Δ Γ (.prim p a b) p.result
  | record {Ω Γ fs r} : Row.ascending fs = true → FieldsTy (Ω := Ω) Δ Γ fs r →
      HasType (Ω := Ω) Δ Γ (.record fs) (.record r)
  | get {Ω Γ t ℓ r T} : HasType (Ω := Ω) Δ Γ t (.record r) → Row.find? ℓ r = some T →
      HasType (Ω := Ω) Δ Γ (.get t ℓ) T
  | extend {Ω Γ t fs r r2} : HasType (Ω := Ω) Δ Γ t (.record r) → Row.ascending fs = true →
      FieldsTy (Ω := Ω) Δ Γ fs r2 → HasType (Ω := Ω) Δ Γ (.extend t fs) (.record (Row.merge r r2))
  | inj {Ω Γ r ℓ t A} : (Ty.sum r).wf = true → Row.find? ℓ r = some A → HasType (Ω := Ω) Δ Γ t A →
      HasType (Ω := Ω) Δ Γ (.inj (.sum r) ℓ t) (.sum r)
  | case {Ω Γ t arms r B} : HasType (Ω := Ω) Δ Γ t (.sum r) → ArmsTy (Ω := Ω) Δ Γ arms r B →
      HasType (Ω := Ω) Δ Γ (.case t arms) B
  | ite {Ω Γ c a b T} : HasType (Ω := Ω) Δ Γ c .bool → HasType (Ω := Ω) Δ Γ a T → HasType (Ω := Ω) Δ Γ b T →
      HasType (Ω := Ω) Δ Γ (.ite c a b) T
  | ref {Ω Γ i T} : Δ[i]? = some T → HasType (Ω := Ω) Δ Γ (.ref i) T
  | refuse {Ω Γ T w} : T.wf = true → Bounds.reasonOk w = true → HasType (Ω := Ω) Δ Γ (.refuse T w) T

  | hole {Ω Γ n σ d} : Ω.find? (fun d => d.name == n) = some d →
      SubstTy Δ Γ σ d.ctx Ω → HasType Δ Γ (.hole n σ) d.ty Ω

/-- Pointwise typing of an exact-length explicit substitution. -/
inductive SubstTy (Δ : List Ty) : List Ty → List Term → List Ty → (Ω : optParam HoleSignature []) → Prop
  | nil {Ω Γ} : SubstTy Δ Γ [] [] Ω
  | cons {Ω Γ t A σ Ψ} : HasType Δ Γ t A Ω → SubstTy Δ Γ σ Ψ Ω →
      SubstTy Δ Γ (t :: σ) (A :: Ψ) Ω

/-- Fields and their row: same labels, in order, each field at its type. -/
inductive FieldsTy (Δ : List Ty) : List Ty → List (Label × Term) → List (Label × Ty) → (Ω : optParam HoleSignature []) → Prop
  | nil {Ω Γ} : FieldsTy (Ω := Ω) Δ Γ [] []
  | cons {Ω Γ ℓ t T fs r} : HasType (Ω := Ω) Δ Γ t T → FieldsTy (Ω := Ω) Δ Γ fs r →
      FieldsTy (Ω := Ω) Δ Γ ((ℓ, t) :: fs) ((ℓ, T) :: r)

/-- Arms of a case over a sum row: same labels, in order, at least one, each body at `B` with
its payload bound. -/
inductive ArmsTy (Δ : List Ty) : List Ty → List (Label × Term) → List (Label × Ty) → Ty → (Ω : optParam HoleSignature []) → Prop
  | one {Ω Γ ℓ b A B} : HasType (Ω := Ω) Δ (A :: Γ) b B → ArmsTy (Ω := Ω) Δ Γ [(ℓ, b)] [(ℓ, A)] B
  | cons {Ω Γ ℓ b A B arms r} : HasType (Ω := Ω) Δ (A :: Γ) b B → ArmsTy (Ω := Ω) Δ Γ arms r B → arms ≠ [] →
      ArmsTy (Ω := Ω) Δ Γ ((ℓ, b) :: arms) ((ℓ, A) :: r) B
end

end Nanodregg.Lang
