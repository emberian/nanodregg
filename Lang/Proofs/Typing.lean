/-
# Lang.Proofs.Typing — the typing relation, the specification `Lang.infer` decides

`HasType Δ Γ t T`: under the closure's package types `Δ` and local types `Γ`, `t` has type `T`.
One rule per constructor, read off the language's meaning; `Lang.Proofs.Check` proves `infer`
returns exactly the `T` this relation allows. Nothing deployed runs this relation.
-/
import Lang.Check

namespace Nanodregg.Lang

mutual
inductive HasType (Δ : List Ty) : List Ty → Term → Ty → Prop
  | var {Γ i T} : Γ[i]? = some T → HasType Δ Γ (.var i) T
  | lam {Γ A b B} : A.wf = true → HasType Δ (A :: Γ) b B → HasType Δ Γ (.lam A b) (.fn A B)
  | app {Γ f a A B} : HasType Δ Γ f (.fn A B) → HasType Δ Γ a A → HasType Δ Γ (.app f a) B
  | fix {Γ t r} : HasType Δ Γ t (.fn (.record r) (.record r)) → HasType Δ Γ (.fix t) (.record r)
  | nat {Γ n} : n < Bounds.natLimit → HasType Δ Γ (.nat n) .nat
  | bool {Γ b} : HasType Δ Γ (.bool b) .bool
  | bytes {Γ s} : s.size ≤ Bounds.bytesMax → HasType Δ Γ (.bytes s) .bytes
  | digest {Γ s} : s.size ≤ Bounds.digestBytesMax → HasType Δ Γ (.digest s) .digest
  | prim {Γ p a b} : HasType Δ Γ a p.left → HasType Δ Γ b p.right →
      HasType Δ Γ (.prim p a b) p.result
  | record {Γ fs r} : Row.ascending fs = true → FieldsTy Δ Γ fs r →
      HasType Δ Γ (.record fs) (.record r)
  | get {Γ t ℓ r T} : HasType Δ Γ t (.record r) → Row.find? ℓ r = some T →
      HasType Δ Γ (.get t ℓ) T
  | extend {Γ t fs r r2} : HasType Δ Γ t (.record r) → Row.ascending fs = true →
      FieldsTy Δ Γ fs r2 → HasType Δ Γ (.extend t fs) (.record (Row.merge r r2))
  | inj {Γ r ℓ t A} : (Ty.sum r).wf = true → Row.find? ℓ r = some A → HasType Δ Γ t A →
      HasType Δ Γ (.inj (.sum r) ℓ t) (.sum r)
  | case {Γ t arms r B} : HasType Δ Γ t (.sum r) → ArmsTy Δ Γ arms r B →
      HasType Δ Γ (.case t arms) B
  | ite {Γ c a b T} : HasType Δ Γ c .bool → HasType Δ Γ a T → HasType Δ Γ b T →
      HasType Δ Γ (.ite c a b) T
  | ref {Γ i T} : Δ[i]? = some T → HasType Δ Γ (.ref i) T
  | refuse {Γ T w} : T.wf = true → Bounds.reasonOk w = true → HasType Δ Γ (.refuse T w) T

/-- Fields and their row: same labels, in order, each field at its type. -/
inductive FieldsTy (Δ : List Ty) : List Ty → List (Label × Term) → List (Label × Ty) → Prop
  | nil {Γ} : FieldsTy Δ Γ [] []
  | cons {Γ ℓ t T fs r} : HasType Δ Γ t T → FieldsTy Δ Γ fs r →
      FieldsTy Δ Γ ((ℓ, t) :: fs) ((ℓ, T) :: r)

/-- Arms of a case over a sum row: same labels, in order, at least one, each body at `B` with
its payload bound. -/
inductive ArmsTy (Δ : List Ty) : List Ty → List (Label × Term) → List (Label × Ty) → Ty → Prop
  | one {Γ ℓ b A B} : HasType Δ (A :: Γ) b B → ArmsTy Δ Γ [(ℓ, b)] [(ℓ, A)] B
  | cons {Γ ℓ b A B arms r} : HasType Δ (A :: Γ) b B → ArmsTy Δ Γ arms r B → arms ≠ [] →
      ArmsTy Δ Γ ((ℓ, b) :: arms) ((ℓ, A) :: r) B
end

end Nanodregg.Lang
