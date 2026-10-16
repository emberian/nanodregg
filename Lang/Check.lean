/-
# Lang.Check — the type checker, a total function (DECISIONS LANG-3)

`infer Δ Γ t` is the type of `t` under the closure's package types `Δ` (indexed by `ref`) and
the local types `Γ` (indexed by `var`), or `none`. It is syntax-directed and annotation-driven,
O(size of `t` × size of the types it compares). `Lang.Proofs.Check` proves it equal to the typing
relation `HasType` (sound and complete), so a term's type is unique.

Bounds are typing facts: a literal natural must be below `Bounds.natLimit` and a literal byte
string at most `Bounds.bytesMax`, so every value a checked program starts from is in bounds.
A `case` must have at least one arm (its result type comes from the arms).
-/
import Lang.Bounds
import Lang.Term

namespace Nanodregg.Lang

mutual
def infer (Δ Γ : List Ty) : Term → Option Ty
  | .var i => Γ[i]?
  | .lam A b => if A.wf then (infer Δ (A :: Γ) b).map (.fn A) else none
  | .app f a =>
      match infer Δ Γ f, infer Δ Γ a with
      | some (.fn A B), some A' => if A = A' then some B else none
      | _, _ => none
  | .fix t =>
      match infer Δ Γ t with
      | some (.fn (.record r) (.record r')) => if r = r' then some (.record r) else none
      | _ => none
  | .nat n => if n < Bounds.natLimit then some .nat else none
  | .bool _ => some .bool
  | .bytes s => if s.size ≤ Bounds.bytesMax then some .bytes else none
  | .prim p a b =>
      match infer Δ Γ a, infer Δ Γ b with
      | some A, some B => if A = p.left ∧ B = p.right then some p.result else none
      | _, _ => none
  | .record fs => if Row.ascending fs then (inferFields Δ Γ fs).map .record else none
  | .get t ℓ =>
      match infer Δ Γ t with
      | some (.record r) => Row.find? ℓ r
      | _ => none
  | .extend t fs =>
      match infer Δ Γ t with
      | some (.record r) =>
          if Row.ascending fs then (inferFields Δ Γ fs).map (fun r2 => .record (Row.merge r r2))
          else none
      | _ => none
  | .inj T ℓ t =>
      match T with
      | .sum r =>
          if T.wf then
            match Row.find? ℓ r, infer Δ Γ t with
            | some A, some A' => if A = A' then some T else none
            | _, _ => none
          else none
      | _ => none
  | .case t arms =>
      match infer Δ Γ t with
      | some (.sum r) => inferArms Δ Γ arms r
      | _ => none
  | .ite c t e =>
      match infer Δ Γ c, infer Δ Γ t, infer Δ Γ e with
      | some .bool, some A, some B => if A = B then some A else none
      | _, _, _ => none
  | .ref i => Δ[i]?

/-- The row of a list of fields, label for label. -/
def inferFields (Δ Γ : List Ty) : List (Label × Term) → Option (List (Label × Ty))
  | [] => some []
  | (ℓ, t) :: fs =>
      match infer Δ Γ t, inferFields Δ Γ fs with
      | some T, some r => some ((ℓ, T) :: r)
      | _, _ => none

/-- The common type of the arms of a case over the sum row `r`: one arm per label, in order,
each binding its payload; at least one arm. -/
def inferArms (Δ Γ : List Ty) : List (Label × Term) → List (Label × Ty) → Option Ty
  | [(ℓ, b)], [(ℓ', A)] => if ℓ = ℓ' then infer Δ (A :: Γ) b else none
  | (ℓ, b) :: arms@(_ :: _), (ℓ', A) :: r =>
      if ℓ = ℓ' then
        match infer Δ (A :: Γ) b, inferArms Δ Γ arms r with
        | some B, some B' => if B = B' then some B else none
        | _, _ => none
      else none
  | _, _ => none
end

/-- A closed term checked against its declared type. -/
def check (Δ : List Ty) (t : Term) (T : Ty) : Bool := infer Δ [] t == some T

/-- The closure's bodies are closed and have the types `ref` gives them. -/
def checkLib (Δ : List Ty) (lib : List Term) : Bool :=
  lib.length == Δ.length && (lib.zip Δ).all fun p => check Δ p.1 p.2

end Nanodregg.Lang
