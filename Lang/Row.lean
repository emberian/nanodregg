/-
# Lang.Row — label-keyed rows, the one shape of records, sums, their types and their values

A row is a list of `(label, x)`. Canonical rows have strictly ascending labels (`ascending`), so
two record types with the same fields are equal as values. Every operation here looks only at the
labels, so a relation that holds pointwise between two rows with the same labels is preserved by
`put`, `merge` and `find?` (`Lang.Proofs.Row`).
-/
namespace Nanodregg.Lang

abbrev Label := String

namespace Row

variable {α : Type}

/-- The value at a label, first match. -/
def find? (ℓ : Label) : List (Label × α) → Option α
  | [] => none
  | (k, a) :: rest => if ℓ = k then some a else find? ℓ rest

/-- Strictly ascending labels: the canonical form. -/
def ascending : List (Label × α) → Bool
  | [] => true
  | [_] => true
  | a :: b :: rest => decide (a.1 < b.1) && ascending (b :: rest)

/-- Insert or replace one entry, keeping an ascending row ascending. -/
def put (ℓ : Label) (a : α) : List (Label × α) → List (Label × α)
  | [] => [(ℓ, a)]
  | (k, b) :: rest =>
      if ℓ < k then (ℓ, a) :: (k, b) :: rest
      else if ℓ = k then (ℓ, a) :: rest
      else (k, b) :: put ℓ a rest

/-- `over` overrides and extends `base`: the row of `extend`. -/
def merge (base : List (Label × α)) : List (Label × α) → List (Label × α)
  | [] => base
  | (ℓ, a) :: rest => merge (put ℓ a base) rest

end Row
end Nanodregg.Lang
