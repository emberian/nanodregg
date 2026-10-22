/- De Bruijn index maps shared by the deployed term operations (`Lang.Subst`) and the CMTT core
(`Lang.Contextual.Core`): one of each. -/

namespace Nanodregg.Lang

/-- A renaming under one more ordinary binder. -/
def upR (ρ : Nat → Nat) : Nat → Nat
  | 0 => 0
  | i + 1 => ρ i + 1

/-- The index map of weakening at `x`: indices from `x` up move up by one. -/
def liftIdx (x i : Nat) : Nat := if i < x then i else i + 1

/-- Its inverse away from `x`: indices above `x` move down by one. -/
def lowerIdx (x i : Nat) : Nat := if i < x then i else i - 1

end Nanodregg.Lang
