/- Structural equality of first-order data, emitted as ordinary core terms. -/
import Lang.Data

namespace Nanodregg.Lang.Std

mutual
/-- Equality body with right at var 0 and left at var 1.
Function types have no data inhabitants and refuse by name. -/
def eqDataBody : Ty → Term
  | .nat => .prim .eq (.var 1) (.var 0)
  | .bool => .ite (.var 1) (.var 0) (.ite (.var 0) (.bool false) (.bool true))
  | .bytes => .prim .beq (.var 1) (.var 0)
  | .digest => .prim .deq (.var 1) (.var 0)
  | .fn _ _ => .refuse .bool "eqData: function".toUTF8
  | .record r => eqDataFields r
  | .sum r => .case (.var 1) (r.attach.map fun p =>
      (p.val.1, .case (.var 1) (r.map fun q =>
        (q.1, if p.val.1 = q.1 then
          .app (.app (.lam p.val.2 (.lam p.val.2 (eqDataBody p.val.2))) (.var 1)) (.var 0)
          else .bool false))))

termination_by T => sizeOf T
decreasing_by
  all_goals simp_wf
  have h := List.sizeOf_lt_of_mem p.property
  rcases p with ⟨⟨l, t⟩, hm⟩
  simp_all; omega

/-- Conjunction of structural comparisons of a record's fields. -/
def eqDataFields : List (Label × Ty) → Term
  | [] => .bool true
  | (l, t) :: r => .ite
      (.app (.app (.lam t (.lam t (eqDataBody t))) (.get (.var 1) l)) (.get (.var 0) l))
      (eqDataFields r) (.bool false)
termination_by r => sizeOf r
end

/-- Structural equality at a data type. The lambdas bind each operand once, so
case arms cannot capture the caller's variables. Canonical record types are
required by the meaning theorem, as they are by the deployed checker. -/
def eqData (T : Ty) (x y : Term) : Term :=
  .app (.app (.lam T (.lam T (eqDataBody T))) x) y

end Nanodregg.Lang.Std
