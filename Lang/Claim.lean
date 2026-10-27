/-
# Lang.Claim — a certifying-shape checker for package laws

`Claim.keeps` names an invariant and a law. `Term.guardedBy` checks a restricted law
shape: every literal successful leaf is guarded by the invariant applied to the new state,
except a relaw arm over unchanged state. Adoption is not excepted.
`Lang.Proofs.Claim.guardedBy_sound` states the checker's meaning; the LK journey exercises
accepted and rejected shapes.

This module supplies the checker, not package admission: `Package` carries no claims field,
and its wire/install path does not call this checker. A general helper-returned verdict or
an equivalent inline test need not have the accepted syntax.
-/
import Lang.Subst

namespace Nanodregg.Lang

/-- A claim a package makes of itself, checked at install (LANG-83). -/
inductive Claim
  /-- every state an object of the package holds satisfies the interface field `inv : fn S bool`:
  the law `law` refuses every birth, adoption, write and invoke whose new state fails it -/
  | keeps (inv law : Label)
  deriving DecidableEq, Repr, Inhabited

mutual
/-- Every `ok` leaf of `t` is dominated by the true branch of `ite (app I (var k)) _ _`, or sits in
the `relaw` arm of a `case` on `get (var r) "occasion"`; `k` is the index of `new` and `r` of `req`
at the current depth (`1` and `0` under a law's three binders). Only a literal `inj` leaf may be an
`ok`; every other former is refused, so the walk is sound by construction. -/
def Term.guardedBy (I : Term) : (k r : Nat) → Term → Bool
  | k, r, .ite c a b => (c == .app I (.var k) || Term.guardedBy I k r a) && Term.guardedBy I k r b
  | k, r, .case s arms => Term.guardedArms I (k + 1) (r + 1) (s == .get (.var r) "occasion") arms
  | _, _, .inj _ ℓ _ => ℓ != "ok"
  | _, _, .refuse _ _ => true
  | _, _, _ => false

/-- Each arm's body is guarded, or (`occ`: the case is on the occasion) the arm is `relaw`. -/
def Term.guardedArms (I : Term) (k r : Nat) (occ : Bool) : List (Label × Term) → Bool
  | [] => true
  | (ℓ, body) :: arms =>
      ((occ && ℓ == "relaw") || Term.guardedBy I k r body) && Term.guardedArms I k r occ arms
end

end Nanodregg.Lang
