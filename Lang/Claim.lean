/-
# Lang.Claim — a claim a package makes of itself, and the checker of its certifying shape (LANG-83)

A claim is a sentence in a small fixed language that a package carries in its identity and the
kernel refuses to install unless the package's own term bears it: proof-carrying code (Necula 1997)
in the one form nano's install check already has. The type check is such a checker (the claim is
the interface type, the proof is the term, `checkE` decides it in one pass, `Lang.Proofs.Check` is
its soundness); a claim extends the sentences that check the same way. The proof is the term's
SHAPE, the checker is a one-pass function beside `checkE` (unmetered, O(|term|), bounded by the
wire), and its soundness is one Lean theorem, `Lang.Proofs.Claim.guardedBy_sound`. No nano term
ever checks a proof; the kernel does, once, at install, as it types the term.

`keeps inv law`: every state an object of the package holds satisfies the interface field
`inv : fn S bool`, because the law `law` refuses every birth, adoption, write and invoke whose new
state fails it. Its proof is the law's control structure: every `ok` leaf of the law's body is
dominated by the true branch of `ite (app inv new) _ _` (`Term.guardedBy`), the `relaw` arm of a
`case` on `req.occasion` excepted, because the kernel judges a law change over the unchanged state
(`Kernel.Receive.law`; `Lang.Proofs.Chain.LawKeeps`). The `adopt` arm is NOT excepted: an adoption
is a base case like a birth (the incoming law judges the state it is adopted over, KERNEL-27), so a
law in shape refuses to be adopted over a state that fails its invariant.

The checker is sound by construction and incomplete by design: the only former it lets MEAN
`inj "ok" _` is a literal `inj` leaf, so a law that returns a verdict it read from its state, or
through a helper lambda, is not in certifying shape, and its claim is refused by name; the author
writes the law in shape (`Std.keeps` emits one), as a certifying compiler emits checkable code. The
compared `inv` is the closed literal term of the interface field, so no index shifting is needed:
`app inv (var k)` is syntactic equality with `k` the index of `new` at that depth.
Design: `redregg/work/promo/DESIGN-PCC.md`.
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
