/- Contextual declarations and candidate code are immutable ROM, not row values. -/
import Lang.Check
import Lang.Subst

namespace Nanodregg.Lang

/-- What a ROM support, hypothesis or guard pin asserts (E1, LANG-75.1): a row of the hole object at
one exact version, or a kernel cell that is LIVE in the caller's pinned view. A cell is never pinned
"at a version": a grant's slots move on every spend (KERNEL-60), so the assumption is the fact that
the cell stands, which a revoke contradicts (de Kleer 1986 §4.9).

Every support precedes the Turn that reads it (C7, LANG-75.7). The receiver judges each pin on the
World before the Turn (`touchCheck_pin`; a row pin on its row as it stood before the Turn, since a
Turn's row slots are distinct, `rowStep_pin`), and an admitted write leaves its cell strictly past that
entry (`stale_behind_forever`). So no Turn's support names what the Turn writes. A row support is a
row of this hole object, and a cell support says only that a cell stands. No support names another
hole's selection (activities card F (2)), so there is no graph of holes to be acyclic. A theorem lands
with card F (3), the first row that needs a hole to cite a hole. -/
inductive SupportPin where
  | row (rel : Nat) (key : ByteArray) (ver : Nat)
  | cell (id : ByteArray)
  deriving Inhabited, DecidableEq

/-- A code candidate and the derivation supports required independently of its variables. -/
structure HoleCode where
  body : Term
  supports : List SupportPin := []
  deriving Inhabited, DecidableEq

/-- One live contextual declaration. Selection rows contain an index into code.
The context support list is exact-length; none means a structural assumption.
The guard receives whether its guard pin currently holds, as its sole boolean
variable. It has no imports or holes and runs on the ordinary machine. -/
structure HoleROM where
  name : Nat
  ctx : List Ty
  ty : Ty
  code : List HoleCode
  selectionRel : Nat
  selectionKey : ByteArray
  hypotheses : List (Option SupportPin)
  guardPin : Option SupportPin
  guard : Term
  deriving Inhabited, DecidableEq

def HoleROM.decl (h : HoleROM) : HoleDecl (List Ty) Ty :=
  ⟨h.name, h.ctx, h.ty⟩

def holeSignature (hs : List HoleROM) : HoleSignature := hs.map HoleROM.decl

end Nanodregg.Lang
