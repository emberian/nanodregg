/- Contextual declarations and candidate code are immutable ROM, not row values. -/
import Lang.Check
import Lang.Subst

namespace Nanodregg.Lang

/-- A fact at one authenticated row slot and one exact version. -/
structure HolePin where
  rel : Nat
  key : ByteArray
  ver : Nat
  deriving Inhabited, DecidableEq

/-- A code candidate and the derivation supports required independently of its variables. -/
structure HoleCode where
  body : Term
  supports : List HolePin := []
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
  hypotheses : List (Option HolePin)
  guardPin : Option HolePin
  guard : Term
  deriving Inhabited, DecidableEq

def HoleROM.decl (h : HoleROM) : HoleDecl (List Ty) Ty :=
  ⟨h.name, h.ctx, h.ty⟩

def holeSignature (hs : List HoleROM) : HoleSignature := hs.map HoleROM.decl

end Nanodregg.Lang
