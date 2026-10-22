/- The shared contextual hole declaration: `Lang.Check`'s `HoleSignature` is a list of these; the calculus laws
(`CalculusLaws`, `Lang.Proofs.Contextual.LangInstance`) instantiate it at a calculus's own context and type. -/
namespace Nanodregg.Lang

/-- A hole declaration `u :: [Ψ ⊢ A]`: the hole's name, its local context, its type. -/
structure HoleDecl (Ctx Ty : Type) where
  name : Nat
  ctx : Ctx
  ty : Ty

end Nanodregg.Lang
