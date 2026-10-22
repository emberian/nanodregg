/- The shared contextual hole declaration: `Lang.Check`'s `HoleSignature` is a list of these; the closure
(`Lang.Contextual.Closure`) instantiates it at its own context and type. -/
namespace Nanodregg.Lang

/-- A hole declaration `u :: [Ψ ⊢ A]`: the hole's name, its local context, its type. -/
structure HoleDecl (Ctx Ty : Type) where
  name : Nat
  ctx : Ctx
  ty : Ty

end Nanodregg.Lang
