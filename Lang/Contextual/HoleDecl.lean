/- The shared contextual declaration, independent of the closure implementation. -/
namespace Nanodregg.Lang.Contextual

/-- A hole declaration `u :: [Ψ ⊢ A]`: the hole's name, its local context, its type. -/
structure HoleDecl (Ctx Ty : Type) where
  name : Nat
  ctx : Ctx
  ty : Ty

end Nanodregg.Lang.Contextual
