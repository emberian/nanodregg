/-
# Lang.Proofs.Relocate — relocating `ref`s preserves typing

`Lang.load` puts a closure's packages into one `lib` and rewrites each body's `ref i` (an index into
ITS imports) to the closure's index of that import. If the map sends every import to a position of
the same type, the relocated body has the same type: so a body checked at install against its
imports' interfaces is typed in the loaded closure, which is what `LibTy` (and so
`checked_never_stuck`) needs of the deployed path.
-/
import Lang.Package
import Lang.Proofs.Typing

namespace Nanodregg.Lang

variable {Δ Δ' : List Ty} {f : Nat → Nat}

theorem relocateRow_ascending (f : Nat → Nat) :
    ∀ fs : List (Label × Term), Row.ascending (Term.relocateRow f fs) = Row.ascending fs
  | [] => rfl
  | [_] => rfl
  | (a, s) :: (b, t) :: rest => by
      have ih := relocateRow_ascending f ((b, t) :: rest)
      simp only [Term.relocateRow] at ih ⊢
      simp only [Row.ascending, ih]

mutual
theorem relocate_typed (hf : ∀ i A, Δ[i]? = some A → Δ'[f i]? = some A) :
    ∀ {Γ : List Ty} {t : Term} {T : Ty}, HasType Δ Γ t T → HasType Δ' Γ (t.relocate f) T
  | _, _, _, .var h => .var h
  | _, _, _, .lam hw hb => .lam hw (relocate_typed hf hb)
  | _, _, _, .app h1 h2 => .app (relocate_typed hf h1) (relocate_typed hf h2)
  | _, _, _, .fix h => .fix (relocate_typed hf h)
  | _, _, _, .nat h => .nat h
  | _, _, _, .bool => .bool
  | _, _, _, .bytes h => .bytes h
  | _, _, _, .prim h1 h2 => .prim (relocate_typed hf h1) (relocate_typed hf h2)
  | _, _, _, .record (fs := fs) ha h => by
      simp only [Term.relocate]
      exact .record (by rw [relocateRow_ascending]; exact ha) (relocateFields_typed hf h)
  | _, _, _, .get h hl => .get (relocate_typed hf h) hl
  | _, _, _, .extend (fs := fs) h ha hfs => by
      simp only [Term.relocate]
      exact .extend (relocate_typed hf h) (by rw [relocateRow_ascending]; exact ha) (relocateFields_typed hf hfs)
  | _, _, _, .inj hw hl h => .inj hw hl (relocate_typed hf h)
  | _, _, _, .case h ha => .case (relocate_typed hf h) (relocateArms_typed hf ha)
  | _, _, _, .ite h1 h2 h3 => .ite (relocate_typed hf h1) (relocate_typed hf h2) (relocate_typed hf h3)
  | _, _, _, .ref h => .ref (hf _ _ h)

theorem relocateFields_typed (hf : ∀ i A, Δ[i]? = some A → Δ'[f i]? = some A) :
    ∀ {Γ : List Ty} {fs : List (Label × Term)} {r : List (Label × Ty)},
      FieldsTy Δ Γ fs r → FieldsTy Δ' Γ (Term.relocateRow f fs) r
  | _, _, _, .nil => .nil
  | _, _, _, .cons h hs => .cons (relocate_typed hf h) (relocateFields_typed hf hs)

theorem relocateArms_typed (hf : ∀ i A, Δ[i]? = some A → Δ'[f i]? = some A) :
    ∀ {Γ : List Ty} {arms : List (Label × Term)} {r : List (Label × Ty)} {B : Ty},
      ArmsTy Δ Γ arms r B → ArmsTy Δ' Γ (Term.relocateRow f arms) r B
  | _, _, _, _, .one h => .one (relocate_typed hf h)
  | _, _, _, _, .cons (arms := a :: as) h ha _ =>
      .cons (relocate_typed hf h) (relocateArms_typed hf ha) (by simp [Term.relocateRow])
  | _, _, _, _, .cons (arms := []) _ _ hne => absurd rfl hne
end

end Nanodregg.Lang
