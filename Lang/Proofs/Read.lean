/-
# Lang.Proofs.Read — the reader's refusals are names, and a data literal it accepts has its type

`ReadRefusal.name_injective`: distinct refusal constructors have distinct names (law 7).
`dataAt_conforms`: whatever `Read.dataAt` accepts at type `T` conforms to `T` (in bounds, the
type's labels in its order), so `Program.stateSlots` / `Wire.encodeData` have bytes for it.
-/
import Lang.Read
import Lang.Proofs.Data

namespace Nanodregg.Lang.Read

theorem _root_.Nanodregg.Lang.CheckError.name_injective (a b : CheckError) (h : a.name = b.name) :
    a.ctorIdx = b.ctorIdx := by
  cases a <;> cases b <;> simp_all [CheckError.name] <;> rfl

theorem ReadRefusal.name_injective (a b : ReadRefusal) (h : a.name = b.name) : a.ctorIdx = b.ctorIdx := by
  cases a <;> cases b <;> simp_all [ReadRefusal.name] <;> rfl

theorem scalarAt_conforms : ∀ (T : Ty) (x : SExp) {v : Data}, scalarAt T x = .ok v → Conforms v T := by
  intro T x v h
  unfold scalarAt at h
  split at h
  · split at h
    · split at h
      · cases h; exact .nat (by assumption)
      · cases h
    · cases h
  · split at h
    · cases h; exact .bool
    · split at h
      · cases h; exact .bool
      · cases h
  · split at h
    · cases h; exact .bytes (by assumption)
    · cases h
  · split at h
    · split at h
      · cases h; exact .bytes (by assumption)
      · cases h
    · cases h
  · split at h
    · split at h
      · cases h; exact .digest (by assumption)
      · cases h
    · cases h
  · cases h

mutual
theorem dataAt_conforms : (d : Nat) → (T : Ty) → (x : SExp) → ∀ {v : Data}, dataAt d T x = .ok v → Conforms v T
  | 0, _, _, _, h => by simp [dataAt] at h
  | d + 1, T, x, v, h => by
    unfold dataAt at h
    split at h
    · rename_i row p _ fs
      cases hf : dataFields fs with
      | error e => rw [hf] at h; cases h
      | ok fs' =>
        rw [hf] at h
        cases hr : dataRowWith (fun A v => dataAt d A v) p row (Row.sort fs') with
        | error e => simp only [bind, Except.bind, hr] at h; cases h
        | ok ds =>
          simp only [bind, Except.bind, hr, pure, Except.pure] at h
          cases h
          exact .record (dataRow_conforms d p row _ hr)
    · rename_i row p _ ℓ w
      split at h
      · rename_i A hA
        cases hw : dataAt d A w with
        | error e => simp only [bind, Except.bind, hw] at h; cases h
        | ok u =>
          simp only [bind, Except.bind, hw, pure, Except.pure] at h
          cases h
          exact .inj hA (dataAt_conforms d A w hw)
      · cases h
    · rename_i row p ℓ
      split at h
      · rename_i hA
        cases h; exact .inj hA (.record .nil)
      · cases h
    · cases h
    · cases h
    · cases h
    · exact scalarAt_conforms _ _ h

theorem dataRow_conforms : ∀ (d p : Nat) (row : List (Label × Ty)) (fs : List (Label × SExp))
    {ds : List (Label × Data)}, dataRowWith (fun A v => dataAt d A v) p row fs = .ok ds → RowConforms ds row
  | _, _, [], [], _, h => by simp [dataRowWith] at h; subst h; exact .nil
  | _, _, [], _ :: _, _, h => by simp [dataRowWith] at h
  | _, _, _ :: _, [], _, h => by simp [dataRowWith] at h
  | d, p, (ℓ, A) :: row, (k, v) :: fs, ds, h => by
    unfold dataRowWith at h
    split at h
    · rename_i hk
      subst hk
      cases hv : dataAt d A v with
      | error e => simp only [bind, Except.bind, hv] at h; cases h
      | ok u =>
        cases hr : dataRowWith (fun A v => dataAt d A v) p row fs with
        | error e => simp only [bind, Except.bind, hv, hr] at h; cases h
        | ok us =>
          simp only [bind, Except.bind, hv, hr, pure, Except.pure] at h
          cases h
          exact .cons (dataAt_conforms d A v hv) (dataRow_conforms d p row fs hr)
    · cases h
end

end Nanodregg.Lang.Read
