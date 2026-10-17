/-
# Lang.Proofs.Data — decoded data has its type, and data enters the machine typed

`Conforms d T`: data `d` is a value of data type `T` (in bounds; a sum's label names its first arm).
`getData_conforms`: whatever the type-directed decoder returns conforms to the type it decoded at,
from ANY bytes. `toVal_typed`: conforming data becomes a machine value of its type. With
`method_run_sound` this discharges the typing premises for everything a receiver decodes from cells.
-/
import Lang.Wire
import Lang.Proofs.RunTy

namespace Nanodregg.Lang

mutual
inductive Conforms : Data → Ty → Prop
  | nat {n : Nat} : n < Bounds.natLimit → Conforms (.nat n) .nat
  | bool {b : Bool} : Conforms (.bool b) .bool
  | bytes {s : ByteArray} : s.size ≤ Bounds.bytesMax → Conforms (.bytes s) .bytes
  | record {ds r} : RowConforms ds r → Conforms (.record ds) (.record r)
  | inj {r ℓ A d} : Row.find? ℓ r = some A → Conforms d A → Conforms (.inj ℓ d) (.sum r)

inductive RowConforms : List (Label × Data) → List (Label × Ty) → Prop
  | nil : RowConforms [] []
  | cons {ℓ d T ds r} : Conforms d T → RowConforms ds r → RowConforms ((ℓ, d) :: ds) ((ℓ, T) :: r)
end

variable {Δ : List Ty}

mutual
theorem toVal_typed : ∀ {d : Data} {T : Ty}, Conforms d T → ValTy Δ d.toVal T
  | _, _, .nat h => .nat h
  | _, _, .bool => .bool
  | _, _, .bytes h => .bytes h
  | _, _, .record h => .record (rowToVal_typed h)
  | _, _, .inj hf h => .inj hf (toVal_typed h)

theorem rowToVal_typed : ∀ {ds : List (Label × Data)} {r : List (Label × Ty)},
    RowConforms ds r → ThunksTy Δ (Data.rowToVal ds) r
  | _, _, .nil => .nil
  | _, _, .cons h hs => .cons (.cons (toVal_typed h) .nil) (.var rfl) (rowToVal_typed hs)
end

theorem getU64_lt {b : ByteArray} {i n j : Nat} (h : Wire.getU64 b i = .ok (n, j)) :
    n < Bounds.natLimit := by
  unfold Wire.getU64 at h
  cases e : Codec.Stream.u64.get b i with
  | error _ => simp [e, Except.map] at h
  | ok p =>
    simp only [e, Except.map, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, _⟩ := h
    exact p.1.toNat_lt

theorem getRaw_size {max : Nat} {b s : ByteArray} {i j : Nat} (h : Wire.getRaw max b i = .ok (s, j)) :
    s.size ≤ max := by
  unfold Wire.getRaw at h
  split at h
  · simp at h
  · rename_i n k _
    split at h
    · split at h
      · simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, _⟩ := h
        simp [ByteArray.size_extract]; omega
      · simp at h
    · simp at h

mutual
theorem getData_conforms (b : ByteArray) : ∀ (T : Ty) {i : Nat} {d : Data} {j : Nat},
    Wire.getData b T i = .ok (d, j) → Conforms d T
  | .nat, i, d, j, h => by
    unfold Wire.getData at h
    cases e : Wire.getU64 b i with
    | error _ => simp [e, Except.map] at h
    | ok p =>
      simp only [e, Except.map, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, _⟩ := h
      exact .nat (getU64_lt e)
  | .bool, i, d, j, h => by
    unfold Wire.getData at h
    split at h <;> first | (simp at h; done) | (cases h; exact .bool)
  | .bytes, i, d, j, h => by
    unfold Wire.getData at h
    cases e : Wire.getRaw Bounds.bytesMax b i with
    | error _ => simp [e, Except.map] at h
    | ok p =>
      simp only [e, Except.map, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, _⟩ := h
      exact .bytes (getRaw_size e)
  | .record r, i, d, j, h => by
    unfold Wire.getData at h
    cases e : Wire.getDataRow b r i with
    | error _ => simp [e, Except.map] at h
    | ok p =>
      simp only [e, Except.map, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, _⟩ := h
      exact .record (getDataRow_conforms b r e)
  | .sum r, i, d, j, h => by
    unfold Wire.getData at h
    split at h
    · simp at h
    · rename_i n k _
      obtain ⟨ℓ, A, d', rfl, hf, hc⟩ := getArm_conforms b r r h
      exact .inj hf hc
  | .fn _ _, i, d, j, h => by unfold Wire.getData at h; simp at h

theorem getDataRow_conforms (b : ByteArray) : ∀ (r : List (Label × Ty)) {i : Nat}
    {ds : List (Label × Data)} {j : Nat}, Wire.getDataRow b r i = .ok (ds, j) → RowConforms ds r
  | [], i, ds, j, h => by
    unfold Wire.getDataRow at h; simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, _⟩ := h; exact .nil
  | (ℓ, t) :: r, i, ds, j, h => by
    unfold Wire.getDataRow at h
    split at h
    · simp at h
    · rename_i d k hd
      cases e : Wire.getDataRow b r k with
      | error _ => simp [e, Except.map] at h
      | ok p =>
        simp only [e, Except.map, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, _⟩ := h
        exact .cons (getData_conforms b t hd) (getDataRow_conforms b r e)

theorem getArm_conforms (b : ByteArray) (full : List (Label × Ty)) :
    ∀ (r : List (Label × Ty)) {n i : Nat} {d : Data} {j : Nat},
      Wire.getArm b full r n i = .ok (d, j) →
      ∃ ℓ A d', d = .inj ℓ d' ∧ Row.find? ℓ full = some A ∧ Conforms d' A
  | [], n, i, d, j, h => by unfold Wire.getArm at h; simp at h
  | (ℓ, t) :: r, 0, i, d, j, h => by
    unfold Wire.getArm at h
    split at h
    · rename_i hf
      cases e : Wire.getData b t i with
      | error _ => simp [e, Except.map] at h
      | ok p =>
        simp only [e, Except.map, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, _⟩ := h
        exact ⟨ℓ, t, p.1, rfl, hf, getData_conforms b t e⟩
    · simp at h
  | _ :: r, n + 1, i, d, j, h => by
    unfold Wire.getArm at h
    exact getArm_conforms b full r h
end

theorem decodeData_conforms {T : Ty} {b : ByteArray} {d : Data}
    (h : Wire.decodeData T b = .ok d) : Conforms d T := by
  unfold Wire.decodeData Wire.whole at h
  split at h
  · rename_i d' j hd
    split at h
    · cases h; exact getData_conforms b T hd
    · simp at h
  · simp at h

end Nanodregg.Lang
