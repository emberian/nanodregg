/-
# Lang.Proofs.Data — the data codec is canonical, decoded data has its type, and data enters the
machine typed

`dataStream_lawful`: the stream at every type the wire carries is `Lawful` (composed from CODEC's combinator
theorems). `decodeData_eq_ok_iff`: `decodeData T b = .ok d ↔ encodeData T d = some b`: one value,
one byte string. `Conforms d T`: data `d` is a value of data type `T` (in bounds; a sum's label names
its first arm). `decodeData_conforms`: whatever the decoder returns conforms to the type it decoded
at, from ANY bytes. `toVal_typed`: conforming data becomes a machine value of its type. With
`method_run_sound` this discharges the typing premises for everything a receiver decodes from cells.
-/
import Lang.Wire.Data
import Lang.Proofs.RunTy
import Codec.Proofs.Stream
import Codec.Proofs.Kernel

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


/-! ## The stream is lawful -/

namespace Wire
open Nanodregg.Codec Nanodregg.Codec.Stream

theorem noData_lawful : Lawful noData :=
  refine_lawful unit_lawful _ (fun y => nomatch y) (fun _ _ h => by simp at h)

mutual
theorem dataStream_lawful : (T : Ty) → tyWire T = true → Lawful (dataStream T)
  | .nat, _ => u64_lawful
  | .bool, _ => bool_lawful
  | .bytes, _ => bytesOf_lawful _ (by decide)
  | .fn _ _, _ => noData_lawful
  | .record r, h => by
    simp only [tyWire, Bool.and_eq_true] at h
    exact rowStream_lawful r h.2
  | .sum r, h => by
    simp only [tyWire, Bool.and_eq_true, decide_eq_true_eq] at h
    exact tagged_lawful _ (armStream_lawful r h.2) (Kernel.finOf?_finCode (by simpa [rowMax] using h.1))
      Kernel.finCode_of

theorem rowStream_lawful : (r : List (Label × Ty)) → tyRowWire r = true → Lawful (rowStream r)
  | [], _ => unit_lawful
  | (_, t) :: r, h => by
    simp only [tyRowWire, Bool.and_eq_true] at h
    exact product_lawful (dataStream_lawful t h.1.2) (rowStream_lawful r h.2)

theorem armStream_lawful : (r : List (Label × Ty)) → tyRowWire r = true → ∀ i, Lawful (armStream r i)
  | [], _, i => Fin.elim0 i
  | (_, t) :: _, h, ⟨0, _⟩ => by
    simp only [tyRowWire, Bool.and_eq_true] at h
    exact dataStream_lawful t h.1.2
  | _ :: r, h, ⟨i + 1, hi⟩ => by
    simp only [tyRowWire, Bool.and_eq_true] at h
    exact armStream_lawful r h.2 ⟨i, Nat.lt_of_succ_lt_succ hi⟩
end

/-! ## Canonical rows have distinct labels -/

theorem ascending_tail {k : Label} {t : Ty} {r : List (Label × Ty)}
    (h : Row.ascending ((k, t) :: r) = true) : Row.ascending r = true := by
  cases r with
  | nil => rfl
  | cons e r => simp only [Row.ascending, Bool.and_eq_true] at h; exact h.2

theorem ascending_lt_of_find {k ℓ : Label} {t A : Ty} :
    ∀ {r : List (Label × Ty)}, Row.ascending ((k, t) :: r) = true → Row.find? ℓ r = some A → k < ℓ
  | [], _, h => by simp [Row.find?] at h
  | (k2, t2) :: r, ha, hf => by
    simp only [Row.ascending, Bool.and_eq_true, decide_eq_true_eq] at ha
    simp only [Row.find?] at hf
    split at hf
    · rename_i he; subst he; exact ha.1
    · exact String.lt_trans ha.1 (ascending_lt_of_find ha.2 hf)

/-! ## `toData` and `ofData` are inverse at a canonical type -/

mutual
theorem toData_ofData : (T : Ty) → ∀ {d : Data} {x : DataAt T}, ofData T d = some x → toData T x = d
  | .nat, .nat n, x, h => by
    simp only [ofData] at h
    split at h
    · cases h; rfl
    · simp at h
  | .bool, .bool b, x, h => by simp only [ofData, Option.some.injEq] at h; subst h; rfl
  | .bytes, .bytes s, x, h => by
    simp only [ofData] at h
    split at h
    · cases h; rfl
    · simp at h
  | .record r, .record fs, x, h => by
    simp only [ofData] at h
    simp only [toData, rowToData_rowOfData r h]
  | .sum r, .inj ℓ d, ⟨i, y⟩, h => by
    simp only [ofData] at h
    exact armToData_armOfData r h
  | .nat, .bool _, _, h | .nat, .bytes _, _, h | .nat, .record _, _, h | .nat, .inj _ _, _, h
  | .bool, .nat _, _, h | .bool, .bytes _, _, h | .bool, .record _, _, h | .bool, .inj _ _, _, h
  | .bytes, .nat _, _, h | .bytes, .bool _, _, h | .bytes, .record _, _, h | .bytes, .inj _ _, _, h
  | .record _, .nat _, _, h | .record _, .bool _, _, h | .record _, .bytes _, _, h
  | .record _, .inj _ _, _, h
  | .sum _, .nat _, _, h | .sum _, .bool _, _, h | .sum _, .bytes _, _, h | .sum _, .record _, _, h
  | .fn _ _, _, _, h => by simp [ofData] at h

theorem rowToData_rowOfData : (r : List (Label × Ty)) → ∀ {fs : List (Label × Data)} {x : RowAt r},
    rowOfData r fs = some x → rowToData r x = fs
  | [], [], x, _ => rfl
  | (ℓ, t) :: r, (k, d) :: fs, x, h => by
    simp only [rowOfData] at h
    split at h
    · rename_i hk
      subst hk
      split at h
      · rename_i a y ha hy
        cases h
        simp only [rowToData, toData_ofData t ha, rowToData_rowOfData r hy]
      · simp at h
    · simp at h
  | [], _ :: _, _, h | _ :: _, [], _, h => by simp [rowOfData] at h

theorem armToData_armOfData : (r : List (Label × Ty)) → ∀ {ℓ : Label} {d : Data} {i : Fin r.length}
    {y : ArmAt r i}, armOfData r ℓ d = some ⟨i, y⟩ → armToData r i y = .inj ℓ d
  | [], _, _, _, _, h => by simp [armOfData] at h
  | (k, t) :: r, ℓ, d, i, y, h => by
    simp only [armOfData] at h
    split at h
    · rename_i hk
      subst hk
      cases e : ofData t d with
      | none => simp [e] at h
      | some a =>
        simp only [e, Option.map, Option.some.injEq] at h
        cases h
        show Data.inj ℓ (toData t a) = .inj ℓ d
        rw [toData_ofData t e]
    · cases e : armOfData r ℓ d with
      | none => simp [e] at h
      | some a =>
        obtain ⟨j, z⟩ := a
        simp only [e, Option.map, Option.some.injEq] at h
        cases h
        obtain ⟨jv, jh⟩ := j
        exact armToData_armOfData r e
end

-- At a canonical type every arm's data names its own arm (labels are distinct), so `ofData` reads
-- back the value `toData` wrote.
mutual
theorem ofData_toData : (T : Ty) → T.wf = true → ∀ (x : DataAt T), ofData T (toData T x) = some x
  | .nat, _, x => by
    show (if h : UInt64.toNat x < 2 ^ 64 then some (UInt64.ofNatLT (UInt64.toNat x) h) else none) = some x
    rw [dif_pos (UInt64.toNat_lt x)]; rfl
  | .bool, _, x => rfl
  | .bytes, _, x => by
    show (if h : x.val.size ≤ Bounds.bytesMax then some ⟨x.val, h⟩ else none) = some x
    rw [dif_pos x.2]; rfl
  | .fn _ _, _, x => nomatch x
  | .record r, h, x => by
    simp only [Ty.wf, Bool.and_eq_true] at h
    simp only [toData, ofData]; exact rowOfData_rowToData r h.2 x
  | .sum r, h, ⟨i, y⟩ => by
    simp only [Ty.wf, Bool.and_eq_true] at h
    obtain ⟨ℓ, d, A, he, _, hb⟩ := armOfData_armToData r h.1 h.2 i y
    show ofData (.sum r) (armToData r i y) = some ⟨i, y⟩
    rw [he]; exact hb

theorem rowOfData_rowToData : (r : List (Label × Ty)) → Ty.rowWf r = true → ∀ (x : RowAt r),
    rowOfData r (rowToData r x) = some x
  | [], _, () => rfl
  | (ℓ, t) :: r, h, (x, y) => by
    simp only [Ty.rowWf, Bool.and_eq_true] at h
    simp only [rowToData, rowOfData, if_pos, ofData_toData t h.1 x, rowOfData_rowToData r h.2 y]

theorem armOfData_armToData : (r : List (Label × Ty)) → Row.ascending r = true → Ty.rowWf r = true →
    ∀ (i : Fin r.length) (y : ArmAt r i), ∃ ℓ d A, armToData r i y = .inj ℓ d ∧ Row.find? ℓ r = some A ∧
      armOfData r ℓ d = some ⟨i, y⟩
  | [], _, _, i, _ => Fin.elim0 i
  | (k, t) :: r, ha, hw, ⟨0, _⟩, y => by
    simp only [Ty.rowWf, Bool.and_eq_true] at hw
    exact ⟨k, toData t y, t, rfl, by simp [Row.find?],
      by simp only [armOfData, if_true, ofData_toData t hw.1 y]; rfl⟩
  | (k, t) :: r, ha, hw, ⟨i + 1, hi⟩, y => by
    simp only [Ty.rowWf, Bool.and_eq_true] at hw
    obtain ⟨ℓ, d, A, he, hf, hb⟩ := armOfData_armToData r (ascending_tail ha) hw.2 ⟨i, Nat.lt_of_succ_lt_succ hi⟩ y
    have hne : ℓ ≠ k := fun e => String.ne_of_lt (ascending_lt_of_find ha hf) e.symm
    refine ⟨ℓ, d, A, he, by simp [Row.find?, hne, hf], ?_⟩
    simp only [armOfData, hne, if_false, hb, Option.map_some]
    rfl
end

/-! ## One value, one byte string -/

theorem decodeData_eq_ok_iff {T : Ty} {b : ByteArray} {d : Data} :
    decodeData T b = .ok d ↔ encodeData T d = some b := by
  unfold decodeData encodeData
  by_cases hdt : dataTy T = true
  · have hw : T.wf = true := by simp only [dataTy, Bool.and_eq_true] at hdt; exact hdt.1
    have hl : tyWire T = true := by simp only [dataTy, Bool.and_eq_true] at hdt; exact hdt.2
    simp only [hdt, if_true]
    constructor
    · intro h
      cases e : (dataStream T).decode b with
      | error _ => simp [e, Except.map] at h
      | ok x =>
        simp only [e, Except.map, Except.ok.injEq] at h
        subst h
        rw [ofData_toData T hw x]
        simp [(decode_eq_ok_iff (dataStream_lawful T hl)).mp e]
    · intro h
      cases e : ofData T d with
      | none => simp [e] at h
      | some x =>
        simp only [e, Option.map_some, Option.some.injEq] at h
        subst h
        rw [decode_bytes (dataStream_lawful T hl)]
        simp [Except.map, toData_ofData T e]
  · simp [hdt]

end Wire

/-! ## Decoded data conforms -/

mutual
theorem toData_conforms : (T : Ty) → T.wf = true → ∀ (x : Wire.DataAt T), Conforms (Wire.toData T x) T
  | .nat, _, x => .nat (UInt64.toNat_lt x)
  | .bool, _, _ => .bool
  | .bytes, _, x => .bytes x.2
  | .fn _ _, _, x => nomatch x
  | .record r, h, x => by
    simp only [Ty.wf, Bool.and_eq_true] at h
    exact .record (rowToData_conforms r h.2 x)
  | .sum r, h, ⟨i, y⟩ => by
    simp only [Ty.wf, Bool.and_eq_true] at h
    obtain ⟨ℓ, A, d, he, hf, hc⟩ := armToData_conforms r h.1 h.2 i y
    show Conforms (Wire.armToData r i y) (.sum r)
    rw [he]; exact .inj hf hc

theorem rowToData_conforms : (r : List (Label × Ty)) → Ty.rowWf r = true → ∀ (x : Wire.RowAt r),
    RowConforms (Wire.rowToData r x) r
  | [], _, () => .nil
  | (ℓ, t) :: r, h, (x, y) => by
    simp only [Ty.rowWf, Bool.and_eq_true] at h
    exact .cons (toData_conforms t h.1 x) (rowToData_conforms r h.2 y)

theorem armToData_conforms : (r : List (Label × Ty)) → Row.ascending r = true → Ty.rowWf r = true →
    ∀ (i : Fin r.length) (y : Wire.ArmAt r i), ∃ ℓ A d, Wire.armToData r i y = .inj ℓ d ∧
      Row.find? ℓ r = some A ∧ Conforms d A
  | [], _, _, i, _ => Fin.elim0 i
  | (k, t) :: r, _, hw, ⟨0, _⟩, y => by
    simp only [Ty.rowWf, Bool.and_eq_true] at hw
    exact ⟨k, t, Wire.toData t y, rfl, by simp [Row.find?], toData_conforms t hw.1 y⟩
  | (k, t) :: r, ha, hw, ⟨i + 1, hi⟩, y => by
    simp only [Ty.rowWf, Bool.and_eq_true] at hw
    obtain ⟨ℓ, A, d, he, hf, hc⟩ :=
      armToData_conforms r (Wire.ascending_tail ha) hw.2 ⟨i, Nat.lt_of_succ_lt_succ hi⟩ y
    have hne : ℓ ≠ k := fun e => String.ne_of_lt (Wire.ascending_lt_of_find ha hf) e.symm
    exact ⟨ℓ, A, d, he, by simp [Row.find?, hne, hf], hc⟩
end

theorem decodeData_conforms {T : Ty} {b : ByteArray} {d : Data}
    (h : Wire.decodeData T b = .ok d) : Conforms d T := by
  unfold Wire.decodeData at h
  split at h
  · rename_i hdt
    have hw : T.wf = true := by simp only [Wire.dataTy, Bool.and_eq_true] at hdt; exact hdt.1
    cases e : (Wire.dataStream T).decode b with
    | error _ => simp [e, Except.map] at h
    | ok x =>
      simp only [e, Except.map, Except.ok.injEq] at h
      subst h; exact toData_conforms T hw x
  · simp at h

end Nanodregg.Lang
