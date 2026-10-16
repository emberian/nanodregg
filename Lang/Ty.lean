/-
# Lang.Ty — the types of the core: monomorphic, exact, canonical (DECISIONS LANG-3)

No subtyping, no type variables, no quantities: type equality is `=`. The checker requires
canonical rows (strictly ascending labels) at every record literal and every annotation (`wf`);
that every INFERRED type is canonical needs `merge` to keep rows ascending, which is not yet a
theorem. Polymorphism and row-generic mixins are the authoring tool's job: it instantiates
every template before a term reaches the checker.
-/
import Lang.Row

namespace Nanodregg.Lang

inductive Ty
  | nat
  | bool
  | bytes
  | fn (dom cod : Ty)
  | record (row : List (Label × Ty))
  | sum (row : List (Label × Ty))
  deriving Repr, Inhabited

mutual
/-- Structural equality; `DecidableEq Ty` is built on it (deriving does not reach nested rows). -/
def Ty.beq : Ty → Ty → Bool
  | .nat, .nat | .bool, .bool | .bytes, .bytes => true
  | .fn a b, .fn c d => Ty.beq a c && Ty.beq b d
  | .record r, .record s => Ty.rowBeq r s
  | .sum r, .sum s => Ty.rowBeq r s
  | _, _ => false

def Ty.rowBeq : List (Label × Ty) → List (Label × Ty) → Bool
  | [], [] => true
  | (l, a) :: r, (m, b) :: s => decide (l = m) && Ty.beq a b && Ty.rowBeq r s
  | _, _ => false
end

mutual
private theorem Ty.eq_of_beq : (a b : Ty) → Ty.beq a b = true → a = b
  | .nat, .nat, _ | .bool, .bool, _ | .bytes, .bytes, _ => rfl
  | .fn a b, .fn c d, h => by
      simp only [Ty.beq, Bool.and_eq_true] at h
      rw [Ty.eq_of_beq a c h.1, Ty.eq_of_beq b d h.2]
  | .record r, .record s, h => by
      simp only [Ty.beq] at h
      rw [Ty.rowEq_of_rowBeq r s h]
  | .sum r, .sum s, h => by
      simp only [Ty.beq] at h
      rw [Ty.rowEq_of_rowBeq r s h]
  | .nat, .bool, h | .nat, .bytes, h | .nat, .fn _ _, h | .nat, .record _, h | .nat, .sum _, h
  | .bool, .nat, h | .bool, .bytes, h | .bool, .fn _ _, h | .bool, .record _, h | .bool, .sum _, h
  | .bytes, .nat, h | .bytes, .bool, h | .bytes, .fn _ _, h | .bytes, .record _, h
  | .bytes, .sum _, h
  | .fn _ _, .nat, h | .fn _ _, .bool, h | .fn _ _, .bytes, h | .fn _ _, .record _, h
  | .fn _ _, .sum _, h
  | .record _, .nat, h | .record _, .bool, h | .record _, .bytes, h | .record _, .fn _ _, h
  | .record _, .sum _, h
  | .sum _, .nat, h | .sum _, .bool, h | .sum _, .bytes, h | .sum _, .fn _ _, h
  | .sum _, .record _, h => by simp [Ty.beq] at h

private theorem Ty.rowEq_of_rowBeq :
    (r s : List (Label × Ty)) → Ty.rowBeq r s = true → r = s
  | [], [], _ => rfl
  | (l, a) :: r, (m, b) :: s, h => by
      simp only [Ty.rowBeq, Bool.and_eq_true, decide_eq_true_eq] at h
      rw [h.1.1, Ty.eq_of_beq a b h.1.2, Ty.rowEq_of_rowBeq r s h.2]
  | [], _ :: _, h | _ :: _, [], h => by simp [Ty.rowBeq] at h
end

mutual
private theorem Ty.beq_self : (a : Ty) → Ty.beq a a = true
  | .nat | .bool | .bytes => rfl
  | .fn a b => by simp only [Ty.beq, Ty.beq_self a, Ty.beq_self b, Bool.and_self]
  | .record r => by simp only [Ty.beq]; exact Ty.rowBeq_self r
  | .sum r => by simp only [Ty.beq]; exact Ty.rowBeq_self r

private theorem Ty.rowBeq_self : (r : List (Label × Ty)) → Ty.rowBeq r r = true
  | [] => rfl
  | (l, a) :: r => by
      simp only [Ty.rowBeq, Ty.beq_self a, Ty.rowBeq_self r, decide_true, Bool.and_self]
end

instance : DecidableEq Ty := fun a b =>
  if h : Ty.beq a b = true then isTrue (Ty.eq_of_beq a b h)
  else isFalse (fun e => h (e ▸ Ty.beq_self a))

mutual
/-- Every row in the type is canonical. -/
def Ty.wf : Ty → Bool
  | .nat | .bool | .bytes => true
  | .fn a b => a.wf && b.wf
  | .record r => Row.ascending r && Ty.rowWf r
  | .sum r => Row.ascending r && Ty.rowWf r

def Ty.rowWf : List (Label × Ty) → Bool
  | [] => true
  | (_, t) :: rest => t.wf && Ty.rowWf rest
end

mutual
/-- First-order data: what an object's state, a method's arguments and a result can be. -/
def Ty.isData : Ty → Bool
  | .nat | .bool | .bytes => true
  | .fn _ _ => false
  | .record r => Ty.rowData r
  | .sum r => Ty.rowData r

def Ty.rowData : List (Label × Ty) → Bool
  | [] => true
  | (_, t) :: rest => t.isData && Ty.rowData rest
end

end Nanodregg.Lang
