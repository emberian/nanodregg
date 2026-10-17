/-
# Lang.Proofs.Meaning — reading a term's meaning off its `BigStep` derivation

Inversion lemmas for the reference semantics (one per term former a law uses), and the
data-level view of a law's environment: a state or request is `Data` put into the machine with
`toVal`, so a field selection means the field's data (`bigStep_getVar`). Everything here is about
`BigStep`, never about the machine; `Lang.Proofs.Agree` carries a machine result to a meaning.
-/
import Lang.Proofs.BigStep
import Lang.Data

namespace Nanodregg.Lang

variable {lib : List Term} {env : Env}

/-! ## Inversion -/

theorem bigStep_var_inv {i : Nat} {r : Except Fault Val} (h : BigStep lib env (.var i) r) :
    ∃ v, env[i]? = some v ∧ r = .ok v := by
  cases h with | var h => exact ⟨_, h, rfl⟩

theorem bigStep_var_ok {i : Nat} {v : Val} (h : BigStep lib env (.var i) (.ok v)) : env[i]? = some v := by
  cases h with | var h => exact h

theorem bigStep_nat_inv {n : Nat} {r : Except Fault Val} (h : BigStep lib env (.nat n) r) :
    r = .ok (.nat n) := by cases h; rfl

theorem bigStep_bool_inv {b : Bool} {r : Except Fault Val} (h : BigStep lib env (.bool b) r) :
    r = .ok (.bool b) := by cases h; rfl

theorem bigStep_bytes_inv {s : ByteArray} {r : Except Fault Val} (h : BigStep lib env (.bytes s) r) :
    r = .ok (.bytes s) := by cases h; rfl

theorem bigStep_digest_inv {s : ByteArray} {r : Except Fault Val} (h : BigStep lib env (.digest s) r) :
    r = .ok (.digest s) := by cases h; rfl

/-- A conditional with a value: the condition was a boolean and the taken branch has the value. -/
theorem bigStep_ite_ok {c a b : Term} {v : Val} (h : BigStep lib env (.ite c a b) (.ok v)) :
    (BigStep lib env c (.ok (.bool true)) ∧ BigStep lib env a (.ok v)) ∨
    (BigStep lib env c (.ok (.bool false)) ∧ BigStep lib env b (.ok v)) := by
  cases h with
  | iteT hc ha => exact .inl ⟨hc, ha⟩
  | iteF hc hb => exact .inr ⟨hc, hb⟩

/-- A primitive with a value: both operands had values and `primEval` gave it. -/
theorem bigStep_prim_ok {p : Prim} {a b : Term} {v : Val} (h : BigStep lib env (.prim p a b) (.ok v)) :
    ∃ x y, BigStep lib env a (.ok x) ∧ BigStep lib env b (.ok y) ∧ primEval p x y = .ok v := by
  generalize hr : (Except.ok v : Except Fault Val) = r at h
  cases h with
  | prim ha hb _ => exact ⟨_, _, ha, hb, by first | exact hr.symm | rfl⟩
  | primL _ => cases hr
  | primR _ _ => cases hr

theorem bigStep_inj_ok {A : Ty} {ℓ : Label} {t : Term} {v : Val}
    (h : BigStep lib env (.inj A ℓ t) (.ok v)) : ∃ w, BigStep lib env t (.ok w) ∧ v = .inj ℓ w := by
  cases h with | inj ht => exact ⟨_, ht, rfl⟩

/-- A case with a value: the scrutinee was an injection, its label's arm ran on its payload. -/
theorem bigStep_case_ok {t : Term} {arms : List (Label × Term)} {v : Val}
    (h : BigStep lib env (.case t arms) (.ok v)) :
    ∃ ℓ w body, BigStep lib env t (.ok (.inj ℓ w)) ∧ Row.find? ℓ arms = some body ∧
      BigStep lib (w :: env) body (.ok v) := by
  cases h with | case ht hf hb => exact ⟨_, _, _, ht, hf, hb⟩

/-- Applying a closed `λ` to a variable: the body ran with the variable's value bound. -/
theorem bigStep_app_ok {f : Term} {a : Term} {v : Val}
    (h : BigStep lib env (.app f a) (.ok v)) :
    ∃ body cenv w, BigStep lib env f (.ok (.clo body cenv)) ∧ BigStep lib env a (.ok w) ∧
      BigStep lib (w :: cenv) body (.ok v) := by
  cases h with | app hf ha hb => exact ⟨_, _, _, hf, ha, hb⟩

/-! ## Data in the environment -/

theorem find_rowToVal {ℓ : Label} : ∀ {fs : List (Label × Data)} {t : Term} {e : Env},
    Row.find? ℓ (Data.rowToVal fs) = some (t, e) → ∃ x, Row.find? ℓ fs = some x ∧ t = .var 0 ∧ e = [x.toVal]
  | [], _, _, h => by simp [Data.rowToVal, Row.find?] at h
  | (k, d) :: fs, t, e, h => by
    simp only [Data.rowToVal, Row.find?] at h ⊢
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨d, by simp [*], rfl, rfl⟩
    · rw [if_neg (by assumption)]; exact find_rowToVal h

/-- Selecting a field of record data bound at `var i` means the field's data. -/
theorem bigStep_getVar {i : Nat} {d : Data} {ℓ : Label} {v : Val} (hi : env[i]? = some d.toVal)
    (h : BigStep lib env (.get (.var i) ℓ) (.ok v)) : ∃ x, d.field ℓ = some x ∧ v = x.toVal := by
  cases h with
  | get ht hs =>
    obtain ⟨w, hw, hv⟩ := bigStep_var_inv ht
    rw [hi] at hw; cases hv; cases hw
    cases d with
    | record fs =>
      cases hs with
      | field hf hb =>
        obtain ⟨x, hx, rfl, rfl⟩ := find_rowToVal hf
        obtain ⟨u, hu, hu'⟩ := bigStep_var_inv hb
        simp at hu; subst hu; cases hu'
        exact ⟨x, hx, rfl⟩
    | nat _ | bool _ | bytes _ | digest _ | inj _ _ => cases hs

theorem Data.toVal_nat {x : Data} {n : Nat} (h : x.toVal = .nat n) : x = .nat n := by
  cases x <;> simp [Data.toVal] at h <;> simp [h]

theorem Data.toVal_bool {x : Data} {b : Bool} (h : x.toVal = .bool b) : x = .bool b := by
  cases x <;> simp [Data.toVal] at h <;> simp [h]

theorem Data.toVal_bytes {x : Data} {s : ByteArray} (h : x.toVal = .bytes s) : x = .bytes s := by
  cases x <;> simp [Data.toVal] at h <;> simp [h]

theorem Data.toVal_digest {x : Data} {s : ByteArray} (h : x.toVal = .digest s) : x = .digest s := by
  cases x <;> simp [Data.toVal] at h <;> simp [h]

theorem Data.toVal_inj {x : Data} {ℓ : Label} {w : Val} (h : x.toVal = .inj ℓ w) :
    ∃ y, x = .inj ℓ y ∧ w = y.toVal := by
  cases x <;> simp [Data.toVal] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨_, rfl, rfl⟩

end Nanodregg.Lang
