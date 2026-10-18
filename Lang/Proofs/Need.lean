/-
# Lang.Proofs.Need — the required count IS the size of the reference derivation

`Derives lib env t r n` is `BigStep lib env t r` carrying the number `n` of rule instances in the
derivation. Every constructor is a `BigStep`/`Sel`/`Ext` rule and adds exactly 1 for itself to its
premises' sizes. `derives_bigStep` and `bigStep_derives` show that erasing the size gives `BigStep`
and that every `BigStep` derivation has a size. `derives_unique` shows the size is a function of
the term: a meaning has one derivation size. `need_derives` shows that `Lang.Sim.Need.need`
returns that size, and nothing else. The machine appears nowhere above.

Extraction: `Forces lib T v n` holds when the derivations extraction must perform at type `T`
from `v` (the unfoldings of knots, then each record field in row order) have sizes summing to
`n`. `forces_le` ties it to `Machine.extract`: the deployed extraction forces those suspensions and
pays at least their sizes. `forces_unique` shows the sum is one number, and `needExtract_forces` is its
counter's spec.

`requiredOf_spec` and `runMeasured_setup` give the whole count: for an invoke that `runMeasured`
admits, `requiredOf` counts the derivation of the very value the deployed machine computed
(`required_counts_the_run`), plus the forced suspensions at the method's result type.
`required_lt_ticks`: the count is below the ticks charged, so the ratio is above 1.
`runBy_step` says the plant's loop is the deployed loop. Teeth: concrete sizes, a size that is
not one, and the plant costing two more ticks per application.
-/
import Lang.Sim.Need
import Lang.Proofs.Agree
import Lang.Proofs.Derives
import Lang.Proofs.Complete

namespace Nanodregg.Lang

open Nanodregg.Kernel
open Nanodregg.Kernel.Receive

variable {lib : List Term}

mutual
/-- **One size per meaning**: two sized derivations of one term agree on the meaning AND the size. -/
theorem derives_unique : ∀ {env : Env} {t : Term} {r r' : Except Fault Val} {n n' : Nat},
    Derives lib env t r n → Derives lib env t r' n' → r = r' ∧ n = n'
  | _, _, _, _, _, _, .var h, h' => by
    cases h' with | var h2 => rw [h] at h2; cases h2; exact ⟨rfl, rfl⟩
  | _, _, _, _, _, _, .lam, h' => by cases h'; exact ⟨rfl, rfl⟩
  | _, _, _, _, _, _, .app hf ha hb, h' => by
    cases h' with
    | app hf' ha' hb' =>
      obtain ⟨h1, rfl⟩ := derives_unique hf hf'; cases h1
      obtain ⟨h2, rfl⟩ := derives_unique ha ha'; cases h2
      obtain ⟨hr, rfl⟩ := derives_unique hb hb'; exact ⟨hr, rfl⟩
    | appF hf' => cases (derives_unique hf hf').1
    | appA _ ha' => cases (derives_unique ha ha').1
  | _, _, _, _, _, _, .appF hf, h' => by
    cases h' with
    | app hf' _ _ => cases (derives_unique hf hf').1
    | appF hf' => obtain ⟨hr, rfl⟩ := derives_unique hf hf'; exact ⟨hr, rfl⟩
    | appA hf' _ => cases (derives_unique hf hf').1
  | _, _, _, _, _, _, .appA hf ha, h' => by
    cases h' with
    | app _ ha' _ => cases (derives_unique ha ha').1
    | appF hf' => cases (derives_unique hf hf').1
    | appA hf' ha' =>
      obtain ⟨_, rfl⟩ := derives_unique hf hf'
      obtain ⟨hr, rfl⟩ := derives_unique ha ha'; exact ⟨hr, rfl⟩
  | _, _, _, _, _, _, .fix ht, h' => by
    cases h' with
    | fix ht' => obtain ⟨h1, rfl⟩ := derives_unique ht ht'; cases h1; exact ⟨rfl, rfl⟩
    | fixE ht' => cases (derives_unique ht ht').1
  | _, _, _, _, _, _, .fixE ht, h' => by
    cases h' with
    | fix ht' => cases (derives_unique ht ht').1
    | fixE ht' => obtain ⟨hr, rfl⟩ := derives_unique ht ht'; exact ⟨hr, rfl⟩
  | _, _, _, _, _, _, .nat, h' | _, _, _, _, _, _, .bool, h' | _, _, _, _, _, _, .bytes, h'
  | _, _, _, _, _, _, .digest, h' | _, _, _, _, _, _, .refuse, h'
  | _, _, _, _, _, _, .record, h' => by cases h'; exact ⟨rfl, rfl⟩
  | _, _, _, _, _, _, .prim ha hb _, h' => by
    cases h' with
    | prim ha' hb' _ =>
      obtain ⟨h1, rfl⟩ := derives_unique ha ha'; cases h1
      obtain ⟨h2, rfl⟩ := derives_unique hb hb'; cases h2; exact ⟨rfl, rfl⟩
    | primL ha' => cases (derives_unique ha ha').1
    | primR _ hb' => cases (derives_unique hb hb').1
  | _, _, _, _, _, _, .primL ha, h' => by
    cases h' with
    | prim ha' _ _ => cases (derives_unique ha ha').1
    | primL ha' => obtain ⟨hr, rfl⟩ := derives_unique ha ha'; exact ⟨hr, rfl⟩
    | primR ha' _ => cases (derives_unique ha ha').1
  | _, _, _, _, _, _, .primR ha hb, h' => by
    cases h' with
    | prim _ hb' _ => cases (derives_unique hb hb').1
    | primL ha' => cases (derives_unique ha ha').1
    | primR ha' hb' =>
      obtain ⟨_, rfl⟩ := derives_unique ha ha'
      obtain ⟨hr, rfl⟩ := derives_unique hb hb'; exact ⟨hr, rfl⟩
  | _, _, _, _, _, _, .get ht hs, h' => by
    cases h' with
    | get ht' hs' =>
      obtain ⟨h1, rfl⟩ := derives_unique ht ht'; cases h1
      obtain ⟨hr, rfl⟩ := dsel_unique hs hs'; exact ⟨hr, rfl⟩
    | getE ht' => cases (derives_unique ht ht').1
  | _, _, _, _, _, _, .getE ht, h' => by
    cases h' with
    | get ht' _ => cases (derives_unique ht ht').1
    | getE ht' => obtain ⟨hr, rfl⟩ := derives_unique ht ht'; exact ⟨hr, rfl⟩
  | _, _, _, _, _, _, .extend ht hx, h' => by
    cases h' with
    | extend ht' hx' =>
      obtain ⟨h1, rfl⟩ := derives_unique ht ht'; cases h1
      obtain ⟨hr, rfl⟩ := dext_unique hx hx'; exact ⟨hr, rfl⟩
    | extendE ht' => cases (derives_unique ht ht').1
  | _, _, _, _, _, _, .extendE ht, h' => by
    cases h' with
    | extend ht' _ => cases (derives_unique ht ht').1
    | extendE ht' => obtain ⟨hr, rfl⟩ := derives_unique ht ht'; exact ⟨hr, rfl⟩
  | _, _, _, _, _, _, .inj ht, h' => by
    cases h' with
    | inj ht' => obtain ⟨h1, rfl⟩ := derives_unique ht ht'; cases h1; exact ⟨rfl, rfl⟩
    | injE ht' => cases (derives_unique ht ht').1
  | _, _, _, _, _, _, .injE ht, h' => by
    cases h' with
    | inj ht' => cases (derives_unique ht ht').1
    | injE ht' => obtain ⟨hr, rfl⟩ := derives_unique ht ht'; exact ⟨hr, rfl⟩
  | _, _, _, _, _, _, .case ht hf hb, h' => by
    cases h' with
    | case ht' hf' hb' =>
      obtain ⟨h1, rfl⟩ := derives_unique ht ht'; cases h1; rw [hf] at hf'; cases hf'
      obtain ⟨hr, rfl⟩ := derives_unique hb hb'; exact ⟨hr, rfl⟩
    | caseE ht' => cases (derives_unique ht ht').1
  | _, _, _, _, _, _, .caseE ht, h' => by
    cases h' with
    | case ht' _ _ => cases (derives_unique ht ht').1
    | caseE ht' => obtain ⟨hr, rfl⟩ := derives_unique ht ht'; exact ⟨hr, rfl⟩
  | _, _, _, _, _, _, .iteT hc ha, h' => by
    cases h' with
    | iteT hc' ha' =>
      obtain ⟨_, rfl⟩ := derives_unique hc hc'
      obtain ⟨hr, rfl⟩ := derives_unique ha ha'; exact ⟨hr, rfl⟩
    | iteF hc' _ => cases (derives_unique hc hc').1
    | iteE hc' => cases (derives_unique hc hc').1
  | _, _, _, _, _, _, .iteF hc hb, h' => by
    cases h' with
    | iteT hc' _ => cases (derives_unique hc hc').1
    | iteF hc' hb' =>
      obtain ⟨_, rfl⟩ := derives_unique hc hc'
      obtain ⟨hr, rfl⟩ := derives_unique hb hb'; exact ⟨hr, rfl⟩
    | iteE hc' => cases (derives_unique hc hc').1
  | _, _, _, _, _, _, .iteE hc, h' => by
    cases h' with
    | iteT hc' _ => cases (derives_unique hc hc').1
    | iteF hc' _ => cases (derives_unique hc hc').1
    | iteE hc' => obtain ⟨hr, rfl⟩ := derives_unique hc hc'; exact ⟨hr, rfl⟩
  | _, _, _, _, _, _, .ref hi hb, h' => by
    cases h' with
    | ref hi' hb' =>
      rw [hi] at hi'; cases hi'; obtain ⟨hr, rfl⟩ := derives_unique hb hb'; exact ⟨hr, rfl⟩

theorem dsel_unique : ∀ {v : Val} {ℓ : Label} {r r' : Except Fault Val} {n n' : Nat},
    DSel lib v ℓ r n → DSel lib v ℓ r' n' → r = r' ∧ n = n'
  | _, _, _, _, _, _, .field hf hb, h' => by
    cases h' with
    | field hf' hb' =>
      rw [hf] at hf'; cases hf'; obtain ⟨hr, rfl⟩ := derives_unique hb hb'; exact ⟨hr, rfl⟩
  | _, _, _, _, _, _, .knot hb hs, h' => by
    cases h' with
    | knot hb' hs' =>
      obtain ⟨h1, rfl⟩ := derives_unique hb hb'; cases h1
      obtain ⟨hr, rfl⟩ := dsel_unique hs hs'; exact ⟨hr, rfl⟩
    | knotE hb' => cases (derives_unique hb hb').1
  | _, _, _, _, _, _, .knotE hb, h' => by
    cases h' with
    | knot hb' _ => cases (derives_unique hb hb').1
    | knotE hb' => obtain ⟨hr, rfl⟩ := derives_unique hb hb'; exact ⟨hr, rfl⟩

theorem dext_unique : ∀ {v : Val} {fs : List (Label × Term)} {env : Env} {r r' : Except Fault Val}
    {n n' : Nat}, DExt lib v fs env r n → DExt lib v fs env r' n' → r = r' ∧ n = n'
  | _, _, _, _, _, _, _, .record, h' => by cases h'; exact ⟨rfl, rfl⟩
  | _, _, _, _, _, _, _, .knot hb hx, h' => by
    cases h' with
    | knot hb' hx' =>
      obtain ⟨h1, rfl⟩ := derives_unique hb hb'; cases h1
      obtain ⟨hr, rfl⟩ := dext_unique hx hx'; exact ⟨hr, rfl⟩
    | knotE hb' => cases (derives_unique hb hb').1
  | _, _, _, _, _, _, _, .knotE hb, h' => by
    cases h' with
    | knot hb' _ => cases (derives_unique hb hb').1
    | knotE hb' => obtain ⟨hr, rfl⟩ := derives_unique hb hb'; exact ⟨hr, rfl⟩
end

/-! ## `need` computes exactly that size -/

theorem meaningful_ne {r : Except Fault Val} (h : Need.meaningful r = true) : r ≠ .error .stuck := by
  rintro rfl; simp [Need.meaningful] at h

/-- **The counter's spec**: what `need` returns is a sized derivation, so its count is THE size of
the term's derivation (`derives_unique`). -/
theorem need_derives_all : ∀ f : Nat,
    (∀ env t r n, Need.need lib f env t = some (r, n) → Derives lib env t r n) ∧
    (∀ v ℓ r n, Need.needSel lib f v ℓ = some (r, n) → DSel lib v ℓ r n) ∧
    (∀ v fs env r n, Need.needExt lib f v fs env = some (r, n) → DExt lib v fs env r n)
  | 0 => ⟨by simp [Need.need], by simp [Need.needSel], by simp [Need.needExt]⟩
  | f + 1 => by
    obtain ⟨ih, ihs, ihx⟩ := need_derives_all f
    refine ⟨?_, ?_, ?_⟩
    · intro env t r n h
      cases t with
      | var i =>
        simp only [Need.need] at h; split at h
        · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
          exact .var ‹_›
        · cases h
      | lam A b =>
        simp only [Need.need, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; exact .lam
      | app fn a =>
        simp only [Need.need] at h
        repeat' split at h
        all_goals first
          | (simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
             first
              | exact .app (ih _ _ _ _ ‹_›) (ih _ _ _ _ ‹_›) (ih _ _ _ _ ‹_›)
              | exact .appA (ih _ _ _ _ ‹_›) (ih _ _ _ _ ‹_›)
              | exact .appF (ih _ _ _ _ ‹_›))
          | cases h
      | fix t =>
        simp only [Need.need] at h
        repeat' split at h
        all_goals first
          | (simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
             first | exact .fix (ih _ _ _ _ ‹_›) | exact .fixE (ih _ _ _ _ ‹_›))
          | cases h
      | nat k =>
        simp only [Need.need, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; exact .nat
      | bool b =>
        simp only [Need.need, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; exact .bool
      | bytes s =>
        simp only [Need.need, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; exact .bytes
      | digest s =>
        simp only [Need.need, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; exact .digest
      | refuse T w =>
        simp only [Need.need, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; exact .refuse
      | prim p a b =>
        simp only [Need.need] at h
        repeat' split at h
        all_goals first
          | (simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
             first
              | exact .prim (ih _ _ _ _ ‹_›) (ih _ _ _ _ ‹_›) (meaningful_ne ‹_›)
              | exact .primR (ih _ _ _ _ ‹_›) (ih _ _ _ _ ‹_›)
              | exact .primL (ih _ _ _ _ ‹_›))
          | cases h
      | record fs =>
        simp only [Need.need, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; exact .record
      | get t ℓ =>
        simp only [Need.need] at h
        repeat' split at h
        all_goals first
          | (simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
             first
              | exact .get (ih _ _ _ _ ‹_›) (ihs _ _ _ _ ‹_›)
              | exact .getE (ih _ _ _ _ ‹_›))
          | cases h
      | extend t fs =>
        simp only [Need.need] at h
        repeat' split at h
        all_goals first
          | (simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
             first
              | exact .extend (ih _ _ _ _ ‹_›) (ihx _ _ _ _ _ ‹_›)
              | exact .extendE (ih _ _ _ _ ‹_›))
          | cases h
      | inj A ℓ t =>
        simp only [Need.need] at h
        repeat' split at h
        all_goals first
          | (simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
             first | exact .inj (ih _ _ _ _ ‹_›) | exact .injE (ih _ _ _ _ ‹_›))
          | cases h
      | case t arms =>
        simp only [Need.need] at h
        repeat' split at h
        all_goals first
          | (simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
             first
              | exact .case (ih _ _ _ _ ‹_›) ‹_› (ih _ _ _ _ ‹_›)
              | exact .caseE (ih _ _ _ _ ‹_›))
          | cases h
      | ite c a b =>
        simp only [Need.need] at h
        repeat' split at h
        all_goals first
          | (simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
             first
              | exact .iteT (ih _ _ _ _ ‹_›) (ih _ _ _ _ ‹_›)
              | exact .iteF (ih _ _ _ _ ‹_›) (ih _ _ _ _ ‹_›)
              | exact .iteE (ih _ _ _ _ ‹_›))
          | cases h
      | ref i =>
        simp only [Need.need] at h
        repeat' split at h
        all_goals first
          | (simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
             exact .ref ‹_› (ih _ _ _ _ ‹_›))
          | cases h
    · intro v ℓ r n h
      cases v <;> simp only [Need.needSel] at h
      repeat' split at h
      all_goals first
        | (simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
           first
            | exact .field ‹_› (ih _ _ _ _ ‹_›)
            | exact .knot (ih _ _ _ _ ‹_›) (ihs _ _ _ _ ‹_›)
            | exact .knotE (ih _ _ _ _ ‹_›))
        | cases h
    · intro v fs env r n h
      cases v <;> simp only [Need.needExt] at h
      repeat' split at h
      all_goals first
        | (simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
           first
            | exact .record
            | exact .knot (ih _ _ _ _ ‹_›) (ihx _ _ _ _ _ ‹_›)
            | exact .knotE (ih _ _ _ _ ‹_›))
        | cases h

theorem need_derives {f : Nat} {env : Env} {t : Term} {r : Except Fault Val} {n : Nat}
    (h : Need.need lib f env t = some (r, n)) : Derives lib env t r n :=
  (need_derives_all f).1 env t r n h

/-! ## Extraction: the derivations of the suspensions it forces -/

/-- Unfolding knots until a record appears (`Machine.unknot`): the unfoldings' sizes, summed. -/
inductive Unknots (lib : List Term) : Val → List (Label × (Term × Env)) → Nat → Prop
  | record {fs} : Unknots lib (.record fs) fs 0
  | knot {body env v fs n m} : Derives lib (.knot body env :: env) body (.ok v) n →
      Unknots lib v fs m → Unknots lib (.knot body env) fs (n + m)

mutual
/-- The derivations extraction must perform at type `T` from `v`: unfold knots until a record
appears, then each field's suspension in row order, then inside each field's value. The sizes
are summed. It is defined independently of the machine; `extract_forces` (every completed
extraction has a `Forces`) and `forces_le` (extraction pays at least its size) tie it to
`Machine.extract`. `forces_unique` shows the size is one number. -/
inductive Forces (lib : List Term) : Ty → Val → Nat → Prop
  | nat {k} : Forces lib .nat (.nat k) 0
  | bool {b} : Forces lib .bool (.bool b) 0
  | bytes {s} : Forces lib .bytes (.bytes s) 0
  | digest {s} : Forces lib .digest (.digest s) 0
  | record {row v fs n m} : Unknots lib v fs n → ForcesRow lib row fs m →
      Forces lib (.record row) v (n + m)
  | sum {row ℓ w A n} : Row.find? ℓ row = some A → Forces lib A w n →
      Forces lib (.sum row) (.inj ℓ w) n

inductive ForcesRow (lib : List Term) : List (Label × Ty) → List (Label × (Term × Env)) → Nat → Prop
  | nil : ForcesRow lib [] [] 0
  | cons {ℓ A row t env fs v n m k} : Derives lib env t (.ok v) n → Forces lib A v m →
      ForcesRow lib row fs k → ForcesRow lib ((ℓ, A) :: row) ((ℓ, (t, env)) :: fs) (n + m + k)
end

theorem unknots_unique {v : Val} {fs fs' : List (Label × (Term × Env))} {n n' : Nat}
    (h : Unknots lib v fs n) (h' : Unknots lib v fs' n') : fs = fs' ∧ n = n' := by
  induction h generalizing fs' n' with
  | record => cases h'; exact ⟨rfl, rfl⟩
  | knot hb _ ih =>
    cases h' with
    | knot hb' hu' =>
      obtain ⟨h1, rfl⟩ := derives_unique hb hb'; cases h1
      obtain ⟨rfl, rfl⟩ := ih hu'; exact ⟨rfl, rfl⟩

mutual
/-- **One size per extraction**: what extraction must force at `T` from `v` has one total size. -/
theorem forces_unique : ∀ {T : Ty} {v : Val} {n n' : Nat},
    Forces lib T v n → Forces lib T v n' → n = n'
  | _, _, _, _, .nat, h' => by cases h'; rfl
  | _, _, _, _, .bool, h' => by cases h'; rfl
  | _, _, _, _, .bytes, h' => by cases h'; rfl
  | _, _, _, _, .digest, h' => by cases h'; rfl
  | _, _, _, _, .record hu hr, h' => by
    cases h' with
    | record hu' hr' =>
      obtain ⟨rfl, rfl⟩ := unknots_unique hu hu'
      rw [forcesRow_unique hr hr']
  | _, _, _, _, .sum hA hf, h' => by
    cases h' with
    | sum hA' hf' => rw [hA] at hA'; cases hA'; exact forces_unique hf hf'

theorem forcesRow_unique : ∀ {row : List (Label × Ty)} {fs : List (Label × (Term × Env))} {n n' : Nat},
    ForcesRow lib row fs n → ForcesRow lib row fs n' → n = n'
  | _, _, _, _, .nil, h' => by cases h'; rfl
  | _, _, _, _, .cons hd hf hr, h' => by
    cases h' with
    | cons hd' hf' hr' =>
      obtain ⟨h1, rfl⟩ := derives_unique hd hd'; cases h1
      rw [forces_unique hf hf', forcesRow_unique hr hr']
end

theorem needForce_derives {fuel : Nat} {t : Term} {env : Env} {v : Val} {n : Nat}
    (h : Need.needForce lib fuel t env = some (v, n)) : Derives lib env t (.ok v) n := by
  simp only [Need.needForce] at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
    exact need_derives ‹_›
  · cases h

theorem needUnknot_unknots {fuel : Nat} : ∀ (rounds : Nat) {v : Val} {fs : List (Label × (Term × Env))}
    {n : Nat}, Need.needUnknot lib fuel rounds v = some (fs, n) → Unknots lib v fs n
  | rounds, .record gs, fs, n, h => by
    cases rounds <;> simp only [Need.needUnknot, Option.some.injEq, Prod.mk.injEq] at h <;>
      obtain ⟨rfl, rfl⟩ := h <;> exact .record
  | 0, .knot _ _, _, _, h => by simp [Need.needUnknot] at h
  | r + 1, .knot body env, fs, n, h => by
    simp only [Need.needUnknot] at h
    repeat' split at h
    all_goals first
      | (simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
         exact .knot (needForce_derives ‹_›) (needUnknot_unknots r ‹_›))
      | cases h
  | _, .nat _, _, _, h | _, .bool _, _, _, h | _, .bytes _, _, _, h | _, .digest _, _, _, h | _, .clo _ _, _, _, h
  | _, .inj _ _, _, _, h => by cases ‹Nat› <;> simp [Need.needUnknot] at h

mutual
theorem needExtract_forces {fuel : Nat} : ∀ (T : Ty) {v : Val} {n : Nat},
    Need.needExtract lib fuel T v = some n → Forces lib T v n
  | .nat, .nat _, n, h => by simp only [Need.needExtract, Option.some.injEq] at h; subst h; exact .nat
  | .bool, .bool _, n, h => by simp only [Need.needExtract, Option.some.injEq] at h; subst h; exact .bool
  | .bytes, .bytes _, n, h => by simp only [Need.needExtract, Option.some.injEq] at h; subst h; exact .bytes
  | .digest, .digest _, n, h => by simp only [Need.needExtract, Option.some.injEq] at h; subst h; exact .digest
  | .record row, v, n, h => by
    simp only [Need.needExtract] at h
    repeat' split at h
    all_goals first
      | (simp only [Option.some.injEq] at h; subst h
         exact .record (needUnknot_unknots _ ‹_›) (needExtractRow_forces row ‹_›))
      | cases h
  | .sum row, .inj ℓ w, n, h => by
    simp only [Need.needExtract] at h
    obtain ⟨A, hA, hf⟩ := needExtractArm_forces row h
    exact .sum hA hf
  | .nat, .bool _, _, h | .nat, .bytes _, _, h | .nat, .digest _, _, h | .nat, .clo _ _, _, h
  | .nat, .record _, _, h | .nat, .knot _ _, _, h | .nat, .inj _ _, _, h
  | .bool, .nat _, _, h | .bool, .bytes _, _, h | .bool, .digest _, _, h | .bool, .clo _ _, _, h
  | .bool, .record _, _, h | .bool, .knot _ _, _, h | .bool, .inj _ _, _, h
  | .bytes, .nat _, _, h | .bytes, .bool _, _, h | .bytes, .digest _, _, h | .bytes, .clo _ _, _, h
  | .bytes, .record _, _, h | .bytes, .knot _ _, _, h | .bytes, .inj _ _, _, h
  | .digest, .nat _, _, h | .digest, .bool _, _, h | .digest, .bytes _, _, h | .digest, .clo _ _, _, h
  | .digest, .record _, _, h | .digest, .knot _ _, _, h | .digest, .inj _ _, _, h
  | .sum _, .nat _, _, h | .sum _, .bool _, _, h | .sum _, .bytes _, _, h | .sum _, .digest _, _, h
  | .sum _, .clo _ _, _, h | .sum _, .record _, _, h | .sum _, .knot _ _, _, h
  | .fn _ _, _, _, h => by simp [Need.needExtract] at h

theorem needExtractArm_forces {fuel : Nat} : ∀ (row : List (Label × Ty)) {ℓ : Label} {w : Val} {n : Nat},
    Need.needExtractArm lib fuel row ℓ w = some n → ∃ A, Row.find? ℓ row = some A ∧ Forces lib A w n
  | [], _, _, _, h => by simp [Need.needExtractArm] at h
  | (k, A) :: row, ℓ, w, n, h => by
    simp only [Need.needExtractArm] at h
    split at h
    · exact ⟨A, by simp [Row.find?, *], needExtract_forces A h⟩
    · obtain ⟨B, hB, hf⟩ := needExtractArm_forces row h
      exact ⟨B, by simp [Row.find?, *], hf⟩

theorem needExtractRow_forces {fuel : Nat} : ∀ (row : List (Label × Ty))
    {fs : List (Label × (Term × Env))} {n : Nat},
    Need.needExtractRow lib fuel row fs = some n → ForcesRow lib row fs n
  | [], [], n, h => by simp only [Need.needExtractRow, Option.some.injEq] at h; subst h; exact .nil
  | [], _ :: _, _, h => by simp [Need.needExtractRow] at h
  | _ :: _, [], _, h => by simp [Need.needExtractRow] at h
  | (ℓ, A) :: row, (ℓ', (t, env)) :: fs, n, h => by
    simp only [Need.needExtractRow] at h
    repeat' split at h
    all_goals first
      | (simp only [Option.some.injEq] at h; subst h; subst ‹ℓ = ℓ'›
         exact .cons (needForce_derives ‹_›) (needExtract_forces A ‹_›) (needExtractRow_forces row ‹_›))
      | cases h
end

/-! ## The plant's loop is the deployed loop -/

/-! ## Extraction pays at least what it requires (`Forces` is what `Machine.extract` forces)

`force_lt`: a forced suspension whose meaning has a derivation of `n` rule instances leaves less
than `fuel - n`. `unknot_le` and `forces_le`: the machine's unfolding and extraction force exactly
the suspensions `Unknots`/`Forces` name (the same field rows, the same values, by determinism),
and spend at least their sizes. So `Forces` is not only a definition of what extraction requires:
the deployed extraction performs those derivations and pays for each. -/

theorem force_lt {fuel fuel' n : Nat} {t : Term} {env : Env} {v v' : Val}
    (h : (Machine.mk lib).force fuel t env = .ok (v, fuel')) (hd : Derives lib env t (.ok v') n) :
    v' = v ∧ n + fuel' < fuel := by
  unfold Machine.force at h
  split at h
  · rename_i w used hr
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hv := bigStep_deterministic (derives_bigStep hd) (run_bigStep hr)
    simp only [Except.ok.injEq] at hv
    obtain ⟨hn, hu⟩ := derives_lt_used hd hr
    exact ⟨hv, by omega⟩
  · cases h

theorem unknot_le {v : Val} {fs : List (Label × (Term × Env))} {n : Nat} (hu : Unknots lib v fs n) :
    ∀ {rounds fuel fuel' : Nat} {fs' : List (Label × (Term × Env))},
      (Machine.mk lib).unknot rounds fuel v = .ok (fs', fuel') → fs' = fs ∧ n + fuel' ≤ fuel := by
  induction hu with
  | record =>
    intro rounds fuel fuel' fs' h
    cases rounds <;> simp only [Machine.unknot, Except.ok.injEq, Prod.mk.injEq] at h <;>
      obtain ⟨rfl, rfl⟩ := h <;> exact ⟨rfl, by omega⟩
  | knot hd _ ih =>
    intro rounds fuel fuel' fs' h
    cases rounds with
    | zero => simp [Machine.unknot] at h
    | succ r =>
      simp only [Machine.unknot] at h
      split at h
      · rename_i v1 f1 hf
        obtain ⟨rfl, hlt⟩ := force_lt hf hd
        obtain ⟨rfl, hle⟩ := ih h
        exact ⟨rfl, by omega⟩
      · cases h

theorem extractArm_find {fuel : Nat} {w : Val} : ∀ {row : List (Label × Ty)} {ℓ : Label} {A : Ty},
    Row.find? ℓ row = some A → (Machine.mk lib).extractArm row ℓ fuel w = (Machine.mk lib).extract A fuel w
  | [], _, _, h => by cases h
  | (k, B) :: row, ℓ, A, h => by
    simp only [Row.find?] at h
    simp only [Machine.extractArm]
    split
    · rename_i hk; rw [if_pos hk] at h; cases h; rfl
    · rename_i hk; rw [if_neg hk] at h; exact extractArm_find h

mutual
theorem forces_le : ∀ {T : Ty} {v : Val} {n : Nat}, Forces lib T v n →
    ∀ {fuel left : Nat} {d : Data}, (Machine.mk lib).extract T fuel v = .ok (d, left) → n + left ≤ fuel
  | _, _, _, .nat, _, _, _, h | _, _, _, .bool, _, _, _, h | _, _, _, .bytes, _, _, _, h
  | _, _, _, .digest, _, _, _, h => by
    simp only [Machine.extract, Except.ok.injEq, Prod.mk.injEq] at h; omega
  | _, _, _, .record hu hr, fuel, left, d, h => by
    have ihr := @forcesRow_le _ _ _ hr
    simp only [Machine.extract] at h
    split at h
    · rename_i fs' f1 hk
      split at h
      · rename_i ds f2 hx
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        obtain ⟨rfl, h1⟩ := unknot_le hu hk
        have h2 := ihr hx
        omega
      · cases h
    · cases h
  | _, _, _, .sum hA hf, fuel, left, d, h => by
    have ihf := @forces_le _ _ _ hf
    simp only [Machine.extract] at h
    split at h
    · rename_i d' f1 hx
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      rw [extractArm_find hA] at hx
      exact ihf hx
    · cases h

theorem forcesRow_le : ∀ {row : List (Label × Ty)} {fs : List (Label × (Term × Env))} {n : Nat},
    ForcesRow lib row fs n → ∀ {fuel left : Nat} {ds : List (Label × Data)},
      (Machine.mk lib).extractRow row fuel fs = .ok (ds, left) → n + left ≤ fuel
  | _, _, _, .nil, _, _, _, h => by
    simp only [Machine.extractRow, Except.ok.injEq, Prod.mk.injEq] at h; omega
  | _, _, _, .cons hd hf hr, fuel, left, ds, h => by
    have ihf := @forces_le _ _ _ hf
    have ihr := @forcesRow_le _ _ _ hr
    simp only [Machine.extractRow, if_true] at h
    split at h
    · rename_i v1 f1 hfo
      split at h
      · rename_i d f2 hx
        split at h
        · rename_i ds' f3 hrest
          simp only [Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨-, rfl⟩ := h
          obtain ⟨rfl, h1⟩ := force_lt hfo hd
          have h2 := ihf hx
          have h3 := ihr hrest
          omega
        · cases h
      · cases h
    · cases h
end


theorem force_derives {fuel fuel' : Nat} {t : Term} {env : Env} {v : Val}
    (h : (Machine.mk lib).force fuel t env = .ok (v, fuel')) : ∃ n, Derives lib env t (.ok v) n := by
  unfold Machine.force at h
  split at h
  · rename_i w used hr
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact bigStep_derives (run_bigStep hr)
  · cases h

theorem unknot_unknots : ∀ (rounds : Nat) {fuel fuel' : Nat} {v : Val} {fs : List (Label × (Term × Env))},
    (Machine.mk lib).unknot rounds fuel v = .ok (fs, fuel') → ∃ n, Unknots lib v fs n
  | rounds, _, _, .record gs, fs, h => by
    cases rounds <;> simp only [Machine.unknot, Except.ok.injEq, Prod.mk.injEq] at h <;>
      obtain ⟨rfl, rfl⟩ := h <;> exact ⟨0, .record⟩
  | 0, _, _, .knot _ _, _, h => by simp [Machine.unknot] at h
  | r + 1, _, _, .knot body env, fs, h => by
    simp only [Machine.unknot] at h
    split at h
    · rename_i v1 f1 hf
      obtain ⟨n, hd⟩ := force_derives hf
      obtain ⟨m, hu⟩ := unknot_unknots r h
      exact ⟨n + m, .knot hd hu⟩
    · cases h
  | _, _, _, .nat _, _, h | _, _, _, .bool _, _, h | _, _, _, .bytes _, _, h | _, _, _, .digest _, _, h
  | _, _, _, .clo _ _, _, h
  | _, _, _, .inj _ _, _, h => by cases ‹Nat› <;> simp [Machine.unknot] at h

mutual
/-- **Extraction's meaning is `Forces`**: every extraction the deployed machine completes performs
derivations `Forces` names, so `forces_le` applies to every admitted extraction. -/
theorem extract_forces : ∀ (T : Ty) {fuel left : Nat} {v : Val} {d : Data},
    (Machine.mk lib).extract T fuel v = .ok (d, left) → ∃ n, Forces lib T v n
  | .nat, _, _, .nat _, _, _ => ⟨0, .nat⟩
  | .bool, _, _, .bool _, _, _ => ⟨0, .bool⟩
  | .bytes, _, _, .bytes _, _, _ => ⟨0, .bytes⟩
  | .digest, _, _, .digest _, _, _ => ⟨0, .digest⟩
  | .record row, fuel, left, v, d, h => by
    simp only [Machine.extract] at h
    split at h
    · rename_i fs f1 hk
      split at h
      · rename_i ds f2 hx
        obtain ⟨n, hu⟩ := unknot_unknots fuel hk
        obtain ⟨m, hr⟩ := extractRow_forces row hx
        exact ⟨n + m, .record hu hr⟩
      · cases h
    · cases h
  | .sum row, fuel, left, .inj ℓ w, d, h => by
    simp only [Machine.extract] at h
    split at h
    · rename_i d' f1 hx
      obtain ⟨A, hA, n, hf⟩ := extractArm_forces row hx
      exact ⟨n, .sum hA hf⟩
    · cases h
  | .nat, _, _, .bool _, _, h | .nat, _, _, .bytes _, _, h | .nat, _, _, .digest _, _, h | .nat, _, _, .clo _ _, _, h
  | .nat, _, _, .record _, _, h | .nat, _, _, .knot _ _, _, h | .nat, _, _, .inj _ _, _, h
  | .bool, _, _, .nat _, _, h | .bool, _, _, .bytes _, _, h | .bool, _, _, .digest _, _, h | .bool, _, _, .clo _ _, _, h
  | .bool, _, _, .record _, _, h | .bool, _, _, .knot _ _, _, h | .bool, _, _, .inj _ _, _, h
  | .bytes, _, _, .nat _, _, h | .bytes, _, _, .bool _, _, h | .bytes, _, _, .digest _, _, h | .bytes, _, _, .clo _ _, _, h
  | .bytes, _, _, .record _, _, h | .bytes, _, _, .knot _ _, _, h | .bytes, _, _, .inj _ _, _, h
  | .digest, _, _, .nat _, _, h | .digest, _, _, .bool _, _, h | .digest, _, _, .bytes _, _, h | .digest, _, _, .clo _ _, _, h
  | .digest, _, _, .record _, _, h | .digest, _, _, .knot _ _, _, h | .digest, _, _, .inj _ _, _, h
  | .sum _, _, _, .nat _, _, h | .sum _, _, _, .bool _, _, h | .sum _, _, _, .bytes _, _, h | .sum _, _, _, .digest _, _, h
  | .sum _, _, _, .clo _ _, _, h | .sum _, _, _, .record _, _, h | .sum _, _, _, .knot _ _, _, h
  | .fn _ _, _, _, _, _, h => by simp [Machine.extract] at h

theorem extractArm_forces : ∀ (row : List (Label × Ty)) {ℓ : Label} {fuel left : Nat} {w : Val} {d : Data},
    (Machine.mk lib).extractArm row ℓ fuel w = .ok (d, left) →
      ∃ A, Row.find? ℓ row = some A ∧ ∃ n, Forces lib A w n
  | [], _, _, _, _, _, h => by simp [Machine.extractArm] at h
  | (k, A) :: row, ℓ, _, _, _, _, h => by
    simp only [Machine.extractArm] at h
    split at h
    · exact ⟨A, by simp [Row.find?, *], extract_forces A h⟩
    · obtain ⟨B, hB, hf⟩ := extractArm_forces row h
      exact ⟨B, by simp [Row.find?, *], hf⟩

theorem extractRow_forces : ∀ (row : List (Label × Ty)) {fuel left : Nat}
    {fs : List (Label × (Term × Env))} {ds : List (Label × Data)},
    (Machine.mk lib).extractRow row fuel fs = .ok (ds, left) → ∃ n, ForcesRow lib row fs n
  | [], _, _, [], _, _ => ⟨0, .nil⟩
  | [], _, _, _ :: _, _, h => by simp [Machine.extractRow] at h
  | _ :: _, _, _, [], _, h => by simp [Machine.extractRow] at h
  | (ℓ, A) :: row, fuel, left, (ℓ', (t, env)) :: fs, ds, h => by
    simp only [Machine.extractRow] at h
    split at h
    · rename_i hl
      subst hl
      split at h
      · rename_i v1 f1 hfo
        split at h
        · rename_i d f2 hx
          split at h
          · rename_i ds' f3 hrest
            obtain ⟨n, hd⟩ := force_derives hfo
            obtain ⟨m, hf⟩ := extract_forces A hx
            obtain ⟨k, hr⟩ := extractRow_forces row hrest
            exact ⟨n + m + k, .cons hd hf hr⟩
          · cases h
        · cases h
      · cases h
    · cases h
end


/-- `runBy` over the deployed step is `run`: the plant changes the stepper and nothing else. -/
theorem runBy_step (cap : Nat) : ∀ (fuel used : Nat) (s : State),
    Need.runBy (step lib) cap fuel used s = run lib cap fuel used s
  | 0, _, _ => rfl
  | fuel + 1, used, s => by
    simp only [Need.runBy, run]
    cases step lib s with
    | halt v => rfl
    | fault f => rfl
    | next s' =>
      simp only
      split
      · rfl
      · exact runBy_step cap fuel (used + 1) s'

/-! ## The whole count, over the run the deployed machine makes -/

variable {D : Type} {bytesOf : D → ByteArray} {digestOf : ByteArray → Option D}

/-- `requiredOf`'s count: the size of the method run's derivation, plus the forced suspensions'. -/
theorem requiredOf_spec {look : Pinned D} {rv : RowView D} {pkg : D} {state : Slots} {method : Nat} {args : ByteArray}
    {r : Req D} {budget N : Nat}
    (h : Need.requiredOf bytesOf digestOf look rv pkg state method args r budget = .ok N) :
    ∃ (S : RunSetup) (v : Val) (n m : Nat),
      runSetup bytesOf digestOf look rv pkg state method args r = .ok S ∧
      Derives S.lib S.env S.term (.ok v) n ∧ Forces S.lib S.ty v m ∧ N = n + m := by
  unfold Need.requiredOf at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · rename_i S hs
    split at h
    · split at h
      · simp only [Except.ok.injEq] at h; subst h
        exact ⟨S, _, _, _, hs, need_derives ‹_›, needExtract_forces _ ‹_›, rfl⟩
      · cases h
    · cases h
    · cases h

/-- `runMeasured`'s front half is `runSetup`, and its tick count is the run of that term in that
environment plus the extraction at that type. -/
theorem runMeasured_setup {look : Pinned D} {rv : RowView D} {pkg : D} {state : Slots} {method : Nat} {args : ByteArray}
    {r : Req D} {budget : Nat} {s : Slots} {calls : List (Body D)}
    {rows : List (RowSlot D × RowAct)} {ticks k : Nat}
    (h : runMeasured bytesOf digestOf look rv pkg state method args r budget = .ok (s, calls, rows, ticks, k)) :
    ∃ (S : RunSetup) (v : Val) (used : Nat) (d : Data) (left : Nat),
      runSetup bytesOf digestOf look rv pkg state method args r = .ok S ∧
      run S.lib Bounds.stackMax budget 0 (State.init S.term S.env) = .value v used ∧
      (Machine.mk S.lib).extract S.ty (budget - used) v = .ok (d, left) ∧ ticks = budget - left := by
  unfold runMeasured at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  repeat' split at h
  all_goals first | (simp at h; done) | skip
  simp only [Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨-, -, -, rfl, -⟩ := h
  exact ⟨_, _, _, _, _, ‹_›, ‹_›, ‹_›, rfl⟩

/-- **The denominator counts the deployed run**: for an invoke `runMeasured` admits, the ratio's two
sides are one run's. The setup is THIS invoke's (`runSetup` of its inputs). The numerator `ticks`
is that term's machine run in that environment plus the extraction at that type, under what the
run left. The denominator `requiredOf` is the size of the derivation of the very value the
machine computed (`derives_unique`), plus the size of what extraction must force at that type
(`forces_unique`). -/
theorem required_counts_the_run {look : Pinned D} {rv : RowView D} {pkg : D} {state : Slots} {method : Nat}
    {args : ByteArray} {r : Req D} {budget N : Nat} {s : Slots} {calls : List (Body D)}
    {rows : List (RowSlot D × RowAct)} {ticks k : Nat}
    (hm : runMeasured bytesOf digestOf look rv pkg state method args r budget = .ok (s, calls, rows, ticks, k))
    (hq : Need.requiredOf bytesOf digestOf look rv pkg state method args r budget = .ok N) :
    ∃ (S : RunSetup) (v : Val) (used : Nat) (d : Data) (left n m : Nat),
      runSetup bytesOf digestOf look rv pkg state method args r = .ok S ∧
      run S.lib Bounds.stackMax budget 0 (State.init S.term S.env) = .value v used ∧
      (Machine.mk S.lib).extract S.ty (budget - used) v = .ok (d, left) ∧ ticks = budget - left ∧
      Derives S.lib S.env S.term (.ok v) n ∧ Forces S.lib S.ty v m ∧ N = n + m := by
  obtain ⟨S, v, n, m, hs, hd, hf, rfl⟩ := requiredOf_spec hq
  obtain ⟨S', v', used, d, left, hs', hr, he, hticks⟩ := runMeasured_setup hm
  rw [hs] at hs'
  simp only [Except.ok.injEq] at hs'
  subst hs'
  have := bigStep_deterministic (derives_bigStep hd) (run_bigStep hr)
  simp only [Except.ok.injEq] at this; subst this
  exact ⟨S, v, used, d, left, n, m, hs, hr, he, hticks, hd, hf, rfl⟩

/-- **The ratio is above 1** (cv 01a14a87-33b2): for an invoke `runMeasured` admits, the ticks it
charged exceed what `requiredOf` counts. The method's run pays more ticks than its meaning's
derivation has rule instances (`derives_lt_used`), and extraction pays at least the size of every
suspension it must force (`forces_le`). So `ticks-per-required-step` cannot go below 1 for any
admitted invoke, and a counter that over-counted the requirement would contradict it. -/
theorem required_lt_ticks {look : Pinned D} {rv : RowView D} {pkg : D} {state : Slots} {method : Nat}
    {args : ByteArray} {r : Req D} {budget N : Nat} {s : Slots} {calls : List (Body D)}
    {rows : List (RowSlot D × RowAct)} {ticks k : Nat}
    (hm : runMeasured bytesOf digestOf look rv pkg state method args r budget = .ok (s, calls, rows, ticks, k))
    (hq : Need.requiredOf bytesOf digestOf look rv pkg state method args r budget = .ok N) :
    N < ticks := by
  obtain ⟨S, v, used, d, left, n, m, -, hr, he, rfl, hd, hf, rfl⟩ := required_counts_the_run hm hq
  obtain ⟨h1, h2⟩ := derives_lt_used hd hr
  have h3 := forces_le hf he
  omega

/-! ## Teeth -/

private def idApp : Term := .app (.lam .nat (.var 0)) (.nat 1)

/-- `(λx. x) 1`: an `app`, a `lam`, a `nat` and the body's `var`: four rule instances. -/
theorem need_idApp : Need.need [] 4 [] idApp = some (.ok (.nat 1), 4) := rfl

/-- And four is THE size: no derivation of it has three. -/
theorem idApp_not_three : ¬ Derives [] [] idApp (.ok (.nat 1)) 3 := fun h =>
  absurd (derives_unique h (need_derives need_idApp)).2 (by decide)

/-- The machine takes seven ticks on it (the `app` three, each leaf one, the halt one), the plant nine. -/
theorem idApp_ticks : (run [] 8 16 0 (State.init idApp)).used = 7 := by decide

theorem idApp_plant_ticks : (Need.runBy (Need.wasteStep []) 8 16 0 (State.init idApp)).used = 9 := by decide

/-- The tooth of `derives_lt_used` and `required_lt_ticks`: a machine that skips rule instances
(`Need.skipStep`) finishes `idApp` in 3 ticks, below its derivation's 4 (`need_idApp`). So
"more ticks than rule instances" is a fact about the deployed step, and the plant refutes it. -/
theorem idApp_skip_below :
    (match Need.runBy (Need.skipStep []) 8 16 0 (State.init idApp) with
      | .value (.nat 1) 3 => true
      | _ => false) = true := by decide

end Nanodregg.Lang
