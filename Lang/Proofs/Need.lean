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
`n`. It is a definition of what extraction requires, not a claim about `Machine.extract`'s
forcing. `forces_unique` shows the sum is one number, and `needExtract_forces` is its
counter's spec.

`requiredOf_spec` and `runMeasured_setup` give the whole count: for an invoke that `runMeasured`
admits, `requiredOf` counts the derivation of the very value the deployed machine computed
(`required_counts_the_run`), plus the forced suspensions at the method's result type.
`runBy_step` says the plant's loop is the deployed loop. Teeth: concrete sizes, a size that is
not one, and the plant costing two more ticks per application.
-/
import Lang.Sim.Need
import Lang.Proofs.Agree

namespace Nanodregg.Lang

open Nanodregg.Kernel
open Nanodregg.Kernel.Receive

mutual
/-- `BigStep` with the derivation's size: one per rule instance. -/
inductive Derives (lib : List Term) : Env → Term → Except Fault Val → Nat → Prop
  | var {env i v} : env[i]? = some v → Derives lib env (.var i) (.ok v) 1
  | lam {env A b} : Derives lib env (.lam A b) (.ok (.clo b env)) 1
  | app {env f a b cenv w r n m k} : Derives lib env f (.ok (.clo b cenv)) n →
      Derives lib env a (.ok w) m → Derives lib (w :: cenv) b r k →
      Derives lib env (.app f a) r (n + m + k + 1)
  | appF {env f a e n} : Derives lib env f (.error e) n → Derives lib env (.app f a) (.error e) (n + 1)
  | appA {env f a v e n m} : Derives lib env f (.ok v) n → Derives lib env a (.error e) m →
      Derives lib env (.app f a) (.error e) (n + m + 1)
  | fix {env t b cenv n} : Derives lib env t (.ok (.clo b cenv)) n →
      Derives lib env (.fix t) (.ok (.knot b cenv)) (n + 1)
  | fixE {env t e n} : Derives lib env t (.error e) n → Derives lib env (.fix t) (.error e) (n + 1)
  | nat {env k} : Derives lib env (.nat k) (.ok (.nat k)) 1
  | bool {env b} : Derives lib env (.bool b) (.ok (.bool b)) 1
  | bytes {env s} : Derives lib env (.bytes s) (.ok (.bytes s)) 1
  | prim {env p a b x y n m} : Derives lib env a (.ok x) n → Derives lib env b (.ok y) m →
      primEval p x y ≠ .error .stuck → Derives lib env (.prim p a b) (primEval p x y) (n + m + 1)
  | primL {env p a b e n} : Derives lib env a (.error e) n →
      Derives lib env (.prim p a b) (.error e) (n + 1)
  | primR {env p a b x e n m} : Derives lib env a (.ok x) n → Derives lib env b (.error e) m →
      Derives lib env (.prim p a b) (.error e) (n + m + 1)
  | record {env fs} : Derives lib env (.record fs) (.ok (.record (suspend env fs))) 1
  | get {env t ℓ v r n m} : Derives lib env t (.ok v) n → DSel lib v ℓ r m →
      Derives lib env (.get t ℓ) r (n + m + 1)
  | getE {env t ℓ e n} : Derives lib env t (.error e) n → Derives lib env (.get t ℓ) (.error e) (n + 1)
  | extend {env t fs v r n m} : Derives lib env t (.ok v) n → DExt lib v fs env r m →
      Derives lib env (.extend t fs) r (n + m + 1)
  | extendE {env t fs e n} : Derives lib env t (.error e) n →
      Derives lib env (.extend t fs) (.error e) (n + 1)
  | inj {env A ℓ t w n} : Derives lib env t (.ok w) n →
      Derives lib env (.inj A ℓ t) (.ok (.inj ℓ w)) (n + 1)
  | injE {env A ℓ t e n} : Derives lib env t (.error e) n →
      Derives lib env (.inj A ℓ t) (.error e) (n + 1)
  | case {env t arms ℓ w body r n m} : Derives lib env t (.ok (.inj ℓ w)) n →
      Row.find? ℓ arms = some body → Derives lib (w :: env) body r m →
      Derives lib env (.case t arms) r (n + m + 1)
  | caseE {env t arms e n} : Derives lib env t (.error e) n →
      Derives lib env (.case t arms) (.error e) (n + 1)
  | iteT {env c a b r n m} : Derives lib env c (.ok (.bool true)) n → Derives lib env a r m →
      Derives lib env (.ite c a b) r (n + m + 1)
  | iteF {env c a b r n m} : Derives lib env c (.ok (.bool false)) n → Derives lib env b r m →
      Derives lib env (.ite c a b) r (n + m + 1)
  | iteE {env c a b e n} : Derives lib env c (.error e) n →
      Derives lib env (.ite c a b) (.error e) (n + 1)
  | ref {env i body r n} : lib[i]? = some body → Derives lib [] body r n →
      Derives lib env (.ref i) r (n + 1)

/-- `Sel` with its size. -/
inductive DSel (lib : List Term) : Val → Label → Except Fault Val → Nat → Prop
  | field {fs ℓ t env r n} : Row.find? ℓ fs = some (t, env) → Derives lib env t r n →
      DSel lib (.record fs) ℓ r (n + 1)
  | knot {b env ℓ v r n m} : Derives lib (.knot b env :: env) b (.ok v) n → DSel lib v ℓ r m →
      DSel lib (.knot b env) ℓ r (n + m + 1)
  | knotE {b env ℓ e n} : Derives lib (.knot b env :: env) b (.error e) n →
      DSel lib (.knot b env) ℓ (.error e) (n + 1)

/-- `Ext` with its size. -/
inductive DExt (lib : List Term) : Val → List (Label × Term) → Env → Except Fault Val → Nat → Prop
  | record {gs fs env} : DExt lib (.record gs) fs env (.ok (.record (Row.merge gs (suspend env fs)))) 1
  | knot {b kenv fs env v r n m} : Derives lib (.knot b kenv :: kenv) b (.ok v) n →
      DExt lib v fs env r m → DExt lib (.knot b kenv) fs env r (n + m + 1)
  | knotE {b kenv fs env e n} : Derives lib (.knot b kenv :: kenv) b (.error e) n →
      DExt lib (.knot b kenv) fs env (.error e) (n + 1)
end

variable {lib : List Term}

/-! ## The size erases to `BigStep`, every `BigStep` has one, and it is unique -/

mutual
theorem derives_bigStep : ∀ {env : Env} {t : Term} {r : Except Fault Val} {n : Nat},
    Derives lib env t r n → BigStep lib env t r
  | _, _, _, _, .var h => .var h
  | _, _, _, _, .lam => .lam
  | _, _, _, _, .app a b c => .app (derives_bigStep a) (derives_bigStep b) (derives_bigStep c)
  | _, _, _, _, .appF a => .appF (derives_bigStep a)
  | _, _, _, _, .appA a b => .appA (derives_bigStep a) (derives_bigStep b)
  | _, _, _, _, .fix a => .fix (derives_bigStep a)
  | _, _, _, _, .fixE a => .fixE (derives_bigStep a)
  | _, _, _, _, .nat => .nat
  | _, _, _, _, .bool => .bool
  | _, _, _, _, .bytes => .bytes
  | _, _, _, _, .prim a b h => .prim (derives_bigStep a) (derives_bigStep b) h
  | _, _, _, _, .primL a => .primL (derives_bigStep a)
  | _, _, _, _, .primR a b => .primR (derives_bigStep a) (derives_bigStep b)
  | _, _, _, _, .record => .record
  | _, _, _, _, .get a s => .get (derives_bigStep a) (dsel_sel s)
  | _, _, _, _, .getE a => .getE (derives_bigStep a)
  | _, _, _, _, .extend a x => .extend (derives_bigStep a) (dext_ext x)
  | _, _, _, _, .extendE a => .extendE (derives_bigStep a)
  | _, _, _, _, .inj a => .inj (derives_bigStep a)
  | _, _, _, _, .injE a => .injE (derives_bigStep a)
  | _, _, _, _, .case a h b => .case (derives_bigStep a) h (derives_bigStep b)
  | _, _, _, _, .caseE a => .caseE (derives_bigStep a)
  | _, _, _, _, .iteT a b => .iteT (derives_bigStep a) (derives_bigStep b)
  | _, _, _, _, .iteF a b => .iteF (derives_bigStep a) (derives_bigStep b)
  | _, _, _, _, .iteE a => .iteE (derives_bigStep a)
  | _, _, _, _, .ref h a => .ref h (derives_bigStep a)

theorem dsel_sel : ∀ {v : Val} {ℓ : Label} {r : Except Fault Val} {n : Nat},
    DSel lib v ℓ r n → Sel lib v ℓ r
  | _, _, _, _, .field h a => .field h (derives_bigStep a)
  | _, _, _, _, .knot a s => .knot (derives_bigStep a) (dsel_sel s)
  | _, _, _, _, .knotE a => .knotE (derives_bigStep a)

theorem dext_ext : ∀ {v : Val} {fs : List (Label × Term)} {env : Env} {r : Except Fault Val} {n : Nat},
    DExt lib v fs env r n → Ext lib v fs env r
  | _, _, _, _, _, .record => .record
  | _, _, _, _, _, .knot a x => .knot (derives_bigStep a) (dext_ext x)
  | _, _, _, _, _, .knotE a => .knotE (derives_bigStep a)
end

mutual
theorem bigStep_derives : ∀ {env : Env} {t : Term} {r : Except Fault Val},
    BigStep lib env t r → ∃ n, Derives lib env t r n
  | _, _, _, .var h => ⟨_, .var h⟩
  | _, _, _, .lam => ⟨_, .lam⟩
  | _, _, _, .app a b c =>
    let ⟨_, a⟩ := bigStep_derives a; let ⟨_, b⟩ := bigStep_derives b; let ⟨_, c⟩ := bigStep_derives c
    ⟨_, .app a b c⟩
  | _, _, _, .appF a => let ⟨_, a⟩ := bigStep_derives a; ⟨_, .appF a⟩
  | _, _, _, .appA a b =>
    let ⟨_, a⟩ := bigStep_derives a; let ⟨_, b⟩ := bigStep_derives b; ⟨_, .appA a b⟩
  | _, _, _, .fix a => let ⟨_, a⟩ := bigStep_derives a; ⟨_, .fix a⟩
  | _, _, _, .fixE a => let ⟨_, a⟩ := bigStep_derives a; ⟨_, .fixE a⟩
  | _, _, _, .nat => ⟨_, .nat⟩
  | _, _, _, .bool => ⟨_, .bool⟩
  | _, _, _, .bytes => ⟨_, .bytes⟩
  | _, _, _, .prim a b h =>
    let ⟨_, a⟩ := bigStep_derives a; let ⟨_, b⟩ := bigStep_derives b; ⟨_, .prim a b h⟩
  | _, _, _, .primL a => let ⟨_, a⟩ := bigStep_derives a; ⟨_, .primL a⟩
  | _, _, _, .primR a b =>
    let ⟨_, a⟩ := bigStep_derives a; let ⟨_, b⟩ := bigStep_derives b; ⟨_, .primR a b⟩
  | _, _, _, .record => ⟨_, .record⟩
  | _, _, _, .get a s => let ⟨_, a⟩ := bigStep_derives a; let ⟨_, s⟩ := sel_dsel s; ⟨_, .get a s⟩
  | _, _, _, .getE a => let ⟨_, a⟩ := bigStep_derives a; ⟨_, .getE a⟩
  | _, _, _, .extend a x =>
    let ⟨_, a⟩ := bigStep_derives a; let ⟨_, x⟩ := ext_dext x; ⟨_, .extend a x⟩
  | _, _, _, .extendE a => let ⟨_, a⟩ := bigStep_derives a; ⟨_, .extendE a⟩
  | _, _, _, .inj a => let ⟨_, a⟩ := bigStep_derives a; ⟨_, .inj a⟩
  | _, _, _, .injE a => let ⟨_, a⟩ := bigStep_derives a; ⟨_, .injE a⟩
  | _, _, _, .case a h b =>
    let ⟨_, a⟩ := bigStep_derives a; let ⟨_, b⟩ := bigStep_derives b; ⟨_, .case a h b⟩
  | _, _, _, .caseE a => let ⟨_, a⟩ := bigStep_derives a; ⟨_, .caseE a⟩
  | _, _, _, .iteT a b =>
    let ⟨_, a⟩ := bigStep_derives a; let ⟨_, b⟩ := bigStep_derives b; ⟨_, .iteT a b⟩
  | _, _, _, .iteF a b =>
    let ⟨_, a⟩ := bigStep_derives a; let ⟨_, b⟩ := bigStep_derives b; ⟨_, .iteF a b⟩
  | _, _, _, .iteE a => let ⟨_, a⟩ := bigStep_derives a; ⟨_, .iteE a⟩
  | _, _, _, .ref h a => let ⟨_, a⟩ := bigStep_derives a; ⟨_, .ref h a⟩

theorem sel_dsel : ∀ {v : Val} {ℓ : Label} {r : Except Fault Val},
    Sel lib v ℓ r → ∃ n, DSel lib v ℓ r n
  | _, _, _, .field h a => let ⟨_, a⟩ := bigStep_derives a; ⟨_, .field h a⟩
  | _, _, _, .knot a s => let ⟨_, a⟩ := bigStep_derives a; let ⟨_, s⟩ := sel_dsel s; ⟨_, .knot a s⟩
  | _, _, _, .knotE a => let ⟨_, a⟩ := bigStep_derives a; ⟨_, .knotE a⟩

theorem ext_dext : ∀ {v : Val} {fs : List (Label × Term)} {env : Env} {r : Except Fault Val},
    Ext lib v fs env r → ∃ n, DExt lib v fs env r n
  | _, _, _, _, .record => ⟨_, .record⟩
  | _, _, _, _, .knot a x => let ⟨_, a⟩ := bigStep_derives a; let ⟨_, x⟩ := ext_dext x; ⟨_, .knot a x⟩
  | _, _, _, _, .knotE a => let ⟨_, a⟩ := bigStep_derives a; ⟨_, .knotE a⟩
end

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
are summed. This is a DEFINITION of what extraction requires: no theorem ties it to the
suspensions `Machine.extract` actually forces (a machine that forced a field twice would be
waste this denominator is meant to expose). `forces_unique` shows the size is one number. -/
inductive Forces (lib : List Term) : Ty → Val → Nat → Prop
  | nat {k} : Forces lib .nat (.nat k) 0
  | bool {b} : Forces lib .bool (.bool b) 0
  | bytes {s} : Forces lib .bytes (.bytes s) 0
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
  | _, .nat _, _, _, h | _, .bool _, _, _, h | _, .bytes _, _, _, h | _, .clo _ _, _, _, h
  | _, .inj _ _, _, _, h => by cases ‹Nat› <;> simp [Need.needUnknot] at h

mutual
theorem needExtract_forces {fuel : Nat} : ∀ (T : Ty) {v : Val} {n : Nat},
    Need.needExtract lib fuel T v = some n → Forces lib T v n
  | .nat, .nat _, n, h => by simp only [Need.needExtract, Option.some.injEq] at h; subst h; exact .nat
  | .bool, .bool _, n, h => by simp only [Need.needExtract, Option.some.injEq] at h; subst h; exact .bool
  | .bytes, .bytes _, n, h => by simp only [Need.needExtract, Option.some.injEq] at h; subst h; exact .bytes
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
  | .nat, .bool _, _, h | .nat, .bytes _, _, h | .nat, .clo _ _, _, h | .nat, .record _, _, h
  | .nat, .knot _ _, _, h | .nat, .inj _ _, _, h
  | .bool, .nat _, _, h | .bool, .bytes _, _, h | .bool, .clo _ _, _, h | .bool, .record _, _, h
  | .bool, .knot _ _, _, h | .bool, .inj _ _, _, h
  | .bytes, .nat _, _, h | .bytes, .bool _, _, h | .bytes, .clo _ _, _, h | .bytes, .record _, _, h
  | .bytes, .knot _ _, _, h | .bytes, .inj _ _, _, h
  | .sum _, .nat _, _, h | .sum _, .bool _, _, h | .sum _, .bytes _, _, h | .sum _, .clo _ _, _, h
  | .sum _, .record _, _, h | .sum _, .knot _ _, _, h
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
theorem requiredOf_spec {look : Pinned D} {pkg : D} {state : Slots} {method : Nat} {args : ByteArray}
    {r : Req D} {budget N : Nat}
    (h : Need.requiredOf bytesOf digestOf look pkg state method args r budget = .ok N) :
    ∃ (lib : List Term) (t : Term) (env : Env) (T : Ty) (v : Val) (n m : Nat),
      Need.setupOf bytesOf digestOf look pkg state method args r = .ok (lib, t, env, T) ∧
      Derives lib env t (.ok v) n ∧ Forces lib T v m ∧ N = n + m := by
  unfold Need.requiredOf at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · rename_i x hs
    obtain ⟨lib, t, env, T⟩ := x
    simp only at h
    split at h
    · split at h
      · simp only [Except.ok.injEq] at h; subst h
        exact ⟨lib, t, env, T, _, _, _, hs, need_derives ‹_›, needExtract_forces T ‹_›, rfl⟩
      · cases h
    · cases h
    · cases h

/-- `runMeasured`'s front half is `setupOf`, and its tick count is the run of that term in that
environment plus the extraction at that type. -/
theorem runMeasured_setup {look : Pinned D} {pkg : D} {state : Slots} {method : Nat} {args : ByteArray}
    {r : Req D} {budget : Nat} {s : Slots} {calls : List (Body D)} {ticks k : Nat}
    (h : runMeasured bytesOf digestOf look pkg state method args r budget = .ok (s, calls, ticks, k)) :
    ∃ (lib : List Term) (t : Term) (env : Env) (T : Ty) (v : Val) (used : Nat) (d : Data) (left : Nat),
      Need.setupOf bytesOf digestOf look pkg state method args r = .ok (lib, t, env, T) ∧
      run lib Bounds.stackMax budget 0 (State.init t env) = .value v used ∧
      (Machine.mk lib).extract T (budget - used) v = .ok (d, left) ∧ ticks = budget - left := by
  unfold runMeasured at h
  unfold Need.setupOf
  simp only [bind, Except.bind, pure, Except.pure] at h ⊢
  repeat' split at h
  all_goals first | (simp at h; done) | skip
  all_goals
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨-, -, rfl, -⟩ := h
    refine ⟨_, _, _, _, _, _, _, _, ?_, ‹_›, ‹_›, rfl⟩
    simp_all

/-- **The denominator counts the deployed run**: for an invoke `runMeasured` admits, the ratio's two
sides are one run's. The setup is THIS invoke's (`setupOf` of its inputs). The numerator `ticks`
is that term's machine run in that environment plus the extraction at that type, under what the
run left. The denominator `requiredOf` is the size of the derivation of the very value the
machine computed (`derives_unique`), plus the size of what extraction must force at that type
(`forces_unique`). -/
theorem required_counts_the_run {look : Pinned D} {pkg : D} {state : Slots} {method : Nat}
    {args : ByteArray} {r : Req D} {budget N : Nat} {s : Slots} {calls : List (Body D)} {ticks k : Nat}
    (hm : runMeasured bytesOf digestOf look pkg state method args r budget = .ok (s, calls, ticks, k))
    (hq : Need.requiredOf bytesOf digestOf look pkg state method args r budget = .ok N) :
    ∃ (lib : List Term) (t : Term) (env : Env) (T : Ty) (v : Val) (used : Nat) (d : Data) (left n m : Nat),
      Need.setupOf bytesOf digestOf look pkg state method args r = .ok (lib, t, env, T) ∧
      run lib Bounds.stackMax budget 0 (State.init t env) = .value v used ∧
      (Machine.mk lib).extract T (budget - used) v = .ok (d, left) ∧ ticks = budget - left ∧
      Derives lib env t (.ok v) n ∧ Forces lib T v m ∧ N = n + m := by
  obtain ⟨lib, t, env, T, v, n, m, hs, hd, hf, rfl⟩ := requiredOf_spec hq
  obtain ⟨lib', t', env', T', v', used, d, left, hs', hr, he, hticks⟩ := runMeasured_setup hm
  rw [hs] at hs'
  simp only [Except.ok.injEq, Prod.mk.injEq] at hs'
  obtain ⟨rfl, rfl, rfl, rfl⟩ := hs'
  have := bigStep_deterministic (derives_bigStep hd) (run_bigStep hr)
  simp only [Except.ok.injEq] at this; subst this
  exact ⟨lib, t, env, T, v, used, d, left, n, m, hs, hr, he, hticks, hd, hf, rfl⟩

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

end Nanodregg.Lang
