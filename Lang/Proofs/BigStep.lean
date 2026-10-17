/-
# Lang.Proofs.BigStep — the reference semantics: what a term MEANS, independent of the machine

`BigStep lib env t r`: under the closure's bodies `lib` and the environment `env`, the term `t`
evaluates to `r` — a value (`.ok v`) or an arithmetic fault (`.error e`). One rule per
constructor (plus one per place a fault can arise), read off the language's meaning (LANG-1/2):
call by value, record fields suspended and forced by `get` (`Sel`), `extend` overriding the row
(`Ext`), and selection from a knot unrolling the knot (`fix`). Ticks and the stack bound are the
machine's resources, not meanings: they are not results here.

`bigStep_deterministic`: a term has at most one meaning. `run_bigStep` / `run_fault_bigStep`
(Lang.Proofs.Agree): every value and every non-`stuck` fault the CEK machine ends with is the
term's meaning; `bigStep_run` / `bigStep_run_fault` (Lang.Proofs.Complete): every meaning is
reached, budgets permitting. So the determinism re-execution relies on is a fact about the
language, and any other evaluator that agrees with `BigStep` agrees with the machine.

What `BigStep` does NOT check independently: it shares the VALUE domain with the machine (`Val`,
closures, `suspend`, `primEval`, `Row.find?`/`Row.merge`), so a bug there is inherited; it is
independent of the control (frames, stack, depth). `stuck` is never a meaning: no rule derives it
(the `prim` rule refuses a `primEval` that is stuck). One language decision is visible here and
named in decisions/lang.md LANG-18: `extend` of a knot unrolls the knot once and merges, so the
inherited fields keep the OLD self (no late binding of self through `extend`;
`bigStep_extend_keeps_old_self`).
-/
import Lang.Eval

namespace Nanodregg.Lang



mutual
inductive BigStep (lib : List Term) : Env → Term → (Except Fault Val) → Prop
  | var {env i v} : env[i]? = some v → BigStep lib env (.var i) (.ok v)
  | lam {env A b} : BigStep lib env (.lam A b) (.ok (.clo b env))
  | app {env f a b cenv w r} : BigStep lib env f (.ok (.clo b cenv)) → BigStep lib env a (.ok w) →
      BigStep lib (w :: cenv) b r → BigStep lib env (.app f a) r
  | appF {env f a e} : BigStep lib env f (.error e) → BigStep lib env (.app f a) (.error e)
  | appA {env f a v e} : BigStep lib env f (.ok v) → BigStep lib env a (.error e) →
      BigStep lib env (.app f a) (.error e)
  | fix {env t b cenv} : BigStep lib env t (.ok (.clo b cenv)) →
      BigStep lib env (.fix t) (.ok (.knot b cenv))
  | fixE {env t e} : BigStep lib env t (.error e) → BigStep lib env (.fix t) (.error e)
  | nat {env n} : BigStep lib env (.nat n) (.ok (.nat n))
  | bool {env b} : BigStep lib env (.bool b) (.ok (.bool b))
  | bytes {env s} : BigStep lib env (.bytes s) (.ok (.bytes s))
  | prim {env p a b x y} : BigStep lib env a (.ok x) → BigStep lib env b (.ok y) →
      primEval p x y ≠ .error .stuck → BigStep lib env (.prim p a b) (primEval p x y)
  | primL {env p a b e} : BigStep lib env a (.error e) → BigStep lib env (.prim p a b) (.error e)
  | primR {env p a b x e} : BigStep lib env a (.ok x) → BigStep lib env b (.error e) →
      BigStep lib env (.prim p a b) (.error e)
  | record {env fs} : BigStep lib env (.record fs) (.ok (.record (suspend env fs)))
  | get {env t ℓ v r} : BigStep lib env t (.ok v) → Sel lib v ℓ r → BigStep lib env (.get t ℓ) r
  | getE {env t ℓ e} : BigStep lib env t (.error e) → BigStep lib env (.get t ℓ) (.error e)
  | extend {env t fs v r} : BigStep lib env t (.ok v) → Ext lib v fs env r →
      BigStep lib env (.extend t fs) r
  | extendE {env t fs e} : BigStep lib env t (.error e) → BigStep lib env (.extend t fs) (.error e)
  | inj {env A ℓ t w} : BigStep lib env t (.ok w) → BigStep lib env (.inj A ℓ t) (.ok (.inj ℓ w))
  | injE {env A ℓ t e} : BigStep lib env t (.error e) → BigStep lib env (.inj A ℓ t) (.error e)
  | case {env t arms ℓ w body r} : BigStep lib env t (.ok (.inj ℓ w)) → Row.find? ℓ arms = some body →
      BigStep lib (w :: env) body r → BigStep lib env (.case t arms) r
  | caseE {env t arms e} : BigStep lib env t (.error e) → BigStep lib env (.case t arms) (.error e)
  | iteT {env c a b r} : BigStep lib env c (.ok (.bool true)) → BigStep lib env a r →
      BigStep lib env (.ite c a b) r
  | iteF {env c a b r} : BigStep lib env c (.ok (.bool false)) → BigStep lib env b r →
      BigStep lib env (.ite c a b) r
  | iteE {env c a b e} : BigStep lib env c (.error e) → BigStep lib env (.ite c a b) (.error e)
  | ref {env i body r} : lib[i]? = some body → BigStep lib [] body r → BigStep lib env (.ref i) r

/-- Selecting `ℓ` from a value: a record forces the field's suspension; a knot unrolls once and
selects from what it unrolls to. -/
inductive Sel (lib : List Term) : Val → Label → (Except Fault Val) → Prop
  | field {fs ℓ t env r} : Row.find? ℓ fs = some (t, env) → BigStep lib env t r →
      Sel lib (.record fs) ℓ r
  | knot {b env ℓ v r} : BigStep lib (.knot b env :: env) b (.ok v) → Sel lib v ℓ r →
      Sel lib (.knot b env) ℓ r
  | knotE {b env ℓ e} : BigStep lib (.knot b env :: env) b (.error e) →
      Sel lib (.knot b env) ℓ (.error e)

/-- Extending a value with suspended fields `fs` written in `env`: a record merges; a knot unrolls
once and extends what it unrolls to. -/
inductive Ext (lib : List Term) : Val → List (Label × Term) → Env → (Except Fault Val) → Prop
  | record {gs fs env} : Ext lib (.record gs) fs env (.ok (.record (Row.merge gs (suspend env fs))))
  | knot {b kenv fs env v r} : BigStep lib (.knot b kenv :: kenv) b (.ok v) → Ext lib v fs env r →
      Ext lib (.knot b kenv) fs env r
  | knotE {b kenv fs env e} : BigStep lib (.knot b kenv :: kenv) b (.error e) →
      Ext lib (.knot b kenv) fs env (.error e)
end

mutual
theorem bigStep_deterministic {lib : List Term} :
    ∀ {env : Env} {t : Term} {r r' : (Except Fault Val)}, BigStep lib env t r → BigStep lib env t r' → r = r'
  | _, _, _, _, .var h, h' => by cases h' with | var h2 => rw [h] at h2; cases h2; rfl
  | _, _, _, _, .lam, h' => by cases h'; rfl
  | _, _, _, _, .app hf ha hb, h' => by
    cases h' with
    | app hf' ha' hb' =>
      cases bigStep_deterministic hf hf'; cases bigStep_deterministic ha ha'
      exact bigStep_deterministic hb hb'
    | appF hf' => cases bigStep_deterministic hf hf'
    | appA _ ha' => cases bigStep_deterministic ha ha'
  | _, _, _, _, .appF hf, h' => by
    cases h' with
    | app hf' _ _ => cases bigStep_deterministic hf hf'
    | appF hf' => exact bigStep_deterministic hf hf'
    | appA hf' _ => cases bigStep_deterministic hf hf'
  | _, _, _, _, .appA hf ha, h' => by
    cases h' with
    | app _ ha' _ => cases bigStep_deterministic ha ha'
    | appF hf' => cases bigStep_deterministic hf hf'
    | appA _ ha' => exact bigStep_deterministic ha ha'
  | _, _, _, _, .fix ht, h' => by
    cases h' with
    | fix ht' => cases bigStep_deterministic ht ht'; rfl
    | fixE ht' => cases bigStep_deterministic ht ht'
  | _, _, _, _, .fixE ht, h' => by
    cases h' with
    | fix ht' => cases bigStep_deterministic ht ht'
    | fixE ht' => exact bigStep_deterministic ht ht'
  | _, _, _, _, .nat, h' | _, _, _, _, .bool, h' | _, _, _, _, .bytes, h'
  | _, _, _, _, .record, h' => by cases h'; rfl
  | _, _, _, _, .prim ha hb _, h' => by
    cases h' with
    | prim ha' hb' _ => cases bigStep_deterministic ha ha'; cases bigStep_deterministic hb hb'; rfl
    | primL ha' => cases bigStep_deterministic ha ha'
    | primR _ hb' => cases bigStep_deterministic hb hb'
  | _, _, _, _, .primL ha, h' => by
    cases h' with
    | prim ha' _ _ => cases bigStep_deterministic ha ha'
    | primL ha' => exact bigStep_deterministic ha ha'
    | primR ha' _ => cases bigStep_deterministic ha ha'
  | _, _, _, _, .primR ha hb, h' => by
    cases h' with
    | prim _ hb' _ => cases bigStep_deterministic hb hb'
    | primL ha' => cases bigStep_deterministic ha ha'
    | primR _ hb' => exact bigStep_deterministic hb hb'
  | _, _, _, _, .get ht hs, h' => by
    cases h' with
    | get ht' hs' => cases bigStep_deterministic ht ht'; exact sel_deterministic hs hs'
    | getE ht' => cases bigStep_deterministic ht ht'
  | _, _, _, _, .getE ht, h' => by
    cases h' with
    | get ht' _ => cases bigStep_deterministic ht ht'
    | getE ht' => exact bigStep_deterministic ht ht'
  | _, _, _, _, .extend ht hx, h' => by
    cases h' with
    | extend ht' hx' => cases bigStep_deterministic ht ht'; exact ext_deterministic hx hx'
    | extendE ht' => cases bigStep_deterministic ht ht'
  | _, _, _, _, .extendE ht, h' => by
    cases h' with
    | extend ht' _ => cases bigStep_deterministic ht ht'
    | extendE ht' => exact bigStep_deterministic ht ht'
  | _, _, _, _, .inj ht, h' => by
    cases h' with
    | inj ht' => cases bigStep_deterministic ht ht'; rfl
    | injE ht' => cases bigStep_deterministic ht ht'
  | _, _, _, _, .injE ht, h' => by
    cases h' with
    | inj ht' => cases bigStep_deterministic ht ht'
    | injE ht' => exact bigStep_deterministic ht ht'
  | _, _, _, _, .case ht hf hb, h' => by
    cases h' with
    | case ht' hf' hb' =>
      cases bigStep_deterministic ht ht'; rw [hf] at hf'; cases hf'
      exact bigStep_deterministic hb hb'
    | caseE ht' => cases bigStep_deterministic ht ht'
  | _, _, _, _, .caseE ht, h' => by
    cases h' with
    | case ht' _ _ => cases bigStep_deterministic ht ht'
    | caseE ht' => exact bigStep_deterministic ht ht'
  | _, _, _, _, .iteT hc ha, h' => by
    cases h' with
    | iteT _ ha' => exact bigStep_deterministic ha ha'
    | iteF hc' _ => cases bigStep_deterministic hc hc'
    | iteE hc' => cases bigStep_deterministic hc hc'
  | _, _, _, _, .iteF hc hb, h' => by
    cases h' with
    | iteT hc' _ => cases bigStep_deterministic hc hc'
    | iteF _ hb' => exact bigStep_deterministic hb hb'
    | iteE hc' => cases bigStep_deterministic hc hc'
  | _, _, _, _, .iteE hc, h' => by
    cases h' with
    | iteT hc' _ => cases bigStep_deterministic hc hc'
    | iteF hc' _ => cases bigStep_deterministic hc hc'
    | iteE hc' => exact bigStep_deterministic hc hc'
  | _, _, _, _, .ref hi hb, h' => by
    cases h' with | ref hi' hb' => rw [hi] at hi'; cases hi'; exact bigStep_deterministic hb hb'

theorem sel_deterministic {lib : List Term} :
    ∀ {v : Val} {ℓ : Label} {r r' : (Except Fault Val)}, Sel lib v ℓ r → Sel lib v ℓ r' → r = r'
  | _, _, _, _, .field hf hb, h' => by
    cases h' with | field hf' hb' => rw [hf] at hf'; cases hf'; exact bigStep_deterministic hb hb'
  | _, _, _, _, .knot hb hs, h' => by
    cases h' with
    | knot hb' hs' => cases bigStep_deterministic hb hb'; exact sel_deterministic hs hs'
    | knotE hb' => cases bigStep_deterministic hb hb'
  | _, _, _, _, .knotE hb, h' => by
    cases h' with
    | knot hb' _ => cases bigStep_deterministic hb hb'
    | knotE hb' => exact bigStep_deterministic hb hb'

theorem ext_deterministic {lib : List Term} :
    ∀ {v : Val} {fs : List (Label × Term)} {env : Env} {r r' : (Except Fault Val)},
      Ext lib v fs env r → Ext lib v fs env r' → r = r'
  | _, _, _, _, _, .record, h' => by cases h'; rfl
  | _, _, _, _, _, .knot hb hx, h' => by
    cases h' with
    | knot hb' hx' => cases bigStep_deterministic hb hb'; exact ext_deterministic hx hx'
    | knotE hb' => cases bigStep_deterministic hb hb'
  | _, _, _, _, _, .knotE hb, h' => by
    cases h' with
    | knot hb' _ => cases bigStep_deterministic hb hb'
    | knotE hb' => exact bigStep_deterministic hb hb'
end

/-! ## The meaning on concrete terms (each a derivation; a mutated rule loses it) -/

/-- A field is forced only when selected: the diverging-shaped `bad` is never evaluated. -/
theorem bigStep_lazy_field :
    BigStep [] [] (.get (.record [("bad", .get (.var 0) "bad"), ("good", .nat 7)]) "good") (.ok (.nat 7)) :=
  .get .record (.field rfl .nat)

/-- `extend` overrides: the new field wins. -/
theorem bigStep_extend_overrides :
    BigStep [] [] (.get (.extend (.record [("a", .nat 1)]) [("a", .nat 2)]) "a") (.ok (.nat 2)) :=
  .get (.extend .record .record) (.field rfl .nat)

/-- A fault is a meaning: `2 - 3` underflows, and the fault propagates through an application. -/
theorem bigStep_underflow_propagates :
    BigStep [] [] (.app (.lam .nat (.var 0)) (.prim .sub (.nat 2) (.nat 3))) (.error .underflow) :=
  .appA .lam (by
    have h := BigStep.prim (lib := []) (env := []) (p := .sub) (BigStep.nat (n := 2)) (BigStep.nat (n := 3))
      (by simp [primEval])
    exact h)

/-- `self` for the knot below: `{a = 1, g = self.a}`. -/
private def oldSelf : Term := .record [("a", .nat 1), ("g", .get (.var 0) "a")]

/-- `extend` does not late-bind self (LANG-18): `(fix (λself. {a = 1, g = self.a}) with a = 2).g`
is `1`, the OLD `a`, because extending a knot unrolls it once and the inherited `g` keeps the
knot as its self. A late-binding `extend` would give `2`. -/
theorem bigStep_extend_keeps_old_self :
    BigStep [] [] (.get (.extend (.fix (.lam .nat oldSelf)) [("a", .nat 2)]) "g") (.ok (.nat 1)) :=
  .get (.extend (.fix .lam) (.knot .record .record))
    (.field rfl (.get (.var rfl) (.knot .record (.field rfl .nat))))

/-- No meaning for a type error (the machine gets stuck): applying a natural. -/
theorem bigStep_no_app_nat : ¬ ∃ r, BigStep [] [] (.app (.nat 1) (.nat 2)) r := by
  rintro ⟨r, h⟩
  cases h with
  | app hf _ _ => cases hf
  | appF hf => cases hf
  | appA _ ha => cases ha

/-- No meaning for selecting from a natural. -/
theorem bigStep_no_get_nat : ¬ ∃ r, BigStep [] [] (.get (.nat 1) "a") r := by
  rintro ⟨r, h⟩
  cases h with
  | get ht hs => cases ht; cases hs
  | getE ht => cases ht

/-- No meaning for a wrong-shaped primitive (`stuck` is never a meaning). -/
theorem bigStep_no_add_bool : ¬ ∃ r, BigStep [] [] (.prim .add (.bool true) (.nat 1)) r := by
  rintro ⟨r, h⟩
  cases h with
  | prim ha hb hs => cases ha; cases hb; exact hs rfl
  | primL ha => cases ha
  | primR _ hb => cases hb

end Nanodregg.Lang
