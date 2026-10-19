/-
# Lang.Proofs.Derives — `BigStep` carrying its size

`Derives lib env t r n` is `BigStep lib env t r` with the number `n` of rule instances in the
derivation (`DSel`, `DExt` for `Sel`, `Ext`): every constructor adds exactly 1 for itself to its
premises' sizes, except `prim`, which adds the primitive's `primTicks` (LANG-64: the language's price
for it, one per word of bytes its operands hold, 1 for every primitive on at most a word). The
price list is shared with the machine, as `primEval` is; the machine's control is not. `derives_bigStep` erases the size; `bigStep_derives` gives every derivation one.
`Lang.Proofs.Complete` counts the machine against it (`derives_leads`); `Lang.Proofs.Need` shows
the BAR's counter computes it.
-/
import Lang.Proofs.BigStep
import Lang.Proofs.Cost

namespace Nanodregg.Lang

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
  | digest {env s} : Derives lib env (.digest s) (.ok (.digest s)) 1
  | refuse {env T w} : Derives lib env (.refuse T w) (.error (.refused w)) 1
  | prim {env p a b x y n m} : Derives lib env a (.ok x) n → Derives lib env b (.ok y) m →
      primEval p x y ≠ .error .stuck →
      Derives lib env (.prim p a b) (primEval p x y) (n + m + primTicks p x y)
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

/-! ## The size erases to `BigStep`, and every `BigStep` has one -/

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
  | _, _, _, _, .digest => .digest
  | _, _, _, _, .refuse => .refuse
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
  | _, _, _, .digest => ⟨_, .digest⟩
  | _, _, _, .refuse => ⟨_, .refuse⟩
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

end Nanodregg.Lang
