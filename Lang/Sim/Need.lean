/-
# Lang.Sim.Need — what a run REQUIRES: the size of its reference derivation (tooling)

THE BAR's `ticks-per-required-step` (gates/waste.tsv, cv 01a14a39-c22e) divides the machine's ticks
by the work the program requires. That denominator is the number of rule instances in the `BigStep`
derivation of the run's meaning (Lang.Proofs.BigStep), plus, for extraction, the derivations of
the suspensions it forces. It is computed here by `need`, a fuel-bounded evaluator with one clause
per `BigStep`/`Sel`/`Ext` rule. Each clause adds 1 for its own rule instance to the counts of its
premises. It never reads the machine: no `step`, no `run`, no tick.
`Lang.Proofs.Need.need_derives` says the count IS the derivation's size (`Derives`, BigStep
carrying its size, `derives_bigStep`/`bigStep_derives`, the size unique by
`derives_size_unique`).

`requiredOf` has `runMeasured`'s inputs and front half: it loads, resolves, reads and decodes
with the same deployed functions. In place of the machine it counts the method's derivation and
extraction's forced suspensions (`needExtract`, shaped like `Machine.extract`). A count past its
fuel is a named refusal (`required: fuel`), never a zero.

The plant (`wasteStep`, `runBy`): a machine that takes two needless transitions per application
(it returns through an `ite true` detour before entering the body). It has the same meaning and
more ticks. `runBy (step lib)` is the deployed `run` (`Lang.Proofs.Need.runBy_step`), so the
plant differs from the deployed machine only in the stepper.
-/
import Lang.Program

namespace Nanodregg.Lang.Need

open Nanodregg.Lang
open Nanodregg.Kernel
open Nanodregg.Kernel.Receive

/-- A primitive result `BigStep` admits as a meaning (`stuck` is never one). -/
def meaningful : Except Fault Val → Bool
  | .error .stuck => false
  | _ => true

mutual
/-- The meaning of `t` in `env` and the number of rule instances of its derivation, within `fuel`
nested rule applications; `none` past the fuel or where no rule applies. -/
def need (lib : List Term) : Nat → Env → Term → Option (Except Fault Val × Nat)
  | 0, _, _ => none
  | f + 1, env, t =>
    match t with
    | .var i =>
      match env[i]? with
      | some v => some (.ok v, 1)
      | none => none
    | .lam _ b => some (.ok (.clo b env), 1)
    | .app fn a =>
      match need lib f env fn with
      | some (.error e, n) => some (.error e, n + 1)
      | some (.ok v, n) =>
        match need lib f env a with
        | some (.error e, m) => some (.error e, n + m + 1)
        | some (.ok w, m) =>
          match v with
          | .clo b cenv =>
            match need lib f (w :: cenv) b with
            | some (r, k) => some (r, n + m + k + 1)
            | none => none
          | _ => none
        | none => none
      | none => none
    | .fix t =>
      match need lib f env t with
      | some (.ok (.clo b cenv), n) => some (.ok (.knot b cenv), n + 1)
      | some (.error e, n) => some (.error e, n + 1)
      | _ => none
    | .nat n => some (.ok (.nat n), 1)
    | .bool b => some (.ok (.bool b), 1)
    | .bytes s => some (.ok (.bytes s), 1)
    | .prim p a b =>
      match need lib f env a with
      | some (.error e, n) => some (.error e, n + 1)
      | some (.ok x, n) =>
        match need lib f env b with
        | some (.error e, m) => some (.error e, n + m + 1)
        | some (.ok y, m) =>
          if meaningful (primEval p x y) then some (primEval p x y, n + m + 1) else none
        | none => none
      | none => none
    | .record fs => some (.ok (.record (suspend env fs)), 1)
    | .get t ℓ =>
      match need lib f env t with
      | some (.error e, n) => some (.error e, n + 1)
      | some (.ok v, n) =>
        match needSel lib f v ℓ with
        | some (r, m) => some (r, n + m + 1)
        | none => none
      | none => none
    | .extend t fs =>
      match need lib f env t with
      | some (.error e, n) => some (.error e, n + 1)
      | some (.ok v, n) =>
        match needExt lib f v fs env with
        | some (r, m) => some (r, n + m + 1)
        | none => none
      | none => none
    | .inj _ ℓ t =>
      match need lib f env t with
      | some (.ok w, n) => some (.ok (.inj ℓ w), n + 1)
      | some (.error e, n) => some (.error e, n + 1)
      | none => none
    | .case t arms =>
      match need lib f env t with
      | some (.error e, n) => some (.error e, n + 1)
      | some (.ok (.inj ℓ w), n) =>
        match Row.find? ℓ arms with
        | some body =>
          match need lib f (w :: env) body with
          | some (r, m) => some (r, n + m + 1)
          | none => none
        | none => none
      | _ => none
    | .ite c a b =>
      match need lib f env c with
      | some (.error e, n) => some (.error e, n + 1)
      | some (.ok (.bool true), n) =>
        match need lib f env a with
        | some (r, m) => some (r, n + m + 1)
        | none => none
      | some (.ok (.bool false), n) =>
        match need lib f env b with
        | some (r, m) => some (r, n + m + 1)
        | none => none
      | _ => none
    | .ref i =>
      match lib[i]? with
      | some body =>
        match need lib f [] body with
        | some (r, n) => some (r, n + 1)
        | none => none
      | none => none

/-- Selection (`Sel`): its meaning and its derivation's size. -/
def needSel (lib : List Term) : Nat → Val → Label → Option (Except Fault Val × Nat)
  | 0, _, _ => none
  | f + 1, .record fs, ℓ =>
    match Row.find? ℓ fs with
    | some (t, env) =>
      match need lib f env t with
      | some (r, n) => some (r, n + 1)
      | none => none
    | none => none
  | f + 1, .knot b env, ℓ =>
    match need lib f (.knot b env :: env) b with
    | some (.error e, n) => some (.error e, n + 1)
    | some (.ok v, n) =>
      match needSel lib f v ℓ with
      | some (r, m) => some (r, n + m + 1)
      | none => none
    | none => none
  | _ + 1, _, _ => none

/-- Extension (`Ext`): its meaning and its derivation's size. -/
def needExt (lib : List Term) : Nat → Val → List (Label × Term) → Env → Option (Except Fault Val × Nat)
  | 0, _, _, _ => none
  | _ + 1, .record gs, fs, env => some (.ok (.record (Row.merge gs (suspend env fs))), 1)
  | f + 1, .knot b kenv, fs, env =>
    match need lib f (.knot b kenv :: kenv) b with
    | some (.error e, n) => some (.error e, n + 1)
    | some (.ok v, n) =>
      match needExt lib f v fs env with
      | some (r, m) => some (r, n + m + 1)
      | none => none
    | none => none
  | _ + 1, _, _, _ => none
end

/-- A forced suspension's value and derivation size (`Machine.force`'s counterpart). -/
def needForce (lib : List Term) (fuel : Nat) (t : Term) (env : Env) : Option (Val × Nat) :=
  match need lib fuel env t with
  | some (.ok v, n) => some (v, n)
  | _ => none

/-- `Machine.unknot`'s counterpart: the derivations of each unfolding until a record appears. -/
def needUnknot (lib : List Term) (fuel : Nat) : (rounds : Nat) → Val →
    Option (List (Label × (Term × Env)) × Nat)
  | _, .record fs => some (fs, 0)
  | r + 1, v@(.knot body env) =>
    match needForce lib fuel body (v :: env) with
    | some (v', n) =>
      match needUnknot lib fuel r v' with
      | some (fs, m) => some (fs, n + m)
      | none => none
    | none => none
  | _, _ => none

mutual
/-- `Machine.extract`'s counterpart: the sizes of the derivations extraction forces, summed. -/
def needExtract (lib : List Term) (fuel : Nat) : Ty → Val → Option Nat
  | .nat, .nat _ => some 0
  | .bool, .bool _ => some 0
  | .bytes, .bytes _ => some 0
  | .record row, v =>
    match needUnknot lib fuel fuel v with
    | some (fs, n) =>
      match needExtractRow lib fuel row fs with
      | some m => some (n + m)
      | none => none
    | none => none
  | .sum row, .inj ℓ w => needExtractArm lib fuel row ℓ w
  | _, _ => none

def needExtractArm (lib : List Term) (fuel : Nat) : List (Label × Ty) → Label → Val → Option Nat
  | [], _, _ => none
  | (k, A) :: row, ℓ, w => if ℓ = k then needExtract lib fuel A w else needExtractArm lib fuel row ℓ w

def needExtractRow (lib : List Term) (fuel : Nat) :
    List (Label × Ty) → List (Label × (Term × Env)) → Option Nat
  | [], [] => some 0
  | (ℓ, A) :: row, (ℓ', (t, env)) :: fs =>
    if ℓ = ℓ' then
      match needForce lib fuel t env with
      | some (v, n) =>
        match needExtract lib fuel A v with
        | some m =>
          match needExtractRow lib fuel row fs with
          | some k => some (n + m + k)
          | none => none
        | none => none
      | none => none
    else none
  | _, _ => none
end

/-- `Lang.run`'s loop over any stepper. -/
def runBy (st : State → Step) (stackMax : Nat) : (fuel used : Nat) → State → Outcome
  | 0, used, _ => .fault .ticks used
  | fuel + 1, used, s =>
      match st s with
      | .halt v => .value v (used + 1)
      | .fault f => .fault f (used + 1)
      | .next s' =>
          if stackMax < s'.depth then .fault .stack (used + 1)
          else runBy st stackMax fuel (used + 1) s'

variable {D : Type} [DecidableEq D]

section
variable (bytesOf : D → ByteArray) (digestOf : ByteArray → Option D)

/-- `runMeasured`'s front half, with the same deployed functions: the closure's bodies, the term
the method run evaluates, its environment, and the type extraction reads the result at. -/
def setupOf (look : Pinned D) (pkg : D) (state : Slots) (method : Nat) (args : ByteArray)
    (r : Req D) : Except (Refusal D) (List Term × Term × Env × Ty) := do
  unless reqOk bytesOf r do throw (.program "request out of bounds")
  let (L, g) ← load digestOf look closureDepthMax (bytesOf pkg) ⟨[], [], []⟩
  let some p := L.pkgs[g]? | throw (.program "closure")
  let (ℓ, A, ks) ← resolveMethod p method
  let row := recordRow p.state
  let s ← match readState row state with | .ok d => pure d | .error e => throw (.program e)
  let a ← match Wire.decodeData A args with
    | .ok d => pure d
    | .error e => throw (.program s!"arguments: {decodeText e}")
  pure (L.lib, apply3 g ℓ, [(reqData bytesOf r).toVal, a.toVal, s.toVal], resultTy p.state ks)

/-- The steps an invoke requires: the size of the method run's derivation plus those of the
suspensions extraction forces, with `budget` as the fuel of each count. -/
def requiredOf (look : Pinned D) (pkg : D) (state : Slots) (method : Nat) (args : ByteArray)
    (r : Req D) (budget : Nat) : Except (Refusal D) Nat := do
  let (lib, t, env, T) ← setupOf bytesOf digestOf look pkg state method args r
  match need lib budget env t with
  | some (.ok v, n) =>
    match needExtract lib budget T v with
    | some m => pure (n + m)
    | none => throw (.program "required: extraction")
  | some (.error _, _) => throw (.program "required: a fault is not a run")
  | none => throw (.program "required: fuel")

/-- The method run alone under a stepper: the ticks it used (`runBy (step lib)` is the deployed
run, `Lang.Proofs.Need.runBy_step`). -/
def runTicksBy (stp : List Term → State → Step) (look : Pinned D) (pkg : D) (state : Slots)
    (method : Nat) (args : ByteArray) (r : Req D) (budget : Nat) : Except (Refusal D) Nat := do
  let (lib, t, env, _) ← setupOf bytesOf digestOf look pkg state method args r
  match runBy (stp lib) Bounds.stackMax budget 0 (State.init t env) with
  | .value _ used => pure used
  | .fault f _ => throw (.program s!"run: {faultText f}")
end

/-- PLANT (the ratio's tooth): the deployed step, except that entering a closure first returns
`true` through an `ite` frame whose branch is the body. That is two needless transitions per
application, with the same meaning. -/
def wasteStep (lib : List Term) (s : State) : Step :=
  match s.control, s.stack with
  | .ret v, .appR (.clo body cenv) :: k =>
    .next ⟨.eval (.bool true) [], .ite body body (v :: cenv) :: k, s.depth⟩
  | _, _ => step lib s

/-- PLANT (`required_lt_ticks`' tooth): the deployed step, except that applying a literal function
to a literal number enters the body at once. It skips the transitions of the function's and the
argument's rule instances, keeps the meaning, and charges fewer ticks than the derivation has
rule instances. -/
def skipStep (lib : List Term) (s : State) : Step :=
  match s.control with
  | .eval (.app (.lam _ b) (.nat k)) env => .next ⟨.eval b (.nat k :: env), s.stack, s.depth⟩
  | _ => step lib s

end Nanodregg.Lang.Need
