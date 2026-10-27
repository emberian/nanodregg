/-
# Lang.Eval — the one evaluator: a small-step CEK machine under a tick budget (DECISIONS LANG-2)

Call-by-value, except record fields: `record` and `extend` SUSPEND their fields (a field is a
term with its environment) and `get` forces the selected one, so `{good = 7, bad = self.bad}.good`
is `7`. `fix t` with `t : R → R` evaluates to the knot `knot body env`; selecting from a knot
applies `t`'s body to the knot itself, so the knot is the final self of open recursion. There is
no heap and no update: a field is re-evaluated at every selection (the known cost, LANG-2).

`step` is one transition, and one transition is one tick. Its work is bounded by the term node it
looks at (a `record` suspends its fields in one step), the environment index it reads (`env[i]?` is
O(i)) and, for `extend`, the two rows it merges; all three are bounded by
`Wire.depthMax`/`Wire.rowMax`, not by a theorem. A primitive that walks bytes (`beq`, `deq`, `cat`)
walks up to 128 KiB, so it is charged per word (LANG-64): its `primR` frame counts the ticks paid
(`primTicks`, one per `Bounds.wordBytes` its operands hold), and only the last of them computes it.
A budget that runs out while a primitive is paying for its bytes has walked none of them, and a run
walks at most `wordBytes` primitive operand bytes per tick it is charged (`Lang.Proofs.Cost.walked_le`,
measured by `walked`). `run` is the only loop: at most `fuel` steps, a stack
of at most `stackMax` frames (carried as `depth`, so the bound costs nothing per step), and it
reports the exact number of steps it took. Every way a run can end is a named `Fault` or a value;
`Lang.Proofs.Sound` proves a checked program never reaches `stuck` and that only a primitive faults;
`Lang.Proofs.Run` that a final outcome is independent of any extra fuel.
-/
import Lang.Bounds
import Lang.Term
import Codec.Varint

namespace Nanodregg.Lang

/-- Runtime values. A field is suspended: a term with the environment it was written in. -/
inductive Val
  | nat (value : Nat)
  | bool (value : Bool)
  | bytes (value : ByteArray)
  | digest (value : ByteArray)
  | clo (body : Term) (env : List Val)
  | record (fields : List (Label × (Term × List Val)))
  /-- The fixed point of `lam _ body` closed over `env`: selecting from it runs `body` with the
  knot itself as the bound variable. -/
  | knot (body : Term) (env : List Val)
  | inj (label : Label) (payload : Val)
  deriving Inhabited

abbrev Env := List Val

/-- What to do with the value being computed. -/
inductive Frame
  /-- the function is being computed; the argument is next -/
  | appL (arg : Term) (env : Env)
  /-- the argument is being computed; then enter the function -/
  | appR (fn : Val)
  | fix
  | primL (p : Prim) (right : Term) (env : Env)
  /-- the right operand is being computed; then the primitive, after `paid` of its `primTicks`
  are paid (LANG-64) -/
  | primR (p : Prim) (left : Val) (paid : Nat)
  | get (label : Label)
  | extend (fields : List (Label × Term)) (env : Env)
  | inj (label : Label)
  | case (arms : List (Label × Term)) (env : Env)
  | ite (whenTrue whenFalse : Term) (env : Env)
  deriving Inhabited

inductive Control
  | eval (t : Term) (env : Env)
  | ret (v : Val)
  deriving Inhabited

/-- `depth` is the stack's length, carried so the bound check is O(1) (`Lang.Proofs.Sound.step_depth`). -/
structure State where
  control : Control
  stack : List Frame
  depth : Nat
  deriving Inhabited

/-- How a run ends without a value, by name (law 7). -/
inductive Fault
  /-- no transition applies: a type error; never reached by a checked program -/
  | stuck
  /-- an arithmetic result is not below `Bounds.natLimit` -/
  | overflow
  /-- `sub` below zero -/
  | underflow
  | divZero
  /-- `cat` beyond `Bounds.bytesMax` -/
  | tooLarge
  /-- the tick budget is spent -/
  | ticks
  /-- the stack bound is reached -/
  | stack
  /-- the program refused, by the name it wrote (`Term.refuse`, LANG-51) -/
  | refused (why : ByteArray)
  deriving DecidableEq

instance : Repr Fault where
  reprPrec f _ := match f with
    | .stuck => "Fault.stuck" | .overflow => "Fault.overflow" | .underflow => "Fault.underflow"
    | .divZero => "Fault.divZero" | .tooLarge => "Fault.tooLarge" | .ticks => "Fault.ticks"
    | .stack => "Fault.stack" | .refused w => s!"Fault.refused {w.toList}"

inductive Step
  | next (s : State)
  | halt (v : Val)
  | fault (f : Fault)
  deriving Inhabited

def natResult (n : Nat) : Except Fault Val :=
  if n < Bounds.natLimit then .ok (.nat n) else .error .overflow

/-- A payload writer's result (LANG-87): the bytes it wrote, within `bytesMax`, else `tooLarge`. -/
def appended (r : ByteArray) : Except Fault Val :=
  if r.size ≤ Bounds.bytesMax then .ok (.bytes r) else .error .tooLarge

/-- One primitive on two values. Wrong-shaped operands are `stuck`. -/
def primEval : Prim → Val → Val → Except Fault Val
  | .add, .nat a, .nat b => natResult (a + b)
  | .sub, .nat a, .nat b => if b ≤ a then .ok (.nat (a - b)) else .error .underflow
  | .mul, .nat a, .nat b => natResult (a * b)
  | .div, .nat a, .nat b => if b = 0 then .error .divZero else .ok (.nat (a / b))
  | .mod, .nat a, .nat b => if b = 0 then .error .divZero else .ok (.nat (a % b))
  | .eq, .nat a, .nat b => .ok (.bool (decide (a = b)))
  | .lt, .nat a, .nat b => .ok (.bool (decide (a < b)))
  | .le, .nat a, .nat b => .ok (.bool (decide (a ≤ b)))
  | .beq, .bytes a, .bytes b => .ok (.bool (decide (a = b)))
  | .deq, .digest a, .digest b => .ok (.bool (decide (a = b)))
  | .lenLe, .bytes a, .nat n => .ok (.bool (decide (a.size ≤ n)))
  | .cat, .bytes a, .bytes b =>
      if a.size + b.size ≤ Bounds.bytesMax then .ok (.bytes (a ++ b)) else .error .tooLarge
  | .u64be, .bytes a, .nat n => appended (Codec.Stream.u64be.put (UInt64.ofNat n) a)
  | .sized, .bytes a, .bytes s => appended (Codec.Stream.putVarint s.size a ++ s)
  | .dsized, .bytes a, .digest d => appended (Codec.Stream.putVarint d.size a ++ d)
  | _, _, _ => .error .stuck

/-- The operand bytes a primitive walks (LANG-64), read off the compiled machine: `beq` and `deq`
decide `a = b` on `ByteArray`, which compares the two `data` arrays, and each `data` is built from
its byte string (`lean_byte_array_data`): both operands are copied whatever their sizes. `cat`
copies both into the result (`a ++ b` is `copySlice`; a shared `a` is copied first). A `cat` past
`bytesMax` refuses on the sizes alone and walks nothing. A payload writer (LANG-87) copies its
buffer and writes its payload: charged the size of its result (`written`), nothing when it refuses.
Every other primitive walks no bytes: naturals are below `2^64` and `lenLe` reads a size. -/
def primBytes : Prim → Val → Val → Nat
  | .beq, .bytes a, .bytes b | .deq, .digest a, .digest b => a.size + b.size
  | .cat, .bytes a, .bytes b => if a.size + b.size ≤ Bounds.bytesMax then a.size + b.size else 0
  | .u64be, .bytes a, .nat n => written (Codec.Stream.u64be.put (UInt64.ofNat n) a)
  | .sized, .bytes a, .bytes s => written (Codec.Stream.putVarint s.size a ++ s)
  | .dsized, .bytes a, .digest d => written (Codec.Stream.putVarint d.size a ++ d)
  | _, _, _ => 0
where
  /-- The bytes a writer is charged: its result's size when it is within `bytesMax`. -/
  written (r : ByteArray) : Nat := if r.size ≤ Bounds.bytesMax then r.size else 0

/-- The ticks a primitive is charged (LANG-64): one per `Bounds.wordBytes` it walks, rounded up
(`⌈n / 32⌉` for `n ≥ 1` bytes), and one when it walks none. A primitive on at most one word of
bytes costs one tick, as every primitive did before LANG-64; a 64 KiB `cat` costs 2048. -/
def primTicks (p : Prim) (x y : Val) : Nat :=
  (primBytes p x y - 1) / Bounds.wordBytes + 1

/-- Suspend each field in one environment. -/
def suspend (env : Env) (fs : List (Label × Term)) : List (Label × (Term × Env)) :=
  fs.map fun f => (f.1, (f.2, env))

/-- Push a frame; the depth moves with the stack. -/
@[inline] def push (s : State) (c : Control) (f : Frame) : Step :=
  .next ⟨c, f :: s.stack, s.depth + 1⟩

/-- The transition at a primitive with operands `a` and `v`, `paid` of its ticks paid, on the
stack `k` below its frame: before its last tick it pays one more and waits; on its last it
computes. So its bytes are walked only once every tick for them is paid. -/
def primStep (k : List Frame) (d : Nat) (p : Prim) (a v : Val) (paid : Nat) : Step :=
  if paid + 1 < primTicks p a v then .next ⟨.ret v, .primR p a (paid + 1) :: k, d⟩
  else
    match primEval p a v with
    | .ok r => .next ⟨.ret r, k, d - 1⟩
    | .error e => .fault e

/-- One transition. `lib` is the closure's package bodies, indexed by `ref`. -/
def step (lib : List Term) (s : State) : Step :=
  match s.control with
  | .eval t env =>
    match t with
    | .var i =>
        match env[i]? with
        | some v => .next { s with control := .ret v }
        | none => .fault .stuck
    | .lam _ b => .next { s with control := .ret (.clo b env) }
    | .app f a => push s (.eval f env) (.appL a env)
    | .fix t => push s (.eval t env) .fix
    | .nat n => .next { s with control := .ret (.nat n) }
    | .bool b => .next { s with control := .ret (.bool b) }
    | .bytes b => .next { s with control := .ret (.bytes b) }
    | .digest b => .next { s with control := .ret (.digest b) }
    | .prim p a b => push s (.eval a env) (.primL p b env)
    | .record fs => .next { s with control := .ret (.record (suspend env fs)) }
    | .get t ℓ => push s (.eval t env) (.get ℓ)
    | .extend t fs => push s (.eval t env) (.extend fs env)
    | .inj _ ℓ t => push s (.eval t env) (.inj ℓ)
    | .case t arms => push s (.eval t env) (.case arms env)
    | .ite c a b => push s (.eval c env) (.ite a b env)
    | .ref i =>
        match lib[i]? with
        | some body => .next { s with control := .eval body [] }
        | none => .fault .stuck
    | .refuse _ why => .fault (.refused why)
    | .hole _ _ => .fault (.refused "holeUnresolved".toUTF8)
  | .ret v =>
    match s.stack with
    | [] => .halt v
    | f :: k =>
      let pop (c : Control) : Step := .next ⟨c, k, s.depth - 1⟩
      match f with
      | .appL a env => .next ⟨.eval a env, .appR v :: k, s.depth⟩
      | .appR fn =>
          match fn with
          | .clo body cenv => pop (.eval body (v :: cenv))
          | _ => .fault .stuck
      | .fix =>
          match v with
          | .clo body cenv => pop (.ret (.knot body cenv))
          | _ => .fault .stuck
      | .primL p b env => .next ⟨.eval b env, .primR p v 0 :: k, s.depth⟩
      | .primR p a paid => primStep k s.depth p a v paid
      | .get ℓ =>
          match v with
          | .record fs =>
              match Row.find? ℓ fs with
              | some (t, env) => pop (.eval t env)
              | none => .fault .stuck
          | .knot body env => .next ⟨.eval body (v :: env), s.stack, s.depth⟩
          | _ => .fault .stuck
      | .extend fs env =>
          match v with
          | .record gs => pop (.ret (.record (Row.merge gs (suspend env fs))))
          | .knot body kenv => .next ⟨.eval body (v :: kenv), s.stack, s.depth⟩
          | _ => .fault .stuck
      | .inj ℓ => pop (.ret (.inj ℓ v))
      | .case arms env =>
          match v with
          | .inj ℓ w =>
              match Row.find? ℓ arms with
              | some body => pop (.eval body (w :: env))
              | none => .fault .stuck
          | _ => .fault .stuck
      | .ite a b env =>
          match v with
          | .bool true => pop (.eval a env)
          | .bool false => pop (.eval b env)
          | _ => .fault .stuck

/-- How a run ended, with the exact number of steps it took. -/
inductive Outcome
  | value (v : Val) (used : Nat)
  | fault (f : Fault) (used : Nat)
  deriving Inhabited

def Outcome.used : Outcome → Nat
  | .value _ u | .fault _ u => u

/-- At most `fuel` steps from `s`, with at most `stackMax` frames; `used` counts the steps
already taken (the loop is tail-recursive). Running out of fuel is the fault `ticks`. -/
def run (lib : List Term) (stackMax : Nat) : (fuel used : Nat) → State → Outcome
  | 0, used, _ => .fault .ticks used
  | fuel + 1, used, s =>
      match step lib s with
      | .halt v => .value v (used + 1)
      | .fault f => .fault f (used + 1)
      | .next s' =>
          if stackMax < s'.depth then .fault .stack (used + 1)
          else run lib stackMax fuel (used + 1) s'

/-- Whether a transition from a primitive's frame with `paid` ticks paid, over `below` frames, only
paid one more: it left a primitive's frame with `paid + 1` on top of `below` frames. -/
def Step.pays (paid below : Nat) : Step → Bool
  | .next ⟨.ret _, .primR _ _ j :: k, _⟩ => j == paid + 1 && k.length == below
  | _ => false

/-- The bytes the transition of `st` from `s` walks (LANG-64), read off what the transition does: a
transition from a primitive's frame that does anything but pay one more tick (it computes, faults,
or pops) walks the primitive's operands; every other transition walks none. A measure for
`Lang.Proofs.Cost`, not run by the machine. -/
def stepBytesBy (st : State → Step) (s : State) : Nat :=
  match s with
  | ⟨.ret v, .primR p a paid :: k, _⟩ => if (st s).pays paid k.length then 0 else primBytes p a v
  | _ => 0

/-- The primitive operand bytes a run of the stepper `st` walks within `fuel` transitions from `s`,
under the stack bound: `stepBytesBy` summed along the transitions `run`'s loop takes. -/
def walkedBy (st : State → Step) (stackMax : Nat) : (fuel : Nat) → State → Nat
  | 0, _ => 0
  | fuel + 1, s =>
      stepBytesBy st s +
        match st s with
        | .next s' => if stackMax < s'.depth then 0 else walkedBy st stackMax fuel s'
        | _ => 0

/-- The primitive operand bytes the deployed machine walks: `walkedBy (step lib)`. -/
abbrev walked (lib : List Term) (stackMax : Nat) : (fuel : Nat) → State → Nat :=
  walkedBy (step lib) stackMax

/-- The machine about to evaluate a closed term. -/
def State.init (t : Term) (env : Env := []) : State := ⟨.eval t env, [], 0⟩

/-- Run a term to its end under `ticks`, with the consensus stack bound. -/
def eval (lib : List Term) (ticks : Nat) (t : Term) (env : Env := []) : Outcome :=
  run lib Bounds.stackMax ticks 0 (State.init t env)

end Nanodregg.Lang
