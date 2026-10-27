# 4 Execution

This chapter defines how a term runs, how a package is installed and loaded, how a method runs, how laws and guards judge, and how holes are filled.
§4.1 to §4.4 define the machine and its tick accounting.
§4.5 to §4.9 define the runtime the kernel calls through its program interface (`Kernel/Receive/Call.lean` `structure Program`).
§4.10 defines the contextual semantics.

## 4.1 Runtime structure

Values and environments are those of §2.10.

```
frame φ   ::= appL t E          the function is being computed; the argument t is next
            | appR v            the argument is being computed; then enter the closure v
            | fix               the record transformer is being computed
            | primL p t E       the left operand is being computed; the right t is next
            | primR p v j       the right operand is being computed; j ticks of p paid
            | get ℓ             select field ℓ of the value
            | extend fs E       override and extend the value with fields fs in E
            | inj ℓ             inject the value at ℓ
            | case arms E       case on the value
            | ite t₁ t₂ E       branch on the value
control C ::= eval t E | ret v
state   s ::= ⟨C | K⟩           K a stack of frames; its depth |K| is carried with it
fault   f ::= stuck | overflow | underflow | divZero | tooLarge | ticks | stack | refused b
outcome   ::= value v n | fault f n          n the number of transitions taken
```

Lean: `Lang/Eval.lean` `inductive Frame`, `inductive Control`, `structure State`, `inductive Fault`, `inductive Outcome`.

A *closure library* `lib` is the list of the closure's package bodies, indexed as `ref` indexes them (§4.5).
The machine reads it and never changes it.

## 4.2 The machine

The machine is a CEK machine: call by value, except that record fields are *suspended*.
A record value pairs each field's term with the environment it was written in, and selecting a field evaluates it then.
There is no heap and no update: a field is evaluated at every selection.

One transition is one *tick*.
`step lib s` is the transition function (`Lang/Eval.lean` `step`).
Each rule below is one case of it.
A state that matches no rule ends the run with `fault stuck`.

### 4.2.1 Evaluating a term

```
⟨eval (var i) E | K⟩          ↪ ⟨ret E[i] | K⟩                         E-Var
⟨eval (lam τ t) E | K⟩        ↪ ⟨ret (clo t E) | K⟩                    E-Lam
⟨eval (app f a) E | K⟩        ↪ ⟨eval f E | appL a E :: K⟩             E-App
⟨eval (fix t) E | K⟩          ↪ ⟨eval t E | fix :: K⟩                  E-Fix
⟨eval (nat n) E | K⟩          ↪ ⟨ret (nat n) | K⟩                      E-Lit
⟨eval (prim p a b) E | K⟩     ↪ ⟨eval a E | primL p b E :: K⟩          E-Prim
⟨eval (record fs) E | K⟩      ↪ ⟨ret (record [(ℓ, (t, E)) | (ℓ = t) ∈ fs]) | K⟩    E-Record
⟨eval (get t ℓ) E | K⟩        ↪ ⟨eval t E | get ℓ :: K⟩                E-Get
⟨eval (extend t fs) E | K⟩    ↪ ⟨eval t E | extend fs E :: K⟩          E-Extend
⟨eval (inj τ ℓ t) E | K⟩      ↪ ⟨eval t E | inj ℓ :: K⟩                E-Inj
⟨eval (case t arms) E | K⟩    ↪ ⟨eval t E | case arms E :: K⟩          E-Case
⟨eval (ite c a b) E | K⟩      ↪ ⟨eval c E | ite a b E :: K⟩            E-Ite
⟨eval (ref i) E | K⟩          ↪ ⟨eval lib[i] [] | K⟩                   E-Ref
⟨eval (refuse τ b) E | K⟩     ↪ fault (refused b)                      E-Refuse
⟨eval (hole n σ) E | K⟩       ↪ fault (refused "holeUnresolved")       E-Hole
```

E-Lit also covers `bool`, `bytes` and `digest` literals.
E-Var with `i` past `E`, and E-Ref with `i` past `lib`, are `stuck`.

* A variable returns its value from the environment.
* A function returns a closure over the current environment.
* A record returns at once, its fields unevaluated.
* `ref i` evaluates the `i`-th body of the library in the empty environment: a package body is closed.
* `refuse τ b` ends the run with the fault `refused b`.
* A hole that preparation did not replace ends the run with `refused "holeUnresolved"`.
  A prepared package has no hole terms left (§4.10).

### 4.2.2 Returning a value

```
⟨ret v | []⟩                          ↪ halt v                                       R-Halt
⟨ret v | appL a E :: K⟩               ↪ ⟨eval a E | appR v :: K⟩                     R-AppL
⟨ret w | appR (clo t E) :: K⟩         ↪ ⟨eval t (w :: E) | K⟩                        R-AppR
⟨ret (clo t E) | fix :: K⟩            ↪ ⟨ret (knot t E) | K⟩                         R-Fix
⟨ret v | primL p b E :: K⟩            ↪ ⟨eval b E | primR p v 0 :: K⟩                R-PrimL
⟨ret w | primR p v j :: K⟩            ↪ ⟨ret w | primR p v (j+1) :: K⟩   if j+1 < ticks(p,v,w)                   R-PrimPay
⟨ret w | primR p v j :: K⟩            ↪ ⟨ret r | K⟩     if j+1 ≥ ticks(p,v,w), primEval p v w = ok r          R-PrimOk
⟨ret w | primR p v j :: K⟩            ↪ fault f         if j+1 ≥ ticks(p,v,w), primEval p v w = error f       R-PrimFault
⟨ret (record fs) | get ℓ :: K⟩        ↪ ⟨eval t E | K⟩                    where fs(ℓ) = (t, E)                  R-Get
⟨ret (knot t E) | get ℓ :: K⟩         ↪ ⟨eval t (knot t E :: E) | get ℓ :: K⟩                                  R-GetKnot
⟨ret (record gs) | extend fs E :: K⟩  ↪ ⟨ret (record (gs ⊕ [(ℓ, (t, E)) | (ℓ = t) ∈ fs])) | K⟩              R-Extend
⟨ret (knot t E') | extend fs E :: K⟩  ↪ ⟨eval t (knot t E' :: E') | extend fs E :: K⟩                        R-ExtendKnot
⟨ret v | inj ℓ :: K⟩                  ↪ ⟨ret (inj ℓ v) | K⟩                                                     R-Inj
⟨ret (inj ℓ w) | case arms E :: K⟩    ↪ ⟨eval b (w :: E) | K⟩             where arms(ℓ) = b                     R-Case
⟨ret (bool true) | ite a b E :: K⟩    ↪ ⟨eval a E | K⟩                                                          R-IteT
⟨ret (bool false) | ite a b E :: K⟩   ↪ ⟨eval b E | K⟩                                                          R-IteF
```

* A value returned to an empty stack is the run's value.
* Application evaluates the function, then the argument, then the closure's body with the argument bound at index 0.
* `fix` turns a closure `clo t E` into the knot `knot t E`.
* Selecting from a knot evaluates the knot's body with the knot itself bound, and keeps the `get` frame: the body's record is then selected from.
  So the knot is the final self of open recursion.
* `extend` of a record merges the new suspended fields into the old ones (`Row.merge`).
  `extend` of a knot unrolls the knot once and merges into the result, so the inherited fields keep the old self (LANG-18; `Lang/Proofs/BigStep.lean` `bigStep_extend_keeps_old_self`).
* A primitive's frame first pays its ticks one at a time (§4.3), then computes.

## 4.3 Primitive cost

A primitive that walks bytes is charged one tick per 32 bytes it walks, and pays every tick before it walks any byte (LANG-64).

```
bytes(beq, b₁, b₂) = |b₁| + |b₂|          bytes(deq, d₁, d₂) = |d₁| + |d₂|
bytes(cat, b₁, b₂) = |b₁| + |b₂|  if |b₁| + |b₂| ≤ Bounds.bytesMax, else 0
bytes(w, b, x)     = |w(b, x)|    if |w(b, x)| ≤ Bounds.bytesMax, else 0      for a payload writer w
bytes(p, v, w)     = 0            for every other primitive

ticks(p, v, w) = ⌊(bytes(p, v, w) − 1) / Bounds.wordBytes⌋ + 1        Bounds.wordBytes = 32
```

Lean: `Lang/Eval.lean` `primBytes`, `primTicks`, `primStep`.

`bytes(…) − 1` is truncated subtraction, so a primitive that walks no bytes costs one tick, and one that walks `n ≥ 1` bytes costs `⌈n/32⌉`.
A `cat` or a payload writer whose result would pass `Bounds.bytesMax` walks nothing and faults `tooLarge` on its one tick.
A 64 KiB `cat` costs 2048 ticks.

**Theorem** (`Lang/Proofs/Cost.lean` `walked_le`).
The primitive operand bytes a run walks are at most `Bounds.wordBytes` times the ticks it took.
So one tick does at most a bounded amount of byte work.

## 4.4 Runs

```
run lib cap 0 u s       = fault ticks u
run lib cap (n+1) u s   = value v (u+1)                 if s ↪ halt v
                        = fault f (u+1)                 if s ↪ fault f
                        = fault stack (u+1)             if s ↪ s' and cap < |K(s')|
                        = run lib cap n (u+1) s'        if s ↪ s' and |K(s')| ≤ cap
eval lib n t E          = run lib Bounds.stackMax n 0 ⟨eval t E | []⟩
```

Lean: `Lang/Eval.lean` `run`, `eval`, `State.init`.

1. A run takes at most `n` transitions, its *budget*.
2. Running out of budget is the fault `ticks`, printed `exhausted`.
3. A transition that would leave more than `Bounds.stackMax` = 4096 frames is the fault `stack`.
4. The outcome reports the exact number of transitions taken, the halting one included.

`Bounds.stackMax` is a consensus constant, not part of a budget.

### 4.4.1 Extraction

A value leaves the machine as data only by *extraction* at a data type (`Lang/Data.lean` `Machine.extract`).

1. A scalar extracts as itself at its type.
2. At `rec ρ`, a knot is first unrolled, each unrolling a run of the knot's body; then each field of `ρ`, in row order, is forced by a run of its suspended term and extracted at its type.
3. At `sum ρ`, an `inj ℓ w` extracts `w` at `ρ(ℓ)`.
4. Any other value at a type is `stuck`.

Every forcing run spends from the budget the run left.
So extraction is metered like the run, and a field that diverges exhausts the budget instead of hanging.

### 4.4.2 What a run can end with

| fault | printed | cause |
|---|---|---|
| `stuck` | `stuck` | no rule applies; a checked program never reaches it |
| `overflow` | `overflow` | `add` or `mul` reaches `2^64` |
| `underflow` | `underflow` | `sub` below zero |
| `divZero` | `divZero` | `div` or `mod` by zero |
| `tooLarge` | `tooLarge` | `cat` or a payload writer past `Bounds.bytesMax` |
| `ticks` | `exhausted` | the budget is spent |
| `stack` | `stack` | the stack bound is passed |
| `refused b` | `refused b` | the run reached `refuse τ b`, or a blocked hole |

Lean: `Lang/Eval.lean` `Fault`; `Lang/Program.lean` `faultText`.

### 4.4.3 Theorems about runs

**Theorem** (`Lang/Proofs/Sound.lean` `checked_never_stuck`).
If every body of `lib` checks at its closure type and `t` checks at `τ`, then `eval lib n t []` ends with a value of type `τ` or with a fault other than `stuck`, for every budget `n`.

**Theorem** (`Lang/Proofs/Run.lean` `run_agree`).
Two runs of the same state that both end within their budgets end with the same outcome.
So a final outcome does not depend on how much budget beyond its need was given.

**Theorem** (`Lang/Proofs/Agree.lean` `run_bigStep`, `run_fault_bigStep`).
A value the machine ends with is the term's meaning under the reference semantics `BigStep`; so is every fault other than `stuck`, `ticks` and `stack`.

**Theorem** (`Lang/Proofs/Complete.lean` `bigStep_run`).
Every value meaning is reached by the machine for every large enough stack bound and budget.

**Theorem** (`Lang/Proofs/BigStep.lean` `bigStep_deterministic`).
A term has at most one meaning.

`BigStep` (`Lang/Proofs/BigStep.lean`) is a big-step semantics with one rule per former and one per place a fault arises.
It shares the value domain with the machine and is independent of its control.

## 4.5 Installing and loading

### 4.5.1 Reading a package cell

A package cell is read through the caller's pinned view (`Lang/Program.lean` `readPackage`).

1. The id must be pinned, or the call is refused `unpinned`.
2. The cell must be a package cell with the read-only discipline and a slot 0 that decodes as a package (§5), or `malformedCell`.

A read-only cell never changes once born (`Kernel/Proofs/Frame.lean` `fold_rom`), so a package read at one World is the package read at every later World.

### 4.5.2 Loading a closure

`load look fuel id acc` loads package `id` and its import closure into the accumulated closure `acc`, each package once (`loadUsing`).

1. A package already in `acc` returns its index.
2. With no fuel left the load is refused `imports too deep`.
3. The id bytes must be a digest of the World (`import is not a digest`).
4. Read the package cell (§4.5.1).
5. Load each import in order with one less fuel; this yields the imports' closure indices `gis`.
6. *Admit* the package against its imports' interfaces (below), and append it with its body *relocated*: each `ref i` in it becomes `ref gis[i]`.

A run loads with fuel `closureDepthMax` = 8.
Install loads the new package's imports with fuel 7, so an installed package can itself be loaded.

*Admission* re-checks the package every time it is loaded (LANG-16).
A package without holes is admitted by `checkWith` and the digest-literal check (§3.7.3).
A package with holes is admitted by `checkContextual` (§3.7.4), then *prepared* into a closed body, which must check at the interface; only the prepared body enters the library, and the loaded closure keeps the original package (`admitContextual`).

There are three preparers:

| load | used by | a hole becomes |
|---|---|---|
| `loadContextual` | install, laws | `refuse τ "holeUnresolved"` (`unresolvedBody`) |
| `loadLive` | a method run | the selected candidate, or a typed refusal naming the failure (§4.10) |
| `load` | closed loads | (refuses a package with holes) |

### 4.5.3 Install

`checkInstall look b` (`Lang/Program.lean`):

1. Decode `b` as a package (§5), or `program "decode …"`.
2. Load its imports with `loadContextual` at fuel 7.
3. Admit the package with `admitContextual` against the imports' interfaces.

The kernel's `install` receiver calls it and bears a read-only package cell holding `b` at its content id (`Kernel/Receive/Derive.lean` `install`).
A generated package, returned in an object's `install` or `createOf` call, takes the same path.

## 4.6 Running a method

The kernel's `invoke` receiver calls `run look rv pkg state method args req budget` (`Lang/Program.lean` `program`, `runMeasuredLive`).
`look` is the caller's pinned view and `rv` its pinned rows.

### 4.6.1 Setup

`runSetupLive` (`runSetupWith` with `loadLive`):

1. The request must fit the language's data: digests at most 32 bytes, window ends below `2^64`, occasion within bounds (`reqOk`), or `request out of bounds`.
2. Load the closure of `pkg` with `loadLive`: every contextual package of the closure is prepared from the caller's rows (§4.10).
3. Resolve the method: `methods[method]` is its label `ℓ` (`no method N`), and the interface field `ℓ` has a method signature (§3.5).
4. Read the state: field `i` of the state record lives in slot `stateBase + i` and decodes at its type; every digest in it must be a digest of the World (`state field ℓ missing`, `state field ℓ: …`).
5. Decode the argument bytes at the method's argument type, and check its digests (`arguments: …`).
6. Build the *rows* argument from the caller's pinned rows and signed ranges under the object's own relations, and under its peer when the method declares a peer read (`methodReads`, `Lang/Rel.lean` `readsData`).
7. The term is `get (ref g) ℓ` applied to the rows, the state, the argument and the request, in that order (`apply4`); the environment holds them as data turned to values.

### 4.6.2 The run

```
prep = Σ over the closure's packages P of  holeCharge(P, m_P)        Package.preparationCost
holeCharge(P, m) = 0                                  if P has no holes
                 = nodes(body P) × (m + 1) + 256 × |holes P|   otherwise
```

`m_P` is the largest node count among `P`'s committed candidates, and 256 is `Bounds.holeGuardFuel`.

1. If `prep` exceeds the budget, the run is refused `holeTicks`.
2. Run the term with budget `budget − prep`.
   A fault `f` refuses the run `program "ℓ: f"`, with `ticks` printed `exhausted`.
3. Extract the value at the method's result type under the budget left (§4.4.1).
4. Lay the extracted state record out as slots: field `i` at `stateBase + i`, each in the data encoding of its type (§5.6).
5. Read the calls (§4.7.1), check the grade (§4.7.2), read the edits (§4.7.3), run the guards (§4.9), check held value (§4.7.4).
6. Return the new state's slots, the calls, the row edits, and the ticks used, `budget − left`, preparation included.

The kernel then checks, in order (`Kernel/Receive/Derive.lean` `invoke`):

1. the ticks used are at most the fuel it gave, `min(budget, pool)` (`overTicks`);
2. every row edit is under the invoked object (`rowParent`);
3. the new state is canonical (`stateKey`);
4. every law in force admits the old and the new state on the occasion `invoke method` (§4.8);
5. there are at most `callsMax` = 8 calls (`tooManyCalls`);
6. it derives each returned call, depth first, as the invoked object (§4.8.3).

## 4.7 Calls, grades, edits and held value

### 4.7.1 Calls

Each call slot `cᵢ` holds `inj none` or `inj some δ` at its declared call type.
`callsOf` reads each `some` as a kernel call, in slot order (`Lang/Call.lean`).

* An `invoke` arm's `args` value is encoded at the slot's argument type, the encoding the callee decodes at its own argument type (LANG-77).
* A `createOf` arm's `state` is laid out as state slots, as a birth's seed is (LANG-96).
* An `install` arm's `pkg` is passed to the kernel's install as it is.
* A digest field must be a digest of the World, or `program "calls: cI FIELD: not a digest"`.

Every call `callsOf` returns is of a kind an object may make (`Lang/Proofs/Call.lean` `callsOf_callable`).

### 4.7.2 Grades

```
moves(calls) = Σ amount over the transfer and credit calls
moves(calls) ≤ grade(ℓ).moves     else  program "effectExceeded moves M past N"
```

Lean: `Lang/Call.lean` `movesOf`, `checkMoves`.

**Theorem** (`Lang/Proofs/Effect.lean` `runMeasured_moves_le`).
A method run that succeeds returned calls whose moved value is at most the method's grade.

### 4.7.3 Edits

Each edit slot `eᵢ` holds `inj none` or `inj some (inj ℓ e)`, an edit `e` of relation `ℓ` (`Lang/Rel.lean` `editsOf`).

| edit | row act | requirement |
|---|---|---|
| `insert {key, val}` | insert at a free key | none on the pin |
| `upsert {key, val}` | replace the row the caller pinned, present or absent | the row is pinned |
| `retract {key}` | remove the row the caller pinned | the relation allows retraction (`edits: eI: ℓ is insert-only`) |

The key's bytes are its data encoding in declared order (§5.6); the value's bytes are its data encoding at the relation's value type.
The kernel judges each act against the rows (`Kernel/World.lean` `rowStepOn`; [`kernel.md`](../reference/kernel.md)).

### 4.7.4 Held value

For a relation with `holds f`, each row holds the `leg` in its field `f` (LANG-90).

1. For each edit, the new row's leg must be moved *into* the object's account of its asset, and the replaced or retracted row's leg moved *out*.
2. Sum what the edits need per asset; compare with what the calls move into and out of `self`'s account of that asset.
3. A shortfall in is `program "legUnfunded REL"`; a shortfall out is `program "legStranded REL"`.

Lean: `Lang/Rel.lean` `legsOf`, `checkLegs`; theorem `Lang/Proofs/Holds.lean` `checkLegs_backed`.

## 4.8 Laws

### 4.8.1 Judging

`judge look pkg laws old new req` runs every law in force: the laws of the object's package, then the laws of each extra law package, in order (`Lang/Program.lean` `judgeContextual`).
For each law package:

1. The request must fit (`request out of bounds`).
2. Load the package with `loadContextual`: holes are typed refusals.
3. Read `old` and `new` at *that* package's state type (`lawDenied LAW "state field …"`).
4. For each law label `ℓ` of the package, in order, run the law (below).
   `refused r` refuses the call `lawDenied LAW "ℓ: r"`; a fault `f` refuses it `lawDenied LAW "ℓ: f"`.

A law runs by `runLaw` (`Lang/Law.lean`):

```
runLaw lib t δ_old δ_new δ_req:
  run   app (app (app t (var 2)) (var 1)) (var 0)   in env [req, new, old]   with budget lawTicks
  extract the value at verdict under the budget left
  inj ok _          → admitted
  inj refused b     → refused b
```

`lawTicks` = 100000 is a consensus constant: the caller cannot buy more of it.

**Theorem** (`Lang/Proofs/LawRun.lean` `runLaw_never_stuck`).
A law of a loaded package never ends `stuck`.

### 4.8.2 Which act presents which occasion

The kernel's receivers present these occasions ([`kernel.md`](../reference/kernel.md); `Kernel/Receive/Derive.lean`):

| act | object | occasion | old | new | laws that judge |
|---|---|---|---|---|---|
| `create` / `createOf` | any | `birth` | seed | seed | the package's and the extra laws |
| `write` | data object | `write` | state | state with the edits | the extra laws |
| `law laws'` | data object | `relaw laws'` | state | state | the laws in force |
| `law laws'` | data object | `adopt laws'` | state | state | each incoming law not already in force |
| `invoke m` | programmed object | `invoke m` | state before | state the method returned | the package's and the extra laws |
| `retire` | object | `retire` | last state | last state | the package's and the extra laws |

A programmed object's package and laws never change: `write` and `law` on it are refused `hasMethods`.
A law that refuses `retire` makes its object permanent.
A law replacement is judged twice: by the outgoing regime as `relaw`, and by each incoming law as `adopt` (KERNEL-27, LANG-24).

### 4.8.3 Nested calls

The kernel derives the calls a method returned depth first, each *as the invoked object* (KERNEL-28).
A nested call's request has `caller = some o` for the object `o` whose run returned it; a member's call has `caller = none` (KERNEL-76).
An object already invoked in the call's tree is refused `revisited`.
A call nested more than `Kernel.Bounds.callDepthMax` = 4 levels below the signed call is refused `callTooDeep`.
Every method run in the tree draws from one tick pool: the signed `invoke`'s budget, capped at `Kernel.Bounds.treeTicksMax` = 131072 (`Kernel/Receive/Derive.lean` `poolOf`).
A signed call of any other kind has a pool of 0.
Laws and guards do not draw from the pool: each runs under its own `lawTicks`.
The ticks the tree used count against the signer's tick meter for the window ([`kernel.md`](../reference/kernel.md)).
The whole tree is one Turn: a refused nested call refuses the call, and no earlier effect of the tree is committed.

## 4.9 Guards

For each edit a run returned, in order, the guard of its relation, if it declares one, judges it (`Lang/Program.lean` `guardEdits`).

1. First find every edit's *old row*: the row at the edit's key as the caller pinned it, `none` for a pinned-absent row or an unpinned insert.
   An upsert or retract whose row the caller did not pin is refused `rowUnpinned` with the parent, relation and key, before any guard runs.
2. Run the guard `S → req → rec (edit, old) → verdict` by `runLaw` on the state before the run, the request, and the edit with its old row.
3. `refused r` refuses the run `lawDenied PKG "g: r"`; a fault refuses it `lawDenied PKG "g: f"`.

A guard's work is proportional to the number of edits, never to the relation's size.

## 4.10 The contextual semantics

This section defines how a method run fills a package's holes.
All of it happens in the method's setup (§4.6.1, step 2), against the caller's pinned view `look` and pinned rows `rv`.
None of it reads anything else.

### 4.10.1 Supports

A support *holds* on the caller's view by these rules (`Lang/LiveHoles.lean` `supportLive`):

```
rv(self, r, k) = row with version v'     v' = v
─────────────────────────────────────────────── Sup-Row
row r k v holds

look(d) = live cell                     look(d) = live cell c     l ∈ lawslots(c)
────────────────── Sup-Cell             ──────────────────────────────────────── Sup-Law
cell d holds                            cellLaw d l holds

look(d) = live cell c     package(c) = q
──────────────────────────────────────── Sup-Package
cellPackage d q holds
```

A cell support is *observed* when the caller pinned its cell, live, as a tombstone or absent (`supportObserved`).
A row is read through `holeRow`, which tells a row the caller did not pin from a row the caller pinned absent.
A tombstone, an absence and an unpinned cell are not live.
A row support holds only at exactly the version the ROM names.

### 4.10.2 Selection

`selectHole look rv self h` (`Lang/LiveHoles.lean`) selects hole `h`'s candidate.

1. Read the selection row `(h.selection.rel, h.selection.key)` of `self` from the caller's pins.
   If the caller did not pin it: `holeUnpinnedRow REL KEY`.
   If it is pinned absent: `holeSelectionAbsent n`.
2. Decode its value as a natural `i`, or `holeSelectionType n`.
3. Take candidate `c = code[i]`, or `holeSelectionIndex n`.
4. Every cell support of `c` must be observed, or `holeUnpinned π…` naming every unobserved one.
5. Every row support of `c` must be pinned, or `holeSupportUnpinned n π…` naming every one whose row the caller did not pin.
6. Every row support of `c` must hold, or `holeDerivationMoved n π…` naming every one that moved or is pinned absent.
7. Every support of `c` must hold, or `holeSupportDead n π…` naming every cell support that is not live.
8. For each context position `x` with a support hypothesis `π`:
   `π` must be pinned (`holeUnpinnedRow REL KEY` for a row, `holeUnpinned π` for a cell);
   if `π` holds, keep `x`;
   if `π` does not hold and `c` uses variable `x`, refuse `holeSupportMoved n x π`;
   if `π` does not hold and `c` does not use `x`, *strengthen* `x` away.
9. The guard pin, if any, must be pinned, as in step 8; run the guard on whether it holds (`true` with no pin), under `Bounds.holeGuardFuel` = 256 ticks.
   `false` is `holeGuardBlocked n`; a fault or a non-boolean is `holeGuardFault n`.
10. Factor the candidate over the kept positions and re-embed it at the original context (`factorHole`, `reembed`).
   The result is the filling.

A refusal names its coordinates as `row:REL:KEYHEX:VER`, `cell:IDHEX`, `cellLaw:IDHEX:LAWHEX` or `cellPackage:IDHEX:PKGHEX` (`SupportPin.wire`).
The checks run in the order above and stop at the first failing step.
The coordinates a refusal lists are every failure of that step, not of later steps.

### 4.10.3 Resolution and preparation

```
selectHole h = ok s                           selectHole h = error e
───────────────────────────── Res-Sel         ───────────────────────────────────── Res-Block
resolve h = s.body                            resolve h = refuse τ_h (wire e)
```

Lean: `resolveHole`, `HoleResolution.body`.

`instantiateHoles look rv self Δ P` prepares package `P` for one invocation (`Lang/LiveHoles.lean`):

1. Check `P` contextually against `Δ` (§3.7.4).
2. Resolve every hole.
3. Replace each `hole n σ` in the body by its resolution under `σ` (`Term.fillBounded`), within `Wire.nodeMax` nodes (`holeWorkBound`, `holeSizeBound`).
4. Every digest literal of the result must come from the body or a selected candidate (`holeProvenance`).
5. The result must check closed at the interface (`holeInstanceType`).

The prepared body is used for this invocation only; nothing is installed or stored.
The selection is recomputed at every invocation from the rows the caller pins.

### 4.10.4 Demand

A blocked hole is a `refuse` term.
It ends the run only if the run evaluates it: by E-Refuse, its refusal is the run's fault `refused "holeSupportDead 0 cell:…"`.
A hole in a record field the run never selects, or in a branch it never takes, does not end the run.

**Theorem** (`Lang/Proofs/LiveHoles.lean` `blocked_step`).
A blocked resolution's body takes one transition, to the fault `refused` with the wire form of its refusal.

### 4.10.5 Repair

When a support dies, the selection that cites it stops selecting: every later invocation that demands the hole is refused with the support's name.
A retired cell stays a tombstone (`Kernel/Proofs/Versions.lean` `stale_behind_forever`), so a candidate that cites a retired cell never selects again.
A `cellLaw` or `cellPackage` support can hold again if the cell's law list changes back.

Repair is a new selection: a call that writes another index into the selection row, under the object's methods and laws.
Nothing selects an alternative candidate automatically.
The README's program does this with its `choose` method (rows RM8 to RM11 of `Lang/Journey/Readme.lean`).

### 4.10.6 Theorems

**Theorem** (`selectHole_origin`).
A successful selection is the candidate the pinned selection row names, and every support of that candidate holds on the caller's view.

**Theorem** (`selectHole_cell_support`, `selectHole_contract_support`).
Every cell support of a selected candidate names a cell that is live in the caller's view; every `cellLaw` support's cell has the law in its law slots, and every `cellPackage` support's cell runs the package.

**Theorem** (`selectHole_hypotheses`).
A context position is strengthened away exactly when its hypothesis does not hold, and then the candidate does not use it.

**Theorem** (`selectHole_factor`).
The factored filling is typed at the strengthened context, and re-embedding it gives back the committed candidate exactly.

**Theorem** (`selectHole_live_selects`).
If the selection row names candidate `i`, every support of `i` is observed and holds, every hypothesis is observed and holds where `i` uses it, and the guard returns `true`, then selection succeeds with index `i`.

**Theorem** (`revoked_support_refused`).
If the selected candidate has a cell support whose cell is pinned absent or as a tombstone, selection fails and the hole has no receipt.

**Theorem** (`instantiateHoles_typed`, `instantiateHoles_sources`).
A prepared body is closed, typed at the package's interface, and within `Wire.nodeMax` nodes; its digest literals come from the body and the selected candidates.

These are statements about one invocation.
No top claim of `Spec/` yet lifts them to histories; that statement is in flight (§1.6).

## 4.11 Refusal names of execution

A method run, a law or a guard refuses a call with the kernel's `program` refusal or its `lawDenied` refusal, carrying text whose first token is a name.

| text | raised by |
|---|---|
| `request out of bounds` | §4.6.1 step 1, §4.8.1 step 1 |
| `imports too deep`, `import is not a digest`, `closure` | §4.5.2 |
| `decode …` | §4.5.3 |
| `no method N`, `no method ℓ`, `method ℓ` | §4.6.1 step 3 |
| `state field ℓ missing`, `state field ℓ: …` | §4.6.1 step 4 |
| `arguments: …` | §4.6.1 step 5 |
| `peer: no pair`, `peer: samePeer`, `peer: notParty`, `peer: not a digest`, `peer: another package` | §4.6.1 step 6 |
| `holeTicks` | §4.6.2 step 1 |
| `ℓ: FAULT` | §4.6.2 step 2, §4.4.2 |
| `ℓ: state`, `ℓ: state bytes` | §4.6.2 steps 3 and 4 |
| `calls: …` | §4.7.1 |
| `effectExceeded moves M past N` | §4.7.2 |
| `edits: …`, `old: …` | §4.7.3, §4.9 |
| `rowUnpinned` | §4.9 step 1 |
| `legUnfunded REL`, `legStranded REL` | §4.7.4 |
| `lawDenied LAW "ℓ: REASON"` | §4.8.1, §4.9 |
| `hole…` | §4.10.2, §4.10.3; the full list is in chapter 6 |
| `notDigest` | §3.7, §4.5.2 |
