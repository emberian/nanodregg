# 3 Validation

A term is *valid* when it has a type under the typing relation of this chapter.
A package is *valid* when it passes the install check of §3.7.
The kernel runs no package that is not valid: install refuses it, and every later load re-checks it (§4.5).

The typing relation is `Lang/Proofs/Typing.lean` `HasType`.
Nothing deployed runs it.
The deployed checker is the function `Lang/Check.lean` `inferE`, and §3.4 states the theorem that the two agree.

## 3.1 Well-formed types

```
───────────  ───────────  ────────────  ─────────────
⊢ nat wf     ⊢ bool wf    ⊢ bytes wf    ⊢ digest wf

⊢ τ₁ wf    ⊢ τ₂ wf          ρ canonical    ⊢ τ wf for each (ℓ : τ) ∈ ρ
──────────────────          ──────────────────────────────────────────
  ⊢ τ₁ → τ₂ wf                     ⊢ rec ρ wf        ⊢ sum ρ wf
```

Lean: `Lang/Ty.lean` `Ty.wf`, `Ty.rowWf`.

A type is well formed when every row in it has strictly ascending labels.
The checker requires a well-formed type wherever a term carries one: the domain of `lam`, the sum of `inj`, the type of `refuse`.
Every type the checker infers is then well formed (`Lang/Proofs/Canon.lean` `hasType_wf`, `infer_wf`).

## 3.2 Contexts

A typing judgement has three contexts.

* `Δ`, the *closure context*: the interface types of the packages in the closure, so `ref i` has type `Δ[i]`.
* `Γ`, the *local context*: the types of the enclosing binders, nearest first, so `var i` has type `Γ[i]`.
* `Ω`, the *hole signature*: the package's hole declarations (§2.5).

`Ω(n)` is the first declaration in `Ω` named `n` (`List.find?`).

## 3.3 Typing rules

There is one rule for each term former.
Three auxiliary judgements type a record's fields, a case's arms and a hole's substitution.

### Variables and functions

```
Γ[i] = τ
────────────────────  T-Var    HasType.var
Δ; Γ ⊢_Ω var i : τ
```

`var i` has the type at index `i` of the local context.
A variable past the context has no type.

```
⊢ A wf     Δ; A :: Γ ⊢_Ω t : B
──────────────────────────────  T-Lam    HasType.lam
Δ; Γ ⊢_Ω lam A t : A → B
```

`lam A t` has type `A → B` when `A` is well formed and `t` has type `B` with a variable of type `A` bound at index 0.

```
Δ; Γ ⊢_Ω f : A → B     Δ; Γ ⊢_Ω a : A
──────────────────────────────────────  T-App    HasType.app
Δ; Γ ⊢_Ω app f a : B
```

An application has the function's result type when the argument has exactly the function's parameter type.

```
Δ; Γ ⊢_Ω t : rec ρ → rec ρ
──────────────────────────  T-Fix    HasType.fix
Δ; Γ ⊢_Ω fix t : rec ρ
```

`fix t` has type `rec ρ` when `t` maps `rec ρ` to the same `rec ρ`.
Only a record transformer has a fixed point.

### Literals and primitives

```
n < Bounds.natLimit                         |b| ≤ Bounds.bytesMax
──────────────────────  T-Nat               ─────────────────────────  T-Bytes
Δ; Γ ⊢_Ω nat n : nat                        Δ; Γ ⊢_Ω bytes b : bytes

                                            |d| ≤ Bounds.digestBytesMax
──────────────────────  T-Bool              ───────────────────────────  T-Digest
Δ; Γ ⊢_Ω bool b : bool                      Δ; Γ ⊢_Ω digest d : digest
```

Lean: `HasType.nat`, `HasType.bool`, `HasType.bytes`, `HasType.digest`.

A literal is in bounds or has no type.
So every value a checked program starts from is in bounds.
A digest literal is also checked to be a digest of the World when its package is installed and at every load (§4.5).

```
Δ; Γ ⊢_Ω t₁ : left(p)     Δ; Γ ⊢_Ω t₂ : right(p)
─────────────────────────────────────────────────  T-Prim    HasType.prim
Δ; Γ ⊢_Ω prim p t₁ t₂ : result(p)
```

`left`, `right` and `result` are the columns of the table in §2.3 (`Prim.left`, `Prim.right`, `Prim.result`).

### Records

```
fs canonical     Δ; Γ ⊢_Ω fs :: ρ
──────────────────────────────────  T-Record    HasType.record
Δ; Γ ⊢_Ω record fs : rec ρ

Δ; Γ ⊢_Ω t : rec ρ     ρ(ℓ) = τ
───────────────────────────────  T-Get    HasType.get
Δ; Γ ⊢_Ω get t ℓ : τ

Δ; Γ ⊢_Ω t : rec ρ     fs canonical     Δ; Γ ⊢_Ω fs :: ρ'
─────────────────────────────────────────────────────────  T-Extend    HasType.extend
Δ; Γ ⊢_Ω extend t fs : rec (ρ ⊕ ρ')
```

The fields judgement types a list of fields as a row, label for label, in order:

```
──────────────────  F-Nil    FieldsTy.nil
Δ; Γ ⊢_Ω [] :: []

Δ; Γ ⊢_Ω t : τ     Δ; Γ ⊢_Ω fs :: ρ
────────────────────────────────────────  F-Cons    FieldsTy.cons
Δ; Γ ⊢_Ω (ℓ = t) :: fs :: (ℓ : τ) :: ρ
```

A record literal's fields must be in canonical order.
`extend` overrides and extends: a field of `fs` replaces the field of the same label in `ρ`, in place, and a new label is inserted in order (`Row.merge`).
An overriding field may change the field's type.

### Sums

```
⊢ sum ρ wf     ρ(ℓ) = A     Δ; Γ ⊢_Ω t : A
──────────────────────────────────────────  T-Inj    HasType.inj
Δ; Γ ⊢_Ω inj (sum ρ) ℓ t : sum ρ

Δ; Γ ⊢_Ω t : sum ρ     Δ; Γ ⊢_Ω arms :: ρ ⇒ B
─────────────────────────────────────────────  T-Case    HasType.case
Δ; Γ ⊢_Ω case t arms : B
```

An injection carries its sum type, so its type is not inferred from context.
The arms judgement requires one arm per arm of the sum, with the same labels in the same order, at least one, each body at the common type `B` with the payload bound at index 0:

```
Δ; A :: Γ ⊢_Ω b : B
─────────────────────────────────────  A-One    ArmsTy.one
Δ; Γ ⊢_Ω [(ℓ ⇒ b)] :: [(ℓ : A)] ⇒ B

Δ; A :: Γ ⊢_Ω b : B     Δ; Γ ⊢_Ω arms :: ρ ⇒ B     arms ≠ []
──────────────────────────────────────────────────────────────  A-Cons    ArmsTy.cons
Δ; Γ ⊢_Ω (ℓ ⇒ b) :: arms :: (ℓ : A) :: ρ ⇒ B
```

So a `case` is exhaustive and has no default arm.
A `case` on the empty sum has no type.

### Control

```
Δ; Γ ⊢_Ω c : bool     Δ; Γ ⊢_Ω t₁ : τ     Δ; Γ ⊢_Ω t₂ : τ
─────────────────────────────────────────────────────────  T-Ite    HasType.ite
Δ; Γ ⊢_Ω ite c t₁ t₂ : τ

⊢ τ wf     reasonOk(b)
────────────────────────  T-Refuse    HasType.refuse
Δ; Γ ⊢_Ω refuse τ b : τ
```

`refuse τ b` has any well-formed type the author names.
Its reason `b` must be a *name*: at most `Bounds.reasonMax` = 256 bytes of UTF-8 with no control character (`Lang/Bounds.lean` `reasonOk`).
So the name a run is refused by prints on one line, as written.

### Packages and holes

```
Δ[i] = τ
────────────────────  T-Ref    HasType.ref
Δ; Γ ⊢_Ω ref i : τ
```

`ref i` has the interface type of the `i`-th package of the closure.

```
Ω(n) = hole n : [Ψ ⊢ τ]     Δ; Γ ⊢_Ω σ :: Ψ
────────────────────────────────────────────  T-Hole    HasType.hole
Δ; Γ ⊢_Ω hole n σ : τ
```

A hole has its declared type when its substitution supplies a term of each type of its context, in order, exactly as many:

```
──────────────────  S-Nil    SubstTy.nil
Δ; Γ ⊢_Ω [] :: []

Δ; Γ ⊢_Ω t : A     Δ; Γ ⊢_Ω σ :: Ψ
───────────────────────────────────  S-Cons    SubstTy.cons
Δ; Γ ⊢_Ω t :: σ :: A :: Ψ
```

The substitution's terms are typed in the hole's surroundings `Γ`; the filling is typed in the hole's context `Ψ` (§3.6).
This is the contextual-substitution discipline of Nanevski, Pfenning and Pientka: a filling checked once at `Ψ` is valid under every substitution for `Ψ` (§3.8).

## 3.4 The checker

`inferE Δ Γ t Ω` returns the type of `t` or the rule it breaks (`Lang/Check.lean`).
It is syntax-directed: one case per former, the same premises as the rule, checked left to right.
Its work is the size of `t` times the size of the types it compares.

**Theorem** (`Lang/Proofs/Check.lean` `inferE_iff_live`).
For all `Δ`, `Γ`, `Ω`, `t` and `τ`: `inferE Δ Γ t Ω = ok τ` if and only if `Δ; Γ ⊢_Ω t : τ`.

**Theorem** (`hasType_unique_live`).
A term has at most one type: `Δ; Γ ⊢_Ω t : A` and `Δ; Γ ⊢_Ω t : B` imply `A = B`.

**Theorem** (`check_iff_live`).
`check Δ t τ Ω = true` if and only if `Δ; [] ⊢_Ω t : τ`.

When `inferE` refuses, it names the rule and the path from `t` to the subterm, outermost segment first (LANG-27).
The path's segments are `body` (under `lam`), `fn` and `arg`, `fix`, `left` and `right`, a field or arm label, `target`, `cond`, `then` and `else`, and `substitution`.
The wire form is `NAME @a.b.c`, or `NAME @top` at the root (`TypeErr.text`).

| name | the rule it breaks |
|---|---|
| `unbound` | T-Var: index past `Γ` |
| `noPackage` | T-Ref: index past `Δ` |
| `noHole` | T-Hole: no declaration of that name in `Ω` |
| `holeSubstitution` | S-Nil/S-Cons: the substitution and the context differ in length |
| `badType` | T-Lam, T-Inj, T-Refuse: an annotation is not well formed |
| `notFunction` | T-App: the function's type is not a function type |
| `argument` | T-App: the argument's type differs from the parameter type; S-Cons: a substitution term's type differs from its context type |
| `notSelfMap` | T-Fix: not `rec ρ → rec ρ` |
| `natRange`, `bytesRange`, `digestRange` | T-Nat, T-Bytes, T-Digest: a literal out of bounds |
| `badReason` | T-Refuse: the reason is not a name |
| `operands` | T-Prim: an operand's type differs from the primitive's |
| `notCanonical` | T-Record, T-Extend: field labels not strictly ascending |
| `notRecord` | T-Get, T-Extend: the target is not a record |
| `noField` | T-Get: the record has no such field |
| `notSum` | T-Inj: the annotation is not a sum; T-Case: the scrutinee is not a sum |
| `noArm` | T-Inj: the sum has no such arm |
| `payload` | T-Inj: the payload's type differs from the arm's |
| `arms` | A-One/A-Cons: the arms do not follow the sum's labels one for one |
| `armType` | A-Cons: two arms have different types |
| `condition` | T-Ite: the condition is not `bool` |
| `branches` | T-Ite: the branches have different types |
| `declared` | `checkE`: the term's type is not the declared one |

Lean: `Lang/Check.lean` `inductive TypeError`, `TypeError.name`.

## 3.5 Method, law and guard shapes

The install check reads a method's type back as a *signature* (`Lang/Package.lean` `methodSig`, `structure Sig`): its argument type, its call slot types, its reads and its number of edit slots.
A field of interface type `τ` is a *method* over state `S` and relations `rels` when all of these hold:

1. `τ = R → S → A → req → rec (calls : rec κs) (edits : rec es) (state : S)`;
2. `A` is a data type;
3. `κs` has at most `Kernel.Bounds.callsMax` = 8 entries, labelled `c0`, `c1`, … in order, each `opt κ` for a call type `κ` (`callSlotsOf`);
4. `es` has at most `editsMax` = 8 entries, labelled `e0`, `e1`, … in order, each `opt E` for the package's edit type `E` (`editSlotsOf`);
5. `R` is exactly the rows type of its declared reads (`rowsOf`, which rebuilds the type from the reads it finds and compares);
6. a method that reads a peer names `pair` in its argument (`pairNamed`);
7. a method that reads a receipt column has `receipt : bytes` in its argument.

A type `κ` is a *call type* when it is a sum of at least one of the arms of §2.9.4, each at exactly its type; an `invoke` arm's argument type is data the wire can carry, and a `createOf` arm's state type is a record of such data (`callSlotOk`, `invokeArgOk`, `createStateOk`).

A field is a *law* over `S` when its type is exactly `S → S → req → verdict` (`lawTy`).

A relation's guard is a field of type exactly `S → req → rec (edit : reledit) (old : opt val) → verdict` (`guardTy`).

## 3.6 Hole declarations

A package's ROM holes are checked against the closure context `Δ` of its imports.

```
⊢ τ' wf for each τ' ∈ Ψ     ⊢ τ wf
|hypotheses| = |Ψ|
|code| ≤ Bounds.holeCandidatesMax
[]; [bool] ⊢_[] guard : bool
Δ; Ψ ⊢_[] c.body : τ for each c ∈ code
──────────────────────────────────────────  H-Rom    HoleROM.check
Δ ⊢ (hole n [Ψ ⊢ τ], code, …, guard) ok
```

Lean: `Lang/LiveHoles.lean` `HoleROM.check`.

1. The context and the type are well formed, or the declaration is refused `holeType n`.
2. There is one hypothesis per context position, or `holeContext n`.
3. There are at most `Bounds.holeCandidatesMax` = 64 candidates, or `holeCandidates n`.
4. The guard has type `bool` with one free variable of type `bool`, no closure and no holes, or `holeGuardType n`.
5. Every candidate, selected or not, has type `τ` in context `Ψ` under the package's closure, with no holes, or `holeCandidateType n i` for candidate `i`.

A candidate is checked once, at install, at its declared context.
It cannot introduce another hole: candidates are typed under the empty signature.

## 3.7 The install check

The install check decides whether a package's bytes may become a package cell.
It is the tail of the loader every run uses (§4.5): `Lang/Program.lean` `checkInstall`.

### 3.7.1 Shape

```
|imports| ≤ 16     |methods| ≤ 64     |laws| ≤ 16     |claims| ≤ 16
state = rec ρ with ⊢ rec ρ wf and rec ρ data
⊢ iface wf
──────────────────────────────────────────────────────────────────  P-Shape    Package.checkShape
⊢ P shaped
```

Refusals, in the order checked: `tooManyImports`, `tooManyMethods`, `tooManyLaws`, `tooManyClaims`, `stateNotData`, `ifaceNotRecord`.

### 3.7.2 Fields

With `iface = rec ρ`, the fields check runs these checks in order (`Package.checkFields`):

1. **Relations** (`checkRels`): at most `relsMax` = 8 relations (`tooManyRels`), labels ascending and each a label (`badRel`).
   For each relation: a nonempty key of at most 8 fixed-width fields with labels, its record type well formed, its width at a 32-byte digest at most `Kernel.Bounds.keyBytesMax` = 128 bytes (`relKey ℓ`); a well-formed data value type the wire carries, `1 ≤ limit ≤ Kernel.Bounds.rowsPerRelationMax` = 4096, with no sum column `cap = 0`, and with a sum column `0 < cap < 2^64` and the column a natural field of the value, a held field that is a `leg` field of the value, a guard that is an interface field of guard type, and a label other than `peer` (`badRel ℓ`).
2. **Methods** (`checkMethods`): each label in `methods` is a field of `ρ` (`noMethod ℓ`) of method shape (§3.5).
   A field of the wrong shape is refused by the most specific name that applies: `liveNotCellKeyed ℓ` (a live read of a relation not keyed by one digest), `peerNotNamed ℓ`, `receiptRead ℓ`, otherwise `badMethod ℓ`.
3. **Grades** (`checkEffects`): the `effects` entries ascend and each names a method (`badEffect ℓ`); a method whose type has a `transfer` or `credit` arm in any call slot has a grade above 0 (`effectExceeded ℓ`).
4. **Laws** (`checkLaws`): each label in `laws` is a field of `ρ` (`noLaw ℓ`) of type `lawTy S` (`badLaw ℓ`).
5. **Claims** (`checkClaims`, §3.9).

### 3.7.3 A package without holes

```
⊢ P shaped     Δ; [] ⊢_[] body : iface     holes = []     ⊢ τ wf for each τ ∈ Δ     fields ok
────────────────────────────────────────────────────────────────────────────────────────────────  P-Closed    Package.checkWith
Δ ⊢ P ok
```

Order: shape; then the body at the interface (`illTyped NAME @path`); then `contextualSignature` if the package has holes; then `importType` if an import's interface is not well formed; then the fields.
The install check then requires every digest literal of the body to be a digest of the World (`notDigest`, `Program.checkLits`).

### 3.7.4 A package with holes

```
⊢ P shaped     fields ok     |holes| ≤ 16     hole names distinct
Δ ⊢ h ok for each h ∈ holes
Δ; [] ⊢_Ω body : iface     where Ω = the holes' declarations
──────────────────────────────────────────────────────────────  P-Contextual    Package.checkContextual
Δ ⊢ P ok
```

Lean: `Lang/LiveHoles.lean` `Package.checkContextual`, `Lang/HoleROM.lean` `holeSignature`.

Refusals: a shape or field refusal as above; `holeSignatureBound`; `holeDuplicate`; the hole refusals of §3.6; `holeBodyType NAME @path`.
The hole signature is the only thing typing sees of a hole: its name, context and type.
A candidate's behaviour is not part of the package's type (LANG-75.8).

Install then *prepares* the package without a row view: every hole becomes `refuse τ "holeUnresolved"` (`unresolvedBody`), and the prepared body must check closed at the interface (`holeInstanceType`).
Every digest in the body, in every candidate, in the guard and in every cell a support names must be a digest of the World (`notDigest`, `checkROMLits`).

### 3.7.5 Imports

Install decodes the bytes (§5), then loads the import closure: each import's cell is pinned by the signer, is a package cell, decodes, and is admitted by the same check at its own holes, at most `closureDepthMax` = 8 levels deep (§4.5).
The package is then checked against its imports' interfaces in order, as `Δ`.

**Theorem** (`Lang/Proofs/LiveHoles.lean` `install_loads`).
If the install check of bytes `b` succeeds on a view, and that view holds a read-only package cell whose slot 0 is `b`, then the contextual load of that cell succeeds on the same view and yields the package `b` decodes to.
So no package installs only to fail its own load.

## 3.8 Contextual substitution

**Theorem** (`Lang/Proofs/Fill.lean` `fillHoles_typed`).
Let `σ` map hole names to terms.
If every filling `σ(n) = M` for a declaration `hole n : [Ψ ⊢ τ]` in `Ω` has `Δ; Ψ ⊢_[] M : τ`, and every declaration `σ` leaves unfilled is also in `Ω'`, then `Δ; Γ ⊢_Ω t : τ` implies `Δ; Γ ⊢_Ω' fillRefs σ t : τ`.

This is Theorem 4.3 of Nanevski, Pfenning and Pientka (TOCL 2008) for the substitution fragment.
It says a filling typed at its declared context preserves the type of any term containing the hole.
It does not say which filling the World supplies; §4.10 does.

## 3.9 Claims

A claim `keeps inv law` is checked against the package's own term (`Lang/Package.lean` `checkClaim`).

1. `law` is one of the package's laws, or `claimNotLaw law`.
2. `inv` is an interface field of type `S → bool`, or `claimNotInvariant inv`.
3. The body is a record literal holding `inv` as a literal `lam S i` and `law` as a literal `lam S (lam S (lam req b))`, or `claimShape law`.
4. Every `ok` leaf of `b` is guarded by the invariant applied to `new`, or `claimUnproved law`.

*Guarded* is the judgement `guardedBy I k r t` with `I = lam S i`, `k` the index of `new` and `r` the index of `req`, starting at `k = 1`, `r = 0` (`Lang/Claim.lean` `Term.guardedBy`):

```
c = app I (var k)   or   guardedBy I k r t₁        guardedBy I k r t₂
───────────────────────────────────────────────────────────────────  G-Ite
guardedBy I k r (ite c t₁ t₂)

occ = (s = get (var r) occasion)
for each arm (ℓ ⇒ b): (occ and ℓ = relaw) or guardedBy I (k+1) (r+1) b
─────────────────────────────────────────────────────────────────────  G-Case
guardedBy I k r (case s arms)

ℓ ≠ ok                                     
──────────────────────────  G-Inj          ───────────────────────────  G-Refuse
guardedBy I k r (inj τ ℓ t)                guardedBy I k r (refuse τ b)
```

No other former is guarded.
So in a law in certifying shape, every path to `ok` passes the test `I new` on its true branch, or lies in the `relaw` arm of a case on the occasion.
The `relaw` arm is excepted because a law replacement leaves the state unchanged.
The walk is linear in the law's size and unmetered, as the type check is.

**Theorem** (`Lang/Proofs/Claim.lean` `guardedBy_sound`).
If `guardedBy (lam S i) k r t` and `t` evaluates to `inj ok w` in environment `E` under the reference semantics, then `i` holds of `E[k]`, or `t` read a `relaw` occasion at index `r`.

**Theorem** (`keeps_step`, `chain_keeps`).
A law in certifying shape that admits a request whose occasion is not `relaw` leaves a state the invariant holds of; along any chain of steps the law admits, every state keeps the invariant once the first does.

**Theorem** (`install_claims`).
If the install check admits bytes that decode to `P`, then every claim `keeps inv law` of `P` is borne by `P`'s body in the sense of steps 1 to 4.

**Theorem** (`Kernel/Proofs/Logic/Claims.lean` `object_history_keeps`).
For a package that bears `keeps inv law` with a law term that references no package (`NoRef`), every state along an object history in which that law is in force keeps the invariant, once the first state does.

A claim is part of the package's bytes and so of its id: a package cannot gain or lose a claim without becoming another package (LANG-93).

## 3.10 Grades

A grade is checked twice.
Install checks it against the type: a method whose call slots name `transfer` or `credit` has `moves > 0` (§3.7.2).
The run checks it against the calls the method returned (§4.7).
