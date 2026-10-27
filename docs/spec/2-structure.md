# 2 Structure

This chapter gives the abstract syntax of every construct.
Each section gives the grammar, the core text that writes it (`Lang/Read.lean`), and the Lean type it restates.

## 2.1 Values

The language computes with four kinds of scalar.

| kind | domain | bound | Lean |
|---|---|---|---|
| natural | `0 ≤ n < 2^64` | `Bounds.natLimit` = 18446744073709551616 | `Lang/Bounds.lean` |
| boolean | `true`, `false` | | |
| byte string | at most 65536 bytes | `Bounds.bytesMax` = `Kernel.Bounds.valueBytesMax` | `Lang/Bounds.lean` |
| digest | at most 32 bytes | `Bounds.digestBytesMax` = 32 | `Lang/Bounds.lean` |

A *digest* is an id by which the kernel names a cell or a member.
Whether a byte string is a digest is decided by the World's digest decoder, `digestOf`, where an id enters a run; in the deployed system a digest is exactly 32 bytes (`Codec/Digest.lean` `Digest.ofBytes?`).
No primitive makes a digest from bytes, and `deq` is the only primitive that reads one (LANG-38).

## 2.2 Types

```
type τ ::= nat
         | bool
         | bytes
         | digest
         | τ₁ → τ₂                     function
         | rec ρ                       record over the row ρ of types
         | sum ρ                       sum over the row ρ of types
row  ρ ::= (ℓ₁ : τ₁) … (ℓₙ : τₙ)
```

Lean: `Lang/Ty.lean` `inductive Ty` (constructors `nat`, `bool`, `bytes`, `digest`, `fn`, `record`, `sum`).

The core text writes `nat`, `bool`, `bytes`, `digest`, `(-> τ₁ τ₂)`, `(rec (ℓ τ)…)` and `(sum (ℓ τ)…)`.
The reader sorts the entries of a `rec` or `sum` by label, so text may list them in any order.

There are no type variables, no subtyping and no quantities.
Two types are equal exactly when they are the same syntax (`Ty.beq`, which decides `DecidableEq Ty`).

A type is *well formed*, `⊢ τ wf`, when every row in it is canonical (`Ty.wf`).

A type is *data* when it contains no function type (`Ty.isData`).
State, method arguments, row values, verdicts and every value that crosses between a run and the World are data.

Three abbreviations recur:

```
opt τ   = sum (none : rec) (some : τ)                      Lang/Package.lean  optTy
verdict = sum (ok : rec) (refused : bytes)                 Lang/Package.lean  verdictTy
leg     = rec (amount : nat) (asset : digest)              Lang/Package.lean  legTy
```

`rec` with an empty row is written `rec` and is the unit type.

## 2.3 Primitives

A primitive is a strict binary operation.

| primitive | core text | left | right | result | meaning |
|---|---|---|---|---|---|
| `add` | `+` | nat | nat | nat | sum; past `2^64` faults `overflow` |
| `sub` | `-` | nat | nat | nat | difference; below 0 faults `underflow` |
| `mul` | `*` | nat | nat | nat | product; past `2^64` faults `overflow` |
| `div` | `/` | nat | nat | nat | floor quotient; by 0 faults `divZero` |
| `mod` | `%` | nat | nat | nat | remainder; by 0 faults `divZero` |
| `eq` | `==` | nat | nat | bool | equality |
| `lt` | `<` | nat | nat | bool | less than |
| `le` | `<=` | nat | nat | bool | at most |
| `beq` | `beq` | bytes | bytes | bool | byte equality |
| `cat` | `cat` | bytes | bytes | bytes | concatenation; past `Bounds.bytesMax` faults `tooLarge` |
| `deq` | `deq` | digest | digest | bool | digest equality |
| `lenLe` | `len<=` | bytes | nat | bool | the left operand has at most `n` bytes |
| `u64be` | `u64be` | bytes | nat | bytes | append the natural's eight big-endian bytes |
| `sized` | `sized` | bytes | bytes | bytes | append the right operand as a varint length and its bytes |
| `dsized` | `dsized` | bytes | digest | bytes | append the digest as a varint length and its bytes |

Lean: `Lang/Term.lean` `inductive Prim`, `Prim.left`, `Prim.right`, `Prim.result`; the meaning is `Lang/Eval.lean` `primEval`.

The last three are the *payload writers* (LANG-87).
Each appends to its left operand the codec's spelling of its right operand, so a run can write the bytes of a package tree (§2.12).
A digest enters a byte string only through `dsized`, as a length-prefixed payload.
Each faults `tooLarge` when its result would pass `Bounds.bytesMax`.

## 2.4 Terms

```
term t ::= var i                        variable, de Bruijn index i
         | lam τ t                      function with parameter type τ
         | app t₁ t₂                    application
         | fix t                        fixed point of a record transformer
         | nat n | bool b | bytes b | digest d     literals
         | prim p t₁ t₂                 primitive p
         | record (ℓ₁ = t₁) … (ℓₙ = tₙ)  record of suspended fields
         | get t ℓ                      field selection
         | extend t (ℓ₁ = t₁) … (ℓₙ = tₙ)  override and extend a record
         | inj τ ℓ t                    injection into the sum τ at ℓ
         | case t (ℓ₁ ⇒ t₁) … (ℓₙ ⇒ tₙ)   case analysis; arm k binds the payload
         | ite t₀ t₁ t₂                 conditional
         | ref i                        the i-th package of the closure
         | refuse τ b                   end the run, refused by the name b
         | hole n (t₁ … tₖ)             hole n under an explicit substitution
```

Lean: `Lang/Term.lean` `inductive Term`, eighteen constructors.

| construct | core text |
|---|---|
| `var i` | a name bound by an enclosing binder |
| `lam τ t` | `(lam x τ t)` |
| curried `lam` | `(fn (x₁ τ₁) … (xₖ τₖ) t)` |
| `app (lam τ t₂) t₁` | `(let x τ t₁ t₂)` |
| `app t₁ t₂` | `(t₁ t₂)`; `(f a₁ … aₖ)` applies left to right |
| `fix t` | `(fix t)` |
| `nat n` | a decimal numeral |
| `bool b` | `true`, `false` |
| `bytes b` | `"text"` (UTF-8) or `#hex` |
| `digest d` | `(digest #hex)` |
| `prim p t₁ t₂` | `(OP t₁ t₂)` with `OP` from §2.3 |
| `record …` | `(record (ℓ t)…)` |
| `get t ℓ` | `(. t ℓ)` |
| `extend t …` | `(extend t (ℓ t)…)` |
| `inj τ ℓ t` | `(inj τ ℓ t)` |
| `case t …` | `(case t (ℓ x t)…)`, where `x` names the payload |
| `ite t₀ t₁ t₂` | `(if t₀ t₁ t₂)` |
| `ref i` | `(ref i)` |
| `refuse τ b` | `(refuse τ "why")` or `(refuse τ #hex)` |
| `hole n (t…)` | `(hole n (subst t…))` |

The reader resolves names to de Bruijn indices: index 0 is the nearest binder.
It sorts the fields of `record` and `extend` and the arms of `case` by label.
A binder may not be named like a literal, a head word or a primitive; such a name is refused `reservedBinder` (`Lang/Read.lean` `binder`).

Three properties of the terms are fixed by their syntax:

* A `record` field and an `extend` field are *suspended*: the machine evaluates a field when it is selected, never before (§4.2).
* `fix t` with `t : rec ρ → rec ρ` is the final self of open recursion: selecting a field of the fixed point runs `t`'s body with the fixed point bound as its parameter.
  Mixin composition `λself. λsuper. u self (l self super)` is a term the authoring tool writes, not a construct.
* A `refuse` reason is a literal, so the name a run is refused by is fixed in the text (LANG-51).

## 2.5 Holes

A *hole declaration* gives a hole's name, its local context and its type:

```
holedecl  ::= hole n : [Ψ ⊢ τ]          Ψ a list of types
signature Ω ::= holedecl*
```

Lean: `Lang/HoleDecl.lean` `structure HoleDecl` (`name`, `ctx`, `ty`); `Lang/Check.lean` `HoleSignature`.

A term `hole n (t₁ … tₖ)` refers to the declaration of `n` in `Ω` and supplies one term for each type of its context.

A package declares its holes in *read-only memory* (ROM): with the declaration, the package commits every candidate filling and the facts each candidate relies on.

```
holerom   ::= { name n, context Ψ, type τ,
                code c₁ … cₘ,                         candidates, 0 ≤ m ≤ 64
                selection (r, k),                     relation index r, key bytes k
                hypotheses h₁ … h_|Ψ|,                one per context position
                guardpin g?, guard t }
candidate c ::= { body t, supports π* }
hypothesis h ::= structural | π
support  π ::= row r k v                              the object's row (r, k) at version v
             | cell d                                 cell d is live
             | cellLaw d l                            cell d is live and law l is among its laws
             | cellPackage d q                        cell d is live and runs package q
```

Lean: `Lang/HoleROM.lean` `structure HoleROM`, `structure HoleCode`, `inductive SupportPin`.

* A candidate's body is a term typed at the hole's context `Ψ` and type `τ`.
* The *selection* is a row of the object itself: relation index `r`, key bytes `k`.
  Its value is a natural, the index of the selected candidate.
* A *hypothesis* belongs to a context position.
  A `structural` hypothesis is an assumption the selection never checks; a support hypothesis must hold if the selected candidate uses that position's variable.
* The *guard* is a term of type `bool` with one free variable of type `bool`, bound to whether the guard pin holds; with no guard pin, it is bound to `true`.

The core text of a ROM declaration is

```
(hole n (context τ…) (result τ) (selection r #k) (hypotheses h…)
  (guard g t) (code (candidate t (supports π…))…))
```

with `h` and `g` each `(structural)` or a support, and supports written `(pin r #k v)`, `(cell #d)`, `(cell-law #d #l)` and `(cell-package #d #q)`.
A candidate's context variables are named `x0`, `x1`, …, with `x0` the last context position; the guard's variable is `x0`.

The surface text (`Lang/Surface.lean`) writes the same declaration by name, in the notation `u :: [Ψ ⊢ τ]`:

```
(hole u ((x₁ τ₁ [π₁]) … (xₖ τₖ [πₖ]) ⊢ τ)
  (select ℓ key)
  [(guard [π] t)]
  (candidate t π…)…)
```

and a body uses it as `(hole u t₁ … tₖ)`.
Each part lowers to one field of the ROM declaration:

| surface | ROM declaration |
|---|---|
| `u` | `name n`, where `n` is the hole's position among the package's hole declarations |
| `(xᵢ τᵢ)` | context position `i` of type `τᵢ`, with hypothesis `structural` |
| `(xᵢ τᵢ π)` | context position `i` of type `τᵢ`, with hypothesis `π` |
| `τ` after `⊢` | `type τ` |
| `(select ℓ key)` | `selection (r, k)`: `r` is the index of relation `ℓ` in label order, `k` the bytes of `key` (`Lang/Rel.lean` `keyBytes`) |
| `(guard π t)`, `(guard t)`, none | `guardpin π`, no guard pin, or no guard pin and the guard `true`; `t` names the guard's variable `present` |
| `(candidate t π…)` | one candidate, in order; `t` names context position `i` as `xᵢ` |
| `(row ℓ key v)` | `row r k v` |
| `(cell #d)`, `(cell #d (law #l))`, `(cell #d (runs #q))` | `cell d`, `cellLaw d l`, `cellPackage d q` |
| `(hole u t₁ … tₖ)` in a body | `hole n (t₁ … tₖ)` |

A key is the relation's key fields as a record literal, `(record (f v)…)`.
A body that names no declared hole is refused `noHole`; a malformed declaration is refused `badClause`, at the offset of the form.

Lean: `Lang/Surface.lean` `holeDecl`, `pinOf`; the surface's package is printed and read again by the core reader, and a printed hole reads back as itself (`Lang/Proofs/Print.lean` `holeROM_read`, `readPackage_packageText`).

## 2.6 Relations

A *relation* is a place under an object that holds keyed rows.
No term has a relation type, so no run holds a whole relation.

```
reldecl ::= { key (ℓ₁ : κ₁) … (ℓⱼ : κⱼ),       1 ≤ j ≤ 8, declared order
              val τ, limit n,
              sum ℓ?, cap n,
              retract bool, guard ℓ?, holds ℓ? }
keytype κ ::= nat | bool | digest | sum (ℓ : rec)+ | rec (ℓ : κ)*
```

Lean: `Lang/Package.lean` `structure RelDecl`, `keyFixed`.

* The key is fixed-width data in declared order; its bytes are its fields' data encodings in that order (§5.6).
* `val` is the type of a row's value.
* `limit` bounds the number of rows; `sum` names a natural field of `val` whose total the relation's head keeps, and `cap` bounds that total.
* `retract false` makes the relation insert-only.
* `guard` names an interface field that judges each edit (§4.9).
* `holds` names a `leg` field of `val`: each row then holds that much value in the object's account (LANG-90).

The core text is `(ℓ (key (ℓ τ)…) (val τ) (limit n) (sum [ℓ]) (cap n) (retract b) (guard [ℓ]) (holds [ℓ]))`, all eight clauses in this order.

## 2.7 Grades and claims

A *grade* bounds a method's effect (LANG-89).

```
grade ::= { moves n } | { moves n, produces I }
```

`moves` bounds the sum of `amount` over the `transfer` and `credit` calls one run returns.
A method with no grade has the grade `{ moves 0 }`.
`produces I` names the interface every package the run installs or makes must have: a record of
method and law names and types, the same shape a package's interface has (LANG-103).
The core text writes the grade as `(ℓ n)` or `(ℓ n I)`; the surface writes the clause
`(effect (moves n) [(produces I)])`, `I` that record written as a type.
Lean: `Lang/Package.lean` `structure Effect`, `Package.effectOf`, `producesOk`.

A *claim* is a sentence a package makes of itself (LANG-93).

```
claim ::= keeps ℓᵢ ℓₗ
```

`keeps inv law` says: the law `law` refuses every birth, adoption, write and invocation whose new state fails the interface field `inv : S → bool`.
Lean: `Lang/Claim.lean` `inductive Claim`.

## 2.8 Packages

```
package P ::= { imports d*,          ids of installed packages, ≤ 16
                state S,             a record data type
                iface I,             the type of body
                body t,
                methods ℓ*,          interface fields that are methods, ≤ 64
                laws ℓ*,             interface fields that are laws, ≤ 16
                rels (ℓ : reldecl)*, labels ascending, ≤ 8
                doc b,               one printable line, ≤ 256 bytes
                holes holerom*,      ≤ 16
                effects (ℓ : grade)*, labels ascending, each a method
                claims claim* }      ≤ 16
```

Lean: `Lang/Package.lean` `structure Package`; the bounds are `importsMax`, `methodsMax`, `lawsMax`, `relsMax`, `Bounds.docMax`, `Bounds.holeSignatureMax`, `claimsMax`.

The body's `ref i` names the `i`-th import.
A package's id is the digest of its bytes (§5), so it commits to its imports' ids and through them to its whole closure, while the body holds no import's digest.
Relation `i` of a package is the `i`-th entry of `rels`.
A method is named by its index in `methods`.

The core text is

```
(package (imports "hex"…) (doc ["text"]) (state S) (iface I)
         (methods ℓ…) (laws ℓ…) (rels reldecl…) (body t)
         [(effects (ℓ n [I])…)] [(claims (keeps ℓ ℓ)…)] [(holes holerom…)])
```

with the last three sections present exactly when nonempty, in this order.

## 2.9 The shapes the kernel reads

A package's interface is a record type.
The install check (§3.7) requires each method and law field to have one of the shapes below.

### 2.9.1 Requests and occasions

```
occasion = sum (adopt : bytes) (birth : rec) (invoke : nat) (relaw : bytes) (retire : rec) (write : rec)
req      = rec (agent : digest) (caller : opt digest) (notBefore : nat) (occasion : occasion)
               (principal : digest) (self : digest) (validUntil : nat)
```

Lean: `Lang/Package.lean` `occasionTy`, `reqTy`.

* `agent` is the member who signed the call.
* `principal` is the member whose authority the call uses.
* `self` is the object judged or run.
* `caller` is `some o` when object `o`'s run returned this call, `none` when a member signed it (KERNEL-76, LANG-85).
* `notBefore` and `validUntil` are the signed window: the Turn lands at a height in `[notBefore, validUntil]`.
* `occasion` is the act judged.
  `adopt` and `relaw` carry the incoming law ids' bytes, concatenated; `invoke` carries the method index.

### 2.9.2 Laws

```
law S = S → S → req → verdict
```

A law sees the old state, the new state and the request.
Lean: `lawTy`.

### 2.9.3 Methods

```
method S A ks R E m = R → S → A → req → result S ks E m
result S ks E m     = rec (calls : calls ks) (edits : edits E m) (state : S)
calls [κ₀ … κₖ₋₁]   = rec (c0 : opt κ₀) … (c(k-1) : opt κₖ₋₁)      k ≤ Kernel.Bounds.callsMax = 8
edits E m           = rec (e0 : opt E) … (e(m-1) : opt E)           m ≤ editsMax = 8
```

Lean: `methodTy`, `resultTy`, `callsTy`, `editsTy`.

* `R` is the *rows* argument: what the method reads of relations (§2.9.5).
* `S` is the state; `A` is the argument, a data type.
* Each `κᵢ` is a *call type*, a sub-sum of the call arms (§2.9.4).
  The number of slots and the arms of each are fixed by the type, so a method's type says how many calls it may make and of which kinds.
* `E` is the package's one edit type (§2.9.5).

### 2.9.4 Calls

A call type is a sum of one or more of these arms, each at exactly its type:

```
account  : rec (asset : digest) (owner : digest)
createOf : rec (pkg : bytes) (state : T)                                       T a record data type
credit   : rec (acct : acctref) (amount : nat) (via : opt digest) (well : digest)
grant    : rec (grantee : digest) (parent : opt digest) (rights : rights) (target : digest)
install  : rec (pkg : bytes)
invoke   : rec (args : A) (budget : nat) (method : nat) (obj : digest) (via : opt digest)   A a data type
transfer : rec (amount : nat) (dst : acctref) (once : opt bytes) (src : acctref) (via : opt digest)

acctref  = sum (of : rec (asset : digest) (owner : digest)) (well : digest)
right    = sum (credit : nat) (enroll : nat) (invoke : nat) (mutate : rec) (observe : rec) (transfer : nat)
rights   = rec (r0 : opt right) (r1 : opt right) (r2 : opt right) (r3 : opt right)
```

Lean: `callArms`, `accountArm`, `createOfArm`, `creditArm`, `grantArm`, `installArm`, `invokeArm`, `transferArm`, `acctRefTy`, `rightTy`, `rightsTy`.

* `install` installs the package the bytes encode (LANG-86).
* `createOf` installs the package if the World lacks it and creates an object of it, owned by the signer, with the given state (LANG-96, KERNEL-77).
* In the surface text a slot lists its kinds, `(calls (install transfer (invoke T) (createOf S)))`, `S` the state type of the created object; `done` returns `(createOf (pkg e) (state e))` (LANG-108).
* `invoke`'s `args` is a value of the slot's declared argument type, which the runtime encodes for the callee (LANG-77).
* The other arms are the kernel's acts on accounts, value and grants; [`kernel.md`](../reference/kernel.md) defines them.

### 2.9.5 Reads, edits and guards

A method reads only rows the caller pinned under the object's own relations, and, when it declares a *peer read*, the same relations under one other object of the same package.

```
R        = rec (ℓ : relread ℓ)* [(peer : rec (ℓ : relread ℓ)*)]      ℓ relation labels, ascending
relread  = rec (p0 : opt point) … (p(n-1) : opt point) [(range : rec (pre : prefix) (rows : rec (r0 : opt rangerow) …))]
point    = rec (key : key) [(live : bool)] [(receipt : seen)] (val : opt val)
rangerow = rec (key : key) [(live : bool)] [(receipt : seen)] (val : val)
seen     = rec (height : nat) (turn : digest) (tx : digest)
```

Lean: `readsTy`, `relReadTy`, `pointRecTy`, `rangeRowTy`, `rowsTy`, `seenTy`, `RelRead`.

* `n ≤ 8` point slots hold the caller's row pins in pin order; a range holds up to 8 rows under a key prefix the caller signed.
* `live` is present only for a relation keyed by one digest: it says whether the cell that key names is live in the caller's view.
* `receipt` is present only for such a relation and an argument with a `receipt : bytes` field: it is a foreign World's committed call, checked against the head object the key names.
* A peer read requires the argument to name `pair : rec (a : digest) (b : digest)`, one member of which is the object itself.

A method's edits use the package's one edit type:

```
E       = sum (ℓ₁ : reledit ℓ₁) … (ℓᵣ : reledit ℓᵣ)               over the package's relations
reledit = sum (insert : row) [(retract : rec (key : key))] (upsert : row)    retract only if allowed
row     = rec (key : key) (val : val)
```

Lean: `editTy`, `relEditTy`, `rowTy`.

A *guard* judges one edit of its relation:

```
guard S d = S → req → rec (edit : reledit d) (old : opt val) → verdict
```

`old` is the row the edit replaces, as the caller pinned it.
Lean: `guardTy`, `guardInTy`.

## 2.10 Data and machine values

*Data* are the first-order values that cross between a run and the World.

```
data δ ::= nat n | bool b | bytes b | digest d | record (ℓ = δ)* | inj ℓ δ
```

Lean: `Lang/Data.lean` `inductive Data`.

*Machine values* are what a run computes.

```
value v ::= nat n | bool b | bytes b | digest d
          | clo t E                        closure: body and environment
          | record (ℓ = (t, E))*            record of suspended fields
          | knot t E                        fixed point of a record transformer
          | inj ℓ v
env   E ::= v*
```

Lean: `Lang/Eval.lean` `inductive Val`.

Data enter the machine by `Data.toVal`, which makes each field a suspension that is already a value.
A value leaves the machine as data only by *extraction* at a data type, which forces suspended fields under the remaining budget (§4.4).

## 2.11 Packages as programs

A package's body is usually a record literal of its interface fields.
The program in the [README](../../README.md#one-program) is a complete package in surface text; `ob '(core P)'` prints its core text.
`Lang/Std*.lean` are Lean functions that emit packages: activities, offers, escrow, posted-candidate holes, heads and generators.

## 2.12 Packages that write packages

A run writes the bytes of a package with the payload writers (§2.3) and returns them in an `install` or `createOf` call.
The bytes are a byte string; the language has no type of packages.
The kernel checks the bytes when it installs them, exactly as it checks a member's package (§4.5).
A type of installed interfaces, `Ty.pkg I`, is in flight: redregg `promo/DESIGN-META.md` §10.
