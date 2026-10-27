# 1 Introduction

## 1.1 What Objective Bend is

Objective Bend is a typed language for programs that run inside a replicated state machine whose every step each participant re-executes.
A program is a *package*.
A package is a closed term together with the types and labels that say how the kernel uses it: an interface type, an object state type, which interface fields are methods and which are laws, keyed relations, typed holes, grades and claims.
An installed package is immutable and is named by the digest of its bytes.
An *object* is a cell that holds an owner, a list of extra laws, a state and, for a *programmed* object, a package's id.
An object without a package is a *data object*.

A *method* computes a proposal: a new state, a bounded list of calls the object makes, and a bounded list of edits to the object's rows.
A *law* judges a proposal: it sees the old state, the new state and the request, and returns `ok` or a refusal with a reason.
The kernel commits a method's proposal only when every law in force admits it, and commits the calls the method returned as nested calls of the same step.

The language's meaning is *contextual*.
A package may declare typed holes.
At each invocation the runtime fills each hole with a candidate the package committed at install, chosen by a row the caller pinned, and only while the facts that candidate relies on hold in the caller's pinned view of the World.
A hole that cannot be filled becomes a typed refusal that names why: the support that failed, the selection that is missing, or the guard that blocked.
That refusal ends the run only if the run demands the hole.

## 1.2 Design goals

**Exactness.**
Types are monomorphic and carry no quantities; type equality is syntactic equality.
Every annotation needed for checking is in the term, so checking is a total function with no inference of annotations.
That function is proved equal to a declarative typing relation.

**Determinism.**
A term's outcome depends only on the term, its environment, the closure it runs in and the tick budget.
Every member re-executes every run and must reach the same outcome.
A final outcome does not depend on how much budget beyond what it used was given.

**Bounds.**
Every value a program can build is bounded: a natural below `2^64`, a byte string at most one kernel slot.
Every run is bounded: one machine transition costs one tick, a primitive that walks bytes costs one tick per 32 bytes, and the stack has a consensus depth bound.
Every way a run can end without a value is a named fault.

**First-order boundary.**
State, arguments, row values and verdicts are first-order data.
Functions exist inside a run and never cross into the World.
An id is its own type, `digest`, that no run can make from bytes.

**No value in the language.**
A language value carries no money.
Value lives in kernel accounts, and a method moves it only by returning a call the kernel judges.

**Judged, not trusted, extension.**
Every way the language grows a World goes through the same checks a member's act goes through: a generated package is checked as a member's package is, an object's law replacement is judged by the laws in force and by the incoming laws, and a package's claim about itself is checked against its own term at install.

## 1.3 Scope

This specification defines:

* the abstract syntax of types, terms, packages, relations, holes, grades and claims (chapter 2);
* the typing relation and the install check (chapter 3);
* the machine, its tick accounting, and the runtime rules that install a package, load a closure, prepare holes, run a method, extract its result, and judge laws and guards (chapter 4);
* the package wire format at version 10 (chapter 5).

It does not define:

* the World, the Turn, the kernel's receivers and its refusals beyond the interface the language implements; those are in [`docs/reference/kernel.md`](../reference/kernel.md);
* how members sign, submit, follow and settle calls; that is in [`docs/reference/protocol.md`](../reference/protocol.md);
* the surface text of `Lang/Surface.lean`, which lowers to the core text and is outside admission;
* the library of package generators in `Lang/Std*.lean` (activities, offers, escrow, the posted-candidate hole, heads), which are Lean functions that emit ordinary packages.

## 1.4 Dependencies

The language is defined in Lean 4 at the toolchain in [`lean-toolchain`](../../lean-toolchain) (v4.30.0), with core and Std and no other library.

It depends on two other layers of the tree:

* the codec (`Codec/`): byte encodings, the varint, the one recursive tree codec, digests (32 bytes in the deployed system, `Codec/Deployed.lean`);
* the kernel's program interface (`Kernel/Receive/Call.lean` `structure Program`): the language is one value of that structure, `Lang/Program.lean` `program`, with four functions the kernel calls: `checkInstall`, `judge`, `run` and `rels`.

Every read the language makes of the World goes through the caller's pinned view (`Pinned`) and pinned rows (`RowView`).
So two members with the same pins compute the same result (`Kernel/Proofs/Receive.lean` `receive_congr`).

## 1.5 Overview

A package passes through these stages.
Each stage names the chapter that defines it.

1. **Text.** An author writes core text, or surface text that lowers to it (§2, `Lang/Read.lean`, `Lang/Surface.lean`).
2. **Bytes.** The package is encoded as one version byte and one tree (§5, `Lang/Package.lean` `Wire.encodePackage`).
3. **Install.** A member signs `install` of the bytes, or an object's method returns an `install` call.
   The kernel calls `checkInstall`: decode the bytes, load and re-check the import closure, and admit the package by the same admission every later load uses (§3.7, §4.5).
   The package's cell is read-only, and its id is the digest of its content.
4. **Birth.** A member creates an object of the package with a seed state.
   Every law in force judges the birth (§4.8).
   The object's relations are declared with it.
5. **Invocation.** A member, or an object's run, invokes a method.
   The runtime loads the closure, prepares each contextual package's holes against the caller's pins, runs the method on the machine under the call's tick budget, extracts its result, reads its calls, checks them against the method's grade, reads its edits, runs each edited relation's guard, and checks that the calls move the value the edited rows hold (§4.6, §4.7, §4.9).
   The kernel then has every law in force judge the old and new state, and derives the returned calls as the object, depth first (§4.8).
6. **Turn.** If every check passes, the kernel commits all effects of the call tree as one Turn; otherwise it records the first refusal by name.

## 1.6 In flight

These designs are not on `main` and this specification does not describe them as landed:

* **The slot.** A resolution judgment with run-time withdrawal and one repair rule, in which the resident's decisions run as holes: redregg `promo/DESIGN-CTX.md` §11, module `Lang/Contextual/Slot.lean`.
* **Contextual integrity.** A top claim over histories that every contextual run used a justified candidate and every hole refusal names a failed justification: redregg `promo/DESIGN-CTX.md` §2.4.
* **A type of packages.** `Ty.pkg I`, whose values are package bytes that install at interface `I`: redregg `promo/DESIGN-META.md` §10.
* **The bytes meter.** A meter of bytes written, beside the tick meter: redregg `promo/DESIGN-OBS.md` §1.4.
