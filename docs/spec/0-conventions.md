# 0 Conventions

This chapter fixes the notation of the specification.
Every later chapter, and the two documents in [`docs/reference/`](../reference/), use it without restating it.

## 0.1 Normative source

The Lean tree is normative.
This document restates it.
Each rule cites the definition it restates and, where one exists, the theorem about it, by file and name, for example `Lang/Check.lean` `inferE`.
Where this document and the Lean disagree, the Lean decides and the document has a defect.

A statement marked **in flight** describes a design that is not on `main`.
It names the design and its section.
No other statement describes anything that is not on `main`.

This revision restates `main` at `276ded8`.

## 0.2 Abstract syntax

Abstract syntax is written as a grammar in a fenced block.

```
type τ ::= nat | bool | bytes | digest | τ₁ → τ₂ | rec ρ | sum ρ
```

A production lists its alternatives after `::=`, separated by `|`.
A name on the left of `::=` is a nonterminal; the Greek or Latin letter after it is the meta-variable that ranges over it.
Words in `monospace` on the right are terminals.

Sequences use these suffixes:

| notation | meaning |
|---|---|
| `x*` | zero or more `x` |
| `x+` | one or more `x` |
| `x?` | zero or one `x` |
| `xⁿ` | exactly `n` of `x` |
| `x₁ … xₙ` | the sequence of `x₁` to `xₙ`; `n` may be 0 |

`[x₁, …, xₙ]` is a list and `[]` the empty list.
`|s|` is the length of a list or byte string `s`.
`s[i]` is the element at index `i`, counted from 0; it is undefined past the end.
`x :: s` is the list with head `x` and tail `s`; `s ++ s'` is concatenation.

## 0.3 Labels and rows

A *label* `ℓ` is a nonempty string of at most 64 bytes of UTF-8 that contains no parenthesis, no `"`, no `;` and no white space (`Lang/Row.lean` `labelAtom`, `Lang/Wire.lean` `labelOk`).
Labels are ordered by Lean's `String` order, which compares code points from the left.

A *row* `ρ` is a list of pairs `ℓ : x`.
A row is *canonical* when its labels strictly ascend (`Lang/Row.lean` `Row.ascending`).
A canonical row therefore has distinct labels.
Records, sums, their types and their values all use rows.

Three operations on rows recur:

| notation | meaning | Lean |
|---|---|---|
| `ρ(ℓ)` | the value at the first entry labelled `ℓ`; undefined if there is none | `Row.find?` |
| `ρ ⊕ ρ'` | `ρ` with each entry of `ρ'` inserted in order, replacing an entry of the same label | `Row.merge` |
| `sort ρ` | the stable insertion sort of `ρ` by label | `Row.sort` |

`ρ ⊕ ρ'` keeps a canonical `ρ` canonical (`Lang/Proofs/Row.lean` `merge_ascending`).

## 0.4 Meta-variables

| letter | ranges over |
|---|---|
| `τ`, `σ`, `A`, `B`, `S`, `T` | types |
| `t`, `u`, `e`, `f` | terms |
| `v`, `w` | machine values |
| `δ` | first-order data |
| `ℓ`, `m` | labels |
| `ρ` | rows |
| `i`, `j`, `k`, `n` | natural numbers |
| `b`, `p` | byte strings |
| `d` | digest byte strings |
| `Γ` | local typing contexts: lists of types, indexed by de Bruijn index |
| `Δ` | closure contexts: the interface types of the packages a term may `ref`, by index |
| `Ω` | hole signatures: lists of hole declarations |
| `E` | machine environments: lists of values, indexed by de Bruijn index |
| `K` | machine stacks: lists of frames |
| `P` | packages |
| `W` | Worlds |

A prime or a subscript makes a fresh variable of the same kind: `τ'`, `t₁`.

## 0.5 Judgements and rules

A judgement is a relation written in a fixed form.
The forms used are:

| form | reading | chapter |
|---|---|---|
| `Δ; Γ ⊢_Ω t : τ` | under closure `Δ`, locals `Γ` and holes `Ω`, term `t` has type `τ` | 3 |
| `⊢ τ wf` | type `τ` has canonical rows throughout | 3 |
| `Δ ⊢ P ok` | package `P` passes the install check against import interfaces `Δ` | 3 |
| `s ↪ s'` | the machine takes one transition, one tick, from state `s` to state `s'` | 4 |
| `s ↪ halt v` | the machine ends with value `v` | 4 |
| `s ↪ fault f` | the machine ends with fault `f` | 4 |

A rule has premises above a line and a conclusion below it, its name on the right, and the Lean constructor or definition it restates after the name:

```
Γ[i] = τ
─────────────────────  T-Var    HasType.var
Δ; Γ ⊢_Ω var i : τ
```

A rule with no premises has an empty line above the bar.
Each rule is followed by its reading in prose.
The prose reading says the same thing as the rule, in steps where the rule is an algorithm.

## 0.6 Refusals

Every way a check, a decoder or a run ends without success has a name (CHARTER law 7).
This document writes a refusal by the name the implementation prints, in monospace: `holeSupportDead`, `lawDenied`, `tooLarge`.
Where the printed form carries data, the data follows the name as it does on the wire: `holeSupportDead 0 cell:ab…`.
A refusal is never a value of the language and never a verdict.

## 0.7 Bounds

A bound is a named constant of the Lean.
This document writes it by its Lean name, `Bounds.natLimit`, and gives its value where it is first used.
Chapter 6 lists every bound the language uses.

## 0.8 Concrete text

The language has two concrete texts.
The *core text* (`Lang/Read.lean`) is the abstract syntax as s-expressions, with names in place of de Bruijn indices.
The *surface text* (`Lang/Surface.lean`) lowers to the core text.
Chapter 2 gives each construct's core text beside its abstract syntax.
Examples in this document are core text unless they say otherwise, and each was read by `Lang.Read` and checked by the install check at `276ded8`.

## 0.9 Byte strings

A byte string is written in hexadecimal, two digits a byte, most significant digit first: `0a00`.
In the core text a byte string literal is `#` followed by its hexadecimal digits.
`ε` is the empty byte string and `b · b'` concatenation.
`u8(n)`, `u32le(n)`, `u64be(n)` and `varint(n)` are the encodings of chapter 5.
