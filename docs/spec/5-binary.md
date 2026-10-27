# 5 Binary format

A package's bytes are one version byte followed by one *tree*.
A tree is the codec's one recursive encoding; types, terms and every section of a package are trees.
Data (state, arguments, row values, keys) is encoded by type, without trees.
Every encoding in this chapter is canonical: a value has exactly one byte string, and a byte string decodes to at most one value.

The normative source is `Lang/Package.lean` (namespace `Wire`), `Lang/Wire.lean`, `Lang/HoleWire.lean`, `Lang/Wire/Data.lean`, `Codec/Tree.lean`, `Codec/Stream.lean` and `Codec/Varint.lean`.
The vectors in [`gates/codec-vectors.tsv`](../../gates/codec-vectors.tsv), site `lang/package/10`, are generated from the codec and fix what package bytes mean (§5.8).

## 5.1 Scalars

```
u8(n)      ::= one byte n                                       0 ≤ n < 256
u32le(n)   ::= four bytes, least significant first             0 ≤ n < 2^32
u64be(n)   ::= eight bytes, most significant first             0 ≤ n < 2^64
bool(b)    ::= 0x00 (false) | 0x01 (true)                       any other byte refused
varint(n)  ::= LEB128, shortest form, at most five bytes        0 ≤ n < 2^32
```

Lang: `Codec/Stream.lean` `u8`, `u32`, `u64be`, `bool`; `Codec/Varint.lean` `varint`, `putVarint`.

A varint writes `n` in base 128, least significant digit first, with the top bit of each byte set when another byte follows.
A decoder refuses a final `0x00` after a continuation byte (`varint/overlong`), a sixth byte, and a value at or past `2^32` (`pastBound`).

## 5.2 Trees

```
tree ::= node(tag, payload, children)
node(t, p, c₁ … cₙ) ::= u8(t) · varint(|p|) · p · varint(n) · c₁ · … · cₙ
```

Lean: `Codec/Tree.lean` `inductive Tree`, `Tree.putD`, `Tree.getD`.

A tree in the package wire *fits* `Wire.nodeMax` = 65536 and `Wire.depthMax` = 1024: every payload is at most 65536 bytes, every node has at most 65536 children, and the tree nests at most 1024 levels, the root counting as one (`Tree.fits`).

A reader refuses:

| refusal | when |
|---|---|
| `truncated i n` | fewer than `n` bytes remain at offset `i` |
| `pastBound i max got` | a payload length or child count past 65536 |
| `tooDeep i limit` | a node at nesting level 1025 |
| `rejected i varint/overlong` | a varint that is not in shortest form |

A node with tag `t`, payload `p` and children `cs` is written below as `t⟨p⟩[cs]`.
`t⟨⟩[]` is a node with an empty payload and no children.

**Theorem** (`Codec/Proofs/Tree.lean` `tree_lawful`).
The tree codec is lawful: writing appends exactly the encoding, and reading at an offset where an encoding occurs returns that tree and the offset after it, and nothing else.

## 5.3 Labels, indices and literals in payloads

| field | payload | requirement |
|---|---|---|
| label `ℓ` | the UTF-8 bytes of `ℓ` | a label (§0.3): 1 to 64 bytes, valid UTF-8, no delimiter |
| index `i` (`var`, `ref`, hole name, relation index) | `u32le(i)` | exactly four bytes |
| natural `n` (`nat` literal, limit, cap, version, grade) | `u64be(n)` | exactly eight bytes |
| boolean literal | `bool(b)` | exactly one byte, 0 or 1 |
| primitive | `u8(code)` | a code of §5.5 |
| byte string, digest, refusal reason, doc | the bytes | |
| key bytes, cell id | the bytes | |

Lean: `Lang/Wire.lean` `labelOf`, `u32Of`, `u64Of`, `boolOf`, `primOfBytes`.

## 5.4 Types

```
nat            0⟨⟩[]
bool           1⟨⟩[]
bytes          2⟨⟩[]
digest         7⟨⟩[]
τ₁ → τ₂        3⟨⟩[τ₁, τ₂]
rec ρ          4⟨⟩[field…]          at most Wire.rowMax = 256 fields
sum ρ          5⟨⟩[field…]          at most 256 fields
field ℓ : τ    6⟨ℓ⟩[τ]
```

Lean: `Lang/Wire.lean` `tyTree`, `tyOf`.

## 5.5 Terms

```
var i                 0⟨u32le(i)⟩[]
lam τ t               1⟨⟩[τ, t]
app f a               2⟨⟩[f, a]
fix t                 3⟨⟩[t]
nat n                 4⟨u64be(n)⟩[]
bool b                5⟨bool(b)⟩[]
bytes b               6⟨b⟩[]
prim p a b            7⟨u8(code p)⟩[a, b]
record fs             8⟨⟩[field…]                at most 256 fields
get t ℓ               9⟨ℓ⟩[t]
extend t fs           10⟨⟩[t, field…]            at most 256 fields
inj τ ℓ t             11⟨ℓ⟩[τ, t]
case t arms           12⟨⟩[t, field…]            at most 256 arms; an arm is a field
ite c t e             13⟨⟩[c, t, e]
ref i                 14⟨u32le(i)⟩[]
field ℓ = t           15⟨ℓ⟩[t]
digest d              16⟨d⟩[]
refuse τ b            17⟨b⟩[τ]
hole n (t₁ … tₖ)      18⟨u32le(n)⟩[t₁, …, tₖ]    at most 256 terms
```

Primitive codes:

| code | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| primitive | add | sub | mul | div | mod | eq | lt | le | beq | cat | deq | lenLe | u64be | sized | dsized |

Lean: `Lang/Wire.lean` `termTree`, `termOf`, `primCode`, `primOf`.

The tag spaces of types and terms overlap; a reader knows which it reads from the position.
A tree that is not one of these forms, or whose payload breaks §5.3, reads as no term.

**Theorem** (`Lang/Proofs/Wire.lean` `termOf_termTree`, `tree_of_termOf`).
A representable term reads back from its tree, and a tree that reads as a term is that term's tree.
The same holds for types (`tyOf_tyTree`, `tree_of_tyOf`).

## 5.6 Data

Data at a type `τ` is written by a codec built from `τ` (`Lang/Wire/Data.lean` `dataStream`):

```
data(nat, n)            = u64be(n)
data(bool, b)           = bool(b)
data(bytes, b)          = u32le(|b|) · b              |b| ≤ 65536
data(digest, d)         = u32le(|d|) · d              |d| ≤ 32
data(rec ρ, record δs)  = data(τ₁, δ₁) · … · data(τₙ, δₙ)        fields in row order, no labels
data(sum ρ, inj ℓ δ)    = u8(k) · data(ρ(ℓ), δ)          k the index of ℓ in ρ
data(τ₁ → τ₂, _)        : no value
```

Only a well-formed type the wire carries has a data codec (`Wire.dataTy`).
A natural is big-endian so that the bytes of two keys compare as their numbers do (LANG-57).

**Theorem** (`Lang/Proofs/Data.lean` `decodeData_eq_ok_iff`).
`decodeData τ b = ok δ` if and only if `encodeData τ δ = some b`.

Data is used in these places:

| what | type | where it lives |
|---|---|---|
| state field `i` | the field's type | slot `stateBase + i` of the object cell |
| method argument | the method's argument type | the signed `invoke` call |
| `invoke` call argument | the slot's argument type | the nested call |
| row value | the relation's value type | the row |
| relation key | `rec (k0 : κ₀) … (k(j-1) : κ_(j-1))`, the key's fields in declared order | the row's key bytes |
| range prefix | the first `m` key fields, labelled the same way | the signed range read |
| selection value | `nat` | the hole's selection row |

Lean: `Lang/Rel.lean` `keyWireTy`, `keyBytes`, `preBytes`; `Lang/Call.lean` `stateSlots`.

A key's fields are renamed `k0`, `k1`, … in declared order, so the record codec, which writes fields in row order, writes them in declared order.

## 5.7 Packages

```
package(P) = u8(10) · tree(P)

tree(P) = 0⟨⟩[ 0⟨⟩[0⟨d⟩[] for each import d],
               state type,
               iface type,
               body term,
               1⟨⟩[1⟨ℓ⟩[] for each method ℓ],
               1⟨⟩[1⟨ℓ⟩[] for each law ℓ],
               2⟨⟩[rel for each relation],
               0⟨doc⟩[],
               3⟨⟩[holerom for each hole],
               4⟨⟩[grade for each graded method],
               5⟨⟩[claim for each claim] ]
```

The root has exactly eleven children in this order, and every wrapper payload shown empty must be empty.

```
rel ℓ d       = 0⟨ℓ⟩[ 0⟨⟩[6⟨ℓᵢ⟩[κᵢ] for each key field, declared order],
                      val type,
                      0⟨u64be(limit)⟩[],
                      optlabel(sum),
                      0⟨u64be(cap)⟩[],
                      r⟨⟩[]            r = 1 if retract, else 0,
                      optlabel(guard),
                      optlabel(holds) ]
optlabel(none)   = 0⟨⟩[]
optlabel(ℓ)      = 1⟨ℓ⟩[]
grade ℓ {moves n} = 0⟨ℓ⟩[0⟨u64be(n)⟩[]]
claim (keeps i l) = 0⟨⟩[1⟨i⟩[], 1⟨l⟩[]]
```

```
holerom = 3⟨u32le(name)⟩[ 0⟨⟩[context types…],
                          result type,
                          0⟨⟩[candidate…],
                          0⟨selection key⟩[0⟨u32le(selection rel)⟩[]],
                          0⟨⟩[optpin(h) for each hypothesis],
                          optpin(guard pin),
                          guard term ]
candidate = 0⟨⟩[body term, 0⟨⟩[pin…]]
pin(row r k v)          = 0⟨k⟩[0⟨u32le(r)⟩[], 0⟨u64be(v)⟩[]]
pin(cell d)             = 1⟨d⟩[]
pin(cellLaw d l)        = 2⟨d⟩[0⟨l⟩[]]
pin(cellPackage d q)    = 3⟨d⟩[0⟨q⟩[]]
optpin(structural)      = 0⟨⟩[]
optpin(π)               = 1⟨⟩[pin(π)]
```

Lean: `Lang/Package.lean` `Wire.packageTree`, `Wire.packageOf`, `Wire.relTree`, `Wire.effectTree`, `Wire.claimTree`; `Lang/HoleWire.lean` `holeROMTree`, `holeCodeTree`, `supportPinTree`, `supportOptPinTree`.

Decoding (`Wire.decodePackage`):

1. The first byte must be 10, `Bounds.packageWireVersion`, or the input is refused `rejected 0 "lang/package-version/10"`.
2. Read one tree that fits the bounds of §5.2; bytes after it are refused `trailing`.
3. The tree must read as a package (`packageOf`), or `rejected 0 "lang/package/10"`.
   Besides the forms above, this requires: each import at most 32 bytes; the doc at most `Bounds.docMax` = 256 bytes of UTF-8 with no control character and no `"` (`Bounds.docOk`); every label, index and natural as in §5.3.

Decoding checks form, not meaning.
A package that decodes may still fail the install check (chapter 3).

**Theorem** (`Lang/Proofs/Wire.lean` `decodePackage_eq_ok_iff`).
`decodePackage b = ok P` if and only if `encodePackage P = some b`: a package has exactly one byte string.

**Theorem** (`packageCodec_lawfulOn`).
The package codec is lawful on exactly the packages whose tree is representable and fits the bounds.

**Theorem** (`unversioned_package_refused`, `decodePackage_wrong_version`).
Bytes of any other version, including the unversioned wires before version 3, are refused by the version byte.

## 5.8 The package id

A package's id is the digest of its read-only cell:

```
id(P) = hash("nanodregg/kernel/rom-id/v1", cellBytes({kind package, discipline rom, slots [(0, package(P))]}))
```

Lean: `Kernel/World.lean` `romIdOf`, `domRomId`; `Codec/Kernel.lean` `cellBytes`.
The deployed hash is cSHAKE256 with a 32-byte output (`Codec/Deployed.lean`).
So the id commits to every byte of the package, its imports' ids among them.

## 5.9 Worked examples

Each example is a row of [`gates/codec-vectors.tsv`](../../gates/codec-vectors.tsv), site `lang/package/10`, read byte by byte.

### Row 0: the smallest package

```
0a                      version 10
00 00 0b                root: tag 0, payload length 0, 11 children
  00 00 00              imports: tag 0, no payload, no children
  04 00 00              state: rec with no fields
  04 00 00              iface: rec with no fields
  00 04 00000000 00     body: var 0 (tag 0, payload length 4, u32le 0, no children)
  01 00 00              methods: none
  01 00 00              laws: none
  02 00 00              relations: none
  00 00 00              doc: empty
  03 00 00              holes: none
  04 00 00              grades: none
  05 00 00              claims: none
```

The row decodes to `{ imports [], state rec, iface rec, body var 0, … }`.
Decoding succeeds; the install check would refuse it, because `var 0` is unbound (`illTyped unbound @top`).

### Row 7: a primitive

The body is

```
07 01 00 02             prim: tag 7, payload length 1, code 0 (add), 2 children
  04 08 0000000000000001 00     nat 1
  04 08 0000000000000002 00     nat 2
```

and reads as `prim add (nat 1) (nat 2)`.

### Row 11: an injection

```
0b 01 61 02             inj: tag 11, payload "a", 2 children
  05 00 01              sum, 1 field
    06 01 61 01         field "a"
      00 00 00          nat
  04 08 0000000000000001 00     nat 1
```

reads as `inj (sum (a : nat)) a (nat 1)`.

### Row 16: a refusal

```
11 07 746f6f20626967 01   refuse: tag 17, payload "too big", 1 child
  00 00 00                nat
```

reads as `refuse nat "too big"`.

### Row 17: a hole term

```
12 04 07000000 02         hole: tag 18, payload u32le 7, 2 children
  04 08 0000000000000003 00     nat 3
  05 01 01 00                   bool true
```

reads as `hole 7 (nat 3, bool true)`.
Decoding accepts it; install refuses it, because the package declares no hole 7 (`illTyped noHole @top`).

### Row 43: methods and laws

```
01 00 01  01 01 6d 00     methods: one leaf, label "m"
01 00 01  01 01 6c 00     laws: one leaf, label "l"
```

### Row 44: a grade

```
04 00 01                  grades: one entry
  00 01 6d 01             label "m", 1 child
    00 08 000000000000000a 00   moves 10
```

### Row 46: a claim

```
05 00 01                  claims: one entry
  00 00 02                claim node, 2 children
    01 01 69 00           invariant "i"
    01 01 6c 00           law "l"
```

reads as `keeps i l`.

### Rows that are refused

| row | bytes that differ from row 0 | refusal | why |
|---|---|---|---|
| 48 | body `13 00 00` | `rejected 0 "lang/package/10"` | tag 19 is no term (`package_refuses_unknown_term_tag`) |
| 49 | body `12 00 00` | `rejected 0 "lang/package/10"` | a hole's payload must be four bytes |
| 50 | state `08 00 00` | `rejected 0 "lang/package/10"` | tag 8 is no type |
| 51 | primitive code `0f` | `rejected 0 "lang/package/10"` | code 15 is no primitive |
| 56 | doc `61 0a 62` | `rejected 0 "lang/package/10"` | a doc has no control character (`package_refuses_newline_doc`) |
| 57 | doc `61 ff` | `rejected 0 "lang/package/10"` | a doc is valid UTF-8 (`package_refuses_nonUtf8_doc`) |
| 55 | first byte `09` | `rejected 0 "lang/package-version/10"` | version 9 |
| 58 | the whole input is `00 00 07 …`, an unversioned tree with seven children | `rejected 0 "lang/package-version/10"` | its first byte, the root's tag 0, reads as version 0 |

### A key

Site `lang/key`, row 0, is the key `(k0 : nat) (k1 : bool) (k2 : digest)` at `0`, `false` and 32 bytes of `ab`:

```
0000000000000000          k0: u64be 0
00                        k1: false
20000000                  k2: u32le length 32
abab…ab                   k2: 32 bytes
```

Row 7 states a length of 32 and supplies 31 bytes; it is refused `truncated 13 32`.

## 5.10 Version history

`Bounds.packageWireVersion` is bumped by every change of what package bytes mean (LANG-60).
The codec's label is `lang/package/N` at version `N` (`Lang/Proofs/Wire.lean` `packageCodec_label`), so the bump also moves the vectors' tag.

| version | change | decision |
|---|---|---|
| 3 | the version byte and the doc | LANG-60 |
| 4 | the holes section | LANG-P7 |
| 5 | a support may name a kernel cell | LANG-75.1 |
| 6 | the payload writers, primitive codes 12 to 14 | LANG-87 |
| 7 | a support may demand a cell's law or package | LANG-84 |
| 8 | the grades section | LANG-89 |
| 9 | a relation's held leg | LANG-90 |
| 10 | the claims section, the eleventh child | LANG-93 |

Lean: the docstring of `Lang/Bounds.lean` `packageWireVersion`.
