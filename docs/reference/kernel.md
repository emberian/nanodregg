# The kernel: the World and its transition

This document restates the kernel of nanodregg: the World, the call a member signs, the derivation of a Turn from the call, and the admission of the Turn.
It restates `main` at `276ded8`.
Its notation is that of [0 Conventions](../spec/0-conventions.md).
The Lean tree is normative: `Kernel/World.lean`, `Kernel/Cell.lean`, `Kernel/Turn.lean`, `Kernel/Value.lean`, `Kernel/Bounds.lean`, `Kernel/Trie.lean` and `Kernel/Receive/*.lean`.
Every rule names the definition it restates, and every theorem is named by file and name.

Contents:

1. [Structure](#1-structure)
2. [The call](#2-the-call)
3. [The transition](#3-the-transition)
4. [The window and the meter](#4-the-window-and-the-meter)
5. [Authority](#5-authority)
6. [Value](#6-value)
7. [The refusal table](#7-the-refusal-table)
8. [Theorems](#8-theorems)

## 0 Meta-variables of this document

Beside those of 0.4, this document uses the letters below.
Two of them differ from the language chapters: here `E` is the kernel's environment, not a machine environment, and `π` is a draft, not a support.

| letter | ranges over | Lean |
|---|---|---|
| `W` | Worlds | `World D` |
| `κ` | cells | `Cell` |
| `η` | cell entries | `Entry` |
| `θ` | Turns | `Turn D` |
| `x` | touches | `Touch D` |
| `c` | signed calls | `Call D` |
| `u` | unsigned calls | `Unsigned D` |
| `β` | call bodies | `Body D` |
| `π` | drafts | `Draft D` |
| `L` | pinned views | `Pinned D` |
| `a` | positions in a call's tree | `At D` |
| `ω` | walks of a call's tree | `Walk D` |
| `r` | recorded refusals | `Refused D` |
| `s` | log steps | `Step D` |
| `id`, `o`, `g`, `m` | ids: any, an object's, a grant's, a member's | `D` |
| `h`, `H` | heights | `Nat` |

`D` is the digest type; the kernel is generic in it.
`E` is the environment (`Kernel/World.lean` `Env`): `E.hash dom b` is the digest of byte string `b` under domain string `dom`, written `H(dom, b)`; `E.bytes d` is the canonical bytes of digest `d`, written `bytes(d)`; `E.cellBytes κ` and `E.turnBytes θ` are the canonical bytes of a cell and a Turn.
The deployed `Env` is CODEC's: a 32-byte digest and cSHAKE256 with the domain as customization string.
`nat64(n)` is CODEC's `Stream.nat64`, eight little-endian bytes; `nat32(n)` is `Stream.nat32`; `u32le(n)` is `index32 n`; `varint(n)` is `natBytes n`, LEB128 in shortest form.

## 1 Structure

### 1.1 Cells

A *cell* is a kind, a discipline and a slot list (`Kernel/Cell.lean` `Cell`).

```
cell        κ ::= { kind : n, discipline : disc, slots : slots }
disc          ::= rom | appendOnly | ram | value
slots         ::= (n, b)*
op            ::= set n b | erase n
```

A slot list is *canonical* when its keys strictly ascend (`Slots.ascending`).
`Slots.set` inserts or replaces and keeps keys ascending; `Slots.erase` removes a key.
The discipline fixes how a cell may change after its birth:

| discipline | writes the kernel admits | retirement | Lean |
|---|---|---|---|
| `rom` | none (`romWrite`) | none (`romRetire`) | `Discipline.rom` |
| `appendOnly` | `set` at a key the cell does not hold; never `erase` (`appendOnly`) | admitted | `Discipline.appendOnly` |
| `ram` | any `set` or `erase` | admitted | `Discipline.ram` |
| `value` | any, if the cell afterwards decodes as a value and is within its floor (section 6) | admitted | `Discipline.value` |

A written cell holds at most `Bounds.slotsPerCellMax` = 1024 slots (`postWrite`).
A cell's weight is its codec size: `Cell.weight κ = 9 + Σ (8 + |b|)` over its slots.

### 1.2 Entries, tombstones and pins

The World holds at each cell id an *entry* (`Kernel/World.lean` `Entry`).

```
entry       η ::= live κ v | tomb
```

`live κ v` is a live cell with version `v`.
The version counts the cell's writes: 0 at birth, one more per admitted write (`touchCheck`).
`tomb` is the tombstone a retirement leaves.
A tombstone is terminal: no step removes an entry, and a birth at a taken id is refused `idTaken` (`checkCreates`).

A *pin* is a digest of what a signer saw at an id (`pinOf`, KERNEL-54).
There are three pins, one domain each:

| what the id holds | pin |
|---|---|
| nothing | `H("nanodregg/kernel/pin-absent/v1", ε)` |
| `tomb` | `H("nanodregg/kernel/pin-tomb/v1", ε)` |
| `live κ v` | `H("nanodregg/kernel/pin-cell/v2", nat64(v) · cellBytes κ)` |

Absent, tombstone and live are distinct pins, so the sequence never-born, born, retired never returns to the absent pin (`Kernel/Proofs/Versions.lean` `pinOf_old_recurs` is the tooth on the pin without the tombstone domain).
`pinPre` is the (domain, bytes) input of `pinOf`, which theorems name in their collision disjuncts.

### 1.3 Cell kinds and slot layouts

The kernel reads no kind but through the discipline `value` (section 6).
The receive layer assigns kinds and reads slots (`Kernel/Receive/Call.lean`, "Cell kinds and slot layouts"; `Kernel/Receive/Ledger.lean` `kindAccount`).

| kind | number | discipline | slots | born by |
|---|---|---|---|---|
| package | `kindPackage` = 1 | `rom` | 0: the package's canonical bytes | `install`, `createOf` |
| object | `kindObject` = 2 | `ram` | 0: package id (absent for a data object); 1: owner; 2–15: extra law ids (`lawBase` = 2); 16 on: state (`stateBase` = 16) | `create`, `createOf` |
| grant | `kindGrant` = 3 | `appendOnly` | 0: target; 1: grantee; 2: issuer; 3: parent (absent at a root); 16: `observe`; 17: `mutate`; 1024 + i: enrolment ledger; 2048 + i: transfer ledger; 2560 + i: credit ledger; 4096 + j: `invoke j` | `grant`, genesis |
| member | `kindMember` = 4 | `ram` | 0: current key (`slotKey`); 1: digest of the next key (`slotNext`); 2: sponsor (`slotSponsor`; absent for a founder) | `enroll`, genesis |
| authority | `kindAuthority` = 5 | `ram` | 0: threshold; 1: certifier count; 2 + i: certifier `i`'s key (`certifierBase` = 2); 513 + i: certifier `i`'s committed next-key digest (`nextBase` = 513) | genesis only; written only by `rotateCertifier` (KERNEL-79) |
| account | `kindAccount` = 6 | `value` | 1: owner; 8: denomination; 9: balance; 10: floor | `issue`, `account` |

A *data object* has no package slot; a *programmed object* has one.
A *well* is an account whose denomination is the bytes of its own id (`issue`).
A ledger slot `base + i` holds, as `nat64`, what the counted right has left after its `i`-th spend; slot `base` holds the amount granted (`ledgerLeft`, section 5.4).

### 1.4 Ids

Every id is a digest.
No id is chosen by a writer: a follower re-derives every Turn from its call (section 3.8), so an id a receiver did not compute is `eventMismatch`.

| id | definition | Lean |
|---|---|---|
| transaction id | `H("nanodregg/kernel/tx/v1", callBytes c)` | `txIdOf` |
| content id of a ROM cell | `H("nanodregg/kernel/rom-id/v1", cellBytes κ)` | `romIdOf` |
| birth id of the `i`-th fresh birth | `H("nanodregg/kernel/cell-id/v1", bytes(txId) · u32le(i))` | `cellIdOf` |
| id of a born cell | `romIdOf κ` for `rom`, else `cellIdOf txId i` | `bornId` |
| member id | `H("nanodregg/kernel/member-id/v1", joinMessage origin sponsor next key)` | `memberId` |
| account id | `H("nanodregg/kernel/account/v1", bytes(owner) · bytes(asset))` | `accountId` |
| the World as a grant target | `H("nanodregg/kernel/world/v1", ε)`; no cell is born there | `worldId` |
| founder `i`, its root grant | `H("nanodregg/kernel/founder/v2", bytes(origin) · u32le(i))`, `H("nanodregg/kernel/founder-grant/v2", …)` | `founderId`, `founderGrantId` |
| the authority cell | `H("nanodregg/kernel/authority/v1", ∅)`, one per World (KERNEL-79) | `authorityId` |
| a `once` nullifier | `H("nanodregg/kernel/once/v1", bytes(src) · key)` | `onceNullifier` |

The index `i` of a birth counts the fresh births before it in the call's whole tree (`Walk.born`, `bornAt`).

### 1.5 The World

```
world W ::= { trie : Cells, journal : Journal, refusals : Refusals, rows : Rows,
              height : n, steps : n, chain : d, allowance : n, origin : d }
```

A World is four authenticated maps and five counters (`Kernel/World.lean` `World`).
The four maps are instances of one trie (`Kernel/Trie.lean` `T`): a persistent, path-compressed binary Merkle trie whose shape is a function of its key set.
Each node caches its digest; `empty`, `leaf` and `node` are hashed in domain `"nanodregg/kernel/trie/v1"` behind tag bytes 0, 1 and 2, and a node's hash commits its branching bit.

| map | key | leaf | depth | Lean |
|---|---|---|---|---|
| `trie` | `cell id` or `nullifier n` (`Slot`); bit 0 is the kind | `entry η` at a cell; `spent` at a nullifier (`Leaf`) | `Bounds.trieDepth` = 257 | `Cells`, `trieSpec` |
| `journal` | a transaction id | `(h, turnDigest θ)` | `Bounds.journalDepth` = 256 | `Journal`, `journalSpec` |
| `refusals` | `refusal (tx id)`, `refusal (count m win)`, `refusal (total origin win)`, `meter (ticks m win)` (`WindowSlot`) | `refused h code m` at `tx`; `count n` at the other three (`RefusalLeaf`) | `Bounds.refusalDepth` = 328 | `Refusals`, `refusalSpec` |
| `rows` | `head p rel` or `row ⟨p, rel, k⟩` (`RowSlot`) | `head count sum limit cap width retract floor` or `row amt val ver` (`RowLeaf`) | `Bounds.rowDepth` = 1320 | `Rows`, `rowSpec` |

The window trie `refusals` holds two kinds of key under one root: the refusal window's (`RefusalSlot`, KERNEL-44) and the meter's (`MeterSlot`, KERNEL-68).
Its keys are fixed width: a kind byte (0 `tx`, 1 `count`, 2 `total`, 3 `meter`), a digest, and eight bytes (`refusalKeyBytes`).
`total`'s digest is the World's `origin`, a filler.
`World.refusalAt` reads only refusal keys and `World.meterAt` reads only meter keys.

The counters:

| field | meaning |
|---|---|
| `height` | admitted Turns; a recorded refusal does not raise it |
| `steps` | admitted Turns plus recorded refusals (KERNEL-47); a genesis starts it at 0, a carry at the carried height |
| `chain` | the head of the log chain: `genesisChain origin = H("nanodregg/kernel/genesis/v1", bytes(origin))` at the start, then one link per step |
| `allowance` | the storage budget left, in bytes |
| `origin` | the World's identity (KERNEL-24), set at genesis and never written again |

`World.roots` is `rootsOf`: `H("nanodregg/kernel/roots/v1", bytes(cells root) · bytes(journal root) · bytes(refusals root) · bytes(rows root))`.
A head link is `headLink prev tag d rd = H("nanodregg/kernel/chain/v1", tag · bytes(prev) · bytes(d) · bytes(rd))`, where `tag` is 0 for a Turn and 1 for a recorded refusal, `d` the step's digest and `rd` the roots digest after the step (`chainNext`, `refusalLink`).

`World.entry W id` is the entry at `id`.
`World.live W id` is the cell of a live entry and `none` for a tombstone or nothing.
`World.taken W id` holds when the id has an entry.

### 1.6 Relations

A *relation* is a set of keyed rows under a parent object (KERNEL-46, KERNEL-48).
Its *head* `head p rel` holds the row count, the sum of the rows' `amt` column, the row `limit`, the sum `cap` (0: no sum column), the key `width`, whether rows may be retracted, and the relation's `floor`.
A row `row ⟨p, rel, k⟩` holds an `amt`, value bytes and a version.
`rel < 256`, `|k| = width ≤ Bounds.keyBytesMax` = 128, `limit ≤ Bounds.rowsPerRelationMax` = 4096.

The rows keys are `bytes(p) · varint(rel) · 00` for a head and `bytes(p) · varint(rel) · 01 · varint(|k|) · k` for a row (`rowKeyBytes`); the encoding is injective and prefix-free (`Kernel/Proofs/RowsSep.lean` `rowKeyBytes_append_inj`).

Versions and floors (KERNEL-54):

* an insert gives the row its relation's floor as its version;
* an upsert of a present row gives it one more than its version, and of an absent row the floor;
* a retract removes the row and raises the floor to `max floor ver + 1`;
* nothing else moves the floor while the parent lives.

A *row pin* is `H("nanodregg/kernel/row-pin-absent/v2", nat64(floor))` for an absent row and `H("nanodregg/kernel/row-leaf/v2", rowLeafBytes l)` for a present leaf `l` (`rowPin`).
A *range read* names a parent, a relation, a key prefix `pre`, a maximum `most` and a pin (`Kernel/Turn.lean` `RangeRead`).
Its listing is the rows of the relation whose key starts with `pre`, in key order, at most `most` of them (`rangeRows`); a longer listing is refused, never truncated.
A *range pin* is `H("nanodregg/kernel/range-pin/v2", rowsPrefix · varint(|pre|) · pre · nat64(floor) · nat32(len) · Σ (rowKeyBytes · bytes(rowDigest)))` over the listing (`rangePin`, `rangePinBytes`).
Both pins read the floor, so a listing or an absence observed once never recurs while the parent lives.
A retired parent's heads leave with it (`dropHeads`), and its floor reads 0 again.

### 1.7 The Turn

A *Turn* is the one log entry (`Kernel/Turn.lean` `Turn`).

```
turn       θ ::= { txId : d, notBefore : n, validUntil : n, touches : x*, creates : (d, κ)*,
                   nullifiers : d*, charge : n, event : b, rows : rowtouch*, ranges : range*,
                   member : d, ticks : n }
touch      x ::= { cell : d, seen : d, act : act }
act          ::= keep | write op* | retire
rowtouch     ::= { slot : rowslot, seen : d?, act : rowact }
rowslot      ::= head d n | row ⟨d, n, b⟩
rowact       ::= keep | insert n b | upsert n b | retract | declare n n n bool
range        ::= { parent : d, rel : n, pre : b, most : n, seen : d }
```

| field | meaning |
|---|---|
| `txId` | the transaction id of the signed call |
| `notBefore`, `validUntil` | the window: the heights the Turn may land at |
| `touches` | every existing or pinned-absent cell the Turn names, once each, with its pin `seen` and what the Turn does to it |
| `creates` | the cells the Turn bears, each with its id |
| `nullifiers` | one-time tokens, each spendable once in the life of the World |
| `charge` | what the Turn pays; must equal `Turn.weight θ` |
| `event` | the signed call's bytes |
| `rows` | the row slots the Turn names: a pinned slot carries `seen = some pin`; an `insert` and a `declare` carry none |
| `ranges` | the range reads the Turn pins |
| `member` | the member who signed the call |
| `ticks` | the ticks the call's tree of runs used; 0 for every body but an invoke |

A Turn writes or retires only a cell it observed: an act other than `keep` is on a touched cell.
A born id is never touched (`bornTouched`).

`Turn.weight θ = Turn.logWeight θ + Turn.growth θ`.
`logWeight` is the byte size of the Turn's log record, field by field in the codec's order.
`growth` is the most the Turn can add to the World: each born cell with its id, version and weight, each write's ops, each nullifier, and each row touch's growth (`RowTouch.growth`).
`Turn.weight` does not read `charge`, so a signer can state the price.

### 1.8 Steps and the log

```
step     s ::= turn θ | refusal r
refused  r ::= { txId : d, member : d, notBefore : n, validUntil : n, code : n, event : b, cancel : b }
event      ::= turn b | refusal b | cancel b b
```

A log is a list of steps (KERNEL-47).
A recorded refusal carries the call's transaction id, signer, window, the refusal's code (section 7.1), the call's bytes, and, for a cancel, the member's signature over `domCancel · bytes(txId)` (`Refused`).
`Step.event s` is what a follower re-derives the step from: a Turn's call, a judged refusal's call, or a cancel's signature and call; a refusal is a cancel exactly when its `cancel` field is non-empty.

## 2 The call

### 2.1 Unsigned and Call

```
unsigned u ::= { world : d, member : d, key : b, notBefore : n, validUntil : n,
                 pins : (d, d)*, maxCharge : n, body : β, rowPins : (rowslot, d)*, ranges : range* }
call     c ::= { unsigned : u, signature : b }
```

| field | meaning |
|---|---|
| `world` | the origin of the World the call is for |
| `member` | the signer's member id |
| `key` | the key the call is signed with |
| `notBefore`, `validUntil` | the window the Turn may land in |
| `pins` | the signer's observation: `(id, pin)` per cell |
| `maxCharge` | the price ceiling |
| `body` | the operation |
| `rowPins` | the row slots the signer observed, each with its row pin |
| `ranges` | the range reads the signer observed |

The signature is over `callMessage u = "nanodregg/kernel/call-signature" · unsignedBytes u` (`Ctx.callMessage`, KERNEL-42).

### 2.2 Bodies

```
body β ::= enroll key next origin join via | rotate key next | rotateCertifier i key next | install p
         | create pkg? laws state | createOf p laws state
         | write o edits via? | law o laws via? | invoke o j args budget via?
         | grant target grantee rights parent? | retire id
         | issue cap | account asset owner
         | transfer src dst amount via? once? | credit well acct amount via?
acct     ::= well asset | of owner asset
right    ::= observe | mutate | invoke j | enroll n | transfer n | credit n
```

| body | what it asks for | callable from a method |
|---|---|---|
| `enroll key next origin join via` | sponsor a new member with `key`, precommitting `next`; `join` is the key's consent to join `origin` through this sponsor; `via` is a World grant carrying `enroll` | no |
| `rotate key next` | move the signer's member to the precommitted `key` and precommit `next`; signed by `key` | no |
| `rotateCertifier i key next` | move certifier `i` of the World's authority to its committed successor `key` and commit `next`; the call's member is the authority cell; signed by `key` (KERNEL-79) | no |
| `install p` | bear a ROM package cell holding the bytes `p` | yes (KERNEL-75) |
| `create pkg laws state` | bear an object owned by the actor, programmed by `pkg` or a data object | no |
| `createOf p laws state` | install `p` if the signer's view holds no package there, then bear an object of it owned by the signer (KERNEL-77) | yes |
| `write o edits via` | set or erase state slots of a data object | no |
| `law o laws via` | replace a data object's extra laws | no |
| `invoke o j args budget via` | run method `j` of a programmed object | yes |
| `grant target grantee rights parent` | let `grantee` exercise `rights` on `target`, as the signer or, through `parent`, attenuated | yes |
| `retire id` | retire a grant, an object or an account (KERNEL-70) | no |
| `issue cap` | bear a new denomination's well, with floor `cap` | no |
| `account asset owner` | bear the empty account of `asset`'s denomination owned by `owner` | yes |
| `transfer src dst amount via once` | move `amount` from `src` to `dst`, with `src`'s owner's authority; `once` spends a nullifier | yes |
| `credit well acct amount via` | move `amount` of the well's floor to `acct` | yes |

The last column is `Body.callable`.
An `acct` reference `well asset` names the account at `asset`; `of owner asset` names `accountId owner asset` (`AcctRef.resolve`).

### 2.3 Requests and occasions

A law and a method see a *request* (`Req`): the signer (`agent`), whose authority the act exercises (`principal`), the object it is judged on (`self`), the call's window, the *occasion*, and the calling object (`caller`, `none` for a member's own call).

```
occasion ::= birth | write | relaw laws | adopt laws | invoke j | retire
```

| occasion | presented by | old state | new state | laws that judge |
|---|---|---|---|---|
| `birth` | `create` | the seed | the seed | the package's, then the extra laws |
| `write` | `write` | the object's state | the edited state | the extra laws in force |
| `relaw laws'` | `law` | the object's state | the same | the extra laws in force |
| `adopt laws'` | `law` | the object's state | the same | each incoming law not already in force |
| `invoke j` | `invoke` | the object's state | the run's new state | the package's, then the extra laws in force |
| `retire` | `retire` of an object | the object's state | the same | the package's, then the extra laws in force |

`Program.judge` (LANG) decides whether every law admits; a law that refuses is `lawDenied`.
A data object has no package, so only its extra laws judge it.

## 3 The transition

### 3.1 Overview

A signed call becomes at most one log step:

1. The Host's decision `Receive.submit` derives a Turn from the call and admits it, or refuses by name (section 3.6).
2. `Receive.judge` records an authenticated refusal as a step (`World.refuse`), or declines it (section 3.7).
3. A follower re-derives each step from its event (`Receive.rederive`, section 3.8).

The judgements:

| form | reading | Lean |
|---|---|---|
| `L; a; ω ⊢ β ⇓ π; ω'` | under view `L`, at position `a` and walk `ω`, body `β` derives draft `π` and walk `ω'` | `dispatch` |
| `W ⊢ c ⇒ θ` | on World `W`, call `c` derives Turn `θ` | `Receive.receive` |
| `W ⊢ θ ⟶ W'` | World `W` admits Turn `θ` and becomes `W'` | `World.admit` |
| `W ⊢ r ⟶ W'` | World `W` records refusal `r` and becomes `W'` | `World.refuse` |
| `W ⊢ s* ⟶* W'` | World `W` folds the log `s*` to `W'` | `World.fold` |

### 3.2 The view, the draft and the tree

A receiver never reads the World.
It reads the *pinned view* `L = pinned W pins`: `L id` is `ok (live W id)` when `id` is among the call's pins, and `unpinned id` otherwise (`Kernel/Receive/Call.lean` `pinned`).
`L` returns the World's current cell at a pinned id whatever the pin says; `submit` compares the pins before any receiver runs (KERNEL-66).
A method reads rows only through the *row view* (`rowView`): the leaves of the call's row pins under a relation, and the current listings of the call's signed range reads.

`readKind L id k` is the live pinned cell at `id` of kind `k`; it refuses `unpinned id`, `missingCell id` or `wrongKind id k`.
`slotDigest id κ k` decodes the digest at slot `k`; it refuses `malformedCell id k`.

A receiver produces a *draft* (`Draft`): births with their ids, effects `(id, act)`, nullifiers, and row effects.
Drafts of one call's tree are concatenated (`Draft.append`) and sealed once.
A *position* `a = ⟨actor, base, caller⟩` names whose authority the receiver spends, the fresh births before it in the tree, and the calling object (`At`).
A *walk* `ω = ⟨visited, pool, born⟩` holds the objects invoked so far, the ticks left in the tree's pool, and the fresh births so far (`Walk`).

`dispatch` sends each body to its receiver; each receiver but `invoke` advances `born` by its births (`stepped`).
A method's returned calls are derived by `tree`:

```
                                        β callable    L; ⟨o, ω.born, some o⟩; ω ⊢ β ⇓ π; ω'   (at depth n)
──────────────────────────  T-Deep     ─────────────────────────────────────────────────────────  T-Call    Receive.tree
tree 0 ω o β = callTooDeep              tree (n+1) ω o β = π; ω'
```

A call at depth 0 of the budget is `callTooDeep`.
A call of a body that is not callable is `notCallable` with the body's kind name.
Otherwise the call is derived by the same `dispatch` as a signed call, with the calling object as actor and as caller (`Kernel/Proofs/Tree.lean` `effect_as_signed`).
The signed call starts at depth `Bounds.callDepthMax` = 4 (`deriveWithTicks`).

### 3.3 The derivation rules

In each rule `u` is the call's unsigned part and `txId = txIdOf c`.
`req(self, principal, occ)` is `reqOf u self principal occ a.caller`.
`P` is the program (`Ctx.program`), supplied by LANG.

#### enroll

```
walk L worldId (enroll 0) true 8 via a.actor = ok _
readKind L via kindGrant = κ_g      spendAt 1024 via κ_g 1 (enrollSpent via) = e
verify(key, joinMessage origin a.actor next key, join)
m = memberId origin a.actor next key
κ = { kind 4, ram, [(0, key), (1, bytes(next)), (2, bytes(a.actor))] }
─────────────────────────────────────────────────────────────  D-Enroll    Receive.enroll
L; a ⊢ enroll key next origin join via ⇓ ⟨[(m, κ)], e?, [], []⟩
```

The sponsor holds, through `via`, a World grant chain for `enroll` rooted at a founder's grant.
The enrolment spends one unit of `via`'s own enrolment ledger (`enrollSpent` past what is left).
The new key's `join` verifies over `joinMessage` (`badJoin` otherwise).
`joinMessage origin sponsor next key = "nanodregg/kernel/join/v1" · bytes(origin) · bytes(sponsor) · bytes(next) · key`.
The member is born at the digest of that consent, so one consent enrols one member (a second birth there is `idTaken`).
That `origin` is the receiving World is `receive`'s check (`otherWorld`), not the receiver's.

#### rotate

```
readKind L u.member kindMember = κ     u.key = key
slotDigest u.member κ 1 = H("nanodregg/kernel/next-key/v1", key)
──────────────────────────────────────────────────────────────────  D-Rotate    Receive.rotate
L; a ⊢ rotate key next ⇓ ⟨[], [(u.member, write [set 0 key, set 1 bytes(next)])], [], []⟩
```

The call is signed by the new key, and the new key's digest is the one the member precommitted; otherwise `notPrecommitted`.
The write installs the key and the next precommitment.

#### rotateCertifier

```
readKind L u.member kindAuthority = κ     authorityOfCell κ = A     u.key = key
i < |A.certifiers|     A.next[i] = bytes(H("nanodregg/kernel/certify-next/v1", key))     key ∉ A.certifiers
──────────────────────────────────────────────────────────────────  D-RotateCertifier    Receive.rotateCertifier
L; a ⊢ rotateCertifier i key next ⇓ ⟨[], [(u.member, write [set (2 + i) key, set (513 + i) bytes(next)])], [], []⟩
```

The call names the World's authority cell as its member and is signed by the successor key; any premise failing is `notPreRotated i` (KERNEL-79).
The holder of the current certifier key cannot rotate it.
No other receiver writes the authority cell (`Kernel/Proofs/InvokeTree.lean` `effect_at_authority`).

#### install

```
P.checkInstall L p = ok       κ = { kind 1, rom, [(0, p)] }
──────────────────────────────────────────────  D-Install    Receive.install
L; a ⊢ install p ⇓ ⟨[(romIdOf κ, κ)], [], [], []⟩
```

LANG's install check decides the package; the cell is born at its content id.
An install of a package the World holds is admitted by no World: its id is taken (`idTaken`).

#### create

```
pkg = some p ⇒ readKind L p kindPackage = _           (checkPackage)
|laws| ≤ 14     ∀ l ∈ laws. readKind L l kindPackage = _   (checkLaws)
the keys of state are ≥ 16 and strictly ascend         (checkState)
self = cellIdOf txId a.base
P.judge L pkg laws state state req(self, a.actor, birth) = ok
decls = P.rels L p self if pkg = some p, else []
────────────────────────────────────────────────────────────────────────  D-Create    Receive.create
L; a ⊢ create pkg laws state ⇓ ⟨[(self, objectCell a.actor pkg laws state)], [], [], [(head self i, decls[i])]ᵢ⟩
```

Anyone may bear an object; its owner is the actor.
The laws in force, the package's and the extra ones, judge the seed on occasion `birth` with `old = new`.
The package's relations are declared with the object, in relation order.
`objectCell` writes the package id at 0, the owner at 1, the laws from 2 and the state as given (`Receive.objectCell`).

#### createOf

```
q = romIdOf (packageCell p)     L q = ok (some _)
L; ⟨u.member, a.base, a.caller⟩ ⊢ create (some q) laws state ⇓ π
──────────────────────────────────────────────────  D-CreateOf-Reuse    Receive.createOf
L; a ⊢ createOf p laws state ⇓ π

q = romIdOf (packageCell p)     L q ∈ { unpinned q, ok none }
L; ⟨a.actor, a.base + 1, a.caller⟩ ⊢ install p ⇓ π_i
withBorn L q (packageCell p); ⟨u.member, a.base, a.caller⟩ ⊢ create (some q) laws state ⇓ π_o
──────────────────────────────────────────────────  D-CreateOf-Install    Receive.createOf
L; a ⊢ createOf p laws state ⇓ π_o ++ π_i
```

The object is owned by the signer `u.member`, whoever the actor is.
If the signer's view holds the package live, the object is created of it.
Otherwise the package is installed one birth index later, and the object is created over the view with the new package cell in it (`withBorn`).
The object is born at the call's birth index either way, so its id does not depend on the branch.
Any other refusal of `L q` is the rule's refusal.

#### write

```
readKind L o kindObject = κ        packageOf o κ = none              (else hasMethods o)
ownerAuthority a.actor o κ mutate via = principal
∀ (i, _) ∈ edits. 16 + i < Bounds.slotKeyLimit                      (else stateKey i)
old = stateOf κ      new = applyEdits old edits
P.judge L none (lawsOf o κ) old new req(o, principal, write) = ok
─────────────────────────────────────────────────────────────  D-Write    Receive.write
L; a ⊢ write o edits via ⇓ ⟨[], writeOf o (diffOps old new), [], []⟩
```

Only a data object is written by `write`; a programmed object's state moves only by its methods.
The actor is the owner, or holds through `via` a chain for `mutate` whose root issuer is the owner.
Edit `(i, some b)` sets state slot `16 + i`; `(i, none)` erases it.
The extra laws judge the change on occasion `write`.
The effect is the slot operations from the old state to the new, or `keep` when there are none (`writeOf`).

#### law

```
readKind L o kindObject = κ        packageOf o κ = none              (else hasMethods o)
ownerAuthority a.actor o κ mutate via = principal
checkLaws L laws'        laws = lawsOf o κ        S = stateOf κ
P.judge L none laws S S req(o, principal, relaw laws') = ok
P.judge L none [l ∈ laws' | l ∉ laws] S S req(o, principal, adopt laws') = ok
─────────────────────────────────────────────────────────────  D-Law    Receive.law
L; a ⊢ law o laws' via ⇓ ⟨[], writeOf o (diffOps (lawSlotsOf κ) (lawSlots laws')), [], []⟩
```

The laws in force judge their replacement on occasion `relaw`.
Each incoming law not already in force judges the state it is adopted over on occasion `adopt` (KERNEL-27).
A law kept across the change is judged once, on `relaw`.

#### invoke

```
o ∉ ω.visited                                                        (else revisited o)
readKind L o kindObject = κ      packageOf o κ = some p              (else noMethods o)
ownerAuthority a.actor o κ (invoke j) via = principal
r = req(o, principal, invoke j)      fuel = min budget ω.pool
P.run L R p (stateOf κ) j args r fuel = (new, calls, rows, used)
used ≤ fuel                                                          (else overTicks)
∀ (slot, _) ∈ rows. slot is under o                                  (else rowParent o)
checkState new
P.judge L (some p) (lawsOf o κ) (stateOf κ) new r = ok
|calls| ≤ Bounds.callsMax
π₀ = ⟨[], writeOf o (diffOps (stateOf κ) new), [], rows⟩
ω₀ = ω with visited := o :: ω.visited, pool := ω.pool − used
fold of tree over calls, as o, from (π₀, ω₀) = (π, ω')
────────────────────────────────────────────────────────────────  D-Invoke    Receive.invoke
L; a; ω ⊢ invoke o j args budget via ⇓ π; ω'
```

The actor holds the owner's authority for `invoke j` (KERNEL-25).
The run takes at most the call's budget and what the tree's pool has left, and its reported ticks are asserted within that (`overTicks`).
A run edits only its own object's rows (`rowParent`).
The run's new state is canonical state, and the laws in force judge it on occasion `invoke j`.
A run returns at most `Bounds.callsMax` = 8 calls (`tooManyCalls`); each is derived depth-first, as the object, by `tree` one level down.
An object invoked twice in one tree is `revisited`.
The pool of a signed call is `min budget Bounds.treeTicksMax` for an invoke and 0 for any other body (`poolOf`); the Turn's `ticks` is the pool less what is left.

#### grant

```
grantee = worldId, or readKind L grantee kindObject or kindMember succeeds   (checkGrantee)
checkRights target rights
checkParent L a.actor target rights parent = e?
κ = { kind 3, appendOnly, target, grantee, issuer a.actor, parent?, rightSlots rights }
─────────────────────────────────────────────────────────  D-Grant    Receive.grant
L; a ⊢ grant target grantee rights parent ⇓ ⟨[(cellIdOf txId a.base, κ)], e?, [], []⟩
```

The grantee is a live member, a live object, or the World (a public grant).
The rights fit the target (section 5.3).
Without a parent the grant is a root issued by the actor; a root on the World or carrying `enroll` is `unrooted`.
With a parent the grant attenuates it, and a counted right's amount is spent from the parent's ledger (section 5.5).

#### retire

```
L id = ok (some κ)      κ.kind = 3      slotDigest id κ 2 = a.actor          (else notIssuer id)
────────────────────────────────────────────  D-Retire-Grant    Receive.retireCheck

L id = ok (some κ)      κ.kind = 2      slotDigest id κ 1 = a.actor          (else notOwner id)
P.judge L (packageOf κ) (lawsOf κ) (stateOf κ) (stateOf κ) req(id, a.actor, retire) = ok
────────────────────────────────────────────  D-Retire-Object    Receive.retireCheck

L id = ok (some κ)      κ.kind = 6      slotDigest id κ 1 = a.actor          (else notOwner id)
Value.ofCell κ = ⟨_, 0, 0⟩                                                  (else valueRemains id)
────────────────────────────────────────────  D-Retire-Account    Receive.retireCheck

each conclusion:  L; a ⊢ retire id ⇓ ⟨[], [(id, retire)], [], []⟩            Receive.retire
```

A grant is retired by its issuer; this is revocation.
An object is retired by its owner, and every law in force judges occasion `retire` over its last state; a law that refuses it makes the object permanent.
An account is retired by its owner once its balance and floor are both 0.
A member, a package or the authority is `notRetirable`.
An absent or retired `id` is `missingCell id`.
`retire` takes no `via`: the actor itself is the issuer or the owner.

#### issue

```
well = cellIdOf txId a.base        cap ≤ 2^63                     (else overflow well)
──────────────────────────────────────────────────────────────  D-Issue    Receive.issue
L; a ⊢ issue cap ⇓ ⟨[(well, accountCell a.actor bytes(well) cap)], [], [], []⟩
```

Anyone may bear a denomination.
The well is an account owned by the actor, its denomination its own id's bytes, balance 0, floor `cap`.

#### account

```
──────────────────────────────────────────────────────────────────────  D-Account    Receive.account
L; a ⊢ account asset owner ⇓ ⟨[(accountId owner asset, accountCell owner bytes(asset) 0)], [], [], []⟩
```

Anyone may open anyone's account of any denomination, once; a second open of the pair is `idTaken`.
The receiver reads no cell, so an open never pins the well.

#### transfer

```
readRef L src = (s, κ_s, v_s)       readRef L dst = (d, _, v_d)
ownerAuthority a.actor s κ_s (transfer 0) via = _
s ≠ d  (sameAccount)    0 < amount  (zeroAmount)    v_d.denom = v_s.denom  (assetMismatch d)
b_s = v_s.balance − amount   b_d = v_d.balance + amount   both fit i64   (overflow)
spendVia L 2048 via amount transferSpent = e?
────────────────────────────────────────────────────────────────────  D-Transfer    Receive.transfer
L; a ⊢ transfer src dst amount via once ⇓
   ⟨[], [(s, write [set 9 i64(b_s)]), (d, write [set 9 i64(b_d)])] ++ e?, [onceNullifier s k | once = some k], []⟩
```

The actor holds the source's owner's authority, directly or through a chain for `transfer`; `mutate` moves no value.
Through `via`, the move spends `amount` of `via`'s transfer ledger.
A `well asset` reference must name a well (`notWell`).
There is no solvency check here: an overdraft is the kernel's `belowFloor`.

#### credit

```
readAccount L well = (κ_w, v_w)     readRef L acct = (t, _, v_t)
ownerAuthority a.actor well κ_w (credit 0) via = _
v_w.denom = bytes(well)  (notWell)   well ≠ t  (sameAccount)   0 < amount  (zeroAmount)
v_t.denom = v_w.denom  (assetMismatch t)   amount ≤ v_w.floor  (overflow well)   v_t.floor + amount ≤ 2^63  (overflow t)
spendVia L 2560 via amount creditSpent = e?
─────────────────────────────────────────────────────────────────  D-Credit    Receive.credit
L; a ⊢ credit well acct amount via ⇓
   ⟨[], [(well, write [set 10 u64(v_w.floor − amount)]), (t, write [set 10 u64(v_t.floor + amount)])] ++ e?, [], []⟩
```

A credit line moves floor from the well to an account of its denomination.
It is the issuer's act: the actor holds the well's owner's authority, directly or through a chain for `credit`.
The denomination's floor sum does not move.
A line past the well's unissued headroom leaves the well below its own floor: `belowFloor`.

### 3.4 Receive and the seal

```
u.world = W.origin                                                   (else wrongWorld)
verify(u.key, callMessage u, c.signature)                            (else badSignature)
joinOrigin u.body ∈ { none, some W.origin }                          (else otherWorld)
keyRule L u = ok
L; ⟨u.member, 0, none⟩; ⟨[], poolOf u.body, 0⟩ ⊢ u.body ⇓ π; ω      at depth 4
sealTurn c π (poolOf u.body − ω.pool) = θ
───────────────────────────────────────────────────────────────  R-Receive    Receive.receive
W ⊢ c ⇒ θ        where L = pinned W u.pins
```

The first check is the World the call names (KERNEL-24).
`keyRule` requires the member cell to be pinned (`unpinned`), live, of kind member, and to hold `u.key` as its current key (`checkKey`: `unknownKey`); a rotation is exempt, and its receiver checks the precommitment.
The derivation reads the World only through `L` and the row view.

`sealTurn` builds the Turn:

1. every effect is on a pinned cell (`unpinned`), and no cell has two effects (`duplicateEffect`) (`effectsPinned`);
2. each row pin becomes a row touch with its effect, then each `insert` and `declare` without a pin is appended; a pinned act on an unpinned slot is `rowUnpinned`, a slot with two effects `duplicateRow` (`rowTouchesOf`);
3. each pin becomes a touch, in the signer's order, with the act of its effect or `keep` (`touchesOf`);
4. the Turn's `txId`, window, `event = callBytes c`, `ranges = u.ranges`, `member = u.member` and `ticks` are the call's;
5. `charge = Turn.weight θ`, and `charge > u.maxCharge` is `overPrice charge`.

### 3.5 Admission

`World.admit E W θ` runs `checkWith` against `W` alone, and on success commits.
Nothing is written before every check passes.
The checks, in order (`Kernel/World.lean` `checkWith`):

1. **Bounds** (`checkBounds`): touches ≤ 512, ops per write ≤ 256, creates ≤ 64, nullifiers ≤ 64, event ≤ 65536 bytes, slots per born cell ≤ 1024, slot keys < 2^32, values ≤ 65536 bytes, `validUntil ≤ notBefore + Bounds.windowMax`, `Turn.weight θ ≤ Bounds.weightMax` = 262144, `ticks ≤ Bounds.treeTicksMax` = 131072, every counter < 2^64 and every kind < 2^32, and the row and range bounds (`rows ≤ 32`, `ranges ≤ 4`, `rel < 256`, keys and prefixes ≤ 128 bytes). Each refuses `overBound` with the bound's name (section 7.3).
2. **Window** (`checkWindow`): `notBefore ≤ W.height + 1 ≤ validUntil`, else `outsideWindow`.
3. **Journal** (`checkJournal`): a journaled `txId` is `replayed h` with its height; a recorded `txId` is `refusedFinal code` with its code.
4. **Shape** (`checkShape`): distinct touched cells (`duplicateTouch`), distinct nullifiers (`duplicateNullifier`), distinct keys within each write (`duplicateKey`), canonical born cells (`nonCanonicalCell i`).
5. **Touches** (`touchCheck`, each touch in order, one lookup each):
   the pin equals `pinOf (W.entry id)` (`stale id`);
   `keep` changes nothing;
   `write ops` on `live κ v` requires `v + 1 < 2^64` (`overBound version`) and `postWrite` (`romWrite`, `appendOnly`, `overBound slotsPerCell`, `valueMalformed`, `belowFloor`), and leaves `live κ' (v + 1)`;
   `retire` on `live κ v` requires a non-ROM cell (`romRetire`) and leaves `tomb`;
   `write` or `retire` on a tombstone or nothing is `missingCell id`.
6. **Value** (`checkValue`): every born value cell decodes (`valueMalformed`) and is within its floor (`belowFloor`); over the touches' and births' flows at most `Bounds.denomsMax` = 8 denominations move (`overBound denoms`); each moves its balance sum by 0 (`notConserved`) and its floor sum by 0 unless the denomination is the bytes of an id the Turn bears (`floorNotConserved`).
7. **Nullifiers** (`checkNullifiers`): none is spent (`spent n`).
8. **Rows remain** (`checkRowsRemain`): a retired cell holds no row (`rowsRemain`).
9. **Ranges** (`checkRanges`, against the rows before the Turn): the parent is touched (`rowParentUnpinned`), the relation has a head (`noRelation`), `|pre| ≤ width` (`keyWidth`), the listing fits `most` (`rangeTooLong`), and its range pin is the signer's (`stale parent`).
10. **Rows** (`rowsRun`): the row bounds again (`overBound rows`), no slot twice (`duplicateRow`), then each row touch in order (`rowStep`, below), then a retired parent's heads leave (`dropHeads`).
11. **Charge** (`checkCharge`): `charge = Turn.weight θ` (`chargeMismatch weight`) and `charge ≤ W.allowance + back`, where `back` is what the touches and the row touches give back (`overAllowance`).
12. **Created ids** (`checkCreates`): a born ROM cell sits at its content id (`notContentId`); the born ids are distinct (`idTaken`), not touched (`bornTouched`), and not taken in `W` (`idTaken`).
13. **Meter** (`checkTicks`): the member's ticks this window plus `ticks` are at most `Bounds.ticksPerWindow` (`ticksBudget member`).
14. **Steps** (`checkSteps`): `W.steps + 1 < 2^64` (`overBound counter`).

A row touch, judged on the rows written so far in this Turn (`rowStepOn`):

| slot, act | checks, in order | result |
|---|---|---|
| `head p rel`, `declare limit cap width retract` | `rel < 256` (`overBound rows`); no pin (`rowShape`); `p` is born by this Turn (`declareLate`); `limit ≤ 4096`, `width ≤ 128`, `cap < 2^64` (`overBound rows`); no head there (`keyTaken`) | head with count 0, sum 0, floor 0 |
| `head p rel`, any other act | | `rowShape` |
| `row ⟨p, rel, k⟩`, any act | `p` is touched (`rowParentUnpinned`); `p` is live in `W` and not retired by this Turn (`orphanRow`); a head exists (`noRelation`); `|k| = width` (`keyWidth`) | |
| `keep` | the pin is present (`rowShape`) and equals the row pin at the floor of `W` (`stale p`) | unchanged |
| `insert amt v` | no pin (`rowShape`); the slot is empty (`keyTaken`); `count < limit` (`relationFull`); `sum + amt ≤ cap` (`relationCapped`); `|v| ≤ 65536` (`overBound valueBytes`) | row at version `floor`; count + 1, sum + amt |
| `upsert amt v` | pin as for `keep`; `|v| ≤ 65536`; the new version < 2^64 (`overBound version`); a fresh row needs `count < limit` (`relationFull`); `sum − old + amt ≤ cap` (`relationCapped`) | row at `ver + 1`, or at `floor` if fresh |
| `retract` | pin as for `keep`; the relation allows retracts (`retractForbidden`); the row is present (`missingRow`); `max floor ver + 1 < 2^64` (`overBound version`) | row removed; count − 1, sum − amt, floor `max floor ver + 1` |
| `declare` | | `rowShape` |

Every pin is judged against `W`, the World before the Turn: an earlier retract in the same Turn raises the floor in the rows being written but does not stale a later pin of the same Turn.

The commit (`commitWith`):

```
checkWith E W θ = ok (posts, (rows', freed))
H = W.height + 1
trie'     = W.trie with each post's entry, each born cell at live κ 0, each nullifier spent
journal'  = pruneJournal H (W.journal with txId ↦ (H, turnDigest θ))
refusals' = pruneRefusals H (commitMeter W θ)
────────────────────────────────────────────────────────────────────  A-Admit    World.admit
W ⊢ θ ⟶ { trie', journal', refusals', rows', height := H, steps := W.steps + 1,
           chain := chainNext W.chain θ (rootsOf trie' journal' refusals' rows'),
           allowance := W.allowance + credit posts + freed − θ.charge, origin := W.origin }
```

A post is what a touch leaves: the new entry, the storage it frees, and its value flows (`Post`).
A write frees `Cell.weight κ + opsWeight − Cell.weight κ'`; a retirement frees `counterWeight + Cell.weight κ` (`touchCheck`).
An upsert of a present row and a retract give back the replaced or removed row's weight with its key (`rowFreed`), and so does each dropped head.
`turnDigest θ = H("nanodregg/kernel/turn/v1", turnBytes θ)`.
The compiled transition `World.admitImpl` commits the rows `checkWith` reached without re-running them; it equals `World.admit` (`World.admit_eq_admitImpl`, private, `@[csimp]`, in `Kernel/World.lean`).

### 3.6 The Host's decision

`Receive.submit X W c`, in order (`Kernel/Receive/Submit.lean`):

1. a journaled `txIdOf c` is `replayed h`;
2. a recorded `txIdOf c` is `refusedFinal code`, without re-deriving;
3. `signedBy`: the World the call names (`wrongWorld`), the signature (`badSignature`), the World an enrolment's join names (`otherWorld`), and the key (`authKey`: `checkKey`, or for a rotation the `rotate` receiver);
4. `checkPins`: every cell pin, row pin and range read against `W`; the first that disagrees is `stale` (KERNEL-66);
5. `deriveTurn` on the pinned view: the receivers, then the seal;
6. `World.admit` of the derived Turn.

A refusal at 3 or 5 is a `Verdict.refused`; at 1, 2, 4 or 6 a `Verdict.rejected`.
Steps 3 and 5 are `receive` (`Kernel/Proofs/Receive.lean` `receive_signed`).
The pins are compared after `signedBy`, so a party holding no key of the member learns nothing of the World's cells from a `stale`.

### 3.7 Recorded refusals

A refusal is *recorded* when `judge` writes it into the log as a step; otherwise it is *declined* and leaves no trace (KERNEL-44).

`Receive.judge X W c` takes `submit`'s answer:

* admitted: the outcome is `admitted θ W'`;
* a `stale` verdict: declined;
* a verdict on a call that `signedBy` does not pass (`authenticated`): declined;
* otherwise `World.refuse` of `refusedOf c v`: recorded if it succeeds; if it refuses `refusalBudget` or `refusalsFull`, declined with that name as the verdict; any other refusal of `World.refuse`, declined with the original verdict.

`Verdict.code` gives a receive refusal its index in `refusalNames` and a kernel rejection `|refusalNames|` plus its index in `rejectNames` (section 7).

```
r.event ≤ 65536 bytes, counters < 2^64, r.validUntil ≤ r.notBefore + 1024,
   |r.cancel| ≤ 64                                         (overBound event / counter / window)
W.steps + 1 < 2^64                                         (overBound counter)
r.notBefore ≤ W.height + 1 ≤ r.validUntil                  (outsideWindow)
W.journalAt r.txId = none                                  (replayed h)
W.refusalAt (tx r.txId) is not a record                    (refusedFinal code)
refusalCount W r.member < Bounds.refusalsPerWindow          (refusalBudget)
refusalTotal W < Bounds.refusalsPerWindowMax                (refusalsFull)
w = refusalWindow W.height
refusals' = W.refusals with tx r.txId ↦ refused (W.height + 1) r.code r.member,
            count r.member w ↦ count (refusalCount + 1), total W.origin w ↦ count (refusalTotal + 1)
─────────────────────────────────────────────────────────────  A-Refuse    World.refuse
W ⊢ r ⟶ W with refusals := refusals', steps := W.steps + 1,
              chain := refusalLink W.chain r (rootsOf W.trie W.journal refusals' W.rows)
```

A recorded refusal moves only the refusals, the step counter and the chain.
It is final for its transaction id within its window: `submit` of the same call answers `refusedFinal` until the record is pruned.
A record outside the call's window is refused, so an early call's refusal is never recorded.
`refusedDigest r = H("nanodregg/kernel/refused/v1", refusedBytes r)` is the step digest in the chain.

A *cancel* is a recorded refusal of the member's own outstanding call, code `cancelled` (KERNEL-60).
`Receive.cancel X W c sig` requires the call to name this World (`wrongWorld`), `0 < |sig| ≤ 64` (`badSignature`), and `sig` to verify under the member's current key over `"nanodregg/kernel/cancel-signature" · bytes(txIdOf c)` (`badSignature`; `unknownKey` when the member cell is absent, has no key, or is not a member).
It then records `cancelOf c sig` through `World.refuse`, and is charged to the member's budget like any record.

### 3.8 Steps, the fold and re-derivation

```
W ⊢ θ ⟶ W'                 W ⊢ r ⟶ W'
──────────────────  S-Turn  ──────────────────  S-Refusal    World.step
W ⊢ turn θ ⟶ W'            W ⊢ refusal r ⟶ W'

                            W ⊢ s ⟶ W₁    W₁ ⊢ s* ⟶* W'
────────────  F-Nil         ─────────────────────────────  F-Cons    World.fold
W ⊢ [] ⟶* W                 W ⊢ s :: s* ⟶* W'
```

`World.step` is the one transition of a log.
`World.fold` is the follower's meaning of a log; a failing step is reported with its index.

A follower does not trust the writer's derivations.
`Receive.rederive X W e` re-derives a step from its event (`Kernel/Receive/Rederive.lean`):

| event | re-derivation | refused |
|---|---|---|
| `turn b` | decode `b`, then `submit` must admit | `eventMismatch` when it does not decode or a receiver refuses; the kernel's name when admission rejects |
| `refusal b` | decode `b`, then `judge` must record | `eventMismatch` otherwise |
| `cancel sig b` | decode `b`, then `cancel` with `sig` must record | `eventMismatch` when it does not decode; `cancelForged` otherwise |

`rederiveStep` requires the re-derived step to be the logged step (`eventMismatch` otherwise), and `rederiveLog` runs it along a log.

## 4 The window and the meter

### 4.1 Heights and windows

The height of a World counts its admitted Turns.
A Turn admitted at `W` lands at height `W.height + 1`.
A call's window is `[notBefore, validUntil]`, at most `Bounds.windowMax` = 1024 heights wide (`checkBounds`).
A Turn lands only inside its window (`checkWindow`), and a refusal is recorded only inside its call's window (`checkRefusal`).

### 4.2 The journal and its pruning

The journal maps each admitted transaction id to its height and Turn digest.
An exact retry inside its window is `replayed h` (KERNEL-7).
At every height `H` that is a multiple of `Bounds.windowMax`, the journal drops each entry `(h, _)` with `H ≥ h + 2 · Bounds.windowMax` (`pruneJournal`, `kept`, KERNEL-33).
Between multiples it is unchanged.
An entry is kept at least `Bounds.windowMax` heights after its window ends, so a call is admitted at most once (`Kernel/Proofs/Journal.lean` `submit_once`).
A World at height `H` can no longer answer for a call with `notBefore + 2 · Bounds.windowMax ≤ H` (`journalForgets`): absence of its id then says nothing.
Every World a genesis reaches holds fewer than `Bounds.journalMax` = 3 · 1024 entries (`reach_journal_bounded`).

### 4.3 The refusal window

`refusalWindow H = H / Bounds.windowMax`, as a `UInt64`.
A record lives at key `tx id` with the height `h = W.height + 1` it was refused at, its code and its member.
A member's count lives at `count m (refusalWindow W.height)`, and the World's total at `total origin (refusalWindow W.height)`.
A member records at most `Bounds.refusalsPerWindow` = 16 refusals a window (`refusalBudget`), and the World at most `Bounds.refusalsPerWindowMax` = 16384 (`refusalsFull`, KERNEL-55).
At every multiple `H` of `Bounds.windowMax` reached by a Turn, a record is kept while `H < h + 2 · Bounds.windowMax`, and a count, a total or a meter leaf only if it is of window `refusalWindow H` (`pruneRefusals`, `keptRefusal`).
A recorded refusal does not prune.

### 4.4 The meter

The meter counts each member's admitted ticks per window (KERNEL-68).
`ticksUsed W m` reads the meter leaf at `ticks m (refusalWindow (W.height + 1))`, the window the Turn lands in, and is 0 where there is none.
A Turn passes when `ticksUsed W θ.member + θ.ticks ≤ Bounds.ticksPerWindow` = 16 · 131072 (`checkTicks`); otherwise it is `ticksBudget member`, a recordable rejection.
`commitMeter` writes the sum to that leaf when `θ.ticks > 0`, before the prune.
A Turn with no ticks passes and writes nothing.

The meter counts in the window of `W.height + 1`; the refusal counts in the window of `W.height`.

## 5 Authority

### 5.1 Owners and principals

An object and an account name their owner in slot 1.
A call exercises the authority of a *principal*: the actor, or the root issuer of a grant chain the actor holds (`principalOf`).
`ownerAuthority actor o κ right via` requires the principal for `right` to be `o`'s owner (`noGrant o` otherwise) and returns it.
The receivers that change a cell they do not bear use it: `write` and `law` with `mutate`, `invoke` with `invoke j`, `transfer` with `transfer 0`, `credit` with `credit 0`.
`create`, `createOf`, `install`, `issue` and `account` need no authority beyond the signer's key.
`grant` needs a held parent only when it attenuates one (section 5.5).

### 5.2 Grant chains

```
readKind L g kindGrant = κ        slotDigest g κ 0 = obj                    (else grantTarget g)
granteeHolds g κ agent pub                                                  (else noGrant g)
κ holds slot rightKey right                                                 (else grantRight g)
slotDigest g κ 2 = issuer
κ has no slot 3:                         walk … (n+1) g agent = ok issuer
κ has slot 3 = parent:                   walk … (n+1) g agent = walk L obj right false n parent issuer
─────────────────────────────────────────────────────────────  W-Link    Receive.walk
walk L obj right pub 0 g agent = grantTooDeep                               W-Deep
```

A chain is walked from the actor's grant toward its root, at most `grantDepthMax` = 8 links.
Each link is a pinned live grant on the same target, held by the next agent, carrying the right.
The first link may be a public grant: its grantee is `worldId`, and any enrolled member holds it if its member cell is pinned and live (`granteeHolds` with `pub = true`, KERNEL-26).
Every later link is held by its child's issuer exactly.
The walk returns the root's issuer.
A malformed parent slot is `malformedCell g 3`.

`rightKey` places each right: `observe` at 16, `mutate` at 17, `enroll` at 1024, `transfer` at 2048, `credit` at 2560, `invoke j` at 4096 + j.

### 5.3 Rights

| right | meaning in the kernel |
|---|---|
| `observe` | on the World target: the holder may follow the World (`Receive.mayFollow`); no receiver reads it on any other target |
| `mutate` | `write` and `law` of a data object; it moves no value |
| `invoke j` | run method `j` of a programmed object |
| `enroll n` | enrol at most `n` members, directly or through grants carved from it; only on the World target |
| `transfer n` | move at most `n` out of the target account in all; never on the World target |
| `credit n` | extend at most `n` of credit out of the target well's floor in all; never on the World target |

`checkRights` refuses `rightTarget target` when a grant carries both `transfer` and `credit`, `enroll` with either, `enroll` off the World, or `transfer` or `credit` on it; and `overflow target` when a transfer or credit amount passes 2^63.
So a grant carries at most one counted kind, one ledger.

### 5.4 Counted rights and ledgers

A counted right's ledger occupies slots `base` to `base + ledgerSpendsMax` (`ledgerSpendsMax` = `enrollMax` = 256).
`ledgerLeft base g κ` is the number of ledger slots present and the amount in the last (`grantRight g` when there is none; `malformedCell` when it does not decode).
`spendAt base g κ units short` requires `units ≤ left` and, for `units > 0`, a free ledger slot, else `short`; its effect appends `left − units` at the next slot.
A grant is append-only, so what is left only falls.
`spendVia` spends through `via` and spends nothing for the owner's own authority.
The enrolment ledger is spent by `enroll` (`enrollSpent`); the transfer ledger by `transfer` (`transferSpent`); the credit ledger by `credit` (`creditSpent`).

### 5.5 Attenuation

```
parent = none:     target ≠ worldId and no right is enroll                 (else unrooted target)
parent = some p:   readKind L p kindGrant = κ_p
                   slotDigest p κ_p 0 = target                             (else grantTarget p)
                   slotDigest p κ_p 1 = actor                              (else noGrant p)
                   ∀ r ∈ rights. κ_p holds slot rightKey r                 (else grantWidens p)
                   the counted amount is spent from κ_p's ledger           (else grantWidens p)
─────────────────────────────────────────────────────────────  checkParent
```

An attenuated grant narrows a parent the actor holds as grantee on the same target.
Every right it carries is carried by the parent.
A counted right's amount is carved from the parent's ledger, and that spend is the grant's effect on the parent.
World rights and enrolment rights have no root but genesis: each founder's root grant carries `observe` and `enroll 256` on the World (`Receive.founderRoot`).
A root grant on any other target is born without a check that the actor owns the target; it confers nothing unless its issuer is the owner, because `ownerAuthority` compares the root issuer with the owner.

### 5.6 Revocation

Retiring a grant (`retire g` by its issuer) leaves a tombstone at `g`.
Every walk through `g` then reads no live cell there and refuses `missingCell g`, or `stale g` if the call pinned the grant's last live entry.
Nothing is born at `g` again.

## 6 Value

### 6.1 Value cells

A cell of discipline `value` holds, at kernel keys, a denomination (8), a balance (9, CODEC `i64`) and a floor (10, CODEC `u64`) (`Kernel/Value.lean`).
`Value.ofCell κ` is `⟨denom, balance, floor⟩` when the cell is a value cell, all three decode, and `|denom| ≤ Bounds.denomBytesMax` = 64; otherwise `none`.
A value is *within its floor* when `−floor ≤ balance` (`Value.withinFloor`).

### 6.2 Flows and conservation

A cell changing from `pre` to `post` flows `−value(pre) + value(post)` into its denomination's balance sum and floor sum (`flowsOf`).
A cell that is not a value cell flows nothing.
`checkValue` sums the flows of the touches and the births per denomination (`accumulate`) and requires:

* at most `Bounds.denomsMax` denominations (`overBound denoms`);
* each balance sum unchanged (`notConserved denom`);
* each floor sum unchanged unless the denomination is the bytes of an id the Turn bears (`floorNotConserved denom`).

Every written value cell decodes and is within its floor (`postWrite`), and so is every born one (`checkValue`).
A retired value cell flows its whole value out, so retiring an account with a nonzero balance or floor is `notConserved` or `floorNotConserved` unless another cell of the Turn takes it.

### 6.3 Denominations, wells and issuance

A denomination is the bytes of its well's id.
`issue cap` bears the well with floor `cap` and balance 0, in the Turn that bears the denomination, so its floor sum may move only then.
There is no mint and no burn: issuing is a transfer out of the well, burning is a transfer into it.
The well's floor bounds what can be outstanding of its denomination, since the well's balance stays at or above minus its floor.
A credit line moves floor from the well to an account; the floor sum is unchanged, so the cap still bounds what is outstanding.
`World.valueSum`, `World.floorSum` and `World.outstanding` are the specification measures over a World's live value cells (`Kernel/World.lean`).

Conservation is a theorem of the kernel, not of the receivers: `Kernel/Proofs/Value.lean` `admit_value` states that every Turn `World.admit` admits leaves every denomination's balance sum as it was, and `admit_floors` that it leaves the floor sum of every denomination it does not bear.

### 6.4 Storage

The allowance is the World's storage budget.
A Turn pays `charge = Turn.weight θ` and gets back what its touches and row touches free; it is refused `overAllowance` when it cannot pay.
`World.weight` is the storage the World holds: each cell entry with its id, each spent nullifier, each rows entry with its key; the journal and the window trie are not in it.

## 7 The refusal table

### 7.1 Classes and codes

Every way the kernel ends without success has a name (CHARTER law 7).
There are two tables: the receive layer's `Refusal` (`Kernel/Receive/Call.lean`) and the kernel's `Reject` (`Kernel/World.lean`).
Each name is its constructor's (`Refusal.name`, `Reject.name`); the wire drops the data, which `Repr` prints for diagnostics only.
Each table's names are in constructor order in `refusalNames` and `rejectNames` (`Kernel/Receive/Submit.lean`).
A recorded refusal's code is its index: receive refusals 0–49, kernel rejections 50–89 (`Verdict.code`); `codeName` reads a code back (`Kernel/Proofs/Refusals.lean` `codeName_code`).
`missingCell`, `rangeTooLong` and `duplicateRow` are names in both tables; their codes differ.

The class column:

| class | meaning |
|---|---|
| **R** | recordable: `judge` records it when the call passes `signedBy`, the record is inside its window, and the member's and World's budgets have room |
| **D** | declined: never recorded |
| **D/R** | declined when `signedBy` raises it (the signer is not authenticated); recordable when a receiver raises it |
| **F** | follower only: raised by `rederive`, never by the Host's decision |
| **C** | a code only: the code of a cancel record; no check raises it |

A rejection of `World.admit` is reached only past `signedBy` (`Verdict.verified`).
`judge` records a verdict only if `World.refuse` accepts the record, and `checkRefusal` re-checks the record's event length, window width, window ends and window.
So `outsideWindow`, and an `overBound` caused by the call's event length, window width or window ends, are declined although `World.admit` raises them past `signedBy`.

### 7.2 Receive refusals (`Refusal`)

| code | name | data | raised by | class |
|---|---|---|---|---|
| 0 | `wrongWorld` | — | `receive`, `signedBy`, `cancelAuth`: the call names another World | D |
| 1 | `badSignature` | — | `checkSignature` (in `receive`, `signedBy`), `cancelAuth` | D |
| 2 | `unknownKey` | member | `checkKey`: the member cell is not live, not a member, or `key` is not its current key; `cancelAuth` | D |
| 3 | `notPrecommitted` | member | `rotate`: `key` is not the signed key, or its digest is not the precommitted one | D |
| 4 | `badJoin` | — | `enroll`: the join does not verify under the new key | R |
| 5 | `otherWorld` | — | `receive`, `signedBy`: the enrolment's join names another World | D |
| 6 | `unpinned` | cell | `pinned`: a read of an unpinned id; `effectsPinned`: an effect on an unpinned cell | D/R |
| 7 | `missingCell` | cell | `readKind`, `retireCheck`: no live cell at a pinned id | D/R |
| 8 | `wrongKind` | cell, expected kind | `readKind` | D/R |
| 9 | `malformedCell` | cell, slot | `slotDigest`, `packageOf`, `walk`, `ledgerLeft`, `readAccount`, `retireCheck`; LANG's `readPackage` | D/R |
| 10 | `lawDenied` | law, reason | LANG `Lang/Program.lean` `judgeOneWith`: a law refused the occasion | R |
| 11 | `program` | reason | LANG: install check, type, budget or method error | R |
| 12 | `stateKey` | key | `checkStateFrom`: a state key below 16 or out of order; `write`: an edit key past 2^32 | R |
| 13 | `tooManyLaws` | — | `checkLaws`: more than 14 laws | R |
| 14 | `hasMethods` | object | `write`, `law` on a programmed object | R |
| 15 | `noMethods` | object | `invokeRun` (`requireMethods`) on a data object | R |
| 16 | `noGrant` | cell | `ownerAuthority`: the principal is not the owner; `granteeHolds`; `checkParent`: the parent's grantee is not the actor | R |
| 17 | `grantTarget` | grant | `walk`, `checkParent`: the grant's target is not the object | R |
| 18 | `grantRight` | grant | `walk`: the link lacks the right; `ledgerLeft`: no ledger | R |
| 19 | `grantWidens` | parent | `checkParent`: a right the parent lacks, or a counted amount past the parent's | R |
| 20 | `unrooted` | target | `checkParent`: a root grant on the World or carrying `enroll` | R |
| 21 | `enrollSpent` | grant | `enroll`: the grant's enrolment count is used up | R |
| 22 | `transferSpent` | grant | `transfer` (`spendVia`): past the transfer cap left or the ledger's end | R |
| 23 | `creditSpent` | grant | `credit` (`spendVia`): past the credit cap left or the ledger's end | R |
| 24 | `rightTarget` | target | `checkRights` | R |
| 25 | `notIssuer` | grant | `retireCheck`: a grant retired by another than its issuer | R |
| 26 | `notOwner` | cell | `retireCheck`: an object or account retired by another than its owner | R |
| 27 | `valueRemains` | cell | `retireCheck`: an account with nonzero balance or floor | R |
| 28 | `notRetirable` | cell | `retireCheck`: a member, package or authority | R |
| 29 | `grantTooDeep` | — | `walk`: more than 8 links | R |
| 30 | `overPrice` | charge | `sealTurn`: the weight passes `maxCharge` | R |
| 31 | `eventMismatch` | — | `rederive`, `rederiveStep` | F |
| 32 | `duplicateEffect` | cell | `effectsPinned`: one cell given two effects | R |
| 33 | `sameAccount` | — | `transfer`, `credit` | R |
| 34 | `zeroAmount` | — | `transfer`, `credit` | R |
| 35 | `assetMismatch` | cell | `transfer`, `credit`: denominations differ (names the destination) | R |
| 36 | `overflow` | cell | `transfer`: a balance past i64; `credit`: past the well's floor or a floor past 2^63; `issue`: cap past 2^63; `checkRights` | R |
| 37 | `notWell` | cell | `readRef`, `credit`: the account is not a well | R |
| 38 | `notCallable` | kind | `tree`: a method returned a body objects may not call | R |
| 39 | `callTooDeep` | — | `tree`: past depth 4 | R |
| 40 | `revisited` | object | `invoke`: an object invoked twice in one tree | R |
| 41 | `tooManyCalls` | — | `invoke`: more than 8 calls | R |
| 42 | `overTicks` | — | `invoke`: a run reported more ticks than it was given | R |
| 43 | `rowUnpinned` | parent, rel, key | `rowTouchesOf`: an upsert, retract or keep on an unpinned row slot | R |
| 44 | `rangeUnpinned` | parent, rel | `rowView`: a run read a range of a relation with no head | R |
| 45 | `rangeTooLong` | parent | `rowView`: a signed range holds more than `most` rows | R |
| 46 | `rowParent` | object | `invoke`: a row edit under another object | R |
| 47 | `duplicateRow` | parent | `rowTouchesOf`: one row slot given two effects | R |
| 48 | `cancelled` | — | the code of a cancel record (`cancelOf`) | C |
| 49 | `cancelForged` | — | `rederive`: a logged cancel that `cancel` does not record | F |

A `Program` returns `Refusal` values, so LANG may return any name of this table; the deployed LANG glue raises `lawDenied`, `program` and the reads' names.

### 7.3 Kernel rejections (`Reject`)

| code | name | data | raised by | class |
|---|---|---|---|---|
| 50 | `overBound` | bound | `checkBounds`, `touchCheck`, `postWrite`, `checkValue`, `rowsRun`, `rowStepOn`, `checkSteps`, `checkRefusedBounds` (section 7.4) | R |
| 51 | `replayed` | height | `checkJournal`, `submit`, `checkRefusal`: the id is journaled | D |
| 52 | `duplicateTouch` | cell | `checkShape` | R |
| 53 | `duplicateNullifier` | nullifier | `checkShape` | R |
| 54 | `duplicateKey` | cell, key | `checkShape`: a write with a key twice | R |
| 55 | `nonCanonicalCell` | index | `checkShape`: a born cell's keys do not ascend | R |
| 56 | `outsideWindow` | — | `checkWindow`, `checkRefusal` | D |
| 57 | `stale` | cell or parent | `touchCheck`, `checkRanges`, `rowStepOn`, `checkPins` | D |
| 58 | `spent` | nullifier | `checkNullifiers` | R |
| 59 | `chargeMismatch` | expected | `checkCharge`: `charge ≠ Turn.weight` | R |
| 60 | `overAllowance` | — | `checkCharge` | R |
| 61 | `idTaken` | cell | `checkCreates`: a born id taken in the World or born twice | R |
| 62 | `notContentId` | cell | `checkCreates`: a born ROM cell off its content id | R |
| 63 | `bornTouched` | cell | `checkCreates`: a born id also touched | R |
| 64 | `missingCell` | cell | `touchCheck`: a write or retire of a tombstone or nothing | R |
| 65 | `romWrite` | cell | `postWrite` | R |
| 66 | `romRetire` | cell | `touchCheck` | R |
| 67 | `appendOnly` | cell, key | `postWrite`: an overwrite or erase of an append-only cell | R |
| 68 | `valueMalformed` | cell | `checkValueCell` (in `postWrite`, `checkValue`) | R |
| 69 | `belowFloor` | cell | `checkValueCell` | R |
| 70 | `notConserved` | denomination | `checkValue` | R |
| 71 | `floorNotConserved` | denomination | `checkValue` | R |
| 72 | `refusedFinal` | code | `checkJournal`, `submit`, `checkRefusal`: the id holds a record | D |
| 73 | `refusalBudget` | — | `checkRefusal`: the member's window count is full | D |
| 74 | `keyTaken` | parent | `rowStepOn`: an insert at a present row, or a declare at a present head | R |
| 75 | `relationFull` | parent | `rowStepOn`: `count = limit` | R |
| 76 | `relationCapped` | parent | `rowStepOn`: the sum would pass `cap` | R |
| 77 | `rowParentUnpinned` | parent | `rowStepOn`, `checkRanges`: the parent is not touched | R |
| 78 | `orphanRow` | parent | `rowStepOn`: the parent is not live, or is retired by this Turn | R |
| 79 | `rowsRemain` | parent | `checkRowsRemain` | R |
| 80 | `keyWidth` | parent | `rowStepOn`: `|k| ≠ width`; `checkRanges`: `|pre| > width` | R |
| 81 | `noRelation` | parent | `rowStepOn`, `checkRanges`: no head | R |
| 82 | `retractForbidden` | parent | `rowStepOn` | R |
| 83 | `declareLate` | parent | `rowStepOn`: a declare in a Turn that does not bear the parent | R |
| 84 | `rangeTooLong` | parent | `checkRanges` | R |
| 85 | `duplicateRow` | parent | `rowsRun` | R |
| 86 | `rowShape` | parent | `rowStepOn`: an act on the wrong slot kind, or a pin present where none belongs or absent where one must be | R |
| 87 | `missingRow` | parent | `rowStepOn`: a retract of an absent row whose absent pin matched | R |
| 88 | `refusalsFull` | — | `checkRefusal`: the World's window total is full | D |
| 89 | `ticksBudget` | member | `checkTicks` | R |

`stale` is never recorded (KERNEL-54): a pin observed on the fold and stale now is stale at every World the fold reaches, up to a collision on the pin inputs (`stale_behind_forever`), so the fold settles it; a pin naming a future version is stale now and not final.

### 7.4 Bounds named by `overBound`

| bound | refused when | value | raised by |
|---|---|---|---|
| `touches` | more touches | `Bounds.touchesMax` = 512 | `checkBounds` |
| `opsPerWrite` | more ops in a write | `Bounds.opsPerWriteMax` = 256 | `checkBounds` |
| `creates` | more births | `Bounds.createsMax` = 64 | `checkBounds` |
| `nullifiers` | more nullifiers | `Bounds.nullifiersMax` = 64 | `checkBounds` |
| `event` | a longer event; a recorded refusal's longer event or cancel signature | `Bounds.eventBytesMax` = 65536; `Bounds.cancelBytesMax` = 64 | `checkBounds`, `checkRefusedBounds` |
| `slotsPerCell` | a born or written cell with more slots | `Bounds.slotsPerCellMax` = 1024 | `checkBounds`, `postWrite` |
| `slotKey` | a slot key at or past the limit | `Bounds.slotKeyLimit` = 2^32 | `checkBounds` |
| `valueBytes` | a longer slot or row value | `Bounds.valueBytesMax` = 65536 | `checkBounds`, `rowStepOn` |
| `window` | `validUntil > notBefore + windowMax` | `Bounds.windowMax` = 1024 | `checkBounds`, `checkRefusedBounds` |
| `weight` | `Turn.weight` past the bound | `Bounds.weightMax` = 262144 | `checkBounds` |
| `counter` | a window end, charge, code or step count at or past 2^64, or a kind at or past 2^32 | `Bounds.counterLimit`, `Bounds.kindLimit` | `checkBounds`, `checkSteps`, `checkRefusedBounds` |
| `denoms` | more denominations moved | `Bounds.denomsMax` = 8 | `checkValue` |
| `rows` | more row touches or ranges, `rel ≥ 256`, a key or prefix past 128 bytes, a declare past its limits | `Bounds.rowsMax` = 32, `Bounds.rangesMax` = 4, `Bounds.keyBytesMax` = 128, `Bounds.rowsPerRelationMax` = 4096 | `checkBounds`, `rowsRun`, `rowStepOn` |
| `version` | a cell's or row's version, or a floor, would reach 2^64 | `Bounds.counterLimit` | `touchCheck`, `rowStepOn` |
| `ticks` | `ticks` past the tree budget | `Bounds.treeTicksMax` = 131072 | `checkBounds` |

### 7.5 Genesis and carry refusals

A World starts at a genesis or a carry, not at a step; their refusals are not recorded.

| name | refused when | Lean |
|---|---|---|
| `nameTooLong`, `nonceTooLong` | the name or the Host's nonce is longer than 65536 bytes | `GenesisRefusal`, `CarryRefusal` |
| `tooManyFounders` | more than 65536 founders | `GenesisRefusal` |
| `founderKeyTooLong i`, `founderNextTooLong i` | founder `i`'s key or next-key digest bytes are longer than 65536 | `GenesisRefusal` |
| `tooManyCertifiers` | the certifiers and two counts do not fit one cell | `GenesisRefusal` |
| `certifierTooLong i`, `repeatedCertifier i` | certifier `i`'s key is too long, or repeats an earlier one | `GenesisRefusal` |
| `badThreshold` | the threshold is past the certifier count, or zero with certifiers listed | `GenesisRefusal` |
| `allowanceTooLarge` | the allowance plus the World's storage is not below 2^64 | `GenesisRefusal`, `CarryRefusal` |
| `heightTooLarge` | the carried height is not below 2^64 | `CarryRefusal` |
| `journalTooLong` | the carried journal has more than `Bounds.journalMax` entries | `CarryRefusal` |
| `entryTooLarge` | a carried digest is longer than 65536 bytes, or an entry's height not below 2^64 | `CarryRefusal` |

`Receive.genesis` checks these (`checkGenesis`) and builds `genesisWorld`: each founder's member cell and root World grant, and the authority cell, under the origin `originOf` (`Kernel/Receive/Follow.lean`).
`Receive.carry` builds a new World from a `Carried` state (cells, allowance, height, journal, rows) under a new origin; the refusals, chain and origin are not carried.

## 8 Theorems

Each theorem below is about the relation this document restates.
Premises such as canonical tries (`World.Canon`, `World.RowsCanon`, `World.JournalCanon`, `World.RefusalsCanon`) hold of every World a fold reaches from a genesis.

### 8.1 Derivation

| theorem | file | statement |
|---|---|---|
| `receive_wrongWorld` | `Kernel/Proofs/Receive.lean` | a call naming another World is refused `wrongWorld`. |
| `receive_congr` | `Kernel/Proofs/Receive.lean` | two Worlds with one origin that agree on the call's pinned cells and on its row view derive the same Turn or the same refusal. |
| `receive_signed` | `Kernel/Proofs/Receive.lean` | `receive` is `signedBy` followed by `deriveTurn` on the pinned view. |
| `submit_ok` | `Kernel/Proofs/Receive.lean` | a submission commits exactly `World.admit` of what `receive` derived. |
| `effect_as_signed` | `Kernel/Proofs/Tree.lean` | a call a method returns is a callable body, derived by the same `dispatch` as a signed call with the calling object as actor. |
| `write_authorized` | `Kernel/Proofs/Authority.lean` | a derived `write` comes from the owner, or from an actor holding a `mutate` chain whose root issuer is the owner. |
| `law_judged` | `Kernel/Proofs/Authority.lean` | a derived `law` passed the owner authority, the `relaw` judgement by the laws in force, and the `adopt` judgement by the added laws. |
| `key_current` | `Kernel/Proofs/Authority.lean` | every derived call but a rotation is signed by its member's current key. |
| `grant_rooted` | `Kernel/Proofs/Authority.lean` | a derived grant on the World or carrying `enroll` has a parent. |
| `grant_carves` | `Kernel/Proofs/Authority.lean` | a derived grant carrying `enroll` carves its count from a parent the actor holds on the same target. |

### 8.2 Admission

| theorem | file | statement |
|---|---|---|
| `admit_window` | `Kernel/Proofs/Fold.lean` | an admitted Turn lands inside its window. |
| `admit_frame` | `Kernel/Proofs/Frame.lean` | a cell the Turn neither writes, retires nor bears keeps its entry. |
| `admit_nullifiers` | `Kernel/Proofs/Frame.lean` | each nullifier of an admitted Turn was unspent and is spent, and the spent set only grows. |
| `fold_rom` | `Kernel/Proofs/Frame.lean` | a live ROM cell survives every fold unchanged. |
| `check_local` | `Kernel/Proofs/Local.lean` | two Worlds that agree on what `check` reads check a Turn alike. |
| `admit_stale_pin` | `Kernel/Proofs/StaleOnly.lean` | a `stale y` rejection names a cell pin, a row pin or a range pin under `y` that disagrees with the World. |
| `stale_behind_forever` | `Kernel/Proofs/Versions.lean` | a cell pin observed on the fold and stale now differs from the pin at every World the fold reaches, or the hash collides among the two pin inputs. |
| `row_stale_behind_forever`, `range_stale_behind_forever` | `Kernel/Proofs/Versions.lean` | the same for row and range pins, or the parent is a tombstone. |
| `admit_row_touch` | `Kernel/Proofs/Rows.lean` | an admitted row touch is a `rowStep` from rows that read at its slot what the World read, and the World after reads what that step left. |
| `head_sum` | `Kernel/Proofs/RowsHead.lean` | a head's count and sum are its rows' count and `amt` sum, within its limit and cap. |
| `admit_comm` | `Kernel/Proofs/RowsComm.lean` | two Turns with disjoint footprints outside the heads, whose inserts fit together, whose windows and charges allow both, admit in either order to Worlds that agree on cells, nullifiers and every rows slot. |
| `rowsRun_eq`, `commitTrie_eq` | `Kernel/Proofs/Admit.lean` | the batched rows and trie writes equal the one-at-a-time writes the proofs read. |
| `Reject.name_injective` | `Kernel/Proofs/Admit.lean` | two rejections with one wire name have one constructor. |
| `Refusal.name_injective` | `Kernel/Proofs/Receive.lean` | two receive refusals with one wire name have one constructor. |

### 8.3 Logs, refusals and the window

| theorem | file | statement |
|---|---|---|
| `fold_chain` | `Kernel/Proofs/Fold.lean` | the chain a fold reaches is the log's steps linked, each with the roots digest it left. |
| `head_roots` | `Kernel/Proofs/Cells.lean` | a head record matching a step's chain names that World's four roots, or two inputs the opening compares collide. |
| `refuse_frame` | `Kernel/Proofs/Refuse.lean` | a recorded refusal changes no cell, journal entry, height, allowance or origin. |
| `refuse_window` | `Kernel/Proofs/Fold.lean` | a refusal is recorded inside its call's window. |
| `submit_refused_final` | `Kernel/Proofs/Refusals.lean` | after a refusal of call `c` is recorded, `submit c` answers `refusedFinal` with its code at every later World below the prune height. |
| `submit_once` | `Kernel/Proofs/Journal.lean` | a call admitted once is admitted by no World a later log reaches. |
| `fold_retains` | `Kernel/Proofs/Journal.lean` | a journal entry stays while the height is below its height plus `2 · windowMax`. |
| `reach_journal_bounded` | `Kernel/Proofs/Journal.lean` | every World a genesis reaches holds fewer than `3 · windowMax` journal entries. |
| `fold_refusals_bounded` | `Kernel/Proofs/RefusalsBound.lean` | every fold keeps at most `3 · refusalsPerWindowMax` records, `refusalsPerWindowMax` counts and one total. |
| `refusalsFull_independent` | `Kernel/Proofs/RefusalsBound.lean` | there is a well-formed World where every member has room in its budget and a refusal is declined `refusalsFull`. |
| `refusalCount_eq_of_counted` | `Kernel/Proofs/RefusalsCounted.lean` | on a World that passes `refusalsCounted`, each count equals its member's records this window. |
| `admit_refusalAt`, `admit_meterAt`, `admit_meterAt_self` | `Kernel/Proofs/Refusals.lean` | what an admission does to the refusal window and to the meter, key by key. |
| `stale_declined_before_receive` | `Kernel/Proofs/Rederive.lean` | an authenticated call whose pins disagree is `stale` and declined, whatever any receiver would say. |
| `judge_stale_declined`, `judge_recorded_not_stale` | `Kernel/Proofs/Rederive.lean` | `judge` declines every stale verdict, and nothing it records is stale. |
| `rederiveLog_iff` | `Kernel/Proofs/Rederive.lean` | the re-deriver accepts a log exactly when the log folds and every step is the Host's own decision (`Honest`). |
| `rotate_stales_outstanding` | `Kernel/Proofs/RotateStale.lean` | after a rotation, no Turn derived from a call that pinned the member's earlier entry is admitted, up to a collision among the two pin inputs. |
| `retire_final` | `Kernel/Proofs/WriteNext.lean` | after an admitted retirement of `o`, every later World holds a tombstone at `o` and no live cell. |

### 8.4 Value and storage

| theorem | file | statement |
|---|---|---|
| `admit_value` | `Kernel/Proofs/Value.lean` | every admitted Turn leaves every denomination's balance sum unchanged. |
| `admit_floors` | `Kernel/Proofs/Value.lean` | every admitted Turn leaves the floor sum of every denomination it does not bear unchanged. |
| `admit_world_weight` | `Kernel/Proofs/Weight.lean` | the World's weight grows by the Turn's growth less what its touches and row touches free. |
| `fold_potential` | `Kernel/Proofs/Weight.lean` | `145 · weight + 84 · allowance` never rises over a fold. |
| `allowance_bounds_world` | `Kernel/Proofs/Weight.lean` | every World a fold reaches has `145 · weight ≤ 145 · weight₀ + 84 · allowance₀`. |
| `retire_frees_credit` | `Kernel/Proofs/WriteNext.lean` | a retirement returns the retired entry's weight and its heads' to the allowance, less the charge. |
| `honest_ledgerContiguous` | `Kernel/Proofs/LedgerNext.lean` | every honest folded log keeps every grant's ledgers contiguous. |
| `honest_rooted` | `Kernel/Proofs/Rooted.lean` | every honest folded log keeps `WorldRooted R`: every live grant is append-only and targeted, and every live grant on the World has a parent or satisfies `R`. |

### 8.5 Spec claims about the kernel

| claim | definition | top theorem | statement |
|---|---|---|---|
| B1 | `Integrity.authority` (`Spec/Proofs/Auth.lean`) | `top_integrity_authority` | along an audited log, every step that changes a live cell is a Turn derived by `receive` from the call its event decodes to, and that call was entitled to the change. |
| B2 | `Integrity.value` (`Spec/Proofs/Claims.lean`) | `top_integrity_value` (`Spec/Proofs/Deployed.lean`) | along any fold, every denomination's balance sum is unchanged, and its floor sum unless a Turn of the log bore its well. |
| B2 | `Integrity.grantCap` (`Spec/Proofs/Cap.lean`) | `top_integrity_grantCap` | along an audited log, the transfers (credit lines) sent through a live grant sum to at most what its transfer (credit) ledger had left. |
| B3 | `Integrity.law` (`Spec/Proofs/Claims.lean`) | `top_integrity_law` (`Spec/Proofs/Deployed.lean`) | along an audited log, an object's package never changes while it lives, and every history of it under a `NoRef` law is a chain the law's reference meaning admits. |
| A2 | `OneHistory.pair` (`Spec/Proofs/Claims.lean`) | `top_oneHistory_pair` (`Spec/Proofs/Deployed.lean`) | two folds from one World with equal step counts and chains reach one World, up to a collision among their link inputs. |

Each claim has a floor refuting a lazy system: `floor_integrity_authority` (`Spec/Proofs/Auth.lean`), `floor_integrity_value` and `floor_integrity_law` (`Spec/Proofs/Floor.lean`), `floor_integrity_grantCap` (`Spec/Proofs/Cap.lean`).
`Spec/README.md` lists their premises.
