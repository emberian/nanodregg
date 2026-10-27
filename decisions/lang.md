# decisions/lang.md — LANG (BUILD-LANG)

LANG-0..7 and LANG-L are in the frozen DECISIONS.md (ruled by ROOT 2026-10-16: (1) one language,
append-only upgrade ACCEPTED with a named law verdict; (2) install the checked core ACCEPTED, the
source hash a claim; (3) the CEK machine ACCEPTED for v0 with the exponential plant; (4) no perform in
v0 ACCEPTED, grants are KERNEL receivers). New entries go here.

## LANG-8 A law returns a verdict, not a Bool (2026-10-16)
**Decision.** A law has type `State → State → Req → Verdict`, `Verdict = sum {ok : {}, refused :
bytes}`. `refused r` becomes KERNEL's `Refusal.lawDenied law (label ++ ": " ++ r)` (r as UTF-8, else
hex); running out of budget is `lawDenied law (label ++ ": exhausted")`; any other fault is
`program`. **Alternatives.** Bool with the law's label as the only name (LANG-4); the machine's trace
naming the failing node. **Why.** Law 7: the author names the clause, in the author's words; a trace
node index means nothing to a reader. **Critique.** The reason is author-chosen text, so a law can
lie about why it refused or leak state into the refusal (refusals are public). A law that returns
`refused` with a 64 KiB reason bloats every refusal frame; the reason is cut to 256 bytes.
**Meta-critique.** A sum where a Bool would do is more for the author to write; ROOT asked for it,
and I would not have.

## LANG-9 Package identity is KERNEL's `romIdOf` of the package cell (2026-10-16; answers KERNEL-3)
**Decision.** Confirmed: no LANG digest. A package's id is `romIdOf (cell kind=package, rom,
slots [(0, package bytes)])`. Because the package bytes contain the import ids, the id commits to the
whole closure (Merkle), which is all LANG-5 asked for. **Alternatives.** LANG-5's
`H("nanodregg/lang/package/v1" ‖ bytes)`. **Why.** Law 1: one identity for a ROM thing; a second
digest of the same bytes would be a twin. **Critique.** The id depends on the kernel's cell encoding
(kind, discipline, slot framing): a change there moves every package id (a re-genesis, which is
free) and an author cannot compute their package's id from the package bytes alone without the
kernel's cell codec. **Meta-critique.** Accepting it is the low-friction answer to the layer above me.

## LANG-10 The stack bound is a consensus constant, not part of a budget (2026-10-16)
**Decision.** `Bounds.stackMax = 4096`; `eval` takes ticks only. **Why.** The vacuity review showed
two runs with different stack caps both end `Final` with different outcomes (a value, a `stack`
fault), so "executors agree whatever budgets" was false with a per-call stack cap. With the cap
fixed, `run_agree` says what re-execution needs. **Critique.** A program that needs 4097 frames can
never run, whatever it pays; 4096 frames bounds the deepest non-tail recursion at ~2000 calls.
**Meta-critique.** I fixed a theorem's premise by removing a knob, which is the cheap direction;
stack monotonicity (a value under cap c is the same value under c' ≥ c) is true and would have kept
the knob.

## LANG-11 The object's state is a record type; field i lives at slot `stateBase + i` (2026-10-16)
**Decision.** A package declares `state : Ty` (a record of data types, canonical order). KERNEL's
`Slots` at `stateBase + i` hold `Wire.encodeData Tᵢ vᵢ` for the i-th field. A law package also
declares a state type: an extra law judges an object's slots decoded at the LAW's state type, and a
slot that does not decode is `lawDenied law "state"`. So a law over a data object (no package)
reads the slots it declares and nothing else. **Critique.** The layout is positional: adding a field
in the middle of a state type renumbers every later slot, so a new state type is a new object (no
migration, which is the v0 position anyway). Two laws on one data object may disagree about the type
of one slot; each decodes its own view, so neither can be confused, but the object has no single
type. **Meta-critique.** KERNEL's data objects forced the "law reads at its own type" rule; I would
have given every object a package.

## LANG-12 Methods are indexed; their shape is fixed (2026-10-16)
**Decision.** A package lists `methods : List Label` (KERNEL's `method : Nat` indexes it) and
`laws : List Label`, fields of its interface record. A method has type
`State → Args → Req → State` (`Args` any data type, decoded from the call's `args` bytes);
`Req = {agent : bytes, principal : bytes}` (the members' digest bytes). Install refuses a method or
law of the wrong shape. **Critique.** No result value: an invoke can change state but cannot answer
the caller (KERNEL's `run` returns only `Slots`); a read is an observe, not a method. No height or
time in `Req`, so no law can say "not before height h". **Meta-critique.** Shaped by KERNEL's
`Program.run` signature, which I did not write.

## LANG-13 The v1 fork: cross-object calls (2026-10-16, open)
ROOT ruled that grants/delegation are KERNEL receivers and v0 needs no call. The fork for v1:
(a) **in-language synchronous calls** (`perform call obj method args` answered in the same turn,
call tree to a depth bound, re-entry refused — minidregg's ObjectiveCall). Critique: brings back
`perform` and continuation typing; a call tree's writes to several objects must be judged by every
object's laws in one turn; DAO-style re-entry must be refused by a theorem. (b) **messages as turns**
(a method's result names messages; each is a later turn of its own, paid by the sender). Critique:
no atomic multi-object update, which the powerbox's `exercise` (check grant, then call target) needs;
the grant receiver then has to be the atomic part, which is what ROOT ruled. Meta-critique: (b) is
what the v0 code already is, so I am biased toward it.

## LANG-14 LANG owns the recursive codec until CODEC has a recursive combinator (2026-10-16)
**Decision.** `Lang/Wire.lean` encodes `Ty`, `Term`, `Data` and the package with CODEC's primitives
(u8/u32/u64 via `Codec.Stream`), depth-bounded readers, type-directed data. **Critique.** It is a
second codec SHAPE outside `Stream` (it has no `Shape`, so no derived tag), which law 1 calls a
defect; it exists because `Stream`/`Shape` cannot express a recursive type. The fix is CODEC's: a
`Shape.rec`/fixpoint combinator; proposals/lang.md asks. **Meta-critique.** Writing it myself was
faster than waiting, which is how twins start.
Status: CLOSED by LANG-17 (the hand readers are deleted).

## LANG-15 No Mathlib (2026-10-16; GATES-1 not challenged)
The language's metatheory (typing, CEK soundness, budget theorems) needed only core `omega`/`simp`
and structural recursion over nested inductives. Nothing pulls for Mathlib.

## LANG-16 Loading a closure re-checks every package in it (2026-10-16; amends LANG-5)
**Decision.** `Lang.load` runs `Package.checkWith` on each package of the closure against its
imports' interfaces as loaded, before appending it. **Why.** LANG-5 said invoke re-checks nothing
because install checked and the cell is ROM; that makes `run`'s soundness a WORLD invariant ("every
package cell was born by install, which checked") that no theorem states. Re-checking makes it local:
`load`'s closure satisfies `LibTy` by construction (Lang.Proofs.Relocate: relocation preserves
typing), so `checked_never_stuck` applies to the deployed path. **Critique.** O(closure size) checker
work on every invoke and every law judged; delvetalk measured re-check at ~1/5 of an entry's compile.
The fix when measured is a Host memo keyed by package id (ROM: the id determines the bytes), not
dropping the check. **Meta-critique.** I chose the check whose theorem is local over the cheaper one
whose theorem is global — the bias toward what I can prove this session.

## LANG-17 The port onto `Codec.Tree`: terms on the tree, data on the combinators (2026-10-16; closes LANG-14, answers CODEC-9)
**Decision.** (1) A type, a term and a package are each one `Codec.Tree` (`Lang/Wire.lean`,
`Lang/Package.lean`): one node per constructor, scalars as a payload written by CODEC's ordinary
codecs, subterms as children, a row entry as a field node (label payload, one child). The decoder is
`Stream.tree nodeMax depthMax` then `packageOf`; the encoder is `Option`-valued: `encodePackage p` is
`none` unless `packageWire p` (labels ≤ 64 bytes UTF-8, rows ≤ 256, indices < 2^32, literal naturals
< 2^64, import ids ≤ 32 bytes) and the tree fits. (2) DATA does not go on the tree: `dataStream T` is
built from `u64`/`bool`/`bytesOf`/`product`/`sum` by recursion on the TYPE (`Lang/Wire/Data.lean`),
over a type family `DataAt T`, so data's `Shape` is the type's structure and its canonicity is the
combinators' (no Lang inverse proof at the byte level). Only a canonical (`wf`) type has a data codec.
(3) Theorems: `decodePackage_eq_ok_iff` and `decodeData_eq_ok_iff` (`decode b = ok v ↔ encode v =
some b`), `decodeData_conforms` (re-proved), teeth in `Proofs/WireTeeth`.
**Alternatives.** CODEC-9's literal recipe, `Stream.refine "lang/term" tree ofTree toTree` with
`β = Term`: impossible, since `toTree` is not total into `Tree.Fitting` (an unbounded label or a
2^64 literal has no fitting tree), so `β` would be a subtype of representable terms carried through
every `Package` field. Data on the tree too (self-describing): 9 bytes of node framing per value (a
`nat` slot 8 → 17 bytes) for a reader that already knows the type. A re-encode-and-compare decoder
(decode, then check `tree (decode t) = t`): canonical by construction but a second pass on every
load. **Why.** The tree is the one recursive codec (law 1); data needs no recursion over the input
(the type is finite), so a combinator stream is the smaller and better-typed answer; an `Option`
encoder names the representable values once (`*Wire`) instead of threading a subtype. **Critique.**
(Superseded 10-17, ROOT relaying CODEC-13: data sums are CODEC's `choice`, one tag byte for up to
256 arms, so a data type needs `tyWire` as well as `wf` (`dataTy`); the unary nested-sum index this
entry first shipped is gone: a second flag day for state bytes.) `packageOf` refuses with one name
(`rejected 0 "lang/package"`): a resident does not learn WHICH node is wrong (their `encodePackage`
is `none` first, equally nameless). `depthMax = 1024` now counts tree levels, and a record field is
two (field node + type), so a type of nested records reaches the bound at ~512 records deep; the old
1024 counted constructors. The tree's one bound `nodeMax = 65536` caps both a payload and a child
list, so the READER accepts a 65536-byte label or 65536 children before `labelOf`/`rowMax` refuse
them after the node is read (bounded by the input, but looser than the old length-prefix refusal).
The framing was 9 bytes per node (Owned 2529 bytes vs ~1181 on the old wire); CODEC-13 (3135d3d)
moved the tree to varint framing: Owned is 1227 bytes. **Meta-critique.** I chose
the combinator data codec because it made the proof nearly free, and only then argued its wire
size; the unary sum is the price of using `Stream.sum` rather than adding an n-ary tagged sum to
CODEC, which I did not ask for.
**Flag day.** Package bytes (hence every package id, `romIdOf` of the bytes) and every data slot's
bytes change: an installed package or object state from before this commit refuses to load
(`malformedCell` at its package slot; state fields as `decode …` refusals). Re-genesis.

## LANG-18 A reference semantics beside the machine; `extend` keeps the old self (2026-10-17)
**Decision.** `Lang/Proofs/BigStep.lean` defines what a term MEANS as a big-step relation
(`BigStep`/`Sel`/`Ext`, results `Except Fault Val`), and the machine is proved to compute exactly it:
`run_bigStep`/`run_fault_bigStep` (machine result ⇒ meaning, any budget) and
`bigStep_run`/`bigStep_run_fault` (meaning ⇒ the machine reaches it under every large enough stack
bound and tick budget), with `bigStep_deterministic`. `stuck` is never a meaning. Ticks and the stack
bound are resources, not meanings: a meaning may need more than `Bounds.stackMax`, and then the
deployed run ends `.stack`. The language decision this exposed: `extend (fix f) fs` unrolls the knot
once and merges, so inherited fields keep the OLD self (`bigStep_extend_keeps_old_self`): no late
binding of self through `extend`; open recursion is `fix` over a mixin the authoring tool writes
(LANG-1's `mix`), not `extend` of a knot.
**Alternatives.** A denotational interpreter (a second evaluator: ruled out by "one language, one
evaluator"); a relation only, with no completeness (then any non-overlapping added rule is invisible:
the reviewer's appNat example). **Why.** A relation in a Proofs module runs nowhere, so it is a spec,
not a twin; the two directions make it the machine's graph exactly, and its rules can be read.
**Critique.** It shares the value domain with the machine (`Val`, `suspend`, `primEval`, `Row`), so a
bug there is inherited, not caught; call-by-value order in ill-typed corners (an applied natural
whose argument faults "means" the argument's fault) was read off `step`. The old-self `extend` may be
the wrong language choice for mixins; it is now a named, toothed decision rather than an accident.
**Meta-critique.** The rules were written by reading `step`; their independence is of control only.
A truly independent reference would define `primEval`'s arithmetic on `Nat`/`ByteArray` directly.

## LANG-19 The judge is told what it judges: `Req.occasion` (2026-10-16; ID-1, with KERNEL-4)
**Decision.** KERNEL's `Req` carries `occasion : Occasion D` (`birth | write | relaw (laws : List D)
| invoke (method : Nat)`), and each receiver passes its own: `create` birth, `write` write, `law`
relaw with the NEW law ids, `invoke` its method. LANG's `reqTy` gains `occasion : occasionTy`,
`occasionTy = sum {birth : {}, invoke : nat, relaw : bytes, write : {}}`; a relaw's ids are their
digest bytes concatenated in order (`occasionData`), and `reqOk` asserts they fit one byte value.
The ids are fixed-width digests, so the concatenation is unambiguous. A law that cases on the
occasion must give every arm (the checker requires exactly one arm per label, in the sum's order),
so the case form has no default. Rows (lang-journey): L8b a seed carrying approvals is refused at
birth (`fresh: seeded`); L8e the invoke's method index reaches the law (method `b` closed, `a`
open); L9d an extra law refuses its own replacement (`frozen: laws are frozen`); L10 a law admits
a replacement by exactly the agreed ids (`[Tally]` refused, `[Frozen]` admitted). Plants: the judge
told every act is a write (the judge before this entry) admits L8b, L8e, L9d and L10c; the judge
that loses the payload (a relaw names no laws, every invoke is method 0) admits L8e and refuses
L10d. **Alternatives.** (a) A package `init` constructor `create` runs, so a seed is
computed, never supplied: closes only a programmed object's birth; data objects and relaw stay
open. (b) `Req.birth : Bool`: misses relaw. (c) `old : Option S`: changes `lawTy`, misses relaw.
(d) The assembly's `relaw` with no payload. **Why.** One field closes all three `old = new` sites.
Against (d): with no payload a law can refuse its replacement or allow it under a state condition,
but cannot bind consent to WHAT replaces it, so a quorum's approvals for one proposal would license
deleting the quorum (the unbound-approval bug LANG-20's proposal field fixes for commits, moved to
the law slots). With the ids a law can require an exact replacement or bind approvals to it.
**Critique.** It fails open by omission: a hand-written law that ignores `occasion` keeps both
holes, and install cannot tell (only the stdlib's `lawOf`, LANG-20, makes the clauses unavoidable).
The relaw payload is bytes, not a list: the language has no list type, so a law can compare the
whole replacement for equality but cannot ask "is my id among them" (a package cannot contain its
own id anyway). KERNEL-6 judges a law change by the OLD laws only, so a newly adopted law never
judges the state it is adopted over (adding `total ≤ 100` to an object at 500 is admitted); that
is KERNEL's, named here. Every law term grows by one `case`. **Meta-critique.** I took the shape
with fewest mechanisms and the one I could run today; the constructor (a) is what a Hermes author
would expect and has a real property (a package's methods may rely on invariants no law states,
which only a constructor establishes) that this loses. Nobody has asked an author.
**Flag day.** `reqTy` changes, so `lawTy` and `methodTy`, so the interface, bytes and id
(`romIdOf`) of every package with a law or a method (a pure library package that never mentions
`reqTy` keeps its id). Such a package from before refuses to load: `load` re-checks it, and
`checkFields` refuses `badLaw`/`badMethod` against the new `reqTy` (`program` on the wire).
Re-genesis. Re-emitted:
`Journey.ownedText` (now printed from `reqTy` by `Read.showTy`, never restated), PROTOCOL's
`Protocol/Rows.lean` `reqTy` string (cross-layer; PROTOCOL asked to print it from `Lang.reqTy`).

## LANG-20 The law library: generated core terms, each with a meaning theorem over `BigStep` (2026-10-16; ID-2, ID-3)
**Decision.** `Lang/Std.lean` holds Lean GENERATORS that emit closed terms of type `lawTy S`;
nothing in it runs at admission. Every law is `lawOf S birth relaw change` (`λ old new req. case
req.occasion` with an arm for every act, LANG-19): there is no default arm, so each law states
what it does at a birth and at a relaw (`lawOf4` gives writes and invokes separate clauses).
Clauses are written against `At` (how many binders sit below the law's three arguments), so a
clause may open a `case` of its own and still name `old`, `new`, `req`. AUTHORITY IS THE KERNEL'S
once KERNEL-25 lands (ruled 10-17, NOT YET BUILT: invoke owner-gated like write, so every admitted
act's `principal` is the object's owner or a chain rooted at it, and a stranger never reaches a
law; today a write or relaw already is, an invoke is not); a law only NARROWS it. Laws: `ownerSigns` (the signer is the principal: no delegate acts through a grant);
`allowlist` (the signer is listed, every occasion); `bounded` (a natural
field ≤ max in every state, the seed included); `quorum S T members k guarded` with state
`{approvals : nat (a mask over the members), proposal : sum {laws : bytes, set : T}}` where a
change is exactly one of commit (the guarded field becomes the proposed value, ≥ k approvals,
approvals reset), propose (proposal changes, approvals reset), approve (the signer adds its own
unset bit) or a no-op, a birth has no approvals, and a relaw needs ≥ k approvals of exactly the
incoming laws; `windowed S T W limit guarded` (the signed window lies in one epoch `notBefore / W`,
the state's `epoch` is it, `count` rises by one per change of `guarded` up to `limit`, a later
epoch restarts it; no clock holder, the probe's H3); `machine S f states initial edges` (a
finite-state field moved only by methods along named edges `(from, method label, to)`; writes and
relaws refused) with its method `stepTo` (for HOSTING's grain lifecycle). `pkgOf S laws methods`.
ID-3's required `Authority` (with `anyone` and `ownerActs`) is DELETED: under KERNEL-25 `ownerActs`
re-checks the kernel's gate against a copy of the owner in state (a twin), and `anyone` is false
(the kernel refuses strangers; a public object will be the owner issuing a World-grantee grant,
KERNEL-4's proposal, unruled). The one law runner is `Lang.Law.runLaw` (the
receiver's `judgeOne` and every test call it). `Lang/Proofs/Std.lean` proves, over `BigStep` and
compositionally from inversion lemmas of the combinators (`guard_ok`, `allOf_ok`, `anyOf_true`,
`lawCase_arm`, `sameProposal_bool`, `popcount_field`), never by evaluating a generated term:
`bounded_spec`, `ownerSigns_spec`, `allowlist_spec`, `machine_birth`, `machine_invoke`,
`machine_write_refused`, `machine_relaw_refused`,
`quorum_birth_empty`, `quorum_relaw_needs_k`, `quorum_change` (the four-way classification) and its
corollary `quorum_change_needs_k`, `windowed_lands_in_epoch`, `windowed_counts`. Each is stated
over `Admits lib t rq n o` (the law's body means `ok` with the request, new and old states bound),
which `runLaw_admits` (a closed term, as a test runs it) and `runLaw_ref_admits` (a package field,
as the receiver runs it) produce from an admitting `runLaw`. The generators that take parameters
are CHECKED (`quorum`, `windowed`, `machine`, `stepTo` return `Except StdRefusal Term`): duplicate
members (one member, two votes), a threshold outside `1 ≤ k ≤ members`, more than 63 members, an
epoch of width 0, duplicate or unknown states, an unknown method label are refused by name; the
theorems are about the unchecked terms (`quorumLaw`, …), and `quorum_ok`/`windowed_ok` say what
acceptance guarantees. The check protects an author who uses the checked generator: the
unchecked `*Law` terms are public (the theorems are about them), and install cannot tell a
generated term from a hand-written one, so `pkgOf S [("q", quorumLaw S T [a, a, b] 2 g)] []`
installs. Machine edges name methods by LABEL and are resolved to indices in
`pkgOf`'s sorted order (`methodIndex`), so an edge cannot silently name the wrong method. Teeth
(`Proofs/StdTeeth`, kernel-evaluated instances of `runLaw` on the CHECKED generators' output, and
the checked generators' refusals): each law admits a legitimate act (the premises are satisfiable) and each clause refuses the act with
that one thing wrong, by its reason.
**Alternatives.** (a) Parameters in STATE: one installed `std/quorum` reused by every object.
(b) Laws as text a resident copies. (c) The combinators as test helpers outside `Lang/`. (d) A
`proposal` of the guarded type only (the assembly's sketch). **Why.** (a) does not compose: LANG-11
lays state out positionally, so two separately installed law packages on one data object read slot
`stateBase + i` at their own types (quorum's 16 is `approvals`, windowed's is `count`); author-time
composition into one package has no such conflict. (b) has no parameters (the core is monomorphic).
(c) leaves residents nothing to use and the theorems nothing to be about. Against (d): approvals
bound only to a value of the guarded field still authorise the law's own replacement, which is the
same unbound-approval bug moved to the law slots (LANG-19's argument for a relaw payload).
**Critique.** `ownerSigns` means "only the owner's own key" ONLY with KERNEL-25 built; on a
kernel where invoke is open, `agent = principal` admits any member invoking without a grant. Every
object type is its own install (2–3 KB of ROM each), and changing a member
set is a new package and a new object. The spec theorems are per-STEP: "k distinct members
approved the committed value" is their induction over a history (with `quorum_ok`'s distinct
members), which no theorem here states (and the history is KERNEL's); likewise "at most `limit`
changes per epoch" for `windowed`. Any member may propose, which resets every approval: one member
can stall a quorum forever (liveness, not safety). The chain from the receiver to these theorems
is not closed: `judgeOne` admitting ⇒ `runLaw` admitting each law, `L.lib[g]` = the relocated
body, relocation of a ref-free term is the identity, and a `pkgOf` body's field is the generator's
term are each still to prove; until then "the receiver's run means this" is a hypothesis. (CLOSED for an
import-free `pkgOf` package by LANG-26, `Lang.Proofs.Receiver`; a package with imports is still open.) A hand-written law that ignores the occasion keeps H1/H2; only
`lawOf` makes the clauses unavoidable, and install cannot tell a stdlib term from a hand-written
one. The relaw payload is the ids' bytes, so `quorum` binds to an exact replacement but cannot say
"any list containing me". `quorum` supports ≤ 63 members (a mask bit is a natural below 2^64). `windowed`'s epoch is the signer's window, which the signer picks: a
signer can choose a LATER epoch than the current one only by signing a window the World has not
reached, which admission refuses (`outsideWindow`), so it cannot pre-spend future epochs; but the
law trusts `World.admit`'s window check, a fact about KERNEL it does not state. `eqAt T` compares at
`nat` unless `T = bytes`; any other guarded type fails install as ill-typed.
**Meta-critique.** I chose per-instance generation partly because it let me skip bytes primitives
(ID-4), which is the "phase ordering that avoids a hard part" smell; the composition argument is
derived, not run. The proof shape (inversion over `BigStep`, with data-level views of the
environment) was the one I could make go quickly; it shares `Val`/`primEval` with the machine
(LANG-18's named gap), so a bug in `primEval` would be inherited by every spec.
**Amended (FAERIE-DOCS 2026-10-27).** KERNEL-25 is BUILT (be98647): an invoke is owner-gated like a write, so "NOT YET BUILT" and "an invoke is not" above no longer hold.

## LANG-21 Cross-object calls: effects as data, restated over touches; built with LEDGER's first method-triggered receiver (2026-10-17; ID-9, closes the LANG-13 fork as a design)
**Decision.** LANG-13's fork is decided for (a)'s atomicity without (a)'s `perform`: a method
returns its new state AND a list of calls as DATA, `methodTy S A := fn S (fn A (fn reqTy (rec
{calls : <effect list>, state : S})))`; KERNEL's `run` returns `Slots × List (Effect D)` with
`Effect := {target, method, args, budget, via}`; the invoke receiver visits the call tree depth
first, running each object ONCE on its pre-Turn state (so nothing reads an intermediate state),
refusing re-entry by name (`reentry obj`), bounded by `callDepthMax = 4`, `callsMax = 8` and a
consensus `treeTicksMax`; every visited object's laws judge its own `old → new` with occasion
`invoke m`; `sealTurn` takes the visited objects' effects (it already takes a list since
KERNEL's `duplicateEffect` change), and `visit_distinct` (each object once) makes
`duplicateEffect` unreachable. A callee's `Req.principal` is the CALLING OBJECT (object-as-grantee:
a grant may name an object), `agent` stays the signer. `Body.invokeAll` (a client-composed batch
of independent invokes) is REJECTED: one signer's batch carries no authority its single invokes
lack (each is gated by the kernel on its own, KERNEL-25), and no object's law sees the others, so a bounty's `approve` cannot
check that the funds moved; with effects as data, `approve` itself emits the transfer, so the
package guarantees approve ⇒ transfer. **Build trigger:** LEDGER's first receiver that a method
must trigger (pay/well/bounty, PROTOCOL-15); a `calls` field nothing consumes would be a no-op
shape. Tracked as a `cv task`. **Alternatives.** (a) synchronous `perform call` with continuation
typing; (b) messages as later turns; (c) `invokeAll`. **Why.** (b) has no atomic multi-object
update; (a) brings back `perform` and continuation typing for no expressiveness effects-as-data
lacks (no answer flows back in either v1 shape). **Critique.** Confused deputy: a callee's laws see
the calling object, not the signer's authority, so `Req` may need `origin`; no answer flows back
to the caller; no law spans the objects changed together; the client must pin the whole tree.
**Meta-critique.** "Build it with LEDGER" is a phase ordering (R7): if LEDGER decides value moves
only by client-signed ledger calls, this is never built and LANG-13 stays open. The guard is this
entry, written with a decided shape, and LEDGER's design answering it by name.

## LANG-22 The resident readers: a seed and a method's arguments read as TEXT at the package's types; `#HEX` bytes (2026-10-17; written by PROTOCOL-5 for LANG-3, agreed)
**Decision.** `Program.resolveMethod p method` is the ONE method resolution (index → label →
iface field → `methodArg`); `runMeasured` calls it. `seedOf look pkg TEXT` reads TEXT at the
package's state type and writes the state slots (`stateSlots`; no bytes is refused by name, never
an empty seed); `argsOf look pkg method TEXT` reads TEXT at the method's argument type and encodes
it. A reader refusal is `program` with its `name @offset` text. `Read.scalarAt` reads `#HEX` (an
even count of lowercase hex digits) at type `bytes` only, which is what `ob`'s `showData` prints for
bytes that are not quote-free UTF-8, so `ob`'s output now reads back. Theorems
(Lang/Proofs/Invoke.lean): `argsOf_decodes` (the bytes decode, at the type `resolveMethod` gives,
to the data the text read to: the run decodes a planned call's arguments), `seedOf_reads` (the slots
read back through `readState` to the data the text read to), with `readState_go_stateSlots` and
`readData_record`; `scalarAt_conforms` extended. Journey L0b: an owner written as a member id
(ob's printing), and three refusals (odd hex, uppercase hex, hex at a nat).
**Alternatives.** The readers in Protocol (method resolution restated a second time: a twin);
args as raw hex of the wire bytes (the member signs bytes it cannot read); a `(hex …)` form (a
second spelling of a scalar where an atom suffices).
**Critique.** `argsOf_decodes` is about `readPackage`'s package, while the run resolves the method
on `load`'s copy of it (the closure's relocated package); they agree on methods, iface and state
because load relocates only bodies, but that is not a theorem here. Reading at plan time and
running at admission are two reads of the package; a package cell is ROM, so they cannot disagree.
**Meta-critique.** I wrote this from PROTOCOL's side because the verbs needed it; the shape of
`seedOf` (slots, not data) is what `Body.create` takes, which a LANG owner might have cut at data.
**Status.** landed; LANG's successor reviews.

## LANG-23 Effects are `Body` calls in a fixed-arity row; the forwarding check is withdrawn (2026-10-17; LANG-4's answer to LEDGER-5, amends LANG-21 and LANG-3's answer recorded in decisions/kernel.md 1b4135c)
**Decision.** LEDGER-5 is accepted with changes. An effect is a `Kernel.Receive.Body D` of a
callable kind (`invoke`, `transfer`, `account`, `credit`, `grant`); LANG-21's `Effect` record is
deleted, never kept beside `Body` (law 1). The core has no list or recursive type, so a method
returns `rec {calls : callsTy, state : S}` with
`callsTy = rec {c0 … c7 : optTy callTy}` (arity `Kernel.Bounds.callsMax`, KERNEL's, because Kernel
cannot import Lang), `optTy T = sum {none : rec {}, some : T}`, and `callTy` one arm per callable
kind, its fields the Body constructor's (digests as `bytes`, `Option` as `optTy`, a grant's
`List Right` as the fixed-arity `rightsTy = rec {r0 … r3 : optTy rightTy}`,
`rightTy = sum {enroll : nat, invoke : nat, mutate : rec {}, observe : rec {}}`).
`methodTy S A := fn S (fn A (fn reqTy (rec {calls : callsTy, state : S})))`; `reqTy` is unchanged
(agent = the signer, principal = the calling object, LEDGER-5 (b)). `Lang/Call.lean`: `callData`
(an exhaustive match on `Body`: a new constructor does not build until it is classified callable
or not), `bodyOf`, `callsOf` (slots in label order, `none` skipped, a non-digest refused
`program "calls: cI FIELD: not a digest"`); `Lang/Proofs/Call.lean`: `callsOf_callable`,
`callsOf_length`, the round trip `bodyOf_callData` / `callData_bodyOf`, teeth per arm.
`Program.run`/`runMethod` return `Slots × List (Body D)`, `runMeasured` adds the counts;
`Std.methodOf` emits every slot `none`, `Std.methodWith` takes calls. KERNEL keeps
`notCallable` as its own assertion where the program's calls enter (law 4: `Program` is abstract to
it); for `Lang.program` it is unreachable by `callsOf_callable`. `visit_distinct` is KERNEL's (the
visitor is in Derive). Order: KERNEL-5's run signature, `callsMax`, `notCallable`, Draft; then this
as one `lang!` flag day (every package with a method re-ids; HOSTING re-emits `world/grain`); then
LEDGER's escrow.
**Withdrawn: `forwardsCalls`** (LANG-3's install refusal of a method whose argument type contains
`callTy`). It refuses the legitimate smart-account shape: a quorum-governed object whose state
holds a proposed call and whose commit emits it (an object-owned treasury) needs `propose(call)`.
And it was incomplete by its author's statement: fields assembled from arguments are the same
power. A structural check that is known incomplete is one the next reader trusts. The guard is the
kernel's: KERNEL-25's owner-gated invoke, grants naming which method, and principal = the calling
object spending only that object's authority; a callee's law still sees `agent` = the signer.
ROOT APPROVED the withdrawal (2026-10-17) on condition that the guard is a THEOREM: KERNEL-5 owes
`effect_as_signed` with LEDGER-5 (b) (an emitted call derives exactly as the calling object signing
it over the same pinned view; plant: the emission under the invoker's principal goes red), beside
`invoke_stranger_noGrant`. That theorem is what replaced the check.
**Not taken from LANG-3's answer:** "callTy is GENERATED from KERNEL's Body codec shape". No
generator from a `Codec.Kernel` stream to a `Lang.Ty` exists, and the meaning is `Body`, not its
bytes. The round trip is stated against `Body`.
**Escrow gaps sent to LEDGER** (LEDGER-5 (e)): (i) under (b) `deposit` cannot debit the
depositor's account (the object does not own it). The depositor must grant the escrow OBJECT
`mutate` on it, and `deposit` emits the transfer through that grant. Otherwise an unfunded deposit
reaches `held`, and both release and refund are `belowFloor`: the escrow wedges. (ii) a method reads
no other cell and account ids are born in the Draft, so the escrow cannot check its own account id.
An argument-supplied `acct` lets a depositor name an account of its own. An account id determined
by (owner, asset) would make the binding derivable. (iii) a nested invoke's `args` are bytes. Until
ID-4's bytes primitives, a method forwards only bytes it already holds. **(iii) is CLOSED by LANG-77 (2026-10-23):
the invoke arm is typed and the runtime encodes the value the method returned.**
**Alternatives.** (1) A list type in the core (recursive types): a new Ty constructor and fold
semantics, which the demand machine's budget theorems would have to reach, to carry at most 8
items. (2) `calls : bytes` of the kernel's Body codec: the method could not build a call without
bytes primitives, and the checker would see nothing. (3) Keep `forwardsCalls` as "a second line":
see above.
**Critique.** A fixed arity of 8 is a consensus constant baked into every method's type: raising
it re-ids every package. A method that emits fewer calls still carries eight `none` slots in its
term (author-time cost only; no bytes on the wire, since calls are not stored). With
`forwardsCalls` gone, a package author who writes `exec(call)` behind a grant to strangers lends the
object's whole authority, and nothing in LANG says so. `mutate` on an account is the whole balance,
so the escrow-funding grant is wider than `amount`. `rightsMax = 4` assumes Right keeps four
constructors. `callData` is exhaustive, so a new Right breaks the build, which is the intent.
**Meta-critique.** Withdrawing the check also removes work from my layer, which is the
"phase ordering that avoids a hard part" smell in reverse. The independent test is the treasury
example, which the check refuses. I accepted `Body` as the effect type partly because LANG-3 had
already agreed, so I am not the right judge of whether a narrower posting type would have been
safer for value.
**Status.** agreed with LEDGER (sent 2026-10-17); built in the post-D5 `lang!` day with LANG-33's amendment: the fixed eight-slot row is replaced by declared slots.

## LANG-24 The fifth occasion: `adopt laws'` — every Std law states what it does when it is ADDED over existing state (2026-10-17; with KERNEL-5's KERNEL-27, ROOT ruled `.adopt`)
**Decision.** `occasionTy` gains `adopt : bytes`: the incoming laws' ids, encoded as `relaw`'s
are. `law` on a data object first runs the laws in force on `relaw laws'`. Then each INCOMING law
judges the unchanged state on `adopt laws'`. The payload is LANG's ask, agreed by KERNEL-5: ROOT's
"quorum's adopt arm = its relaw arm" needs the incoming set, and an incoming law does not know the
rest of the list it arrives with. `Std.lawCase5`/`lawOf5` replace `lawCase4`/`lawOf4`, and
`lawOf S birth adopt relaw change` takes the adopt clause explicitly (no default arm). The arms:
`ownerSigns`/`allowlist` = their one clause; `bounded` = its clause (the bound holds in the state it
is added over); `quorum` = its relaw clause (a member, `k` approvals of exactly the incoming
laws in the state it is added over); `windowed` = its birth clause (the call's epoch, count 0);
`machine` = its birth clause (the field at `initial`). Theorems: `lawCase_adopt`,
`quorum_adopt_needs_k`, `machine_adopt`, `bounded_spec` and `windowed_lands_in_epoch` extended to
adopt. Teeth (StdTeeth): quorum_adopts / _needs_two / _only_the_proposal / _members_only,
windowed_adopts / _adopt_stale_epoch / _adopt_spent_count, bounded_adopt(s),
allowlist_adopt_refuses, machine_adopts / _adopt_initial. Journey L11: `BirthOnly` (adopt refused)
may be born under (L11b) but not added later (L11c); plant erase-occasion admits L11c.
**Alternatives.** KERNEL-27 as first built: adoption judged as `.birth`. It cannot say "only at
birth", and it makes a quorum adoptable with no consent. `adopt` with no payload: quorum's arm does
not typecheck. Windowed adopt = ok: an adopted window with a stale epoch refuses every later change
forever (same-epoch needs the call's epoch, a later one needs an unreachable window).
**Critique.** A quorum added over a state must find `proposal = laws L` with `k` approvals already in
that state, so a data object that did not run the quorum's fields cannot adopt it (it fails at the
state type). That is the point (the members consent in state), but it means a quorum is in practice
born, not adopted. Windowed's adopt is stricter than needed (count 0, not count ≤ limit). Every
package with a law re-ids.
**Meta-critique.** I picked each adopt arm by "the clause that asks the same question of a state",
which is the birth clause for every state-predicate law. That is the conflation KERNEL-27 first
made, now per law and visible, rather than a different idea.
**Status.** built (a533d7a), then AMENDED the same day (below).
**Amendment (LANG-4, 2026-10-17, after the vacuity read by a773ed76).** "quorum's adopt arm = its relaw
arm" was UNSOUND. At adoption the quorum is not in force yet, so the `approvals` and `proposal` it reads
were written under the previous laws: the owner writes every approval bit and `proposal = laws L`,
then adopts L, and the k-check passes with no member's consent. `quorum_adopt_needs_k` was true and
its gloss false; the tooth `quorum_adopts` tested exactly the forgeable state. Now quorum adopt =
its birth clause (`approvals = 0`; theorem `quorum_adopt_fresh`; teeth `quorum_adopts` on a fresh
state, `quorum_adopt_forged_approvals` refused). A relaw that KEEPS the quorum would then refuse
(its state holds k approvals at that moment), so KERNEL-27's second judge runs on the ADDED laws only
(`laws'.filter (· ∉ laws)`, agreed by KERNEL-5): a kept law already judged the change as
`relaw laws'`. Journey L11d: keep BirthOnly and add Frozen, admitted. Also `windowed_fresh` (birth or
adopt ⇒ count = 0, the per-epoch bound's base case) and positive adopt teeth for allowlist and
ownerSigns. This departs from ROOT's 10-17 wording for quorum. ROOT accepted it (907b55d) and records that its ruling
was the error: approvals written under the previous laws are the previous owner's word, not member
consent, so "adopt = relaw arm" was forgeable by construction. The consent to an adoption is the OLD
laws' `relaw` judgement, which is where it belongs; the incoming quorum's adopt only requires a fresh
state.
Meta-critique of the first arm: I took a ruling's wording as a specification, without asking
whose writes the arm reads.

## LANG-25 An object names accounts by reference, not by hashing: `Req.self` yes, an `accountOf` builtin no (2026-10-17; answers LEDGER-6 (b), PROPOSED to LEDGER-2 for D5)
**Decision.** `Req.self : D` (the object judged or run on, set by KERNEL where it builds a `Req`)
is accepted: `reqTy` gains `(self bytes)` in the post-D5 `lang!` day, and `reqOk` bounds it. The
LANG builtin `accountOf : bytes → bytes → bytes` is refused. In its place, accounts in a call are
`AcctRef D = well (asset : D) | of (owner asset : D)` (Body's `transfer src dst` and `credit acct`;
LEDGER-7 narrowed LANG's `id` arm to `well`, refused `notWell` off a well, so every value cell has one
name), and the receiver resolves `of` to `accountId X owner asset` (KERNEL theorems `resolve_of`,
`resolve_well`). In `callTy` these fields are `acctRefTy = sum {of : rec {asset : bytes, owner : bytes},
well : bytes}`. Minting is a transfer out of `well`, unchanged.
**Alternatives.** (1) `accountOf` as a `Prim`: it threads KERNEL's hash (a `Ctx` parameter, a
different function in the Sim) into Eval, `primEval`, BigStep and every meaning proof. It also kills
the `decide +kernel` teeth under a real hash (the documented reduction bomb), and it makes a second
place that computes `accountId`. (2) Owner-addressed fields only (LEDGER-6's rejected alternative):
breaks minting. A sum keeps the well.
**Critique.** Resolution moves work into every value receiver, and the client must compute the
resolved id to pin it (as it already does for born ids). A package that wants the account's id as
DATA (to show or compare it) still cannot compute it. `of` with an attacker-chosen owner names an
account the object does not own; the transfer is then refused by authority, as for any `id`.
**Meta-critique.** Refusing the builtin keeps hashing out of my layer, which is convenient for me. The
independent tests are the teeth (b) and law 1 (c), not my convenience.
**Status.** agreed (LEDGER-7, 7229d95); built in D5 (kernel, c3c7aa3) and the post-D5 `lang!` day (`acctRefTy` in `callArms`, `(self bytes)` in `reqTy`, bounded by `reqOk`; journey LC3 checks `req.self` is the invoked object).

## LANG-26 The receiver's verdict on a stdlib package is its laws' meaning (2026-10-17; closes LANG-20's chain)
**Decision.** `Lang/Proofs/Receiver.lean` proves `judgeOne_pkgOf_admits`. If the receiver's judge admits
`old → new` and the pinned package is `Std.pkgOf S laws methods` (distinct labels, digest round trip),
then both states read at `S` and every law of the package with no `ref` and a law's shape `Admits`
the transition with the receiver's request. The proof has four links: `judgeOne_ok` (the for-loop over
`p.laws` inverted), `load_leaf` (an import-free package loads as itself at 0; deleted by LANG-55 for
`load_top`, which covers imports), `relocate_noRef`
with `noRef_<law>` for every Std law, and `find_of_mem_nodup` with `sortRow_perm`. Corollaries restate
three specs on the deployed run: `judgeOne_quorum_change`, `judgeOne_quorum_relaw` and
`judgeOne_machine_invoke`.
**Alternatives.** Evaluate `judgeOne` on concrete packages by `decide +kernel`: impossible, because
`decodePackage` is well-founded (LANG-2's gap 4), and it would be one instance, not the general fact.
Change `admitPackage` to skip relocation for import-free packages: it changes deployed code to suit a
proof, and it would be a second code path.
After the vacuity read (a773ed76): the quorum corollaries take the CHECKED generator
(`quorum … = .ok t`) and conclude `ms.Nodup ∧ 1 ≤ k ≤ |ms|`; `methodIndex_pkgOf` shows an edge's method
label is what the kernel's index runs; `load_top` shows the loaded package at `load`'s index is
`readPackage`'s (imports or not), which closes LANG-22's critique. `reqData_agent` states the agent
field over `r`.
**Critique.** The premise `readPackage … = .ok (pkgOf …)` is about the decoded package, so a package
built by hand that equals a `pkgOf` output is covered and one that differs is not. The chain does not
reach packages with imports (`load_leaf`; LANG-55: `judgeOne_admits` does, through `load_top`). `NoRef`/`IsLaw` are per-law premises in the conclusion,
discharged for every Std generator but not for a hand-written law. The conclusion is `∃ lib, Admits …`:
sound for the Std specs, which hold for every `lib`, but weaker than naming `L.lib`.
**Meta-critique.** I proved the import-free case because it is all the Std packages produce today.
That is "the case that went quickly" once more, and it is labelled as such above. The distinct-labels
premise could be derived from the install check (a non-ascending row does not check), and
`load_leaf` names fuel 7 by `closureDepthMax = 8` definitionally; both are left as stated. (LANG-55 closes
both: distinct labels follow from the receiver's own load, `load_checked` + `pkgOf_labels_nodup`, and the
fuel is `closureDepthMax - 1`.)
**Status.** built.

## LANG-27 Type errors by name and path: `inferE` is the checker, `infer` its `toOption` (2026-10-17; LANG-3's open item 3)
**Decision.** `Lang.Check.inferE Δ Γ t : Except TypeErr Ty` is the one checker. `TypeErr` holds a
`TypeError` (20 named rules: `unbound`, `notFunction`, `argument`, `noField`, `notCanonical`,
`payload`, `arms`, `armType`, `branches`, `declared`, …) and the path to the failing subterm,
outermost first (`fn`/`arg`, `body`, `target`, `cond`/`then`/`else`, `left`/`right`, a field or arm
label). `infer := (inferE …).toOption` and `check := (checkE …).toBool`, so there is no second
checker. Install's refusal `illTyped` carries the `TypeErr`: its wire text is `illTyped RULE @PATH`,
e.g. `illTyped declared @top` or `illTyped operands @a`. `ob type`/`ob eval` print the same.
Theorems: `inferE_sound`, `inferE_complete`, `inferE_iff`, `checkE_ok_iff`; `infer_sound`,
`infer_complete`, `infer_iff`, `hasType_unique` and `check_iff` are now corollaries.
**Alternatives.** Keep `infer : Option` and add `inferE` beside it with an agreement theorem: two
checkers, one of them only for diagnostics, which is the twin shape. Report a byte offset: terms
carry no positions after reading, so the reader's offset is lost by then.
**Critique.** The path names term STRUCTURE, not source text: a resident must still map `@body.f.arg`
back to their s-expression. Only the first failure is reported, in evaluation order (function
before argument, condition before branches). The error carries types, so its text can be long, and
`text` prints only the rule name and the path.
**Meta-critique.** I picked rule names by reading the `none` branches of the old checker, so the
taxonomy is the implementation's. A resident might have wanted names for the mistakes people
actually make (a missing case arm, a wrong field).
**Status.** built.

## LANG-28 One printer: `Lang.Print` (2026-10-17; LANG-3's open item 4, for HOSTING)
**Decision.** `Lang/Print.lean` is the one printer of the core as the text `Lang.Read` reads. Types,
terms, data and packages print first as a `Read.SExp` (offsets 0) and then as characters
(`chars`/`items`, one separator between elements). Anything with no text is `none`: a label that is
not one atom (empty, or holding a `Read.isDelim` character) and a free variable. A bound variable
is `x<depth>`. Bytes print as `"text"` when they are UTF-8 with no `"`, otherwise as `#hex`.
`Read.term` now reads `#hex` atoms as bytes too, as `Read.dataAt` already did, so every term with
atom labels and no free variable has a text. `Read.showTy`, `Resident.showData` and `Resident.hex`
are deleted. `ob` refuses `unprintable` when there is no text. The rows and the journey use
`Print.tyText T`, whose argument `(tySx T).isSome` is decided where the constant is written, so the
printer has no fallback string. HOSTING deletes `Hosting/Text.lean` and uses `Print.package`, which
keeps that file's layout of one section per line: `world/grain/Lifecycle` does not change.
**Alternatives.** Keep HOSTING's string printer and give `showTy` a home in it: that leaves two printers
of types, and the second one checks no labels. A total printer that prints any label as given: an
unreadable label would then print as text that reads back as something else, or as nothing, with
no refusal at all. Print straight to `String` without the `SExp` step: then the round trip has to be
proved through string appends, rather than as two separate facts, the parser over `chars` and
elaboration over an `SExp`.
**Critique.** The label check is looser than HOSTING's `atomOk` (that one excluded `true`, `false` and
numerals). This is correct because `Read` takes any atom in a label position, but it is a claim, and
`Lang.Proofs.Print` (the next commit) is what makes it a theorem. Until then the only check is
HOSTING's compiled instance, `lifecycle_text_reads`. `#hex` in a term shadows a binder whose name
starts with `#`, just as a numeral shadows a binder named `5`.
**Meta-critique.** I kept HOSTING's package layout so that their shipped file stays byte-identical. That
is a compatibility reason, which CLAUDE.md says is not a reason. The real reason is that one section
per line is the layout a member reads.
**Status.** built; the round trip is LANG-29.

## LANG-29 The printer's round trip is a theorem (2026-10-17; LANG-28's next commit)
**Decision.** `Lang.Proofs.PrintParse` + `Lang.Proofs.Print` prove that reading the printed text
gives back exactly what was printed: `readTy_ty` (a `wf` type), `readTerm_term` (a `Canon` closed
term: ascending rows, `wf` annotations), `readData_data` (data conforming to a `wf` type, at that
type), `readPackage_package`, and the corollaries `readTerm_checked` / `readPackage_checked`: every
closed term that checks, and every package `checkWith` accepts over canonical import interfaces,
is canonical (`hasType_canon`) and so reads back. The proof has two halves. The parser half
(`sexp_chars`, `sexps_items`) shows that `Read.sexp` over `chars x` returns `x` up to offsets
(`Same`) for an `Ok` form within the fuel `need x`. The elaboration half (`ty_tySx`,
`term_termSx`, `dataAt_dataSx`) runs over any form `Same` as the printed one. The printer now
refuses (`none`) a form past `Read.depthMax` (`fits`), so its `some` covers every case the theorem
does: the fuel is not a premise. Teeth: `reqTy_reads`, `five_reads`, `id_reads`, `empty_package_reads`, three refusals by `decide`;
journey L0c prints `Owned` and reads it back to the same bytes, refuses a non-atom label, and
round-trips non-UTF-8 bytes as `#hex`.
**Alternatives.** One closed instance per shipped package by `native_decide` (HOSTING's
`lifecycle_text_reads`): an instance of a general fact, trusting the compiler. A bisimulation over
strings without the `SExp` step: the offsets and the string appends would be tangled together in
every case.
**Critique.** `Canon` is a premise of `readTerm_term`, discharged for checked terms. A term that does not
check but has unsorted rows prints to a text that reads back as the SORTED term. The theorem
says nothing about such a term, and nothing should. `readPackage_checked` needs canonical
import interfaces: an import whose interface is not `wf` could make a `case` over its sum read back
reordered. Installed interfaces are checked, but this file does not prove that (LANG-2's item 3).
The parser theorem covers only the printer's own layout (one space, or "\n  " per section), not
arbitrary whitespace or comments. That is enough for a round trip, and it is not a statement
about every text. The fuel bound is the reader's, and the reader spends fuel per list ELEMENT as
well as per nesting level (`Read.sexps`), so a long `anyOf`/`guards` chain costs in proportion to
its length: measured 10-17, a 63-member `Std.quorum` law needs 385 of 512 and a 63-id `allowlist`
351. An installed package that goes past 512 has no text at all, for the reader and the printer
alike. The fix is on the reader side: fuel by nesting depth only, with list length bounded
separately. It is open (vacuity read a773ed76, MEDIUM). Also open from that read: `Read` accepts a
binder named `true`, `5` or `#ab`, and every use of it reads as the literal, so that binder is
unreachable. The reader should refuse such a binder by name.
**Meta-critique.** I proved the round trip because HOSTING held a compiled instance and the brief
said "the general fact". The fuel bound became a printer check partly so the theorem could drop a
premise. It is also right on its own terms: the printer must not emit a text the reader refuses.
**Status.** built.

## LANG-30 The reader's fuel is nesting depth; a list's length has its own bound (2026-10-17; LANG-29's MEDIUM)
**Decision.** `Read.sexp` spends one unit of fuel per nesting level and nothing per list element.
A list's elements are read by `Read.sexpsWith`, at most `Read.listMax = Wire.rowMax + 2` of them,
and one more is refused `tooLong` (a new `ReadRefusal`, at the list's open offset). The
elaborator works the same way: `entries`, `arms`, `fnWith` and `dataRowWith` recurse on the list
and give every element the same fuel. `Print.need` is the nesting depth, `Print.width` is the
longest list, and `Print.fits` checks both. So a printed text the reader would refuse is still
`none`. Every form the wire carries fits the width (a row is at most `Wire.rowMax` entries after
at most two head words; an application prints as two elements), so for an installable package
only depth can fail. Each stdlib chain that grows with its parameter now has a named cap in its
checked generator: `Std.membersMax = 63` (was the literal 63), `Std.idsMax = 256` (`allowlist`
is now checked and refuses `tooManyIds`; `allowlistLaw` is the unchecked term), `Std.edgesMax =
256` (`machine` refuses `tooManyEdges`), and states at most `Wire.rowMax` (`tooManyStates`, in
`machine` and `stepTo`). `Lang.Proofs.StdFits` bounds each law's printed depth as a function of
its parameter and of the state type: quorum `max d(S) (n + 14) + 3`, allowlist
`max d(S) (n + 8) + 3`, machine `max d(S) (e + 8) + 3`. `quorum_text`, `allowlist_text` and
`machine_text` show that every checked output over a state type at most 256 deep has a text, and
the `_reads` forms show that it reads back once it checks. Measured on the printer (10-17): a
63-member quorum now needs 80 (was 385), a 63-id allowlist 72 (was 351). The two row sorts are
now one: `Row.sort`, an insertion sort. The kernel evaluates it, so it still serves the teeth.
`Std.sortRow` and `Read.sortRow` (a mergeSort) are deleted. Both were stable sorts by label, so
every sorted row and every package id is unchanged.
**Alternatives.** Keeping per-element fuel and raising `depthMax`: the cost would still grow with
chain length, and a deeper bound would only move the cliff. Fuel-free elaboration by structural
recursion on `SExp`: it is possible, but every round-trip lemma would have to be restated around
it, and the parser's depth bound already makes the elaborator's fuel inert. Moving the caps into
`Package.checkWith`: install already has the wire's bounds, and these caps are about the TEXT,
which is the generators' business.
**Critique.** The `_text` theorems take the state type's depth (`TyPrints 256 S`) as a premise.
They do not derive it from the install check, and they cannot yet. The wire's bound is a TREE
depth of 1024 (`Wire.depthMax`), and printing nests a row entry one level deeper than its tree
node, so an installable package can be deeper than the reader's 512. The wire also accepts labels
the printer cannot print (a space, a parenthesis). So today a wire-valid package can have no text
(vacuity read a773ed76, MEDIUM). The fix is to align the bounds: one label rule shared by the
wire and the printer, and a reader depth that covers the wire's. Then prove `encodePackage p = some b
→ (package p).isSome` and delete the 256 premise. That is LANG-31, LANG-6's next commit. The reader still elaborates `fn` binders and multi-argument applications into
terms deeper than their text (n binders in a depth-2 form). Nothing relies on the term's depth
being bounded by the text's, and the wire's own bound refuses a term too deep to carry. `Prints`
bounds are upper bounds composed by `mono`, not exact. The printer's figures are 80 and 72; the
theorem says at most 80 and at most 74. Teeth: `quorum_at_cap_text` and `allowlist_at_cap_text`
(premises met at the caps), `allowlist_past_cap_no_text` (600 ids: no text, so the cap carries
the weight), `machine_at_cap_accepted`/`_text`, refusal teeth for each new cap in StdTeeth, and
`allowlist_at_cap_reads` (the law checks at the cap, so the `_reads` premise is met), and
journey L0d: an allowlist of `idsMax` ids prints and reads back to the same package bytes, a list of `listMax + 1` elements
is `tooLong`, and a form `depthMax + 1` deep is `tooDeep`, each next to the bound that reads.
**Meta-critique.** The measured 385 made "raise the bound" look sufficient. The design question was
which quantity the fuel should count, and only nesting has a reason to be bounded. I priced the
general fit theorems as heavy and was tempted by instance checks at each cap. Those would have
said nothing about any other member list. The constructor-bound toolkit (`prints_*`, about 500
lines) gives the general statements.
**Status.** built.

## LANG-31 One label rule for the wire, the reader and the printer; the reader reads two levels past the wire; every installable package has a text (2026-10-18; LANG-30's critique, vacuity MEDIUM; LANG-6's WIP finished by LANG-8)
**Decision.** A label is one atom of the text (`labelAtom`: nonempty, no `Read.isDelim` character;
both now live in `Lang/Row.lean`) of at most 64 bytes of UTF-8. `Wire.labelOk` is that rule, and
`Wire.labelOf` refuses a non-atom label when decoding, so the wire, the reader and the printer all
use one predicate (`Print.labelOk` is deleted; the printer and every proof `open Wire (labelOk)`).
`Read.depthMax = Wire.depthMax + 2` (1026, was 512). The reason for the 2: a printed form is at most one
level deeper than its tree. A row entry is one tree node and one list. Only the leaves `(ref i)`,
`(rec)` and `(record)` print as a list over a tree leaf. A package's sections add the second
level. `Lang.Proofs.Prints` is the constructor-bound toolkit, split out of `StdFits`.
`Lang.Proofs.PrintWire` proves the alignment:
`tyWire_prints` (a type whose tree fits depth `D` prints within `D + 1`), `hasType_prints` /
`fieldsTy_prints` / `armsTy_prints` (the same for a well-typed term under its context's binders,
by recursion on the typing derivation), `package_prints` (wire-valid + tree in bounds + install
check accepts ⇒ `Print.package p` is `some`), `installed_prints` / `installed_reads` (for any
bytes `decodePackage` accepts, and the text reads back to exactly the package), `state_prints`
(an encodable package's state type prints within `Wire.depthMax`, which is `StdFits`' premise:
`quorum_text_at`, `allowlist_text_at`, `machine_text_at` take the package instead of the depth).
`StdFits`' law skeleton bound is now `max (M + 2) (max 9 (N + 5))` (was `max M (max 6 (N + 2)) + 3`:
the state type sits one level less deep than that said; the 9 is the request type's lambda).
**What breaks.** The decoder now refuses bytes it used to accept: a package with a label that is
not one atom (a space, a parenthesis, a quote, `;`, or empty) is refused `lang/package`, and
`encodePackage` returns `none` for it. No bytes change for any other package, so nothing
re-ids. Every package on main has atom labels: `world/grain/Lifecycle`'s bytes are unchanged (its
generated row), and the journey's and the rows' packages (THE BAR's counter) encode as before
(their verdict exes in this commit's judge). LEDGER's escrow and HOSTING's Allowance must use
atom labels; identifiers are.
**Alternatives.** (1) Escape labels in the printer (`|a b|`): a second label syntax in the reader,
plus an escape round-trip proof, all for labels no program needs. (2) Keep the reader at 512 and
lower `Wire.depthMax` to 510: the wire's bound is CODEC's tree depth shared with the size
accounting, and the reader's fuel costs nothing past the text's own length. (3) Prove
`package_prints` only for Std's generators (LANG-30's state): that leaves a hand-written package
with no text.
**Critique.** `Read.depthMax` is exact for packages but not for a standalone term or type: a
closed term whose tree is 1024 deep prints within 1025, so `Print.term` has one level of slack.
The theorems state upper bounds. The tooth `deep_needs_depthMax` shows the package bound is met
exactly: `deepPkg` is 511 record levels in body and interface, its tree is `Wire.depthMax` deep,
and its text needs exactly `Read.depthMax`. `deeper_unfit` shows one more level has no tree, and
`spaced_label_tree_refused` / `atom_label_tree_reads` tooth the decoder's side over a tree, and
journey L0f runs the same package text-first (read, check, encode, print, read: same bytes; one
level deeper `tooDeep`). `package_prints` needs the install check only for two things: the typing
(to rule out free variables) and `checkShape`'s list lengths (imports ≤ 16, methods ≤ 64, laws ≤
16, so the section lists fit `Read.listMax`). A wire-valid package that fails the check may have
no text, and that is by design: `ob` prints what can be installed. `installed_reads` assumes
canonical import interfaces (`∀ A ∈ ifaces, A.wf`), as `readPackage_checked` does. The loader's
interfaces come from installed packages whose `checkShape` passed, but no theorem here connects the
two (LANG-4's Receiver leftovers; cv task). At a state type 1024 deep the stdlib's laws need exactly
`Read.depthMax` (`max (M + 2) …` at M = 1024): the `_text_at` corollaries hold with zero margin.
**Meta-critique.** LANG-30 measured the gap and named it MEDIUM. Then it bounded only the stdlib,
because a general theorem looked heavy. The general theorem took one recursion on the typing
derivation (the template was `hasType_canon`). The "+1 overall" argument (a row entry's extra list is absorbed by its own tree node, so the
printed form is one level deeper than the tree in total, not per level) was the only real
content, and it was cheaper to prove than the Std-specific bounds. The narrowing of the wire
looked like a flag day and was priced as one. Checking what holds the old shape took one grep:
nothing does.
**Status.** built (this commit). `lang!`: the decoder narrows. Nothing re-emits.

## LANG-32 A binder may not have a reserved name: `reservedBinder` (2026-10-17; LANG-29's vacuity point 8; LANG-31 is the bound alignment, next)
**Decision.** `Read.term` reads an atom as a literal (`true`, `false`, a numeral, `#hex`) before it
looks at the scope, and a list headed by a form's word (`if`, `lam`, `case`, …) or a primitive
(`+`, `beq`, …) as that form. So a binder named like any of these could not be referred to.
`(lam true bool true)` silently meant the constant, and `(lam if nat (if a b c))` the
conditional. `Read.binder` refuses a reserved name at every binding site (`lam`, `let`, a `fn`
binder, a `case` arm) as `reservedBinder @pos name`, a new `ReadRefusal`. `Read.isReserved` is
`isLiteral` (the test `term` applies to atoms), `keywords` (the head words `term` matches) and
`primOf`. The printer names binders `x<depth>` (`isReserved_name`, `binder_name`), so the
round-trip theorems keep their statements. No shipped text uses such a binder:
`world/grain/Lifecycle` is printed by `Lang.Print`, and the Std laws are terms, not texts. So no
package re-ids. Journey L0e plants seven refusals (`true`, `5`, `#ab`, `false`, an arm named `7`,
`if`, `+`) and one acceptance (`x5`).
**Alternatives.** Let the scope shadow reserved words, so a bound `true` or `if` reads as the
variable: then a text means different things depending on its context. Renaming silently would
be a twin of the binder.
**Critique.** `keywords` is a list written beside `term`'s patterns. `term_unreserved_head` ties
the two together. A bound name that is not reserved, heading a list of ANY arguments, reads as an
application of that variable. Its proof needs the head words of every form, so a form added to
`term` without its word in `keywords` makes the theorem false (vacuity read a773ed76's
suggestion: stated for one and two arguments only, it left `lam`/`if`/`inj`/`let` covered only
by the journey). An atom like `#6` (an odd hex count) is not reserved: it
reads as a variable, so it is reachable and fine.
**Meta-critique.** I first wrote this for literals only and noted keywords as "the same class,
narrower, not refused". That is the honest-label move. The class is one fault, so the refusal is
one refusal.
**Status.** built.

## LANG-33 A method declares its call slots: k ≤ callsMax, each a sub-sum of `callTy` (2026-10-18; the post-D5 `lang!` day, amends LANG-23's fixed arity)
**Decision.** A method's type is `methodTy S A ks = fn S (fn A (fn reqTy (rec {calls : callsTy ks,
state : S})))`. `callsTy ks` has slots `c0 … c(k-1)`, slot `i` being `optTy ks[i]`. `methodSig`
(the install check's method shape) requires `k ≤ Kernel.Bounds.callsMax`, the labels in order,
and every `ks[i]` a sum of some of `callArms`, each arm at exactly its `callArms` type
(`callSlotOk`). `callOf kinds` builds one. A method that makes no calls has `calls : rec {}`
(`Std.methodOf`, `Std.stepTo`); `Std.methodWith` takes slot terms (`noCallT T`, `someCallT T t`)
and refuses more than `callsMax` (`tooManyCalls`). `Std.pkgOf`'s methods become
`(label, argument type, call slot types, term)`. `resolveMethod` returns the slots, and
`runMeasured` extracts at the method's own `resultTy p.state ks`, then `callsOf` gives KERNEL its
`List (Body D)`. Theorems (`Lang/Proofs/Call.lean`): `run_calls` (the deployed run's calls are at
most `callsMax` and all callable, so KERNEL's `tooManyCalls` and `notCallable` never fire on a
Lang method; KERNEL keeps both as its own assertions, law 4), `bodyOf_callData` /
`callData_bodyOf` (the round trip against `Body`), `callData_not_callable`; `methodSig_spec`
(`Proofs/Load`); `method_run_sound` and `invoke_never_stuck` restated at `resultTy p.state ks`.
Journey rows LC0–LC6: a six-object `Relay` chain whose method invokes the next object through a
grant naming it, forwarding pre-encoded arguments (LANG-23 (iii)). Depth 4 is admitted, every
object runs once, and `req.self` is the callee. Depth 5 is refused `callTooDeep`. A call naming its
object by non-digest bytes is refused `program "calls: c0 obj: not a digest"`. A method with nine
slots is refused `badMethod go` at install. Plant `drop-calls` (the run's calls never reach the
kernel): LC3's chain end is untouched, and LC4 is admitted.
**Why the amendment.** With LANG-23's fixed eight slots of `optTy callTy`, every method's type
carried eight copies of `callTy` and every body's eight `none` annotations eight more:
`world/grain/Lifecycle` went from 7215 to 57953 bytes, and the rows' `grain` row went red at its
create (`refused badResult`; I did not trace which bound the larger package hit, and the row is
green at the declared-slot size). LANG-23's critique called the
eight `none` slots "author-time cost only; no bytes on the wire". That was false: they are in the
package bytes, hence its id and every install. With declared slots the Lifecycle is 7505 bytes
(+290: `rec {calls : rec {}, state : S}` and `self` in `reqTy`). The type also states the
method's capability: a lifecycle method's type says it makes no calls (Hosting's
`method_no_calls`), and the escrow's says it may make only transfers.
**Alternatives.** (1) Keep the fixed row and share `none` by a `λ`: it halves the body, but the
type still carries `callsMax × callTy` per method. (2) A list or recursive type in the core: see
LANG-23. (3) One shared calls-type package imported by reference: the closure must load it for
every method, and the type is still expanded at the checker.
**Critique.** Call data is not canonical: option rows (calls and a grant's rights) skip `none`
wherever it sits, so `callData_bodyOf` is stated up to re-encoding. A slot type is checked
structurally against `callArms` (width subtyping at one boundary only, the method shape), not by
the core typing, so `callSlotOk` is a second place that knows `callTy`'s arms: `callArms` is the
one list both read. The extraction now forces the result record, +4 ticks per invoke: 2 to force
the `calls` field and 2 to force the `state` field (each forced suspension is an init step and a
value step; an empty calls row and the unknot of a record value cost 0). THE BAR's
`ticks-per-call` was re-pinned 30 → 34 with GATES-2's agreement. GATES-2's critique, owed by LANG:
`ticks-per-call` is an absolute count, so every honest semantic change raises its ceiling and hides
real waste among the honest raises. The row should be a ratio, the machine's ticks over what the
program requires (e.g. the BigStep derivation's size), pinned near 1.
**Meta-critique.** I built the fixed row exactly as LANG-23 said, saw the journey green, and found
the cost only when a row in another layer went red. The size of a type had never been measured.
The independent check is the Lifecycle's byte count in the commit, and G0's byte gate on it.
**Addendum (LANG-8, cv 01a14a39-c253).** The converse is proved in `Lang.Proofs.CallLive`:
`bodyOf_live` / `callsOf_live` (data conforming to `callTy` / `callsTy ks` is refused only as
`FIELD: not a digest`, for bytes the digest decoder refuses), `extract_conforms` (extraction of a
typed value conforms), and `runMeasured_kinds` / `runMeasured_calls_le` (the deployed run's calls
match, in order and one to one, a sublist of the method's declared slots, each of its own slot's
kinds; so at most one call per slot). The refused bytes are bytes OF the data (`BytesIn`), not any
byte string (the reviewer's MEDIUM on the first draft). `sim_digest_roundtrip` discharges `bodyOf_callData`'s premise at the Sim.
**Status.** built (this commit). Re-ids every package with a method or a law (`reqTy` changed):
`world/grain/Lifecycle` re-emitted, and THE BAR's counter re-ids.

## LANG-34 THE BAR's tick row is a ratio: machine ticks per step the program requires, the required count being the size of the reference derivation (2026-10-18; cv 01a14a39-c22e, GATES-2's critique of LANG-33, with PROTOCOL-6 and GATES-2)
**Decision.** `gates/waste.tsv`'s `invoke ticks-per-call` (an absolute 34) is deleted. Its
replacement is `invoke ticks-per-required-step` = Σ machine ticks / Σ required steps over THE
BAR's invokes. It measures 34 / 22 = 1.5454… (printed 1.545), and the ceiling is rounded UP to
1.546 (GATES-3). The numerator is unchanged:
`runMeasured`'s ticks, i.e. the method run plus extraction. The denominator is
`Lang.Need.requiredOf` (tooling, `Lang/Sim/Need.lean`). It counts the size of the method run's
`BigStep` derivation and those of the suspensions extraction forces. `need` is a fuel-bounded
evaluator with one clause per `BigStep`/`Sel`/`Ext` rule, each adding 1 for its own instance.
It never calls `step`, `run` or anything the machine's count is defined by.
Theorems (`Lang/Proofs/Need.lean`): `Derives` is `BigStep` carrying its size, one constructor
per rule. `derives_bigStep` and `bigStep_derives` show the size erases to exactly `BigStep`.
`derives_unique` shows the meaning and the size are functions of the term. `need_derives` shows
the count is THE size, not a bound. `needExtract_forces` gives extraction's count as the sizes of what extraction must
force (`Forces`, a definition), and `forces_unique` shows that sum is one number (the vacuity
reader's MEDIUM: without it only the run half was exact). `runMeasured_setup` and
`requiredOf_spec` give `required_counts_the_run`: for an invoke `runMeasured` admits, the two
sides are one run's. The setup is this invoke's (`setupOf` of its inputs, PROTOCOL-6's
amendment), `ticks = budget - left` over that run and its extraction, and the count is the
derivation of the very value the deployed machine computed plus `Forces` at that type. Scale: a
`get` counts two rule instances (`get` and `Sel`), so the ratio reads per rule, not per term node. Rows (`Protocol/Rows/Run.lean`, cross-layer, PROTOCOL-6
agreed): sums over sums. The bar is broken by name if no invoke was measured, if Σ required = 0,
or if any invoke's count failed (`requiredOf` refuses `required: fuel` / `required: extraction`,
never a zero). The plant `waste-app` (`Lang.Need.wasteStep`: entering a closure first returns
`true` through an `ite` frame, two needless transitions per application, same meaning;
`runBy_step` shows the loop it runs in is the deployed `run`) must measure strictly above the
honest ratio. It measures 1.818, and a BLIND plant breaks the bar by name. Teeth: `need_idApp`
(`(λx.x) 1` requires 4), `idApp_not_three`, `idApp_ticks` (the machine takes 7),
`idApp_plant_ticks` (the plant 9).
**Why.** An absolute count rises with every honest semantic change (30 → 34 at LANG-33), so real
waste hides among honest raises. A ratio over the reference derivation moves with the semantics
in both terms and rises only when the machine does more work per rule instance. The denominator
must be independent of the machine. GATES-2's condition: it must be exact, since an over-count
hides waste and `count := ticks` passes any `count ≤ ticks` bound. So the theorem pins equality
with the derivation's size, not a bound against the machine.
**Alternatives.** (1) Weighted rule instances (3 per app, …) chosen so the ratio is 1: that is
the machine's count read back, constant by construction. (2) A sized twin of `BigStep` alone:
`Derives` IS that, which is why it ships with the erasure theorems in both directions; replacing
`BigStep` by `Derives` everywhere (Agree, Complete) was not done. (3) A lower bound
`required ≤ ticks` (ratio ≥ 1): true by the CEK shape, not proved, and not needed for the gate's
direction.
**Critique.** `Forces` defines what extraction must force. No theorem ties it to the meaning of
extraction (for `v` extracted at `T` to `d`, `Forces T v m` holds and its forced meanings are
`d`'s), so extraction's share of the denominator is tied to `BigStep` but not to `extract`'s
result. In THE BAR that share is the `calls` and `state` fields. Not proved either:
`required ≤ ticks` (ratio ≥ 1), and its corollary that `requiredOf` never refuses on an invoke
the machine finished (a derivation's size bounds its depth, which bounds `need`'s fuel). Until
then a refusal breaks the bar by name; it is never skipped. Both are owed (cv task). The plant wastes only in the method run (extraction runs on the
deployed `force`): the planted ticks are runMeasured's ticks − the honest run + the wasteful run.
`need`'s fuel is the call's tick budget. A derivation deeper than the budget would refuse the
measurement by name; it cannot read as cheap. `runBy` is a second copy of `run`'s eight-line
loop, kept honest by `runBy_step`. The reader proposed deleting it by defining the deployed `run`
as `runBy (step lib)`. I kept the copy: the plant must run a different stepper somewhere, the
equality is a theorem rather than an agreement, and the generic deployed loop would re-open
about 25 proof sites for a tooling plant. The plant is checked in rows against the honest ratio, not
in `gates/waste.py` against the ceiling. Since the ceiling is pinned at the measured value they
coincide today. A waste.py-level plant is GATES' to add if wanted.
**Meta-critique.** The design note I inherited proposed `need_bigStep` (soundness) plus a count
"of a derivation". A sound evaluator that counts 2 per node also satisfies that. GATES-2's reply
caught it before any code: the exactness has to be a statement over the derivation, and the
uniqueness of the size is what makes "the" derivation's size mean anything. The independent
check is the teeth (4 for `(λx.x) 1`, refuted 3) and the plant's measured rise.
**Status.** built (this commit). Nothing re-ids: no deployed definition changed. `gates/waste.tsv`
loses one row and gains one (`WASTE: invoke:` in the commit).

## LANG-35 The install check reads its imports through the loader (2026-10-18; cv 01a14a52-4721, the LANG-31 vacuity read; LANG-2's gap 3)
**Decision.** `checkInstall` takes the interfaces it checks a package against from
`loadAll digestOf look (closureDepthMax - 1) p.imports` and `ifacesAt` (refusal `closure`). That is
the loader a run and a judge use, one depth below the package's own load. Before, it read each
import's cell with `readPackage` (decode only). So the install check now re-checks the imports'
whole closure: every package in it must be pinned, decode, pass `checkWith` against its own
imports, and fit the depth a run will load. Theorems (`Lang/Proofs/PrintWire.lean`):
`checkInstall_checked` (the interfaces the check read are canonical, by `loadAll_inv` and
`checkShape_wf`) and `install_reads` (every package `checkInstall` admits has a text that reads
back to it, with no premise). Canon's docstring no longer names the install path as the
exception.
**Why.** `installed_reads` took `∀ A ∈ ifaces, A.wf` as a premise that nothing discharged for a
package with imports. Proving that pinned package cells were installed would be a KERNEL World
invariant, on another layer and in another induction. Loading at install is one code path with
run and judge (law 1), and it also refuses at install a package a run could never load (an
import closure that is unpinned, too deep or no longer checks), where before it installed and
then failed at every invoke.
**Alternatives.** (1) A World invariant "every kindPackage cell passed checkInstall" (KERNEL). It
is true of the deployed receivers, but it is a theorem about all of KERNEL's writes. (2) Drop the
premise by proving `readPackage_checked` without it. I could not build a counterexample: every
annotation is itself checked wf, so an unsorted import row cannot reach an annotation (`badType`).
The premise may be an artifact of `hasType_canon`'s statement, but that proof is not done.
**Critique.** The tooth is weak. No journey row installs a package whose import closure is
unpinned or fails its re-check, so the new refusals are reached by no test, only by the theorem's
hypothesis. Owed (cv task, rated LOW by the vacuity reader, to be done soon): that row, with a
plant restoring the raw read that flips it to admitted; and `install_loads` (an installed
package's own load succeeds under the same pins), which is the property clients rely on and
which no theorem states yet. A client-visible change: install now needs the import CLOSURE
pinned, not only the direct imports; a call pinning only direct imports is refused `unpinned`. Install now costs a closure load: each import is decoded and re-checked once per
install, which is bounded by `closureDepthMax` and the packages' sizes, and is what every invoke
already pays.
**Meta-critique.** The cv task asked for "a theorem over the loader or a refusal by name at
load". I took the code-path change because it made the theorem a two-line corollary. The
independent check is that lang-journey and rows stay green (no installed package changed its
verdict) while the theorem's premise disappeared.
**The owed tooth (cv 01a14a91-be1e, LANG-10).** lang-journey LI: `Mid` imports `Owned`, `Top`
imports `Mid`; installing `Top` pinning only `Mid` is refused `unpinned` naming `Owned` (LI2), pinning
both is admitted (LI3). PLANT raw-install puts back the pre-LANG-35 check (each import's interface
read raw from its cell) and LI2 flips to admitted, so the refusal comes from the closure load and
from nothing else. `install_loads` (Lang/Proofs/Load.lean): `checkInstall look b = ok`, `idb` a digest
of a pinned package cell whose slot 0 is `b` ⇒ `load look closureDepthMax idb` succeeds and the
package at its index is `b`'s. LI3 meets its premises.
**Critique of the tooth.** `install_loads` holds the pinned view fixed: install and a later run see
the same `look`. Import cells are ROM, so a later World agrees on them, but that is KERNEL's fact
and not stated here; a run that pins less than the install did is still refused `unpinned`, as it
should be. No row covers an import closure that fails its re-check (every package that got into a
cell passed the install check of its day; one would need a package cell written some other way).
**Meta-critique.** The plant is the right control: it is the old code, verbatim, so a pass under it
measures exactly what LANG-35 changed. The theorem is a direct unfolding (install's `loadAll` IS the
load's `loadAll` one fuel down), which is the point of LANG-35, not a weakness of the statement.
**Status.** built (this commit). Nothing re-ids: no package bytes changed.

## LANG-36 A not-a-digest refusal is tied to the path it names (2026-10-17; cv 01a14a69-5909, the c253 vacuity re-read, LOW)
**Decision.** `Lang/Proofs/CallLive.lean` replaces `BytesIn b d` ("b is some bytes leaf of d") with
`BytesAt b p d` ("b sits in d at label path p"). Every record field on the path is named in `p`; a
sum arm is either passed over (`inj`: an option's `some`, a call's kind, an account's `of`) or named
(`arm`: an account's `well`). It adds `Names p f` (f is p's labels joined by `.`) and `Under p d d0`
(d sits at p in d0). `Live d0 x` now says a refusal `F: not a digest` has a path `p` with
`Names p F` and refused bytes at `p` in `d0`. `DigestRefusal c e` says slot `ℓ`, path `p` in its
call, bytes at `ℓ :: p` in `c`, and the refusal `calls: ℓ F: not a digest` with `Names p F`. The
proofs of `digest_live`, `optDigest_live` and `acctRef_live` now carry the path, so each literal
name in `bodyOf` and `acctRefOf` (`"obj"`, `s!"{f}.owner"`, ...) is checked against the record
label that holds the bytes. A typo in a refusal name breaks the proof.
Tooth: `CallTeeth.method_named_not_live`. On the LC5 row (obj is 3 bytes, args is empty, so `dig8`
refuses both), `calls: c0 method: not a digest` is not a `DigestRefusal`, because `method` holds a
nat. Under `BytesIn` it was one, witnessed by any bytes leaf.
**Alternatives.** (1) Name the arm on every `inj`, which would make paths unique. That changes the
deployed refusal texts: the call kind would join the name (`c0 invoke.obj`), and LC5b and every
client that matches the text would change. That is not wanted for a proof's convenience. (2) A
computed path set per datum: a `def` returning lists, which a proof module may not export.
**Critique.** Two looseness points remain. (a) `inj` and `arm` both apply at any arm, so a datum
has more than one path to the same leaf (`c0 obj` and `c0 invoke.obj`). Live allows either name,
and only the deployed one occurs. (b) A path is a bytes leaf the decoder refuses, not a field the
reader reads as a digest. On the LC5 row, `calls: c0 args: not a digest` is still a
`DigestRefusal`, though `bodyOf` reads `args` with `bytesAt` and never refuses it. That is owed
work, not a limit of the model (vacuity reader; my first draft called it a model limit, which was
the cost-estimate-to-constraint move). It is a real fork, cv 01a14aab-adae. (i), the default: one
`digestPaths` source in `Lang/Call.lean` that `bodyOf`/`acctRefOf` consult to choose `digestAt` or
`bytesAt`, with `DigestRefusal` requiring the path to be in it; no flag day. (ii) a `digest` type in
`Ty`, so that laws, methods and extraction can tell an id from bytes; a lang! day that re-ids every
package with a method, to be chosen with ROOT.
**Meta-critique.** The task asked that the bytes be tied to the named field. The proofs now do that
for the reader's own literal names, which is where a mistake would hide (a renamed record label
with a stale message). (b) is open and labelled owed.
**Status.** built (this commit). Nothing re-ids: proof modules only.

## LANG-37 THE BAR's ratio is above 1 by theorem, and extraction's requirement is what extraction forces (2026-10-17; cv 01a14a87-33b2, the LANG-34 vacuity read)
**Decision.** `Lang/Proofs/Derives.lean` (new) holds `Derives`/`DSel`/`DExt`, `derives_bigStep` and
`bigStep_derives`, moved out of `Proofs/Need` so that `Proofs/Complete` can count against them
without importing tooling. `Complete.Leads` now carries a transition count. `bigStep_leads` is
replaced by `derives_leads` (a derivation of size `n` is followed by the machine in `m ≥ n`
transitions; an error's count includes its faulting step), and `bigStep_run`/`bigStep_run_fault`
are restated over it. There is ONE simulation proof, not a counted twin. `reach_value` says a run
that returns follows every reach. `derives_lt_used`: if the run returns, `n < used ≤ fuel`. In
`Proofs/Need`: `force_lt`, `unknot_le`, `forces_le` (extraction pays at least `Forces`' size and
forces exactly the suspensions `Unknots`/`Forces` name), `extract_forces` (every completed
extraction has a `Forces`, so `Forces` is extraction's meaning, not only a definition beside it),
and `required_lt_ticks`: for an invoke `runMeasured` admits and `requiredOf` counts, `N < ticks`.
Tooth: `Need.skipStep` (a plant stepper that enters a literal application's body at once) finishes
`idApp` with value 1 in 3 ticks, below its derivation's 4 (`idApp_skip_below`). So the bound is a
property of the deployed step, and a machine that skips rule instances breaks it.
**Why.** LANG-34's ratio rested on "required counts the run" (`required_counts_the_run`) with no
inequality: a counter that over-counted, and so made the machine look efficient, would not have
contradicted anything. Now it would.
The bound is STRICT: even a machine with no waste pays at least one tick more than the
requirement (the final halt), so a ratio ceiling of exactly 1.0 must never be set.
**Alternatives.** A separate counted copy of `bigStep_leads` next to the old one: a twin, refused.
Counting the machine inside `Derives`: that would mix the reference relation with the machine.
**Critique.** (1) `requiredOf` can still refuse `required: fuel` on an invoke the machine finished,
because `need`'s completeness is unproved (cv 01a14aba-1281). The ratio row then reads
UNMEASURED, not wrong, but the reachability half of the cv task is open. (2) The bound is strict
and loose by a constant per application (app = 3 transitions, 1 rule). `ratio ≤ c` is not
claimed: that is the waste row's measurement, not a theorem. (3) The plant is a stepper the
theorems do not quantify over. It shows the statement would be false for another machine, not
that the deployed machine is tight.
**Meta-critique.** The Derives move changes no statement other than `Leads`' arity (`Leads` is used
only in Complete). The bound came almost for free once the existing simulation carried counts,
which says the simulation was the right shape. The unproved completeness is named and owed, not
called a limit. Also owed (vacuity read): an EXTRACTION plant (a field forced twice) to show the
waste row catches extraction waste, cv 01a14abb-aa73-7e40-8bb9-1a264910eb79; skipStep teeth the floor, not the row.
**Status.** built (this commit). Nothing re-ids: proof and tooling modules only.

## LANG-38 Ids are a type: `digest` (2026-10-17; cv 01a14aab-adae, ROOT ruling (ii); the digest `lang!` day)
**Decision.** `Ty.digest` is a type with one equality primitive, `deq : digest → digest → bool`, and one
literal form, `Term.digest s` (text `(digest #hex)`, at most `Bounds.digestBytesMax` = 32 bytes, checker
`digestRange` past it). The value is `Val.digest` and the data is `Data.digest`. In text, data at type
`digest` reads and prints as `#hex`. The wire adds tags and moves none: Ty tag 7, Term tag 16, prim code 10.
Data at `digest` is `bytesOf digestBytesMax`. The ids a program sees or names are all `digest`: `reqTy`'s
`agent`, `principal` and `self`, and every id field of `callTy` (`obj`, `target`, `grantee`, `parent`,
every `via`, `well`, and an `of` account's `owner` and `asset`). `invoke`'s `args`, `transfer`'s `once`
and the occasion's `relaw`/`adopt` payload stay `bytes`. `Std`'s member tests (`ownerSigns`,
`allowlist`, `quorum`'s `isMember`/`approvalBy`) compare `agent` by `deq` against digest literals, and
`eqAt` gives `deq` at a digest field. No primitive makes a digest from bytes, and none turns one into bytes.
A digest is checked against the World where it enters a run:
- install, and every load's re-check, refuses a body with a digest literal that `digestOf` rejects
  (`program "notDigest"`, `Program.checkLits`);
- `readState` refuses a state digest leaf it rejects (`state field ℓ: not a digest`);
- the argument decode refuses one in the arguments (`arguments: not a digest`);
- the resident readers (`readAt`, so `seedOf`/`argsOf`) refuse one in seed or argument text
  (`notDigest`).
`callsOf`'s `not a digest` now ranges over digest leaves only (`CallLive.DigestRefusal`, tooth
`args_named_not_live`).
**What the type refuses that bytes did not.** (1) A call whose id field is built from bytes: a bytes
literal, a `cat`, an argument's bytes or a reason string in `obj`/`target`/`grantee`/`well`/... was
admitted at install and refused only at run time (`calls: cI obj: not a digest`), and only if the bytes
happened not to decode. A bytes value that DID decode named a cell the author never held as an id. That
package is now `illTyped argument/payload @path` at install, by name. (2) An id compared with bytes: a
law `beq`ing `agent` with a payout key or with a concatenation, or `cat`ing two ids into a "member", is
ill-typed. (3) A literal member id that is not a digest of the World (an allowlist naming bytes no member
can sign as) is refused `notDigest` at install, where before the law silently admitted no one.
(4) An id in state or in arguments that is not a digest is refused where the data enters the run, not
copied forward into a later call.
**Why.** ROOT ruling (ii) on cv 01a14aab-adae: a not-a-digest refusal should name a DIGEST field, and the
only way to make that true by construction is to make "is an id" a type. Fork (i), one `digestPaths`
list consulted by the reader, would have kept ids as bytes everywhere else (laws, Std, the machine).
**Alternatives.** (a) The digest arm as the kernel's own digest codec `dc : Stream D` (CODEC-7's
suggestion): a wrong-width digest would then be refused by the codec as well. Refused for now, and the
real reason is this: Lang's wire is not parameterized by `dc`. `decodePackage`, `decodeData` and the
data streams are D-free, so this change threads D through every package decode and every proof over
them. It is not refused because the Sim's digest is 8 bytes; `dc` would carry that. The check it would
add is subsumed: `digestOf` at every boundary refuses every non-digest, a wrong width included, so the
codec would hold a second check of a fact already checked, not a missing one. Named as an option, not
owed. (b) A fixed 32-byte Lang digest: every toy digest would become a non-digest, so the Sim width
would have to move. (c) A `digest → bytes` primitive (LEDGER-3's escrow used `req.self` as its once
key): refused, because an id that can become bytes can be `cat`ed and compared as bytes, which is the
leak this closes. The escrow now carries a creator-set `nonce : bytes` (LEDGER-11). (d) The relaw
payload as a row of digest option slots: the core has no lists, and the kernel bounds a law list only by
`lawsMax` = 16. A fixed-arity row of 16 options is possible but makes every law's relaw arm bigger. The
payload is a list of ids compared as one value (quorum's `proposedLaws` `beq`s two whole lists), never
consumed as an id, so it stays bytes and no primitive consumes an id from it.
**Flag day.** Every package with a method or a law re-ids, because `reqTy` changed and every method's and
law's type mentions it. Re-emitted in this commit: `world/grain/Lifecycle`, `world/hosting/Allowance`,
`world/escrow/Escrow` (`ledger-sim --write-text`, LEDGER-3), the journey's packages, and THE BAR's
counter's packages (PROTOCOL-7 re-runs rows). Every store re-geneses. That is the SECOND re-genesis
today, after CODEC-6's World journal flag day (9dd1e8c, KERNEL-39/CODEC-28). The two days could not be
merged: the World journal day landed before this one could start (it waited on LANG-37, cv 01a14a87-33b2,
by ROOT's order), so there was no shared window left. What refuses to load: a package cell from before
this day decodes, but its interface no longer checks against `reqTy` (`badMethod`/`badLaw`); a state slot
written as bytes under a type that is now `digest` decodes at the new type only if its bytes are a digest.
Nothing reinterprets: the old packages are refused, not read.
**Critique.** (1) A digest is a digest of SOME World, not of this one's cells: `deq` and the boundary
checks say "well-formed id", not "names a live cell". That is the kernel's question, asked when the call
enters (`unknown`/`noGrant`). (2) `callsOf`'s `not a digest` is now unreachable whenever the inputs
passed the boundary checks, because a run can only copy digests, never make them. That is not proved: a
provenance theorem over the machine (every digest a run returns is one of its literals or one of its
inputs) would make it a theorem rather than a check that never fires. (3) The occasion payload is still
bytes (alternative (d)). (4) No journey row now reaches `callsOf`'s `not a digest`, because the boundary checks
catch every non-digest first. The second line of defence is undetected until a plant reaches it. That plant is a
split of `runMeasured`'s digestOf into boundary and calls uses, owed as cv 01a14af1-2132 (vacuity read a773ed76, LOW),
alongside (2)'s provenance theorem, owed as cv 01a14acf-a188. (5) `ob check` (Lang.Resident) runs the id-literal
check at the deployed digest `Codec.Digest.ofBytes?`, so a resident sees `notDigest` before install does.
Its answer is the deployed World's, not a Sim's. (6) The plant `bytesIds` rewrites every bytes literal, so it
flips LD1 only because that fixture holds one bytes literal, the callee. That is pinned in its docstring.
**Meta-critique.** The type was easy; the boundary was the work. The tempting cut was to stop at the
type (install refuses bytes in id positions) and leave state, arguments and seeds unchecked, so that a
non-digest in state would still surface late, at `callsOf`. That would have moved the refusal without
removing it. The four boundary checks are what make (2) above true at all. Whether (a) should land is a
real fork, and it is recorded as one, not as a debt.
**Statements changed** (none weaker; vacuity read a773ed76 OK, four LOWs, handled above): Std's
member/owner/quorum specs and Receiver's now conclude `.digest m`; `Call.callData_conforms`' digest premise is
`≤ digestBytesMax`; CallLive's `BytesAt` is `DigestAt`, with a `.digest` leaf; Invoke's readState lemmas and
`invoke_never_stuck`/`law_never_stuck` take `digestOf`; `readState_go_stateSlots` gains a `digestsOk` premise,
discharged at its one consumer (`seedOf_reads`) by `readAt`'s own check. New teeth: `args_named_not_live`, `no_digest_at_args`.
**Status.** built (this commit). Re-ids every package with a method or law; re-genesis.

## LANG-39 THE BAR's ratio has an extraction tooth (2026-10-17; cv 01a14abb-aa73, the LANG-37 vacuity read; with PROTOCOL-7)
**Decision.** `Lang.Need.extractTicksTwice` (tooling) runs the deployed method run and the deployed
`Machine.extract`, then the same extraction again on the same value. Fields are not memoized, so this
re-forces every suspension extraction forced. It returns the ticks with one extraction and with two. The
rows (`Loopback.measureInvoke`) require the one-extraction count to equal `runMeasured`'s ticks, or the
count is refused by name (`extraction recount N is not the run's M`). They sum the two-extraction count as
`Invoked.extracted` and print `PLANT waste-extract ticks-per-required-step` (2.136 on THE BAR, = 47/22)
beside `PLANT waste-app` (1.818). The bar row is red by name if either plant differs from its stated value
(`Rows.Run.plantAppStated`/`plantExtractStated`: `plant NAME MOVED R≠S`) or is not above the honest ratio
(`BLIND`). This was observed: with the stated value still a placeholder, the row went red
`plant waste-extract MOVED 2.136≠0.000`.
**Why.** LANG-37's tooth (`skipStep`) and waste-app plant the METHOD RUN only. A machine that re-forced
extraction's suspensions would have raised the ratio, and nothing showed the row would see it.
**Alternatives.** A twin of `Machine.extract` with a force-twice arm: a second extractor whose honest mode
would need an equality theorem to be trusted. Refused, since running the deployed extractor twice IS the
waste, with no twin. A parameter on `Machine.extract`: a knob in deployed code (PROTOCOL-32), refused.
**Critique.** (1) The plant doubles all of extraction. It does not plant a SINGLE field forced twice, so
the row is shown to see extraction waste in bulk, not a one-field regression. Here, though, one extra
force of the smallest field (a literal, 1 tick plus its unknot) would move the printed ratio by
≥ 1/22 ≈ 0.045, well above the 0.001 resolution. (2) The honest recount is a runtime check on every run,
not a theorem. The deployed functions are the same ones, so a theorem would restate `runMeasured`'s
middle.
**Meta-critique.** Stating plant values exactly (PROTOCOL-7's condition) turned a "plant above honest"
check into one that also catches a plant that silently weakened, the same discipline as GATES-13's
immutable vectors.
**Status.** built (this commit). Nothing re-ids: tooling and rows only.

## LANG-40 The required counter is complete: `requiredOf` never refuses fuel on an admitted invoke (2026-10-17; cv 01a14aba-1281, LANG-37's critique (1))
**Decision.** `Lang/Proofs/NeedComplete.lean` (new). `need_complete`: a derivation of size `n` is what
`need` returns under any fuel `≥ n`. It is mutual with the `Sel`/`Ext` twins. `needExtract_complete`: what
extraction must force, of total size `m`, is counted under any fuel `≥ m`. It goes through
`needForce_complete` and `needUnknot_complete`; rounds suffice because every unfolding is a derivation of
size ≥ 1, by `derives_pos`. Corollary `requiredOf_total`: for every invoke `runMeasured` admits,
`requiredOf` returns a count `N < ticks`. So `required: fuel` and `required: extraction` are unreachable on
an admitted invoke, and THE BAR's ratio row can no longer read UNMEASURED there. Teeth: `need_idApp_short`
(under fuel 1 `need` finds nothing) and `need_idApp_depth` (under fuel 2 it finds the size-4 derivation).
`need`'s fuel is nesting depth, so "fuel ≥ size" is sufficient and not necessary.
**Why.** LANG-37 left the reachability half of cv 01a14a87-33b2 open. `required_lt_ticks` assumed
`requiredOf = .ok N`, so it said nothing about an invoke on which the counter gave up.
The floor keeps ONE source: `requiredOf_total` produces the count and takes `N < ticks` from
`required_lt_ticks`. Rows' break on a `requiredOf` refusal (`bar: an invoke's required count failed`) is
now provably unreachable on an admitted invoke. It stays as defence in depth and does not count as a gate
that can go red (vacuity read a773ed76).
**Alternatives.** Giving `requiredOf` unbounded fuel (a `partial def`): refused by the gates, and a count
with no bound is a hang, not a refusal. Raising its fuel to `budget * k`: unnecessary, since the budget
already suffices by the theorem.
**Critique.** (1) The bound is loose (depth vs. size), and it does not need to be tight. (2) Only
`runMeasured`-admitted invokes are covered. A faulting run has no requirement by design
(`required: a fault is not a run`).
**Meta-critique.** The completeness proof is one structural recursion per relation, the mirror of
`need_derives_all`. That was cheap once `Derives` carried sizes, which is LANG-37's shape paying off a
second time.
**Status.** built (this commit). Nothing re-ids: one new proof module.

## LANG-41 Every id a run holds came from where ids enter; `callsOf`'s `not a digest` is unreachable from checked Lang output (2026-10-17; cv 01a14acf-a188, cv 01a14af1-2132, LANG-38's critique (2) and vacuity LOW (5))
**Decision.** (1) `runMeasured`'s front half is ONE deployed function, `Lang.runSetup` (Lang/Program.lean,
returning a `RunSetup`: closure bodies and size, method label, state row, result type, state and
arguments as data, term, environment). It runs the same checks in the same order as before. `runMeasured`
runs from it, and `Lang.Need`'s copy (`setupOf`) is deleted, so the WASTE counter and the deployed run
share one front half instead of two that agree today. `Lang.Proofs.Load.runSetup_spec` states what it admits.
(2) `Lang/Proofs/Provenance.lean`. `ValLits P v`: every digest a value holds, and every id literal and
value of each closure, suspension and knot inside it, satisfies `P`. One step keeps it (`step_lits`,
for any `P`, since no primitive makes a digest), and so do `run_lits`, `force_lits` and `extract_lits`.
At the deployed run, `runSetup_sources` (THE PROVENANCE THEOREM): every digest of the extracted result
is the request's `agent`, `principal` or `self`, a digest of the arguments, a digest of the state the
World held, or an id literal of the loaded closure (`RunSource`). These are three origins: the World (state
and the request's ids), the request's fields (arguments) and literals the World accepted. `runSetup_accepted`:
each source was accepted where it entered (the arguments and state by `runSetup`'s `digestOf` checks, the
literals by `checkLits` at every load, which `load_lits` carries through relocation), and the request's
ids are accepted under the World law `hdig : ∀ x, (digestOf (bytesOf x)).isSome`.
`runMeasured_past_extraction`: under `hdig`, once the method ran and its result extracted, the result is a
calls row and a state record, `callsOf` reads the calls, and the deployed run refuses only for state with
no bytes. So `calls: cI FIELD: not a digest` is unreachable from checked Lang output.
(3) Teeth. `catTerm_bytes`/`catTerm_forged`: `Need.forgeStep` is the deployed step with a `cat` that
returns a digest, and it makes an id from a literal-free term in an empty environment, which
`run_lits` forbids for the deployed step. Journey LD5: `Caller` (no state, no arguments) calls the
signing member as an object, and the honest run is refused `wrongKind` by the kernel, so `callsOf`
read the call. PLANT unlawful-codec: the same run under a World whose `digestOf` refuses the founder's
own id (`hdig` false at one point) is refused by `callsOf`, `calls: c0 obj: not a digest`.
**Why.** LANG-38 claimed that no primitive makes a digest and that the boundary checks catch every
non-digest first. That was prose. Now it is a theorem with the sources named. cv 2132 asked for a plant
reaching the refusal with "boundary off, callsOf honest". A split `digestOf` (boundary vs callsOf) would
be a knob in deployed admission (PROTOCOL-32's rule), so it is not built. The theorem shows the only
input that reaches `callsOf` unchecked is the request's ids, so the plant breaks exactly that input's
premise, through `Lang.program`'s existing `digestOf` parameter. No new switch anywhere.
ROOT's default (ii), a Kernel.Sim arm handing the receiver a hand-built `Body` with a non-digest where an
id belongs, is unrepresentable. `Body D`'s ids are the World's `D` (a `UInt64` in the Sim, CODEC's `Digest`
deployed), so no Body holds a non-digest, and the refusal lives on `Data`, in Lang. No Kernel/Sim change
was made and none was needed from KERNEL-12.
**Alternatives.** (a) A fourth run-time check (`reqOk` asks `digestOf` about agent/principal/self). That
would remove `hdig`, and then `callsOf`'s refusal would be dead under every World, with no plant possible.
It costs three decodes per run to re-verify the World's own codec law, which the Sim proves
(`sim_digest_roundtrip`) and CODEC's digest codec states. Not taken, but it is the move if a World's
codec ever stops being lawful by theorem. (b) Proving provenance only for `P := accepted`. Rejected: the
sources theorem is strictly more informative, and acceptance is its corollary.
**Critique.** (1) `hdig` is a premise on the World, not a check. A World whose `bytesOf` and `digestOf`
disagree gets a refusal at `callsOf` (by name, the plant), not at the request. It is discharged for
the Sim (`sim_hdig`, `runMeasured_past_extraction_sim`). It is NOT yet a law of the kernel's `Ctx`
(vacuity read a773ed76, LOW): `Ctx.digestOf` carries no round-trip law, so every other World discharges
it by hand. The owed item is a KERNEL field `∀ x, X.digestOf (X.env.bytes x) = some x` on the lawful
context (cv task filed, asked of KERNEL). (2) Provenance is stated for
method runs. Laws (`judgeOne`) return verdicts with no ids, so nothing consumes their digests, and the same
`run_lits` covers them if that changes. (3) `RunSource` does not say WHICH literal or field: provenance up
to membership, not up to position.
**Meta-critique.** The refactor (1) was the price of a clean statement. The old twin `setupOf` made every
deployed-run theorem restate the front half, and deleting it shortened four proofs. The machine
invariant took one pass with no new machinery (`ValLits` is an ordinary inductive), which says LANG-38's
"no primitive makes a digest" was cheap to make true and was only ever unstated.
**Status.** built (this commit). Nothing re-ids: no package, wire or Store shape changed.

## LANG-42 The one law runner is never stuck on a loaded package's law: extraction makes progress (2026-10-17; LANG-5/6 leftover "runLaw extraction never stuck")
**Decision.** `Lang/Proofs/LawRun.lean` (new). `extract_progress` (mutual with `extractArm_progress` and
`extractRow_progress`, via `force_progress` and `unknot_progress`): extracting a value typed at a data
type fails, if at all, by a named fault of a forced suspension, never `stuck`. `verdict_shape`: data
conforming to `verdictTy` is `ok {}` or `refused bytes`. `runLaw_never_stuck`: on a loaded package's law,
on states read at its row and a request in bounds, `runLaw` never returns `.error .stuck`. Its third arm
("a value of another shape") is unreachable, and so is a `stuck` extraction. Law.lean's docstring, which
said "not yet a theorem", now cites it. Teeth: `extract_fn_stuck` (a function type is not data) and
`runLaw_nat_stuck` (a closed law returning a number IS stuck, so the closure typing is what the theorem uses).
**Why.** `law_never_stuck` covered only the machine run inside `runLaw`. A receiver that denies a law
`ℓ: stuck` would mean a checked law reached a type error. It is now provably impossible, so that
denial text is reserved for a broken checker.
**Alternatives.** Folding progress into `extract_conforms` as a sum type: one statement, but every
caller of `extract_conforms` would have to destructure it. Kept separate.
**Critique.** (1) Faults remain possible (ticks under `lawTicks`, stack, arithmetic); this says only that
they are named. (2) The method run's extraction (`runMeasured`) gets the same corollary for free from
`extract_progress`. It is not stated, because `runMeasured` already reports any extraction fault by name.
**Meta-critique.** The proof is the error-side mirror of `extract_conforms`, the same recursion with the
same lemmas. That it was "nearly a corollary" for four predecessors and was never written is the cost of
an open list item that looks done.
**Status.** built (this commit). Nothing re-ids: one new proof module and a docstring.

## LANG-43 `Std.stepTo` refuses an ambiguous edge: every declared edge is the one its method takes (2026-10-17; LANG-5/6 leftover "duplicate machine edges", vacuity note)
**Decision.** `StdRefusal.ambiguousEdge`. `stepTo` refuses when two resolved edges leave one state by one
method index. `Lang.Proofs.Std.stepTo_ok` and `stepTo_takes_every_edge`: for a method `stepTo`
generates, every declared edge `(x, i, y)` of its index is the edge its target lookup finds from `x`
(`find_edge_of_nodup`, stated over `stepTarget`, the lookup `stepLaw` uses). Teeth (StdTeeth): `stepTo_refuses_ambiguous_edge`, and `first_edge_shadows` (the
plant: without the check the lookup takes the first edge and the second declared edge is never taken).
**Why.** `machineLaw` admits a move along ANY declared edge, and `stepLaw` takes the FIRST. With two edges
`(a, m, b)`, `(a, m, c)`, the law admits `a → c` by `m`, a move no generated method makes. The second
edge was silently dead and the law was looser than the program. The check sits in `stepTo`, not
`machine`: a hand-written method may choose between two declared edges, and the law should then admit
both, so `machine` stays as it was.
**Alternatives.** Refusing in `machine`: that would forbid legitimate nondeterministic machines whose
methods are hand-written. Making `stepLaw` take the last edge, or all edges: it would still be
deterministic and would hide the same dead edge.
**Critique.** (1) A package that pairs `machine` with hand-written methods is still not checked for
law/method agreement; only generated methods are. (2) An exact duplicate edge is refused under the same
name, though it was harmless. (3) The theorem is lookup-level (`stepTarget es i x = y`, the lookup `stepLaw` uses, factored out by name per the vacuity read), not run-level. The run-level fact is owed as cv 01a14b36-6da2-7a12-a70c-8b9837b63661.
**Meta-critique.** It is a refusal added to a generator, a strengthening, so it is not a pause item.
Hosting's lifecycle machine (`Hosting/Package.lean`) is deterministic, so its package bytes are unchanged.
**Status.** built (this commit). Nothing re-ids: valid inputs produce the same terms.

## LANG-44 Relations: keyed, bounded rows under an object, in a third instance of the one trie; inserts at distinct keys commute because their footprints are disjoint, never because a pin is relaxed (2026-10-18; PROPOSED, LANG-13 with a KERNEL half for KERNEL-13 to co-sign; Ember's delvetalk question; DELVETALK-LEARNINGS §4.2; LANG-1's critique)
**Ember's question.** "didn't we have some learnings from delvetalk that were to apply? especially about its
relation-based state model? I feel like that is maybe a genuinely different constructional alternative to this
blockchain replay stuff (maybe it isn't)."

**(a) The two models, precisely.**
- *delvetalk* (dt = `~/dev/delvetalk2`). An object is `{maker, pin, law, version, behaviour, state}`; essential state
  is scalar fields plus RELATIONS, "derived state is a pure Bend function and is never written" (dt:docs/FOUNDATION.md
  §8 principles, §9). A relation is `Relation<T>` declared once per package as `{field, key, limit, retain?}`; the
  host keeps it canonical after every write: rows sorted by the canonical bytes of the key projection, no key twice,
  at most `limit` (default 4,096), the first rows in key order dropped past it (§9 "Canonical form"; invariant 10).
  Edits are data: `insert | upsert | retract` beside `keep | add | append` (§9 "Edits"). A turn records the roots
  it read (object version, a field, or per-cell: the rows forced, the key-order spans walked, the gaps a lookup fell
  in) and commits "iff every root is current or every edit of a moved root commutes" (invariant 2): `keep`, `add`,
  `append`, `insert` re-apply on the current state and are re-judged there (an insert meeting another row of its
  key is `keyTaken`, binding); `upsert`/`retract` commit when no admitted write since the read touched the key
  (`keysChangedSince`, a per-object index of height to keys); otherwise `staleRoot`, transient, re-run once. "Two
  agents raining on one bell never collide" (§9 "Inserts commute; rows rebase"; `test_commute`,
  dt:tests/README.md "Host"). The rule is `#guard`ed, not proved (§1 "Not proved"). Laws over relations are
  `insertOnly(F)`, counts and column membership (§9), and `insertOnly` is judged over BOTH sides' rows
  (dt:docs/KERNEL-HANDOFF.md §16 item 17: ~12 ms per 2,048-row write; item 3: a Bend law reads a whole state per
  write). The journal is one entry per turn, admitted or refused, with a receipt; "Replay re-judges recorded edits
  and never re-runs resident Bend" (dt:README.md:195–211; dt:docs/AUTHORING.md opening). One Lean process is the
  only writer, so its method runs are TRUSTED: replay re-judges the laws over the recorded edits and does not
  check that the edits are what the method computes. A bell is a RECORD layer with one relation of 768 rains
  keyed `{author, at, n}` (dt:world/bodies/bell.obend:16–47), and its rain writes `lines: insert {...}` AND
  `next: add 1n` (bell.obend:52): a row plus a commuting counter.
- *nanodregg* (nd = hbox main). A cell is `{kind, discipline, slots}`, a bounded canonical map `Nat → bytes`
  (Kernel/Cell.lean); an object's state is a record whose field `i` is the slot `stateBase + i` (LANG-11). The
  World is ONE trie of cells and nullifiers (KERNEL-30) plus the journal as a second instance of the trie type
  (KERNEL-41 (a′)); the head link commits both roots. A Turn names each cell once, `Touch {cell, seen, act}`,
  `Act := keep | write ops | retire`; `touchCheck` refuses `stale` unless `pinOf (current cell) = seen` (KERNEL-11,
  Kernel/World.lean `touchCheck`). The pin is the SIGNER's: `Unsigned.pins` is signed, and `sealTurn` makes the
  touches from it (Kernel/Receive/Call.lean `touchesOf`). The receiver derives on the Host's CURRENT World
  (`Receive.submit`: `receive X w c`, then `World.admit`), so a method always runs on current state; the only thing
  that makes the second of two concurrent writers fail is that its signer pinned a digest that moved. Blind writes
  are gone (KERNEL-11 critique: "two writers of one hot cell conflict"). The core has no list or recursive type
  (LANG-1 critique: "a wiki page's list of links has no type. That is the first language extension a real app will
  demand"). Replay has TWO forms: `World.fold` re-applies recorded ops (re-runs nothing), and the follower's
  `audit` (Kernel/Receive/Audit.lean) re-derives every Turn from its signed event, i.e. RE-RUNS the receivers,
  methods and laws included, and requires the same Turn. Correction to the reading that both systems "never re-run
  resident code": nanodregg's auditing follower does, and that is the check on an untrusted writer (there is no
  proof system: admission is checked by re-execution).

**(b) An alternative to replay, or a layer?** Not an alternative to replay. Both systems keep a totally ordered
journal of one entry per turn, both rebuild state by folding it from a checkpoint, and delvetalk even carries a town
across editions by rebuilding every object (dt:README.md:213–218). What is genuinely different is (1) the unit of
state (a keyed row vs a whole cell) and (2) the commit rule (a moved root admitted when the edits commute vs every
pin exact). Those are a concurrency design, orthogonal to replay. The one reading under which relations ARE a
different construction is the CRDT one: an insert-only relation is a grow-only set, and a set of facts that commute
needs no total order, so replicas could converge by union and an auditor could check each fact independently of
order. That holds only for the commuting fragment; nanodregg's value discipline, authority, limits, escrow phases
and once-keys do not commute, so the World keeps its total order. Relations are therefore a LAYER over the pinned
World. But not in the shape "an `insert` act that commutes against a MOVED pin" (DELVETALK §4.2's phrasing): that
shape relaxes a pin, and the right shape relaxes nothing. In nanodregg the Host already re-derives on current state
(the rebase delvetalk has to perform is free here). The only obstacle to "two rains on one bell both land" is pin
GRANULARITY: both rains pin the whole bell cell, and the first one moves it. Give rows their own leaves, keyed under
the object, and a rain that inserts at its own key, pins the bell's cell with `keep` and pins no other row, has a
footprint disjoint from every other rain's. Both land, in either order, to the same World, and `stale_refused` keeps
its exact statement for every pin, a row pin included. Commutation becomes a THEOREM about disjoint footprints
(`admit_comm`, below), not an admission rule, so the delvetalk rule that was only `#guard`ed arrives proved.

**Decision (proposed).**
*LANG half.*
1. A package declares its relations beside its state: `Package.rels : List (Label × RelDecl)`, at most
   `relsMax = 8`, `RelDecl := {key : Ty, val : Ty, limit : Nat, retract : Bool}`. A relation is a PLACE, never a
   value: no term has a relation type, so no method holds a whole relation (law 5 by construction).
2. Keys are FIXED-WIDTH data: `nat`, `bool`, `digest`, enum sums (all arms `rec {}`), and records of those; `bytes`,
   functions and payload-carrying sums are refused at install by name (`relKey`). Key bytes are the ordinary data
   encoding with naturals BIG-ENDIAN (a Lang data flag day: every nat in state goes u64 BE, so one encoding is
   order-preserving; CODEC supplies `u64be` in the one family). So the trie's byte order IS the key order, with
   records ordered by their labels in canonical (ascending) order: delvetalk's "shorter-column surprise" becomes a
   "label-order rule" (`{a_at, b_author}` sorts by `at` first), stated, not surprising.
3. Reads are DATA, like calls (LANG-21/23/33): a method declares `rs : List (Label × Nat)`, how many rows of each
   relation it reads (≤ `readsMax`), and receives `reads : rec {ℓ : rec {r0..r(k-1) : rec {key : K, val : optTy V}}}`,
   filled by the receiver from the call's ROW PINS in pin order (absent → `none`). A method reads exactly the rows
   its signer pinned: there is no lookup oracle in the machine, so Eval/BigStep/Need are untouched.
4. Writes are DATA: a method declares `es ≤ editsMax` edit slots and returns
   `rec {calls, edits : rec {e0..e(m-1) : optTy editTy}, state}`, `editTy = sum {insert : rec {key, rel, val}, upsert
   : …, retract : rec {key, rel}}` (one sum over the package's relations, by label).
   `methodTy S A ks rs es = fn S (fn A (fn reqTy (fn readsTy (rec {calls, edits, state})))))`.
5. Row GUARDS judge each edit, O(edits), never a relation: `RelDecl.guard : Label` names a body field of type
   `fn S (fn reqTy (fn editTy verdictTy))` (the object's state before, the request, one edit). The bell's guard is
   "the row's author is `req.agent`". `retract = false` makes the relation insert-only by declaration (the kernel
   refuses a retract by name; delvetalk's `insertOnly(F)` without a judge reading both sides' rows, which is §16 item
   17's fix by construction). The old/new law type is UNCHANGED, so the 85 law theorems keep their statements
   (Std, StdTeeth, Receiver, LawRun, StdFits).

*KERNEL half (for KERNEL-13 to co-sign; the KERNEL-41 (a′) pattern).*
6. `World.rows : Trie.T D RowKey RowLeaf D`, a THIRD instance of the one trie type (cells, journal, rows); the head
   link commits three roots: `headLink E prev td root′ jroot′ rroot′`. `RowKey = parent : D, rel : u8, k : bytes`
   with bits `bytes parent ‖ rel ‖ tag ‖ k` (tag 0 = the relation's HEAD, tag 1 = a row), depth
   `256 + 16 + 8·keyBytesMax`. Width is fixed per relation (the head records it), so the key set is prefix-free
   with no World invariant: rows of one relation share a prefix, so a relation is a SUBTREE: ordered, enumerable,
   and authenticated by the rows root (a phone verifies a page of rains against one head).
7. `RowLeaf := head (count limit width : Nat) | row (val : ByteArray)`. The head is written ONLY by the kernel:
   born with the parent (the create receiver emits one per `RelDecl`), `count` maintained by admission, `limit`
   checked at admission on the CURRENT count (`relationFull`, binding like `keyTaken`, never stale).
8. `Turn.rows : List (RowTouch D)`, `RowTouch := {key : RowKey D, seen : Option D, act : RowAct}`,
   `RowAct := keep | insert v | upsert v | retract`. `seen = some d` is an exact pin (the row's leaf digest or the
   absent pin), refused `stale` when it moved, exactly as a cell pin. `seen = none` is allowed ONLY for `insert`, and
   then the key must be absent at admission (`keyTaken`): an insert is a BIRTH of a row, unpinned like a cell birth
   (KERNEL-11: a born id is never touched). `upsert`/`retract` must pin (no blind write). Every row's parent must be
   a cell the turn touches (`rowParentUnpinned`), live (`orphanRow`), so a turn still changes only what hangs under
   cells it observed.
9. Retract REMOVES the leaf with the canonical collapse (`Trie.retainAt` on the row's path, KERNEL-41 step 1), so a
   relation truly forgets and its storage is bounded by `limit`. The collapse premise (`RowsCanon`) lands on the
   rows trie's readers only, as `JournalCanon` did (KERNEL-41 (a′) (5)); no cell reader gains anything. A parent
   with a non-empty relation cannot retire (`rowsRemain`).
10. Storage: a row's bytes are growth (`Turn.growth`), charged and conserved like a cell's (KERNEL-12/15/19); a
    retract credits them back.
11. The new theorem that is the point: `admit_comm`: two turns whose footprints are disjoint (no cell either writes is
    touched by the other; no row key either writes is pinned or written by the other; their inserts at distinct keys)
    admitted in either order from `w` reach Worlds with equal cells and rows tries (heights, journals and chains
    differ by construction). Tooth: the bell row below, and a plant that makes the rain pin the relation's head (the
    whole relation) turns the second rain `stale`.

**(c) The concurrency gain and its exact cost (premises, not only hashes).** Gain: N writers inserting distinct
keys under one object all land, without re-signing, and the result does not depend on their order (`admit_comm`).
Hashes: one row path plus the head's (they share the `parent ‖ rel` prefix) per insert, ≈ 2 × 13.7 at the journal's
measured steady state (`admit hashes-per-journal-entry`), pinned as `admit hashes-per-row-insert` on landing; one
more 32-byte block per turn in the link. Premises and statements, enumerated by grep over theorem STATEMENTS on
main 189c201 (a statement mentioning the link, the weight, the bounds or Carried):
- Statement changes, no new premise (the link gains a root, Carried gains rows): Kernel/Proofs Cells
  `headLink_roots`, `head_roots`, `head_root`, `head_read_sound`, `head_absent_sound`; Fold `chainOf_concat`,
  `chainNext_inj`, `chain_binds`, `fold_chain`; Admit `admit_chain`; JournalHead (7: `journal_inclusion_sound` …
  `journal_prove_absent`); RootedDeployed (8 `deployed_head_*`); RootedFold `RootedFold.chain`; Host Base
  `Record.step_origin`, `Record.foldlM_journalOk`, Serve `step_submit`; Carry (16), CarryRooted (2), Codec Carried
  (12), Host Carry (5), Host Deployed (4): Carried's listing gains the rows listing. About 66 statements.
- Weight: `admit_world_weight`, `fold_world_weight`, `admit_conserves`, `fold_conserves`, `touches_weight` and the
  rest of Kernel/Proofs/Weight (14 statements) and Codec/Proofs/Kernel's 6 weight statements gain the rows term;
  `checkBounds` statements (Admit 2, Fold 4, Codec Kernel 2) gain `rowsMax`.
- NEW premise `RowsCanon` (Trie.Canon at the rows root) on rows readers only; genesis gives it, insert and
  `retainAt` keep it; reached corollaries premise-free (as `reach_journalOk`).
- NO premise on any cell reader: `admit_frame`, `rom_keep`, `admit_rom`, `admit_nullifiers`, `admit_live`, the Value
  and Ledger sums, Rooted stay as they are, because rows are not slots of the cell trie (the reason (a) of KERNEL-41
  was rejected applies with full force to rows-as-cell-trie-slots: a removing retract would collapse across kinds).
- `stale_refused`/`admit_pins` extended to row pins with the SAME conclusion (a moved pin refuses); not weakened.
- Codec: Turn codec (rows list), World and Carried codecs (rows listing rebuilt by `build`, canonicity `=`), Package
  (`rels`), data nat → u64 BE; vectors re-pinned (CODEC).
- Lang, enumerated the same way (Lang/Proofs, 896 theorems): method-shape statements (24: Call 5, CallLive 3, Invoke
  3, Load 4, Need 4, NeedComplete 1, Provenance 4) restate over the new `methodTy`; package-shape statements (69,
  mostly PrintWire 14, Invoke 11, Load 10) restate over `Package.rels`; law statements (85) UNCHANGED because guards
  are a separate field type, not a new law argument. New: `rows_of_pins` (the reads row is exactly the pinned rows),
  `editsOf` round trip and liveness twins of `callsOf`'s, `guard_never_stuck` (a twin of `law_never_stuck`'s
  statement over `runLaw`).

**(d) Journal, checkpoint, replay.** The journal's unit stays the Turn: delvetalk's is one entry per turn too, and
commutation here needs no per-edit entries because it comes from disjoint footprints. A Turn's rows are its edits,
so a turn appending to a collection logs O(row), where today the only way to keep a collection is one bytes field
rewritten whole per append (O(n) per append, O(n²) of log over a relation's life; and every such write conflicts).
A sealed base holds the rows trie as an ascending listing (like the journal), bounded by Σ limits. Ember's "the amount
of replay is too damn high": what already bounds it is the sealed base (open reads base + one index entry + tail,
`open bytes-read-per-record` 1.007, HOST-33), the base/4 seal cadence (HOST-14), the journal window (KERNEL-33), thin
consent `adopt HEIGHT DIGEST` (PROTOCOL-14/18/37) and carry, which keeps state and never history (law 1). What is
still unbounded: an AUDITING follower from genesis re-derives every Turn, methods included: O(history) re-execution,
and the price of not trusting the writer. delvetalk's replay is cheaper because its host is trusted to run methods.
A "laws-only audit" (re-judge authority and laws over recorded ops, never re-run methods) would cut it, and it
WEAKENS a check (the writer could apply any ops the laws admit): a pause item, recorded as a fork for ROOT, not
proposed. Relations shrink replay bytes for collection-shaped objects and remove conflict retries; they do not change
the O(history) audit.

**(e) Bounded.** Per relation: fixed key width ≤ `keyBytesMax` (64), value ≤ `valueBytesMax`, `limit ≤
Bounds.rowsPerRelationMax` (4,096, delvetalk's), checked at admission on the current head count. Per method:
`readsMax`, `editsMax` (8 each, like `callsMax`). Per turn: `rowsMax` row touches. Reads and writes are O(touched
rows) by construction: a method sees only pinned rows, a guard sees one edit, the kernel walks one path per row and
one per head. Enumeration (a card listing the latest rains) is a READ off the request path: a subtree walk with a range
proof, O(rows returned + depth), served by HOST/PROTOCOL.

**(f) Rejected shapes.**
- *An unbounded list (μ-types or a built-in `list`) in the core.* State would be a whole list per field: every
  append re-encodes and rewrites it (O(n) per write, O(n²) log), two writers conflict on the field, a law reads both
  sides whole (delvetalk's §16 item 17), and the demand machine's budget theorems must reach a recursive fold.
- *Relations as a store beside the World* (a table per object, SQLite, a host index): two maps over one key space,
  not committed by the head; a second admission path; law 1.
- *Rows as slots of the parent cell, with an `insert` act checked against a pin that masks the relation* (the literal
  §4.2 shape): it relaxes a pin (a weakened check); `pinOf` and the leaf digest hash the whole cell, so every insert
  is O(relation) and a relation's life O(n²); slot keys are `Nat < 2^32`, so byte keys and their order do not fit; the
  cell's 1024-slot bound caps it.
- *Rows as ordinary cells at hashed ids* `H(domRow, parent ‖ rel ‖ key)` (keyed ids like LEDGER's accounts): the
  cheapest (no trie change), and wrong: hashed ids scatter a relation, so it cannot be enumerated or range-proved
  without an index beside the World (law 1), there is no count to bound it, and a retired row tombstones its key
  forever.
- *Rows as a third slot kind of the cell trie*: ordered and enumerable, but a removing retract collapses nodes across
  kinds, which is exactly KERNEL-41 (a)'s rejected premise spread over ~150 cell theorems; with tombstones instead,
  a relation never forgets.
- *delvetalk's commuting `keep` (a last-writer-wins scalar set re-applied on current state)*: a blind write; KERNEL-11
  removed them on purpose.

**Open, not decided here: commuting COUNTERS.** delvetalk's `add` and Mini's `EditNat.add` (Mini world/activity/
Tally.obend: "a concurrent write … is kept, never overwritten") commute too, and the bell itself bumps `next: add 1n`.
Rows do not give them. A count of a relation is the head's `count` (derived, never written, readable by pinning the
head, which then conflicts by design). A SUM with a cap (Mini's CappedTally: `law cap: new.total <= 1000`) is not:
the honest options are an `Act.add` on a declared counter slot checked at admission on the current value (a pin
that excludes that slot: a weakened pin, so a pause item) or a per-contribution relation whose head carries a
declared aggregate. The deciding experiment (LANG-45, CappedTally ported by hand) measures this need; ROOT rules
after it.

**Critique.** (1) It is large: a kernel day of KERNEL-41's size plus a Lang day of LANG-33's, and both halves must
land before anything uses rows (the kernel half alone is inert unless the data-object `write` receiver can emit
rows, which it should, so the kernel half is live and testable on its own). (2) Reads are declared by the signer, so
a method that must "find a free key" cannot search; it must be told which key to check (the client plans: PROTOCOL-11's
`plan` already re-derives). (3) Fixed-width keys exclude text keys: a wiki page keyed by title must key by the
title's digest and loses alphabetical order. (4) `count` is the only aggregate; a law over "the rows as a whole" is
not expressible, by design. (5) Range reads inside a method (a span pin, delvetalk's `spans`) are not in v0. (6) Data
nat → big-endian moves every state byte: free here (re-genesis), but it is a second Lang data flag day after
LANG-38. (7) Creator-added laws cannot constrain rows (guards are the package's, in ROM).
**Meta-critique.** I came to this with ROOT's and the reader's phrase, "an insert that commutes against a moved pin",
and the pull was to build exactly that, because it is the delvetalk rule. The independent test was to ask what the pin
protects and when the second rain actually fails: in nanodregg the Host already re-runs the method on current state,
so the conflict is only the pin's granularity, and a finer footprint makes commutation a consequence instead of a
rule that relaxes a check. The rows-trie shape is the KERNEL-41 (a′) shape, which I like because it was just ruled;
that is familiarity, and the test it must pass is the premise enumeration above (no cell reader gains a premise),
not the precedent. I have not measured anything: every hash figure here is an estimate from the journal's row.
**Flag day.** Turn (rows), World and Carried (rows trie), the head link (three roots), Package (`rels`), `methodTy`
(reads, edits), data nat → u64 BE: every chain, every package id and every state byte change; every Store
re-geneses; an old base refuses `shapeMismatch`, an old package `malformedCell`. Re-emits: world/grain/Lifecycle and
world/hosting/Allowance (HOSTING), world/escrow/Escrow (LEDGER, `ledger-sim --write-text`), THE BAR's counter
(PROTOCOL), codec vectors (CODEC); new waste rows `admit hashes-per-row-insert`, `admit hashes-per-row-retract`.
**Acceptance row (lang:, after both halves).** A bell package (`rains : rel {at : nat, author : digest} → bytes,
limit 768, retract false`, guard author = agent): two members' rains pinned at the same bell digest both admitted,
in both orders to equal cells and rows roots; the same key twice `keyTaken`; the 769th `relationFull`; a rain with
another's author refused by the guard; a retract refused by declaration; plant: pinning the head on insert makes the
second rain `stale`.
Status: SUPERSEDED PROPOSAL: relations were built in LANG-49 and refined later; this section retains the proposed design.

## LANG-45 The deciding experiment: Mini's CappedTally ported by hand to nano's core; what it needs first is a capped commuting COUNTER, which LANG-44's rows give once the head carries a declared sum (2026-10-18; NANO-VS-MINI §5, ROOT's order on LANG-44; journey rows LT0–LT8)
**What was ported.** Mini `tests/objective-native/CappedTally.obend` at 2c27b08b is the smallest Mini program with
state, laws and two members. It is a tally the owner starts with an initial total and a decider. The decider answers
with amounts within a patience of 4 heights, and each answer is an `add` delta the kernel applies to the current view
("a concurrent write … is kept, never overwritten"). Two enforced laws hold: `cap: new.total <= 1000` and
`grows: monotone(total)`. The port is `Lang.Journey.cappedTallyText`, the s-expression a resident writes, read by
`Lang.Read` and run through the real receivers:
- The decider answers by invoking `reply {amount}` through the owner's grant (KERNEL-25).
- The patience is a `closes` height. The law `decider` holds the signer's window to it (`req.validUntil ≤ closes`)
  and refuses any agent but the decider.
- `cap` and `grows` are ordinary laws.
Rows:
- LT2a: a start at 1001 is refused `cap`.
- LT4: B replies 600 and is admitted.
- LT5: 600 + 500 is refused `cap`. Plant skip-judge: LT5 is then admitted.
- LT6: the owner's reply is refused by `decider`.
- LT7: two answers signed over one view. The first is admitted and the second is `stale`. Mini keeps both.
- LT8: a tally closing before the answer's window ends refuses it `closed`.
**Measured** (deterministic counts, lang-journey on hbox at 189c201 + this row):
| | Mini (.obend) | nano (core text) |
|---|---|---|
| lines | 71 (15 comment, 2 law lines) | 34 |
| characters | 2506 (1269 without comments) | 3903 |
| package bytes | (front-end artifact, not compared) | 2797 |
| required steps / machine ticks of one `reply` | (call-by-need, not counted) | 33 / 47 (THE BAR's counter, `requiredOf` / `runMeasured`) |
- Where nano's characters go: the state record is written 15 times (47 chars each), the request type 7 times
  (interpolated from `Print.tyText reqTy`; a resident pastes it), and the verdict sum 13 times. About 2,200 of the
  3,903 characters are repeated types: the authoring-surface need (DELVETALK §4.1), measured. Type aliases alone would
  bring the text under Mini's.
- Where Mini's lines go: 13 records and sums of activity plumbing (`Plan`, `Await`, `Source`, `Outcome`, `Resumed`,
  `Step`, `View`, `EditNat`, `Write`, `Start`, `Ask`, `At`, `Reply`) and one recursive `ask`. With no activities,
  nano needs none of them; the method is three lines.
- Nothing was exponential: no record field reads `self` twice (LANG-2's case did not arise).
**What could not be expressed, and what replaced it.**
1. *Activities* (`perform`/`await`, resumed with a view). Replaced by the decider invoking a method through a grant.
   This is cut on purpose (LANG-6), and the port lost nothing observable but the activity's return value. Mini's
   `tally` returns the final total; nano's caller reads the state.
2. *`timedOut`*: Mini's kernel ends the tally at the deadline with nobody signing. In nano no turn happens without
   a signer, so "closed" is a law refusal of late answers, not an event (DELVETALK §4.6's point, met again).
3. *The `add` delta*, the one real loss. Two answers over one view do not both land (LT7: total 610, Mini's 630).
   This is the commuting counter LANG-44 left open, and it is THIS program's first need, ahead of rows.
4. `grows` is implied by `reply` (the amount is a nat), so as a law it bites only on a non-method write. It is kept
   for fidelity; no row reaches it.
**The answer to LANG-44's open question (counters).** Rows alone do not give a capped counter: a relation's head
carries a count, but `cap` bounds a SUM. Two ways to give it:
- (i) An `Act.add` on a declared counter slot, admitted against a pin that excludes that slot. This WEAKENS a pin, so
  it is a pause item.
- (ii) LANG-44 as approved, plus ONE head field. A relation may declare a nat column `sum` and a `cap`. The row leaf
  carries that column's value where the kernel can read it, the head keeps `sum` beside `count`, and an insert is
  refused `relationCapped` when the current `sum + v > cap`. The tally becomes an insert-only relation of answers,
  keyed `{agent, nonce}`. Its total is the head's sum, `grows` holds by construction (insert-only), and two answers
  are two unpinned row births with disjoint footprints, so both land (`admit_comm` covers it unchanged).
I recommend (ii). It weakens nothing, it is O(touched) (one head update per insert), and it is one field more in the
kernel half, not a second commutation rule. Mini's other commuting edit, `set` (`EditNat.set`), is the blind write
KERNEL-11 removed, and it stays removed.
**Critique.** (1) One program is one sample. It is the smallest Mini program with a law, and the larger ones are
list-shaped (`world/story/CoAuthor.obend` keeps `Proposals`, `Ballots` and `Chapters` as recursive sums: three
relations), so "the counter is the first need" holds for this program, not for Mini. (2) The port moved the
decider check into a law, where Mini had it in the await's named subject. A resident can now remove it by relaw
unless the law freezes the laws. (3) Characters are a proxy for authoring cost; a resident pastes the request type,
it does not type it. (4) The required/ticks figure counts one `reply` on a small record; it is not a BAR
measurement. (5) A key `{agent, nonce}` makes the signer choose a nonce. A reused one is `keyTaken`, which binds,
so a client must draw nonces fresh.
**Meta-critique.** I chose the program that the counter question would decide, and it decided for the counter. A
list-shaped program would have decided for rows. The independent check is that LANG-44's rows are the mechanism in
both cases ((ii) is a head field, not a second design). Still, the order of building should follow the next
program ported, not this one.
**Status.** Rows LT0–LT8 built (lang-journey GREEN, including the skip-judge plant). (ii) goes to ROOT as an
amendment to LANG-44's kernel half, and KERNEL-13 is told.

## LANG-46 The digest round trip is a law of the `Ctx`, not a free premise: `Receive.Ctx.Lawful` (2026-10-18; cv 01a14b28-7029, LANG-41's owed item; agreed by KERNEL-12 and KERNEL-13)
**Decision.** Kernel/Proofs/Lawful.lean adds `Receive.Ctx.Lawful X` with one field,
`digestOf_bytes : ∀ x, X.digestOf (X.env.bytes x) = some x`: the receive layer's one assumption about a `Ctx`
beyond its `Env`. It is discharged with no premise in two places. At the deployed codec it is
`Receive.deployed_ctx_lawful` (any program, from `Codec.Deployed.digestOf_bytes`). At the Sim it is
`Lang.sim_ctx_lawful` (any program, from `sim_digest_roundtrip`). Its refutation tooth is `sim_drop_not_lawful`: the
Sim `Ctx` with a decoder that drops the first byte is not lawful (id 0, `decide`). Provenance's `runSetup_accepted`
and `runMeasured_past_extraction` now take `hX : X.Lawful`, and the old `hdig` forms are private lemmas. The
vacuity read found a HIGH: the law speaks of the `Ctx`'s decoder, while `Lang.program` carries its own, and LD5's
plant changes only the program's, so LD5 was no tooth of `hX`. That gave
`program_run_past_extraction (hX) (hp : X.program = Lang.program X.env.bytes X.digestOf)`, stated over
`X.program.run`, the run the receivers make. `deployed_program_own_codec` (rfl) meets `hp` at the deployed `Ctx`.
Journey LD5 (PLANT unlawful-codec) breaks `hp`, and `sim_drop_not_lawful` breaks the law.
**Alternatives.** (a) A field of `Env.Lawful`: impossible, since `Env` has no decoder. (b) Bundle `Env.Lawful` into
`Ctx.Lawful`: the Sim's `Env` has no lawfulness proof, so the Sim discharge would gain a premise (KERNEL-12's
condition forbids it). (c) Make `Ctx.program` derived from the codec: that is a kernel shape change for a Lang
fact, and the receivers' `Program` is abstract on purpose (law 4).
**Critique.** `hp` is a structural premise that the deployed `Ctx` meets by construction. Nothing stops a future
`Ctx` from pairing a lawful decoder with a program over another one; that is what LD5 does, on purpose. The tooth of
the law is a constructed `Ctx` that no run uses.
**Meta-critique.** I first restated the theorems over the law and called the condition met. The reviewer saw that
the journey's own tooth had silently stopped being one: a premise moved and the plant did not follow it. That is
the failure "A FALSIFIER THAT STOPPED FALSIFYING" names, caught before landing.
**Status.** built (this commit). Nothing re-ids.

## LANG-47 The list-shaped sample: Mini's CoAuthor ported by hand; three relations are its first need, and its seal needs a RANGE read, which LANG-44 v0 does not have (2026-10-18; ROOT's order after LANG-45; journey rows LS0–LS10)
**What was ported.** Mini `world/story/CoAuthor.obend` at 2c27b08b (486 lines). A crowd writes a story one chapter
per round. Each author proposes one passage and may edit it while the round is open. Each elector votes once.
After the window anyone seals the round, and the most-voted proposal (ties go to the earliest) becomes the next
chapter, forever. Its state is three recursive lists: `Proposals`, `Ballots` and `Chapters`. The port is
`Lang.Journey.coAuthorText`:
- Each list is bounded to 4 slots: 4 proposals, 4 electors, 4 chapters. A bitmask records who voted, and each
  proposal counts its own votes.
- A method cannot refuse. Each method is therefore Mini's `react`: it returns either the moved story (`version + 1`)
  or the unmoved story with `why` set. The one law `react` refuses an unmoved story by its `why`, and refuses every
  `write`.
- Now is the signer's window: an act is in the round when its window ends by `closes`, and a seal must start after
  `closes`.
The rows, through the real receivers:
- LS4/LS5: two proposals. LS5b: a second proposal by one author, refused `alreadyProposed`.
- LS6: a vote is counted. LS6b: a second vote, refused `alreadyVoted`. LS6c: a vote for an unknown proposal,
  refused `unknown`.
- LS7: another author's edit, refused `notAuthor`. LS7b: the author's own rewrite.
- LS8: a seal inside the window, refused `early`.
- LS9: the seal after the window makes the rewritten passage chapter 1, with its 1 vote.
- LS10: two proposals signed over one view. The second is `stale`.
- Plant skip-judge: LS5b is then ADMITTED, a turn that changed nothing a reader sees (delvetalk's W7, here exactly
  what the law exists to refuse).
**Measured** (deterministic counts, lang-journey on hbox at 7869bbc + this row):
| | Mini (.obend) | nano (core text, lists bounded to 4) |
|---|---|---|
| lines | 486 (67 comment, 106 blank; 296 for the pure story, 51 for its activity, 139 for scenario and tests) | 142 (long lines) |
| characters | 13,872 non-comment; 7,896 for the pure story | 63,865 |
| package bytes | (front-end artifact) | 52,965, of the kernel's 65,536 per event |
| required steps / ticks | (call-by-need, not counted) | propose 135 / 191, vote 226 / 322, seal 184 / 261 |
| bytes one turn logs | (n/a) | vote 655, seal 563 |
- **The first port could not be installed.** It wrote each list walk the way a Mini `match` on a list reads: the
  walk's tail written in both arms of a `case`. The core has no join point and no recursion, so the text DOUBLES at
  every slot. With 4 slots that made 125,955 characters and 114,004 package bytes, and the World refused the install
  `overBound` (eventBytesMax 65,536). This is the recorded "linear in Mini, exponential in nano" case, met for real.
  It is exponential in program SIZE, not in run time (LANG-2's case is run time under call-by-value). Sharing each
  tail through a `let` (a chain of continuations, evaluated eagerly) made it linear: 52,965 bytes. Eight slots would
  not fit under the bound even so.
- Where the 63,865 characters go: the 1,084-character state type is written 41 times (44,444 characters, 70%):
  10 in the interface, 7 in method and law binders, 24 in the `let` continuations. The authoring-surface need again,
  sharper than LANG-45's, because a list-shaped state is a big type.
- What a vote costs: the `proposals` field is ONE slot (LANG-11), so a vote rewrites every passage of the round (655
  bytes logged for one ballot). A relation row would log one ballot.
**What could not be expressed, and what replaced it.**
1. *Unbounded lists.* The bound is 4: a fifth proposal is refused `full` and a fifth chapter `storyFull`, while Mini's
   `total` is any number. This is the relation need, measured: CoAuthor is THREE relations. `proposals` is keyed
   `{author}`, and `keyTaken` IS `alreadyProposed`. `ballots` is keyed `{voter}`, and `keyTaken` IS `alreadyVoted`.
   `chapters` is keyed `{number}` and insert-only (a sealed chapter is "never edited again" by declaration).
2. *A refusal from a method* (`Transition.refused`): replaced by `version`/`why` plus the law, an encoding every
   method must carry. A surface needs `refuse` (delvetalk has `refuse(line)`); in the core it is this pattern.
3. *`now`*: the signer's window, as in LANG-45.
4. *The activity's `publish`*: not ported (no activities, LANG-6); a chapter is state, and a reader reads it.
5. *Concurrency.* Two proposals or two votes over one view: the second is `stale` (LS10). With LANG-44's rows,
   proposals and ballots are unpinned births at distinct keys and both land.
**What it says about LANG-44, beyond LANG-45.**
- Rows are this program's first need, and keyed inserts give two of its refusals for free.
- The SEAL reads the whole round: the winner is an arg-max over the proposals and their votes. LANG-44 v0 gives
  only point reads of pinned rows (its critique (5): "range reads inside a method are not in v0"), so seal cannot
  be written over relations without a RANGE read. The read is bounded, because the round's proposals relation has a
  limit, and a range pin (the subtree's hash: stale if any row in it moved) is exactly right for seal: a seal must
  see the whole round, and a vote landing under it must make it stale.
- So LANG-44 needs, before its build: a range read (a method declares `(rel, at most k rows)`; the signer pins the
  relation's subtree root; the receiver supplies its rows in key order, refused `rangeTooLong` past k) and the
  kernel's range pin. That is a kernel arm KERNEL-13 must co-sign with the rest.
- Per-proposal vote counts are a `count` per pick. With ballots keyed `{voter}`, a vote count is a filtered count,
  O(relation). Two honest answers: key ballots `{pick, voter}` and count a pick's subtree (a sub-range count; the
  head has only the whole relation's count), or keep a `votes` column on the proposal row updated under a pin
  (votes then conflict per proposal, which is honest: two votes for one passage race). I recommend the sub-range: a
  range read over `{pick, *}` returns the votes for one pick, and seal reads at most `limit` of them.
- Clearing a round means retracting every proposal and ballot: O(round) at seal, bounded by the limits, which is a
  retract-many act (or a relation per round: a key prefix `{round, …}`, so nothing is retracted and the old round's
  rows are a closed prefix). The prefix form is better: history is kept, and nothing is O(round) at seal.
**Critique.** (1) A bound of 4 is mine. Mini's story has no bound, and every bound I pick is a refusal Mini does not
have. (2) `let`-shared continuations evaluate every slot eagerly. That is linear, but a run pays for slots it does not
need (vote: 226 steps). (3) The CBV `let` chain is a hand transformation a surface would do (join points); a resident
writing the core by hand will write the doubling version first, as I did. (4) Two samples now, CappedTally and
CoAuthor, and they disagree on the first need (a counter, rows). Both are given by LANG-44 as amended, plus the range
read this sample adds.
**Meta-critique.** I wrote the doubling version first because the Mini source reads that way. The finding
("exponential in size") came from the World refusing my install, not from my design. The `let` fix is mine, and the
cost it hides (eager evaluation of every slot) is measured above. I have not ported the Activity layer, which is a
quarter of what Mini's program is about. It is cut on purpose (LANG-6), so it is not counted as a loss here.
**Status.** Rows LS0–LS10 built (lang-journey GREEN, including the skip-judge plant). The range read goes to ROOT
and KERNEL-13 as an addition to LANG-44.

## LANG-48 The pending slot: one Std law family for "a value whose shape is fixed now and which arrives later", with a meaning theorem after breadstuffs' `holeFill_binds_in_circuit` (2026-10-18; PROPOSED, design only; ROOT's queue item from MINI-CONCEPTS-IN-NANO-20261018 §6/§8)
**Why.** Breadstuffs' weak guarded hole (B:`metatheory/Dregg2/Exec/GuardedHole.lean`) is "determination EAGER, witness
LAZY". A hole's shape (which field, who fills it, the guard) is fixed when it is made, and only the value comes
later. `holeFill_binds_in_circuit`: a successful fill commits exactly the underlying write and has discharged every
guard caveat. `holeFill_rejects_guard_violation` is the tooth. The co-receipt (an open offer anyone matching may fill)
is the same object with an open filler. Mini lost it (MINI-CONCEPTS §2), and nano has it only as hand-written
patterns: LANG-45's CappedTally (a decider, a `closes` height, a cap law) and LEDGER's escrow (`held → released |
refunded`, settled by the arbiter, absorbing). Two hand-written copies of one idea are the defect law 1 names, and
each carries its own proofs (Ledger/Proofs/Escrow: `escrow_absorbing`, `escrow_one_payout`, …).
**Decision (proposed).** A generator `Std.pending` in LANG-20's library, emitting a law term and the fill method,
each with its meaning theorem over `BigStep`, as `quorum`/`windowed`/`machine` already are:
1. *The slot.* A state field `f : pendingTy V = sum {open : rec {closes : nat, filler : fillerTy}, filled : rec {by :
   digest, value : V}}`. `fillerTy = sum {anyone : rec {}, member : digest}`: `anyone` is the co-receipt's open offer,
   `member` the decider or the arbiter. The shape is eager (filler, closes, `V`, and the guard below are fixed when the
   slot is made). The value is lazy.
2. *The guard*, given to the generator as a clause over `(old, value, req)` (an `At → Term` like every Std clause,
   e.g. `value ≤ max` or `old.total + value ≤ cap`), so it may read the rest of the state but not write it.
3. *Two modes.* `once` (escrow, offers): `filled` is absorbing. `accrue combine` (CappedTally): a fill keeps the slot
   open and folds the value into a declared field by a declared combine (`add`), under the same guard.
4. *The generated law*, by occasion:
   - `birth`: the slot is `open` (no pre-filled seed).
   - `invoke fillMethod`: `old.f` is `open {closes, filler}`, the signer matches `filler` (`anyone`, or `deq agent
     d`), `req.validUntil ≤ closes`, the guard admits, `new.f` is `filled {by = agent, value}` (once; the value is
     the method's argument, recorded), or the accrual is applied (accrue), and every other field is unchanged.
   - Any other invoke or write: the slot's shape never changes while open, and `filled` never changes again.
   - `relaw`/`adopt`: an object may not shed or add this law while the slot is open (LANG-24's adopt clause).
5. *The generated method* `fill {value}` writes exactly that, and may declare one call slot (LANG-33). The funding
   form emits a `transfer` from the object's held account to `by` (the escrow's payout: `once` key the slot's
   nonce), so "funded by which escrow" is a declared call, atomic with the fill (the call tree co-fails).
6. *The meaning theorem* `pending_fill_binds` (the nano `holeFill_binds_in_circuit`): `Admits (pendingLaw …) old new
   req` at `invoke fill` ↔ `old.f = open {closes, filler}` ∧ the signer matches `filler` ∧ `req.validUntil ≤ closes`
   ∧ the guard's meaning admits the value ∧ `new.f = filled {agent, value}` (or the accrual) ∧ every other field of
   `new` equals `old`'s. Both directions, so the law admits EXACTLY the fills the shape promised: a fill binds its
   value AND its guard, and nothing else moves. Teeth on the CHECKED output: a guard violation is refused, a second
   fill of a `once` slot is refused (absorbing), a wrong filler and a late window are each refused, and an
   `anyone` slot admits a stranger. Plus a run-level corollary through the receiver, as LANG-26's
   `judgeOne_pkgOf_admits` did for quorum.
7. *Instances.* CappedTally becomes `pending (accrue add total) (filler = member decider) (guard: total + value ≤
   1000)`. Its hand-written `cap`/`decider` laws are deleted, and `grows` follows from `accrue add` over `nat`. The
   escrow's settlement becomes `pending once (filler = member arbiter) V = sum {release, refund}` with the funding
   call. LEDGER's `escrow_absorbing`/`escrow_one_payout` then restate as corollaries of `pending_fill_binds` (LEDGER
   owns that restatement; its deposit phase stays its own). Journey LT re-reads its text from the generator, and the
   escrow re-emits.
8. *With LANG-44's rows.* An `open` slot can be a ROW keyed by its requester (or a nonce). A fill is then an `upsert`
   pinned at that one row, so fills of different slots on one object have disjoint footprints and commute
   (`admit_comm`), and the head's `count` says how many are open. Offers that many members fill at once (the
   co-receipt market) need exactly that.
**Price.** Kernel: zero (a law shape). Lang: Std gains a generator and its theorems (Proofs/Std, StdTeeth, StdFits'
print bounds); nothing landed changes statement. LEDGER: the escrow re-emits (`ledger-sim --write-text`) and its
proofs restate onto the family, which is LEDGER's work; it re-ids the escrow package. Rows: none until LANG-44.
**Alternatives.** (a) A kernel `HoleSpec` (Mini's `Theory/GuardedAdvice.lean`): a second shape of "a law over pending
state", and the kernel object never reached Mini's Host (MINI-CONCEPTS §6(4)). (b) Leave the two hand-written
instances: two copies of one idea with two proof sets. (c) Suspended activities (`perform`/await): LANG-6's cut,
measured. (d) Matching as a solver (find a filler for an offer): not adopted; matching is the guard, checked at fill.
**Critique.** (1) The guard is a clause over `(old, value, req)`, so a guard over OTHER objects (a match against a
counter-offer held elsewhere) is not expressible. That is the invariant-domain gap (MINI-CONCEPTS §4), and a fill
can only pin what its signer pinned. (2) `accrue` makes CappedTally an instance, but at the cost of a mode. If accrue
is really a different idea (a capped counter), it belongs to LANG-44's head `sum`/`cap`, and this family should be
`once` only. I lean to keeping both until the rows land, then measuring which form residents write. (3) The strong
hole (an undetermined amount or shape) stays inexpressible, as breadstuffs decided: `charge = weight` is fixed by
the signer. (4) A `member` filler is one digest; a quorum of fillers is `quorum`, not this.
**Meta-critique.** ROOT named the instances (CappedTally, escrow) before I designed the family, and I fitted the
family to them: `accrue` exists so that CappedTally fits. The independent test is breadstuffs' own object: its
`GuardedHole` is one field, one actor and one guard, written once. That is `once` mode exactly. `accrue` is my
addition, and (2) says so.
**Status.** PROPOSED (design only, ROOT rules). Build order if approved: after LANG-44 (its rows give the many-slots form).

## LANG-49 · Relations built: LANG-44's Lang half as ruled (rows, range reads, head sum/cap), against KERNEL-48's signatures (2026-10-18; LANG-14, on the one `kernel!` rows day with KERNEL-16, CODEC-9 and HOST)
**Decision.**
- *Declared per package.* `Package.rels : List (Label × RelDecl)` (labels ascending, ≤ `relsMax` 8), relation `i`
  is the `i`-th. `RelDecl := {key : List (Label × Ty) (DECLARED order), val : Ty, limit, sum : Option Label, cap,
  retract : Bool, guard : Option Label}`. Install refuses by name: `relKey ℓ` (a key that is empty, has > 8 fields,
  a repeated label, a field that is not fixed-width data (nat, bool, digest, an enumeration, records of those;
  bytes/functions/payload sums refused), or is wider than `Kernel.Bounds.keyBytesMax` (128) at the deployed 32-byte
  digest), `badRel ℓ` (a value that is not wire data; limit outside 1..`rowsPerRelationMax`; `sum` not a nat field of
  a record value, or `cap` set without it (cap 0 ⇔ no sum, the kernel's convention); a guard that is not an interface
  field of type `fn S (fn reqTy (fn relEditTy verdictTy))`), `tooManyRels`.
- *Key bytes* are the ordinary data encoding of the key's fields in declared order (`keyWireTy`: positional labels
  `k0 …`, so CODEC's record = product writes them; a range prefix is the first `m` fields). The method sees a key as a
  record (labels ascending). No `u64be` flag day: v0 ranges are PREFIX-EQUALITY, never intervals, so numeric key
  order is unused (named limit: "the latest rows by number" is not a range until CODEC gives `u64be`).
- *A method's shape* (one shape for every method): `methodTy S A ks R E es = fn R (fn S (fn A (fn reqTy (rec {calls,
  edits, state})))))`. ROWS FIRST, so every body's state/argument/request keep `var 2/1/0`. `R` is a record over the
  relations the method reads: per relation `p0 … p(n-1) : optTy (rec {key, val : optTy V})` (the caller's row pins
  under it, in pin order; absent row = `val none`; more pins than slots refused) and optionally `range : rec {pre :
  first-m-fields record, rows : rec {r0 … r(k-1) : optTy (rec {key, val})}}` (the one signed range under it; its
  `most` ≤ k; none or two signed ranges refused). `edits : rec {e0 … e(m-1) : optTy editTy}`, `editTy = sum over the
  package's relations of sum {insert : row, [retract : rec {key}] (only if retract), upsert : row}`. Bounds: points ≤ 8,
  range rows ≤ 8, edits ≤ 8 (each ≤ 10 so slot labels ascend), plus the kernel's per-turn `rowsMax` 32 / `rangesMax` 4.
  `methodSig S rels` reads the declaration back EXACTLY (it rebuilds `readsTy`/`editsTy` and compares), returning
  `Sig {arg, calls, reads, edits}`. A method that reads and edits nothing has `R = rec {}`, `edits = rec {}`.
- *The run* (`Program.run`, now `Pinned → RowView → … → Slots × calls × row edits × ticks`): `readsData` builds `R`
  from the `RowView` (`points`, `ranges` under `(self, i)` only: no lookup oracle, Eval/BigStep/Need untouched);
  `editsOf` reads the edits row into `(RowSlot.row ⟨self, i, keyBytes⟩, insert|upsert amt v | retract)`, `amt` = the
  value's sum column (0 without one); then each edit's GUARD runs through the one law runner `runLaw` over (state
  before, request, the relation edit): O(edits), never a relation (law 5); refusal `lawDenied pkg "GUARD: reason"`.
  `Program.rels` gives a create the `declare limit cap width retract` acts (width at the World's digest width).
- *Receive* (Kernel/Receive, with KERNEL-15's agreement, cross-layer): `Unsigned.rowPins`, `Unsigned.ranges` (signed);
  `RowView`/`rowView` (the view of the CURRENT World through the caller's row pins and signed ranges, listings at the
  head's width, `rangeTooLong` never truncated); `Draft.rows`; `sealTurn` → `Turn.rows` (each row pin with its act or
  `keep`, then unpinned inserts/declares) and `Turn.ranges`; new receive refusals `rowUnpinned`, `rangeUnpinned`,
  `rangeTooLong`, `rowParent` (law 4: a run edits only its own object's rows, asserted where edits enter),
  `duplicateRow`. `receive_congr` gains its one honest premise: the two `RowView`s agree.
- *Text*: a seventh package section `(rels (ℓ (key (f T)…) (val T) (limit n) (sum [f]) (cap n) (retract b) (guard
  [g]))…)` between `laws` and `body`, always present; the wire's package node gains a seventh child `node 2 [rel…]`.
**Critique.** (1) The rows argument is verbose for a resident: `p0 … p(n-1)` slots and the `range` record are
fixed-arity data, the cost of "no lookup oracle"; the authoring surface (LANG-50) is where this gets names. (2) A
range's `most` must be ≤ the method's slots, and the method must still CHECK `pre` against its own state (a signer
may pin a different round's range); the type gives the method `pre`, not the obligation. (3) Guards are package code
like methods; a guard sees (state before, request, edit), NOT the old row, so "an upsert may not change the author"
is not a guard (CoAuthor has none for that reason; the method checks it); on a programmed object they are a declarative per-edit invariant (as laws are), not a second authority.
(4) Head reads (count/sum) are not offered: pinning the head would serialize every insert, by design; a method that
needs the sum cannot see it (the tally does not: the kernel enforces the cap). (5) One method shape for all means
the ROWLESS methods pay for the rows methods' shape: THE BAR's counter `add 1` rose from 1.545 to 1.577 ticks per
required step (one more application, one more extracted field); ROOT ruled the ceiling 1.546 → 1.578 with that reason
(law 1: one shape over two). It also means every package re-ids and every hand-written text gains `(v (rec))`, `(edits (record))` and `(rels)`.
**Meta-critique.** The pull was toward an optional rows argument (methods without rows keep three binders) because it
spares Ledger/Hosting/Protocol proofs a restatement; that is two method shapes, the thing this repo deletes. Rows-first
was chosen for a cheaper reason (indices unchanged) and I checked it is not worse for the reader: the surface binds by
name anyway.
**Flag day.** Package bytes (seventh node), every method type (rows binder, edits field), every package id; the call
(Unsigned rowPins/ranges); re-emits world/grain/Lifecycle, world/hosting/Allowance (hosting-sim --write-text),
world/escrow/Escrow (ledger-sim --write-text), THE BAR counter; an old package text refuses `notPackage`, an old
package's bytes `lang/package` (decode), an old method type `badMethod`.
**Measured (the rows half of LANG-50's spec).** CappedTally on a relation: 4,355 chars / 3,034 package bytes (by hand
over a pinned total: 3,903 chars); one reply 40 required steps / 63 ticks. CoAuthor on four relations: 37,287 chars, 67
lines, 30,028 package bytes (over 4-slot lists: 63,865 / 142 / 52,965); propose 85/129, vote 115/166 (770 B logged), seal
236/299 (676 B). Two answers / two proposals over one view both land, in both orders, to the same rows and cells roots
(LT7c, LS10c); a vote and an edit of one proposal over one view: the second `stale` (LS11).

## LANG-50 The authoring surface: a second reader that lowers to the core text `Lang.Read` reads, outside the TCB; with LANG-51, the two core additions it cannot do without (2026-10-18; PROPOSED, design only; LANG-15; DELVETALK-LEARNINGS §4.1/§4.5/§3.1, LANG-0 (c), LANG-45/47/49's measurements)
**Why.** Every package anyone has written for nano was written in Lean, not in the language: `Std`, `Hosting.Grain`,
`Ledger.Escrow` and the journey's `s!` templates are the authoring surface today, and only an agent with a Lean
toolchain can use them. What a resident would write by hand is the printed core, and the two ports measured it:
CoAuthor's 1,084-char state type written 41 times (70% of 63,865 chars, LANG-47); the tally's types 15/7/13 times
(LANG-45); Lifecycle's state record 14 times in 7,709 bytes. The core is right for the kernel (closed, monomorphic,
annotated, one checker proved equal to a relation). It is wrong for a hand. LANG-0 (c) deferred the Front because it
had "no deployed consumer"; the consumer is now the Hermes resident (CHARTER's BAR) and THE BAR's `use=U` row.
**Decision (proposed).**
1. *One more reader, never in admission.* `Lang/Surface.lean`: `Surface.readPackage : String → Except ReadRefusal
   Package` = `Read.parse` (the same s-expression parser) → `Surface.lower : SExp → P SExp` (a surface form to a CORE
   form; every core node it makes carries the offset of the surface node that made it) → `Read.package` (the one core
   reader). So the surface's output IS a core text read by `Lang.Read`; the surface never builds a `Term`.
   `ob` and every tool that installs then do `Print.package` → `Read.readPackage` → `checkWith` → `encodePackage`:
   what is installed is the printed core re-read by the one reader, so a surface bug can make a WRONG program (which
   the checker and the laws judge like any other) but never an unread one. The kernel, the receivers and the
   install check do not change. The surface is a superset: a core package text lowers to itself (theorem 1 below).
2. *Package declarations*, any order, each at most once per name: `(type N T)` a type name, substituted wherever
   `N` is written (types have no binders in the core, so a name is a macro and never reaches the core); `(state T)`;
   `(rel ℓ (key (f T)…) (val T) (limit n) [(sum f) (cap n)] [(retract)] [(guard g)])` (defaults: no sum, cap 0,
   insert-only, no guard: the core's `rels` entry with its defaults written for you); `(method ℓ [(reads (rel (points
   n) | (range m k))…)] [(arg T)] [(calls (kind…)…)] [(edits n)] BODY)`; `(law ℓ CLAUSE)`; `(guard g BODY)`;
   `(import N "hex")`; `(layer N)`. The core's `iface`, `methods`, `laws` and every binder annotation are DERIVED
   from the declarations (iface = laws at `lawTy S` and methods at `methodTy S A ks R E es`, `Std.pkgOf`'s order), so
   the state type is written once and no method type is written at all. Built-in type names: `Req`, `Verdict`,
   `Occasion`, `AcctRef`, `Right`; type forms `(enum a b …)` (a sum of empty records), `(option T)`.
3. *Fixed binder names by position* (delvetalk's `state, input, context`): a method binds `rows state arg req`, a law
   `old new req`, a guard `state req edit`. A dotted atom `x.f.g` is `(. (. x f) g)` when `x` is bound and `x.f.g`
   is not (a bound name wins, so no core text changes meaning).
4. *Term forms, each filled ONLY from a declaration, never inferred* (the surface has no type inference, so it is not a
   second checker): `ok` / `(refuse e)` (in a law or guard: the verdict injections; in a method: LANG-51's core
   `refuse`); `(done STATE ITEM…)` the method result, each ITEM an edit `(insert rel K V)` `(upsert rel K V)`
   `(retract rel K)` or a call `(transfer (f e)…)` `(invoke …)` … filling the declared edit and call slots in order,
   the rest `none`, every `inj` annotation from `rels` and the declared call kinds; `(with e (f x)…)` the full state
   record, every other field `(. e f)` (Std.methodOf's shape); `(N ℓ [e])` for a type name `N` of a sum: `(inj N ℓ
   e)` (`(record)` if omitted); `(some T e)` / `(none T)`; `(is N e ℓ)` = `Std.isState`; `(all (c "why")…)`,
   `(check (c "why")… BODY)`, `(any e…)`, `(and a b)`, `(not a)` = `Std.allOf/guards/anyOf/andT/notT` in the
   context's `refuse`; `(index m)` a method's index (`Std.methodIndex`); `(fold (acc T init) (x rel) STEP BODY)` over
   the method's declared range of `rel`: the `let` chain LANG-47 found by hand (one `let` per row slot, so the text
   is linear, never doubled). A law clause is `(on occ [x] BODY)…` with `occ` one occasion or a list, then
   `(else BODY)`, which is REQUIRED unless all five occasions are written (no silent default verdict). Std clauses
   by name lower by CALLING the generator and printing its term: `(machine f initial (from method to)…)` declares law
   `f` = `Std.machine` and a `Std.stepTo` method per method label not declared by hand; `(bounded f max)`,
   `(allowlist id…)`, `(quorum …)`, `(windowed …)`. A clause's meaning theorem (LANG-20/26) is then about the very
   term the surface emits.
5. *Bounded argument forms (§4.5).* In an `arg` type only: `(nat lo hi)`, `(bytes lo hi)` (and a type name for one).
   The core type is `nat`/`bytes`; the method body is prefixed by one check per bounded field in label order, `(if
   IN-BOUNDS BODY (refuse "text 1..200"))` — the refusal names the field and the bound (delvetalk's dialect; its
   obend night refused `from: 0` against `1..1e9` six times with no field named). A bound anywhere else (state,
   rel value, inside a sum) is refused `boundOutsideArg`: a state bound is a law (`bounded`), a row bound a guard.
6. *`layer` (amends LANG-18's "open recursion is a mixin the authoring tool writes").* `(layer N)` over the imported
   package `N`: the layer has `N`'s state and rels EXACTLY, inherits `N`'s methods and laws, may add methods and laws
   and override a method at the SAME type (`retypedOverride` otherwise), and may not override or drop a law
   (`overridesLaw`: a layer never weakens its super's laws). It lowers to `(imports "N")`, `body = (extend (ref 0)
   (ℓ new)…)`, iface = `N`'s plus the new fields, laws = `N`'s ∪ new. `(super m)` is `(. (ref 0) m)`, `N`'s OWN
   method: the layer gives delvetalk's `Super.f` and override, and NOT late binding of self (LANG-18's old-self
   `extend` stands, now as the surface's stated semantics: nano methods do not call siblings, calls are effects).
   The super's checked core is what runs, its id is in the layer's imports, so "which layers made this object"
   (LANG-1's lost reflection) is readable from the bytes. Lowering needs the super's package text (`ob` gains
   `(check P (imports P…))`; a reader without the World passes it).
7. *The source digest, beside the core and NOT in it (decides LANG-0's "one field").* The package bytes and id do not
   change. A source binds to a package by computation, not by a stored claim: `ob (source TEXT)` answers the package
   id the text lowers to and the source's digest, so anyone holding an id and a text checks the binding offline.
   Putting the digest IN the package (LANG-0's literal reading) was rejected: the kernel cannot check it (no front end
   in admission), so it would be an unchecked field inside ROM identity that the next reader trusts (CLAUDE.md's "a
   no-op kept is worse"), and it would give two sources of one core two ids. Finding a text from an id is a store:
   the Host keeps a source by package id ONLY after lowering it to that id (the Host may run the surface; admission
   never does). That store is PROTOCOL/HOST's (cv task to PROTOCOL; not part of this build). The shipped packages
   keep their surface text beside the core in the repo: `world/grain/Lifecycle.ob`, `world/hosting/Allowance.ob`,
   `world/escrow/Escrow.ob`.
8. *Errors name the surface line.* `Read.locate : SExp → (path : List String) → Nat` walks the core SExp along a
   `TypeErr` path (LANG-27). Because lowering stamps each core node with its surface offset, `ob` answers
   `refused illTyped noField @body.reply.fn.fn line 5: (. arg amout)`; `noMethod ℓ` / `badRel ℓ` / `relKey ℓ` name the
   declaring line. A type in an answer prints with the package's names (`Surface.tyText names T`: the largest
   subtree equal to a name's expansion prints as the name), so a wrong method type reads `(-> (rec) (-> State …))`,
   not 1,084 characters.
9. *The three shipped texts are re-emitted FROM their surface sources*, byte-identical core: the sims' rows
   G0/A0/E0 become "`Print.package (Surface.readPackage world/…/X.ob)` = `world/…/X` = `Print.package` of the Lean
   builder", and `--write-text` writes the core from the surface. Each row carries a PLANT: the row run on the
   surface text with one token flipped (`(revoked true)` → `(revoked false)`, an edge reversed, `"notOpen"` →
   `"notHeld"`) must go red. The Lean builders stay (their meaning theorems are about them: `Std.machine_invoke`, `stepTo_takes_every_edge`,
   LEDGER's `escrow_absorbing`, …), and the row ties text to builder; a resident reads the `.ob`.
**LANG-51 (proposed with it; a core change, append-only on the wire).** Two things the ports showed a hand cannot
write in the core at all, which §4.5 and LANG-47's critique (2) need:
- `refuse T e` (term tag 17): evaluates `e : bytes`, then the run ends in a new `Fault.refused why`; typed at the
  annotation `T` (like `inj`). A method refuses by name today only through a `why` state field plus a law reading it
  (CoAuthor's encoding: one field, one law and a `no` continuation per method, written in every method). Run in a
  method it is `program "ℓ: refused why"`; in a law or guard `lawDenied ℓ: refused why`.
- `len<= a n` (prim code appended): `a.size ≤ n : bool`, O(1). There is no byte length in the core, so `text 1..200`
  cannot be checked at all.
Both are new tags only: no shipped package's bytes, id or text change (Lifecycle, Allowance and Escrow use neither),
THE BAR's counter values are unchanged (its programs use neither; `Need` gains two one-step rules). Reshaped
statements, each restated with the new disjunct and nothing else, for the vacuity read: `Sound.step_fault`
(a fault is `stuck`, a primitive's error, OR a `refuse`), `RunOK`'s fault set, `faultText`/`faultName`, and every
theorem that enumerates `Fault` (to be listed by grep at build; `checked_never_stuck` keeps its statement). New
theorems: typing/step/`BigStep` cases with `run_bigStep`/`bigStep_run` re-proved; `refuse_refuses` (a checked
method whose body reaches `refuse e` is refused with exactly `e`'s bytes, never admitted) with its tooth.
**Theorems (LANG-50).**
1. `read_print_surface`: `Print.package p = some t → Surface.readPackage t = Read.readPackage t` (with LANG-29,
   `= .ok p`): the surface reinterprets no printed core. Tooth: a printed package whose labels ARE the surface's head
   words (a method `with`, a field `done`, a law `machine`, a relation `insert`) reads to itself, and a lowering that
   rewrites heads in label position fails on that instance.
2. `bound_check_meaning` over `BigStep`: the lowered prefix of a bounded method means `refused "f lo..hi"` iff some
   bounded field is outside its bound (first in label order), else the body's meaning. Tooth: `bytes 1 200` at the
   empty text and at 201 bytes, refused; at 1 and 200, the body.
3. `tyText_names`: reading `Surface.tyText names T` back under `names` gives `T` (the named printer is an inverse).
4. Rows: G0/A0/E0 byte identity with their plants (9); LT0 the tally's surface lowers to EXACTLY today's tally core;
   LS0 CoAuthor re-cut on `refuse`; LE a planted type error on line 16 answers `line 16`; LL a layer over the tally
   (one method added) installs and runs through the receivers, and a layer overriding the law `decider` is refused
   `overridesLaw`.
No theorem is offered for "the surface output is a core text": that is the pipeline's construction (1.), not a fact
to prove, and it would collapse to `readPackage_package`.
**Measured spec** (drafts in hand, chars of the surface text; core = what is shipped or printed today):
| text | core today | surface | target |
|---|---|---|---|
| world/grain/Lifecycle | 7,709 | 277 | state record once |
| world/hosting/Allowance | 2,625 | 478 | state record once |
| world/escrow/Escrow | 12,019 | 2,223 | state record once |
| CappedTally (journey LT) | 4,355 | 667 | under Mini's 1,269 (no comments) |
| CoAuthor (journey LS) | 37,287 | 2,464 | under Mini's 7,896 (the pure story) |
(The brief's "CoAuthor under 64 KiB with 8 slots" was met by LANG-49's relations, 30,028 package bytes with an 8-row
range; the surface target is the hand's text, so it is set against Mini's.) Required steps and ticks: unchanged for
Lifecycle/Allowance/Escrow/tally (identical core); CoAuthor's re-measured (it loses the `why` field and its law).
**Price.** A second reader (~700–900 lines, Lang tooling, outside the deployed closure: no receiver imports it);
`ob` reads both (it is a superset); `Read.locate` (+ a row); LANG-51's two constructors through every Lang proof
that inducts on `Term`/`Prim`/`Fault` (statements unchanged except the fault enumerations above); cross-layer: the
three `.ob` files and the G0/A0/E0 rows (HOSTING, LEDGER: not live, ROOT agrees). No kernel, codec or protocol change;
CODEC's term vectors gain two tags if CODEC keeps vectors for Lang terms. No premise is added to any landed theorem.
**What it does NOT do, and why.**
- *No type variables, no row-generic mixins* (LANG-1/3's cuts stand). A type name is a macro over CLOSED types, so
  every surface type is a core type and every core theorem (all about closed monomorphic terms) covers it. A layer
  that adds state fields or relations would need either core row polymorphism (exact types are why `=` is type
  equality and checking is a function proved equal to a relation) or re-elaborating the super's SOURCE at the
  layer's types: then a package's meaning depends on names another author chose, its errors land in someone
  else's file, and the super's checked core is not what runs. delvetalk does not do it either: its bell writes
  `type State = Super.State`. A layer that wants more state is a new package; measured cost: its text.
- *No inference.* No `inj` annotation, call kind or result type is guessed from context; all come from a
  declaration. So the surface cannot disagree with the checker about a type: it never decides one.
- *No join points by analysis.* `let` and `fold` share by hand; the surface does not find common tails (LANG-47's
  doubling stays writable, now with `fold` beside it).
- *Not in admission, not in the id.* The kernel judges the core; nothing about the source is stored by the kernel.
**Alternatives.** (a) Lower straight to `Term` with the Std combinators called on terms (byte identity by
construction for every combinator, not only the Std clauses): loses the offsets, so errors would point into a core
no one wrote, and the surface would be a second term reader beside `Read.term`. Rejected; the combinators are
small, mirrored in SExp, and held by the byte-identity rows. (b) Generate the shipped texts' surfaces from the Lean
builders (a resugaring printer): the `.ob` would then be an output, never what an author writes. (c) Make the `.ob`
the ONLY source (delete the Lean builders): their meaning theorems are proved about the builders, and re-proving them
through the reader is a reduction bomb of the kind Poseidon2 taught; kept, tied by rows. (d) The source digest in
the package: rejected in 7. (e) `refuse` as a surface pattern over a `why` field and a law: every package that refuses
pays a state field and a law, and a resident must know the pattern; LANG-51 instead.
**Critique.** (1) The combinators (`all`, `any`, `check`, `is`) are mirrored, not shared: a second statement of
`Std.allOf`'s shape, held equal only by the rows over the texts that use them (Escrow uses all four). A theorem per
combinator (`Read.term (lower (all cs)) = Std.allOf …`) would close it; I price it at a day and propose it only if a
row ever drifts. (2) Fixed binder names (`state`, `arg`) are a dialect, and a dialect is something to learn; they
also make `state.state` possible when a state has a field `state`. (3) `machine` declaring methods for you is
action at a distance: a method appears with no `(method …)`. delvetalk's clause distance has the same property.
(4) LANG-51 is a core change proposed inside a surface decision; it is separable, and without it §4.5 cannot be
built at all (no length, no refusal), so I propose them together rather than ship bounds as a `why`-field pattern.
(5) The source store (7) is the half of §3.1 a reader of someone else's object needs, and it is not in this build.
**Meta-critique.** I measured the surface against texts that were written by generators, so the drafts benefit from
regularities a hand-written package may not have (Lifecycle is 277 chars because it IS one Std clause). The honest
tests are the two hand ports (the tally, CoAuthor), and the first resident package written in it, which I cannot
measure. I also chose to keep the Lean builders, which keeps my layer's proofs where they are; the reason given (the
meaning theorems are about the builders) is real, and the cost is a text and a builder that a row must keep equal.
Status: SUPERSEDED PROPOSAL: Lang.Surface implements the authoring reader. Source-identity and executable-documentation follow-ons are separate obligations, not asserted complete.
The original build order is historical; the following amendment records the core and surface implementation.

**LANG-51 · Built (2026-10-18; LANG-15; ROOT APPROVED both, with conditions).** `Term.refuse (ty : Ty) (why : ByteArray)`
(wire tag 17, `why` the payload, `ty` the one child), `Fault.refused why`, `Prim.lenLe` (code 11; `bytes, nat → bool`,
`a.size ≤ n`: `ByteArray.size`, O(1)). One amendment to the proposal, from the vacuity read: the reason is a LITERAL
(not an evaluated term) and the checker requires `Bounds.reasonOk` (at most `reasonMax` = 256 bytes, UTF-8, no
control character; `badReason` otherwise). A refusal is a name (law 7), so the program's data never chooses it, and
what it wrote is exactly what every reader shows on one line (`reasonText` truncates at 256: no two names collide in
display). `ob` prints `fault refused <reason>`.
- *Reshaped statement (the only one):* `Sound.step_fault` gains a third disjunct, a state evaluating `refuse T w` with
  `f = .refused w`. No premise added anywhere. `HasType`, `BigStep`, `Derives`, `Canon` gain one constructor each;
  `RunOK`/`StepOK` (`f ≠ .stuck`), `checked_never_stuck`, `eval_sound` unchanged (vacuity reader: LAND-WITH-FIXES, no
  HIGH; its two MEDIUMs fixed as above).
- *New theorems:* `bigStep_refuse_iff`, `primEval_lenLe`; teeth per tag: `refuse_named`, `refuse_one_step`,
  `refuse_lazy_field`, `refuse_untaken_arm`/`refuse_taken_arm`, `refuse_left_first`, `lenLe_at_bound`,
  `lenLe_past_bound`, `lenLe_size_not_content`, `lenLe_empty_zero` (machine); `refuse_round_trip`,
  `refuse_untyped_refused`, `lenLe_code` (wire); `refuse_prints`/`refuse_reads`, `refuse_typed`,
  `refuse_unsorted_refused`, `refuse_newline_refused`, `refuse_long_refused`, `lenLe_typed`, `lenLe_nat_refused` (checker,
  printer). Journey LR0–LR4 through the receivers: a method's refusal is `program "put: refused note 0..4"`, a law's
  `lawDenied … "small: refused over 100"`, the four-byte note at the bound lands.
- *Flag day:* none for shipped bytes. Lifecycle, Allowance and Escrow print byte-identical (G0/A0/E0 green); no
  package id moves; THE BAR's programs use neither tag. New: term tag 17, prim code 11, `Fault.refused`,
  `TypeError.badReason`, reader keyword `refuse` (a binder named `refuse` is now `reservedBinder`), `ReadRefusal.badRefuse`.

**LANG-50 · Built (2026-10-18; LANG-15; ROOT APPROVED with conditions 1–4).** `Lang/Surface.lean` (the reader, never
in admission: no receiver imports it), `Lang/Proofs/Surface.lean`, `Lang/Proofs/SurfaceTeeth.lean`; `ob` reads both
forms; the three shipped packages have their surface sources beside their cores, and `--write-text` writes the core
FROM the surface.
- *Measured spec, met* (surface text chars; core chars; package bytes):
  | text | core | surface | target |
  |---|---|---|---|
  | world/grain/Lifecycle | 7,709 (5,970 B) | 305 | state record once: met |
  | world/hosting/Allowance | 2,625 (2,175 B) | 478 | met |
  | world/escrow/Escrow | 12,019 (9,375 B) | 2,223 | met |
  | CappedTally (LT0s) | 4,002 printed (3,034 B), byte-identical | 668 | under Mini's 1,269: met |
  | CoAuthor (LS0) | 45,735 (36,979 B) | 2,464 | under Mini's 7,896: met |
  | a layer over the tally (LL0) | 1,710 B | 111 | — |
  The first three and the tally lower to EXACTLY the shipped/printed core (G0s, A0s, E0s, LT0s). CoAuthor's CORE grew
  (37,287 → 45,735 chars, 30,028 → 36,979 bytes): it is now a different program (method refusals instead of a `why`
  field and a law), and every `refuse` carries its method's full result type as its annotation (LANG-3's annotations,
  measured: 16 refusal sites in the lowered core). Required steps / ticks: propose 85/129 → 102/152 (two bound checks), vote 115/166 →
  111/159, seal 236/299 → 270/339 (`fold` binds its first row then walks all 8). THE BAR's programs are unchanged.
- *How it differs from the proposal, and why.* (a) Bound checks are built on TERMS after the one reader read the method
  (`boundCheck`, `wrapMethod`), not in the s-expression, so their meaning is a theorem about a Lean function; `ob`'s
  error locator skips the checks (`locateField`). (b) A package's methods are sorted by label (as `Std.pkgOf`
  and `Std.methodIndex` sort; CoAuthor's rows re-indexed: edit 0, propose 1, seal 2, vote 3), EXCEPT a layer, whose
  methods are its super's in the super's order followed by its own sorted (`layer_keeps_indices`): a super law that
  names a method by index still judges the same method. `(index m)` is the position in the package's method list.
  (e) `(machine f initial (methods m…) edges…)` names the methods it steps; an edge naming any other is refused
  (`unknownMethod`), so a typo never makes a public method. (c) A type name may name a bounded form (`(type Line (bytes 1 200))`), usable only in
  an argument (`boundOutsideArg` elsewhere). (d) The story has no law. The hand port's `react` also refused a direct
  `write`; KERNEL refuses that first for every programmed object (`hasMethods`, LS2b, measured), so a law arm would be
  a no-op. The skip-judge plant no longer has a story row to bite (LS6c's line deleted; it bites in L*/LT*);
  drop-range-row still bites at LS9.
- *Theorems.* `read_print_surface` (every printed package is read by the surface exactly as by `Read.readPackage`);
  `layer_keeps_laws` (a layer that lowers has all of its super's laws, imports exactly the super, shares state and
  relations, and its body is `extend (ref 0) fs` with no field named like a super law), `layer_keeps_guards`,
  `layer_keeps_indices`, `layer_law_is_super`, and `ext_sel_untouched` (the evaluator's form: for ANY value, record or
  knot, extended by fields not named `ℓ`, selecting `ℓ` means exactly what it meant before); `boundCheck_in`,
  `boundCheck_out` (the first field out of its bound refuses by exactly `"f lo..hi"`), `boundCheck_all_in`,
  `Bound.cond_nat`, `Bound.cond_bytes`. Teeth: `empty_package_surface`; `layer_adds_method`, `layer_law_refused`,
  `layer_retype_refused`, `layer_override_same_type`; `bound_name`, `bound_empty_refused`, `bound_long_refused`,
  `bound_one_passes`, `bound_four_passes`. Rows: G0s/A0s/E0s (byte identity + a plant each: an edge reversed,
  `(revoked true)` flipped, a reason renamed), LT0s (identical core; `Lang.Read` alone refuses the surface text),
  LE (a misspelt field is refused naming its own line), LS4b/LS4c (`propose: refused slot 0..7`,
  `propose: refused text 1..2000`), LL0–LL5 (a layer installs, its own `close` runs, the tally's `reply` runs from
  the tally's installed core, the tally's law judges the layer's object, a layer naming `decider` is refused
  `overridesLaw … line 5`).
- *Vacuity read* (LAND-WITH-FIXES, all fixed here). H1: a layer re-sorted its super's method indices (fixed: prefix
  order, `layer_keeps_indices`). H2: CoAuthor's lost write refusal (measured: KERNEL's `hasMethods`, row LS2b). H3:
  `with` dropped an unknown or repeated field silently (now `noField`). M1: `is` with a foreign arm, a repeated `on`
  arm or `else` (now refused). M2: a layer overriding a super's relation guard (now `overridesGuard`). M3: the law
  theorem tied to the evaluator (`ext_sel_untouched`). M4: `wrapMethod` refuses a method that is not four binders
  (`badShape`). M5: machine methods named. LOW: a bounded top-level argument refused; a shipped row's plant must still
  lower; LT0s gains a plant (`(cap 999)`); historical sizes labelled.
- *Flag day:* none. No shipped byte, id or THE BAR value moves; three new files `world/*/*.ob`; HOSTING's and
  LEDGER's text writers now read them (ROOT for HOSTING/LEDGER).

## LANG-52 The Bell: the first package a resident uses that a person wrote in the surface (2026-10-18; LANG-16, with HOSTING-8, who owns the resident process; STAND-INS-20261019 A1/E12)

**What.** `world/resident/Bell.ob` (762 chars) and its emitted core `world/resident/Bell` (6,697 chars;
5,234 package bytes). A ringer rings with a text; the hosted resident reads the bell, asks its model
and answers; one ring at a time.

    state (rec (answer bytes) (open bool) (pending bool) (resident digest) (ring bytes) (ringer digest))
    answer {text (bytes 1 2000)}   refused notResident unless req.agent = state.resident; unrung unless pending
    close / open                   set open (the owner's, or granted)
    ring   {text (bytes 1 2000)}   refused closed unless open; busy while pending; sets ring, ringer = req.agent,
                                   answer = "", pending
    law bell                       a birth is not rung ("rung"); an invoke keeps resident ("resident")

**Why state only, no relation (measured).** The resident reads the World only through `nd --stdio`, and
`read OBJ` (Protocol/Command/Machine.lean `render`) prints state slots, never relation rows. A guestbook
in `rel posts` would be a package no resident can read. A queue of rings is the bell over a relation,
once a row read exists in the resident's verbs (PROTOCOL's).

**Who may ring is the kernel's, who may answer is the text's.** Grants (KERNEL-25) decide who invokes
`ring`. They cannot express "only the resident answers": the owner may invoke every method (LB8). So
`answer` checks `req.agent = state.resident` in the text, by name.

**The law is not a no-op.** No Bell method changes `resident` or rings at birth, but (a) the creator
writes the birth state, so without `bell`'s birth arm an operator could seed a ring nobody rang
(LB2), and (b) a layer may override `answer` and cannot override a law (LANG-50 `layer_keeps_laws`):
LB13 installs a layer whose `answer` makes the signer the resident, and `bell` refuses it.

**Critique.** (1) `busy` refuses a second ringer until the resident answers: a limit the read path
forces, not a design preference. (2) `ringer` is any member the grants allow; the bell does not bound
how often one member rings (a windowed law would, `(law ℓ (windowed f W limit))`, when a box shows the
need). (3) `answer = ""` on ring is a value, not an absence: an `(option bytes)` would say "no answer
yet" exactly, and costs the resident a sum to read; `pending` already says it.
**Meta-critique.** (1) is the one that would harden into a stand-in: written down here and in a cv task,
so the swap to a relation is findable (cv 01a14ece-43f1). (2) and (3) are taste until a resident runs: the bell is small
enough that changing it is a re-emit of one text and its core, which LB0 checks.

**Rows (lang-journey, through the real receivers).** LB0 source lowers to the shipped core byte for byte,
plant `(pending true) -> (pending false)` caught; LB1 install; LB2 born rung refused (`bell: rung`);
LB3 create with B the resident; LB4 grant B answer; LB5 unrung; LB6 ring (pending, ring, ringer read
back); LB7 busy; LB8 the owner answers: notResident; LB9 empty text: `text 1..2000`; LB9b B rings: the
kernel's grantRight; LB10 B answers (answer read back); LB11 unrung again; LB12/12b closed; LB13 the
takeover layer refused (`bell: resident`). Plants: skip-judge makes LB2 and LB13c admitted. No theorem
moves; no shipped core byte moves (the three shipped texts and the two ports are untouched).

## LANG-53 stepTo at run level: the generated method lands where its edge says (2026-10-18; LANG-16; cv 01a14b36-6da2, LANG-43's owed item)

**What.** `Lang/Proofs/StdRun.lean` (new; its own module so Complete and Program do not widen `Lang.Proofs.Std`'s import cone): `stepTo_moves` — a method `stepTo` generates, installed as field `ℓm`
of the package body at `lib[g]` and run as the receiver runs it (`apply4 g ℓm` over rows, state,
argument, request: the env `runSetup` builds), from a state whose field `f` is `x`, means a result
whose state field `f` is `y`, for every declared edge `(x, m, y)`. `stepTo_keeps`: every other field
means what it meant. `stepTo_stays`: from a state no edge of `m` leaves, `f` stays `x` (then
`machine_invoke` refuses the turn). `stepTo_run_moves`: the CEK machine returns exactly `inj y {}`
under large enough bounds, and no other value under any (`bigStep_run`, `run_bigStep`, determinism).
Helpers: `sel_toVal`, `find_keyed`, `sel_method`, `stepLaw_moves/keeps` (general over the closure's
origin), `mapM_ok_each/back`, `resolveEdges_mem/_back`, `methodIndex_inj`.

**How.** Over the reference semantics, compositionally: the `stepLaw` body is unfolded once, its
`case` arm is found by `find_keyed` (every arm is a function of its label) and the edge's target is
`stepTarget`, which `stepTo_takes_every_edge` pins to the declared `y` (the `ambiguousEdge` check makes
it unique). No term is evaluated by `decide` in the general theorems.

**Teeth (StdRun, kernel-evaluated machine runs of `apply4 0 m`).** `flip` (`a→b`, `b→a`): from `a` to
`b` and from `b` to `a` (not a constant); `n = 7` kept; `backOnly` (`b→a`): from `c` stays `c` (no
edge leaves `c` and none enters it); `fork` (`a -go→ b`, `a -stop→ c`): `go` lands `b`, `stop` lands `c` (the edge is the
invoked method's). HOSTING's `method_iff_step` is the deployed Lifecycle's evaluated instance.

**Critique.** (1) The bounds in `stepTo_run_moves` are existential: it does not say `Bounds.stackMax`
suffices (stated in the docstring). The receiver's metered run is what decides that per turn, and a
`stack` fault is a named refusal, never a wrong state. (2) The premise `lib[g]? = some (.record fs)`,
`Row.find? ℓm fs = some t` is how a package body holds a method (`pkgOf` builds exactly that); a
lemma deriving it from `pkgOf` and Load's relocation would close the chain to a loaded package
(cv 01a14edf-6505; the teeth meet the premises at lib[0]). (3) `sd` need not be of
type `S`: the theorem holds for any data with the field, which covers the receiver's `readState`
output as a special case.
**Meta-critique.** (1) could be closed by a derivation-depth bound (the derivation here is
constant-depth). It is not closed because nothing consumes it: the per-turn metered run already
refuses by name. If a consumer appears (a static admission that a machine method never faults
`stack`), that is the work, and it goes in a cv task then, not now.

Vacuity read (second agent, statements only, two passes): LAND-WITH-FIXES; fixed before landing: apply4
restatement, bounds docstring, distinguishing teeth (fork; backOnly run from `c`), stepTo_stays; the LOW
(premises from pkgOf/Load) is cv 01a14edf-6505. No
existing statement changed; no new premise on an existing theorem. No shipped byte moves.

## LANG-54 Std `quorum` and `windowed` run through the receivers as SURFACE laws (2026-10-18; LANG-16; LANG-12/13's owed journey rows)

**What.** lang-journey rows LQ1–LQ10 and LW1–LW8: two packages written in the surface, each with one
Std clause as its law (`(law shared (quorum value 2 #a #b))`, `(law rate (windowed value 64 2))`),
installed, created, invoked by methods and judged by the real receivers. Until now these laws were
proved (`Lang.Proofs.Std`) and run by `runLaw` on closed instances (StdTeeth) but never judged a
turn.

- quorum: propose 5; apply with no approvals and with one of two: `shared: no quorum`; A setting B's
  bit, and A approving twice: `shared: not an approval`; B (through a grant) approves and applies:
  value 5, approvals reset to 0.
- windowed: every call is signed with a window inside one epoch of 64 heights; two changes count
  1, 2; a third: `rate: rate limit 2`; an unchanged write is not counted; a window spanning two
  epochs: `rate: window spans epochs`; in the next epoch the count restarts at 1.
- Plants: skip-judge admits LQ5 and LW5.

**Critique.** The methods are deliberately permissive (`approve` adds whatever bit it is given,
`set` trusts its own epoch arithmetic): the rows test the LAW, and a method that pre-checked would
hide whether the law bites. A package a person ships would refuse in the method too, by name.
**Meta-critique.** That makes these demonstration packages, not world/ packages, so they stay inline
in the journey (like CappedTally's layer), not in `world/`. If a resident needs a shared setting or a
rate, the Bell's critique (2) is where `windowed` lands for real.
No theorem moves; no shipped byte moves.

**LANG-54 addendum (LANG-3's named rows, all now through the receivers).** LQ2b a birth with an
approval already counted: `shared: approvals at birth`; LQ9b with the quorum reached, a value other
than the proposal (`force 77` where 5 was proposed): `shared: not the proposal` (the proposal
binding); LQ11/LQ11b the relaw arm, on a DATA object governed by the same law: removing the law with
no quorum: `shared: no quorum` (skip-judge plant admits it); LW2b a birth claiming an epoch other than
its window's: `rate: epoch is not the call's window`.

## LANG-55 The receiver-admits chain loses three of its four stated gaps (2026-10-18; LANG-16; LANG-4's vacuity leftovers)

LANG-26's `judgeOne_pkgOf_admits` named what it assumed. Three of those assumptions are now gone:

- **Packages with imports.** `judgeOne_admits`: for ANY package `p` the pinned cell holds, with imports
  or without, `judgeOne` admitting means that both states read at `p`'s state type, and that every law
  label whose body field `t` has a law's shape `Admits` the transition AS LOADED, i.e. `t` relocated
  into the closure (one relocation `f` for the package, on `load`'s own `lib`). A law that names no
  closure package is its own relocation (`relocate_noRef`). So laws that do name imported packages
  are covered too. The proof goes through `load_top`. `load_leaf` is deleted: `load_top` subsumes it.
  The fuel is now named `closureDepthMax - 1`.
- **Distinct labels: a premise REMOVED.** `judgeOne_pkgOf_admits` and its three corollaries
  (`judgeOne_quorum_change`, `judgeOne_quorum_relaw`, `judgeOne_machine_invoke`) no longer take `hnd`.
  The receiver's own load re-ran the install check (`load_checked`), and a `pkgOf` package that passes
  `checkShape` has distinct labels, because its interface is a strictly ascending row
  (`pkgOf_labels_nodup`, `ascending_labels_nodup`).
- **The cell holds the package.** `readPackage_installed`: a package cell whose slot 0 holds
  `encodePackage p` reads as `p` (`decodePackage_eq_ok_iff`: the codec is canonical).

**Changed statements.** `judgeOne_pkgOf_admits`, `judgeOne_quorum_change`, `judgeOne_quorum_relaw` and
`judgeOne_machine_invoke` each LOSE the premise `hnd` (a strengthening). Their conclusions are
unchanged. `load_leaf` is deleted; it had no other user. No existing theorem gains a premise.

**Still assumed, by name.** (1) The digest round trip. This is the lawful `Ctx` (LANG-46): KERNEL's
law, not LANG's. (2) That a World's package cell holds bytes that `install` checked. This is KERNEL's
admission invariant, and the receiver's load re-checks anyway. (3) A layer's laws reach the layer's
body through `extend (ref 0)`. They are not fields of the layer's own record, so `judgeOne_admits`
reaches them at the super package, not at the layer.
**Critique.** (3) is real for surface layers. LANG-50's `layer_keeps_laws` covers it on the surface
side. The receiver side needs `Sel` through `Ext` over a relocated `ref`, and nothing consumes it today:
no deployed package is a layer.
**Meta-critique.** (3) is not deferred silently: cv 01a14ef6-598d (trigger: the first deployed layer).
The vacuity reader's first pass found that `pkgOf_labels_nodup` was a bridge nothing crossed while
`hnd` stayed a premise. The fix was to derive `hnd` from the load and remove the premise, not to keep
the lemma beside it.

Teeth: the install check refuses a `pkgOf` with a repeated label and accepts one with distinct labels.
So `pkgOf_labels_nodup`'s premise is neither vacuous nor universal.

## LANG-56 A printed value is one line: the printer shows a byte string as text only when every character is plain (2026-10-18; LANG-16; PROTOCOL-13's open item after PROTOCOL-48)

**The defect (measured by reading `Print.bytesSx`).** A byte string that is UTF-8 with no `"` printed as a
string literal VERBATIM, line feeds included. PROTOCOL-48's `read OBJ` prints a programmed object's state
as `Print.data` plus one newline, and a resident reads `nd --stdio` replies by lines. The Bell's `answer`
is a model's reply, so it will hold line feeds: the reply would have spanned lines, and "one line" was
true only for the rows' sample values.

**Decision.** `Print.plainChar c := 32 ≤ c.toNat ∧ c.toNat ≠ 127 ∧ c ≠ '"'`. `bytesSx` prints `"text"`
only when every character is plain, and `#hex` otherwise. The reader is unchanged: it reads both. So
`readData_data` (print, then read, gives the same value) holds as before, and its proof changed in one
pattern (`bytesSx_cases` gains a conjunct: every character is plain). New module
`Lang/Proofs/PrintLine.lean`: `data_one_line`, which says `Print.data`'s text holds no line feed and no
carriage return. It comes through `chars_noBreak` (an `Ok` form whose strings are plain prints no line
break; an atom is delimiter-free, so no whitespace) and `dataSx_plain`.
Teeth: `"a\nb"` prints as `#610a62`; `"a b"` prints as itself.

**Shipped texts.** Lifecycle, Allowance, Escrow and the Bell print byte for byte as before (G0/G0s,
A0/A0s, E0/E0s, LB0 all pass). None holds a control character in a byte literal. Rows `state` and
`describe` pass. No package BYTES move: the printer is outside the wire.

**Critique.** A reply with line feeds is now hex in `read OBJ`, which is unreadable to a person. The
resident reads it with `Lang.Read.readData`, which is what PROTOCOL-48 ruled anyway (no hand decode).
An escape syntax inside string literals (`\n`) would keep it readable, but it is a READER change: a
second spelling of the same bytes, plus a proof obligation on every string. **Meta-critique.** The
reader stays as small as it is; if people need to read answers by eye, `ob` can render, outside the TCB.

**LANG-53 addendum (cv 01a14edf-6505 closed).** In Lang/Proofs/StdRun.lean, `stepTo_loaded` covers a `pkgOf`
package the pinned cell holds whose method `ℓm` is a `stepTo` output. It shows that the closure the
receiver's own `load` returns (runSetup's exact call) holds, at `load`'s index, a record whose field `ℓm`
is that method. So the `lib[g]`/field premises are derived and no longer assumed. They come from:
- `load_top`;
- `load_checked` with `pkgOf_labels_nodup`, so the labels are distinct;
- `noRef_stepLaw` with `relocate_noRef`, so relocation leaves the method unchanged.

`stepTo_moves_loaded`, `stepTo_keeps_loaded`, `stepTo_stays_loaded` and `stepTo_run_moves_loaded` are the
four run-level facts on `L.lib` with `apply4 g ℓm`. `stepTo_invoke_loaded` covers the case where the
generator's methods are the package's own and the method is installed under its own label. There, the
index `stepTo` resolved `m` to (the one the machine law compares an invoke with) is where the package's
method list holds `m` (`methodIndex_pkgOf`), and invoking it lands at the edge's target. Vacuity reader:
LAND. Both of its optional LOW follow-ups (the other three facts in loaded form, and the index tie) are
done here.

## LANG-57 A relation's keys list in their declared order: a natural in Lang data is big-endian, and key-byte order is a theorem about fields (2026-10-19; ROOT APPROVED 2026-10-19, ROOT for CODEC; LANG-17; PROTOCOL-16's FINDING on PROTOCOL-51, cv 01a14f18-b8c8; blocks cv 01a14ece-43f1, the Bell as a queue)

**The defect (measured by reading `Lang/Wire/Data.lean:53` and `Codec/Stream.lean:124`).** A key's bytes are the data
encoding of its fields in declared order (`Lang.Rel.keyBytes`, LANG-49). A natural is written `Stream.u64`:
eight bytes, LITTLE-endian. The kernel's range read lists rows in strictly ascending key-BYTE order
(`range_rows_exact` (ii), `Kernel/Proofs/RowsRange.lean:604`; MSB-first, CODEC-29). So a relation keyed
`(n nat)` lists 0, 256, 512, …, 1, 257, …: 256 lands between 0 and 1. Every ordered use of a nat key is wrong
past 255 (the Bell's rings, any log, any "next id"), and nothing says so: the only order statement is about
bytes, and no statement relates it to the fields.

**Census of key field types (`Lang.keyFixed`, `Package.lean:340`), what each encoding does to order:**
- `nat` → u64 LE: WRONG (the defect).
- `bool` → one byte 00/01: false first. Right.
- enumeration (a sum of `rec {}` arms) → one tag byte = the arm's index; a canonical type's arms ascend, so arm
  order = label order. Right.
- `digest` → `u32 len (LE) ‖ bytes`. `digestBytesMax = 32 < 256`, so the LE length is `[n,0,0,0]` and its
  bytes compare as `n`: shorter first, then bytewise (shortlex). A total order, and the only one a digest has.
- record → its fields' encodings concatenated. Lexicographic product, PROVIDED two different field values never
  have one encoding a proper prefix of the other: true (fixed width per type; two digests of different length
  differ at their first byte).
So ONE encoding is wrong, and fixing it makes key-byte order the field-wise lexicographic order with no
premise at all.

**Decision.**
1. **CODEC primitive (ROOT for CODEC):** `Stream.u64be : Stream UInt64`, eight bytes most significant first,
   new `Shape.u64be` with tag code 19 in `Shape.put` (`Shape.put_prefix` extended, as CODEC-35 did for u16),
   `u64be_lawful` beside `u64_lawful`. Not a `refine` of `u64` through a byte swap: a refine keeps the inner
   Shape, so the tag would claim `.u64` (LE) for big-endian bytes, a shape that lies.
2. **Lang data's natural is `u64be`** (`dataStream .nat := Stream.u64be`). `DataAt .nat` stays `UInt64`;
   `toData`/`ofData` do not change. Key bytes stay EXACTLY the data encoding (one codec, one decoder:
   `keyOf` still reads through `decodeData`). Values and state slots move with it (see flag day): there is
   one encoding of a Lang natural as data, not a key one and a value one.
3. **The order, as a theorem** (new def `Lang.keyCmp : Ty → Data → Data → Ordering` in Lang/Rel.lean, the
   declared order: a natural by value, `false` first, an enumeration by arm index, a digest shortlex, a record
   field by field; `keyRowCmp` over the declared key fields), in new leaf `Lang/Proofs/KeyOrder.lean`:
   - `keyBytes_compare`: `keyBytes d k = some b → keyBytes d k' = some b' →
      compare b.data b'.data = keyRowCmp d.key k k'`. (As built: one premise, every key field fixed-width,
      which installation supplies; see "As built".)
   - `range_keys_ascend` (the queue's statement, composing `range_rows_exact`): in a range read the kernel
     returns for one relation, the keys `keyOf` reads (rangeRowData's path) are strictly ascending in
     `keyRowCmp`. (All rows under one `rowsPrefix … width` have keys of exactly `width` bytes, so
     `compare (rowKeyBytes …)` reduces to `compare` of the key bytes: no new premise beyond
     `range_rows_exact`'s own.)
   - Teeth: see "As built".
4. **Vectors (ROOT for CODEC, both table rules hold).** The package wire holds NO data (Ty, Term, RelDecl
   only; term literals are `Lang.Wire.u64Bytes`, unchanged), so `lang/package` does NOT see this change —
   the brief's assumption is wrong, and today no vector pins data bytes at all. New site `lang/key`
   (`Tag.of "lang/key" (dataStream keyVecTy)`, not a refine: its shape is all primitives, so the tag itself
   sees the natural's wire; one fixed declaration `(n nat) (f bool) (d digest)`) with rows: k0 = 0, 1, 255, 256, 2^64-1 (bytes visibly ascending),
   a `k2` of 31 vs 32 bytes, and the boundary row (a key cut one byte short, refused `truncated`). Rule 1 (re-draw
   only where the tag moves): no existing site's shape contains `dataStream`, so no existing row moves; the
   new site is drawn fresh. Rule 2 (unchanged tag ⇒ unchanged decoded text): vacuous for existing rows.

**Premise spread (statements that name key or data bytes), all re-checked, none gains a premise:**
- Lang: `dataStream_lawful` (Proofs/Data, nat case `u64be_lawful`), the decoder-conformance theorems built on
  it, `keyOf_keyBytes`/`_fields` (Proofs/Rel), `keyOf_conforms`/`_key` (Proofs/Invoke), `editOf_spec`,
  `editOf_amt`, `valOf_decodes`, `relReads_points`: all state over `keyBytes`/`encodeData`/`decodeData`
  symbolically; texts unchanged, proofs re-run. Concrete bytes: `Lang/Journey.lean` builds keys through
  `keyBytes` (symbolic); any journey row printing hex of a nat datum re-pins (listed at landing).
- Kernel: none. `rowKeyBytes` carries key bytes as given (KERNEL-46); `range_rows_exact` is about bytes.
  `Kernel.Sim.dc = Stream.u64` (the toy digest) is a different codec and does not move.
- Codec: `Shape.put`, `Shape.put_prefix` and every exhaustive match on `Shape` (Codec/Tag, Codec/Proofs/Tag,
  Census/Refines) gain one case. `u64`, `nat64`, the World wire: unchanged.
- PROTOCOL-51 (in flight): its theorems are over `rangeRows`' list and `Lang.Print`; texts unchanged.

**Flag day (`lang!`).** What changes bytes: every Lang datum holding a natural — object state slots,
row values, row KEYS, method arguments (`Program`'s call data) — so every World holding a programmed object
with a nat re-geneses (devnet re-genesis; sims rebuild their Worlds). What does NOT: package bytes and ids (no
data in the wire), every shipped text (G0/G0s, A0/A0s, E0/E0s, LB0 compare texts), every kernel/codec vector
(no site contains dataStream). What refuses: an old data blob with a nat decodes at the wrong value (same
width — it is NOT refused, it is misread). Accepted because nothing holds old data (greenfield); the
re-genesis is the refusal. New vectors: the `lang/key` site.

**Critique.**
- (a) The alternative "keep data LE, write KEY bytes with a second, big-endian key codec" keeps value bytes
  but makes two encodings of one `Data` and two decoders (`keyOf` would stop being `decodeData`), which is the
  twin the repo keeps deleting. Refused.
- (b) "A fixed-width big-endian `seq` type for ordered keys": a new `Ty` constructor through the checker,
  machine, reader, printer and surface, and `nat` keys would STILL misorder silently. Refused.
- (c) "A digest key with no order" gives up the queue. Refused.
- (d) The term wire's natural literal stays LE (`u64Bytes`, a `Codec.Tree` payload, never ordered, like
  every kernel number). So Lang has two spellings of a natural: data (ordered, BE) and term literal (LE).
  Changing the literal too would re-id every package and re-draw 43 `lang/package` rows for consistency
  alone; not proposed.
- (e) A blob written under the old wire reads as a different number instead of refusing. The re-genesis is
  what makes that harmless; there is no in-band epoch on Lang data. Named, not fixed.
**Meta-critique.** (d) is the place this could be wrong: "two spellings that agree today will disagree
later" is the repo's rule, and here they already disagree by design. The defence is that they are
different wires (a term payload vs data) with no function that moves bytes between them; if one ever
appears (a literal compiled into a stored datum by bytes), the literal moves too. And the order theorem is
the real deliverable: without `keyBytes_compare` the BE switch would be one more byte fact nobody can rely
on; with it, "ring order" is a statement a resident's reader can cite.


**As built (what changed from the proposal).**
- `Codec.Stream.u64be` + `Shape.u64be` (tag 19) + `u64be_lawful` (Codec/Proofs/Stream.lean); new
  Codec/Proofs/Order.lean: `compare_append` (lexicographic order cuts at a common length),
  `u64be_compare` (two values' bytes compare as the values), teeth `u64_misorders` (under `u64`, 256's
  bytes come before 1's) and `u64be_orders_1_256`.
- Lang/Rel.lean: `keyCmp`/`keyRowCmp` (a field value's order) and `keyOrder` (declared order). New leaf
  Lang/Proofs/KeyOrder.lean: `dataCmp`/`rowCmp` (the encoding at a fixed-width type, followed by
  anything, compares as `keyCmp` then the rest), `keyBytes_compare`, `keyBytes_compare_installed`,
  `range_keys_ascend` (on `range_rows_exact_of`'s premises: one digest size n ≤ 32, injective bytes —
  weaker than `Env.Lawful`, so the toy below satisfies it), and after the vacuity read: `keyBytes_keyOf`
  (the converse of `keyOf_keyBytes`, at a canonical key type) and `range_keys_ascend_read` (the keys the
  READER decodes, `rangeRowData`'s path, are strictly ascending, for an installed relation; a row whose key
  does not decode is outside the statement, and `rangeRowData` refuses the whole read on it). Teeth:
  `key_order_1_256`, `key_order_declared_first` (declared order, not label order),
  `key_order_digest_shortlex`; on a concrete rows trie (ring 256 inserted first) `queue_lists_1_first`
  against `le_queue_lists_256_first` (the old little-endian key bytes list 256 first: the key-level
  refutation of the old wire), `queue_key_bytes_1_256` (bytes computed by `decide`, not through
  `keyBytes_compare`), `range_keys_ascend_read_satisfiable` (every premise met on that trie, the read's
  two keys `.lt` from the theorem).
- **Correction to "no premise".** `keyBytes_compare` takes `d.key.all (keyFixed ·.2)`: a `bytes` key
  field (length is a 4-byte LE u32 up to bytesMax) would NOT be order-preserving, so the theorem is false
  without it. It is exactly the check `checkRel` makes at install, so `keyBytes_compare_installed` takes
  `checkRel S row (ℓ, d) = .ok ()` instead: no premise beyond installation. `range_keys_ascend` takes
  `range_rows_exact`'s own premises plus the same one.
- **The LE form cannot be "refused by name"**: every eight bytes are some `u64be`, so a little-endian
  blob decodes, to a different number. The tooth for the old wire is the theorem `u64_misorders`; the
  `lang/key` site's refused boundary row is a key cut one byte short (`truncated`).
- `lang/key` site: 8 rows (k0 = 0, 1, 255, 256, 2^64-1; a 31-byte digest; `true`; the cut key). 199
  vectors / 52 sites; `--check` ok; no existing row moved (`git diff` adds 8 lines only).
- Measured on the candidate: lang-journey GREEN; ledger-sim, hosting-sim 1-3, host-sim 1, kernel-sim 64,
  rows and rows --deployed ALL PASS; every generated table `--check` rc 0. **Nothing re-pinned**: no
  journey row, sim row or vector pinned the bytes of a Lang natural (the reason the `lang/key` site was
  needed). Shipped texts (G0/G0s, A0/A0s, E0/E0s, LB0) byte-identical; package bytes and ids unchanged.
- The term wire's natural literal (`Lang.Wire.u64Bytes`) stays LE: the term wire is never ordered (no
  function compares package bytes, and no bytes move from a term payload into data). ROOT accepted it
  for now; cv 01a14fe9-784c moves it at the next `lang!` that re-ids every package anyway.

**Build order (done):** CODEC half (u64be, Shape 19, lawful, put_prefix) + Lang half (dataStream, keyCmp,
KeyOrder.lean, the `lang/key` site) in ONE `lang!` commit with `--cross-layer` for Codec/ + Emit/Vectors
+ gates/codec-vectors.tsv (ROOT stands in for CODEC). Then the Bell as a queue (cv 01a14ece-43f1) once
PROTOCOL-51 lands.

**Vacuity read** (a383cd00e4775b730): LAND-WITH-FIXES, none vacuous; fixes done: the read-side form
(`keyBytes_keyOf`, `range_keys_ascend_read`), a concrete instance of the range theorem, the key-level LE
tooth, a direct byte tooth. Not done (optional): keyOrder as a strict total order corollary.
**Finding, not acted on (a check, so a pause item):** `checkRel`'s `decide ((Row.sort d.key).length =
d.key.length)` is always true (`Row.sort` is a permutation, `Row.length_sort`): it checks nothing.
Distinct key labels are enforced by `(keyTy d).wf` (sorted strictly ascending), which `keyBytes_keyOf`
uses. Reported to ROOT.

**LANG-57 addendum: the always-true key check is deleted, with its fact as a theorem (ROOT's ruling, 2026-10-19).**
`checkRel` held `decide ((Row.sort d.key).length = d.key.length)`, which is true of every list (`Row.sort` is a
permutation, `Row.length_sort`): a gate that could not go red, and its presence told readers that key-label
distinctness was checked there. Distinctness was already enforced by the next conjunct, `(keyTy d).wf`: the sorted
key fields must strictly ascend. ROOT ruled "replace, not merely delete; pick by which leaves one check". A new
`keyLabelsDup` check would be a twin of `wf`, so the honest move is the deletion WITH the fact: `checkRel_key_nodup`
(Lang/Proofs/KeyOrder.lean): `checkRel S row (ℓ, d) = .ok () → (d.key.map (·.1)).Nodup`, through `wf` alone. Plant:
`checkRel_refuses_dup_key_label` (a key declaring `n` twice is refused `relKey "r"` by name) against its twin
`checkRel_admits_distinct_key_labels`. No verdict moves (the deleted conjunct was always true), nothing re-ids,
nothing re-emits; `checkRel`'s docstring now names where distinctness comes from. Proofs that destructured the
conjunction re-indexed (`keyBytes_compare_installed`, `range_keys_ascend_read`); no statement text changed.

## LANG-58 The Bell is a queue of rings: `pending` is the cursor, a ring is keyed by its signed notBefore and its ringer, and nothing a ring or an answer writes is the bell's cell (2026-10-19; ROOT APPROVED Q1-Q4; LANG-18; cv 01a14ece-43f1; HOSTING-10's requirements; with HOSTING-11's resident cut-over, HOSTING-31)
**What.** `world/resident/Bell.ob` (2,367 chars, of which 390 are its header comment) and its core
`world/resident/Bell` (31,542 chars; 24,906 package bytes) replace LANG-52's state-only bell.

    state   (rec (open bool) (resident digest))
    rel answers (notBefore nat)(ringer digest) -> (rec (text bytes))  limit 1024  retract  guard said
    rel pending (notBefore nat)(ringer digest) -> (rec (text bytes))  limit 64    retract  guard queued
    rel rings   (notBefore nat)(ringer digest) -> (rec (text bytes))  limit 1024  retract  guard rung
    ring   {text 1..2000}            closed unless open; inserts pending[k] and rings[k], k = (req.notBefore, req.agent)
    answer {notBefore ringer text}   notResident unless the agent is the resident; inserts answers[k], retracts pending[k]
    retire {notBefore ringer}        retracts answers[k] and rings[k]
    open / close                     as before
    guards  rung: insert ringer = agent ("notYours"), upsert "final" | queued: insert ringer = agent, retract by the
            resident ("notResident"), upsert "final" | said: insert by the resident, upsert "final"
    law bell  an invoke keeps resident ("resident")

**The key (ROOT Q1).** A state counter makes `ring` write the bell's cell, so two rings over one view collide (the
second is stale, declined, re-signed): it gives up LANG-44's acceptance row, and a `lo` in state would make every
answer collide with every ring too. A {ringer, nonce} key commutes but orders by digest: the smallest digest is
served first, always. `(notBefore, ringer)` commutes (LB5c: two rings over one view, both orders, equal rows and
cells roots) and orders by admission to within the kernel's window, since `notBefore ≤ h+1 ≤ validUntil ≤
notBefore + windowMax`: **a ringer can jump the queue by at most windowMax = 1024 heights; ties at one height break
by ringer digest; one ringer twice from one view is `keyTaken`.** The clock is the one Std `windowed` uses. The key
field is named `notBefore` so `read BELL ?`'s rel line says which clock it is (a package doc line is cv
01a15078-f528). Rejected: a kernel-supplied admission height in `Req` (exact order, but an unpinned input to every
method and a height premise on `receive_congr`).

**The cursor is a relation, not a number (ROOT Q4).** A range prefix is exact-match (Lang.preBytes), so a state
low-water mark cannot start a read at itself; answered rows at the front of `rings` would hide new rings from any
K-row read. `pending` is exactly the unanswered rings: `read BELL pending 64` lists them lowest first (LANG-57's range_keys_ascend; LB6
checks the order and the digest tie at one height, at heights under 256, so it is not itself evidence for
big-endian), and answering removes the ring from it (LB7). The read refuses past K (`rangeTooLong`, never
truncated), so the resident reads K = pending's described limit.

**Exactly once, twice.** An answered ring has no pending row: answering it again is refused `missingRow` (LB8; the
KERNEL-54 name for a retract of an absent pinned row). Two answers over one view both pin pending[k]: the second
is `stale` (LB8b). And answers[k] is an unpinned insert, so a second one is `keyTaken` (LB13g: a layer's
`say`, which files answers[k] with no pending row, twice: the kernel's lock alone). No answer is changed IN PLACE:
answers and rings refuse upsert by GUARD, which no layer can override (LB13e `said: final`), and only the resident
inserts an answer or retracts a pending ring (LB13c `said: notResident`; LB13c' plants both guard arms open and the
same answer is admitted). An answer can be RETIRED (retire, or a layer method: any signer may retract answers and
rings rows), and a retired key can be rung again inside its window; that is a new ring at a reused key, not a
rewrite of the old answer, which is gone.

**No row read in any method (ROOT Q2).** `answer` and `retire` compute keys from their arguments and read nothing.
Invoked without pins, `answer` is refused `rowUnpinned` naming the key (LB7u); nd's `derivePins` (PROTOCOL-17, on
the KERNEL-54 day) pins that row and re-plans. So the resident passes arguments only.

**Bounded.** pending 64: a ring past it is `relationFull` (LB11), the old `busy` at depth 64. rings 1024: past it
a ring is `relationFull` until the owner retires answered rings (who may retire is the grants'). Retiring a pending
ring is refused `missingRow` on answers[k] (LB10b). Text 1..2000 by the bounded argument (LB9b). Held twice: a
pending ring's text is in pending and rings, at most 64 × 2000 B, both final (HOSTING-10: one read per tick, text and
cursor from one listing).

**Measured.** ring: 77 required steps / 116 ticks; answer: 77 / 116 (lang-journey LB4, LB7). THE BAR round stays
2 writes (one ring, one answer), neither touching a cell. Rows per ring 2 inserts; per answer 1 insert + 1 retract.

**Critique.** (1) The order is window-coarse and signer-influenced, by up to 1024 heights: a fairness bound, not
FIFO. (2) "retire takes answered rows only" holds against a layer for answers[k] (missingRow) but a layer method
can retract rings[k] alone, or retract a pending ring as the resident: a guard does not see the old row (LANG-49
critique 3). LANG-59 (guards see the pinned old row) is its trigger. (3) The surface is 1,977 chars without its
comment, over the 1,500 target: ~600 are the guards, which are the layer-proofing; a guard macro is a LANG-50
follow-up. (4) The owner must retire, or the bell stops taking rings at 1024 (RUNBOOK, OPS). (5) The text held twice
is two copies of one value written by one method, neither changeable in place; a layer method may retract one copy
and a ringer re-insert it with other text, so they agree only through the Bell's own methods (LANG-59 again). Likewise, on a layered object answers ⊄
rings: a layer method may file an answer to a ring never rung (LB13f); only the Bell's own methods keep
pending ⊆ rings, answers ⊆ rings and pending ∩ answers = ∅.
**Meta-critique.** The sketch I inherited (counter + lo) carried HOSTING's authority; the read path (an exact-match
prefix cannot start at lo) refuted it before any taste did. The `notBefore` clock is a precedent; I checked that it
is sound (signed, kernel-bounded, re-derived identically by an auditor), and that being a precedent does not make it
a good queue order: the 1024-height bound is the price, stated in the decision and in the text's header.
**Flag day (`lang!`).** world/resident/Bell(.ob) re-emit; the Bell's package id changes; LB0's byte-identity row
re-pins with the reason "the Bell became a queue"; the LB rows are re-cut (LB0-LB13). The resident (Hosting/Resident,
launcher/tests/resident_bell.rs) cuts over in the same commit (HOSTING-11, HOSTING-31). An old Bell object's state does not read
at the new state type; every Store re-geneses on the KERNEL-54 day anyway.

## LANG-59 A guard sees the row its edit replaces; the Bell's exactly-once is a guard on one relation; term literals go big-endian (2026-10-20; ROOT APPROVED the design, Q1 yes, Q2 = (B); LANG-18 proposed, LANG-19 built; cv 01a150a4-27ee, cv 01a14fe9-784c; with HOSTING-11's resident cut-over)
**What.** A relation's guard has type `S -> Req -> guardInTy d -> Verdict` with
`guardInTy d = rec {edit : relEditTy d, old : optTy d.val}`: the arity stays 3, so the one law runner
(`runLaw`, apply3) runs guards unchanged. `old` is the row now at the slot the caller pinned
(`Lang.pinAt`, read through the receiver's `RowView`): a pinned-absent slot is `none`, a pinned row is its
value read by `valOf` (the conversion
`relReads` uses), an insert with no pin is `none`. An upsert or retract with no pin has no old row:
`guardOld` refuses it `rowUnpinned parent rel key`, the refusal and key the receiver's `rowTouchesOf`
gives. `guardEdits` finds EVERY edit's old row before it runs ANY guard, so a caller deriving pins from
refusals learns each row whatever a guard would say (journey LB7v: the answered ring with only `rings`
pinned is refused `rowUnpinned` at `pending`, not `rung: answered`). The surface binds a guard's
`state req edit old`; it lowers to `(lam edit GIn (let old (option V) (. edit old) (let edit RE
(. edit edit) BODY)))`, one binder name for the record so no fresh name can capture a user's. `old` is
the row as the World holds it at the pin: when the pin is stale the guard judges the current row, and a
refusal comes before the kernel's `stale` (LB8b).

**Folded in (ROOT Q1, cv 01a14fe9-784c).** A natural in the package wire (a term literal, a relation's
limit and cap) is `Stream.u64be`, as Lang data's is since LANG-57: one encoding of `nat` in both Lang wires.
The refine is renamed `lang/package/2` (its content tag moves; codec-vectors re-drew exactly the 43
`lang/package` rows, now under the site `lang/package/2`, which the census requires to carry the refine name; nothing else moved).

**The Bell (ROOT Q2 = (B)).** Answered-ness moves into the row a guard sees. `answers` is deleted.

    rel pending (notBefore nat)(ringer digest) -> (rec (text bytes))                         limit 64    guard queued
    rel rings   (notBefore nat)(ringer digest) -> (rec (answer (option bytes)) (text bytes)) limit 1024  guard rung
    ring   {text 1..2000}                          inserts pending[k] {text} and rings[k] {answer none, text}
    answer {notBefore ringText ringer text}        notResident unless the resident; upserts rings[k] {answer some text,
                                                   text ringText}, retracts pending[k]; reads no row
    retire {notBefore ringer}                      retracts rings[k]
    rung   insert: ringer = agent ("notYours"), answer none ("answered")
           upsert: agent = resident ("notResident"); old present ("unrung"); old.answer none ("answered");
                   new text = old.text ("text"); new answer some ("unanswered")
           retract: old present ("unrung"), old.answer some ("unanswered")

Exactly once is now ONE guard over ONE relation, layer-proof: a second answer is `rung: answered` (LB8),
also over one view (LB8b), also through a layer that skips `pending` (LB13e). Retire takes only an answered
ring (LB10b; a layer's `drop`, LB13f). A ring cannot be inserted already answered (LB13g), and an answer
must send back the ring's own text (LB8t): the resident re-sends it (bounded 1..2000), so no method reads a
row. `pending` stays the cursor: a range read cannot filter by value. LB13' plants `rung` open (and
`queued`'s retract) and all four takeovers are admitted, so each refusal is the guard's.

**CoAuthor.** `proposals` gains `authored`: an insert's author is its signer, and an upsert may not change
the author (the method checked both, so a layer could not be stopped): LS12, a layer's `steal`, and LS12i,
a layer's `forge` filing a proposal under another's name, are refused `authored: author`; LS12' (both arms
planted `ok`) admits both. CappedTally: unchanged in meaning, its hand core re-written for the new iface
type (LT0s holds byte for byte).

**Statements restated, no new premise** (the reader's list; second-agent read with the disjunct check by
a383cd00e4775b730: LAND-WITH-FIXES, all applied: `authored`'s insert arm (M1, LS12i), the words "the row
now at the slot" (L1), `guardEdits_unpinned` strengthened to x's own key (L2), the tooth
`guardOld_pinned_row` (L3); no theorem vacuous, no premise added; `hol` covers every guard run). `guard_run_ok`, `guard_never_stuck`: `Conforms e (relEditTy dl)` -> `Conforms e
(guardInTy dl)`. `guardEdits_never_stuck`: binds `hol : es.mapM (guardOld digestOf rv r.self) = .ok olds`
(guardEdits' own first pass, the computed input, not a premise on package or World) and concludes over
`q ∈ es.zip olds` with `guardIn q.1.data q.2`, exactly the runs `guardEdits` makes. Provenance's four
past-extraction equations: `guardEdits` gains `digestOf … rv`. Wire: `lang/package/2`. The tooth term
`caseGuard` reads `.edit`. The 85 law theorems (Std, StdTeeth, Receiver, LawRun, StdFits): no file touched.
New: `guardOld_conforms`, `guardIn_conforms`, `mapM_zip_ok`, `guardOld_unpinned`, `guardEdits_unpinned`
(for edits `pre ++ x :: post` whose `pre` all have old rows, an unpinned upsert/retract `x` makes
`guardEdits` refuse `rowUnpinned` at x's own parent, relation and key, whatever any guard says),
`except_map_ok`, `mapM_prefix_error`; teeth `freshGuard_reads_old` (one edit, two old rows, two verdicts:
`old` reaches the guard), `guardOld_pinned_absent`, `guardOld_pinned_row` and `guardOld_unpinned_witness`
(none, some, refused).

**Measured.** ring 79 required steps / 120 ticks (was 77 / 116), answer 96 / 143 (was 77 / 116): answer now
builds an option and a two-field value; retire edits one row. Required steps count the method run and its
extraction; guards run under `lawTicks` and are not in them, so CappedTally's and CoAuthor's rows do not
move. Bell: 2,876 chars of surface, core 27,679 chars, 21,780 package bytes (was 31,542 / 24,906).
bench-worstcut's rows tail: 24.892 trie-hashes per step (reopen and audit); the worst stays 33.938 (retires).

**Critique.** (1) The guard sees the CURRENT row at a pin, not the pinned version: a stale answer is refused
by the guard, never reaching `stale`; the verdict is the same (no write), the name differs, and a resident
must read `rung: answered` as "already done". (2) The pin requirement is checked twice, by Lang (the old
row's existence) and by the kernel (admission); one fact, two statements, by design: the alternative is a
guessed `none` that would refuse ahead of the receiver. (3) Guards stay O(one edit) of one relation: a
cross-relation fact (pending ⊆ unanswered rings) still holds only through the Bell's own methods; the
resident may retract `pending[k]` without answering through a layer, leaving a ring unanswered and off the
cursor (resident-only). (4) An old package's bytes decode under u64be as a DIFFERENT package rather than
refusing: only the re-genesis makes that moot (as at LANG-57); a wire version byte would make it refuse.
(5) The answer re-sends up to 2,000 bytes it does not change.
**Meta-critique.** LANG-58 and the brief assumed "the guard sees the old row" closes the Bell's layer gaps;
reading what each gap reads refuted it (they were cross-relation). (B) is justified without a layer: one
relation fewer, one guard for exactly-once instead of two locks, and no row read in any method.
**Flag day (`lang!`).** Every package re-ids (term literals u64be): Escrow, Lifecycle, Allowance, CappedTally,
CoAuthor, the Bell, THE BAR's counter. Guarded packages' iface type changes (CappedTally, the Bell, CoAuthor
gains a guard). Re-emitted: world/resident/Bell(.ob) (LB0 re-pins: "answers live in rings; a guard sees the
old row"); the `lang/package` vectors (codec-vectors --write, tag moved). The other shipped cores
(Escrow, Lifecycle, Allowance; E0s/G0s/A0s) hold no guard, so their TEXT is unchanged and --write-text
writes nothing; their ids move. Refused now: an unpinned upsert/retract, `rowUnpinned` by Lang before any
guard; a guard written at the old type, `badRel` at install; the guards' own refusals by name. The resident
(Hosting/Resident, launcher/tests/resident_bell.rs) cuts over in the same commit (HOSTING-11), and
bench-worstcut's rows tail (PERF-9) and PROTOCOL's bell row (an answer to a ring nobody rang is now
`lawDenied` by `rung`, was `missingRow`) with it. Stores re-genesis.

## LANG-60 The package wire has a version; a package says one line of itself (2026-10-20; ROOT ruled both parts into one lang!; LANG-19 found the reinterpretation, LANG-20 built; cv 01a15078-f528; CODEC-14 reviewed the codec hunks; PROTOCOL-19 the describe line)
**Why.** Under LANG-59 an old (LANG-58) package's bytes DECODED as a different package (big-endian
literals): a reinterpretation, which CLAUDE.md's rule forbids ("make the old shape refuse to load").
Only a re-genesis made it moot. Now the wire itself refuses.

**What (1): the version.** A package's bytes are `u8 packageWireVersion ‖ tree` (`Lang.Wire.packageStream
= product packageVersion treeStream`). `Lang.Bounds.packageWireVersion = 3`, bumped by every `lang!` that
changes what package bytes mean. Any other first byte is refused `lang/package-version` by name before
a tree is read (`packageStream_get_wrong_version`, `decodePackage_wrong_version`, `_not_ok`,
`packageCodec_wrong_version`), at install too (`checkInstall` decodes first: `refused program "decode …
rejected 0 \"lang/package-version\""`). Every package written before LANG-60 was a node-0 tree (first byte 0)
and no version may be 0 (`packageWireVersion_ne_zero`), so all of them refuse (`treeStream_bytes_node0`,
`unversioned_package_refused`). The twin: `encodePackage_version` (what is written begins with the
version). The package refine is `lang/package/N` at version N, a literal the refine census sees, tied
to the constant by `packageCodec_label` (bump one without the other and the build is red), so the vectors'
tag moves with the version (CODEC-14: a refine's shape carries its name, never its accept function).
The labels `lang/package` (the unversioned pre-LANG-59 wire) and `lang/package/2` (LANG-59) are retired.

**What (2): the doc.** `Package.doc : ByteArray` (default empty), `Bounds.docOk`: at most `docMax = 256`
bytes of UTF-8 `docChar`s (printable, no control character, no `"`: the one printer's `plainChar`,
`docChar_eq`), so a doc always prints as `"text"` on one line. Wire: an eighth child of the package tree,
`node 0 doc []`; `packageOf` refuses a doc that is not `docOk` (`lang/package/N`). Text: a core package
always has the section after imports, `(doc)` for the empty doc and `(doc "text")` otherwise; the reader
refuses `(doc "")` and any doc that is not `docOk` as `badDoc` (one spelling per doc;
`readPackage_package` holds with no new premise: printing succeeded means the doc is `docOk`). Surface:
`(doc "text")`, once (`duplicate`); a layer's doc is its own. Describe (PROTOCOL's file, agreed):
`read OBJ ?` prints `doc "TEXT"` first, before `state`, and no line for the empty doc
(`packageLines_doc`: the line is there, one line, and `Read.parse` + `Read.doc` read it back as the doc;
`docLines_empty`). The doc is never run and never judged: required steps do not move.

**The Bell** now states what LANG-18 could not: `(doc "A ring is answered once, by the resident, with its
text sent back; a ringer can backdate by at most the kernel's window (1024 heights); ties at one height go
by ringer digest.")` (175 bytes; journey LB0d: prints as one line, reads back, names the window and the
tie; one past docMax refused `badDoc`).

**Flag day.** Every package re-ids (the version byte and the doc child): Escrow, Lifecycle, Allowance,
CappedTally, CoAuthor, the Bell, THE BAR's counter, every journey and rows package. Re-emitted: the
shipped cores (`ledger-sim --write-text`, `hosting-sim --write-text`; the Bell's core by its surface),
`gates/codec-vectors.tsv` from an empty file (only `lang/package/2` → `lang/package/3` and the new
`lang/package-version` moved). Refused: a package at any other version (`lang/package-version`), a doc
past its bound or not `docOk` (`lang/package/N` on the wire, `badDoc` in text). A re-genesis is required
for any World holding package cells.

**Measured.** The Bell: 3,062 chars of surface (was 2,876), core 27,865 chars (was 27,679), 21,960 package
bytes (was 21,780: +1 version, +175 doc, +4 framing). An empty doc costs 3 bytes and the version 1:
`Owned` 1,788 → 1,792. Required steps unchanged everywhere (the doc is never run).

**Read.** Second-agent vacuity read with the disjunct check: nothing vacuous, nothing weakened; WEAKs
fixed: `packageLines_doc` now pins the doc line as the FIRST line (`ls.head?`); the empty-doc twin is
`packageLines_no_doc` (the pre-LANG-60 list, exactly); `decodePackage_refused_label` ties the decoder's
refusal name to the version as `packageCodec_label` ties the codec's; reader teeth (`(doc)` is empty;
`(doc "")`, `#hex`, two strings refused `badDoc`) and decoder teeth (a doc with a line feed or not UTF-8
is no package; a plain one reads). CODEC-14 agreed the codec hunks (and asked for the version-derived
label, the general unversioned theorem, the control/non-UTF-8 teeth: all in); PROTOCOL-19 agreed the
Describe/Rows hunks; HOSTING-12 confirmed the resident's shape parse ignores a `doc` line.

## LANG-61 What extraction forces is the meaning: each field of an extracted record is its `get`'s value (2026-10-21; ROOT ruled it Lang's; LANG-21; LEDGER-4's hand-off, cv 01a152e3-9c8e)
**Why.** LEDGER proves the escrow's calls on the reference evaluator, one field projection at a time
(`slotField`: `.get (.get (methodAt ℓ) "calls") "c0"`); the receiver runs the whole method application
and `extract`s the result at `resultTy`. Nothing related the two: an extracted field was a machine
artefact of a budget, not a fact of the language.

**What.** `Lang/Proofs/Extract.lean`. `Means lib T v d` (with `RowMeans`, `Unknots`): `d` is what `v`
means at data type `T` by `BigStep`, with no machine and no budget. `extract_means`: whatever `extract`
returns, at any budget, is the meaning (no premise at all: an ill-typed value is `stuck`, never data).
`means_deterministic`: one meaning per value and type. `means_get` (the field lemma): if `t` means `v`
and `v` means record data `d` at `rec row`, then for EVERY `w` that `.get t ℓ` means, `d.field ℓ` is
`w`'s meaning at `ℓ`'s type (`means_get_exists`: such a `w` exists); `extract_get` is the one-extraction
form. `runMeasured_means` strengthens `runMeasured_calls`: a successful run extracted the MEANING of
`apply4 g ℓ` in the environment the setup built (request, arguments, state, rows, each named by its
reading equation), and its calls are `callsOf` of that meaning's `calls` field. A consumer composes
`means_get` twice (`calls`, then `c0`) with its own reference-semantics derivation of the projection and
`means_deterministic`. The account step: `.inj "of" {asset, owner}` reads as `AcctRef.of` by `bodyOf`
(`callData_bodyOf`/`bodyOf_callData`, Lang's, on main); `AcctRef.of o a ↦ accountId X o a` is KERNEL's
resolver (`Kernel/Receive/Ledger.lean`), by definition.

**The closure.** The receiver means `apply4 g ℓ` under `L.lib`; a consumer computes under a lib of its
own. `bigStep_relib`: a derivation of a `NoRef` term over a no-ref environment (`NoRefVal`; every
`Data.toVal` is one, `toVal4_noRef`) is a derivation under every lib, and its value holds no ref.
`Relib` composes it (`relib_ref`, `relib_app`, `relib_get`, `relib_case`, `relib_apply4`): two libs
holding one `NoRef` body give the method application, and every projection over it, one meaning.
An INLINED method term (the escrow's `methodAt`, lib `[]`) is not that: its field closes over the
run's environment where `.ref g` closes over `[]`, so values differ while data agree. The consumer
restates projections over `apply4 0 ℓ` under `[body]`.

**Teeth.** `extract_get_tooth`: the knot `fix (λself. {a = 1, g = self.a})` never extracts with `g = 2`,
at any budget (its `g` means 1); `extract_knot_ok`: it does extract, to `g = 1` (by `rfl`).
`relib_needs_one_body` and `relib_needs_noRef`: each premise of `relib_ref` is needed.

**Read.** Second-agent vacuity read with the disjunct check, twice: nothing vacuous. Fixed from the first
read: the field premise had no supplier (`means_field_exists`, `rowMeans_labels`); the projection
route did not compose (the `Relib` half above). Fixed from the second: the `NoRef` tooth. What
LEDGER discharges itself (none unsatisfiable): `readPackage look pkg = .ok escrow`, the digest
round trip, `NoRef escrow.body` (not yet proved), the state's shape from `readState`, and restating
`escrow_calls_payout` over `apply4 0 ℓ` with projections that keep the `well`/`none` tags.

**Nothing moves.** No wire, no vector, no shipped text, no required step.

## LANG-62 The run's state is the record it extracted; a no-ref meaning is lib-free, in Lang; `Forces` is `Means` with sizes (2026-10-21; LANG-22; LEDGER-13's open (b) and (d); cv 01a153a2-6489)
**Why.** LEDGER-13 proved what the escrow's receiver run CALLS, not what it WRITES: `runMeasured_means`
named the extracted `state` field `st` and said nothing of the slots `s` the run returned, so the
receiver-side state half and the chain over receiver runs had no first step (LEDGER-13 critique (b),
(c)). LEDGER also proved `means_relib`, a Lang fact, privately (critique (d)). LANG-21 left the
parsimony question: `Means` (Extract, data) and `Forces` (Need, `Derives` sizes) walk one path.

**What.** (1) `runMeasured_means` now concludes the extracted result is
`.record [("calls", c), ("edits", e), ("state", .record ds)]`, `stateSlots (recordRow p.state) ds 0 = some s`
for the run's own `s`, and `RowConforms ds (recordRow p.state)` (`stateSlots_conforms`: written
fields decode back, so they conform; `means_state_labels`: the meaning carries the row's labels),
with no new premise. It is the brief's `st = .record ds ∧ …` with `st` substituted. A consumer reads
the slots back with `readState_go_stateSlots` given one more fact: every digest in `ds` passes
`digestsOk`. The run does not check it and no theorem gives it (cv 01a153b1-dc52, below). (2) `means_relib` (with `unrolls_relib`, `rowMeans_relib`) is public in
`Lang/Proofs/Extract.lean` beside `bigStep_relib`; LEDGER's private copy is deleted in the same
commit; EscrowRun's one use is unchanged. (3) The relations stay two, bridged as `Derives` is to
`BigStep`: `means_forces` (Means → ∃ n, Forces) and `forces_means` (Forces → ∃ d, Means), with
`unrolls_unknots`/`unknots_unrolls` and the row forms, in `Lang/Proofs/Need.lean`. The machine walk
that gave `extract_forces` (`force_derives`, `unknot_unknots`, `extract_forces`, `extractArm_forces`,
`extractRow_forces`, ~100 lines) is deleted: every completed extraction's `Forces` is
`means_forces (extract_means …)`, so the walk over `Machine.extract` is proved once.

**Why two relations, and not one.** A merged `Forces lib T v d n` (data and size) would make every
`Means` consumer carry a size it never reads, and every `Forces` consumer (`forces_le`,
`forces_unique`, `needExtract_forces`, NeedComplete's counter) carry data it never reads; the repo
already holds that pair for terms (`Derives`/`BigStep`, bridged by `derives_bigStep`/`bigStep_derives`).
What two relations risk is drifting apart; the bridge in both directions makes a drift a red build,
and the deleted walk removes the one place they were each proved against the machine separately.

**Teeth.** `run_state_tooth`: the `stateSlots` conjunct is not implied by the `Means` one: `{a = natLimit}`
is a meaning at `rec {a : nat}` (a meaning has no bounds) and `stateSlots` writes nothing of it;
`{a = 1}` it writes. `means_relib_needs_noRef`: the knot `knot (ref 0) []` means `{a = 1}` under `[{a = 1}]` and
not under `[{a = 2}]`, so `means_relib`'s `NoRefVal` premise is needed.

**Read.** Second-agent vacuity read with the disjunct check, twice: no disjunction anywhere; nothing
vacuous, nothing weaker than main (`runMeasured_means` strictly stronger; `means_relib` identical to
the deleted private copy; the bridge loses nothing `extract_forces` gave). Fixed from the first read:
the state tooth tested only constructor disjointness and what `Means` already excludes (now the
`natLimit` tooth); the docstring promised a read-back that needs two facts it did not give (now
`RowConforms` is a conjunct and the digest fact is named as missing). The second read: no fixes.

**Critique.** The read-back of the written slots lacks `digestsOk` of `ds`. `runMeasured` checks it on
the arguments and `readState` on the state it reads, but nothing on the state a run writes. No prim
makes a digest (`primEval` only compares them), so every digest of a run's value is a literal
(`checkLits`) or from the checked environment: probably an invariant, unproved. If it is false, a run
writes a state the next run refuses (an object wedges). cv 01a153b1-dc52: the provenance theorem
over `BigStep`, then a `digestsOk` conjunct here; the fallback is a named refusal in `runMeasured`.
LEDGER's escrow does not wait on it: its `ds` is a concrete `methodResult`, whose digests are the
read state's. **Meta-critique.** I considered merging the relations
first (the doctrine prefers deleting a twin); the merge deletes no theorem a bridge cannot, and costs
every consumer a field; the bridge plus the deleted duplicate walk is the deletion that matters.

**Nothing moves.** No wire, vector, shipped text or required step.

## LANG-63 The slots a run writes read back to the state it extracted (2026-10-21; LANG-22; corrects LANG-62's critique; cv 01a153b1-dc52)
**Why.** LANG-62 said that the written state passing `digestsOk` was unproved. That was wrong. LANG-41
(`Lang/Proofs/Provenance.lean`) proves that no primitive makes a digest, and that every digest of a
run's extracted result is one `digestOf` accepts under a codec that reads its own ids back
(`runSetup_accepted_of`). It was private, and LANG-62 did not compose it.
**What.** `runSetup_accepted_of` is now public. `runMeasured_means` gains a final conjunct:
`(∀ x, (digestOf (bytesOf x)).isSome = true) → readState digestOf (recordRow p.state) s = .ok (.record ds)`.
The proof composes `stateSlots_conforms`, `runSetup_accepted_of` and `readState_go_stateSlots`. The
next run of the object therefore reads the state this run wrote. The premise is the codec law
(`Ctx.Lawful.digestOf_bytes` implies it), and it sits inside the conjunct, so `runMeasured_means` still
takes no premise. `Lang/Proofs/Extract.lean` now imports `Lang.Proofs.Provenance`.
**Tooth.** `reads_back_needs_ids`: a digest field that `stateSlots` writes, read by a decoder that
names no id, is refused (`state field a: not a digest`). So the codec premise is not idle.
**Read.** A second-agent vacuity read with the disjunct check found nothing vacuous. There is no
disjunction. The premise is satisfiable (EscrowRun's `hdig` implies it). The conclusion is about the
run's own `s` and `ds`, and needs the run's own setup, run and extraction. The tooth is honest about
the component: it shows the `readState` step needs the premise. It does not show a whole run under
an unlawful codec writing an unreadable state; that run-level tooth is optional and not done.
**Nothing moves.** No wire, vector, shipped text or required step.

## LANG-64 A tick walks at most one word: the byte primitives are charged per 32 bytes, paid before they walk (2026-10-21; LANG-23; DECISIONS-20261021 card 6, ID-4, ROOT's lean α; cv 01a14805-3d32)
**The defect (measured by the scholar, restated).** LANG-L reads the tick as a unit of work (every step
O(1)). `cat` copied `a.size + b.size ≤ bytesMax` = 65,536 bytes in one tick and `beq` compared up to
two 64 KiB operands in one tick (Lang/Eval.lean:111-115 before this entry). So one tick could be
128 KiB of work, and one law run under `lawTicks` = 100,000 could copy about 6.5 GB inside the
writer's admission loop. The bound was on values, not on work.
**The honest unit, read off the compiled machine.** `beq` and `deq` are `decide (a = b)` on
`ByteArray`: `ByteArray.ext_iff` reduces it to `a.data = b.data`, and each `.data` is
`lean_byte_array_data`, which builds an `Array UInt8` from the byte string. Both operands are copied
whatever their sizes, so `beq` walks |a| + |b| bytes, not the shorter one. `cat` is `copySlice`
(a shared `a` is copied first, then `b`): |a| + |b|. A `cat` past `bytesMax` refuses on the sizes
alone and walks nothing. Every other primitive walks no bytes: naturals are below 2^64 and `lenLe`
reads a size field.
**Decision.** `primBytes p x y` is those walked bytes. `primTicks p x y = (primBytes p x y - 1) / 32 + 1`:
one tick per `Bounds.wordBytes` = 32 bytes, rounded up, and one tick for a primitive that walks none.
A primitive on at most one word costs one tick, as before; a 64 KiB `cat` costs 2048 and a `beq` of
two 64 KiB strings 4096. The frame `primR p left paid` counts the ticks paid, and `primStep` pays one
per transition and computes on the LAST one. So a tick stays a transition, `run` is unchanged, and
a budget that runs out while a primitive is paying has walked none of its bytes. `stepBytesBy st s`
measures a transition by what it does: a transition from a primitive's frame that does anything but
pay one more tick (`Step.pays`: a frame with `paid + 1` over the same frames below) walks the
operands, and every other transition walks none. `walkedBy st` sums that along a run of the
stepper `st`, and `walked lib` is `walkedBy (step lib)`. (The other order,
computing first and charging after, lets a run with one tick left copy 64 KiB; that would break the
bound at the budget's edge.) The reference derivation charges the same price: `Derives`' prim rule
adds `primTicks` for its instance, not 1, and so does `Need.need`. The price is read off the operands,
not off the machine, so LANG-34's rule holds: the denominator reads no machine. A 64 KiB `cat` is
required work, not waste, so THE BAR's ratio does not count it as waste.
**Theorems (Lang/Proofs/Cost.lean, CostTeeth.lean).** `primBytes_le`: a primitive walks at most
`wordBytes` bytes per tick it is charged. `walked_le`: a run from `State.init` walks at most
`wordBytes × used` primitive operand bytes, under every budget and stack bound and however it ends. `walked_le_paid`
is the general form, from any state, with the ticks already paid on its stack. This is LANG-L made a
theorem for the byte primitives. `law_walks_le`: no run under `lawTicks` walks more than 3,200,000
primitive operand bytes. `primTicks_word`, `primTicks_nat` and `primTicks_lenLe`: nothing else moved. `primBytes_cat`:
the bytes `cat` is charged for are the size of what it writes. `primBytes_beq` and `primBytes_deq`:
both operands. So every row of the price list is a named fact. Simulation: `Ends.paid` (Agree) and
`prim_leads` (Complete). `derives_lt_used`, `bigStep_run` and `run_bigStep` keep their statements.
**Plant.** `cat64_price`: for every a, b with |a| + |b| = 65,536, `cat` of their literals returns
under 2053 ticks (2048 + 5) and is refused `ticks` under 2052. `cat64_walks`: that run walks exactly
65,536 bytes, so `walked` does not read 0 by construction. `cat64_flat`: `Need.flatStep` (the
deployed step, except that a primitive computes on its first tick: the machine before this entry)
returns the same value in 6 ticks while `walkedBy` counts its 65,536 bytes, so `walked_le` is false
for it. The cat's reference size is 2050, above 6, so `derives_lt_used` is false for it too.
**Required steps, before and after.** Every journey row that prints required steps / ticks is unchanged:
LT4 40/63, LS4 102/152, LS6 111/159, LS9 270/339, LB4 79/120, LB7 96/143 (and their repeats). THE BAR
`invoke ticks-per-required-step` 1.577 (plants waste-app 1.885, waste-extract 2.154) is unchanged too,
as is every other WASTE/PLANT line of `rows`. `rows --deployed`, `ledger-sim 1`, `hosting-sim 1` and
`host-sim 1` are byte-identical. Control: the same tree with `wordBytes` set to 2^30 (`primTicks` ≡ 1,
exactly the old transitions) reproduces main's journey and rows output byte for byte, apart from the
wall-clock LIVE lines. Why nothing moves: no shipped package, in the Sim, applies a byte primitive
to more than 32 bytes. Its texts and names are short, and the Sim digest is 8 bytes. DEPLOYED, a `deq` of
two 32-byte digests walks 64 bytes and now costs 2 ticks where it cost 1. No printed measurement runs
deployed digests through the machine, so that rise is stated here, not measured.
**Read.** A second-agent vacuity read with the disjunct check. Its first pass found one VACUOUS item:
`stepBytes` copied `primStep`'s guard, so on the flat machine (`paid` stays 0) a computing tick read
0, and `walked_le` held there too. It found the plant OVERSTATED (its second conjunct was about
the instance alone, the conjunct form of the disjunct check) and the computing-tick tooth WEAK (it
checked hand-built states, not the run). All three are fixed above: the measure reads the
transition, and `cat64_flat`/`cat64_walks` are run-level. It also found docstrings counting "bytes"
where only primitive operands are counted (reworded), and asked for a separate reference unit
`wordRef` pinned equal to `wordBytes`. I refused that one: two constants pinned equal are a twin.
`wordBytes` is the language's price list, shared by the reference and the machine as `primEval` is,
and a machine that pays twice per word still raises the ratio.
A second pass over the fixes found F1 to F4 OK for the deployed step. It found one hole in the
price list: `beq` and `deq` were priced by nothing but a docstring, so an under-pricing would have
moved the charge, the denominator and the measure together, silently. Fixed by `primBytes_beq` and
`primBytes_deq`. The refutation of `derives_lt_used` for the plant is now a named conjunct
(`¬ 2050 < used`). Left as named residue: `Step.pays` matches the SHAPE of a paying transition (a
`primR` frame with `paid + 1` over the same number of frames below), not its identity. A generic
stepper could compute and fake that shape, which would give a plant tooth a false negative. It is not a
hole in `walked_le`: for the deployed `step`, a computing transition never has that shape.
**Not a wire.** Ticks are a budget, not a byte any message carries. Nothing re-ids, nothing re-emits,
and nothing re-geneses: a `lang:`. What changes is what a budget buys. A program that walks more than
32 bytes per primitive costs more ticks, and one that fit `lawTicks` may now be refused `ticks`. No
shipped program is one.
**Alternatives.** β, a second meter (`bytesTouched`): two meters for one resource, and THE BAR's tick
row would stop measuring work. γ, the status quo: 6.5 GB per law run on the request path, refused.
Charging over the shorter operand for `beq` (the card's draft): the machine copies both operands, so
that is below the work. A unit of 64 bytes, which would keep `deq` at one tick: no rule picks it; the
card's word is 32, and the rule stays one rule for every byte primitive.
**Critique.** (1) The bytes are still walked in ONE transition: the ticks are paid first, and the
transition that computes does up to 128 KiB. The bound is per tick of the run, from its start, not
per transition. Walking a word per transition would need a chunked `cat`/`beq` and ByteArray slice
lemmas core does not have; it is possible and not done. (2) `primBytes` is a model of the runtime,
read from Lean's sources (`lean_byte_array_data`, `copySlice`), not proved about it. Only `cat`'s count
is tied to an output (`primBytes_cat`). (3) The other non-constant work in a transition (`env[i]?` is
O(i), `Row.merge`, label comparison in `Row.find?`) is bounded by Wire constants, not charged; Eval's
header says so. (4) `beq` pays for `lean_byte_array_data`'s copies. A size-first loop over the two
byte strings would walk min(|a|, |b|) and allocate nothing. That is an evaluator change, and with it
`primBytes` for `beq` may FALL, which needs its own entry.
**Meta-critique.** The first draft charged after the work, because that order is the natural place
for a debt frame. Writing `walked_le` exposed the edge: the theorem is false for a run cut off right
after a 64 KiB `cat`. That is why the frame counts ticks PAID, not owed. The before/after table is
empty because the Sim workload has no long bytes. The plant, not the table, is this entry's evidence.
**len/take/drop.** Not added (δ): no package needs them. When one does, `len` is one tick
(`primBytes` 0), and `take`/`drop n` fall under `primBytes` = n.
**Also (cv 01a15456-b411).** `readState_get` (readState reads slots only by key) moves from
Ledger/Proofs/EscrowRun.lean to Lang/Proofs/Invoke.lean, beside `readState_conforms`. The Ledger copy
is deleted (ROOT for LEDGER, cross-layer).

## LANG-66 Contextual modal types, the guarded contextual closure and the hole rows: activities and continuations get their theory at the Lean level, and their first demonstration through the receivers (2026-10-22; ACTIVITIES-1, deputized by Ember; ROOT GO with three conditions; design `redregg/work/ACTIVITIES-DESIGN-20261022.md` §9–9.1)
**Ember's ruling.** "I want activities and continuations … promote those things into nano, because we would finally have
a firm theoretical, metaprogrammatic and proof-engineering basis to rest them upon"; then, on the first design and its
obend prototype: "I don't see the actual explicit things GPT wrote about, contextual modal type theory etc. … implement
this properly and thoroughly at the Lean level."
**Decision.** Three things land as one `lang:`; nothing on the wire moves, no package re-ids, no Store re-geneses.
1. `Lang/Contextual/Core.lean` + `Lang/Proofs/Contextual/Core.lean` (113 theorems): a well-scoped, simply typed Contextual
   Modal Type Theory (Nanevski–Pfenning–Pientka): types `base | arr | box Ψ A` (the contextual type `[Ψ ⊢ A]`), terms with
   de Bruijn variables, `box Ψ t` CLOSED to its ambient context, `letbox`, and metavariable occurrences `mvar u σ` carrying
   an explicit simultaneous substitution; one `HasTy Δ Γ t A` (with `HasSubst` and `Step`, the judgments, in the proof module `Lang/Proofs/Contextual/Typing.lean`) over a meta-context that is a FUNCTION from names to declarations (`MEnv`, so a partial fill leaves unfilled holes at their names); a total type checker `infer`/`check` proved SOUND AND COMPLETE; decidable term equality by hand; `msubstP` (named, simultaneous, partial filling) with `hasTy_msubstP`; the strengthening FUNCTION `unshiftAt` with `shiftAt_unshiftAt`, `hasTy_unshiftAt`, `uses_shiftAt`; ordinary and metavariable substitution with their lemmas
   (`subst_lemma`, `msubst_lemma`, `subst_comp`, weakening both ways); the proposal's factorization `strengthen` (a term
   not using a hypothesis is a smaller-context term under the projection); weak-head reduction with `subject_reduction`
   (its two redex cases ARE the two substitution lemmas) and `step_deterministic`. Teeth: `box_cannot_capture`,
   `mvar_blocked`/`msubst_unblocks` (an unresolved metavariable blocks inspection until a METAvariable substitution
   arrives, never an ordinary one: Hu–Pientka's layered discipline, operational in `letbox_needs_box`),
   `strengthen_needs_unused`, `no_step_under_box`, `box_ambient_free` (a box typed under one ambient context is typed under any other). The Bell's resumption is a toy: a continuation `box [base] …` typed under
   ANY ambient context, resumed by `letbox`, computed by `rfl`.
2. `Lang/Contextual/Closure.lean` + `Lang/Proofs/Contextual/{Closure,Experiments}.lean` (86 + 36 theorems): the GUARDED
   CONTEXTUAL CLOSURE — the proposal's `(P, Ω, σ, D, support, Φ, t)` — over an abstract calculus split as nano splits everything: `CalculusData` (a def module: Ty, Ctx, Tm, decidable term equality, msubst, check, uses, drop, strengthen, weaken, var, lookup) and `CalculusLaws D HasTy : Prop` (a proof module: msubst_lemma, check_sound, check_complete, strengthen_lemma, strengthen_factor, weaken_avoids, hasTy_var, uses_var; the last three anchor `uses` and `drop` so no degenerate instance satisfies them), `HasTy` a parameter, a template's typing the predicate `Template.Typed` (so the theory is calculus-independent, as Mini's `GuardedAdvice` was candidate-independent, and the gate's def/proof split holds: C3): immutable versioned assumption tokens, a
   hole's interface with its guard, chooser and acceptor (POLARITY), retained candidates with the reason each was set
   aside (`Status := verified | suspended | pruned | conflict | uncovered`), five repair outcomes, `judge` the one status
   function, `Derivable` SEPARATE from `Available`, `repair` and `fromScratch`. Theorems: conditional soundness
   (`conditional_soundness(_closure)`), repair correctness (`repair_agrees_from_scratch` under `Coherent`, kept reachable
   by `repair_coherent`/`fromScratch_coherent`), locality (`repair` RETURNS the candidates it re-judged; `repair_rejudged_eq_touched`: exactly the touched ones, a statement recompute-all FAILS; `locality`, `repair_carries_untouched`, `judge_frame`; `rejudged_only_touched` computed on experiment 1),
   `withdraw_never_refutes` (a withdrawal never acquires a negation), `select_requires_available`,
   `executed_prefix_blocks_replan` (no select, deselect OR prune of an accepted selection), `history_is_prefix`, `conflict_illTyped_refutes` (with `check_complete` an ill-typed verdict is a true refutation), `session_preserves_coherent`/`s1_coherent` (Coherent shown on an experiment state, from the session theorems), `provenance_iff` (the ATMS/semiring reading, THE BRIDGE between two independent definitions: `provenance` is a WORLD-FREE polynomial over tokens, supports positive literals and blockers negative, and a hole has a verified candidate iff some monomial holds at the world; `provenance_world_free`), `stability_class`/`valueGuard_iff` (which substitutions a guard's
   verdict survives), and the EIGHT EXPERIMENTS as named theorems over a concrete session: withdraw one of two supports,
   withdraw the last, withdraw a pruning reason, a cycle losing its grounding (NOT expressible in the one-level closure: a separate rule model, `unfounded_not_derivable`, over a world where an unrelated fact stays live; least fixpoint loses it, naive counting keeps it: both proved), a dependent-context change, replace a filling preserving its contract, correctness kept but a
   cost bound lost, re-apply an earlier filling.
3. `Lang/Journey.lean`: rows LH0–LH11, the hole as a surface package (`holeText`, the text a resident writes) through the
   real receivers: a candidate's supports are assumption-token ROWS on the hole object; a support re-pinned or withdrawn
   by its poster refuses a `select` BY NAME (`select: refused support0 moved` / `support0 withdrawn`), also over the view
   before the withdrawal; the candidate with the surviving support is selected (139 required steps / 179 ticks); a select
   after `accept` is refused `accepted`; a post-acceptance withdrawal leaves the selection; the over-cap candidate is
   retained `suspended "cap"`; the chooser prunes naming why. Plant (by hand, logged): the pin equality removed from
   `select` turns LH7 admitted and LH7b `rejected stale` — the kernel's row pin is reached exactly when the method's check
   is absent: derivability and admission are two judges, measured.
**What the Lean theory corrected in the design that was proposed** (and in `ACTIVITIES-DESIGN` §3–4, which §9 supersedes):
a method never sees its call's cell pins and reads rows under `self` only, so a support is a row under the hole object,
never a pin on another cell; `relaw` is refused `hasMethods` on a programmed object, so a pruning reason or guard
parameter is STATE changed by a method, not a law; `admit_comm` is insert-only, so selects do not commute by it; an
identical row upsert bumps the version (measured), so an exported `value` row must skip unchanged upserts; the guard
belongs to the hole, not the candidate; the outcomes need `kept` and differ in who may apply each (`replacement` is
OFFERED to the chooser, never applied by repair; after `accept` only `suspended (reconcile)`); repair-equals-from-scratch
needs `Coherent` and an explicit observable (the selection is history), and locality is a separate theorem.
**Price.** No landed theorem gains a premise, no landed statement changes: three new def modules, four new proof modules,
rows appended to one journey. `Lang/Proofs/Contextual/Closure.lean` is 1,236 lines in one proof module (law 8 asks for a
split; a follow-up `lang:`). SIZE: modules, lines and theorems rise, stated in the commit.
**Not in this landing, by name.** (a) The REAL-CMTT instance (`Lang/Contextual/CoreCalculus.lean`: `cmttData : CalculusData`, `holeEnv`; `Lang/Proofs/Contextual/CoreInstance.lean`: `theorem cmttLaws : CalculusLaws cmttData (HasTy ∘ holeEnv)`, every law discharged, `weaken_avoids` by `uses_shiftAt`, `check_complete` by the checker's completeness; `bell_template_toy`: the template `λx.u₀[x]` typed WITH the hole and not without, filled by `rfl`, typed with no holes left through the instance's `msubst_lemma`; `cmtt_strengthen_toy`: the real strengthening is not the identity) is BUILT and lands as the SECOND `lang:` right after this one (ROOT's condition 2); until it lands the closure theory is instantiated only abstractly and by its toy calculus. (b) First-class substitutions
(Cave–Pientka): cv task 01a1587d-9a98, with the two syntax options. (c) Open protocols with polarized holes and linear
resources (`Lang/Contextual/Protocol.lean`, the two-cell one-use-capability negotiation): a lane in flight, its own
`lang:`. (d) The `Std.activity`/`Std.hole` generators that make the Bell an instance: after (a)–(c).
**Alternatives.** (i) Build only the obend package and rows (the first design): refused by Ember as "half-assed"; the
theorems were the point. (ii) A kernel continuation cell kind: refused on price (the three totalities, every `readKind`
site, a `kernel!`) and on law 1 (rows are "keyed bounded things under an object"). (iii) Depend on Mathlib for the
category-theoretic reading (presheaves over contexts): refused by LANG-15/GATES-1; the stability class is stated directly
(`StableUnder`, `valueGuard_iff`). (iv) Import Mini's `IndexedProgram`/`GuardedAdvice`: law 11 (no twins); restated
smaller and, for the closure, over an abstract calculus rather than Mini's `Vocabulary`.
**Critique.** (1) The closure's supports are one level deep: a hole cannot support a hole; the cycle experiment is
therefore a separate rule-system model (`Rule`/`Derives`/`lfpIter`), not a closure over closures. (2) An `env` edit marks
every candidate touched (locality bites on token edits only). (3) The toy calculus's hole occurrences carry no explicit
`u[θ]`; the real instance is where the CMTT and the closure meet, and it is not landed here. (4) The theory is simply
typed; the proposal's dependent-context experiment is modelled by a guard parametrized by `n`, not by `Vec n`. (5) The
rows demonstrate one hole per object; many holes per object (the `waits` row design) and the `Std` generators are not
built. (6) 1,407 lines in one proof module (`Lang/Proofs/Contextual/Closure.lean`), a law-8 split owed as a follow-up `lang:`. (7) Named limits from the instance lane: fillings are typed in the empty meta-context (no hole inside a filling, so hierarchical refinement is not expressible); hole-name uniqueness lives in `Template`, not in `HasTy` (the instance takes the first declaration of a name); fillings compare syntactically, so β-equal fillings are different candidates.
**Meta-critique.** The first design mapped the proposal onto nano's existing vocabulary and called the obend package the
deliverable; an adversarial read found 8 HIGH defects in that mapping and Ember named the substitution for what it was.
The pull was familiarity: pins and rows were already proved, so I reached for them instead of the theory. The second pull,
in this landing, is to call the abstractly-instantiated closure "the CMTT closure" — it is not until `cmttCalculus`
lands, which is why (a) is named above and the commit message says so.

## LANG-67 Open protocols as typed families of continuations: holes with polarity, linear tokens, obligations, the executed prefix, and the two-cell one-use-capability negotiation; nano's `interp_runs` re-derived as an instance (2026-10-22; ACTIVITIES-1; `redregg/work/ACTIVITIES-DESIGN-20261022.md` §9.4)
**Why.** Ember: "the GPT design discussed repair and open protocols, which seems like a natural way to express the sort of
smart-contract system this is." The proposal's doc 2: an open protocol as a typed, inspectable family of continuations
with explicit obligations for making a particular continuation executable; three kinds of openness (an unspecified
component, an interaction with an environment, an unfinished execution), polarity and causality, shared parameters,
the executed prefix; doc 3's first integration experiment.
**Decision.** `Lang/Contextual/Protocol.lean` (757 lines) + `Lang/Contextual/NanoBridge.lean` (66; the resident `Prog` read as a
protocol) and `Lang/Proofs/Contextual/{ProtocolTyping,Protocol,Negotiation}.lean` (132 + 961 + 474; the judgments
`HasProt`, `Started`, `Dispatched`, `Open.WF`, `Assigns`… in `ProtocolTyping`, a proof module, per the gate's def/proof split),
one `lang:`; no wire moves, no package re-ids, no re-genesis.
1. *The object.* An indexed signature `Sig {Op, Resp, next}` and the free protocol `Prot := ret | call op k | hole h`:
   a `call` branches over EVERY response (`k : (r : Resp op) → Prot (next op r)`, the interaction with an environment);
   a `hole` is an unspecified component named in an interface list Ω (polarity `ours | theirs`, acceptor, context, the
   tokens it needs, its result condition, the obligations it owes, an acceptance contract). A `Spec` says per operation
   what it consumes (a linear token), requires (reusable facts) and establishes (obligations). The judgment
   `Ω;Γ;Δ ⊢ P ⊣ Φ` is `HasProt sp Ω Γ Q Φ Δ P`: Δ a BAG of tokens, a `spend` removes one for every continuation; Φ an
   UPPER BOUND on what any path establishes (a call branches, so Φ cannot be an output). History `Hist` = the answered
   calls plus at most one call in flight; `Started`, `Dispatched` (the history has ENTERED a hole). The open object
   `Open` = template, Ω, σ, Γ, Δ, Q, Φ, history; `Open.replan` is a plain setter and `Open.Replan` (a statement) its guard:
   the theorems that re-plan take the guard as a hypothesis. Admission (`admits`) is SEPARATE from typing: it checks only the next effect against the current world,
   and a hole admits nothing.
2. *The four families, proved.* Contextual completion: `fill_preserves_hasProt`, `fill_skips_theirs`,
   `theirs_hole_untypable`, `HasProt.weaken`, `mem_holes_iff`. Interpretation of substitution: `fold_fusion`,
   `fold_subst`, `interpret_fill` (running P[σ] = running the template with σ in the environment), `interpret_record`
   (the recording run appends exactly a complete path, or exactly the prefix to the hole where it stopped). Selective
   repair: `locality`, `repair_agrees_from_scratch`, `repair_residual` (the leftover obligations named),
   `repair_reuses` (only the affected fragments are read). Admission and history: `hasProt_reach` (along any prefix,
   tokens spent stay within Δ, obligations within Φ, the remainder still judged), `at_most_once` (a token held once is
   spent at most once on every path; the discipline is AFFINE: `ret` accepts any leftover Δ), `resubst_preserves_started`/`Open.resubst_wf` (re-filling holes the history has
   not entered keeps the history and its obligations), `admits_local`, `commit_once`.
3. *Polarity and causality, proved.* `no_foresight`: for every peer bit some filling wins, but no single filling chosen
   before the reveal wins against every bit; `response_dependent_succeeds`: the same game as a `call` continuation wins
   against every bit; `theirs_never_planned`; `foresight_iff_names_separate` (∃θ∀b wins ↔ the hole's name differs across the response),
   `response_indexed_names_have_foresight`. So a hole is NOT an interaction when its NAME does not depend on the response: one filling then enters every response
   branch unchanged. The reader found the general claim FALSE: with response-indexed hole names (`HoleN .revealed := Bool`)
   θ(b) := ret b wins every bit (`response_indexed_names_have_foresight`), so the separation is a NAMING discipline the
   template must obey, stated as such, not a fact of the calculus.
4. *Shared parameters and search.* `separate_witnesses_insufficient` (buyer ≤ 5, seller ≥ 7: each satisfiable, no
   shared price; `witnesses_do_not_compose` general, `separate_witnesses_bounded` decided), `greedy_vs_logical`
   (first-fit scores 1 of 2; complete search finds [1,0]; by decide), `search_state_ne_logical_status` (scalar illustrations); and over the template itself
   `separate_witnesses_over_substitutions` (Θ := Subst over the Negotiation template in the world with p1 revoked: the
   buyer guard and admission each satisfiable, no completion satisfies all).
5. *The integration experiment* (`Negotiation.lean`): two parties, a one-use capability, alternative providers, a
   deadline, a cancellation path. (a) `unrelated_update_keeps_plan` (via `admits_local`), `unrelated_update_repair_reuses`;
   (b) `provider_revoked_unavailable` (available [1,2,3] → [2,3]; `plan p1` still derivable, not admissible; the template
   still judged; `revocation_repair` residual [1]); (c) `representation_change_transports` (epoch : Nat, a PARTIAL correspondence `Tok'.current`; `stale_opening_refused`: an
   opening at another epoch is refused);
   (d) `competing_commitments`, `replay_refused`, `internal_once_not_external_once` (one spent token is consistent
   with 0, 1 or 2 external executions), `exactly_once_needs_reply_and_dedupe`; `deadline_expires`,
   `cancel_path_refunds_obligation` (`commit_path_pays` the contrast); `lost_reply_keeps_obligation`,
   `lost_reply_blocks_replan` (an unguarded `replan` after dispatch fails `WF` and `Replan` refuses it, to the other provider
   and to the cancel path), `answered_blocks_replan` (the answered half), `guard_stricter_than_wf` (a filling with the same
   first call keeps WF but `Replan` refuses it: the guard is sufficient, and stricter than WF needs), `replan_before_dispatch`;
   `internal_once_not_external_once` and `exactly_once_needs_reply_and_dedupe` over `Internal.ofHist` of `lost p`, `H₀`,
   `answeredH p b` (the delivery model linked to the history).
6. *The nano bridge.* `Hosting.Resident.Prog` is the instance with a trivial index and no holes (`Nano.ofProg`, `toEv`):
   `nano_runs_iff` (nano's `Runs p es a` iff `ofProg p` has a `Runs` path reading as `es`), `nano_interp_agrees`
   (nano's `Prog.interp (recorder o)` = this `interpret` at the oracle environment), `nano_interp_runs` (HOSTING-37's
   `interp_runs`, RE-DERIVED from `interpret_record`). So the resident's proved continuation structure IS a protocol,
   and the protocol theory's statements apply to it.
**What formalizing corrected in the prose.** (1) Φ "the obligations for a particular completion" is not an output of
the judgment (a call branches over every response): Φ is an upper bound; and a call's obligation starts at DISPATCH,
not at the reply (the lost-reply case makes sense only so). (2) Polarity does not capture causality; SCOPE does, and scope is the
template's hole NAMING (response-independent names), which the theory must state and the reader made it state;
`theirs_hole_untypable`/`fill_skips_theirs` are this calculus's own rules (a `theirs` hole is a `call`), not findings;
"who must accept" is a contract predicate on the filling.
(3) "Replacing an unexecuted component preserves the history" needs ENTERED, not executed: not reached / reached but
re-plannable (`replan_before_dispatch`) / entered (a call performed or in flight), which cannot be re-planned, not even
to the cancel path (`lost_reply_blocks_replan`).
**Price.** No landed theorem gains a premise; no landed statement changes. New modules only. The bridge imports
`Hosting.Resident.Run` into a Lang def module (a cross-lib import of a deployed module; C9 allows it).
**Not in this landing, by name.** `fold_rel` (mini's logical-relation fold) not restated; `Consistent`/`External` are this
module's own delivery and deduplication model (the proposal gives none), so the external-once theorems hold relative to
it; multi-WRITER agreement over a hole stays out (charter item 3: the two parties are two members of one World).
**Alternatives.** (i) Holes carrying their interface in the node (refused: substitution would need casts; Ω by name, indexed
by `Ix`, needs none). (ii) Φ as an output of the judgment (refused: ill-defined under branching). (iii) A `theirs` hole as
a freely instantiable existential (refused by `no_foresight`: it would give the planner foresight no participant has).
**Critique.** (0) The gate's split moved "no unguarded re-plan" from the operation's TYPE (`resubst` took its guard as a
proof argument, which mentions the statement `Dispatched`, so a def module cannot hold it) to the theorems' hypotheses
(`Open.Replan`); `lost_reply_blocks_replan` is what keeps the guard load-bearing. (1) `Open.resubst_wf`'s history-equality conjunct is true by construction; the substance is the
well-formedness and the obligation bound. (2) `unrelated_update_keeps_plan`'s unrelated-store part is true by
construction (the world view never reads it); the revoke-p2 part exercises locality. (3) `holes` needs a finite listing of
each operation's responses. (4) The Coin and Negotiation instance definitions live in the def module (deployed lines).
(5) The external-once gap is a theorem of a delivery/deduplication model this module chose; the reader required it to be
linked to the history (`Internal.ofHist` from `consumed` and the answered entry, stated over `lost p` and `H₀`) or
labelled as the model's. (6) "Linear" is affine: `ret` accepts any Δ, so unused tokens are dropped; the once theorem is
at-most-once. (7) Substitution is single-pass: a filling's own holes are not filled by the same σ, so "replace an
unexecuted sub-component of an entered filling" is not expressible. (8) `Iface.acceptor` was a field nothing read (a
no-op the reader caught): DELETED; "who must accept" remains the `accepts` contract, exercised by no instance yet (named gap).
**Meta-critique.** The lane was briefed to re-cut mini's `IndexedProgram` and it did; the risk was a theory that only
restates mini. The test is the nano bridge: HOSTING-37's `interp_runs` is re-derived as an instance, so the theory says
something about code the kernel runs, which mini's `fold_fusion` never did.

## LANG-68 Lang's deployed term language is a lawful instance of the guarded contextual closure, on its closed-hole fragment (2026-10-20 real; ACTIVITIES-2; ROOT ruled fork (A); cv 01a158c0-ddbf step 3's foundation; the (B) fork is Ember's card, cv 01a158da-0192)
**Why.** LANG-66's closure theory was instantiated by its toy calculus and by CMTT (`cmttLaws`); the generators that make the
Bell an instance (LANG-66 (d)) need the closure's carrier to be what a nano package is written in. ACTIVITIES-1's handoff
asked whether that instance can be HONEST: what are `uses`/`drop`/`strengthen`/`weaken` for a Lang filling such that
`weaken_avoids` and `uses_var` discharge non-degenerately (READER-CONTEXTUAL's HIGH: `drop := id` or `uses ≡ false`
satisfy the strengthening laws)? Answered by building it, not by prose.
**Decision.** `Lang/Contextual/LangCalculus.lean` (def module, 568 lines, no theorem) + `Lang/Proofs/Contextual/LangInstance.lean`
(proof module, 46 theorems): `langData : CalculusData` with `Tm := Lang.Term` (the DEPLOYED term, `Lang/Term.lean`), not
`Lang.Data`: a data value has no variables, so `uses_var`/`hasTy_var` could be met only by bolting a variable onto data,
the lookalike the reader refused. `check Ψ M A := decide (infer [] Ψ M = some A)` (the deployed checker, sound and complete
by `infer_iff`); `uses`/`weaken`/`strengthen` a binder-aware de Bruijn rename (`Term.renameVar`, `lam` and every `case` arm
bind one; `liftIdx`/`lowerIdx` from Core); `drop := eraseIdx`; `var := Term.var`; `lookup := Ψ[x]?`; a hole is `ref n`
(the only hole shape a `Term` has) and `msubst := Term.fillRefs` (closed fillings, no shifting); a structural
`Term.decEq` by hand (17 constructors, nested rows; `Term` had no decidable equality). `LangHasTy Ω Γ t T :=
(∀ d ∈ Ω, d.ctx = []) ∧ RefsDeclared Ω t ∧ HasType (ΔOf Ω) Γ t T` with `ΔOf Ω` name-indexed (hole `n` at package position
`n`, LANG-66's `holeEnv` move) and `RefsDeclared` = every `ref` the template uses is a declared hole (it is what refutes
`msubst := id` and what makes `ΔOf`'s `.nat` placeholder at an undeclared name make no theorem true: `usesRef_fillRefs`
+ `refsDeclared_nil`). `theorem langLaws : CalculusLaws langData LangHasTy`: msubst_lemma ← `fillRefs_typed`
(+ `tyOf_filter`, `ΔOf_getElem?`, `hasType_closed_lift`: a closed filling types under every Γ, used exactly at the `lam`/arm
binders where capture would otherwise occur); check_sound/complete ← `Lang.infer_sound/complete` + `langHasTy_nil_iff`
(whose right-to-left needs `hasType_usesRef`: a term typed under Δ = [] uses no `ref`); strengthen_lemma ←
`hasType_unshiftAt`; strengthen_factor ← `Term.shiftAt_unshiftAt`; weaken_avoids ← `usesVar_shiftAt` (unconditional);
hasTy_var ← `HasType.var`; uses_var by `simp`. Toys: `lang_strengthen_toy` (`strengthen 1 (app (var 0) (var 2)) =
app (var 0) (var 1)`, weakened back: the strengthening is not the identity); `lang_template_toy` (`app (ref 0) (nat 3)`
typed WITH the hole `⟨0, [], nat → nat⟩`, NOT without it — refuted by `RefsDeclared`, and by `HasType` too since
`ΔOf [] = []` — filled with `λx.x` by `rfl`, typed with the hole gone through `langLaws.msubst_lemma`).
**The boundary, as a theorem.** `langTemplate_no_hyps : Template.Typed tpl LangHasTy → ∀ I ∈ tpl.Ω, I.hyps = []`. A Lang
`ref` is a closed package reference: it carries no local context and no substitution, so every hole of a typed Lang
template is CLOSED, and three closure paths are EMPTY ON EVERY LANG TEMPLATE: the `strengthening` outcome
(`repairSelected`'s `D.uses` branch), the alternative-by-hypothesis outcome, and hypothesis-derived supports
(`effSupports`' second summand). They are exercised only by the CMTT instance. So the bridge the generators build
(LANG-66 (d), next) is over the FULL `CalculusLaws` restricted to the closed-hole fragment, not over a sub-structure of
the laws; the fragment's name is this theorem.
**Price.** No landed theorem gains a premise; no landed statement changes (READER-CONTEXTUAL: `git diff --stat HEAD`
empty before the two new files; nothing landed imports them). SIZE: two modules, one proof module, ~1,380 Lang lines (568
deployed), 46 theorems, max dependents +1 (the instance is OVER the deployed checker: one more dependent of its closure).
**Vacuity read.** READER-CONTEXTUAL (`a883dc3fb9dca28c8`, resumed), 47 theorems with the disjunct check per theorem,
each iff's two sides and each ∃ witness named: LAND-WITH-FIXES, nothing vacuous or false; the two LOWs applied
(`langHasTy_closed_holes` was `h.1`, a projection: DELETED, the conjunct is cited instead; `ΔOf`'s docstring names the
theorems that make its placeholder harmless); the MEDIUM is a closure-design item made visible by this instance, filed
cv 01a158da-017c for CLOSURE: no operation requires `Template.Typed` (C3 moved it from the structure to a predicate), so a
closure over an UNTYPED template with a non-empty hole ctx reports `verified` for an open filling (`check [nat] (var 0)
nat`) that `fillRefs` would place unshifted — no landed theorem claims that state Derivable (every derivability theorem
takes `ht`), but the report is the checker's verdict in a context the template never justified; its own `lang:` with its
own read; the generators state Typed for every generated iface (ctx = [] by construction).
**Alternatives.** (i) `Tm := Lang.Data` with a variable constructor bolted on: refused, the reader's degenerate class in
new clothes. (ii) A curried encoding of contextual holes (`ref n : fnOf Ψ A`, occurrences `app (ref n) σ…`): refused
here because `msubst` must then wrap fillings in `lam`s over Ψ, which needs Ω — a `CalculusData` signature change
(`msubst` taking Ω) restating `msubst_lemma`/`Derivable` and everything through them; not foreclosed. (iii) (B) CMTT's
`u[σ]` as an 18th `Term` constructor `hole n σ`: the honest contextual instance in the DEPLOYED language; a `lang!`
(checker, BigStep, printer/reader, the `lang/package` wire with CODEC review, every Term induction one case each, every
package re-ids; premises added: none known). ROOT ruled (A) now and sent (B) to Ember as a design fork: under (A) the
strengthening outcome is a theorem of the MODEL only, reachable by no deployed package — the honestly-labelled-caveat
class; the question is whether nano's deployed language should carry what its theory proves. (A) does not foreclose (B):
the generators' statements are over `LangHasTy` and survive it losing the `d.ctx = []` conjunct.
**Critique.** (1) The instance proves the laws for ALL Lang terms, but every template the laws reach has closed holes;
the contextual half of "contextual modal types" is, for Lang, a theorem about a fragment nothing deployed inhabits
(the card above). (2) `fillRefs` does not shift: sound only because fillings are closed, which `LangHasTy []` forces;
a future (B) must add the shift. (3) `ΔOf` is positional over a name-indexed list with a placeholder; the honest shape
would index `HasType`'s Δ by name, which is a change to the deployed checker's signature, refused for this landing.
(4) `Term.decEq` is 272 hand-listed off-diagonal cases (the Ty.lean idiom); `deriving` is refused by Lean v4.30.0 on
the nested inductive. (5) The reader's MEDIUM is older than this landing (C3's restructure of LANG-66 made `Template.Typed`
a predicate no operation demands); this instance is the first with a non-trivial ctx to make it bite.
**Meta-critique.** The handoff's question had a tempting prose answer ("the bridge is over a data-only sub-structure of
the laws"); it was WRONG in both directions — the laws discharge in full, and the restriction is on the templates, not
the laws — and only building the instance showed where the restriction actually sits. The pull to resist next is to let
`langTemplate_no_hyps` read as a limit of Lang rather than as a design choice ROOT made and Ember may reverse.

## LANG-69 Split the contextual closure proof module by responsibility (2026-10-20 real; CX-ACT; cv 01a158c0-ddae)
**Decision.** Replace the 1,533-line Lang/Proofs/Contextual/Closure.lean with eight proof modules:
ClosureStatements (calculus laws and judgments), Judge (tokens, judgment, provenance, withdrawal, lookup),
Repair (candidate pass, coherence, locality and the exact work log), Outcomes (soundness of repair outcomes),
Operations (operation frames and history prefix), Soundness (conditional soundness and preserved invariants),
History (selection, acceptance, consumer boundary and sessions), Stability (value guards and grounding).
CoreInstance and LangInstance import ClosureStatements only; Experiments imports History and Stability.
There is no compatibility import hub. This is moves plus imports and module wrappers, with NO statement changes.
**Price premises.** None. No landed theorem gains a hypothesis; none is restated. No definition in the deployed
language changes, no package re-ids, no wire moves. LANG-68's LangCalculus line count was 567, not its recorded 568.
**Verification.** A source partition audit accounts for every original line 32..1532 exactly once, preserving
all 102 declaration names (89 theorems) and every statement/proof body byte-for-byte. The scoped build of
Experiments, CoreInstance and LangInstance is GREEN (59 jobs), under 6G/two threads and Lean's finite default
heartbeat cap. The original statements and their disjunct readings are the LANG-66 reader's unchanged statements;
this change adds no assertion, disjunct or premise. No new semantic check is added, so no new mutation plant
is applicable to these moves. The consumer build checks resolution and composition after changing imports.
**Alternatives.** Keep an import-only Closure compatibility module: rejected because it preserves a broad
dependency entry point rather than teaching each consumer which family it needs. Split by line count: rejected
because it makes the module boundaries arbitrary and leaves unrelated dependencies together.
**Critique.** Soundness still joins operation frames with repair outcome lemmas, and History consequently imports
both; this follows the current proof dependencies, not an ideal independent theory. A further split should be
driven by an actual consumer or rebuild bottleneck, not a target module count.
**Meta-critique.** Moving code can masquerade as simplification. Here the measurable benefit is that the two
calculus instances no longer depend on the 89 closure theorems; only their laws/judgments are imported. The
statement/body equality audit prevents a proof cleanup from slipping into this structural change.

## LANG-72 Boundary declarations and independent reuse licenses (2026-10-20 real; CX-P2)
**Decision.** Add Boundary def/proof modules over the landed closure, without changing its judge,
repair, selection, or existing theorem statements. A boundary belongs to an Iface and declares a
subset of four observations: typingInterface, logicalContract, observableBehavior, costGuarantee.
The order is inclusion of promises; intersection/union and empty/full declarations form the
powerset lattice. Cost and behavior are explicitly incomparable. Each boundary supplies its
behavior projection and cost promise independently of the admission budget.

Boundary.failures compares declared observations against the retained old reference.
Boundary.obligations reads actual old/new selections and emits named (hole, observation)
obligations; absence on either side emits every declared obligation. Exact failure coverage,
empty-list equivalence, and monotonicity connect that executable report to its specification.
Each reuse theorem needs only its own observation absent from the failure list, so an unrelated
cost failure cannot invalidate the membership cache license. Typing reuse applies the existing
CalculusLaws.msubst_lemma to a client template; contract reuse applies a client's proof conditional
on the guard; behavior reuse covers every function of the declared projection; cost reuse composes
a bound with client overhead. Typing, contract and cost additionally require old success:
equality of two failures does not establish validity.

The dependent-type counterexample uses inhabited Fin 1 and empty Fin 0 despite both indices
having carrier Nat. A client whose family factors through preserved behavior transports its
inhabitant by equality. The pruning corollary reopens every retained member of an explicit finite
region whose sole exclusion token is withdrawn, independent of a selected answer's support.

**Experiment.** Actual fuel-bounded binary and structural linear searches compute membership and
key-probe counts. On eight sorted elements, searching for seven takes three versus eight probes.
An existing Session proposes both, selects binary, withdraws its sortedness token, then selects
linear. Its computed statuses are suspended [sortedToken] / verified, with selection 1 and the
same true answer. Boundary.obligations reports exactly costGuarantee: admission budget stays eight,
the separate boundary promise stays four (1 + log2 8). A theorem instantiates the general cache
license despite that cost failure. Queries 0..9 exercise positive/negative membership; [2,0,1]
exposes binary's dependence on sortedness. Another session has an empty selected support trace
but rejudges and reopens the excluded alternative when its exclusion token is withdrawn.

**Price premises.** None. No landed theorem gains a hypothesis; none is restated. Only the two
new modules and this append are proposed. No wire, Store, pins, refusals, or existing gates change.
SIZE adds two modules (one proof), 451 Lang lines (179 counted as deployed), and 29 theorems.

**Alternatives.** A four-element chain would falsely imply that a cost promise entails a particular
behavior; the independent observations require the powerset lattice. Requiring the whole
declaration to pass before any reuse would prevent the card's membership/cost separation.
Replacing the closure judge with a boundary-aware judge would couple this independent audit to
admission and violate this wave's append-only ownership discipline. This addition is a callable
audit over actual selections, not automatic enforcement in existing select/repair. A future
consumer can invoke it without replacing the judge.

**Verification.** Scoped Lang.Proofs.Contextual.Boundary build is green under 6G/two threads;
proof maxHeartbeats is 400000 (definitions retain Lean's finite default). Five temporary mutations
in the new definition module each failed compilation of named concrete theorems, and restoring
the original source rebuilt green. Suppressing typingInterface, logicalContract, observableBehavior,
or costGuarantee makes all_observation_checks_exercised false. Suppressing cost additionally
makes binary_to_linear_boundary false. Treating missing selections as no obligations makes
unfilled_boundary_obligations false. Whole plant outputs were read, including diagnostics;
the logs are CX-P2-plant-<observation>.log and CX-P2-plant-missingSelection.log in hbox logs.
The actual diagnostic is "Tactic `decide` proved that the proposition ... is false", at log
line 14 for typing/contract/behavior and the cost-only boundary, line 17 for cost's all-four
check, line 4 for missing-selection. No persistent check was removed or weakened.

**Critique.** The cost is key probes, not runtime: List.take/drop work is not charged. The
eight-element experiment is not an asymptotic complexity theorem or universal search correctness.
The guard is a decidable contract and the generic cost field needs an instance-specific connection
to execution; this experiment computes it from the algorithm. The search CalculusData is a
demonstration, not deployed Lang and not a new claimed CalculusLaws instance. The general typing
license requires lawful L and applies independently to the already lawful contextual instances.
A boundary's behavior projection is an abstraction choice; consumers reading syntax or other
undeclared details do not receive the reuse license. Full declaration equality can preserve
false checks, hence the explicit old-validity premises in the relevant reuse theorems.

**Meta-critique.** It would be easy to encode four labels and call their equality modularity,
or to equate a chosen fallback with a repaired performance guarantee. Concrete session outputs,
computed costs, the actual meta-substitution theorem, arbitrary contract/cache clients, and
mutations keep those shortcuts visible. The additive audit has a real consumer in the session
experiment but is not a deployed protocol. Independent second-agent vacuity/disjunct review is
still required before ROOT lands; this lane only prepares READY.

**Verification correction (same unlanded change).** The source refusals gate disallows any local
set_option budget override. The unnecessary 400000 override above was removed; both modules now
build under Lean's finite default maxHeartbeats cap. The gate itself is unchanged.

**Independent second read (2026-10-20, CX-READER-P2).** LAND: all 29 theorem statements
read with the disjunct check; no conclusion offers an Or escape. Reflexivity and bounds are
ordinary lattice laws, not repair evidence. Existing theorem signatures are unchanged.
The five real mutation logs were read whole; the independent capped scoped build passed.
The callable audit, concrete-session scope, and probe-count cost limits remain as stated above.

## LANG-72 Alternative worlds and world-indexed grounding (2026-10-20 real; CX-P3; contextual program CARD P3)
**Decision.** Add Lang/Contextual/Worlds.lean and Lang/Proofs/Contextual/Worlds.lean.
This is a demonstration Mini can take: an extension of LANG-66's rule model, not another
kernel World or an admission path. Normal rules have positive bodies, default-absence tests
and immutable external support tokens. Each proposed world determines its OWN positive
reduct; grounded consequences use the landed Rule/lfpIter/Derives definitions.
The checker first checks that its finite iterate is closed under every reduct rule.
Only a closed iterate can yield a completed yes/no answer. Otherwise the result is unfinished.
It then compares both directions: every proposed atom grounded, every grounded head proposed.
This is equivalent to the independent inductive Stable judgment (check_decides), not a
definition of stability by the checker. Saturation needs no guessed sufficient fuel premise.

The analyzer enumerates every sublist of the distinct program heads, including the empty
world, and keeps successes as separate worlds. collect_checked and collect_mem rule out
silently dropping pending candidates. analyze_sublist_exact connects completed search to
Stable on every canonical world; mem_subsets_iff proves enumeration coverage.
The four reports are noJustification, alternatives (two different witness worlds),
conflictingEvidence (one evidence world), and unfinished. supported and noWorld cover the
two additional ordinary cases without conflating an empty world with no world.
A query supplies two atoms intended as incompatible evidence. Default absence is not an
explicit negative atom. A conflict in the caller's proposal is diagnostic, not admission
of that proposal. alternatives_sound proves both witnesses stable and separately supporting
the queried atoms; noJustification_sound requires completed, nonempty-world search and no
queried evidence in any resulting world.

**Experiments.** Kernel decide evaluates the two-rule program p :- not q; q :- not p,
its exact worlds {p} and {q}, and rejection of their union (also proved not Stable).
A concrete session withdraws p's rule token, then q's, reasserts p's, then q's:
[{q},{p}] -> [{q}] -> [{}] -> [{p}] -> [{q},{p}].
Reissuing p's token at a new version does not re-enable the rule citing the old token.
The positive cycle has a unique grounded world; withdrawing its grounding leaves only the
unrelated fact 5 and consequence 6, and reassertion restores it. Counting still keeps its
two cycle members for every iteration. unfounded_excluded lifts the landed unfounded-set
theorem to every accepted world, not just the experiment.

**Price premises.** None. No landed theorem gains a hypothesis; no existing statement changes.
New world-indexed statements restate the consequences of lfpIter_sound,
unfounded_not_derivable, cycle_loses_grounding and counting_keeps_cycle without editing them.
Token, Edit, applyAll and reissue_never_reenables remain unchanged.
Two new modules, 123 definition lines, 316 proof lines, 21 theorems. No wire or Store moves.
All changes belong to LANG, with SIZE.md regenerated by the standard gate tool.

**Alternatives.** Unioning supported atoms is refuted by admissible_not_union_closed.
Positive support counting is refuted by cycle_loses_grounding_over_worlds beside
counting_keeps_cycle_over_worlds. Treating an exhausted finite iterate as a completed
rejection confuses operational progress with semantics; explicit saturation removes that
assumption instead of pricing fuel as a semantic limit. A fixed sufficient round bound
could later prove automatic completion, but is not needed for the exact completed verdict.

**Verification.** Scoped build Lang.Proofs.Contextual.Worlds GREEN under 6G/two threads and
400000 maxHeartbeats. Five mutation plants bypass default absence, external applicability,
grounding, the reverse inclusion, and saturation separately. Each mutant definition BUILDS,
then the real Lean kernel rejects a concrete decide theorem; restored source and probes GREEN.
Real outputs: /tank/dregg-build/nanodregg/logs/CX-P3-plant3-{defaults,premises,grounding,closure,completion}.log.
The expected kernel line is "error: Tactic `decide` proved that the proposition", followed
by the exact false proposition; full outputs were read. Earlier harness attempts that hit
an unused-variable linter and then a missing rebuilt olean were not counted as teeth.
The source gates and per-theorem disjunct reading are recorded in CX-P3's lane report;
ROOT's second reader must approve before landing.

**Critique.** This is a finite reference analyzer, exponential in the number of distinct heads;
it recomputes after edits and is not a differential-dataflow implementation. It proves exactness
when completed, not a general sufficient iteration budget. Enumeration represents worlds as
canonical sublists; check and Stable also accept other list orders, but analyze returns only
the canonical order. Query incompatibility is supplied by the user of the report, not inferred
from arbitrary atom numbers. Conflicting evidence is paraconsistent diagnostic data, not an
explosion rule, and does not itself prove the proposed world stable. The one-level guarded
closure still does not make holes support other holes: this extends its separate rule model.

**Meta-critique.** The tempting shortcut was four hand-written tags beside two Boolean examples,
or defining admissibility by the successful check and calling its projection soundness.
The inductive Stable judgment, completed-search equivalence, and mutation plants instead
connect the computations to independently stated semantics. The remaining temptation is
calling a finite reference analyzer a production incremental engine; no such claim is made.

**Source-gate correction before readiness.** The first source-gate run correctly refused the
explicit 400000 heartbeat override (refusals.py). Removed that override; the final source uses
Lean's stricter default 200000 heartbeat cap. Final counts: 123 definition + 314 proof = 437
Lean lines, still 21 theorems. Mutation probes used the finite 400000 cap in lane scratch.

**Independent second reader (CX-READER-P3, 2026-10-20 real).** LAND: all 21 theorem
statements read with the disjunct check; no vacuous escape branch or changed landed
signature. Both new modules passed a scoped rehashed build and fresh source elaboration
under 6G/two threads and maxHeartbeats 200000. Read all five real mutation outputs
whole, their successful mutant builds, controls, and restored runs; each refusal
is the expected kernel decide failure. No Lean correction required. The finite
reference-analyzer and caller-supplied incompatibility limits above remain explicit.

## LANG-73 First-class repair values, composed residuals, policy selection and checked transport (2026-10-20 real; CX-P4)
**Decision.** New `Lang/Contextual/RepairObjects.lean` and two proof modules
(`RepairObjects`, `RepairExperiments`) extend LANG-66..69 without changing any landed declaration.
A `Change E w v` indexes a `Repair D e` value from `State D w` to `Result D v`.
Atomic repairs call the existing incremental pass. Composition threads state and concatenates
residual checkpoints, exact inspection logs and named transport refusals. Each residual retains
its world, template, alternatives and history; its obligations combine the closure's outstanding
obligations with the full suspended outcomes, without duplicates. It resumes through another edit.

The law `Repair.Sound` separates coherence from conservation of the retained analysis problem
at every world. `atomic_sound`, `ofChange_sound` and `compose_sound` establish it for the
actual interpreter and arbitrary sound constituent repairs. `repair_correctness` compares the
final observation against from-scratch analysis of the ORIGINAL retained problem at the final
world; conditional soundness and exact-work locality remain independently named results.
`compose_keeps_obligation` preserves intermediate obligations even when later edits resolve them.

`select policy` minimizes a supplied cost function among intent-eligible candidates that judge
verified NOW; ties choose the leftmost candidate. It calls the landed select for authority,
accepted history and final checking. The generic index, eligibility, minimality and selection
theorems connect the result to the actual retained candidate. Policy is not an input to judge.
The existing hard budget remains enforced: moving a preference out of the judge does not permit
silently weakening its established cost guarantee.

A `Correspondence` stores source/target interfaces and forward/backward term maps.
`Correspondence.Checked : Prop` certifies typing both ways and both inverses on checked
fillings; `Registry.Sound` certifies every certificate lookup. This follows the existing
Data/Laws boundary, including LANG-67's explicit guard hypothesis, not an executable claim to
decide arbitrary function equivalence. `transport` verifies the certificate lookup and source
typing, conserves every effective source dependency, computes the image and freshly judges the
destination, including its independent guard, supports, blockers and hard budget. Its evidence
names the exact registry entry and retains the old term and image. The old five outcome values
embed unchanged in a type with a sixth semantic case, `transported`. `withTransport` makes
the offer part of a repair value's result. Transport offers do not change a template or accepted
selection; the example image reaches ordinary propose/select in an explicitly new template.

**Price premises.** Landed theorems gaining a hypothesis: none. Landed theorems restated: none.
No wire/Store change, package re-id or re-genesis. Three modules, two proof modules, 719 Lean
lines (188 deployed), 33 theorems. No existing source module or import is modified.

**Evidence.** Scoped build of `Lang.Proofs.Contextual.RepairExperiments`: GREEN, 14 jobs,
6G/two threads, Lean's finite default maxHeartbeats 200000. Concrete sessions computed by decide cover withdrawal of
the last support, resumption and preserved intermediate residuals; minimum-cost vs intent choice;
wrong chooser, accepted prefix and hard-budget refusal; a representation change, unknown
certificate, ill-typed source, destination guard/support/cost refusal; distinct transport output
and normal selection of its image. The world-repair session uses cmttData. The representation
experiment is deliberately a data-only tagged-Nat checker, NOT a purported CalculusLaws instance:
its registry equivalence is proved for every Nat payload, and `transport_typing` is the generic
bridge over any lawful calculus. The concrete session's coherence is proved from the session
preservation theorem, so the main repair correctness premise is inhabited.

Nine real mutation builds refute omitted intent/current judgment, reversed cost order, ignored
certificate ID, omitted source/destination checks, lost source hypotheses, discarded intermediate
residuals and a false backward map. Complete logs were read under lane-prefixed hbox logs; each
failed in Lean's named contract, not in the driver. Restored source builds GREEN. The certificate
binding was made explicit in transport_sound after reviewing the certificate mutation.

**Alternatives.** Editing the five-constructor landed Outcome would break every exhaustive match
and violate this wave's append-only rule; embedding it preserves those proofs while extending
the result. Treating a forward function alone as an equivalence would accept arbitrary replacement
and fails the inverse plant. Automatically rewriting the old template would require a theorem
about all its clients and could violate accepted history; this operation offers a checked filling
to an explicitly supplied destination, just as replacement is an offer.

**Critique.** Equality of transported terms is syntactic; quotient or observational equivalences
need a separately stated relation and its laws. A raw caller can supply an unsound registry:
transport_sound requires Registry.Sound, as the existing calculus and replan theories require
their laws. This is a Lean-level demonstration, not a new wire certificate format or solver.
Repair correctness deliberately compares candidate statuses, not history-dependent selections.
The composition trace retains entire snapshots; this exposes obligations but is not yet a
space-efficient deployed history representation.

**Meta-critique.** A wrapper called Repair could falsely imply an algebra; the test here is
compose_sound over arbitrary sound implementations and agreement with the original retained
problem, alongside a mutation that actually loses an intermediate obligation. Likewise a
transport tag alone proves nothing: the certificate is tied to a checked two-sided map, the
destination is rejudged, and the image has a real selection consumer. The remaining temptation
is to present a tagged-value demonstration as a deployed-language equivalence engine; it is
explicitly labelled as a checker-only experiment.

## LANG-70 P5 logical statuses and alternating simulation; P1 finite interaction guards (2026-10-20 real; CX-P15)
**Purpose.** A demonstration Mini can take, implementing contextual-program P5 first and P1 over its
status type. No wire or Store change. Four new modules; every old declaration remains byte-identical.
**Decision.** P5.LogicalStatus has witnessed, open(first obligation, rest), refuted(evidence), and
outsideThisProcedure(reason). Open is nonempty by construction. P5.judge answers a Problem whose finite
domain is explicit and distinct from its retained search list. A witness is checked for domain membership
and acceptance. Refutation carries an exclusion enumeration: checkRefutation checks coverage of the
question's domain AND replays every exclusion. refuted_sound proves every member of that domain fails;
no_certificate_never_refuted and exhausted_is_open prohibit interpreting search failure as impossibility.
This is a finite completion procedure, not a solver claiming to decide arbitrary Lean propositions.
The generic status type can carry other evidence formats; this procedure admits only its replayable format.
Outside is a distinct constructor, with unsupportedFragment/budgetExhausted explanations.
**Partial evaluation.** Formula/evaluate leaves unfilled atoms suspended, also under negation.
Conjunction is strict and combines outstanding atom names. There is no missing-atom-as-false conversion.
**Polarity.** Machine is an input-deterministic interface automaton with nondeterministic outputs.
AlternatingSimulation matches specification inputs and implementation outputs with related successor
states; Refines is pointed existence of that relation. Reflexivity, transitivity, input-session
preservation and arbitrary finite mixed-session safety are proved. Moves/Action.owner uses LANG-67's
Polarity directly. price_refines permits more accepted prices and fewer replies. The concrete seven-price
session breaks after ten becomes five; adding a reply also fails refinement. no_foresight is consumed
by P1.coin_interaction_obstruction over ALL uniform substitutions; the P5 finite coin question computes
a refuted status over its two answer candidates.
**Interactions.** Interaction is a named Boolean counter-test. Design.complete versus Design.gaveUp
separates completed repair from daimon-like behavior. OrthogonalTo admits gaveUp; inspect always
reports its named gaveUp obligation, even with zero tests. Eligible is admissibility intersected with
the orthogonal family. adding_obligation proves exact intersection, not just monotonicity;
required_implies_tested / eligible_antitone give the tested/required direction. Reports carry the
exact Interaction objects, not only their potentially colliding display names. inspect_witnessed and
analyze_witnessed connect returned witnesses to the actual report's scope. analyze uses the P5 judge;
analyze_refuted quantifies over the declared domain, never over just retained repairs.
**Existing judge connection.** withInteractions installs a finite conjunction as Iface.guard;
singleton_judge proves equality of the entire old/new candidate verdict for the original predicate.
judgeAt consumes Family indexed by hole and world; its verified iff spells out interaction, typing,
support, blockers and budget. Nullable.required uses an explicit environment precondition, allowing
the existing Session.run/repair to demonstrate non-null withdrawal as setEnv false, then suspension,
tolerant replacement, checked replacement, or explicit re-preconditioning as setEnv true.
Those sessions compute by decide; unchecked crashes on null, tolerate supplies zero, check returns
rejectedNull. The handler enumeration is a model of null handling, NOT a claimed lawful CMTT calculus
and NOT execution of a deployed nullable package.
**Price premises.** None. No LANDED theorem gains a hypothesis; no landed statement is restated or
edited. All old candidate-judge and repair results stand. Added imports reach only these new leaf
modules; no existing consumer imports them, and the Host closure is unchanged.
**Alternatives examined.** Mapping every exhausted retained search to refuted is wrong when an unretained
witness exists (unretained_repair_exists). Making refuted a reason string loses checked impossibility.
Identifying daimon orthogonality with successful repair accepts a never-answering object. Covariant
input narrowing breaks seven; output broadening breaks peers. Label-only refinement without successor
relations cannot justify mixed-session preservation. The implementations retain the distinctions.
**Critique.** (1) Refutations are relative to the EXPLICIT finite domain and acceptance function: they
say nothing about candidates outside it, and the generic data constructor itself is not a proof;
the authority is judge plus refuted_sound. (2) This is finite interaction orthogonality, not full ludics
biorthogonal closure. (3) Arbitrary world-dependent Family changes are NOT tracked by the landed
touches function; judgeAt makes no repair-locality claim. The concrete session uses env changes, which
already touch every candidate. (4) Re-establishing non-nullness is an explicit caller assumption, not
evidence conjured by the checker. (5) Alternating simulation here excludes internal actions, fairness,
and nondeterministic input transitions; SafeFor proves absence of refused interactions, not progress.
(6) C3 keeps data and laws separate: consumers must use the named checked operations and soundness
theorems, not treat arbitrary constructed Reports as evidence.
**Meta-critique.** It would be tempting to rename the old candidate statuses and call P5 complete, or
to add unused interaction metadata to the old guard. The domain/retained distinction, exact returned
scope, singleton bridge, concrete withdrawal sessions and mixed-session refinement theorem prevent
those substitutions. The remaining temptation is to sell bounded model experiments as deployed
behavior; the nullable model and finite procedure limits are therefore explicit above.
**Validation.** Scoped build of Lang.Proofs.Contextual.P5 and P1 under 6G/two threads, Lean default 200000
heartbeat cap (no source override); concrete theorems by decide. Separate mutation scratch modules exercise domain
membership, certificate coverage/replay, exhaustion status, procedure limits, suspended negation,
admissibility, tested interactions, daimon status and the nullable guard. Source gates and per-theorem
self disjunct read are recorded in CX-P15's private lane report.
**Independent second reader (CX-READER-P15, 2026-10-20 real).** LAND. All 45 theorem statements
read with the disjunct check; no escape disjunct or changed landed signature. Both new proof modules
passed an independent scoped build under 6G/two threads and default maxHeartbeats 200000. All twenty
control/mutant outputs read whole and all ten saved source mutations inspected; the failures are
semantic Lean failures, with no harness error. No theorem correction required. Finite-domain,
nullable-model and refusal-safety limits above remain explicit.

## LANG-P10 Declared verifying traces, complete observations and early cutoff (2026-10-20 real; CX-P10)
**Decision.** A demonstration Mini can take. New Trace data/proof modules factor the existing
candidate judgment through a finite observation: the guard's declared environment values,
missing effective supports (including used context hypotheses), and live blockers.
Guard.run receives only the projected values; it never receives the ambient environment.
Guard.install constructs that interface. It is not an assertion that an arbitrary pre-existing
opaque guard obeys a declaration. evaluate_observe identifies the entire verdict with the
landed judge on this constructed interface, including typing, guard, blockers, supports and cost.

Cached binds a candidate to its trace; Valid equates its stored status to evaluation of that
trace. seed establishes Valid, refresh and repair preserve it, and from_scratch_consistency
equates every resulting status with fresh judgment at the new world. These are exact values,
not hashes, so there is no collision premise. Equal-valued edits are clean. repair_minimal
identifies exactly the candidate indices with changed traces; repair_once makes the log Nodup.
This is minimality relative to the declared reads and fixed candidate/interface/guard definitions,
not synthesis of the globally smallest dependency set or a dynamic transitive scheduler.

A pass separately records changed statuses. early_cutoff proves that a reader of a selected
candidate's status is not dirtied when fresh judgment equals its previous status. Concrete
sessions include a changed guard input with the same result, a changed result propagating to
its reader, and a second pass that stays clean because the new trace was saved. Selection
identity is fixed across this pass; the function does not choose alternatives or repair history.
Clients reading behavior, cost, or choice changes need their corresponding Boundary observation.

**Complete package observations.** checkedJudge collects every declared environment key,
effective support and blocker before computing a verdict. Missing.environment / Missing.token
are distinct refusals. A pinned-absent row is some false; an omitted pin is none. capture_sound
and checkedJudge_sound assume only authenticity of PROVIDED observations, and derive agreement
with the complete world's judgment; there is no complete-pin-set hypothesis. checkedJudge_total
shows success is inhabited. This directly addresses the missing-negative-observation mechanism
identified by the activities reader. The adapter is executable Lean; the concurrent Std.hole
generator is not present on this worktree's main and does not yet call it. This change does not
claim to repair that generator or establish its whole-Receive simulation. Its integration must
preserve the omitted/pinned-absent distinction at the real row-view lookup boundary.

**Literature.** Mokhov, Mitchell and Peyton Jones, Build Systems à la Carte (ICFP 2018),
Def.2.1 p.79:3, Def.3.1 p.79:11, §4.2.2 pp.79:14–15:
https://simon.peytonjones.org/assets/pdfs/build-systems-original.pdf .
The guard construction strengthens the existing Protocol.Frag.ReadsOnly pattern by preventing
undeclared reads at its interface. Static per-filling read sets are intentionally distinct from
the paper's dynamic traces. Append-only add_decl_doc commands attach the requested literature
to Candidate, box_ambient_free, reissue_never_reenables, and both repair_agrees_from_scratch
theorems. The latter retain their names and explicitly say from-scratch consistency
(Stein–Chang–Sridharan, PLDI 2021, Thm.6.1 PDF p.10).
AGM recovery (1985 p.513, postulate −6) is rejected as a policy of recovery by identifier,
not refuted mathematically: a re-versioned token is not AGM's same proposition.

**Price premises.** Landed theorems gaining a hypothesis: none. Landed theorems restated: none.
All landed declarations and proofs remain byte-identical; five old files receive only trailing
documentation commands. New consistency statements price cache coherence, established by seed
and preserved by repair. New checked-boundary statements price authenticity of supplied values,
as the receiver already must; complete observation is established by collection, not assumed.
No wire, Store, gate, pin, refusal or existing admission path changes. Four new modules.
No foreign ownership path is edited; SIZE.md is the shared generated view.

**Alternatives.** An annotation beside an arbitrary E -> Term -> Bool guard would merely move the
old completeness premise into a law callers might never establish. The projected guard removes
that escape. Defaulting absent supplied observations to false recreates the blocker omission
defect. Hashing the observations adds collision assumptions without helping this bounded
demonstration, so values remain exact. Comparing output statuses only would miss changed inputs
and could reuse a stale success. Dirtying every reader on input change loses early cutoff.

**Critique.** The trace declaration can overapproximate semantic dependencies: a guard may ignore
one supplied value, and static typing failure may render guard/token values irrelevant. The
minimality claim is about the declared task graph, not semantic optimality. Trace verification
still scans declared reads, and the pass scans its candidate list; this is not an O(edited)
reverse-indexed deployed scheduler. Candidate, guard or interface changes require reseeding;
no self-tracking claim is made. There are no hole-to-hole support cycles here. Authentication
of supplied observations must connect to real Receive pins before this adapter certifies a
deployed package. All concrete teeth use the actual landed CMTT calculus.

**Meta-critique.** The tempting shortcut was to rename locality as minimality, or call an
extra equality hypothesis complete observation. The exact work log, structural guard input,
checked missing reads and changed-output log provide separate mechanisms. The remaining risk
is overstating the adapter as a deployed-package fix: that consumer connection is explicitly
not claimed. No theorem says equality of status implies arbitrary contextual behavior equality.

**Verification.** Scoped build of all four new modules and all five documentation appendices is
GREEN (logs/CX-P10-docbuild.log); default 200000 maxHeartbeats, 6G/two threads. There are
34 new theorems: 20 generic statements and 14 concrete teeth/invariant statements. Eight real
definition mutations each built, then the actual Lean kernel rejected the executable tooth.
Missing-blocker omission: logs/CX-P10-plant-missing-blocker.log:1, Tactic rfl failed on the
named missing-token refusal; guard/support/blocker observation deletion, always/never dirty,
no cutoff and stale traces: logs/CX-P10-plant-*.log:1, Tactic decide proved the proposition false.
All eight complete outputs and mutant-build logs were read, including error/unbound/missing-file/
Traceback control scan. There are no harness failures. Restoring source is GREEN. Source gates
with explicit changed paths and message are GREEN (CX-P10-gates1.log); final metadata check and
each theorem's disjunct read are in the lane report. ROOT's independent reader must review before
landing. No landing was launched by CX-P10.

**Independent second reader (CX-READER-P10, 2026-10-20 real).** LAND. All 34 statements
and their definitions/proofs read with the disjunct check: no escape alternative or changed
landed hypothesis. The five existing Lean files preserve every byte of main's prefix and
append only add_decl_doc. Def.2.1 minimality is specialized to fixed candidate-index tasks
over declared finite reads; repair_once and the actual refresh branch supply at-most-once
evaluation. Early cutoff uses equality of status after a genuinely changed input, for readers
whose observable is that selected status. These are the paper's properties on this explicit
one-level graph, not claims of semantic dependency optimality or a dynamic scheduler.
All eight saved mutant definitions, successful mutant builds, entire tooth outputs and
restored control were read: semantic kernel failures, no harness failures. An independent
fresh rebuild of all nine affected source modules passed at 6G/two threads and 200000
maxHeartbeats (logs/CX-READER-P10-rebuild.log). No source correction was needed. The
complete-observation adapter still requires the separately owned Std.hole receive-path
integration; the decision above accurately retains that boundary.

## LANG-P12 Separate certified acyclic hole-provenance adapter (2026-10-20 real; CX-P12)
**Decision and ruling.** Implement ROOT's alternative (B) as an additive adapter, a demonstration
Mini can take. The input has a finite closed namespace of holes, expressions with alternative
and joint dependencies, finite token-provenance leaves, and natural-number rank witnesses.
Validation scans every actual reference, including undemanded holes and branches whose token
polynomial is zero. An accepted edge strictly decreases rank. The first failed edge returns
fixedPointDependency(hole) for a direct self-reference or rankNotDecreasing(consumer, dependency)
otherwise. An invalid rank witness is not asserted to prove the graph cyclic.

The output is exactly the LANDED carrier List (List Token × List Token) of Closure.provenance,
including negative token literals. Expansion distributes joint requirements over alternatives.
Successful adapt results have independent finite proof-tree semantics (Derives): adapt_correct
is an equivalence for every token world, with no caller-supplied acyclicity hypothesis.
unroll_stable preserves the exact polynomial, including order/multiplicity, above the checked
rank bound; unroll_equation proves all graph equations exactly. Depends is nonempty dependency
reachability; adapt_acyclic excludes every self-returning path, and cycle_refused returns a
named error even for an undemanded cycle. refusal_explained ties every emitted reason to an
actual nondecreasing reference and exact endpoints. Ranked witnesses are accepted, not merely
sound when some unrelated check happens to accept them.

**Connection to the landed closure.** chain_exact handles arbitrary finite local polynomials.
chain_candidates consumes the LANDED provenance_iff directly to equate the new two-hole
derivation with verification by BOTH actual candidate judges. Leaves retain the landed
fixed-environment scope: an environment change requires regenerating these leaves. This is
not P9's all-environment carrier, and this lane has no unlanded dependency on P9. Token edits
can evaluate the same finite polynomial at another liveness world.

**Price premises.** LANDED theorems gaining hypotheses: none. LANDED theorems restated: none.
No existing Lean file or import is changed, including every Worlds statement. New premises
Ranked and rank bounds belong only to new helper theorems; adapt_correct derives the needed
certificate from the executed validator. Four new modules, two proof modules, 388 Lean lines
(101 deployed), 31 new theorems. No wire, Store, package identity, gate, ceiling or pin changes.

**Sources and boundary.** Stein–Chang–Sridharan, Demanded Abstract Interpretation (PLDI 2021),
arXiv:2104.01270, §4/§6 and conclusion p13: their dependency graph remains acyclic through
unrolling; their full framework also uses widening and fixed-point convergence. Here the
acyclic unrolling technique is specialized to explicit finite hole references with checked
ranks. No widening, convergence test, or automatic transformation of a cyclic source graph
is claimed. Cyclic fixed-point provenance is refused; Worlds retains stable-model semantics
for its separate cyclic-rule analysis.

Alternative (A) is open as cv task **01a15b72-8953-7a72-a08f-73b1dfb4fc95**:
trigger **the first deployed hole that must depend on itself through a fixed point**.
It calls for an absorptive fully-continuous carrier, specialization/truth correspondence and
a deployed consumer, following Dannert–Grädel–Naaf–Tannen, Generalized Absorptive Polynomials
and Provenance Semantics for Fixed-Point Logic (CSL 2021), arXiv:1910.07910, pp1–2.
Both papers' relevant extracted source passages were read, along with
LITERATURE-CONTEXTUAL-20261020.md §§1.14,2.15,4 item6. This source basis does not identify our
finite proof-tree semantics with general least/greatest fixed-point provenance.

**Evidence.** Scoped build of Lang.Proofs.Contextual.AcyclicExamples GREEN with the default
finite maxHeartbeats 200000, 6G/two threads. Exact two-hole output retains both alternatives,
joint positive tokens and negative blockers. A seeded self-reference refuses by name;
mutual, undemanded and zero-product-masked cycles also refuse. A wrongly ranked acyclic
chain refuses its witness, while a correct witness for that same graph succeeds.

Nine source-only scratch mutations exercise validation bypass, strict descent, reference
coverage under both expression constructors, whole-graph coverage, refusal naming, both
token polarities and sufficient depth. Every mutant definition builds, every corresponding
probe fails, and the unmutated control passes. Actual Bypass log line 2 prints
"SILENT_DROP accepted 2 seed monomials"; line 3 is the rfl failure of self_refused_by_name at
CX_P12_BypassProbe.lean:8:67. An additional mutant-only theorem proves the bypassed result
equals the seed exactly. Evidence lives under hbox logs/CX-P12-plants/, complete output
logs/CX-P12-plants.log; every output was read whole and error controls find only expected
semantic failures. No production check is weakened.

**Alternatives.** Adding acyclicity to the landed arbitrary-hole or Worlds statements would
change their meaning and is excluded by ROOT's ruling. Treating a fuel-exhausted reference
as an absent branch is the measured silent-drop mutation. Finite expansion uses a zero
internal approximation, but validation plus rank completeness prevents any accepted output
from losing a dependency that way. A cyclic fixed-point carrier remains a distinct triggered
task, not something rejected because it costs more.

**Critique.** This is a Lean-level reference adapter; no deployed package or resident path
calls it yet. Input size and ranks are finite caller data, not a new wire resource budget.
Full distributive provenance can be exponentially large, and repeated references recompute
their expansions; this is not an incremental or memoized analysis engine. Negative *token*
literals are supported; negative hole recursion, arbitrary fixed points and automatic rank
inference are outside this expression language. A raw unroll call remains an approximation:
only adapt plus its theorem is the certified boundary. Supplied ranks may reject an acyclic
graph until corrected; the refusal says so rather than diagnosing a cycle.

**Meta-critique.** The easy false success would be to show only a two-hole example and call
all cycles handled, or to assume acyclicity on a theorem about an unchecked interpreter.
The independent Derives equivalence, exact graph-equation theorem, all-node cycle boundary
and measured silent-drop mutation prevent those substitutions. Conversely, presenting this
as all of Stein's widening/fixed-point framework would overstate it; the explicit refusal
and triggered alternative (A) preserve the broader destination.

**Independent second reader (CX-READER-P12, 2026-10-20 real).** LAND: all 31 theorem
statements and their proofs read with the disjunct check. No vacuous escape branch or
changed landed premise. The boundary is adapt_acyclic/cycle_refused together with
refusal_explained and the seeded self_refused_by_name counterexample. chain_exact,
two_hole_direct and chain_candidates connect exact output to both actual leaf judges,
not merely to validation success. All nine original mutation outputs and the control
read whole; failures are semantic, not harness errors. Worlds source and proof bytes
are unchanged. The finite fixed-environment scope, no deployed caller, and distinction
from Stein's full widening/fixed-point framework remain explicit. Alternative (A)'s
absorptive-carrier task is OPEN. No source correction or weakened check was required.

## LANG-P11b Material guards, change laws, context morphisms and the modal boundary (2026-10-20 real; Codex CX-P11b)

**Decision.** A demonstration Mini can take, in eleven new LANG leaf modules.
Existing declarations, including LANG-70..73, remain byte-identical. No wire, Store,
pin, gate, budget or refusal policy changes. ROOT integrates after independent review.

Material implements a finite address-based specialization of Fouquere–Quatrini
Def 5.1 (PDF p24). Tests choose paths through a finite filling; material records the
actual terminal addresses visited, with prefixes implicit and repeated visits retained.
A successful receipt carries the EXACT test objects and the computed fragment.
withMaterial conjoins completion interactions with the ORIGINAL interface guard;
inspectCandidate pairs the existing candidate judge with that receipt. candidate_verified
and candidate_gaveUp_refused connect the record to the actual judge.

The paper corrects the digest: Def 5.5 (p26) explicitly closes incarnation under
daimon. Materiality alone therefore does NOT establish successful repair. Completion
is a separate admission requirement, retaining P1's existing gaveUp refusal. inspect
distinguishes incomplete visited material from a completed but rejected answer.
The constructor is spelled incomplete because the existing source gate rejects the
token partial even as a constructor. No gate was changed.

RepairChanges supplies Cai et al. Def 2.1's data/laws split and lawful replacement
deltas for decidable observations, with nil, update, difference and associative
composition. repair_derivative proves the Def 2.4 equation for the ACTUAL Repair
interpreter from landed from-scratch consistency. composed_derivative consumes the
landed compose_sound without modifying it. Full Repair result associativity and both
identity sides additionally preserve residuals, inspection logs and transport refusals.
Nil keeps the entire state and emits no synthetic recheck or residual.

TransportKinds distinguishes rechecked and internal claims by data constructors.
Validity is a separate indexed Prop; constructing a tag alone grants nothing.
recheck uses the landed transport's fresh destination judgment (Ringer et al. p7).
Observed quotients support internally proved map preservation and inverse laws
(Viola et al. pp1–2). internal_from_quotient combines quotient equality with a value
guard, source admission, and explicit checker/dependency/cost preservation to derive
destination admission. Those are NEW theorem premises, not additional premises on
any landed result. A genuine many-to-one flag representation has inverse quotient
maps for all representatives. Internal beta transport reaches the ordinary
propose/select consumer through Claim.destination.

ContextMorphisms represents substitution values indexed by source and destination
contexts, with a separate Valid judgment mapping declared variables to same-typed
terms. Application and composition reuse landed capture-avoiding substFn and its
typing laws; identity, weakening, heterogeneous exchange and checked strengthening
are covered. Strengthening is a partial inverse on unused variables, not a total
substitution for an unavailable variable. Token withdrawal has no constructor in
this API. This is the context-morphism scope of Cave–Pientka pp1–2.

ModalBoundary provides intrinsically scoped, simply-typed Code and typed syntax
patterns. Erasure has a HasTy derivation in the actual CMTT calculus; raw_erase
connects pattern execution to the raw extension installed at an existing Boundary.
The original candidate checker still protects that extension's domain. A real
typed beta step preserves the declared beta observation and cost while changing
the syntax guard: the exact reopened boundary obligation is logicalContract.
Extensional consumers preserve any declared behavior through congruence. These are
the two sides of Kavvos's split (p1), using a simply-typed contextual pattern
fragment inspired by Moebius (pp1–2).

**Price premises.** LANDED theorems gaining hypotheses: none. LANDED theorems
restated: none. All additions are in new modules; no existing import is edited.
The extra context, value-guard and evidence conditions appear only on new results.
No cross-layer ownership exception is required; SIZE.md is the standard SHARED
generated view.

**Validation.** Scoped build Lang.Proofs.Contextual.P11bExperiments reaches all
eleven modules under 6G/two threads and the default 200000 heartbeat cap.
Ten source mutations in lane scratch individually suppress trace capture,
completion admission, answer acceptance, preservation of the old guard,
incomplete classification, strengthening's unused-variable check, typed syntax
refusal, difference reconstruction, requested-cost forwarding and internal
destination binding. Each mutated definition builds; its concrete Lean probe
fails; restored definitions/probes succeed. Logs use the hbox
logs/CX-P11b-plant-<name>-{control,build,red,restore,restored-control}.log names.
The expected rejection strings were captured from these actual runs, not planted
by a fake tool. Source gates and the per-theorem disjunct read are in the private
lane report. No lander was launched.

**Alternatives and critique.** Equating materiality with daimon-freedom is refuted
by the cited paper itself. Replacing the existing guard would silently weaken
admission, so the new guard is conjunctive and has a specific mutation tooth.
The material model is finite and uses explicit interaction paths; it is not full
ludics, an interpreter-instrumentation system, or a biorthogonal closure algorithm.
The Cai structure is on observed repair results, NOT a claim that arbitrary
function-valued Worlds admit a finite edit difference. Replacement deltas are
lawful but do not promise compact changes or automatic differentiation. Residual
histories remain explicit; their full associativity is proved separately.
Quotient evidence only transports the DECLARED observable, and cannot remove the
other guard/checker/support/cost conditions. This is not a mechanization of
PUMPKIN Pi's whole algorithm or of the Cubical Agda correctness development.
The context-morphism API does not implement dependent CTTs substitution-variable
normal forms. Typed Code is the variable/lambda/application fragment, not the full
polymorphic/multilevel Moebius language. betaObservation is one explicit contraction,
not normalization or a global observational-equivalence decision procedure.
Private data examples are demonstrations; none claim new CalculusLaws instances.

**Meta-critique.** The main temptation was to rename old records after papers and
call the result their metatheory. Concrete guard, candidate, Repair and boundary
consumers, complete-result composition laws, quotient inverse maps, and the mutation
probes supply narrower, executable claims instead. The remaining risk is reading
these finite fragments as the full cited calculi; their limits are explicit above.

**Independent second reader (Codex CX-READER-P11b, 2026-10-20 real): LAND.**
Read all 54 theorem statements and their definitions, applying the disjunct check;
no escape disjunct, no changed landed signature and no additional landed premise.
Directly checked Fouquere–Quatrini pp24–26, Cai pp2–4, Kavvos pp1–2,
Moebius pp1–2, Cave–Pientka pp1–2, Ringer p7 and Viola pp1–2.
The correction above is essential: incarnation is daimon-closed; completion is
our separate admission requirement. The change structure is on repair observations;
the recomputation-style derivative does not claim efficient automatic differentiation.
The typed syntax fragment and quotient transfer do not claim the full cited calculi.
All ten actual mutation failures and their restored controls were read whole, and
all saved mutants inspected. Independent scoped build and separate elaboration of
all eleven added source files passed at 6G/two threads, maxHeartbeats 200000.
No theorem correction was required; the critique and meta-critique above stand.

## LANG-P9 All-environment provenance, computed minimal repairs and recorded nogoods (2026-10-20 real; CX-P9; contextual program CARD P9)
**Purpose and evidence.** A demonstration Mini can take. The first built theorem,
provenance_env_specialized, exhibits the actual LANG-66 boundary: setEnv true verifies
a CMTT candidate absent from the old environment-specialized polynomial. It precedes
the new implementation. Sources read in the original PDFs: Grädel–Tannen (2024),
Def4 p9, update pitfall p19, Prop15 p20, Prop16 p23 (also the examples p22);
de Kleer (1986), pp144–145 (PDF18–19); Green–Karvounarakis–Tannen (2007), pp3–4.
The latter supports the positive-fragment provenance analogy only; negative literals
use Grädel–Tannen. Candidate is a Doyle IN/OUT justification, not an ATMS label.
The existing reissue_never_reenables deliberately rejects recovery of an old version:
AGM recovery is not a law of immutable versioned tokens.

**Decision.** Three new data modules and five proof modules, no existing Lean edits.
P9.provenance keeps guard(filling) and budget(cost) as explicit envLits. It has no
environment argument, and prefilters only the immutable typing problem.
P9.provenance_iff relates this one polynomial to the original judge at EVERY world.
specialize_eq recovers the landed polynomial with its exact order and multiplicity;
provenance_update states that equation after actual Edit.apply.
The third monomial component is the card's permitted route for opaque E: an environment
key model would require a new declared-key interface which this layer does not invent.
Budget is fixed by Iface but retained as a literal rather than erasing its candidate.

Complementary products never verify. label first removes them and then absorbs larger
literal sets, including both polarities and envLits. minimal_subset/minimal_covers
prove that retained products are original and cover every original product;
minimal_eval/label_iff preserve the original semantic bridge. provenance_minimal
proves the antichain property modulo equality of literal sets. This is the Boolean
image, not an arithmetic semiring implementation or a minimal Boolean-formula solver.
It does not decide semantic implication between arbitrary guard programs.

**Reverse provenance.** repairTerms specializes the uneditable environment and budget,
then removes complementary products. Every remaining monomial computes changes:
currently missing positive tokens plus currently live blockers. tokenEdits maps
them to actual assert/withdraw edits; applyAll semantics are proved even with repeated
input tokens. repairs_of_provenance verifies an original retained candidate.
The converse provenance_of_repair finds a subrepair in every successful token update.
repairPlans applies the SAME absorption algorithm to edit sets; repairPlans_minimal
is global inclusion-minimality among all token updates, not just minimality in the
candidate list. repairPlans_complete covers every minimal repair up to set equality.
residualRepairPlans consumes P4's actual saved Residual world, closure and candidates;
its theorem gives global minimality for every returned plan. Unknown hole and no plan
are different results. Plans are proposed values; this does not authorize token edits
or execute committed effects.

**Recorded consistency.** RecordedClosure extends the landed Closure with nogoods.
judgeRecorded checks for a recorded subset of EFFECTIVE supports before consulting
the original judge. It returns the old guard-conflict status plus the exact recorded
core; missing supports never downgrade this conflict to suspension.
recordedLabel_iff and recordedRepairs_sound connect labels and repairs to this same
policy. classifyRecorded constructs P5.refuted only with a found recorded core;
recorded_refuted shows membership, subset evidence, and non-verification at EVERY
world. This refutes that candidate relative to the recorded database, not the whole
hole or arbitrary propositions assigned to tokens. selectRecorded consumes the policy
and then delegates authority/accepted-history/current judgment to the landed select.
The database remains attached to successful results.

**Price premises.** LANDED theorems gaining hypotheses: none. LANDED statements
restated or renamed: none. The original provenance_iff and all original Closure/Judge/
Repair declarations remain byte-identical. P9.provenance_iff is a new namespaced theorem.
New repair statements explicitly operate on the token-repairable specialization,
because no token edit can repair an opaque false guard or over-budget candidate:
that is Prop16's fixed uneditable facts, not an omitted proof of arbitrary env synthesis.
No wire/Store/pin/gate changes; no existing refusal becomes acceptance.

**Alternatives and limits.** Editing the landed Closure/Status constructors would
violate this wave's append-only discipline and require restating all exhaustive
consumers. The namespaced record extension follows P4's accepted additive pattern.
Erasing it toClosure deliberately loses the nogood policy; ordinary select/repair
are not silently upgraded. Callers needing it use the recorded operations.
Nogoods are recorded premises of the ATMS policy, not checked Lean derivations of
logical False. Empty nogoods are allowed and refute every support. The full EnvLit
theory is generic in E but environment synthesis is not implemented. Flat finite
candidate lists and quadratic absorption are a reference computation; no cyclic-hole
or polynomial-time enumeration claim is made. No full semiring carrier was added.

**Verification.** Scoped Lang.Proofs.Contextual.ProvenanceExperiments builds GREEN
under SWARM_MEM_MAX=6G, LEAN_NUM_THREADS=2, Lean default maxHeartbeats 200000.
Thirteen concrete experiments use the actual CMTT checker. Seventeen temporary
mutants each BUILT their definitions, then failed a def-only Lean probe; control
and restored probe passed. Full outputs were read, including the successful mutant
builds, not only a summary grep. Logs are hbox logs/CX-P9-plant-<name>.log and
CX-P9-plant-<name>-build.log; driver CX-P9-plants.py, source probe CX-P9-probe.lean.
Actual kernel failures say the decide tactic proved the proposition false for
16 mutations; the refutation mutation fails the expected constructor equality
with "error: Application type mismatch". The named probes cover guard, budget,
typing, complements, absorption and its three literal sets, edit polarity, missing
edits, repair environment/consistency, nogood bypass/partial matching, hypothesis
supports, P5 refutation and selection. Source gates and all 52 theorem disjunct
reads are recorded in CX-P9's private report. ROOT's independent reader and landing
remain separate: this lane only prepares READY.

**Critique.** Literal-set minimality does not remove semantically equivalent arbitrary
guard programs; doing so would require their own equivalence evidence. Guards and
budgets are immutable inputs of a token-only repair problem. Treating a database
entry as a mathematical contradiction would overstate recorded_refuted; its scope
is explicitly policy-relative and candidate-specific. The extension has concrete
selection and residual consumers, but is not a new deployed protocol or automatic
replacement of every old closure operation.

**Meta-critique.** The tempting shortcuts were to prove another fixed-env bridge,
to call a necessary edit list a repair without running applyAll, or to call a search
failure refutation. The first tooth, all-env theorem, two-way global minimality,
actual residual consumer, and nogood selection/refutation plants reject these
shortcuts. Another temptation is to treat the successful symbolic demonstration as
permission to edit old shared constructors; retaining the additive boundary keeps
that migration a separate, explicit integration decision.

**Independent second reader (CX-READER-P9, 2026-10-20 real).** LAND. All 52 new
statements and proofs read with the disjunct check; no escape disjunct, no landed
signature changed. The original fixed-env polynomial and bridge remain byte-identical.
The first tooth uses the original polynomial and an actual setEnv edit. The new
polynomial retains guard/budget literals and works at every world. Absorption preserves
both directions through minimal_eval/label_iff. Minimal repairs quantify over every
successful token-update set; the converse returns equality of token sets, not merely
an already chosen witness. Recorded nogoods produce conflict before missing-support
suspension; classifyRecorded constructs P5.refuted from the recorded core, and
recorded_refuted proves candidate-specific exclusion at every world under that policy.
All 17 full mutation outputs, successful mutant builds, and control/restored outputs
were read; failures are semantic Lean diagnostics, not driver failures. Restored source
matches all saved mutation originals. No theorem correction required. The finite-list,
fixed-environment token-repair and recorded-policy limits above remain explicit.

## LANG-P11a Stable labellings, interface substitution and evidence-bearing game statuses (2026-10-20 real; CX-P11a)

**Purpose.** A demonstration Mini can take. The sources name the landed rule semantics
and strengthen its connections to independent judgments. No wire, Store, key, pin or
admission-format change. ROOT owns landing; this lane supplies a green candidate only.

**Decision.** WorldsField states model closure and relative unfoundedness separately
from Derives and proves Lifschitz Definitions C/D equivalent. A completed analyze result
is exactly the canonical stable IN/OUT labellings; the unfounded cycle and non-union
examples consume this correspondence. Existing cycle_loses_grounding,
counting_keeps_cycle and their Worlds variants retain their exact names, statements
and proofs. Literature notes are appended to their files. Elkan (1990), p219 abstract,
identifies the JTMS/stable-set connection and the general NP-completeness result.
That complexity result is not a termination theorem for any individual run.

Interfaces spells out de Alfaro–Henzinger Definition 14's input/output inclusions
AND implementation-successor matching and proves equivalence to the landed relation.
Deterministic input transitions justify the reversed input matching formulation.
Substitutivity proves peer compatibility and a successor-closed simulation of
synchronized products. This is the fixed-alphabet, closed binary-product, no-hidden-action
specialization of Theorem 4. The no-new-peer-input side condition is automatic here;
we do not claim the full open-interface theorem. A repeated seven-price peer is an
inhabited consumer. A two-input counterexample excludes mere current label inclusion.

Games checks a finite closed region without sinks, with root membership. The independent
Solved inductive judgment formalizes backward induction (win by a move to a loss;
lose when every move reaches a win). A checked trap rules out both derivations, giving
a semantic draw. The certificate is sufficient, not complete: a true draw may also have
bad exits. An operational budget/fragment limit is NOT evidence for draw. The original
P5 constructors and reasons are unchanged. Köhler et al. explicitly say FO provenance
games are draw-free; the loop arena is a separate cyclic game.

NogoodGames combines finite-domain completion with recorded explanations. Each excluded
candidate must be covered, cite a member of the actual nogood database, contain that
nogood in its effective assumptions, and fail the current acceptance test on replay.
The returned refutation proves loss in an independently defined finite completion game.
A witness proves win. The P9 bridge consumes actual classifyRecorded/recorded_refuted
and constructs a checked singleton completion refutation from the recorded token set.
The singleton theorem concerns that candidate, not every possible filling of a hole;
the generic checker covers an explicitly supplied finite domain.

**Price premises.** LANDED theorems gaining a hypothesis: none. Restated existing names
are cycle_loses_grounding, counting_keeps_cycle, cycle_loses_grounding_over_worlds and
counting_keeps_cycle_over_worlds, through appended literature annotations only; no Lean
signature changes. Every new theorem is in a new proof module. Owned change: eight
new modules (three data, five proof), 731 new Lean lines plus 24 appended comment lines,
115 deployed lines, 34 new theorems. P9's six source dependency snapshots are not this
lane's contribution or landing paths; the bridge requires P9 integration first.

**Cyclic-hole policy / separate card.** After this worker stopped, ROOT selected (B):
an additive certified acyclic adapter with explicit ranks/unrolling and a named refusal
plus boundary theorem for dependencies it cannot represent. CX-P12 owns that separate
implementation; none of it is in this bundle. Worlds retains stable semantics for cyclic
rule analysis. The alternative (A), a fully continuous absorptive carrier (Dannert et al.),
requires carrier/evaluation/fixed-point proofs and is deferred to the first deployed hole
requiring self-dependence through a fixed point. Neither additive design gains a landed
hypothesis; retrofitting acyclicity into existing arbitrary-hole interfaces is not performed.
The current one-level closure still has token supports, not cyclic selection dependencies.

**Source accuracy.** GMS93, printed pp158,164–166, counts derivations, proposes counting
for nonrecursive views and DRed for recursion, and allows some recursive counting while
warning of nontermination. Our immediate-support countRun is NOT their algorithm, so
its counterexample does not refute GMS. Our repair is well-founded re-derivation, not a
claimed DRed implementation. Primary sources read: Lifschitz PDF pp7–8; de Alfaro–Henzinger
PDF pp5–6 and p10 (printed118); Köhler et al. PDF pp2–4; de Kleer PDF p19 (printed145);
Dannert PDF pp1–2; Stein PDF p13; GMS93 original PDF sections1/7/8; Elkan publisher abstract
only (full text unavailable locally). No quotations from private exchanges are included.

**Validation.** Scoped builds with 6G/two threads/default maxHeartbeats 200000 are green.
Seven real mutation teeth compile their mutated definitions, then fail the corresponding
kernel decide theorem: draw root coverage, nonsinkness and successor closure; refutation
domain coverage, record membership, assumption inclusion and current-verdict replay.
Unmutated controls pass. Full outputs, not summary-only greps, were read. Each real log
reports that tactic decide proved the probe proposition false. The first draw harness
used an incorrect package root and is excluded from the evidence. Source gates and the
per-theorem disjunct read are in the lane report. No independent second-reader claim is made.

**Critique.** The world theorem is finite propositional JTMS semantics with frozen external
tokens, not a complete implementation of Elkan's TMS or an NP-completeness formalization.
Interfaces do not model hidden actions or partial-overlap alphabets. The trap checker
does not solve arbitrary games. Nogoods are a recorded consistency policy; they are not
new axioms asserting token propositions imply False. Replaying acceptance prevents
untrusted or stale explanations from refuting a currently accepted candidate. The P9
bridge has been built against explicit source snapshots; ROOT must integrate its owner
before landing this consumer. The separately ruled cyclic-hole adapter remains outside this bundle.

**Meta-critique.** Renaming a checker result as a field term can hide a tautology. The
independent model/unfounded predicates, reversed successor matching, game derivations
and mutated executable checks make the connection refutable. Conversely, forcing the
literature to endorse a budget timeout as draw, or blaming GMS for our naive counter,
would make the vocabulary less accurate. The remaining limitation is scope: these are
small, explicit specializations, not claims to have mechanized every result in the papers.

**Independent second reader (CX-READER-P11a, 2026-10-20 real).** LAND-WITH-FIXES:
the only correction is the policy paragraph above and matching message, which now reflect
ROOT's subsequent B ruling without claiming CX-P12's adapter. All 34 new statements were
read with the disjunct check; no vacuous escape or altered landed premise was found.
The two old proof files are byte-prefix extensions of main, preserving every declaration.
A warm dependency build and fresh elaboration of all ten owned Lean source files passed
under 6G/two threads and maxHeartbeats 200000. Both mutation controls and all seven real
mutant-definition/probe logs were read whole; only the expected kernel false-proposition
errors occur. Closure C3 is respected: executable definitions in data modules and Prop
judgments/theorems in proof modules. The fixed-alphabet, no-hidden-action and universal
refusal-safety scope of interface substitution is explicit; it is not the full open-interface
theorem. The canonical-world restriction and finite sufficient draw certificate are explicit.

**Integration receipt (CX-READER-P11a).** P9 landed as c58757f6ad04c5cef4877350962cb6a748d4fdc4;
its six dependency modules are consumed from main and excluded from P11a landing paths.
The earlier worker-snapshot integration blocker is resolved.

## LANG-P6 · Certificates retain their logic and checked Environment context (2026-10-20 real; CX-P6)

**Decision.** This is development tooling, a demonstration Mini can take, not nano admission.
A certificate retains target, statement, declaration context, admitted assumptions and checker
identity. The generic reader compares every payload with the destination lookup and closes the
context under statement/type/value/shape dependencies. Extraction is bounded and runs the
same acceptance check before returning. Same-statement certificates with different contexts
remain different objects; checker identity is intrinsic as well.

The concrete adapter lives beside the existing census tooling: Census/CertificateData.lean
projects Lean's checked kernel Environment; Census/Certificate.lean provides the command;
Census/Proofs/Certificate.lean contains its two proof statements. ROOT authorized these GATES
paths on real 10-20. C2/C5 and every existing gate remain unchanged. Full expression DAGs retain
universes, binder annotations, metadata and projection names; declaration payloads retain each
ConstantInfo variant's fields, including recursor rules and inductive shapes. Structural cache
equality, not a digest comparison, identifies shared expression nodes. The context includes
opaque proof values as well as definitions: it is a conservative read closure, not a trace of
which reductions the kernel happened to perform.

**Proved contract and exact trust boundary.** The generic eight theorem declarations establish
acceptance/factory fidelity, finite transitive reachability coverage (cycles allowed), missing
dependency and changed projected-body refusal, and context/checker identity distinctions.
Census.Certificate.read_environment proves that every returned entry comes from an actual
env.checked.get.find? result, with exactly the declaration projection stored in that entry.
Census.Certificate.accepted_environment_reachable gives the same result along every finite
reader dependency path. These are environment-relative extraction theorems, not proofs of the
target theorem, foreign-logic interpretation, or a verified Lean kernel.

The named trusted read-offs are Lean.Environment.checked/get/find? and imported oleans;
Census.Certificate.encodeExpr/expression/declaration (field coverage, reference extraction
and encoding injectivity are not proved); Lean.Expr.equal/ExprStructEq and core Repr/JSON;
Lean.collectAxioms including its imported-module cache; compiler/command execution; and file IO,
Python JSON and lossless gzip. No theorem identifies raw ConstantInfo values from equal encodings.
The successful factory/acceptance claims quantify over the concrete projection above; they
must not be promoted to completeness of this trusted extraction or proof authentication.

**Real vector and verdict.** gates/certificate.py imports Ledger.Proofs.GrantCap and emits
Nanodregg.Ledger.Proofs.grant_moves_le_cap, including its full telescope. The checker name,
Lean version/compiler githash and actual direct imports are retained. The exact target
collectAxioms inventory is distinct from the possibly larger conservative context inventory;
every reported target axiom must occur in the accepted context. gates/certificate-grant.json.gz
is the complete emitted JSON object compressed losslessly, not a list of hashes or a synthetic
sample. The script row in gates/runs.tsv regenerates the object and compares all fields and
all declaration payloads. It refuses changed axioms, constants, definitions, statement or
checker; normal checking never refreshes the vector. --emit-vector is explicit authoring.

**Price premises.** Landed theorems gaining hypotheses: none. Landed theorem statements
restated: none. The new certificate component has no deployed caller. The size classifier
still counts its 119 Lang definition lines as deployed; this is reported, not hidden.
The Host import closure and maximum dependents are unchanged. Exact final counts and source
gate results accompany the message and lane report.

**Teeth.** The generic 15-case executable covers cycles, equal statements with distinct
accepted contexts, each acceptance refusal, non-theorem/missing-dependency reads and fuel.
Eight run-1 disabled-check plants returned actual Except.ok () for invalid objects, producing
real FAIL lines; run 2 read all eight complete outputs. The Environment plant helper creates
a twin of the actual GrantCap telescope, once using the landed proof and once using a new
scratch axiom; collectAxioms must observe the extra axiom and the real vector comparator must
refuse. A second scratch theorem keeps its statement/axioms but changes the definition it
unfolds. Disabling the comparator in lane scratch exposes false acceptance of the actual
extra-axiom output. Whole output and exact log locators are recorded in the lane report.
The normal vector and harness-control are exercised separately.
The separate collectAxioms coverage guard also has a tooth: an actual scratch compilation of
the adapter with poisoned axiom classification is refused by that guard; a scratch copy with
the guard disabled emits the inconsistent inventory and a separate executable assertion fails.
No production source is mutated by these Environment plants.

**Final validation.** Scoped builds GREEN; scoped axiom census over both proof modules GREEN
(40 declarations, zero allowance rows); all 15 generic cases GREEN; fresh full-vector
regeneration GREEN; known-red controls and all three Environment mutation families behaved
as required. Source gates, including ownership and C2/C3/C5, GREEN. The full vector contains
6857 declarations and the target's three axioms (propext, Classical.choice, Quot.sound);
101964263 JSON bytes compress to 11961094 bytes. The exact whole-output logs and per-theorem
disjunct readings are in the private lane report; ROOT's independent reader owns landing.

**Critique.** This is an auditable extraction boundary, not a proof of serialization or a new
checker. Source/encoding changes may conservatively invalidate the vector even when logical
meaning is unchanged; they require review. Huge proof terms must retain sharing: the tree-shaped Repr attempts first hit the work
bound, then exited 143 without a result (the cause of that signal was not established). The
DAG representation completes under the same 6G cap without discarding proof declarations or
weakening the closure check. The reader's
finite fuel can still refuse very large theories by name; there is no claim of total extraction
for every Environment. Toolchain identity does not authenticate producer-supplied strings.

**Meta-critique.** Generic laws alone could have looked like a completed bridge. This change
connects them to an executing Environment adapter, a real landed theorem and a pinned full
object, while naming exactly which projection facts remain trusted. A serialization theorem
would strengthen this boundary; its absence is a limit, not an unstated axiom of these proofs.

**Independent second reader (CX-READER-P6, real 2026-10-20): LAND.** Read all ten
theorem statements and proof bodies with the disjunct check; none has an escape disjunct.
No landed signature changes. Projection fidelity and the named trusted read-offs above
match the actual proofs. Scoped build and source gates passed; one fresh extraction
reproduced all 11961094 gzip bytes exactly. Read every generic and Environment plant
output, including the coverage-guard refusal and the disabled-guard assertion failure.

**Authorized landing repair (CX-READER-P6, real 2026-10-20).** ROOT for CLIENT
authorized four expect-to-unwrap substitutions in devtools/tests/workspace.rs,
pre-existing since bb77db4. The file already allows unwrap for test setup.
Every absent value, failed IO and failed thread still panics; no test changed its
assertion. No lint allowance, gate or refusal changes. Landed theorem hypotheses:
none; restated statements: none.
**Critique.** Panic diagnostics lose the four custom labels; the same failing
operations and assertions remain. Scoped clippy and the affected scratch test
validate the repair; the full judge still decides this landing.
**Meta-critique.** A pre-existing clippy failure is not evidence against P6, but
also not a reason to bypass the judge. ROOT's explicit ownership grant permits
this behavior-preserving repair in the same landing.

## LANG-P8 Atomic one-use integration over the real receive path (2026-10-20 real; CX-P8)

**Purpose and decision.** A demonstration Mini can take. Extend the hole journey with
a fresh session: A owns the open requester; B owns the value source and grants the
requester Right.transfer 1. Two provider authorities and candidate rows are retained.
The additional commit method copies the existing selection checks and, in the SAME
kernel turn, records the selected provider, marks acceptance, and transfers one unit.
Nano is the single-transaction case of the LPCFS comparison: one Store writer, several
cells in one atomic turn, no distributed agreement or external exactly-once claim.
The application deadline and signed-call window are checked separately. Cancellation
uses Receive.cancel (the cancel operation used by PROTOCOL-63), not a new cancel flag.

P10 observes each provider's actual live kernel grant and its recorded version pin.
An unrelated birth preserves the trace and the previously signed plan still submits.
P9's polynomial retains both candidates and evaluates against every live World; after
one grant is revoked it reads [false,true], and the old instantiation refuses stale.
The changed fact-row correspondence separately refuses support0 moved. P4/P11b
recheck an old/new provider-index representation through a checked involution; the
returned image's provider index is used to construct the actual commit call. Unknown
certificate ids refuse unknownCertificate. This is rechecked evidence, never internal
evidence. The schema checker is explicitly data-only, not a new Lang typechecker.

**Six objectives and scope.** Integration.lean applies LANG-67's substitution judgment;
specializes P10 observation completeness and P9's all-environment bridge to the actual
journey World adapter; proves the correspondence/registry, destination validity,
returned-image provider preservation and equality of the actual invocation arguments; derives the event/id/journal receipt from
submit_ok, receiveWith_sealed, sealTurn_ok and admit_journaled; specializes
LEDGER-18/19 grant_moves_le_cap to one unit; and composes HOST-64's actual openWith
path with a spent-base invariant and audited-tail assumption. ReadyWriter explicitly
requires fresh journal/refusal state, successful checked re-execution, and admissibility
of that turn. Its progress theorem proves one submit, not network fairness or eventual
service. The abstract protocol-to-package lowering is exercised by rows, not proved
as a compiler refinement. The journey retains its documented toy crypto parameters.

Recovery names what is assumed: the decoded base has CheckpointTrusted at the pinned
origin, canonical cells, contiguous ledgers, and zero left in this grant; the trusted
writer's replayed tail has an audited history. A received/pruned checkpoint does not
acquire this from its MAC alone. The theorem binds its base to Base.read and its tail
to the actual open result, and shows zero further consumption in that audited history and EVERY future audited
continuation after reopening (the two histories compose by audit_append_to).
The executable row folds the committed suffix and reads the real spent ledger and
journal again. It is not an IO fault-injection test or a proof of filesystem durability.

After commitment, P8.4 freshly re-executes through submit: exact replay refuses replayed,
a freshly signed commit refuses accepted, and a competing transfer at the real counted
receiver refuses transferSpent. No saved effectful continuation is filled and resumed.

**Price premises.** Landed theorems gaining hypotheses: none. Landed theorem statements
restated or renamed: none. All old journey checks remain. Only Lang/Journey.lean,
Lang/Proofs/Contextual/Integration.lean and this append are authored. No wire, Store,
key, pin format, gate or foreign layer file changes. ROOT owns review and landing.

**Validation.** Scoped builds and lang-journey under SWARM_MEM_MAX=6G,
LEAN_NUM_THREADS=2, maxHeartbeats 200000. Real package mutations remove the deadline,
support equality and accepted-prefix checks: respectively the invalid commit admits,
the moved correspondence admits, and the named refusal falls through to transferSpent.
Controls pass. Additional adapter/cap mutations exercise live provenance, the support
pin in the real signed call, certificate lookup and counted amount. Exact real output
locations and source-gate results are retained in the private lane report.

**Critique.** This is a concrete composition experiment, not a general proof that every
surface package implements an abstract protocol. Provider authority is read by the
journey adapter and included in its generated signed pin set; the package's fact rows
alone do not inspect arbitrary kernel cells. The correspondence changes a provider
index's representation, not the installed package ABI. Recovery still trusts the
writer/checkpoint premises and the stated audit correspondence. The bound covers unit
transfers through the counted grant, not unrestricted actions of the well's owner.

**Meta-critique.** The easy but wrong shortcut was to equate an accepted flag with durable
consumption, or to reuse the pure fill-and-resume story across a transfer. The counted
ledger and the atomic nested transfer provide independent evidence. Another shortcut
would have returned an arbitrary base or empty witness history in recovery: its final
statement binds Base.read, the actual replay output, the audited log and the chain's
step projection. Conversely, a generic ready-writer lemma is only one-step progress;
the executable positive session supplies its concrete client, not a claim of liveness.

**Independent second reader (Codex CX-READER-P8, 2026-10-20 real): LAND.**
All fifteen statements and their proofs read with the disjunct check. The six
objectives consume the concrete Journey adapters or landed protocol, receive,
ledger and checkpoint theorems. No landed hypothesis or foreign source changes.
The amount disjunction is a universally constrained measurement premise, not an
escape conclusion; the chain projects to the supplied history. Recovery bounds
every future audited continuation from the actual reopened World, assuming a
spent trusted decoded base and an audited path to that World. That premise does
not certify IO crash safety or identify each disk record with an audited step.
ReadyWriter is explicitly one-step progress under receiver/kernel readiness,
not eventual service. Nano is the single-Store atomic transaction case.
All nine complete semantic mutation outputs and successful source-mutant builds
were read, together with their drivers and passing control. The initial unused-
variable environment mutation failed compilation and remains excluded. The three
package-string mutants installed actual checked packages before their rows failed.
A scoped build and fresh elaboration of both changed Lean modules passed at
6G/two threads with maxHeartbeats 200000. No source correction was required.


## LANG-ACT Generated activities and guarded holes; Bell as an activity (2026-10-20 real; CX-ACT; cv 01a158c0-ddbf)
**Decision.** Std.eqData generates structural equality for data types, with actual BigStep meaning and
an equality iff under canonical, conforming data. Std.activity generates ordinary continuation rows:
a time/signer cursor and a retained captured-plan log. Insert is signer-owned and unanswered; upsert
requires the resumer, the same capture and plan, and the first answer; retirement requires an answer.
The author's resume function receives both the retained capture and the explicit response.
Surface activity declarations compose their edit types with application relations. Applications can
choose exposed generated methods, call generated closed code from bounded public wrappers, and retain
their diagnostic vocabulary without replacing predicates.

**Hole.** Std.hole generates candidates, posted facts, selection, acceptance and the activity used to
dispatch an accepted filling. Candidates retain two optional versioned supports, one optional blocker
support, their status and pruning-reason text. A probe matches cell identity and then version; it searches
all three pinned fact points, not their arrival order. Select/fill/accept recompute clause, blocker and
support observations. Rejudge RECORDS the resulting status, including negative statuses. This is ROOT's
rejudge ruling (A): the reason an alternative was set aside remains available. A pruning reason is a
posted fact token plus text; withdrawing the token releases pruning, while the text stays. Selection is
revisable; acceptance dispatches the immutable captured value. Generic start_fill is not exposed.

**Bound and bundle.** The first in-package construction measured 392,235 bytes and refused overPrice.
Sharing and small-result refusal sequencing reduced it to 120,523, still refused overBound. The measured
breakdown was 29,062 bytes of interface/relations, 18,407 for resume_fill and 12,266 for accept.
ROOT chose ordinary imports (A). The generator partitions pure fields into independently checked ROMs
and returns a root layout whose link operation checks the supplied imports and slot bound. The measured
journey bundle has helper ROMs of 57,662 / 64,276 / 9,218 bytes and a 29,521-byte root. All pass the existing
install path, each below the unchanged 65,536-byte bound. No pin, gate, wire constructor or bound moves.

**Bridge and scope.** HoleModel uses the existing langData, not a new Data-only calculus. Its ref-0 template
is proved Typed by LangHasTy. Operational proofs cover actual clause/probe composition through holeJudge,
the shared admission gate and the negative-status renderer. Under fixed observations matching the
world, the judgment segment used by select/fill admits iff the existing Closure.judge verifies;
separate lemmas establish Closure select/fill equivalence
and exact rejudge status for a present candidate. The proof states its representation boundary: observed
clause evaluation and complete pinned support observations must represent the model's environment and
token liveness. Independent chooser, existence, accepted and window checks precede candidate judgment.
The arbitrary-point lookup theorem proves actual identity/version/absence behavior; executable teeth
also exercise the three-point search and row-order independence. This is not a whole-Kernel.Receive
simulation theorem or a claim that missing pins describe a complete world.
LANG-68's langTemplate_no_hyps remains the boundary: strengthening, alternative-by-hypothesis and
hypothesis-derived supports are EMPTY ON EVERY LANG TEMPLATE. No work on fork (B) is included.

**Bell flag day.** Bell is an activity instance. Its bounded answer/close/open/retire/ring wrappers and
method indices remain; ring invokes generated start_ask. Generated queued/rung guards preserve the
established notResident/unrung/text/answered/unanswered/final/notYours refusals, including through layers.
Rows now hold captured ask values and tagged answered responses; the resident decoder follows them.
The declared key remains time first, then signer (the field is agent); tied rings keep digest order.
Bell, layers built over it, hole ROMs/root and hole candidate/argument types re-id. Install new packages
and create new objects, or re-genesis, while cutting the resident over with Bell. No existing Store bytes
are migrated, and no Store representation changes.

**Price premises.** NONE. No LANDED theorem gains a hypothesis; none is restated. All new typing,
canonicality and observation premises belong to new statements. Existing resident proof statements are
unchanged. The extra cost is generated code/ROMs and focused meaning/model/proof modules, measured in SIZE.

**Evidence.** Scoped proofs and lang-journey are green on main 06da84f. The real generated hole is installed
with its helper closure and exercises fill success/conflict/suspension, moved and withdrawn supports,
live-blocker refusal, withdrawal of that blocker with its reason retained, acceptance and negative rejudge.
All Bell LB rows, their takeover plants and the shipped-core equality row pass. Filtered resident_bell is
green (1/1): queue ordering, exactly-once, restart intent, refusal and crash-loop recovery.
Plants independently bypass each activity method check (five native verdicts change to ok); bypassing the
hole conflict gate admits LH5g/LH5h, pruning admits LH8q, and moved-support admission admits LH7/LH7f while
LH7b reaches kernel stale. Six lookup/birth mutations make the expected kernel-decided statement FALSE.
Twenty-eight additional emitted-code rows cover authority, window, existence, candidate immutability
and fixed shape. Sixteen independently disabled refusal names make their exact rows RED; every
mutated package still passes the checker. The accepted hole also completes its activity path:
captured value survives withdrawal, acknowledgment succeeds, replay refuses, and retirement succeeds.
EqData's 16 statements have CX-READER-ACT's LAND. Every later statement still requires ROOT's second reader;
this source is prepared for that read, not a claim of independent approval.

**Critique.** The hole currently represents two positive supports and one blocker, not an unbounded
provenance polynomial. Its methods implement the declared operations; this is not a claim that arbitrary
layer overrides preserve hole selection semantics. Fact completeness is an explicit interpretation
condition, not derivable from a missing read. Import bundling repeats some type/closure syntax between
ROMs; a later measured sharing pass can improve it without changing the bound. Bell's answer wrapper
supplies the expected capture so the existing rung:text refusal stays a guard property, while the generic
resume method normally reads its capture itself. Both paths share the continuation guard.

**Meta-critique.** Counting a typechecked generator or a fixture as the closure bridge would hide the
important join. Here the calculus is the landed Lang instance, the judgment segment is actual emitted
code, and the observation assumptions are stated rather than erased. Conversely, pretending that
rejudge refuses would destroy the very retained negative reasons the design needs. The slot-bound
refusal exposed representation pressure; ordinary checked imports address it without turning the bound
into a moving target. Independent review must assess the operational boundary as well as the iff syntax.

**Pre-repair review (CX-READER-ACT2, 2026-10-20 real; superseded by LANG-P13 below).** LAND-WITH-FIXES under ROOT's
explicit disposition. Read all 71 new non-eqData statements with the disjunct check; eqData's 16
retain CX-READER-ACT's approval. Existing landed statements gain no hypotheses and are not restated.
All 24 changed/reached modules re-elaborated at 6G/two threads; all 11 source gates pass.
The original bridge's deployed correspondence claim is refused: a real journey retaining every
control but omitting the live blocker fact pin ADMITS select and accept and records verified on
rejudge, where the complete-pin control refuses pruned. No production check was disabled.
The theorem is renamed hole_judgment_admission_fixed_observations with an explicit omitted live
blocker pin docstring; its already-conditional mathematical statement and proof are unchanged.
This bundle does NOT repair complete observation coverage. ROOT directed landing this scoped
result and tracking integration of CX-P10's proved declared-read-set adapter into the emitted
receive path: cv 01a15b7a-6dd9-7510-b0b4-45089e4ca484.

**Review critique.** The negative dependency requires coverage: an unobserved blocker is not an
observed-absent blocker. Existing positive-support and pruning bypass plants supplied all pins,
so they did not exercise this gap. Selection, acceptance and rejudge remain affected until the
tracked receive-path integration; no arbitrary-request soundness is claimed here.

**Review meta-critique.** A conditional semantic equivalence cannot certify that real requests
satisfy its observation premises. Naming that boundary is an honest restatement, not the repair.
The follow-up must establish coverage by construction and connect authenticated observations to
the actual world, with missing-blocker mutation teeth on the emitted path.

**Flag-day benchmark consumer (CX-READER-ACT2, ROOT granted PERF, 2026-10-20 real).**
The first full judge exposed Bench/WorstCutRows using ringer for the activity's row
pins, refusing rowUnpinned before its known-red control. Its public retire argument
still uses ringer; only its three pin sites now use agent/notBefore through a separate
activityRowKey constructor. Measurements, check predicates and harness-control are
unchanged. The real control reaches its intended harness-control refusal; the normal
bench passes. At 16448 steps, reopen/audit hashes are 331897 rather than 331960
(63 fewer), ratios 20.179 rather than 20.182; verification ratios remain 0.000/1.000.
The recut Bell's base world is 29253 bytes; the tail fills 18837876 of 18876520 bytes
(0.998). ROOT authorized the downward measured-value re-pin in gates/waste.tsv;
every ceiling stays unchanged. No theorem gains a hypothesis or is restated.

**Benchmark critique.** The Bell re-id changes the workload and its key distribution,
so an unchanged counting method need not produce an identical ratio. This measures
the actual recut workload; it does not attribute the small hash decrease to a new
algorithm. Preserving the old ringer public method argument separately from the new
row key prevents a pin adaptation from silently changing invocation bytes.


## LANG-P13 Complete observations in the generated hole (2026-10-20 real; Codex CX-P13)

**Decision.** Land the ACTIVITIES bundle and its observation repair together as
one lang! flag day. ROOT withdrew the earlier scoped-bridge / dated-RED split:
a newly red verdict never receives an exemption. P10 landed 0a8c780 first.

The candidate declares its read set through s0, s1 and blocker. The emitted
holePointCovered checks the key of an actual point under self; a point whose
value is none is an observed absence, whereas a missing point is unobserved.
holeSupportCovered searches all three bounded points by identity. Optional
dependencies that are none impose no read. The source receive path remains
readsData/relReads on RowView under self only; no cell pins or foreign rows
are exposed, and no kernel or generic row-view API changes.

holeCheckedJudge collects coverage before the raw judgment. Its coverage
check is the finite three-role lowering of P10 Trace.collect, established by
holeCoverageCheck_application against holeCoverageOutcome, which calls that
LANDED collector. This is generated core code with a refinement proof, not
a direct native checkedJudge call hidden in the interpreter. The package
binds this wrapper as its shared holeJudge value, so propose, fill, select,
accept, prune and rejudge all cross it. An omitted support refuses by its
role (support0 withdrawn/support1 withdrawn); an omitted blocker refuses
pruned. Missing observation cannot become a negative liveness observation.
Complete negative observations still reach rejudge's status renderer.

**Bridge.** hole_judgment_admission_bridge is about the actual emitted checked
judgment and admission gate: successful execution iff P10's finite collector
succeeds AND the existing closed-Lang world judgment verifies. No complete
caller read set is assumed. Only PROVIDED observations must be authentic;
the resulting coverage is enforced by the generated expressions. The fixed
complete-observation form is a corollary. The old raw calculation is retained
as holeJudge_fixed_observations. Clause/probe BigStep premises remain the
representation boundary; the bridge does not claim a whole-Kernel.Receive
simulation or erase independent chooser, existence, window, stale, budget
or law checks. holePointCovered_meaning proves the actual key comparison
for arbitrary optional row points, separately from liveness.

**Price premises.** LANDED theorems gaining hypotheses: none. LANDED theorems
restated: none. These changes affect the UNLANDED hole/bridge and add new
coverage statements. Existing activity and equality statements retain their
reviewed bytes; the unlanded bridge's scope/names and proof are revised.
The contextual calculus, its judge and P10 proofs retain their landed bytes.
No gate, waste ceiling, slot bound or pin changes. The inherited benchmark
measured-value downward re-pin and granted HOSTING cutover remain in this
same bundle.

**Real evidence.** The predecessor's complete 71-line Receive probe admitted
all three requests after removing only the live blocker fact pin. With the
wrapper, select, accept AND rejudge refuse pruned by name; pinned absence
after withdrawal still permits rejudge to record verified and retain the
reason. The permanent named hole:omitted-blocker-pin-admits tooth runs both
inside the default journey and as a registered dedicated argument run.
No dated RED or known-red exemption lands. The exact generator bypass
reproduces RED (3); restoring the wrapper restores GREEN.

The checked bundle measures helper ROMs 59747 / 65139 / 12525 bytes, root
29521; every installed package is below the unchanged 65536-byte slot bound.
The largest has 397 bytes of headroom. Nine kernel-executed coverage teeth
distinguish all roles, observed absence, unrelated rows, order, and a false
clause with missing coverage. Disabling each of the three coverage checks
must refute its actual tooth; the integration bypass drives real Receive.

**Alternatives.** Treating omitted blocker observations as false is the
confirmed fail-open. Making every negative judgment refuse would destroy
rejudge's retained statuses and is not this repair. Enumerating the entire
facts relation would change the bounded read discipline and is unnecessary:
the candidate itself names the finite dependencies. Changing the kernel to
supply an ambient lookup oracle would widen this task into a different
language/receive design. The chosen collector implements P10's already
reviewed missing-versus-absent boundary within the existing method interface.

**Critique.** The generated hole is still limited to two supports and one
blocker. Authentication of supplied decoded row values and the clause-to-
model relation remain explicit semantic obligations, as in P10; completeness
is no longer one. Missing and semantically negative observations deliberately
share existing method refusal names, while rejudge distinguishes them by
refusing only missing observations and recording observed negative results.
The wrapper increases select from 476/688 to 644/928 required steps/ticks in
this fixture. A second key scan is bounded by three points, but it is real
work and not claimed to be a minimum semantic read set.

**Meta-critique.** A collector proved in isolation would leave the same wound.
The production binding, actual Receive omission requests, and a mutation
that removes that binding test the integration. Conversely, calling this a
whole-receiver theorem would overstate its BigStep representation boundary;
the correspondence is the checked judgment segment, with collection on its
success side and independent receiver checks still in force.

**P13 validation receipt.** Scoped build of the changed proof modules plus
Surface/Resident consumers and deployed host/resident tools GREEN (276 jobs,
6G/two threads, Lean's finite default heartbeat cap). Whole 754-line default
lang-journey output read, GREEN. Dedicated omission journey GREEN. Filtered
cargo test --locked -p nanodregg-launcher --test resident_bell -- --nocapture
passes 1/1 in 72.07s with this worktree's own cargo target; expected pathMissing,
crashLoop and refusal/restart controls precede its success.

Four source mutants individually bypass support0, support1, blocker coverage
or point-key equality. Each altered definition builds, then the actual Lean
kernel reports that the relevant named coverage tooth is false. Real semantic
diagnostics: CX-P13-plant3-s0-tooth.log:2 (theorem line 28),
-s1-tooth.log:2 (32), -blocker-tooth.log:2/5/8 (36/40/61);
CX-P13-plant4-key-tooth.log:2 (61). The fifth mutant bypasses the package's
checked-judge binding: CX-P13-plant-bypass-receive.log:58/59/60 admits the
three omitted-pin requests and ends RED (3). Restored real Receive is GREEN.
All cited outputs and successful mutant-build outputs were read whole.
The first diagnostic attempt hit pretty-printer recursion; the second used
an unsupported pretty-printer option and is INVALID evidence. The final
three-role runs use maxRecDepth 10000 to expose the genuine semantic failure,
with explicit maxHeartbeats 800000; no production resource bound changes.
Point-key mutation is a separate real run, not a synthesized diagnostic.

Builder's own disjunct/premise read covers every added/revised statement.
ROOT's independent second reader must review the new coverage statements and
revised bridge before landing; this receipt does not claim that approval.


**Independent second reader (CX-READER-ACT3, 2026-10-20 real).** LAND.
Read all 17 added/renamed/revised coverage and bridge statements in full with
the disjunct check; no vacuous alternative, free witness or assumed admission.
The bridge certifies the emitted checked judgment segment, with supplied-row
authenticity explicit and collection success on the conclusion side. Existing
Std statements and resident proof bytes are unchanged; no landed premise cost.
ACT2's other 70 statements and ACT's 16 equality statements retain reviewed bytes.

Independent real-Receive omission probe refuses select/accept/rejudge as pruned.
Removing only the production holeCheckedJudge binding reproduces three admissions
and RED (3); restoration returns GREEN, including pinned-absence withdrawal.
Whole logs read: CX-READER-ACT3-probe-{green,red,restored}.log; actual failure
lines 58-60 of probe-red, no harness errors. Helper ROMs 59747/65139/12525 B and
root 29521 B install through the existing path, all below unchanged 65536 B.
The 27 changed/reached modules re-elaborate at 6G/two threads with explicit
maxHeartbeats 800000. P13's whole resident_bell output and all four final
individual coverage mutation logs independently read. Bell, bench and equality
source bytes are unchanged; the actual ACT2 benchmark/control outputs confirm
20.179 with unchanged method and ceilings. Main's 998f75a decision prefix is
preserved in the rebase onto 710dd08.

**Review critique.** The bridge still exposes its clause/observation representation
boundary; it does not quantify arbitrary authenticated Kernel.Receive requests.
Operational omission tests supply that separate integration evidence. The
largest fixture ROM has only 397 B headroom; generic construction refuses any
oversize field/root through the existing bound rather than widening it.

**Review meta-critique.** A renamed conditional equivalence would not close ACT2's
wound. The independent binding mutation makes that distinction observable:
the same real requests change from three named refusals to three admissions.


**Concurrent P8 integration (CX-READER-ACT3, 2026-10-20 real).**
The first landing passed two full judges, but both lost to newer main tips.
P8/ad96bab added a commitment fixture by splicing the old holeText while this
bundle replaced that fixture with the generated hole. The third merge was
textually clean and correctly failed compilation on the removed identifier.

**Decision.** Keep P8's full client and compose its atomic commitment with the
actual generated select method. The root adds a commit field that checks the
contract deadline, calls the imported checked select, and returns its candidate
edit plus accepted=true and the ordinary one-unit transfer in the SAME method
result. The kernel still admits that result atomically. No legacy hole clone,
new production API, method-check bypass, or saved effectful continuation.
P8 installs the existing helper bundle, links actual helper identities, pins
its import closure on create/invoke and supplies the proposal's support row.
Its root is 36998 B; all helper/root packages use the unchanged install bound.
The printed source remains available to package-mutation probes; its unlinked
library identities are replaced by the actual installed identities before
installation, as with HoleBundle.link.

All P8 row predicates are retained, including named deadline, moved-support,
accepted, stale, replayed, transferSpent and recovery checks. Its 15 landed
theorems and the Std/resident statements are byte-identical to main.
PRICE PREMISES: no landed theorem gains a hypothesis; none is restated.

**Evidence.** Independent standalone actual-Receive P8 control GREEN.
Bypassing the deadline yields actual admitted at the contract-deadline row,
RED (1); bypassing the generated select yields admitted at moved-support and
transferSpent instead of accepted at repeated commitment, RED (2). Whole logs
CX-READER-ACT3-p8-plant-deadline.log and -p8-plant-select.log read; no synthetic
expected failure output or harness error. The latter has an unused binding
warning caused by bypassing select; it still installs and executes its mutant.

**Critique.** P8's external transfer commitment does not dispatch the separate
hole-filling activity: it retains its landed atomic-value-transfer experiment.
The compose step trusts only a checked method result and carries its edits,
so dropping those edits or bypassing selection would be a different program.
The P8 model-to-package correspondence retains its earlier stated scope;
no new end-to-end compiler theorem is asserted.

**Meta-critique.** Preserving the old text beside the new generator would have
made compilation green while leaving a second hole implementation. Composing
the existing checked selection makes the new consumer share the repaired
boundary, and the two real bypass plants keep that connection refutable.

**Post-port validation.** The combined lang-journey is GREEN (787 output lines),
its dedicated omission tooth GREEN, and harness-control RED (1); the scoped
Journey/Integration build passes and Integration's statements and proofs are
byte-identical to ad96bab. All nine P8 mutation categories were independently
rerun against this port and are semantic RED: deadline (1), support (1),
accepted (1), cap (4), pin (1), environment (3), certificate (1), live (1),
version (1). Every whole output was read. Support and accepted mutations alter
the installed generated helper bodies; the accepted mutation makes fresh
reexecution reach transferSpent, and the support mutation admits moved support.
An initial root-only accepted mutation changed no actual check and stayed
GREEN; it was rejected as a no-op and replaced by the helper mutation. No
production check was removed, no row expectation changed, no theorem weakened.
The final source rebase also preserves HOSTING/0cd046c's unrelated startup fix.

## LANG-P7 preparatory substitution and deployment fork (2026-10-21 real; CX-P7)

**Scope.** Nano is a demonstration Mini can take. The ruled destination remains contextual
holes in deployed Lang, not the closed-hole boundary of LANG-68. Main's fixed activities
bundle is 68e704d. This preparatory entry does not claim that destination is implemented.

**Decision before building the common foundation.** Add capture-avoiding simultaneous
ordinary substitution over Lang.Term, with list substitution, lambda/case binder lifting,
and its typing theorem over the current deployed HasType. This is necessary for either
placement of contextual instantiation. The existing ref substitution is not replaced
until the installed representation is settled. No existing executable/check changes.

**PRICE PREMISES (foundation).** Landed theorems gaining hypotheses: none. Landed statements
restated: none. Existing proof files touched: none. New proofs: substVarRow_ascending,
upVarSubst_typed, substVar_typed, substVarFields_typed, substVarArms_typed,
substListFn_typed, substList_typed, substList_lam_capture, substList_case_capture,
substList_nested_capture, substList_ambient_checked, substList_replaces.
All are implications or equations without a disjunctive escape.

**Unresolved deployment fork, reported ASK to ROOT.** The generator's candidate relation stores
value:V and checkRel requires its value to be data; the model's Candidate instead stores
Term. The bridge explicitly assumes a closed context, empty hypothesis list and a typed
filling. A substituted-hole constructor alone does not make syntax into a stored candidate.
(1) Stage instantiation at authoring: check/fill/repair terms, emit and install each resulting
closed package. This retains the old machine judgments as closed specializations with no
added hypotheses, but the repair journey crosses authoring/install; it is not a dynamically
resumable installed open term.
(2) Retain a contextual signature and candidate code in package/ROMs, authenticate selected
candidates through pinned rows, and instantiate for each fresh invocation. This requires a
runtime hole environment and its typing, cost and provenance invariants, plus package-wire
declarations. Old closed statements can remain specializations; the generalized statements
must bind the environment checked by load, never assume an unverified filling is typed.
Recommend (2) on semantics, not a cost argument against (1); no dependent change is made
while this contract-required fork is pending. Re-genesis is never a design penalty.

**Literature.** Murase, Nishiwaki and Igarashi, Contextual Modal Type Theory with Polymorphic
Contexts (ESOP 2023, arXiv:1801.09225v2), abstract and introduction: context polymorphism
abstracts over portions of a context and is the principled system for code under arbitrary
ambient extensions. The ordinary weakening/substitution lemmas here are prerequisites,
not an implementation of their context-polymorphic language. Norell, Towards a practical
programming language based on dependent type theory (Chalmers PhD 2007), chapter 3,
pp. 50–54: guarded constants in the signature retain a candidate and constraints and
reduce only when the constraints are discharged. This precedes storing a blocked hole's
guard with its declaration; it does not prove nano's withdrawal or effectful resumption.

**Wire audit pending CODEC.** Bounds.packageWireVersion is 3. The unused term tag is 18
(tag 15 is a row-field node, not a Term constructor). Adding hole at tag 18 requires a
version bump, an updated boundary tooth and an explicit index/substitution encoding.
Every package's leading version byte changes, so all package ROM IDs and transitive
import IDs change. Old version-3 packages must refuse lang/package-version; no fallback.
Emit/Vectors.lean owns termRows, rawPackage, packageVecs and the lang/package/3 site.
Those are CODEC-owned; the lane has requested ROOT's patch or an explicit ownership grant.
No source/vector meaning changes are claimed by this preparatory patch.

**Critique.** This foundation is useful but not P7: no 18th constructor, no generalized
LangHasTy and no deployed five-outcome journey yet. Proving capture avoidance without
connecting it to fillRefs would merely move the same integration boundary. The final
implementation must use this function at hole occurrences and test real installed code.
**Meta-critique.** It would be convenient to call a repaired host-side Term a deployed hole,
or to choose staging just because its proofs are smaller. The explicit fork keeps that
scope choice visible. Conversely, a second evaluator for code bytes would create a twin;
the live design must use the existing checker and demand machine.

## LANG-P7 live contextual packages — implementation ruling (2026-10-21 real, CX-P7 run 2)

**Decision before construction.** ROOT ruled the live shape: the typed hole signature and
candidate code reside in the package ROM, current selections and their support are checked
from pinned rows, and every fresh invocation instantiates the selected code with the explicit
substitution at its hole occurrences. It runs the existing demand machine. No staged package
replacement or second evaluator is introduced. Ordinary package refs and contextual holes have
separate namespaces. The checker retains its closed API and gains a signature-indexed
form of the SAME recursion; the typing relation checks each substitution entry against the
corresponding declared context, including exact length. An unresolved hole is refused by name.

**PRICE PREMISES.** Landed theorem hypotheses added: none. Existing closed APIs remain
specializations; generalized results explicitly bind the checked signature and environment.
Affected proofs: inferE_sound/complete, inferFields_sound/complete, inferArms_sound/complete,
infer_sound/complete/iff, hasType_wf/fieldsTy_wf/armsTy_wf, relocate_typed and row/arm companions,
relocate_id/relocateRow_id, load_libTy, bigStep_deterministic and sel/ext companions, agrees,
derives_leads, derives_bigStep/bigStep_derives, step_sound/progress/preserves/depth,
checkLib_sound/checked_never_stuck, stepBytes_le_paid/step_paid, Need/NeedComplete induction,
bigStep_relib/sel_relib/ext_relib, relocate_noRef/relocateRow_noRef, step_lits,
relocate_digestLits and row companion, term_termSx and row/arm companions, termSx_ok,
hasType_canon/hasType_prints and companions, termOf_termTree/fieldsOf_fieldsTree,
termOf_inv/tree_of_termOf and package inverse/version teeth. Contextual instance proofs:
rename composition/identity/congruence, usesVar rename, strengthening factor, variable
renaming typing, usesRef rename/fill origins, fillRefs_typed and row/arm companions,
declaration lookup/filter, langHasTy_nil_iff, langLaws, lang_template_toy and HoleBridge.
The explicitly authorized boundary langTemplate_no_hyps is replaced by deployed strengthening.
This is a pre-build spread, not a claim all ports have compiled.

**Literature and scope.** Murase, Nishiwaki and Igarashi, Contextual Modal Type Theory with
Polymorphic Contexts (ESOP 2023; arXiv:1801.09225v2), motivates code typed under abstract
ambient contexts; ordinary capture-avoiding substitution does not by itself implement their
polymorphic calculus. Norell, Towards a practical programming language based on dependent
type theory (2007), chapter 3 pp.50–54, supplies the precedent of guarded constants in the
signature: a blocked declaration persists and reduces only once its guard discharges.
Nano retains its explicit guard and authenticated dependency observations at invocation.

**Wire contract.** Leading package version 03 becomes 04; lang/package/3 becomes
lang/package/4. Hole term tag 18 (hex12), u32 index payload, children in substitution order.
Existing term/type/primitive tag meanings do not move. Unknown-tag tooth becomes19;
malformed tag18 payload and substitution children receive separate teeth. The signature and
candidate sections are part of the ROM tree; their exact section table is recorded with the
implementation before vector generation. Every package re-ids; import digest literals re-emit
transitively. Version3 refuses lang/package-version. No old bytes are reinterpreted.
ROOT grants Emit/Vectors.lean and generated CODEC outputs plus gates/codec-vectors.tsv;
generated output is emitted, never hand-edited. No handoff is READY until vectors and the
live deployed experiments have run.

**Critique.** Invocation-time expansion must be bounded before allocation grows; candidate
syntax must be checked against its own context rather than a same-result-type impostor.
Loading ROM alone authenticates no selection row: the live runner must check pinned support
and account for the actual chosen code, with wrong-context, cost and moved-support plants.
**Meta-critique.** Calling author-time filling deployed would repeat LANG-68. Equally,
changing every closed theorem to assume a sound runtime environment would hide a missing
boundary proof. The closed specializations and the checked environment theorem prevent that.

### LANG-P7 runtime boundary refinement (CX-P7, real 2026-10-21)
PRICE PREMISES: no landed theorem gains a hypothesis. Existing load, install,
runSetup and source/provenance statements remain the closed specializations;
live loading must additionally prove the checked instantiation invariant.
The generalized checker treats a hole signature like its library context;
wellformedness of declared context/result types is checked at the package
boundary, not imposed as an extra premise on the old arbitrary-type hole model.
This avoids silently restricting its quantified result type.

Live ROM declarations carry the contextual type, candidate syntax, a pinned
selection location, context support locations and expected versions, and a
typed guard. The selection row supplies only a candidate index, never code.
All candidate syntax is checked when admitting the package and again when
instantiating; selection and support are read from the authenticated RowView.
The same evaluator runs the guard and the filled method. Preparation is per
invocation, and no filled package is encoded, installed, or cached as a ROM.
An unused withdrawn contextual assumption can be removed by strengthening;
a used withdrawn assumption suspends that selection unless a supported candidate
is explicitly selected. Guard failure stays blocked. Cost is computed from
actual template and candidate syntax before output allocation.
Critique: retaining closed APIs risks proving only the old path. The live
deployed journey and live invariant theorems must therefore name the deployed
entry points, including current-row reauthentication, not just the checker.
Meta-critique: package bytes commit to syntax, while invocation pins commit to
the evolving facts. Conflating those commitments would either stage the design
or accept stale support. Both are excluded by the runtime boundary above.

### LANG-P7 deployment bridge and textual identity (CX-P7, real 2026-10-21)
PRICE PREMISES: none added. program_run_past_extraction now names runSetupLive
and charges total budget = machine budget + S.preparation. Its machine run and
extraction premises are unchanged; the original runMeasured_past_extraction
remains the closed specialization. New live variants prove the actual deployed
program path. loadUsing is one shared closure traversal, parameterized by
admission; closed and contextual admission both produce closed typed machine
libraries. The contextual admission retains original ROM packages, rechecks all
candidate code and literals, and fills transient library bodies afresh.

Readable package text adds a holes section containing hole/context/result,
selection, hypotheses, guard, and code/candidate/supports forms. A candidate's
explicit context uses the printer's existing xN binder names. Empty signatures
retain the old source spelling (source is not the versioned wire). The printer
checks its completed text against the one reader before returning: Read sorts
rows, so otherwise malformed metadata could print as a different ROM. No decoder,
gate, or canonicality check is relaxed. Positive live print/read rows and an
identity mutation tooth are required, since a success implication alone cannot
show the printer produces a useful artifact. Critique: this is an additional
reader pass. Meta-critique: it shares the authoritative source normalization and
makes textual ROM identity an executable invariant instead of maintaining a
second normalization checker.

### LANG-P7 CODEC flag day: exact moving bytes (CX-P7, real 2026-10-21)
PRICE PREMISES: none gained. Wrong-version theorem conclusions restate the
version-specific refusal site lang/package-version/4. The actual vector check
caught that changing the accepted version under the old unversioned refinement
name changes meaning under the same tag; the site is therefore renamed, not
re-pinned under its old tag.

| Location | Old bytes/schema | New bytes/schema |
| --- | --- | --- |
| Package prefix | 03 | 04 |
| Package root child count | 08 | 09 |
| Ninth root child, including closed packages | absent | tag 03, empty payload, hole-declaration children (empty section is 03 00 00) |
| Term | tag 12 hex unused | tag 12 hex, four-byte little-endian hole name payload, direct ordered substitution term children |
| First unknown term tooth | tag 12 hex | tag 13 hex; separate tag-12 empty-payload malformed-hole row retained |
| Hole declaration | absent | tag 03, u32LE name payload, seven ordered children: context, result, candidates, selection, hypotheses, guard pin, guard code |
| Context | absent | node0 empty payload, ordered tyTree children |
| Candidates | absent | node0 empty payload, ordered candidate children; each node0 empty [termTree body, node0 empty support pins] |
| Selection | absent | node0 key bytes [node0 u32LE relation leaf] |
| Hypotheses | absent | node0 empty, one optional pin per contextual variable |
| Pin | absent | node0 key bytes [node0 u32LE relation leaf, node0 u64BE version leaf] |
| Optional pin | absent | none = node0 empty leaf; some = node1 empty [pin] |
| Guard code | absent | existing termTree encoding; guard gets one boolean variable |
| Refinement names/tags | lang/package/3 and lang/package-version | lang/package/4 and lang/package-version/4 |

All existing type tags, primitive tags, term tags 0..17, and first eight package
sections retain their internal encodings. Tree node/payload/child lengths retain
the existing canonical varints. All packages re-id, including closed helpers:
the prefix and ninth section change. Re-emit package ROMs/helper bundles, source
unit installs and package vectors; regenerate generated.rs through emit-rust
(the protocol table is expected byte-identical and must be checked). Old
version-3 and unversioned packages refuse at lang/package-version/4 before their
tree is interpreted. There is no old-version loader or reinterpretation. Source
package text remains readable and gains an explicit holes section for live ROMs.
The ordinary vectors emitter includes every constructor plus a declaration with
both optional-pin cases, multiple candidates, supports, a guard and nonempty
substitution; generated-files must compare it against a fresh emit.

The closed checkWith specialization now explicitly refuses a nonempty contextual
signature and non-wellformed import interfaces. The deployed contextual checker
handles the live signature. These checks make the closed boundary explicit and
retain every theorem's premises; no deployed valid import was previously allowed
a malformed interface (every loaded package already passed checkShape).

### LANG-P7 live resolution and final proof spread (CX-P7, real 2026-10-21)
PRICE PREMISES: LANDED theorems gaining a hypothesis: none. Checker soundness,
completeness, equivalences and uniqueness generalize the signature with the empty
specialization preserved. Renaming/strengthening do likewise. fillRefs_typed,
fillRefsFields_typed and fillRefsArms_typed replace the obsolete ref-as-hole
hypotheses with contextual candidate typing and retained declarations; ordinary
imports stay untouched. hasType_usesRef, fieldsTy_usesRef and armsTy_usesRef now
name declared holes. step_fault includes the residual-hole refusal case.
program_run_past_extraction names live setup and the charged preparation budget.
The five version-refusal conclusions name the version-4 codec sites. Fixture
constructors gain the empty signature field; the unknown-tag fixture moves to19.
The sole deleted theorem is the explicitly superseded langTemplate_no_hyps;
deployed generated_signature, linked_signature, selected_uses_context,
strengthening_factor and strengthening_uses_argument replace its boundary.
Other touched landed statements retain their hypotheses and conclusions.

Resolution is a sum of authenticated selected code and a typed blocked refusal.
A blocked resolution produces no selection receipt; demanding it fires the
original refusal name. Independent management code remains callable to bootstrap
or repair it. This is the ROOT-ruled Norell-style guard behavior; it does not turn
a demanded refusal into an accepted result. Both cases enter the same final
closed typing, literal-source and size checks. Guard execution is bounded to256
machine ticks; the explicit structural preparation charge is bounded by the ROM's
maximum candidate syntax and number of declarations. The cost theorems describe
this language budget, not host wall-clock time.

The closed printer retains its landed invalid-input behavior because relWf is
load-bearing in badRel_prints/badRel_reads_other; contextual ROM text alone gets
the new literal read-back equality check and its named refusal tooth.

The signed journey executes the five outcomes and eight experiments through
Receive.submit/World.admit with installed contextual ROMs, guarded selection
rows and fresh authenticated observations. Contract change uses the same ROM
under another object's immutable cap, not an unauthorized mutation of frozen
state. The cyclic example compiles the three-node least-fixed-point computation
into the selected contextual filling: withdrawing the grounding loses p and q
while independent r survives. It is a finite concrete deployed experiment, not
a claim that the runtime now supplies a general cyclic dependency engine.
P8's atomic commitment demands hole0[nat1]; the selected open filling var0
determines the consumed amount. The old full management regression is also
parameterized over the live bundle to retain omitted-blocker refusal teeth.

Critique: a success-only invariant could hide an always-refusing implementation.
The positive signed journeys, explicit contextual argument dependence and
mutation runs therefore accompany the boundary theorems. The provenance and
final typing checks are defensive against implementation faults; their teeth
inject such faults before disabling the corresponding boundary, rather than
claiming welltyped ROM input normally reaches those errors.
Meta-critique: a new proof API must preserve the live dependency on rv/self.
The generic extraction lemma abstracts the complete setup function; it avoids
forcing a row-dependent loader into the old row-independent loader parameter,
which previously caused elaboration to exceed the6G cap.

### LANG-P7 final convergence (CX-P7, real 2026-10-21)
PRICE PREMISES: none gained. empty_package_surface only supplies the explicit
empty ninth Package field in its two fixtures; its assertion is unchanged.
The whole Lang.Proofs closure compiled with that final fixture port checked
separately. The permanent contextual checks (59) and signed contextual journey
pass after restoring every mutation. A fresh ordinary vector emit is byte-identical
to gates/codec-vectors.tsv (263 vectors, 56 sites). emit-rust --check and
emit-units --check pass: generated.rs and deploy/units are unchanged. Installed
package ROMs still all re-id and must be re-emitted/reinstalled at the flag day;
the unchanged units are service launch files, not serialized package ROMs.

### LANG-P7 explicit contract succession (CX-P7 run 3, real 2026-10-21)
ROOT ruled B after the reader exhibited the false old library-changing contract.
This entry supersedes the run-2 claim that every old contract was preserved.
PRICE PREMISES: no other landed theorem gains a hypothesis. The six obsolete
ref-model names below are DELETED, not rebound to a different proposition:
- fillRefs_typed -> fillHoles_typed: old import replacement could change Δ to Δ';
  live filling preserves Δ, fills named holes with code typed in each declaration's
  context via its occurrence substitution, and transports retained declarations Ω to Ω'.
- fillRefsFields_typed -> fillHolesFields_typed: the same explicit contract change
  for record fields; ordinary imported refs remain refs.
- fillRefsArms_typed -> fillHolesArms_typed: the same explicit contract change for
  case arms, preserving their payload binders through capture-avoiding substitution.
- hasType_usesRef -> hasType_declaresHole: old used import positions belonged to Δ;
  live used contextual hole names must occur in Ω, including holes in substitutions.
- fieldsTy_usesRef -> fieldsTy_declaresHole: the same change for field occurrences.
- armsTy_usesRef -> armsTy_declaresHole: the same change for arm occurrences.
The reader's Δ=[nat], Δ'=[], t=ref0, filling=nat0 example is intentionally NOT
an instance of the new filling contract: source and target have the SAME Δ.
No retained theorem claims imports can be eliminated by contextual filling.
The closed checker and renaming/strengthening statements keep their old names and
byte-identical statements; generalized proofs receive explicit _live names.
Touched proof families in this repair: Check; LangRenaming; LangSubstitution;
LangFilling; LangOccurrences; LangInstance; closed deployment bridge and teeth.
Deployed closed admission must use the existing closed admission exactly when
the ROM has no holes: no contextual expansion is necessary, and the closed
checker already excludes residual holes. This is the closed specialization of
one loader, not a second substitution operation. We will prove equality through
the actual live loading/setup/execution path, including charged ticks.
Critique: claiming API preservation from inferred empty parameters concealed a
real semantic replacement. Explicit names and counterexample teeth must expose it.
Meta-critique: preserving a stale name to minimize a diff would repeat that error;
preserving the closed executable specialization prevents redesign from silently
charging closed packages for nonexistent contextual work.

### LANG-P7 closed bridge and successor teeth (CX-P7 run 3, real 2026-10-21)
PRICE PREMISES: none for every other landed theorem. The exact source-statement
comparison restores all 13 checker statements, four renaming/strengthening
statements and program_run_past_extraction under their original names. Their
generalized results are named with _live. The latter old theorem now reaches
the deployed Program.run through program_run_closed, rather than claiming the
closed theorem alone establishes deployment.

Closed admission delegates to admitPackage when holes=[]; contextual admission
and all its selected/blocked checks remain in force for nonempty signatures.
The closed checker already excludes holes, so no contextual work bound is
charged or imposed on the closed body. The bridge derives a closed loaded
closure from successful old load (no new old premise), proves its preparation
charge zero, transports the same RunSetup and proves equality of runMeasuredLive
and runMeasured for EVERY budget, including faults, calls, edits and charged
ticks. checkInstallContextual's closed branch uses checkInstall exactly;
law execution uses the same admitted library. Wire version4 remains a flag day:
this preserves behavior of the re-emitted closed package, not loading version3.

The six superseded statements' teeth are carried as follows:
| Deleted statement | Live successor | Named successor tooth |
| --- | --- | --- |
| fillRefs_typed | fillHoles_typed | fillHoles_term_tooth |
| fillRefsFields_typed | fillHolesFields_typed | fillHoles_fields_tooth |
| fillRefsArms_typed | fillHolesArms_typed | fillHoles_arms_tooth |
| hasType_usesRef | hasType_declaresHole | declaredHole_term_tooth |
| fieldsTy_usesRef | fieldsTy_declaresHole | declaredHole_fields_tooth |
| armsTy_usesRef | armsTy_declaresHole | declaredHole_arms_tooth |

Main's shared lang_template_toy is retained over the actual hole constructor:
declared checks, undeclared refuses, filling changes syntax, result types with
the declaration removed. lang_strengthen_toy is unchanged. Main has no separate
field/arm concrete teeth for these six; the named successors add them.
reader_import_contract_tooth carries the reader's counterexample and shows the
new contract cannot type its source at the proposed empty target library.
fillHoles_preserves_import_tooth applies the successor with Δ=[nat] and proves
the import remains typed there, while usesRef reports no contextual occurrence.
Runtime rows successor-fill-{term,fields,arms}, successor-declared-{term,fields,arms},
reader-import-contract and closed-admission-identity exercise those same boundaries.
The last supplies a preparation function that always refuses: closed admission
must succeed without invoking nonexistent contextual preparation.
Critique: a success implication could hide a refused old package; the closed
admission row is positive and the bridge constrains faults and tick accounting,
not just the success projection. Meta-critique: maintaining both old import
substitution and contextual filling would conceal two meanings; the old six
names are absent, and the exact broken meanings remain in the succession entry.

### LANG-P7 consumer ports and seventh contract succession (CX-READER-P7 run 3, real 2026-10-21)

ROOT granted KERNEL InvokeWitness/History and LEDGER EscrowRun proof-consumer ports,
including named dependent proof consumers. The additionally reached consumers are
Kernel/Proofs/InvokeTreeWitness.lean, Ledger/Proofs/EscrowWitness.lean and
Ledger/Proofs/EscrowAdmitted.lean. Their statements remain unchanged.

PRICE PREMISES: none on every retained landed theorem, public or private.
Compared against 3bd8c12, all retained statements in the six ported consumer files
are byte-identical. The earlier P7 source receipt is unchanged except this appended
decision and regenerated SIZE.md. The seventh superseded contract is:
- Ledger.Proofs.EscrowRun.run_of_program (private) -> runLive_of_program (private).
  OLD: successful deployed Program.run of ANY package implies there exist t,n
  with successful CLOSED runMeasured returning (s,calls,rows,t,n).
  NEW: that same success implies there exists n with successful runMeasuredLive
  returning (s,calls,rows,used,n), preserving the Program.run charge used exactly.
  The old generic closed implication is false for contextual packages. The new
  statement names the actual deployed path; it does not assume a closed closure.
  Escrow's callers derive the closed result from its fixed holes=[] and imports=[]
  through runMeasuredLive_leaf_closed, with those facts discharged by reflexivity.

ClosedLeaf proves equality of live and closed loading/setup/measured execution/law
evaluation for a leaf ROM with empty signature and no imports. These equalities
include refusals and charges; no success-only shortcut is used. Counter, relay and
escrow witnesses run through this bridge. Existing payout, next-run, nested-invoke
and history theorem statements and teeth remain intact.

History cannot use a closed-package premise: its arbitrary package may contain
contextual imports and its NoRef law may contain dormant holes. LawMeaning relates
the source law to the law loader's unresolved preparation, then proves backward
meaning preservation mutually for BigStep, selection and extension. The relation
preserves labels, base values, faults, closure environments and suspended fields;
an unresolved hole becomes only the same named refusal. It has no imported-ref
constructor, matching the existing NoRef premise. LawReceiver extracts the actual
contextual load, original ROM and prepared field and proves
judgeOneContextual_admits_relib under every library, without adding any signature
or closure premise. History's object_history_chain and object_history_start use it.

Teeth: contextual_law_dormant_hole loads a nonempty-signature package from encoded
ROM through loadContextual and the actual Program.judge, admits a law containing
an undemanded hole, and derives the original ROM law's meaning. Its paired
contextual_law_demanded_hole demands the hole and proves the exact deployed refusal
lawDenied 7 "law: refused holeUnresolved". Existing escrow_second_release_refused,
escrow_link_bites, admitted deposit/release, counter next-run and nested-invoke
witnesses rebuild on the live path. No runtime check or gate is removed or changed.

Critique: fixed closed witnesses alone would miss History's arbitrary contextual
packages; NoRef excludes imports but does not exclude holes. The backward relation
must cover suspended fields, knots and closures, not merely direct evaluations.
The two contextual-law teeth exercise both dormant and demanded holes.
Meta-critique: a small closure hypothesis would make the compiler green by reducing
the theorem's scope. Instead the port pays for the semantic transport proof, while
retaining the original public contracts and explicitly naming the one obsolete
private contract. Proof duplication is limited to extraction scaffolding; the
deployed evaluator, loader, substitution and checks have one implementation.

The second-agent boundary is unchanged: CX-READER-P7 prepares READY-PORTS;
CX-P7 run4 reads these new statements and lands with the full lang! judge.

### LANG-P7 axiom census correction (CX-P7 run 4, real 2026-10-21)

PRICE PREMISES: none. No theorem statement or proof changes in this correction.
The live-constructor port already replaced Print.badRel_reads_other's native_decide
proof with parse_layout, bounded case analysis and decide +kernel while retaining
the exact statement. Its elaborated axiom set is now propext, Classical.choice
and Quot.sound; the full judge correctly rejects the two obsolete allow rows for
that theorem and its absent _native.native_decide.ax_1_1 auxiliary.

ROOT granted removal of those two rows from gates/axioms-allow.tsv in this lang!
on real 10-21. The two Hosting invoke_slots rows are unchanged. This removes unused
trust exceptions; the census code, refusal rules and remaining allow entries are
unchanged. The existing malformed relation tooth still proves the same unequal
readback result. No new check or theorem is introduced by the table correction.

Critique: a successful proof build alone does not establish that the old native
exception disappeared. The full axiom census reports the stale rows and a direct
#print axioms query independently finds only the three standard axioms.
Meta-critique: keeping stale exceptions would misstate the current trust boundary;
deleting them alongside the kernel-checked replacement preserves the statement
and lets the unchanged census enforce the smaller exception set.


The corresponding LANG-owned native_decide component row is also removed from
gates/tcb.tsv (SHARED in OWNERS). Its documented lift condition is now met:
badRel_reads_other is checked by the kernel. The unchanged source TCB gate
requires this table to agree with axioms-allow.tsv and rejected the stale row.
No TCB checker rule or other component changes.

### LANG-P7 restore the bar's measured tail (CX-P7 run 4, real 2026-10-21)

PRICE PREMISES: none. No theorem statement or proof is changed by this fixture
repair. ROOT granted Protocol/Rows.lean, Protocol/Rows/Loopback.lean and
Protocol/Rows/Run.lean for the bar fixture/instrumentation, plus the measured
staleBase pin change for the six wire-4 install bytes; every ceiling stays fixed.

The full judge exposed a real measurement failure. With wire 4, the final invoke
sealed at offset 41518, exactly the synced end. The cold open read 520 framing
bytes over zero tail bytes. A zero denominator means the fixture no longer
exercises its subject and remains a refusal.

Restore the old workload shape with an explicit operator seal before the last
23 of the SAME 64 invokes: 41 invokes, seal, then 23 invokes leaving 7912 bytes.
The birth count also remains 64. barWithCount materializes --times N as N births
and N total invokes before splitting its suffix; the runner does not multiply
both parts by N. The candidate that added seven invokes instead was measured and
rejected: frames/write rose to 10.978 and steps/write to 0.993, above their
unchanged ceilings. Retaining the workload restores all honest counts exactly.

| Measure | Parent | Restored wire-4 fixture |
| --- | --- | --- |
| Honest reopen bytes / bytes past base | 8432 / 7912 = 1.066 | 8432 / 7912 = 1.066 |
| Mandatory framing beyond the tail | 520 | 520 |
| staleBase bytes / bytes past base | 41612 / 7912 = 5.259 | 41618 / 7912 = 5.260 |
| Frames / write commands | 1449 / 132 = 10.977 | 1449 / 132 = 10.977 |
| Steps / write commands | 131 / 132 = 0.992 | 131 / 132 = 0.992 |
| twiceEach frames / write commands | 2887 / 132 = 21.871 | 2887 / 132 = 21.871 |
| twiceEach steps / write commands | 261 / 132 = 1.977 | 261 / 132 = 1.977 |

The six bytes are required wire data: the empty hole section 03 00 00 adds three
bytes to each closed package; the install Turn records it both in the created
ROM cell's slot 0 (Receive.install) and in the signed call (sealTurn.event).
Version and root-arity bytes change values without changing their widths.
Codec.Kernel.turn serializes both copies. Thus staleBase's whole-log read grows
by six, while the restored honest tail and framing are unchanged. Only the
plant's exact ratio moves to 5.260. The waste table's numerical columns stay
byte-identical; its source text records the new plant and these counts.

The staleBase plant applies to the measured cold reopen. The unmeasured operator
seal uses the newest durable base, so the fault actually reaches the intended
measurement instead of destroying setup. The actual older-base flag must still
be true. Zero denominators, exact MOVED values, BLIND comparisons and the
zeroDeadline known-red control are unchanged.

Critique: the package flag day can change the seal boundary even when every
command succeeds; successful execution alone cannot validate the measured tail.
The original zero-tail run and the setup-sabotaging mutant are both observed reds.
The explicit suffix gives the bar the same measured work as its parent.
Meta-critique: increasing total work also changes per-command framing ratios.
Holding all 64 invokes and naming the checkpoint boundary preserves those
comparison units and exposes the six-byte wire cost in the mutant's exact pin.

### LANG-P7 obsolete-exception removal record (CX-P7 run 4, real 2026-10-21)
PRICE PREMISES: none. The stale-path guard correctly requires --reverts
42c261b93025 for the two intentionally deleted badRel_reads_other allow rows
introduced by that commit. ROOT explicitly authorized their removal after the
kernel proof made them unused. The generated REVERTS hunk names exactly these
two exceptions; it does not revert the rows design, theorem, or any check.
This differs from the rejected escrow_link_bites exception: that theorem was
retained, so such a removal record would have been false. Here the removal is
real and desired. Critique: deletion authorization must be explicit in the
machine-checked landing record as well as the decision. Meta-critique: the old
commit subject spans several layers; the precise path/hunk is the scope.

## LANG-PE1 — receipt-first shadow obligation journal (2026-10-21, CX-PE1)

**Decision.** Keep the existing judge authoritative and retain eight named Kernel
obligations as immutable revisions with two archived evidence routes each.
CalculusData.check inspects finite receipt data; Lean remains the external proof
checker. The new Journal modules connect actual Closure admission to matching,
successful, complete receipts and declared inputs, and instantiate Protocol's
proved repair/composition laws. Kernel source and landed signatures are unchanged.

The exporter walks actual types, proof values, inductive/constructor/recursor
structure, axiom sets and local premise applications. Shared expression DAGs
replace the initial expanding-tree encoding that exceeded 6G. Retained terms
are independently kernel-checked against current types; fresh recipes are a
separate baseline. Missing exports/imports never reduce the persistent inventory.
An inverted support index is derived from the retained list oracle. Whole scratch
outputs and source mutations are retained on hbox; gates/journal-report.md records
the measured comparisons and exact candidate identities.

PRICE PREMISES: landed theorems gaining hypotheses: none; restated: none.
The scratch required-premise variant explicitly prices its new Bool equality and
strengthened conclusion; the unused True binder is separately measured.
CROSS-LAYER: GATES (ROOT granted the journal exporter beside the census tooling, real 10-21)

**Critique.** The formal invariant stops at finite receipt data. It does not prove
the producer, SHA-256 identity, arbitrary semantic audit coverage, or a dependent
context bridge. The global-collision detector covers the exercised outer
existential escape; a newly checked literal proof is still pruned for the
advertised binding claim. Recipe source-closure hashes intentionally over-invalidate.
Exact structural expression hashes retain generated binder hygiene labels, which
also over-invalidate unrelated roots in the collision branch. Alpha canonicalization
is proposed in the lane REPORT but not applied under its refusal-change pause rule.
The exhausted-budget experiment has actual C timeouts while B still succeeds;
A's suspended result reflects deliberately unavailable receipt-service tokens,
not a fabricated kernel timeout or false target.

**Meta-critique.** A dependency graph alone cannot decide claim authority. The
pilot keeps old candidates and check receipts, token versions, pruning reasons,
grounding choices, cost and audit evidence separate, and compares its status
observation with actual kernel replay and reconstruction. Disagreement is evidence
about that boundary, not automatically a defect in Lean or a proof of invalidity.
The conservative false invalidations are reported rather than presented as an
optimization. Index-query savings exclude producer/export cost and do not assert
an end-to-end complexity theorem. ROOT's receipt-first ruling remains sequencing,
not a reduced destination: the dependent-context bridge and mini/bread acceptance
cases remain the next card.


### LANG-PE1 reader correction (2026-10-21, CX-READER-PE1)

**Decision.** Accept the explicitly measured conservative identity for this pilot
under the reader brief. ROOT already granted option B, bound-variable-label
normalization; the earlier pending-ASK wording records the builder's stale state,
not an outstanding permission barrier. B is unimplemented: canonicalization law,
roundtrip and both-direction plants remain follow-on obligations. Existing
conservative-run numbers remain unchanged.

Correct the scoped coverage receipt writer's literal backslash-n and add a
check-disabled missing-import plant. It uses a real failed Lean import and its
absent export: the enabled validator reports INCOMPLETE and retains eight owed
obligations; a scratch-only missing-file refusal bypass claims complete with zero,
which the coverage tooth rejects. No installed production check is weakened.

PRICE PREMISES: landed theorems gaining hypotheses: none; restated: none.

**Critique.** Exact binder labels still cause false invalidations (collision case
16 old-candidate mismatches although six B/C roots pass). This is acceptable pilot
evidence, not fulfillment of B or a semantic equivalence claim. The missing-import
plant checks one producer failure mode, not arbitrary exporter completeness.

**Meta-critique.** A green export plant does not substitute for the missing-import
failure path, and a permission ruling is not implementation. Keep those distinctions
in executable receipts and the comparison instead of relying on a builder summary.


**P7 integration.** Rebased onto d7989d9 by preserving the exact own decision tail
after main's decision. No P7-changed module is in the exported Kernel slice and
all baseline recipe input hashes remain equal. The reached-module build checks
the extracted HoleDecl import against the receipt adapter. No new premise or
Kernel edit is introduced by PE1.


### LANG-PE1 scoped Census release (2026-10-21, CX-READER-PE1; ROOT release)

**Decision.** CONSOLIDATION-MAP-20261021.md §6 supersedes the original full-pilot
landing scope above. Land only Census.JournalExpr, Census.Journal, Census.JournalRun,
the six journal Python helpers and comparison report. Exclude all three unlanded
Lang Journal modules and their 21 theorems. The exporter already stands independently
of contextual theory. Move finite receipt records/checks into Census.JournalRun
without a CalculusData instance; remove the toy-world command and its two active
matrix cases. Keep the original 15-case comparison explicitly historical and
preserve all old sources/outputs outside the landing. The remaining 13 source/policy
cases use real exports, kernel checks, recipes and finite Census receipt checks.

The finite disabling harness now tests Census receipt data directly. Historical
migration compares named statuses, because the Census verdict constructors differ;
new incremental/full comparisons still require exact detail equality. No claimed
Closure/Protocol repair theorem lands. Consolidation S0 is the intended consumer of
the real environment and declaration digests; the live bridge belongs to S13.

PRICE PREMISES: landed theorems gaining hypotheses: none; restated: none.
New theorems in this scoped landing: none.
CROSS-LAYER: GATES (ROOT scoped release explicitly grants Census and journal helpers).

**Critique.** The remaining checks do not prove exporter completeness, authenticity,
hash injectivity or arbitrary semantic audit coverage. Candidate-set equality and
index consistency are measurements. Bound-label normalization B remains unimplemented,
with the measured conservative invalidation reported. Source tooling is useful before
the live bridge exists, but must not be advertised as that bridge.

**Meta-critique.** Reusing Closure through an identity calculus looked like integration
while adding another language-shaped instance. The release keeps the actual Kernel
export/check boundary and records the reduced formal claim explicitly, rather than
moving the same degenerate instance into another directory.

## LANG-74 Consolidation of the contextual program: one module per concept; the toys, the second judges and the second shapes are deleted (2026-10-22; CX-FOLD; `redregg/work/CONSOLIDATION-MAP-20261021.md`, `REVIEW-20261021.md`; rulings ledger R-0001–R-0003)

**Decision.** `Lang/Contextual` + `Lang/Proofs/Contextual` (92 modules, 17,389 lines, 908 theorems at d7989d9) fold
into one module per concept. A module stays in Lang only if a deployed object reaches it, its theorems are about a
deployed object, or it is the abstract spine (calculus laws, closure, judge, provenance, repair, soundness) of which
the deployed language is a proved instance. Everything whose subject is a toy calculus, a private language, a second
judge with its own status type, or a paper's definitions restated is deleted. The steps, one landing each, one Lang
worker at a time (R-0001), each preceded by an IMPACT file read by a cross-family reader:
- S1, S3, S4, S5: pure deletions of the beside-modules (44 modules; S1's `Integration.lean` waits for S1b, which re-homes its two deployed facts to KERNEL/HOST); S2 drops the journey's `p8Data` toy rows first,
  because the journey is S4's only outside consumer;
- S6–S8: the deployed term operations and their proofs leave namespace `Contextual` for `Lang/` and `Lang/Proofs/`
  (`Lang/Index`, `Lang/Subst`, `Lang/HoleDecl`; `Lang/Proofs/{Index,Subst,Fill,HoleBudget,LiveHoles,LiveClosed,
  LawMeaning,LawReceiver,LiveTeeth,LiveJourney}`), statements identical by census digest; `ΔOf`/`holeBound` (a no-op)
  deleted; S8 changes four Kernel/Ledger import lines under CROSS-LAYER (R-0002);
- S9: P7's conformance (refusal constructors, bounds in `Bounds`, one preparation charge, named closed/contextual
  entry points), a `lang!`;
- S10: the all-environment provenance replaces the env-specialized twin; experiment 4's `Rule`/`lfpIter`/`countRun`
  leave `Closure`; S11: `Trace.collect` and its three lemmas move beside `StdHoleModel`, the cache theory is deleted;
  S12: the P6 certificate reader moves to `Census`;
- S13–S15 wait for Ember's rulings R1 (the open-protocol calculus, default delete), R2 (keep `judge` in Lang only with
  a proved live bridge, default build it), R3 (the CMTT core, default delete after S13).

**Per step, the gate that can refute it**: the statement-digest diff of the whole tree's elaborated environment,
before against after, under the step's declared delete/rename map (every vanished name in the delete list, every
surviving name's statement digest equal, every new name in the rename image); the reached build; `gates/check.py`;
the journey after S2/S9; the whole-tree build after S6–S8/S12.

**Erratum: the decision ids of the contextual program.** This file has two `## LANG-72` headings (Boundary
declarations, CX-P2; Alternative worlds, CX-P3), no LANG-71, and LANG-70 (P5/P1, CX-P15) after LANG-73. From this
entry on, the SECOND LANG-72 (Alternative worlds and world-indexed grounding, CX-P3) is cited as **LANG-71**; LANG-70
keeps its number out of order. The card-named entries LANG-P10, LANG-P12, LANG-P11b, LANG-P9, LANG-P11a, LANG-P6,
LANG-P8, LANG-ACT, LANG-P13, both LANG-P7 entries and LANG-PE1 keep their ids, because commit messages cite them; as
to their modules each is superseded by the LANG-74.n step that deletes or rehomes them. The headings above are not
edited: this file is an append-only record, and an old id must stay findable by its old text.

**Alternatives.** (1) A `Research` lean_lib for the breadth cards (review B4 P9): the same twin behind a different
lakefile line, still built by every Lang change and still a second vocabulary. (2) One status type extended with
P5's `refuted`/`outside` and P1's `partial` (review §A2): keeps the toy vocabularies alive; no deployed object needs
them. One status type is reached by deleting the others. (3) Keep the toys as documentation of the theory's
lineage: git keeps them at d7989d9, with their docstrings and literature pointers.

**Critique.** The fold deletes about 590 theorems. None is consumed by a surviving theorem (measured per step), but
several are teeth: concrete executions of the closure's judge on calculi where the general theorem could have been
vacuous. After the fold the spine is exercised concretely by the CMTT instance (until R3), `langLaws`, `HoleBridge`
and the deployed experiments (`P/Deployed`, `P/DeployedCycle`, the journey); if R3 deletes the CMTT core, the only
non-identity instances left are the deployed language's, which is the point but narrows the falsifiers to one
calculus. **Meta-critique.** The map that orders this fold was written from a read of the tree, not a build; its
counts (151 theorems in S1) came from a regex and its reach from `^import` lines. I measured each again on the
elaborated environment before landing, and the regex was off by twelve Prop-structure fields in S1. The bias to name
is trusting a plan's numbers because the plan is careful: every step re-measures on the current tip.

Status: ruled by ROOT 2026-10-21 (R-0001, R-0002); steps land as LANG-74.n.

### LANG-74.1 S1 · thirteen modules with no importer (2026-10-22; CX-FOLD; IMPACT `redregg/work/fold/IMPACT-S1.md`; cross-family read `redregg/work/fold/READ-S1-grok.md`; RELEASE R-0005, GRANT R-0006)

**Decision.** Delete these 13 modules (1,949 lines; 140 theorem constants: 136 `theorem` declarations and the four
fields of the Prop structure `P5.Interfaces.Definition14`), each with its reason (map §2.2):
- D-TOY (`decide` sessions over a toy, next to the general theorem they instance; the deployed experiments are P7's
  `P/Deployed`, `P/DeployedCycle`, `Lang/Journey/Contextual*`): `Lang/Proofs/Contextual/Experiments.lean` (ToyCalc,
  `toyLaws`, the eight experiments), `Lang/Proofs/Contextual/P11bExperiments.lean`,
  `Lang/Proofs/Contextual/ProvenanceExperiments.lean`, `Lang/Proofs/Contextual/RepairExperiments.lean`,
  `Lang/Proofs/Contextual/TraceExamples.lean` + `Lang/Contextual/TraceExamples.lean`,
  `Lang/Proofs/Contextual/AcyclicExamples.lean` + `Lang/Contextual/AcyclicExamples.lean`;
- D-RULES (a second rule semantics beside the closure): `Lang/Proofs/Contextual/WorldsField.lean` (stable worlds =
  labellings for P3's `Worlds`, which S5 deletes; `StableLabelling` is defined in the same file);
- D-JUDGE (second and third judges and their status types): `Lang/Proofs/Contextual/NogoodGameBridge.lean`,
  `Lang/Proofs/Contextual/Interfaces.lean` + `Lang/Contextual/Interfaces.lean` (de Alfaro–Henzinger Definition 14
  restated), `Lang/Proofs/Contextual/P1.lean` (P1's interaction guards with their own `Report`).

Two doc sentences that named deleted modules are rewritten in the same landing: `Lang/Contextual/Closure.lean`:6–8
(the instances are now `cmttLaws` and `langLaws`; it named the toy) and `Lang/Proofs/Contextual/Worlds.lean`:321–322
(it named `WorldsField`). This list is the explicit deletion authorization of this landing (map §5.4).

**Not in this step: `Lang/Proofs/Contextual/Integration.lean`** (map S1's fourteenth). The cross-family read found
that it holds the only statements of two facts about deployed objects: the private `audit_append_to`
(`Kernel.Receive.audit` composes over `++`; `Kernel.Proofs.Fold.fold_append` is about `World.fold`, and `audit_ok`
plus `fold_append` does not state it, there being no `Honest`-append lemma) and `recovery_preserves_consumption` (a
`Host.openWith` from a spent trusted base admits zero further grant movement on any audited future). R-0006: S1b
re-homes a polymorphic `audit_append` in `Kernel/Proofs/Audit.lean` and the recovery theorem with its premise bundle
in a Host proof module; S1c then deletes Integration with its p8 statements and the three aliases of landed theorems
(`one_use_consumption`, `reexecute_committed_effect`, `progress_under_ready_writer`).

**What breaks.** Nothing that survives. Measured over the whole tree's elaborated environment (all 11 libraries)
before and after this candidate: every vanished constant is a constant of the 13 modules; zero surviving constants
change their elaborated type or value hash; zero surviving constants reference a deleted constant (edges by the
exporter's `Census.Journal.expressionEdges`; the same detector reports 76 references for an imported control module).
Lazily realized equation lemmas of the surviving `Closure.countRun` are now realized by another module, with identical
statements. No lakefile target, gates table row, rows fixture, generated file or wire vector names a deleted module.
Re-emit: none. The modules `P/P5`, `P/Nogoods`, `P/NogoodGames` and `P/ProvenanceTeeth` lose their last importers here
and stay built by the glob until S3/S10.
Census digest diff, base 71db964 (Lean tree = 3070fac) against the candidate: 54,249 → 53,699 constants; 550 vanished,
all of the 13 modules; 3 lazily realized `countRun` equation lemmas re-owned with identical statements; 0 new; 0
statement changes; 0 value-hash changes. Whole-tree build of the 11 libraries GREEN at 541 jobs (554 − 13).

**Critique.** `Worlds.Experiment.counting_keeps_cycle_over_worlds` is now the only tooth that immediate-support
counting keeps a withdrawn cycle; S5 deletes it while `Closure.countRun` still exists, so S5 must delete `countRun`
or keep that tooth (S10's plan moves `countRun` out of `Closure`; S5's IMPACT must order the two). **Meta-critique.** A
pure deletion invites a pure-deletion read ("zero importers, done"). My own IMPACT named Integration's two facts and
then defaulted to deleting them, because a re-home was outside this worker's grant: a scope boundary priced as a
reason. The reader refused it. The bias is letting the edge of one's own grant decide what a fact is worth.

Status: landed by CX-FOLD; next S1b (KERNEL/HOST re-home, R-0006), S1c (Integration), then LANG-74.2 (S2).

### LANG-74.1b S1b · the two deployed facts of `Integration.lean` re-homed to KERNEL and HOST before it is deleted (2026-10-22; CX-FOLD; cross-family read `redregg/work/fold/READ-S1-grok.md` ruling (b); GRANT R-0006)

**Decision.** Before S1c deletes `Lang/Proofs/Contextual/Integration.lean`, its two statements about deployed objects
move to the layers that own those objects:
- `Kernel.Receive.audit_append` in `Kernel/Proofs/Audit.lean`: `audit X w pre = .ok mid → audit X mid suffix = .ok
  final → audit X w (pre ++ suffix) = .ok final`, for every `D` with `[Ord D] [DecidableEq D]` and every `X : Ctx D`.
  Integration's private `audit_append_to` stated it at `Host.Deployed.D`/`Host.Deployed.X` only; the proof is the same
  induction on `audit`. It was the tree's only append law for `audit` (`fold_append` is about `World.fold`; `audit_ok`
  relates `audit` to a fold only with `Honest`, which has no append law). Consumer:
  `Host.Deployed.recovery_preserves_consumption`.
- `Host.Deployed.SpentCheckpoint` (the premise bundle: trusted, canonical cells, contiguous ledger, the grant's left
  at 0) and `Host.Deployed.recovery_preserves_consumption` in the new `Host/Proofs/SpentCheckpoint.lean`: a successful
  `Host.openWith` from a spent trusted base, with an audited tail, opens to a trusted World, and the tail followed by
  any audited future moves nothing through the grant. It sits beside `openWith_trusted`, which it composes with
  `Ledger.Proofs.grant_moves_le_cap` (whose other consumers are `Ledger/Proofs/GrantCapTooth.lean`,
  `Ledger/Proofs/EscrowAdmitted.lean` and the certificate pin) through `audit_append`.

**Statements.** Re-homed exactly. Measured in one environment holding both: the new
`recovery_preserves_consumption`, `SpentCheckpoint`, its constructor and its four fields are structurally equal
(`Expr ==`, and equal printed form) to Integration's after renaming the one constant
`Integration.Recovery.SpentCheckpoint` ↦ `Host.Deployed.SpentCheckpoint`; the control comparisons (unrenamed; another
theorem) are false. `audit_append` at `D := Host.Deployed.D`, `X := Host.Deployed.X` proves the old private statement
verbatim (an `example` that elaborates). Generalizing `audit_append` added no premise: the polymorphic statement's
instance binders are the file's `[Ord D] [DecidableEq D]`, which `Host.Deployed.D` has. No landed theorem gains a
hypothesis or changes.

**What breaks.** Nothing. Census digest diff of the whole tree against f665e94: 12 new constants (the two theorems,
the structure and its generated constants), 0 vanished, 0 statement or value-hash changes (one lazily realized
`Lang.Std.lawCase5.eq_1` re-owned, statement identical). `Host/Proofs/SpentCheckpoint.lean` is the first Host module
to import a Ledger module (`Ledger.Proofs.GrantCap`); it is a proof leaf, outside every exe closure, and Ledger
imports no Host module, so no cycle and no deployed closure changes. The two copies in Integration exist until S1c,
the next landing.

**Critique.** `recovery_preserves_consumption` keeps its premise `htail` (the tail has SOME audited history): that is
the re-execution-honesty assumption of the local opener, named, not discharged here; a reopen that audits its tail
would discharge it, and nothing does yet. **Meta-critique.** I priced the re-home as "outside this worker's grant"
and defaulted to deleting the facts; the reader's ruling made it a grant. The bias was treating the edge of the grant
I held as the edge of what the fold should preserve.

Status: landed by CX-FOLD under R-0006; next S1c deletes Integration.lean.

### LANG-74.1c S1c · `Integration.lean`, the fourteenth S1 module (2026-10-22; CX-FOLD; GRANT R-0006 "then S1c = delete Integration.lean")

**Decision.** Delete `Lang/Proofs/Contextual/Integration.lean` (267 lines; 23 theorem constants: 15 `theorem`
declarations and the eight fields of the Prop structures `ReadyWriter` and `Recovery.SpentCheckpoint`). Group D-WRAP
(map §2.2): ten statements over the journey's identity calculus `p8Data`/`p8Iface`/`p8World`/`p8Registry` (whose
rows S2 drops), three aliases of landed theorems (`reexecute_committed_effect := submit_replayed hj`;
`one_use_consumption := grant_moves_le_cap …` with the same premises; `progress_under_ready_writer`, `simp [submit]`
over a structure whose fields are `submit`'s branches), `commitment_binds_receipt` (a conjunction of `submit_ok`,
`receiveWith_sealed`, `sealTurn_ok`, `admit_journaled`, each landed), and the recovery theorem with its private
append lemma, whose statements now live in `Host/Proofs/SpentCheckpoint.lean` and `Kernel/Proofs/Audit.lean`
(LANG-74.1b). This path is the explicit deletion authorization of this landing.

**What breaks.** Nothing that survives. Census digest diff of the whole tree against 82ac944: 45 constants vanish,
all of this module; 0 surviving statements or value hashes change; 0 new; the lazily realized
`Closure.Iface.mk.congr_simp` is re-owned with an identical statement. No surviving module imports it (it had no
importer; the whole-tree build is GREEN at 541 jobs). Re-emit: none. S1 is complete: the map's fourteen modules are
gone, and its two deployed facts are on main in their owners' layers.

**Critique.** `commitment_binds_receipt` goes without a re-home: each conjunct is landed, but the conjunction at the
journey's program is stated nowhere else; nothing consumed it. **Meta-critique.** The reader's (b) ruling covered the
two facts I had flagged; I did not re-ask whether the conjunction deserved the same, because the ruling read as a
complete list. The bias is treating a ruling's enumeration as exhaustive when it answered only what was asked.

Status: landed by CX-FOLD; next LANG-74.2 (S2, the journey's p8 toy rows), after IMPACT-S2 and its RELEASE.

### LANG-74.2 S2 · the journey's p8 toy calculus is dropped; the P8 rows read the live kernel and ROM (2026-10-22; CX-FOLD; IMPACT `redregg/work/fold/IMPACT-S2.md`; cross-family read `redregg/work/fold/READ-S2-grok.md`; RELEASE R-0007; cv task 01a16171-d004 "P8 WITHDRAWAL GAP")

**Decision.** `Lang/Journey.lean` loses its fifth `CalculusData`, the identity calculus `p8Data` (`msubst _ t := t`,
`uses _ _ := false`, `strengthen _ t := t`), and everything built on it: `p8Guard`, `p8Iface`, `p8Candidate`,
`p8Swap`, `p8Correspondence`, `p8Registry`, `p8World`, `p8Available`, and the imports of `Lang.Contextual.Trace`,
`Lang.Contextual.Provenance`, `Lang.Contextual.TransportKinds` (map §2.2 D-WRAP, F4). The P8 rows change:
- `P8.1 old signed plan after unrelated update`: the "trace rejudged" half (`Trace.repair` on the toy) is gone; the
  kernel half (the plan still submits) stays;
- `P8.2 withdrawn instantiation`: "live provenance" (`P9.provenance` over the toy) becomes "live authority", the same
  two booleans read from the kernel view by the new `p8Live` (live, and pinned at the recorded version);
- `P8.2 re-pinned tombstone: conflict guardFails`: DELETED, a mirror (below);
- `P8.2 mismatched live authority pin`: now the REAL commit with the live provider pinned at version 0, refused
  `rejected stale` by the kernel's pin check (plant: the correct pin turns the journey RED (1), `FAIL … admitted`);
- `P8.3 checked representation false -> true; unknownCertificate refused`: DELETED (`TransportKinds.recheck` over the
  toy registry); the index it produced is now the live ROM's own selection, `chooseCode r 1`, row `P8.3 second
  provider selects contextual ROM candidate`;
- `P8 initial authority was live for both candidates`: same text, `p8Live` instead of `p8Available`.
Every other P8 row is byte-identical in the output. The journey is GREEN, 787 lines (789 before).

**The finding the toy rows hid.** Replacing the toy judge's tombstone verdict with the same call through the real
kernel and package gives `admitted`: after provider 0's authority grant is revoked (`live` false), a fresh commit
that pins the grant's tombstone is admitted, the artifact is accepted with provider 0 selected, and the counted unit
is spent (left 0). The causes, read at source: the commit runs `select` over the hole's own fact rows and transfers
via the cap, never reading the provider grant; `pinOf (some .tomb)` is its own digest (`Kernel/World.lean`:342–347),
and `touchCheck` accepts a pin that matches the entry, tombstone included (:995–1003). `p8World`'s docstring ("a
tombstoned grant or a changed pin cannot specialize to true") was true of the toy only. IMPACT-S2 §5, verbatim:

> What is measured: a commit citing a revoked provider authority is admitted when the caller pins the tombstone. What
> I infer [INFERRED]: the P8 composition's "provider authority" is enforced only through the pin set the caller
> chooses to sign; the package's hole reads fact rows (posted supports), and nothing retracts a provider's fact row
> when its grant is revoked. Three shapes for the fix, none of them S2's:
> - (A) the support fact must be retracted (a `withdraw` edit) for the withdrawal to count, and the journey's P8.2
>   should withdraw that way; the grant revoke then is not the withdrawal at all;
> - (B) the package reads the provider's grant cell (a pinned read of a kernel cell by a program: the capability the
>   LANG-P8 critique says fact rows do not have) and refuses a tombstone;
> - (C) the kernel refuses a pin of a tombstone for an id the call also cites as authority (a KERNEL semantics change).
>
> S2 as proposed does not depend on the answer: it deletes the mirror row and asserts nothing about the gap. I will
> open a `cv task` (LANG, P8 withdrawal) with the probe and this section before S2 lands, unless you RULE that the fix
> is part of S2 (then S2 becomes a real row asserting refusal, after the fix). Default: S2 lands as above; the gap is a
> task.

Ruled (R-0007): S2 asserts nothing about the gap in the journey. A row expecting a refusal would be red on every run
and couple the remaining fold steps to an open product choice; a row asserting `admitted` would read as the
requirement. The gap is cv task 01a16171-d004, with the probe.

**What breaks.** Nothing that survives. Census digest diff of the whole tree against 6eb92fe: 17 constants vanish
(the `p8*` toy definitions and six compiler matchers of `p8Rows`), 3 new (`p8Live`, two renumbered matchers); the only
type/value changes are `p8Rows` and its `match_*`/`_sparseCasesOn_*` auxiliaries; 0 theorems change. Whole-tree build
GREEN (618 jobs with `lang-journey`). Re-emit: none; no gates row reads a P8 row text (`gates/runs.tsv`:22 judges the
`lang-journey: GREEN` line).

**Critique.** The P8 journey now says less about withdrawal than it did, and what it said before was false. A reader
of the printed rows sees the withdraw admitted, the old plan stale, live authority `[false, true]`, a bad pin stale,
and no fresh plan against the tombstone: silence that can be read as "withdrawal is the whole story". The task is
where that is answered. **Meta-critique.** The map listed this row among those that vanish and I nearly deleted it as
a toy without running its call for real; the admission appeared only because I replaced each toy row with its real
call before deciding what to keep. The bias is reading "delete the toy" as "the toy's claim was true".

Status: landed by CX-FOLD; next LANG-74.3 (S3).

### LANG-74.3 S3 · P5, the games, the nogoods, the material guards and C/P1 (2026-10-22; CX-FOLD; IMPACT `redregg/work/fold/IMPACT-S3.md`; cross-family read `redregg/work/fold/READ-S3-grok.md`; RELEASE R-0008)

**Decision.** Delete these 11 modules (1,273 lines; 62 theorem constants: 60 `theorem` declarations and the two
fields of the Prop structure `P5.AlternatingSimulation`). Group D-JUDGE (map §2.2, law 1): second, third and fourth
judges with their own status types, beside the closure's `Contextual.judge`/`Status` and the deployed hole judgment.
- `Lang/Contextual/P5.lean` + `Lang/Proofs/Contextual/P5.lean`: `P5.judge` over its own `Problem`/`Refutation`,
  `LogicalStatus`, `Formula`/`Evaluation`, `Machine`/`Refines`/`AlternatingSimulation`, `priceReceiver`;
- `Lang/Contextual/Games.lean` + `Lang/Proofs/Contextual/Games.lean`, `Lang/Contextual/NogoodGames.lean` +
  `Lang/Proofs/Contextual/NogoodGames.lean`: game statuses and certificates over P5;
- `Lang/Contextual/Nogoods.lean` + `Lang/Proofs/Contextual/Nogoods.lean`: `RecordedClosure`, `judgeRecorded`, a second
  judgment beside `Closure.judge`;
- `Lang/Contextual/Material.lean` + `Lang/Proofs/Contextual/Material.lean`, `Lang/Contextual/P1.lean`: the material
  and P1 interaction guards with their own `Report`/`Verdict`.
The eleven are a closed import cluster after S1. This list is the explicit deletion authorization of this landing.

**What breaks.** Nothing that survives. Census digest diff of the whole tree against a9ab514: 1,027 constants vanish,
all of the 11 modules; 0 surviving statement or value-hash changes; 0 new; the lazily realized
`Closure.Iface.mk.congr_simp` is re-owned, statement identical; 0 surviving constants reference a deleted constant.
Whole-tree build GREEN (530 jobs). The open-protocol calculus (R1) loses its importers C/P5 and P/P5 and stands
alone; `ProvenanceRepairs` (def and proof) loses its importers and stays an unimported glob leaf until S4. Re-emit:
none.

**Critique.** `P/P5` held the tree's only alternating-simulation and refinement theory. Its subject is P5's own
`Machine`, not `Protocol.Prot` and not a deployed program, so it is not the refinement notion R1's fork A would need;
that notion, if wanted, is written over `Prot` then. **Meta-critique.** Three steps in, the deletions read as
routine, and routine is when a step's own measurement goes unread: the diff tool still printed "the declared 14
modules" for an eleven-module step, and the reader, not I, noticed. The bias is trusting a tool's label because its
numbers were right last time.

Status: landed by CX-FOLD; next LANG-74.4 (S4).

### LANG-74.4 S4 · the boundary, repair-object, transport, morphism, change and provenance-repair modules (2026-10-22; CX-FOLD; IMPACT `redregg/work/fold/IMPACT-S4.md`; cross-family read `redregg/work/fold/READ-S4-grok.md`; RELEASE R-0009)

**Decision.** Delete these 14 modules (1,747 lines; 109 theorem constants: 102 `theorem` declarations and seven
fields of Prop structures). Group D-PRIVATE (map §2.2): private languages and second shapes of spine concepts.
- `Lang/Contextual/Boundary.lean` + `Lang/Proofs/Contextual/Boundary.lean`: P2's four-constructor search `Term`, "not
  an encoding of deployed Lang terms" (with the review's H2 examples `dependent_inhabitants_change_types`,
  `reuse_cost_bound`, `reuse_cached_observation`);
- `Lang/Contextual/ModalBoundary.lean` + `Lang/Proofs/Contextual/ModalBoundary.lean`: a third syntax over the CMTT core;
- `Lang/Contextual/RepairObjects.lean` + `Lang/Proofs/Contextual/RepairObjects.lean`: the second `Outcome` type, with
  `Policy`, `Registry` and transport;
- `Lang/Contextual/RepairChanges.lean` + `Lang/Proofs/Contextual/RepairChanges.lean`,
  `Lang/Contextual/TransportKinds.lean` + `Lang/Proofs/Contextual/TransportKinds.lean`,
  `Lang/Contextual/ContextMorphisms.lean` + `Lang/Proofs/Contextual/ContextMorphisms.lean`: P11b's paper structures
  over the above;
- `Lang/Contextual/ProvenanceRepairs.lean` + `Lang/Proofs/Contextual/ProvenanceRepairs.lean`: repair plans over
  `RepairObjects`.
The closure's own repair theory stays (`P/Repair`, `P/Outcomes` over the one `Closure.Outcome`, `P/Soundness`). One
docstring sentence in `Lang/Contextual/Trace.lean`:125–126 that named a Boundary declaration is rewritten. This list
is the explicit deletion authorization of this landing.

**What breaks.** Nothing that survives. Census digest diff of the whole tree against e1ccc50: 886 constants vanish,
all of the 14 modules; 0 surviving statement or value-hash changes; 0 new; `Closure.Iface.decl.eq_1` re-owned,
statement identical; 0 surviving constants reference a deleted constant. Whole-tree build GREEN (593 jobs with
`lang-journey`; the journey GREEN). `P/Stability` keeps `P/Worlds` as its only importer until S5. Re-emit: none.

**Critique.** `RepairObjects` held the program's only first-class repair VALUES (composition, identity, a policy
choosing among them); the spine keeps repair as a judge operation, not as data a consumer can carry. Nothing deployed
carries a repair value today, so nothing is lost now; if activities come to need one, it is one `Repair` over the one
`Outcome`, not this module back. **Meta-critique.** The pull at this step was momentum: three clean deletion steps
made the fourth's statement appendix feel like paperwork, and I generated it rather than reading it. Reading
`RepairObjects`' list is what surfaced the critique above. The bias is letting a repeated procedure stand in for the
reading it was built to force.

Status: landed by CX-FOLD; next LANG-74.5 (S5).

### LANG-74.5 S5 · the worlds, the acyclic adapter and stability, with the experiment-4 definitions only they used (2026-10-22; CX-FOLD; IMPACT `redregg/work/fold/IMPACT-S5.md`; cross-family read `redregg/work/fold/READ-S5-grok.md`; RELEASE R-0010)

**Decision.** Delete these 5 modules (819 lines; 45 theorems). Group D-RULES (map §2.2): a second rule semantics
beside the closure.
- `Lang/Contextual/Worlds.lean` + `Lang/Proofs/Contextual/Worlds.lean`: P3's alternative worlds / stable-model rule
  programs with their own `Report`, and the last copies of the counting teeth over them;
- `Lang/Contextual/Acyclic.lean` + `Lang/Proofs/Contextual/Acyclic.lean`: P12's rank-witnessed unrolling adapter with
  its own `Expr`/`Graph`/`Refusal`/`Derives` (`P/DeployedCycle` is the substrate version);
- `Lang/Proofs/Contextual/Stability.lean`: `lfpIter_sound`, `stability_class`, the value-guard facts.
With them go seven spine definitions whose last theorems were in these modules (map S10 scheduled the first four;
the last three were unlisted): `Rule`, `lfpIter`, `supportCount`, `countRun` (the experiment-4 section,
`Lang/Contextual/Closure.lean`:546–566) and the Prop definitions `ValueGuard`, `StableUnder`, `Derives`
(`Lang/Proofs/Contextual/ClosureStatements.lean`:74–85). None is read by `Closure.judge`, `langData`, `LiveHoles`,
`Std.hole`, `HoleBridge`, the journey or the Host. This list is the explicit deletion authorization of this landing.

**The 42 spine constants that vanish, exactly** (the seven definitions and their generated constants; full list
`redregg/work/fold/S5-spine-vanished.txt`):
- `Lang.Contextual.Closure` (28): `Rule`, `Rule._sizeOf_1`, `Rule._sizeOf_inst`, `Rule.body`, `Rule.casesOn`, `Rule.ctorIdx`, `Rule.head`, `Rule.mk`, `Rule.mk._flat_ctor`, `Rule.mk.inj`, `Rule.mk.injEq`, `Rule.mk.noConfusion`, `Rule.mk.sizeOf_spec`, `Rule.noConfusion`, `Rule.noConfusionType`, `Rule.rec`, `Rule.recOn`, `countRun`, `countRun._f`, `countRun._sunfold`, `countRun._unsafe_rec`, `countRun.match_1`, `lfpIter`, `lfpIter._f`, `lfpIter._sunfold`, `lfpIter._unsafe_rec`, `lfpIter.match_1`, `supportCount`;
- `Lang.Proofs.Contextual.ClosureStatements` (14): `Derives`, `Derives.below`, `Derives.below.casesOn`, `Derives.below.fact`, `Derives.below.rec`, `Derives.below.rule`, `Derives.brecOn`, `Derives.casesOn`, `Derives.fact`, `Derives.rec`, `Derives.recOn`, `Derives.rule`, `StableUnder`, `ValueGuard`.
(`countRun.eq_1`/`eq_2`/`eq_def` were realized in `P/Worlds` since S1 and are counted among its 458.)

**What breaks.** Nothing that survives. Census digest diff of the whole tree against a747368: 500 constants vanish,
the 458 of the 5 modules and the 42 above; 0 surviving statement or value-hash changes; 0 new; 0 re-owned; 0
surviving constants referenced the 5 modules. Whole-tree build with `host` and `lang-journey` GREEN (630 jobs); the
journey GREEN. The Host closure loses 21 lines of source (Closure's section), not a module. Re-emit: none.

**Critique.** With `countRun` and the worlds gone, the program no longer states the counting-versus-least-fixpoint
boundary at all (experiment 4): the closure's supports are one level, so the boundary had no subject in the
deployed judge, and P7's grounded cycle (`P/DeployedCycle`) is the substrate's answer. If multi-level supports ever
reach the deployed hole, that experiment is re-asked over the deployed judge, not restored from here.
**Meta-critique.** The map put these seven in a later "tidy" step, and I nearly followed it, which would have left
seven definitions with no theorem for five landings; the reader's S1 note is what made me check. The bias is
treating a plan's step boundaries as dependencies.

Status: landed by CX-FOLD; the pure-deletion phase S1–S5 is complete; next LANG-74.6 (S6).

### LANG-74.6 S6 · the deployed term operations leave `Contextual`: `Lang/Index`, `Lang/Subst`, `Lang/HoleDecl` (2026-10-22; CX-FOLD-2; IMPACT `redregg/work/fold/IMPACT-S6.md`; rename map `redregg/work/fold/S6-renames.tsv`; cross-family read `redregg/work/fold/READ-S6-grok.md`; RELEASE R-0011; cv task 01a16201-ef03)

**Decision.** The code the Host runs no longer lives in the theory directory or its namespace (map F1, F6).

What moved:
- `Lang/Index.lean` (new): `upR`, `liftIdx`, `lowerIdx`, out of `Lang/Contextual/Core.lean`. The CMTT core imports it.
- `Lang/Subst.lean` (new): `Lang/Contextual/LangSubstitution.lean` whole (renaming, substitution) and the term half
  of `Lang/Contextual/LangCalculus.lean`: `Term.decEq*`, `Term.instDecEq`, `usesVar*`, `usesRef*`, `fillRefs*`, and
  `tyOf`, renamed **`holeTy`** (with its lemmas `holeTy_some`/`holeTy_filter`). At `Nanodregg.Lang` it would have
  shadowed `Lang.Wire.tyOf` under `open Lang.Wire`; the first build failed on exactly that at
  `Lang/Proofs/WireTeeth.lean`:80.
- `Lang/HoleDecl.lean` (from `Lang/Contextual/HoleDecl.lean`).
- `Lang/Contextual/LangInstance.lean` (new): `langData` (the tail of `LangCalculus`) and `Lang/Contextual/HoleModel.lean`
  whole. This is the deployed language as a closure calculus, imported by no deployed module.
- `Lang/HoleBudget.lean` stays in its file and leaves namespace `Contextual` (`Term.nodes` stays with the other node
  counts).

All moved names go from `Nanodregg.Lang.Contextual` to `Nanodregg.Lang`, except `langData` and the HoleModel defs,
whose names are unchanged. Old → new is the 45-row rename map. Consumers changed only imports and qualifiers:
`Check`, `HoleROM`, `LiveHoles` (drops `open Contextual`), `Program`:168/214/216, `Journey/ContextualChecks`, `Closure`,
and the proof modules `LawMeaning`, `LawReceiverTeeth`, `LangRenaming`, `LangSubstitution`, `HoleBridge`,
`LangInstance`.

Deleted (D-NOOP; the explicit deletion authorization of this landing): `holeBound`, `ΔOf` and the three lemmas about
them only, `lt_holeBound`, `ΔOf_getElem?`, `ΔOf_nil`. Files deleted: `Lang/Contextual/{HoleDecl,HoleModel,
LangCalculus,LangSubstitution}.lean`.

**What breaks.** Every old spelling `Contextual.Term.*`, `Contextual.HoleDecl`, `Contextual.upR` etc. no longer
resolves. The tree has no remaining user of them.

The Host closure goes from 91 to 89 modules: the CMTT core, the abstract closure and `LangCalculus` leave it. No
deployed module imports `Lang/Contextual/*`.

**Census digest diff against a27b2da under the rename map** (`redregg/work/fold/diff-S6.txt`, full lists, no
truncation):
- No user statement changes.
- 11 declared constants vanish: the five deleted declarations and six of their generated constants.
- 510 constants change module, all from a moved module.
- The rest is ONE CLASS of generated constants, named so that a reader of the digest six weeks out does not take
  it for a statement change.
  - Cause: Lean shares a structurally identical matcher within a module. With `usesVar*`/`fillRefs` now in the file
    that holds `renameVar*`, they reuse `renameVarList.match_1`/`renameVarRow.match_1`/`renameVar.match_1`, and `upR`
    in its own file gets `upR.match_1`.
  - Effect 1: the matchers `fillRefs.match_3`, `usesVarList.match_1` and `usesVarRow.match_1` and their 34 lazily
    realized private equation/splitter lemmas vanish (37).
  - Effect 2: 26 matcher lemmas appear.
  - Effect 3: the **15 equation lemmas** `Term.fillRefs.eq_16/eq_17/eq_def`, `fillRefsList.eq_def`,
    `fillRefsRow.eq_2/eq_def`, `usesRefList.eq_def`, `usesRefRow.eq_2/eq_def`, `usesVarArms.eq_2/eq_def`,
    `usesVarList.eq_def`, `usesVarRow.eq_2/eq_def` and `upR.eq_2` change printed type. They name the shared matcher
    and take its binder names. Their left sides and meaning are unchanged, and no consumer cites them.
  - Effect 4: 36 value hashes change. These are the compiled bodies (`._f`, `._sunfold`, `._unsafe_rec`, `.eq_def`)
    of those functions, `upR`'s own value (its matcher), and the three `HoleDecl` projections, whose `Expr.proj` is
    keyed by the structure name and is not rewritten by the digest tool.

Wire: `codec-vectors --check` is ok, and `--write` regenerates a table byte-identical to `gates/codec-vectors.tsv`
(54 `lang/package/4` vectors among 263). `Term`/`Package`/`Wire` are untouched, hence `lang:`, not `lang!`. Whole tree
with `host`, `lang-journey` and `codec-vectors` GREEN (631 jobs); the journey GREEN. Re-emit: none. Nothing refuses to
load.

**Not here, a GATES card** (cv 01a16201-ef03, R-0011): `gates/size.py`'s "Lean lines (deployed)" still counts every
non-proof module, so `Lang/Contextual/*` is still reported as deployed although no exe closure contains it.

**Critique.** `langData` now sits beside the closure it instantiates, and the Host does not link the theory. But the
proof closures of Kernel/Ledger still reach the CMTT metatheory (`P/Core`, `P/Typing`) through
`P/LangRenaming`'s two `upR` lemmas. That is S7's cut, and until it lands the theory is still on the deployed
proofs' path.

**Meta-critique.** I first wrote the digest diff as an exact-string comparison of printed types. It reported 440
"statement changes" that were hygienic binder names embedding the module path, and I nearly read the result as
"moves are inherently noisy" instead of fixing the comparison. The bias is trusting an instrument's first number
over its semantics. Binder names are not statements; the tool now says so in its code.

Status: landed by CX-FOLD-2; next LANG-74.7 (S7).

### LANG-74.7 S7 · the deployed-subject substitution and filling proofs leave `Contextual`: `Lang/Proofs/{Index,Subst,Fill,HoleBudget}` (2026-10-22; CX-FOLD-2; IMPACT `redregg/work/fold/IMPACT-S7.md`; rename map `redregg/work/fold/S7-renames.tsv`; cross-family read `redregg/work/fold/READ-S7-grok.md`; RELEASE R-0012)

**Decision.** The proofs whose subject is the deployed term operations move out of the theory directory and out of
namespace `Contextual` (`Nanodregg.Lang.Contextual.X` → `Nanodregg.Lang.X`, 101 names):
- `Lang/Proofs/Index.lean` (new): `upR_upR`, `upR_id`, out of `Lang/Proofs/Contextual/Core.lean`. These are the only
  CMTT-core facts the deployed proofs used.
- `Lang/Proofs/Subst.lean`: `Lang/Proofs/Contextual/LangRenaming.lean` + `LangSubstitution.lean`.
- `Lang/Proofs/Fill.lean`: `Lang/Proofs/Contextual/LangFilling.lean` + `LangOccurrences.lean`.
- `Lang/Proofs/HoleBudget.lean`: `Lang/Proofs/Contextual/HoleBudget.lean`.

The five old files are deleted, their text moved byte-identical; this list is the deletion authorization. Consumers
changed only imports: `P/LangInstance`, `P/LiveHoles`. `P/LiveHoles`, `P/LiveCost` and `P/Deployed` drop `open
Contextual`, a namespace no longer declared in their closure. No declaration is deleted.

**What breaks.** The old `Contextual.`-qualified names of the 101 no longer resolve; nothing in the tree uses them.
The proof closures of `Kernel/Proofs/InvokeWitness` (97 → 94 modules), `Kernel/Proofs/Logic/History` (123 → 120) and
`Ledger/Proofs/EscrowRun` (141 → 138) no longer contain the CMTT core (`C/Core`, `P/Core`, `P/Typing`). Only the
spine reaches it now (`P/CoreInstance`, `C/CoreCalculus`, `P/ProvenanceTeeth`), pending S10/S15.

**Census digest diff against d3e850d under the rename map** (`redregg/work/fold/diff-S7.txt`): no user statement
changes; 0 declared deletions; 581 module changes, all out of the six edited modules. The residual has two named
causes:
- **Auxiliary-proof renumbering** in `Term.shiftAt_unshiftAt`, `hasType_unshiftAt_live` and `usesVar_shiftAt`. Their
  abstracted sub-proofs `._proof_1_k` are renumbered: 4 vanish, 4 appear, and the reused name `._proof_1_2` makes 2
  type-digest lines.
  - Their proof values cite the new names: 5 value lines.
  - The three statements are unchanged, and each theorem's multiset of auxiliary statements is equal before and
    after.
  - A `._proof_N` is a name for a sub-term of the proof, not a hypothesis.
- **The S6 generated matcher class.** 22 private `renameVar`/`renameVarList` matcher lemmas `P/HoleBudget` no longer
  re-realizes; 3 private `upR.match_1` lemmas; and `upR.eq_1/eq_2`, `liftIdx.eq_1`, `lowerIdx.eq_1` are now realized in
  `Lang.Proofs.Subst`.

Whole tree with `host` and `lang-journey` GREEN (627 jobs); the journey GREEN. Re-emit: none; no deployed module,
wire byte or table changes.

**Critique.** `Lang/Proofs/Subst.lean` is 560 lines: renaming then substitution. That is one concept by the map's
rule, but over law 8's comfort; it is a candidate to split by responsibility (renaming/strengthening vs substitution)
if it grows.

**Meta-critique.** I treated the digest's TYPE list as the verdict and only afterwards asked what a `._proof_1_2`
denotes. The reader had to confirm the renumbering account from the patch, because my artifact listed names, not
the auxiliaries' statements. The bias is publishing the conclusion without the comparison that supports it. S8's
diff will print the auxiliary-statement check itself.

Status: landed by CX-FOLD-2; next LANG-74.8 (S8, CROSS-LAYER: the four Kernel/Ledger import lines).

### LANG-74.8 S8 · the live, closed and law-receiver proofs leave `Contextual` (2026-10-22; CX-FOLD-2; IMPACT `redregg/work/fold/IMPACT-S8.md`; rename map `redregg/work/fold/S8-renames.tsv`; cross-family read `redregg/work/fold/READ-S8-grok.md`; RELEASE R-0013; CROSS-LAYER KERNEL, LEDGER: import lines only, GRANT R-0002)

**Decision.** The proofs whose subject is the live loader, the closed specialization, the law receiver and the
installed ROM move to `Lang/Proofs/` as eight modules. Each source keeps its own `section`, so its `open`s and
`variable`s keep their scope.
- `Lang/Proofs/LiveHoles.lean`: `P/LiveHoles` + `P/LiveCost`.
- `Lang/Proofs/LiveInvoke.lean`: `P/LiveInvoke`.
- `Lang/Proofs/LiveNeed.lean`: `P/LiveNeed`.
- `Lang/Proofs/LiveClosed.lean`: `P/ClosedDeployment` + `P/ClosedLeaf`.
- `Lang/Proofs/LawMeaning.lean`, `Lang/Proofs/LawReceiver.lean`.
- `Lang/Proofs/LiveTeeth.lean`: `P/ContractTeeth` + `P/LawReceiverTeeth`. ContractTeeth now imports
  `Lang.Proofs.Fill`, not the spine's `P/LangInstance`, and its 8 teeth leave namespace `Contextual`.
- `Lang/Proofs/LiveJourney.lean`: `P/Deployed` + `P/DeployedCycle`.

The 12 old files are deleted; this list is the deletion authorization.

**Two deviations from the map's grouping, each measured:**
- `LiveNeed` stays separate. Merged into `LiveHoles` it is an import cycle: LiveNeed → NeedComplete → Need → Extract
  → Provenance → the live-hole facts.
- `LiveInvoke` stays separate. Merged, it would put `Lang.Proofs.Invoke` and `Lang.Proofs.Read` into
  `Kernel/Proofs/InvokeWitness`'s closure (94 → 95) for two theorems only `Lang.Proofs.Provenance` uses. Separate,
  that closure goes 94 → 93.

**CROSS-LAYER, the only edits outside Lang:**
- `Kernel/Proofs/InvokeWitness.lean`:38: `import Lang.Proofs.LiveClosed`.
- `Kernel/Proofs/Logic/History.lean`:51: `import Lang.Proofs.LawReceiver`.
- `Ledger/Proofs/EscrowRun.lean`:59–60: `import Lang.Proofs.LiveClosed` and `import Lang.Proofs.LawReceiver`.

The theorems those files use were already in `Nanodregg.Lang`, so their digests are unchanged. After S8 the Kernel
and Ledger proof closures reach no `Contextual` module. `Lang/Proofs/Contextual/` holds only the spine, the CMTT
core (R3) and the protocol modules (R1).

**What breaks.** The old module paths no longer exist, and the Contextual-qualified names of ContractTeeth's 8 teeth
no longer resolve. Nothing in the tree uses either.

Census digest diff against 3944bbf under the rename map (`redregg/work/fold/diff-S8.txt`): 0 type changes, 0 new
constants; 3 generated constants vanish. The one user value change is `foldMax_member`: its nil-case `simp`
now cites the merged module's same-statement auxiliary `loadAllUsing_inv._simp_3` instead of emitting its own
`_simp_1_1`. Its statement is unchanged. The rest is generated: the shared `selectHole` matcher splitters, and the
doubly realized `Need.runBy` equation lemmas, whose recorded module follows import order.

Whole tree with `host` and `lang-journey` GREEN (623 jobs); the journey GREEN. Re-emit: none. Nothing refuses to
load.

**Critique.** `Lang/Proofs/LiveHoles.lean` and `LiveClosed.lean` carry `section` wrappers whose only job is to keep
two sources' scopes apart. The honest follow-up is to make the two halves share one `open`/`variable` header where
they agree. That is a text tidy, not a move, and it is not in this step.

**Meta-critique.** I executed the map's grouping as written and found two of its merges wrong only by building and
by diffing closures. The map's groups were INFERRED and I treated them as a spec. The bias is reading a plan's
labels as measurements; the closure diff now runs before I call a move done.

Status: landed by CX-FOLD-2; next LANG-74.9 (S9, the `lang!` conformance card).

### LANG-74.9 S9 · the P7 conformance card: preparation refusals are constructors, the hole bounds are named, one preparation charge, the hole signature is always stated (2026-10-22; CX-FOLD-2 designed, CX-FOLD-3 built; IMPACT `redregg/work/fold/IMPACT-S9.md` (section BUILT); cross-family reads `redregg/work/fold/READ-S9-grok.md` and `redregg/work/fold/READ-S9-built-grok.md`; RELEASE R-0014 under five conditions, RELEASE R-0016 of the built diff)

**Decision.** The live contextual preparation stops speaking `String`.
- `Lang/LiveHoles.lean` gets `inductive HoleRefusal` (21 constructors) and one printer `HoleRefusal.wire`.
  `HoleROM.check`, `Package.checkContextual`, `holeRow`, `changedHypotheses`, `runHoleGuard`, `selectHole`,
  `instantiateHoles`, `unresolvedBody` and `admitContextual`'s `prepare` return `Except HoleRefusal`.
  `HoleResolution.blocked` carries a `HoleRefusal`; its body is `.refuse T why.wire.toUTF8`.
- `Lang/HoleBudget.lean` gets `inductive ExpansionBound | work | size`; `Term.fillBounded` returns
  `Except ExpansionBound`, reaching `HoleRefusal.expansion` by an explicit `match` at its two callers.
- `Lang.Bounds` gets `holeCandidatesMax = 64`, `holeSignatureMax = 16` and ONE `holeGuardFuel = 256`. That one field
  is the guard's `run` fuel and the per-hole coefficient of the charge. It is not `reasonMax` or `docMax`, which are
  other facts that are also 256.
- `Package.holeCharge p m` is the one charge formula. The actual cost is it at `m = resolutionMax rs`; the static
  `Package.preparationCost` is it at the fold over every committed candidate. Both folds keep their floor of 1. Same
  formula, not the same number: `instantiateHoles_cost` is still `≤`.
- The seven `(Ω : HoleSignature := [])` defaults are gone from `inferE`, `inferFields`, `inferArms`, `inferSubst`,
  `infer`, `checkE`, `check`. Every caller names its signature; a closed call is written `(Ω := [])`. No second
  checker name.

**The reachable arm.** `instantiateHoles`' closed re-check keeps its own constructor `instanceRecheck`, whose wire is
the bare `holeInstanceType` it printed before; `admitContextual`'s re-check is `instanceType e`
(`holeInstanceType {e.text}`). The design (IMPACT §1) wanted to fold them, calling the first arm unreachable. It is
reachable: a ROM hole name is an unbounded `Nat`, a blocked hole's refusal text carries it, and past
`Bounds.reasonMax` that text makes the filled `.refuse` ill-typed. The plant `recheck-arm-reachable`
(`--contextual-checks`) drives a hole named `10^300` there and expects `.instanceRecheck`, with name 0 as the
control. With the arm mutated to `.instanceType e` the row is FAIL and the run RED.

**What stays a string (no widening).** `Print.contextualText`'s refusals, `StdContextualHole`'s generator
refusals (its two `checkContextual` calls map through `HoleRefusal.wire`), the machine's `holeUnresolved`, the
budget's `holeTicks`, the journey's `resultName`/`refusedBy` rows (they read the wire, and are the gate that it did
not move), and the `admission-prepared-type` prefix check on `Refusal.program`.

**Statements re-spelled, measured.** Census digest diff ac34521 → candidate: 27 user theorems change type, all in
IMPACT §3's list of 33. Each change is a token substitution (`redregg/work/fold/S9-typediff.txt`): `String` →
`HoleRefusal` (`ExpansionBound` for `fillBounded_bounds`); `why` → `why.wire` in `blocked_step` and
`resolveHole_refusal`; `"holeSupportMoved 0 1"` → `.supportMoved 0 1` in `used_hypothesis_suspends`; `256` →
`Bounds.holeGuardFuel` in `runHoleGuard_cost`. **No landed theorem gains a hypothesis**: 0 binders added in any of
the 27. Kernel, Ledger and Host: 0 type changes and no source edit; `object_history_start`'s proof term changes
only because it instantiates `loadContextual_top`. The Ω edit changes no theorem type. The two vanished constants are
`_simp` auxiliaries of re-proved theorems; the other type changes are the definitions above and their generated
matchers, equation lemmas and splitters.

The six of IMPACT §3's 33 that do not move: `resolutionMax_committed` (two `Nat`s; the blocked reason is not in
its statement), `loadLive_checked`, `loadLive_libTy`, `loadLive_of_load`, `method_live_run_sound`,
`invoke_live_never_stuck` (`loadLive`'s type is `Except (Refusal D)` and did not change). They were listed because
the design's census followed `loadLive`/`resolveHole`; none of their statements mentions the refusal string or the
literal. The first four change proof value only; the last two change neither.

**Wire.** No byte moves. `lang-journey` and `--contextual` output byte-identical to ac34521's;
`--contextual-checks` identical except the new plant row; `codec-vectors` check ok and write byte-identical.

What locks the bytes is the executing journey rows that still compare strings (`holeSelectionAbsent 0`,
`holeUnpinned`, `holeGuardBlocked 0`, `holeSupportMoved 0 1`, `holeDerivationMoved 0`, `holeTicks`), unchanged by
this step. The constructor rows, the new plant among them, compare values, not `wire`; the codec vectors carry no
refusal text and are only the control. The bare `holeInstanceType` of `instanceRecheck` has no exact byte row (the
`admission-prepared-type` row is a prefix check of the with-text spelling): a printer edit that kept the constructor
and changed that string would stay green. That is the gap named in the critique.

**What breaks.** `Except String` → `Except HoleRefusal` on the nine preparation functions; `fillBounded` →
`Except ExpansionBound`; the checker's `Ω` is required; a caller that matched refusal strings matches constructors.
In-tree callers are all updated. Re-emit: none. Nothing refuses to load.

**Critique.** `HoleRefusal.wire` reprints today's strings by construction, and the only check that it does is that
the journey reads the same bytes. A theorem `wire` is injective, or at least that the 21 prefixes are distinct, would
make the "constructor ⇔ bytes" claim a fact rather than an observation. Not in this step.

**Meta-critique.** The design called the re-check arm unreachable because a theorem about the success direction
existed nearby. I read the presence of a typing theorem as a proof of absence. The cross-family reader found the
witness in a bound nobody had joined to the hole name; the bias is trusting a neighbouring theorem's name for the
claim it does not make.

Status: landed by CX-FOLD-3; next LANG-74.10 (S10, the provenance twin).

### LANG-74.10 S10 · the provenance twin: P9's all-environment `provenance` is THE provenance (2026-10-22; CX-FOLD-3; IMPACT `redregg/work/fold/IMPACT-S10.md`; rename map `redregg/work/fold/S10-renames.tsv`; cross-family read `redregg/work/fold/READ-S10-grok.md`; RELEASE R-0018, choice (a))

**Decision.** The spine had two provenance polynomials. The env-specialized one (`Closure.provenance I env cs`,
guard and budget evaluated at one environment) and its `provenance_iff` (`P/Judge`) are deleted, with the tooth that
refuted it (`P/ProvenanceTeeth`, `provenance_env_specialized`). P9's polynomial, which keeps the guard and the budget as
literals and answers at every world, is now `Contextual.provenance`: its definitions (`EnvLit`, `Monomial`,
`monomial`, `provenance`, `Monomial.consistent`, `Monomial.subsumes`, `minimal`, `label`) move verbatim from
`Lang/Contextual/Provenance.lean` (deleted) into `Lang/Contextual/Closure.lean` at the twin's place, and
`Lang/Proofs/Contextual/Provenance.lean` leaves namespace `P9`. `P9.provenance_iff` is now `Contextual.provenance_iff`.
`Monomial.holds` (only the twin's theorem used it) is deleted.

Choice (a), ruled: `specialize`, `specialize_eq` and `provenance_update` (Prop15: specializing P9's polynomial
recovers the twin) are deleted. Their statements named the deleted definition; restating them with the twin's body
inline would keep the twin under no name.

`tm_decEq_toy` drops its reflexive conjunct `Tm.mvar 3 [...] = Tm.mvar 3 [...]`; the inequality is unchanged.

**Measured** (census digest diff against 6c31cab under the map, `redregg/work/fold/diff-S10.txt`): 10 declared
constants vanish (plus the twin's 5 rows, listed in `fold/S10-twin-rows.txt`); 0 new; 72 module changes, all
`Lang.Contextual.Provenance` → `Lang.Contextual.Closure`. Type changes: `tm_decEq_toy` (the conjunct), and 20 that are
the implicit binder order `{D} {E}` → `{E} {D}`: each before/after type string has the same token multiset. The moved
definitions now follow `Closure.lean`'s `variable {E}` … `variable {D}` order, the order of `judge` and `effSupports`.
No binder is added. Nothing outside the provenance files and `Core.lean` changes. Whole tree with `host`,
`lang-journey`, `codec-vectors` GREEN; journey byte-identical; theorems 6078 → 6074.

**What breaks.** `Lang/Contextual/Provenance.lean`, `Lang/Proofs/Contextual/ProvenanceTeeth.lean` no longer exist;
`Contextual.P9.*` no longer resolves; `Contextual.provenance`/`provenance_iff` now name the all-environment objects;
`Monomial.holds`, `specialize`, `specialize_eq`, `provenance_update` are gone; the moved definitions take `{E} {D}`.
Nothing in the tree uses the old shapes. Re-emit: none. Nothing refuses to load.

**Critique.** The binder-order change is a side effect of where the definitions landed, not a decision about the
API. It matches the file, but it is twenty digest lines a reader had to classify. Inserting the block under its own
`variable {D} {E}` section would have kept the digest quiet; matching the host file's order is the better final shape.

**Meta-critique.** I kept the twin's theorem names for the survivors because the map said so, and that makes
`Contextual.provenance_iff` mean something different from yesterday under the same name. The bias is treating a name
as owned by whoever holds it last; the decision text is the only place the change of meaning is findable.

Status: landed by CX-FOLD-3; next LANG-74.11 (S11, the Trace split).

### LANG-74.11 S11 · the Trace split: `collect` joins the generated hole's model; the rest of P10's trace is deleted (2026-10-22; CX-FOLD-3; IMPACT `redregg/work/fold/IMPACT-S11.md`; rename map `redregg/work/fold/S11-renames.tsv`; cross-family read `redregg/work/fold/READ-S11-grok.md`; RELEASE R-0019)

**Decision.** `Contextual.Trace.collect`, the 8-line complete collector the generated hole's coverage check uses, moves
verbatim to `Lang/StdHoleModel.lean` as `Nanodregg.Lang.Std.collect`, beside its one user `holeCoverageOutcome`. Its
three lemmas (`collect_sound`, `collect_total`, `collect_missing`) move verbatim to `Lang/Proofs/StdHoleCoverage.lean`.
`Lang/Contextual/Trace.lean` and `Lang/Proofs/Contextual/Trace.lean` are deleted (this is the deletion
authorization): P10's guard/snapshot/cache/repair model of the abstract closure, whose consumers left in S1 and S2.

The 17 deleted theorems: `seed_valid`, `refresh_valid`, `refresh_consistent`, `repair_entries`,
`from_scratch_consistency`, `repair_minimal`, `repair_once`, `early_cutoff`, `repair_valid`, `capture_sound`,
`checkedJudge_sound`, `checkedJudge_total`, `changed_iff`, `tagged_filter`, `evaluate_observe`, `guard_reads_only`,
`observation_complete`. None is the only statement about the generated hole, the activity, the journey or the live
path.

**Measured** (census digest diff against 4f5f18b's tree under the map, `redregg/work/fold/diff-S11.txt`): 184 constants
vanish, all declared; 0 type changes; one value change, `Std.collect.eq_def`, which cites the matcher of the module
that realizes it; 9 generated private matcher lemmas of `collect` re-created under the new module's private prefix.
No `lean_exe` import closure changes. Whole tree GREEN; the three journey modes byte-identical; theorems 6074 → 6057.

**What breaks.** The two Trace modules no longer exist; `Contextual.Trace.*` no longer resolves; `collect` and its
lemmas are `Nanodregg.Lang.Std.*`. Re-emit: none. Nothing refuses to load.

**Critique.** The three lemmas now have no consumer: they are kept as the specification of a deployed function, and
`holeCoverageOutcome_ok_iff` still proves its own fact by enumerating eight cases instead of citing them.
Connecting the two is a small proof, not part of a move.

**Meta-critique.** I measured the 17 against the map's list and stopped there. The bias is reading agreement with the
plan as evidence; the evidence is the census VANISHED list and the empty consumer grep, which agree.

Status: landed by CX-FOLD-3; next LANG-74.12 (S12, the certificate reader to Census).

### LANG-74.12 S12 · the P6 certificate reader leaves Lang for Census (2026-10-22; CX-FOLD-3; IMPACT `redregg/work/fold/IMPACT-S12.md`; rename map `redregg/work/fold/S12-renames.tsv`; cross-family read `redregg/work/fold/READ-S12-grok.md`; GRANT R-0015 (Census/**, lakefile.lean; CROSS-LAYER: GATES), GRANT R-0017 (devtools/certificate_plants.py, two strings; CROSS-LAYER: CLIENT); RELEASE R-0020)

**Decision.** The certificate reader is Census tooling ("a data/reader interface, not nano admission"), and every
consumer is in Census. Four files move verbatim, namespace `Nanodregg.Lang.Contextual.Certificate` →
`Census.CertificateReader`:
- `Lang/Contextual/Certificate.lean` → `Census/CertificateReader.lean`;
- `Lang/Proofs/Contextual/Certificate.lean` → `Census/Proofs/CertificateReader.lean`;
- `Lang/Journey/Certificate.lean` → `Census/CertificateReaderTests.lean`;
- `Lang/Journey/CertificateMain.lean` → `Census/CertificateReaderMain.lean` (the `certificate-tests` root; the lakefile
  entry follows, the exe name and its `gates/runs.tsv` row are unchanged).

The four Lang paths are deleted (this is the deletion authorization). `Census/{Certificate,CertificateData}` and
`Census/Proofs/Certificate` change qualified names and imports only. `devtools/certificate_plants.py` changes the
two strings that name the moved source and its build target; no plant logic changes.

**Measured.** Census digest diff under the map (`redregg/work/fold/diff-S12.txt`): 0 type changes, 0 deletions; the
value changes are structure projections (their `Expr.proj` carries the structure name), `Refusal.noConfusion`,
`instReprRefusal.repr` and `Tests.run` (printed names); a derived private instance is renamed
`instDecidableEqExcept_lang` → `_census` by Lean after the root namespace. `certificate-tests`: the same 15 PASS and
GREEN; its harness control still fails on the same row, the message differing only in the constructor's qualified
name. `gates/certificate.py` re-emits the certificate of `Nanodregg.Ledger.Proofs.grant_moves_le_cap` (6,857
declarations) and matches the untouched pinned vector. The plant driver (`devtools/certificate_plants.py`) on the
candidate, with its log directory pointed at scratch: the control goes RED by name, each of the 8 plants (7 guards
replaced by `if False then`, plus the missing-target branch) builds and goes RED with `actual Except.ok ()`, and the
restored source is GREEN. Whole tree with `certificate-tests` GREEN.

**What breaks.** `Nanodregg.Lang.Contextual.Certificate.*` no longer resolves (`Census.CertificateReader.*`); the four
Lang paths no longer exist. Re-emit: none (the 12 MB golden is untouched; its re-pin is cv 01a16131-5868). Nothing
refuses to load.

**Finding, not fixed here.** The plant driver writes `CX-P6-*.log` and `CX-P6-plants.pid` into the shared
`/tank/dregg-build/nanodregg/logs/`, so a run overwrites the previous run's evidence. That is CLIENT's file and not in
R-0017's two strings.

**Critique.** `Census.Certificate` (the command and adapter) and `Census.CertificateReader` (the generic reader) are
now two namespaces in one directory whose names differ by a suffix. They are different things, but a reader has to
learn that from the files.

**Meta-critique.** I priced the move by grep and found the CLIENT path only because I grepped beyond the map's
consumer list. The bias is trusting a list of consumers that was written for Lean files to cover the scripts that
name those files by path.

Status: landed by CX-FOLD-3. The consolidation S1–S12 is complete; S13–S15 wait for Ember's rulings R1–R3.

## LANG-75 The promotion program: the toy contextual theory is promoted into deployed nano, card by card (2026-10-22; CX-PROMO; plan `redregg/work/PROGRAM-20261022.md` approved by Ember; rulings R-0024 RELEASE, R-0025 GRANT)

**Decision.** Ember (real 10-22): "PROMOTE the toy instances into actually deployed aspects of the exact nanodregg
system … a more powerful repair-capable, contextual, open/still-analyzable system." The program's cards, each an
IMPACT file → a cross-family read → a RELEASE row → one landing, one Lang worker at a time:
- P1: E1 the cross-object read and C1 support pins on kernel cells (one `lang!`, LANG-75.1); C9 use-once grants as
  revocable certificates; the charter's scope item 3 rewritten (the writer model).
- P2: the live bridge at the kernel's World (C2, after its two-hour statement measurement), the CMTT core deleted
  (R3, R-0022), repair over `resolveHole` (C5), provenance over live selections (C4a), the live label (C3), acyclicity
  over the pin graph (C7, only with its plant), the boundary docstring (C6).
- P3–P6: the protocol promotion (PROT-1..8 with E2–E4), the mini specs (M1, M2), receipts between Worlds (E5),
  replicated agreement (E7, offered and priced; started on Ember's word). E8 (merging divergent histories) is refused.
Each card says what nano object it promotes, which landed theorem gains a hypothesis (the premise price; a binder is
not one), and the deployed mutation that makes each new theorem false.

### LANG-75.1 E1 + C1 · a fact read is a live read: the kernel cell a fact names must be live, read through the caller's pins, in the same Turn (2026-10-22; CX-PROMO; IMPACT `redregg/work/promo/IMPACT-E1.md`; probes `redregg/work/promo/E1-support-probe.txt`; cross-family read `redregg/work/promo/READ-E1-grok.md`; GRANT R-0026 (cross-layer), RELEASE R-0027 under three conditions; cv 01a16171-d004, 01a1649d-d708, 01a1649e-7c2d, 01a16502-c55e item 1; LANG-21 01a14805-3d00 closed by name)

**The defect, measured before the design** (`E1-support-probe.txt`, through the real `Receive.submit` and the installed
Std.hole package at f8d04ac). (a) A fact naming a cell the kernel never had, at an arbitrary pin, was admitted by
`post`; a candidate citing it was recorded `verified`; `select` admitted; P8's `commit` admitted and spent the one
counted unit to it. (b) After provider 0's grant was revoked, a commit that pinned the grant at its TOMBSTONE was
admitted and spent the unit (the S2 probe, re-measured). Revoke then unpost, as two calls, made the next commit refuse
`support0 withdrawn`; revoke and unpost in ONE call is not constructible (`Unsigned` carries one `Body`; a method's
calls are made as the object, and the grant's issuer is the member). So the poster-withdraws shape (REOR D.1, "A")
leaves the gap reachable by any client that revokes without unposting; the plan's §8.3 refuter did not refute, and
shape B stands: the reader checks the cell.

**What lands.**
- **One liveness.** `cellLive look g` (Lang/Rel): the caller pinned `g` and the World holds a live cell there
  (`pinned` returns `World.live`, `none` at a tombstone or absence). Never "at a version": a grant's slots move on
  every spend (KERNEL-60), and the authority's other tests stay `spendVia_ok`'s.
- **The live column (E1; READ-E1 R3 replaces the plan's `Package.cites` + `cited` relation).** A method's read of a
  relation keyed by exactly one digest (`RelDecl.cellKeyed`) may declare `live` (`RelRead.live`; surface
  `(reads REL (points N) (live))`): each point's record is `{key, live, val}` (`pointRecTy`), and the runtime fills
  `live` from `cellLive look g` for the cell its key names (`pointData`, after `readPoint`). An unpinned cell is the
  kernel's own `unpinned` refusal. The column is not in `editTy`: no method can type an edit of it, and the runtime
  passes the rows argument itself. A `(live)` read of a relation that is not cell-keyed is refused at install by its
  own name, `liveNotCellKeyed` (READ-E1 condition 1). `readsData`/`relReads` take `look`; both the closed and the live
  setup read rows the same way, so `runMeasuredLive_leaf_closed` keeps its statement.
- **C1 in Std.hole.** `facts` (keyed by `cell : digest`) is read live by every generated method that judges
  (accept, fill, propose, prune, rejudge, select; P8's commit through select). The probe reads absent 0, same pin at a
  LIVE cell 1, moved 2, same pin at a dead cell 3; the verdicts gain `support0Dead`/`support1Dead`, recorded
  `suspended "support0 dead"` and refused `support0 dead`. `holePosted` is unchanged: a fact stays the poster's claim
  (`hole_postArg g pin`); every reader now checks the cell it names.
- **The ROM grain.** `SupportPin` (`.row rel key ver | .cell id`) replaces `HolePin` in a `HoleROM`'s supports,
  hypotheses and guard pin. A cell support must be pinned (`unpinned`) and live (`HoleRefusal.supportDead`, wire
  `holeSupportDead N`); an unpinned ROW support stays `derivationMoved` (R1, today's behaviour). `selectHole`,
  `changedHypotheses`, `runHoleGuard`, `resolveHole`, `instantiateHoles` take `digestOf look`; `loadLive` already held
  `look` and passes it. `checkROMLits` checks every cell id a ROM names is a digest of the World.

**Theorems** (each with the deployed mutation that makes it false; plants below):
- `cellLive_iff` (Proofs/Rel) — mutation `cellLive := true` (plant a).
- `cited_authenticated` (Proofs/Rel; sibling of `holeRow_authenticated`): on a live read, slot j is the caller's
  j-th pinned point, its key read back from the pinned bytes, its `live` bit `cellLive look g` for the cell that key
  names — mutation: `pointData` writes `live := true` without the `look` read (plant b; `pointData_ok` and this fail).
- `selectHole_cell_support` (Proofs/LiveHoles) — mutation `supportLive (.cell _) := true` (plant a2; this fails while
  `selectHole_origin`'s new conclusion still holds, which is why it is a separate theorem).
- `revoked_support_refused` (ROM: a selection row picking a candidate that cites a cell pinned at its tombstone gives
  no selection, a blocked resolution, no receipt) and `revoked_support_refused_hole` (Std.hole: such a fact probes 3
  and the admission is `support0 dead` whatever the other support observes). Stated over the deployed read and the
  deployed judge, not over `receive` (R2): the through-`submit` evidence is the journey row P8.2.
- `posted_support_checked` (Proofs/StdHoleCells): a support the generated probe reads as current names a fact at the
  support's cell and pin AND, with the runtime's bit, a cell the caller's pinned view holds live — mutation: the probe
  ignores `live` (plant c).
- teeth, named and decided: `hole_probe_dead`, `hole_probe_dead_moved`, `cell_support_live_selects`,
  `cell_support_dead_refused`, `cell_support_unpinned_refused`, `live_read_not_cell_keyed_refused` and its control
  `live_read_cell_keyed_admitted`; `readPoint_ok`, `pointData_ok`, `mapM_ok_getElem`, `holePointObservation_current`.
- None is a disjunct; none has an unbounded `∃ a b, a ≠ b ∧ h a = h b`.

**Premise price, MEASURED** (census digest diff under `promo/E1-renames.tsv`, `promo/diff-E1.txt`; top-level
hypothesis count old vs new over every changed theorem, `promo/hyps-E1.txt`): no user theorem gains a hypothesis
(127 same, the only "gained" are three generated `relReads.match_1.eq_3` matcher equations). The statement changes:
- binders `digestOf look`: `selectHole_origin`, `resolveHole_refusal`, `instantiateHoles_typed`,
  `instantiateHoles_sources`, `runHoleGuard_cost`, `selectHole_nodes`, `resolutionMax_committed`,
  `instantiateHoles_cost` (the plan's `loadLive_libTy`/`loadLive_checked` were already over `look` and did not change);
- binder `look`: `runSetup_spec`, `runSetupWith_spec`, `runMeasured_means`, `invoke_never_stuck`,
  `invoke_live_never_stuck`, `readsData_conforms`, `relReads_conforms`, `readsData_digests`, `relReads_digests`,
  `relReads_points` (its private `pinD` now carries the live column), `relReads_pins_past_slots`,
  `relReads_points_witness`, and Ledger's private `setup_eq`/`hw0` (CROSS-LAYER: LEDGER, proof only);
- MEANING: `selectHole_origin`'s conclusion `c.supports.all (supportLive …)` covers cells (on row supports it is the old
  `holePinHolds`; its one consumer `resolutionMax_committed` uses only the body conjunct);
- a weaker PREMISE, never a stronger one: `holeVerdictCheck_{application,meaning,admits_iff,evaluated_iff}`,
  `holeStatusOf_{application,meaning}`, `holeCheckedAdmission_evaluated_iff` take `l` in a list of nine labels (was
  seven); `HoleBridge.holeDecision_label`'s conclusion lists nine (forced: the function can now return the two);
- data: the probe teeth's point data gains `live`; the Wire version theorems carry `lang/package-version/5`;
  `DeployedContextual.*` (8) apply `selectHole` to `Kernel.Sim.digestOf noCells`.
Renamed (`E1-renames.tsv`): `HolePin` → `SupportPin` (`.mk` → `.row`; its projections go), `holePinHolds` →
`supportLive`, `Wire.holePin*`/`holeOptPin*` → `supportPin*`/`supportOptPin*` (and the four `Proofs/Wire` round-trip
theorems), `Print.holePinSx`/`holeOptPinSx`, `Read.holePin`/`holeOptPin` likewise. Every other vanished or new constant
is generated (matchers, `_sparseCasesOn`, equation lemmas, hygienic names): listed in `diff-E1.txt`.

**Plants, each a temporary edit, the journey exe rebuilt under it, whole output read, then restored and GREEN again**
(`promo/E1-plants/`):
- (a) `cellLive := true`: RED `P8.2 re-pinned tombstone` (admitted), `LH14b` (recorded verified, select admitted),
  `LP cell-support-dead`; `cellLive_iff` and `selectHole_cell_support` fail; `LH14a` stays green.
- (a2) `supportLive (.cell _) := true` only: RED `LP cell-support-dead`; `selectHole_cell_support` fails; the journey
  stays GREEN (the ROM grain is its own route).
- (b) `pointData` writes `live := true`, no `look` read: RED `LH14a` (the unpinned ghost admitted), `LH14b`, `P8.2`;
  `pointData_ok` fails.
- (c) `holeProbePoint` ignores `live`: RED `LH14b`, `P8.2`; `LH14a` stays GREEN (the runtime still refuses the
  unpinned cell); `hole_probe_dead` and `holeProbePoint_meaning` fail. (b) and (c) differ on LH14a.
- (d) the generator emits the facts read without `live` (READ-E1's generator-level tooth): the generated hole no
  longer typechecks (the judge's probe is typed at the live point), RED `LH0 generating the hole`, `LP generate`;
  the positive rows `LH0f`/`P8 every method reading facts reads it live` list each judging method.

**Rows** (`lang-journey` GREEN, 792 lines; `--contextual`, `--contextual-checks`, `--hole-omitted-blocker-pin-admits`
GREEN; `--harness-control` RED by name). New: `P8.2 re-pinned tombstone: refused support0 dead` (the probe is the row;
counted left 1), `LH14a` (unpinned: refused `unpinned`), `LH14b` (pinned absent: recorded `suspended "support0 dead"`,
select refused `support0 dead`), `LH0f`, `P8 every method reading facts reads it live`, `LP cell-support-{live,dead,
unpinned}`, `LP wire-cell-pin-reads`, `wire-cell-pin-children`, `wire-pin-unknown-tag`. Changed text:
`P8.2 withdrawn instantiation` is now `refused … support0 dead` (the plan signed before the revoke reads the cell as
it is; the kernel's stale stands behind it, as LH7b for a moved row; the row accepts either). Number-only changes:
helper/package byte counts, LH7/LH8 steps/ticks, every package id printed in a refusal (the version byte moves every
package id). LV1–LV3 print version 5 and `lang/package-version/5`. Fixtures re-pinned: the LH calls pin both fact
cells (a, b); P8's propose pins its provider grant; the cycle's two groundings name the members' cells (a fact now
asserts a live cell; the LP E4 rows are unchanged).

**Wire (the `lang!`), every byte.** `Bounds.packageWireVersion` 4 → 5: a ROM pin's new tag `node 1 id []` (`.cell`)
turns a refused boundary into a read; a `.row` pin is the version-4 `node 0 key [rel, ver]` byte for byte. Codec
labels `lang/package/4` → `lang/package/5`, `lang/package-version/4` → `/5`. `gates/codec-vectors.tsv` re-drawn by
`codec-vectors --write` (the sites' names moved), a second `--write` byte-identical, `--check` ok (263 vectors of 56
sites); `promo/E1-vectors-diff.txt` row by row: the package site's 54 rows — 52 differ only in their first byte
04 → 05; row 42 (the rich ROM) also carries the new `.cell` support arm and prints its pins as `SupportPin.row`; row
50 (the previous-version probe) 03 → 04; row 53 (the LANG-59-era bytes, first byte 00) is unchanged, its refusal now
names `lang/package-version/5`; the version site's 2 rows 05/04 (were 04/03). No other site moves. A version-4
package refuses `lang/package-version/5` before its tree is read: never reinterpreted. RelRead is not a package-tree
field: the live column reaches the wire only inside the method types that request it.

**What breaks, what re-emits.** Every package id (the version byte); every journey World re-runs from genesis; the
Std.hole bundles re-emit (their methods' types gain the column). No deployed Store holds a package. Nothing outside
the journeys holds a package id (`deploy/`, `client/`, `rows/`: none).

**The residual (READ-E1, named).** `(live)` is per read: a hand-written method that reads `facts` WITHOUT it can still
treat a pin match as current — the probe's bug, still typeable. B1–B3 hold for Std.hole-generated packages, whose
generator always reads live (rows `LH0f`, P8's; plant d). A stranger package is not covered.

**Critique.** The column is opt-in, and the judge's guarantee rests on a generator invariant plus a row, not on a type
that every reader of a cell-keyed relation must satisfy. And two pins now say different things about one cell id:
the fact's stored `pin` (the poster's claim, compared to the candidate's) and the caller's kernel pin (whose
liveness is read). They are deliberately two; a reader six weeks out will want the docstrings.

**Meta-critique.** I built the candidate while the cross-family read was still out, and the read changed the plants
and the byte list, not the design; the BIAS is momentum — treating "the design will survive the read" as a fact
because I had already paid for it. The first plant run also read a stale journey binary (a failed module stopped
lake before it relinked); the verdicts I had nearly recorded were from the previous plant. A plant's verdict needs
proof the binary was rebuilt under it, which the runner now checks.

**The charter (R-0025, in this landing, CROSS-LAYER: ROOT).** `CHARTER.md` Scope item 3 "Multi-node agreement.
Nothing." becomes "Writers." in Ember's words (plan §2(d), verbatim): one writer per World; many parties, processes
and Worlds in scope, Worlds speaking by receipts with no atomic cross-World commitment; replication of a World's
writer a planned, priced phase keeping one decided log per World, liveness measured, never proved; merging divergent
histories refused (a fork is a new World). The section's lead sentence and its "briefed against" list follow so they
do not contradict item 3 ("replicate the writer" outside its planned phase; "merge two histories of a World").

Status: landed by CX-PROMO (lang!). Next: C9 (LANG-75.2), then the C2 measurement (P2).

### LANG-75.2 C9 · use-once grants and the one Turn: a docstring and a row, no theorem (2026-10-22; CX-PROMO; IMPACT `redregg/work/promo/IMPACT-C9.md`; cross-family read `redregg/work/promo/READ-C9-grok.md`; RELEASE R-0031 as DOCSTRING; GRANT R-0030 (decisions/kernel.md, CROSS-LAYER: KERNEL))

**Decision (plan §8.2 applied: a promotion that is a rename lands as a docstring).** The IMPACT proposed
`commit_checks_justification_atomically` (an admitted `invoke` ran its method and derived every returned call under
one `look`) and `cellLive_pinned` (`cellLive (pinned E w pins) g` ↔ pinned ∧ `w.live` is some). The read: the first is
a rename of `invoke` — `receive` builds one view and `invoke` runs and derives under it by definition; no landed
theorem or consumer is weaker without it, and no deployed mutation falsifies it that a conjunct's own tooth does not
already catch (the plan's two-Turn split leaves it TRUE: each Turn threads its own view). The second has a real
mutation (`pinned` answering a tombstone with a cell) but no landed consumer; it rides with C2's `kernelWorld`, its
caller. Neither lands; the theorem count falls by the two the IMPACT proposed (both were built and proved in the
candidate, then removed).

**What lands.**
- The docstring on `cellLive` (Lang/Rel) and an addendum to KERNEL-60 (decisions/kernel.md, R-0030), in the read's
  words: a method's live read and the calls that run returns are the same Turn — the pin check plus one Turn, not a
  certificate the kernel consumes; in P8 the checked cell is the provider grant and the spent cell is `cap`.
- The plan's two-Turn split as a journey row, recording what it does: `P8.2s two-Turn split: Turn 1 select while
  live admitted; revoke admitted; Turn 2 commit refused … support0 dead; counted left 1`. The second Turn re-reads the
  cell through its own pins (the E1 path). The row states the boundary: across Turns nothing is shared, so a second
  Turn that spent WITHOUT its own live read would admit — the kernel does not close that gap; the method's read does.
  The read predicted that shape (a spend-only second Turn) admits; the deployed P8 package has no spend-only method,
  and adding one to show a broken protocol admits is not this card (INFERRED, not run).
- Not landed: the builder's plant "commit without its `select`" (it REDs P8.2, P8.4 and the moved-support row,
  `promo/C9-plants/`): a weaker mutation than LANG-75.1's plant (c), already caught.

**Price.** 0: no statement changes, no definition changes but a comment, no wire, no re-genesis.

**Critique.** The row shows the deployed protocol re-checks; it does not exhibit the gap it names, because the
gap-exhibiting protocol does not exist in nano. A reader has to trust the sentence "a spend-only second Turn would
admit" from the read's reasoning, not from a run.

**Meta-critique.** I built both theorems while the read was out and they compiled at once; that ease was the
signal I ignored. The BIAS: equating "a statement Lean accepts about a deployed function" with "a fact the system
did not already state". The plan's own refuter (§8.2) was the test, and the read ran it before I did.

Status: landed by CX-PROMO (lang:). Next: C2 waits on the D.2 measurement's ruling (`promo/IMPACT-C2-MEASURE.md`).

### LANG-75.3 C2 (other branch) + R3 · the abstract closure and the CMTT core leave Lang; the live judgment is `selectHole` (2026-10-22; CX-PROMO-2; IMPACT `redregg/work/promo/IMPACT-C2.md`; measurement `redregg/work/promo/IMPACT-C2-MEASURE.md` and its read `redregg/work/promo/READ-C2M-grok.md`; cross-family read `redregg/work/promo/READ-C2-grok.md`; RELEASE R-0032 (other branch), RULE R-0033 (shape), R-0022 (R3), RELEASE R-0038)

**Decision.** The D.2 measurement fired both of the plan's triggers (§8.1). Of its seven (a)-binders, three are real
premises a bridge `selectHole ↔ judge (kernelWorld …)` would have landed with — `hsel` (the selection row names `i`
and `code[i] = c`: `judge` judges a GIVEN candidate), `hpinned` (an unused hypothesis or the guard pin unpinned throws
`unpinned` while `judge` can say `verified`), `hchecked` (`judge` re-checks with `Lang.infer []`, the run never
re-checks) — and four were how it was stated (`enc/dec` is a definable injection, the guard encoding is a
definition, `hfuel` is needed for no clause of the iff, `hyps_real` is provable inside `romIface`). (c) = 2 (`pruned`,
`uncovered`: no ROM blocker, no per-candidate cost) suffices alone. So the abstract judge is a second, coarser shape
of four live answers plus two arms nothing produces: it leaves, with everything that fed it.

**What is deleted** (15 modules; 209 theorems = 103 of the closure + 106 of the CMTT core; 4,284 lines in the
deleted files = 2,504 + 1,780, and 62 more out of survivors — the hole-model fragment and four docstrings — for the
diff's 4,346): `Lang/Contextual/{Closure, Core, CoreCalculus}`,
`Lang/Proofs/Contextual/{ClosureStatements, Judge, Repair, Outcomes, Operations, Soundness, History, Provenance,
HoleBridge, Core, CoreInstance, Typing}`, and the hole-model fragment of `Lang/Contextual/LangInstance`. Every
statement is listed by name with its successor or its reason in the IMPACT (§1). R3 rides here, not next: the CMTT
instance imported the closure. `drop_removes` goes rather than moves: its premise is false at `langData`.
`Consumer`/`consumer_boundary` (C6's deletion half) go with Closure.

**What moves** (statements identical, digest): `CalculusData` beside `langData` (def module, law 8); `CalculusLaws` and
`weaken_never_var` beside `langLaws` (proof module); `holeDecision_verified_iff`/`holeDecision_label` into
`Lang/Proofs/StdHole.lean` (they read no closure object; the first is C3's live label at the row grain).
`Lang/Contextual` is LangInstance + Protocol + NanoBridge.

**Measured.** Digest: vanished 1,834, all declared; new 0; type-digest changed 0; value-hash changed 0; 45 moved
constants, all from the moved modules. Reverse deps: only the two LangInstance modules used the deleted modules.
Premise price 0. Host closure 89 → 89. Whole tree GREEN; journey byte-identical; no wire, no vector, no re-genesis;
nothing that loads changes shape.

**What C5/C4a/C3 become** (R-0038): C3 and C4(a) are DOCSTRINGS, in the next fast landing — the row-grain label
already exists (`holeVerdictLabel` + the moved `holeDecision_verified_iff`) and nothing reads a receipt monomial
(`selectHole_origin` + C5's `selectHole_hypotheses` are that product). C5 is its own card: three theorems over
`selectHole` (`selectHole_hypotheses`, `selectHole_factor`, `selectHole_live_selects`), landed only with the three
plants the read names (a dead unused `.cell` hypothesis pin; two kept variables after a strengthening; a guard pin
refused while live), the mutations no tooth runs. `cellLive_pinned` stays out (R-0031): there is no `kernelWorld`.

**Critique.** `CalculusData`/`CalculusLaws` now have one inhabitant: an abstraction over a single instance, kept by
R-0033 because `langLaws` states the CMTT laws of the deployed language by name. Real mathematics left the tree with
the closure (provenance minimality, the de Kleer/Doyle label, repair-agrees-with-from-scratch); a planner or a label
reader that arrives later restates it over `selectHole`, it is not resurrected.

**Meta-critique.** A deletion's digest comes back 0/0/0 almost by construction, and I nearly let that stand as the
argument. The BIAS: reading a clean digest as evidence the deletion is RIGHT. The digest proves nothing surviving
changed; only the per-name table argues nothing lost was owed, and several of its rows say "no deployed
counterpart" rather than "successor" — one (`withdraw_never_refutes`) is outright false of the deployed guard, which
reads its pin's liveness.

Status: landed by CX-PROMO-2 (lang:). Next: C3 + C4(a) docstrings (fast), then C5 (`promo/IMPACT-C5.md`).

### LANG-75.4 C3 + C4(a) · the live label and the receipt monomial are docstrings (2026-10-22; CX-PROMO-2; ruling R-0038 per `redregg/work/promo/READ-C2-grok.md` §3; IMPACT `redregg/work/promo/IMPACT-C2.md` §6)

**Decision (plan §8.2: a promotion with no reader lands as a docstring).** C4(a): no `HoleSelection.environment`
field and no `selection_monomial_sound`. A ROM candidate's provenance is one positive product (its supports and the
pins of the hypotheses its body uses), all live at a selection by `selectHole_origin` and the `supportMoved` refusal;
a theorem of it is a rename of those, and nothing reads a receipt (`Lang.Program` keeps the body only; the kernel
record holds no selection). The field would also have changed `selectHole_origin`, `selectHole_nodes` and
`resolutionMax_committed` for no consumer. C3: no `live_label_iff`. The row machine's live label is
`holeVerdictLabel`, read by `holeDecision_verified_iff` (moved into `Lang/Proofs/StdHole.lean` at LANG-75.3) and tied
to the generated term by `holeDecision_meaning`; a ROM label has no reader (no tick reads a ROM hole's candidates).

**What lands.** Two docstrings in `Lang/LiveHoles.lean`: on `HoleSelection` (the product, why it is not stored, its
trigger: a first reader) and on `selectHole` (only the named index is judged; the ROM label's trigger).

**Price.** 0: comments only; no statement, no definition, no wire.

**Critique.** A docstring that names a trigger is only as good as the next reader's search: "a field lands with its
first reader" will be found by someone adding an audit row only if they read `HoleSelection` first.

**Meta-critique.** The plan priced C3 and C4(a) as theorems before anyone asked who reads them; I carried that
framing into IMPACT-C2 §6 as "no new theorem" instead of asking it at the plan. The BIAS: treating a plan's card as a
deliverable to be discharged rather than a question to be answered.

Status: landed by CX-PROMO-2 (lang:). Next: C5 (`promo/IMPACT-C5.md`).

### LANG-75.5 C5 (part 1) · which hypotheses a selection drops, and when a live candidate selects: two theorems over `selectHole` (2026-10-22; CX-PROMO-2; IMPACT `redregg/work/promo/IMPACT-C5.md`; cross-family read `redregg/work/promo/READ-C5-grok.md`; RULE/RELEASE R-0040)

**Decision.** Two theorems land in `Lang/Proofs/LiveHoles.lean`, statements as judged:
`selectHole_hypotheses` — a selection strengthens away EXACTLY the hypotheses whose pins do not hold, and the selected
code uses none of them; `selectHole_live_selects` — when none of `selectHole`'s refusal arms fires (the row names
`i`; code `i`'s supports observed and holding; every hypothesis pin observed and every used one holding; the guard
pin observed and the guard RUN returning `true`), the hole selects `i` at the row's version. With
`selectHole_origin` they are the deployed judgment of a hole, soundness and completeness, with no abstract judge
(LANG-75.3). They succeed `strengthening_sound`, `suspended_sound`'s hypothesis arm, `hyp_var_cites`,
`judge_verified_iff` (←) and `select_ok`.

**The step is named.** `changedHypotheses` now folds `hypothesisStep` (`Lang/LiveHoles.lean`), one hypothesis
position; behaviour identical (journey byte-identical, 793 lines). The proofs read that step, so a mutation of it reds
the fold invariant that IS `selectHole_hypotheses`'s first conjunct, not a restatement's `rfl`.

**Plants** (READ-C2 §3's mutations, the shapes no tooth runs; `redregg/work/promo/C5/plants-landed/`), each with the
five teeth GREEN (elaborated from a copy of `Lang/Proofs/LiveJourney.lean` that does not import this module),
`lang-journey` GREEN and byte-identical, the module RED by name, and a witness that flips:
- a dead unused `.cell` hypothesis pin is not strengthened (`hypothesisStep`): `strengthened [0]` → `[]`; RED at
  the dead-unused step of `selectHole_hypotheses`'s fold (`changed_fold`); `selectHole_live_selects` stays green (it
  is still true: the hole still selects);
- the guard pin refused while live, before the guard runs (`runHoleGuard`): `index 0` → `refused holeGuardBlocked
  0`; RED in `selectHole_live_selects`'s guard step.

**The five teeth stay standalone.** `kept_context`, `strengthening_factor`, `alternative_same_filling`,
`replacement_filling`, `used_hypothesis_suspends` are closed instances over one ROM each and are NOT corollaries of
these theorems (neither mentions the factor's context or filling); the plan's "they elaborate as corollaries" is not
met, and this says so.

**Measured.** Digest against LANG-75.3's: type-digest changed 0; value changed 1 (`changedHypotheses`, now a fold
of the named step); vanished 1 (`changedHypotheses.match_1`, now `hypothesisStep.match_1`); new 25 (the two
theorems, `hypothesisStep`, four private lemmas and generated equations). Premise price 0. Whole tree GREEN;
`gates/check.py` ok. Theorems 5,866 → 5,872 (two public, four private).

**Not in this landing.** `selectHole_factor` (T3): R-0040 keeps the factor (two journey rows decide its context and
filling, and a wrong embedding keeps the node count `selectHole_nodes` checks); it is C5 part 2, with the
mis-embedding plant (two kept variables, the second sent to 0).

**Critique.** `selectHole_live_selects` restates `selectHole`'s refusal arms as premises; it is only as strong as
the claim that those are all the arms, which the read checked by hand against the definition, not a theorem.

**Meta-critique.** IMPACT-C5 recommended deleting the factor on "nothing reads it" and quoted two journey checks as
they would read after my edit, not as they read: the read caught it. The BIAS: arguing from the shape I meant to
make, cited as if it were the tree.

Status: landed by CX-PROMO-2 (lang:). Next: C5 part 2 (`selectHole_factor`).

### LANG-75.6 C5 (part 2) · the factor is typed and re-embeds to the ROM code: `selectHole_factor`; the embedding moves in the factor's own fold (2026-10-22; CX-PROMO-2; IMPACT `redregg/work/promo/IMPACT-C5.md` §3.3 (option A); cross-family read `redregg/work/promo/READ-C5-grok.md` §2; RULE/RELEASE R-0040)

**Decision.** `selectHole_factor` lands in `Lang/Proofs/LiveHoles.lean`, statement as judged: on an installed ROM
(`h.check Δ`, which `instantiateHoles` runs first), the strengthened filling types at the strengthened context, and
the body a selection runs is exactly the selected ROM code. The factor stays (R-0040 refuted my "nothing reads it":
the journey rows `strengthened-context` and `LP strengthened over deployed ROM` decide its context and filling, and a
mis-embedding keeps the node count `selectHole_nodes` checks).

**Deployed changes, behaviour identical** (journey byte-identical, 793 lines): `factorHole` computes the embedding in
its own fold — the context's position list under the same erasures — instead of a second computation
(`(List.range n).filter (!removed.contains ·)`) of the surviving positions; the re-embedding is named `reembed`, so the
theorem reads that step itself.

**New general fact.** `hasType_usesVar_lt` (with its list/row/arm/substitution siblings, `Lang/Proofs/Subst.lean`):
a variable a typed term uses is in its context. The re-embedding is correct only on those.

**Plant** (READ-C2 §3; `redregg/work/promo/C5/plants-landed/pT3-*`): `reembed` sends the second kept variable to 0
when a strengthening moved it — the shape no tooth runs (two kept variables after one strengthening). The five teeth
GREEN, `lang-journey` GREEN and byte-identical, `Lang.Proofs.LiveHoles` RED at `selectHole_factor`'s
`s.body = s.original` step, by name; witness (context `[nat, bool, nat]`, the bool dead and unused, code `x0 + x2`):
`body-is-original true` → `false`.

**Measured.** Digest against LANG-75.5's: vanished 0; type-digest changed 1 — `factor_fold_nodes` RESTATED: it gains
the fold's embedding component (a binder `E`), its conclusion (the term's node count is kept) unchanged; values
changed 8 (`factorHole`, `selectHole` and the proofs that unfold them); new 44 (`reembed`, `selectHole_factor`, the
four scope lemmas, four private lemmas, generated equations). Premise price 0. Whole tree GREEN (725); `check.py` ok.
Theorems 5,872 → 5,881.

**Critique.** `selectHole_factor` needs `h.check Δ`: it is true on every live path because `instantiateHoles` checks
first, but `selectHole` alone does not check, so the theorem is about the composition, not about `selectHole` by
itself.

**Meta-critique.** I argued for deleting the factor on the ground that its theorem would be an identity. The read's
answer was that an identity nobody has proved is exactly what a mis-embedding hides behind; the BIAS: taking "it is
the identity on the fixtures" (the teeth's `rfl`) for "it is the identity".

Status: landed by CX-PROMO-2 (lang:). Next: C7 (`promo/IMPACT-C7.md`), then C6.

### LANG-75.7 C7 · acyclicity over the pin graph is a docstring: a support precedes its Turn by `touchCheck_pin`, and no support names a selection (2026-10-22; CX-PROMO-3; IMPACT `redregg/work/promo/IMPACT-C7.md`; plants `redregg/work/promo/C7/`; GRANT R-0042 (unused: nothing lands in Kernel))

**Decision (plan §8.2; R-0042's own condition).** No theorem. `support_precedes` was written as a statement and built
in scratch, GREEN at 100ad08. It says that for an admitted Turn, a write or retire touch's pin is the pin of the entry
before the Turn, and that no World from the post-state on holds that pin again, unless the two pin inputs collide
(`CollidesAmong` over an explicit two-element list). Its proof composes `touchCheck_pin`, the private `touchCheck_adv`
carried through `commit`, `fold_entryStep` and `pinPre_adv_ne`. That is `stale_behind_forever` started at the
pre-state, plus `touchCheck_pin`. The plant R-0042 names, `touchCheck` comparing against the entry the act leaves, was
built and run first. It reds `touchCheck_pin` (Admit.lean:74) and `touchCheck_stale` (:162) by name, with both
statements false, and lake stops at `Kernel.Proofs.Admit`. Every home `support_precedes` could have imports that
module, so the plant can never red it by name. A write that keeps its version, the only other way the conclusion can
fail, stops earlier at a `CellsFit` proof script.

**No reader.** A ROM row support is a row of the hole object itself, and a cell support says only that a cell stands.
In `Std.hole`, a support is the hole's own `facts` row (activities card F (2): a support is never a hole's row). The
cell a fact names is checked for liveness only. So a support never names another hole's selection, and the deployed
support graph has depth one: every support is a kernel fact of the World before the Turn.

**What lands.** The docstring on `SupportPin` (`Lang/HoleROM.lean`) says this, and gives the theorem's trigger: card F
(3), the first row that needs a hole to cite a hole, where supports become transitive through selections and get a
reader over `rowStep_pin` as well as `touchCheck_pin`. The trigger is cv 01a165f2-bb33.

**Price.** 0: comments only. No statement, no definition, no wire.

**Critique.** "Well-founded by height", the plan's wording, has no object in the kernel. No entry records the height
that wrote it; the order that exists is `EAdv`, per cell. A theorem stated over heights would have needed a history
record the kernel does not keep.

**Meta-critique.** I built the statement and both plants before asking who reads it, as the brief ordered. The answer
to the reader question decided the card, and it was available from `HoleROM.lean:7` and card F without a build. The
BIAS: letting an ordered procedure (plant first) stand in for the question that decides the card (consumer first).

Status: landed by CX-PROMO-3 (lang:). Next: C6 (`promo/IMPACT-C6.md`).

### LANG-75.8 C6 · boundary = Ω: the hole boundary is typing and cost, never behaviour, as two docstrings (2026-10-22; CX-PROMO-3; IMPACT `redregg/work/promo/IMPACT-C6.md`; RELEASE R-0043, no read: a pure docstring)

**Decision.** No theorem. A package's holes show the rest of the system two things. `holeSignature` gives each hole's
name, context and type: all that `checkE … (Ω := holeSignature p.holes)` sees at install, and all that
`unresolvedBody` uses to refuse a residual hole by its type. `Package.holeCharge` gives the expansion bound plus one
guard allowance per hole. What a selected candidate does belongs to neither. The deletion half of the card,
`Consumer`, `Consumer.holds` and `consumer_boundary`, went with `Closure.lean` in LANG-75.3; it had no deployed reader.

**What lands.** A docstring on `holeSignature` (`Lang/HoleROM.lean`) and a paragraph on `Package.holeCharge`
(`Lang/LiveHoles.lean`).

**Price.** 0: comments only.

**Critique.** "Never behaviour" holds only while no consumer pins a filling's value. Activities design experiment 6
(a consumer pinning an exported `value` row) is where it stops holding, and that row is not built.

**Meta-critique.** The plan wrote C6 as "boundary = Ω" before LANG-75.3 deleted the abstract consumer, so most of the
card was done by a deletion two landings earlier. The BIAS: keeping a card's original size after the work that
shrank it has already landed.

Status: landed by CX-PROMO-3 (lang:). P2 complete. Next: PROT-1 (`promo/IMPACT-PROT-1.md`, R-0044).

### LANG-75.9 PROT-1 → PROT-4 (first half) · the receiver is the monitor: an admitted run's edits passed their guards, and every admitted edit at an activity log is a step of the log row's machine (2026-10-22; CX-PROMO-4; IMPACT `redregg/work/promo/IMPACT-PROT-1.md` and `redregg/work/promo/IMPACT-PROT-4a.md`; plants `redregg/work/promo/PROT4a/`; cross-family read `redregg/work/promo/READ-PROT-1-grok.md`; RULE R-0046 (fork B, PROT-1 folds into PROT-4), RELEASE R-0047 under `redregg/work/promo/READ-PROT-4a-grok.md`)

**Why PROT-1's composition had no object.** The plan wrote `activity_history_runs` via `object_history_chain` +
`machine_reached`. Three facts, measured, kept it from being written:
1. An activity has no machine LAW. `machine_reached` is a chain of a state law over a phase field. `Std.activity` writes
   no phase into state. Its protocol is a machine per KEY of its log relation (absent → waiting → answered → absent),
   and the log's ROW GUARD enforces it (`activityWaiting`).
2. The kernel's history drops the rows. `ObjectStep.invoke`/`.nested` bind the run's `rows` and leave them out of
   the trace.
3. Nothing landed said an admitted run's edits passed their guards. The past-extraction theorems connect a run to the
   `guardEdits` CALL, and `guardEdits_never_stuck` says "not stuck".
Widening the trace (fork A) would have restated 18 statements in Kernel and Ledger and given the ledger nothing it can
use (Grok's read §2, §5). The per-key "Reach" is the step relation read per step. Threading it across Turns is
`rowsRun_eq`, a kernel fact about every turn, so no mutation reds a history theorem without first redding a landed one.
So PROT-1 is this card's step fact (R-0046) and lands no history theorem.

**Decision.** Three facts, all new, no landed statement changed:
- `run_edits_guarded` (`Lang/Proofs/Rel.lean`), with `runMeasuredWith_ok` (the run's do-block inverted, the converse of
  `runMeasured_past_extraction`) and `guardEdits_ok`. When a run returns, its rows are its edits' slots and acts. Each
  edit's old row was found, and every guard its relation declares returned `ok` over that row, the state before the
  run and the run's request. This holds for every setup.
- `WaitingStep` (`Lang/Proofs/StdActivityMonitor.lean`), the log row's machine as data, with three actions. `start`:
  an insert by the key's own agent of an unanswered row. `answer`: an upsert by the resumer of a waiting row, keeping
  its capture and answering its own plan. `retire`: a retraction of an answered row. `waiting_body_step`: what the
  generated waiting guard admits, run as the receiver runs a package field (`Admits`, any closure environment), is a
  `WaitingStep`.
- `activity_monitor_safe` (over `runMeasured`) and `activity_program_safe` (over `Lang.program`'s `run`, the run
  `ObjectStep.invoke` binds, at a package with no imports and no holes). For a package whose relation's guard field is
  the generated waiting guard, every edit at that relation of a run that returned is a `WaitingStep` over the old row
  the kernel found. The premises are on the package's guard, so every method of such a package is covered,
  generated or hand-written. The one package decided to meet them is the generated fixture:
  `activity_fixture_monitored` (StdActivityTeeth). The compiled Bell (`rung` as the waiting guard) is the next
  witness, not decided here. `Std.hole`'s installed root is outside the premises: its body is an application and it
  has imports.
  `activityLog`'s value is now the named `activityLogVal`: the same term, no byte moves.

**Why not a corollary of `waiting_*_iff`.** They are stated at `activityApply W [var 2, var 1, var 0]` evaluated in
the inputs' own environment, which runs the body under a doubled environment. The receiver runs the guard as a loaded
record field, under closure environment `[]`. No instantiation makes the two equal, and the iffs cover one input
shape each. They stay as they are: they are the transparency half (PROT-4b), and that card restates them at the deployed
shape.

**Plants** (whole-tree `lake build` under each). P1b: `guardEdits` accepts a guard's refusal. It reds `guardEdits_ok`
and nothing landed. P3: the generated log is unguarded. It reds only the fixture witness `activity_fixture_monitored`.
`StdActivityMonitor` builds under it: the theorem is an implication whose package premise P3 makes false at that one
package, so P3 is the witness's tooth, not the monitor's.
P2 (the waiting guard accepts a second answer) is already `waiting_no_replay` + `activity_answer_no_replay`, so it is
not duplicated. **Correction:** CX-PROMO-3's P1 (`let _ := guardEdits …` in `runMeasuredWith`) is not this theorem's
tooth. On the whole tree it also reds the landed `runMeasured_past_extraction_of` and
`runMeasuredLive_past_extraction_of`. The earlier "no landed theorem reds" came from building `Lang.Proofs.Rel`'s
closure only, which does not contain `Provenance`. Lake leaves a failed module's importers unbuilt, so each
"nothing landed" covers the tree outside that cone.

**Consumers.** A follower re-runs the monitor operationally: `rederive` → `receive` → `program.run` → `guardEdits`.
It calls neither `guardEdits` nor these theorems, and the theorem it can cite is `activity_program_safe` for a package
meeting the premises. PROT-3's `answered_row_is_kept_answer` is the later consumer, and it needs the Bell witness. The StdActivityTeeth admitting rows are
closed instances of the three actions and stay as rows.

**Price.** Landed theorems gaining a hypothesis: 0. Restated: 0. Deleted: 0. `decls` map: 0 lines. No wire, fixture,
package id or journey row moves.

**Critique.** `WaitingStep.answer`'s resumer clause is "the resumer term, applied to this state and request in the
guard's environment, said true" (`Resumes`). For a closed resumer that is its meaning. The statement does not
abstract it further, and a reader who wants "the signer is the resident" must still read the Bell's resumer term. The
premise `hv : d.val = activityLogVal plans` ties the theorem to logs whose value is exactly the generated one. A
package that extends the log's value record is outside it.

**Meta-critique.** The PROT-1 IMPACT and the card brief both carried P1 as "measured: reds only the new theorem". The
measurement was a module-closure build, and the claim was a whole-tree one. The BIAS: treating the build I ran as the
universe the claim quantifies over. A plant's "nothing else reds" is a whole-tree statement or it is not made.

Status: landed by CX-PROMO-4 (lang:). PROT-1 closed into this card (R-0046). Next: PROT-2 (roles replace `Polarity`;
the Bell's open/close/retire refuse by role).

### LANG-75.10 PROT-2 · `Polarity` becomes a role index: a rename on a wider type, not yet roles; the Bell's open/close/retire are the kernel's per-method grant (2026-10-23; CX-PROMO-4; IMPACT `redregg/work/promo/IMPACT-PROT-2.md`; plants and journey `redregg/work/promo/PROT2/`; cross-family read `redregg/work/promo/READ-PROT-2-grok.md`; RELEASE R-0048 as docstring-plus-rename under the read's four conditions)

**Decision.** `Polarity` (`ours | theirs`) is deleted. The protocol calculus takes a type `Role`:
`Iface.chooser : Role`, `Open.me : Role`, `Subst.mine me`, `fill me`, `HasProt sp me`, `Fills sp me`, `SubstOK sp me`.
The four polarity rules keep their content under new names: `fill_skips_others`, `others_hole_untypable`,
`SubstOK.mine`, `Coin.peer_hole_never_planned`. The examples name their parties (Coin: player/peer; Negotiation:
buyer/provider).

**What this is not.** The plan said "roles replace Polarity", and that claim is not earned yet. Every rule tests
`chooser = me` or `chooser ≠ me`, and no theorem tells two roles other than `me` apart. Under `ours ↦ chooser = me`,
`theirs ↦ chooser ≠ me`, each old theorem is the new one. This is not a projection (HYC's `G ↾ p`, Scalas–Yoshida).
The calculus has no `responder` and no `acceptor` field, because nothing reads either. Where the claim would be earned:
PROT-6, whose two offer rows name two chooser roles on this `Iface` and judge `HasProt sp r1` / `HasProt sp r2` without
a further index on `HasProt`, and PROT-3's `proj`, the first reader of a call's responder.

**The 34 RESTATES-MEANING lines.** GATES-20t accepts that verb only: an extra binder is a different elaborated term.
They do not change meaning in the price's sense. `me` is an index (a binder), no hypothesis was gained, and the
restatement reaches every statement that mentions `HasProt`, `fill`, `SubstOK` or `Open.WF`. The plan's "~12" counted
the statements that mention `.ours`.

**The Bell (cv 01a165f1-a212, closed as MIS-MEASURED).** The Bell's `close`, `open` and `retire` bodies check no
signer. That is true, and the owner passes them (LB10, LB12). But a member never reaches them. The kernel gives invoke
authority per method (`invoke_authorized`, KERNEL-25): the owner, or a grant chain naming `invoke method`. The deployed
Bell grants the resident `invoke:0` and a ringer `invoke:4`, and nobody `invoke:1|2|3`. New journey rows LB12n, LB12o
and LB12q: B (granted answer and ring) closes, opens and retires. Each is refused `grantRight`. LB12n and LB12q read the
run the call returned (the bell still open, the ring still present). They are controls of KERNEL-25, not a new tooth.
A resident check on `close` would refuse the operator (LB12). A ringer-scoped `retire` is a delegation choice the
operator makes with grants, not a defect.

**Plants.** R2 (`Subst.mine` fills every hole) reds `fill_skips_others` and `Coin.peer_hole_never_planned`. R3 (the
negotiation's hole chosen by `.provider`) reds the Negotiation module from `template_hasProt` on. A definitional
plant that drops the hole rule's premise breaks proof scripts by arity, so it identifies no false statement and is
not a tooth.

**Price.** 34 RESTATES-MEANING (an index), 4 renamed rules, 5 DELETES; 0 hypotheses; no deployed consumer (nothing
outside these four modules imports them); no wire, fixture, package or re-genesis; three journey rows added.

**Critique.** The 34 lines pay for a parameter whose second use is a card away. If PROT-6 ends up judging both offers
as one role, the index will have bought nothing over `Polarity` but a name.

**Meta-critique.** The plan's "roles replace Polarity" and the filed Bell defect were both read off the surface of a
definition: a type with two constructors, and a method body with no check. Neither reading looked at what consumes
it, which here is a judgment that only ever compares to `me`, and a kernel gate that runs before the body. The BIAS:
taking the local definition as the whole of the semantics when an enclosing layer decides first.

Status: landed by CX-PROMO-4 (lang:). Next: E3 + PROT-6 (the fuse), R-0044.

### LANG-75.11 E3 + PROT-6 · the declared peer row read, Std.offer, and the fuse as a matcher: two runs of one judge term, one forwarded byte string, one seal (2026-10-23; CX-PROMO-5 design, CX-PROMO-6 build; IMPACT `redregg/work/promo/IMPACT-PROT-6.md`; cross-family reads `redregg/work/promo/READ-PROT-6-grok.md`, `READ-PROT-6b-grok.md`; RELEASE R-0050 as fork M, built diff read in `READ-PROT-6-built-grok.md`, RELEASE R-0063 to land; grants R-0049)

**Decision.**
- **The peer read.** A method's rows record may carry one reserved field, `peer`. It holds reads of the package's OWN relations under the other member of the argument's `pair : rec {a, b : digest}` (`Lang.peerOf`; `rowsTy`, `rowsOf`, `methodPeer`).
  - A peer-reading method without a `pair` is refused at install, `peerNotNamed`.
  - A relation labelled `peer` is refused, `badRel peer`.
  - `methodReads` is the only path from the RowView to a method. It reads the peer with the SAME `readsData`, at `parent := peer`, after the kernel's `readKind` (an unpinned peer cell is the kernel's own refusal) and a same-package-id check (`peer: another package`).
  - The kernel price is 0: `RowView.points` is parent-indexed, and every row pin is a RowTouch.
  - `Sig` gains no field.
- **Std.offer** (`Lang/StdOffer.lean`). An offer is a row `{role, terms}`: a chooser role and an acceptance box over θ (closed nat intervals).
  - `offer_guard`: an insert's box must be well formed (`badTerms`); a retract only on `invoke take|withdraw` (`notConsumer`); an upsert never (`final`).
  - The session row is an `activityLog` row guarded by `activityWaiting`. No method of this package answers or retires it; settlement moves value, which is PROT-8.
  - Methods: `post`, `withdraw`, `take`, `fuse`.
- **Fork M.** The matcher's `fuse` returns `[invoke x take deal, invoke y take deal]`, the same bytes to both. Each `take` runs as its own object. It decodes the bytes, reads its own offer and its peer's, evaluates `offerJoint` (`sameRole` / `notCompliant`), and only on `ok` retracts its OWN offer (law 4) and inserts its session row capturing `{pair, θ}`.
  - The two retracts sit in one Draft, sealed once.
  - This is not a joint law and not one judge. Nothing observes both rows together. The one θ is the MATCHER's guarantee (`fuse_calls`), not the takes'. An owner may root-invoke its own `take`, so one session row is not a fuse.
  - KERNEL-45 item 3 fired at its stated price; the amendment is in `decisions/kernel.md`.

**Theorems** (`Lang/Proofs/PeerRead.lean`, `StdOffer.lean`, `DispatchRows.lean`, `StdOfferFuse.lean`):
- The peer read: `peerOf_party`, `peerReads_parent`, `peerReads_package`, `peerReads_unpinned`, `methodReads_no_peer`.
- The term: `offerJoint_meaning` and `offerJoint_total` (the generated term's three verdicts).
- Each side's honesty: `take_iff_compliant` at the method-term grain. The matcher is not a premise. Six take refusals are named; `peerRowUnpinned` is its own name (an unpinned peer ROW), distinct from the kernel's `unpinned` (an unpinned peer CELL).
- The deployed run: `take_run_sound` (`Lang.program`'s run ⇒ `JointOk`, no calls, exactly the own retract and own session insert) and `fuse_calls`.
- `fuse_refused_disjoint` over the two real rows. It replaces the arithmetic half of the deleted `separate_witnesses_over_substitutions`.
- Kernel-side, proved from outside: `dispatched_invoke_rows` / `dispatched_ok_rows` (a dispatched invoke's returned row acts are touches of the sealed Turn) and `admit_retract_absent`.
- The fuse call (premises on the matcher z and the two parties only; `X.program = Lang.program`): `fuse_atomic` (both offer retracts are touches of the sealed Turn, slot AND act), `jointLaw_sound` (one pair and θ decoded from the one forwarded deal; each take found `JointOk` on what it read; each one's peer is the other, so both read the same two pinned rows; the two session inserts carry the same bytes), `invitation_once` (after `World.admit` both offer rows are absent: once per standing row; the grant is not spent).

**Not proved, said out loud.** The run-grain CONVERSE of `take_run_sound` (compliant ⇒ the run returns). Two lemmas are missing from the tree: machine completeness at `Bounds.stackMax` (`bigStep_run` names no stack bound; `StdRun.lean:203` records the same gap), and `extract` completeness. TAKE estimated roughly 400 lines. Journey row LF1 is its instance; `take_iff_compliant` is the iff at the term grain. `offer_safe_forever` is NOT this landing. It needs a new `row_turn_cases` (the row twin of `object_turn_cases`), and READ-PROT-6b condition 2 makes its second conjunct as written false (owner-root take). The escrow instance is DEFERRED to PROT-8, because a value-moving offer needs `Val`.

**Rows.** Journey §LF has 12 rows. LF1 is admitted: both offer rows gone, two session rows, equal `captured`. LF2 is refused `notCompliant` and both rows stand. LF2r is `sameRole`. LF3 is the peer cell `unpinned`. LF3r is `peerRowUnpinned`. LF4 is `peer: another package`. LF5 is `noOffer`, with the grants still live. The controls LF6a/b/c (`noGrant` / `grantRight` / `unpinned`, following `via`) and LF7 (`revisited`) are KERNEL-25's and the walk's, not teeth.

**Plants** (whole tree): P1 `offerJoint := ok` reds the judge's evaluation lemmas (`offerJoint_meaning`'s route) and journey LF2/LF2r admit; P2 `take` skips the judge reds `take_iff_compliant`'s route and LF2/LF2r admit (B7's tooth: no judge remains in `fuse`); P3 `fuse` drops the second call reds `fuse_calls` and LF1; P4 a second deal for y reds `fuse_calls` and every LF row (a changed argument type, so the journey deal no longer decodes); P5 retract → upsert is refused `final` by `offer_guard`, so LF1 refuses: its tooth is the row, not a theorem; P6 the peer read under `self` reds `peerReads_parent` and LF1/LF2 (`sameRole`); P7 no package check reds `peerReads_package` and LF4. Each red is read from the whole tree; under P1–P5 Lake leaves `StdOfferFuse` unbuilt below the red `Proofs.StdOffer`, so `fuse_atomic`/`jointLaw_sound` are reasoned (P3: Y's retract is absent from an admitted Turn; P4: the one-θ conjunct), not observed red. Several reds sit in private helper lemmas of the target theorem's proof; the journey rows are the outcome-level evidence (`redregg/work/promo/PROT6/plants/`).

**Deletes.**
- From `Lang/Contextual/Protocol.lean`: `Conds`, `firstFit`, `coverAll`, `priceConds`, and the Negotiation `World` with its helpers (`Tok'` included).
- From `ProtocolTyping.lean`: `Conds.space` and `Assigns`.
- From `Proofs/Contextual/Protocol.lean`: four scalar illustrations.
- From `Negotiation.lean`: twelve World theorems plus `BuyerGuard`.
- Each was a kernel fact restated over a private model. PROT-5's `Consistent` / `External` / `Internal` family stays.
- `separate_witnesses_bounded` (a scalar illustration not on the ruled list) stays, and is a candidate for PROT-5's sweep.

**The roles claim (R-0048), the second read's §(5) verbatim** (`redregg/work/promo/READ-PROT-6-built-grok.md`):

> Still not earned. The index still has no reader, and this landing does not revert it.
>
> [READ `offerJoint` / `offerJoint_meaning`] the two chooser roles are fields of two offer *values*. The test is `o.field "role" ≠ q.field "role"`. No new theorem mentions `HasProt`, `Iface`, or `Open.me`. No theorem has `HasProt sp r1` and `HasProt sp r2` for `r1 ≠ r2`, both different from `me`. A's offer and B's offer are distinguished by which object holds the row and by a label in the row. A third `Role` still changes no `HasProt` theorem. [READ `LANG-75.11.draft.md` "The roles claim"] "Not earned here, and not reverted here. … PROT-3's `proj` is still the index's named reader." That is the sentence the decision has to keep, and the draft has it.

**Price.** 9 RESTATES-MEANING (the rows step `readsData → methodReads`, and `methodSig_spec`'s `readsTy → rowsTy`: a peer-free method reads exactly as before, `methodReads_no_peer`), the private `setup_eq` in Ledger (CROSS-LAYER: LEDGER, R-0049), 0 hypotheses gained, 39 DELETES; no byte moves (codec vectors identical, `lang:`), no re-genesis, Std.activity's layout unchanged; journey +12 LF rows, every other row byte-identical.

**Finding (JR).** `take` consumes whichever own offer row the CALL pinned. The deal names no offer key. So a party with several standing offers does not bind which one a fuse consumes, unless θ or the box excludes the others. Every consumed offer still passes `offerJoint`. If a row owner wants that binding, the deal gains the two keys (the takes check them against their pinned points); it is a later card.

**LANG-23 (iii) stays open.** Its trigger is rewritten: the first method whose nested invoke argument is not a byte string it already holds. This fuse is not that method: it forwards bytes. T (typed nested-call arguments) is its own card — built as LANG-77 (2026-10-23): the matcher's `deal` is a value of `offerTakeArg theta` since then, and the matcher itself goes in LANG-77's second landing.

**Critique.** `take_iff_compliant` is an iff at the term grain and only a soundness at the run grain. The honesty the plan wants, "a party never retracts without judging", is the run-grain direction, and it is the one proved. The converse is liveness, and its absence is a real gap in Lang's metatheory (no completeness at the deployed stack bound), not this card's.

**Meta-critique.** The plan's shape (X.fuse → Y.take) was written before anyone read the call language, and the blocker was found by measurement only after the IMPACT's first revision. The BIAS: designing a two-party protocol from the session-type literature's picture, where a participant hands its peer a value, and not from the ABI the methods actually have, which forwards bytes.

Status: landed by CX-PROMO-6 (lang:). Next: E5's lang! from CX-P5's patch set (R-0059), after READY E5-PATCHSET.

### LANG-75.12 P4 · M1 · the captured row loses nothing a mini checkpoint keeps that a nano row uses; no checkpointed continuation (2026-10-22; CX-P4; IMPACT `redregg/work/promo/IMPACT-P4.md` §1; landed in CX-PROMO-6's PROT-6 landing per R-0063)
**Measured.** A mini `ObjectiveActivity.Record` (M:`Kernel/ObjectiveActivity.lean:176`) holds the whole
demand-machine state as its checkpoint (heap, control and frame stack; M:`Theory/ObjectiveBendCheckpoint.lean:265`),
plus generation, pin, input, escrow and phase. A nano log row holds `{answered, captured}`, with `captured`
first-order data (`Package.lean:455`, `Ty.isData`).
A nano resumption is `p.resume state captured response req`. The state and request are read in the resuming Turn,
which is mini's "resume with view". The frame stack becomes the plan tag plus `captured` by defunctionalisation, at
most 31 points per activity (`2·plans+1 ≤ methodsMax`). Pin and input are unnecessary because a programmed object's
code and laws are fixed (`Derive.lean:148,163` refuse `hasMethods`).
Census of the four plans on main (Bell `ask`, hole `fill`, the journey's and the fixture's `step`): each resume
reads only the state, the capture and the response. The planned fuse session (`captured := {pair, θ}`) needs
nothing more, and P3 measured 0 second rounds.
**Decision.** No checkpointed continuation and no `lang!`. Two things move:
- The plan's `activity_history_runs` was never written (LANG-75.9). The coverage is `activity_resume_state` (the
  generated method reaches the author's continuation at the capture and the response) plus `activity_program_safe`
  (every admitted log edit is a `WaitingStep`).
- The response-dependent body of `p.resume` is author code. No theorem covers it beyond its typing.
**Not a checkpoint, recorded:** an unanswered row has no exit (`activityWaiting` refuses retracting it). ACT-D's
"abandon = retire past closes" is not what the generator does. That is a separate item (deadline arm; it widens a
guard, so Ember's call). It is not a reason for a checkpoint.
**Price.** 0 theorems restated. 0 bytes moved.

### LANG-75.13 P4 · M2 · divergence is a refusal: the global type has no `Tau` node (2026-10-22; CX-P4; IMPACT `redregg/work/promo/IMPACT-P4.md` §2; landed in CX-PROMO-6's PROT-6 landing per R-0063)
**Measured.** Every program run in a Turn has fuel `min budget treeTicksMax` = at most 131072
(`Derive.lean:362-365`, `Bounds.lean:85`). `run` is structural on fuel and ends with a value or a named fault
(`Eval.lean:245-253`, `run_used_le`). Every fault is a refusal:
- a method fault at `Program.lean:453`, with `runMeasuredWith_ok` as its converse;
- an extraction fault at `:465`;
- a guard fault at `:438`;
- a law fault by `fault_never_admits`.
A refused call is final (KERNEL-44).
Mini's `spin` (M:`ObjectiveBendInteraction.lean:71`, `node_spin_iff`) is a node of a budget-free reference tree. Nano
has no budget-free semantics. A body that never halts and one that halts after 131072 ticks give the same
refusal, `{label}: Fault.ticks`.
**Decision.** PROT-3's global type is over admitted Turns and has no `Tau`/divergence node. `activity_program_safe`
covers every admitted run, because admitted means returned within the cap. Divergence is a strict subset of tick
exhaustion, which is a named, final refusal that commits nothing.
**Boundary, stated.** The monitor is safety only. A silent resumer, or a resume term over the cap, leaves its log row
waiting forever: nothing may retract an unanswered row (`StdActivity.lean:80-82`). Mini handles this with
`deadline`/`timedOut`; nano has no counterpart (see M1's recorded item).
**Price.** 0. No theorem, no byte.

### LANG-75.14 E5 · Lang's half of receipts between Worlds: `Lang.program` takes a receipt check, a cell-keyed read may declare a `(receipt)` column, and `Std.head` holds another World's head (2026-10-23; CX-P5 design and build, CX-PROMO-7 landing; IMPACT `redregg/work/promo/IMPACT-E5.md`; cross-family reads `redregg/work/promo/READ-E5-grok.md`, `READ-E5-built-grok.md`; RELEASE R-0059 to build, R-0066 to land under one condition (PL1 re-planted on a fresh transaction); grants R-0051, R-0055; the protocol half is PROTOCOL-65)

**Decision.**
- **One parameter.** `Lang.program` takes `receipts : ReceiptCheck` (`Cell → ByteArray → Except String Seen`, `Lang/Rel.lean`). It has no default. `Lang.noReceipts` refuses every receipt and is what the toy contexts pass; `Host.Deployed.X` passes `Protocol.Foreign.check`. Lang still imports nothing from Protocol.
- **The column.** A cell-keyed read may be declared `(receipt)`. Each pinned point, and each row of a signed range, then carries a `receipt` field. `Lang.receiptSeen` fills it: it runs the check on the method's own `receipt : bytes` argument against the head object the row's key names, through the caller's pinned view. A refusal of the check is the run's refusal, by name. What the check shows enters only as language data (`seenFits`).
- **Install.** A `(receipt)` read of a relation that is not cell-keyed, or of a method without `receipt : bytes`, is refused `receiptRead`. The read is spelled by the method's rows TYPE (`relReadShape`), as E1's `live` is. So no package byte moves.
- **`Std.head`** (`Lang/StdHead.lean`, text `world/head/Head`). Its methods `post` and `fork` decide nothing; the law `head` decides. It refuses `otherWorld`, `staleHead`, `forkedHead`, `badHead` and `badFork`, and `forked` is frozen. The law's theorems are over BigStep, not evaluation: `head_at_at`, `head_forked_frozen`, `head_at_fork`, `head_world_fixed` (`Lang/Proofs/StdHead.lean`).
- **On the fuse.** `methodReads` threads the same check and the method's arguments into the peer part. A `(receipt)` read is a column of the reader's own rows and of its peer's alike.

**Corrections to the plan's card, as corrections** (PROGRAM-20261022 §2(a) and §3 P5; each MEASURED or READ in IMPACT-E5 §0, each confirmed by READ-E5-grok §1):
1. The plan keyed a fork on "same height, different roots". That is wrong in nano: a recorded refusal advances `steps` and the refusals root at one height. The fork key is STEPS.
2. The plan had the runtime "synthesize `receipts : tx → verified`" with no placement. Lang cannot call `Protocol.Receipt.check`, because Protocol imports Lang, and a check the Host runs before submit is a second semantics that no follower re-runs. So it is ONE `Lang.program` parameter, instantiated by Protocol (KERNEL declares `Program`, LANG instantiates it; LANG declares `ReceiptCheck`, PROTOCOL instantiates it).
3. The plan's §4 had E5 wait on PROT-6's offer rows. It does not: the column is E1's mechanism, on the acceptor's own cell-keyed `heads` relation, read through `look`.
4. The plan said "a foreign head cell". A data cell holds raw UTF-8, and no law can parse a head out of it. The head is an object of a generated package, `Std.head`.
5. The plan listed refusals-trie inclusion/exclusion soundness as E5's KERNEL half. It had already landed (`Kernel/Proofs/RefusalsHead.lean`). The texts that said otherwise are corrected (PROTOCOL-65 amends PROTOCOL-45's critique). The "last head link" half is a `World` field with no E5 consumer, and it stays open.
6. The plan had the Host lookup reply carry a receipt (cv 01a14dfa-1ffb). PROTOCOL-46 §7 had already closed its consumer: the Host hints and follow settles. It is not built, and the cv is closed as superseded.

Two more corrections came from the build, not the card. The plan's gate (`protocol!`/`host!`, a reply layout field) and the first read's 5 → 6 wire bump both assumed that a byte moves. None does: `codec-vectors --check` is ok and `--write` is byte-identical (263 vectors, 56 sites). The landing is `lang!` because install now accepts a method type it used to refuse, so an old log can re-fold differently.

**The point-pin gap (cv 01a166e9-a543), named.** The deployed `nd` cannot pin a POINT read. `Machine.derivePins` pins only the cells the derivation asks for and the `rowUnpinned` rows, and `nd invoke` has `--range` only. So E1's `live` column, and a point receipt read, are reachable from the Sims and the journey and not from the deployed client. E5 therefore also put the column on range rows (`receiptRows`, `rangeRowTy`; one core, `receiptSeen`), and the fixture acceptor reads `(heads (range 1 1) (receipt))`. That cv task holds the fix, in two halves: a client point pin, and the `live` column on range reads.

**Said, not proved.**
- `receipt_column_authenticated` states the POINT slots. No theorem concludes the range row's `receipt` field, and that is the arm the deployed fixture uses. The range assembly is the three-line `receiptRow` over the same `receiptSeen` (READ-E5-built §5). It is a statement gap, not a second check.
- The Lang journey has no HD/RC rows. The head law's refusals are covered by L2–L6 over BigStep and by the two-Store rows X3/X3b. `headDead` and `notCommitted` have no `nd` verb and no closed-instance row anywhere; their teeth are the definitions. Both gaps are filed as cv tasks.

**Price.** 108 RESTATES-MEANING, all against 28e2d88, and the judge's list equals `promo/E5/restates-2.txt` exactly. They are the binder `{rc : ReceiptCheck}` (and `{args}` where a read now sees the method's arguments), the `noReceipts` instances in the witnesses, the `RelRead` constructor's new `false`, and two real conclusion changes: `cited_authenticated` (the live record is `key :: live :: col ++ val`, with `col = []` when `receipt = false`) and `pointData_ok` (a third disjunct for `receipt = true`). 0 hypotheses gained: no added token span in any of the 108 statement diffs contains an arrow. 0 DELETES. The two vanished declarations are `CheckError`'s generated `match_on_same_ctor` (the type gained `receiptRead`). The journey is byte-identical (811 lines).

**Critique.** The Lang half is sound at the grain it states, but the deployed path runs through the arm it does not state: the range row. The column was widened to range rows to get around a client limit. That makes the most-used arm of the feature the least-proved one. The receipt column also authenticates exactly what `Foreign.check` says, and that is only as fresh as the posted head. Lang adds no trust and removes none.

**Meta-critique.** The BIAS: treating "the patch set was read twice" as if it were "the landing was checked". The reads were of CX-P5's tree. This landing re-measured every claim on this worktree at 28e2d88 (build, journey, vectors, decls, the X rows and the six plants), and the decls judge's own list, not the builder's, is the map. The re-measurement found one thing that neither read had raised: `world/head/Head` is HOSTING's path, and no grant row named it (it rides in under CROSS-LAYER: HOSTING as R-0059's patch set). It also found one word in the landing brief that the measurement does not support. Without the mutant, PL1's row X2r refuses `headMismatch`, not `pathMismatch`: the roots comparison comes before inclusion.

And the bias held for me too. The first full judge found three things that neither read nor my re-measurement had checked: the statement census refused `foreign_receipt_sound`'s `∃ r td` form (a collision disjunct over inputs the conclusion chooses), clippy refused the test's module doc, and `cargo fmt` refused the test file. That doc also claimed `headDead` and `notCommitted` were Lang journey rows, which do not exist. All four were fixed forward: `r` and `td` became premises supplied by `check_committed_of`, and the doc now says those two refusals have no row (cv 01a1671d-09d7). I re-measured build, journey, vectors and decls, but not the census or the Rust lints, because I chose the gates I ran from what the card was about rather than from what the judge runs.

**Next.** PROT-2r per R-0064: the `HasProt` `Role` index reverts to what the theorems use (me vs other, under an honest name), its own landing, `lang:` fast.

Status: landed by CX-PROMO-7 (lang!), with CX-P5 as second reader.

**Addendum (CX-PROMO-7, after the landing).** While 1f09446 was judged, eb77b78 landed `nd invoke --pin REL KEY`. That closes the CLIENT half of the point-pin gap this entry names open (cv 01a166e9-a543): a point read, so E1's `live` column and a point `(receipt)` read, is now drivable from `nd`. What stays open is the other half, E1's `live` column on RANGE reads. E5's fixture still reads its heads by range; that is still the arm without a statement (cv 01a1671d-09bf).

### LANG-75.15 PROT-2r · the role index reverts to what the theorems use: a hole's `Chooser` is `me` or `other` (2026-10-23; CX-PROMO-7; RULE R-0064, after READ-PROT-6-built-grok §5; method R-0069: no IMPACT, no read, built and planted, fast judge)

**Decision.** PROT-2 (LANG-75.10) replaced `Polarity` with a type parameter `Role`, carried by `Iface`, `Ctx`, `Open` (`Open.me`), `Subst.mine me`, `fill me`, `HasProt sp me`, `Fills`, `SubstOK`, `Open.WF` and `Open.Replan`. The index had one reader in prospect: PROT-6's two chooser roles. The fuse's read settled that it has none. The two chooser roles of `Std.offer` are fields of two offer VALUES (`o.field "role" ≠ q.field "role"`). No theorem mentions `HasProt sp r1` and `HasProt sp r2` with `r1 ≠ r2`, both different from `me`, and PROT-3's kernel half is a docstring, so `proj` reads nothing either. So the parameter goes. `Iface.chooser : Chooser`, with two constructors: `me`, the party whose protocol is judged (`HasProt`'s `hole` rule requires `chooser = .me`), and `other`, whose hole `fill` never fills. That is exactly what every rule tests. The name says who chooses, and it makes no claim about roles. The two instances' private `Party` types (Coin's `player | peer`, Negotiation's `buyer | provider`) are deleted: they were the `Role` argument, nothing else read them, and their `me` was always the first constructor.

**Where a roles claim would be earned.** A theorem that judges one protocol twice, as `HasProt sp r1` and as `HasProt sp r2`, with `r1 ≠ r2 ≠ me`, and that says something about the pair (a projection, a duality, a deadlock-freedom over both). Nothing on the program's path needs one. The fuse judges two VALUES with one term, and the Bell is the kernel's per-method grant (LANG-75.10's LB12n/o/q controls stay).

**Price** (MEASURED, `gates/decls.py judge` with an empty message on base 7a33fe8): 32 RESTATES-MEANING (R-0064 counted 38 at PROT-2; PROT-6's deletions took 6 of them with Negotiation's World), 6 DELETES (the two `Party` types and their derived instances), 0 hypotheses gained. The only added token spans are `Chooser.other`, in place of `chooser ≠ me`, in `fill_skips_others` and `others_hole_untypable`: one hypothesis restated, not one gained. The theorem names PROT-2 chose stay (`fill_skips_others`, `others_hole_untypable`, `SubstOK.mine`, `Coin.peer_hole_never_planned`). The Contextual calculus has no deployed consumer, so no byte moves (`lang:`). The journey is byte-identical (811 lines). Whole tree 735 GREEN.

**Plants** (whole tree, `hbox logs/promo/e5/p2r/`). R2: `Subst.mine` ignores the chooser (`∨ True`) reds `fill_skips_others` (`Proofs/Contextual/Protocol.lean:118`) and `Coin.peer_hole_never_planned` (`:803`). Lake leaves `Negotiation` unbuilt below that red. R3: the Negotiation interface's `chooser := .other` reds `template_hasProt`, `choose_ok`, `holes_instance`, `cancel_path_refunds_obligation`, `commit_path_pays`, `reach_reserved`, `lost_reply_not_started` and `lost_reply_blocks_replan`. Both reverted byte-identical.

**Critique.** This is PROT-2's diff, reversed by hand over PROT-6's deletions. Two landings bought one rename (`pol` → `chooser`, `ours`/`theirs` → `me`/`other`) and a decision record. The generalisation was paid for in advance of a reader. That reader was named, PROT-6, and when PROT-6 was built it read something else.

**Meta-critique.** The BIAS was session-type literature priming. "Roles" is the vocabulary of multiparty session types, so a two-valued polarity looked like an under-generalised role set. But the index is only as wide as the theorems that consume it. I wrote "two values because every rule tests exactly that" into the docstring so that the next generalisation has to name its theorem first.

### LANG-75.16 PROT-5 + E4(ii) · lost replies over the deployed objects: the kernel reliable, keybroker unreliable, one Boolean per peer; the private delivery model deleted (2026-10-23; CX-PROMO-8; method R-0069: no IMPACT, no read, built and planted, fast judge; absorbs cv 01a16502-c55e item (4), already closed)

**Decision.** The protocol calculus modelled a lost reply twice: as `Hist.inflight` (a dispatched call whose reply has not arrived) and as a private delivery model beside it (`External` deliveries and dedupe, `Internal` read off a history, `Consistent`, and `internal_once_not_external_once` / `exactly_once_needs_reply_and_dedupe` over them). The second was an assumption the experiment supplied ("the proposal supplies none"), stated over a toy provider. Nano has two real owners of a lost reply, so the model is deleted and they are stated. `Lang/Proofs/Contextual/Failures.lean`:

- `submit_at_most_once` (B9, Graversen–Montesi–Peressotti's at-most-once with the frame identity = the call digest): once `Receive.submit` admitted call `c` from `w₀`, no World the log reaches admits it again, and until `journalForgets` a retry of `c` is answered `replayed (w₀.height + 1)` without being re-derived. `reach_submit_at_most_once` is the same from a genesis, with no premise. The first conjunct is KERNEL-33's `submit_once`. The second is new and is what makes the kernel RELIABLE: a client that lost the reply re-sends the same bytes and learns where the call committed.
- `lost_ask_keeps_obligation` (the deployed `lost_reply_keeps_obligation`, over `AskEnd.lost` and `tick_counts`): on every path of a tick, an ask that ended `lost` is the tick's only ask, and the only answer the tick may invoke is `(unanswered WHY)` for that ring. The obligation (the ring gets an answer) stands, and nothing is re-planned in its place.
- `lost_reply_policy (p : Peer)`: one Boolean per peer (`Nano.Peer.reliable`: `kernel` true, `broker` false; Barwell et al.'s reliable roles). A reliable peer's lost reply leaves its request kept, and the next tick re-sends it while the ring is pending (`LostKept`, proved for the kernel as `kernel_lost_kept` from `kept_follows` and the tick's core). An unreliable peer's lost request is never sent again before something freed its ring (`LostSpent`, proved for keybroker as `broker_lost_spent` from `bell_resident_conforms`). Each side is false for the other peer, so flipping either Boolean reds the theorem (PL5b, PL5c).

What the kernel's reliability is NOT: the resident's re-delivery after a lost invoke is a FRESH signed call, so the journal does not recognise it. What makes that retry safe is the bell's `answered` guard plus the resident's re-read (`DeliverAfter`), not `submit_at_most_once`. PL5e measured the same split on P8. With BOTH journal checks dropped (submit's journal-first and `World.admit`'s `checkJournal`), the replayed commit is still not admitted twice: the object's own `accepted` guard refuses it. What the journal keeps is the ANSWER (`replayed` at its height, instead of a re-judged `refused program "commit: refused accepted"`), which a client that lost its reply must be able to read.

`Hist.inflight` and the calculus's re-plan guard teeth (`lost_reply_not_started`, `lost_reply_blocks_replan`, `answered_blocks_replan`, `guard_stricter_than_wf`, `guarded_replan_after_dispatch_is_noop`, `replan_before_dispatch`) stay. They test `Open.Replan`, a calculus definition, not delivery. `Hist`'s docstring names its deployed instances. `Peer`, `Peer.reliable`, `Peer.req` and `lostReply` are definitions in `Lang/Contextual/NanoBridge.lean`, next to the embedding of the resident's effects.

**Price** (MEASURED, `gates/decls.py judge` with an empty message on base 1103509): 11 DELETES (the delivery model's 6 definitions, its `Consistent` statement, `internal_of_histories`, `internal_once_not_external_once`, `exactly_once_needs_reply_and_dedupe`, and the toy `lost_reply_keeps_obligation`, restated deployed), 0 RESTATES-MEANING, 0 hypotheses gained on any landed theorem. No byte moves (`lang:`). Journey byte-identical (811 lines). Whole tree 736 GREEN.

**Plants** (whole tree, hbox `logs/promo/p5/plants/`, each reverted byte-identical):
- PL5a: submit's journal-first lookup dropped. Reds `Kernel.Proofs.Receive.submit_ok` and `submit_replayed`. The journey goes RED (2): `P8.4 replay` and `P8 recovered suffix` are answered `refused program "commit: refused accepted"`, the retry RE-JUDGED.
- PL5e: that plus `World.admit`'s `checkJournal`. Adds `replay_named` and `admit_new` (Kernel.Proofs.Admit). Same two journey reds, and still no double admission (see above).
- PL5b: `broker` reliable. Reds `lost_reply_policy`.
- PL5c: `kernel` unreliable. Reds `lost_reply_policy`.
- PL5d: the resident forgets a lost delivery (`deliverP`'s `.error` arm forgets; `DeliverAfter` follows). Reds `deliver_core`, `deliver_counts`, `deliver_kept` and `deliver_runs` (Hosting.Proofs.ResidentRun).

Under PL5a/PL5e/PL5d, `Failures` sits in the unbuilt cone below the upstream red (lesson 19). So `submit_at_most_once` and `kernel_lost_kept` are reasoned red there, not observed. The journey rows are the outcome evidence for PL5a/PL5e.

**Critique.** `submit_at_most_once`'s first conjunct is a citation, and its second is `fold_answers` composed with `submit_replayed`: the kernel already had the content, and the card adds the statement a lost reply needs. `lost_reply_policy` is a conjunction gated by a Boolean that is defined by cases. Its tooth is real (each side is false for the other peer), but it does not let a third peer be added without a new proof. The resident's reliability toward the kernel is the bell's guard, not the journal: written above, and not proved here (it is E2's member-socket join).

**Meta-critique.** The BIAS was taking the card's plant literally. "Drop the journal check → a replay admits twice" was measured false on the one deployed replay row: the object's guard catches the double admission, and only the answer changes. Writing the plant's prediction into the plan before measuring it is the same habit LANG-75.15 named for roles: a sentence earns its place when a measurement says it.

### LANG-75.17 PROT-7 · the hole's interface as a quotient: a docstring, because nothing reads completeness (2026-10-23; CX-PROMO-8; plan §8.2; method R-0069)

**Decision.** PROT-7 asked for `iface_complete`: a filling under which the filled template is judged is judged in the WEAKEST interface the template admits at the hole, and the declared `Ω` is checked to be at least as strong, so an over-strong `Ω` is refutable. The second half already exists. `HasProt`'s hole rule IS that check, premise by premise: `I.ctx ⊆ Γ`, `SubBag I.need Δ`, `I.post → Q` and `I.owes ⊆ Φ` against the occurrence's own `(Γ, Δ, Q, Φ)`. The first half (completeness, the inversion through `subst`) has no reader. The card named the fuse's candidate check as its consumer. MEASURED: `Lang/StdOffer.lean`'s `offerJoint` (LANG-75.11) judges two offer BOXES and one θ by one Lang term (`sameRole` / `notCompliant` / `ok`). It reads no `Iface`, no `HasProt` and no `Prot`, and no module outside `Lang/Contextual` and `Lang/Proofs/Contextual` imports the calculus (`git grep` of the imports at ff5d55b). Per plan §8.2 the card lands as a docstring on `HasProt` (`Lang/Proofs/Contextual/ProtocolTyping.lean`). The docstring says what the hole rule checks, that completeness is not proved, and what would read it: a candidate check that judges fillings by `HasProt`.

**Price.** One docstring. No declaration changes (decls: 0 map lines), no byte moves, journey untouched.

**Critique.** Proving the inversion would have taken about 60 lines and would have had a falsifying mutation (a hole rule that checks a wrong `Δ`). It still would have been a theorem with no consumer. In the fuse, the role of the quotient is played by `offerJoint_meaning`: θ inside both boxes is exactly the intersection. That is the deployed "weakest joint interface", over boxes rather than protocols.

**Meta-critique.** The BIAS was completion pressure: a card numbered in a sequence reads as owed. The card's own consumer clause was the test, and it failed on a two-minute grep.

### LANG-75.18 PROT-8 · linear value is the kernel's: the escrow instance of `Std.offer` holds its leg and moves it with every retract of its row; the calculus keeps one affine kind (2026-10-23; CX-PROMO-8; method R-0069)

**Decision.** PROT-8 asked for two things: split the calculus's `Tok` into `Cap` (affine) and `Val` (linear: `ret` only with Δ_val empty, or the leftover credited back), stating the linear half "by READING `admit_value`, never by a second count", and build the escrow that PROT-6 deferred (LANG-75.11: an offer that moves value needs linear value). The two halves pull against each other. A `Val` bag in `HasProt` IS a second count of value, and it would have no reader: PROT-7 measured that nothing outside `Lang/Contextual` and `Lang/Proofs/Contextual` imports the calculus, and the escrow is a Lang package, not a `Prot`. So the escrow is built, and linearity is stated where value lives. The calculus keeps ONE affine kind, and its header now says why (`Lang/Contextual/Protocol.lean`). `hasProt_reach` and `at_most_once` are NOT restated. This departs from the card text, and the reason is the card's own clause.

`Lang/StdOfferEscrow.lean`, `Std.offerEscrowPackage theta roles`: `Std.offer` with a value leg. Same method names and indices (`fuse post take withdraw`), the same fuse (the matcher forwards one deal), the same judge (`offerJoint` on each offer's `{role, terms}`), the same guard (`offer_guard`: a retract only from `take` or `withdraw`), the same session log. An offer row's value adds `give {amount, asset}` and `payTo`.
- `post` inserts the row and, in the same tree, moves the leg from the poster's account into the object's (`transfer (of agent asset) (of self asset) amount (via := some grant)`, the poster's KERNEL-60 grant): the row stands exactly when the leg moved in.
- `take`, on `ok`, retracts its own offer, logs its session, and pays its leg to the PEER's `payTo`. Both takes are in the matcher's one tree, so both legs move or neither.
- `withdraw {}` reads its own pinned offer, retracts it, and credits its leg back to its own `payTo` (refusals `offerUnpinned`, `noOffer`).

A standing offer's leg leaves the object only with its row, and only to the peer or back to `payTo`. The kernel makes what leaves one account arrive in another (`admit_value`).

**Rows** (`Lang/Journey/OfferEscrow.lean`, §LE, through `Receive.submit` with `Lang.program`, balances read from the value cells):
- LE0: setup. α and β minted, X holds its 5 α leg and Y its 8 β (two offers).
- LE1: the fuse at price 9. Both rows go; X 5→0 α, B 0→5 α, Y 8→1 β, A 0→7 β; α in accounts 20 before and after.
- LE2: not compliant. Refused `notCompliant`, nothing moved.
- LE3: withdraw. The row goes, X 5→0, A 15→20.
- LE4: withdraw with no row pinned. Refused `offerUnpinned`.
- LE5: a post whose leg exceeds the poster's grant. Refused `transferSpent`, no row, nothing moved.

**Plants** (hbox `logs/promo/p8/plants/`, each reverted byte-identical):
- P8d: the take pays nothing (call slot `none`). LE1 RED: both rows gone, X still holds 5 α, B 0. The value is stranded, which is the linear tooth.
- P8e: the withdraw pays nothing. LE3 RED: the row is gone and X keeps 5.
- P8f: the post deposits nothing. LE0 RED. Then LE1 and LE3 are REJECTED `belowFloor`: the kernel will not pay a leg the object does not hold.
- P8a/P8b: the take and the withdraw pay the object ITSELF. LE1 and LE3 RED, refused by the kernel's `sameAccount` before any Lang code could strand value that way (lesson 14: the layer before).

**Price.** New: `Lang/StdOfferEscrow.lean` (generator), `Lang/Journey/OfferEscrow.lean` (6 rows, `Lang/Journey/Main.lean` runs them). No landed declaration changes (decls: 0 map lines). No byte moves (`lang:`). The rest of the journey is byte-identical (811 → 817 lines: the 6 LE rows).

**Not in this landing, said out loud.** The run-grain theorems over the escrow's methods (`escrow_take_run_sound`: a returned take's one call is its own leg to the peer's `payTo`, and its edits are its own retract and session insert; `escrow_withdraw_run_sound`, the same for the refund), and the linear corollary over `offer_guard` (every retract of an escrow row is in a run that pays that row's leg). Today their evidence is the rows and plants above. They follow as their own landing.

**Critique.** The escrow duplicates `Std.offer`'s take body (35 lines) instead of parametrising one generator by a leg. A parameter would have restated every PROT-6 theorem (each mentions `offerPackageOf theta roles ol sl b`) to buy one shape. Two shapes that agree today can drift later. If the PROT-6 offer without value finds no user, it should be deleted in favour of this one. The legs are fixed per offer and do not depend on θ (a real DvP would pay `θ.price`). That is a limit of the instance, not of the shape. **[Corrected by LANG-82, 2026-10-24]** This sentence priced the wrong gap. Worse than θ not moving the legs: no party's acceptance named what it RECEIVES, so the judge admitted a fuse paying 5 α for 1 of anything (READ-LANGPROOFS F1), and `escrow_fuse_admitted` held of it. LANG-82 adds `want` and the judge reads both legs; θ still moves nothing.

**Meta-critique.** The BIAS was reading the card's two clauses as one plan. "Split `Tok`" and "never by a second count" contradict each other once the calculus is measured to have no reader. Following the first would have repeated LANG-75.10's mistake (an index generalised ahead of its theorem).

### LANG-75.20 PROT-6 follow-up · the fuse deal names its offer: one key per side, checked by each take (`offerNotNamed`); the matcher's run moves beside the fuse theorems so each plant reds its own module (2026-10-23; CX-PROMO-8/promo8-escrow; cv 01a166fa-5091; method R-0069)

**Decision.** LANG-75.11 recorded (finding JR) that a take consumed whichever of its own standing offers the CALL pinned: the deal named no offer, so a matcher chose which of a party's offers a fuse consumed, limited only by `offerJoint`. The deal now names one offer per side. `offerTakeArg theta` is `{keys {a, b : nat}, pair, theta}`, shared by `Std.offer` and its escrow instance. Each take, after both offer slots are read present and before the judge, checks that its own pinned point's key `n` is the one the deal names for `self` (`keys.a` when `self` is `pair.a`, else `keys.b`; `offerNamedT`, `offerNamedOkT`). Otherwise it refuses `offerNotNamed`. The session row's capture stays `{pair, theta}`.
- `NamedKey self keys pair k` (Lang/Proofs/StdOffer.lean) is what the term computes. `offerNamedOk_eval` is its evaluation lemma.
- `take_iff_compliant`: the take returns iff `NamedKey ∧ JointOk`. `take_offerNotNamed` is the new refusal by name. `take_sameRole`, `take_notCompliant` and `fuse_refused_disjoint` gain the `NamedKey` premise.
- `take_run_sound`: a returned take decoded `{keys, pair, theta}`, and its own pinned key `k` is the one the deal names for `self`. Its row acts are exactly the retract of THAT row and its session insert.
- `fuse_atomic` is restated. The forwarded deal decodes to `{keys, pair, theta}`, and the two retracts sealed in the Turn are at the keys the deal names for `x'` and for `y'`. Whichever rows the matcher pinned, the rows consumed are the named ones. `jointLaw_sound`, `invitation_once` and the private `party` carry `keys` in the decoded argument.
- Journey LF8: the deal names Y's offer 1, the call pins Y's offer 0 (compliant with X's at price 9). It is refused `take: refused offerNotNamed`, and all three offers stand. LF2/LF2r/LE2 now name the offer they pin.

**Plants per module (the task's second half).** Before, P1–P5 all redded `Lang.Proofs.StdOffer`, so `Lang.Proofs.StdOfferFuse` never elaborated. The matcher's run (`fuse_calls`, `ViaReads` and their helpers) now sits in `Lang.Proofs.StdOfferFuse`. `Lang.Proofs.StdOffer` no longer unfolds `offerFuseBody` or `offerFuseArg`. The helpers both modules use are public: `get_data`, `find_suspend_of`, `apply4_field`, `runMeasured_inv`, `conforms_empty`, `conforms_opt`, `means_toVal`, `rowMeans_toVal`.

**Plants** (whole tree, hbox `logs/promo/p8/promo8-escrow/plants/`, each reverted byte-identical):
- P3, the fuse drops its second call. Reds `fuse_calls` (and `noRef_fuse`) in `Lang.Proofs.StdOfferFuse`. `Lang.Proofs.StdOffer` builds (738/740). Journey LF1 and LE1 are red.
- P4, a second deal for y. Reds `fuse_calls` (and `fuseArg_cases`) in `Lang.Proofs.StdOfferFuse`. `Lang.Proofs.StdOffer` builds. Every LF/LE fuse row is red ("no bytes").
- P9 (new), `Lang.peerOf` answers `b` for `b` (the b-side's peer is itself). Reds `peerOf_spec` in `Lang.Proofs.StdOfferFuse` (the route of `jointLaw_sound`'s `peerOf` conjuncts) and `peerOf_party` in `Lang.Proofs.PeerRead`. `Lang.Proofs.StdOffer` builds. LF1, LF5 and LE1 are refused `sameRole` (Y's take judges its own offer against itself).
- PA (new), the name check skipped. Reds `body_ok`, `body_notNamed` and `body_refused` in `Lang.Proofs.StdOffer` (the route of `take_iff_compliant`, `take_offerNotNamed` and `take_run_sound`). LF8 is admitted.
- P1, `offerJoint := ok`. Reds `joint_eval`, `noRef_offerJoint` and `noRef_take` in `Lang.Proofs.StdOffer`. LF2, LF2r and LE2 are admitted.
- P2, the take skips the judge. Reds `body_ok`, `body_refused` and `noRef_take`. LF2 and LF2r are admitted.
- P5, retract → upsert. Reds `body_ok`. LF1, LF8 and LF5 are refused `offer_guard: final`.

Under P1/P2/P5/PA the generator's take is unfolded by `Lang.Proofs.StdOffer`, so the fuse module is the unchecked cone. Their theorems are that module's. Under P3/P4/P9 the take module is observed GREEN and the fuse module red. `fuse_atomic` does not red under P3: error recovery admits `fuse_calls` with its statement unchanged. P3's tooth for `fuse_atomic` is `fuse_calls`, by name.

**Price** (MEASURED, `gates/decls.py judge` against d23091d):
- RESTATES-MEANING: 8 public theorems (`take_iff_compliant`, `take_sameRole`, `take_notCompliant`, `take_run_sound`, `fuse_refused_disjoint`, `fuse_atomic`, `jointLaw_sound`, `invitation_once`).
- Each gains `NamedKey` as a premise or a conclusion, and `keys` in the decoded argument. 0 hypotheses gained on any theorem outside the offer modules.
- 7 RENAMES (private helpers made public, statements unchanged), `apply4_field` made public and restated (its environment written as a list: a proof module exports no `Env`-valued `abbrev`, gate C3), and 7 private restatements (`party`, `arg_cases`, `body_ok`, `body_refused`, `editsT_means`, `judge_in_take`, and `callsFuse_means` moved with `fuse_calls`): 23 map lines, `decls: ok`.
- Bytes move: `Std.offer`'s and the escrow's take argument type, so both packages' bytes and ids change. Journey ids for the LF/LE rows change; every other row is byte-identical.

**Critique.** The check reads `self` against `pair.a` with `deq`. A deal whose pair does not name `self` was already refused by the peer read (`peer: notParty`), so the `else` arm (`keys.b`) is reached only by `pair.b`. The keys are naturals, because `offerKey` is `{n}`. A package with a wider offer key would need `keys` at the key type and `eqData`.

**Meta-critique.** The BIAS was believing an observed red is a whole-tree property. Moving `fuse_calls` made P3's red observable, and it showed that a downstream theorem built on a red lemma does not red. Error recovery admits the lemma. So "observed" is per declaration whose proof unfolds the planted site. A theorem that only cites one has no tooth of its own.

### LANG-75.19 E5 owed items · the range receipt theorem and the head journey rows (2026-10-23; CX-PROMO-8/promo8-e5; method R-0069; closes cv 01a1671d-09bf and cv 01a1671d-09d7, both filed at LANG-75.14)

**Decision.**
- **`receipt_row_authenticated`** (`Lang/Proofs/Rel.lean`, beside `receipt_column_authenticated`, of which it is the range twin). On a receipt read with a range (`x.receipt = true`, `x.range = some (m, n)`), `relReads` returning `v` means three things. The caller signed exactly one listing of the relation (`rv.ranges self i = .ok [(pre, most, rows)]`). `v` is the point slots followed by `range {pre, rows = slotsD "r" n rs}`. Row `j` of `rs` is the listing's `j`-th row `(.row key, .row amt vb ver)`: its key is read back at the key (`keyOf … key.k = .ok k`), and its value at the value type (`valOf … vb = .ok val`). Its `receipt` field is `seenData s` with `rc c rb = .ok s`, where `c` is the live cell the row's key names through the caller's pins (`look g = .ok (some c)`) and `rb` is the method's own `receipt` argument. This is the arm the deployed acceptor reads (`client/tests/fixtures/foreign/Accept.ob`, `(heads (range 1 1) (receipt))`). Helper: `rangeRowData_getElem` (row `j` of `rangeRowData` is the `j`-th listed row, read back). The name follows the sibling `receipt_column_authenticated`. `live_range_read_kept` is the install-side round trip of a type, which is a different claim.
- **`Lang/Journey/Head.lean`** (`headSession`, run by `Lang/Journey/Main.lean`). It sets up two Sim Worlds: A commits one call, and B installs `Std.headPackage` and the deployed acceptor, which is read from the fixture's own file (no second copy). Every row goes through `Receive.submit` with `Lang.program Sim.dc.bytes Sim.digestOf (Protocol.Foreign.check Sim.env Sim.dc)`. That is the deployed receipt check at the Sim's parameters, built as `Host.Deployed.X` builds it at the deployed ones. Rows:
  - HD0: install, create, an honest advance. `hpkg = Foreign.headPackageId`.
  - HD1 `otherWorld`; HD1c control.
  - HD2 `staleHead`, HD3 `forkedHead`, HD4 `badHead`, HD5 `badFork`. Each is judged on the World after HD0, and the head reads back unchanged afterwards.
  - HD5c: the honest fork is admitted and reads back `forked`.
  - HD6: a post to the forked head is refused `forkedHead` (frozen).
  - RC0: `accept` with A's receipt of its committed call is admitted, and the acceptance row is at A's transaction id, at the committed height.
  - RC1 `headDead`; RC2 `notCommitted`.

**What the rows found about reachability** (each MEASURED by the row, not assumed):
- `otherWorld` cannot be reached through `Std.head`'s own methods: `post` and `fork` both copy `world`. HD1 reaches it through a DATA object judged by the head law (`create none [Std.head]`, then a `write` of its `world`). The law's clause guards that path. For a head object, `head_world_fixed` is the statement.
- No `Body` retires an object in nano, so "a retired head object" cannot exist. RC1's anchor is a retired cell of another kind, B's revoked grant (a tombstone), pinned. `receiptSeen` reads it through the pins and refuses `headDead`. The fixture revokes a trust anchor with `distrust`, which retracts the row (`untrusted`, Rust X5). `headDead` guards a key that names a dead cell.
- RC2 runs `notCommitted`'s `absent` arm. Its `refused` arm (a receipt of a call A recorded as refused) has no row. `Receive.submit` records no refusal (the Host's `World.refuse` does), so that arm needs the Host path. It is filed (cv below).

**Plants** (hbox `logs/promo/p8/promo8-e5/plants/`, each reverted byte-identical, `cmp`):
- P-THM: `columnRow` takes its columns from a check that admits whatever `rc` refuses (`fun c b => match rc c b with | .ok s => .ok s | .error _ => .ok ⟨0, key, key⟩`). Whole tree: `receipt_row_authenticated` red, and nothing else in `Lang.Proofs.Rel` (`receipt_column_authenticated` stays green, because the point arm is untouched). Journey RC2 red (admitted). Rust `foreign` X2 red (the height-forged receipt was admitted). Unbuilt below the red: `Lang.Proofs.StdActivityMonitor`, `Lang.Proofs.KeyOrder`, `Lang.Proofs.StdHoleCells`. The first form of this plant (`⟨0, .empty, .empty⟩`) failed `seenFits`. It went red as `receiptBounds`, and it also reddened RC0. A plant that reds through another refusal tests the wrong claim, so it was re-made.
- P-HD1 to P-HD6: the head law's `otherWorld`, `staleHead`, `forkedHead` (at), `badHead`, `badFork` (other ≠ held) and frozen-`forkedHead` guards, each in turn made `.bool true`. Each one turns exactly its row red (admitted), on `lang-journey Lang.Proofs.StdHead`. The law theorems go red alongside: P-HD1 `head_change_case`; P-HD2, P-HD3 and P-HD4 `head_at_at`; P-HD5 `head_at_fork`; P-HD6 `head_forked_frozen`.
- P-RC1: `receiptSeen`'s `look = .ok none` arm refuses `notHead` instead of `headDead`. RC1 red, on `lang-journey`.
- P-RC2: `Foreign.check` answers a non-committed receipt `.ok`. RC2 red (admitted), and `Protocol.Proofs.Foreign` `check_committed_of` red, on `lang-journey Protocol.Proofs.Foreign`.

**Price.** New: `Lang/Journey/Head.lean` (14 rows). In `Lang/Proofs/Rel.lean`: 2 theorems and the module header line. `Main.lean`: 2 lines. decls: 0 map lines (nothing deleted or restated). No byte moves (`lang:`). The journey goes from 817 to 831 lines; the 817 non-HD/RC lines are byte-identical to LANG-75.18's. Whole tree 745 GREEN at d23091d, and Rust `--test foreign` green.

**Critique.** The theorem ends at `RowView.ranges`: it says what Lang made of the listing it was handed. That the listing is the kernel's at the signed pin is the kernel's half (`rowView`, the range pin admission recomputes), and nothing here restates it. The RC rows run the deployed CHECK at the Sim's parameters. The deployed parameters are the Rust X rows'. `Lang/Journey/Head.lean` is the first Lang module that imports Protocol. It is tooling (a journey), and no deployed Lang module does. "Lang imports nothing from Protocol" now holds for deployed Lang, not for every file under `Lang/`. The module doc of `client/tests/foreign.rs` still says `headDead` and `notCommitted` have no row. That is CLIENT's file and is left to it (cv below).

**Meta-critique.** The BIAS was reading a written list of refusals as a list of reachable rows. Two of the seven names in the card cannot be reached as the card states them: `otherWorld` through `Std.head`'s methods, and `headDead` of a head OBJECT. Building the rows is what showed it, and the rows say so rather than counting a twin path as the thing itself. The bias also held for my own measurements. HD1's first run was admitted, and I nearly read it as "the head law does not judge writes". A probe showed that the kernel's `write` edits are relative to `stateBase`, and my row had written slot `stateBase + 1` past it. The first P-THM went red as well, but by the wrong refusal. A red is evidence only once its NAME is the claim's.

### LANG-75.21 PROT-8 follow-up · the escrow's run-grain theorems: each returned take, withdraw and post makes exactly its one leg transfer, and every retract of an offer row comes with the transfer of that row's leg (2026-10-23; CX-PROMO-8/promo8-escrow; method R-0069)

**Decision.** LANG-75.18 said it out loud: the escrow's run-grain theorems were owed, with only rows and plants as evidence. They land in a new module, `Lang/Proofs/StdOfferEscrow.lean`. Each theorem is over `Lang.program`'s run of `offerEscrowPackageOf theta roles ol sl b`.
- `escrow_take_run_sound`. A returned take decoded `{keys, pair, theta}` and read both pinned offers `o` and `q`. Its own key is the one the deal names (`NamedKey`), and the two are `JointOk`. Its calls are exactly `[transfer (of self asset) (of payTo asset) amount none none]`, where `{amount, asset}` is `o.give` and `payTo` is `q.payTo`. Its row acts are exactly its own offer's retract and its session insert.
- `escrow_withdraw_run_sound`. A returned withdraw read its own pinned offer `o`, which is present. Its calls are exactly `o`'s leg paid to `o.payTo`, and its row acts are exactly that offer's retract.
- `escrow_post_run_sound`. A returned post's calls are exactly `transfer (of agent asset) (of self asset) amount (some grant) none`. Its one row act inserts offer `n` with exactly the value `{give, payTo, role, terms}`.
- `escrow_retract_moves_leg`, the linear corollary, stated over the package's run for ANY method index. Every retract at `⟨self, 0, kb⟩` among a returned run's row acts is of a row the run read (`keyBytes k = kb`, value `o`). The run's calls include `transfer (of self asset) (of to asset) amount none none` of `o.give`, where `to` is `o.payTo` or the `payTo` of the offer the run read under its peer. In the proof, fuse has no row acts (`fuse_calls`), post only inserts, and indices ≥ 4 do not resolve (`resolve_lt`).

**What the theorems needed.** No lemma was missing from the tree; three things were reshaped first.
1. The take's case tree is ONE generated term, `offerTakeTree theta roles R V done`. `Std.offer`'s take is `offerTakeTree … (offerValTy …) (offerTakeDone …)`, and the escrow's is `offerTakeTree … (escrowValTy …) (escrowTakeDone …)`. Their two edits are one list, `offerTakeEdits`. This deletes the 35-line duplicate that LANG-75.18's critique named. `Std.offer`'s package bytes are unchanged: every LF row is byte-identical.
2. `offerJoint theta roles V` is typed at the value type it judges. `escrowJudged` (a record rebuilt from `role` and `terms`) is deleted, and the judge reads the escrow value's own fields. A rebuilt record evaluates to a suspension, not to a `Data`. The term-grain judge lemma (`offerJoint_eval`, now over any value with conforming `role` and `terms` fields) could not see through it. The escrow's package bytes move: LE5's refusal id changes, and every other LE row text is unchanged.
3. `offerTakeTree_inv` (public) inverts the shared tree once for both takes. `fuse_calls` is stated for any closed package whose `fuse` method is the generated matcher and resolves to its signature.

`offerTakeArg_cases`, `point_cases`, `offerTakeRows_cases`, `offerTakeEdits_means` and `offerTake_editsOf` are the old private take lemmas, made public, generalised over the offer relation's declaration and written with explicit data.

**Plants by name.** Each run-grain theorem reads its own call off the generator: the `calls` field of `escrowTakeDone`, `escrowWithdrawDone` or the post's result. The shared `*_core` lemmas take that fact as a premise, so a plant there reds the named theorem, not a helper. Whole tree, hbox `logs/promo/p8/promo8-escrow/plants/`, each reverted byte-identical:
- P8d, the take pays nothing (call slot `none`). Reds `escrow_take_run_sound` and `escrow_retract_moves_leg` by name (the `rfl` that reads the call field), plus `noRef_take` and the unused-simp-argument linter in `take_core`. LE1 is red: both rows gone, X keeps 5 α, B gets 0.
- P8e, the withdraw pays nothing. Reds `escrow_withdraw_run_sound` and `escrow_retract_moves_leg` by name, plus `noRef_withdraw` and the linter in `withdraw_core`. LE3 is red: the row is gone and X keeps 5.
- P8f, the post deposits nothing. Reds `escrow_post_run_sound` by name, plus `noRef_post` and the linter in `post_core`. `escrow_retract_moves_leg` stays GREEN: a post retracts nothing. LE0 is red, and LE1/LE3 are rejected `belowFloor`.
- P8g, the take pays its OWN offer's `payTo`. Reds `escrow_take_run_sound` and `escrow_retract_moves_leg` by name. The kernel refuses first: LE1 is refused `unpinned`, because A's β account is not pinned.
- The cone is checked: each plant site is upstream only of `Lang.Proofs.StdOfferEscrow` (743/744 jobs built).

**Price** (MEASURED, `gates/decls.py judge` against b6f8a6a): 23 map lines, `decls: ok`.
- RESTATES-MEANING: `fuse_calls` (the package is a parameter), `offerJoint_meaning` and `offerJoint_total` (the judge takes `V`), the generalised take lemmas above, and 10 private body, judge and shape lemmas.
- DELETES: `escrowJudged`, `doneT`, `editsT`.
- 0 hypotheses gained on any theorem outside the offer modules.
- Bytes move: the escrow package only. No re-genesis; no descriptor or vector holds it.
- Journey GREEN. Against de9b403 the only changed line is LE5's refusal id; b6f8a6a adds the HD/RC rows. Whole tree 746 jobs GREEN.

**Critique.**
- The corollary's payee is a disjunction: the row's own `payTo`, or the peer offer's. It does not say WHICH method pays where. The per-method theorems do: the take pays the peer's, and the withdraw pays its own. P8g reds the corollary only because its proof reads the take's exact call. The mutant (a take refunding itself) still satisfies the corollary's statement.
- The theorems state the CALL. Whether the kernel admits the transfer, and that value is conserved, is `admit_value` and the rows LE1/LE3. Nothing here composes the two into one admitted-Turn theorem like `fuse_atomic`.
- The `*_core` premise pattern (the generator's field as a hypothesis, discharged by `rfl` in each named theorem) exists so a plant can red a name. It is a device for observing plants, and it costs one `rfl` per theorem.

**Meta-critique.** The BIAS was trusting the term-grain lemma's interface (`a ↦ o.toVal`) as if it were the language's semantics. `escrowJudged` was correct at run time, and the journey passed. It was unprovable at the grain the theorems use, because a record term evaluates to a suspension. The fix was in the generator, not a new lemma. When a proof needs the code to change shape, the code was carrying a shape only the runtime understood.

### LANG-75.22 PROT-8 follow-up · the escrow fuse at the admitted Turn: both legs move with both retracts, and value is conserved by reading `admit_value` (2026-10-23; CX-BACKLOG; closes cv 01a16829-1872; method R-0069)

**Decision.** LANG-75.21's critique named the gap: the escrow's theorems stated the CALL at `Lang.program`'s run, and nothing composed them with the kernel into an admitted-Turn theorem. It lands in a new module, `Lang/Proofs/StdOfferEscrowFuse.lean` (new, so FABLE-T's fuse rewrite of `StdOfferFuse`/`StdOfferEscrow` does not collide with it).
- `EscrowLegMoved … P` (a `Prop`): party `P`'s take, on the forwarded `{keys, pair, theta}`, read its own pinned offer `{k, o}` (the one the deal names, `NamedKey`) and its peer's `{kq, q}`, found them `JointOk`; its offer row `⟨P, 0, kb⟩` is retracted in `t` and absent in `w'`; and `o.give = {amount, asset}` left `of P asset` (balance in `w'` exactly `amount` lower) and arrived in `of q.payTo asset` (exactly `amount` higher), denominations and floors kept.
- `escrow_fuse_admitted`: a signed `z.fuse` of `offerEscrowPackageOf …` that `receive` derives and `World.admit` admits from canonical cells and rows: ONE `{keys, pair, theta}`, `EscrowLegMoved` of `x'` AND of `y'`, and `∀ d, w'.valueSum d = w.valueSum d`, which is `admit_value hcan ha d` read at this Turn, not a second count of the legs.

**How.** No unrolling of the fuse's tree (as `fuse_tree` does for `Std.offer`). The proof walks the kernel's own record of the walk, `Dispatched`: the signed fuse is the root (`dispatched_of_signed`); `fuse_calls` gives its two `take` invokes; `dispatched_signed_children` dispatches each one level down; `escrow_take_run_sound` gives each take's one transfer and its two row acts; `dispatched_invoke_children` dispatches that transfer one level further; and the new KERNEL lemma `transfer_reads_back_dispatched` (`Kernel/Proofs/LedgerNext.lean`) reads a dispatched transfer's two balances back on `w'`. Each balance write is THE act at its cell, by `duplicateEffect` (the private `effect_written`, now shared with `effect_reads_back`). Two small exposures: `escrow_fuse_resolve` (was the private `fuse_resolve` of `StdOfferEscrow`) and `Nanodregg.Lang.invokeRun_pkg` in `DispatchRows` (a public copy of `StdOfferFuse`'s private one: that private copy is FABLE-T's file and is deleted when card cv 01a16821-581a folds the StdOffer helpers).

**Plant (MEASURED, hbox `logs/backlog/plants/C1-P8d.build.log`).** P8d, the take pays nothing (its call slot `none` in `escrowTakeDone`): `lake build Lang.Proofs.StdOfferEscrowFuse` is RED at `Lang.Proofs.StdOfferEscrow`, by name at `escrow_take_run_sound` (`rfl` on the generator's call field, line 417) and `escrow_retract_moves_leg` (line 843). `escrow_fuse_admitted` is not elaborated: its import failed. Reverted byte-identical. Journey row LE1 is this theorem's instance on the Sim World (both offers gone, X's 5 α to B, Y's 7 β to A, α outstanding 20); P8d reds it too (LANG-75.21).

**Critique.**
- A generator plant cannot red a downstream theorem by name. Every way a take could pay one leg, or none, changes the call that `escrow_take_run_sound` states exactly, so the run-grain module goes red first, and this module is blocked, not refuted. The Turn theorem's tooth is inherited, not its own. A Turn-only fact (a KERNEL plant that drops the destination credit) would red `transfer_exact` upstream the same way.
- The peer's `payTo` is the payTo of the offer `P`'s take read under its peer. That this is the OTHER party's own offer (`qx = oy`) is `jointLaw_sound`'s coupling for `Std.offer`; its helpers (`methodReads_offer`, `peer_pair`) are private in FABLE-T's `StdOfferFuse`, so the escrow statement does not carry the coupling or `x' ≠ y'`. Both follow from the same proof once those helpers are public.
- `transfer_reads_back_dispatched` and `transfer_exact` both read back a transfer's two balances. `transfer_exact` (in `Kernel.Proofs.Ledger`, below `InvokeTree`) also states the frame and the grant ledger for the SIGNED transfer; it cannot import the dispatched one. It is two statements of one fact at two grains.

**Meta-critique.** The BIAS was to copy `fuse_tree`'s shape: unroll the derivation by hand, `callStep` by `callStep`. The kernel already records the walk as `Dispatched`, and `spend_reads_back_dispatched` is the pattern at any depth. Reading the kernel's own index of the tree is shorter, and it is the same statement whichever object makes the call.

### LANG-75.23 E5 follow-up · the refused arm of `notCommitted`: a row and its theorem (2026-10-23; CX-BACKLOG-2; closes cv 01a16814-02d9; method R-0069)

**Decision.**
- **The row** (`Lang/Journey/Head.lean`, RC3). A's Host refuses and RECORDS one call (`Receive.judge`, the Host's decision: a create naming a package A does not hold, `missingCell`) before B builds the head object of A's head. B's deployed acceptor, given A's receipt of that call, refuses `notCommitted`. The row first asserts that the receipt's own answer is `refused` (so it cannot pass on the absent arm), then reads the verdict. RC0 to RC2 are unchanged (A's head now has 2 steps: the commit and the refusal).
- **The theorem** (`Protocol/Proofs/Foreign.lean`, P5 `refused_receipt_notCommitted`, the consumer of `check_refused_sound`). Take a receipt at the held head's roots, of a World folded from A's genesis, that checks `refused h code m`. Then the column refuses it `notCommitted`, and A's World holds `refusalAt (.tx r.txId) = some (.refused h code m)`, or the hash collides among the listed inputs (the receipt and the World are premises, so the list is explicit). `RefusalsOk` is discharged from the fold (`fold_refusalsOk` from the empty genesis refusals).
- **CLIENT's doc** (`client/tests/foreign.rs`): `headDead` and `notCommitted` have no Rust row because `nd` has no verb for them. They are now journey rows RC1–RC3, and the doc points there instead of saying "no row".
- The brief named Protocol/Rows. The row lives beside RC1/RC2 in the Lang journey, where both Worlds and the deployed acceptor already are. The loopback rows have no second World.

**Plant (MEASURED, hbox `logs/backlog/plants/C5-refused-accepted.*`).** `Foreign.check` was changed to accept a `refused` receipt as committed. Results:
- `Protocol.Proofs.Foreign` RED at `check_committed_of` (l.59) and at `refused_receipt_notCommitted` (l.173);
- lang-journey `RC3 … admitted` FAIL, `RED (1)`.

Restored. MEASURED green: `lang-journey: GREEN`, RC3 `refused … "notCommitted"` with `the receipt states refused: true` (`c5-lang-journey.log`).

**Critique.** RC3's refused call is a `missingCell` create. A `cancelled` record (`Receive.cancel`) would exercise the same arm by another writer of the refusals trie. The theorem covers both; the row covers one.

**Meta-critique.** The pull was to place the row where the brief said (Protocol/Rows) and build a second-World harness there. The question is which runner already holds a foreign World. Lang journey's Head does. Building there needs no new machinery, which kept this card small.

### LANG-75.24 Law 1 · the offer proofs' run helpers are MethodRun's; the fuse's twins deleted; the escrow fuse no longer takes `x' ≠ y'` (2026-10-23; CX-BACKLOG-3; closes cv 01a16821-581a; method R-0069)

**Decision.**
- **Deleted twins** (each an exact copy of a lemma that already existed):
  - from `Lang.Proofs.StdOffer`: `get_data`, `find_suspend_of`, `means_toVal`, `rowMeans_toVal` and the private `find_rowToVal_of` (`Lang.Proofs.MethodRun`'s, HOSTING-44), and `apply4_field`, which is `apply4_method` at `activityMethod`. The six call sites in StdOffer, StdOfferFuse and StdOfferEscrow now call `apply4_method`.
  - from `Lang.Proofs.StdOfferFuse`: the private `invokeRun_pkg` (DispatchRows has the public one), `peerOf_spec` (`Lang.Proofs.PeerRead.peerOf_party`, same statement) and the private `callStep_ok_`.
  - from `Lang.Proofs.DispatchRows`: the private `callStep_ok'`, and the alias `admit_retract_absent`. StdOfferFuse now names `Kernel.admit_retract_row` (KERNEL-65) directly.
- **Kernel** (`Kernel/Proofs/InvokeTree.lean`): `callStep_ok` is public now, so the two Lang copies could go. Two new lemmas:
  - `dispatched_actor_visited`: below the root, a dispatched Body's caller is already in the walk.
  - `dispatched_invoke_fresh`: in a received call, a dispatched invoke is of an object the walk had not yet visited (`revisited` otherwise).
- **`escrow_fuse_admitted` loses `hne : x' ≠ y'`** (LANG-77's open follow-up (a)). The fuser's second call invokes its peer one level below the root, where `x'` is already in the walk. So the peer is not `x'`. `peerOf_party` then makes the peer `y'`: if the pair's `b` were `x'`'s bytes, the peer would be the pair's `a`, which reads back to `x'`. The premise was needed because `peerOf`'s `samePeer` check compares bytes, and two different byte strings can still read back to one object. The other fuse theorems (`fuse_atomic`, `jointLaw_sound`, `invitation_once`) keep their statements. `fuse_tree` already derives `x' ≠ y'` the same way, from the dispatch.

**Plant (MEASURED, hbox `logs/backlog/plants/C6-no-revisited.build.log`).** `invoke`'s `revisited` check was replaced by `req true`. `lake build Kernel.Proofs.InvokeTree` is RED at `Kernel.Proofs.Tree` `invoke_ok` (l.46) and at `Kernel.Proofs.Authority` (l.147, l.151). `dispatched_invoke_fresh` and the escrow theorem sit behind that import. Restored; `git diff` empty.

**Flag day.** None. The proofs changed, and no definition, wire format or VK did. The decls export shows deletions, one restated theorem (the dropped premise), one private-to-public change and two additions.

**Critique.** DispatchRows' `foldCalls_rows` and `foldCalls_split_rows` are the rows analogues of InvokeTree's `foldCalls_effects` and `foldCalls_split`. They are not copies: one fold lemma over both fields would replace four, but that is a restatement and is not done here. The two private `fuseOkEnv` abbrevs (StdOfferFuse, StdOfferEscrowFuse) stay duplicated because closure C3 refuses a proof module that exports an abbrev.

## LANG-76 An activity may declare a patience: an unanswered row is retired by anyone from its deadline on, with its cursor row (2026-10-23; CX-DEADLINE; Ember's open decision cv 01a166ba-7af9, built as its DEFAULT; IMPACT `redregg/work/promo/IMPACT-P4.md` §1.5; method R-0069)

**This was Ember's decision, and this landing is its default.** cv 01a166ba-7af9 asked whether an unanswered activity row may be retired after a declared deadline. The default was yes: a deadline arm in the generated guard, a widened check with a named refusal before the deadline and a journey row after it. The alternative was "leave it": an unanswered row waits forever and holds one of the log's slots (the Bell has 1024), on the bet that 1024 rows are enough in practice. The default was approved for building. The decision is resolved to the default with this landing's hash.

**The defect (READ).** `activityWaiting` refused every retraction of an unanswered row (`("none", refusedT "unanswered")`), and every method passes through it. A silent resumer, or a resume past `treeTicksMax`, left the row waiting forever. ACT-D's "abandon = retire past closes, by anyone" was not what the generator did.

**What changed.**
- `Std.activityDue p key req` is `key.notBefore + p ≤ req.notBefore`. It is the clock `windowed` already uses: a Turn lands in its signed window `[notBefore, validUntil]` (KERNEL-10), so no clock holder is read. A starter may backdate its key by at most the kernel's window, so the deadline falls between `p − 1024` and `p` heights after the start landed. The sum faults past `natLimit`, and a fault refuses.
- `activityWaiting … (patience : Option Nat := none)`. An unanswered row's retraction goes to `activityLate patience`: with `none` it is `refusedT "unanswered"` (the old term, byte for byte); with `some p` it is `guard (activityDue p …) "unanswered" okT`. Before the deadline the refusal keeps its old name. From the deadline on, anyone may retract. Answers stay the resumer's.
- `activityQueued … patience`: the cursor's retraction is the resumer's, or anyone's from the deadline on (`activityDequeue`).
- `activityPackage … patience`: with a patience, the generated `retire` is `activityRetireMethod`. It reads the log row at its key, as `resume` does. An answered row leaves the log alone (one edit). An unanswered row leaves the log and the cursor in one Turn (two edits), which both guards admit only from the deadline. Without a patience, `retire` is the old one-edit method, so `Std.hole`, `Std.offer` and the escrow emit byte-identical packages.
- `Std.activity … patience` refuses `some 0` by name (`zeroPatience`): anyone could abandon at once.
- Surface: `(activity cursor log [(limits …)] [(patience n)] …)`.
- The Bell (`world/resident/Bell.ob`) declares `(patience 2048)`, and its doc says so. Its hand-written `retire` reads its `rings` row (`(reads (rings (points 1)))`). Answered, it retracts `rings`. Unanswered, it retracts `rings` and `pending` together, which `rung` admits from notBefore + 2048. `Lang.Bell.patience` and `rung` follow, so `shapeOk` reads the re-emitted core.

**Why the abandon retracts both rows (a design point the card did not name).** The card asked for "retire … admitted and the row is retracted". A log-only retraction of an unanswered row leaves its cursor row behind. The Bell's resident reads `pending`, answers that ring, and the answer is refused for the whole queue (`answerRefused` stops the queue; Hosting/Resident/Run.lean's header). The cursor row also holds one of `pending`'s 64 slots for good. So the activity's own methods keep "a cursor row for each unanswered log row" across an abandon. A hand-written layer method can still break that, as LB13's `drop` already could. That is the guard's grain: the guards admit each edit, and the method decides which edits travel together.

**Theorems.**
- `Lang/Proofs/StdActivity.lean`: `activityDue_meaning`, `waiting_retract_unanswered_meaning` (the arm, as an `if`), `waiting_retract_before_deadline_refused`, `waiting_retire_after_deadline_admitted`. `waiting_retract_iff` is RESTATED: admitted ↔ `answer.isSome ∨ ∃ P, patience = some P ∧ n + P ≤ m`. `activity_retire_some_meaning` is generalised over names and patience. `activity_retire_none_meaning` is generalised over names, at `none`.
- `Lang/Proofs/StdActivityMonitor.lean`: `WaitingStep` takes the guard's patience and gains `timedOut`: with `patience = some p`, a retraction of an unanswered row signed at `m ≥ key.notBefore + p`. `waiting_body_step`, `noRef_activityWaiting`, `activity_monitor_safe` and `activity_program_safe` are RESTATED at the guard's patience (RESTATES-MEANING). With `none` the machine is the old one: `timedOut` needs `patience = some p`.
- `Lang/Proofs/StdActivityTeeth.lean`: the fixture at `some 10` (`activity_late_*`). Before, at and after the deadline at the log guard and the cursor guard. The resumer is unchanged. The generated `retire`'s edits: `log` when answered, `log+cursor` when unanswered, `key` and `unknown` refusals. `activity_zero_patience_refused`.
- `Lang/Proofs/Bell.lean` (`rung_is_waiting`, `bell_monitored`) and `Hosting/Proofs/BellRow.lean` (`answered_row_is_kept_answer`) are restated at `some Lang.Bell.patience`. This is one argument each in CX-BELL's files.

**Journey.** LB10b: A retires B's ring before its deadline and is refused `rung: unanswered`; both rows stand. LB10c: at notBefore 2100, one height before the deadline, refused. LB10d: at 2101, admitted, and both rows leave (pending 1 → 0, rings 2 → 1).

**A second defect, found on the way and fixed (PROTOCOL; MEASURED).** The re-emitted Bell's install (36,379 call bytes) was committed and never confirmed. Follow's confirm runs `receipt <CALL in hex>`, and that argv was past `argvBytesMax` (65536). Follow refused it `argvPastBound`, and the attempt read that as `uncertain`. This was traced in `rows bell` with a temporary trace in `Loopback.drive`, since reverted. Any admitted call past 32,760 bytes had this defect. The kernel admits calls up to `eventBytesMax` = 65536. `argvBytesMax` is now DERIVED, `2 * eventBytesMax + 1024` = 132096. The theorem `Protocol.Command.receipt_argv_fits` says that every call within `eventBytesMax` has a `receipt` argv within it, by `toHex_utf8ByteSize` (hex is two ASCII digits a byte). `Text.toHex` now folds over the byte array's data (the same output), so its size is a list fold. `argv_fits_frame` still holds: 132097 ≤ 262144. `client/src/generated.rs` is re-emitted (`ARGV_BYTES_MAX`).

**Plants** (hbox `logs/deadline/`, plant tree `wt/deadline-plant`, each restored):
- P1: the log arm's comparison dropped (`some _ => okT`). Red: `waiting_retract_unanswered_meaning` (Lang.Proofs.StdActivity), `activity_late_retire_before_deadline` (Teeth); LB10b and LB10c FAIL. The early retire is then refused by `queued: notResident`: the cursor guard still holds. LB13f FAIL.
- P1b: `activityDue` always true (both guards). Red: `activityDue_meaning`, `activity_late_retire_before_deadline`, `activity_late_cursor_before_deadline`. LB10b is ADMITTED, and LB13f is admitted.
- P2: the arm dropped (`some _ => refusedT "unanswered"`). Red: `waiting_retract_unanswered_meaning`, `activity_late_retire_at_deadline`; LB10d FAIL (`rung: unanswered`).

**What re-emits (lang!).** `world/resident/Bell` is re-emitted: 35,012 → 45,980 core chars, 27,569 → 36,277 package bytes. The Bell's package id changes. LB0, LBw and `rows bell` read the new core. A resident World holding the old Bell re-geneses (deploy/RUNBOOK.md §1). An old bell's rows would still read, but its `retire` cannot abandon. Every other package is byte-identical: `patience = none` emits the old terms, MEASURED for the Bell's old source under this generator (35,012 chars, the shipped old core). `launcher/tests/resident_bell.rs` Q5 pins the `rings` row its `retire` reads (`--pin rings KEY`). `ARGV_BYTES_MAX` moves in `client/src/generated.rs`.

**Critique.** The deadline is relative to the starter's own `notBefore`. A starter that backdates loses up to one window of its own patience, and nobody else's. A deadline stored in the row would have been absolute, but it would change the log's layout and every activity's bytes for a 1024-height slack the Bell's doc already states. The Bell's 2048 is a choice in heights, not in time. In a quiet World heights move slowly, but the log fills only by rings, and every ring is a height. Liveness (every row eventually answered or retired) is still not stated. `WaitingStep` is safety only. With a patience, the abandon exists, so "eventually leaves" is now statable over a World whose heights advance.

**Meta-critique.** The BIAS was reading the card's guard-grain wording ("the row is retracted") as the whole design. The first build answered it to the letter: the log's arm, plus a separate `timeout` method. Measuring the Bell's methods against the arm showed that its own `retire` would orphan `pending`, so the abandon had to live in `retire` itself, with a read. The same bias nearly hid the Protocol defect. The resident test went red at `install … uncertain`, and "uncertain" reads like the Host. The PROTOCOL-55 precedent (`uncertain` rendered from a refused confirm) is what made me trace it rather than shrink the Bell under the bound.

## LANG-77 Typed nested-call arguments: an `invoke` slot declares its argument type, and the runtime encodes the value the method returned (2026-10-23; FABLE-T; cv 01a16679-198f; design `redregg/work/promo/DESIGN-T.md`; closes LANG-23 (iii); method R-0069)

**The defect (MEASURED, IMPACT-PROT-6 §0.6 and READ-PROT-6b-grok §1).** The `invoke` arm of `callArms` was
`("args", .bytes)`, `bodyOf` read it with `bytesAt`, and no `Term` or `Prim` produced the wire bytes of a value. A
method received its argument DECODED (`runSetupWith`, `decodeData sg.arg`) and could send a nested call only
BYTES it already held: the Relay forwarded `rest`, the fuse's matcher forwarded one `deal`. The runtime already
encoded a method's state (`stateSlots`) and its row values (`Rel.lean`) at their declared types on the way out;
calls were the one typed thing it did not encode. Nano's open composition (LANG-21/23) could not compose a call
from a value a program computed. Open since LANG-23 (2026-10-17) as (iii).

**Decision.**
- `Lang/Package.lean`: the arms are named (`accountArm`, `creditArm`, `grantArm`, `transferArm`); `invokeArm (A : Ty)`
  is the `invoke` arm whose `args : A`; `callArms : Option Ty → List (Label × Ty)` lists the arms of a slot whose
  invoke (if any) is at `A`; `callTy (A : Option Ty)`; `callOf kinds` is the invoke-free slot (an `invoke` in
  `kinds` is NOT an arm: the slot is then empty and install refuses it `badMethod`); `invokeOf A kinds` is the slot
  that may invoke with a value of `A`. `callSlotOk` requires an `invoke` arm to be exactly `invokeArm A` with
  `invokeArgOk A = A.isData && Wire.dataTy A` (`isData` as `methodSig` asks of the method's own argument; `dataTy` as
  the codec refuses without). `Wire.dataTy` moves from `Lang/Wire/Data.lean` to `Lang/Wire.lean`, beside `tyWire`:
  the install check and the codec read ONE predicate (law 1).
- `Lang/Call.lean`: `bodyOf digestOf (A : Option Ty)` encodes the `invoke` arm's `args` with `argsBytes A`
  (`Wire.encodeData A`, the one data codec; refused by name `args: no invoke arm` / `args: no bytes at the slot's
  type`, both unreachable past typing); `callData bytesOf (A : Option Ty)` reads `args` back at `A` (`argsData`,
  `none` when the bytes are not a value); `callsOf digestOf (ks : List Ty)` walks the slots WITH their declared
  types (`slotInvokeArg`); `callFits` drops the `args.size` clause of its invoke arm (a bound nothing read).
- `Lang/Program.lean`: `RunSetup.calls : List Ty` (the resolved method's slot types); `runMeasuredWith` reads
  `callsOf digestOf S.calls c`. The kernel is untouched: `Body.invoke … (args : ByteArray)`, 13 Body kinds, the codec
  vectors. The callee still decodes at ITS argument type (`runSetupWith`): a caller's `A` and a callee's `A'` agree
  when their shapes agree (labels are not on the wire); a mismatch is the callee's existing `program "arguments: …"`,
  the one place argument bytes are checked, for a root call and a nested one alike (LC8).
- `Lang/Surface.lean`: a slot's kind list may hold `(invoke T)`: `(calls ((invoke TakeArg) transfer) (transfer))`;
  `T` is read by the one type reader. The bare atom `invoke` names no arm.
- Journey §LC (`Lang/Journey.lean`): the Relay COMPOSES. `Relay {hits, me, n, next, via}`; `arm {via}` holds the
  hop's grant in state (it exists only after both objects do); `go {n}` invokes `next.go {n := n + 1}` through it.
  LC3: o5 received `n = 4`, composed by four relays. LD4b arms with a non-digest via. LC2b arms each relay. LC7: a
  slot at `(fn nat nat)` is refused `badMethod` at install. LC8: a relay composes `{n}` for a Sink taking
  `{n, note}`: refused `program arguments: …` at the callee; the tree fails whole (the relay's hits stay 0).
  `relayArgs`, `chainArgs`, `RA` are deleted (nothing forwards opaque bytes).
- `Lang/StdOffer.lean`: the matcher's `offerFuseArg theta` carries `deal : offerTakeArg theta` (a VALUE);
  `offerCallTy theta := invokeOf (offerTakeArg theta)`. The matcher shape is kept in THIS landing and goes in the
  next (the fuse as two objects, DESIGN-T §3): one `lang!` for the language, one `lang:` for its consumer.
- `Kernel/Proofs/InvokeTreeWitness.lean` (CROSS-LAYER KERNEL, a proof fixture): its relay's slot is `invokeOf .nat`
  and its call datum `.nat 4`; the Bodies the witness checks are unchanged (`natBytes 4`).

**Why the runtime encodes (T1), not a `Term` encoder (T2).** T2 adds a constructor to `Term`, a typing rule, a
machine step, a `BigStep` rule, a `Need` count and a case in every metatheorem, and keeps `args : bytes`: the
method would still manage encodings itself and its type would still say nothing of what it sends. T1 is the
pattern the runtime already has for state and rows (typed data out, the runtime encodes at the declared type),
touches no machine metatheory, and makes a method's type state what it sends: `fuse`'s type says it invokes `take`
with an `offerTakeArg`.

**Theorems.**
- `Lang/Proofs/Data.lean` (new): `ofData_of_conforms`, `rowOfData_of_conforms`, `armOfData_of_ofData`,
  `encodeData_of_conforms`: a datum conforming to a `dataTy` type HAS bytes. `Conforms` bounds exactly what `ofData`
  requires at every leaf (`n < natLimit = 2^64`, `bytesMax`, `digestBytesMax`), pairs a record's labels as
  `rowOfData` does and names a sum's first arm as `armOfData` does. This is the answer to the card's refuter ("a
  partial encoder makes composition a lie"): on checked output the encoder is total.
- `Lang/Proofs/Call.lean`: `argsBytes_argsData` / `argsData_argsBytes` (the two directions of one codec, by
  `decodeData_eq_ok_iff`); `bodyOf_callData`, `callData_bodyOf` restated with the slot's `A`; `callData_isSome`
  gains the ONE honest hypothesis: an invoke's `args` decode at `A` (the power the typed arm takes away is
  emitting bytes that are not a value); `bodyOf_args` (the converse, from a read-back Body); `callData_conforms`
  now `Conforms d (callTy A)`; `callsOf_*` over `ks`; `runMeasured*_calls` name `x.2.calls` / `S.calls`.
- `Lang/Proofs/CallLive.lean`: `argsBytes_live` (the encoder is live on a value of a wire type); `bodyOf_live` at
  `callTy A` for `A` a wire type (`find_some`, `bodyOf_live_fixed`); `slot_conforms` at `callTy (slotInvokeArg T)`;
  `callSlotOk_dataTy`; `callsOf_go_live` / `callsOf_go_kinds` walk `ks` with the labels; `callsOf_live` keeps its
  conclusion (`DigestRefusal` is still the only refusal) with NO new premise: `callSlotOk` carries `dataTy`.
  `callSlotsOf_two` / `callSlotsOf_one` read a slot row's result off `callSlotOk` (a slot type that depends on a
  package parameter is not `decide`d). `SlotRow` and `slotRow_callsTy` are deleted.
- `Lang/Proofs/CallTeeth.lean`: `callsOf_encodes` (an invoke at `.nat` leaves with the bytes of `4`), `callsOf_no_arm`,
  `slot_bare_invoke` (`callOf ["invoke"]` is the empty slot: `badMethod`), `slot_fn_arg`; the rest at `invokeOf UA`.
- `Lang/Proofs/StdOfferFuse.lean`: `fuse_calls` returns the ENCODED deal `db` with `encodeData (offerTakeArg theta)
  deal = some db`; `fuse_atomic`, `jointLaw_sound`, `invitation_once` conclude `deal = {keys, pair, theta}` (an
  equation on the value, where they concluded a decode of bytes); `fuse_resolve` reads `callSlotOk` off the resolve
  (the slot's argument type depends on `theta`, so the old `decide` is gone).
- Past extraction (`Provenance.lean`, six statements), `Extract.runMeasured_means`, `MethodRun.runMeasured_inv`,
  `Load.runSetupWith_spec` / `runSetup_spec`: `callsOf` with the run's slots; no hypothesis gained.
  `Std.runMeasured_inv` (`Lang/Proofs/StdOffer.lean`) was a twin of `Lang.runMeasured_inv`: DELETED.

**Price (MEASURED by `gates/decls.py export` on the parent and the candidate over the 25 touched modules; the map
lines are in the commit message).** 55 RESTATES-MEANING (48 public, among them LANG-75.22's `escrow_fuse_admitted` and `escrow_fuse_resolve`, landed
while this was built and adapted to the typed deal; 7 private: the Provenance pair, four offer-proof helpers, Ledger's
`setup_eq`), 7 DELETES (`Journey.RA`, `relayArgs`, `chainArgs`; `SlotRow`, `slotRow_callsTy`; the
twin `Std.runMeasured_inv`; the private `invokeTy`), 1 moved (`Wire.dataTy`), 49 added. Hypotheses gained by a
landed theorem: ONE, `callData_isSome`'s invoke clause (§Theorems). Deployed bytes moved: none (§What re-emits).

**Plants (whole tree; hbox `wt/fable-t/logs/fable-t-plant{1,2}-{build,journey}.log`, each restored).**
- PT1 `callsOf.go` hands `bodyOf` `none` (every slot "has no invoke arm"): RED `Lang.Proofs.CallLive` at
  `callsOf_go_live` (its dependents CallTeeth, StdOfferFuse, StdOfferEscrow left unbuilt below it) and
  `Kernel.Proofs.InvokeTreeWitness` at `c1_runA` (the witness computes the Body); `lang-journey: RED (33)`: LC3, LC4,
  LC8, LD5c and every LF/LE row refused `program "calls: c0 args: no invoke arm"`.
- PT2 `argsBytes` returns empty bytes (the encoder dropped): RED `Lang.Proofs.Call` at `argsBytes_argsData` and
  `argsData_argsBytes` (dependents unbuilt) and `Kernel.Proofs.InvokeTreeWitness` at `c1_runA`; `lang-journey: RED
  (23)`: LC3/LC4 refused at the CALLEE, `program "arguments: decode … truncated 0 8"`, and LF1–LF6, LE1 refused the
  same way at the takes — the takes saw bytes that are not the value, and the tree failed whole.
- Rows standing as teeth: LC3 (the composed `n = 4` arrived), LC7 (`badMethod` for a function-typed slot), LC8 (the
  callee's `arguments:` refusal for a shape the caller's slot does not match).

**What re-emits (`lang!`).** The call-slot language changed: an `invoke` arm's `args` is a value of the slot's
declared type and the runtime encodes it. The old spellings refuse to load: `callOf ["invoke"]` in Lean is the empty
slot (`badMethod`, `slot_bare_invoke`); the bare kind `invoke` in a surface `(calls …)` is the same. No deployed
package declares an invoke slot (MEASURED: `world/` declares `(calls (transfer))` three times and no-call rows
otherwise), `callOf ["transfer"]` is byte-identical, so `world/escrow/Escrow`'s id does not move and no Store
re-geneses. Fixtures re-id: `Std.offer`, `Std.offerEscrow`, the LC Relay family, the Kernel witness relay.
The judge's generated-files and codec-vector gates (the full judge this `lang!` runs) are the control for
"nothing deployed moves".

**Critique.** A caller's slot type and a callee's argument type agree STRUCTURALLY (labels off the wire): `{x : nat}`
calls `{n : nat}`; a nominal check would need the callee's package at the caller's install, which does not exist.
The agreement is checked at the callee one step later inside the same tree, so a mistyped call costs the whole
tree (LC8) — a second check in `callsOf` would be one fact checked twice. `callSlotOk` re-checks `dataTy A` though
the iface's `wf`/`tyWire` imply it, as `methodSig` re-checks `isData`: a local premise the theorems use alone, at the
price of a redundant decide at install. The Relay no longer forwards opaque bytes; a `bytes`-typed slot still can,
and nothing deployed does. `callData_isSome` gains a hypothesis: the truth of the new language, not a lost theorem.
The matcher is kept for one more landing: the second landing deletes it (DESIGN-T §3), so for the span of one commit
the tree holds a consumer the language has outgrown.

**Meta-critique.** The first draft of the consumer (DESIGN-T §3) had `take` refuse a root call by `req.principal ≠
peer` and claimed "a session row implies a fuse". The BIAS: reading LANG-21's "a callee's principal is the calling
object" as the kernel's behaviour, when `Authority.principalOf` walks a grant to its ROOT ISSUER, the owner, so a
nested call and the owner's root call are indistinguishable in `Req` (READ-PROT-6b condition 2 had said so; the code
said so again when read). The second bias, watched for: pricing T by `git grep callsOf` (12 files, two of them
homonyms: `Host/Check.callsOf` decodes a journal segment, `Hosting/Proofs/Allowance.callsOf` is a private test
helper); the real reach was measured by the decls export, not by the name. The third, caught by the build: proving
`fuse_resolve` by `decide` only worked while the matcher's slot type was closed; with `theta` inside it the truth of
`callSlotOk` had to be READ off the resolve hypothesis, which is the honest shape (a malformed `theta` does not
install, and the theorem should not presume it does).

**Status.** L1 landed in the commit that carries the text above (`lang!`, FABLE-T, 2026-10-23). L2 landed in the
commit that carries the addendum below (`lang:`, the same session).

### LANG-77 · second landing · the fuse is one party's method, the matcher deleted (2026-10-23; FABLE-T; DESIGN-T §3; retires LANG-75.11's fork M)

**Decision.** `Std.offer`'s `fuse {keys, pair, theta, via}` is run by a PARTY as itself: it is the take's tree (own
offer, peer's offer, `offerNotNamed`, the judge) whose success retracts its own offer, logs its session row, and
invokes its PEER's `take` on `{keys, pair, theta}` of its own argument — a VALUE the runtime encodes (LANG-77) —
through the grant `via` the peer's owner gave it. `offerPeerT` names the peer as the other member of `pair`.
`offerGuard` admits `invoke fuse` as a consumer. The escrow instance's fuse pays its own leg to the peer offer's
`payTo` beside the invoke (two call slots). The matcher object, its two forwarded invokes and `x`/`y`/`viaX`/`viaY`
are deleted; `activityResultCalls` is the result-with-calls both fuses use (`activityResult` its no-call case).
Journeys §LF/§LE have two objects: B invites X (`[invoke take]` on Y), A invokes `X.fuse`; LF2/LF2r/LF3r/LF5 refuse at
`fuse` (X judges first), LF8 at the nested take (`offerNotNamed`), LF6a–c follow `via` at the nested take, LF7 is
`peer: samePeer`. LE1 moves both legs.

**Why "either", not "a third".** READ-PROT-6b §(2) said the matcher was "the fuse this ABI can express", and that T
"does not make L the honest fuse: a driver that judges θ and sends a different value is the same split as a matcher
that forwards two blobs, except the generated driver can be tied to one value by the encoder." That last clause is
the point: the fuser's run ENCODES the value it judged, so `jointLaw_sound`'s one θ is the codec's canonicity
(`decodeData_eq_ok_iff`) on the fuser's own argument — no third party holds the bytes, nothing forwarded is trusted,
and the sentence "a package other than this one, granted take, could hand the two takes different bytes" leaves the
docstrings. `rowParent` and `revisited` still make each retract its own object's and keep a party from calling itself.

**Theorems.** `fuse_run_sound` (the fuser's run: decoded `{keys, pair, theta, via}`, its reads, `NamedKey`, `JointOk`,
its own retract and session insert, ONE call `invoke p take db budget via'` with `encodeData (offerTakeArg theta)
{keys, pair, theta} = some db`, `p` the peer `peerOf` named) replaces `fuse_calls`. `fuse_atomic`, `jointLaw_sound`,
`invitation_once` are restated over the two-object tree (`fuse_tree`: the root run is the fuser's, its one call the
peer's take; `fuser` and `party` locate each run's row acts in the Turn). `take_iff_compliant`, `take_run_sound` and
the six take refusals are untouched (the take did not move). `escrow_fuse_run_sound` (two calls) and the escrow's
`escrow_retract_moves_leg` fuse case (a retract with its transfer). LANG-75.22's `escrow_fuse_admitted` is restated
over `x'.fuse`: the fuser's leg by its own run's transfer, the peer's by its take, one value; `EscrowLegMoved` takes
the party's argument; the theorem takes `x' ≠ y'` (a same-object pair is `samePeer`-refused at run time, LF7; the
theorem does not re-derive it). Proof plumbing: the take-tree helper lemmas of `Lang/Proofs/StdOffer.lean` take a
`tail` of extra argument fields, so one `offerTakeTree_inv` serves the take (`[]`) and the fuse (`[via]`);
`readsData_offer_args` (a point read without `live`/`receipt` reads nothing of the argument) couples the fuser's peer
read to the peer's own read; `callSlotsOf_two (T U)`.

**Price (MEASURED, `decls.py export` L1 vs L2 over 10 modules).** 19 RESTATES-MEANING (7 public: the three fuse
theorems, `escrow_fuse_admitted`, `escrow_fuse_resolve`, `offerTakeTree_inv`, `callSlotsOf_two`; 12 private helpers),
20 DELETES (`fuse_calls`, `lfDeal`, the matcher's private helpers, and 7 shape lemmas re-emitted public), 35 added.
Hypotheses gained: `escrow_fuse_admitted`'s `hne : x' ≠ y'`; `offerTakeTree_inv`'s `tail` is a binder, not a premise.

**What re-emits.** `Std.offer` and `Std.offerEscrow` re-id (fixtures; no deployed Store holds them). The matcher shape
is no longer generated: a `fuse {deal, x, y, viaX, viaY}` text would not install (no such method type is emitted and
the LF/LE rows do not write one).

**Plants (whole tree; hbox `wt/fable-t2/logs/l2-plant{3,4}-*.log`, each restored).**
- PT3 the fuse sends `keys` where it sends `theta` (`("theta", .get arg "keys")`): the generated package no longer
  CHECKS — `offerPackage` and `offerEscrowPackage` refuse `body does not check at its interface: payload
  @fuse…calls.c0.some` / `…c1.some` (the typed invoke arm catches the wrong value at generation, before any run);
  `lang-journey: RED (2)` (LF0, LE0 cannot build the package); RED `Lang.Proofs.StdOfferFuse` at
  `callsFuse_means`. Under fork M the same mutation (P4, a second deal) was a run-time matter; under LANG-77 it is a
  type error.
- PT4 the fuse drops its call (`noCallT` in its slot): RED `Lang.Proofs.StdOfferFuse` at `noRef_fuse` and
  `fuse_run_sound` (the calls conjunct), its dependents unbuilt; `lang-journey: RED (5)`: LF1 ADMITTED with X's offer
  gone and Y's standing and no session row under Y (half a fuse), LF8 and LF6a–c admitted (no nested take to refuse).

**Critique.** `fuse` and `take` share one tree and one judge; the fuse differs in one call and `via`. A third party can
still run a fuse if either owner grants it `[invoke fuse]`: the fuser is then that party's object, and `rowParent`
still makes the retract the fuser's own. One session row is still not a fuse (the owner's root `take`; READ-PROT-6b
condition 2); K's trigger stays. `escrow_fuse_admitted`'s `hne` is a premise the dispatch could discharge (the
nested invoke of the fuser itself is `revisited`); it is left as a premise to keep the Dispatched-based proof.

**Meta-critique.** The BIAS this landing watched for was the one LANG-75.11 recorded: designing the two-party protocol
from the session-type picture instead of the ABI. This time the ABI was read first (LANG-77's first landing) and the
consumer written to it; the proofs then forced one honest generalisation (the take tree's argument may carry more
fields than the three it reads), which the original matcher design had hidden by giving the matcher its own argument.
 L2 (the fuse as two objects: `X.fuse` judges, retracts, logs and invokes `Y.take`
with the deal it decoded; the matcher deleted) is the next commit of this session (DESIGN-T §3, §4 PT3/PT4).

**Amended (FAERIE-DOCS 2026-10-27; LANG-75.24, READ-LANGPROOFS F8 and F-7).** `escrow_fuse_admitted` no longer takes `hne : x' ≠ y'`: the peer is not `x'` because `x'` is already in the walk, and the Critique's sentence that `hne` is left as a premise is superseded by LANG-75.24. PT3's "type error at generation" holds at the fixture's `theta = [price]`; at `theta = [a, b]` the type `offerThetaTy [a, b]` equals `offerKeysTy`, so the mutation checks, and a well-typed wrong value (a swapped pair) is never a generation error.

## LANG-78 One install loader: install admits every package of the closure, and the package itself, by the admission a run's load uses (2026-10-24; FIX-LANG card 1; COLLATION-20261024 §A10; READ-LANG F-1; method R-0069)

**The defect (MEASURED by the reader, re-measured here).** `checkInstallContextual` chose its import loader from the ROOT: a root with no holes went to the closed `checkInstall`, whose `loadAll` admits each import by `admitPackage` → `Package.checkWith`, which type-checks the import's body with no hole signature. A run chooses per package: `loadLive` admits every package by `admitContextual`, which takes the holed ones through their own signature. So install refused what the run would load. A plain package importing the installed contextual hole was refused `illTyped noHole @execute.body.body.body.body.cond.arg`, a typing error inside the IMPORT, which had installed and checked. LANG-35 and Program.lean's header said install "loads its imports' closure exactly as a run does". Law 1 (two loaders deciding one closure) and law 7 (the refusal names a rule of a package that is fine).

**What changed.**
- `Lang/Program.lean`: ONE `checkInstall`. It decodes the bytes, loads the imports with `loadAllContextual` (the traversal every load uses, each package admitted by `admitContextual` at its own holes), and admits the package itself by that same `admitContextual` over those imports. Install has no row view, so a hole is prepared as its typed refusal (`unresolvedBody`), as the judge's `loadContextual` prepares it; the run prepares it from the caller's rows. `checkInstallContextual` is deleted; `program.checkInstall` is `checkInstall`.
- For a root without holes the admission is `admitPackage` (`admitContextual_closed`), the old check exactly; only a holed import is now admitted where it was refused. For a holed root the admission adds what the old contextual install skipped and every judge's load ran: the unresolved preparation (its expansion bound), the closed `checkE` of the prepared body and `checkLits`. A holed package that passed the old install and failed every later judge (INFERRED: an unresolved body past `Wire.nodeMax`) is now refused at install.

**Theorems.**
- `install_loads` (moved from Lang/Proofs/Load.lean to Lang/Proofs/LiveHoles.lean, which holds the contextual load invariant) RESTATED: if `checkInstall b = .ok ()` and the ROM cell `idb` holds `b`, `loadContextual … idb` succeeds and its package at the returned index is `b`'s. Install IS that load's last step. The old statement concluded the CLOSED `load` and was about the closed `checkInstall`, which the deployed program ran only for hole-free roots; under this landing the closed `load` of a plain package over a holed import refuses, so the old conclusion is false of the deployed check. The new one is about the deployed check and the judge's loader.
- `checkInstall_checked` RESTATED: every interface the install read is well-formed (from `loadAllUsing_inv` with `admitContextual_inv`), and a package WITHOUT holes passed the closed check over them. `install_reads` RESTATED: a hole-free installed package has a text that reads back to it. The old premise-free forms were stated on the closed check, whose every success was hole-free, so on that domain nothing is lost; a holed package's read-back was not stated before and is not now.
- `admitContextual_shape` (one admission appends the package at `acc.ids.length`, and gives the same result under any id) and `admitContextual_ifaces` (the interfaces it read; for a hole-free package the closed check over them).
- `checkInstallContextual_closed` DELETED with its definition.

**Journey (Lang/Journey/ContextualReceive.lean).** LP A10: the layer `layerOver pkg` (no holes, one import: the installed contextual ROM, one method `set`) installs (`admitted`), an object of it is created, and `set 7` runs over the closure holding the holed ROM (`admitted`, state `n = 7`).

**Plant** (hbox `wt/promo/logs/fixlang/plant1*.log`, restored): the root-based choice put back (`if p.holes.isEmpty then loadAll … else loadAllContextual …`). `contextual-journey: RED (1)`: LP A10 `refused program "illTyped noHole @execute.body.body.body.body.cond.arg"`, the reader's measured refusal. The plant breaks `install_loads`' PROOF but not its statement: refusing more keeps a soundness statement true (a closed `loadAll` success gives the contextual one, `load_closed_live`). The row is the tooth.

**What re-emits.** Nothing. No package's bytes, no wire format and no deployed package's install verdict change (no deployed package imports a holed one).

**Not done here, named (cv 01a16d4a-c0c9).** The closed/live twins of the RUN and the JUDGE (`load`/`loadAll`, `judgeOne`/`judge`, `runSetup`, `runMeasured`/`runMethod` beside the live ones; READ-LANG F-5) are untouched by one install loader: they are a restatement of every landed theorem on `runMethod`/`runSetup`, a campaign of its own. THE BAR's `requiredOf` sits on the closed twin (F-6) and stays silently absent for contextual packages until it moves.

**Critique.** "One loader" is one TRAVERSAL and one ADMISSION, with the preparation a parameter: install and the judge prepare a hole as a refusal, the run from the caller's rows. A plain package over a holed import now installs, and at run its import's holes are instantiated against the RUNNING object's rows (`loadLive … r.self`), not against the import's own objects. That was already the run's semantics for any import; LP A10 does not touch the import's holes, so it neither tests nor endorses that semantics for a layer that does. Whether a layer should be able to reach an import's hole at all is a design question this card did not settle.

**Meta-critique.** The pull was toward the smallest edit that turns the row green: make the closed branch's `loadAll` a `loadAllContextual` and keep two install functions. That leaves two checks of one fact (law 1) and the root's own admission still a hand-rolled copy of `admitContextual`'s arms. Writing install as the tail of the load is what made `install_loads` a short proof instead of a parallel argument, and what showed the old theorem had been about a check the deployed program used only half the time.

## LANG-79 The hole's coverage check refuses a missing pin `unpinned` by role, never under a verdict's name (2026-10-24; FIX-LANG card 2; COLLATION-20261024 §A11; READ-LANG F-2; method R-0069)

**The defect (MEASURED by the reader, re-measured here).** `holeCoverageCheck` (Lang/StdHole.lean), the complete-observation collector every judging method of `Std.hole` runs first, refused an unobserved support as `support0 withdrawn` / `support1 withdrawn` and an unobserved blocker as `pruned`: the judgment's own verdict names. An omitted support pin and a withdrawn fact were the same refusal; an omitted blocker pin and a live prune were the same refusal. A client that derives its pins from a refusal (Rel.lean's `rowUnpinned` docstring says clients do) is told the fact is gone when it forgot a pin. Law 7 and the minted class "refusal renders as the expected verdict". Worse, deleting the support half of the check changed no `select` output (the judge's own probe also says `support0 withdrawn` for an absent point), and no journey row ran the one method where it shows: `rejudge`, which under that deletion RECORDS a suspension of a fact that stands.

**What changed.** The collector's three refusals are `unpinned support0`, `unpinned support1` and `unpinned blocker` (the name first, then the role, as the kernel's `unpinned <id>`): the term in `holeCoverageCheck` and the model `holeCoverageOutcome` (Lang/StdHoleModel.lean), which `holeCoverageCheck_application` equates. Observed absence still reaches the judge and keeps its verdict name.

**Theorems.**
- `holeCoverageOutcome_unpinned` (new, Lang/Proofs/StdHoleCoverage.lean): the collector's only refusals are the three `unpinned` names.
- RESTATED (the refusal text): `hole_omitted_support0_refused` / `_support1_refused` / `_blocker_refused`, `hole_conflict_requires_observation`, `hole_unrelated_row_is_not_coverage` (Lang/Proofs/StdHoleCoverageTeeth.lean).

**Journey (Lang/Journey.lean, §LH).** LH7u: A selects c2 with its support f2's pin omitted: `select: refused unpinned support0`. LH7v: the same on `rejudge`: `rejudge: refused unpinned support0`. The three `hole:omitted-blocker-pin-admits` rows (select, accept, rejudge with the blocker's pin omitted) now require `unpinned blocker`, not `pruned`. LH7c (the fact pinned ABSENT) keeps `support0 withdrawn`. The rows run in the ordinary journey and in `holeObservationJourney` (the runs.tsv `--hole-omitted-blocker-pin-admits` row and the contextual journey's hole instance).

**Plant** (this session, hbox `wt/promo`, restored): the coverage check deleted (`holeCoverageCheck` returns `true`). `lang-journey: RED (5)`: LH7u `select: refused support0 withdrawn` (the old name: the plant is now visible on `select`); LH7v `admitted` (the false suspension recorded); the three omitted-blocker rows `admitted`. RED in Lean: the five teeth above and `holeCoverageCheck_application`.

**What re-emits.** `Std.hole`'s generated package bytes change (three refusal literals); it is a fixture generated at the journey, no deployed package or Store holds it. No wire format moves.

**Critique.** The name says WHICH role's pin is missing, not which cell: the client knows the candidate it asked about and reads the cell from the candidate's own `s0`/`s1`/`blocker`. The kernel's `unpinned` carries the id because it has no candidate. Two names for one condition at two layers (kernel `unpinned <id>` for a cell, this `unpinned <role>` for a row the hole reads) remain; they are one word and one meaning, not one constructor.

**Meta-critique.** The reader's evidence was that the plant was invisible to `select`; the tempting fix was to add a `rejudge` row and leave the names. That would have made the plant visible and kept the lie on every refusal. The row is the tooth; the name is the defect.

## LANG-81 The hole's support theorems are about the cell the support cites, and the deployed read supplies that binding (2026-10-24; FIX-LANG card 4; COLLATION-20261024 §A15; READ-LANGPROOFS F2; method R-0069)

**The defect (READ by the reader).** `posted_support_checked` and `revoked_support_refused_hole` (Lang/Proofs/StdHoleCells.lean, LANG-75.1's B1/B2 at the generated judge) quantified a kernel cell `g` tied to nothing: `hlive : p.live = cellLive look g` and nothing relating `g` to the support's `cell` or the point's key. Their docstrings say "the caller's pinned view holds THAT kernel cell live" and "a fact … whose cell the caller pinned at its tombstone". The statements said "if the bit equals `cellLive` of SOME `g`, that `g` is live / dead". The binding of the bit to the key's cell lived only in `cited_authenticated` (Rel.lean), at the rows grain, and no theorem composed the two. So `revoked_support_refused_hole`, instantiated at a revoked cell `b`, held for a support citing a LIVE cell `a` whose point carried `b`'s bit: it "refused `a`'s support for `b`'s revocation", and nothing in the statement could tell.

**What changed (statements only; no definition moves).**
- `posted_support_checked` takes `digestOf` and `hg : digestOf p.cell = some g` (the cell the point's key names) beside `hlive`, and concludes `digestOf cell = some g ∧ ∃ c, look g = .ok (some c)`: the cell the SUPPORT cites is live.
- `revoked_support_refused_hole` takes the same `hg` and concludes `digestOf cell = some g` beside the probe's `3` and the `support0 dead` admission: the dead cell is the one the support cites.
- `cited_hole_point` (new): on a live, non-receipt read (`relReads … = .ok v`), every slot of the rows argument that is a hole point `p` has `digestOf p.cell = some g ∧ p.live = cellLive look g` for some `g`: exactly `hg` and `hlive`, derived from `cited_authenticated` (key cell = `p.cell`, bit = the caller's pinned view of it). The two theorems' premises are now the deployed read's conclusion, not free parameters.
- `other_cell_revoked_current` (new, the plant's instance): cell `a` live, cell `b` tombstoned; a support citing `a` with `a`'s bit probes current (1), and `hg` cannot be met at `g := b` (`some a ≠ some b`).

**Strength, said plainly.** Adding `hg` is, as logic, a premise: the old `revoked_support_refused_hole` implied the new one's probe conjunct for every `g`. The probe reads only the bit, so no statement about it alone can be stronger. What is stronger is the conclusion (it names the cited cell) and the composition (`cited_hole_point` discharges `hg` and `hlive` from the deployed read). The pair is the theorem the docstrings described.

**Plant** (this session, hbox `wt/promo`, restored): the live column reads ANOTHER cell (`keyColumns`' live arm reports the liveness of the fixed id `digestOf ByteArray.empty`, unpinned, so dead). `lang-journey: RED (25)`: LH5a/LH5b record `suspended "support0 dead"` for candidates whose supports' cells are live, LH5f/LH8/LH8q refuse `support0 dead`, LH8s keeps the false suspension: supports refused for a cell they do not cite. Lean: RED first at `Lang.Proofs.Invoke` (l.409, a `keyColumns` lemma), so `Rel.cited_authenticated` and `cited_hole_point` sit in the unbuilt cone; that `cited_hole_point`'s conclusion is false under the plant (the bit is `false` at a live cell) is INFERRED from its statement. The two restated theorems alone cannot red under any code plant: their content is the binding, which only the composition reads.

**What re-emits.** Nothing.

**Critique.** `cited_hole_point` stops at the rows argument; it does not say the probe the generated judge runs reads THAT slot for THAT support (the probe matches by cell over the three slots, `holeSupportProbe`). The match is by cell identity (`holeProbePoint` compares `key.cell` with `s.cell`), and the slot's key cell is `p.cell`, so the chain closes, but as two theorems and an unfolding, not one statement at the judge's grain.

**Meta-critique.** The first draft added `hg` and left the conclusions as they were: a theorem with an unused premise, "bound" in name only, the same shape as the defect. Making each conclusion SAY the cited cell, and writing the composition that discharges the premise, is what the binding is for.

## LANG-80 A deal's session row has a patience: `Std.offer` and `Std.offerEscrow` get the activity's retire, and the take tree types each refusal at its payload (2026-10-24; FIX-LANG card 3; COLLATION-20261024 §A12; READ-LANG F-3; method R-0069)

**The defect (READ by the reader).** The session log of `Std.offer` and `Std.offerEscrow` was `activityWaiting … offerResumer` with no patience, the resumer constant `false`, and no `retire`. Every take and every fuse inserts one session row at each party, nothing could ever remove one (an upsert is `notResumer`, a retract of an unanswered row `unanswered`, and no method retracts), and the kernel refuses `relationFull` past the log's limit (1024). So an object of either package took at most 1024 deals, ever. LANG-76 fixed exactly this class for activities and left these two packages byte-identical on purpose (decisions/lang.md LANG-76 "What changed", last bullet).

**What changed (one mechanism: the activity's).**
- `Lang/StdActivity.lean`: `activityRetireMethod S rels log ld cursor` is THE retire of a log. With no cursor (`none`) it is the one edit, the log's retract at the argument key, and the log guard decides; with a cursor it is LANG-76's reading retire (log and cursor together for an unanswered row). `activityRetireTy` is its type. `activityPackage` emits `activityRetireMethod … (patience.map fun _ => (cursor, cd))`: without a patience the old one-edit term, with one the old two-edit term, byte for byte.
- `Lang/StdOffer.lean`: `offerSessionPatience = 2048` (heights, the Bell's choice in LANG-76); `offerSessionGuard theta sd patience` is `activityWaiting … offerResumer (patience := some patience)`; `offerRetireBody` is `activityRetireMethod … "session" sd none`; `offerPackageOf theta roles offerLimit sessionLimit sessionPatience budget` gains the patience and the method `retire` (index 2: `offerMethods = [fuse, post, retire, take, withdraw]`, so `take` is 3 and `withdraw` 4); `offerPackage` takes `(sessionPatience := offerSessionPatience)` and refuses `zeroPatience` (anyone could retire at once). The same in `Lang/StdOfferEscrow.lean`.
- **The blocker, fixed first (MEASURED).** With `retire` the escrow package was 66,414 bytes, past the kernel's 65,536-byte event: its install was `rejected overBound` (LE0). It was already 63,029 before this card (96% of the bound), and card 5 adds to it. 1,806 bytes of each refusal in the take tree were its annotation: `.refuse R why` typed at the method's whole result type, whose edits name every relation's row type, seven times per take and per fuse. `offerTakeTree theta roles V done` (the `R` parameter deleted) now types each refusal at what its arm would bind: `offerUnwrap T s why body` is `(λ T. body) (case s [none ↦ refuse T why; some ↦ var 0])`, the same environment for `body` as the `some` arm gave, and `offerGate` (the named check and the judge) refuses `offerNotNamed` / `sameRole` / `notCompliant` at `{}`. Same refusals, same order, same environment at `done`. The take tree went from 18,916 to 7,454 bytes; the packages from 63,029 to 42,216 (escrow) and 48,309 to 31,946 (offer) with `retire` included.

**Theorems.**
- `offer_session_retract_iff` (new, Lang/Proofs/StdOffer.lean): the session guard admits a retraction iff the call's signed `notBefore` is at least the key's plus the patience (`waiting_retract_iff` at the offer's guard).
- `escrow_retract_moves_leg` keeps its statement over every method: `retire` is a new case (`retire_core`: its one row act is a SESSION row's retract, relation 1, never an offer's), and the indices shift (`take` 3, `withdraw` 4, none past 4).
- `offerTakeTree_inv` and every theorem over `offerPackageOf` / `offerEscrowPackageOf` are restated at the new arities (one more argument: the patience; `offerTakeTree` one fewer: `R`); their content does not move. The tree's private lemmas are re-proved over `offerUnwrap_some` / `offerUnwrap_none` (new, public).

**Journey.** LF9a–c (`Std.offer`, the session row LF1 left under X) and LE6a–c (the escrow, LE1's): `retire` signed at `notBefore` 0 and at 2047 is `refused lawDenied … "session_waiting: unanswered"` with the row standing; at 2048 (the heights are set, as LB10's are) it is `admitted` and the row leaves. LF0 reads `methods [fuse, post, retire, take, withdraw]`.

**Plants** (hbox `/tmp/fixlang/plant3-*.log`, restored): (P1) the session guard's patience dropped (`none`): `lang-journey: RED (2)`, LF9c and LE6c `refused … unanswered` at the deadline; Lean RED at `offer_session_retract_iff`. (P2) the patience made 1: `RED (2)`, LF9b and LE6b `admitted` one height before the deadline; Lean RED at `offer_session_retract_iff`.

**What re-emits (lang!).** `Std.offer` and `Std.offerEscrow` re-emit (31,946 and 42,216 bytes; they were 48,309 and 63,029) and re-id: a package of the old shape has no `retire` and its `take` is index 2; nothing deployed holds either (fixtures, LANG-77). An invitation grant of `[invoke 2]` written for the old shape now names `retire`. Activity packages, `Std.hole` and the Bell are byte-identical (`activityRetireMethod … none` and `… some` are the old terms; MEASURED for the Bell by LB0/LBw).

**Critique.** The patience is a constant per package (2048 heights by default), not per deal: a deal's session row records only that it happened (nothing answers it in these packages), so its retention is the package's policy. When PROT-8's settlement answers a session row, the row's own deadline will matter and the patience belongs in the deal. The session key is still `(agent, notBefore)`: two deals at one object by one signer at one `notBefore` collide (`keyTaken`), as the reader noted; a patience does not change that. The Lang package wire still repeats every type in full: `offerUnwrap` removes the repetition the generator controls, not the representation's. A type table in `Lang.Wire` is the systemic fix (cv 01a16d6b-f492).

**Meta-critique.** The overBound refusal tempted two shortcuts: raise the event bound (KERNEL's, and PROTOCOL's frames are already tight, A3), or leave the escrow without `retire` and call the defect "Std.offer only". Measuring where the bytes were showed a third of the package was one type annotation repeated, which no other design choice needed. The refusals keep their names and order, so the shrink is a statement-preserving change, not a new judge.

## LANG-82 The escrow's judge reads the legs: an offer declares what it wants, and a fuse moves value only when each side gives what the other asks (2026-10-24; FIX-LANG card 5; COLLATION-20261024 §A4; READ-LANGPROOFS F1, F10; method R-0069)

**The defect (READ by the reader).** `Std.offerEscrow`'s judge was `Std.offer`'s: `offerJoint` reads exactly `role` and `terms`. An escrow offer declared what it GIVES (`give`) and where its counter-leg is paid (`payTo`), and nothing about what it RECEIVES. So the judge admitted a fuse paying 5 α for 1 unit of any denomination, and `escrow_fuse_admitted` ("both legs moved") held of it: the theorem was true of a one-sided gift. LANG-75.18's critique said "the legs are fixed per offer and do not depend on θ … a limit of the instance", which priced the θ/price decoupling and not this. That sentence is annotated in place.

**What changed.**
- `Lang/StdOfferEscrow.lean`: an offer's value is `{give, payTo, role, terms, want}`; `want : {amount, asset}` is the leg it asks in return, a floor (the same denomination, at least the amount). `post` takes and stores it. `escrowFairT`, under the judge's `ok` arm, decides both directions: what the peer gives meets this offer's `want`, and what this offer gives meets the peer's `want` (`escrowLegMeetsT`: asset equal, `want.amount ≤ give.amount`). Each party's judge checks both, as each checks both boxes.
- `Lang/StdOffer.lean`: `offerGate theta roles V fair` and `offerTakeTree theta roles V fair done` take the instance's own compliance `fair : Option Term`; `Std.offer` passes `none` (its terms are unchanged), the escrow `some escrowFairT`. A failed check refuses `unfairLegs`, typed at `{}` (LANG-80's size discipline). The refusals, in order: `offerUnpinned`, `noOffer`, `peerRowUnpinned`, `noPeerOffer`, `offerNotNamed`, `sameRole`, `notCompliant`, `unfairLegs`.
- The module header is rewritten: it named a matcher deleted in LANG-77 and said `offer_guard` admits a retract only from `take` or `withdraw` (it admits `fuse` too).

**Theorems.**
- `LegsMatch o q` (the spec), `escrowFair_eval` (the term evaluates to a Boolean that is `true` iff `LegsMatch`), `escrow_fair_true`.
- `offerTakeTree_inv` RESTATED: a premise that `fair` evaluates to a Boolean in the `ok` arm's environment, and a conclusion that it evaluated to `true`; `body_unfair` (private) is its refusal.
- `escrow_take_run_sound`, `escrow_fuse_run_sound` RESTATED: `LegsMatch o q` beside `JointOk`.
- `EscrowLegMoved … P o q` RESTATED with the own offer `o` and the peer read `q` as PARAMETERS and `LegsMatch o q` among its conjuncts.
- `escrow_fuse_admitted` RESTATED: `∃ ox oy, EscrowLegMoved … x' ox oy ∧ EscrowLegMoved … y' oy ox ∧ value sums`. The two parties' offers are ONE pair: the offer `x'` read under its peer is the one `y'` consumed, and vice versa (READ-LANGPROOFS F10's coupling, proved as `jointLaw_sound` proves it for `Std.offer`: `methodReads_offer`, `peer_of_pair`, `readsData_offer_args`, now public). So `x'` receives `oy.give` at `ox.payTo` and it meets `ox.want`; `y'` receives `ox.give` at `oy.payTo` and it meets `oy.want`. "The admitted legs are the ones each offer declared."
- `escrow_shape`, the post's theorems (`escrow_post_run_sound`, `post_core`, `post_arg_cases`) carry `want`.

**Journey (Lang/Journey/OfferEscrow.lean).** Every post declares its `want` (X: gives 5 α, wants 7 β; Y's offer 0: gives 7 β, wants 5 α). LE1 (a fair deal) moves both legs as before. LE7: Y's offer 3 (compliant with X's box at price 9) gives 1 β where X wants 7 β: `fuse: refused unfairLegs`, nothing moves. LE7b: Y's offer 4 gives 7 β but wants 6 α where X gives 5 α: `fuse: refused unfairLegs`.

**Plant** (PLANT-RESULTS).

**What re-emits (lang!).** (SIZES). `Std.offerEscrow` re-emits and re-ids: an old offer row has no `want` and does not decode at the new value type; nothing deployed holds one. `Std.offer`'s bytes: (OFFERSIZE).

**Critique.** `want` is a floor in one denomination, fixed per offer; θ still moves nothing (the legs do not depend on the agreed price, as a real DvP's would: `θ.price × quantity`). A party overpays only by its own declaration (its `give`). The fairness is judged at the take, so a root `take` by Y's owner (no fuse, READ-LANG F-8 / Q-1) is still judged against the offer Y read under its peer, but the peer's leg does not move in that case: one session row is still not a fuse.

**Meta-critique.** The pull was to state "the judge reads the legs" by adding `LegsMatch` to each party's `EscrowLegMoved` and stop. Each party's judgment is about ITS READS; without the coupling, "X received what it wanted" would be a statement about the offer X read, not the offer Y paid from. The coupling was the reader's F10, "a statement gap, no attack"; here it is what turns the judge's check into a statement about what moved.

## LANG-86 A generator is a package whose method installs a package: `install` is a call an object may make, and `Std.headGenerator` is `Std.head` as an installed object (2026-10-26; FABLE-META, axis 1 of FRONTIER-AXES-20261026; design `redregg/work/promo/DESIGN-META.md`; with KERNEL-75)

**The question (Ember's, verbatim in the axis).** What if packages could generate packages, the generators were themselves nano programs judged by the kernel, "install a generator" were a Turn, and a generated package carried a receipt of its generation — a self-describing, self-extending World in which the Std library is installed objects rather than Lean-emitted constants?

**The answer, built at its first rung.** A GENERATOR is an ordinary package with a method whose calls row holds one slot of the new call arm `install : rec {pkg : bytes}` (`Lang.installArm`, in `callArms` between `grant` and `invoke`). The method computes package bytes and returns `install b`; the kernel's tree derives the call as the object (`effect_as_signed`) through the one `install` receiver, which takes no authority from its actor, runs `checkInstall` on the bytes at the signer's pinned view, and bears the ROM cell `romIdOf b` (KERNEL-3). So a generation is a nested call of a Turn, re-derived by every follower, and THE TURN IS THE RECEIPT: its journal row names the generator object and the argument; the cell's id is the content digest of what the method returned; `generate_run_sound` says what the method returns; `tree_package_checked` (KERNEL-75) says the kernel checked it. No new cell kind, slot, right or receiver.

- `Lang/StdGen.lean`: `installSlot := callOf ["install"]`; `generatorOf b doc`, the CONSTANT generator (one method `generate`, argument `rec {}`, state `rec {}`, no laws) whose run returns `install b`; `headPackageBytes` (the value `Protocol.Foreign.headPackageBytes` is); `headGenerator := generatorOf headPackageBytes …`: `Std.head` as an installed object, byte for byte, which the journey checks as one digest (the cell a generation bears is `Protocol.Foreign.headPackageId`).
- `Lang/Call.lean`: `callData (.install pkg)`, `bodyOf`'s `install` arm, `callFits (.install pkg) = pkg.size ≤ bytesMax` (a package an object installs is at most a `bytes` value: 128 KiB; `Std.offerEscrow`, the largest, is 42,216 bytes).
- `Lang/Proofs/StdGen.lean`: `generate_run_sound`: for `generatorOf b doc` read at `pkg`, every admitted run of method 0 returns `[.install b]` and no row acts, whatever the state, argument, view and budget (the `take_run_sound` route: `runMeasuredLive_leaf_closed`, `runMeasured_inv`, `runSetup_spec`, `load_top`, `apply4_method`, `extract_means`, `means_get`, `means_deterministic`). `generate_resolve` and `generator_body` are `rfl`. That the generator has bytes is GN0's row (no `native_decide`).
- `Lang/Proofs/{Call,CallLive,CallTeeth}.lean`: the arm in `bodyOf_callData`, `callData_conforms`, `bodyOf_live_fixed`, `find_some`; `install_reads`: an install datum reads as `.install` of its bytes.
- `Lang/Journey/Gen.lean` (GN0–GN5, in `lake exe lang-journey`): GN0 B installs `Std.headGenerator` and creates G; GN1 `G.generate` is admitted, the Turn bears exactly one cell, a package cell whose id is `headPackageId`, and `Std.headPackageBytes == Protocol.Foreign.headPackageBytes`; GN2 the generated package runs (a head object of that id, an honest post); GN3 a second generation is `idTaken` (generation is idempotent up to refusal: Unison's property through `romIdOf`); GN4 a generator of bytes that are not a package: `refused program decode …` at the nested install, nothing born, the World unchanged (the floor of `tree_package_checked`, run); GN5 a generator of a package naming a method it lacks: `program noMethod …`.

**Hygiene, and why the reader's embarrassment is the wrong target here.** A generated body is a closed de Bruijn term whose `ref i` name its OWN imports; the generator's run has no names, so nothing in the generated code can capture the installer's bindings; the generator's data enters the code only as literals, and digest literals are re-checked at install (`checkLits`, LANG-38). The hand-counted indices HOLISTIC-LANG §3.2(iii) named are a fact about AUTHORING the Lean generators, which stands; the wire they emit is what makes staging hygienic for free.

**What the kernel checks.** Nothing new: the same `checkInstall` as a member's install, at the signer's pins, before the birth; typed and bounded by the package wire; a generator that emits an ill-typed package fails the whole Turn by name (GN4, GN5).

**Where the staging stands against the field (DESIGN-META §1.1).** Template Haskell's choice (untyped splices checked after, by the ordinary checker) and not MetaML's (a static type of code); Racket's phases as Turns (the generation Turn is phase 1, the generated package's runs phase 0, the receipt the boundary); Lean's elaborator/kernel split with the `.ob` reader as the elaborator and `checkInstall` as the kernel; Unison's content addressing by `romIdOf`.

**The price.** TOPLEVEL-SPEC's five claims: no statement moves, no premise is added (a package cell has no owner and never changes; B1 is about changes). The generator-spec tier gains PROVENANCE OF CODE (DESIGN-META §4.3). Proofs gaining a case: `tree_zeroBorn` (install), `bodyOf_callData`, `callData_conforms`, `bodyOf_live_fixed`, `find_some`. No wire byte moves: `callOf kinds` filters the arms by name, so no deployed method type changes (`grep -rho "(calls [^)]*)" world/` names only `transfer`); the surface's `(calls (install))` works unchanged through `callOf`.

**What re-emits.** Nothing. What refuses to load: nothing.

**The one way it is wrong (DESIGN-META §6).** It stages at the BYTE level: a generator's type says it emits bytes, not a package; composing two generators' outputs is composing bytes. That is the "fixed-arity rows as lists" workaround at the meta level, chosen because a type of code needs a bounded sequence type nano lacks (axis 7), and named so it is replaced when the language gets one. Second: a nested call returns nothing and a method cannot hash, so a generator cannot `create` an object of what it bore in the same Turn (two Turns, or a `createOf` arm with `create`'s authority question).

**Next (rung 1, its own `lang!` card).** Parameters spliced into the package tree need the codec's framing as primitives: `len : bytes → nat`, `varint : nat → bytes → bytes`, `be : nat → nat → bytes` (and `idBytes : digest → bytes` to name a member in an emitted law); each a new term tag, so the package wire version moves 5 → 6, every fixture re-emits by its version byte, `headPackageId` moves, the devnet re-genesises: priced in DESIGN-META §3.3. With them `Lang.Quote.packageTerm : Package → Term` with `eval (packageTerm p) = encodePackage p`, and `Std.bounded` as the first template generator. Structural generators (a plan list, a quorum's members) wait for lists.

**Critique.** `generatorOf` is a constant function wearing a method; the mechanism it exercises (the arm, the nested check, the id, the receipt) is the landing's content and the generator is its floor inhabitant. `generate_run_sound` says what the run returns and not that the returned bytes are `headPackage`'s: that is `headGenerator`'s definition plus GN1's digest, a definitional fact and a row, not a theorem about `decodePackage headPackageBytes`. A generator object has no law tonight; `Std.quorum` over a counter is the obvious one and was not written.

**Meta-critique.** The temptation was to land rung 1's primitives tonight so the first generator could take a parameter; that would have put a wire flag day under the judge's one question (may an object install, and is it checked as a member's) and made two questions of it. The other temptation was a `code` type; the design prices it and says why bytes first.

## LANG-87 Rung 1 of generators: three payload writers (`u64be`, `sized`, `dsized`), a quoter whose output is proved to be the encoder's bytes, and the first template generator `Std.boundedGenerator` (2026-10-26; FABLE-META-2, axis 1; design `redregg/work/promo/DESIGN-META.md` §3; a `lang!`: package wire 5 → 6)

**The question.** Rung 0 (LANG-86) installed a CONSTANT: `Std.headGenerator`'s method returns `install` of a byte
literal. A generator worth the name takes a PARAMETER and writes a package whose text carries it — a bound, a doc,
a member's id. The package wire is one concatenative `Codec.Tree` (`tag ‖ varint |p| ‖ p ‖ varint k ‖ kids`), so a
method with `cat` can assemble any tree from literal fragments EXCEPT the three payloads a parameter changes: a
`nat` literal's eight big-endian bytes, a `bytes` literal's length-prefixed bytes, a `digest` literal's. The core
had no `nat → bytes`, no length as a number, and (LANG-38) an id was a type never made from bytes — nor, until now,
made INTO bytes.

**The answer: three payload writers, one per scalar literal kind, each a deployed codec's `put`.** `Prim` gains
`u64be : bytes → nat → bytes` (`Stream.u64be.put`: the operand appended as a datum's eight big-endian bytes, a `nat`
literal's payload), `sized : bytes → bytes → bytes` (`Stream.bytesV`'s put: a varint length then the bytes — a
`bytes` literal's payload, a label's, a refusal name's, a doc's), `dsized : bytes → digest → bytes` (the same for an
id: a `digest` literal's payload). Each is BINARY and buffer-first — `Term.prim` is binary everywhere (the `primL`/
`primR` frames, the checker, `BigStep`), so a unary `len`/`idBytes` would have needed a dummy operand; an append
whose left operand is the buffer being built is the natural binary shape and is exactly how the codec's own `put`
is written (`Codec/Stream.lean`: `put v buf` appends). A `bool` parameter needs no writer: `ite` over the two literal
nodes. Each writer is charged the bytes it writes, as `cat` is (`primBytes.written`: its result's size; LANG-64's
one word per tick), refuses `tooLarge` past `bytesMax` and then walks nothing (`appended`); none can be `stuck` on
typed operands (`appended_sound`, in `primEval_sound`). What there is NOT: a `len : bytes → nat`, a standalone
`varint`, a raw `digest → bytes`. The first two are not needed by any template (a template's child counts and
closed payload lengths are constants; a parameter's length is written by `sized` itself); the third is refused on
LANG-38's ground made stronger: **an id's bytes enter a byte string only as a codec payload, never raw**, so a
program can name a member in a package it writes and cannot smuggle an id into a key or a value.

**The quoter (`Lang/Quote.lean`), and what it means.** A TEMPLATE is an open `Term`: a free variable (`var i` at
or past the binders above it) is a stage-1 parameter (`Quote.Param`: its scalar type and the term that fetches it
where the generator runs, e.g. `get (var 1) "max"`). `quoteTerm ps d buf t` is a nano term appending to `buf` the
wire bytes of `t` with each free variable replaced by its parameter's LITERAL — cross-stage persistence, as MetaML
lifts a stage-1 value into a bracket. Every CLOSED subterm is one `cat` of one literal fragment (written by the
ordinary encoder at authoring time); only the nodes on the path to a parameter are built from their frame
(`Quote.frame`: `Tree.putD`'s own prefix, not a second spelling of the codec) and their children. `quotePackage ps
buf p` writes `encodePackage`'s bytes of a package whose body is a template: version byte, the package node's
frame, the closed sections, the body quoted, the closed sections after it — three fragments and the body. The
specification is `Term.fill vals d t` (free variables replaced by the values' literals; `fillPackage`), and the
theorem is `Quote.quotePackage_sound` (`Lang/Proofs/Quote.lean`): under `Params` (each parameter term evaluates to a
scalar of its declared type), whenever `encodePackage (fillPackage vals p) = some B`, the quoted term appends
EXACTLY `B` to any buffer (`Appends`: for every buffer meaning `b` with `b ++ B` within `bytesMax`, the term means
`b ++ B`). One induction over the template (`quoteTerm_sound`, mutual with the field and term lists), every case the
same step — a node's bytes are its frame then its children's, and `Appends.comp` composes; `putD_of_fits` lets a
closed subtree written at `depthMax` stand for the same subtree at the depth its node leaves it; `appends_param`
is the four writers. The quoter names no closure package (`noRef_quotePackage`), so the receiver runs it as
written. Hygiene stays the wire's: a parameter enters the generated code only as a literal node; a `var` of the
template under its binders is a bound variable of the GENERATED program and is written as one.

**The first template generator.** `Std.boundedWith S f maxT` is `Std.bounded` with its bound a TERM at the law
clause's depth (4: the law's three binders and the arm's); `Std.bounded S f max := boundedWith S f (natT max)` —
one definition. Its refusal is now `"{f} over the bound"`, not `"{f} over {max}"`: a nano program cannot write a
number as text, and the bound is in the law's text (a describe prints it) and in the generation's receipt (the
Turn's argument). `Std.boundedPackageWith r f maxT` is a record state `r` under that law with a `set` method
writing the state whole; `boundedPackage r f max` its instance. `Std.boundedGenerator r f` is a package whose
`generate {max : nat}` returns `install` of `quotePackage [maxParam] "" (boundedPackageWith r f (var 4))`.
`generate_bounded_sound` (`Lang/Proofs/StdGen.lean`): every admitted run of `generate` whose argument decodes to
`{max = m}` returns `[install B]` with `encodePackage (boundedPackage r f m) = some B` — **the nano generator IS
the Lean generator at the receipt's argument, byte for byte** — through `fill_boundedPackage` (the template filled
at `m` is `boundedPackage r f m`, by `simp`), `quotePackage_sound`, and the method-run machinery of
`generate_run_sound`. So the law's theorem `bounded_spec` (the new value of `f` is at most `max` in every admitted
change) is about what the kernel checked and installed, for the `max` the receipt names, with no Lean in the
member's hands.

**Journey (`Lang.Journey.Gen`, in `lake exe lang-journey`).** GN6 B installs `Std.boundedGenerator {n : nat} n`,
creates G, and generates at 100: admitted; the Turn bears one package cell whose id is the content id of
`encodePackage (boundedPackage {n : nat} n 100)` — the deployed run of `generate_bounded_sound`. GN7 B creates an
object O of THAT id at n = 0 and sets n = 50: admitted. GN8 B sets n = 101: refused `lawDenied bounded: n over the
bound` by name — the generated law holds at the generated bound. GN0–GN5 unchanged. Teeth (`Lang.Proofs.Teeth`):
`u64be_writes`, `sized_writes`, `dsized_writes` (the bytes, after the buffer);
`Lang.Proofs.WireTeeth.prim_codes` (was `lenLe_code`): codes 11–14 are `len<=`, `u64be`, `sized`, `dsized` and 15 is
none.

**Wire (the `lang!`), every byte.** `Bounds.packageWireVersion` 5 → 6: primitive codes 12, 13, 14 under term tag 7
turn three refused boundary rows into reads. Codec labels `lang/package/5` → `/6`, `lang/package-version/5` → `/6`
(`packageCodec_label` ties the label to the version). `gates/codec-vectors.tsv` re-drawn by `codec-vectors --write`
(the sites' names moved), `--check` ok: the package site gains the three writer rows (`primRows`, codes 12–14) and
its boundary row moves from code 12 to 15; every other package row differs only in its first byte 05 → 06; the
version site's rows are 06/05 (were 05/04); the LANG-59-era row's refusal now names `lang/package-version/6`. A
version-5 package refuses `lang/package-version/6` before its tree is read: never reinterpreted (row LV, LV1–LV3 print
version 6). No other site moves. Rust: the primitive table is Lean's (the client decodes no terms; `grep lenLe
client/` finds nothing); nothing in Rust moves. The surface reader and printer know the three words (`u64be`,
`sized`, `dsized`).

**What breaks, what re-emits.** Every package id (the version byte): every journey World re-runs from genesis;
`Protocol.Foreign.headPackageId` moves (it is computed, not pinned; `Std.headGenerator` still bears it, GN1). Every
Store re-geneses (none deployed). The worstcut-rows bench's base World holds the installed Bell under a new id, so its trie
keys differ: 55 more trie hashes over 16448 steps (20.184 → 20.187 per step, `gates/waste.tsv`, the WASTE line). The `.ob` fixtures are source and re-encode at read. Nothing outside the
journeys holds a package id.

**The price, in the spec's terms.** TOPLEVEL-SPEC's claims: no statement moves, no premise is added. Theorems gaining
a case: `primEval_sound` (three writer cases through `appended_sound`), `LawVal.prim`, `primEval_lits`,
`primEval_noRefVal` (each by unfolding `appended`); `bounded_spec` and `noRef_bounded` carry the new refusal text.
`generate_bounded_sound`'s premises, named: the Lean generator's package has bytes (`encodePackage … = some B`:
labels within bounds, the tree within `depthMax`) and `B.size ≤ bytesMax` — the honest limit of staging at the
BYTE level: a generator writes a package the language can hold as one value (128 KiB; `callFits` says the same of
an install). Cost: the bounded generator's method is three `cat`s of fragments plus the path to the bound (a
record field, a case, three arms each one `ite` and one `u64be`), charged per word copied: a few thousand ticks at
a 2 KiB package.

**Critique.** The quoter is a mirror of `termTree` with eighteen cases, and its theorem is the only thing that
makes it not a twin: a certified compiler against the one encoder, which is the sanctioned shape (the Std generators
are the same shape at the term level). `fill_boundedPackage` is proved by `simp` over the law combinators, which is
a proof about one template; a general "a template's free variables at the clause depth" lemma would serve the next
generators (`allowlist` with a `digest` parameter, `windowed` with two `nat`s) without a `simp` each — write it when
the second one comes. `Params` is a per-index relation (`ParamAt`) rather than `List.Forall₂` so the var case needs
no library lemma; it is the less idiomatic of the two.

**Meta-critique.** The pull was to land the predecessor's four primitives as designed (`len`, `varint`, `be`,
`idBytes`) and discover their arity problem in the proofs; reading `Term.prim`'s binary shape FIRST turned four
primitives of mixed arity into three binary appends that are the codec's own `put`s, and deleted `len` and `varint`
as unneeded by any template. The second pull was to keep `"{f} over {max}"` and let the nano generator emit a
DIFFERENT law text from `Std.bounded`'s; that would have made two bounded laws (a twin) and a theorem about the wrong
one. The number left the name instead, and `bounded` became one definition with a term-shaped bound.

**Next (rung 1 continued, then rung 2).** `Std.allowlistGenerator` (a `digest` parameter from `req.agent`:
authority by naming, written by `dsized`); `createOf` (generate and instantiate in one Turn, DESIGN-META §6.3); a
quorum-gated generator (laws on a generator object, no new machinery). Rung 2, structural generators, waits for a
bounded sequence type (`Ty.seq`, axis 7, TYPES's column): then `code` over it (DESIGN-META §6.2) replaces bytes as
the type of what a generator emits.

## LANG-88 A generator whose output names its invoker: `Std.ownerGenerator` takes no argument and installs the one-member allowlist of the member who generated, read from the Turn's request (2026-10-26; FABLE-META-2, axis 1; DESIGN-META §8; a `lang:`, no wire change)

**What.** `Std.allowlistWith S idT` is the one-member allowlist with its member a TERM at the law clause's depth
(`allowlistLaw S [i] = allowlistWith S (digest i)`, rfl). `Std.ownedPackageWith r idT` is a record state `r` under
that law (`owner`) with `set`; `ownedPackage r i` its instance. `Std.ownerGenerator r` has one method, `generate {}`,
whose body quotes the template at the free variable `var 4` with the parameter `agentParam = ⟨digest, get (var 0)
"agent"⟩` — the generator's own REQUEST's `agent`, the signer of the generating Turn — written into the law by the
`dsized` writer (LANG-87) as a digest literal, which `checkInstall` re-checks against the World (`checkLits`).
`generate_owner_sound` (`Lang/Proofs/StdGen.lean`): every admitted run by request `rq` returns `[install B]` with
`encodePackage (ownedPackage r (bytesOf rq.agent)) = some B` (within `bytesMax`). The proof is `generate_bounded_sound`'s
with the parameter read from `reqData` instead of the argument (`sel_toVal` on the request's `agent` field) and
`fill_ownedPackage` (the template at `i` is `ownedPackage r i`, by `simp`).

**Why it matters.** DESIGN-META §2.3 said a generator CAN bake the signer's id into a law — authority by naming — and
that `checkLits` keeps it honest. This is that, with the receipt as the ONLY input: a member invokes `generate` with
no argument and gets a package that admits them by id and no one else; the Turn's journal row (the signer) is the
whole provenance of who the package names. The `dsized` writer gets its deployed use; three writers, three
generators' worth of parameter kinds remain (`bytes`, `bool`) for a later card.

**Journey (`Lang.Journey.Gen`, in `lake exe lang-journey`; the session gains a second founder A).** GN9 B installs
`Std.ownerGenerator {n : nat}` and generates with no argument: admitted; the Turn bears one package cell, the cell of
`encodePackage (ownedPackage {n : nat} B)` (1613 bytes) — B's id read from the Turn's request. GN10 B creates an
object O of it and sets n = 7: admitted. GN11 B grants A invoke on O; A sets n = 9 through the grant: refused
`lawDenied owner: not on the allowlist` by name (a stranger never reaches a law; the grant makes A reach it, and the
generated law refuses A by name).

**Price.** No statement moves, no premise is added; no wire byte moves; nothing re-emits.

**Critique.** `fill_ownedPackage` is the second `simp`-per-template proof (LANG-87's critique named it); the general
lemma — a template whose free variables sit at the clause depth fills to the Lean generator at the literals — is now
owed by the third template. `generate_owner_sound`'s proof duplicates `generate_bounded_sound`'s 60 lines with one
parameter changed; a `generate_sound` over any `(template, params, fill)` triple is the refactor the third generator
should land instead of a third copy.

**Next.** `createOf` (generate and instantiate in one Turn, DESIGN-META §6.3; a KERNEL receiver arm: coordinate with
TRUST's column); a quorum-gated generator (`Std.quorum` over a generator object: k of n members approve a
generation); rung 2 over TYPES's `Ty.seq`.

### LANG-88.1 One theorem for every template generator: `Std.templateGenerator A ps p` and `generate_template_sound` (2026-10-26; FABLE-META-2; the refactor LANG-87's and LANG-88's critiques named)

`Std.templateMethod A ps p` is the one method a template generator has (`generate : A`, the body quoting `p` at `ps`);
`Std.templateGenerator A ps p doc` the package; `boundedGenerator` and `ownerGenerator` are its two instances, byte for
byte what they were (GN6–GN11 unchanged). `generate_template_sound` (`Lang/Proofs/StdGen.lean`): every admitted run of
`generate` returns `[install B]` with `encodePackage (fillPackage vals p) = some B` and no row acts, whenever the
parameters mean `vals` in the method's environment `[req, arg, state, rows]` — for every closure and decoded argument
the run produces — and `B` fits a byte value. `generate_bounded_sound` and `generate_owner_sound` keep their statements
and become ten-line instances (the parameter's meaning, by the argument's decoding or by `reqData`, and the fill lemma).
Deleted: the two per-generator method definitions and six per-generator lemmas. Price: none; the general theorem's
`Params` hypothesis quantifies over the run's closure and data, which is exactly what each instance can supply.
The third generator (a quorum-gated one, or any template with a `bytes`/`bool` parameter) now costs a template, a
fill lemma and a `Params` proof.

## LANG-83 The document: a section is a `Std.hole` at `bytes` whose candidates are members' posts, justified by their grants, selected by an editor, withdrawn by name on revocation; its refusals name the justification that failed (2026-10-26; FABLE-CTX; design `redregg/work/promo/DESIGN-CTX.md` §2.3, §4, S0 + S1; method R-0069)

**Ember's ask.** "Elaborating the contextual theory thoroughly into the most powerful possible instantiation of itself seems reasonable." The design memo answers it (what the theory is: justified instantiation of contextual types inside a replicated state machine; the SLOT as the one object the ROM hole, the activity's waiting row, the offer, the law list and the package link all inhabit; the top clause CONTEXTUAL INTEGRITY ∧ REPAIR as a clause of INTEGRITY with its floor). The first two steps of its sequence land here, because together they make the top clause inhabited by a run a member can see, and neither needs the kernel.

**S0 (landed `18cd38b`, `lang:`).** A hole's refusal NAMES THE JUSTIFICATION THAT FAILED. `HoleRefusal` (`Lang/LiveHoles.lean`): `unpinnedRow rel key` (a row of the hole object the caller did not pin), `unpinned (pins)` (every cell support the caller did not pin), `supportMoved hole position pin`, `derivationMoved hole (pins)`, `supportDead hole (pins)`; `selectHole` throws the FILTER of the failed `all`, so the list is never empty when thrown; `SupportPin.wire` prints `row:REL:KEYHEX:VER` / `cell:IDHEX` (`hexOf`: two pushes a byte, no list). Before, `holeUnpinned` named nothing and `holeSupportDead 0` named the hole and not the cell, while `Lang/Rel.lean`'s `rowUnpinned` already said clients derive their pins from refusals. No statement over `selectHole` changed (the thrown term is not in them); the three LiveJourney teeth name the pin or cell they refuse on; 9 declared changes of meaning. No package byte moved. Journey: the LP rows read the coordinates through `Receive.submit` (`holeDerivationMoved 0 row:2:<hex>:0`, `holeUnpinnedRow 2 <hex>`, `holeSupportMoved 0 1 row:2:<hex>:0`).

**S1 (this landing, `lang:`).** The DOCUMENT, the charter's approved "documents" demonstration and the second running contextual instance beside the Bell.
- `Lang/Journey/Doc.lean`: a SECTION is `Std.hole .bytes clause` (a text of at most 2000 bytes). Its candidates are texts members `propose` (anyone granted it), each justified by a support naming the poster's own grant cell (a `facts` row the poster `post`s, read LIVE since LANG-75.1); its chooser is the editor (`select`); a revoked contributor's text is recorded `suspended "support0 dead"` by `rejudge` and a `select` of it is refused `support0 dead`; another contributor's text is selected: the document repairs and nobody re-installs anything. `texts` emits the generator's packages as text — the three helpers, then the root linked by the helpers' DEPLOYED ids (KERNEL's `romIdOf` under CODEC's deployed Env, what `nd install` prints) — and `lang-journey --write DIR` writes them.
- `world/doc/Section.lib0`, `.lib1`, `.lib2`, `Section`: the shipped texts (78,739 / 73,681 / 29,585 / 38,479 chars; 61,652 / 57,537 / 23,287 / 29,776 package bytes, each under `eventBytesMax`). Row DC0 reads them from disk in the default journey and refuses a text that is not the generator's (one copy, as the Bell's LB0). Rows DC1–DC9c run the section's life through `Receive.submit` on the generator's packages linked at the Sim's ids: install, create (editor A), grant B post+propose, B's fact and text (`verified`), A selects (state `selected`), A revokes, A rejudges (`suspended "support0 dead"`), A's select refused `select: refused support0 dead`, B's new grant, fact and text, A selects it.
- `client/tests/doc.rs` (`gates/runs.tsv` row `cargo:client:doc`, `nobin RED`): the same life by two REAL members over `nd` — A the founder and editor, B joined over a signed invitation as `join.rs` joins, each with its own follower — on the SHIPPED texts: `nd install` ×4, `nd create --pkg`, `nd grant OBJ B invoke:2,invoke:3`, B's `nd invoke … --via`, B's `propose … --pin facts …`, A's `select … --pin candidates … --pin facts …`, `nd read OBJ candidates 8` showing `verified` then `suspended … support0 dead`, `nd revoke`, the refused select naming `support0 dead`, the repair. MEASURED on hbox: `cargo test -p nanodregg-client --test doc` passes (1 test, 5.6 s), two followers and one writer over real sockets; the first run found that `read OBJ ?` prints the state's TYPE (the selected candidate is read from `read OBJ`, the state printed by the one printer).

**Theorems.** None new, on purpose: the section is `Std.hole`'s package at a value type, and `Std.hole`'s theorems (`posted_support_checked`, `revoked_support_refused_hole`, `cited_hole_point`, `holeDecision_verified_iff`) are its theorems. The design's statement over the whole (CONTEXTUAL INTEGRITY ∧ REPAIR, `Spec/Claims.lean` B4/B4′) is S5's, after the sequence; the DC rows and the cargo row are its INHABITED half today.

**Plants (MEASURED, hbox `wt/fable-ctx`, each restored byte-identical).** (P0) one byte appended to `world/doc/Section`: DC0 `world/doc/Section is the generator's text` FAIL, `lang-journey: RED (1)`; the three helpers' DC0 rows stay green. (P1, LANG-75.1's (c), not re-run) the judge ignoring `live` records B's text `verified` after the revoke: DC8 is its row at `bytes`.

**What re-emits.** Nothing deployed: `Std.hole`'s generator is unchanged, the shipped texts are new files, no wire moves (`lang:`). A deployed World that wants a document installs the four texts in order.

**Critique.** One section per object: a document of K sections is K objects, and "the document" is the reader's composition of them; the K-slot `Std.hole` (several `selected` fields) is named in DESIGN-CTX §4 and not built. The support's `pin` field is the poster's claim (the grant's own id here) and only the cell's LIVENESS is read (LANG-75.1's two pins); a contributor could cite any live cell it may pin, and the clause does not say "the cell is YOUR grant" — contract-by-law (DESIGN-CTX §2.5a, S2) is where a support says what the cell must be. The shipped texts are generated files checked by a journey row, not by `gates/generated.tsv`'s `--check` (the journey's DC0 is the one check; `--write` is the one writer). The cargo row runs at convergence, not in the fast judge.

**Meta-critique.** The pull was to call the LH rows "the document" and ship nothing: the readers' finding was that nothing DEPLOYED reads the contextual layer, and a Sim row is not a reader. The second pull was the opposite: build the K-slot generator first. The smallest thing a member can see is one section over `nd`, and it found two things the Sim did not state: the editor's select must pin the SUPPORT'S cell (the Sim's `pinsOf` had hidden it under "every cell pinned"), and `nd`'s `--pin` is the whole read-set discipline a member has (no pin, no judgment).

## LANG-84 Contract pins: a hole's support may demand that the cell it cites be GOVERNED by a named law or RUN a named package, read off the cell the kernel holds; a relaw that drops the law withdraws the fill by name (2026-10-26; FABLE-CTX; DESIGN-CTX §2.5a, S2; the package wire moves to version 7; method R-0069)

**What a program could not do.** A candidate that links a hole to another member's object could justify the link by the object's grant being live (`SupportPin.cell`, LANG-75.1): a fact about AUTHORITY, nothing about what the object IS. P8's providers are selected that way. A program whose holes are filled by other members' programs under a CONTRACT needs the support to say what the cell must be, and the kernel already holds the two things it can say without a proof system: the laws in force on a data object (its law slots, `lawBase ≤ k < stateBase`, consulted on every move of it: B3) and the package a programmed object runs (`slotPackage`, fixed for ever: `audit_package_fixed`).

**What changed.**
- `Lang/HoleROM.lean`: `SupportPin.cellLaw (id law)` — the cell is live AND `law` (a package id) is among its laws in force; `SupportPin.cellPackage (id pkg)` — the cell is live AND runs `pkg`. `Lang/LiveHoles.lean`: `cellGoverned look g law` (the law slots hold `law`'s bytes), `cellRuns look g pkg` (`slotPackage` holds `pkg`'s), `supportLive`'s two arms, `SupportPin.cellOf` (the cell a pin names; `supportObserved`, `rowSupportHolds`, `supportPinned` read it), `SupportPin.wire` (`cellLaw:IDHEX:LAWHEX`, `cellPackage:IDHEX:PKGHEX`). `Lang/Program.lean`: `SupportPin.cellIds` names both digests, so `checkROMLits` holds a ROM to cells and packages the World has.
- The wire (`Lang/HoleWire.lean`): `node 2 id [node 0 law []]`, `node 3 id [node 0 pkg []]`; `Bounds.packageWireVersion` 6 → 7; the codec labels `lang/package-version/7`, `lang/package/7` (`Lang/Package.lean`); `gates/codec-vectors.tsv` re-drawn. Print/Read: `(cell-law #id #law)`, `(cell-package #id #pkg)`.
- Theorems: `selectHole_contract_support` (Lang/Proofs/LiveHoles.lean): a selected candidate's `cellLaw` supports name live cells whose law slots hold the law, its `cellPackage` ones live cells whose package slot is the package — under `supportLive (.cellLaw ..) := cellLive` (a contract read as mere liveness) `selectHole_origin` and `selectHole_cell_support` still hold and this fails. `supportPinOf_tree` / `tree_of_supportPinOf` gain the two arms. The version theorems carry the label (statement edits).
- Journey. Boundary rows (`--contextual-checks`): `cell-law-governed` selects, `cell-law-ungoverned` / `cell-law-dead` / `cell-package-other` refuse `supportDead` naming the contract pin, `cell-law-unpinned` refuses `unpinned`; `wire-cell-law-pin-reads`, `wire-cell-package-pin-reads`, `wire-cell-law-pin-children`, `wire-pin-unknown-tag` (now 4). `Lang/Journey/ContextualLaw.lean` (`--contextual`, LG0–LG6, through `Receive.submit`): a law package `L` (one law, admits every act), a data object `g` under `L` and an object `o` of `L`; a ROM whose code 0 cites `cellLaw g L`, code 1 `cellPackage o L`, code 2 `cellPackage o g`; code 0 executes (value 7); A relaws `g` to no laws (judged by `L` as relaw); the same execute is refused `holeSupportDead 0 cellLaw:<g>:<L>`; code 1 executes; code 2 is refused `holeSupportDead 0 cellPackage:<o>:<g>`. The LV rows read the version from `Bounds`.
**MEASURED (hbox `wt/fable-ctx`, 62a36ee + this).** `lang-journey` default GREEN (LV1–LV3 refuse `lang/package-version/7`; DC0 reads the re-emitted `world/doc/Section`), `--contextual` GREEN (LG0–LG6: LG4 `execute: refused holeSupportDead 0 cellLaw:<g>:<L>`, LG6 `… cellPackage:<o>:<g>`), `--contextual-checks` GREEN, `--hole-omitted-blocker-pin-admits` GREEN; `codec-vectors --write` then `--check` ok (291 vectors of 59 sites; the package site's rows and the version site's two rows move); `cargo test -p nanodregg-client --test doc` passes (5.4 s) with the host rebuilt at version 7.

**Plant (MEASURED, restored byte-identical).** `supportLive (.cellLaw id _) := (digestOf id).any (cellLive look)` (the contract read as mere liveness): Lean RED at `selectHole_contract_support` by name (Lang.Proofs.LiveHoles:108); `--contextual-checks` RED (1): `cell-law-ungoverned` FAIL; `--contextual` RED (2): `cell-law-ungoverned` FAIL and `LG4 execute after the relaw: admitted` — a hole filled under a contract the object no longer meets. `selectHole_origin` and `selectHole_cell_support` stay green under it, which is why the new theorem is separate.

**What re-emits (`lang!`).** Every package's bytes begin with version 7, so every package id moves and every journey World re-runs from genesis; a version-6 package refuses `lang/package-version/7` before its tree is read, never reinterpreted (LV1–LV3). `world/doc/Section` re-emits (its `(imports …)` are the helpers' ids, which moved); the helpers' texts are unchanged. No deployed Store holds a package (deploy/, client/, rows/ hold no package id). `gates/codec-vectors.tsv`: the package site's rows change in their first byte and the version site's two rows; the rich-ROM row gains nothing (no shipped ROM cites a contract).

**Critique.** A contract by law says "L was consulted on every move of g" (B3's promise), not "g behaves as L's name says" — the stdlib-law meaning is the generator-spec tier (TOPLEVEL §10.3). `cellLaw` on a PROGRAMMED object is permanent (its laws never change), and `cellPackage` is permanent until the package is a slot (DESIGN-CTX §2.5c, S4); only a data object makes the contract defeasible today. The law is matched by package id (bytes equal), so two packages with the same law text and different docs are different contracts. Nothing deployed cites a contract yet: the document's sections (LANG-83) cite grants; the market (S3) is the first consumer whose candidates are strangers' objects.

**Meta-critique.** The pull was to make the contract a TERM (a predicate the hole author writes over the cited cell), which is the general thing and would have needed a cell view in the method environment (ACT-D §9 correction 1: a method sees no pins). Two constructors over what the kernel already reads through `look` cost one arm each in six functions and no new Term former, and they are exactly the two contracts a kernel without a proof system can keep.
## LANG-92 A claim is a sentence the kernel refuses to let be false: `keeps inv law`, its certifying shape, and the checker proved sound (L1, 2026-10-26; FABLE-PCC; design `redregg/work/promo/DESIGN-PCC.md`; method R-0069)

**Premise price.** Landed theorems gaining a hypothesis: none. Landed theorems restated: none. Three new modules, one new `Std` generator, one journey session.

**Why.** The kernel checks one proof about every installed program today: its type (`checkE`, `inferE_sound`). Everything else a package says of itself is its doc, "never run, never judged" (LANG-60), and the World cannot tell a package whose doc lies from one whose doc is true. VERDICT-20261024 §3's "every defect sat under such a sentence" is as true of package docs as of Lean docstrings. TOPLEVEL-SPEC §3.3(ii) leaves it open by design: B3 promises "your law was run", not "your law means its name". Re-execution makes a MONITOR the right check for every per-step property (the escrow's law costs 29–108 ticks per judgment, MEASURED on hbox at ad90a47, against `lawTicks` = 100,000; Necula's economic argument for PCC is worth 33 ticks per step here), so what a static check buys in nano is not ticks but a SUMMARY: a sentence in a small fixed language, carried in the package's identity, that install refuses unless the term bears it. The proof is the term's shape; the checker is Lean beside `checkE`, unmetered, O(|term|); its soundness is one theorem. No nano term checks a proof (the brief's "reflection costs too many ticks" is avoided, not solved: DESIGN-PCC §2).

**What (L1: the checker and its theorem; no byte moves).**
- `Lang/Claim.lean`: `Claim.keeps (inv law : Label)` — every state an object of the package holds satisfies the interface field `inv : fn S bool`, because the law `law` refuses every birth, adoption, write and invoke whose new state fails it. `Term.guardedBy I k r t`: every `ok` leaf of `t` is dominated by the true branch of `ite (app I (var k)) _ _` (`k` the index of `new`, `r` of `req`), the `relaw` arm of a `case` on `get (var r) "occasion"` excepted (the kernel judges a law change over the unchanged state). The `adopt` arm is NOT excepted: an adoption is a base case like a birth (KERNEL-27). Only a literal `inj` leaf may be an `ok`; `var`, `get`, `app`, `lam` and every other former are refused, so the walk is sound by construction and incomplete by design (a law that returns a verdict it read, or through a helper lambda, is "not in shape"; the author writes it in shape, as a certifying compiler emits checkable code).
- `Lang/Std.lean`: `Std.keeps S inv`, a law in shape: `guard (app inv new) "invariant" okT` on birth, adopt, write and invoke; `okT` on relaw.
- `Lang/Proofs/Claim.lean`: `Keeps lib ib n := ∃ env, BigStep lib (n.toVal :: env) ib (.ok (.bool true))` (stated as `Std.Admits` is; `ib` is typed under `[S]` so it reads only `var 0`); `guardedBy_sound` (a term in shape means `inj "ok" _` only when `I` meant `true` of the value at `k`, or a `relaw` occasion was read at `r`); `keeps_step` (a law in shape that `Admits` a non-relaw request leaves a state that `Keeps`); `chain_keeps` (along a `Std.Chain` of `Std.Step`s every state keeps the invariant once the first does: the term half of THE LIFT, `object_history_chain`); `keeps_guarded`, `isLaw_keeps`, `noRef_keeps`.
- `Lang/Journey/Claims.lean` (§LK, in `lang-journey`): LK1 a hand-written law in shape and `Std.keeps` check; LK2 a `write` arm admitting without the test does not; LK3 a law returning a verdict read from its state is not in shape; LK4 the journey's own `bounded` (inline `new.total ≤ 100`, not `app le100 new`) is not in shape: the row that measures DESIGN-PCC §3.4's gap.

**Plant** (hbox, L1 on 62a36ee). P1: the `inj` arm of `guardedBy` accepts every label. `guardedBy_sound` RED at its `inj` case (`Lang/Proofs/Claim.lean:65-68`, an application type mismatch and an unsolved goal); `lang-journey` RED (2): LK2 and LK4 flip to `true`. Restored (cmp).

**What re-emits.** Nothing: no wire moves in L1. L2 (DESIGN-PCC §8) carries `Package.claims` as the ninth package child at wire version 6 (`lang/package/6`), checks claims in `checkWith` with the refusals `claimNotLaw`, `claimNotInvariant`, `claimShape`, `claimUnproved`, proves `install_claims`, lifts to the World (`Kernel/Proofs/Logic/Claims.lean`, KERNEL-73), and runs the rows through the receivers: a true claim installs, a false one is refused `claimUnproved`, a claim with no proof in the term is refused `claimShape`. Every package re-ids then; shipped core texts do not change (the section is optional); a re-genesis is owed.

**Critique.** (a) `Keeps` quantifies the closure environment existentially; the tree has no "BigStep ignores unused variables" lemma, so the statement is as strong as the closed one only by determinism over a fixed environment and by `ib`'s typing. (b) The checker matches the invariant only as the closed literal `app inv new`; `Std.bounded`'s inline test is not in shape (LK4), and no `Std` law is claimable until either the renaming lemma for `BigStep` lands (DESIGN-PCC §3.4(i)) or the generators are re-emitted through `Std.keeps`. (c) A claim language is a second place to be wrong: a reader who trusts the NAME `keeps` without reading `Keeps` is trusting a docstring one level up; the mitigation is that the meaning is one short definition per claim class, not a theorem per package. (d) The refusal names the law, not the leaf; L2 should carry the path to the first unguarded `ok` as `TypeErr` carries its path.

**Meta-critique.** The pull was to answer "check a proof about a program" with a proof OBJECT: a derivation the kernel re-runs, which is the picture the literature draws (Necula's VCgen, Appel's FPCC). Measuring the escrow's law first (29–108 ticks) showed the budget was never the constraint and that re-execution already monitors every per-step property; what was missing was not a prover but a SENTENCE the World vouches for. The second pull was to exempt the `adopt` arm as the `relaw` arm is (both judge an unchanged state); writing `chain_keeps` showed adoption is the base case for an object whose law arrives mid-history, and an exempt `adopt` would have made B4 false for every adopted-over object.

## LANG-95 `Std.head` carries the chain: `headAtTy` = `{chain, height, roots, steps}`, the head law compares it at an equal step count, `headView.at` carries it (2026-10-26; FABLE-TRUST-2, Lang/StdHead by FABLE-OWNERSHIP; DESIGN-TRUST T2 §4.2; the Protocol half and the critique are PROTOCOL-75)

One head record, the kernel's spelling (`Protocol.Head`: origin, steps, height, roots, chain), now in the Lang object too: a receipt checks against the roots, one history is equality of the CHAIN (`fold_head_binds`), and a head without the chain lets two posters of one foreign World disagree only by roots at one step count. `head_at_at` (L2+L4) gains `c = c'` at an equal step count; `AtOk` and `atRec_conforms` the chain's bound; the journey gains HD3b (the held roots with another chain: `forkedHead`). `world/head/Head` re-emitted from `Lang.Print.packageText Std.headPackage` (its package id moves: a `lang!` flag day; every World that installed the old text re-geneses). What changed meaning: `headAtTy`, `atRec`, `HeadView`, `headView` (one field each), `AtOk`, `head_at_at`'s conclusion. Consumers restated by binder: `Protocol.Foreign.check` (ignores the field), `Protocol.Proofs.Foreign`'s four statements, `Lang.Journey.Head`, the X rows' `head_text`.
