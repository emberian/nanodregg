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
ID-4's bytes primitives, a method forwards only bytes it already holds.
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
**Status.** agreed with LEDGER (sent 2026-10-17); KERNEL-5's signature pending; not built.

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
**Status.** agreed (LEDGER-7, 7229d95); built in D5 (kernel) and the post-D5 `lang!` day (callTy, reqTy).

## LANG-26 The receiver's verdict on a stdlib package is its laws' meaning (2026-10-17; closes LANG-20's chain)
**Decision.** `Lang/Proofs/Receiver.lean` proves `judgeOne_pkgOf_admits`. If the receiver's judge admits
`old → new` and the pinned package is `Std.pkgOf S laws methods` (distinct labels, digest round trip),
then both states read at `S` and every law of the package with no `ref` and a law's shape `Admits`
the transition with the receiver's request. The proof has four links: `judgeOne_ok` (the for-loop over
`p.laws` inverted), `load_leaf` (an import-free package loads as itself at 0), `relocate_noRef`
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
reach packages with imports (`load_leaf`). `NoRef`/`IsLaw` are per-law premises in the conclusion,
discharged for every Std generator but not for a hand-written law. The conclusion is `∃ lib, Admits …`:
sound for the Std specs, which hold for every `lib`, but weaker than naming `L.lib`.
**Meta-critique.** I proved the import-free case because it is all the Std packages produce today.
That is "the case that went quickly" once more, and it is labelled as such above. The distinct-labels
premise could be derived from the install check (a non-ascending row does not check), and
`load_leaf` names fuel 7 by `closureDepthMax = 8` definitionally; both are left as stated.
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
**Status.** built (the round trip theorem is LANG-28's next commit).
