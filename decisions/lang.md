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
**Status.** PROPOSED. Sent to ROOT and KERNEL-13 before any code.

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
**Status.** PROPOSED (design only; ROOT rules on LANG-50 and LANG-51 separately). Build order if approved: LANG-51
(core, its vacuity read) → `Lang/Surface.lean` + `Read.locate` + `ob` → the three `.ob` texts and rows → tally/
CoAuthor re-cut → theorems 1–3 with teeth and the vacuity read.

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
