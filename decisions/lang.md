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
