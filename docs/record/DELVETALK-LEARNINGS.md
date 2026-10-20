> record copy of redregg/work/DELVETALK-LEARNINGS.md, 2026-10-17; the lane logs stay in redregg

# What delvetalk2's Objective Bend learned that nanodregg has not taken in

Reader: one agent for Ember and ROOT, 2026-10-17. Read-only on both sides.
- delvetalk2 = `/Users/ember/dev/delvetalk2` (abbreviated `dt:`), plus its lane chronicles in
  `/Users/ember/dev/delvetalk2-lanes/chronicle/` (`dtc:`), which hold the retro material: the obend night
  of 13–14 Oct, and the scar audit.
- nanodregg = `hbox:/tank/dregg-build/nanodregg/main` at 71379a1 (`nd:`), plus `nd:DECISIONS.md` (frozen,
  where LANG-0..7 and LANG-L live).

Tags: **[read]** means I read the line cited. **[inferred]** means I am drawing a conclusion the files do not
state. Every claim about nanodregg comes from the files listed. None comes from memory. Where I looked and
found nothing, I say "not found in the files read", which is weaker than "absent".

Ember's framing was "that project had a lot of learnings, but wasn't quite good/ready enough". The evidence
for "not ready" is in §6. The short version: 91% of the obend night's resident turns came from Ember's own
three residents, and after the 08:59 carry "almost nobody played" (dtc:obend-2026-10-14.md "The shape of the
night", "Numbers") [read]. The third playtest's generativity measures were all zero (dt:docs/OVERHAUL.md §6
table, column "Third playtest") [read].

---

## 1. What delvetalk2's obend IS

**Objects.** Every thing is an object with four parts: an id (`bell/1`), a pin (the CID of its sealed
*source* closure), a versioned typed state, and one text of `law`/`rule`/`want` lines (dt:README.md:153–157;
dt:docs/METAPHYSICS.md §1) [read]. There are three base packages. RECORD holds lines with their authors,
marks, doors and presence. THING holds custody by offer and accept. KIND is a thing that makes things
(METAPHYSICS §5) [read]. A kind lays a **body** on each thing it makes. A body is a module that begins
`layer over ./Record.obend`. Every declaration is a field of one knot, so a body's `f` overrides the base's
`f`, `Super.f` reaches the layer below, and a retyped override is refused (dt:docs/KERNEL-HANDOFF.md §8
"Layers"; dt:world/bodies/bell.obend:1, 30–47) [read]. The core is Faré's prototypes, using `fix` and `mix`
(README:180–188) [read]. **Forms** (`form rain: text: text 1..200`) declare a verb's typed and bounded
argument. The State is the schema: edits, `keep()` and form inputs are all derived from `record State`
(bell.obend:33–45; KERNEL-HANDOFF §10) [read]. A **card** is the thing rendered. It says what the thing is
now, the verbs it takes, what it wants, and its law in plain words, and it ends on the exact spell to type
(README:5; dt:docs/FOUNDATION.md §8 "The voice") [read]. State is relations: keyed, sorted by canonical
bytes, each with a limit and a retention policy (FOUNDATION §9; invariant 10) [read].

**Acts.** A turn is a method running as an activity that yields `world.X(...)` calls (asking the world is the
only effect). It commits only if every root it read is current, or moved only by edits that commute with its
own: "two rains on one bell both land" (README:195–201; FOUNDATION intro) [read]. Every act, admitted or
refused, is **one journal entry** with a **receipt**: a number and a spoken two-word name taken from 32 bits
of the CID ("nosap-hodaz"). A receipt resolves forever, across carries (README:56–58, 203–206) [read]. A
refusal is also a receipt, and it names its clause and the next line to type: `refused alive: …; tend it:
delvetalk bell/1 tend` (README:85–87) [read]. **Dry-run**: `try` is "the same turn with the write switched
off". Its `if:` line sends the act only if nothing it read has moved, else `refused moved` (README:72–75,
201) [read]. **Rules** fire their spell when a write makes a condition true. A rule runs under whoever placed
it, at their cost, and can never refuse the write. Bounds are 8 a commit (the rest queued), 32 on a thing,
and 4 deep (README:171–175; dt:docs/OVERHAUL.md §2–3) [read]. **Wants** are standing conditions printed
with the spell that answers them. The commonplace lists "What wants a hand" (dt:docs/SEEDING.md §3) [read].
A verb a thing lacks is **grown** by the first hand that uses it (README:175–176) [read]. The law grammar is
linear: comparisons, filtered counts, membership in a cited object, `%`. It has a metarule: a law is
accepted only if it admits an amendment by its own proposer (dt:docs/LAW.md §1, §4) [read].

**Host.** One Lean process is the only writer. Replay re-judges the recorded edits and never re-runs
resident Bend (README:195–211) [read]. An **edition** (replay edition 20) names what replay derives. A host
refuses to replay another edition (dt:docs/HOST-HANDOFF.md §6 "Replay edition") [read]. **Carry**: a new
edition never begins a new town. Every object is rebuilt from its sources under the new host, then migrated
by its package's `migrate` or retired by name, and the new journal is chained to the old head. "the town is
carried across whole, every name and receipt with it" (README:11, 213–218; FOUNDATION §8 invariant 13 "No
wipe") [read]. The journal is an **AT Protocol repository**. There is one signed k256 record per journal
entry, served by `getRepo` and `getLatestCommit` under `did:web:gsb.fg-goose.online` (README:251–263)
[read]. **hob**, a small model, turns prose into the spell meant, and never decides admission
(README:141–143) [read]. **Paint**: the host lets a model arrange facts the host selects into a few
sentences, checks them token by token, and never journals them (README:220–227; OVERHAUL §4) [read].

**What ran.** Two towns run one binary at edition 20: gsb (by invitation, from delve.town) and obend (open,
feed-only) (README:16–18) [read]. The obend night produced 2,146 entries, 924 resident turns, 61
resident-made objects, 17 rooms, 7 kinds and 4 NPC inhabitants, and three carries mid-play
(dtc:obend-2026-10-14.md "Numbers") [read].

---

## 2. Already landed in nanodregg, in the same shape

| # | delvetalk | nanodregg | note |
|---|---|---|---|
| 2.1 | **Asking the world is the only effect; Bend does no I/O.** dt:FOUNDATION §8 invariant 1 | A method is a pure function `State → Args → Req → {calls, state}`. Effects are data the kernel runs. nd:DECISIONS.md LANG-6; nd:decisions/lang.md LANG-21, LANG-23 | [read] |
| 2.2 | **Self-write.** `write` changes only the running object; a cross-object change is a call judged by the callee's own law. FOUNDATION §8 inv. 3 | Every visited object's laws judge its own old → new, and the callee's `principal` is the calling object. LANG-21; `effect_as_signed` LANG-23 | [read] |
| 2.3 | **Replay does not re-run resident code; it re-judges recorded edits.** README:208–211 | A follower folds Turns, not receivers. DECISIONS.md LANG-5 critique; nd:decisions/kernel.md KERNEL-7 | [read] |
| 2.4 | **Retry returns the retained receipt and journals nothing.** FOUNDATION §8 inv. 6 | `replayed` by txId; `submit` answers the original receipt. KERNEL-7; nd:decisions/host.md HOST-8 | [read] |
| 2.5 | **Closed, named refusals.** Every refusal has a class from `refusalClasses`. FOUNDATION §8 inv. 5 | Charter law 7, "Refusals by name"; LANG-27 `illTyped RULE @PATH` | [read] |
| 2.6 | **A law refuses in the author's words** (`law NAME "reading": …`). LAW §1 | `Verdict = ok \| refused bytes`, cut to 256 bytes. LANG-8 | [read] |
| 2.7 | **Dry run guarded by reads.** `try`, then send only if no read moved (`refused moved`). README:72–75 | `plan` returns a call only if follow's own `World.admit` accepts it. Pins are the guard: one staleness refusal. nd:decisions/protocol.md PROTOCOL-1 ("dry-run (130) → follow computes `World.admit`"), PROTOCOL-11 `plan_admits`; KERNEL-11 | [read]. nanodregg's guard is stronger, because it is structural. A preview with no submit is not a verb (PROTOCOL-11's verb list) [read] |
| 2.8 | **Grants**: one principal acts as another on one method, until a clock, for N uses. FOUNDATION §8 | Grant cells with method slots, chains of up to `grantDepthMax`, attenuation that only narrows, and revoke that kills the chain. KERNEL-4, KERNEL-20 | [read]. nanodregg's is richer |
| 2.9 | **Static bounds everywhere**, pinned by a tariff test. dt:KERNEL-HANDOFF §4–5 | Charter law 4; `Lang/Bounds.lean` (u64 naturals with an `overflow` fault) | [read] |
| 2.10 | **Rule storms bounded**: 8 a commit, 4 deep. OVERHAUL §7 risk 1 | Calls bounded: `callsMax = 8`, `callDepthMax = 4`, re-entry refused. LANG-21 | [read]. The same numbers; whether that is a coincidence is [inferred] |
| 2.11 | **No wipe without a check**: a candidate binary must `carry` the newest backup, or it does not merge. OVERHAUL §5 step 0 | The carry row. nd:decisions/protocol.md PROTOCOL-35; KERNEL-29 `carry_of_carried` | [read] |
| 2.12 | **The archive replay is the integration gate** (rehearsal). FOUNDATION §11 | "the conformance ROWS restate the minidregg journeys … the journeys ARE the spec". nd:CHARTER.md law 11; PROTOCOL-5, PROTOCOL-10 | [read] |
| 2.13 | **Content-addressed identity that commits to the closure.** FOUNDATION §8 inv. 9 | The package id is `romIdOf` of the package cell, which holds the import ids. LANG-5, LANG-9 | Same principle, but the object hashed differs (see §3.1) |
| 2.14 | **Python carries bytes and decides nothing.** README:241–244 | Charter law 2: Rust moves bytes and consumes Lean-generated tables | [read] |
| 2.15 | **A law that is added later must say what it does over existing state.** The commonplace's `firstline` rule "does not reach back" to yue's line pending since 01:15. dtc:obend "What went wrong" item 8 | The `adopt` occasion: every Std law states what it does when it is ADDED over existing state. LANG-24 | [read] for both. That they are the same lesson is [inferred] |

---

## 3. Landed differently

**3.1 What a pin names.** dt: the pin is the CID of the sealed SOURCE closure, and no compiler change moves
the pin of unchanged source (FOUNDATION §8 inv. 9). Every card's code is "a spell away" (README:133)
[read]. nd: the checked CORE is installed, and the source is a claim (DECISIONS.md LANG-0 point 2, LANG-5).
LANG-0's own critique says the property "install nothing not re-derivable from source" is dropped, and that
getting it back costs "one field (`source digest` beside the core) and an offline gate" [read].
**Which is better:** nanodregg's choice is right for admission (no front end in the receiver). delvetalk's
is right for a reader of someone else's object. They compose once nanodregg has a source to digest (§4.1).

**3.2 Open recursion.** dt: `layer over` gives late binding. `Super.f` reaches the version below, and
`checkOverrides` refuses a retyped override (KERNEL-HANDOFF §8 "Layers") [read]. nd: `extend` keeps the OLD
self (`bigStep_extend_keeps_old_self`), and open recursion is `fix` over a mixin that "the authoring tool
writes" (LANG-18; nd:Lang/Term.lean header) [read]. **Which is better:** delvetalk, for authoring. Every
delvetalk body is a layer that overrides some methods and inherits the rest (bell.obend). LANG-18 calls
old-self `extend` possibly "the wrong language choice for mixins" [read].

**3.3 Laws by reference.** dt: `under "kind/bell"` conjoins the kind's *current* text. The kind's owner
amends it once, which re-laws every instance. Tenure applies: a cited law "never takes it from its owner"
(LAW §4 F; dt:docs/AUTHORING.md §4) [read]. nd: an object's laws are the package's laws plus the creator's
laws by `(package digest, label)`, all in ROM (DECISIONS.md LANG-4). A Std law is generated per instance,
with its parameters baked in (LANG-20) [read]. **Which is better:** this is taste, and depends on the use.
ROM laws are what a counterparty to an escrow needs. A mutable kind law is what a shared furniture kind
needs. nanodregg has only the first.

**3.4 Amendment and lockout.** dt: the metarule says no law is accepted unless it admits an amendment by its
proposer. The world's opener additionally "is admitted whatever the law says" (LAW §1 "The metarule") [read].
nd: a law may refuse every replacement. Row L9d is `frozen: laws are frozen`, and the Escrow package's relaw
arm is `refused "frozen"` (LANG-19; nd:world/escrow/Escrow) [read]. There is no opener override (not found
in the files read). Upgrade is append-only (LANG-4) [read]. **Which is better:** nanodregg, for value. A
frozen escrow is the point of an escrow, and an opener override is a second admission path (charter law 1).
delvetalk's metarule protects the author from a typo. nanodregg has no equivalent of that protection, and
LANG-4's critique names the cost: "cannot RELAX a law that was too strict, ever" [read].

**3.5 Time.** dt: a clock principal journals a minute tick, and laws read `request.clock` (METAPHYSICS §1
"Time"; LAW §4 A) [read]. nd: `Req` carries `notBefore` and `validUntil` (the signer's window; see the
`Req` type in nd:world/grain/Lifecycle), and `windowed` counts per epoch of that window (LANG-20) [read].
**Which is better:** nanodregg. There is no clock principal to trust, and a window is part of the signature.
delvetalk's "tended within 1440 minutes" cannot be said without a turn that someone signs (§4.6).

**3.6 History.** dt: "Nothing forgets, and nothing can be made to", and `viewAt` rebuilds any past version
(METAPHYSICS §1 "Memory") [read]. nd: the in-World journal is pruned to the window. Past it, a lookup
answers `uncertain forgotten` (KERNEL-33, PROTOCOL-33). A carry keeps state, not history (charter law 1)
[read]. Whether the host's log frames are kept forever is not stated in what I read. **Which is better:**
nanodregg's is right for law 4. delvetalk's "receipt resolves forever" (README:58) is a product promise
that nanodregg does not make (§4.4).

**3.7 Diagnostics.** dt: a located refusal names `definition`, `module` and `span`, and adds a dialect hint
(KERNEL-HANDOFF §8 "Located refusals", "Dialect hints") [read]. nd: a `TypeErr` gives the rule plus a path
into the core term (LANG-27) [read]. **Which is better:** delvetalk's, for an author. nanodregg's path
points into a printed core no resident wrote (§4.1).

**3.8 Evaluation.** dt: a call-by-need heap machine with checkpoints, plus three independent evaluators
(C, JS and Python) as conformance (FOUNDATION §1; README:246–249) [read]. nd: a CBV CEK machine with lazy
record fields and no heap, plus a `BigStep` reference semantics proved equal in both directions (LANG-2,
LANG-18) [read]. **Which is better:** nanodregg's proof. LANG-2's own critique names the risk it has not
measured: "a program that is linear under call-by-need is exponential here" [read].

---

## 4. Missing, and worth it (ranked by value)

**4.1 An authoring surface that a resident (or Hermes) can read and write.** *Highest.*
- *Why delvetalk needed it.* "behaviour is a package layer, written at three distances, all checked by one
  checker": a clause, then a verb with a body, then a kind body (dt:AUTHORING.md opening) [read]. The
  smallest real thing, a clicker, is five lines over RECORD (AUTHORING §1) [read]. Its checker answers "Lines
  1 to 15 are the header the workshop wrote; your first line is line 16" (§2) [read]. On the obend night
  residents wrote 3 Bend objects and 7 kinds (dtc:obend "The shape of the night") [read].
- *nanodregg's state.* The surface is "an authoring tool that runs in the resident's client" (LANG-0 point 2)
  [read]. In what I read, nothing beyond the core s-expression reader exists. The three shipped packages are
  printed core. `world/grain/Lifecycle` repeats its whole state record in every method's type and every
  `lam` annotation: `(rec (entry bytes)` occurs 14 times in 7 lines of 7,529 bytes, and there is no type
  alias [read]. `Lang/Ty.lean` says
  "Polymorphism and row-generic mixins are the authoring tool's job" [read]. LANG-3's critique: annotations
  "make core terms bigger to write by hand (an LLM resident will write them)" [read].
- *Where it goes.* LANG, as the Front that LANG-0 alternative (c) deferred: "right eventually but Front has
  no deployed consumer" [read]. The consumer is the Hermes resident (CHARTER's BAR). Minimum content: named
  types (aliases that print), `layer`/`mix` lowering (amends LANG-18), forms with bounds (§4.5), and a source
  digest beside the core (LANG-0's one field, giving back §3.1). It must elaborate to exactly the core
  `Lang.Read` reads, with `Lang.Print` as the inverse, so it stays outside the TCB [inferred].

**4.2 Bounded keyed relations in state, with commuting inserts at admission.**
- *Why delvetalk needed it.* "essential state is relations; derived state is computed" (FOUNDATION §8
  Principles) [read]. "commutative edits commit against moved roots … two rains on one bell both land"
  (FOUNDATION intro; `test_commute` in dt:tests/README.md "Host") [read]. The thirst table's top row is
  receipts, and its second is "rooms with history … wear" (METAPHYSICS §7.3) [read]. Both are append-only
  rows on a shared hot object.
- *nanodregg's state.* The core has no list or recursive type. LANG-1's critique: "a wiki page's list of
  links has no type. That is the first language extension a real app will demand" [read]. LANG-23 had to
  write calls as eight fixed option slots for the same reason [read]. KERNEL-11's critique: "Blind writes
  are gone … two writers of one hot cell conflict" [read].
- *Where it goes.* LANG first: a bounded `relation` type (key, limit, canonical order). This extends LANG-1
  and LANG-17, and needs a CODEC `Shape` for it. Then KERNEL: an `Act.insert` that commutes against a moved
  pin. This extends KERNEL-11's `Act` and must keep `stale_refused` true for every other act. One flag day.

**4.3 Refusals that say what to do next, and objects that describe themselves.**
- *Why delvetalk needed it.* "A refusal is also a receipt, and it names its clause and the next line to
  type" (README:85) [read]. Each want "printed with the spell that answers it" (README:9–10) [read]. On the
  obend night, a refusal naming no fix sent a client eight times at `world/delvetalk/receive` (dtc:obend
  "Frictions" item 8) [read]. "the voice is right when an agent, after an hour, can say this back unprompted"
  (dt:docs/VOICE.md "What an agent can say back after an hour") [read]. `delvetalk <card> ?` lists every spell
  and costs nothing (VOICE ibid.) [read].
- *nanodregg's state.* Refusals are names (law 7). `Lang/Resident` (`ob FORM`) checks a form offline [read].
  I found no read that returns a live object's interface, laws and argument types as text. "petnames are not
  in the language" (PROTOCOL-11) [read].
- *Where it goes.* PROTOCOL: a `read` kind that prints an object's iface and laws through `Lang.Print`. This
  needs no new decision by Lean, only the one printer (LANG-28). The hint goes on the refusal frame
  (PROTOCOL-21's `status ‖ payload`): `stale` names the cell to re-read, and `lawDenied` names the law
  label. LANG-8's 256-byte reason already carries the author's words.

**4.4 Receipts as nameable, durable things; refusals recorded.** *A design fork. Flag it to ROOT, do not brief
it.*
- *Why delvetalk needed it.* "a receipt as proof", 185 posts by 11 authors, is the top thirst
  (METAPHYSICS §7.3) [read]. "Admitted or refused, the turn is one journal entry" (README:201) [read]. The
  rehearsal's "rules to probe" row (141 posts) wants "a refusal that comes with a receipt" [read].
- *nanodregg's state.* "The Host keeps no record of refusals, so `lookup` never answers `refused`" (HOST-8).
  The journal forgets past the window (KERNEL-33) [read].
- *Where it goes.* KERNEL and HOST: a refusal record costs storage that nobody signed for (KERNEL-12's charge
  is storage). That is a real conflict with law 4, which is why this is a fork [inferred]. A spoken name
  for a txId (32 bits of the digest as two words, dt:Host/Slug.lean via README:204–205) is client-side and
  free.

**4.5 Bounded argument forms.**
- *Why delvetalk needed it.* Forms bound every argument (`text 1..200`), and empty lines admitted as text
  were a named defect (dtc:obend "What went wrong" item 7). A bound with a bad default (`from: 0` against
  `1..1e9`) caused six refusals, and hob echoed the bad value back (ibid. item 2) [read].
- *nanodregg's state.* Types are `nat | bool | bytes | digest | fn | rec | sum` with no refinement
  (DECISIONS.md LANG-3; Lang/Ty.lean) [read]. A bound is a law (`bounded`, LANG-20) [read].
- *Where it goes.* The surface (§4.1) lowers a form's bounds to an argument check in the method. A typed
  refinement in the core is not needed [inferred].

**4.6 Reaction: rules and wants.** *Lower. Build only behind a measure.*
- *Why delvetalk needed it.* "Need, feed and tend are what make things act on each other with nobody
  posting" (METAPHYSICS §7.4) [read]. On the obend night residents did place tide rules: yue hit
  `placedPerHand` at her fifth, and the inhabitants were rules on the tide (dtc:obend items 1 and 4) [read].
  But the third playtest's measures were 0 rules and 0 grown verbs written by residents (OVERHAUL §6 table)
  [read].
- *nanodregg's state.* Effects-as-data give atomic same-turn calls (LANG-21, LANG-23). No condition-triggered
  firing was found in the files read.
- *Where it goes.* A rule is a Turn some principal signs, so nanodregg would need a signer for "when X
  becomes true". That is the delegated, pre-signed grant shape (KERNEL-20), not a host loop. Defer it until
  §4.7's measure says residents ask for it [inferred].

**4.7 A resident-use measure beside THE BAR.**
- *Why delvetalk needed it.* "the offering is judged against this table; work that cannot say which row it
  serves does not ship" (METAPHYSICS §7.3) [read]. Playtest go/no-go: "resident-made things used by a
  resident other than their maker … at least 4" (dt:docs/PLAYTEST-2.md §5) [read].
- *nanodregg's state.* THE BAR is two friends plus hosted Hermes, 1000 records, a write in 5 s or less, and a
  cold reopen in 60 s or less (CHARTER preamble) [read]. It measures performance, not whether anyone uses
  the system.
- *Where it goes.* PROTOCOL's rows or OPS: one row that counts objects made by one member and used by
  another [inferred].

---

## 5. Missing, and rightly so

| delvetalk did | why nanodregg rightly does not | pointer |
|---|---|---|
| Activities that suspend (`perform`, `await`), with a checkpoint codec and resume proofs | delvetalk measured checkpoint work as where time went; nanodregg ruled "no perform in v0" | DECISIONS.md LANG-6; dt:KERNEL-HANDOFF §7, §14 [read] |
| A call-by-need heap and blackholes | Heap typing in every proof; minidregg's ~25 `Demand*` files | LANG-2 [read]. Its exponential cost is still unmeasured |
| Python deciding (bridge-written refusal and receipt text in English; Python deciding who is a resident) | The scar audit's top finding: "it breaks the boundary"; charter law 2 | dtc:scar-audit-2026-10-14.md §3 A, top ten #1; CHARTER law 2 [read] |
| The opener amends any law regardless (`openerAmends`) | A second admission path (law 1); a frozen escrow needs it absent | dt:LAW §1; nd:world/escrow/Escrow [read] |
| A model (hob, paint) inside the turn path; a token verifier over model prose | "hob's one `say:` line was false and believed (69275)"; and OVERHAUL risk 11: "a token verifier cannot check meaning". The paint is product, not kernel | dt:OVERHAUL §4 opening, §7 risk 11 [read] |
| A second law language (`ObjectiveBendLaw`), linear and parsed separately | One language: a law is a method run by the same evaluator | DECISIONS.md LANG-0 point 1, LANG-4 [read] |
| Carry with per-package `migrate` and `StateN` types | The scar audit: spent carry machinery and old-edition readers are its largest real scar. nanodregg refuses old shapes and carries state by checked re-genesis | dtc:scar-audit "Point", top ten #4–#6; CHARTER law 1; KERNEL-29 [read] |
| Off-by-default features kept built (hosted accounts, request poller, firehose: ~8,000 lines with tests) | Charter law 12 (size ratchet) and the doctrine "never keep a no-op" | dtc:scar-audit §3 B [read] |
| Proof-only modules outside `make check` that "rot silently" | nanodregg's runs table executes every verdict program of every importer on every landing | dtc:scar-audit §3 D; SESSION-SYNTHESIS "Gates" [read] |
| `Delvetalk/Profile.lean`: a second copy of the tariff loop with no equivalence proof | nanodregg made `runSetup` the one deployed function and deleted `Need`'s copy | dtc:scar-audit §3 D; lang.md entry at "`runMeasured`'s front half is ONE deployed function" [read] |
| The canonical-CBOR round trip "`#guard`ed", not proved | Charter law 6; CODEC canonicity theorems | dt:KERNEL-HANDOFF §16 "Not proved"; CHARTER law 6 [read] |

---

## 6. delvetalk's named failures, and whether nanodregg prevents each

Sources: dtc:obend-2026-10-14.md "What went wrong for them" (W1–W10) and "Frictions and bugs, ranked"
(F1–F16); dt:tests/test_obend_night.py docstring; OVERHAUL §6; dtc:scar-audit.

| failure (delvetalk) | does nanodregg prevent it? |
|---|---|
| **W1/F1. Prose became addresses.** `haunts`/`tide` were free text used as object ids. Edition 19 retyped them, and the carry stranded every NPC, which the tide re-armed into refusals every hour | **Yes, by type.** `digest` is a type, and every id a run holds came from where ids enter (LANG-38, LANG-41) [read]. ROM packages cannot change a field's meaning under a live object (LANG-5, LANG-11) [read] |
| **W7/F6. Admitted turns that did nothing**: `writes: []`, the help card only, empty lines admitted | **Not shown.** I found no theorem or row saying an admitted invoke changes a cell or says that it did not. **Gap:** a row in which an invoke whose new state equals its old state is either refused by name or reported as a no-op [inferred] |
| **W2/F5. A bounded argument with an out-of-bound default**, which hob echoed back | **N/A as built.** No forms, no hob. Becomes live with §4.5: the surface must refuse to emit a default outside the bound [inferred] |
| **W3/F4. The transport mangled scene blocks**, storing them raw | **Yes, by law 2 and one reader** (charter laws 2 and 3; LANG-22 readers) [read] |
| **W5/F9. `staleRoot` after the resident's own grow-then-write** | **The same class, mitigated.** The command machine re-derives and re-plans before submit, and refuses `planMoved` (PROTOCOL-11) [read]. Two separate commands that change behaviour and then write still race [inferred] |
| **W8/F7. A rule added later does not reach existing state** | **Yes for laws**: the `adopt` occasion (LANG-24) [read] |
| **F8. A refusal for a mistyped target gives no hint** (8 turns at `world/delvetalk`) | **Gap.** Refusals carry names, not the next action (§4.3) |
| **F2/F3. The web door turned people away; the play box silently discarded words** | **Out of the files read** (CLIENT/OPS). Lesson for the hosted path: a turn that journals nothing must answer by name (law 7) [inferred] |
| **W4/F10. Quota walls hit before they were raised** | **Different shape.** Storage is one budget and the charge is signed (KERNEL-15, KERNEL-12) [read]. No per-hour quotas exist to misjudge |
| **F12. Presence never lapses** | N/A (no presence) |
| **F13. The painter invents handles** | N/A (no paint) |
| **F15. A ghost identity**: a harness claimed a second key, and there is no way to merge or retire a twin | **Partly.** Members, keys and rotation are KERNEL-6 [read]. A member retiring a twin identity was not found in the files read |
| **OVERHAUL §6. The third playtest**: 0 verbs grown, 0 rules, 0 errands by residents; 0 of 3 residents said the world was generative | **No instrument.** THE BAR measures speed, not use (§4.7). **Gap** |
| **The obend night's drop-off**: 91% of turns from Ember's three; after the 08:59 carry, "almost nobody played"; 0 reports in the mending basket | **No instrument** (as above) |
| **scar-audit #1**: Python generates world text | **Yes**: law 2 plus the emitted tables (SESSION-SYNTHESIS "Interfaces") [read] |
| **KERNEL-HANDOFF §16 items 3 and 17**: whole-state reads per write; `insertOnly` judged over both sides' rows (~12 ms per 2,048-row write) | **Yes in spirit**: law 4 forbids O(store) on the request path, and lazy fields give O(touched) reads (LANG-2) [read]. It becomes live again with §4.2's relations: judge from the write's own edits |
| **dt FOUNDATION §1 "Not proved"**: the `noActivity` guard, the canonical-CBOR round trip, the commutative-root rule beyond `#guard`s | No activities; canonicity is proved (law 6) [read]. The commutative rule returns with §4.2 and must arrive as a theorem, not a `#guard` |

---

## 7. Recommendation for ROOT

Brief three lanes first. All three extend existing LANG/KERNEL/PROTOCOL decisions, and none needs a new
layer.

1. **LANG: the authoring surface (§4.1).** Named types, a `layer` that lowers to `fix`/`mix` (amending
   LANG-18's old-self `extend`), and bounded forms, all elaborating to exactly what `Lang.Read` reads. The
   source digest from LANG-0 rides beside the core.
   - The evidence: today's shipped `world/grain/Lifecycle` repeats its state record in every type and
     annotation (14 copies in 7,529 bytes). A Hermes resident can neither read nor write it.
   - delvetalk's residents wrote 3 Bend objects and 7 kinds in one night, because a clicker was five lines
     over RECORD.
2. **LANG + KERNEL: bounded keyed relations with a commuting `insert` act (§4.2), as one flag day.** This
   is the first extension LANG-1's own critique predicts. Without it, every shared append-only object (a
   guestbook, a log, a bell's rains) is a hot cell where two writers conflict (KERNEL-11's critique).
3. **PROTOCOL: self-description and next-step refusals (§4.3), with a resident-use row (§4.7).**
   - A `read` that prints an object's interface and laws through the one printer.
   - Refusal frames that name what would answer them.
   - One conformance row counting objects made by one member and used by another.

   delvetalk's clearest lesson is that the machinery worked and the residents still left. Without such a
   row, nanodregg can pass THE BAR with the same outcome.

Hold back two items as ROOT decisions, not lane briefs: whether refusals are recorded (§4.4: storage
nobody signed for, against law 4), and rules and wants (§4.6: wait for the use row).
