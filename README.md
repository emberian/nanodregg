# nanodregg

nanodregg is a research system built around one language, **Objective Bend**.
An Objective Bend program is a *package*: a typed interface, a state type, methods, laws, keyed relations and typed holes.
An *object* holds a package and a state.
Objects live in a *World*, a shared state with one writer.
Every member re-executes every step of the World's log before accepting the World it produces.
Lean defines the language and the World, and the deployed writer and follower run that Lean, compiled.

The language is small and exact.
Its core has eighteen term formers, seven type formers and fifteen primitives.
Types are monomorphic, rows are canonical, and type equality is syntactic.
The checker is a total function, proved sound and complete for a declarative typing relation (`Lang/Proofs/Check.lean`, `inferE_iff_live`).
Programs run on one CEK machine under a tick budget.
A checked program never gets stuck (`Lang/Proofs/Sound.lean`, `checked_never_stuck`), and every way a run ends without a value is a named fault.

Two properties set Objective Bend apart from other ledger languages.

**Its meaning is contextual.**
A package may leave a decision open as a typed hole `u :: [Ψ ⊢ A]`, in the sense of contextual modal type theory.
The package commits the hole's candidates at install.
Each candidate lists the facts of the World it relies on: a row of the object at an exact version, or a cell that must be live, possibly governed by a named law or running a named package.
At each invocation the runtime reads the selection the caller pinned, checks the selected candidate's facts against the caller's pinned view, and splices the candidate in.
When a fact does not hold, the hole becomes a typed refusal that names the fact.
That refusal fires only if the run demands the hole.
So the code an installed package runs is a function of the caller's view of the World, and a run that needs a dead fact is refused by the fact's name.

**Its surface is extensible.**
A law judges a change by the act that makes it: birth, write, law replacement, adoption, invocation or retirement.
A law replacement on a data object is judged by the laws in force and by each incoming law.
A method may return a call that installs package bytes it computed, or that installs a package and creates an object of it in the same step, so packages generate packages.
A package may carry a claim, `keeps INV LAW`, that is part of its identity, and install refuses the package unless the law's term has the shape that proves the claim.
A method may declare a grade, `(effect (moves N))`, that bounds the value one run moves.
A relation may declare that each of its rows holds value, and a run that writes such a row must move that value.

## One program

The program below is one complete package.
It is a counter whose step is a hole with two candidates.
A law judges every act on the counter.
A third method generates a package.

The core text writes every type in full.
For reading, this page names seven of them:

```
S       = (rec (count nat))
Req     = (rec (agent digest) (caller (sum (none (rec)) (some digest))) (notBefore nat)
               (occasion (sum (adopt bytes) (birth (rec)) (invoke nat) (relaw bytes) (retire (rec)) (write (rec))))
               (principal digest) (self digest) (validUntil nat))
Verdict = (sum (ok (rec)) (refused bytes))
Row     = (rec (key (rec (k nat))) (val nat))
Choice  = (sum (insert Row) (upsert Row))
Edit    = (sum (choice Choice))
Call    = (sum (install (rec (pkg bytes))))
(Opt T) = (sum (none (rec)) (some T))
```

`PRE` and `POST` name two byte strings, given after the program.
`G` names the id of a grant.
[`Lang/Journey/Readme.lean`](Lang/Journey/Readme.lean) holds the literal text, writes a real grant's id for `G`, and runs every step described below through the kernel's receivers (`Receive.submit` with `Lang.program`) on a simulator World (`lake exe lang-journey`, rows RM1 to RM14).

```
(package
  (imports)
  (doc "a counter whose step is chosen in context; it spawns parameter packages")
  (state S)
  (iface (rec
    (bump (-> (rec) (-> S (-> (rec) (-> Req (rec (calls (rec)) (edits (rec)) (state S)))))))
    (cap (-> S (-> S (-> Req Verdict))))
    (choose (-> (rec) (-> S (-> (rec (i nat)) (-> Req (rec (calls (rec)) (edits (rec (e0 (Opt Edit)))) (state S)))))))
    (spawn (-> (rec) (-> S (-> (rec (n nat)) (-> Req (rec (calls (rec (c0 (Opt Call)))) (edits (rec)) (state S)))))))))
  (methods bump choose spawn)
  (laws cap)
  (rels (choice (key (k nat)) (val nat) (limit 1) (sum) (cap 0) (retract false) (guard) (holds)))
  (body (record
    (bump (fn (rows (rec)) (state S) (arg (rec)) (req Req)
      (record (calls (record)) (edits (record))
        (state (record (count (+ (. state count) (hole 0 (subst)))))))))
    (cap (fn (old S) (new S) (req Req)
      (let ok Verdict (inj Verdict ok (record))
      (let within Verdict (if (<= (. new count) 100) ok (inj Verdict refused "over 100"))
        (case (. req occasion)
          (adopt x within) (birth x within) (invoke m within)
          (relaw x (inj Verdict refused "frozen"))
          (retire x (if (== (. old count) 0) ok (inj Verdict refused "not empty")))
          (write x (inj Verdict refused "frozen")))))))
    (choose (fn (rows (rec)) (state S) (arg (rec (i nat))) (req Req)
      (record (calls (record)) (state state)
        (edits (record (e0 (inj (Opt Edit) some
          (inj Edit choice (inj Choice upsert
            (record (key (record (k 0))) (val (. arg i))))))))))))
    (spawn (fn (rows (rec)) (state S) (arg (rec (n nat))) (req Req)
      (record (edits (record)) (state state)
        (calls (record (c0 (inj (Opt Call) some
          (inj Call install
            (record (pkg (cat (u64be #PRE (. arg n)) #POST)))))))))))))
  (holes (hole 0 (context) (result nat) (selection 0 #0000000000000000) (hypotheses)
    (guard (structural) true)
    (code (candidate 1 (supports)) (candidate 10 (supports (cell #G)))))))
```

```
PRE  = 0a00000b00000004000004000106016e010000000800010f016e010408
POST = 00010000010000020000000000030000040000050000
```

Read it section by section.

`(imports)` is empty, so the body refers to no other package.
`(doc …)` is one line the package says of itself; nothing runs it.

`(state S)` makes an object's state a record with one natural, `count`.
State is first-order data, and each field lives in its own slot of the object's cell.

`(iface …)` is the type of the body, a record with four fields.
A *method* has type `rows → state → argument → request → result`.
`rows` is what the method reads from relations; these methods read none, so it is `(rec)`.
The result is a record of `calls` the object makes, `edits` to its rows, and the new `state`.
The type fixes how many calls and edits a method may return, and of which kinds: `bump` makes none, `choose` makes one edit, `spawn` makes one call of kind `install`.
A *law* has type `old → new → request → Verdict`.
`Req` is what a method and a law see of the request: the member who signed, the object, the calling object if any, the signed height window, and the *occasion*, which says which act is judged.

`(methods bump choose spawn)` and `(laws cap)` say which fields are methods and which are laws.
A member invokes a method by its index in this list: `bump` is 0, `choose` 1, `spawn` 2.

`(rels …)` declares one relation, `choice`: rows keyed by a natural, holding a natural, at most one row, no sum column, no retraction, no guard, holding no value.
Relation 0 holds the hole's selection.

`bump` adds the hole's value to `count`.
`(hole 0 (subst))` is hole 0 under the empty substitution; it has type `nat` because the hole's declaration says so.

`cap` is the law.
It cases on `(. req occasion)`, and the checker requires one arm per occasion, so a law has no default.
At a birth, an adoption and an invocation, the new count must be at most 100.
A retirement is judged over the object's last state; `cap` admits it only at count 0.
Writes and law replacements are refused.
The kernel refuses those two acts on an object that has methods before any law runs; the arms matter when the package serves as an extra law on a data object.

`choose` writes the selection.
It returns one edit: an `upsert` into relation `choice` at key 0, with the candidate index from its argument.
An upsert replaces the row at a key the caller pinned, present or absent.

`spawn` is a generator.
It returns one call, `install`, whose package bytes it computes: `PRE`, then the argument `n` as eight big-endian bytes, then `POST`.
At `n = 7` those bytes read as `(package (imports) (doc) (state (rec)) (iface (rec (n nat))) (methods) (laws) (rels) (body (record (n 7))))`, a package that exports one constant.
The kernel installs them as it installs a member's package: it decodes and checks them, and the new package cell's id is the digest of the bytes.

`(holes …)` declares hole 0.
Its context is empty and its result type is `nat`.
Its selection is the row of relation 0 at key `0000000000000000`, the eight-byte encoding of `k = 0`.
It has no hypotheses.
Its guard has no pin and evaluates `true`.
It has two candidates: `1`, which relies on nothing, and `10`, which relies on cell `G` being live.

The journey runs the program as follows.
Member B makes the grant `G` and installs the package.
Install checks every candidate at the hole's context and type, and checks the body with the hole's declaration in scope (RM2).
B creates a counter at count 0 (RM3).
`bump` before any selection is refused `program "bump: refused holeSelectionAbsent 0"`: the run demanded a hole whose selection row is absent (RM4).
B chooses candidate 1, and `bump` with `G` pinned raises count to 10 (RM5, RM6).
`bump` without `G` pinned is refused `program "bump: refused holeUnpinned cell:G"` (RM7).
B revokes `G`.
`bump` with `G` pinned at its tombstone is refused `program "bump: refused holeSupportDead 0 cell:G"`, and count stays 10 (RM8, RM9).
B chooses candidate 0, and `bump` raises count to 11 (RM10, RM11).
`spawn` at 7 installs exactly the package above; the Turn creates one cell, whose id is the digest of the computed bytes (RM12).
Retiring the counter at count 11 is refused `lawDenied … "cap: not empty"` (RM13).
Creating a counter at count 101 is refused `lawDenied … "cap: over 100"` at its birth (RM14).

The language has a second, higher-level text, [`Lang/Surface.lean`](Lang/Surface.lean), which lowers to the core text and adds names for `Req` and `Verdict`, declared types, bounded arguments and generated activities.
It has no syntax for holes, so this page uses the core text.
[`world/escrow/Escrow.ob`](world/escrow/Escrow.ob) is a complete package in the surface text.

## What the World guarantees

A World is cells, accounts, grants, relation rows and value, under four authenticated tries.
One writer orders signed calls.
A call that passes every check becomes a *Turn*: its effects, committed together or not at all.
A call that fails a check is recorded as a named refusal.
Each member's follower re-derives every Turn and every refusal from its own copy of the World.

The top claims are stated over the deployed entry points in [`Spec/`](Spec/README.md).
Each has a top theorem, a *floor* that refutes it for a trivial system, and a deployed run that reaches its premise.
One sentence each:

| claim | what it says | theorem |
|---|---|---|
| `OneHistory.member` | A follower's World is an audited extension of the World it held, or the adoption of a base its trusted sponsor pinned. | `top_oneHistory_member`, under `keyFaithful` |
| `OneHistory.pair` | Two folds from one World that agree on step count and chain are one World, up to a hash collision among their link inputs. | `top_oneHistory_pair` |
| `Integrity.authority` | Every step that changes a live cell is a Turn derived from a signed call entitled to that change. | `top_integrity_authority` |
| `Integrity.value` | Along any fold, every denomination's balance sum is unchanged, and its floor sum unless the log created its well. | `top_integrity_value` |
| `Integrity.law` | An object's package never changes, and every history of an object under a law without package references is a chain that law's reference meaning admits. | `top_integrity_law` |
| `Integrity.grantCap` | Transfers and credit sent through a grant sum to at most what its ledger had left. | `top_integrity_grantCap` |
| `Integrity.exchange` | An admitted fuse pays each party what its offer wants, with value conserved. | `top_integrity_exchange` |
| `Integrity.escrow` | Along any admitted history of one escrow, at most one call is a payout. | `top_integrity_escrow` |
| `Consent.signs` | Every call message the follower offers for signature is the call its planner derived on the follower's own World. | `top_consent_signs` |
| `Consent.signShapes` | Every message the follower offers for signature has one of six named shapes. | `top_consent_signShapes` |
| `Consent.okCommitted` | A command that ends `done ok` means the follower's World journals the call. | `top_consent_okCommitted` |
| `Consent.cancelOk` | A cancel that ends `done ok` leaves the call recorded as refused `cancelled`. | `top_consent_cancelOk` |
| `Consent.final` | A settlement `expired`, or `refused` other than `stale`, is never contradicted on any extension. | `top_consent_final` |
| `Consent.staleFinal` | A call settled `refused stale` is admitted on no extension, up to a collision among its pin inputs. | `top_consent_staleFinal` |
| `ForkConsistent` | A follower that absorbs another fold's head post shares that fold's history up to the post, or refuses `forkedPost`. | `top_forkConsistent` |
| `ForkConsistent.sync` | A `sync --to STEPS:CHAIN` that reaches the stated head holds the other fold's log up to it. | `top_forkConsistent_sync` |
| `Agree.pageAbsorbs` | The writer's page of a batch moves the follower to the World the writer keeps. | `top_agree_pageAbsorbs` |
| `Durable.reopen` | A successful reopen returns the fold of exactly the records the recovery check verifies. | `top_durable_reopen` |
| `Durable.follower` | Every follower step that persists persists a rooted run of the kernel. | `top_durable_follower` |
| `Durable.resident` | A resident's keep is atomic across a crash and durable once complete. | `top_durable_resident` |
| `ReceiptTruth` | A receipt the check answers against a World's own head is its journal entry, its refusal, or the absence of both. | `top_receiptTruth` |
| `Bell.ringer` | Every answer a run writes to the Bell answers a waiting ring the caller pinned, signed by the resident. | `top_bell_ringer` |
| `Bell.oneAsk` | Every path of the resident's act asks the model at most once, about the decided ring, after keeping its intent. | `top_bell_oneAsk` |
| `Foreign` | A receipt shown committed against a held head names a call admitted in that head's fold, under `HeadOf`. | `top_foreign` |

The premises are named in [`Spec/README.md`](Spec/README.md).
Three matter most here.
`keyFaithful` says a member's adoption names the sponsor key the member trusts.
`NoRef` restricts `Integrity.law` to laws that name no other package; a law with holes is inside it when its fillings are.
`HeadOf` says a held head belongs to a fold of the foreign World.

No top claim yet covers the contextual layer at the level of a history.
The run-level theorems exist: a successful selection is the candidate the pinned row names with every support live (`Lang/Proofs/LiveHoles.lean`, `selectHole_origin`, `selectHole_cell_support`); a retired support refuses the selection (`revoked_support_refused`); a prepared body is typed at the interface (`instantiateHoles_typed`).
The history-level statement, contextual integrity with repair, is a design in redregg's `promo/DESIGN-CTX.md` §2.4, not a theorem.

The claims do not cover the Lean compiler, the C runtime, the filesystem or the operating system.
They give no secrecy from the operator, no agreement among several writers, and no end-to-end durability over crashes with acknowledged replies.

## Where to read

| Question | Read |
|---|---|
| What is the language, exactly: syntax, typing, execution, bytes? | [`docs/spec/`](docs/spec/README.md), the Objective Bend specification; read it first |
| What is a World, and which transition does a call make? | [`docs/reference/kernel.md`](docs/reference/kernel.md) |
| How do members sign, follow, settle and compare heads? | [`docs/reference/protocol.md`](docs/reference/protocol.md) |
| Which executable scenario shows each construction? | [`docs/OBJECTS.md`](docs/OBJECTS.md) |
| What exactly is claimed, with which premises? | [`Spec/README.md`](Spec/README.md) |
| What does a member trust? | [`docs/TRUST.md`](docs/TRUST.md) |
| What is the whole system? | [`docs/OVERVIEW.md`](docs/OVERVIEW.md) |
| How do I act as a member, and what does each command check? | [`docs/MEMBER.md`](docs/MEMBER.md) |
| Why is each part designed as it is? | [`decisions/lang.md`](decisions/lang.md) and the other files of [`decisions/`](decisions/README.md); later entries revise earlier ones |
| What does a complete scenario look like? | [`Lang/Journey/`](Lang/Journey/) for the language, [`Protocol/Rows.lean`](Protocol/Rows.lean) for member conversations |
| What rules shape the implementation? | [`CHARTER.md`](CHARTER.md) |
| How do I run a World natively? | [`docs/OPERATING.md`](docs/OPERATING.md), then [`deploy/RUNBOOK.md`](deploy/RUNBOOK.md) |
| How does the browser system work? | [`docs/TESTGROUND.md`](docs/TESTGROUND.md) |
| How do I land a change? | [`docs/JUDGE.md`](docs/JUDGE.md) |
| What is still proposed? | [`proposals/`](proposals/README.md) |

Research memos and outside reviews live in a separate repository, redregg, which is not part of this tree.

## Try it

The testground runs the real kernel, compiled to WebAssembly, in a browser tab.
It is served from the demo box at <https://nano.demo.dregg.online/>, with a GitHub Pages mirror at <https://emberian.github.io/nanodregg/>.
Its "Document section with a hole" demonstration shows a candidate withdrawn by name when the grant supporting it is revoked.

The README's program runs as journey rows RM1 to RM14:

```sh
lake build lang-journey
lake exe lang-journey
```

`lake exe lang-journey` runs every registered language session, the README's among them, and prints one line per row.

### Run the browser testground locally

The route needs no hosted World and no native binary.

Prerequisites:

- `elan` with the Lean toolchain in [`lean-toolchain`](lean-toolchain) (Lean v4.30.0), and `git` with network access, because the build fetches the Lean runtime sources and libuv headers at pinned tags.
- Emscripten 6 or later, active in the shell (`source EMSDK/emsdk_env.sh`).
- `python3`, which `build.sh` calls and which also serves the page.

Build into a private scratch directory:

```sh
source "$EMSDK/emsdk_env.sh"
testground/build/build.sh all "$(mktemp -d)"
```

The first argument selects both stages: `c` builds Lean's C for the kernel closure and `wasm` compiles it with Emscripten.
The script writes `testground/kernel.mjs`, `kernel.wasm` and `kernel.json` into the worktree, and copies the demo packages beside the page.
`kernel.json` records the commit, whether the tree was clean, and the sha256 of `kernel.wasm`.

Serve the directory over HTTP, because the page does not load from a `file:` URL:

```sh
python3 -m http.server 18741 --bind 127.0.0.1 --directory testground
```

Open <http://127.0.0.1:18741/>.
The page shows a desktop of windows with a Start here icon.
Step 1 of Start here creates a cell and reads it, and both commands print `exit ok`.
The World window shows the sha256 the tab computed of the kernel bytes it loaded, beside the commit from `kernel.json`.
The two hashes agree.
No `deployment.json` is present in a local build, so the page offers no door to a live World.
[`docs/TESTGROUND.md`](docs/TESTGROUND.md) describes the windows, hosted mode and the hosted setup.

## The system around the language

The one-page map is [`docs/OVERVIEW.md`](docs/OVERVIEW.md).
Each layer below has an entry point, a role and its decision file.

**Kernel.** [`Kernel/World.lean`](Kernel/World.lean) holds the World, its tries, `admit` and the fold over log steps.
[`Kernel/Receive/Submit.lean`](Kernel/Receive/Submit.lean) connects signed calls to admission.
Admission refuses stale pins, missing authority, overspending and exhausted budgets, including the member's ticks per window.
[`Host.Deployed.X`](Host/Deployed.lean) binds the generic kernel to the deployed codecs and language.
Decisions: [`decisions/kernel.md`](decisions/kernel.md).

**Lang (Objective Bend).** [`Lang/Package.lean`](Lang/Package.lean) defines a package: a typed interface, state, methods, laws and relations.
[`Lang/Program.lean`](Lang/Program.lean) is the kernel's program runner, one metered CEK machine.
An invocation reads through its pinned view.
A missing required observation causes a refusal.
A contextual slot selects code using checked observations, such as a live grant.
A method can return an install call that contains a generated package, as the [generator](Lang/StdGen.lean) does, and the kernel checks that package through the same loader.
Decisions: [`decisions/lang.md`](decisions/lang.md).

**Codec and Emit.** [`Codec/Stream.lean`](Codec/Stream.lean) defines canonical encoders and decoders.
[`Codec/Deployed.lean`](Codec/Deployed.lean) fixes 32-byte digests, cSHAKE256 and Ed25519, and [`Emit/`](Emit/) emits the layouts into Rust.
Decoders refuse malformed, noncanonical and out-of-bound input.
Trusted implementation components are listed in [`gates/tcb.tsv`](gates/tcb.tsv).
Decisions: [`decisions/codec.md`](decisions/codec.md).

**Protocol.** [`Protocol/Table.lean`](Protocol/Table.lean) lists the operations.
[`Protocol/Command/Machine.lean`](Protocol/Command/Machine.lean) is the command machine behind `host follow`: it plans calls, requests signatures, absorbs log pages and settles attempts.
A head records a World's position, and [`Protocol/Head.lean`](Protocol/Head.lean) defines heads, attestations and certificates.
Genesis can name the keys and the threshold used to certify heads, and a genesis that names none requires no certificate.
[`Protocol/Foreign.lean`](Protocol/Foreign.lean) checks a foreign receipt against a held head.
Decisions: [`decisions/protocol.md`](decisions/protocol.md).

**Host.** [`Host/Deployed.lean`](Host/Deployed.lean) wires `host serve`, `host follow`, the Store and the pager.
The writer syncs MAC-chained log frames before it acknowledges them, and it reopens its own Store periodically.
A failed write or sync yields `uncertain`.
Corruption or a divergent reopen is refused by name.
The process introduction is [`docs/OPERATING.md`](docs/OPERATING.md).
Decisions: [`decisions/host.md`](decisions/host.md).

**Ledger.** [`Kernel/Value.lean`](Kernel/Value.lean) defines balances, denominations and credit floors.
[`Ledger/Escrow.lean`](Ledger/Escrow.lean) defines the escrow package shipped in [`world/escrow/`](world/escrow/).
Escrow changes its phase and moves its value in one Turn.
Members choose the denomination's issuer and the escrow's parties.
Conservation does not establish that an issuer can redeem a balance.
Decisions: [`decisions/ledger.md`](decisions/ledger.md).

**Hosting.** [`Hosting/Resident/Bell.lean`](Hosting/Resident/Bell.lean) holds a resident's decisions and [`Hosting/Broker.lean`](Hosting/Broker.lean) holds provider access.
The `resident` answers the Bell through its own member socket.
A Lean decider authorizes and meters each model request.
The Bell in [`world/resident/`](world/resident/) is an object with pending rings and guarded answers.
The broker refuses missing allowances, unauthorized residents and malformed replies.
Decisions: [`decisions/hosting.md`](decisions/hosting.md).

**Rust.** `client/` supplies `nd` and `nd-supervise`.
`launcher/` supplies `grain-launch`, `nd-members` and `keybroker`.
Rust carries frames and performs operating-system effects.
It stores keys and signed attempts.
It checks custody paths.
Lean supplies protocol decisions and generated tables.
`sandbox/` confines the children: each child confines itself, with Landlock and seccomp on Linux and `sandbox-exec` on macOS, and the launch is refused where no mechanism exists.
Decisions: [`decisions/client.md`](decisions/client.md).

**Testground.** [`testground/index.html`](testground/index.html) is a desktop of member terminals, object windows, demonstrations and a wire inspector.
[`Web/Sim/Testground.lean`](Web/Sim/Testground.lean) compiles the real writer and follower decisions to WebAssembly.
Local mode runs the writer over an in-memory Store.
Hosted mode sends writer frames over a WebSocket and keeps the follower in the tab, where forged replies are refused.
A visitor trusts the page's kernel and the channel that supplies its sponsor key.

**Spec.** [`Spec/README.md`](Spec/README.md) and [`Spec/System.lean`](Spec/System.lean) state the member-level claims over a record of deployed entry points.
Each top theorem has a floor that rejects a trivial substitute system.
Decisions: [`decisions/spec.md`](decisions/spec.md).

**Rows, the census and the report.** [`gates/runs.tsv`](gates/runs.tsv) registers the simulations, journeys, conformance rows and Rust tests, each with the line a passing run prints.
[`Census/`](Census/) counts axioms over elaborated declarations.
[`gates/check.py`](gates/check.py) checks module boundaries, the TCB table and the codec vectors.
The convergence report covers every registered row and identifies reused results.
It lists failures and the landings that changed their inputs.
It distinguishes a failed check from a check that did not run.
Decisions: [`decisions/gates.md`](decisions/gates.md).

**Deploy, Ops and Bench.** [`deploy/RUNBOOK.md`](deploy/RUNBOOK.md) covers genesis, custody, joining, service units, backup and recovery.
`Ops/` emits the units and operator tables.
[`Bench/`](Bench/) and [`scripts/bar.sh`](scripts/bar.sh) run THE BAR: two members and one hosted resident against one World.
Each benchmark records its measurement conditions.
Decisions: [`decisions/ops.md`](decisions/ops.md), [`decisions/perf.md`](decisions/perf.md).

## Ideas and literatures

The design draws on the work below.
Each entry gives the shared mechanism, one material difference, and a primary source.

- **Auditing by replay.** [PeerReview](https://www.mpi-sws.org/tr/2007-003.pdf) audits recorded behavior by replay, with witnesses. Nano uses one receiver for the writer's Turn and the follower's check.
- **Fork consistency.** [SUNDR](https://www.usenix.org/conference/osdi-04/secure-untrusted-data-repository-sundr) proves fork consistency for a file service on an untrusted server. Nano does not have it: a call names no prefix, so a writer can admit one call on two branches. Nano's nearest claim compares a member's stated head with another member's fold, and detects a split only when heads are compared ([PROTOCOL-82](decisions/protocol.md)).
- **Collaborative state.** [SPORC](https://www.cs.princeton.edu/courses/archive/fall15/cos518/papers/sporc.pdf) merges concurrent edits with operational transformation over encrypted state. Nano has one ordering writer, merges nothing, and gives the operator every byte.
- **Authenticated commitments.** [Certificate Transparency, RFC 9162](https://www.rfc-editor.org/rfc/rfc9162.html) separates inclusion proofs from append-only consistency proofs. Nano's foreign receipt proves transaction admission against a stored head, and a signature on a head does not replace re-execution.
- **Validated read sets.** [Kung and Robinson](https://www.eecs.harvard.edu/~htk/publication/1981-tods-kung-robinson.pdf) validate reads before commit. [Fabric](https://hyperledger-fabric.readthedocs.io/en/release-2.5/readwrite.html) records versioned read sets, and [Sui](https://docs.sui.io/develop/sui-architecture/object-model) names versioned object references as transaction inputs. Nano's pins are not new. Its refusals separate a pin that is behind from one that is ahead and name the missing observation, so a client can fetch it.
- **Delegated authority.** [KeyKOS](https://css.csail.mit.edu/6.858/2014/readings/keykos-sec.pdf) protects capabilities as references, [SPKI](https://www.rfc-editor.org/rfc/rfc2693.html) signs authorization certificates, and [macaroons](https://research.google.com/pubs/archive/41892.pdf) attenuate bearer credentials with caveats. Nano keeps grant records in authenticated mutable state, so revocation and counted consumption happen in the same ordered transition as the object operation.
- **Validated transactions.** [EUTXO](https://developers.cardano.org/docs/get-started/technical-concepts/eutxo/) and Cardano validators check a proposed transaction against explicit inputs and context. Nano uses mutable objects and kernel balance cells instead of unspent outputs.
- **Credit.** [XRPL trust lines](https://xrpl.org/docs/concepts/tokens/fungible-tokens/trust-line-tokens) allow bounded debt. Nano allows a negative balance down to a floor, and the floor sum is conserved except where the log creates the well.
- **Resource safety.** [Move](https://arxiv.org/abs/2004.05106) prevents unauthorized copying and discarding of protected language values. Nano's conservation applies to kernel balances, and a language value carries no money.
- **Abstract machine.** The CEK machine gives the evaluator its structure. Nano's metered machine charges ticks, and `Lang/Proofs/Cost.lean` bounds the primitive operand bytes per tick.
- **Verified evaluation.** [CakeML](https://github.com/CakeML/cakeml) relates executable evaluation to its [semantics](https://github.com/CakeML/cakeml/blob/master/semantics/evaluateScript.sml). Nano relates its machine to the reference semantics in `Lang/Proofs/Agree.lean` and `Complete.lean`. It does not verify the compilation from Lean to native code.
- **Typed open code.** [Contextual modal type theory](https://www.cs.cmu.edu/afs/cs.cmu.edu/user/fp/www/papers/cmtt05.pdf) gives open code an explicit context. The deployed system selects typed candidates and checks recorded support at invocation. [`docs/OBJECTS.md`](docs/OBJECTS.md) separates the research model from the deployed preparation.
- **Reasons for belief.** [Doyle's truth maintenance](https://www.ijcai.org/Proceedings/77-1/Papers/035.pdf) records the reasons for a belief, and [de Kleer's ATMS](https://www.sciencedirect.com/science/article/pii/0004370286900809) tracks the assumption sets that support a conclusion. Nano checks one recorded support set and names the failed observation. It is not an ATMS.
- **Missing answers.** [Why-not provenance](https://citeseerx.ist.psu.edu/document?doi=1aa60b5ae893cd93a221bf71b6b264f5aa5ca6b8&repid=rep1&type=pdf) explains why a query result is absent. Nano's refusal explains why a selection was withdrawn.
- **Reified effects.** [Interaction Trees](https://arxiv.org/abs/1906.00046) represent effects as data with interpreters, and handle non-termination by coinduction. Nano's resident is an inductive `Prog` with a handler, and its trace theorems inspect paths through it.
- **Protocol without I/O.** [Sans-I/O](https://sans-io.readthedocs.io/) keeps protocol logic free of network operations. Nano's decisions return effects that an outer Rust process performs.
- **Verified parsers.** [EverParse](https://www.microsoft.com/en-us/research/publication/everparse/) generates verified, zero-copy parsers with memory safety. [Narcissus](https://www.cs.purdue.edu/homes/bendy/papers/Narcissus/index.html) derives encoders and decoders from format descriptions. Nano proves round trip and canonical form in Lean and emits Rust layouts. Fixed vectors pin byte meanings that a structural tag cannot distinguish, and they do not prove a parser correct.
- **Log integrity after compromise.** [Schneier and Kelsey](https://www.schneier.com/academic/archives/1999/05/secure_audit_logs_to.html) protect earlier log entries with evolving keys. Nano's Store has one MAC key for integrity at rest, which does not protect against a party that can write the Store.
- **Identity rotation.** [KERI](https://keri.one/) precommits to future identity-control keys. Nano's member keys rotate by a precommitted next key.
- **Specification checks.** [Kupferman and Vardi](https://cris.huji.ac.il/en/publications/vacuity-detection-in-temporal-model-checking-13/) detect vacuity by asking whether parts of a specification affect its truth. Nano's floors are countermodel checks: a trivial system that must fail the claim. One countermodel does not show that every premise matters.

## Building and working

[`lean-toolchain`](lean-toolchain) pins Lean v4.30.0.
Lean uses core and Std, with no external packages.
Warnings are errors in the Lean build.
The Rust crates share [`Cargo.toml`](Cargo.toml) (edition 2024, resolver 3) and its lockfile.
The manifests do not pin a Rust release.
The native host also needs a C compiler.

From a development worktree:

```sh
export CARGO_TARGET_DIR="$PWD/target"
lake build host
cargo build --locked --release -p nanodregg-client
lake exe kernel-sim --seeds 64
lake exe host-sim 1
lake exe host-file-sim 1
lake exe lang-journey --contextual
lake exe rows --deployed receipt
```

`lake build` builds every default library and executable.
`lake exe lang-journey` runs all registered language scenarios, so select the scenarios or protocol rows relevant to a change.
Filter Rust tests, for example `cargo test --locked -p nanodregg-client --test frame`.
The host executable is `.lake/build/bin/host` and the release client is `target/release/nd`.
[`docs/OPERATING.md`](docs/OPERATING.md) and the runbook create a Store and connect each member's follower through `nd-supervise`.

Land source changes on main.
[`docs/JUDGE.md`](docs/JUDGE.md) describes how: build what you changed, run what you touched, push, and read the periodic report.
It also holds the shared build host's resource policy.
[`gates/waste.tsv`](gates/waste.tsv) records the work ratios the benches measure.
Definitions and proofs live in separate modules.
Changes to decisions append their reasons and both critiques.

## Provenance

nanodregg draws its requirements from minidregg's scenarios, simulations, workload and theorem statements.
It is a research demonstration in the Dragon's Egg project.
Earlier systems include minidregg and dregg, also called breadstuffs.

License: [AGPL-3.0](LICENSE).
