# nanodregg

nanodregg is a research system for shared objects whose updates each member checks independently.
One writer orders signed calls.
Each member's follower re-executes the log from a trusted starting state.
Objective Bend defines the objects' methods and laws.
Methods propose changes.
Laws decide whether changes are allowed.
The kernel commits an accepted call's effects together.
The system includes document and escrow demonstrations, a native host and client, a hosted model resident, and a browser testground.
Lean proofs cover specified properties of admission, history and settlement.
The operator can read every byte in a World.

The testground is the quickest way in.
It is served from the demo box at <https://nano.demo.dregg.online/>, with a GitHub Pages mirror as the sandbox at <https://emberian.github.io/nanodregg/>.
It runs the real kernel, compiled to WebAssembly, in your tab.

## One edit, followed through

A **World** is the shared state: objects, packages, members, grants and value.
A **member** is a key that can sign calls.
Alice and Bob are members of a World that holds a document section.
The section is an object, and its text is a slot that members fill by proposing candidates.

1. Bob proposes a text. He runs `nd invoke DOC 3 ARGS --pin facts PIN --via GRANT`. Method 3 of the section package proposes a candidate, `--pin` names the version of the cell it reads, and `--via` names the grant that lets him call it.
2. Bob's **follower** plans the call. The follower is the process that holds Bob's own copy of the World and checks every step of it. It catches up with the log, then derives the call against that copy: the pins, Bob's authority, the section's laws and the budget. If any check fails, the follower refuses and Bob's key signs nothing.
3. Bob's key signs the call, and `nd` sends it to the **writer**. The writer is the one process that orders calls for this World.
4. The writer derives the call again. If it is admitted, the kernel builds a **Turn**: the call's effects, committed together or not at all. A **law** is code in the package that sees the old state, the new state and the request, and accepts or rejects the change. The writer appends the Turn to the log. If the call is stale or a law rejects it, the writer records a refusal instead.
5. Bob's follower reads the log page, re-derives each step, and accepts only the World it computed itself. The writer's reply is a hint. The follower settles the call.
6. Bob runs `nd receipt CALL`. A **receipt** is evidence, checked against the follower's own head, that the call is in Bob's journal.

Alice selects Bob's text with the same sequence.
When Alice revokes Bob's grant, the fact that supported his text dies.
The next check suspends the candidate, and a second selection is refused with the dead support named.
The testground's "Document section with a hole" demonstration plays this out.
[`docs/MEMBER.md`](docs/MEMBER.md) lists every command and what it checks.

## Run the browser testground locally

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

## What the system consists of

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

## Where to read what

| Question | Read |
|---|---|
| What is the whole system? | [`docs/OVERVIEW.md`](docs/OVERVIEW.md) |
| How do I act as a member, and what does each command check? | [`docs/MEMBER.md`](docs/MEMBER.md) |
| What are packages, methods, laws, relations and contextual slots? | [`docs/OBJECTS.md`](docs/OBJECTS.md) |
| What does a member trust? | [`docs/TRUST.md`](docs/TRUST.md) |
| What exactly is claimed, with which premises? | [`Spec/README.md`](Spec/README.md) |
| How do I run a World natively? | [`docs/OPERATING.md`](docs/OPERATING.md), then [`deploy/RUNBOOK.md`](deploy/RUNBOOK.md) |
| How does the browser system work? | [`docs/TESTGROUND.md`](docs/TESTGROUND.md) |
| How do I land a change? | [`docs/JUDGE.md`](docs/JUDGE.md) |
| What rules shape the implementation? | [`CHARTER.md`](CHARTER.md), the twelve laws and scope |
| Why is a layer designed this way? | [`decisions/README.md`](decisions/README.md), one append-only file per layer. Later entries revise earlier ones. |
| What does a complete scenario look like? | [`Lang/Journey/`](Lang/Journey/) for language scenarios and [`Protocol/Rows.lean`](Protocol/Rows.lean) for member conversations |
| What is still proposed? | [`proposals/`](proposals/README.md) |

Research memos and outside reviews live in a separate repository, redregg, which is not part of this tree.

## What a member is promised

Each claim below names its subject.
[`Spec/README.md`](Spec/README.md) holds the theorem names, floors and premises.
The proofs assume Lean's kernel and the trusted components in [`gates/tcb.tsv`](gates/tcb.tsv).
They do not cover the compiler, the C runtime, the filesystem or the operating system.

**A checked history for each member.**
The admission and follower decisions are implemented in Lean.
A member's World is an audited fold from a start the member consents to (`OneHistory.member`).
That claim assumes the member's adoption key is the one it trusts (`keyFaithful`).

**Comparing two members.**
Two logs folded from the same starting World produce the same World when their step counts and chains match, unless the hash collides among their link inputs (`OneHistory.pair`).
This binds a comparison.
It does not make disconnected members agree, and it is not consensus.
Comparing heads can expose conflicting histories, and nothing merges them.

**Value.**
Along any fold from a World with canonical tries, every denomination's balance sum is unchanged (`Integrity.value`).
Its floor sum is unchanged too, unless a Turn of the log created the denomination's well.

**Laws.**
For a law in force throughout an object's history, [`Integrity.law`](Spec/Proofs/Claims.lean) relates the object's transitions to that law's reference semantics.
It requires an audited log, canonical cells, `IsLaw` and `NoRef` for the law, where `NoRef` means the law term holds no reference to another package.
Runtime admission of a law is a separate mechanism, described under Kernel above.

**Signing and settlement.**
The follower derives a call against its own World before it requests a signature.
`Consent.signs` states the composed property: every call message the follower offers custody is the call that `plan` produced on its own World.
A submitted command that ends `done ok` is in that World's journal (`Consent.okCommitted`).
A successful cancel is settled there as cancelled (`Consent.cancelOk`).
A final refusal stays final on every extension, and a stale settlement is admitted on no extension (`Consent.final`, `Consent.staleFinal`).

**Durability.**
The writer syncs a log frame before it acknowledges it.
`Durable.reopen` states that a successful open returns the fold of exactly the records the recovery check verifies.
It is a model of the Store contract.
Durability over crash images with acknowledged replies is not yet a claim.

**The Bell.**
The resident keeps its intent before it asks the provider and keeps its answer before it submits it.
`Bell.oneAsk` states that each path of the resident's act asks at most once about the decided ring.
The Bell's guards reject a second answer to an answered ring.
The composition of these across crashes and retries is not yet a claim, and Spec records that "once per ring key" does not hold today.

**Foreign receipts.**
A foreign receipt proves transaction admission relative to a held head.
It names a call admitted in a fold of the cited World, under the premise that the held head belongs to such a fold (`Foreign`).
It does not establish freshness, outside content or atomicity across Worlds.

## Ideas and literatures

The design draws on the work below.
Each entry gives the shared mechanism, one material difference, and a primary source.

- **Auditing by replay.** [PeerReview](https://www.mpi-sws.org/tr/2007-003.pdf) audits recorded behavior by replay, with witnesses. Nano uses one receiver for the writer's Turn and the follower's check.
- **Fork consistency.** [SUNDR](https://www.usenix.org/conference/osdi-04/secure-untrusted-data-repository-sundr) proves fork consistency for a file service on an untrusted server. Nano's nearest claim is `ForkConsistent`, which covers a head posted inside a page the follower walks.
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
