# nanodregg

nanodregg is a verified single-writer World: a shared state whose members check its
history by re-executing the log. Its metered ledger language, Objective Bend, gives
objects methods and laws, with programs whose meaning depends on justified facts
in the World. A World's position is itself a kernel object: members can hold
heads, compare histories, and check receipts against them, with an authority
fixed at genesis naming who may certify a head. One writer orders calls; each
member's own follower decides what to accept and what to sign.

A World contains typed cells for objects, immutable packages, members, grants and
value, together with authenticated rows and a journal. A signed call names the
versions it reads. The kernel checks those pins, derives a Turn, judges its
authority and laws, and admits its effects together. A log step records an
admitted Turn or a recorded refusal. The follower derives these decisions again
from their signed inputs; it does not accept a writer's claimed result.

Programs can also construct programs. A [generator](Lang/StdGen.lean) is an
ordinary package whose method returns an install call; the kernel checks the
generated package through the same loader, and its generation belongs to the
Turn every follower re-executes.

The operator sees the World's bytes. Membership and follow grants define access;
this is a trusted vat with independently checked execution. Each World has one
decided log. Worlds interact through receipts against held heads, without an
atomic transaction across Worlds. Availability depends on the writer and the
transport; comparing heads exposes conflicting histories but does not merge them.

## What the system consists of

**Kernel — state and admission.** [`Kernel/World.lean`](Kernel/World.lean) is the
starting point for the World, its tries, `admit` and the fold over log steps;
[`Kernel/Receive/Submit.lean`](Kernel/Receive/Submit.lean) connects signed calls
to that admission, refusing stale pins, missing authority, overspending and
exhausted budgets, including the member's ticks per window.
The running instance is [`Host.Deployed.X`](Host/Deployed.lean), which binds the
generic kernel to the deployed codecs and language.
Its proofs use canonical state and lawful encodings; hash-binding conclusions
name the finite inputs among which a collision would defeat them.

**Lang — Objective Bend.** Start at [`Lang/Package.lean`](Lang/Package.lean):
a package contains a typed interface, state, methods, laws and relations, while
[`Lang/Program.lean`](Lang/Program.lean) supplies the kernel's program runner,
using one metered CEK machine and refusing ill-typed code, blocked contextual
choices or an exhausted budget.
A contextual slot selects a typed candidate under pinned justifications, such as
a live grant or a provider's package identity; the document in
[`world/doc/`](world/doc/) uses this to withdraw a contribution when its support
is revoked.
The design assumes that every fact an invocation needs is in its pinned view;
the program cannot read an ambient World behind the signer's back.

**Codec and Emit — bytes and their meaning.** Start at
[`Codec/Stream.lean`](Codec/Stream.lean) for canonical encoders and decoders,
then [`Codec/Deployed.lean`](Codec/Deployed.lean) for the concrete instance:
32-byte digests, cSHAKE256 and Ed25519, with layouts emitted into Rust by
[`Emit/`](Emit/).
Decoders refuse malformed, noncanonical or out-of-bound inputs; structural tags
identify shapes, and fixed vectors distinguish meanings a shape alone cannot
distinguish.
The design assumes the cryptographic primitives' security and the compiler and
runtime behavior recorded in [`gates/tcb.tsv`](gates/tcb.tsv).

**Protocol — the member's conversation.** Start at
[`Protocol/Table.lean`](Protocol/Table.lean) for operations and
[`Protocol/Command/Machine.lean`](Protocol/Command/Machine.lean) for the command
machine used by `host follow`: it plans calls, requests signatures, absorbs log
pages, settles attempts and refuses replies that do not check.
[`Protocol/Head.lean`](Protocol/Head.lean) defines heads, attestations and
certificates; `Std.head` stores a position in a World, and
[`Protocol/Foreign.lean`](Protocol/Foreign.lean) checks a foreign receipt against
such a held head.
Joining assumes a trusted sponsor key or genesis, and a foreign receipt assumes
the held head represents the foreign history being cited.

**Host — the durable process.** [`Host/DESIGN.md`](Host/DESIGN.md) introduces the
process boundary; [`Host/Deployed.lean`](Host/Deployed.lean) is the concrete
wiring of `host serve`, `host follow`, the Store and the pager.
The writer batches admissions, syncs MAC-chained log frames before acknowledging
them, seals whole-World bases, and periodically reopens its own Store; corruption
or a divergent reopen is refused by name, while a failed write or sync yields
`uncertain`.
Recovery assumes the filesystem's sync, rename and locking contracts, and a
trusted checkpoint or external anchor for the history it starts from.

**Ledger — value and escrow.** Start at [`Kernel/Value.lean`](Kernel/Value.lean)
for balances, denominations and credit floors, then
[`Ledger/Escrow.lean`](Ledger/Escrow.lean) for the concrete escrow package
shipped in [`world/escrow/`](world/escrow/).
Transfers conserve value, counted grants bound delegated spending, and escrow
couples its phase change to its transfer in one Turn, refusing an unauthorized
or repeated payout.
The ledger assumes the denomination's issuer and the escrow's named parties and
arbiter have the roles the members intend; conservation does not decide the
economic meaning of an asset.

**Hosting — residents and the Bell.** Start at
[`Hosting/Resident/Bell.lean`](Hosting/Resident/Bell.lean) for a resident's
decisions and [`Hosting/Broker.lean`](Hosting/Broker.lean) for provider access:
the concrete `resident` answers the Bell through its own member socket, and a
Lean decider authorizes and meters each model request.
The Bell in [`world/resident/`](world/resident/) is an activity with pending
rings and guarded answers; the broker refuses missing allowances, unauthorized
residents and malformed replies.
Its guarantees assume the member socket and durable volume contracts, while
provider availability and the usefulness of a model's answer remain external
facts.

**Rust — bytes, custody and processes.** Start at
[`client/DESIGN.md`](client/DESIGN.md): `client/` supplies `nd` and
`nd-supervise`, `launcher/` supplies `grain-launch`, `nd-members` and
`keybroker`, and `sandbox/` confines their children.
These programs carry frames, keep keys and attempts, and perform process and
filesystem operations, refusing unsafe custody paths and confinement failures;
law 2 assigns semantic decisions to Lean and gives Rust generated protocol tables.
This boundary assumes the OS isolation mechanisms and the Rust implementation
of the byte and effect contracts.

**Testground — a World in a browser tab.** Start at
[`testground/index.html`](testground/index.html): a desktop of member terminals,
object windows, demos and a wire inspector makes the system explorable.
[`Web/Sim/Testground.lean`](Web/Sim/Testground.lean) compiles the real writer and
follower decisions to WebAssembly; local mode runs the writer over an in-memory
Store, while hosted mode sends writer frames over a WebSocket and keeps the
follower in the tab, where forged replies are refused.
The visitor trusts the page's kernel and the channel that supplies its sponsor
key; the hosted setup is in [`deploy/testground/`](deploy/testground/README.md).

**Spec — the member-level claims.** Start at [`Spec/README.md`](Spec/README.md)
and [`Spec/System.lean`](Spec/System.lean): claims quantify over a record of
entry points whose concrete instance names the deployed functions.
Each top theorem has a floor that rejects a trivial substitute, such as a
follower that trusts the writer or a kernel that creates value.
The claim's named premises are part of its meaning: these include canonical
tries, faithful handling of the trusted adoption key, and `NoRef` laws for the
law-history claim (laws without references to other packages).

**Census, gates and scripts — checking the implementation.** Start at
[`gates/check.py`](gates/check.py) and [`gates/runs.tsv`](gates/runs.tsv):
source gates enforce ownership, module boundaries and size limits, while
[`Census/`](Census/) inspects elaborated declarations and their dependencies.
[`scripts/commit`](scripts/commit) is the concrete landing path, refusing a
candidate whose required checks fail; verdict readers themselves face known-red
controls.
These checks assume Lean's kernel and the explicitly listed trusted components,
and keep the distinction between a failed check and a check that could not run.

**Deploy, Ops and Bench — operating and measuring.** Start at
[`deploy/RUNBOOK.md`](deploy/RUNBOOK.md) for genesis, custody, joining, service
units, backup and recovery; `Ops/` emits the units and operator tables used by
the deployment.
[`Bench/`](Bench/) and [`scripts/bar.sh`](scripts/bar.sh) exercise the concrete
Store and client paths, refuse invalid measurements, and measure THE BAR:
two friends and a hosted resident using one World.
Operational guarantees assume the runbook's filesystem and identity setup;
performance limits are judged in the conditions the benchmark names.

## Ideas and literatures

These are the lines of work behind the design, and the choices that give nano its
particular shape.

- **Accountability by re-execution — PeerReview, SUNDR and SPORC.** Members
  reconstruct the writer's decisions and compare heads. Nano makes the same
  receiver the source of the writer's Turn and the follower's check, and makes
  consent before signing a property of that command path.
- **Receipts and trust — Certificate Transparency.** Authenticated paths let a
  member check a claim against a held head. Nano puts heads and their governing
  authority into the World's vocabulary, so an object can use a foreign receipt
  as an input to its own law.
- **Optimistic concurrency — Kung–Robinson, Sui and Fabric.** Calls commit to
  their read sets. Nano distinguishes a pin that is behind from one that is
  ahead, and refusals identify missing pin coordinates so a client can discover
  the observations its program needs.
- **Capabilities as state — KeyKOS, SPKI and macaroons.** Authority is delegated
  and attenuated. Nano stores the grant chain in the same authenticated state as
  the objects it controls, including counted rights consumed by a Turn.
- **Value and laws — EUTXO, XRPL trust lines, Cardano validators and Move.**
  Nano conserves balances and floors in the kernel; a language value does not
  itself carry money. Laws are indexed by the act they judge, and replacing a
  data object's laws requires judgment by both the old and incoming regimes.
- **Execution and fuel — CEK machines and CakeML's adequacy approach.** The
  metered machine is the shared execution semantics. Its relationship to the
  reference meaning and the fuel it requires is proved, so ticks have a
  specified meaning across re-executions.
- **Contextual meaning — contextual modal type theory, de Kleer's ATMS,
  Doyle's truth maintenance and why-not provenance.** A deferred choice is a
  typed slot with a justification. Nano checks that justification against the
  caller's pinned World and names the failed support when it withdraws a
  choice; the document makes that behavior visible as a suspended section.
- **Effects — Interaction Trees and sans-I/O.** Decisions describe effects
  that an outer process performs. Nano applies this boundary to the resident
  and its Rust plumbing, including a keybroker whose authorization policy is a
  Lean decider.
- **Canonical bytes — EverParse and Narcissus.** Encoders and parsers are proved
  together. Nano also treats structural tags' limits explicitly: relabeling
  same-typed cases can preserve a tag, so the vector table pins their byte
  meanings.
- **Durable logs and custody — Schneier–Kelsey and KERI.** Nano combines a
  MAC-chained log with precommitted key rotation. The writer's routine reopen
  compares recovery with its live state, exercising recovery during service.
- **Specification checks — mutation testing and Kupferman–Vardi vacuity.**
  A known bad system must fail the claim or gate intended to exclude it.
  Nano makes the verdict readers' ability to recognize failure a standing
  check, and `Spec/` gives the top claims explicit trivial countermodels.

## What a member is promised

The organizing promise is **one lawful history**: the member's World is an
audited fold from a start it consents to, and every step preserves the kernel's
integrity rules. Matching step counts and chains identify the same World, up to
a collision among the named link inputs. Value is conserved; an object's
history follows its laws.

**Consent and settlement** belong to the member's follower. It signs calls its
own copy admits. A submitted command ending `done ok` is in that copy's journal;
a successful cancel is settled there as cancelled. A final refusal stays final
on extensions, with stale finality tied to the pin comparison.

**Durability** means acknowledged steps survive recovery under the Store's
storage contract. **The Bell** carries this through a running application:
a resident keeps its request and answer across retries, answers through its own
member socket, and the Bell's guard prevents a second answer.

[`Spec/README.md`](Spec/README.md) is the precise map from these sentences to
claims, top theorems, floors and premises. It distinguishes the composed
history, value, law and settlement claims from the durability and Bell
compositions whose models and component proofs live in `Host/` and `Hosting/`.
Safety is a theorem under stated assumptions; progress is measured on the
running system.

## Where to read what

| Question | Start here |
|---|---|
| What rules shape the implementation? | [`CHARTER.md`](CHARTER.md), the twelve laws and scope. |
| Why is a layer designed this way? | [`decisions/`](decisions/README.md), one append-only file per layer, with alternatives, critique and meta-critique. Read later entries for revisions. |
| What does the system claim? | [`Spec/`](Spec/README.md), then its linked definitions and proofs. |
| How does a complete scenario work? | [`Lang/Journey/`](Lang/Journey/): documents, generators, heads, holes, offers and the inbox; [`Protocol/Rows.lean`](Protocol/Rows.lean) for member conversations. |
| What does the judge check? | [`gates/`](gates/), especially `runs.tsv`, `tcb.tsv` and `OWNERS`; [`scripts/commit`](scripts/commit) for landing. |
| How do I run a World? | [`deploy/RUNBOOK.md`](deploy/RUNBOOK.md) and [`deploy/testground/README.md`](deploy/testground/README.md). |
| Where are the original design records? | [`docs/record/`](docs/record/README.md), a historical archive; [`proposals/`](proposals/README.md), the interface proposals. |
| Where are the research memos and outside reviews? | In the separate **redregg** repository, under `work/promo/` and `work/readers/`. `DESIGN-CTX.md`, `TOPLEVEL-SPEC.md` and `DESIGN-TESTGROUND.md` explain the larger designs; the reader verdict and holistic reviews place them against the literature. |

## Building, running and working

[`lean-toolchain`](lean-toolchain) pins Lean v4.30.0. Lean uses core and Std,
with no external packages. The Rust crates share [`Cargo.toml`](Cargo.toml)
and its lockfile and build with stable Rust; the native host also needs a C
compiler. Warnings are errors in the Lean build.

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

`lake build` builds every default library and executable. `lake exe lang-journey`
runs all registered language scenarios; select the scenarios or named protocol
rows relevant to a change while developing. Rust tests are filtered, for example
`cargo test --locked -p nanodregg-client --test frame`.
On the shared build host, use its `swarm-build` resource controls and the
layer's memory budget; whole-tree builds belong to the coordinated convergence.

The host executable is `.lake/build/bin/host`; the release client is
`target/release/nd`. Follow the runbook to create a Store and connect each
member's follower through `nd-supervise`. For the browser, follow
[`testground/build/build.sh`](testground/build/build.sh): it emits Lean's C,
builds the WebAssembly module with Emscripten, and copies the demo packages for
a static server.

Main is the integration branch. Work in a detached worktree within
[`gates/OWNERS`](gates/OWNERS), run the affected checks, and land exactly the
paths intended with `scripts/commit -F MESSAGE_FILE PATH...`.
The script merges against current main and judges the candidate before landing
by compare-and-swap. Ordinary changes take the source gates and the build they
reach; flag days and judge-code changes take the full judge.
[`scripts/converge`](scripts/converge) coordinates the whole-system check, and
[`scripts/standing.sh`](scripts/standing.sh) produces its verdict.

Definitions and proofs live in separate modules. Changes to decisions append
their reasons and both critiques. [`SIZE.md`](SIZE.md) is generated;
[`gates/ceilings.tsv`](gates/ceilings.tsv) and
[`gates/waste.tsv`](gates/waste.tsv) hold the size and work limits.

## Provenance

nanodregg is rebuilt from minidregg's specification and battleground: its
journeys, simulations, workload and meaningful theorem statements.
It is a focused research demonstration that minidregg can draw from, within the
Dragon's Egg lineage whose earlier whole-system exploration is dregg
(breadstuffs).

License: [AGPL-3.0](LICENSE).
