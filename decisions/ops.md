# decisions/ops.md — BUILD-OPS (format: decisions/README.md)

OPS is the operator's path: genesis, units, backup/restore, status. It renders and drives; it
decides nothing that HOST, KERNEL or CLIENT decides. Source of the row: ASSEMBLY-ops.md (the Opus
evaluation of scouts O1–O5, `~/dev/redregg/work/nanodregg-scout/`).

## OPS-0 · the row: a renderer and a driver, and nothing imports it (2026-10-16)

**Decision.** OPS owns `Ops/` (Lean: unit renderer, the test founder, the backup plants), `deploy/`
(the emitted units, `deploy/RUNBOOK.md`, `deploy/live/` harness scripts) and this file. NOT `ops/`:
on the Mac reader (case-insensitive APFS) `ops/` and `Ops/` are ONE directory, so a lowercase
`ops/` tree silently lands inside the Lean library (it did, in my Mac worktree: `ops/RUNBOOK.md`
became `Ops/RUNBOOK.md`). gates/OWNERS' `ops/` row was replaced by `deploy/` and the `paths` gate
refuses case-colliding paths (GATES-2, aa4c0ab). Every number it
renders is read from another layer's Lean value (HOST's `Status.codesOf`, CLIENT's nd-supervise
grammar), never copied. Closure rule C10 (GATES, 5be0d98): nothing outside `Ops/` imports `Ops`.
**Alternatives.** (a) No OPS layer: units in `client/`, plants in `Host/Sim/`, the runbook in
`Host/DESIGN.md`. Each piece is small, but then nobody owns "can an operator actually run this",
and that is exactly what was never exercised: the first `host serve` on a missing Store died
`uncaught exception`, exit 1, no name (fixed in 28de15e). (b) OPS inside HOST: HOST would render
its own units, which is fine until a unit needs CLIENT's grammar too.
**Why.** The operator's path crosses three layers (HOST's exits, CLIENT's supervisor, the service
manager). A renderer over their values is the one place that can be checked against all three.
**CRITIQUE.** A layer whose deliverables are "glue" grows into minidregg's ops-utilities hub: every
"where does this go" lands here. C10 stops other layers depending on it, not it from growing. The
guard is the SIZE ratchet on `Lean lines (Ops)` and this rule: an Ops module that would DECIDE
(choose a restart policy, judge a Store) is a defect; ask the owner.
**META-CRITIQUE.** I was spawned as OPS, so I argue for OPS. The honest test is (a): if after the
units land Ops/ is only `Units.lean` + `Plants.lean`, it may belong in GATES' tooling.
**Status.** row accepted by ROOT 10-16 ("renderer/driver; nothing imports Ops").

## OPS-1 · law 1: state is carried only by re-genesis from a checked export (2026-10-16)

**Decision (argued to ROOT; landed as charter text b3787d3).** "Old SHAPES refuse to load; STATE may
be carried only by re-genesis from a checked export." Concretely:
- **export = the fold**: the World a Store opens to (`openFollower` + the writer's `foldStep`, the
  same open `host check` runs), as CODEC's canonical World bytes.
- **import = genesis under a new epoch** whose initial World is that World's cells, re-sealed
  under the new build's codecs and a new Store key.
- **check**: the imported World's canonical bytes equal the exported World's, up to the epoch's own
  header fields (origin, height, chain, the journal).
- **not carried**: every signature over old bytes — calls, possession proofs, the journal's txIds,
  receipts. History is never carried, only state. A member's old receipts do not verify against
  the new World; that is correct, not a loss to be patched.
**Interaction with KERNEL-4's D3 (World-bound calls).** A carried World is under a new origin, so
every call signed for the old World is `wrongWorld` in the new one. Without D3, a carried World
whose founder ids survive is replay-open for every old call with `validUntil` ≥ the new height
(OPS-2): carry makes D3 mandatory, not optional.
**Alternatives.** (a) Law 1 as written ("nothing migrates"): a flag day destroys friends' data, so
"re-genesis is free" is false in the product sense the first day there is data. (b) O2's `carry`
(rename every id, rewrite slots by role, custody-supplied precommits): a migration with its own id
derivation and role table, twins of the kernel's (discarded by the evaluator). (c) Carry history
too (re-sign): impossible without every member's key; a carried history would be the operator
attesting to itself.
**Why.** It keeps "old shapes refuse to load" (the fix for silent reinterpretation) while making
state survival a checked, one-way, operator-initiated act rather than a reader that understands
two shapes.
**CRITIQUE.** "Up to the epoch header" is where a migration hides: if the header grows a field
that the importer fills from the old World by interpretation, it is a second reader of the old
shape. The check must be byte equality of the cells part, with the header fields listed, never
"equivalent". Ids: if cell ids are derived from the World origin (D3's alternative), carried cells
keep old ids that no new derivation produces; that is acceptable only while ids are opaque.
**META-CRITIQUE.** ROOT's brief framed carry this way and I restated it; the scout (O2) did the hard
part I declined (ids by role). Nothing here is built: the export/import verbs do not exist, so
this is a law, not a capability, until HOST/KERNEL build `export`/`import` and a plant (import a
World whose bytes differ → refused by name).
**Status.** ACCEPTED by ROOT 10-16; charter b3787d3.

## OPS-2 · cross-World replay: reproduced against the real `host`, routed to KERNEL-4 (2026-10-16)

**Finding.** Two `host genesis STORE w KEY NEXT` runs with the same label and founder keys produce
identical founder ids and genesis chains (`Receive.genesis` places founder i at
`founderId X name i`; `Unsigned` names no World; `worldId` is a constant). One signed `create`,
pinned only on founder 0's cell, admits in both Stores (status 0, height 1, same turn digest
d9b10451…), each with its own random Store key; in process the same World refuses it `replayed 1`
and a second genesis admits it again; a different label refuses `unknownKey` (the accidental
immunity). Deployed Ctx, real Ed25519 (RFC 8032 TEST 1). Driver + logs:
`~/dev/redregg/work/ops/replay-20261016/`. Replay is bounded by `Bounds.windowMax` (1024 heights:
`validUntil ≤ notBefore + 1024`), so it is open for the first ≤ 1024 heights of the new World.
**Routing.** KERNEL-4: D3 (signed `world` = the genesis origin nonce, `wrongWorld`, the one-World
theorem, the Sim plant). PROTOCOL-4: the `wrongWorld` row, blockedOn KERNEL. HOST: `host genesis`
draws the nonce (HOST-4). OPS: the RUNBOOK's re-genesis step names it as the HOST-side consequence.
**CRITIQUE.** I reproduced the case the evaluator predicted; I did not look for a second replay
path (e.g. a grant chain whose ids are name-derived).
**META-CRITIQUE.** A reproduction is evidence, not a fix; my urge to "just add the nonce" is the
quick fix the kernel owner must not inherit.
**Status.** routed (ROOT 10-16).

## OPS-3 · backup = the three files in order; restore = `host check --anchor` (2026-10-16)

**Decision.** A backup copies `key`, then `base.world`, then `seg.log` (ASSEMBLY D7). A restore
copies them back and runs `host check STORE --anchor HEIGHT:CHAIN` (D6, landed 28de15e), with the
anchor from a member follower's head or the highest receipt a client holds. The plant table
(`store-plants HOST DIR`, Ops/Plants.lean) runs the real `host` exe, deployed Ed25519, anchors
computed independently by `Receive.submit`:

| plant | without anchor | with anchor |
|---|---|---|
| intact copy | — | eof (0) |
| cut at a frame boundary | **eof: opens at a lower height** | behindAnchor |
| cut mid-frame (torn) | eof, torn>0 | behindAnchor |
| one foreign last frame (HOST-12's undecidable case) | **eof** | behindAnchor |
| drop a middle record | corrupt | — |
| flip a byte in a record after the base | corrupt | — |
| flip a byte in the origin frame, before the base | corrupt ("corrupt history") | — |
| wrong key | baseCorrupt | — |
| rollback to an older complete copy | **eof** | behindAnchor |
| another history, same key, same height | — | chainMismatch |
| anchor at a past height (own / other history) | — | eof / chainMismatch |
| missing Store | io | — |
| `check` writes nothing (torn copy keeps its bytes) | PASS | — |

The three bold rows are why an anchor is not optional: without one, `check` certifies integrity
and height, never completeness, and its line says `anchor=none`.
**Found by planting.** Since 9f2373e's origin frame, the bytes before the base are read by no open;
a flipped origin byte opened clean. `host check` now recovers that prefix (`historyClean`).
**Alternatives.** O3's MANIFEST (a second authenticated inventory): forgeable under HOST-16 (the key
is in STORE), and it still accepts a rollback. Discarded; the anchor is the only real check.
**CRITIQUE.** (1) The copy is plain file reads in a fixed order; the live-copy race (copy during a
running `host serve`, a seal renaming `base.world` mid-copy) is ARGUED safe (rename keeps the old
inode; the segment is append-only, so a later segment copy is a superset of any base's offset) and
NOT YET PLANTED: it needs a running writer, and the Mac is frozen for runs (ROOT 10-17). (2) No
plant seals a base (1 MiB cadence), so `segmentShort` and the pre-base history check after a
real seal are unexercised. (3) An anchor is only as good as its source; a lying follower is the
trust the operator chose.
**META-CRITIQUE.** The table is the scout's (O3) restated for HEAD; I added rows where my own run
surprised me. The rows I could not run are the ones most likely to be wrong.
**Status.** open (plants landed with the `ops:` commit after 28de15e; live-copy and sealed-Store rows
PENDING an execution node).

## OPS-4 · the test founder signs with RFC 8032's published vectors (2026-10-16)

**Decision.** `Ops.Founder` signs calls with `Codec.Ed25519.sign` under RFC 8032 §7.1 TEST 1's
secret key (next key: TEST 2's public key). These are published test vectors, not key material;
no real seed is ever generated, held or copied by OPS.
**Alternatives.** openssl over the same vector (used for the first reproduction, OPS-2): a second
signer outside Lean. PROTOCOL's `toySign` rows: not the deployed verifier.
**CRITIQUE.** A test key known to the world signs calls that real `host` exes admit; anyone who
boots a World with this founder has a World anyone can write. Genesis must never be run with it
outside a plant directory; the RUNBOOK says so.
**META-CRITIQUE.** Convenience: the vector was already in my scratch driver.
**Status.** open.

## OPS-5 · THE BAR is PERF's; OPS builds no BAR driver (2026-10-17)

**Decision.** Retract the evaluator's step 6 (`Ops/Bar.lean` + `bar` exe). PERF-1 (`scripts/bar.sh`,
b616a8d) already runs THE BAR through the deployed processes (two confined members, one confined
writer, real sockets). A second BAR driver would be two measurements of one bar (law 1). Ember's
ruling 10-17: no wall-clock benching until near the end of development.
**CRITIQUE.** PERF's BAR goes through `nd` and so cannot isolate the Host loop; if a regression must
be localised, the in-process rows (`rows --times`) and a Bench number are the tools, not a third BAR.
**META-CRITIQUE.** Dropping a deliverable is cheap to argue; check that nothing in the RUNBOOK
needed the Ops driver (it does not: the RUNBOOK cites PERF's script).
**Status.** CONFIRMED by ROOT 10-17 (Ops/Bar.lean deleted from the plan).

## OPS-6 · one prevent list from both exit tables, a start limit, and a generated operator table (OPS-2, 2026-10-17)

**Decision.** (a) `Ops.Units.preventCodes := Status.codesOf .fatal ++ SupervisorExit.codesOf .fatal`
(CLIENT-2's Protocol.Exit, 5122e62): nd-supervise passes the child's code through, so a unit reads
one code space and must stop on both tables' fatal exits. `ofNode_prevent` (a Host status is
prevented iff fatal) and `ofNode_prevent_supervisor` (a supervisor exit is prevented iff fatal)
hold over the joined list; the Host half needs `code_disjoint_host` (no supervisor code is a Host
code). Tooth: `preventCodes_supervisor_split` (66 restarted, 64 prevented) is false if the
supervisor half is dropped. (b) Every unit gets `StartLimitIntervalSec=120`, `StartLimitBurst=5`.
(c) `deploy/units/EXITS.md` is RENDERED by `emit-units` (code, name, class, what the unit does,
what the operator does) from both tables and two exhaustive matches, `hostAction` and
`supervisorAction`; the RUNBOOK's hand table (§7) is deleted.
**Breaking.** Both `.service` files re-render: `RestartPreventExitStatus` gains 38 39 42 43
(HOST's statuses since b2b901d) and 64 65; `[Unit]` gains the start limit. `gates/generated.tsv`
now checks `deploy/units` (unit files and EXITS.md), so a hand edit or a table change without a
re-render is red.
**Alternatives.** (1) Keep the RUNBOOK's hand table: it was already wrong at b2b901d+10 commits
(no 29, 38–44, 64–66; fuel listed as removed while the constructor stays). (2) Operator text as
HOST docstrings, read by a meta program: one source, but `emit-units` would read docstrings from
the environment (compile-time reflection in a renderer) and HOST's prose would become operator
instructions nobody owns. (3) No start limit, relying on systemd's default: 5 starts in 10 s
never trips at `RestartSec=2`, so a deterministic crash in a restart class (66 on every start)
loops forever, the "silent restart" the exit table exists to prevent.
**Why.** The prevent list must be a function of the tables or it drifts (the old 2/70/1 did). The
operator table is the same data plus one sentence per code; a generated copy cannot drift and an
exhaustive match cannot forget a code.
**CRITIQUE.** The exhaustive match couples HOST to OPS: a HOST commit adding a Status does not
build `Ops.Units` until it adds a `hostAction` arm, i.e. a cross-layer edit or an OPS commit
first. That is the point (every exit has an operator action) but it is friction on HOST's path,
and an arm written by HOST in a hurry ("report to HOST") is a placeholder in clothes. The start
limit's numbers (5 in 120 s) are taste: they bound a crash loop to ~10 s of restarts per 2 min
window, and a slow-burn restart class (an `uncertain` once a minute) never trips it, which is
correct for a transient and wrong for a slow deterministic fault. Restart-class exits are
transient BY ASSUMPTION in both tables; the limit is the only check of that assumption.
**META-CRITIQUE.** (c) grew from "update §7" into a generator, the move a renderer-owner likes;
the test is whether anything else would have caught the stale table: nothing did for ten commits.
I did not argue (b) with HOST/CLIENT, whose classes it reinterprets as "transient up to 5 in 120 s".
**Status.** landed with this commit; HOST-5 and CLIENT told of the coupling.
