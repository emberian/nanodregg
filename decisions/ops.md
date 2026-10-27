# decisions/ops.md — BUILD-OPS (format: decisions/README.md)

OPS is the operator's path: genesis, units, backup/restore, status. It renders and drives; it
decides nothing that HOST, KERNEL or CLIENT decides. Source of the row: ASSEMBLY-ops.md (the Opus
evaluation of scouts O1–O5, `docs/record/ASSEMBLY-ops.md`).

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
- **not carried**: every signature over old bytes — calls, join consents, the journal's txIds,
  receipts. History is never carried, only state. A member's old receipts do not verify against
  the new World; that is correct, not a loss to be patched.
  (Corrected 2026-10-26, PROTOCOL-79: this line said "possession proofs". Possession of a key is a
  fact of the key, shown by any signature it makes, so it is neither carried nor not; what is bound to
  a World is a JOIN, the consent a new key signs over `domJoin ‖ origin ‖ sponsor ‖ next ‖ key`. A
  carried World's join is a new join (the old consent is refused `otherWorld` there); members already
  in the exported World are carried as members, with their state (KERNEL-40).)
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
**Status.** ACCEPTED by ROOT 10-16; charter b3787d3. BUILT 2026-10-17: KERNEL-29 (b8e0f82, Carried
{trie, allowance, height, journal}), CODEC-22 (28b4a38, content-addressed carried codec), HOST-28
(6b89d6f, `export` / `import --digest`), planted through the real exe by OPS (store-plants
`carry-*`, 13 rows) with RUNBOOK §6. The "up to the epoch header" worry of the CRITIQUE is closed by
byte equality of the carried codec plus the required digest; the id worry stands (carried member
ids keep the old-origin keying; members sign the new origin under their old ids).

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
**Status.** CLOSED by KERNEL-24 (9e91ede). Planted against the real exe (OPS-2, the plants commit
after it): the same call served to a second genesis under another nonce does not land
(`replay-other-nonce-not-admitted`), and under the same nonce it does
(`replay-same-nonce-admitted-control`, the restore case). The RUNBOOK's never-reuse-a-LABEL rule
is replaced by "a fresh nonce, never an old one".

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
**Planted since (OPS-2).** One live `host serve`, fed 48 calls holding a 48 KiB slot each (so it
seals real 1 MiB bases while it runs), with the backup interleaved at its worst point: `key` and
`base.world` copied, the writer fed until it seals a newer base (polled by `host check`, bounded),
then `seg.log`. Rows: live-copy-raced-a-seal (asserts the copied base is no longer the Store's,
or FAILS), live-copy-anchor-at-segment-copy (eof at the writer's height), sealed-store-has-a-real-base
(asserts base past the origin, or the rows after it test nothing), sealed-intact-anchor (eof),
sealed-segment-cut-below-base (segmentShort), sealed-flip-history-before-base (corrupt history,
after a real seal), copy-segment-before-base-wrong-order (segmentShort: why the order is the rule).
**CRITIQUE.** (1) The live interleave is deterministic in ORDER (copy, feed to a seal, copy) but
not in where inside the copy of one file a rename lands; the argument (a rename keeps the open
inode) covers that and no plant does. (2) The seal is async, so which height the writer seals at
varies run to run (12 or 16 seen); the rows assert relations (a newer base, the writer's height),
never a number. (3) An anchor is only as good as its source; a lying follower is the
trust the operator chose.
**META-CRITIQUE.** The table is the scout's (O3) restated for HEAD; I added rows where my own run
surprised me. The rows I could not run are the ones most likely to be wrong.
**Status.** ACCEPTED: every row of the table and the live and sealed rows run in store-plants
(standing's `plants=` stage).

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

## OPS-7 · the broker's production TLS anchors are a build-pinned generated file (HOSTING-15, 2026-10-17)

**Decision.** `deploy/tls/anchors.pem` is the keybroker's ANCHORS for production: concatenated PEM
CERTIFICATE blocks, one per `webpki_root_certs::TLS_SERVER_ROOT_CERTS` entry in the crate's order,
emitted by `emit-anchors` (workspace member `deploy/anchors`, webpki-root-certs `=1.0.9`). The
`cargo:emit-anchors deploy/tls/anchors.pem` row of gates/generated.tsv (GATES-2's 2ed0386) checks
it byte for byte on every commit, so an edit that widens trust is red, and so is a version bump
without a re-emit. A test passes its own CA file; production never does.
**Alternatives.** (1) The broker reads webpki-root-certs at runtime: no operator data, but then the
test cannot pass its own CA without a second code path (HOSTING-15's reason for ANCHORS). (2) The
OS trust store: not pinned by build, and differs per box. (3) A Lean emitter: the roots are a Rust
crate's bytes; a Lean copy would be a twin.
**CRITIQUE.** The pin decides trust: 121 public roots is wider than the one upstream the broker
calls. A per-upstream pin (one root, or the upstream's own CA) would be narrower; that is
HOSTING's call per upstream, and this file is the default. The base64 encoder is hand-written
(no dependency) and tested only on RFC 4648's vectors and by openssl parsing all 121 blocks once.
**META-CRITIQUE.** "Generated + checked" is the shape I already own (emit-units, STORE.md), so I
reached for it; the test of it is the alternative (1)'s second path, which it avoids.
**Status.** landed with the file it checks.

## OPS-8 · the keybroker unit, rendered from HOSTING-16's exit tables, checks its anchors at every start (2026-10-17)

**Decision.** `deploy/units/linux/nd-keybroker.service` is rendered by emit-units from `Ops.Units.keybroker`
(paths through checkPath, upstream a plain host:port): User=nd, keybroker's nine arguments in its
order with ND_OPERATOR/ND_RESIDENTS from `/etc/nd/keybroker/keybroker.env`, RuntimeDirectory
`nd-keybroker` (PID file) and `nd-keybroker/sock` (sockets), `ExecStartPre=emit-anchors --check` on
the installed anchors (HOSTING-15's install check, made a start condition), and
`RestartPreventExitStatus` = `DeciderExit.codesOf .fatal ++ KeybrokerExit.codesOf .fatal`
(HOSTING-16, 12ce0ff; asked by OPS because keybroker exited 1 for a custody refusal and a transient
end alike). Theorems: mem_brokerPrevent_decider / _keybroker (prevented iff fatal),
brokerPrevent_panic_and_done (101 and 0 never prevented), brokerPrevent_split (the tooth).
EXITS.md gains both broker tables with exhaustive operator sentences. Measured on hbox (AppArmor
userns restriction ON): nd-supervise's confinement runs under NoNewPrivileges (`setpriv
--no-new-privs`), so the units' NoNewPrivileges=yes does not break the nd-bwrap profile.
**Alternatives.** (1) The install check as an operator step only (HOSTING-15's wording): an edited
installed copy would then be read at the next restart, long after the check. (2) keybroker
confined by nd-supervise: it needs outbound TCP 443, which the sandbox (no network) refuses by
design; it confines its decider itself.
**CRITIQUE.** An ExecStartPre failure is not the main process's exit, so RestartPreventExitStatus does
not stop it: a bad anchors file is retried until the start limit (5 in 120 s), named in the journal
each time. The sockets' mode (0600 under UMask=0077) admits only `nd`: a grain under another uid
cannot connect until HOSTING's stage 3 says who may. The unit is RENDERED, not RUN: no box has
run it under systemd (the burst5 harness was torn down); its first run is a deploy-time fact.
**META-CRITIQUE.** Making the check a start condition is stricter than asked; the cost is an
emit-anchors binary on the node, which I chose without asking HOSTING.
**Status.** landed; run PENDING a box.

## OPS-9 · HOST-33's moved check, planted through the real exe; the operator runs `check` (OPS-3, 2026-10-18)

**Decision.** HOST-33 (ff60a08) moved the detection of a corrupt middle `index.log` entry from open to
first read or `host check`. store-plants plants it on the sealed live Store `L` (48 calls, base at
height 40, 6 counted entries of 80 bytes at hbox): `index-middle-entry-is-counted-not-last` (the
precondition: whole entries, the flipped entry `k = total/2` is counted and not the last, so open does
not read it and every page's binary search reads it second), `index-middle-log-page-intact-control`
(founder 0's signed read envelope, `Founder.logFrame`, answered `ok` by the intact copy),
`index-middle-flip-opens-page-badIndex` (`serve` exits 0 and answers that page `refused badIndex`),
`index-middle-flip-check-indexCorrupt-names-entry` (46, `refused indexCorrupt entry 3`). The RUNBOOK
(§3) says where the detection now sits and tells the operator to run `check` on every backup; the
`badIndex` operator sentence says a writer never exits 34 on a page (only `host check --anchor` does);
the `orphan-index-page-*` rows are renamed `orphan-index-entries-*` and STORE.md's wording follows
(there are no index pages since HOST-33).
**Tooth (measured, not committed).** With `Entry.read`'s tag comparison removed in Host/Base.lean, the
two flip rows FAIL by name: the page is SERVED (status 0, 247 243 bytes, built from the flipped entry,
since the walk reads frames by offset) and `check` exits 0.
**Alternatives.** (1) Flip entry 0 (the other always-read entry): it is not a middle entry, and HOST's
host-sim already flips every position in process; the exe row exists for the middle. (2) Assert the
probe sequence of `Page.locate` from outside: it would copy HOST's search into OPS (a twin); the row
instead asserts the precondition it relies on and FAILS if `total/2` stops being a counted middle entry.
**CRITIQUE.** The row depends on `locate` reading `total/2` second; if HOST changes the search the
precondition row still passes and the page row may go red on an honest page that never read the
flipped entry. That red is loud and points at the change, but it is a coupling to HOST's search, named
here. The plant has 6 entries: it says nothing about large indexes (host-sim's entryRows does). A
Store whose damaged entry nobody pages through serves until `check` runs: the operator step is the
whole defence for history nobody reads, and nothing schedules it.
**META-CRITIQUE.** I chose the row HOST-9 described rather than asking whether OPS should schedule
`check` (a timer unit) — the gap the CRITIQUE names; a periodic check is a unit OPS could render, and
I deferred it as not asked for (cv task below).
**Status.** landed with this decision.

## OPS-10 · the node's two users, SOCKDIR and the writer's runtime directory are rendered; the nd-hosted follower waits for CLIENT-3's socket group (OPS-3, 2026-10-18; ROOT ruling on HOSTING-17 §7)

**Decision.** emit-units renders, from `Ops.Units.keybroker` (which gains `hosted := "nd-hosted"`):
`deploy/units/linux/sysusers/nd.conf` (`u nd`, `u nd-hosted`, each its own primary group, no `m`
line) and `deploy/units/linux/tmpfiles/nd-broker.conf` (`d /run/nd-broker 2710 nd nd-hosted -`).
`Broker.check` refuses `hostedIsKeyHolder` first (HOSTING-17's CRITIQUE: keybroker cannot tell a
SOCKDIR of its own primary group from the one-uid test, so the install refuses it), with
`Broker.check_hosted_ne_user`, `tmpfiles_hosted_ne_user`, `sysusers_hosted_ne_user` and the plant
`plant_hosted_is_key_holder`. The writer's unit gains `RuntimeDirectory=nd`: nothing made `/run/nd`
on a fresh box, so the rendered `nd-supervise /run/nd/host.sock` had no directory to bind in. A
node with a runtime directory names its socket by FILE NAME and `Node.sock` composes `/run/NAME/FILE`,
so a socket outside its runtime directory cannot be written (`ofNode_runtime_system`); a runtime
directory on a user unit is refused `runtimeOnUserUnit` (`plant_runtime_on_user_unit`). The
ofNode proofs now go through one `ofNode_ok`. Measured on hbox (systemd 256, `--dry-run`, no box
change): sysusers parses and would create both users and groups; the tmpfiles line fails
`Failed to resolve user 'nd'` until they exist, so the RUNBOOK orders users before tmpfiles.
**The follower (ROOT's ruling, recorded here and owed to HOSTING-17).** `host follow` advances only
when a client drives it over its socket and relays its log asks to host.sock, and nd-supervise binds
every socket 0600, so nothing running as nd-hosted could be fed. ROOT ruled (B): the TRUSTED side
initiates to the less-trusted side, never the reverse. host.sock stays nd-only (unchanged: no
widening of who may connect to the writer). The nd-hosted follower binds its socket in
`/run/nd-follow` (tmpfiles `d /run/nd-follow 2710 nd-hosted nd -`; setgid gives it group nd, and
nd-hosted joins no group), nd-supervise binds it 0660 under CLIENT-3's `--group GID` (refused at
launch unless the directory is the unit user's, 02710, a trusted chain, group GID), and the driver is
the existing client `nd` running as nd (`nd-follow-drive`), the relay the client already is. What
widens: nd may connect to the follower's socket (a process nd already fully trusts). The gid is
operator data (`ND_GID` in the unit's environment file, `getent group nd`), as ND_PEER is: no NSS
lookup in Rust, no number in a generated file. Rendered when CLIENT-3's flag and HOST-10's path
shape land.
**Alternatives.** (1) The users and SOCKDIR as RUNBOOK prose only (OPS-2's §2a): an operator types the
mode, and nothing refuses `nd-hosted` = `nd`. (2) `RuntimeDirectory=` for SOCKDIR: deleted at every
stop, which breaks running sandboxes (HOSTING-17 §4). (3) A free socket path plus a check that it
lies under `/run/NAME/`: string containment cannot be planted by `decide` (String does not reduce in
the kernel), and by construction is stronger than a check. (4) Pinned numeric uids in sysusers: the
renderer would then know ND_PEER/ND_GID, but a pinned id collides with whatever a box already
allocated; ids stay the box's.
**CRITIQUE.** sysusers and tmpfiles are systemd-only; the Mac (a member machine) needs neither, but a
non-systemd Linux writer node has no rendered equivalent. `Broker.check` refuses only `hosted =
user` by NAME: two different names for one uid (an operator who aliases) pass, and only keybroker's
PEER/SO_PEERCRED check at runtime sees uids. `RuntimeDirectory=nd` is removed at stop, so a client
holding the old socket path sees ENOENT until the restart binds it: the same as before for the
socket, now also for the directory. None of these units has run under systemd yet (§2 PENDING).
**META-CRITIQUE.** I first wrote the runtime check as a string test and turned to construction only
when the plant would not reduce — the right design arrived from a proof obstacle, not from the
question "can it be wrong?", which I should have asked first. I lean toward rendering more files
(two new ones) where the RUNBOOK sufficed; the test is whether an operator ever types a mode by hand.
**Status.** landed with this decision; follower and grain-launch units PENDING (CLIENT-3 `--group`,
HOST-10 path shape, HOSTING-6 grain-launch exit table).

## OPS-11 · the hosted follower is a template unit per World, its socket flat in /run/nd-follow (OPS-3, 2026-10-18)

**Decision.** `deploy/units/linux/nd-hosted-follow@.service` (instance = the World's label):
User=nd-hosted, `nd-supervise /run/nd-follow/%i.sock … --group ${ND_GID} …` (CLIENT-21, 77fde4e),
writing `/srv/nd-hosted/worlds/%i/store` (the path grain-launch's controller reads), environment
`/etc/nd/hosted/%i.env` (ND_MEMBER/ND_GRANT of an observe-only member, ND_GID), hiding `/etc/nd`
and `/home`; `deploy/units/linux/tmpfiles/nd-follow.conf` `d /run/nd-follow 2710 nd-hosted nd -`.
Node gains `template` (`%i` allowed in its paths; a plain unit's paths still refuse `%`, so an
instance cannot leak into a non-template unit) and `group` (`--group ${ND_GID}` inside
nd-supervise's options: `ofNode_group`). Path agreed with HOST-10 and CLIENT-3: FLAT, one socket per
World in one directory, not a directory per World: nothing binds the follower socket into a
sandbox (HOSTING-17 §4's reason for per-resident directories), and a per-World directory would
need one tmpfiles line per World, operator data no generated file can hold. The rendered argv is
run through the real nd-supervise by `deploy/live/follow-argv.py`: on hbox `/tank` it is refused
`sharedDirRefused: Dir(...)` (64), the grammar accepted.
**Alternatives.** (1) A unit per World rendered with the label baked in: generated files would hold
operator data. (2) `Group=nd` on the follower: the process would run with nd's gid and reach nd's
group-readable files; ROOT's rule is that nd-hosted joins no nd group. (3) The socket in a
RuntimeDirectory: owned by User= with its primary group, not nd, and removed at stop.
**CRITIQUE.** The follower is rendered but cannot advance until PROTOCOL-7's `sync` and CLIENT-3's
custody mode land: a unit that serves and never moves. It is landed now so the driver unit renders
against a real follower, and the RUNBOOK says so. All Worlds' follower sockets share one directory
and one group: any process of uid nd can reach every World's follower, which the trust direction
allows (nd is the trusted side) but which no check narrows. `%i` is systemd's ESCAPED instance; a
label with characters systemd escapes would name another path. Labels are plain today
(Controller's badLabel); that coupling is unproven. The positive run (a passing chain, nd connecting)
is PENDING on burst5.
**META-CRITIQUE.** I took the per-World-name shape to HOST and CLIENT with an argument from
operator data ("no generated file can hold it") that is a convenience of my renderer; the stronger
argument is that nothing needs the directory. Both were stated; the first could have carried a
worse design.
**Status.** landed; the driver (`nd sync` timer) PENDING PROTOCOL-7 + CLIENT-3; grain-launch PENDING HOSTING-19.

## OPS-12 · the grain launcher is a template unit per World, rendered from HOSTING-19's two exit tables (OPS-3, 2026-10-18)

**Decision.** `deploy/units/linux/nd-grain-launch@.service`: User=nd-hosted, RuntimeDirectory
`nd-grain-launch/%i` (the grains' PID files), `grain-launch /srv/nd-hosted /run/nd-broker %i
/run/nd-grain-launch/%i /opt/nd/bin/hosting-controller /srv/nd-hosted/worlds/%i/store %i`,
`Wants=`/`After=` its World's follower, `After=` keybroker, `RestartPreventExitStatus` =
`ControllerExit.codesOf .fatal ++ LaunchExit.codesOf .fatal` (8be4026). Exhaustive operator
sentences `controllerAction`/`launchAction`; EXITS.md gains both tables. `Launcher.check` refuses
a launcher whose controller Store is not its follower's or whose user is not the follower's
(`Launcher.check_follower`). Theorems: `mem_launchPrevent_controller`/`_launch` (prevented iff
fatal), `launchPrevent_panic_and_done`, `launchPrevent_split` (the tooth). The rendered argv runs
through the real grain-launch and the confined controller (`deploy/live/unit-argv.py`, which
replaces OPS-11's follower-only script): over an empty store directory, controller `store` 109
passed through, grain-launch exits 109.
**Alternatives.** (1) grain-launch under nd-supervise: it confines its own children (each a
`sandbox::command`), and the controller must spawn grains; a second confinement layer would have
to allow exactly what grain-launch does. (2) `RestrictAddressFamilies=AF_UNIX`: bwrap's
`--unshare-net` configures loopback over netlink, untested under that restriction, so not rendered
until a box runs it. (3) `Requires=` on the follower: a follower restart would then stop every
grain; `Wants=` keeps them apart (the controller tails a Store, it does not talk to the follower).
**CRITIQUE.** The unit has run on no systemd box; the argv row is a parser row, not a start. A
controller over a follower that never advances (the driver is PENDING) sees an empty World and
launches nothing: green and idle. `%i` is used as grain-launch's LABEL verbatim: the instance name
must be the World's label exactly (systemd escapes `-` and `/` in instance names).
**META-CRITIQUE.** I chose `Wants=` over `Requires=` from a restart argument without measuring how a
controller behaves when its follower Store is being written mid-seal; HOST-10 says Tail.open reads
unlocked and writes nothing, which I took on their word.
**Status.** landed; the burst5 run (with the keybroker's) PENDING.

## OPS-13 · the follower's driver is an always-restarting `nd sync` per World, not a timer (OPS-3, 2026-10-18)

**Decision.** `deploy/units/linux/nd-follow-drive@.service`: User=nd, `nd sync` with
`ND_WORKSPACE=/etc/nd/follow/%i` (CLIENT-22's observer custody), `ND_FOLLOW_SOCK=/run/nd-follow/%i.sock`,
`ND_HOST_SOCK=/run/nd/host.sock`; `Restart=always`, `RestartSec=40`,
`RestartPreventExitStatus` = `CommandExit.codesOf .fatal` (refused, 1). `Driver.check` refuses a
driver that is not the writer's user, is the follower's user, or talks to another host socket
(`Driver.check_trusted`: ROOT's direction rule as a render refusal). `commandAction` exhaustive;
EXITS.md gains the `nd sync` table. Theorems `mem_drivePrevent`, `drivePrevent_split`,
`sync_loop_under_start_limit` (120 / 40 + 1 < 5).
**Alternatives.** (1) A `.timer` firing a oneshot (what CLIENT-3 and I first said): a timer starts
its service again after a fatal end, so a refusal by name would repeat every period forever; the
restart loop stops on the fatal class, which is the property every other unit here has.
(2) `Type=oneshot` + `Restart=on-failure`: a clean `sync` (0) would then end the loop.
**CRITIQUE.** The cadence (40 s) is chosen, not derived: it bounds how stale the controller's World
can be when the writer is quiet, and nothing measures what the controller needs. `client` (52) is
restart-class, so a mis-installed workspace retries every 40 s by name instead of stopping;
`absent` (50) is `done`, which under `Restart=always` also runs again (harmless: sync sends no call).
Run only as a parser row (nd exits 52 on a missing socket); the observer's enrolment is an operator
step no row runs here.
**META-CRITIQUE.** I nearly rendered the timer everyone named, because two owners had said
"timer"; the stop-on-fatal property, not the word, picked the shape.
**Status.** landed; run PENDING burst5.

## OPS-14 · the units under systemd: keybroker needs AF_NETLINK; grain-launch depends on its driver (OPS-3, 2026-10-18; burst5 run, HOSTING-7's resident row)

**Decision.** (1) `nd-keybroker.service`'s `RestrictAddressFamilies` gains AF_NETLINK: on burst5
(systemd 255) the decider died at every start because `bwrap --unshare-net` brings the sandbox's
loopback up over NETLINK_ROUTE (run 1, two rows red by name); with it all eight rows pass (run 2:
start under NoNewPrivileges with the decider confined, decider SIGKILL → deciderSignaled 102
restarted, edited anchors refused by ExecStartPre to the start limit, keyFileMode 84 and sockDir 105
stopped, the hosted follower 0660 under `--group`, grain-launch running, controller `store` 109
stopping its launcher). (2) `nd-grain-launch@` Wants=/After= `nd-follow-drive@` as well as the
follower (Launcher.driver): HOSTING-7's resident row measured that the follow Store advances only
while `nd sync` drives it. (3) RUNBOOK §2b makes `worlds/L/members` at install (every plan hides
it) and gives ROOT's observer enrolment order (3e09d67: `--init-hosted`, `init`, the operator's
`enroll` + `grant … observe`, `--seal-observer` last).
**Alternatives.** (1) Drop `RestrictAddressFamilies` on keybroker: the process needs only UNIX, INET
and netlink, so a named list still narrows it. (2) `Requires=` on the driver: a driver restart (every
40 s by design) would stop every grain.
**CRITIQUE.** AF_NETLINK lets keybroker itself open netlink sockets (route, audit…), a widening of
the unit's own filter to make its child's sandbox work; the narrower fix (the decider's sandbox
setup outside the filter) is not a unit setting. A missing `members` directory still ends in
`crashLoop` after `pathMissing`, not a refusal at start (asked of HOSTING-7). The harness runs one
uid: the two-uid branches (`peerRefused`, ConnectOwner, the group crossing) are still the broker
test's. The deployed (system) units were run as user units; `User=`, `RuntimeDirectory=` and the
system sockets' parents are still unrun.
**META-CRITIQUE.** I had predicted the netlink failure for grain-launch (OPS-12: not rendering the
restriction there) and did not apply the same reading to the keybroker unit OPS-2 rendered: I
audited my own new unit and trusted the inherited one.
**Status.** landed.

## OPS-15 · a follow Store is JOINED from a signed invitation, never a reproduced genesis; the hosted follower's join is a hand-run operator verb (OPS-4, 2026-10-18; PROTOCOL-42, CLIENT-26, ROOT-ruled)

**Decision.** (1) RUNBOOK §2: a member's follow Store comes from `nd --join KEY_FILE INVITATION
~/.nd/follow-store /opt/nd/bin/host` into an empty 0700 directory, the invitation from the sponsor's
`nd invite`, the sponsor's `key` (`nd --keys`) over a SECOND channel the joiner already trusts, in a
file under the §2a chain (0644 or 0600, the joiner's). Refusals by name: inviteRefused pinMismatch /
notSponsor / badInvitation (nd 1), the key file's chain (nd 52), `invitation: exists` (nd 52). (2)
RUNBOOK §2b: the hosted follower's Store is `sudo -u nd-hosted /opt/nd/bin/host join STORE INVITATION
KEY_HEX`, run by hand once per World. No join unit and no kept file. (3) §6.7 states the carry
rejoin as trust on first use by design (cv 01a14de7-224a) with its mitigation. (4) store-plants gains
six `join-*`/`follow-*` rows through the real host, using that argv; deploy/live row L joins instead of
reproducing; row P (a follower over a refused join stops `missing`, NRestarts=0) is written and
preflighted outside systemd, not yet run under it.
**Alternatives.** (1) A rendered oneshot `nd-hosted-join@` that the follower Requires=. It would
run `host` bare: nd-supervise is a socket mux and cannot run a one-shot that prints lines.
Ops/Units.lean's own law is that a unit which would run the host unconfined is never rendered
(`ofNode_supervised`). (2) ExecStartPre on the follower: on the second start it would be `exists`.
(3) A confined store-only join in nd (`nd --join-store`, CLIENT): that would be a second join path,
with no custody gain on a box whose operator is the sponsor (ROOT: not taken). (4) Key and
invitation kept as files under the chain: a custody object with no reader. `host join` takes both
as hex arguments, and the only Rust readers that enforce the chain (nd, keybroker) are not on this
path.
**The hosted path's chain rule is the operator's shell, not a Rust reader.** This is acceptable here
for two reasons. The operator is the sponsor, so the key is its own `nd --keys` output and crosses
no channel. The operator also owns the box, and whoever can alter its shell's input can already
write /srv/nd-hosted. A member, whose key DOES cross a channel, gets the Rust-enforced chain through
`nd --join`.
**Plants and teeth (measured, hbox, wt/ops at 46c826e + this change; 66 rows ALL PASS).**
- Signature and sponsor-key checks removed from `Invite.accept` (a building mutation): three rows go
  red by name: `join-forged-invitation-writes-nothing`, `join-other-key-notSponsor-writes-nothing`
  (each exit 0 with files written), and `follow-over-refused-join-is-fatal` (that directory now opens).
- The nonce flipped inside `accept`'s genesis: `join-honest-is-the-writers-world` goes red (another
  origin).
- The `exists` check removed from `Host.Store.genesis`: `join-again-exists` goes red (io 13).
- `follow-opens-the-joined-store` is a positive control. Its tooth is unmeasured.
**CRITIQUE.** The hosted join runs unconfined as nd-hosted. It parses an invitation that the
operator's own nd produced, which is the same exposure `host genesis` had there before. The
founder residual is real: a founder still takes the writer's nonce on its word, and the mitigation
(compare `input HEX` out of band) is a procedure, not a check. Row P has run on no systemd. The test
invitation is built in Lean from published vectors (`Founder.invitation`), not by `nd invite`. Its
fidelity to the deployed signer rests on both using `Invite.unsignedBytes`/`message`. Client's
join.rs covers the nd-signed path.
**META-CRITIQUE.** ROOT's brief named a unit, a theorem and an EXITS.md re-emit. I nearly built them
because they were named, and the module's confinement law refused the shape. I asked before building
rather than after. The phrase "operator data under the StrictModes chain" assumed a reader that the
`host` verb does not have. I checked the verb's argv first, which made that visible.
**Status.** landed (this commit); row P PENDING a box window.


## OPS-16 · the live harness judges only this run's journal: a cursor, planted (OPS-4, 2026-10-18; GATES-5's fail-open finding, ROOT)

**Decision.** deploy/live/journal.sh, sourced by harness.sh and broker.sh: `jr ARGS` =
`journalctl --user ARGS --after-cursor=CUR`. CUR is recorded at the run's start and written to
`report/journal-cursor`. Every journal read a row judges goes through `jr`. `journal_mark` plants
the filter itself before any unit starts: a marker written before CUR must be hidden and one written
after it seen, or the run stops `journal-reads-only-this-run FAIL` (exit 2). Row B now judges the
post-restart feed (one `status=0`, height 5) instead of printing it.
**Alternatives.** (1) The unit's InvocationID: a restart changes it, and rows B, D and E judge
the exit of the invocation BEFORE the restart, so a per-invocation filter hides exactly the line
they need. (2) `--since` the run's start: one-second granularity, so a previous run that ended in
the same second leaks in (broker.sh had this). (3) A fresh unit name per run: that leaves a link
per run in ~/.config/systemd/user.
**CRITIQUE.** The plant proves the cursor filter on a TAG, and the rows read by UNIT. Both go
through the same `jr` and the same `--after-cursor`, but `-u` matching is journald's, not mine.
The tooth swaps the function, not journald. Neither script has run under systemd since the change.
**META-CRITIQUE.** broker.sh's comment recorded that run 2's first draft had read run 1's lines.
OPS-3 fixed that script and did not carry the lesson to harness.sh, OPS-2's. Same pattern as OPS-14:
the new file audited, the inherited one trusted.
**Status.** landed (this commit); systemd re-run PENDING a box window.


## OPS-18 · the owner's audit of the six OPS-path landings made without an OPS lane (OPS-6, 2026-10-20)

**Decision.** e1e8084 (HOSTING-33), cfdb08d (HOST-56), c0cd535 (CLIENT-30), bfdff2d (PERF-10) were read hunk by
hunk against the code each sentence describes (Host/Exit.lean, Hosting/BrokerExit.lean, client/src/mux.rs
`fds_max`, launcher/src/bin/nd-members.rs, keybroker.rs `parse_pins`). The operator sentences were right: 58/59,
the 73 fds (8 + 64 + 1), the decider `hosting-residents /srv/nd/store`. Stale prose that no landing touched is
corrected here:
- `worldTooLarge` (11) said "the HOST-14 design limit"; since HOST-57 no admitted World reaches
  `worldBytesMax`, so it is a defect (its own arm; EXITS.md re-rendered).
- RUNBOOK §2b still said nd-members reads `ND_OPERATOR` (HOSTING-33 removed it), named four roots as five, and had
  no word for the journal names `memberStopping` / `memberStopForced` (CLIENT-30), now there.
- RUNBOOK §2b join and §6 import list `allowancePastBound` 58 / `potentialPastBound` 59 (HOST-56).
- RUNBOOK §8 worst cut carried the numbers from before 16f3b9f and LANG-59 (20.374 / 33.031 / 33.959, three
  shapes); now PERF-10's, with the fourth shape, and the worst-World bench is stated.
**Breaks.** Only EXITS.md row 11 re-renders; no unit file changes.
**CRITIQUE.** The sentences are checked against the code's names and constants, not run: no unit has run under
systemd since 5771c74.
**Status.** landed (this commit).


## OPS-19 · THE PIN: api.anthropic.com's leaf key is shipped in deploy/tls/pins (OPS-6, 2026-10-21; Ember approved B1, ROOT for HOSTING)

**Decision.** `Hosting.Pins.pins` holds `("api.anthropic.com", 9fe3851dbd7a61523c284bb1e372e4e238c5b0aefac4ba256af95c0024045eae)`;
`emit-pins` re-emits `deploy/tls/pins`. This is HOSTING-28's recipe, exactly, and the first outward contact with the
provider: `openssl s_client -connect api.anthropic.com:443 -servername api.anthropic.com </dev/null | openssl x509 -pubkey
-noout | openssl pkey -pubin -outform der | sha256sum`, four fetches (two from hbox, two from another network, a Mac),
all equal. Certificate: subject CN=api.anthropic.com, issuer C=US O=Google Trust Services CN=WE1, notBefore
2026-09-21 18:15:27 GMT, notAfter 2026-12-20 19:15:03 GMT, certificate SHA-256
BF:92:EB:A5:7D:8C:E9:D8:9B:26:B2:74:3A:CC:F9:66:B3:F0:D7:B8:BC:11:85:37:DB:B0:75:4E:14:2A:33:71. No request was
sent and no key was used or touched: the provider KEY is a separate act Ember has not given.
**Alternatives.** Keep the file empty (every call refused: safe, and useless). Not taken: Ember approved the pin.
**CRITIQUE.** A pin taken during an attack pins the attacker, and nothing checks it. The four fetches share what
they can: the same DNS-routed CDN edge may serve one certificate to every vantage point I have, so agreement shows
no per-path forgery, not that the key is the provider's. The leaf expires 2026-12-20 and Let's Encrypt-style renewal
may or may not keep the key; if it changes, every call is refused `pinMismatch` until the operator re-pins
(RUNBOOK §2a). The shipped file is only the default: the installed /etc/nd/keybroker/pins is the operator's.
**Status.** landed (this commit); no provider call has been made.


## OPS-20 · the re-genesis owed for LANG-76's Bell: no deployed World holds the old Bell (CX-OPS, 2026-10-23; Ember approved the re-genesis)

**Decision.** 231af0e (LANG-76, PROTOCOL-68) re-emitted `world/resident/Bell` and owed a re-genesis of any
resident World holding the old Bell (RUNBOOK §1). There is none to re-genesis. The inventory, read on
2026-10-23 at 231af0e:
- hbox: no `/srv/nd`, `/srv/nd-hosted` or `/etc/nd`; `/srv/nd-members` is empty (the tmpfiles directory of
  10-19); no `nd*` system or user unit is loaded; no `resident` exe runs. burst5, where deploy/live ran the
  units as user units, is torn down (OPS-8). The Mac runs no nanodregg process.
- The only resident Worlds are test fixtures. `launcher/tests/resident_bell.rs` makes a fresh World per run
  (`World::genesis_following`, a fresh nonce) and installs `world/resident/Bell` from the tree, so every run
  re-geneses with the Bell of its commit.
So the §1 procedure (stop by PID file, back up, genesis, install, confirm, restart) had no Store to act on, and
nothing was stopped, moved or deleted.

**Measured at 231af0e (hbox wt/ops; logs/ops-regenesis/).**
- The Bell's package id, `nd install` against the real `host serve`, in two fresh plant Worlds of different
  origins (588113f3…, aba69c53…), the same in both (a ROM id is its content digest, `romIdOf`):
  OLD (231af0e^, 35,012 text bytes) `22d6d508b3b05d5bcfd84467b3b339b040ad705aec4c8669962611cb5679bcb1`;
  NEW (231af0e, 45,980 text bytes, `(patience 2048)`) `0b81cfb4b8c126f568d9be15d6b01a814b556ecad0ae46ef84a53925443cce68`.
- The confirm: both installs exit 0 with `tx` and `id`, i.e. committed and confirmed, not `uncertain` (2). The
  new Bell is past the 32,760-byte call that PROTOCOL-68 fixed. A second install of the new Bell is
  `refused idTaken`, and `host check` reads height=2 torn=0.
- The smoke: `cargo test -p nanodregg-launcher --test resident_bell`, 1 passed in 71 s (`smoke.log`).

**Alternatives.** Genesis a standing resident World on hbox now, so that the next Bell change has something to
re-genesis. Not taken: a deployed World is the VM deployment's (RUNBOOK §1a, STAND-INS B1), and a plant World
on hbox would be an object nobody uses.

**CRITIQUE.** The old Bell's id was measured under the new binary: it is the id the old text gets now, not one
read from an old Store, since no old Store exists. The pre-fix `uncertain` for a >32 KB install is
CX-DEADLINE's measurement (RED before PROTOCOL-68), not repeated here. hbox carries 328 leaked test-fixture
processes, 4-5 days old (`nd-supervise`, `host`, `keybroker`, `nd-members` under `~/.cache/nd-t`, from
`nanodregg-gate-3` and `wt/client` runs). They hold throwaway Worlds, not a deployment, and nothing here
stopped them: they have no PID file of this lane's.
**Status.** landed (this commit). Nothing re-emits; nothing refuses to load.
