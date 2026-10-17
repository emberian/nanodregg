# deploy/live — the rendered units under a real service manager (owner: OPS)

`harness.sh SRC ROOT` runs the units `emit-units --live ROOT` renders (the same `Service.ofNode` and
`Service.systemd` as `deploy/units/`, other paths) under a systemd **user** manager, against the
real `host` and `nd-supervise`, and prints one `ROW NAME PASS|FAIL|INFO :: detail` per question.
`feed.py` sends `live-calls` payloads to a unit's client socket. Units are started and stopped by
name; the only process signalled by hand is a unit's host child, found from the unit's MainPID.

## Deploy-time install (not made by the units or the harness)

nd-supervise's Linux mechanism is the fixed path `/usr/local/libexec/nd-bwrap` (sandbox/src/lib.rs
`MECHANISM`; missing is `MechanismMissing`, exit 64, never a fallback). The operator installs it:

    sudo install -D -o root -g root -m 0755 /usr/bin/bwrap /usr/local/libexec/nd-bwrap

- **Restriction ON** (Ubuntu 24.04+ default, `kernel.apparmor_restrict_unprivileged_userns = 1`;
  hbox, Ubuntu 24.10): also install `sandbox/apparmor/nd-bwrap`, granting `userns` to that path alone.
- **Restriction OFF** (burst5-a: Ubuntu 24.04.5, `apparmor_restrict_unprivileged_userns = 0`, no
  `/etc/apparmor.d`, systemd 255): the root-owned copy is enough.

On Linux the sandbox does not filter exec (`EXEC_FILTERED = false`, b487eef): `--exec` bounds what
is visible, not what may run.

## Run 1 — burst5-a, 2026-10-17 10:22Z (main 4ae6608 + fd1d4b2 binaries, built on hbox)

| row | verdict | what happened |
|---|---|---|
| floor-suffices-for-lean-resident | PASS (row printed FAIL: the harness's own grep read `base_height=0` too; fixed) | confined `host serve` active under the rendered unit; 4 × 49 KiB submits answered status 0; `host check` height=4 |
| host-killed-is-restarted | PASS | SIGKILL of the host child: `status=137`, NRestarts 0 → 1, the next submit answered 0 |
| second-writer-locked-is-stopped | PASS | second writer on the same Store: ExecMainStatus=16 (`locked`), NRestarts=0, failed/exit-code |
| crash-loop-hits-start-limit | PASS (row printed FAIL: systemd 255 reports `Result=exit-code`, the journal says `Start request repeated too quickly`; the row now reads the journal) | 5 restarts, then refused |
| store-sound-after-the-kills | INFO | `host check`: height=5, torn=0 |
| append-failure-is-uncertain-restarted | **FAIL** | `LimitFSIZE` just above the segment: the host dies by SIGXFSZ, the unit sees `status=153`, not 3; restarted (153 is in no prevent list) |
| follower-unit | INFO | exit 64: nd-supervise refuses a `--write` path that does not exist (the follow Store directory); the harness now makes it, RUNBOOK §2 says the operator does |

## Runs 2 and 3 — burst5-a, 2026-10-17 (main 46a1189: nd-supervise with c6e4abf, host with HOST-25)

All rows PASS but one. host-killed-is-restarted: `status=66` (childSignaled, CLIENT's c6e4abf), was
137. crash-loop-hits-start-limit: PASS on the journal. append-failure-is-uncertain-restarted: still
FAIL, now `status=66` (SIGXFSZ, named), restarted; exit 3 waits on HOST-6's SIG_IGN. Run 2's
follower exited 13 (`io`: a follow Store is a reproduced genesis, not a directory); run 3 reproduces
the writer's genesis with its nonce and follower-unit-starts PASSES (confined `STATUS follow
height=0`, the writer's genesis chain).

## Run 4 — burst5-a, 2026-10-17 (main 645116a: host with HOST-27's SIGXFSZ ignore) — ALL PASS

append-failure-is-uncertain-restarted PASSES: `LimitFSIZE` = the fresh segment + 4096 bytes, so the
first 49 KiB submit's frame crosses it mid-frame; the write fails EFBIG, the client's reply is
status 2 (`uncertain`), the unit exits `status=3` and is restarted, and the restarted writer opens
at height 0 (the torn tail dropped). Every other row PASS as in run 3.

Findings, routed:
- **No signal death is named on Linux** (CLIENT): nd-supervise's direct child is bwrap, which turns
  the host's signal death into a normal exit 128+N (137 for SIGKILL, 153 for SIGXFSZ), so
  `childSignaled` (66) was unreachable and the unit restarted on a code no table names. FIXED by
  CLIENT-2 at c6e4abf (`killed_by_signal`: on Linux a mechanism exit ≥ 128 is a signal death, so
  nd-supervise exits 66); run 2 re-measures. Consequence: under the Linux sandbox a child's own
  codes are readable only below 128 (the Host's are below 64).
- **An append past RLIMIT_FSIZE kills `host` instead of answering `uncertain`** (HOST): SIGXFSZ is
  not ignored. The Store stays sound (a torn tail, opened clean). HOST-6 told. Exit 3 restarted is
  therefore NOT yet shown on any box; this row is its plant.

## Rendered argv through the real programs (OPS-3, 2026-10-18)

`unit-argv.py UNIT DIR WORD=VALUE...` runs a rendered unit's ExecStart (with its `Environment=`) with
each rendered path, `%i` and `${VAR}` replaced by a scratch value (an unmapped one, or a value nothing asks for, fails
before anything runs). On hbox at 8be4026:
- `nd-grain-launch@.service`: grain-launch parses ROOT BROKER LABEL PIDS CONTROLLER, starts the
  confined hosting-controller, which parses `STORE LABEL` and, over an empty store directory, ends
  `store` (109, `hosting-controller: store badKey`); grain-launch passes 109 through
  (`controllerEnded 109`): a fatal class, so the unit stops.
- `nd-hosted-follow@.service`: under hbox's group-writable `/tank`, nd-supervise exits 64
  `sharedDirRefused: Dir(...)`: the rendered `--group ${ND_GID}` sits where its grammar takes it and
  the shared-dir check refuses a chain another can write, by name. The positive run (a passing
  chain, the follower serving, an nd-group peer connecting) needs burst5's `/srv/scratch`: PENDING.
- `nd-follow-drive@.service` (cfb789b): over a fresh `nd --init-observer` workspace and no
  follower socket, `nd sync` exits 52 (`client`, `nd: follow.sock: No such file or directory`).

## The keybroker unit (OPS-3): `broker.sh SRC ROOT`

`emit-units --live ROOT DIR` also renders `nd-ops-live-keybroker.service` from `Ops.Units.liveBroker`:
the deployed keybroker render as a user unit (no `User=`, no RuntimeDirectory, PIDS under ROOT),
upstream an unreachable local port. Rows: keybroker-unit-starts (ExecStartPre passes on the pinned
anchors; the resident socket 0660 in its 02710 directory; the decider running confined under
NoNewPrivileges=yes), decider-killed-is-restarted (SIGKILL by keybroker's own PID file →
deciderSignaled, restarted), anchors-edited-refused-at-start (one byte → ExecStartPre refuses every
start, start limit, no socket), key-mode-0644-stops (keyFileMode, NRestarts=0), sockdir-mode-stops
(SOCKDIR 0755 → sockDir, no socket). Codes are read from EXITS.md by name. ROOT's chain must pass
StrictModes (the script sets umask 022 and ROOT 0755: hbox's umask 002 made a first preflight end
`keyFileDir`). Preflight outside systemd on hbox (`~/.cache/nd-t`, the broker test's scratch):
keybroker binds `broker/01/broker.sock` 0660, writes `pids/decider.pid`, and runs until stopped.
The same script then runs the hosted pair, rendered as user-unit templates by `Ops.Units.liveHostedFollower`
/ `liveLauncher` (instance `w`): hosted-follower-starts (the World's genesis reproduced into
`hosted/worlds/w/store`, socket 0660 of the shared directory's group under `--group`),
grain-launch-starts (active 10 s later, NRestarts 0: the confined controller tails the follow
Store), controller-store-refusal-stops (instance `x` over an empty store directory: the
controller's `store` passed through, the unit stopped). Codes come from EXITS.md by table and name.
Run under systemd: PENDING (burst5, INTEGRATOR-6's window).
