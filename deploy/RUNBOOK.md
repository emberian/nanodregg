# deploy/RUNBOOK.md — running a nanodregg Store (owner: OPS)

Every command below is marked **RAN** (run by OPS against the real `host` exe, with the commit) or
**PENDING (owner)**. Exit codes are `Host.Status` (Host/Exit.lean); `host` prints `refused NAME` or
`exit NAME` on stderr; the full table with what systemd does and what the operator does is
`deploy/units/EXITS.md` (generated). Never run genesis with the RFC 8032 test founder (Ops.Founder) outside a
plant directory: its secret is published, so anyone can write that World.

## 1. Genesis — RAN (store-plants, at the KERNEL-24 flag day 9e91ede)

    host genesis STORE LABEL [--nonce HEX32] KEY_HEX NEXT_HEX [KEY_HEX NEXT_HEX]...

Creates the Store's files (`deploy/units/STORE.md`, generated from `Host.Store.layout`); prints `origin …`, `nonce …`, `founder i member … grant …` and `chain …`.
Refuses `exists` (17) if any Store file is there. KEY is the founder's Ed25519 public key; NEXT
its precommitted next key. Omit `--nonce`: `host genesis` draws 32 bytes from the OS. Record the
printed `origin` and `nonce` with the Store's backup.

The World is its ORIGIN (KERNEL-24): a hash of the label, the nonce, the allowance and every
founder's key and next-key digest. Founder ids are keyed by it and every call signs it; a call
signed for another World is refused `wrongWorld` before its key or signature is read. So:
- **A LABEL may be reused for a re-genesis**, with a fresh nonce (the default): the new World
  shares no member id with the old, and no old call lands in it. Planted:
  `replay-other-nonce-not-admitted` (OPS-2's replay: founder 0's call served to a second genesis
  of the same label and founders under another nonce does not land).
- **Same label, same nonce, same founders is the SAME World** by design: that is what a restore
  rebuilds, and every call of the old one lands in it (`replay-same-nonce-admitted-control`).
  Never pass an old `--nonce` to a genesis meant to be a new World.

## 2. Start — PENDING (OPS: deploy/live on burst5)

Writer's node (systemd system unit, `deploy/units/linux/nd-host-serve.service`, emitted by
`emit-units deploy/units` from Host.Status and Protocol.SupervisorExit; `gates/generated.tsv`
refuses a unit file that differs from the tables):

    nd-supervise /run/nd/host.sock --write /srv/nd/store --exec /opt/nd/bin/host --hide /srv/nd/ws --hide /home -- /opt/nd/bin/host serve /srv/nd/store

Member machine (user unit `nd-host-follow.service`; `%h/.nd/nd-host-follow.env` holds
`ND_MEMBER=<hex>` and `ND_GRANT=<hex>` from genesis/enrol):

    nd-supervise %h/.nd/ws/follow.sock --write %h/.nd/follow-store --exec /opt/nd/bin/host --hide %h/.nd/ws --hide %h/.nd/holding -- /opt/nd/bin/host follow %h/.nd/follow-store ${ND_MEMBER} ${ND_GRANT}

Before the first start the member makes the hidden directories, `mkdir -m 0700 ~/.nd ~/.nd/ws
~/.nd/holding` (the writer's node likewise `/srv/nd/ws`), and its follow Store, which is the
writer's genesis REPRODUCED with the writer's nonce: `host genesis ~/.nd/follow-store LABEL --nonce
NONCE KEY_HEX NEXT_HEX…` with the label, nonce and founders the writer's genesis printed (KERNEL-24:
same label, nonce and founders = the same World; its printed `chain` must equal the writer's).
nd-supervise refuses a `--write` or `--hide` path that does not exist (64), and `host follow` on a
directory with no Store is `io` (13); both stop the unit (measured on burst5, deploy/live/README.md).
A host killed by a signal is nd-supervise's 66 childSignaled, restarted (on Linux bwrap reports it
as 128+N; CLIENT's c6e4abf maps that to 66).

systemd restarts every failure except the fatal codes of both tables (`RestartPreventExitStatus`:
the Host's fatal class and nd-supervise's 64 refusedAtLaunch and 65 childUnroutable); a fatal
refusal stops the unit and its name is in the journal. A restart-class exit that repeats more
than `StartLimitBurst` times inside `StartLimitIntervalSec` fails the unit (a crash on every
start does not loop forever); `systemctl reset-failed UNIT` after the cause is fixed. macOS
(launchd) restarts every non-zero exit every `ThrottleInterval` seconds: a fatal refusal repeats
by name, truncating nothing.

## 3. Status — RAN

    host check STORE
    STATUS height=H chain=C base_offset=O base_height=B seg_bytes=S records=R torn=T anchor=none

Read-only (no lock, writes nothing; works while the writer runs or is down). `torn>0` is the
writer's unsynced last frame. `anchor=none` means: integrity and height only, NOT completeness.

## 4. Backup — RAN (stopped and LIVE: store-plants)

Copy the files in the order `deploy/units/STORE.md` lists (generated from
`Host.Store.backupOrder`; the base before every append-only file), each whole. It is safe while
the writer runs, across a seal: a seal installs a new `base.world` atomically and the append-only
files only grow, so each one copied after `base.world` holds the prefix the copied base names.
Planted in store-plants: `live-copy-raced-a-seal` / `live-copy-anchor-at-segment-copy` (the right
order across a seal opens at the writer's height); `orphan-index-page-*` (an index page past the
stale base's prefix: a reader ignores it, the writer's open truncates it and reopens at the same
height). The OTHER orders are refused by name: `seg.log` copied before a seal is `segmentShort`
(`copy-segment-before-base-wrong-order`), `index.log` copied before a seal is `indexShort`
(`copy-index-before-base-wrong-order`); neither opens short. Record an anchor at the
same time: `HEIGHT:CHAIN` from a member follower's head (its own `host check` on its follow
Store) or the highest receipt a client holds. The key travels with the copy (HOST-16: it guards
integrity, not secrecy; a copy without it is `baseCorrupt`).

## 5. Restore — RAN (store-plants; a sealed Store too: `sealed-*`)

Copy the files (`deploy/units/STORE.md`) into an empty STORE, then:

    host check STORE --anchor HEIGHT:CHAIN

0 and `anchor=ok` = the copy reaches the anchor with the anchor's chain. Without an anchor, a copy
cut at a frame boundary, a single foreign last frame and a rollback to an older complete copy ALL
open cleanly at a lower height; that is why the anchor is not optional.

## 6. Re-genesis (flag day) — PENDING (OPS-1 export/import: KERNEL-29, CODEC's carried codec, HOST-28)

1. Stop the writer unit and every member's follow unit (by unit name). An export is taken from a
   STOPPED writer only (HOST-28): the carried state is the writer's last durable World.
2. The operator moves the old Store aside BY HAND (`mv STORE STORE.old-<date>`); nothing deletes it.
3. `host genesis STORE NEW-LABEL …` (a new label: §1).
4. State carry (law 1, OPS-1) is export = the old Store's fold, import = genesis whose World is
   those cells re-sealed, check = canonical bytes equal up to the epoch header. No verb exists yet.
   Without it, a flag day starts from an empty World. Old receipts and signed calls are never valid
   in the new World.

## 7. Refusals and what the operator does

`deploy/units/EXITS.md`: every code of `host` and of nd-supervise, its class, what the rendered
unit does with it and what the operator does, generated from Host/Exit.lean, Protocol/Exit.lean
and the exhaustive `Ops.Units.hostAction` / `supervisorAction` (a new status without an operator
action does not build). No hand copy of it lives here.
