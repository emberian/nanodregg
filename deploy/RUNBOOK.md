# deploy/RUNBOOK.md — running a nanodregg Store (owner: OPS)

Every command below is marked **RAN** (run by OPS against the real `host` exe, with the commit) or
**PENDING (owner)**. Exit codes are `Host.Status` (Host/Exit.lean); `host` prints `refused NAME` or
`exit NAME` on stderr; the full table with what systemd does and what the operator does is
`deploy/units/EXITS.md` (generated). Never run genesis with the RFC 8032 test founder (Ops.Founder) outside a
plant directory: its secret is published, so anyone can write that World.

## 1. Genesis — RAN (28de15e)

    host genesis STORE LABEL KEY_HEX NEXT_HEX [KEY_HEX NEXT_HEX]...

Creates `STORE/key` (32 random bytes, 0600), `STORE/seg.log` (the origin frame) and
`STORE/base.world`; prints `founder i member … grant …` and `chain …`. Refuses `exists` (17) if
any Store file is there. KEY is the founder's Ed25519 public key; NEXT its precommitted next key.
- **Cross-World replay (OPS-2), OPEN.** Today two genesis runs with the same LABEL and founders
  make identical founder ids and chains, and every call signed for one admits in the other
  (reproduced: `~/dev/redregg/work/ops/replay-20261016/`). The fix is DECIDED, not built:
  KERNEL-24 (decisions/kernel.md, 9d2e5df) gives `World.genesis` a separate 32-byte nonce that
  `host genesis` draws from the OS, an `origin` committing to name, nonce, allowance and every
  founder's key and next-key digest, founder ids keyed by the origin, and a signed
  `Unsigned.world` refused `wrongWorld` before anything else. Checked at 7797070: no `origin`,
  no nonce, no `wrongWorld` refusal in Kernel/ or Host/ (the PROTOCOL row `wrongWorld` is
  blockedOn KERNEL). Until it lands, NEVER reuse a LABEL for a re-genesis: use
  `LABEL-<date>-<random>`. When it lands this note is deleted, not amended: a re-genesis under
  the same label is then a different World, and the bound is the nonce, not the label.

## 2. Start — PENDING (OPS: deploy/live on burst5)

Writer's node (systemd system unit, `deploy/units/linux/nd-host-serve.service`, emitted by
`emit-units deploy/units` from Host.Status and Protocol.SupervisorExit; `gates/generated.tsv`
refuses a unit file that differs from the tables):

    nd-supervise /run/nd/host.sock --write /srv/nd/store --hide /srv/nd/ws --hide /home -- /opt/nd/bin/host serve /srv/nd/store

Member machine (user unit `nd-host-follow.service`; `%h/.nd/nd-host-follow.env` holds
`ND_MEMBER=<hex>` and `ND_GRANT=<hex>` from genesis/enrol):

    nd-supervise %h/.nd/ws/follow.sock --write %h/.nd/follow-store --hide %h/.nd/ws --hide %h/.nd/holding -- /opt/nd/bin/host follow %h/.nd/follow-store ${ND_MEMBER} ${ND_GRANT}

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

## 4. Backup — RAN (on a stopped Store; live copy PENDING plant)

Copy, in this order: `STORE/key`, `STORE/base.world`, `STORE/seg.log`. Record an anchor at the
same time: `HEIGHT:CHAIN` from a member follower's head (its own `host check` on its follow
Store) or the highest receipt a client holds. The key travels with the copy (HOST-16: it guards
integrity, not secrecy; a copy without it is `baseCorrupt`).

## 5. Restore — RAN (store-plants, 16 plants)

Copy the three files into an empty STORE, then:

    host check STORE --anchor HEIGHT:CHAIN

0 and `anchor=ok` = the copy reaches the anchor with the anchor's chain. Without an anchor, a copy
cut at a frame boundary, a single foreign last frame and a rollback to an older complete copy ALL
open cleanly at a lower height; that is why the anchor is not optional.

## 6. Re-genesis (flag day) — PENDING (OPS-1 export/import: HOST/KERNEL)

1. Stop the writer unit and every member's follow unit (by unit name).
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
