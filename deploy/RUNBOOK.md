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

## 2. Start — RAN as user units (deploy/live on burst5: host units OPS-2 runs 1–4; keybroker, hosted follower, grain-launch OPS-3 run 2)

Writer's node (systemd system unit, `deploy/units/linux/nd-host-serve.service`, emitted by
`emit-units deploy/units` from Host.Status and Protocol.SupervisorExit; `gates/generated.tsv`
refuses a unit file that differs from the tables):

    nd-supervise /run/nd/host.sock --write /srv/nd/store --exec /opt/nd/bin/host --hide /srv/nd/ws --hide /home -- /opt/nd/bin/host serve /srv/nd/store

Member machine (user unit `nd-host-follow.service`; `%h/.nd/nd-host-follow.env` holds
`ND_MEMBER=<hex>` and `ND_GRANT=<hex>`: a founder's from genesis, a joiner's from its enrolment below):

    nd-supervise %h/.nd/ws/follow.sock --write %h/.nd/follow-store --exec /opt/nd/bin/host --hide %h/.nd/ws --hide %h/.nd/holding -- /opt/nd/bin/host follow %h/.nd/follow-store ${ND_MEMBER} ${ND_GRANT}

The writer's unit has `RuntimeDirectory=nd`: systemd makes `/run/nd` (owner nd) before every start
and removes it at stop, and nd-supervise binds `/run/nd/host.sock` (0600, nd only) in it afresh.
Without it nothing makes `/run/nd` on a fresh box and nd-supervise cannot bind its socket (not yet run under systemd: PENDING with §2).
Before the first start the member makes the hidden directories and an EMPTY follow Store directory,
`mkdir -m 0700 ~/.nd ~/.nd/ws ~/.nd/holding ~/.nd/follow-store` (the writer's node likewise
`/srv/nd/ws`), its custody (`ND_WORKSPACE=~/.nd/ws ND_HOLDING=~/.nd/holding nd --init`), and then its
follow Store FROM AN INVITATION its sponsor signed (PROTOCOL-42, CLIENT-26; `nd` below always runs
with `ND_WORKSPACE`/`ND_HOLDING` set as here). The World is derived from inputs the sponsor signed,
never from bytes the Host or anyone else hands over:

1. The sponsor (any member; the operator's own member for the first joiners) prints the invitation
   with `nd invite` (bare: it reads the World's genesis inputs the sponsor kept; a FOUNDER keeps them
   once with `nd --input HEX`, the `input HEX` line its genesis printed last) and its public key with
   `nd --keys` (the `key HEX` line). The invitation PINS the writer's newest base, as the sponsor's
   OWN follow verified it (PROTOCOL-47, 5f9edc2): the step count the writer states for it and the
   digest of follow's own World there, never the writer's word and never the sponsor's tip. A thin
   joiner adopts exactly that base, so before inviting one the operator SEALS the writer (HOST-43):

       systemctl stop nd-host-serve
       sudo -u nd /opt/nd/bin/host seal /srv/nd/store      # prints `sealed steps=S chain=C digest=D`
       systemctl start nd-host-serve

   and then the sponsor runs `nd invite` (it catches up first, crossing the sealed base). `host seal`
   is the operator's alone: no member operation seals. On a running writer it is refused `locked`
   (16) and writes nothing; at an already-sealed position it writes nothing and prints the same line
   again. The base stays the newest until the writer's next cadence seal (1 MiB of log), so later
   commits do not spoil an invitation already made. The sponsor's refusals (nd exit 1, the name on
   stderr, a hint on stdout):
   - `refused noBase`: the sponsor's follow has not verified the writer's newest base (follow was
     restarted since, the record is in its memory; or the writer sealed and follow has not crossed
     it). Seal as above, then `nd invite` again.
   - `refused baseMismatch`: the writer states a base digest that is not the sponsor's own World at
     that step count. Do NOT invite through this writer: it states a base it does not hold (a lying
     or forged base); stop and investigate it (`host check` on the writer's Store, §3).
   `host seal` refuses by the names of `host serve` (the Store it cannot open; deploy/units/EXITS.md)
   and `locked`; one more is its own, `positionUnfit` (56, fatal): the segment position is past
   u64, which a base cannot spell; nothing was written, keep the Store untouched and report to HOST.
   The joiner checks the pin: `nd adopt` prints `adopted STEPS DIGEST`, which must equal the `steps=`
   and `digest=` of the operator's `sealed` line.
   Planted: store-plants `seal-live-writer-locked`, `seal-base-is-the-pin`, `seal-again-idempotent`;
   PROTOCOL's rows `seal`, `basePin`; client/tests/join.rs (a thin joiner adopts exactly the sealed
   `steps=` and `digest=`).
2. The two reach the joiner by TWO channels. The invitation may travel any way: it is checked. The
   KEY is the trust root: it comes over a channel the joiner already trusts (in person, a message the
   joiner can attribute), never from the Host, never in the same message as the invitation.
3. The joiner writes the key's hex (one line) to `~/.nd/sponsor.pub`, owned by the joiner, mode 0644
   (or 0600): no group or other write, every directory up to `/` passing §2a's chain rule.
4. `nd --join ~/.nd/sponsor.pub INVITATION ~/.nd/follow-store /opt/nd/bin/host` — nd reads the key file
   under the chain rule and runs `host join` confined (the follower's own policy); Lean accepts the
   invitation under the key and only then writes the Store (`join_genesis_iff`). It prints the
   genesis lines, `sponsor HEX`, `input HEX` and the joiner's `join HEX`, and keeps the invitation and
   the inputs in the workspace (0600; the joiner can now `nd invite` others itself).
5. The sponsor enrols it: `nd enroll JOIN_HEX` → `id MEMBER`; `nd grant world MEMBER observe --via
   GRANT` → `id GRANT`. Those two are the joiner's `ND_MEMBER` / `ND_GRANT` in the env file above.

Refused, each writing nothing (the Store directory stays empty, the workspace keeps nothing),
planted against the real host (`client/tests/join.rs` through nd; store-plants `join-*` with the
argv §2b runs): `refused inviteRefused pinMismatch` (nd exit 1: a byte changed after the sponsor
signed, a forged nonce among them); `refused inviteRefused notSponsor` (exit 1: signed by another key
than the one in the file); `refused inviteRefused badInvitation` (exit 1: not an invitation); a key
file failing the chain, `key file: Dir(PATH)` / `Mode(M)` / `Owner(UID)` (nd exit 52); `invitation:
exists` (exit 52, before host runs: this workspace has joined). A refusal by name means: get a fresh
invitation and check the key's channel, not retry.

The residual (stated, not closed): a FOUNDER's own follow Store is still the writer's genesis
REPRODUCED, `host genesis ~/.nd/follow-store LABEL --nonce NONCE KEY_HEX NEXT_HEX…` with the label,
nonce and founders the writer's genesis printed (KERNEL-24: same inputs = same World). The founder's
keys are its own, but the NONCE is taken on the word of whoever ran the writer's genesis: trust on
first use, narrower than before (one 32-byte value, not a whole World) and not zero. Mitigation:
every founder compares the `input HEX` (or `origin HEX`) its own genesis printed with the one the
writer's genesis printed, out of band and with another founder, before it keeps it with `nd --input`.
Test fixtures that reproduce a genesis with a known nonce do so by construction (harmless).
The log reply's shape changed at PROTOCOL-47 (it states the newest base): a follower and a writer
built on opposite sides of it refuse every log page `badResult`, so upgrade the writer and every
follower together.
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

### 2a. Custody paths (CLIENT-19, eb0ec6a)

Every custody read (a member's key and holding directory, the keybroker's provider key file and
its TLS anchors) checks, before it opens the file, that EVERY directory from the file up to `/` is
owned by the reading user or root and has no group or other write bit, as sshd's StrictModes does.
A sticky world-writable directory (`/tmp`) fails too. Refused by name: `Dir(PATH)`, naming the
first directory that fails (the keybroker reports it as `keyFileDir`). The file itself must be
owned by the reading user (`Owner(UID)` otherwise; a root-owned system CA bundle is refused):
- a private file (a key) at mode 0600 exactly (`Mode(M)` otherwise);
- a public custody file (the anchors) with no group/other write and no set-id bit (0644 passes).
So never place these files under a group-writable tree: on hbox the umask-002 `/tank` tree and
`/tmp` both fail.

The node's two system users (HOSTING-17 §1), from `deploy/units/linux/sysusers/nd.conf`
(generated): `nd` runs `host serve` and keybroker (and its decider); `nd-hosted` runs grain-launch,
the controller and every grain. Each has its own primary group and neither is in the other's, so a
sandbox escape is the hosted uid: it reads no provider key and writes no Store. Then SOCKDIR,
from `deploy/units/linux/tmpfiles/nd-broker.conf` (generated; `d /run/nd-broker 2710 nd nd-hosted -`:
nd writes, the hosted group only traverses, the setgid bit gives every inode inside the group
nd-hosted). It is NOT a RuntimeDirectory: it outlives the unit, so a restarted keybroker is
reachable inside running sandboxes (HOSTING-17 §4). Users first, then tmpfiles (measured on hbox,
systemd 256: the tmpfiles line fails `Failed to resolve user 'nd'` until the users exist):

    sudo install -m 0644 deploy/units/linux/sysusers/nd.conf /etc/sysusers.d/nd.conf
    sudo systemd-sysusers
    sudo install -m 0644 deploy/units/linux/tmpfiles/nd-broker.conf /etc/tmpfiles.d/nd-broker.conf
    sudo systemd-tmpfiles --create /etc/tmpfiles.d/nd-broker.conf
    sudo install -m 0644 deploy/units/linux/tmpfiles/nd-member.conf /etc/tmpfiles.d/nd-member.conf
    sudo systemd-tmpfiles --create /etc/tmpfiles.d/nd-member.conf

The second pair makes the MEMBER root `/run/nd-member` (`d /run/nd-member 2710 nd nd-hosted -`, the same
shape, HOSTING-20/25): a resident's member socket `/run/nd-member/<dirOf id>/nd.sock` is served as
nd and reached by the hosted group. It must be disjoint from `/srv/nd-hosted` and `/run/nd-broker`
(grain-launch refuses nesting: `rootsOverlap`, 117).

The render refuses a hosted user equal to the key holder (`hostedIsKeyHolder`,
`Ops.Units.Broker.check_hosted_ne_user`): keybroker cannot tell that misconfiguration from the
one-uid test, so the install refuses it. The keybroker's custody layout, which passes by
construction:

    sudo install -d -o root -g root -m 0755 /etc/nd
    sudo install -d -o nd -g nd -m 0700 /etc/nd/keybroker
    sudo install -o nd -g nd -m 0644 deploy/tls/anchors.pem /etc/nd/keybroker/anchors.pem
    sudo install -o nd -g nd -m 0600 PROVIDER_KEY_FILE /etc/nd/keybroker/provider.key

A member's own files live under its home (`~/.nd`, 0700, made by `nd --init`); its home and every
parent must also pass (a group-writable home is refused `Dir(/home/USER)`). The keybroker unit is
rendered by emit-units as `deploy/units/linux/nd-keybroker.service` (system unit, User=nd):
- install `keybroker`, `hosting-broker` and `emit-anchors` in `/opt/nd/bin`; write
  `/etc/nd/keybroker/keybroker.env` (owned by root or nd, not group/other writable) with
  `ND_OPERATOR=<operator member hex>` and
  `ND_PEER=<the uid of nd-hosted>` (`id -u nd-hosted`: the one uid keybroker serves, HOSTING-17 §3);
- every start first runs `emit-anchors --check /etc/nd/keybroker/anchors.pem`: an installed copy
  that differs from the build's pinned roots by one byte refuses to start (and, failing on every
  start, stops at the start limit; the journal names it);
- there is no operator list of residents (HOSTING-26, ruled (A)): keybroker asks its decider which
  resident grains the World holds, every 200 ms, so a resident's socket appears when its grain is born
  and goes, with its directory, when the grain is removed, with no restart and no operator step. A
  World with more than 1024 resident grains stops the unit `residentsPastBound` (decider 7, EXITS.md);
  an ask on a socket whose resident was since removed is refused `notResident`. A resident started
  before keybroker has learned its birth is refused `pathMissing` and counted; keybroker's next poll
  binds the socket;
- resident `r`'s socket (`r` is the grain's directory, its id in lowercase hex) is
  `/run/nd-broker/<r>/broker.sock`: keybroker makes `<r>` (02710, the
  hosted group by setgid) and binds the socket 0660 nd:nd-hosted; on every accept it serves only a
  peer of uid ND_PEER and SOCKDIR's group, anything else is refused `peerRefused` on the wire. A
  SOCKDIR of any other owner, group or mode, or a directory above it writable by another, ends
  keybroker `sockDir` (105, the unit stops). `/run/nd-keybroker` (RuntimeDirectory) holds only the
  decider's PID file;
- keybroker's and the decider's ends are `deploy/units/EXITS.md`'s two broker tables (HOSTING-16):
  every custody refusal stops the unit, a signalled or lagging decider restarts.
- RAN under systemd 255 (burst5, the rendered unit as a user unit, `deploy/live/broker.sh` run 2, all
  PASS): it starts under NoNewPrivileges=yes with the decider confined by nd-bwrap; a SIGKILLed
  decider ends keybroker `deciderSignaled` (102) and the unit restarts; a one-byte edit of the
  installed anchors makes ExecStartPre refuse every start until the start limit (keybroker never
  runs); key mode 0644 stops it `keyFileMode` (84), SOCKDIR 0755 stops it `sockDir` (105), each with
  no restart. Run 1 found that `RestrictAddressFamilies` without AF_NETLINK kills the decider at
  every start (bwrap brings the sandbox's loopback up over NETLINK_ROUTE); the unit now allows it.

### 2b. The hosted follower (HOSTING-17 §7, ROOT's ruling) — follower and launcher RAN as user units (burst5, OPS-3 run 2); the driver PENDING

The controller never reads the writer's files: it tails its OWN follow Store, written by `host follow`
running as `nd-hosted`, one per hosted World, from the template
`deploy/units/linux/nd-hosted-follow@.service` (instance = the World's label `L`):

    nd-supervise /run/nd-follow/L.sock --write /srv/nd-hosted/worlds/L/store --exec /opt/nd/bin/host --group ${ND_GID} --hide /etc/nd --hide /home -- /opt/nd/bin/host follow /srv/nd-hosted/worlds/L/store ${ND_MEMBER} ${ND_GRANT}

The direction rule: the TRUSTED side initiates. `host.sock` stays nd-only (0600); the follower's
socket is shared with group `nd` (0660, `--group`, CLIENT-21) in `/run/nd-follow`, from
`deploy/units/linux/tmpfiles/nd-follow.conf` (generated; `d /run/nd-follow 2710 nd-hosted nd -`:
the setgid bit gives the socket group nd without nd-hosted joining it). nd-supervise refuses at
launch (64) a socket directory not owned by the unit's user, not mode exactly 02710, under a parent
another can write (`sharedDirRefused: Dir(PATH)`), or of another group (`groupMismatch`). Planted
with the rendered argv (each rendered word replaced by a scratch path, `deploy/live`): under hbox's
group-writable `/tank` it is refused `sharedDirRefused: Dir(...)`, as it must be (`deploy/live/unit-argv.py`).

Install, per World `L` (after §2a's users):

    sudo install -m 0644 deploy/units/linux/tmpfiles/nd-follow.conf /etc/tmpfiles.d/nd-follow.conf
    sudo systemd-tmpfiles --create /etc/tmpfiles.d/nd-follow.conf
    sudo install -d -o nd-hosted -g nd-hosted -m 0700 /srv/nd-hosted /srv/nd-hosted/worlds /srv/nd-hosted/worlds/L /srv/nd-hosted/worlds/L/members /srv/nd-hosted/worlds/L/store
    sudo -u nd-hosted /opt/nd/bin/host join /srv/nd-hosted/worlds/L/store INVITATION KEY_HEX

The follower's Store is JOINED from the operator's invitation (PROTOCOL-42), never a reproduced
genesis: INVITATION is the `invite HEX` the operator's own member prints (`nd invite`, §2 step 1)
and KEY_HEX that member's own `key HEX` (`nd --keys`). Here the sponsor IS the operator and the box
is the operator's, so the key crosses no channel and nothing is kept on the box: `host join` takes
both as arguments, the operator's shell is the only reader, and to re-make the Store (moved aside
after a `store` refusal, §5) the operator runs the same line with a fresh `nd invite`. It prints the
genesis lines, then `sponsor HEX` (the operator's member id: OPERATOR_MEMBER in the observer's
`nd init` below) and `input HEX`. A forged invitation is `refused inviteRefused pinMismatch` (44), a
key other than the signer's `refused inviteRefused notSponsor` (44), both writing nothing; a join
into a Store that exists is `refused exists` (17). If the follower unit is started over the empty
directory a refused join left, `host follow` ends `missing` (20, fatal: the unit stops by name and
is not restarted; it never follows a World nobody accepted). Planted through the real host with
this argv (store-plants `join-forged-invitation-writes-nothing`, `join-other-key-notSponsor-writes-nothing`,
`join-honest-is-the-writers-world`, `join-again-exists`, `follow-over-refused-join-is-fatal`,
`follow-opens-the-joined-store`; under systemd, deploy/live/broker.sh row P: PENDING a box window).

Then `/etc/nd/hosted/L.env` (root-owned 0644) with `ND_MEMBER`/`ND_GRANT` of the follower's own
OBSERVE-ONLY member (the operator's member enrols it, then `grant world MEMBER observe --via GRANT`:
PENDING, PROTOCOL-7) and `ND_GID=$(getent group nd | cut -d: -f3)`. `grain-launch` reads
`ROOT/worlds/L/store` with ROOT `/srv/nd-hosted`, so the follower writes exactly there.

The LAUNCHER, per World `L`, from `deploy/units/linux/nd-grain-launch@.service` (as nd-hosted;
after the follower, `Wants=`/`After=`; PID files in its RuntimeDirectory `/run/nd-grain-launch/L`):

    grain-launch /srv/nd-hosted /run/nd-broker /run/nd-member L /run/nd-grain-launch/L /opt/nd/bin/hosting-controller /srv/nd-hosted/worlds/L/store L

The MEMBER socket, per resident grain (HOSTING-20/25), from `deploy/units/linux/nd-member@.service`
(as nd; the instance is the grain's directory, its id in lowercase hex). nd-supervise serves
`/run/nd-member/%i/nd.sock` (0660, group nd-hosted, only the hosted uid admitted: `--group` /
`--peer`) and runs `nd --stdio` over the resident's own member workspace, the only path it writes;
the operator's workspace (`/etc/nd`) and `/home` are hidden. The unit makes `/run/nd-member/%i` 02710
first (nd-supervise makes no directory). Its environment file `/etc/nd/hosted/member-%i.env` (owner
nd, 0600) holds the box's own values: `ND_GID`, `ND_PEER` (the nd-hosted gid and uid, as for
keybroker), `ND_MEMBER_WS` (`/srv/nd-hosted/worlds/L/members/%i`), `ND_FOLLOW_SOCK` (that member's own
follower socket, from `host follow` as that member) and `ND_HOST_SOCK` (`/run/nd/host.sock`). The child
connects to exactly the last two, and a confined connector sees its socket's WHOLE parent directory
(CLIENT-20): each of the two sockets must sit alone in its directory, never in a workspace that holds
keys. `/run/nd` holds only `host.sock`; give the member's follower socket a directory of its own. The
unit must be up before the grain starts: a launch whose member socket is missing is refused
`pathMissing` and then crash-loops. How the unit learns of a grain's birth is HOSTING's open item;
until it settles, the operator starts `nd-member@ID` before the resident's grain is born.
`foreignPath` (69, fatal) is a defect in the controller's actions, not the box: keep the World's
state, report to HOSTING. Not yet run under systemd (the live harness renders no member unit).

The controller reads only the follow Store (`Launcher.check_follower`: the render refuses a launcher
whose Store is not its follower's, or whose user is not the follower's). Its exits and the
controller's (passed through) are EXITS.md's last two tables (HOSTING-19): a Store refusal (109)
or any defect stops the unit; a signalled controller (126), a failed report pipe (123) or a
lifetime end restarts. Run through the real programs (`deploy/live/unit-argv.py`): over an empty
store directory the controller ends `store` 109 and grain-launch exits 109.

The DRIVER, per World `L`, from `deploy/units/linux/nd-follow-drive@.service`: `nd sync` as nd
(the trusted side initiates to both sockets; `Driver.check_trusted`), every 40 s
(`Restart=always`, `RestartSec=40`; `sync_loop_under_start_limit`: an honest loop never trips the
start limit), with

    ND_WORKSPACE=/etc/nd/follow/L ND_FOLLOW_SOCK=/run/nd-follow/L.sock ND_HOST_SOCK=/run/nd/host.sock

Its ends are EXITS.md's `nd sync` table (PROTOCOL-38's CommandExit): a refusal by name (1) stops
it; `uncertain` (2), `behind` (51, still behind after the page bound: the next run continues) and
`client` (52, nd could not run: a socket or the workspace, named on stderr) run again. The
workspace is the follower's OBSERVE-ONLY custody (CLIENT-22, cfb789b; enrolment ROOT-ruled at
3e09d67), which, once sealed, signs read envelopes and nothing else (`refused envelopeOnly` for any
other step). Made in this order, as nd (`/etc/nd` root 0755, §2a: the whole chain must pass
StrictModes):

    sudo install -d -o nd -g nd -m 0700 /etc/nd/follow /etc/nd/follow/L
    sudo -u nd env ND_WORKSPACE=/etc/nd/follow/L /opt/nd/bin/nd --init-hosted
    sudo -u nd env ND_WORKSPACE=/etc/nd/follow/L ND_FOLLOW_SOCK=<the operator's follower socket> ND_HOST_SOCK=/run/nd/host.sock /opt/nd/bin/nd init OPERATOR_MEMBER   # prints `join HEX`
    # the operator's own nd: `enroll HEX` → `id OBSERVER`; `grant world OBSERVER observe --via OPERATOR_GRANT` → `id GRANT`
    #   OBSERVER and GRANT are the follower's ND_MEMBER / ND_GRANT in /etc/nd/hosted/L.env
    sudo -u nd env ND_WORKSPACE=/etc/nd/follow/L /opt/nd/bin/nd --seal-observer                # LAST: ws/keys → ws/observer, once

`--seal-observer` is irreversible (`exists` if run again, `rotationInFlight` while a rotation is
pending). `nd --init-observer` makes a sealed record directly, for tests only: it cannot join. Run through the real nd
(`deploy/live/unit-argv.py`, hbox): over an observer workspace with no follower socket, `nd sync`
exits 52 `nd: follow.sock: No such file or directory`: the rendered environment is the one nd reads,
and a missing socket is named and retried. A run against a serving writer and follower: PENDING.

A resident sees a new turn only after the driver's next `sync` (HOSTING-7's resident row,
113537f): the driver is a HARD dependency of hosting, so `nd-grain-launch@L` Wants=/After=
`nd-follow-drive@L` as well as the follower. A stopped or refused driver is a resident that never
sees new turns (liveness, not safety); every launch and stop waits up to `RestartSec` (40 s) plus
one sync. `worlds/L/members` must exist before the first launch (every plan hides it; a missing
hidden path is `pathMissing` at each launch, then `crashLoop`): the install line above makes it.

## 3. Status — RAN

    host check STORE
    STATUS height=H steps=N chain=C base_offset=O base_steps=B seg_bytes=S records=R torn=T use=U anchor=none

(the line `Host.Check` prints, field by field; parse it by field name, never by position.)
Read-only (no lock, writes nothing; works while the writer runs or is down). `torn>0` is the
writer's unsynced last frame. `anchor=none` means: integrity and height only, NOT completeness.
`use=U`: the number of distinct objects one member made that another member invoked or wrote, over
every call committed in the Store's segment (history and tail). A Store used by one resident reads 0
(PROTOCOL-43, db0b43c; planted: `use-zero-on-creates-only`, `use-self-use-zero`, `use-reads-every-call`).

`check` reads EVERY `index.log` entry the base counts; an open reads only the last one (HOST-33).
So a corrupt middle entry is refused at first read or by check, not at open: the writer opens and
serves, the first `log` page whose search reads that entry is answered `refused badIndex` (the
writer keeps serving), and `host check` refuses `indexCorrupt` (46)
naming it, `refused indexCorrupt entry K`. Planted in store-plants on the sealed Store:
`index-middle-flip-opens-page-badIndex`, `index-middle-flip-check-indexCorrupt-names-entry` (with
`index-middle-log-page-intact-control`). A damaged entry nobody pages through is found only by
`check`: run it on every backup (§4) and after any unclean stop. A corrupt LAST entry still stops
the open (`indexCorrupt`, the unit stops).

A failed READ of the Store's files for one page (an IO error in `log` or `read`, HOST-48 01396b7) is
refused that page, `refused pageIo`, and the writer keeps serving: it does not exit `ioServing` (6).
The writer's stderr carries one line per failed page, `STATUS page refused=pageIo error="<the IO
error>"`. The member sees `refused host pageIo` and runs its command again. One line means a
transient read failure; if it repeats, check the disk (`base.world`, `seg.log` and `index.log` are
readable by the writer's user) and run `host check STORE`. Planted in the Host's simulation
(`pageIoPlant`: the first page is refused, the second is served). The exit table is unchanged.

## 4. Backup — RAN (stopped and LIVE: store-plants)

Copy the files in the order `deploy/units/STORE.md` lists (generated from
`Host.Store.backupOrder`; the base before every append-only file), each whole. It is safe while
the writer runs, across a seal: a seal installs a new `base.world` atomically and the append-only
files only grow, so each one copied after `base.world` holds the prefix the copied base names.
Planted in store-plants: `live-copy-raced-a-seal` / `live-copy-anchor-at-segment-copy` (the right
order across a seal opens at the writer's height); `orphan-index-entries-*` (index entries past
the ones the stale base counts: a reader ignores them, the writer's open truncates them and
reopens at the same height). The OTHER orders are refused by name: `seg.log` copied before a seal is `segmentShort`
(`copy-segment-before-base-wrong-order`), `index.log` copied before a seal is `indexShort`
(`copy-index-before-base-wrong-order`); neither opens short. Record an anchor at the
same time: `HEIGHT:CHAIN` from a member follower's head (an operator's `host seal`, §2, is a seal like the
cadence's: the same order covers a backup taken across it) (its own `host check` on its follow
Store) or the highest receipt a client holds. The key travels with the copy (HOST-16: it guards
integrity, not secrecy; a copy without it is `baseCorrupt`).

## 5. Restore — RAN (store-plants; a sealed Store too: `sealed-*`)

Copy the files (`deploy/units/STORE.md`) into an empty STORE, then:

    host check STORE --anchor HEIGHT:CHAIN

A Store file reported `missing` (20, `refused missing FILE`, HOST-35) is never re-created by hand
and never genesis'd over: restore ALL of the Store's files from one backup (§4 order) into an empty
STORE. No open creates a Store file (only genesis does), so a missing `seg.log` or `index.log`
cannot silently come back empty. Deleted while the writer runs: the next batch's sync fails, that
batch ends `uncertain` (3, restarted; nothing is acknowledged) and the restart refuses `missing`
(fatal, the unit stops). Planted by HOST in store-plants: `missing-key`, `-base`, `-index`,
`-segment`, `missing-index-serve`, `missing-segment-serve`. An absent STORE directory is `io` (13).

0 and `anchor=ok` = the copy reaches the anchor with the anchor's chain. Without an anchor, a copy
cut at a frame boundary, a single foreign last frame and a rollback to an older complete copy ALL
open cleanly at a lower height; that is why the anchor is not optional.

## 6. Re-genesis with state carried (flag day) — RAN (store-plants `carry-*`, HOST-28 6b89d6f, KERNEL-29)

State crosses a flag day only by re-genesis from a checked export (law 1, OPS-1). History never
crosses: every old call and receipt is for the old World.

1. Stop the writer unit and every member's follow unit, by unit name. Export only from a STOPPED
   writer (HOST-28): the carried state is its last durable World.
2. With the OLD binary: `host export STORE OUT`. It reads STORE only (`carry-export-reads-only`),
   refuses an existing OUT (`refused out`, 17), and prints `carried HEX` (the file's digest),
   `from HEX` (the old origin) and `anchor H:C`. Record all three beside the backup.
3. The operator moves the old Store aside BY HAND (`mv STORE STORE.old-<date>`); nothing deletes it.
4. With the NEW binary: `host import STORE NAME OUT --digest HEX` (the `carried` digest; a fresh
   nonce is drawn unless `--nonce`). Refused by name, before any Store file is written:
   no `--digest` → `refused digest` (8); a wrong digest or a byte changed in transit →
   `refused carryMismatch digest` (49); a file written under another carried shape →
   `refused carried` (43, shapeMismatch): that flag day changed the carried shape and cannot
   carry, so it is a plain re-genesis (§1) and the old Store stays aside; `carryMismatch decode`,
   `anchor`, `tooLarge`, `carry NAME`. A `carryMismatch reopen` may leave a Store: move it aside.
5. `host check STORE`: the height is the old anchor's (the carry keeps it), the chain is the new
   World's own, `origin` (printed by import) is new.
6. Publish the new origin to members. Every call signed for the old origin does not land
   (`carry-old-origin-call-not-admitted`); members sign the new origin as their SAME member ids
   (`carry-new-origin-call-admitted`); a call committed before the export still answers `lookup`
   committed (`carry-lookup-committed-after-import`: the journal is carried, PROTOCOL-29).
7. Members re-create their follow Stores from the new World by reproducing the import (the same
   carried file, `--digest` and the import's printed `--nonce`). This is trust on first use BY DESIGN
   (cv 01a14de7-224a): a carried World has no genesis inputs a sponsor could sign, so there is no
   invitation to join from. Mitigation: each member compares the `origin` its own import printed with
   the operator's, out of band. Two imports of one export are two Worlds
   (`carry-two-imports-two-worlds`): the operator imports once, members reproduce that one.

## 7. Refusals and what the operator does

`deploy/units/EXITS.md`: every code of `host` and of nd-supervise, its class, what the rendered
unit does with it and what the operator does, generated from Host/Exit.lean, Protocol/Exit.lean
and the exhaustive `Ops.Units.hostAction` / `supervisorAction` (a new status without an operator
action does not build). No hand copy of it lives here.

## 8. Measuring THE BAR — RAN (scripts/bar.sh, PERF-2/3/4, at 5f7c58d; standing runs the bounded form on every judge)

THE BAR (CHARTER): two friends and a hosted resident; 1000 records; each write ≤ 5 s; a cold reopen ≤ 60 s;
measured over sockets on a quiet box. `scripts/bar.sh` drives exactly the deployed binaries: one writer
(`host serve`) and three actors, each with its own `nd` workspace, custody, and `host follow` Store. Every
process is under `nd-supervise`. The actors are two friends (`nd --init`, a separate holding) and today's
STAND-IN for the hosted resident (`nd --init-hosted`, driven by `nd` argv). HOSTING-8's resident replaces
the stand-in.

### The full measure (the operator, in a quiet window)

    scripts/bar.sh --records 1000 [--record]

- Run it from a checkout at the commit to be measured. It builds `host` and `bench-count` with lake, and
  `nd` and `nd-supervise` with `cargo --release`.
- `--root DIR` puts the Stores on DIR's device. The default is `$HOME`. The write latency is that device's
  fsync, and the `BAR device` line names it (ext4/nvme measured ~40 ms per write at p50; ZFS on tank
  ~540 ms). A tmpfs is refused by name.
- The custody workspaces always go under `$HOME`. Custody refuses a key under any directory a group or
  other can write (`refused … Dir`).
- THE BAR is judged only when the box is quiet: load1 < 2 before AND after the run.
  - Otherwise the verdict is `UNJUDGED load1 A/B >= 2`, naming any limit it would have exceeded.
    UNJUDGED is never a pass.
  - Limits come from `gates/bar.tsv` (`limit` rows: 5000, 60000).
  - A broken run is RED at any load: a failed or silent `nd`, a writer that never answers, a follower
    not at the writer's tip, use≠3, or a mid-run seal at the wrong step.
- `--record` appends a `run` row to gates/bar.tsv: date, sha, device, mode, N, load, write p99, writer and
  follow reopen, use, steps/cmd, seg-bytes/cmd, writer fds/cmd, verdict. These rows are the trend, never
  a ratchet. Commit them through `scripts/commit` like any change.

What one run does, in order:
1. Genesis with three founders.
2. Each actor creates an object and grants it `anyone mutate`.
3. Half the writes, each actor alternating its own object and the next actor's through the grant.
4. The writer is stopped by its PID file, `host seal W` runs, and the writer starts again.
5. The other half of the writes.
6. Every follow syncs, and `host check W --anchor` holds each follow's head.
7. The cold reopens are timed: a new writer up to its first reply, then a new follow up to its first
   `nd read` answered.
8. `bench-count W` re-derives the writer's tail at deployed parameters.

The lines to read:
- `BAR verdict`.
- `BAR limit write-p99-ms V limit L` and the two reopen limits.
- `BAR use 3 of 3` (PROTOCOL-43: objects one member made and another used).
- `BAR count stale-writes / stale-reruns / stale-after-sync`. A stale write is re-run after one `nd sync`,
  at most 8 times. Each stale refusal spends the member's refusal budget (16 per window; cv 01a14edf-6f12).
- `BAR count …` deterministic counts: steps, records and log bytes per command; supervisor fds; the reopen
  tail; trie hashes and verifies per step.
- `BAR load-before / load-after (N cpus)`.
- `BAR scope`, which says what this run is NOT: one box, no ssh, the resident a stand-in, a warm OS cache.

### The bounded form (standing; nothing for the operator to do)

    scripts/bar.sh --records 60 --standing --root {fresh}        (gates/runs.tsv `script:scripts/bar.sh`)

- One command at a time, so every count is a function of N.
- The clock is reported, never judged.
- The counts are pinned in gates/waste.tsv (op `bar`; ceilings only fall).
- Its known-red control `--harness-control` must read RED naming `harness-control` with all four planted
  expectations fired (limits 0, use 4 of 3, follow one step past the writer, bench-count's own control),
  or the runner reads none of its verdicts.

### The worst cut (a bench, not a bar run) — PENDING (PERF): `bench-worstcut` is not on main

It lands as a standing-only row once GATES picks the mechanism; PERF sends the hash, and this paragraph then reads RAN.

    bench-worstcut SCRATCH

- Writes a deployed Store whose tail past its base fills tailMax: 28,928 one-slot writes, 18.85 MB of
  18.88 MB.
- Counts the reopen: 20.374 trie hashes and 0 verifies per step. A reopen verifies no signature
  (HOST-22).
- Counts the follower's re-derivation: 20.374 trie hashes and 1 verify per step.
- About 2 min 16 s and 87 MB on hbox.

### What a bad number means

- write p99 high and load low: check the Store device's fsync first (`BAR device`).
- reopen high: compare `BAR count reopen-tail-bytes` with the base. A writer whose seals stopped landing
  reopens a longer tail; `host check` shows `base_steps` far behind `steps`.
- `writer-supervisor-fds-per-command` above 0: nd-supervise is holding connections (cv 01a14ed9-8c59
  was exactly that). At 1024 fds the box's soft limit refuses the unit at launch
  (`refusedAtLaunch`, EXITS 64: `RLIMIT_NOFILE N is below the M fds it may hold`, CLIENT-28; raise `LimitNOFILE`).
- stale re-runs reaching `declined refusalBudget`: honest contention spent the budget (KERNEL-19's open
  question). The members re-run later, after the window moves.
