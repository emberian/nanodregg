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

### 1a. The custody fence, as Ember ratified it (2026-10-21; HOSTING-17 addendum, decisions/hosting.md)

The deployed fence is the one built through HOSTING-17/20/25/26/32, CLIENT-26..32 and OPS-15 (DECISIONS-20261021.md
card 5), ratified as built. What the operator may rely on: `nd` runs `host serve`, keybroker, nd-members and every
nd-supervise child; `nd-hosted` runs grain-launch, the controller and every grain, and is in no group of `nd`'s; the
provider key is read by keybroker alone; member seeds and resident follower Stores live under `/srv/nd-members/L`,
nd 0700, outside the hosted tree. Two widenings are named and nothing else widened: `signIncoming` (CLIENT-27, bounded:
while a rotation is armed the precommitted next key may sign READ envelopes, never a call), and the TCB's two
unverified crates `signal-hook` and `signal-hook-registry` (gates/tcb.tsv, CLIENT-30).

RUN WITH TWO REAL UIDS (hbox, 2026-10-21, HOSTING-40; the row `cargo-untraced:launcher:fence`): the 0660 group peer
check refuses `nd`, a third uid holding the group and `nd-hosted` with another gid (`peerRefused`), and decides
`nd-hosted`; the grant naming `/home` is refused by name for both uids, but by the grant scan (`cannot list grant`)
before the `/home` hide is reached, because hbox's homes are 0750 (cv 01a155e0-8f91). The run needed three fixes,
above and in §2a: the nd-bwrap ACL (gone with bwrap, CLIENT-48), mkdir at mode, UMask 0027 on keybroker and nd-members. The units themselves
(sysusers, tmpfiles, `User=`, NoNewPrivileges) are still to run on a box (STAND-INS B1 and B6).

DEPLOYMENT SHAPE (Ember, 2026-10-21): the deployment will be inside its own VMs. That changes STAND-INS B1: the
"deployment box" is a VM, so B1's system-unit run (sysusers, tmpfiles, `User=`, `RuntimeDirectory=`, NoNewPrivileges,
and the confinement's Landlock floor, ABI 3) is run INSIDE a VM image with two real uids, not on a shared host; the box window is
the VM's. Nothing in the rendered units changes for it. The VM is a boundary outside the nd / nd-hosted fence, not a
replacement for it: this RUNBOOK still installs both uids.

## 2. Start — RAN as user units (deploy/live on burst5: host units OPS-2 runs 1–4; keybroker, hosted follower, grain-launch OPS-3 run 2)

Writer's node (systemd system unit, `deploy/units/linux/nd-host-serve.service`, emitted by
`emit-units deploy/units` from Host.Status and Protocol.SupervisorExit; `gates/generated.tsv`
refuses a unit file that differs from the tables):

    nd-supervise /run/nd/host.sock --write /srv/nd/store --exec /opt/nd/bin/host --landlock-abi 6 --hide /srv/nd/ws --hide /home -- /opt/nd/bin/host serve /srv/nd/store

THE PRODUCTION PROFILE (CLIENT-52). The writer's and the hosted follower's units carry the confinement
profile `Ops.Units.Node.profile` renders: the tree read-only but the Store (and the follower's socket
directory), the Store `NoExecPaths`, no home, private /tmp, /dev and IPC, the kernel-surface lines
(`SystemCallFilter=@system-service @sandbox`, `RestrictNamespaces=yes`, `MemoryDenyWriteExecute=yes`,
`CapabilityBoundingSet=`, `RestrictAddressFamilies=AF_UNIX`, `IPAddressDeny=any`, …) and finite
resources (`MemoryMax=2G`, `TasksMax=64`, `LimitNOFILE=1024`, `LimitFSIZE=4G`). `--landlock-abi 6`
makes nd-supervise refuse to launch on a kernel below Landlock ABI 6 (Debian 13's 6.12; exit 64,
`confine: landlock ABI 5, the policy requires 6` on stderr), never run with less; every start logs
`nd-supervise: confine: landlock ABI N: full|PARTIAL …`. nd-supervise itself refuses to run as root or
holding a capability (`privileged`). THE STORE'S TOTAL SIZE IS THE OPERATOR'S: `/srv/nd/store` (and each
`/srv/nd-hosted/worlds/<label>/store`) is its own fixed-size filesystem or carries an XFS/ext4 project
quota, because no unit line bounds total writes (`MemoryMax` bounds memory, `LimitFSIZE` one file).
`deploy/live/confined-unit.sh` runs the writer, and with `PROBE=1` the sandbox probe, under exactly
these lines read back out of the rendered unit.

RETENTION (HOST-64, KERNEL-44 Part 2). The unit above keeps every file, the default: no `--retain` is rendered. To
keep only the newest N segment files, set the node's `retain` in Ops/Units.lean (`Node.retain := some N`) and
re-render: `host serve /srv/nd/store --retain N`. N below 2 is refused twice by one name: at render
(`retainBelowFloor`, nothing is written) and by `host` itself (`refused retainBelowFloor`, exit 8 `usage`, nothing
opened); a non-number is `usage retain`. A follower node takes none (`retainOnFollower` at render): the hosted
follower is the ARCHIVE and keeps everything by default, so retention on the writer never loses history for
members who follow. What retention drops is read back as `checkpointed` (61) on a `log` page below `retained_from`
(§3). `host seal STORE --retain N` takes the same flag, for the operator's seal of a stopped writer.

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
A host killed by a signal is nd-supervise's 66 childSignaled, restarted (the child is the program
itself on both platforms, so the death arrives as the signal, CLIENT-48).

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

    sudo install -D -m 0644 deploy/units/linux/sysusers/nd.conf /etc/sysusers.d/nd.conf
    sudo systemd-sysusers
    sudo install -m 0644 deploy/units/linux/tmpfiles/nd-broker.conf /etc/tmpfiles.d/nd-broker.conf
    sudo systemd-tmpfiles --create /etc/tmpfiles.d/nd-broker.conf
    sudo install -m 0644 deploy/units/linux/tmpfiles/nd-member.conf /etc/tmpfiles.d/nd-member.conf
    sudo systemd-tmpfiles --create /etc/tmpfiles.d/nd-member.conf

On hbox the confs are installed (the five tmpfiles confs and nd.conf, 2026-10-21; `/etc/sysusers.d` did not exist, hence `-D`), so a reboot recreates the dirs.

The second pair makes the MEMBER root `/run/nd-member` (`d /run/nd-member 2710 nd nd-hosted -`, the same
shape, HOSTING-20/25): a resident's member socket `/run/nd-member/<dirOf id>/nd.sock` is served as
nd and reached by the hosted group. It must be disjoint from `/srv/nd-hosted` and `/run/nd-broker`
(grain-launch refuses nesting: `rootsOverlap`, 117).

The keybroker and nd-members units run with UMask=0027, not 0077 like the other units: the resident
socket directory is created under the setgid parent and must be 02710 so the hosted group can search
it. Under 0077 it comes out 02700 and keybroker ends `sockDir` (105), so neither unit can serve a
resident in a two-uid deployment (HOSTING-40 R4). Other bits stay off; the socket itself is chmodded
0660/0600 explicitly (by keybroker, and by nd-supervise for nd-members' sockets).

The sandbox installs nothing (CLIENT-48): every confined child restricts itself with Landlock and
seccomp before its program runs, so there is no mechanism binary, AppArmor profile or ACL to deploy.
The box needs a kernel with Landlock enabled at ABI 3 or newer (`landlock` in
`/sys/kernel/security/lsm`; Linux 6.2+); without it every launch is refused `MechanismMissing`.
A unit with `SystemCallFilter=@system-service` must add `@sandbox` (the Landlock and seccomp calls,
each of which only restricts its caller), or the same refusal follows.

The render refuses a hosted user equal to the key holder (`hostedIsKeyHolder`,
`Ops.Units.Broker.check_hosted_ne_user`): keybroker cannot tell that misconfiguration from the
one-uid test, so the install refuses it. The keybroker's custody layout, which passes by
construction:

    sudo install -d -o root -g root -m 0755 /etc/nd
    sudo install -d -o nd -g nd -m 0700 /etc/nd/keybroker
    sudo install -o nd -g nd -m 0644 deploy/tls/anchors.pem /etc/nd/keybroker/anchors.pem
    sudo install -o nd -g nd -m 0644 deploy/tls/pins /etc/nd/keybroker/pins
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
- the PROVIDER'S LEAF KEY IS PINNED, as operator data (HOSTING-28). `/etc/nd/keybroker/pins` (keybroker's
  third argument; same custody as the anchors: a regular file owned by `nd`, mode 0644, no writable
  directory above it) holds one line per accepted leaf: `HOST HEX` plus LF, HEX the 64 lowercase hex
  digits of the SHA-256 of the leaf certificate's DER SubjectPublicKeyInfo; no comments, no blank
  lines, no uppercase, no pin twice (else `pinsMalformed` 148). An empty file is no pin. The shipped
  `deploy/tls/pins` holds the `api.anthropic.com` leaf taken 2026-10-21 (generated by `emit-pins`
  from `Hosting.Pins`, gated; two fetches from hbox and two from another network agreed, SPKI
  SHA-256 `9fe3851d…4045eae`, leaf valid until 2026-12-20 19:15:03Z, issuer Google Trust Services WE1).
  The leaf rotates: from its renewal on, every real call is refused `pinMismatch` (23) on every ask,
  loudly, until the operator pins the new leaf (the recipe below; the shipped file only moves at a
  rebuild). A host with no line is refused the same way. A missing file stops the unit `pinsMissing` (146, fatal, not restarted); the
  other custody refusals are 140-145 and 147 (EXITS.md). The pin is host-scoped. No ExecStartPre
  compares it with the build's copy: rotation needs no rebuild. To pin (the first real call is the
  operator's act), compute the leaf key's hash:

      openssl s_client -connect api.anthropic.com:443 -servername api.anthropic.com </dev/null \
        | openssl x509 -pubkey -noout | openssl pkey -pubin -outform der | sha256sum

  and write `api.anthropic.com HEX` to the pins file. Run it from TWO vantage points (different
  networks) and compare: a pin taken during an attack pins the attacker, and nothing checks this.
  Across a provider's key rotation keep the old line beside the new one, then remove the old. A
  `pinMismatch` cannot tell an attack from a rotation, and keybroker logs nothing per ask: the operator
  learns it from the resident's refusals. Restart the unit after editing (the file is read once);
- the ANCHORS are narrowed to the provider's roots: 7 of 121 (GTS Root R1, R3, R4; SSL.com Root CA RSA
  and ECC; SSL.com TLS RSA and ECC Root CA 2022), from Certificate Transparency (10-18), never a
  handshake. A certificate chaining to any other root is `tlsCertificate`. If the provider moves to
  another CA, add its root's DER SHA-256 to `PROVIDER_ROOTS` (deploy/anchors) and re-emit
  `deploy/tls/anchors.pem`, then reinstall it (ExecStartPre refuses a copy that differs);
- the resident never sees the provider's body (HOSTING-29): keybroker's decider reads the JSON in Lean
  and the resident receives `reply TEXT`, `status N` (any provider status other than 200, body never
  relayed) or `refused NAME`. A 200 body that is not one object with a `content` array of typed
  blocks, or has a repeated key, is refused `replyMalformed` (22). A reply text holding the key is
  `keyEchoed`;
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
  PASS): it starts under NoNewPrivileges=yes with the decider confined (then by nd-bwrap; now by its own step, CLIENT-48); a SIGKILLed
  decider ends keybroker `deciderSignaled` (102) and the unit restarts; a one-byte edit of the
  installed anchors makes ExecStartPre refuse every start until the start limit (keybroker never
  runs); key mode 0644 stops it `keyFileMode` (84), SOCKDIR 0755 stops it `sockDir` (105), each with
  no restart. Run 1 found that `RestrictAddressFamilies` without AF_NETLINK killed the decider at
  every start (bwrap brought the sandbox's loopback up over NETLINK_ROUTE); with bwrap gone
  (CLIENT-48) the unit no longer allows AF_NETLINK.

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
    sudo install -d -o nd-hosted -g nd-hosted -m 0700 /srv/nd-hosted /srv/nd-hosted/worlds /srv/nd-hosted/worlds/L /srv/nd-hosted/worlds/L/store
    sudo -u nd-hosted /opt/nd/bin/host join /srv/nd-hosted/worlds/L/store INVITATION KEY_HEX

The follower's Store is JOINED from the operator's invitation (PROTOCOL-42), never a reproduced
genesis: INVITATION is the `invite HEX` the operator's own member prints (`nd invite`, §2 step 1)
and KEY_HEX that member's own `key HEX` (`nd --keys`). Here the sponsor IS the operator and the box
is the operator's, so the key crosses no channel and nothing is kept on the box: `host join` takes
both as arguments, the operator's shell is the only reader, and to re-make the Store (moved aside
after a `store` refusal, §5) the operator runs the same line with a fresh `nd invite`. It prints the
genesis lines, then `sponsor HEX` (the operator's member id: OPERATOR_MEMBER in the observer's
`nd init` below) and `input HEX`. A forged invitation is `refused inviteRefused pinMismatch` (44), a
key other than the signer's `refused inviteRefused notSponsor` (44), both writing nothing, as is an invitation
whose World's budget this binary does not admit (`refused allowancePastBound` 58 / `potentialPastBound` 59,
HOST-56: the sponsor's binary has another budget; do not join it); a join
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

The MEMBER sockets, one `nd-members` per World (HOSTING-30, CLIENT-29), from
`deploy/units/linux/nd-members@.service` (as nd; the instance `L` is the World's label). It asks its decider
which resident grains the World holds (every 200 ms, as keybroker does) and, for each one that is
PROVISIONED, runs two nd-supervise children: the resident's OWN follower (`FOLLOW/<dirOf>/follow.sock`,
`host follow`, one follower per resident: a follower plans in its own member's name, ROOT ruled (A)) and
`nd --stdio` on `MEMBER/<dirOf>/nd.sock` (0660, the hosted group, only the hosted uid admitted), confined to
write the resident's workspace and connect to `/run/nd/host.sock` and its own follow socket. There is no
per-resident unit and no environment file; the unit reads `ND_PEER` from keybroker's
`keybroker.env` (§2a). Its decider is `hosting-residents /srv/nd/store` (HOSTING-33), which answers only the
residents question: no clock, no key slots and no operator id reach nd-members. Install `nd-members`,
`hosting-residents`, `nd-supervise`, `nd` and `host` in `/opt/nd/bin`. Roots, made by tmpfiles (`nd-member.conf` above; the follow root is its own file):

    sudo install -m 0644 deploy/units/linux/tmpfiles/nd-member-follow.conf /etc/tmpfiles.d/nd-member-follow.conf
    sudo systemd-tmpfiles --create /etc/tmpfiles.d/nd-member-follow.conf

`/run/nd-member-follow` is nd's 0700 (short, for sun_path); each `FOLLOW/<dirOf>` and `MEMBER/<dirOf>` holds
only its socket (a connector sees its socket's whole parent directory, CLIENT-20): `host.sock` therefore
sits alone in `/run/nd`, never beside keys.

PROVISIONING a resident replaces "start a unit before the birth": the name is the grain's id, so it may be
done just after the birth, and nd-members binds the socket within a tick. Under
the roots OUTSIDE the hosted tree (HOSTING-32, ROOT's ruling: a grain's plan reaches neither a member
workspace nor a follower Store; the stdio child's write set is MEMBERS alone), all nd 0700 with the
StrictModes chain clean (`nd-members.conf` makes `/srv/nd-members`; the rest is made at provisioning):

    sudo install -m 0644 deploy/units/linux/tmpfiles/nd-members.conf /etc/tmpfiles.d/nd-members.conf
    sudo systemd-tmpfiles --create /etc/tmpfiles.d/nd-members.conf
    sudo -u nd install -d -m 0700 /srv/nd-members/L /srv/nd-members/L/members /srv/nd-members/L/follow

`MEMBERS = /srv/nd-members/L/members`, `STATE = /srv/nd-members/L/follow`. Per resident `<dirOf id>`:
- `MEMBERS/<dirOf id>/` holds the member's custody (`nd --init-hosted`, `nd init`, the operator's `enroll`
  and `grant world … observe`): the workspace `nd --stdio` writes;
- `STATE/<dirOf id>/store`, the follower's Store, made by `host genesis … --nonce` with the World's genesis
  arguments; written only by the `host follow` child;
- `STATE/<dirOf id>/follow`, one line `MEMBER_HEX GRANT_HEX` and LF, mode 0600: the member and grant the
  follower acts as, so the stdio child cannot rewrite it either.
MEMBER, MEMBERS, STATE and FOLLOW must be pairwise disjoint trees (after canonicalizing): nd-members ends
`rootsOverlap` (161) otherwise, and `stateRoot` (160) if STATE is not a 0700 nd directory with a clean chain.
The hosted tree is kept apart from them by the grain plans (`roots_disjoint`), not by this check.
A resident's own trouble is never an exit; it is a line in the journal and that resident unbound while the
others are served: `memberMissing NAME …` (not provisioned yet; retried every tick), `socketDirShared NAME …`
(its directory holds something other than its socket: remove it), `memberCrashLoop NAME ROLE` (5 starts in
120 s; unbound until the World's resident set changes) and `memberSpawn NAME ROLE`. A removed resident's two
supervisors are sent SIGTERM (each names every open connection's close, `closed unreachable`, CLIENT-30) and
reaped on later ticks; `memberStopping NAME` says its rebirth waits for them (automatic: nothing to do), and
`memberStopForced NAME` says one did not end within its grace period and was SIGKILLed (some peer may have
seen the connection end without the named close; if it repeats for one resident, report to CLIENT). The
unit's own ends are
EXITS.md's nd-members table (150-161; only a signalled decider restarts; 7 is more than 1024 resident
grains). A removed resident loses both children, sockets and directories.
A launch whose member socket is missing is refused `pathMissing` and counted (as for the broker socket), so
provision before the grain is started. `foreignPath` (69, fatal) is a defect in the controller's actions,
not the box: keep the World's state, report to HOSTING. NOT run under systemd; the live harness renders
no nd-members unit. Run by hand: the rendered ExecStart's argv, with its paths rebased, parses (no
`usage` 150) and ends `memberRoot` (151) at a missing MEMBER.

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
one sync. `worlds/L/store` must exist before the first launch (every plan hides it; a missing
hidden path is `layoutMissing` at start, `pathMissing` at a launch, then `crashLoop`): the install line above
makes it. Since HOSTING-32 the hosted tree holds no member workspace: those are nd's, under
`/srv/nd-members/L` (§2b, provisioning).

A grain refused `crashLoop` (`restartsMax` = 5 exits inside `restartWindowMs` = 60 s) is relaunched by the
controller BY ITSELF once 60 s have passed since those exits, with no owner act: grain-launch reports its
clock every second (`tick`, `tickMs` = 1000; HOSTING-38). Fix the cause (for example a missing path, or
nd-members not yet serving the grain's member socket), then wait one window. An owner's stop and start is
no longer needed. While the cause stands, the grain retries in a burst of 5 once per window. Upgrade
grain-launch and the controller together: a controller without `tick` refuses it `badReport`.

## 3. Status — RAN

    host check STORE
    STATUS height=H steps=N chain=C base_offset=O base_steps=B seg_bytes=S records=R torn=T use=U retained_from=F anchor=none

(the line `Host.Check` prints, field by field; parse it by field name, never by position.)
`retained_from=F` is the step count at the oldest segment file the Store keeps (HOST-64): 0 while the Store
keeps its whole history, past 0 once `host serve --retain N` has dropped files. `check` verifies from there,
and `use=U` counts only the records kept. A `log` page below F is refused `checkpointed` (61): nothing is wrong
with the Store, the history was dropped by retention; the member joins from a served base (`nd adopt`, §2) or
reads the archive. The archive is the hosted follower: its unit takes no `--retain` (the render refuses one,
`retainOnFollower`), so it keeps every file; keep at least one follower alive if you set `--retain` on the writer.
Read-only (no lock, writes nothing; works while the writer runs or is down). `torn>0` is the
writer's unsynced last frame. `anchor=none` means: integrity and height only, NOT completeness.
`use=U`: the number of distinct objects one member made that another member invoked or wrote, over
every call committed in the Store's segment (history and tail). A Store used by one resident reads 0
(PROTOCOL-43, db0b43c; planted: `use-zero-on-creates-only`, `use-self-use-zero`, `use-reads-every-call`).

`check` reads EVERY index entry (`index.<k0>.log`) the base counts; an open reads only the last one (HOST-33).
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
transient read failure; if it repeats, check the disk (`base.world`, every `seg.<o>.log` and `index.<k0>.log` are
readable by the writer's user) and run `host check STORE`. Planted in the Host's simulation
(`pageIoPlant`: the first page is refused, the second is served). The exit table is unchanged.

## 4. Backup — RAN (stopped and LIVE: store-plants)

Copy the files in the order `deploy/units/STORE.md` lists (generated from
`Host.Store.backupOrder`: `key`, `base.world`, `index.<k0>.log`, then every `seg.<o>.log` oldest first; the
base before every append-only file), each whole. The segment files are a family, one per seal start that the
Store still keeps (`--retain N` drops the oldest), so list the directory and copy them all: a copy missing one
is refused `missing seg.<o>.log` (20) at the restore. It is safe while
the writer runs, across a seal: a seal installs a new `base.world` atomically and the append-only
files only grow, so each one copied after `base.world` holds the prefix the copied base names.
Planted in store-plants: `live-copy-raced-a-seal` / `live-copy-anchor-at-segment-copy` (the right
order across a seal opens at the writer's height); `orphan-index-entries-*` (index entries past
the ones the stale base counts: a reader ignores them, the writer's open truncates them and
reopens at the same height). The OTHER orders are refused by name: a segment file copied before a seal is `segmentShort`
(`copy-segment-before-base-wrong-order`), the index file copied before a seal is `indexShort`
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
STORE. No open creates a Store file (only genesis does), so a missing `seg.<o>.log` or `index.<k0>.log`
cannot silently come back empty (`refused missing seg.<o>.log`, naming the file's real start).
A segment file whose header fails its MAC under the Store key, or that is shorter than a header, is
`checkpointCorrupt` (62, fatal): keep the Store untouched and restore from a backup. A Store of the layout
before HOST-64 (`seg.log`, `index.log`) refuses `shapeMismatch` or `missing`: it is never read as the new
layout; re-genesis it (§1) or carry its state (§6). Deleted while the writer runs: the next batch's sync fails, that
batch ends `uncertain` (3, restarted; nothing is acknowledged) and the restart refuses `missing`
(fatal, the unit stops). Planted by HOST in store-plants: `missing-key`, `-base`, `-index`,
`-segment`, `missing-index-serve`, `missing-segment-serve`. An absent STORE directory is `io` (13).

0 and `anchor=ok` = the copy reaches the anchor with the anchor's chain. Without an anchor, a copy
cut at a frame boundary, a single foreign last frame and a rollback to an older complete copy ALL
open cleanly at a lower height; that is why the anchor is not optional.

### 5a. A joiner of a CARRIED World pins its origin (HOST-67 832a815)

A member who re-creates its follow Store from a carried World (§6 step 7) has no invitation to join from, so
without a pin it trusts the carried file's digest and the operator's word. `host import` can pin the World's
ORIGIN instead:

    host import STORE NAME IN --origin ORIGIN_HEX --nonce NONCE_HEX32

ORIGIN_HEX is the origin the operator's own import printed (`origin HEX`, out of band), and NAME and NONCE_HEX32
the same import's name and `nonce HEX`: the origin is a hash of the label, the nonce and the carried roots, so a
fresh nonce could never make a named origin. A carried World whose origin is not ORIGIN_HEX is refused
`refused carryMismatch wrongWorld` (49), before anything is written: the file is not the World you were told
of (another export, another nonce, or a doctored copy). `--origin` without `--nonce` is `refused nonce`
(8, usage) and a malformed ORIGIN_HEX is `refused origin` (8, usage); neither writes a Store file. An origin pin
checks no digest (`--digest` is the other pin; give one, not both), so it is as strong as the origin you obtained.
This flag is the INTERIM way to pin: when PROTOCOL-61 lands, `host join STORE INVITE KEY` takes the pin from the
sponsor's signed invitation and the manual flag is for the operator's own checks. Planted through the real binary
(store-plants `carry-import-origin-without-nonce`, `-malformed`, `-other-world-refused`, with
`-pinned-accepted-control`; a binary that sent `--origin` to the digest check turns three of them red).

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
   `refused carryMismatch digest` (49); a carried World whose allowance, or whose weight and allowance
   together, are past what this binary's budget admits → `refused allowancePastBound` (58) /
   `refused potentialPastBound` (59) (HOST-56: exported by a binary of another budget; do not import it);
   a file written under another carried shape →
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

- bar.sh refuses binaries that are not the tree's (PERF-7, ce23f2e): RED `binaries-stale` / `binaries-foreign`.
  It prints `BAR built lean ...` and `BAR binaries <sha256s>`, and `--record` on a dirty tree is RED `dirty-tree`.
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

### The worst cut (benches, not a bar run) — RAN (c392f51; split per shape by PERF-12; standing only, one `standing:bench-worstcut-<shape>` row each, GATES-17)

    bench-worstcut-writes SCRATCH      bench-worstcut-births SCRATCH
    bench-worstcut-retires SCRATCH     bench-worstcut-rows SCRATCH

- Each writes a deployed Store whose tail past its base fills tailMax in one tail shape (PERF-6, PERF-9; numbers
  measured on main e86f237 and c15487e, PERF-12): writes (18.661 trie hashes per step), births (30.595), retires (32.217, the
  worst) and rows (20.182: the Bell queue's ring, answer and retire cycles, LANG-59). Verifies are 0 at reopen and
  1 at audit in every shape. A reopen verifies no signature (HOST-22). A shape above its own pinned value, or any
  shape above the worst's 32.217, is RED.
- The writes shape is 28,928 one-slot writes. The WORST tail is retires: 32,320 revokes over a 5,812,239 B base.
- On hbox at load1 11-31 (reported, never judged; a loaded box, not a limit; PERF-12 on e86f237 and c8ebb06): writes about
  2-4 min, births 2-5, retires 4-6.5, rows 4.5-7 (its re-derivation alone is 2-3.5 min: each Turn is an invoke the
  follower judges again, and the Bell package is re-checked per invoke, LANG cv 01a1558a-1644). Under 200 MB each. Each prints its own
  phase clocks (`wall ms (reported, never judged)`).

### The worst World (a bench) — RAN (PERF-10, 359e9e8; standing row `worstworld`, the 200,000-entry form)

    bench-worstworld synthetic N

- A Store whose base holds N one-slot entries. A reopen decodes 2·entries - 1 trie hashes (2.000 per entry),
  exactly, at 200,002, 2,626,114 and 7,669,002 entries.
- The bound is `worldBytesMax` = 91,965,546 B (HOST-57, derived; KERNEL-68 raised it by 51,200 B, the meter's
  ≤ windowMax leaves; the counts and timings below are HOST-57's at 91,914,346): 2,626,114 entries, 5,252,227 hashes. By hand at
  the bound the reopen took 56.3 s on a loaded hbox (load1 12-15; reported, never judged; THE BAR's 60 s is a
  quiet-box limit, v2, so the margin there is unmeasured). One entry more (synthetic 2626113) is refused at the
  seal, `Host.genesis worldTooLarge`; no World an admitted turn reaches comes near it. A base record past
  `baseRecordMax` 91,914,474 B (HOST-64; its frame past `Log.frameMax`, the record + 36) is refused `baseTooLarge` (21) by a reader.

A bar.sh killed hard leaves its supervisors findable: its PID files live in `$HOME/.nd-bar/run.XXXXXX/NAME.pid`,
outside the run root. Stop them by those files only (never by pattern).

### What a bad number means

- write p99 high and load low: check the Store device's fsync first (`BAR device`).
- reopen high: compare `BAR count reopen-tail-bytes` with the base. A writer whose seals stopped landing
  reopens a longer tail; `host check` shows `base_steps` far behind `steps`.
- `writer-supervisor-fds-per-command` above 0: nd-supervise is holding connections (cv 01a14ed9-8c59
  was exactly that). At 1024 fds the box's soft limit refuses the unit at launch
  (`refusedAtLaunch`, EXITS 64: `RLIMIT_NOFILE N is below the M fds it may hold`, CLIENT-28; raise `LimitNOFILE`).
- stale re-runs reaching `declined refusalBudget`: honest contention spent the budget (KERNEL-19's open
  question). The members re-run later, after the window moves.

### THE BAR v2: two friends over ssh, the real resident, a cold cache. PENDING (PERF-2): the box, a person at each friend's machine, and Ember for drop_caches; the resident has landed (0e4d57f); nothing here has been run

What v1 (`scripts/bar.sh`, above) is NOT, and v2 is: v1 runs one box with no ssh, uses a hosted-custody
STAND-IN for the resident, and reopens with a warm OS cache (`BAR scope`). v2 measures the same four limits
(1000 records; each write ≤ 5 s; a cold writer reopen ≤ 60 s; a cold follow reopen ≤ 60 s) on the deployed
shape of §2, §2a and §2b.

Needs, each one RAN before the measure:
- **The box.** One host running the §2 `host serve` unit, the §2a keybroker, and the §2b hosted follower and
  grain-launch, with its Store on the device the operator means to run, named in the run's `device` line
  (never tmpfs). The box is quiet: load1 < 2 before and after, as v1 requires.
- **Two friends, two other machines.** Each friend has its own `nd --init` workspace, custody and
  `host follow` Store under its own `$HOME` (custody's StrictModes chain). Each reaches the box through
  CLIENT-12 B: its host.sock is `nd-supervise ws/host.sock … -- ssh -T box`, the box's authorized_keys line
  is `restrict,command="nd-attach HOST_SOCK"`, and its follow grant is an envelope (PROTOCOL's row). No
  StreamLocal forwarding, and no unix account per friend beyond the forced command.
- **The resident.** The HOSTING-27 Lean resident runs as a grain under grain-launch. It writes through its
  own member socket (HOSTING-25: MEMBER/<dirOf>/nd.sock served by `nd --stdio`) and asks through keybroker
  (HOSTING-29: it receives `reply TEXT` and never a provider body). Its share of the writes is the resident's
  own work, not argv. `use` must be 3 of 3 (PROTOCOL-43), as in v1: it comes from the friends' writes (the
  bell is the resident's object, used by the friends who ring it).
- **The resident's round** (HOSTING-11, under the bell queue LANG-58 / HOSTING-31, 96179fb, re-shaped by
  LANG-59 / HOSTING-34, c100be5: `answers` is deleted, a ring's answer lives in `rings[k]`): one ring
  answered = 2 writes, neither of which writes the Bell's cell.
  - A friend rings: 1 write inserting `pending[k]` {text} and `rings[k]` {answer none, text} (k = notBefore,
    ringer).
  - The resident's tick (Resident.tickMs = 1 s) is ONE `read BELL pending 64`, which returns every
    unanswered ring in key order. It answers the lowest first: 1 ask (keybroker), then 1 write, through its
    member socket `--via` its grant, upserting `rings[k]` to {answer some TEXT, text RINGTEXT} and retracting
    `pending[k]`. It re-sends the ring's own text, read from `pending` in the same read, and the `rings`
    guard refuses a second answer (`rung: answered`) or another text (`rung: text`). The answer carries
    the reply text (1..2000 bytes).
  - Required steps: ring 79 (120 ticks), answer 96 (143 ticks), as LANG-19 measured at c100be5 (LANG-59;
    was 77 / 116 each). The owner's retire of an answered ring retracts `rings[k]`.
  - The resident writes only its bell's relations and holds no `anyone mutate` grant (widening that is a
    custody call, ROOT's). The World drives it; there is no argv or control socket.
  - Rings from different ringers commute, so v2 rings from both friends at once. Each round is timed
    from its ring's nd answer to the read that shows `rings[k]` with `answer some`; its floor is about one tick + the ask
    + two command round trips. The ring and the answer each count as one of the 1000 records. The tick
    is reported.
  - The run's own limits, never the resident's: `relationFull` when 64 rings are pending or `rings` holds
    1024 (until the owner retires answered ones). The 1000 records are at most 500 rings, inside 1024, so a
    v2 run that meets `relationFull` is RED by name. One ringer ringing twice from one view is `keyTaken`:
    v2 syncs before ringing again.
  - The resident never re-asks: one ask per ring, kept durably. `status N` comes back as the text
    `(status N)`, a refusal as `(refused NAME)`, a lost answer as `(unanswered ...)`. v2 records each such
    answer by name and does not re-ring (a re-ring is a new ask and a new meter charge).
  - The resident landed at 0e4d57f (HOSTING-27). Its exe is `resident` (`lake build resident`), placed as
    the grain's `pkg/resident`. `pkg/resident.conf` is `(record (bell #BELL) (grant #GRANT) (maxTokens N)
    (model "M") (system "S"))`, GRANT the operator's `observe,invoke:0` grant on the bell to the resident's
    member; the resident also needs an allowance on the model. The flow end to end is
    `launcher/tests/resident_bell.rs`.

The run, in order:
1. Genesis with three founders (§1); each actor creates an object and grants it `anyone mutate`.
2. 500 writes round-robin: each friend alternates its own object and the next actor's through the grant,
   and the resident takes its turn. Each write is timed at its spawner (the friend's `nd`, from exec to
   exit, over ssh; the resident's write, from ask to its nd answer).
3. The writer is stopped by its PID file (`systemctl stop`, seen gone), `host seal` runs, and the writer
   starts again: the midpoint seal, as in v1 (PERF-4).
4. 500 more writes.
5. Every follow syncs; `host check W --anchor` holds each follow's head; `bench-count` re-derives the tail
   (counts only: verifies 1.000 per step, trie hashes under the bar row).
6. **Cold reopens.** Stop the writer and the friends' follows by their PID files. Drop the page cache on
   each machine (`sync; echo 3 > /proc/sys/vm/drop_caches`, as root on EACH machine: a box act, ROOT-ruled the operator's: Ember drops the page cache on each machine (root), then says go. The run neither does nor assumes it; and a box
   where that is not allowed cannot run v2), then time: the writer from unit start to its first reply, and
   each friend's follow from start to its first `nd read` answered over ssh.

Judging is v1's: limits from `gates/bar.tsv` (5000, 60000), judged only at load1 < 2 on the box AND on both
friend machines, otherwise UNJUDGED (never a pass). A broken run is RED at any load: a refused connect, a
`closed …` from nd-attach, a follow not at the writer's tip, use ≠ 3, or a resident answer other than
a reply text (`(status N)`, `(refused NAME)` and `(unanswered ...)` are recorded by name, never re-rung).

`--record` appends a `run` row with mode `v2`, the three machines' load lines, each machine's device line, the
ssh RTT (median of 20 `ssh box true`, reported, never judged), and the wall-clock numbers. As in v1, the clock
is reported and judged only against the CHARTER limits on a quiet run. It is never pinned. What v2 adds to
v1's deterministic counts: nd-attach's per-connection fd count on the box (its WASTE row joins op `bar` at
0.000 per command, as the supervisors' did after CLIENT-28).

What the operator records if v2 fails a limit:
- a write p99 over 5 s with a low ssh RTT is the box's fsync or the writer; compare v1 on the same box;
- a cold follow reopen over 60 s: compare its bytes with `bench-worstcut-retires`'s tail (19.7 MB, the worst; PERF-6, PERF-12), and its clock with
  `bench-worstcut-rows`' re-derivation (an invoke tail re-judged: the slowest follow per byte), read over
  the friend's ssh link, since a remote follow pages its catch-up over the bridge (PROTOCOL's answer to
  CLIENT-12);
- the resident's writes slow but the friends' fast: the provider's latency is on the resident's write path,
  by design, and its median ask time is in the run row.
