# decisions/client.md — BUILD-CLIENT (client/, sandbox/)

Earlier entries, frozen in `DECISIONS.md`: CLIENT-1 (Rust at all; ruled by ROOT 2026-10-16: custody +
transport only, ≤ 2,000 lines), CLIENT-2 (follow drives by steps; ruled, protocol in HOST-9), CLIENT-3
(attempts), CLIENT-4 (workspace dir, OpenSSH forwarding), CLIENT-5 (Ed25519 until KERNEL names the
scheme), CLIENT-6 (no binary until the generated table), CLIENT-7 (sandbox/ own crate, Hermes is a member;
ruled), CLIENT-8 (isolation invariant), KEY-CUSTODY (open, for Ember).

## CLIENT-9 one confinement shape, deny by default, one mechanism per platform, no fallback (2026-10-16; allow-list landed by CLIENT-2)
**Decision.** `sandbox/` exposes one function: `command(policy, program, args) -> Command`. The policy
is ALLOWS plus an invariant: `read`, `write`, `exec` (paths the child may touch; the program, which must
be absolute, is always read+exec) and `hidden` (paths that must lie outside every allowed path and the
platform floor; a policy where one reaches the other, either way, is refused as `Exposed` before
launch). macOS: `sandbox-exec` with `(deny default)`, `process-exec` of the program and `exec`,
`file-read*` of the floor + read/exec/write, `file-write*` of write, `file-read-metadata` of each
allowed path's ancestors (realpath stats them). The macOS floor was MEASURED by bisecting a deny-default
profile until `/bin/cat` and a lake-built Lean exe (host-sim, ALL PASS) ran: the `/` listing (literal;
dyld aborts with rc 134 without it — the predecessor's failed attempt), `/dev/urandom` (the Lean
runtime opens it at start), `/usr/lib`, `/System/Volumes/Preboot/Cryptexes` (the dyld shared cache).
No network, no mach/IPC, no fork, no sysctl. Linux: `bwrap --unshare-all --disable-userns --cap-drop
ALL --clearenv --dev /dev --proc /proc`, read-only binds of the floor (`/usr`, `/lib`, `/lib64`,
`/etc/ld.so.cache`, the optional ones `-try`) and of read/exec/program, `--bind` of write, nothing else
mounted. The environment is cleared on both. Any other platform, a missing mechanism, a missing or
unnameable path: refused by name, never launched. `nd-supervise` takes `--hide/--read/--write/--exec`.
A Host child gets `--write STORE --hide WORKSPACE` and nothing else (HOST-2's answer: STORE is the only
path it reads or writes). It gets NO socket: the child speaks only stdio, the supervisor holds the
sockets, so the brief's "allow the sockets" is deliberately not granted.
**Alternatives.** (a) The deny-list this replaced (`(allow default)` minus the hidden paths, `--ro-bind
/ /` + tmpfs); (b) Landlock on Linux (in-process, no bwrap); (c) minidregg's two bwrap profiles (P3);
(d) a whole-volume read allow with only writes restricted.
**Why.** The child is a parser of bytes from the network (a friend's frames); it should see the Store
and its own runtime, not the member's home (other keys, the ssh agent socket, browser profiles), which a
deny-list exposed. With deny-by-default the CLIENT-8 invariant is a CHECK on the policy plus a plant on
the profile, not a rule that might be forgotten. One argv shape for every child is law 1.
**Critique.** The floor is a hand list measured on ONE macOS version; an update that moves the dyld cache
breaks every child at launch (loudly: abort, which is the right failure, but a dead node). `/usr/lib`
and `/System/…/Cryptexes` are subtrees, wider than the dylibs one exe links. Children must be given
REAL paths (a `/var/…` argument fails: the `/var` link is not readable); nd-supervise does not rewrite
argv, so the service file must. `sandbox-exec` is deprecated by Apple. The Linux branch has only been
`cargo clippy --target x86_64-unknown-linux-gnu`-checked, never run (no Linux box; hbox is Ember's):
merged-/usr distributions with `/lib → usr/lib` symlinks may need `--symlink` instead of a bind, and
that is unknown. The tests' python children need their framework prefix as read+exec (it re-execs
itself), which is a test fixture's need leaking into the policy surface (`exec`).
**Meta-critique.** I measured the floor with the two binaries I had and stopped when they ran; a real
`host serve` (FFI to Host/c, fsync, flock on LOCK) may need more, and I am assuming flock/fsync on an
allowed fd need no extra operation. The "no sockets" call contradicts my brief; I think the brief
assumed the child dials, and HOST-2 says it does not.
**Plants.** sandbox/tests/confine.rs: confined cat reads an allowed file (control), fails on the seed in
the hidden workspace AND on an unmentioned sibling file (the allow-list property: red under the old
deny-list), a policy reaching the workspace (read its parent, or write it) is `Exposed`. Mutations:
adding `(subpath "/")` to the read clause, or `(allow default)`, turns both confine and
client/tests/supervise.rs red (`isolation: child read the seed`).
**Amended (a1bd695, a53bffc).** The floor also allows exactly `sysctl-read (sysctl-name "hw.ncpu")`:
the Lean runtime sizes its task pool from it, and denied, `IO.asTask .dedicated` runs inline, so ANY
Lean resident that reads stdin on a task (`host serve`, `host follow`) answers nothing until EOF and
then exits 0, which every rc-only check passes. The bisect above used `host-sim`, which never reads
stdin on a task, so it missed this: a floor measured with a binary that does not exercise the
runtime's concurrency is not a floor for the residents. Plant: a confined `host serve` must answer
within 3 s (tests/supervise.rs).
**Linux, first run (hbox, Ubuntu 24.10, bubblewrap 0.10.0, 2026-10-17).** Three findings, all fixed:
(1) `--disable-userns` requires `--unshare-user` (`--unshare-all` only tries it): every launch failed.
(2) Merged /usr (`/lib -> usr/lib`, /lib64, /bin): the floor recreates each link with `--symlink`
instead of binding it. (3) `kernel.apparmor_restrict_unprivileged_userns = 1` gives the distro
`/usr/bin/bwrap` no capabilities in its user namespace (`setting up uid map: Permission denied`), so
the mechanism is `/usr/local/libexec/nd-bwrap`, a root-owned copy of the distro ELF with its own
AppArmor profile granting `userns` to that path alone (`sandbox/apparmor/nd-bwrap`, with its install
lines); the global sysctl stays as Ember set it. Measured with the identical ELF minidregg's profile
already covers (`/usr/local/libexec/mini-grain-bwrap`, same sha256 as /usr/bin/bwrap): confine 3/3,
roundtrip, supervise (with the 3 s Lean plant) and the real round trip green under bwrap. The macOS
`hw.ncpu` lesson has no Linux twin to allow: the runtime uses sched_getaffinity, which bwrap does not
filter, and the round trip is green with no /proc, so /proc is no longer mounted. /dev is needed
(without it `host follow` closes at its first frame). Plants: re-adding `--ro-bind / /` turns confine
red (`isolation: child read the seed`).
*Critique.* nd-bwrap needs root to install, per host; until it is installed every Linux launch is
refused `MechanismMissing` (the right failure, but a dead node). The macOS branch is now the
check-only one in the gates (scripts/commit runs on Linux). A distro bwrap update does not update the
copy: the install lines check the sha256, and whoever upgrades the distro must re-copy it.
**Platform row: `EXEC_FILTERED` (sandbox/src/lib.rs, ROOT 10-17).** macOS filters exec
(`process-exec` only for the program and `exec`); Linux bwrap does not, so every program under the
read-only /usr floor runs inside and `Policy::exec` bounds what is visible there, not what runs.
Nobody may read `exec` as an exec bound on Linux. Plant: `exec_is_filtered_exactly_where_the_platform_says`
(a shell allowed only itself starts an unlisted /usr/bin/true: ran on Linux, row false; flipping the
Linux row to true turns it red). The macOS half of the plant has not run since main moved to hbox.
**Status.** landed (macOS run 10-16; Linux run 10-17; nd-bwrap installed by ROOT 10-17).

## CLIENT-10 the step layout read by hand until it is emitted — a twin with an expiry (2026-10-16)
**Decision.** `client/src/wire.rs` reads and writes the step layouts of proposals/client.md §2
(argv, the four steps, resume) by hand, so `nd` runs end to end now. It is deleted the day PROTOCOL /
CODEC commit the layout in Lean and `Emit/Rust.lean` emits its reader; the step TAGS already come
from `generated.rs`. Asked of PROTOCOL/CODEC: the layout as a `Codec` in Lean and its Rust reader.
**Alternatives.** Wait (no `nd`, no end-to-end plant); have follow speak a layout the generator
already covers (it covers none yet).
**Critique.** This is exactly the shape law 1 forbids and HOST-5 already named: a Rust codec of a
Lean-owned shape, with a promised expiry. If the Lean layout differs, the round-trip test still passes
against its own scripted follow (a mirror) — the integration with BUILD-HOST's follow is the real check.
**Meta-critique.** ROOT asked for running binaries before my handoff, and that deadline chose this.
**Status.** superseded (CLIENT-2, 2026-10-16). CODEC landed the layouts as Lean data with an emitted
reader at f81e093 (`generated::layout::{Command, Resume, Step}`, CODEC-8: `k` and `result` are
length-prefixed); wire.rs is deleted and `run.rs` uses the generated `Step` itself (its own `Step` enum
was a second copy of the same shape). The client still checks the encoded `command` against
`ARGV_BYTES_MAX`, because the emitted `list` bounds each item and the count, not the total
(`Bounds.argvBytesMax` is stated as the total; asked of CODEC to make the Lean codec carry it).

## CLIENT-11 the member signature: pure Ed25519 or hybrid Ed25519 + ML-DSA-65, and Lean verifies it (2026-10-16, NOT IMPLEMENTED: waits for KERNEL)
**What is already fixed.** KERNEL's `Receive.Call` carries one opaque `signature : ByteArray` under one
`key : ByteArray`, and `Ctx.verify : key → message → signature → Bool` is the ONLY check
(`Derive.lean`: `badSignature`, `badPossession`). So the scheme is a property of the deployed `Ctx`, not
of the call shape. Custody's side is one function, `sign(message) -> bytes`, over the exact bytes a
`sign` step names; Rust never verifies, never decides acceptance, never chooses what is signed.
**Decision (proposed, for KERNEL).** Hybrid, as one opaque pair inside the existing fields:
`key = ed25519_pk (32) ‖ mldsa65_pk (1952)`, `signature = σ_ed (64) ‖ σ_ml (3309)`, both over the SAME
message under one domain (`Env.hash` customization, CODEC-7), and `verify` = BOTH halves verify, each
length exact, refused by name per half (`badSignature` split into `badEd25519` / `badMlDsa` so a row
can tell which leg failed). Custody derives both keys from the one 32-byte seed by a named KDF
(cSHAKE256 domain per scheme; ML-DSA keygen takes a 32-byte ξ), so there is still exactly one secret.
The precommitted next-key digest (KERNEL-6) commits to the whole pair.
**Who verifies.** Lean, in `Ctx.verify`, at the Host's `receive` and at every follower's `rederive`
(PROTOCOL-4). HOST-2 reports (10-16) that no layer owns an Ed25519 `verify` in Lean today, so a real
`host serve` cannot run yet even for pure Ed25519; this blocks CLIENT's real round trip (B) as well.
Options for the verifier, in order of preference: (i) an FFI to a verified C implementation (HACL*
Ed25519 and the libcrux/HACL* ML-DSA, the EverCrypt line) declared in Lean with the call's premise
asserted where it enters (law 4), census-listed; (ii) Ed25519 restated in Lean over GMP-backed `Nat`
(feasible, slow: a scalar mult per verify; ML-DSA in pure Lean is a larger port). Rust verification
(ed25519-dalek beside the Lean path) is refused: it is a Rust decision and a twin.
**Alternatives.** (a) Pure Ed25519 (today's custody, CLIENT-5). (b) Hybrid as two fields in the Call
(`sigEd`, `sigMl`), visible to KERNEL. (c) ML-DSA only.
**Why hybrid.** The log is permanent and followers re-verify it forever; a signature scheme broken later
(a quantum adversary against Ed25519) lets anyone forge history a NEW follower would fold. Ed25519 is kept
because ML-DSA is young (implementation bugs, side channels); the AND means a forger must break both.
**Critique of hybrid.** 3,373 bytes per signature and 1,984 per key against 64/32: at THE BAR (1000
records) that is ~3.4 MB of signatures, per `log` page ~70 signatures fit in one 256 KiB frame, and
every follower fold verifies both halves (HOST-11 already names verify as the cold follow's dominant
cost; ML-DSA-65 verify is, from published benchmarks I have not re-measured, of the order of Ed25519's, so
the cost is mostly bytes and I/O, not CPU). The PQ threat to a two-friends deployment is hypothetical today; the cost is
paid now. And the AND is only as good as its weakest IMPLEMENTATION: an FFI verifier that returns true
on a malformed σ_ml (or a Lean glue that ignores one half) gives Ed25519-only security while every
document says hybrid. That is exactly minidregg's state: its SDK signed under
`MINI/SDK/HYBRID/ML-DSA-65/v1`, the verifier's comment said Lean's `CredentialSignatureIO.combineHalves`
decided the conjunction, that function did not exist, and `verify-mldsa` had no caller: the ML-DSA half
was verified NOWHERE on the Lean path (DELETE-RUST-20261016 S2; cv 01a14700). So hybrid ships only with
two plants: a call whose σ_ed is valid and σ_ml is flipped must be refused `badMlDsa`, and vice versa,
both as rows against the real `host serve`, both mutation-checked.
**Critique of pure Ed25519.** One scheme, 64 bytes, a verifier small enough to restate in Lean and prove
against RFC 8032 vectors; but rotating to PQ later is a re-genesis (free here) AND a re-signing of every
member key, and the history signed before the rotation stays Ed25519-only forever, which is the attack
the hybrid exists for.
**Meta-critique.** I lean hybrid because minidregg did it and because "post-quantum" is the fashionable
answer; the honest decider is whether anyone ever follows a log signed today after a CRQC exists. The
option ordering (FFI to HACL* first) is chosen to avoid porting ML-DSA to Lean, the hard part; that
puts unverified-by-us C (but machine-verified upstream) in the TCB.
**Status.** open: KERNEL decides which signature a Turn carries (pure or hybrid, and the refusal names);
ROOT assigns who owns the Lean verifier. CLIENT implements custody's half the day it is named.

## CLIENT-12 friends over ssh: the remote host.sock (2026-10-16, DESIGN ONLY: waits for PROTOCOL's row)
**The need (THE BAR).** Two friends and a hosted Hermes on one Store. Each friend runs `nd` and their
OWN `host follow` (consent is their own fold, HOST-7) on their own machine; the one writer `host serve`
runs on the operator's box. A friend's nd must reach the remote host.sock, and the friend's follow must
get the log (`log` op, gated in Lean by a follow grant, HOST-11).
**Option A: OpenSSH StreamLocal forwarding (CLIENT-4 as written).** `ssh -N -o StreamLocalBindUnlink=yes
-L ws/host.sock:/srv/nd/host.sock friend@box`. Zero code. Each friend is a unix account on the box; the
socket must be connectable by them (0660 + a group: nd-supervise binds 0600 today, so this flips a mode).
**Option B: a forced-command bridge over one ssh channel.** The friend's machine runs `nd-supervise
ws/host.sock --hide ws --read ~/.ssh … -- /usr/bin/ssh -T box` (the SAME mux: many local connections,
conn-tagged frames over one child's stdio); on the box, the operator's `authorized_keys` has one line per
friend key: `restrict,command="nd-attach /srv/nd/host.sock"`, and `nd-attach` is the mux's inverse
(conn-tagged frames on stdin ⇄ one host.sock connection per conn; bounded by CONNECTIONS_MAX; exits on
EOF). No per-friend unix account, no group mode, no forwarding enabled in sshd (`restrict` turns it off),
revocation is deleting one line.
**Option C: a TCP listener** on the box with its own authentication (Noise/TLS + member keys). Refused:
new Rust crypto, a public port, and a second authenticated channel beside ssh; the Host already
authenticates every request by signature in Lean, so transport auth is only DoS control.
**Recommendation: B.** Because: sshd cannot restrict which socket a key may forward to (no `permitopen`
for streamlocal), so A makes every friend able to reach EVERY socket their uid can connect to on the box,
and gives each friend a shell account to harden (`Match User`, `ForceCommand`, `PermitTTY no`); B gives
them exactly one bridged socket and no account. B reuses the frame wire byte for byte (law 1: the
conn-tagged child frame is already the supervisor's one shape), and the remote end is the same
supervisor protocol read the other way.
**Critique of B.** It is new code on the box's attack surface (~100 lines, `nd-attach`, parsing frame
HEADERS from an authenticated but untrusted friend) where A is zero code; a bug there is reachable by any
friend key. One ssh connection carries every conn, so one slow friend conn head-of-line blocks that
friend's others (not other friends'). The friend's ssh client runs under nd-supervise's sandbox and
needs `~/.ssh` and the network, so the sandbox policy grows a `network` allowance it has refused so far
(or the ssh child runs unconfined: it holds no member seed, but it is a second process shape).
**Critique of A.** Correct by delegation and free, but its authorization is the filesystem (group mode on
a socket) and the friend count is unix accounts; that is the "ssh access IS the grant" shape HOST-11 (c)
rejected, moved one layer down. For the operator's own Hermes (same box) A is trivially right: a local
socket, no ssh.
**What PROTOCOL must define first (the row).** Which side pulls the log for a remote friend's follow
(follow asks nd for `host(log, from)` steps through host.sock — then the bridge carries it — or a
separate replication process), the row that a revoked follow grant stops `log` over the bridge, the row
that an unknown ssh key is refused by sshd (sshe2e), and the CONNECTIONS_MAX / idle-deadline numbers for
remote conns (PROTOCOL-8 names an idle deadline as CLIENT's). Asked of PROTOCOL (a45ff664477fefd42).
**Meta-critique.** I recommend B partly because it is the shape I can test on one laptop (two ssh-less
pipes stand in for sshd); A's real check is sshd configuration, which no test here can run. minidregg had
a forced-command `mini socket-proxy` (CLIENT-4's rejected alternative), so B is also familiarity; the
difference I claim is that B carries the existing conn-tagged frame, not a new proxy protocol.
**PROTOCOL's answer (a45ff664477fefd42, 10-16).** B. A remote follow catches up only through
`host(log, envelope)` steps relayed by nd over host.sock (so over the bridge); the envelope (member,
follow-grant id, fromHeight, validUntil, signature) becomes layout data in Protocol/Table.lean; revocation
refuses `noFollowGrant`; an unknown ssh key is a refused connect (no frame, no protocol name);
`Protocol.Bounds.idleMsMax` will be generated for remote conns; CONNECTIONS_MAX stays 64.
**Status.** B chosen; build waits for PROTOCOL's rows and `idleMsMax` in generated.rs (sha to come).
**Built (2026-10-17, BUILD-TRANSPORT).** `attach/` (its own crate and SIZE row, ROOT): `nd-attach
HOST_SOCK`, no peer label (one ssh session is one process, so the cap `peerConnectionsMax` is per
session). Every end is named: `closed full` past the cap, `closed unreachable` when the Store's
socket refuses or goes away, `closed ended` for a frame of an ended conn; the friend supervisor's
hang-up (PROTOCOL-23) closes the upstream connection, frees the slot and is acknowledged by name; a
box `closed` is relayed and ends the conn on the friend's side too. Exits are Lean's
(`SupervisorExit`: refusedAtLaunch for argv, childUnroutable for a malformed frame from the friend's
supervisor). Tested with two pipes for sshd in front of the real `host serve`
(attach/tests/attach.rs). **Declared absence:** a friend with several ssh sessions has several caps;
only sshd's MaxSessions/MaxStartups bind across sessions, so "one friend cannot take all
`connectionsMax` slots" does NOT hold.

## CLIENT-13 the precommitted next key: where custody holds it, and the rotation step (2026-10-16, FOR EMBER: key custody)
**Why this exists.** PROTOCOL's 5f7d90f makes a `sign` result `signResultLayout = (key, next, signature)`:
custody's current public key, its precommitted NEXT public key, and the current key's signature over
exactly the message (follow needs `next` for `init`/`enroll`, whose `next : D` is the next key's
digest). KERNEL-6's `rotate key next` is signed by the INCOMING key, which must hash to the member's
precommitted digest (`notPrecommitted`), and precommits the digest of the key after it. Row `rotate`
(JROT/JROTL): "a stolen daily key cannot rotate". So custody must hold a second secret, and the
question is where and how it is born. Until this is ruled, nd's `sign` answers a bare signature and
follow refuses it `badResult`: nd cannot sign anything.
**Withdrawn: a deterministic ratchet** (`next = H(domain, seed)`, one secret file). This was my first
lean, sent to PROTOCOL and ROOT; ROOT's critique is correct and I withdraw it. Whoever steals the
current seed derives the next key too, so a thief rotates first and the precommitment recovers from
nothing: row `rotate`'s premise becomes false while the row's plant (a thief with an ARBITRARY next key
is refused) still passes, because the plant's thief does not know the ratchet. The "no second secret
file" convenience is exactly what must be traded away. The next key is FRESH randomness from the OS
generated at precommit time, never derivable from the current seed.
**The question for Ember: where the next key lives.** Fresh randomness is necessary, not sufficient:
the next key protects against a compromise only if that compromise does not reach it too.
- **Option 1: the same custody record.** One file `keys` (0600, O_NOFOLLOW, owner, exact length, the
  current checks): `current ‖ next` (64 B), `current ‖ next ‖ pending` (96 B) during a rotation.
  Every transition is write-tmp + fsync + rename + fsync(dir): one atomic replace, so there is never a
  crash state where `current` and `next` disagree with each other.
  *Critique.* A thief who reads the file (a backup, a stolen laptop disk, a process that can read the
  member's home) has both keys, so pre-rotation recovers only from a leak of the CURRENT key alone: a
  signing side channel, a key pasted somewhere, a compromised signing helper. It is the convenient shape
  and it protects much less than the row's name says. Precommitment then mostly buys "rotate without a
  sponsor", not "recover from theft".
- **Option 2: a separate holding.** `seed` (current) in the workspace; `next` somewhere a compromise of
  the workspace does not reach: a file on removable media or another machine, a different uid's key
  broker (minidregg's `mini-keys`, SO_PEERCRED), or a hardware token. nd reads only the next PUBLIC key
  day to day (stored beside the seed, not secret); the next SECRET is brought to custody only for a
  rotation.
  *Critique.* Real compromise recovery, at a real cost: a rotation needs the member to fetch the
  offline secret (friction, and a member who loses it can never rotate again: recovery then goes
  through a sponsor's `enroll` of a new member, which loses identity continuity). Two places to back
  up. For a hosted Hermes there is no "offline": its next key would sit with the operator, which is
  Option 1 by another name. A broker uid is more Rust (KEY-CUSTODY's open question).
- Either way: the new next key is generated and written durably BEFORE the rotate call is frozen (the
  call commits its digest; losing it after that is a member locked out of rotation), and `current`
  advances only after the rotate call SETTLES committed, never on send.
**Rotation step shape (proposed to PROTOCOL).** Two new step tags and no new Rust decision:
1. `precommit` (no fields) → result `(next_pk, pending_pk)`. Custody returns the pending key if one
   exists, else generates one from OS randomness, writes it durably (Option 1: the 96 B replace;
   Option 2: beside the next secret), then answers. Idempotent: a retried command never mints a second
   pending key, so a frozen rotate call never names a key custody lost.
2. `signNext ‖ bytes message` → `signResultLayout` with `key = next_pk`, `next = pending_pk`, signed by
   the NEXT key (follow builds the rotate call with `key = next_pk`, `next = H(pending_pk)`). It refuses
   (by name, as a `done`) when no pending key exists. It arms the rotation: the following `submit`
   step's attempt is recorded as the rotation attempt.
3. The `submit` step as today. Custody advances on ITS OWN settlement (CLIENT-3), not on a follow
   command: committed → atomically `current := next`, `next := pending`; definitively refused → drop
   the pending key (a fresh one is minted next time); uncertain → stay armed, lookup only, resumed by
   `retry` (row JROTL's `--drop-reply` then `retry --expect-committed`). Advancing on a follow verb
   instead would let a follow bug move custody to a key the chain has not accepted.
Ordinary `sign` keeps meaning "the current key" and returns `(current_pk, next_pk, σ)`.
**Alternatives.** The ratchet (withdrawn above); one step `rotate ‖ message-template` where custody
fills in the next key's digest (custody would then build call bytes: a Rust decision, refused); advance
by a follow step (above).
**Meta-critique.** My first answer optimised for "one secret file" because the current custody code has
one, which is a phase ordering chosen to avoid a hard part. Option 2 is harder to build and to use; I have
not priced how often a two-friends deployment rotates, and that number decides whether Option 2's
friction is paid once a year or every week.
**Status.** RULED by Ember (10-16): Option 2 for members (separate holding); a hosted resident has
no offline and gets Option 1 (same record), with the rotate row's claim narrowed for it as above.
Implemented in client/src/custody.rs: `Keys` with `Separate` and `SameRecord`; `precommit` (idempotent,
durable), `sign_next`, `arm` (`ws/rotation` = attempt ‖ incoming ‖ pending, written before the first
send), `settle` (advance on committed, drop pending on refused; idempotent); nd settles an armed
rotation by lookup before every command. Custody refusals become tagged resume results that follow
renders (PROTOCOL-2's answer) once PROTOCOL-3 adds the `precommit`/`signNext` steps; until then rotation
is reachable only through the library and reconcile. The holding's checks (a 0700 directory, 0600
files, owner) refuse FAT/exFAT media, which have no modes: a removable holding needs a POSIX file system.
**Amended (CLIENT-27, 2026-10-18, ROOT ruling).** The next key signs the rotate that makes it current,
and, once that rotate is signed and armed, read envelopes until the rotation settles (`signIncoming`:
envelope-domain messages only, never a call). A hostile Host that refuses `unknownKey` falsely gains only
an envelope signed by a key whose public half it already holds. nd settles an armed rotation from its
own follow's receipt (PROTOCOL-46), never from a Host lookup.

## CLIENT-14 the mux: one writer per connection, the idle rule waits for nothing in flight, every close named (2026-10-17, BUILD-TRANSPORT; PROTOCOL-22; scout T2)
**Decision.** `client/src/mux.rs` reworked in place (no second mux). Each connection has its own
writer thread that owns the write half and is fed through a two-slot channel holding at most one
reply (an atomic `slot` flag) and the one last frame; `route` never writes to a peer, it only
`try_send`s, and a reply arriving while the previous one is unread closes that connection
`replyBacklog`. The reader (`forward`) records each request's send time; at a frame boundary it
wakes every quarter of `min(idle, reply)` and closes `replyTimeout` when the oldest request in flight
is older than `REPLY_MS_MAX`, or `idle` when nothing is in flight and the connection has been quiet
for `IDLE_MS_MAX`; a started frame is read through a deadline reader and closes `frameStalled` past
`FRAME_MS_MAX`, an empty or oversized one `frameRefused`. Every close is one last frame
`status::CLOSED ‖ CloseReason::name()` from the connection's own writer (so frames never interleave),
then shutdown; the over-the-bound accept answers `full`; a `closed` from the child ends that
connection after delivering it; when the child closes its stdout, queued replies are delivered and
the writers joined before `serve` returns (found by the route test going red 3 of 5 runs: the old
end shut streams under queued replies). On the client: host.sock reads `closed` as an unknown
status (settled by lookup, `tests/run.rs a_submit_answered_closed_is_settled_by_lookup`);
follow.sock renders `closed NAME`.
**Alternatives.** (a) One epoll loop: fewer threads, more Rust and unsafe-adjacent code under
`unsafe_code = "forbid"`. (b) Per-connection writers with an unbounded queue: a non-reading peer
then holds memory instead of a slot. (c) Write timeout only (no slot): T2's mutation shows a route
blocked for the whole write timeout per stalled peer.
**Critique.** Two threads per connection (≤ 2·64 + accept). The idle and reply clocks are Rust's
(law 2 stretch, PROTOCOL-22). The FIFO reply assumption per connection is stated, not enforced:
a reordering Host would make `replyTimeout` later, never sooner. `replyBacklog` closes a pipelining
client. The child is never told a connection ended: harmless for `host serve`, but it is why
`nd-attach` (CLIENT-12 B) cannot land yet — its per-session cap would leak upstream connections
until the box's idle close (a hang-up frame on the child wire is a HOST + PROTOCOL decision, asked).
Size: client/src rises 1715 → 1959 of its 2000 ceiling; `nd-attach` (~127 lines) does not fit.
**Meta-critique.** The mechanisms are T2's, ported because the head-of-line block is readable in the
old `route`; the mutation checks (six, each red) are the evidence, not a deployed measurement over
sshd.
**Status.** landed (this commit). `nd-attach` waits on the hang-up frame and the size ceiling.
**Amended (CLIENT-28, 2026-10-18).** The ≤ 2·64 + accept thread bound was false: a writer never ended when its peer left (2 fds + 1 thread leaked per connection), and `full` counted map entries. A connection is now one fd, counted until it closes.

## CLIENT-15 one custody read for every key holder, in the sandbox crate (2026-10-17, CLIENT-3; asked by HOSTING-3)

**Decision.** The custody read moves from `client/src/fsx.rs` (pub(crate)) to
`nanodregg_sandbox::custody`, public: `read_private(path, RangeInclusive<usize>)` and
`check_private_dir(dir)`, with `PRIVATE` (0600) and `PRIVATE_DIR` (0700). The client calls the moved
one and its copy is deleted; HOSTING-12's keybroker calls the same function for the operator's
provider-key file. A file is refused, each by its own name: `Link` (O_NOFOLLOW), `NotRegular` (a
directory, device, socket or FIFO; the open is O_NONBLOCK so a FIFO is refused, never waited on),
`Owner(uid)` (not the euid), `Mode(m)` (not exactly 0600), `Length(n)` (outside the caller's range,
or grown while read), `Io(e)`. The bytes are `Zeroizing`. Owner is checked BEFORE mode. The client's
SameRecord `keys` is read at `64..=96` and refused `Length` unless it is whole seeds: the range is
the read's, the record's shape is custody's.
**Alternatives.** (a) HOSTING copies the read into launcher/: a twin (law 1). (b) A third crate
`custody`: one more manifest and lock for ~90 lines; the sandbox crate is already the one both
launchers depend on, and "what a process may read" is its subject. (c) Keep a list of exact lengths:
HOSTING's key file has no fixed length; a range serves both, and the client's exact sizes are
`len..=len`.
**Critique.** The checks are unchanged in strength: same O_NOFOLLOW, same exact mode, same owner,
the length check now a range. Three things changed on purpose. (1) `NotRegular` split into `Link`
and `NotRegular`, so a refusal names which. (2) Owner before mode: the order changes only the name,
never accept vs refuse, and it makes the Owner refusal plantable without root (a 0600 file of
another user cannot be opened by us at all; root's world-readable `/etc/passwd` can, and is now
`Owner(0)`). (3) O_NONBLOCK: before it, a FIFO planted at a seed path hung the reader forever.
The owner plant needs a non-root runner and asserts so. `nanodregg-sandbox` gains two pinned deps
(rustix, zeroize, both already in client), so launcher/Cargo.lock and attach/Cargo.lock change.
**Meta-critique.** I moved `check_private_dir` too, though HOSTING asked only for the file read,
because it shares the owner/mode helper; leaving it would split one check across two crates.
**Plants.** `sandbox/tests/custody.rs`, one per refusal (link, mode ×4, owner, length ×2, directory
and FIFO, holding dir). Mutations, each red: NOFOLLOW removed, regular-file check removed, owner
check removed, mode check removed (two plants red), length check removed, NONBLOCK removed (red by
name `fifoWaited` at a 5 s liveness deadline, not a hang), the dir symlink check removed.
**Status.** landed (this commit).

## CLIENT-16 the phone's leaf Fits check: a theorem of Lean's leaf decoder, not a Rust refusal (2026-10-17, CLIENT-3; PROTOCOL-6's routed item, cv 01a149bf-8b34)

**Asked.** The phone's leaf decoder must refuse a leaf whose cell is not `Codec.Kernel.Cell.Fits`
before it trusts a read: the `hlf` premise of `Receive.deployed_head_read_sound` (KERNEL-31), with a
named refusal and a plant that skips the check and goes red.
**Found.** (1) No head-read path exists in any layer. The client has none; PROTOCOL-14 ruled option
A (`read` serves base pages a thin member checks against a pinned World digest) and left option B,
the per-cell inclusion read a phone would run, unbuilt as Ember's "phone" question. No `Trie.Proof`
reaches any client today. (2) A leaf decoder that refuses is a decision, so by law 2 it is Lean's
(`Codec.World.leaf`), never Rust's. (3) With Lean's decoder the premise is a theorem, not a check:
`leaf_lawfulOn : LawfulOn Leaf.Fits leaf` says every leaf the codec reads satisfies `Leaf.Fits`, and
`Leaf.Fits l → l.CellFit Cell.Fits` holds case by case (`entry (live c)` is `Cell.Fits c`; `tomb`
and `spent` are `True` on both sides). A non-fitting cell cannot come out of the decoder (a kind
read by `nat32` is below 2^32), so a runtime `Fits` test after decoding is dead code, and a plant
that "skips the check" could never go red: a vacuous plant.
**Decision.** No Rust leaf decoder and no Rust Fits check (the client keeps no protocol knowledge
beyond CODEC's table). Routed instead: CODEC proves `leaf decode b = ok l → l.CellFit Cell.Fits`,
and KERNEL states the phone's read over leaf BYTES (`deployed_head_read_sound` with the leaf
obtained by the deployed leaf decoder), so no premise about the leaf is left. Its tooth is the
build: a decoder that admits a non-fitting cell breaks the proof. When PROTOCOL builds option B,
`follow` (Lean) decodes and verifies, the client moves the bytes, and the row's plant is a forged
proof refused by name in Lean.
**Critique.** This declines the brief's literal shape (a Rust refusal with a skip-plant). If a
future phone is a non-Lean app, it must still show only what Lean decoded; that is a constraint on
the phone's build, written here so it is findable. CODEC-4 emitted `generated::cell_fits` into client/src/generated.rs
(c64bb52) on the brief's first reading; under this decision it has no Rust consumer, and an emitted
predicate nobody calls is a check that cannot go red. Whether it stays is CODEC's and ROOT's call.
**Meta-critique.** The pull was to build the asked refusal because it was asked; the codec's
`LawfulOn` theorem is what decides that there is nothing to refuse at runtime.
**Condition (ROOT, 2026-10-17).** The phone's head-read path, when it is built (after THE BAR), goes
through Lean's leaf decoder and NEVER through a Rust parse of the leaf.
**Status.** ACCEPTED by ROOT 2026-10-17. Routed: CODEC-4 proves the decode-to-CellFit lemma, KERNEL-8
states `deployed_head_read_sound_bytes` over leaf bytes, PROTOCOL-6 closes cv 01a149bf-8b34 against
the theorem; the uncalled emitted `cell_fits` is deleted (CODEC). Nothing of client/ changes.
**Closed (KERNEL-34, 5652aba).** `Receive.deployed_head_read_sound_bytes` (a reached World) and
`deployed_head_read_sound_decoded_bytes` (a reopened base) take the served leaf bytes `b` and
`Codec.Kernel.leaf.decode b = .ok lf`, with no premise about the leaf (`leaf_decode_cellFit`). The
phone shows only what that decoder returns: those two theorems are what its read cites.

## CLIENT-17 one Cargo workspace, and one dev crate for the test harness (2026-10-17, CLIENT-3; ROOT ruling, HOSTING-4's stage 2b ask)

**Decision.** The repository root holds the one `Cargo.toml` (`[workspace]`, resolver 3, members
attach, client, devtools, launcher, sandbox, listed explicitly) and the one `Cargo.lock`; the
per-crate locks and per-crate `[workspace]` stanzas are deleted; one target dir (`/target`). Owned
SHARED (GATES-2's OWNERS rows, 248fcea). `devtools/` (`nanodregg-devtools`, OWNERS CLIENT) is a
DEV-DEPENDENCY ONLY and holds what a second crate's tests would otherwise copy, nothing else:
`lean_bin(name)` / `lean_bin_in(dir, name)` (`$ND_LEAN_BIN`, else `.lake/build/bin`; missing FAILS
by name; `ND_HOST_EXE` is gone, one variable, the one gates/runs.py sets), `nd()` / `nd_supervise()`
(built once per test process from this tree into `<target>/devtools-bins`, its own target dir so it
never waits on the outer `cargo test`'s lock and is never stale; `BUILD_DEADLINE` 900 s, failing
`buildTimedOut` / `buildFailed` with cargo's stderr tail), `Supervisor::hold(child, pid_file)` (stops
by its own handle on drop, pid file while alive) and `supervise_host(nd_supervise, sock, hide, store,
args)` (host under nd-supervise with `--write STORE`, binds within 20 s or fails `neverBound`). The
API was agreed with HOSTING-4. client/tests (common's Supervisor and lean_host, real.rs's
supervise) and attach/tests (Held, lean_host) use it and their copies are deleted; launcher/tests
switch in HOSTING-4's next commit. Client tests keep `CARGO_BIN_EXE_*` for their own binaries.
**Alternatives.** (a) `ND_CLIENT_BIN` env for launcher tests: a third discovery, and a stale binary
is found silently. (b) Nested `cargo build` into the shared target dir: blocks on the outer
`cargo test`'s build lock. (c) Cargo artifact dependencies (`-Z bindeps`): unstable. (d)
`RealStore::genesis`: one caller today; it moves in when a second appears (ROOT's scope rule).
**Critique.** `nd()` builds the client a second time (into devtools-bins) the first time a
non-client test asks; that is compile work, not a copy of code. The workspace unifies versions: libc
is 0.2.190 for all (launcher's lock had 0.2.191), syn 3.0.9 as client had. `devtools` may panic: its
asserts are test failures, and no deployed crate depends on it (plant).
**Meta-critique.** I parse the root manifest's `members` line by hand in the plant rather than
adding a TOML parser to devtools; the plant breaks loudly (not silently) if the line's shape
changes.
**Plants.** devtools/tests/workspace.rs: every crate directory is a member and holds no lock or
workspace of its own; no crate depends on devtools outside `[dev-dependencies]`; a missing Lean exe
fails by name; the built supervisor runs the built host and its holder removes its pid file.
Mutations, each red: a member dropped (`notAMember`), a per-crate lock (`ownLock`), devtools in
attach's `[dependencies]` (`devtoolsDeployed`), lean_bin's existence check removed, the pid file
kept. "The workspace builds every member" is GATES-2's workspace judgement (cargo check/clippy
--workspace), landing after this.
**Status.** landed (this commit).

## CLIENT-18 the public read: a file custody's integrity depends on, but whose bytes are not secret (2026-10-17, CLIENT-3; HOSTING-4's ask for HOSTING-15)

**Decision.** `nanodregg_sandbox::custody::read_public(path, RangeInclusive<usize>) -> Vec<u8>`
reads keybroker's TLS trust anchors (PEM, public). It shares every check with `read_private`
through one private `read_checked` (not a link, a regular file, owned by the euid, length in range,
O_NONBLOCK) and differs only in the mode rule: no group or other WRITE bit and no
setuid/setgid/sticky bit (`PUBLIC_REFUSED = 0o7022`), so 0600, 0644 and 0444 pass and 0664, 0646 are
`Mode`. The bytes are not zeroized. `Refused` is unchanged.
**Alternatives.** (a) keybroker checks the anchors itself: a twin of the open-and-check sequence.
(b) `read_private` for the anchors: a 0600 anchors file works, but forbidding 0644 on a public file
is a rule with no threat behind it. (c) Accept a root-owned anchors file (a system CA bundle): that
widens who may decide what keybroker trusts beyond the operator's euid; not asked, not done.
**Ruled (ROOT, 2026-10-17): the refusal of a root-owned system bundle STAYS.** The anchors file is
operator DATA, emitted by deploy and owned by the operator (HOSTING-15's design); reading the system
bundle would widen trust to whatever the OS ships, which is what the emitted-vs-crate byte check
exists to prevent. A root-owned anchors file is `Owner(0)` by design.
**Critique.** What an anchors file protects is integrity: whoever can write it chooses whom
keybroker trusts upstream. The rule refuses every writer but the owner; it does not refuse a
directory another user can write (a rename over the file). Same as the private read, whose parent
directory is also unchecked; checking the parent chain is a separate, wider decision.
Superseded by CLIENT-19 (ROOT's ruling): both reads now check the parent chain.
**Meta-critique.** I refactored the private read into the shared checker in the same commit; the
ten mutations (seven old, re-run on the refactor, three new) are the evidence that it still refuses
what it refused.
**Plants.** sandbox/tests/custody.rs `a_public_file_is_refused_writable_by_others_and_by_the_shared_checks`.
Mutations, each red: the public write-bit rule removed, the special bits dropped from
`PUBLIC_REFUSED`, the private read given the public rule; and the seven of CLIENT-15, re-run.
**Status.** landed (this commit).

## CLIENT-19 the custody reads check the directory chain, sshd's StrictModes rule (2026-10-17, CLIENT-3; ROOT ruling on CLIENT-18's flag)

**Decision.** `read_private`, `read_public` and `check_private_dir` first canonicalize the path's
parent and refuse `Dir(path)`, naming the offending directory, unless every directory from it up to
`/` is owned by the euid or by root and has no group or other write bit. A sticky world-writable
directory (`/tmp`) is refused too, as sshd refuses it. The file is then opened through the canonical
parent, so a symlinked component swapped after the check cannot redirect the open. `nd --init`
makes the workspace 0700 whatever the umask. Tests make their scratch with
`devtools::scratch(name)` (`$ND_SCRATCH`, else `$HOME/.cache/nd-t`, 0700) and `devtools::mkdirs`
(0700), because `/tmp` and a umask-002 target dir would both be refused. keybroker names the new
refusal `keyFileDir` / `anchorsDir` (HOSTING-5).
**Why.** A directory another user can write, or another user owns, lets them rename a different
operator-owned, correctly-moded file into place: not a leak but a confusion of WHICH key signs or
which anchors are trusted, a custody defect. Greenfield: no holding or workspace has users.
**Alternatives.** (a) Accept root-owned sticky directories (`/tmp`): the sticky bit stops others
renaming OUR entry, but a stricter rule costs only the test scratch location, and sshd's is the rule
operators already know. (b) Check the lexical path's directories: a symlinked component lives in a
directory the canonical chain does not contain.
**Critique.** This tightens what any process may read (CLIENT-13's custody records and HOSTING's
key file included): on hbox, where umask 002 leaves the /tank tree group-writable, a key file under
it is now refused `Dir`. That is the intended direction. The plant for a foreign-owned parent finds a
real directory of another non-root user on the box and FAILS if there is none; it never skips.
**Meta-critique.** The swap-after-check race on the canonical chain itself needs a writer of a
checked directory, which the check refuses; I did not plant the canonical-open half (it is a race,
not a deterministic mutation) and say so.
**Plants.** sandbox/tests/custody.rs `a_parent_writable_by_others_or_owned_by_another_user_is_refused_dir`
(0770, 0707 and 1777 parents; /tmp; a foreign user's directory; both reads and check_private_dir);
client/tests/real.rs asserts `nd --init` made the workspace 0700. Mutations, each red: the chain
check skipped, its owner condition removed, its write-bit condition removed, nd's workspace mode
0777 (the umask leaves 0775, and custody then refuses it).
**Status.** landed (this commit).

## CLIENT-20 `Policy.connect`, and a file grant is a connect grant on Linux (2026-10-17, CLIENT-3; HOSTING-17 §5, ROOT rulings)

**Finding (measured 2026-10-17 on hbox, nd-bwrap = bubblewrap 0.10.0).** Under nd-bwrap
(`--unshare-all`, no network namespace shared) a confined child connects to a PATH unix socket whose
directory is in its view, and gets ENOENT for one whose directory is not. So on Linux every `read`,
`write` or `exec` directory is already a connect grant to every socket inside it, then or later. The
probe was a scratch integration test, not landed: in a `devtools::scratch` root, a listener bound at
`d/s.sock` and another at `o/s.sock`; a python child (`python3 -I -c` connecting to each argv path)
launched by `sandbox::command` with `read = [d, /usr]`, `exec = [/usr]`, `hidden = [ws]` printed
`d/s.sock CONNECTED` and `o/s.sock ERR FileNotFoundError`; with `read = [/usr]` both were
FileNotFoundError. macOS `(deny default)` refuses unix connects not allowed (unrun since the hbox
move). It is the shape of `EXEC_FILTERED`: bwrap filters by mount, not by operation.
**Decision.** (1) `CONNECT_FILTERED` (Linux false, macOS true), a platform fact with its plant and
a tcb row. (2) `Policy.connect: Vec<PathBuf>`, at most `CONNECT_MAX` = 2 (`ConnectTooMany`), each
entry checked at resolve: `lstat` a socket (`ConnectLink`, `ConnectNotSocket`); EITHER owner = euid
at exactly 0600 OR owner ≠ euid, group = egid at exactly 0660 (`ConnectOwner`, `ConnectMode`; the
egid, never a supplementary group); every ancestor owned by root, the euid or the socket's owner,
no group/other write (`ConnectDir`, the CLIENT-19 walk with one more admitted uid). Linux
read-only binds the socket's PARENT directory (a restarted server's new socket is the one seen);
macOS allows `network-outbound` to that `path-literal`. Connect directories count as allowed paths
for `Exposed`. (3) `ConnectOverlap`: a connect directory under or containing any read/write/exec
entry (or the program) is refused, so a socket directory is never also a file grant. (4)
`SocketInGrant(path)`: each read/write/exec entry not under the platform floor is walked (links not
followed) and a socket in it at launch is refused; a directory in it that cannot be listed is
`GrantUnlisted` (a socket in it could be reached by name). Write roots are scanned too (HOSTING-6:
a grain's own vol socket refuses that grain's next launch; the controller's crash-loop bound reports
it). (5) For keybroker (HOSTING-17): `custody::check_shared_dir` (ours, exactly 02710, chain passes;
returns its gid) and `custody::peer_cred` (`SO_PEERCRED`; macOS `Unsupported`, declared).
**What it cannot see.** A socket bound under a read/write/exec root AFTER launch: (3) and (4) are
launch-time. That is the tcb row's words, and HOSTING's placement keeps SOCKDIR (`/run/nd-broker`)
on its own root, never under or around a grain root (grain-launch refuses a BROKER under or around
ROOT by name, HOSTING-6). The floor (`/usr`, …) is not scanned: a socket there is in every child's
view regardless of policy.
**Alternatives.** Bind the socket inode (dead after a server restart, HOSTING-17 §4); a seccomp or
Landlock connect filter (the real lift of `CONNECT_FILTERED`; Landlock scopes abstract sockets
only today); documenting the overlap instead of refusing it (ROOT: refuse).
**Critique.** `CONNECT_MAX` is the sandbox's own bound, not emitted from Lean: the plan's list is
Lean's, and a longer one is refused by name at launch rather than mirrored. The scan walks every
non-floor grant at each launch; its cost is the grant's entry count (a Store or a package dir).
`ConnectOwner`'s ACCEPTING branch (another uid, group = egid, 0660) needs a second uid and is
DECLARED UNRUN on hbox; its refusing branch is planted with a real foreign socket found on the box
(hbox: root:docker /run/docker.sock), failing if none exists.
**Plants.** sandbox/tests/connect.rs (7): reached vs sibling ENOENT; a third entry; mode 0666 and
0660-of-ours, a regular file, a link, a group-writable ancestor; a foreign socket; overlap three
ways; a socket in a read and a write grant; CONNECT_FILTERED (a socket bound under a read grant
after launch is reached exactly when not filtered). sandbox/tests/custody.rs: shared dir, peer
cred. Mutations, each red: the count check, the link check, the socket check, the mode check, the
owner branch, the ancestor walk, the overlap, the scan, the Linux directory bind, CONNECT_FILTERED
flipped, the shared-dir mode.
**Status.** landed (this commit).

## CLIENT-21 nd-supervise `--group GID`: a socket another uid of one group may connect to (2026-10-17, CLIENT-3; ROOT ruling on HOSTING-17 §7, OPS-3, HOST-10)

**Decision.** By default nd-supervise binds its socket 0600, owner-only, as before. With `--group GID`
(a NUMERIC gid: OPS-3 renders it from the install step's `getent group nd`, operator data, never an
NSS lookup in Rust), the socket is bound 0660, and nd-supervise refuses at launch
(`refusedAtLaunch`) unless the socket's directory passes `custody::check_shared_dir`: owned by the
euid, mode exactly 02710, a trusted parent chain (CLIENT-19), and its group equal to GID. The refusals
are named `sharedDirRefused: <Refused>` (wrong mode, owner, link, missing directory, untrusted
chain) and `groupMismatch`. The checks do not depend on the argument (OPS-3), so a wrong ND_GID is
refused, never served. The socket is created under umask 0177 and widened only after the checks;
the umask is restored before the child starts, so the child inherits the operator's umask. The
setgid directory gives the socket its group, so no separate check of the socket's gid is made (it
would be unreachable, and an unreachable check cannot go red).
Path (HOST-10): `/run/nd-follow/<label>/follow.sock`, with `/run/nd-follow` and every `<label>`
02710 nd-hosted:nd, created by OPS-3's tmpfiles. nd-supervise never creates a directory; a missing
one is `sharedDirRefused`. The driver is the existing `nd` running as nd. Principle (ROOT): the
trusted side initiates to the less-trusted side, never the reverse.
**Alternatives.** A group name (needs NSS, or a hand parse of /etc/group: a twin of libc); a mode
argument (it would admit 0666); binding a shared directory the supervisor creates (it would then
decide placement).
**Critique.** The accepting case runs as one uid on hbox: the 0660 socket is reached by a peer in the
group only in the deployment (nd, as a second uid). On one uid the plant checks the mode and group
bits, not a cross-uid connect: DECLARED UNRUN.
**Plants.** client/tests/supervise.rs `a_group_socket_binds_0660_only_in_a_shared_directory_of_that_group`:
a 02710 directory binds 0660 with the directory's group; another group is `groupMismatch`; a 0710
directory and a missing one are `sharedDirRefused`; the control (no `--group`) binds 0600.
Mutations, each red: the directory check skipped, its group comparison ignored, the group mode
0600, the default mode 0660.
**Status.** landed (this commit).

## CLIENT-22 the observer record: custody that signs read envelopes only (2026-10-17, CLIENT-3; ROOT ruling, HOSTING-17 §7, PROTOCOL-7)

**Decision.** The nd-hosted follower is its own OBSERVE-ONLY member (the operator's member grants
`world MEMBER observe`, KERNEL-20). Its key is a custody record `ws/observer = current ‖ next`
(the SameRecord layout under another name), made by `nd --init-observer`, owned by nd, read
under the custody checks and the StrictModes chain (CLIENT-19). `Custody::open` refuses `Shape`
unless exactly one of `seed`, `keys`, `observer` is present, so the mode is a property of the
RECORD, never an environment switch that a missing variable could widen. An observer custody signs
only a message that starts with `generated::ENVELOPE_DOMAIN` (emitted from `Protocol.domEnvelope`,
never a Rust literal); any other message, and every `precommit` and `signNext`, is refused
`envelopeOnly` (`CustodyRefusal::EnvelopeOnly`, PROTOCOL-38), which follow receives as a refused
custody result. nd's own failure now exits `command_exit::CLIENT` (52), never 2, which is follow's
`uncertain` (PROTOCOL-7's find): a timer can tell "nd could not run" from "the append is uncertain".
**The fence (proved since 1ed7867).** Every message a member key signs begins with its own
domain (KERNEL-42 / PROTOCOL-39): a call's is `callMessage = domCall ‖ unsignedBytes`. So the prefix
fence is exact, with no hash premise: `Nanodregg.Protocol.call_not_envelope : domEnvelope ++ r ≠
X.callMessage u`, `possession_not_envelope` and `whoami_not_envelope` (Protocol/Proofs/Domains.lean)
say an observer never signs a call, a possession proof or the whoami probe. Before 1ed7867 the fence
was prefix-only, holding up to cSHAKE preimage resistance (a call's message carried no domain,
CODEC-6), while the kernel's observe-only grant was the authority (the key cannot write regardless):
the gap was in the second fence, never the first. Both fences are planted through the real Host
(client/tests/real.rs): observe-only, a write is refused `noGrant` by Lean before custody is asked;
granted `mutate` on the object, the sealed record still refuses to sign it, `envelopeOnly`, and
nothing commits.
**Alternatives.** A keyless driver (built, measured, dropped: every catch-up log page needs a signed
read envelope, PROTOCOL-27/29); `ND_CUSTODY=envelope` (an env switch widens when dropped); a length
check (a call can be 155 bytes too; with the theorem it would be a second fence that cannot go red).
**Critique.** Observer rotation is refused in v0 (cv task 01a14adf-8582); the record holds `next`,
so the rotation step comes later with no shape change.
**Plants.** client/tests/custody.rs `an_observer_signs_read_envelopes_only` (an envelope-prefixed
message signed and verifying; a call's bytes, the domain minus its first byte and the empty message
refused; precommit and signNext refused; the record unchanged; an observer beside keys is Shape; a
0640 record is refused by the custody checks); client/tests/real.rs: nd's own failure exits
CLIENT. Mutations, each red: the prefix check, the precommit guard, the signNext guard, the record's
mode flag, the exit back to 2.
**Status.** landed (this commit); the theorem-backed plant follows the flag day.

## CLIENT-23 an observer joins like any member, then is sealed by one rename (2026-10-17, CLIENT-3; ROOT ruling (A))

**Problem.** An observer cannot enroll itself: `nd init SPONSOR` signs `whoami` and a possession
proof, and envelope-only custody refuses both (correctly: they are other domains).
**Decision (ROOT, A).** The observer starts as a full one-record custody (`nd --init-hosted`,
`ws/keys`), joins like any member (`nd init SPONSOR`; the operator `enroll`s it and grants
`world MEMBER observe`), and is then sealed: `nd --seal-observer` RENAMES `ws/keys` to
`ws/observer` (renameat NOREPLACE, then the directory synced), once, durably, irreversibly. The
seal is a rename, not a copy: no second key material ever exists (the plant checks the inode). The
record's `next` is kept, so a later observer rotation (cv 01a14adf-8582) needs no shape change.
Refused by name: `exists` when an observer is already there (a second seal), `rotationInFlight`
while a rotation is armed or a pending key is minted, `shape` for any custody that is not one
`keys` record (a member's separate custody). OPS-3's RUNBOOK §2b enrolment gains the seal as its
last line.
**Alternatives.** (B) the observer also signs whoami and possession: the fence wider for the
record's whole life, for a one-time need (ROOT: no).
**Critique.** Between `init` and the seal the record is a full custody; the window is the operator's
enrolment, on the operator's box, before the follower runs.
**Plants.** client/tests/custody.rs `a_joined_record_is_sealed_as_an_observer_by_one_rename`
(control: unsealed it signs a call; sealed: same inode and bytes, keys kept, a call refused, an
envelope signed; a second seal `Exists`; armed `RotationInFlight`; pending minted
`RotationInFlight`; separate custody `Shape`); client/tests/real.rs: the whole path through the real
Host (init, enroll, grant observe, its own `host follow`, seal, `sync` and `read` served, the two
fences above). Mutations, each red: the prefix check (real), the armed check, the pending check,
the exists pre-check, the shape check.
**Status.** landed (this commit).

## CLIENT-24 `nd --stdio`: a hosted resident's commands through nd-supervise, a surface it cannot widen (2026-10-17, CLIENT-3; HOSTING-20, ROOT rulings, PROTOCOL-40)

**Decision.** `nd --stdio WORKSPACE FOLLOW_SOCK HOST_SOCK` is nd-supervise's child serving one
resident over the mux child wire: each request `follow_op::COMMAND ‖ layout::Command{argv}` is one
nd command, each reply `status::OK ‖ layout::CommandReply{exit, stdout, stderr}` (PROTOCOL-40). The
places are nd's argv at start (the sandbox clears the environment); the peer sends argv words only.
The surface is the MODE's property, never the peer's:
(a) argv[0] must be in `generated::STDIO_VERBS` (Lean's `Verb.onStdio`, a total match: every World
verb but init, rotate, adopt; `Command.mem_stdioWords_iff`), else `refused notOnSurface VERB`
before follow sees anything: flags (`--keys`, `--init`), custody words, an `ND_WORKSPACE=…` word;
(b) a request that is not `COMMAND ‖ Command` is `refused undecodable`;
(c) the custody it opens (`stdio::custody`) refuses `precommit` and `signNext` as `noRotation`
(CustodyRefusal 9), a second fence behind (a);
(d) nd-supervise `--peer UID` (with `--group GID`) admits only a connection whose `SO_PEERCRED`
is (UID, GID); any other is closed `peerRefused` before a frame is read or a connection id is spent.
It runs CONFINED (HOSTING-7, ROOT): nd-supervise `--write WORKSPACE --exec ND --connect HOST_SOCK
--connect FOLLOW_SOCK` (connectMax = 2); nothing else is visible, provider keys included. nd-supervise
gains `--connect` for that. **Corrected premise (ROOT accepted):** a resident cannot make nd read a
file: `install TEXT` takes the package text inline, and nothing in nd or follow resolves an argv
word against the file system (checked on main). The class "no path-valued argument" is true by
construction; the canary plant keeps it so. The socket (HOSTING-7): `/run/nd-member/<id>/nd.sock`,
0660 in a setgid 02710 nd:nd-hosted directory, `--group nd-hosted --peer <nd-hosted uid>`.
**Alternatives.** An unconfined trusted child (wider than needed); an env switch for the mode (a
dropped variable would widen it); a Rust verb list (a twin of Lean's; a new verb would be on it by
default).
**Critique.** Requests are served in order, one at a time (one resident, one socket); a slow command
delays the next. nd's own failures inside a request answer exit CLIENT with `nd: …`, as nd does.
nd-supervise's `bind` and the stdio argv now live in the library (the two binaries' ceilings hold).
Found on the way: a stale `host` exe answered `badResult` to the new custody refusal tag, until
rebuilt; the client's Lean-driving tests are now gates/runs.tsv rows so the judge rebuilds first.
**Plants.** client/tests/stdio.rs (through the real Host, nd --stdio confined under nd-supervise):
a read and a granted write served; seven off-surface argvs refused `notOnSurface`; another op and
non-Command bytes `undecodable`; a canary file named as `install`'s text never read; with the
surface widened in process to `rotate`, custody refuses `noRotation` and mints nothing.
client/tests/supervise.rs: `--peer` own uid served, another uid closed `peerRefused`, `--peer`
without `--group` refused. client/tests/custody.rs: a stdio custody signs, never precommits or
rotates. Mutations, each red: the surface check, the op check, the peer check, the custody guards,
`--connect` mapped to read, the stdio custody opened without `refusing_rotation`.
**Status.** landed (this commit).

## CLIENT-25 · `declined` is not final: the attempt stays OPEN (2026-10-18, written by PROTOCOL-8 with ROOT standing in for CLIENT; KERNEL-44/47, PROTOCOL-41; landed in the refusals day)
**What changed.** The Host now has two kinds of refusal for a submit (PROTOCOL-41):
- `refused` (1) is FINAL: the refusal is recorded in the World, or was recorded before (the name is the recorded one), or the call's window has passed.
- `declined` (5, payload NAME) is NOT final: an unauthenticated code, an early `outsideWindow`, or `refusalBudget`. Nothing is recorded, and the same bytes may still be admitted later. Example: a call signed with the precommitted next key is `unknownKey` until the rotate.

The emitted table carries it: `status::DECLINED`, `command_exit::DECLINED` (53, restart class) and `attempt::Seen::Declined` / `Action::Declined`. In `attempt::next`, (submit, declined) gives Declined and (lookup, declined) gives BadReply.

The client half, all mechanical from the table:
- `run::Table.declined`.
- `run::settlement` classifies DECLINED as `Settlement::Declined(reply)`, and that maps to `Seen::Declined`.
- `Attempt::drive` on `Action::Declined` returns the in-memory `State::Declined { sends, reply }`. It writes NO settlement file, so on disk the attempt is exactly `Uncertain` (its `sent.*` markers) and the next run looks it up.
- `run::run`'s submit arm resumes follow with (DECLINED, reply), and follow prints `declined NAME` with exit 53. An armed rotation stays armed: custody is not settled.

**Plants.**
- `client/tests/attempt.rs`:
  - `declined_leaves_the_attempt_open_and_the_next_run_looks_up`: one send; no settlement file; reloads as `Uncertain { sends: 1 }`; the next run's only request is a lookup of the same bytes.
  - `a_declined_lookup_is_a_bad_reply`.
- `client/tests/run.rs`: `a_declined_rotation_submit_stays_armed_and_open`. One submit, no lookup. Follow is told declined. Custody is not advanced and is still armed. The attempt is Uncertain on disk.

**Why not reuse `uncertain`.** The Host can say the call did not commit and is not recorded, so `uncertain` would be a lie about what it knows. Treated as uncertain, the client would also look it up and resubmit inside the same run, up to `sendsMax`, learning nothing new.

**Critique.** An open attempt for a deterministic refusal (badSignature) stays open until its window passes and the lookup answers `expired`. A timer re-running it spends one lookup per run. That is bounded, but it is waste. CLIENT-5 may want `nd` to say so.

**For CLIENT-5.** Read this first. Nothing else in the client changed.

## CLIENT-26 · `nd --join`: a member's own World from an invitation its sponsor signed (2026-10-18, CLIENT-5; PROTOCOL-42/44, ROOT rulings on (a)–(c))
**Decision.** `nd --join KEY_FILE INVITATION STORE /ABS/HOST` replaces the deployed client's trust on first use: RUNBOOK §2's reproduction of the writer's genesis with the writer's nonce.
- **Two channels, one per trust level.**
  - The sponsor's public KEY is a FILE (hex, one optional newline), read by `custody::read_public` under the StrictModes chain (CLIENT-19). It is the trust root, a person's word, so it must sit where no other uid could have swapped it.
  - The INVITATION is a hex ARGUMENT. It is untrusted until Lean's `Invite.accept` checks it, so it may arrive relayed or pasted, even through the Host.
  - Never one blob: a blob carrying both would let whoever relays the invitation also choose the key.
- **nd decides nothing.**
  - `host join STORE INVITATION KEY` runs `accept` and writes STORE only when it passed (`join_genesis_iff`).
  - nd maps host's exit by the emitted tables:
    - `host_status::INVITE_REFUSED` (44) → `command_exit::REFUSED`, host's `refused inviteRefused NAME` passed through;
    - any other non-zero → `command_exit::CLIENT` (52), host's stderr in the message;
    - nothing is kept on either.
  - Then `init SPONSOR` (the id `host join` printed) is follow's. It signs whoami and possession and prints `join HEX`.
- **One spawner.** `join::confined` is the only way nd starts `host`. It is used by `host join` and by init's one-shot follower. Shape:
  - its policy is the member follower unit's own flag words (`--write STORE --exec HOST --hide WS [--hide HOLDING]`);
  - those words are read by `Policy::list`, the parser nd-supervise reads its argv with (moved into sandbox/ and shared, not re-stated);
  - it launches through `nanodregg_sandbox::command`, the same mechanism nd-supervise uses.
  - A member follower's policy still comes from Rust and the unit text rather than a Lean plan. Hosting's grains have one; cv 01a14df6-0647.
- **init's follower.** `host follow STORE 0^32 0^32` runs one-shot on a socket pair, speaking the mux child wire with connection 0. Each direction is bounded by `replyMsMax`.
  - init needs no World (`Machine.start`) and no Self, so the placeholder ids are never read. The rows use the same stranger placeholder.
  - A Host step asked during init is an error (`NoHost`).
  - Follow exits on stdin EOF.
- **What the workspace keeps.** Two non-secret files, 0600, `create_once`:
  - `invitation`, as received;
  - `input`, the genesis inputs `host join` printed (PROTOCOL-44). Founders keep `host genesis`'s line with `nd --input HEX`.
  Both are re-read under the chain rule (`read_private`):
  - bare `nd invite` becomes `invite <input>`;
  - `nd adopt KEY_FILE` becomes `adopt <invitation> <key>`.
  Explicit hex forms pass through unread. A workspace that has joined refuses a second `--join` (`invitation: exists`) before host runs.
- **Off the stdio surface.** `--join`, `--input`, `invite` and `adopt` are not in STDIO_VERBS. stdio's argv is decided before any of this (notOnSurface), and nothing on the stdio path reads an argv path (CLIENT-24's canary stays).
- **Deleted.** `adopt STEPS DIGEST` and its out-of-band pin are gone. The client held only the stdio plant's argv for it, now `adopt INVITE KEY`'s shape.

**Plants** (`client/tests/join.rs`, row `cargo:client:join`, the real host over sockets; a filtered target):
- a forged invitation (one signature nibble) is `refused inviteRefused pinMismatch`, exit 1, with workspace and Store unwritten;
- a key other than the sponsor's is `notSponsor`, likewise;
- a key file under a 0770 directory is `key file: Dir(…)`, exit 52, likewise;
- the honest join: origin = the sponsor's, `sponsor` = the founder's id, `input` = genesis's; both kept 0600; a second join is refused `exists`;
- enrolled and granted, the joiner's write is served and the founder reads it;
- the joiner's bare `invite` is served from its kept input;
- a kept invitation widened to 0640 is `invitation: Mode(…)`, and a 0770 workspace is `Dir(…)`;
- a thin joiner's `nd adopt KEY_FILE` reaches Lean with the kept bytes: the wrong key is `notSponsor`, the sponsor's is `baseMoved` (residue 1).

Mutations, each red: kept-file read unchecked; key-file read unchecked; the exists check removed; keeping before `host join`; refusal stderr dropped; 44 mapped as CLIENT.

**Residue.**
1. The deployed `host` has no seal act. The writer seals only at its cadence (1 MiB), and the rows' `seal` is a harness checkpoint, so a served real thin adopt needs the inviter's tip to land on a cadence base. PROTOCOL-9 records it in PROTOCOL-42's critique; until it lands, deployed thin joining is unusable and full joining (`host join`, then fold) is the path.
2. The `baseMoved` hint ("ask your sponsor for a fresh invitation") is follow's rendering (PROTOCOL-45), not nd's.
3. A failed init after a successful join leaves a joined Store and the kept files. The recovery is to empty STORE, remove the two files, and join again. No refusal here can come from the join itself.

**Critique.**
- nd now execs `host` itself (until now only nd-supervise did). It is confined, but it is a second caller of the spawner.
- The flag-word spelling inside `confined` is ceremony to share one parser. It shares the parser, not the policy's source: the follower's policy should be a Lean plan.
- The placeholder follower is a real follower process for two signatures.
- The client half of a served thin adopt cannot be driven through the real host. The plant stops at Lean's `baseMoved` under the right key. ROOT routes the fix (a `host seal` verb, or the rows' seal as a real act) to HOST-12 and PROTOCOL-9.

**Meta-critique.** I first proposed exec'ing host directly and called it "the supervisor path". ROOT read that as a second spawner and refused. The correction showed that the premise ("nd already spawns follow on pipes") was false in both directions: nd spawned nothing, and the one spawner is the sandbox's.

## CLIENT-27 · a settlement is the member's word: the attempt store settles a call only from its own follow's receipt; `absent` with a live window is OPEN; a landed rotation reads through its incoming key (2026-10-18, CLIENT-6; PROTOCOL-46 with PROTOCOL-10, ROOT rulings)
**The defects (read, not assumed).**
1. `run::settlement` classified the Host's reply by its status byte, `attempt.rs` wrote `committed` / `not-committed` holding the Host's reply verbatim, and `reconcile` handed that to `custody.settle`. A Host that says `ok` for an unlanded rotation advanced custody to a key the World never installed; one that says `refused` for a landed rotation dropped the pending key and kept a revoked one. Either way the member was locked out on the Host's word.
2. `Attempt.next`'s terminal `absent` ("nothing committed; running the command again is safe") was false while the call's window is live: any relay holding the signed bytes can still submit them, and a re-run signs a NEW call, so both commit.
3. Found while building (CLIENT-6, ROOT ruled): PROTOCOL-46 as proposed would have made (1) WORSE for a rotation. `confirm` runs follow `receipt CALL`, whose catch-up signs a read envelope with custody's current key, and `Envelope.check` (Protocol/Envelope.lean) admits only the World's current key. In `reconcile` of a rotation that COMMITTED, custody is still on the old key, so the Host refuses `unknownKey`, the receipt never builds, the attempt stays open and the rotation stays armed forever: a lockout with no way out (the old code at least advanced on the Host's `ok`).

**Decision.**
- **The Host hints; follow settles.** `submit` / `lookup` replies are classified (`run::hint`) only to steer the emitted loop. Every end the Host claims (`ok`, `refused`) is `confirm`ed, and a lookup's `absent` with no send left is `probe`d, both as `follow receipt CALLHEX` (`run::receipt`, the same step loop, which may only sign and read). `attempt::Receipt::read` takes exactly the three lines (`receipt`, `head`, `settle VERDICT`) and names the verdict by the generated `settle_seen`; nothing here classifies.
- **The settlement file is `settled`**: follow's three lines verbatim (the receipt and the head it was checked against: re-checkable and quotable later), written only on the table's `committed` / `refused` (with `expired`), which it names only after a `confirm` / `probe` whose verdict was that. A directory holding any other file (`committed`, `not-committed`, anything) refuses to load `Inconsistent`, as does a `settled` that is not a final verdict: the old layout is refused, never reinterpreted (no attempt dirs exist outside tests).
- **Every other end is OPEN on disk** (`State::Open { end, payload }` in memory, `Uncertain` on disk): `declined`, `open` (absent, window live), `contradicted`, `uncertain`, `badReply`. The terminal `absent` is gone; `AttemptError::Ended` and `RunError::Uncertain` are deleted.
- **follow is told the table's end**: the submit step resumes with `Action.code ‖ payload` (the verdict text for committed / refused, the refusal name for declined, `HOSTSAID FOLLOWSAID` for contradicted), and the Machine maps it to CommandExit (open 54, hostContradicted 55; absent 50 deleted, not reused).
- **Custody settles only from the receipt.** `custody.settle` is called only on `State::Settled` (a `settled` file that was just written from follow's verdict). A rotation whose attempt ends `open` or anything else stays armed. In `reconcile`, `contradicted` ends the run with `command_exit::HOST_CONTRADICTED` and `hostContradicted HOSTSAID FOLLOWSAID (attempt DIR)` on stderr, the rotation still armed; `open` leaves it armed and the command goes on.
- **`signIncoming` (Step code 6; PROTOCOL-10's Machine re-signs an envelope refused `unknownKey` ONCE with it).** `Custody::sign_incoming` signs ONLY a message beginning with `ENVELOPE_DOMAIN` (PROTOCOL-39: never a call), ONLY while a rotation is armed (`notArmed`), with that rotation's incoming key (also after an interrupted advance), naming (incoming, pending); `nd --stdio` custody refuses it `noRotation`. CLIENT-13 is amended to match.

**Why the incoming key may sign envelopes.** It is the narrowing ROOT ruled; widening `Envelope.check` at the Host to admit a precommitted next key would let a key read before its rotate lands, at the trusted side. Here the key reaches nothing new: the holding is already read in `reconcile` to settle, and the signature is over a read envelope. A hostile Host that refuses `unknownKey` falsely gains only an envelope signed by a key whose public half it already holds (the rotate call names it). What settles is still the member's own fold of the pages: a Host that accepts the incoming key while the rotation did not land must still serve pages that fold to a World without it, so the verdict is `open` / `expired`, never `committed`.

**Plants (each mutation red).**
- `client/tests/attempt.rs`: `a_host_ok_is_confirmed_and_the_settlement_is_follows_receipt`; `a_host_ok_for_an_absent_call_is_contradicted_and_stays_open`; `a_host_refused_for_a_committed_call_settles_committed`; `absent_with_sends_exhausted_and_a_live_window_stays_open` (then `expired` after the window, final); `lost_reply_is_uncertain_and_only_looked_up` (with a lost confirm); `only_this_layout_loads` (gap, an old `committed` file, a non-final or garbled `settled`); `a_receipt_reads_only_as_three_lines_with_a_named_verdict`; the declined / badReply pair re-cut.
- `client/tests/run.rs`: `a_host_ok_for_an_unlanded_rotation_is_contradicted_and_custody_stays_armed`; `a_host_refused_for_a_landed_rotation_settles_committed`; `a_contradicted_rotation_submit_is_handed_to_follow_and_stays_armed`; **`a_landed_rotation_is_confirmed_through_the_incoming_key`** (defect 3: a follow+Envelope.check model that admits only the World's key); `a_second_unknown_key_ends_the_confirm_uncertain` (once, never a loop).
- `client/tests/custody.rs`: `an_armed_rotation_signs_read_envelopes_with_its_incoming_key_only` (notArmed before arming, envelopeOnly for calls, the incoming key, after an interrupted advance, notArmed after settle); the stdio custody refuses it `noRotation`.
- `client/tests/run.rs`: `a_receipt_not_ok_or_asking_to_rotate_settles_nothing` (a receipt that does not exit ok, or asks custody to precommit inside an attempt, is no answer; nothing minted).
- `client/tests/roundtrip.rs`: the python stand-in follow answers `receipt` with three lines; `settled` holds them, and follow is told `Action.code ‖ verdict`.
- `client/tests/real.rs`: the real rotate now confirms through the incoming key against the real Host; a write through a Host proxy that answers its submit `refused` settles committed, `settled` holding follow's three lines.
- Mutations, all red (`logs/client6-mut.py`, 11): M1 the store settles on the Host's status byte; M2a/M2b custody settles from the Host's reply (submit step / reconcile); M3 the terminal `absent` restored; M4 `sign_incoming` signs with the current key (red in custody, run AND the real round trip); M5 no envelope fence; M6 no armed check; M7 stdio custody signs incoming; M8 an old layout loads; M9 a receipt not exit-ok is read; M10 a nested receipt may rotate.

**Critique.**
- Every final settlement costs one follow catch-up, and an absent call is final only after its window (at most `windowMax` heights). Before that the member sees `open`, which is the truth, but a member that wanted "it failed, try again" now waits a window. A cancel step (PROTOCOL-46 (c)) is KERNEL's to propose.
- `contradicted` in `reconcile` stops every command until the rotation settles or the Host stops lying. That is deliberate (a member should not keep acting through a Host its own fold just contradicted), but a Host that lies once and then answers honestly still costs one stopped run: the next run looks up again and settles.
- `reconcile`'s stderr line (`hostContradicted HOSTSAID FOLLOWSAID (attempt DIR)`) is the one line nd prints itself; the names are the emitted `Seen::name`, the word `hostContradicted` is spelled in Rust (the exit's name is not emitted). The submit-step contradiction is printed by the Machine.
- The real round trip proves the incoming-key retry and the overruled `refused` against the real Host; the lying `ok` for an unlanded call is shown only against stubs (making a real writer hold back a call it answered `ok` needs a Host fault, which is PROTOCOL's `lieLookup` row).

**Meta-critique.** I found defect 3 by reading `Envelope.check` before writing `confirm`, not by a test: every stub I would have written signs with whatever key the test chose, so the stubs would have been green over a permanent lockout. The `EnvelopeFollow` model in run.rs exists to make that class visible, and it is still a model: the real Machine's retry is checked only by the real round trip's rotate.

**Size.** client library 2342 → 2495 (ceiling 2350; asked ROOT for 2500 with the breakdown: attempt +49, run +72, custody +33, table +2).

## CLIENT-28 · a connection is one fd with one end: the supervisor gives back what each connection held, and `full` bounds its fds (2026-10-18, CLIENT-7; PERF-1 FINDING 1, ROOT rulings)
**The defects (verified at source, then measured before the fix).**
1. **The leak.** `write_loop` held an `Arc<Conn>`, and `Conn` held the writer's only `SyncSender` and the writer's own `JoinHandle`. When a peer left, `end(id, None)` sent nothing, so `rx.recv()` never returned. The writer thread stayed blocked for good with both `try_clone`s of the stream (its own and `Conn.stream`): two fds and one thread per connection. A `replyWriteFailed` close whose `Last` frame could not be queued did the same. Measured with the real `nd-supervise` from `/proc/PID`: (10 fds, 4 threads) after a warm connection, then (410, 204) after 200 connections that asked and left. PERF-1 saw +252 fds over 120 commands. Near RLIMIT_NOFILE 1024 the `try_clone` failed, and `accept` dropped the connection with `else { continue }`: no frame, no count, so nd saw EPIPE on its first write.
2. **The bound bounded nothing (ROOT condition 1).** `full` compared `connections_max` with the routing map. A connection leaves the map in `end`, before its writer and its fds are gone, so `CONNECTIONS_MAX` (Lean's 64) put no bound on the supervisor's fds or threads. CLIENT-14's "≤ 2·64 + accept" threads was false until this commit.

**Decision.**
- **One fd per connection.** `Conn` owns the accepted stream. The reader (`forward`) reads `&c.stream`, the writer writes `&c.stream`, and `end` shuts it down. There is no `try_clone`, so the silent `else { continue }` has nothing left to guard and is gone. Read and write timeouts are separate socket options, and `shutdown` applies to the socket, so sharing one fd changes nothing the clones did.
- **`end` takes the writer's sender** (`out: Mutex<Option<SyncSender>>`). The writer drains what is queued (at most one reply and the close, each write within `reply_write`) and returns on `Last` or on the closed channel. `route` finding no sender drops the reply, like any reply for a gone connection.
- **A connection counts until its fd closes.** It is counted when it is admitted and released in `Conn`'s `Drop`. The fd closes in that same drop, once the routing table, the reader, the writer and any in-flight `route` have all let go. `accept` refuses `full` against that count. The name is Lean's existing `CloseReason.full`. ROOT ruled that a second name (`tooManyPeers`) would be a twin of the same bound.
- **The static bound (law 4):** `MuxLimits::fds_max() = 6 + connections_max + 1`: stdin, stdout, stderr, the listener and the child's two pipes; one fd per counted connection; and the one connection accepted only to be answered `full`. Threads: main, accept, and two per counted connection. Writer threads are detached by design. Each ends within 2·`reply_write` of its connection's end, and the number alive is bounded by the count. `serve` still joins the writers of the connections open when the child closes.
- **`nd-supervise` refuses at launch** (`refusedAtLaunch`, stderr `RLIMIT_NOFILE N is below the M fds it may hold`) when its soft RLIMIT_NOFILE is below `fds_max` (71 today). It never raises the limit itself.
- **An `accept()` error** has no peer to name it to: it is counted on stderr (`mux: accept failed (K so far): E`) and paced by `reply_write`. Before, it was a silent `continue` that would spin on EMFILE/ENFILE.

**Measured after (hbox, the same plant).** (6, 2) before; (6, 2) after 200 connections; (70, 130) with 64 open, under a bound of 71; one more connection is answered `full`; (6, 2) after all of them end.

**Plants.** `client/tests/supervise.rs`:
- `every_connection_gives_back_its_fds_and_threads` (Linux, `/proc`): after 200 connections the counts equal those before; at 64 open the counts are within `fds_max` and two threads per connection; the 65th is `full`; the counts return after everything ends. It is red on the old code at (410, 204).
- `an_fd_limit_below_the_bound_is_refused_at_launch` (`ulimit -n fds_max-1`).

`client/tests/mux.rs` `a_connection_counts_until_its_fd_closes` (Linux): A leaves, but its reader is blocked handing the child its hang-up through a full pipe. B is `full`. Once the child reads, A's fd closes and C is admitted with the next id.

**Mutations, each red** (`logs/client7-mut.py`):
- M1 the writer keeps its sender. Red in `every_connection`: the leak now shows as `full` at the 65th sequential connection, because the count holds.
- M2 the count is of map entries again (ROOT condition 1). Red in `a_connection_counts_until_its_fd_closes`.
- M3 no launch check.
- M4 a silent close at the bound (the old silent `continue` in its new place).
- M5 the count is never released.

**Alternatives.**
- (a) Close the leaked handles in `end`: the thread still blocks unless the sender goes too. It is the same fix with two owners.
- (b) Raise RLIMIT_NOFILE: it postpones the leak and fixes nothing.
- (c) One epoll thread: CLIENT-14 (a) still holds.
- (d) Release the count when the connection leaves the map (the old shape): defect 2.
- (e) Exit the supervisor on an accept error, the one restart path: a transient ENFILE would then cold-restart the writer's Host. Pacing is less destructive, and the error is counted.

**Critique.**
- A connection whose peer has left still costs a slot until its writer drains: up to 2·`reply_write` against a peer that stopped reading. Under churn against a stalled peer, an honest client can therefore see `full` sooner than before. That is the bound being true, but it is a behaviour change.
- The count and the pacing are Rust's (law 2 stretch, as CLIENT-14's clocks).
- `fds_max`'s 6 is the supervisor binary's own shape, written as a constant in the mux. A seventh fd in nd-supervise would pass the launch check and could exceed the bound by one before `every_connection` names it.
- `accept`'s stderr count is not plantable without exhausting the system's file table; it is a report, not a check.
- `nd-attach` still clones per upstream connection (two fds each, at most `PEER_CONNECTIONS_MAX` = 8); its clone failure is named `unreachable`, so it is not this defect.

**Meta-critique.** PERF-1 found this by running THE BAR, not by any client plant. CLIENT-14's tests checked every NAMED end and never what an end gives back. The one plant that counts resources against the real binary is the class this adds. The fd/thread plant and the launch refusal are Linux-only (`/proc`, and the bound is judged on hbox); macOS stays declared unrun, as the other macOS halves.

**Size.** client library 2495 → 2514 (ROOT ruling 2026-10-18: ceiling 2500 → 2520); nd-supervise 118 → 127 of 160.

**Status.** landed (this commit). Operator sentence for EXITS.md sent to OPS-5. PERF-1 re-measures the WASTE rows.
**Amended (CLIENT-28 follow-up, ROOT ruling, law 7).** A peer never gets a bare EOF from a missing or dead child.
- **The socket is bound only once the child exists** (`sockets::check_supervised` before the launch: the group check and the live/stale socket check, unchanged in order; `bind_supervised` after the spawn, which checks again). A launch refused before the child (policy, spawn) leaves no socket, so no peer waits in a backlog nobody will serve. A bind that fails after the spawn kills the child and refuses at launch.
- **When the child closes its stdout,** every open connection's last frame is `closed unreachable`, after the replies already queued for it (it was an empty frame, a bare EOF). `unreachable` is Lean's nearest name: the Host behind this socket cannot be reached. Its docstring in Protocol/Table.lean still says "nd-attach: the Store's socket does not accept a connection", so widening that doc to name the supervisor case is PROTOCOL's (asked through ROOT); no new name was added.
- **Plants:** `supervise a_child_that_dies_is_named_unreachable_to_every_peer` (A answered and idle, B in flight: both read `closed unreachable`); `supervise a_launch_refused_before_the_child_leaves_no_socket` (`Exposed` policy → refusedAtLaunch, no socket file); `mux replies_route_by_connection_and_child_close_ends_serve` now requires `closed unreachable` on both connections (it encoded the bare EOF). Mutations: N1 empty last frame → both red; N2 bound before the child → red.
- **Critique.** A peer that connects in the instant between the child's death and the supervisor's exit can still reach a backlog that is never accepted, and gets a reset. Naming that peer would need the accept thread to outlive `serve`. With bind-after-spawn, the window is the child's own death, not its launch.

## CLIENT-29 · nd-members: each resident grain's member socket from the World, over its OWN follower; nd-member@ and its env file are deleted (2026-10-19, CLIENT-8; HOSTING-30 with HOSTING-9, ROOT rulings; HOSTING-10 agreed)
**The gap (HOSTING-30 §1).** A resident's launch resolves `MEMBER/<dirOf id>/nd.sock`. It came from `nd-member@ID.service`, which needed a per-resident env file (`/etc/nd/hosted/member-ID.env`) and an operator who started the unit before the grain's birth. A launch that came first was refused `pathMissing` and counted toward `crashLoop`. keybroker had the same fault for broker sockets, and HOSTING-26 closed it from the World.

**Decision.**
- **`nd-members MEMBER MEMBERS FOLLOW PIDS HOST_SOCK PEER SUPERVISE ND HOST STORE [--hide PATH]… -- /ABS/DECIDER [ARG]…`** is one process per World, run as nd. It asks its decider `residents` at start and every 200 ms, using the frames keybroker reads (`launcher/src/residents.rs`: `ask` and `decider_end`, which both binaries call). It serves exactly the names answered: from a grain's birth to its removal, with no operator list and no env file.
- **One follower per resident (ROOT ruled (A)).** A follower is not a read replica. It is one member's command machine. `host follow STORE MEMBER GRANT` starts `Follow.loop` with `Self = ⟨origin, member, grant⟩` (Host/Cli.lean:341), and every call it plans names `me.member` (Protocol/Command/Machine.lean:359), as does every envelope (:607). So per resident, nd-members runs two existing `nd-supervise` children:
  - **follow**: `FOLLOW/<name>/follow.sock` → `host follow MEMBERS/<name>/store MEMBER GRANT`. The policy is write = the store, exec = host. MEMBER and GRANT are read from the provisioning step's `MEMBERS/<name>/follow`: `HEX HEX` and LF, 0600, read through `custody::read_private` (the chain rule).
  - **stdio**: `MEMBER/<name>/nd.sock` → `nd --stdio MEMBERS/<name> FOLLOW/<name>/follow.sock HOST_SOCK`. The policy is write = the workspace, exec = nd, connect = [HOST_SOCK, its own follow socket] (CLIENT-24's fence, unchanged). The socket is 0660 with `--group <MEMBER's group> --peer PEER`, or 0600 with no group when PEER is this euid (HOSTING-21). The stdio child starts only once the follow socket exists, because its connect grant resolves the socket at launch.
  - Each child hides STORE and every `--hide` path (the unit passes `/etc/nd` and `/home`). Each child has a PID file, `PIDS/<name>.<role>.pid`. The decider's is `PIDS/decider.pid`.
- **nd-supervise is reused unchanged.** Bind-after-child, `peerRefused`, `fds_max` with `refusedAtLaunch`, and `closed unreachable` are each nd-supervise's own, per socket. nd-members holds no mux, reads no frame of a member socket, and holds no key.
- **The decider** is started confined: read = STORE, exec = itself, hidden = MEMBERS and every `--hide`. Until HOSTING ships `hosting-residents STORE`, it is `hosting-broker`, which already answers `residents`.
- **Placement: a launcher binary.** The residents codec is launcher's emitted `broker_generated.rs`, and launcher already depends on nanodregg-client (HOSTING-25), so a client-crate binary would be a dependency cycle. The ceiling row is its own.

**What it refuses, by name.**
- **Ends** (`members_exit`, Lean's `Hosting.MembersExit`, codes 150–159, emitted beside `keybroker_exit`): `usage`; `memberRoot` (MEMBER fails `check_shared_dir`, or a resident name fails `grain_name_ok`); `membersRoot`; `followRoot` (each fails `check_private_dir`); `fdLimit` (RLIMIT_NOFILE below `MUX.fds_max()` = 71: every child inherits the limit and would refuse at launch, so CLIENT-28's rule is applied once, here); `deciderRefused`; `pidFile`; `deciderSignaled` (restart); `deciderLost`; `deciderMechanism`. The decider's own end is passed through. All are fatal except `deciderSignaled`.
- **A World past `RESIDENTS_MAX` (1024, emitted from `Broker.Bounds.residentsMax`) ends it with code 7**, DeciderExit's `residentsPastBound`. It is the same fact under the same code, whichever side counts first (`members_past_bound_code`).
- **A resident's own trouble is a line on stderr, never an end**, because one resident must not stop the others:
  - `memberMissing <name>` (no `follow` file, or a malformed one, or no store directory): retried every tick and named once, so provisioning just after the birth binds the resident within a tick.
  - `socketDirShared <name>` (`MEMBER/<name>/` or `FOLLOW/<name>/` holds anything but its socket, CLIENT-20).
  - `memberCrashLoop <name> <role>` (STARTS_MAX = 5 starts in 120 s, restarts at least RESTART_AFTER = 2 s apart: nd-member@'s StartLimit and RestartSec): the resident is left unbound until the answer changes.
  - `memberSpawn <name> <role>`.
- **A resident not in the World has no socket.** A removed resident loses both children (each stopped by its own handle), both sockets, both directories and both PID files. A connect to its socket is refused `ENOENT`.

**Static bounds (law 4).**
- nd-members' own fds are a constant, whatever the number of residents: 3 stdio, 2 decider pipes, and for an instant one spawn pipe, one PID-file write or one directory listing, so at most 6. The plant samples `/proc/PID/fd` before and after a birth and finds them equal.
- Each resident's nd-supervise holds at most `fds_max` = 71 fds in its own process (CLIENT-28).
- Processes: 1 + 1 decider + 2·N nd-supervise + 2·N bwrap/children ≤ 2 + 4·1024.
- Threads: one per nd-supervise, plus 2 + 2·`CONNECTIONS_MAX` each.
- The unit's TasksMax is therefore OPS's to set from these numbers.

**Plants** (`launcher/tests/members.rs`, row `cargo:launcher:members`; real writer, Store, decider, nd-supervise, nd and host):
- `each_resident_grain_gets_its_member_socket_and_a_removed_one_loses_it`:
  - two residents born at genesis are bound; a `read` through each is served (`1=operator`); each socket is 0600 and its directory lists only `nd.sock`; an app grain gets nothing;
  - a resident born while running, and provisioned only after its birth (its name is its id), is bound and served;
  - nd-members' fds are unchanged;
  - each child was started exactly once (no start spent on a refusal), and none ended;
  - the removed resident's two directories and two PID files are gone, and a connect is `ENOENT`;
  - CONTROL: r1 is still served.
- `a_stranger_on_the_member_socket_is_refused_by_name`: with PEER set to another uid, the socket is 0660 and our connection is `closed peerRefused`.
- `an_unprovisioned_member_or_a_shared_socket_directory_is_named_and_the_others_served`: `memberMissing` is named once; `socketDirShared` is named; r1 is served meanwhile; once the stray file goes, r2 is bound on a later tick.
- `a_dead_follower_is_named_to_its_resident_and_started_again`:
  - nd-members is held stopped while its follower is SIGKILLed, so the window is the test's and not a race with the tick;
  - a `sync` then gets a named reply from nd (exit `client`, `nd: follow.sock: …`), never a bare EOF;
  - once nd-members is continued, the follower is started again (a new PID) and `sync` is served.
- `another_residents_follower_is_refused_by_name`: r1's workspace driven at r2's follow socket, by hand. The writer refuses its envelope (`unknownKey`), follow retries once by the incoming key (PROTOCOL-46), and stdio custody ends it `refused noRotation`. CONTROL: r1's own follower serves the same `sync`.
- `a_member_that_always_crashes_is_named_crash_loop_and_left_unbound`: the follower Store is an empty directory. There are at most 2 starts in the first 1.5 s (the backoff), exactly 5 starts, then `memberCrashLoop`; at most one stdio start (nd-supervise binds the follow socket once host follow is spawned, an instant before host refuses its Store); no socket directory; no start after.
- `nd_members_ends_by_name`:
  - `usage`; `fdLimit` (`ulimit -n 40`); `memberRoot`, `membersRoot`, `followRoot` (each root at 0755); `deciderMechanism` (`/usr/bin/false`);
  - a stub decider answering `../x` gives `memberRoot`, and answering 1025 names gives code 7 `residentsPastBound 1025`;
  - CONTROL: 1024 names are read without an end.

**Mutations, each red** (`logs/client8-mut.py`): M1 never unbind; M2 ask only once; M3 no peer admission; M4 a socket directory not alone accepted; M5 no fd check; M6 no resident bound; M7 the follower never reaped; M8 the follow identity swapped; M9 no name check; M10 a missing member not retried; M11 an unnamed decider code passed through; M12 no FOLLOW check; M13 stdio started before its follow socket; M14 no backoff; M15 no crash-loop bound. A first draft's workspace `check_private_dir` survived its mutation (M16: `read_private` of the `follow` file already applies the chain rule, and nd's custody checks the workspace itself), so it was deleted rather than kept as a check that no test can turn red.

**Alternatives.**
- (a) One process multiplexing N member sockets in-process (HOSTING-30 §4's sketch). It needs 1024 × 71 ≈ 72.7k fds in one process, plus a second mux owner in CLIENT's code. Composing nd-supervise keeps every per-socket law where it is already planted.
- (b) A mode of nd-supervise: the same cycle problem (client cannot read the residents codec), and nd-supervise's one-socket shape would become a supervisor of supervisors.
- (c) One shared follower per World (ROOT's first ruling). It does not work, as the CRITIQUE says.
- (d) (B) of that question: one follower Store with `Self` supplied per command. It is filed as cv 01a14fb9-adb0 with its trigger (the disk cost of N follow Stores past a stated bound) and its custody question. It is not built, because it unbinds the follower's plan from one identity.
- (e) systemd templates per resident, instantiated by a generator from the World (HOSTING-30's meta-critique). That puts World data into unit files, and a generator runs only at daemon-reload, so it does not track births.

**CRITIQUE.**
- **ROOT first ruled ONE shared member follower per World, on an assumed shape** ("a follow Store is a read replica"). The code corrected it before anything was built: the follower plans every call and envelope in its MEMBER's name, and a resident driving another member's follower is refused (the plant above). The ruling was withdrawn for (A). The brief was the least-checked source, as usual. The check was reading `Self`, not the follower's docstring.
- **Shared fate.** nd-members restarting drops every resident's socket until it rebinds (about 200 ms plus each child's launch). Its children are not bwrapped, so a SIGKILLed nd-members leaves them running. In deployment the unit's control group stops them; in a test, `Members` stops them by their PID files. *(Corrected by CLIENT-38: "there is no safe way, without `unsafe`, to give them a parent-death signal" was false; rustix's safe `set_parent_process_death_signal` gives every binary of ours one, and a SIGKILLed nd-members now takes its supervisors with it.)*
- **A removed resident's open connection gets a bare EOF.** Its nd-supervise is SIGKILLed by its handle, so the mux cannot write `closed unreachable` (CLIENT-28 law 7). The grain is being stopped by the controller on the same Turn, and new connects are `ENOENT`. A clean stop would need nd-supervise to handle SIGTERM (a signal handler, which needs `unsafe` or a new crate). This is offered to ROOT, not built.
- **The stdio child may write the follower's Store.** The Store lies inside the workspace it writes (`MEMBERS/<name>/store`, ROOT's layout), and a hidden path may not lie inside a grant. Both processes are the same member's and run as nd, so this widens nothing across identities. A separate store root would narrow it.
- **`noRotation` is the name a resident sees for "wrong follower".** The writer's `unknownKey` is the true cause. Follow's incoming-key retry reaches a custody that refuses rotation and renames the end. That is PROTOCOL's to sharpen (reported).
- **The stub decider** (`/bin/sh` + `cat`) is the only way to plant the bad-name and past-bound ends without 1025 grains. It shows nd-members' own checks, not the decider's.
- **Unrun:** a second real uid (the stranger plant uses PEER = another uid); the argv as OPS renders it (the unit is OPS-5's next step, and members.rs then switches to the rendered argv, as broker.rs does); the macOS half.

**META-CRITIQUE.** I reached for nd-supervise composition partly because it is mine and planted. The test of that choice is whether nd-supervise's per-process shape (2N processes, 2N bwraps) becomes the cost a box notices before the fd bound does. Separately, I wrote the residents-bound check knowing the decider already ends at 1024. It stays because nd-members' process count is stated as a function of that bound, and Rust must not trust the bound it multiplies by. I also wrote a workspace check that turned out redundant, and only the mutation showed it.

**Size.** nd-members 550 (new row, measured by gates/metrics/nd-members, which the parent gates also run; GATES-6 agreed), residents.rs 45 (launcher, unrowed like keybroker), keybroker −17. The client library is untouched at 2520.

**Flag day.**
- `nd-member@.service` and `/etc/nd/hosted/member-*.env` are deleted by OPS-5's re-render, which adds `nd-members@WORLD.service`.
- RUNBOOK §2a's "start nd-member@ID before the birth" becomes "provision the member: `MEMBERS/<dirOf>/` with its custody, `store` (from the World's genesis) and `follow` (`MEMBER GRANT`, 0600)".
- `broker_generated.rs` is re-emitted (`members_exit`, `RESIDENTS_MAX`).
- Nothing persisted changes.

**Status.** landed (this commit). The decider becomes `hosting-residents` when HOSTING ships it, and the resident row moves onto nd-members (HOSTING-10).
**Amended (CLIENT-30).** A removed resident's nd-supervise children are SIGTERMed and reaped on later ticks, so every open peer reads `closed unreachable`; the CRITIQUE bullet "a removed resident's open connection gets a bare EOF" is closed there.

## CLIENT-30 · SIGTERM ends no connection bare: nd-supervise names every close, nd-members stops a removed resident without stalling the tick (2026-10-20, CLIENT-9; cv 01a1507c-722d, ROOT rulings, HOSTING-12 agreed)
**The defect (CLIENT-8 finding (a), CLIENT-29's critique).** nd-members stopped a removed resident's two nd-supervise children with SIGKILL, through their handles. nd-supervise had no SIGTERM handling either, so the default action killed it. Either way a peer with an open connection read a bare EOF, against CLIENT-28's law 7. A unit's stop (systemd sends SIGTERM to the whole control group) did the same to every supervisor.

**Decision.**
- **nd-supervise catches SIGTERM** before its child exists (`signal_hook::iterator::Signals`, a self-pipe). Its thread kills the child through the handle the main thread keeps in a `Mutex`. The child's stdout closes, so `serve` ends every connection `closed unreachable` (Lean's name; its docstring already says "at nd-supervise, its child's stdout closed"; no Protocol change). The supervisor then ends by SIGTERM's own default action (`emulate_default_handler`), so systemd and nd-members see exactly the end they saw before.
  - If the thread cannot take the lock, the main thread is past `serve` and every peer is already named, so the thread applies the default action at once.
  - A SIGTERM that arrives before the registration is the default death, and no socket is bound yet (bind-after-child, CLIENT-28).
- **`MuxLimits::fds_max` = 8 + connections_max + 1 = 73.** The SIGTERM pipe pair is two more fds of the supervisor's own (was 6 + 64 + 1 = 71). The operator sentences (Ops/Units.lean refusedAtLaunch and fdLimit, deploy/units/EXITS.md) read 73 (ROOT ruling, for OPS).
- **nd-members stops a removed resident without waiting.** `Pair::stop` removes both sockets and both directories (a connect is `ENOENT` at once) and SIGTERMs both children. Each child goes into `stopping` with a deadline of `GRACE` = 3·`reply_write` (90 s): CLIENT-28's writer bound, a queued reply and the close each within `reply_write`, plus one `reply_write` for the child's death and the supervisor's exit. Every tick reaps the children that ended and SIGKILLs and reaps each one past its deadline (`memberStopForced <name>`). Its PID file goes when it is seen gone. The tick never waits (ROOT ruling (4)).
  - **The static bound holds:** a stopping child stays counted. Before a birth is bound, `reap` keeps at most 2·(RESIDENTS_MAX − live − 1) stopping children and SIGKILLs the oldest beyond that (`memberStopForced`). So live plus stopping supervisors ≤ 2·RESIDENTS_MAX, and processes ≤ 2 + 4·RESIDENTS_MAX, as CLIENT-29 states and TasksMax was derived.
  - **A rebirth of a name that is still stopping waits** (`memberStopping <name>`, named once). Its old supervisor would remove the new socket path on its way out, so the name never gets a second supervisor.
  - At nd-members' own end every child is SIGTERMed and `stopping` is drained under the same deadlines.
- **The dependency (ROOT ruling (1)).** `signal-hook =0.3.18` (feature `iterator` only) and `signal-hook-registry 1.4.8`, both pinned in Cargo.lock. They are trusted and unverified, with two rows in gates/tcb.tsv, because the sigaction lives in the registry and the self-pipe in signal-hook. gates/tcb.py lists them by name in `UNSAFE_HOLDERS`, so a locked holder without a row is red by name. std and rustix give no safe handler, and SIGTERM handling is unavoidable: a unit stops by SIGTERM whatever nd-members does.

**Plants.**
- `client/tests/supervise.rs sigterm_names_every_peer_unreachable_and_ends_by_sigterm`: A answered and idle, B with a request the child holds. On SIGTERM both read `closed unreachable`, the socket is gone, and the supervisor's status is signal 15.
- `every_connection_gives_back_its_fds_and_threads` now bounds the peak by 73: 72 with 64 open, red at 71.
- `launcher/tests/members.rs`:
  - `each_resident_…`: a peer on each of r2's sockets (the member one served once) reads `closed unreachable` when r2 is removed, and the PID files go on a later tick.
  - `a_held_removal_stalls_no_birth_and_is_killed_at_its_grace`, with a steered stub decider that answers a file the test renames between ticks:
    - r2's stdio supervisor is held (SIGSTOP) while r2 is removed and r3 born in one answer, and r3 is served within 10 s;
    - r2 answered again is `memberStopping` and gets no second stdio start; r1 is served meanwhile;
    - at GRACE the held one is SIGKILLed (`memberStopForced`, not before GRACE, its /proc entry gone) and r2 is bound again (a second start). About 95 s.
- SIGSTOP stands for "a peer that never reads". No slow peer holds a supervisor past GRACE, because its writers give up within `reply_write`, so a supervisor that cannot end is the only way to reach the kill.

**Mutations, each red** (`logs/client9-mut.py` → `logs/client9-mut.out`):
- S1 SIGTERM not caught (both plants);
- S2 never flagged (ends `childSignaled` 66);
- S3 the default action while serving (no named close);
- S4 fds_max without the pair;
- M1 SIGKILL at once;
- M2 no grace;
- M3 the tick drains `stopping` (the birth waits);
- M4 no rebirth guard (a second supervisor);
- M5 no kill at the deadline.

**Declared unplanted:** the room eviction before a birth (needs RESIDENTS_MAX live residents); macOS.

**Alternatives.**
- (a) Close the child's stdin on SIGTERM and let it drain: graceful for a request in flight, but its length is the child's (up to `REPLY_MS_MAX`), past any grace nd-members can hold.
- (b) Watch nd-supervise's stdin as a stop pipe instead of a signal: no crate, but a unit's SIGTERM still kills it bare.
- (c) A flag handler (`signal_hook::flag`) with a polling thread: no fds, but 2048 supervisors waking on a timer.
- (d) nd-members blocking on its stops (the first build): a removed resident's stuck peer would stall every birth for up to 90 s. HOSTING-12 measured that a birth nd-members has not bound yet crash-loops its grain (`pathMissing` ×5 in milliseconds). ROOT ruled it a defect.

**CRITIQUE.**
- A peer that does not read within `reply_write` still gets no name. Its close cannot be written, as with CLIENT-28's `replyWriteFailed`. A supervisor SIGKILLed at GRACE ends its peers bare, and that is named on nd-members' stderr instead.
- The kill of the child is abrupt: a request in flight gets `closed unreachable`, not its reply. The member's attempt store owns that recovery (CLIENT-27).
- signal-hook adds two trusted crates with unsafe to a TCB whose own crates forbid unsafe.
- `GRACE`'s third `reply_write` is a margin for process exit, not a measured number.
- The over-bound eviction is reached only by churn past RESIDENTS_MAX removals within GRACE, and no plant reaches it.

**META-CRITIQUE.** I first built the blocking stop and called its stall a trade-off in my own critique. It was the defect CLIENT-29 already named ("one resident must not stop the others"), so it was not a trade-off. HOSTING-12's measurement of what a stalled birth costs, and ROOT's ruling, turned it.

**Size.** nd-supervise 132 → 160 of 160. Client library unchanged at 2520. nd-members 578 → 623 (ROOT ruling, gates/ceilings.tsv).

**Flag day.**
- fds_max goes from 71 to 73: a unit whose LimitNOFILE is exactly 71 now refuses at launch (none is rendered at 71).
- nd-supervise's end on SIGTERM is unchanged (signal 15).
- Nothing persisted changes.

**Status.** landed (this commit).

## CLIENT-31 · nd-members refuses at start a socket root its residents' sockets would not fit in sun_path; the name and path bounds are emitted (2026-10-20, CLIENT-9; CLIENT-8 item 10, ROOT ruling)
**The gap.** `Hosting.Proofs.Plan.sockets_fit` proves that every socket a resident gets fits sun_path (107 bytes), for every grain name of at most 64 bytes, under the DEPLOYED roots. nd-members takes MEMBER and FOLLOW as arguments, though, and checked no length. A root that is too long showed up per resident: the bind fails, `refusedAtLaunch` follows, and then `memberCrashLoop`. That fails closed, but under a misleading name and only once a resident exists. The Rust side also wrote the 64 as a literal in `grain_name_ok`.
**Decision.**
- `Emit.Broker` now emits `GRAIN_NAME_MAX` (`Codec.Path.componentMax`) and `SOCK_PATH_MAX` (`Hosting.sockPathMax`) into broker_generated.rs. `grain_name_ok` reads `GRAIN_NAME_MAX`, and `sockets_fit`'s premise is `n.size ≤ componentMax`, so the theorem and both Rust readers share one number.
- At start, after the directory checks, nd-members refuses `memberRoot` / `followRoot` (codes unchanged) when `ROOT/<GRAIN_NAME_MAX bytes>/SOCK` would pass `SOCK_PATH_MAX`. The stderr line gives the length. The Ops sentences for both codes name the case (EXITS.md mirrored).
**Plant.** `members.rs nd_members_ends_by_name`: for each of MEMBER and FOLLOW, a root one byte too long is refused by name, with `socket path 108 bytes` on its line. CONTROL: at exactly 107 bytes the roots pass, and the run ends at its decider (`/usr/bin/false` → `deciderMechanism`). Both mutations are red: L1 (no check) and L2 (`>=` for `>`).
**Critique.** The socket names `nd.sock` and `follow.sock` are still literals in nd-members (Lean's `memberSock`/`followSock` are ByteArrays, and the tagged emitter carries only numbers). The check assumes the longest name and does not measure the names answered. That is the right side to err on, since a name is at most GRAIN_NAME_MAX by `grain_name_ok`.
**Size.** nd-members 623 → 639 (ROOT ruling). Status: landed (this commit).

## CLIENT-32 · an `uncertain` attempt end carries follow's own words for a receipt it did not give (2026-10-20, CLIENT-9; cv 01a150b1, PROTOCOL-55's critique, PROTOCOL-58 the Lean half, ROOT ruling)
**The defect.** run.rs `receipt()` read a `receipt CALL` that follow ended without ok (e.g. `refused badResult`, an empty page short of the tip) as `Reply::Lost`, which drops follow's stderr. `drive` then ended `uncertain` with an empty payload. So a refused confirm rendered exactly like the Host's failed append, and telling the two apart cost PROTOCOL-18 a trace (the refusal-renders-as-the-verdict class).
**Decision.**
- `Reply::Lost(Vec<u8>)`. `receipt()`'s non-ok arm carries that command's stderr VERBATIM; Rust parses nothing. A transport loss, a timeout or a status the table does not name carries none.
- `drive` keeps the last non-empty one within `HINT_BYTES_MAX` (512, Lean's `Protocol.Bounds.hintBytesMax`, emitted). A longer one is no hint, never a cut one. Both uncertain ends carry it: the table's, and the loop bound's.
- Lean (PROTOCOL-58, 0856ca3) prints `hint confirm: refused NAME` only when the first line equals a table name byte for byte, and the printed name is the table's string. So no unvalidated byte reaches the surface.
**Plants.**
- `client/tests/attempt.rs an_uncertain_end_carries_follows_last_words_within_the_bound`: refused carried; exactly 512 carried; 513 gives none; a transport loss gives none.
- `client/tests/run.rs a_refused_confirm_hands_follow_its_own_words_with_uncertain`: follow's resume gets `uncertain ‖ refused badResult\n`.
**Mutations** (`logs/client9-mut3.py` → `.out`): H1–H4 are RED. H5, the loop-bound end dropping the hint, is GREEN: 72 reply patterns probed, and Lean's table always ends first, so that end is a backstop no plant reaches. It carries `why` so both uncertain ends agree. It is declared, not claimed.
**Critique.** "Last" is not separately planted: a drive makes one confirm or probe before its uncertain end. The rows' Loopback model (PROTOCOL-58's `dropHint`) cannot see this store regress; these two plants can.
**Size.** client library 2520 → 2528 (ROOT ruling). Status: landed (this commit).

## CLIENT-33 · Test scratch belongs to its creating test thread (2026-10-20, CX-GATES; ROOT granted CLIENT item)

**Premise price.** Landed theorems gaining a hypothesis: none. Landed theorems restated: none.

**Decision.** devtools::scratch registers each directory in a thread-local guard. The guard removes those directories when the creating test thread exits, including after an assertion panic. The existing initial removal of a same-name directory remains. This fixes the leak at creation rather than scheduling deletion of the shared cache. The integration plant spawns a test thread, observes its directory while it runs, joins it, and asserts both absence and an unchanged matching directory count. The previously leaked directories belong to Ember and are left untouched.

**Alternative.** Change scratch to return an owned path guard and migrate every caller. Several callers immediately call .join() and discard the root value; a guard would delete that root before the resulting path is used. Migrating all callers is possible, but would scatter a shared test-lifetime rule across many crates.

**Critique.** A test that deliberately hands its scratch path to an unjoined thread outliving the creator will see the directory removed. The existing tests use the path within the creating test's lifetime; such a handoff would need an explicit owner.

**Meta-critique.** Thread-local cleanup is attractive because it preserves the PathBuf API. The plant tests the actual destructor boundary rather than assuming that a successful test assertion implies cleanup.

## CLIENT-34 · Scratch plant obeys the standing Clippy rule (2026-10-20, CX-GATES; follow-up to CLIENT-33)

**Premise price.** Landed theorems gaining a hypothesis: none. Landed theorems restated: none.

**Evidence.** Convergence ed34b1b read `cargo clippy` RED at four `expect()` calls in the new scratch-count plant. The file already explicitly permits `clippy::unwrap_used` for failed plant setup. The filtered scratch test had passed; the full standing Clippy lane, which covers all targets, caught this style gate.

**Decision.** Use `unwrap()` at those four setup and join sites. Each failure still fails the test, while the existing file-level lint boundary applies. No assertion, cleanup action or tested behavior changes.

**Critique.** `unwrap()` gives less site-specific panic text than `expect()`. The source line and Rust backtrace still identify the failed setup; keeping the whole-workspace Clippy gate green is worth that diagnostic reduction.

**Meta-critique.** The fast landing judge reached the CLIENT package but did not run the standing Clippy lane. Future test-only changes should run the narrow Clippy target before landing when the crate has stricter workspace lints.

## CLIENT-35 · `nd invoke … --pin REL KEY`: a member pins a POINT read, so a `(live)` read (E1) is drivable from the deployed client (2026-10-23, CX-CLIENT; cv 01a166e9-a543, measured by CX-P5)

**The gap.** `nd invoke` could sign a range (`--range`, PROTOCOL-59) but no point. `derivePins` pins a cell only when the kernel asks (`unpinned`) and a row only when an edit asks (`rowUnpinned`). A method's POINT read asks for neither: an unpinned point is just an empty slot (`relReads` reads `rv.points self i`, the caller's row pins). So the method saw `none` and the E1 live column (4916f3a, `pointData`'s `live`) was never filled from nd. B1/B2 ("a revoked grant refuses", P8.2) were deployed in the kernel and the journey only.

**Decision.**
- Grammar: `invoke OBJ METHOD ARGS [--range REL K [PREFIX]] [--pin REL KEY]... [--via GRANT]`. KEY is LANG text at the relation's key type, read on follow's World when the call is planned, exactly as `--range`'s PREFIX. `Cmd.invoke`'s fourth field becomes `InvokeReads` (`range`, `points`): the TEXT the member named.
- `Command.signedReads` replaces `rangesOf`. It returns `SignedReads` (`ranges`, `points : List RowKey`): `invokeRange` (the old range body, unchanged) and `invokePoint`. `invokePoint` is relation REL of the object's package under the object, at `Lang.keyBytes` of KEY: the bytes an edit of that key writes. It refuses `missingCell`, `unknownRelation`, and the new `badKey` (KEY does not read at the key type) by name.
- `plan`/`planUnchecked` take `SignedReads`. The unsigned call starts with `rowPins := points.map (rowPinAt X.env w)`, the same `rowPinAt` the derivation uses for `rowUnpinned`. So the pin is follow's own World's, present or absent, and `planUnchecked_rowPins` / `plan_pins` keep their conclusions with no new premise. The cell the key names is pinned by the existing loop: `pointData`'s `look` on an unpinned cell is the kernel's `unpinned`, and `derivePins` answers it.
- No cell form of `--pin`. A cell pin is already derived on demand at follow's World, so an explicit one would be the same pin (a no-op flag).

**Plant.** `client/tests/pin.rs pinned_live_point_read_refuses_a_revoked_grant`, on two real Stores (`host serve` / `host follow`, as `real.rs`). The package's `use` reads its cell-keyed `facts` `(live)` with one point. Without `--pin` it refuses `unread`. With `--pin facts (record (cell #G))` it commits while grant G is live. After `revoke G` the same argv is refused `program` with the hint `grantDead`: the method's own name, read in the same Turn (P8.2 from nd). Also checked: `badKey`, `unknownRelation`, and a dangling `--pin` (`usage`). The fixture is `client/tests/fixtures/pin/Live`, core text printed by LANG's printer from the surface quoted in the test (`nd install` reads core text).

**Mutation.** M1: `planUnchecked` drops the command's points (`rowPins := []`). The `host` exe rebuilt, the plant is RED at the live commit (`hint program: use: refused unread`). Restored GREEN.

**Critique.**
- KEY is read at the full key type, so a point names exactly one row; a prefix point has no meaning.
- The flag order is fixed (range, then pins). A PREFIX is "the word after K unless it is `--pin`". That rule leans on no LANG text being the word `--pin`, which is true of the reader today and is not stated as a theorem.
- The pins are bounded only by the argv bound (`argvBytesMax`) and the receiver's `x.points` slot count (more pins than slots are refused by LANG, by name). `Kernel.Bounds.touchesMax` bounds the derived pins, not these.

**Meta-critique.** The obvious fix was to make `derivePins` "pin what the method reads". That is impossible without the member saying WHICH key: a point read does not refuse, it reads an empty slot. That is exactly why the gap was silent. The pin is the member's statement, as a range is, so it belongs beside `--range` in the plan's signed reads, not in the derivation loop.

**Premise price.** No landed theorem gains a hypothesis. `plan_pins`, `planUnchecked_*`, `plan_admits`, `step_submit_planned`, `staleBehind_final(_sep)` and the Socket statements take `SignedReads` where they took `List RangeRead`, and `plan_pins` concludes `u.ranges = rs.ranges`. `rangesOf_pins` becomes `signedReads_ranges` (the ranges half) over `invokeRange_pins`.

**Flag day.** None persisted. The argv grammar only widens: every argv that parsed before parses to the same call. `Cmd.invoke`'s fourth field is `InvokeReads`, a Lean-side shape with no wire form.

**Status.** landed eb77b78. The LANG half of the card (the live column on RANGE rows, one core with E5's receipt column) is CLIENT-36.

## CLIENT-36 · the live column on RANGE rows: a listed row of a `(live)` read carries its key's cell liveness, from the one core a point uses (`Lang.keyColumns`) (2026-10-23, CX-CLIENT; cv 01a166e9-a543's LANG half, on E5's receipt column)

**The defect (READ, then decided).** A method's `(live)` applied to points only. `rangeRowTy` had no `live` column. So the type of a range-only live read, `(rel (range m k) (live))`, was the plain range read's type, and `relReadShape` read it back as `live = false`. The `(live)` was dropped without a refusal:
- a body that never read `.live` installed as a plain range read;
- one that did was refused for an ill-typed body, never by the declaration's own name;
- a live range read of a relation that is not cell-keyed installed instead of being refused `liveNotCellKeyed`.

E5 had just given range rows its `receipt` column (`receiptRow`, `receiptSeen`). So the point and the row computed their columns in two places, and a range row of a read that was both live and receipt dropped `live`.

**Decision.**
- `Lang.keyColumns` is THE columns of one read key: `live` (E1's `cellLive` through `look`; an unpinned cell is the kernel's `unpinned`), `receipt` (E5's `receiptSeen`), both, or none.
- `pointData` = key ++ `keyColumns` ++ val. `columnRow` (was `receiptRow`) = key ++ `keyColumns` ++ val. `columnRows` (was `receiptRows`) applies it on a live or receipt read.
- `rangeRowTy d live receipt` mirrors `pointRecTy`'s columns. `relReadTy` passes `x.live`.
- `pointData_ok`'s statement is unchanged (proved from `keyColumns_ok`). `columnRow_conforms`, `columnRows_conforms` and `columnRows_digests` restate E5's three range theorems over both columns. `keyColumns_digests` is new.

**Teeth.**
- `live_range_read_kept`: a live range read's type reads back live.
- `live_range_read_typed` (control): its type is not the plain one.
- `live_range_not_cell_keyed_refused`: refused by name.
- `live_range_cell_keyed_admitted` (control).
- Plant: `client/tests/pin.rs` gains `scan` (`(facts (range 0 4) (live))`), driven by nd `--range facts 4`. It commits while the grant is live, and after `revoke` it is refused `scan: refused grantDead`.
- Mutation M2: `columnRows` adds columns only on a receipt read (the E5 shape). The host is rebuilt and the plant is RED (`hint program: scan: stuck`); `columnRows_conforms` no longer holds. Restored, then GREEN.
- E5's `client/tests/foreign.rs` (receipt range rows) is green on the shared core.

**Premise price.** None. No theorem gains a hypothesis. The three restated theorems take `live` beside `receipt`, and at `live = false` they are E5's.

**Flag day.** No package version byte. A package's types state which columns its reads carry. The live-range type did not exist before (it was the plain one), so nothing installed reinterprets: every package installed before keeps its exact type and read. A text that declared `(live)` on a range-only read now gets the column it declared. Fixture `client/tests/fixtures/pin/Live` re-printed.

**Critique.**
- `pointRecTy` and `rangeRowTy` still spell the column list twice (value `optTy val` vs `val`). They are one in meaning, not in code, because the many landed proofs that `simp only [pointRecTy, …]` would all move. That is a refactor with no behaviour, deferred to whoever next touches those proofs.
- M2 is the only range-specific behavioural plant. A mutation of `keyColumns`' live arm is E1's plant (a) and reds both columns at once.

**Meta-critique.** "Make range reads live" was in the card as parity. The finding that matters is that `(live)` on a range was SILENTLY DROPPED by the type round trip: a declaration the reader accepted and the checker forgot. The teeth are aimed at that: the round-trip theorem, not only the runtime column.

**Status.** landed (this commit).

## CLIENT-37 · the next run of the same argv IS its open attempt: nothing re-plans beside a call that may still land (2026-10-24, FIX-RUST; readers/COLLATION-20261024 A6, READ-RUST F1)

**The defect (READ at f9657bd).** `attempt.rs:18-21`, `Protocol/Attempt.lean:21-23,38,90,99`, CLIENT-25 and CLIENT-27 promise that an attempt left open (`declined`, `open`, `contradicted`, `uncertain`, `badReply`) is looked up again by the next run. Nothing did: `Attempt::load` had one caller, `reconcile`, and only for an armed rotation. Every other run computed `max+1` and froze a NEW call, which follow planned on its current World. So after `uncertain` (a lost submit reply) the member's or the resident's re-run signed a second call beside the first, and both could commit: the double-effect window `Attempt.lean` names. The tests that "showed" the next run drove `Attempt::load` + `drive` by hand.

**Measured.** `client/tests/real.rs`, on the real `host serve` / `host follow`: a write whose submit reaches the writer and whose reply and lookup are lost (a reply-losing proxy in front of host.sock: the observable of a writer dying after its commit, without the race of killing it) ends `uncertain`; the same argv again. With the reload skipped (the plant), the height moves by TWO (`left: 10, right: 9`, `fixrust-scratch/plant1.log`).

**Decision.**
- An attempt directory freezes, beside `call`, the command it was signed for (`argv`: the generated `Command` encoding, the bytes follow is sent) and follow's continuation at the submit step (`cont`). `call` is written last, so a directory with `call` is complete; one without it is a crashed freeze, never sent, and is passed over.
- `run` begins with `Attempt::open_for(attempts, argv)`: the newest attempt frozen for these exact argv bytes that has no `settled`. When there is one, the run IS that attempt: it is driven from where its files say it stands (`Attempt.next`, emitted), and follow is resumed with the attempt's own `cont` and its end, exactly the step-4 resume the run that froze it would have made. Follow's `settled` (Machine.lean) then decides the command's end on its own World (`ownSettle`), as before. Follow is never asked to plan, so custody signs nothing new.
- A re-run of `rotate` whose armed attempt is open continues it the same way (`reconcile` steps aside for the attempt the run continues; `finish` settles custody on the member's verdict).
- One function, `finish`, drives an attempt and says its end as follow's result, for a fresh submit and a continued one alike.

**Where the decision lives (law 2).** What each request is, and what the command's end is, stay Lean's (`Attempt.next`, `Command.settled`). Rust looks the attempt up by its stored argv bytes (a key lookup in the member's own workspace) and hands follow back follow's own continuation. The considered alternative was `Command.start` taking the open call and choosing itself. Refused: a frame would carry the argv twice (the continuation holds it), which is A3's whole-frame bound problem again, and the `tx … / id …` text a commit prints comes from the Turn the PLAN derived (`receipt X t`), which cannot be re-derived from the call on a World that has moved. The continuation is follow's own words; re-presenting it is what every step of every command already does. The one Rust branch left ("an open attempt for this argv: resume, else command") is the rule Attempt.lean states in prose; a Lean table of one row for it would move no decision.

**Plants.**
- `client/tests/real.rs` (above): GREEN with the continuation (height +1, one attempt frozen for the two runs, the read shows one write); RED without it.
- `client/tests/run.rs a_rerun_of_the_same_argv_continues_its_open_attempt_and_signs_nothing`: the second run's only Host request is a lookup of the frozen bytes; follow is resumed once, with the first run's continuation and `committed`; a third run, after settlement, plans afresh. `an_open_attempt_is_continued_only_by_its_own_argv`; `a_rerun_of_rotate_continues_the_armed_rotation`. Both re-run plants RED under the skipped reload.
- `client/tests/attempt.rs open_for_finds_the_newest_unsettled_attempt_of_its_argv`: settled, other-argv and crashed-freeze directories passed over; a `call` without `argv` refuses to load.

**Critique.**
- The intent's identity is its argv bytes. A member who means the same write twice while the first is open gets the first one's outcome, and runs it again after it settles. That is the at-most-once price, and the honest one.
- An attempt that ends `open` (sends exhausted, window live) now holds its argv until the window passes or `nd cancel CALL`; in a World nobody else writes to, heights do not advance, so that can be long. Before, the re-run signed a second call instead. `open`'s stderr does not name the call to cancel (it is `attempts/<n>/call`).
- NOT closed: a run that writes `settled committed` and dies before printing, or (F23) an `nd --stdio` command that commits after the resident gave up on it (`replyTimeout`). The attempt is settled, so the resident's retry plans afresh: a second effect. Closing it needs an intent identity the caller holds across its retries, not a property of the attempt store (cv 01a16d4c-4294).
- `open_for` reads the directory: O(attempts) per run, F15's debt, unchanged in order (`next_dir` already listed it).

**Meta-critique.** The old tests passed because each performed "the next run" itself; the defect was an absence, not a wrong branch, so no unit test of a branch could see it. The plants here run `run::run` twice over one workspace, and the real one counts heights on the writer.

**Flag day.** The attempt directory layout: `argv` and `cont` beside `call`. An older attempt (a `call` without them) refuses to load (`attempt: inconsistent directory`), and `open_for` reaches every unsettled attempt, so a workspace holding one refuses every command: empty `attempts/` (or re-init) after this lands. No wire, no Lean, nothing re-emitted.

**Size.** client library 2528 → 2678 (gates/ceilings.tsv, this commit).

**Status.** landed a7bccd8.

**Amended (2026-10-24, FIX-RUST, a regression a7bccd8 shipped).** THE BAR's standing run read RED `friend1 nd write exit 1: refused stale` (MEASURED in a full judge on main 7332f9c, and reproduced: `fixrust-scratch/bar2.log`). The BAR re-runs a write declined `stale` after one `nd sync`. With the continuation, that re-run continued the old attempt; follow's probe settled it refused (stale BEHIND, final by KERNEL-54), and the command ended `refused stale` instead of writing. A call follow's own World holds refused or expired can never land, so it is no reason to refuse the intent. Now the run resumes follow with the attempt's refused end FIRST, so step 4 checks the claim on its own World (`ownSettle`). Only when follow answers `refused` does the run plan the command afresh (`Table.exit_refused` = `CommandExit.refused`, emitted). Committed, open, uncertain, declined and contradicted ends are the command's end, as before. Plant: `client/tests/run.rs a_rerun_whose_open_attempt_is_dead_plans_afresh`; THE BAR standing PASS (`bar1.log`: stale-writes 1, stale-reruns 1, stale-after-sync 0). Both are RED with the replan removed. Meta-critique: CLIENT-37's critique named the intent-identity price and missed its converse. A DEAD attempt must release its argv, or the at-most-once rule becomes at-most-zero. The plant that would have caught it (the BAR's forced stale) runs only at convergence, which is where R-0069 says the debt is paid.

## CLIENT-38 · every process of ours dies with the parent that spawned it; the runner kills a timed-out row's whole process group; a dead stderr no longer stops nd-supervise's SIGTERM (2026-10-24, FIX-RUST; readers/COLLATION-20261024 A19, READ-RUST F2; closes cv 01a16b44)

**The defect (READ at f9657bd).** cv 01a16b44's 328/336 leaked processes (nd-supervise, host, keybroker, nd-members, hosting-broker, nd-bwrap, 4–5 days old). Teardown is `Drop` only, and `Drop` runs only if the test process unwinds. `gates/runs.py` ran each row with `subprocess.run(…, timeout=600)`, which SIGKILLs its DIRECT child only: cargo, or `strace -f` without `--kill-on-exit` (whose tracees are then detached, not killed). The test binary under it lived on, then died without unwinding, and every unconfined process it had started (nd-supervise, nd-members, keybroker, grain-launch) was orphaned with its confined child alive. No binary of ours had a parent-death link. CLIENT-29 said there was "no safe way, without `unsafe`" to give one. That was false: rustix 1.1.2, already a dependency, has the safe `set_parent_process_death_signal`.

**Measured.**
- The old runner's call (`subprocess.run(sh -c 'sleep & sleep', timeout=2)`): the grandchild is alive after the timeout. With `run_group`: it is gone.
- A second defect found by the plant, not by the reader. With every binary linked, the held tree below still left four nd-supervise alive, with their children, under one plant. Reproduced alone (`fixrust-scratch/pd/epipe.py`): an nd-supervise whose stderr pipe has no reader does NOT stop on SIGTERM. Its SIGTERM thread's first act was `eprintln!`, which panics on EPIPE (Rust ignores SIGPIPE), so the thread died before `kill()` of the child. A supervisor under a dead nd-members has exactly that stderr. CLIENT-30's SIGTERM path depended on the stderr reader being alive.

**Decision.**
- `nanodregg_sandbox::die_with_parent()` (a platform fact, law 2). Linux: `PR_SET_PDEATHSIG = SIGTERM`, plus a `getppid` compare across the call for a parent that died in between. macOS: no such signal exists, so a thread compares `getppid` every `ORPHAN_POLL` (200 ms) and raises the same SIGTERM. The signal is SIGTERM because it is the stop a service manager sends: nd-supervise answers it by naming every close (CLIENT-30), and the other binaries take it as their default end. Their confined children follow (`--die-with-parent`). It is the first act of nd-supervise, nd-members, keybroker and grain-launch.
- `nd` is not linked. It is a member's CLI, and a parent-death signal would kill `nohup nd …` when its shell exits. As a stdio child it is confined (`--die-with-parent`). `probe` is a test grain, already confined.
- A failure to set the link is an end by name in each emitted table: `parentDeath` = keybroker 149, nd-members 162, grain-launch 63 (fatal; `Hosting/BrokerExit.lean`, `Hosting/LaunchExit.lean`; `codes_nodup` / `codes_disjoint` / `codes_reserved` re-decided). nd-supervise uses its `refusedAtLaunch` with the text `parentDeath: E`. The Ops unit actions are rendered; `RestartPreventExitStatus` gains the three codes.
- `gates/runs.py run_group`: every row runs as the leader of its own process group (`start_new_session`); past DEADLINE the WHOLE group is killed. `gates/readset.py` traces with `--kill-on-exit` (and probes for it), so a killed strace takes its tracees.
- `nanodregg_sandbox::say` / `say_line` is the ONE stderr line writer: one write, never a panic (was `nanodregg_launcher::say`, which is now a re-export). nd-supervise, the mux's accept loop and nd use it in place of `eprintln!`.

**Plants** (`fixrust-scratch/plants2.log`, each RED under its mutation, GREEN restored).
- `devtools/tests/orphan.rs a_supervisor_whose_parent_is_killed_ends_with_its_child`: nd-supervise under an `sh` killed by SIGKILL; it and its confined child are gone within 10 s. P1: no `die_with_parent` in nd-supervise → 4 processes outlive.
- `devtools/tests/orphan.rs sigterm_stops_a_supervisor_whose_stderr_has_no_reader`. P2: the SIGTERM line by `eprintln!` → it does not end within 10 s.
- `launcher/tests/members.rs a_killed_test_process_leaves_no_supervisor_behind`: the real leak's shape. A child test process (`hold_a_tree`) holds a World, nd-members with one resident, keybroker and grain-launch (24+ processes, every unconfined binary named), and is SIGKILLed. Nothing under it survives 15 s. P-nd-members, P-keybroker and P-grain-launch: each binary without the link → exactly its own subtree outlives.
- The devtools helpers name each process by (pid, start time), and teardown stops survivors only by that pair, never by a pattern.

**Critique.**
- PDEATHSIG fires on the death of the spawning THREAD. Every spawner of ours keeps its children on the thread that owns them (main loops; libtest's test thread outlives its locals). A spawner that hands a child to a thread which ends early would see it SIGTERMed. MEASURED that a SIGKILLed parent's non-main-thread child does die.
- Residual window: a parent that dies before the child's first `getppid` (inside exec and runtime start) is not caught. Closing it needs the spawner to pass its pid, or a `pre_exec` prctl (`unsafe`, forbidden). The window is microseconds; the runner's group kill covers the test case.
- A process that left the runner's process group (bwrap's `--new-session`) is reached only through the parent-death chain, which is why both halves are needed.
- macOS: the watch costs one wakeup per 200 ms per supervisor process.
- The 328 already-leaked processes are not touched: no PID file names them. They are Ember's to stop by hand (cv 01a16b44's option (a)).

**Meta-critique.** The reader's diagnosis (no parent-death link, the runner kills one process) was right and incomplete. The plant that holds a real tree found the EPIPE panic, which the reader could not see: a fix verified only against the `sh` toy (the first plant) would have shipped with nd-members' supervisors still leaking. The last plant is the leak's own shape, a SIGKILLed test process, and not a reconstruction of it.

**Flag day.** Three exit codes are added to the emitted tables and the rendered units (re-emitted: `launcher/src/generated.rs`, `launcher/src/broker_generated.rs`, `deploy/units/`). No wire, no Store.

**Status.** landed (this commit).

## CLIENT-38 · every process of ours dies with the parent that spawned it; the runner kills a timed-out row's whole process group; a dead stderr no longer stops nd-supervise's SIGTERM (2026-10-24, FIX-RUST; readers/COLLATION-20261024 A19, READ-RUST F2; closes cv 01a16b44)

**The defect (READ at f9657bd).** cv 01a16b44's 328/336 leaked processes (nd-supervise, host, keybroker, nd-members, hosting-broker, nd-bwrap, 4–5 days old). Teardown is `Drop` only, and `Drop` runs only if the test process unwinds. `gates/runs.py` ran each row with `subprocess.run(…, timeout=600)`, which SIGKILLs its DIRECT child only: cargo, or `strace -f` without `--kill-on-exit` (whose tracees are then detached, not killed). The test binary under it lived on, then died without unwinding, and every unconfined process it had started (nd-supervise, nd-members, keybroker, grain-launch) was orphaned with its confined child alive. No binary of ours had a parent-death link. CLIENT-29 said there was "no safe way, without `unsafe`" to give one. That was false: rustix 1.1.2, already a dependency, has the safe `set_parent_process_death_signal`.

**Measured.**
- The old runner's call (`subprocess.run(sh -c 'sleep & sleep', timeout=2)`): the grandchild is alive after the timeout. With `run_group`: it is gone.
- A second defect found by the plant, not by the reader. With every binary linked, the held tree below still left four nd-supervise alive, with their children, under one plant. Reproduced alone (`fixrust-scratch/pd/epipe.py`): an nd-supervise whose stderr pipe has no reader does NOT stop on SIGTERM. Its SIGTERM thread's first act was `eprintln!`, which panics on EPIPE (Rust ignores SIGPIPE), so the thread died before `kill()` of the child. A supervisor under a dead nd-members has exactly that stderr. CLIENT-30's SIGTERM path depended on the stderr reader being alive.

**Decision.**
- `nanodregg_sandbox::die_with_parent()` (a platform fact, law 2). Linux: `PR_SET_PDEATHSIG = SIGTERM`, plus a `getppid` compare across the call for a parent that died in between. macOS: no such signal exists, so a thread compares `getppid` every `ORPHAN_POLL` (200 ms) and raises the same SIGTERM. The signal is SIGTERM because it is the stop a service manager sends: nd-supervise answers it by naming every close (CLIENT-30), and the other binaries take it as their default end. Their confined children follow (`--die-with-parent`). It is the first act of nd-supervise, nd-members, keybroker and grain-launch.
- `nd` is not linked. It is a member's CLI, and a parent-death signal would kill `nohup nd …` when its shell exits. As a stdio child it is confined (`--die-with-parent`). `probe` is a test grain, already confined.
- A failure to set the link is an end by name in each emitted table: `parentDeath` = keybroker 149, nd-members 162, grain-launch 63 (fatal; `Hosting/BrokerExit.lean`, `Hosting/LaunchExit.lean`; `codes_nodup` / `codes_disjoint` / `codes_reserved` re-decided). nd-supervise uses its `refusedAtLaunch` with the text `parentDeath: E`. The Ops unit actions are rendered; `RestartPreventExitStatus` gains the three codes.
- `gates/runs.py run_group`: every row runs as the leader of its own process group (`start_new_session`); past DEADLINE the WHOLE group is killed. `gates/readset.py` traces with `--kill-on-exit` (and probes for it), so a killed strace takes its tracees.
- `nanodregg_sandbox::say` / `say_line` is the ONE stderr line writer: one write, never a panic (was `nanodregg_launcher::say`, which is now a re-export). nd-supervise, the mux's accept loop and nd use it in place of `eprintln!`.

**Plants** (`fixrust-scratch/plants2.log`, each RED under its mutation, GREEN restored).
- `devtools/tests/orphan.rs a_supervisor_whose_parent_is_killed_ends_with_its_child`: nd-supervise under an `sh` killed by SIGKILL; it and its confined child are gone within 10 s. P1: no `die_with_parent` in nd-supervise → 4 processes outlive.
- `devtools/tests/orphan.rs sigterm_stops_a_supervisor_whose_stderr_has_no_reader`. P2: the SIGTERM line by `eprintln!` → it does not end within 10 s.
- `launcher/tests/members.rs a_killed_test_process_leaves_no_supervisor_behind`: the real leak's shape. A child test process (`hold_a_tree`) holds a World, nd-members with one resident, keybroker and grain-launch (24+ processes, every unconfined binary named), and is SIGKILLed. Nothing under it survives 15 s. P-nd-members, P-keybroker and P-grain-launch: each binary without the link → exactly its own subtree outlives.
- The devtools helpers name each process by (pid, start time), and teardown stops survivors only by that pair, never by a pattern.

**Critique.**
- PDEATHSIG fires on the death of the spawning THREAD. Every spawner of ours keeps its children on the thread that owns them (main loops; libtest's test thread outlives its locals). A spawner that hands a child to a thread which ends early would see it SIGTERMed. MEASURED that a SIGKILLed parent's non-main-thread child does die.
- Residual window: a parent that dies before the child's first `getppid` (inside exec and runtime start) is not caught. Closing it needs the spawner to pass its pid, or a `pre_exec` prctl (`unsafe`, forbidden). The window is microseconds; the runner's group kill covers the test case.
- A process that left the runner's process group (bwrap's `--new-session`) is reached only through the parent-death chain, which is why both halves are needed.
- macOS: the watch costs one wakeup per 200 ms per supervisor process.
- The 328 already-leaked processes are not touched: no PID file names them. They are Ember's to stop by hand (cv 01a16b44's option (a)).

**Meta-critique.** The reader's diagnosis (no parent-death link, the runner kills one process) was right and incomplete. The plant that holds a real tree found the EPIPE panic, which the reader could not see: a fix verified only against the `sh` toy (the first plant) would have shipped with nd-members' supervisors still leaking. The last plant is the leak's own shape, a SIGKILLed test process, and not a reconstruction of it.

**Flag day.** Three exit codes are added to the emitted tables and the rendered units (re-emitted: `launcher/src/generated.rs`, `launcher/src/broker_generated.rs`, `deploy/units/`). No wire, no Store.

**Status.** landed (this commit).

## CLIENT-39 · one deadline per reply, never per read: every peer of ours (Host, follow, a decider, an upstream) is bounded by `frame::Deadline`; a late decider is lost for good; `create_once` leaves a file absent or whole (2026-10-24, FIX-RUST; readers/COLLATION-20261024 A18, READ-RUST F3, F4, F5, F20)

**The defects (READ at f9657bd).**
- `sockets.rs` bounded each `read()` by `replyMsMax` (`SO_RCVTIMEO`), not the reply. A Host or follow that sends one byte every 119 s held one frame (up to 262 144 bytes) for about a year, and behind it the resident's serial `nd --stdio`. The mux's reply writes had the same per-syscall shape (`write_within`).
- keybroker and nd-members read their decider with no timeout at all. keybroker held the decider `Mutex` across the read, so a decider that was alive and silent (stuck, SIGSTOPped, half a frame written) wedged the tick and every resident's ask, and its `ENDING_TICKS` path never ran.
- keybroker's `UPSTREAM_TIMEOUT` was documented "connect to last byte" and enforced per read.
- `fsx::create_once` wrote in place, so a crash after the create and before the write left an empty `rotation`, and every later command refused (`custody: …rotation: Length(0)`).

**Decision.**
- `nanodregg_client::frame::Deadline`: reads and writes on any fd that fail `TimedOut` once one instant has passed. Each call polls for what is left. A write moves at most `PIPE_BUF` bytes, which a ready pipe or socket takes without blocking. ONE mechanism (law 1), used by:
  - `sockets.rs`: one deadline over the request AND its reply (`replyMsMax`);
  - the mux: the frame deadline (`frameMsMax`, its own `Deadline` deleted) and every reply write (`replyWriteMsMax`);
  - keybroker's upstream call (connect to last byte, as documented);
  - the decider pipes.
- The decider bound is LEAN's: `Hosting.Broker.Bounds.answerMsMax` (120 000 ms, a backstop above THE BAR's 60 s cold reopen), emitted as `ANSWER_MS_MAX`.
- `residents::Decider` is the one shape both consumers hold (CLIENT-29's "one consumer shape"). Every question is its frames written and one verdict read under one deadline. A decider that misses it, or sends bytes that do not decode, is LOST for good, because a late or half-read verdict would put the next answer out of step. Its consumer then ends by the decider's own end or `deciderLost`, as before. `KeybrokerExit.deciderLost`'s doc and its unit action now name the silent case.
- `fsx::create_once` writes `.NAME.tmp`, syncs it, and gives it its name by a HARD LINK, which refuses an existing name as `O_EXCL` did, then syncs the directory. `replace` shares the staging. `.NAME.tmp` is fsx's crash residue: the next write removes it, and the attempt scan passes over it.

**Plants** (`fixrust-scratch/plants3.log`, `plants3c.log`; each RED under its mutation).
- `client/tests/sockets.rs a_trickling_peer_is_a_timeout_within_one_reply_bound`: a header and then one byte per 100 ms is `timeout` within the 1 s bound. P3a: per-read timeouts → HANG past 5 s.
- `launcher/tests/broker.rs a_silent_or_stalled_decider_is_lost_within_the_answer_bound`: a silent decider and a half-frame decider are lost within 300 ms, and the next question is not asked. CONTROL: an answering one is read. P3c: no deadline on the read → HANG.
- `client/tests/attempt.rs a_killed_freeze_leaves_its_call_absent_or_whole`: a child freezing 4 MiB calls is SIGKILLed twenty times; every `call` present is whole. P3b: the in-place write → short calls (red three runs of three).
- `client/tests/custody.rs a_crash_inside_arm_leaves_the_workspace_unarmed`: the residue reads as not armed and the next `arm` succeeds. A short `rotation` made outside fsx still refuses by name.

**Critique.**
- The mux's reply-write bound has no plant of its own (it is the same `Deadline` the trickle plant reds). The keybroker upstream bound has none either: a trickling TLS upstream needs a test server, and the call goes through the same type.
- `PIPE_BUF` chunking costs one poll per 4 096 bytes on Linux (512 on macOS): 64 polls for a full 262 144-byte frame.
- The residents' own broker sockets (`RESIDENT_IDLE`, per read) are not changed. A resident is the client of its own grant, and the trust class is the member's, not a stranger's. If that changes, the same type applies.
- The bound for one decider answer is a constant, not a theorem about the decider. The decider's loop is total (fuel), but no Lean statement says an answer takes at most 120 s: it is the consumer's patience, named.

**Meta-critique.** The fix is ONE type, not three local timeouts, because the defect was one class (a per-syscall bound standing in for a per-reply one) found at four sites, and the mux already had the right shape privately. A future peer gets the bound by using the type, not by remembering it.

**Flag day.** A new emitted constant (`ANSWER_MS_MAX`, `launcher/src/broker_generated.rs`) and one changed unit-action text (`deploy/units/EXITS.md`). No wire or Store format changes: `create_once`'s files are byte-identical, only the way they come to exist changed.

**Status.** landed (this commit).

## CLIENT-40 · law 2 for the client's own bytes: every hand-read layout's widths are Lean's, the frame / child wire / rotation record are checked row by row against Lean's codec, and the hand-copied names and numbers are emitted (2026-10-24, FIX-RUST-2; readers/COLLATION-20261024 A17, HOLISTIC-CODEC §4.1–4.2, READ-RUST F16)

**The defects (READ at 7655145).**
- `client/src/frame.rs` (`HEADER = 4`), `mux.rs` (`CONN = 4`), `stdio.rs`, `join.rs` and `attach` (`saturating_add(4)`, `get(..4)`, `body[5..]`) each spelled the frame and child-wire layouts by hand. The mux built its reply and close frames itself, with `u32::try_from(len).unwrap_or(u32::MAX)`: a length that does not fit would have been written as a LIE (`u32::MAX`) rather than refused.
- `custody.rs` wrote and read the armed rotation as `u64le ‖ 32 ‖ 32`, a 72-byte record known only to Rust.
- Hand copies of Lean facts: the receipt line prefixes (`attempt.rs`, follow prints them in `Command.Machine.receiptText`), the socket names (`nd.rs`, `nd-members.rs`, `keybroker.rs`; `Ops.Units` again as strings), nd-members' restart policy (`2 s / 5 / 120 s`, citing the deleted `nd-member@`), the 200 ms decider tick (twice), `grain_name_ok`'s character class (Lean's `labelByte`), and "a code ≥ 128 is a signal" restated unconditionally in `residents.rs` and `grain-launch.rs`. The platform fact (`nanodregg_sandbox::killed_by_signal`) says that only on Linux.
- `client/tests/foreign.rs` X1b asserted only "failed"; the comment after X2h claimed a check (at the advanced head the receipt checks, refused as a second acceptance) that the test never made.

**Decision.**
- Widths from Lean, tied at compile time: `Protocol.Bounds.frameLenBytes` / `connBytes` (each `Stream.u32.size 0`), `childBodyMax` (`Host.Wire.bodyMax` is it), `Codec.Ed25519.publicKeyBytes` (`verify_pk_size`), emitted `FRAME_LEN_BYTES`, `CONN_BYTES`, `CHILD_BODY_MAX`, `PUBLIC_KEY_BYTES`. `frame.rs` asserts in `const` that both are a `u32`'s width; `custody.rs` that the key width is `ed25519_dalek`'s. A Lean width change fails the Rust BUILD, not a test.
- One writer and one reader of each layout: `frame::encode_body` is the only place a length prefix is written (`write_body` uses it). `frame::child_parts` / `child_frame` / `write_child` / `child_max` are the child wire for the mux, `nd --stdio`, init's follower and `nd-attach`. The mux's reply and close frames go through `encode_body`. A reply past the client bound ends the mux `ChildMalformed` by name; a close that does not frame is said on stderr and the connection is shut unnamed. A short child body is `FrameError::BadLength` (Host.Wire's `badLength`); `Truncated` carries Lean's offset.
- The rotation record is Lean's: `Protocol.rotationLayout` (`u64 attempt, bytes incoming, bytes pending`) with the codec `rotationFrame` and `rotationBytes` (80, `rotationFrame_size`). It is emitted as `layout::ArmedRotation` and `ROTATION_BYTES`; custody arms and reads through it.
- Bilateral vectors (HOLISTIC-CODEC §4.1's emitted-Rust leg, for these three layouts): sites `wire/frame` (`Protocol.socketFrame`, read by `Protocol.bodyParts?`), `wire/child` (`Host.childFrame` + `Host.decodeBody`, framed by `Host.encodeFrame`/`encodeReply`) and `client/rotation` in `Emit.Vectors`. Each has drawn rows and refusal rows (empty, past bound, truncated header, truncated body, trailing, a short child body, the 72-byte CLIENT-39-era record). `client/tests/vectors.rs` decodes every row with the deployed Rust reader, renders Lean's text (refusals at Lean's offsets), and re-encodes each accepted row with the deployed writer to the same bytes. Runs row `cargo:client:vectors` (`nobin ok`).
- Names and numbers emitted: `FOLLOW_SOCK`, `HOST_SOCK`, `MEMBER_SOCK`, `BROKER_SOCK` (Hosting.Plan; `hostSock` is new, and `Ops.Units` uses `hostSockName`/`followSockName`); `RECEIPT_WORD`, `HEAD_WORD`, `SETTLE_WORD` (`Protocol.Attempt`, which `receiptText` prints by); `DECIDER_TICK_MS` (`Hosting.Broker.Bounds.tickMs`); `RESTART_SECONDS`, `START_BURST`, `START_INTERVAL_SECONDS` (the restart policy, moved from `Ops.Units` to `Hosting` because nothing may import Ops (closure C10); the units render the same one); `LABEL_BYTES` (`Hosting.labelByte`): `grain_name_ok` = `!empty && wire::path_clean && ⊆ LABEL_BYTES`, Lean's `labelOk`.
- Signal deaths: `decider_end` and grain-launch's `ended` take the `ExitStatus` and ask `killed_by_signal`. grain-launch passes a controller's code through only when `ControllerExit` names it.
- foreign.rs: X1b asserts `keyTaken`. The claimed check is made: at the advanced head, a later receipt of the same call is refused `keyTaken` and not `headMismatch` (MEASURED green on hbox).

**Plant** (cheap, run once): `child_parts` reading the conn id big-endian → `every_child_wire_vector_reads_and_writes_as_lean_says` RED (`wire/child 0: re-encoded`).

**Critique.**
- The frame and mux are still hand-written Rust: what is Lean's is their widths, bounds and every row's verdict, not their code. HOLISTIC-CODEC §4.2 asks for emitted or deleted. The deadline and stream handling are not layout and stay hand-written. Emitting the byte part would mean a second string template (the thing §4.2 says to stop growing) until an emitter with a semantics exists.
- `Emit/Rust.lean`'s `frameIo` template (launcher/broker generated files) is a third u32 framing (`as u32`, a literal 4). It is emitted, so not hand Rust, but the vectors do not cover it. It is the obvious next site: `wire/frame` at `FRAME_MAX`.
- The three-way check is two-way here (compiled Lean writes the table; the Rust reads it). The kernel leg is the codecs' lawfulness theorems, not a decision over these rows.
- Tests that state a deployed layout (`launcher/tests/members.rs`'s socket listing, `isolation.rs`) keep their literals on purpose: a test that reads the constant cannot see a wrong constant. `resident_bell.rs`'s `PATIENCE` (Lang.Bell.patience) is a hand copy left as is. There is no batch-write verb, so its 2048 sequential writes stay (LANG's call, READ-RUST §4).
- `SameRecord`'s `keys` file (2–3 seeds, no lengths) is still a Rust-only layout. It is secret material and a fixed-width array, which `Layout` does not express.

**Meta-critique.** The test of each move was whether a Lean change would be FELT in Rust without anyone remembering. Widths fail the build; layouts fail the vectors; names and numbers change by re-emission. The weakest part is the first critique point. The vectors make a hand reader's disagreement visible, but they do not make it impossible.

**Flag day.** The custody rotation record is 80 bytes (`rotationLayout`). A 72-byte `ws/rotation` refuses `Length` by name: settle or remove it before upgrading a workspace with a rotation armed. Re-emitted: `client/src/generated.rs`, `launcher/src/generated.rs`, `launcher/src/broker_generated.rs`, `gates/codec-vectors.tsv` (three new sites, no existing row moved). Units are byte-identical.

**Status.** landed (this commit).
