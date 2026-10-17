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
**The fence today.** The fence is prefix-only and not yet backed by a theorem: it holds up to
cSHAKE preimage resistance, because a call's signed message (`unsignedBytes`, world digest first)
carries no domain today and could begin with the envelope domain's bytes (CODEC-6, PROTOCOL-7). The
authority in the meantime is the kernel's observe-only grant (the key cannot write regardless), so
the gap is in the second fence, not the first. PROTOCOL-7's call-domain flag day (every call and
rotation message `domCall ‖ unsignedBytes`; `Protocol.envelope_call_disjoint : domEnvelope ++ r ≠
X.callMessage u`) closes it; then the real-round-trip plant (an observer's `nd write` refused
`envelopeOnly`, its `nd sync` served) goes in and this entry cites the theorem as proved.
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
