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
