# decisions/client.md — BUILD-CLIENT (client/, sandbox/)

Earlier entries, frozen in `DECISIONS.md`: CLIENT-1 (Rust at all; ruled by ROOT 2026-10-16: custody +
transport only, ≤ 2,000 lines), CLIENT-2 (follow drives by steps; ruled, protocol in HOST-9), CLIENT-3
(attempts), CLIENT-4 (workspace dir, OpenSSH forwarding), CLIENT-5 (Ed25519 until KERNEL names the
scheme), CLIENT-6 (no binary until the generated table), CLIENT-7 (sandbox/ own crate, Hermes is a member;
ruled), CLIENT-8 (isolation invariant), KEY-CUSTODY (open, for Ember).

## CLIENT-9 one confinement shape, one mechanism per platform, no fallback (2026-10-16)
**Decision.** `sandbox/` exposes one function: `command(policy, program, args) -> Command`. The policy
is a list of hidden paths (an input; for a Lean child it is "the member's workspace", for a hosted
resident it will be Lean's profile). Linux: `bwrap --unshare-all --disable-userns --cap-drop ALL
--clearenv --ro-bind / / --dev /dev --proc /proc --tmpfs <hidden>…`. macOS: `sandbox-exec` with
`(allow default)(deny file-read* file-write* (subpath <hidden>))…`. Any other platform, a missing
mechanism, a hidden path that does not exist or cannot be named safely: refused by name, never launched.
**Alternatives.** (a) An allow-list profile (deny default, allow the Store and the binary's libraries);
(b) Landlock on Linux (in-process, no bwrap); (c) minidregg's two bwrap profiles (SPK floor and the
weaker Hermes worker profile, P3).
**Why.** The invariant CLIENT-8 states is a deny ("cannot read the seed"), so a deny-list states it
exactly and the plant tests exactly it. One argv shape for every child is law 1 (minidregg's P3 twin).
**Critique.** A deny-list hides only what it names: the child still reads the rest of the member's home
(other keys, ssh agent socket, browser profiles). An allow-list (a) is the honest shape for a parser of
untrusted bytes, and on Linux `--ro-bind / /` is the opposite of minimal. `sandbox-exec` is deprecated
by Apple and could vanish. The Linux branch is `cargo check`ed on the Mac but has not run (no Linux box
in use; hbox is off limits).
**Meta-critique.** I chose the shape that makes today's plant pass on the machine I have; the allow-list
is harder and I postponed it by calling the deny-list "exact".
**Status.** open (allow-list is the named next step).

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
