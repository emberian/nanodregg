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
