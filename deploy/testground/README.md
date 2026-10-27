# deploy/testground — the testground's hosted World (DESIGN-TESTGROUND §3.2; CLIENT-43)

The page (`testground/`, published by Ember) is a member's client: its follow runs in the tab. A
hosted World swaps one function: the member's writer frames go over a WebSocket to a real `host serve`.
Three processes on the writer's box, each with a PID file (`run.sh`) or a unit (`units/`):

| process | what | listens |
|---|---|---|
| `nd-supervise … -- host serve STORE` | the writer, under the supervisor's mux (bounds, deadlines, named closes) | `STATE/run/host.sock` (0600) |
| `node testground/guestbook.mjs serve STATE/gb STATE/run/host.sock` | founder 0, a member like any other: signs the invitation (`world.json`), enrols each visitor's join token (`enroll`, `grant world … observe`) with its own follow re-deriving | `STATE/gb/guestbook.sock` |
| `python3 ws-relay.py` | WebSocket ↔ host.sock, bytes only (parses no frame, no op); `GET /world.json`; `POST /enroll` and `GET /attest` → the guest-book | `127.0.0.1:PORT` |

To turn it on (hbox, MEASURED 10-26 in `wt/testground-b`, PORT 18787 behind an ssh tunnel):

    testground/build/build.sh c WORK && testground/build/build.sh wasm WORK   # kernel.{mjs,wasm} beside guestbook.mjs
    lake build host && cargo build --release -p nanodregg-client --bin nd-supervise
    deploy/testground/run.sh genesis STATE      # the guest-book's seeds (0600) and `host genesis`
    PORT=8787 deploy/testground/run.sh start STATE
    deploy/testground/run.sh stop STATE         # each process by its PID file
    PORT=8787 deploy/testground/run.sh serve STATE   # the same in the foreground, for systemd (units/)

Under systemd (`units/nd-testground.service`, Type=simple around `run.sh serve`): the writer
confines itself (Landlock and seccomp, CLIENT-48), so every hardening directive may stay on
(`RestrictNamespaces=yes`, `ProtectKernelTunables=yes`, `ProcSubset=pid`, `RestrictSUIDSGID=yes`);
a `SystemCallFilter=@system-service` must add `@sandbox` (`deploy/live/confined-unit.sh` runs the
writer and a member's follower as transient units with the demo box's full drop-ins).
The kernel build pins libuv's headers at v1.48.0 (`build.sh`), so no CPATH is needed.

Then expose `127.0.0.1:PORT` as `wss://HOST/ws` (TLS and the proxy are the operator's act; nothing
here listens beyond loopback) and open the page as `…/testground/?hosted=wss://HOST/ws&join`. Each tab
joins over the invitation, under the sponsor key `world.json` names (`Invite.accept`), is enrolled,
and is then a member; a second tab is a second member of the same World.

**The fork (CLIENT-46).** A second writer of the SAME genesis is a fork: `run.sh fork STATE FORK`
copies the guest-book's seeds and runs `host genesis` with STATE's label and nonce (it refuses unless
the genesis input is byte-identical), then `PORT=8788 run.sh start FORK`. Both Worlds have one origin
and one invitation; they part at their first different Turn. Open tab one as
`?hosted=wss://A/ws&join&fork=wss://B/ws` and tab two as `?hosted=wss://B/ws&join`; tab two writes; in
tab one, World ▸ Fork check ▸ "check its attestation" fetches B's guest-book's signed head (`GET
/attest`: its `sync --attest`) and tab one's follow, cold, catches up through that position on A's
log and is refused `forkedWorld` by name. Check from the LONGER World's tab: a position past your
writer's tip is not reached yet. `testground/fork-run.mjs ws://A/ws ws://B/ws` is the same under node
(the control, A's own attestation, is `shared`).

**What a visitor trusts.** Its own follow, checking every reply the writer sends. **The caveat**: the
kernel and the sponsor key come from whoever serves the page and `world.json`; until the kernel's hash
is reproducible from source and the sponsor key travels by a channel the visitor already trusts
(RUNBOOK §2b's two channels), this demonstrates the check, it is not a trust anchor. Once TRUST-SEED's
certified heads land, a visitor can check the writer's certified head instead of one sponsor's word.

**Abuse.** The relay bounds its connections (`--max-conns`); each connection is one host.sock
connection under the mux's bounds. How many visitors the guest-book enrols is the kernel's to bound
(its World grant's enrolments, `enrollMax` 256; the meter, KERNEL-68), and a guest-book that ran out
refuses by name. Two bounds keep one client from spending them: the relay enrols at most
`--enroll-per-hour` (`ND_TESTGROUND_ENROLL_PER_HOUR`, default 10) per client address in a sliding
hour (the last `X-Forwarded-For` entry the proxy appends, else the TCP peer), answering `429`,
`Retry-After` and `{"refused":"enrollBudget"}` past it; and the guest-book refuses a `join`
`enrollFloor` once its own fold's `enrollLeft` is at `ND_TESTGROUND_ENROLL_FLOOR` (default 16), the
operator's reserve, spent only by a `reserve HEX` line on guestbook.sock, which the relay never
sends. A member enrolled once never enrols again (the page keeps its keys), so the floor only stops
new visitors of a World that is due a re-genesis. Per-address connection limits are the proxy's or
the box's firewall's.

## The resident (HOSTING-62): a model answers the World's public Bell

A hosted World may have one resident: a program that answers rings of the World's public Bell with a
model's words, delivered as the candidate of the section the ring aims at (the page's "Ask the
resident", CLIENT-54). Four more processes, two of them long-lived services:

| process | what | network |
|---|---|---|
| `keybroker` + its decider `hosting-broker` (`run.sh keys STATE`) | holds the provider key; serves the resident's socket `STATE/kb/<grain>/broker.sock`; the decider follows `STATE/store` for the allowance and the resident grain | **the only process that reaches the network**: TLS to `api.anthropic.com` (Lean's host, pinned leaf) |
| the resident's follower, its `nd --stdio` member and `resident` (`run.sh resident-serve STATE`) | each under nd-supervise; the resident reads the Bell, asks, answers | none |

Once, with the World up, as the World's user:

    run.sh resident STATE        # the resident's member and, through the guest-book, the inbox

It prints the ids it made (also in `STATE/gb/resident.json`). The allowance: `ND_MODEL`
(claude-haiku-5-5), `ND_CAP` micro-dollars per `ND_WINDOW_MS` (25000 per 300000), `ND_PRICE`
micro-dollars per 1000 tokens (500: Haiku 5.5's output price, charged for input and output alike).

**The key, and the daily cap.** The operator writes the key file; nothing in git holds a key:

    install -d -m 0700 KEYDIR
    ( umask 077; printf '7 %s\nasks 300\n' "$ANTHROPIC_KEY" > KEYDIR/provider.key )

Slot 7 is the allowance's `keySlot`. `asks 300` is the daily ask cap (HOSTING-62): at most 300 asks a
day are sent, whatever the World's allowance says, and the count survives restarts in
`KEYDIR/provider.key.asks` (keybroker makes it; never delete it to lift the cap: raise `asks`
instead). keybroker checks the file's custody (owned by the user, 0600, every directory above it
owned by the user or root and not group- or world-writable). `run.sh keys` installs
`deploy/tls/anchors.pem` (each start) and `deploy/tls/pins` (once; re-pin by editing it) into
KEYDIR. `ND_UPSTREAM` is the address keybroker dials (default `api.anthropic.com:443`; a numeric
`IP:443` needs no DNS: the certificate is still verified for `api.anthropic.com` and its leaf
pinned). keybroker's resident directories must come out 02710: `run.sh keys` sets umask 027.

**What it costs.** One answer is one ask; the allowance charges the worst case before the call (the
request's bytes plus 300 output tokens), about 1,250 micro-dollars for a 2,000-byte question, so at
most 300 × $0.00125 ≈ $0.38 a day. A restart of keybroker forfeits the current allowance window: for
up to `ND_WINDOW_MS` the resident answers `(refused overSpend)`. Past the day's cap it answers
`(refused askCap)`.

**Who can see the key.** keybroker reads it; its decider hides it; the resident's three supervisors
hide KEYDIR and the guest-book's seeds; every confined child sees neither. When all processes run as
one uid (the demo box), each other service hides KEYDIR as well (systemd `InaccessiblePaths=`).
