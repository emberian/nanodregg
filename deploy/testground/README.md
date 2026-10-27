# deploy/testground — the testground's hosted World (DESIGN-TESTGROUND §3.2; CLIENT-43)

The page (`testground/`, published by Ember) is a member's client: its follow runs in the tab. A
hosted World swaps one function: the member's writer frames go over a WebSocket to a real `host serve`.
Three processes on the writer's box, each with a PID file (`run.sh`) or a unit (`units/`):

| process | what | listens |
|---|---|---|
| `nd-supervise … -- host serve STORE` | the writer, under the supervisor's mux (bounds, deadlines, named closes) | `STATE/run/host.sock` (0600) |
| `node testground/guestbook.mjs serve STATE/gb STATE/run/host.sock` | founder 0, a member like any other: signs the invitation (`world.json`), enrols each visitor's join token (`enroll`, `grant world … observe`) with its own follow re-deriving | `STATE/gb/guestbook.sock` |
| `python3 ws-relay.py` | WebSocket ↔ host.sock, bytes only (parses no frame, no op); `GET /world.json`; `POST /enroll` → the guest-book | `127.0.0.1:PORT` |

To turn it on (hbox, MEASURED 10-26 in `wt/testground-b`, PORT 18787 behind an ssh tunnel):

    testground/build/build.sh c WORK && testground/build/build.sh wasm WORK   # kernel.{mjs,wasm} beside guestbook.mjs
    lake build host && cargo build --release -p nanodregg-client --bin nd-supervise
    deploy/testground/run.sh genesis STATE      # the guest-book's seeds (0600) and `host genesis`
    PORT=8787 deploy/testground/run.sh start STATE
    deploy/testground/run.sh stop STATE         # each process by its PID file

Then expose `127.0.0.1:PORT` as `wss://HOST/ws` (TLS and the proxy are the operator's act; nothing
here listens beyond loopback) and open the page as `…/testground/?hosted=wss://HOST/ws&join`. Each tab
joins over the invitation, under the sponsor key `world.json` names (`Invite.accept`), is enrolled,
and is then a member; a second tab is a second member of the same World.

**What a visitor trusts.** Its own follow, checking every reply the writer sends. **The caveat**: the
kernel and the sponsor key come from whoever serves the page and `world.json`; until the kernel's hash
is reproducible from source and the sponsor key travels by a channel the visitor already trusts
(RUNBOOK §2b's two channels), this demonstrates the check, it is not a trust anchor. Once TRUST-SEED's
certified heads land, a visitor can check the writer's certified head instead of one sponsor's word.

**Abuse.** The relay bounds its connections (`--max-conns`); each connection is one host.sock
connection under the mux's bounds. How many visitors the guest-book enrols is the kernel's to bound
(its World grant's enrolments; the meter, KERNEL-68), and a guest-book that ran out refuses by name.
