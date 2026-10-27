# client/ — DESIGN (BUILD-CLIENT, 2026-10-16)

The member's side, in Rust: **custody** (one seed, the frozen attempts), **transport** (frames over
Unix sockets) and the **workspace** (a directory). It decides nothing: every accept, refuse, select,
order, digest, encoding and rendering is done by a Lean process at the other end of a socket. Its
whole protocol knowledge is the table CODEC generates (see `proposals/client.md`). Decisions with
their critiques: `DECISIONS.md` CLIENT-1..7.

## 1. Processes

```
 nd <argv…>  ──follow.sock──▶ supervisor ──stdio──▶ host follow STORE   (member's own fold: authors, plans, renders)
     │
     └──────host.sock───────▶ supervisor ──stdio──▶ host serve STORE    (the one writer)
```

- `nd` is one process per command. It opens two sockets in the workspace and spawns nothing.
  The operations, status bytes, step tags and bounds are `Protocol/Table.lean` (6 ops: `submit`,
  `lookup`, `read`, `log` on host.sock; `command`, `resume` on follow.sock), reaching Rust only as
  CODEC's generated file.
- The **supervisor** (`nd-supervise`, same crate; core in `src/mux.rs`) is the byte mux HOST-2 asks for: it binds a Unix
  socket, accepts connections, and moves `(conn, op, payload)` frames to a Lean child's stdin and
  `(conn, status, payload)` replies back by `conn`. It parses no payload. It serves both `host serve`
  and `host follow` (HOST-7: consent is `host follow`). It is started by the service manager, never by `nd`; it launches its child through `sandbox/`
  so the child sees only its program, its Store and the platform floor, never the member's seed
  (CLIENT-8/9, deny by default; plants in `sandbox/tests/confine.rs`), and it
  exits when the child does (one restart path: the service manager's).
- `host.sock` may be a local socket or an OpenSSH `StreamLocalForward` of the remote one; the client
  cannot tell and does not care (CLIENT-4).

## 2. One command, end to end

`nd` never builds a request. It sends its argv to `follow` and executes the **steps** follow returns,
echoing an opaque continuation each time:

```
nd → follow : command(argv)                      follow parses argv (the ONE command language, Lean)
follow → nd : Sign(header, k)                    custody signs header exactly; nd → follow: resume(k, σ)
follow → nd : Host(op, payload, k)               nd relays to host.sock;      nd → follow: resume(k, reply)
follow → nd : Submit(call, k)                    nd freezes the attempt, drives submit/lookup on host.sock,
                                                 then nd → follow: resume(k, settled reply)
follow → nd : Done(exit, stdout, stderr)         nd writes them and exits
```

Challenge → prepare → assemble → submit → lookup is therefore a sequence of steps whose order is
follow's (Lean's); the Rust side has five step tags and a loop bounded by `stepsPerCommandMax`.
Rendering a Host refusal is a `Host`/`resume` round trip like any other: `nd` prints bytes.

## 3. Custody (`src/custody.rs`)

One 32-byte seed file, opened with `O_NOFOLLOW`, refused unless regular, exactly 32 bytes, mode 0600,
owned by the effective user; held in zeroizing memory; signs the bytes it is handed and adds nothing.
Ed25519 only until KERNEL names the signature scheme (CLIENT-5).

## 4. Attempts (`src/attempt.rs`)

A signed call is frozen in a new directory before a byte leaves (`call`, written once). Each send
writes `sent.<n>` first; the Host's settlement is one file, `committed` or `not-committed`. State is
which files exist, so a crash anywhere reloads as `Signed`, `Uncertain` or `Settled` — never as
"failed". `Uncertain` only looks up; a lookup that answers absent permits one more send of the same
bytes, up to `sendsMax`. Classification of a reply is the Host's status byte (ok / refused /
uncertain), never a decode. Freezing is custody: the member never signs two calls for one attempt.

## 5. Frames (`src/frame.rs`)

`u32le body_len ‖ body`, body = one op/status byte ‖ payload, `1 ≤ body_len ≤ frameBytesMax`.
Past the bound is refused before allocation; a stream ending inside a frame is `Truncated`.

## 6. Workspace

A directory: `seed`, `host.sock`, `follow.sock`, `attempts/<n>/`. No config file and so no parser:
a socket is a socket (or a symlink to one). Everything durable goes through `fsx::create_once`
(O_EXCL, 0600, write, fsync, fsync dir).

## 7. What does not exist here, on purpose

No command parser, no request encoder, no outcome decoder, no refusal names, no host-image hash, no
ssh client, no local fallback that execs a Host, no codec child, no JSON. Each was a minidregg Rust
module (dossier: `~/dev/redregg/work/DELETE-RUST-20261016.md`).

## 8. Gates

- `cargo check` + `cargo clippy --all-targets` clean before every push.
- Plants, run filtered: `cargo test --test frame --test custody --test attempt`. Each plant is a
  mutation that must go red by name (recorded per commit).
- Size: Rust lines in `SIZE.md`; the ceiling for `client/src` is 2,000 lines (minidregg: 113,757 for
  `mini` alone).
