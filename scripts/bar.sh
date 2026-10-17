#!/usr/bin/env bash
# scripts/bar.sh [--records N] [--record] — THE BAR end to end over sockets (owner: PERF; ASSEMBLY-perf ID-9).
#
# Real processes only: two members, each with its own `nd` workspace, custody holding and Store
# (`host follow`, confined by `nd-supervise`), writing through ONE writer (`host serve`, confined by
# `nd-supervise`, its socket shared by both members). N records (default 1000) = N/2 `nd create`
# per member, the two members concurrently; every `nd` invocation is timed end to end (follow
# pages to the tip, custody signs, the writer admits and fsyncs, follow renders). Then the writer is
# stopped by its PID file and started again: the cold reopen is spawn → first reply to one `read`
# frame through the new supervisor's socket.
#
# Prints, one per line:
#   BAR path create · BAR members 2 · BAR scope … · BAR device … · BAR sha …
#   BAR write-n N · BAR write-p50-ms V · BAR write-p99-ms V limit L · BAR write-max-ms V
#   BAR reopen-ms V limit L · BAR reopen-tail-bytes B · BAR load-before/after "…"
#   BAR verdict PASS | RED <what> | UNJUDGED <why>
# Limits come from gates/bar.tsv (`limit` rows), times BAR_LIMIT_SCALE (default 1): standing's
# plant runs BAR_LIMIT_SCALE=0.0001 and requires RED. A limit is judged only when load1 < 2
# both before and after the run (CHARTER: THE BAR is judged on a quiet machine); otherwise
# UNJUDGED (naming any limit it would have exceeded), never PASS. The plant judges regardless of load. A failed or timed-out `nd` (60 s) is RED by name, never a slow sample.
# --record appends the run to gates/bar.tsv as a `run` row (the nightly trend, not a ratchet).
#
# Not measured here (stated, not hidden): the hosted resident (Hermes) — no hosted verb exists
# yet; OS page cache is warm at reopen (`purge` needs root); follow lag inside nd (nd prints no
# clock). Every process this starts is stopped by its PID file; every wait has a deadline.
set -uo pipefail
here=$(cd "$(dirname "$0")/.." && pwd -P)
records=1000 record=0
while [ $# -gt 0 ]; do
  case $1 in
    --records) records=$2; shift ;;
    --record) record=1 ;;
    *) echo "usage: scripts/bar.sh [--records N] [--record]" >&2; exit 2 ;;
  esac
  shift
done
[ $((records % 2)) -eq 0 ] && [ "$records" -gt 0 ] || { echo "bar: --records must be even and positive" >&2; exit 2; }

load() { sysctl -n vm.loadavg 2>/dev/null | tr -d '{}' | awk '{print $1, $2, $3}' || cut -d' ' -f1-3 /proc/loadavg; }
before=$(load)

# Build what runs: the Lean host (lake) and the client binaries (cargo, release).
( cd "$here" && lake build host >/dev/null ) || { echo "BAR verdict RED build:host"; exit 1; }
cargo build --quiet --release --manifest-path "$here/client/Cargo.toml" --bin nd --bin nd-supervise \
  || { echo "BAR verdict RED build:client"; exit 1; }
HOST=$here/.lake/build/bin/host
BIN=${CARGO_TARGET_DIR:-$here/client/target}/release
[ -x "$HOST" ] && [ -x "$BIN/nd" ] && [ -x "$BIN/nd-supervise" ] || { echo "BAR verdict RED binaries-missing"; exit 1; }

# A short real root: a socket path must fit 104 bytes on macOS, and the sandbox checks real paths.
root=$(cd "$(mktemp -d "${TMPDIR:-/tmp}/ndbar.XXXXXX")" && pwd -P)
trap 'for p in "$root"/*.pid; do [ -f "$p" ] && kill "$(cat "$p")" 2>/dev/null; done; rm -rf "$root"' EXIT

lim() { awk -F'\t' -v m="$1" '$1=="limit" && $2==m {print $3}' "$here/gates/bar.tsv"; }
scale=${BAR_LIMIT_SCALE:-1}
wlim=$(awk -v l="$(lim write-p99-ms)" -v s="$scale" 'BEGIN{print l*s}')
rlim=$(awk -v l="$(lim reopen-ms)" -v s="$scale" 'BEGIN{print l*s}')
[ -n "$(lim write-p99-ms)" ] && [ -n "$(lim reopen-ms)" ] || { echo "BAR verdict RED gates/bar.tsv has no limit rows"; exit 1; }

python3 -I - "$root" "$HOST" "$BIN" "$records" "$wlim" "$rlim" <<'PY' > "$root/out" 
import os, socket, struct, subprocess, sys, threading, time
root, host, bindir, records, wlim, rlim = sys.argv[1], sys.argv[2], sys.argv[3], int(sys.argv[4]), float(sys.argv[5]), float(sys.argv[6])
nd, sup = os.path.join(bindir, "nd"), os.path.join(bindir, "nd-supervise")
red = []

def run(cmd, env=None, timeout=60):
    return subprocess.run(cmd, env=env, capture_output=True, timeout=timeout, text=True)

def line(out, key):
    for l in out.splitlines():
        if l.startswith(key):
            return l[len(key):].strip()
    raise SystemExit(f"BAR verdict RED setup: no `{key}` in {out!r}")

def start(name, sock, hides, store, args):
    """nd-supervise SOCK --hide … --write STORE -- host ARGS…, its PID in ROOT/NAME.pid."""
    cmd = [sup, sock] + sum((["--hide", h] for h in hides), []) + ["--write", store, "--", host] + args
    p = subprocess.Popen(cmd, stdin=subprocess.DEVNULL, stdout=subprocess.DEVNULL, stderr=open(os.path.join(root, name + ".err"), "w"))
    open(os.path.join(root, name + ".pid"), "w").write(str(p.pid))
    return p

def bound(sock, deadline_s):
    end = time.monotonic() + deadline_s
    while time.monotonic() < end:
        try:
            s = socket.socket(socket.AF_UNIX); s.connect(sock); return s
        except OSError:
            time.sleep(0.005)
    raise SystemExit(f"BAR verdict RED setup: {sock} never bound in {deadline_s} s")

def stop(name, p):
    """Stop a supervisor by its PID file; wait (deadline) for it and for its confined child."""
    pid = int(open(os.path.join(root, name + ".pid")).read())
    kids = run(["pgrep", "-P", str(pid)]).stdout.split()
    os.kill(pid, 15)
    p.wait(timeout=30)
    os.unlink(os.path.join(root, name + ".pid"))
    end = time.monotonic() + 30
    for k in kids:   # the child sees EOF on stdin and exits, releasing the Store's lock
        while time.monotonic() < end:
            try: os.kill(int(k), 0)
            except ProcessLookupError: break
            time.sleep(0.01)
        else:
            raise SystemExit(f"BAR verdict RED stop: confined child {k} of {name} still alive after 30 s")

members = []
for i in (1, 2):
    ws, hold, fs = (os.path.join(root, f"{d}{i}") for d in ("ws", "hold", "F"))
    os.mkdir(ws); os.mkdir(hold, 0o700)
    env = dict(os.environ, ND_WORKSPACE=ws, ND_HOLDING=hold)
    r = run([nd, "--init"], env)
    if r.returncode: raise SystemExit(f"BAR verdict RED setup: nd --init: {r.stderr.strip()}")
    k = run([nd, "--keys"], env).stdout
    members.append(dict(ws=ws, env=env, F=fs, key=line(k, "key "), next=line(k, "next ")))
fargs = sum(([m["key"], m["next"]] for m in members), [])
W = os.path.join(root, "W")
g = run([host, "genesis", W, "bar"] + fargs)
if g.returncode: raise SystemExit(f"BAR verdict RED setup: genesis: {g.stderr.strip()}")
for i, m in enumerate(members):
    gi = run([host, "genesis", m["F"], "bar"] + fargs)
    if gi.stdout != g.stdout: raise SystemExit("BAR verdict RED setup: member genesis differs from the writer's")
    m["member"], m["grant"] = line(g.stdout, f"founder {i} member ").split(" grant ")
hides = [m["ws"] for m in members]
wsock = os.path.join(root, "host.sock")
writer = start("writer", wsock, hides, W, ["serve", W])
bound(wsock, 30).close()
follows = []
for i, m in enumerate(members):
    os.symlink(wsock, os.path.join(m["ws"], "host.sock"))
    fsock = os.path.join(m["ws"], "follow.sock")
    follows.append((f"follow{i}", start(f"follow{i}", fsock, hides, m["F"], ["follow", m["F"], m["member"], m["grant"]])))
    bound(fsock, 30).close()

times = []
lock = threading.Lock()
def member(m, n):
    for _ in range(n):
        t0 = time.monotonic_ns()
        try:
            r = run([nd, "create"], m["env"])
        except subprocess.TimeoutExpired:
            with lock: red.append("ndTimeout(60s)")
            return
        dt = time.monotonic_ns() - t0
        if r.returncode or not r.stdout.startswith("tx "):
            with lock: red.append(f"nd-create-failed({r.returncode}: {r.stderr.strip()[:80]})")
            return
        with lock: times.append(dt)
ts = [threading.Thread(target=member, args=(m, records // 2)) for m in members]
for t in ts: t.start()
for t in ts: t.join()

stop("writer", writer)
for name, p in follows: stop(name, p)
tail = os.path.getsize(os.path.join(W, "seg.log")) if os.path.exists(os.path.join(W, "seg.log")) else -1

# The cold reopen: a fresh supervisor + host process over the Store; spawn → first reply.
t0 = time.monotonic_ns()
writer = start("writer", wsock, hides, W, ["serve", W])
s = bound(wsock, 120)
s.settimeout(120)
s.sendall(struct.pack("<IB", 1, 3))  # one `read` frame, empty payload: any reply proves the open
try:
    hdr = s.recv(4)
    reopen = (time.monotonic_ns() - t0) / 1e6
    if len(hdr) < 4: red.append("reopen: writer closed the socket without a reply")
except socket.timeout:
    reopen = None; red.append("reopen: no reply in 120 s (silent)")
s.close()
stop("writer", writer)

times.sort()
ms = lambda ns: round(ns / 1e6, 3)
pct = lambda q: times[min(len(times) - 1, (len(times) * q) // 100)] if times else 0
print(f"BAR write-n {len(times)}")
if len(times) != records: red.append(f"write-n {len(times)} of {records}")
print(f"BAR write-p50-ms {ms(pct(50))}")
print(f"BAR write-p99-ms {ms(pct(99))} limit {wlim:g}")
print(f"BAR write-max-ms {ms(times[-1] if times else 0)}")
print(f"BAR reopen-ms {reopen if reopen is None else round(reopen, 3)} limit {rlim:g}")
print(f"BAR reopen-segment-bytes {tail}")
over = []
if times and ms(pct(99)) > wlim: over.append(f"write-p99-ms {ms(pct(99))} > {wlim:g}")
if reopen is not None and reopen > rlim: over.append(f"reopen-ms {round(reopen, 3)} > {rlim:g}")
print("RED " + "; ".join(red) if red else ("OVER " + "; ".join(over) if over else "OK"))
PY
rc=$?
after=$(load)
grep '^BAR ' "$root/out"
dev=$(df -P "$root" | awk 'NR==2{print $1}')
echo "BAR path create"
echo "BAR members 2"
echo "BAR scope two members, one writer; no hosted resident; OS cache warm at reopen"
echo "BAR device $(uname -sm) $dev $( [ "$(uname -s)" = Darwin ] && echo F_FULLFSYNC || echo fdatasync)"
echo "BAR sha $(git -C "$here" rev-parse --short HEAD)"
echo "BAR load-before $before"
echo "BAR load-after $after"
status=$(grep -E '^(RED|OVER|OK)' "$root/out" | tail -1)
# A limit is judged only on a quiet machine — except under the plant (BAR_LIMIT_SCALE ≠ 1), which
# tests the comparator, not the machine. A broken run (a failed nd, a silent writer) is RED always.
quiet() { [ "$scale" != 1 ] || awk -v a="${before%% *}" -v b="${after%% *}" 'BEGIN{exit !(a < 2 && b < 2)}'; }
if [ $rc -ne 0 ] || [ -z "$status" ]; then
  verdict="RED $(grep -h 'BAR verdict RED' "$root/out" | head -1 | sed 's/^BAR verdict RED //')${status:+ $status}"
  [ "$verdict" = "RED " ] && verdict="RED driver-exit-$rc"
elif [ "${status%% *}" = RED ]; then verdict=$status
elif ! quiet; then verdict="UNJUDGED load1 ${before%% *}/${after%% *} >= 2${status#OK}"
elif [ "${status%% *}" = OVER ]; then verdict="RED ${status#OVER }"
else verdict=PASS
fi
echo "BAR verdict $verdict"
if [ $record -eq 1 ]; then
  w=$(awk '$2=="write-p99-ms"{print $3}' "$root/out"); r=$(awk '$2=="reopen-ms"{print $3}' "$root/out")
  printf 'run\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' "$(date -u +%Y-%m-%dT%H:%MZ)" "$(git -C "$here" rev-parse --short HEAD)" \
    "$(uname -sm)" "$before / $after" "$w" "$r" "${verdict%% *}" >> "$here/gates/bar.tsv"
fi
case $verdict in PASS) exit 0 ;; UNJUDGED*) exit 3 ;; *) exit 1 ;; esac
