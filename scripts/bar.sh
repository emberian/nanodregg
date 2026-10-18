#!/usr/bin/env bash
# scripts/bar.sh [--records N] [--standing] [--record] [--root DIR] [--harness-control]
# THE BAR end to end over sockets (owner: PERF; decisions/perf.md PERF-1, PERF-2).
#
# Real processes only. ONE writer (`host serve`, confined by `nd-supervise`) and three actors, each
# with its own `nd` workspace, custody and `host follow` Store (confined): two friends (`nd --init`,
# a separate holding) and the hosted-resident STAND-IN (`nd --init-hosted`, one-record custody,
# driven by `nd` argv: no model and no `nd --stdio` wire; HOSTING-8's resident replaces it). The
# three are founders of one genesis. N records are N write commands:
#   setup   each actor `create`s one object and `grant`s it `anyone mutate` (6 records), then `sync`s;
#   use     the other N-6 are `write`s, round robin over the actors, each actor alternating its own
#           object and the NEXT actor's through that actor's grant, so every object is used by a
#           member that did not make it: `host check`'s use= must be exactly 3 (PROTOCOL-43).
# Full mode (default): the actors write concurrently (THE BAR). `--standing`: one command at a time,
# so every count below is a function of N alone (the bounded run standing makes on every judge).
# Halfway through the writes every actor waits while the writer is stopped, sealed (`host seal`,
# HOST-43) and started again (C6): the final reopen reads a base past genesis and the second half's
# tail, never the tailMax worst cut (~25k records away: tailMax ~18.9 MB at deployed cadence since
# HOST-47; a Bench case).
# Every `nd` is timed from its spawner (exec to exit). Then each follow is synced to the tip and
# checked against the writer (`host check W --anchor` its head), the writer and one follow are
# stopped by their PID files and started again (the cold reopens: spawn -> first reply).
#
# Counts (deterministic, from the deployed binaries, never a clock): `host check` STATUS of the
# writer's Store before and after (steps, records, seg_bytes, use), the reopen's tail (steps and
# bytes past the base), and on Linux the writer's /proc/PID/io (syscalls and bytes through read and
# write). They print as `BAR count …` lines, and in --standing also as `WASTE bar <metric> <ratio>`
# lines that gates/waste.tsv pins (ceilings only fall). Signature verifies and trie hashes per step
# come from `bench-count W` (PERF-3): the follower's re-derivation of the writer's tail under
# KERNEL-36's countingEnv at deployed parameters, required to reach the host's own World, with a
# toy-Store plant it must refuse by name. The host process counts nothing (law 3). Verifies per step
# are exact and pinned; hashes per step depend on the trie's shape, which the run's random keys and
# nonce draw, so they are reported, not pinned. Lang ticks: not counted.
#
# Wall clock (`BAR write-p99-ms V limit L`, reopen-ms) is reported with the load average beside it
# and judged only in full mode on a quiet box (load1 < 2 before and after; else UNJUDGED, never
# PASS). --standing never judges a clock. Limits are gates/bar.tsv `limit` rows.
#
# --harness-control (GATES-15's known-red control): every comparator gets one expectation nothing
# meets: limits 0 (any measured time is over; judged at any load and in --standing), use must be 4 of 3, the
# follow-at-tip check expects one step more than the writer holds, and bench-count runs with its own
# --harness-control. The verdict is RED naming `harness-control` only when ALL FOUR fired; a control in which one stayed quiet prints the pass
# line and exits 0, so the runner (gates/runs.py) refuses every verdict of this row.
#
# Two fresh directories. The Stores (the bulk, and the device whose fsync a write pays) go under
# --root (a gate passes its own scratch, which it removes; a tmpfs there makes every fsync free, so it
# is RED by name). The custody workspaces, sockets and logs (a few KB) go under $HOME: custody refuses a
# key under any directory a group or other can write (sshd's StrictModes), which every path under a
# 775 build tree is, so that directory's chain is checked and RED by name too. Without --root the
# Stores share the $HOME directory. Both are removed on exit (a SIGKILL leaves them: KB under $HOME). Every process this starts is stopped by its PID file; every wait has
# a deadline. ND_LEAN_BIN / ND_BIN name prebuilt bin directories (host; nd, nd-supervise); unset,
# this builds them (lake build host; cargo build --release).
set -uo pipefail
here=$(cd "$(dirname "$0")/.." && pwd -P)
records=1000 record=0 standing=0 control=0 base=
while [ $# -gt 0 ]; do
  case $1 in
    --records) records=$2; shift ;;
    --record) record=1 ;;
    --standing) standing=1 ;;
    --root) base=$2; shift ;;
    --harness-control) control=1 ;;
    *) echo "usage: scripts/bar.sh [--records N] [--standing] [--record] [--root DIR] [--harness-control]" >&2; exit 2 ;;
  esac
  shift
done
case $records in ''|*[!0-9]*) echo "bar: --records must be a number" >&2; exit 2 ;; esac
[ "$records" -ge 12 ] || { echo "bar: --records must be at least 12 (6 setup records + 2 writes per actor)" >&2; exit 2; }

load() { if [ -r /proc/loadavg ]; then cut -d' ' -f1-3 /proc/loadavg; else sysctl -n vm.loadavg | tr -d '{}' | awk '{print $1, $2, $3}'; fi; }
before=$(load)

# absolute: the sandbox names the program by its real path
if [ -n "${ND_LEAN_BIN:-}" ]; then HOST=$(cd "$ND_LEAN_BIN" && pwd -P)/host || exit 1; else
  ( cd "$here" && lake build host bench-count >/dev/null ) || { echo "BAR verdict RED build:host"; exit 1; }
  HOST=$here/.lake/build/bin/host
fi
# --standing judges counts only, so it takes the dev profile a gate's cargo rows already built; the
# full bar's clock is release's.
if [ $standing = 1 ]; then profile=dev dir=debug; else profile=release dir=release; fi
if [ -n "${ND_BIN:-}" ]; then BIN=$(cd "$ND_BIN" && pwd -P) || exit 1; else
  cargo build --quiet --profile $profile --manifest-path "$here/Cargo.toml" -p nanodregg-client --bin nd --bin nd-supervise \
    || { echo "BAR verdict RED build:client"; exit 1; }
  BIN=${CARGO_TARGET_DIR:-$here/target}/$dir
fi
[ -x "$HOST" ] && [ -x "$(dirname "$HOST")/bench-count" ] && [ -x "$BIN/nd" ] && [ -x "$BIN/nd-supervise" ] || { echo "BAR verdict RED binaries-missing ($HOST, $BIN)"; exit 1; }

[ -n "${HOME:-}" ] && [ -d "$HOME" ] || { echo "BAR verdict RED setup: HOME is not a directory (custody's workspaces live under it)"; exit 1; }
root=$(mktemp -d "$(cd "$HOME" && pwd -P)/ndbar.XXXXXX") || { echo "BAR verdict RED setup: mktemp under $HOME"; exit 1; }
if [ -n "$base" ]; then
  [ -d "$base" ] || { echo "BAR verdict RED setup: --root $base is not a directory"; rm -rf "$root"; exit 1; }
  stores=$(mktemp -d "$(cd "$base" && pwd -P)/ndbar.XXXXXX") || { echo "BAR verdict RED setup: mktemp under $base"; rm -rf "$root"; exit 1; }
else stores=$root
fi
trap 'for p in "$root"/*.pid; do [ -f "$p" ] && kill "$(cat "$p")" 2>/dev/null; done; rm -rf "$root" "$stores"' EXIT

lim() { awk -F'\t' -v m="$1" '$1=="limit" && $2==m {print $3}' "$here/gates/bar.tsv"; }
[ -n "$(lim write-p99-ms)" ] && [ -n "$(lim reopen-ms)" ] || { echo "BAR verdict RED gates/bar.tsv has no limit rows"; exit 1; }
scale=1; [ $control = 1 ] && scale=0
wlim=$(awk -v l="$(lim write-p99-ms)" -v s="$scale" 'BEGIN{print l*s}')
rlim=$(awk -v l="$(lim reopen-ms)" -v s="$scale" 'BEGIN{print l*s}')

python3 -I - "$root" "$HOST" "$BIN" "$records" "$standing" "$control" "$stores" <<'PY' > "$root/out"
import os, socket, struct, subprocess, sys, threading, time
root, host, bindir = sys.argv[1], sys.argv[2], sys.argv[3]
count = os.path.join(os.path.dirname(host), "bench-count")
records, standing, control, stores = int(sys.argv[4]), sys.argv[5] == "1", sys.argv[6] == "1", sys.argv[7]
nd, sup = os.path.join(bindir, "nd"), os.path.join(bindir, "nd-supervise")
red = []

def stderrs():
    for f in sorted(os.listdir(root)):   # what each confined process said, so a red names its cause
        if f.endswith(".err"):
            for l in open(os.path.join(root, f)).read().splitlines()[-3:]:
                print(f"BAR stderr {f[:-4]}: {l[:200]}")

def die(why):
    stderrs()
    print(f"BAR verdict RED setup: {why}"); sys.stdout.flush(); raise SystemExit(1)

def run(cmd, env=None, timeout=60):
    return subprocess.run(cmd, env=env, capture_output=True, timeout=timeout, text=True)

def line(out, key):
    for l in out.splitlines():
        if l.startswith(key):
            return l[len(key):].strip()
    die(f"no `{key}` in {out!r}")

# The workspaces' directory: every directory up to / owned by root or us and writable by no one else
# (custody refuses a key under any other, and would refuse it later, mid-run). The Stores' directory:
# not a RAM file system.
d = root
while True:
    st = os.stat(d)
    if st.st_uid not in (0, os.geteuid()) or st.st_mode & 0o022:
        die(f"{d} is writable by a group or other (custody's StrictModes refuses keys under it): HOME must not be")
    if d == "/": break
    d = os.path.dirname(d)
fstype = "?"
if os.path.exists("/proc/self/mounts"):
    best = ""
    for m in open("/proc/self/mounts"):
        dev, mnt, typ = m.split()[:3]
        if (stores + "/").startswith(mnt.rstrip("/") + "/") and len(mnt) >= len(best):
            best, fstype = mnt, typ
    if fstype in ("tmpfs", "ramfs"):
        die(f"{stores} is on {fstype}: every fsync is free there, so a write's latency is not THE BAR's: pass --root")
print(f"BAR fs {fstype}")

def start(name, sock, hides, store, args):
    """nd-supervise SOCK --hide … --write STORE --exec HOST -- HOST ARGS…, its PID in ROOT/NAME.pid
    (the program is named to the sandbox: Linux's bwrap floor refuses one outside every path)."""
    cmd = [sup, sock] + sum((["--hide", h] for h in hides), []) + ["--write", store, "--exec", host, "--", host] + args
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
    die(f"{sock} never bound in {deadline_s} s")

def descendants(pid):
    out, todo = [], [pid]
    while todo:
        p = todo.pop()
        try: kids = open(f"/proc/{p}/task/{p}/children").read().split()
        except OSError: kids = run(["pgrep", "-P", str(p)]).stdout.split()
        out += [int(k) for k in kids]; todo += [int(k) for k in kids]
    return out

def stop(name, p):
    """Stop a supervisor by its PID file; wait (deadline) for it and for every process under it."""
    pid = int(open(os.path.join(root, name + ".pid")).read())
    kids = descendants(pid)
    os.kill(pid, 15)
    p.wait(timeout=30)
    os.unlink(os.path.join(root, name + ".pid"))
    end = time.monotonic() + 30
    for k in kids:   # the child sees EOF on stdin and exits, releasing the Store's lock
        while time.monotonic() < end:
            try: os.kill(k, 0)
            except ProcessLookupError: break
            time.sleep(0.01)
        else:
            die(f"stop: process {k} under {name} still alive after 30 s")

def hostio(name):
    """The confined `host` process's /proc/PID/io under supervisor NAME (Linux), else None."""
    pid = int(open(os.path.join(root, name + ".pid")).read())
    for k in descendants(pid):
        try:
            if open(f"/proc/{k}/comm").read().strip() == "host":
                return dict(l.split(": ") for l in open(f"/proc/{k}/io").read().split("\n") if l)
        except OSError:
            pass
    return None

def status(store, anchor=None):
    r = run([host, "check", store] + (["--anchor", anchor] if anchor else []))
    if r.returncode:
        return None, r.stderr.strip()
    return dict(kv.split("=", 1) for kv in r.stdout.split()[1:]), ""

names = ["friend1", "friend2", "resident"]
actors = []
for i, who in enumerate(names):
    ws, hold = (os.path.join(root, f"{d}{i}") for d in ("ws", "hold"))
    fs = os.path.join(stores, f"F{i}")
    os.mkdir(ws, 0o700)
    if who == "resident":
        env = dict(os.environ, ND_WORKSPACE=ws); env.pop("ND_HOLDING", None)
        r = run([nd, "--init-hosted"], env)
    else:
        os.mkdir(hold, 0o700)
        env = dict(os.environ, ND_WORKSPACE=ws, ND_HOLDING=hold)
        r = run([nd, "--init"], env)
    if r.returncode: die(f"{who} nd --init: {r.stderr.strip()}")
    k = run([nd, "--keys"], env)
    if k.returncode: die(f"{who} nd --keys: {k.stderr.strip()}")
    actors.append(dict(who=who, ws=ws, env=env, F=fs, key=line(k.stdout, "key "), next=line(k.stdout, "next ")))
fargs = sum(([a["key"], a["next"]] for a in actors), [])
W = os.path.join(stores, "W")
g = run([host, "genesis", W, "bar"] + fargs)
if g.returncode: die(f"genesis: {g.stderr.strip()}")
nonce = line(g.stdout, "nonce ")
for i, a in enumerate(actors):
    gi = run([host, "genesis", a["F"], "bar", "--nonce", nonce] + fargs)
    if gi.stdout != g.stdout: die(f"{a['who']}'s genesis differs from the writer's")
    a["member"], a["grant"] = line(g.stdout, f"founder {i} member ").split(" grant ")
s0, why = status(W)
if s0 is None: die(f"host check of the genesis Store: {why}")
hides = [a["ws"] for a in actors]
wsock = os.path.join(root, "host.sock")
writer = start("writer", wsock, hides, W, ["serve", W])
bound(wsock, 30).close()
follows = {}
def start_follow(i, a):
    fsock = os.path.join(a["ws"], "follow.sock")
    follows[i] = start(f"follow{i}", fsock, hides, a["F"], ["follow", a["F"], a["member"], a["grant"]])
    return fsock
for i, a in enumerate(actors):
    os.symlink(wsock, os.path.join(a["ws"], "host.sock"))
    bound(start_follow(i, a), 30).close()

def baseline(n):
    """Supervisor N's fds at rest: the least of 10 samples over 0.5 s (the probe connection `bound`
    made is closed by the mux asynchronously), None off Linux."""
    if not os.path.isdir("/proc/self/fd"): return None
    pid = int(open(os.path.join(root, n + ".pid")).read())
    v = []
    for _ in range(10):
        v.append(len(os.listdir(f"/proc/{pid}/fd"))); time.sleep(0.05)
    return min(v)
fds0 = {n: baseline(n) for n in ["writer"] + [f"follow{i}" for i in range(len(actors))]}
times, lock, stale, recur, staled = [], threading.Lock(), [0], [0], [0]
STALE_MAX = 8
def nd_ok(a, args, key=None):
    """One timed `nd ARGS` as actor a; its `key` line's value, or "" (None after a red). A write
    refused `stale` (another member's write moved the object it pinned: concurrent friends meet it)
    is run again after one `nd sync` (the friend catches up first), at most STALE_MAX times; the
    record's time is from the first exec to the committed exit. Counted: writes that met a stale
    at all, re-runs, and re-runs that were stale AGAIN after the sync (`BAR count stale-…`)."""
    t0 = time.monotonic_ns()
    for attempt in range(STALE_MAX + 1):
        try:
            r = run([nd] + args, a["env"])
        except subprocess.TimeoutExpired:
            with lock: red.append(f"{a['who']} nd {args[0]}: no exit in 60 s")
            return None
        if r.returncode and r.stderr.strip() == "refused stale" and attempt < STALE_MAX:
            with lock:
                stale[0] += 1
                if attempt == 0: staled[0] += 1
                else: recur[0] += 1
            try:
                run([nd, "sync"], a["env"])
            except subprocess.TimeoutExpired:
                pass
            continue
        break
    dt = time.monotonic_ns() - t0
    if r.returncode:
        with lock: red.append(f"{a['who']} nd {args[0]} exit {r.returncode}: {(r.stderr or r.stdout).strip()[:100]}")
        return None
    if args[0] != "sync" and args[0] != "read":
        with lock: times.append(dt)
    if key is None: return ""
    for l in r.stdout.splitlines():
        if l.startswith(key): return l[len(key):].strip()
    with lock: red.append(f"{a['who']} nd {args[0]}: no `{key}` line in {r.stdout.strip()[:100]!r}")
    return None

# setup: one object each, granted to anyone, then every follow catches up
for a in actors:
    a["obj"] = nd_ok(a, ["create"], "id ")
    if a["obj"]: a["pub"] = nd_ok(a, ["grant", a["obj"], "anyone", "mutate"], "id ")
if red or not all(a.get("pub") for a in actors): die("; ".join(red) or "setup")
for a in actors: nd_ok(a, ["sync"])

writes = records - 2 * len(actors)
plan = [[] for _ in actors]
for j in range(writes):
    i = j % len(actors); n = len(plan[i])
    if n % 2 == 0:
        plan[i].append(["write", actors[i]["obj"], str(n % 16 + 1), f"v{n:06d}"])
    else:
        b = actors[(i + 1) % len(actors)]
        plan[i].append(["write", b["obj"], str(n % 16 + 1), f"v{n:06d}", "--via", b["pub"]])
def workload(plan):
    if standing:
        for k in range(max(len(p) for p in plan)):
            for i, a in enumerate(actors):
                if k < len(plan[i]) and not red: nd_ok(a, plan[i][k])
    else:
        def member(i):
            for args in plan[i]:
                if red or nd_ok(actors[i], args) is None: return
        ts = [threading.Thread(target=member, args=(i,)) for i in range(len(actors))]
        for t in ts: t.start()
        for t in ts: t.join()
    if red: stderrs(); print("RED " + "; ".join(red)); raise SystemExit(0)

# C6: a base past genesis. Half the writes, then every actor waits while the writer is stopped by its
# PID file, sealed (`host seal`, HOST-43: the writer's own open and checkpoint, inline) and started
# again; then the other half. The final reopen reads that base and the second half's tail.
workload([p[:len(p) // 2] for p in plan])
stop("writer", writer)
sl = run([host, "seal", W])
if sl.returncode or not sl.stdout.startswith("sealed steps="): die(f"host seal W: {(sl.stderr or sl.stdout).strip()}")
sealed_at = int(sl.stdout.split()[1].split("=", 1)[1])
writer = start("writer", wsock, hides, W, ["serve", W])
bound(wsock, 30).close()
fds0["writer"] = baseline("writer")
workload([p[len(p) // 2:] for p in plan])

def fds(name):
    """Open file descriptors of supervisor NAME (Linux /proc), else None."""
    try: return len(os.listdir(f"/proc/{int(open(os.path.join(root, name + '.pid')).read())}/fd"))
    except OSError: return None

# every follow at the writer's tip, and the writer holding each follow's head
for a in actors: nd_ok(a, ["sync"])
io = hostio("writer")
def settled(n):
    """The fds supervisor N holds once every connection has closed: an exited nd's connection is closed
    by the mux asynchronously, so wait (deadline 5 s) for the count to come back to where it started;
    what is still held then is held (a leak), and is what the row counts."""
    end = time.monotonic() + 5
    while (v := fds(n)) is not None and fds0[n] is not None and v > fds0[n] and time.monotonic() < end:
        time.sleep(0.05)
    return v
sfds = {n: settled(n) for n in ["writer"] + [f"follow{i}" for i in range(len(actors))]}
stop("writer", writer)
s1, why = status(W)
if s1 is None: die(f"host check W: {why}")
steps = int(s1["steps"]) - int(s0["steps"])
if int(s1["base_steps"]) != sealed_at: red.append(f"the writer's base is at step {s1['base_steps']}, `host seal` sealed step {sealed_at}")
at_tip = int(s1["steps"]) + (1 if control else 0)
fired = []
for i, a in enumerate(actors):
    stop(f"follow{i}", follows[i])
    sf, why = status(a["F"])
    if sf is None: red.append(f"host check {a['who']}'s follow Store: {why}"); continue
    if int(sf["steps"]) != at_tip:
        (fired if control else red).append(f"follow {a['who']} at step {sf['steps']}, want {at_tip} (the writer at {s1['steps']})")
    _, why = status(W, f"{sf['steps']}:{sf['chain']}")
    if why and not control: red.append(f"the writer does not hold {a['who']}'s head: {why}")
use, want = int(s1["use"]), len(actors) + (1 if control else 0)
print(f"BAR use {use} of {len(actors)} objects, made by one member and used by another (PROTOCOL-43)")
if use != want:
    (fired if control and use == len(actors) else red).append(f"use {use}, want {want}")

# the cold reopens: a fresh supervisor + host over the writer's Store (spawn -> first reply to one
# `read` frame), then a fresh follow (spawn -> its first `nd read` answered)
t0 = time.monotonic_ns()
writer = start("writer", wsock, hides, W, ["serve", W])
s = bound(wsock, 120); s.settimeout(120)
s.sendall(struct.pack("<IB", 1, 3))  # one `read` frame, empty payload: any reply proves the open
try:
    hdr = s.recv(4); reopen = (time.monotonic_ns() - t0) / 1e6
    if len(hdr) < 4: red.append("reopen: writer closed the socket without a reply")
except socket.timeout:
    reopen = None; red.append("reopen: no reply in 120 s (silent)")
s.close()
for i, a in enumerate(actors[:1]):
    t0 = time.monotonic_ns()
    bound(start_follow(i, a), 120).close()
    freopen = None if nd_ok(a, ["read", a["obj"]]) is None else (time.monotonic_ns() - t0) / 1e6
    stop(f"follow{i}", follows[i])
stop("writer", writer)

# PERF-3: the tail's work re-derived at deployed parameters from this very Store (bench-count: the
# follower's audit under countingEnv and a counted verify, required to reach the host's own World;
# its toy-Store plant must be refused by name)
bc = run([count, W, os.path.join(stores, "count")] + (["--harness-control"] if control else []), timeout=600)
bcl = bc.stdout.splitlines()
for l in bcl:
    if l.startswith(("COUNT ", "PLANT ")): print(f"BAR {l.lower() if l.startswith('COUNT ') else l}")
if not any(l.startswith("PLANT toy-store refused") for l in bcl):
    red.append("bench-count: its toy-Store plant was not refused by name")
if control:
    # quiet, the control's shell names it missed (`count`), so the runner refuses the row
    if any(l.startswith("FAIL harness-control") for l in bcl): fired.append("bench-count harness-control")
elif bc.returncode or bcl[-1:] != ["BENCH-COUNT PASS"]:
    red.append(f"bench-count: {next((l for l in bcl if l.startswith('FAIL')), (bc.stderr or 'exit ' + str(bc.returncode)).strip())}")

N = records
def ratio(x): return f"{x / N:.3f}"
# STATUS records counts the records past the base (the open's fold), so the ratio is taken over the
# steps past it: after the mid-run seal, the second half
tailsteps = int(s1["steps"]) - int(s1["base_steps"])
counts = [("steps-per-command", steps),
          ("seg-bytes-per-command", int(s1["seg_bytes"]) - int(s0["seg_bytes"]))]
if io:
    counts += [("writer-read-syscalls-per-command", int(io["syscr"])), ("writer-write-syscalls-per-command", int(io["syscw"])),
               ("writer-read-bytes-per-command", int(io["rchar"])), ("writer-written-bytes-per-command", int(io["wchar"]))]
if sfds["writer"] is not None:
    counts += [("writer-supervisor-fds-per-command", sfds["writer"] - fds0["writer"]),
               ("follow-supervisor-fds-per-command", max(sfds[f"follow{i}"] - fds0[f"follow{i}"] for i in range(len(actors))))]
print(f"BAR count records-per-command {int(s1['records']) / tailsteps:.3f} ({s1['records']} records over the {tailsteps} steps past the base)")
if standing and not control: print(f"WASTE bar records-per-command {int(s1['records']) / tailsteps:.3f}")
for m, v in counts:
    print(f"BAR count {m} {ratio(v)} ({v} over {N} commands)")
    # the /proc io counts drift by one between identical runs: reported, not pinned (PERF-2)
    if standing and not control and not m.startswith(("writer-read-", "writer-write-", "writer-written-")):
        print(f"WASTE bar {m} {ratio(v)}")
print(f"BAR count stale-writes {staled[0]} stale-reruns {stale[0]} stale-after-sync {recur[0]} (writes that met `refused stale`; re-runs, each after one nd sync; re-runs stale again. A stale refusal is a recorded step and spends the member's refusal budget)")
print(f"BAR count reopen-tail-steps {int(s1['steps']) - int(s1['base_steps'])} (steps past the base the writer's reopen folds, no signature verified: HOST-22)")
tailb = int(s1['seg_bytes']) - int(s1['base_offset'])
print(f"BAR count reopen-tail-bytes {tailb} past the base at step {s1['base_steps']} (sealed mid-run, C6; not the tailMax worst cut)")
print(f"BAR count reopen-tail-bytes-per-command {ratio(tailb)}")
if standing and not control:
    print(f"WASTE bar reopen-tail-bytes-per-command {ratio(tailb)}")
    for l in bcl:   # verifies per step are exact; hashes per step vary with the drawn trie (reported)
        if l.startswith("WASTE bar audit-verifies-per-step "): print(l)
        elif l.startswith("WASTE bar audit-hashes-per-step "): print("BAR count" + l[len("WASTE bar"):] + " (varies with the run's random keys: not pinned)")
print("BAR unmeasured ticks per command: no deployed counter for the Lang machine (PERF-3 counts hashes and verifies)")
times.sort()
ms = lambda ns: round(ns / 1e6, 3)
pct = lambda q: times[min(len(times) - 1, (len(times) * q) // 100)] if times else 0
print(f"BAR write-n {len(times)}")
if len(times) != records: red.append(f"write-n {len(times)} of {records}")
print(f"BAR write-p50-ms {ms(pct(50))}")
print(f"BAR write-p99-ms {ms(pct(99))}")
print(f"BAR write-max-ms {ms(times[-1] if times else 0)}")
print(f"BAR reopen-ms {reopen if reopen is None else round(reopen, 3)}")
print(f"BAR follow-reopen-ms {freopen if freopen is None else round(freopen, 3)}")
print("FIRED " + "; ".join(fired))
print("RED " + "; ".join(red) if red else "OK")
PY
rc=$?
after=$(load)
grep -E '^(BAR|WASTE) ' "$root/out" | grep -v '^BAR verdict'
dev=$(df -P "$stores" | awk 'NR==2{print $1}')
echo "BAR scope three actors (two friends, the hosted-resident stand-in: a hosted-custody member driven by nd argv), one writer, one box, no ssh; OS cache warm at reopen"
echo "BAR mode $([ $standing = 1 ] && echo "standing (serial; counts judged by gates/waste.tsv, clock reported only)" || echo "full (concurrent)")"
echo "BAR device $(uname -sm) $dev $( [ "$(uname -s)" = Darwin ] && echo F_FULLFSYNC || echo fdatasync)"
echo "BAR sha $(git -C "$here" rev-parse --short HEAD 2>/dev/null || echo none)"
echo "BAR load-before $before ($(getconf _NPROCESSORS_ONLN) cpus)"
echo "BAR load-after $after"
p99=$(awk '$2=="write-p99-ms"{print $3}' "$root/out"); rms=$(awk '$2=="reopen-ms"{print $3}' "$root/out")
fms=$(awk '$2=="follow-reopen-ms"{print $3}' "$root/out")
echo "BAR limit write-p99-ms $p99 limit $wlim"
echo "BAR limit reopen-ms $rms limit $rlim"
echo "BAR limit follow-reopen-ms $fms limit $rlim"
over=$(awk -v w="$wlim" -v r="$rlim" '
  $2=="write-p99-ms" && $3+0 > w {o = o "; write-p99-ms " $3 " > " w}
  ($2=="reopen-ms" || $2=="follow-reopen-ms") && $3 != "None" && $3+0 > r {o = o "; " $2 " " $3 " > " r}
  END {print substr(o, 3)}' "$root/out")
status=$(grep -E '^(RED|OK)' "$root/out" | tail -1)
fired=$(grep '^FIRED ' "$root/out" | sed 's/^FIRED //')
quiet() { awk -v a="${before%% *}" -v b="${after%% *}" 'BEGIN{exit !(a < 2 && b < 2)}'; }
if [ $rc -ne 0 ] || [ -z "$status" ]; then
  verdict="RED $(grep -h 'BAR verdict RED' "$root/out" | head -1 | sed 's/^BAR verdict RED //')"
  [ "$verdict" = "RED " ] && verdict="RED driver-exit-$rc"
elif [ "${status%% *}" = RED ]; then verdict=$status
elif [ $control = 1 ]; then
  # all four planted expectations must have fired, each through its own comparator
  missed=""
  [ -n "$over" ] || missed="$missed limit"
  case $fired in *"use "*) ;; *) missed="$missed use" ;; esac
  case $fired in *"follow "*) ;; *) missed="$missed at-tip" ;; esac
  case $fired in *"bench-count harness-control"*) ;; *) missed="$missed count" ;; esac
  if [ -z "$missed" ]; then verdict="RED harness-control: $over; $fired"
  else  # a planted expectation stayed quiet: the control PASSES, so the runner reads no verdict of this row
    echo "BAR control: a planted expectation stayed quiet:$missed"; echo "BAR verdict PASS"; exit 0
  fi
elif [ $standing = 1 ]; then verdict=PASS
elif ! quiet; then verdict="UNJUDGED load1 ${before%% *}/${after%% *} >= 2${over:+ (over: $over)}"
elif [ -n "$over" ]; then verdict="RED $over"
else verdict=PASS
fi
if [ $record -eq 1 ]; then
  c() { awk -v m="$1" '$1=="BAR" && $2=="count" && $3==m {print $4}' "$root/out"; }
  printf 'run\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' "$(date -u +%Y-%m-%dT%H:%MZ)" \
    "$(git -C "$here" rev-parse --short HEAD)" "$(uname -sm) $([ $standing = 1 ] && echo standing || echo full) N=$records" \
    "$before / $after" "$p99" "$rms" "$fms" "$(awk '$2=="use"{print $3}' "$root/out")" \
    "$(c steps-per-command)" "$(c seg-bytes-per-command)" "$(c writer-supervisor-fds-per-command)" "${verdict}" >> "$here/gates/bar.tsv"
fi
echo "BAR verdict $verdict"
case $verdict in PASS) exit 0 ;; UNJUDGED*) exit 3 ;; *) exit 1 ;; esac
