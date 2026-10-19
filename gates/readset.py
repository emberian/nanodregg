"""gates/readset.py — traced read-sets (GATES-20; design redregg/work/GATES-20-DESIGN.md, ROOT F1/F2).

Every verdict run executes under `strace -f -qq -y --seccomp-bpf -e trace=%file,execve,getdents64` (wrap). Its trace
is reduced to a READ-SET over the judged tree (reduce):
  T = every tree path the run touched by name: opened, exec'd, stat'ed, accessed, readlink'd, probed
      and absent (ENOENT is a read of absence). A stat is keyed by CONTENT, like an open: cargo's
      fingerprint compares a source's mtime and size, so a stat is a proxy for the bytes.
  L = every tree directory it listed (an add or a remove in it can move the run);
  X = every binary under .lake/build/bin it exec'd.
Excluded: .lake/runs/ (the run's own scratch, made fresh per run), .lake/cargo-target/ (cargo's
cache: derived, and a source change reaches it only through T, which cargo stats), and everything under
a directory the run itself created (mkdir = 0: its own output, e.g. host-file-sim's
.lake/host-file-sim/run-<random>, which the standing re-trace check read as nondeterminism).
Paths outside the tree are counted by class (F2): toolchain, tmp, home, system. Standing REPORTS the
non-toolchain ones; turning that into RED is GATES-20b (trigger: the census is sorted).

A read-set's KEY on a tree (key): sha256 over the row's line, the rustc/cargo/python versions (tools),
the runner's bytes, each T path's bytes
(or ABSENT, or DIR), each L directory's sorted names, and each X binary's bytes, all read from the
materialized tree's disk (it is exactly the judged tree plus its .lake). Two trees with the same key
for a read-set present a deterministic run with the same inputs, so it reads the same things and gives
the same verdict. An invalid or missing read-set falls back to the static rules (fail-closed).
"""
import hashlib
import json
import os
import re
import shutil
import subprocess

VERSION = b"GATES-20 traced key v1"
EXCL = (".lake/runs/", ".lake/cargo-target/")
BIN = ".lake/build/bin/"
RUNNER = ("gates/runs.py", "gates/tree.py", "gates/readset.py")
LINE = re.compile(r"^(\d+)\s+(?:<\.\.\. (\w+) resumed>|(\w+)\()(.*)$")
STR = re.compile(r'"((?:[^"\\]|\\.)*)"')
TOOLCHAIN = (".elan", ".cargo", ".rustup")


def available() -> str | None:
    """The strace this box judges with, or None (then every run is untraced: static rules)."""
    p = shutil.which("strace")
    if not p:
        return None
    try:
        r = subprocess.run([p, "-V"], capture_output=True, text=True, timeout=30)
    except (OSError, subprocess.TimeoutExpired):
        return None
    return p if r.returncode == 0 else None


def wrap(strace: str, argv: list[str], out: str) -> list[str]:
    return [strace, "-f", "-qq", "-y", "--seccomp-bpf", "-e", "trace=%file,execve,getdents64", "-e", "signal=none",
            "-s", "4096", "-o", out] + list(argv)


def _class(path: str) -> str:
    home = os.path.expanduser("~") + "/"
    if path.startswith(home):
        return "toolchain" if path[len(home):].split("/")[0] in TOOLCHAIN else "home"
    if path.startswith(("/tmp/", "/var/tmp/")):
        return "tmp"
    return "system"


DIRFD = re.compile(r'^(?:AT_FDCWD|-?\d+)<((?:[^>\\]|\\.)*)>,\s*')
FDARG = re.compile(r'^-?\d+<((?:[^>\\]|\\.)*)>')
CWD = re.compile(r'AT_FDCWD<((?:[^>\\]|\\.)*)>')


def reduce(trace: str, root: str) -> dict | None:
    """The read-set of one trace file, or None when there is none to trust (missing, empty, or not
    strace output): the caller then holds no read-set for the row, and the static rules apply.
    Paths are placed with strace -y's annotations: a `*at` call's directory fd prints its path
    (`AT_FDCWD</cwd>`, `3</dir>`), so a name relative to a directory fd or to a chdir'd cwd lands
    where it was opened. A relative name with no annotation is resolved against the last cwd that
    process showed (the run's cwd, the tree root, before any)."""
    root = os.path.realpath(root)
    try:
        lines = open(trace, encoding="utf-8", errors="replace").read().splitlines()
    except OSError:
        return None
    T, L, X, outside, outside_paths = set(), set(), set(), {}, {}
    made: set[str] = set()   # directories this run created: what lies under them is its own output
    cwd: dict[str, str] = {}
    parsed = 0

    def place(s: str) -> None:
        nonlocal T
        s = os.path.normpath(s)
        if s != root and not s.startswith(root + "/"):
            c = _class(s)
            outside[c] = outside.get(c, 0) + 1
            if c in ("tmp", "home"):
                outside_paths.setdefault(c, set()).add(s)
            return None
        r = os.path.relpath(s, root)
        if r == "." or r.startswith(EXCL) or r + "/" in EXCL:
            return None
        return r

    for line in lines:
        m = LINE.match(line)
        if not m:
            continue
        parsed += 1
        pid, resumed, call, rest = m.group(1), m.group(2), m.group(3), m.group(4)
        call = call or resumed
        if resumed:
            continue   # the call's arguments were printed on its `<unfinished ...>` line
        c = CWD.search(rest)
        if c:
            cwd[pid] = c.group(1)
        if call == "getdents64":
            f = FDARG.match(rest)
            if f:
                r = place(f.group(1))
                if r is not None:
                    L.add(r)
            continue
        base = cwd.get(pid, root)
        args = rest
        d = DIRFD.match(rest)
        if d and (call.endswith("at") or call in ("statx", "openat2", "faccessat2", "execveat", "renameat2")):
            base, args = d.group(1), rest[d.end():]
        ss = STR.findall(args)
        if not ss:
            continue
        s = ss[0]
        s = os.path.join(base, s) if s else base
        r = place(s)
        if r is None:
            continue
        if call in ("mkdir", "mkdirat"):
            if rest.rstrip().endswith("= 0"):
                made.add(r)
            continue
        if "O_DIRECTORY" in rest:
            L.add(r)
            continue
        if call in ("execve", "execveat") and r.startswith(BIN):
            X.add(r[len(BIN):])
        T.add(r)
    if parsed == 0:
        return None
    own = lambda r: any(r == m or r.startswith(m + "/") for m in made)
    T = {r for r in T if not own(r)}
    L = {r for r in L if not own(r)}
    return {"T": sorted(T), "L": sorted(L), "X": sorted(X), "outside": outside,
            "outside_paths": {c: sorted(v)[:50] for c, v in outside_paths.items()}}


def union(sets: list[dict | None]) -> dict | None:
    """A row's read-set: the union over its runs (control included). One run without a read-set and
    the row has none."""
    if not sets or any(s is None for s in sets):
        return None
    out = {"T": set(), "L": set(), "X": set(), "outside": {}, "outside_paths": {}}
    for s in sets:
        for k in ("T", "L", "X"):
            out[k] |= set(s[k])
        for c, n in s["outside"].items():
            out["outside"][c] = out["outside"].get(c, 0) + n
        for c, ps in s.get("outside_paths", {}).items():
            out["outside_paths"].setdefault(c, set()).update(ps)
    return {"T": sorted(out["T"]), "L": sorted(out["L"]), "X": sorted(out["X"]), "outside": out["outside"],
            "outside_paths": {c: sorted(v)[:50] for c, v in out["outside_paths"].items()}}


def _file(root: str, r: str) -> str:
    p = os.path.join(root, r)
    if os.path.isdir(p):
        return "DIR"
    try:
        with open(p, "rb") as fh:
            return hashlib.sha256(fh.read()).hexdigest()
    except FileNotFoundError:
        return "ABSENT"
    except OSError as e:
        return f"UNREADABLE {e.errno}"


_TOOLS: list[str] = []


def tools() -> str:
    """The toolchain outside the tree that a run's verdict depends on and no tree path names: rustc
    and cargo (a cargo row rebuilds its test under them; .lake/cargo-target is excluded) and the
    Python that runs the runner. The Lean toolchain is lean-toolchain (a tree path lake reads) and the
    X binaries' bytes."""
    if not _TOOLS:
        out = []
        for argv in (["rustc", "-Vv"], ["cargo", "-V"]):
            try:
                r = subprocess.run(argv, capture_output=True, text=True, timeout=60)
                out.append(f"{argv[0]} exit {r.returncode}: {r.stdout.strip()}")
            except (OSError, subprocess.TimeoutExpired) as e:
                out.append(f"{argv[0]}: {e}")
        import sys
        out.append("python " + sys.version)
        _TOOLS.append("\n".join(out))
    return _TOOLS[0]


def key(rs: dict, root: str, row_line: str) -> str:
    h = hashlib.sha256(VERSION)
    def put(x: str) -> None:
        b = x.encode()
        h.update(len(b).to_bytes(8, "big"))
        h.update(b)
    put(row_line)
    put(tools())
    for r in RUNNER:
        put(r + " " + _file(root, r))
    for r in rs["T"]:
        put("T " + r + " " + _file(root, r))
    for d in rs["L"]:
        p = os.path.join(root, d)
        put("L " + d + " " + ("\0".join(sorted(os.listdir(p))) if os.path.isdir(p) else "ABSENT"))
    for b in rs["X"]:
        put("X " + b + " " + _file(root, BIN + b))
    return h.hexdigest()


def touched_by(rs: dict, changed: list[str], added_or_deleted: set[str]) -> str | None:
    """Why a change reaches a read-set (a path it touched, or an add/delete in a directory it
    listed), or None."""
    t = set(rs["T"])
    for p in changed:
        if p in t:
            return f"changed path {p} (traced)"
    ls = set(rs["L"])
    for p in sorted(added_or_deleted):
        if os.path.dirname(p) in ls or (os.path.dirname(p) == "" and "." in ls):
            return f"added/removed {p} in a listed directory (traced)"
    return None


def subset_violation(fresh: dict, recorded: dict) -> str | None:
    """The standing re-trace check: under an equal key a fresh read-set must lie inside the recorded
    one (a run may read less, e.g. cargo with a warm cache; never more). Anything more is a forged
    or narrowed record, a nondeterministic run, or an input channel the record missed."""
    for k, what in (("T", "touched"), ("L", "listed"), ("X", "exec'd")):
        extra = sorted(set(fresh[k]) - set(recorded[k]))
        if extra:
            return f"{what} {extra[0]}{f' (+{len(extra) - 1} more)' if len(extra) > 1 else ''}"
    return None


# The store: <common>/nanodregg-traces/<row>/<key>.json = {"tree": OID, "row", "line", "readset"}. A file is named
# by the key its read-set had on the tree it was traced on.
def safe(row: str) -> str:
    return re.sub(r"[^A-Za-z0-9_.-]", "_", row)


def store(store_dir: str, row: str, k: str, tree_oid: str, line: str, rs: dict) -> None:
    d = os.path.join(store_dir, safe(row))
    os.makedirs(d, exist_ok=True)
    tmp = os.path.join(d, f".{k}.{os.getpid()}")
    with open(tmp, "w", encoding="utf-8") as fh:
        json.dump({"tree": tree_oid, "row": row, "line": line, "readset": rs}, fh)
    os.replace(tmp, os.path.join(d, k + ".json"))


def stored(store_dir: str, row: str) -> list[tuple[str, dict]]:
    """(key, record) for the row, newest first."""
    d = os.path.join(store_dir, safe(row))
    if not os.path.isdir(d):
        return []
    out = []
    for n in os.listdir(d):
        if n.endswith(".json") and not n.startswith("."):
            p = os.path.join(d, n)
            try:
                out.append((os.path.getmtime(p), n[:-5], json.load(open(p, encoding="utf-8"))))
            except (OSError, ValueError):
                continue
    return [(k, r) for _, k, r in sorted(out, key=lambda x: x[0], reverse=True)]
