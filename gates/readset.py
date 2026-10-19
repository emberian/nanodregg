"""gates/readset.py — traced read-sets (GATES-20; design redregg/work/GATES-20-DESIGN.md, ROOT F1/F2).

Every verdict run executes under `strace -f -qq -y --seccomp-bpf -e trace=%file,execve,getdents64,clone,clone3,fork,vfork`
(wrap). Its trace is reduced to a READ-SET over the judged tree (reduce):
  T = every tree path the run touched by name: opened, exec'd, stat'ed, accessed, readlink'd, probed
      and absent (ENOENT is a read of absence). A stat is keyed by CONTENT, like an open: cargo's
      fingerprint compares a source's mtime and size, so a stat is a proxy for the bytes.
  C = the same, touched by a COMPILE: a process that exec'd rustc, and every process or thread it
      cloned (GATES-20d). A cargo row compiles only when its cache is cold, so C is present in one
      trace of a row and empty in the next; T is what the run reads whatever the cache holds (cargo's
      own fingerprint stats every source the crate's dep-info lists, so the sources stay in T).
  L = every tree directory it listed (an add or a remove in it can move the run);
  X = every binary under .lake/build/bin it exec'd.
Excluded: .lake/runs/ (the run's own scratch, made fresh per run), .lake/cargo-target/ (cargo's
cache: derived, and a source change reaches it only through T, which cargo stats), and everything under
a directory the run itself created (mkdir = 0: its own output, e.g. host-file-sim's
.lake/host-file-sim/run-<random>, which the standing re-trace check read as nondeterminism).
Paths outside the tree are counted by class (F2): toolchain, tmp, home, system. Standing REPORTS the
non-toolchain ones; turning that into RED is GATES-20c (trigger: the census is sorted).

A read-set's KEY on a tree (key): sha256 over the row's line, the rustc/cargo/python versions (tools),
the runner's bytes, each T and C path's bytes
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

VERSION = b"GATES-20 traced key v2 (GATES-20d: compile reads C)"
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
    return [strace, "-f", "-qq", "-y", "--seccomp-bpf", "-e", "trace=%file,execve,getdents64,clone,clone3,fork,vfork",
            "-e", "signal=none",
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
RET = re.compile(r'=\s*(\d+)(?:<[^>]*>)?\s*$')
CLONES = ("clone", "clone3", "fork", "vfork")
COMPILERS = ("rustc",)


def _compiler(path: str) -> bool:
    return os.path.basename(path).startswith(COMPILERS)


# Why the last reduce held no read-set (runs.py prints it: a trace it cannot read is never silent).
WHY: list[str] = []


def _none(why: str) -> None:
    WHY[:] = [why]
    return None


def reduce(trace: str, root: str) -> dict | None:
    """The read-set of one trace file, or None when there is none to trust (missing, empty, not
    strace output, or a name strace had to escape): the caller then holds no read-set for the row,
    and the static rules apply.
    Paths are placed with strace -y's annotations: a `*at` call's directory fd prints its path
    (`AT_FDCWD</cwd>`, `3</dir>`), so a name relative to a directory fd or to a chdir'd cwd lands
    where it was opened. A relative name with no annotation is resolved against the last cwd that
    process showed (the run's cwd, the tree root, before any)."""
    root = os.path.realpath(root)
    try:
        lines = open(trace, encoding="utf-8", errors="replace").read().splitlines()
    except OSError:
        return _none("no trace file")
    T, C, L, X, outside, outside_paths = set(), set(), set(), set(), {}, {}
    comp: set[str] = set()   # pids of a compile: exec'd rustc, or cloned from such a pid
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
        if call in CLONES:
            # the child's pid is the return value (on the call's line, or on its `resumed` line)
            r = RET.search(rest)
            if r and pid in comp:
                comp.add(r.group(1))
            continue
        if resumed:
            continue   # the call's arguments were printed on its `<unfinished ...>` line
        # A name strace had to escape (a backslash: a byte it would not print, a quote) is not a path this
        # reducer can place: strace reads a string argument from the tracee's memory, and a thread that
        # rewrites it meanwhile leaves bytes (145283a's standing: `O\222\17\333\5` in members). The
        # whole trace is then untrusted (None: the static rules), never the one name dropped (GATES-20d).
        # Checked on every name this reducer places or resolves against: the path argument, the
        # directory-fd and cwd annotations (an execve's argv may hold backslashes and is not a name).
        c = CWD.search(rest)
        if c:
            if "\\" in c.group(1):
                return _none(f"an escaped name: {c.group(1)[:60]}")
            cwd[pid] = c.group(1)
        if call == "getdents64":
            f = FDARG.match(rest)
            if f:
                if "\\" in f.group(1):
                    return _none(f"an escaped name: {f.group(1)[:60]}")
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
        if "\\" in s or "\\" in base:
            return _none(f"an escaped name: {(s if chr(92) in s else base)[:60]}")
        if call in ("execve", "execveat") and _compiler(s):
            comp.add(pid)
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
        (C if pid in comp else T).add(r)
    if parsed == 0:
        return _none("no strace line in the trace")
    own = lambda r: any(r == m or r.startswith(m + "/") for m in made)
    T = {r for r in T if not own(r)}
    C = {r for r in C if not own(r)} - T
    L = {r for r in L if not own(r)}
    return {"T": sorted(T), "C": sorted(C), "L": sorted(L), "X": sorted(X), "outside": outside,
            "outside_paths": {c: sorted(v)[:50] for c, v in outside_paths.items()}}


def union(sets: list[dict | None]) -> dict | None:
    """A row's read-set: the union over its runs (control included). One run without a read-set and
    the row has none."""
    if not sets or any(s is None for s in sets):
        return None
    out = {"T": set(), "C": set(), "L": set(), "X": set(), "outside": {}, "outside_paths": {}}
    for s in sets:
        for k in ("T", "C", "L", "X"):
            out[k] |= set(s.get(k, []))
        for c, n in s["outside"].items():
            out["outside"][c] = out["outside"].get(c, 0) + n
        for c, ps in s.get("outside_paths", {}).items():
            out["outside_paths"].setdefault(c, set()).update(ps)
    return {"T": sorted(out["T"]), "C": sorted(out["C"] - out["T"]), "L": sorted(out["L"]), "X": sorted(out["X"]),
            "outside": out["outside"],
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
    for r in rs.get("C", []):
        put("C " + r + " " + _file(root, r))
    for d in rs["L"]:
        p = os.path.join(root, d)
        put("L " + d + " " + ("\0".join(sorted(os.listdir(p))) if os.path.isdir(p) else "ABSENT"))
    for b in rs["X"]:
        put("X " + b + " " + _file(root, BIN + b))
    return h.hexdigest()


def touched_by(rs: dict, changed: list[str], added_or_deleted: set[str]) -> str | None:
    """Why a change reaches a read-set (a path it touched, or an add/delete in a directory it
    listed), or None."""
    t = set(rs["T"]) | set(rs.get("C", []))
    for p in changed:
        if p in t:
            return f"changed path {p} (traced)"
    ls = set(rs["L"])
    for p in sorted(added_or_deleted):
        if os.path.dirname(p) in ls or (os.path.dirname(p) == "" and "." in ls):
            return f"added/removed {p} in a listed directory (traced)"
    return None


def subset_violation(fresh: dict, recorded: dict, root: str | None = None) -> str | None:
    """The standing re-trace check: a fresh read-set must lie inside every stored one valid on this tree
    (the run consults nothing the record lacks). Anything more is a forged or narrowed record, a
    nondeterministic run, or an input channel the record missed. T, L and X are compared always.
    C, a compile's reads, only when the record compiled too (GATES-20d): whether cargo compiles is its
    cache's state, not the run's, so a record traced on a warm cache holds no C, and a compile on a cold
    one reads rustc's module probes and directories (measured: every extra of 13 cargo rows at 145283a was
    a directory or an absent `X/mod.rs` probe). A compile against a compile is still compared.
    One touch is IMPLIED, not extra: a directory D touched by name when the record touched a path under
    D that is a file on this tree (ROOT the tree the key was re-computed on). That file's key pins its
    bytes, so it exists, so D is a directory; a stat or readlink of D reads nothing more (cargo resolves
    each dep-info path's ancestors after a compile: `readlink launcher/tests` = EINVAL)."""
    pairs = [("T", "touched"), ("L", "listed"), ("X", "exec'd")]
    if recorded.get("C"):
        pairs.append(("C", "compiled from"))
    have = set(recorded.get("T", [])) | set(recorded.get("C", []))
    def implied(d: str) -> bool:
        return root is not None and os.path.isdir(os.path.join(root, d)) and any(
            p.startswith(d + "/") and os.path.isfile(os.path.join(root, p)) for p in have)
    for k, what in pairs:
        extra = sorted(p for p in set(fresh.get(k, [])) - set(recorded.get(k, []))
                       - (set(recorded.get("T", [])) if k == "C" else set()) if k not in ("T", "C") or not implied(p))
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
