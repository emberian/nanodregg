"""gates/readset.py — traced read-sets (GATES-20; design redregg/work/GATES-20-DESIGN.md, ROOT F1/F2).

Every verdict run executes under
`strace -f -qq -y --seccomp-bpf --decode-pids=pidns -e trace=%file,execve,getdents64,clone,clone3,fork,vfork,bind,unshare,setns,fchdir,open_tree,move_mount,fsopen,fsconfig,fsmount,mount_setattr,umount2`
(wrap). Its trace is reduced to a READ-SET over the judged tree (reduce):
  T = every tree path the run touched by name: opened, exec'd, probed and absent (ENOENT is a read of
      absence), and stat'ed, accessed or readlink'd BY CARGO: cargo's fingerprint compares a source's
      mtime and size, so cargo's stat is a proxy for the bytes, keyed by CONTENT like an open.
  K = every tree path some OTHER process only stat'ed, accessed or readlink'd (GATES-22, 20h (a)): a tree
      walk (devtools' workspace scan, a test's `exists`) reads what KIND of thing is there, not its bytes,
      so K is keyed by kind (DIR / FILE / ABSENT / LINK target / OTHER) and only an add, a delete or a
      kind change of the path reaches it. A K path also opened is in T (K -= T). A CARGO process is one
      that exec'd `cargo`, and its clones, until one exec's something else (the test binary cargo
      spawns is not cargo); a compile (C) stays C.
  C = the same, touched by a COMPILE: a process that exec'd rustc, and every process or thread it
      cloned (GATES-20d). A cargo row compiles only when its cache is cold, so C is present in one
      trace of a row and empty in the next; T is what the run reads whatever the cache holds (cargo's
      own fingerprint stats every source the crate's dep-info lists, so the sources stay in T).
  L = every tree directory it listed (an add or a remove in it can move the run);
  X = every binary under .lake/build/bin it exec'd.
  WR, O, NS = what the run WROTE (GATES-20g; never keyed: a write is no input), outside .lake/runs/ and
      .lake/cargo-target/, in the tree and under /tmp, /var/tmp and the home directory (an outside path is kept
      absolute, a tree path relative): O the outermost directories it MADE (mkdir = 0); WR every other path it
      created, opened for writing, truncated, removed, renamed or linked (either name) or bound an AF_UNIX socket
      at, not under a directory of O (what lies there is its own); RM the outermost paths it removed or renamed
      away (unlink, rmdir, a rename's source), its own directories' contents included (a row that empties a
      directory it made may empty another's inside it); LD every tree directory it LISTED (getdents64; L also
      holds a directory it only opened, and omits its own: L is an input set, LD a collision set). NS: some process of the run entered a mount
      namespace of its own (clone/unshare CLONE_NEWNS, setns). HOST_VIEW says every successful bind
      into bwrap's newroot had a traced host source: reads below it are translated through the bind
      table. NS writes remain unplaced, so runs.py still runs such a row alone.
  W = the waste rows (`op<TAB>metric`) the run MEASURED (its `WASTE` lines; runs.py adds it): no trace
      shows gates/waste.tsv, because the JUDGE reads it, not the run, yet its ceilings decide the row's
      verdict (GATES-20e, PERF-4's finding at 41e041f). The key holds each W row's ceiling and measured.
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
import threading

VERSION = b"GATES-20 traced key v5 (GATES-20m: namespace reads in host bind-source view)"
WASTE = "gates/waste.tsv"
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
        r = subprocess.run([p, "--decode-pids=pidns", "-V"], capture_output=True, text=True, timeout=30)
    except (OSError, subprocess.TimeoutExpired):
        return None
    # Without host-PID annotations, clone inside CLONE_NEWPID returns a namespace PID
    # different from the PID that prefixes its child's trace lines.
    return p if r.returncode == 0 else None


def wrap(strace: str, argv: list[str], out: str) -> list[str]:
    return [strace, "-f", "-qq", "-y", "--seccomp-bpf", "--decode-pids=pidns", "-e",
            "trace=%file,execve,getdents64,clone,clone3,fork,vfork,bind,unshare,setns,fchdir,open_tree,move_mount,fsopen,fsconfig,fsmount,mount_setattr,umount2",
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
RET = re.compile(r"=\s*(\d+)(?:<[^>]*>)?(?:\s+/\*\s*(\d+) in strace's PID NS \*/)?\s*$")
CLONES = ("clone", "clone3", "fork", "vfork")
COMPILERS = ("rustc",)


def _compiler(path: str) -> bool:
    return os.path.basename(path).startswith(COMPILERS)


# A call that reads what a path IS (its kind, its metadata, a link's target), never its bytes.
STATLIKE = ("stat", "lstat", "newfstatat", "fstatat64", "statx", "access", "faccessat", "faccessat2",
            "readlink", "readlinkat", "stat64", "lstat64")


# Why the last reduce held no read-set (runs.py prints it: a trace it cannot read is never silent). One per
# thread: rows are judged concurrently (GATES-20g), and one row's reason must never be printed for another's.
_TLS = threading.local()


def why_none() -> str | None:
    return getattr(_TLS, "why", None)


def _none(why: str) -> None:
    _TLS.why = why
    return None


# GATES-20g: the calls that write the path they name. An open writes when its flags say so; a mkdir makes a
# directory only when it returns 0; a bind writes only an AF_UNIX path (an abstract name, `@…`, is no file).
WRITES = ("unlink", "unlinkat", "rmdir", "rename", "renameat", "renameat2", "link", "linkat", "symlink",
          "symlinkat", "truncate", "creat", "mknod", "mknodat")
OPENS = ("open", "openat", "openat2")
WFLAGS = re.compile(r"\bO_(?:WRONLY|RDWR|CREAT|TRUNC)\b")
PAIR = re.compile(r'(?:AT_FDCWD|-?\d+)<((?:[^>\\]|\\.)*)>,\s*"((?:[^"\\]|\\.)*)"')
SUN = re.compile(r'sun_path="((?:[^"\\]|\\.)*)"')


def write_key(path: str, root: str) -> str | None:
    """A written absolute path as WR/O hold it: tree-relative inside the tree, absolute under /tmp, /var/tmp or the
    home directory; None for the run's own {fresh} (.lake/runs/), cargo's cache (.lake/cargo-target/, under
    cargo's own lock), the toolchain and the system."""
    path = os.path.normpath(path)
    if path == root or path.startswith(root + "/"):
        r = os.path.relpath(path, root)
        return None if r == "." or r.startswith(EXCL) or r + "/" in EXCL else r
    return path if _class(path) in ("tmp", "home") else None


def under(p: str, d: str) -> bool:
    """p is d or lies below it."""
    return p == d or p.startswith(d.rstrip("/") + "/")


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
    wrote: set[str] = set()     # GATES-20g: write_key of every non-mkdir write
    madew: set[str] = set()     # GATES-20g: write_key of every directory it made (tree and outside)
    ns: set[str] = set()        # GATES-20g: pids in a mount namespace of their own
    removed: set[str] = set()   # GATES-20g: write_key of every path removed or renamed away
    LD: set[str] = set()        # GATES-20g: every tree directory listed by getdents64, its own included
    pending: dict[tuple[str, str], str] = {}  # strace interleaves unfinished and resumed mount/clone calls
    binds: dict[str, dict[str, str]] = {}  # namespace destination -> host bind source, per pid
    pivots: dict[str, int] = {}  # bwrap first pivots to /tmp, then to /newroot
    mapped: set[str] = set()  # pids for which a host bind source was observed
    unknown_mount: set[str] = set()  # a bind into newroot whose source could not be placed
    comp: set[str] = set()   # pids of a compile: exec'd rustc, or cloned from such a pid
    cargo: set[str] = set()  # pids of cargo itself: exec'd cargo, or cloned from such a pid, until another exec
    K: set[str] = set()
    made: set[str] = set()   # directories this run created: what lies under them is its own output
    cwd: dict[str, str] = {}
    parsed = 0
    seen_pids: set[str] = set()

    def host_path(pid: str, path: str) -> str | None:
        path = os.path.normpath(path)
        if pid not in ns or pivots.get(pid, 0) == 0:
            return path
        if path == "/oldroot" or path.startswith("/oldroot/"):
            return path[len("/oldroot"):] or "/"
        phase = pivots.get(pid, 0)
        if phase == 1:
            if not (path == "/newroot" or path.startswith("/newroot/")):
                return None  # bwrap's pivot tmpfs, not a host path
            path = path[len("/newroot"):] or "/"
        elif path == "/newroot" or path.startswith("/newroot/"):
            path = path[len("/newroot"):] or "/"
        for dest, source in sorted(binds.get(pid, {}).items(), key=lambda item: -len(item[0])):
            if under(path, dest):
                return os.path.normpath(source + path[len(dest):])
        return None  # a namespace scaffold, tmpfs or devpts, not a host input

    def place(s: str, pid: str) -> str | None:
        s = host_path(pid, s)
        if s is None:
            return None
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
        seen_pids.add(m.group(1))
        pid, resumed, call, rest = m.group(1), m.group(2), m.group(3), m.group(4)
        call = call or resumed
        # strace prints setup calls in two lines on a busy box. Their arguments are on the first
        # and success/child pid on the resumed line; neither line alone establishes a bind.
        if call in (*CLONES, "mount", "pivot_root", "unshare", "setns") and not resumed and "<unfinished ...>" in rest:
            pending[(pid, call)] = rest.split("<unfinished ...>", 1)[0]
            continue
        if resumed and call in (*CLONES, "mount", "pivot_root", "unshare", "setns"):
            first = pending.pop((pid, call), None)
            if first is None:
                unknown_mount.add(pid)
                continue
            rest = first + rest
        if call in CLONES:
            r = RET.search(rest)
            if r:
                child = r.group(2) or r.group(1)
                if pid in ns or "CLONE_NEWNS" in rest:
                    ns.add(child)
                    binds[child] = dict(binds.get(pid, {}))
                    pivots[child] = pivots.get(pid, 0)
                    if pid in mapped:
                        mapped.add(child)
                    if pid in unknown_mount:
                        unknown_mount.add(child)
                if pid in comp:
                    comp.add(child)
                if pid in cargo:
                    cargo.add(child)
                if child not in cwd and pid in cwd:
                    cwd[child] = cwd[pid]
            continue
        if call in ("unshare", "setns"):
            if rest.rstrip().endswith("= 0") and ("CLONE_NEWNS" in rest or call == "setns"):
                ns.add(pid)
                if call == "setns":
                    unknown_mount.add(pid)  # a foreign namespace has no traced bind table
            continue
        if call in ("open_tree", "move_mount", "fsopen", "fsconfig", "fsmount", "mount_setattr"):
            if pid in ns:
                unknown_mount.add(pid)  # the new mount API has no bind mapping in this reducer
            continue
        if call == "umount2":
            if pid in ns and not (rest.startswith('"oldroot"') or rest.startswith('"."')):
                unknown_mount.add(pid)
            continue
        if call == "pivot_root":
            if rest.rstrip().endswith("= 0"):
                ns.add(pid)
                pivots[pid] = pivots.get(pid, 0) + 1
            continue
        if call == "mount":
            if rest.rstrip().endswith("= 0") and "MS_BIND" in rest and "MS_REMOUNT" not in rest:
                names = STR.findall(rest)
                if len(names) >= 2 and (names[1] == "/newroot" or names[1].startswith("/newroot/")):
                    src, dest = names[:2]
                    if "\\" in src or "\\" in dest:
                        unknown_mount.add(pid)
                        continue
                    if src.startswith("/oldroot/"):
                        source = src[len("/oldroot"):]
                    elif pivots.get(pid, 0) == 0 and src.startswith("/"):
                        source = src
                    else:
                        unknown_mount.add(pid)
                        continue
                    target = dest[len("/newroot"):]
                    ns.add(pid)
                    binds.setdefault(pid, {})[os.path.normpath(target)] = os.path.normpath(source)
                    mapped.add(pid)
                    # The bind source itself is an input, even when the child reads by the
                    # destination's name. Child path reads below it are translated by host_path.
                    r = place(source, "")  # empty pid is the host view
                    if r is not None:
                        T.add(r)
                elif pivots.get(pid, 0) >= 1:
                    unknown_mount.add(pid)  # a later bind outside newroot is not translated
            continue
        if resumed:
            continue   # ordinary calls' arguments were placed from their unfinished line
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
        if call in ("getdents64", "fchdir"):
            f = FDARG.match(rest)
            if f:
                if "\\" in f.group(1):
                    return _none(f"an escaped name: {f.group(1)[:60]}")
                if call == "fchdir":
                    if rest.rstrip().endswith("= 0"):
                        cwd[pid] = os.path.normpath(f.group(1))   # GATES-20g: `mkdir -p` walks by fchdir
                    continue
                r = place(f.group(1), pid)
                if r is not None:
                    L.add(r)
                    LD.add(r)
            continue
        base = cwd.get(pid, root)
        if call == "bind":
            sp = SUN.search(rest)
            if sp and rest.rstrip().endswith("= 0") and not sp.group(1).startswith("@") and pid not in ns:
                if "\\" in sp.group(1):
                    return _none(f"an escaped name: {sp.group(1)[:60]}")
                wk = write_key(os.path.join(base, sp.group(1)), root)
                if wk is not None:
                    wrote.add(wk)
            continue
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
        mk = call in ("mkdir", "mkdirat") and rest.rstrip().endswith("= 0")
        if pid not in ns and (mk or call in WRITES or (call in OPENS and WFLAGS.search(args))):
            # every name the call writes: the first (placed as a read is), and a rename's or link's second
            ws = [os.path.join(base, s) if s else base]
            if call in ("rename", "link", "symlink") and len(ss) > 1:
                ws.append(os.path.join(cwd.get(pid, root), ss[1]))
            elif call in ("renameat", "renameat2", "linkat", "symlinkat"):
                ps = PAIR.findall(rest)
                if len(ps) > 1:
                    ws.append(os.path.join(ps[1][0], ps[1][1]))
                elif len(ss) > 1:
                    ws.append(os.path.join(cwd.get(pid, root), ss[1]))
            for w in ws:
                if "\\" in w:
                    return _none(f"an escaped name: {w[:60]}")
                wk = write_key(w, root)
                if wk is not None:
                    (madew if mk else wrote).add(wk)
                    if w is ws[0] and call in ("unlink", "unlinkat", "rmdir", "rename", "renameat", "renameat2"):
                        removed.add(wk)
        if call in ("execve", "execveat") and rest.rstrip().endswith("= 0"):
            if os.path.basename(s) == "cargo":
                cargo.add(pid)
            else:
                cargo.discard(pid)
        s = os.path.join(base, s) if s else base
        if call == "chdir" and rest.rstrip().endswith("= 0"):
            cwd[pid] = os.path.normpath(s)   # a bare name after it is relative to this
        r = place(s, pid)
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
        if call in STATLIKE and pid not in comp and pid not in cargo:
            K.add(r)
            continue
        (C if pid in comp else T).add(r)
    if parsed == 0:
        return _none("no strace line in the trace")
    host_view = not ns or all(p in seen_pids and p in mapped and p not in unknown_mount for p in ns)
    own = lambda r: any(r == m or r.startswith(m + "/") for m in made)
    T = {r for r in T if not own(r)}
    C = {r for r in C if not own(r)} - T
    L = {r for r in L if not own(r)}
    K = {r for r in K if not own(r)} - T - C
    O = {m for m in madew if not any(m != x and under(m, x) for x in madew)}
    WR = {w for w in wrote if not any(under(w, m) for m in madew)}
    RM = {x for x in removed if not any(x != y and under(x, y) for y in removed)}
    return {"T": sorted(T), "C": sorted(C), "K": sorted(K), "L": sorted(L), "X": sorted(X),
            "WR": sorted(WR), "O": sorted(O), "RM": sorted(RM), "LD": sorted(LD), "NS": bool(ns), "HOST_VIEW": host_view, "outside": outside,
            "outside_paths": {c: sorted(v)[:50] for c, v in outside_paths.items()}}


def keyable(rs: dict) -> bool:
    """A traced record may narrow/reuse only when its namespace status is explicit and,
    for a namespace, every bind source was placed in the host view. Missing NS is a record
    from before GATES-20g; missing HOST_VIEW on NS is a record from before GATES-20m."""
    return rs.get("NS") is False or (rs.get("NS") is True and rs.get("HOST_VIEW") is True)


def union(sets: list[dict | None]) -> dict | None:
    """A row's read-set: the union over its runs (control included). One run without a read-set and
    the row has none."""
    if not sets or any(s is None for s in sets):
        return None
    out = {"T": set(), "C": set(), "K": set(), "L": set(), "X": set(), "WR": set(), "O": set(), "RM": set(),
           "LD": set(), "outside": {},
           "outside_paths": {}}
    ns = any(s.get("NS") for s in sets)
    host_view = all(s.get("HOST_VIEW") is True for s in sets)
    for s in sets:
        for k in ("T", "C", "K", "L", "X", "WR", "O", "RM", "LD"):
            out[k] |= set(s.get(k, []))
        for c, n in s["outside"].items():
            out["outside"][c] = out["outside"].get(c, 0) + n
        for c, ps in s.get("outside_paths", {}).items():
            out["outside_paths"].setdefault(c, set()).update(ps)
    return {"T": sorted(out["T"]), "C": sorted(out["C"] - out["T"]), "K": sorted(out["K"] - out["T"] - out["C"]),
            "L": sorted(out["L"]), "X": sorted(out["X"]),
            # one run's own directory may hold another run's write: the row's O is the union's outermost
            "O": sorted(m for m in out["O"] if not any(m != x and under(m, x) for x in out["O"])),
            "WR": sorted(w for w in out["WR"] if not any(under(w, m) for m in out["O"])),
            "RM": sorted(x for x in out["RM"] if not any(x != y and under(x, y) for y in out["RM"])),
            "LD": sorted(out["LD"]), "NS": ns, "HOST_VIEW": host_view,
            "outside": out["outside"],
            "outside_paths": {c: sorted(v)[:50] for c, v in out["outside_paths"].items()}}


def kind(root: str, r: str) -> str:
    """What a stat sees of a path, never its bytes: DIR, FILE, ABSENT, LINK <target>, OTHER."""
    p = os.path.join(root, r)
    try:
        st = os.lstat(p)
    except FileNotFoundError:
        return "ABSENT"
    except OSError as e:
        return f"UNREADABLE {e.errno}"
    import stat as st_
    if st_.S_ISLNK(st.st_mode):
        return "LINK " + os.readlink(p)
    if st_.S_ISDIR(st.st_mode):
        return "DIR"
    if st_.S_ISREG(st.st_mode):
        return "FILE"
    return "OTHER"


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
    for r in rs.get("K", []):
        put("K " + r + " " + kind(root, r))
    for d in rs["L"]:
        p = os.path.join(root, d)
        put("L " + d + " " + ("\0".join(sorted(os.listdir(p))) if os.path.isdir(p) else "ABSENT"))
    for b in rs["X"]:
        put("X " + b + " " + _file(root, BIN + b))
    if rs.get("W"):
        rows = waste_rows(_text(root, WASTE))
        for w in rs["W"]:
            put("W " + w + " " + "\t".join(rows.get(w, ("ABSENT",))))
    return h.hexdigest()


def _text(root: str, rel: str) -> str:
    try:
        return open(os.path.join(root, rel), encoding="utf-8").read()
    except OSError:
        return ""


def waste_rows(text: str) -> dict[str, tuple[str, ...]]:
    """gates/waste.tsv as the JUDGE reads it: `op<TAB>metric` -> (ceiling, measured). The source prose is
    not a judge input (waste.py compares the numbers only)."""
    out = {}
    for line in text.splitlines():
        f = line.split("\t")
        if line.startswith("#") or len(f) < 4:
            continue
        out[f[0] + "\t" + f[1]] = (f[2], f[3])
    return out


def waste_changed(old: str, new: str) -> set[str]:
    """The waste rows (`op<TAB>metric`) whose ceiling or measured value differs, or that were added or removed."""
    a, b = waste_rows(old), waste_rows(new)
    return {k for k in set(a) | set(b) if a.get(k) != b.get(k)}


def touched_by(rs: dict, changed: list[str], added_or_deleted: set[str]) -> str | None:
    """Why a change reaches a read-set (a path it touched, a path it stat'ed only (K) added, deleted
    or changed in kind, or an add/delete in a directory it listed), or None."""
    t = set(rs["T"]) | set(rs.get("C", []))
    for p in changed:
        if p in t:
            return f"changed path {p} (traced)"
    k = set(rs.get("K", []))
    for p in sorted(added_or_deleted):
        if p in k:
            return f"added/removed/re-kinded {p}, which it stat'ed (traced)"
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
    pairs = [("T", "touched"), ("L", "listed"), ("X", "exec'd"), ("K", "stat'ed")]
    if recorded.get("C"):
        pairs.append(("C", "compiled from"))
    have = set(recorded.get("T", [])) | set(recorded.get("C", []))
    # a fresh stat-only path is inside the record when the record read it at all (K, T or C); a fresh T path
    # the record only stat'ed IS an extra (its bytes were never keyed)
    def implied(d: str) -> bool:
        return root is not None and os.path.isdir(os.path.join(root, d)) and any(
            p.startswith(d + "/") and os.path.isfile(os.path.join(root, p)) for p in have)
    for k, what in pairs:
        extra = sorted(p for p in set(fresh.get(k, [])) - set(recorded.get(k, []))
                       - (set(recorded.get("T", [])) if k == "C" else set()) - (have if k == "K" else set())
                       if k not in ("T", "C", "K") or not implied(p))
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
