"""gates/runs.py TREE [--changed FILE] [--waste-out FILE] — the verdict runs (sims, journeys, rows,
plants): every lean_exe whose answer is a verdict, run over the built TREE as gates/runs.tsv says.

gates/runs.tsv rows, `exe<TAB>runs<TAB>pass<TAB>control`:
  runs  the argument lists, separated by ` ; `, each one run of the exe (`(none)`: no arguments). `{host}` is the built
        `host` exe and `{fresh}` a fresh directory under TREE/.lake/runs (it does not exist when the
        run starts; it is removed after). `-` = not a verdict exe (a generator or the deployed
        binary), with the reason in `pass`.
  pass  the last line a passing run prints.
  control  the KNOWN-RED control (GATES-15): one argument list whose run must read RED with a
        line naming `harness-control` (the exe adds one expectation nothing meets and judges it on
        its ordinary path). `-` on a `-` row. A runner that cannot read a failure is not a runner
        (CLIENT-6's mutation harness read every mutation green behind `cargo test -q`), so the
        control runs FIRST and an exe whose control does not read red has none of its verdicts
        read: the control is `RED(harness: the known-red control passed: …)` and each run `UNREAD`.
Every lean_exe has exactly one row (check.py's `runs` gate), so a new exe is classified when it lands.

A row `cargo:CRATE:TEST` is a Rust integration test that drives built Lean exes (HOSTING's
physical isolation tooth, launcher/tests/isolation.rs): `runs` names those exes (comma-separated),
`pass` is `exit 0`, `control` is `nobin RED` (the test drives the exes it names: run with
ND_LEAN_BIN = an empty directory it must read red, or it never drove them) or `nobin ok` (it runs
no exe: it reads a generated table, and the exes it names only select it; with no binaries it must
still pass, so the declaration is measured too). The cargo reader itself is proven each
invocation: whenever a cargo row runs, at least one `nobin RED` control runs first (the table's
first such row when none is selected). It runs `cargo test --locked --manifest-path Cargo.toml -p PACKAGE --test TEST`
(PACKAGE = CRATE/Cargo.toml's name; the root workspace) with
ND_LEAN_BIN = the tree's built bin directory, after the build; it is selected when CRATE/ changed or
any exe it drives is selected.

A row `script:PATH` is a script of this tree that drives the built Lean exes and the client binaries
over real sockets (PERF-2: scripts/bar.sh, THE BAR at a bounded scale). `runs` are its argument lists
as for an exe (`{fresh}` is a fresh directory that exists when the run starts and is removed after),
`pass` its last stdout line, and `control` its known-red control (an argument list with
--harness-control, read exactly as an exe's). It runs with ND_LEAN_BIN = the built bin directory and
the cargo target directory a cargo row uses, so it builds no Lean and shares the cargo artifacts;
ND_BIN is removed from its environment, so it builds the candidate's client (GATES-6). It has
no import closure to select it by, so it is selected on every judge (fail-closed: a script row is never
skipped because its inputs are unknown).

A row `standing:EXE` is a verdict row of the lean_exe EXE that runs in standing only (GATES-17: a
bench whose run costs minutes). It is read exactly as an exe's row and needs a --harness-control
control; `-` is refused. runs.py runs it only with --standing (scripts/standing.sh); a pre-push run
prints `run standing:EXE: NOT RUN(standing-only; its inputs are unchanged)` unless this commit changed its inputs (a data
path, or a module of EXE's closure): then it runs in pre-push like any selected row (GATES-19, ROOT: standing-only is a
cost choice, never a correctness one). An EXE has
one row, plain or standing. Its WASTE rows are judged by standing's full waste check, where a pinned
row with no measurement is red, so a standing row that stops running is red there.

A cargo run is ok on exit 0 with libtest's summary saying at least one test passed (a run that
ran zero tests, or whose summary the reader cannot find, is RED: an absent verdict is not a pass).
A run is ok on exit 0 with its pass line last; INCOMPLETE on exit 3 (a row with no driver yet:
pending is a real outcome, law 7); RED otherwise, naming the first `FAIL`/`ROW … FAIL`/`PLANT …
FAIL` line or the exit code and last line. A run past DEADLINE (600 s of wall clock) is re-run once;
past it twice it is UNREAD(timeout …), never RED (GATES-16: a wall-clock deadline measures the box's
load as much as the commit, so it can withhold a verdict but never give one). `WASTE <op> <metric> <ratio>` lines
go to --waste-out. With --changed (pre-push), only the exes whose import closure holds a changed
module run (all of them when any changed path is not a .lean source, outside gates/doc-allow.tsv and SIZE.md:
the lakefile, the toolchain, a C source, runs.tsv, world/ texts, deploy/, the Rust tree, the runner; GATES-19): a sim is a verdict
a build cannot give, so the importers of a change are RUN, not only built (ROOT/HOSTING 10-17, after
HOSTING's grain text went stale under LANG's ID-1 with every build green).
A run killed by signal 9/15 (earlyoom, the cgroup) is KILLED(load), not RED (GATES-11's amendment).
With --keys/--reuse/--record (pre-push on a lander's candidate; GATES-19): a row whose input key
(gates/rebase.py, computed by the JUDGE's copy before the runs) is byte-identical to the key under
which the lander's previous judge recorded it ok is not run: its lines and WASTE lines are carried,
`  reuse EXE: reused (key …)`; a row whose key differs prints `  reuse EXE: re-run (key changed)` and
runs. Every row that reads ok (its control and every run) is written to --record; nothing else is,
so a red, INCOMPLETE, UNREAD, KILLED or ABSENT verdict is never carried.
With --traces DIR (GATES-20; pre-push on every judge, and standing): every run executes under
strace (gates/readset.py) and a row whose runs all read ok stores its READ-SET under its traced key.
Selection (with --base/--git-dir): a row holding a read-set valid for the parent is selected only by
its reach and by a change its read-set touched; a row with none falls to the static rules
(fail-closed). A lander's verdict is carried under the traced key of its own previous run's read-set
when that key is byte-identical on the candidate. Standing (--standing) re-traces every row and reads
RED when a fresh read-set exceeds the stored one under an equal key, and reports reads outside the
tree (F2; RED is GATES-20c).
Prints one `  run <exe> <args>: <verdict>` line per run and
`runs: ok|RED|KILLED(load)|UNREAD(timeout)|INCOMPLETE`; exits 0, 1, 76 (killed or timed out twice,
nothing red: not judged) or 3 (incomplete, nothing red, killed or timed out).
"""
import argparse
import json
import os
import re
import shutil
import subprocess
import sys
import tomllib

import readset
import tree

RUNS = os.path.join("gates", "runs.tsv")
# The wall-clock deadline of one run, seconds. ND_RUN_DEADLINE overrides it (the GATES-16 plant sets 1):
# a shorter one can only withhold verdicts (UNREAD), never give one.
DEADLINE = int(os.environ.get("ND_RUN_DEADLINE", "600"))


CONTROL = "harness-control"
NOBIN = ("nobin RED", "nobin ok")
STANDING = "standing:"


def table(root: str) -> dict[str, tuple[list[list[str]] | None, str, list[str] | str | None]]:
    """exe -> (runs, pass line, control); runs and control are None for a `-` row; a cargo row's
    control is one of NOBIN. Malformed rows raise ValueError."""
    out: dict[str, tuple[list[list[str]] | None, str, list[str] | str | None]] = {}
    p = os.path.join(root, RUNS)
    if not os.path.isfile(p):
        return out
    for n, line in enumerate(open(p, encoding="utf-8"), 1):
        if not line.strip() or line.startswith("#"):
            continue
        f = line.rstrip("\n").split("\t")
        if len(f) != 4 or not all(x.strip() for x in f):
            raise ValueError(f"{RUNS}:{n}: need exe<TAB>runs<TAB>pass<TAB>control: {line.rstrip()!r}")
        if f[0] in out or f[0].removeprefix(STANDING) in out or STANDING + f[0] in out:
            raise ValueError(f"{RUNS}:{n}: second row for {f[0].removeprefix(STANDING)}")
        if f[0].startswith("cargo:"):
            if len(f[0].split(":")) != 3 or f[2] != "exit 0" or f[3] not in NOBIN:
                raise ValueError(f"{RUNS}:{n}: a cargo row is cargo:CRATE:TEST<TAB>EXE,…<TAB>exit 0<TAB>nobin RED|nobin ok: {line.rstrip()!r}")
            out[f[0]] = ([[x.strip() for x in f[1].split(",") if x.strip()]], f[2], f[3])
            continue
        if f[1].strip() == "-":
            if f[0].startswith(STANDING):
                raise ValueError(f"{RUNS}:{n}: a standing row is a verdict run (runs, pass, a --{CONTROL} control), never `-`: {line.rstrip()!r}")
            if f[3].strip() != "-":
                raise ValueError(f"{RUNS}:{n}: a `-` row has control `-`: {line.rstrip()!r}")
            out[f[0]] = (None, f[2], None)
            continue
        if f"--{CONTROL}" not in f[3].split():
            raise ValueError(f"{RUNS}:{n}: verdict row {f[0]} needs a known-red control, an argument list with "
                             f"--{CONTROL} (GATES-15): {line.rstrip()!r}")
        runs = [[] if r.strip() == "(none)" else r.split() for r in f[1].split(" ; ")]
        out[f[0]] = (runs, f[2], f[3].split())
    return out


def check(t: tree.Tree) -> list[str]:
    """The table classifies exactly the lakefile's exes."""
    try:
        rows = table(t.root)
    except ValueError as e:
        return [str(e)]
    exes = set(t.exes)
    cargo = {k for k in rows if k.startswith("cargo:")}
    script = {k for k in rows if k.startswith("script:")}
    standing = {k for k in rows if k.startswith(STANDING)}
    named = (set(rows) - standing) | {k.removeprefix(STANDING) for k in standing}
    red = ([f"lean_exe {e} has no row in {RUNS} (a verdict run, or `-` with why it is not one)" for e in sorted(exes - named)]
           + [f"{RUNS} row {e} names no lean_exe" for e in sorted(set(rows) - exes - cargo - script - standing)]
           + [f"{RUNS} row {k} names no lean_exe" for k in sorted(standing) if k.removeprefix(STANDING) not in exes]
           + [f"{RUNS} row {k}: no executable {k[len('script:'):]}" for k in sorted(script)
              if not os.access(os.path.join(t.root, k[len("script:"):]), os.X_OK)]
           + [f"{RUNS} row {k}: a script row is a verdict run (runs, pass, a --{CONTROL} control), never `-`"
              for k in sorted(script) if rows[k][0] is None])
    for k in sorted(cargo):
        _, crate, test = k.split(":")
        if not os.path.isfile(os.path.join(t.root, crate, "tests", test + ".rs")):
            red.append(f"{RUNS} row {k}: no {crate}/tests/{test}.rs")
        red += [f"{RUNS} row {k}: drives {e}, which is no lean_exe" for e in rows[k][0][0] if e not in exes]
        red += [f"{RUNS} row {k}: {f} names lean_exe {e}, which its drives column omits (a drive no row "
                f"declares selects nothing: declare it, GATES-8)"
                for e, f in sorted(named_exes(t, crate, test).items()) if e not in rows[k][0][0]]
    if cargo:
        red += no_second_door(t.root)
    if cargo and not any(rows[k][2] == "nobin RED" for k in cargo):
        red.append(f"{RUNS}: no cargo row has the control `nobin RED`, so nothing proves the cargo reader reads a failure")
    return red


def data_paths(root: str, changed: list[str]) -> list[str]:
    """The changed paths a run may read at run time that no import closure tracks: every path that is
    not a .lean source, not under gates/doc-allow.tsv's prefixes (absent file: none) and not SIZE.md (a
    function of the other paths). GATES-19 / LANG-18: a re-emitted world/ package text (world/resident/Bell,
    installed by cargo:launcher:resident_bell and the rows) selected no row, so a known red could land
    GREEN and surface only in standing. No row declares what it reads, so such a path selects every row;
    traced read-sets are what will narrow it."""
    p = os.path.join(root, "gates", "doc-allow.tsv")
    allow = tuple(l.strip() for l in open(p, encoding="utf-8") if l.strip() and not l.startswith("#")) if os.path.isfile(p) else ()
    return [x for x in changed if not x.endswith(".lean") and x != "SIZE.md" and not (allow and x.startswith(allow))]


# A module that spawns a process (`IO.Process.spawn`/`output`/`run`): Ops.Plants runs {host}, and
# Protocol.Rows.Run runs `lake exe NAME` for names its row files hold. Read on the blanked code, so a
# comment or a string naming it does not count.
SPAWN = re.compile(r"\bIO\.Process\b|\bProcess\.(?:spawn|output|run)\b")


def reach(t: tree.Tree, e: str) -> set[str]:
    """The modules whose change can move a run of exe `e`: its import closure, and, when that closure
    holds a module that spawns a process, EVERY exe's closure (what it spawns is data, so it is taken
    as every exe). GATES-8: store-plants (runs {host}) and rows (runs `lake exe lang-journey`) were
    selected by their own closure only; ten of main's last 150 landings changed a module only a driven
    binary links and judged pre-push GREEN without the run (standing was the backstop)."""
    c = t.closure([t.exes[e]])
    if any(SPAWN.search(t.modules[m].code) for m in c if m in t.modules):
        return set().union(*(t.closure([r]) for r in t.exes.values()))
    return c


def named_exes(t: tree.Tree, crate: str, test: str) -> dict[str, str]:
    """lean_exe -> the first file that resolves it through the one door, `devtools::lean_bin("NAME")` or
    `lean_bin_in(DIR, "NAME")` (no_second_door keeps it the one), over the cargo test's sources:
    CRATE/tests/TEST.rs, CRATE/tests/common/ when it says `mod common`, and CRATE/src/. What a test may
    run, over-approximated by what its sources resolve (GATES-8: the resident rows ran hosting-residents
    through tests/common, undeclared, so a change only it links selected neither)."""
    first = os.path.join(crate, "tests", test + ".rs")
    files = [first]
    body = open(os.path.join(t.root, first), encoding="utf-8").read()
    dirs = [os.path.join(crate, "src")] + ([os.path.join(crate, "tests", "common")]
                                           if re.search(r"(?m)^\s*(?:pub\s+)?mod common\b", body) else [])
    for d in dirs:
        for top, _, names in sorted(os.walk(os.path.join(t.root, d))):
            files += sorted(os.path.relpath(os.path.join(top, n), t.root) for n in names if n.endswith(".rs"))
    out: dict[str, str] = {}
    for f in files:
        text = open(os.path.join(t.root, f), encoding="utf-8").read()
        for e in sorted(t.exes):
            if re.search(r"\blean_bin(?:_in\s*\([^()]*?,|\s*\()\s*\"" + re.escape(e) + r"\"\s*\)", text):
                out.setdefault(e, f)
    return out


def no_second_door(root: str) -> list[str]:
    """named_exes reads the lean_bin door only, so a Rust file outside devtools/src that reaches the
    Lean bin directory itself (the `"ND_LEAN_BIN"` variable or a `".lake/build/bin` path, as string
    literals) is a drive no scan sees: RED."""
    red = []
    for top, dirs, names in os.walk(root):
        dirs[:] = sorted(d for d in dirs if not d.startswith(".") and d != "target")
        for n in sorted(names):
            f = os.path.relpath(os.path.join(top, n), root)
            if n.endswith(".rs") and not f.startswith("devtools/src/"):
                text = open(os.path.join(root, f), encoding="utf-8", errors="replace").read()
                if '"ND_LEAN_BIN"' in text or '".lake/build/bin' in text:
                    red.append(f"{f}: reaches the Lean bin directory itself; resolve a Lean exe with "
                               f"devtools::lean_bin(NAME), the door gates/runs.py reads drives from (GATES-8)")
    return red


def selected(t: tree.Tree, changed: list[str] | None, rows: dict) -> set[str]:
    cargo = {k: rows[k][0][0] for k in rows if k.startswith("cargo:")}
    script = {k for k in rows if k.startswith("script:")}
    if changed is None or data_paths(t.root, changed):
        return set(t.exes) | set(cargo) | script
    mods = {p[:-5].replace("/", ".") for p in changed if p.endswith(".lean")}
    out = {e for e in t.exes if reach(t, e) & mods}
    return out | script | {k for k, drives in cargo.items()
                  if set(drives) & out or any(p.startswith(k.split(":")[1] + "/") for p in changed)}


def standing_selected(t: tree.Tree, changed: list[str] | None, rows: dict) -> dict[str, str]:
    """The standing rows this commit's change reaches, with why: a data path, or a module of the exe's closure."""
    if changed is None:
        return {k: "no change list" for k in rows if k.startswith(STANDING)}
    mods = {p[:-5].replace("/", ".") for p in changed if p.endswith(".lean")}
    d = data_paths(t.root, changed)
    out = {}
    for k in rows:
        e = k.removeprefix(STANDING)
        if not k.startswith(STANDING):
            continue
        hit = sorted(reach(t, e) & mods) if e in t.exes else []
        if d or hit:
            out[k] = f"changed path {d[0]}" if d else f"changed module {hit[0]}"
    return out


def verdict(out: str, rc: int, want: str) -> str:
    lines = out.rstrip("\n").split("\n")
    last = lines[-1] if lines else ""
    if rc == 0 and last == want:
        return "ok"
    if rc in (-9, -15, 137, 143):
        return f"KILLED(load: signal {abs(rc) % 128})"
    if rc == 3:
        return f"INCOMPLETE({last})"
    fail = next((l for l in lines if re.match(r"(?:ROW \S+ |PLANT \S+ )?FAIL\b", l)), None)
    return f"RED({fail or f'exit {rc}, last line: {last}'})"


def summary(out: str) -> tuple[int, int] | None:
    """libtest's `test result:` lines summed: (passed, failed); None when there is none."""
    rs = re.findall(r"(?m)^test result: \S+ (\d+) passed; (\d+) failed;", out)
    return (sum(int(p) for p, _ in rs), sum(int(f) for _, f in rs)) if rs else None


def run(t: tree.Tree, exe: str, args: list[str], passline: str, fresh: str, bindir: str,
        drives: list[str] = ()) -> tuple[str, str]:
    """One run: (its output, its verdict). `bindir` is where the Lean exes are taken from (a cargo
    row's control passes an empty directory and no `drives`); a cargo row's `drives` must be there."""
    shutil.rmtree(fresh, ignore_errors=True)
    os.makedirs(os.path.dirname(fresh), exist_ok=True)
    env = None
    if exe.startswith("cargo:"):
        _, crate, test = exe.split(":")
        # One workspace (ROOT 10-17): the member is named by its [package] name under the
        # root manifest, so every test shares the root lock and target dir.
        with open(os.path.join(t.root, crate, "Cargo.toml"), "rb") as fh:
            package = tomllib.load(fh)["package"]["name"]
        argv = ["cargo", "test", "--quiet", "--locked", "--manifest-path", os.path.join(t.root, "Cargo.toml"),
                "-p", package, "--test", test]
        env = dict(os.environ, ND_LEAN_BIN=bindir,
                   CARGO_TARGET_DIR=os.environ.get("CARGO_TARGET_DIR", os.path.join(t.root, ".lake", "cargo-target")))
        missing = [e for e in drives if not os.path.isfile(os.path.join(bindir, e))]
        if missing:
            return "", "ABSENT(no binary: " + ", ".join(missing) + ")"
    elif exe.startswith("script:"):
        # `{fresh}` exists for a script (its bulk goes there and is removed after); ND_BIN is dropped so the
        # script builds the candidate's own client, never a prebuilt one the judge's environment names
        os.makedirs(fresh)
        argv = [os.path.join(t.root, exe[len("script:"):])] + [x.replace("{fresh}", fresh) for x in args]
        env = dict(os.environ, ND_LEAN_BIN=bindir,
                   CARGO_TARGET_DIR=os.environ.get("CARGO_TARGET_DIR", os.path.join(t.root, ".lake", "cargo-target")))
        env.pop("ND_BIN", None)
        if not os.path.isfile(os.path.join(bindir, "host")):
            return "", "ABSENT(no binary: host)"
    else:
        host = os.path.join(bindir, "host")
        name = exe.removeprefix(STANDING)
        argv = [os.path.join(bindir, name)] + [x.replace("{host}", host).replace("{fresh}", fresh) for x in args]
        if not os.path.isfile(argv[0]):
            return "", "ABSENT(no binary: " + name + ")"
    tr = fresh.rstrip("/") + ".trace"
    if TRACING["strace"]:
        try:
            os.remove(tr)
        except FileNotFoundError:
            pass
        argv = readset.wrap(TRACING["strace"], argv, tr)
    try:
        r = subprocess.run(argv, cwd=t.root, capture_output=True, text=True, timeout=DEADLINE, env=env)
        out = r.stdout + r.stderr
        if exe.startswith("cargo:"):
            failed = re.findall(r"(?m)^---- (\S+) stdout ----", out)
            n = summary(r.stdout)
            if r.returncode == 0 and (n is None or n[0] == 0):
                v = "RED(harness: " + ("no `test result:` line to read" if n is None else "zero tests ran") + ")"
            else:
                v = verdict("exit 0" if r.returncode == 0 else out, r.returncode, passline)
                if failed and v.startswith("RED"):
                    v = f"RED(FAIL {', '.join(failed)})"
        else:
            # The verdict reads stdout, where the pass line is printed; the log keeps both.
            v = verdict(r.stdout or r.stderr, r.returncode, passline)
    except subprocess.TimeoutExpired as e:
        # What it printed before the deadline goes to the log (libtest names a test running past
        # 60 s); the verdict is UNREAD, never RED (GATES-16).
        out = "".join(x.decode(errors="replace") if isinstance(x, bytes) else (x or "") for x in (e.stdout, e.stderr))
        last = next((l.strip() for l in reversed(out.splitlines()) if l.strip()), "no output")
        v = f"UNREAD(timeout: past {DEADLINE} s of wall clock; last line: {last[:160]})"
    shutil.rmtree(fresh, ignore_errors=True)
    if TRACING["strace"]:
        TRACING["sets"].append(readset.reduce(tr, t.root))
        try:
            os.remove(tr)
        except FileNotFoundError:
            pass
    else:
        TRACING["sets"].append(None)
    return out, v


# GATES-20: the strace this judge traces with (None: untraced, every key static), and the read-sets of
# the runs of the row being judged, one per run (None for a run with no read-set).
TRACING: dict = {"strace": None, "sets": []}


def row_line(root: str, table_path: str | None, exe: str) -> str | None:
    p = table_path or os.path.join(root, RUNS)
    try:
        for line in open(p, encoding="utf-8"):
            if line.split("\t", 1)[0] == exe:
                return line.rstrip("\n")
    except OSError:
        return None
    return None


def git_out(gitdir: str, *args: str) -> str | None:
    r = subprocess.run(["git", "-C", gitdir, *args], capture_output=True, text=True)
    return r.stdout if r.returncode == 0 else None


def added_or_deleted(gitdir: str, a: str, b: str) -> set[str] | None:
    """Paths added, deleted or changed in kind between two tree-ishes (a listing sees these; an edit it
    does not), or None when git cannot say (the caller then counts every changed path)."""
    out = git_out(gitdir, "diff", "--name-status", "--no-renames", a, b)
    if out is None:
        return None
    return {l.split("\t")[-1] for l in out.splitlines() if l[:1] in ("A", "D", "T")}


def valid_readset(t: tree.Tree, exe: str, store: str, gitdir: str, base: str, line: str | None):
    """The newest stored read-set of `exe` valid for the parent `base`, or None. Valid: traced on a
    tree S such that nothing between S and base can move the run: no changed path it touched, no
    path changed in a directory it listed, no .lean of its reach, no runner file, and the same row
    line. Only the git-tracked part is checked here (the parent is not built at selection time); the
    .lake part (binaries, build products) is a function of the .lean sources, which the reach covers."""
    if line is None:
        return None
    reach_mods = reach_of(t, exe)
    for k, rec in readset.stored(store, exe)[:3]:
        rs, src = rec.get("readset"), rec.get("tree")
        if not rs or not src or rec.get("line") != line:
            continue
        diff = git_out(gitdir, "diff", "--name-only", src, base)
        if diff is None:
            continue
        d = diff.split()
        ad = added_or_deleted(gitdir, src, base)
        if (readset.touched_by(rs, d, set(d) if ad is None else ad) or any(x in readset.RUNNER for x in d)
                or {x[:-5].replace("/", ".") for x in d if x.endswith(".lean")} & reach_mods):
            continue
        return rs
    return None


def reach_of(t: tree.Tree, exe: str) -> set[str]:
    """The modules whose change can move a row: a Lean row's reach; a cargo row's drives' reach; a
    script row every exe's closure (it has no closure of its own)."""
    if exe.startswith("cargo:"):
        rows = table(t.root)
        drives = rows.get(exe, ([[]],))[0][0] if rows.get(exe) and rows[exe][0] else []
        return set().union(*(reach(t, e) for e in drives if e in t.exes)) if drives else set()
    if exe.startswith("script:"):
        return set().union(*(t.closure([r]) for r in t.exes.values()))
    e = exe.removeprefix(STANDING)
    return reach(t, e) if e in t.exes else set()


def traced_selected(t: tree.Tree, changed: list[str], rows: dict, store: str, gitdir: str, base: str,
                    table_path: str | None, base_table: str | None,
                    tree_oid: str | None) -> tuple[set[str], dict[str, str]]:
    """GATES-20's selection: per row, a valid read-set narrows; none falls to the static rule. Returns
    (selected rows, why) over every verdict row, standing rows included."""
    static = selected(t, changed, rows)
    static_standing = standing_selected(t, changed, rows)
    mods = {p[:-5].replace("/", ".") for p in changed if p.endswith(".lean")}
    ad = added_or_deleted(gitdir, base, tree_oid) if tree_oid else None
    out, why = set(), {}
    for exe in sorted(rows):
        if not rows[exe][0]:
            continue
        line = row_line(t.root, table_path, exe)
        rs = valid_readset(t, exe, store, gitdir, base, row_line(t.root, base_table, exe) if base_table else line)
        is_static = exe in static or exe in static_standing
        if rs is None:
            if is_static:
                out.add(exe); why[exe] = "no read-set valid for the parent: the static rule"
            continue
        hit = sorted(reach_of(t, exe) & mods)
        crate = exe.split(":")[1] + "/" if exe.startswith("cargo:") else None
        if base_table and row_line(t.root, base_table, exe) != line:
            why[exe] = "its row changed"
        elif any(x in readset.RUNNER for x in changed):
            why[exe] = "the runner changed"
        elif hit:
            why[exe] = f"changed module {hit[0]}"
        elif crate and any(x.startswith(crate) for x in changed):
            why[exe] = f"its crate {crate} changed"
        elif exe.startswith("script:"):
            why[exe] = "a script row (no closure: every judge)"
        else:
            w = readset.touched_by(rs, changed, set(changed) if ad is None else ad)
            if not w:
                continue
            why[exe] = w
        out.add(exe)
    return out, why


def run_once_more(t: tree.Tree, exe: str, args: list[str], passline: str, fresh: str, bindir: str,
                  drives: list[str] = ()) -> tuple[str, str]:
    """`run`, and once more when it timed out: a second timeout stays UNREAD (GATES-16)."""
    out, v = run(t, exe, args, passline, fresh, bindir, drives)
    if v.startswith("UNREAD(timeout"):
        sys.stderr.write(out + f"\n[runs.py] {exe} {' '.join(args)}: {v}; re-running once\n")
        out, v = run(t, exe, args, passline, fresh, bindir, drives)
        if v.startswith("UNREAD(timeout"):
            v = "UNREAD(timeout twice" + v[len("UNREAD(timeout"):]
    return out, v


def redlines(exe: str, out: str) -> list[str]:
    """The lines that name a failure: a cargo row's failed test names, an exe's FAIL/BLIND/RED lines."""
    if exe.startswith("cargo:"):
        return sorted(set(re.findall(r"(?m)^---- (\S+) stdout ----", out)))
    return [l.strip() for l in out.splitlines()
            if not l.startswith("WASTE ") and re.search(r"\b(FAIL|FAILED|BLIND|RED)\b", l)]


def control_reads_red(exe: str, v: str, out: str) -> str | None:
    """None when a known-red control read red; else why the harness is refused."""
    if v.startswith(("KILLED", "UNREAD", "ABSENT")):
        return None if v.startswith("ABSENT") else v
    if not v.startswith("RED"):
        return f"RED(harness: the known-red control passed: {v})"
    if exe.startswith("cargo:") and not v.startswith("RED(FAIL "):
        return f"RED(harness: the known-red control named no failed test: {v})"
    if not exe.startswith("cargo:") and CONTROL not in out:
        return f"RED(harness: the known-red control read red without naming {CONTROL}: {v})"
    return None


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("root")
    ap.add_argument("--changed")
    ap.add_argument("--waste-out")
    ap.add_argument("--standing", action="store_true", help="also run the `standing:` rows (scripts/standing.sh\n"
                    "only; pre-push never passes it: GATES-17)")
    ap.add_argument("--keys", help="unit<TAB>key per unit (gates/rebase.py keys), for --reuse/--record")
    ap.add_argument("--reuse", help="the lander's previous judge's record (GATES-19)")
    ap.add_argument("--record", help="write this judge's ok rows here (GATES-19)")
    ap.add_argument("--table", help="judge with this runs.tsv instead of TREE's (pre-push runs the\n"
                    "candidate's table over the parent tree, so both sides make the same runs)")
    ap.add_argument("--traces", help="GATES-20: trace every run and keep read-sets in this store")
    ap.add_argument("--git-dir", help="GATES-20: the repository, for a read-set's validity on --base")
    ap.add_argument("--base", help="GATES-20: the parent commit the selection is against")
    ap.add_argument("--base-table", help="GATES-20: the parent's runs.tsv (a changed row line selects its row)")
    ap.add_argument("--tree-oid", help="GATES-20: the tree object judged here (a stored read-set names it)")
    a = ap.parse_args()
    t = tree.read(a.root)
    rows = table(os.path.dirname(os.path.dirname(os.path.abspath(a.table)))) if a.table else table(t.root)
    # Judging a PARENT with the candidate's table (pre-push): a run the parent's own table does not
    # hold, row for row (same exe, same argument list, same pass line, same control; for a cargo
    # row, the parent has the test file too), was never a verdict of the parent. It is NOT RUN
    # there, so the candidate's red is new. An absent verdict is never a red one (the fail-open
    # class: cc4f6fe's new `cargo:launcher:broker` row, red in its own judge, landed as
    # "PRE-EXISTING"). A parent table this runner cannot read holds no comparable verdict at all.
    try:
        own = table(t.root) if a.table else rows
    except ValueError:
        own = {}
    changed = open(a.changed, encoding="utf-8").read().split() if a.changed else None
    want = selected(t, changed, rows)
    if changed is not None and data_paths(t.root, changed):
        d = data_paths(t.root, changed)
        print(f"  selection: every row ({len(d)} changed path(s) a run may read: {', '.join(d[:3])}{' …' if len(d) > 3 else ''})")
    traced_why = None
    if a.traces:
        TRACING["strace"] = readset.available()
        if not TRACING["strace"]:
            print("  trace: strace unavailable on this box: no read-set is recorded and every key is static")
    if TRACING["strace"] and changed is not None and a.git_dir and a.base and not a.standing:
        tw, traced_why = traced_selected(t, changed, rows, a.traces, a.git_dir, a.base, a.table, a.base_table, a.tree_oid)
        want = {e for e in tw if not e.startswith(STANDING)}
        for e in sorted(tw):
            print(f"  select {e}: {traced_why[e]}")
    standing = sorted(k for k in rows if k.startswith(STANDING))
    if a.standing:
        want |= set(standing)
    else:
        # Standing-only is a COST choice, never a correctness one (ROOT 10-19, LANG-18/PERF-9): a standing row
        # whose inputs this commit changed (a data path, or a module of its exe's closure) runs here like
        # any selected row, control included; only an unchanged one waits for standing.
        sel = standing_selected(t, changed, rows) if traced_why is None else \
            {k: traced_why[k] for k in standing if k in traced_why}
        for k in standing:
            why = sel.get(k)
            if why:
                want.add(k)
                print(f"  run {k}: selected in pre-push (its inputs changed: {why}; a standing-only row costs minutes)")
            else:
                print(f"  run {k}: NOT RUN(standing-only; its inputs are unchanged)")
    bindir = os.path.join(t.root, ".lake", "build", "bin")
    nobin = os.path.join(t.root, ".lake", "runs", "nobin")
    scratch = os.path.join(t.root, ".lake", "runs")
    shutil.rmtree(nobin, ignore_errors=True)
    os.makedirs(nobin)
    waste = []
    results = []

    def mine(exe: str) -> bool:
        m = own.get(exe)
        return m is not None and m[1:] == rows[exe][1:] and (not exe.startswith("cargo:") or os.path.isfile(
            os.path.join(t.root, exe.split(":")[1], "tests", exe.split(":")[2] + ".rs"))) and (
            not exe.startswith("script:") or os.path.isfile(os.path.join(t.root, exe[len("script:"):])))

    lines: list[tuple[str, str]] = []

    def report(exe: str, args: list[str], v: str, out: str, tag: str = "") -> None:
        sys.stderr.write(out)
        name = f"{exe} {' '.join(args)}{tag}"
        print(f"  run {name}: {v}")
        results.append(v)
        lines.append((name, v))
        # Every failure line of a red run is its own key (`    red RUN: LINE`): pre-push calls a red
        # PRE-EXISTING only line by line, so a new failure behind an old one on the same exe is new.
        if v.startswith("RED"):
            for l in redlines(exe, out)[:40]:
                print(f"    red {name}: {l}")

    todo = sorted(e for e in want & set(rows) if rows[e][0])
    keys = dict(l.rstrip("\n").split("\t", 1) for l in open(a.keys, encoding="utf-8") if "\t" in l) if a.keys else {}
    prev = {}
    if a.reuse and os.path.isfile(a.reuse):
        for l in open(a.reuse, encoding="utf-8"):
            f = l.rstrip("\n").split("\t", 3)
            if len(f) == 4 and f[0].startswith("run:"):
                prev[f[0][4:]] = (f[1], json.loads(f[3]))
    record = open(a.record, "a", encoding="utf-8") if a.record else None
    reused = set()
    for exe in todo:
        k = keys.get("run:" + exe)
        if exe in prev and prev[exe][0].startswith("t:"):
            # GATES-20: the previous judge's own read-set for this verdict, keyed on this tree
            rs0, line = prev[exe][1].get("readset"), row_line(t.root, a.table, exe)
            k = "t:" + readset.key(rs0, t.root, line) if rs0 and line else None
        if exe in prev and k is not None and prev[exe][0] == k and mine(exe):
            reused.add(exe)
            for name, v in prev[exe][1]["lines"]:
                print(f"  run {name}: {v}")
                results.append(v)
            waste += prev[exe][1]["waste"]
            print(f"  reuse {exe}: reused (key {k[:16]}, byte-identical to the previous judge's)")
            record and record.write(f"run:{exe}\t{k}\treused\t{json.dumps(prev[exe][1])}\n")
        elif exe in prev:
            print(f"  reuse {exe}: re-run (key changed)")
    todo = [e for e in todo if e not in reused]
    # The cargo reader's own control: whenever a cargo row runs, some `nobin RED` control runs first.
    cargo = [e for e in todo if e.startswith("cargo:")]
    if cargo and not any(rows[e][2] == "nobin RED" for e in cargo):
        first = next((e for e in sorted(rows) if e.startswith("cargo:") and rows[e][2] == "nobin RED"), None)
        if first is None:
            report("cargo", [], f"RED(harness: no `nobin RED` row proves the cargo reader)", "", " (control)")
        elif mine(first):
            TRACING["sets"] = []
            out, v = run_once_more(t, first, [], "exit 0", os.path.join(scratch, "reader"), nobin)
            report(first, [], control_reads_red(first, v, out) or "ok(known-red control read red)", out, " (reader control)")
    for exe in todo:
        runs, passline, control = rows[exe]
        lines.clear()
        TRACING["sets"] = []
        w0 = len(waste)
        if not mine(exe):
            for args in runs:
                print(f"  run {exe} {' '.join(args)}: NOT RUN(not in this tree's own table)")
            continue
        # The known-red control runs FIRST: a runner that cannot read a failure has no verdict to read.
        if exe.startswith("cargo:"):
            out, v = run_once_more(t, exe, [], passline, os.path.join(scratch, f"{exe}-control"), nobin)
            if control == "nobin RED":
                bad = control_reads_red(exe, v, out)
            else:   # `nobin ok`: declared to run no exe, so it must pass with none
                bad = None if v == "ok" or v.startswith(("KILLED", "UNREAD")) else \
                    f"RED(harness: declared `nobin ok` but with no Lean binaries it read {v})"
            cv, cargs = (bad or ("ok(known-red control read red)" if control == "nobin RED" else v)), []
        else:
            out, v = run_once_more(t, exe, control, passline, os.path.join(scratch, f"{exe}-control"), bindir)
            bad = control_reads_red(exe, v, out)
            cv, cargs = (bad or "ok(known-red control read red)"), control
        # A control's WASTE lines are not measurements (it plants); they are never collected.
        report(exe, cargs, cv if not v.startswith(("KILLED", "UNREAD", "ABSENT")) or bad else v, out, " (control)")
        if bad or v.startswith(("KILLED", "UNREAD", "ABSENT")):
            for args in runs:
                print(f"  run {exe} {' '.join(args)}: UNREAD(its known-red control did not read red)")
            continue
        for k, args in enumerate(runs):
            out, v = run_once_more(t, exe, args, passline, os.path.join(scratch, f"{exe}-{k}"), bindir,
                         args if exe.startswith("cargo:") else ())
            waste += [l for l in out.splitlines() if l.startswith("WASTE ")]
            report(exe, [] if exe.startswith("cargo:") else args, v, out)
        ok_all = bool(lines) and all(v.startswith("ok") for _, v in lines)
        rs = readset.union(TRACING["sets"]) if TRACING["strace"] else None
        if TRACING["strace"] and rs is None:
            # GATES-20d: a run whose trace could not be read: the static rules apply to this row, and
            # standing's re-trace check cannot run on it (standing counts these lines: INCOMPLETE).
            print(f"  untraced {exe}: no read-set ({readset.WHY[0] if readset.WHY else 'a run held none'}); "
                  f"the static rules apply")
        line = row_line(t.root, a.table, exe)
        tk = readset.key(rs, t.root, line) if rs and line else None
        if rs and a.traces:
            o = {c: n for c, n in rs["outside"].items() if c in ("tmp", "home")}
            if o:
                print(f"  outside {exe}: " + ", ".join(f"{c} {n}" for c, n in sorted(o.items()))
                      + " (F2: reported; RED is GATES-20c)")
            # The stored read-sets VALID on this tree: each one's own key, re-computed here, equals the key
            # it was stored under (a run on this tree consults exactly what it consulted there).
            same = [rec for k2, rec in readset.stored(a.traces, exe)
                    if rec.get("readset") and readset.key(rec["readset"], t.root, line) == k2]
            if a.standing:
                # The re-trace check: under an equal key a fresh read-set lies inside the stored one.
                for rec in same:
                    bad = readset.subset_violation(rs, rec.get("readset") or {"T": [], "L": [], "X": []}, t.root)
                    if bad:
                        report(exe, [], f"RED(trace: the run {bad}, which a stored read-set valid on this tree "
                                        f"omits: a forged or narrowed record, a nondeterministic run, or an input no "
                                        f"key covers)", "", " (re-trace)")
                        ok_all = False
                        break
            if ok_all and tk and not same:
                readset.store(a.traces, exe, tk, a.tree_oid or "", line, rs)
        if record and ok_all and tk:
            record.write(f"run:{exe}\tt:{tk}\trun\t{json.dumps({'lines': lines, 'waste': waste[w0:], 'readset': rs})}\n")
        elif record and keys.get("run:" + exe) and ok_all:
            record.write(f"run:{exe}\t{keys['run:' + exe]}\trun\t{json.dumps({'lines': lines, 'waste': waste[w0:]})}\n")
    record and record.close()
    shutil.rmtree(nobin, ignore_errors=True)
    if a.waste_out:
        with open(a.waste_out, "w", encoding="utf-8") as f:
            f.write("".join(l + "\n" for l in waste))
    red = any(not v.startswith(("ok", "INCOMPLETE", "KILLED", "UNREAD", "ABSENT")) for v in results)
    killed = any(v.startswith("KILLED") for v in results)
    timed = any(v.startswith("UNREAD(timeout") for v in results)
    inc = any(v.startswith(("INCOMPLETE", "ABSENT")) for v in results)
    word = ("RED" if red else "KILLED(load)" if killed else "UNREAD(timeout)" if timed
            else "INCOMPLETE" if inc else "ok")
    print(f"runs: {word} ({len(results)} runs of {len(want)} exes)")
    return 1 if red else 76 if killed or timed else 3 if inc else 0


if __name__ == "__main__":
    sys.exit(main())
