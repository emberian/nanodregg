"""gates/runs.py TREE [--standing] [--waste-out FILE] … — the verdict runs (sims, journeys, rows, plants): every
lean_exe whose answer is a verdict, run over the built TREE as gates/runs.tsv says. The convergence's runner
(scripts/standing.sh); a landing runs only the rows its change touched, through gates/touched.py, with run() below.

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

A row `cargo-untraced:CRATE:TEST` (GATES-20j, HOSTING-15's fence) is a cargo row that runs WITHOUT the GATES-20
tracer: a test that must cross a setuid boundary (sudo to the deployed uids) cannot run under it, since strace
--seccomp-bpf sets no_new_privs and sudo refuses (measured on hbox 10-21: `sudo -n -u nd true` exit 0 plain, exit 1
traced). It holds no read-set, so it is attributed by the static rules alone (its crate, its drives' closures, and
every non-.lean change) and is never carried.
A cargo run (either kind) that prints a line starting `skipped: ` (stdout or stderr) is never ok, whatever its exit
and libtest's summary: libtest counts a test that returned early as PASSED, so a test whose environment is absent
would read ok on a box without it (HOSTING-15: the fence absent). Outside standing it reads
INCOMPLETE(skipped: N, first: LINE); in standing (--standing) it reads RED(skipped: N, first: LINE), so an environment that went missing (a reboot cleared /run) is a
standing red until restored. The test's skip line carries its restore command. Neither is recorded or carried; on a
`nobin RED` control a skip is a control that did not read red.

A row `script:PATH` is a script of this tree that drives the built Lean exes and the client binaries
over real sockets (PERF-2: scripts/bar.sh, THE BAR at a bounded scale). `runs` are its argument lists
as for an exe (`{fresh}` is a fresh directory that exists when the run starts and is removed after),
`pass` its last stdout line, and `control` its known-red control (an argument list with
--harness-control, read exactly as an exe's). It runs with ND_LEAN_BIN = the built bin directory and
the cargo target directory a cargo row uses, so it builds no Lean and shares the cargo artifacts;
ND_BIN is removed from its environment, so it builds the tree's own client (GATES-6). It runs in every report.

A row `standing:EXE` is a verdict row of the lean_exe EXE that runs in standing only (GATES-17: a
bench whose run costs minutes). It is read exactly as an exe's row and needs a --harness-control
control; `-` is refused. runs.py runs it only with --standing (scripts/standing.sh). An EXE has
one row, plain or standing. Its WASTE rows are judged by standing's full waste check, where a pinned
row with no measurement is red, so a standing row that stops running is red there.

A cargo run is ok on exit 0 with libtest's summary saying at least one test passed (a run that
ran zero tests, or whose summary the reader cannot find, is RED: an absent verdict is not a pass).
A run is ok on exit 0 with its pass line last; INCOMPLETE on exit 3 (a row with no driver yet:
pending is a real outcome, law 7); RED otherwise, naming the first `FAIL`/`ROW … FAIL`/`PLANT …
FAIL` line or the exit code and last line. A run past DEADLINE (1200 s of wall clock) is re-run once;
past it twice it is UNREAD(timeout …), never RED (GATES-16: a wall-clock deadline measures the box's
load as much as the commit, so it can withhold a verdict but never give one). `WASTE <op> <metric> <ratio>` lines
go to --waste-out.
A run killed by signal 9/15 (earlyoom, the cgroup) is KILLED(load), not RED (GATES-11's amendment).
With --traces DIR (GATES-20): every run executes under strace (gates/readset.py) and a row whose runs all read ok
stores its READ-SET under its traced key; the convergence attributes a red row to the landings that touched what it
read. Standing (--standing) re-traces every row and reads
RED when a fresh read-set exceeds the stored one under an equal key, and reports reads outside the
tree (F2; RED is GATES-20c).
CONCURRENT ROWS (GATES-20g; Ember 10-21: the convergence's 46 min were ~43 min of rows run one after another).
With --slots-dir/--slots N (standing) the rows run concurrently, at most N at once in this tree: standing's own
lock runs one row, and each further row takes a free row token (<common>/nanodregg-gate-K.flock, non-blocking) for
as long as that one row runs, then gives it back. A row's own
runs stay in order, one at a time; its lines are printed in row order whatever order the rows finished in, each
row followed by `  time ROW: N s (own|borrowed slot K|alone)` read by this runner's own clock.
Every run has a TMPDIR of its own (GATES-25), made by this runner and removed after, which the read-set excludes as
it does {fresh}: a fixed name under the temp directory (rustix's build-script probe) is never a shared scratch.
Concurrency needs the tracer, which shows what each row WROTE (readset WR and O): two rows that share a scratch
are RED (`run concurrency A + B: RED(shared scratch …)`): one writes a path the other writes, removes or renames
the other's, or writes inside a directory the other made; or one writes a path the other reads (touched or
stat'ed), or an entry of a directory it lists (getdents; host-file-sim's .lake/host-file-sim/run-<random> is safe beside a
second such writer only while neither lists, cleans or reads the other's); whether or not they overlapped in
time this once, since the next schedule may overlap them. A row run now is checked against every row run
now and every carried row whose record holds what it wrote. A row whose writes cannot be seen never runs beside another: a
`cargo-untraced:` row, every row of an untraced judge, and a row whose last run entered a mount namespace of its
own (readset NS: its writes still lack a host mapping) run alone after the rest; a row that ran beside others
and turned out unseen (no read-set, or NS), and every row that ran beside it, are run again alone, and those runs
are their verdicts (`  alone ROW: …`); the collision check reads the union of what both of its runs wrote (GATES-25:
the alone run's cache is warm, so a cold build's writes are only in the first). A concurrent red is a red like any other.
THE CARRY (GATES-20l; standing: --reuse the previous standing's record, --record this one's, --daily SECONDS):
a row whose stored record's traced key is byte-identical on this tree (every path it read, stat'ed, listed or
exec'd, its row line, its waste rows, the runner and the tools) is not run; its lines and WASTE lines are carried
(`  carry ROW: carried (key …, run at SHA TIME)`). A record whose run is older than --daily is not carried
(`  daily ROW: re-run …`): every row runs at least daily, since the re-trace check, which only a run can make, is
what catches a narrowed record.
Prints one `  run <exe> <args>: <verdict>` line per run and
`runs: ok|RED|KILLED(load)|UNREAD(timeout)|INCOMPLETE`; exits 0, 1, 76 (killed or timed out twice,
nothing red: not judged) or 3 (incomplete, nothing red, killed or timed out).
"""
import argparse
import concurrent.futures as cf
import fcntl
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
import time
import tomllib

import readset
import tree

RUNS = os.path.join("gates", "runs.tsv")
# The wall-clock deadline of one run, seconds. ND_RUN_DEADLINE overrides it (the GATES-16 plant sets 1):
# a shorter one can only withhold verdicts (UNREAD), never give one.
DEADLINE = int(os.environ.get("ND_RUN_DEADLINE", "1200"))


CONTROL = "harness-control"
CARGO = ("cargo:", "cargo-untraced:")
STANDING_RUN = {"on": False}   # set by --standing: a skipped cargo run is RED there, INCOMPLETE elsewhere
SKIPPED = re.compile(r"(?m)^skipped: .*$")
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
        if f[0].startswith(CARGO):
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
    cargo = {k for k in rows if k.startswith(CARGO)}
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
# Protocol.Rows.Run runs the exe NAME beside itself for names its row files hold. Read on the blanked code, so a
# comment or a string naming it does not count.
SPAWN = re.compile(r"\bIO\.Process\b|\bProcess\.(?:spawn|output|run)\b")


def reach(t: tree.Tree, e: str) -> set[str]:
    """The modules whose change can move a run of exe `e`: its import closure, and, when that closure
    holds a module that spawns a process, EVERY exe's closure (what it spawns is data, so it is taken
    as every exe). GATES-8: store-plants (runs {host}) and rows (runs lang-journey) were
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
    cargo = {k: rows[k][0][0] for k in rows if k.startswith(CARGO)}
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


def run_group(argv: list[str], cwd: str, env: dict) -> subprocess.CompletedProcess:
    """Run `argv` as the leader of a process group of its own; past DEADLINE the WHOLE group is
    killed (SIGKILL), not only the direct child (CLIENT-38, A19: the child is cargo or strace, and a
    kill of it alone left the test binary and every supervisor under it alive: the 336 of 10-23).
    A process that left the group (a confined child calls setsid, CLIENT-48) is our binaries' parent-death link's
    to end. Raises subprocess.TimeoutExpired as subprocess.run does, with what was printed."""
    with subprocess.Popen(argv, cwd=cwd, env=env, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                          text=True, start_new_session=True) as p:
        try:
            out, err = p.communicate(timeout=DEADLINE)
        except subprocess.TimeoutExpired:
            try:
                os.killpg(p.pid, 9)
            except ProcessLookupError:
                pass
            out, err = p.communicate()
            raise subprocess.TimeoutExpired(argv, DEADLINE, output=out, stderr=err)
        return subprocess.CompletedProcess(argv, p.returncode, out, err)


def run(t: tree.Tree, exe: str, args: list[str], passline: str, fresh: str, bindir: str,
        drives: list[str] = (), sets: list | None = None) -> tuple[str, str]:
    """One run: (its output, its verdict). `bindir` is where the Lean exes are taken from (a cargo
    row's control passes an empty directory and no `drives`); a cargo row's `drives` must be there."""
    shutil.rmtree(fresh, ignore_errors=True)
    os.makedirs(os.path.dirname(fresh), exist_ok=True)
    env = None
    if exe.startswith(CARGO):
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
    # GATES-25: every run has a TMPDIR of its own, made here (mode 0700) and removed after, so a fixed name under
    # the temp directory (rustix's build probe writes TMPDIR/rustix_test_can_compile; cv 01a17007) is never
    # shared by two rows, nor by two judges of one box. It sits under the judge's own temp directory, not under
    # {fresh}: a socket a test binds in it must fit sun_path (108 bytes), which a tree path does not leave room for.
    tmp = os.path.realpath(tempfile.mkdtemp(prefix="nd-runtmp-"))
    env = dict(os.environ if env is None else env, TMPDIR=tmp)
    tr = fresh.rstrip("/") + ".trace"
    traced = TRACING["strace"] and not exe.startswith("cargo-untraced:")
    if traced:
        try:
            os.remove(tr)
        except FileNotFoundError:
            pass
        argv = readset.wrap(TRACING["strace"], argv, tr)
    try:
        r = run_group(argv, t.root, env)
        out = r.stdout + r.stderr
        if exe.startswith(CARGO):
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
    # GATES-22 follow-up (GATES-10 verified at source): the tracer itself can fail mid-run, `strace: ptrace(PTRACE_LISTEN,
    # …): Input/output error`, and the run exits non-zero. That is no verdict about the run: UNREAD(tracer), re-run once
    # (run_once_more), twice is NOT JUDGED, never RED. Only strace's own lines (`strace: ` or `…/strace: `, TRACER)
    # count, and only on a run that did not read ok.
    if traced and not v.startswith("ok"):
        tl = TRACER.search(out)
        if tl:
            v = f"UNREAD(tracer: {tl.group(0)[:200]})"
    if exe.startswith(CARGO) and not v.startswith(("RED", "KILLED", "UNREAD")):
        sk = SKIPPED.findall(out)
        if sk:
            v = f"{'RED' if STANDING_RUN['on'] else 'INCOMPLETE'}(skipped: {len(sk)}, first: {sk[0][:200]})"
    shutil.rmtree(fresh, ignore_errors=True)
    shutil.rmtree(tmp, ignore_errors=True)
    sets = [] if sets is None else sets
    if traced:
        sets.append(readset.reduce(tr, t.root, tmp))
        try:
            os.remove(tr)
        except FileNotFoundError:
            pass
    else:
        sets.append(None)
    return out, v


# GATES-20: the strace this judge traces with (None: untraced, every key static). A row's runs' read-sets are
# the row's own list (Row.sets, one per run, None for a run with no read-set): rows run concurrently (GATES-20g).
TRACING: dict = {"strace": None}
# strace names itself by its argv[0], the absolute path readset.available() found (`/usr/bin/strace: ptrace(…)`), and
# its line can follow the tracee's unterminated output (libtest's progress dots: `………/usr/bin/strace: ptrace(…)`, hbox
# gate-2/4c04f20aa738.log:860, gate-3/2b29a0426731.log:412, gate-3/846590c46570.log:301). The match is `strace: ` at a
# line start or right after a `/`, to the end of the line.
TRACER = re.compile(r"(?m)(?:^|/)strace: .*$")


def row_line(root: str, table_path: str | None, exe: str) -> str | None:
    p = table_path or os.path.join(root, RUNS)
    try:
        for line in open(p, encoding="utf-8"):
            if line.split("\t", 1)[0] == exe:
                return line.rstrip("\n")
    except OSError:
        return None
    return None


def reach_of(t: tree.Tree, exe: str) -> set[str]:
    """The modules whose change can move a row: a Lean row's reach; a cargo row's drives' reach; a
    script row every exe's closure (it has no closure of its own)."""
    if exe.startswith(CARGO):
        rows = table(t.root)
        drives = rows.get(exe, ([[]],))[0][0] if rows.get(exe) and rows[exe][0] else []
        return set().union(*(reach(t, e) for e in drives if e in t.exes)) if drives else set()
    if exe.startswith("script:"):
        return set().union(*(t.closure([r]) for r in t.exes.values()))
    e = exe.removeprefix(STANDING)
    return reach(t, e) if e in t.exes else set()


def run_once_more(t: tree.Tree, exe: str, args: list[str], passline: str, fresh: str, bindir: str,
                  drives: list[str] = (), sets: list | None = None, row: "Row | None" = None) -> tuple[str, str]:
    """`run`, and once more when it timed out or its tracer failed: a second one stays UNREAD (GATES-16).
    `row` collects what would be printed (rows run concurrently and print in row order); None prints now."""
    out, v = run(t, exe, args, passline, fresh, bindir, drives, sets)
    for kind in ("UNREAD(timeout", "UNREAD(tracer"):
        if v.startswith(kind):
            msg = out + f"\n[runs.py] {exe} {' '.join(args)}: {v}; re-running once\n"
            row.err.append(msg) if row else sys.stderr.write(msg)
            if sets:
                sets.pop()   # the failed run's read-set is not the row's: the re-run's is
            out, v = run(t, exe, args, passline, fresh, bindir, drives, sets)
            if v.startswith(kind):
                v = kind + " twice" + v[len(kind):]
            elif kind == "UNREAD(tracer":
                # standing counts these (`flakes=N`): a tracer that keeps failing is the box's to fix
                line = f"  flake {exe} {' '.join(args)}: the tracer failed once; the re-run read {v[:80]}"
                row.say(line) if row else print(line, flush=True)
            break
    return out, v


def redlines(exe: str, out: str) -> list[str]:
    """The lines that name a failure: a cargo row's failed test names, an exe's FAIL/BLIND/RED lines."""
    if exe.startswith(CARGO):
        return sorted(set(re.findall(r"(?m)^---- (\S+) stdout ----", out)))
    return [l.strip() for l in out.splitlines()
            if not l.startswith("WASTE ") and re.search(r"\b(FAIL|FAILED|BLIND|RED)\b", l)]


def control_reads_red(exe: str, v: str, out: str) -> str | None:
    """None when a known-red control read red; else why the harness is refused."""
    if v.startswith(("KILLED", "UNREAD", "ABSENT")):
        return None if v.startswith("ABSENT") else v
    if not v.startswith("RED"):
        return f"RED(harness: the known-red control passed: {v})"
    if exe.startswith(CARGO) and not v.startswith("RED(FAIL "):
        return f"RED(harness: the known-red control named no failed test: {v})"
    if not exe.startswith(CARGO) and CONTROL not in out:
        return f"RED(harness: the known-red control read red without naming {CONTROL}: {v})"
    return None


class Row:
    """One row's judgement, kept apart so rows can run concurrently (GATES-20g): its printed lines (printed in
    row order once every row is done), its runs' stderr, verdicts, WASTE lines, record lines and read-set, its
    wall time by this runner's clock and where it ran."""

    def __init__(self, exe: str) -> None:
        self.exe, self.out, self.err, self.results, self.lines = exe, [], [], [], []
        self.waste, self.record, self.sets, self.rs = [], [], [], None
        self.ran, self.wall, self.start, self.end, self.where = False, 0.0, 0.0, 0.0, "own"
        # GATES-25: the read-set of this row's run beside others, when it was run again alone: what it wrote
        # there is what it writes (a cold cache's build writes run once), so the collision check reads both
        self.beside = None

    def say(self, line: str) -> None:
        self.out.append(line)

    def report(self, exe: str, args: list[str], v: str, out: str, tag: str = "") -> None:
        self.err.append(out)
        name = f"{exe} {' '.join(args)}{tag}"
        self.say(f"  run {name}: {v}")
        self.results.append(v)
        self.lines.append((name, v))
        # Every failure line of a red run is its own key (`    red RUN: LINE`): pre-push calls a red
        # PRE-EXISTING only line by line, so a new failure behind an old one on the same exe is new.
        if v.startswith("RED"):
            for l in redlines(exe, out)[:40]:
                self.say(f"    red {name}: {l}")


class Slots:
    """GATES-20g: row tokens (<common>/nanodregg-gate-K.flock, K = 1..N). The caller already holds its own place; a
    further row takes a token whose flock is free (non-blocking) and gives it back when the row ends. The descriptor
    is os.open's, not inheritable (PEP 446): no run's child keeps a token after its row."""

    def __init__(self, common: str, n: int) -> None:
        self.common, self.n = common, n

    def borrow(self) -> tuple[int, int] | None:
        for k in range(1, self.n + 1):
            try:
                fd = os.open(os.path.join(self.common, f"nanodregg-gate-{k}.flock"), os.O_WRONLY | os.O_CREAT, 0o664)
            except OSError:
                continue
            try:
                fcntl.flock(fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
                return k, fd
            except OSError:
                os.close(fd)
        return None

    @staticmethod
    def give_back(tok: tuple[int, int]) -> None:
        os.close(tok[1])


def collisions(rs: dict[str, dict]) -> list[tuple[str, str, str]]:
    """GATES-20g: (row A, row B, what) for every pair of rows that cannot run beside each other (readset WR, O):
    A writes a path B writes, or one holding B's write or B's own directory (a removal or rename of it), or a path
    inside a directory B made; or A writes a path B reads (touched, compiled from or stat'ed: the path or one below
    it), or adds or removes an entry of a directory B lists. Two rows each making their own directory under one
    shared parent do not collide (neither can see the other), unless one lists, removes or writes into the other's.
    A removal (RM) reaches every write of the other row below it, its own directories' contents included.
    A row with no write record (traced before GATES-20g) is not compared."""
    under = readset.under
    out = []
    names = sorted(e for e in rs if rs[e] is not None and "WR" in rs[e])
    for i, a in enumerate(names):
        for b in names[i + 1:]:
            hit = None
            for x, y in ((a, b), (b, a)):
                wx, ox, wy, oy = rs[x]["WR"], rs[x].get("O", []), rs[y]["WR"], rs[y].get("O", [])
                reads = set(rs[y].get("T", [])) | set(rs[y].get("C", [])) | set(rs[y].get("K", []))
                lists = set(rs[y].get("LD", []))
                q = next(((d, v) for d in rs[x].get("RM", []) for v in list(wy) + list(oy) if under(v, d)), None)
                if q:
                    hit = f"{x} removes {q[0]}, which holds {y}'s {q[1]}"
                    break
                for w in wx:
                    q = next((v for v in list(wy) + list(oy) if under(v, w)), None) or                         next((o for o in oy if under(w, o) and w != o), None)
                    if q:
                        hit = f"{x} writes {w} and {y} writes {q}"
                        break
                    q = next((r for r in sorted(reads) if under(r, w)), None)
                    if q:
                        hit = f"{x} writes {w}, which {y} reads ({q})"
                        break
                for o in ([] if hit else ox):
                    q = next((r for r in sorted(reads) if under(r, o) and r != o), None)
                    if q:
                        hit = f"{x} makes {o}, inside which {y} reads ({q})"
                        break
                    q = next((d for d in sorted(lists) if under(d, o)), None)
                    if q:
                        hit = f"{x} makes {o} and writes inside it, and {y} lists {q}"
                        break
                for w in ([] if hit else list(wx) + list(ox)):
                    d = os.path.dirname(w) or "."
                    if d in lists:
                        hit = f"{x} writes {w}, an entry of {d}, which {y} lists"
                        break
                if hit:
                    break
            if hit:
                out.append((a, b, hit))
    return out


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("root")
    ap.add_argument("--waste-out")
    ap.add_argument("--standing", action="store_true", help="also run the `standing:` rows (scripts/standing.sh)")
    ap.add_argument("--reuse", help="the previous report's record (GATES-20l)")
    ap.add_argument("--record", help="write this report's ok rows here (GATES-20l)")
    ap.add_argument("--traces", help="GATES-20: trace every run and keep read-sets in this store")
    ap.add_argument("--tree-oid", help="GATES-20: the tree object judged here (a stored read-set names it)")
    ap.add_argument("--slots-dir", help="GATES-20g: the git common dir, where the row tokens' flocks are")
    ap.add_argument("--slots", type=int, default=1, help="GATES-20g: at most N rows at once")
    ap.add_argument("--daily", type=int, help="GATES-20l (standing): a record older than this many seconds is not carried")
    a = ap.parse_args()
    t = tree.read(a.root)
    STANDING_RUN["on"] = a.standing
    rows = table(t.root)
    own = rows
    want = set(t.exes) | {k for k in rows if k.startswith(CARGO + ("script:",))}
    if a.traces:
        TRACING["strace"] = readset.available()
        if not TRACING["strace"]:
            print("  trace: strace unavailable on this box: no read-set is recorded and every key is static")
    if a.standing:
        want |= {k for k in rows if k.startswith(STANDING)}
    bindir = os.path.join(t.root, ".lake", "build", "bin")
    nobin = os.path.join(t.root, ".lake", "runs", "nobin")
    scratch = os.path.join(t.root, ".lake", "runs")
    shutil.rmtree(nobin, ignore_errors=True)
    os.makedirs(nobin)
    waste = []
    results = []

    def mine(exe: str) -> bool:
        m = own.get(exe)
        return m is not None and m[1:] == rows[exe][1:] and (not exe.startswith(CARGO) or os.path.isfile(
            os.path.join(t.root, exe.split(":")[1], "tests", exe.split(":")[2] + ".rs"))) and (
            not exe.startswith("script:") or os.path.isfile(os.path.join(t.root, exe[len("script:"):])))

    head = Row("")   # the carried rows' lines and the cargo reader's control, printed before the rows run now
    now = time.time()
    todo = sorted(e for e in want & set(rows) if rows[e][0])
    prev = {}
    if a.reuse and os.path.isfile(a.reuse):
        for l in open(a.reuse, encoding="utf-8"):
            f = l.rstrip("\n").split("\t", 3)
            if len(f) == 4 and f[0].startswith("run:"):
                prev[f[0][4:]] = (f[1], json.loads(f[3]))
    record = open(a.record, "a", encoding="utf-8") if a.record else None
    reused = set()
    word = "carry" if a.standing else "reuse"
    for exe in todo:
        k = None
        if exe in prev and prev[exe][0].startswith("t:"):
            # GATES-20: the previous judge's own read-set for this verdict, keyed on this tree
            rs0, line = prev[exe][1].get("readset"), row_line(t.root, None, exe)
            k = "t:" + readset.key(rs0, t.root, line) if rs0 and line else None
        at = prev[exe][1].get("at") if exe in prev else None
        if exe in prev and prev[exe][0].startswith("t:") and not readset.keyable(prev[exe][1].get("readset") or {}):
            head.say(f"  {word} {exe}: re-run (traced in a mount namespace, "
                     f"or the record predates GATES-20g)")
            continue
        if exe in prev and k is not None and prev[exe][0] == k and mine(exe) and a.daily is not None and (
                not isinstance(at, (int, float)) or now - at > a.daily):
            # GATES-20l: every row runs at least daily (the re-trace check, which only a run makes, is what
            # catches a narrowed record); a record that does not say when it ran is as old as can be
            head.say(f"  daily {exe}: re-run (its key is byte-identical, but its last run was "
                     + (f"{(now - at) / 3600:.1f} h ago" if isinstance(at, (int, float)) else "at an unrecorded time")
                     + f"; every row runs at least every {a.daily / 3600:.0f} h)")
        elif exe in prev and k is not None and prev[exe][0] == k and mine(exe):
            reused.add(exe)
            for name, v in prev[exe][1]["lines"]:
                head.say(f"  run {name}: {v}")
                head.results.append(v)
            waste += prev[exe][1]["waste"]
            if a.standing:
                head.say(f"  carry {exe}: carried (key {k[:16]}, byte-identical to its run at "
                         f"{str(prev[exe][1].get('tree', '?'))[:12]} "
                         f"{time.strftime('%Y-%m-%dT%H:%MZ', time.gmtime(at)) if isinstance(at, (int, float)) else '?'})")
            else:
                head.say(f"  reuse {exe}: reused (key {k[:16]}, byte-identical to the previous judge's)")
            head.record.append(f"run:{exe}\t{k}\treused\t{json.dumps(prev[exe][1])}\n")
        elif exe in prev:
            head.say(f"  {word} {exe}: re-run (key changed)")
    todo = [e for e in todo if e not in reused]
    # The cargo reader's own control: whenever a cargo row runs, some `nobin RED` control runs first.
    cargo = [e for e in todo if e.startswith(CARGO)]
    if cargo and not any(rows[e][2] == "nobin RED" for e in cargo):
        first = next((e for e in sorted(rows) if e.startswith(CARGO) and rows[e][2] == "nobin RED"), None)
        if first is None:
            head.report("cargo", [], f"RED(harness: no `nobin RED` row proves the cargo reader)", "", " (control)")
        elif mine(first):
            out, v = run_once_more(t, first, [], "exit 0", os.path.join(scratch, "reader"), nobin, row=head)
            head.report(first, [], control_reads_red(first, v, out) or "ok(known-red control read red)", out, " (reader control)")

    def judge_row(exe: str) -> Row:
        o = Row(exe)
        runs, passline, control = rows[exe]
        if not mine(exe):
            for args in runs:
                o.say(f"  run {exe} {' '.join(args)}: NOT RUN(not in this tree's own table)")
            return o
        o.ran, o.start = True, time.monotonic()
        try:
            judge_runs(o, exe, runs, passline, control)
        finally:
            o.end = time.monotonic()
            o.wall = o.end - o.start
        return o

    def judge_runs(o: Row, exe: str, runs, passline: str, control) -> None:
        # The known-red control runs FIRST: a runner that cannot read a failure has no verdict to read.
        if exe.startswith(CARGO):
            out, v = run_once_more(t, exe, [], passline, os.path.join(scratch, f"{exe}-control"), nobin, sets=o.sets, row=o)
            if control == "nobin RED":
                bad = control_reads_red(exe, v, out)
            else:   # `nobin ok`: declared to run no exe, so it must pass with none
                bad = None if v == "ok" or v.startswith(("KILLED", "UNREAD")) else \
                    f"RED(harness: declared `nobin ok` but with no Lean binaries it read {v})"
            cv, cargs = (bad or ("ok(known-red control read red)" if control == "nobin RED" else v)), []
        else:
            out, v = run_once_more(t, exe, control, passline, os.path.join(scratch, f"{exe}-control"), bindir, sets=o.sets, row=o)
            bad = control_reads_red(exe, v, out)
            cv, cargs = (bad or "ok(known-red control read red)"), control
        # A control's WASTE lines are not measurements (it plants); they are never collected.
        o.report(exe, cargs, cv if not v.startswith(("KILLED", "UNREAD", "ABSENT")) or bad else v, out, " (control)")
        if bad or v.startswith(("KILLED", "UNREAD", "ABSENT")):
            for args in runs:
                o.say(f"  run {exe} {' '.join(args)}: UNREAD(its known-red control did not read red)")
            o.rs = readset.union(o.sets) if TRACING["strace"] and not exe.startswith("cargo-untraced:") else None
            return
        for k, args in enumerate(runs):
            out, v = run_once_more(t, exe, args, passline, os.path.join(scratch, f"{exe}-{k}"), bindir,
                                   args if exe.startswith(CARGO) else (), sets=o.sets, row=o)
            o.waste += [l for l in out.splitlines() if l.startswith("WASTE ")]
            o.report(exe, [] if exe.startswith(CARGO) else args, v, out)
        ok_all = bool(o.lines) and all(v.startswith("ok") for _, v in o.lines)
        if exe.startswith("cargo-untraced:"):
            rs = None   # untraced by its row's kind: static selection and the static key, never a read-set
        else:
            rs = readset.union(o.sets) if TRACING["strace"] else None
        o.rs = rs
        if rs is not None:
            # GATES-20e: the waste rows this row measured, a judge input no trace can show
            rs["W"] = sorted({"\t".join(l.split()[1:3]) for l in o.waste if len(l.split()) >= 4})
        if TRACING["strace"] and rs is None and not exe.startswith("cargo-untraced:"):
            # GATES-20d: a run whose trace could not be read: the static rules apply to this row, and
            # standing's re-trace check cannot run on it (standing counts these lines: INCOMPLETE).
            o.say(f"  untraced {exe}: no read-set ({readset.why_none() or 'a run held none'}); "
                  f"the static rules apply")
        line = row_line(t.root, None, exe)
        tk = readset.key(rs, t.root, line) if rs and line else None
        if rs and a.traces:
            oc = {c: n for c, n in rs["outside"].items() if c in ("tmp", "home")}
            if oc:
                o.say(f"  outside {exe}: " + ", ".join(f"{c} {n}" for c, n in sorted(oc.items()))
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
                        o.report(exe, [], f"RED(trace: the run {bad}, which a stored read-set valid on this tree "
                                          f"omits: a forged or narrowed record, a nondeterministic run, or an input no "
                                          f"key covers)", "", " (re-trace)")
                        ok_all = False
                        break
            if ok_all and tk and not same:
                readset.store(a.traces, exe, tk, a.tree_oid or "", line, rs)
        ran = {"at": int(time.time()), "tree": a.tree_oid or ""}
        if ok_all and tk:
            o.record.append(f"run:{exe}\tt:{tk}\trun\t{json.dumps({'lines': o.lines, 'waste': o.waste, 'readset': rs, **ran})}\n")

    # GATES-20g: at most N rows at once, this judge's own place plus free judge slots borrowed per row. A row with
    # no read-set (a cargo-untraced row; every row of an untraced judge) runs alone, after the rest.
    cap = a.slots if a.slots_dir and a.slots > 1 and TRACING["strace"] else 1
    # the schedule's memory (never a verdict): each row's last wall, and whether its last run entered a mount
    # namespace of its own (readset NS: such a row runs alone, so it is scheduled alone from the start)
    walls_p = os.path.join(a.traces, "_walls.json") if a.traces else None
    try:
        walls = json.load(open(walls_p, encoding="utf-8")) if walls_p and os.path.isfile(walls_p) else {}
        walls = {e: (w if isinstance(w, dict) else {"wall": w}) for e, w in walls.items()}
    except (OSError, ValueError, AttributeError):
        walls = {}
    alone = [e for e in todo if cap == 1 or e.startswith("cargo-untraced:") or walls.get(e, {}).get("ns")]
    done: dict[str, Row] = {}
    borrowed, t_all = 0, time.monotonic()
    together = [e for e in todo if e not in alone]
    if together:
        slots = Slots(a.slots_dir, a.slots)
        # the longest row first by its last wall (a schedule, never a verdict); a row never timed goes first
        pending = sorted(together, key=lambda e: (-float(walls.get(e, {}).get("wall", 1e9)), e))
        running: dict = {}
        own_free = True
        with cf.ThreadPoolExecutor(max_workers=cap) as ex:
            while pending or running:
                while pending and len(running) < cap:
                    tok = None
                    if not own_free:
                        tok = slots.borrow()
                        if tok is None:
                            break
                        borrowed += 1
                    e = pending.pop(0)
                    own_free = own_free and tok is not None
                    running[ex.submit(judge_row, e)] = (e, tok)
                fin, _ = cf.wait(list(running), timeout=5, return_when=cf.FIRST_COMPLETED)
                for fu in fin:
                    e, tok = running.pop(fu)
                    if tok is None:
                        own_free = True
                    else:
                        Slots.give_back(tok)
                    done[e] = fu.result()   # a row that crashed crashes the runner: no verdict, never ok
                    done[e].where = "own" if tok is None else f"borrowed slot {tok[0]}"
        # A row that ran beside others with no read-set wrote what no one can see: it, and every row that ran
        # beside it, are run again alone, and those runs are their verdicts.
        def met(x: str, y: str) -> bool:
            return x != y and done[x].ran and done[y].ran and done[x].start < done[y].end and done[y].start < done[x].end
        def unseen(e: str) -> str | None:
            rs = done[e].rs
            return "no read-set" if rs is None else "a mount namespace of its own" if rs.get("NS") else None
        blind = [e for e in together if done[e].ran and unseen(e) and any(met(e, x) for x in together)]
        again = {e: (f"it ran beside others with {unseen(e)}: what it wrote is unknown" if e in blind else
                     f"it ran beside {', '.join(sorted(b for b in blind if met(b, e)))}, whose writes are unknown")
                 for e in sorted(set(blind) | {x for b in blind for x in together if met(b, x)})}
        for e, why in again.items():
            beside = done[e].rs
            o = judge_row(e)
            o.beside = beside
            o.out.insert(0, f"  alone {e}: re-run with no other row running ({why}); this run is its verdict")
            o.where = "alone"
            done[e] = o
    for e in alone:
        done[e] = judge_row(e)
        done[e].where = "alone" if cap > 1 else "own"
    print(f"  concurrency: at most {cap} row(s) at once; {len(todo)} rows run"
          + (f" ({len(alone)} alone)" if cap > 1 else "") + ", "
          f"{borrowed} on a borrowed judge slot, {len(reused)} {'carried' if a.standing else 'reused'}"
          + ("" if cap > 1 else " (one row at a time: " + ("no --slots" if not (a.slots_dir and a.slots > 1) else "untraced") + ")"))
    for l in head.out:
        print(l)
    sys.stderr.write("".join(head.err))
    results += head.results
    record and record.write("".join(head.record))
    for exe in todo:
        o = done[exe]
        sys.stderr.write("".join(o.err))
        for l in o.out:
            print(l)
        if o.ran:
            print(f"  time {exe}: {o.wall:.0f} s ({o.where})")
        results += o.results
        waste += o.waste
        record and record.write("".join(o.record))
    # GATES-20g: two rows that share a scratch, or one writing what the other reads, are RED: every pair of rows
    # run now, and each row run now against every carried row whose record says what it wrote.
    # GATES-25: a row run again alone is compared on the union of both runs' writes. Its alone run's cache is the
    # one its first run warmed, so a write only a cold build makes (rustix's build probe, cv 01a17007) is in the
    # first run's read-set alone; reading the verdict run's only, the check saw it only when a row was cold twice.
    wr = {e: (done[e].rs if done[e].beside is None else readset.union([done[e].rs, done[e].beside]) or done[e].rs)
          for e in todo if done[e].rs is not None}
    pairs = collisions({**wr, **{e: prev[e][1].get("readset") for e in reused}})
    for x, y, what in pairs:
        if x in wr or y in wr:
            v = (f"RED(shared scratch: {what}; rows run concurrently (GATES-20g), so each keeps its scratch in its own "
                 f"{{fresh}} or a directory no other row writes or reads)")
            print(f"  run concurrency {x} + {y}: {v}")
            results.append(v)
    print(f"  runs wall: {time.monotonic() - t_all:.0f} s ({len(todo)} rows run)")
    if walls_p:
        walls.update({e: {"wall": round(done[e].wall, 1), "ns": bool(done[e].rs and done[e].rs.get("NS"))}
                      for e in todo if done[e].ran})
        try:
            tmpw = f"{walls_p}.{os.getpid()}"
            with open(tmpw, "w", encoding="utf-8") as fh:
                json.dump(walls, fh)
            os.replace(tmpw, walls_p)
        except OSError:
            pass
    record and record.close()
    shutil.rmtree(nobin, ignore_errors=True)
    if a.waste_out:
        with open(a.waste_out, "w", encoding="utf-8") as f:
            f.write("".join(l + "\n" for l in waste))
    red = any(not v.startswith(("ok", "INCOMPLETE", "KILLED", "UNREAD", "ABSENT")) for v in results)
    killed = any(v.startswith("KILLED") for v in results)
    timed = any(v.startswith(("UNREAD(timeout", "UNREAD(tracer")) for v in results)
    inc = any(v.startswith(("INCOMPLETE", "ABSENT")) for v in results)
    word = ("RED" if red else "KILLED(load)" if killed else "UNREAD(timeout)" if timed
            else "INCOMPLETE" if inc else "ok")
    print(f"runs: {word} ({len(results)} runs of {len(want)} exes)")
    return 1 if red else 76 if killed or timed else 3 if inc else 0


if __name__ == "__main__":
    sys.exit(main())
