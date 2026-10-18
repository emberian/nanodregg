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

A cargo run is ok on exit 0 with libtest's summary saying at least one test passed (a run that
ran zero tests, or whose summary the reader cannot find, is RED: an absent verdict is not a pass).
A run is ok on exit 0 with its pass line last; INCOMPLETE on exit 3 (a row with no driver yet:
pending is a real outcome, law 7); RED otherwise, naming the first `FAIL`/`ROW … FAIL`/`PLANT …
FAIL` line or the exit code and last line; TIMEOUT after 600 s. `WASTE <op> <metric> <ratio>` lines
go to --waste-out. With --changed (pre-push), only the exes whose import closure holds a changed
module run (all of them when the lakefile, the toolchain or a C source changed): a sim is a verdict
a build cannot give, so the importers of a change are RUN, not only built (ROOT/HOSTING 10-17, after
HOSTING's grain text went stale under LANG's ID-1 with every build green).
A run killed by signal 9/15 (earlyoom, the cgroup) is KILLED(load), not RED (GATES-11's amendment).
Prints one `  run <exe> <args>: <verdict>` line per run and `runs: ok|RED|KILLED(load)|INCOMPLETE`;
exits 0, 1, 76 (killed, nothing red) or 3 (incomplete, nothing red or killed).
"""
import argparse
import os
import re
import shutil
import subprocess
import sys
import tomllib

import tree

RUNS = os.path.join("gates", "runs.tsv")
DEADLINE = 600


CONTROL = "harness-control"
NOBIN = ("nobin RED", "nobin ok")


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
        if f[0] in out:
            raise ValueError(f"{RUNS}:{n}: second row for {f[0]}")
        if f[0].startswith("cargo:"):
            if len(f[0].split(":")) != 3 or f[2] != "exit 0" or f[3] not in NOBIN:
                raise ValueError(f"{RUNS}:{n}: a cargo row is cargo:CRATE:TEST<TAB>EXE,…<TAB>exit 0<TAB>nobin RED|nobin ok: {line.rstrip()!r}")
            out[f[0]] = ([[x.strip() for x in f[1].split(",") if x.strip()]], f[2], f[3])
            continue
        if f[1].strip() == "-":
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
    red = ([f"lean_exe {e} has no row in {RUNS} (a verdict run, or `-` with why it is not one)" for e in sorted(exes - set(rows))]
           + [f"{RUNS} row {e} names no lean_exe" for e in sorted(set(rows) - exes - cargo - script)]
           + [f"{RUNS} row {k}: no executable {k[len('script:'):]}" for k in sorted(script)
              if not os.access(os.path.join(t.root, k[len("script:"):]), os.X_OK)]
           + [f"{RUNS} row {k}: a script row is a verdict run (runs, pass, a --{CONTROL} control), never `-`"
              for k in sorted(script) if rows[k][0] is None])
    for k in sorted(cargo):
        _, crate, test = k.split(":")
        if not os.path.isfile(os.path.join(t.root, crate, "tests", test + ".rs")):
            red.append(f"{RUNS} row {k}: no {crate}/tests/{test}.rs")
        red += [f"{RUNS} row {k}: drives {e}, which is no lean_exe" for e in rows[k][0][0] if e not in exes]
    if cargo and not any(rows[k][2] == "nobin RED" for k in cargo):
        red.append(f"{RUNS}: no cargo row has the control `nobin RED`, so nothing proves the cargo reader reads a failure")
    return red


def selected(t: tree.Tree, changed: list[str] | None, rows: dict) -> set[str]:
    cargo = {k: rows[k][0][0] for k in rows if k.startswith("cargo:")}
    script = {k for k in rows if k.startswith("script:")}
    if changed is None or any(p in ("lakefile.lean", "lean-toolchain", RUNS) or p.endswith((".c", ".h")) for p in changed):
        return set(t.exes) | set(cargo) | script
    mods = {p[:-5].replace("/", ".") for p in changed if p.endswith(".lean")}
    out = {e for e, r in t.exes.items() if t.closure([r]) & mods}
    return out | script | {k for k, drives in cargo.items()
                  if set(drives) & out or any(p.startswith(k.split(":")[1] + "/") for p in changed)}


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
        argv = [os.path.join(bindir, exe)] + [x.replace("{host}", host).replace("{fresh}", fresh) for x in args]
        if not os.path.isfile(argv[0]):
            return "", "ABSENT(no binary: " + exe + ")"
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
    except subprocess.TimeoutExpired:
        out, v = "", f"TIMEOUT({DEADLINE} s)"
    shutil.rmtree(fresh, ignore_errors=True)
    return out, v


def redlines(exe: str, out: str) -> list[str]:
    """The lines that name a failure: a cargo row's failed test names, an exe's FAIL/BLIND/RED lines."""
    if exe.startswith("cargo:"):
        return sorted(set(re.findall(r"(?m)^---- (\S+) stdout ----", out)))
    return [l.strip() for l in out.splitlines()
            if not l.startswith("WASTE ") and re.search(r"\b(FAIL|FAILED|BLIND|RED)\b", l)]


def control_reads_red(exe: str, v: str, out: str) -> str | None:
    """None when a known-red control read red; else why the harness is refused."""
    if v.startswith(("KILLED", "TIMEOUT", "ABSENT")):
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
    ap.add_argument("--table", help="judge with this runs.tsv instead of TREE's (pre-push runs the\n"
                    "candidate's table over the parent tree, so both sides make the same runs)")
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

    def report(exe: str, args: list[str], v: str, out: str, tag: str = "") -> None:
        sys.stderr.write(out)
        name = f"{exe} {' '.join(args)}{tag}"
        print(f"  run {name}: {v}")
        results.append(v)
        # Every failure line of a red run is its own key (`    red RUN: LINE`): pre-push calls a red
        # PRE-EXISTING only line by line, so a new failure behind an old one on the same exe is new.
        if v.startswith(("RED", "TIMEOUT")):
            for l in redlines(exe, out)[:40]:
                print(f"    red {name}: {l}")

    todo = sorted(e for e in want & set(rows) if rows[e][0])
    # The cargo reader's own control: whenever a cargo row runs, some `nobin RED` control runs first.
    cargo = [e for e in todo if e.startswith("cargo:")]
    if cargo and not any(rows[e][2] == "nobin RED" for e in cargo):
        first = next((e for e in sorted(rows) if e.startswith("cargo:") and rows[e][2] == "nobin RED"), None)
        if first is None:
            report("cargo", [], f"RED(harness: no `nobin RED` row proves the cargo reader)", "", " (control)")
        elif mine(first):
            out, v = run(t, first, [], "exit 0", os.path.join(scratch, "reader"), nobin)
            report(first, [], control_reads_red(first, v, out) or "ok(known-red control read red)", out, " (reader control)")
    for exe in todo:
        runs, passline, control = rows[exe]
        if not mine(exe):
            for args in runs:
                print(f"  run {exe} {' '.join(args)}: NOT RUN(not in this tree's own table)")
            continue
        # The known-red control runs FIRST: a runner that cannot read a failure has no verdict to read.
        if exe.startswith("cargo:"):
            out, v = run(t, exe, [], passline, os.path.join(scratch, f"{exe}-control"), nobin)
            if control == "nobin RED":
                bad = control_reads_red(exe, v, out)
            else:   # `nobin ok`: declared to run no exe, so it must pass with none
                bad = None if v == "ok" or v.startswith(("KILLED", "TIMEOUT")) else \
                    f"RED(harness: declared `nobin ok` but with no Lean binaries it read {v})"
            cv, cargs = (bad or ("ok(known-red control read red)" if control == "nobin RED" else v)), []
        else:
            out, v = run(t, exe, control, passline, os.path.join(scratch, f"{exe}-control"), bindir)
            bad = control_reads_red(exe, v, out)
            cv, cargs = (bad or "ok(known-red control read red)"), control
        # A control's WASTE lines are not measurements (it plants); they are never collected.
        report(exe, cargs, cv if not v.startswith(("KILLED", "TIMEOUT", "ABSENT")) or bad else v, out, " (control)")
        if bad or v.startswith(("KILLED", "TIMEOUT", "ABSENT")):
            for args in runs:
                print(f"  run {exe} {' '.join(args)}: UNREAD(its known-red control did not read red)")
            continue
        for k, args in enumerate(runs):
            out, v = run(t, exe, args, passline, os.path.join(scratch, f"{exe}-{k}"), bindir,
                         args if exe.startswith("cargo:") else ())
            waste += [l for l in out.splitlines() if l.startswith("WASTE ")]
            report(exe, [] if exe.startswith("cargo:") else args, v, out)
    shutil.rmtree(nobin, ignore_errors=True)
    if a.waste_out:
        with open(a.waste_out, "w", encoding="utf-8") as f:
            f.write("".join(l + "\n" for l in waste))
    red = any(not v.startswith(("ok", "INCOMPLETE", "KILLED", "ABSENT")) for v in results)
    killed = any(v.startswith("KILLED") for v in results)
    inc = any(v.startswith(("INCOMPLETE", "ABSENT")) for v in results)
    word = "RED" if red else "KILLED(load)" if killed else "INCOMPLETE" if inc else "ok"
    print(f"runs: {word} ({len(results)} runs of {len(want)} exes)")
    return 1 if red else 76 if killed else 3 if inc else 0


if __name__ == "__main__":
    sys.exit(main())
