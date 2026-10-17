"""gates/runs.py TREE [--changed FILE] [--waste-out FILE] — the verdict runs (sims, journeys, rows,
plants): every lean_exe whose answer is a verdict, run over the built TREE as gates/runs.tsv says.

gates/runs.tsv rows, `exe<TAB>runs<TAB>pass`:
  runs  the argument lists, separated by ` ; `, each one run of the exe (`(none)`: no arguments). `{host}` is the built
        `host` exe and `{fresh}` a fresh directory under TREE/.lake/runs (it does not exist when the
        run starts; it is removed after). `-` = not a verdict exe (a generator or the deployed
        binary), with the reason in `pass`.
  pass  the last line a passing run prints.
Every lean_exe has exactly one row (check.py's `runs` gate), so a new exe is classified when it lands.

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

import tree

RUNS = os.path.join("gates", "runs.tsv")
DEADLINE = 600


def table(root: str) -> dict[str, tuple[list[list[str]] | None, str]]:
    """exe -> (runs, pass line); runs is None for a `-` row. Malformed rows raise ValueError."""
    out: dict[str, tuple[list[list[str]] | None, str]] = {}
    p = os.path.join(root, RUNS)
    if not os.path.isfile(p):
        return out
    for n, line in enumerate(open(p, encoding="utf-8"), 1):
        if not line.strip() or line.startswith("#"):
            continue
        f = line.rstrip("\n").split("\t")
        if len(f) != 3 or not f[0].strip() or not f[1].strip() or not f[2].strip():
            raise ValueError(f"{RUNS}:{n}: need exe<TAB>runs<TAB>pass: {line.rstrip()!r}")
        if f[0] in out:
            raise ValueError(f"{RUNS}:{n}: second row for {f[0]}")
        runs = None if f[1].strip() == "-" else [[] if r.strip() == "(none)" else r.split() for r in f[1].split(" ; ")]
        out[f[0]] = (runs, f[2])
    return out


def check(t: tree.Tree) -> list[str]:
    """The table classifies exactly the lakefile's exes."""
    try:
        rows = table(t.root)
    except ValueError as e:
        return [str(e)]
    exes = set(t.exes)
    return ([f"lean_exe {e} has no row in {RUNS} (a verdict run, or `-` with why it is not one)" for e in sorted(exes - set(rows))]
            + [f"{RUNS} row {e} names no lean_exe" for e in sorted(set(rows) - exes)])


def selected(t: tree.Tree, changed: list[str] | None) -> set[str]:
    if changed is None or any(p in ("lakefile.lean", "lean-toolchain", RUNS) or p.endswith((".c", ".h")) for p in changed):
        return set(t.exes)
    mods = {p[:-5].replace("/", ".") for p in changed if p.endswith(".lean")}
    return {e for e, r in t.exes.items() if t.closure([r]) & mods}


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
    changed = open(a.changed, encoding="utf-8").read().split() if a.changed else None
    want = selected(t, changed)
    bindir = os.path.join(t.root, ".lake", "build", "bin")
    scratch = os.path.join(t.root, ".lake", "runs")
    waste = []
    results = []
    for exe in sorted(want & set(rows)):
        runs, passline = rows[exe]
        for k, args in enumerate(runs or []):
            fresh = os.path.join(scratch, f"{exe}-{k}")
            shutil.rmtree(fresh, ignore_errors=True)
            os.makedirs(scratch, exist_ok=True)
            argv = [os.path.join(bindir, exe)] + [x.replace("{host}", os.path.join(bindir, "host")).replace("{fresh}", fresh) for x in args]
            if not os.path.isfile(argv[0]):
                print(f"  run {exe} {' '.join(args)}: ABSENT(no binary)")
                continue
            try:
                r = subprocess.run(argv, cwd=t.root, capture_output=True, text=True, timeout=DEADLINE)
                # The verdict reads stdout, where the pass line is printed; the log keeps both.
                out, v = r.stdout + r.stderr, verdict(r.stdout or r.stderr, r.returncode, passline)
            except subprocess.TimeoutExpired:
                out, v = "", f"TIMEOUT({DEADLINE} s)"
            shutil.rmtree(fresh, ignore_errors=True)
            sys.stderr.write(out)
            waste += [l for l in out.splitlines() if l.startswith("WASTE ")]
            print(f"  run {exe} {' '.join(args)}: {v}")
            results.append(v)
    if a.waste_out:
        with open(a.waste_out, "w", encoding="utf-8") as f:
            f.write("".join(l + "\n" for l in waste))
    red = any(not v.startswith(("ok", "INCOMPLETE", "KILLED")) for v in results)
    killed = any(v.startswith("KILLED") for v in results)
    inc = any(v.startswith("INCOMPLETE") for v in results)
    word = "RED" if red else "KILLED(load)" if killed else "INCOMPLETE" if inc else "ok"
    print(f"runs: {word} ({len(results)} runs of {len(want)} exes)")
    return 1 if red else 76 if killed else 3 if inc else 0


if __name__ == "__main__":
    sys.exit(main())
