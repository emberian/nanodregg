#!/usr/bin/env python3
"""gates/build_peak.py SCRATCH [--harness-control] — the elaboration memory of the modules a build
cannot afford to be surprised by (HOSTING-51).

gates/build-peaks.tsv holds `module<TAB>ceiling-MiB<TAB>why`. For each row this elaborates the
module's source alone, single-threaded (`LEAN_NUM_THREADS=1 lake env lean FILE`, after the build:
its imports are the built tree's), and reads the peak resident set of that process and its children
from the kernel (`os.wait4`'s ru_maxrss). A row is FAIL when the peak is above its ceiling, when
the module's file is gone, or when elaboration fails. The measured peak is printed for every row.

Why a row exists: Hosting/Proofs/Reply.lean took 13.1 GB (a closed-instance `decide +kernel` over a
650-byte body) and was found only when a 6 GB convergence was cgroup-killed on it. A ceiling here
makes the next such regression a named red in the judge, not an OOM in another lane.

--harness-control (GATES-15): every ceiling is read as 1 MiB, which a real elaboration exceeds, so
every row is FAIL and the output names harness-control. SCRATCH is unused (the runs.tsv `{fresh}`).
"""
import os
import subprocess
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
TABLE = os.path.join("gates", "build-peaks.tsv")
CONTROL = "--harness-control" in sys.argv


def rows() -> list[tuple[str, int, str]]:
    out = []
    with open(os.path.join(ROOT, TABLE), encoding="utf-8") as f:
        for n, line in enumerate(f, 1):
            if not line.strip() or line.startswith("#"):
                continue
            p = line.rstrip("\n").split("\t")
            if len(p) != 3 or not p[1].isdigit() or not p[2].strip():
                raise SystemExit(f"FAIL {TABLE}:{n}: need module<TAB>ceiling-MiB<TAB>why: {line.rstrip()!r}")
            out.append((p[0], int(p[1]), p[2]))
    if not out:
        raise SystemExit(f"FAIL {TABLE}: no rows (a table over nothing checks nothing)")
    return out


def peak(path: str) -> tuple[int, int, str]:
    """(exit code, peak RSS in KiB over the process and its waited children, output)."""
    env = dict(os.environ, LEAN_NUM_THREADS="1")
    p = subprocess.Popen(["lake", "env", "lean", path], cwd=ROOT, env=env,
                         stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    out = p.stdout.read().decode(errors="replace")
    _, status, ru = os.wait4(p.pid, 0)
    p.returncode = os.waitstatus_to_exitcode(status)
    return p.returncode, ru.ru_maxrss, out


def main() -> int:
    fails = []
    for module, ceiling, _ in rows():
        path = os.path.join(*module.split(".")) + ".lean"
        if not os.path.isfile(os.path.join(ROOT, path)):
            fails.append(f"FAIL {module}: {path} is gone (a stale row)")
            continue
        code, kib, out = peak(path)
        mib = (kib + 1023) // 1024
        limit = 1 if CONTROL else ceiling
        print(f"{module}\tpeak {mib} MiB\tceiling {limit} MiB" + (" (harness-control)" if CONTROL else ""))
        if code != 0:
            last = (out.strip().splitlines() or ["no output"])[-1]
            fails.append(f"FAIL {module}: elaboration exited {code}: {last}")
        elif mib > limit:
            fails.append(f"FAIL {module}: peak {mib} MiB above its ceiling {limit} MiB"
                         + (" (harness-control: every ceiling read as 1 MiB)" if CONTROL else ""))
    for f in fails:
        print(f)
    if fails:
        return 1
    print("BUILD PEAKS GREEN")
    return 0


if __name__ == "__main__":
    sys.exit(main())
