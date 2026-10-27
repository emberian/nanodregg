#!/usr/bin/env python3
"""gates/interp.py EXE [ARG...] [--harness-control] — the compiled exe held to the interpreter's account (GATES-27).

THE GAP. Every theorem is about a Lean TERM; `decide +kernel` checks a few closed instances of it in the kernel; the
binary that runs is the term after the compiler (LCNF → IR → EmitC → cc), trusted on the compiler's word. CODEC-4
measured that word false once (a string literal the C emitter fuses, GATES-20y). Nothing measured it over the code the
deployment runs.

THE ROW. EXE is a lean_exe of this tree. One run is two runs of the same program on the same arguments:
  compiled     $ND_LEAN_BIN/EXE ARG...                    (the shipped artefact)
  interpreted  lake env lean --run <EXE's root>.lean ARG... (Lean's IR interpreter over the same imported modules)
Both must print byte-identical stdout and stderr and exit with the same code; any difference is RED, naming the first
line that differs. The compiled stdout must hold at least one `TRACE ` line: an exe compared here prints a function of
what it COMPUTED (a World's chain and roots, every verdict name), not only counts, or a hash, signature or codec that
computes other bytes consistently on both sides of its own checks would agree here as well (kernel-sim's
`Gen.traceLine`). Its own verdict (pass, fail, exit 3) is its own row's: this row judges only that the two agree.

WHAT IT MEASURES, AND WHAT NOT. The interpreter runs the same IR the C emitter reads, so this measures EmitC, the C
compiler, the compiled runtime's calling conventions (boxing, borrowed parameters, destructive update of a shared
value) and every user `@[extern]` it reaches against the interpreter. It cannot see an LCNF or IR pass that is wrong
in both, nor an `@[extern]` of Lean's own runtime (both call the same C). The kernel is the evaluator that sees those;
it reaches only small closed instances (a whole seed under whnf is far out of its reach).

--harness-control (the known-red control, GATES-15): the interpreted side is given the NEXT seed (the last all-digit
argument, plus one), so the two sides compute two different runs and the comparator must read RED naming
harness-control. A comparator that read two different runs as one would pass it, and no verdict of this row would be
read. (The exe's own --harness-control is not the control: kernel-sim's adds a required arm that is judged only over
16 seeds, so at one seed it changes nothing: MEASURED, the first control of this row read AGREE.) An argument list
with no seed has no control and is refused as usage, never red.

A red line starts `FAIL interp`; the last line of an agreeing run is `INTERP AGREE` (gates/runs.py reads it exactly).
"""
from __future__ import annotations

import os
import re
import subprocess
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.dont_write_bytecode = True     # rows run concurrently and read gates/ (GATES-20s)

EXE = re.compile(r"lean_exe\s+«([^»]+)»\s+where\s+root\s*:=\s*`([\w.]+)")


def root_file(exe: str) -> str | None:
    """The source of EXE's root module, from lakefile.lean (the one place an exe's root is named)."""
    text = open(os.path.join(ROOT, "lakefile.lean"), encoding="utf-8").read()
    for name, mod in EXE.findall(text):
        if name == exe:
            return mod.replace(".", "/") + ".lean"
    return None


def first_difference(a: str, b: str) -> str:
    al, bl = a.splitlines(), b.splitlines()
    for i, (x, y) in enumerate(zip(al, bl)):
        if x != y:
            return f"line {i + 1}: compiled {x[:200]!r} interpreted {y[:200]!r}"
    return f"compiled has {len(al)} line(s), interpreted {len(bl)}"


def main() -> int:
    argv = sys.argv[1:]
    control = "--harness-control" in argv
    argv = [a for a in argv if a != "--harness-control"]
    if not argv:
        print(__doc__)
        return 2
    exe, args = argv[0], argv[1:]
    label = " ".join([exe] + args)
    src = root_file(exe)
    bindir = os.environ.get("ND_LEAN_BIN", os.path.join(ROOT, ".lake", "build", "bin"))
    binary = os.path.join(bindir, exe)
    if src is None or not os.path.isfile(os.path.join(ROOT, src)):
        print(f"FAIL interp {label}: no lean_exe «{exe}» with a root source in lakefile.lean")
        return 1
    if not os.path.isfile(binary):
        print(f"FAIL interp {label}: no compiled binary {binary}")
        return 1
    t0 = time.monotonic()
    comp = subprocess.run([binary] + args, cwd=ROOT, capture_output=True)
    t1 = time.monotonic()
    iargs = list(args)
    if control:
        seeds = [i for i, a in enumerate(iargs) if a.isdigit()]
        if not seeds:
            print(f"usage: the known-red control needs a seed argument to move (got {label})")
            return 2
        iargs[seeds[-1]] = str(int(iargs[seeds[-1]]) + 1)
    interp = subprocess.run(["lake", "env", "lean", "--run", src] + iargs, cwd=ROOT, capture_output=True)
    t2 = time.monotonic()
    # (this line never names the control: runs.py reads a control as red only when some line names it)
    moved = f" (the control: interpreted with {' '.join(iargs)})" if control else ""
    print(f"interp: {label}{moved}: compiled exit {comp.returncode} in {t1 - t0:.1f} s, interpreted exit "
          f"{interp.returncode} in {t2 - t1:.1f} s ({(t2 - t1) / max(t1 - t0, 1e-3):.0f}x)")
    out_c, out_i = comp.stdout.decode("utf-8", "replace"), interp.stdout.decode("utf-8", "replace")
    # a red that is not a disagreement of two well-formed runs (no trace, a crash) is never the control's: only
    # `differs` lines carry the harness-control label, so a control that reds for another reason is not read as red
    broken = []
    traces = [l for l in out_c.splitlines() if l.startswith("TRACE ")]
    if not traces:
        broken.append("the compiled run printed no `TRACE ` line: counts alone are not a trajectory")
    if interp.returncode not in (0, 1, 3) or comp.returncode not in (0, 1, 3):
        broken.append(f"a run did not end as a verdict exe ends (compiled exit {comp.returncode}, interpreted exit "
                      f"{interp.returncode}): {interp.stderr.decode('utf-8', 'replace')[-600:]!r}")
    differs = []
    if comp.stdout != interp.stdout:
        differs.append("stdout differs, " + first_difference(out_c, out_i))
    if comp.stderr != interp.stderr:
        differs.append("stderr differs, " + first_difference(comp.stderr.decode("utf-8", "replace"),
                                                             interp.stderr.decode("utf-8", "replace")))
    if comp.returncode != interp.returncode:
        differs.append(f"exit differs: compiled {comp.returncode}, interpreted {interp.returncode}")
    for r in broken:
        print(f"FAIL interp {label}: {r}")
    for r in ([] if broken else differs):
        print(f"FAIL interp {label}{' (harness-control)' if control else ''}: {r}")
    if broken or differs:
        return 1
    print(f"interp: {len(traces)} TRACE line(s) agree, {len(comp.stdout)} stdout bytes, {len(comp.stderr)} stderr bytes")
    print(f"interp: {label}: agree")
    print("INTERP AGREE")
    return 0


if __name__ == "__main__":
    sys.exit(main())
