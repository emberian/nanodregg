#!/usr/bin/env python3
"""Scoped check-disabling plants. Run on hbox under swarm-build with a private worktree.

Only this lane's certificate source is temporarily mutated. Finally restores byte-for-byte
source, then rebuilds both the proof module and test executable. No cache is removed.
Each verdict is read from the entire captured output; successful compilation is mandatory.
"""
import os
from pathlib import Path
import re
import subprocess

root = Path(__file__).resolve().parents[1]
logs = Path("/tank/dregg-build/nanodregg/logs")
(logs / "CX-P6-plants.pid").write_text(str(os.getpid()) + "\n")
source = root / "Lang/Contextual/Certificate.lean"
original = source.read_text()
exe = root / ".lake/build/bin/certificate-tests"


def run(label, argv, want):
    p = subprocess.run(argv, cwd=root, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    path = logs / ("CX-P6-" + label + ".log")
    path.write_text(p.stdout)
    print(str(path) + ": exit " + str(p.returncode), flush=True)
    print(p.stdout, end="", flush=True)
    if re.search(r"error:|unbound|No such file|Traceback", p.stdout, re.I):
        raise RuntimeError("unexpected diagnostic in whole output: " + str(path))
    if p.returncode != want:
        raise RuntimeError("wrong exit: " + str(path))
    return p.stdout


guards = [
    ("checker", "c.checker ≠ r.checker"),
    ("not-theorem", "r.isTheorem target ≠ true"),
    ("statement", "c.statement ≠ r.typeOf target"),
    ("target-context", "(c.context.any fun e => decide (e.name = c.target ∧ e.body = target)) ≠ true"),
    ("definition", "(c.context.all fun e => decide (r.lookup e.name = some e.body)) ≠ true"),
    ("transitive-constant", "((r.references c.statement ++ c.context.flatMap (fun e => reads r e.body)).all\n        fun n => decide (n ∈ names c)) ≠ true"),
    ("assumptions", "c.assumptions ≠ assumptions r c.context"),
]
try:
    run("plants-baseline-build", ["lake", "build", "certificate-tests"], 0)
    run("plants-baseline", [str(exe)], 0)
    out = run("plants-control", [str(exe), "--harness-control"], 1)
    if "FAIL certificate: harness-control;" not in out:
        raise RuntimeError("control did not fail by name")
    for name, condition in guards:
        needle = "if " + condition + " then"
        if original.count(needle) != 1:
            raise RuntimeError("ambiguous plant: " + name)
        source.write_text(original.replace(needle, "if False then"))
        run("plant-" + name + "-build", ["lake", "build", "certificate-tests"], 0)
        out = run("plant-" + name, [str(exe)], 1)
        lines = [line for line in out.splitlines() if line.startswith("FAIL certificate: " + name + ";")]
        if len(lines) != 1 or "actual Except.ok ()" not in lines[0]:
            raise RuntimeError("plant did not expose acceptance of invalid certificate: " + name)
        print("CAPTURED " + lines[0], flush=True)
    # Missing target has no body with which to continue; the mutant accepts that branch.
    source.write_text(original.replace("| none => .error .missingTarget", "| none => .ok ()", 1))
    run("plant-missing-target-build", ["lake", "build", "certificate-tests"], 0)
    out = run("plant-missing-target", [str(exe)], 1)
    if not any(line.startswith("FAIL certificate: missing-target;") and "actual Except.ok ()" in line
               for line in out.splitlines()):
        raise RuntimeError("missing target plant did not expose an accepted absent declaration")
finally:
    source.write_text(original)
    run("plants-restored-build", ["lake", "build", "Lang.Proofs.Contextual.Certificate", "certificate-tests"], 0)
    run("plants-restored", [str(exe)], 0)
print("certificate-plants: GREEN", flush=True)
