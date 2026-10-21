#!/usr/bin/env python3
"""Real Environment plants for the P6 certificate vector (hbox, under swarm-build).
Only lane scratch files are written; no theorem, gate, or compiled module is overwritten.
"""
import copy
import importlib.util
import json
import os
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
LOGS = Path("/tank/dregg-build/nanodregg/logs")
SCRATCH = LOGS / "CX-P6-environment-plants"
SCRATCH.mkdir(exist_ok=True)
(LOGS / "CX-P6-environment-plants.pid").write_text(str(os.getpid()) + "\n")
spec = importlib.util.spec_from_file_location("certificate", ROOT / "gates/certificate.py")
gate = importlib.util.module_from_spec(spec)
spec.loader.exec_module(gate)


def save(path, obj):
    path.write_text(json.dumps(obj, ensure_ascii=False))


def compare_run(label, before, after, want, script=None):
    where = SCRATCH / label
    where.mkdir(exist_ok=True)
    save(where / "before.json", before)
    save(where / "after.json", after)
    result = subprocess.run(
        [sys.executable, str(script or ROOT / "gates/certificate.py"), str(where),
         "--check-json", str(where / "before.json"), str(where / "after.json")],
        cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
    path = LOGS / ("CX-P6-env-" + label + ".log")
    path.write_text(result.stdout)
    print(str(path) + ": exit " + str(result.returncode), flush=True)
    print(result.stdout, end="", flush=True)
    if re.search(r"error:|unbound|No such file|Traceback", result.stdout, re.I):
        raise RuntimeError("unexpected diagnostic in whole output: " + str(path))
    if result.returncode != want:
        raise RuntimeError("wrong verdict: " + str(path))
    return result.stdout


def twin(extra_axiom):
    # The type is the actual landed theorem's type, read from this Environment.
    declaration = """
open Lean Elab Command in
elab "#make_p6_twin" : command => do
  let .thmInfo v ← getConstInfo `Nanodregg.Ledger.Proofs.grant_moves_le_cap
    | throwError "expected a theorem"
"""
    if extra_axiom:
        declaration += """
  liftCoreM <| addDecl (.axiomDecl {
    name := `CX_P6_extra, levelParams := v.levelParams, type := v.type, isUnsafe := false })
"""
    body = "CX_P6_extra" if extra_axiom else gate.TARGET
    return declaration + """
  liftCoreM <| addDecl (.thmDecl { v with
    name := `CX_P6_twin, value := mkConst `""" + body + """ (v.levelParams.map Level.param) })
#make_p6_twin
"""


def coverage_plant():
    # Poison only a scratch copy of the real adapter's axiom classification.
    # The production coverage guard must catch the resulting trusted-read-off mismatch.
    data = (ROOT / "Census/CertificateData.lean").read_text()
    command = (ROOT / "Census/Certificate.lean").read_text()
    needle = "ci.isAxiom, ci.isTheorem"
    if data.count(needle) != 1:
        raise RuntimeError("ambiguous axiom-classification plant")
    data = data.replace(needle, "false, ci.isTheorem")
    command = command.replace("import Census.CertificateData\n", "")
    guard = "unless axs.all (fun n => c.assumptions.contains n) do"
    if command.count(guard) != 1:
        raise RuntimeError("ambiguous coverage guard")
    for label, body, wanted in (
            ("coverage-guard", command, 1),
            ("coverage-disabled", command.replace(guard, "unless true do"), 0)):
        where = SCRATCH / label
        where.mkdir(exist_ok=True)
        output = where / "certificate.json"
        source = where / "CoverageRun.lean"
        source.write_text(data + "\n" + body + """
axiom CX_P6_coverage_axiom : True
theorem CX_P6_coverage : True := CX_P6_coverage_axiom
#certificate_census """ + json.dumps(str(output)) + " CX_P6_coverage\n")
        result = subprocess.run(
            ["lake", "env", "lean", "-DmaxHeartbeats=200000", str(source)],
            cwd=ROOT, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        path = LOGS / ("CX-P6-env-" + label + ".log")
        path.write_text(result.stdout)
        print(str(path) + ": exit " + str(result.returncode), flush=True)
        print(result.stdout, end="", flush=True)
        lines = result.stdout.splitlines()
        expected_error = "error: CERTIFICATE RED: collectAxioms escaped the context"
        unexpected = [line for line in lines if re.search(
            r"error:|unbound|No such file|Traceback", line, re.I) and expected_error not in line]
        if unexpected or result.returncode != wanted:
            raise RuntimeError("wrong coverage plant outcome: " + str(path))
        if wanted == 1 and not any(expected_error in line for line in lines):
            raise RuntimeError("coverage guard did not refuse by name")
        if wanted == 0:
            c = json.loads(output.read_text())
            if c["axioms"] != ["CX_P6_coverage_axiom"] or c["contextAxioms"]:
                raise RuntimeError("disabled guard did not expose missing axiom coverage")
            # A separate executable assertion goes RED on that actually emitted certificate.
            probe = subprocess.run(
                [sys.executable, "-c",
                 "import json,sys; c=json.load(open(sys.argv[1])); "
                 "ok=set(c['axioms']) <= set(c['contextAxioms']); "
                 "print('certificate-coverage: GREEN' if ok else "
                 "'FAIL certificate-coverage: emitted target axioms escape the context'); "
                 "sys.exit(0 if ok else 1)", str(output)],
                text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
            (LOGS / "CX-P6-env-coverage-tooth.log").write_text(probe.stdout)
            print(probe.stdout, end="", flush=True)
            if probe.returncode != 1 or "FAIL certificate-coverage:" not in probe.stdout:
                raise RuntimeError("coverage assertion did not go red")
    print("certificate-coverage-plant: GREEN", flush=True)


if "--coverage-only" in sys.argv:
    coverage_plant()
    sys.exit(0)


normal = gate.emit(SCRATCH / "twin-original", twin(False), "CX_P6_twin")
mutant = gate.emit(SCRATCH / "twin-axiom", twin(True), "CX_P6_twin")
if "CX_P6_extra" not in mutant["axioms"] or "CX_P6_extra" in normal["axioms"]:
    raise RuntimeError("the real collectAxioms read did not observe the planted axiom")
out = compare_run("extra-axiom", normal, mutant, 1)
if "RED" not in out or "axioms" not in out:
    raise RuntimeError("extra axiom was not refused by name")

base_source = """
def CX_P6_dependency : Nat := Nat.zero
theorem CX_P6_small : CX_P6_dependency = Nat.zero := rfl
"""
base = gate.emit(SCRATCH / "constant-original", base_source, "CX_P6_small")
changed = gate.emit(SCRATCH / "constant-changed",
                    base_source.replace(":= Nat.zero", ":= Nat.add Nat.zero Nat.zero"),
                    "CX_P6_small")
if base["statement"] != changed["statement"] or base["axioms"] != changed["axioms"]:
    raise RuntimeError("constant plant changed the statement or axiom set")
out = compare_run("unfolded-constant", base, changed, 1)
if "RED" not in out or "CX_P6_dependency" not in out:
    raise RuntimeError("definition change was not refused by name")

# The same real mutated Environment outputs expose a disabled vector comparison.
disabled = SCRATCH / "disabled-comparison.py"
source = (ROOT / "gates/certificate.py").read_text()
if source.count("if problems:") != 1:
    raise RuntimeError("ambiguous comparison plant")
disabled.write_text(source.replace("if problems:", "if False:"))
# A real rejection test must go red against the disabled comparator, not just print a verdict.
probe = SCRATCH / "rejection_probe.py"
probe.write_text(
    "import subprocess, sys\n"
    "r = subprocess.run(sys.argv[1:])\n"
    "if r.returncode != 1:\n"
    "    print(f'FAIL certificate-rejection: expected exit 1; actual exit {r.returncode}')\n"
    "    sys.exit(1)\n"
    "print('certificate-rejection: GREEN')\n")
where = SCRATCH / "extra-axiom"
result = subprocess.run(
    [sys.executable, str(probe), sys.executable, str(disabled), str(where),
     "--check-json", str(where / "before.json"), str(where / "after.json")],
    text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, cwd=ROOT)
path = LOGS / "CX-P6-env-disabled-check.log"
path.write_text(result.stdout)
print(str(path) + ": exit " + str(result.returncode), flush=True)
print(result.stdout, end="", flush=True)
if re.search(r"error:|unbound|No such file|Traceback", result.stdout, re.I):
    raise RuntimeError("unexpected diagnostic in disabled-check output")
if result.returncode != 1 or "FAIL certificate-rejection: expected exit 1; actual exit 0" not in result.stdout:
    raise RuntimeError("disabled comparison did not make the rejection test red")
compare_run("unchanged", normal, copy.deepcopy(normal), 0)
coverage_plant()
print("certificate-environment-plants: GREEN", flush=True)
