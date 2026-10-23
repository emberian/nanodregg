#!/usr/bin/env python3
"""gates/certificate.py SCRATCH [--harness-control] [--emit-pin PATH] [--check-json A B] — the certificate pin of
grant_moves_le_cap (decisions/gates.md GATES-20u; review H3). Run under swarm-build on hbox, over the built tree.

Census/Certificate.lean's `#certificate_pin` emits, from the built Environment, the theorem's statement, its
`collectAxioms` set, each direct support's statement and each statement word's declaration. This script replaces
every encoding by its SHA-256 and compares the result with gates/certificate-grant.json section by section; a
difference is RED by section and name. A change in the cone that keeps the four sections is GREEN (the old
whole-closure vector made every such change RED). No verdict run writes the pin; --emit-pin is explicit authoring.
--check-json compares two emitted objects (gates/certificate_plants.py uses it).
"""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
TARGET = "Nanodregg.Ledger.Proofs.grant_moves_le_cap"
PIN = ROOT / "gates/certificate-grant.json"
FIELDS = ("target", "statement", "axioms", "supports", "vocabulary")
# The compared sections (gates/certificate_plants.py drops one in a scratch copy: its plant must then escape).
SECTIONS = ("statement", "axioms", "supports", "vocabulary")


def sha(text: str) -> str:
    return hashlib.sha256(text.encode()).hexdigest()


def digest(emitted: dict) -> dict:
    """The pin of one emitted object: every encoding replaced by its SHA-256."""
    return {"target": emitted["target"], "statement": sha(emitted["statement"]),
            "axioms": sorted(emitted["axioms"]),
            "supports": {n: sha(e) for n, e in sorted(emitted["supports"].items())},
            "vocabulary": {n: sha(json.dumps(ps)) for n, ps in sorted(emitted["vocabulary"].items())}}


def differences(expected: dict, actual: dict, pretty: str | None = None) -> list[str]:
    red = []
    if sorted(expected) != sorted(FIELDS):
        red.append(f"pin fields {sorted(expected)}, need {sorted(FIELDS)}")
    if expected.get("target") != actual["target"]:
        red.append(f"target {expected.get('target')} -> {actual['target']}")
    for sec in SECTIONS:
        a, b = expected.get(sec), actual[sec]
        if a == b:
            continue
        if sec == "statement":
            red.append("statement" + (f" (live: {pretty})" if pretty else ""))
        elif sec == "axioms":
            a = a or []
            red.append(f"axioms added {sorted(set(b) - set(a))} removed {sorted(set(a) - set(b))}")
        else:
            a = a or {}
            parts = (("changed", sorted(n for n in a.keys() & b.keys() if a[n] != b[n])),
                     ("added", sorted(b.keys() - a.keys())), ("removed", sorted(a.keys() - b.keys())))
            red.append(sec + " " + "; ".join(f"{w} {v}" for w, v in parts if v))
    return red


def verdict(expected: dict, actual: dict, label: str, pretty: str | None = None) -> int:
    red = differences(expected, actual, pretty)
    if red:
        print(label + ": RED " + " | ".join(red))
        return 1
    print(label + ": GREEN")
    return 0


def run_lean(scratch: Path, source: Path, extra: list[str]) -> str:
    """The tree's lean over SOURCE; whole output to SCRATCH/<stem>.log, then read (never a pipe)."""
    log = scratch / (source.stem + ".log")
    with open(log, "w") as fh:
        code = subprocess.run(["lake", "env", "lean", "-DmaxHeartbeats=200000", *extra, str(source)],
                              cwd=ROOT, stdout=fh, stderr=subprocess.STDOUT).returncode
    out = log.read_text()
    print(out, end="", flush=True)
    if code or "CERTIFICATE ok:" not in out:
        raise SystemExit(f"certificate-pin: RED extraction failed (exit {code}); see {log}")
    return out


def emit(scratch: Path) -> dict:
    """The emitted object of TARGET over the built tree."""
    scratch.mkdir(parents=True, exist_ok=True)
    output = scratch / "certificate.json"
    source = scratch / "CertificatePin.lean"
    source.write_text("import Census.Certificate\nimport Ledger.Proofs.GrantCap\n\n#certificate_pin "
                      + json.dumps(str(output)) + " " + TARGET + "\n")
    run_lean(scratch, source, [])
    return json.loads(output.read_text())


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("scratch", type=Path)
    ap.add_argument("--harness-control", action="store_true")
    ap.add_argument("--emit-pin", type=Path)
    ap.add_argument("--check-json", nargs=2, type=Path)
    args = ap.parse_args()
    if args.check_json:
        a, b = (json.loads(p.read_text()) for p in args.check_json)
        return verdict(digest(a), digest(b), "certificate-pin", b.get("statementPretty"))
    actual = emit(args.scratch)
    if args.emit_pin:
        args.emit_pin.write_text(json.dumps(digest(actual), indent=1, sort_keys=True) + "\n")
        print("certificate-pin: emitted " + str(args.emit_pin))
        return 0
    expected = json.loads(PIN.read_text())
    if args.harness_control:
        # An impossible axiom set, through the same comparison.
        expected["axioms"] = sorted(expected.get("axioms", []) + ["CX_G2_harness_control"])
    return verdict(expected, digest(actual), "certificate-pin harness-control" if args.harness_control
                   else "certificate-pin", actual["statementPretty"])


if __name__ == "__main__":
    sys.exit(main())
