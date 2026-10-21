#!/usr/bin/env python3
"""Re-emit the real theorem certificate and compare the entire pinned object.
The gzip vector is lossless JSON, not a digest. Run under swarm-build on hbox.
No normal verdict run rewrites the vector. --emit-vector is explicit authoring only.
"""
import argparse
import gzip
import json
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
TARGET = "Nanodregg.Ledger.Proofs.grant_moves_le_cap"
VECTOR = ROOT / "gates/certificate-grant.json.gz"


def compare(expected, actual, label="certificate-vector"):
    problems = []
    for field in ("target", "statement", "statementPretty", "statementConstants",
                  "checker", "axioms", "contextAxioms"):
        if expected.get(field) != actual.get(field):
            problems.append(field)
    before = {e["name"]: e for e in expected["context"]}
    after = {e["name"]: e for e in actual["context"]}
    if before.keys() != after.keys():
        added, removed = sorted(after.keys() - before.keys()), sorted(before.keys() - after.keys())
        problems.append(f"unfolded constants: added {len(added)} {added[:8]!r}; "
                        f"removed {len(removed)} {removed[:8]!r}")
    changed = sorted(n for n in before.keys() & after.keys() if before[n] != after[n])
    if changed:
        problems.append(f"declarations ({len(changed)}): " + ", ".join(changed[:12]))
    # Exact object comparison also catches extra fields, duplicates, and list order.
    if expected != actual and not problems:
        problems.append("certificate structure/order")
    if problems:
        print(label + ": RED " + "; ".join(problems))
        return 1
    print(label + ": GREEN")
    return 0


def emit(scratch, extra="", target=TARGET):
    scratch.mkdir(parents=True, exist_ok=True)
    output = scratch / "certificate.json"
    source = scratch / "CertificateRun.lean"
    source.write_text("import Census.Certificate\nimport Ledger.Proofs.GrantCap\n"
                      + extra + "\n#certificate_census " + json.dumps(str(output))
                      + " " + target + "\n")
    result = subprocess.run(["lake", "env", "lean", "-DmaxHeartbeats=200000", str(source)],
                            cwd=ROOT, text=True, stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT)
    (scratch / "extract.log").write_text(result.stdout)
    print(result.stdout, end="", flush=True)
    if result.returncode or "CERTIFICATE ok:" not in result.stdout:
        raise RuntimeError("certificate extraction failed; see " + str(scratch / "extract.log"))
    return json.loads(output.read_text())


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("scratch", type=Path)
    ap.add_argument("--harness-control", action="store_true")
    ap.add_argument("--emit-vector", type=Path)
    ap.add_argument("--check-json", nargs=2, type=Path)
    args = ap.parse_args()
    if args.check_json:
        return compare(*(json.loads(p.read_text()) for p in args.check_json))
    actual = emit(args.scratch)
    if args.emit_vector:
        args.emit_vector.write_bytes(gzip.compress(
            (json.dumps(actual, ensure_ascii=False, separators=(",", ":")) + "\n").encode(),
            mtime=0))
        print("certificate-vector: emitted " + str(args.emit_vector))
        return 0
    expected = json.loads(gzip.decompress(VECTOR.read_bytes()))
    if args.harness_control:
        # An impossible axiom inventory, passed through the actual comparison.
        expected["axioms"] = expected["axioms"] + ["CX_P6_harness_control"]
    return compare(expected, actual, "certificate-vector harness-control"
                   if args.harness_control else "certificate-vector")


if __name__ == "__main__":
    sys.exit(main())
