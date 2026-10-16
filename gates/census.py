"""gates/census.py TREE — run the axiom census over every built module of TREE.

Writes .lake/gates/CensusRun.lean importing every module outside Census except the lean_exe roots (they hold only `main`,
closure C7, and two `main`s cannot share one environment), then runs
`#axiom_census "gates/axioms-allow.tsv" <every lib but Census>` under `lake env lean`.
Every module must already be built (scripts/pre-push builds first).
"""
import os
import subprocess
import sys

import tree


def main(root: str) -> int:
    t = tree.read(root)
    roots = set(t.exes.values())  # exe roots hold only `main` (closure C7); two would collide
    mods = sorted(m for m in t.modules if t.modules[m].lib != "Census" and m not in roots)
    libs = sorted(set(t.modules[m].lib for m in mods))
    if not mods:
        print("census: ok (no modules)")
        return 0
    os.makedirs(os.path.join(t.root, ".lake", "gates"), exist_ok=True)
    run = os.path.join(t.root, ".lake", "gates", "CensusRun.lean")
    with open(run, "w", encoding="utf-8") as f:
        f.write("import Census.Axioms\n" + "".join(f"import {m}\n" for m in mods))
        f.write(f'#axiom_census "gates/axioms-allow.tsv" {" ".join(libs)}\n')
    r = subprocess.run(["lake", "env", "lean", run], cwd=t.root, capture_output=True, text=True)
    out = (r.stdout + r.stderr).strip()
    print(out)
    ok = r.returncode == 0 and "AXIOM-CENSUS ok" in out
    print(f"census: {'ok' if ok else 'RED'}")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1] if len(sys.argv) > 1 else "."))
