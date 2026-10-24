"""gates/census.py TREE — run the axiom census over every built module of TREE.

Writes .lake/gates/CensusRun.lean importing every module outside Census except the lean_exe roots (they hold only `main`,
closure C7, and two `main`s cannot share one environment), then runs
`#axiom_census "gates/axioms-allow.tsv" <every lib but Census>` and `#refine_census "gates/refines-allow.tsv" "gates/codec-vectors.tsv" …`
(CODEC-28: every refinement carries its lawfulness theorem) and
`#statement_census ".lake/gates/statements.tsv" …` over elaborated theorem conclusions under `lake env lean`
(GATES-20s: a disjunct comparing two inputs the statement chooses is red, and its fixtures are judged first:
a misread fixture prints `STATEMENT-CENSUS harness:`, never `STATEMENT-CENSUS ok`).
Every module must already be built (scripts/pre-push builds first).

gates/census.py TREE --changed FILE — THE REACH CENSUS (GATES-20v (c)), the fast judge's: the axiom census and the
statement census over the modules a landing reaches (the changed modules and their importers, gates/decls.py's
`reach`), importing only those. A theorem outside the reach has the parent's statement, axioms and definitions, so
nothing outside it can read differently; an allow row is judged when its declaration is in the reach. The
refine census (whose allow rows and vectors are tree-wide) and an allow row whose declaration is gone run at
convergence (scripts/standing.sh's whole census). A build input (lakefile,
toolchain, manifest) makes the reach the tree.
"""
import os
import subprocess
import sys

import tree

sys.dont_write_bytecode = True   # rows run concurrently and read gates/ (GATES-20s)


def modules(t: tree.Tree) -> tuple[list[str], list[str]]:
    """Every module the census imports, and the libraries it censuses (gates/statement_plants.py reuses them)."""
    roots = set(t.exes.values())  # exe roots hold only `main` (closure C7); two would collide
    mods = sorted(m for m in t.modules if t.modules[m].lib != "Census" and m not in roots)
    return mods, sorted(set(t.modules[m].lib for m in mods))


def reach_main(root: str, changed_file: str) -> int:
    import decls
    t = tree.read(root)
    changed = [l.strip() for l in open(changed_file, encoding="utf-8") if l.strip()]
    mods_all, libs = modules(t)
    if any(p in ("lakefile.lean", "lean-toolchain", "lake-manifest.json") for p in changed):
        mods = mods_all
    else:
        lean = {p[:-5].replace("/", ".") for p in changed if p.endswith(".lean") and p != "lakefile.lean"}
        mods = sorted(decls.reach(t, lean) & set(mods_all))
    if not mods:
        print("census (reach): ok (no module of the census changed)")
        return 0
    gd = os.path.join(t.root, ".lake", "gates")
    os.makedirs(gd, exist_ok=True)
    listing, run = os.path.join(gd, "census-reach.txt"), os.path.join(gd, "CensusReachRun.lean")
    with open(listing, "w", encoding="utf-8") as f:
        f.write("".join(m + "\n" for m in mods))
    with open(run, "w", encoding="utf-8") as f:
        f.write("import Census.Axioms\nimport Census.Statements\n" + "".join(f"import {m}\n" for m in mods))
        f.write(f'#axiom_census_in "gates/axioms-allow.tsv" "{listing}" {" ".join(libs)}\n')
        f.write(f'#statement_census_in ".lake/gates/statements-reach.tsv" "{listing}" {" ".join(libs)}\n')
    r = subprocess.run(["lake", "env", "lean", run], cwd=t.root, capture_output=True, text=True)
    out = (r.stdout + r.stderr).strip()
    print(out)
    ok = r.returncode == 0 and "AXIOM-CENSUS ok" in out and "STATEMENT-CENSUS ok" in out
    print(f"census (reach, {len(mods)} module(s)): {'ok' if ok else 'RED'}")
    return 0 if ok else 1


def main(root: str) -> int:
    t = tree.read(root)
    mods, libs = modules(t)
    if not mods:
        print("census: ok (no modules)")
        return 0
    os.makedirs(os.path.join(t.root, ".lake", "gates"), exist_ok=True)
    run = os.path.join(t.root, ".lake", "gates", "CensusRun.lean")
    with open(run, "w", encoding="utf-8") as f:
        f.write("import Census.Axioms\nimport Census.Refines\nimport Census.Statements\n" + "".join(f"import {m}\n" for m in mods))
        f.write(f'#axiom_census "gates/axioms-allow.tsv" {" ".join(libs)}\n')
        f.write(f'#refine_census "gates/refines-allow.tsv" "gates/codec-vectors.tsv" {" ".join(libs)}\n')
        f.write(f'#statement_census ".lake/gates/statements.tsv" {" ".join(libs)}\n')
    r = subprocess.run(["lake", "env", "lean", run], cwd=t.root, capture_output=True, text=True)
    out = (r.stdout + r.stderr).strip()
    print(out)
    ok = r.returncode == 0 and "AXIOM-CENSUS ok" in out and "REFINE-CENSUS ok" in out and "STATEMENT-CENSUS ok" in out
    print(f"census: {'ok' if ok else 'RED'}")
    return 0 if ok else 1


if __name__ == "__main__":
    if len(sys.argv) == 4 and sys.argv[2] == "--changed":
        sys.exit(reach_main(sys.argv[1], sys.argv[3]))
    sys.exit(main(sys.argv[1] if len(sys.argv) > 1 else "."))
