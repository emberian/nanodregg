"""gates/check.py TREE [--base-waste F] [--message F] [--changed F] [--base-tree DIR] — the source checks, one line
each, exit 1 if any is red. A REPORT: scripts/standing.sh (the convergence) prints it; no landing is refused by it
(WORK-RULES 10-27). What it reads: the import closure rules, the refusal names, the 1 MB file law, case collisions and
conflict markers, the runs table's classification, the TCB table, the codec vectors, the waste ceilings."""
import argparse
import os
import re
import sys

import closure
import refusals
import runs
import size_limit
import tcb
import tree
import vectors
import waste

ap = argparse.ArgumentParser()
ap.add_argument("root")
ap.add_argument("--base-waste")
ap.add_argument("--base-tree", help="the parent tree: size rises are measured against it, and a\n                closure/refusal red the parent already had is reported as PRE-EXISTING, not red")
ap.add_argument("--message")
ap.add_argument("--changed", help="file listing the paths the commit changes (accepted; unused)")
a, _unknown = ap.parse_known_args()  # a parent's check.py must accept a child's new flags
t = tree.read(a.root)
msg = open(a.message, encoding="utf-8").read() if a.message else ""


def has_lakefile(d):
    return any(os.path.exists(os.path.join(d, f)) for f in ("lakefile.lean", "lakefile.toml"))


def read(p):
    return open(p, encoding="utf-8").read() if p and os.path.exists(p) else None




MARKER = re.compile(r"^(<{7}|>{7})(?: |$)")


def conflict_markers(root: str) -> list[str]:
    """A merge-conflict marker line (`<<<<<<< ours`, `>>>>>>> theirs`) in any file of the judged
    tree: an unresolved merge that a lane's own `git apply --3way` or `checkout -m` left in a file it
    then committed whole (4c327a7, 10-17, two decisions appended to decisions/host.md). The `=======`
    middle line is not matched: it is also a Markdown heading underline."""
    red = []
    for d, dirs, files in os.walk(root):
        dirs[:] = [x for x in dirs if x not in tree.SKIP_DIRS]
        for f in files:
            path = os.path.join(d, f)
            try:
                with open(path, encoding="utf-8") as fh:
                    for n, line in enumerate(fh, 1):
                        if MARKER.match(line):
                            red.append(f"{os.path.relpath(path, root)}:{n}: conflict marker {line.rstrip()[:40]!r}")
            except (UnicodeDecodeError, OSError):
                continue  # not text
    return red


def case_collisions(root: str) -> list[str]:
    """Two paths (files or directories) that differ only in case are ONE path on a case-insensitive
    disk (the Mac reader's APFS): `ops/RUNBOOK.md` silently became `Ops/RUNBOOK.md` inside the
    Lean library on 10-17 (OPS). Red by name."""
    seen: dict[str, set[str]] = {}
    for d, dirs, files in os.walk(root):
        dirs[:] = [x for x in dirs if x not in tree.SKIP_DIRS]
        rel = os.path.relpath(d, root)
        for x in dirs + files:
            path = os.path.normpath(os.path.join(rel, x))
            seen.setdefault(path.lower(), set()).add(path)
    return [f"{' and '.join(sorted(v))} differ only in case: one path on a case-insensitive disk"
            for v in seen.values() if len(v) > 1]


results = {
    "closure": closure.check(t),
    "refusals": refusals.check(t),
    "size_limit": size_limit.check(t.root),
    "paths": case_collisions(t.root) + conflict_markers(t.root),
    "runs": runs.check(t),
    "tcb": tcb.check(t.root),
    "vectors": vectors.check(t.root, a.base_tree if a.base_tree and has_lakefile(a.base_tree) else None),
    "waste": waste.check(read(os.path.join(t.root, "gates", "waste.tsv")) or "", read(a.base_waste), msg),
}
# Reds the parent already had are printed PRE-EXISTING: the report names what this commit added.
old = set()
if a.base_tree and has_lakefile(a.base_tree):
    bt = tree.read(a.base_tree)
    old = {re.sub(r":\d+", ":", r) for r in closure.check(bt) + refusals.check(bt)}
red = False
for gate, reds in results.items():
    new = []
    for r in reds:
        if gate in ("closure", "refusals") and re.sub(r":\d+", ":", r) in old:
            print(f"  {gate}: PRE-EXISTING {r}")
        else:
            print(f"  {gate}: {r}")
            new.append(r)
    print(f"{gate}: {'RED' if new else 'ok'}")
    red |= bool(new)
sys.exit(1 if red else 0)
