"""gates/check.py TREE [--base-size F] [--base-waste F] [--message F] [--changed F]
[--base-tree DIR] — every source gate, one line each, exit 1 if any is red. The build and the census are scripts/pre-push's."""
import argparse
import os
import re
import sys

import closure
import owners
import refusals
import size
import tree
import waste

ap = argparse.ArgumentParser()
ap.add_argument("root")
ap.add_argument("--base-size")
ap.add_argument("--base-waste")
ap.add_argument("--base-tree", help="the parent tree: size rises are measured against it, and a\n                closure/refusal red the parent already had is reported as PRE-EXISTING, not red")
ap.add_argument("--message")
ap.add_argument("--changed", help="file listing the paths the commit changes (enables the owners gate)")
a, _unknown = ap.parse_known_args()  # a parent's check.py must accept a child's new flags
t = tree.read(a.root)
msg = open(a.message, encoding="utf-8").read() if a.message else ""


def read(p):
    return open(p, encoding="utf-8").read() if p and os.path.exists(p) else None


changed = open(a.changed, encoding="utf-8").read().split() if a.changed else None
results = {
    "closure": closure.check(t),
    "refusals": refusals.check(t),
    "size": size.check(t, read(os.path.join(t.root, "SIZE.md")) or "", read(a.base_size), msg,
                    tree.read(a.base_tree) if a.base_tree and os.path.exists(os.path.join(a.base_tree, "lakefile.toml")) else None),
    "waste": waste.check(read(os.path.join(t.root, "gates", "waste.tsv")) or "", read(a.base_waste), msg),
}
if changed is not None:
    results["owners"] = owners.check(t.root, changed, msg)
# A commit is refused for the reds it introduces. Reds its parent already had are printed (they
# are some layer's to fix forward, and scripts/standing.sh counts every one) but do not block an
# unrelated commit: otherwise one layer's red stops all six.
old = set()
if a.base_tree and os.path.exists(os.path.join(a.base_tree, "lakefile.toml")):
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
for w in size.WARN:
    print(f"WARN {w}")
sys.exit(1 if red else 0)
