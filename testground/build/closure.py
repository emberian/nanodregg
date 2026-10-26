#!/usr/bin/env python3
"""closure.py ROOT TOOLCHAIN_SRC MOD... : the transitive import closure of MODs; `T name` for a tree
module, `L name` for a toolchain one (Init/Std/Lean). Reads each header up to its first command."""
import os, re, sys
root, tsrc, mods = sys.argv[1], sys.argv[2], sys.argv[3:]
def path(m):
    rel = m.replace(".", "/") + ".lean"
    for base in (root, tsrc):
        p = os.path.join(base, rel)
        if os.path.exists(p): return p, base == root
    return None, None
def header(t):
    t = re.sub(r"/-.*?-/", " ", t, flags=re.S)
    t = re.sub(r"--[^\n]*", "", t)
    toks = t.split()
    deps, prelude, i = [], False, 0
    while i < len(toks):
        w = toks[i]
        if w in ("module",): i += 1; continue
        if w == "prelude": prelude = True; i += 1; continue
        if w in ("public", "private", "meta") and i + 1 < len(toks) and toks[i+1] in ("import", "meta", "public"):
            i += 1; continue
        if w == "import":
            i += 1
            if i < len(toks) and toks[i] == "all": i += 1
            deps.append(toks[i]); i += 1; continue
        break
    return deps, prelude
seen, order, stack = {}, [], list(mods)
while stack:
    m = stack.pop()
    if m in seen: continue
    p, tree = path(m)
    if p is None: print("MISSING", m, file=sys.stderr); seen[m] = None; continue
    seen[m] = tree; order.append(m)
    deps, prelude = header(open(p).read())
    if not prelude: deps.append("Init")
    stack += deps
for m in order:
    print(("T " if seen[m] else "L ") + m)
