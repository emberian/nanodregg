#!/usr/bin/env python3
"""gates/decls_plants.py — the plants of the declaration diff (GATES-20t, R-0023), judged by the judge's own code.

  gates/decls_plants.py --synthetic FRESH [--harness-control]     the synthetic plants (the fast judge runs them)
  gates/decls_plants.py --synthetic F1 --lean F2 [--harness-control]   the standing row: both, last line
                                                                  `DECLS PLANTS GREEN`
  gates/decls_plants.py --repo REPO --work DIR --cache DIR [--wrap CMD] [--maps FILE] [--only NAME]...

--lean (GATES-20v′) runs decls.py whole, its own Lean export included, over a two-module Demo package lake builds in
F2: a definition's body edited to `∧ False` with no map line (`undeclared redefinition`, naming the theorems), and
declared; a body equal by unfolding; a matcher changed under the same arms (the matcher is part of the definition);
a definition no statement names (no line); a theorem restated to `True`, undeclared and declared (accepted: the spec
layer's to judge); and, pinned as the KNOWN MISS, a body two levels below the statement (GREEN). About a minute.

--synthetic runs decls.py's own decision code (judge) over hand-made export rows, the Lean export replaced by them:
moved, deleted (declared and not), restated (declared and not), renamed (equal, unequal, undeclared), an unused map
line, an owned constructor, a private declaration moved across modules, and the stale-copy lack over a reverted
definition value, a held one, a non-blank line outside every declaration and a blank one. It needs no build and is a
script row of gates/runs.tsv. The historical plants below need a warm work tree and minutes of builds; they are run
by hand when the judge's declaration code changes, and their whole outputs are kept in the decision.

Each plant is a (parent, candidate tree, message) as scripts/commit would hand it on: the lander's record (base = the
parent's blob, ours = the candidate's), `gates/rebase.py stale --lean-lacks` on the candidate index, then, when stale
passes, the candidate built in DIR (a tree with a .lake; the parent built and exported whole first when its digest is
not in the cache) and `gates/decls.py judge`. Every verdict is read from whole output; nothing is landed.

  H1 P7 (d7989d9 on fe89edf): `escrow_link_bites` moved and re-proved: PASS (it is in no map line)
  H2 E1 (4916f3a on f8d04ac): `runSetup*_spec` restated, declared: PASS without `--reverts d7989d94af13`
  H3 S9 (6c31cab on ac34521): the restatement-heavy step, declared: PASS
  each Hn-: the same with one map line removed: RED naming that declaration
  R1 GATES-20b V1 (a1ca640's launcher/tests/members.rs + one line, on 4916f3a): `stale path` (the text half)
  R2 a stale Ops/Proofs/Units.lean (7790f68^'s copy + one line, on 4916f3a): `writer_keeps_all` absent
  R3 a stale Emit/Rust.lean (0856ca3^'s copy + one line, on 4916f3a): a definition's value reverted
  C0 the known-red control: H2 plus a map line naming nothing: `unused map line`
A plant whose mutation is not in its candidate (the file equal to the parent's, the named text present) FAILS before
its verdict is read (a falsifier that stopped falsifying reads green).
"""
from __future__ import annotations

import argparse
import os
import subprocess
import sys
import tempfile
import time

HERE = os.path.dirname(os.path.abspath(__file__))
# importing decls (and tree) must not write gates/__pycache__: a concurrent row reads gates/ (GATES-20s)
sys.dont_write_bytecode = True
LANE = "-- GATES-20t plant: a lane's line\n"


def git(repo, *a, inp=None, env=None, check=True) -> str:
    r = subprocess.run(["git", "-C", repo, *a], input=inp, capture_output=True, env=env)
    if check and r.returncode != 0:
        raise SystemExit(f"plant: git {' '.join(a)}: {r.stderr.decode(errors='replace')}")
    return r.stdout.decode(errors="replace")


def message_of(repo, rev) -> str:
    """REV's message without the REVERTS blocks a landing appended (a plant re-judges, it never inherits them)."""
    out, skip = [], False
    for line in git(repo, "log", "-1", "--format=%B", rev).splitlines():
        if line.startswith("REVERTS:"):
            skip = True
            continue
        if skip and line.startswith("    "):
            continue
        skip = False
        out.append(line)
    return "\n".join(out).rstrip() + "\n"


class Plant:
    """EXPECT is `GREEN` or the list of refusal strings the verdict must ALL contain (law 7: the name, not an exit).
    REPLACE maps a path to (source rev, transform of its bytes): the candidate is CAND's tree (else the parent's)
    with each such file replaced."""
    def __init__(self, name, parent, cand=None, replace=None, maplines=(), reverts=(), drop=None, expect="GREEN",
                 absent=None, extra=()):
        self.name, self.parent, self.cand, self.replace = name, parent, cand, replace or {}
        self.maplines, self.reverts, self.drop = list(maplines), list(reverts), drop
        self.expect = expect if expect == "GREEN" else ([expect] if isinstance(expect, str) else list(expect))
        self.absent, self.extra = absent, list(extra)


def add_lane(data: bytes) -> bytes:
    return data + LANE.encode()


def drop_link_bites(data: bytes) -> bytes:
    """GATES-20p's planted removal of `escrow_link_bites` from the real P7 file, with its docstring (a docstring
    left before `end` does not parse, and a plant must reach the guard)."""
    start = data.index(b"\n/-- **Tooth for the link")
    end = data.index(b"\nend Nanodregg.Ledger.Proofs", start)
    return data[:start] + data[end:]


def candidate_tree(repo, p: Plant, idx: str) -> str:
    env = dict(os.environ, GIT_INDEX_FILE=idx)
    if p.cand and not p.replace:
        git(repo, "read-tree", p.cand, env=env)
        return git(repo, "rev-parse", f"{p.cand}^{{tree}}").strip()
    git(repo, "read-tree", p.cand or p.parent, env=env)
    for path, (src, transform) in p.replace.items():
        data = transform(subprocess.run(["git", "-C", repo, "show", f"{src}:{path}"], capture_output=True,
                                        check=True).stdout)
        oid = git(repo, "hash-object", "-w", "--stdin", inp=data).strip()
        git(repo, "update-index", "--add", "--cacheinfo", f"100644,{oid},{path}", env=env)
    return git(repo, "write-tree", env=env).strip()


def materialize(repo, tree_oid, d, idx):
    os.makedirs(d, exist_ok=True)
    env = dict(os.environ, GIT_INDEX_FILE=idx)
    subprocess.run(["git", "-C", repo, f"--work-tree={d}", "read-tree", "--reset", "-u", tree_oid], env=env, check=True,
                   capture_output=True)


def run(cmd, cwd=None, env=None, log=None) -> tuple[int, str]:
    t0 = time.monotonic()
    r = subprocess.run(cmd, cwd=cwd, env=env, capture_output=True, text=True)
    out = r.stdout + r.stderr
    if log:
        with open(log, "a", encoding="utf-8") as fh:
            fh.write(f"$ {' '.join(cmd)}\n{out}\n[exit {r.returncode}; {time.monotonic() - t0:.1f} s wall]\n")
    return r.returncode, out


def judge(repo, work, cache, wrap, p: Plant, log) -> tuple[int, str]:
    with tempfile.TemporaryDirectory(prefix=f"decls-plant-{p.name}-", dir=work) as t:
        idx = os.path.join(t, "index")
        cand = candidate_tree(repo, p, idx)
        base = git(repo, "rev-parse", f"{p.parent}^{{tree}}").strip()
        changed = git(repo, "diff", "--name-only", base, cand).split()
        # the mutation must be in the candidate before any verdict is read
        for path in p.replace:
            if git(repo, "rev-parse", f"{cand}:{path}").strip() == git(repo, "rev-parse", f"{p.cand or p.parent}:{path}").strip():
                return 2, f"PLANT {p.name} FAIL: the mutation of {path} is not in the candidate"
        if p.absent:
            path, text = p.absent
            body = git(repo, "show", f"{cand}:{path}")
            if text in body:
                return 2, f"PLANT {p.name} FAIL: {text!r} is still in the candidate's {path}"
        snap = os.path.join(t, "snapshot.tsv")
        with open(snap, "w", encoding="utf-8") as fh:
            for path in changed:
                b = git(repo, "rev-parse", "-q", "--verify", f"{base}:{path}", check=False).strip() or "-"
                o = git(repo, "rev-parse", "-q", "--verify", f"{cand}:{path}", check=False).strip() or "-"
                fh.write(f"{path}\t{b}\t{o}\t100644\n")
        msg = os.path.join(t, "msg")
        lines = [l for l in p.maplines if l != p.drop]
        if p.drop is not None and len(lines) == len(p.maplines):
            return 2, f"PLANT {p.name} FAIL: the map line to drop is not in the map: {p.drop}"
        with open(msg, "w", encoding="utf-8") as fh:
            fh.write((message_of(repo, p.cand) if p.cand else f"gates: plant {p.name}\n") + "\n" +
                     "".join(l + "\n" for l in lines + p.extra))
        lacks = os.path.join(t, "lean-lacks")
        env = dict(os.environ, GIT_INDEX_FILE=idx)
        cmd = ["python3", os.path.join(HERE, "rebase.py"), "stale", "--repo", repo, "--snapshot", snap, "--main",
               p.parent, "--message", msg, "--lean-lacks", lacks]
        for r in p.reverts:
            cmd += ["--reverts", r]
        rc, out = run(cmd, env=env, log=log)
        if rc != 0:
            return rc, out
        if os.path.exists(lacks):
            with open(log, "a", encoding="utf-8") as fh:
                fh.write("lean-lacks:\n" + open(lacks, encoding="utf-8").read())
        tree_dir, base_dir = os.path.join(work, "tree"), os.path.join(t, "base")
        materialize(repo, base, base_dir, os.path.join(t, "base.index"))
        decls = os.path.join(HERE, "decls.py")
        lenv = dict(os.environ)
        tidx = os.path.join(work, "tree.index")
        if run(["python3", decls, "have", "--cache", cache, "--tree", base])[0] != 0:
            materialize(repo, base, tree_dir, tidx)
            libs = run(["python3", decls, "libs", "--root", tree_dir])[1].split()
            rc, out = run(wrap + ["lake", "build", *libs], cwd=tree_dir, env=lenv, log=log)
            if rc != 0:
                return 2, f"PLANT {p.name} FAIL: the parent {p.parent} does not build:\n{out[-3000:]}"
            rc, out = run(wrap + ["python3", decls, "bootstrap", "--root", tree_dir, "--cache", cache, "--tree", base],
                          env=lenv, log=log)
            if rc != 0:
                return 2, f"PLANT {p.name} FAIL: the parent's export failed:\n{out[-3000:]}"
        materialize(repo, cand, tree_dir, tidx)
        libs = run(["python3", decls, "libs", "--root", tree_dir])[1].split()
        rc, out = run(wrap + ["lake", "build", *libs], cwd=tree_dir, env=lenv, log=log)
        if rc != 0:
            return 2, f"PLANT {p.name} FAIL: the candidate does not build (a plant must reach the guard):\n{out[-3000:]}"
        rc, out = run(wrap + ["python3", decls, "judge", "--root", tree_dir, "--base-root", base_dir, "--cache", cache,
                              "--base", base, "--cand", cand, "--changed", _write(t, "changed", changed),
                              "--message", msg, "--lean-lacks", lacks], env=lenv, log=log)
        return rc, out


def _write(d, name, lines) -> str:
    p = os.path.join(d, name)
    with open(p, "w", encoding="utf-8") as fh:
        fh.write("".join(l + "\n" for l in lines))
    return p


def plants(maps: dict[str, list[str]]) -> list[Plant]:
    """Oldest first: the work tree only moves forward, so each candidate builds as a delta."""
    out = []
    for name, parent, cand, drop in (
            ("H4", "832a815^", "832a815", "import_genesis_iff"),     # the 10-20 trio: today's 20p refuses it
            ("H1", "fe89edf", "d7989d9", None),                       # P7: escrow_link_bites moved, no line for it
            ("H3", "ac34521", "6c31cab", "runHoleGuard_cost"),        # S9: the declaration-price fixture
            ("H2", "f8d04ac", "4916f3a", "selectHole_origin")):       # E1: restated, refused by 20p's rule
        ml = maps.get(name, [])
        rv = ["42c261b"] if name == "H1" else []
        out.append(Plant(name, parent, cand=cand, maplines=ml, reverts=rv))
        line = next((l for l in ml if drop and l.endswith("." + drop)), None)
        if drop and line is None and ml:
            raise SystemExit(f"plant: {name}: the map names no {drop}: the negative control has nothing to drop")
        if line:
            out.append(Plant(name + "-", parent, cand=cand, maplines=ml, reverts=rv, drop=line,
                             expect=f"undeclared restatement: {line.split()[-1]}"))
        if name == "H1":
            # R2, pinned (R-0034 (3)): GATES-20p's removal of escrow_link_bites from the real P7 file, on H1: a move's
            # negative control is the deletion
            out.append(Plant("R2", parent, cand=cand, maplines=ml, reverts=rv,
                             replace={"Ledger/Proofs/EscrowWitness.lean": ("d7989d9", drop_link_bites)},
                             absent=("Ledger/Proofs/EscrowWitness.lean", "theorem escrow_link_bites"),
                             expect=["undeclared deletion: Nanodregg.Ledger.Proofs.escrow_link_bites",
                                     "stale declaration: Nanodregg.Ledger.Proofs.escrow_link_bites"]))
        if name == "H2":
            out.append(Plant("C0", parent, cand=cand, maplines=ml, extra=["DELETES: Nanodregg.GatesPlant.nothing"],
                             expect="unused map line: DELETES: Nanodregg.GatesPlant.nothing"))
    out += [
        # R1, pinned: GATES-20b's V1, a1ca640's members.rs plus one lane line, HEAD at main (the text half)
        Plant("R1", "4916f3a", replace={"launcher/tests/members.rs": ("a1ca640", add_lane)},
              expect="stale path: launcher/tests/members.rs"),
        # R3: a definition's value reverted by a stale copy (0856ca3^'s Emit/Rust.lean plus one lane line)
        Plant("R3", "4916f3a", replace={"Emit/Rust.lean": ("0856ca3^", add_lane)},
              absent=("Emit/Rust.lean", '("HINT_BYTES_MAX", Bounds.hintBytesMax)'),
              expect="stale declaration: Nanodregg.Emit.Rust.bounds"),
    ]
    return out

# ---------------------------------------------------------------- the standing synthetic plants (no Lean build)

SYN_LAKE = """import Lake
open Lake DSL System

package nanodregg where
  leanOptions := #[]

@[default_target] lean_lib Demo where
  globs := #[.submodules `Demo]
"""


def syn_row(name, module, kind, l0, l1, shape, consts="", vshape="-", vconsts="-", priv="-", owner="-"):
    text = f'"{shape} {consts}"' if kind in ("theorem", "axiom") else "-"
    return [name, priv, owner, module, kind, str(l0), str(l1), shape, consts, vshape, vconsts, text, "r"]


def synthetic(fresh: str, control: bool) -> int:
    """decls.py's decision logic over hand-made export rows: the Lean export is replaced by the rows, nothing else.
    Every case names the refusal it must read (or GREEN). --harness-control adds a case whose expectation nothing
    meets; the run must then read RED naming harness-control (GATES-15)."""
    import contextlib
    import io
    import shutil
    sys.path.insert(0, HERE)
    import decls
    A, B, CM = "Demo.A", "Demo.B", "Demo.C"
    f = syn_row("Demo.A.f", A, "definition", 3, 5, "S0", "", "V1", "Nat.succ")
    t = syn_row("Demo.B.t", B, "theorem", 3, 4, "X", "Demo.A.f")
    k = syn_row("Demo.C.k", CM, "theorem", 1, 1, "K")
    base = [f, t,
            syn_row("Demo.A.I", A, "inductive", 7, 9, "I"),
            syn_row("Demo.A.I.mk", A, "constructor", 8, 8, "K", owner="Demo.A.I"),
            syn_row("Demo.A.I.casesOn", A, "definition", 7, 9, "Q", "", "W", ""),
            syn_row("_private.Demo.A.0.Demo.h", A, "theorem", 11, 11, "H", priv="Demo.h"), k]
    keep = base[2:6]
    t2 = syn_row("Demo.B.t", B, "theorem", 3, 4, "Y", "Demo.A.f")
    u_eq = syn_row("Demo.B.u", B, "theorem", 3, 4, "X", "Demo.A.f")
    u_other = syn_row("Demo.B.u", B, "theorem", 3, 4, "Z", "Demo.A.f")
    g = syn_row("Demo.A.g", A, "definition", 3, 5, "S0", "", "V1", "Nat.succ")
    AB = "Demo/A.lean\nDemo/B.lean\n"
    ABC = AB + "Demo/C.lean\n"
    cases = [  # name, candidate rows, message map, the lack (path, side, spans), the changed paths, drop C?, want
        ("moved", keep + [f, syn_row("Demo.B.t", B, "theorem", 10, 11, "X", "Demo.A.f")], "", None, AB, 0, "GREEN"),
        ("deleted", keep + [f], "", None, AB, 0, "undeclared deletion: Demo.B.t"),
        ("deleted-declared", keep + [f], "DELETES: Demo.B.t", None, AB, 0, "GREEN"),
        ("restated", keep + [f, t2], "", None, AB, 0, "undeclared restatement: Demo.B.t"),
        ("restated-meaning", keep + [f, t2], "RESTATES-MEANING: Demo.B.t", None, AB, 0, "GREEN"),
        # GATES-20v′: a definition a statement names, its body edited, is named by one line
        ("body-edited", keep + [syn_row("Demo.A.f", A, "definition", 3, 5, "S0", "", "V2", "Nat.succ"), t], "", None,
         AB, 0, "undeclared redefinition: Demo.A.f"),
        ("body-edited-declared", keep + [syn_row("Demo.A.f", A, "definition", 3, 5, "S0", "", "V2", "Nat.succ"), t],
         "RESTATES-MEANING: Demo.A.f", None, AB, 0, "GREEN"),
        ("restates-checked", keep + [f, t2], "RESTATES: Demo.B.t", None, AB, 0, "restate not equal: RESTATES: Demo.B.t"),
        ("restates-unrelated", keep + [f, u_other], "RESTATES: Demo.B.t → Demo.B.u", None, AB, 0,
         "restate not equal: RESTATES: Demo.B.t → Demo.B.u"),
        ("restates-equal", keep + [f, u_eq], "RESTATES: Demo.B.t → Demo.B.u", None, AB, 0, "GREEN"),
        ("meaning-unchanged", keep + [f, t], "RESTATES-MEANING: Demo.B.t", None, AB, 0,
         "unused map line: RESTATES-MEANING: Demo.B.t"),
        ("renamed", keep + [g, syn_row("Demo.B.t", B, "theorem", 3, 4, "X", "Demo.A.g")],
         "RENAMES: Demo.A.f → Demo.A.g", None, AB, 0, "GREEN"),
        ("renamed-undeclared", keep + [g, syn_row("Demo.B.t", B, "theorem", 3, 4, "X", "Demo.A.g")], "", None, AB, 0,
         "undeclared deletion: Demo.A.f"),
        ("rename-unequal", keep + [syn_row("Demo.A.g", A, "definition", 3, 5, "S1", "", "V1", "Nat.succ"),
                                   syn_row("Demo.B.t", B, "theorem", 3, 4, "X", "Demo.A.g")],
         "RENAMES: Demo.A.f → Demo.A.g", None, AB, 0, "rename not equal: RENAMES: Demo.A.f → Demo.A.g"),
        ("unused", keep + [f, t], "DELETES: Demo.B.t", None, AB, 0, "unused map line: DELETES: Demo.B.t"),
        ("owner", [f, t, base[5]], "DELETES: Demo.A.I", None, AB, 0, "GREEN"),
        ("owner-undeclared", [f, t, base[5]], "", None, AB, 0, "undeclared deletion: Demo.A.I "),
        ("private-moved", base[2:5] + [f, t, syn_row("_private.Demo.B.0.Demo.h", B, "theorem", 20, 20, "H",
                                                     priv="Demo.h")], "", None, AB, 0, "GREEN"),
        ("module-deleted", keep + [f, t], "", None, ABC, 1, "undeclared module deletion: Demo.C"),
        ("module-declared", keep + [f, t], "DELETES-MODULE: Demo.C", None, ABC, 1, "GREEN"),
        ("module-unused", keep + [f, t, k], "DELETES-MODULE: Demo.C", None, ABC, 0,
         "unused map line: DELETES-MODULE: Demo.C"),
        ("stale-value", keep + [syn_row("Demo.A.f", A, "definition", 3, 5, "S0", "", "V0", "Nat.succ"), t], "",
         ("Demo/A.lean", "add", "4-4"), AB, 0, "stale declaration: Demo.A.f"),
        ("stale-value-held", keep + [syn_row("Demo.A.f", A, "definition", 13, 15, "S0", "", "V1", "Nat.succ"), t], "",
         ("Demo/A.lean", "add", "4-4"), AB, 0, "GREEN"),
        ("stale-outside", keep + [f, t], "", ("Demo/A.lean", "add", "1-1"), AB, 0, "stale path: Demo/A.lean"),
        ("stale-blank", keep + [f, t], "", ("Demo/A.lean", "add", "2-2"), AB, 0, "GREEN"),
    ]
    if control:
        cases.append(("harness-control", keep + [f], "", None, AB, 0, "GREEN"))
    src = {"Demo/A.lean": "-- a comment outside every declaration\n\n" + "x\n" * 18,
           "Demo/B.lean": "import Demo.A\n" + "y\n" * 20, "Demo/C.lean": "z\n"}

    def tree_dir(d: str, drop_c: bool) -> str:
        os.makedirs(os.path.join(d, "Demo"), exist_ok=True)
        open(os.path.join(d, "lakefile.lean"), "w").write(SYN_LAKE)
        for p, text in src.items():
            if not (drop_c and p == "Demo/C.lean"):
                open(os.path.join(d, p), "w").write(text)
        return d
    base_root = tree_dir(os.path.join(fresh, "base"), False)
    cache = os.path.join(fresh, "cache")
    decls.save_cache(cache, "base", base)
    red = []
    for name, cand_rows, msg, lack, changed, drop_c, want in cases:
        d = os.path.join(fresh, name)
        cand_root = tree_dir(os.path.join(d, "tree"), bool(drop_c))
        for fn, text in (("changed", changed), ("msg", f"gates: plant {name}\n\n{msg}\n"),
                         ("lacks", "\t".join([lack[0], "c0ffee000000", "plant", lack[1], lack[2]]) + "\n" if lack else "")):
            open(os.path.join(d, fn), "w").write(text)
        a = argparse.Namespace(root=cand_root, base_root=base_root, cache=cache, base="base", cand=f"c-{name}",
                               changed=os.path.join(d, "changed"), message=os.path.join(d, "msg"),
                               lean_lacks=os.path.join(d, "lacks"))
        out = io.StringIO()
        with contextlib.redirect_stdout(out):
            rc = decls.judge(a, lean=lambda root, modules, _r=cand_rows: [list(x) for x in _r if x[3] in modules])
        got = out.getvalue()
        ok = rc == 0 if want == "GREEN" else (rc == 1 and want in got)
        print(f"  {name}: {'ok' if ok else 'FAIL'} (exit {rc}; want {want})")
        if not ok:
            red.append(name)
            print("\n".join("    " + l for l in got.strip().splitlines()[:12]))
        shutil.rmtree(d, ignore_errors=True)
    print(f"decls-synthetic: {'GREEN' if not red else 'RED (' + str(len(red)) + '): ' + ' '.join(red)}")
    return 1 if red else 0

# ---------------------------------------------------------------- the standing Lean plants (GATES-20v)

LEAN_A = """namespace Demo.A
def Lim : Nat := 10
def MovesThrough (n : Nat) : Prop := n ≤ Lim
def Cap : Nat := 10
def Spare : Nat := 1
def Kind : Nat → Prop
  | 0 => True
  | _ => False
end Demo.A
"""
LEAN_B = """import Demo.A
namespace Demo.B
open Demo.A
theorem cap (n : Nat) (h : MovesThrough n) (h2 : 0 < n) : n ≤ Cap := h
theorem two (n : Nat) (h : MovesThrough n) : n ≤ 10 := h
theorem kind_ok (n : Nat) (h : Kind n) : Kind n := h
end Demo.B
"""


def lean_cases() -> list[tuple[str, dict[str, str], str, list[str] | str]]:
    """(name, the candidate's edits as (old, new) text replacements per file, the map, what the verdict must name)."""
    false_body = {"Demo/A.lean": [("n ≤ Lim\n", "n ≤ Lim ∧ False\n")],
                  "Demo/B.lean": [("n ≤ Cap := h\n", "n ≤ Cap := h.1\n"), ("n ≤ 10 := h\n", "n ≤ 10 := h.1\n")]}
    true_cap = {"Demo/B.lean": [("theorem cap (n : Nat) (h : MovesThrough n) (h2 : 0 < n) : n ≤ Cap := h\n",
                                 "theorem cap : True := trivial\n")]}
    return [
        # A2's plant: the body edit reds by name with no map line, naming the theorems it moved
        ("body-false", false_body, "", ["undeclared redefinition: Demo.A.MovesThrough", "Demo.B.cap", "Demo.B.two"]),
        ("body-false-declared", false_body, "RESTATES-MEANING: Demo.A.MovesThrough", "GREEN"),
        # a body equal by unfolding is still an edit of the body
        ("refactor", {"Demo/A.lean": [("def Cap : Nat := 10", "def Cap : Nat := 5 + 5")]}, "",
         ["undeclared redefinition: Demo.A.Cap"]),
        # the matcher is part of the definition: the same arms over another pattern is a redefinition
        ("matcher", {"Demo/A.lean": [("  | 0 => True\n", "  | 1 => True\n")]}, "",
         ["undeclared redefinition: Demo.A.Kind"]),
        # a definition no statement names needs no line
        ("unnamed-definition", {"Demo/A.lean": [("def Spare : Nat := 1", "def Spare : Nat := 2")]}, "", "GREEN"),
        ("to-true-undeclared", true_cap, "", ["undeclared restatement: Demo.B.cap"]),
        # a declared restatement is accepted on its line: whether it still says what it said is the spec layer's
        # (GATES-20v′), pinned here so the boundary is findable
        ("to-true-declared", true_cap, "RESTATES-MEANING: Demo.B.cap", "GREEN"),
        # KNOWN MISS, pinned so it is findable: a body two levels below the statement (Lim, under MovesThrough)
        ("two-levels-known-miss", {"Demo/A.lean": [("def Lim : Nat := 10", "def Lim : Nat := 9")],
                                   "Demo/B.lean": [("n ≤ 10 := h\n", "n ≤ 10 := Nat.le_succ_of_le h\n"),
                                                   ("n ≤ Cap := h\n", "n ≤ Cap := Nat.le_succ_of_le h\n")]},
         "", "GREEN"),
    ]


def lean_plants(fresh: str, control: bool) -> int:
    """decls.py judge, whole (the judge's own Lean: export, read-back, transplant, strength check), over a two-module
    Demo package built by lake: base, then each case's candidate. Every case names what its verdict must read, and
    its edit is checked to be in the candidate before the verdict is read. --harness-control adds a case whose
    expectation nothing meets: the run must read RED naming harness-control."""
    import contextlib
    import io
    import shutil
    sys.path.insert(0, HERE)
    import decls
    cases = lean_cases()
    if control:
        # refactor's edit, expected GREEN: nothing meets it
        cases.append(("harness-control", next(e for n, e, _, _ in cases if n == "refactor"), "", "GREEN"))
    toolchain = open(os.path.join(HERE, "..", "lean-toolchain")).read()

    def write_tree(d: str, files: dict[str, str]) -> None:
        os.makedirs(os.path.join(d, "Demo"), exist_ok=True)
        for p, text in {"lakefile.lean": SYN_LAKE, "lean-toolchain": toolchain, **files}.items():
            with open(os.path.join(d, p), "w", encoding="utf-8") as fh:
                fh.write(text)

    def build(d: str) -> None:
        r = subprocess.run(["lake", "build"], cwd=d, capture_output=True, text=True)
        if r.returncode != 0:
            raise SystemExit(f"decls-lean: NO VERDICT — a plant tree does not build ({d}):\n{(r.stdout + r.stderr)[-2000:]}")

    t0 = time.monotonic()
    # lake writes absolute LEAN_PATH entries, and a `:` splits one: the judge's {fresh} is
    # `.lake/runs/script:gates/decls_plants.py-N` (GATES-20s's hazard), so the packages live in a temporary directory
    # of their own, removed after
    work = tempfile.mkdtemp(prefix="nanodregg-decls-lean-")
    if ":" in work:
        raise SystemExit(f"decls-lean: NO VERDICT — the temporary directory {work} holds ':' (LEAN_PATH would split)")
    try:
        return _lean_plants(work, cases, decls, toolchain, write_tree, build, t0)
    finally:
        shutil.rmtree(work, ignore_errors=True)


def _lean_plants(fresh, cases, decls, toolchain, write_tree, build, t0) -> int:
    import contextlib
    import io
    import shutil
    base_root, cand_root = os.path.join(fresh, "base"), os.path.join(fresh, "cand")
    base_files = {"Demo/A.lean": LEAN_A, "Demo/B.lean": LEAN_B}
    write_tree(base_root, base_files)
    build(base_root)
    cache = os.path.join(fresh, "cache")
    decls.save_cache(cache, "base", decls.run_export(base_root, ["Demo.A", "Demo.B"]))
    shutil.copytree(base_root, cand_root, ignore=shutil.ignore_patterns(".lake"))
    red = []
    for name, edits, msg, want in cases:
        files = dict(base_files)
        for path, reps in edits.items():
            for old, new in reps:
                if files[path].count(old) != 1:
                    raise SystemExit(f"decls-lean: plant {name}: the site {old!r} does not occur once in {path}")
                files[path] = files[path].replace(old, new)
        assert files != base_files, name      # the mutation is in the candidate before any verdict is read
        write_tree(cand_root, files)
        build(cand_root)
        d = os.path.join(fresh, "case-" + name)
        os.makedirs(d, exist_ok=True)
        for fn, text in (("changed", "".join(p + "\n" for p in edits)), ("msg", f"gates: plant {name}\n\n{msg}\n")):
            open(os.path.join(d, fn), "w").write(text)
        a = argparse.Namespace(root=cand_root, base_root=base_root, cache=cache, base="base", cand=f"c-{name}",
                               changed=os.path.join(d, "changed"), message=os.path.join(d, "msg"), lean_lacks=None)
        out = io.StringIO()
        with contextlib.redirect_stdout(out):
            rc = decls.judge(a)
        got = out.getvalue()
        ok = rc == 0 if want == "GREEN" else (rc == 1 and all(w in got for w in want))
        print(f"  {name}: {'ok' if ok else 'FAIL'} (exit {rc}; want {want})")
        if not ok:
            red.append(name)
        if not ok or os.environ.get("DECLS_PLANTS_VERBOSE"):
            print("\n".join("    " + l for l in got.strip().splitlines()[:16]))
    print(f"decls-lean: {'GREEN' if not red else 'RED (' + str(len(red)) + '): ' + ' '.join(red)} "
          f"({len(cases)} cases, {time.monotonic() - t0:.0f} s)")
    return 1 if red else 0


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--synthetic", metavar="FRESH", help="the standing plants: decls.py's logic over hand-made rows")
    ap.add_argument("--lean", metavar="FRESH", help="the standing plants: decls.py whole over a built Demo package")
    ap.add_argument("--harness-control", action="store_true")
    ap.add_argument("--repo")
    ap.add_argument("--work")
    ap.add_argument("--cache")
    ap.add_argument("--wrap", default="")
    ap.add_argument("--maps", help="a file of `PLANT<TAB>map line` rows: each historical landing's declared map")
    ap.add_argument("--only", action="append", default=[])
    a = ap.parse_args()
    if a.synthetic or a.lean:
        rc = synthetic(a.synthetic, a.harness_control) if a.synthetic else 0
        if a.lean:
            rc |= lean_plants(a.lean, a.harness_control)
            # the row's last line (both sets ran): runs.py reads it exactly
            print(f"DECLS PLANTS {'GREEN' if rc == 0 else 'RED'}")
        return rc
    if not (a.repo and a.work and a.cache):
        ap.error("--repo, --work and --cache name the historical plants' clone, work tree and cache")
    a.work, a.cache = os.path.abspath(a.work), os.path.abspath(a.cache)
    maps: dict[str, list[str]] = {}
    if a.maps:
        for line in open(a.maps, encoding="utf-8"):
            if "\t" in line:
                k, v = line.rstrip("\n").split("\t", 1)
                maps.setdefault(k, []).append(v)
    wrap = a.wrap.split() if a.wrap else []
    log = os.path.join(a.work, "plants.log")
    bad = 0
    for p in plants(maps):
        if a.only and p.name not in a.only:
            continue
        rc, out = judge(a.repo, a.work, a.cache, wrap, p, log)
        with open(log, "a", encoding="utf-8") as fh:
            fh.write(f"=== {p.name}: exit {rc}\n{out}\n")
        if rc == 2 and out.startswith("PLANT"):
            print(out.splitlines()[0]); bad += 1
        elif p.expect == "GREEN":
            if rc == 0:
                print(f"PLANT {p.name} GREEN ({out.strip().splitlines()[-1][:160]})")
            else:
                print(f"PLANT {p.name} FAIL: must pass, exit {rc}:")
                print("\n".join("    " + l for l in out.strip().splitlines()[:40])); bad += 1
        elif rc == 1 and all(e in out for e in p.expect):
            for e in p.expect:
                hit = next(l for l in out.splitlines() if e in l)
                print(f"PLANT {p.name} RED: {hit.strip()[:200]}")
        else:
            print(f"PLANT {p.name} FAIL: exit {rc} without all of {p.expect!r}:")
            print("\n".join("    " + l for l in out.strip().splitlines()[:40])); bad += 1
    print(f"decls plants: {'GREEN' if not bad else f'RED ({bad})'}")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
