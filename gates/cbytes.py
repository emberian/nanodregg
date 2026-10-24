#!/usr/bin/env python3
"""gates/cbytes.py — the string literals the C backend compiles wrongly, read from the COMPILED bytes (GATES-20y).

  gates/cbytes.py scan TREE [--changed FILE]     the emitted C of every module of TREE (of its reach, with --changed)
  gates/cbytes.py vectors FRESH [--harness-control]   the standing row: which literal classes the toolchain breaks

THE DEFECT (CODEC-4, measured 10-17; Lean v4.30.0, Lean/Compiler/LCNF/EmitC.lean `quoteString`): the C emitter
writes a character <= 31 other than \\n \\r \\t as `\\xHH`, and C's `\\x` escape is GREEDY, so when the next character is
a hex digit the two fuse: "a\\u0000b" runs as the bytes [97, 11] compiled and [97, 0, 98] interpreted. The SOURCE
spelling does not decide it: `"\\x00b"`, `"a\\u0000b"`, `"\\x00" ++ "b"` (which the compiler folds into one literal)
and a literal any elaboration produces all reach the same emitter. So this gate reads what the emitter wrote.

SCAN. Every `.c` the build emitted for a module of the tree (`.lake/build/ir/<module path>.c`), each C string literal
parsed escape by escape: a `\\x` escape followed by a hex digit is RED, naming the module, the C line and the literal.
A module with no `.c` (not built) is RED in scan of the whole tree, skipped with --changed only when outside the
reach. It runs after the build (scripts/pre-push, both modes).

VECTORS. A scratch package whose exe prints the UTF-8 bytes of one literal per class the emitter distinguishes
(printable; \\n \\r \\t \\\\ \\" ? escapes; a control character before a non-hex and before a hex digit, spelled
`\\x01`, `\\u0000`, and as a fold `"\\x00" ++ "b"`; DEL; two- and four-byte UTF-8 before a hex digit; a literal
backslash before `x41`). The compiled exe's bytes are compared with the interpreter's (`lake env lean --run` of the
same file). The classes that disagree must be EXACTLY the ones SCAN refuses (BROKEN below), and SCAN over the
package's own C must name exactly those literals: a toolchain that fixes the class, or breaks another, reds this row
by name (re-derive BROKEN and the scan with it). --harness-control expects one more broken class than there is.
Last line: `CBYTES VECTORS GREEN`.
"""
from __future__ import annotations

import os
import re
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.dont_write_bytecode = True     # rows run concurrently and read gates/ (GATES-20s)
sys.path.insert(0, HERE)
import tree  # noqa: E402

C_STRING = re.compile(r'"(?:[^"\\\n]|\\.)*"')
C_ESCAPE = re.compile(r"\\(?:(?P<greedy>x[0-9a-fA-F]{2}(?=[0-9a-fA-F]))|x[0-9a-fA-F]{2}|.)")


def greedy(c_text: str) -> list[tuple[int, str]]:
    """(C line, literal) of every C string literal holding a `\\x` escape directly followed by a hex digit. Comments are
    not literals: the emitter writes none holding a quote, and a `//` or `/*` inside a literal is inside it."""
    out = []
    for lit in C_STRING.finditer(c_text):
        if any(e.group("greedy") for e in C_ESCAPE.finditer(lit.group(0))):
            out.append((c_text.count("\n", 0, lit.start()) + 1, lit.group(0)))
    return out


def scan(root: str, changed: str | None) -> int:
    import decls
    t = tree.read(root)
    mods = set(t.modules)
    if changed:
        ch = [l.strip() for l in open(changed, encoding="utf-8") if l.strip()]
        if not any(p in ("lakefile.lean", "lean-toolchain", "lake-manifest.json") for p in ch):
            mods = decls.reach(t, {p[:-5].replace("/", ".") for p in ch if p.endswith(".lean") and p != "lakefile.lean"})
    red = []
    for m in sorted(mods):
        c = os.path.join(t.root, ".lake", "build", "ir", *m.split(".")) + ".c"
        if not os.path.exists(c):
            red.append(f"cbytes: {m}: no emitted C ({os.path.relpath(c, t.root)}): the module is not built")
            continue
        for line, lit in greedy(open(c, encoding="utf-8", errors="replace").read()):
            red.append(f"cbytes: {m}: {os.path.relpath(c, t.root)}:{line}: {lit[:60]} holds a \\x escape followed by a "
                       f"hex digit, which C reads as one escape (Lean v4.30.0's emitter, GATES-20y): write the bytes as a "
                       f"ByteArray")
    for r in red:
        print(r)
    print(f"cbytes: {'RED' if red else 'ok'} ({len(mods)} module(s) scanned, {len(red)} refused)")
    return 1 if red else 0


# (class, the literal as Lean source, whether the toolchain is known to break it: BROKEN)
VECTORS = [
    ("printable", r'"ab09"', False),
    ("newline-digit", r'"a\n1"', False),
    ("return-hex", r'"a\rb"', False),
    ("tab-hex", r'"a\tb"', False),
    ("backslash-x41", r'"\\x41"', False),
    ("quote-question", r'"\"?b"', False),
    ("ctrl-nonhex", r'"\x01g"', False),
    ("ctrl-hex", r'"\x01b"', True),
    ("nul-hex-unicode", r'"a\u0000b"', True),
    ("nul-hex-fold", r'"\x00" ++ "b"', True),
    ("ctrl-end", r'"b\x1f"', False),
    ("del-hex", r'"\x7fb"', False),
    ("utf8-2-hex", r'"é1"', False),
    ("utf8-4-hex", r'"😀a"', False),
]


def vectors(fresh: str, control: bool) -> int:
    """FRESH is the judge's: `.lake/runs/script:gates/cbytes.py-N` holds a `:`, which splits lake's LEAN_PATH, so the
    package is built in a temporary directory of its own, removed after."""
    import shutil
    import tempfile
    work = tempfile.mkdtemp(prefix="nanodregg-cbytes-")
    if ":" in work:
        print(f"CBYTES VECTORS RED: the temporary directory {work} holds ':' (LEAN_PATH would split)")
        return 1
    try:
        return _vectors(work, control)
    finally:
        shutil.rmtree(work, ignore_errors=True)


def _vectors(fresh: str, control: bool) -> int:
    toolchain = open(os.path.join(HERE, "..", "lean-toolchain"), encoding="utf-8").read()
    os.makedirs(os.path.join(fresh, "CBytes"), exist_ok=True)
    src = ["namespace CBytes", "", "/-- One literal per class the C emitter distinguishes (gates/cbytes.py). -/",
           "def literals : List (String × String) := ["]
    src += [f'  ("{n}", {lit}){"," if i < len(VECTORS) - 1 else "]"}' for i, (n, lit, _) in enumerate(VECTORS)]
    src += ["", "def run : IO Unit := do", "  for (n, s) in literals do", '    IO.println s!"{n} {s.toUTF8.toList}"', "",
            "end CBytes", "", "def main : IO Unit := CBytes.run", ""]
    files = {
        "lakefile.lean": "import Lake\nopen Lake DSL\n\npackage cbytes\n\nlean_exe cbytes where\n  root := `CBytes.Main\n",
        "lean-toolchain": toolchain,
        "CBytes/Main.lean": "\n".join(src),
    }
    for p, text in files.items():
        with open(os.path.join(fresh, p), "w", encoding="utf-8") as fh:
            fh.write(text)
    b = subprocess.run(["lake", "build", "cbytes"], cwd=fresh, capture_output=True, text=True)
    if b.returncode != 0:
        print((b.stdout + b.stderr)[-2000:])
        print("CBYTES VECTORS RED: the vector exe does not build")
        return 1
    comp = subprocess.run([os.path.join(fresh, ".lake", "build", "bin", "cbytes")], capture_output=True, text=True)
    interp = subprocess.run(["lake", "env", "lean", "--run", "CBytes/Main.lean"], cwd=fresh, capture_output=True,
                            text=True)
    if comp.returncode != 0 or interp.returncode != 0:
        print(comp.stderr[-1000:], interp.stderr[-1000:])
        print("CBYTES VECTORS RED: a run failed")
        return 1
    cl = dict(l.split(" ", 1) for l in comp.stdout.splitlines() if " " in l)
    il = dict(l.split(" ", 1) for l in interp.stdout.splitlines() if " " in l)
    red = []
    if set(cl) != {n for n, _, _ in VECTORS} or set(il) != set(cl):
        red.append(f"the runs printed {sorted(set(cl) ^ {n for n, _, _ in VECTORS})} unexpectedly")
    broken = {n for n, _, b in VECTORS if b} | ({"printable"} if control else set())
    for n, lit, _ in VECTORS:
        same = cl.get(n) == il.get(n)
        print(f"  {n:16} {lit:16} compiled {cl.get(n)} interpreted {il.get(n)} {'agree' if same else 'DISAGREE'}")
        if same == (n in broken):
            red.append(f"{n}: compiled and interpreted {'agree' if same else 'disagree'}, the gate says it is "
                       f"{'broken' if n in broken else 'sound'}{' (harness-control)' if n == 'printable' and control else ''}")
    # the scan must refuse exactly the broken literals, by their C
    c = os.path.join(fresh, ".lake", "build", "ir", "CBytes", "Main.c")
    hits = greedy(open(c, encoding="utf-8", errors="replace").read()) if os.path.exists(c) else []
    if len(hits) != sum(1 for _, _, b in VECTORS if b):
        red.append(f"scan: the emitted C holds {len(hits)} refused literal(s), the broken classes are "
                   f"{sum(1 for _, _, b in VECTORS if b)}: {[h[1] for h in hits]}")
    for r in red:
        print("CBYTES VECTORS RED: " + r)
    if not red:
        print(f"  scan of the vector's own C refuses {len(hits)} literal(s): {', '.join(h[1] for h in hits)}")
        print("CBYTES VECTORS GREEN")
    return 1 if red else 0


def main() -> int:
    a = sys.argv[1:]
    if len(a) >= 2 and a[0] == "scan":
        return scan(a[1], a[a.index("--changed") + 1] if "--changed" in a else None)
    if len(a) >= 2 and a[0] == "vectors":
        return vectors(os.path.abspath(a[1]), "--harness-control" in a)
    print(__doc__)
    return 2


if __name__ == "__main__":
    sys.exit(main())
