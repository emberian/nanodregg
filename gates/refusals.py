"""gates/refusals.py TREE — constructs that never land. Matched on blanked code (comments and
strings removed), so prose may name them. Red on:

  sorry, admit                      unproved obligations
  #guard #eval #print #check #reduce #guard_msgs #exit
                                    a fact worth asserting is a named theorem (law 6), and the
                                    build is not a REPL
  example                           an unnamed check; name it
  axiom                             no new axioms; the census allows only the standard three
  partial, unsafe                   no partial or unsafe code anywhere (law 4)
  @[implemented_by], @[extern]      an unproved second implementation; allowed only for a module
                                    listed in gates/native-allow.tsv (module<TAB>reason)
  set_option maxHeartbeats / maxRecDepth / synthInstance.*  a slow proof is fixed, not fed
  set_option autoImplicit / relaxedAutoImplicit / warningAsError / linter.*  lakefile's options hold
  List UInt8 in a def-module        bytes are ByteArray (law 3)
  "…\\xHH<hex digit>…"             a string literal Lean v4.30's C backend miscompiles (greedy C \\x)
  createTempFile/createTempDir/withTempFile/withTempDir
                                    segfault under a missing TMPDIR (v4.30); name the path
"""
import os
import re
import sys

import tree

PATTERNS = [
    (r"\bsorry\b", "sorry"),
    # the tactic, not the identifier (`World.admit`, a constructor or field named admit)
    (r"(?:\bby|[;\n(])[ \t]*admit[ \t]*(?=$|\n|;|\)|<;>)", "admit"),
    (r"(?m)^\s*#(guard_msgs|guard|eval|print|check|reduce|exit)\b", "command"),
    (r"(?m)^\s*(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable)\s+)*example\b", "example"),
    (r"(?m)^\s*(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable)\s+)*axiom\b", "axiom"),
    (r"\bpartial\b", "partial"),
    (r"\bunsafe\b", "unsafe"),
    (r"\bset_option\s+(maxHeartbeats|maxRecDepth|synthInstance\.\w+)\b", "set_option budget"),
    (r"\bset_option\s+(autoImplicit|relaxedAutoImplicit|warningAsError|linter\.[\w.]+)\b", "set_option override"),
    # Lean v4.30's temp-file primitives segfault (exit 139, no output) when TMPDIR names a missing
    # directory, instead of raising an IO error: a crash is never a refusal (law 7). Measured
    # 10-17 (OPS D9). A process names its own paths.
    (r"\b(?:createTempFile|createTempDir|withTempFile|withTempDir)\b", "temp file"),
]
NATIVE = re.compile(r"@\[[^\]]*\b(implemented_by|extern)\b")
LIST_BYTES = re.compile(r"\bList\s+UInt8\b")


def native_allow(root: str) -> set[str]:
    path = os.path.join(root, "gates", "native-allow.tsv")
    out = set()
    if os.path.exists(path):
        for line in open(path, encoding="utf-8"):
            if line.strip() and not line.startswith("#"):
                parts = line.rstrip("\n").split("\t")
                if len(parts) < 2 or not parts[1].strip():
                    raise SystemExit(f"native-allow.tsv: row without a reason: {line!r}")
                out.add(parts[0])
    return out


# Lean v4.30.0's C backend emits a String literal's `\xHH` escape into C unchanged, and C's `\x`
# escape is greedy: "a\x00b" compiles to the bytes a, 0x0b (two bytes) while the interpreter and the
# kernel see a, 0x00, b. Measured 10-17 (CODEC-4, CODEC-27 / 23c9530; GATES-2 saw `lean -c` emit the
# C literal "a\x00b"). So a `\xHH` escape directly followed by a hex digit is refused in every
# module (tooling compiles too); write the bytes as a ByteArray, or end the literal (`"\x00" ++ "b"`).
# Lift when a toolchain splits the C literal (re-run the plant in the commit that lifts it).
STRING = re.compile(r'"(?:[^"\\\n]|\\.)*"')
GREEDY_X = re.compile(r"\\(?:(?P<greedy>x[0-9a-fA-F]{2}(?=[0-9a-fA-F]))|.)")


def greedy_hex_escapes(m) -> list[str]:
    red = []
    code = tree.blank(m.text, strings=False)
    for lit in STRING.finditer(code):
        for e in GREEDY_X.finditer(lit.group(0)):
            if e.group("greedy"):
                line = code.count("\n", 0, lit.start()) + 1
                red.append(f"hex escape: {m.path}:{line}: {e.group(0)} followed by a hex digit in {lit.group(0)[:40]} "
                           f"(Lean v4.30.0's C backend compiles it as one greedy C \\x escape)")
    return red


def check(t: tree.Tree) -> list[str]:
    red = []
    allowed = native_allow(t.root)
    for m in t.modules.values():
        for pat, what in PATTERNS:
            for hit in re.finditer(pat, m.code):
                line = m.code.count("\n", 0, hit.start()) + 1
                red.append(f"{what}: {m.path}:{line}: {m.text.splitlines()[line - 1].strip()}")
        red += greedy_hex_escapes(m)
        if m.name not in allowed:
            for hit in NATIVE.finditer(m.code):
                line = m.code.count("\n", 0, hit.start()) + 1
                red.append(f"native: {m.path}:{line}: @[{hit.group(1)}] outside gates/native-allow.tsv")
        if not m.is_proof:
            for hit in LIST_BYTES.finditer(m.code):
                line = m.code.count("\n", 0, hit.start()) + 1
                red.append(f"List UInt8: {m.path}:{line}: def-modules carry bytes as ByteArray")
    for name in allowed - set(t.modules):
        red.append(f"native-allow.tsv: {name} is not a tree module (stale row)")
    return red


if __name__ == "__main__":
    red = check(tree.read(sys.argv[1] if len(sys.argv) > 1 else "."))
    for r in red:
        print(r)
    print(f"refusals: {'RED' if red else 'ok'} ({len(red)})")
    sys.exit(1 if red else 0)
