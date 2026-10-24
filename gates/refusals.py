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


# The string literal Lean v4.30.0's C backend miscompiles (a control character before a hex digit, CODEC-4) is
# refused from the COMPILED C, after the build, by gates/cbytes.py (GATES-20y): its source spelling does not decide
# it ("a\u0000b", "\x00" ++ "b" reach the same emitter).


def check(t: tree.Tree) -> list[str]:
    red = []
    allowed = native_allow(t.root)
    for m in t.modules.values():
        for pat, what in PATTERNS:
            for hit in re.finditer(pat, m.code):
                line = m.code.count("\n", 0, hit.start()) + 1
                red.append(f"{what}: {m.path}:{line}: {m.text.splitlines()[line - 1].strip()}")
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
