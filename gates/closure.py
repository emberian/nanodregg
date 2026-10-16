"""gates/closure.py TREE — the module-graph gate. Red on:

  C1 a .lean file outside a declared lib (a lib is `[[lean_lib]] name = X, globs = ["X.+"]`
     and owns exactly the directory X/), or a lib that is not rooted that way;
  C2 an import that is neither a tree module nor Init/Std (Lean only from Census);
  C3 a def-module exporting a theorem, or a proof-module (a `Proofs` path component)
     exporting a definition whose type is not `Prop`; private helpers are allowed on either
     side; statements (a declaration whose result type is Prop: `structure Checked … : Prop`,
     `inductive HasType : … → Prop`, `def P : X → Prop`) live in proof-modules, and a
     def-module exporting one is red;
  C4 a def-module importing a proof-module;
  C5 a module outside Census importing Census;
  C6 a lean_exe root that is a proof-module or not a tree module.
"""
import sys

import tree


def check(t: tree.Tree) -> list[str]:
    red = []
    libs = {}
    for lib in t.lake.get("lean_lib", []):
        name = lib["name"]
        if lib.get("globs") != [f"{name}.+"] or "roots" in lib:
            red.append(f"C1 lib {name}: must be rooted by globs = [\"{name}.+\"] and nothing else")
        libs[name] = lib
    for m in t.modules.values():
        if "." not in m.name:
            red.append(f"C1 {m.path}: a top-level module is an umbrella hub; put it in a layer directory")
        elif m.lib not in libs:
            red.append(f"C1 {m.path}: directory {m.lib}/ is not a declared lean_lib in lakefile.toml")
    for m in t.modules.values():
        for i in m.imports:
            root = i.split(".")[0]
            if i in t.modules:
                target = t.modules[i]
                if not m.is_proof and target.is_proof:
                    red.append(f"C4 {m.name} (def-module) imports proof-module {i}")
                if target.lib == "Census" and m.lib != "Census":
                    red.append(f"C5 {m.name} imports {i}: Census is build tooling, never a dependency")
            elif root in ("Init", "Std"):
                pass
            elif root == "Lean" and m.lib == "Census":
                pass
            else:
                red.append(f"C2 {m.name} imports {i}: not a tree module and not Init/Std")
        for d in m.decls:
            if d.private or d.kind in ("example", "axiom"):
                continue  # example/axiom are refusals.py's
            if m.is_proof and d.kind in tree.DEF_KINDS and not d.is_prop:
                red.append(f"C3 {m.path}:{d.line} proof-module exports {d.kind} {d.name}")
            if not m.is_proof and d.kind in tree.DEF_KINDS and d.is_prop:
                red.append(f"C3 {m.path}:{d.line} def-module exports statement {d.kind} {d.name} (its type is "
                           f"Prop); statements belong in a Proofs module")
            if not m.is_proof and d.kind in tree.THEOREM_KINDS:
                red.append(f"C3 {m.path}:{d.line} def-module exports theorem {d.name}; "
                           f"move it to a Proofs module or make it private")
    for exe, root in t.exes.items():
        if root not in t.modules:
            red.append(f"C6 lean_exe {exe}: root {root} is not a tree module")
        elif t.modules[root].is_proof:
            red.append(f"C6 lean_exe {exe}: root {root} is a proof-module")
    return red


if __name__ == "__main__":
    red = check(tree.read(sys.argv[1] if len(sys.argv) > 1 else "."))
    for r in red:
        print(r)
    print(f"closure: {'RED' if red else 'ok'} ({len(red)})")
    sys.exit(1 if red else 0)
