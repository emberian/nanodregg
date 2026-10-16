"""The one reader of a nanodregg tree. Every gate reads modules, imports and declarations here.

A tree is a directory holding `lakefile.lean`, read here with a strict grammar (see `lakefile`). Its modules are the `.lean` files below it,
outside `.lake/` and `.git/`. Text is read with comments and string literals blanked (newlines
kept), so a word inside a docstring or a string is never mistaken for code.
"""
from __future__ import annotations

import os
import re
from dataclasses import dataclass, field

SKIP_DIRS = {".lake", ".git", "target", "node_modules"}

# Imports from outside the tree that a module may name. `Lean` (the elaborator) is reserved for
# the Census lib; closure.py enforces that.
EXTERNAL_ROOTS = ("Init", "Std", "Lean")

DEF_KINDS = {"def", "abbrev", "structure", "inductive", "class", "instance", "opaque",
             "macro", "macro_rules", "syntax", "elab", "elab_rules", "notation", "infix",
             "infixl", "infixr", "prefix", "postfix", "initialize", "builtin_initialize",
             "declare_syntax_cat", "register_option"}
THEOREM_KINDS = {"theorem", "lemma"}
MODIFIERS = {"private", "protected", "noncomputable", "partial", "unsafe", "nonrec", "public",
             "meta", "scoped", "local"}

_DECL = re.compile(
    r"^[ \t]*((?:@\[[^\]]*\][ \t\n]*)*)((?:(?:" + "|".join(sorted(MODIFIERS)) + r")[ \t]+)*)"
    r"(" + "|".join(sorted(DEF_KINDS | THEOREM_KINDS | {"example", "axiom"}, key=len, reverse=True))
    + r")\b[ \t]*([^\s:({\[]*)",
    re.M)


def blank(text: str, strings: bool = True) -> str:
    """Replace comments (and, unless strings=False, string/char literals) by spaces, keeping
    every newline."""
    out = []
    i, n = 0, len(text)
    while i < n:
        c = text[i]
        if text.startswith("--", i):
            j = text.find("\n", i)
            j = n if j < 0 else j
            out.append(" " * (j - i))
            i = j
        elif text.startswith("/-", i):
            depth, j = 1, i + 2
            while j < n and depth:
                if text.startswith("/-", j):
                    depth, j = depth + 1, j + 2
                elif text.startswith("-/", j):
                    depth, j = depth - 1, j + 2
                else:
                    j += 1
            out.append(re.sub(r"[^\n]", " ", text[i:j]))
            i = j
        elif c == '"' and strings:
            j = i + 1
            while j < n and text[j] != '"':
                j += 2 if text[j] == "\\" else 1
            j = min(j + 1, n)
            out.append(re.sub(r"[^\n]", " ", text[i:j]))
            i = j
        elif c == "'" and strings and (i == 0 or not (text[i - 1].isalnum() or text[i - 1] in "_'.!?")):
            m = re.match(r"'(\\.[^']*|[^'\\])'", text[i:])
            if m:
                out.append(" " * len(m.group(0)))
                i += len(m.group(0))
            else:
                out.append(c)
                i += 1
        else:
            out.append(c)
            i += 1
    return "".join(out)


def header_imports(code: str) -> list[str]:
    """The imports of a blanked module header: `module`/`prelude`, then `[public|meta] import [all] M…`."""
    toks = code.split()
    out, i = [], 0
    while i < len(toks):
        t = toks[i]
        if t in ("module", "prelude"):
            i += 1
        elif t in ("public", "meta", "private") and i + 1 < len(toks) and toks[i + 1] in ("import", "meta"):
            i += 1
        elif t == "import":
            i += 1
            if i < len(toks) and toks[i] == "all":
                i += 1
            # `import A B C` is legal: take names until a keyword-looking token.
            while i < len(toks) and re.fullmatch(r"[A-Z«][\w.«»']*", toks[i]):
                out.append(toks[i])
                i += 1
        else:
            break
    return out


@dataclass
class Decl:
    kind: str
    name: str
    private: bool
    partial: bool
    attrs: str
    line: int
    header: str = ""

    @property
    def is_prop(self) -> bool:
        """A declaration whose result type is `Prop` (a statement: a structure of facts, a typing
        relation `inductive HasType : Ctx → Term → Ty → Prop`, a predicate `def P : X → Prop`)."""
        return re.search(r"(?::|→|->)\s*(?:Prop|Sort\s+0)\s*$", self.header) is not None


@dataclass
class Module:
    name: str
    path: str          # relative to the tree root
    text: str
    code: str          # blanked text
    imports: list[str]
    decls: list[Decl] = field(default_factory=list)

    @property
    def lines(self) -> int:
        return self.text.count("\n") + (0 if self.text.endswith("\n") or not self.text else 1)

    @property
    def lib(self) -> str:
        return self.name.split(".")[0]

    @property
    def is_proof(self) -> bool:
        """A proof-module has a path component named `Proofs` (e.g. `Kernel.Proofs.World`)."""
        return "Proofs" in self.name.split(".")[1:]


@dataclass
class Tree:
    root: str
    lake: dict
    modules: dict[str, Module]

    @property
    def libs(self) -> list[str]:
        return [lib["name"] for lib in self.lake.get("lean_lib", [])]

    @property
    def exes(self) -> dict[str, str]:
        return {e["name"]: e.get("root", e["name"]) for e in self.lake.get("lean_exe", [])}

    def closure(self, roots) -> set[str]:
        seen, stack = set(), list(roots)
        while stack:
            m = stack.pop()
            if m in seen or m not in self.modules:
                continue
            seen.add(m)
            stack.extend(self.modules[m].imports)
        return seen

    def dependents(self) -> dict[str, set[str]]:
        """Every module's transitive importers (what an edit of it rebuilds)."""
        direct: dict[str, set[str]] = {m: set() for m in self.modules}
        for m, mod in self.modules.items():
            for i in mod.imports:
                if i in direct:
                    direct[i].add(m)
        out = {}
        for m in self.modules:
            seen, stack = set(), list(direct[m])
            while stack:
                x = stack.pop()
                if x not in seen:
                    seen.add(x)
                    stack.extend(direct[x])
            out[m] = seen
        return out


def decls(code: str) -> list[Decl]:
    out = []
    for m in _DECL.finditer(code):
        attrs, mods, kind, name = m.group(1), m.group(2).split(), m.group(3), m.group(4)
        line = code.count("\n", 0, m.start(3)) + 1
        end = re.search(r":=|\bwhere\b|\n\s*\||\n\s*\n|\n(?=\S)", code[m.end():])
        header = code[m.end():m.end() + (end.start() if end else 0)].strip()
        out.append(Decl(kind, name, "private" in mods, "partial" in mods, attrs, line, header))
    return out


_LIB = re.compile(r"(?:@\[default_target\]\s+)?lean_lib\s+(\w+)\s+where\s+globs\s*:=\s*#\[\s*\.submodules\s+`(\w+)\s*\]\s*$", re.S)
_EXE = re.compile(r"(?:@\[default_target\]\s+)?lean_exe\s+«([\w-]+)»\s+where\s+root\s*:=\s*`([\w.]+)\s*$", re.S)
_EXTERN = re.compile(r"extern_lib\s+«([\w-]+)»\s+pkg\s*:=\s*do\b(.*)$", re.S)
_PACKAGE = re.compile(r"package\s+nanodregg\s+where\s+leanOptions\s*:=\s*#\[(.*)\]\s*$", re.S)


def lakefile(root: str) -> dict:
    """Read lakefile.lean as a table. Top-level forms (a form starts at column 0): `import Lake`,
    `open Lake DSL System`, the package, `lean_lib X where globs := #[.submodules `X]`,
    `lean_exe «n» where root := `M`, `extern_lib «n» pkg := do …` whose C directory is
    `pkg.dir / "<Lib>" / "c"`. Anything else lands in `errors` (closure C0 is red on it)."""
    lean = os.path.join(root, "lakefile.lean")
    if not os.path.exists(lean):
        # A parent tree from before the switch (2026-10-16): read its lakefile.toml so the
        # transition gate can compare target sets. A candidate without lakefile.lean is C0-red.
        import tomllib
        with open(os.path.join(root, "lakefile.toml"), "rb") as f:
            t = tomllib.load(f)
        return {"lean_lib": [{"name": x["name"], "globs": x.get("globs", [])} for x in t.get("lean_lib", [])],
                "lean_exe": [{"name": x["name"], "root": x.get("root", x["name"])} for x in t.get("lean_exe", [])],
                "extern_lib": [], "errors": ["no lakefile.lean"], "options": ""}
    text = open(lean, encoding="utf-8").read()
    code = blank(text, strings=False)
    forms, cur = [], []
    for line in code.split("\n"):
        if line and not line[0].isspace() and not (cur and cur[-1].strip().startswith("@[")):
            if cur:
                forms.append("\n".join(cur))
            cur = [line]
        elif cur or line.strip():
            cur.append(line)
    if cur:
        forms.append("\n".join(cur))
    out = {"lean_lib": [], "lean_exe": [], "extern_lib": [], "errors": [], "options": ""}
    for f in (x.strip() for x in forms):
        if not f or f in ("import Lake", "open Lake DSL System"):
            continue
        if m := _LIB.match(f):
            if m.group(1) != m.group(2):
                out["errors"].append(f"lean_lib {m.group(1)} globs a different directory {m.group(2)}")
            out["lean_lib"].append({"name": m.group(1), "globs": [f"{m.group(2)}.+"]})
        elif m := _EXE.match(f):
            out["lean_exe"].append({"name": m.group(1), "root": m.group(2)})
        elif m := _EXTERN.match(f):
            dirs = re.findall(r'pkg\.dir\s*/\s*"(\w+)"\s*/\s*"c"', m.group(2))
            if len(dirs) != 1:
                out["errors"].append(f"extern_lib {m.group(1)} must compile exactly one <Lib>/c directory")
            out["extern_lib"].append({"name": m.group(1), "cdirs": [f"{d}/c" for d in dirs]})
        elif m := _PACKAGE.match(f):
            out["options"] = m.group(1)
        else:
            out["errors"].append("unknown top-level form: " + f.splitlines()[0][:100])
    return out


def read(root: str) -> Tree:
    root = os.path.abspath(root)
    lake = lakefile(root)
    modules = {}
    for d, dirs, files in os.walk(root):
        dirs[:] = sorted(x for x in dirs if x not in SKIP_DIRS)
        for f in sorted(files):
            if not f.endswith(".lean"):
                continue
            rel = os.path.relpath(os.path.join(d, f), root)
            if rel == "lakefile.lean":
                continue
            name = rel[:-5].replace(os.sep, ".")
            with open(os.path.join(d, f), encoding="utf-8") as fh:
                text = fh.read()
            code = blank(text)
            modules[name] = Module(name, rel, text, code, header_imports(code), decls(code))
    return Tree(root, lake, modules)


if __name__ == "__main__":
    # `tree.py targets DIR`: every lean_lib and lean_exe name; `tree.py exes DIR`: exe names;
    # `tree.py has-exe DIR NAME`: exit 0 iff NAME is a lean_exe.
    import sys
    cmd, d = sys.argv[1], sys.argv[2]
    lk = lakefile(d)
    if cmd == "targets":
        print(" ".join([x["name"] for x in lk["lean_lib"]] + [x["name"] for x in lk["lean_exe"]]))
    elif cmd == "exes":
        print(" ".join(x["name"] for x in lk["lean_exe"]))
    elif cmd == "has-exe":
        sys.exit(0 if any(x["name"] == sys.argv[3] for x in lk["lean_exe"]) else 1)
    else:
        sys.exit(f"tree.py: unknown command {cmd}")
