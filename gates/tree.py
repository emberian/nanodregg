"""The one reader of a nanodregg tree. Every gate reads modules, imports and declarations here.

A tree is a directory holding `lakefile.toml`. Its modules are the `.lean` files below it,
outside `.lake/` and `.git/`. Text is read with comments and string literals blanked (newlines
kept), so a word inside a docstring or a string is never mistaken for code.
"""
from __future__ import annotations

import os
import re
import tomllib
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


def blank(text: str) -> str:
    """Replace comments and string/char literals by spaces, keeping every newline."""
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
        elif c == '"':
            j = i + 1
            while j < n and text[j] != '"':
                j += 2 if text[j] == "\\" else 1
            j = min(j + 1, n)
            out.append(re.sub(r"[^\n]", " ", text[i:j]))
            i = j
        elif c == "'" and (i == 0 or not (text[i - 1].isalnum() or text[i - 1] in "_'.!?")):
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


def read(root: str) -> Tree:
    root = os.path.abspath(root)
    with open(os.path.join(root, "lakefile.toml"), "rb") as f:
        lake = tomllib.load(f)
    modules = {}
    for d, dirs, files in os.walk(root):
        dirs[:] = sorted(x for x in dirs if x not in SKIP_DIRS)
        for f in sorted(files):
            if not f.endswith(".lean"):
                continue
            rel = os.path.relpath(os.path.join(d, f), root)
            name = rel[:-5].replace(os.sep, ".")
            with open(os.path.join(d, f), encoding="utf-8") as fh:
                text = fh.read()
            code = blank(text)
            modules[name] = Module(name, rel, text, code, header_imports(code), decls(code))
    return Tree(root, lake, modules)
