"""gates/decls.py — the declaration diff of a landing, from the census environment (GATES-20t, R-0023).

  decls.py judge --root CAND --base-root BASE --cache DIR --base OID --cand OID --changed FILE --message FILE
                 [--lean-lacks FILE]                 exit 0 ok, 1 RED, 4 the parent's digest is not cached
  decls.py bootstrap --root TREE --cache DIR --tree OID     export a BUILT tree whole into the cache
  decls.py have --cache DIR --tree OID                      exit 0 when OID's digest is cached
  decls.py export --root TREE --out FILE [--modules FILE]   the raw export (every module by default)
  decls.py libs --root TREE                                 the lean_lib names (what a whole export imports)

THE EXPORT. `#decl_export` (LEAN below: the JUDGE's Lean, interpreted, written after the imports into
.lake/gates/DeclRun.lean exactly as census.py writes CensusRun) writes one row per constant of a named module that
HAS A DECLARATION RANGE: the elaborator's own record that the source declared it (`.eq_1`, `match_`, `_proof_`,
`_simp_` have none), and one row (`a`) per rangeless non-theorem constant a declared definition's value reaches under
that definition's name (its `match_`, `_unary`: they are part of the definition; `splitter`, `sizeOf` and the like,
which no value reads, are not exported). Columns: name, its user name when private (else -), its owner (a
constructor's or recursor's inductive, a projection's structure; else -), module, kind, first and last source line,
the statement's serialization and the constants it names, the value's (a non-theorem's; a proof is irrelevant: -), a
theorem's statement as text (for the diff a refusal prints), `r`/`a`. Module docs are rows of
kind `doc`. The serialization is the term's post-order DAG hash-consed on the emitted token (sharing is canonical,
binder NAMES are erased, binder INFO kept, metadata transparent, a string literal hex) with constants abstracted to
indices into a first-visit list. Digests are SHA-256 over it, taken here. No hash is equality inside Lean.

THE CACHE. A tree's export, raw, per (tree, exporter): `DIR/<tree>-<exporter>.tsv.gz` (about 7.5 MB; the newest 32
kept): the body digest reads a definition's parts by name. A landing exports only its REACH (the changed modules and
their importers, in either tree, plus the importers of a deleted module): a module outside both reaches has the same
source and the same imports in both trees, so the same declarations. The candidate's export is the parent's rows
outside the reach plus its own export of it, cached under the candidate's tree, which is main's tree once it lands. A
miss (exit 4) is bootstrapped by scripts/pre-push: the parent built in the slot and exported whole.

CHECK 1, THE DIFF (R-0034's conditions). Every declaration of the parent absent from the candidate, every theorem (or
axiom) of the parent whose elaborated statement differs, and every DEFINITION whose body differs while a theorem
statement of the reach names it (GATES-20v′), is named by a line of the landing's message:
  RENAMES: OLD → NEW             NEW is OLD renamed: its statement (a definition: and body) must equal OLD's under the
                                 map (checked)
  RESTATES: OLD → NEW            the same check (`restate not equal`); OLD may be NEW (then it must have changed
                                 nothing but its proof, and the line is unused)
  RESTATES-MEANING: OLD [→ NEW]  a deliberate change of meaning: the statement (a definition: the body) may differ
                                 (and must)
  DELETES: NAME                  NAME removed
  DELETES-MODULE: MODULE         MODULE removed, with every declaration in it (one line; no free pass)
A theorem whose statement differs without a line is `undeclared restatement`, printed with the diff of the two
statements (the kernel printer's text; the digest, never the text, decides). A definition whose body moved under a
statement that names it is `undeclared redefinition: D … the statements of T… name it`: `MovesThrough := … ∧ False`
changed no statement and moved every theorem over it (GATES-20u's P3). A definition's BODY is its statement and value
with its parts: the rangeless constants its value reaches under its name (`match_`, `_unary`) and its `where`
helpers, so a matcher's patterns are part of it; a hygienic name is read without its macro scope. One line per edited
definition, not per theorem. A declared change of meaning is accepted on its line: whether a restated statement still
says what it said is the spec layer's (the pins of the top-level statements), not this diff's (GATES-20v′).
A line covers the declarations its declaration OWNS (constructors, recursor, projections, `casesOn`/`noConfusion`,
`where` helpers, a `native_decide` axiom). A two-name line renames OLD inside every candidate statement (inverted:
NEW → OLD, by the longest component-wise prefix, so generated children follow their owner) before the compare, so the
cached parent digest never depends on a map; a renamed definition's body is still compared. A private declaration
whose user name is unique among the private declarations of both trees is matched by that name across a module
move. A line that applies to nothing is `unused map line`.

CHECK 2, THE STALE COPY. gates/rebase.py `stale` still detects, by text, that a `.lean` copy lacks a window commit
C's change (GATES-20b/20b′); it no longer refuses it but writes the lack (--lean-lacks: path, C, side, the lines in
main's copy for a block C added, in the candidate's for a block C removed). Here the lines are mapped to the
declarations whose recorded ranges hold them (main's environment for an added block, the candidate's for a removed
one). An added block is explained when each declaration holding it is in the candidate as main has it (theorem:
the same statement, the proof free; anything else: the same type and value) or is named by the map; a removed
block when each declaration holding it is in the parent as the candidate has it, or is named. A non-blank line in
no declaration and no module doc keeps the text verdict (`stale path`, `--reverts C`). "As main has it" compares
meanings (theorems) and bodies (everything else), so a reverted matcher is a stale declaration too.
"""
from __future__ import annotations

import argparse
import gzip
import hashlib
import os
import re
import subprocess
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import tree  # noqa: E402

LEAN = r'''
open Lean Elab Command Meta

namespace GatesDecls

/-- `Expr.equal` as the memo key: binder names and infos compared, so the memo never merges different terms. -/
structure K where
  e : Expr
instance : BEq K := ⟨fun a b => a.e.equal b.e⟩
instance : Hashable K := ⟨fun k => k.e.hash⟩

structure S where
  memo : Std.HashMap K Nat := {}
  intern : Std.HashMap String Nat := {}
  out : Array String := #[]
  consts : Std.HashMap Name Nat := {}
  names : Array Name := #[]

abbrev M := StateM S

def cidx (n : Name) : M Nat := do
  let s ← get
  match s.consts[n]? with
  | some i => pure i
  | none =>
    set { s with consts := s.consts.insert n s.names.size, names := s.names.push n }
    pure s.names.size

def lvl : Level → String
  | .zero => "0"
  | .succ l => "s" ++ lvl l
  | .max a b => "m(" ++ lvl a ++ "," ++ lvl b ++ ")"
  | .imax a b => "i(" ++ lvl a ++ "," ++ lvl b ++ ")"
  | .param n => "p" ++ n.toString
  | .mvar _ => "?"

def bi : BinderInfo → String
  | .default => "d" | .implicit => "i" | .strictImplicit => "s" | .instImplicit => "c"

def hex (s : String) : String :=
  s.toUTF8.foldl (fun acc b => acc ++ String.ofList (Nat.toDigits 16 (b.toNat / 16)) ++ String.ofList (Nat.toDigits 16 (b.toNat % 16))) ""

/-- The post-order DAG of `e`, hash-consed on the emitted token. Structural on `Expr` (CHARTER law 4: no `partial`). -/
def go (e : Expr) : M Nat := do
  if let .mdata _ b := e then return ← go b
  if let some i := (← get).memo[K.mk e]? then return i
  let tok ← match e with
    | .bvar i => pure s!"b{i}"
    | .sort l => pure ("S" ++ lvl l)
    | .const n ls => do pure s!"C{← cidx n}[{",".intercalate (ls.map lvl)}]"
    | .app f a => do let x ← go f; let y ← go a; pure s!"A{x},{y}"
    | .lam _ t b i => do let x ← go t; let y ← go b; pure s!"L{bi i}{x},{y}"
    | .forallE _ t b i => do let x ← go t; let y ← go b; pure s!"P{bi i}{x},{y}"
    | .letE _ t v b nd => do let x ← go t; let y ← go v; let z ← go b; pure s!"Z{if nd then 1 else 0}{x},{y},{z}"
    | .lit (.natVal n) => pure s!"N{n}"
    | .lit (.strVal s) => pure ("T" ++ hex s)
    | .proj n i v => do let k ← cidx n; let x ← go v; pure s!"J{k},{i},{x}"
    | .mdata _ b => go b >>= fun x => pure s!"{x}"
    | .fvar _ => pure "?f"
    | .mvar _ => pure "?m"
  let s ← get
  match s.intern[tok]? with
  | some i => set { s with memo := s.memo.insert (K.mk e) i }; pure i
  | none =>
    let i := s.out.size
    set { s with memo := s.memo.insert (K.mk e) i, intern := s.intern.insert tok i, out := s.out.push tok }
    pure i

def ser (e : Expr) : String × String :=
  let (_, s) := (go e).run {}
  (";".intercalate s.out.toList, " ".intercalate (s.names.toList.map toString))

def kind : ConstantInfo → String
  | .axiomInfo _ => "axiom" | .thmInfo _ => "theorem" | .defnInfo _ => "definition" | .opaqueInfo _ => "opaque"
  | .inductInfo _ => "inductive" | .ctorInfo _ => "constructor" | .recInfo _ => "recursor" | .quotInfo _ => "quotient"

syntax (name := declExport) "#decl_export " str str : command

/-- One row per constant of a named module: those the source declared (a declaration range), and the rangeless
non-theorem constants generated beside them (`match_`, `_unary`, …: column 13 `a`), whose bodies are part of the
definition that uses them. Columns: name, priv, owner, module, kind, l0, l1, statement (ser, names), value (ser,
names), text, `r`/`a`. -/
@[command_elab declExport]
def elabDeclExport : CommandElab
  | `(#decl_export $path:str $mods:str) => do
    let wanted : NameSet := ((← IO.FS.readFile mods.getString).splitOn "\n").foldl
      (fun s m => if m.isEmpty then s else s.insert m.toName) {}
    let env ← getEnv
    let h ← IO.FS.Handle.mk path.getString .write
    let mut n := 0
    -- the declared constants, and the rangeless non-theorem ones generated beside them (`match_`, `_unary`, …)
    let mut declared : Array (Name × ConstantInfo × Name × Nat × Nat) := #[]
    let mut rangeless : NameMap (ConstantInfo × Name) := {}
    for (c, ci) in env.constants.map₁.toList do
      let some idx := env.getModuleIdxFor? c | continue
      let mod := env.header.moduleNames[idx.toNat]!
      unless wanted.contains mod do continue
      match ← findDeclarationRanges? c with
      | some r => declared := declared.push (c, ci, mod, r.range.pos.line, r.range.endPos.line)
      | none => unless ci matches .thmInfo _ do rangeless := rangeless.insert c (ci, mod)
    -- a generated constant is a row (`a`) when a declared definition's value reaches it under that definition's name:
    -- it is part of that definition (its matcher, its well-founded unfolding); the rest (`splitter`, `sizeOf`,
    -- `noConfusionType`, …) no definition's value reads
    let mut parts : Array (Name × ConstantInfo × Name) := #[]
    let mut seen : NameSet := {}
    for (c, ci, _, _, _) in declared do
      if ci matches .thmInfo _ then continue
      let some v := ci.value? (allowOpaque := true) | continue
      let mut todo := v.getUsedConstants.toList
      let mut fuel := rangeless.size + 1
      while fuel > 0 do
        fuel := fuel - 1
        match todo with
        | [] => fuel := 0
        | x :: rest =>
          todo := rest
          if seen.contains x || !c.isPrefixOf x then continue
          let some (xi, xm) := rangeless.find? x | continue
          seen := seen.insert x
          parts := parts.push (x, xi, xm)
          if let some xv := xi.value? (allowOpaque := true) then todo := todo ++ xv.getUsedConstants.toList
    let row := fun (c : Name) (ci : ConstantInfo) (mod : Name) (l0 l1 : Nat) (ranged : Bool) =>
      let priv := (privateToUserName? c).map toString |>.getD "-"
      let owner : String := match ci with
        | .ctorInfo i => toString i.induct
        | .recInfo _ => toString c.getPrefix
        | _ => match env.getProjectionFnInfo? c with
          | some p => toString p.ctorName.getPrefix
          | none => "-"
      let (ts, tc) := ser ci.type
      let (vs, vc) := match ci with
        | .thmInfo _ => ("-", "-")
        | _ => match ci.value? (allowOpaque := true) with
          | some v => ser v
          | none => ("-", "-")
      -- the statement as text, for the diff a refusal prints (never compared: the digest is). The kernel
      -- printer, not the delaborator: `ppExpr` over every theorem costs 37 s at f8d04ac, this a few.
      let pp := match ci with
        | .thmInfo _ | .axiomInfo _ => (toString ci.type).quote
        | _ => "-"
      s!"{c}\t{priv}\t{owner}\t{mod}\t{kind ci}\t{l0}\t{l1}\t{ts}\t{tc}\t{vs}\t{vc}\t{pp}\t{if ranged then "r" else "a"}"
    for (c, ci, mod, l0, l1) in declared do
      h.putStrLn (row c ci mod l0 l1 true)
      n := n + 1
    for (c, ci, mod) in parts do
      h.putStrLn (row c ci mod 0 0 false)
      n := n + 1
    for mod in env.header.moduleNames do
      unless wanted.contains mod do continue
      for d in (getModuleDoc? env mod).getD #[] do
        let r := d.declarationRange
        h.putStrLn s!"-\t-\t-\t{mod}\tdoc\t{r.pos.line}\t{r.endPos.line}\t{d.doc.quote}\t-\t-\t-\t-\tr"
        n := n + 1
    h.flush
    logInfo m!"DECL-EXPORT ok: {n} rows"
  | _ => throwUnsupportedSyntax

end GatesDecls
'''

EXPORTER = hashlib.sha256((LEAN + "v4").encode()).hexdigest()[:12]
KEEP = 32            # cache entries kept (the newest); each is one tree's export, about 8 MB gzipped
STATEMENT_KINDS = {"theorem", "axiom"}
FIELDS = 13


def sha(*parts: str) -> str:
    return hashlib.sha256("\0".join(parts).encode()).hexdigest()


def names_of(s: str) -> list[str]:
    return s.split(" ") if s and s != "-" else []


HYGIENE = re.compile(r"\._@\.\S*?\._hyg\.[0-9]+")


def canon(x: str) -> str:
    """A constant's name as a digest reads it: a hygienic name without its macro scope (`…match_on_same_ctor._@.
    Kernel.World.4041475992._hygCtx._hyg.203`, which a derived `decEq` names, renumbers when unrelated text before it
    moves)."""
    return HYGIENE.sub("._@", x) if "._@." in x else x


class Table:
    """One tree's declarations, as exported: the raw rows by name (the declared ones and the rangeless generated
    definitions beside them, `a`), and the digests a judge compares, under RENAME (a function on constant names)
    applied before hashing.

      stmt(n)     the statement: its serialization and the constants it names
      body(n)     what a statement naming n reads of it: a definition's statement and value with its parts (the
                  generated `match_`, `_unary`, … and its `where` helpers, which are the definition); an inductive's
                  statement and its constructors'; an opaque's, a constructor's, a recursor's, an axiom's
                  statement. A theorem has none (its proof is irrelevant)."""
    def __init__(self, raws, rename=None):
        self.rows: dict[str, list[str]] = {}
        self.docs: list[list[str]] = []
        r = rename or (lambda x: x)
        self.r = lambda x: canon(r(x))
        self.ctors: dict[str, list[str]] = {}
        for f in raws:
            if f[4] == "doc":
                self.docs.append(f)
                continue
            self.rows[f[0]] = f
            if f[4] == "constructor" and f[2] != "-":
                self.ctors.setdefault(f[2], []).append(f[0])
        self._body: dict[str, str] = {}
        self._stmt: dict[str, str] = {}

    def cs(self, s: str) -> str:
        return " ".join(self.r(x) for x in names_of(s))

    def stmt(self, n: str) -> str:
        if n not in self._stmt:
            f = self.rows[n]
            self._stmt[n] = sha(f[7], self.cs(f[8]))
        return self._stmt[n]

    def value(self, n: str) -> str:
        f = self.rows[n]
        return "-" if f[9] == "-" else sha(f[9], self.cs(f[10]))

    def parts(self, n: str) -> list[str]:
        """What is part of definition N: the constants its value reaches under its name, generated beside it (no
        range: `match_`, `_unary`) or declared inside its range (a `where` helper), as `adopt` reads ownership."""
        f = self.rows[n]
        out, todo, seen = [], names_of(f[10]), set()
        while todo:
            x = todo.pop()
            if x in seen or not x.startswith(n + "."):
                continue
            seen.add(x)
            g = self.rows.get(x)
            if g is None or g[4] == "theorem":
                continue
            if g[12] == "a" or (g[3] == f[3] and int(f[5]) <= int(g[5]) and int(g[6]) <= int(f[6])):
                out.append(x)
                todo += names_of(g[10])
        return sorted(out, key=self.r)

    def body(self, n: str) -> str | None:
        """None for a theorem and for a constant this tree does not export (the toolchain's)."""
        f = self.rows.get(n)
        if f is None or f[4] == "theorem":
            return None
        if n in self._body:
            return self._body[n]
        k = f[4]
        if k == "definition":
            out = sha("D", self.stmt(n), self.value(n),
                      *(f"{self.r(x)}={self.stmt(x)}={self.value(x)}" for x in self.parts(n)))
        elif k == "inductive":
            ks = sorted(self.ctors.get(n, []), key=self.r)
            out = sha("I", self.stmt(n), *(f"{self.r(x)}={self.stmt(x)}" for x in ks))
        else:                                # opaque (uninterpreted in proofs), constructor, recursor, axiom, quotient
            out = sha(k, self.stmt(n))
        self._body[n] = out
        return out



class Row:
    __slots__ = ("name", "priv", "owner", "module", "kind", "l0", "l1", "stmt", "value", "text", "raw")

    def __init__(self, f: list[str], t: Table | None):
        self.name, self.priv, self.owner, self.module, self.kind = f[0], f[1], f[2], f[3], f[4]
        self.l0, self.l1, self.text, self.raw = int(f[5]), int(f[6]), f[11], f
        if self.kind == "doc":
            self.stmt = self.value = sha("doc", f[7])
        else:
            self.stmt = t.stmt(self.name)
            self.value = t.body(self.name) or "-"

    def key(self) -> str:
        return f"doc:{self.module}:{self.stmt}" if self.kind == "doc" else self.name


def rows_of(t: Table, raws, rename=None) -> dict[str, Row]:
    """The DECLARED rows of RAWS (a rangeless generated definition is part of its user, never a row of its own), keyed
    by name under RENAME (docs by their text)."""
    r = rename or (lambda x: x)
    out = {}
    for f in raws:
        if f[4] != "doc" and f[12] != "r":
            continue
        row = Row(f, t)
        out[r(row.name) if row.kind != "doc" else row.key()] = row
    return out


def run_export(root: str, modules: list[str]) -> list[list[str]]:
    """Import MODULES (built) in ROOT's environment and export their declarations, raw."""
    gd = os.path.join(root, ".lake", "gates")
    os.makedirs(gd, exist_ok=True)
    mods_file, out, run = (os.path.join(gd, x) for x in ("decl-modules.txt", "decl-export.tsv", "DeclRun.lean"))
    with open(mods_file, "w", encoding="utf-8") as fh:
        fh.write("".join(m + "\n" for m in modules))
    with open(run, "w", encoding="utf-8") as fh:
        fh.write("import Lean\n" + "".join(f"import {m}\n" for m in modules) + LEAN +
                 f'\n#decl_export "{out}" "{mods_file}"\n')
    if os.path.exists(out):
        os.remove(out)
    r = subprocess.run(["lake", "env", "lean", "-DmaxHeartbeats=0", run], cwd=root, capture_output=True, text=True)
    said = (r.stdout + r.stderr).strip()
    if r.returncode != 0 or "DECL-EXPORT ok" not in said or not os.path.exists(out):
        # a kill under load names its signal, so scripts/pre-push reads KILLED(load), never a verdict
        sig = -r.returncode if r.returncode < 0 else r.returncode - 128 if r.returncode in (137, 143) else 0
        how = f"(signal {sig})" if sig else f"(lean exit {r.returncode})"
        raise SystemExit(f"decls: NO VERDICT — the export failed {how}: {said[-2000:]}")
    rows = []
    with open(out, encoding="utf-8") as fh:
        for line in fh:
            f = line.rstrip("\n").split("\t")
            if len(f) != FIELDS:
                raise SystemExit(f"decls: NO VERDICT — an export row has {len(f)} fields, not {FIELDS}: {line[:200]!r}")
            rows.append(f)
    return rows


def importable(t: tree.Tree) -> list[str]:
    roots = set(t.exes.values())   # an exe root holds only `main` (closure C7); two would collide
    return sorted(m for m in t.modules if m not in roots)


def cache_path(cache: str, oid: str) -> str:
    return os.path.join(cache, f"{oid}-{EXPORTER}.tsv.gz")


def load_cache(cache: str, oid: str) -> list[list[str]] | None:
    """OID's export, raw (every row the judge's Lean wrote, so a parent's statement can be read back)."""
    p = cache_path(cache, oid)
    if not os.path.exists(p):
        return None
    with gzip.open(p, "rt", encoding="utf-8") as fh:
        return [line.rstrip("\n").split("\t") for line in fh]


def save_cache(cache: str, oid: str, raws: list[list[str]]) -> None:
    os.makedirs(cache, exist_ok=True)
    p = cache_path(cache, oid)
    tmp = f"{p}.{os.getpid()}.tmp"
    with gzip.open(tmp, "wt", encoding="utf-8") as fh:
        for f in sorted(raws):
            fh.write("\t".join(f) + "\n")
    os.replace(tmp, p)
    # This judge's own files only: the newest KEEP entries stay.
    entries = sorted((os.path.join(cache, x) for x in os.listdir(cache) if x.endswith(".tsv.gz")),
                     key=os.path.getmtime, reverse=True)
    for old in entries[KEEP:]:
        try:
            os.remove(old)
        except OSError:
            pass


def adopt(rows) -> None:
    """A declaration generated WITH another (`casesOn`, `noConfusion`, `recOn`, a derived instance's method, a
    `where` helper, the axiom `native_decide` adds for a theorem) has that one as its owner: its name extends the
    owner's, and the elaborator records it inside the owner's source range. Constructors, recursors and projections
    carry their owner from Lean. The nearest such prefix owns it."""
    rows = list(rows)
    at = {(r.name, r.module): r for r in rows if r.kind != "doc"}
    for r in rows:
        if r.kind == "doc" or r.owner != "-":
            continue
        pre = r.name
        while "." in pre:
            pre = pre.rsplit(".", 1)[0]
            o = at.get((pre, r.module))
            if o is not None and o.l0 <= r.l0 and r.l1 <= o.l1:
                r.owner = pre
                break


def reach(t: tree.Tree, changed_mods: set[str]) -> set[str]:
    """The changed modules present in T, their importers, and the importers of a changed module T lacks."""
    present = {m for m in changed_mods if m in t.modules}
    gone = changed_mods - present
    dep = t.dependents()
    r = set(present).union(*(dep[m] for m in present)) if present else set()
    for m, mod in t.modules.items():
        if gone & set(mod.imports):
            r |= {m} | dep[m]
    return r


# ---------------------------------------------------------------- the declared map

VERBS = ("RESTATES-MEANING", "RESTATES", "RENAMES", "DELETES-MODULE", "DELETES")
MAPLINE = re.compile(r"^(" + "|".join(VERBS) + r"):[ \t]*(\S+)(?:[ \t]*(?:→|->)[ \t]*(\S+))?[ \t]*$", re.M)


def read_map(message: str) -> list[tuple[str, str, str, str]]:
    """(verb, old, new, the line) of every map line of the message."""
    return [(m.group(1), m.group(2), m.group(3) or m.group(2), m.group(0).strip()) for m in MAPLINE.finditer(message)]


def prefix_map(pairs: dict[str, str]):
    """A function renaming a constant by the longest entry that is a component-wise prefix of it."""
    keys = sorted(pairs, key=len, reverse=True)

    def f(x: str) -> str:
        for k in keys:
            if x == k or x.startswith(k + "."):
                return pairs[k] + x[len(k):]
        return x
    return f if pairs else (lambda x: x)


def text_diff(old: str, new: str, width: int = 6, cap: int = 8) -> list[str]:
    """The changed token runs of two statements (the kernel printer's text), with WIDTH tokens of context."""
    import difflib
    unq = lambda s: s[1:-1].replace('\\"', '"').replace("\\\\", "\\") if len(s) > 1 and s[0] == '"' else s
    # a hygienic binder name embeds its module and a counter; shown as `x✝` (display only: the digest decides)
    hyg = lambda s: re.sub(r"(\S*?)\._@\.\S*?\._hyg\.[0-9]+", r"\1✝", s)
    a, b = hyg(unq(old)).split(), hyg(unq(new)).split()
    out = []
    for op, i1, i2, j1, j2 in difflib.SequenceMatcher(None, a, b, autojunk=False).get_opcodes():
        if op == "equal":
            continue
        ctx = " ".join(a[max(0, i1 - width):i1])
        out.append(f"      … {ctx} [- {' '.join(a[i1:i2])[:300]} -] [+ {' '.join(b[j1:j2])[:300]} +] …")
        if len(out) == cap:
            out.append("      … (more changes)")
            break
    return out or ["      (the texts are equal; the elaborated terms differ in what the printer does not show)"]


# ---------------------------------------------------------------- the judge

def judge(a, lean=None) -> int:
    """LEAN (the plants' stand-in for `run_export`) defaults to the judge's own Lean."""
    lean = lean or run_export
    cand_t, base_t = tree.read(a.root), tree.read(a.base_root)
    changed = [l.strip() for l in open(a.changed, encoding="utf-8") if l.strip()]
    lean_mods = {p[:-5].replace("/", ".") for p in changed if p.endswith(".lean") and p != "lakefile.lean"}
    build_inputs = any(p in ("lakefile.lean", "lean-toolchain", "lake-manifest.json") for p in changed)
    rc_ = reach(cand_t, lean_mods) if not build_inputs else set(cand_t.modules)
    rb_ = reach(base_t, lean_mods) if not build_inputs else set(base_t.modules)
    exe_roots = set(cand_t.exes.values()) | set(base_t.exes.values())
    rc, rb = rc_ - exe_roots, rb_ - exe_roots
    base_raw = load_cache(a.cache, a.base)
    if not rc and not rb:
        if base_raw is not None:
            save_cache(a.cache, a.cand, base_raw)
        print("decls: ok (no module changed)")
        return 0
    if base_raw is None:
        print(f"decls: the parent's declarations ({a.base[:12]}, exporter {EXPORTER}) are not cached")
        return 4
    entries = read_map(open(a.message, encoding="utf-8").read())
    # RENAMES / RESTATES / RESTATES-MEANING with two names rename OLD inside every statement (inverted on the
    # candidate side, so the parent's digests are taken as they are).
    pairs = {new: old for verb, old, new, _ in entries
             if verb in ("RESTATES", "RENAMES", "RESTATES-MEANING") and new != old}
    base = Table(base_raw)
    in_reach = lambda f: f[3] in rb or f[3] in rc
    raw = lean(a.root, sorted(rc)) if rc else []

    bpriv, cpriv = {}, {}
    for f in base_raw:
        if f[1] != "-" and f[4] != "doc" and f[12] == "r":
            bpriv.setdefault(f[1], []).append(f[0])
    for f in raw:
        if f[1] != "-" and f[12] == "r":
            cpriv.setdefault(f[1], []).append(f[0])
    for u, cs in cpriv.items():       # a private declaration moved with its module: matched by its user name
        bs = bpriv.get(u, [])
        if len(cs) == 1 and len(bs) == 1 and cs[0] != bs[0] and cs[0] not in base.rows:
            pairs.setdefault(cs[0], bs[0])
    inv = prefix_map(pairs)

    whole = [f for f in base_raw if not in_reach(f)] + raw
    save_cache(a.cache, a.cand, whole)
    cand = Table(whole, inv)
    plain = rows_of(Table(whole), raw)
    cand_names = {r.name for r in plain.values() if r.kind != "doc"}
    C = rows_of(cand, raw, inv)
    P = rows_of(base, [f for f in base_raw if in_reach(f)])
    deleted_mods = {m for m in base_t.modules if m not in cand_t.modules}
    adopt(P.values())
    adopt(plain.values())
    owned = {}
    for r in P.values():
        if r.owner != "-":
            owned.setdefault(r.owner, set()).add(r.key())

    def covers(name: str) -> set[str]:
        out, todo = set(), [name]
        while todo:
            x = todo.pop()
            if x not in out:
                out.add(x)
                todo.extend(owned.get(x, ()))
        return out

    def top(r: Row) -> Row:
        """The declaration R was generated with (its owner, transitively, within the parent)."""
        seen = set()
        while r.owner != "-" and r.owner in P and r.owner not in seen:
            seen.add(r.owner)
            r = P[r.owner]
        return r

    def same(p: Row, c: Row) -> bool:
        if p.kind in STATEMENT_KINDS:
            return p.stmt == c.stmt
        return p.stmt == c.stmt and p.value == c.value

    def diff_of(p: Row, c: Row | None) -> list[str]:
        if c is None or p.kind not in STATEMENT_KINDS:
            return []
        return text_diff(p.text, c.text)

    # the theorems of the parent's reach whose statements name each definition (GATES-20v′: what a body edit moves)
    named_by: dict[str, list[str]] = {}
    for r in P.values():
        if r.kind in STATEMENT_KINDS:
            for x in names_of(base.rows[r.name][8]):
                named_by.setdefault(x, []).append(r.name)

    red, add = [], []
    named: dict[str, str] = {}             # parent declaration → the map line that names it
    modules_named = set()
    for verb, old, new, line in entries:
        if verb == "DELETES-MODULE":
            if old not in base_t.modules or old in cand_t.modules:
                red.append(f"  decls: unused map line: {line} ({old} is "
                           f"{'not a module of the parent' if old not in base_t.modules else 'still a module'}); "
                           f"drop the line")
            else:
                modules_named.add(old)
            continue
        if old not in P:
            red.append(f"  decls: unused map line: {line} ({old} is not a declaration of the parent in the modules "
                       f"this landing reaches); drop the line")
            continue
        if verb == "DELETES":
            if old in cand_names:
                red.append(f"  decls: unused map line: {line} ({old} is still declared); drop the line")
                continue
        elif new not in cand_names:
            red.append(f"  decls: unused map line: {line} ({new} is not declared by the landing); drop the line")
            continue
        elif old != new and old in cand_names:
            red.append(f"  decls: unused map line: {line} ({old} is still declared beside {new}: that is a new "
                       f"declaration, not a {verb.lower()})")
            continue
        else:
            p, c = P[old], C.get(old)
            if verb in ("RENAMES", "RESTATES"):
                if verb == "RENAMES" and old == new:
                    red.append(f"  decls: unused map line: {line} (a rename names two different declarations)")
                    continue
                if not same(p, c):
                    what = "rename" if verb == "RENAMES" else "restate"
                    red.append(f"  decls: {what} not equal: {line}: {new}'s elaborated "
                               f"{'statement' if p.kind in STATEMENT_KINDS else 'statement and body'} under the map is "
                               f"not {old}'s; a deliberate change of meaning is written RESTATES-MEANING: "
                               f"{old}{'' if old == new else ' → ' + new}")
                    red += diff_of(p, c)
                    continue
                if old == new:
                    red.append(f"  decls: unused map line: {line} ({old} is unchanged); drop the line")
                    continue
            elif same(p, c):      # RESTATES-MEANING
                red.append(f"  decls: unused map line: {line} ({new}'s "
                           f"{'statement' if p.kind in STATEMENT_KINDS else 'statement and body'} is {old}'s under "
                           f"the map: {'drop the line' if old == new else 'write RENAMES'})")
                continue
        for k in covers(old):
            named.setdefault(k, line)

    lined = {old for verb, old, *_ in entries if verb != "DELETES-MODULE"}   # a refused line is reported once
    reported_mods = set()
    for k, p in sorted(P.items()):
        if p.kind == "doc":
            continue
        c = C.get(k)
        t = top(p)
        if c is None:
            if k in named or t.key() in named or p.module in modules_named or k in lined:
                continue
            if t is not p:
                continue           # generated with its owner: the owner's absence is reported, or its change is not a deletion
            if p.module in deleted_mods:
                if p.module not in reported_mods:
                    reported_mods.add(p.module)
                    n = sum(1 for r in P.values() if r.module == p.module and r.kind != "doc")
                    red.append(f"  decls: undeclared module deletion: {p.module} ({n} declarations) is absent from "
                               f"the landing")
                    add.append(f"DELETES-MODULE: {p.module}")
                continue
            red.append(f"  decls: undeclared deletion: {k} ({p.kind}, {p.module}:{p.l0}-{p.l1}) is absent from the "
                       f"landing")
            add.append(f"DELETES: {k}")
        elif k in named or k in lined or t is not p:
            continue
        elif p.kind in STATEMENT_KINDS and p.stmt != c.stmt:
            red.append(f"  decls: undeclared restatement: {k} ({p.module}:{p.l0}-{p.l1}): its elaborated statement "
                       f"differs from the parent's")
            red += diff_of(p, c)
            add.append(f"RESTATES-MEANING: {k}")
        elif p.kind not in STATEMENT_KINDS and p.value != c.value and k in named_by:
            # GATES-20v′: a definition a theorem's statement names moved its body (`MovesThrough := … ∧ False`): the
            # meaning of those statements moved with no statement changing; one line names it
            ts = named_by[k]
            red.append(f"  decls: undeclared redefinition: {k} ({p.module}:{p.l0}-{p.l1}): its body changed, and the "
                       f"statements of {', '.join(ts[:4])}{f' and {len(ts) - 4} more' if len(ts) > 4 else ''} name it")
            add.append(f"RESTATES-MEANING: {k}")

    # CHECK 2: the stale-copy lacks rebase.py forwarded (.lean paths).
    if a.lean_lacks and os.path.exists(a.lean_lacks):
        cdocs = {r.stmt for r in C.values() if r.kind == "doc"}
        pdocs = {r.stmt for r in P.values() if r.kind == "doc"}
        crow_by_mod, prow_by_mod = {}, {}
        for r in plain.values():
            crow_by_mod.setdefault(r.module, []).append(r)
        for r in P.values():
            prow_by_mod.setdefault(r.module, []).append(r)
        for line in open(a.lean_lacks, encoding="utf-8"):
            f = line.rstrip("\n").split("\t")
            if len(f) != 5:
                continue
            path, c_short, subj, side, spans = f
            mod = path[:-5].replace("/", ".")
            lines = [tuple(map(int, s.split("-"))) for s in spans.split(",") if s]
            root = a.base_root if side == "add" else a.root
            text = open(os.path.join(root, path), encoding="utf-8", errors="replace").read().split("\n")
            rows = prow_by_mod.get(mod, []) if side == "add" else crow_by_mod.get(mod, [])
            bad, outside = [], []
            for lo, hi in lines:
                if lo == 0:                # the block could not be located: every line of it is unexplained
                    outside.append(0)
                    continue
                for n in range(lo, hi + 1):
                    hold = [r for r in rows if r.l0 <= n <= r.l1]
                    if not hold:
                        if n - 1 < len(text) and text[n - 1].strip():
                            outside.append(n)
                        continue
                    for r in hold:
                        if r.kind == "doc":
                            if r.stmt not in (cdocs if side == "add" else pdocs):
                                bad.append(("doc", r))
                            continue
                        if side == "add":
                            c = C.get(r.key())
                            ok = (r.key() in named or top(r).key() in named or r.module in modules_named
                                  or (c is not None and same(r, c)))
                        else:
                            k = inv(r.name)
                            p = P.get(k)
                            ok = k in named or (p is not None and k in C and same(p, C[k]))
                        if not ok:
                            bad.append(("declaration", r))
            seen = set()
            for what, r in bad:
                if (what, r.key()) in seen:
                    continue
                seen.add((what, r.key()))
                nm = r.name if what == "declaration" else f"the module doc at {path}:{r.l0}"
                if side == "add":
                    red.append(f"  decls: stale declaration: {nm} ({path}:{r.l0}-{r.l1} in main's copy): {c_short} "
                               f"({subj}) changed it and the landing does not hold main's version; re-apply your "
                               f"edit on main's copy (git show main:{path})")
                else:
                    red.append(f"  decls: stale declaration: {nm} ({path}:{r.l0}-{r.l1} in the landing's copy): "
                               f"{c_short} ({subj}) removed these lines and the landing holds them again; re-apply "
                               f"your edit on main's copy (git show main:{path})")
            if outside:
                spans_s = ",".join(str(n) for n in outside[:20]) + ("…" if len(outside) > 20 else "")
                where = "main's copy" if side == "add" else "the landing's copy"
                red.append(f"  decls: stale path: {path}: the landing lacks {c_short}'s change ({subj}) on lines "
                           f"{spans_s} of {where}, outside every declaration; re-apply your edit on main's copy (git "
                           f"show main:{path}), or, when undoing {c_short} is the point, add: --reverts {c_short}")
    meaning = sum(1 for v, *_ in entries if v == "RESTATES-MEANING")
    if red:
        print("\n".join(red))
        # each line a lander may paste, in the verdict's summary (scripts/pre-push prints the `  decls: ` lines)
        print("\n".join(f"  decls: when it is the point, add the line: {x}" for x in add))
        print(f"decls: RED ({sum(1 for l in red if l.startswith('  decls: '))}) — {len(rc)} module(s) exported, "
              f"{len(P)} parent declaration(s) in the reach")
        return 1
    print(f"decls: ok — {len(rc)} module(s) exported, {len(P)} parent declaration(s) in the reach, {len(entries)} map "
          f"line(s), {meaning} declared change(s) of meaning")
    return 0


def main() -> int:
    ap = argparse.ArgumentParser()
    sub = ap.add_subparsers(dest="cmd", required=True)
    j = sub.add_parser("judge")
    for x in ("--root", "--base-root", "--cache", "--base", "--cand", "--changed", "--message"):
        j.add_argument(x, required=True)
    j.add_argument("--lean-lacks")
    b = sub.add_parser("bootstrap")
    for x in ("--root", "--cache", "--tree"):
        b.add_argument(x, required=True)
    h = sub.add_parser("have")
    for x in ("--cache", "--tree"):
        h.add_argument(x, required=True)
    lb = sub.add_parser("libs")
    lb.add_argument("--root", required=True)
    e = sub.add_parser("export")
    e.add_argument("--root", required=True)
    e.add_argument("--out", required=True)
    e.add_argument("--modules")
    a = ap.parse_args()
    if a.cmd == "judge":
        return judge(a)
    if a.cmd == "libs":
        print(" ".join(tree.read(a.root).libs))
        return 0
    if a.cmd == "have":
        return 0 if os.path.exists(cache_path(a.cache, a.tree)) else 1
    if a.cmd == "bootstrap":
        t = tree.read(a.root)
        raws = run_export(a.root, importable(t))
        save_cache(a.cache, a.tree, raws)
        print(f"decls: the parent's declarations exported whole: {len(raws)} rows ({a.tree[:12]})")
        return 0
    t = tree.read(a.root)
    mods = [l.strip() for l in open(a.modules) if l.strip()] if a.modules else importable(t)
    with open(a.out, "w", encoding="utf-8") as fh:
        for f in run_export(a.root, mods):
            fh.write("\t".join(f) + "\n")
    return 0


if __name__ == "__main__":
    sys.exit(main())
