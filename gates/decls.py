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
`_simp_` have none). Columns: name, its user name when private (else -), its owner (a constructor's or recursor's
inductive, a projection's structure; else -), module, kind, first and last source line, the statement's
serialization and the constants it names, the value's (a non-theorem's; a proof is irrelevant: -), and a theorem's
statement as text (for the diff a refusal prints). Module docs are rows of kind `doc`. The serialization is the term's post-order DAG hash-consed on the emitted token (sharing is
canonical, binder NAMES are erased, binder INFO kept, metadata transparent) with constants abstracted to indices
into a first-visit list; the digest is SHA-256 over it, taken here. No hash is equality inside Lean.

THE CACHE. A digest file per (tree, exporter): `DIR/<tree>-<exporter>.tsv.gz`, rows `name priv owner module kind l0
l1 statement value text` (digests under the identity map; text = a theorem's statement as the kernel prints it). A landing exports only its REACH (the changed modules and their
importers, in either tree, plus the importers of a deleted module): a module outside both reaches has the same
source and the same imports in both trees, so the same declarations. The candidate's digest is the parent's rows
outside the reach plus the candidate's export of it, cached under the candidate's tree, which is main's tree once
it lands. A miss (exit 4) is bootstrapped by scripts/pre-push: the parent built in the slot and exported whole.

CHECK 1, THE DIFF (R-0034's conditions). Every declaration of the parent absent from the candidate, and every
theorem (or axiom) of the parent whose elaborated statement differs, is named by a line of the landing's message:
  RENAMES: OLD → NEW             NEW is OLD renamed: its statement must equal OLD's under the map (checked)
  RESTATES: OLD → NEW            the same check (`restate not equal`); OLD may be NEW (then it must have changed
                                 nothing but its proof, and the line is unused)
  RESTATES-MEANING: OLD [→ NEW]  a deliberate change of meaning: the statement may differ (and must)
  DELETES: NAME                  NAME removed
  DELETES-MODULE: MODULE         MODULE removed, with every declaration in it (one line; no free pass)
A theorem whose statement differs without a RESTATES-MEANING line is `undeclared restatement`, printed with the
diff of the two statements (the kernel printer's text; the digest, never the text, decides). A line covers the
declarations its declaration OWNS (constructors, recursor, projections, `casesOn`/`noConfusion`, `where` helpers,
a `native_decide` axiom). A two-name line renames OLD inside every candidate statement (inverted: NEW → OLD, by the
longest component-wise prefix, so generated children follow their owner) before the compare, so the cached parent
digest never depends on a map. A private declaration whose user name is unique among the private declarations of
both trees is matched by that name across a module move. A line that applies to nothing is `unused map line`.

CHECK 2, THE STALE COPY. gates/rebase.py `stale` still detects, by text, that a `.lean` copy lacks a window commit
C's change (GATES-20b/20b′); it no longer refuses it but writes the lack (--lean-lacks: path, C, side, the lines in
main's copy for a block C added, in the candidate's for a block C removed). Here the lines are mapped to the
declarations whose recorded ranges hold them (main's environment for an added block, the candidate's for a removed
one). An added block is explained when each declaration holding it is in the candidate as main has it (theorem:
the same statement, the proof free; anything else: the same type and value) or is named by the map; a removed
block when each declaration holding it is in the parent as the candidate has it, or is named. A non-blank line in
no declaration and no module doc keeps the text verdict (`stale path`, `--reverts C`).
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
open Lean Elab Command

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

partial def go (e : Expr) : M Nat := do
  if let .mdata _ b := e then return ← go b
  if let some i := (← get).memo[K.mk e]? then return i
  let tok ← match e with
    | .bvar i => pure s!"b{i}"
    | .sort l => pure ("S" ++ lvl l)
    | .const n ls => do pure s!"C{← cidx n}[{",".intercalate (ls.map lvl)}]"
    | .app f a => do let x ← go f; let y ← go a; pure s!"A{x},{y}"
    | .lam _ t b i => do let x ← go t; let y ← go b; pure s!"L{bi i}{x},{y}"
    | .forallE _ t b i => do let x ← go t; let y ← go b; pure s!"P{bi i}{x},{y}"
    | .letE _ t v b nd => do let x ← go t; let y ← go v; let z ← go b; pure s!"Z{nd}{x},{y},{z}"
    | .lit (.natVal n) => pure s!"N{n}"
    | .lit (.strVal s) => pure ("T" ++ s.quote)
    | .proj n i v => do let k ← cidx n; let x ← go v; pure s!"J{k},{i},{x}"
    | .mdata _ b => do let x ← go b; pure s!"{x}"
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

@[command_elab declExport]
def elabDeclExport : CommandElab
  | `(#decl_export $path:str $mods:str) => do
    let wanted : NameSet := ((← IO.FS.readFile mods.getString).splitOn "\n").foldl
      (fun s m => if m.isEmpty then s else s.insert m.toName) {}
    let env ← getEnv
    let h ← IO.FS.Handle.mk path.getString .write
    let mut n := 0
    for (c, ci) in env.constants.map₁.toList do
      let some idx := env.getModuleIdxFor? c | continue
      let mod := env.header.moduleNames[idx.toNat]!
      unless wanted.contains mod do continue
      let some r ← findDeclarationRanges? c | continue
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
      h.putStrLn s!"{c}\t{priv}\t{owner}\t{mod}\t{kind ci}\t{r.range.pos.line}\t{r.range.endPos.line}\t{ts}\t{tc}\t{vs}\t{vc}\t{pp}"
      n := n + 1
    for mod in env.header.moduleNames do
      unless wanted.contains mod do continue
      for d in (getModuleDoc? env mod).getD #[] do
        let r := d.declarationRange
        h.putStrLn s!"-\t-\t-\t{mod}\tdoc\t{r.pos.line}\t{r.endPos.line}\t{d.doc.quote}\t-\t-\t-\t-"
        n := n + 1
    h.flush
    logInfo m!"DECL-EXPORT ok: {n} rows"
  | _ => throwUnsupportedSyntax

end GatesDecls
'''

EXPORTER = hashlib.sha256((LEAN + "v2").encode()).hexdigest()[:12]
KEEP = 64            # cache entries kept (the newest); each is one tree's digest
STATEMENT_KINDS = {"theorem", "axiom"}
FIELDS = 12


def sha(*parts: str) -> str:
    return hashlib.sha256("\0".join(parts).encode()).hexdigest()


class Row:
    __slots__ = ("name", "priv", "owner", "module", "kind", "l0", "l1", "stmt", "value", "text", "raw")

    def __init__(self, name, priv, owner, module, kind, l0, l1, stmt, value, text="-", raw=None):
        self.name, self.priv, self.owner, self.module, self.kind = name, priv, owner, module, kind
        self.l0, self.l1, self.stmt, self.value, self.text, self.raw = int(l0), int(l1), stmt, value, text, raw

    def key(self) -> str:
        return f"doc:{self.module}:{self.stmt}" if self.kind == "doc" else self.name

    def line(self) -> str:
        return "\t".join([self.name, self.priv, self.owner, self.module, self.kind, str(self.l0), str(self.l1),
                          self.stmt, self.value, self.text]) + "\n"


def digest_row(f: list[str], rename=None) -> Row:
    """A raw export row → its digests; RENAME (a function on constant names) applied before hashing."""
    name, priv, owner, module, kind, l0, l1, ts, tc, vs, vc, text = f
    if kind == "doc":
        return Row(name, priv, owner, module, kind, l0, l1, sha("doc", ts), "-", "-", f)
    r = rename or (lambda x: x)
    cs = lambda s: " ".join(r(x) for x in s.split(" ")) if s else ""
    stmt = sha(ts, cs(tc))
    value = "-" if vs == "-" else sha(vs, cs(vc))
    return Row(name, priv, owner, module, kind, l0, l1, stmt, value, text, f)


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


def load_cache(cache: str, oid: str) -> dict[str, Row] | None:
    p = cache_path(cache, oid)
    if not os.path.exists(p):
        return None
    out = {}
    with gzip.open(p, "rt", encoding="utf-8") as fh:
        for line in fh:
            r = Row(*line.rstrip("\n").split("\t"))
            out[r.key()] = r
    return out


def save_cache(cache: str, oid: str, rows: dict[str, Row]) -> None:
    os.makedirs(cache, exist_ok=True)
    p = cache_path(cache, oid)
    tmp = f"{p}.{os.getpid()}.tmp"
    with gzip.open(tmp, "wt", encoding="utf-8") as fh:
        for k in sorted(rows):
            fh.write(rows[k].line())
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

def judge(a) -> int:
    cand_t, base_t = tree.read(a.root), tree.read(a.base_root)
    changed = [l.strip() for l in open(a.changed, encoding="utf-8") if l.strip()]
    lean_mods = {p[:-5].replace("/", ".") for p in changed if p.endswith(".lean") and p != "lakefile.lean"}
    build_inputs = any(p in ("lakefile.lean", "lean-toolchain", "lake-manifest.json") for p in changed)
    rc_ = reach(cand_t, lean_mods) if not build_inputs else set(cand_t.modules)
    rb_ = reach(base_t, lean_mods) if not build_inputs else set(base_t.modules)
    exe_roots = set(cand_t.exes.values()) | set(base_t.exes.values())
    rc, rb = rc_ - exe_roots, rb_ - exe_roots
    base = load_cache(a.cache, a.base)
    if not rc and not rb:
        if base is not None:
            save_cache(a.cache, a.cand, base)
        print("decls: ok (no module changed)")
        return 0
    if base is None:
        print(f"decls: the parent's declarations ({a.base[:12]}, exporter {EXPORTER}) are not cached")
        return 4
    entries = read_map(open(a.message, encoding="utf-8").read())
    # RENAMES / RESTATES / RESTATES-MEANING with two names rename OLD inside every statement (inverted on the
    # candidate side, so the cached parent digest is used as it is).
    pairs = {new: old for verb, old, new, _ in entries
             if verb in ("RESTATES", "RENAMES", "RESTATES-MEANING") and new != old}

    raw = run_export(a.root, sorted(rc)) if rc else []
    bpriv, cpriv = {}, {}
    for r in base.values():
        if r.priv != "-" and r.kind != "doc":
            bpriv.setdefault(r.priv, []).append(r.name)
    for f in raw:
        if f[1] != "-":
            cpriv.setdefault(f[1], []).append(f[0])
    for u, cs in cpriv.items():       # a private declaration moved with its module: matched by its user name
        bs = bpriv.get(u, [])
        if len(cs) == 1 and len(bs) == 1 and cs[0] != bs[0] and cs[0] not in base:
            pairs.setdefault(cs[0], bs[0])
    inv = prefix_map(pairs)
    plain = [digest_row(f) for f in raw]
    cand_names = {r.name for r in plain if r.kind != "doc"}
    C = {(inv(r.name) if r.kind != "doc" else r.key()): digest_row(r.raw, inv) for r in plain}

    in_reach = lambda r: r.module in rb or r.module in rc
    whole = {k: r for k, r in base.items() if not in_reach(r)}
    for r in plain:
        whole[r.key()] = r
    save_cache(a.cache, a.cand, whole)

    P = {k: r for k, r in base.items() if in_reach(r)}
    deleted_mods = {m for m in base_t.modules if m not in cand_t.modules}
    adopt(P.values())
    adopt(plain)
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
                    red.append(f"  decls: {what} not equal: {line}: {new}'s elaborated statement under the map is "
                               f"not {old}'s; a deliberate change of meaning is written RESTATES-MEANING: "
                               f"{old}{'' if old == new else ' → ' + new}")
                    red += diff_of(p, c)
                    continue
                if old == new:
                    red.append(f"  decls: unused map line: {line} ({old} is unchanged); drop the line")
                    continue
            elif same(p, c):      # RESTATES-MEANING
                red.append(f"  decls: unused map line: {line} ({new}'s statement is {old}'s under the map: "
                           f"{'drop the line' if old == new else 'write RENAMES'})")
                continue
        for k in covers(old):
            named.setdefault(k, line)

    lined = {old for verb, old, _, _ in entries if verb != "DELETES-MODULE"}   # a refused line is reported once
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
        elif p.kind in STATEMENT_KINDS and p.stmt != c.stmt and t is p and named.get(k, "").split(":")[0] \
                != "RESTATES-MEANING":
            if k in named or k in lined:
                continue           # a RENAMES/RESTATES line that names it was refused above, with its diff
            red.append(f"  decls: undeclared restatement: {k} ({p.module}:{p.l0}-{p.l1}): its elaborated statement "
                       f"differs from the parent's")
            red += diff_of(p, c)
            add.append(f"RESTATES-MEANING: {k}")

    # CHECK 2: the stale-copy lacks rebase.py forwarded (.lean paths).
    if a.lean_lacks and os.path.exists(a.lean_lacks):
        cdocs = {r.stmt for r in C.values() if r.kind == "doc"}
        pdocs = {r.stmt for r in P.values() if r.kind == "doc"}
        crow_by_mod, prow_by_mod = {}, {}
        for r in plain:
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
                            ok = k in named or (p is not None and same(p, C[k]))
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
        rows = {}
        for f in run_export(a.root, importable(t)):
            r = digest_row(f)
            rows[r.key()] = r
        save_cache(a.cache, a.tree, rows)
        print(f"decls: the parent's declarations exported whole: {len(rows)} rows ({a.tree[:12]})")
        return 0
    t = tree.read(a.root)
    mods = [l.strip() for l in open(a.modules) if l.strip()] if a.modules else importable(t)
    with open(a.out, "w", encoding="utf-8") as fh:
        for f in run_export(a.root, mods):
            fh.write("\t".join(f) + "\n")
    return 0


if __name__ == "__main__":
    sys.exit(main())
