"""gates/size.py TREE [--base SIZE.md-of-parent] [--message FILE] [--write]

The size ratchet (law 12). Measures the tree, then:
  - SIZE.md's `now` column must equal the measurement (`--write` rewrites it);
  - a measured value above its ceiling is red;
  - a value above the parent commit's `now` needs a line `SIZE: <metric>: <why>` in the commit
    message; a raised ceiling needs `SIZE-CEILING: <metric>: <why>`.
Metrics this script cannot measure come from executables in gates/metrics/, each printing
`<metric>\t<integer>` lines; a SIZE.md row nobody measures shows `unmeasured`, which is red
and a row with a ceiling that nothing measures is printed as `WARN unmeasured`, which
scripts/standing.sh turns into an INCOMPLETE verdict (a ceiling over nothing checks nothing).
"""
import argparse
import os
import re
import subprocess
import sys

import tree

HOST_EXE = "nanodregg-host"


# A file Emit/Rust.lean wrote starts with this line (CODEC's header), and is registered in
# gates/generated.tsv, whose rows `lake exe emit-rust --check` gates. The client/src ceiling bounds
# hand-written Rust (CLIENT-1, ROOT 10-16), so it excludes generated files; `Rust lines (generated)`
# keeps their growth visible. Only a REGISTERED file with the header counts as generated: a
# hand-written file that copies the header is counted as hand-written AND shows in the ceiling-0 row
# `Rust files with an unregistered generated header`.
GENERATED = re.compile(r"^// @generated .* by Emit/Rust\.lean\. DO NOT EDIT\.$")


def registered(root: str) -> set[str]:
    p = os.path.join(root, "gates", "generated.tsv")
    if not os.path.isfile(p):
        return set()
    rows = (l.split("\t") for l in open(p, encoding="utf-8") if l.strip() and not l.startswith("#"))
    return {os.path.normpath(r[1].strip()) for r in rows if len(r) > 1}


def rust_files(root: str, sub: str = ""):
    """(path relative to root, line count, has the generated header) for each .rs under root/sub."""
    for d, dirs, files in os.walk(os.path.join(root, sub)):
        dirs[:] = [x for x in dirs if x not in tree.SKIP_DIRS]
        for f in files:
            if f.endswith(".rs"):
                path = os.path.join(d, f)
                with open(path, encoding="utf-8", errors="replace") as fh:
                    lines = fh.readlines()
                header = bool(lines) and bool(GENERATED.match(lines[0].rstrip("\n")))
                yield os.path.normpath(os.path.relpath(path, root)), len(lines), header


def rust_lines(root: str) -> int:
    return sum(n for _, n, _ in rust_files(root))


# Constructor-count metrics (ROOT ruling 2026-10-16: PROTOCOL's rows are computed, never hand
# rows): metric -> [(module prefix, inductive name)]; a missing module counts 0.
CONSTRUCTORS = {
    "protocol operations": [("Protocol.Table", "Op")],
    "call kinds (Receive.Body constructors)": [("Kernel.Receive", "Body")],
    "command verbs (the one command language)": [("Protocol.Command", "Verb")],
    "refusal constructors": [("Kernel.World", "Reject"), ("Kernel.Receive", "Refusal")],
}


def constructors(t: tree.Tree, prefix: str, name: str) -> int:
    n = 0
    for m in t.modules.values():
        if m.is_proof or not (m.name == prefix or m.name.startswith(prefix + ".")):
            continue
        for hit in re.finditer(r"(?m)^[ \t]*(?:(?:private|protected)[ \t]+)?inductive[ \t]+" + re.escape(name) + r"\b", m.code):
            body = []
            for line in m.code[hit.end():].split("\n")[1:]:
                if line and not line[0].isspace() or re.match(r"\s*deriving\b", line):
                    break
                body.append(line)
            n += sum(len(re.findall(r"(?:^|\s)\|\s*[\w«]", l)) for l in body)
    return n


def measure(t: tree.Tree) -> dict[str, int]:
    mods = t.modules.values()
    out = {}
    host = t.exes.get(HOST_EXE)
    out["Lean modules in the Host closure"] = len(t.closure([host])) if host else 0
    out["Lean modules"] = len(t.modules)
    out["Lean proof-modules"] = sum(1 for m in mods if m.is_proof)
    for lib in sorted(set(m.lib for m in mods)):
        out[f"Lean lines ({lib})"] = sum(m.lines for m in mods if m.lib == lib)
    out["Lean lines (deployed)"] = sum(m.lines for m in mods if not m.is_proof)
    deps = t.dependents()
    out["max dependents of one module"] = max((len(v) for v in deps.values()), default=0)
    out["theorems"] = sum(1 for m in mods for d in m.decls if d.kind in tree.THEOREM_KINDS)
    out["partial defs (deployed)"] = sum(1 for m in mods for d in m.decls if d.partial)
    out["sorry"] = sum(len(re.findall(r"\bsorry\b", m.code)) for m in mods)
    out["native (extern/implemented_by)"] = sum(
        len(re.findall(r"@\[[^\]]*\b(?:implemented_by|extern)\b", m.code)) for m in mods)
    out["C lines"] = sum(
        sum(1 for _ in open(os.path.join(d, f), encoding="utf-8", errors="replace"))
        for d, dirs, files in os.walk(t.root) if not (set(d.split(os.sep)) & tree.SKIP_DIRS)
        for f in files if f.endswith((".c", ".h")))
    out["Rust lines"] = rust_lines(t.root)
    gen = registered(t.root)
    rs = list(rust_files(t.root))
    out["Rust lines (client/src)"] = sum(
        n for p, n, h in rs if p.startswith("client" + os.sep + "src" + os.sep) and not (h and p in gen))
    out["Rust lines (generated)"] = sum(n for p, n, h in rs if h and p in gen)
    out["Rust files with an unregistered generated header"] = sum(
        1 for p, _, h in rs if h and p not in gen)
    for metric, sources in CONSTRUCTORS.items():
        out[metric] = sum(constructors(t, p, n) for p, n in sources)
    mdir = os.path.join(t.root, "gates", "metrics")
    if os.path.isdir(mdir):
        for f in sorted(os.listdir(mdir)):
            p = os.path.join(mdir, f)
            if os.access(p, os.X_OK) and os.path.isfile(p):
                r = subprocess.run([p, t.root], capture_output=True, text=True, timeout=120)
                if r.returncode != 0:
                    raise SystemExit(f"size: gates/metrics/{f} failed: {r.stderr.strip()}")
                for line in r.stdout.splitlines():
                    k, v = line.split("\t")
                    out[k] = int(v)
    return out


ROW = re.compile(r"^\|\s*([^|]+?)\s*\|\s*([^|]*?)\s*\|\s*([^|]*?)\s*\|\s*$")


def parse_raw(text: str) -> dict[str, tuple[str, str]]:
    rows = {}
    for line in text.splitlines():
        m = ROW.match(line)
        if m and m.group(1) != "metric" and not set(m.group(1)) <= set("-: "):
            rows[m.group(1)] = (m.group(2), m.group(3))
    return rows


def parse(text: str):
    """SIZE.md rows: metric -> (now, ceiling); an int, or None when the cell is not a plain number
    (a ceiling cell may carry a note after its number: `6 (ROOT ruling)`)."""
    rows = {}
    for line in text.splitlines():
        m = ROW.match(line)
        if not m or m.group(1) in ("metric",) or set(m.group(1)) <= set("-: "):
            continue
        def num(s):
            return int(s.replace(",", "")) if re.fullmatch(r"[\d,]+", s) else None

        def lead(s):
            g = re.match(r"([\d,]+)(\s|$)", s)
            return int(g.group(1).replace(",", "")) if g else None
        rows[m.group(1)] = (num(m.group(2)), lead(m.group(3)))
    return rows


def render(head: str, measured: dict[str, int], raw: dict) -> str:
    """Rewrite `now` for every measured metric; a row this script does not measure is kept
    exactly as written (now and ceiling), never dropped or blanked."""
    keys = list(raw) + [k for k in measured if k not in raw]
    lines = [head.rstrip("\n"), "", "| metric | now | ceiling |", "|---|---|---|"]
    for k in keys:
        now_raw, ceil_raw = raw.get(k, ("", "—"))
        now = str(measured[k]) if k in measured else now_raw
        lines.append(f"| {k} | {now} | {ceil_raw or '—'} |")
    return "\n".join(lines) + "\n"


HEAD = ("# SIZE — the ratchet (law 12)\n\n"
        "`now` is written by `python3 gates/size.py . --write` and checked by every commit. A rise needs\n"
        "`SIZE: <metric>: <why>` in the commit message; a raised ceiling needs `SIZE-CEILING: <metric>: <why>`.")


WARN: list[str] = []


def check(t, size_text, base_text, message, base_tree=None) -> list[str]:
    """A rise is judged against the PARENT TREE's measurement when given (the parent's SIZE.md
    may itself be stale), else against the parent's SIZE.md `now`."""
    measured = measure(t)
    rows = parse(size_text)
    base = parse(base_text) if base_text is not None else {}
    if base_tree is not None:
        bm = measure(base_tree)
        base = {k: (bm.get(k), base.get(k, (None, None))[1]) for k in set(base) | set(bm)}
    red = []
    for k, v in measured.items():
        if k not in rows:
            red.append(f"SIZE.md has no row for measured metric '{k}' (= {v}); run gates/size.py --write")
        elif rows[k][0] != v:
            red.append(f"SIZE.md stale: '{k}' says {rows[k][0]}, tree measures {v}; run gates/size.py --write")
    for k, (now, ceil) in rows.items():
        v = measured.get(k)
        if v is None:
            if ceil is not None and k not in measured:
                WARN.append(f"'{k}' has ceiling {ceil} but nothing measures it (add gates/metrics/<x>)")
            continue
        if ceil is not None and v > ceil:
            red.append(f"'{k}' = {v} exceeds its ceiling {ceil}")
        b_now, b_ceil = base.get(k, (None, None))
        if b_now is not None and v > b_now and not re.search(r"(?m)^SIZE:\s*" + re.escape(k) + r"\s*:\s*\S", message):
            red.append(f"'{k}' rose {b_now} -> {v}: the commit message needs 'SIZE: {k}: <why>'")
        if b_ceil is not None and (ceil is None or ceil > b_ceil) and not re.search(
                r"(?m)^SIZE-CEILING:\s*" + re.escape(k) + r"\s*:\s*\S", message):
            red.append(f"'{k}' ceiling raised {b_ceil} -> {ceil}: needs 'SIZE-CEILING: {k}: <why>'")
    for k in base:
        if k not in rows and k in parse(base_text or ""):
            red.append(f"SIZE.md dropped row '{k}'; rows are never removed silently "
                       f"(a removed metric needs 'SIZE-CEILING: {k}: <why>')"
                       if not re.search(r"(?m)^SIZE-CEILING:\s*" + re.escape(k) + r"\s*:", message) else "")
    return [r for r in red if r]


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("root", nargs="?", default=".")
    ap.add_argument("--base", help="SIZE.md of the parent commit")
    ap.add_argument("--message", help="commit message file")
    ap.add_argument("--write", action="store_true")
    a = ap.parse_args()
    t = tree.read(a.root)
    path = os.path.join(t.root, "SIZE.md")
    text = open(path, encoding="utf-8").read() if os.path.exists(path) else ""
    if a.write:
        open(path, "w", encoding="utf-8").write(render(HEAD, measure(t), parse_raw(text)))
        print("size: SIZE.md written")
        sys.exit(0)
    base = open(a.base, encoding="utf-8").read() if a.base else None
    msg = open(a.message, encoding="utf-8").read() if a.message else ""
    red = check(t, text, base, msg)
    for r in red:
        print(r)
    for w in WARN:
        print("WARN unmeasured:", w)
    print(f"size: {'RED' if red else 'ok'} ({len(red)})")
    sys.exit(1 if red else 0)
