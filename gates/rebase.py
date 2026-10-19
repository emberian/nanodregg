"""gates/rebase.py — what scripts/commit does with a lander's paths when main has moved under them (GATES-19).

  rebase.py merge --repo DIR --head REV --main REV [--bases FILE] -- PATH...

PATH... are the files the lander named whose copy at REV --head (the worktree's HEAD) differs from
main's. Before GATES-19 each was refused (`worktree behind main on F`) and re-applied by hand: 19
such round trips in 36 h, most on gates/runs.tsv, waste.tsv, the lakefile and decisions/*.md, with
the two edits on different lines. Now each is a 3-way merge (`git merge-file`): base = the copy
the lander edited (HEAD's, or the main copy a previous merge of this lander took, from --bases),
ours = the worktree file, theirs = main's copy. Every file merges cleanly or nothing is written:
a conflict is refused by name with its hunks, never resolved by the tool. A clean result is
written into the worktree file (the candidate is built from the worktree, and a worktree left
holding the pre-merge copy would revert main's change at the lander's next commit: 051a8cc), and
the RESULT is what the judge judges (ROOT ruling 10-19). A file absent on any side (deleted or
added) or one git cannot merge (binary) is refused, never guessed. Exit 0 = all merged (or
nothing to do), 1 = refused, 2 = a tool failure (also a refusal).

--bases FILE records `path<TAB>theirs-blob<TAB>result-blob` per merged file, for the lander's next
attempt: when main moves again and the worktree file is still exactly the result, the next merge's
base is the main copy this one took (B0's), not HEAD's, so the lander's own edit is the only thing
"ours" adds.

  rebase.py keys --listing FILE --tree DIR --table RUNS.TSV
  rebase.py verify --listing FILE --tree DIR --table RUNS.TSV --record FILE [--reuse FILE] [--skip-runs]
  rebase.py check TREE

INPUT KEYS. A judged unit's verdict may be carried from the lander's previous judge to its re-based
candidate only when the unit's input key is byte-identical (ROOT 10-19; design §2c). A key is a
SHA-256 over what the unit can read, over-approximated where that is not known:
- `run:EXE` (a gates/runs.tsv verdict row, its control with it): the row's text, the NAMES of the
  `.lean` and DOC_ALLOW paths (a tree walk lists them: GATES-8), every other tree path's bytes (data the run may open: world/, deploy/, gates/*.tsv,
  the runner, the scripts, the Rust tree, lean-toolchain, the lakefile), the bytes of EVERY executable
  in the built bin directory, and the Python and rustc versions. Every binary, not the exe's own: a
  verdict exe may drive any other (the rows exe runs `lake exe NAME` for its rows; store-plants runs
  {host}), and a set narrower than what a run executes would be a false reuse. Binary bytes, not the
  import closure: a rebuild that is not byte-reproducible costs a re-run, never a false reuse.
- `census`: every tree path outside DOC_ALLOW (all .lean among them).
- `cargo-check`, `clippy`, `fmt`: every non-.lean path outside DOC_ALLOW and the rustc version.
The .lean sources stand outside the run keys only because the binaries built from them are inside;
SIZE.md (DERIVED) because it is a function of the paths that are.
`keys` prints `unit<TAB>key` for every unit; `verify` re-computes every key of a judge's RECORD on the
tree as it is now and refuses `stale verdict: UNIT` when one differs, or when a unit claimed as reused
has no ok verdict under that exact key in the previous judge's record (--reuse). The record is
`unit<TAB>key<TAB>run|reused<TAB>payload` and holds ok units only: a red, INCOMPLETE, UNREAD, KILLED
or ABSENT unit is never carried. `check` is the gate that DOC_ALLOW holds: no tree file outside it
names a path under it in a string literal (a run that opened one would read an input no key covers).
"""
import argparse
import hashlib
import json
import re
import os
import subprocess
import sys
import tempfile


def git(repo: str, *args: str, inp: bytes | None = None, check: bool = True) -> subprocess.CompletedProcess:
    return subprocess.run(["git", "-C", repo, *args], input=inp, capture_output=True, check=check)


def blob(repo: str, rev: str, path: str) -> str | None:
    r = git(repo, "rev-parse", "-q", "--verify", f"{rev}:{path}", check=False)
    return r.stdout.decode().strip() if r.returncode == 0 else None


def show(repo: str, oid: str) -> bytes:
    return git(repo, "cat-file", "blob", oid).stdout


def hunks(text: bytes, limit: int = 40) -> list[str]:
    out, inside = [], False
    for line in text.decode(errors="replace").splitlines():
        if line.startswith("<<<<<<< "):
            inside = True
        if inside:
            out.append("    " + line)
        if line.startswith(">>>>>>> "):
            inside = False
    return out[:limit] + (["    …"] if len(out) > limit else [])


def merge(repo: str, head: str, main: str, bases_file: str | None, paths: list[str]) -> int:
    bases: dict[str, tuple[str, str]] = {}
    if bases_file and os.path.isfile(bases_file):
        for line in open(bases_file, encoding="utf-8"):
            f = line.rstrip("\n").split("\t")
            if len(f) == 3:
                bases[f[0]] = (f[1], f[2])
    refused: list[str] = []
    results: list[tuple[str, bytes, str, str]] = []   # path, merged bytes, theirs blob, how
    for p in paths:
        wt = os.path.join(repo, p)
        ours = open(wt, "rb").read() if os.path.isfile(wt) else None
        ours_oid = git(repo, "hash-object", "--stdin", inp=ours).stdout.decode().strip() if ours is not None else None
        theirs_oid = blob(repo, main, p)
        base_oid, how = blob(repo, head, p), "base = this worktree's HEAD"
        if p in bases and ours_oid == bases[p][1]:
            base_oid, how = bases[p][0], "base = the main copy this lander's previous merge took"
        if ours_oid == theirs_oid:
            continue   # both sides hold the same bytes (or both deleted it)
        if ours is None or theirs_oid is None or base_oid is None:
            side = ("deleted in your worktree" if ours is None else "deleted on main" if theirs_oid is None
                    else "added on both sides")
            refused.append(f"scripts/commit: REFUSED — cannot merge {p}: {side}, and the other side holds different "
                           f"bytes; re-apply your edit on main's copy (git show main:{p})")
            continue
        theirs = show(repo, theirs_oid)
        if ours_oid == base_oid:
            results.append((p, theirs, theirs_oid, how + "; you had not edited it: main's copy taken"))
            continue
        with tempfile.TemporaryDirectory() as d:
            fo, fb, ft = (os.path.join(d, x) for x in ("ours", "base", "theirs"))
            open(fo, "wb").write(ours)
            open(fb, "wb").write(show(repo, base_oid))
            open(ft, "wb").write(theirs)
            r = subprocess.run(["git", "merge-file", "-p", "-L", "yours", "-L", "base", "-L", "main", fo, fb, ft],
                               capture_output=True)
        if r.returncode == 0:
            results.append((p, r.stdout, theirs_oid, how))
        elif 0 < r.returncode < 128:
            refused.append(f"scripts/commit: REFUSED — merge conflict in {p} ({r.returncode} hunk(s); {how}); your edit "
                           f"and main's overlap. Re-apply your edit on main's copy (git show main:{p}). The hunks:")
            refused += hunks(r.stdout)
        else:
            refused.append(f"scripts/commit: REFUSED — cannot merge {p}: git merge-file: "
                           f"{r.stderr.decode(errors='replace').strip() or f'exit {r.returncode}'}")
    if refused:
        print("\n".join(refused))
        print("scripts/commit: nothing was written to your worktree")
        return 1
    rows = []
    for p, data, theirs_oid, how in results:
        wt = os.path.join(repo, p)
        mode = os.stat(wt).st_mode
        with open(wt, "wb") as fh:
            fh.write(data)
        os.chmod(wt, mode)
        res = git(repo, "hash-object", "--stdin", inp=data).stdout.decode().strip()
        rows.append(f"{p}\t{theirs_oid}\t{res}\n")
        print(f"scripts/commit: merged main's change to {p} into your copy (3-way, {how}); the merged file is judged")
    if bases_file and rows:
        with open(bases_file, "a", encoding="utf-8") as fh:
            fh.writelines(rows)
    return 0


def doc_allow() -> tuple[str, ...]:
    """gates/doc-allow.tsv beside this file: one path prefix per line, the paths no unit reads at run
    time. Data, not a literal here, so this file passes its own `check`."""
    p = os.path.join(os.path.dirname(os.path.abspath(__file__)), "doc-allow.tsv")
    return tuple(l.strip() for l in open(p, encoding="utf-8") if l.strip() and not l.startswith("#"))


DOC_ALLOW = doc_allow()
# A derived file is a function of the tree's other paths: in any candidate check.py passes, SIZE.md is
# exactly what gates/size.py writes from them (`SIZE.md is not the generated view` otherwise), so a key
# over the rest already determines it. It is outside every key; every landing changes it.
DERIVED = ("SIZE.md",)
KEY_VERSION = b"GATES-19 input key v2 (GATES-8: names of doc and .lean paths)"


def listing(path: str) -> list[tuple[str, str, str]]:
    """`git ls-tree -r -z --full-tree TREE` output: (mode, oid, path) per blob."""
    out = []
    for rec in open(path, "rb").read().split(b"\0"):
        if rec:
            meta, p = rec.decode().split("\t", 1)
            mode, _typ, oid = meta.split()
            out.append((mode, oid, p))
    return out


def digest(*parts: str | bytes) -> str:
    h = hashlib.sha256(KEY_VERSION)
    for x in parts:
        b = x if isinstance(x, bytes) else x.encode()
        h.update(len(b).to_bytes(8, "big"))
        h.update(b)
    return h.hexdigest()


def paths_digest(ls: list[tuple[str, str, str]], lean: bool) -> str:
    """Every path's mode, blob and name, except: a DOC_ALLOW path, and (lean=False) a .lean source, by
    NAME and mode only. A tree walk sees names without reading contents (cargo:devtools:workspace stats
    every entry under the root, decisions/ included: GATES-8's trace), so an add or a remove re-keys
    while a prose edit still reuses. SIZE.md (DERIVED) not at all."""
    keep = sorted(f"{m} name {p}" if p.startswith(DOC_ALLOW) or (not lean and p.endswith(".lean")) else f"{m} {o} {p}"
                  for m, o, p in ls if p not in DERIVED)
    return digest("\n".join(keep))


def bins_digest(bindir: str) -> str:
    rows = []
    if os.path.isdir(bindir):
        for n in sorted(os.listdir(bindir)):
            p = os.path.join(bindir, n)
            if os.path.isfile(p) and os.access(p, os.X_OK):
                rows.append(n + " " + hashlib.sha256(open(p, "rb").read()).hexdigest())
    return digest("\n".join(rows))


def tool(argv: list[str]) -> str:
    try:
        r = subprocess.run(argv, capture_output=True, text=True)
        return f"{argv[0]} exit {r.returncode}: {r.stdout.strip()}"
    except OSError as e:
        return f"{argv[0]}: {e}"


def compute(listing_file: str, root: str, table: str) -> dict[str, str]:
    ls = listing(listing_file)
    src, full = paths_digest(ls, False), paths_digest(ls, True)
    rust = tool(["rustc", "-Vv"])
    bins = bins_digest(os.path.join(root, ".lake", "build", "bin"))
    keys = {"census": digest("census", full),
            **{u: digest(u, src, rust) for u in ("cargo-check", "clippy", "fmt")}}
    for line in open(table, encoding="utf-8"):
        f = line.rstrip("\n").split("\t")
        if line.startswith("#") or len(f) != 4 or f[1].strip() == "-":
            continue
        keys["run:" + f[0]] = digest("run", line.rstrip("\n"), src, bins, sys.version, rust)
    return keys


def read_record(path: str | None) -> dict[str, tuple[str, str, str]]:
    out = {}
    if path and os.path.isfile(path):
        for line in open(path, encoding="utf-8"):
            f = line.rstrip("\n").split("\t", 3)
            if len(f) == 4:
                out[f[0]] = (f[1], f[2], f[3])
    return out


def verify(listing_file: str, root: str, table: str, record: str, reuse: str | None, skip_runs: bool) -> int:
    now = compute(listing_file, root, table)
    prev = read_record(reuse)
    rec = read_record(record)
    if not os.path.isfile(record):
        print(f"stale verdict: no record {record} to verify")
        return 1
    bad = []
    for unit, (key, how, _payload) in sorted(rec.items()):
        if skip_runs and unit.startswith("run:"):
            continue
        if now.get(unit) != key:
            bad.append(f"stale verdict: {unit} (recorded key {key[:16]}, the candidate's key now "
                       f"{(now.get(unit) or 'none')[:16]})")
        elif how == "reused" and prev.get(unit, ("",))[0] != key:
            bad.append(f"stale verdict: {unit} (claimed reused, but the previous judge's record holds no ok verdict "
                       f"under key {key[:16]})")
        elif how not in ("run", "reused"):
            bad.append(f"stale verdict: {unit} (record says {how!r})")
    print("\n".join(bad) if bad else f"verify: ok ({len(rec)} units, every key re-computed on the candidate)")
    return 1 if bad else 0


_ALT = "|".join(re.escape(d) for d in DOC_ALLOW)
DQ = re.compile(r"\"[^\"\n]*(?<![A-Za-z0-9_])(" + _ALT + r")[^\"\n]*\"")
SQ = re.compile(r"'[^'\n]*(?<![A-Za-z0-9_])(" + _ALT + r")[^'\n]*'")


def check(root: str) -> list[str]:
    """DOC_ALLOW holds: no file outside it names a path under it in a string literal: "…" in any file, and
    '…' in a script (*.py, *.sh, or a #! first line), where single quotes make strings; in Lean, Rust and
    prose a single quote is a character or an apostrophe."""
    import tree
    red = []
    for d, dirs, files in os.walk(root):
        dirs[:] = [x for x in dirs if x not in tree.SKIP_DIRS]
        rel = os.path.relpath(d, root)
        if rel != "." and (rel + "/").startswith(DOC_ALLOW):
            dirs[:] = []
            continue
        for f in files:
            p = os.path.join(d, f)
            try:
                text = open(p, encoding="utf-8").read()
            except (UnicodeDecodeError, OSError):
                continue
            script = f.endswith((".py", ".sh")) or text.startswith("#!")
            for n, line in enumerate(text.splitlines(), 1):
                m = DQ.search(line) or (script and SQ.search(line))
                if m:
                    red.append(f"{os.path.relpath(p, root)}:{n}: names {m.group(0)[:60]}, under the doc allow-list "
                               f"{', '.join(DOC_ALLOW)} that no input key covers (gates/rebase.py)")
    return red


def main() -> int:
    ap = argparse.ArgumentParser()
    sub = ap.add_subparsers(dest="cmd", required=True)
    m = sub.add_parser("merge")
    m.add_argument("--repo", required=True)
    m.add_argument("--head", required=True)
    m.add_argument("--main", required=True)
    m.add_argument("--bases")
    m.add_argument("paths", nargs="*")
    for name in ("keys", "verify"):
        k = sub.add_parser(name)
        k.add_argument("--listing", required=True)
        k.add_argument("--tree", required=True)
        k.add_argument("--table", required=True)
        if name == "verify":
            k.add_argument("--record", required=True)
            k.add_argument("--reuse")
            k.add_argument("--skip-runs", action="store_true")
    c = sub.add_parser("check")
    c.add_argument("root")
    a = ap.parse_args()
    if a.cmd == "keys":
        for u, k in sorted(compute(a.listing, a.tree, a.table).items()):
            print(f"{u}\t{k}")
        return 0
    if a.cmd == "verify":
        return verify(a.listing, a.tree, a.table, a.record, a.reuse, a.skip_runs)
    if a.cmd == "check":
        sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
        red = check(a.root)
        print("\n".join(red) if red else "rebase: ok")
        return 1 if red else 0
    try:
        return merge(a.repo, a.head, a.main, a.bases, a.paths)
    except (OSError, subprocess.CalledProcessError) as e:
        print(f"scripts/commit: REFUSED — the merge could not run: {e}")
        return 2


if __name__ == "__main__":
    sys.exit(main())
