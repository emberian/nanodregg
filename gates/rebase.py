"""gates/rebase.py — what scripts/commit lands of a lander's paths, and the input keys of its judge
(GATES-19; the landed copy GATES-20b).

  rebase.py snapshot  --repo DIR --out FILE -- PATH...
  rebase.py candidate --repo DIR --snapshot FILE --main REV
  rebase.py stale     --repo DIR --snapshot FILE --main REV --message FILE [--reverts C]...
  rebase.py writeback --repo DIR --snapshot FILE --landed REV

THE LANDED COPY (GATES-20b, ROOT 10-21). A lander's copy of a path is never taken as the working
tree holds it. `snapshot`, once per lander (its first attempt), records for every file under
PATH... the BASE (the blob at the worktree's HEAD then) and OURS (the working copy, written to the
object store), `path<TAB>base<TAB>ours<TAB>mode` with `-` for absent. Every attempt's candidate is
built from that record by `candidate`, into the attempt's private index, file by file against
main's blob M: OURS = M, or OURS = BASE (the lander did not edit it: main's copy wins), or BASE = M
(main did not change it: OURS), else the 3-way merge `git merge-file OURS BASE M`. A conflict, or
a side absent or unmergeable, is refused by name with its hunks, never resolved. One exception (GATES-22 (b)): an
append-only file (gates/append-only.tsv: the decision records) that the lander only APPENDED to since its base lands as
main's copy, whatever main changed in it, with the lander's addition after it; a lander's edit above the end is merged as
any file. The working tree is
not read again: an edit made while the lander runs is not in what it lands, and is named at the end.

Before GATES-20b the merge ran only for a path whose HEAD copy differed from main's, with HEAD's copy
as the base, and the candidate was then `git add -A` of the working copy. A working copy that was
not made on top of HEAD (a scratch copy copied in, a `git reset` that moved HEAD and left the file,
a rewrite between attempts) was landed WHOLE: hbox logs/gates9-verify.sh, launcher/tests/members.rs
from a1ca640 plus one line in a worktree at main, candidate `81 +++----`, CLIENT-31's 70 lines gone.

`stale` catches what no recorded base can see: a base that is itself wrong (HEAD moved before the
launch, a copy made from an older main). It runs on the FINAL candidate, after the merge, so a merge
that lost a hunk is caught too. For every path the candidate changes, and every commit C of main's
last REVERT_WINDOW first-parent commits that changed it: C's change is CONTAINED in a copy X when
merging C's own change into X (`git merge-file X pre_C post_C`) is clean and leaves X as it is, or when
X holds C's change whatever its context (holds): every block of lines C added is in X, contiguous, and
every block C removed is not; it is LACKING when that merge is clean, changes X, and X does not hold
C's change. The second test is GATES-20b' (ROOT 10-21, PERF-6's false positive): 35daeab added the
bench-worstworld block using the bench-worstcut lines as CONTEXT; PERF-12 deleted those lines and kept
the block, so the merge, re-anchored on the surviving context, inserted the block a SECOND time and
`stale` refused a copy that reverts nothing. A merge that would only duplicate lines X already holds is
not a lack. A purely added Lean theorem is also held when its exact statement occurs once as
active code anywhere in X, even if its proof moved or changed; an absent added theorem is lacking
even when its replay conflicts on other edits (GATES-20p). Other blocks still compare whole:
a removed block X still holds, or an added one it does not, reads LACKING. A path whose candidate lacks C's change while main's
copy contains it would revert C: refused `stale path: P`, unless the lander names it with `--reverts
C`. A named revert of another layer's commit needs that layer named in a CROSS-LAYER line (reverting
another layer's change is cross-layer by definition), and its hunk is appended to the message under
`REVERTS:`, so the revert is findable later; a `--reverts C` the candidate does not revert is refused.
A merge that conflicts is neither (a later edit of C's lines is not a revert of them).

`writeback` (after the compare-and-swap) puts the landed blob into each working file that still holds
the snapshot's OURS. A file edited meanwhile keeps that edit merged 3-way onto the landed copy (base =
OURS), as an uncommitted edit; one that does not merge is left as it is and named, and the next
landing's `stale` is its check.

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
import difflib
import os
import subprocess
import sys
import tempfile

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import owners  # noqa: E402  (gates/owners.py beside this file: the layer of a reverted commit)


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


# The reach of `stale`: main's last REVERT_WINDOW first-parent commits. Measured 2026-10-21: the
# oldest live worktree base (wt/transport) sat 297 commits behind main, two days. A copy made from an
# older main than that is not caught by `stale`; its recorded base still merges it when HEAD is right.
REVERT_WINDOW = 300
ABSENT = "-"


def hash_bytes(repo: str, data: bytes, write: bool = False) -> str:
    return git(repo, "hash-object", *(["-w"] if write else []), "--stdin", inp=data).stdout.decode().strip()


def tree_entry(repo: str, rev: str, path: str) -> tuple[str, str] | None:
    """(mode, blob) of PATH at REV, or None."""
    r = git(repo, "ls-tree", "-z", "--full-tree", rev, "--", path, check=False)
    for rec in r.stdout.split(b"\0"):
        if rec:
            meta, p = rec.decode().split("\t", 1)
            mode, typ, oid = meta.split()
            if p == path and typ == "blob":
                return mode, oid
    return None


def working(repo: str, path: str) -> tuple[str, bytes] | None:
    """(mode, bytes) of the working file, or None when it is absent."""
    full = os.path.join(repo, path)
    if os.path.islink(full):
        return "120000", os.readlink(full).encode()
    if not os.path.isfile(full):
        return None
    return ("100755" if os.access(full, os.X_OK) else "100644"), open(full, "rb").read()


def files_under(repo: str, paths: list[str]) -> list[str]:
    """Every file a lander's PATH... names: at HEAD, in the index, or in the working tree (untracked,
    not ignored), as `git add -A -- PATH...` sees them."""
    spec = [f":(top,literal){p}" for p in paths]
    at_head = git(repo, "ls-tree", "-r", "-z", "--name-only", "--full-tree", "HEAD", "--", *spec, check=False).stdout
    here = git(repo, "ls-files", "-z", "-c", "-o", "--exclude-standard", "--full-name", "--", *spec, check=False).stdout
    names = {x.decode() for x in (at_head + b"\0" + here).split(b"\0") if x}
    return sorted(names)


def snapshot(repo: str, out: str, paths: list[str]) -> int:
    rows = []
    for p in files_under(repo, paths):
        b = tree_entry(repo, "HEAD", p)
        w = working(repo, p)
        ours = hash_bytes(repo, w[1], write=True) if w else ABSENT
        mode = w[0] if w else (b[0] if b else "100644")
        rows.append(f"{p}\t{b[1] if b else ABSENT}\t{ours}\t{mode}\n")
    with open(out + ".tmp", "w", encoding="utf-8") as fh:
        fh.writelines(rows)
    os.replace(out + ".tmp", out)
    print(f"scripts/commit: your copy of {len(rows)} file(s) recorded at {git(repo, 'rev-parse', '--short', 'HEAD').stdout.decode().strip()}"
          f" (base = this worktree's HEAD); every attempt lands from this record, never from the working tree")
    return 0


def read_snapshot(path: str) -> list[tuple[str, str, str, str]]:
    out = []
    for line in open(path, encoding="utf-8"):
        f = line.rstrip("\n").split("\t")
        if len(f) == 4:
            out.append((f[0], f[1], f[2], f[3]))
    return out


# The append-only files (GATES-22 (b), KERNEL-26's conflict on an append-only decision record): two appends never
# conflict. gates/append-only.tsv names the directories whose *.md files are append-only (a table, read from the
# judge's own gates/: this module names no path of the doc allow-list itself, GATES-19's rule).
def _append_only() -> tuple[str, ...]:
    p = os.path.join(os.path.dirname(os.path.abspath(__file__)), "append-only.tsv")
    try:
        return tuple(l.strip() for l in open(p, encoding="utf-8") if l.strip() and not l.startswith("#"))
    except OSError:
        return ()


APPEND_ONLY = _append_only()


def append_only(p: str) -> bool:
    return p.endswith(".md") and any(p.startswith(d) and "/" not in p[len(d):] for d in APPEND_ONLY)


def merge3(ours: bytes, base: bytes, theirs: bytes) -> tuple[int, bytes, str]:
    """`git merge-file -p OURS BASE THEIRS`: (exit, merged bytes, stderr). 0 clean, 1..127 conflicts."""
    with tempfile.TemporaryDirectory() as d:
        fo, fb, ft = (os.path.join(d, x) for x in ("ours", "base", "theirs"))
        open(fo, "wb").write(ours)
        open(fb, "wb").write(base)
        open(ft, "wb").write(theirs)
        r = subprocess.run(["git", "merge-file", "-p", "-L", "yours", "-L", "base", "-L", "main", fo, fb, ft],
                           capture_output=True)
    return r.returncode, r.stdout, r.stderr.decode(errors="replace").strip()


def candidate(repo: str, snap: str, main: str) -> int:
    """Into the caller's GIT_INDEX_FILE (main's tree already read): each recorded file's landed copy."""
    refused, updates, said = [], [], []
    for p, base, ours, mode in read_snapshot(snap):
        m = tree_entry(repo, main, p)
        moid = m[1] if m else ABSENT
        if ours == moid:
            continue
        if ours == base:
            if moid != base:
                said.append(f"scripts/commit: {p}: you had not edited it and main changed it since your base: main's copy taken")
            continue
        if base == moid:
            updates.append((p, mode, ours))
            continue
        if ABSENT in (ours, base, moid):
            side = ("deleted in your copy" if ours == ABSENT else "deleted on main" if moid == ABSENT
                    else "added on both sides")
            refused.append(f"scripts/commit: REFUSED — cannot merge {p}: {side}, and the other side holds different "
                           f"bytes; re-apply your edit on main's copy (git show main:{p})")
            continue
        if append_only(p):
            bb, ob, mb = show(repo, base), show(repo, ours), show(repo, moid)
            if ob.startswith(bb):
                # GATES-22 (b): the lander only APPENDED to an append-only file: main's copy as it is now (whatever
                # main changed, above the end or at it), then the lander's addition. A lander that edited above the
                # end is merged and refused as below.
                tail = ob[len(bb):]
                data = mb + (b"" if not mb or mb.endswith(b"\n") else b"\n") + tail
                updates.append((p, mode, hash_bytes(repo, data, write=True)))
                said.append(f"scripts/commit: {p}: you only appended since your base: your addition follows main's "
                            f"copy (append-only, GATES-22)")
                continue
        rc, data, err = merge3(show(repo, ours), show(repo, base), show(repo, moid))
        if rc == 0:
            updates.append((p, mode, hash_bytes(repo, data, write=True)))
            said.append(f"scripts/commit: merged main's change to {p} into your copy (3-way, base = your recorded base "
                        f"{base[:12]}); the merged file is judged")
        elif 0 < rc < 128:
            refused.append(f"scripts/commit: REFUSED — merge conflict in {p} ({rc} hunk(s); base = your recorded base "
                           f"{base[:12]}); your edit and main's overlap. Re-apply your edit on main's copy "
                           f"(git show main:{p}). The hunks:")
            refused += hunks(data)
        else:
            refused.append(f"scripts/commit: REFUSED — cannot merge {p}: git merge-file: {err or f'exit {rc}'}")
    if refused:
        print("\n".join(refused))
        return 1
    for p, mode, oid in updates:
        if oid == ABSENT:
            git(repo, "update-index", "--force-remove", "--", p)
        else:
            git(repo, "update-index", "--add", "--cacheinfo", f"{mode},{oid},{p}")
    if said:
        print("\n".join(said))
    return 0


def window(repo: str, main: str, path: str) -> list[str]:
    lim = git(repo, "rev-list", "--first-parent", "--max-count=1", f"--skip={REVERT_WINDOW}", main, check=False).stdout.decode().strip()
    rng = [f"{lim}..{main}"] if lim else [main]
    return git(repo, "rev-list", "--first-parent", *rng, "--", f":(top,literal){path}", check=False).stdout.decode().split()


def active_lean_statement(source: bytes, statement: bytes) -> bool:
    """The exact statement occurs once as code, not as a copy inside a Lean comment or string."""
    found = 0
    depth = 0
    line_comment = string = escaped = False
    i = 0
    while i < len(source):
        if depth == 0 and not line_comment and not string and source.startswith(statement, i):
            if (i == 0 or source[i - 1] == 10) and (i + len(statement) == len(source)
                                                    or source[i + len(statement) - 1] == 10):
                found += 1
        if line_comment:
            if source[i] == 10:
                line_comment = False
        elif string:
            if escaped:
                escaped = False
            elif source[i] == 92:
                escaped = True
            elif source[i] == 34:
                string = False
        elif source.startswith(b"/-", i):
            depth += 1
            i += 1
        elif depth and source.startswith(b"-/", i):
            depth -= 1
            i += 1
        elif not depth and source.startswith(b"--", i):
            line_comment = True
            i += 1
        elif not depth and source[i] == 34:
            string = True
        i += 1
    return found == 1


def added_theorem_statement(pre: bytes, added: bytes) -> bytes | None:
    """The exact statement of a sole new theorem in an insertion block, if identifiable."""
    declarations = list(re.finditer(rb"(?m)^theorem [A-Za-z_][A-Za-z_0-9']*\b[^\n]*"
                                    rb"(?:\n(?!theorem |lemma |def |instance |structure |inductive |"
                                    rb"namespace |end ).*)*?:= by\n", added))
    if len(declarations) != 1:
        return None
    statement = declarations[0].group()
    if re.search(rb"(?m)^(?:theorem|lemma|def|instance|structure|inductive|namespace|end)\b",
                 added[declarations[0].end():]):
        return None
    return statement if not active_lean_statement(pre, statement) else None


def retained_added_theorem(x: bytes, pre: bytes, added: bytes) -> bool:
    """A pure insertion may move/change a proof if its original theorem statement survives."""
    statement = added_theorem_statement(pre, added)
    return statement is not None and active_lean_statement(x, statement)


def missing_added_theorem(x: bytes, pre: bytes, post: bytes) -> bytes | None:
    """The missing exact statement, even where replay conflicts on unrelated edits."""
    a, b = pre.splitlines(keepends=True), post.splitlines(keepends=True)
    for op, i1, i2, j1, j2 in difflib.SequenceMatcher(None, a, b, autojunk=False).get_opcodes():
        if op == "insert":
            statement = added_theorem_statement(pre, b"".join(b[j1:j2]))
            if statement is not None and not active_lean_statement(x, statement):
                return statement
    return None


def holds(x: bytes, pre: bytes, post: bytes) -> bool:
    """X holds each changed block, or the exact active statement of a purely added theorem."""
    a, b = pre.splitlines(keepends=True), post.splitlines(keepends=True)
    hay = b"\n" + x + (b"" if x.endswith(b"\n") else b"\n")

    def has(block: list[bytes]) -> bool:
        body = b"".join(block)
        return (b"\n" + body + (b"" if body.endswith(b"\n") else b"\n")) in hay

    for op, i1, i2, j1, j2 in difflib.SequenceMatcher(None, a, b, autojunk=False).get_opcodes():
        if op == "equal":
            continue
        if j2 > j1 and not has(b[j1:j2]):
            if i2 != i1 or not retained_added_theorem(x, pre, b"".join(b[j1:j2])):
                return False
        if i2 > i1 and has(a[i1:i2]):
            return False
    return True


def lacks(x: bytes, pre: bytes, post: bytes) -> bool | None:
    """True: X lacks the change pre -> post; False: X contains it; None: neither (it conflicts)."""
    if missing_added_theorem(x, pre, post) is not None:
        return True
    rc, data, _ = merge3(x, pre, post)
    if rc != 0:
        return None
    return data != x and not holds(x, pre, post)


def layer_of(repo: str, c: str) -> str | None:
    subject = git(repo, "log", "-1", "--format=%s", c).stdout.decode()
    m = re.match(r"([a-z]+)(?:\([^)]*\))?!?:", subject)
    layers = owners.SUBJECT.get(m.group(1)) if m else None
    return sorted(layers)[0] if layers else None


def stale(repo: str, snap: str, main: str, message: str, reverts: list[str]) -> int:
    """On the final candidate (the caller's GIT_INDEX_FILE): refuse a path that would revert a commit of
    the window, unless named by --reverts; append each named revert's hunk to MESSAGE."""
    named = {git(repo, "rev-parse", "--verify", f"{r}^{{commit}}").stdout.decode().strip(): r for r in reverts}
    msg = open(message, encoding="utf-8").read()
    m = re.match(r"([a-z]+)(?:\([^)]*\))?!?:", msg.strip().splitlines()[0] if msg.strip() else "")
    mine = owners.SUBJECT.get(m.group(1), set()) if m else set()
    reasons = "\n".join(re.findall(r"(?m)^CROSS-LAYER:\s*(\S.*)$", msg))
    staged = {}
    for rec in git(repo, "ls-files", "-s", "-z").stdout.split(b"\0"):
        if rec:
            meta, p = rec.decode().split("\t", 1)
            staged[p] = meta.split()[1]
    refused, used, notes = [], set(), []
    for p in sorted({row[0] for row in read_snapshot(snap)}):
        cand = staged.get(p)
        mm = tree_entry(repo, main, p)
        if cand is None or mm is None or cand == mm[1]:
            continue
        x, mx = show(repo, cand), show(repo, mm[1])
        for c in window(repo, main, p):
            pre, post = tree_entry(repo, c + "^", p), tree_entry(repo, c, p)
            if pre is None or post is None or pre[1] == post[1]:
                continue
            bpre, bpost = show(repo, pre[1]), show(repo, post[1])
            if lacks(x, bpre, bpost) is not True or lacks(mx, bpre, bpost) is not False:
                continue
            short = git(repo, "rev-parse", "--short=12", c).stdout.decode().strip()
            subj = git(repo, "log", "-1", "--format=%s", c).stdout.decode().strip()[:90]
            replay_rc, redone, _ = merge3(x, bpre, bpost)
            missing = missing_added_theorem(x, bpre, bpost)
            if replay_rc != 0 and missing is not None:
                # The replay conflicts on unrelated edits: show the precise missing declaration,
                # not conflict markers or the first 60 lines of an unrelated whole-file diff.
                body = ["@@ added theorem statement absent from candidate @@"]
                body += ["-" + line for line in missing.decode(errors="replace").splitlines()]
            else:
                with tempfile.TemporaryDirectory() as d:
                    a, b = os.path.join(d, "a"), os.path.join(d, "b")
                    open(a, "wb").write(redone)
                    open(b, "wb").write(x)
                    diff = subprocess.run(["git", "diff", "--no-index", "--no-color", "-U1", "--src-prefix=main/",
                                           "--dst-prefix=landed/", a, b], capture_output=True).stdout.decode(errors="replace")
                body = [l for l in diff.splitlines() if not l.startswith(("diff --git", "index ", "--- ", "+++ "))][:60]
            layer = layer_of(repo, c)
            foreign = bool(layer) and layer not in mine and not owners.named(reasons, layer)
            fix = f"--reverts {short}" + (f" and name {layer} in --cross-layer (e.g. \"{layer}-N agreed: …\", or "
                                          f"\"ROOT for {layer}\")" if foreign else "")
            if c not in named:
                refused.append(f"stale path: {p}: the landing would revert {short}'s change to it ({subj}): your copy "
                               f"lacks it, and main's copy holds it. Your copy was made on an older copy than your "
                               f"recorded base: re-apply your edit on main's copy (git show main:{p}), or, when undoing "
                               f"{short} is the point, add: {fix}. The hunk it would undo:")
                refused += ["    " + l for l in body]
                continue
            used.add(c)
            if foreign:
                refused.append(f"--reverts {short}: {short} is {layer}'s ({subj}); reverting another layer's change is "
                               f"cross-layer: add {fix}")
                continue
            notes.append(f"REVERTS: {short} in {p} ({subj})")
            notes += ["    " + l for l in body]
    for c, r in named.items():
        if c not in used:
            refused.append(f"--reverts {r}: the candidate reverts no change of {r} on any path it lands (in main's "
                           f"last {REVERT_WINDOW} commits); drop the flag")
    if refused:
        print("\n".join(refused))
        return 1
    if notes:
        with open(message, "a", encoding="utf-8") as fh:
            fh.write("\n" + "\n".join(notes) + "\n")
        print("\n".join(n for n in notes if n.startswith("REVERTS:")))
    return 0


def writeback(repo: str, snap: str, landed: str) -> int:
    for p, _base, ours, _mode in read_snapshot(snap):
        w = working(repo, p)
        now = hash_bytes(repo, w[1]) if w else ABSENT
        e = tree_entry(repo, landed, p)
        full = os.path.join(repo, p)
        if now != ours:
            # Edited while the lander ran: that edit was made on the recorded copy, so it is carried onto
            # the landed copy 3-way (base = the recorded copy); where it cannot be, the file is left as it
            # is and named (it would read as an edit reverting main's change: the next `stale` refuses it).
            rc = None
            if w and e and ours != ABSENT and e[0] != "120000":
                rc, data, _ = merge3(w[1], show(repo, ours), show(repo, e[1]))
            if rc == 0:
                with open(full, "wb") as fh:
                    fh.write(data)
                print(f"scripts/commit: {p} changed in your worktree while this lander ran: that edit is not in the "
                      f"landing; it is kept, merged onto the landed copy, as an uncommitted edit")
            else:
                print(f"scripts/commit: WARNING {p} changed in your worktree while this lander ran and that edit does "
                      f"not merge onto the landed copy: the file is left as it is, NOT on top of the landing; re-apply "
                      f"your edit on the landed copy (git show HEAD:{p})")
            continue
        if e is None:
            if w:
                os.unlink(full)
            continue
        if now == e[1]:
            continue
        data = show(repo, e[1])
        if e[0] == "120000":
            if os.path.lexists(full):
                os.unlink(full)
            os.symlink(data.decode(), full)
            continue
        os.makedirs(os.path.dirname(full) or ".", exist_ok=True)
        with open(full, "wb") as fh:
            fh.write(data)
        os.chmod(full, 0o755 if e[0] == "100755" else 0o644)
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


def traced_now(unit: str, payload: str, root: str, table: str) -> str | None:
    """GATES-20: a run recorded under a TRACED key (`t:…`) is re-keyed from the read-set its payload
    carries, by this (the judge's) gates/readset.py, on the candidate as it is now."""
    sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
    import readset
    try:
        rs = json.loads(payload).get("readset")
    except ValueError:
        return None
    exe = unit[len("run:"):]
    line = next((l.rstrip("\n") for l in open(table, encoding="utf-8") if l.split("\t", 1)[0] == exe), None)
    return "t:" + readset.key(rs, root, line) if rs and line else None


def verify(listing_file: str, root: str, table: str, record: str, reuse: str | None, skip_runs: bool) -> int:
    now = compute(listing_file, root, table)
    prev = read_record(reuse)
    rec = read_record(record)
    if not os.path.isfile(record):
        print(f"stale verdict: no record {record} to verify")
        return 1
    bad = []
    for unit, (key, how, payload) in sorted(rec.items()):
        if skip_runs and unit.startswith("run:"):
            continue
        nk = traced_now(unit, payload, root, table) if key.startswith("t:") else now.get(unit)
        if nk != key:
            bad.append(f"stale verdict: {unit} (recorded key {key[:16]}, the candidate's key now "
                       f"{(nk or 'none')[:16]})")
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
    s = sub.add_parser("snapshot")
    s.add_argument("--repo", required=True)
    s.add_argument("--out", required=True)
    s.add_argument("paths", nargs="+")
    for name in ("candidate", "stale", "writeback"):
        x = sub.add_parser(name)
        x.add_argument("--repo", required=True)
        x.add_argument("--snapshot", required=True)
        if name == "writeback":
            x.add_argument("--landed", required=True)
        else:
            x.add_argument("--main", required=True)
        if name == "stale":
            x.add_argument("--message", required=True)
            x.add_argument("--reverts", action="append", default=[])
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
        if a.cmd == "snapshot":
            return snapshot(a.repo, a.out, a.paths)
        if a.cmd == "candidate":
            return candidate(a.repo, a.snapshot, a.main)
        if a.cmd == "stale":
            return stale(a.repo, a.snapshot, a.main, a.message, a.reverts)
        return writeback(a.repo, a.snapshot, a.landed)
    except (OSError, subprocess.CalledProcessError) as e:
        err = e.stderr.decode(errors="replace").strip() if isinstance(e, subprocess.CalledProcessError) and e.stderr else e
        print(f"scripts/commit: REFUSED — rebase.py {a.cmd} could not run: {err}")
        return 2


if __name__ == "__main__":
    sys.exit(main())
