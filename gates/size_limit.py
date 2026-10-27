"""gates/size_limit.py [ROOT] — the charter's artifact law (CHARTER.md, "Build on the Mac"): "no
large artifacts, no fixtures over 1 MB". Nothing enforced it and an 11,961,094-byte
gates/certificate-grant.json.gz landed unnoticed. A file above LIMIT is red by name (exactly
1048576 bytes is fine), unless a row of gates/size-allow.tsv (path<TAB>bytes-ceiling<TAB>reason)
holds it under its ceiling; a malformed or stale allow row is red itself. It imports no sibling
module: it must run under `python3 -I`, where the script directory is off sys.path."""
import argparse
import os
import stat
import subprocess
import sys

LIMIT = 1_048_576
SKIP_DIRS = {".lake", ".git", "target", "node_modules"}
TABLE = os.path.join("gates", "size-allow.tsv")


def tracked_names(root: str) -> list[str] | None:
    """The tracked files of ROOT, or None when ROOT has no record of what is tracked. A git checkout
    lists `git ls-files`. An exported tree (scripts/gate-lib.sh materialize: `read-tree -u` into DIR with
    its index at DIR.index, inside some repo's git dir) lists that index: the export also holds untracked
    build products (testground/kernel.wasm, gitignored), which are not the tree being judged."""
    env = dict(os.environ)
    cmd = ["git", "-C", root, "ls-files", "-z"]
    if not os.path.exists(os.path.join(root, ".git")):
        index = root.rstrip(os.sep) + ".index"
        gitdir, d = None, os.path.dirname(os.path.abspath(root))
        while gitdir is None and d != os.path.dirname(d):
            if os.path.basename(d) == ".git" and os.path.isdir(d):
                gitdir = d
            d = os.path.dirname(d)
        if not os.path.exists(index) or gitdir is None:
            return None
        env.update(GIT_DIR=gitdir, GIT_WORK_TREE=os.path.abspath(root), GIT_INDEX_FILE=index)
        cmd = ["git", "ls-files", "-z"]
    r = subprocess.run(cmd, capture_output=True, env=env, cwd=root)
    if r.returncode != 0:
        raise RuntimeError(f"git ls-files: {r.stderr.decode(errors='replace').strip()}")
    return [os.fsdecode(x) for x in r.stdout.split(b"\0") if x]


def listing(root: str) -> dict[str, int]:
    """Every tracked file of ROOT, name -> size on disk (tracked_names). A tree with no record of what
    is tracked (a bare directory, as the plants build) is walked outside SKIP_DIRS. Symlinks and
    non-regular files are skipped, as is a tracked path deleted from the worktree."""
    names = tracked_names(root)
    if names is None:
        names = []
        for d, dirs, files in os.walk(root):
            dirs[:] = [x for x in dirs if x not in SKIP_DIRS]
            names += [os.path.relpath(os.path.join(d, f), root) for f in files]
    out: dict[str, int] = {}
    for name in names:
        try:
            st = os.lstat(os.path.join(root, name))
        except FileNotFoundError:
            continue
        if stat.S_ISREG(st.st_mode):
            out[name] = st.st_size
    return out


def read_allow(root: str) -> tuple[dict[str, int], list[tuple[int, str]], list[str]]:
    """gates/size-allow.tsv: (path -> ceiling, rows in file order, reds for malformed rows)."""
    allow, rows, red = {}, [], []
    if not os.path.exists(os.path.join(root, TABLE)):
        return allow, rows, red
    seen: set[str] = set()
    for n, line in enumerate(open(os.path.join(root, TABLE), encoding="utf-8"), 1):
        if not line.strip() or line.startswith("#"):
            continue
        f = line.rstrip("\n").split("\t")
        what: str | None = None
        ceiling = -1
        if len(f) != 3:
            what = f"{len(f)} tab-separated fields, need path<TAB>bytes-ceiling<TAB>reason"
        else:
            try:
                ceiling = int(f[1])
            except ValueError:
                what = f"ceiling {f[1]!r} is not an integer"
        if what is None and ceiling <= LIMIT:
            what = f"ceiling {ceiling} is not above the {LIMIT}-byte limit"
        if what is None and not f[2].strip():
            what = "reason is empty"
        if what is None and f[0] in seen:
            what = f"second row for {f[0]}"
        if what is not None:
            red.append(f"{TABLE}:{n}: {what}")
        else:
            seen.add(f[0])
            allow[f[0]] = ceiling
            rows.append((n, f[0]))
    return allow, rows, red


def check(root: str) -> list[str]:
    sizes = listing(root)
    allow, rows, red = read_allow(root)
    for path, size in sizes.items():
        if size > LIMIT:
            if path in allow:
                if size > allow[path]:
                    red.append(f"{path}: {size} bytes exceeds its allowlist ceiling {allow[path]} ({TABLE})")
            else:
                red.append(f"{path}: {size} bytes exceeds the {LIMIT}-byte limit "
                           f"(CHARTER.md: no fixtures over 1 MB)")
    red += [f"{TABLE}:{n}: {path} no longer needs its allow row"
            for n, path in rows if path not in sizes or sizes[path] <= LIMIT]
    return sorted(red)


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("root", nargs="?", default=os.path.realpath(
        os.path.join(os.path.dirname(os.path.abspath(__file__)), os.pardir)))
    red = check(ap.parse_args().root)
    for r in red:
        print(r)
    print(f"size_limit: {'RED (' + str(len(red)) + ')' if red else 'ok'}")
    return 1 if red else 0


if __name__ == "__main__":
    sys.exit(main())
