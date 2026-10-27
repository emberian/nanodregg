#!/usr/bin/env python3
"""gates/reverts.py REPO COMMIT [--window N] — the hunks of recent landings that COMMIT takes back.

A hunk of a landing L is reverted by COMMIT when COMMIT's parent holds L's after-image of it and COMMIT's
tree holds L's before-image instead: `git apply --check` of that one hunk succeeds in reverse on the
parent's tree and forward on COMMIT's tree, and not the other way on either. L ranges over the last N
(default 100) non-merge commits of the parent's history, and only files COMMIT changed are looked at.

Prints one line per landing it reverts (`REVERTS <hash> <hunks>/<all> <subject> :: <files>`) and a total
line `reverts N hunks of M landings`; exits 1 when N > 0, 0 otherwise, 2 on a usage or git failure.

GATES-30: d422453 was committed from a stale copy of the tree; its diff took back every hunk of five
landings and scripts/commit replayed it cleanly, because a replay sees a diff, never whose work the diff
undoes. scripts/commit runs this on every commit it replays and refuses one that reverts, unless the
lane says it means to (`--reverts`).
"""
import os
import re
import subprocess
import sys
import tempfile


def git(repo, *args, env=None, check=True, inp=None):
    r = subprocess.run(["git", "-C", repo, *args], capture_output=True, env=env, input=inp)
    if check and r.returncode != 0:
        sys.stderr.write(r.stderr.decode(errors="replace"))
        sys.exit(2)
    return r


def hunks(patch):
    """Split one file's `git diff` into (header, [hunk…])."""
    parts = re.split(rb"(?m)^(?=@@ )", patch)
    return parts[0], parts[1:]


def main():
    args = sys.argv[1:]
    window = 100
    if "--window" in args:
        i = args.index("--window")
        window = int(args[i + 1])
        del args[i:i + 2]
    if len(args) != 2:
        sys.stderr.write(__doc__)
        sys.exit(2)
    repo, commit = args
    parent = git(repo, "rev-parse", f"{commit}^").stdout.decode().strip()
    mine = set(git(repo, "diff", "--name-only", parent, commit).stdout.decode().split("\n")) - {""}
    if not mine:
        print("reverts 0 hunks of 0 landings")
        return 0
    landings = git(repo, "rev-list", "--no-merges", f"-n{window}", parent).stdout.decode().split()
    with tempfile.TemporaryDirectory() as tmp:
        idx = {}
        for name, tree in (("parent", parent), ("commit", commit)):
            env = dict(os.environ, GIT_INDEX_FILE=os.path.join(tmp, name))
            git(repo, "read-tree", tree, env=env)
            idx[name] = env

        def applies(env, patch, reverse):
            a = ["apply", "--cached", "--check"] + (["-R"] if reverse else [])
            return git(repo, *a, env=env, check=False, inp=patch).returncode == 0

        found = []
        for L in landings:
            theirs = set(git(repo, "diff-tree", "--no-commit-id", "--name-only", "-r", L).stdout.decode().split("\n"))
            both = sorted(mine & theirs)
            if not both:
                continue
            n = total = 0
            files = []
            for f in both:
                head, hs = hunks(git(repo, "diff", "--no-renames", f"{L}^", L, "--", f).stdout)
                if b"Binary files" in head:
                    continue
                k = 0
                for h in hs:
                    total += 1
                    p = head + h
                    if (applies(idx["parent"], p, True) and not applies(idx["parent"], p, False)
                            and applies(idx["commit"], p, False) and not applies(idx["commit"], p, True)):
                        k += 1
                if k:
                    n += k
                    files.append(f"{f} ({k})")
            if n:
                subj = git(repo, "log", "-1", "--format=%s", L).stdout.decode().strip()[:80]
                found.append((L[:9], n, total, subj, files))
        for h, n, total, subj, files in found:
            print(f"REVERTS {h} {n}/{total} {subj} :: {', '.join(files)}")
        hn = sum(x[1] for x in found)
        print(f"reverts {hn} hunks of {len(found)} landings")
        return 1 if hn else 0


if __name__ == "__main__":
    sys.exit(main())
