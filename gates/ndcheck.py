"""gates/ndcheck.py — elaborate a lane's REACH against the box's one warm build of origin/main (METHOD-20261027 §3).

  ndcheck.py check --repo REPO --tree TREE --gen GEN --out OUT [--rev REV] [--jobs N] [--exes] [MODULE|FILE…]
  ndcheck.py snapshot BUILD GEN SHA          publish the warm build's outputs as a generation (scripts/warm)
  ndcheck.py leaks GEN                       exit 1 when a file of GEN changed after it was published

THE GENERATION. scripts/warm builds origin/main whole in one tree (~/nd-land/warm) and, when the build is green,
publishes GEN = ~/nd-land/.warm/gen/<sha12>: hard links to that build's `.olean` files (lib/lean), compiled module
objects (ir/*.c.o.export), static libraries (lib/*.a) and executables (bin/), and copies of the link response files
(bin/*.rsp). A hard link is safe only for a file the build replaces by rename and never rewrites in place; MEASURED
on hbox with Lean 4.30 (strace of `lean -o -i -c`): the .olean is written to `X.olean.tmp` and renamed, while the
.ilean and the .c are opened O_TRUNC and rewritten in place, so a generation links no .ilean, no .c, no lake
.trace/.hash. `leaks` is the standing check of that claim: a generation's files are never written after their
STAMP, so a file newer than it is a build output rewritten in place through the link, and the generation is
refused.

THE CHECK. The REACH is what the lane changed relative to the generation's commit W (with --rev: `git diff W REV`;
without: the worktree, committed or not, and its untracked .lean files, against W) and every importer of a changed
module (gates/tree.py reach, the rule touched.py builds by). A change of lakefile.lean, lean-toolchain or
lake-manifest.json reaches every module. W must be an ancestor of the lane's HEAD (or REV): a lane behind the warm
build is told to rebase and nothing is checked (exit 2). Each module of the reach is elaborated, in import order and
N at a time, with the exact invocation lake uses (`lean SRC -o -i -c --setup S.json`, the package's leanOptions),
where S.json's importArts map each import to the lane's own output when the import is in the reach and to the
generation's .olean otherwise; LEAN_PATH is the lane's lib then the generation's. Outputs go to OUT (lib/lean, ir,
bin), never to the generation and never to a `.lake`. Named MODULEs or FILEs restrict the check to them and the
reached modules they import. A module whose source, options and in-reach imports' outputs are unchanged since the
last check against the same generation is not elaborated again.

THE EXES. Without names (or with --exes), every lean_exe whose import closure meets the reach is compiled and
linked in OUT/bin (the reached modules' C by the toolchain's clang with lake's flags, the other modules' objects
and the static libraries taken from the generation, lake's own link flags from the generation's response file);
a change under an extern_lib's C directory rebuilds that library in OUT and relinks every exe. Every other exe is
the generation's, hard-linked into OUT/bin, so OUT/bin is a complete bin directory for the rows.

Exit 0 green; 1 red (each failed module's messages printed, its importers named as not checked); 2 refused (rebase
first, or no generation); 76 when a lean or clang was killed by a signal (the memory cap): not a verdict.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import tree as treemod  # noqa: E402

BUILD_INPUTS = ("lakefile.lean", "lean-toolchain", "lake-manifest.json")
PACKAGE = "nanodregg"


def git(repo: str, *args: str, check: bool = True) -> str:
    r = subprocess.run(["git", "-C", repo, *args], capture_output=True, text=True)
    if check and r.returncode != 0:
        raise SystemExit(f"nd-check: git {' '.join(args)}: {r.stderr.strip()}")
    return r.stdout


def sha256_file(path: str) -> str:
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for b in iter(lambda: f.read(1 << 20), b""):
            h.update(b)
    return h.hexdigest()


def options(lake: dict) -> dict:
    """The package's leanOptions (`⟨`name, value⟩, …`) as the setup file's options object."""
    out = {}
    for name, val in re.findall(r"⟨\s*`([\w.]+)\s*,\s*([^⟩]+?)\s*⟩", lake.get("options", "")):
        if val in ("true", "false"):
            out[name] = val == "true"
        elif re.fullmatch(r"\d+", val):
            out[name] = int(val)
        else:
            out[name] = val.strip('"')
    return out


def unlink(path: str) -> None:
    try:
        os.unlink(path)
    except FileNotFoundError:
        pass


def link_or_copy(src: str, dst: str) -> None:
    os.makedirs(os.path.dirname(dst), exist_ok=True)
    unlink(dst)
    try:
        os.link(src, dst)
    except OSError:
        shutil.copy2(src, dst)


# ---------------------------------------------------------------------------------------------------- generations

def snapshot(build: str, gen: str, sha: str) -> int:
    """Hard-link BUILD's rename-written outputs into GEN (a new directory), copy the response files, stamp it."""
    if os.path.exists(gen):
        print(f"nd-check: {gen} exists", file=sys.stderr)
        return 2
    tmp = gen + ".tmp"
    shutil.rmtree(tmp, ignore_errors=True)
    n = 0
    for sub, keep in (("lib/lean", (".olean",)), ("ir", (".c.o.export",))):
        src = os.path.join(build, sub)
        for d, _dirs, files in os.walk(src):
            for f in files:
                if f.endswith(keep):
                    rel = os.path.relpath(os.path.join(d, f), build)
                    os.makedirs(os.path.dirname(os.path.join(tmp, rel)), exist_ok=True)
                    os.link(os.path.join(d, f), os.path.join(tmp, rel))
                    n += 1
    libdir = os.path.join(build, "lib")
    for f in sorted(os.listdir(libdir)) if os.path.isdir(libdir) else []:
        if f.endswith(".a"):
            os.makedirs(os.path.join(tmp, "lib"), exist_ok=True)
            os.link(os.path.join(libdir, f), os.path.join(tmp, "lib", f))
            n += 1
    bindir = os.path.join(build, "bin")
    os.makedirs(os.path.join(tmp, "bin"), exist_ok=True)
    for f in sorted(os.listdir(bindir)) if os.path.isdir(bindir) else []:
        p = os.path.join(bindir, f)
        if f.endswith(".rsp"):
            shutil.copy2(p, os.path.join(tmp, "bin", f))
        elif "." not in f and os.path.isfile(p) and os.access(p, os.X_OK):
            os.link(p, os.path.join(tmp, "bin", f))
            n += 1
    with open(os.path.join(tmp, "COMMIT"), "w") as f:
        f.write(sha + "\n")
    open(os.path.join(tmp, ".lock"), "w").close()
    # the STAMP is written last: every linked file is older than it, so `leaks` can see a later in-place write
    time.sleep(0.01)
    with open(os.path.join(tmp, "STAMP"), "w") as f:
        f.write(f"{time.time():.3f}\n")
    os.rename(tmp, gen)
    print(f"nd-check: generation {os.path.basename(gen)}: {n} files linked")
    return 0


def leaks(gen: str) -> int:
    stamp = os.path.join(gen, "STAMP")
    t = os.stat(stamp).st_mtime
    bad = []
    for d, _dirs, files in os.walk(gen):
        for f in files:
            p = os.path.join(d, f)
            if f not in ("STAMP", "COMMIT", ".lock") and os.stat(p).st_mtime > t:
                bad.append(os.path.relpath(p, gen))
    for b in bad[:20]:
        print(f"LEAK {os.path.basename(gen)} {b}: written after the generation was published (an in-place write through a hard link)")
    return 1 if bad else 0


# ---------------------------------------------------------------------------------------------------- the check

def changed_paths(repo: str, tree: str, w: str, rev: str | None) -> list[str]:
    if rev:
        return [p for p in git(repo, "diff", "--name-only", "--no-renames", w, rev).splitlines() if p]
    out = set(p for p in git(tree, "diff", "--name-only", "--no-renames", w).splitlines() if p)
    out |= set(p for p in git(tree, "ls-files", "--others", "--exclude-standard").splitlines() if p.endswith(".lean"))
    return sorted(out)


def toolchain(cwd: str) -> str:
    return subprocess.run(["lean", "--print-prefix"], capture_output=True, text=True, check=True, cwd=cwd).stdout.strip()


def cflags(prefix: str) -> list[str]:
    # lake 4.30's module object compile (read from a warm build's ir/*.c.o.export.trace)
    return ["-I", f"{prefix}/include", "-fstack-clash-protection", "-fdata-sections", "-ffunction-sections", "-fPIC",
            "-fvisibility=hidden", "-Wno-unused-command-line-argument", "--sysroot", prefix, "-nostdinc",
            "-isystem", f"{prefix}/include/clang", "-O3", "-DNDEBUG", "-DLEAN_EXPORTING"]


class Job:
    def __init__(self, name: str, argv: list[str], out: str, env: dict | None = None, cwd: str | None = None):
        self.name, self.argv, self.out, self.env, self.cwd = name, argv, out, env, cwd
        self.p = None
        self.t0 = 0.0


def run_dag(jobs: dict[str, Job], deps: dict[str, set[str]], n: int, on_done) -> tuple[set, set, set, bool]:
    """Run JOBS, each after its DEPS succeeded, N at once. A failed job's dependents are not run (blocked)."""
    ok, bad, blocked, killed = set(), set(), set(), False
    pending, running = set(jobs), {}
    while pending or running:
        for k in sorted(pending):
            if len(running) >= n:
                break
            if deps[k] & (bad | blocked):
                pending.discard(k)
                blocked.add(k)
            elif deps[k] <= ok:
                j = jobs[k]
                j.t0 = time.time()
                j.fh = open(j.out, "w")
                j.p = subprocess.Popen(j.argv, stdout=j.fh, stderr=subprocess.STDOUT, env=j.env, cwd=j.cwd)
                running[k] = j
                pending.discard(k)
        if not running:
            if pending:   # nothing runnable and nothing running: the rest is blocked
                blocked |= pending
                pending.clear()
            break
        pid, status = os.wait()
        for k, j in list(running.items()):
            if j.p.pid == pid:
                j.p.returncode = os.waitstatus_to_exitcode(status)
                j.fh.close()
                del running[k]
                rc = j.p.returncode
                if rc < 0 or rc >= 128:
                    killed = True
                (ok if rc == 0 else bad).add(k)
                on_done(k, j, rc)
                break
    return ok, bad, blocked, killed


def check(a) -> int:
    repo, treedir, gen, out = (os.path.abspath(x) for x in (a.repo, a.tree, a.gen, a.out))
    t0 = time.time()
    w = open(os.path.join(gen, "COMMIT")).read().strip()
    head = a.rev or git(treedir, "rev-parse", "HEAD").strip()
    if subprocess.run(["git", "-C", repo, "merge-base", "--is-ancestor", w, head]).returncode != 0:
        print(f"nd-check: REFUSED — the warm build is at {w[:12]} and this lane's {'commit' if a.rev else 'HEAD'} "
              f"{head[:12]} does not contain it: rebase onto origin/main first (git rebase origin/main), then check again")
        return 2
    ahead = git(repo, "rev-list", "--count", f"{w}..{head}").strip()
    changed = changed_paths(repo, treedir, w, a.rev)
    t = treemod.read(treedir)
    # the package's modules are its libs' (lakefile globs `.submodules X` per lib X): a .lean under another directory
    # of the worktree (a copy of the tree, a scratch file) is not one
    t.modules = {m: v for m, v in t.modules.items() if m.split(".")[0] in set(t.libs)}
    changed = [p for p in changed if not p.endswith(".lean") or p == "lakefile.lean" or p.split("/")[0] in set(t.libs)]
    opts = options(t.lake)
    whole = [p for p in changed if p in BUILD_INPUTS]
    cdirs = {x["name"]: x["cdirs"] for x in t.lake["extern_lib"]}
    cchanged = sorted(n for n, ds in cdirs.items() if any(p.startswith(d.rstrip("/") + "/") for d in ds for p in changed))
    mods = treemod.changed_modules(changed)
    reach = set(t.modules) if whole else treemod.reach(t, mods)
    # a module the generation has no .olean for (it was never built there) is built here
    for m in t.modules:
        if m not in reach and not os.path.exists(os.path.join(gen, "lib/lean", m.replace(".", "/") + ".olean")):
            reach.add(m)
    reach |= {m for m in t.modules if t.closure([m]) & reach}   # importers of what was just added
    if a.targets:
        named = set()
        for x in a.targets:
            x = x[2:] if x.startswith("./") else x
            m = x[:-5].replace("/", ".") if x.endswith(".lean") else x
            if m not in t.modules:
                print(f"nd-check: no module {x} in this tree")
                return 2
            named.add(m)
        same = sorted(named - reach)
        if same:
            print(f"nd-check: unchanged since the warm build, nothing to check: {' '.join(same)}")
        need = set().union(*(t.closure([m]) for m in named)) & reach
    else:
        need = reach
    exes = {}
    if not a.targets or a.exes:
        for e, root in t.exes.items():
            if cchanged or whole or t.closure([root]) & need:
                exes[e] = root
    print(f"nd-check: warm {w[:12]}, this lane {ahead} commit(s) ahead; {len(changed)} path(s) changed, "
          f"{len(mods)} module(s), reach {len(reach)}, checking {len(need)}"
          + (f", linking {len(exes)} exe(s)" if exes else "")
          + (f"; a build input changed ({' '.join(whole)}): every module" if whole else "")
          + (f"; C changed in {' '.join(cchanged)}" if cchanged else ""), flush=True)
    if a.plan:   # scripts/nd-check asks first, so a check with nothing to build takes no build slot
        return 10 if need or exes or cchanged else 0

    # OUT belongs to one generation: a different warm commit makes every output stale
    gf = os.path.join(out, "GEN")
    if not os.path.exists(gf) or open(gf).read().strip() != w:
        for sub in ("lib", "ir", "bin", "keys", "log"):
            shutil.rmtree(os.path.join(out, sub), ignore_errors=True)
        os.makedirs(out, exist_ok=True)
        with open(gf, "w") as f:
            f.write(w + "\n")
    for sub in ("lib/lean", "ir", "bin", "keys", "log"):
        os.makedirs(os.path.join(out, sub), exist_ok=True)

    def p_out(m: str, ext: str, sub: str = "lib/lean") -> str:
        return os.path.join(out, sub, m.replace(".", "/") + ext)

    def olean(m: str) -> str:
        return p_out(m, ".olean") if m in need else os.path.join(gen, "lib/lean", m.replace(".", "/") + ".olean")

    keys: dict[str, str] = {}
    env = dict(os.environ, LEAN_PATH=os.path.join(out, "lib/lean") + os.pathsep + os.path.join(gen, "lib/lean"))
    tcfile = os.path.join(treedir, "lean-toolchain")
    tc = open(tcfile).read().strip() if os.path.exists(tcfile) else ""
    jobs, deps = {}, {}
    order = sorted(need)
    for m in order:
        deps[m] = {i for i in t.modules[m].imports if i in need}

    def key(m: str) -> str:
        h = hashlib.sha256()
        h.update(json.dumps([tc, opts, m]).encode())
        h.update(open(os.path.join(treedir, t.modules[m].path), "rb").read())
        for i in sorted(t.closure([m]) - {m}):
            h.update(f"\0{i}\0".encode())
            if i in need:
                h.update(keys.get(i, "?").encode())
        return h.hexdigest()

    cached = set()
    for m in order:
        s = os.path.join(out, "ir", m.replace(".", "/") + ".setup.json")
        os.makedirs(os.path.dirname(s), exist_ok=True)
        os.makedirs(os.path.dirname(p_out(m, ".olean")), exist_ok=True)
        with open(s, "w") as f:
            json.dump({"plugins": [], "package": PACKAGE, "options": opts, "name": m, "isModule": False,
                       "importArts": {i: [olean(i)] for i in sorted(t.closure([m]) - {m})}, "dynlibs": []}, f)
        jobs[m] = Job(m, ["lean", os.path.join(treedir, t.modules[m].path), "-o", p_out(m, ".olean"),
                          "-i", p_out(m, ".ilean"), "-c", p_out(m, ".c", "ir"), "--setup", s],
                      os.path.join(out, "log", m + ".log"), env, treedir)

    # a module whose key (its source, the options, its in-reach imports' keys) is unchanged keeps its outputs
    def keyed(m: str) -> str:
        if m not in keys:
            for i in sorted(deps[m]):
                keyed(i)
            keys[m] = key(m)
        return keys[m]
    for m in order:
        kf = os.path.join(out, "keys", m)
        if os.path.exists(kf) and open(kf).read() == keyed(m) and os.path.exists(p_out(m, ".olean")) \
                and os.path.exists(p_out(m, ".c", "ir")):
            cached.add(m)
    for m in cached:
        del jobs[m]
    for m in jobs:
        deps[m] = deps[m] - cached
        unlink(os.path.join(out, "keys", m))
        for p in (p_out(m, ".olean"), p_out(m, ".ilean"), p_out(m, ".c", "ir")):
            unlink(p)

    def done(m: str, j: Job, rc: int) -> None:
        dt = time.time() - j.t0
        if rc == 0:
            with open(os.path.join(out, "keys", m), "w") as f:
                f.write(keyed(m))
            print(f"  ok {m} ({dt:.0f} s)", flush=True)
        else:
            print(f"  FAILED {m} ({dt:.0f} s, exit {rc}):", flush=True)
            txt = open(j.out, errors="replace").read().rstrip()
            print("\n".join("    " + l for l in txt.splitlines()[-200:]), flush=True)

    ok, bad, blocked, killed = run_dag(jobs, {m: deps[m] for m in jobs}, a.jobs, done)
    elab = time.time() - t0
    if bad or blocked:
        if blocked:
            print(f"  not checked (an import failed): {' '.join(sorted(blocked))}")
        verdict = "NOT BUILT — a lean was killed (the memory cap?): not a verdict" if killed else "RED"
        print(f"nd-check: {verdict}: {len(bad)} module(s) failed, {len(blocked)} not checked, {len(ok)} ok, "
              f"{len(cached)} unchanged, in {elab:.0f} s (logs: {os.path.join(out, 'log')})")
        return 1 if any(jobs[m].p.returncode == 1 for m in bad) or not killed else 76

    # the exes: reached modules' objects compiled here, every other object and library the generation's
    prefix = toolchain(treedir) if exes or cchanged else ""
    libs = {}
    for name, ds in cdirs.items():
        a_ = "lib" + name + ".a"
        libs[name] = os.path.join(gen, "lib", a_)
    if cchanged or whole:
        inc = f"{prefix}/include"
        for name in (cchanged if not whole else sorted(cdirs)):
            objs = []
            for d in cdirs[name]:
                for f in sorted(os.listdir(os.path.join(treedir, d))):
                    if f.endswith(".c"):
                        o = os.path.join(out, "c", f[:-2] + ".o")
                        os.makedirs(os.path.dirname(o), exist_ok=True)
                        unlink(o)
                        r = subprocess.run(["cc", "-c", "-o", o, os.path.join(treedir, d, f), "-I", inc, "-fPIC", "-O2",
                                            "-Wall", "-Wextra", "-Werror"], capture_output=True, text=True)
                        if r.returncode:
                            print(f"  FAILED {d}/{f}:\n{r.stdout}{r.stderr}")
                            return 1
                        objs.append(o)
            lib = os.path.join(out, "lib", "lib" + name + ".a")
            unlink(lib)
            subprocess.run([os.path.join(prefix, "bin", "llvm-ar"), "rcs", lib, *objs], check=True)
            libs[name] = lib
            print(f"  ok extern_lib {name}")
    objneed = sorted(set().union(*(t.closure([r]) for r in exes.values())) & need) if exes else []
    cjobs = {}
    for m in objneed:
        o = p_out(m, ".c.o.export", "ir")
        if m in cached and os.path.exists(o):
            continue
        unlink(o)
        cjobs[m] = Job(m, [os.path.join(prefix, "bin", "clang"), "-c", "-o", o, p_out(m, ".c", "ir"), *cflags(prefix)],
                       os.path.join(out, "log", m + ".cc.log"))
    cok, cbad, _, ckilled = run_dag(cjobs, {m: set() for m in cjobs}, a.jobs,
                                    lambda m, j, rc: rc and print(f"  FAILED cc {m}:\n" + open(j.out).read()))
    if cbad:
        return 76 if ckilled else 1
    linked = 0
    for e, root in sorted(exes.items()):
        rsp = os.path.join(gen, "bin", e + ".rsp")
        if not os.path.exists(rsp):   # a new exe: lake's link flags are the same for every exe of the package
            rsps = sorted(f for f in os.listdir(os.path.join(gen, "bin")) if f.endswith(".rsp"))
            if not rsps:
                print(f"  FAILED link {e}: the generation holds no link response file")
                return 1
            rsp = os.path.join(gen, "bin", rsps[0])
        flags = [x.strip('"') for x in open(rsp).read().split("\n") if x.strip()]
        flags = [x for x in flags if not x.endswith((".o.export", ".a"))]
        objs = [p_out(m, ".c.o.export", "ir") if m in need else os.path.join(gen, "ir", m.replace(".", "/") + ".c.o.export")
                for m in [root] + sorted(t.closure([root]) - {root})]
        lrsp = os.path.join(out, "bin", e + ".rsp")
        with open(lrsp, "w") as f:
            f.write("\n".join(f'"{x}"' for x in objs + [libs[n] for n in sorted(libs)] + flags) + "\n")
        dst = os.path.join(out, "bin", e)
        unlink(dst)
        r = subprocess.run([os.path.join(prefix, "bin", "clang"), "-o", dst, "@" + lrsp], capture_output=True, text=True)
        if r.returncode:
            print(f"  FAILED link {e}:\n{r.stdout[-3000:]}{r.stderr[-3000:]}")
            return 76 if r.returncode < 0 or r.returncode >= 128 else 1
        linked += 1
    # every other exe is the generation's, so OUT/bin is a whole bin directory for the rows
    for f in sorted(os.listdir(os.path.join(gen, "bin"))):
        if not f.endswith(".rsp") and f not in exes:
            link_or_copy(os.path.join(gen, "bin", f), os.path.join(out, "bin", f))
    print(f"nd-check: ok — {len(ok)} module(s) elaborated, {len(cached)} unchanged since the last check, "
          f"{len(cok)} compiled, {linked} exe(s) linked, against warm {w[:12]} in {time.time() - t0:.0f} s"
          f" (elaboration {elab:.0f} s); bin: {os.path.join(out, 'bin')}")
    return 0


def main() -> int:
    if len(sys.argv) > 1 and sys.argv[1] == "snapshot":
        return snapshot(*sys.argv[2:5])
    if len(sys.argv) > 1 and sys.argv[1] == "leaks":
        return leaks(sys.argv[2])
    ap = argparse.ArgumentParser(prog="ndcheck.py check")
    ap.add_argument("cmd", choices=["check"])
    ap.add_argument("--repo", required=True)
    ap.add_argument("--tree", required=True)
    ap.add_argument("--gen", required=True)
    ap.add_argument("--out", required=True)
    ap.add_argument("--rev")
    ap.add_argument("--jobs", type=int, default=int(os.environ.get("ND_CHECK_JOBS", "6")))
    ap.add_argument("--exes", action="store_true", help="with named modules, also link the exes they reach")
    ap.add_argument("--plan", action="store_true", help="print the reach and exit: 0 nothing to build, 10 something")
    ap.add_argument("targets", nargs="*")
    return check(ap.parse_args())


if __name__ == "__main__":
    sys.exit(main())
