"""gates/fast.py — what one landing is judged by (GATES-22, Ember 10-21: "we don't need to focus on landings as much,
as long as every now and then we make sure the whole system still builds and passes its tests, and do convergences at
those points instead of EVERY LANDING").

  fast.py mode --message FILE --changed FILE     prints `fast` or `full WHY`
  fast.py targets TREE --changed FILE            the lake targets the change reaches, one line (`` = none)
  fast.py crates TREE --changed FILE             `workspace`, the packages to check (one line), or `` = none

THE MODE. A landing is judged in FULL (scripts/pre-push: every target, the census, the selected rows, the waste, the
generated files, the whole Rust workspace) when its subject is a flag day (`kernel!:`) or it changes the JUDGE'S CODE:
gates/*.py or anything under scripts/ (the self-judge rule: main's code judges a judge change, and a judge change is
judged in full). Everything else lands FAST: scripts/commit's stale-path guard (GATES-20b/20b'), every source gate
(gates/check.py, the candidate's and the parent's: owners, closure, refusals, size, paths, the runs table, tcb, vectors,
the waste ratchet, targets), `lake build` of exactly the targets the change reaches, `cargo check` and `cargo fmt --check`
of the packages it reaches, and nothing else. A gates/*.tsv change is DATA (20h (b)): it is judged by the source gates
(the ratchets of ceilings.tsv and waste.tsv, runs.tsv's classification) at the landing, and by every row it feeds at
the next convergence.

THE TARGETS. A changed module, every module that imports it (gates/tree.py dependents), and every module that imports
a module this change deleted (its import now dangles): the lean_libs holding one of them and the lean_exes whose import
closure holds one (an exe links: an extern or a missing `main` fails only there). A non-module build input (lakefile.lean,
lean-toolchain, lake-manifest.json, a C source or header) builds every target. A lib target is built whole: lake's traces
rebuild only what the slot's .lake lacks.

THE CRATES. A path under a workspace member reaches that member's package and every member that depends on it by a
path dependency (a changed API breaks its importers); the root Cargo.toml or Cargo.lock, or a manifest that
does not parse, reaches the workspace whole.
"""
import os
import re
import sys
import tomllib

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import tree  # noqa: E402

FLAGDAY = re.compile(r"^[a-z]+(?:\([^)]*\))?!:")
BUILD_INPUTS = ("lakefile.lean", "lean-toolchain", "lake-manifest.json")


def judge_code(p: str) -> bool:
    return p.startswith("scripts/") or (p.startswith("gates/") and p.endswith(".py"))


def mode(subject: str, changed: list[str]) -> str:
    if FLAGDAY.match(subject):
        return "full a flag day (`!` in the subject)"
    j = next((p for p in changed if judge_code(p)), None)
    if j:
        return f"full the judge's code changes ({j}): a judge change is judged in full by main's judge"
    return "fast"


def targets(root: str, changed: list[str]) -> list[str]:
    t = tree.read(root)
    allt = [x["name"] for x in t.lake["lean_lib"]] + [x["name"] for x in t.lake["lean_exe"]]
    if any(p in BUILD_INPUTS or p.endswith((".c", ".h")) for p in changed):
        return allt
    lean = [p[:-5].replace("/", ".") for p in changed if p.endswith(".lean") and p != "lakefile.lean"]
    if not lean:
        return []
    present = {m for m in lean if m in t.modules}
    gone = set(lean) - present
    dep = t.dependents()
    r = set(present).union(*(dep[m] for m in present))
    for m, mod in t.modules.items():
        if gone & set(mod.imports):
            r |= {m} | dep[m]
    libs = [x for x in t.libs if any(m.split(".")[0] == x for m in r)]
    exes = [e for e, root_mod in t.exes.items() if t.closure([root_mod]) & r]
    # a deleted module with no importer reaches its lib (its other modules may still name it in a doc only)
    libs += [x for x in t.libs if x not in libs and any(m.split(".")[0] == x for m in gone)]
    return libs + exes


def crates(root: str, changed: list[str]) -> list[str] | str:
    if any(p in ("Cargo.toml", "Cargo.lock") for p in changed):
        return "workspace"
    try:
        members = tomllib.load(open(os.path.join(root, "Cargo.toml"), "rb"))["workspace"]["members"]
        assert isinstance(members, list) and all(isinstance(m, str) for m in members)
    except FileNotFoundError:
        return []
    except Exception:
        return "workspace"
    hit = [m for m in members if any(p.startswith(m.rstrip("/") + "/") for p in changed)]
    if not hit:
        return []
    # each member's package name and path dependencies, read from the manifests
    name, deps = {}, {}
    try:
        for m in members:
            man = tomllib.load(open(os.path.join(root, m, "Cargo.toml"), "rb"))
            name[m] = man["package"]["name"]
            ds = set()
            for sec in ("dependencies", "dev-dependencies", "build-dependencies"):
                for v in (man.get(sec) or {}).values():
                    if isinstance(v, dict) and "path" in v:
                        ds.add(os.path.normpath(os.path.join(m, v["path"])))
            deps[m] = ds
    except Exception:
        return "workspace"
    out, stack = set(), list(hit)
    while stack:
        m = stack.pop()
        if m in out:
            continue
        out.add(m)
        stack += [x for x in members if os.path.normpath(m) in deps[x]]
    return [name[m] for m in members if m in out]


def main() -> int:
    cmd = sys.argv[1]
    args = sys.argv[2:]

    def opt(f: str) -> str:
        return args[args.index(f) + 1]
    changed = [x for x in open(opt("--changed"), encoding="utf-8").read().split("\n") if x]
    if cmd == "mode":
        subject = open(opt("--message"), encoding="utf-8").read().strip().split("\n")[0]
        print(mode(subject, changed))
    elif cmd == "targets":
        print(" ".join(targets(args[0], changed)))
    elif cmd == "crates":
        c = crates(args[0], changed)
        print(c if isinstance(c, str) else " ".join(c))
    else:
        print(f"fast.py: unknown command {cmd}", file=sys.stderr)
        return 2
    return 0


if __name__ == "__main__":
    sys.exit(main())
