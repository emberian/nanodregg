"""gates/touched.py — what a change touches: what a landing builds and runs (WORK-RULES 10-27, rule 1).

  touched.py plan TREE --changed FILE [--base-table F]
                                                 two lines: `crates: …`, `rows: …`
  touched.py rows TREE --changed FILE --bin DIR [--base-table F]
                                                 run the rows the change touches over the built exes in DIR; one
                                                 line per run, exit 1 when one is not ok

A landing builds what it changed and runs what it touched, then pushes (scripts/commit). Nothing else gates it; the
whole tree, every row, the benches, the census and the tables are the convergence's REPORT (scripts/converge).

THE LEAN BUILD is not planned here: scripts/commit checks the change's reach (the changed modules, their importers,
the importers of a deleted module: tree.reach) against the box's warm build with gates/ndcheck.py (GATES-32), which
also links the exes whose closure the reach meets; every other exe a row runs is the warm build's.

THE CRATES. A path under a workspace member reaches that member's package and every member that depends on it by a
path dependency; the root Cargo.toml or Cargo.lock, or a manifest that does not parse, reaches the workspace whole.

THE ROWS (gates/runs.tsv, read by gates/runs.py's table). A Lean verdict row runs when a changed module is in its
exe's reach (runs.reach: the import closure, every exe's closure for an exe that spawns others), when its own row line
changed, or when a path under world/ changed (the package texts the rows install). A `cargo:`/`cargo-untraced:` row
runs when its crate changed or it drives an exe that runs. `standing:` rows (benches) and `script:` rows (THE BAR, the
gates' own plants) are the convergence's. A row passes when every one of its argument lists exits 0 and prints its
pass line last (a cargo row: exit 0). Known-red controls are not run here.
"""
import os
import sys
import tomllib

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import tree  # noqa: E402

BUILD_INPUTS = ("lakefile.lean", "lean-toolchain", "lake-manifest.json")


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


def row_lines(path: str) -> dict[str, str]:
    try:
        return {l.split("\t", 1)[0]: l.rstrip("\n") for l in open(path, encoding="utf-8") if l.strip() and not l.startswith("#")}
    except FileNotFoundError:
        return {}


def rows(root: str, changed: list[str], base_table: str | None = None) -> list[str]:
    import runs  # noqa: E402  (the table reader and the exe reach)
    t = tree.read(root)
    table = runs.table(root)
    mods = tree.changed_modules(changed)
    world = any(p.startswith("world/") for p in changed)
    now, before = row_lines(os.path.join(root, runs.RUNS)), row_lines(base_table) if base_table else {}
    moved = {k for k in now if runs.RUNS in changed and now.get(k) != before.get(k)}
    lean = [k for k, (rs, _p, _c) in table.items()
            if rs is not None and not k.startswith(runs.CARGO + ("script:", runs.STANDING))
            and k in t.exes and (world or k in moved or runs.reach(t, k) & mods)]
    reached = set(lean) | {e for e in t.exes if mods and runs.reach(t, e) & mods}
    cargo = [k for k, (rs, _p, _c) in table.items() if k.startswith(runs.CARGO)
             and (k in moved or any(p.startswith(k.split(":")[1] + "/") for p in changed) or set(rs[0]) & reached)]
    return sorted(lean) + sorted(cargo)


def run_rows(root: str, selected: list[str], bindir: str) -> int:
    import runs  # noqa: E402
    import tempfile  # noqa: E402
    t = tree.read(root)
    table = runs.table(root)
    bad = 0
    scratch = tempfile.mkdtemp(prefix="nd-land-rows-")
    for k in selected:
        rs, passline, _ = table[k]
        lists = [[]] if k.startswith(runs.CARGO) else rs
        for i, args in enumerate(lists):
            out, v = runs.run(t, k, args, passline, os.path.join(scratch, f"r{i}"), bindir,
                              drives=rs[0] if k.startswith(runs.CARGO) else ())
            label = k + (" " + " ".join(args) if args else "")
            print(f"  row {label}: {v}", flush=True)
            if not v.startswith("ok"):
                bad += 1
                tail = [l for l in out.strip().splitlines() if l.strip()][-12:]
                print("\n".join("    | " + l[:200] for l in tail), flush=True)
    os.rmdir(scratch) if os.path.isdir(scratch) and not os.listdir(scratch) else None
    print(f"rows: {'ok' if not bad else f'{bad} not ok'} ({len(selected)} row(s))")
    return 1 if bad else 0


def main() -> int:
    cmd, root, args = sys.argv[1], sys.argv[2], sys.argv[3:]

    def opt(f: str) -> str | None:
        return args[args.index(f) + 1] if f in args else None
    changed = [x for x in open(opt("--changed"), encoding="utf-8").read().split("\n") if x]
    if cmd == "plan":
        c = crates(root, changed)
        print("crates: " + (c if isinstance(c, str) else " ".join(c)))
        print("rows: " + " ".join(rows(root, changed, opt("--base-table"))))
        return 0
    if cmd == "rows":
        return run_rows(root, rows(root, changed, opt("--base-table")), opt("--bin"))
    print(f"touched.py: unknown command {cmd}", file=sys.stderr)
    return 2


if __name__ == "__main__":
    sys.exit(main())
