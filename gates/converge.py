"""gates/converge.py — a convergence's verdict, its attribution, its time-to-fix and its reverts (GATES-22).

  converge.py record --repo DIR --sha SHA --line FILE --dir STANDING_DIR --tree TREE --traces DIR [--now EPOCH]
  converge.py owners --repo DIR --commit C

A CONVERGENCE is scripts/standing.sh on main (every 3 h while landings happen; scripts/converge). Landings between
two convergences are judged FAST (gates/fast.py): what the standing judges and a fast landing does not (the census,
every row, the benches, the waste measurements, the generated files, the whole Rust workspace with clippy) is judged
here, over the RANGE since the last GREEN standing. `record` reads the STANDING line (FILE), the standing's per-sha
log and runs output (STANDING_DIR/<sha12>.log, .runs.out) and prints:

  CONVERGENCE <sha> range <green>..<sha> landings=N (fast F, full U) => GREEN|RED|INCOMPLETE reds=K fixed=J
  RED <unit> (red at N convergences since <sha>, <h> h): attributed to <c> <OWNER> "<subject>" (<why>) | …
  FIXED <unit> after <h> h (red at N convergences; first <sha>)
  REVERT <c> <unit>                   (scripts/converge lands the revert: --reverts C, C's owners named)
  REVERT-PENDING <unit>: <c> <c> …    (more than one commit attributed: ROOT picks, `scripts/converge --revert C`)

A UNIT is one red thing: `gates`, `build`, `census`, `generated:<out>`, `cargo`, `run:<row>` (a row, its re-trace
included), `waste:<op> <metric>`. ATTRIBUTION names the commits of the range that the red unit READ:
  run:<row>    the commits a full judge of that commit alone would have selected the row for: its row line changed,
               the runner changed, a module of its reach changed, its crate changed (a cargo row), a waste row it
               measured changed, or its newest stored read-set (gates/readset.py) was touched by the commit (a path
               it read, a path it stat'ed added/removed/re-kinded, an add or remove in a directory it listed); a
               row with no stored read-set by the static rule (gates/runs.py selected), which over-attributes;
  build        the commits that changed a module of the import closure of a module the build log names in an
               error, or a non-module build input; with no module named, every commit that changed a build input;
  census       the commits that changed a module or gates/axioms-allow.tsv;
  generated:O  the commits that changed O, or a module of its generator's reach (a cargo generator: the workspace);
  cargo        the commits that changed the Rust workspace;
  waste:W      the commits that changed W's row in gates/waste.tsv, and the attribution of every row whose
               stored read-set says it measured W;
  gates        the commits that changed a path a red gate line names; none named: every commit of the range.
Each attributed commit is printed with its OWNER (the layer of its subject prefix, gates/owners.py SUBJECT).
A unit's history is kept in STANDING_DIR/converge-state.json: first seen (sha, time), the commits attributed then,
how many convergences it has been red. A unit whose stage reads ok is FIXED (time-to-fix printed); a stage that did
not run (ABSENT, INCOMPLETE, UNJUDGED) leaves its units as they were (a stage that cannot run proves nothing).
THE REVERT RULE (Ember via ROOT, 10-21): a unit still red at the NEXT convergence is reverted by name. Its commit is
the one attributed both at its first sighting and now; exactly one: REVERT (scripts/converge lands it, the owners
named in CROSS-LAYER, --reverts C); several: REVERT-PENDING naming them, for ROOT. A commit is reverted once.
"""
import argparse
import json
import os
import re
import subprocess
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import fast  # noqa: E402
import owners  # noqa: E402
import readset  # noqa: E402
import runs  # noqa: E402
import tree as treemod  # noqa: E402

STAGES = ("gates", "build", "census", "generated", "cargo", "runs", "waste")


def git(repo: str, *args: str, check: bool = True) -> str:
    r = subprocess.run(["git", "-C", repo, *args], capture_output=True, text=True)
    if check and r.returncode != 0:
        raise RuntimeError(f"git {' '.join(args)}: {r.stderr.strip()}")
    return r.stdout


def stages(line: str) -> dict[str, str]:
    """`gates=ok build=ok … runs=RED(…) waste=ok(pinned …)` -> {stage: value}, values with balanced parens."""
    out = {}
    for st in STAGES:
        m = re.search(rf"(?:^| ){st}=", line)
        if not m:
            continue
        i, depth = m.end(), 0
        j = i
        while j < len(line) and (depth or line[j] != " "):
            depth += {"(": 1, ")": -1}.get(line[j], 0)
            j += 1
        out[st] = line[i:j]
    return out


def judged(v: str | None) -> str:
    """ok / RED / not (a stage that did not give a verdict)."""
    if v is None:
        return "not"
    if v == "ok" or v.startswith("ok("):
        return "ok"
    return "RED" if v.startswith("RED") else "not"


def owner_of(subject: str) -> str:
    m = re.match(r"([a-z]+)(?:\([^)]*\))?!?:", subject)
    if not m:
        return "ROOT"
    return "/".join(sorted(owners.SUBJECT.get(m.group(1), {m.group(1).upper()})))


class Commit:
    def __init__(self, repo: str, sha: str):
        self.sha = sha
        body = git(repo, "log", "-1", "--format=%B", sha)
        self.subject = body.split("\n", 1)[0]
        self.fast = bool(re.search(r"(?m)^JUDGED: fast", body))
        st = git(repo, "diff", "--name-status", "--no-renames", f"{sha}^", sha).splitlines()
        self.changed = [l.split("\t")[-1] for l in st if l]
        self.ad = {l.split("\t")[-1] for l in st if l[:1] in ("A", "D", "T")}
        self.mods = {p[:-5].replace("/", ".") for p in self.changed if p.endswith(".lean") and p != "lakefile.lean"}
        self.owner = owner_of(self.subject)
        self._repo = repo

    def show(self, rev: str, path: str) -> str:
        return git(self._repo, "show", f"{rev}:{path}", check=False)

    def label(self) -> str:
        return f'{self.sha[:12]} {self.owner} "{self.subject[:70]}"'


def row_line_in(text: str, row: str) -> str | None:
    for line in text.splitlines():
        if line.split("\t", 1)[0] == row:
            return line
    return None


def newest_readset(store: str, row: str, line: str | None) -> dict | None:
    for _, rec in readset.stored(store, row):
        if rec.get("readset") and (line is None or rec.get("line") == line):
            return rec["readset"]
    return None


def attribute_row(t, rows, store: str, row: str, cs: list[Commit]) -> list[tuple[Commit, str]]:
    line = runs.row_line(t.root, None, row)
    rs = newest_readset(store, row, line)
    reach = runs.reach_of(t, row)
    crate = row.split(":")[1] + "/" if row.startswith(("cargo:", "cargo-untraced:")) else None
    out = []
    for c in cs:
        why = None
        if "gates/runs.tsv" in c.changed and (row_line_in(c.show(c.sha + "^", "gates/runs.tsv"), row)
                                              != row_line_in(c.show(c.sha, "gates/runs.tsv"), row)):
            why = "its row changed"
        elif any(x in readset.RUNNER for x in c.changed):
            why = f"the runner changed ({next(x for x in c.changed if x in readset.RUNNER)})"
        elif reach & c.mods:
            why = f"changed module {sorted(reach & c.mods)[0]}, of its reach"
        elif crate and any(x.startswith(crate) for x in c.changed):
            why = f"changed its crate {crate}"
        elif readset.WASTE in c.changed and rs and rs.get("W") and (
                set(rs["W"]) & readset.waste_changed(c.show(c.sha + "^", readset.WASTE), c.show(c.sha, readset.WASTE))):
            why = "changed a waste row it measures"
        elif rs is not None:
            why = readset.touched_by(rs, c.changed, c.ad)
        elif row in runs.selected(t, c.changed, rows) or row in runs.standing_selected(t, c.changed, rows):
            why = "the static rule (no stored read-set: over-attributes)"
        if why:
            out.append((c, why))
    return out


ERR_MOD = re.compile(r"(?:✖ \[\d+/\d+\] Building ([\w.]+))|(?:error: (?:\./)?([\w/]+)\.lean:\d+:\d+)")


def attribute_build(t, log: str, cs: list[Commit]) -> list[tuple[Commit, str]]:
    named = set()
    for m in ERR_MOD.finditer(log):
        named.add(m.group(1) or m.group(2).replace("/", "."))
    clo = t.closure(sorted(named)) | named if named else set()
    out = []
    for c in cs:
        bi = next((p for p in c.changed if p in fast.BUILD_INPUTS or p.endswith((".c", ".h"))), None)
        if bi:
            out.append((c, f"changed build input {bi}"))
        elif named and c.mods & clo:
            out.append((c, f"changed {sorted(c.mods & clo)[0]}, in the closure of {sorted(named)[0]} (named in an error)"))
        elif not named and c.mods:
            out.append((c, f"changed module {sorted(c.mods)[0]} (the log names no module)"))
    return out


def attribute_unit(unit: str, t, rows, store: str, log: str, cs: list[Commit], gen: dict[str, str]):
    if unit.startswith("run:"):
        return attribute_row(t, rows, store, unit[4:], cs)
    if unit == "build":
        return attribute_build(t, log, cs)
    if unit == "census":
        return [(c, "changed a module or the axiom allow-list") for c in cs
                if c.mods or "gates/axioms-allow.tsv" in c.changed]
    if unit == "cargo":
        return [(c, "changed the Rust workspace") for c in cs if fast.crates(t.root, c.changed)]
    if unit.startswith("generated:"):
        out_path = unit.split(":", 1)[1]
        exe = gen.get(out_path, "")
        res = []
        for c in cs:
            if out_path in c.changed:
                res.append((c, f"changed {out_path}"))
            elif exe.startswith("cargo:") and fast.crates(t.root, c.changed):
                res.append((c, "changed the Rust workspace (its generator)"))
            elif exe in t.exes and runs.reach(t, exe) & c.mods:
                res.append((c, f"changed {sorted(runs.reach(t, exe) & c.mods)[0]}, of its generator's reach"))
        return res
    if unit.startswith("waste:"):
        w = unit[6:].replace(" ", "\t", 1)
        res = [(c, "changed its row in gates/waste.tsv") for c in cs if readset.WASTE in c.changed and
               w in readset.waste_changed(c.show(c.sha + "^", readset.WASTE), c.show(c.sha, readset.WASTE))]
        seen = {c.sha for c, _ in res}
        for row in rows:
            rs = newest_readset(store, row, runs.row_line(t.root, None, row))
            if rs and w in rs.get("W", []):
                for c, why in attribute_row(t, rows, store, row, cs):
                    if c.sha not in seen:
                        res.append((c, f"row {row} measures it: {why}"))
                        seen.add(c.sha)
        return res
    if unit == "gates":
        reds = "\n".join(l for l in log.splitlines() if re.match(r"^  [a-z-]+: ", l) and "PRE-EXISTING" not in l)
        res = []
        for c in cs:
            hit = next((p for p in c.changed if p in reds), None)
            if hit:
                res.append((c, f"changed {hit}, named by a red gate line"))
        return res or [(c, "the gates read the whole tree and no red line names a path") for c in cs]
    return [(c, "unattributable unit") for c in cs]


def red_units(st: dict[str, str], runs_out: str, log: str) -> dict[str, set[str] | None]:
    """stage -> the red units of a RED stage, an empty set for an ok stage, None for a stage with no verdict."""
    out: dict[str, set[str] | None] = {}
    for s in STAGES:
        j = judged(st.get(s))
        if j == "not":
            out[s] = None
        elif j == "ok":
            out[s] = set()
        elif s == "runs":
            rs = {"run:" + m.group(1) for m in re.finditer(r"(?m)^  run (\S+).*?: RED", runs_out)}
            out[s] = rs or {"run:?"}
        elif s == "waste":
            ws = {"waste:" + m.group(1) + " " + m.group(2)
                  for m in re.finditer(r"(?m)^waste (\S+) ([^:]+): ", log)}
            out[s] = ws or {"waste:?"}
        elif s == "generated":
            inner = re.match(r"RED\((.*)\)$", st[s])
            out[s] = {"generated:" + x for x in (inner.group(1).split(",") if inner else ["?"])}
        else:
            out[s] = {s}
    return out


def unit_stage(u: str) -> str:
    if u.startswith("run:"):
        return "runs"
    for p in ("waste", "generated"):
        if u.startswith(p + ":"):
            return p
    return u


def record(a) -> int:
    line = open(a.line, encoding="utf-8").read().strip()
    sha = git(a.repo, "rev-parse", a.sha).strip()
    st = stages(line)
    verdict = line.rsplit("=> ", 1)[-1].strip() if "=> " in line else "INCOMPLETE"
    s12 = sha[:12]

    def rd(p: str) -> str:
        try:
            return open(os.path.join(a.dir, p), encoding="utf-8", errors="replace").read()
        except OSError:
            return ""
    log, runs_out = rd(f"{s12}.log"), rd(f"{s12}.runs.out")
    greens = [l.split()[1] for l in rd("verdicts.log").splitlines()
              if l.startswith("STANDING ") and l.rstrip().endswith("=> GREEN") and not sha.startswith(l.split()[1])]
    green = None
    for g in reversed(greens):
        full = git(a.repo, "rev-parse", "--verify", "-q", g + "^{commit}", check=False).strip()
        if full and subprocess.run(["git", "-C", a.repo, "merge-base", "--is-ancestor", full, sha]).returncode == 0:
            green = full
            break
    rng = f"{green}..{sha}" if green else sha
    shas = git(a.repo, "rev-list", "--first-parent", *(["--max-count=300"] if not green else []), rng).split()
    cs = [Commit(a.repo, c) for c in shas]
    nf = sum(c.fast for c in cs)
    t = treemod.read(a.tree)
    try:
        rows = runs.table(a.tree)
    except ValueError:
        rows = {}
    gen = {}
    gp = os.path.join(a.tree, "gates", "generated.tsv")
    for l in open(gp, encoding="utf-8") if os.path.isfile(gp) else []:
        f = l.split()
        if len(f) == 2 and not l.startswith("#"):
            gen[f[1]] = f[0]
    units = red_units(st, runs_out, log)
    statep = os.path.join(a.dir, "converge-state.json")
    try:
        state = json.load(open(statep, encoding="utf-8"))
    except (OSError, ValueError):
        state = {}
    now = a.now or int(time.time())
    out = []
    fixed = []
    for u in sorted(list(state)):
        s = unit_stage(u)
        if units.get(s) is not None and u not in units[s]:
            e = state.pop(u)
            h = (now - e["first"]) / 3600
            fixed.append(f"FIXED {u} after {h:.1f} h (red at {e['seen']} convergence(s); first {e['first_sha'][:12]})")
    reds = sorted(set().union(*(v for v in units.values() if v)))
    reverts = []
    for u in reds:
        att = attribute_unit(u, t, rows, a.traces, log, cs, gen)
        now_c = [c.sha for c, _ in att]
        e = state.get(u)
        if e is None:
            e = state[u] = {"first": now, "first_sha": sha, "commits": now_c, "seen": 0, "reverted": []}
        e["seen"] += 1
        h = (now - e["first"]) / 3600
        who = " | ".join(f"{c.label()} ({why})" for c, why in att) or "no commit of the range (ROOT)"
        out.append(f"RED {u} (red at {e['seen']} convergence(s) since {e['first_sha'][:12]}, {h:.1f} h): attributed to {who}")
        if e["seen"] >= 2:
            cand = [c for c in e["commits"] if c in now_c and c not in e["reverted"]]
            if len(cand) == 1:
                reverts.append(f"REVERT {cand[0]} {u}")
                e["reverted"].append(cand[0])
            elif cand:
                reverts.append(f"REVERT-PENDING {u}: {' '.join(c[:12] for c in cand)} (several commits read it: ROOT "
                               f"picks, scripts/converge --revert C)")
            elif not e["reverted"]:
                reverts.append(f"REVERT-PENDING {u}: no commit attributed at both sightings (ROOT routes)")
    tmp = statep + f".{os.getpid()}"
    json.dump(state, open(tmp, "w", encoding="utf-8"), indent=1, sort_keys=True)
    os.replace(tmp, statep)
    head = (f"CONVERGENCE {s12} range {green[:12] + '..' if green else '(no GREEN standing in the log; the last 300) ..'}{s12} "
            f"landings={len(cs)} "
            f"(fast {nf}, full {len(cs) - nf}) => {verdict} reds={len(reds)} fixed={len(fixed)} "
            f"at {time.strftime('%Y-%m-%dT%H:%MZ', time.gmtime(now))}")
    text = "\n".join([head] + out + fixed + reverts)
    print(text)
    with open(os.path.join(a.dir, "convergence.log"), "a", encoding="utf-8") as fh:
        fh.write(text + "\n")
    return 0


def owners_cmd(a) -> int:
    """The layers owning C's paths, and C's subject layer: what a revert of C names in CROSS-LAYER."""
    c = Commit(a.repo, a.commit)
    rows = owners.table(git(a.repo, "rev-parse", "--show-toplevel").strip())
    names = {owners.owner(rows, p) for p in c.changed} - {"SHARED"}
    names |= set(c.owner.split("/"))
    print(" ".join(sorted(names)))
    return 0


def main() -> int:
    ap = argparse.ArgumentParser()
    sub = ap.add_subparsers(dest="cmd", required=True)
    r = sub.add_parser("record")
    for x in ("--repo", "--sha", "--line", "--dir", "--tree", "--traces"):
        r.add_argument(x, required=True)
    r.add_argument("--now", type=int)
    o = sub.add_parser("owners")
    o.add_argument("--repo", required=True)
    o.add_argument("--commit", required=True)
    a = ap.parse_args()
    return record(a) if a.cmd == "record" else owners_cmd(a)


if __name__ == "__main__":
    sys.exit(main())
