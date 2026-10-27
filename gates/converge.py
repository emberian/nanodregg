"""gates/converge.py — the convergence REPORT: what is red on origin/main, the landings it came from, time-to-fix.

  converge.py record --repo DIR --sha SHA --line FILE --dir STANDING_DIR --tree TREE --traces DIR [--now EPOCH]
  converge.py build [--tool lake|cargo] --out FILE --rc N --cgroup FILE [--peaks FILE --sha SHA --threads N]
  converge.py floor --peaks FILE [--days N]

A CONVERGENCE is scripts/standing.sh on origin/main (every 3 h while landings happen; scripts/converge). A landing
builds what it changed and runs what it touched (scripts/commit); everything else (the whole build, the census, every
row, the benches, the waste measurements, the generated files, the Rust workspace with clippy, the source checks) is
looked at here, over the RANGE since the last GREEN report. It refuses nothing and reverts nothing.
`record` reads the STANDING line (FILE), the standing's per-sha
log and runs output (STANDING_DIR/<sha12>.log, .runs.out) and prints:

  CONVERGENCE <sha> range <green>..<sha> landings=N => GREEN|RED|INCOMPLETE reds=K fixed=J
  RED <unit> (red at N convergences since <sha>, <h> h): attributed to <c> <OWNER> "<subject>" (<why>) | …
  FIXED <unit> after <h> h (red at N convergences; first <sha>)
  TIMES stages: gates=Ns build=Ns … total=Ns       (standing.sh's own clock, STANDING_DIR/<sha12>.times; GATES-20g)
  ROWS wall Ns; concurrency …; ran N: ROW Ns (where), …; carried N: ROW …; daily N: ROW …
                                      (runs.py's own `  time ROW:` lines; reported, never gated)

A UNIT is one red thing: `gates`, `build`, `census`, `generated:<out>`, `cargo`, `run:<row>` (a row, its re-trace
included), `waste:<op> <metric>`. ATTRIBUTION names the commits of the range that the red unit READ:
  run:<row>    the commits whose change the row reads: its row line changed,
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
Each attributed commit is printed with its OWNER (the layer of its subject prefix, SUBJECT below).
A unit's history is kept in STANDING_DIR/converge-state.json: first seen (sha, time), the commits attributed then,
how many convergences it has been red. A unit whose stage reads ok is FIXED (time-to-fix printed); a stage that did
not run (ABSENT, INCOMPLETE, UNJUDGED) leaves its units as they were (a stage that cannot run proves nothing).
A red is a task for the lane whose landing it names; it is fixed forward (WORK-RULES 10-27 rule 3).
A unit's sightings are counted per origin/main, never per re-run at the same sha (GATES-24).

THE BUILD'S VERDICT (`build`, GATES-24; cv 01a16f6d): standing.sh's whole-tree `lake build` reads
  ok      lake exit 0 and its `Build completed successfully (N jobs)` line;
  RED     the build FINISHED and FAILED: lake's own exit 1 with an `error:` line, nothing killed: what `record`
          attributes;
  ABSENT(killed: …)  the build did not finish: its cgroup scope was OOM-killed (the scope's journal, `Failed with
          result 'oom-kill'`, read by the unit name the build wrote from /proc/self/cgroup), or lake ended by a
          signal (exit >= 128), or lake wrote no `error:` line: never RED, never attributed (at 2d5056e and at
          743a4fb a 6 GB scope killed lean with no error line and both read build=RED, 84 reds attributed);
`--tool cargo` (standing's cargo check, clippy and fmt): ok on exit 0, RED on cargo's failure exits (101: a compile
error or a lint under -D warnings; 1: fmt's diff), ABSENT(killed: …) otherwise. A completed lake build's scope
memory peak is appended to --peaks (`sha12 epoch peak_bytes threads jobs`).
`floor` prints the whole-tree build's memory floor from that record: 1.25 x the largest peak of the last --days
(default 14) days, rounded up to a GiB, `FLOOR_BYTES text`; scripts/converge refuses a SWARM_MEM_MAX below it.
"""
import argparse
import json
import os
import re
import shutil
import subprocess
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import touched  # noqa: E402
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


# subject prefix -> the layer a landing's subject names, for the report's labels (gates/OWNERS maps paths to layers)
SUBJECT = {"kernel": {"KERNEL"}, "ledger": {"LEDGER"}, "codec": {"CODEC"}, "emit": {"CODEC"}, "host": {"HOST"},
           "protocol": {"PROTOCOL"}, "rows": {"PROTOCOL"}, "client": {"CLIENT"}, "sandbox": {"CLIENT"},
           "lang": {"LANG"}, "hosting": {"HOSTING"}, "ops": {"OPS"}, "perf": {"PERF"},
           "transport": {"TRANSPORT"}, "spec": {"SPEC"}, "gates": {"GATES"}, "build": {"GATES"}, "charter": {"ROOT"},
           "root": {"ROOT"}}


def owner_of(subject: str) -> str:
    m = re.match(r"([a-z]+)(?:\([^)]*\))?!?:", subject)
    if not m:
        return "ROOT"
    return "/".join(sorted(SUBJECT.get(m.group(1), {m.group(1).upper()})))


class Commit:
    def __init__(self, repo: str, sha: str):
        self.sha = sha
        body = git(repo, "log", "-1", "--format=%B", sha)
        self.subject = body.split("\n", 1)[0]
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
        bi = next((p for p in c.changed if p in touched.BUILD_INPUTS or p.endswith((".c", ".h"))), None)
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
        return [(c, "changed the Rust workspace") for c in cs if touched.crates(t.root, c.changed)]
    if unit.startswith("generated:"):
        out_path = unit.split(":", 1)[1]
        exe = gen.get(out_path, "")
        res = []
        for c in cs:
            if out_path in c.changed:
                res.append((c, f"changed {out_path}"))
            elif exe.startswith("cargo:") and touched.crates(t.root, c.changed):
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
            rs = {"run:" + m.group(1) for m in re.finditer(r"(?m)^  run (\S+).*?: RED", runs_out)
                  if m.group(1) != "concurrency"}
            # GATES-20g: a shared scratch is a red of both rows (`run concurrency A + B: RED(…)`)
            rs |= {"run:" + x for m in re.finditer(r"(?m)^  run concurrency (\S+) \+ (\S+): RED", runs_out)
                   for x in m.groups()}
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


def times(dir_: str, s12: str, runs_out: str) -> list[str]:
    """The TIMES and ROWS lines of a convergence: read from the standing's own time line and runs.py's own clock
    (never the read-set store's mtimes, which concurrent judges write)."""
    try:
        st = open(os.path.join(dir_, f"{s12}.times"), encoding="utf-8").read().strip()
    except OSError:
        st = "stages: (none: standing.sh wrote no time line)"
    rows = sorted(((int(n), r, w) for r, n, w in re.findall(r"(?m)^  time (\S+): (\d+) s \(([^)]*)\)$", runs_out)),
                  reverse=True)
    wall = re.search(r"(?m)^  runs wall: (\d+) s", runs_out)
    conc = re.search(r"(?m)^  concurrency: (.*)$", runs_out)
    carried = re.findall(r"(?m)^  carry (\S+): carried", runs_out)
    daily = re.findall(r"(?m)^  daily (\S+): ", runs_out)
    return [f"TIMES {st}",
            f"ROWS wall {wall.group(1) + 's' if wall else '?'}; {conc.group(1) if conc else 'concurrency: ?'}; "
            f"ran {len(rows)}: " + (", ".join(f"{r} {n}s ({w})" for n, r, w in rows) or "none")
            + f"; carried {len(carried)}" + (": " + ", ".join(carried) if carried else "")
            + f"; daily {len(daily)}" + (": " + ", ".join(daily) if daily else "")]


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
    for u in reds:
        att = attribute_unit(u, t, rows, a.traces, log, cs, gen)
        now_c = [c.sha for c, _ in att]
        e = state.get(u)
        if e is None:
            e = state[u] = {"first": now, "first_sha": sha, "commits": now_c, "seen": 0}
        if e.get("last_sha", e["first_sha"] if e["seen"] else None) != sha:
            e["seen"] += 1   # GATES-24: a sighting per main, never per re-run at the same main
        e["last_sha"] = sha
        h = (now - e["first"]) / 3600
        who = " | ".join(f"{c.label()} ({why})" for c, why in att) or "no commit of the range (ROOT)"
        out.append(f"RED {u} (red at {e['seen']} convergence(s) since {e['first_sha'][:12]}, {h:.1f} h): attributed to {who}")
    tmp = statep + f".{os.getpid()}"
    json.dump(state, open(tmp, "w", encoding="utf-8"), indent=1, sort_keys=True)
    os.replace(tmp, statep)
    head = (f"CONVERGENCE {s12} range {green[:12] + '..' if green else '(no GREEN standing in the log; the last 300) ..'}{s12} "
            f"landings={len(cs)} => {verdict} reds={len(reds)} fixed={len(fixed)} "
            f"at {time.strftime('%Y-%m-%dT%H:%MZ', time.gmtime(now))}")
    text = "\n".join([head] + times(a.dir, s12, runs_out) + out + fixed)
    print(text)
    with open(os.path.join(a.dir, "convergence.log"), "a", encoding="utf-8") as fh:
        fh.write(text + "\n")
    return 0


UNITS = {"K": 1 << 10, "M": 1 << 20, "G": 1 << 30, "T": 1 << 40}


def size_bytes(t: str) -> int | None:
    """`6G`, `13.2G`, `664.1M`, `24G`, `25769803776` -> bytes (systemd's and swarm-build's binary units)."""
    m = re.fullmatch(r"\s*([\d.]+)\s*([KMGT]?)i?B?\s*", t or "")
    return int(float(m.group(1)) * UNITS.get(m.group(2), 1)) if m else None


def gib(n: int) -> str:
    return f"{n / (1 << 30):.1f}G"


def scope_journal(unit: str, wait: float = 10.0) -> str:
    """The user journal of a finished transient scope, once systemd has written its `Consumed …` line."""
    end = time.monotonic() + wait
    while True:
        r = subprocess.run(["journalctl", "--user", "-u", unit, "-o", "cat", "--no-pager"],
                           capture_output=True, text=True)
        if "Consumed " in r.stdout or time.monotonic() >= end:
            return r.stdout
        time.sleep(1)


def build_cmd(a) -> int:
    out = open(a.out, encoding="utf-8", errors="replace").read() if os.path.exists(a.out) else ""
    try:
        cg = open(a.cgroup, encoding="utf-8").read().strip().splitlines()
    except OSError:
        cg = []
    unit = next((p.rsplit("/", 1)[-1] for p in cg if p.rstrip().endswith(".scope")), None)
    journal = scope_journal(unit) if unit and shutil.which("journalctl") else ""
    peak = re.search(r"Consumed .*?, ([\d.]+[KMGT]?) memory peak", journal)
    peak_b = size_bytes(peak.group(1)) if peak else None
    cap = os.environ.get("SWARM_MEM_MAX") or ("96G (swarm-build's default)" if unit else "none")
    jobs = re.search(r"Build completed successfully \((\d+) jobs?\)", out)
    last = None
    if a.peaks and os.path.exists(a.peaks):
        for l in open(a.peaks, encoding="utf-8"):
            f = l.split()
            if len(f) >= 5 and not l.startswith("#") and f[4].isdigit():
                last = f[4]
    oom = "oom-kill" in journal or "killed by the OOM killer" in journal
    where = f"scope {unit}, peak {peak.group(1) if peak else '?'} of SWARM_MEM_MAX {cap}" if unit else "no cgroup scope"
    plan = f"; the last completed build ran {last} jobs" if last else ""
    errs = [l for l in out.splitlines() if l.startswith("error:") or (a.tool == "cargo" and l.startswith("error"))]
    if a.tool == "cargo":
        # cargo check/clippy exit 101 on a compile error, fmt --check exits 1 on a diff: finished and failed
        if a.rc == 0 and not oom:
            print("ok")
            return 0
        if not oom and a.rc in (1, 101):
            print("RED")
            print(f"cargo: RED (exit {a.rc}; {where})", file=sys.stderr)
            return 0
        v = (f"ABSENT(killed: cgroup OOM, {where})" if oom else
             f"ABSENT(killed: cargo ended by signal {a.rc - 128}, {where})" if a.rc >= 128 else
             f"ABSENT(cargo exit {a.rc}, not a failure exit, {where})")
        print(v)
        print(f"cargo: {v} (never RED: GATES-24)", file=sys.stderr)
        return 0
    if a.rc == 0 and jobs and not oom:
        if a.peaks and peak_b:
            with open(a.peaks, "a", encoding="utf-8") as fh:
                fh.write(f"{(a.sha or '?')[:12]} {int(time.time())} {peak_b} {a.threads or '?'} {jobs.group(1)}\n")
        print("ok")
        print(f"build: ok ({jobs.group(1)} jobs; {where})", file=sys.stderr)
        return 0
    if oom:
        v = f"ABSENT(killed: cgroup OOM, {where}{plan})"
    elif a.rc >= 128:
        v = f"ABSENT(killed: lake ended by signal {a.rc - 128}, {where}{plan})"
    elif a.rc == 0:
        v = f"ABSENT(lake exit 0 without its completion line, {where})"
    elif not errs:
        v = f"ABSENT(the build did not finish: lake exit {a.rc} with no error line, {where}{plan})"
    elif any(re.search(r"exited with code (13[4-9]|14[0-3])|signal|Killed", l) for l in errs):
        v = f"ABSENT(killed: a lean process ended by a signal, {where}: {errs[0][:120]})"
    else:
        print("RED")
        print(f"build: RED (lake exit {a.rc}, {len(errs)} error line(s), first: {errs[0][:160]}; {where})",
              file=sys.stderr)
        return 0
    print(v)
    print(f"build: {v} (never RED: a build that did not finish proves nothing; GATES-24)", file=sys.stderr)
    return 0


def floor_cmd(a) -> int:
    now = time.time()
    best = None
    try:
        for l in open(a.peaks, encoding="utf-8"):
            f = l.split()
            if l.startswith("#") or len(f) < 3 or not f[1].isdigit() or not f[2].isdigit():
                continue
            if now - int(f[1]) <= a.days * 86400 and (best is None or int(f[2]) > best[0]):
                best = (int(f[2]), f[0], int(f[1]))
    except OSError:
        pass
    if best is None:
        fl = 16 << 30
        print(f"{fl} {gib(fl)} (no completed build recorded in {a.days} days in {a.peaks}: the fallback, from "
              f"FIX-CONVERGE's 10-24 journal measurement of 13.7G, the largest whole-tree build peak that day)")
        return 0
    fl = -(-int(best[0] * 1.25) // (1 << 30)) << 30
    print(f"{fl} {gib(fl)} (1.25 x the largest completed build peak recorded in {a.days} days, {gib(best[0])} at "
          f"{best[1]} {time.strftime('%Y-%m-%dT%H:%MZ', time.gmtime(best[2]))}; {a.peaks})")
    return 0


def main() -> int:
    ap = argparse.ArgumentParser()
    sub = ap.add_subparsers(dest="cmd", required=True)
    r = sub.add_parser("record")
    for x in ("--repo", "--sha", "--line", "--dir", "--tree", "--traces"):
        r.add_argument(x, required=True)
    r.add_argument("--now", type=int)
    b = sub.add_parser("build")
    b.add_argument("--tool", choices=("lake", "cargo"), default="lake")
    b.add_argument("--out", required=True)
    b.add_argument("--rc", type=int, required=True)
    b.add_argument("--cgroup", required=True)
    b.add_argument("--peaks")
    b.add_argument("--sha")
    b.add_argument("--threads")
    f = sub.add_parser("floor")
    f.add_argument("--peaks", required=True)
    f.add_argument("--days", type=int, default=14)
    a = ap.parse_args()
    return {"record": record, "build": build_cmd, "floor": floor_cmd}[a.cmd](a)


if __name__ == "__main__":
    sys.exit(main())
