#!/usr/bin/env python3
"""gates/waste.py TREE [--base WASTE.tsv-of-parent] [--message FILE] — the waste ratchet (law 5).

gates/waste.tsv rows: `op<TAB>metric<TAB>ceiling<TAB>measured<TAB>source`, where `measured`
is the work an operation does divided by the work it must do (a waste ratio, >= 1), and
`source` names the measurement (`perf stat --no-scale` log, sim run, commit). A ceiling written `=V`
is EXACT (GATES-20x): the fact is an equality, so a measurement below it is as red as one above
(THE BAR's forced contention is exactly one stale write, one re-run, no stale re-run: 0/0/0 is the
contention not happening, which a ceiling passes). Red on:
  - measured above ceiling; for an exact row, measured other than V;
  - a ceiling raised against the parent, a row removed, or an exact row's value changed or made a
    ceiling, without `WASTE: <op>: <why>` in the commit message (ceilings only fall);
  - a malformed row.
An empty table is not red; scripts/standing.sh reports how many operations are pinned.

`--measured FILE` (scripts/standing.sh): FILE holds `WASTE <op> <metric> <value>` lines that
the simulations and benches print. A pinned (op, metric) measured above its ceiling (an exact row:
other than its value) is red; a measurement with no row is listed as unpinned (pin it: add the row
with ceiling = measured). A pinned row that nothing measured is one of two things (GATES-24), and
`--runs-out FILE --traces DIR` (standing's runs output and the read-set store) tell them apart:
  RED     `waste OP M: pinned … but nothing measured it this run (…)`: a row that measures it (its newest
          stored read-set's W names it) ran to an ok verdict and printed no measurement: a ceiling over
          nothing checks nothing; or no stored read-set names its row and every row of gates/runs.tsv
          ran ok;
  ABSENT  `waste-absent OP M: …`: the runs did not run or did not finish (FILE absent, or no `runs:`
          line), or every row that measures it did not reach an ok verdict (KILLED, UNREAD, INCOMPLETE,
          not run, or RED: that row's own red is the unit; its missing measurement is not a second
          one), or no read-set names its row while some row did not run ok. Never RED: a measurement
          that was not taken did not fail (two convergences read 83 such rows RED, cv 01a16f6d).
Without --runs-out every unmeasured pinned row is RED, as before (the old caller). Exit 0 ok, 1 RED (a measured
breach or a RED unmeasured row), 3 ABSENT (nothing red, some pinned row not measured).

`--plants` (a gates/runs.tsv script row; GATES-20x): over the tree's own table, every exact row measured at
its value is ok, and each one measured one off it is RED by name (one below; one above a 0: THE BAR's stale
rows read 0/0/1, and 0/0/0 is two of those, which a ceiling passed); an exact row moved, or made a ceiling, without a WASTE line is RED, and with one is ok.
Last line `WASTE PLANTS GREEN`.
"""
import argparse
import json
import os
import re
import sys


def parse(text: str) -> dict:
    """(op, metric) -> (ceiling, measured, source, exact)."""
    rows = {}
    for n, line in enumerate(text.splitlines(), 1):
        if not line.strip() or line.startswith("#"):
            continue
        p = line.split("\t")
        if len(p) != 5 or not all(x.strip() for x in p):
            raise ValueError(f"waste.tsv:{n}: need op, metric, ceiling, measured, source: {line!r}")
        exact = p[2].startswith("=")
        rows[(p[0], p[1])] = (float(p[2][1:] if exact else p[2]), float(p[3]), p[4], exact)
    return rows


def breach(value: float, ceil: float, exact: bool) -> str | None:
    """Why VALUE breaks the row, or None."""
    if exact:
        return None if value == ceil else f"{value} != exactly {ceil}"
    return f"{value} > ceiling {ceil}" if value > ceil else None


def row_status(runs_out: str | None) -> dict[str, str] | None:
    """runs.py's output -> {row: ok|red|absent} for every row it printed; None when the runs did not finish (no
    output, or no final `runs:` line). A carried row is ok; a row is ok when it has a run line and every one of
    them (its control excepted) reads ok; red when one reads RED; absent otherwise (KILLED, UNREAD, INCOMPLETE)."""
    if not runs_out or not re.search(r"(?m)^runs: ", runs_out):
        return None
    lines: dict[str, list[str]] = {}
    carried = set()
    for m in re.finditer(r"(?m)^  carry (\S+): carried", runs_out):
        carried.add(m.group(1))
    for m in re.finditer(r"(?m)^  run (\S+)(.*?): (\S.*)$", runs_out):
        row, mid, v = m.groups()
        if row == "concurrency" or "(control)" in mid:
            continue
        lines.setdefault(row, []).append(v)
    out = {}
    for row in set(lines) | carried:
        vs = lines.get(row, [])
        if any(v.startswith("RED") for v in vs):
            out[row] = "red"
        elif row in carried or (vs and all(v.startswith("ok") for v in vs)):
            out[row] = "ok"
        else:
            out[row] = "absent"
    return out


def measurers(traces: str | None, rows: list[str]) -> dict[tuple[str, str], set[str]]:
    """(op, metric) -> the rows whose newest stored read-set that names waste rows (readset W, GATES-20e) names it."""
    out: dict[tuple[str, str], set[str]] = {}
    if not traces:
        return out
    for row in rows:
        d = os.path.join(traces, re.sub(r"[^A-Za-z0-9_.-]", "_", row))
        try:
            names = [n for n in os.listdir(d) if n.endswith(".json") and not n.startswith(".")]
        except OSError:
            continue
        for n in sorted(names, key=lambda n: os.path.getmtime(os.path.join(d, n)), reverse=True):
            try:
                w = (json.load(open(os.path.join(d, n), encoding="utf-8")).get("readset") or {}).get("W")
            except (OSError, ValueError):
                continue
            if w:
                for x in w:
                    op, _, metric = x.partition("\t")
                    out.setdefault((op, metric), set()).add(row)
                break
    return out


def measured_check(text: str, measured: str, partial: bool = False, status: dict[str, str] | None = None,
                   who: dict[tuple[str, str], set[str]] | None = None, table_rows: list[str] | None = None,
                   judged: bool = False) -> tuple[list[str], list[str], list[str]]:
    """(red, unpinned, absent). partial (a run of only some exes): a pinned row
    nothing measured is neither. judged (standing with --runs-out): an unmeasured row is RED only when a row that
    measures it ran ok (status, who; table_rows: every row of gates/runs.tsv), else ABSENT; status None: the runs
    did not finish, every unmeasured row is ABSENT. Not judged: every unmeasured row is RED (the old caller)."""
    rows = parse(text)
    seen = {}
    for line in measured.splitlines():
        p = line.split()
        if len(p) == 4 and p[0] == "WASTE":
            seen[(p[1], p[2])] = max(float(p[3]), seen.get((p[1], p[2]), 0.0))
    red, unpinned, absent = [], [], []
    who = who or {}
    for key, (ceil, _, src, exact) in rows.items():
        if key not in seen:
            if partial:
                continue
            pin = f"pinned ({'exactly' if exact else 'ceiling'} {ceil})"
            if not judged:
                red.append(f"waste {key[0]} {key[1]}: {pin} but nothing measured it this run")
                continue
            if status is None:
                absent.append(f"waste-absent {key[0]} {key[1]}: {pin}, not measured: the runs did not run or did not "
                              f"finish (ABSENT, not RED)")
                continue
            r = sorted(who.get(key, set()))
            ran = [x for x in r if status.get(x) == "ok"]
            if ran:
                red.append(f"waste {key[0]} {key[1]}: {pin} but nothing measured it this run (its row "
                           f"{', '.join(ran)} ran ok)")
            elif r:
                absent.append(f"waste-absent {key[0]} {key[1]}: {pin}, not measured: its row "
                              + ", ".join(f"{x} ({status.get(x, 'not run')})" for x in r)
                              + " did not run to an ok verdict (ABSENT, not RED)")
            else:
                notok = [x for x in (table_rows or sorted(status)) if status.get(x) != "ok"]
                if notok:
                    absent.append(f"waste-absent {key[0]} {key[1]}: {pin}, not measured: no stored read-set names "
                                  f"its row, and {len(notok)} row(s) did not run ok ({', '.join(notok[:4])}"
                                  f"{', …' if len(notok) > 4 else ''}) (ABSENT, not RED)")
                else:
                    red.append(f"waste {key[0]} {key[1]}: {pin} but nothing measured it this run (no stored read-set "
                               f"names its row, and every row ran ok)")
        elif why := breach(seen[key], ceil, exact):
            red.append(f"waste {key[0]} {key[1]}: measured {why}")
    for key, v in sorted(seen.items()):
        if key not in rows:
            unpinned.append(f"{key[0]}\t{key[1]}\t{v}")
    return red, unpinned, absent


def check(text, base_text, message) -> list[str]:
    try:
        rows = parse(text)
        base = parse(base_text) if base_text else {}
    except ValueError as e:
        return [str(e)]
    red = []
    for (op, metric), (ceil, measured, src, exact) in rows.items():
        if why := breach(measured, ceil, exact):
            red.append(f"waste {op} {metric}: measured {why} ({src[:80]})")
    for key, (b_ceil, _, _, b_exact) in base.items():
        op = key[0]
        justified = re.search(r"(?m)^WASTE:\s*" + re.escape(op) + r"\s*:\s*\S", message)
        if justified:
            continue
        if key not in rows:
            red.append(f"waste {op} {key[1]}: row removed; needs 'WASTE: {op}: <why>'")
        elif b_exact and (not rows[key][3] or rows[key][0] != b_ceil):
            red.append(f"waste {op} {key[1]}: exactly {b_ceil} -> {'exactly ' if rows[key][3] else 'ceiling '}"
                       f"{rows[key][0]}; an exact row moves only by 'WASTE: {op}: <why>'")
        elif rows[key][0] > b_ceil:
            red.append(f"waste {op} {key[1]}: ceiling raised {b_ceil} -> {rows[key][0]}; needs 'WASTE: {op}: <why>'")
    return red


def plants(text: str, control: bool) -> int:
    rows = parse(text)
    exact = {k: v for k, v in rows.items() if v[3]}
    bad = []

    def expect(name: str, reds: list[str], want: str | None) -> None:
        ok = (not reds) if want is None else any(want in r for r in reds)
        print(f"  {name}: {'ok' if ok else 'FAIL'} (want {want or 'GREEN'}){'' if ok else ': ' + '; '.join(reds)}")
        if not ok:
            bad.append(name)
    if not exact:
        print("WASTE PLANTS RED: the table pins no exact row")
        return 1
    at = "".join(f"WASTE {op} {m} {v[0]}\n" for (op, m), v in rows.items())
    expect("exact-at-value", measured_check(text, at)[0], None)
    for (op, m), (v, *_rest) in sorted(exact.items()):
        off = v - 1 if v >= 1 else v + 1           # a count: one below its value, or above a 0
        other = at.replace(f"WASTE {op} {m} {v}\n", f"WASTE {op} {m} {off}\n")
        expect(f"exact-off {op} {m}", measured_check(text, other)[0], f"waste {op} {m}: measured {off} != exactly {v}")
    # GATES-24: an unmeasured row is ABSENT when the row that measures it did not run, RED when it ran ok, and
    # ABSENT for every row when the runs did not finish
    (op, m), (v, *_rest) = sorted(exact.items())[0]
    gone = at.replace(f"WASTE {op} {m} {v}\n", "")
    who = {(op, m): {"plant-row"}}
    expect("unmeasured-row-ran-ok", measured_check(text, gone, status={"plant-row": "ok"}, who=who, judged=True)[0],
           f"waste {op} {m}: pinned (exactly {v}) but nothing measured it this run (its row plant-row ran ok)")
    for st in ("absent", "red"):
        r, _, ab = measured_check(text, gone, status={"plant-row": st}, who=who, judged=True)
        expect(f"unmeasured-row-{st}", r + ([] if any(f"waste-absent {op} {m}: " in x for x in ab)
                                            else ["no ABSENT line"]), None)
    r, _, ab = measured_check(text, "", status=None, judged=True)
    expect("runs-did-not-finish", r + ([] if len(ab) == len(rows) else [f"{len(ab)} ABSENT of {len(rows)}"]), None)
    line = next(l for l in text.splitlines() if l.startswith(f"{op}\t{m}\t="))
    f = line.split("\t")
    moved = text.replace(line, "\t".join([f[0], f[1], f"={v + 1}", str(v + 1), f[4]]))
    loose = text.replace(line, "\t".join([f[0], f[1], f[2][1:], f[3], f[4]]))
    expect("exact-moved", check(moved, text, ""), f"waste {op} {m}: exactly {v} -> exactly {v + 1}")
    expect("exact-moved-declared", check(moved, text, f"WASTE: {op}: the plant\n"), None)
    expect("exact-made-ceiling", check(loose, text, ""), f"waste {op} {m}: exactly {v} -> ceiling {v}")
    if control:
        expect("harness-control", [], "harness-control: nothing reads this")
    print(f"WASTE PLANTS {'GREEN' if not bad else 'RED (' + str(len(bad)) + '): ' + ' '.join(bad)}")
    return 1 if bad else 0


if __name__ == "__main__":
    if len(sys.argv) >= 2 and sys.argv[1] == "--plants":
        here = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
        sys.exit(plants(open(os.path.join(here, "gates", "waste.tsv"), encoding="utf-8").read(),
                        "--harness-control" in sys.argv))
    ap = argparse.ArgumentParser()
    ap.add_argument("root", nargs="?", default=".")
    ap.add_argument("--base")
    ap.add_argument("--message")
    ap.add_argument("--measured")
    ap.add_argument("--partial", action="store_true", help="with --measured: unmeasured pinned rows are not red")
    ap.add_argument("--runs-out", help="with --measured: standing's runs output (GATES-24: ABSENT vs RED per row)")
    ap.add_argument("--traces", help="with --runs-out: the read-set store (which row measures which waste row)")
    a = ap.parse_args()
    path = os.path.join(a.root, "gates", "waste.tsv")
    text = open(path, encoding="utf-8").read() if os.path.exists(path) else ""
    base = open(a.base, encoding="utf-8").read() if a.base and os.path.exists(a.base) else ""
    msg = open(a.message, encoding="utf-8").read() if a.message else ""
    if a.measured:
        status = table_rows = None
        if a.runs_out is not None:
            try:
                status = row_status(open(a.runs_out, encoding="utf-8", errors="replace").read())
            except OSError:
                status = None
            sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
            import runs  # noqa: E402
            try:
                table_rows = sorted(runs.table(a.root))
            except ValueError:
                table_rows = []
        red, unpinned, absent = measured_check(
            text, open(a.measured, encoding="utf-8").read() if os.path.exists(a.measured) else "", a.partial,
            status, measurers(a.traces, table_rows or []), table_rows, judged=a.runs_out is not None)
        for r in red + absent:
            print(r)
        for u in unpinned:
            print("unpinned", u)
        word = "RED" if red else "ABSENT" if absent else "ok"
        print(f"waste-measured: {word} ({len(parse(text))} pinned, {len(red)} red, {len(absent)} absent, "
              f"{len(unpinned)} unpinned)")
        sys.exit(1 if red else 3 if absent else 0)
    red = check(text, base, msg)
    for r in red:
        print(r)
    print(f"waste: {'RED' if red else 'ok'} ({len(parse(text)) if not red else '?'} ops pinned)")
    sys.exit(1 if red else 0)
