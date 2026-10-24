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
other than its value) is red; a pinned row that nothing measured is red (a ceiling over nothing
checks nothing); a measurement with no row is listed as unpinned (pin it: add the row with ceiling =
measured).

`--plants` (a gates/runs.tsv script row; GATES-20x): over the tree's own table, every exact row measured at
its value is ok, and each one measured one off it is RED by name (one below; one above a 0: THE BAR's stale
rows read 0/0/1, and 0/0/0 is two of those, which a ceiling passed); an exact row moved, or made a ceiling, without a WASTE line is RED, and with one is ok.
Last line `WASTE PLANTS GREEN`.
"""
import argparse
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


def measured_check(text: str, measured: str, partial: bool = False) -> tuple[list[str], list[str]]:
    """partial (pre-push, which runs only the exes a commit can affect): a pinned row nothing
    measured is not red; a measured row above its ceiling still is."""
    rows = parse(text)
    seen = {}
    for line in measured.splitlines():
        p = line.split()
        if len(p) == 4 and p[0] == "WASTE":
            seen[(p[1], p[2])] = max(float(p[3]), seen.get((p[1], p[2]), 0.0))
    red, unpinned = [], []
    for key, (ceil, _, src, exact) in rows.items():
        if key not in seen:
            if partial:
                continue
            red.append(f"waste {key[0]} {key[1]}: pinned ({'exactly' if exact else 'ceiling'} {ceil}) but nothing "
                       f"measured it this run")
        elif why := breach(seen[key], ceil, exact):
            red.append(f"waste {key[0]} {key[1]}: measured {why}")
    for key, v in sorted(seen.items()):
        if key not in rows:
            unpinned.append(f"{key[0]}\t{key[1]}\t{v}")
    return red, unpinned


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
    (op, m), (v, *_rest) = sorted(exact.items())[0]
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
    a = ap.parse_args()
    path = os.path.join(a.root, "gates", "waste.tsv")
    text = open(path, encoding="utf-8").read() if os.path.exists(path) else ""
    base = open(a.base, encoding="utf-8").read() if a.base and os.path.exists(a.base) else ""
    msg = open(a.message, encoding="utf-8").read() if a.message else ""
    if a.measured:
        red, unpinned = measured_check(text, open(a.measured, encoding="utf-8").read(), a.partial)
        for r in red:
            print(r)
        for u in unpinned:
            print("unpinned", u)
        print(f"waste-measured: {'RED' if red else 'ok'} ({len(parse(text))} pinned, {len(unpinned)} unpinned)")
        sys.exit(1 if red else 0)
    red = check(text, base, msg)
    for r in red:
        print(r)
    print(f"waste: {'RED' if red else 'ok'} ({len(parse(text)) if not red else '?'} ops pinned)")
    sys.exit(1 if red else 0)
