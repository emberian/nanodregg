"""gates/waste.py TREE [--base WASTE.tsv-of-parent] [--message FILE] — the waste ratchet (law 5).

gates/waste.tsv rows: `op<TAB>metric<TAB>ceiling<TAB>measured<TAB>source`, where `measured`
is the work an operation does divided by the work it must do (a waste ratio, >= 1), and
`source` names the measurement (`perf stat --no-scale` log, sim run, commit). Red on:
  - measured above ceiling;
  - a ceiling raised against the parent, or a row removed, without `WASTE: <op>: <why>` in the
    commit message (ceilings only fall);
  - a malformed row.
An empty table is not red; scripts/standing.sh reports how many operations are pinned.
"""
import argparse
import os
import re
import sys


def parse(text: str) -> dict:
    rows = {}
    for n, line in enumerate(text.splitlines(), 1):
        if not line.strip() or line.startswith("#"):
            continue
        p = line.split("\t")
        if len(p) != 5 or not all(x.strip() for x in p):
            raise ValueError(f"waste.tsv:{n}: need op, metric, ceiling, measured, source: {line!r}")
        rows[(p[0], p[1])] = (float(p[2]), float(p[3]), p[4])
    return rows


def check(text, base_text, message) -> list[str]:
    try:
        rows = parse(text)
        base = parse(base_text) if base_text else {}
    except ValueError as e:
        return [str(e)]
    red = []
    for (op, metric), (ceil, measured, src) in rows.items():
        if measured > ceil:
            red.append(f"waste {op} {metric}: measured {measured} > ceiling {ceil} ({src})")
    for key, (b_ceil, _, _) in base.items():
        op = key[0]
        justified = re.search(r"(?m)^WASTE:\s*" + re.escape(op) + r"\s*:\s*\S", message)
        if key not in rows and not justified:
            red.append(f"waste {op} {key[1]}: row removed; needs 'WASTE: {op}: <why>'")
        elif key in rows and rows[key][0] > b_ceil and not justified:
            red.append(f"waste {op} {key[1]}: ceiling raised {b_ceil} -> {rows[key][0]}; needs 'WASTE: {op}: <why>'")
    return red


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("root", nargs="?", default=".")
    ap.add_argument("--base")
    ap.add_argument("--message")
    a = ap.parse_args()
    path = os.path.join(a.root, "gates", "waste.tsv")
    text = open(path, encoding="utf-8").read() if os.path.exists(path) else ""
    base = open(a.base, encoding="utf-8").read() if a.base and os.path.exists(a.base) else ""
    msg = open(a.message, encoding="utf-8").read() if a.message else ""
    red = check(text, base, msg)
    for r in red:
        print(r)
    print(f"waste: {'RED' if red else 'ok'} ({len(parse(text)) if not red else '?'} ops pinned)")
    sys.exit(1 if red else 0)
