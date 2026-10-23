#!/usr/bin/env python3
"""gates/certificate_plants.py SCRATCH [--harness-control] — prove the certificate pin can fail, and that it no
longer fails where the old whole-closure vector did (GATES-20u). A script row of gates/runs.tsv: the judge runs it
after the build; it builds nothing of the tree and writes only under SCRATCH.

Every plant is a scratch copy of the REAL Ledger/Proofs/GrantCap.lean, read now, with `import Census.Certificate`
added and `#certificate_pin` appended, elaborated by `lean -R` at SCRATCH/<plant> so its module is
Ledger.Proofs.GrantCap and its private names are the real ones. It imports the built oleans below GrantCap and not
GrantCap itself. Each mutation site must occur exactly as often as stated, or the plant is RED `site moved`.
  C0  no mutation: its pin equals the real environment's pin, section by section (the copy route is faithful).
  P1  a direct support's statement (`leftAt_of` flipped): RED in supports, naming it, and nowhere else.
  P2  a proof two levels down (`left_falls`, a dependency of the direct support `spends_le_left`): GREEN; a probe
      asserts its declaration changed and is a dependency of the support, so the old vector, which held the whole
      closure, would be RED. This is the over-pinning the pin removes.
  P3  vacuity: `MovesThrough … ∧ False` (every amount forced to 0): RED in vocabulary naming MovesThrough ONLY;
      statement, axioms and supports equal (a pin of those three alone reads this GREEN).
  P4  an axiom used two levels down: RED in axioms only.
  P5  the target's statement (`≤ left` → `≤ left + 0`): RED in statement.
  M   scratch copies of gates/certificate.py without the supports / vocabulary section read P1 / P3 GREEN.
--harness-control (GATES-15) additionally expects P2 RED, which it is not. Last line on success:
`CERTIFICATE PLANTS GREEN`.
"""
import argparse
import json
import os
from pathlib import Path
import subprocess
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
# No gates/__pycache__: rows run concurrently and another row reads gates/ (GATES-20g).
sys.dont_write_bytecode = True
sys.path.insert(0, str(HERE))
import certificate  # noqa: E402

TARGET = certificate.TARGET
MODULE = Path("Ledger/Proofs/GrantCap.lean")
PRIVATE = "_private.Ledger.Proofs.GrantCap.0.Nanodregg.Ledger.Proofs."

# (old, new, occurrences) or ("region", start, end, new): [start, end) replaced; each anchor occurs once.
PLANTS = {
    "C0": [],
    "P1": [(": leftAt base E g w = l := by", ": l = leftAt base E g w := by", 1),
           ("rw [leftAt_of hl hll, leftAt_of hl' hll']", "rw [← leftAt_of hl hll, ← leftAt_of hl' hll']", 3),
           ("rwa [leftAt_of hl hleft] at this", "rwa [← leftAt_of hl hleft] at this", 2)],
    "P2": [("· rw [leftAt_none hn]; exact Nat.zero_le _",
            "· rw [leftAt_none hn]; exact Nat.le_trans (Nat.zero_le 0) (Nat.zero_le _)", 1)],
    "P3": [("Dispatched X o c n wk actor (.transfer src dst a (some g) once)\n",
            "Dispatched X o c n wk actor (.transfer src dst a (some g) once) ∧ False\n", 1),
           ("region", "  obtain ⟨t, c, k, wk, actor, src, dst, once, rfl, hdec, hd⟩ := hm",
            "\n/-- A credit line through `g` weighs",
            "  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hfalse⟩ := hm\n  exact hfalse.elim\n")],
    "P4": [("/-- What is left at `g` never rises along a step. -/",
            "axiom g2_plant_axiom : True\n\n/-- What is left at `g` never rises along a step. -/", 1),
           ("    leftAt base X.env g n ≤ leftAt base X.env g o := by\n",
            "    leftAt base X.env g n ≤ leftAt base X.env g o := by\n  have _hax := g2_plant_axiom\n", 1)],
    "P5": [("≤ left := by\n  obtain ⟨steps, hmap, hc⟩ := audit_grant_chain hcan hlc (.inl ⟨cell, hl, hk⟩) h\n"
            "  refine ⟨steps, hmap, hc, fun amt hf => ?_⟩\n  have := spends_le_left (.inr (.inl rfl))",
            "≤ left + 0 := by\n  obtain ⟨steps, hmap, hc⟩ := audit_grant_chain hcan hlc (.inl ⟨cell, hl, hk⟩) h\n"
            "  refine ⟨steps, hmap, hc, fun amt hf => ?_⟩\n  have := spends_le_left (.inr (.inl rfl))", 1)],
}

# P2's probe: the declaration of `left_falls` and the dependencies of the direct support `spends_le_left`.
PROBE = r'''
open Lean Elab Command in
elab "#certificate_plant_probe " p:str : command => do
  let env ← getEnv
  let find (n : Name) (s : String) :=
    (((Census.Certificate.lookup env n).map (·.dependencies)).getD []).find? (·.toString == s)
  let some support := find `Nanodregg.Ledger.Proofs.grant_moves_le_cap "SUPPORT"
    | throwError "probe: SUPPORT is not a support of the target"
  let some deep := find support "DEEP"
    | throwError "probe: DEEP is not a dependency of SUPPORT"
  let some d := Census.Certificate.lookup env deep | throwError "probe: no declaration for DEEP"
  IO.FS.writeFile p.getString (Json.mkObj [("payload", toJson d.payload)]).compress
'''.replace("SUPPORT", PRIVATE + "spends_le_left").replace("DEEP", PRIVATE + "left_falls")


class Red(Exception):
    pass


def mutate(src: str, plant: str) -> str:
    for m in PLANTS[plant]:
        if m[0] == "region":
            _, a, b, new = m
            if src.count(a) != 1 or src.count(b) != 1 or src.index(a) > src.index(b):
                raise Red(f"plant {plant} site moved: region {a!r} .. {b!r}")
            src = src[:src.index(a)] + new + src[src.index(b):]
        else:
            old, new, k = m
            if src.count(old) != k:
                raise Red(f"plant {plant} site moved: {old!r} occurs {src.count(old)} times, expected {k}")
            src = src.replace(old, new)
    return src


def emit_plant(scratch: Path, plant: str) -> tuple[dict, dict]:
    where = scratch / plant
    (where / MODULE.parent).mkdir(parents=True, exist_ok=True)
    out, probe = where / "certificate.json", where / "probe.json"
    src = mutate((ROOT / MODULE).read_text(), plant)
    src = ("import Census.Certificate\n" + src + "\n" + PROBE + "\n#certificate_pin " + json.dumps(str(out)) + " "
           + TARGET + "\n#certificate_plant_probe " + json.dumps(str(probe)) + "\n")
    source = where / MODULE
    source.write_text(src)
    try:
        certificate.run_lean(where, source, ["-R", str(where)])
    except SystemExit as e:
        raise Red(f"plant {plant}: {e}")
    return json.loads(out.read_text()), json.loads(probe.read_text())


def red_sections(a: dict, b: dict) -> dict[str, str]:
    """The sections of pin b that differ from pin a, with the comparator's line for each."""
    lines = certificate.differences(a, b)
    return {line.split(" ")[0]: line for line in lines}


def mutant_reads(scratch: Path, drop: str, before: Path, after: Path) -> int:
    source = (HERE / "certificate.py").read_text()
    line = 'SECTIONS = ("statement", "axioms", "supports", "vocabulary")'
    if source.count(line) != 1:
        raise Red(f"mutant: `{line}` occurs {source.count(line)} times in gates/certificate.py, expected 1")
    kept = ", ".join(f'"{s}"' for s in certificate.SECTIONS if s != drop)
    path = scratch / f"certificate_without_{drop}.py"
    path.write_text(source.replace(line, f"SECTIONS = ({kept},)"))
    log = scratch / f"mutant-{drop}.log"
    with open(log, "w") as fh:
        code = subprocess.run([sys.executable, "-B", str(path), str(scratch), "--check-json", str(before), str(after)],
                              cwd=ROOT, stdout=fh, stderr=subprocess.STDOUT).returncode
    print(log.read_text(), end="")
    return code


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("scratch", type=Path)
    ap.add_argument("--harness-control", action="store_true")
    a = ap.parse_args()
    scratch = a.scratch.resolve()
    scratch.mkdir(parents=True, exist_ok=True)
    red: list[str] = []
    try:
        real = certificate.digest(certificate.emit(scratch / "real"))
        emitted = {p: emit_plant(scratch, p) for p in PLANTS}
        pins = {p: certificate.digest(e) for p, (e, _) in emitted.items()}
        c0 = pins["C0"]

        def expect(plant: str, want: dict[str, str], why: str = "") -> None:
            got = red_sections(c0, pins[plant])
            ok = sorted(got) == sorted(want) and all(w in got[s] for s, w in want.items())
            print(f"PLANT {plant} {'as required' if ok else 'WRONG'}: "
                  + (" | ".join(got.values()) if got else "GREEN") + f" (required: {want or 'GREEN'})")
            if not ok:
                red.append(f"plant {plant}{why}: read {sorted(got) or 'GREEN'}, required {sorted(want) or 'GREEN'}")

        got = certificate.differences(real, c0)
        print("PLANT C0 " + ("as required: equal to the real environment's pin" if not got else "WRONG: " + " | ".join(got)))
        if got:
            red.append("plant C0: the copy's pin differs from the real environment's: " + " | ".join(got))
        expect("P1", {"supports": PRIVATE + "leftAt_of"})
        expect("P2", {"statement": ""} if a.harness_control else {},
               " (harness-control: P2 is required RED in statement, which nothing meets)" if a.harness_control else "")
        before, after = emitted["C0"][1]["payload"], emitted["P2"][1]["payload"]
        print("PLANT P2 probe: left_falls's declaration " + ("changed" if before != after else "UNCHANGED")
              + "; it is a dependency of the direct support spends_le_left, so the old whole-closure vector would have refused it")
        if before == after:
            red.append("plant P2: the probe saw no change in left_falls: the mutation did not happen")
        expect("P3", {"vocabulary": "changed ['Nanodregg.Ledger.Proofs.MovesThrough']"})
        expect("P4", {"axioms": "added ['Nanodregg.Ledger.Proofs.g2_plant_axiom'] removed []"})
        expect("P5", {"statement": "statement", "supports": "added", "vocabulary": "added"})
        for drop, plant in (("supports", "P1"), ("vocabulary", "P3")):
            code = mutant_reads(scratch, drop, scratch / "C0/certificate.json", scratch / plant / "certificate.json")
            print(f"PLANT M-{drop}: {'as required' if code == 0 else 'WRONG'}: without the {drop} section {plant} "
                  f"{'escapes' if code == 0 else f'still reads exit {code}'}")
            if code != 0:
                red.append(f"mutant {drop}: {plant} did not escape (exit {code})")
    except Red as e:
        red.append(str(e))
    for r in red:
        print("CERTIFICATE PLANTS RED: " + r)
    print("CERTIFICATE PLANTS " + (f"RED ({len(red)})" if red else "GREEN"))
    return 1 if red else 0


if __name__ == "__main__":
    sys.exit(main())
