#!/usr/bin/env python3
"""gates/statement_plants.py SCRATCH [--harness-control] — prove the statement census can fail (GATES-20s).

Over the BUILT tree (a script row of gates/runs.tsv, so the judge runs it after the build; it builds nothing of
the tree), in SCRATCH only:
  plant    a module `StatementPlant.Vacuous` (outside every lib) holding three real vacuous theorems with
           `chain_binds`'s binders and premises, each proved from `E.Lawful` alone by pigeonhole (KERNEL-56's
           logs/kernel21-ver-pigeon.lean): the escape inline, through an alias, and as `∃ S, CollidesAmong hash S`;
           and a control, the landed `chain_binds` statement over `chainPres`. The census over the tree plus the
           plant must read `STATEMENT-CENSUS RED (3)` naming exactly the three, with the control's row ok.
  control  the census over the tree alone must read `STATEMENT-CENSUS ok`.
  mutant   a scratch copy of Census/Statements.lean with the two-chosen-sides test disabled must be refused by
           its own fixtures (`STATEMENT-CENSUS harness:`), so the in-run fixtures are planted too.
  reach    the fast judge's census (GATES-20v (c): `#axiom_census_in`, `#statement_census_in` over a landing's
           reach): over the plant module alone it must read the plant's `native_decide` theorem, which has no allow
           row, `AXIOM-CENSUS red` by name, and the three vacuous theorems `STATEMENT-CENSUS RED (3)`; over a tree
           module (Kernel.Proofs.Fold) it must read both ok.
--harness-control (GATES-15) adds one expectation nothing meets, a fourth RED the plant does not hold, judged on
the same comparison. Last line on success: `STATEMENT PLANTS GREEN`.
"""
import argparse
import os
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
# No gates/__pycache__: rows run concurrently and another row reads gates/ (GATES-20g's shared-scratch RED).
sys.dont_write_bytecode = True
sys.path.insert(0, HERE)
import census  # noqa: E402
import tree  # noqa: E402

PLANT_ROOT = "StatementPlant"
VACUOUS = ["chain_binds_inline", "chain_binds_alias", "chain_binds_chosen_list"]
CONTROL_THM = "chain_binds_named"
NS = "Nanodregg.Kernel.StatementPlant."

PLANT = r'''import Kernel.Proofs.Fold

/-! gates/statement_plants.py's plant (never in the tree): three vacuous theorems the statement census must
name RED, and the landed `chain_binds` statement it must read ok. -/

namespace Nanodregg.Kernel.StatementPlant
open Nanodregg.Kernel
variable {D : Type}

def enc : List UInt8 → Nat
  | [] => 0
  | b :: l => b.toNat + 256 * enc l

theorem enc_lt : ∀ l : List UInt8, enc l < 256 ^ l.length
  | [] => by simp [enc]
  | b :: l => by
      have := enc_lt l; have hb := b.toNat_lt
      simp only [enc, List.length_cons, Nat.pow_succ]; omega

theorem enc_inj : ∀ a b : List UInt8, a.length = b.length → enc a = enc b → a = b
  | [], [], _, _ => rfl
  | x :: a, y :: b, hl, h => by
      simp only [enc] at h
      have hx := x.toNat_lt; have hy := y.toNat_lt
      have h1 : x.toNat = y.toNat := by omega
      have h2 : enc a = enc b := by omega
      rw [enc_inj a b (by simpa using hl) h2, UInt8.toNat_inj.mp h1]

theorem nodup_lt_len : ∀ (M : Nat) (l : List Nat), l.Nodup → (∀ x ∈ l, x < M) → l.length ≤ M
  | 0, [], _, _ => Nat.le_refl 0
  | 0, x :: _, _, h => absurd (h x (by simp)) (Nat.not_lt_zero _)
  | M + 1, l, hn, h => by
      have ih := nodup_lt_len M (l.erase M) (hn.erase M) (by
        intro x hx; rw [hn.mem_erase_iff] at hx; have := h x hx.2; omega)
      have := List.length_erase_le (a := M) (l := l)
      by_cases hm : M ∈ l
      · rw [List.length_erase_of_mem hm] at ih; omega
      · rw [List.erase_of_not_mem hm] at ih; omega

/-- Every lawful Env collides on two inputs it may choose (pigeonhole: digests are n ≤ 32 bytes). -/
theorem lawful_collides [Ord D] {E : Env D} {n : Nat} (hE : E.Lawful n) :
    ∃ (dom : String) (a b : ByteArray), a ≠ b ∧ E.hash dom a = E.hash dom b := by
  apply Classical.byContradiction
  intro hno
  have hinj : ∀ a b, E.hash "x" a = E.hash "x" b → a = b := by
    intro a b h; apply Classical.byContradiction; intro hne; exact hno ⟨"x", a, b, hne, h⟩
  let z : Nat → ByteArray := fun i => ⟨Array.replicate i 0⟩
  let f : Nat → Nat := fun i => enc (E.bytes (E.hash "x" (z i))).data.toList
  have flt : ∀ i, f i < 256 ^ n := by
    intro i; have := enc_lt (E.bytes (E.hash "x" (z i))).data.toList
    simpa [hE.size] using this
  have finj : ∀ i j, f i = f j → i = j := by
    intro i j h
    have h1 := enc_inj _ _ (by simp [hE.size]) h
    have h2 : E.bytes (E.hash "x" (z i)) = E.bytes (E.hash "x" (z j)) := by
      cases hb : E.bytes (E.hash "x" (z i)); cases hb' : E.bytes (E.hash "x" (z j))
      simp_all
    have h3 := hinj _ _ (hE.bytes_inj h2)
    have : (z i).size = (z j).size := by rw [h3]
    simpa [z] using this
  have hnd : ((List.range (256 ^ n + 1)).map f).Nodup :=
    List.Pairwise.map f (fun a b hab h => hab (finj a b h)) List.nodup_range
  have := nodup_lt_len (256 ^ n) _ hnd (by
    intro x hx; simp only [List.mem_map] at hx; obtain ⟨i, -, rfl⟩ := hx; exact flt i)
  simp at this; omega

/-- The pre-KERNEL-56 escape under another name. -/
def Escape (hash : String → ByteArray → D) : Prop :=
  ∃ (dom : String) (a b : ByteArray), a ≠ b ∧ hash dom a = hash dom b

/-- RED: the deleted escape written inline; no chain premise is used. -/
theorem chain_binds_inline [Ord D] {E : Env D} {n : Nat} (hE : E.Lawful n) {c : D} :
    ∀ (k : Nat) (l₁ l₂ : List (Step D × D)), l₁.length = k → l₂.length = k →
      (∀ p ∈ l₁, p.1.Bounded) → (∀ p ∈ l₂, p.1.Bounded) →
      chainOf E c l₁ = chainOf E c l₂ →
        l₁ = l₂ ∨ ∃ (dom : String) (a b : ByteArray), a ≠ b ∧ E.hash dom a = E.hash dom b :=
  fun _ _ _ _ _ _ _ _ => .inr (lawful_collides hE)

/-- RED: the same escape through a definition. -/
theorem chain_binds_alias [Ord D] {E : Env D} {n : Nat} (hE : E.Lawful n) {c : D} :
    ∀ (k : Nat) (l₁ l₂ : List (Step D × D)), l₁.length = k → l₂.length = k →
      (∀ p ∈ l₁, p.1.Bounded) → (∀ p ∈ l₂, p.1.Bounded) →
      chainOf E c l₁ = chainOf E c l₂ → l₁ = l₂ ∨ Escape E.hash :=
  fun _ _ _ _ _ _ _ _ => .inr (lawful_collides hE)

/-- RED: `CollidesAmong` over a list the statement chooses. -/
theorem chain_binds_chosen_list [Ord D] {E : Env D} {n : Nat} (hE : E.Lawful n) {c : D} :
    ∀ (k : Nat) (l₁ l₂ : List (Step D × D)), l₁.length = k → l₂.length = k →
      (∀ p ∈ l₁, p.1.Bounded) → (∀ p ∈ l₂, p.1.Bounded) →
      chainOf E c l₁ = chainOf E c l₂ → l₁ = l₂ ∨ ∃ S, CollidesAmong E.hash S :=
  fun _ _ _ _ _ _ _ _ =>
    let ⟨dom, a, b, hne, h⟩ := lawful_collides hE
    .inr ⟨[(dom, a), (dom, b)], CollidesAmong.pair (fun e => hne (congrArg Prod.snd e)) h⟩

/-- The reach census's plant (GATES-20v (c)): a `native_decide` theorem with no allow row in gates/axioms-allow.tsv. -/
theorem plant_native : (2 : Nat) + 2 = 4 := by native_decide

/-- CONTROL (ok): the landed `chain_binds`, over the two chains' own inputs. -/
theorem chain_binds_named [Ord D] {E : Env D} {n : Nat} (hE : E.Lawful n) {c : D} :
    ∀ (k : Nat) (l₁ l₂ : List (Step D × D)), l₁.length = k → l₂.length = k →
      (∀ p ∈ l₁, p.1.Bounded) → (∀ p ∈ l₂, p.1.Bounded) →
      chainOf E c l₁ = chainOf E c l₂ → l₁ = l₂ ∨ CollidesAmong E.hash (chainPres E c l₁ ++ chainPres E c l₂) :=
  chain_binds hE

end Nanodregg.Kernel.StatementPlant
'''

# The two-chosen-sides test of Census/Statements.lean, and its disabled form for the mutant.
TEST = "&& mentions chosen l && mentions chosen r then"
DISABLED = "&& mentions chosen l && mentions chosen r && false then"


def write(path: str, text: str) -> None:
    os.makedirs(os.path.dirname(path), exist_ok=True)
    with open(path, "w", encoding="utf-8") as fh:
        fh.write(text)


# Lean runs with cwd = SCRATCH and names SCRATCH's directories RELATIVELY: the judge's {fresh} is
# `.lake/runs/script:gates/statement_plants.py-N`, and a `:` in a LEAN_PATH entry splits it, so an absolute
# scratch entry silently falls off the path (the first full judge read the real Census.Statements in place of
# the mutant, and no plant module at all). The tree's own entries come from `lake env` and are absolute.
LEAN = ""


def lean(scratch: str, args: list[str], lean_path: list[str], log: str) -> tuple[int, str]:
    """Run the tree's lean in SCRATCH with LEAN_PATH = lean_path; output to a file, then read."""
    bad = [p for p in lean_path if ":" in p]
    if bad:
        raise SystemExit(f"STATEMENT PLANTS RED: a LEAN_PATH entry holds ':' and would split: {bad}")
    with open(os.path.join(scratch, log), "w", encoding="utf-8") as fh:
        r = subprocess.run([LEAN, *args], cwd=scratch, env=dict(os.environ, LEAN_PATH=":".join(lean_path)),
                           stdout=fh, stderr=subprocess.STDOUT)
    with open(os.path.join(scratch, log), encoding="utf-8") as fh:
        return r.returncode, fh.read()


def run_census(scratch: str, name: str, imports: list[str], roots: list[str], lean_path: list[str]) -> tuple[int, str, str]:
    write(os.path.join(scratch, f"{name}.lean"), "import Census.Statements\n" + "".join(f"import {m}\n" for m in imports)
          + f'#statement_census "{name}.tsv" {" ".join(roots)}\n')
    code, out = lean(scratch, [f"{name}.lean"], lean_path, f"{name}.out")
    return code, out, os.path.join(scratch, f"{name}.tsv")


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("scratch")
    ap.add_argument("--harness-control", action="store_true")
    a = ap.parse_args()
    scratch = os.path.abspath(a.scratch)
    os.makedirs(scratch, exist_ok=True)
    global LEAN
    base = subprocess.run(["lake", "env", "printenv", "LEAN_PATH"], cwd=ROOT, capture_output=True,
                          text=True, check=True).stdout.strip().split(":")
    prefix = subprocess.run(["lake", "env", "lean", "--print-prefix"], cwd=ROOT, capture_output=True,
                            text=True, check=True).stdout.strip()
    LEAN = os.path.join(prefix, "bin", "lean")
    mods, libs = census.modules(tree.read(ROOT))
    red: list[str] = []

    # plant: compile the vacuous module into SCRATCH, then census the tree plus the plant
    write(os.path.join(scratch, "src", PLANT_ROOT, "Vacuous.lean"), PLANT)
    os.makedirs(os.path.join(scratch, "lib", PLANT_ROOT), exist_ok=True)
    code, out = lean(scratch, ["-R", "src", "-o", f"lib/{PLANT_ROOT}/Vacuous.olean", f"src/{PLANT_ROOT}/Vacuous.lean"],
                     base + ["lib"], "plant-compile.out")
    if code != 0:
        print(out)
        print(f"STATEMENT PLANTS RED: the plant module did not compile (exit {code}); see {scratch}/plant-compile.out")
        return 1
    code, out, tsv = run_census(scratch, "PlantRun", mods + [f"{PLANT_ROOT}.Vacuous"], libs + [PLANT_ROOT],
                                base + ["lib"])
    print(out.strip())
    want = len(VACUOUS) + (1 if a.harness_control else 0)
    if code == 0 or f"STATEMENT-CENSUS RED ({want}):" not in out:
        red.append(f"plant{' (harness-control: a fourth RED expected)' if a.harness_control else ''}: "
                   f"wanted `STATEMENT-CENSUS RED ({want}):` with Lean exit 1, read exit {code}")
    for thm in VACUOUS:
        if f"{NS}{thm}: right disjunct:" not in out:
            red.append(f"plant: {thm} is not named RED")
    rows = open(tsv, encoding="utf-8").read().splitlines() if os.path.exists(tsv) else []
    ctl = [r for r in rows if f"\t{NS}{CONTROL_THM}\t" in r]
    if len(ctl) != 1 or not ctl[0].endswith("\tok"):
        red.append(f"plant: the control {CONTROL_THM} must be one ok row, read {ctl!r}")

    # control: the tree alone reads ok
    code, out, _ = run_census(scratch, "TreeRun", mods, libs, base)
    print(out.strip())
    if code != 0 or "STATEMENT-CENSUS ok:" not in out:
        red.append(f"control: the tree alone must read `STATEMENT-CENSUS ok`, read exit {code}")

    # mutant: the census with the two-chosen-sides test disabled is refused by its own fixtures
    source = open(os.path.join(ROOT, "Census", "Statements.lean"), encoding="utf-8").read()
    if source.count(TEST) != 1:
        red.append(f"mutant: the test `{TEST}` occurs {source.count(TEST)} times in Census/Statements.lean, expected 1")
    else:
        write(os.path.join(scratch, "mutsrc", "Census", "Statements.lean"), source.replace(TEST, DISABLED))
        os.makedirs(os.path.join(scratch, "mut", "Census"), exist_ok=True)
        code, out = lean(scratch, ["-R", "mutsrc", "-o", "mut/Census/Statements.olean", "mutsrc/Census/Statements.lean"],
                         base, "mutant-compile.out")
        if code != 0:
            red.append(f"mutant: did not compile (exit {code}); see {scratch}/mutant-compile.out")
        else:
            code, out, _ = run_census(scratch, "MutantRun", [], [PLANT_ROOT], ["mut"] + base)
            print(out.strip())
            if code == 0 or "STATEMENT-CENSUS harness:" not in out:
                red.append(f"mutant: with the test disabled the fixtures must refuse (`STATEMENT-CENSUS harness:`), read exit {code}")
            else:
                print("PLANT RED: the two-chosen-sides test disabled -> the census's own fixtures refuse it")

    # reach: the fast judge's census commands over a reach (the plant module; then a tree module, the control)
    allow = os.path.join(ROOT, "gates", "axioms-allow.tsv")
    for name, mod, roots, path, planted in (("ReachPlant", f"{PLANT_ROOT}.Vacuous", libs + [PLANT_ROOT], base + ["lib"], True),
                                            ("ReachTree", "Kernel.Proofs.Fold", libs, base, False)):
        write(os.path.join(scratch, f"{name}.txt"), mod + "\n")
        write(os.path.join(scratch, f"{name}.lean"), "import Census.Axioms\nimport Census.Statements\n"
              f"import {mod}\n#axiom_census_in \"{allow}\" \"{name}.txt\" {' '.join(roots)}\n"
              f"#statement_census_in \"{name}.tsv\" \"{name}.txt\" {' '.join(roots)}\n")
        code, out = lean(scratch, [f"{name}.lean"], path, f"{name}.out")
        print(out.strip())
        if planted:
            bad = []
            if "AXIOM-CENSUS red" not in out or f"{NS}plant_native ({PLANT_ROOT}.Vacuous) uses" not in out:
                bad.append("reach: the plant's native_decide theorem is not named by `#axiom_census_in`")
            if f"STATEMENT-CENSUS RED ({len(VACUOUS)}):" not in out:
                bad.append(f"reach: `#statement_census_in` over the plant must read RED ({len(VACUOUS)})")
            red += bad
            if not bad:
                print("PLANT RED: the reach census names the native_decide theorem and the three vacuous ones")
        elif code != 0 or "AXIOM-CENSUS ok" not in out or "STATEMENT-CENSUS ok" not in out:
            red.append(f"reach: over a tree module both must read ok, read exit {code}")

    if red:
        for r in red:
            print("STATEMENT PLANTS RED: " + r)
        return 1
    print("STATEMENT PLANTS GREEN")
    return 0


if __name__ == "__main__":
    sys.exit(main())
