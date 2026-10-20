/-
# Bench.WorstCutBirthsMain — `bench-worstcut-births SCRATCH [--harness-control]` (PERF-12)

The exe root: Bench.WorstCutBirths gives the shape, Bench.WorstCut builds, counts and prints.
-/
import Bench.WorstCutBirths

def main (args : List String) : IO UInt32 := Nanodregg.Bench.WorstCut.run Nanodregg.Bench.WorstCut.Births.shape args
