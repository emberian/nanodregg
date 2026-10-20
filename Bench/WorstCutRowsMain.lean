/-
# Bench.WorstCutRowsMain — `bench-worstcut-rows SCRATCH [--harness-control]` (PERF-12)

The exe root: Bench.WorstCutRows gives the shape, Bench.WorstCut builds, counts and prints.
-/
import Bench.WorstCutRows

def main (args : List String) : IO UInt32 := Nanodregg.Bench.WorstCut.run Nanodregg.Bench.WorstCut.Rows.shape args
