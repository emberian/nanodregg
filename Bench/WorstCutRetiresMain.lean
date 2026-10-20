/-
# Bench.WorstCutRetiresMain — `bench-worstcut-retires SCRATCH [--harness-control]` (PERF-12)

The exe root: Bench.WorstCutRetires gives the shape, Bench.WorstCut builds, counts and prints.
-/
import Bench.WorstCutRetires

def main (args : List String) : IO UInt32 := Nanodregg.Bench.WorstCut.run Nanodregg.Bench.WorstCut.Retires.shape args
