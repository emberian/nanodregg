/-
# Bench.WorstCutWritesMain — `bench-worstcut-writes SCRATCH [--harness-control]` (PERF-12)

The exe root: Bench.WorstCutWrites gives the shape, Bench.WorstCut builds, counts and prints.
-/
import Bench.WorstCutWrites

def main (args : List String) : IO UInt32 := Nanodregg.Bench.WorstCut.run Nanodregg.Bench.WorstCut.Writes.shape args
