/-
# Bench.WorstCutWrites — `bench-worstcut-writes SCRATCH [--harness-control]` (PERF-5, PERF-12)

The worst cut's `writes` tail: one-slot `write`s to the founder's object, over a base holding only
it. Bench.WorstCut builds, counts and prints.
-/
import Bench.WorstCut

namespace Nanodregg.Bench.WorstCut.Writes

open Nanodregg.Kernel Nanodregg.Kernel.Receive Nanodregg.Host Nanodregg.Host.Deployed
open Nanodregg.Bench.WorstCut

def shape : Shape Unit where
  name := "writes"
  first _ _ w _ := pure (.ok (#[], w, ()))
  step _ m obj w i := .ok (call w m [m.id, obj] (.write obj [(stateBase, some (Kernel.Sim.Gen.nat (i + 1)))] none), ())

end Nanodregg.Bench.WorstCut.Writes
