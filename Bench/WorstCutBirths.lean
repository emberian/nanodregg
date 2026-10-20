/-
# Bench.WorstCutBirths — `bench-worstcut-births SCRATCH [--harness-control]` (PERF-6, PERF-12)

The worst cut's `births` tail: one-slot data-object `create`s (the World grows by a cell per step),
over a base holding only the founder's object. Bench.WorstCut builds, counts and prints.
-/
import Bench.WorstCut

namespace Nanodregg.Bench.WorstCut.Births

open Nanodregg.Kernel Nanodregg.Kernel.Receive Nanodregg.Host Nanodregg.Host.Deployed
open Nanodregg.Bench.WorstCut

def shape : Shape Unit where
  name := "births"
  first _ _ w _ := pure (.ok (#[], w, ()))
  step _ m _ w i := .ok (call w m [m.id] (.create none [] [(stateBase, Kernel.Sim.Gen.nat (i + 1))]), ())

end Nanodregg.Bench.WorstCut.Births
