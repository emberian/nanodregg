import Kernel.Sim

def main (args : List String) : IO UInt32 :=
  Nanodregg.Kernel.Sim.Gen.report Nanodregg.Kernel.Sim.toy (Nanodregg.Kernel.Sim.Gen.parseSeeds args)
