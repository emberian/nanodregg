import Kernel.Sim
import Kernel.Sim.Deployed

open Nanodregg.Kernel.Sim in
/-- `kernel-sim [--toy] (SEED… | --seeds N)`: the deployed parameters by default. -/
def main (args : List String) : IO UInt32 :=
  match args with
  | "--toy" :: rest => Gen.report toy (Gen.parseSeeds rest)
  | _ => Gen.report Deployed.params (Gen.parseSeeds args)
