import Kernel.Sim
import Kernel.Sim.Deployed

open Nanodregg.Kernel.Sim in
/-- `kernel-sim (SEED… | --seeds N)`: the deployed parameters, the only run (GATES-14). A removed
mode is refused by name, never run as something else. -/
def main (args : List String) : IO UInt32 :=
  match args with
  | "--toy" :: _ => do
    IO.eprintln "kernel-sim: --toy was removed (GATES-14: its carry-budget plant is vacuous at the toy digest)"
    pure 2
  | _ => Gen.report Deployed.params (Gen.parseSeeds args)
