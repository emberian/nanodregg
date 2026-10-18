import Kernel.Sim
import Kernel.Sim.Deployed

open Nanodregg.Kernel.Sim in
/-- `kernel-sim [SEED… | --seeds N] [--harness-control]`: the deployed parameters, the only run
(GATES-14). A removed mode is refused by name, and any argument `Gen.parseArgs` does not read is
refused (exit 2), never run as something else (GATES-15). -/
def main (args : List String) : IO UInt32 :=
  match args with
  | "--toy" :: _ => do
    IO.eprintln "kernel-sim: --toy was removed (GATES-14: its carry-budget plant is vacuous at the toy digest)"
    pure 2
  | _ => match Gen.parseArgs args with
    | some (seeds, control) => Gen.report Deployed.params seeds control
    | none => do
      IO.eprintln s!"usage: kernel-sim [SEED… | --seeds N] [--harness-control] (got {args})"
      pure 2
