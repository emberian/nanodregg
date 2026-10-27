/- The `emit-traces` executable: only `main` (closure C7); the generator is `Emit.Traces`. -/
import Emit.Traces

def main (args : List String) : IO UInt32 := Nanodregg.Emit.Traces.run args
