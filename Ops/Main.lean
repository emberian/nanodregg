/- The `emit-units` executable: only `main` (closure C7); the renderer is `Ops.Units`. -/
import Ops.Units

def main (args : List String) : IO UInt32 := Nanodregg.Ops.Units.run args
