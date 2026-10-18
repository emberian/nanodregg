/- The `emit-pins` executable: only `main` (closure C7); the generator is `Emit.Pins`. -/
import Emit.Pins

def main (args : List String) : IO UInt32 := Nanodregg.Emit.Pins.run args
