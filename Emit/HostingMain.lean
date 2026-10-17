/- The `emit-hosting` executable: only `main` (closure C7); the generator is `Emit.Hosting`. -/
import Emit.Hosting

def main (args : List String) : IO UInt32 := Nanodregg.Emit.Hosting.run args
