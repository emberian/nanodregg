/- The `codec-vectors` executable: only `main` (closure C7); the generator and check are `Emit.Vectors`. -/
import Emit.Vectors

def main (args : List String) : IO UInt32 := Nanodregg.Emit.Vectors.run args
