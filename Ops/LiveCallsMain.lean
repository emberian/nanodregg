/- The `live-calls` executable: only `main` (closure C7); the generator is `Ops.LiveCalls`. -/
import Ops.LiveCalls

def main (args : List String) : IO UInt32 := Nanodregg.Ops.LiveCalls.run args
