/- The `emit-broker` executable: only `main` (closure C7); the generator is `Emit.Broker`. -/
import Emit.Broker

def main (args : List String) : IO UInt32 := Nanodregg.Emit.Broker.run args
