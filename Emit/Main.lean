/- The `emit-rust` executable: only `main` (closure C7); the generator is `Emit.Rust`. -/
import Emit.Rust

def main (args : List String) : IO UInt32 := Nanodregg.Emit.Rust.run args
