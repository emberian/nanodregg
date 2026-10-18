import Emit.Rust
import Hosting.Pins

/-!
# Emit.Pins — `deploy/tls/pins`, the provider leaf-key pins the repository ships (HOSTING-28)

The file is `Hosting.Pins.text` and nothing else.
-/

namespace Nanodregg.Emit.Pins

/-- `emit-pins PATH` writes the file; `emit-pins --check PATH` exits 1 if PATH differs. -/
def run (args : List String) : IO UInt32 := Rust.runWith "emit-pins" (.ok Hosting.Pins.text) args

end Nanodregg.Emit.Pins
