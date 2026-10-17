import Emit.Rust
import Hosting.Wire

/-!
# Emit.Hosting — the Rust copy of HOSTING's frames

`launcher/src/generated.rs` is this function's output and nothing else (law 2): the controller's
actions and the launcher's reports (`Hosting.Wire.actionCases`, `Hosting.Wire.reportCases`) as
`wire::Action` and `wire::Report`, with `FRAME_MAX` (the frame and field bound) and `GRAINS_MAX`.
-/

namespace Nanodregg.Emit.Hosting

open Nanodregg.Hosting

def file : Except String String :=
  Rust.taggedFile "Hosting/Wire.lean" [("FRAME_MAX", Bounds.frameMax), ("GRAINS_MAX", Bounds.grainsMax)]
    Bounds.frameMax [("Action", Wire.actionCases), ("Report", Wire.reportCases)]

/-- `emit-hosting PATH` writes the file; `emit-hosting --check PATH` exits 1 if PATH differs. -/
def run (args : List String) : IO UInt32 := Rust.runWith "emit-hosting" file args

end Nanodregg.Emit.Hosting
