import Emit.Rust
import Hosting.Wire
import Hosting.LaunchExit
import Hosting.Plan

/-!
# Emit.Hosting — the Rust copy of HOSTING's frames

`launcher/src/generated.rs` is this function's output and nothing else (law 2): the controller's
actions and the launcher's reports (`Hosting.Wire.actionCases`, `Hosting.Wire.reportCases`) as
`wire::Action` and `wire::Report`, with `FRAME_MAX` (the frame and field bound) and `GRAINS_MAX`, and
grain-launch's exit codes as `launch_exit` and its controller's as `controller_exit`
(`Hosting.LaunchExit`, HOSTING-19).
-/

namespace Nanodregg.Emit.Hosting

open Nanodregg.Hosting

def file : Except String String :=
  Rust.taggedFile "Hosting/Wire.lean" [("FRAME_MAX", Bounds.frameMax), ("GRAINS_MAX", Bounds.grainsMax)]
    Bounds.frameMax [("Action", Wire.actionCases), ("Report", Wire.reportCases)]
  |>.map (· ++ "\n" ++ Rust.byteModule "launch_exit" LaunchExit.all (fun e => e.code.toUInt8) ++
    "\n\n" ++ Rust.byteModule "controller_exit" ControllerExit.all (fun e => e.code.toUInt8) ++
    "\n\n/// The directories under `worlds/<label>` every plan hides (`Hosting.layoutHidden`,\n" ++
    "/// `Proofs.plan_hidden_layout`): grain-launch refuses to start without them.\n" ++
    Rust.rustStrsConst "LAYOUT_HIDDEN" (layoutHidden.map String.fromUTF8!) ++ "\n")

/-- `emit-hosting PATH` writes the file; `emit-hosting --check PATH` exits 1 if PATH differs. -/
def run (args : List String) : IO UInt32 := Rust.runWith "emit-hosting" file args

end Nanodregg.Emit.Hosting
