import Emit.Rust
import Hosting.Wire
import Hosting.LaunchExit
import Hosting.Plan
import Hosting.Controller

/-!
# Emit.Hosting — the Rust copy of HOSTING's frames

`launcher/src/generated.rs` is this function's output and nothing else (law 2): the controller's
actions and the launcher's reports (`Hosting.Wire.actionCases`, `Hosting.Wire.reportCases`) as
`wire::Action` and `wire::Report`, with `FRAME_MAX` (the frame and field bound), `GRAINS_MAX`,
`TICK_MS` (the launcher's idle tick) and `RESTART_WINDOW_MS` (the controller's crash-loop window,
which the bell test's race waits out), and grain-launch's exit codes as `launch_exit` and its
controller's as `controller_exit` (`Hosting.LaunchExit`, HOSTING-19), and the label bytes `LABEL_BYTES`.
-/

namespace Nanodregg.Emit.Hosting

open Nanodregg.Hosting

def file : Except String String :=
  Rust.taggedFile "Hosting/Wire.lean" [("FRAME_MAX", Bounds.frameMax), ("GRAINS_MAX", Bounds.grainsMax),
    ("TICK_MS", tickMs), ("RESTART_WINDOW_MS", Controller.restartWindowMs)]
    Bounds.frameMax [("Action", Wire.actionCases), ("Report", Wire.reportCases)]
  |>.map (· ++ "\n" ++ Rust.byteModule "launch_exit" LaunchExit.all (fun e => e.code.toUInt8) ++
    "\n\n" ++ Rust.byteModule "controller_exit" ControllerExit.all (fun e => e.code.toUInt8) ++
    "\n\n/// The directories under `worlds/<label>` every plan hides (`Hosting.layoutHidden`,\n" ++
    "/// `Proofs.plan_hidden_layout`): grain-launch refuses to start without them.\n" ++
    Rust.rustStrsConst "LAYOUT_HIDDEN" (layoutHidden.map String.fromUTF8!) ++
    "\n\n/// The bytes a Store label or a grain name may hold (`Hosting.labelByte`, CLIENT-40): a label is\n" ++
    "/// one clean path component (`wire::path_clean`) of these bytes (`Hosting.labelOk`).\n" ++
    Rust.rustByteConst "LABEL_BYTES" ⟨((List.range 256).map Nat.toUInt8 |>.filter labelByte).toArray⟩ ++ "\n")

/-- `emit-hosting PATH` writes the file; `emit-hosting --check PATH` exits 1 if PATH differs. -/
def run (args : List String) : IO UInt32 := Rust.runWith "emit-hosting" file args

end Nanodregg.Emit.Hosting
