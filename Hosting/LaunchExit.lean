/-
# Hosting.LaunchExit — how grain-launch and its controller end, as data (OPS-3's ask, HOSTING-19)

The grain-launch unit sees one code space, as keybroker's does (HOSTING-16): grain-launch's own ends
(`LaunchExit`, 116 to 127, then 67 and 68: the space below 128 is nearly spent) and its controller's
(`ControllerExit`, 0 and 106 and up), which grain-launch passes through when `hosting-controller` exits,
but only a code `ControllerExit` names (`controller_exit::ALL`); any other is `controllerMechanism`. Each code has the Host's `ExitClass`, so `Ops.Units`
renders the unit's `RestartPreventExitStatus` from `codesOf .fatal` of both tables. grain-launch reads
its codes only from the emitted `generated::launch_exit`.

Every code is below 128: under bwrap a status of 128 or more IS a signal death (`sandbox`'s platform
fact), so grain-launch reads a controller status ≥ 128 as `controllerSignaled`, never as a code. The
codes avoid 1 and 2, 101 (a Rust panic), and every Host, nd-supervise, decider and keybroker code
(`Hosting.Proofs.LaunchExit`).
-/
import Host.Exit

namespace Nanodregg.Hosting

open Nanodregg.Host (ExitClass)

/-- Every way `hosting-controller` ends, by kind (`Cli.Exit.kind`). -/
inductive ControllerExit where
  /-- the launcher closed the report pipe: the normal end -/
  | launcherGone
  /-- argv is not `STORE LABEL` -/
  | usage
  /-- the label is refused by `plan` for every grain -/
  | badLabel
  /-- the lifecycle package has no id: a defect of the build -/
  | noPackage
  /-- the Store refused to open or to be followed: the operator's to look at -/
  | store
  /-- the report pipe ended inside a frame: a defect in the launcher -/
  | torn
  /-- a report frame's length is 0 or past `frameMax`: a defect in the launcher -/
  | badLength
  /-- a report frame does not decode: a defect in the launcher -/
  | badReport
  /-- an action has no frame: a defect (the controller's plans encode) -/
  | unencodable
  /-- `Cli.lifetime` rounds or reports: a fresh life continues -/
  | lifetime
  /-- the pipes or the disk raised an IO error -/
  | io
  deriving DecidableEq, Repr

namespace ControllerExit

def all : List ControllerExit :=
  [launcherGone, usage, badLabel, noPackage, store, torn, badLength, badReport, unencodable, lifetime, io]

def code : ControllerExit → Nat
  | launcherGone => 0 | usage => 106 | badLabel => 107 | noPackage => 108 | store => 109 | torn => 110
  | badLength => 111 | badReport => 112 | unencodable => 113 | lifetime => 114 | io => 115

/-- The controller restarts on its own lifetime only. A fresh start re-reads the World whole and its
memory is empty (HOSTING-10: grain-launch killed every child when the pipe closed), so that is safe; a
Store refusal, an IO error and every defect stop the unit. -/
def cls : ControllerExit → ExitClass
  | launcherGone => .done
  | lifetime => .restart
  | usage | badLabel | noPackage | store | torn | badLength | badReport | unencodable | io => .fatal

def codesOf (k : ExitClass) : List Nat := (all.filter (·.cls == k)).map code

end ControllerExit

/-- Every way `grain-launch` ends on its own account (its controller's exit is passed through). -/
inductive LaunchExit where
  /-- argv does not parse, or a root does not exist -/
  | usage
  /-- the broker root and the hosting root nest (HOSTING-17 §8) -/
  | rootsOverlap
  /-- the sandbox refused the controller's policy, or it could not be spawned -/
  | controllerRefused
  /-- an action frame did not decode: a defect in the controller -/
  | frame
  /-- an action broke the frame contract (a path past a bound): a defect in the controller -/
  | badAction
  /-- a grain name outside `[a-z0-9-]{1,64}`: a defect in the controller -/
  | badGrain
  /-- a second launch for a grain whose child is up: a defect in the controller -/
  | duplicateLaunch
  /-- the report pipe to the controller failed: it is gone, a fresh pair starts over -/
  | reportPipe
  /-- a child's PID file could not be written: the operator's to look at -/
  | pidFile
  /-- `LIFETIME_TICKS` ticks in one process: a fresh life continues -/
  | lifetime
  /-- the controller was killed by a signal (the OOM killer, an operator), or its status was ≥ 128:
  transient by assumption -/
  | controllerSignaled
  /-- `wait` on the controller failed: nothing says a restart is safe -/
  | controllerLost
  /-- the controller's process ended below 128 with a code `ControllerExit` does not name: the
  controller never ran its own end (bwrap's setup, a missing program or library), so a restart
  meets the same mechanism (HOSTING-23) -/
  | controllerMechanism
  /-- a directory the World's layout hides (`Plan.layoutHidden` under `worlds/<label>`) is absent:
  the sandbox would refuse every launch `pathMissing` (HOSTING-24) -/
  | layoutMissing
  deriving DecidableEq, Repr

namespace LaunchExit

def all : List LaunchExit :=
  [usage, rootsOverlap, controllerRefused, frame, badAction, badGrain, duplicateLaunch, reportPipe,
   pidFile, lifetime, controllerSignaled, controllerLost, controllerMechanism, layoutMissing]

def code : LaunchExit → Nat
  | usage => 116 | rootsOverlap => 117 | controllerRefused => 118 | frame => 119 | badAction => 120
  | badGrain => 121 | duplicateLaunch => 122 | reportPipe => 123 | pidFile => 124 | lifetime => 125
  | controllerSignaled => 126 | controllerLost => 127 | controllerMechanism => 67 | layoutMissing => 68

def cls : LaunchExit → ExitClass
  | reportPipe | lifetime | controllerSignaled => .restart
  | usage | rootsOverlap | controllerRefused | frame | badAction | badGrain | duplicateLaunch | pidFile
  | controllerLost | controllerMechanism | layoutMissing => .fatal

/-- The name printed on stderr (`grain-launch: NAME …`). -/
def name (e : LaunchExit) : String := ((toString (repr e)).splitOn ".").getLast!

def codesOf (k : ExitClass) : List Nat := (all.filter (·.cls == k)).map code

end LaunchExit

end Nanodregg.Hosting
