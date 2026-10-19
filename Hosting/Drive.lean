/-
# Hosting.Drive — `hosting-drive`: one Lean-planned launch, for the launcher's isolation test

    hosting-drive [--plant-read-worlds] [--resident] [--plant-foreign broker|member HEX]
                  [--exit-after-launch] LABEL IDHEX ENTRY

A stand-in for `hosting-controller` that needs no Store: it plans ONE grain (an app, or with
`--resident` a resident, whose plan connects to its own broker socket, HOSTING-17) with the deployed
`plan` (label, directory name, entry), writes that launch with the deployed `Wire.encodeAction`, then
reads the launcher's reports and prints each on stderr (`report started`, `report exited STATUS`,
`report failed NAME`; a `tick` is read and not printed), ending at the grain's first `exited` or
`failed`. The plan is Lean's, never built in Rust (the launcher's test runs this exe).

`--exit-after-launch` ends the drive right after it writes the launch, with the code a controller's
Store refusal has (`ControllerExit.store`, 109): the launcher's next report then meets a gone reader,
and its exit must still be the controller's code (HOSTING-19).

`--plant-foreign ROOT HEX` is the launcher test's plant for HOSTING-25: the plan's socket entry under
ROOT (`broker` or `member`) is replaced by the same socket of the grain directory HEX, which no Lean
plan does (`Proofs.Plan.plan_sockets_named`), so grain-launch must end `foreignPath` before it
launches anything.

`--plant-read-worlds` is the test's plant: `worlds/` is added to the plan's `read`, which covers the
hidden Store, so the sandbox must refuse the launch (`exposed`) — or, were the hidden check gone, the
probe would read the neighbour; either way the confined verdict changes, which is the point.
-/
import Hosting.Plan
import Hosting.LaunchExit
import Host.Wire

namespace Nanodregg.Hosting.Drive

/-- How the drive ended. -/
inductive Exit
  | usage
  | refused (why : Refusal)
  | done
  | launcherGone
  | badReport (name : String)
  | unencodable
  | rounds
  /-- `--exit-after-launch`: gone right after the launch, as a controller's Store refusal -/
  | abandoned

def Exit.name : Exit → String
  | .usage => "usage" | .refused r => s!"refused {r.name}" | .done => "done"
  | .launcherGone => "launcherGone" | .badReport n => s!"badReport {n}"
  | .unencodable => "unencodable" | .rounds => "rounds" | .abandoned => "abandoned"

def Exit.code : Exit → UInt32
  | .done => 0
  | .usage => 2
  | .abandoned => ControllerExit.store.code.toUInt32
  | _ => 1

/-- Reports read at most: the probe starts once and exits once, and the launcher ticks every
`tickMs` meanwhile (HOSTING-38), so this bounds the drive at about twelve days of ticks. -/
def reportsMax : Nat := 1 <<< 20

def readReports (input : IO.FS.Stream) (grain : ByteArray) : Nat → IO Exit
  | 0 => pure .rounds
  | fuel + 1 => do
    let some head ← Host.readExact input 4 | return .launcherGone
    let some len := Host.Log.lenAt head 0 | return .launcherGone
    if len = 0 ∨ Bounds.frameMax < len then return .badReport "badLength"
    let some body ← Host.readExact input len | return .launcherGone
    match Wire.decodeReport body with
    | .error r => return .badReport (reprStr r)
    | .ok (.tick _) => readReports input grain fuel
    | .ok (.started g _) =>
      IO.eprintln "report started"
      if g == grain then readReports input grain fuel else return .badReport "otherGrain"
    | .ok (.exited g s _) =>
      IO.eprintln s!"report exited {s}"
      return if g == grain then .done else .badReport "otherGrain"
    | .ok (.failed g why _) =>
      IO.eprintln s!"report failed {why.name}"
      return if g == grain then .done else .badReport "otherGrain"

/-- Which socket root `--plant-foreign` rewrites. -/
inductive Foreign
  | broker (hex : ByteArray)
  | member (hex : ByteArray)

def run (plantReadWorlds abandon : Bool) (foreign : Option Foreign) (kind : Grain.Kind)
    (label idHex entry : ByteArray) : IO Exit := do
  match plan label { idHex, kind, entry } with
  | .error r => return .refused r
  | .ok p =>
    let p := if plantReadWorlds then { p with read := [lit "worlds"] :: p.read } else p
    let p := match foreign with
      | some (.broker h) => { p with broker := [[h, brokerSock]] }
      | some (.member h) => { p with member := [[h, memberSock]] }
      | none => p
    let some b := Wire.encodeAction { grain := idHex, verdict := .launch p } | return .unencodable
    let out ← IO.getStdout
    out.write (Host.Log.lenBytes b.size ++ b)
    out.flush
    if abandon then return .abandoned
    readReports (← IO.getStdin) idHex reportsMax

def main (args : List String) : IO UInt32 := do
  let (plant, rest) := match args with
    | "--plant-read-worlds" :: rest => (true, rest)
    | rest => (false, rest)
  let (kind, rest) := match rest with
    | "--resident" :: rest => (Grain.Kind.resident, rest)
    | rest => (Grain.Kind.app, rest)
  let (foreign, rest) := match rest with
    | "--plant-foreign" :: "broker" :: h :: rest => (some (Foreign.broker h.toUTF8), rest)
    | "--plant-foreign" :: "member" :: h :: rest => (some (Foreign.member h.toUTF8), rest)
    | rest => (none, rest)
  let (abandon, rest) := match rest with
    | "--exit-after-launch" :: rest => (true, rest)
    | rest => (false, rest)
  let e ← match rest with
    | [label, idHex, entry] => run plant abandon foreign kind label.toUTF8 idHex.toUTF8 entry.toUTF8
    | _ => pure .usage
  IO.eprintln s!"hosting-drive: {e.name}"
  return e.code

end Nanodregg.Hosting.Drive
