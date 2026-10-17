/-
# Hosting.Cli — `hosting-controller STORE LABEL`: follow one Store, tell `grain-launch` what to run

    hosting-controller STORE LABEL

The operator's `grain-launch` starts this process with two pipes: actions go out on stdout,
reports come in on stdin, each frame `u32le len ‖ payload` with `1 ≤ len ≤ Bounds.frameMax`
(`Hosting.Wire`; the Rust end is `launcher/src/generated.rs`'s `read_frame`/`write_frame`). STORE is
read, never written: HOST's tail (`Host.Tail`), the open and then O(appended bytes) per round.

Round 0 decides every live cell id (`Loop.allIds`, once, at start). Each later round reads what was
appended (`Tail.next`), drains the reports the reader task queued, and runs `Loop.step` on the
touched ids and those reports; nothing new and no report sleeps `Host.tailPollMs`. A round's
actions are written and flushed before the next round. Every way it ends is an `Exit` by name on
stderr; there is no unbounded loop (rounds and frames are bounded by `lifetime`, 2^48).
-/
import Hosting.Loop
import Host.Deployed
import Host.Tail
import Host.Wire
import Hosting.LaunchExit

namespace Nanodregg.Hosting.Cli

open Nanodregg.Kernel Nanodregg.Codec Nanodregg.Hosting.Controller
open Nanodregg.Host (Tail File tailPollMs readKey Keys StoreFault)

/-- Rounds, and report frames, in one process: centuries at any rate. -/
def lifetime : Nat := 1 <<< 48

/-- Reports the reader may queue ahead of the loop. -/
def queueMax : Nat := 1024

/-- How the controller ended. -/
inductive Exit
  /-- the arguments are not `STORE LABEL` -/
  | usage
  /-- the label is refused by `plan` for every grain (`labelOk`) -/
  | badLabel
  /-- the lifecycle package has no id (`Controller.lifecycleId`): no grain could qualify -/
  | noPackage
  /-- the Store refused to open or to be followed (its own name, `StoreFault.name`) -/
  | store (name : String)
  /-- the launcher closed the report pipe at a frame boundary: it is gone, so are its children -/
  | launcherGone
  /-- the report pipe ended inside a frame -/
  | torn
  /-- a report frame's length is 0 or past `frameMax` -/
  | badLength
  /-- a report frame does not decode (the codec's refusal, by name) -/
  | badReport (name : String)
  /-- an action has no frame (past a bound or an unclean path: `encodeAction` = none) -/
  | unencodable
  /-- `lifetime` rounds or report frames in one process -/
  | lifetime
  /-- the pipes or the disk raised an IO error -/
  | io (msg : String)

def Exit.name : Exit → String
  | .usage => "usage" | .badLabel => "badLabel" | .noPackage => "noPackage"
  | .store n => s!"store {n}" | .launcherGone => "launcherGone" | .torn => "torn"
  | .badLength => "badLength" | .badReport n => s!"badReport {n}" | .unencodable => "unencodable"
  | .lifetime => "lifetime" | .io m => s!"io {m}"

/-- The end's row in Lean's exit table (`Hosting.ControllerExit`, HOSTING-19). -/
def Exit.kind : Exit → ControllerExit
  | .usage => .usage | .badLabel => .badLabel | .noPackage => .noPackage | .store _ => .store
  | .launcherGone => .launcherGone | .torn => .torn | .badLength => .badLength
  | .badReport _ => .badReport | .unencodable => .unencodable | .lifetime => .lifetime | .io _ => .io

/-- The exit status: the table's code for the end's kind (0 only when the launcher left first). -/
def Exit.code (e : Exit) : UInt32 := e.kind.code.toUInt32

def finish (e : Exit) : IO UInt32 := do
  IO.eprintln s!"hosting-controller: {e.name}"
  return e.code

/-- Read report frames from `input` into `ch` until the pipe ends or a frame is refused. -/
def readReports (input : IO.FS.Stream) (ch : Std.CloseableChannel.Sync Report) : Nat → IO Exit
  | 0 => do discard <| (ch.close).toBaseIO; pure .lifetime
  | fuel + 1 => do
    let head ← input.read 4
    let stop (e : Exit) : IO Exit := do discard <| (ch.close).toBaseIO; pure e
    if head.isEmpty then return ← stop .launcherGone
    let head ← if head.size = 4 then pure (some head) else do
      match ← Host.readExact input (4 - head.size) with
      | some rest => pure (some (head ++ rest))
      | none => pure none
    let some head := head | return ← stop .torn
    let some len := Host.Log.lenAt head 0 | return ← stop .torn
    if len = 0 ∨ Bounds.frameMax < len then return ← stop .badLength
    let some body ← Host.readExact input len | return ← stop .torn
    match Wire.decodeReport body with
    | .error r => stop (.badReport (reprStr r))
    | .ok rep =>
      match ← (ch.send rep).toBaseIO with
      | .ok () => readReports input ch fuel
      | .error _ => pure .launcherGone

/-- Every report queued now, at most `queueMax`. -/
def drain (ch : Std.CloseableChannel.Sync Report) : Nat → List Report → IO (List Report)
  | 0, acc => pure acc.reverse
  | n + 1, acc => do
    match ← ch.tryRecv with
    | some r => drain ch n (r :: acc)
    | none => pure acc.reverse

/-- Write one round's actions, each in its frame, and flush. -/
def send (out : IO.FS.Stream) (acts : List Action) : IO (Option Exit) := do
  for a in acts do
    match Wire.encodeAction a with
    | some b => out.write (Host.Log.lenBytes b.size ++ b)
    | none => return some .unencodable
  out.flush
  return none

abbrev D := Host.Deployed.D

/-- The rounds after the first, at most `fuel`. -/
def rounds (keys : Keys) (seg : File) (label pkgId : ByteArray) (out : IO.FS.Stream)
    (ch : Std.CloseableChannel.Sync Report) (reader : Task (Except IO.Error Exit)) :
    Nat → Tail (World D) → Loop.State D → IO Exit
  | 0, _, _ => pure .lifetime
  | fuel + 1, t, st => do
    match ← Tail.next keys Host.Deployed.c Host.Deployed.tailStep seg t with
    | .error f => pure (.store f.name)
    | .ok (t', outs) =>
      let reps ← drain ch queueMax []
      if outs.isEmpty && reps.isEmpty then
        if ← IO.hasFinished reader then
          match reader.get with
          | .ok e => return e
          | .error err => return .io (toString err)
        IO.sleep tailPollMs.toUInt32
        rounds keys seg label pkgId out ch reader fuel t' st
      else
        let touched := touchedIds (outs.toList.flatten.map Prod.fst)
        let (st', acts) := Loop.step Host.Deployed.X.env Digest.bytes label pkgId t'.world st touched reps
        match ← send out acts with
        | some e => pure e
        | none => rounds keys seg label pkgId out ch reader fuel t' st'

def run (store : System.FilePath) (label : ByteArray) : IO Exit := do
  unless labelOk label do return .badLabel
  let some pid := lifecycleId Host.Deployed.X.env | return .noPackage
  let pkgId := pid.bytes
  match ← (readKey store : IO (Except (StoreFault (Host.Record.Fault (Reject D))) Digest)) with
  | .error f => return .store f.text
  | .ok key =>
    let keys := Keys.ofKey key Host.Deployed.shapes
    match ← Tail.open store keys Host.Deployed.c Host.Deployed.world Host.Deployed.recorder.mark
        Host.Deployed.originChain Host.Deployed.tailStep with
    | .error f => return .store f.text
    | .ok (t, seg) =>
      let ch ← Std.CloseableChannel.Sync.new (some queueMax)
      let input ← IO.getStdin
      let reader ← IO.asTask (readReports input ch lifetime) .dedicated
      let out ← IO.getStdout
      let (st, acts) := Loop.step Host.Deployed.X.env Digest.bytes label pkgId t.world Loop.State.empty
        (Loop.allIds t.world) []
      match ← send out acts with
      | some e => return e
      | none => rounds keys seg label pkgId out ch reader lifetime t st

def main (args : List String) : IO UInt32 := do
  match args with
  | [store, label] =>
    let e ← try run store label.toUTF8 catch err => pure (.io (toString err))
    finish e
  | _ =>
    IO.eprintln "usage: hosting-controller STORE LABEL"
    finish .usage

end Nanodregg.Hosting.Cli
