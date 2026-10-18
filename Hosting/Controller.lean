/-
# Hosting.Controller — what to launch and what to kill: the World says, the box converges

The controller (HOSTING-7) is per Store. It reads the World (the follower open), and for every cell
id a batch touched (or, at its start, every id) it compares what the World DESIRES (the grain's
`phase`) with what the launcher OBSERVES (`Live`: a child running, its recent exits). Observed state
lives only here and in the OS process table, never in the World.

The grain a decision names is rendered HERE from the World id (`dirOf`), never paired by a caller:
an action for id `i` is decided on `w.live i` and names `dirOf i` (`Proofs.Controller.reconcile_names`).

A cell is a grain only if it is an OBJECT whose package slot holds exactly the lifecycle package's
id (`lifecycleId`: KERNEL's `romIdOf` of the ROM cell `install` creates for the package's bytes):
any member may create an object with a look-alike state, and it must never be launched.

Fail closed: a running child whose cell is gone, is not a lifecycle object, does not decode, or
does not desire `running` is killed. Restart backoff is ADVISORY: `now` and the exit times are the
launcher's report, so the crash-loop refusal is only as honest as the operator's own process.
-/
import Hosting.Plan
import Lang.Print
import Kernel.World

namespace Nanodregg.Hosting.Controller

open Nanodregg.Kernel
open Nanodregg.Hosting

/-- How many exits within the window refuse a restart. -/
def restartsMax : Nat := 5
def restartWindowMs : Nat := 60000

/-- What the launcher reports of one grain's child (never World state). -/
structure Live where
  grain : ByteArray
  running : Bool
  /-- exit times, in the launcher's milliseconds -/
  exits : List Nat

/-- The ROM cell `install` creates for package bytes `b` (`Receive.install`). -/
def packageCell (b : ByteArray) : Cell :=
  { kind := Receive.kindPackage, discipline := .rom, slots := [(0, b)] }

/-- The lifecycle package's id under `E`: what a grain's package slot must hold. -/
def lifecycleId {D : Type} (E : Env D) : Option D :=
  (Grain.lifecycle?.toOption.bind Lang.Wire.encodePackage).map fun b => romIdOf E (packageCell b)

def isGrain (pkgId : ByteArray) (c : Cell) : Bool :=
  c.kind == Receive.kindObject && c.slots.get Receive.slotPackage == some pkgId

/-- The directory name of a grain: its id's bytes in lowercase hex (`Lang.Print.hex`); injective,
`Proofs.Controller.dirOf_injective`. -/
def dirOf (idBytes : ByteArray) : ByteArray := (Lang.Print.hex idBytes).toUTF8

/-- The grain a lifecycle cell describes, and its desired phase; `none` when a slot does not
decode. -/
def grainOf (dir : ByteArray) (c : Cell) : Option (Grain × Phase) := do
  let s := c.slots
  let k ← Grain.kindOf s
  let e ← Grain.entryOf s
  let p ← Grain.phaseOf s
  pure ({ idHex := dir, kind := k, entry := e }, p)

/-- A resident grain that is born and not removed: a lifecycle object (`isGrain`) whose state
decodes (`grainOf`, the controller's own reader), of kind `resident`, in any phase but `removed`.
keybroker serves exactly these grains' broker sockets (HOSTING-26): the set covers every grain the
controller may launch as a resident (`Proofs.launch_served`), from its birth, so its socket exists
before its start can be decided. -/
def residentOf (pkgId : ByteArray) (c : Cell) : Option Unit :=
  match grainOf .empty c with
  | some (gr, ph) => if isGrain pkgId c && gr.kind == .resident && ph != .removed then some () else none
  | none => none

def runningIn (live : List Live) (g : ByteArray) : Bool := live.any fun l => l.grain == g && l.running

/-- Every exit the launcher reported for `g`, across all its reports. -/
def exitsOf (live : List Live) (g : ByteArray) : List Nat :=
  (live.filter (·.grain == g)).flatMap (·.exits)

def recentExits (now : Nat) (live : List Live) (g : ByteArray) : Nat :=
  ((exitsOf live g).filter fun t => now < t + restartWindowMs).length

def crashLooping (now : Nat) (live : List Live) (g : ByteArray) : Bool :=
  restartsMax ≤ recentExits now live g

/-- One cell (`none`: no live cell at that id), its grain named `g`. -/
def decideCell (label pkgId : ByteArray) (now : Nat) (live : List Live) (g : ByteArray)
    (cell : Option Cell) : Option Verdict :=
  let up := runningIn live g
  let stop : Option Verdict := if up then some .kill else none
  match cell with
  | none => stop
  | some c =>
    if !isGrain pkgId c then stop else
    match grainOf g c with
    | none => if up then some .kill else some (.refuse .malformedGrain)
    | some (gr, ph) =>
      if ph = .running then
        if up then none
        else if crashLooping now live g then some (.refuse .crashLoop)
        else match plan label gr with
          | .ok p => some (.launch p)
          | .error r => some (.refuse r)
      else stop

variable {D : Type} [Ord D] [DecidableEq D]

/-- The ids a batch of Turns may have changed: every touched cell and every born one (HOST's tail
returns each record's Turns, `Host.Deployed.tailStep`). -/
def touchedIds (ts : List (Turn D)) : List D :=
  ts.flatMap fun t => t.touches.map (·.cell) ++ createdIds t

/-- Every touched id (duplicates once), at most `Bounds.grainsMax` per call: the caller pages the rest. -/
def reconcile (E : Env D) (bytesOf : D → ByteArray) (label pkgId : ByteArray) (now : Nat)
    (live : List Live) (w : World D) (ids : List D) : List Action :=
  (ids.eraseDups.take Bounds.grainsMax).filterMap fun i =>
    let g := dirOf (bytesOf i)
    (decideCell label pkgId now live g (w.live E i)).map fun v => { grain := g, verdict := v }

end Nanodregg.Hosting.Controller
