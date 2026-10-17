/-
# Hosting.Plan — what a grain may touch: a total function of (store label, grain)

The controller (HOSTING-4) hands the launcher one `Plan` per grain to start; the launcher turns it
into `sandbox::Policy` field for field and spawns through `sandbox::command`, deciding nothing.
Every path is RELATIVE to the operator's hosting root (the launcher joins it; Lean never sees the
OS), a list of clean components.

Layout under the root, for the Store labelled `l`:

    worlds/l/store            the Store's files            hidden from every grain
    worlds/l/members          member workspaces (seeds)    hidden from every grain
    worlds/l/grains/<id>/pkg  the grain's package files    read (its program is pkg/<entry>)
    worlds/l/grains/<id>/vol  the grain's volume           read + write

There is no volume REQUEST (ASSEMBLY HOSTING-5): the volume is a function of (store, grain), so no
input names another world's or grain's path. That a grain cannot reach `worlds/<other>` is the
sandbox's deny-default, tested physically by the launcher's plant (HOSTING-5), not proved here.
-/
import Hosting.Package

namespace Nanodregg.Hosting

/-- A path below the hosting root, as components. -/
abbrev Path := List ByteArray

/-- The `sandbox::Policy` a grain is launched under, plus its program. `connect` is the Unix
sockets the child may connect to (empty for an app; HOSTING-6 for a resident). -/
structure Plan where
  program : Path
  read : List Path
  write : List Path
  exec : List Path
  connect : List Path
  hidden : List Path
  deriving DecidableEq

/-- Why no plan exists, by name (law 7). -/
inductive Refusal
  /-- the Store label is not one clean path component -/
  | labelUnclean
  /-- the grain's entry is not one clean path component -/
  | entryUnclean
  /-- the grain's id directory name is not one clean path component -/
  | idUnclean
  /-- a lifecycle cell whose kind, entry or phase does not decode -/
  | malformedGrain
  /-- the grain exited `Controller.restartsMax` times within the restart window -/
  | crashLoop
  /-- a resident's plan needs `Policy.connect` (CLIENT) and the broker (HOSTING-6, HOSTING-7) -/
  | residentUnsupported
  deriving DecidableEq, Repr

def Refusal.name : Refusal → String
  | .labelUnclean => "labelUnclean"
  | .entryUnclean => "entryUnclean"
  | .idUnclean => "idUnclean"
  | .malformedGrain => "malformedGrain"
  | .crashLoop => "crashLoop"
  | .residentUnsupported => "residentUnsupported"

/-- The most grains one reconcile call decides (the caller pages a larger batch). -/
def grainsMax : Nat := 256

/-- The longest component, in bytes. -/
def componentMax : Nat := 64

/-- One clean component: nonempty, at most `componentMax` bytes, not `.` or `..`, no `/` and no NUL. -/
def clean (c : ByteArray) : Bool :=
  let bs := c.data.toList
  !bs.isEmpty && bs.length ≤ componentMax && bs != [46] && bs != [46, 46] &&
    bs.all (fun b => b != 47 && b != 0)

def lit (s : String) : ByteArray := s.toUTF8

/-- A grain the controller read off the World: its cell id as the digest's hex (the controller
renders it; `plan` still refuses an unclean one, `idUnclean`, so no theorem rests on the renderer),
its kind, its entry. -/
structure Grain where
  idHex : ByteArray
  kind : Grain.Kind
  entry : ByteArray

def worldRoot (l : ByteArray) : Path := [lit "worlds", l]
def storeDir (l : ByteArray) : Path := worldRoot l ++ [lit "store"]
def membersDir (l : ByteArray) : Path := worldRoot l ++ [lit "members"]
def grainDir (l : ByteArray) (g : Grain) : Path := worldRoot l ++ [lit "grains", g.idHex]
def pkgDir (l : ByteArray) (g : Grain) : Path := grainDir l g ++ [lit "pkg"]
def volDir (l : ByteArray) (g : Grain) : Path := grainDir l g ++ [lit "vol"]

/-- The plan of an app grain: run `pkg/<entry>`, read its package, read and write its volume; the
Store and the member workspaces are hidden (the launcher's `Exposed` check is the second barrier). -/
def plan (l : ByteArray) (g : Grain) : Except Refusal Plan := do
  unless clean l do throw .labelUnclean
  unless clean g.idHex do throw .idUnclean
  unless clean g.entry do throw .entryUnclean
  match g.kind with
  | .resident => throw .residentUnsupported
  | .app =>
    pure { program := pkgDir l g ++ [g.entry], read := [pkgDir l g], write := [volDir l g],
           exec := [], connect := [], hidden := [storeDir l, membersDir l] }

/-- Every path a plan ALLOWS. -/
def Plan.allowed (p : Plan) : List Path := p.program :: p.read ++ p.write ++ p.exec ++ p.connect

end Nanodregg.Hosting
