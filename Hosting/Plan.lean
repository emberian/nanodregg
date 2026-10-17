/-
# Hosting.Plan — what a grain may touch: a total function of (store label, grain)

The controller (HOSTING-4) hands the launcher one `Plan` per grain to start; the launcher turns it
into `sandbox::Policy` field for field and spawns through `sandbox::command`, deciding nothing
(`Plan`, `Refusal` and their frames are `Hosting.Wire`).
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
import Hosting.Wire
import Codec.Path

namespace Nanodregg.Hosting

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
  unless Codec.Path.clean l do throw .labelUnclean
  unless Codec.Path.clean g.idHex do throw .idUnclean
  unless Codec.Path.clean g.entry do throw .entryUnclean
  match g.kind with
  | .resident => throw .residentUnsupported
  | .app =>
    pure { program := pkgDir l g ++ [g.entry], read := [pkgDir l g], write := [volDir l g],
           exec := [], hidden := [storeDir l, membersDir l] }

/-- Every path a plan ALLOWS. -/
def Plan.allowed (p : Plan) : List Path := p.program :: p.read ++ p.write ++ p.exec

end Nanodregg.Hosting
