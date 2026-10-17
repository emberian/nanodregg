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

/-- A byte a Store label may hold: a lowercase ASCII letter, a digit, or `-`. A label names a
directory, and on a case-insensitive (or Unicode-normalising) file system two labels differing in
case or normal form would name ONE world's directory: no uppercase and no non-ASCII byte is
accepted, so two accepted labels name one directory only if they are equal. -/
def labelByte (b : UInt8) : Bool := (97 ≤ b && b ≤ 122) || (48 ≤ b && b ≤ 57) || b == 45

/-- Every byte of `c` from index `i` on, for `n` more bytes, is a label byte (structural, so a
literal label is checked by `decide`). -/
def labelFrom (c : ByteArray) (i : Nat) : (n : Nat) → Bool
  | 0 => true
  | n + 1 => (if h : i < c.size then labelByte c[i] else true) && labelFrom c (i + 1) n

/-- A Store label: one clean component of label bytes. A grain's directory name must be one too
(`dirOf`'s lowercase hex is: `Proofs.Controller.reconcile_labels_deployed`), so two grains never share a
directory on a case-insensitive file system either. -/
def labelOk (l : ByteArray) : Bool := Codec.Path.clean l && labelFrom l 0 l.size

/-- ASCII case folding of one byte, as a case-insensitive file system compares names (the
specification `Proofs.Plan.labels_fold_injective` is stated against; nothing deployed calls it). -/
def foldByte (b : UInt8) : UInt8 := if 65 ≤ b && b ≤ 90 then b + 32 else b

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
  unless labelOk l do throw .labelUnclean
  unless labelOk g.idHex do throw .idUnclean
  unless Codec.Path.clean g.entry do throw .entryUnclean
  match g.kind with
  | .resident => throw .residentUnsupported
  | .app =>
    pure { program := pkgDir l g ++ [g.entry], read := [pkgDir l g], write := [volDir l g],
           exec := [], hidden := [storeDir l, membersDir l] }

/-- Every path a plan ALLOWS. -/
def Plan.allowed (p : Plan) : List Path := p.program :: p.read ++ p.write ++ p.exec

end Nanodregg.Hosting
