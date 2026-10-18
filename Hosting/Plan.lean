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

and, for a resident only, one socket under each of two further roots of the operator's:

    BROKER/<id>/broker.sock   its broker socket (keybroker, HOSTING-17)        connect
    MEMBER/<id>/nd.sock       its member socket (`nd --stdio` as nd, HOSTING-20) connect

The two socket lists are separate plan fields, each relative to its own root (`Plan.broker`,
`Plan.member`), so a member socket cannot be planned as a broker socket or the reverse. Both
entries are named by the grain's own directory: a plan names no socket of another grain
(`Proofs.Plan.plan_sockets_own`), and grain-launch refuses a frame that does, `foreignPath`.

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

/-- The directories of a World's layout that every plan hides, by name inside `worlds/<l>`
(`Proofs.plan_hidden_layout`: exactly a plan's `hidden`). grain-launch reads them (emitted as
`LAYOUT_HIDDEN`) and refuses to start, `layoutMissing`, when one is absent: the sandbox refuses a
missing hidden path at every launch (HOSTING-24). -/
def layoutHidden : List ByteArray := [lit "store", lit "members"]

/-- A resident's broker socket's name in its own directory of the broker root (HOSTING-17 §2). -/
def brokerSock : ByteArray := lit "broker.sock"

/-- A resident's member socket's name in its own directory of the member root (HOSTING-20): the
socket nd-supervise serves `nd --stdio` on, as nd, over the resident's member workspace
`worlds/<l>/members/<id>` (hidden from every grain). -/
def memberSock : ByteArray := lit "nd.sock"

/-- The socket a resident may connect to under one root: its own directory there, and the root's
one name in it; an app none. -/
def socketOf (name : ByteArray) (g : Grain) : List Path :=
  match g.kind with
  | .app => []
  | .resident => [[g.idHex, name]]

/-- Relative to the broker root: a resident's own broker socket `<id>/broker.sock` (the directory
keybroker names by the same `dirOf`). -/
def brokerOf (g : Grain) : List Path := socketOf brokerSock g

/-- Relative to the member root: a resident's own member socket `<id>/nd.sock`, through which it
reads and writes the World as its member (HOSTING-20, HOSTING-25). -/
def memberOf (g : Grain) : List Path := socketOf memberSock g

/-- The plan of a grain: run `pkg/<entry>`, read its package, read and write its volume, and (a
resident) connect to its own broker socket and its own member socket; the Store and the member
workspaces are hidden (the launcher's `Exposed` check is the second barrier). -/
def plan (l : ByteArray) (g : Grain) : Except Refusal Plan := do
  unless labelOk l do throw .labelUnclean
  unless labelOk g.idHex do throw .idUnclean
  unless Codec.Path.clean g.entry do throw .entryUnclean
  pure { program := pkgDir l g ++ [g.entry], read := [pkgDir l g], write := [volDir l g],
         exec := [], broker := brokerOf g, member := memberOf g, hidden := [storeDir l, membersDir l] }

/-- Every path a plan ALLOWS. -/
def Plan.allowed (p : Plan) : List Path := p.program :: p.read ++ p.write ++ p.exec

end Nanodregg.Hosting
