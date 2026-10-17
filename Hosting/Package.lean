/-
# Hosting.Package — the grain package, built from `edges` with LANG's Std generators

The lifecycle as a LANG package (decisions/hosting.md HOSTING-3, HOSTING-5). State
`{entry : bytes, kind : Kind, owner : bytes, phase : Phase}`; `Kind` and `Phase` are sums of empty
records, so a decoded state holds one of their values by its TYPE. `entry` (the package-relative
program the controller launches) and `kind` (`app | resident`, HOSTING-2) are set at birth and
carried unchanged by every method; `Hosting.Plan` refuses an entry that is not a clean component.

* law `phase` = `Std.machine` over `edges`: at birth the phase is `installed`; an invoke of method
  `m` moves `old.phase → new.phase` only along an edge `(old, m, new)`; writes and law changes are
  refused (a programmed object changes only by its methods);
* methods `remove`, `start`, `stop` = `Std.stepTo`: each sets `phase` to its edge's target from the
  current phase, or leaves it (and the law refuses). Their indices are `pkgOf`'s sorted order:
  `Event.index`, pinned to `Std.methodIndex` by `Proofs.Package.index_is_methodIndex`;
* law `owner` (INTERIM, until KERNEL-25 makes `invoke` owner-gated in the kernel): at birth the
  state's owner is the creator (principal); after it the principal is the owner and the owner never
  changes. Without it, today, any member can stop any grain (HOSTING-4). It is deleted, with the
  `owner` field, the day KERNEL-25 lands (HOSTING-5).
-/
import Hosting.Lifecycle
import Lang.Std
import Lang.Wire.Data
import Kernel.Receive.Call

namespace Nanodregg.Hosting.Grain

open Nanodregg.Lang
open Nanodregg.Hosting

def unit : Ty := .record []

def phaseLabels : List Label := Phase.all.map Phase.label

def phaseTy : Ty := Std.stateTy phaseLabels

inductive Kind | app | resident
  deriving DecidableEq, Repr

def Kind.all : List Kind := [.app, .resident]

def Kind.label : Kind → String
  | .app => "app" | .resident => "resident"

def kindTy : Ty := .sum (Kind.all.map fun k => (k.label, unit))

def stateTy : Ty :=
  .record [("entry", .bytes), ("kind", kindTy), ("owner", .bytes), ("phase", phaseTy)]

def methodLabels : List Label := Event.all.map Event.label

/-- The edge list as Std takes it: (from, method label, to). -/
def edgeLabels : List (Label × Label × Label) := edges.map fun (p, e, q) => (p.label, e.label, q.label)

/-- Law `owner` (interim, HOSTING-5): see the module doc. -/
def ownerLaw : Term :=
  let isOwner (a : Std.At) := Term.prim .beq (a.reqF "principal") (a.oldF "owner")
  let kept (a : Std.At) := Term.prim .beq (a.newF "owner") (a.oldF "owner")
  Std.lawOf stateTy
    (fun a => Std.allOf [(.prim .beq (a.newF "owner") (a.reqF "principal"), "not the creator")])
    (fun a => Std.allOf [(isOwner a, "not the owner")])
    (fun a => Std.allOf [(isOwner a, "not the owner"), (kept a, "changed")])

/-- The package, or LANG's refusal of the generator's inputs (`Proofs.Package.lifecycle_built`:
it is built). -/
def lifecycle? : Except Std.StdRefusal Package := do
  let phase ← Std.machine stateTy "phase" phaseLabels initial.label methodLabels edgeLabels
  let ms ← Event.all.mapM fun e => do
    pure (e.label, unit, ← Std.stepTo stateTy "phase" phaseLabels methodLabels e.label edgeLabels)
  pure (Std.pkgOf stateTy [("owner", ownerLaw), ("phase", phase)] ms)

/-! ## Slots: what `create` seeds and what the controller reads -/

/-- The state's fields at KERNEL's state slots, in `stateTy`'s order. -/
def slotEntry : Nat := Kernel.Receive.stateBase
def slotKind : Nat := Kernel.Receive.stateBase + 1
def slotOwnerField : Nat := Kernel.Receive.stateBase + 2
def slotPhase : Nat := Kernel.Receive.stateBase + 3

def unitD : Data := .record []

/-- The seed of a grain of `kind` running `entry`, owned by `owner`, installed. `none` when a byte
string is past LANG's bound (its encoder refuses it). -/
def seed (kind : Kind) (entry owner : ByteArray) : Option Kernel.Slots := do
  let en ← Wire.encodeData .bytes (.bytes entry)
  let k ← Wire.encodeData kindTy (.inj kind.label unitD)
  let o ← Wire.encodeData .bytes (.bytes owner)
  let p ← Wire.encodeData phaseTy (.inj initial.label unitD)
  pure [(slotEntry, en), (slotKind, k), (slotOwnerField, o), (slotPhase, p)]

/-- A method's argument: the empty record's bytes. -/
def noArgs : Option ByteArray := Wire.encodeData unit unitD

def phaseOfLabel (l : String) : Option Phase := Phase.all.find? (·.label == l)

def kindOfLabel (l : String) : Option Kind := Kind.all.find? (·.label == l)

/-- The kind a grain's state slots hold, decoded at `kindTy`. -/
def kindOf (s : Kernel.Slots) : Option Kind :=
  match s.get slotKind with
  | none => none
  | some b => match Wire.decodeData kindTy b with
    | .ok (.inj l _) => kindOfLabel l
    | _ => none

/-- The entry a grain's state slots hold, decoded at `bytes`. -/
def entryOf (s : Kernel.Slots) : Option ByteArray :=
  match s.get slotEntry with
  | none => none
  | some b => match Wire.decodeData .bytes b with
    | .ok (.bytes e) => some e
    | _ => none

/-- The phase a grain's state slots hold, decoded at `phaseTy`. -/
def phaseOf (s : Kernel.Slots) : Option Phase :=
  match s.get slotPhase with
  | none => none
  | some b => match Wire.decodeData phaseTy b with
    | .ok (.inj l _) => phaseOfLabel l
    | _ => none

end Nanodregg.Hosting.Grain
