/-
# Hosting.Allowance — the operator's allowance objects in the World (HOSTING-13)

The broker's allowances come from the World. One allowance is one meter (`Broker.Allowance`): one
resident, one model, its key slot, price, window, cap and per-ask token bound. It is an ordinary
object of the package `allowance`, and its owner (KERNEL's slot 1) must be the operator: anyone may
create an object of this package, and the broker reads only those `OPERATOR` owns
(`allowanceOf`). Authority is KERNEL's: KERNEL-25 owner-gates `invoke`, and a programmed object
refuses `write` (`hasMethods`), so only the owner, or a member it granted, changes an allowance,
and only through its methods.

State `{cap, keySlot, maxTokens, microPerKTok : nat, model, resident : bytes, revoked : bool,
windowMs : nat}`, one field per KERNEL state slot in that order. `resident` is the resident
grain's World id; the broker names it by `Controller.dirOf`, the name of its socket. The package
has no law. Its two methods are its only change path:
* `revoke` sets `revoked`; every other field is kept;
* `set` replaces `cap`, `keySlot`, `maxTokens`, `microPerKTok` and `windowMs` with its argument, and
  keeps `model`, `resident` and `revoked`. So a revoked allowance stays revoked
  (`Proofs.Allowance.methods_write`), and a different model or resident is a different object.
KERNEL never retires an object (KERNEL-17). Two unrevoked operator allowances for one resident and
model refuse `allowanceAmbiguous`, and the operator ends the ambiguity by revoking one.
Whether the numbers can be applied (a zero window, a price of 0, …) is `Broker.decide`'s one check
(`allowanceMalformed`), not a law: a law would be its twin.
-/
import Hosting.Broker
import Hosting.Controller
import Lang.Std
import Lang.Wire.Data
import Kernel.Receive.Call

namespace Nanodregg.Hosting.Allow

open Nanodregg.Lang Nanodregg.Kernel

def unit : Ty := .record []

/-- The state's fields, in the order of the state type (ascending) and of the slots. -/
def fields : List (Label × Ty) :=
  [("cap", .nat), ("keySlot", .nat), ("maxTokens", .nat), ("microPerKTok", .nat), ("model", .bytes),
   ("resident", .bytes), ("revoked", .bool), ("windowMs", .nat)]

def stateTy : Ty := .record fields

/-- What `set` replaces. -/
def settable : List Label := ["cap", "keySlot", "maxTokens", "microPerKTok", "windowMs"]

def setTy : Ty := .record (fields.filter fun f => settable.contains f.1)

/-- `λ state () req. state with revoked := true`. -/
def revokeT : Term :=
  Std.methodOf stateTy unit (fields.map fun (l, _) => (l, if l = "revoked" then .bool true else .get (.var 2) l))

/-- `λ state arg req. state with the settable fields from arg`. -/
def setT : Term :=
  Std.methodOf stateTy setTy (fields.map fun (l, _) => (l, .get (.var (if settable.contains l then 1 else 2)) l))

/-- The package: no law, the methods `revoke` (0) and `set` (1). -/
def allowance : Package := Std.pkgOf stateTy [] [("revoke", unit, [], revokeT), ("set", setTy, [], setT)]

/-- The index of method `revoke` and of `set` (`Std.pkgOf`'s sorted order,
`Proofs.Allowance.method_indices`). -/
def revokeIndex : Nat := 0
def setIndex : Nat := 1

/-- The package's id under `E`: what an allowance's package slot must hold. -/
def allowanceId {D : Type} (E : Env D) : Option D :=
  (Wire.encodePackage allowance).map fun b => romIdOf E (Controller.packageCell b)

/-! ## Slots -/

/-- The state slot of field `i` of `fields`. -/
def slotAt (i : Nat) : Nat := Receive.stateBase + i

/-- The slots `create` seeds for `resident` and allowance `a`, unrevoked, one field per slot in
`fields` order; `none` when a field is past LANG's bound (a natural ≥ 2^64, bytes past a slot).
`Proofs.Allowance.seed_reads`: the object KERNEL creates from it reads back as `a`. -/
def seed (resident : ByteArray) (a : Broker.Allowance) : Option Kernel.Slots := do
  pure [(slotAt 0, ← Wire.encodeData .nat (.nat a.cap)),
        (slotAt 1, ← Wire.encodeData .nat (.nat a.keySlot)),
        (slotAt 2, ← Wire.encodeData .nat (.nat a.maxTokens)),
        (slotAt 3, ← Wire.encodeData .nat (.nat a.microPerKTok)),
        (slotAt 4, ← Wire.encodeData .bytes (.bytes a.model)),
        (slotAt 5, ← Wire.encodeData .bytes (.bytes resident)),
        (slotAt 6, ← Wire.encodeData .bool (.bool false)),
        (slotAt 7, ← Wire.encodeData .nat (.nat a.windowMs))]

/-- The argument of `set`. -/
def setArgs (a : Broker.Allowance) : Option ByteArray :=
  Wire.encodeData setTy (.record [("cap", .nat a.cap), ("keySlot", .nat a.keySlot),
    ("maxTokens", .nat a.maxTokens), ("microPerKTok", .nat a.microPerKTok), ("windowMs", .nat a.windowMs)])

/-- `revoke`'s argument: the empty record's bytes. -/
def noArgs : Option ByteArray := Wire.encodeData unit (.record [])

def natAt (s : Kernel.Slots) (i : Nat) : Option Nat :=
  match s.get (slotAt i) with
  | some b => match Wire.decodeData .nat b with
    | .ok (.nat n) => some n
    | _ => none
  | none => none

def bytesAt (s : Kernel.Slots) (i : Nat) : Option ByteArray :=
  match s.get (slotAt i) with
  | some b => match Wire.decodeData .bytes b with
    | .ok (.bytes x) => some x
    | _ => none
  | none => none

def boolAt (s : Kernel.Slots) (i : Nat) : Option Bool :=
  match s.get (slotAt i) with
  | some b => match Wire.decodeData .bool b with
    | .ok (.bool x) => some x
    | _ => none
  | none => none

/-- The allowance an object holds, as the broker uses it: the resident's socket name
(`Controller.dirOf` of its id) and the meter's terms. `none` unless the cell is an object of the
allowance package (`pkgId`), owned by `operator`, unrevoked, and every field decodes. -/
def allowanceOf (pkgId operator : ByteArray) (c : Cell) : Option (ByteArray × Broker.Allowance) :=
  let s := c.slots
  if c.kind == Receive.kindObject && s.get Receive.slotPackage == some pkgId &&
      s.get Receive.slotOwner == some operator then
    match boolAt s 6 with
    | some false => do
      pure (Controller.dirOf (← bytesAt s 5),
        ⟨← bytesAt s 4, ← natAt s 1, ← natAt s 3, ← natAt s 7, ← natAt s 0, ← natAt s 2⟩)
    | _ => none
  else none

end Nanodregg.Hosting.Allow
