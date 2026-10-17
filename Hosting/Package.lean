/-
# Hosting.Package — the grain package, generated from `edges`

The lifecycle as a LANG package (decisions/hosting.md HOSTING-3). State
`{entry : bytes, kind : Kind, last : Last, owner : bytes, phase : Phase}`; `Kind`, `Last` and `Phase`
are sums of empty records, so a decoded state can only hold one of their values: the type, not a
code range, is what makes the theorems over `Phase.all` exhaustive. `entry` (the package-relative
program the controller launches) and `kind` (`app | resident`, HOSTING-2) are set at birth and
carried unchanged by every method; `Hosting.Plan` refuses an entry that is not a clean component.

* methods `start`, `stop`, `remove` (indices `Event.index`): each records itself in `last` and
  moves `phase` to `target phase e`, which is the phase unchanged when `(phase, e)` is no edge;
* law `phase`: `checkTerm old.phase new.last new.phase` is `ok` exactly when `admits` (an edge,
  or the born pair `installed → installed` when `last = born`);
* law `owner`: at birth (`last = born`) the state's owner is the creator (`create` judges with
  `principal` = the signer = KERNEL's owner, slot 1); after it, the owner never changes and the
  call's PRINCIPAL is the owner. KERNEL's `invoke` derives `principal` through the grant chain but
  never compares it to the owner (`Receive.invoke`), so without this law any member could stop any
  grain; with it, a member acting through the owner's `invoke:n` grant may run method `n` only.

A law sees state slots, never KERNEL's owner slot, so the owner is a state field the `owner` law
pins to the creator at birth and keeps constant after.
-/
import Hosting.Lifecycle
import Lang.Package
import Lang.Wire.Data
import Kernel.Receive.Call

namespace Nanodregg.Hosting.Grain

open Nanodregg.Lang
open Nanodregg.Hosting

def unit : Ty := .record []

def phaseTy : Ty := .sum (Phase.all.map fun p => (p.label, unit))

/-- What `last` holds: `none` is `born`. In ascending label order (a sum's arms follow it). -/
def lastAll : List (Option Event) := [none, some .remove, some .start, some .stop]

def lastLabel : Option Event → String
  | none => "born"
  | some e => e.label

def lastTy : Ty := .sum (lastAll.map fun o => (lastLabel o, unit))

inductive Kind | app | resident
  deriving DecidableEq, Repr

def Kind.all : List Kind := [.app, .resident]

def Kind.label : Kind → String
  | .app => "app" | .resident => "resident"

def kindTy : Ty := .sum (Kind.all.map fun k => (k.label, unit))

def stateTy : Ty :=
  .record [("entry", .bytes), ("kind", kindTy), ("last", lastTy), ("owner", .bytes), ("phase", phaseTy)]

def phaseV (p : Phase) : Term := .inj phaseTy p.label (.record [])
def lastV (o : Option Event) : Term := .inj lastTy (lastLabel o) (.record [])
def okT : Term := .inj verdictTy "ok" (.record [])
def refusedT (why : String) : Term := .inj verdictTy "refused" (.bytes why.toUTF8)

/-- The verdict for `old.phase = p`, `new.last = o`, `new.phase` at `var 2` (under the two case
binders of `checkTerm`). -/
def leaf (p : Phase) (o : Option Event) : Term :=
  if Phase.all.any (admits p o) then
    .case (.var 2) (Phase.all.map fun q =>
      (q.label, if admits p o q then okT
        else refusedT s!"{p.label} {lastLabel o} {q.label} is not an edge"))
  else refusedT s!"no {lastLabel o} from {p.label}"

/-- `λ a e b. verdict`, closed: `ok` exactly when `admits a e b`. -/
def checkTerm : Term :=
  .lam phaseTy (.lam lastTy (.lam phaseTy
    (.case (.var 2) (Phase.all.map fun p =>
      (p.label, .case (.var 2) (lastAll.map fun o => (lastLabel o, leaf p o)))))))

/-- `λ p. target p e`, closed. -/
def targetTerm (e : Event) : Term :=
  .lam phaseTy (.case (.var 0) (Phase.all.map fun p => (p.label, phaseV (target p e))))

def app3 (f a b c : Term) : Term := .app (.app (.app f a) b) c

/-- Method `e`: `λ s _ r. {s with last = e, phase = target s.phase e}`. -/
def methodTerm (e : Event) : Term :=
  .lam stateTy (.lam unit (.lam reqTy (.record
    [("entry", .get (.var 2) "entry"), ("kind", .get (.var 2) "kind"),
     ("last", lastV (some e)), ("owner", .get (.var 2) "owner"),
     ("phase", .app (targetTerm e) (.get (.var 2) "phase"))])))

/-- Law `phase`: `λ old new r. checkTerm old.phase new.last new.phase`. -/
def phaseLaw : Term :=
  .lam stateTy (.lam stateTy (.lam reqTy
    (app3 checkTerm (.get (.var 2) "phase") (.get (.var 1) "last") (.get (.var 1) "phase"))))

/-- Law `owner`. Under the case binder: var 1 = r, var 2 = new, var 3 = old. -/
def ownerLaw : Term :=
  let born : Term :=
    .ite (.prim .beq (.get (.var 2) "owner") (.get (.var 1) "principal")) okT
      (refusedT "not the creator")
  let live : Term :=
    .ite (.prim .beq (.get (.var 3) "owner") (.get (.var 2) "owner"))
      (.ite (.prim .beq (.get (.var 1) "principal") (.get (.var 3) "owner")) okT
        (refusedT "not the owner"))
      (refusedT "changed")
  .lam stateTy (.lam stateTy (.lam reqTy
    (.case (.get (.var 1) "last") (lastAll.map fun o =>
      (lastLabel o, match o with | none => born | some _ => live)))))

/-- The laws, in the order the judge runs them. -/
def laws : List Label := ["phase", "owner"]

def iface : Ty :=
  .record [("owner", lawTy stateTy), ("phase", lawTy stateTy), ("remove", methodTy stateTy unit),
    ("start", methodTy stateTy unit), ("stop", methodTy stateTy unit)]

def lifecycle : Package :=
  { imports := [], state := stateTy, iface,
    body := .record [("owner", ownerLaw), ("phase", phaseLaw), ("remove", methodTerm .remove),
      ("start", methodTerm .start), ("stop", methodTerm .stop)],
    methods := Event.all.map Event.label, laws }

/-! ## Slots: what `create` seeds and what the controller reads -/

/-- The state's fields at KERNEL's state slots, in `stateTy`'s order. -/
def slotEntry : Nat := Kernel.Receive.stateBase
def slotKind : Nat := Kernel.Receive.stateBase + 1
def slotLast : Nat := Kernel.Receive.stateBase + 2
def slotOwnerField : Nat := Kernel.Receive.stateBase + 3
def slotPhase : Nat := Kernel.Receive.stateBase + 4

def unitD : Data := .record []

/-- The seed of a grain of `kind` running `entry`, owned by `owner`: born, installed. `none` when a
byte string is past LANG's bound (its encoder refuses it). -/
def seed (kind : Kind) (entry owner : ByteArray) : Option Kernel.Slots := do
  let en ← Wire.encodeData .bytes (.bytes entry)
  let k ← Wire.encodeData kindTy (.inj kind.label unitD)
  let l ← Wire.encodeData lastTy (.inj "born" unitD)
  let o ← Wire.encodeData .bytes (.bytes owner)
  let p ← Wire.encodeData phaseTy (.inj initial.label unitD)
  pure [(slotEntry, en), (slotKind, k), (slotLast, l), (slotOwnerField, o), (slotPhase, p)]

/-- A method's argument: the empty record's bytes. -/
def noArgs : Option ByteArray := Wire.encodeData unit unitD

def phaseOfLabel (l : String) : Option Phase := Phase.all.find? (·.label == l)

/-- The phase a grain's state slots hold, decoded at `phaseTy`. -/
def phaseOf (s : Kernel.Slots) : Option Phase :=
  match s.get slotPhase with
  | none => none
  | some b => match Wire.decodeData phaseTy b with
    | .ok (.inj l _) => phaseOfLabel l
    | _ => none

end Nanodregg.Hosting.Grain
