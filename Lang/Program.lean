/-
# Lang.Program — the language as KERNEL's `Receive.Program`: install check, laws, methods

`program bytesOf digestOf` instantiates `Kernel.Receive.Program D`. Every read goes through the
caller's `Pinned` view (so `receive_congr` covers LANG's reads): a package and every package in its
closure must be pinned, or the receiver refuses `unpinned`.

* `checkInstall` decodes the package (canonical bytes or a named decode refusal), reads each
  import's interface from its pinned ROM cell, and runs `Package.checkWith`.
* `run` loads the closure (each package once, depth ≤ `closureDepthMax`, bodies relocated to the
  closure's indices), decodes the state at the package's state type and the arguments at the
  method's argument type, runs `method state args req` under the call's tick budget and extracts
  its result (`resultTy` at the method's call slots: the calls, then the new state) under what is left of it; the calls are
  KERNEL `Body`s by `Lang.callsOf`.
* `judge` runs every law in force — the package's own, then each extra law package's — on
  `old → new`, each under `lawTicks`, each reading the slots at ITS state type (LANG-11). `refused r`
  is `lawDenied law (label ++ ": " ++ r)`; running out of ticks is `lawDenied law (label ++ ": exhausted")`.
-/
import Kernel.Receive.Call
import Lang.Law
import Lang.Wire.Data
import Lang.Read
import Lang.Call

namespace Nanodregg.Lang

open Nanodregg.Kernel
open Nanodregg.Kernel.Receive

/-- How deep a closure's import graph may be. -/
def closureDepthMax : Nat := 8
/-- The longest reason a law may give, in bytes. -/
def reasonMax : Nat := 256

variable {D : Type} [DecidableEq D]

/-- A loaded closure: package ids in `lib` order, the relocated bodies, the packages. -/
structure Loaded where
  ids : List ByteArray
  lib : List Term
  pkgs : List Package

/-- The interfaces of a closure's packages, in `lib` order: the types `ref` gives them. -/
abbrev Loaded.ifaces (L : Loaded) : List Ty := L.pkgs.map (·.iface)

def faultText : Fault → String
  | .stuck => "stuck" | .overflow => "overflow" | .underflow => "underflow"
  | .divZero => "divZero" | .tooLarge => "tooLarge" | .ticks => "exhausted" | .stack => "stack"

def decodeText (e : Codec.Refusal) : String := s!"decode {repr e}"

section
variable (bytesOf : D → ByteArray) (digestOf : ByteArray → Option D)

/-- The package in a pinned package cell. -/
def readPackage (look : Pinned D) (id : D) : Except (Refusal D) Package := do
  let cell ← readKind look id kindPackage
  match cell.slots.get 0 with
  | none => throw (.malformedCell id 0)
  | some b =>
    match Wire.decodePackage b with
    | .ok p => pure p
    | .error _ => throw (.malformedCell id 0)

def idOf (b : ByteArray) : Except (Refusal D) D :=
  match digestOf b with
  | some d => .ok d
  | none => .error (.program "import is not a digest")

def indexIn (b : ByteArray) : List ByteArray → Option Nat
  | [] => none
  | x :: xs => if x = b then some 0 else (indexIn b xs).map (· + 1)

/-- The interfaces of the closure's packages at positions `gs`. -/
def ifacesAt (pkgs : List Package) : List Nat → Option (List Ty)
  | [] => some []
  | g :: gs =>
    match pkgs[g]?, ifacesAt pkgs gs with
    | some P, some r => some (P.iface :: r)
    | _, _ => none

/-- Append package `p` (imports already loaded at `gis`) to the closure, RE-CHECKING it against its
imports' interfaces (decisions/lang.md LANG-16), its body relocated to the closure's indices. -/
def admitPackage (idb : ByteArray) (p : Package) (acc : Loaded) (gis : List Nat) :
    Except (Refusal D) (Loaded × Nat) :=
  match ifacesAt acc.pkgs gis with
  | none => .error (.program "closure")
  | some ifs =>
    match p.checkWith ifs with
    | .error e => .error (.program e.wire)
    | .ok () =>
      .ok ({ ids := acc.ids ++ [idb], lib := acc.lib ++ [p.body.relocate fun i => gis.getD i 0],
             pkgs := acc.pkgs ++ [p] }, acc.ids.length)

mutual
/-- Load package `idb` and its closure into `acc` (each package once); its index in the closure. -/
def load (look : Pinned D) (fuel : Nat) (idb : ByteArray) (acc : Loaded) :
    Except (Refusal D) (Loaded × Nat) :=
  match indexIn idb acc.ids with
  | some i => .ok (acc, i)
  | none =>
    match fuel with
    | 0 => .error (.program "imports too deep")
    | fuel + 1 =>
      match idOf digestOf idb with
      | .error e => .error e
      | .ok id =>
        match readPackage look id with
        | .error e => .error e
        | .ok p =>
          match loadAll look fuel p.imports acc with
          | .error e => .error e
          | .ok (acc', gis) => admitPackage idb p acc' gis
termination_by (fuel, 0)

def loadAll (look : Pinned D) (fuel : Nat) (ds : List ByteArray) (acc : Loaded) :
    Except (Refusal D) (Loaded × List Nat) :=
  match ds with
  | [] => .ok (acc, [])
  | d :: ds =>
    match load look fuel d acc with
    | .error e => .error e
    | .ok (acc', g) =>
      match loadAll look fuel ds acc' with
      | .error e => .error e
      | .ok (acc'', gs) => .ok (acc'', g :: gs)
termination_by (fuel, ds.length + 1)
end

def checkInstall (look : Pinned D) (b : ByteArray) : Except (Refusal D) Unit := do
  let p ← match Wire.decodePackage b with
    | .ok p => pure p
    | .error e => throw (.program (decodeText e))
  let ifaces ← p.imports.mapM fun d => do
    let id ← idOf digestOf d
    pure (← readPackage look id).iface
  match p.checkWith ifaces with
  | .ok () => pure ()
  | .error e => throw (.program e.wire)

/-- The state slots of a record row: field `i` at `stateBase + i`; `none` if a field has no bytes at
its type (extraction at the state type makes that unreachable; it is refused by name, not written). -/
def stateSlots : List (Label × Ty) → List (Label × Data) → Nat → Option Slots
  | [], [], _ => some []
  | (_, t) :: row, (_, d) :: ds, i =>
    match Wire.encodeData t d, stateSlots row ds (i + 1) with
    | some b, some s => some ((stateBase + i, b) :: s)
    | _, _ => none
  | _, _, _ => none

def readState (row : List (Label × Ty)) (s : Slots) : Except String Data :=
  go row 0
where
  go : List (Label × Ty) → Nat → Except String Data
    | [], _ => .ok (.record [])
    | (ℓ, t) :: row, i =>
      match s.get (stateBase + i) with
      | none => .error s!"state field {ℓ} missing"
      | some b =>
        match Wire.decodeData t b, go row (i + 1) with
        | .ok d, .ok (.record ds) => .ok (.record ((ℓ, d) :: ds))
        | .error e, _ => .error s!"state field {ℓ}: {decodeText e}"
        | _, .error e => .error e
        | _, _ => .error "state"

/-- The occasion as data at `occasionTy`; a law replacement's (and an adoption's) incoming ids as
their bytes, concatenated in the call's order (digests are fixed-width, so the concatenation is unambiguous). -/
def occasionData : Occasion D → Data
  | .birth => .inj "birth" (.record [])
  | .write => .inj "write" (.record [])
  | .relaw ls => .inj "relaw" (.bytes (ls.foldl (fun acc l => acc ++ bytesOf l) .empty))
  | .adopt ls => .inj "adopt" (.bytes (ls.foldl (fun acc l => acc ++ bytesOf l) .empty))
  | .invoke m => .inj "invoke" (.nat m)

/-- The occasion fits the language's data: a method index is a natural, a law list's bytes one
byte value. -/
def occasionOk : Occasion D → Bool
  | .birth | .write => true
  | .relaw ls | .adopt ls => decide ((ls.foldl (fun acc l => acc ++ bytesOf l) .empty).size ≤ Bounds.bytesMax)
  | .invoke m => decide (m < Bounds.natLimit)

/-- The request fits the language's data: its member and object digests fit a byte value, its window fits
a natural, its occasion fits `occasionTy`. KERNEL bounds the window only at admission
(`checkBounds`, after the receivers ran), so the language asserts it where the request enters a
run (law 4). -/
def reqOk (r : Req D) : Bool :=
  decide ((bytesOf r.agent).size ≤ Bounds.bytesMax) && decide ((bytesOf r.principal).size ≤ Bounds.bytesMax) &&
    decide ((bytesOf r.self).size ≤ Bounds.bytesMax) &&
    decide (r.notBefore < Bounds.natLimit) && decide (r.validUntil < Bounds.natLimit) &&
    occasionOk bytesOf r.occasion

def reqData (r : Req D) : Data :=
  .record [("agent", .bytes (bytesOf r.agent)), ("notBefore", .nat r.notBefore),
    ("occasion", occasionData bytesOf r.occasion),
    ("principal", .bytes (bytesOf r.principal)), ("self", .bytes (bytesOf r.self)),
    ("validUntil", .nat r.validUntil)]

/-- Apply field `ℓ` of closure body `g` to values bound as `var 2, var 1, var 0`. -/
def apply3 (g : Nat) (ℓ : Label) : Term :=
  .app (.app (.app (.get (.ref g) ℓ) (.var 2)) (.var 1)) (.var 0)

def recordRow : Ty → List (Label × Ty)
  | .record r => r
  | _ => []

def reasonText (r : ByteArray) : String :=
  let r := r.extract 0 reasonMax
  (String.fromUTF8? r).getD s!"{r.size} bytes"

/-- Every law of the package at closure index `g` (whose id is `law`) on `old → new`, each run by
the one law runner `runLaw` on the package's field. -/
def judgeOne (look : Pinned D) (law : D) (old new : Slots) (r : Req D) :
    Except (Refusal D) Unit := do
  unless reqOk bytesOf r do throw (.program "request out of bounds")
  let (L, g) ← load digestOf look closureDepthMax (bytesOf law) ⟨[], [], []⟩
  let some p := L.pkgs[g]? | throw (.program "closure")
  let row := recordRow p.state
  let deny (why : String) : Refusal D := .lawDenied law why
  let o ← match readState row old with | .ok d => pure d | .error e => throw (deny e)
  let n ← match readState row new with | .ok d => pure d | .error e => throw (deny e)
  for ℓ in p.laws do
    match runLaw L.lib (.get (.ref g) ℓ) o n (reqData bytesOf r) with
    | .ok (.ok ()) => pure ()
    | .ok (.error why) => throw (deny s!"{ℓ}: {reasonText why}")
    | .error f => throw (deny s!"{ℓ}: {faultText f}")

def judge (look : Pinned D) (pkg : Option D) (laws : List D) (old new : Slots) (r : Req D) :
    Except (Refusal D) Unit := do
  if let some p := pkg then judgeOne bytesOf digestOf look p old new r
  for l in laws do judgeOne bytesOf digestOf look l old new r

/-- Method `method` of package `p`: its label, its argument type and its call slots (the one
resolution: the run and the resident readers below all ask here). -/
def resolveMethod (p : Package) (method : Nat) : Except (Refusal D) (Label × Ty × List Ty) := do
  let some ℓ := p.methods[method]? | throw (.program s!"no method {method}")
  let some mty := Row.find? ℓ (recordRow p.iface) | throw (.program s!"no method {ℓ}")
  let some (A, ks) := methodSig p.state mty | throw (.program s!"method {ℓ}")
  pure (ℓ, A, ks)

/-- Run method `method` of package `pkg` on `state`: the new state slots and the calls the method
makes as the object (`callsOf`, in slot order), with what the run cost (WASTE rows, PROTOCOL-4):
the machine steps the method and its extraction used, and the packages of the closure loaded and
re-checked (LANG-16). `runMethod` and `program`'s `run` are its components, so a measured number
is the deployed run's. -/
def runMeasured (look : Pinned D) (pkg : D) (state : Slots) (method : Nat) (args : ByteArray)
    (r : Req D) (budget : Nat) : Except (Refusal D) (Slots × List (Body D) × Nat × Nat) := do
  unless reqOk bytesOf r do throw (.program "request out of bounds")
  let (L, g) ← load digestOf look closureDepthMax (bytesOf pkg) ⟨[], [], []⟩
  let some p := L.pkgs[g]? | throw (.program "closure")
  let (ℓ, A, ks) ← resolveMethod p method
  let row := recordRow p.state
  let s ← match readState row state with | .ok d => pure d | .error e => throw (.program e)
  let a ← match Wire.decodeData A args with
    | .ok d => pure d
    | .error e => throw (.program s!"arguments: {decodeText e}")
  let env := [(reqData bytesOf r).toVal, a.toVal, s.toVal]
  match run L.lib Bounds.stackMax budget 0 (State.init (apply3 g ℓ) env) with
  | .fault f _ => throw (.program s!"{ℓ}: {faultText f}")
  | .value v used =>
    match (Machine.mk L.lib).extract (resultTy p.state ks) (budget - used) v with
    | .ok (.record [("calls", c), ("state", .record ds)], left) =>
      match stateSlots row ds 0 with
      | some slots => do
        let calls ← callsOf digestOf c
        pure (slots, calls, budget - left, L.pkgs.length)
      | none => throw (.program s!"{ℓ}: state bytes")
    | .ok _ => throw (.program s!"{ℓ}: state")
    | .error f => throw (.program s!"{ℓ}: {faultText f}")

def runMethod (look : Pinned D) (pkg : D) (state : Slots) (method : Nat) (args : ByteArray)
    (r : Req D) (budget : Nat) : Except (Refusal D) (Slots × List (Body D)) :=
  (runMeasured bytesOf digestOf look pkg state method args r budget).map fun x => (x.1, x.2.1)

/-! ## The resident readers: TEXT at a package's types (what `nd create --pkg` and `nd invoke` sign)

A reader refusal is `program` with its `name @offset` text (law 7's convention for `program`
reasons: the first token is the name). -/

def readAt (T : Ty) (text : String) : Except (Refusal D) Data :=
  match Read.readData T text with
  | .ok d => .ok d
  | .error e => .error (.program e.text)

/-- A seed state read at package `pkg`'s state type, as the object's state slots. -/
def seedOf (look : Pinned D) (pkg : D) (text : String) : Except (Refusal D) Slots := do
  let p ← readPackage look pkg
  match ← readAt p.state text with
  | .record ds =>
    match stateSlots (recordRow p.state) ds 0 with
    | some s => pure s
    | none => throw (.program "seed: no bytes at the state type")
  | _ => throw (.program "seed: not a record")

/-- Method `method`'s arguments read at its argument type, as the bytes the run decodes. -/
def argsOf (look : Pinned D) (pkg : D) (method : Nat) (text : String) : Except (Refusal D) ByteArray := do
  let p ← readPackage look pkg
  let (_, A, _) ← resolveMethod p method
  match Wire.encodeData A (← readAt A text) with
  | some b => pure b
  | none => throw (.program "arguments: no bytes at the argument type")

end

/-- The language, as the kernel's receivers see it. -/
def program (bytesOf : D → ByteArray) (digestOf : ByteArray → Option D) : Program D where
  checkInstall := checkInstall digestOf
  judge := judge bytesOf digestOf
  -- the slots, the calls the method makes as the object, and the ticks it used (LEDGER-8 (e))
  run := fun look pkg state method args r budget =>
    (runMeasured bytesOf digestOf look pkg state method args r budget).map fun x => (x.1, x.2.1, x.2.2.1)

end Nanodregg.Lang
