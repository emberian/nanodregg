/-
# Lang.Program — the language as KERNEL's `Receive.Program`: install check, laws, methods

`program bytesOf digestOf` instantiates `Kernel.Receive.Program D`. Every read goes through the
caller's `Pinned` view (so `receive_congr` covers LANG's reads): a package and every package in its
closure must be pinned, or the receiver refuses `unpinned`.

* `checkInstall` decodes the package (canonical bytes or a named decode refusal), loads its imports'
  closure exactly as a run does (each import pinned, decoded and RE-CHECKED by `admitContextual` at
  its own holes, depth one below the package's own load), and admits the package by that same
  admission over those interfaces (LANG-35, LANG-78).
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
import Lang.Rel
import Lang.LiveHoles

namespace Nanodregg.Lang

open Nanodregg.Kernel
open Nanodregg.Kernel.Receive

/-- How deep a closure's import graph may be. -/
def closureDepthMax : Nat := 8
/-- The longest reason a law may give, in bytes. -/
def reasonMax : Nat := Bounds.reasonMax

variable {D : Type} [DecidableEq D]

/-- A loaded closure: package ids in `lib` order, the relocated bodies, the packages. -/
structure Loaded where
  ids : List ByteArray
  lib : List Term
  pkgs : List Package

/-- The interfaces of a closure's packages, in `lib` order: the types `ref` gives them. -/
abbrev Loaded.ifaces (L : Loaded) : List Ty := L.pkgs.map (·.iface)

def reasonText (r : ByteArray) : String :=
  let r := r.extract 0 reasonMax
  (String.fromUTF8? r).getD s!"{r.size} bytes"

def faultText : Fault → String
  | .stuck => "stuck" | .overflow => "overflow" | .underflow => "underflow"
  | .divZero => "divZero" | .tooLarge => "tooLarge" | .ticks => "exhausted" | .stack => "stack"
  | .refused why => s!"refused {reasonText why}"

def decodeText (e : Codec.Refusal) : String := s!"decode {repr e}"

section
variable (bytesOf : D → ByteArray) (digestOf : ByteArray → Option D) (rc : ReceiptCheck)

/-- The package in a pinned package cell. The cell must be ROM (install's birth, `Receive.install`):
what a package id reads is then what it read at install, at every World a fold reaches
(`Kernel.Proofs.Frame.fold_rom`), so a description read at one World and an invoke planned at a
later one read the same package (HOSTING-43). A package cell of another discipline is
`malformedCell`. -/
def readPackage (look : Pinned D) (id : D) : Except (Refusal D) Package := do
  let cell ← readKind look id kindPackage
  if cell.discipline ≠ .rom then throw (.malformedCell id 0)
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

/-- Every digest in `ds` is a digest of the World (LANG-38: an id enters a run only as one). -/
def digestsOk (ds : List ByteArray) : Bool := ds.all fun b => (digestOf b).isSome

/-- Install's and every load's id-literal check: the checked package, or `notDigest` when a
digest literal of its body is not a digest of the World (LANG-38). -/
def checkLits (p : Package) : Except (Refusal D) Unit :=
  if digestsOk digestOf p.body.digestLits then .ok () else .error (.program "notDigest")

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
      match checkLits digestOf p with
      | .error e => .error e
      | .ok () =>
      .ok ({ ids := acc.ids ++ [idb], lib := acc.lib ++ [p.body.relocate fun i => gis.getD i 0],
             pkgs := acc.pkgs ++ [p] }, acc.ids.length)

mutual
/-- Load package `idb` and its closure into `acc` (each package once); its index in the closure. -/
def loadUsing (admit : ByteArray → Package → Loaded → List Nat → Except (Refusal D) (Loaded × Nat)) (look : Pinned D) (fuel : Nat) (idb : ByteArray) (acc : Loaded) :
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
          match loadAllUsing admit look fuel p.imports acc with
          | .error e => .error e
          | .ok (acc', gis) => admit idb p acc' gis
termination_by (fuel, 0)

def loadAllUsing (admit : ByteArray → Package → Loaded → List Nat → Except (Refusal D) (Loaded × Nat)) (look : Pinned D) (fuel : Nat) (ds : List ByteArray) (acc : Loaded) :
    Except (Refusal D) (Loaded × List Nat) :=
  match ds with
  | [] => .ok (acc, [])
  | d :: ds =>
    match loadUsing admit look fuel d acc with
    | .error e => .error e
    | .ok (acc', g) =>
      match loadAllUsing admit look fuel ds acc' with
      | .error e => .error e
      | .ok (acc'', gs) => .ok (acc'', g :: gs)
termination_by (fuel, ds.length + 1)
end

/-- The closed specialization of the shared closure traversal. -/
def load (look : Pinned D) (fuel : Nat) (idb : ByteArray) (acc : Loaded) :
    Except (Refusal D) (Loaded × Nat) :=
  loadUsing digestOf (admitPackage digestOf) look fuel idb acc

def loadAll (look : Pinned D) (fuel : Nat) (ds : List ByteArray) (acc : Loaded) :
    Except (Refusal D) (Loaded × List Nat) :=
  loadAllUsing digestOf (admitPackage digestOf) look fuel ds acc

/-- The cell ids a ROM pin names (E1): each enters a run as a digest of the World (LANG-38). -/
def SupportPin.cellIds : SupportPin → List ByteArray
  | .row .. => []
  | .cell id => [id]
  | .cellLaw id law => [id, law]
  | .cellPackage id pkg => [id, pkg]

/-- Every cell id a ROM names, in its supports, hypotheses and guard pin. -/
def HoleROM.cellIds (h : HoleROM) : List ByteArray :=
  h.code.flatMap (fun c => c.supports.flatMap SupportPin.cellIds) ++
    h.hypotheses.flatMap (fun o => (o.map SupportPin.cellIds).getD []) ++
    (h.guardPin.map SupportPin.cellIds).getD []

/-- All ROM code, including unselected candidates, passes the World's literal boundary; so does
every cell id its pins name. -/
def checkROMLits (p : Package) : Except (Refusal D) Unit :=
  if digestsOk digestOf (p.body.digestLits ++ p.holes.flatMap
      (fun h => h.guard.digestLits ++ h.code.flatMap (fun c => c.body.digestLits) ++ h.cellIds))
  then .ok () else .error (.program "notDigest")

/-- A residual hole is a typed refusal when no row view is available (install
and law checking). Ordinary fields still evaluate; no selected code is guessed. -/
def unresolvedBody (p : Package) : Except HoleRefusal Term :=
  if p.holes.isEmpty then .ok p.body
  else match Term.fillBounded Wire.nodeMax 1
    (fun n => ((holeSignature p.holes).find? (fun d => d.name == n)).map
      (fun d => .refuse d.ty "holeUnresolved".toUTF8)) p.body with
    | .error b => .error (.expansion b)
    | .ok t => .ok t

/-- Shared live admission. The package retained in Loaded is the original ROM;
only the transient machine library receives an instantiated body. -/
def admitContextual (prepare : List Ty → Package → Except HoleRefusal Term)
    (idb : ByteArray) (p : Package) (acc : Loaded) (gis : List Nat) :
    Except (Refusal D) (Loaded × Nat) :=
  if p.holes.isEmpty then admitPackage digestOf idb p acc gis
  else match ifacesAt acc.pkgs gis with
  | none => .error (.program "closure")
  | some ifs =>
    match p.checkContextual ifs with
    | .error e => .error (.program e.wire)
    | .ok () =>
      match prepare ifs p with
      | .error e => .error (.program e.wire)
      | .ok body =>
        match checkE ifs body p.iface (Ω := []) with
        | .error e => .error (.program (HoleRefusal.instanceType e).wire)
        | .ok () =>
          match checkROMLits digestOf p, checkLits digestOf { p with body } with
          | .ok (), .ok () =>
            .ok ({ ids := acc.ids ++ [idb],
                   lib := acc.lib ++ [body.relocate fun i => gis.getD i 0],
                   pkgs := acc.pkgs ++ [p] }, acc.ids.length)
          | .error e, _ | _, .error e => .error e

def loadContextual (look : Pinned D) (fuel : Nat) (idb : ByteArray) (acc : Loaded) :
    Except (Refusal D) (Loaded × Nat) :=
  loadUsing digestOf (admitContextual digestOf (fun _ => unresolvedBody)) look fuel idb acc

def loadAllContextual (look : Pinned D) (fuel : Nat) (ds : List ByteArray) (acc : Loaded) :
    Except (Refusal D) (Loaded × List Nat) :=
  loadAllUsing digestOf (admitContextual digestOf (fun _ => unresolvedBody)) look fuel ds acc

def loadLive (rv : RowView D) (self : D) (look : Pinned D) (fuel : Nat)
    (idb : ByteArray) (acc : Loaded) : Except (Refusal D) (Loaded × Nat) :=
  loadUsing digestOf (admitContextual digestOf (fun Δ p =>
    (instantiateHoles digestOf look rv self Δ p).map (·.body))) look fuel idb acc

/-- Conservative preparation charge derived entirely from the actual ROM syntax;
the selected candidate cannot exceed the maximum over its committed candidates. -/
def Package.preparationCost (p : Package) : Nat :=
  p.holeCharge ((p.holes.flatMap (fun h => h.code)).foldl (fun n c => max n (Term.nodes c.body)) 1)


/-- The install check (LANG-35, LANG-78): the package decoded (canonical bytes or a named decode
refusal), its imports' closure loaded by the one admission every load uses (`admitContextual`:
each package of the closure admitted at ITS OWN holes, as a run admits it, one depth below the
package's own load), and the package itself admitted by that same admission over those imports.
That is the tail of `loadContextual` of a cell holding `b` (`install_loads`). Install has no row
view, so a hole is prepared as its typed refusal (`unresolvedBody`), as a law's load prepares it;
a run prepares it from the caller's pinned rows (`loadLive`). -/
def checkInstall (look : Pinned D) (b : ByteArray) : Except (Refusal D) Unit := do
  let p ← match Wire.decodePackage b with
    | .ok p => pure p
    | .error e => throw (.program (decodeText e))
  let (L, gis) ← loadAllContextual digestOf look (closureDepthMax - 1) p.imports ⟨[], [], []⟩
  let _ ← admitContextual digestOf (fun _ => unresolvedBody) b p L gis
  pure ()

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
        | .ok d, .ok (.record ds) =>
          if digestsOk digestOf d.digests then .ok (.record ((ℓ, d) :: ds))
          else .error s!"state field {ℓ}: not a digest"
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
  | .retire => .inj "retire" (.record [])

/-- The occasion fits the language's data: a method index is a natural, a law list's bytes one
byte value. -/
def occasionOk : Occasion D → Bool
  | .birth | .write | .retire => true
  | .relaw ls | .adopt ls => decide ((ls.foldl (fun acc l => acc ++ bytesOf l) .empty).size ≤ Bounds.bytesMax)
  | .invoke m => decide (m < Bounds.natLimit)

/-- The request fits the language's data: its member and object digests fit a byte value, its window fits
a natural, its occasion fits `occasionTy`. KERNEL bounds the window only at admission
(`checkBounds`, after the receivers ran), so the language asserts it where the request enters a
run (law 4). -/
def reqOk (r : Req D) : Bool :=
  decide ((bytesOf r.agent).size ≤ Bounds.digestBytesMax) &&
    decide ((bytesOf r.principal).size ≤ Bounds.digestBytesMax) &&
    decide ((bytesOf r.self).size ≤ Bounds.digestBytesMax) &&
    decide (r.notBefore < Bounds.natLimit) && decide (r.validUntil < Bounds.natLimit) &&
    occasionOk bytesOf r.occasion

def reqData (r : Req D) : Data :=
  .record [("agent", .digest (bytesOf r.agent)), ("notBefore", .nat r.notBefore),
    ("occasion", occasionData bytesOf r.occasion),
    ("principal", .digest (bytesOf r.principal)), ("self", .digest (bytesOf r.self)),
    ("validUntil", .nat r.validUntil)]

/-- Apply field `ℓ` of closure body `g` to values bound as `var 2, var 1, var 0`. -/
def apply3 (g : Nat) (ℓ : Label) : Term :=
  .app (.app (.app (.get (.ref g) ℓ) (.var 2)) (.var 1)) (.var 0)

/-- Apply method `ℓ` of closure body `g` to its rows, state, arguments and request, bound as
`var 3, var 2, var 1, var 0` (LANG-49: rows first). -/
def apply4 (g : Nat) (ℓ : Label) : Term :=
  .app (.app (.app (.app (.get (.ref g) ℓ) (.var 3)) (.var 2)) (.var 1)) (.var 0)

def recordRow : Ty → List (Label × Ty)
  | .record r => r
  | _ => []

/-- Every law of the package at closure index `g` (whose id is `law`) on `old → new`, each run by
the one law runner `runLaw` on the package's field. -/
def judgeOneWith (loader : Pinned D → Nat → ByteArray → Loaded → Except (Refusal D) (Loaded × Nat)) (look : Pinned D) (law : D) (old new : Slots) (r : Req D) :
    Except (Refusal D) Unit := do
  unless reqOk bytesOf r do throw (.program "request out of bounds")
  let (L, g) ← loader look closureDepthMax (bytesOf law) ⟨[], [], []⟩
  let some p := L.pkgs[g]? | throw (.program "closure")
  let row := recordRow p.state
  let deny (why : String) : Refusal D := .lawDenied law why
  let o ← match readState digestOf row old with | .ok d => pure d | .error e => throw (deny e)
  let n ← match readState digestOf row new with | .ok d => pure d | .error e => throw (deny e)
  for ℓ in p.laws do
    match runLaw L.lib (.get (.ref g) ℓ) o n (reqData bytesOf r) with
    | .ok (.ok ()) => pure ()
    | .ok (.error why) => throw (deny s!"{ℓ}: {reasonText why}")
    | .error f => throw (deny s!"{ℓ}: {faultText f}")

def judgeOne (look : Pinned D) (law : D) (old new : Slots) (r : Req D) : Except (Refusal D) Unit :=
  judgeOneWith bytesOf digestOf (load digestOf) look law old new r

def judgeContextual (look : Pinned D) (pkg : Option D) (laws : List D) (old new : Slots) (r : Req D) :
    Except (Refusal D) Unit := do
  if let some p := pkg then
    judgeOneWith bytesOf digestOf (loadContextual digestOf) look p old new r
  for l in laws do
    judgeOneWith bytesOf digestOf (loadContextual digestOf) look l old new r

def judge (look : Pinned D) (pkg : Option D) (laws : List D) (old new : Slots) (r : Req D) :
    Except (Refusal D) Unit := do
  if let some p := pkg then judgeOne bytesOf digestOf look p old new r
  for l in laws do judgeOne bytesOf digestOf look l old new r

/-- Method `method` of package `p`: its label, its argument type and its call slots (the one
resolution: the run and the resident readers below all ask here). -/
def resolveMethod (p : Package) (method : Nat) : Except (Refusal D) (Label × Sig) := do
  let some ℓ := p.methods[method]? | throw (.program s!"no method {method}")
  let some mty := Row.find? ℓ (recordRow p.iface) | throw (.program s!"no method {ℓ}")
  let some sg := methodSig p.state p.rels mty | throw (.program s!"method {ℓ}")
  pure (ℓ, sg)

/-- The peer reads method `ℓ` of `p` declares (PROT-6; `[]`: none). -/
def Package.peerReads (p : Package) (ℓ : Label) : List (Label × RelRead) :=
  match Row.find? ℓ (recordRow p.iface) with
  | some t => methodPeer p.rels t
  | none => []

/-- The object a peer read is under (PROT-6): the member of the argument's `pair` that is not the
reader, each a digest of the World (`digestOf`); a pair that does not name the reader is
`notParty`, one that names it twice `samePeer`. -/
def peerOf (self : D) (args : Data) : Except (Refusal D) D := do
  let some (.record [("a", .digest a), ("b", .digest b)]) := args.field "pair"
    | throw (.program "peer: no pair")
  if a == b then throw (.program "peer: samePeer")
  let other ← if a == bytesOf self then pure b
    else if b == bytesOf self then pure a
    else throw (.program "peer: notParty")
  match digestOf other with
  | some p => pure p
  | none => throw (.program "peer: not a digest")

/-- A method's rows argument (LANG-49, PROT-6): its own reads (`readsData` under `self`), and, when
it declares peer reads `ps`, the SAME reads under its peer (`readsData` under `peerOf`), at the field
`peer`. The peer is a live object of THIS package (`readKind` first: an unpinned peer is the
kernel's own `unpinned`, by name; then its package slot), so its relations are this package's and
no foreign declaration is read. Every row of either part is a row the caller pinned (`RowView`). -/
def methodReads (look : Pinned D) (pkg : D) (rels : List (Label × RelDecl)) (rv : RowView D) (self : D)
    (args : Data) (rs ps : List (Label × RelRead)) : Except (Refusal D) Data := do
  let own ← readsData digestOf rc look rels rv self rs args
  if ps.isEmpty then return own
  let peer ← peerOf bytesOf digestOf self args
  let cell ← readKind look peer kindObject
  unless cell.slots.get slotPackage == some (bytesOf pkg) do throw (.program "peer: another package")
  let pd ← readsData digestOf rc look rels rv peer ps args
  match own with
  | .record fs => pure (.record (Row.sort (fs ++ [(peerLabel, pd)])))
  | d => pure d

/-- What a method run starts from once every boundary check has passed (LANG-41): the closure's
bodies and size, the method's label, the state's record row, the type the result is extracted at,
the state and the arguments as data, and the term the machine evaluates in its environment
(`[req, args, state]`). Every id that enters a run enters here: a request's members and object
from the World (`reqData`), the state and the arguments each checked by `digestOf`, and the
closure's id literals checked at load (`checkLits`). -/
structure RunSetup where
  lib : List Term
  pkgs : Nat
  /-- the package's index in the closure, and its relations (LANG-49: guards run at `g`) -/
  g : Nat
  rels : List (Label × RelDecl)
  label : Label
  row : List (Label × Ty)
  ty : Ty
  /-- the method's declared call slot types (LANG-33); `callsOf` reads the calls against them,
  encoding each invoke's `args` at its slot's argument type (LANG-77) -/
  calls : List Ty
  state : Data
  args : Data
  /-- the rows argument (LANG-49): what `readsData` built from the caller's view; the env's fourth value -/
  reads : Data
  term : Term
  env : Env
  preparation : Nat := 0
  /-- the method's grades (LANG-89): `checkMoves` bounds the calls the run returns -/
  effect : Effect := {}

/-- The front half of every method run: the request's bounds, the closure loaded and re-checked
(LANG-16), the method resolved, the state read at its row and the arguments decoded at their type,
each refused by name. `runMeasured` runs from it; the WASTE counter (`Lang.Need`) counts from it. -/
def runSetupWith (loader : Pinned D → Nat → ByteArray → Loaded → Except (Refusal D) (Loaded × Nat))
    (charge : Loaded → Nat) (look : Pinned D) (rv : RowView D) (pkg : D) (state : Slots) (method : Nat) (args : ByteArray)
    (r : Req D) : Except (Refusal D) RunSetup := do
  unless reqOk bytesOf r do throw (.program "request out of bounds")
  let (L, g) ← loader look closureDepthMax (bytesOf pkg) ⟨[], [], []⟩
  let some p := L.pkgs[g]? | throw (.program "closure")
  let (ℓ, sg) ← resolveMethod p method
  let row := recordRow p.state
  let s ← match readState digestOf row state with | .ok d => pure d | .error e => throw (.program e)
  let a ← match Wire.decodeData sg.arg args with
    | .ok d => if digestsOk digestOf d.digests then pure d else throw (.program "arguments: not a digest")
    | .error e => throw (.program s!"arguments: {decodeText e}")
  let rows ← methodReads bytesOf digestOf rc look pkg p.rels rv r.self a sg.reads (p.peerReads ℓ)
  pure { lib := L.lib, pkgs := L.pkgs.length, g, rels := p.rels, label := ℓ, row,
         ty := resultTy p.state sg.calls (editTy p.rels) sg.edits, calls := sg.calls, state := s,
         args := a, reads := rows, term := apply4 g ℓ, env := [(reqData bytesOf r).toVal, a.toVal, s.toVal, rows.toVal], preparation := charge L,
         effect := p.effectOf ℓ }

/-- Closed specialization retained for its landed statements. -/
def runSetup (look : Pinned D) (rv : RowView D) (pkg : D) (state : Slots) (method : Nat) (args : ByteArray)
    (r : Req D) : Except (Refusal D) RunSetup :=
  runSetupWith bytesOf digestOf rc (load digestOf) (fun _ => 0) look rv pkg state method args r

def Loaded.preparationCost (L : Loaded) : Nat :=
  (L.pkgs.map Package.preparationCost).foldl (· + ·) 0

/-- The deployed setup reauthenticates every contextual selection for this invocation. -/
def runSetupLive (look : Pinned D) (rv : RowView D) (pkg : D) (state : Slots) (method : Nat) (args : ByteArray)
    (r : Req D) : Except (Refusal D) RunSetup :=
  runSetupWith bytesOf digestOf rc (loadLive digestOf rv r.self)
    Loaded.preparationCost
    look rv pkg state method args r

/-- Every edit judged by its relation's guard, if it has one, over the state before the run, the
request, and the edit with its old row (LANG-49: O(edits), never a relation; one law runner,
`runLaw`). Every edit's old row is found first (`guardOld`), so an unpinned upsert or retract is
refused `rowUnpinned` before any guard runs (LANG-59). -/
def guardEdits (S : RunSetup) (rv : RowView D) (pkg : D) (r : Req D) (es : List (Edit D)) :
    Except (Refusal D) Unit := do
  let olds ← es.mapM (guardOld digestOf rv r.self)
  (es.zip olds).forM fun (e, o) =>
    match e.decl.guard with
    | none => .ok ()
    | some gl =>
      match runLaw S.lib (.get (.ref S.g) gl) S.state (reqData bytesOf r) (guardIn e.data o) with
      | .ok (.ok ()) => .ok ()
      | .ok (.error why) => .error (.lawDenied pkg s!"{gl}: {reasonText why}")
      | .error f => .error (.lawDenied pkg s!"{gl}: {faultText f}")

/-- Run method `method` of package `pkg` on `state`: the new state slots and the calls the method
makes as the object (`callsOf`, in slot order), with what the run cost (WASTE rows, PROTOCOL-4):
the machine steps the method and its extraction used, and the packages of the closure loaded and
re-checked (LANG-16). `runMethod` and `program`'s `run` are its components, so a measured number
is the deployed run's. -/
def runMeasuredWith
    (setup : Pinned D → RowView D → D → Slots → Nat → ByteArray → Req D → Except (Refusal D) RunSetup) (look : Pinned D) (rv : RowView D) (pkg : D) (state : Slots) (method : Nat) (args : ByteArray)
    (r : Req D) (budget : Nat) :
    Except (Refusal D) (Slots × List (Body D) × List (RowSlot D × RowAct) × Nat × Nat) := do
  let S ← setup look rv pkg state method args r
  if S.preparation > budget then throw (.program "holeTicks")
  let machineBudget := budget - S.preparation
  match run S.lib Bounds.stackMax machineBudget 0 (State.init S.term S.env) with
  | .fault f _ => throw (.program s!"{S.label}: {faultText f}")
  | .value v used =>
    match (Machine.mk S.lib).extract S.ty (machineBudget - used) v with
    | .ok (.record [("calls", c), ("edits", e), ("state", .record ds)], left) =>
      match stateSlots S.row ds 0 with
      | some slots => do
        let calls ← callsOf digestOf S.calls c
        checkMoves S.effect calls
        let es ← editsOf S.rels r.self e
        guardEdits bytesOf digestOf S rv pkg r es
        checkLegs digestOf rv r.self calls es
        pure (slots, calls, es.map (fun x => (x.slot, x.act)), budget - left, S.pkgs)
      | none => throw (.program s!"{S.label}: state bytes")
    | .ok _ => throw (.program s!"{S.label}: state")
    | .error f => throw (.program s!"{S.label}: {faultText f}")

def runMeasured (look : Pinned D) (rv : RowView D) (pkg : D) (state : Slots) (method : Nat) (args : ByteArray)
    (r : Req D) (budget : Nat) :
    Except (Refusal D) (Slots × List (Body D) × List (RowSlot D × RowAct) × Nat × Nat) :=
  runMeasuredWith bytesOf digestOf (runSetup bytesOf digestOf rc) look rv pkg state method args r budget

def runMeasuredLive (look : Pinned D) (rv : RowView D) (pkg : D) (state : Slots) (method : Nat) (args : ByteArray)
    (r : Req D) (budget : Nat) :
    Except (Refusal D) (Slots × List (Body D) × List (RowSlot D × RowAct) × Nat × Nat) :=
  runMeasuredWith bytesOf digestOf (runSetupLive bytesOf digestOf rc) look rv pkg state method args r budget

def runMethod (look : Pinned D) (rv : RowView D) (pkg : D) (state : Slots) (method : Nat) (args : ByteArray)
    (r : Req D) (budget : Nat) : Except (Refusal D) (Slots × List (Body D) × List (RowSlot D × RowAct)) :=
  (runMeasured bytesOf digestOf rc look rv pkg state method args r budget).map fun x => (x.1, x.2.1, x.2.2.1)

/-- The `declare` acts of the relations of an object of package `pkg` born at `self`, in
relation order: each key's width at the World's digest width (`self`'s). -/
def relsOf (look : Pinned D) (pkg : D) (self : D) : Except (Refusal D) (List RowAct) := do
  let p ← readPackage look pkg
  pure (p.rels.map fun r => .declare r.2.limit r.2.cap (r.2.width (bytesOf self).size) r.2.retract)

/-! ## The resident readers: TEXT at a package's types (what `nd create --pkg` and `nd invoke` sign)

A reader refusal is `program` with its `name @offset` text (law 7's convention for `program`
reasons: the first token is the name). -/

def readAt (T : Ty) (text : String) : Except (Refusal D) Data :=
  match Read.readData T text with
  | .ok d => if digestsOk digestOf d.digests then .ok d else .error (.program "notDigest")
  | .error e => .error (.program e.text)

/-- A seed state read at package `pkg`'s state type, as the object's state slots. -/
def seedOf (look : Pinned D) (pkg : D) (text : String) : Except (Refusal D) Slots := do
  let p ← readPackage look pkg
  match ← readAt digestOf p.state text with
  | .record ds =>
    match stateSlots (recordRow p.state) ds 0 with
    | some s => pure s
    | none => throw (.program "seed: no bytes at the state type")
  | _ => throw (.program "seed: not a record")

/-- Method `method`'s arguments read at its argument type, as the bytes the run decodes. -/
def argsOf (look : Pinned D) (pkg : D) (method : Nat) (text : String) : Except (Refusal D) ByteArray := do
  let p ← readPackage look pkg
  let (_, sg) ← resolveMethod p method
  match Wire.encodeData sg.arg (← readAt digestOf sg.arg text) with
  | some b => pure b
  | none => throw (.program "arguments: no bytes at the argument type")

end

/-- The language, as the kernel's receivers see it. -/
def program (bytesOf : D → ByteArray) (digestOf : ByteArray → Option D) (rc : ReceiptCheck) : Program D where
  checkInstall := checkInstall digestOf
  judge := judgeContextual bytesOf digestOf
  -- the slots, the calls the method makes as the object, and the ticks it used (LEDGER-8 (e))
  run := fun look rv pkg state method args r budget =>
    (runMeasuredLive bytesOf digestOf rc look rv pkg state method args r budget).map fun x =>
      (x.1, x.2.1, x.2.2.1, x.2.2.2.1)
  rels := relsOf bytesOf

end Nanodregg.Lang
