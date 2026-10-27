/- Live contextual preparation: ROM code, authenticated rows, one evaluator. -/
import Lang.Package
import Lang.HoleBudget
import Lang.Eval
import Lang.Wire.Data
import Kernel.Receive.Call
import Lang.Rel
import Lang.Print

namespace Nanodregg.Lang
open Nanodregg.Kernel Nanodregg.Kernel.Receive

/-- Why live contextual preparation refuses: one constructor per refusal (law 7). `wire` is the one printer;
its text is what the kernel's `Refusal.program` and a blocked hole's `.refuse` carry.

A refusal about a justification NAMES THE JUSTIFICATION (DESIGN-CTX §2.3, the why-not half of CONTEXTUAL
INTEGRITY): the row the caller did not pin (`unpinnedRow`: its relation and key), every cell support the caller
did not pin (`unpinned`), every support whose row moved or whose cell is not live (`derivationMoved`,
`supportDead`), the hypothesis position AND its pin (`supportMoved`). The lists are never empty when thrown
(each is the filter of a failed `all`); a client re-plans from them without guessing. -/
inductive HoleRefusal where
  | type (hole : Nat)
  | context (hole : Nat)
  | candidates (hole : Nat)
  | guardType (hole : Nat)
  | candidateType (hole code : Nat)
  | package (e : CheckError)
  | signatureBound
  | duplicate
  | bodyType (e : TypeErr)
  /-- a row of the hole object the caller did not pin: the selection row, a row support of a hypothesis, the
  guard pin's row (absent and unpinned differ: `holeRow`) -/
  | unpinnedRow (rel : Nat) (key : ByteArray)
  /-- the cell supports of the selected candidate (or the one cell pin of a hypothesis or the guard) the caller
  did not pin -/
  | unpinned (pins : List SupportPin)
  /-- a hypothesis the selected code USES whose pin does not hold: the position and the pin -/
  | supportMoved (hole position : Nat) (pin : SupportPin)
  | guardBlocked (hole : Nat)
  | guardFault (hole : Nat)
  | selectionAbsent (hole : Nat)
  | selectionType (hole : Nat)
  | selectionIndex (hole : Nat)
  /-- the selected candidate's row supports that are not at their ROM version -/
  | derivationMoved (hole : Nat) (pins : List SupportPin)
  /-- the selected candidate's cell supports that are not live in the caller's pinned view (E1) -/
  | supportDead (hole : Nat) (pins : List SupportPin)
  | expansion (b : ExpansionBound)
  | provenance
  | instanceRecheck
  | instanceType (e : TypeErr)
  deriving DecidableEq

/-- Signature validation checks every candidate at exactly its declared context,
including candidates not currently selected. A candidate cannot introduce another hole. -/
def HoleROM.check (Δ : List Ty) (h : HoleROM) : Except HoleRefusal Unit := do
  unless h.ctx.all Ty.wf && h.ty.wf do throw (.type h.name)
  unless h.hypotheses.length = h.ctx.length do throw (.context h.name)
  unless h.code.length ≤ Bounds.holeCandidatesMax do throw (.candidates h.name)
  match inferE [] [.bool] h.guard (Ω := []) with
  | .ok .bool => pure ()
  | _ => throw (.guardType h.name)
  for (c, i) in h.code.zipIdx do
    match inferE Δ h.ctx c.body (Ω := []) with
    | .ok T => unless T = h.ty do throw (.candidateType h.name i)
    | .error _ => throw (.candidateType h.name i)

def Package.checkContextual (Δ : List Ty) (p : Package) : Except HoleRefusal Unit := do
  match p.checkShape with | .error e => throw (.package e) | .ok () => pure ()
  match p.checkFields with | .error e => throw (.package e) | .ok () => pure ()
  unless p.holes.length ≤ Bounds.holeSignatureMax do throw .signatureBound
  unless (p.holes.map (·.name)).eraseDups.length = p.holes.length do throw .duplicate
  for h in p.holes do h.check Δ
  match checkE Δ p.body p.iface (Ω := holeSignature p.holes) with
  | .error e => throw (.bodyType e)
  | .ok () => pure ()

/-- The row must occur in the authenticated point view; absent and unpinned differ.
No ambient store is read by this module. -/
def holeRow {D : Type} (rv : RowView D) (self : D) (rel : Nat) (key : ByteArray) :
    Except HoleRefusal (Option RowLeaf) :=
  match (rv.points self rel).find? (fun p => decide (p.1 = key)) with
  | none => .error (.unpinnedRow rel key)
  | some (_, leaf) => .ok leaf

/-- The cell `g` is live in the caller's pinned view AND `law` is among its laws in force: the law
slots an object cell holds at `lawBase ≤ k < stateBase` (`Kernel.Receive.lawSlotsOf`'s range), each
the digest bytes of a law package (DESIGN-CTX §2.5a). A tombstone, an absence and an unpinned cell
are `false`, as `cellLive`. -/
def cellGoverned {D : Type} (look : Pinned D) (g : D) (law : ByteArray) : Bool :=
  match look g with
  | .ok (some c) => c.slots.any fun p => decide (lawBase ≤ p.1 ∧ p.1 < stateBase) && p.2 == law
  | _ => false

/-- The cell `g` is live AND runs package `pkg`: its `slotPackage` holds `pkg`'s digest bytes. -/
def cellRuns {D : Type} (look : Pinned D) (g : D) (pkg : ByteArray) : Bool :=
  match look g with
  | .ok (some c) => c.slots.get slotPackage == some pkg
  | _ => false

/-- Whether a ROM pin holds: a row support at exactly its version; a cell support live; a contract
support live and governed by its law / running its package. -/
def supportLive {D : Type} (digestOf : ByteArray → Option D) (look : Pinned D) (rv : RowView D)
    (self : D) : SupportPin → Bool
  | .row rel key ver =>
    match holeRow rv self rel key with
    | .ok (some (.row _ _ v)) => v == ver
    | _ => false
  | .cell id => (digestOf id).any (cellLive look)
  | .cellLaw id law => (digestOf id).any fun g => cellGoverned look g law
  | .cellPackage id pkg => (digestOf id).any fun g => cellRuns look g pkg

/-- The cell id a pin names, if it names one (every arm but a row's). -/
def SupportPin.cellOf : SupportPin → Option ByteArray
  | .row .. => none
  | .cell id | .cellLaw id _ | .cellPackage id _ => some id

/-- Whether a ROM pin's cell was observed: a cell support must be pinned (a pinned tombstone is
observed, an unpinned cell is not); a row support is checked by `holeRow`. -/
def supportObserved {D : Type} (digestOf : ByteArray → Option D) (look : Pinned D) (p : SupportPin) : Bool :=
  match p.cellOf with
  | none => true
  | some id =>
    match digestOf id with
    | some g => match look g with | .ok _ => true | .error _ => false
    | none => false

/-- A row pin holds; a cell pin is not judged here (`supportLive` on its own arm). -/
def rowSupportHolds {D : Type} (digestOf : ByteArray → Option D) (look : Pinned D) (rv : RowView D)
    (self : D) (p : SupportPin) : Bool :=
  match p with
  | .row .. => supportLive digestOf look rv self p
  | _ => true

/-- The caller observed the pin: its row under `self` (absent and unpinned differ) or its cell. -/
def supportPinned {D : Type} (digestOf : ByteArray → Option D) (look : Pinned D) (rv : RowView D)
    (self : D) (p : SupportPin) : Except HoleRefusal Unit :=
  match p with
  | .row rel key _ => (holeRow rv self rel key).map fun _ => ()
  | _ => if supportObserved digestOf look p then .ok () else .error (.unpinned [p])

/-- Bytes as lowercase hex, two digits a byte: the text of a key or a cell id inside a refusal. Two pushes a
byte, no list (law 4). -/
def hexOf (b : ByteArray) : String :=
  b.foldl (fun s x => (s.push (Print.hexDigit (x >>> 4).toNat)).push (Print.hexDigit (x &&& 15).toNat)) ""

/-- A pin's coordinates in a refusal: `row:REL:KEYHEX:VER` or `cell:IDHEX`. A client that is refused re-reads
exactly this (DESIGN-CTX §2.3: a refusal is the negative literal of the assumption that failed, with its
coordinate). -/
def SupportPin.wire : SupportPin → String
  | .row rel key ver => s!"row:{rel}:{hexOf key}:{ver}"
  | .cell id => s!"cell:{hexOf id}"
  | .cellLaw id law => s!"cellLaw:{hexOf id}:{hexOf law}"
  | .cellPackage id pkg => s!"cellPackage:{hexOf id}:{hexOf pkg}"

/-- The pins of one refusal, space-separated. -/
def pinsWire (ps : List SupportPin) : String := " ".intercalate (ps.map SupportPin.wire)

def HoleRefusal.wire : HoleRefusal → String
  | .type n => s!"holeType {n}"
  | .context n => s!"holeContext {n}"
  | .candidates n => s!"holeCandidates {n}"
  | .guardType n => s!"holeGuardType {n}"
  | .candidateType n i => s!"holeCandidateType {n} {i}"
  | .package e => e.wire
  | .signatureBound => "holeSignatureBound"
  | .duplicate => "holeDuplicate"
  | .bodyType e => s!"holeBodyType {e.text}"
  | .unpinnedRow rel key => s!"holeUnpinnedRow {rel} {hexOf key}"
  | .unpinned ps => s!"holeUnpinned {pinsWire ps}"
  | .supportMoved n i p => s!"holeSupportMoved {n} {i} {p.wire}"
  | .guardBlocked n => s!"holeGuardBlocked {n}"
  | .guardFault n => s!"holeGuardFault {n}"
  | .selectionAbsent n => s!"holeSelectionAbsent {n}"
  | .selectionType n => s!"holeSelectionType {n}"
  | .selectionIndex n => s!"holeSelectionIndex {n}"
  | .derivationMoved n ps => s!"holeDerivationMoved {n} {pinsWire ps}"
  | .supportDead n ps => s!"holeSupportDead {n} {pinsWire ps}"
  | .expansion .work => "holeWorkBound"
  | .expansion .size => "holeSizeBound"
  | .provenance => "holeProvenance"
  | .instanceRecheck => "holeInstanceType"
  | .instanceType e => s!"holeInstanceType {e.text}"

/-- A successful invocation receipt retains the selected code index, exact
selection version, and the hypothesis positions removed by strengthening.

Its provenance is one positive product (C4(a), LANG-75.4): the selected code's `supports` and the pins of the
hypotheses its body uses, every one live at the caller's view (`selectHole_origin` for the supports; a used
hypothesis whose pin does not hold refuses `supportMoved`). A ROM candidate has no blocker and no environment
literal: the guard and the cost belong to the hole. Nothing reads a receipt beyond the instantiated body
(`Lang.Program` keeps `instantiateHoles`'s `body`; the kernel record does not hold a selection), so the product is
not stored here; a field for it lands with its first reader. -/
structure HoleSelection where
  name : Nat
  index : Nat
  version : Nat
  body : Term
  strengthened : List Nat
  guardTicks : Nat
  context : List Ty
  filling : Term
  embedding : List Nat
  original : Term
  deriving Inhabited

/-- One hypothesis position `pi = (pin, x)` of `changedHypotheses`: a structural assumption (`none`) is skipped;
a pin must be observed (`unpinned`); a live pin keeps `x`; a dead pin used by the code refuses `supportMoved`; a dead
unused pin strengthens `x` away. Named so the theorems over `selectHole` (`selectHole_hypotheses`) read this step
itself (C5, LANG-75.5). -/
def hypothesisStep {D : Type} (digestOf : ByteArray → Option D) (look : Pinned D)
    (rv : RowView D) (self : D) (h : HoleROM) (c : HoleCode) (removed : List Nat)
    (pi : Option SupportPin × Nat) : Except HoleRefusal (List Nat) :=
  match pi.1 with
  | none => .ok removed
  | some pin => do
    supportPinned digestOf look rv self pin
    if supportLive digestOf look rv self pin then .ok removed
    else if Term.usesVar pi.2 c.body then .error (.supportMoved h.name pi.2 pin)
    else .ok (removed ++ [pi.2])

/-- Positions whose support moved. Only genuinely unused variables may be
strengthened away; a moved support actually used by the candidate is refused. -/
def changedHypotheses {D : Type} (digestOf : ByteArray → Option D) (look : Pinned D)
    (rv : RowView D) (self : D) (h : HoleROM) (c : HoleCode) :
    Except HoleRefusal (List Nat) :=
  h.hypotheses.zipIdx.foldlM (hypothesisStep digestOf look rv self h c) []

/-- Evaluate the signature guard on the current authenticated guard pin. -/
def runHoleGuard {D : Type} (digestOf : ByteArray → Option D) (look : Pinned D) (rv : RowView D)
    (self : D) (h : HoleROM) : Except HoleRefusal Nat := do
  if let some p := h.guardPin then
    supportPinned digestOf look rv self p
  let present := h.guardPin.all (supportLive digestOf look rv self)
  match run [] Bounds.stackMax Bounds.holeGuardFuel 0 (State.init h.guard [.bool present]) with
  | .value (.bool true) used => .ok used
  | .value (.bool false) _ => .error (.guardBlocked h.name)
  | _ => .error (.guardFault h.name)

/-- Remove unused positions from right to left so every index still names its
original assumption. The embedding records where each retained variable came
from; fillRefs receives that re-embedded factor, not unchecked row syntax. The context, the term and the embedding
move in one fold: the embedding is the context's own position list under the same erasures (C5, LANG-75.6). -/
def factorHole (h : HoleROM) (c : HoleCode) (removed : List Nat) :
    List Ty × Term × List Nat :=
  removed.reverse.foldl (fun (a : List Ty × Term × List Nat) x =>
    (a.1.eraseIdx x, Term.renameVar (lowerIdx x) a.2.1, a.2.2.eraseIdx x))
    (h.ctx, c.body, List.range h.ctx.length)

/-- The body a selection runs: the factor's filling with every retained variable sent back to the position it came
from. Named so `selectHole_factor` reads this step itself (C5, LANG-75.6). -/
def reembed (embedding : List Nat) (filling : Term) : Term :=
  Term.renameVar (fun n => embedding.getD n n) filling

/-- Selection is fresh on each invocation. Its bytes contain a code index,
never a filling supplied by the caller. All derivation supports and used
contextual assumptions must still have the ROM-pinned versions; every cell support must be pinned
(`unpinned`) and live (`supportDead`). Each refusal carries EVERY support that failed its check (the filter of
the failed `all`), so the caller learns its whole missing read set in one refusal (DESIGN-CTX §2.3).

Each invocation judges only the index its selection row names. The hole's LIVE LABEL, the indices that would select
at this view, is not computed: nothing reads it (no resident's tick reads a ROM hole's candidates). The row
machine's live label is `Std.holeVerdictLabel`, read by `Std.holeDecision_verified_iff`; a ROM label lands with its
first reader (C3, LANG-75.4). -/
def selectHole {D : Type} (digestOf : ByteArray → Option D) (look : Pinned D) (rv : RowView D)
    (self : D) (h : HoleROM) : Except HoleRefusal HoleSelection := do
  let leaf ← holeRow rv self h.selectionRel h.selectionKey
  let some (.row _ bytes version) := leaf | throw (.selectionAbsent h.name)
  let .ok (.nat i) := Wire.decodeData .nat bytes | throw (.selectionType h.name)
  let some c := h.code[i]? | throw (.selectionIndex h.name)
  unless c.supports.all (supportObserved digestOf look) do
    throw (.unpinned (c.supports.filter fun p => !supportObserved digestOf look p))
  unless c.supports.all (rowSupportHolds digestOf look rv self) do
    throw (.derivationMoved h.name (c.supports.filter fun p => !rowSupportHolds digestOf look rv self p))
  unless c.supports.all (supportLive digestOf look rv self) do
    throw (.supportDead h.name (c.supports.filter fun p => !supportLive digestOf look rv self p))
  let removed ← changedHypotheses digestOf look rv self h c
  let used ← runHoleGuard digestOf look rv self h
  let (ctx, filling, embedding) := factorHole h c removed
  let body := reembed embedding filling
  pure ⟨h.name, i, version, body, removed, used, ctx, filling, embedding, c.body⟩

/-- A blocked hole is not a candidate receipt. Its original named refusal
is retained in typed code and fires only when the machine demands that hole. -/
inductive HoleResolution where
  | selected (receipt : HoleSelection)
  | blocked (name : Nat) (ty : Ty) (reason : HoleRefusal)

def HoleResolution.name : HoleResolution → Nat
  | .selected s => s.name
  | .blocked n _ _ => n

def HoleResolution.body : HoleResolution → Term
  | .selected s => s.body
  | .blocked _ T why => .refuse T why.wire.toUTF8

def HoleResolution.receipt : HoleResolution → Option HoleSelection
  | .selected s => some s
  | .blocked _ _ _ => none

def resolveHole {D : Type} (digestOf : ByteArray → Option D) (look : Pinned D) (rv : RowView D)
    (self : D) (h : HoleROM) : HoleResolution :=
  match selectHole digestOf look rv self h with
  | .ok s => .selected s
  | .error why => .blocked h.name h.ty why

def resolutionEnv (rs : List HoleResolution) (n : Nat) : Option Term :=
  (rs.find? (fun r => r.name == n)).map HoleResolution.body

def resolutionMax (rs : List HoleResolution) : Nat :=
  rs.foldl (fun n r => max n (Term.nodes r.body)) 1

/-- THE preparation charge of a contextual package, at the largest candidate size `m` it may expand: the
expansion bound of `Term.fillBounded` plus one guard allowance (`Bounds.holeGuardFuel`) per declared hole;
the same formula at two different `m`s, not the same number. The invocation's
actual cost is this at the resolved candidates (`instantiateHoles`); the static charge is this at the largest
committed candidate (`Package.preparationCost`).

With `holeSignature`, this is the hole boundary (C6, LANG-75.8): typing and cost, never behaviour. No
consumer reads a projection of a selected filling; the abstract `consumer_boundary` left with LANG-75.3
for that reason. -/
def Package.holeCharge (p : Package) (m : Nat) : Nat :=
  if p.holes.isEmpty then 0
  else Term.nodes p.body * (m + 1) + Bounds.holeGuardFuel * p.holes.length

/-- Actual syntax cost and guard steps are charged before evaluation. This is
preparation for one invocation, never an installed replacement package. -/
structure HoleInstance where
  body : Term
  selections : List HoleSelection
  resolutions : List HoleResolution
  cost : Nat

def instantiateHoles {D : Type} (digestOf : ByteArray → Option D) (look : Pinned D)
    (rv : RowView D) (self : D) (Δ : List Ty) (p : Package) :
    Except HoleRefusal HoleInstance := do
  p.checkContextual Δ
  let rs := p.holes.map (resolveHole digestOf look rv self)
  let ss := rs.filterMap HoleResolution.receipt
  let body ← match Term.fillBounded Wire.nodeMax (resolutionMax rs) (resolutionEnv rs) p.body with
    | .error b => throw (.expansion b)
    | .ok t => pure t
  unless body.digestLits.all (fun b => (p.body.digestLits ++
      ss.flatMap (fun s => s.original.digestLits)).any (fun a => decide (a = b))) do throw .provenance
  -- The closed checker is the invocation boundary too; proof connects this
  -- check to contextual substitution, rather than trusting a receipt.
  match checkE Δ body p.iface (Ω := []) with
  | .error _ => throw .instanceRecheck
  | .ok () => pure ⟨body, ss, rs, p.holeCharge (resolutionMax rs)⟩

end Nanodregg.Lang
