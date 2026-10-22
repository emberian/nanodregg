/- Live contextual preparation: ROM code, authenticated rows, one evaluator. -/
import Lang.Package
import Lang.HoleBudget
import Lang.Eval
import Lang.Wire.Data
import Kernel.Receive.Call

namespace Nanodregg.Lang
open Nanodregg.Kernel Nanodregg.Kernel.Receive

/-- Signature validation checks every candidate at exactly its declared context,
including candidates not currently selected. A candidate cannot introduce another hole. -/
def HoleROM.check (Δ : List Ty) (h : HoleROM) : Except String Unit := do
  unless h.ctx.all Ty.wf && h.ty.wf do throw s!"holeType {h.name}"
  unless h.hypotheses.length = h.ctx.length do throw s!"holeContext {h.name}"
  unless h.code.length ≤ 64 do throw s!"holeCandidates {h.name}"
  match inferE [] [.bool] h.guard with
  | .ok .bool => pure ()
  | _ => throw s!"holeGuardType {h.name}"
  for (c, i) in h.code.zipIdx do
    match inferE Δ h.ctx c.body with
    | .ok T => unless T = h.ty do throw s!"holeCandidateType {h.name} {i}"
    | .error _ => throw s!"holeCandidateType {h.name} {i}"

def Package.checkContextual (Δ : List Ty) (p : Package) : Except String Unit := do
  match p.checkShape with | .error e => throw e.wire | .ok () => pure ()
  match p.checkFields with | .error e => throw e.wire | .ok () => pure ()
  unless p.holes.length ≤ 16 do throw "holeSignatureBound"
  unless (p.holes.map (·.name)).eraseDups.length = p.holes.length do throw "holeDuplicate"
  for h in p.holes do h.check Δ
  match checkE Δ p.body p.iface (Ω := holeSignature p.holes) with
  | .error e => throw s!"holeBodyType {e.text}"
  | .ok () => pure ()

/-- The row must occur in the authenticated point view; absent and unpinned differ.
No ambient store is read by this module. -/
def holeRow {D : Type} (rv : RowView D) (self : D) (rel : Nat) (key : ByteArray) :
    Except String (Option RowLeaf) :=
  match (rv.points self rel).find? (fun p => decide (p.1 = key)) with
  | none => .error "holeUnpinned"
  | some (_, leaf) => .ok leaf

def holePinHolds {D : Type} (rv : RowView D) (self : D) (p : HolePin) : Bool :=
  match holeRow rv self p.rel p.key with
  | .ok (some (.row _ _ ver)) => ver == p.ver
  | _ => false

/-- A successful invocation receipt retains the selected code index, exact
selection version, and the hypothesis positions removed by strengthening. -/
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

/-- Positions whose support moved. Only genuinely unused variables may be
strengthened away; a moved support actually used by the candidate is refused. -/
def changedHypotheses {D : Type} (rv : RowView D) (self : D) (h : HoleROM) (c : HoleCode) :
    Except String (List Nat) :=
  h.hypotheses.zipIdx.foldlM (fun removed pi =>
    match pi.1 with
    | none => .ok removed
    | some pin => do
      let _ ← holeRow rv self pin.rel pin.key
      if holePinHolds rv self pin then .ok removed
      else if Term.usesVar pi.2 c.body then .error s!"holeSupportMoved {h.name} {pi.2}"
      else .ok (removed ++ [pi.2])) []

/-- Evaluate the signature guard on the current authenticated guard pin. -/
def runHoleGuard {D : Type} (rv : RowView D) (self : D) (h : HoleROM) : Except String Nat := do
  if let some p := h.guardPin then
    let _ ← holeRow rv self p.rel p.key
    pure ()
  let present := h.guardPin.all (holePinHolds rv self)
  match run [] Bounds.stackMax 256 0 (State.init h.guard [.bool present]) with
  | .value (.bool true) used => .ok used
  | .value (.bool false) _ => .error s!"holeGuardBlocked {h.name}"
  | _ => .error s!"holeGuardFault {h.name}"

/-- Remove unused positions from right to left so every index still names its
original assumption. The embedding records where each retained variable came
from; fillRefs receives that re-embedded factor, not unchecked row syntax. -/
def factorHole (h : HoleROM) (c : HoleCode) (removed : List Nat) :
    List Ty × Term × List Nat :=
  let small := removed.reverse.foldl (fun (a : List Ty × Term) x =>
    (a.1.eraseIdx x, Term.renameVar (lowerIdx x) a.2)) (h.ctx, c.body)
  (small.1, small.2, (List.range h.ctx.length).filter (fun i => !removed.contains i))

/-- Selection is fresh on each invocation. Its bytes contain a code index,
never a filling supplied by the caller. All derivation supports and used
contextual assumptions must still have the ROM-pinned versions. -/
def selectHole {D : Type} (rv : RowView D) (self : D) (h : HoleROM) : Except String HoleSelection := do
  let leaf ← holeRow rv self h.selectionRel h.selectionKey
  let some (.row _ bytes version) := leaf | throw s!"holeSelectionAbsent {h.name}"
  let .ok (.nat i) := Wire.decodeData .nat bytes | throw s!"holeSelectionType {h.name}"
  let some c := h.code[i]? | throw s!"holeSelectionIndex {h.name}"
  unless c.supports.all (holePinHolds rv self) do throw s!"holeDerivationMoved {h.name}"
  let removed ← changedHypotheses rv self h c
  let used ← runHoleGuard rv self h
  let (ctx, filling, embedding) := factorHole h c removed
  let body := Term.renameVar (fun n => embedding.getD n n) filling
  pure ⟨h.name, i, version, body, removed, used, ctx, filling, embedding, c.body⟩

/-- A blocked hole is not a candidate receipt. Its original named refusal
is retained in typed code and fires only when the machine demands that hole. -/
inductive HoleResolution where
  | selected (receipt : HoleSelection)
  | blocked (name : Nat) (ty : Ty) (reason : String)

def HoleResolution.name : HoleResolution → Nat
  | .selected s => s.name
  | .blocked n _ _ => n

def HoleResolution.body : HoleResolution → Term
  | .selected s => s.body
  | .blocked _ T why => .refuse T why.toUTF8

def HoleResolution.receipt : HoleResolution → Option HoleSelection
  | .selected s => some s
  | .blocked _ _ _ => none

def resolveHole {D : Type} (rv : RowView D) (self : D) (h : HoleROM) : HoleResolution :=
  match selectHole rv self h with
  | .ok s => .selected s
  | .error why => .blocked h.name h.ty why

def resolutionEnv (rs : List HoleResolution) (n : Nat) : Option Term :=
  (rs.find? (fun r => r.name == n)).map HoleResolution.body

def resolutionMax (rs : List HoleResolution) : Nat :=
  rs.foldl (fun n r => max n (Term.nodes r.body)) 1

/-- Actual syntax cost and guard steps are charged before evaluation. This is
preparation for one invocation, never an installed replacement package. -/
structure HoleInstance where
  body : Term
  selections : List HoleSelection
  resolutions : List HoleResolution
  cost : Nat

def instantiateHoles {D : Type} (rv : RowView D) (self : D) (Δ : List Ty) (p : Package) :
    Except String HoleInstance := do
  p.checkContextual Δ
  let rs := p.holes.map (resolveHole rv self)
  let ss := rs.filterMap HoleResolution.receipt
  let body ← Term.fillBounded Wire.nodeMax (resolutionMax rs) (resolutionEnv rs) p.body
  unless body.digestLits.all (fun b => (p.body.digestLits ++
      ss.flatMap (fun s => s.original.digestLits)).any (fun a => decide (a = b))) do throw "holeProvenance"
  -- The closed checker is the invocation boundary too; proof connects this
  -- check to contextual substitution, rather than trusting a receipt.
  match checkE Δ body p.iface with
  | .error _ => throw "holeInstanceType"
  | .ok () =>
    pure ⟨body, ss, rs, if p.holes.isEmpty then 0 else
      Term.nodes p.body * (resolutionMax rs + 1) + 256 * rs.length⟩

end Nanodregg.Lang
