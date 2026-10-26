/- Contextual ROM fixtures shared by the real receive journey and its proof teeth. -/
import Lang.StdContextualHole
import Lang.Print
import Lang.Program
import Kernel.Sim

namespace Nanodregg.Lang.Journey.Contextual
open Nanodregg.Kernel Nanodregg.Kernel.Receive

def factKeyAt (n : Nat) : ByteArray :=
  (Wire.encodeData (keyTy Std.holeFacts)
    (.record [("cell", .digest (Sim.dc.bytes (UInt64.ofNat n)))])).getD .empty

def factPinAt (n : Nat) : SupportPin := .row 2 (factKeyAt n) 1

/-- A contextual filling that uses its nat assumption and can lose its unused bool. -/
def declaration : HoleROM where
  name := 0
  ctx := [.bool, .nat]
  ty := .nat
  code := [⟨.var 1, [factPinAt 2]⟩, ⟨.var 1, [factPinAt 3]⟩, ⟨.nat 9, []⟩]
  selectionRel := 0
  selectionKey := .empty
  -- Generated relation order: candidates, computed, facts, fills, pending, selection.
  hypotheses := [some (factPinAt 1), some (factPinAt 4)]
  guardPin := some (factPinAt 5)
  guard := .ite (.var 0) (.bool false) (.bool true)

def clause : Term :=
  .lam Std.holeState (.lam .nat (.prim .le (.var 0) (.get (.var 1) "cap")))

def bundle : Except String Std.HoleBundle :=
  Std.contextualHole .nat declaration [.bool true, .var 1] clause

def libraryIds (b : Std.HoleBundle) : List Sim.D :=
  (List.range b.libraries.length).map fun n => UInt64.ofNat (n + 10)

def linked (b : Std.HoleBundle) : Except String Package :=
  b.linkContextual ((libraryIds b).map Sim.dc.bytes)

def packageCell (p : Package) : Option Cell :=
  (Wire.encodePackage p).map fun bytes => ⟨kindPackage, .rom, [(0, bytes)]⟩

/-- The method boundary fixture has actual canonical ROM bytes and separately
pinned helper cells; the signed receive journey uses the same generated bundle. -/
def look (b : Std.HoleBundle) (p : Package) : Pinned Sim.D := fun id =>
  if id = 99 then .ok (packageCell p)
  else match ((libraryIds b).zip b.libraries).find? (fun q => q.1 == id) with
    | some (_, lib) => .ok (packageCell lib)
    | none => .error (.unpinned id)

/-- A view that pins no kernel cell: for ROMs whose pins are all rows. -/
def noCells : Pinned Sim.D := fun g => .error (.unpinned g)

def key : ByteArray :=
  (keyBytes Std.codeSelection (.record [("hole", .nat 0)])).getD .empty

def factKey : ByteArray := factKeyAt 1

/-- Every dependency includes an explicit absence; an omitted pin is not absence. -/
def view (selected : Option Nat) (hypVersion : Option Nat)
    (coverHyp : Bool := true) (left : Option Nat := some 1) (right : Option Nat := some 1)
    (used : Option Nat := some 1) (blocker : Option Nat := none)
    (coverBlocker : Bool := true) : RowView Sim.D where
  points _ rel :=
    if rel = 5 then [(key, selected.map fun n => .row 0
      ((Wire.encodeData .nat (.nat n)).getD .empty) 1)]
    else if rel = 2 then
      ((if coverHyp then [(factKeyAt 1, hypVersion)] else []) ++
        [(factKeyAt 2, left), (factKeyAt 3, right), (factKeyAt 4, used)] ++
        (if coverBlocker then [(factKeyAt 5, blocker)] else [])).map
          (fun (k, v) => (k, v.map fun n => .row 0 .empty n))
    else if rel = 1 then [(key, none)]
    else []
  ranges _ _ := .ok []

def request (agent : Sim.D := 1) : Req Sim.D :=
  ⟨agent, agent, 3, 0, 10, .invoke 0⟩

def seed (accepted : Bool := false) : Slots :=
  (stateSlots (recordRow Std.holeState)
    [("accepted", .bool accepted), ("acceptor", .digest (Sim.dc.bytes 2)),
      ("cap", .nat 10), ("chooser", .digest (Sim.dc.bytes 1)), ("closes", .nat 1000),
      ("selected", .inj "none" (.record []))] 0).getD []

def invoke (b : Std.HoleBundle) (p : Package) (rv : RowView Sim.D) (method : Label)
    (args : Data) (A : Ty) (agent : Sim.D := 1) (accepted : Bool := false) (budget : Nat := 100000) (validUntil : Nat := 10) :
    Except (Refusal Sim.D) (Slots × List (Body Sim.D) × List (RowSlot Sim.D × RowAct) × Nat) :=
  (program Sim.dc.bytes Sim.digestOf noReceipts).run (look b p) rv 99 (seed accepted)
    (p.methods.idxOf method) ((Wire.encodeData A args).getD .empty) { request agent with validUntil := validUntil } budget

def resultName {α : Type} : Except (Refusal Sim.D) α → String
  | .ok _ => "ok"
  | .error (.program why) => why
  | .error e => e.name

def outputNat : Except (Refusal Sim.D)
    (Slots × List (Body Sim.D) × List (RowSlot Sim.D × RowAct) × Nat) → Option Nat
  | .ok (_, _, [(_, .upsert _ bytes)], _) =>
      match Wire.decodeData .nat bytes with | .ok (.nat n) => some n | _ => none
  | _ => none

/-- Positive and negative boundary probes, also called by the signed journey.
These are not a replacement for submit/World.admit rows. -/
def boundaryRows : List (String × Bool) := Id.run do
  let .ok b := bundle | return [("generate", false)]
  let .ok p := linked b | return [("link", false)]
  let some h := p.holes.head? | return [("signature", false)]
  let good := view (some 0) (some 1)
  let withdrawn := view (some 0) none
  let blocked := view none none
  let L := look b p
  let selected := selectHole Sim.digestOf L good (3 : Sim.D) h
  let strengthened := selectHole Sim.digestOf L withdrawn (3 : Sim.D) h
  -- E1 at ROM grain: a candidate whose support is a kernel CELL selects only while that cell is
  -- pinned and live (99 is the pinned package cell; 77 is pinned at its tombstone; 78 is unpinned)
  let tomb : Pinned Sim.D := fun id => if id = 77 then .ok none else L id
  let cellCode (id : Sim.D) : HoleROM :=
    { h with code := [⟨.var 1, [factPinAt 2, .cell (Sim.dc.bytes id)]⟩] }
  let contractCode (pin : SupportPin) : HoleROM := { h with code := [⟨.var 1, [factPinAt 2, pin]⟩] }
  let (lawA, lawB, pkgX) := (Sim.dc.bytes 91, Sim.dc.bytes 92, Sim.dc.bytes 93)
  -- an object cell: package `pkgX` at `slotPackage`, owner at `slotOwner`, one law `lawA` at `lawBase`
  let governed : Pinned Sim.D := fun id =>
    if id = 76 then .ok (some ⟨kindObject, .ram, [(slotPackage, pkgX), (slotOwner, Sim.dc.bytes 1), (lawBase, lawA)]⟩)
    else tomb id
  let chosen : Ty := .record [("hole", .nat), ("index", .nat)]
  let choice := Data.record [("hole", .nat 0), ("index", .nat 0)]
  let extraKey := (keyBytes Std.codeSelection (.record [("hole", .nat 1)])).getD .empty
  let extraView : RowView Sim.D := {
    points := fun self rel => good.points self rel ++ if rel = 5 then [(extraKey, none)] else []
    ranges := good.ranges }
  let printed := match Print.package p with
    | none => false
    | some t => match Read.readPackage t with
      | .ok q => decide (p = q)
      | .error _ => false
  let wrong := { p with holes := [{ h with code := [⟨.var 0, []⟩] }] }
  return [
    ("generated-print-read", printed),
    ("context-used", (invoke b p good "execute" (.nat 7) .nat |> outputNat) == some 7),
    ("strengthened-value", (invoke b p withdrawn "execute" (.nat 7) .nat |> outputNat) == some 7),
    ("strengthened-context", match strengthened with
      | .ok s => decide (s.context = [.nat] ∧ s.filling = .var 0 ∧ s.body = .var 1)
      | _ => false),
    ("kept-context", match selected with | .ok s => s.strengthened.isEmpty | _ => false),
    ("blocked-name", (invoke b p blocked "execute" (.nat 7) .nat |> resultName) ==
      "execute: refused holeSelectionAbsent 0"),
    ("blocked-not-selected", (resolveHole Sim.digestOf L blocked (3 : Sim.D) h).receipt.isNone),
    ("cell-support-live", (selectHole Sim.digestOf tomb good (3 : Sim.D) (cellCode 99)).isOk),
    ("cell-support-dead", match selectHole Sim.digestOf tomb good (3 : Sim.D) (cellCode 77) with
      | .error why => decide (why = .supportDead 0 [.cell (Sim.dc.bytes 77)]) | .ok _ => false),
    ("cell-support-unpinned", match selectHole Sim.digestOf tomb good (3 : Sim.D) (cellCode 78) with
      | .error why => decide (why = .unpinned [.cell (Sim.dc.bytes 78)]) | .ok _ => false),
    -- contract pins (S2, LANG-84): 76 is an object cell governed by law `lawA` and running package `pkgX`
    ("cell-law-governed", (selectHole Sim.digestOf governed good (3 : Sim.D) (contractCode (.cellLaw (Sim.dc.bytes 76) lawA))).isOk),
    ("cell-law-ungoverned", match selectHole Sim.digestOf governed good (3 : Sim.D) (contractCode (.cellLaw (Sim.dc.bytes 76) lawB)) with
      | .error why => decide (why = .supportDead 0 [.cellLaw (Sim.dc.bytes 76) lawB]) | .ok _ => false),
    ("cell-law-dead", match selectHole Sim.digestOf governed good (3 : Sim.D) (contractCode (.cellLaw (Sim.dc.bytes 77) lawA)) with
      | .error why => decide (why = .supportDead 0 [.cellLaw (Sim.dc.bytes 77) lawA]) | .ok _ => false),
    ("cell-package-runs", (selectHole Sim.digestOf governed good (3 : Sim.D) (contractCode (.cellPackage (Sim.dc.bytes 76) pkgX))).isOk),
    ("cell-package-other", match selectHole Sim.digestOf governed good (3 : Sim.D) (contractCode (.cellPackage (Sim.dc.bytes 76) lawA)) with
      | .error why => decide (why = .supportDead 0 [.cellPackage (Sim.dc.bytes 76) lawA]) | .ok _ => false),
    ("cell-law-unpinned", match selectHole Sim.digestOf governed good (3 : Sim.D) (contractCode (.cellLaw (Sim.dc.bytes 78) lawA)) with
      | .error why => decide (why = .unpinned [.cellLaw (Sim.dc.bytes 78) lawA]) | .ok _ => false),
    ("management-bootstrap", (invoke b p blocked "choose_code" choice chosen).isOk),
    ("management-authority", (invoke b p blocked "choose_code" choice chosen 2 |> resultName) != "ok"),
    ("management-accepted", (invoke b p blocked "choose_code" choice chosen 1 true |> resultName) != "ok"),
    ("management-deadline", (invoke b p blocked "choose_code" choice chosen (validUntil := 1001) |> resultName) != "ok"),
    ("management-hole-name", (invoke b p extraView "choose_code"
      (.record [("hole", .nat 1), ("index", .nat 0)]) chosen |> resultName) != "ok"),
    ("management-candidate-index", (invoke b p blocked "choose_code"
      (.record [("hole", .nat 0), ("index", .nat 99)]) chosen |> resultName) != "ok"),
    -- the refusal names the row the caller did not pin: the hypothesis's fact row (DESIGN-CTX §2.3)
    ("omitted-context-pin", (invoke b p (view (some 0) none false) "execute" (.nat 7) .nat |> resultName) ==
      s!"execute: refused holeUnpinnedRow 2 {hexOf (factKeyAt 1)}"),
    ("wrong-context", (match wrong.checkContextual (b.libraries.map (·.iface)) with
      | .error why => decide (why = .candidateType 0 0) | .ok () => false)),
    ("guard-blocked", (invoke b p (view (some 0) (some 1) (blocker := some 1))
      "execute" (.nat 7) .nat |> resultName) == "execute: refused holeGuardBlocked 0"),
    ("omitted-blocker-pin", (invoke b p (view (some 0) (some 1) (coverBlocker := false))
      "execute" (.nat 7) .nat |> resultName) == s!"execute: refused holeUnpinnedRow 2 {hexOf (factKeyAt 5)}"),
    ("used-hypothesis-withdrawn", (invoke b p (view (some 0) (some 1) (used := none))
      "execute" (.nat 7) .nat |> resultName) == s!"execute: refused holeSupportMoved 0 1 {(factPinAt 4).wire}"),
    ("derivation-withdrawn", (invoke b p (view (some 0) (some 1) (left := none))
      "execute" (.nat 7) .nat |> resultName) == s!"execute: refused holeDerivationMoved 0 {(factPinAt 2).wire}"),
    ("alternative-same-filling", (invoke b p (view (some 1) (some 1) (left := none))
      "execute" (.nat 7) .nat |> outputNat) == some 7),
    ("clause-conflict", (invoke b p good "execute" (.nat 11) .nat |> resultName) ==
      "execute: refused conflict"),
    ("preparation-budget", (invoke b p good "execute" (.nat 7) .nat (budget := 0) |> resultName) ==
      "holeTicks"),
    ("replacement-value", (invoke b p (view (some 2) none) "execute" (.nat 7) .nat |> outputNat) == some 9)]

end Nanodregg.Lang.Journey.Contextual
