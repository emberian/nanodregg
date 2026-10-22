/- Named refusal probes for the live signature and invocation preparation. -/
import Lang.Journey.Contextual

namespace Nanodregg.Lang.Journey.Contextual
open Nanodregg.Kernel Nanodregg.Kernel.Receive

def minimalPackage : Package where
  imports := []
  methods := []
  laws := []
  state := .record []
  iface := .record [("value", .nat)]
  body := .record [("value", .hole 0 [.bool true, .nat 7])]
  holes := [{ declaration with selectionRel := 5, selectionKey := key }]

def named {α : Type} (r : Except String α) (why : String) : Bool :=
  match r with | .error e => e == why | .ok _ => false

/-- The refusal is exactly this constructor (LANG-74.9: preparation refusals are values, not strings). -/
def refusedAs {ε α : Type} [DecidableEq ε] (r : Except ε α) (why : ε) : Bool :=
  match r with | .error e => decide (e = why) | .ok _ => false

def gateRows : List (String × Bool) := Id.run do
  let p := minimalPackage
  let h := p.holes[0]!
  let good := view (some 0) (some 1)
  let withDecl (d : HoleROM) := { p with holes := [d] }
  let badTy := Ty.record [("z", .nat), ("a", .nat)]
  let plain := { p with body := .record [("value", .nat 7)] }
  let wrongData : RowView Sim.D := {
    points := fun self rel => if rel = 5 then
      [(key, some (.row 0 ((Wire.encodeData .bool (.bool true)).getD .empty) 1))]
      else good.points self rel
    ranges := good.ranges }
  let longGuard : Term := (List.range 80).foldl
    (fun t _ => .app (.lam .bool (.var 0)) t) (.bool true)
  let duplicate : Term := .prim .add (.var 0) (.var 0)
  let nested := (List.range 6).foldl (fun t _ => Term.hole 0 [t]) (.nat 1)
  let badPrint := withDecl { h with ctx := [badTy, .nat] }
  let printMismatch := match Print.packageText badPrint with
    | some text => named (Print.contextualText badPrint text) "contextualPrintMismatch" &&
      (Print.package badPrint).isNone
    | none => false
  let fill := fun _ => some (Term.var 0)
  -- LANG-74.9 plant: a hole name whose refusal text is wider than `Bounds.reasonMax` makes the blocked
  -- hole's `.refuse` ill-typed, so the closed re-check in instantiateHoles refuses (`.instanceRecheck`).
  let wide : Nat := 10 ^ 300
  let wideBody : Term := .record [("value", .hole wide [.bool true, .nat 7])]
  let wideP : Package := { p with holes := [{ h with name := wide }], body := wideBody }
  let termHole := Term.hole 7 [.nat 9]
  let armHole := Term.hole 7 [.prim .add (.var 0) (.nat 9)]
  let sig : HoleSignature := [⟨7, [.nat], .nat⟩]
  let closed := { plain with holes := [] }
  return [
    ("successor-fill-term", decide (Term.fillRefs fill termHole = .nat 9)),
    ("successor-fill-fields", decide (Term.fillRefsRow fill [("v", termHole)] = [("v", .nat 9)])),
    ("successor-fill-arms", decide (Term.fillRefsRow fill [("v", armHole)] = [("v", .prim .add (.var 0) (.nat 9))])),
    ("successor-declared-term", Term.usesRef 7 termHole && (inferE [] [] termHole (Ω := sig)).isOk && !(inferE [] [] termHole (Ω := [])).isOk),
    ("successor-declared-fields", Term.usesRefRow 7 [("v", termHole)] && (inferFields [] [] [("v", termHole)] (Ω := sig)).isOk &&
      !(inferFields [] [] [("v", termHole)] (Ω := [])).isOk),
    ("successor-declared-arms", Term.usesRefRow 7 [("v", armHole)] && (inferArms [] [] [("v", armHole)] [("v", .nat)] (Ω := sig)).isOk &&
      !(inferArms [] [] [("v", armHole)] [("v", .nat)] (Ω := [])).isOk),
    ("reader-import-contract", decide (Term.fillRefs (fun _ => some (.nat 0)) (.ref 0) = .ref 0) &&
      (inferE [.nat] [] (.ref 0) (Ω := [])).isOk && !(inferE [] [] (.ref 0) (Ω := [])).isOk &&
      !Term.usesRef 0 (.ref 0)),
    -- The preparation is never called: a closed package does not prepare.
    ("closed-admission-identity", (admitContextual (fun _ => some (3 : Sim.D))
      (fun _ _ => .error .provenance) .empty closed ⟨[], [], []⟩ []).isOk),

    ("minimal-contextual-check", p.checkContextual [] |>.isOk),
    ("closed-signature-refusal", match plain.checkWith [] with
      | .error .contextualSignature => true | _ => false),
    ("closed-import-type-refusal", match ({ plain with holes := [] }).checkWith [badTy] with
      | .error .importType => true | _ => false),
    ("signature-context-type", refusedAs ((withDecl { h with ctx := [badTy, .nat] }).checkContextual []) (.type 0)),
    ("signature-hypothesis-length", refusedAs ((withDecl { h with hypotheses := [] }).checkContextual []) (.context 0)),
    ("signature-candidate-bound", refusedAs ((withDecl { h with code := List.replicate 65 ⟨.var 1, []⟩ }).checkContextual [])
      (.candidates 0)),
    ("signature-guard-type", refusedAs ((withDecl { h with guard := .nat 0 }).checkContextual []) (.guardType 0)),
    ("candidate-result-type", refusedAs ((withDecl { h with code := [⟨.bool false, []⟩] }).checkContextual [])
      (.candidateType 0 0)),
    ("candidate-context-scope", refusedAs ((withDecl { h with code := [⟨.var 9, []⟩] }).checkContextual [])
      (.candidateType 0 0)),
    ("signature-bound", refusedAs (({ p with holes := List.replicate 17 h }).checkContextual []) .signatureBound),
    ("signature-name-unique", refusedAs (({ p with holes := [h, h] }).checkContextual []) .duplicate),
    ("hole-substitution-type", match ({ p with body := .record [("value", .hole 0 [.nat 3, .nat 7])] }).checkContextual [] with
      | .error (.bodyType _) => true | _ => false),
    ("hole-substitution-length", match ({ p with body := .record [("value", .hole 0 [.bool true])] }).checkContextual [] with
      | .error (.bodyType _) => true | _ => false),
    ("selection-data-type", refusedAs (selectHole wrongData (3 : Sim.D) h) (.selectionType 0)),
    ("selection-code-index", refusedAs (selectHole (view (some 99) (some 1)) (3 : Sim.D) h) (.selectionIndex 0)),
    ("selection-support-version", refusedAs (selectHole (view (some 0) (some 1) (left := some 2)) (3 : Sim.D) h)
      (.derivationMoved 0)),
    ("guard-budget", refusedAs (selectHole good (3 : Sim.D) { h with guard := longGuard }) (.guardFault 0)),
    ("expansion-work-bound", refusedAs (Term.fillBounded 1 1 (fun _ => none) (.nat 1)) .work),
    ("expansion-size-bound", refusedAs (Term.fillBounded 64 3 (fun _ => some duplicate) nested) .size),
    ("recheck-arm-reachable", refusedAs (instantiateHoles (view none (some 1)) (3 : Sim.D) [] wideP) .instanceRecheck &&
      (instantiateHoles (view none (some 1)) (3 : Sim.D) [] p).isOk),
    ("contextual-print-mismatch", printMismatch),
    ("contextual-print-unreadable", named (Print.contextualText p "(") "contextualPrintRead"),
    ("rom-candidate-literals", match checkROMLits (fun _ => (none : Option Sim.D))
      (withDecl { h with ty := .digest, code := [⟨.digest "bad".toUTF8, []⟩] }) with
      | .error (.program "notDigest") => true | _ => false),
    ("rom-guard-literals", match checkROMLits (fun _ => (none : Option Sim.D))
      (withDecl { h with guard := .prim .deq (.digest "bad".toUTF8) (.digest "bad".toUTF8) }) with
      | .error (.program "notDigest") => true | _ => false),
    ("admission-prepared-type", match admitContextual (fun _ => some (3 : Sim.D))
      (fun _ _ => .ok (.record [("value", .bool true)])) .empty p ⟨[], [], []⟩ [] with
      | .error (.program why) => why.startsWith "holeInstanceType" | _ => false)]
end Nanodregg.Lang.Journey.Contextual
