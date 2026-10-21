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
  let termHole := Term.hole 7 [.nat 9]
  let armHole := Term.hole 7 [.prim .add (.var 0) (.nat 9)]
  let sig : HoleSignature := [⟨7, [.nat], .nat⟩]
  let closed := { plain with holes := [] }
  return [
    ("successor-fill-term", decide (Contextual.Term.fillRefs fill termHole = .nat 9)),
    ("successor-fill-fields", decide (Contextual.Term.fillRefsRow fill [("v", termHole)] = [("v", .nat 9)])),
    ("successor-fill-arms", decide (Contextual.Term.fillRefsRow fill [("v", armHole)] = [("v", .prim .add (.var 0) (.nat 9))])),
    ("successor-declared-term", Contextual.Term.usesRef 7 termHole && (inferE [] [] termHole sig).isOk && !(inferE [] [] termHole).isOk),
    ("successor-declared-fields", Contextual.Term.usesRefRow 7 [("v", termHole)] && (inferFields [] [] [("v", termHole)] sig).isOk &&
      !(inferFields [] [] [("v", termHole)]).isOk),
    ("successor-declared-arms", Contextual.Term.usesRefRow 7 [("v", armHole)] && (inferArms [] [] [("v", armHole)] [("v", .nat)] sig).isOk &&
      !(inferArms [] [] [("v", armHole)] [("v", .nat)]).isOk),
    ("reader-import-contract", decide (Contextual.Term.fillRefs (fun _ => some (.nat 0)) (.ref 0) = .ref 0) &&
      (inferE [.nat] [] (.ref 0)).isOk && !(inferE [] [] (.ref 0)).isOk &&
      !Contextual.Term.usesRef 0 (.ref 0)),
    ("closed-admission-identity", (admitContextual (fun _ => some (3 : Sim.D))
      (fun _ _ => .error "must-not-prepare-closed") .empty closed ⟨[], [], []⟩ []).isOk),

    ("minimal-contextual-check", p.checkContextual [] |>.isOk),
    ("closed-signature-refusal", match plain.checkWith [] with
      | .error .contextualSignature => true | _ => false),
    ("closed-import-type-refusal", match ({ plain with holes := [] }).checkWith [badTy] with
      | .error .importType => true | _ => false),
    ("signature-context-type", named ((withDecl { h with ctx := [badTy, .nat] }).checkContextual []) "holeType 0"),
    ("signature-hypothesis-length", named ((withDecl { h with hypotheses := [] }).checkContextual []) "holeContext 0"),
    ("signature-candidate-bound", named ((withDecl { h with code := List.replicate 65 ⟨.var 1, []⟩ }).checkContextual [])
      "holeCandidates 0"),
    ("signature-guard-type", named ((withDecl { h with guard := .nat 0 }).checkContextual []) "holeGuardType 0"),
    ("candidate-result-type", named ((withDecl { h with code := [⟨.bool false, []⟩] }).checkContextual [])
      "holeCandidateType 0 0"),
    ("candidate-context-scope", named ((withDecl { h with code := [⟨.var 9, []⟩] }).checkContextual [])
      "holeCandidateType 0 0"),
    ("signature-bound", named (({ p with holes := List.replicate 17 h }).checkContextual []) "holeSignatureBound"),
    ("signature-name-unique", named (({ p with holes := [h, h] }).checkContextual []) "holeDuplicate"),
    ("hole-substitution-type", match ({ p with body := .record [("value", .hole 0 [.nat 3, .nat 7])] }).checkContextual [] with
      | .error why => why.startsWith "holeBodyType" | _ => false),
    ("hole-substitution-length", match ({ p with body := .record [("value", .hole 0 [.bool true])] }).checkContextual [] with
      | .error why => why.startsWith "holeBodyType" | _ => false),
    ("selection-data-type", named (selectHole wrongData (3 : Sim.D) h) "holeSelectionType 0"),
    ("selection-code-index", named (selectHole (view (some 99) (some 1)) (3 : Sim.D) h) "holeSelectionIndex 0"),
    ("selection-support-version", named (selectHole (view (some 0) (some 1) (left := some 2)) (3 : Sim.D) h)
      "holeDerivationMoved 0"),
    ("guard-budget", named (selectHole good (3 : Sim.D) { h with guard := longGuard }) "holeGuardFault 0"),
    ("expansion-work-bound", named (Contextual.Term.fillBounded 1 1 (fun _ => none) (.nat 1)) "holeWorkBound"),
    ("expansion-size-bound", named (Contextual.Term.fillBounded 64 3 (fun _ => some duplicate) nested) "holeSizeBound"),
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
