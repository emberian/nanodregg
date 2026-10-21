/- The fixed guarded-activity generator extended with live contextual code.
Management remains ordinary checked helper code; only execute demands the hole. -/
import Lang.StdHole
import Lang.LiveHoles
import Lang.Rel

namespace Nanodregg.Lang.Std
open HoleSyntax

def codeSelection : RelDecl :=
  ⟨[("hole", .nat)], .nat, 16, none, 0, true, some "codeChosen"⟩

def codeOutput (V : Ty) : RelDecl :=
  ⟨[("hole", .nat)], V, 16, none, 0, true, none⟩

/-- Guard every selection row write, including writes returned by a different
method: only the chooser before acceptance/deadline can choose an existing code. -/
def codeChosen (name count : Nat) : Term :=
  let authority (rest : H) :=
    hguard (hp .deq (hg (hv "req") "agent") (hg (hv "state") "chooser")) "notChooser"
      (hguard (ht (hg (hv "state") "accepted") (hb false) (hb true)) "accepted"
        (hguard (hp .le (hg (hv "req") "validUntil") (hg (hv "state") "closes")) "closed" rest))
  let choice : H :=
    hguard (hp .eq (hg (hg (hv "x") "key") "hole") (hc (.nat name))) "unknownHole"
      (hguard (hp .lt (hg (hv "x") "val") (hc (.nat count))) "unknownCandidate" (hc okT))
  (hl "state" holeState (hl "req" reqTy (hl "input" (guardInTy codeSelection)
    (authority (hf (hg (hv "input") "edit")
      [("insert", "x", choice), ("retract", "x", hc (refusedT "selected")),
       ("upsert", "x", choice)]))))) []

/-- Extend the fixed bundle. σ is explicit syntax in execute's environment
[request, argument, state, reads]; checkContextual checks it against the ROM context.
The returned signature uses the generated relation index and canonical key bytes.
Hypothesis/support pins in declaration remain the caller's explicit ROM commitments. -/
def contextualHole (A : Ty) (declaration : HoleROM) (σ : List Term) (clause : Term)
    (reads : List (Label × RelRead) := []) :
    Except String HoleBundle := do
  let bundle ← match hole declaration.ty clause
      [("computed", codeOutput declaration.ty), ("selection", { codeSelection with guard := none })] with
    | .ok b => pure b
    | .error e => throw e.name
  let p := bundle.layout
  -- Attach the guard together with its field; the intermediate helper bundle
  -- has no selection method or codeChosen field. The final package is checked below.
  let rels := p.rels.map fun (n, d) =>
    (n, if n = "selection" then codeSelection else d)
  let some key := keyBytes codeSelection (.record [("hole", .nat declaration.name)]) |
    throw "holeSelectionKey"
  let h := { declaration with
    selectionRel := (rels.map (·.1)).idxOf "selection", selectionKey := key }
  let Reads := readsTy rels reads
  let R := resultTy holeState [] (editTy rels) 1
  let Arg := Ty.record [("hole", .nat), ("index", .nat)]
  let choice := activityEdit rels "selection" codeSelection "upsert"
    (.record [("hole", .get (.var 1) "hole")]) (.get (.var 1) "index")
  let choose : Term := .lam (.record []) (.lam holeState (.lam Arg (.lam reqTy
    (activityResult rels (.var 2) [choice]))))
  let output := activityEdit rels "computed" (codeOutput declaration.ty) "upsert"
    (.record [("hole", .nat h.name)]) (.hole h.name σ)
  let execute : Term := .lam Reads (.lam holeState (.lam A (.lam reqTy
    (.ite (activityApply clause [.var 2, .hole h.name σ])
      (activityResult rels (.var 2) [output]) (.refuse R "conflict".toUTF8)))))
  let .record ts := p.iface | throw "holeRootType"
  let .record fs := p.body | throw "holeRootBody"
  let additions : List (Label × Ty × Term) := [
    ("choose_code", methodTy holeState Arg [] (.record []) (editTy rels) 1, choose),
    ("codeChosen", guardTy holeState codeSelection, codeChosen h.name h.code.length),
    ("execute", .fn Reads (.fn holeState (.fn A (.fn reqTy R))), execute)]
  let p := { p with
    iface := .record (Row.sort (ts ++ additions.map fun (n, t, _) => (n, t))),
    body := .record (Row.sort (fs ++ additions.map fun (n, _, t) => (n, t))),
    rels, holes := [h], methods := (p.methods ++ ["choose_code", "execute"]).mergeSort }
  p.checkContextual (bundle.libraries.map (·.iface))
  pure { bundle with layout := p }

/-- Link live ROM to its ordinary checked helpers. No filling is staged here. -/
def HoleBundle.linkContextual (b : HoleBundle) (ids : List ByteArray) : Except String Package := do
  unless ids.length = b.libraries.length do throw "holeImports"
  let p := { b.layout with imports := ids }
  p.checkContextual (b.libraries.map (·.iface))
  let some bytes := Wire.encodePackage p | throw "holeRootTooLarge"
  unless bytes.size ≤ Bounds.bytesMax do throw "holeRootTooLarge"
  pure p

end Nanodregg.Lang.Std
