/- Deployed contextual repair through signed Receive.submit and World.admit. -/
import Lang.Journey
import Lang.Journey.Contextual

namespace Nanodregg.Lang.Journey
open Nanodregg.Kernel Nanodregg.Kernel.Receive

def liveDeclaration : HoleROM :=
  let pin (n : Nat) : SupportPin := .row 2 (Contextual.factKeyAt n) 0
  { Contextual.declaration with
    code := [⟨.var 1, [pin 2]⟩, ⟨.var 1, [pin 3]⟩, ⟨.nat 9, []⟩,
      ⟨.prim .add (.nat 2) (.nat 5), []⟩,
      ⟨(List.range 8).foldl (fun t _ => .app (.lam .nat (.var 0)) t) (.nat 7), []⟩,
      ⟨.nat 2, []⟩]
    hypotheses := [some (pin 1), some (pin 4)]
    guardPin := some (pin 5) }

/-- A plain package (no holes) whose one import is `imp` (A10's layer): `set n` writes its state. -/
def layerState : Ty := .record [("n", .nat)]

def layerOver (imp : ByteArray) : Package :=
  { imports := [imp], state := layerState, iface := .record [("set", methodTy layerState .nat)],
    body := .record [("set", Std.methodOf layerState .nat [("n", .var 1)])], methods := ["set"], laws := [] }

def contextualRows (r0 : Run) (a b : Sim.Member) : Run := Id.run do
  let prog := langProgram
  let X := ctxWith prog
  let mut r := r0
  for (n, ok) in Contextual.boundaryRows do
    r := note r s!"LP boundary {n}" ok
  let bundle ← match Std.contextualHole .nat liveDeclaration [.bool true, .var 1] Contextual.clause with
    | .ok b => pure b
    | .error e => return note r s!"LP generate: {e}" false
  let mut ids : List D := []
  for lib in bundle.libraries do
    let some bytes := Wire.encodePackage lib | return note r "LP helper wire" false
    let (rr, verdict, turn) := go prog r (Sim.signed r.st a a.key
      (Sim.S.pinsFor r.st.host [a.id]) (.install bytes))
    r := note rr s!"LP install helper {bytes.size}: {verdict}" (verdict == "admitted")
    let some id := turn.bind fun t => (createdIds t).head? | return r
    ids := ids ++ [id]
  let p ← match bundle.linkContextual (ids.map Sim.dc.bytes) with
    | .ok p => pure p
    | .error e => return note r s!"LP link: {e}" false
  let some text := Print.package p | return note r "LP print" false
  let .ok back := Surface.readPackage text | return note r "LP read" false
  r := note r "LP live signature survives resident text" (decide (back = p))
  let some bytes := Wire.encodePackage p | return note r "LP wire" false
  let (rr, verdict, turn) := go prog r (Sim.signed r.st a a.key
    (Sim.S.pinsFor r.st.host (a.id :: ids)) (.install bytes))
  r := note rr s!"LP install contextual ROM {bytes.size}: {verdict}" (verdict == "admitted")
  let some pkg := turn.bind fun t => (createdIds t).head? | return r
  let some seed := stateSlots (recordRow p.state)
    [("accepted", .bool false), ("acceptor", .digest (Sim.dc.bytes b.id)), ("cap", .nat 10),
     ("chooser", .digest (Sim.dc.bytes a.id)), ("closes", .nat 100000),
     ("selected", .inj "none" (.record []))] 0 | return note r "LP seed" false
  let (rr, verdict, turn) := go prog r (Sim.signed r.st a a.key
    (Sim.S.pinsFor r.st.host ([a.id, pkg] ++ ids)) (.create (some pkg) [] seed))
  r := note rr s!"LP create without a selection: {verdict}" (verdict == "admitted")
  let some obj := turn.bind fun t => (createdIds t).head? | return r
  let factData (n : Nat) := Data.record [("cell", .digest (Sim.dc.bytes (UInt64.ofNat n)))]
  let choiceKey := Data.record [("hole", .nat 0)]
  let pinsAt (target : D) (r : Run) (omitBlocker : Bool := false) (omitFact : Option Nat := none) :=
    (([1, 2, 3, 4] ++ if omitBlocker then [] else [5]).filter
      (fun n => omitFact != some n)).flatMap
      (fun n => hole_pinAt target r.st.host 2 Std.holeFacts (factData n)) ++
    hole_pinAt target r.st.host 5 Std.codeSelection choiceKey ++
    hole_pinAt target r.st.host 1 (Std.codeOutput .nat) choiceKey
  let call (r : Run) (method : Label) (args : ByteArray) (omitBlocker : Bool := false) (omitFact : Option Nat := none) (budget : Nat := 100000) :=
    signedAt r.st a (Sim.S.pinsFor r.st.host ([a.id, obj, pkg] ++ ids))
      (.invoke obj (p.methods.idxOf method) args budget none)
      r.st.host.height (r.st.host.height + 1024) (pinsAt obj r omitBlocker omitFact)
  let exec (r : Run) := call r "execute" (argBytes .nat (.nat 7))
  let choose (r : Run) (i : Nat) := call r "choose_code"
    (argBytes (.record [("hole", .nat), ("index", .nat)])
      (.record [("hole", .nat 0), ("index", .nat i)]))
  let withdraw (r : Run) (n : Nat) := call r "unpost"
    (argBytes (.record [("cell", .digest)]) (factData n))
  let value (r : Run) := match storyRow r.st.host obj 1 (Std.codeOutput .nat) choiceKey with
    | some (.nat n) => some n | _ => none
  let receipt (r : Run) := selectHole Sim.digestOf (pinned X.env r.st.host (exec r).unsigned.pins)
    (rowView X.env r.st.host (exec r).unsigned) obj p.holes[0]!
  let (_, v0, _) := go prog r (exec r)
  r := note r s!"LP suspended before selection: {v0}" (refusedBy v0 "execute" "holeSelectionAbsent 0")
  for n in [1, 2, 3, 4] do
    let (rr, v, _) := go prog r (call r "post"
      (hole_postArg (Sim.dc.bytes (UInt64.ofNat n)) (Sim.dc.bytes pkg)) (omitFact := some n))
    r := note rr s!"LP management post fact{n}: {v}" (v == "admitted")
  let (rr, vc, _) := go prog r (choose r 0)
  r := note rr s!"LP bootstrap chooser selection: {vc}" (vc == "admitted")
  let before := r
  let (rr, v, _) := go prog r (exec r)
  r := note rr s!"LP kept, context argument7: {v}; {measure before.st.host (exec before)}"
    (v == "admitted" && value rr == some 7 &&
      match receipt before with | .ok s => s.strengthened.isEmpty | _ => false)
  -- E3: the live guard blocks a previously usable branch, then its withdrawal reopens it.
  let (rr, v, _) := go prog r (call r "post"
    (hole_postArg (Sim.dc.bytes 5) (Sim.dc.bytes pkg)) (omitFact := some 5))
  r := note rr s!"LP E3 post exclusion token: {v}" (v == "admitted")
  let (_, v, _) := go prog r (exec r)
  r := note r s!"LP E3 excluded branch: {v}" (refusedBy v "execute" "holeGuardBlocked 0")
  let (rr, v, _) := go prog r (withdraw r 5)
  r := note rr s!"LP E3 withdraw exclusion: {v}" (v == "admitted")
  let (rr, v, _) := go prog r (exec r)
  r := note rr s!"LP E3 branch reopens without reproposal: {v}"
    (v == "admitted" && value rr == some 7)
  -- E6: a different syntax has the same exported value and satisfies the same clause.
  let (rr, v, _) := go prog r (choose r 3)
  r := note rr s!"LP E6 choose 2+5: {v}" (v == "admitted")
  let before := r
  let (rr, v, _) := go prog r (exec r)
  r := note rr s!"LP E6 same value, different syntax: {v}"
    (v == "admitted" && value rr == some 7 &&
      match receipt before with | .ok s => decide (s.body ≠ .var 1) | _ => false)
  -- E8: retained earlier code can be reselected without rewriting the ROM.
  let (rr, v, _) := go prog r (choose r 0)
  r := note rr s!"LP E8 reapply retained contextual filling: {v}" (v == "admitted")
  let fast := match measure r.st.host (exec r) with | .ok (_, t) => t | _ => 0
  let (rr, v, _) := go prog r (exec r)
  r := note rr s!"LP E8 earlier filling still yields7: {v}" (v == "admitted" && value rr == some 7)
  -- E7: equal values do not imply preservation of a cost guarantee.
  let (rr, v, _) := go prog r (choose r 4)
  r := note rr s!"LP E7 choose slower equal-value code: {v}" (v == "admitted")
  let (_, v, _) := go prog r (call r "execute" (argBytes .nat (.nat 7)) (budget := fast))
  r := note r s!"LP E7 prior tick bound {fast} lost: {v}"
    (v.startsWith "refused program" && (v.splitOn "execute: exhausted").length > 1)
  let (rr, v, _) := go prog r (exec r)
  r := note rr s!"LP E7 value remains7 with adequate budget: {v}" (v == "admitted" && value rr == some 7)
  let (rr, v, _) := go prog r (choose r 0)
  r := note rr s!"LP restore first route: {v}" (v == "admitted")
  let (rr, v, _) := go prog r (withdraw r 1)
  r := note rr s!"LP withdraw unused bool hypothesis: {v}" (v == "admitted")
  let before := r
  let (rr, v, _) := go prog r (exec r)
  r := note rr s!"LP strengthened over deployed ROM: {v}"
    (v == "admitted" && value rr == some 7 &&
      match receipt before with
      | .ok s => decide (s.context = [.nat] ∧ s.filling = .var 0 ∧ s.body = .var 1)
      | _ => false)
  let (rr, v, _) := go prog r (withdraw r 2)
  r := note rr s!"LP withdraw first derivation: {v}" (v == "admitted")
  let (_, v, _) := go prog r (exec r)
  -- the refusal names the moved support (its relation, key and ROM version), through the real receivers
  r := note r s!"LP stale derivation blocked: {v}"
    (refusedBy v "execute" s!"holeDerivationMoved 0 {(SupportPin.row 2 (Contextual.factKeyAt 2) 0).wire}")
  let (rr, v, _) := go prog r (choose r 1)
  r := note rr s!"LP management selects surviving derivation: {v}" (v == "admitted")
  let (rr, v, _) := go prog r (exec r)
  r := note rr s!"LP alternative preserves filling7: {v}" (v == "admitted" && value rr == some 7)
  let (lost, v, _) := go prog r (withdraw r 3)
  let (_, blocked, _) := go prog lost (exec lost)
  r := note r s!"LP E2 last derivation withdrawn ({v}): {blocked}"
    (v == "admitted" && refusedBy blocked "execute" "holeDerivationMoved 0")
  let (reissued, v, _) := go prog r (call r "post"
    (hole_postArg (Sim.dc.bytes 2) (Sim.dc.bytes pkg)) (omitFact := some 2))
  let (reselected, vc, _) := go prog reissued (choose reissued 0)
  let (_, old, _) := go prog reselected (exec reselected)
  r := note r s!"LP E8 reissued fact cannot reactivate old pin ({v}, {vc}): {old}"
    (v == "admitted" && vc == "admitted" && refusedBy old "execute" "holeDerivationMoved 0")
  let (_, v, _) := go prog r (call r "execute" (argBytes .nat (.nat 7)) true)
  r := note r s!"LP omitted blocker pin: {v}"
    (refusedBy v "execute" s!"holeUnpinnedRow 2 {hexOf (Contextual.factKeyAt 5)}")
  -- the selected candidate cites fact3; the caller that does not pin it is told the new name, not
  -- the moved one (the rows it named moved only when it pinned them)
  let (_, v, _) := go prog r (call r "execute" (argBytes .nat (.nat 7)) false (omitFact := some 3))
  r := note r s!"LP omitted derivation pin: {v}"
    (refusedBy v "execute" s!"holeSupportUnpinned 0 {(SupportPin.row 2 (Contextual.factKeyAt 3) 0).wire}")
  let (rr, v, _) := go prog r (withdraw r 4)
  r := note rr s!"LP withdraw used nat hypothesis: {v}" (v == "admitted")
  let (_, v, _) := go prog r (exec r)
  r := note r s!"LP suspension preserves used hypothesis refusal: {v}"
    (refusedBy v "execute" s!"holeSupportMoved 0 1 {(SupportPin.row 2 (Contextual.factKeyAt 4) 0).wire}")
  let (rr, v, _) := go prog r (choose r 2)
  r := note rr s!"LP chooser offers replacement while old code blocked: {v}" (v == "admitted")
  let (rr, v, _) := go prog r (exec r)
  r := note rr s!"LP replacement yields9: {v}" (v == "admitted" && value rr == some 9)
  -- E5: cap is deliberately frozen within an object. A new invocation context
  -- is a second instance of the SAME ROM at cap5, not an illicit state edit.
  let some lowSeed := stateSlots (recordRow p.state)
    [("accepted", .bool false), ("acceptor", .digest (Sim.dc.bytes b.id)), ("cap", .nat 5),
     ("chooser", .digest (Sim.dc.bytes a.id)), ("closes", .nat 100000),
     ("selected", .inj "none" (.record []))] 0 | return note r "LP E5 seed" false
  let (rr, v, turn) := go prog r (Sim.signed r.st a a.key
    (Sim.S.pinsFor r.st.host ([a.id, pkg] ++ ids)) (.create (some pkg) [] lowSeed))
  r := note rr s!"LP E5 same ROM under cap5 context: {v}" (v == "admitted")
  let some low := turn.bind fun t => (createdIds t).head? | return r
  let lowCall (r : Run) (m : Label) (args : ByteArray) :=
    signedAt r.st a (Sim.S.pinsFor r.st.host ([a.id, low, pkg] ++ ids))
      (.invoke low (p.methods.idxOf m) args 100000 none)
      r.st.host.height (r.st.host.height + 1024) (pinsAt low r)
  let lowChoose (r : Run) (i : Nat) := lowCall r "choose_code"
    (argBytes (.record [("hole", .nat), ("index", .nat)])
      (.record [("hole", .nat 0), ("index", .nat i)]))
  let (rr, v, _) := go prog r (lowChoose r 3)
  r := note rr s!"LP E5 retain prior candidate7: {v}" (v == "admitted")
  let (_, v, _) := go prog r (lowCall r "execute" (argBytes .nat (.nat 7)))
  r := note r s!"LP E5 candidate7 conflicts with changed contract: {v}"
    (refusedBy v "execute" "conflict")
  let (rr, v, _) := go prog r (lowChoose r 5)
  r := note rr s!"LP E5 chooser selects retained replacement2: {v}" (v == "admitted")
  let (rr, v, _) := go prog r (lowCall r "execute" (argBytes .nat (.nat 7)))
  let out := match storyRow rr.st.host low 1 (Std.codeOutput .nat) choiceKey with
    | some (.nat n) => some n | _ => none
  r := note rr s!"LP E5 replacement satisfies new contract: {v}"
    (v == "admitted" && out == some 2)
  -- A10 (LANG-78): a plain package layered over the installed contextual ROM. Install admits its
  -- import at the import's own holes, as the run's load does, so it installs, and its method runs
  -- over a closure that holds the holed ROM.
  let some layerBytes := Wire.encodePackage (layerOver (Sim.dc.bytes pkg)) | return note r "LP A10 wire" false
  let (rr, v, turn) := go prog r (Sim.signed r.st a a.key
    (Sim.S.pinsFor r.st.host ([a.id, pkg] ++ ids)) (.install layerBytes))
  r := note rr s!"LP A10 a plain package importing the contextual ROM installs: {v}" (v == "admitted")
  let some layer := turn.bind fun t => (createdIds t).head? | return r
  let some layerSeed := stateSlots (recordRow layerState) [("n", .nat 0)] 0 | return note r "LP A10 seed" false
  let (rr, v, turn) := go prog r (Sim.signed r.st a a.key
    (Sim.S.pinsFor r.st.host ([a.id, layer, pkg] ++ ids)) (.create (some layer) [] layerSeed))
  r := note rr s!"LP A10 create the layer: {v}" (v == "admitted")
  let some lobj := turn.bind fun t => (createdIds t).head? | return r
  let (rr, v, _) := go prog r (signedAt r.st a (Sim.S.pinsFor r.st.host ([a.id, lobj, layer, pkg] ++ ids))
    (.invoke lobj 0 (argBytes .nat (.nat 7)) 100000 none) r.st.host.height (r.st.host.height + 1024))
  r := note rr s!"LP A10 the layer's method runs over the holed import: {v}"
    (v == "admitted" && natSlotOf X.env rr.st.host lobj 0 == some 7)
  return r

def contextualSession : Run :=
  let X := ctxWith langProgram
  let fk := [("lp-a".toUTF8, "lp-a-next".toUTF8), ("lp-b".toUTF8, "lp-b-next".toUTF8)]
  match genesis X Sim.worldName (Sim.nonceOf 7) 100000000
      (fk.map fun (k, n) => (k, nextKeyDigest X n)) Authority.none with
  | .error e => note { st := { rng := ⟨1⟩, host := World.genesis X.env 0 0, members := [] } }
      s!"LP genesis: {e.name}" false
  | .ok g =>
    let ms := fk.zipIdx.map fun ((k, n), i) => (⟨founderId X g.origin i, k, n⟩ : Sim.Member)
    contextualRows { st := { rng := ⟨1⟩, host := g, members := ms } }
      (ms.headD ⟨0, .empty, .empty⟩) (ms.getD 1 ⟨0, .empty, .empty⟩)

initialize register { name := "contextual", run := pure contextualSession, contextual := true }

end Nanodregg.Lang.Journey
