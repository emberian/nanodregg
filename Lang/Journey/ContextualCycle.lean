/- Grounded cyclic rules compiled into a deployed contextual filling. -/
import Lang.Journey.ContextualReceive

namespace Nanodregg.Lang.Journey
open Nanodregg.Kernel Nanodregg.Kernel.Receive

def cycleTy : Ty := .record [("p", .bool), ("q", .bool), ("r", .bool)]

/-- Synchronous least-fixpoint unrolling of p ← a, p ← q, q ← p;
r ← u is independent. Three rounds suffice for this three-node graph. -/
def cyclePQ : Nat → Term × Term
  | 0 => (.bool false, .bool false)
  | n + 1 => let (p, q) := cyclePQ n; (.ite (.var 0) (.bool true) q, p)

def cycleTerm : Term :=
  let (p, q) := cyclePQ 3
  .record [("p", p), ("q", q), ("r", .var 1)]

/-- Read a declared immutable fact token through the fixed generator's complete
observation adapter. Missing coverage refuses; pinned absence is false. A fact names a kernel cell
that must be LIVE (E1): the cycle's two groundings are the two members' cells. -/
def observedFact (n : Sim.D) : Term :=
  let support := Term.record [("cell", .digest (Sim.dc.bytes n)),
    ("pin", .digest (Sim.dc.bytes 0))]
  .ite (Std.activityApply Std.holeSupportCovered [support, .var 3])
    (.prim .eq (Std.activityApply Std.holeSupportProbe [support, .var 3]) (.nat 1))
    (.refuse .bool "holeUnpinned".toUTF8)

def cycleBundle (c1 c5 : Sim.D) : Except String Std.HoleBundle :=
  Std.contextualHole (.record [])
    { name := 0, ctx := [.bool, .bool], ty := cycleTy,
      code := [⟨cycleTerm, []⟩], selectionRel := 0, selectionKey := .empty,
      hypotheses := [none, none], guardPin := none, guard := .var 0 }
    [observedFact c1, observedFact c5] (.lam Std.holeState (.lam cycleTy (.bool true)))
    [("facts", ⟨3, none, true, false⟩)]

def cycleRows (r0 : Run) (a b : Sim.Member) : Run := Id.run do
  let mut r := r0
  let prog := langProgram
  -- the groundings "1" and "5" are the members' cells a and b
  let cellOf (n : Nat) : Sim.D := if n = 1 then a.id else b.id
  let bundle ← match cycleBundle a.id b.id with
    | .ok b => pure b | .error why => return note r s!"LP E4 generate: {why}" false
  let mut ids : List D := []
  for lib in bundle.libraries do
    let some bytes := Wire.encodePackage lib | return note r "LP E4 helper wire" false
    let (rr, v, t) := go prog r (Sim.signed r.st a a.key
      (Sim.S.pinsFor r.st.host [a.id]) (.install bytes))
    r := note rr s!"LP E4 helper {bytes.size}: {v}" (v == "admitted")
    let some id := t.bind fun t => (createdIds t).head? | return r
    ids := ids ++ [id]
  let p ← match bundle.linkContextual (ids.map Sim.dc.bytes) with
    | .ok p => pure p | .error why => return note r s!"LP E4 link: {why}" false
  let some bytes := Wire.encodePackage p | return note r "LP E4 package wire" false
  let (rr, v, t) := go prog r (Sim.signed r.st a a.key
    (Sim.S.pinsFor r.st.host (a.id :: ids)) (.install bytes))
  r := note rr s!"LP E4 cyclic-rule contextual ROM {bytes.size}: {v}" (v == "admitted")
  let some pkg := t.bind fun t => (createdIds t).head? | return r
  let some seed := stateSlots (recordRow p.state)
    [("accepted", .bool false), ("acceptor", .digest (Sim.dc.bytes b.id)), ("cap", .nat 10),
     ("chooser", .digest (Sim.dc.bytes a.id)), ("closes", .nat 100000),
     ("selected", .inj "none" (.record []))] 0 | return note r "LP E4 seed" false
  let (rr, v, t) := go prog r (Sim.signed r.st a a.key
    (Sim.S.pinsFor r.st.host ([a.id, pkg] ++ ids)) (.create (some pkg) [] seed))
  r := note rr s!"LP E4 create: {v}" (v == "admitted")
  let some obj := t.bind fun t => (createdIds t).head? | return r
  let factKey (n : Nat) := Data.record [("cell", .digest (Sim.dc.bytes (cellOf n)))]
  let key := Data.record [("hole", .nat 0)]
  let pins (r : Run) (omitted : Option Nat := none) :=
    ([1, 5].filter (fun n => omitted != some n)).flatMap
      (fun n => hole_pinAt obj r.st.host 2 Std.holeFacts (factKey n)) ++
    hole_pinAt obj r.st.host 5 Std.codeSelection key ++
    hole_pinAt obj r.st.host 1 (Std.codeOutput cycleTy) key
  let call (r : Run) (m : Label) (args : ByteArray) (omitted : Option Nat := none) :=
    signedAt r.st a (Sim.S.pinsFor r.st.host ([a.id, b.id, obj, pkg] ++ ids))
      (.invoke obj (p.methods.idxOf m) args 100000 none)
      r.st.host.height (r.st.host.height + 1024) (pins r omitted)
  let exec (r : Run) := call r "execute" (argBytes (.record []) (.record []))
  let out (r : Run) := match storyRow r.st.host obj 1 (Std.codeOutput cycleTy) key with
    | some (.record [("p", .bool p), ("q", .bool q), ("r", .bool u)]) => some (p, q, u)
    | _ => none
  for n in [1, 5] do
    let (rr, v, _) := go prog r (call r "post"
      (hole_postArg (Sim.dc.bytes (cellOf n)) (Sim.dc.bytes 0)) (some n))
    r := note rr s!"LP E4 ground fact{n}: {v}" (v == "admitted")
  let (rr, v, _) := go prog r (call r "choose_code"
    (argBytes (.record [("hole", .nat), ("index", .nat)])
      (.record [("hole", .nat 0), ("index", .nat 0)])))
  r := note rr s!"LP E4 select rule program: {v}" (v == "admitted")
  let (rr, v, _) := go prog r (exec r)
  r := note rr s!"LP E4 grounded cycle p/q and independent r: {v}"
    (v == "admitted" && out rr == some (true, true, true))
  let (rr, v, _) := go prog r (call r "unpost"
    (argBytes (.record [("cell", .digest)]) (factKey 1)))
  r := note rr s!"LP E4 withdraw grounding a: {v}" (v == "admitted")
  let (rr, v, _) := go prog r (exec r)
  r := note rr s!"LP E4 unfounded p/q both false, independent r remains true: {v}"
    (v == "admitted" && out rr == some (false, false, true))
  let (_, v, _) := go prog r (call r "execute" (argBytes (.record []) (.record [])) (some 1))
  r := note r s!"LP E4 omitted grounding observation: {v}"
    (refusedBy v "execute" "holeUnpinned")
  return r

def cycleSession : Run :=
  let X := ctxWith langProgram
  let fk := [("lc-a".toUTF8, "lc-a-next".toUTF8), ("lc-b".toUTF8, "lc-b-next".toUTF8)]
  match genesis X Sim.worldName (Sim.nonceOf 6) 100000000
      (fk.map fun (k, n) => (k, nextKeyDigest X n)) Authority.none with
  | .error e => note { st := { rng := ⟨1⟩, host := World.genesis X.env 0 0, members := [] } }
      s!"LP E4 genesis: {e.name}" false
  | .ok g =>
    let ms := fk.zipIdx.map fun ((k, n), i) => (⟨founderId X g.origin i, k, n⟩ : Sim.Member)
    cycleRows { st := { rng := ⟨1⟩, host := g, members := ms } }
      (ms.headD ⟨0, .empty, .empty⟩) (ms.getD 1 ⟨0, .empty, .empty⟩)

initialize register { name := "contextual-cycle", run := pure cycleSession, contextual := true }

end Nanodregg.Lang.Journey
