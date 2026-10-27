/-
# Lang.Journey.Inbox — the Bell as the agent's inbox: an aimed ring is delivered by its answer
(HOSTING-53; DESIGN-AGENT §4, A1)

A ring captures its text AND an optional AIM: a target object, a method of it, a grant the Bell
OBJECT holds on it (`via`) and a candidate id. The capture is immutable with the ring (the `rung`
guard compares it), so the resident must echo the aim it read; `answer` records the text in `rings`
as before and, for an aimed ring, returns ONE typed nested call to the target in the same Turn
(LANG-77), derived as the Bell object (`Kernel.Receive.Derive`: a nested call's actor is the calling
object), authorised by the grant the target's owner gave the Bell. Answered is delivered: a target
that refuses refuses the answer, and the ring stays pending by name.

The first target is the document's section (`Lang.Journey.Doc`: a `Std.hole` at `bytes`), whose
`propose` the Bell is granted. The candidate the section receives is byte for byte the text
`rings[k]` holds, `by` the resident (the signer; the AUTHORITY is the Bell object's grant), supported by the Bell's grant itself (`cell = pin = via`),
which the editor posted as a fact. Revoke the grant: the next judgment suspends the candidate by
name (`support0 dead`) and a `select` of it is refused — the hole the agent filled is re-judged when
its support is withdrawn — and a further aimed answer is refused by the kernel (`missingCell`: the revoked grant is a
tombstone), the ring left pending. The ringer then withdraws that ring at once (LANG-97, DESIGN-AGENT
§6.4): a ring aimed at a target that refuses does not hold the resident's queue until the patience.

The LI rows run this through `Receive.submit` on the Sim, over the Bell's surface source and the
section generator's packages linked at the Sim's ids.
-/
import Lang.Journey.Doc

namespace Nanodregg.Lang.Journey.Inbox
open Nanodregg.Kernel Nanodregg.Kernel.Receive Nanodregg.Lang.Journey

/-- The aim's `to` datum as the pending row's capture holds it, read back. -/
def capturedTo (row : Option Data) : Option Data :=
  match row.bind (·.field "captured") with
  | some (.inj "ask" value) => value.field "to"
  | _ => none

/-- Two optional data compared by their printed text (`Data` has no `BEq`). -/
def sameData (a b : Option Data) : Bool := (a.bind Print.data) == (b.bind Print.data)

/-- A candidate's `by` and `value`, read back. -/
def candidateOf (w : World D) (obj : D) (dC : RelDecl) (cand : ByteArray) : Option (ByteArray × ByteArray) :=
  match storyRow w obj 0 dC (.record [("cand", .digest cand)]) with
  | some row =>
    match row.field "by", row.field "value" with
    | some (.digest b), some (.bytes v) => some (b, v)
    | _, _ => none
  | none => none

/-- The inbox's life: the Bell and a section; an aimed ring; the answer that drops the aim refused by
the guard; the answer that echoes it delivered as the section's candidate; the grant revoked, the
candidate suspended by name, its selection refused, the next forward refused and the ring pending. -/
def lifeRows (r0 : Run) (a b : Sim.Member) (bell : String) : Run := Id.run do
  let prog := langProgram
  let mut r := r0
  -- LI1 the Bell (A owns it, B is its resident, granted answer and ring)
  let p ← match Surface.readPackage bell with
    | .ok p => pure p
    | .error e => return note r s!"LI1 read the Bell ({bellSourcePath}): {e.text bell}" false
  let some pb := Wire.encodePackage p | return note r "LI1 the Bell has no bytes" false
  let (r1, v1, t1) := go prog r (Sim.signed r.st a a.key (Sim.S.pinsFor r.st.host [a.id]) (.install pb))
  r := note r1 s!"LI1 A installs the Bell ({pb.size} package bytes): {v1}" (v1 == "admitted")
  let some pkg := t1.bind fun t => (createdIds t).head? | return note r "LI1 no package id" false
  let some dP := p.rels.lookup "pending" | return note r "LI1 no pending" false
  let some dR := p.rels.lookup "rings" | return note r "LI1 no rings" false
  let seed ← match Read.readData p.state s!"(record (open true) (resident #{Print.hex (Sim.dc.bytes b.id)}))" with
    | .ok (.record ds) => match stateSlots (recordRow p.state) ds 0 with
      | some s => pure s
      | none => return note r "LI1 seed has no bytes" false
    | _ => return note r "LI1 no seed" false
  let (r2, v2, t2) := go prog r (Sim.signed r.st a a.key (Sim.S.pinsFor r.st.host [a.id, pkg]) (.create (some pkg) [] seed))
  let some obj := t2.bind fun t => (createdIds t).head? | return note r2 s!"LI1 no bell: {v2}" false
  r := note r2 s!"LI1 A creates the bell, B its resident: {v2}" (v2 == "admitted")
  let (r3, v3, t3) := go prog r (Sim.signed r.st a a.key (Sim.S.pinsFor r.st.host [a.id, b.id, obj]) (.grant obj b.id [.invoke 0, .invoke 4] none))
  let some gr := t3.bind fun t => (createdIds t).head? | return note r3 s!"LI1 A grants B answer and ring: {v3}" false
  r := note r3 s!"LI1 A grants B answer and ring: {v3}" (v3 == "admitted")
  -- LI2 the section (A its editor), as the document's rows build it
  let bnd ← match Doc.bundle with
    | .ok x => pure x
    | .error e => return note r s!"LI2 generating the section: {e}" false
  let mut libIds : List D := []
  for lib in bnd.libraries do
    let some bytes := Wire.encodePackage lib | return note r "LI2 helper has no bytes" false
    let (rL, vL, tL) := go prog r (Sim.signed r.st a a.key (Sim.S.pinsFor r.st.host [a.id]) (.install bytes))
    r := { rL with log := r.log, bad := r.bad }
    let some id := tL.bind fun t => (createdIds t).head? | return note r s!"LI2 a section helper: {vL}" false
    libIds := libIds ++ [id]
  let q ← match bnd.link (libIds.map Sim.dc.bytes) with
    | .ok q => pure q
    | .error e => return note r s!"LI2 linking the section: {e.name}" false
  let some qb := Wire.encodePackage q | return note r "LI2 the section has no bytes" false
  let (r4, v4, t4) := go prog r (Sim.signed r.st a a.key (Sim.S.pinsFor r.st.host (a.id :: libIds)) (.install qb))
  let some spkg := t4.bind fun t => (createdIds t).head? | return note r4 s!"LI2 A installs the section: {v4}" false
  let some dC := q.rels.lookup "candidates" | return note r "LI2 no candidates" false
  -- the target's relation the forward's support cites (`Bell.forwardRel`), as the resident pins it
  let some dF := q.rels.lookup Bell.forwardRel | return note r "LI2 no facts" false
  let factsIndex := (q.rels.map (·.1)).idxOf Bell.forwardRel
  let propose := q.methods.idxOf "propose"
  let seedData : List (Label × Data) :=
    [("accepted", .bool false), ("acceptor", .digest (Sim.dc.bytes a.id)), ("cap", .nat 2000),
     ("chooser", .digest (Sim.dc.bytes a.id)), ("closes", .nat 100000), ("selected", .inj "none" (.record []))]
  let some sseed := stateSlots (recordRow q.state) seedData 0 | return note r "LI2 section seed has no bytes" false
  let (r5, v5, t5) := go prog r4 (Sim.signed r4.st a a.key (Sim.S.pinsFor r4.st.host ([a.id, spkg] ++ libIds)) (.create (some spkg) [] sseed))
  let some sec := t5.bind fun t => (createdIds t).head? | return note r5 s!"LI2 A creates the section: {v5}" false
  r := note { r5 with log := r.log, bad := r.bad } s!"LI2 A installs the section ({qb.size} bytes; propose is method {propose}) and creates it, A its editor: {v4}, {v5}"
    (v4 == "admitted" && v5 == "admitted")
  -- LI3 A grants THE BELL OBJECT propose on the section, and posts the fact of that grant (cell gB, pin gB)
  let (r6, v6, t6) := go prog r (Sim.signed r.st a a.key (Sim.S.pinsFor r.st.host [a.id, obj, sec]) (.grant sec obj [.invoke propose] none))
  let some gB := t6.bind fun t => (createdIds t).head? | return note r6 s!"LI3 A grants the bell propose on the section: {v6}" false
  r := note r6 s!"LI3 A grants the bell object propose on the section: {v6}" (v6 == "admitted")
  let gBb := Sim.dc.bytes gB
  let secb := Sim.dc.bytes sec
  let factKey : Data := Bell.forwardKey gBb
  let pinFact (w : World D) := hole_pinAt sec w factsIndex dF factKey
  let pinCand (w : World D) (cand : ByteArray) := hole_pinAt sec w 0 dC (.record [("cand", .digest cand)])
  let status (w : World D) (cand : ByteArray) := hole_statusOf w sec dC cand
  let secCall (r : Run) (m : Sim.Member) (method : Label) (x : ByteArray) (rowPins : List (RowSlot D × D) := [])
      (cells : List D := []) : Call D :=
    signedAt r.st m (Sim.S.pinsFor r.st.host ([m.id, a.id, sec, spkg] ++ libIds ++ cells))
      (.invoke sec (q.methods.idxOf method) x 100000 none) r.st.host.height (r.st.host.height + 1024) rowPins
  let (r7, v7, _) := go prog r (secCall r a "post" (Doc.postArg gBb gBb))
  r := note r7 s!"LI3 A posts the fact of the bell's grant on the section (cell gB, pin gB): {v7}" (v7 == "admitted")
  -- the Bell's calls: `m` signs method `method` with the rows pinned; B's answer carries the section's cells too
  let pinRing (w : World D) (key : Data) := hole_pinAt obj w 0 dP key ++ hole_pinAt obj w 1 dR key
  let bellCall (r : Run) (m : Sim.Member) (method : Nat) (x : ByteArray) (nb : Nat)
      (rowPins : List (RowSlot D × D) := []) (cells : List D := []) : Call D :=
    let via := if m.id == b.id then some gr else none
    signedAt r.st m (Sim.S.pinsFor r.st.host ([m.id, obj, pkg] ++ via.toList ++ cells)) (.invoke obj method x 100000 via)
      nb (nb + 1024) rowPins
  let forwardCells := [sec, spkg, gB] ++ libIds
  -- LI4 A rings, aimed at the section's propose through gB, candidate gB
  let cand := gBb
  let h0 := r.st.host.height
  let k0 := ringKey h0 a
  let (r8, v8, _) := go prog r (bellCall r a 4 (aimedBellArg "what should the first section say?" cand propose secb gBb) h0)
  let aimRead := capturedTo (storyRow r8.st.host obj 0 dP k0)
  r := note r8 s!"LI4 A rings \"what should the first section say?\" aimed at the section's propose ({propose}) through the bell's grant: {v8}; the pending row holds the aim: {sameData aimRead (some (Bell.toData (some (Bell.aimData cand propose secb gBb))))}"
    (v8 == "admitted" && sameData aimRead (some (Bell.toData (some (Bell.aimData cand propose secb gBb)))))
  -- LI5 B answers DROPPING the aim: the rung guard compares the capture and refuses
  let (_, v9, _) := go prog r (bellCall r b 0 (answerArg h0 a "what should the first section say?" "a lamp on the stair") r.st.host.height
    (pinRing r.st.host k0))
  r := note r s!"LI5 B answers the aimed ring with the aim dropped (to none): {v9}" (deniedWith v9 "rung: text")
  -- LI6 B answers echoing the aim: the text lands in `rings` AND as the section's candidate, in one Turn
  let aim := Bell.toData (some (Bell.aimData cand propose secb gBb))
  let (r10, v10, t10) := go prog r (bellCall r b 0 (answerArgTo h0 a "what should the first section say?" "a lamp on the stair" (some (Bell.aimData cand propose secb gBb))) r.st.host.height
    (pinRing r.st.host k0 ++ pinFact r.st.host) forwardCells)
  let ringAnswer := match (storyRow r10.st.host obj 1 dR k0).bind (·.field "answered") with
    | some (.inj "some" (.inj "ask" (.bytes t))) => some t
    | _ => none
  let candRow := candidateOf r10.st.host sec dC cand
  -- `by` is the request's agent: the SIGNER (B, the resident), while the authority for the nested call is the
  -- Bell object's grant (`invokeRun`: `reqOf u obj principal`; `ownerAuthority … actor := obj`)
  let byResident := candRow.map (·.1) == some (Sim.dc.bytes b.id)
  r := note r10 s!"LI6 B answers echoing the aim: {v10}; rings[k] answered {ringAnswer.map String.fromUTF8!}; the section's candidate: value {candRow.map fun c => String.fromUTF8! c.2}, status {status r10.st.host cand}, by the resident B {byResident}; one turn with {t10.map (·.rows.length)} row acts; pending row gone {(storyRow r10.st.host obj 0 dP k0).isNone}"
    (v10 == "admitted" && ringAnswer == some "a lamp on the stair".toUTF8 && (candRow.map (·.2)) == some "a lamp on the stair".toUTF8 &&
      status r10.st.host cand == some "verified" && byResident && (storyRow r10.st.host obj 0 dP k0).isNone)
  -- LI6b the capture in `rings` is the ring's own: the aim as rung
  let keptAim := capturedTo (storyRow r10.st.host obj 1 dR k0)
  r := note r s!"LI6b the answered ring's capture still holds the aim as rung: {sameData keptAim (some aim)}" (sameData keptAim (some aim))
  -- LI7 A selects the agent's text: the section reads it
  let (r11, v11, _) := go prog r (secCall r a "select" (Doc.candArg cand) (pinCand r.st.host cand ++ pinFact r.st.host) [gB])
  r := note r11 s!"LI7 A selects the agent's text: {v11}; selected {hole_selectedOf Sim.env r11.st.host sec == some (some cand)}"
    (v11 == "admitted" && hole_selectedOf Sim.env r11.st.host sec == some (some cand))
  -- LI8 A revokes the bell's grant: the candidate's support is dead; rejudge says so by name; select refuses
  let (r12, v12, _) := go prog r (Sim.signed r.st a a.key (Sim.S.pinsFor r.st.host [a.id, gB]) (.retire gB))
  r := note r12 s!"LI8 A revokes the bell's grant on the section: {v12}" (v12 == "admitted")
  let (r13, v13, _) := go prog r (secCall r a "rejudge" (Doc.candArg cand) (pinCand r.st.host cand ++ pinFact r.st.host) [gB])
  r := note r13 s!"LI8b A rejudges the agent's text: {v13}; status {status r13.st.host cand}"
    (v13 == "admitted" && status r13.st.host cand == some "suspended \"support0 dead\"")
  let (_, v14, _) := go prog r (secCall r a "select" (Doc.candArg cand) (pinCand r.st.host cand ++ pinFact r.st.host) [gB])
  r := note r s!"LI8c A selects the withdrawn text again: {v14}" (refusedBy v14 "select" "support0 dead")
  -- LI9 a second aimed ring after the revoke: the forward is refused by the kernel (the revoked grant cell
  -- is a tombstone: `missingCell`), the answer with it; the ring stays pending
  let h1 := r.st.host.height
  let k1 := ringKey h1 a
  let cand2 := Sim.dc.bytes b.id
  let (r15, v15, _) := go prog r (bellCall r a 4 (aimedBellArg "and the second?" cand2 propose secb gBb) h1)
  r := note r15 s!"LI9 A rings again, aimed through the revoked grant: {v15}" (v15 == "admitted")
  let (r16, v16, _) := go prog r (bellCall r b 0 (answerArgTo h1 a "and the second?" "a ship in the fog" (some (Bell.aimData cand2 propose secb gBb))) r.st.host.height
    (pinRing r.st.host k1 ++ pinFact r.st.host) forwardCells)
  r := note r s!"LI9b B answers it echoing the aim: {v16}; the ring stays pending {(storyRow r16.st.host obj 0 dP k1).isSome}; no candidate {(candidateOf r16.st.host sec dC cand2).isNone}"
    (v16.startsWith "refused missingCell" && (storyRow r16.st.host obj 0 dP k1).isSome && (candidateOf r16.st.host sec dC cand2).isNone)
  -- LI9c (LANG-97) the ringer withdraws its own aimed ring at once: A, who aimed it through the revoked
  -- grant, retires it before its deadline; the ring and its pending row leave, and the queue is clear
  let (r17, v17, _) := go prog r (bellCall r a 3 (retireArg h1 a) r.st.host.height (pinRing r.st.host k1))
  r := note r17 s!"LI9c A withdraws its own aimed ring at {h1}, before its deadline: {v17}; pending row gone {(storyRow r17.st.host obj 0 dP k1).isNone}; rings row gone {(storyRow r17.st.host obj 1 dR k1).isNone}"
    (v17 == "admitted" && (storyRow r17.st.host obj 0 dP k1).isNone && (storyRow r17.st.host obj 1 dR k1).isNone)
  return r

/-- The inbox session over the Bell's surface source. -/
def session (bell : String) : Run :=
  let X := ctxWith langProgram
  let empty : Run := { st := { rng := ⟨1⟩, host := World.genesis X.env 0 0, members := [] } }
  let fk := [("li-a".toUTF8, "li-a-next".toUTF8), ("li-b".toUTF8, "li-b-next".toUTF8)]
  match genesis X Sim.worldName (Sim.nonceOf 12) 100000000
      (fk.map fun (k, n) => (k, nextKeyDigest X n)) Authority.none with
  | .error e => note empty s!"LI1 genesis: {e.name}" false
  | .ok g =>
    let ms := fk.zipIdx.map fun ((k, n), i) => (⟨founderId X g.origin i, k, n⟩ : Sim.Member)
    lifeRows { empty with st := { rng := ⟨1⟩, host := g, members := ms } }
      (ms.headD ⟨0, .empty, .empty⟩) (ms.getD 1 ⟨0, .empty, .empty⟩) bell

initialize register { name := "inbox", run := do pure (session (← readOr bellSourcePath)) }

end Nanodregg.Lang.Journey.Inbox
