/-
# Lang.Journey.Retire — §RT: an object's end, judged by every law in force (KERNEL-70)

`Body.retire` ends a cell; for an object every law in force judges the occasion `retire` over its
last state (`old = new`, `Receive.retireCheck`), and `World.admit` clears what hangs under it. Every
row is a call through `Receive.submit` with `Lang.program` as the kernel's `Program`, except RT9 and
RT10, which hand `World.admit` (the one admission path, which a follower re-runs) a Turn no receiver
derives. Each row names its expected verdict.

* RT0 A installs two law packages (`Std.ownerSigns`, `Std.quorum` over {A, B}, k = 2) and the board
  (a programmed object whose package declares the relation `notes`, retract allowed, with `put` and
  `drop`).
* RT1 a data object A owns under `ownerSigns`: B's retirement is the kernel's `notOwner`; RT2 A's is
  admitted, the cell is a tombstone and the World's allowance gets back exactly its weight.
* RT3 a data object A owns under `quorum`: A's retirement is `lawDenied` (`quorum`), and the object
  stays live.
* RT4 A creates the board and puts a note (one row; the relation's head holds it); RT5 its
  retirement is `rowsRemain` (`World.admit`: a relation is cleared before its object goes); RT6
  `drop` retracts the row; RT7 the retirement is admitted: the cell is a tombstone, its relation
  head left with it (`dropHeads`), and the allowance gets back the object's weight plus the heads'
  (the rows' weight it no longer holds).
* RT8 a call pinning the board at its last live entry is `stale`; RT9 a row touch under it, the
  board pinned at its tombstone, is `orphanRow`; RT10 a range read of its relation is `noRelation`.
-/
import Lang.Journey
import Lang.Surface

namespace Nanodregg.Lang.Journey.Retire

open Nanodregg.Kernel Nanodregg.Kernel.Receive Nanodregg.Lang.Journey

/-- The board: one relation, `notes`, keyed by a natural, retract allowed; `put` inserts a note,
`drop` retracts one; the law `board` admits every act. -/
def boardSource : String := "
(package
  (doc \"A board of notes: put inserts a note, drop retracts it; the board ends only once its notes are gone.\")
  (state (rec (n nat)))
  (rel notes (key (k nat)) (val (rec (v nat))) (limit 8) (retract))
  (method put (arg (rec (k nat))) (edits 1)
    (done state (insert notes (record (k arg.k)) (record (v 1)))))
  (method drop (arg (rec (k nat))) (edits 1)
    (done state (retract notes (record (k arg.k)))))
  (law board (else ok)))
"

def RS : Ty := .record [("total", .nat)]
def QS : Ty := .record [("approvals", .nat), ("proposal", Std.proposalTy .nat), ("total", .nat)]

/-- The entry's weight, what a retirement gives back (`Entry.weight`). -/
def weightOf (w : World D) (x : D) : Nat := ((w.entry Sim.env x).map Entry.weight).getD 0

def isTomb (w : World D) (x : D) : Bool := w.entry Sim.env x == some .tomb

def rtRows (r0 : Run) (a b : Sim.Member) : Run := Id.run do
  let prog := langProgram
  let mut r := r0
  let install (r : Run) (p : Package) : Run × String × Option D :=
    match Wire.encodePackage p with
    | none => (r, "no bytes", none)
    | some pb =>
      let (r', v, t) := go prog r (Sim.signed r.st a a.key (Sim.S.pinsFor r.st.host [a.id]) (.install pb))
      (r', v, t.bind fun t => (createdIds t).head?)
  let q ← match Std.quorum QS .nat [Sim.dc.bytes a.id, Sim.dc.bytes b.id] 2 "total" with
    | .ok q => pure q
    | .error e => return note r s!"RT0 quorum refused: {e.name}" false
  let board ← match Surface.readPackage boardSource with
    | .ok p => pure p
    | .error e => return note r s!"RT0 read the board: {e.text boardSource}" false
  let some nd := board.rels.lookup "notes" | return note r "RT0 the board has no notes relation" false
  let (r1, v1, own?) := install r (Std.pkgOf RS [("own", Std.ownerSigns RS)] [])
  let (r2, v2, quo?) := install r1 (Std.pkgOf QS [("shared", q)] [])
  let (r3, v3, bpk?) := install r2 board
  let some own := own? | return note r1 s!"RT0 install ownerSigns: {v1}" false
  let some quo := quo? | return note r2 s!"RT0 install quorum: {v2}" false
  let some bpk := bpk? | return note r3 s!"RT0 install the board: {v3}" false
  r := note r3 s!"RT0 A installs ownerSigns, quorum \{A, B} k 2 and the board (methods {board.methods}, relations {board.rels.map (·.1)}): {[v1, v2, v3]}"
    ([v1, v2, v3].all (· == "admitted") && board.methods == ["drop", "put"] && board.rels.map (·.1) == ["notes"])
  let retire (r : Run) (m : Sim.Member) (x : D) (cells : List D) : Run × String × Option (Turn D) :=
    go prog r (Sim.signed r.st m m.key (Sim.S.pinsFor r.st.host ([m.id, x] ++ cells)) (.retire x))
  -- RT1/RT2 a data object under ownerSigns
  let some s0 := stateSlots (recordRow RS) [("total", .nat 3)] 0 | return note r "RT1 no seed bytes" false
  let (rc, vc, tc) := go prog r (Sim.signed r.st a a.key (Sim.S.pinsFor r.st.host [a.id, own]) (.create none [own] s0))
  let some dobj := tc.bind fun t => (createdIds t).head? | return note rc s!"RT1 A creates a data object under ownerSigns: {vc}" false
  r := rc
  let (_, v4, _) := retire r b dobj [own]
  r := note r s!"RT1 B retires A's data object under ownerSigns (expected notOwner): {v4}"
    (v4.startsWith "refused notOwner" && !isTomb r.st.host dobj)
  let w0 := r.st.host
  let back := weightOf w0 dobj
  let (r5, v5, t5) := retire r a dobj [own]
  let paid := (t5.map (·.charge)).getD 0
  r := note r5 s!"RT2 A retires it (expected admitted): {v5}; a tombstone {isTomb r5.st.host dobj}; allowance {w0.allowance} → {r5.st.host.allowance}, charge {paid}, weight back {back}"
    (v5 == "admitted" && isTomb r5.st.host dobj && 0 < back &&
      r5.st.host.allowance + paid == w0.allowance + back)
  -- RT3 a data object under quorum: one signer does not end it
  let some sq := stateSlots (recordRow QS)
      [("approvals", .nat 0), ("proposal", .inj "set" (.nat 0)), ("total", .nat 0)] 0
    | return note r "RT3 no seed bytes" false
  let (rq, vq, tq) := go prog r (Sim.signed r.st a a.key (Sim.S.pinsFor r.st.host [a.id, quo]) (.create none [quo] sq))
  let some qobj := tq.bind fun t => (createdIds t).head? | return note rq s!"RT3 A creates a data object under quorum: {vq}" false
  r := rq
  let (_, v6, _) := retire r a qobj [quo]
  r := note r s!"RT3 A, its owner, retires the quorum object (expected lawDenied quorum): {v6}"
    (deniedWith v6 "shared: quorum" && (r.st.host.live Sim.env qobj).isSome)
  -- RT4 the board, holding one note
  let some sb := stateSlots (recordRow board.state) [("n", .nat 0)] 0 | return note r "RT4 no seed bytes" false
  let (rb, vb, tb) := go prog r (Sim.signed r.st a a.key (Sim.S.pinsFor r.st.host [a.id, bpk]) (.create (some bpk) [] sb))
  let some bobj := tb.bind fun t => (createdIds t).head? | return note rb s!"RT4 A creates the board: {vb}" false
  r := rb
  let key : Data := .record [("k", .nat 1)]
  let some kb := keyBytes nd key | return note r "RT4 no key bytes" false
  let slot : RowSlot D := .row ⟨bobj, 0, kb⟩
  let some karg := Wire.encodeData (.record [("k", .nat)]) (.record [("k", .nat 1)]) | return note r "RT4 no arg bytes" false
  let callB (r : Run) (method : Nat) (rowPins : List (RowSlot D × D)) : Call D :=
    signedRows r.st a (Sim.S.pinsFor r.st.host [a.id, bobj, bpk]) rowPins [] (.invoke bobj method karg 100000 none)
  let present (w : World D) : Bool := (rowAt Sim.env w.rows slot).isSome
  let pinNow (w : World D) : List (RowSlot D × D) :=
    [(slot, rowPin Sim.env (headFloor Sim.env w.rows bobj 0) (rowAt Sim.env w.rows slot))]
  let (rp, vp, tp) := go prog r (callB r 1 [])
  let some tPut := tp | return note rp s!"RT4 A puts note 1: {vp}" false
  r := note rp s!"RT4 A creates the board and puts note 1 (expected admitted): {[vb, vp]}; the row stands {present rp.st.host}; head count {headCount rp.st.host bobj 0}"
    (vb == "admitted" && vp == "admitted" && present rp.st.host && headCount rp.st.host bobj 0 == some 1)
  -- RT5 a parent holding a row is not retired
  let (_, v7, _) := retire r a bobj [bpk]
  r := note r s!"RT5 A retires the board while note 1 stands (expected rowsRemain): {v7}"
    (v7.startsWith "rejected rowsRemain" && (r.st.host.live Sim.env bobj).isSome)
  -- RT6 drop retracts the row
  let (rd, vd, _) := go prog r (callB r 0 (pinNow r.st.host))
  r := note rd s!"RT6 A drops note 1 (expected admitted): {vd}; the row stands {present rd.st.host}; head count {headCount rd.st.host bobj 0}"
    (vd == "admitted" && !present rd.st.host && headCount rd.st.host bobj 0 == some 0)
  -- RT7 the empty board is retired; its head leaves with it
  let w1 := r.st.host
  let live := weightOf w1 bobj
  let heads := rowsWeight w1.rows
  -- the call RT8 sends: signed while the board was live, pinned at that entry
  let late := callB r 1 []
  let (rr, v8, t8) := retire r a bobj [bpk]
  let w2 := rr.st.host
  let paid := (t8.map (·.charge)).getD 0
  let headsBack := heads - rowsWeight w2.rows
  r := note rr s!"RT7 A retires the empty board (expected admitted): {v8}; a tombstone {isTomb w2 bobj}; its head {(headOf Sim.env w1.rows bobj 0).isSome} → {(headOf Sim.env w2.rows bobj 0).isSome}; allowance {w1.allowance} → {w2.allowance}, charge {paid}, back {live} (the cell) + {headsBack} (its heads)"
    (v8 == "admitted" && isTomb w2 bobj && (headOf Sim.env w1.rows bobj 0).isSome &&
      (headOf Sim.env w2.rows bobj 0).isNone && rowsWeight w2.rows < heads && 0 < live &&
      w2.allowance + paid == w1.allowance + live + headsBack)
  -- RT8 a call pinned at the board's live entry
  let (_, v9, _) := go prog r late
  r := note r s!"RT8 a put pinned at the board's last live entry (expected stale): {v9}" (v9.startsWith "rejected stale")
  -- RT9/RT10 Turns no receiver derives, handed to World.admit: the board pinned at its tombstone
  let atTomb : List (Touch D) := [⟨bobj, pinOf Sim.env (w2.entry Sim.env bobj), .keep⟩]
  let tRow : Turn D :=
    { tPut with txId := tPut.txId + 1, touches := atTomb, notBefore := w2.height + 1, validUntil := w2.height + 1 }
  let v10 := match World.admit Sim.env w2 tRow with
    | .error e => e.name
    | .ok _ => "admitted"
  r := note r s!"RT9 a row insert under the retired board, the board pinned at its tombstone (expected orphanRow): {v10}"
    (v10 == "orphanRow")
  let tRange : Turn D := { tRow with txId := tPut.txId + 2, rows := [], ranges := [⟨bobj, 0, .empty, 8, 0⟩] }
  let v11 := match World.admit Sim.env w2 tRange with
    | .error e => e.name
    | .ok _ => "admitted"
  r := note r s!"RT10 a range read of the retired board's relation (expected noRelation): {v11}"
    (v11 == "noRelation")
  return r

/-- A fresh session for the RT rows. -/
def retireSession : Run :=
  let X := ctxWith langProgram
  let fk := [("rt-a".toUTF8, "rt-a-next".toUTF8), ("rt-b".toUTF8, "rt-b-next".toUTF8)]
  match genesis X Sim.worldName (Sim.nonceOf 11) 100000000
      (fk.map fun (k, n) => (k, nextKeyDigest X n)) Authority.none with
  | .error e => note { st := { rng := ⟨1⟩, host := World.genesis X.env 0 0, members := [] } }
      s!"RT genesis: {e.name}" false
  | .ok g =>
    let ms := fk.zipIdx.map fun ((k, n), i) => (⟨founderId X g.origin i, k, n⟩ : Sim.Member)
    rtRows { st := { rng := ⟨1⟩, host := g, members := ms } }
      (ms.headD ⟨0, .empty, .empty⟩) (ms.getD 1 ⟨0, .empty, .empty⟩)

initialize register { name := "retire", run := pure retireSession }

end Nanodregg.Lang.Journey.Retire
