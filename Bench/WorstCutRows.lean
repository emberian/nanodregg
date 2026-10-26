/-
# Bench.WorstCutRows — `bench-worstcut-rows SCRATCH [--harness-control]` (PERF-9, PERF-12)

The worst cut's `rows` tail: the deployed Bell queue (world/resident/Bell.ob, LANG-58/59), installed in
the object's first record with a bell whose resident is a second founder and the resident's grant,
then ring, answer, retire, ... : every Turn a row-only invoke (see `rowsCall`). Bench.WorstCut builds,
counts and prints.
-/
import Bench.WorstCut
import Lang.Surface
import Lang.Bell
import Lang.Read
import Lang.Print
import Lang.Rel
import Lang.Program

namespace Nanodregg.Bench.WorstCut.Rows

open Nanodregg.Kernel Nanodregg.Kernel.Receive Nanodregg.Host Nanodregg.Host.Deployed
open Nanodregg.Bench.WorstCut

/-- The `rows` shape's second founder: the Bell's resident (the first rings and retires). -/
def residentSecret : ByteArray := "worstcut-resident".toUTF8
def residentNext : ByteArray := "worstcut-resident-next".toUTF8
def foundersRows : List (ByteArray × D) := founders ++ [(P.pub residentSecret, nextKeyDigest X (P.pub residentNext))]

/-! ### The `rows` shape: the deployed Bell (world/resident/Bell.ob, LANG-58/59), installed and rung

A round of the Bell queue in THE BAR is a ring (2 row inserts) and its answer (1 upsert of the ring's
`rings` row with the answer, the ring's text sent back; 1 retract of `pending`); the owner retires an
answered ring (1 retract of `rings`), which keeps `pending` under its 64 and `rings` under its 1024
for a whole tail. So the tail is ring, answer, retire, ring, ... : every Turn a row-only
invoke, no cell written. -/

/-- What the rows tail needs: the resident member, the package, the bell, the resident's grant, and
the two relations' declarations. -/
structure RowsCtx where
  b : Who
  pkg : D
  obj : D
  gr : D
  dP : Lang.RelDecl
  dR : Lang.RelDecl

def bellSource : System.FilePath := "world" / "resident" / "Bell.ob"

def argOf (T : Lang.Ty) (d : Lang.Data) : ByteArray := (Lang.Wire.encodeData T d).getD .empty

def ringKey (nb : Nat) (ringer : D) : Lang.Data :=
  .record [("notBefore", .nat nb), ("ringer", .digest (X.env.bytes ringer))]

/-- The activity's row key; the public retire argument above keeps ringer. -/
def activityRowKey (nb : Nat) (ringer : D) : Lang.Data :=
  .record [("agent", .digest (X.env.bytes ringer)), ("notBefore", .nat nb)]

/-- Relation `rel`'s row at `key` on `w`, pinned at what the signer sees (Lang.Journey's `pinRow`). -/
def pinRow (rc : RowsCtx) (w : World D) (rel : Nat) (d : Lang.RelDecl) (key : Lang.Data) : List (RowSlot D × D) :=
  match Lang.keyBytes d key with
  | some k =>
    let s : RowSlot D := .row ⟨rc.obj, rel, k⟩
    [(s, rowPin X.env (headFloor X.env w.rows rc.obj rel) (rowAt X.env w.rows s))]
  | none => []

/-- Rows tail step `j` on `w` (methods: answer 0, retire 3, ring 4); `ring` is the notBefore of the
round's ring (set at phase 0). The call, and the ring's notBefore after it. -/
def rowsCall (rc : RowsCtx) (a : Who) (w : World D) (j ring : Nat) : Call D × Nat :=
  match j % 3 with
  | 0 =>
    (call w a [a.id, rc.obj, rc.pkg]
      (.invoke rc.obj 4 (argOf Lang.Bell.ringArg (.record [("text", .bytes "r".toUTF8), ("to", Lang.Bell.toData none)])) 100000 none), w.height)
  | 1 =>
    (call w rc.b [rc.b.id, rc.obj, rc.pkg, rc.gr]
      (.invoke rc.obj 0 (argOf Lang.Bell.answerArg
        (Lang.Bell.answerData ring "r".toUTF8 (X.env.bytes a.id) "a".toUTF8 none)) 100000 (some rc.gr))
      (pinRow rc w 0 rc.dP (activityRowKey ring a.id) ++ pinRow rc w 1 rc.dR (activityRowKey ring a.id)), ring)
  | _ =>
    (call w a [a.id, rc.obj, rc.pkg]
      (.invoke rc.obj 3 (argOf (.record [("notBefore", .nat), ("ringer", .digest)]) (ringKey ring a.id)) 100000 none)
      (pinRow rc w 1 rc.dR (activityRowKey ring a.id)), ring)

/-- Install the Bell, create a bell whose resident is `b`, grant `b` answer and ring: three admitted
calls on `w`, staged; the context, the steps and the World after. -/
def bellBase (src : String) (a b : Who) (w : World D) :
    Except String (RowsCtx × Array (Step D × D) × World D) := do
  let p ← match Lang.Surface.readPackage src with
    | .ok p => pure p
    | .error _ => throw s!"{bellSource} does not read as a package"
  let some pb := Lang.Wire.encodePackage p | throw "the Bell has no package bytes"
  let some dP := p.rels.lookup "pending" | throw "the Bell has no pending"
  let some dR := p.rels.lookup "rings" | throw "the Bell has no rings"
  let (s1, w1, pkg?) ← admitBorn w a [a.id] (.install pb)
  let some pkg := pkg? | throw "the install bore no package"
  let seed ← match Lang.Read.readData p.state s!"(record (open true) (resident #{Lang.Print.hex (X.env.bytes b.id)}))" with
    | .ok (.record ds) => match Lang.stateSlots (Lang.recordRow p.state) ds 0 with
      | some sl => pure sl
      | none => throw "the bell's seed has no bytes"
    | _ => throw "the bell's seed does not read"
  let (s2, w2, obj?) ← admitBorn w1 a [a.id, pkg] (.create (some pkg) [] seed)
  let some obj := obj? | throw "the create bore no bell"
  let (s3, w3, gr?) ← admitBorn w2 a [a.id, b.id, obj] (.grant obj b.id [.invoke 0, .invoke 4] none)
  let some gr := gr? | throw "the grant bore no cell"
  pure (⟨b, pkg, obj, gr, dP, dR⟩, #[s1, s2, s3], w3)

def shape : Shape (RowsCtx × Nat) where
  name := "rows"
  founders := foundersRows
  first g m w _ := do
    let src ← IO.FS.readFile bellSource
    let b := Who.of ⟨founderId X g.origin 1, residentSecret, residentNext⟩
    return (bellBase src m b w).map fun (rc, ss, w') => (ss, w', (rc, 0))
  step st m _ w j := let (cl, rg) := rowsCall st.1 m w j st.2; .ok (cl, (st.1, rg))

end Nanodregg.Bench.WorstCut.Rows
