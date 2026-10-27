/-
# Spec.Sim.Bell — the inputs of THE BELL's floors and inhabitants (TOPLEVEL-SPEC §6)

Tooling (a `Sim` module, closure C9): the row values the ringer's promise names, the two trivial
systems (`laxBell`: `bellAccept := bellLayoutOk`; `askFirstResident`: `ringAct := askFirst`), the
packages and run inputs of the deployed program's `answer` runs, and the tick around a parameter act.
The claims, top theorems, floors and inhabitants are `Spec.Proofs.Bell`.
-/
import Spec.System

namespace Nanodregg.Spec

/-- An answered `rings` value: `answered (some (l y))`, captured `l c`. -/
def answeredRow (l : Lang.Label) (y c : Lang.Data) : Lang.Data :=
  .record [("answered", .inj "some" (.inj l y)), ("captured", .inj l c)]

/-- A waiting `rings` value: not answered, captured `l c`. -/
def waitingRow (l : Lang.Label) (c : Lang.Data) : Lang.Data :=
  .record [("answered", .inj "none" (.record [])), ("captured", .inj l c)]


section ringerRun
open Nanodregg.Kernel Nanodregg.Kernel.Receive Nanodregg.Codec

/-- Each relation's guard erased. -/
def eraseGuards (rs : List (Lang.Label × Lang.RelDecl)) : List (Lang.Label × Lang.RelDecl) :=
  rs.map fun q => (q.1, { q.2 with guard := none })

/-- The lazy acceptance: `Lang.Bell.shapeOk` with the relations compared by layout only (each
relation's guard erased): the resident that checks the bell's answer type and its relations'
shapes, as `Shape.ofLines` alone did before HOSTING-45, but not the guards that make it a Bell. -/
def bellLayoutOk (p : Lang.Package) : Bool :=
  decide (eraseGuards p.rels = eraseGuards Lang.Bell.rels) && Lang.Bell.shapeOk { p with rels := Lang.Bell.rels }

/-- The Bell's parts the witness reads, as one package: `answer`, the cursor guard `queued` and the
log guard `rung` (the generated terms), the Bell's state and relations. `Lang.Bell.shapeOk` holds. -/
def minBell : Lang.Package where
  imports := []
  state := Lang.Bell.S
  iface := .record [("answer", Lang.Bell.answerTy), ("queued", Lang.guardTy Lang.Bell.S Lang.Bell.pending),
    ("rung", Lang.guardTy Lang.Bell.S Lang.Bell.rings)]
  body := .record [("answer", Lang.Bell.answer),
    ("queued", Lang.Std.activityQueued Lang.Bell.S Lang.Bell.pending Lang.Bell.resumer Lang.Bell.names
      (some Lang.Bell.patience)),
    ("rung", Lang.Bell.rung)]
  methods := ["answer"]
  laws := []
  rels := Lang.Bell.rels

/-- **The unguarded Bell**: `minBell` without `(guards queued rung)` (each relation's guard `none`). -/
def unguardedBell : Lang.Package := { minBell with rels := eraseGuards minBell.rels }

def bellDg (n : UInt8) : Digest := ⟨⟨Array.replicate 32 n⟩, by simp [ByteArray.size]⟩
def bellPkg : Digest := bellDg 1
def bellResident : Digest := bellDg 3
def bellRinger : Digest := bellDg 4
def bellCell (p : Lang.Package) : Cell := ⟨kindPackage, .rom, [(0, (Lang.Wire.encodePackage p).getD .empty)]⟩
def bellLook (p : Lang.Package) : Pinned Digest :=
  fun id => if id = bellPkg then .ok (some (bellCell p)) else .ok none
def bellState : Slots :=
  (Lang.stateSlots (Lang.recordRow Lang.Bell.S) [("open", .bool true), ("resident", .digest bellResident.bytes)] 0).getD []
def bellCapture : Lang.Data := .record [("text", .bytes "ring".toUTF8), ("to", Lang.Bell.toData none)]
/-- The ring answered `first`. -/
def bellAnsweredB : ByteArray :=
  (Lang.Wire.encodeData Lang.Bell.rings.val (answeredRow "ask" (.bytes "first".toUTF8) bellCapture)).getD .empty
/-- The ring waiting. -/
def bellWaitingB : ByteArray :=
  (Lang.Wire.encodeData Lang.Bell.rings.val (waitingRow "ask" bellCapture)).getD .empty
def bellKey : ByteArray := (Lang.keyBytes Lang.Bell.rings (Lang.Bell.keyData 5 bellRinger.bytes)).getD .empty
def bellPendB : ByteArray :=
  (Lang.Wire.encodeData Lang.Bell.pending.val (.record [("captured", .inj "ask" bellCapture)])).getD .empty
/-- The caller's view: `rings` at the key holds `old`; `pending` there holds the ring. -/
def bellRv (old : ByteArray) : RowView Digest :=
  ⟨fun _ rel => if rel = 1 then [(bellKey, some (.row 0 old 0))] else [(bellKey, some (.row 0 bellPendB 0))],
   fun _ _ => .ok []⟩
/-- `answer`'s argument: the ring `(5, ringer)`, its text `ring`, no aim, the answer `second`. -/
def bellArgs : ByteArray :=
  (Lang.Wire.encodeData Lang.Bell.answerArg
    (Lang.Bell.answerData 5 "ring".toUTF8 bellRinger.bytes "second".toUTF8 none)).getD .empty
def bellReq : Req Digest := ⟨bellResident, bellResident, bellDg 2, 5, 10, .invoke 0, none⟩

/-- Whether the deployed program's run of `answer` (method 0) at `p` over the `rings` row `old`
returns, upserting `rings` at the ring's key. -/
def bellUpserts (p : Lang.Package) (old : ByteArray) : Bool :=
  match Host.Deployed.X.program.run (bellLook p) (bellRv old) bellPkg bellState 0 bellArgs bellReq 1000000 with
  | .ok (_, _, rows, _) => rows.any fun q => decide (q.1 = .row ⟨bellReq.self, 1, bellKey⟩) &&
      match q.2 with
      | .upsert _ _ => true
      | _ => false
  | .error _ => false

/-- The package cell reads back as `p`, and the package id is a digest. -/
def bellReads (p : Lang.Package) : Bool :=
  decide (Digest.ofBytes? bellPkg.bytes = some bellPkg) &&
  match Lang.readPackage (bellLook p) bellPkg with
  | .ok q => decide (q = p)
  | .error _ => false

/-- The answered row's bytes read back as a row whose `answered` field is `some`. -/
def bellAnsweredReads : Bool :=
  match Lang.Wire.decodeData Lang.Bell.rings.val bellAnsweredB with
  | .ok d =>
    match d.field "answered" with
    | some (.inj "some" _) => true
    | _ => false
  | .error _ => false

/-- **The lax resident**: it accepts the bell's package by layout, not by its guards. -/
def laxBell (d : ByteArray → ByteArray) : System Digest := { deployed d with bellAccept := bellLayoutOk }

end ringerRun

section oneAsk
open Nanodregg.Hosting Nanodregg.Hosting.Resident

/-- The resident's act on the pending rings a tick read (deployed: `Hosting.Resident.actOn`). -/
abbrev RingAct := Where → Shape → Mem → List Ring → Prog Tick

/-- `Hosting.Resident.readP` with the act a parameter: the act IS the filling of the tick's `serve` hole
(`Hosting.Resident.fill`), so the System chooses how the hole is filled. -/
def readPWith (act : RingAct) (w : Where) (sh : Shape) (m : Mem) : Prog Tick :=
  .cmd (.read sh) fun
  | .error e => .say s!"read {e}" (.done (retry m s!"read {e}"))
  | .ok r =>
    if r.exit ≠ Protocol.CommandExit.ok.code then
      .say s!"read exit {r.exit} {String.fromUTF8? r.stderr |>.getD "?"}" (.done (retry m s!"read exit {r.exit}"))
    else
    match readOut sh r with
    | .error (x, d) => .done (.stop x d)
    | .ok pending => act w sh (m.prune pending) pending

/-- `Hosting.Resident.tickP` with the act a parameter: the resident's tick around `act`. -/
def tickWith (act : RingAct) (w : Where) (m : Mem) : Prog Tick :=
  match m.shape with
  | some sh => readPWith act w sh m
  | none =>
    .cmd .describe fun
    | .error e => .say s!"describe {e}" (.done (retry m s!"describe {e}"))
    | .ok r =>
      if r.exit ≠ Protocol.CommandExit.ok.code then
        .say s!"describe exit {r.exit} {String.fromUTF8? r.stderr |>.getD "?"}"
          (.done (retry m s!"describe exit {r.exit}"))
      else
        match describeOut w.conf r with
        | .ok sh =>
          .say s!"bell answer method {sh.answer} pending limit {sh.pending.limit}" <|
            readPWith act w sh { m with shape := some sh }
        | .error (x, d) => .done (.stop x d)

/-- **The act that asks first**: `actOn` with the ask before the intent's keep (what a crash between
the two would lose: the restart finds no intent and asks again). -/
def askFirst : RingAct := fun w sh m pending =>
  match decideTick pending m.kept with
  | .ask ring =>
    .ask ring (askOf w.conf ring) fun x =>
    .keep ring intentText fun ok =>
    if !ok then .done (.stop .volume "keep") else
    match x with
    | .notSent why => .say s!"ask not sent {why}" <| forgetThen (retry { m with kept := none } s!"ask {why}")
    | .answered a => answeredP sh m ring (answerText a)
    | .lost why => .say s!"ask spent, answer lost {why}" <| answeredP sh m ring (fit (named s!"unanswered {why}"))
  | _ => actOn w sh m pending

/-- A resident, a shape, a ring. -/
def bellWhere : Where := ⟨⟨.empty, .empty, 0, .empty, .empty⟩, "", "", ⟨""⟩, ⟨""⟩, ⟨""⟩⟩
def bellShape : Shape :=
  ⟨0, { key := pendingKey, val := pendingVal, limit := 64, sum := none, cap := 0, retract := true, guard := none },
   rfl, rfl⟩
def bellRing : Ring := ⟨5, .empty, "ring".toUTF8, none⟩
def bellMem : Mem := ⟨some bellShape, none, 0, []⟩

/-- **The ask-first resident**: its act asks before keeping the intent. -/
def askFirstResident (d : ByteArray → ByteArray) : System Codec.Digest := { deployed d with ringAct := askFirst }

end oneAsk

end Nanodregg.Spec
