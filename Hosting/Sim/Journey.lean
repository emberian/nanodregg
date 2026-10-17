/-
# Hosting.Sim.Journey — a grain's lifecycle through KERNEL's receivers, with its plants

`lake exe hosting-sim` drives the REAL receive path (`Receive.submit`: the receivers, then
`World.admit`) with `Lang.program` as the kernel's `Program`, under the Sim's toy parameters. Two
founders: A (the grain's owner) and B (another member, later the operator A grants `start` to).

* G0 `world/grain/Lifecycle` is the generated text (`Text.package lifecycle`), byte for byte.
* G1 A installs the grain package — admitted.
* G2 A creates a grain born `installed`, owned by A — admitted; its phase reads `installed`.
* G3 a grain born `running` — refused `lawDenied` by `phase` (born-only-initial).
* G4 a grain whose state names B as owner, created by A — refused `lawDenied` by `owner`.
* G5 A starts it — admitted, `running`. G6 A starts it again — refused by `phase` (no double start).
* G7 B, with no grant, stops it — refused by `owner`: KERNEL's `invoke` lets B act as itself, so
  only the law stands between a stranger and another member's grain.
* G8 A stops it — `stopped`. G9 A grants B `invoke:0` (start only). G10 B starts it through the
  grant — admitted, `running`. G11 B stops it through the same grant — refused `grantRight`.
* G12 A stops and removes it — `removed`. G13 A starts it — refused by `phase` (terminal).
* G14 the follower (`World.fold`) and the auditor reach the Host's World.

Plants (each must flip its line, or the run is RED):
* P1 skip-judge: G3's grain born `running` is ADMITTED, G6's double start is ADMITTED;
* P2 the package without its `owner` law: G7's stranger stop is ADMITTED.

The run is deterministic: a SEED argument (standing passes 1 2 3) changes nothing.
-/
import Kernel.Sim
import Lang.Program
import Hosting.Package
import Hosting.Text

namespace Nanodregg.Hosting.Sim

open Nanodregg.Kernel Nanodregg.Kernel.Receive Nanodregg.Lang
open Nanodregg.Hosting Nanodregg.Hosting.Grain
abbrev D := Kernel.Sim.D

def textPath : System.FilePath := "world" / "grain" / "Lifecycle"

def langProgram : Program D := Lang.program Kernel.Sim.dc.bytes Kernel.Sim.digestOf
def skipJudge : Program D := { langProgram with judge := fun _ _ _ _ _ _ => .ok () }

/-- The planted package: the lifecycle without its `owner` law. -/
def noOwnerLaw : Package := { lifecycle with laws := ["phase"] }

structure Run where
  st : Kernel.Sim.State
  log : List String := []
  bad : Nat := 0

def note (r : Run) (line : String) (good : Bool) : Run :=
  { r with log := r.log ++ [s!"{if good then "ok  " else "FAIL"} {line}"],
           bad := r.bad + (if good then 0 else 1) }

/-- Submit on the Host path; the verdict's text and the Turn. -/
def go (prog : Program D) (r : Run) (c : Call D) : Run × String × Option (Turn D) :=
  match Receive.submit (Kernel.Sim.ctxWith prog) r.st.host c with
  | .error (.refused (.lawDenied _ why)) => (r, s!"refused lawDenied {why}", none)
  | .error (.refused e) => (r, s!"refused {e.name}", none)
  | .error (.rejected e) => (r, s!"rejected {Kernel.Sim.nameOf e}", none)
  | .ok (t, w') => ({ r with st := { r.st with host := w', log := r.st.log ++ [t] } }, "admitted", some t)

def phaseAt (w : World D) (g : D) : Option Phase := (w.live g).bind fun c => phaseOf c.slots

def phaseName : Option Phase → String
  | some p => p.label
  | none => "none"

def created (t : Option (Turn D)) : Option D := t.bind fun t => (createdIds Kernel.Sim.env t).head?

def lawSays (v why : String) : Bool := v.startsWith "refused lawDenied" && (v.splitOn why).length > 1

/-- What a line must see: an exact verdict, or a law refusal with this reason. -/
inductive Want
  | admitted
  | law (why : String)
  | refusal (name : String)

def Want.met (v : String) : Want → Bool
  | .admitted => v == "admitted"
  | .law why => lawSays v why
  | .refusal n => v == s!"refused {n}"

/-- Which plant this run is. -/
inductive Plant | none | skipJudge | noOwnerLaw
  deriving DecidableEq

def journey (plant : Plant) : Run := Id.run do
  let prog := if plant = .skipJudge then skipJudge else langProgram
  let pkg := if plant = .noOwnerLaw then noOwnerLaw else lifecycle
  let tag := match plant with | .none => "" | .skipJudge => "P1 skip-judge: " | .noOwnerLaw => "P2 no owner law: "
  let fk : List (ByteArray × ByteArray) := [("f0".toUTF8, "f0-next".toUTF8), ("f1".toUTF8, "f1-next".toUTF8)]
  let X := Kernel.Sim.ctxWith prog
  let g0 := genesis X Kernel.Sim.worldName 100000000 (fk.map fun (k, n) => (k, nextKeyDigest X n))
  let members := fk.zipIdx.map fun ((k, n), i) => (⟨founderId X Kernel.Sim.worldName i, k, n⟩ : Kernel.Sim.Member)
  let mut r : Run := { st := { rng := ⟨1⟩, host := g0, members } }
  let a := members.headD ⟨0, .empty, .empty⟩
  let b := members.getD 1 ⟨0, .empty, .empty⟩
  let call := fun (r : Run) (m : Kernel.Sim.Member) (ids : List D) (body : Body D) =>
    Kernel.Sim.signed r.st m m.key (Kernel.Sim.S.pinsFor r.st.host ids) body
  let some pkgBytes := Wire.encodePackage pkg | return note r "G1 the package has no bytes" false
  let some seedA := seed .app "app".toUTF8 (Kernel.Sim.dc.bytes a.id) | return note r "G2 no seed" false
  let some seedB := seed .app "app".toUTF8 (Kernel.Sim.dc.bytes b.id) | return note r "G4 no seed" false
  let some running := Wire.encodeData phaseTy (.inj "running" unitD) | return note r "G3 no bytes" false
  let some args := noArgs | return note r "G5 no argument bytes" false
  -- G1 install
  let (r1, v1, t1) := go prog r (call r a [a.id] (.install pkgBytes))
  r := note r1 s!"{tag}G1 A installs the grain package: {v1}" (v1 == "admitted")
  let some p := created t1 | return note r "G1 no package id" false
  -- G2 create
  let (r2, v2, t2) := go prog r (call r a [a.id, p] (.create (some p) [] seedA))
  r := note r2 s!"{tag}G2 A creates a grain: {v2}, phase {phaseName ((created t2).bind (phaseAt r2.st.host))}"
    (v2 == "admitted" && (created t2).bind (phaseAt r2.st.host) == some .installed)
  let some gr := created t2 | return note r "G2 no grain id" false
  -- G3 born running
  let (r3, v3, _) := go prog r (call r a [a.id, p] (.create (some p) [] (seedA.set slotPhase running)))
  let want3 : Want := if plant = .skipJudge then .admitted else if plant = .none then .law "phase: no born from running" else .law "phase"
  r := note r3 s!"{tag}G3 a grain born running: {v3}" (want3.met v3)
  -- G4 owner in state is not the creator
  let (r4, v4, _) := go prog r (call r a [a.id, p] (.create (some p) [] seedB))
  if plant = .none then r := note r4 s!"G4 A creates a grain owned by B: {v4}" (Want.met v4 (.law "owner: not the creator"))
  else r := r4
  -- the event steps on the grain
  let ev := fun (r : Run) (m : Kernel.Sim.Member) (e : Event) (via : Option D) =>
    go prog r (call r m ([m.id, gr, p] ++ via.toList) (.invoke gr e.index args 100000 via))
  let check := fun (r : Run) (line : String) (want : Want) (v : String) (ph : Option Phase) =>
    note r s!"{tag}{line}: {v}, phase {phaseName (phaseAt r.st.host gr)}" (want.met v && (ph.isNone || phaseAt r.st.host gr == ph))
  let (r5, v5, _) := ev r a .start none
  r := check r5 "G5 A starts" .admitted v5 (some .running)
  let (r6, v6, _) := ev r a .start none
  r := check r6 "G6 A starts again" (if plant = .skipJudge then .admitted else if plant = .none then .law "phase: no start from running" else .law "phase") v6 none
  let (r7, v7, _) := ev r b .stop none
  if plant = .skipJudge then r := r7
  else r := check r7 "G7 B (no grant) stops" (if plant = .noOwnerLaw then .admitted else .law "owner: not the owner") v7 none
  if plant ≠ .none then return r
  let (r8, v8, _) := ev r a .stop none
  r := check r8 "G8 A stops" .admitted v8 (some .stopped)
  let (r9, v9, t9) := go prog r (call r a [a.id, b.id, gr] (.grant gr b.id [.invoke Event.start.index] none))
  r := note r9 s!"G9 A grants B invoke:{Event.start.index} (start): {v9}" (v9 == "admitted")
  let some gB := created t9 | return note r "G9 no grant id" false
  let (r10, v10, _) := ev r b .start (some gB)
  r := check r10 "G10 B starts through the grant" .admitted v10 (some .running)
  let (r11, v11, _) := ev r b .stop (some gB)
  r := check r11 "G11 B stops through the start-only grant" (.refusal "grantRight") v11 (some .running)
  let (r12a, v12a, _) := ev r a .stop none
  let (r12, v12, _) := ev r12a a .remove none
  r := check r12 s!"G12 A stops ({v12a}) and removes" .admitted v12 (some .removed)
  let (r13, v13, _) := ev r a .start none
  r := check r13 "G13 A starts a removed grain" (.law "phase: no start from removed") v13 (some .removed)
  match World.fold Kernel.Sim.env g0 r.st.log with
  | .ok w => r := note r s!"G14 the follower reaches the Host's World ({r.st.log.length} turns)" (Kernel.Sim.same w r.st.host)
  | .error (i, e) => r := note r s!"G14 follower refused at {i}: {Kernel.Sim.nameOf e}" false
  match audit X g0 r.st.log with
  | .ok w => r := note r "G14 the auditor reaches the Host's World" (Kernel.Sim.same w r.st.host)
  | .error (i, e) => r := note r s!"G14 auditor refused at {i}: {reprStr e}" false
  return r

/-- G0: the shipped text is the generated one. -/
def textLine : IO (String × Bool) := do
  let some want := Text.package lifecycle | return ("G0 the grain package has no text", false)
  let have_ ← try IO.FS.readFile textPath catch _ => pure ""
  if have_ == want then return (s!"G0 {textPath} is the generated text ({want.length} bytes)", true)
  return (s!"G0 {textPath} differs from Text.package lifecycle (hosting-sim --write-text rewrites it)", false)

def runAll (args : List String) : IO UInt32 := do
  if args == ["--write-text"] then
    let some t := Text.package lifecycle | IO.eprintln "no text"; return 1
    IO.FS.createDirAll (textPath.parent.getD ".")
    IO.FS.writeFile textPath t
    IO.println s!"wrote {textPath}"
    return 0
  let (l0, ok0) ← textLine
  IO.println s!"{if ok0 then "ok  " else "FAIL"} {l0}"
  let runs := [journey .none, journey .skipJudge, journey .noOwnerLaw]
  for r in runs do for l in r.log do IO.println l
  let bad := runs.foldl (· + ·.bad) (if ok0 then 0 else 1)
  IO.println s!"hosting-sim: {if bad = 0 then "GREEN" else s!"RED ({bad})"}"
  return if bad = 0 then 0 else 1

end Nanodregg.Hosting.Sim
