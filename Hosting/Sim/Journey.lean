/-
# Hosting.Sim.Journey — a grain's lifecycle through KERNEL's receivers, with its plants

`lake exe hosting-sim` drives the REAL receive path (`Receive.submit`: the receivers, then
`World.admit`) with `Lang.program` as the kernel's `Program`, under the Sim's toy parameters. Two
founders: A (the grain's owner, KERNEL's slot 1) and B (another member, later the operator A
grants `start` to).

* G0 `world/grain/Lifecycle` is the generated text (`Lang.Print.package lifecycle`), byte for byte.
* G1 A installs the grain package — admitted.
* G2 A creates a grain born `installed`, owned by A — admitted; its phase reads `installed`.
* G3 a grain born `running` — refused `lawDenied` by `phase` (born-only-initial).
* G5 A starts it — admitted, `running`. G6 A starts it again — refused by `phase` (no double start).
* G7 B, with no grant, stops it — refused `noGrant` by KERNEL's `invoke` (KERNEL-25: owner-gated,
  before any law runs; it holds under skip-judge too: authority is not a law).
* G8 A stops it — `stopped`. G9 A grants B `invoke:1` (start only). G10 B starts it through the
  grant — admitted, `running`. G11 B stops it through the same grant — refused `grantRight`.
* G12 A stops and removes it — `removed`. G13 A starts it — refused by `phase` (terminal).
* G15 the controller (Store `w1`) over the running grain's id (listed twice: one action), no child: `launch` with the plan
  `worlds/w1/grains/<hex>/pkg/app`; with its child running: nothing. A look-alike (same state,
  another package, started) is never launched; the ids of the log's Turns (`touchedIds`, what HOST's
  tail hands the controller) reconcile to exactly the grain's launch.
* G17 the controller's ROUND (`Loop.step`, what `hosting-controller` runs): round 0 over every live
  id launches exactly the grain; touched again before any report: nothing (the launch marks it
  running); `started`: nothing; `exited` while it still desires `running`: relaunched; four
  `failed` reports more (five exits in the window): refused `crashLoop`, never launched.
* G16 the controller over the removed grain with its child still running: `kill`.
* G14 the follower (`World.fold`) and the auditor reach the Host's World.

Plants (each must flip its line, or the run is RED):
* P1 skip-judge: G3's grain born `running` is ADMITTED, G6's double start is ADMITTED.
The stranger plant moved to KERNEL (kernel-sim's invoke-no-grant arm, KERNEL-25).

The run (`Hosting.Sim.Run`, with the allowance journey `Hosting.Sim.Allowance`) is deterministic: a
SEED argument (standing passes 1 2 3) changes nothing. It ends `ALL PASS`.
-/
import Kernel.Sim
import Lang.Program
import Hosting.Package
import Lang.Print
import Hosting.Controller
import Hosting.Loop

namespace Nanodregg.Hosting.Sim

open Nanodregg.Kernel Nanodregg.Kernel.Receive Nanodregg.Lang
open Nanodregg.Hosting Nanodregg.Hosting.Grain
abbrev D := Kernel.Sim.D

def textPath : System.FilePath := "world" / "grain" / "Lifecycle"

def langProgram : Program D := Lang.program Kernel.Sim.dc.bytes Kernel.Sim.digestOf
def skipJudge : Program D := { langProgram with judge := fun _ _ _ _ _ _ => .ok () }

def lifecycle : Option Package := Grain.lifecycle?.toOption

/-- A look-alike: the same state and methods, no law, so other bytes and another package id. -/
def lookAlike : Option Package := lifecycle.map fun p => { p with laws := [] }

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

def phaseAt (w : World D) (g : D) : Option Phase := (w.live Kernel.Sim.env g).bind fun c => phaseOf c.slots

/-- The plan G15 expects, spelled out path by path (not through `Plan`'s own helpers). -/
def wantPlan (label hx : ByteArray) : Plan where
  program := [lit "worlds", label, lit "grains", hx, lit "pkg", lit "app"]
  read := [[lit "worlds", label, lit "grains", hx, lit "pkg"]]
  write := [[lit "worlds", label, lit "grains", hx, lit "vol"]]
  exec := []
  hidden := [[lit "worlds", label, lit "store"], [lit "worlds", label, lit "members"]]

/-- The launcher's report of a grain whose child is running. -/
def upLive (g : ByteArray) : Controller.Live := { grain := g, running := true, exits := [] }

def phaseName : Option Phase → String
  | some p => p.label
  | none => "none"

def created (t : Option (Turn D)) : Option D := t.bind fun t => (createdIds t).head?

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
inductive Plant | none | skipJudge
  deriving DecidableEq

def journey (plant : Plant) (pkg : Package) : Run := Id.run do
  let prog := if plant = .skipJudge then skipJudge else langProgram
  let tag := match plant with | .none => "" | .skipJudge => "P1 skip-judge: "
  let fk : List (ByteArray × ByteArray) := [("f0".toUTF8, "f0-next".toUTF8), ("f1".toUTF8, "f1-next".toUTF8)]
  let X := Kernel.Sim.ctxWith prog
  let g0 ← match genesis X Kernel.Sim.worldName (Kernel.Sim.nonceOf 0) 100000000 (fk.map fun (k, n) => (k, nextKeyDigest X n)) with
    | .ok g => pure g
    | .error e =>
        return note { st := { rng := ⟨1⟩, host := World.genesis X.env 0 0, members := [] } } s!"genesis refused {e.name}" false
  let members := fk.zipIdx.map fun ((k, n), i) => (⟨founderId X g0.origin i, k, n⟩ : Kernel.Sim.Member)
  let mut r : Run := { st := { rng := ⟨1⟩, host := g0, members } }
  let a := members.headD ⟨0, .empty, .empty⟩
  let b := members.getD 1 ⟨0, .empty, .empty⟩
  let call := fun (r : Run) (m : Kernel.Sim.Member) (ids : List D) (body : Body D) =>
    Kernel.Sim.signed r.st m m.key (Kernel.Sim.S.pinsFor r.st.host ids) body
  let some pkgBytes := Wire.encodePackage pkg | return note r "G1 the package has no bytes" false
  let some seedA := seed .app "app".toUTF8 | return note r "G2 no seed" false
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
  let want3 : Want := if plant = .skipJudge then .admitted else .law "phase: phase does not start at installed"
  r := note r3 s!"{tag}G3 a grain born running: {v3}" (want3.met v3)
  -- the event steps on the grain
  let ev := fun (r : Run) (m : Kernel.Sim.Member) (e : Event) (via : Option D) =>
    go prog r (call r m ([m.id, gr, p] ++ via.toList) (.invoke gr e.index args 100000 via))
  let check := fun (r : Run) (line : String) (want : Want) (v : String) (ph : Option Phase) =>
    note r s!"{tag}{line}: {v}, phase {phaseName (phaseAt r.st.host gr)}" (want.met v && (ph.isNone || phaseAt r.st.host gr == ph))
  let (r5, v5, _) := ev r a .start none
  r := check r5 "G5 A starts" .admitted v5 (some .running)
  let (r6, v6, _) := ev r a .start none
  r := check r6 "G6 A starts again" (if plant = .skipJudge then .admitted else .law "phase: no edge") v6 none
  let (r7, v7, _) := ev r b .stop none
  r := check r7 "G7 B (no grant) stops" (.refusal "noGrant") v7 none
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
  -- G15 the controller over the World
  let label := "w1".toUTF8
  let some pid := Controller.lifecycleId Kernel.Sim.env | return note r "G15 the lifecycle has no id" false
  r := note r "G15 Controller.lifecycleId is the installed package's id" (pid == p)
  let pkgId := Kernel.Sim.dc.bytes pid
  let hx := (Lang.Print.hex (Kernel.Sim.dc.bytes gr)).toUTF8
  let ctl := fun (r : Run) (live : List Controller.Live) (g : D) (_ : ByteArray) =>
    Controller.reconcile Kernel.Sim.env Kernel.Sim.dc.bytes label pkgId 0 live r.st.host [g, g]
  let want := wantPlan label hx
  r := note r "G15 controller, no child: launch with the grain's plan"
    (ctl r [] gr hx == [{ grain := hx, verdict := .launch want }])
  r := note r "G15 the ids of the log's Turns, reconciled, launch exactly the grain"
    (Controller.reconcile Kernel.Sim.env Kernel.Sim.dc.bytes label pkgId 0 [] r.st.host
      (Controller.touchedIds r.st.log) == [{ grain := hx, verdict := .launch want }])
  r := note r "G15 controller, child running: nothing"
    ((ctl r [upLive hx] gr hx).isEmpty)
  -- G17 the controller's round
  let round := fun (st : Loop.State D) (ids : List D) (rs : List Report) =>
    Loop.step Kernel.Sim.env Kernel.Sim.dc.bytes label pkgId r.st.host st ids rs
  let launchA : List Action := [{ grain := hx, verdict := .launch want }]
  let (s0, a0) := round Loop.State.empty (Loop.allIds r.st.host) []
  r := note r s!"G17 round 0 over every live id ({(Loop.allIds r.st.host).length}): launch exactly the grain" (a0 == launchA)
  let (s1, a1) := round s0 [gr] []
  r := note r "G17 touched again before its report: nothing (the launch marks it running)" a1.isEmpty
  let (s2, a2) := round s1 [] [.started hx 10]
  r := note r "G17 started: nothing" a2.isEmpty
  let (s3, a3) := round s2 [] [.exited hx 0 20]
  r := note r "G17 exited while it desires running: relaunched" (a3 == launchA)
  let (s4, a4) := round s3 [] [.failed hx .programOutside 30]
  let (s5, a5) := round s4 [] [.failed hx .programOutside 40]
  let (s6, a6) := round s5 [] [.failed hx .programOutside 50]
  let (_, a7) := round s6 [] [.failed hx .programOutside 60]
  let (sx, ax) := round Loop.State.empty [] [.started (lit "stranger") 1]
  let (_, ay) := round Loop.State.empty [gr] [.started hx 1]
  r := note r "G17 a report for a grain this process never launched is ignored (a stranger's `started` neither stops the grain's launch nor stays in memory)"
    (ax.isEmpty && sx.live.isEmpty && sx.launched.isEmpty && ay == launchA)
  r := note r "G17 failed launches are exits: relaunched three times, then refused crashLoop"
    (a4 == launchA && a5 == launchA && a6 == launchA &&
      a7 == [{ grain := hx, verdict := .refuse .crashLoop }])
  let some lookBytes := lookAlike.bind Wire.encodePackage | return note r "G15 no look-alike bytes" false
  let (rl, vl, tl) := go prog r (call r a [a.id] (.install lookBytes))
  let some lp := created tl | return note rl s!"G15 look-alike install: {vl}" false
  let (rl2, _, tl2) := go prog rl (call rl a [a.id, lp] (.create (some lp) [] seedA))
  let some lg := created tl2 | return note rl2 "G15 look-alike create" false
  let (rl3, vl3, _) := go prog rl2 (call rl2 a [a.id, lg, lp] (.invoke lg Event.start.index args 100000 none))
  r := rl3
  let lhx := (Lang.Print.hex (Kernel.Sim.dc.bytes lg)).toUTF8
  r := note r s!"G15 a started look-alike ({vl3}, phase {phaseName (phaseAt r.st.host lg)}) is never launched"
    (vl3 == "admitted" && phaseAt r.st.host lg == some .running && (ctl r [] lg lhx).isEmpty)
  let (r12a, v12a, _) := ev r a .stop none
  let (r12, v12, _) := ev r12a a .remove none
  r := check r12 s!"G12 A stops ({v12a}) and removes" .admitted v12 (some .removed)
  r := note r "G16 controller, removed grain with a running child: kill"
    (ctl r [upLive hx] gr hx == [{ grain := hx, verdict := .kill }])
  let (r13, v13, _) := ev r a .start none
  r := check r13 "G13 A starts a removed grain" (.law "phase: no edge") v13 (some .removed)
  match World.fold Kernel.Sim.env g0 r.st.log with
  | .ok w => r := note r s!"G14 the follower reaches the Host's World ({r.st.log.length} turns)" (Kernel.Sim.same w r.st.host)
  | .error (i, e) => r := note r s!"G14 follower refused at {i}: {Kernel.Sim.nameOf e}" false
  match audit X g0 r.st.log with
  | .ok w => r := note r "G14 the auditor reaches the Host's World" (Kernel.Sim.same w r.st.host)
  | .error (i, e) => r := note r s!"G14 auditor refused at {i}: {reprStr e}" false
  return r

/-- G0: the shipped text is the generated one. -/
def textLine : IO (String × Bool) := do
  let some want := lifecycle.bind Lang.Print.package | return ("G0 the grain package has no text", false)
  let have_ ← try IO.FS.readFile textPath catch _ => pure ""
  if have_ == want then return (s!"G0 {textPath} is the generated text ({want.length} bytes)", true)
  return (s!"G0 {textPath} differs from Lang.Print.package lifecycle (hosting-sim --write-text rewrites it)", false)

end Nanodregg.Hosting.Sim
