/-
# Hosting.Sim.Allowance — the operator's allowances through KERNEL's receivers, read as the broker reads them

Two founders: A (the operator, who owns the allowances) and B (another member). Every line drives
the REAL receive path (`Receive.submit`, `Lang.program`), then reads the World with
`Allow.allowanceOf` (owner = A) and decides asks with `Broker.decide` over `Broker.follow`, as
`hosting-broker` does.

* A0 `world/hosting/Allowance` is the generated text (`Lang.Print.package allowance`), byte for byte.
* A1 A installs the allowance package; its id is `Allow.allowanceId`.
* A2 A creates an allowance for resident `R` on model `claude-m`; the broker reads it.
* A3 B creates a look-alike allowance (same package, B owns it) for `R` on `m`: admitted by the World,
  never read (owner ≠ operator), so the broker's allowance stays A's alone.
* A4 B invokes `set` on A's allowance: refused `noGrant` (KERNEL-25).
* A5 A writes its allowance's state: refused `hasMethods` (a programmed object changes only by method).
* A6 A `set`s cap 9000: read with the new cap, model and resident kept. A broker life that held the
  old allowance follows the change: the changed allowance is a new budget, so an ask in the window
  of the change is `overSpend` (HOSTING-13), and in the next window it is granted.
* A7 A creates a second allowance for `R` on `m`: an ask is refused `allowanceAmbiguous`.
* A8 A revokes the second: it reads as nothing, and the ask is granted again on the first, whose
  meter the second's coming and going did not touch.
* A9 A `set`s the revoked one: admitted, still revoked, still not read.
-/
import Hosting.Sim.Journey
import Hosting.Allowance

namespace Nanodregg.Hosting.Sim.Allowance

open Nanodregg.Kernel Nanodregg.Kernel.Receive Nanodregg.Lang
open Nanodregg.Hosting Nanodregg.Hosting.Sim

def textPath : System.FilePath := "world" / "hosting" / "Allowance"

/-- The allowance package's surface source (LANG-50): the core text is written from it. -/
def sourcePath : System.FilePath := "world" / "hosting" / "Allowance.ob"

def resident : ByteArray := "resident-R".toUTF8
def alw : Broker.Allowance := ⟨"claude-m".toUTF8, 7, 1000, 60000, 5000, 100⟩

/-- Every allowance the operator holds in the World, as the broker reads it. -/
def readAll (w : World D) (pkgId operator : ByteArray) : List (ByteArray × Broker.Allowance) :=
  (Loop.allIds w).filterMap fun i => (w.live Kernel.Sim.env i).bind (Allow.allowanceOf pkgId operator)

def ask : Broker.Ask := ⟨"claude-m".toUTF8, 10, .empty, ⟨#[0]⟩, ["hi".toUTF8]⟩

def verdict : Except Broker.Refusal (Broker.Broker × Broker.Grant) → String
  | .ok (_, g) => s!"granted {g.charged}"
  | .error r => r.name

def journey : Run := Id.run do
  let fk : List (ByteArray × ByteArray) := [("f0".toUTF8, "f0-next".toUTF8), ("f1".toUTF8, "f1-next".toUTF8)]
  let X := Kernel.Sim.ctxWith langProgram
  let g0 ← match genesis X Kernel.Sim.worldName (Kernel.Sim.nonceOf 0) 100000000 (fk.map fun (k, n) => (k, nextKeyDigest X n)) with
    | .ok g => pure g
    | .error e =>
        return note { st := { rng := ⟨1⟩, host := World.genesis X.env 0 0, members := [] } } s!"A genesis refused {e.name}" false
  let members := fk.zipIdx.map fun ((k, n), i) => (⟨founderId X g0.origin i, k, n⟩ : Kernel.Sim.Member)
  let mut r : Run := { st := { rng := ⟨1⟩, host := g0, members } }
  let a := members.headD ⟨0, .empty, .empty⟩
  let b := members.getD 1 ⟨0, .empty, .empty⟩
  let call := fun (r : Run) (m : Kernel.Sim.Member) (ids : List D) (body : Body D) =>
    Kernel.Sim.signed r.st m m.key (Kernel.Sim.S.pinsFor r.st.host ids) body
  let prog := langProgram
  let operator := Kernel.Sim.dc.bytes a.id
  let some pkgBytes := Wire.encodePackage Allow.allowance | return note r "A1 the package has no bytes" false
  let some seedR := Allow.seed resident alw | return note r "A2 no seed" false
  let some noArgs := Allow.noArgs | return note r "A8 no argument bytes" false
  let some setArgs := Allow.setArgs { alw with cap := 9000 } | return note r "A6 no argument bytes" false
  let (r1, v1, t1) := go prog r (call r a [a.id] (.install pkgBytes))
  r := r1
  let some p := created t1 | return note r s!"A1 no package id ({v1})" false
  r := note r s!"A1 A installs the allowance package: {v1}"
    (v1 == "admitted" && Allow.allowanceId Kernel.Sim.env == some p)
  let pkgId := Kernel.Sim.dc.bytes p
  let reads := fun (r : Run) => readAll r.st.host pkgId operator
  let rn := Controller.dirOf resident
  let (r2, v2, t2) := go prog r (call r a [a.id, p] (.create (some p) [] seedR))
  r := r2
  let some al := created t2 | return note r s!"A2 no allowance id ({v2})" false
  r := note r s!"A2 A creates an allowance: {v2}" (v2 == "admitted" && reads r == [(rn, alw)])
  let (r3, v3, _) := go prog r (call r b [b.id, p] (.create (some p) [] seedR))
  r := r3
  r := note r s!"A3 B creates a look-alike for the same resident and model: {v3}; never read"
    (v3 == "admitted" && reads r == [(rn, alw)])
  let (r4, v4, _) := go prog r (call r b [b.id, al, p] (.invoke al Allow.setIndex setArgs 100000 none))
  r := note r4 s!"A4 B sets A's allowance: {v4}" (v4 == "refused noGrant" && reads r4 == [(rn, alw)])
  let (r5, v5, _) := go prog r (call r a [a.id, al] (.write al [(0, some (Lang.Print.hex resident).toUTF8)] none))
  r := note r5 s!"A5 A writes its allowance's state: {v5}" (v5 == "refused hasMethods")
  let b5 := Broker.Broker.start 0 [7] (reads r)
  let (r6, v6, _) := go prog r (call r a [a.id, al, p] (.invoke al Allow.setIndex setArgs 100000 none))
  r := r6
  r := note r s!"A6 A sets cap 9000: {v6}" (v6 == "admitted" && reads r == [(rn, { alw with cap := 9000 })])
  let b6 := b5.follow 60000 (reads r)
  let d6 := Broker.decide b6 60000 rn ask
  let d6' := Broker.decide b6 120000 rn ask
  r := note r s!"A6 a broker that held the old allowance follows the change: ask in that window {verdict d6}, in the next {verdict d6'}"
    (verdict d6 == "overSpend" && (verdict d6').startsWith "granted")
  let (r7, v7, t7) := go prog r (call r a [a.id, p] (.create (some p) [] seedR))
  r := r7
  let some al2 := created t7 | return note r s!"A7 no second allowance ({v7})" false
  let b7 := b6.follow 120000 (reads r)
  let d7 := Broker.decide b7 120000 rn ask
  r := note r s!"A7 A creates a second allowance for the same resident and model: {v7}; an ask: {verdict d7}"
    (v7 == "admitted" && verdict d7 == "allowanceAmbiguous")
  let (r8, v8, _) := go prog r (call r a [a.id, al2, p] (.invoke al2 Allow.revokeIndex noArgs 100000 none))
  r := r8
  let b8 := b7.follow 120000 (reads r)
  let d8 := Broker.decide b8 120000 rn ask
  r := note r s!"A8 A revokes the second: {v8}; the ask: {verdict d8}"
    (v8 == "admitted" && reads r == [(rn, { alw with cap := 9000 })] && (verdict d8).startsWith "granted")
  let (r9, v9, _) := go prog r (call r a [a.id, al2, p] (.invoke al2 Allow.setIndex setArgs 100000 none))
  r := r9
  let revokedNow := (r.st.host.live Kernel.Sim.env al2).bind fun c => Allow.boolAt c.slots 6
  r := note r s!"A9 A sets the revoked one: {v9}; revoked {revokedNow}, still not read"
    (v9 == "admitted" && revokedNow == some true && reads r == [(rn, { alw with cap := 9000 })])
  return r

/-- A0: the shipped text is the generated one. -/
def textLine : IO (String × Bool) := do
  let some want := Lang.Print.package Allow.allowance | return ("A0 the allowance package has no text", false)
  let have_ ← try IO.FS.readFile textPath catch _ => pure ""
  if have_ == want then return (s!"A0 {textPath} is the generated text ({want.length} bytes)", true)
  return (s!"A0 {textPath} differs from Lang.Print.package allowance (hosting-sim --write-text rewrites it)", false)

/-- A0s: the surface source lowers to exactly the shipped core; `revoke` flipped is caught. -/
def sourceLine : IO (String × Bool) := do
  let src ← try IO.FS.readFile sourcePath catch _ => pure ""
  let core ← try IO.FS.readFile textPath catch _ => pure ""
  return Lang.Surface.shippedRow "A0s" src core Allow.allowance ("(revoked true)", "(revoked false)")

/-- The core text, written from the surface source through the lowering. -/
def writeText : IO Bool := do
  let src ← try IO.FS.readFile sourcePath catch _ => pure ""
  let some t := Lang.Surface.coreText src | return false
  IO.FS.createDirAll (textPath.parent.getD ".")
  IO.FS.writeFile textPath t
  IO.println s!"wrote {textPath}"
  return true

end Nanodregg.Hosting.Sim.Allowance
