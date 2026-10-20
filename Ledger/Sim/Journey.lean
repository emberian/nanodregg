/-
# Ledger.Sim.Journey — the escrow through KERNEL's receivers, with its plants

`lake exe ledger-sim` drives the REAL receive path (`Receive.submit`: the receivers, then
`World.admit`) with `Lang.program` as the kernel's `Program`, under the Sim's toy parameters. Four
founders: A (the arbiter, who creates the escrow and so owns it), P (the depositor, who issues the
denomination), B (the beneficiary), Z (a stranger).

* E0 `world/escrow/Escrow` is the generated text (`Lang.Print.package escrow`), byte for byte, and
  reads back as the package (`ledger-sim --write-text` rewrites it).
* E1 P issues a denomination (its well) and mints 100 into its own account.
* E2 A installs the package; E3 A creates an escrow of 30 for B; E3b one born `held` is refused
  `lawDenied` (`notOpen`).
* E4 Z opens the escrow's account (`account asset e`, owner the escrow object) and B's.
* E5 A grants P `invoke 0` (deposit) and `invoke 2` (release), B `invoke 1` (refund), Z `invoke 2`.
* E6 an UNFUNDED deposit (the grant named is not P's grant to the escrow): the whole call is
  refused, the phase stays `open`, no balance moves.
* E7 P grants the escrow object `transfer 30` on P's account: exactly the deposit, so the kernel, not
  the package text, bounds what the deposit can move (KERNEL-60, LEDGER-16).
* E8 P deposits through it: admitted; `held`; the escrow holds 30, P 70.
* E9 a second deposit: `notOpen`. E10 Z releases through A's grant: `notParty` (the law checks the
  signer; KERNEL's grant let it reach the law).
* E11 P releases: admitted; `released`; B holds 30, the escrow 0.
* E12 TOP-UP: P transfers 30 into the escrow's account (anyone may pay into it): admitted.
* E13 P releases again: `settled`. E14 B refunds: `settled`. The escrow still holds 30, B 30.
* E15 the follower (`World.fold`) and the auditor reach the Host's World.

Plants (each must flip its lines, or the run is RED):
* skip-judge (the judge admits everything): E3b admitted; E9 is the kernel's `transferSpent` (the
  grant lent exactly one deposit and E8 spent it; the deposit's once key would refuse it next); E10 admitted (Z pays B: the parties are the law's); E13 and E14 are refused
  `spent` (the ONE payout nullifier: the kernel's second line holds without the law).
* two-keys + skip-judge (refund spends `"refund"`, not `"payout"`, AND no law): E14 is ADMITTED,
  the escrow pays twice (B by release, P by refund): the shared key is what the second line needs.
* drop-calls (a method's calls never reach the kernel): E6's unfunded deposit is ADMITTED, so the
  escrow is `held` with nothing in it (E8 is then `notOpen`); E11's release is admitted and moves
  nothing.
* short-cap (P's grant lends one less than the deposit moves: the package asking for `amount + 1` of
  what it was lent): E8 is refused `transferSpent`, the escrow stays `open` and empty (KERNEL-60).

Deterministic: a SEED argument changes nothing. It ends `ALL PASS`.
-/
import Kernel.Sim
import Lang.Program
import Lang.Print
import Lang.Read
import Lang.Surface
import Ledger.Escrow

namespace Nanodregg.Ledger.Sim

open Nanodregg.Kernel Nanodregg.Kernel.Receive Nanodregg.Lang
open Nanodregg.Ledger.Escrow
abbrev D := Kernel.Sim.D

def textPath : System.FilePath := "world" / "escrow" / "Escrow"

/-- The escrow package's surface source (LANG-50): the core text is written from it. -/
def sourcePath : System.FilePath := "world" / "escrow" / "Escrow.ob"

/-- E0s: the surface source lowers to exactly the shipped core; one flipped reason is caught. -/
def sourceLine : IO (String × Bool) := do
  let src ← try IO.FS.readFile sourcePath catch _ => pure ""
  let core ← try IO.FS.readFile textPath catch _ => pure ""
  return Surface.shippedRow "E0s" src core escrow ("\"notOpen\")", "\"notHeld\")")

def langProgram : Program D := Lang.program Kernel.Sim.dc.bytes Kernel.Sim.digestOf
def skipJudge : Program D := { langProgram with judge := fun _ _ _ _ _ _ => .ok () }
def dropCalls : Program D :=
  { langProgram with run := fun look rv p s m a r b => (langProgram.run look rv p s m a r b).map fun x => (x.1, [], x.2.2) }

/-- The plant package: `refund` spends its own key, so the two payouts are two nullifiers. -/
def twoKeys : Package :=
  Std.pkgOf stateTy [("escrow", law)] (methods.map fun (ℓ, A, ks, t) =>
    if ℓ = "refund" then
      (ℓ, A, ks, .lam (.record []) (.lam stateTy (.lam unit (.lam reqTy (resultT
        (callsT [someCallT T (transferT (ofT (rq "self")) (ofT (st "depositor")) noneD (someB (.bytes "refund".toUTF8)))])
        (.record (keep "refunded")))))))
    else (ℓ, A, ks, t))

inductive Mode | honest | skipJudge | twoKeys | dropCalls | shortCap
  deriving DecidableEq

def Mode.name : Mode → String
  | .honest => "honest" | .skipJudge => "PLANT skip-judge" | .twoKeys => "PLANT two-keys+skip-judge"
  | .dropCalls => "PLANT drop-calls" | .shortCap => "PLANT short-cap"

def Mode.program : Mode → Program D
  | .honest | .shortCap => langProgram
  | .skipJudge | .twoKeys => Sim.skipJudge
  | .dropCalls => Sim.dropCalls

def Mode.package : Mode → Package
  | .twoKeys => Sim.twoKeys
  | _ => escrow

structure Run where
  st : Kernel.Sim.State
  log : List String := []
  bad : Nat := 0

def note (r : Run) (line : String) (good : Bool) : Run :=
  { r with log := r.log ++ [s!"{if good then "ok  " else "FAIL"} {line}"], bad := r.bad + (if good then 0 else 1) }

def go (prog : Program D) (r : Run) (c : Call D) : Run × String × Option (Turn D) :=
  let X := Kernel.Sim.ctxWith prog
  let st := r.st
  match Receive.submit X st.host c with
  | .error (.refused e) => (r, s!"refused {Kernel.Sim.nameOf e} {reprStr e}", none)
  | .error (.rejected e) => (r, s!"rejected {Kernel.Sim.nameOf e}", none)
  | .ok (t, w') => ({ r with st := { st with host := w', log := st.log ++ [.turn t] } }, "admitted", some t)

/-- Refused by the kernel under name `n`, at its receivers or at `World.admit`. -/
def refusedAs (v n : String) : Bool := v.startsWith s!"refused {n} " || v == s!"rejected {n}"

def deniedWith (v why : String) : Bool := v.startsWith "refused lawDenied" && (v.splitOn why).length > 1

def balanceAt (w : World D) (id : D) : Option Int :=
  (w.live Kernel.Sim.env id).bind fun c => (c.slots.get Value.balanceKey).bind Value.balanceOf

def phaseAt (w : World D) (id : D) : Option Label :=
  (w.live Kernel.Sim.env id).bind fun c => Escrow.phaseOf c.slots

def lit (s : String) : D := Kernel.Sim.fnv s.toUTF8

/-- E0: the shipped text is the generated one, and it reads back as the package. -/
def textLine : IO (String × Bool) := do
  let some want := Print.package escrow | return ("E0 the escrow package has no text", false)
  let have_ ← try IO.FS.readFile textPath catch _ => pure ""
  let reads := match Read.readPackage have_ with
    | .ok q => Wire.encodePackage q == Wire.encodePackage escrow
    | .error _ => false
  if have_ == want && reads then
    return (s!"E0 {textPath} is the generated text ({want.length} bytes) and reads back as the package", true)
  return (s!"E0 {textPath} differs from Lang.Print.package escrow (ledger-sim --write-text rewrites it)", false)

def journey (mode : Mode) : Run := Id.run do
  let prog := mode.program
  let X := Kernel.Sim.ctxWith prog
  let keys : List (ByteArray × ByteArray) :=
    [("ka".toUTF8, "ka-next".toUTF8), ("kp".toUTF8, "kp-next".toUTF8), ("kb".toUTF8, "kb-next".toUTF8),
     ("kz".toUTF8, "kz-next".toUTF8)]
  let g ← match genesis X Kernel.Sim.worldName (Kernel.Sim.nonceOf 0) 100000000
      (keys.map fun (k, n) => (k, nextKeyDigest X n)) with
    | .ok g => pure g
    | .error e =>
      let r0 : Run := { st := { rng := ⟨1⟩, host := World.genesis X.env 0 0, members := [] } }
      return note r0 s!"{mode.name}: genesis refused {e.name}" false
  let members := keys.zipIdx.map fun ((k, n), i) => (⟨founderId X g.origin i, k, n⟩ : Kernel.Sim.Member)
  let mut r : Run := { st := { rng := ⟨1⟩, host := g, members } }
  r := note r s!"--- {mode.name}" true
  let a := members.headD ⟨0, .empty, .empty⟩
  let p := members.getD 1 ⟨0, .empty, .empty⟩
  let b := members.getD 2 ⟨0, .empty, .empty⟩
  let z := members.getD 3 ⟨0, .empty, .empty⟩
  let call := fun (r : Run) (m : Kernel.Sim.Member) (ids : List D) (body : Body D) =>
    go prog r (Kernel.Sim.signed r.st m m.key (Kernel.Sim.S.pinsFor r.st.host (m.id :: ids)) body)
  let bytesOf := Kernel.Sim.dc.bytes
  -- E1 the denomination and P's funds
  let (r1, v1, t1) := call r p [] (.issue 1000)
  let some w := t1.bind fun t => (createdIds t).head? | return note r1 s!"E1 issue: {v1}" false
  let acctP := accountId X p.id w
  let (r1, v1b, _) := call r1 p [w] (.account w p.id)
  let (r1, v1c, _) := call r1 p [w, acctP] (.transfer (.well w) (.of p.id w) 100 none none)
  r := note r1 s!"E1 P issues, opens its account, mints 100: {v1b}, {v1c}"
    (v1b == "admitted" && v1c == "admitted" && balanceAt r1.st.host acctP == some 100)
  -- E2 install
  let some pkgBytes := Wire.encodePackage mode.package | return note r "E2 the package has no bytes" false
  let (r2, v2, t2) := call r a [] (.install pkgBytes)
  r := note r2 s!"E2 A installs the escrow package: {v2}" (v2 == "admitted")
  let some pkg := t2.bind fun t => (createdIds t).head? | return note r "E2 no package id" false
  -- E3 create
  let terms : Terms := ⟨30, bytesOf a.id, bytesOf w, bytesOf b.id, bytesOf p.id, "escrow-1".toUTF8⟩
  let some seedOpen := seed terms | return note r "E3 no seed" false
  let some heldB := Wire.encodeData phaseTy (.inj "held" unitD) | return note r "E3 no phase bytes" false
  let seedHeld := seedOpen.set (stateBase + 6) heldB
  let (r3b, v3b, _) := call r a [pkg] (.create (some pkg) [] seedHeld)
  let (r3, v3, t3) := call r3b a [pkg] (.create (some pkg) [] seedOpen)
  let some e := t3.bind fun t => (createdIds t).head? | return note r3 s!"E3 create: {v3}" false
  r := note r3 s!"E3 A creates an escrow of 30 for B: {v3}, phase {phaseAt r3.st.host e}"
    (v3 == "admitted" && phaseAt r3.st.host e == some "open")
  if mode == .honest || mode == .dropCalls || mode == .shortCap then
    r := note r s!"E3b an escrow born held: {v3b}" (deniedWith v3b "notOpen")
  else
    r := note r s!"E3b an escrow born held, no law: {v3b}" (v3b == "admitted")
  let acctE := accountId X e w
  let acctB := accountId X b.id w
  -- E4 accounts
  let (r4, v4, _) := call r z [w, e] (.account w e)
  let (r4, v4b, _) := call r4 z [w] (.account w b.id)
  r := note r4 s!"E4 Z opens the escrow account and B's: {v4}, {v4b}" (v4 == "admitted" && v4b == "admitted")
  -- E5 grants of invoke
  let grantOf := fun (r : Run) (who : Kernel.Sim.Member) (m : Nat) =>
    call r a [e, who.id] (.grant e who.id [.invoke m] none)
  let (r5, v5a, t5a) := grantOf r p deposit
  let (r5, v5b, t5b) := grantOf r5 p release
  let (r5, v5c, t5c) := grantOf r5 b refund
  let (r5, v5d, t5d) := grantOf r5 z release
  let gid := fun (t : Option (Turn D)) => (t.bind fun t => (createdIds t).head?).getD 0
  let gDep := gid t5a
  let gRelP := gid t5b
  let gRefB := gid t5c
  let gRelZ := gid t5d
  r := note r5 s!"E5 A grants P deposit+release, B refund, Z release: {v5a} {v5b} {v5c} {v5d}"
    ([v5a, v5b, v5c, v5d].all (· == "admitted"))
  let pins := [pkg, e, w, acctP, acctE, acctB]
  let invoke := fun (r : Run) (m : Kernel.Sim.Member) (method : Nat) (args : ByteArray) (via : D) (extra : List D) =>
    call r m (pins ++ [via] ++ extra) (.invoke e method args 100000 (some via))
  -- E6 unfunded deposit: the grant named is P's grant of INVOKE from A, not of transfer to e
  let some argsBad := depositArgs (bytesOf gDep) | return note r "E6 no args" false
  let (r6, v6, _) := invoke r p deposit argsBad gDep [gDep]
  if mode == .dropCalls then
    -- without its call the deposit is admitted: the escrow is `held` with nothing in it
    r := note r6 s!"E6 an unfunded deposit, calls dropped: {v6}; phase {phaseAt r6.st.host e}, escrow {balanceAt r6.st.host acctE}"
      (v6 == "admitted" && phaseAt r6.st.host e == some "held" && balanceAt r6.st.host acctE == some 0)
  else
    r := note r6 s!"E6 an unfunded deposit: {v6}; phase {phaseAt r6.st.host e}, P {balanceAt r6.st.host acctP}"
      (v6.startsWith "refused" && phaseAt r6.st.host e == some "open" && balanceAt r6.st.host acctP == some 100 &&
        balanceAt r6.st.host acctE == some 0)
  -- E7 P lends the escrow object exactly the deposit out of its account (short-cap: one less)
  let cap := if mode == .shortCap then 29 else 30
  let (r7, v7, t7) := call r p [acctP, e] (.grant acctP e [.transfer cap] none)
  let gm := gid t7
  r := note r7 s!"E7 P grants the escrow transfer {cap} on its account: {v7}" (v7 == "admitted")
  -- E8 deposit
  let some argsDep := depositArgs (bytesOf gm) | return note r "E8 no args" false
  let (r8, v8, _) := invoke r p deposit argsDep gDep [gm]
  r := r8
  let held := phaseAt r.st.host e == some "held"
  if mode == .shortCap then
    return note r s!"E8 P deposits 30 through a grant of 29: {v8}; phase {phaseAt r.st.host e}, escrow {balanceAt r.st.host acctE}"
      (refusedAs v8 "transferSpent" && phaseAt r.st.host e == some "open" && balanceAt r.st.host acctE == some 0)
  if mode == .dropCalls then
    r := note r s!"E8 deposit, calls dropped (already held by E6): {v8}; escrow {balanceAt r.st.host acctE}"
      (deniedWith v8 "notOpen" && held && balanceAt r.st.host acctE == some 0)
  else
    r := note r s!"E8 P deposits: {v8}; held {held}, escrow {balanceAt r.st.host acctE}, P {balanceAt r.st.host acctP}"
      (v8 == "admitted" && held && balanceAt r.st.host acctE == some 30 && balanceAt r.st.host acctP == some 70)
  -- E9 deposit again
  let (r9, v9, _) := invoke r p deposit argsDep gDep [gm]
  r := r9
  match mode with
  | .honest | .dropCalls => r := note r s!"E9 a second deposit: {v9}" (deniedWith v9 "notOpen")
  | _ => r := note r s!"E9 a second deposit, no law: the grant's cap is spent: {v9}" (refusedAs v9 "transferSpent")
  -- E10 the stranger through A's grant
  let some noA := noArgs | return note r "E10 no args" false
  let (r10, v10, _) := invoke r z release noA gRelZ []
  if mode == .honest || mode == .dropCalls then
    r := note r10 s!"E10 Z releases through A's grant: {v10}" (deniedWith v10 "notParty")
  else
    -- without the law Z's release is admitted and pays B: the parties are the law's
    r := note r10 s!"E10 Z releases, no law: {v10}" (v10 == "admitted")
  -- E11 release (in the plants without a law Z already released)
  let (r11, v11, _) := invoke r p release noA gRelP []
  if mode == .honest then
    r := note r11 s!"E11 P releases: {v11}; {phaseAt r11.st.host e}, B {balanceAt r11.st.host acctB}, escrow {balanceAt r11.st.host acctE}"
      (v11 == "admitted" && phaseAt r11.st.host e == some "released" && balanceAt r11.st.host acctB == some 30 &&
        balanceAt r11.st.host acctE == some 0)
  else if mode == .dropCalls then
    r := note r11 s!"E11 P releases, calls dropped: {v11}; B {balanceAt r11.st.host acctB}"
      (v11 == "admitted" && balanceAt r11.st.host acctB == some 0)
  else
    -- the account Z's release emptied: the floor refuses first, until the top-up
    r := note r11 s!"E11 P releases after Z did, no law: {v11}" (refusedAs v11 "belowFloor")
  -- E12 top-up
  let (r12, v12, _) := call r p [acctP, acctE, w] (.transfer (.of p.id w) (.of e w) 30 none none)
  r := note r12 s!"E12 P tops the escrow up by 30: {v12}; escrow {balanceAt r12.st.host acctE}"
    (v12 == "admitted" && balanceAt r12.st.host acctE == some 30)
  -- E13 release again, E14 refund
  let (r13, v13, _) := invoke r p release noA gRelP []
  r := r13
  let (r14, v14, _) := invoke r b refund noA gRefB []
  r := r14
  match mode with
  | .honest =>
    r := note r s!"E13 P releases again: {v13}" (deniedWith v13 "settled")
    r := note r s!"E14 B refunds after the release: {v14}; escrow {balanceAt r.st.host acctE}, B {balanceAt r.st.host acctB}"
      (deniedWith v14 "settled" && balanceAt r.st.host acctE == some 30 && balanceAt r.st.host acctB == some 30)
  | .skipJudge =>
    r := note r s!"E13 release again, no law: the kernel's one payout nullifier: {v13}" (refusedAs v13 "spent")
    r := note r s!"E14 refund, no law: the same nullifier: {v14}" (refusedAs v14 "spent")
  | .twoKeys =>
    r := note r s!"E13 release again, no law: {v13}" (refusedAs v13 "spent")
    r := note r s!"E14 refund under its own key, no law: PAID TWICE: {v14}; escrow {balanceAt r.st.host acctE}"
      (v14 == "admitted" && balanceAt r.st.host acctE == some 0)
  | .dropCalls =>
    r := note r s!"E13 release again, calls dropped: {v13}" (deniedWith v13 "settled")
    r := note r s!"E14 refund, calls dropped: {v14}" (deniedWith v14 "settled")
  | .shortCap => pure ()  -- unreachable: the short-cap run ends at E8
  -- E15 follower and auditor
  match World.fold Kernel.Sim.env g r.st.log with
  | .ok w' => r := note r s!"E15 the follower reaches the Host's World ({r.st.log.length} turns)" (Kernel.Sim.same w' r.st.host)
  | .error (i, e) => r := note r s!"E15 follower refused at {i}: {Kernel.Sim.nameOf e}" false
  match audit X g r.st.log with
  | .ok w' => r := note r "E15 the auditor reaches the Host's World" (Kernel.Sim.same w' r.st.host)
  | .error (i, e) => r := note r s!"E15 auditor refused at {i}: {reprStr e}" false
  return r

def runAll (args : List String) : IO UInt32 := do
  if args == ["--write-text"] then
    -- the core text is written from the surface source, through the lowering (LANG-50)
    let src ← IO.FS.readFile sourcePath
    let some t := Surface.coreText src | IO.eprintln s!"{sourcePath} does not lower"; return 1
    IO.FS.createDirAll (textPath.parent.getD ".")
    IO.FS.writeFile textPath t
    IO.println s!"wrote {textPath}"
    return 0
  -- `--harness-control` (GATES-15): one line nothing meets, counted on the ordinary path
  let control := args.contains "--harness-control"
  let args := args.filter (· != "--harness-control")
  match args with
  | [] => pure ()
  | [seed] =>
    match seed.toNat? with
    | some n => IO.println s!"seed {n}: the escrow journey is deterministic; the seed selects nothing"
    | none => IO.eprintln s!"usage: ledger-sim [SEED | --write-text] (got {seed})"; return 2
  | _ => IO.eprintln "usage: ledger-sim [SEED | --write-text]"; return 2
  let (l0, ok0) ← textLine
  IO.println s!"{if ok0 then "ok  " else "FAIL"} {l0}"
  let (ls, oks) ← sourceLine
  IO.println s!"{if oks then "ok  " else "FAIL"} {ls}"
  let runs := [Mode.honest, .skipJudge, .twoKeys, .dropCalls, .shortCap].map journey
  let runs := match control, runs with
    | true, r :: rest => note r "harness-control: GATES-15's known-red control, an expectation nothing meets (this run must read RED)" false :: rest
    | _, rs => rs
  for r in runs do for l in r.log do IO.println l
  let bad := runs.foldl (· + ·.bad) ((if ok0 then 0 else 1) + (if oks then 0 else 1))
  IO.println (if bad = 0 then "ALL PASS" else s!"ledger-sim: RED ({bad})")
  return if bad = 0 then 0 else 1

end Nanodregg.Ledger.Sim
