/-
# Lang.Journey — the first law end to end: install → create → invoke through KERNEL's receivers

`lake exe lang-journey` drives the REAL receive path (`Receive.submit` = `receive` then
`World.admit`) with `Lang.program` as the kernel's `Program`, under the Sim's toy parameters
(UInt64 digest, FNV hash, toy signatures: memory "toy parameters in the real pipeline"). The
package `Owned` keeps `{owner : bytes, total : nat}`; its method `set n` writes `total := n`; its
laws are `bounded` (`new.total ≤ 100`, else "over 100") and `ownerOnly` (the SIGNING member must be
the owner and the owner never changes). Rows:

* L0 the text form of `Owned` (`Lang.Read`, what a resident writes) reads to the same bytes.
* L1 founder A installs `Owned` (a ROM cell, id `romIdOf`) — admitted.
* L2 A creates an object owned by A, seed `{owner = A, total = 0}`, judged by both laws — admitted.
* L3 A invokes `set 50` — admitted; the object's `total` slot decodes to 50.
* L4 A invokes `set 101` — refused `lawDenied` by `bounded`, nothing written.
* L5 B, holding A's grant to invoke method 0 (so the kernel's authority check passes with principal
  A), invokes `set 7` — refused `lawDenied` by `ownerOnly`: a law can be stricter than authority.
* L6 a package whose body does not check at its interface — refused `program` at install.
* L7 the follower (`World.fold` from genesis) and the auditor reach the Host's World.
* PLANT: the Sim.same rows against a program whose `judge` admits everything: L4 must be ADMITTED
  there (the row flips), proving the refusal in L4 came from the law, not from elsewhere.
-/
import Kernel.Sim
import Lang.Program
import Lang.Read

namespace Nanodregg.Lang.Journey

open Nanodregg.Kernel Nanodregg.Kernel.Receive
abbrev D := Sim.D

def S : Ty := .record [("owner", .bytes), ("total", .nat)]

def ok : Term := .inj verdictTy "ok" (.record [])
def refused (why : String) : Term := .inj verdictTy "refused" (.bytes why.toUTF8)

/-- Under `lam S (lam S (lam reqTy _))`: var 2 = old, var 1 = new, var 0 = req. -/
def law3 (body : Term) : Term := .lam S (.lam S (.lam reqTy body))

def bounded : Term :=
  law3 (.ite (.prim .le (.get (.var 1) "total") (.nat 100)) ok (refused "over 100"))

def ownerOnly : Term :=
  law3 (.ite (.prim .beq (.get (.var 0) "agent") (.get (.var 1) "owner"))
    (.ite (.prim .beq (.get (.var 2) "owner") (.get (.var 1) "owner")) ok (refused "owner changed"))
    (refused "not the owner"))

/-- `set state n req = {owner = state.owner, total = n}` -/
def setM : Term :=
  .lam S (.lam .nat (.lam reqTy (.record [("owner", .get (.var 2) "owner"), ("total", .var 1)])))

def iface : Ty :=
  .record [("bounded", lawTy S), ("ownerOnly", lawTy S), ("set", methodTy S .nat)]

def owned : Package :=
  { imports := [], state := S, iface,
    body := .record [("bounded", bounded), ("ownerOnly", ownerOnly), ("set", setM)],
    methods := ["set"], laws := ["bounded", "ownerOnly"] }

/-- The Sim.same package with a body that does not check at its interface (`set` returns a nat). -/
def illTyped : Package :=
  { owned with body := .record [("bounded", bounded), ("ownerOnly", ownerOnly),
      ("set", .lam S (.lam .nat (.lam reqTy (.var 1))))] }

/-- `Owned`, as a resident writes it (Lang.Read): must read to exactly the package above. -/
def ownedText : String := "
(package (imports)
  (state (rec (owner bytes) (total nat)))
  (iface (rec (set (-> (rec (owner bytes) (total nat))
                    (-> nat (-> (rec (agent bytes) (notBefore nat) (principal bytes) (validUntil nat))
                                (rec (owner bytes) (total nat))))))
              (bounded (-> (rec (owner bytes) (total nat)) (-> (rec (owner bytes) (total nat))
                (-> (rec (agent bytes) (notBefore nat) (principal bytes) (validUntil nat))
                    (sum (ok (rec)) (refused bytes))))))
              (ownerOnly (-> (rec (owner bytes) (total nat)) (-> (rec (owner bytes) (total nat))
                (-> (rec (agent bytes) (notBefore nat) (principal bytes) (validUntil nat))
                    (sum (ok (rec)) (refused bytes))))))))
  (methods set)
  (laws bounded ownerOnly)
  (body
    (record
      (set (fn (s (rec (owner bytes) (total nat))) (n nat)
               (r (rec (agent bytes) (notBefore nat) (principal bytes) (validUntil nat)))
             (record (owner (. s owner)) (total n))))
      (bounded (fn (old (rec (owner bytes) (total nat))) (new (rec (owner bytes) (total nat)))
                   (r (rec (agent bytes) (notBefore nat) (principal bytes) (validUntil nat)))
                 (if (<= (. new total) 100)
                     (inj (sum (ok (rec)) (refused bytes)) ok (record))
                     (inj (sum (ok (rec)) (refused bytes)) refused \"over 100\"))))
      (ownerOnly (fn (old (rec (owner bytes) (total nat))) (new (rec (owner bytes) (total nat)))
                     (r (rec (agent bytes) (notBefore nat) (principal bytes) (validUntil nat)))
                   (if (beq (. r agent) (. new owner))
                       (if (beq (. old owner) (. new owner))
                           (inj (sum (ok (rec)) (refused bytes)) ok (record))
                           (inj (sum (ok (rec)) (refused bytes)) refused \"owner changed\"))
                       (inj (sum (ok (rec)) (refused bytes)) refused \"not the owner\")))))))
"

/-- A u64 argument or slot (`none` past `2^64`). -/
def nat64 (n : Nat) : Option ByteArray := Wire.encodeData .nat (.nat n)

def ctxWith (prog : Program D) : Ctx D := Sim.ctxWith prog

def langProgram : Program D := Lang.program Sim.dc.bytes Sim.digestOf

/-- The plant: a program whose judge admits every write. -/
def skipJudge : Program D := { langProgram with judge := fun _ _ _ _ _ _ => .ok () }

structure Run where
  st : Sim.State
  log : List String := []
  bad : Nat := 0

def note (r : Run) (line : String) (good : Bool) : Run :=
  { r with log := r.log ++ [s!"{if good then "ok  " else "FAIL"} {line}"], bad := r.bad + (if good then 0 else 1) }

/-- Submit on the Host path with program `prog`; the verdict's name. -/
def go (prog : Program D) (r : Run) (c : Call D) : Run × String × Option (Turn D) :=
  let X := ctxWith prog
  let st := r.st
  match Receive.submit X st.host c with
  | .error (.refused e) => ({ r with st }, s!"refused {Sim.nameOf e} {reprStr e}", none)
  | .error (.rejected e) => ({ r with st }, s!"rejected {Sim.nameOf e}", none)
  | .ok (t, w') => ({ r with st := { st with host := w', log := st.log ++ [t] } }, "admitted", some t)

def totalOf (w : World D) (obj : D) : Option Nat :=
  match w.live obj with
  | some cell => match cell.slots.get (stateBase + 1) with
    | some b => match Wire.decodeData .nat b with
      | .ok (.nat n) => some n
      | _ => none
    | none => none
  | none => none

def journey (prog : Program D) (plant : Bool) : Run := Id.run do
  let fk : List (ByteArray × ByteArray) :=
    [("f0".toUTF8, "f0-next".toUTF8), ("f1".toUTF8, "f1-next".toUTF8)]
  let X := ctxWith prog
  let g := genesis X Sim.worldName 100000000 (fk.map fun (k, n) => (k, nextKeyDigest X n))
  let members := fk.zipIdx.map fun ((k, n), i) => (⟨founderId X Sim.worldName i, k, n⟩ : Sim.Member)
  let mut r : Run := { st := { rng := ⟨1⟩, host := g, members } }
  let a := members.headD ⟨0, .empty, .empty⟩
  let b := members.getD 1 ⟨0, .empty, .empty⟩
  -- L0 the resident's text reads to exactly the package
  let some ownedBytes := Wire.encodePackage owned | return note r "L0 Owned has no bytes" false
  let some illBytes := Wire.encodePackage illTyped | return note r "L0 illTyped has no bytes" false
  match Read.readPackage ownedText with
  | .error e => r := note r s!"L0 read Owned: {e}" false
  | .ok q =>
    let same := Wire.encodePackage q == some ownedBytes
    r := note r "L0 read Owned from text: same bytes as the AST" same
  -- L1 install
  let c1 := Sim.signed r.st a a.key (Sim.S.pinsFor r.st.host [a.id]) (.install ownedBytes)
  let (r1, v1, t1) := go prog r c1
  r := note r1 s!"L1 install Owned: {v1}" (v1 == "admitted")
  let some pkg := t1.bind fun t => (createdIds Sim.env t).head? | return note r "L1 no package id" false
  -- L6 an ill-typed package
  let c6 := Sim.signed r.st a a.key (Sim.S.pinsFor r.st.host [a.id]) (.install illBytes)
  let (r6, v6, _) := go prog r c6
  r := note r6 s!"L6 install ill-typed: {v6}" (v6.startsWith "refused program")
  -- L2 create
  let some ownerBytes := Wire.encodeData .bytes (.bytes (Sim.dc.bytes a.id)) | return note r "L2 no owner bytes" false
  let some n0 := nat64 0 | return note r "L2 no bytes for 0" false
  let some n50 := nat64 50 | return note r "L3 no bytes for 50" false
  let some n101 := nat64 101 | return note r "L4 no bytes for 101" false
  let some n7 := nat64 7 | return note r "L5 no bytes for 7" false
  let seed : Slots := [(stateBase, ownerBytes), (stateBase + 1, n0)]
  let c2 := Sim.signed r.st a a.key (Sim.S.pinsFor r.st.host [a.id, pkg]) (.create (some pkg) [] seed)
  let (r2, v2, t2) := go prog r c2
  r := note r2 s!"L2 create object: {v2}" (v2 == "admitted")
  let some obj := t2.bind fun t => (createdIds Sim.env t).head? | return note r "L2 no object id" false
  -- L3 set 50
  let c3 := Sim.signed r.st a a.key (Sim.S.pinsFor r.st.host [a.id, obj, pkg]) (.invoke obj 0 n50 10000 none)
  let (r3, v3, _) := go prog r c3
  r := note r3 s!"L3 A set 50: {v3}, total = {totalOf r3.st.host obj}" (v3 == "admitted" && totalOf r3.st.host obj == some 50)
  -- L4 set 101
  let c4 := Sim.signed r.st a a.key (Sim.S.pinsFor r.st.host [a.id, obj, pkg]) (.invoke obj 0 n101 10000 none)
  let (r4, v4, _) := go prog r c4
  if plant then
    r := note r4 s!"PLANT skip-judge: L4 A set 101 must now be admitted: {v4}" (v4 == "admitted")
  else
    r := note r4 s!"L4 A set 101: {v4}, total = {totalOf r4.st.host obj}"
      (v4.startsWith "refused lawDenied" && (v4.splitOn "bounded: over 100").length > 1 && totalOf r4.st.host obj == some 50)
  -- L5 B through a grant
  let cg := Sim.signed r.st a a.key (Sim.S.pinsFor r.st.host [a.id, b.id, obj]) (.grant obj b.id [.invoke 0] none)
  let (rg, vg, tg) := go prog r cg
  r := note rg s!"L5a A grants B invoke 0: {vg}" (vg == "admitted")
  let some gr := tg.bind fun t => (createdIds Sim.env t).head? | return note r "L5 no grant id" false
  let c5 := Sim.signed r.st b b.key (Sim.S.pinsFor r.st.host [b.id, obj, pkg, gr]) (.invoke obj 0 n7 10000 (some gr))
  let (r5, v5, _) := go prog r c5
  unless plant do
    r := note r5 s!"L5 B (granted) set 7: {v5}" (v5.startsWith "refused lawDenied" && (v5.splitOn "ownerOnly: not the owner").length > 1)
  r := { r5 with log := r.log, bad := r.bad }
  -- L7 follower and auditor
  match World.fold Sim.env g r.st.log with
  | .ok w => r := note r s!"L7 follower reaches the Host's World ({r.st.log.length} turns)" (Sim.same w r.st.host)
  | .error (i, e) => r := note r s!"L7 follower refused at {i}: {Sim.nameOf e}" false
  match audit (ctxWith prog) g r.st.log with
  | .ok w => r := note r "L7 auditor reaches the Host's World" (Sim.same w r.st.host)
  | .error (i, e) => r := note r s!"L7 auditor refused at {i}: {reprStr e}" false
  return r

def runAll : IO UInt32 := do
  let honest := journey langProgram false
  let planted := journey skipJudge true
  for l in honest.log ++ planted.log do IO.println l
  let bad := honest.bad + planted.bad
  IO.println s!"lang-journey: {if bad = 0 then "GREEN" else s!"RED ({bad})"}"
  return if bad = 0 then 0 else 1

end Nanodregg.Lang.Journey
