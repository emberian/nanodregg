/-
# Lang.Journey — the first law end to end: install → create → invoke through KERNEL's receivers

`lake exe lang-journey` drives the REAL receive path (`Receive.submit` = `receive` then
`World.admit`) with `Lang.program` as the kernel's `Program`, under the Sim's toy parameters
(UInt64 digest, FNV hash, toy signatures: memory "toy parameters in the real pipeline"). The
package `Owned` keeps `{owner : bytes, total : nat}`; its method `set n` writes `total := n`; its
laws are `bounded` (`new.total ≤ 100`, else "over 100") and `ownerOnly` (the SIGNING member must be
the owner and the owner never changes). Rows:

* L0 the text form of `Owned` (`Lang.Read`, what a resident writes) reads to the same bytes.
* L0c `Lang.Print` gives `Owned` its text, which reads back to the same bytes; a non-atom label
  has no text; bytes that are not quote-free UTF-8 print as `#hex` and read back.
* L0d the reader's fuel counts nesting only: an allowlist at `Std.idsMax` ids prints and reads
  back; a list past `Read.listMax` is refused `tooLong`, a form past `Read.depthMax` `tooDeep`.
* L0e a binder named like a literal (`true`, `5`, `#ab`), a head word or a primitive is refused
  `reservedBinder`.
* L0f (LANG-31) one label rule, and the reader two levels past the wire: a package written as text
  with its body and interface nested to the wire's depth bound reads, checks, encodes, prints and
  reads back to the same bytes; one level deeper the reader refuses it `tooDeep`; a label with a
  space has no bytes.
* L1 founder A installs `Owned` (a ROM cell, id `romIdOf`) — admitted.
* L2 A creates an object owned by A, seed `{owner = A, total = 0}`, judged by both laws — admitted.
* L3 A invokes `set 50` — admitted; the object's `total` slot decodes to 50.
* L4 A invokes `set 101` — refused `lawDenied` by `bounded`, nothing written.
* L5 B invokes `set 7` through A's grant for method 0 (so the principal is A, the grant's root
  issuer) — refused `lawDenied` by `ownerOnly`, which checks the SIGNER: a law can be stricter than
  the principal.
* L6 a package whose body does not check at its interface — refused `program` at install.
* LI (LANG-35) install loads the import closure: `Mid` imports `Owned` and installs; `Top` imports
  `Mid`, and its install pinning only `Mid` is refused `unpinned` naming `Owned` (LI2: the check loads
  `Mid`'s own closure, so `Owned` must be pinned too); pinning both, it is admitted (LI3).
* L8 (ID-1) `Tally`'s law `fresh` cases on the occasion: a birth seeded with approvals is refused,
  a zero seed admitted.
* L8d/e the invoke's method index reaches the law: `fresh` closes method `b`, `a` passes.
* L9 (ID-1) `Frozen`, an extra law on a data object, refuses its own replacement; writes pass.
* L10 the relaw carries the incoming law ids: `OnlyTo [Frozen]` refuses a replacement by `[Tally]`
  and admits one by `[Frozen]`.
* L11 (KERNEL-27 `adopt`) `BirthOnly` admits a birth and refuses its adoption: an object may be
  born under it (L11b), and adding it to an existing object is refused (L11c) by the incoming law
  itself, which a birth-conflated occasion could not say. L11d: a relaw that KEEPS BirthOnly and adds
  Frozen is admitted, since only ADDED laws judge adopt (KERNEL-27).
* L7 the follower (`World.fold` from genesis) and the auditor reach the Host's World.
* PLANT skip-judge: the same rows against a program whose `judge` admits everything: L4 must be
  ADMITTED there (the row flips), proving the refusal in L4 came from the law, not from elsewhere.
* PLANT erase-occasion: the same rows against a program whose judge is told every act is a write
  (the judge before ID-1): L8b, L8e, L9d, L10c and L11c must be ADMITTED there, so their refusals came
  from the occasion.
* PLANT raw-install: the install check before LANG-35, each import's interface read raw from its
  cell and its closure never loaded: LI2 must be ADMITTED there, so its refusal came from the loader.
  That mode stops after LI2: the plant runs the rows before LI and LI2, not the rows after.
* PLANT erase-payload: the occasion's payload is lost (a relaw names no laws, every invoke is
  method 0): L8e must be admitted and L10d refused, so the payload reaches the law.
-/
import Kernel.Sim
import Lang.Program
import Lang.Print
import Lang.Resident
import Lang.Std

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
def setM : Term := Std.methodOf S .nat [("owner", .get (.var 2) "owner"), ("total", .var 1)]

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

/-- The request type as the resident pastes it (printed from `reqTy`, so it is never restated). -/
def rq : String := Print.tyText reqTy (by decide +kernel)

/-- `Owned`'s method result type and its empty calls row, printed from `resultTy` and `callsT`. -/
def ownedRes : String := Print.tyText (resultTy S) (by decide +kernel)
def noCalls : String := Print.noCallsText

/-- `Owned`, as a resident writes it (Lang.Read): must read to exactly the package above. -/
def ownedText : String := s!"
(package (imports)
  (state (rec (owner bytes) (total nat)))
  (iface (rec (set (-> (rec (owner bytes) (total nat))
                    (-> nat (-> {rq} {ownedRes}))))
              (bounded (-> (rec (owner bytes) (total nat)) (-> (rec (owner bytes) (total nat))
                (-> {rq}
                    (sum (ok (rec)) (refused bytes))))))
              (ownerOnly (-> (rec (owner bytes) (total nat)) (-> (rec (owner bytes) (total nat))
                (-> {rq}
                    (sum (ok (rec)) (refused bytes))))))))
  (methods set)
  (laws bounded ownerOnly)
  (body
    (record
      (set (fn (s (rec (owner bytes) (total nat))) (n nat)
               (r {rq})
             (record (calls {noCalls}) (state (record (owner (. s owner)) (total n))))))
      (bounded (fn (old (rec (owner bytes) (total nat))) (new (rec (owner bytes) (total nat)))
                   (r {rq})
                 (if (<= (. new total) 100)
                     (inj (sum (ok (rec)) (refused bytes)) ok (record))
                     (inj (sum (ok (rec)) (refused bytes)) refused \"over 100\"))))
      (ownerOnly (fn (old (rec (owner bytes) (total nat))) (new (rec (owner bytes) (total nat)))
                     (r {rq})
                   (if (beq (. r agent) (. new owner))
                       (if (beq (. old owner) (. new owner))
                           (inj (sum (ok (rec)) (refused bytes)) ok (record))
                           (inj (sum (ok (rec)) (refused bytes)) refused \"owner changed\"))
                       (inj (sum (ok (rec)) (refused bytes)) refused \"not the owner\")))))))
"

/-! ### The occasion rows (ID-1): a law that knows which act it judges

`Tally` keeps `{approvals : nat, total : nat}`; its law `fresh` refuses a birth whose seed carries
approvals and admits every other act. `Frozen` is a law package over a data object whose law
refuses any replacement of the laws and admits every other act. Without the occasion both were
unwritable: `create` judges the seed as `old = new`, and `law` judges the unchanged state, so each
looked like a no-op write. -/

def T : Ty := .record [("approvals", .nat), ("total", .nat)]

/-- Under `case req.occasion`, inside an arm: var 3 = old, var 2 = new, var 1 = req, var 0 = the
arm's payload. -/
def tallyFresh : Term :=
  .lam T (.lam T (.lam reqTy (.case (.get (.var 0) "occasion")
    [("adopt", ok), ("birth", .ite (.prim .eq (.get (.var 2) "approvals") (.nat 0)) ok (refused "seeded")),
     ("invoke", .ite (.prim .eq (.var 0) (.nat 1)) (refused "method b is closed") ok),
     ("relaw", ok), ("write", ok)])))

/-- `set state n req = {approvals = state.approvals, total = n}`, as both methods `a` and `b`. -/
def tallySet : Term := Std.methodOf T .nat [("approvals", .get (.var 2) "approvals"), ("total", .var 1)]

def tally : Package :=
  { imports := [], state := T,
    iface := .record [("a", methodTy T .nat), ("b", methodTy T .nat), ("fresh", lawTy T)],
    body := .record [("a", tallySet), ("b", tallySet), ("fresh", tallyFresh)],
    methods := ["a", "b"], laws := ["fresh"] }

def frozenLaw : Term :=
  .lam (.record []) (.lam (.record []) (.lam reqTy (.case (.get (.var 0) "occasion")
    [("adopt", ok), ("birth", ok), ("invoke", ok), ("relaw", refused "laws are frozen"), ("write", ok)])))

def frozen : Package :=
  { imports := [], state := .record [], iface := .record [("frozen", lawTy (.record []))],
    body := .record [("frozen", frozenLaw)], methods := [], laws := ["frozen"] }

/-- A law that may govern an object from its birth but refuses to be added to one later. -/
def birthOnly : Package :=
  let law := Term.lam (.record []) (.lam (.record []) (.lam reqTy (.case (.get (.var 0) "occasion")
    [("adopt", refused "only at birth"), ("birth", ok), ("invoke", ok), ("relaw", ok), ("write", ok)])))
  { imports := [], state := .record [], iface := .record [("birthOnly", lawTy (.record []))],
    body := .record [("birthOnly", law)], methods := [], laws := ["birthOnly"] }

/-- A law package admitting a replacement of the laws only by exactly the ids whose bytes are `to`. -/
def onlyTo (to : ByteArray) : Package :=
  let law := Term.lam (.record []) (.lam (.record []) (.lam reqTy (.case (.get (.var 0) "occasion")
    [("adopt", ok), ("birth", ok), ("invoke", ok),
     ("relaw", .ite (.prim .beq (.var 0) (.bytes to)) ok (refused "not the agreed laws")), ("write", ok)])))
  { imports := [], state := .record [], iface := .record [("onlyTo", lawTy (.record []))],
    body := .record [("onlyTo", law)], methods := [], laws := ["onlyTo"] }

/-! ### Calls (LANG-23, KERNEL-28): a method's calls are derived as the object, at most
`callDepthMax` deep

`Relay` keeps `{hits : nat, me : bytes, next : bytes}`. Its method `go {rest, via}` counts the hit,
records `req.self` as `me`, and, when `next` is not empty, invokes `next`'s method 0 through grant
`via` (a grant naming THIS object) with `rest` as the arguments: bytes it holds, forwarded whole
(LANG-23 (iii)), so the journey nests each level's encoded arguments inside the previous one. -/

def R : Ty := .record [("hits", .nat), ("me", .bytes), ("next", .bytes)]
def RA : Ty := .record [("rest", .bytes), ("via", .bytes)]

/-- `go`'s one call slot: an invoke, nothing else. -/
def K : Ty := callOf ["invoke"]

/-- `invoke next 0 rest 1000 (some via)`, under the method's binders (state var 2, args var 1). -/
def relayCall : Term :=
  .inj K "invoke" (.record [("args", .get (.var 1) "rest"), ("budget", .nat 1000),
    ("method", .nat 0), ("obj", .get (.var 2) "next"), ("via", .inj (optTy .bytes) "some" (.get (.var 1) "via"))])

def relayGo : Term :=
  .lam R (.lam RA (.lam reqTy (resultT
    (.ite (.prim .beq (.get (.var 2) "next") (.bytes .empty)) (callsT [noCallT K]) (callsT [someCallT K relayCall]))
    (.record [("hits", .prim .add (.get (.var 2) "hits") (.nat 1)), ("me", .get (.var 0) "self"),
      ("next", .get (.var 2) "next")]))))

def relay : Package :=
  { imports := [], state := R, iface := .record [("go", methodTy R RA [K])],
    body := .record [("go", relayGo)], methods := ["go"], laws := [] }

/-- One call slot more than `callsMax`. -/
def nineLabels : List Label := slotLabels "c" (Kernel.Bounds.callsMax + 1)

def nineGo : Term :=
  .lam R (.lam RA (.lam reqTy (resultT (callsT (nineLabels.map fun _ => noCallT K)) (.var 2))))

def nineTy : Ty := methodTy R RA (nineLabels.map fun _ => K)

/-- A method whose calls row has one slot more than `callsMax`: its type is not a method's. -/
def nineCalls : Package :=
  { imports := [], state := R, iface := .record [("go", nineTy)],
    body := .record [("go", nineGo)], methods := ["go"], laws := [] }

/-- A u64 argument or slot (`none` past `2^64`). -/
def nat64 (n : Nat) : Option ByteArray := Wire.encodeData .nat (.nat n)

def ctxWith (prog : Program D) : Ctx D := Sim.ctxWith prog

def langProgram : Program D := Lang.program Sim.dc.bytes Sim.digestOf

/-- Plant 1: a program whose judge admits every write. -/
def skipJudge : Program D := { langProgram with judge := fun _ _ _ _ _ _ => .ok () }

/-- Plant 2: a program whose judge is told every act is a write (the judge before ID-1). -/
def eraseOccasion : Program D :=
  { langProgram with judge := fun look p ls o n r => langProgram.judge look p ls o n { r with occasion := .write } }

/-- Plant 3: the occasion's payload is lost (a relaw names no laws, every invoke is method 0). -/
def erasePayload : Program D :=
  { langProgram with judge := fun look p ls o n r =>
      let occasion : Occasion D := match r.occasion with
        | .relaw _ => .relaw [] | .adopt _ => .adopt [] | .invoke _ => .invoke 0 | o => o
      langProgram.judge look p ls o n { r with occasion } }

/-- Plant 4: the calls a method makes never reach the kernel (the glue before this day). -/
def dropCalls : Program D :=
  { langProgram with run := fun look p s m a r b => (langProgram.run look p s m a r b).map fun x => (x.1, [], x.2.2) }

/-- Plant 5: the install check before LANG-35: each import's interface read raw from its cell
(decoded, never re-checked), the import's own closure never loaded. -/
def rawInstall : Program D :=
  { langProgram with checkInstall := fun look b => do
      let p ← match Wire.decodePackage b with
        | .ok p => pure p
        | .error e => throw (.program (decodeText e))
      let ifaces ← p.imports.mapM fun d => do
        let id ← idOf Sim.digestOf d
        pure (← readPackage look id).iface
      match p.checkWith ifaces with
      | .ok () => pure ()
      | .error e => throw (.program e.wire) }

/-- A package with nothing in it but its imports (LI). -/
def importer (imports : List ByteArray) : Package :=
  { imports, state := .record [], iface := .record [], body := .record [], methods := [], laws := [] }

/-- Which program the journey runs under. -/
inductive Mode
  | honest | skipJudge | eraseOccasion | erasePayload | dropCalls | rawInstall
  deriving DecidableEq

def Mode.program : Mode → Program D
  | .honest => langProgram
  | .skipJudge => Journey.skipJudge
  | .eraseOccasion => Journey.eraseOccasion
  | .erasePayload => Journey.erasePayload
  | .dropCalls => Journey.dropCalls
  | .rawInstall => Journey.rawInstall

/-- A refusal by a law, with `why` in its reason. -/
def deniedWith (v why : String) : Bool := v.startsWith "refused lawDenied" && (v.splitOn why).length > 1

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

def totalOf (E : Kernel.Env D) (w : World D) (obj : D) : Option Nat :=
  match w.live E obj with
  | some cell => match cell.slots.get (stateBase + 1) with
    | some b => match Wire.decodeData .nat b with
      | .ok (.nat n) => some n
      | _ => none
    | none => none
  | none => none

/-- A Relay object's state slot `i` (0 hits, 1 me, 2 next). -/
def slotOf (E : Kernel.Env D) (w : World D) (obj : D) (i : Nat) : Option ByteArray :=
  (w.live E obj).bind fun cell => cell.slots.get (stateBase + i)

def hitsOf (E : Kernel.Env D) (w : World D) (obj : D) : Option Nat :=
  match (slotOf E w obj 0).map (Wire.decodeData .nat) with
  | some (.ok (.nat n)) => some n
  | _ => none

def meOf (E : Kernel.Env D) (w : World D) (obj : D) : Option ByteArray :=
  match (slotOf E w obj 1).map (Wire.decodeData .bytes) with
  | some (.ok (.bytes b)) => some b
  | _ => none

/-- `go`'s arguments: `rest` forwarded whole, `via` the grant the call goes through. -/
def relayArgs (rest via : ByteArray) : Option ByteArray :=
  Wire.encodeData RA (.record [("rest", .bytes rest), ("via", .bytes via)])

/-- The arguments of a chain entered at the first of `grants` (grant `i` names object `i` on
object `i+1`): each level's arguments nest the next level's, and the last object gets empty ones. -/
def chainArgs : List ByteArray → Option ByteArray
  | [] => relayArgs .empty .empty
  | g :: gs => do relayArgs (← chainArgs gs) g

/-- The install-closure rows (LI, LANG-35): `Top` imports `Mid` imports `Owned` (`pkg`). -/
def installRows (mode : Mode) (r0 : Run) (a : Sim.Member) (pkg : D) : Run := Id.run do
  let prog := mode.program
  let mut r := r0
  let some midBytes := Wire.encodePackage (importer [Sim.dc.bytes pkg]) | return note r "LI Mid has no bytes" false
  let (ri1, vi1, ti1) := go prog r (Sim.signed r.st a a.key (Sim.S.pinsFor r.st.host [a.id, pkg]) (.install midBytes))
  r := note ri1 s!"LI1 install Mid importing Owned: {vi1}" (vi1 == "admitted")
  let some mid := ti1.bind fun t => (createdIds t).head? | return note r "LI no Mid id" false
  let some topBytes := Wire.encodePackage (importer [Sim.dc.bytes mid]) | return note r "LI Top has no bytes" false
  let (ri2, vi2, _) := go prog r (Sim.signed r.st a a.key (Sim.S.pinsFor r.st.host [a.id, mid]) (.install topBytes))
  if mode = .rawInstall then
    return note ri2 s!"PLANT raw-install: LI2 Top pinning only Mid must now be admitted: {vi2}" (vi2 == "admitted")
  r := note ri2 s!"LI2 install Top importing Mid, pinning only Mid: {vi2}" (vi2.startsWith "refused unpinned" && (vi2.splitOn s!"unpinned {reprStr pkg}").length > 1)
  let (ri3, vi3, _) := go prog r (Sim.signed r.st a a.key (Sim.S.pinsFor r.st.host [a.id, mid, pkg]) (.install topBytes))
  r := note ri3 s!"LI3 install Top pinning Mid and Owned: {vi3}" (vi3 == "admitted")
  return r

/-- The call rows (LC): Relay chains through the real receivers. -/
def callRows (mode : Mode) (r0 : Run) (a : Sim.Member) : Run := Id.run do
  let prog := mode.program
  let mut r := r0
  -- LC calls: a chain of six Relay objects o0 … o5, o5 last (empty `next`); grant k lets o_k invoke o_{k+1}
  let some relayBytes := Wire.encodePackage relay | return note r "LC Relay has no bytes" false
  let (rc0, vc0, tc0) := go prog r (Sim.signed r.st a a.key (Sim.S.pinsFor r.st.host [a.id]) (.install relayBytes))
  r := note rc0 s!"LC0 install Relay: {vc0}" (vc0 == "admitted")
  let some rid := tc0.bind fun t => (createdIds t).head? | return note r "LC no Relay id" false
  let some h0 := nat64 0 | return note r "LC no bytes for 0" false
  let some emptyB := Wire.encodeData .bytes (.bytes .empty) | return note r "LC no empty bytes" false
  let mut objs : List D := []
  for _ in [0:6] do
    let next := match objs.head? with | some o => Sim.dc.bytes o | none => .empty
    let some nextB := Wire.encodeData .bytes (.bytes next) | return note r "LC no next bytes" false
    let (rk, vk, tk) := go prog r (Sim.signed r.st a a.key (Sim.S.pinsFor r.st.host [a.id, rid])
      (.create (some rid) [] [(stateBase, h0), (stateBase + 1, emptyB), (stateBase + 2, nextB)]))
    r := note rk s!"LC1 A creates Relay o{5 - objs.length}: {vk}" (vk == "admitted")
    let some o := tk.bind fun t => (createdIds t).head? | return note r "LC no object id" false
    objs := o :: objs
  let mut grants : List D := []
  for (x, y) in objs.zip objs.tail do
    let (rk, vk, tk) := go prog r (Sim.signed r.st a a.key (Sim.S.pinsFor r.st.host [a.id, x, y]) (.grant y x [.invoke 0] none))
    r := note rk s!"LC2 A grants o_k invoke 0 on o_k+1: {vk}" (vk == "admitted")
    let some gk := tk.bind fun t => (createdIds t).head? | return note r "LC no grant id" false
    grants := grants ++ [gk]
  let gBytes := grants.map Sim.dc.bytes
  let pinsAll := Sim.S.pinsFor r.st.host ([a.id, rid] ++ objs ++ grants)
  let o0 := objs.headD 0
  let o1 := objs.getD 1 0
  let o5 := objs.getD 5 0
  -- LC3 entered at o1: o2 … o5 at depths 1 … 4 = callDepthMax, admitted; every object ran once
  let some args1 := chainArgs gBytes.tail | return note r "LC3 no arguments" false
  let (rc3, vc3, _) := go prog r (Sim.signed r.st a a.key pinsAll (.invoke o1 0 args1 10000 none))
  r := { rc3 with log := r.log, bad := r.bad }
  let hit5 := hitsOf Sim.env r.st.host o5
  if mode = .dropCalls then
    r := note r s!"PLANT drop-calls: LC3 the chain's end must now be untouched: {vc3}, o5 hits {hit5}" (vc3 == "admitted" && hit5 == some 0)
  else
    r := note r s!"LC3 A invokes o1, calls 4 deep: {vc3}; o5 hits {hit5}, o5 sees itself as self {meOf Sim.env r.st.host o5 == some (Sim.dc.bytes o5)}"
      (vc3 == "admitted" && hit5 == some 1 && hitsOf Sim.env r.st.host o1 == some 1 &&
        meOf Sim.env r.st.host o5 == some (Sim.dc.bytes o5))
  -- LC4 entered at o0: o5 would be at depth 5, past callDepthMax
  let some args0 := chainArgs gBytes | return note r "LC4 no arguments" false
  let pins4 := Sim.S.pinsFor r.st.host ([a.id, rid] ++ objs ++ grants)
  let (rc4, vc4, _) := go prog r (Sim.signed r.st a a.key pins4 (.invoke o0 0 args0 10000 none))
  r := { rc4 with log := r.log, bad := r.bad }
  if mode = .dropCalls then
    r := note r s!"PLANT drop-calls: LC4 five deep must now be admitted: {vc4}" (vc4 == "admitted")
  else
    r := note r s!"LC4 A invokes o0, calls 5 deep: {vc4}" (vc4.startsWith "refused callTooDeep")
  -- LC5 a call naming a cell by bytes that are not a digest is refused by name
  let some xyz := Wire.encodeData .bytes (.bytes "xyz".toUTF8) | return note r "LC5 no bytes" false
  let (rc5, vc5, tc5) := go prog r (Sim.signed r.st a a.key (Sim.S.pinsFor r.st.host [a.id, rid])
    (.create (some rid) [] [(stateBase, h0), (stateBase + 1, emptyB), (stateBase + 2, xyz)]))
  r := note rc5 s!"LC5a A creates a Relay whose next is not a digest: {vc5}" (vc5 == "admitted")
  let some bad := tc5.bind fun t => (createdIds t).head? | return note r "LC5 no object id" false
  let some argsB := relayArgs .empty .empty | return note r "LC5 no arguments" false
  let (rc5b, vc5b, _) := go prog r (Sim.signed r.st a a.key (Sim.S.pinsFor r.st.host [a.id, rid, bad]) (.invoke bad 0 argsB 10000 none))
  r := note rc5b s!"LC5b A invokes it: {vc5b}" (vc5b.startsWith "refused program" && (vc5b.splitOn "calls: c0 obj: not a digest").length > 1)
  -- LC6 a method with more call slots than callsMax is not a method: install refuses it by name
  let some nineBytes := Wire.encodePackage nineCalls | return note r "LC6 NineCalls has no bytes" false
  let (rc6, vc6, _) := go prog r (Sim.signed r.st a a.key (Sim.S.pinsFor r.st.host [a.id]) (.install nineBytes))
  r := note rc6 s!"LC6 install a method with {Kernel.Bounds.callsMax + 1} call slots: {vc6}"
    (vc6.startsWith "refused program" && (vc6.splitOn "badMethod go").length > 1)
  return r

def journey (mode : Mode) : Run := Id.run do
  let prog := mode.program
  let fk : List (ByteArray × ByteArray) :=
    [("f0".toUTF8, "f0-next".toUTF8), ("f1".toUTF8, "f1-next".toUTF8)]
  let X := ctxWith prog
  let g ← match genesis X Sim.worldName (Sim.nonceOf 0) 100000000 (fk.map fun (k, n) => (k, nextKeyDigest X n)) with
    | .ok g => pure g
    | .error e =>
        return note { st := { rng := ⟨1⟩, host := World.genesis X.env 0 0, members := [] } } s!"genesis refused {e.name}" false
  let members := fk.zipIdx.map fun ((k, n), i) => (⟨founderId X g.origin i, k, n⟩ : Sim.Member)
  let mut r : Run := { st := { rng := ⟨1⟩, host := g, members } }
  let a := members.headD ⟨0, .empty, .empty⟩
  let b := members.getD 1 ⟨0, .empty, .empty⟩
  -- L0 the resident's text reads to exactly the package
  let some ownedBytes := Wire.encodePackage owned | return note r "L0 Owned has no bytes" false
  let some illBytes := Wire.encodePackage illTyped | return note r "L0 illTyped has no bytes" false
  match Read.readPackage ownedText with
  | .error e => r := note r s!"L0 read Owned: {e.text}" false
  | .ok q =>
    let same := Wire.encodePackage q == some ownedBytes
    r := note r "L0 read Owned from text: same bytes as the AST" same
  -- L0c the printer (Lang.Print) gives Owned a text that reads back to the same bytes; a label
  -- that is not one atom has no text; non-UTF-8 bytes in a term print as #hex and read back
  match Print.package owned with
  | none => r := note r "L0c print Owned: no text" false
  | some t =>
    let same := match Read.readPackage t with
      | .ok q => Wire.encodePackage q == some ownedBytes
      | .error _ => false
    r := note r "L0c print Owned, read the text: same bytes" same
  r := note r "L0c a method label with a space has no text"
    (Print.package { owned with methods := ["s et"] }).isNone
  let ff : ByteArray := ⟨#[0xff, 0x22]⟩
  let hexBack := match Print.term (.prim .cat (.bytes ff) (.bytes "q".toUTF8)) with
    | some t => (match Read.readTerm t with
      | .ok (.prim .cat (.bytes x) (.bytes y)) => x == ff && y == "q".toUTF8
      | _ => false) && t == "(cat #ff22 \"q\")"
    | none => false
  r := note r "L0c bytes that are not quote-free UTF-8 print as #hex and read back" hexBack
  -- L0d the reader's fuel counts nesting, not length: an allowlist at `Std.idsMax` (a chain one
  -- level per id) prints and reads back; a list past `Read.listMax` is refused `tooLong`, a form
  -- nested past `Read.depthMax` `tooDeep`, and each bound itself is read
  let ids := (List.range Std.idsMax).map fun i => ByteArray.mk #[UInt8.ofNat (i / 256), UInt8.ofNat (i % 256)]
  let longOk := match Std.allowlist S ids with
    | .ok law => match Print.term law with
      | some t => (match Read.readTerm t with
        | .ok law' => Wire.encodePackage (Std.pkgOf S [("al", law')] []) == Wire.encodePackage (Std.pkgOf S [("al", law)] [])
        | .error _ => false)
      | none => false
    | .error _ => false
  r := note r s!"L0d an allowlist of {Std.idsMax} ids prints and reads back (the same package bytes)" longOk
  let recordOf (n : Nat) : String :=
    "(record" ++ String.join ((List.range n).map fun i => s!" (a{i} 1)") ++ ")"
  let wideOk := match Read.readTerm (recordOf (Read.listMax - 1)) with | .ok _ => true | .error _ => false
  r := note r s!"L0d a list of {Read.listMax} elements reads" wideOk
  let tooLong := match Read.readTerm (recordOf Read.listMax) with | .error (.tooLong _) => true | _ => false
  r := note r s!"L0d a list of {Read.listMax + 1} elements: tooLong" tooLong
  let nested (n : Nat) : String := String.join (List.replicate (n - 1) "(fix ") ++ "1" ++ String.join (List.replicate (n - 1) ")")
  let deepOk := match Read.readTerm (nested Read.depthMax) with | .ok _ => true | .error _ => false
  r := note r s!"L0d a form nested {Read.depthMax} deep reads" deepOk
  let tooDeep := match Read.readTerm (nested (Read.depthMax + 1)) with | .error (.tooDeep _) => true | _ => false
  r := note r s!"L0d a form nested {Read.depthMax + 1} deep: tooDeep" tooDeep
  -- L0e a binder named like a literal is refused by name (every use would read as the literal)
  for (txt, why) in [("(lam true bool true)", "true"), ("(lam 5 nat 5)", "a numeral"), ("(let #ab nat 1 #ab)", "#hex"),
                     ("(fn (false bool) false)", "false"),
                     ("(case (inj (sum (a nat)) a 1) (a 7 7))", "a numeral in a case arm"),
                     ("(lam if nat if)", "a head word"), ("(lam + nat +)", "a primitive")] do
    let refused := match Read.readTerm txt with
      | .error (.reservedBinder _ _) => true
      | _ => false
    r := note r s!"L0e refuse a binder named {why}: reservedBinder" refused
  let named := match Read.readTerm "(lam x5 nat x5)" with | .ok (.lam .nat (.var 0)) => true | _ => false
  r := note r "L0e a binder named x5 reads as a variable" named
  -- L0f (LANG-31) a package at the wire's depth bound, written as text: `n` record levels through field `f`
  -- make a body and an interface whose trees are `2n + 1` deep, so n = 511 puts the package's tree at
  -- Wire.depthMax and its text at Read.depthMax
  let nestTy (n : Nat) : String := String.join (List.replicate n "(rec (f ") ++ "(rec)" ++ String.join (List.replicate n "))")
  let nestT (n : Nat) : String := String.join (List.replicate n "(record (f ") ++ "(record)" ++ String.join (List.replicate n "))")
  let deepText (n : Nat) : String :=
    s!"(package\n  (imports)\n  (state (rec))\n  (iface {nestTy n})\n  (methods)\n  (laws)\n  (body {nestT n}))\n"
  let deepOk := match Read.readPackage (deepText 511) with
    | .ok p => (p.checkWith []).toBool && (match Wire.encodePackage p, Print.package p with
      | some b, some t => (match Read.readPackage t with
        | .ok q => Wire.encodePackage q == some b
        | .error _ => false)
      | _, _ => false)
    | .error _ => false
  r := note r s!"L0f a package {Wire.depthMax} deep as a tree reads, checks, encodes, prints, reads back: same bytes" deepOk
  let deeper := match Read.readPackage (deepText 512) with | .error (.tooDeep _) => true | _ => false
  r := note r "L0f one level deeper: tooDeep" deeper
  r := note r "L0f a label with a space has no bytes"
    (Wire.encodePackage { owned with methods := ["s et"] }).isNone
  -- L0b a seed state read at the package's state type (Read.readData): fields in any order; a
  -- missing field, a wrong-typed value, an unknown sum arm refused `notOfType`
  let seedOk := match Read.readData S "(record (total 5) (owner \"a\"))" with
    | .ok (.record [("owner", .bytes o), ("total", .nat 5)]) => o == "a".toUTF8
    | _ => false
  r := note r "L0b read a seed at Owned's state type" seedOk
  -- the owner as a member's id: bytes that need not be UTF-8, written `#HEX`
  let ownerHex := Print.bytesText (Sim.dc.bytes a.id)
  let hexOk := match Read.readData S s!"(record (owner {ownerHex}) (total 0))" with
    | .ok (.record [("owner", .bytes o), ("total", .nat 0)]) => o == Sim.dc.bytes a.id
    | _ => false
  r := note r "L0b read a seed whose owner is a member id, as ob prints it (#HEX)" hexOk
  for (txt, why) in [("(record (total 5))", "missing field"), ("(record (owner 1) (total 5))", "wrong type"),
                     ("(record (owner \"a\") (total 18446744073709551616))", "past natLimit"),
                     ("(record (owner #6) (total 5))", "odd count of hex digits"),
                     ("(record (owner #6A) (total 5))", "uppercase hex digit"),
                     ("(record (owner \"a\") (total #05))", "hex at a nat")] do
    let refused := match Read.readData S txt with
      | .error (.notOfType _) => true
      | _ => false
    r := note r s!"L0b refuse a seed with a {why}: notOfType" refused
  -- L1 install
  let c1 := Sim.signed r.st a a.key (Sim.S.pinsFor r.st.host [a.id]) (.install ownedBytes)
  let (r1, v1, t1) := go prog r c1
  r := note r1 s!"L1 install Owned: {v1}" (v1 == "admitted")
  let some pkg := t1.bind fun t => (createdIds t).head? | return note r "L1 no package id" false
  -- L6 an ill-typed package
  let c6 := Sim.signed r.st a a.key (Sim.S.pinsFor r.st.host [a.id]) (.install illBytes)
  let (r6, v6, _) := go prog r c6
  r := note r6 s!"L6 install ill-typed: {v6}" (v6.startsWith "refused program")
  r := installRows mode r a pkg
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
  let some obj := t2.bind fun t => (createdIds t).head? | return note r "L2 no object id" false
  -- L3 set 50
  let c3 := Sim.signed r.st a a.key (Sim.S.pinsFor r.st.host [a.id, obj, pkg]) (.invoke obj 0 n50 10000 none)
  let (r3, v3, _) := go prog r c3
  r := note r3 s!"L3 A set 50: {v3}, total = {totalOf Sim.env r3.st.host obj}" (v3 == "admitted" && totalOf Sim.env r3.st.host obj == some 50)
  -- L4 set 101
  let c4 := Sim.signed r.st a a.key (Sim.S.pinsFor r.st.host [a.id, obj, pkg]) (.invoke obj 0 n101 10000 none)
  let (r4, v4, _) := go prog r c4
  if mode = .skipJudge then
    r := note r4 s!"PLANT skip-judge: L4 A set 101 must now be admitted: {v4}" (v4 == "admitted")
  else
    r := note r4 s!"L4 A set 101: {v4}, total = {totalOf Sim.env r4.st.host obj}"
      (v4.startsWith "refused lawDenied" && (v4.splitOn "bounded: over 100").length > 1 && totalOf Sim.env r4.st.host obj == some 50)
  -- L5 B through a grant
  let cg := Sim.signed r.st a a.key (Sim.S.pinsFor r.st.host [a.id, b.id, obj]) (.grant obj b.id [.invoke 0] none)
  let (rg, vg, tg) := go prog r cg
  r := note rg s!"L5a A grants B invoke 0: {vg}" (vg == "admitted")
  let some gr := tg.bind fun t => (createdIds t).head? | return note r "L5 no grant id" false
  let c5 := Sim.signed r.st b b.key (Sim.S.pinsFor r.st.host [b.id, obj, pkg, gr]) (.invoke obj 0 n7 10000 (some gr))
  let (r5, v5, _) := go prog r c5
  unless mode = .skipJudge do
    r := note r5 s!"L5 B (granted) set 7: {v5}" (v5.startsWith "refused lawDenied" && (v5.splitOn "ownerOnly: not the owner").length > 1)
  r := { r5 with log := r.log, bad := r.bad }
  -- L8 a birth is judged as a birth: a seed carrying approvals is refused by `fresh`
  let some tallyBytes := Wire.encodePackage tally | return note r "L8 Tally has no bytes" false
  let (r8, v8, t8) := go prog r (Sim.signed r.st a a.key (Sim.S.pinsFor r.st.host [a.id]) (.install tallyBytes))
  r := note r8 s!"L8a install Tally: {v8}" (v8 == "admitted")
  let some tid := t8.bind fun t => (createdIds t).head? | return note r "L8 no Tally id" false
  let some n7' := nat64 7 | return note r "L8 no bytes for 7" false
  let seeded : Slots := [(stateBase, n7'), (stateBase + 1, n0)]
  let (r8b, v8b, _) := go prog r (Sim.signed r.st a a.key (Sim.S.pinsFor r.st.host [a.id, tid]) (.create (some tid) [] seeded))
  r := { r8b with log := r.log, bad := r.bad }
  if mode = .eraseOccasion then
    r := note r s!"PLANT erase-occasion: L8b the seeded birth must now be admitted: {v8b}" (v8b == "admitted")
  else if mode = .honest then
    r := note r s!"L8b A creates Tally seeded approvals = 7: {v8b}"
      (v8b.startsWith "refused lawDenied" && (v8b.splitOn "fresh: seeded").length > 1)
  let (r8c, v8c, t8c) := go prog r (Sim.signed r.st a a.key (Sim.S.pinsFor r.st.host [a.id, tid]) (.create (some tid) [] [(stateBase, n0), (stateBase + 1, n0)]))
  r := note r8c s!"L8c A creates Tally seeded approvals = 0: {v8c}" (v8c == "admitted")
  let some tobj := t8c.bind fun t => (createdIds t).head? | return note r "L8 no Tally object" false
  -- the invoke's method index reaches the law: `b` (method 1) is closed, `a` (method 0) open
  let (r8d, v8d, _) := go prog r (Sim.signed r.st a a.key (Sim.S.pinsFor r.st.host [a.id, tobj, tid]) (.invoke tobj 0 n7 10000 none))
  r := note r8d s!"L8d A invokes Tally.a 7: {v8d}" (v8d == "admitted")
  let (r8e, v8e, _) := go prog r (Sim.signed r.st a a.key (Sim.S.pinsFor r.st.host [a.id, tobj, tid]) (.invoke tobj 1 n7 10000 none))
  r := { r8e with log := r.log, bad := r.bad }
  if mode = .eraseOccasion || mode = .erasePayload then
    r := note r s!"PLANT {if mode = .eraseOccasion then "erase-occasion" else "erase-payload"}: L8e Tally.b must now be admitted: {v8e}" (v8e == "admitted")
  else if mode = .honest then
    r := note r s!"L8e A invokes Tally.b 7: {v8e}" (deniedWith v8e "fresh: method b is closed")
  -- L9 a law replacement is judged as one: `frozen` refuses its own removal
  let some frozenBytes := Wire.encodePackage frozen | return note r "L9 Frozen has no bytes" false
  let (r9, v9, t9) := go prog r (Sim.signed r.st a a.key (Sim.S.pinsFor r.st.host [a.id]) (.install frozenBytes))
  r := note r9 s!"L9a install Frozen: {v9}" (v9 == "admitted")
  let some fid := t9.bind fun t => (createdIds t).head? | return note r "L9 no Frozen id" false
  let (r9b, v9b, t9b) := go prog r (Sim.signed r.st a a.key (Sim.S.pinsFor r.st.host [a.id, fid]) (.create none [fid] [(stateBase, n0)]))
  r := note r9b s!"L9b A creates a data object under Frozen: {v9b}" (v9b == "admitted")
  let some dobj := t9b.bind fun t => (createdIds t).head? | return note r "L9 no object id" false
  let (r9c, v9c, _) := go prog r (Sim.signed r.st a a.key (Sim.S.pinsFor r.st.host [a.id, dobj, fid]) (.write dobj [(0, some n7)] none))
  r := note r9c s!"L9c A writes under Frozen: {v9c}" (v9c == "admitted")
  let (r9d, v9d, _) := go prog r (Sim.signed r.st a a.key (Sim.S.pinsFor r.st.host [a.id, dobj, fid]) (.law dobj [] none))
  r := { r9d with log := r.log, bad := r.bad }
  if mode = .eraseOccasion then
    r := note r s!"PLANT erase-occasion: L9d removing Frozen must now be admitted: {v9d}" (v9d == "admitted")
  else if mode = .honest then
    r := note r s!"L9d A removes Frozen: {v9d}"
      (v9d.startsWith "refused lawDenied" && (v9d.splitOn "frozen: laws are frozen").length > 1)
  -- L10 the relaw carries the incoming laws: `onlyTo [Frozen]` admits exactly that replacement
  let some onlyBytes := Wire.encodePackage (onlyTo (Sim.dc.bytes fid)) | return note r "L10 OnlyTo has no bytes" false
  let (r10, v10, t10) := go prog r (Sim.signed r.st a a.key (Sim.S.pinsFor r.st.host [a.id]) (.install onlyBytes))
  r := note r10 s!"L10a install OnlyTo [Frozen]: {v10}" (v10 == "admitted")
  let some oid := t10.bind fun t => (createdIds t).head? | return note r "L10 no OnlyTo id" false
  let (r10b, v10b, t10b) := go prog r (Sim.signed r.st a a.key (Sim.S.pinsFor r.st.host [a.id, oid]) (.create none [oid] []))
  r := note r10b s!"L10b A creates a data object under OnlyTo: {v10b}" (v10b == "admitted")
  let some oobj := t10b.bind fun t => (createdIds t).head? | return note r "L10 no object id" false
  let (r10c, v10c, _) := go prog r (Sim.signed r.st a a.key (Sim.S.pinsFor r.st.host [a.id, oobj, oid, tid]) (.law oobj [tid] none))
  r := { r10c with log := r.log, bad := r.bad }
  if mode = .eraseOccasion then
    -- OnlyTo, told a write, now admits; the refusal is the incoming Tally judging the state it
    -- would govern (LANG-19), which lacks Tally's fields
    r := note r s!"PLANT erase-occasion: L10c OnlyTo must now pass the wrong replacement to the incoming laws: {v10c}"
      (deniedWith v10c "state field approvals missing")
  else if mode != .skipJudge then
    r := note r s!"L10c A replaces OnlyTo by [Tally]: {v10c}" (deniedWith v10c "onlyTo: not the agreed laws")
  if mode != .eraseOccasion then
    let (r10d, v10d, _) := go prog r (Sim.signed r.st a a.key (Sim.S.pinsFor r.st.host [a.id, oobj, oid, fid]) (.law oobj [fid] none))
    r := { r10d with log := r.log, bad := r.bad }
    if mode = .erasePayload then
      r := note r s!"PLANT erase-payload: L10d the agreed replacement must now be refused: {v10d}" (deniedWith v10d "onlyTo: not the agreed laws")
    else
      r := note r s!"L10d A replaces OnlyTo by [Frozen]: {v10d}" (v10d == "admitted")
  -- L11 adopt: `birthOnly` may be born under, never added later
  let some boBytes := Wire.encodePackage birthOnly | return note r "L11 BirthOnly has no bytes" false
  let (r11, v11, t11) := go prog r (Sim.signed r.st a a.key (Sim.S.pinsFor r.st.host [a.id]) (.install boBytes))
  r := note r11 s!"L11a install BirthOnly: {v11}" (v11 == "admitted")
  let some bid := t11.bind fun t => (createdIds t).head? | return note r "L11 no BirthOnly id" false
  let (r11b, v11b, t11b) := go prog r (Sim.signed r.st a a.key (Sim.S.pinsFor r.st.host [a.id, bid]) (.create none [bid] []))
  r := note r11b s!"L11b A creates a data object under BirthOnly: {v11b}" (v11b == "admitted")
  let some bobj := t11b.bind fun t => (createdIds t).head? | return note r "L11 no BirthOnly object" false
  let (r11o, v11o, t11o) := go prog r (Sim.signed r.st a a.key (Sim.S.pinsFor r.st.host [a.id]) (.create none [] []))
  r := note r11o s!"L11o A creates a lawless data object: {v11o}" (v11o == "admitted")
  let some lobj := t11o.bind fun t => (createdIds t).head? | return note r "L11 no object id" false
  let (r11c, v11c, _) := go prog r (Sim.signed r.st a a.key (Sim.S.pinsFor r.st.host [a.id, lobj, bid]) (.law lobj [bid] none))
  r := { r11c with log := r.log, bad := r.bad }
  if mode = .eraseOccasion then
    r := note r s!"PLANT erase-occasion: L11c adding BirthOnly must now be admitted: {v11c}" (v11c == "admitted")
  else if mode != .skipJudge then
    r := note r s!"L11c A adds BirthOnly to an existing object: {v11c}" (deniedWith v11c "birthOnly: only at birth")
  -- L11d a law KEPT across a relaw is not adopted again: only the added Frozen judges adopt
  let (r11d, v11d, _) := go prog r (Sim.signed r.st a a.key (Sim.S.pinsFor r.st.host [a.id, bobj, bid, fid]) (.law bobj [bid, fid] none))
  r := { r11d with log := r.log, bad := r.bad }
  if mode = .honest then
    r := note r s!"L11d A keeps BirthOnly and adds Frozen: {v11d}" (v11d == "admitted")
  r := callRows mode r a
  -- L7 follower and auditor
  match World.fold Sim.env g r.st.log with
  | .ok w => r := note r s!"L7 follower reaches the Host's World ({r.st.log.length} turns)" (Sim.same w r.st.host)
  | .error (i, e) => r := note r s!"L7 follower refused at {i}: {Sim.nameOf e}" false
  match audit (ctxWith prog) g r.st.log with
  | .ok w => r := note r "L7 auditor reaches the Host's World" (Sim.same w r.st.host)
  | .error (i, e) => r := note r s!"L7 auditor refused at {i}: {reprStr e}" false
  return r

def runAll : IO UInt32 := do
  let runs := [Mode.honest, .skipJudge, .eraseOccasion, .erasePayload, .dropCalls, .rawInstall].map journey
  for r in runs do for l in r.log do IO.println l
  let bad := (runs.map (·.bad)).foldl (· + ·) 0
  IO.println s!"lang-journey: {if bad = 0 then "GREEN" else s!"RED ({bad})"}"
  return if bad = 0 then 0 else 1

end Nanodregg.Lang.Journey
