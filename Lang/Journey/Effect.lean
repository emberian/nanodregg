/-
# Lang.Journey.Effect — §EF: a method's GRADE bounds what its run moves (LANG-89, DESIGN-TYPES §2)

A Treasury package: state `{asset, asset2, payee}`, a method `pay {amount}` typed `(calls (transfer))`
that moves `amount` of `asset` from the object's own account to the payee's, and `pay2 {amount}` with
TWO transfer slots, moving `amount` of `asset` and `amount + 1` of `asset2` (the kernel admits one
effect per cell per Turn, `duplicateEffect`, so the legs touch disjoint accounts). With the grade `(effect (moves 10))` on each it installs and a
run within the grade is admitted (EF1); the same package with NO grade is refused at install by name,
`effectExceeded pay` (EF2: the type names a value-moving arm under the zero grade); a run past the
grade is refused by name, `program effectExceeded …` (EF3), and nothing moves. The grade is the SUM
over the returned calls: `pay2 {amount 4}` (4 α + 5 β = 9) is admitted (EF4) and `pay2 {amount 5}`
(5 α + 6 β = 11) refused (EF5), which a `movesOf` taking the largest call (6) would admit (EF5 red). Every row is a call through
`Receive.submit` with `Lang.program`; balances are read from the value cells.
-/
import Lang.Journey.OfferEscrow

namespace Nanodregg.Lang.Journey

open Nanodregg.Kernel Nanodregg.Kernel.Receive

def trS : Ty := .record [("asset", .digest), ("asset2", .digest), ("payee", .digest)]
def trA : Ty := .record [("amount", .nat)]
def trC : Ty := callOf ["transfer"]

/-- Under the method's binders (rows 3, state 2, arg 1, req 0): `transfer amt (of self ASSET) (of payee ASSET)`,
`ASSET` a state field (`asset` or `asset2`). -/
def trPayCallWith (amt : Term) (asset : Label) : Term :=
  let st (f : Label) : Term := .get (.var 2) f
  .inj trC "transfer" (.record [
    ("amount", amt),
    ("dst", .inj acctRefTy "of" (.record [("asset", st asset), ("owner", st "payee")])),
    ("once", .inj (optTy .bytes) "none" (.record [])),
    ("src", .inj acctRefTy "of" (.record [("asset", st asset), ("owner", .get (.var 0) "self")])),
    ("via", .inj (optTy .digest) "none" (.record []))])

def trPayCall : Term := trPayCallWith (.get (.var 1) "amount") "asset"

def trPayBody : Term :=
  .lam (.record []) (.lam trS (.lam trA (.lam reqTy (resultT (callsT [someCallT trC trPayCall]) (.var 2)))))

/-- Two transfer slots, `amount` of `asset` and `amount + 1` of `asset2` (one effect per CELL per Turn
is the kernel's rule, `duplicateEffect`: the two legs must touch disjoint accounts): a run moves
2 × amount + 1 units. -/
def trPay2Body : Term :=
  .lam (.record []) (.lam trS (.lam trA (.lam reqTy
    (resultT (callsT [someCallT trC trPayCall,
      someCallT trC (trPayCallWith (.prim .add (.get (.var 1) "amount") (.nat 1)) "asset2")]) (.var 2)))))

/-- The Treasury, graded `moves n` when `grade = some n`, ungraded (the zero grade) otherwise. -/
def treasury (grade : Option Nat) : Package :=
  { imports := [], state := trS,
    iface := .record [("pay", methodTy trS trA [trC]), ("pay2", methodTy trS trA [trC, trC])],
    body := .record [("pay", trPayBody), ("pay2", trPay2Body)], methods := ["pay", "pay2"], laws := [],
    effects := match grade with | some n => [("pay", { moves := n }), ("pay2", { moves := n })] | none => [] }

def trArgs (amount : Nat) : Option ByteArray := Wire.encodeData trA (.record [("amount", .nat amount)])

def efRows (r0 : Run) (a b : Sim.Member) : Run := Id.run do
  let prog := langProgram
  let X := ctxWith prog
  let mut r := r0
  let some pb := Wire.encodePackage (treasury (some 10)) | return note r "EF0 Treasury has no bytes" false
  let signed (r : Run) (m : Sim.Member) (ids : List D) (body : Body D) : Call D :=
    Sim.signed r.st m m.key (Sim.S.pinsFor r.st.host (m.id :: ids)) body
  let mk (r : Run) (m : Sim.Member) (ids : List D) (body : Body D) : Run × String × Option D :=
    let (r', v, t) := go prog r (signed r m ids body)
    (r', v, t.bind fun t => (createdIds t).head?)
  let (r1, v1, pkg?) := mk r a [] (.install pb)
  r := r1
  let some pkg := pkg? | return note r s!"EF0 install Treasury: {v1}" false
  let (r2, vα, α?) := mk r a [] (.issue 100)
  r := r2
  let some α := α? | return note r s!"EF0 issue α: {vα}" false
  let (r2b, vβ, β?) := mk r a [] (.issue 100)
  r := r2b
  let some β := β? | return note r s!"EF0 issue β: {vβ}" false
  let some seed := stateSlots (recordRow trS) [("asset", .digest (Sim.dc.bytes α)), ("asset2", .digest (Sim.dc.bytes β)),
      ("payee", .digest (Sim.dc.bytes b.id))] 0
    | return note r "EF0 no seed bytes" false
  let (r3, vx, ox?) := mk r a [pkg, α, β, b.id] (.create (some pkg) [] seed)
  r := r3
  let some ox := ox? | return note r s!"EF0 create the treasury object: {vx}" false
  let acct (owner asset : D) : D := accountId X owner asset
  let mut setup : List String := [v1, vα, vβ, vx]
  for asset in [α, β] do
    for owner in [ox, b.id] do
      let (r', v, _) := mk r a [asset] (.account asset owner)
      r := r'; setup := setup ++ [v]
    let (r', v, _) := mk r a [asset, acct ox asset] (.transfer (.well asset) (.of ox asset) 50 none none)
    r := r'; setup := setup ++ [v]
  let bal (w : World D) (owner asset : D) : Int := (lvBalance w (acct owner asset)).getD (-1)
  let w0 := r.st.host
  r := note r s!"EF0 A installs Treasury (pay: (calls (transfer)), pay2: (calls (transfer) (transfer)), each (effect (moves 10))), issues α and β, creates X \{asset α, asset2 β, payee B}, funds X with 50 of each: {setup}; X holds {bal w0 ox α} α and {bal w0 ox β} β, B {bal w0 b.id α} α and {bal w0 b.id β} β"
    (setup.all (· == "admitted") && bal w0 ox α == 50 && bal w0 b.id α == 0 && bal w0 ox β == 50 && bal w0 b.id β == 0)
  let pay (r : Run) (method : Nat) (amount : Nat) : Run × String :=
    match trArgs amount with
    | none => (r, "no bytes")
    | some x =>
      let (r', v, _) := go prog r (signed r a [pkg, ox, α, β, acct ox α, acct b.id α, acct ox β, acct b.id β]
        (.invoke ox method x 100000 none))
      (r', v)
  -- EF1 within the grade: 10 of a grade of 10
  let (r5, v5) := pay r 0 10
  let w1 := r5.st.host
  r := note r5 s!"EF1 A invokes X.pay \{amount 10} under moves 10: {v5}; X holds {bal w1 ox α} α (was 50), B {bal w1 b.id α} α (was 0)"
    (v5 == "admitted" && bal w1 ox α == 40 && bal w1 b.id α == 10)
  -- EF2 the body exceeds the grade: the same method with no grade is refused at install, by name
  let some ub := Wire.encodePackage (treasury none) | return note r "EF2 ungraded Treasury has no bytes" false
  let (r6, v6, _) := mk r a [] (.install ub)
  r := note r6 s!"EF2 install the Treasury with (calls (transfer)) and no effect: {v6}"
    (v6.startsWith "refused program" && (v6.splitOn "effectExceeded pay").length > 1)
  -- EF3 the run exceeds the grade: 20 of a grade of 10, refused by name, nothing moves
  let (r7, v7) := pay r 0 20
  let w2 := r7.st.host
  r := note r7 s!"EF3 A invokes X.pay \{amount 20} under moves 10: {v7}; X holds {bal w2 ox α} α (still 40), B {bal w2 b.id α} α (still 10)"
    (v7.startsWith "refused program" && (v7.splitOn "effectExceeded moves 20 past 10").length > 1 &&
      bal w2 ox α == 40 && bal w2 b.id α == 10)
  -- EF4 the grade is a SUM over the calls: 4 α and 5 β under moves 10, admitted (disjoint cells)
  let (r8, v8) := pay r 1 4
  let w3 := r8.st.host
  r := note r8 s!"EF4 A invokes X.pay2 \{amount 4} (two transfers, 4 α + 5 β = 9) under moves 10: {v8}; X holds {bal w3 ox α} α (was 40) and {bal w3 ox β} β (was 50), B {bal w3 b.id α} α (was 10) and {bal w3 b.id β} β (was 0)"
    (v8 == "admitted" && bal w3 ox α == 36 && bal w3 b.id α == 14 && bal w3 ox β == 45 && bal w3 b.id β == 5)
  -- EF5 5 α and 6 β sum to 11 past 10: refused by name though each call is within the grade
  let (r9, v9) := pay r 1 5
  let w4 := r9.st.host
  r := note r9 s!"EF5 A invokes X.pay2 \{amount 5} (5 α + 6 β = 11) under moves 10: {v9}; X holds {bal w4 ox α} α (still 36) and {bal w4 ox β} β (still 45), B {bal w4 b.id α} α (still 14) and {bal w4 b.id β} β (still 5)"
    (v9.startsWith "refused program" && (v9.splitOn "effectExceeded moves 11 past 10").length > 1 &&
      bal w4 ox α == 36 && bal w4 b.id α == 14 && bal w4 ox β == 45 && bal w4 b.id β == 5)
  return r

def effectSession : Run :=
  let X := ctxWith langProgram
  let fk := [("ef-a".toUTF8, "ef-a-next".toUTF8), ("ef-b".toUTF8, "ef-b-next".toUTF8)]
  match genesis X Sim.worldName (Sim.nonceOf 11) 100000000
      (fk.map fun (k, n) => (k, nextKeyDigest X n)) Authority.none with
  | .error e => note { st := { rng := ⟨1⟩, host := World.genesis X.env 0 0, members := [] } }
      s!"EF genesis: {e.name}" false
  | .ok g =>
    let ms := fk.zipIdx.map fun ((k, n), i) => (⟨founderId X g.origin i, k, n⟩ : Sim.Member)
    efRows { st := { rng := ⟨1⟩, host := g, members := ms } }
      (ms.headD ⟨0, .empty, .empty⟩) (ms.getD 1 ⟨0, .empty, .empty⟩)

initialize register { name := "effect", run := pure effectSession }

end Nanodregg.Lang.Journey
