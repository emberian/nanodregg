/-
# Lang.Journey.OfferEscrow — §LE: `Std.offer` with a value leg through the real receivers (PROT-8)

`E := offerEscrowPackage ["price"] ["buyer", "seller"]`, installed by A. A's object X and B's
object Y, both of `E`. A issues denomination α and B issues β; each mints 20 to its own account. A
posts X's offer 0 (buyer, price [5,10], leg 5 α, payTo A) and B posts Y's offer 0 (seller, [8,12],
leg 7 β, payTo B) and offer 1 (seller, [11,12], leg 1 β); each post moves its leg from the poster's
account into the offering object's through the poster's grant of `transfer` to the object. B
invites X (`[invoke take]` on Y); A invokes `X.fuse`, which pays X's leg to B, retracts X's offer,
logs, and invokes `Y.take` on the judged deal (LANG-77), which pays Y's leg to A, retracts and logs.
Every row is a call through `Receive.submit` with `Lang.program`, read back from the World it
leaves: offer rows by `storyRow`, balances by the value cells. LE2–LE5 are judged on the World
before LE1.
-/
import Lang.Journey.Offer
import Lang.StdOfferEscrow

namespace Nanodregg.Lang.Journey

open Nanodregg.Kernel Nanodregg.Kernel.Receive

def lvBalance (w : World D) (id : D) : Option Int :=
  (w.live Sim.env id).bind fun c => (c.slots.get Value.balanceKey).bind Value.balanceOf

/-- `post {give {amount, asset}, grant, n, payTo, role, terms, want {amount, asset}}` with the one term
`price` in `[lo, hi]`: the offer gives `amount` of `asset` and asks at least `wamount` of `wasset`. -/
def lvPostArg (n : Nat) (role : Label) (lo hi amount : Nat) (asset grant payTo : D) (wamount : Nat) (wasset : D) :
    Option ByteArray :=
  Wire.encodeData (Std.escrowPostArg ["price"] ["buyer", "seller"])
    (.record [("give", .record [("amount", .nat amount), ("asset", .digest (Sim.dc.bytes asset))]),
      ("grant", .digest (Sim.dc.bytes grant)), ("n", .nat n), ("payTo", .digest (Sim.dc.bytes payTo)),
      ("role", .inj role (.record [])),
      ("terms", .record [("price", .record [("hi", .nat hi), ("lo", .nat lo)])]),
      ("want", .record [("amount", .nat wamount), ("asset", .digest (Sim.dc.bytes wasset))])])

def lvRows (r0 : Run) (a b : Sim.Member) : Run := Id.run do
  let prog := langProgram
  let X := ctxWith prog
  let mut r := r0
  let P ← match Std.offerEscrowPackage ["price"] ["buyer", "seller"] with
    | .ok p => pure p
    | .error e => return note r s!"LE0 offerEscrowPackage refused: {e.name}" false
  let some od := P.rels.lookup "offer" | return note r "LE0 E has no offer relation" false
  let some sd := P.rels.lookup "session" | return note r "LE0 E has no session relation" false
  let some pb := Wire.encodePackage P | return note r "LE0 E has no bytes" false
  let (r1, v1, t1) := go prog r (Sim.signed r.st a a.key (Sim.S.pinsFor r.st.host [a.id]) (.install pb))
  let some pkg := t1.bind fun t => (createdIds t).head? | return note r1 s!"LE0 install E: {v1}" false
  r := r1
  let signed (r : Run) (m : Sim.Member) (ids : List D) (body : Body D) : Call D :=
    Sim.signed r.st m m.key (Sim.S.pinsFor r.st.host (m.id :: ids)) body
  let mk (r : Run) (m : Sim.Member) (ids : List D) (body : Body D) : Run × String × Option D :=
    let (r', v, t) := go prog r (signed r m ids body)
    (r', v, t.bind fun t => (createdIds t).head?)
  let (rt1, vx, X?) := mk r a [pkg] (.create (some pkg) [] [])
  r := rt1
  let (rt3, vy, Y?) := mk r b [pkg] (.create (some pkg) [] [])
  r := rt3
  let (rt4, vα, α?) := mk r a [] (.issue 100)
  r := rt4
  let (rt5, vβ, β?) := mk r b [] (.issue 100)
  r := rt5
  let (some ox, some oy, some α, some β) := (X?, Y?, α?, β?)
    | return note r s!"LE0 objects and denominations: {[vx, vy, vα, vβ]}" false
  let acct (owner asset : D) : D := accountId X owner asset
  let mut setup : List String := [v1, vx, vy, vα, vβ]
  for (owner, asset) in [(a.id, α), (ox, α), (b.id, α), (b.id, β), (oy, β), (a.id, β)] do
    let (r', v, _) := mk r a [asset] (.account asset owner)
    r := r'; setup := setup ++ [v]
  let (rm1, vm1, _) := mk r a [α, acct a.id α] (.transfer (.well α) (.of a.id α) 20 none none)
  let (rm2, vm2, _) := mk rm1 b [β, acct b.id β] (.transfer (.well β) (.of b.id β) 20 none none)
  r := rm2; setup := setup ++ [vm1, vm2]
  -- each poster's grant to its object of `transfer` on its own account (KERNEL-60)
  let (rt6, vga, gA?) := mk r a [ox, acct a.id α] (.grant (acct a.id α) ox [.transfer 5] none)
  r := rt6
  let (rt7, vgb, gB?) := mk r b [oy, acct b.id β] (.grant (acct b.id β) oy [.transfer 9] none)
  r := rt7
  let (some gA, some gB) := (gA?, gB?) | return note r s!"LE0 deposit grants: {[vga, vgb]}" false
  setup := setup ++ [vga, vgb]
  let post (r : Run) (m : Sim.Member) (obj : D) (ids : List D) (arg : Option ByteArray) : Run × String :=
    match arg with
    | none => (r, "no bytes")
    | some x =>
      let (r', v, _) := go prog r (signed r m ([obj, pkg] ++ ids) (.invoke obj Std.offerPostIx x 100000 none))
      (r', v)
  let (rt8, vpx) := post r a ox [gA, α, acct a.id α, acct ox α] (lvPostArg 0 "buyer" 5 10 5 α gA a.id 7 β)
  r := rt8
  let (rt9, vpy) := post r b oy [gB, β, acct b.id β, acct oy β] (lvPostArg 0 "seller" 8 12 7 β gB b.id 5 α)
  r := rt9
  let (rt10, vpy1) := post r b oy [gB, β, acct b.id β, acct oy β] (lvPostArg 1 "seller" 11 12 1 β gB b.id 5 α)
  r := rt10
  let (rt12, viy, gY?) := mk r b [oy, ox] (.grant oy ox [.invoke Std.offerTakeIx] none)
  r := rt12
  let some gY := gY? | return note r s!"LE0 invitation: {viy}" false
  setup := setup ++ [vpx, vpy, vpy1, viy]
  let w0 := r.st.host
  let bal (w : World D) (owner asset : D) : Int := (lvBalance w (acct owner asset)).getD (-1)
  let present (w : World D) (obj : D) (n : Nat) : Bool := (storyRow w obj 0 od (lfOfferKey n)).isSome
  r := note r s!"LE0 A installs E = offerEscrowPackage [price] [buyer, seller] and creates X, B creates Y; A issues α and B β (mint 20 each); A posts X's offer 0 (buyer [5,10], leg 5 α, payTo A) and B posts Y's offers 0 (seller [8,12], leg 7 β) and 1 (seller [11,12], leg 1 β), each through its grant to its object of transfer on its own account; B invites X [invoke take] on Y: {setup}; held: X {bal w0 ox α} α, Y {bal w0 oy β} β; A {bal w0 a.id α} α, B {bal w0 b.id β} β"
    (setup.all (· == "admitted") && bal w0 ox α == 5 && bal w0 oy β == 8 && bal w0 a.id α == 15 &&
      bal w0 b.id β == 12 && present w0 ox 0 && present w0 oy 0 && present w0 oy 1)
  let r0' := r
  let fuse (r : Run) (cells : List D) (rows : List (RowSlot D × D)) (arg : Option ByteArray) : Run × String :=
    match arg with
    | none => (r, "no bytes")
    | some x =>
      let (r', v, _) := go prog r (signedRows r.st a (Sim.S.pinsFor r.st.host ([a.id, pkg] ++ cells)) rows []
        (.invoke ox Std.offerFuseIx x 1000000 none))
      (r', v)
  let pinOffer (w : World D) (obj : D) (n : Nat) := hole_pinAt obj w 0 od (lfOfferKey n)
  let cells := [ox, oy, gY, α, β, acct ox α, acct b.id α, acct oy β, acct a.id β]
  let arg1 := lfFuseArg ox oy 9 0 0 (some gY)
  -- LE1 the fuse moves both legs: X's 5 α to B, Y's 7 β to A; both offers gone (an instance of
  -- `Std.escrow_fuse_admitted`, Lang.Proofs.StdOfferEscrowFuse)
  let (rf1, vf1) := fuse r0' cells (pinOffer w0 ox 0 ++ pinOffer w0 oy 0) arg1
  let w1 := rf1.st.host
  r := note rf1 s!"LE1 A invokes X.fuse (theta price 9, via B's grant) pinning both offers 0: {vf1}; X's offer 0 present {present w1 ox 0}, Y's offer 0 present {present w1 oy 0}; X holds {bal w1 ox α} α (was 5), B holds {bal w1 b.id α} α (was 0); Y holds {bal w1 oy β} β (was 8), A holds {bal w1 a.id β} β (was 0); α outstanding in accounts {bal w1 a.id α + bal w1 ox α + bal w1 b.id α} (was 20)"
    (vf1 == "admitted" && !present w1 ox 0 && !present w1 oy 0 && present w1 oy 1 &&
      bal w1 ox α == 0 && bal w1 b.id α == 5 && bal w1 oy β == 1 && bal w1 a.id β == 7 &&
      bal w1 a.id α + bal w1 ox α + bal w1 b.id α == 20)
  -- LE2 not compliant: nothing moves
  let (rf2, vf2) := fuse r0' cells (pinOffer w0 ox 0 ++ pinOffer w0 oy 1)
    (lfFuseArg ox oy 9 0 1 (some gY))
  r := note r s!"LE2 the same fuse naming and pinning Y's offer 1 (seller [11,12], price 9 outside it): {vf2}; X still holds {bal rf2.st.host ox α} α, Y {bal rf2.st.host oy β} β"
    (refusedBy vf2 "fuse" "notCompliant" && bal rf2.st.host ox α == 5 && bal rf2.st.host oy β == 8 &&
      present rf2.st.host ox 0 && present rf2.st.host oy 1)
  -- LE3 withdraw credits the leg back to payTo
  let wd (r : Run) (rows : List (RowSlot D × D)) : Run × String :=
    match Wire.encodeData (.record []) (.record []) with
    | none => (r, "no bytes")
    | some x =>
      let (r', v, _) := go prog r (signedRows r.st a (Sim.S.pinsFor r.st.host [a.id, pkg, ox, α, acct ox α, acct a.id α])
        rows [] (.invoke ox Std.offerWithdrawIx x 100000 none))
      (r', v)
  let (rw3, vw3) := wd r0' (pinOffer w0 ox 0)
  let w3 := rw3.st.host
  r := note r s!"LE3 A invokes X.withdraw pinning X's offer 0: {vw3}; offer 0 present {present w3 ox 0}; X holds {bal w3 ox α} α, A {bal w3 a.id α} α (was 15)"
    (vw3 == "admitted" && !present w3 ox 0 && bal w3 ox α == 0 && bal w3 a.id α == 20)
  let (rw4, vw4) := wd r0' []
  r := note r s!"LE4 X.withdraw with no offer row pinned: {vw4}"
    (refusedBy vw4 "withdraw" "offerUnpinned" && bal rw4.st.host ox α == 5 && present rw4.st.host ox 0)
  -- LE5 a post whose grant is smaller than its leg: refused, no row, nothing moved
  let (rp5, vp5) := post r0' a ox [gA, α, acct a.id α, acct ox α] (lvPostArg 2 "buyer" 5 10 6 α gA a.id 7 β)
  r := note r s!"LE5 A posts X's offer 2 with leg 6 α through its grant of transfer 5: {vp5}; offer 2 present {present rp5.st.host ox 2}"
    (vp5.startsWith "refused" && !present rp5.st.host ox 2 && bal rp5.st.host ox α == 5 &&
      bal rp5.st.host a.id α == 15)
  -- LE7 (LANG-82) the judge reads the legs: on the World before LE1, B posts Y's offer 3 (seller [8,12],
  -- compliant with X's at price 9) giving 1 β where X wants 7 β; the fuse naming it is refused by name,
  -- and nothing moves. LE7b: Y's offer 4 gives 7 β but wants 6 α where X gives 5 α.
  let (rp7, vp7) := post r0' b oy [gB, β, acct b.id β, acct oy β] (lvPostArg 3 "seller" 8 12 1 β gB b.id 5 α)
  let w7 := rp7.st.host
  let (rf7, vf7) := fuse rp7 cells (pinOffer w7 ox 0 ++ pinOffer w7 oy 3) (lfFuseArg ox oy 9 0 3 (some gY))
  r := note r s!"LE7 B posts Y's offer 3 (seller [8,12], gives 1 β, wants 5 α: {vp7}); X.fuse naming it at price 9 (X wants 7 β): {vf7}; X holds {bal rf7.st.host ox α} α, Y {bal rf7.st.host oy β} β"
    (vp7 == "admitted" && refusedBy vf7 "fuse" "unfairLegs" && bal rf7.st.host ox α == 5 &&
      bal rf7.st.host oy β == 9 && present rf7.st.host ox 0 && present rf7.st.host oy 3)
  let (rb7, rv7) := mk r0' b [oy, acct b.id β] (.grant (acct b.id β) oy [.transfer 7] none)
  let some gB' := rv7.2 | return note r s!"LE7b second deposit grant: {rv7.1}" false
  let (rp7b, vp7b) := post rb7 b oy [gB', β, acct b.id β, acct oy β] (lvPostArg 4 "seller" 8 12 7 β gB' b.id 6 α)
  let w7b := rp7b.st.host
  let (rf7b, vf7b) := fuse rp7b cells (pinOffer w7b ox 0 ++ pinOffer w7b oy 4) (lfFuseArg ox oy 9 0 4 (some gY))
  r := note r s!"LE7b B posts Y's offer 4 (gives 7 β, wants 6 α: {vp7b}); X.fuse naming it (X gives 5 α): {vf7b}; X holds {bal rf7b.st.host ox α} α"
    (vp7b == "admitted" && refusedBy vf7b "fuse" "unfairLegs" && bal rf7b.st.host ox α == 5 &&
      present rf7b.st.host oy 4)
  -- LE6 (LANG-80) the session row LE1 left under X is retired from its deadline on, not before
  r := sessionRetireRows "LE6" prog { r with st := rf1.st } a [pkg, ox] ox sd
  return r

/-- A fresh session for the LV rows. -/
def offerEscrowSession : Run :=
  let X := ctxWith langProgram
  let fk := [("lv-a".toUTF8, "lv-a-next".toUTF8), ("lv-b".toUTF8, "lv-b-next".toUTF8)]
  match genesis X Sim.worldName (Sim.nonceOf 10) 100000000
      (fk.map fun (k, n) => (k, nextKeyDigest X n)) with
  | .error e => note { st := { rng := ⟨1⟩, host := World.genesis X.env 0 0, members := [] } }
      s!"LE genesis: {e.name}" false
  | .ok g =>
    let ms := fk.zipIdx.map fun ((k, n), i) => (⟨founderId X g.origin i, k, n⟩ : Sim.Member)
    lvRows { st := { rng := ⟨1⟩, host := g, members := ms } }
      (ms.headD ⟨0, .empty, .empty⟩) (ms.getD 1 ⟨0, .empty, .empty⟩)

end Nanodregg.Lang.Journey
