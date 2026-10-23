/-
# Lang.Journey.Offer — §LF: `Std.offer` through the real receivers (PROT-6, fork M)

`P := offerPackage ["price"] ["buyer", "seller"]`, installed by A. A's object X and the matcher Z,
B's object Y, all of `P`. Each owner invites Z by granting it `[.invoke take]` on its own object;
`Z.fuse` returns two invokes of `take` carrying ONE deal byte string, one to X through A's grant
and one to Y through B's. Every row is a call through `Receive.submit` (`receive` then
`World.admit`) with `Lang.program` as the kernel's `Program`, and passes only when its verdict is
the expected one. LF2–LF4, LF6 and LF8 are judged on the World before LF1 (refused calls leave it as it
was); LF5 and LF7 on the World after LF1. LF6a–c and LF7 are controls of the kernel (KERNEL-25's
authority, the tree's `revisited`), not teeth of the package.
-/
import Lang.Journey
import Lang.StdOffer

namespace Nanodregg.Lang.Journey

open Nanodregg.Kernel Nanodregg.Kernel.Receive

/-- What a session row captures: the pair `{a, b}` and the terms `{price}`. -/
def lfCapture (a b : D) (price : Nat) : Data :=
  .record [("pair", .record [("a", .digest (Sim.dc.bytes a)), ("b", .digest (Sim.dc.bytes b))]),
    ("theta", .record [("price", .nat price)])]

/-- The deal `take` decodes: the offer key it names for `a` and for `b`, the pair, the terms. -/
def lfDeal (a b : D) (price ka kb : Nat) : Data :=
  .record [("keys", .record [("a", .nat ka), ("b", .nat kb)]),
    ("pair", .record [("a", .digest (Sim.dc.bytes a)), ("b", .digest (Sim.dc.bytes b))]),
    ("theta", .record [("price", .nat price)])]

def lfOpt : Option D → Data
  | some g => .inj "some" (.digest (Sim.dc.bytes g))
  | none => .inj "none" (.record [])

/-- `fuse {deal, x, y, viaX, viaY}`, the deal as its bytes at `offerTakeArg ["price"]`. -/
def lfFuseArg (deal : Data) (x y : D) (viaX viaY : Option D) : Option ByteArray := do
  let d ← Wire.encodeData (Std.offerTakeArg ["price"]) deal
  Wire.encodeData Std.offerFuseArg (.record [("deal", .bytes d), ("viaX", lfOpt viaX), ("viaY", lfOpt viaY),
    ("x", .digest (Sim.dc.bytes x)), ("y", .digest (Sim.dc.bytes y))])

/-- `post {n, role, terms}` with the one term `price` in `[lo, hi]`. -/
def lfPostArg (n : Nat) (role : Label) (lo hi : Nat) : Option ByteArray :=
  Wire.encodeData (Std.offerPostArg ["price"] ["buyer", "seller"])
    (.record [("n", .nat n), ("role", .inj role (.record [])),
      ("terms", .record [("price", .record [("hi", .nat hi), ("lo", .nat lo)])])])

def lfOfferKey (n : Nat) : Data := .record [("n", .nat n)]

def lfRows (r0 : Run) (a b : Sim.Member) : Run := Id.run do
  let prog := langProgram
  let mut r := r0
  let P ← match Std.offerPackage ["price"] ["buyer", "seller"] with
    | .ok p => pure p
    | .error e => return note r s!"LF0 offerPackage refused: {e.name}" false
  let some od := P.rels.lookup "offer" | return note r "LF0 P has no offer relation" false
  let some sd := P.rels.lookup "session" | return note r "LF0 P has no session relation" false
  let some pb := Wire.encodePackage P | return note r "LF0 P has no bytes" false
  let (r1, v1, t1) := go prog r (Sim.signed r.st a a.key (Sim.S.pinsFor r.st.host [a.id]) (.install pb))
  let some pkg := t1.bind fun t => (createdIds t).head? | return note r1 s!"LF0 install P: {v1}" false
  r := r1
  -- an object of `oid`, born empty (P's state is the empty record)
  let create (r : Run) (m : Sim.Member) (oid : D) : Run × String × Option D :=
    let (r', v, t) := go prog r (Sim.signed r.st m m.key (Sim.S.pinsFor r.st.host [m.id, oid]) (.create (some oid) [] []))
    (r', v, t.bind fun t => (createdIds t).head?)
  let (rx, vx, X?) := create r a pkg
  let (rz, vz, Z?) := create rx a pkg
  let (ry, vy, Y?) := create rz b pkg
  let some X := X? | return note rx s!"LF0 A creates X: {vx}" false
  let some Z := Z? | return note rz s!"LF0 A creates Z: {vz}" false
  let some Y := Y? | return note ry s!"LF0 B creates Y: {vy}" false
  r := ry
  let post (r : Run) (m : Sim.Member) (oid obj : D) (arg : Option ByteArray) : Run × String :=
    match arg with
    | none => (r, "no bytes")
    | some x =>
      let (r', v, _) := go prog r (Sim.signed r.st m m.key (Sim.S.pinsFor r.st.host [m.id, obj, oid])
        (.invoke obj Std.offerPostIx x 100000 none))
      (r', v)
  let (rpx, vpx) := post r a pkg X (lfPostArg 0 "buyer" 5 10)
  let (rpy, vpy) := post rpx b pkg Y (lfPostArg 0 "seller" 8 12)
  -- two more of Y's offers, so the pin, not the argument, chooses the offer a take judges
  let (rpy1, vpy1) := post rpy b pkg Y (lfPostArg 1 "seller" 11 12)
  let (rpy2, vpy2) := post rpy1 b pkg Y (lfPostArg 2 "buyer" 8 12)
  r := rpy2
  let grant (r : Run) (m : Sim.Member) (obj : D) (rights : List Right) : Run × String × Option D :=
    let (r', v, t) := go prog r (Sim.signed r.st m m.key (Sim.S.pinsFor r.st.host [m.id, obj, Z]) (.grant obj Z rights none))
    (r', v, t.bind fun t => (createdIds t).head?)
  let (rgx, vgx, gX?) := grant r a X [.invoke Std.offerTakeIx]
  let (rgy, vgy, gY?) := grant rgx b Y [.invoke Std.offerTakeIx]
  let (rgp, vgp, gP?) := grant rgy b Y [.invoke Std.offerPostIx]
  let setup := [vx, vz, vy, vpx, vpy, vpy1, vpy2, vgx, vgy, vgp]
  let some gX := gX? | return note rgx s!"LF0 A grants Z take on X: {vgx}" false
  let some gY := gY? | return note rgy s!"LF0 B grants Z take on Y: {vgy}" false
  let some gP := gP? | return note rgp s!"LF0 B grants Z post on Y: {vgp}" false
  r := rgp
  r := note r s!"LF0 A installs P = offerPackage [price] [buyer, seller] (methods {P.methods}, relations {P.rels.map (·.1)}) and creates X and the matcher Z; B creates Y; A posts X's offer 0 buyer price [5,10]; B posts Y's offers 0 seller [8,12], 1 seller [11,12], 2 buyer [8,12]; A grants Z [invoke take] on X, B the same on Y (the invitations), and B grants Z [invoke post] on Y: {setup}"
    (v1 == "admitted" && setup.all (· == "admitted") && P.methods == Std.offerMethods &&
      P.rels.map (·.1) == ["offer", "session"])
  let w0 := r
  let pinOffer (w : World D) (obj : D) (n : Nat) := hole_pinAt obj w 0 od (lfOfferKey n)
  let present (w : World D) (obj : D) (n : Nat) : Bool := (storyRow w obj 0 od (lfOfferKey n)).isSome
  let sessionKey : Data := .record [("agent", .digest (Sim.dc.bytes a.id)), ("notBefore", .nat 0)]
  -- a session row's `captured`, as its bytes at the log's capture type (the comparison is of bytes)
  let capTy := Std.activityCaptured [Std.offerSettlePlan ["price"]]
  let captured (w : World D) (obj : D) : Option ByteArray :=
    ((storyRow w obj 1 sd sessionKey).bind (·.field "captured")).bind (Wire.encodeData capTy)
  -- A's call of Z.fuse: `cells` pinned besides A and the package, `rows` the row pins
  let fuse (r : Run) (cells : List D) (rows : List (RowSlot D × D)) (arg : Option ByteArray) : Run × String :=
    match arg with
    | none => (r, "no bytes")
    | some x =>
      let (r', v, _) := go prog r (signedRows r.st a (Sim.S.pinsFor r.st.host ([a.id, pkg] ++ cells)) rows []
        (.invoke Z Std.offerFuseIx x 1000000 none))
      (r', v)
  let allCells := [Z, X, Y, gX, gY]
  let rowsAt (w : World D) (ny : Nat) := pinOffer w X 0 ++ pinOffer w Y ny
  let arg1 := lfFuseArg (lfDeal X Y 9 0 0) X Y (some gX) (some gY)
  -- LF1 the fuse: both takes judge the one deal; each retracts its own offer and logs a session
  let (rf1, vf1) := fuse w0 allCells (rowsAt w0.st.host 0) arg1
  let w1 := rf1.st.host
  let cX := captured w1 X
  let cY := captured w1 Y
  let want : Option ByteArray := Wire.encodeData capTy (.inj "settle" (lfCapture X Y 9))
  r := note rf1 s!"LF1 A invokes Z.fuse \{deal = the bytes of \{keys \{a 0, b 0}, pair \{a X, b Y}, theta \{price 9}}, x X, y Y, viaX (A's grant), viaY (B's grant)} pinning Z, X, Y, both grants and both offer rows: {vf1}; read back: X's offer 0 present {present w1 X 0}, Y's offer 0 present {present w1 Y 0}; session rows under X and Y {cX.isSome && cY.isSome}, their captured values equal {cX == cY} (and the forwarded deal {cX == want})"
    (vf1 == "admitted" && !present w1 X 0 && !present w1 Y 0 && present w1 Y 1 && present w1 Y 2 &&
      cX.isSome && cX == cY && cX == want && want.isSome)
  -- LF2 / LF2r the judge, on the World before LF1
  let (_, vf2) := fuse w0 allCells (rowsAt w0.st.host 1) (lfFuseArg (lfDeal X Y 9 0 1) X Y (some gX) (some gY))
  r := note r s!"LF2 the same call naming and pinning Y's offer 1, seller [11,12] (price 9 outside it): {vf2}; read back on the unchanged World: X's offer 0 and Y's offer 1 stand {present w0.st.host X 0 && present w0.st.host Y 1}"
    (refusedBy vf2 "take" "notCompliant" && present w0.st.host X 0 && present w0.st.host Y 1)
  let (_, vf2r) := fuse w0 allCells (rowsAt w0.st.host 2) (lfFuseArg (lfDeal X Y 9 0 2) X Y (some gX) (some gY))
  r := note r s!"LF2r the same call naming and pinning Y's offer 2, buyer [8,12] (both buyer): {vf2r}"
    (refusedBy vf2r "take" "sameRole")
  -- LF8 the deal names the offer: the matcher pins Y's offer 0 where the deal names Y's offer 1
  let (_, vf8) := fuse w0 allCells (rowsAt w0.st.host 0) (lfFuseArg (lfDeal X Y 9 0 1) X Y (some gX) (some gY))
  r := note r s!"LF8 the deal names Y's offer 1 and the call pins Y's offer 0 (compliant with X's at price 9): {vf8}; read back on the unchanged World: X's offer 0 and Y's offers 0 and 1 stand {present w0.st.host X 0 && present w0.st.host Y 0 && present w0.st.host Y 1}"
    (refusedBy vf8 "take" "offerNotNamed" && present w0.st.host X 0 && present w0.st.host Y 0 &&
      present w0.st.host Y 1)
  -- LF3 / LF3r the peer read: the peer's CELL unpinned is the kernel's `unpinned`; its ROW unpinned is the take's
  let (_, vf3) := fuse w0 [Z, X, gX, gY] (rowsAt w0.st.host 0) arg1
  r := note r s!"LF3 LF1's call without pinning Y's cell: {vf3}"
    (vf3.startsWith "refused unpinned" && (vf3.splitOn s!"unpinned {reprStr Y}").length > 1)
  let (_, vf3r) := fuse w0 allCells (pinOffer w0.st.host X 0) arg1
  r := note r s!"LF3r LF1's call with Y's cell pinned and Y's offer row not pinned: {vf3r}"
    (refusedBy vf3r "take" "peerRowUnpinned")
  -- LF4 the peer is an object of another package: the same generator at another offer limit
  let P' ← match Std.offerPackage ["price"] ["buyer", "seller"] 63 with
    | .ok p => pure p
    | .error e => return note r s!"LF4 offerPackage refused: {e.name}" false
  let some pb' := Wire.encodePackage P' | return note r "LF4 P' has no bytes" false
  let (rq1, vq1, tq1) := go prog w0 (Sim.signed w0.st b b.key (Sim.S.pinsFor w0.st.host [b.id]) (.install pb'))
  let some pkg' := tq1.bind fun t => (createdIds t).head? | return note r s!"LF4 install P': {vq1}" false
  let (rq2, vq2, W?) := create rq1 b pkg'
  let some W := W? | return note r s!"LF4 B creates W of P': {vq2}" false
  let (rq3, vq3) := post rq2 b pkg' W (lfPostArg 0 "seller" 8 12)
  let (_, vf4) := fuse rq3 (allCells ++ [W]) (pinOffer rq3.st.host X 0 ++ pinOffer rq3.st.host W 0)
    (lfFuseArg (lfDeal X W 9 0 0) X Y (some gX) (some gY))
  r := note r s!"LF4 B installs P' = offerPackage [price] [buyer, seller] 63 ({vq1}), creates W of P' ({vq2}) and posts W's offer 0 seller [8,12] ({vq3}); LF1's call with pair \{a X, b W}: {vf4}"
    (vq1 == "admitted" && vq2 == "admitted" && vq3 == "admitted" && pkg' != pkg &&
      vf4.startsWith "refused program" && (vf4.splitOn "peer: another package").length > 1)
  -- LF5 the offer is consumed once per standing row; the grant is not spent
  let (_, vf5) := fuse rf1 allCells (rowsAt w1 0) arg1
  r := note r s!"LF5 LF1's call again on the World after LF1, pinning the now-absent offer rows: {vf5}; A's grant gX and B's grant gY still live {(w1.live Sim.env gX).isSome && (w1.live Sim.env gY).isSome}"
    (refusedBy vf5 "take" "noOffer" && (w1.live Sim.env gX).isSome && (w1.live Sim.env gY).isSome)
  -- LF6 controls of KERNEL-25: the name follows `viaY`
  let (_, vf6a) := fuse w0 allCells (rowsAt w0.st.host 0) (lfFuseArg (lfDeal X Y 9 0 0) X Y (some gX) none)
  r := note r s!"LF6a control: LF1's call with viaY none: {vf6a}" (vf6a.startsWith "refused noGrant")
  let (_, vf6b) := fuse w0 (allCells ++ [gP]) (rowsAt w0.st.host 0) (lfFuseArg (lfDeal X Y 9 0 0) X Y (some gX) (some gP))
  r := note r s!"LF6b control: LF1's call with viaY B's live grant to Z of [invoke post] only: {vf6b}"
    (vf6b.startsWith "refused grantRight" && (vf6b.splitOn s!"grantRight {reprStr gP}").length > 1)
  let (_, vf6c) := fuse w0 [Z, X, Y, gX] (rowsAt w0.st.host 0) arg1
  r := note r s!"LF6c control: LF1's call with B's take grant not pinned: {vf6c}"
    (vf6c.startsWith "refused unpinned" && (vf6c.splitOn s!"unpinned {reprStr gY}").length > 1)
  -- LF7 control: the matcher cannot be a party (the tree visits an object once)
  let (_, vf7) := fuse rf1 allCells (rowsAt w1 0) (lfFuseArg (lfDeal Z Y 9 0 0) Z Y (some gX) (some gY))
  r := note r s!"LF7 control: Z.fuse naming Z itself as x: {vf7}"
    (vf7.startsWith "refused revisited" && (vf7.splitOn s!"revisited {reprStr Z}").length > 1)
  return r

/-- A fresh session for the LF rows. -/
def offerSession : Run :=
  let X := ctxWith langProgram
  let fk := [("lf-a".toUTF8, "lf-a-next".toUTF8), ("lf-b".toUTF8, "lf-b-next".toUTF8)]
  match genesis X Sim.worldName (Sim.nonceOf 9) 100000000
      (fk.map fun (k, n) => (k, nextKeyDigest X n)) with
  | .error e => note { st := { rng := ⟨1⟩, host := World.genesis X.env 0 0, members := [] } }
      s!"LF genesis: {e.name}" false
  | .ok g =>
    let ms := fk.zipIdx.map fun ((k, n), i) => (⟨founderId X g.origin i, k, n⟩ : Sim.Member)
    lfRows { st := { rng := ⟨1⟩, host := g, members := ms } }
      (ms.headD ⟨0, .empty, .empty⟩) (ms.getD 1 ⟨0, .empty, .empty⟩)

end Nanodregg.Lang.Journey
