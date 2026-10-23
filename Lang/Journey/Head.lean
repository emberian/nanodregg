/-
# Lang.Journey.Head — §HD/§RC: `Std.head` and the `(receipt)` column through the real receivers (E5)

Two Worlds of the Sim: A, whose founder commits one call, and B, whose founder installs
`Std.headPackage` and the deployed acceptor (`client/tests/fixtures/foreign/Accept.ob`, the one the
Rust rows X1–X5 run). Every row is a call through `Receive.submit` (`receive` then `World.admit`)
with `Lang.program` as the kernel's `Program`, instantiated with the deployed receipt check
(`Protocol.Foreign.check`) at the Sim's parameters, as `Host.Deployed.X` instantiates it at the
deployed ones. A row passes only when its verdict is the expected one.

* HD0 B installs `Std.head` (its id is `Protocol.Foreign.headPackageId`), creates a head object
  holding A's head at `{height 10, steps 20}`, and posts an honest advance `{height 11, steps 21}`.
* HD1 `otherWorld`: `Std.head`'s methods never write `world`, so a change of it is reached through a
  DATA object judged by the head law (`create none [Std.head]`): a write of its `world` is refused
  by the law; HD1c the write of an honest advance to the same object is admitted.
* HD2 `staleHead` (a post below the held step count), HD3 `forkedHead` (a post at the held step
  count with other roots), HD4 `badHead` (a higher step count at a lower height), HD5 `badFork` (a
  fork naming the held roots as the other's), each judged on the World after HD0; HD5c the honest
  fork is admitted and the head reads back forked; HD6 a post to the forked head is refused
  `forkedHead` (frozen).
* RC0 B trusts a head object holding A's real head; `accept` with A's receipt of its committed call
  is admitted, and the acceptance row is keyed by A's transaction id at the committed height.
* RC1 `headDead`: the trusted key names a RETIRED cell (B's revoked grant: no Body retires an object
  in nano, so a dead anchor is a retired cell of another kind), read through the caller's pins.
* RC2 `notCommitted`: the receipt of a call A never committed (it shows `absent`).
-/
import Lang.Journey
import Lang.StdHead
import Protocol.Foreign

namespace Nanodregg.Lang.Journey

open Nanodregg.Kernel Nanodregg.Kernel.Receive

/-- `Lang.program` with the deployed receipt check at the Sim's parameters. -/
def headProgram : Program D :=
  Lang.program Sim.dc.bytes Sim.digestOf (Protocol.Foreign.check Sim.env Sim.dc)

/-- The deployed acceptor's source, read by `lang-journey` from the repository root. -/
def acceptSourcePath : System.FilePath := "client" / "tests" / "fixtures" / "foreign" / "Accept.ob"

def hdDig (n : D) : ByteArray := Sim.dc.bytes n

def hdAtArg (h : Nat) (roots : ByteArray) (s : Nat) : Option ByteArray :=
  Wire.encodeData Std.headAtTy (Std.atRec h roots s)

def hdForkArg (other : ByteArray) (s : Nat) : Option ByteArray :=
  Wire.encodeData Std.forkArgTy (.record [("other", .digest other), ("steps", .nat s)])

/-- A head object's state slots, holding `at {h, roots, s}` of World `w`. -/
def hdSeed (h : Nat) (roots : ByteArray) (s : Nat) (w : ByteArray) : Option Slots :=
  stateSlots (recordRow Std.headStateTy) [("head", .inj "at" (Std.atRec h roots s)), ("world", .digest w)] 0

/-- A refusal of the run's program whose reason names `why`. -/
def programRefused (v why : String) : Bool :=
  v.startsWith "refused program" && (v.splitOn why).length > 1

def headRows (r0 : Run) (b : Sim.Member) (rA0 : Run) (a : Sim.Member) (acceptText : String) : Run := Id.run do
  let prog := headProgram
  let X := ctxWith prog
  let mut r := r0
  -- World A: one call committed, one never sent
  let cA := Sim.signed rA0.st a a.key (Sim.S.pinsFor rA0.st.host [a.id]) (.create none [] [])
  let cNever := Sim.signed rA0.st a a.key (Sim.S.pinsFor rA0.st.host [a.id])
    (.create none [] [(stateBase, "never".toUTF8)])
  let (rA, vA, _) := go prog rA0 cA
  let wA := rA.st.host
  let worldA := hdDig wA.origin
  let receiptOf (c : Call D) : Option ByteArray :=
    Protocol.Receipt.bytes Sim.env Sim.dc (Protocol.Receipt.build Sim.env wA (txIdOf X c))
  -- B installs Std.head
  let some hb := Wire.encodePackage Std.headPackage | return note r "HD0 Std.head has no bytes" false
  let (r1, v1, t1) := go prog r (Sim.signed r.st b b.key (Sim.S.pinsFor r.st.host [b.id]) (.install hb))
  let some hpkg := t1.bind fun t => (createdIds t).head? | return note r1 s!"HD0 install Std.head: {v1}" false
  r := r1
  let create (r : Run) (pkg : Option D) (laws : List D) (seed : Option Slots) : Run × String × Option D :=
    match seed with
    | none => (r, "no bytes", none)
    | some s =>
      let (r', v, t) := go prog r (Sim.signed r.st b b.key (Sim.S.pinsFor r.st.host ([b.id] ++ pkg.toList ++ laws))
        (.create pkg laws s))
      (r', v, t.bind fun t => (createdIds t).head?)
  let invoke (r : Run) (obj : D) (cells : List D) (m : Nat) (arg : Option ByteArray)
      (ranges : List (RangeRead D) := []) : Run × String :=
    match arg with
    | none => (r, "no bytes")
    | some x =>
      let (r', v, _) := go prog r (signedRows r.st b (Sim.S.pinsFor r.st.host ([b.id, obj] ++ cells)) [] ranges
        (.invoke obj m x 1000000 none))
      (r', v)
  let held (r : Run) (obj : D) : Option HeadView :=
    (r.st.host.live Sim.env obj).bind (headView Sim.digestOf (hdDig hpkg))
  let R1 := hdDig 101
  let R2 := hdDig 102
  let R3 := hdDig 103
  let R4 := hdDig 104
  -- HD0 the head object and an honest advance (Std.head: method 0 `fork`, method 1 `post`)
  let (r2, v2, H?) := create r (some hpkg) [] (hdSeed 10 R1 20 worldA)
  let some H := H? | return note r2 s!"HD0 B creates a head object: {v2}" false
  let (r3, v3) := invoke r2 H [hpkg] 1 (hdAtArg 11 R2 21)
  r := note r3 s!"HD0 B installs Std.head ({v1}; its id is Foreign.headPackageId {hpkg == Protocol.Foreign.headPackageId Sim.env}), creates H holding A's head at \{height 10, steps 20} ({v2}) and posts the advance \{height 11, steps 21} with other roots: {v3}"
    (v1 == "admitted" && v2 == "admitted" && v3 == "admitted" && hpkg == Protocol.Foreign.headPackageId Sim.env &&
      held r2 H == some (.at worldA 10 R1 20) && held r3 H == some (.at worldA 11 R2 21))
  let w0 := r
  -- HD1 / HD1c otherWorld, through a data object judged by the head law
  let (rj, vj, J?) := create w0 none [hpkg] (hdSeed 10 R1 20 worldA)
  let some J := J? | return note rj s!"HD1 B creates a data object under the head law: {vj}" false
  let some otherW := Wire.encodeData .digest (.digest (hdDig 7)) | return note r "HD1 no bytes" false
  let (_, v1w, _) := go prog rj (Sim.signed rj.st b b.key (Sim.S.pinsFor rj.st.host [b.id, J, hpkg])
    (.write J [(1, some otherW)] none))
  r := note r s!"HD1 a data object J judged by the head law ({vj}); a write of its world to another World's: {v1w}"
    (vj == "admitted" && deniedWith v1w "head: otherWorld")
  let some adv := Wire.encodeData Std.headTy (.inj "at" (Std.atRec 11 R2 21)) | return note r "HD1c no bytes" false
  let (rjc, v1c, _) := go prog rj (Sim.signed rj.st b b.key (Sim.S.pinsFor rj.st.host [b.id, J, hpkg])
    (.write J [(0, some adv)] none))
  r := note r s!"HD1c control: a write of J's head to the advance \{height 11, steps 21}: {v1c}"
    (v1c == "admitted" && (rjc.st.host.live Sim.env J).isSome)
  -- HD2–HD5 the law's refusals of a post and a fork, each on the World after HD0
  let (_, v4) := invoke w0 H [hpkg] 1 (hdAtArg 12 R3 19)
  r := note r s!"HD2 a post at \{height 12, steps 19}, below the held 21 steps: {v4}" (deniedWith v4 "head: staleHead")
  let (_, v5) := invoke w0 H [hpkg] 1 (hdAtArg 11 R3 21)
  r := note r s!"HD3 a post at the held step count 21 with other roots: {v5}" (deniedWith v5 "head: forkedHead")
  let (_, v6) := invoke w0 H [hpkg] 1 (hdAtArg 9 R3 22)
  r := note r s!"HD4 a post at \{height 9, steps 22}: more steps, a lower height: {v6}" (deniedWith v6 "head: badHead")
  let (_, v7) := invoke w0 H [hpkg] 0 (hdForkArg R2 21)
  r := note r s!"HD5 a fork naming the held roots as the other poster's: {v7}" (deniedWith v7 "head: badFork")
  r := note r s!"HD2–HD5 left the head as HD0 posted it: {held w0 H == some (.at worldA 11 R2 21)}"
    (held w0 H == some (.at worldA 11 R2 21))
  -- HD5c / HD6 the honest fork, then the frozen head
  let (rf, v8) := invoke w0 H [hpkg] 0 (hdForkArg R3 21)
  r := note r s!"HD5c control: a fork naming other roots at the held step count: {v8}; H reads back forked"
    (v8 == "admitted" && held rf H == some (.forked worldA))
  let (_, v9) := invoke rf H [hpkg] 1 (hdAtArg 12 R4 22)
  r := note r s!"HD6 a post to the forked head \{height 12, steps 22}: {v9}" (deniedWith v9 "head: forkedHead")
  -- RC: the deployed acceptor, over B's head object holding A's real head
  let acc ← match Surface.readPackage acceptText with
    | .ok p => pure p
    | .error e => return note r s!"RC0 read {acceptSourcePath}: {e.text acceptText}" false
  let some ab := Wire.encodePackage acc | return note r "RC0 the acceptor has no bytes" false
  let some hi := relIndex acc.rels "heads" | return note r "RC0 the acceptor has no heads relation" false
  let some hd := acc.rels.lookup "heads" | return note r "RC0 the acceptor has no heads relation" false
  let some ai := relIndex acc.rels "accepted" | return note r "RC0 the acceptor has no accepted relation" false
  let some ad := acc.rels.lookup "accepted" | return note r "RC0 the acceptor has no accepted relation" false
  let (ra1, va1, ta1) := go prog rf (Sim.signed rf.st b b.key (Sim.S.pinsFor rf.st.host [b.id]) (.install ab))
  let some apkg := ta1.bind fun t => (createdIds t).head? | return note r s!"RC0 install the acceptor: {va1}" false
  let (ra2, va2, Acc?) := create ra1 (some apkg) [] (some [])
  let some Acc := Acc? | return note r s!"RC0 B creates the acceptor: {va2}" false
  let (ra3, va3, HA?) := create ra2 (some hpkg) [] (hdSeed wA.height (hdDig (wA.roots Sim.env)) wA.steps worldA)
  let some HA := HA? | return note r s!"RC0 B creates the head object of A's head: {va3}" false
  -- a retired cell: B's grant on the acceptor, revoked
  let (ra4, va4, tg) := go prog ra3 (Sim.signed ra3.st b b.key (Sim.S.pinsFor ra3.st.host [b.id, Acc, HA])
    (.grant Acc HA [.invoke 0] none))
  let some G := tg.bind fun t => (createdIds t).head? | return note r s!"RC1 B's grant: {va4}" false
  let (ra5, va5, _) := go prog ra4 (Sim.signed ra4.st b b.key (Sim.S.pinsFor ra4.st.host [b.id, G]) (.revoke G))
  let cellArg (c : D) : Option ByteArray :=
    Wire.encodeData (.record [("cell", .digest)]) (.record [("cell", .digest (hdDig c))])
  -- acceptor methods, labels ascending: 0 accept, 1 distrust, 2 trust
  let (ra6, va6) := invoke ra5 Acc [apkg] 2 (cellArg HA)
  let (ra7, va7) := invoke ra6 Acc [apkg] 2 (cellArg G)
  let setup := [vA, va1, va2, va3, va4, va5, va6, va7]
  r := note r s!"RC0 setup: A commits one call ({vA}); B installs the acceptor from {acceptSourcePath} (methods {acc.methods}) and creates it, creates HA holding A's head at \{height {wA.height}, steps {wA.steps}}, grants and revokes G, and trusts HA and G: {setup}"
    (setup.all (· == "admitted") && acc.methods == ["accept", "distrust", "trust"])
  let w1 := ra7
  -- the acceptor's signed range over `heads` at the key `k`, at what B sees on `w`
  let rangeAt (w : World D) (k : D) : List (RangeRead D) :=
    match Wire.encodeData (keyWireTy hd 1) (.record [("k0", .digest (hdDig k))]), headOf Sim.env w.rows Acc hi with
    | some pre, some (_, _, _, _, width, _) =>
      match rangeRows Sim.env w.rows Acc hi width pre 1 with
      | some l =>
        let seen := rangePin Sim.env Acc hi width pre (headFloor Sim.env w.rows Acc hi) l
        [{ parent := Acc, rel := hi, pre, most := 1, seen }]
      | none => []
    | _, _ => []
  let acceptArg (rb : Option ByteArray) : Option ByteArray :=
    rb.bind fun x => Wire.encodeData (.record [("receipt", .bytes)]) (.record [("receipt", .bytes x)])
  let txA := hdDig (txIdOf X cA)
  let committedAt : Option Nat := (wA.journalAt Sim.env (txIdOf X cA)).map (·.1)
  let (rc0, vc0) := invoke w1 Acc [apkg, HA] 0 (acceptArg (receiptOf cA)) (rangeAt w1.st.host HA)
  let row := storyRow rc0.st.host Acc ai ad (.record [("tx", .digest txA)])
  r := note r s!"RC0 accept, the range naming HA, with A's receipt of its committed call: {vc0}; an acceptance row at A's transaction id {row.isSome}, A committed the call at height {committedAt}"
    (vc0 == "admitted" && committedAt.isSome &&
      (match row.bind (·.field "height"), committedAt with
       | some (.nat h), some h' => h == h'
       | _, _ => false))
  let (_, vc1) := invoke w1 Acc [apkg, G] 0 (acceptArg (receiptOf cA)) (rangeAt w1.st.host G)
  r := note r s!"RC1 accept, the range naming the retired cell G (pinned), with the same receipt: {vc1}"
    (programRefused vc1 "headDead")
  let (_, vc2) := invoke w1 Acc [apkg, HA] 0 (acceptArg (receiptOf cNever)) (rangeAt w1.st.host HA)
  r := note r s!"RC2 accept, the range naming HA, with A's receipt of a call it never committed (absent): {vc2}"
    (programRefused vc2 "notCommitted")
  return r

/-- A fresh session for the HD and RC rows: World B (the rows' World) and World A (the foreign one). -/
def headSession (acceptText : String) : Run :=
  let X := ctxWith headProgram
  let empty : Run := { st := { rng := ⟨1⟩, host := World.genesis X.env 0 0, members := [] } }
  let one (name next : String) (nonce : Nat) : Except String (Run × Sim.Member) :=
    match genesis X Sim.worldName (Sim.nonceOf nonce) 100000000 [(name.toUTF8, nextKeyDigest X next.toUTF8)] with
    | .error e => .error e.name
    | .ok g =>
      let m : Sim.Member := ⟨founderId X g.origin 0, name.toUTF8, next.toUTF8⟩
      .ok ({ st := { rng := ⟨1⟩, host := g, members := [m] } }, m)
  match one "hd-b" "hd-b-next" 11, one "hd-a" "hd-a-next" 12 with
  | .ok (rB, b), .ok (rA, a) => headRows rB b rA a acceptText
  | .error e, _ => note empty s!"HD genesis B: {e}" false
  | _, .error e => note empty s!"HD genesis A: {e}" false

end Nanodregg.Lang.Journey
