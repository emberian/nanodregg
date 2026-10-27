/-
# Lang.Proofs.StdOfferFuse — what a signed fuse seals (PROT-6, LANG-77)

* `fuse_run_sound` (`Lang.program`'s run of a party's `fuse`): a returned fuse decoded
  `{keys, pair, theta, via}`, read its own pinned offer and its peer's (the declared peer read),
  found its own the one the deal names for it (`NamedKey`) and the two `JointOk` at θ, its row acts
  are exactly its own retract and its own session insert, and its ONE call is
  `invoke peer take db budget via`, where `db` is the ENCODING of `{keys, pair, theta}`, the deal
  it judged (LANG-77: the runtime encodes the value the method returned; `encodeData_of_conforms`).

A signed call invoking `x'.fuse` of the generated package `offerPackageOf …`, its arguments naming
the pair `{x', y'}`, both objects of that one package, which `receive` turns into a Turn `t`:

* `fuse_atomic`: `t.rows` holds the retract of `x'`'s offer row AND the retract of `y'`'s, each at
  the key the deal NAMES for that party (`NamedKey`): neither party can choose which of the other's
  standing offers the fuse consumes.
* `jointLaw_sound`: `y'`'s take decoded the very `{keys, pair, theta}` `x'` judged (one value,
  encoded once by `x'`'s run: no third party holds the bytes, nothing forwarded is trusted), each
  read its own offer and its peer's, each found `JointOk` of what it read (two evaluations of one
  generated term), the pair names exactly the two parties, the two runs read the same two pinned
  rows, and the two session inserts carry the same value bytes.
* `invitation_once`: once the Turn is admitted, both offer rows the runs read are absent.

All three are about the FUSE call. The owner can root-invoke its own `take` with no fuse (a nested
call's principal is the grant's issuer, so `take` cannot tell), and one session row is not a fuse.
A fuse in which the peer's take refuses derives no Turn: that branch is "no `receive` result", true
of every refusal, and is no conjunct here.
-/
import Lang.Proofs.DispatchRows
import Lang.Proofs.PeerRead
import Lang.Proofs.StdOffer
import Lang.Proofs.CallLive

namespace Nanodregg.Lang.Std

section fuser
open Nanodregg.Lang Nanodregg.Kernel Nanodregg.Kernel.Receive

private theorem slot_c1 : slotLabels "c" 1 = ["c0"] := by decide
private theorem slot_p1 : slotLabels "p" 1 = ["p0"] := by decide
private theorem slot_e2 : slotLabels "e" 2 = ["e0", "e1"] := by decide

/-- A call's `via` field read as the kernel reads it: no grant, or a grant that is a digest of the World. -/
def ViaReads {D : Type} (digestOf : ByteArray → Option D) (v : Data) (g : Option D) : Prop :=
  (v = .inj "none" (.record []) ∧ g = none) ∨ ∃ b d, v = .inj "some" (.digest b) ∧ digestOf b = some d ∧ g = some d

theorem viaReads_of {D : Type} {digestOf : ByteArray → Option D} {v : Data} {g : Option D}
    (hv : Conforms v (optTy .digest)) (h : optOf (digestAt digestOf "via") "via" v = .ok g) :
    ViaReads digestOf v g := by
  rcases conforms_opt hv with rfl | ⟨z, rfl, hz⟩
  · simp [optD, optOf] at h
    exact .inl ⟨rfl, h.symm⟩
  · cases hz with
    | @digest b _ =>
      cases hb : digestOf b with
      | none => simp [optD, optOf, digestAt, hb, Except.map] at h
      | some d =>
        simp [optD, optOf, digestAt, hb, Except.map] at h
        exact .inr ⟨b, d, rfl, hb, h.symm⟩

/-! ## The fuse's signature -/

private theorem fuse_rowsOf (theta roles : List Label) (ol sl : Nat) :
    rowsOf (offerRels theta roles ol sl) (offerTakeRows (offerRels theta roles ol sl)) =
      some (offerRead, offerRead) := by
  simp [rowsOf, offerTakeRows, rowsTy, readsTy, offerRead, offerRels, Row.find?, relReadTy, readsOf,
    relReadOf, relReadShape, peerLabel, slot_p1, Row.sort, Row.insert, pointsMax, rangeRowsMax]

/-- The fuse resolves to its declared signature: the deal with `via`, one invoke slot at the take's
argument type, the one offer point read under itself and under its peer, two edits. The slot's
argument type depends on `theta`, so whether the slot checks is read off `h`, not decided. -/
private theorem fuse_resolve {D : Type} {theta roles : List Label} {ol sl pt b : Nat} {x : Label × Sig}
    (h : resolveMethod (D := D) (offerPackageOf theta roles ol sl pt b) offerFuseIx = .ok x) :
    x = ("fuse", ⟨offerFuseArg theta, [offerCallTy theta], offerRead, 2⟩) := by
  have he : editSlotsOf (offerRels theta roles ol sl)
      [("e0", optTy (editTy (offerRels theta roles ol sl))), ("e1", optTy (editTy (offerRels theta roles ol sl)))] =
      some 2 := by simp [editSlotsOf, editsMax, slot_e2]
  have hn : pairNamed (offerFuseArg theta) offerRead = true := by
    simp [pairNamed, offerFuseArg, Row.find?, offerRead]
  have hc := callSlotsOf_one (offerCallTy theta)
  by_cases hok : callSlotOk (offerCallTy theta) = true
  · rw [if_pos hok] at hc
    simp [resolveMethod, offerPackageOf, offerFuseIx, offerMethods, recordRow, Row.find?, methodSig, methodTy,
      resultTy, callsTy, slot_c1, slot_e2, hc, he, fuse_rowsOf, hn] at h
    split at h
    · rename_i sg hsg
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      split at hsg
      · cases hsg; rfl
      · cases hsg
    · simp [throw, throwThe, MonadExceptOf.throw] at h
  · rw [if_neg hok] at hc
    simp [resolveMethod, offerPackageOf, offerFuseIx, offerMethods, recordRow, Row.find?, methodSig, methodTy,
      resultTy, callsTy, slot_c1, slot_e2, hc, he, fuse_rowsOf, throw, throwThe, MonadExceptOf.throw] at h

private theorem fuse_peerReads (theta roles : List Label) (ol sl pt b : Nat) :
    (offerPackageOf theta roles ol sl pt b).peerReads "fuse" = offerRead := by
  simp [Package.peerReads, offerPackageOf, recordRow, Row.find?, methodPeer, methodTy, fuse_rowsOf]

private theorem noRef_fuse (theta roles : List Label) (rels : List (Label × RelDecl)) (od sd : RelDecl) (budget : Nat) :
    NoRef (activityMethod offerStateTy (offerFuseArg theta) (offerTakeRows rels)
      (offerFuseBody theta roles rels od sd budget)) := by
  simp [activityMethod, offerFuseBody, NoRef, NoRefRow, activityResultCalls, activityEdit, resultT, activityKeyTerm,
    noCallT, someCallT, callsT, slot_e2, slot_c1, activityApply, noRef_offerJoint, offerNamedOkT, offerNamedT,
    offerTakeTree, offerUnwrap, offerGate, offerFuseDone, offerFuseCall, offerTakeCall, offerPeerT, offerTakeEdits]

/-- The slot's invoke argument type, read off the slot. -/
theorem slotInvokeArg_offer (theta : List Label) :
    slotInvokeArg (offerCallTy theta) = some (offerTakeArg theta) := rfl

/-! ## The fuse's argument and its call -/

theorem fuseArg_cases {theta : List Label} {ad : Data} (h : Conforms ad (offerFuseArg theta)) :
    ∃ keys pair th via, ad = .record [("keys", keys), ("pair", pair), ("theta", th), ("via", via)] ∧
      Conforms keys offerKeysTy ∧ Conforms pair pairTy ∧ Conforms th (offerThetaTy theta) ∧
      Conforms via (optTy .digest) := by
  cases h with
  | record hr =>
    cases hr with
    | cons h1 hr => cases hr with
      | cons h2 hr => cases hr with
        | cons h3 hr => cases hr with
          | cons h4 hr =>
            cases hr
            exact ⟨_, _, _, _, rfl, h1, h2, h3, h4⟩

/-- The fuse's `ok`-arm environment: payload 0, peer value 1, peer point 2, own value 3, own point 4,
request 5, argument 6, state 7, rows 8. -/
private abbrev fuseOkEnv (rq keys pair th via k o kq q : Data) (state : Val) : Env :=
  .record [] :: q.toVal :: (Data.record [("key", kq), ("val", .inj "some" q)]).toVal ::
    o.toVal :: (Data.record [("key", k), ("val", .inj "some" o)]).toVal :: rq.toVal ::
    (Data.record [("keys", keys), ("pair", pair), ("theta", th), ("via", via)]).toVal :: state ::
    (Data.record [("offer", .record [("p0", .inj "some" (.record [("key", k), ("val", .inj "some" o)]))]),
      ("peer", .record [("offer", .record [("p0", .inj "some" (.record [("key", kq), ("val", .inj "some" q)]))])])]).toVal ::
      []

/-- The peer term's value: `pair.b` when `self` is `pair.a`, else `pair.a`. -/
theorem peerT_eval {lib : List Term} {env : Env} {rq ag : Term} {a b sb : ByteArray}
    (hs : BigStep lib env (.get rq "self") (.ok (.digest sb)))
    (hpa : BigStep lib env (.get ag "pair") (.ok (Data.record [("a", .digest a), ("b", .digest b)]).toVal)) :
    BigStep lib env (offerPeerT rq ag) (.ok (.digest (if sb = a then b else a))) := by
  have hpa' : BigStep lib env (.get (.get ag "pair") "a") (.ok (Data.digest a).toVal) :=
    get_data (d := .record [("a", .digest a), ("b", .digest b)]) (x := .digest a) hpa rfl
  have hpb' : BigStep lib env (.get (.get ag "pair") "b") (.ok (Data.digest b).toVal) :=
    get_data (d := .record [("a", .digest a), ("b", .digest b)]) (x := .digest b) hpa rfl
  have hdeq : BigStep lib env (.prim .deq (.get rq "self") (.get (.get ag "pair") "a"))
      (.ok (.bool (decide (sb = a)))) :=
    BigStep.prim (x := .digest sb) (y := .digest a) hs hpa' (by simp [primEval])
  unfold offerPeerT
  by_cases h : sb = a
  · rw [if_pos h]; exact .iteT (by simpa [h] using hdeq) hpb'
  · rw [if_neg h]; exact .iteF (by simpa [h] using hdeq) hpa'

/-- **What the fuse's calls row means** in the `ok` arm: one invoke of the peer's `take`, its
argument the VALUE `{keys, pair, theta}` of the fuser's own argument. -/
private theorem callsFuse_means {lib : List Term} {theta : List Label} {budget : Nat}
    {rq keys th via k o kq q : Data} {state : Val} {a b sb : ByteArray}
    (hself : rq.field "self" = some (.digest sb))
    (hkeys : Conforms keys offerKeysTy)
    (hpair : Conforms (Data.record [("a", .digest a), ("b", .digest b)]) pairTy)
    (hth : Conforms th (offerThetaTy theta)) (hvia : Conforms via (optTy .digest)) {W : Val}
    (hW : BigStep lib (fuseOkEnv rq keys (.record [("a", .digest a), ("b", .digest b)]) th via k o kq q state)
      (callsT [someCallT (offerCallTy theta) (offerFuseCall theta budget (.var 5) (.var 6))]) (.ok W)) :
    Means lib (callsTy [offerCallTy theta]) W
      (.record [("c0", .inj "some" (.inj "invoke" (.record [
        ("args", .record [("keys", keys), ("pair", .record [("a", .digest a), ("b", .digest b)]), ("theta", th)]),
        ("budget", .nat budget), ("method", .nat offerTakeIx),
        ("obj", .digest (if sb = a then b else a)), ("via", via)])))]) := by
  unfold callsT at hW
  cases hW
  simp only [callsTy, List.length_cons, List.length_nil, Nat.zero_add, slot_c1, List.map, List.zip, suspend,
    offerFuseCall, offerTakeCall]
  have hf : Row.find? "invoke" ((callArms (some (offerTakeArg theta))).filter
      fun x => x.1 == "invoke" || ([] : List Label).contains x.1) = some (invokeArm (offerTakeArg theta)) := rfl
  have hs : BigStep lib (fuseOkEnv rq keys (.record [("a", .digest a), ("b", .digest b)]) th via k o kq q state)
      (.get (.var 5) "self") (.ok (.digest sb)) :=
    get_data (x := .digest sb) (BigStep.var (i := 5) rfl) hself
  have hpa : BigStep lib (fuseOkEnv rq keys (.record [("a", .digest a), ("b", .digest b)]) th via k o kq q state)
      (.get (.var 6) "pair") (.ok (Data.record [("a", .digest a), ("b", .digest b)]).toVal) :=
    get_data (ℓ := "pair") (x := .record [("a", .digest a), ("b", .digest b)]) (BigStep.var (i := 6) rfl) rfl
  refine .record .record (.cons (.inj (.inj .record)) ?_ .nil)
  exact .inj rfl (.inj hf (.record .record
    (.cons .record (.record .record
      (.cons (get_data (ℓ := "keys") (x := keys) (BigStep.var (i := 6) rfl) rfl) (means_toVal hkeys)
      (.cons hpa (means_toVal hpair)
      (.cons (get_data (ℓ := "theta") (x := th) (BigStep.var (i := 6) rfl) rfl) (means_toVal hth) .nil))))
    (.cons .nat .nat (.cons .nat .nat
    (.cons (peerT_eval hs hpa) .digest
    (.cons (get_data (ℓ := "via") (x := via) (BigStep.var (i := 6) rfl) rfl) (means_toVal hvia) .nil)))))))

/-- A read of one offer point is a record with one field, `offer`. -/
theorem readsData_offer {D : Type} {digestOf : ByteArray → Option D} {rc : Lang.ReceiptCheck} {look : Pinned D}
    {rels : List (Label × RelDecl)} {rv : RowView D} {self : D} {args : Data} {R : Data}
    (h : Nanodregg.Lang.readsData digestOf rc look rels rv self offerRead args = .ok R) :
    ∃ A, R = .record [("offer", A)] := by
  unfold Nanodregg.Lang.readsData offerRead at h
  simp only [List.mapM_cons, List.mapM_nil, except_bind_ok] at h
  obtain ⟨fs, ⟨dl, hdl, h⟩, hR⟩ := h
  obtain ⟨a, ha, h⟩ := h
  simp only [pure, Except.pure, Except.ok.injEq] at ha h hR
  subst ha h hR
  split at hdl
  · split at hdl
    · simp only [except_bind_ok, pure, Except.pure, Except.ok.injEq] at hdl
      obtain ⟨A, -, rfl⟩ := hdl
      exact ⟨A, rfl⟩
    · cases hdl
  · cases hdl

/-- **A party's reads**: its own offer point under `self` and the same read under its peer, the
`peerOf` of the arguments. -/
theorem methodReads_offer {D : Type} {bytesOf : D → ByteArray} {digestOf : ByteArray → Option D} {rc : Lang.ReceiptCheck}
    {look : Pinned D} {pkg : D} {rels : List (Label × RelDecl)} {rv : RowView D} {self : D} {args R : Data}
    (h : Nanodregg.Lang.methodReads bytesOf digestOf rc look pkg rels rv self args offerRead offerRead = .ok R) :
    ∃ p A B, Nanodregg.Lang.peerOf bytesOf digestOf self args = .ok p ∧
      Nanodregg.Lang.readsData digestOf rc look rels rv self offerRead args = .ok (.record [("offer", A)]) ∧
      Nanodregg.Lang.readsData digestOf rc look rels rv p offerRead args = .ok (.record [("offer", B)]) ∧
      R = .record [("offer", A), ("peer", .record [("offer", B)])] := by
  unfold Nanodregg.Lang.methodReads at h
  simp only [except_bind_ok] at h
  obtain ⟨own, hown, h⟩ := h
  obtain ⟨A, rfl⟩ := readsData_offer hown
  rw [if_neg (by simp [offerRead])] at h
  simp only [except_bind_ok] at h
  obtain ⟨⟨⟩, -, p, hp, cell, -, h⟩ := h
  split at h
  · simp only [except_bind_ok] at h
    obtain ⟨⟨⟩, -, pd, hpd, h⟩ := h
    obtain ⟨B, rfl⟩ := readsData_offer hpd
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    have hle : ("offer" : String) ≤ "peer" := by decide
    exact ⟨p, A, B, hp, hown, hpd, by simp [Row.sort, Row.insert, peerLabel, hle]⟩
  · simp [bind, Except.bind] at h

/-- A point read with no `live` and no `receipt` column (`offerRead`) reads nothing of the argument:
the fuser's read of its peer and the peer's read of itself are one read. -/
private theorem relReads_points_args {D : Type} {digestOf : ByteArray → Option D} {rc : Lang.ReceiptCheck}
    {look : Pinned D} {rv : RowView D} {self : D} {i n : Nat} {ℓ : Label} {d : RelDecl} (a1 a2 : Data) :
    Nanodregg.Lang.relReads digestOf rc look rv self i ℓ d ⟨n, none, false, false⟩ a1 =
      Nanodregg.Lang.relReads digestOf rc look rv self i ℓ d ⟨n, none, false, false⟩ a2 := by
  simp only [Nanodregg.Lang.relReads, Nanodregg.Lang.pointData, Nanodregg.Lang.keyColumns, Bool.false_eq_true,
    ↓reduceIte]

theorem readsData_offer_args {D : Type} {digestOf : ByteArray → Option D} {rc : Lang.ReceiptCheck}
    {look : Pinned D} {rels : List (Label × RelDecl)} {rv : RowView D} {self : D} (a1 a2 : Data) :
    Nanodregg.Lang.readsData digestOf rc look rels rv self offerRead a1 =
      Nanodregg.Lang.readsData digestOf rc look rels rv self offerRead a2 := by
  simp only [Nanodregg.Lang.readsData, offerRead, List.mapM_cons, List.mapM_nil, relReads_points_args a1 a2]

/-- The peer the run named is the one the term computes: `pair.b` when `self` is `pair.a`, else
`pair.a`; and the term's digest reads as the peer (`peerOf` succeeded). -/
theorem peer_term {D : Type} {bytesOf : D → ByteArray} {digestOf : ByteArray → Option D} {self p : D}
    {a b : ByteArray} {args : Data}
    (hf : args.field "pair" = some (.record [("a", .digest a), ("b", .digest b)]))
    (h : Nanodregg.Lang.peerOf bytesOf digestOf self args = .ok p) :
    digestOf (if bytesOf self = a then b else a) = some p := by
  unfold Nanodregg.Lang.peerOf at h
  rw [hf] at h
  by_cases hab : a = b
  · subst hab
    simp [bind, Except.bind] at h
  · by_cases ha : a = bytesOf self
    · subst ha
      rw [if_pos rfl]
      simp [hab, bind, Except.bind, pure, Except.pure] at h
      split at h
      · rename_i q hq
        simp only [Except.ok.injEq] at h
        subst h
        exact hq
      · simp [throw, throwThe, MonadExceptOf.throw] at h
    · rw [if_neg (fun e => ha e.symm)]
      by_cases hb : b = bytesOf self
      · subst hb
        simp [ha, bind, Except.bind, pure, Except.pure] at h
        split at h
        · rename_i q hq
          simp only [Except.ok.injEq] at h
          subst h
          exact hq
        · simp [throw, throwThe, MonadExceptOf.throw] at h
      · simp [hab, ha, hb, bind, Except.bind, pure, Except.pure] at h

/-! ## The deployed run of `fuse` -/

/-- **The deployed fuse is sound** (`Lang.program`'s `run` of `fuse` of an object of the generated
package): a run that RETURNED decoded `{keys, pair, theta := th, via}`, built (by the declared peer
read) the rows `{offer: {p0: some {key k, val some o}}, peer: {offer: {p0: some {key kq, val some
q}}}}` from the caller's pins, its own pinned key `k` is the one the deal NAMES for `self`
(`NamedKey`), found `JointOk` of the two pinned offers and θ, makes exactly ONE call —
`invoke p take db budget via'`, `p` the peer `peerOf` named, `db` the bytes of the VALUE
`{keys, pair, theta}` (LANG-77) — and its row acts are exactly the retract of its named offer and the
insert of its own session row. Mutations: PT4 (the call dropped) makes the calls conjunct false;
PT3 (the fuse sends `keys` where it sends `theta`) makes `db` the bytes of another value. -/
theorem fuse_run_sound {D : Type} (bytesOf : D → ByteArray) (digestOf : ByteArray → Option D) {rc : Lang.ReceiptCheck}
    {theta roles : List Label} {ol sl pt budget : Nat}
    {look : Kernel.Receive.Pinned D} {rv : Kernel.Receive.RowView D} {pkg : D} {state : Kernel.Slots}
    {args : ByteArray} {r : Kernel.Receive.Req D} {budget' : Nat} {s : Kernel.Slots}
    {calls : List (Kernel.Receive.Body D)} {rows : List (Kernel.RowSlot D × Kernel.RowAct)} {used : Nat}
    (hR : (offerRoleTy roles).wf = true)
    (hid : digestOf (bytesOf pkg) = some pkg)
    (hp : readPackage look pkg = .ok (offerPackageOf theta roles ol sl pt budget))
    (h : (Lang.program bytesOf digestOf rc).run look rv pkg state offerFuseIx args r budget' =
      .ok (s, calls, rows, used)) :
    ∃ keys pair th via k o kq q p db via' kb sb vb,
      Wire.decodeData (offerFuseArg theta) args =
        .ok (.record [("keys", keys), ("pair", pair), ("theta", th), ("via", via)]) ∧
      methodReads bytesOf digestOf rc look pkg (offerRels theta roles ol sl) rv r.self
        (.record [("keys", keys), ("pair", pair), ("theta", th), ("via", via)]) offerRead offerRead =
        .ok (.record [("offer", .record [("p0", .inj "some" (.record [("key", k), ("val", .inj "some" o)]))]),
          ("peer", .record [("offer", .record [("p0", .inj "some" (.record [("key", kq), ("val", .inj "some" q)]))])])]) ∧
      NamedKey (bytesOf r.self) keys pair k ∧ JointOk (offerLabels theta) o q th ∧
      Nanodregg.Lang.peerOf bytesOf digestOf r.self
        (.record [("keys", keys), ("pair", pair), ("theta", th), ("via", via)]) = .ok p ∧
      Wire.encodeData (offerTakeArg theta) (.record [("keys", keys), ("pair", pair), ("theta", th)]) = some db ∧
      ViaReads digestOf via via' ∧
      calls = [.invoke p offerTakeIx db budget via'] ∧
      keyBytes (offerDecl theta roles ol) k = some kb ∧
      keyBytes (offerSessionDecl theta sl)
        (.record [("agent", .digest (bytesOf r.agent)), ("notBefore", .nat r.notBefore)]) = some sb ∧
      Wire.encodeData (offerSessionDecl theta sl).val
        (.record [("answered", .inj "none" (.record [])),
          ("captured", .inj "settle" (.record [("pair", pair), ("theta", th)]))]) = some vb ∧
      rows = [(.row ⟨r.self, 0, kb⟩, .retract), (.row ⟨r.self, 1, sb⟩, .insert 0 vb)] := by
  change (runMeasuredLive bytesOf digestOf rc look rv pkg state offerFuseIx args r budget').map _ = _ at h
  rw [runMeasuredLive_leaf_closed hid hp rfl rfl] at h
  cases hm : runMeasured bytesOf digestOf rc look rv pkg state offerFuseIx args r budget' with
  | error e => rw [hm] at h; cases h
  | ok x =>
  rw [hm] at h
  obtain ⟨s', calls', rows', t', n'⟩ := x
  simp only [Except.map, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl, rfl⟩ := h
  obtain ⟨S, v, used, c, e, ds, left, es, hS, hrun, hx, hc, hes, hrows⟩ := runMeasured_inv hm
  obtain ⟨L, g, p, ℓ, sg, sd, ad, wd, -, hl, hpg, hres, -, had, -, hwd, rfl⟩ := runSetup_spec hS
  obtain ⟨hpg', f, hlib⟩ := load_top bytesOf digestOf (fuel := closureDepthMax - 1) hid hp hl
  rw [hpg'] at hpg
  cases hpg
  obtain ⟨mty, -, hA⟩ := resolveMethod_spec hres
  have hks := methodSig_slots hA
  have hsig := fuse_resolve hres
  cases hsig
  have hT : Wire.dataTy (offerTakeArg theta) = true :=
    callSlotOk_dataTy (hks _ (List.mem_cons_self ..)) _ (slotInvokeArg_offer theta)
  rw [fuse_peerReads] at hwd
  simp only at hrun hx hes
  obtain ⟨keys, pair, th, via, rfl, hkeys, hpair, hth, hvia⟩ := fuseArg_cases (decodeData_conforms had)
  obtain ⟨X, Y, rfl, hX, hY⟩ := offerTakeRows_cases (methodReads_conforms hwd)
  have hbig := run_bigStep hrun
  have hself : (reqData bytesOf r).field "self" = some (.digest (bytesOf r.self)) := by
    simp [reqData, Data.field, Row.find?]
  have fwd : ∀ {r' : Except Fault Val}, BigStep L.lib
      [(reqData bytesOf r).toVal, (Data.record [("keys", keys), ("pair", pair), ("theta", th), ("via", via)]).toVal, sd.toVal,
        (Data.record [("offer", .record [("p0", X)]), ("peer", .record [("offer", .record [("p0", Y)])])]).toVal]
      (offerFuseBody theta roles (offerRels theta roles ol sl) (offerDecl theta roles ol) (offerSessionDecl theta sl) budget) r' →
      BigStep L.lib [(reqData bytesOf r).toVal, (Data.record [("keys", keys), ("pair", pair), ("theta", th), ("via", via)]).toVal,
        sd.toVal, (Data.record [("offer", .record [("p0", X)]), ("peer", .record [("offer", .record [("p0", Y)])])]).toVal]
        (apply4 g "fuse") r' :=
    fun hb => apply4_method hlib rfl (by simp [Row.find?, activityMethod]) (noRef_fuse _ _ _ _ _ _) hb
  obtain ⟨fs, hfs⟩ : ∃ fs, offerFuseDone theta (offerRels theta roles ol sl) (offerDecl theta roles ol)
      (offerSessionDecl theta sl) budget = .record fs := ⟨_, rfl⟩
  obtain ⟨k, o, kq, q, rfl, rfl, hk, ho, hq, hnk, hok, -, rfl⟩ :=
    offerTakeTree_inv offer_fields hR rfl hth hself hkeys hpair hX hY hfs (fun (f : Term) (e : (none : Option Term) = some f) => nomatch e) fwd hbig
  obtain ⟨a, b, rfl⟩ := pair_shape hpair
  have hM := extract_means _ _ hx
  -- the edits
  have hfE : Row.find? "edits" fs = some (.record ((slotLabels "e"
      (offerTakeEdits theta (offerRels theta roles ol sl) (offerDecl theta roles ol) (offerSessionDecl theta sl)).length).zip
      ((offerTakeEdits theta (offerRels theta roles ol sl) (offerDecl theta roles ol) (offerSessionDecl theta sl)).map
        fun t => someCallT (editTy (offerRels theta roles ol sl)) t))) := by
    simp only [offerFuseDone, activityResultCalls, resultT, Term.record.injEq] at hfs
    subst hfs; rfl
  have hwE := BigStep.get (ℓ := "edits") hbig (.field (find_suspend_of hfE) .record)
  obtain ⟨A, hA, hmA⟩ := means_get hbig hM rfl hwE
  simp [Row.find?] at hA
  subst hA
  have hED := offerTakeEdits_means (lib := L.lib) (od := offerDecl theta roles ol) (sl := sl)
    (env := fuseOkEnv (reqData bytesOf r) keys (.record [("a", .digest a), ("b", .digest b)]) th via k o kq q sd.toVal) rfl
    (get_data (d := .record [("key", k), ("val", .inj "some" o)]) (BigStep.var (i := 4) rfl) rfl) hk
    (get_data (ℓ := "agent") (d := reqData bytesOf r) (x := .digest (bytesOf r.agent)) (BigStep.var (i := 5) rfl) rfl)
    (get_data (ℓ := "notBefore") (d := reqData bytesOf r) (x := .nat r.notBefore) (BigStep.var (i := 5) rfl) rfl)
    (get_data (ℓ := "pair") (x := .record [("a", .digest a), ("b", .digest b)]) (BigStep.var (i := 6) rfl) rfl) hpair
    (get_data (ℓ := "theta") (x := th) (BigStep.var (i := 6) rfl) rfl) hth .record
  have he := means_deterministic hmA hED
  subst he
  obtain ⟨kb, sb, vb, hkb, hsb, hvb, hmap⟩ := offerTake_editsOf (od := offerDecl theta roles ol) rfl hes
  -- the call
  have hfC : Row.find? "calls" fs =
      some (callsT [someCallT (offerCallTy theta) (offerFuseCall theta budget (.var 5) (.var 6))]) := by
    simp only [offerFuseDone, activityResultCalls, resultT, Term.record.injEq] at hfs
    subst hfs; rfl
  have hwC := BigStep.get (ℓ := "calls") hbig (.field (find_suspend_of hfC) .record)
  obtain ⟨A', hA', hmC⟩ := means_get hbig hM rfl hwC
  simp [Row.find?] at hA'
  subst hA'
  have hce := means_deterministic hmC (callsFuse_means (budget := budget) (k := k) (o := o) (kq := kq) (q := q)
    (state := sd.toVal) hself hkeys hpair hth hvia .record)
  subst hce
  obtain ⟨pr, A, B, hpeer, -, -, -⟩ := methodReads_offer hwd
  have hpd := peer_term (bytesOf := bytesOf) (digestOf := digestOf) (self := r.self) (a := a) (b := b)
    (args := .record [("keys", keys), ("pair", .record [("a", .digest a), ("b", .digest b)]), ("theta", th), ("via", via)])
    (by simp [Data.field, Row.find?]) hpeer
  have hdc : Conforms (Data.record [("keys", keys), ("pair", .record [("a", .digest a), ("b", .digest b)]), ("theta", th)])
      (offerTakeArg theta) := .record (.cons hkeys (.cons hpair (.cons hth .nil)))
  obtain ⟨db, hdb⟩ := encodeData_of_conforms hT hdc
  cases hov : optOf (digestAt digestOf "via") "via" via with
  | error e =>
    simp [callsOf, callsOf.go, bodyOf, argsBytes, slotInvokeArg_offer, digestAt, natOf, hdb, hpd, hov, bind,
      Except.bind] at hc
  | ok via' =>
    simp [callsOf, callsOf.go, bodyOf, argsBytes, slotInvokeArg_offer, digestAt, natOf, hdb, hpd, hov, bind,
      Except.bind, pure, Except.pure, Except.map] at hc
    exact ⟨keys, .record [("a", .digest a), ("b", .digest b)], th, via, k, o, kq, q, pr, db, via', kb, sb, vb, had, hwd,
      hnk, hok, hpeer, hdb, viaReads_of hvia hov, hc.symm, hkb, hsb, hvb, hrows.trans hmap⟩

end fuser

open Nanodregg.Kernel Nanodregg.Kernel.Receive

variable {D : Type} [Ord D] [DecidableEq D]

/-! ## Helpers -/

omit [Ord D] [DecidableEq D] in
/-- A reader whose peer read succeeded on the pair `{a := xb, b := yb}`, with `xb`, `yb` the bytes
of `x'`, `y'` and the reader one of them: its peer is the other. -/
theorem peer_of_pair {bytesOf : D → ByteArray} {digestOf : ByteArray → Option D} {self p x' y' : D}
    {xb yb : ByteArray} {args : Data}
    (hf : args.field "pair" = some (.record [("a", .digest xb), ("b", .digest yb)]))
    (hxd : digestOf xb = some x') (hyd : digestOf yb = some y')
    (hrx : digestOf (bytesOf x') = some x') (hry : digestOf (bytesOf y') = some y') (hne : x' ≠ y')
    (hself : self = x' ∨ self = y')
    (h : Nanodregg.Lang.peerOf bytesOf digestOf self args = .ok p) :
    (self = x' ∧ p = y') ∨ (self = y' ∧ p = x') := by
  obtain ⟨a, b, hf', -, hc⟩ := Nanodregg.Lang.peerOf_party _ _ h
  rw [hf] at hf'
  simp only [Option.some.injEq, Data.record.injEq, List.cons.injEq, Prod.mk.injEq, Data.digest.injEq,
    true_and, and_true] at hf'
  obtain ⟨rfl, rfl⟩ := hf'
  rcases hself with rfl | rfl
  · rcases hc with ⟨-, hb⟩ | ⟨hb, -⟩
    · rw [hyd] at hb; exact .inl ⟨rfl, (Option.some.inj hb).symm⟩
    · exfalso; rw [hb, hrx] at hyd; exact hne (Option.some.inj hyd)
  · rcases hc with ⟨ha, -⟩ | ⟨-, ha⟩
    · exfalso; rw [ha, hry] at hxd; exact hne (Option.some.inj hxd).symm
    · rw [hxd] at ha; exact .inr ⟨rfl, (Option.some.inj ha).symm⟩

/-- **The fuse's tree, unfolded.** The signed call ran `x'`'s `fuse`; its one call invoked `y'`'s
`take` on the bytes `db` of the deal `x'` judged (`fuse_run_sound`); each run's row acts are touches
of the sealed Turn; `y'` is not `x'` (`revisited`). -/
private theorem fuse_tree {bytesOf : D → ByteArray} {digestOf : ByteArray → Option D} {rc : Lang.ReceiptCheck}
    {theta roles : List Label} {ol sl pt budget : Nat} {X : Ctx D} {w : World D} {c : Call D} {t : Turn D}
    {args : ByteArray} {b : Nat} {via : Option D} {pkg : D} {keys th v : Data}
    {xb yb : ByteArray} {x' y' : D}
    (hX : X.program = Lang.program bytesOf digestOf rc) (hc : receive X w c = .ok t)
    (hb : c.unsigned.body = .invoke x' offerFuseIx args b via)
    (hdec : Wire.decodeData (offerFuseArg theta) args =
      .ok (.record [("keys", keys), ("pair", .record [("a", .digest xb), ("b", .digest yb)]), ("theta", th), ("via", v)]))
    (hxd : digestOf xb = some x') (hyd : digestOf yb = some y')
    (hid : digestOf (bytesOf pkg) = some pkg) (hidK : X.digestOf (X.env.bytes pkg) = some pkg)
    (hp : readPackage (pinned X.env w c.unsigned.pins) pkg = .ok (offerPackageOf theta roles ol sl pt budget))
    (hR : (offerRoleTy roles).wf = true)
    (hx : ∃ cl, w.live X.env x' = some cl ∧ cl.slots.get slotPackage = some (X.env.bytes pkg))
    (hy : ∃ cl, w.live X.env y' = some cl ∧ cl.slots.get slotPackage = some (X.env.bytes pkg)) :
    x' ≠ y' ∧ ∃ db via',
    Wire.encodeData (offerTakeArg theta)
      (.record [("keys", keys), ("pair", .record [("a", .digest xb), ("b", .digest yb)]), ("theta", th)]) = some db ∧
    (∃ (st : Slots) (rq : Req D) (f : Nat) (s : Slots) (rows : List (RowSlot D × RowAct)) (used : Nat),
      rq.self = x' ∧
      (Lang.program bytesOf digestOf rc).run (pinned X.env w c.unsigned.pins) (rowView X.env w c.unsigned) pkg st
        offerFuseIx args rq f = .ok (s, [.invoke y' offerTakeIx db budget via'], rows, used) ∧
      ∀ e ∈ rows, ∃ τ ∈ t.rows, τ.slot = e.1 ∧ τ.act = e.2) ∧
    (∃ (st : Slots) (rq : Req D) (f : Nat) (s : Slots) (rows : List (RowSlot D × RowAct)) (used : Nat),
      rq.self = y' ∧
      (Lang.program bytesOf digestOf rc).run (pinned X.env w c.unsigned.pins) (rowView X.env w c.unsigned) pkg st
        offerTakeIx db rq f = .ok (s, [], rows, used) ∧
      ∀ e ∈ rows, ∃ τ ∈ t.rows, τ.slot = e.1 ∧ τ.act = e.2) := by
  obtain ⟨-, hw⟩ := receive_ok_with hc
  obtain ⟨-, d, _k, hd', hs⟩ := receiveWith_sealed hw
  replace hd' := derive_of_withTicks hd'
  rw [derive_eq] at hd'
  cases hRt : dispatch X (pinned X.env w c.unsigned.pins) (rowView X.env w c.unsigned) c
      (tree X (pinned X.env w c.unsigned.pins) (rowView X.env w c.unsigned) c Bounds.callDepthMax)
      ⟨[], poolOf c.unsigned.body, 0⟩ c.unsigned.member c.unsigned.body with
  | error e => rw [hRt] at hd'; cases hd'
  | ok R =>
  rw [hRt] at hd'
  simp only [Except.map, Except.ok.injEq] at hd'
  subst hd'
  have hcov := Nanodregg.Lang.rowTouchesOf_covers (Nanodregg.Lang.sealTurn_rows hs)
  rw [hb] at hRt
  simp only [dispatch] at hRt
  obtain ⟨-, cx, px, rqx, newx, callsx, rowsx, usedx, hirx, hrunx, -, -, -, -, -, hdcx⟩ := invoke_ok hRt
  obtain rfl := invokeRun_pkg hirx hx hidK
  rw [hX] at hrunx
  obtain ⟨keys', pair', th', via', k, o, kq, q, p, db, vg, kb, sb, vb, hdec', hreads, -, -, hpeer, hdb, -, rfl, -, -, -, -⟩ :=
    fuse_run_sound bytesOf digestOf hR hid hp hrunx
  rw [hdec] at hdec'
  simp only [Except.ok.injEq, Data.record.injEq, List.cons.injEq, Prod.mk.injEq, true_and, and_true] at hdec'
  obtain ⟨rfl, rfl, rfl, rfl⟩ := hdec'
  have hselfx := (Nanodregg.Lang.invokeRun_req hirx).1
  unfold deriveCalls at hdcx
  rw [List.foldlM_cons, except_bind_ok] at hdcx
  obtain ⟨a1, h1, h2⟩ := hdcx
  simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h2
  subst h2
  obtain ⟨qy, hqy, rfl⟩ := callStep_ok h1
  obtain ⟨my, -, -, hqy⟩ := effect_as_signed hqy
  simp only [dispatch] at hqy
  obtain ⟨hyv, cy, py, rqy, sy, callsy, rowsy, usedy, hiry, hruny, -, -, -, -, -, hdcy⟩ := invoke_ok hqy
  -- the peer the fuse named is `y'`: `x'` itself would be `revisited`
  have hpy : p = y' := by
    obtain ⟨a, b', hf, -, hcase⟩ := Nanodregg.Lang.peerOf_party _ _ hpeer
    simp only [Data.field, Row.find?, ↓reduceIte] at hf
    obtain ⟨rfl, rfl⟩ := hf
    rw [hselfx] at hcase
    rcases hcase with ⟨-, hb'⟩ | ⟨hb', ha⟩
    · rw [hyd] at hb'; exact (Option.some.inj hb').symm
    · exfalso
      rw [hxd] at ha
      obtain rfl := Option.some.inj ha
      exact hyv (by simp)
  subst hpy
  obtain rfl := invokeRun_pkg hiry hy hidK
  rw [hX] at hruny
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, rfl, -⟩ := take_run_sound bytesOf digestOf hR hid hp hruny
  simp only [deriveCalls, List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at hdcy
  subst hdcy
  refine ⟨fun e => hyv (by simp [e]), db, vg, hdb,
    ⟨_, rqx, _, _, rowsx, usedx, hselfx, hrunx, fun e he => hcov e (by simp [Draft.append, he])⟩,
    ⟨_, rqy, _, sy, rowsy, usedy, (Nanodregg.Lang.invokeRun_req hiry).1, hruny,
      fun e he => hcov e (by simp [Draft.append, he])⟩⟩

omit [Ord D] [DecidableEq D] in
/-- One party's take, read off `take_run_sound` at `self = P`, its row acts located in the Turn. -/
private theorem party {bytesOf : D → ByteArray} {digestOf : ByteArray → Option D} {rc : Lang.ReceiptCheck}
    {theta roles : List Label} {ol sl pt budget : Nat} {look : Pinned D} {rv : RowView D} {pkg : D}
    {t : Turn D} {deal : ByteArray} {P : D} {st : Slots} {rq : Req D} {f : Nat} {s : Slots}
    {rows : List (RowSlot D × RowAct)} {used : Nat}
    (hR : (offerRoleTy roles).wf = true) (hid : digestOf (bytesOf pkg) = some pkg)
    (hp : readPackage look pkg = .ok (offerPackageOf theta roles ol sl pt budget))
    (hself : rq.self = P)
    (hrun : (Lang.program bytesOf digestOf rc).run look rv pkg st offerTakeIx deal rq f = .ok (s, [], rows, used))
    (hcov : ∀ e ∈ rows, ∃ τ ∈ t.rows, τ.slot = e.1 ∧ τ.act = e.2) :
    ∃ keys pair th k o kq q kb sb vb,
      Wire.decodeData (offerTakeArg theta) deal = .ok (.record [("keys", keys), ("pair", pair), ("theta", th)]) ∧
      methodReads bytesOf digestOf rc look pkg (offerRels theta roles ol sl) rv P
        (.record [("keys", keys), ("pair", pair), ("theta", th)]) offerRead offerRead =
        .ok (.record [("offer", .record [("p0", .inj "some" (.record [("key", k), ("val", .inj "some" o)]))]),
          ("peer", .record [("offer", .record [("p0", .inj "some" (.record [("key", kq), ("val", .inj "some" q)]))])])]) ∧
      NamedKey (bytesOf P) keys pair k ∧ JointOk (offerLabels theta) o q th ∧
      keyBytes (offerDecl theta roles ol) k = some kb ∧
      Wire.encodeData (offerSessionDecl theta sl).val
        (.record [("answered", .inj "none" (.record [])),
          ("captured", .inj "settle" (.record [("pair", pair), ("theta", th)]))]) = some vb ∧
      (∃ τ ∈ t.rows, τ.slot = .row ⟨P, 0, kb⟩ ∧ τ.act = .retract) ∧
      (∃ τ ∈ t.rows, τ.slot = .row ⟨P, 1, sb⟩ ∧ τ.act = .insert 0 vb) := by
  obtain ⟨keys, pair, th, k, o, kq, q, kb, sb, vb, hdec, hreads, hnk, hj, -, hkb, -, hvb, rfl⟩ :=
    take_run_sound bytesOf digestOf hR hid hp hrun
  subst hself
  obtain ⟨τ₁, h₁, hs₁, ha₁⟩ := hcov (.row ⟨rq.self, 0, kb⟩, .retract) (by simp)
  obtain ⟨τ₂, h₂, hs₂, ha₂⟩ := hcov (.row ⟨rq.self, 1, sb⟩, .insert 0 vb) (by simp)
  exact ⟨keys, pair, th, k, o, kq, q, kb, sb, vb, hdec, hreads, hnk, hj, hkb, hvb, ⟨τ₁, h₁, hs₁, ha₁⟩,
    ⟨τ₂, h₂, hs₂, ha₂⟩⟩

omit [Ord D] [DecidableEq D] in
/-- The fuser's run, read off `fuse_run_sound` at `self = P`, its row acts located in the Turn. -/
private theorem fuser {bytesOf : D → ByteArray} {digestOf : ByteArray → Option D} {rc : Lang.ReceiptCheck}
    {theta roles : List Label} {ol sl pt budget : Nat} {look : Pinned D} {rv : RowView D} {pkg : D}
    {t : Turn D} {args : ByteArray} {P : D} {st : Slots} {rq : Req D} {f : Nat} {s : Slots}
    {calls : List (Body D)} {rows : List (RowSlot D × RowAct)} {used : Nat}
    (hR : (offerRoleTy roles).wf = true) (hid : digestOf (bytesOf pkg) = some pkg)
    (hp : readPackage look pkg = .ok (offerPackageOf theta roles ol sl pt budget))
    (hself : rq.self = P)
    (hrun : (Lang.program bytesOf digestOf rc).run look rv pkg st offerFuseIx args rq f = .ok (s, calls, rows, used))
    (hcov : ∀ e ∈ rows, ∃ τ ∈ t.rows, τ.slot = e.1 ∧ τ.act = e.2) :
    ∃ keys pair th via k o kq q kb sb vb,
      Wire.decodeData (offerFuseArg theta) args =
        .ok (.record [("keys", keys), ("pair", pair), ("theta", th), ("via", via)]) ∧
      methodReads bytesOf digestOf rc look pkg (offerRels theta roles ol sl) rv P
        (.record [("keys", keys), ("pair", pair), ("theta", th), ("via", via)]) offerRead offerRead =
        .ok (.record [("offer", .record [("p0", .inj "some" (.record [("key", k), ("val", .inj "some" o)]))]),
          ("peer", .record [("offer", .record [("p0", .inj "some" (.record [("key", kq), ("val", .inj "some" q)]))])])]) ∧
      NamedKey (bytesOf P) keys pair k ∧ JointOk (offerLabels theta) o q th ∧
      keyBytes (offerDecl theta roles ol) k = some kb ∧
      Wire.encodeData (offerSessionDecl theta sl).val
        (.record [("answered", .inj "none" (.record [])),
          ("captured", .inj "settle" (.record [("pair", pair), ("theta", th)]))]) = some vb ∧
      (∃ τ ∈ t.rows, τ.slot = .row ⟨P, 0, kb⟩ ∧ τ.act = .retract) ∧
      (∃ τ ∈ t.rows, τ.slot = .row ⟨P, 1, sb⟩ ∧ τ.act = .insert 0 vb) := by
  obtain ⟨keys, pair, th, via, k, o, kq, q, -, -, -, kb, sb, vb, hdec, hreads, hnk, hj, -, -, -, -, hkb, -, hvb, rfl⟩ :=
    fuse_run_sound bytesOf digestOf hR hid hp hrun
  subst hself
  obtain ⟨τ₁, h₁, hs₁, ha₁⟩ := hcov (.row ⟨rq.self, 0, kb⟩, .retract) (by simp)
  obtain ⟨τ₂, h₂, hs₂, ha₂⟩ := hcov (.row ⟨rq.self, 1, sb⟩, .insert 0 vb) (by simp)
  exact ⟨keys, pair, th, via, k, o, kq, q, kb, sb, vb, hdec, hreads, hnk, hj, hkb, hvb, ⟨τ₁, h₁, hs₁, ha₁⟩,
    ⟨τ₂, h₂, hs₂, ha₂⟩⟩

/-! ## The theorems -/

/-- **A signed fuse seals both retracts, of the offers the deal names** (PROT-6, the FUSE call). A
signed call invoking `x'.fuse` of the generated package, its deal naming the pair `{x', y'}` (digests
`xb`, `yb`), both objects of that one package, which `receive` turns into `t`: among `t.rows` are the
retract touch of `x'`'s offer row at the key the deal names for `x'` and the retract touch of `y'`'s
at the key it names for `y'` (slot AND act; `NamedKey`). Whichever rows the caller pinned, the rows
consumed are the named ones (each run's row acts are exactly its retract and its session insert:
`fuse_run_sound`, `take_run_sound`). Mutation PT4, the fuse dropping its call: `receive` is still `.ok`
and `y'`'s retract is absent. This is about the fuse call only: the owner can root-invoke `take`
alone, and one session row is not a fuse. A fuse whose take refuses derives no Turn; that branch is
true of every refusal and is not a conjunct. -/
theorem fuse_atomic {bytesOf : D → ByteArray} {digestOf : ByteArray → Option D} {rc : Lang.ReceiptCheck}
    {theta roles : List Label} {ol sl pt budget : Nat} {X : Ctx D} {w : World D} {c : Call D} {t : Turn D}
    {args : ByteArray} {b : Nat} {via : Option D} {pkg : D} {keys th v : Data}
    {xb yb : ByteArray} {x' y' : D}
    (hX : X.program = Lang.program bytesOf digestOf rc) (hc : receive X w c = .ok t)
    (hb : c.unsigned.body = .invoke x' offerFuseIx args b via)
    (hdec : Wire.decodeData (offerFuseArg theta) args =
      .ok (.record [("keys", keys), ("pair", .record [("a", .digest xb), ("b", .digest yb)]), ("theta", th), ("via", v)]))
    (hxd : digestOf xb = some x') (hyd : digestOf yb = some y')
    (hid : digestOf (bytesOf pkg) = some pkg) (hidK : X.digestOf (X.env.bytes pkg) = some pkg)
    (hp : readPackage (pinned X.env w c.unsigned.pins) pkg = .ok (offerPackageOf theta roles ol sl pt budget))
    (hR : (offerRoleTy roles).wf = true)
    (hx : ∃ cl, w.live X.env x' = some cl ∧ cl.slots.get slotPackage = some (X.env.bytes pkg))
    (hy : ∃ cl, w.live X.env y' = some cl ∧ cl.slots.get slotPackage = some (X.env.bytes pkg)) :
    ∃ kx ky kbx kby,
      NamedKey (bytesOf x') keys (.record [("a", .digest xb), ("b", .digest yb)]) kx ∧
      NamedKey (bytesOf y') keys (.record [("a", .digest xb), ("b", .digest yb)]) ky ∧
      keyBytes (offerDecl theta roles ol) kx = some kbx ∧ keyBytes (offerDecl theta roles ol) ky = some kby ∧
      (∃ τ ∈ t.rows, τ.slot = .row ⟨x', 0, kbx⟩ ∧ τ.act = .retract) ∧
      (∃ τ ∈ t.rows, τ.slot = .row ⟨y', 0, kby⟩ ∧ τ.act = .retract) := by
  obtain ⟨-, db, vg, hdb, ⟨_, _, _, _, _, _, hsx, hrx', hcx⟩, ⟨_, _, _, _, _, _, hsy, hry', hcy⟩⟩ :=
    fuse_tree hX hc hb hdec hxd hyd hid hidK hp hR hx hy
  obtain ⟨keys', pair', th', via', kx, -, -, -, kbx, -, -, hdx, -, hnx, -, hkx, -, hτx, -⟩ := fuser hR hid hp hsx hrx' hcx
  rw [hdec] at hdx
  simp only [Except.ok.injEq, Data.record.injEq, List.cons.injEq, Prod.mk.injEq, true_and, and_true] at hdx
  obtain ⟨rfl, rfl, rfl, rfl⟩ := hdx
  obtain ⟨keys', pair', th', ky, -, -, -, kby, -, -, hdy, -, hny, -, hky, -, hτy, -⟩ := party hR hid hp hsy hry' hcy
  have h1 := Wire.decodeData_eq_ok_iff.mpr hdb
  rw [h1] at hdy
  simp only [Except.ok.injEq, Data.record.injEq, List.cons.injEq, Prod.mk.injEq, true_and, and_true] at hdy
  obtain ⟨rfl, rfl, rfl⟩ := hdy
  exact ⟨kx, ky, kbx, kby, hnx, hny, hkx, hky, hτx, hτy⟩

/-- **Two evaluations of one generated term, coupled by one VALUE** (PROT-6 under LANG-77, the FUSE
call; under `fuse_atomic`'s premises, and `y'`'s digest reading back). `x'` judged `{keys, pair, theta}`
and its run encoded that value for `y'`'s take, which decoded exactly it: ONE θ, by the codec's
canonicity (`decodeData_eq_ok_iff`), not by anyone's forwarding. `x'` read its own offer `ox` and its
peer's `qx`, `y'` its own `oy` and its peer's `qy`; each evaluated `offerJoint` on what it read and
found `JointOk`; the keys and offers cross (`kx = kqy ∧ ox = qy ∧ ky = kqx ∧ oy = qx`), so the two runs
read the same two pinned rows; and the two session inserts in
`t.rows` carry the same value bytes. Mutations: P1 (`offerJoint := okT`: `JointOk` fails on F2's pair)
and PT3 (the fuse sends `keys` where it sends `theta`: the one-θ conjunct fails). -/
theorem jointLaw_sound {bytesOf : D → ByteArray} {digestOf : ByteArray → Option D} {rc : Lang.ReceiptCheck}
    {theta roles : List Label} {ol sl pt budget : Nat} {X : Ctx D} {w : World D} {c : Call D} {t : Turn D}
    {args : ByteArray} {b : Nat} {via : Option D} {pkg : D} {keys th v : Data}
    {xb yb : ByteArray} {x' y' : D}
    (hX : X.program = Lang.program bytesOf digestOf rc) (hc : receive X w c = .ok t)
    (hb : c.unsigned.body = .invoke x' offerFuseIx args b via)
    (hdec : Wire.decodeData (offerFuseArg theta) args =
      .ok (.record [("keys", keys), ("pair", .record [("a", .digest xb), ("b", .digest yb)]), ("theta", th), ("via", v)]))
    (hxd : digestOf xb = some x') (hyd : digestOf yb = some y')
    (hid : digestOf (bytesOf pkg) = some pkg) (hidK : X.digestOf (X.env.bytes pkg) = some pkg)
    (hp : readPackage (pinned X.env w c.unsigned.pins) pkg = .ok (offerPackageOf theta roles ol sl pt budget))
    (hR : (offerRoleTy roles).wf = true)
    (hx : ∃ cl, w.live X.env x' = some cl ∧ cl.slots.get slotPackage = some (X.env.bytes pkg))
    (hy : ∃ cl, w.live X.env y' = some cl ∧ cl.slots.get slotPackage = some (X.env.bytes pkg))
    (hrx : digestOf (bytesOf x') = some x') (hry : digestOf (bytesOf y') = some y') :
    ∃ kx ox kqx qx ky oy kqy qy vb sbx sby,
      methodReads bytesOf digestOf rc (pinned X.env w c.unsigned.pins) pkg (offerRels theta roles ol sl)
        (rowView X.env w c.unsigned) x'
        (.record [("keys", keys), ("pair", .record [("a", .digest xb), ("b", .digest yb)]), ("theta", th), ("via", v)])
        offerRead offerRead =
        .ok (.record [("offer", .record [("p0", .inj "some" (.record [("key", kx), ("val", .inj "some" ox)]))]),
          ("peer", .record [("offer", .record [("p0", .inj "some" (.record [("key", kqx), ("val", .inj "some" qx)]))])])]) ∧
      methodReads bytesOf digestOf rc (pinned X.env w c.unsigned.pins) pkg (offerRels theta roles ol sl)
        (rowView X.env w c.unsigned) y'
        (.record [("keys", keys), ("pair", .record [("a", .digest xb), ("b", .digest yb)]), ("theta", th)])
        offerRead offerRead =
        .ok (.record [("offer", .record [("p0", .inj "some" (.record [("key", ky), ("val", .inj "some" oy)]))]),
          ("peer", .record [("offer", .record [("p0", .inj "some" (.record [("key", kqy), ("val", .inj "some" qy)]))])])]) ∧
      JointOk (offerLabels theta) ox qx th ∧ JointOk (offerLabels theta) oy qy th ∧
      kx = kqy ∧ ox = qy ∧ ky = kqx ∧ oy = qx ∧
      Wire.encodeData (offerSessionDecl theta sl).val
        (.record [("answered", .inj "none" (.record [])),
          ("captured", .inj "settle" (.record [("pair", .record [("a", .digest xb), ("b", .digest yb)]), ("theta", th)]))]) =
        some vb ∧
      (∃ τ ∈ t.rows, τ.slot = .row ⟨x', 1, sbx⟩ ∧ τ.act = .insert 0 vb) ∧
      (∃ τ ∈ t.rows, τ.slot = .row ⟨y', 1, sby⟩ ∧ τ.act = .insert 0 vb) := by
  obtain ⟨hne, db, vg, hdb, ⟨_, _, _, _, _, _, hsx, hrx', hcx⟩, ⟨_, _, _, _, _, _, hsy, hry', hcy⟩⟩ :=
    fuse_tree hX hc hb hdec hxd hyd hid hidK hp hR hx hy
  obtain ⟨keys', pair', th', via', kx, ox, kqx, qx, -, sbx, vb, hdx, hmx, -, hjx, -, hvx, -, hix⟩ :=
    fuser hR hid hp hsx hrx' hcx
  rw [hdec] at hdx
  simp only [Except.ok.injEq, Data.record.injEq, List.cons.injEq, Prod.mk.injEq, true_and, and_true] at hdx
  obtain ⟨rfl, rfl, rfl, rfl⟩ := hdx
  obtain ⟨keys', pair', th', ky, oy, kqy, qy, -, sby, vb', hdy, hmy, -, hjy, -, hvy, -, hiy⟩ :=
    party hR hid hp hsy hry' hcy
  have h1 := Wire.decodeData_eq_ok_iff.mpr hdb
  rw [h1] at hdy
  simp only [Except.ok.injEq, Data.record.injEq, List.cons.injEq, Prod.mk.injEq, true_and, and_true] at hdy
  obtain ⟨rfl, rfl, rfl⟩ := hdy
  rw [hvx] at hvy
  cases hvy
  obtain ⟨px, Ax, Bx, hpx, hox, hqx, hRx⟩ := methodReads_offer hmx
  obtain ⟨py, Ay, By, hpy, hoy, hqy, hRy⟩ := methodReads_offer hmy
  -- each one's peer is the other
  have hfx : (Data.record [("keys", keys), ("pair", .record [("a", .digest xb), ("b", .digest yb)]), ("theta", th),
      ("via", v)]).field "pair" = some (.record [("a", .digest xb), ("b", .digest yb)]) := by simp [Data.field, Row.find?]
  have hfy : (Data.record [("keys", keys), ("pair", .record [("a", .digest xb), ("b", .digest yb)]), ("theta", th)]).field
      "pair" = some (.record [("a", .digest xb), ("b", .digest yb)]) := by simp [Data.field, Row.find?]
  rcases peer_of_pair hfx hxd hyd hrx hry hne (.inl rfl) hpx with ⟨-, rfl⟩ | ⟨hxy, -⟩
  · rcases peer_of_pair hfy hxd hyd hrx hry hne (.inr rfl) hpy with ⟨hyx, -⟩ | ⟨-, rfl⟩
    · exact absurd hyx.symm hne
    · -- the own read of each is the peer read of the other: `readsData` under one parent, at args
      -- that differ only past the fields the point read uses
      simp only [Data.record.injEq, List.cons.injEq, Prod.mk.injEq, true_and, and_true] at hRx hRy
      obtain ⟨rfl, rfl⟩ := hRx
      obtain ⟨rfl, rfl⟩ := hRy
      rw [readsData_offer_args _ (Data.record [("keys", keys), ("pair", .record [("a", .digest xb), ("b", .digest yb)]),
        ("theta", th)]), hoy] at hqx
      rw [readsData_offer_args _ (Data.record [("keys", keys), ("pair", .record [("a", .digest xb), ("b", .digest yb)]),
        ("theta", th), ("via", v)]), hox] at hqy
      simp only [Except.ok.injEq, Data.record.injEq, List.cons.injEq, Prod.mk.injEq, Data.inj.injEq, true_and,
        and_true] at hqx hqy
      obtain ⟨rfl, rfl⟩ := hqx
      obtain ⟨rfl, rfl⟩ := hqy
      exact ⟨kx, ox, ky, oy, ky, oy, kx, ox, vb, sbx, sby, hmx, hmy, hjx, hjy, rfl, rfl, rfl, rfl, hvx, hix, hiy⟩
  · exact absurd hxy hne

/-- **Once per standing row** (PROT-6, the FUSE call). Under `fuse_atomic`'s premises, the Turn
admitted to `w'` from canonical rows: the offer rows the two runs read, at their key bytes, are
absent in `w'`. The grant is not spent (`.invoke` is not a counted right), and a `post` at the same
key afterwards is a new offer: this is not a spent-never-minted claim. A later fuse on `w'` pinning
either slot refuses `noOffer` (journey row LF5). A retract turned into an upsert (P5) is refused
`final` by `offer_guard`, so no such world admits. -/
theorem invitation_once {bytesOf : D → ByteArray} {digestOf : ByteArray → Option D} {rc : Lang.ReceiptCheck}
    {theta roles : List Label} {ol sl pt budget : Nat} {X : Ctx D} {w : World D} {c : Call D} {t : Turn D}
    {args : ByteArray} {b : Nat} {via : Option D} {pkg : D} {keys th v : Data}
    {xb yb : ByteArray} {x' y' : D}
    (hX : X.program = Lang.program bytesOf digestOf rc) (hc : receive X w c = .ok t)
    (hb : c.unsigned.body = .invoke x' offerFuseIx args b via)
    (hdec : Wire.decodeData (offerFuseArg theta) args =
      .ok (.record [("keys", keys), ("pair", .record [("a", .digest xb), ("b", .digest yb)]), ("theta", th), ("via", v)]))
    (hxd : digestOf xb = some x') (hyd : digestOf yb = some y')
    (hid : digestOf (bytesOf pkg) = some pkg) (hidK : X.digestOf (X.env.bytes pkg) = some pkg)
    (hp : readPackage (pinned X.env w c.unsigned.pins) pkg = .ok (offerPackageOf theta roles ol sl pt budget))
    (hR : (offerRoleTy roles).wf = true)
    (hx : ∃ cl, w.live X.env x' = some cl ∧ cl.slots.get slotPackage = some (X.env.bytes pkg))
    (hy : ∃ cl, w.live X.env y' = some cl ∧ cl.slots.get slotPackage = some (X.env.bytes pkg))
    {w' : World D} (ha : World.admit X.env w t = .ok w') (hcan : w.RowsCanon X.env) :
    ∃ kx ky kbx kby,
      NamedKey (bytesOf x') keys (.record [("a", .digest xb), ("b", .digest yb)]) kx ∧
      NamedKey (bytesOf y') keys (.record [("a", .digest xb), ("b", .digest yb)]) ky ∧
      keyBytes (offerDecl theta roles ol) kx = some kbx ∧ keyBytes (offerDecl theta roles ol) ky = some kby ∧
      rowAt X.env w'.rows (.row ⟨x', 0, kbx⟩) = none ∧ rowAt X.env w'.rows (.row ⟨y', 0, kby⟩) = none := by
  obtain ⟨kx, ky, kbx, kby, hnx, hny, hkx, hky, ⟨τx, hτx, hsτx, haτx⟩, ⟨τy, hτy, hsτy, haτy⟩⟩ :=
    fuse_atomic hX hc hb hdec hxd hyd hid hidK hp hR hx hy
  exact ⟨kx, ky, kbx, kby, hnx, hny, hkx, hky,
    admit_retract_row hcan ha hτx hsτx haτx,
    admit_retract_row hcan ha hτy hsτy haτy⟩

end Nanodregg.Lang.Std
