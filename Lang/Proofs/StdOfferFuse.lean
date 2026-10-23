/-
# Lang.Proofs.StdOfferFuse — what a signed fuse of the generated matcher seals (PROT-6)

* `fuse_calls` (`Lang.program`'s run of the matcher): a returned fuse makes exactly the two `take`
  invokes, carrying the SAME `deal` bytes, and edits nothing. The one θ is the matcher's property,
  not the takes'.

A signed call invoking the matcher `z.fuse` of the generated package `offerPackageOf …`, which
`receive` turns into a Turn `t`, its arguments naming parties `x'` and `y'` of the same package:

* `fuse_atomic`: `t.rows` holds the retract of `x'`'s offer row AND the retract of `y'`'s, each at
  the key the deal NAMES for that party (`NamedKey`): the matcher cannot choose which of a party's
  standing offers the fuse consumes.
* `jointLaw_sound`: both takes decoded ONE θ from the one forwarded `deal`, each read its own offer
  and its peer's, each found `JointOk` of what it read (two evaluations of one generated term), the
  pair names exactly the two parties, the two runs read the same two pinned rows, and the two session
  inserts carry the same value bytes.
* `invitation_once`: once the Turn is admitted, both offer rows the takes read are absent.

`fuse_calls` sits here, not in `Lang.Proofs.StdOffer`, so that a plant in the matcher's body reds
this module and leaves the take's module built. All three are about the FUSE call. The owner can root-invoke its own `take` with no matcher, and one
session row is not a fuse. A fuse in which either take refuses derives no Turn: that branch is
"no `receive` result", true of every refusal, and is no conjunct here.
-/
import Lang.Proofs.DispatchRows
import Lang.Proofs.StdOffer

namespace Nanodregg.Lang.Std

section matcher
open Nanodregg.Lang

/-! ## The deployed run of `fuse`: two invokes of `take`, one `deal` -/

private theorem slot_c2 : slotLabels "c" 2 = ["c0", "c1"] := by decide

/-- A call's `via` field read as the kernel reads it: no grant, or a grant that is a digest of the World. -/
def ViaReads {D : Type} (digestOf : ByteArray → Option D) (v : Data) (g : Option D) : Prop :=
  (v = .inj "none" (.record []) ∧ g = none) ∨ ∃ b d, v = .inj "some" (.digest b) ∧ digestOf b = some d ∧ g = some d

private theorem viaReads_of {D : Type} {digestOf : ByteArray → Option D} {v : Data} {g : Option D}
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

private theorem fuse_resolve {D : Type} {theta roles : List Label} {ol sl b : Nat} {x : Label × Sig}
    (h : resolveMethod (D := D) (offerPackageOf theta roles ol sl b) offerFuseIx = .ok x) :
    x = ("fuse", ⟨offerFuseArg, [offerCallTy, offerCallTy], [], 0⟩) := by
  have hc : callSlotsOf [("c0", optTy offerCallTy), ("c1", optTy offerCallTy)] = some [offerCallTy, offerCallTy] := by
    decide
  have hr : rowsOf (offerRels theta roles ol sl) (.record []) = some ([], []) := by
    simp [rowsOf, readsOf, readsTy, Row.find?]
  simp [resolveMethod, offerPackageOf, offerFuseIx, offerMethods, recordRow, Row.find?, methodSig, methodTy,
    resultTy, callsTy, slot_c2, hc, hr, pairNamed] at h
  split at h
  · rename_i sg hsg
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    split at hsg
    · cases hsg; rfl
    · cases hsg
  · simp [throw, throwThe, MonadExceptOf.throw] at h

private theorem fuse_peerReads (theta roles : List Label) (ol sl b : Nat) :
    (offerPackageOf theta roles ol sl b).peerReads "fuse" = [] := by
  have hr : rowsOf (offerRels theta roles ol sl) (.record []) = some ([], []) := by
    simp [rowsOf, readsOf, readsTy, Row.find?]
  simp [Package.peerReads, offerPackageOf, recordRow, Row.find?, methodPeer, methodTy, hr]

private theorem noRef_fuse (budget : Nat) :
    NoRef (activityMethod offerStateTy offerFuseArg (.record []) (offerFuseBody budget)) := by
  simp [activityMethod, offerFuseBody, NoRef, NoRefRow, resultT, callsT, someCallT, offerTakeCall, slot_c2]

private def fuseArgD (deal : ByteArray) (vx vy : Data) (x y : ByteArray) : Data :=
  .record [("deal", .bytes deal), ("viaX", vx), ("viaY", vy), ("x", .digest x), ("y", .digest y)]

private theorem fuseArg_cases {ad : Data} (h : Conforms ad offerFuseArg) :
    ∃ deal vx vy x y, ad = fuseArgD deal vx vy x y ∧ Conforms vx (optTy .digest) ∧ Conforms vy (optTy .digest) := by
  cases h with
  | record hr =>
    cases hr with
    | cons h1 hr => cases hr with
      | cons h2 hr => cases hr with
        | cons h3 hr => cases hr with
          | cons h4 hr => cases hr with
            | cons h5 hr =>
              cases hr; cases h1; cases h4; cases h5
              exact ⟨_, _, _, _, _, rfl, h2, h3⟩

/-- The fuse's calls row, as `offerFuseBody` writes it. -/
private abbrev callsFuseT (budget : Nat) : Term :=
  callsT [someCallT offerCallTy (offerTakeCall budget (.get (.var 1) "x") (.get (.var 1) "viaX") (.get (.var 1) "deal")),
    someCallT offerCallTy (offerTakeCall budget (.get (.var 1) "y") (.get (.var 1) "viaY") (.get (.var 1) "deal"))]

private def invokeTy : Ty :=
  .record [("args", .bytes), ("budget", .nat), ("method", .nat), ("obj", .digest), ("via", optTy .digest)]

private theorem callsFuse_means {lib : List Term} {req state : Val} {rows : Data} {E : Env}
    {deal : ByteArray} {vx vy : Data} {x y : ByteArray} {budget : Nat}
    (hvx : Conforms vx (optTy .digest)) (hvy : Conforms vy (optTy .digest)) {W : Val}
    (hW : BigStep lib (req :: (fuseArgD deal vx vy x y).toVal :: state :: rows.toVal :: E) (callsFuseT budget) (.ok W)) :
    Means lib (callsTy [offerCallTy, offerCallTy]) W
      (.record [("c0", .inj "some" (.inj "invoke" (.record [("args", .bytes deal), ("budget", .nat budget),
          ("method", .nat offerTakeIx), ("obj", .digest x), ("via", vx)]))),
        ("c1", .inj "some" (.inj "invoke" (.record [("args", .bytes deal), ("budget", .nat budget),
          ("method", .nat offerTakeIx), ("obj", .digest y), ("via", vy)])))]) := by
  cases hW
  simp only [callsTy, List.map, List.zip, suspend, offerTakeCall]
  have hf : Row.find? "invoke" (callArms.filter fun a => ["invoke"].contains a.1) = some invokeTy := by decide
  refine .record .record (.cons (.inj (.inj .record)) ?_ (.cons (.inj (.inj .record)) ?_ .nil))
  · exact .inj rfl (.inj hf (.record .record
      (.cons (get_data (ℓ := "deal") (x := .bytes deal) (BigStep.var (i := 1) rfl) rfl) .bytes
      (.cons .nat .nat (.cons .nat .nat
      (.cons (get_data (ℓ := "x") (x := .digest x) (BigStep.var (i := 1) rfl) rfl) .digest
      (.cons (get_data (ℓ := "viaX") (x := vx) (BigStep.var (i := 1) rfl) rfl) (means_toVal hvx) .nil)))))))
  · exact .inj rfl (.inj hf (.record .record
      (.cons (get_data (ℓ := "deal") (x := .bytes deal) (BigStep.var (i := 1) rfl) rfl) .bytes
      (.cons .nat .nat (.cons .nat .nat
      (.cons (get_data (ℓ := "y") (x := .digest y) (BigStep.var (i := 1) rfl) rfl) .digest
      (.cons (get_data (ℓ := "viaY") (x := vy) (BigStep.var (i := 1) rfl) rfl) (means_toVal hvy) .nil)))))))

/-- **The matcher forwards one deal to both takes** (`Lang.program`'s `run` of `fuse`, for any closed
package whose `fuse` method is the generated matcher and resolves to its signature: `Std.offer` and
its escrow instance): a run that returned decoded `{deal, viaX, viaY, x, y}`, makes exactly two calls, `invoke x take deal budget`
and `invoke y take deal budget`, carrying the SAME `deal` bytes (each `via` read as the kernel reads
it), and edits no row. The matcher judges nothing: the honesty is each take's
(`take_iff_compliant`); the one θ is this theorem's. Mutations: P3 (the second call dropped: the
calls list has one element) and P4 (a second argument field `dealY` sent to `y`: the second call's
bytes are not `deal`). -/
theorem fuse_calls {D : Type} (bytesOf : D → ByteArray) (digestOf : ByteArray → Option D) {rc : Lang.ReceiptCheck}
    {P : Package} {fs : List (Label × Term)} {budget : Nat}
    {look : Kernel.Receive.Pinned D} {rv : Kernel.Receive.RowView D} {pkg : D} {state : Kernel.Slots}
    {args : ByteArray} {r : Kernel.Receive.Req D} {budget' : Nat} {s : Kernel.Slots}
    {calls : List (Kernel.Receive.Body D)} {rows : List (Kernel.RowSlot D × Kernel.RowAct)} {used : Nat}
    (hid : digestOf (bytesOf pkg) = some pkg) (hp : readPackage look pkg = .ok P)
    (hi : P.imports = []) (hh : P.holes = [])
    (hres : ∀ {x : Label × Sig}, resolveMethod (D := D) P offerFuseIx = .ok x →
      x = ("fuse", ⟨offerFuseArg, [offerCallTy, offerCallTy], [], 0⟩))
    (hbody : P.body = .record fs)
    (hf : Row.find? "fuse" fs = some (activityMethod offerStateTy offerFuseArg (.record []) (offerFuseBody budget)))
    (h : (Lang.program bytesOf digestOf rc).run look rv pkg state offerFuseIx args r budget' =
      .ok (s, calls, rows, used)) :
    ∃ deal x y vx vy x' y' vx' vy',
      Wire.decodeData offerFuseArg args =
        .ok (.record [("deal", .bytes deal), ("viaX", vx), ("viaY", vy), ("x", .digest x), ("y", .digest y)]) ∧
      digestOf x = some x' ∧ digestOf y = some y' ∧ ViaReads digestOf vx vx' ∧ ViaReads digestOf vy vy' ∧
      calls = [.invoke x' offerTakeIx deal budget vx', .invoke y' offerTakeIx deal budget vy'] ∧ rows = [] := by
  change (runMeasuredLive bytesOf digestOf rc look rv pkg state offerFuseIx args r budget').map _ = _ at h
  rw [runMeasuredLive_leaf_closed hid hp hi hh] at h
  cases hm : runMeasured bytesOf digestOf rc look rv pkg state offerFuseIx args r budget' with
  | error e => rw [hm] at h; cases h
  | ok x =>
  rw [hm] at h
  obtain ⟨s', calls', rows', t', n'⟩ := x
  simp only [Except.map, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl, rfl⟩ := h
  obtain ⟨S, v, used, c, e, ds, left, es, hS, hrun, hx, hc, hes, hrows⟩ := runMeasured_inv hm
  obtain ⟨L, g, p, ℓ, sg, sd, ad, wd, -, hl, hpg, hres', -, had, -, hwd, rfl⟩ := runSetup_spec hS
  obtain ⟨hpg', f, hlib⟩ := load_top bytesOf digestOf (fuel := closureDepthMax - 1) hid hp hl
  rw [hpg'] at hpg
  cases hpg
  have hsig := hres hres'
  cases hsig
  simp only at hrun hx hes
  obtain ⟨deal, vx, vy, xb, yb, rfl, hvx, hvy⟩ := fuseArg_cases (decodeData_conforms had)
  have hbig := run_bigStep hrun
  have hval : BigStep L.lib [(reqData bytesOf r).toVal, (fuseArgD deal vx vy xb yb).toVal, sd.toVal, wd.toVal]
      (offerFuseBody budget) _ := .record
  cases bigStep_deterministic hbig
    (apply4_field hlib hbody hf (noRef_fuse budget) hval)
  have hM := extract_means _ _ hx
  have hwC := BigStep.get (ℓ := "calls") hbig (.field (find_suspend_of (t := callsFuseT budget) rfl) .record)
  obtain ⟨A, hA, hmA⟩ := means_get hbig hM rfl hwC
  simp [Row.find?] at hA
  subst hA
  have hce := means_deterministic hmA (callsFuse_means (budget := budget) hvx hvy .record)
  subst hce
  have hwE := BigStep.get (ℓ := "edits") hbig (.field (find_suspend_of (t := .record []) rfl) .record)
  obtain ⟨A', hA', hmE⟩ := means_get hbig hM rfl hwE
  simp [Row.find?] at hA'
  subst hA'
  have hee := means_deterministic hmE (.record .record .nil)
  subst hee
  simp [editsOf, editsOf.go] at hes
  subst hes
  cases hdx : digestOf xb <;> cases hdy : digestOf yb <;>
    cases hox : optOf (digestAt digestOf "via") "via" vx <;> cases hoy : optOf (digestAt digestOf "via") "via" vy <;>
    simp [callsOf, callsOf.go, bodyOf, digestAt, natOf, bytesAt, hdx, hdy, hox, hoy, bind, Except.bind, pure,
      Except.pure, Except.map] at hc
  rename_i x' y' vx' vy'
  exact ⟨deal, xb, yb, vx, vy, x', y', vx', vy', had, hdx, hdy, viaReads_of hvx hox, viaReads_of hvy hoy,
    hc.symm, hrows⟩

end matcher

open Nanodregg.Kernel Nanodregg.Kernel.Receive

variable {D : Type} [Ord D] [DecidableEq D]

/-! ## Helpers -/

/-- An invoke of an object whose live cell names package `pkg` runs `pkg`. -/
private theorem invokeRun_pkg {X : Ctx D} {w : World D} {pins : List (D × D)} {c : Call D} {actor obj : D}
    {method : Nat} {via : Option D} {cell : Cell} {p : D} {rq : Req D} {pkg : D}
    (h : invokeRun X (pinned X.env w pins) c actor obj method via = .ok (cell, p, rq))
    (ho : ∃ cl, w.live X.env obj = some cl ∧ cl.slots.get slotPackage = some (X.env.bytes pkg))
    (hk : X.digestOf (X.env.bytes pkg) = some pkg) : p = pkg := by
  obtain ⟨hrk, hpk, -⟩ := Nanodregg.Lang.invokeRun_ok h
  have hl := (readKind_pinned hrk).1
  obtain ⟨cl, hcl, hsl⟩ := ho
  rw [hl] at hcl
  cases hcl
  unfold packageOf at hpk
  rw [hsl] at hpk
  simp only [hk, Except.ok.injEq, Option.some.injEq] at hpk
  exact hpk.symm

omit [Ord D] [DecidableEq D] in
/-- What `peerOf` read: a pair of two different digests, one of them the reader's bytes, and the
peer the other one's digest. -/
private theorem peerOf_spec {bytesOf : D → ByteArray} {digestOf : ByteArray → Option D} {self p : D}
    {args : Data} (h : Nanodregg.Lang.peerOf bytesOf digestOf self args = .ok p) :
    ∃ a b, args.field "pair" = some (.record [("a", .digest a), ("b", .digest b)]) ∧ a ≠ b ∧
      ((a = bytesOf self ∧ digestOf b = some p) ∨ (b = bytesOf self ∧ digestOf a = some p)) := by
  unfold Nanodregg.Lang.peerOf at h
  split at h
  · rename_i a b hf
    refine ⟨a, b, hf, ?_⟩
    by_cases hab : a = b
    · subst hab
      simp [bind, Except.bind] at h
    · refine ⟨hab, ?_⟩
      by_cases ha : a = bytesOf self
      · subst ha
        simp [hab, bind, Except.bind, pure, Except.pure] at h
        split at h
        · rename_i q hq
          simp only [Except.ok.injEq] at h
          subst h
          exact .inl ⟨rfl, hq⟩
        · simp [throw, throwThe, MonadExceptOf.throw] at h
      · by_cases hb : b = bytesOf self
        · subst hb
          simp [ha, bind, Except.bind, pure, Except.pure] at h
          split at h
          · rename_i q hq
            simp only [Except.ok.injEq] at h
            subst h
            exact .inr ⟨rfl, hq⟩
          · simp [throw, throwThe, MonadExceptOf.throw] at h
        · simp [hab, ha, hb, bind, Except.bind, pure, Except.pure] at h
  · simp [throw, throwThe, MonadExceptOf.throw] at h

omit [Ord D] [DecidableEq D] in
/-- A read of one offer point is a record with one field, `offer`. -/
private theorem readsData_offer {digestOf : ByteArray → Option D} {rc : Lang.ReceiptCheck} {look : Pinned D}
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

omit [Ord D] [DecidableEq D] in
/-- **The take's reads**: its own offer point under `self` and the same read under its peer, the
`peerOf` of the arguments. -/
private theorem methodReads_offer {bytesOf : D → ByteArray} {digestOf : ByteArray → Option D} {rc : Lang.ReceiptCheck}
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

omit [Ord D] [DecidableEq D] in
/-- Two different parties that each found the other in one pair: each one's peer is the other. -/
private theorem peer_pair {bytesOf : D → ByteArray} {digestOf : ByteArray → Option D} {x y px py : D}
    {args : Data} (hne : x ≠ y) (hrx : digestOf (bytesOf x) = some x) (hry : digestOf (bytesOf y) = some y)
    (hx : Nanodregg.Lang.peerOf bytesOf digestOf x args = .ok px)
    (hy : Nanodregg.Lang.peerOf bytesOf digestOf y args = .ok py) : px = y ∧ py = x := by
  obtain ⟨a, b, hf, -, hxc⟩ := peerOf_spec hx
  obtain ⟨a', b', hf', -, hyc⟩ := peerOf_spec hy
  rw [hf] at hf'
  simp only [Option.some.injEq, Data.record.injEq, List.cons.injEq, Prod.mk.injEq, Data.digest.injEq,
    true_and, and_true] at hf'
  obtain ⟨rfl, rfl⟩ := hf'
  have hbne : bytesOf x ≠ bytesOf y := fun e => hne (by
    have h := hrx
    rw [e, hry] at h
    exact (Option.some.inj h).symm)
  rcases hxc with ⟨rfl, hb⟩ | ⟨rfl, ha⟩ <;> rcases hyc with ⟨hay, hb'⟩ | ⟨hby, ha'⟩
  · exact absurd hay hbne
  · rw [hby, hry] at hb
    rw [hrx] at ha'
    exact ⟨(Option.some.inj hb).symm, (Option.some.inj ha').symm⟩
  · rw [hay, hry] at ha
    rw [hrx] at hb'
    exact ⟨(Option.some.inj ha).symm, (Option.some.inj hb').symm⟩
  · exact absurd hby hbne

omit [Ord D] [DecidableEq D] in
private theorem callStep_ok_ {sub : Receive.Sub D} {obj : D} {acc q : Draft D × Walk D} {b : Body D}
    (h : callStep sub obj acc b = .ok q) : ∃ q', sub acc.2 obj b = .ok q' ∧ q = (acc.1.append q'.1, q'.2) := by
  unfold callStep at h
  simp only [except_bind_ok, pure, Except.pure, Except.ok.injEq] at h
  obtain ⟨q', h1, rfl⟩ := h
  exact ⟨q', h1, rfl⟩

/-- **The fuse's tree, unfolded.** The signed fuse ran `fuse_calls`' two invokes; each was derived as
the matcher, ran the take of its party's package on the one `deal` with the party as `self`, made no
calls, and its row acts are touches of the sealed Turn; the second party is not the first
(`revisited`). -/
private theorem fuse_tree {bytesOf : D → ByteArray} {digestOf : ByteArray → Option D} {rc : Lang.ReceiptCheck}
    {theta roles : List Label} {ol sl budget : Nat} {X : Ctx D} {w : World D} {c : Call D} {t : Turn D}
    {z : D} {args : ByteArray} {b : Nat} {via : Option D} {pkg : D} {deal : ByteArray} {vX vY : Data}
    {xb yb : ByteArray} {x' y' : D}
    (hX : X.program = Lang.program bytesOf digestOf rc) (hc : receive X w c = .ok t)
    (hb : c.unsigned.body = .invoke z offerFuseIx args b via)
    (hdec : Wire.decodeData offerFuseArg args =
      .ok (.record [("deal", .bytes deal), ("viaX", vX), ("viaY", vY), ("x", .digest xb), ("y", .digest yb)]))
    (hxd : digestOf xb = some x') (hyd : digestOf yb = some y')
    (hid : digestOf (bytesOf pkg) = some pkg) (hidK : X.digestOf (X.env.bytes pkg) = some pkg)
    (hp : readPackage (pinned X.env w c.unsigned.pins) pkg = .ok (offerPackageOf theta roles ol sl budget))
    (hR : (offerRoleTy roles).wf = true)
    (hz : ∃ cl, w.live X.env z = some cl ∧ cl.slots.get slotPackage = some (X.env.bytes pkg))
    (hx : ∃ cl, w.live X.env x' = some cl ∧ cl.slots.get slotPackage = some (X.env.bytes pkg))
    (hy : ∃ cl, w.live X.env y' = some cl ∧ cl.slots.get slotPackage = some (X.env.bytes pkg)) :
    x' ≠ y' ∧
    (∃ (st : Slots) (rq : Req D) (f : Nat) (s : Slots) (rows : List (RowSlot D × RowAct)) (used : Nat),
      rq.self = x' ∧
      (Lang.program bytesOf digestOf rc).run (pinned X.env w c.unsigned.pins) (rowView X.env w c.unsigned) pkg st
        offerTakeIx deal rq f = .ok (s, [], rows, used) ∧
      ∀ e ∈ rows, ∃ τ ∈ t.rows, τ.slot = e.1 ∧ τ.act = e.2) ∧
    (∃ (st : Slots) (rq : Req D) (f : Nat) (s : Slots) (rows : List (RowSlot D × RowAct)) (used : Nat),
      rq.self = y' ∧
      (Lang.program bytesOf digestOf rc).run (pinned X.env w c.unsigned.pins) (rowView X.env w c.unsigned) pkg st
        offerTakeIx deal rq f = .ok (s, [], rows, used) ∧
      ∀ e ∈ rows, ∃ τ ∈ t.rows, τ.slot = e.1 ∧ τ.act = e.2) := by
  obtain ⟨-, hw⟩ := receive_ok_with hc
  obtain ⟨-, d, hd', hs⟩ := receiveWith_sealed hw
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
  obtain ⟨-, cz, pz, rqz, newz, callsz, rowsz, usedz, hirz, hrunz, -, -, -, -, -, hdcz⟩ := invoke_ok hRt
  obtain rfl := invokeRun_pkg hirz hz hidK
  rw [hX] at hrunz
  obtain ⟨deal', xb', yb', vx, vy, x'', y'', vx', vy', hdec', hdx, hdy, -, -, rfl, rfl⟩ :=
    fuse_calls bytesOf digestOf (budget := budget) hid hp rfl rfl fuse_resolve rfl (by simp [Row.find?]) hrunz
  rw [hdec] at hdec'
  simp only [Except.ok.injEq, Data.record.injEq, List.cons.injEq, Prod.mk.injEq, Data.bytes.injEq,
    Data.digest.injEq, true_and, and_true] at hdec'
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hdec'
  rw [hxd] at hdx
  rw [hyd] at hdy
  cases hdx
  cases hdy
  unfold deriveCalls at hdcz
  rw [List.foldlM_cons, except_bind_ok] at hdcz
  obtain ⟨a1, h1, h2⟩ := hdcz
  rw [List.foldlM_cons, except_bind_ok] at h2
  obtain ⟨a2, h3, h4⟩ := h2
  simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h4
  subst h4
  obtain ⟨qx, hqx, rfl⟩ := callStep_ok_ h1
  obtain ⟨qy, hqy, rfl⟩ := callStep_ok_ h3
  obtain ⟨mx, -, -, hqx⟩ := effect_as_signed hqx
  obtain ⟨my, -, -, hqy⟩ := effect_as_signed hqy
  simp only [dispatch] at hqx hqy
  obtain ⟨-, cx, px, rqx, sx, callsx, rowsx, usedx, hirx, hrunx, -, -, -, -, -, hdcx⟩ := invoke_ok hqx
  obtain ⟨hyv, cy, py, rqy, sy, callsy, rowsy, usedy, hiry, hruny, -, -, -, -, -, hdcy⟩ := invoke_ok hqy
  obtain rfl := invokeRun_pkg hirx hx hidK
  obtain rfl := invokeRun_pkg hiry hy hidK
  rw [hX] at hrunx hruny
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, rfl, -⟩ := take_run_sound bytesOf digestOf hR hid hp hrunx
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, rfl, -⟩ := take_run_sound bytesOf digestOf hR hid hp hruny
  simp only [deriveCalls, List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at hdcx hdcy
  subst hdcx hdcy
  refine ⟨fun e => hyv (by simp [e]), ⟨_, rqx, _, sx, rowsx, usedx, (Nanodregg.Lang.invokeRun_req hirx).1, hrunx,
      fun e he => hcov e (by simp [Draft.append, he])⟩,
    ⟨_, rqy, _, sy, rowsy, usedy, (Nanodregg.Lang.invokeRun_req hiry).1, hruny,
      fun e he => hcov e (by simp [Draft.append, he])⟩⟩

omit [Ord D] [DecidableEq D] in
/-- One party's take, read off `take_run_sound` at `self = P`, its row acts located in the Turn. -/
private theorem party {bytesOf : D → ByteArray} {digestOf : ByteArray → Option D} {rc : Lang.ReceiptCheck}
    {theta roles : List Label} {ol sl budget : Nat} {look : Pinned D} {rv : RowView D} {pkg : D}
    {t : Turn D} {deal : ByteArray} {P : D} {st : Slots} {rq : Req D} {f : Nat} {s : Slots}
    {rows : List (RowSlot D × RowAct)} {used : Nat}
    (hR : (offerRoleTy roles).wf = true) (hid : digestOf (bytesOf pkg) = some pkg)
    (hp : readPackage look pkg = .ok (offerPackageOf theta roles ol sl budget))
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

/-! ## The theorems -/

/-- **A signed fuse seals both retracts, of the offers the deal names** (PROT-6, the FUSE call). A
signed call invoking the matcher `z.fuse` of the generated package, its arguments naming `x` and
`y` (digests `x'`, `y'`), the three objects of that one package, which `receive` turns into `t`: the
forwarded deal decodes to `{keys, pair, theta}`, and among `t.rows` are the retract touch of `x'`'s
offer row at the key the deal names for `x'` and the retract touch of `y'`'s at the key it names for
`y'` (slot AND act; `NamedKey`). Whichever rows the caller pinned, the rows consumed are the named
ones (each take's row acts are exactly its retract and its session insert: `take_run_sound`).
Mutations: P3, the fuse dropping its second call: `receive` is still `.ok` and `y'`'s retract is
absent; PA, the take's name check skipped: at LF8 `y'` consumes its offer 0 where the deal names 1. This is about
the fuse call only: the owner can root-invoke `take` alone, and one session row is not a fuse. A fuse
whose take refuses derives no Turn; that branch is true of every refusal and is not a conjunct. -/
theorem fuse_atomic {bytesOf : D → ByteArray} {digestOf : ByteArray → Option D} {rc : Lang.ReceiptCheck}
    {theta roles : List Label} {ol sl budget : Nat} {X : Ctx D} {w : World D} {c : Call D} {t : Turn D}
    {z : D} {args : ByteArray} {b : Nat} {via : Option D} {pkg : D} {deal : ByteArray} {vX vY : Data}
    {xb yb : ByteArray} {x' y' : D}
    (hX : X.program = Lang.program bytesOf digestOf rc) (hc : receive X w c = .ok t)
    (hb : c.unsigned.body = .invoke z offerFuseIx args b via)
    (hdec : Wire.decodeData offerFuseArg args =
      .ok (.record [("deal", .bytes deal), ("viaX", vX), ("viaY", vY), ("x", .digest xb), ("y", .digest yb)]))
    (hxd : digestOf xb = some x') (hyd : digestOf yb = some y')
    (hid : digestOf (bytesOf pkg) = some pkg) (hidK : X.digestOf (X.env.bytes pkg) = some pkg)
    (hp : readPackage (pinned X.env w c.unsigned.pins) pkg = .ok (offerPackageOf theta roles ol sl budget))
    (hR : (offerRoleTy roles).wf = true)
    (hz : ∃ cl, w.live X.env z = some cl ∧ cl.slots.get slotPackage = some (X.env.bytes pkg))
    (hx : ∃ cl, w.live X.env x' = some cl ∧ cl.slots.get slotPackage = some (X.env.bytes pkg))
    (hy : ∃ cl, w.live X.env y' = some cl ∧ cl.slots.get slotPackage = some (X.env.bytes pkg)) :
    ∃ keys pair th kx ky kbx kby,
      Wire.decodeData (offerTakeArg theta) deal = .ok (.record [("keys", keys), ("pair", pair), ("theta", th)]) ∧
      NamedKey (bytesOf x') keys pair kx ∧ NamedKey (bytesOf y') keys pair ky ∧
      keyBytes (offerDecl theta roles ol) kx = some kbx ∧ keyBytes (offerDecl theta roles ol) ky = some kby ∧
      (∃ τ ∈ t.rows, τ.slot = .row ⟨x', 0, kbx⟩ ∧ τ.act = .retract) ∧
      (∃ τ ∈ t.rows, τ.slot = .row ⟨y', 0, kby⟩ ∧ τ.act = .retract) := by
  obtain ⟨-, ⟨_, _, _, _, _, _, hsx, hrx, hcx⟩, ⟨_, _, _, _, _, _, hsy, hry, hcy⟩⟩ :=
    fuse_tree hX hc hb hdec hxd hyd hid hidK hp hR hz hx hy
  obtain ⟨keys, pair, th, kx, -, -, -, kbx, -, -, hdx, -, hnx, -, hkx, -, hτx, -⟩ := party hR hid hp hsx hrx hcx
  obtain ⟨keys', pair', th', ky, -, -, -, kby, -, -, hdy, -, hny, -, hky, -, hτy, -⟩ := party hR hid hp hsy hry hcy
  rw [hdx] at hdy
  simp only [Except.ok.injEq, Data.record.injEq, List.cons.injEq, Prod.mk.injEq, true_and, and_true] at hdy
  obtain ⟨rfl, rfl, rfl⟩ := hdy
  exact ⟨keys, pair, th, kx, ky, kbx, kby, hdx, hnx, hny, hkx, hky, hτx, hτy⟩

/-- **Two evaluations of one generated term, coupled by one forwarded byte string** (PROT-6, the
FUSE call; under `fuse_atomic`'s premises, and the parties' digests reading back). Both takes decoded
ONE θ (and one pair) from the one `deal`; `x'`'s take read its own offer `ox` and its peer's `qx`,
`y'`'s its own `oy` and its peer's `qy`; each evaluated `offerJoint` on what it read and found
`JointOk`; the pair names exactly the two parties (each one's `peerOf` is the other), so the two runs
read the same two pinned rows (`ox = qy`, `qx = oy`, keys too); and the two session inserts in
`t.rows` carry the same value bytes. The one θ is the MATCHER's guarantee (`fuse_calls`, `z` of the
generated package): a caller of another package granted `take` could hand the two takes different
bytes, and each take's own judgement (`take_iff_compliant`) does not depend on who called it.
Mutations: P1 (`offerJoint := okT`: `JointOk` fails on F2's pair) and P4 (the fuse sends `y` a second
deal: the one-θ, same-reads and equal-value conjuncts fail). -/
theorem jointLaw_sound {bytesOf : D → ByteArray} {digestOf : ByteArray → Option D} {rc : Lang.ReceiptCheck}
    {theta roles : List Label} {ol sl budget : Nat} {X : Ctx D} {w : World D} {c : Call D} {t : Turn D}
    {z : D} {args : ByteArray} {b : Nat} {via : Option D} {pkg : D} {deal : ByteArray} {vX vY : Data}
    {xb yb : ByteArray} {x' y' : D}
    (hX : X.program = Lang.program bytesOf digestOf rc) (hc : receive X w c = .ok t)
    (hb : c.unsigned.body = .invoke z offerFuseIx args b via)
    (hdec : Wire.decodeData offerFuseArg args =
      .ok (.record [("deal", .bytes deal), ("viaX", vX), ("viaY", vY), ("x", .digest xb), ("y", .digest yb)]))
    (hxd : digestOf xb = some x') (hyd : digestOf yb = some y')
    (hid : digestOf (bytesOf pkg) = some pkg) (hidK : X.digestOf (X.env.bytes pkg) = some pkg)
    (hp : readPackage (pinned X.env w c.unsigned.pins) pkg = .ok (offerPackageOf theta roles ol sl budget))
    (hR : (offerRoleTy roles).wf = true)
    (hz : ∃ cl, w.live X.env z = some cl ∧ cl.slots.get slotPackage = some (X.env.bytes pkg))
    (hx : ∃ cl, w.live X.env x' = some cl ∧ cl.slots.get slotPackage = some (X.env.bytes pkg))
    (hy : ∃ cl, w.live X.env y' = some cl ∧ cl.slots.get slotPackage = some (X.env.bytes pkg))
    (hrx : digestOf (bytesOf x') = some x') (hry : digestOf (bytesOf y') = some y') :
    ∃ keys pair th kx ox kqx qx ky oy kqy qy vb sbx sby,
      Wire.decodeData (offerTakeArg theta) deal = .ok (.record [("keys", keys), ("pair", pair), ("theta", th)]) ∧
      methodReads bytesOf digestOf rc (pinned X.env w c.unsigned.pins) pkg (offerRels theta roles ol sl)
        (rowView X.env w c.unsigned) x' (.record [("keys", keys), ("pair", pair), ("theta", th)]) offerRead offerRead =
        .ok (.record [("offer", .record [("p0", .inj "some" (.record [("key", kx), ("val", .inj "some" ox)]))]),
          ("peer", .record [("offer", .record [("p0", .inj "some" (.record [("key", kqx), ("val", .inj "some" qx)]))])])]) ∧
      methodReads bytesOf digestOf rc (pinned X.env w c.unsigned.pins) pkg (offerRels theta roles ol sl)
        (rowView X.env w c.unsigned) y' (.record [("keys", keys), ("pair", pair), ("theta", th)]) offerRead offerRead =
        .ok (.record [("offer", .record [("p0", .inj "some" (.record [("key", ky), ("val", .inj "some" oy)]))]),
          ("peer", .record [("offer", .record [("p0", .inj "some" (.record [("key", kqy), ("val", .inj "some" qy)]))])])]) ∧
      JointOk (offerLabels theta) ox qx th ∧ JointOk (offerLabels theta) oy qy th ∧
      peerOf bytesOf digestOf x' (.record [("keys", keys), ("pair", pair), ("theta", th)]) = .ok y' ∧
      peerOf bytesOf digestOf y' (.record [("keys", keys), ("pair", pair), ("theta", th)]) = .ok x' ∧
      kx = kqy ∧ ox = qy ∧ ky = kqx ∧ oy = qx ∧
      Wire.encodeData (offerSessionDecl theta sl).val
        (.record [("answered", .inj "none" (.record [])),
          ("captured", .inj "settle" (.record [("pair", pair), ("theta", th)]))]) = some vb ∧
      (∃ τ ∈ t.rows, τ.slot = .row ⟨x', 1, sbx⟩ ∧ τ.act = .insert 0 vb) ∧
      (∃ τ ∈ t.rows, τ.slot = .row ⟨y', 1, sby⟩ ∧ τ.act = .insert 0 vb) := by
  obtain ⟨hne, ⟨_, _, _, _, _, _, hsx, hrunx, hcx⟩, ⟨_, _, _, _, _, _, hsy, hruny, hcy⟩⟩ :=
    fuse_tree hX hc hb hdec hxd hyd hid hidK hp hR hz hx hy
  obtain ⟨keys, pair, th, kx, ox, kqx, qx, -, sbx, vb, hdx, hmx, -, hjx, -, hvx, -, hix⟩ :=
    party hR hid hp hsx hrunx hcx
  obtain ⟨keys', pair', th', ky, oy, kqy, qy, -, sby, vb', hdy, hmy, -, hjy, -, hvy, -, hiy⟩ :=
    party hR hid hp hsy hruny hcy
  rw [hdx] at hdy
  simp only [Except.ok.injEq, Data.record.injEq, List.cons.injEq, Prod.mk.injEq, true_and, and_true] at hdy
  obtain ⟨rfl, rfl, rfl⟩ := hdy
  rw [hvx] at hvy
  cases hvy
  obtain ⟨px, Ax, Bx, hpx, hox, hqx, hRx⟩ := methodReads_offer hmx
  obtain ⟨py, Ay, By, hpy, hoy, hqy, hRy⟩ := methodReads_offer hmy
  obtain ⟨rfl, rfl⟩ := peer_pair hne hrx hry hpx hpy
  simp only [Data.record.injEq, List.cons.injEq, Prod.mk.injEq, true_and, and_true] at hRx hRy
  obtain ⟨rfl, rfl⟩ := hRx
  obtain ⟨rfl, rfl⟩ := hRy
  rw [hoy] at hqx
  rw [hox] at hqy
  simp only [Except.ok.injEq, Data.record.injEq, List.cons.injEq, Prod.mk.injEq, Data.inj.injEq, true_and,
    and_true] at hqx hqy
  obtain ⟨rfl, rfl⟩ := hqx
  obtain ⟨rfl, rfl⟩ := hqy
  exact ⟨keys, pair, th, kx, ox, ky, oy, ky, oy, kx, ox, vb, sbx, sby, hdx, hmx, hmy, hjx, hjy, hpx, hpy,
    rfl, rfl, rfl, rfl, hvx, hix, hiy⟩

/-- **Once per standing row** (PROT-6, the FUSE call). Under `fuse_atomic`'s premises, the Turn
admitted to `w'` from canonical rows: the offer rows the two takes read, at their key bytes, are
absent in `w'`. The grant is not spent (`.invoke` is not a counted right), and a `post` at the same
key afterwards is a new offer: this is not a spent-never-minted claim. A later take on `w'` pinning
either slot refuses `noOffer`: that is `take_noOffer` at the term grain, with journey row LF5; this
theorem's tooth is journey rows LF1/LF5. A retract turned into an upsert (P5) is refused `final` by
`offer_guard`, so no such world admits. -/
theorem invitation_once {bytesOf : D → ByteArray} {digestOf : ByteArray → Option D} {rc : Lang.ReceiptCheck}
    {theta roles : List Label} {ol sl budget : Nat} {X : Ctx D} {w : World D} {c : Call D} {t : Turn D}
    {z : D} {args : ByteArray} {b : Nat} {via : Option D} {pkg : D} {deal : ByteArray} {vX vY : Data}
    {xb yb : ByteArray} {x' y' : D}
    (hX : X.program = Lang.program bytesOf digestOf rc) (hc : receive X w c = .ok t)
    (hb : c.unsigned.body = .invoke z offerFuseIx args b via)
    (hdec : Wire.decodeData offerFuseArg args =
      .ok (.record [("deal", .bytes deal), ("viaX", vX), ("viaY", vY), ("x", .digest xb), ("y", .digest yb)]))
    (hxd : digestOf xb = some x') (hyd : digestOf yb = some y')
    (hid : digestOf (bytesOf pkg) = some pkg) (hidK : X.digestOf (X.env.bytes pkg) = some pkg)
    (hp : readPackage (pinned X.env w c.unsigned.pins) pkg = .ok (offerPackageOf theta roles ol sl budget))
    (hR : (offerRoleTy roles).wf = true)
    (hz : ∃ cl, w.live X.env z = some cl ∧ cl.slots.get slotPackage = some (X.env.bytes pkg))
    (hx : ∃ cl, w.live X.env x' = some cl ∧ cl.slots.get slotPackage = some (X.env.bytes pkg))
    (hy : ∃ cl, w.live X.env y' = some cl ∧ cl.slots.get slotPackage = some (X.env.bytes pkg))
    {w' : World D} (ha : World.admit X.env w t = .ok w') (hcan : w.RowsCanon X.env) :
    ∃ keys pair th kx ox kqx qx kbx ky oy kqy qy kby,
      Wire.decodeData (offerTakeArg theta) deal = .ok (.record [("keys", keys), ("pair", pair), ("theta", th)]) ∧
      methodReads bytesOf digestOf rc (pinned X.env w c.unsigned.pins) pkg (offerRels theta roles ol sl)
        (rowView X.env w c.unsigned) x' (.record [("keys", keys), ("pair", pair), ("theta", th)]) offerRead offerRead =
        .ok (.record [("offer", .record [("p0", .inj "some" (.record [("key", kx), ("val", .inj "some" ox)]))]),
          ("peer", .record [("offer", .record [("p0", .inj "some" (.record [("key", kqx), ("val", .inj "some" qx)]))])])]) ∧
      methodReads bytesOf digestOf rc (pinned X.env w c.unsigned.pins) pkg (offerRels theta roles ol sl)
        (rowView X.env w c.unsigned) y' (.record [("keys", keys), ("pair", pair), ("theta", th)]) offerRead offerRead =
        .ok (.record [("offer", .record [("p0", .inj "some" (.record [("key", ky), ("val", .inj "some" oy)]))]),
          ("peer", .record [("offer", .record [("p0", .inj "some" (.record [("key", kqy), ("val", .inj "some" qy)]))])])]) ∧
      keyBytes (offerDecl theta roles ol) kx = some kbx ∧ keyBytes (offerDecl theta roles ol) ky = some kby ∧
      rowAt X.env w'.rows (.row ⟨x', 0, kbx⟩) = none ∧ rowAt X.env w'.rows (.row ⟨y', 0, kby⟩) = none := by
  obtain ⟨-, ⟨_, _, _, _, _, _, hsx, hrunx, hcx⟩, ⟨_, _, _, _, _, _, hsy, hruny, hcy⟩⟩ :=
    fuse_tree hX hc hb hdec hxd hyd hid hidK hp hR hz hx hy
  obtain ⟨keys, pair, th, kx, ox, kqx, qx, kbx, -, -, hdx, hmx, -, -, hkx, -, ⟨τx, hτx, hsτx, haτx⟩, -⟩ :=
    party hR hid hp hsx hrunx hcx
  obtain ⟨keys', pair', th', ky, oy, kqy, qy, kby, -, -, hdy, hmy, -, -, hky, -, ⟨τy, hτy, hsτy, haτy⟩, -⟩ :=
    party hR hid hp hsy hruny hcy
  rw [hdx] at hdy
  simp only [Except.ok.injEq, Data.record.injEq, List.cons.injEq, Prod.mk.injEq, true_and, and_true] at hdy
  obtain ⟨rfl, rfl, rfl⟩ := hdy
  exact ⟨keys, pair, th, kx, ox, kqx, qx, kbx, ky, oy, kqy, qy, kby, hdx, hmx, hmy, hkx, hky,
    Nanodregg.Lang.admit_retract_absent hcan ha hτx hsτx haτx,
    Nanodregg.Lang.admit_retract_absent hcan ha hτy hsτy haτy⟩

end Nanodregg.Lang.Std
