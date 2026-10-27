/-
# Spec.Proofs.Bell — THE BELL (TOPLEVEL-SPEC §6): the two slices provable now

The composite (every ring answered at most once, with its own text, by at most one charged ask,
across ticks, socket replies, crashes and restarts) needs `RingLife` (§11.5) and is OWED; it is not
stated here. Two slices are, each a claim with a top theorem and a floor.

**(1) THE RINGER'S PROMISE** (`Bell.ringer`, the Lang half, at the grain of one method run): for the
package the resident accepts as the bell (the field `bellAccept`; deployed `Lang.Bell.shapeOk`, the
check `Resident.bellCore` makes of the configured bell's package, HOSTING-45), every upsert of `rings` (relation 1) that a returning run of
ANY of its methods makes writes an answered row `answered (l y)`, captured `l c`, over a row the
caller pinned at that key that was WAITING with the same capture `l c`, and the run was signed by the
resident of the state it read. So no run rewrites an answered row, an answer keeps the ring's own text
and aim, and only the resident answers. Top: `top_bell_ringer` (`Lang.Bell.shape_parts`,
`Lang.Bell.rung_is_waiting`, `Lang.runMeasuredWith_ok`, `Lang.editOf_spec`, `Lang.Std.waiting_body_step`,
`Lang.Bell.resumes_resident`: `bell_monitored`'s proof with the edits kept). Floor:
`floor_bell_ringer`, `laxBell` (`bellAccept := bellLayoutOk`: the resident that accepts a package by
its layout but not its guards), refused by `unguardedBell` (the Bell without `(guards queued rung)`): its `answer`
run over an ANSWERED row returns an upsert of it (the second of two answers for one key admits).
Inhabited: `inhabited_bell_ringer` (an accepted Bell's `answer` over a waiting row upserts it).

**(2) ONE CHARGED ASK, RIGHT AFTER THE INTENT** (`Bell.oneAsk`, the resident half, over the resident's
act on the rings a tick read, the field `ringAct`, deployed `Hosting.Resident.actOn`; `tickWith act`
is the deployed tick around it, `tickWith_actOn`): every
path of the act asks at most once, about the ring the decision chose, immediately after the intent
`(unanswered restart)` was kept for it; and along any chain of ticks of one process, between two
spent asks about one ring an effect freed it. Top: `top_bell_oneAsk` (`act_counts`, `actOn_core`,
`bell_resident_conforms`). Floor: `floor_bell_oneAsk`, `askFirstResident` (`ringAct := askFirst`, the act
with the ask before the keep; `askFirst_breaks_order` is `order_refuses_ask_before_keep` on its path).

**Premises.** (1): the package id is a digest of the World and `readPackage look pkg = .ok p` (the
run reads the package it was handed, `load_top`); nothing else: any view, state, request, method.
(2): none beyond the path (`Runs`, any result of every effect) and the chain (`TicksWith`).

**What each slice covers of the composite, and the owed seams.**
* (1) covers "answered by the resident, with the ring's own text" and "an answered row is not
  rewritten" for ONE run, against the row the CALLER pinned. Owed: the World grain, along `Audited`:
  a rows twin of `Kernel.Receive.object_turn_cases` (every non-`keep` row touch of a sealed Turn at
  `⟨o, rel, k⟩` is a row act of a run of a dispatched invoke of `o`) plus the pinned row being the
  World's (`rows_stale_refused`), then `admit_Frame`/`admit_row_touch` per step. With it, (1) lifts to
  "along an audited log the `rings` row at a key moves only by `WaitingStep`".
* "At most one answer PER KEY" (cv task 01a17ab4-17b1) is FALSE of the deployed Bell and is not claimed: `retire` retracts an
  answered row (by anyone), the kernel's `insert` needs only an absent row, `WaitingStep.start` takes
  any old row, and the key is `(ringer, notBefore)` with `notBefore` backdatable by the window: ring,
  answer, retire, ring again at the same `notBefore`, answer again with another text. At most one
  answer per ring LIFE (between its insert and its retract) is what (1) gives at the World grain;
  `RingLife` must key a ring by its life, or the Bell must tombstone a retired key.
* (2) covers "at most one charged ask per tick" and, within one process, "per ring". Owed: across a
  crash (`Life` = `Ticks` with crash edges through `resumeOps`): a crash between the intent's keep
  and the ask, the restart reading the kept intent and answering `(unanswered restart)` with no
  second ask (`keep_atomic`, `resume_durable`, `seed_after_keep` exist; their composition does not).
  A lost reply (an `ok` invoke whose reply never came back) and the member's World holding the row
  are `answered_row_is_kept_answer`/`answered_row_committed` (premise forms), not composed here.
  A14 (undecodable stdout read as "nothing pending") is closed in the tree since HOSTING-49
  (`undecodable_frees_nothing`, `read_undecodable_stops`); TOPLEVEL-SPEC §6 still lists it open.
-/
import Spec.System
import Lang.Proofs.Bell
import Lang.Proofs.Data
import Hosting.Proofs.BellConform
import Spec.Sim.Bell

namespace Nanodregg.Spec

/-! ## (1) The ringer's promise -/

section ringer
open Nanodregg.Kernel Nanodregg.Kernel.Receive

variable {D : Type} [Ord D] [DecidableEq D]

/-- **THE RINGER'S PROMISE** (§6 (1), at the grain of one method run). For a package `p` the
resident accepts as the bell (`S.bellAccept`; deployed: `Lang.Bell.shapeOk`, the check `Resident.bellCore`
makes of the configured bell's package), every returning run of any method of `p` by the system's
program, on any view `rv`, state and request, that upserts `rings` (relation 1) at the key bytes
`kb` of the run's own object to bytes `vb`: `vb` is an answered row `answered (l y)` captured `l c`;
the row the caller pinned at `kb` was WAITING with the same capture `l c` (so the ring is answered
once, and with its own text and aim); and the request was signed by the resident of the state the
run read. -/
def Bell.ringer (S : System D) : Prop :=
  ∀ {look : Pinned D} {rv : RowView D} {pkg : D} {p : Lang.Package} {state : Slots} {method : Nat}
    {args : ByteArray} {r : Req D} {budget : Nat} {s : Slots} {calls : List (Body D)}
    {rows : List (RowSlot D × RowAct)} {used amt : Nat} {kb vb : ByteArray},
    S.X.digestOf (S.X.env.bytes pkg) = some pkg → Lang.readPackage look pkg = .ok p → S.bellAccept p = true →
    S.X.program.run look rv pkg state method args r budget = .ok (s, calls, rows, used) →
    (RowSlot.row ⟨r.self, 1, kb⟩, RowAct.upsert amt vb) ∈ rows →
    ∃ (l : Lang.Label) (y c sd : Lang.Data) (amt' ver : Nat) (ob : ByteArray),
      Lang.Wire.decodeData Lang.Bell.rings.val vb = .ok (answeredRow l y c) ∧
      (rv.points r.self 1).find? (fun q => decide (q.1 = kb)) = some (kb, some (.row amt' ob ver)) ∧
      Lang.Wire.decodeData Lang.Bell.rings.val ob = .ok (waitingRow l c) ∧
      Lang.readState S.X.digestOf (Lang.recordRow p.state) state = .ok sd ∧
      sd.field "resident" = some (.digest (S.X.env.bytes r.agent))

/-- In the Bell's relations, index 1 is `rings`. -/
theorem relIndex_bell_one {ℓ : Lang.Label} (h : Lang.relIndex Lang.Bell.rels ℓ = some 1) : ℓ = "rings" := by
  simp [Lang.relIndex, Lang.Bell.rels, List.findIdx?, List.findIdx?.go] at h
  split at h
  · simp at h
  · split at h
    · rename_i h'; exact h'.symm
    · simp at h

omit [Ord D] [DecidableEq D] in
/-- The row a guard found, when it is a present row: the pinned leaf at the edit's key and its
value bytes read at the relation's value type. -/
theorem guardOld_some {digestOf : ByteArray → Option D} {rv : RowView D} {self : D} {x : Lang.Edit D}
    {row : Lang.Data} (h : Lang.guardOld digestOf rv self x = .ok (.inj "some" row)) :
    ∃ k amt ob ver, Lang.pinAt rv self x = some (k, some (.row amt ob ver)) ∧
      Lang.Wire.decodeData x.decl.val ob = .ok row := by
  unfold Lang.guardOld at h
  rcases hp : Lang.pinAt rv self x with _ | ⟨k, _ | l⟩
  · simp only [hp] at h
    split at h <;> simp [Lang.optD] at h
  · simp [hp, Lang.optD] at h
  · cases l with
    | head => simp [hp] at h
    | row a v n =>
      simp only [hp] at h
      unfold Lang.valOf Lang.checked at h
      cases hd : Lang.Wire.decodeData x.decl.val v with
      | error e => simp [hd, Except.map] at h
      | ok d =>
        by_cases hc : (d.digests.all fun b => (digestOf b).isSome) = true
        · simp [hd, hc, Except.map, Lang.optD] at h
          subst h
          exact ⟨k, a, v, n, rfl, hd⟩
        · simp [hd, hc, Except.map] at h

omit [Ord D] [DecidableEq D] in
/-- **The ringer's promise of one run** (any `bytesOf`/`digestOf`, any receipt check): at a package
the Bell's shape reads (`Lang.Bell.shapeOk`), a returning run's upsert of `rings` at `kb` answers a
waiting row with its own capture, signed by the resident. `Lang.Bell.bell_monitored`'s proof with
the run's edits kept (`editsOf … = .ok es`), then `Lang.editOf_spec` on the edit at `(1, kb)`. -/
theorem ringer_run {bytesOf : D → ByteArray} {digestOf : ByteArray → Option D} {rc : Lang.ReceiptCheck}
    {look : Pinned D} {rv : RowView D} {pkg : D} {p : Lang.Package} {state : Slots} {method : Nat}
    {args : ByteArray} {r : Req D} {budget : Nat} {s : Slots} {calls : List (Body D)}
    {rows : List (RowSlot D × RowAct)} {used amt : Nat} {kb vb : ByteArray}
    (hid : digestOf (bytesOf pkg) = some pkg) (hp : Lang.readPackage look pkg = .ok p)
    (hs : Lang.Bell.shapeOk p = true)
    (h : (Lang.program bytesOf digestOf rc).run look rv pkg state method args r budget = .ok (s, calls, rows, used))
    (hm : (RowSlot.row ⟨r.self, 1, kb⟩, RowAct.upsert amt vb) ∈ rows) :
    ∃ (l : Lang.Label) (y c sd : Lang.Data) (amt' ver : Nat) (ob : ByteArray),
      Lang.Wire.decodeData Lang.Bell.rings.val vb = .ok (answeredRow l y c) ∧
      (rv.points r.self 1).find? (fun q => decide (q.1 = kb)) = some (kb, some (.row amt' ob ver)) ∧
      Lang.Wire.decodeData Lang.Bell.rings.val ob = .ok (waitingRow l c) ∧
      Lang.readState digestOf (Lang.recordRow p.state) state = .ok sd ∧
      sd.field "resident" = some (.digest (bytesOf r.agent)) := by
  obtain ⟨hi, hh, -, hR, -, -⟩ := Lang.Bell.shape_parts hs
  obtain ⟨fs, hb, hrel, hgd, hf, hv, hnr, hw⟩ := Lang.Bell.rung_is_waiting hs
  change (Lang.runMeasuredLive bytesOf digestOf rc look rv pkg state method args r budget).map _ = _ at h
  rw [Lang.runMeasuredLive_leaf_closed hid hp hi hh] at h
  cases hm' : Lang.runMeasured bytesOf digestOf rc look rv pkg state method args r budget with
  | error e => rw [hm'] at h; cases h
  | ok q =>
  rw [hm'] at h
  obtain ⟨s', calls', rows', t', n'⟩ := q
  simp only [Except.map, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl, rfl⟩ := h
  obtain ⟨S, v, used', c, e, ds, left, es, hS, hrun, hx, hes, hge, rfl⟩ := Lang.runMeasuredWith_ok hm'
  obtain ⟨L, g, p', ℓm, sg, sd, ad, wd, hr0, hl, hpg, hres, hst, hargs, -, hrows, rfl⟩ := Lang.runSetup_spec hS
  obtain ⟨hpg', f, hlib⟩ := Lang.load_top bytesOf digestOf (fuel := Lang.closureDepthMax - 1) hid hp hl
  rw [hpg'] at hpg
  cases hpg
  obtain ⟨mty, hmt, hA⟩ := Lang.resolveMethod_spec hres
  have hok := Lang.invoke_never_stuck (ticks := budget - 0) hl hpg' hmt hA hst hargs hrows hr0
  simp only at hrun hx hes hge
  rw [hrun] at hok
  -- the edit at `(1, kb)`
  obtain ⟨x, hxe, hxa⟩ := List.mem_map.mp hm
  obtain ⟨fs0, s0, o0, he0, hmem0, hx'⟩ := Lang.editsOf_mem hes x hxe
  obtain ⟨-, hri, hfd, key, k, -, hslot, hact⟩ := Lang.editOf_spec hx'
  simp only [Prod.mk.injEq] at hxa
  obtain ⟨hxs, hxact⟩ := hxa
  rw [hslot] at hxs
  have hkey := RowSlot.row.inj hxs
  have hrel1 : x.rel = 1 := congrArg RowKey.rel hkey
  have hkk : k = kb := congrArg RowKey.k hkey
  subst k
  rw [hR, hrel1] at hri
  have hlab : x.label = "rings" := relIndex_bell_one hri
  rw [hlab, hR] at hfd
  have hdecl : x.decl = Lang.Bell.rings := by
    simp only [Lang.Bell.rels, Lang.Row.find?, String.reduceEq, if_false, if_true, Option.some.injEq] at hfd
    exact hfd.symm
  rcases hact with ⟨v0, b0, -, -, hia⟩ | ⟨v0, b0, hdata, henc, hua⟩ | ⟨-, -, hra⟩
  · rw [hia] at hxact; cases hxact
  · rw [hua] at hxact
    simp only [RowAct.upsert.injEq] at hxact
    obtain ⟨-, rfl⟩ := hxact
    -- the monitor, at this edit
    have hcf := Lang.extract_conforms (Lang.load_libTy hl).1
      (Lang.resultTy p.state sg.calls (Lang.editTy p.rels) sg.edits) hok hx
    cases hcf with
    | record hrow =>
      cases hrow with
      | cons _ hrest =>
        cases hrest with
        | cons hed _ =>
          obtain ⟨-, hc⟩ := Lang.editsOf_conforms hed hes x hxe
          obtain ⟨o, ho, hgl⟩ := Lang.guardEdits_ok hge x hxe
          rw [hdecl] at hc
          have hold := Lang.guardOld_conforms ho
          rw [hdecl] at hold
          obtain ⟨cenv, w, hbody⟩ := Lang.Std.runLaw_ref_admits (g := g) (fs := Lang.Term.relocateRow f fs)
            (by rw [hlib, hb]; rfl)
            (by rw [Lang.find_relocateRow, hf, Option.map_some, Lang.relocate_noRef _ _
                  (Lang.Std.noRef_activityWaiting _ _ _ _ _ hnr)]; rfl)
            (hgl "rung" (by rw [hdecl]; exact hgd))
          have hW := Lang.Std.waiting_body_step hw hv hc hold hbody
          generalize hdx : x.data = dx at hW
          cases hW with
          | start => rw [hdata] at hdx; simp at hdx
          | retire => rw [hdata] at hdx; simp at hdx
          | timedOut => rw [hdata] at hdx; simp at hdx
          | @answer key' c0 y0 l0 hres' =>
            rw [hdata] at hdx
            simp only [Lang.Data.inj.injEq, Lang.Data.record.injEq, List.cons.injEq, Prod.mk.injEq,
              true_and, and_true] at hdx
            obtain ⟨-, rfl⟩ := hdx
            obtain ⟨a, hag, hra⟩ := Lang.Bell.resumes_resident hres'
            have ha : a = bytesOf r.agent := by
              simp only [Lang.reqData, Lang.Data.field, Lang.Row.find?, if_true, Option.some.injEq,
                Lang.Data.digest.injEq] at hag
              exact hag.symm
            subst ha
            obtain ⟨k', amt', ob, ver, hpin, hdec⟩ := guardOld_some ho
            rw [hdecl] at hdec
            have hk' : k' = kb := by
              have := List.find?_some hpin
              simpa [hslot, RowSlot.keyBytes] using this
            subst hk'
            refine ⟨l0, y0, c0, sd, amt', ver, ob, ?_, ?_, hdec, hst, hra⟩
            · rw [hdecl] at henc
              exact Lang.Wire.decodeData_eq_ok_iff.mpr henc
            · unfold Lang.pinAt at hpin
              rw [hrel1] at hpin
              simpa [hslot, RowSlot.keyBytes] using hpin
  · rw [hra] at hxact; cases hxact

/-- **TOP (§6 (1)).** The deployed system keeps the ringer's promise at the package the resident
accepts (`Lang.Bell.shapeOk`, the resident's `bellCore` check, HOSTING-45). -/
theorem top_bell_ringer (d : ByteArray → ByteArray) : Bell.ringer (deployed d) := by
  intro look rv pkg p state method args r budget s calls rows used amt kb vb hid hp hacc hrun hm
  exact ringer_run (rc := Protocol.Foreign.check Codec.Deployed.env Codec.Deployed.digestCodec)
    hid hp hacc hrun hm

end ringer

/-! ### The floor and the inhabitant of (1): runs at the deployed `Ctx` (inputs: `Spec.Sim.Bell`) -/

section ringerRun
open Nanodregg.Kernel Nanodregg.Kernel.Receive Nanodregg.Codec


/-- **The unguarded Bell's second answer admits** (a closed run of the deployed program; the
package decode is well-founded recursion, which the kernel does not reduce). -/
theorem run_unguarded_second_answer :
    (bellLayoutOk unguardedBell && bellReads unguardedBell && bellUpserts unguardedBell bellAnsweredB &&
      bellAnsweredReads) = true := by
  native_decide

/-- **The accepted Bell answers a waiting ring.** -/
theorem run_bell_answers :
    (Lang.Bell.shapeOk minBell && bellReads minBell && bellUpserts minBell bellWaitingB) = true := by
  native_decide

/-- **The tooth is the guard**: the same second answer at the accepted Bell (`minBell`, guards on) is
refused (`rung: answered`), so the floor's run differs from the deployed acceptance exactly by
`(guards queued rung)`. -/
theorem run_bell_refuses_second_answer : bellUpserts minBell bellAnsweredB = false := by
  native_decide

/-- From `bellUpserts`: a returned run and its upsert. -/
theorem bellUpserts_ok {p : Lang.Package} {old : ByteArray} (h : bellUpserts p old = true) :
    ∃ s calls rows used amt vb,
      Host.Deployed.X.program.run (bellLook p) (bellRv old) bellPkg bellState 0 bellArgs bellReq 1000000 =
        .ok (s, calls, rows, used) ∧
      (RowSlot.row ⟨bellReq.self, 1, bellKey⟩, RowAct.upsert amt vb) ∈ rows := by
  unfold bellUpserts at h
  revert h
  generalize Host.Deployed.X.program.run (bellLook p) (bellRv old) bellPkg bellState 0 bellArgs bellReq 1000000 = R
  intro h
  cases R with
  | error e => cases h
  | ok q =>
    obtain ⟨s, calls, rows, used⟩ := q
    obtain ⟨⟨sl, a⟩, hq, hx⟩ := List.any_eq_true.mp h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hx
    obtain ⟨rfl, ha⟩ := hx
    cases a with
    | upsert amt vb => exact ⟨s, calls, rows, used, amt, vb, rfl, hq⟩
    | _ => simp at ha

/-- From `bellReads`. -/
theorem bellReads_ok {p : Lang.Package} (h : bellReads p = true) :
    Digest.ofBytes? bellPkg.bytes = some bellPkg ∧ Lang.readPackage (bellLook p) bellPkg = .ok p := by
  unfold bellReads at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨h1, ?_⟩
  revert h2
  generalize Lang.readPackage (bellLook p) bellPkg = R
  intro h2
  cases R with
  | error e => cases h2
  | ok q => simp only [decide_eq_true_eq] at h2; rw [h2]

/-- **FLOOR (§6 (1)).** The claim refuses the resident that accepts the bell's package by its layout
and not its guards: it accepts `unguardedBell`, whose `answer` run over a ring already answered
`first` returns an upsert of `rings` at that key (the second of two answers for one key), while the
claim says the row the caller pinned there was waiting. -/
theorem floor_bell_ringer (d : ByteArray → ByteArray) : ¬ Bell.ringer (laxBell d) := by
  intro h
  have hr := run_unguarded_second_answer
  simp only [Bool.and_eq_true] at hr
  obtain ⟨⟨⟨hacc, hrd⟩, hup⟩, hans⟩ := hr
  obtain ⟨hid, hp⟩ := bellReads_ok hrd
  obtain ⟨s, calls, rows, used, amt, vb, hrun, hm⟩ := bellUpserts_ok hup
  obtain ⟨l, y, c, sd, amt', ver, ob, -, hfind, hdec, -, -⟩ :=
    h (look := bellLook unguardedBell) (rv := bellRv bellAnsweredB) (pkg := bellPkg) hid hp hacc hrun hm
  have hob : ob = bellAnsweredB := by
    simp only [bellRv, if_true, List.find?, decide_true, Option.some.injEq, Prod.mk.injEq,
      Option.some.injEq, RowLeaf.row.injEq] at hfind
    exact hfind.2.2.1.symm
  subst hob
  unfold bellAnsweredReads at hans
  revert hans hdec
  generalize Lang.Wire.decodeData Lang.Bell.rings.val bellAnsweredB = R
  intro hans hdec
  subst hdec
  simp [waitingRow, Lang.Data.field, Lang.Row.find?] at hans

/-- **INHABITED (§6 (1)).** The claim's premise is reached at the deployed system: a package the
resident accepts (`shapeOk`), whose `answer` run over a waiting ring returns, upserting `rings` at
the ring's key. -/
theorem inhabited_bell_ringer (d : ByteArray → ByteArray) :
    ∃ (look : Pinned Digest) (rv : RowView Digest) (pkg : Digest) (p : Lang.Package) (state : Slots)
      (method : Nat) (args : ByteArray) (r : Req Digest) (budget : Nat) (s : Slots)
      (calls : List (Body Digest)) (rows : List (RowSlot Digest × RowAct)) (used amt : Nat) (kb vb : ByteArray),
      (deployed d).X.digestOf ((deployed d).X.env.bytes pkg) = some pkg ∧ Lang.readPackage look pkg = .ok p ∧
      (deployed d).bellAccept p = true ∧
      (deployed d).X.program.run look rv pkg state method args r budget = .ok (s, calls, rows, used) ∧
      (RowSlot.row ⟨r.self, 1, kb⟩, RowAct.upsert amt vb) ∈ rows := by
  have hr := run_bell_answers
  simp only [Bool.and_eq_true] at hr
  obtain ⟨⟨hacc, hrd⟩, hup⟩ := hr
  obtain ⟨hid, hp⟩ := bellReads_ok hrd
  obtain ⟨s, calls, rows, used, amt, vb, hrun, hm⟩ := bellUpserts_ok hup
  exact ⟨bellLook minBell, bellRv bellWaitingB, bellPkg, minBell, bellState, 0, bellArgs, bellReq, 1000000,
    s, calls, rows, used, amt, bellKey, vb, hid, hp, hacc, hrun, hm⟩

end ringerRun

/-! ## (2) One charged ask, right after the intent -/

section oneAsk
open Nanodregg.Hosting Nanodregg.Hosting.Resident Nanodregg.Hosting.Proofs.ResidentRun
  Nanodregg.Hosting.Proofs.BellConform

variable {D : Type} [Ord D] [DecidableEq D]


/-- The deployed tick is `tickWith actOn`. -/
theorem tickWith_actOn (w : Where) (m : Mem) : tickWith actOn w m = tickP w m := rfl

/-- A chain of ticks of one process life (`ResidentRun.Ticks`) of the tick around `act`. -/
inductive TicksWith (act : RingAct) (w : Where) : Mem → List (List Ev) → Prop
  | nil (m : Mem) : TicksWith act w m []
  | last {m : Mem} {es : List Ev} {e : Exit} {d : String} :
      Runs (tickWith act w m) es (.stop e d) → TicksWith act w m [es]
  | next {m m' : Mem} {es : List Ev} {ess : List (List Ev)} :
      Runs (tickWith act w m) es (.next m') → TicksWith act w m' ess → TicksWith act w m (es :: ess)

theorem ticksWith_actOn {w : Where} {m : Mem} {ess : List (List Ev)} (h : TicksWith actOn w m ess) :
    Ticks w m ess := by
  induction h with
  | nil m => exact .nil m
  | last h => exact .last h
  | next h _ ih => exact .next h ih

/-- **ONE CHARGED ASK, RIGHT AFTER THE INTENT** (§6 (2), the resident half). (a) Every path of the
act on the rings a tick read (any reply, any keep result, any ask end) asks at most once: when it
asks, it asks about the ring the decision chose (`decideTick`), and its effects begin with the
intent `(unanswered restart)` kept for that ring, successfully, and then the ask. (b) Along any
chain of ticks of one process around the act, between two asks about one ring, the first spent
(it left in full: the meter was charged), an effect freed the ring (an `ok` answer or a read that
no longer lists it). -/
def Bell.oneAsk (S : System D) : Prop :=
  (∀ (w : Where) (sh : Shape) (m : Mem) (p : List Ring) (es : List Ev) (a : Tick), Runs (S.ringAct w sh m p) es a →
    asks (core es) = [] ∨ ∃ r x post, decideTick p m.kept = .ask r ∧ asks (core es) = [r] ∧
      core es = .keep r intentText true :: .ask r (askOf w.conf r) x :: post) ∧
  (∀ (w : Where) (m : Mem) (ess : List (List Ev)) (r : Ring) (pre mid post : List Ev) (q q' : Broker.Ask)
    (x x' : AskEnd), TicksWith S.ringAct w m ess →
    core ess.flatten = pre ++ .ask r q x :: mid ++ .ask r q' x' :: post → (askText x).isSome →
      ∃ e ∈ mid, Frees r e)

/-- **TOP (§6 (2)).** The deployed resident's act (`actOn`, inside the deployed tick). -/
theorem top_bell_oneAsk (d : ByteArray → ByteArray) : Bell.oneAsk (deployed d) :=
  ⟨fun _ _ _ _ _ _ h => (act_counts (actOn_core h)).2.1,
   fun _ _ _ _ _ _ _ _ _ _ _ hT hc hx => bell_resident_conforms (ticksWith_actOn hT) hc hx⟩


/-- `askFirst`'s path on one pending ring: the ask (never sent), then the intent's keep, failed. -/
theorem askFirst_runs :
    Runs (askFirst bellWhere bellShape bellMem [bellRing])
      [.ask bellRing (askOf bellWhere.conf bellRing) (.notSent "x"), .keep bellRing intentText false]
      (.stop .volume "keep") := by
  unfold askFirst
  exact Runs.ask (.notSent "x") (Runs.keep false (Runs.done _))

/-- `order_refuses_ask_before_keep` on `askFirst`'s path: the deployed order grammar refuses it. -/
theorem askFirst_breaks_order :
    ¬ ActCore bellWhere.conf bellShape bellMem.kept [bellRing]
      (core [.ask bellRing (askOf bellWhere.conf bellRing) (.notSent "x"), .keep bellRing intentText false]) := by
  simp only [core_ask, core_keep, core_nil]
  exact order_refuses_ask_before_keep _ _ _ _ _ _ _ _

/-- **FLOOR (§6 (2)).** The claim refuses the act that asks before keeping the intent: on one
pending ring it asks with no intent kept before. -/
theorem floor_bell_oneAsk (d : ByteArray → ByteArray) : ¬ Bell.oneAsk (askFirstResident d) := by
  rintro ⟨ha, -⟩
  rcases ha bellWhere bellShape bellMem [bellRing] _ _ askFirst_runs with h | ⟨r, x, post, -, -, h⟩
  · simp [core, Ev.quiet, asks] at h
  · simp [core, Ev.quiet] at h

/-- **INHABITED (§6 (2)).** The deployed act reaches the claim's non-trivial case: on one pending
ring with nothing kept, a path asks about it. -/
theorem inhabited_bell_oneAsk :
    ∃ es a, Runs (actOn bellWhere bellShape bellMem [bellRing]) es a ∧ asks (core es) = [bellRing] := by
  obtain ⟨es, a, h, ha, -⟩ := ask_path_exists (w := bellWhere) (sh := bellShape) (m := bellMem)
    (p := [bellRing]) (r := bellRing) rfl (.reply .empty)
  exact ⟨es, a, h, ha⟩

end oneAsk

end Nanodregg.Spec
