/-
# Spec.Proofs.Law — B3's law-chain floor; B3 and C(ii)'s cancel inhabited

TOPLEVEL-SPEC §3.3. The claim `Integrity.law` (Claims: along an audited log an object's package never
changes and EVERY history of it in which a `NoRef` law is in force is a chain the law's reference
meaning admits) is proved of the deployed system by `top_integrity_law` (Deployed); its package
clause is refused by the raw writer (`floor_integrity_law`, Floor). This module:

* **Floor** `floor_integrity_lawChain`: the unjudged kernel (`Spec.Sim.Law.unjudged`, the program's
  `judge` admitting every step). The founder installs `Std.boundedPackage {n : nat} n 5` (the stdlib
  law `bounded`, `NoRef`), creates a data object under it with `n = 0` (re-derived from genesis by THE
  re-deriver), and writes `n := 9`, which the kernel refuses `lawDenied` and the unjudged kernel
  derives and admits. The write's own one-step history has the law in force, and `bounded_spec`
  admits no step to `n = 9`.
* **Inhabited** `inhabited_law`: on that object the deployed kernel derives and admits `n := 3`, a
  one-step history whose one judged step moves the state, the law in force in its view.
* **Inhabited** `inhabited_cancelOk` (C(ii), cancel): follow at the World holding the founder's
  recorded cancel steps the writer's tip page of `cancel CALL` and ends `done ok`.

Owed: the `NoRef` restriction (§11.6).
-/
import Spec.Proofs.Floor
import Spec.Sim.Law
import Lang.Proofs.Std
import Lang.Proofs.Receiver

namespace Nanodregg.Spec

open Nanodregg.Kernel Nanodregg.Kernel.Receive Nanodregg.Protocol Nanodregg.Codec

/-! ## The law's premises -/

theorem lPkg_body : lPkg.body = .record lFields := rfl
theorem lPkg_laws : "bounded" ∈ lPkg.laws := by simp [lPkg, Lang.Std.boundedPackage, Lang.Std.boundedPackageWith]
theorem lFields_find : Lang.Row.find? "bounded" lFields = some lLaw := by simp [lFields, Lang.Row.find?]
theorem lLaw_isLaw : Lang.IsLaw lLaw := Lang.isLaw_lawOf
theorem lLaw_noRef : Lang.NoRef lLaw := Lang.noRef_bounded _ _ _

/-- A write's request names its occasion `write`, a change. -/
theorem reqOf_write_occasion {X : Ctx Digest} {u : Unsigned Digest} {obj principal : Digest} :
    (Lang.reqData X.env.bytes (reqOf u obj principal .write)).field "occasion" =
      some (.inj "write" (.record [])) := by
  simp [Lang.reqData, Lang.Data.field, Lang.Row.find?, reqOf, Lang.occasionData]

/-! ## §3 INTEGRITY (B3), inhabited: a law judges a step -/

/-- **The judged run**: THE re-deriver accepts the install and the create from genesis; the object is
live, its state reads, the package's id is among its laws and reads as the package in the write's
view; the kernel derives the write `n := 3` (it passed `bounded`), which reads back as its event and
admits, and moves the state. -/
theorem run_law_judged :
    (match rederiveLog Xd wGenesis lLog with
     | .ok w =>
       match w.live Xd.env lObj with
       | some cell => decide (cell.kind = kindObject) &&
          (match Lang.readState Xd.digestOf (Lang.recordRow lPkg.state) (stateOf cell) with
           | .ok _ => true | .error _ => false) &&
          (match lawsOf Xd lObj cell with | .ok ls => decide (lId ∈ ls) | .error _ => false) &&
          (match Lang.readPackage (pinned Xd.env w (lWrite 3).unsigned.pins) lId with
           | .ok q => decide (q = lPkg) | .error _ => false) &&
          decide (applyEdits (stateOf cell) [(0, some (natBytes 3))] ≠ stateOf cell) &&
          match receive Xd w (lWrite 3) with
          | .ok t => decide (Xd.decodeCall t.event = some (lWrite 3)) &&
              (match World.admit Xd.env w t with | .ok _ => true | .error _ => false)
          | .error _ => false
       | none => false
     | .error _ => false) = true := by
  native_decide

/-- **INHABITED (B3).** From a genesis World, an audited log installs a `NoRef` law package and
creates a data object under it; on from there, an audited one-step log whose `ObjectHistory` has one
judged step, which moves the state, with the law in force in its view: the claim's chain clause
has a non-empty history to speak of. -/
theorem inhabited_law (d : ByteArray → ByteArray) (trusted : ByteArray) :
    ∃ (me : Command.Self Digest) (g w w' : World Digest) (l₀ l : List (Step Digest)) (obj law : Digest)
      (p : Lang.Package) (fs : List (Lang.Label × Lang.Term)) (ℓ : Lang.Label) (t : Lang.Term) (cell : Cell)
      (o : Lang.Data) (tr : List (Pinned Digest × Option Digest × List Digest × Req Digest × Slots × Slots ×
        List (Body Digest))),
      Start (deployed d) me trusted g ∧ Audited (deployed d) g l₀ w ∧
      p.body = .record fs ∧ ℓ ∈ p.laws ∧ Lang.Row.find? ℓ fs = some t ∧ Lang.IsLaw t ∧ Lang.NoRef t ∧
      Audited (deployed d) w l w' ∧ CellsCanon Xd.env w ∧ w.live Xd.env obj = some cell ∧
      cell.kind = kindObject ∧ Lang.readState Xd.digestOf (Lang.recordRow p.state) (stateOf cell) = .ok o ∧
      ObjectHistory Xd obj w w' tr ∧ tr ≠ [] ∧
      (∀ e ∈ tr, law ∈ e.2.1.toList ++ e.2.2.1 ∧ Lang.readPackage e.1 law = .ok p) ∧
      ∃ e ∈ tr, e.2.2.2.2.2.1 ≠ e.2.2.2.2.1 := by
  have hr := run_law_judged
  cases ho : rederiveLog Xd wGenesis lLog with
  | error e => rw [ho] at hr; cases hr
  | ok w =>
  rw [ho] at hr
  dsimp only at hr
  have hcan : CellsCanon Xd.env w := by
    have hs := (rederiveLog_sound ho).1
    unfold wGenesis at hs
    exact fold_cellsCanon (genesis_cellsCanon Xd _ _ _ _ _) hs
  have hfh := rederiveLog_sound ho
  have hst : Start (deployed d) sMe trusted wGenesis := .genesis _ _ _ _ _
  have hb : (lWrite 3).unsigned.body = .write lObj [(0, some (natBytes 3))] none := rfl
  revert hst
  revert hfh
  revert hr
  revert hb
  generalize lWrite 3 = c
  generalize natBytes 3 = v
  generalize lObj = obj
  generalize lId = lid
  generalize wGenesis = g
  generalize lLog = l₀
  generalize sMe = me
  intro hb hr hfh hst
  cases hl : w.live Xd.env obj with
  | none => rw [hl] at hr; cases hr
  | some cell =>
  rw [hl] at hr
  dsimp only at hr
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hr
  obtain ⟨⟨⟨⟨⟨hk, hro⟩, hlaws⟩, hpk⟩, hne⟩, hr⟩ := hr
  cases hs : Lang.readState Xd.digestOf (Lang.recordRow lPkg.state) (stateOf cell) with
  | error e => rw [hs] at hro; cases hro
  | ok o =>
  cases hL : lawsOf Xd obj cell with
  | error e => rw [hL] at hlaws; cases hlaws
  | ok ls =>
  rw [hL] at hlaws
  have hmem : lid ∈ ls := of_decide_eq_true hlaws
  cases hP : Lang.readPackage (pinned Xd.env w c.unsigned.pins) lid with
  | error e => rw [hP] at hpk; cases hpk
  | ok q =>
  rw [hP] at hpk
  have hq : q = lPkg := of_decide_eq_true hpk
  subst hq
  cases htw : receive Xd w c with
  | error e => rw [htw] at hr; cases hr
  | ok tw =>
  rw [htw] at hr
  dsimp only at hr
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hr
  obtain ⟨hd, hr⟩ := hr
  cases ha : World.admit Xd.env w tw with
  | error e => rw [ha] at hr; cases hr
  | ok w₂ =>
  obtain ⟨principal, laws, -, hau, hlw, -⟩ := write_next_slots htw ha hb hl (hcan _ _ hl)
  rw [hL] at hlw
  cases hlw
  have htr : ObjectHistory Xd obj w w₂ _ := .cons (.write htw ha hb hl (hcan _ _ hl) hau hL) (.nil w₂)
  have hsa : (deployed d).admit w tw = .ok w₂ := ha
  have haud : Audited (deployed d) w [.turn tw] w₂ :=
    ⟨by simp only [System.fold, System.step, hsa], ⟨c, hd, htw, fun _ _ => trivial⟩⟩
  refine ⟨me, g, w, w₂, l₀, [.turn tw], obj, lid, lPkg, lFields, "bounded", lLaw, cell, o, _, hst,
    audited_deployed.mpr hfh, lPkg_body, lPkg_laws, lFields_find, lLaw_isLaw, lLaw_noRef, haud, hcan, hl,
    hk, hs, htr, by simp, ?_, ⟨(pinned Xd.env w c.unsigned.pins, none, ls,
      reqOf c.unsigned obj principal .write, stateOf cell, applyEdits (stateOf cell) [(0, some v)], []), by simp, hne⟩⟩
  intro e he
  simp only [Option.toList_some, List.append_nil, List.mem_singleton] at he
  subst he
  exact ⟨by simpa using hmem, hP⟩

/-! ## §3 INTEGRITY (B3): the kernel no law judges -/

/-- **The unjudged run**: at the World of the judged run, the write `n := 9` (which the kernel
refuses `lawDenied`) is derived by the unjudged kernel, reads back as its event and admits; the
package is in force in its view; its new state reads with `n` above the bound. -/
theorem run_law_unjudged :
    (match rederiveLog Xd wGenesis lLog with
     | .ok w =>
       match w.live Xd.env lObj with
       | some cell => decide (cell.kind = kindObject) &&
          (match Lang.readState Xd.digestOf (Lang.recordRow lPkg.state) (stateOf cell) with
           | .ok _ => true | .error _ => false) &&
          (match Lang.readState Xd.digestOf (Lang.recordRow lPkg.state)
              (applyEdits (stateOf cell) [(0, some (natBytes 9))]) with
           | .ok dd => (match dd.field "n" with | some (.nat m) => decide (5 < m) | _ => false)
           | .error _ => false) &&
          (match lawsOf Xu lObj cell with | .ok ls => decide (lId ∈ ls) | .error _ => false) &&
          (match Lang.readPackage (pinned Xd.env w (lWrite 9).unsigned.pins) lId with
           | .ok q => decide (q = lPkg) | .error _ => false) &&
          match receive Xu w (lWrite 9) with
          | .ok t => decide (Xd.decodeCall t.event = some (lWrite 9)) &&
              (match World.admit Xd.env w t with | .ok _ => true | .error _ => false)
          | .error _ => false
       | none => false
     | .error _ => false) = true := by
  native_decide

/-- **FLOOR (B3, the law chain).** The claim refuses the kernel no law judges: from a canonical
World an audited one-step log writes `n := 9` to an object under `bounded n 5`; the write is a
history of the object with the law in force, and no `Std.Step` of `bounded` reaches `n = 9`
(`bounded_spec`). -/
theorem floor_integrity_lawChain (d : ByteArray → ByteArray) : ¬ Integrity.law (unjudged d) := by
  intro h
  have hr := run_law_unjudged
  cases ho : rederiveLog Xd wGenesis lLog with
  | error e => rw [ho] at hr; cases hr
  | ok w =>
  rw [ho] at hr
  dsimp only at hr
  have hcan : CellsCanon Xd.env w := by
    have hs := (rederiveLog_sound ho).1
    unfold wGenesis at hs
    exact fold_cellsCanon (genesis_cellsCanon Xd _ _ _ _ _) hs
  have hb : (lWrite 9).unsigned.body = .write lObj [(0, some (natBytes 9))] none := rfl
  revert hr
  revert hb
  generalize lWrite 9 = c
  generalize natBytes 9 = v
  generalize lObj = obj
  generalize lId = lid
  intro hb hr
  cases hl : w.live Xd.env obj with
  | none => rw [hl] at hr; cases hr
  | some cell =>
  rw [hl] at hr
  dsimp only at hr
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hr
  obtain ⟨⟨⟨⟨⟨hk, hro⟩, hrn⟩, hlaws⟩, hpk⟩, hr⟩ := hr
  cases hs : Lang.readState Xd.digestOf (Lang.recordRow lPkg.state) (stateOf cell) with
  | error e => rw [hs] at hro; cases hro
  | ok o =>
  cases hn : Lang.readState Xd.digestOf (Lang.recordRow lPkg.state) (applyEdits (stateOf cell) [(0, some v)]) with
  | error e => rw [hn] at hrn; cases hrn
  | ok dd =>
  rw [hn] at hrn
  dsimp only at hrn
  cases hf : dd.field "n" with
  | none => rw [hf] at hrn; cases hrn
  | some x =>
  rw [hf] at hrn
  cases x
  all_goals dsimp only at hrn
  all_goals first | (cases hrn; done) | skip
  rename_i m₀
  have hm₀ : 5 < m₀ := of_decide_eq_true hrn
  cases hL : lawsOf Xu obj cell with
  | error e => rw [hL] at hlaws; cases hlaws
  | ok ls =>
  rw [hL] at hlaws
  have hmem : lid ∈ ls := of_decide_eq_true hlaws
  cases hP : Lang.readPackage (pinned Xd.env w c.unsigned.pins) lid with
  | error e => rw [hP] at hpk; cases hpk
  | ok q =>
  rw [hP] at hpk
  have hq : q = lPkg := of_decide_eq_true hpk
  subst hq
  cases htw : receive Xu w c with
  | error e => rw [htw] at hr; cases hr
  | ok tw =>
  rw [htw] at hr
  dsimp only at hr
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hr
  obtain ⟨hd, hr⟩ := hr
  cases ha : World.admit Xd.env w tw with
  | error e => rw [ha] at hr; cases hr
  | ok w₂ =>
  have ha' : World.admit Xu.env w tw = .ok w₂ := ha
  have hl' : w.live Xu.env obj = some cell := hl
  obtain ⟨principal, laws, -, hau, hlw, -⟩ := write_next_slots htw ha' hb hl' (hcan _ _ hl)
  rw [hL] at hlw
  cases hlw
  have htr : ObjectHistory Xu obj w w₂ _ := .cons (.write htw ha' hb hl' (hcan _ _ hl) hau hL) (.nil w₂)
  have hsa : (unjudged d).admit w tw = .ok w₂ := ha
  have haud : Audited (unjudged d) w [.turn tw] w₂ :=
    ⟨by simp only [System.fold, System.step, hsa], ⟨c, hd, htw, fun _ _ => trivial⟩⟩
  obtain ⟨-, -, hall⟩ := h (obj := obj) (law := lid) (p := lPkg) (fs := lFields) (ℓ := "bounded") (t := lLaw)
    lPkg_body lPkg_laws lFields_find lLaw_isLaw lLaw_noRef haud hcan hl' hk
  have hin : ∀ e ∈ [(pinned Xu.env w c.unsigned.pins, (none : Option Digest), ls,
      reqOf c.unsigned obj principal .write, stateOf cell, applyEdits (stateOf cell) [(0, some v)],
      ([] : List (Body Digest)))], lid ∈ e.2.1.toList ++ e.2.2.1 ∧ Lang.readPackage e.1 lid = .ok lPkg := by
    intro e he
    simp only [List.mem_singleton] at he
    subst he
    exact ⟨by simpa using hmem, hP⟩
  obtain ⟨steps, hch, hmap⟩ := hall _ htr hin hs
  cases steps with
  | nil => simp at hmap
  | cons s rest =>
    obtain ⟨rq, n⟩ := s
    simp only [Option.toList_some, List.singleton_append, List.map_cons, List.map_nil, List.cons.injEq,
      Prod.mk.injEq] at hmap
    obtain ⟨⟨hreq, hn₂⟩, -⟩ := hmap
    have hn' : Lang.readState (unjudged d).X.digestOf (Lang.recordRow lPkg.state) (applyEdits (stateOf cell) [(0, some v)]) =
        .ok dd := hn
    rw [hn'] at hn₂
    cases hn₂
    cases hch with
    | cons hstep _ =>
      have hocc : rq.field "occasion" = some (.inj "write" (.record [])) := by
        rw [← hreq]; exact reqOf_write_occasion
      obtain ⟨m, hm, hle⟩ := Lang.Std.bounded_spec hstep.1 hocc (.inl (.inl ⟨_, rfl⟩))
      rw [hf] at hm
      cases hm
      omega

/-! ## §4 CONSENT (cancel), inhabited: a cancel that ends `ok` -/

/-- **The cancelled run**: the continuation parses as `cancel` of the founder's call, and follow,
holding the World THE re-deriver reaches on the cancel's log, steps the writer's page at its tip and
ends `done ok`. -/
theorem run_cancelled :
    ((match Command.State.ofBytes cKb with
      | some st => (match Command.parse (D := Digest) Xd.digestOf st.argv with
          | .ok (.cancel cb) => decide (cb = cCb)
          | _ => false)
      | none => false) &&
      match rederiveLog Xd wGenesis cancelLog with
      | .ok w => okDone ((deployed storeDigest).follow sMe ⟨w, none, none⟩ cKb cRes).2.2
      | .error _ => false) = true := by
  native_decide

/-- **INHABITED (C(ii), cancel).** The deployed follower, at a World an audited log from a genesis
World reaches (the founder's cancel recorded), ends a `cancel CALL` command `done ok`: the claim's
premise is reached. -/
theorem inhabited_cancelOk (trusted : ByteArray) :
    ∃ (me : Command.Self Digest) (g : World Digest) (f f' : Command.Follow Digest) (kb res o e : ByteArray)
      (p : Command.Persist Digest) (st : Command.State) (cb : ByteArray) (l : List (Step Digest)),
      Start (deployed storeDigest) me trusted g ∧ Audited (deployed storeDigest) g l f.world ∧
      Command.State.ofBytes kb = some st ∧
      Command.parse (deployed storeDigest).X.digestOf st.argv = .ok (Command.Cmd.cancel cb) ∧
      (deployed storeDigest).follow me f kb res = (f', p, .done CommandExit.ok.code.toUInt8 o e) := by
  have hr := run_cancelled
  simp only [Bool.and_eq_true] at hr
  obtain ⟨hk, hr⟩ := hr
  cases hs : Command.State.ofBytes cKb with
  | none => rw [hs] at hk; cases hk
  | some st =>
    rw [hs] at hk
    dsimp only at hk
    cases hp : Command.parse (D := Digest) Xd.digestOf st.argv with
    | error e => rw [hp] at hk; cases hk
    | ok cmd =>
      rw [hp] at hk
      cases cmd
      all_goals dsimp only at hk
      all_goals first | (cases hk; done) | skip
      rename_i cb
      cases hw : rederiveLog Xd wGenesis cancelLog with
      | error e => rw [hw] at hr; cases hr
      | ok w =>
        rw [hw] at hr
        dsimp only at hr
        have hfh := rederiveLog_sound hw
        have hst : Start (deployed storeDigest) sMe trusted wGenesis := .genesis _ _ _ _ _
        revert hst
        revert hfh
        revert hr
        revert hs
        generalize cKb = kb
        generalize cRes = res
        generalize wGenesis = g
        generalize cancelLog = l
        generalize sMe = me
        intro hs hr hfh hst
        cases hR : (deployed storeDigest).follow me ⟨w, none, none⟩ kb res with
        | mk f' rest =>
          obtain ⟨p, rp⟩ := rest
          rw [hR] at hr
          obtain ⟨o, e, hd⟩ := okDone_eq hr
          subst hd
          exact ⟨me, g, ⟨w, none, none⟩, f', kb, res, o, e, p, st, cb, l, hst, audited_deployed.mpr hfh,
            hs, hp, hR⟩

end Nanodregg.Spec
