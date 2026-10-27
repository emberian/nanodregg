/-
# Lang.Proofs.StdActivityMonitor — the receiver is the monitor (PROT-4, LANG-75.9)

An activity's protocol is a machine per KEY of its log relation (`absent → waiting → answered →
absent`, and, under a declared patience, `waiting → absent` from the row's deadline on: LANG-76), enforced by the log's row guard (`activityWaiting`), not a phase field in object state
(`Lang.StdActivity`: "No phase field is written into object state"). So the monitor theorem is at
the guard's grain:

* `waiting_body_step`: what the waiting guard admits, run as the receiver runs a package field
  (`Admits`, any closure environment), is one of `WaitingStep`'s four actions.
* `activity_monitor_safe` (`activity_program_safe` on `Lang.program`'s `run`): for a package meeting
  its premises, every edit at the log of a method run that RETURNED is such a step, for every method
  of the package, generated or hand-written, from
  `run_edits_guarded` (`Lang.Proofs.Rel`: an admitted run's edits passed their guards), the loaded
  closure (`load_top`) and the relation's guard (`runLaw_ref_admits`).

Operationally a follower re-runs the monitor without citing it: `Receive.rederive` calls `submit`, whose `receive` runs
`program.run`, which runs `guardEdits`. The theorem it can cite is `activity_program_safe`, for a
package that meets the premises. This module decides the generated fixture
(`activity_fixture_monitored`, StdActivityTeeth). The deployed Bell meets them as installed (no
imports, no holes, a record body, `rung` the waiting guard): `Lang.Proofs.Bell.bell_monitored`, with
`Lang.Journey`'s LBw deciding the shipped core is that package (HOSTING-44). A package built on
`Std.hole` is outside the premises (its root's body is an application and it has imports). The
`StdActivityTeeth` admitting rows (`activity_start_unanswered`, `activity_answer_once`,
`activity_retire_after_answer`) are closed instances of `start`, `answer` and `retire`. The `waiting_*` statements in `Lang.Proofs.StdActivity` stay: they are the iff (the guard
also ADMITS each step), which is the monitor's transparency half, not its safety half.
-/
import Lang.Proofs.StdActivity
import Lang.Proofs.Rel
import Lang.Proofs.Receiver
import Lang.Proofs.LiveClosed

namespace Nanodregg.Lang.Std

/-- The resumer, applied to the state and the request (the guard's own operands), says `true`. -/
def Resumes (lib : List Term) (resumer : Term) (req state : Data) : Prop :=
  ∃ env : Env, env[3]? = some state.toVal ∧ env[2]? = some req.toVal ∧
    BigStep lib env (activityApply resumer [.var 3, .var 2]) (.ok (.bool true))

/-- **The log row's machine** (`absent → waiting → answered → absent`, `waiting → absent` past a
deadline): the enabled actions of one key of an activity log declared with `patience`, as an edit
`ed` over the row `old` the kernel found at its key (both as the waiting guard sees them). `start`:
an insert, by the key's own agent, of an unanswered row. `answer`: an upsert, by the resumer, of a
waiting row, keeping its capture and answering its own plan. `retire`: a retraction of an answered
row. `timedOut` (LANG-76): with a declared patience `p`, a retraction of an unanswered row by
anyone, by a call signed at a `notBefore` at least the key's `notBefore` + `p`. Nothing else is a
step; with no patience there is no `timedOut`. -/
inductive WaitingStep (lib : List Term) (resumer : Term) (patience : Option Nat) (req state : Data) :
    Data → Data → Prop
  | start {key c old : Data} {a : ByteArray} :
      key.field "agent" = some (.digest a) → req.field "agent" = some (.digest a) →
      WaitingStep lib resumer patience req state
        (.inj "insert" (.record [("key", key),
          ("val", .record [("answered", .inj "none" (.record [])), ("captured", c)])])) old
  | answer {key c x : Data} {l : Label} :
      Resumes lib resumer req state →
      WaitingStep lib resumer patience req state
        (.inj "upsert" (.record [("key", key),
          ("val", .record [("answered", .inj "some" (.inj l x)), ("captured", .inj l c)])]))
        (.inj "some" (.record [("answered", .inj "none" (.record [])), ("captured", .inj l c)]))
  | retire {key a c : Data} :
      WaitingStep lib resumer patience req state (.inj "retract" (.record [("key", key)]))
        (.inj "some" (.record [("answered", .inj "some" a), ("captured", c)]))
  | timedOut {key c : Data} {p n m : Nat} :
      patience = some p → key.field "notBefore" = some (.nat n) → req.field "notBefore" = some (.nat m) →
      n + p ≤ m →
      WaitingStep lib resumer patience req state (.inj "retract" (.record [("key", key)]))
        (.inj "some" (.record [("answered", .inj "none" (.record [])), ("captured", c)]))

theorem conforms_empty {d : Data} (h : Conforms d (.record [])) : d = .record [] := by
  cases h with | record hr => cases hr; rfl

/-- A value of an option type is `none` or `some` of a conforming value. -/
theorem conforms_opt {d : Data} {T : Ty} (h : Conforms d (optTy T)) :
    d = optD none ∨ ∃ z, d = optD (some z) ∧ Conforms z T := by
  cases h with
  | inj hf hc =>
    rename_i ℓ A z
    simp only [Row.find?] at hf
    split at hf
    · cases hf; subst_vars; exact .inl (by rw [conforms_empty hc]; rfl)
    · split at hf
      · cases hf; subst_vars; exact .inr ⟨z, rfl, hc⟩
      · cases hf

private theorem conforms_logVal {v : Data} {plans : List ActivityPlan} (h : Conforms v (activityLogVal plans)) :
    ∃ a c, v = .record [("answered", a), ("captured", c)] ∧ Conforms a (optTy (activityResponses plans)) ∧
      Conforms c (activityCaptured plans) := by
  cases h with
  | record hr =>
    cases hr with
    | cons ha hr => cases hr with
      | cons hc hr => cases hr; exact ⟨_, _, rfl, ha, hc⟩

private theorem conforms_row {y : Data} {d : RelDecl} {plans : List ActivityPlan}
    (hv : d.val = activityLogVal plans) (h : Conforms y (rowTy d)) :
    ∃ k a c, y = .record [("key", k), ("val", .record [("answered", a), ("captured", c)])] ∧
      Conforms a (optTy (activityResponses plans)) ∧ Conforms c (activityCaptured plans) := by
  cases h with
  | record hr =>
    cases hr with
    | cons _ hr => cases hr with
      | cons hval hr =>
        cases hr
        rw [hv] at hval
        obtain ⟨a, c, rfl, ha, hc⟩ := conforms_logVal hval
        exact ⟨_, a, c, rfl, ha, hc⟩

private theorem conforms_sum {d : Data} {r : List (Label × Ty)} (h : Conforms d (.sum r)) :
    ∃ l z, d = .inj l z := by
  cases h with | inj _ _ => exact ⟨_, _, rfl⟩

/-- Selecting a field of a term whose value is data means the field's data. -/
private theorem bigStep_get_data {lib : List Term} {env : Env} {t : Term} {d : Data} {ℓ : Label} {v : Val}
    (ht : BigStep lib env t (.ok d.toVal)) (h : BigStep lib env (.get t ℓ) (.ok v)) :
    ∃ x, d.field ℓ = some x ∧ v = x.toVal := by
  cases h with
  | get ht' hs =>
    have he := bigStep_deterministic ht ht'
    cases he
    cases d with
    | record fs =>
      cases hs with
      | field hf hb =>
        obtain ⟨x, hx, rfl, rfl⟩ := find_rowToVal hf
        obtain ⟨u, hu, hu'⟩ := bigStep_var_inv hb
        simp at hu; subst hu; cases hu'
        exact ⟨x, hx, rfl⟩
    | nat _ | bool _ | bytes _ | digest _ | inj _ _ => cases hs

private theorem case_at {lib : List Term} {env : Env} {t : Term} {arms : List (Label × Term)}
    {l : Label} {w v : Val} (ht : BigStep lib env t (.ok (.inj l w)))
    (h : BigStep lib env (.case t arms) (.ok v)) :
    ∃ body, Row.find? l arms = some body ∧ BigStep lib (w :: env) body (.ok v) := by
  obtain ⟨l', w', b, ht', hf', hb⟩ := bigStep_case_ok h
  have he := bigStep_deterministic ht ht'
  cases he
  exact ⟨b, hf', hb⟩

theorem deq_true {u v : Data} (h : primEval .deq u.toVal v.toVal = .ok (.bool true)) :
    ∃ a, u = .digest a ∧ v = .digest a := by
  cases u <;> cases v <;> simp [Data.toVal, primEval] at h
  subst h
  exact ⟨_, rfl, rfl⟩

private theorem find_map_fn {names : List (Label × Unit)} {f : Label × Unit → Label × Term} {ℓ : Label}
    {body : Term} (hf : ∀ p, (f p).1 = p.1) (h : Row.find? ℓ (names.map f) = some body) : body = (f (ℓ, ())).2 := by
  induction names with
  | nil => simp [Row.find?] at h
  | cons p ps ih =>
    rcases p with ⟨k, u⟩
    simp only [List.map_cons, Row.find?, hf] at h
    split at h
    · rename_i hk; cases h; subst hk; cases u; rfl
    · exact ih h

/-- An admitting plan comparison compares the two tags. -/
private theorem samePlan_true {lib : List Term} {env : Env} {plans : List ActivityPlan} {x y : Term}
    {l k : Label} {v w : Val} (hx : BigStep lib env x (.ok (.inj l v))) (hy : BigStep lib env y (.ok (.inj k w)))
    (h : BigStep lib env (activitySamePlan plans x y) (.ok (.bool true))) : l = k := by
  unfold activitySamePlan at h
  obtain ⟨b3, e3, wy, hf3, hy', hb3⟩ := bigStep_app_ok h
  obtain ⟨b2, e2, wx, hf2, hx', hb2⟩ := bigStep_app_ok hf3
  cases hf2
  cases hb2
  cases bigStep_deterministic hx hx'
  cases bigStep_deterministic hy hy'
  obtain ⟨body1, hf1, hb1⟩ := case_at (.var rfl) hb3
  rw [find_map_fn (fun _ => rfl) hf1] at hb1
  obtain ⟨body2, hf2, hb2⟩ := case_at (.var rfl) hb1
  rw [find_map_fn (fun _ => rfl) hf2] at hb2
  have := bigStep_bool_inv hb2
  simp at this
  exact this

/-- **What the waiting guard admits is a step of the log row's machine** (guard grain): over any
closure environment (as the receiver runs a package field, `Admits`), an edit of the log's edit type
over an old row of its value type that the generated waiting guard accepts is one of `WaitingStep`'s
four actions, at the guard's own patience. -/
theorem waiting_body_step {lib : List Term} {T : Ty} {plans : List ActivityPlan} {d : RelDecl}
    {resumer : Term} {names : ActivityVocabulary} {patience : Option Nat} {ed old req state : Data}
    {cenv : Env} {w : Val}
    (hw : (activityCaptured plans).wf = true) (hv : d.val = activityLogVal plans)
    (hed : Conforms ed (relEditTy d)) (hold : Conforms old (optTy d.val))
    (h : BigStep lib ((guardIn ed old).toVal :: req.toVal :: state.toVal :: cenv)
      (lawBody (activityWaiting T plans d resumer names patience)) (.ok (.inj "ok" w))) :
    WaitingStep lib resumer patience req state ed old := by
  simp only [activityWaiting, lawBody] at h
  obtain ⟨ℓ, y, body, hfe, harm, hb⟩ := case_field rfl h
  have hed' : ed = .inj ℓ y := by simpa [guardIn, Data.field, Row.find?] using hfe
  subst hed'
  rw [hv] at hold
  obtain ⟨A, hA, hy⟩ : ∃ A, Row.find? ℓ ([("insert", rowTy d)] ++ (if d.retract then [("retract", .record [("key", keyTy d)])] else []) ++ [("upsert", rowTy d)]) = some A ∧ Conforms y A := by
    cases hed with | inj hf hc => exact ⟨_, hf, hc⟩
  simp only [Row.find?] at harm
  split at harm
  · -- insert
    rename_i hl; subst hl; cases harm
    simp [Row.find?] at hA; subst hA
    obtain ⟨k, a, c, rfl, ha, hc⟩ := conforms_row hv hy
    obtain ⟨hcnd, hrest⟩ := guard_ok hb
    obtain ⟨x1, y1, hx1, hy1, hp⟩ := bigStep_prim_ok hcnd
    obtain ⟨ag, hag, rfl⟩ := bigStep_get_data (.get (.var rfl) (.field rfl (.var rfl))) hx1
    obtain ⟨ra, hra, rfl⟩ := bigStep_getVar rfl hy1
    obtain ⟨dg, rfl, rfl⟩ := deq_true hp
    rcases conforms_opt ha with rfl | ⟨z, rfl, -⟩
    · exact .start hag hra
    · obtain ⟨body, hf, hb'⟩ := case_at (.get (.get (.var rfl) (.field rfl (.var rfl))) (.field rfl (.var rfl))) hrest
      simp [Row.find?] at hf; subst hf
      exact (refusedT_not_ok hb').elim
  split at harm
  · -- retract
    rename_i _ hl; subst hl; cases harm
    cases hdr : d.retract <;> simp [hdr, Row.find?] at hA
    subst hA
    obtain ⟨k, rfl⟩ : ∃ k, y = .record [("key", k)] := by
      cases hy with | record hr => cases hr with | cons _ hr => cases hr; exact ⟨_, rfl⟩
    rcases conforms_opt hold with rfl | ⟨row, rfl, hrow⟩
    · obtain ⟨body, hf, hb'⟩ := case_at (.get (.var rfl) (.field rfl (.var rfl))) hb
      simp [Row.find?] at hf; subst hf
      exact (refusedT_not_ok hb').elim
    · obtain ⟨a0, c0, rfl, ha0, -⟩ := conforms_logVal hrow
      obtain ⟨body, hf, hb'⟩ := case_at (.get (.var rfl) (.field rfl (.var rfl))) hb
      simp [Row.find?] at hf; subst hf
      rcases conforms_opt ha0 with rfl | ⟨z, rfl, -⟩
      · obtain ⟨body, hf, hb''⟩ := case_at (.get (.var rfl) (.field rfl (.var rfl))) hb'
        simp [Row.find?] at hf; subst hf
        cases patience with
        | none => exact (refusedT_not_ok hb'').elim
        | some p =>
          obtain ⟨hc, -⟩ := guard_ok hb''
          simp only [activityDue, natT] at hc
          obtain ⟨x, y, hx, hy, hle⟩ := bigStep_prim_ok hc
          obtain ⟨a, b, rfl, rfl, hab⟩ := primEval_le_true hle
          obtain ⟨x2, y2, hx2, hy2, hadd⟩ := bigStep_prim_ok hx
          cases bigStep_nat_inv hy2
          obtain ⟨kn, hkn, rfl⟩ := bigStep_get_data (.get (.var rfl) (.field rfl (.var rfl))) hx2
          cases kn with
          | nat n =>
            simp only [Data.toVal, primEval, natResult] at hadd
            split at hadd
            · simp only [Except.ok.injEq, Val.nat.injEq] at hadd
              exact .timedOut rfl hkn (getVar_nat rfl hy) (by omega)
            · cases hadd
          | _ => simp [Data.toVal, primEval] at hadd
      · exact .retire
  split at harm
  · -- upsert
    rename_i _ _ hl; subst hl; cases harm
    cases hdr : d.retract <;> simp [hdr, Row.find?] at hA <;> subst hA <;>
    · obtain ⟨k, a, c, rfl, ha, hc⟩ := conforms_row hv hy
      obtain ⟨hres, hrest⟩ := guard_ok hb
      have hR : Resumes lib resumer req state := ⟨_, rfl, rfl, hres⟩
      rcases conforms_opt hold with rfl | ⟨row, rfl, hrow⟩
      · obtain ⟨body, hf, hb'⟩ := case_at (.get (.var rfl) (.field rfl (.var rfl))) hrest
        simp [Row.find?] at hf; subst hf
        exact (refusedT_not_ok hb').elim
      · obtain ⟨a0, c0, rfl, ha0, hc0⟩ := conforms_logVal hrow
        obtain ⟨body, hf, hb1⟩ := case_at (.get (.var rfl) (.field rfl (.var rfl))) hrest
        simp [Row.find?] at hf; subst hf
        rcases conforms_opt ha0 with rfl | ⟨z0, rfl, -⟩
        · obtain ⟨body, hf, hb2⟩ := case_at (.get (.var rfl) (.field rfl (.var rfl))) hb1
          simp [Row.find?] at hf; subst hf
          obtain ⟨hq, hb3⟩ := guard_ok hb2
          have hcc : c = c0 := (eqData_true hw
            (.get (.get (.var rfl) (.field rfl (.var rfl))) (.field rfl (.var rfl)))
            (.get (.var rfl) (.field rfl (.var rfl))) hq hc hc0).mp rfl
          subst hcc
          rcases conforms_opt ha with rfl | ⟨z, rfl, hz⟩
          · obtain ⟨body, hf, hb4⟩ := case_at
              (.get (.get (.var rfl) (.field rfl (.var rfl))) (.field rfl (.var rfl))) hb3
            simp [Row.find?] at hf; subst hf
            exact (refusedT_not_ok hb4).elim
          · obtain ⟨body, hf, hb4⟩ := case_at
              (.get (.get (.var rfl) (.field rfl (.var rfl))) (.field rfl (.var rfl))) hb3
            simp [Row.find?] at hf; subst hf
            obtain ⟨hp, -⟩ := guard_ok hb4
            obtain ⟨l, cc, rfl⟩ := conforms_sum hc
            obtain ⟨k', zz, rfl⟩ := conforms_sum hz
            have hlk := samePlan_true
              (.get (.get (.var rfl) (.field rfl (.var rfl))) (.field rfl (.var rfl))) (.var rfl) hp
            subst hlk
            exact .answer hR
        · obtain ⟨body, hf, hb2⟩ := case_at (.get (.var rfl) (.field rfl (.var rfl))) hb1
          simp [Row.find?] at hf; subst hf
          exact (refusedT_not_ok hb2).elim
  · cases harm

/-! ## As the receiver loads and runs it -/

mutual
/-- Structural equality names no closure package. -/
theorem noRef_eqDataBody : (T : Ty) → NoRef (eqDataBody T)
  | .nat => by simp [eqDataBody, NoRef]
  | .bool => by simp [eqDataBody, NoRef]
  | .bytes => by simp [eqDataBody, NoRef]
  | .digest => by simp [eqDataBody, NoRef]
  | .fn _ _ => by simp [eqDataBody, NoRef]
  | .record r => by rw [eqDataBody]; exact noRef_eqDataFields r
  | .sum r => by
    rw [eqDataBody]
    simp only [NoRef, true_and]
    rw [NoRefStd.row_iff]
    intro e he
    simp only [List.mem_map] at he
    obtain ⟨p, -, rfl⟩ := he
    simp only [NoRef, true_and]
    rw [NoRefStd.row_iff]
    intro e he
    simp only [List.mem_map] at he
    obtain ⟨q, -, rfl⟩ := he
    dsimp only
    split
    · simp only [NoRef, and_true]; exact noRef_eqDataBody p.val.2
    · simp [NoRef]
termination_by T => sizeOf T
decreasing_by
  all_goals simp_wf
  · have h := List.sizeOf_lt_of_mem p.property
    rcases p with ⟨⟨l, t⟩, hm⟩
    simp_all; omega

theorem noRef_eqDataFields : (r : List (Label × Ty)) → NoRef (eqDataFields r)
  | [] => by simp [eqDataFields, NoRef]
  | (l, t) :: r => by
    rw [eqDataFields]
    simp only [NoRef, and_true]
    exact ⟨noRef_eqDataBody t, noRef_eqDataFields r⟩
termination_by r => sizeOf r
end

/-- The waiting guard names no closure package beyond its resumer. -/
theorem noRef_activityWaiting (T : Ty) (plans : List ActivityPlan) (d : RelDecl) {resumer : Term}
    (names : ActivityVocabulary) (patience : Option Nat) (h : NoRef resumer) :
    NoRef (activityWaiting T plans d resumer names patience) := by
  have hl : ∀ k r : Term, NoRef k → NoRef r → NoRef (activityLate patience k r) := fun k r hk hr => by
    cases patience <;> simp [activityLate, activityDue, guard, natT, okT, refusedT, NoRef, NoRefRow, hk, hr]
  have hq : ∀ (C : Ty) (x y : Term), NoRef x → NoRef y → NoRef (eqData C x y) := fun C x y hx hy => by
    simp only [eqData, NoRef]; exact ⟨⟨noRef_eqDataBody C, hx⟩, hy⟩
  have hp : ∀ (x y : Term), NoRef x → NoRef y → NoRef (activitySamePlan plans x y) := fun x y hx hy => by
    simp only [activitySamePlan, NoRef, true_and]
    refine ⟨⟨?_, hx⟩, hy⟩
    rw [NoRefStd.row_iff]
    intro e he
    simp only [List.mem_map] at he
    obtain ⟨⟨l, _⟩, -, rfl⟩ := he
    simp only [NoRef, true_and]
    rw [NoRefStd.row_iff]
    intro e he
    simp only [List.mem_map] at he
    obtain ⟨⟨k, _⟩, -, rfl⟩ := he
    simp [NoRef]
  simp only [activityWaiting, activityApply, List.foldl, guard, NoRef, NoRefRow, okT, refusedT, true_and,
    and_true, h]
  exact ⟨hl _ _ trivial trivial, hq _ _ _ trivial trivial, hp _ _ trivial trivial⟩

section
open Nanodregg.Kernel.Receive
variable {D : Type} (bytesOf : D → ByteArray) (digestOf : ByteArray → Option D) (rc : ReceiptCheck)

/-- **The receiver is the monitor** (`activity_monitor_safe`, PROT-4; LANG-76 restates it at the
guard's declared patience, which adds `WaitingStep.timedOut`): for a method run of a package
the pinned cell holds whose relation `ℓ` is guarded by a field that is the generated waiting guard,
every edit at `ℓ` of a run that returned is a step of the log row's machine (`WaitingStep`) over the
old row the kernel found at its key, under the run's request and the state before the run. Every
method of such a package, generated or written by hand, is covered: the premises are on the
package's guard, not on the method. -/
theorem activity_monitor_safe {rc : Lang.ReceiptCheck} {look : Pinned D} {rv : RowView D} {pkg : D} {state : Kernel.Slots}
    {method : Nat} {args : ByteArray} {r : Req D} {budget : Nat} {s : Kernel.Slots}
    {calls : List (Body D)} {rows : List (Kernel.RowSlot D × Kernel.RowAct)} {t n : Nat}
    {p : Package} {fs : List (Label × Term)} {ℓ gl : Label} {d : RelDecl} {T : Ty}
    {plans : List ActivityPlan} {resumer : Term} {names : ActivityVocabulary} {patience : Option Nat}
    (hid : digestOf (bytesOf pkg) = some pkg) (hp : readPackage look pkg = .ok p)
    (hb : p.body = .record fs) (hrel : Row.find? ℓ p.rels = some d) (hg : d.guard = some gl)
    (hf : Row.find? gl fs = some (activityWaiting T plans d resumer names patience)) (hnr : NoRef resumer)
    (hv : d.val = activityLogVal plans) (hw : (activityCaptured plans).wf = true)
    (h : runMeasured bytesOf digestOf rc look rv pkg state method args r budget = .ok (s, calls, rows, t, n)) :
    ∃ S, ∃ es : List (Edit D), runSetup bytesOf digestOf rc look rv pkg state method args r = .ok S ∧
      rows = es.map (fun x => (x.slot, x.act)) ∧
      ∀ x ∈ es, x.label = ℓ → ∃ o, guardOld digestOf rv r.self x = .ok o ∧
        WaitingStep S.lib resumer patience (reqData bytesOf r) S.state x.data o := by
  obtain ⟨S, v, used, c, e, ds, left, es, hS, hrun, hx, hes, hge, rfl⟩ := runMeasuredWith_ok h
  refine ⟨S, es, hS, rfl, fun x hxe hlab => ?_⟩
  obtain ⟨L, g, p', ℓm, sg, sd, ad, wd, hr0, hl, hpg, hres, hst, hargs, -, hrows, rfl⟩ := runSetup_spec hS
  obtain ⟨hpg', f, hlib⟩ := load_top bytesOf digestOf (fuel := closureDepthMax - 1) hid hp hl
  rw [hpg'] at hpg
  cases hpg
  obtain ⟨mty, hm, hA⟩ := resolveMethod_spec hres
  have hok := invoke_never_stuck (ticks := budget - 0) hl hpg' hm hA hst hargs hrows hr0
  simp only at hrun hx hes hge ⊢
  rw [hrun] at hok
  have hcf := extract_conforms (load_libTy hl).1 (resultTy p.state sg.calls (editTy p.rels) sg.edits) hok hx
  cases hcf with
  | record hrow =>
    cases hrow with
    | cons _ hrest =>
      cases hrest with
      | cons hed _ =>
        obtain ⟨hd, hc⟩ := editsOf_conforms hed hes x hxe
        rw [hlab, hrel] at hd
        cases hd
        obtain ⟨o, ho, hgl⟩ := guardEdits_ok hge x hxe
        have hadm := Std.runLaw_ref_admits (g := g) (fs := Term.relocateRow f fs)
          (by rw [hlib, hb]; rfl)
          (by rw [find_relocateRow, hf, Option.map_some, relocate_noRef _ _ (noRef_activityWaiting T plans x.decl names patience hnr)]; rfl)
          (hgl gl hg)
        obtain ⟨cenv, w, hbody⟩ := hadm
        exact ⟨o, ho, waiting_body_step hw hv hc (guardOld_conforms ho) hbody⟩


/-- **The monitor on the deployed run**: `activity_monitor_safe` for `Lang.program`'s `run`, the run
the kernel's history records (`ObjectStep.invoke`), at a package with no imports and no holes, where
the live setup is the closed one (`runMeasuredLive_leaf_closed`). -/
theorem activity_program_safe {rc : Lang.ReceiptCheck} {look : Pinned D} {rv : RowView D} {pkg : D} {state : Kernel.Slots}
    {method : Nat} {args : ByteArray} {r : Req D} {budget : Nat} {s : Kernel.Slots}
    {calls : List (Body D)} {rows : List (Kernel.RowSlot D × Kernel.RowAct)} {used : Nat}
    {p : Package} {fs : List (Label × Term)} {ℓ gl : Label} {d : RelDecl} {T : Ty}
    {plans : List ActivityPlan} {resumer : Term} {names : ActivityVocabulary} {patience : Option Nat}
    (hid : digestOf (bytesOf pkg) = some pkg) (hp : readPackage look pkg = .ok p)
    (hi : p.imports = []) (hc : p.holes = [])
    (hb : p.body = .record fs) (hrel : Row.find? ℓ p.rels = some d) (hg : d.guard = some gl)
    (hf : Row.find? gl fs = some (activityWaiting T plans d resumer names patience)) (hnr : NoRef resumer)
    (hv : d.val = activityLogVal plans) (hw : (activityCaptured plans).wf = true)
    (h : (Lang.program bytesOf digestOf rc).run look rv pkg state method args r budget = .ok (s, calls, rows, used)) :
    ∃ S, ∃ es : List (Edit D), runSetup bytesOf digestOf rc look rv pkg state method args r = .ok S ∧
      rows = es.map (fun x => (x.slot, x.act)) ∧
      ∀ x ∈ es, x.label = ℓ → ∃ o, guardOld digestOf rv r.self x = .ok o ∧
        WaitingStep S.lib resumer patience (reqData bytesOf r) S.state x.data o := by
  change (runMeasuredLive bytesOf digestOf rc look rv pkg state method args r budget).map _ = _ at h
  rw [runMeasuredLive_leaf_closed hid hp hi hc] at h
  cases hm : runMeasured bytesOf digestOf rc look rv pkg state method args r budget with
  | error e => rw [hm] at h; cases h
  | ok x =>
    rw [hm] at h
    obtain ⟨s', calls', rows', t', n'⟩ := x
    simp only [Except.map, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h
    exact activity_monitor_safe bytesOf digestOf hid hp hb hrel hg hf hnr hv hw hm

end
