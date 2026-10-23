/-
# Lang.Proofs.Bell — the deployed Bell, as a witness (HOSTING-43 (e), HOSTING-44)

What the installed Bell (`world/resident/Bell`) does, at every package `Lang.Bell.shapeOk` holds of
(the journey row LBw computes it of the shipped core text):

* `rung_is_waiting`: the log `rings` is guarded by the field `rung`, and that field is the generated
  waiting guard over the Bell's plans and resumer (`deq req.agent state.resident`).
* `bell_monitored`: `activity_program_safe` at the Bell, through `Lang.program`'s `run` (the run the
  kernel records): every `rings` edit of a run of ANY Bell method that returned is a step of the log
  row's machine (`WaitingStep`) over the row the kernel found at its key. The Bell's root has no
  imports and no holes, and its body is a record, so the closed monitor applies as installed.
* `resumes_resident`: the Bell's resumer admits exactly a request whose signer is the state's
  resident, so the `answer` step of that machine is the resident's.
* `answer_run`: a run of the method labelled `answer` that returned decoded `answerData nb x k y`
  (within its bounds), was signed by the resident, makes no calls, and its row acts are exactly the
  upsert of `rings` at `(k, nb)` to `answeredVal x y` (`answered (some (ask y))`, captured
  `ask {text := x}`) and the retract of `pending` there.
-/
import Lang.Bell
import Lang.Proofs.StdActivityMonitor
import Lang.Proofs.MethodRun
import Lang.Proofs.Invoke

namespace Nanodregg.Lang.Bell

open Nanodregg.Lang Nanodregg.Lang.Std

/-- What `shapeOk` says, as statements. -/
theorem shape_parts {p : Package} (h : shapeOk p = true) :
    p.imports = [] ∧ p.holes = [] ∧ p.state = S ∧ p.rels = rels ∧
      Row.find? "answer" (recordRow p.iface) = some answerTy ∧
      ∃ fs, p.body = .record fs ∧ Row.find? "answer" fs = some answer ∧ Row.find? "rung" fs = some rung := by
  simp only [shapeOk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨hi, hh⟩, hs⟩, hr⟩, ha⟩, hb⟩ := h
  refine ⟨hi, hh, hs, hr, ha, ?_⟩
  generalize p.body = t at hb
  cases t with
  | record fs =>
    simp only [bodyOk, Bool.and_eq_true, decide_eq_true_eq] at hb
    exact ⟨fs, rfl, hb⟩
  | _ => simp [bodyOk] at hb

/-- **The compiled Bell's `rung` is the waiting guard**: at a Bell, `rings` is relation `rings`
guarded by the field `rung`, and that field is `activityWaiting` over the Bell's state, plans, log,
resumer and refusal names; the premises `activity_program_safe` takes of the guard hold. -/
theorem rung_is_waiting {p : Package} (h : shapeOk p = true) :
    ∃ fs, p.body = .record fs ∧ Row.find? "rings" p.rels = some rings ∧ rings.guard = some "rung" ∧
      Row.find? "rung" fs = some (activityWaiting S plans rings resumer names) ∧
      rings.val = activityLogVal plans ∧ NoRef resumer ∧ (activityCaptured plans).wf = true := by
  obtain ⟨-, -, -, hr, -, fs, hb, -, hg⟩ := shape_parts h
  refine ⟨fs, hb, by rw [hr]; rfl, rfl, hg, rfl, ?_, by decide⟩
  simp [resumer, NoRef]

section
variable {D : Type} (bytesOf : D → ByteArray) (digestOf : ByteArray → Option D)

/-- **The receiver is the Bell's monitor** (`activity_program_safe` at the Bell): every `rings`
edit of a returning run of any method of the Bell, through `Lang.program`'s `run`, is a step of
the log row's machine over the old row the kernel found at its key. -/
theorem bell_monitored {rc : Lang.ReceiptCheck} {look : Kernel.Receive.Pinned D} {rv : Kernel.Receive.RowView D}
    {pkg : D} {state : Kernel.Slots} {method : Nat} {args : ByteArray} {r : Kernel.Receive.Req D}
    {budget : Nat} {s : Kernel.Slots} {calls : List (Kernel.Receive.Body D)}
    {rows : List (Kernel.RowSlot D × Kernel.RowAct)} {used : Nat} {p : Package}
    (hid : digestOf (bytesOf pkg) = some pkg) (hp : readPackage look pkg = .ok p) (hs : shapeOk p = true)
    (h : (Lang.program bytesOf digestOf rc).run look rv pkg state method args r budget = .ok (s, calls, rows, used)) :
    ∃ S, ∃ es : List (Edit D), runSetup bytesOf digestOf rc look rv pkg state method args r = .ok S ∧
      rows = es.map (fun x => (x.slot, x.act)) ∧
      ∀ x ∈ es, x.label = "rings" → ∃ o, guardOld digestOf rv r.self x = .ok o ∧
        WaitingStep S.lib resumer (reqData bytesOf r) S.state x.data o := by
  obtain ⟨hi, hh, -⟩ := shape_parts hs
  obtain ⟨fs, hb, hrel, hg, hf, hv, hnr, hw⟩ := rung_is_waiting hs
  exact activity_program_safe bytesOf digestOf hid hp hi hh hb hrel hg hf hnr hv hw h

end

/-- **The Bell's resumer is the resident**: what it admits is a request signed by the state's
`resident`. -/
theorem resumes_resident {lib : List Term} {req state : Data} (h : Resumes lib resumer req state) :
    ∃ a, req.field "agent" = some (.digest a) ∧ state.field "resident" = some (.digest a) := by
  obtain ⟨env, h3, h2, hb⟩ := h
  simp only [activityApply, List.foldl, resumer] at hb
  obtain ⟨b1, e1, w1, hf1, ha1, hb1⟩ := bigStep_app_ok hb
  obtain ⟨b0, e0, w0, hf0, ha0, hb0⟩ := bigStep_app_ok hf1
  cases hf0
  cases hb0
  have hw0 := bigStep_var_ok ha0
  rw [h3] at hw0; cases hw0
  have hw1 := bigStep_var_ok ha1
  rw [h2] at hw1; cases hw1
  obtain ⟨x, y, hx, hy, hp⟩ := bigStep_prim_ok hb1
  obtain ⟨ag, hag, rfl⟩ := bigStep_getVar (d := req) rfl hx
  obtain ⟨rs, hrs, rfl⟩ := bigStep_getVar (d := state) rfl hy
  obtain ⟨a, rfl, rfl⟩ := deq_true hp
  exact ⟨a, hag, hrs⟩

/-! ## The `answer` method, run -/

private theorem slot_e2 : slotLabels "e" 2 = ["e0", "e1"] := by decide

/-- `answer` resolves to its declared signature: argument `answerArg`, no calls, no reads, two
edits. -/
theorem answer_sig {D : Type} {p : Package} (hs : shapeOk p = true) {m : Nat} {sg : Sig}
    (h : resolveMethod (D := D) p m = .ok ("answer", sg)) : sg = ⟨answerArg, [], [], 2⟩ := by
  obtain ⟨mty, hf, hsig⟩ := resolveMethod_spec h
  obtain ⟨-, -, hS, hr, ha, -⟩ := shape_parts hs
  rw [ha] at hf
  cases hf
  rw [hS, hr] at hsig
  have : methodSig S rels answerTy = some ⟨answerArg, [], [], 2⟩ := by decide
  rw [this] at hsig
  exact (Option.some.inj hsig).symm

private theorem answerArg_cases {ad : Data} (h : Conforms ad answerArg) :
    ∃ nb x k y, ad = answerData nb x k y := by
  cases h with
  | record hr =>
    cases hr with
    | cons h1 hr => cases hr with
      | cons h2 hr => cases hr with
        | cons h3 hr => cases hr with
          | cons h4 hr =>
            cases hr; cases h1; cases h2; cases h3; cases h4
            exact ⟨_, _, _, _, rfl⟩

private theorem state_cases {sd : Data} (h : Conforms sd S) :
    ∃ b a, sd = .record [("open", .bool b), ("resident", .digest a)] := by
  cases h with
  | record hr =>
    cases hr with
    | cons h1 hr => cases hr with
      | cons h2 hr =>
        cases hr; cases h1; cases h2
        exact ⟨_, _, rfl⟩

/-- A bound `(f (bytes 1 2000))` evaluates to whether the field's size is inside it. -/
private theorem bound_eval {lib : List Term} {env : Env} {f : Label} {s : ByteArray}
    (h : BigStep lib env (.get (.var 1) f) (.ok (.bytes s))) :
    BigStep lib env (Surface.Bound.cond ⟨[f], true, 1, 2000⟩)
      (.ok (.bool (decide (1 ≤ s.size ∧ s.size ≤ 2000)))) := by
  have hle : ∀ n, BigStep lib env (.prim .lenLe (.get (.var 1) f) (.nat n)) (.ok (.bool (decide (s.size ≤ n)))) := by
    intro n
    have := BigStep.prim (p := .lenLe) h (.nat (n := n)) (by rw [primEval_lenLe]; simp)
    rwa [primEval_lenLe] at this
  simp only [Surface.Bound.cond, Surface.pathT, List.foldl, ↓reduceIte, Nat.one_ne_zero, Nat.sub_self]
  by_cases h0 : s.size ≤ 0
  · have hf : decide (1 ≤ s.size ∧ s.size ≤ 2000) = false := by simp; omega
    rw [hf]
    have h0' : decide (s.size ≤ 0) = true := by simp [h0]
    exact .iteT (h0' ▸ hle 0) .bool
  · have hf : decide (1 ≤ s.size ∧ s.size ≤ 2000) = decide (s.size ≤ 2000) := by
      by_cases h2 : s.size ≤ 2000 <;> simp [h2] <;> omega
    rw [hf]
    have h0' : decide (s.size ≤ 0) = false := by simp [h0]
    exact .iteF (h0' ▸ hle 0) (hle 2000)

/-- The edits row of `answer`'s success term. -/
private abbrev editsT : Term :=
  .record [
    ("e0", someCallT E (.inj E "rings" (.inj (relEditTy rings) "upsert" (.record [("key", ringKey),
      ("val", .record [
        ("answered", someCallT (activityResponses plans) (.inj (activityResponses plans) "ask" (.get (.var 1) "text"))),
        ("captured", .inj (activityCaptured plans) "ask" (.record [("text", .get (.var 1) "ringText")]))])])))),
    ("e1", someCallT E (.inj E "pending" (.inj (relEditTy pending) "retract" (.record [("key", ringKey)]))))]

private theorem editsT_means {lib : List Term} {req state rows : Val} {nb : Nat} {x k y : ByteArray} {W : Val}
    (hW : BigStep lib [req, (answerData nb x k y).toVal, state, rows] editsT (.ok W)) :
    Means lib (.record [("e0", optTy E), ("e1", optTy E)]) W (answerEdits nb x k y) := by
  let env : Env := [req, (answerData nb x k y).toVal, state, rows]
  have hg : ∀ (ℓ : Label) (d : Data), (answerData nb x k y).field ℓ = some d →
      BigStep lib env (.get (.var 1) ℓ) (.ok d.toVal) :=
    fun ℓ d hd => get_data (BigStep.var (i := 1) rfl) hd
  have hkey : Means lib (keyTy rings) (.record (suspend env [("agent", .get (.var 1) "ringer"),
      ("notBefore", .get (.var 1) "notBefore")])) (keyData nb k) :=
    .record .record (.cons (hg "ringer" (.digest k) rfl) .digest (.cons (hg "notBefore" (.nat nb) rfl) .nat .nil))
  cases hW
  refine .record .record (.cons (.inj (.inj (.inj .record))) ?_ (.cons (.inj (.inj (.inj .record))) ?_ .nil))
  · refine .inj rfl (.inj rfl (.inj rfl (.record .record (.cons .record hkey (.cons .record ?_ .nil)))))
    refine .record .record (.cons (.inj (.inj (hg "text" (.bytes y) rfl))) (.inj rfl (.inj rfl .bytes))
      (.cons (.inj .record) (.inj rfl (.record .record (.cons (hg "ringText" (.bytes x) rfl) .bytes .nil))) .nil))
  · exact .inj rfl (.inj rfl (.inj rfl (.record .record (.cons .record hkey .nil))))

private theorem answer_editsOf {D : Type} {self : D} {nb : Nat} {x k y : ByteArray} {es : List (Edit D)}
    (h : editsOf rels self (answerEdits nb x k y) = .ok es) :
    ∃ kb vb, keyBytes rings (keyData nb k) = some kb ∧ keyBytes pending (keyData nb k) = some kb ∧
      Wire.encodeData rings.val (answeredVal x y) = some vb ∧
      es.map (fun e => (e.slot, e.act)) =
        [(Kernel.RowSlot.row ⟨self, 1, kb⟩, Kernel.RowAct.upsert 0 vb), (Kernel.RowSlot.row ⟨self, 0, kb⟩, Kernel.RowAct.retract)] := by
  have hpk : keyBytes pending (keyData nb k) = keyBytes rings (keyData nb k) := rfl
  have i0 : relIndex [("pending", pending), ("rings", rings)] "pending" = some 0 := rfl
  have i1 : relIndex [("pending", pending), ("rings", rings)] "rings" = some 1 := rfl
  have ha : amtOf rings (answeredVal x y) = 0 := rfl
  have hr : pending.retract = true := rfl
  rw [hpk]
  cases hk : keyBytes rings (keyData nb k) <;> cases hv : Wire.encodeData rings.val (answeredVal x y) <;>
    simp [editsOf, editsOf.go, editOf, answerEdits, i0, i1, rels, Row.find?, hk, hv, hpk, hr, ha, bind,
      Except.bind, pure, Except.pure] at h
  subst h
  exact ⟨_, _, rfl, rfl, rfl, rfl⟩

private theorem noRef_answer : NoRef answer := by
  simp [answer, answerBody, answerBounds, Surface.boundCheck, Surface.Bound.cond, Surface.pathT, NoRef, NoRefRow,
    resultT, someCallT, ringKey]

section
variable {D : Type} (bytesOf : D → ByteArray) (digestOf : ByteArray → Option D)

/-- **The edits of the Bell's `answer`** (the deployed run, `Lang.program`'s `run`, of the method a
Bell labels `answer`): a run that returned decoded its argument as `answerData nb x k y`, with the
ring's text `x` and the answer `y` inside their bounds; the request was signed by the state's
resident; it makes no calls; and its row acts are exactly the upsert of `rings` (relation 1) at the
ring's key `(k, nb)` to `answeredVal x y` (`answered (some (ask y))`, captured `ask {text := x}`), and
the retract of `pending` (relation 0) at the same key. The answer written is the argument's `text`,
not the ring's. -/
theorem answer_run {rc : Lang.ReceiptCheck} {look : Kernel.Receive.Pinned D} {rv : Kernel.Receive.RowView D}
    {pkg : D} {state : Kernel.Slots} {m : Nat} {args : ByteArray} {r : Kernel.Receive.Req D}
    {budget : Nat} {s : Kernel.Slots} {calls : List (Kernel.Receive.Body D)}
    {rows : List (Kernel.RowSlot D × Kernel.RowAct)} {used : Nat} {p : Package} {sg : Sig}
    (hid : digestOf (bytesOf pkg) = some pkg) (hp : readPackage look pkg = .ok p) (hs : shapeOk p = true)
    (hres : resolveMethod (D := D) p m = .ok ("answer", sg))
    (h : (Lang.program bytesOf digestOf rc).run look rv pkg state m args r budget = .ok (s, calls, rows, used)) :
    ∃ nb x k y kb vb, Wire.decodeData answerArg args = .ok (answerData nb x k y) ∧
      (1 ≤ x.size ∧ x.size ≤ 2000) ∧ (1 ≤ y.size ∧ y.size ≤ 2000) ∧
      (∃ b, readState digestOf (recordRow S) state = .ok (.record [("open", .bool b), ("resident", .digest (bytesOf r.agent))])) ∧
      calls = [] ∧
      keyBytes rings (keyData nb k) = some kb ∧ keyBytes pending (keyData nb k) = some kb ∧
      Wire.encodeData rings.val (answeredVal x y) = some vb ∧
      rows = [(.row ⟨r.self, 1, kb⟩, .upsert 0 vb), (.row ⟨r.self, 0, kb⟩, .retract)] := by
  obtain ⟨hi, hh, hS, hR, -, fs, hb, hfa, -⟩ := shape_parts hs
  have hsg := answer_sig hs hres
  subst hsg
  change (runMeasuredLive bytesOf digestOf rc look rv pkg state m args r budget).map _ = _ at h
  rw [runMeasuredLive_leaf_closed hid hp hi hh] at h
  cases hm : runMeasured bytesOf digestOf rc look rv pkg state m args r budget with
  | error e => rw [hm] at h; cases h
  | ok q =>
  rw [hm] at h
  obtain ⟨s', calls', rows', t', n'⟩ := q
  simp only [Except.map, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl, rfl⟩ := h
  obtain ⟨S', v, used, c, e, ds, left, es, hS', hrun, hx, hc, hes, hrows⟩ := runMeasured_inv hm
  obtain ⟨L, g, p', ℓ, sg', sd, ad, wd, -, hl, hpg, hres', hsd, had, -, hwd, rfl⟩ := runSetup_spec hS'
  obtain ⟨hpg', f, hlib⟩ := load_top bytesOf digestOf (fuel := closureDepthMax - 1) hid hp hl
  rw [hpg'] at hpg
  cases hpg
  rw [hres] at hres'
  cases hres'
  simp only at hrun hx hes
  obtain ⟨nb, x, k, y, rfl⟩ := answerArg_cases (decodeData_conforms had)
  have hsdc := readState_conforms hsd
  rw [hS] at hsdc
  obtain ⟨bo, a, rfl⟩ := state_cases hsdc
  have hbig := run_bigStep hrun
  let env : Env := [(reqData bytesOf r).toVal, (answerData nb x k y).toVal,
    (Data.record [("open", .bool bo), ("resident", .digest a)]).toVal, wd.toVal]
  have fwd : ∀ {r' : Except Fault Val},
      BigStep L.lib env (Surface.boundCheck answerRes answerBounds answerBody) r' →
      BigStep L.lib env (apply4 g "answer") r' :=
    fun hb' => apply4_method hlib hb hfa noRef_answer hb'
  have c1 := bound_eval (lib := L.lib) (env := env) (f := "ringText") (s := x)
    (get_data (d := answerData nb x k y) (x := .bytes x) (BigStep.var (i := 1) rfl) rfl)
  have c2 := bound_eval (lib := L.lib) (env := env) (f := "text") (s := y)
    (get_data (d := answerData nb x k y) (x := .bytes y) (BigStep.var (i := 1) rfl) rfl)
  by_cases hx0 : ¬(1 ≤ x.size ∧ x.size ≤ 2000)
  · rw [decide_eq_false hx0] at c1
    cases bigStep_deterministic hbig (fwd (.iteF c1 .refuse))
  have hx1 := Decidable.not_not.mp hx0
  rw [decide_eq_true hx1] at c1
  by_cases hy0 : ¬(1 ≤ y.size ∧ y.size ≤ 2000)
  · rw [decide_eq_false hy0] at c2
    cases bigStep_deterministic hbig (fwd (.iteT c1 (.iteF c2 .refuse)))
  have hy1 := Decidable.not_not.mp hy0
  rw [decide_eq_true hy1] at c2
  have hag : BigStep L.lib env (.get (.var 0) "agent") (.ok (Data.digest (bytesOf r.agent)).toVal) :=
    get_data (BigStep.var (i := 0) rfl) rfl
  have hrs : BigStep L.lib env (.get (.var 2) "resident") (.ok (Data.digest a).toVal) :=
    get_data (BigStep.var (i := 2) rfl) rfl
  have hdq := BigStep.prim (p := .deq) hag hrs (by simp [Data.toVal, primEval])
  simp only [Data.toVal, primEval] at hdq
  by_cases hA : ¬(bytesOf r.agent = a)
  · rw [decide_eq_false hA] at hdq
    cases bigStep_deterministic hbig (fwd (.iteT c1 (.iteT c2 (.iteF hdq .refuse))))
  have hA' := Decidable.not_not.mp hA
  subst hA'
  rw [decide_eq_true rfl] at hdq
  have hok := fwd (.iteT c1 (.iteT c2 (.iteT hdq .record)))
  cases bigStep_deterministic hbig hok
  have hM := extract_means _ _ hx
  rw [hS, hR] at hM
  have hwE := BigStep.get (ℓ := "edits") hbig (.field (find_suspend_of (t := editsT) rfl) .record)
  obtain ⟨A, hA, hmA⟩ := means_get hbig hM rfl hwE
  simp [slot_e2, Row.find?] at hA
  subst hA
  have hED := editsT_means (lib := L.lib) (req := (reqData bytesOf r).toVal)
    (state := (Data.record [("open", .bool bo), ("resident", .digest (bytesOf r.agent))]).toVal)
    (rows := wd.toVal) (nb := nb) (x := x) (k := k) (y := y) .record
  have he := means_deterministic hmA hED
  subst he
  have hwC := BigStep.get (ℓ := "calls") hbig (.field (find_suspend_of (t := .record []) rfl) .record)
  obtain ⟨A', hA', hmC⟩ := means_get hbig hM rfl hwC
  simp [Row.find?] at hA'
  subst hA'
  have hc0 : Means L.lib (callsTy []) (.record []) (.record []) := .record .record .nil
  have hce := means_deterministic hmC hc0
  subst hce
  simp [callsOf, callsOf.go] at hc
  subst hc
  rw [hR] at hes
  obtain ⟨kb, vb, hkb, hpb, hvb, hmap⟩ := answer_editsOf hes
  refine ⟨nb, x, k, y, kb, vb, had, hx1, hy1, ⟨bo, ?_⟩, rfl, hkb, hpb, hvb, hrows.trans hmap⟩
  rw [← hS]; exact hsd

end

end Nanodregg.Lang.Bell
