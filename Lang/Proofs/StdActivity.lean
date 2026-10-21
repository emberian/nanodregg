/- Meaning of the generated activity's continuation retirement guard. -/
import Lang.StdActivity
import Lang.Proofs.Std

namespace Nanodregg.Lang.Std


private theorem app3_vars_inv
    {lib : List Term} {env : Env} {A B C : Ty} {body : Term} {i q s v : Val}
    (h : BigStep lib (i :: q :: s :: env)
      (activityApply (.lam A (.lam B (.lam C body))) [.var 2, .var 1, .var 0]) (.ok v)) :
    BigStep lib (i :: q :: s :: i :: q :: s :: env) body (.ok v) := by
  obtain ⟨b3, e3, z, hf3, hz, hb3⟩ := bigStep_app_ok h
  obtain ⟨b2, e2, y, hf2, hy, hb2⟩ := bigStep_app_ok hf3
  obtain ⟨b1, e1, x, hf1, hx, hb1⟩ := bigStep_app_ok hf2
  cases hf1
  cases hb1
  cases hb2
  have hx' : x = s := by simpa using (bigStep_var_ok hx).symm
  have hy' : y = q := by simpa using (bigStep_var_ok hy).symm
  have hz' : z = i := by simpa using (bigStep_var_ok hz).symm
  subst x; subst y; subst z
  exact hb3

private theorem case_known
    {lib : List Term} {env : Env} {t : Term} {arms : List (Label × Term)}
    {l : Label} {w v : Val} {body : Term}
    (ht : BigStep lib env t (.ok (.inj l w)))
    (hf : Row.find? l arms = some body)
    (h : BigStep lib env (.case t arms) (.ok v)) :
    BigStep lib (w :: env) body (.ok v) := by
  obtain ⟨l', w', b, ht', hf', hb⟩ := bigStep_case_ok h
  have he := bigStep_deterministic ht ht'
  cases he
  rw [hf] at hf'
  cases hf'
  exact hb

private def retirementInput (key old : Data) : Data :=
  .record [("edit", .inj "retract" (.record [("key", key)])), ("old", old)]

/-- Retirement of an answered continuation succeeds for every requester and
state. The old row comes from the kernel at the edited key; authorisation to
answer is checked on the separate upsert transition. -/
theorem activity_retire_some_meaning
    (S : Ty) (plans : List ActivityPlan) (d : RelDecl) (resumer : Term)
    (key captured answer : Data) (lib : List Term) (env : Env) (state req : Val) :
    BigStep lib
      ((retirementInput key (.inj "some" (.record [
        ("answered", .inj "some" answer), ("captured", captured)]))).toVal :: req :: state :: env)
      (activityApply (activityWaiting S plans d resumer) [.var 2, .var 1, .var 0])
      (.ok (.inj "ok" (.record []))) := by
  unfold activityApply activityWaiting
  simp only [List.foldl]
  apply BigStep.app (BigStep.app (BigStep.app .lam (.var rfl) .lam) (.var rfl) .lam) (.var rfl)
  refine BigStep.case (ℓ := "retract") (w := (Data.record [("key", key)]).toVal) ?_ rfl ?_
  · exact .get (.var rfl) (.field rfl (.var rfl))
  refine BigStep.case (ℓ := "some") (w := (Data.record [("answered", .inj "some" answer), ("captured", captured)]).toVal) ?_ rfl ?_
  · exact .get (.var rfl) (.field rfl (.var rfl))
  refine BigStep.case (ℓ := "some") (w := answer.toVal) ?_ rfl ?_
  · exact .get (.var rfl) (.field rfl (.var rfl))
  exact .inj .record

/-- An unanswered continuation cannot be retired: the guard returns the named
refusal for arbitrary state, request, capture and key. -/
theorem activity_retire_none_meaning
    (S : Ty) (plans : List ActivityPlan) (d : RelDecl) (resumer : Term)
    (key captured : Data) (lib : List Term) (env : Env) (state req : Val) :
    BigStep lib
      ((retirementInput key (.inj "some" (.record [
        ("answered", .inj "none" (.record [])), ("captured", captured)]))).toVal :: req :: state :: env)
      (activityApply (activityWaiting S plans d resumer) [.var 2, .var 1, .var 0])
      (.ok (.inj "refused" (.bytes "unanswered".toUTF8))) := by
  unfold activityApply activityWaiting
  simp only [List.foldl]
  apply BigStep.app (BigStep.app (BigStep.app .lam (.var rfl) .lam) (.var rfl) .lam) (.var rfl)
  refine BigStep.case (ℓ := "retract") (w := (Data.record [("key", key)]).toVal) ?_ rfl ?_
  · exact .get (.var rfl) (.field rfl (.var rfl))
  refine BigStep.case (ℓ := "some") (w := (Data.record [("answered", .inj "none" (.record [])), ("captured", captured)]).toVal) ?_ rfl ?_
  · exact .get (.var rfl) (.field rfl (.var rfl))
  refine BigStep.case (ℓ := "none") (w := .record []) ?_ rfl ?_
  · exact .get (.var rfl) (.field rfl (.var rfl))
  exact .inj .bytes


/-- Retirement admits exactly answered rows, independently of who requests
cleanup. This is an iff about the generated guard's actual semantics. -/
theorem waiting_retract_iff
    (S : Ty) (plans : List ActivityPlan) (d : RelDecl) (resumer : Term)
    (key captured : Data) (answer : Option Data) (lib : List Term)
    (env : Env) (state req : Val) :
    (∃ w, BigStep lib
      ((retirementInput key (.inj "some" (.record [
        ("answered", match answer with | none => .inj "none" (.record []) | some a => .inj "some" a),
        ("captured", captured)]))).toVal :: req :: state :: env)
      (activityApply (activityWaiting S plans d resumer) [.var 2, .var 1, .var 0])
      (.ok (.inj "ok" w))) ↔ answer.isSome = true := by
  cases answer with
  | none =>
    constructor
    · rintro ⟨w, h⟩
      have he := bigStep_deterministic h
        (activity_retire_none_meaning S plans d resumer key captured lib env state req)
      simp at he
    · intro h; cases h
  | some a =>
    exact ⟨fun _ => rfl, fun _ =>
      ⟨.record [], activity_retire_some_meaning S plans d resumer key captured a lib env state req⟩⟩


private def upsertInput (key old value : Data) : Data :=
  .record [("edit", .inj "upsert" (.record [("key", key), ("val", value)])),
    ("old", .inj "some" old)]

/-- Once answered, the generated guard rejects every further upsert, even from
an authorised resumer and even if that upsert changes the capture or answer. -/
theorem waiting_no_replay
    (S : Ty) (plans : List ActivityPlan) (d : RelDecl) (resumer : Term)
    (key captured answer value : Data) (lib : List Term)
    (env : Env) (state req : Val) :
    ¬ ∃ w, BigStep lib
      ((upsertInput key (.record [("answered", .inj "some" answer),
        ("captured", captured)]) value).toVal :: req :: state :: env)
      (activityApply (activityWaiting S plans d resumer) [.var 2, .var 1, .var 0])
      (.ok (.inj "ok" w)) := by
  rintro ⟨w, h⟩
  have hb := app3_vars_inv h
  let old := Data.record [("answered", .inj "some" answer), ("captured", captured)]
  let payload := Data.record [("key", key), ("val", value)]
  let input := upsertInput key old value
  let e := input.toVal :: req :: state :: input.toVal :: req :: state :: env
  have hedit : BigStep lib e (.get (.var 0) "edit")
      (.ok (.inj "upsert" (Data.record [("key", key), ("val", value)]).toVal)) :=
    .get (.var rfl) (.field rfl (.var rfl))
  have hu := case_known hedit rfl hb
  have hr := (guard_ok hu).2
  have hold : BigStep lib (payload.toVal :: e) (.get (.var 1) "old")
      (.ok (.inj "some" (Data.record [("answered", .inj "some" answer),
        ("captured", captured)]).toVal)) :=
    .get (.var rfl) (.field rfl (.var rfl))
  have ho := case_known hold rfl hr
  have hans : BigStep lib (old.toVal :: payload.toVal :: e) (.get (.var 0) "answered") (.ok (.inj "some" answer.toVal)) :=
    .get (.var rfl) (.field rfl (.var rfl))
  exact refusedT_not_ok (case_known hans rfl ho)


private def insertInput (agent : ByteArray) (n : Nat) (captured : Data)
    (answer : Option Data) (old : Data) : Data :=
  .record [("edit", .inj "insert" (.record [
    ("key", .record [("agent", .digest agent), ("notBefore", .nat n)]),
    ("val", .record [
      ("answered", match answer with | none => .inj "none" (.record []) | some a => .inj "some" a),
      ("captured", captured)])])), ("old", old)]

/-- Insertion is signed by the key owner and starts unanswered. The old-row
payload is irrelevant: the kernel separately refuses an already-taken key. -/
theorem waiting_insert_meaning
    (S : Ty) (plans : List ActivityPlan) (d : RelDecl) (resumer : Term)
    (agent signer : ByteArray) (n : Nat) (captured old : Data) (answer : Option Data)
    (lib : List Term) (env : Env) (state : Val) (reqTail : List (Label × Data)) :
    BigStep lib
      ((insertInput agent n captured answer old).toVal ::
        (Data.record (("agent", .digest signer) :: reqTail)).toVal :: state :: env)
      (activityApply (activityWaiting S plans d resumer) [.var 2, .var 1, .var 0])
      (.ok (if agent = signer then
        match answer with
        | none => .inj "ok" (.record [])
        | some _ => .inj "refused" (.bytes "answered".toUTF8)
      else .inj "refused" (.bytes "notYours".toUTF8))) := by
  unfold activityApply activityWaiting
  simp only [List.foldl]
  apply BigStep.app (BigStep.app (BigStep.app .lam (.var rfl) .lam) (.var rfl) .lam) (.var rfl)
  refine BigStep.case (ℓ := "insert") (w := (Data.record [
    ("key", .record [("agent", .digest agent), ("notBefore", .nat n)]),
    ("val", .record [
      ("answered", match answer with | none => .inj "none" (.record []) | some a => .inj "some" a),
      ("captured", captured)])]).toVal) ?_ rfl ?_
  · exact .get (.var rfl) (.field rfl (.var rfl))
  let payload := Data.record [
    ("key", .record [("agent", .digest agent), ("notBefore", .nat n)]),
    ("val", .record [
      ("answered", match answer with | none => .inj "none" (.record []) | some a => .inj "some" a),
      ("captured", captured)])]
  let input := insertInput agent n captured answer old
  let req := Data.record (("agent", .digest signer) :: reqTail)
  have hc : BigStep lib (payload.toVal :: input.toVal :: req.toVal :: state ::
      input.toVal :: req.toVal :: state :: env) (.prim .deq
      (.get (.get (.var 0) "key") "agent") (.get (.var 2) "agent"))
      (.ok (.bool (decide (agent = signer)))) :=
    BigStep.prim (p := .deq) (x := .digest agent) (y := .digest signer)
      (.get (.get (.var rfl) (.field rfl (.var rfl))) (.field rfl (.var rfl)))
      (.get (.var rfl) (.field rfl (.var rfl))) (by simp [primEval])
  cases he : (decide (agent = signer))
  · rw [he] at hc
    rw [if_neg (of_decide_eq_false he)]
    exact .iteF hc (.inj .bytes)
  · rw [he] at hc
    rw [if_pos (of_decide_eq_true he)]
    apply BigStep.iteT hc
    cases answer with
    | none =>
      exact .case (.get (.get (.var rfl) (.field rfl (.var rfl))) (.field rfl (.var rfl))) rfl (.inj .record)
    | some a =>
      exact .case (.get (.get (.var rfl) (.field rfl (.var rfl))) (.field rfl (.var rfl))) rfl (.inj .bytes)

/-- Both directions over the actual generated guard, including its rejecting
cases; the right side mentions data, not the guard's own evaluation. -/
theorem waiting_insert_iff
    (S : Ty) (plans : List ActivityPlan) (d : RelDecl) (resumer : Term)
    (agent signer : ByteArray) (n : Nat) (captured old : Data) (answer : Option Data)
    (lib : List Term) (env : Env) (state : Val) (reqTail : List (Label × Data)) :
    (∃ w, BigStep lib
      ((insertInput agent n captured answer old).toVal ::
        (Data.record (("agent", .digest signer) :: reqTail)).toVal :: state :: env)
      (activityApply (activityWaiting S plans d resumer) [.var 2, .var 1, .var 0])
      (.ok (.inj "ok" w))) ↔ agent = signer ∧ answer = none := by
  have h := waiting_insert_meaning S plans d resumer agent signer n captured old answer lib env state reqTail
  constructor
  · rintro ⟨w, hw⟩
    have he := bigStep_deterministic hw h
    split at he
    · rename_i heq
      have hag : agent = signer := heq
      cases answer <;> simp_all
    · simp at he
  · rintro ⟨rfl, rfl⟩
    exact ⟨.record [], by simpa using h⟩


/-- Any successful update of an unanswered continuation preserves the complete
captured value. This covers arbitrary data types, plans, responses and resumers;
it is the structural equality theorem applied to the actual guard operands. -/
theorem waiting_upsert_preserves_capture
    (S : Ty) (plans : List ActivityPlan) (d : RelDecl) (resumer : Term)
    (key before after answer : Data) (lib : List Term)
    (env : Env) (state req : Val)
    (hw : (activityCaptured plans).wf = true)
    (hb : Conforms before (activityCaptured plans))
    (ha : Conforms after (activityCaptured plans))
    (h : ∃ w, BigStep lib
      ((upsertInput key (.record [("answered", .inj "none" (.record [])),
        ("captured", before)]) (.record [("answered", answer), ("captured", after)])).toVal ::
        req :: state :: env)
      (activityApply (activityWaiting S plans d resumer) [.var 2, .var 1, .var 0])
      (.ok (.inj "ok" w))) : after = before := by
  obtain ⟨w, h⟩ := h
  have hbody := app3_vars_inv h
  let old := Data.record [("answered", .inj "none" (.record [])), ("captured", before)]
  let value := Data.record [("answered", answer), ("captured", after)]
  let payload := Data.record [("key", key), ("val", value)]
  let input := upsertInput key old value
  let e := input.toVal :: req :: state :: input.toVal :: req :: state :: env
  have hedit : BigStep lib e (.get (.var 0) "edit") (.ok (.inj "upsert" payload.toVal)) :=
    .get (.var rfl) (.field rfl (.var rfl))
  have hu := case_known hedit rfl hbody
  have hr := (guard_ok hu).2
  have hold : BigStep lib (payload.toVal :: e) (.get (.var 1) "old")
      (.ok (.inj "some" old.toVal)) :=
    .get (.var rfl) (.field rfl (.var rfl))
  have ho := case_known hold rfl hr
  have hans : BigStep lib (old.toVal :: payload.toVal :: e) (.get (.var 0) "answered")
      (.ok (.inj "none" (.record []))) :=
    .get (.var rfl) (.field rfl (.var rfl))
  have hc := (guard_ok (case_known hans rfl ho)).1
  have hx : BigStep lib (.record [] :: old.toVal :: payload.toVal :: e)
      (.get (.get (.var 2) "val") "captured") (.ok after.toVal) :=
    .get (.get (.var rfl) (.field rfl (.var rfl))) (.field rfl (.var rfl))
  have hy : BigStep lib (.record [] :: old.toVal :: payload.toVal :: e)
      (.get (.var 1) "captured") (.ok before.toVal) :=
    .get (.var rfl) (.field rfl (.var rfl))
  exact (eqData_true hw hx hy hc ha hb).mp rfl


private theorem find_map_unit {names : List (Label × Unit)} {l : Label}
    (hf : Row.find? l names = some ()) (f : Label → Term) :
    Row.find? l (names.map fun p => (p.1, f p.1)) = some (f l) := by
  induction names with
  | nil => simp [Row.find?] at hf
  | cons p ps ih =>
    rcases p with ⟨k, _⟩
    simp only [Row.find?, List.map_cons] at hf ⊢
    split at hf
    · rename_i h; subst h; simp
    · rename_i h; simp only [h, ↓reduceIte]; exact ih hf

/-- Plan identity depends on the two tags, for arbitrary payloads and operand
terms. Both tags must be declared; no equality of payload types is assumed. -/
theorem activitySamePlan_meaning
    (plans : List ActivityPlan) (lib : List Term) (env : Env)
    (x y : Term) (l k : Label) (v w : Val)
    (hl : Row.find? l (Row.sort (plans.map fun p => (p.name, ()))) = some ())
    (hk : Row.find? k (Row.sort (plans.map fun p => (p.name, ()))) = some ())
    (hx : BigStep lib env x (.ok (.inj l v)))
    (hy : BigStep lib env y (.ok (.inj k w))) :
    BigStep lib env (activitySamePlan plans x y) (.ok (.bool (l == k))) := by
  unfold activitySamePlan
  apply BigStep.app (BigStep.app .lam hx .lam) hy
  refine BigStep.case (ℓ := l) (w := v)
    (body := .case (.var 1) ((Row.sort (plans.map fun p => (p.name, ()))).map
      fun p => (p.1, .bool (l == p.1)))) (.var rfl) ?_ ?_
  · exact find_map_unit hl (fun a => .case (.var 1) ((Row.sort (plans.map fun p => (p.name, ()))).map fun q => (q.1, .bool (a == q.1))))
  refine BigStep.case (ℓ := k) (w := w) (.var rfl) ?_ .bool
  exact find_map_unit hk (fun b => .bool (l == b))

private def answerInput (key before after answer : Data) : Data :=
  upsertInput key (.record [("answered", .inj "none" (.record [])), ("captured", before)])
    (.record [("answered", .inj "some" answer), ("captured", after)])

private def answerEnv (key before after answer : Data) (req state : Val) (env : Env) : Env :=
  let input := answerInput key before after answer
  input.toVal :: req :: state :: input.toVal :: req :: state :: env

private def answerPayload (key after answer : Data) : Data :=
  .record [("key", key), ("val", .record [
    ("answered", .inj "some" answer), ("captured", after)])]

/-- Exact acceptance of an answer to an existing unanswered continuation.
The resumer clause's meaning is supplied as a boolean; all remaining conditions
are equalities on the row's actual data and the declared plan tags. -/
theorem waiting_upsert_iff
    (S : Ty) (plans : List ActivityPlan) (d : RelDecl) (resumer : Term)
    (key before : Data) (l k : Label) (capture response : Data)
    (lib : List Term) (env : Env) (state req : Val) (authorized : Bool)
    (hw : (activityCaptured plans).wf = true)
    (hb : Conforms before (activityCaptured plans))
    (ha : Conforms (.inj l capture) (activityCaptured plans))
    (hl : Row.find? l (Row.sort (plans.map fun p => (p.name, ()))) = some ())
    (hk : Row.find? k (Row.sort (plans.map fun p => (p.name, ()))) = some ())
    (hres : BigStep lib
      ((answerPayload key (.inj l capture) (.inj k response)).toVal ::
        answerEnv key before (.inj l capture) (.inj k response) req state env)
      (activityApply resumer [.var 3, .var 2]) (.ok (.bool authorized))) :
    (∃ w, BigStep lib
      ((answerInput key before (.inj l capture) (.inj k response)).toVal :: req :: state :: env)
      (activityApply (activityWaiting S plans d resumer) [.var 2, .var 1, .var 0])
      (.ok (.inj "ok" w))) ↔
      authorized = true ∧ .inj l capture = before ∧ l = k := by
  let after := Data.inj l capture
  let answer := Data.inj k response
  let old := Data.record [("answered", .inj "none" (.record [])), ("captured", before)]
  let payload := answerPayload key after answer
  let e := answerEnv key before after answer req state env
  let ec := Val.record [] :: old.toVal :: payload.toVal :: e
  obtain ⟨same, hs, hi⟩ := eqDataBody_meaning (lib := lib) (env := ec)
    (activityCaptured plans) hw ha hb
  have hx : BigStep lib ec (.get (.get (.var 2) "val") "captured") (.ok after.toVal) :=
    .get (.get (.var rfl) (.field rfl (.var rfl))) (.field rfl (.var rfl))
  have hy : BigStep lib ec (.get (.var 1) "captured") (.ok before.toVal) :=
    .get (.var rfl) (.field rfl (.var rfl))
  have hsame : BigStep lib ec
      (eqData (activityCaptured plans) (.get (.get (.var 2) "val") "captured")
        (.get (.var 1) "captured")) (.ok (.bool same)) :=
    .app (.app .lam hx .lam) hy hs
  have htag : BigStep lib (answer.toVal :: ec)
      (activitySamePlan plans (.get (.get (.var 3) "val") "captured") (.var 0))
      (.ok (.bool (l == k))) :=
    activitySamePlan_meaning plans lib _ _ _ l k capture.toVal response.toVal hl hk
      (.get (.get (.var rfl) (.field rfl (.var rfl))) (.field rfl (.var rfl))) (.var rfl)
  let result : Val := if authorized then
      if same then
        if l == k then .inj "ok" (.record []) else .inj "refused" (.bytes "plan".toUTF8)
      else .inj "refused" (.bytes "captured".toUTF8)
    else .inj "refused" (.bytes "notResumer".toUTF8)
  have hr : BigStep lib
      ((answerInput key before after answer).toVal :: req :: state :: env)
      (activityApply (activityWaiting S plans d resumer) [.var 2, .var 1, .var 0])
      (.ok result) := by
    unfold activityApply activityWaiting
    simp only [List.foldl]
    apply BigStep.app (BigStep.app (BigStep.app .lam (.var rfl) .lam) (.var rfl) .lam) (.var rfl)
    refine BigStep.case (ℓ := "upsert") (w := payload.toVal) ?_ rfl ?_
    · exact .get (.var rfl) (.field rfl (.var rfl))
    cases authorized with
    | false => exact .iteF hres (.inj .bytes)
    | true =>
      apply BigStep.iteT hres
      refine BigStep.case (ℓ := "some") (w := old.toVal) ?_ rfl ?_
      · exact .get (.var rfl) (.field rfl (.var rfl))
      refine BigStep.case (ℓ := "none") (w := .record []) ?_ rfl ?_
      · exact .get (.var rfl) (.field rfl (.var rfl))
      cases same with
      | false => exact .iteF hsame (.inj .bytes)
      | true =>
        apply BigStep.iteT hsame
        refine BigStep.case (ℓ := "some") (w := answer.toVal) ?_ rfl ?_
        · exact .get (.get (.var rfl) (.field rfl (.var rfl))) (.field rfl (.var rfl))
        cases ht : (l == k)
        · simp only [result, ht, ↓reduceIte]
          exact .iteF (by simpa only [ht] using htag) (.inj .bytes)
        · simp only [result, ht, ↓reduceIte]
          exact .iteT (by simpa only [ht] using htag) (.inj .record)
  constructor
  · rintro ⟨w, h⟩
    have he := bigStep_deterministic h hr
    cases authorized <;> cases same <;> by_cases ht : l = k <;>
      simp_all [result]
  · rintro ⟨rfl, hc, rfl⟩
    have hs : same = true := hi.mpr hc
    exact ⟨.record [], by simpa [result, hs] using hr⟩

end Nanodregg.Lang.Std
