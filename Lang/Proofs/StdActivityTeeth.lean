/- Executable activity instances: emitted package, continuation guards, and response-dependent state. -/
import Lang.StdActivity

namespace Nanodregg.Lang.Std

private def actS : Ty := .record [("resident", .digest), ("total", .nat)]
private def actR : Ty := .sum [("keep", .record []), ("set", .nat)]
private def actPlan : ActivityPlan := {
  name := "step", captured := .nat, response := actR,
  precondition := .lam actS (.lam .nat (.lam reqTy (.bool true))),
  start := .lam actS (.lam .nat (.lam reqTy (.var 2))),
  resume := .lam actS (.lam .nat (.lam actR (.lam reqTy
    (.case (.var 1) [("keep", .var 4),
      ("set", .extend (.var 4) [("total", .prim .add (.var 3) (.var 0))])])))) }

private def actResumer : Term := .lam actS (.lam reqTy
  (.prim .deq (.get (.var 0) "agent") (.get (.var 1) "resident")))

private def actBuild := activity actS "pending" "waits" 64 1024 actResumer [actPlan, { actPlan with name := "other" }]
private def actPkg : Package := match actBuild with | .ok p => p | .error _ => default

private def actBuildName : String := match actBuild with
  | .ok _ => "ok"
  | .error (.package why) => why.text
  | .error .noPlans => "noPlans"
  | .error .tooManyPlans => "tooManyPlans"
  | .error .duplicatePlan => "duplicatePlan"
  | .error .sameRelation => "sameRelation"
  | .error .zeroPatience => "zeroPatience"


theorem activity_fixture_generated : actBuildName = "ok" := by decide +kernel

/-- The fixture meets `activity_monitor_safe`'s package premises (`Lang.Proofs.StdActivityMonitor`):
its `waits` log is guarded by the field the relation names, that field is the generated waiting
guard over the log's own declaration, the log's value is `activityLogVal`, and the capture type is
well formed. -/
theorem activity_fixture_monitored :
    (match actPkg.body, Row.find? "waits" actPkg.rels with
      | .record fs, some d =>
        d.guard == some "waits_waiting" &&
        Row.find? "waits_waiting" fs ==
          some (activityWaiting actS [actPlan, { actPlan with name := "other" }] d actResumer) &&
        d.val == activityLogVal [actPlan, { actPlan with name := "other" }] &&
        (activityCaptured [actPlan, { actPlan with name := "other" }]).wf
      | _, _ => false) = true := by decide +kernel

private def actB (s : String) : ByteArray := s.toUTF8
private def actState : Data := .record [("resident", .digest (actB "r")), ("total", .nat 5)]
private def actReq (agent : String) : Data := .record [
  ("agent", .digest (actB agent)), ("notBefore", .nat 1),
  ("occasion", .inj "invoke" (.nat 0)), ("principal", .digest (actB agent)),
  ("self", .digest (actB "self")), ("validUntil", .nat 2)]
private def actKey : Data := .record [("agent", .digest (actB "a")), ("notBefore", .nat 1)]
private def actVal (n : Nat) (answer : Data) : Data := .record [
  ("answered", answer), ("captured", .inj "step" (.nat n))]
private def actNone : Data := .inj "none" (.record [])
private def actSome (d : Data) : Data := .inj "some" d
private def actAnswer : Data := actSome (.inj "step" (.inj "set" (.nat 7)))
private def actInput (op : Label) (old : Data) (new : Data) : Data :=
  .record [("edit", .inj op (.record (if op = "retract" then [("key", actKey)] else [("key", actKey), ("val", new)]))), ("old", old)]

private def actField (name : Label) : Term :=
  match actPkg.body with
  | .record fs => (Row.find? name fs).getD (.nat 0)
  | _ => .nat 0

private def actGuardField (field agent : String) (input : Data) : Option String :=
  match run [] Bounds.stackMax 3000 0 (State.init
    (activityApply (actField field) [.var 2, .var 1, .var 0])
    [input.toVal, (actReq agent).toVal, actState.toVal]) with
  | .value (.inj "ok" _) _ => some "ok"
  | .value (.inj "refused" (.bytes b)) _ => some (String.fromUTF8! b)
  | _ => none

private def actGuard := actGuardField "waits_waiting"

theorem activity_start_unanswered :
    actGuard "a" (actInput "insert" actNone (actVal 3 actNone)) = some "ok" := by decide +kernel

theorem activity_answer_once :
    actGuard "r" (actInput "upsert" (actSome (actVal 3 actNone)) (actVal 3 actAnswer)) = some "ok" := by decide +kernel

theorem activity_capture_immutable :
    actGuard "r" (actInput "upsert" (actSome (actVal 3 actNone)) (actVal 4 actAnswer)) = some "captured" := by decide +kernel

theorem activity_answer_no_replay :
    actGuard "r" (actInput "upsert" (actSome (actVal 3 actAnswer)) (actVal 3 actAnswer)) = some "answered" := by decide +kernel

theorem activity_answer_authorized :
    actGuard "a" (actInput "upsert" (actSome (actVal 3 actNone)) (actVal 3 actAnswer)) = some "notResumer" := by decide +kernel

theorem activity_response_matches_plan :
    actGuard "r" (actInput "upsert" (actSome (actVal 3 actNone))
      (actVal 3 (actSome (.inj "other" (.inj "set" (.nat 7)))))) = some "plan" := by decide +kernel

theorem activity_retire_needs_answer :
    actGuard "a" (actInput "retract" (actSome (actVal 3 actNone)) (actVal 3 actNone)) =
      some "unanswered" := by decide +kernel

theorem activity_retire_after_answer :
    actGuard "a" (actInput "retract" (actSome (actVal 3 actAnswer)) (actVal 3 actNone)) =
      some "ok" := by decide +kernel

private def actRows : Data := .record [("waits", .record [("p0", actSome
  (.record [("key", actKey), ("val", actSome (actVal 3 actNone))]))])]
private def actArgs (response : Data) : Data := .record [
  ("agent", .digest (actB "a")), ("notBefore", .nat 1), ("response", response)]

private def actResumeTotal (response : Data) : Option Nat :=
  let t := activityApply (actField "resume_step") [.var 3, .var 2, .var 1, .var 0]
  let env := [(actReq "r").toVal, (actArgs response).toVal, actState.toVal, actRows.toVal]
  let m : Machine := ⟨[]⟩
  match m.force 3000 t env with
  | .error _ => none
  | .ok (v, _) =>
    match m.extract (resultTy actS [] (editTy actPkg.rels) 2) 3000 v with
    | .error _ => none
    | .ok (d, _) =>
      match d.field "state" >>= (·.field "total") with
      | some (.nat n) => some n
      | _ => none

theorem activity_resume_uses_response :
    actResumeTotal (.inj "set" (.nat 7)) = some 10 := by decide +kernel

theorem activity_resume_other_response :
    actResumeTotal (.inj "keep" (.record [])) = some 5 := by decide +kernel


theorem activity_start_signed :
    actGuard "r" (actInput "insert" actNone (actVal 3 actNone)) = some "notYours" := by decide +kernel

theorem activity_start_not_answered :
    actGuard "a" (actInput "insert" actNone (actVal 3 actAnswer)) = some "answered" := by decide +kernel

theorem activity_answer_started :
    actGuard "r" (actInput "upsert" actNone (actVal 3 actAnswer)) = some "unstarted" := by decide +kernel

theorem activity_answer_present :
    actGuard "r" (actInput "upsert" (actSome (actVal 3 actNone)) (actVal 3 actNone)) = some "unanswered" := by decide +kernel

theorem activity_retire_started :
    actGuard "a" (actInput "retract" actNone (actVal 3 actNone)) = some "unstarted" := by decide +kernel

theorem activity_cursor_insert_signed :
    actGuardField "pending_queued" "r" (actInput "insert" actNone (actVal 3 actNone)) = some "notYours" := by decide +kernel

theorem activity_cursor_insert_own :
    actGuardField "pending_queued" "a" (actInput "insert" actNone (actVal 3 actNone)) = some "ok" := by decide +kernel

theorem activity_cursor_retract_authorized :
    actGuardField "pending_queued" "a" (actInput "retract" actNone (actVal 3 actNone)) = some "notResumer" := by decide +kernel

theorem activity_cursor_retract_resumer :
    actGuardField "pending_queued" "r" (actInput "retract" actNone (actVal 3 actNone)) = some "ok" := by decide +kernel

theorem activity_cursor_no_upsert :
    actGuardField "pending_queued" "r" (actInput "upsert" actNone (actVal 3 actNone)) = some "final" := by decide +kernel


private def actResumeVerdict (who : String) (rows : Data) : String :=
  let t := activityApply (actField "resume_step") [.var 3, .var 2, .var 1, .var 0]
  let m : Machine := ⟨[]⟩
  match m.force 3000 t
      [(actReq who).toVal, (actArgs (.inj "set" (.nat 7))).toVal, actState.toVal, rows.toVal] with
  | .error (.refused why) => String.fromUTF8! why
  | .error _ => "fault"
  | .ok _ => "ok"

private def actRowsAt (key val : Data) : Data :=
  .record [("waits", .record [("p0", actSome
    (.record [("key", key), ("val", val)]))])]

theorem activity_resume_requires_resumer :
    actResumeVerdict "a" actRows = "notResumer" := by decide +kernel

theorem activity_resume_requires_point :
    actResumeVerdict "r" (.record [("waits", .record [("p0", actNone)])]) = "unknown" := by decide +kernel

theorem activity_resume_requires_row :
    actResumeVerdict "r" (actRowsAt actKey actNone) = "unknown" := by decide +kernel

theorem activity_resume_requires_matching_key :
    actResumeVerdict "r" (actRowsAt
      (.record [("agent", .digest (actB "a")), ("notBefore", .nat 2)])
      (actSome (actVal 3 actNone))) = "key" := by decide +kernel

theorem activity_resume_requires_matching_plan :
    actResumeVerdict "r" (actRowsAt actKey (actSome (.record [
      ("answered", actNone), ("captured", .inj "other" (.nat 3))]))) = "wrongPlan" := by decide +kernel


/-! ## The deadline arm (LANG-76): the same fixture with `patience 10` -/

private def lateBuild := activity actS "pending" "waits" 64 1024 actResumer [actPlan, { actPlan with name := "other" }] (some 10)
private def latePkg : Package := match lateBuild with | .ok p => p | .error _ => default

theorem activity_late_fixture_generated :
    (match lateBuild with | .ok p => p.methods == ["resume_other", "resume_step", "retire", "start_other", "start_step"] | .error _ => false) = true := by
  decide +kernel

/-- A declared patience of 0 (anyone may abandon at once) is refused by name. -/
theorem activity_zero_patience_refused :
    (match activity actS "pending" "waits" 64 1024 actResumer [actPlan] (some 0) with
      | .error .zeroPatience => true | _ => false) = true := by decide +kernel

/-- The patience fixture meets `activity_monitor_safe`'s premises at `some 10`. -/
theorem activity_late_fixture_monitored :
    (match latePkg.body, Row.find? "waits" latePkg.rels with
      | .record fs, some d =>
        Row.find? "waits_waiting" fs ==
          some (activityWaiting actS [actPlan, { actPlan with name := "other" }] d actResumer {} (some 10)) &&
        d.val == activityLogVal [actPlan, { actPlan with name := "other" }]
      | _, _ => false) = true := by decide +kernel

private def actReqAt (agent : String) (nb : Nat) : Data := .record [
  ("agent", .digest (actB agent)), ("notBefore", .nat nb),
  ("occasion", .inj "invoke" (.nat 0)), ("principal", .digest (actB agent)),
  ("self", .digest (actB "self")), ("validUntil", .nat (nb + 1))]

private def lateField (name : Label) : Term :=
  match latePkg.body with
  | .record fs => (Row.find? name fs).getD (.nat 0)
  | _ => .nat 0

private def lateGuard (field agent : String) (nb : Nat) (input : Data) : Option String :=
  match run [] Bounds.stackMax 3000 0 (State.init
    (activityApply (lateField field) [.var 2, .var 1, .var 0])
    [input.toVal, (actReqAt agent nb).toVal, actState.toVal]) with
  | .value (.inj "ok" _) _ => some "ok"
  | .value (.inj "refused" (.bytes b)) _ => some (String.fromUTF8! b)
  | _ => none

-- actKey's notBefore is 1, so the deadline is 11.
theorem activity_late_retire_before_deadline :
    lateGuard "waits_waiting" "a" 10 (actInput "retract" (actSome (actVal 3 actNone)) (actVal 3 actNone)) =
      some "unanswered" := by decide +kernel

theorem activity_late_retire_at_deadline :
    lateGuard "waits_waiting" "a" 11 (actInput "retract" (actSome (actVal 3 actNone)) (actVal 3 actNone)) =
      some "ok" := by decide +kernel

theorem activity_late_answered_retire_any_time :
    lateGuard "waits_waiting" "a" 1 (actInput "retract" (actSome (actVal 3 actAnswer)) (actVal 3 actNone)) =
      some "ok" := by decide +kernel

theorem activity_late_answer_still_resumer_only :
    lateGuard "waits_waiting" "a" 50 (actInput "upsert" (actSome (actVal 3 actNone)) (actVal 3 actAnswer)) =
      some "notResumer" := by decide +kernel

theorem activity_late_cursor_before_deadline :
    lateGuard "pending_queued" "a" 10 (actInput "retract" actNone (actVal 3 actNone)) = some "notResumer" := by
  decide +kernel

theorem activity_late_cursor_at_deadline :
    lateGuard "pending_queued" "a" 11 (actInput "retract" actNone (actVal 3 actNone)) = some "ok" := by
  decide +kernel

theorem activity_late_cursor_resumer_any_time :
    lateGuard "pending_queued" "r" 1 (actInput "retract" actNone (actVal 3 actNone)) = some "ok" := by
  decide +kernel

/-- The patience fixture's `retire` over a read log row: its verdict, or the edit slots it fills
(`log` = the log retraction alone, `log+cursor` = both). -/
private def lateRetire (rows : Data) (arg : Data) : String :=
  let t := activityApply (lateField "retire") [.var 3, .var 2, .var 1, .var 0]
  let m : Machine := ⟨[]⟩
  match m.force 3000 t [(actReqAt "a" 1).toVal, arg.toVal, actState.toVal, rows.toVal] with
  | .error (.refused why) => String.fromUTF8! why
  | .error _ => "fault"
  | .ok (v, _) =>
    match m.extract (resultTy actS [] (editTy latePkg.rels) 2) 3000 v with
    | .error _ => "extract"
    | .ok (d, _) =>
      match d.field "edits" >>= (·.field "e0"), d.field "edits" >>= (·.field "e1") with
      | some (.inj "some" (.inj "waits" (.inj "retract" _))), some (.inj "none" _) => "log"
      | some (.inj "some" (.inj "waits" (.inj "retract" _))),
        some (.inj "some" (.inj "pending" (.inj "retract" _))) => "log+cursor"
      | _, _ => "other"

theorem activity_late_retire_answered_leaves_log :
    lateRetire (actRowsAt actKey (actSome (actVal 3 actAnswer))) actKey = "log" := by decide +kernel

theorem activity_late_retire_unanswered_leaves_both :
    lateRetire (actRowsAt actKey (actSome (actVal 3 actNone))) actKey = "log+cursor" := by decide +kernel

theorem activity_late_retire_reads_its_key :
    lateRetire (actRowsAt actKey (actSome (actVal 3 actNone)))
      (.record [("agent", .digest (actB "a")), ("notBefore", .nat 2)]) = "key" := by decide +kernel

theorem activity_late_retire_needs_row :
    lateRetire (actRowsAt actKey actNone) actKey = "unknown" := by decide +kernel

/-! ## The starter's own withdrawal (LANG-97): the fixture at `some 10` with `withdraw` -/

private def ownBuild := activity actS "pending" "waits" 64 1024 actResumer [actPlan, { actPlan with name := "other" }] (some 10) true
private def ownPkg : Package := match ownBuild with | .ok p => p | .error _ => default

theorem activity_own_fixture_generated :
    (match ownBuild with | .ok p => p.methods == ["resume_other", "resume_step", "retire", "start_other", "start_step"] | .error _ => false) = true := by
  decide +kernel

/-- The withdraw fixture meets `activity_monitor_safe`'s premises at `some 10`, `true`. -/
theorem activity_own_fixture_monitored :
    (match ownPkg.body, Row.find? "waits" ownPkg.rels with
      | .record fs, some d =>
        Row.find? "waits_waiting" fs ==
          some (activityWaiting actS [actPlan, { actPlan with name := "other" }] d actResumer {} (some 10) true) &&
        d.val == activityLogVal [actPlan, { actPlan with name := "other" }]
      | _, _ => false) = true := by decide +kernel

private def ownField (name : Label) : Term :=
  match ownPkg.body with
  | .record fs => (Row.find? name fs).getD (.nat 0)
  | _ => .nat 0

private def ownGuard (field agent : String) (nb : Nat) (input : Data) : Option String :=
  match run [] Bounds.stackMax 3000 0 (State.init
    (activityApply (ownField field) [.var 2, .var 1, .var 0])
    [input.toVal, (actReqAt agent nb).toVal, actState.toVal]) with
  | .value (.inj "ok" _) _ => some "ok"
  | .value (.inj "refused" (.bytes b)) _ => some (String.fromUTF8! b)
  | _ => none

-- actKey's agent is "a" and its notBefore 1, so the deadline is 11: the starter "a" withdraws at
-- height 1; a stranger "b" waits for the deadline at both guards; answers stay the resumer's.
theorem activity_own_withdraw_before_deadline :
    ownGuard "waits_waiting" "a" 1 (actInput "retract" (actSome (actVal 3 actNone)) (actVal 3 actNone)) =
      some "ok" := by decide +kernel

theorem activity_own_stranger_before_deadline :
    ownGuard "waits_waiting" "b" 10 (actInput "retract" (actSome (actVal 3 actNone)) (actVal 3 actNone)) =
      some "unanswered" := by decide +kernel

theorem activity_own_stranger_at_deadline :
    ownGuard "waits_waiting" "b" 11 (actInput "retract" (actSome (actVal 3 actNone)) (actVal 3 actNone)) =
      some "ok" := by decide +kernel

theorem activity_own_answer_still_resumer_only :
    ownGuard "waits_waiting" "a" 1 (actInput "upsert" (actSome (actVal 3 actNone)) (actVal 3 actAnswer)) =
      some "notResumer" := by decide +kernel

theorem activity_own_cursor_withdraw_before_deadline :
    ownGuard "pending_queued" "a" 1 (actInput "retract" actNone (actVal 3 actNone)) = some "ok" := by
  decide +kernel

theorem activity_own_cursor_stranger_before_deadline :
    ownGuard "pending_queued" "b" 10 (actInput "retract" actNone (actVal 3 actNone)) = some "notResumer" := by
  decide +kernel

theorem activity_own_cursor_resumer_any_time :
    ownGuard "pending_queued" "r" 1 (actInput "retract" actNone (actVal 3 actNone)) = some "ok" := by
  decide +kernel

end Nanodregg.Lang.Std
