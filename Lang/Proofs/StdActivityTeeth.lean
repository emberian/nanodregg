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


theorem activity_fixture_generated : actBuildName = "ok" := by decide +kernel

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

end Nanodregg.Lang.Std
