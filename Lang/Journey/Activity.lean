/- Activity surface composition is accepted by the same package checker. -/
import Lang.Surface

namespace Nanodregg.Lang.Std

private def activitySurfaceText : String := "
(package
  (state (rec (resident digest) (total nat)))
  (rel facts (key (id digest)) (val nat) (limit 64))
  (activity pending waits (limits 64 1024)
    (resumer (deq req.agent state.resident))
    (plan step (arg nat) (resp (sum (keep (rec)) (set nat)))
      (start state)
      (resume (case response
        (keep _ state)
        (set n (with state (total (+ captured n))))))))
  (method post (arg (rec (id digest) (value nat))) (edits 1)
    (done state (insert facts (record (id arg.id)) arg.value))))
"

def activitySurfaceVerdict : String :=
  match Surface.readPackage activitySurfaceText with
  | .error e => e.name
  | .ok p => match p.checkWith [] with
    | .error e => e.text
    | .ok () => "ok"

end Nanodregg.Lang.Std
