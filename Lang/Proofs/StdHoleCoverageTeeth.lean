/- Kernel-executed teeth for complete self-row observation before judgment. -/
import Lang.StdHole

namespace Nanodregg.Lang.Std

private def absent : Data := .inj "none" (.record [])
private def dep (name : String) : Data :=
  .inj "some" (.record [("cell", .digest name.toUTF8), ("pin", .digest "v".toUTF8)])
private def point (name : String) (present : Bool) : Data :=
  .inj "some" (.record [("key", .record [("cell", .digest name.toUTF8)]),
    ("val", if present then .inj "some" (.record
      [("by", .digest "author".toUTF8), ("pin", .digest "v".toUTF8)]) else absent)])
private def rows (a b c : Data) : Data :=
  .record [("facts", .record [("p0", a), ("p1", b), ("p2", c)])]
private def candidate (s0 s1 blocker : Data) : Data := .record [
  ("blocker", blocker), ("by", .digest "author".toUTF8), ("reason", .bytes "reason".toUTF8),
  ("s0", s0), ("s1", s1), ("status", .inj "verified" (.record [])), ("value", .nat 7)]
private def check (clause : Bool) (c r : Data) : Option String :=
  match run [] Bounds.stackMax 5000 0 (State.init
    (activityApply (holeCheckedJudge .nat (.lam holeState (.lam .nat (.bool clause))))
      [.var 2, .var 1, .var 0]) [r.toVal, c.toVal, (Data.record []).toVal]) with
  | .value (.inj l _) _ => some ("status " ++ l)
  | .fault (.refused why) _ => some ("refused " ++ String.fromUTF8! why)
  | _ => none

theorem hole_omitted_support0_refused :
    check true (candidate (dep "a") absent absent) (rows absent absent absent) =
      some "refused support0 withdrawn" := by decide +kernel

theorem hole_omitted_support1_refused :
    check true (candidate absent (dep "b") absent) (rows absent absent absent) =
      some "refused support1 withdrawn" := by decide +kernel

theorem hole_omitted_blocker_refused :
    check true (candidate absent absent (dep "c")) (rows absent absent absent) =
      some "refused pruned" := by decide +kernel

theorem hole_conflict_requires_observation :
    check false (candidate absent absent (dep "c")) (rows absent absent absent) =
      some "refused pruned" := by decide +kernel

theorem hole_observed_absent_blocker_releases :
    check true (candidate absent absent (dep "c")) (rows (point "c" false) absent absent) =
      some "status verified" := by decide +kernel

theorem hole_observed_absent_support_records :
    check true (candidate (dep "a") absent absent) (rows (point "a" false) absent absent) =
      some "status support0Withdrawn" := by decide +kernel

theorem hole_observed_live_blocker_records :
    check true (candidate absent absent (dep "c")) (rows (point "c" true) absent absent) =
      some "status pruned" := by decide +kernel

theorem hole_coverage_follows_keys :
    check true (candidate (dep "a") (dep "b") (dep "c"))
      (rows (point "b" true) (point "c" false) (point "a" true)) =
      some "status verified" := by decide +kernel

theorem hole_unrelated_row_is_not_coverage :
    check true (candidate absent absent (dep "c")) (rows (point "other" false) absent absent) =
      some "refused pruned" := by decide +kernel

end Nanodregg.Lang.Std
