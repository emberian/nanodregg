/- Executed support lookup teeth: identity, version, absence and ordering. -/
import Lang.StdHole

namespace Nanodregg.Lang.Std


private def support (cell pin : String) : Data :=
  .record [("cell", .digest cell.toUTF8), ("pin", .digest pin.toUTF8)]

private def noPoint : Data := .inj "none" (.record [])

private def point (cell : String) (pin : Option String) : Data :=
  .inj "some" (.record [
    ("key", .record [("cell", .digest cell.toUTF8)]),
    ("val", match pin with
      | none => .inj "none" (.record [])
      | some p => .inj "some" (.record [("by", .digest "poster".toUTF8), ("pin", .digest p.toUTF8)]))])

private def rows (a b c : Data) : Data :=
  .record [("facts", .record [("p0", a), ("p1", b), ("p2", c)])]

private def probe (s r : Data) : Option Nat :=
  match run [] Bounds.stackMax 3000 0
    (State.init (activityApply holeSupportProbe [.var 1, .var 0]) [r.toVal, s.toVal]) with
  | .value (.nat n) _ => some n
  | _ => none

theorem hole_probe_current :
    probe (support "cell" "v1") (rows (point "cell" (some "v1")) noPoint noPoint) = some 1 := by
  decide +kernel

theorem hole_probe_moved :
    probe (support "cell" "v1") (rows (point "cell" (some "v2")) noPoint noPoint) = some 2 := by
  decide +kernel

theorem hole_probe_withdrawn :
    probe (support "cell" "v1") (rows (point "cell" none) noPoint noPoint) = some 0 := by
  decide +kernel

theorem hole_probe_absent :
    probe (support "cell" "v1") (rows noPoint noPoint noPoint) = some 0 := by
  decide +kernel

theorem hole_probe_by_identity :
    probe (support "cell" "v1") (rows (point "other" (some "v1")) noPoint noPoint) = some 0 := by
  decide +kernel

theorem hole_probe_any_position :
    probe (support "cell" "v1")
      (rows (point "other" (some "v2")) noPoint (point "cell" (some "v1"))) = some 1 := by
  decide +kernel


private def candidate (status blocker : Data) : Data := .record [
  ("blocker", blocker), ("by", .digest "author".toUTF8), ("reason", .bytes "reason".toUTF8),
  ("s0", noPoint), ("s1", noPoint), ("status", status), ("value", .nat 7)]

private def birth (who : String) (status blocker : Data) : Option String :=
  let input := Data.record [
    ("edit", .inj "insert" (.record [
      ("key", .record [("cand", .digest "candidate".toUTF8)]),
      ("val", candidate status blocker)])),
    ("old", noPoint)]
  let req := Data.record [("agent", .digest who.toUTF8)]
  let clause := Term.lam holeState (.lam .nat (.bool true))
  match run [] Bounds.stackMax 3000 0 (State.init
    (activityApply (holeProposed .nat clause) [.var 2, .var 1, .var 0])
    [input.toVal, req.toVal, (Data.record []).toVal]) with
  | .value (.inj "ok" _) _ => some "ok"
  | .value (.inj "refused" (.bytes why)) _ => some (String.fromUTF8! why)
  | _ => none

theorem hole_birth_verified :
    birth "author" (.inj "verified" (.record [])) noPoint = some "ok" := by decide +kernel

theorem hole_birth_author :
    birth "stranger" (.inj "verified" (.record [])) noPoint = some "notYours" := by decide +kernel

theorem hole_birth_no_pruned_status :
    birth "author" (.inj "pruned" (.bytes "reason".toUTF8)) noPoint = some "prunedAtBirth" := by decide +kernel

theorem hole_birth_no_blocker :
    birth "author" (.inj "verified" (.record [])) (.inj "some" (support "fact" "v1")) =
      some "prunedAtBirth" := by decide +kernel

end Nanodregg.Lang.Std

