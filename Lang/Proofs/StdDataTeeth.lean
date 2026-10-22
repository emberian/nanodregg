/- Executable teeth for structural equality, using the deployed evaluator and checker. -/
import Lang.StdData
import Lang.Check

namespace Nanodregg.Lang.Std

private def equalityResult (T : Ty) (x y : Term) : Option Bool :=
  match run [] Bounds.stackMax 1000 0 (State.init (eqData T x y)) with
  | .value (.bool b) _ => some b
  | _ => none

private def equalityTy : Ty := .record [
  ("a", .bool), ("b", .bytes), ("c", .digest),
  ("d", .sum [("left", .nat), ("right", .nat)])]

private def equalityValue (label : Label) (n : Nat) : Term := .record [
  ("a", .bool true), ("b", .bytes "captured".toUTF8), ("c", .digest "id".toUTF8),
  ("d", .inj (.sum [("left", .nat), ("right", .nat)]) label (.nat n))]

theorem eqData_nested_checks :
    infer [] [] (eqData equalityTy (equalityValue "left" 3) (equalityValue "left" 4)) (Ω := []) = some .bool := by
  decide +kernel

theorem eqData_nested_equal :
    equalityResult equalityTy (equalityValue "left" 3) (equalityValue "left" 3) = some true := by
  decide +kernel

theorem eqData_nested_payload_diff :
    equalityResult equalityTy (equalityValue "left" 3) (equalityValue "left" 4) = some false := by
  decide +kernel

theorem eqData_nested_tag_diff :
    equalityResult equalityTy (equalityValue "left" 3) (equalityValue "right" 3) = some false := by
  decide +kernel

theorem eqData_bool_diff : equalityResult .bool (.bool true) (.bool false) = some false := by
  decide +kernel

theorem eqData_empty_record :
    equalityResult (.record []) (.record []) (.record []) = some true := by
  decide +kernel

end Nanodregg.Lang.Std
