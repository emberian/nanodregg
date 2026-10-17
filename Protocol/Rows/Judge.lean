/-
# Protocol.Rows.Judge — what a driver saw, and whether the row passed

A driver runs a row and reports an `Observed`; `judge` alone decides. An `exe` row passes when its
executable exits 0 with the row's last line. A `members` row passes when every line got the outcome
it declares, in order, AND the operations the driver saw on the wire are exactly the ones the row
declares: a row that claims an operation it never sent, or sends one it does not declare, is red
(`Protocol.Proofs.Judge.judge_members_pass_iff`). That is what makes `every_op_has_a_row` a
measured fact rather than a claim.
-/
import Protocol.Rows

namespace Nanodregg.Protocol

/-- What a driver saw while running one row. -/
structure Observed where
  /-- `exe` rows: the exit code and the last non-empty line of stdout -/
  exit : UInt32 := 0
  last : String := ""
  /-- `members` rows: each line's outcome in order, and every operation sent on either socket -/
  outcomes : List Expect := []
  ops : List Op := []

inductive Verdict
  | pass
  | fail (why : String)
  deriving DecidableEq, Repr

/-- The first line whose outcome differs from the declared one, if any. -/
def mismatch : Nat → List Expect → List Expect → Option String
  | _, [], [] => none
  | i, [], _ :: _ => some s!"line {i}: not run"
  | i, _ :: _, [] => some s!"line {i}: an outcome the row does not declare"
  | i, g :: gs, e :: es =>
      if g = e then mismatch (i + 1) gs es else some s!"line {i}: got {repr g}, expected {repr e}"

/-- Two operation lists name the same set. -/
def sameOps (a b : List Op) : Bool := a.all (b.contains ·) && b.all (a.contains ·)

def judge (r : Row) (o : Observed) : Verdict :=
  match r.drive with
  | .exe _ _ last =>
      if o.exit ≠ 0 then .fail s!"exit {o.exit}"
      else if o.last ≠ last then .fail s!"last line {repr o.last}, expected {repr last}"
      else .pass
  | .members ls =>
      match mismatch 0 o.outcomes (ls.map Line.expect) with
      | some why => .fail why
      | none =>
          if sameOps o.ops r.ops then .pass
          else .fail s!"observed ops {repr o.ops}, declared {repr r.ops}"

end Nanodregg.Protocol
