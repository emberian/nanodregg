/-
# Protocol.Rows.Judge — what a driver saw, and whether the row passed

A driver runs a row and reports an `Observed`; `judge` alone decides. An `exe` row passes when its
executable exits 0 with the row's last line. A `members` row passes when every line got the outcome
it declares, in order, AND the operations the driver saw on the wire are exactly the ones the row
declares, and so are the receiver kinds of the calls it froze: a row that claims an operation or a
kind it never sent, or sends one it does not declare, is red
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
  /-- `members` rows: the receiver kind (`Body` constructor) of every call a client froze -/
  kinds : List String := []

inductive Verdict
  | pass
  | fail (why : String)
  /-- the first line that differs got `hang`: the system missed a liveness deadline. Not a pass
  and not a fail; the runner reports it by name -/
  | hang (why : String)
  deriving DecidableEq, Repr

/-- The first line whose outcome differs from the declared one, if any. -/
def mismatch : Nat → List Expect → List Expect → Option String
  | _, [], [] => none
  | i, [], _ :: _ => some s!"line {i}: not run"
  | i, _ :: _, [] => some s!"line {i}: an outcome the row does not declare"
  | i, g :: gs, e :: es =>
      if g = e then mismatch (i + 1) gs es else some s!"line {i}: got {g.text}, expected {e.text}"

/-- The first line whose outcome differs from the declared one got `hang`. -/
def firstDiffHangs : List Expect → List Expect → Bool
  | g :: gs, e :: es => if g = e then firstDiffHangs gs es else g = .hang
  | _, _ => false

/-- Two lists name the same set. -/
def sameSet {α : Type} [BEq α] (a b : List α) : Bool := a.all (b.contains ·) && b.all (a.contains ·)

def judge (r : Row) (o : Observed) : Verdict :=
  match r.drive with
  | .exe _ _ last =>
      if o.exit ≠ 0 then .fail s!"exit {o.exit}"
      else if o.last ≠ last then .fail s!"last line {repr o.last}, expected {repr last}"
      else .pass
  | .members ls =>
      match mismatch 0 o.outcomes (ls.map Line.expect) with
      | some why => if firstDiffHangs o.outcomes (ls.map Line.expect) then .hang why else .fail why
      | none =>
          if !sameSet o.ops r.ops then .fail s!"observed ops {repr o.ops}, declared {repr r.ops}"
          else if !sameSet o.kinds r.kinds then .fail s!"observed kinds {o.kinds}, declared {r.kinds}"
          else .pass

/-- A row's plant names a line the row has, and an outcome that line does not declare: a plant that
"catches" the declared outcome would be caught by an unmutated system. -/
def Row.plantDiffers (r : Row) : Bool :=
  match r.plant with
  | .caught _ l g => decide (l < r.lines.length) && (r.lines.map Line.expect)[l]? != some g
  | .internal _ => true

/-- A plant is caught when the lines before its line keep their declared outcomes and its line gets
the planted outcome (which `Protocol.Proofs.Rows.plants_differ` says is not the declared one). -/
def caught (r : Row) (o : Observed) (line : Nat) (got : Expect) : Bool :=
  o.outcomes.take line == (r.lines.map Line.expect).take line && o.outcomes[line]? == some got

end Nanodregg.Protocol
