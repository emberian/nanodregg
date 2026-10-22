/- Observable data and evaluator environments for the generated hole.
Pure descriptions only; their semantics are proved in Lang.Proofs.StdHole*. -/
import Lang.StdHole

namespace Nanodregg.Lang.Std

def holeProbeClosure (env : Env) : Val :=
  match holeSupportProbe with
  | .lam _ body => .clo body env
  | _ => .record []

def holeJudgeEnv (rows candidate state : Val) (env : Env) : Env :=
  holeProbeClosure (rows :: candidate :: state :: env) :: rows :: candidate :: state :: env

def holeObservation (clause : Term) (i : Nat) : Term :=
  ((holeObservationTerms clause)[i]?).getD (.bool false)

def holeAdmission (l : Label) : Except Fault Val :=
  match l with
  | "verified" => .ok (.bool true)
  | "support0Dead" => .error (.refused "support0 dead".toUTF8)
  | "support0Moved" => .error (.refused "support0 moved".toUTF8)
  | "support0Withdrawn" => .error (.refused "support0 withdrawn".toUTF8)
  | "support1Dead" => .error (.refused "support1 dead".toUTF8)
  | "support1Moved" => .error (.refused "support1 moved".toUTF8)
  | "support1Withdrawn" => .error (.refused "support1 withdrawn".toUTF8)
  | _ => .error (.refused l.toUTF8)

def holeRecordedStatus (l : Label) (reason : ByteArray) : Data :=
  match l with
  | "conflict" => .inj "conflict" (.bytes "clause".toUTF8)
  | "pruned" => .inj "pruned" (.bytes reason)
  | "support0Dead" => .inj "suspended" (.bytes "support0 dead".toUTF8)
  | "support0Moved" => .inj "suspended" (.bytes "support0 moved".toUTF8)
  | "support0Withdrawn" => .inj "suspended" (.bytes "support0 withdrawn".toUTF8)
  | "support1Dead" => .inj "suspended" (.bytes "support1 dead".toUTF8)
  | "support1Moved" => .inj "suspended" (.bytes "support1 moved".toUTF8)
  | "support1Withdrawn" => .inj "suspended" (.bytes "support1 withdrawn".toUTF8)
  | _ => .inj "verified" (.record [])

/-- One live point of the facts read: its cell, the fact's poster and pin (none: the row is
absent), and whether the cell is live in the caller's pinned view (E1). -/
structure HolePoint where
  cell : ByteArray
  author : ByteArray
  pin : Option ByteArray
  live : Bool

def holeSupportData (cell pin : ByteArray) : Data :=
  .record [("cell", .digest cell), ("pin", .digest pin)]

def holePointData : Option HolePoint → Data
  | none => .inj "none" (.record [])
  | some p => .inj "some" (.record [
      ("key", .record [("cell", .digest p.cell)]),
      ("live", .bool p.live),
      ("val", match p.pin with
        | none => .inj "none" (.record [])
        | some pin => .inj "some" (.record [("by", .digest p.author), ("pin", .digest pin)]))])

def holePointObservation (cell pin : ByteArray) : Option HolePoint → Nat
  | none => 0
  | some p => if p.cell = cell then
      match p.pin with | none => 0 | some v => if v = pin then (if p.live then 1 else 3) else 2
    else 0

/-- Bounded complete collection; the first omitted read refuses by its key.
Mokhov et al. 2018, §4.2.2 pp.79:14–15. -/
def collect {A B R : Type} (missing : A → R) (read : A → Option B) :
    List A → Except R (List B)
  | [] => .ok []
  | k :: ks =>
    match read k with
    | none => .error (missing k)
    | some v => match collect missing read ks with
      | .error e => .error e
      | .ok vs => .ok (v :: vs)

/-- P10's complete collector, specialized to the emitted finite dependency
roles. These Booleans mean observed, not live; the payload may record absence. -/
def holeCoverageOutcome (s0 s1 blocker : Bool) : Except Fault Val :=
  (collect
    (fun r : Bool × String => Fault.refused r.2.toUTF8)
    (fun r : Bool × String => if r.1 then some () else none)
    [(s0, "support0 withdrawn"), (s1, "support1 withdrawn"), (blocker, "pruned")]).map
      (fun _ => Val.bool true)

def holeCoveredClosure (env : Env) : Val :=
  match holeSupportCovered with
  | .lam _ body => .clo body env
  | _ => .record []

def holeCoverageEnv (rows candidate state : Val) (env : Env) : Env :=
  holeCoveredClosure (rows :: candidate :: state :: env) :: rows :: candidate :: state :: env

def holeCheckedEnv (rows candidate state : Val) (env : Env) : Env :=
  .bool true :: holeCoverageEnv rows candidate state env

def holeCoverageObservation (i : Nat) : Term :=
  (holeCoverageTerms[i]?).getD (.bool false)

def holeCheckedOutcome (s0 s1 blocker : Bool) (l : Label) : Except Fault Val :=
  (holeCoverageOutcome s0 s1 blocker).bind fun _ => .ok (.inj l (.record []))

def holeCheckedAdmission (s0 s1 blocker : Bool) (l : Label) : Except Fault Val :=
  (holeCoverageOutcome s0 s1 blocker).bind fun _ => holeAdmission l

end Nanodregg.Lang.Std
