/- P9: a closure carrying a recorded nogood database (de Kleer 1986, pp144–145).
This append-only extension does not change the landed Closure or its theorems.
The checked operations below consume the database; erasing toClosure loses this policy. -/
import Lang.Contextual.ProvenanceRepairs
import Lang.Contextual.P5

namespace Nanodregg.Lang.Contextual.P9

variable {D : CalculusData} {E : Type}

/-- de Kleer pp144–145: an ATMS label is consistent relative to recorded nogoods.
The base closure still carries the single retained template, candidates, and history. -/
structure RecordedClosure (D : CalculusData) (E : Type) extends Closure D E where
  nogoods : List (List Token)

/-- The first recorded inconsistent subset of the EFFECTIVE support, including used hypotheses.
No liveness test: a missing member does not turn an inconsistent justification into a repair. -/
def findNogood (ngs : List (List Token)) (supports : List Token) : Option (List Token) :=
  ngs.find? fun ng => ng.all (fun t => decide (t ∈ supports))

/-- Checked verdict plus its recorded evidence. A nogood uses the existing named guard conflict:
it is an additional admissibility condition, never a new assumption of falsity. -/
structure NogoodJudgment where
  status : Status
  nogood : Option (List Token)
deriving DecidableEq, Repr

/-- de Kleer pp144–145: consistency is tested before missing supports.
The original judge is still the sole checker of typing, guard, blockers and budget. -/
def judgeRecorded (cl : RecordedClosure D E) (I : Iface D E) (w : World E)
    (c : Candidate D) : NogoodJudgment :=
  match findNogood cl.nogoods (effSupports I c) with
  | some ng => ⟨.conflict .guardFails, some ng⟩
  | none => ⟨judge I w c, none⟩

/-- Retained alternatives consistent with recorded nogoods, used for both labels and repairs. -/
def eligibleCandidates (cl : RecordedClosure D E) (I : Iface D E)
    (cs : List (Candidate D)) : List (Candidate D) :=
  cs.filter fun c => (findNogood cl.nogoods (effSupports I c)).isNone

/-- de Kleer p145: provenance is built only from consistent justifications, retaining env literals. -/
def recordedLabel (cl : RecordedClosure D E) (I : Iface D E) (cs : List (Candidate D)) :=
  label I (eligibleCandidates cl I cs)

/-- Prop16 p23, under the same recorded consistency policy as selection. -/
def recordedRepairPlans (cl : RecordedClosure D E) (I : Iface D E) (w : World E)
    (cs : List (Candidate D)) :=
  repairPlans I w (eligibleCandidates cl I cs)

/-- de Kleer p145: a recorded inconsistent candidate is refuted in this policy at every world.
Other failure statuses stay open; failed search is not a refutation of the hole. -/
def classifyRecorded (cl : RecordedClosure D E) (I : Iface D E) (w : World E)
    (c : Candidate D) : P5.LogicalStatus (Candidate D) (List Token) P5.Need P5.Limit :=
  match (judgeRecorded cl I w c).nogood with
  | some ng => .refuted ng
  | none =>
    if (judgeRecorded cl I w c).status = .verified then .witnessed c
    else .open .admission []

/-- The recorded policy reaches selection: reject inconsistent support before delegating
authority, accepted-history and current-world checks to the original select. -/
def selectRecorded (cl : RecordedClosure D E) (w : World E) (p : Party) (u i : Nat) :
    Except Refusal (RecordedClosure D E) :=
  match cl.toClosure.find u with
  | none => .error .unknownHole
  | some I =>
    match (cl.slot u).cands[i]? with
    | none => .error .noCandidate
    | some c =>
      match findNogood cl.nogoods (effSupports I c) with
      | some _ => .error (.notVerified (.conflict .guardFails))
      | none =>
        (Nanodregg.Lang.Contextual.select w p u i cl.toClosure).map
          fun base => { toClosure := base, nogoods := cl.nogoods }

end Nanodregg.Lang.Contextual.P9
