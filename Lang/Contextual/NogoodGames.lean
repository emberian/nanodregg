/-
P11a: finite completion games with recorded nogood explanations.
Köhler et al. (2013), PDF pp3–4; de Kleer (1986), printed pp144–145.
The generic interface accepts the same token-list nogoods as contextual labels.
It replays the current acceptance test as well as each recorded explanation.
-/
import Lang.Contextual.Games
import Lang.Contextual.Closure

namespace Nanodregg.Lang.Contextual.P5.NogoodGames

/-- Köhler et al., PDF pp3–4: a finite completion question alternates between
choosing a candidate and challenging it. A rejected candidate leads to a sink
for the challenger; an accepted candidate itself is a losing challenger position. -/
inductive Position (A : Type) where
  | question
  | candidate (value : A)
  | terminal
deriving DecidableEq, Repr

/-- Köhler et al., PDF p2: this finite acyclic question is draw-free.
Separate cyclic arenas use Games.judgeDraw; budget limits imply no game value. -/
def moves {A : Type} (p : Problem A) : Position A → List (Position A)
  | .question => p.domain.map Position.candidate
  | .candidate a => if p.accepts a then [] else [.terminal]
  | .terminal => []

/-- de Kleer, printed p145: each excluded candidate names an actual recorded
nogood contained in its assumptions. This data is checked, never trusted by its type. -/
abbrev Certificate (A : Type) := List (A × List Token)

/-- de Kleer, printed pp144–145: record membership and subset explain exclusion;
P5's acceptance function is replayed too, so stale or misapplied records cannot refute
a currently acceptable candidate. Coverage is over the question's declared domain. -/
def checkCertificate {A : Type} [DecidableEq A] (p : Problem A)
    (supports : A → List Token) (nogoods : List (List Token)) (c : Certificate A) : Bool :=
  p.domain.all (fun a => c.any (fun row => row.1 == a)) &&
    c.all (fun row => decide (row.2 ∈ nogoods) &&
      row.2.all (fun t => decide (t ∈ supports row.1)) && !p.accepts row.1)

/-- Köhler et al., PDF p4; de Kleer, printed p145: refuted means lost with a
replayed, recorded nogood for every member of the finite domain. The landed
judge still chooses witnesses and handles operational limits without alteration. -/
def judge {A : Type} [DecidableEq A] (p : Problem A) (retained : List A)
    (supports : A → List Token) (nogoods : List (List Token))
    (certificate : Option (Certificate A)) (limit : Option Limit := none) :
    LogicalStatus A (Certificate A) Need Limit :=
  match P5.judge p retained none limit with
  | .witnessed a => .witnessed a
  | .outsideThisProcedure why => .outsideThisProcedure why
  | _ =>
    match certificate with
    | none => .open .searchRemaining []
    | some c =>
      if checkCertificate p supports nogoods c then .refuted c
      else .open .invalidRefutation []

end Nanodregg.Lang.Contextual.P5.NogoodGames
