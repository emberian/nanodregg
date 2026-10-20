/-
P11a: certified provenance-game draws. Köhler–Ludäscher–Zinn (2013),
First-Order Provenance Games, PDF pp3–4. Infinite play is a draw, while a
position is drawn only if neither player can force a win. Budget exhaustion
alone does not establish either fact. This is a sufficient finite trap certificate.
-/
import Lang.Contextual.P5

namespace Nanodregg.Lang.Contextual.P5.Games

/-- Köhler et al., PDF pp3–4: a finite recorded trap is evidence for indefinite
play. Existing operational limits retain their own constructor and semantics. -/
inductive OutsideReason where
  | drawn (region : List Nat)
  | procedureLimit (limit : Limit)
deriving DecidableEq, Repr

/-- Köhler et al., PDF pp3–4: this stronger-than-necessary draw certificate records
a nonempty successor set at every node and forbids every exit. The root must occur.
It does not purport to find all game draws; failing it leaves the problem open. -/
def checkDraw (moves : Nat → List Nat) (root : Nat) (region : List Nat) : Bool :=
  region.contains root && region.all (fun x =>
    !(moves x).isEmpty && (moves x).all region.contains)

/-- Köhler et al., PDF p4: only a checked semantic draw is tagged drawn.
A failed certificate is an open obligation, not a loss or proof of impossibility. -/
def judgeDraw (moves : Nat → List Nat) (root : Nat) (region : List Nat) :
    LogicalStatus Nat (List Nat) Need OutsideReason :=
  if checkDraw moves root region then .outsideThisProcedure (.drawn region)
  else .open .invalidRefutation []

/-- Köhler et al., PDF p3: the simplest infinite-play arena; its sole move is a
self-loop. Acyclic FO provenance games (PDF p2) have no such drawn positions. -/
def loopMoves (x : Nat) : List Nat := [x]

end Nanodregg.Lang.Contextual.P5.Games
