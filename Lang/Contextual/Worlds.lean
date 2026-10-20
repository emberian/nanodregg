/-
Alternative worlds for the contextual rule model (CARD P3).
A demonstration Mini can take, not a second kernel World or an admission path.
Default absence is tested against ONE proposed world. A reduct uses the landed
positive Rule/lfpIter machinery. Exhausted iteration is unfinished, never false.
-/
import Lang.Contextual.Closure

namespace Nanodregg.Lang.Contextual.Worlds

/-- A normal rule, with immutable external premise tokens. An absent atom is a
default test, not evidence for its explicit contrary. -/
structure NormalRule where
  head : Nat
  body : List Nat
  absent : List Nat
  supports : List Token
deriving DecidableEq, Repr

abbrev Program := List NormalRule
abbrev Alternative := List Nat

/-- Freeze default tests at the proposed world; only positive bodies remain. -/
def reduct {E : Type} (P : Program) (w : World E) (v : Alternative) : List Rule :=
  (P.filter fun r => r.supports.all w.live &&
    r.absent.all (fun a => !v.contains a)).map fun r => ⟨r.head, r.body⟩

/-- No external facts enter secretly: a fact is a rule with an empty body,
optionally backed by external premise tokens. -/
def ground (R : List Rule) (rounds : Nat) : Nat → Bool :=
  lfpIter R (fun _ => false) rounds

/-- Closure under every rule is checked, rather than inferred from the fuel. -/
def closed (R : List Rule) (v : Nat → Bool) : Bool :=
  R.all fun r => !(r.body.all v) || v r.head

/-- The finite universe of possible conclusions. Body-only atoms cannot be derived. -/
def heads (P : Program) : List Nat := (P.map NormalRule.head).eraseDups

def subsets : List Nat → List Alternative
  | [] => [[]]
  | a :: as => subsets as ++ (subsets as).map (a :: ·)

/-- None means the reduct has not stabilized. Some false is a completed rejection.
Comparison covers both directions and arbitrary proposed lists (order irrelevant). -/
def check {E : Type} (rounds : Nat) (P : Program) (w : World E)
    (v : Alternative) : Option Bool :=
  let R := reduct P w v
  let g := ground R rounds
  if closed R g then
    some (v.all g && (heads P).all (fun a => !g a || v.contains a))
  else none

/-- Complete finite search, retaining worlds separately. A pending reduct makes
the whole answer pending: a partially scanned list cannot justify absence. -/
def collect {E : Type} (rounds : Nat) (P : Program) (w : World E) :
    List Alternative → Option (List Alternative)
  | [] => some []
  | v :: vs => do
    let ok ← check rounds P w v
    let rest ← collect rounds P w vs
    pure (if ok then v :: rest else rest)

def analyze {E : Type} (rounds : Nat) (P : Program) (w : World E) :
    Option (List Alternative) :=
  collect rounds P w (subsets (heads P))

/-- The four requested distinctions plus the ordinary supported case and the
separate case of a completed search with no admissible world. A query names two
incompatible evidence atoms; it does not identify absence with explicit negation. -/
inductive Report where
  | noJustification
  | alternatives (left right : Alternative)
  | conflictingEvidence (proposed : Alternative)
  | unfinished
  | supported (worlds : List Alternative)
  | noWorld
deriving DecidableEq, Repr

/-- Diagnose a proposed evidence world and a pair of opposed observations.
Conflicting evidence is reported about the proposal, never asserted admissible.
Alternatives are witnesses from the completed admissible-world search. -/
def report {E : Type} (rounds : Nat) (P : Program) (w : World E)
    (positive negative : Nat) (proposed : Alternative) : Report :=
  match analyze rounds P w with
  | none => .unfinished
  | some worlds =>
    if proposed.contains positive && proposed.contains negative then .conflictingEvidence proposed
    else if worlds.isEmpty then .noWorld
    else
      match worlds.find? (·.contains positive), worlds.find? (·.contains negative) with
      | some left, some right =>
        if left == right then .conflictingEvidence left else .alternatives left right
      | none, none => .noJustification
      | _, _ => .supported worlds

/-- A real edit session, observing every revision including the initial one.
Rules and token identities are retained throughout. -/
def session {E : Type} (rounds : Nat) (P : Program) :
    List (Edit E) → World E → List (Option (List Alternative))
  | [], w => [analyze rounds P w]
  | e :: es, w => analyze rounds P w :: session rounds P es (e.apply w)

namespace Experiment

def pToken : Token := ⟨10, 0⟩
def qToken : Token := ⟨11, 0⟩
def initial : World Unit := ⟨fun t => t == pToken || t == qToken, ()⟩
def twoRules : Program :=
  [⟨0, [], [1], [pToken]⟩, ⟨1, [], [0], [qToken]⟩]
def withdrawn : World Unit := (Edit.withdraw pToken).apply initial
def neither : World Unit := (Edit.withdraw qToken).apply withdrawn
def both : Alternative := [0, 1]
def union (a b : Alternative) : Alternative := (a ++ b).eraseDups

def cycle : Program :=
  [⟨0, [], [], [pToken]⟩, ⟨1, [0], [], []⟩, ⟨1, [2], [], []⟩,
   ⟨2, [1], [], []⟩, ⟨5, [], [], [qToken]⟩, ⟨6, [5], [], []⟩]
def beforeCycle : Alternative := [0, 1, 2, 5, 6]
def afterCycle : Alternative := [5, 6]

end Experiment
end Nanodregg.Lang.Contextual.Worlds
