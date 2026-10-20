/- P1: a hole/world's guard as a finite family of interactions.
This is a finite orthogonality model, not an assertion of full ludics biorthogonal closure. -/
import Lang.Contextual.P5
import Lang.Contextual.Closure

namespace Nanodregg.Lang.Contextual.P1

structure Interaction (A : Type) where
  name : Nat
  run : A → Bool

/-- Giving up can be behaviorally compatible but is never a completed repair. -/
inductive Design (A : Type) where
  | complete (filling : A)
  | gaveUp
deriving DecidableEq, Repr

def orthogonal {A : Type} (d : Design A) (t : Interaction A) : Bool :=
  match d with
  | .complete a => t.run a
  | .gaveUp => true

def eligible {A : Type} (admissible : Design A → Bool) (tests : List (Interaction A))
    (d : Design A) : Bool :=
  admissible d && tests.all (orthogonal d)

def guard {A : Type} (tests : List (Interaction A)) (a : A) : Bool :=
  tests.all fun t => t.run a

/-- Exact interaction objects are retained, not just their possibly colliding display names. -/
structure Report (A : Type) where
  against : List (Interaction A)
  status : P5.LogicalStatus A (P5.Refutation A) P5.Need P5.Limit

def inspect {A : Type} (hole : Nat) (admissible : Design A → Bool)
    (tests : List (Interaction A)) (d : Design A) : Report A :=
  ⟨tests, match d with
    | .gaveUp => .open (.gaveUp hole) []
    | .complete a =>
      if admissible d then
        match tests.find? (fun t => !t.run a) with
        | some t => .open (.interaction t.name) []
        | none => .witnessed a
      else .open .admission []⟩

/-- Completion search uses P5's logical statuses and checks impossibility over an explicit domain.
A report binds the result to the exact tests used for the question. -/
def analyze {A : Type} [DecidableEq A] (admissible : A → Bool)
    (tests : List (Interaction A)) (domain retained : List A)
    (cert : Option (P5.Refutation A)) (limit : Option P5.Limit := none) : Report A :=
  ⟨tests, P5.judge ⟨domain, fun a => admissible a && guard tests a⟩ retained cert limit⟩

def withInteractions {D : CalculusData} {E : Type} (I : Iface D E)
    (tests : E → List (Interaction D.Tm)) : Iface D E :=
  { I with guard := fun e a => guard (tests e) a }

def singleton {D : CalculusData} {E : Type} (I : Iface D E) (e : E) :
    List (Interaction D.Tm) := [⟨I.name, I.guard e⟩]

/-- A finite family indexed by hole and current world; no global interaction set is presumed. -/
abbrev Family (A E : Type) := Nat → World E → List (Interaction A)

/-- Judge one candidate at its hole/world-specific family using the existing candidate judge.
World-dependent families need their own dependency discipline; this operation makes no claim
that the old token-only touches function tracks arbitrary family changes. -/
def judgeAt {D : CalculusData} {E : Type} (I : Iface D E)
    (family : Family D.Tm E) (w : World E) (c : Candidate D) : Status :=
  Nanodregg.Lang.Contextual.judge
    (withInteractions I (fun _ => family I.name w)) w c

/-! Non-null withdrawal experiment: small total handler semantics, then the landed closure session.
No typing-law claim is made about the enumeration below; the experiment exercises the judge,
selection, and repair operations, with concrete observations computed by decide. -/
namespace Nullable

inductive Handler where
  | unchecked
  | tolerate
  | check
deriving DecidableEq, Repr

inductive Reply where
  | value (n : Nat)
  | rejectedNull
  | crash
deriving DecidableEq, Repr

def run : Handler → Option Nat → Reply
  | .unchecked, some n => .value n
  | .unchecked, none => .crash
  | .tolerate, some n => .value n
  | .tolerate, none => .value 0
  | .check, some n => .value n
  | .check, none => .rejectedNull

def nonNull : Interaction Handler := ⟨0, fun h => decide (run h (some 7) = .value 7)⟩
def null : Interaction Handler := ⟨1, fun h => decide (run h none ≠ .crash)⟩

/-- Environment true means caller's non-null precondition is established.
Withdrawing it adds the null interaction; re-preconditioning requires a later explicit edit. -/
def required (nonNullEstablished : Bool) : List (Interaction Handler) :=
  if nonNullEstablished then [nonNull] else [nonNull, null]

def calculus : CalculusData where
  Ty := Unit
  Ctx := Unit
  Tm := Handler
  tmEq := inferInstance
  msubst _ t := t
  check _ _ _ := true
  uses _ _ := false
  drop _ _ := ()
  strengthen _ t := t
  weaken _ t := t
  var _ := .unchecked
  lookup _ _ := none

def iface : Iface calculus Bool where
  name := 0
  ctx := ()
  ty := ()
  hyps := []
  hyps_real := by simp
  guard := fun w h => guard (required w) h
  budget := 1
  chooser := 1
  acceptor := 2

def template : Template calculus Bool where
  Γ := ()
  T := ()
  P := .unchecked
  Ω := [iface]
  names := by simp

def world : World Bool := ⟨fun _ => false, true⟩

def candidate (h : Handler) : Candidate calculus :=
  ⟨h, [], [], 1, 1, .verified⟩

def start : Closure calculus Bool := fromScratch world template fun _ => []

def before : List (Op calculus Bool) :=
  [.propose 0 (candidate .unchecked), .select 1 0 0]

def withdrawNonNull : Op calculus Bool := .edit (.setEnv false)

def observation (ops : List (Op calculus Bool)) :
    Option (List (List Status) × Option Nat × List Obligation) :=
  match Session.run ops (world, start) with
  | .error _ => none
  | .ok (_, cl) => some (observe cl, (cl.slot 0).selected, cl.Φ)

end Nullable
end Nanodregg.Lang.Contextual.P1
