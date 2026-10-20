/- P5: finite completion judgments, suspended negation, polarized transition systems.
A finite domain is part of the QUESTION, never inferred from the retained search list.
Refutation evidence is data; only judge checks it. Soundness is in Proofs/Contextual/P5. -/
import Lang.Contextual.Protocol

namespace Nanodregg.Lang.Contextual.P5


/-- Four logical outcomes. Open always names at least one obligation. -/
inductive LogicalStatus (Witness Refutation Ob Reason : Type) where
  | witnessed (witness : Witness)
  | open (first : Ob) (rest : List Ob)
  | refuted (evidence : Refutation)
  | outsideThisProcedure (reason : Reason)
deriving DecidableEq, Repr

inductive Need where
  | searchRemaining
  | invalidRefutation
  | unfilled (atom : Nat)
  | admission
  | interaction (name : Nat)
  | gaveUp (name : Nat)
deriving DecidableEq, Repr

inductive Limit where
  | unsupportedFragment
  | budgetExhausted
deriving DecidableEq, Repr

structure Problem (A : Type) where
  domain : List A
  accepts : A → Bool

/-- An exclusion argument enumerates candidates, and the checker replays every exclusion. -/
structure Refutation (A : Type) where
  excluded : List A
deriving DecidableEq, Repr

variable {A : Type} [DecidableEq A]

def Problem.valid (p : Problem A) (a : A) : Bool :=
  decide (a ∈ p.domain) && p.accepts a

def checkRefutation (p : Problem A) (r : Refutation A) : Bool :=
  p.domain.all (fun a => decide (a ∈ r.excluded)) &&
    r.excluded.all (fun a => !p.accepts a)

/-- Supported retained search with an optional checked impossibility argument.
No certificate, or a bad certificate, leaves the completion question OPEN. -/
def judge (p : Problem A) (retained : List A) (certificate : Option (Refutation A))
    (limit : Option Limit := none) : LogicalStatus A (Refutation A) Need Limit :=
  match limit with
  | some why => .outsideThisProcedure why
  | none =>
    match retained.find? p.valid with
    | some a => .witnessed a
    | none =>
      match certificate with
      | none => .open .searchRemaining []
      | some r =>
        if checkRefutation p r then .refuted r else .open .invalidRefutation []

/-- Open Boolean syntax. A missing atom is a residual, including under negation.
Conjunction is strict: both judgments must finish; it performs no Boolean shortcut. -/
inductive Formula where
  | atom (name : Nat)
  | neg (body : Formula)
  | conj (left right : Formula)
deriving DecidableEq, Repr

inductive Evaluation where
  | value (b : Bool)
  | suspended (first : Nat) (rest : List Nat)
deriving DecidableEq, Repr

def Evaluation.neg : Evaluation → Evaluation
  | .value b => .value (!b)
  | .suspended n ns => .suspended n ns

def Evaluation.conj : Evaluation → Evaluation → Evaluation
  | .value a, .value b => .value (a && b)
  | .suspended n ns, .suspended m ms => .suspended n (ns ++ m :: ms)
  | .suspended n ns, .value _ => .suspended n ns
  | .value _, .suspended n ns => .suspended n ns

def evaluate (env : Nat → Option Bool) : Formula → Evaluation
  | .atom n => match env n with
    | some b => .value b
    | none => .suspended n []
  | .neg p => (evaluate env p).neg
  | .conj p q => (evaluate env p).conj (evaluate env q)

/-- Input-deterministic interface automata; outputs may be nondeterministic.
A receive is chosen by the peer (LANG-67 'theirs'); an emission by us ('ours').
No hidden/internal actions or fairness claim are included. -/
structure Machine (State Input Output : Type) where
  receive : State → Input → Option State
  emit : State → List (Output × State)

inductive Action (Input Output : Type) where
  | input (value : Input)
  | output (value : Output)
deriving DecidableEq, Repr

def Action.owner {I O : Type} : Action I O → Protocol.Polarity
  | .input _ => .theirs
  | .output _ => .ours

def receiveAll {S I O : Type} (m : Machine S I O) : S → List I → Option S
  | s, [] => some s
  | s, i :: is => (m.receive s i).bind (fun s' => receiveAll m s' is)

/-- Price receiver with a one-use input and a pending reply. -/
def priceReceiver (cap : Nat) (outputs : List Bool) : Machine Bool Nat Bool where
  receive s n := if s = false ∧ n ≤ cap then some true else none
  emit s := if s then outputs.map (fun b => (b, false)) else []

/-- A status session: each revision carries its question, retained search and certificate.
Keeping questions explicit prevents a refutation of yesterday's domain being reused today. -/
structure Request (A : Type) where
  problem : Problem A
  retained : List A
  certificate : Option (Refutation A)
  limit : Option Limit

def runSession (requests : List (Request A)) : List (LogicalStatus A (Refutation A) Need Limit) :=
  requests.map fun q => judge q.problem q.retained q.certificate q.limit

def statusSession : List (Request Nat) :=
  [⟨⟨[0, 1], fun n => n == 1⟩, [0], none, none⟩,
   ⟨⟨[0, 1], fun n => n == 1⟩, [0, 1], none, none⟩,
   ⟨⟨[0, 1], fun _ => false⟩, [0, 1], some ⟨[0, 1]⟩, none⟩,
   ⟨⟨[0, 1], fun _ => false⟩, [], none, some .unsupportedFragment⟩]

end Nanodregg.Lang.Contextual.P5
