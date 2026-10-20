/- First-class repair objects. P4; a demonstration Mini can take.
The indexed data lives here; correctness and equivalence laws live in Proofs.
The old five outcomes embed unchanged; transport adds the sixth case. -/
import Lang.Contextual.Closure

namespace Nanodregg.Lang.Contextual.RepairObjects

variable {D : CalculusData} {E : Type}

/-- An edit path with its source and destination in the type. -/
inductive Change (E : Type) : World E → World E → Type where
  | stay (w : World E) : Change E w w
  | edit (w : World E) (e : Edit E) : Change E w (e.apply w)
  | then {w v z : World E} : Change E w v → Change E v z → Change E w z

/-- A correspondence is data. The registry's Sound law certifies an equivalence on
checker-accepted fillings, including both inverses, not just a one-way replacement. -/
structure Correspondence (D : CalculusData) (E : Type) where
  source : Iface D E
  target : Iface D E
  forward : D.Tm → D.Tm
  backward : D.Tm → D.Tm

/-- Certificate identifiers resolve only through the supplied checked registry.
Its Sound predicate is in the proof module, just as CalculusData uses CalculusLaws. -/
abbrev Registry (D : CalculusData) (E : Type) := Nat → Option (Correspondence D E)

/-- Transport retains the original term and the certificate, so it is distinguishable
from an unrelated replacement even when their destination terms coincide. -/
structure TransportEvidence (D : CalculusData) (E : Type) where
  certificate : Nat
  correspondence : Correspondence D E
  original : Candidate D
  image : Candidate D

/-- Six semantic outcomes: the existing five, plus checked representation transport. -/
inductive Outcome (D : CalculusData) (E : Type) where
  | existing (outcome : Nanodregg.Lang.Contextual.Outcome D)
  | transported (evidence : TransportEvidence D E)

inductive OutcomeKind where
  | kept | replacement | strengthening | alternative | suspended | transported
deriving DecidableEq, Repr

def Outcome.kind : Outcome D E → OutcomeKind
  | .existing (.kept _) => .kept
  | .existing (.replacement _ _ _) => .replacement
  | .existing (.strengthening _ _ _) => .strengthening
  | .existing (.alternative _ _) => .alternative
  | .existing (.suspended _ _) => .suspended
  | .transported _ => .transported

inductive TransportRefusal where
  | unknownCertificate
  | sourceIllTyped
  | destination (status : Status)
deriving DecidableEq, Repr


/-- World-indexed state; coherence is a separate law, not an unchecked field. -/
structure State (D : CalculusData) {E : Type} (w : World E) where
  closure : Closure D E

/-- A resumable residual retains the template, all alternatives, history and world. -/
structure Residual (D : CalculusData) (E : Type) where
  world : World E
  closure : Closure D E
  outcomes : List (Outcome D E)

/-- Include obligations from every suspended alternative, not only the selected one. -/
def Residual.obligations (r : Residual D E) : List Obligation :=
  (r.closure.Φ ++ r.outcomes.flatMap (fun
    | .existing (.suspended _ obligations) => obligations
    | _ => [])).eraseDups

structure Result (D : CalculusData) {E : Type} (w : World E) where
  state : State D w
  /-- Ordered checkpoints: composition never discards intermediate obligations. -/
  residuals : List (Residual D E)
  inspected : List (Nat × Nat)
  transportRefusals : List TransportRefusal

/-- A repair is a value, abstractable over its indexed edit; arbitrary values need Sound. -/
structure Repair (D : CalculusData) {E : Type} {w v : World E} (e : Change E w v) where
  run : State D w → Result D v

def Repair.identity (w : World E) : Repair D (.stay w) :=
  ⟨fun s => ⟨s, [], [], []⟩⟩

def Repair.atomic (w : World E) (e : Edit E) : Repair D (.edit w e) :=
  ⟨fun s =>
    let r := repair w e s.closure
    ⟨⟨r.1⟩, [⟨e.apply w, r.1, r.2.1.map Outcome.existing⟩], r.2.2, []⟩⟩

def Repair.compose {w v z : World E} {e : Change E w v} {f : Change E v z}
    (r : Repair D e) (s : Repair D f) : Repair D (.then e f) :=
  ⟨fun st =>
    let a := r.run st
    let b := s.run a.state
    { b with residuals := a.residuals ++ b.residuals,
             inspected := a.inspected ++ b.inspected,
             transportRefusals := a.transportRefusals ++ b.transportRefusals }⟩

/-- Interpret a first-class edit path using the landed incremental repair. -/
def Repair.ofChange {w v : World E} : (e : Change E w v) → Repair D e
  | .stay w => .identity w
  | .edit w e => .atomic w e
  | .then e f => (Repair.ofChange e).compose (Repair.ofChange f)

/-- Resume the retained state through another edit, using the same incremental machinery. -/
def Residual.resume (r : Residual D E) (e : Edit E) : Result D (e.apply r.world) :=
  (Repair.atomic r.world e).run ⟨r.closure⟩

/-- From-scratch semantics, at any world, of the retained problem and candidates. -/
def analyze (w : World E) (cl : Closure D E) : List (List Status) :=
  observe (fromScratch w cl.tpl fun u => (cl.slot u).cands)

/-- Cost and intent are selection preferences. The existing budget remains a hard check. -/
structure Policy (D : CalculusData) where
  eligible : Candidate D → Bool
  cost : Candidate D → Nat

def Policy.cheapest : Policy D := ⟨fun _ => true, Candidate.cost⟩

/-- Minimum policy cost among CURRENTLY verified eligible candidates. Leftmost wins ties. -/
def choose (policy : Policy D) (I : Iface D E) (w : World E) :
    List (Candidate D) → Nat → Option (Candidate D × Nat)
  | [], _ => none
  | c :: cs, n =>
    let rest := choose policy I w cs (n + 1)
    if policy.eligible c && isVerified (judge I w c) then
      match rest with
      | none => some (c, n)
      | some (d, j) => if policy.cost c ≤ policy.cost d then some (c, n) else some (d, j)
    else rest

inductive SelectionRefusal where
  | base (reason : Refusal)
  | noEligibleCandidate

/-- Selection delegates authority, history and the fresh final judgment to the landed select. -/
def select (policy : Policy D) (w : World E) (p : Party) (u : Nat) (cl : Closure D E) :
    Except SelectionRefusal (Closure D E × Nat) :=
  match cl.find u with
  | none => .error (.base .unknownHole)
  | some I =>
    match choose policy I w (cl.slot u).cands 0 with
    | none => .error .noEligibleCandidate
    | some (_, i) =>
      match Nanodregg.Lang.Contextual.select w p u i cl with
      | .error reason => .error (.base reason)
      | .ok cl' => .ok (cl', i)

/-- No source hypothesis dependency is silently dropped by a representation change.
The destination contributes its own hypothesis dependencies when judged. -/
def Correspondence.image (q : Correspondence D E) (c : Candidate D) (cost : Nat) : Candidate D :=
  { c with filling := q.forward c.filling, supports := effSupports q.source c,
           cost := cost }

/-- Offer a transported filling; never mutate a template or bypass chooser/accepted history.
Equivalence is checked by certificate lookup (Registry.Sound); destination admission is fresh.
The caller supplies the proposed new cost, which is checked against the target's hard budget. -/
def transport (registry : Registry D E) (certificate : Nat) (w : World E)
    (c : Candidate D) (cost : Nat) : Except TransportRefusal (Outcome D E) :=
  match registry certificate with
  | none => .error .unknownCertificate
  | some q =>
    if D.check q.source.ctx c.filling q.source.ty = false then .error .sourceIllTyped
    else
      let d := q.image c cost
      let st := judge q.target w d
      if st = .verified then
        .ok (.transported ⟨certificate, q, c, { d with status := st }⟩)
      else .error (.destination st)

/-- Attach a certificate-checked transport offer to a repair value at its destination world.
Like replacement, this is an offer, not an automatic rewrite of the template/selection.
A failed offer is retained by name; a successful one carries the sixth outcome in the result. -/
def Repair.withTransport {w v : World E} {e : Change E w v} (r : Repair D e)
    (registry : Registry D E) (certificate : Nat) (c : Candidate D) (cost : Nat) : Repair D e :=
  ⟨fun st =>
    let result := r.run st
    match transport registry certificate v c cost with
    | .error reason => { result with transportRefusals := result.transportRefusals ++ [reason] }
    | .ok outcome =>
      { result with residuals := result.residuals ++ [⟨v, result.state.closure, [outcome]⟩] }⟩

end Nanodregg.Lang.Contextual.RepairObjects
