/- The boundary declaration: four independent observations, with explicit failed obligations.
This is a demonstration Mini can take; no wire or existing judgment changes. -/
import Lang.Contextual.Closure

namespace Nanodregg.Lang.Contextual

inductive Observation where
  | typingInterface
  | logicalContract
  | observableBehavior
  | costGuarantee
deriving DecidableEq, Repr

def Observation.all : List Observation :=
  [.typingInterface, .logicalContract, .observableBehavior, .costGuarantee]

/-- The powerset lattice: demanding cost does not imply demanding a particular behavior. -/
abbrev Declaration := Observation → Bool

def Declaration.meet (a b : Declaration) : Declaration := fun o => a o && b o
def Declaration.join (a b : Declaration) : Declaration := fun o => a o || b o
def Declaration.bottom : Declaration := fun _ => false
def Declaration.top : Declaration := fun _ => true

/-- A boundary belongs to a concrete hole interface. The behavior projection specifies exactly
what downstream caches may observe. The cost promise is separate from admission's budget. -/
structure Boundary (D : CalculusData) (E V : Type) where
  iface : Iface D E
  declares : Declaration
  behavior : E → D.Tm → V
  costBound : Nat

def Observation.Value (V : Type) : Observation → Type
  | .observableBehavior => V
  | _ => Bool

instance {V : Type} [DecidableEq V] (o : Observation) :
    DecidableEq (o.Value V) := by cases o <;> simp only [Observation.Value] <;> infer_instance

def Boundary.read {D : CalculusData} {E V : Type} (b : Boundary D E V)
    (w : World E) (c : Candidate D) : (o : Observation) → o.Value V
  | .typingInterface => D.check b.iface.ctx c.filling b.iface.ty
  | .logicalContract => b.iface.guard w.env c.filling
  | .observableBehavior => b.behavior w.env c.filling
  | .costGuarantee => decide (c.cost ≤ b.costBound)

/-- A failed declaration propagates an obligation bearing the hole name AND observation.
The old observation is retained as the reference, never overwritten by the repair's answer. -/
def Boundary.failures {D : CalculusData} {E V : Type} [DecidableEq V]
    (b : Boundary D E V) (w w' : World E) (c c' : Candidate D) : List Observation :=
  Observation.all.filter fun o => b.declares o && !decide (b.read w c o = b.read w' c' o)

/-- Inspect the actual selections after a repair/chooser session. An absent filling cannot
re-establish a declaration; all its promised observations remain obligations. -/
def Boundary.obligations {D : CalculusData} {E V : Type} [DecidableEq V]
    (b : Boundary D E V) (w w' : World E) (cl cl' : Closure D E) : List (Nat × Observation) :=
  let failed := match cl.selectedCand b.iface.name, cl'.selectedCand b.iface.name with
    | some c, some c' => b.failures w w' c c'
    | _, _ => Observation.all.filter b.declares
  failed.map fun o => (b.iface.name, o)

namespace BoundarySearch

/-- A small executable search calculus, not an encoding of deployed Lang terms.
The constructors denote actual algorithms below, not arbitrary supplied answers/costs. -/
inductive Term where
  | binary
  | linear
  | var (n : Nat)
  | hole (n : Nat)
deriving DecidableEq, Repr

def data : CalculusData where
  Ty := Unit
  Ctx := List Unit
  Tm := Term
  tmEq := inferInstance
  msubst σ t := match t with | .hole n => (σ n).getD t | _ => t
  check Γ t _ := match t with
    | .binary | .linear => true
    | .var n => (Γ[n]?).isSome
    | .hole _ => false
  uses t n := match t with | .var m => m == n | _ => false
  drop Γ n := Γ.eraseIdx n
  strengthen n t := match t with | .var m => .var (if m < n then m else m - 1) | _ => t
  weaken n t := match t with | .var m => .var (if m < n then m else m + 1) | _ => t
  var := .var
  lookup Γ n := Γ[n]?

structure Input where
  xs : List Nat
  key : Nat
deriving DecidableEq, Repr

/-- One step is one key probe (equality plus direction); not elapsed time or list traversal. -/
def linear (key : Nat) : List Nat → Bool × Nat
  | [] => (false, 0)
  | x :: xs =>
    if key = x then (true, 1)
    else let r := linear key xs; (r.1, r.2 + 1)

/-- Bounded binary search; fuel exhaustion is distinct from a negative membership answer. -/
def binary : Nat → List Nat → Nat → Option (Bool × Nat)
  | 0, _, _ => none
  | fuel + 1, xs, key =>
    if xs.isEmpty then some (false, 0)
    else
      let mid := xs.length / 2
      let x := xs.getD mid 0
      if key = x then some (true, 1)
      else
        let rest := if key < x then xs.take mid else xs.drop (mid + 1)
        (binary fuel rest key).map fun r => (r.1, r.2 + 1)

def run (i : Input) : Term → Option (Bool × Nat)
  | .binary => binary (i.xs.length + 1) i.xs i.key
  | .linear => some (linear i.key i.xs)
  | _ => none

def membership (i : Input) (t : Term) : Bool :=
  match run i t with
  | some r => r.1 == i.xs.contains i.key
  | none => false

def sortedToken : Token := ⟨20, 0⟩
def exclusionToken : Token := ⟨21, 0⟩

def input : Input := ⟨[0, 1, 2, 3, 4, 5, 6, 7], 7⟩
def world : World Input := ⟨fun t => t == sortedToken || t == exclusionToken, input⟩

/-- Admission allows the linear fallback. A separate boundary promises four probes for eight
elements (1 + log2 8); that promise must be reopened when the fallback takes eight. -/
def iface : Iface data Input :=
  { name := 0, ctx := [], ty := (), hyps := [], hyps_real := by simp,
    guard := membership, budget := 8, chooser := 1, acceptor := 2 }

def template : Template data Input :=
  { Γ := [], T := (), P := .hole 0, Ω := [iface], names := by decide }

def candidate (t : Term) (supports : List Token) : Candidate data :=
  { filling := t, supports := supports, blockers := [],
    cost := ((run input t).map Prod.snd).getD 9, by_ := 3, status := .suspended [] }

def boundary : Boundary data Input (Option Bool) :=
  { iface := iface, declares := Declaration.top,
    behavior := fun i t => (run i t).map Prod.fst, costBound := 4 }

def start : Closure data Input := fromScratch world template fun _ => []

def before : Except Refusal (World Input × Closure data Input) :=
  Session.run [.propose 0 (candidate .binary [sortedToken]),
    .propose 0 (candidate .linear []), .select 1 0 0] (world, start)

def after : Except Refusal (World Input × Closure data Input) :=
  before.bind fun st => Session.run [.edit (.withdraw sortedToken), .select 1 0 1] st

def observations : Except Refusal (World Input × Closure data Input) →
    Option (List (List Status) × Option Nat × Option Bool)
  | .error _ => none
  | .ok st => some (observe st.2, (st.2.slot 0).selected,
      (st.2.sigma 0).bind fun t => (run st.1.env t).map Prod.fst)

def boundaryReport : Option (List (Nat × Observation)) := do
  let old ← before.toOption
  let new ← after.toOption
  pure (boundary.obligations old.1 new.1 old.2 new.2)

/-- A successful answer with an empty support trace, beside an excluded alternative. -/
def prunedSession : Except Refusal (World Input × Closure data Input) :=
  Session.run [.propose 0 (candidate .linear []), .select 1 0 0,
    .propose 0 (candidate .binary []), .prune 1 0 1 exclusionToken] (world, start)

def pruningReport : Option (List Token × List (Nat × Nat) × List (List Status)) := do
  let st ← prunedSession.toOption
  let repaired := repair st.1 (.withdraw exclusionToken) st.2
  pure (st.2.support, repaired.2.2, observe repaired.1)

end BoundarySearch
end Nanodregg.Lang.Contextual
