/-
Explicit logic certificates for proof-engineering tooling. This is a data/reader interface,
not nano admission and not a new proof checker. An adapter supplies the actual environment
lookup and exact declaration payloads. The generic laws do not prove an adapter's extraction
of references complete; that obligation belongs at the Lean.Environment boundary.
-/
import Std

namespace Census.CertificateReader

/-- Checker and environment identity are part of the certificate, not producer annotations.
Revision and imports must be artifact identities supplied by the checker invocation. -/
structure Checker where
  logic : String
  toolchain : String
  revision : String
  imports : List String
  deriving DecidableEq, Repr

/-- The body remains exact, rather than a pretty-printed declaration or a short digest. -/
structure Entry (Name Body : Type) where
  name : Name
  body : Body
  deriving DecidableEq, Repr

/-- Projection from the destination environment. The adapter must include type/value constants,
projection structures, and inductive/recursor shape dependencies in dependencies. -/
structure Reader (Name Expr Body : Type) where
  lookup : Name → Option Body
  typeOf : Body → Expr
  references : Expr → List Name
  dependencies : Body → List Name
  isAxiom : Body → Bool
  isTheorem : Body → Bool
  checker : Checker

/-- The target is a closed declaration: its full telescope and universes belong to its exact
body/type. A separately instantiated claim needs its own checked target declaration. -/
structure Certificate (Name Expr Body : Type) where
  target : Name
  statement : Expr
  context : List (Entry Name Body)
  assumptions : List Name
  checker : Checker
  deriving DecidableEq, Repr

inductive Refusal
  | checkerMismatch
  | missingTarget
  | notTheorem
  | statementMismatch
  | contextMismatch
  | incompleteContext
  | assumptionsMismatch
  | fuelExhausted
  deriving DecidableEq, Repr

variable {Name Expr Body : Type}

def names (c : Certificate Name Expr Body) : List Name := c.context.map Entry.name

def assumptions (r : Reader Name Expr Body) (ctx : List (Entry Name Body)) : List Name :=
  (ctx.filter fun e => r.isAxiom e.body).map Entry.name

/-- All declaration reads include its type even if the adapter lists only body dependencies. -/
def reads (r : Reader Name Expr Body) (body : Body) : List Name :=
  r.references (r.typeOf body) ++ r.dependencies body

/-- Checking never trusts a success bit or an axiom list supplied by a producer. It compares
all exact bodies with the destination lookup and requires a closed declaration footprint.
Acceptance means faithful reading of that environment, not a foreign-logic interpretation. -/
def accept [DecidableEq Name] [DecidableEq Expr] [DecidableEq Body]
    (r : Reader Name Expr Body) (c : Certificate Name Expr Body) : Except Refusal Unit :=
  if c.checker ≠ r.checker then .error .checkerMismatch else
  match r.lookup c.target with
  | none => .error .missingTarget
  | some target =>
    if r.isTheorem target ≠ true then .error .notTheorem else
    if c.statement ≠ r.typeOf target then .error .statementMismatch else
    if (c.context.any fun e => decide (e.name = c.target ∧ e.body = target)) ≠ true then
      .error .contextMismatch else
    if (c.context.all fun e => decide (r.lookup e.name = some e.body)) ≠ true then
      .error .contextMismatch else
    if ((r.references c.statement ++ c.context.flatMap (fun e => reads r e.body)).all
        fun n => decide (n ∈ names c)) ≠ true then .error .incompleteContext else
    if c.assumptions ≠ assumptions r c.context then .error .assumptionsMismatch else
    .ok ()

/-- Bounded closure extraction. Exhaustion is explicit; an incomplete prefix is never returned
as a certificate. Already visited names do not expand again, including mutual recursion. -/
def gather [DecidableEq Name] (r : Reader Name Expr Body) :
    Nat → List Name → List (Entry Name Body) → Except Refusal (List (Entry Name Body))
  | _, [], seen => .ok seen
  | 0, _ :: _, _ => .error .fuelExhausted
  | fuel + 1, n :: pending, seen =>
    if seen.any (fun e => decide (e.name = n)) then gather r fuel pending seen
    else match r.lookup n with
      | none => .error .missingTarget
      | some body => gather r fuel
          (reads r body ++ pending)
          (seen ++ [⟨n, body⟩])

/-- Produces the whole object, then runs the same destination checker that consumers use.
The reader's source kernel is responsible for the declaration's proof validity. -/
def read [DecidableEq Name] [DecidableEq Expr] [DecidableEq Body]
    (r : Reader Name Expr Body) (fuel : Nat) (target : Name) :
    Except Refusal (Certificate Name Expr Body) :=
  match r.lookup target with
  | none => .error .missingTarget
  | some body =>
    match gather r fuel [target] [] with
    | .error e => .error e
    | .ok ctx =>
      let c := Certificate.mk target (r.typeOf body) ctx (assumptions r ctx) r.checker
      match accept r c with
      | .error e => .error e
      | .ok () => .ok c

end Census.CertificateReader
