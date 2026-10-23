/- Checked-Environment projection for the certificate pin (Census/Certificate.lean, decisions/gates.md GATES-20u).
Encoding and reference collection use a shared-node DAG: expanding proof sharing with Repr can require gigabytes.
Trusted read-offs, none proved: encodeExpr/expression/declaration (field coverage, reference extraction and
encoding injectivity), Lean.Environment.checked/find?, ExprStructEq, core Repr/JSON. -/
import Lean

namespace Census.Certificate

open Lean

deriving instance Repr for ReducibilityHints, QuotKind

structure Expression where
  encoded : String
  constants : List Name

structure Encoding where
  seen : Std.HashMap ExprStructEq Nat := {}
  nodes : Array Json := #[]
  constants : List Name := []

/-- Structural cache equality includes binder names/metadata; hash equality alone never suffices.
This executable traversal, Lean.Expr.equal and serialization are named trusted read-offs. -/
def encodeExpr (e : Expr) : StateM Encoding Nat := do
  if let some i := (← get).seen.get? (ExprStructEq.mk e) then return i
  let row ← match e with
    | .bvar i => pure #[toJson "bvar", toJson i]
    | .fvar i => pure #[toJson "fvar", toJson (reprStr i)]
    | .mvar i => pure #[toJson "mvar", toJson (reprStr i)]
    | .sort l => pure #[toJson "sort", toJson (reprStr l)]
    | .const n ls => do
      modify fun s => {s with constants := n :: s.constants}
      pure #[toJson "const", toJson (reprStr n), toJson (reprStr ls)]
    | .app f a => do
      let fi ← encodeExpr f
      let ai ← encodeExpr a
      pure #[toJson "app", toJson fi, toJson ai]
    | .lam n t b bi | .forallE n t b bi => do
      let ti ← encodeExpr t
      let bi' ← encodeExpr b
      pure #[toJson (if e.isLambda then "lam" else "forall"),
        toJson (reprStr n), toJson ti, toJson bi', toJson (reprStr bi)]
    | .letE n t v b nd => do
      let ti ← encodeExpr t
      let vi ← encodeExpr v
      let bi ← encodeExpr b
      pure #[toJson "let", toJson (reprStr n), toJson ti, toJson vi, toJson bi, toJson nd]
    | .lit l => pure #[toJson "lit", toJson (reprStr l)]
    | .mdata md b => do
      let bi ← encodeExpr b
      pure #[toJson "mdata", toJson (reprStr md), toJson bi]
    | .proj n i b => do
      modify fun s => {s with constants := n :: s.constants}
      let bi ← encodeExpr b
      pure #[toJson "proj", toJson (reprStr n), toJson i, toJson bi]
  let i := (← get).nodes.size
  modify fun s => {s with seen := s.seen.insert ⟨e⟩ i, nodes := s.nodes.push (.arr row)}
  return i
termination_by e

def expression (e : Expr) : Expression :=
  let (root, s) := (encodeExpr e).run {}
  ⟨(Json.mkObj [("root", toJson root), ("nodes", .arr s.nodes)]).compress,
    s.constants.eraseDups⟩

structure Declaration where
  type : Expression
  payload : String
  dependencies : List Name
  theoremKind : Bool

/-- Every ConstantInfo variant retains its constructor fields. Type and values are encoded DAGs.
`dependencies` are the values' constants and the shape edges (an inductive's mutual block and constructors, a
constructor's inductive, a recursor's rules); for a theorem, exactly the constants its proof term references. -/
def declaration (ci : ConstantInfo) : Declaration :=
  let ty := expression ci.type
  let values := (ci.value? true).toList.map expression
  let rules : List (RecursorRule × Expression) := match ci with
    | .recInfo v => v.rules.map (fun r => (r, expression r.rhs))
    | _ => []
  let (tag, shape, edges) : String × Json × List Name := match ci with
    | .axiomInfo v => ("axiom", toJson v.isUnsafe, [])
    | .defnInfo v => ("definition", toJson [reprStr v.hints, reprStr v.safety, reprStr v.all], [])
    | .thmInfo v => ("theorem", toJson (reprStr v.all), [])
    | .opaqueInfo v => ("opaque", toJson [reprStr v.isUnsafe, reprStr v.all], [])
    | .quotInfo v => ("quotient", toJson (reprStr v.kind), [])
    | .inductInfo v => ("inductive",
        toJson [reprStr v.numParams, reprStr v.numIndices, reprStr v.all, reprStr v.ctors,
          reprStr v.numNested, reprStr v.isRec, reprStr v.isUnsafe, reprStr v.isReflexive],
        v.all ++ v.ctors)
    | .ctorInfo v => ("constructor",
        toJson [reprStr v.induct, reprStr v.cidx, reprStr v.numParams, reprStr v.numFields,
          reprStr v.isUnsafe], [v.induct])
    | .recInfo v => ("recursor",
        Json.mkObj [("shape", toJson [reprStr v.all, reprStr v.numParams, reprStr v.numIndices,
          reprStr v.numMotives, reprStr v.numMinors, reprStr v.k, reprStr v.isUnsafe]),
          ("rules", toJson (rules.map fun (r, e) =>
            toJson [reprStr r.ctor, reprStr r.nfields, e.encoded]))],
        v.all ++ rules.flatMap (fun (r, e) => r.ctor :: e.constants))
  let payload := (Json.mkObj [("kind", toJson tag), ("name", toJson (reprStr ci.name)),
    ("levels", toJson (reprStr ci.levelParams)), ("type", toJson ty.encoded),
    ("values", toJson (values.map Expression.encoded)), ("shape", shape)]).compress
  ⟨ty, payload, (values.flatMap Expression.constants ++ edges).eraseDups, ci.isTheorem⟩

/-- The reader: a constant's projected declaration in the checked kernel environment (what `collectAxioms`
reads), not pending elaborator data. -/
def lookup (env : Environment) (n : Name) : Option Declaration :=
  (env.checked.get.find? n).map declaration

end Census.Certificate
