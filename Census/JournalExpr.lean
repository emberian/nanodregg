import Lean

/- Exact structural interchange for retained kernel expressions. No pretty-printer parsing,
hash-as-equality, or loss of numeric name components. Metadata is intentionally erased:
kernel checking ignores it. Local metavariables/free variables are incomplete exports. -/
namespace Census.JournalExpr
open Lean

inductive N where
  | anonymous
  | str (parent : N) (s : String)
  | num (parent : N) (n : Nat)
deriving ToJson, FromJson

def N.ofName : Name → N
  | .anonymous => .anonymous
  | .str p s => .str (ofName p) s
  | .num p n => .num (ofName p) n

def N.toName : N → Name
  | .anonymous => .anonymous
  | .str p s => .str p.toName s
  | .num p n => .num p.toName n

inductive L where
  | zero
  | succ (l : L)
  | max (a b : L)
  | imax (a b : L)
  | param (name : N)
deriving ToJson, FromJson

def L.ofLevel : Level → Except String L
  | .zero => pure .zero
  | .succ l => return .succ (← ofLevel l)
  | .max a b => return .max (← ofLevel a) (← ofLevel b)
  | .imax a b => return .imax (← ofLevel a) (← ofLevel b)
  | .param n => pure (.param (.ofName n))
  | .mvar _ => .error "INCOMPLETE COVERAGE: universe metavariable"

def L.toLevel : L → Level
  | .zero => .zero
  | .succ l => .succ l.toLevel
  | .max a b => .max a.toLevel b.toLevel
  | .imax a b => .imax a.toLevel b.toLevel
  | .param n => .param n.toName

inductive Node where
  | bvar (i : Nat)
  | sort (l : L)
  | const (name : N) (levels : List L)
  | app (f a : Nat)
  | lam (n : N) (ty body : Nat) (binder : Nat)
  | forallE (n : N) (ty body : Nat) (binder : Nat)
  | letE (n : N) (ty value body : Nat) (nondep : Bool)
  | natLit (n : Nat)
  | strLit (s : String)
  | proj (name : N) (idx : Nat) (value : Nat)
  | metadata (value : Nat)
deriving ToJson, FromJson

def binderCode : BinderInfo → Nat
  | .default => 0
  | .implicit => 1
  | .strictImplicit => 2
  | .instImplicit => 3

def binderOf : Nat → Except String BinderInfo
  | 0 => pure .default
  | 1 => pure .implicit
  | 2 => pure .strictImplicit
  | 3 => pure .instImplicit
  | _ => .error "INCOMPLETE COVERAGE: invalid binder"

structure Table where
  ids : Std.HashMap Expr Nat := {}
  exprs : Array Expr := #[]

def Table.add (t : IO.Ref Table) (e : Expr) : IO Nat := do
  e.forEach fun x => t.modify fun s =>
    if s.ids.contains x then s else
      { ids := s.ids.insert x s.exprs.size, exprs := s.exprs.push x }
  return (← t.get).ids[e]!

def node (t : Table) (e : Expr) : Except String Node := do
  let id (x : Expr) : Except String Nat :=
    match t.ids[x]? with
    | some n => .ok n
    | none => .error "INCOMPLETE COVERAGE: missing expression child"
  match e with
  | .bvar i => pure (.bvar i)
  | .sort l => return .sort (← L.ofLevel l)
  | .const n ls => return .const (.ofName n) (← ls.mapM L.ofLevel)
  | .app f a => return .app (← id f) (← id a)
  | .lam n ty b bi => return .lam (.ofName n) (← id ty) (← id b) (binderCode bi)
  | .forallE n ty b bi => return .forallE (.ofName n) (← id ty) (← id b) (binderCode bi)
  | .letE n ty v b nd => return .letE (.ofName n) (← id ty) (← id v) (← id b) nd
  | .lit (.natVal n) => pure (.natLit n)
  | .lit (.strVal s) => pure (.strLit s)
  | .proj n i v => return .proj (.ofName n) i (← id v)
  | .mdata _ b => return .metadata (← id b)
  | .mvar _ => .error "INCOMPLETE COVERAGE: metavariable"
  | .fvar _ => .error "INCOMPLETE COVERAGE: free variable"

abbrev Decode := StateT (Std.HashMap Nat Expr) (Except String)

/-- Fuel detects malformed cycles; memoization preserves the expression DAG. -/
def decode (nodes : Array Node) : Nat → Nat → Decode Expr
  | 0, _ => throw "INCOMPLETE COVERAGE: expression cycle/depth"
  | fuel + 1, i => do
    if let some e := (← get)[i]? then return e
    let some n := nodes[i]? | throw "INCOMPLETE COVERAGE: missing expression"
    let d := decode nodes fuel
    let e ← match n with
      | .bvar j => pure (.bvar j)
      | .sort l => pure (.sort l.toLevel)
      | .const n ls => pure (.const n.toName (ls.map L.toLevel))
      | .app f a => return .app (← d f) (← d a)
      | .lam n t b bi => return .lam n.toName (← d t) (← d b) (← binderOf bi)
      | .forallE n t b bi => return .forallE n.toName (← d t) (← d b) (← binderOf bi)
      | .letE n t v b nd => return .letE n.toName (← d t) (← d v) (← d b) nd
      | .natLit j => pure (.lit (.natVal j))
      | .strLit s => pure (.lit (.strVal s))
      | .proj n j v => return .proj n.toName j (← d v)
      | .metadata v => d v
    modify (·.insert i e)
    return e

structure Saved where
  name : N
  levels : List N
  type : Nat
  value : Nat
deriving ToJson, FromJson

end Census.JournalExpr
