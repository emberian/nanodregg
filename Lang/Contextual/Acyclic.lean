/- A separate finite adapter: rank-witnessed hole unrolling, not fixed-point semantics.
Stein–Chang–Sridharan (PLDI 2021), §4 and §6: keep dependencies acyclic.
The output is precisely the finite token carrier returned by Closure.provenance. -/
import Lang.Contextual.Closure

namespace Nanodregg.Lang.Contextual.Acyclic

abbrev Polynomial := List (List Token × List Token)

/-- Joint requirements distribute over alternatives; both token polarities survive. -/
def product (p q : Polynomial) : Polynomial :=
  p.flatMap fun a => q.map fun b => (a.1 ++ b.1, a.2 ++ b.2)

/-- Hole references are in a finite, closed namespace. Token negation remains in leaves. -/
inductive Expr (n : Nat) where
  | tokens (p : Polynomial)
  | hole (i : Fin n)
  | alt (a b : Expr n)
  | joint (a b : Expr n)
deriving DecidableEq

def Expr.refs {n : Nat} : Expr n → List (Fin n)
  | .tokens _ => []
  | .hole i => [i]
  | .alt a b | .joint a b => a.refs ++ b.refs

def Expr.expand {n : Nat} (lookup : Fin n → Polynomial) : Expr n → Polynomial
  | .tokens p => p
  | .hole i => lookup i
  | .alt a b => a.expand lookup ++ b.expand lookup
  | .joint a b => product (a.expand lookup) (b.expand lookup)

/-- Ranks are supplied data and checked, never trusted proof fields. Distinct unrolled
iterations use distinct Fin names; no equality of iterates is taken as a fixed point. -/
structure Graph (n : Nat) where
  body : Fin n → Expr n
  rank : Fin n → Nat

def Graph.edges {n : Nat} (g : Graph n) : List (Fin n × Fin n) :=
  (List.finRange n).flatMap fun i => ((g.body i).refs.map fun j => (i, j))

inductive Refusal where
  | fixedPointDependency (hole : Nat)
  | rankNotDecreasing (consumer dependency : Nat)
deriving DecidableEq, Repr

/-- Check the whole supplied graph, including undemanded and zero-valued branches.
The first failed edge retains its endpoint names in the refusal. -/
def validate {n : Nat} (g : Graph n) : Option Refusal :=
  (g.edges.find? fun e => decide (g.rank e.1 ≤ g.rank e.2)).map fun e =>
    if e.1 = e.2 then .fixedPointDependency e.1.val
    else .rankNotDecreasing e.1.val e.2.val

/-- Finite expansion stages. Stage zero is only an internal approximation;
adapt checks ranks before using a stage proven sufficient for the demanded hole. -/
def unroll {n : Nat} (g : Graph n) : Nat → Fin n → Polynomial
  | 0, _ => []
  | k + 1, i => (g.body i).expand (unroll g k)

def adapt {n : Nat} (g : Graph n) (i : Fin n) : Except Refusal Polynomial :=
  match validate g with
  | some reason => .error reason
  | none => .ok (unroll g (g.rank i + 1) i)

end Nanodregg.Lang.Contextual.Acyclic
