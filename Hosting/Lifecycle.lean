/-
# Hosting.Lifecycle — the lifecycle of a hosted grain: one edge list, and the machine it defines

A grain (an SPK app or a hosted resident, decisions/hosting.md HOSTING-2) is an ordinary World
object whose state holds the phase its owner DESIRES. What the operator's box observes (a pid, an
exit) is never World state (HOSTING-4). `edges` is the single source: `step` is read off it, and
the grain package's law and methods (`Hosting.Package`) are generated from it, with
`Hosting.Proofs.Lifecycle` relating each to `step`.

There is no `absent` phase: birth is KERNEL's `create`, which judges `old = new = seed`, so the one
pair a law admits that is not an edge is the born pair `installed → installed` (`bornOk`). `remove`
leads to the terminal `removed`; the kernel never retires a programmed object by method
(KERNEL-17: nothing is pruned), so a removed grain is a cell the controller treats as absent.

One METHOD per event (index = `Event.index`, the `n` of KERNEL's `Right.invoke n`): an owner can
grant an operator `invoke:1` (start) and nothing else.
-/

namespace Nanodregg.Hosting

inductive Phase | installed | removed | running | stopped
  deriving DecidableEq, Repr

inductive Event | start | stop | remove
  deriving DecidableEq, Repr

namespace Phase
def all : List Phase := [.installed, .removed, .running, .stopped]

/-- The phase's label in the package's state type (ascending, as LANG's rows must be). -/
def label : Phase → String
  | .installed => "installed" | .removed => "removed" | .running => "running" | .stopped => "stopped"
end Phase

namespace Event
/-- In method order (the package's methods sorted by label, `Std.pkgOf`): `remove` is method 0,
`start` 1, `stop` 2. -/
def all : List Event := [.remove, .start, .stop]

def label : Event → String
  | .start => "start" | .stop => "stop" | .remove => "remove"

/-- The method index KERNEL's `Body.invoke` and `Right.invoke` name. -/
def index : Event → Nat
  | .remove => 0 | .start => 1 | .stop => 2
end Event

/-- THE lifecycle: (from, event, to). Nothing else is an edge. -/
def edges : List (Phase × Event × Phase) :=
  [(.installed, .remove, .removed),
   (.installed, .start, .running),
   (.running, .stop, .stopped),
   (.stopped, .remove, .removed),
   (.stopped, .start, .running)]

/-- The phase event `e` leads to from `p`, if `(p, e, _)` is an edge. -/
def step (p : Phase) (e : Event) : Option Phase :=
  (edges.find? fun x => x.1 == p && x.2.1 == e).map (·.2.2)

/-- The phase a grain is born in. -/
def initial : Phase := .installed

/-- The pair a birth may write: `old = new = seed`, so only the initial phase. -/
def bornOk (p q : Phase) : Bool := p == initial && q == initial

/-- What the grain's phase law admits for `old.phase`, the event the new state records (`none`:
born), and `new.phase`. -/
def admits (p : Phase) : Option Event → Phase → Bool
  | none, q => bornOk p q
  | some e, q => step p e == some q

/-- What a method computes: the edge's target, or the phase unchanged. The law refuses the latter
because `step` is `none` there (`Proofs.Lifecycle.target_admitted_iff`); that the phase then does
not move is `target_moves_iff`, which needs `edges_irreflexive`. -/
def target (p : Phase) (e : Event) : Phase := (step p e).getD p

end Nanodregg.Hosting
