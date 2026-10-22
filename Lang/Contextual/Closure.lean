/-
# Lang.Contextual.Closure — the guarded contextual closure `(P, Ω, σ, D, support, Φ, t)`

The object of ACTIVITIES-PROPOSAL doc 2 §9, over an ABSTRACT calculus (its data `CalculusData` here, its laws
`CalculusLaws` in the proof module), so the theory
does not wait on a particular CMTT core. Instances: the CMTT core's `cmttLaws`
(`Lang/Proofs/Contextual/CoreInstance.lean`) and the deployed language's `langLaws`
(`Lang/Proofs/Contextual/LangInstance.lean`).

Limits, stated: fillings are typed in the EMPTY meta-context (`HasTy [] Ψ M A`: no hole inside a
hole's filling); supports are one level (tokens, never another hole's selection), so a support cycle
is not expressible here; an environment edit touches every candidate (dependency sets are
sufficient, not minimal).

* `P, Ω` — the retained `Template`: a term typed under an open interface of holes `u :: [Ψ ⊢ A]`,
  each with its guard, budget, hypothesis tokens and POLARITY (`chooser`, `acceptor`). Kept apart
  from every environment: resubstitution needs it.
* `σ` — `Closure.sigma`: the current partial meta-substitution, the selected filling per hole.
* `D` — the selected candidate per hole (`Slot.selected`): WHICH derivation stands behind `σ`. Two
  candidates with one filling and different supports are one `σ` and two `D`s (provenance `ab + c`).
* `support` — `Closure.support`: the tokens the selected candidates rely on (`effSupports`: the
  declared supports plus the hypothesis tokens of every context variable the filling USES).
* `Φ` — `Closure.Φ`: residual obligations (derived from the statuses) plus `owed` (established by
  the accepted history and never derived away).
* `t` — `Closure.hist`: the accepted interaction history, append-only.

A candidate's status is computed by ONE function, `judge`, from the hole's checker and guard, the
world's environment and the liveness of the candidate's dependencies; the status is never the
proposer's opinion. Assumption tokens are immutable and versioned (`Token`); a world says which are
live. Withdrawal is a liveness change: it can suspend, it never refutes (`conflict` is reachable
only from the checker and the guard, which read no token).
-/

import Lang.Contextual.HoleDecl

namespace Nanodregg.Lang.Contextual

/-! ## The abstract calculus -/

/-- The DATA of a contextual calculus the closure theory uses (its laws, with the typing relation,
are `Lang.Proofs.Contextual.Closure.CalculusLaws`). -/
structure CalculusData where
  Ty : Type
  Ctx : Type
  Tm : Type
  tmEq : DecidableEq Tm
  /-- Simultaneous meta-substitution `⟦σ⟧P` for a PARTIAL `σ` (unfilled holes stay). -/
  msubst : (Nat → Option Tm) → Tm → Tm
  /-- The checker: a proposed filling acquires authority only through it. -/
  check : Ctx → Tm → Ty → Bool
  /-- `uses M x`: the filling mentions hypothesis `x` of its context (free-variable occurrence). -/
  uses : Tm → Nat → Bool
  /-- The context without hypothesis `x`. -/
  drop : Ctx → Nat → Ctx
  /-- Strengthening `t ≡ t₀[π]`: `strengthen x t` is `t₀`, `weaken x` is `π`. -/
  strengthen : Nat → Tm → Tm
  weaken : Nat → Tm → Tm
  /-- The variable term for hypothesis `x`. -/
  var : Nat → Tm
  /-- The type a context gives hypothesis `x`, if it has one. -/
  lookup : Ctx → Nat → Option Ty

instance (D : CalculusData) : DecidableEq D.Tm := D.tmEq

/-! ## Assumption tokens and worlds -/

/-- An immutable, versioned assumption. Re-using an id at a new version is a NEW token: the
proposition a token stands for never changes. -/
structure Token where
  id : Nat
  ver : Nat
deriving DecidableEq, Repr

/-- A world: which tokens are live, and the guard environment (dependent-context parameters). -/
structure World (E : Type) where
  live : Token → Bool
  env : E

variable {E : Type}

def World.set (w : World E) (t : Token) (b : Bool) : World E :=
  { w with live := fun t' => if t' = t then b else w.live t' }

/-- A primitive change of world. -/
inductive Edit (E : Type) where
  | withdraw (t : Token)
  | assert (t : Token)
  | setEnv (e : E)

def Edit.apply : Edit E → World E → World E
  | .withdraw t, w => w.set t false
  | .assert t, w => w.set t true
  | .setEnv e, w => { w with env := e }

/-- Re-issue an id at a new version: the old token is withdrawn and a fresh one asserted. -/
def reissue (id old new : Nat) : List (Edit E) := [.withdraw ⟨id, old⟩, .assert ⟨id, new⟩]

def applyAll : List (Edit E) → World E → World E
  | [], w => w
  | e :: es, w => applyAll es (e.apply w)

/-! ## Holes, candidates, statuses -/

abbrev Party := Nat

/-- A hole's interface: its declaration, the hypotheses of its context backed by tokens, its guard
(the hole's own admissibility condition: the CHECKER of a candidate belongs to the hole, never to the
candidate), its cost budget, and its polarity. -/
structure Iface (D : CalculusData) (E : Type) where
  name : Nat
  ctx : D.Ctx
  ty : D.Ty
  hyps : List (Nat × Token)
  /-- Every token-backed hypothesis is a real hypothesis of the hole's context. -/
  hyps_real : ∀ h ∈ hyps, (D.lookup ctx h.1).isSome = true
  guard : E → D.Tm → Bool
  budget : Nat
  chooser : Party
  acceptor : Party

def Iface.decl {D : CalculusData} (I : Iface D E) : HoleDecl D.Ctx D.Ty := ⟨I.name, I.ctx, I.ty⟩

/-- Checked contrary evidence about ONE candidate (never about the hole). -/
inductive Evidence where
  | illTyped
  | guardFails
deriving DecidableEq, Repr

inductive Status where
  | verified
  /-- the listed supports are not live: what would have to be re-established -/
  | suspended (missing : List Token)
  /-- the listed blockers are live: the retained exclusion argument -/
  | pruned (by_ : List Token)
  | conflict (ev : Evidence)
  /-- correct, but its declared cost exceeds the hole's budget -/
  | uncovered (cost budget : Nat)
deriving DecidableEq, Repr

inductive Obligation where
  /-- hole `u` needs a (new) verified filling -/
  | refill (u : Nat)
  /-- candidate `i` of hole `u` waits on token `t` -/
  | support (u i : Nat) (t : Token)
  /-- the executed selection `i` of hole `u` must be settled -/
  | settle (u i : Nat)
  /-- the executed selection `i` of hole `u` lost its justification after execution -/
  | reconcile (u i : Nat)
deriving DecidableEq, Repr

/-- A retained candidate filling. `status` is the RECORDED status (the last judgment). -/
structure Candidate (D : CalculusData) where
  filling : D.Tm
  supports : List Token
  blockers : List Token
  cost : Nat
  by_ : Party
  status : Status

structure Slot (D : CalculusData) where
  cands : List (Candidate D)
  selected : Option Nat
  accepted : Bool

def Slot.empty {D : CalculusData} : Slot D := ⟨[], none, false⟩

inductive Event where
  | proposed (u i : Nat)
  | selected (u i : Nat)
  | deselected (u : Nat)
  | accepted (u i : Nat)
  | pruned (u i : Nat)
  | rederived (u i : Nat)
deriving DecidableEq, Repr

/-- The typed repair outcomes for one hole. The proposal's four are `replacement`, `strengthening`,
`alternative`, `suspended`; `kept` (the selected candidate stands, nothing to repair) is the fifth
case a total repair function needs. -/
inductive Outcome (D : CalculusData) where
  | kept (u : Nat)
  /-- `σ' = σ[u ↦ M]`: a verified candidate `j` with a DIFFERENT filling, offered to the chooser -/
  | replacement (u j : Nat) (M : D.Tm)
  /-- hypothesis `x` left the hole's context; the selected filling factors as `t₀[π]` -/
  | strengthening (u x : Nat) (t₀ : D.Tm)
  /-- the same filling through another derivation `j`: `σ` unchanged, `D` changed (applied) -/
  | alternative (u j : Nat)
  | suspended (u : Nat) (Φ : List Obligation)

inductive Refusal where
  | unknownHole
  | notChooser
  | notAcceptor
  | noCandidate
  | notVerified (s : Status)
  | accepted
  | notSelected
deriving DecidableEq, Repr

/-! ## The template and the closure -/

structure Template (D : CalculusData) (E : Type) where
  Γ : D.Ctx
  T : D.Ty
  P : D.Tm
  Ω : List (Iface D E)
  names : (Ω.map Iface.name).Nodup

structure Closure (D : CalculusData) (E : Type) where
  tpl : Template D E
  slot : Nat → Slot D
  owed : List Obligation
  hist : List Event

variable {D : CalculusData}

/-! ## Judgment -/

/-- The supports a candidate relies on: declared, plus the token of every hypothesis it uses. -/
def effSupports (I : Iface D E) (c : Candidate D) : List Token :=
  c.supports ++ (I.hyps.filter fun h => D.uses c.filling h.1).map Prod.snd

/-- Everything a candidate's status reads from the token world. -/
def deps (I : Iface D E) (c : Candidate D) : List Token := effSupports I c ++ c.blockers

/-- THE judgment of a candidate at a world. -/
def judge (I : Iface D E) (w : World E) (c : Candidate D) : Status :=
  if D.check I.ctx c.filling I.ty = false then .conflict .illTyped
  else if I.guard w.env c.filling = false then .conflict .guardFails
  else if (c.blockers.filter w.live).isEmpty = false then .pruned (c.blockers.filter w.live)
  else if ((effSupports I c).filter fun t => !w.live t).isEmpty = false then
    .suspended ((effSupports I c).filter fun t => !w.live t)
  else if c.cost ≤ I.budget then .verified else .uncovered c.cost I.budget

/-- The provenance polynomial of a hole at a world: one monomial (a product of tokens) per candidate
that passes everything but its supports; the hole is justified iff some monomial is all live. -/
def provenance (I : Iface D E) (env : E) (cs : List (Candidate D)) :
    List (List Token × List Token) :=
  (cs.filter fun c => D.check I.ctx c.filling I.ty && I.guard env c.filling &&
      decide (c.cost ≤ I.budget)).map fun c => (effSupports I c, c.blockers)

/-- Does the edit touch what the candidate's status reads? (Sufficient, not minimal: an
environment change touches every candidate.) -/
def touches : Edit E → Iface D E → Candidate D → Bool
  | .withdraw t, I, c => decide (t ∈ deps I c)
  | .assert t, I, c => decide (t ∈ deps I c)
  | .setEnv _, _, _ => true

/-- The context hypothesis an edit withdraws from a hole, if any. -/
def hypOf : Edit E → Iface D E → Option Nat
  | .withdraw t, I => (I.hyps.find? fun h => decide (h.2 = t)).map Prod.fst
  | _, _ => none

def holeTouched (e : Edit E) (I : Iface D E) (s : Slot D) : Bool :=
  (hypOf e I).isSome || s.cands.any (touches e I)

/-! ## The seven-tuple's derived components -/

def Closure.find (cl : Closure D E) (u : Nat) : Option (Iface D E) :=
  cl.tpl.Ω.find? fun I => I.name == u

def Closure.selectedCand (cl : Closure D E) (u : Nat) : Option (Candidate D) :=
  match (cl.slot u).selected with
  | some i => (cl.slot u).cands[i]?
  | none => none

/-- `σ`: the current partial substitution. -/
def Closure.sigma (cl : Closure D E) (u : Nat) : Option D.Tm :=
  (cl.selectedCand u).map Candidate.filling

/-- `support`: the tokens behind the selected candidates. -/
def Closure.support (cl : Closure D E) : List Token :=
  cl.tpl.Ω.flatMap fun I => match cl.selectedCand I.name with
    | some c => effSupports I c
    | none => []

/-- The obligations a hole's current state leaves open. -/
def holeObligations (u : Nat) (s : Slot D) : List Obligation :=
  match s.selected with
  | none => [.refill u]
  | some i => match s.cands[i]? with
    | some c => match c.status with
      | .verified => []
      | .suspended ms => ms.map (.support u i)
      | _ => [.refill u]
    | none => [.refill u]

/-- `Φ`: the residual obligations, then those the accepted history owes. -/
def Closure.Φ (cl : Closure D E) : List Obligation :=
  (cl.tpl.Ω.flatMap fun I => holeObligations I.name (cl.slot I.name)) ++ cl.owed

/-- The OBSERVABLE of a closure: the recorded status of every retained candidate, hole by hole,
in order. (Not the selection, which is history-dependent; not the history.) -/
def observe (cl : Closure D E) : List (List Status) :=
  cl.tpl.Ω.map fun I => (cl.slot I.name).cands.map Candidate.status

/-! ## Operations -/

def Closure.update (cl : Closure D E) (u : Nat) (s : Slot D) : Nat → Slot D :=
  fun v => if v = u then s else cl.slot v

/-- Propose a candidate (anyone): retained, judged at `w`, never selected by proposing. -/
def propose (w : World E) (u : Nat) (c : Candidate D) (cl : Closure D E) :
    Except Refusal (Closure D E × Nat) :=
  match cl.find u with
  | none => .error .unknownHole
  | some I =>
    let s := cl.slot u
    let i := s.cands.length
    .ok ({ cl with slot := cl.update u { s with cands := s.cands ++ [{ c with status := judge I w c }] },
                   hist := cl.hist ++ [.proposed u i] }, i)

/-- Select candidate `i` (chooser only, before acceptance, and only if it judges `verified` NOW:
the recorded status is never trusted). -/
def select (w : World E) (p : Party) (u i : Nat) (cl : Closure D E) : Except Refusal (Closure D E) :=
  match cl.find u with
  | none => .error .unknownHole
  | some I =>
    let s := cl.slot u
    if p ≠ I.chooser then .error .notChooser
    else if s.accepted then .error .accepted
    else match s.cands[i]? with
      | none => .error .noCandidate
      | some c =>
        let st := judge I w c
        if st = .verified then
          .ok { cl with slot := cl.update u { s with cands := s.cands.set i { c with status := st },
                                                     selected := some i },
                        hist := cl.hist ++ [.selected u i] }
        else .error (.notVerified st)

/-- Fill = propose, then select it, atomically (chooser). -/
def fill (w : World E) (p : Party) (u : Nat) (c : Candidate D) (cl : Closure D E) :
    Except Refusal (Closure D E) :=
  match propose w u c cl with
  | .error r => .error r
  | .ok (cl₁, i) => select w p u i cl₁

/-- Deselect (chooser, before acceptance): the candidates are RETAINED. -/
def deselect (p : Party) (u : Nat) (cl : Closure D E) : Except Refusal (Closure D E) :=
  match cl.find u with
  | none => .error .unknownHole
  | some I =>
    let s := cl.slot u
    if p ≠ I.chooser then .error .notChooser
    else if s.accepted then .error .accepted
    else .ok { cl with slot := cl.update u { s with selected := none },
                       hist := cl.hist ++ [.deselected u] }

/-- Accept (acceptor): the selected candidate must judge `verified` now; the acceptance is
executed history and owes a settlement. -/
def accept (w : World E) (p : Party) (u : Nat) (cl : Closure D E) : Except Refusal (Closure D E) :=
  match cl.find u with
  | none => .error .unknownHole
  | some I =>
    let s := cl.slot u
    if p ≠ I.acceptor then .error .notAcceptor
    else if s.accepted then .error .accepted
    else match s.selected with
      | none => .error .notSelected
      | some i => match s.cands[i]? with
        | none => .error .noCandidate
        | some c =>
          if judge I w c = .verified then
            .ok { cl with slot := cl.update u { s with accepted := true },
                          owed := cl.owed ++ [.settle u i],
                          hist := cl.hist ++ [.accepted u i] }
          else .error (.notVerified (judge I w c))

/-- Prune (chooser): record the REASON as a blocker token; the candidate is pruned exactly while
that token is live. -/
def prune (w : World E) (p : Party) (u i : Nat) (reason : Token) (cl : Closure D E) :
    Except Refusal (Closure D E) :=
  match cl.find u with
  | none => .error .unknownHole
  | some I =>
    let s := cl.slot u
    if p ≠ I.chooser then .error .notChooser
    else if s.accepted = true ∧ s.selected = some i then .error .accepted
    else match s.cands[i]? with
      | none => .error .noCandidate
      | some c =>
        let c' := { c with blockers := c.blockers ++ [reason] }
        .ok { cl with slot := cl.update u { s with cands := s.cands.set i { c' with status := judge I w c' } },
                      hist := cl.hist ++ [.pruned u i] }

/-- Re-judge one candidate (anyone): a judgment, not an interaction; the history does not grow. -/
def rejudge (w : World E) (u i : Nat) (cl : Closure D E) : Closure D E :=
  match cl.find u with
  | none => cl
  | some I =>
    let s := cl.slot u
    match s.cands[i]? with
    | none => cl
    | some c => { cl with slot := cl.update u { s with cands := s.cands.set i { c with status := judge I w c } } }

/-! ## Repair -/

/-- The first element satisfying `p`, with its index (offset by `n`). -/
def findIx {α : Type} (p : α → Bool) : List α → Nat → Option (α × Nat)
  | [], _ => none
  | a :: as, n => if p a then some (a, n) else findIx p as (n + 1)

/-- Re-judge exactly the touched candidates at the new world `w'`; carry the rest. -/
def repairPass (w' : World E) (e : Edit E) (I : Iface D E) :
    List (Candidate D) → Nat → List (Candidate D) × List Nat
  | [], _ => ([], [])
  | c :: cs, n =>
    if touches e I c then
      ({ c with status := judge I w' c } :: (repairPass w' e I cs (n + 1)).1,
       n :: (repairPass w' e I cs (n + 1)).2)
    else (c :: (repairPass w' e I cs (n + 1)).1, (repairPass w' e I cs (n + 1)).2)

/-- The re-judged candidate list (one pass; the same pass logs what it re-judged). -/
def repairCands (w' : World E) (e : Edit E) (I : Iface D E) (cs : List (Candidate D)) :
    List (Candidate D) :=
  (repairPass w' e I cs 0).1

/-- The indices that pass re-judged. -/
def rejudgedIn (w' : World E) (e : Edit E) (I : Iface D E) (s : Slot D) : List Nat :=
  if holeTouched e I s = false then [] else (repairPass w' e I s.cands 0).2

def suspendObligations (u : Nat) (cs : List (Candidate D)) : List Obligation :=
  .refill u :: (cs.zipIdx.flatMap fun ci => match ci.1.status with
    | .suspended ms => ms.map (.support u ci.2)
    | _ => [])

def isVerified (s : Status) : Bool := decide (s = .verified)

/-- The selected candidate still judges `verified`: kept, or strengthened past a withdrawn
hypothesis of the hole's context. -/
def keptOutcome (e : Edit E) (I : Iface D E) (c : Candidate D) : Outcome D :=
  match hypOf e I with
  | some x => .strengthening I.name x (D.strengthen x c.filling)
  | none => .kept I.name

/-- The selected candidate `i` (filling of `c`) lost its justification and was not executed: the
same filling through another derivation is APPLIED (`σ` unchanged); a different filling is only
OFFERED (the chooser selects); otherwise the hole is suspended with its obligations. -/
def reselect (I : Iface D E) (i : Nat) (c : Candidate D) (cs : List (Candidate D)) :
    Option Nat × Outcome D :=
  match findIx (fun d => isVerified d.status && decide (d.filling = c.filling)) cs 0 with
  | some (_, j) => (some j, .alternative I.name j)
  | none => match findIx (fun d => isVerified d.status) cs 0 with
    | some (d, j) => (some i, .replacement I.name j d.filling)
    | none => (some i, .suspended I.name (suspendObligations I.name cs))

/-- Repair the selection `i` of a hole over its re-judged candidates `cs`. -/
def repairSelected (e : Edit E) (I : Iface D E) (accepted : Bool) (i : Nat)
    (cs : List (Candidate D)) : Option Nat × Option (Outcome D) :=
  match cs[i]? with
  | none => (some i, none)
  | some c =>
    if isVerified c.status then (some i, some (keptOutcome e I c))
    else if accepted then (some i, some (.suspended I.name [.reconcile I.name i]))
    else ((reselect I i c cs).1, some (reselect I i c cs).2)

/-- Repair one hole after edit `e` (new world `w'`): re-judge the touched candidates, then repair
the selection. An untouched hole is returned as it was, with no outcome. -/
def repairHole (w' : World E) (e : Edit E) (I : Iface D E) (s : Slot D) : Slot D × Option (Outcome D) :=
  if holeTouched e I s = false then (s, none)
  else match s.selected with
    | none => ({ s with cands := repairCands w' e I s.cands }, none)
    | some i =>
      ({ s with cands := repairCands w' e I s.cands,
                selected := (repairSelected e I s.accepted i (repairCands w' e I s.cands)).1 },
       (repairSelected e I s.accepted i (repairCands w' e I s.cands)).2)

def Outcome.event : Outcome D → Option Event
  | .alternative u j => some (.rederived u j)
  | _ => none

/-- Repair the closure after edit `e` at world `w`: the repaired closure, the outcomes, and the
log `(hole, index)` of every candidate the pass re-judged. -/
def repair (w : World E) (e : Edit E) (cl : Closure D E) :
    Closure D E × List (Outcome D) × List (Nat × Nat) :=
  let w' := e.apply w
  let outs := cl.tpl.Ω.filterMap fun I => (repairHole w' e I (cl.slot I.name)).2
  ({ cl with slot := fun u => match cl.find u with
                | some I => (repairHole w' e I (cl.slot u)).1
                | none => cl.slot u,
             hist := cl.hist ++ outs.filterMap Outcome.event }, outs,
   cl.tpl.Ω.flatMap fun I => (rejudgedIn w' e I (cl.slot I.name)).map fun k => (I.name, k))

/-- Withdraw a token: a world edit, then repair. -/
def withdraw (w : World E) (t : Token) (cl : Closure D E) :
    Closure D E × List (Outcome D) × List (Nat × Nat) :=
  repair w (.withdraw t) cl

/-- The from-scratch reference: the template and the retained candidates, every status judged
at `w`, nothing selected, no history. -/
def fromScratch (w : World E) (tpl : Template D E) (cands : Nat → List (Candidate D)) : Closure D E :=
  { tpl := tpl
    slot := fun u => match tpl.Ω.find? (fun I => I.name == u) with
      | some I => ⟨(cands u).map fun c => { c with status := judge I w c }, none, false⟩
      | none => ⟨cands u, none, false⟩
    owed := []
    hist := [] }

/-- Every operation on a closure, at one world (`edit` changes the world and repairs). -/
inductive Op (D : CalculusData) (E : Type) where
  | propose (u : Nat) (c : Candidate D)
  | select (p : Party) (u i : Nat)
  | fill (p : Party) (u : Nat) (c : Candidate D)
  | deselect (p : Party) (u : Nat)
  | accept (p : Party) (u : Nat)
  | prune (p : Party) (u i : Nat) (reason : Token)
  | rejudge (u i : Nat)
  | edit (e : Edit E)

def Op.run (w : World E) : Op D E → Closure D E → Except Refusal (Closure D E)
  | .propose u c, cl => (Nanodregg.Lang.Contextual.propose w u c cl).map Prod.fst
  | .select p u i, cl => Nanodregg.Lang.Contextual.select w p u i cl
  | .fill p u c, cl => Nanodregg.Lang.Contextual.fill w p u c cl
  | .deselect p u, cl => Nanodregg.Lang.Contextual.deselect p u cl
  | .accept p u, cl => Nanodregg.Lang.Contextual.accept w p u cl
  | .prune p u i r, cl => Nanodregg.Lang.Contextual.prune w p u i r cl
  | .rejudge u i, cl => .ok (Nanodregg.Lang.Contextual.rejudge w u i cl)
  | .edit e, cl => .ok (Nanodregg.Lang.Contextual.repair w e cl).1

/-- The world after an operation: `edit e` moves it, every other operation keeps it. -/
def Op.next (w : World E) : Op D E → World E
  | .edit e => e.apply w
  | _ => w

/-- A session: operations in order, the world threaded through (`edit e` moves it to
`e.apply w`); the first refusal stops the session and is returned by name. -/
def Session.run : List (Op D E) → World E × Closure D E → Except Refusal (World E × Closure D E)
  | [], st => .ok st
  | op :: ops, (w, cl) => match op.run w cl with
    | .error r => .error r
    | .ok cl' => Session.run ops (op.next w, cl')

/-! ## Boundaries and stability -/

/-- A consumer relying on hole `hole` only through the exported projection `proj`. -/
structure Consumer (D : CalculusData) (V : Type) where
  hole : Nat
  proj : D.Tm → V
  ok : V → Bool

def Consumer.holds {V : Type} (k : Consumer D V) (cl : Closure D E) : Bool :=
  match cl.sigma k.hole with
  | some M => k.ok (k.proj M)
  | none => false

/-! ## Support closure: least fixpoint versus counting (experiment 4) -/

structure Rule where
  head : Nat
  body : List Nat

/-- Bounded iteration of the immediate-consequence operator from the facts. -/
def lfpIter (R : List Rule) (F : Nat → Bool) : Nat → Nat → Bool
  | 0, x => F x
  | n + 1, x => lfpIter R F n x || R.any fun r => r.head == x && r.body.all (lfpIter R F n)

/-- The number of supports of `x` in the alive set `A`: its fact, plus every rule firing in `A`. -/
def supportCount (R : List Rule) (F : Nat → Bool) (A : Nat → Bool) (x : Nat) : Nat :=
  (if F x then 1 else 0) + (R.filter fun r => r.head == x && r.body.all A).length

/-- Naive COUNTING maintenance: starting from the old alive set, an atom dies only when its count of
supports among the currently alive atoms reaches zero. -/
def countRun (R : List Rule) (F : Nat → Bool) (A : Nat → Bool) : Nat → Nat → Bool
  | 0 => A
  | n + 1 => fun x => countRun R F A n x && decide (0 < supportCount R F (countRun R F A n) x)

end Nanodregg.Lang.Contextual

/-- A retained candidate filling, with its last recorded judgment.
The positive supports and negative blockers follow Doyle's support-list (SL) justifications,
IN-list and OUT-list: A Truth Maintenance System, Artificial Intelligence 12 (1979), pp.231–272.
These are one-level versioned tokens; the closure does not implement Doyle's recursive TMS. -/
add_decl_doc Nanodregg.Lang.Contextual.Candidate
