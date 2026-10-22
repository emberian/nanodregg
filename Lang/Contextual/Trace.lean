/- Per-candidate verifying traces; a demonstration Mini can take. -/
import Lang.Contextual.Closure

namespace Nanodregg.Lang.Contextual.Trace

variable {D : CalculusData} {K V : Type}

/-- A guard can see only the declared projection, never the ambient environment.
Mokhov–Mitchell–Peyton Jones, ICFP 2018, §4.2.2, pp.79:14–15. -/
structure Guard (D : CalculusData) (K V : Type) where
  reads : D.Tm → List K
  run : D.Tm → List V → Bool

/-- Install the projected guard in the existing interface; other checks are unchanged.
Mokhov et al. 2018, §4.2.2, pp.79:14–15. -/
def Guard.install (g : Guard D K V) (I : Iface D (K → V)) : Iface D (K → V) :=
  { I with guard := fun e t => g.run t ((g.reads t).map e) }

/-- Exact values, not hashes: supports record missing tokens, blockers record live tokens.
Both lists are complete projections, including negative observations; no collision premise.
Mokhov et al. 2018, §4.2.2, pp.79:14–15. -/
structure Snapshot (V : Type) where
  env : List V
  missing : List Token
  blocked : List Token
deriving DecidableEq, Repr

/-- Observe every declared key, every effective support and every blocker.
Mokhov et al. 2018, §4.2.2, pp.79:14–15. -/
def observe (g : Guard D K V) (I : Iface D (K → V)) (w : World (K → V))
    (c : Candidate D) : Snapshot V :=
  ⟨(g.reads c.filling).map w.env,
   (effSupports I c).filter (fun t => !w.live t), c.blockers.filter w.live⟩

/-- The existing judgment factored through its complete finite observation.
Mokhov et al. 2018, Def.3.1 p.79:11 and §4.2.2 pp.79:14–15. -/
def evaluate (g : Guard D K V) (I : Iface D (K → V)) (c : Candidate D)
    (s : Snapshot V) : Status :=
  if D.check I.ctx c.filling I.ty = false then .conflict .illTyped
  else if g.run c.filling s.env = false then .conflict .guardFails
  else if s.blocked.isEmpty = false then .pruned s.blocked
  else if s.missing.isEmpty = false then .suspended s.missing
  else if c.cost ≤ I.budget then .verified else .uncovered c.cost I.budget

/-- Missing observation is not an observed absence. At the package boundary, a pinned-absent
row maps to `some false`, an omitted pin to `none`. Mokhov et al. 2018, §4.2.2 pp.79:14–15. -/
inductive Missing (K : Type) where
  | environment (key : K)
  | token (key : Token)
deriving DecidableEq, Repr

/-- Bounded complete collection; the first omitted read refuses by its key.
Mokhov et al. 2018, §4.2.2 pp.79:14–15. -/
def collect {A B R : Type} (missing : A → R) (read : A → Option B) :
    List A → Except R (List B)
  | [] => .ok []
  | k :: ks =>
    match read k with
    | none => .error (missing k)
    | some v => match collect missing read ks with
      | .error e => .error e
      | .ok vs => .ok (v :: vs)

/-- Coverage comes from the guard declaration and candidate, never from caller-chosen coverage.
All reads finish before any verdict, including on a failing guard.
Mokhov et al. 2018, §4.2.2 pp.79:14–15. -/
def capture (g : Guard D K V) (I : Iface D (K → V)) (c : Candidate D)
    (env : K → Option V) (live : Token → Option Bool) : Except (Missing K) (Snapshot V) := do
  let es ← collect Missing.environment env (g.reads c.filling)
  let ms ← collect Missing.token (fun t => (live t).map fun b => (t, !b)) (effSupports I c)
  let bs ← collect Missing.token (fun t => (live t).map fun b => (t, b)) c.blockers
  pure ⟨es, (ms.filter Prod.snd).map Prod.fst, (bs.filter Prod.snd).map Prod.fst⟩

/-- The package-facing entry point refuses incomplete observations before judging.
This is a checked adapter, not a claim that an existing package calls it.
Mokhov et al. 2018, §4.2.2 pp.79:14–15. -/
def checkedJudge (g : Guard D K V) (I : Iface D (K → V)) (c : Candidate D)
    (env : K → Option V) (live : Token → Option Bool) : Except (Missing K) Status :=
  (capture g I c env live).map (evaluate g I c)

/-- A trace belongs to its candidate. Changed candidate/interface/guard definitions require
reseeding. Mokhov et al. 2018, §4.2.2 pp.79:14–15 (fixed tasks). -/
structure Cached (D : CalculusData) (V : Type) where
  candidate : Candidate D
  trace : Snapshot V

/-- Initialize a coherent cache from the same observation used by its judgment.
Mokhov et al. 2018, §4.2.2 pp.79:14–15. -/
def seed (g : Guard D K V) (I : Iface D (K → V)) (w : World (K → V))
    (c : Candidate D) : Cached D V :=
  let s := observe g I w c
  ⟨{ c with status := evaluate g I c s }, s⟩

/-- Does the new world change this trace? Equal-valued writes do not dirty it.
Mokhov et al. 2018, Def.2.1 p.79:3, §4.2.2 pp.79:14–15. -/
def meets [DecidableEq V] (g : Guard D K V) (I : Iface D (K → V))
    (w : World (K → V)) (c : Cached D V) : Bool :=
  decide (c.trace ≠ observe g I w c.candidate)

/-- Re-evaluate once only in the dirty branch; update the trace even if the status is equal.
Mokhov et al. 2018, §4.2.2 pp.79:14–15. -/
def refresh [DecidableEq V] (g : Guard D K V) (I : Iface D (K → V))
    (w : World (K → V)) (c : Cached D V) : Cached D V :=
  if meets g I w c then seed g I w c.candidate else c

/-- Exact candidate indices inspected and the smaller set whose statuses changed.
Indices distinguish repeated fillings. Mokhov et al. 2018, Def.2.1 p.79:3, §4.2.2 pp.79:14–15. -/
structure Pass (D : CalculusData) (V : Type) where
  entries : List (Cached D V)
  rejudged : List Nat
  changed : List Nat

/-- Structural single traversal: at most one evaluation per retained candidate.
Mokhov et al. 2018, Def.2.1 p.79:3. -/
def repair [DecidableEq V] (g : Guard D K V) (I : Iface D (K → V))
    (w : World (K → V)) : List (Cached D V) → Nat → Pass D V
  | [], _ => ⟨[], [], []⟩
  | c :: cs, n =>
    let c' := refresh g I w c
    let rest := repair g I w cs (n + 1)
    ⟨c' :: rest.entries,
     if meets g I w c then n :: rest.rejudged else rest.rejudged,
     if c'.candidate.status ≠ c.candidate.status then n :: rest.changed else rest.changed⟩

/-- Only holes reading a changed selection status are dirtied; no other dependency is
tracked here. Mokhov et al. 2018, §2.3 p.79:5, §4.2.2 p.79:15. -/
def dirtyReaders (p : Pass D V) (readers : List (Nat × Nat)) : List Nat :=
  (readers.filter fun r => decide (r.2 ∈ p.changed)).map Prod.fst

end Nanodregg.Lang.Contextual.Trace
