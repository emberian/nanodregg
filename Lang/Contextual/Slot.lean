/-
# Lang.Contextual.Slot — a hole resolved when it is reached, from candidates under live supports

The calculus in `Lang.Contextual.Protocol` fills a hole by a substitution chosen before anything is
observed, and its interpreter stops `stuck` at a hole. A program that runs against a World decides
later: when the run reaches the hole, it looks at the World and takes a candidate whose supports hold
there. This module adds that.

A SLOT is a set of candidates. Each candidate cites SUPPORTS (facts a view can be asked about) and must
pass a JUDGE (the interface contract, independent of the view). A slot may hold a STORED selection. At a
view the selection is USABLE when it passes the judge and every support it cites holds; otherwise it is
BLOCKED, and the read names exactly the supports that do not hold. Stored and usable are different
things: a stored selection stays stored while it is blocked, and a read says which it is.

`slot_repair` is the one repair theorem. A selection is usable at a view iff every support it cites
holds there. A blocked read names every dead support of the selection and nothing else. A support that
is PERMANENT (false once means false at every later view of the World: a retired cell, an answered
ring) keeps the selection blocked, by that name, at every later view. And a candidate whose supports
hold is usable the moment it is selected: the repair changes the selection and nothing else of the slot.

`interp` runs a protocol whose holes a RESOLVER fills when reached; a resolver may refuse, and the run
then ends `withdrawn` with the resolver's reason. `Slot.resolve` is the resolver a slot gives.
-/
import Lang.Contextual.Protocol

namespace Nanodregg.Lang.Contextual.Slot

open Nanodregg.Lang.Contextual.Protocol

/-- A slot over candidates `Cand` whose supports are facts `Fact`. -/
structure Slot (Fact Cand : Type) where
  /-- the facts a candidate cites -/
  supports : Cand → List Fact
  /-- the contract every filling must pass, whatever the view -/
  judge : Cand → Bool

section
variable {Fact Cand : Type}

/-- The supports of `c` that do not hold. -/
def Slot.dead (S : Slot Fact Cand) (holds : Fact → Bool) (c : Cand) : List Fact :=
  (S.supports c).filter fun f => !holds f

/-- Every support of `c`, with whether it holds: the evidence a read shows. -/
def Slot.evidence (S : Slot Fact Cand) (holds : Fact → Bool) (c : Cand) : List (Fact × Bool) :=
  (S.supports c).map fun f => (f, holds f)

/-- `c` passes the judge and every support it cites holds. -/
def Slot.usable (S : Slot Fact Cand) (holds : Fact → Bool) (c : Cand) : Bool :=
  S.judge c && (S.dead holds c).isEmpty

/-- The candidates usable at the view, in order. -/
def Slot.alternatives (S : Slot Fact Cand) (holds : Fact → Bool) (cands : List Cand) : List Cand :=
  cands.filter (S.usable holds)

/-- What a read of a slot's stored selection says. -/
inductive Reading (Fact Cand : Type)
  /-- nothing is selected -/
  | empty
  /-- the selection fails the judge -/
  | rejected (c : Cand)
  /-- the selection is usable; every support it cites, each holding -/
  | usable (c : Cand) (evidence : List (Fact × Bool))
  /-- the selection is stored but not usable; the supports that do not hold, by name -/
  | blocked (c : Cand) (dead : List Fact)

/-- Read a stored selection at a view. -/
def Slot.read (S : Slot Fact Cand) (holds : Fact → Bool) : Option Cand → Reading Fact Cand
  | none => .empty
  | some c =>
    if S.judge c then
      match S.dead holds c with
      | [] => .usable c (S.evidence holds c)
      | d => .blocked c d
    else .rejected c

theorem dead_eq_nil_iff (S : Slot Fact Cand) (holds : Fact → Bool) (c : Cand) :
    S.dead holds c = [] ↔ ∀ f ∈ S.supports c, holds f = true := by
  simp [Slot.dead, List.filter_eq_nil_iff]

theorem mem_dead_iff (S : Slot Fact Cand) (holds : Fact → Bool) (c : Cand) (f : Fact) :
    f ∈ S.dead holds c ↔ f ∈ S.supports c ∧ holds f = false := by
  simp [Slot.dead, List.mem_filter]

theorem usable_iff (S : Slot Fact Cand) (holds : Fact → Bool) (c : Cand) :
    S.usable holds c = true ↔ S.judge c = true ∧ ∀ f ∈ S.supports c, holds f = true := by
  simp [Slot.usable, List.isEmpty_iff, dead_eq_nil_iff]

/-- A read is usable iff the selection passes the judge and every support it cites holds. -/
theorem read_usable_iff (S : Slot Fact Cand) (holds : Fact → Bool) (c : Cand) :
    (∃ ev, S.read holds (some c) = .usable c ev) ↔ S.usable holds c = true := by
  rw [usable_iff]
  unfold Slot.read
  by_cases hj : S.judge c = true
  · simp only [hj, if_true, true_and]
    rw [← dead_eq_nil_iff]
    cases h : S.dead holds c with
    | nil => exact ⟨fun _ => rfl, fun _ => ⟨_, rfl⟩⟩
    | cons f d => simp
  · simp [hj]

/-- A blocked read names every support of the selection that does not hold, and nothing else, and
names at least one. -/
theorem read_blocked_names (S : Slot Fact Cand) (holds : Fact → Bool) {c c' : Cand} {d : List Fact}
    (h : S.read holds (some c) = .blocked c' d) :
    c' = c ∧ d ≠ [] ∧ ∀ f, f ∈ d ↔ f ∈ S.supports c ∧ holds f = false := by
  unfold Slot.read at h
  by_cases hj : S.judge c = true
  · simp only [hj, if_true] at h
    cases hd : S.dead holds c with
    | nil => simp [hd] at h
    | cons f t =>
      simp only [hd, Reading.blocked.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨rfl, List.cons_ne_nil _ _, fun g => by rw [← hd, mem_dead_iff]⟩
  · simp [hj] at h

/-- A support is PERMANENT along a relation of views when, false at a view, it is false at every view
the relation reaches from it. -/
def Permanent {V : Type} (holdsAt : V → Fact → Bool) (later : V → V → Prop) (f : Fact) : Prop :=
  ∀ v v', later v v' → holdsAt v f = false → holdsAt v' f = false

/-- The ONE repair theorem.
(1) A stored selection is usable at a view iff it passes the judge and every support it cites holds.
(2) A blocked read names exactly the dead supports of the selection, at least one.
(3) A dead PERMANENT support keeps the selection blocked, by that name, at every later view.
(4) A candidate that is usable at the view reads usable as soon as it is selected, with its evidence;
    the slot (its supports and its judge) is the same slot: nothing is reinstalled. -/
theorem slot_repair {V : Type} (S : Slot Fact Cand) (holdsAt : V → Fact → Bool)
    (later : V → V → Prop) (v : V) (c : Cand) :
    ((∃ ev, S.read (holdsAt v) (some c) = .usable c ev) ↔
        S.judge c = true ∧ ∀ f ∈ S.supports c, holdsAt v f = true) ∧
    (∀ c' d, S.read (holdsAt v) (some c) = .blocked c' d →
        d ≠ [] ∧ ∀ f, f ∈ d ↔ f ∈ S.supports c ∧ holdsAt v f = false) ∧
    (∀ f, f ∈ S.supports c → holdsAt v f = false → Permanent holdsAt later f →
        ∀ v', later v v' → S.judge c = true →
          ∃ d, S.read (holdsAt v') (some c) = .blocked c d ∧ f ∈ d) ∧
    (∀ c', S.usable (holdsAt v) c' = true →
        S.read (holdsAt v) (some c') = .usable c' (S.evidence (holdsAt v) c')) := by
  refine ⟨(read_usable_iff S _ c).trans (usable_iff S _ c), ?_, ?_, ?_⟩
  · intro c' d h
    exact (read_blocked_names S _ h).2
  · intro f hf hdead hperm v' hv' hj
    have hf' : holdsAt v' f = false := hperm v v' hv' hdead
    have hmem : f ∈ S.dead (holdsAt v') c := (mem_dead_iff S _ c f).2 ⟨hf, hf'⟩
    unfold Slot.read
    simp only [hj, if_true]
    cases hd : S.dead (holdsAt v') c with
    | nil => rw [hd] at hmem; cases hmem
    | cons g t => exact ⟨g :: t, rfl, hd ▸ hmem⟩
  · intro c' hu
    have ⟨hj, hall⟩ := (usable_iff S _ c').1 hu
    have hd : S.dead (holdsAt v) c' = [] := (dead_eq_nil_iff S _ c').2 hall
    unfold Slot.read
    simp [hj, hd]

end

/-! ## Resolution when a hole is reached -/

section
variable {Ix : Type} {S : Sig Ix} {Hole : Ix → Type} {A : Ix → Type}

/-- How a run with resolved holes ends: a result, or WITHDRAWN at a hole its resolver refused, with
the resolver's reason (for a slot: the dead supports, by name), or out of the static bound on how
many holes one run may resolve. -/
inductive Out (Hole : Ix → Type) (A : Ix → Type) (W : Type) where
  | done (j : Ix) (a : A j)
  | withdrawn (j : Ix) (h : Hole j) (why : W)
  | bound (j : Ix) (h : Hole j)

/-- The algebra of one run in a monad: a call is performed by `call` and the run goes on with its
response; a hole is `hole`'s. -/
def runAlg {M : Type → Type} [Monad M] {W : Type}
    (call : {i : Ix} → (op : S.Op i) → M (S.Resp op))
    (hole : {i : Ix} → Hole i → M (Out Hole A W)) :
    Algebra S Hole A (fun _ => M (Out Hole A W)) where
  ret := fun {i} a => pure (.done i a)
  call := fun op k => do let r ← call op; k r
  hole := hole

/-- Run an open protocol in a monad: each call is performed by `call`; each hole is filled when it is
reached by `resolve`, which may refuse. `n` bounds the depth of holes one run resolves (a filling may
itself hold holes). -/
def interp {M : Type → Type} [Monad M] {W : Type}
    (call : {i : Ix} → (op : S.Op i) → M (S.Resp op))
    (resolve : {i : Ix} → Hole i → Except W (Prot S Hole A i)) :
    Nat → {i : Ix} → Prot S Hole A i → M (Out Hole A W)
  | 0 => fold (runAlg call fun {i} h => pure (.bound i h))
  | n + 1 => fold (runAlg call fun {i} h => match resolve h with
    | .ok f => interp call resolve n f
    | .error w => pure (.withdrawn i h w))

/-- Every path of a run with resolved holes: the calls with their responses, and how it ends. `n`
is the depth bound, as `interp`'s. -/
inductive RunsR {W : Type} (resolve : {i : Ix} → Hole i → Except W (Prot S Hole A i)) :
    Nat → {i : Ix} → Prot S Hole A i → Trace S → Out Hole A W → Prop
  | ret {n : Nat} {i : Ix} (a : A i) : RunsR resolve n (.ret a) [] (.done i a)
  | call {n : Nat} {i : Ix} {op : S.Op i} {k : (r : S.Resp op) → Prot S Hole A (S.next op r)}
      {tr : Trace S} {o : Out Hole A W} (r : S.Resp op) :
      RunsR resolve n (k r) tr o → RunsR resolve n (.call op k) (⟨i, op, r⟩ :: tr) o
  | bound {i : Ix} (h : Hole i) : RunsR resolve 0 (.hole h) [] (.bound i h)
  | fill {n : Nat} {i : Ix} {h : Hole i} {f : Prot S Hole A i} {tr : Trace S} {o : Out Hole A W} :
      resolve h = .ok f → RunsR resolve n f tr o → RunsR resolve (n + 1) (.hole h) tr o
  | withdraw {n : Nat} {i : Ix} {h : Hole i} {w : W} :
      resolve h = .error w → RunsR resolve (n + 1) (.hole h) [] (.withdrawn i h w)

/-- A hole whose resolver refuses ends the run there, with the reason, and performs nothing. -/
theorem runsR_withdrawn {W : Type} {resolve : {i : Ix} → Hole i → Except W (Prot S Hole A i)}
    {n : Nat} {i : Ix} {h : Hole i} {w : W} (hw : resolve h = .error w) {tr : Trace S}
    {o : Out Hole A W} (hr : RunsR resolve (n + 1) (.hole h) tr o) :
    tr = [] ∧ o = .withdrawn i h w := by
  cases hr with
  | fill hf _ => rw [hw] at hf; cases hf
  | withdraw hw' => rw [hw] at hw'; cases hw'; exact ⟨rfl, rfl⟩

end

/-! ## The resolver a slot gives -/

section
variable {Fact Cand : Type} {Ix : Type} {S : Sig Ix} {Hole : Ix → Type} {A : Ix → Type}

/-- Why a slot refuses to fill: for each candidate it considered, the candidate and its dead supports
(empty when it failed the judge instead). -/
abbrev Refusal (Fact Cand : Type) := List (Cand × List Fact)

/-- A slot's resolution at a view: the first usable candidate in the chooser's order, its body as the
filling; or the refusal naming, for every candidate, what failed. -/
def Slot.resolve (Sl : Slot Fact Cand) (holds : Fact → Bool) {i : Ix}
    (body : Cand → Prot S Hole A i) (order : List Cand) :
    Except (Refusal Fact Cand) (Prot S Hole A i) :=
  match Sl.alternatives holds order with
  | c :: _ => .ok (body c)
  | [] => .error (order.map fun c => (c, Sl.dead holds c))

/-- A slot fills only with a usable candidate of the chooser's order, the first one: the filling is
the body of the head of the usable candidates. -/
theorem resolve_ok {Sl : Slot Fact Cand} {holds : Fact → Bool} {i : Ix}
    {body : Cand → Prot S Hole A i} {order : List Cand} {f : Prot S Hole A i}
    (h : Sl.resolve holds body order = .ok f) :
    ∃ c rest, Sl.alternatives holds order = c :: rest ∧ c ∈ order ∧ Sl.usable holds c = true ∧
      f = body c := by
  unfold Slot.resolve at h
  cases ha : Sl.alternatives holds order with
  | nil => rw [ha] at h; cases h
  | cons c rest =>
    rw [ha] at h
    cases h
    have hc : c ∈ order.filter (Sl.usable holds) := by
      show c ∈ Sl.alternatives holds order; rw [ha]; exact List.mem_cons_self
    rw [List.mem_filter] at hc
    exact ⟨c, rest, rfl, hc.1, hc.2, rfl⟩

/-- A slot refuses only when no candidate in the chooser's order is usable, and the refusal names,
for each, exactly its dead supports. -/
theorem resolve_error {Sl : Slot Fact Cand} {holds : Fact → Bool} {i : Ix}
    {body : Cand → Prot S Hole A i} {order : List Cand} {w : Refusal Fact Cand}
    (h : Sl.resolve holds body order = .error w) :
    (∀ c ∈ order, Sl.usable holds c = false) ∧ w = order.map fun c => (c, Sl.dead holds c) := by
  unfold Slot.resolve at h
  cases ha : Sl.alternatives holds order with
  | cons c rest => rw [ha] at h; cases h
  | nil =>
    rw [ha] at h
    cases h
    refine ⟨fun c hc => ?_, rfl⟩
    have : c ∉ order.filter (Sl.usable holds) := by
      show c ∉ Sl.alternatives holds order; rw [ha]; simp
    simpa [List.mem_filter, hc] using this

end

end Nanodregg.Lang.Contextual.Slot
