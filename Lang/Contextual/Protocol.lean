/-
# Lang.Contextual.Protocol — open protocols as typed families of continuations (lane PROTOCOL)

The object of the activities proposal's document 2: a protocol between parties is an OPEN object.
Its unspecified components are HOLES, each declared in a context `Ω` with an interface (where it
starts, what it must deliver, which reusable facts and which linear tokens it may use, which
obligations it may leave, who chooses its filling and which contract it must pass). Its
interactions with peers are `call op k` nodes whose continuation is a FAMILY indexed by the response
(`k : (r : Resp op) → Prot (next op r)`). A substitution is ONE filling per hole NAME, chosen before
anything is observed. Whether that separates a hole from an interaction depends on the NAMING, not
on the calculus: a template that puts the SAME name in every response branch gets one filling for
all of them (`Proofs.Contextual.Protocol.Coin.no_foresight`), but a template whose hole names
depend on the response (`call op fun r => hole (h r)`) gets a filling per response, which is
foresight (`response_indexed_names_have_foresight`; `foresight_iff_names_separate` is the exact
condition). Scope (one filling into every branch unchanged) is a naming discipline the author
keeps; the calculus does not enforce it. Its resources are tokens a `call` of a consuming operation
spends. The discipline is AFFINE: a token is spent at most once, and a token left unspent at `ret`
is allowed. Its executed prefix is a history (`Hist`), possibly ending in a call
whose reply was lost (`inflight`), and a re-substitution must leave every hole the history has
already entered alone (`Dispatched`).

The shape generalises minidregg's `Theory/IndexedProgram.lean` (restated in Lean core, law 11): its
`IxSignature`/`Program` gain a third constructor `hole`, its `Algebra` a hole case, its interpreter
a `stuck` outcome (doc 2 section 7: partiality visible in the result type). Nano's own free program
over effects (`Hosting.Resident.Prog`) is the instance with a trivial index and no holes
(`Proofs.Contextual.Protocol.nano_runs_iff`, `nano_interp_agrees`).

The judgment `Ω;Γ;Δ ⊢ P : Protocol(i, A) ⊣ Φ` is `HasProt sp Ω Γ Q Φ Δ P`: `Γ` the reusable facts
(hypothetical: derivability is not current availability, `admits`), `Δ` the linear tokens (a bag:
`SubBag`), `Q` the result postcondition, `Φ` the obligations any completion may still owe (an upper
bound). Substitution is SINGLE-PASS: `subst σ` replaces each hole by its filling and does not
substitute into the filling, so a filling's own holes stay open under the same `σ`. Definitions only. The statements (`HasProt`, `Runs`, `Reach`, `Started`, `Dispatched`, `SubBag`,
`Fills`, `SubstOK`, ...) are in `Lang.Proofs.Contextual.ProtocolTyping`; the theorems are in
`Lang.Proofs.Contextual.Protocol` and `Lang.Proofs.Contextual.Negotiation`.
-/

namespace Nanodregg.Lang.Contextual.Protocol

/-! ## Signatures, the accounting of an operation -/

/-- An indexed signature (mini's `IxSignature`, restated): at index `i` the operations `Op i`; each
operation's response type; the response selects the next index. -/
structure Sig (Ix : Type) where
  Op : Ix → Type
  Resp : {i : Ix} → Op i → Type
  next : {i : Ix} → (op : Op i) → Resp op → Ix

/-- What one operation does to the accounts: the linear token it SPENDS (if any), the reusable
facts it REQUIRES (authority, evidence: used, never consumed), and the obligations its DISPATCH
establishes (established when the call leaves, whatever the reply). -/
structure Spec {Ix : Type} (S : Sig Ix) (Tok Fact Ob : Type) where
  consumes : {i : Ix} → S.Op i → Option Tok
  requires : {i : Ix} → S.Op i → List Fact
  establishes : {i : Ix} → S.Op i → List Ob

/-! ## Open protocols -/

/-- The free open protocol over `S` with result family `A` and hole names `Hole`: return a result,
interact (`call`: one continuation per response, at the index the response selects), or leave a
named component unspecified (`hole h`, its interface in the context `Ω`, as a CMTT metavariable
refers to the meta-context). -/
inductive Prot {Ix : Type} (S : Sig Ix) (Hole : Ix → Type) (A : Ix → Type) : Ix → Type where
  | ret {i : Ix} (a : A i) : Prot S Hole A i
  | call {i : Ix} (op : S.Op i) (k : (r : S.Resp op) → Prot S Hole A (S.next op r)) :
      Prot S Hole A i
  | hole {i : Ix} (h : Hole i) : Prot S Hole A i

section
variable {Ix : Type} {S : Sig Ix} {Hole : Ix → Type} {A : Ix → Type}

/-- A hole's interface `u :: [Γ_u; Δ_u ⊢ Protocol(i, post)] ⊣ owes`, with the ROLE that chooses
its filling and an acceptance contract that every filling must pass (`Fills`). The start index is
the hole name's index. `Role` is an index in place of the former `ours | theirs`: a protocol is
judged as one role `me` (`HasProt sp me …`), and every rule tests `chooser = me` or `chooser ≠ me`.
No theorem yet tells two roles other than `me` apart (LANG-75.10). -/
structure Iface (S : Sig Ix) (Hole : Ix → Type) (A : Ix → Type) (Role Tok Fact Ob : Type) (i : Ix) where
  /-- the role that chooses the filling -/
  chooser : Role
  /-- the reusable facts a filling may require (`Γ_u`) -/
  ctx : List Fact
  /-- the tokens a filling may spend (`Δ_u`) -/
  need : List Tok
  /-- what every result a filling delivers satisfies -/
  post : (j : Ix) → A j → Prop
  /-- the obligations a filling may leave -/
  owes : List Ob
  /-- the acceptance contract on a filling -/
  accepts : Prot S Hole A i → Prop

/-- `Ω`: the declared interface of every unresolved component. -/
abbrev Ctx (S : Sig Ix) (Hole : Ix → Type) (A : Ix → Type) (Role Tok Fact Ob : Type) :=
  (i : Ix) → Hole i → Option (Iface S Hole A Role Tok Fact Ob i)

/-- `σ`: a partial substitution, a filling for some holes (doc 2 section 9). -/
abbrev Subst (S : Sig Ix) (Hole : Ix → Type) (A : Ix → Type) :=
  (i : Ix) → Hole i → Option (Prot S Hole A i)

/-- Typed substitution: every hole `σ` fills is replaced by its filling; nothing else moves. -/
def subst (σ : Subst S Hole A) : {i : Ix} → Prot S Hole A i → Prot S Hole A i
  | _, .ret a => .ret a
  | _, .call op k => .call op fun r => subst σ (k r)
  | i, .hole h => match σ i h with
    | some f => f
    | none => .hole h

/-- `σ` restricted to the holes `Ω` declares chosen by `me`: another role's hole is never filled. -/
def Subst.mine {Role Tok Fact Ob : Type} [DecidableEq Role] (me : Role)
    (Ω : Ctx S Hole A Role Tok Fact Ob) (σ : Subst S Hole A) : Subst S Hole A := fun i h =>
  match Ω i h with
  | some I => if I.chooser = me then σ i h else none
  | none => none

/-- `P[σ]` under `Ω`, as role `me`: fill the holes `me` chooses that `σ` names. -/
def fill {Role Tok Fact Ob : Type} [DecidableEq Role] (me : Role) (Ω : Ctx S Hole A Role Tok Fact Ob)
    (σ : Subst S Hole A) {i : Ix} (P : Prot S Hole A i) : Prot S Hole A i :=
  subst (σ.mine me Ω) P

/-- The single substitution `[f/h]`. -/
def Subst.single [DecidableEq Ix] [∀ i, DecidableEq (Hole i)] {i : Ix} (h : Hole i)
    (f : Prot S Hole A i) : Subst S Hole A := fun j h' =>
  if hj : i = j then (by subst hj; exact if h' = h then some f else none) else none

/-- A signature whose response types are finite, listed. -/
structure Finite (S : Sig Ix) where
  resps : {i : Ix} → (op : S.Op i) → List (S.Resp op)
  complete : ∀ {i : Ix} (op : S.Op i) (r : S.Resp op), r ∈ resps op

/-- The holes of `P`, computed over a finite signature (`mem_holes_iff`: exactly `Occurs`). -/
def holes (fin : Finite S) : {i : Ix} → Prot S Hole A i → List (Σ j, Hole j)
  | _, .ret _ => []
  | _, .call op k => (fin.resps op).attach.flatMap fun r => holes fin (k r.1)
  | i, .hole h => [⟨i, h⟩]

/-! ## Linear tokens as a bag -/

/-! ## The judgment `Ω;Γ;Δ ⊢ P : Protocol(i, Q) ⊣ Φ` -/

/-! ## Algebras, fold, fusion -/

/-- An algebra reads an open protocol into an indexed carrier; holes too. -/
structure Algebra (S : Sig Ix) (Hole : Ix → Type) (A : Ix → Type) (C : Ix → Type) where
  ret : {i : Ix} → A i → C i
  call : {i : Ix} → (op : S.Op i) → ((r : S.Resp op) → C (S.next op r)) → C i
  hole : {i : Ix} → Hole i → C i

/-- The fold. -/
def fold {C : Ix → Type} (alg : Algebra S Hole A C) : {i : Ix} → Prot S Hole A i → C i
  | _, .ret a => alg.ret a
  | _, .call op k => alg.call op fun r => fold alg (k r)
  | _, .hole h => alg.hole h

/-- Substitution as an algebra into protocols. -/
def substAlg (σ : Subst S Hole A) : Algebra S Hole A (Prot S Hole A) where
  ret := .ret
  call := .call
  hole := fun {i} h => match σ i h with
    | some f => f
    | none => .hole h

/-- Read a template under an environment: a filled hole is read as its filling's reading, an
unfilled one as the algebra's hole. -/
def underAlg {C : Ix → Type} (alg : Algebra S Hole A C) (σ : Subst S Hole A) :
    Algebra S Hole A C where
  ret := alg.ret
  call := alg.call
  hole := fun {i} h => match σ i h with
    | some f => fold alg f
    | none => alg.hole h

/-! ## Handlers, the interpreter, partial results -/

/-- A deterministic environment: one operation against an indexed state gives a response and a
state at the index the response selects (mini's `Handler`). -/
structure Handler (S : Sig Ix) (St : Ix → Type) where
  handle : {i : Ix} → (op : S.Op i) → St i → Σ r : S.Resp op, St (S.next op r)

/-- How an interpretation ends: a result, or STUCK at an unresolved hole (never a failure). -/
inductive Result (Hole : Ix → Type) (A : Ix → Type) (St : Ix → Type) where
  | done (j : Ix) (a : A j) (s : St j)
  | stuck (j : Ix) (h : Hole j) (s : St j)

/-- The handler as a state-transformer algebra. -/
def execAlgebra {St : Ix → Type} (H : Handler S St) :
    Algebra S Hole A (fun i => St i → Result Hole A St) where
  ret := fun {i} a s => .done i a s
  call := fun op k s => match H.handle op s with
    | ⟨r, s'⟩ => k r s'
  hole := fun {i} h s => .stuck i h s

/-- Run an open protocol against an environment. -/
def interpret {St : Ix → Type} (H : Handler S St) {i : Ix} (P : Prot S Hole A i) :
    St i → Result Hole A St :=
  fold (execAlgebra H) P

/-- Run a template with its holes bound by `σ` in the environment rather than in the syntax. -/
def interpretUnder {St : Ix → Type} (H : Handler S St) (σ : Subst S Hole A) {i : Ix}
    (P : Prot S Hole A i) : St i → Result Hole A St :=
  fold (underAlg (execAlgebra H) σ) P

/-- The recording environment: `H`, and each call appended to a trace with the response it had
(the shape of nano's `recorder`). -/
def record {St : Ix → Type} (H : Handler S St) : Handler S (fun i => St i × List (Σ i, Σ op : S.Op i, S.Resp op)) where
  handle := fun {i} op p => match H.handle op p.1 with
    | ⟨r, s'⟩ => ⟨r, (s', p.2 ++ [⟨i, op, r⟩])⟩

/-! ## History -/

/-- One performed interaction: the operation, at its index, with the response it had. -/
abbrev Entry (S : Sig Ix) := Σ i, Σ op : S.Op i, S.Resp op

/-- A history of performed interactions, in order. -/
abbrev Trace (S : Sig Ix) := List (Entry S)

/-- An accepted history: the answered interactions and, possibly, ONE dispatched call whose reply
has not arrived (lost or late: `uncertain`, a state, never a license to re-plan). -/
structure Hist (S : Sig Ix) where
  answered : Trace S
  inflight : Option (Σ i, S.Op i)

/-- The tokens a trace spends. -/
def consumed {Tok Fact Ob : Type} (sp : Spec S Tok Fact Ob) (t : Trace S) : List Tok :=
  t.filterMap fun e => sp.consumes e.2.1

/-- The obligations a trace established. -/
def established {Tok Fact Ob : Type} (sp : Spec S Tok Fact Ob) (t : Trace S) : List Ob :=
  t.flatMap fun e => sp.establishes e.2.1

/-- The obligations a history established: the answered calls' and the in-flight call's (its
obligation stands from dispatch, whatever happened to the reply). -/
def Hist.established {Tok Fact Ob : Type} (sp : Spec S Tok Fact Ob) (H : Hist S) : List Ob :=
  Protocol.established sp H.answered ++
    match H.inflight with
    | some ⟨_, op⟩ => sp.establishes op
    | none => []

/-! ## The first-class open object (doc 2 section 9) -/

/-- `(me, P, Ω, σ, Γ, Δ, Q, Φ, t)`: the role whose object it is, the retained TEMPLATE, its open
interface, the current partial substitution, the hypotheses and tokens, the result contract, the
obligation bound, and the accepted history. The template is kept apart from `σ`: that is what makes
re-substitution possible. -/
structure Open (S : Sig Ix) (Hole : Ix → Type) (A : Ix → Type) (Role Tok Fact Ob : Type) (i : Ix) where
  me : Role
  template : Prot S Hole A i
  Ω : Ctx S Hole A Role Tok Fact Ob
  σ : Subst S Hole A
  Γ : List Fact
  Δ : List Tok
  Q : (j : Ix) → A j → Prop
  Φ : List Ob
  hist : Hist S

/-- The object's current protocol `P[σ]`. -/
def Open.current {Role Tok Fact Ob : Type} [DecidableEq Role] {i : Ix}
    (O : Open S Hole A Role Tok Fact Ob i) : Prot S Hole A i :=
  fill O.me O.Ω O.σ O.template

/-- Replace the object's partial substitution. Data only: the GUARD (no re-substitution of a hole
the history has entered) is the statement `Open.Replan` in `Lang.Proofs.Contextual.ProtocolTyping`,
a hypothesis of every theorem about a re-plan (`Open.resubst_wf`). -/
def Open.replan {Role Tok Fact Ob : Type} {i : Ix} (O : Open S Hole A Role Tok Fact Ob i)
    (σ' : Subst S Hole A) : Open S Hole A Role Tok Fact Ob i :=
  { O with σ := σ' }

/-! ## Admission: current evidence, separate from derivability -/

/-- The CURRENT admission evidence: which facts hold now, which tokens are unspent now. -/
structure View (Tok Fact : Type) where
  holds : Fact → Bool
  live : Tok → Bool

/-- One concrete effect is admissible now: its facts hold and its token is unspent. -/
def admitOp {Tok Fact Ob : Type} (sp : Spec S Tok Fact Ob) (v : View Tok Fact) {i : Ix}
    (op : S.Op i) : Bool :=
  (sp.requires op).all v.holds &&
    match sp.consumes op with
    | some t => v.live t
    | none => true

/-- The protocol's NEXT concrete effect is admissible now. A hole has no concrete effect to admit
(an unfinished plan describes a family of transitions; only a complete one is admitted). -/
def admits {Tok Fact Ob : Type} (sp : Spec S Tok Fact Ob) (v : View Tok Fact) {i : Ix} :
    Prot S Hole A i → Bool
  | .ret _ => true
  | .call op _ => admitOp sp v op
  | .hole _ => false

/-- Durable consumption: mark a token spent. -/
def View.spend {Tok Fact : Type} [DecidableEq Tok] (v : View Tok Fact) (t : Tok) : View Tok Fact :=
  { v with live := fun t' => if t' = t then false else v.live t' }

/-- Commit one effect: refused unless admissible now; on success its token is spent durably. -/
def commit {Tok Fact Ob : Type} [DecidableEq Tok] (sp : Spec S Tok Fact Ob) (v : View Tok Fact)
    {i : Ix} (op : S.Op i) : Option (View Tok Fact) :=
  if admitOp sp v op then
    some (match sp.consumes op with
      | some t => v.spend t
      | none => v)
  else none

/-- The keys an effect's admission reads: its facts and its token. -/
def opSupport {Tok Fact Ob : Type} (sp : Spec S Tok Fact Ob) {i : Ix} (op : S.Op i) :
    List (Fact ⊕ Tok) :=
  (sp.requires op).map Sum.inl ++ (match sp.consumes op with
    | some t => [Sum.inr t]
    | none => [])

/-- A change of token REPRESENTATION (an authenticated representation of an unchanged semantic
token, e.g. an opening refreshed because a root moved): the spec with every token renamed. -/
def Spec.mapTok {Tok Tok' Fact Ob : Type} (e : Tok → Tok') (sp : Spec S Tok Fact Ob) :
    Spec S Tok' Fact Ob where
  consumes := fun op => (sp.consumes op).map e
  requires := sp.requires
  establishes := sp.establishes

/-- An interface with its tokens renamed. -/
def Iface.mapTok {Role Tok Tok' Fact Ob : Type} (e : Tok → Tok') {i : Ix}
    (I : Iface S Hole A Role Tok Fact Ob i) : Iface S Hole A Role Tok' Fact Ob i :=
  { I with need := I.need.map e }

/-- A context with its tokens renamed. -/
def Ctx.mapTok {Role Tok Tok' Fact Ob : Type} (e : Tok → Tok') (Ω : Ctx S Hole A Role Tok Fact Ob) :
    Ctx S Hole A Role Tok' Fact Ob := fun i h => (Ω i h).map (Iface.mapTok e)

/-- A view as a store of keys. -/
def View.ofStore {Tok Fact : Type} (w : Fact ⊕ Tok → Bool) : View Tok Fact :=
  ⟨fun f => w (.inl f), fun t => w (.inr t)⟩

end

/-! ## Selective repair over fragments (doc 2 section 9, family 3) -/

/-- A checked fragment: a name, the keys its check declares it reads (its support), the check. -/
structure Frag (Name Key V : Type) where
  name : Name
  support : List Key
  check : (Key → V) → Bool

/-- Is the fragment affected by a change of `changed`? -/
def Frag.affected {Name Key V : Type} [DecidableEq Key] (f : Frag Name Key V)
    (changed : List Key) : Bool :=
  f.support.any fun k => decide (k ∈ changed)

/-- Check everything again. -/
def fromScratch {Name Key V : Type} (fs : List (Frag Name Key V)) (w : Key → V) : List Bool :=
  fs.map fun f => f.check w

/-- Selective repair: re-check the affected fragments, reuse every other cached verdict. -/
def repair {Name Key V : Type} [DecidableEq Key] :
    List (Frag Name Key V) → List Bool → List Key → (Key → V) → List Bool
  | [], _, _, _ => []
  | f :: fs, [], ch, w => f.check w :: repair fs [] ch w
  | f :: fs, c :: cs, ch, w => (if f.affected ch then f.check w else c) :: repair fs cs ch w

/-- The names of the fragments that do not check. Each name stands for one residual obligation
(re-establish that fragment); the list is `Φ′` only in that sense. -/
def residual {Name Key V : Type} : List (Frag Name Key V) → List Bool → List Name
  | [], _ => []
  | f :: fs, [] => f.name :: residual fs []
  | f :: fs, b :: bs => (if b then [] else [f.name]) ++ residual fs bs

/-- One effect's admission as a checked fragment over the store of keys. -/
def admitFrag {Ix : Type} {S : Sig Ix} {Name Tok Fact Ob : Type} (sp : Spec S Tok Fact Ob)
    (name : Name) {i : Ix} (op : S.Op i) : Frag Name (Fact ⊕ Tok) Bool where
  name := name
  support := opSupport sp op
  check := fun w => admitOp sp (View.ofStore w) op

/-! ## Example: the committed bit (doc 2 section 5) -/

namespace Coin

/-- Before and after the peer reveals its bit. -/
inductive Phase
  | waiting
  | revealed
deriving DecidableEq, Repr

/-- The only operation: receive the peer's bit; nothing is available afterwards. -/
inductive Op : Phase → Type
  | recv : Op .waiting

def sig : Sig Phase where
  Op := Op
  Resp := fun | .recv => Bool
  next := fun | .recv, _ => .revealed

/-- One hole name, at `revealed`: our answer, planned before the reveal. -/
def HoleN : Phase → Type
  | .waiting => Empty
  | .revealed => Unit

abbrev Res : Phase → Type := fun _ => Bool

abbrev P := Prot sig HoleN Res

/-- The peer answers `b`. -/
def env (b : Bool) : Handler sig (fun _ => Unit) where
  handle := fun | .recv, () => ⟨b, ()⟩

/-- We win against `b` when the run ends with result `b`; a run stuck at a hole loses. The hole
names `Hn` are a parameter so that templates with different naming disciplines can be compared. -/
def wins {Hn : Phase → Type} {i : Phase} (b : Bool) (p : Prot sig Hn Res i) (s : Unit) : Bool :=
  match interpret (env b) p s with
  | .done _ a _ => a == b
  | .stuck _ _ _ => false

/-- The OPEN plan: receive, then do whatever our hole says. Its filling is chosen once. -/
def planHole : P .waiting := .call (S := sig) Op.recv fun _ => .hole (i := Phase.revealed) ()

/-- The RESPONSE-DEPENDENT plan: the continuation is a family over the response. -/
def planCall : P .waiting := .call (S := sig) Op.recv fun b => .ret b

/-- A template whose hole name may depend on the peer's bit: `name b` is the hole in branch `b`.
Response-free naming is the case `name true = name false`. -/
def planNamed {Hn : Phase → Type} (name : Bool → Hn .revealed) : Prot sig Hn Res .waiting :=
  .call (S := sig) Op.recv fun b => .hole (i := Phase.revealed) (name b)

/-- One hole name per possible bit at `revealed`. -/
def HoleB : Phase → Type
  | .waiting => Empty
  | .revealed => Bool

/-- The filling "answer `c`". -/
def answer (c : Bool) : Subst sig HoleN Res := fun
  | .waiting, h => nomatch h
  | .revealed, () => some (.ret c)

/-- The game's two roles: the player whose plan this is, and its peer. -/
inductive Party
  | player
  | peer
deriving DecidableEq, Repr

/-- The hole's interface, chosen by `c` (no facts, tokens or obligations in this game). -/
def iface (c : Party) : Iface sig HoleN Res Party Unit Unit Unit .revealed where
  chooser := c
  ctx := []
  need := []
  post := fun _ _ => True
  owes := []
  accepts := fun _ => True

/-- `Ω` declaring the answer hole chosen by `c`. -/
def ctxOf (c : Party) : Ctx sig HoleN Res Party Unit Unit Unit := fun
  | .waiting, h => nomatch h
  | .revealed, () => some (iface c)

end Coin

/-! ## The integration experiment: a one-use capability, two providers, a deadline, a cancel
(doc 3). Definitions here; the theorems in `Lang.Proofs.Contextual.Negotiation`.
The scalar matchers and the private Negotiation `World` went with PROT-6, replaced by Std.offer's
deployed fuse (`Lang/StdOffer.lean`). -/

namespace Negotiation

/-- The roles: the buyer, whose plan this is, and a provider, who answers `commit`. -/
inductive Party
  | buyer
  | provider
deriving DecidableEq, Repr

/-- Two candidate providers. -/
inductive Provider
  | p1
  | p2
deriving DecidableEq, Repr

/-- Phases: idle → reserved (deposit held) → done. -/
inductive Phase
  | idle
  | reserved
  | done
deriving DecidableEq, Repr

/-- The operations. `reserve` holds the buyer's deposit; `commit p` spends the one-use capability
on provider `p` (the provider's reply: delivered or not); `cancel` abandons and refunds. -/
inductive Op : Phase → Type
  | reserve : Op .idle
  | commit (p : Provider) : Op .reserved
  | cancel : Op .reserved

def respOf : {i : Phase} → Op i → Type
  | _, .reserve => Unit
  | _, .commit _ => Bool
  | _, .cancel => Unit

def sig : Sig Phase where
  Op := Op
  Resp := respOf
  next := fun
    | .reserve, _ => .reserved
    | .commit _, _ => .done
    | .cancel, _ => .done

/-- The single linear token: the capability. -/
inductive Tok
  | cap
deriving DecidableEq, Repr

/-- Reusable facts: a provider's authority; the deadline has not passed. -/
inductive Fact
  | auth (p : Provider)
  | beforeDeadline
deriving DecidableEq, Repr

/-- Obligations: the deposit is held; pay provider `p`; refund the deposit. -/
inductive Ob
  | holdDeposit
  | pay (p : Provider)
  | refund
deriving DecidableEq, Repr

def spec : Spec sig Tok Fact Ob where
  consumes := fun
    | .commit _ => some .cap
    | _ => none
  requires := fun
    | .commit p => [.auth p, .beforeDeadline]
    | _ => []
  establishes := fun
    | .reserve => [.holdDeposit]
    | .commit p => [.pay p]
    | .cancel => [.refund]

/-- One hole: which provider, chosen by us, after the reservation. -/
def HoleN : Phase → Type
  | .reserved => Unit
  | _ => Empty

/-- Results: whether the capability's service was delivered. -/
abbrev Res : Phase → Type := fun _ => Bool

abbrev P := Prot sig HoleN Res

instance : ∀ i, DecidableEq (HoleN i)
  | .idle => fun a => nomatch a
  | .reserved => fun () () => isTrue rfl
  | .done => fun a => nomatch a

/-- The open protocol: reserve, then the provider hole. -/
def template : P .idle := .call (S := sig) Op.reserve fun _ => .hole (i := Phase.reserved) ()

/-- A candidate: commit the capability on `p`; deliver its reply. -/
def plan (p : Provider) : P .reserved := .call (S := sig) (Op.commit p) fun ok => .ret ok

/-- The cancellation path. -/
def cancelPlan : P .reserved := .call (S := sig) Op.cancel fun _ => .ret false

/-- The hole's interface: chosen by the buyer, accepted by the buyer, may use both providers'
authority and the deadline, may spend the capability, may owe payment to either provider or the
refund. -/
def iface : Iface sig HoleN Res Party Tok Fact Ob .reserved where
  chooser := .buyer
  ctx := [.auth .p1, .auth .p2, .beforeDeadline]
  need := [.cap]
  post := fun _ _ => True
  owes := [.pay .p1, .pay .p2, .refund]
  accepts := fun _ => True

def Ω : Ctx sig HoleN Res Party Tok Fact Ob := fun
  | .reserved, () => some iface
  | .idle, h => nomatch h
  | .done, h => nomatch h

/-- Choose `f` for the provider hole. -/
def choose (f : P .reserved) : Subst sig HoleN Res := fun
  | .reserved, () => some f
  | .idle, h => nomatch h
  | .done, h => nomatch h

/-- The negotiation's responses, listed. -/
def finite : Finite sig where
  resps := fun
    | .reserve => [()]
    | .commit _ => [true, false]
    | .cancel => [()]
  complete := by
    intro i op r
    cases op with
    | reserve => cases r; simp
    | commit p => cases r <;> simp
    | cancel => cases r; simp

/-- The negotiation's hypotheses, tokens and obligation bound. -/
def Γ₀ : List Fact := [.auth .p1, .auth .p2, .beforeDeadline]
def Δ₀ : List Tok := [.cap]
def Φ₀ : List Ob := [.holdDeposit, .pay .p1, .pay .p2, .refund]

/-- The open object: the template with `f` chosen for the provider hole, history `H`. -/
def obj (f : P .reserved) (H : Hist sig) : Open sig HoleN Res Party Tok Fact Ob .idle where
  me := .buyer
  template := template
  Ω := Ω
  σ := choose f
  Γ := Γ₀
  Δ := Δ₀
  Q := fun _ _ => True
  Φ := Φ₀
  hist := H

/-- The reservation answered. -/
def reserved : Entry sig := ⟨.idle, Op.reserve, ()⟩

/-- Reserved; nothing dispatched yet. -/
def H₀ : Hist sig := ⟨[reserved], none⟩

/-- Reserved; the commitment to `p` dispatched and its reply LOST. -/
def lost (p : Provider) : Hist sig := ⟨[reserved], some ⟨.reserved, Op.commit p⟩⟩

/-- An environment: providers deliver iff `deliver`; the state counts calls. -/
def env (deliver : Bool) : Handler sig (fun _ => Nat) where
  handle := fun op n => match op with
    | .reserve => ⟨(), n + 1⟩
    | .commit _ => ⟨deliver, n + 1⟩
    | .cancel => ⟨(), n + 1⟩

/-! ### Internal once versus external once -/

/-- The external side of one commitment: how many times the network delivered the dispatched
request, whether the provider deduplicates by the request identity, and so how many times the
service was performed. -/
structure External where
  deliveries : Nat
  dedupe : Bool

def External.executions (e : External) : Nat :=
  if e.dedupe then min e.deliveries 1 else e.deliveries

/-- What the internal model records about one commitment: the nullifier spent and the reply
(`none`: lost). -/
structure Internal where
  capSpent : Bool
  reply : Option Bool

/-- The reply an answered entry carries, if it is a commitment. -/
def entryReply : Entry sig → Option Bool
  | ⟨_, op, r⟩ => match op, r with
    | .commit _, b => some b
    | .reserve, _ => none
    | .cancel, _ => none

/-- Is an in-flight call a commitment? -/
def inflightSpends : Option (Σ i, sig.Op i) → Bool
  | some ⟨_, .commit _⟩ => true
  | _ => false

/-- The internal record, READ OFF a history: the nullifier is spent when an answered or in-flight
call spent the capability; the reply is the answered commitment's. -/
def Internal.ofHist (H : Hist sig) : Internal where
  capSpent := (consumed spec H.answered).contains .cap || inflightSpends H.inflight
  reply := H.answered.findSome? entryReply

/-- Reserved, then the commitment to `p` answered with `b`. -/
def answeredH (p : Provider) (b : Bool) : Hist sig :=
  ⟨[reserved, ⟨.reserved, Op.commit p, b⟩], none⟩

/-- A filling with the same first call as `plan p` but a different continuation. -/
def planFlip (p : Provider) : P .reserved := .call (S := sig) (Op.commit p) fun ok => .ret (!ok)

end Negotiation

end Nanodregg.Lang.Contextual.Protocol
