/-
# Lang.Proofs.Contextual.ProtocolTyping — the statements of the open-protocol theory (lane PROTOCOL)

The Prop-valued relations over `Lang.Contextual.Protocol`'s data: the judgment
`Ω;Γ;Δ ⊢ P : Protocol(i, Q) ⊣ Φ` (`HasProt`), linear tokens as a bag (`SubBag`), a filling that
satisfies an interface (`Fills`), an interface-respecting substitution (`SubstOK`), algebra
morphisms, complete paths (`Runs`), prefixes (`Reach`), histories (`Started`), entered holes
(`Dispatched`), the guard on a re-plan (`Open.Replan`), the well-formed open object (`Open.WF`),
and sufficient supports (`Frag.ReadsOnly`). Theorems in `Lang.Proofs.Contextual.Protocol`.
The completion space `Conds.space`, the matcher assignments `Assigns`, the scalar matchers and the
private `World` went with PROT-6, replaced by Std.offer's deployed fuse (`Lang/StdOffer.lean`).
-/
import Lang.Contextual.Protocol

namespace Nanodregg.Lang.Contextual.Protocol

section
variable {Ix : Type} {S : Sig Ix} {Hole : Ix → Type} {A : Ix → Type}

/-- `h` occurs in `P` (on some response path). -/
inductive Occurs : {i : Ix} → Prot S Hole A i → (j : Ix) → Hole j → Prop
  | here {j : Ix} (h : Hole j) : Occurs (.hole h) j h
  | call {i : Ix} {op : S.Op i} {k : (r : S.Resp op) → Prot S Hole A (S.next op r)}
      {j : Ix} {h : Hole j} (r : S.Resp op) : Occurs (k r) j h → Occurs (.call op k) j h

/-- `Δ₁ ≤ Δ₂` as bags: no token occurs more often in `Δ₁`. -/
def SubBag {Tok : Type} [DecidableEq Tok] (Δ₁ Δ₂ : List Tok) : Prop :=
  ∀ t, Δ₁.count t ≤ Δ₂.count t

/-- `HasProt sp me Ω Γ Q Φ Δ P`: the protocol judged as role `me`. A `call` requires its facts from `Γ`, records its obligations in `Φ`,
and, if it spends a token, takes it from `Δ`: every continuation is judged with that token gone
(LINEAR: a token is spent by at most one call on any path, `Proofs.hasProt_reach`). A hole is
judged by its declared interface: `me` must be its chooser, its context and tokens available here, its
results within `Q`, its obligations within `Φ`. -/
inductive HasProt {Role Tok Fact Ob : Type} [DecidableEq Tok] (sp : Spec S Tok Fact Ob) (me : Role)
    (Ω : Ctx S Hole A Role Tok Fact Ob) (Γ : List Fact) (Q : (j : Ix) → A j → Prop) (Φ : List Ob) :
    List Tok → {i : Ix} → Prot S Hole A i → Prop
  | ret {Δ : List Tok} {i : Ix} (a : A i) : Q i a → HasProt sp me Ω Γ Q Φ Δ (.ret a)
  | call {Δ : List Tok} {i : Ix} (op : S.Op i)
      (k : (r : S.Resp op) → Prot S Hole A (S.next op r)) :
      sp.consumes op = none → (∀ f ∈ sp.requires op, f ∈ Γ) →
      (∀ o ∈ sp.establishes op, o ∈ Φ) →
      (∀ r, HasProt sp me Ω Γ Q Φ Δ (k r)) → HasProt sp me Ω Γ Q Φ Δ (.call op k)
  | spend {Δ : List Tok} {i : Ix} (op : S.Op i)
      (k : (r : S.Resp op) → Prot S Hole A (S.next op r)) (t : Tok) :
      sp.consumes op = some t → t ∈ Δ → (∀ f ∈ sp.requires op, f ∈ Γ) →
      (∀ o ∈ sp.establishes op, o ∈ Φ) →
      (∀ r, HasProt sp me Ω Γ Q Φ (Δ.erase t) (k r)) → HasProt sp me Ω Γ Q Φ Δ (.call op k)
  | hole {Δ : List Tok} {i : Ix} (h : Hole i) (I : Iface S Hole A Role Tok Fact Ob i) :
      Ω i h = some I → I.chooser = me → (∀ f ∈ I.ctx, f ∈ Γ) → SubBag I.need Δ →
      (∀ j a, I.post j a → Q j a) → (∀ o ∈ I.owes, o ∈ Φ) → HasProt sp me Ω Γ Q Φ Δ (.hole h)

/-- A filling satisfies a hole's interface: judged as `me` in the hole's own context, tokens, result
and obligations, and passing the hole's acceptance contract. -/
def Fills {Role Tok Fact Ob : Type} [DecidableEq Tok] (sp : Spec S Tok Fact Ob) (me : Role)
    (Ω : Ctx S Hole A Role Tok Fact Ob) {i : Ix} (I : Iface S Hole A Role Tok Fact Ob i)
    (f : Prot S Hole A i) : Prop :=
  HasProt sp me Ω I.ctx I.post I.owes I.need f ∧ I.accepts f

/-- A substitution respects `Ω` for role `me`: it fills only declared holes `me` chooses, each with
a filling that satisfies the hole's interface. -/
def SubstOK {Role Tok Fact Ob : Type} [DecidableEq Tok] (sp : Spec S Tok Fact Ob) (me : Role)
    (Ω : Ctx S Hole A Role Tok Fact Ob) (σ : Subst S Hole A) : Prop :=
  ∀ i h f, σ i h = some f → ∃ I, Ω i h = some I ∧ I.chooser = me ∧ Fills sp me Ω I f

/-- `φ` is an algebra morphism `src → dst` (carriers may differ). -/
structure AlgebraHom {C D : Ix → Type} (src : Algebra S Hole A C) (dst : Algebra S Hole A D)
    (φ : (i : Ix) → C i → D i) : Prop where
  ret : ∀ {i : Ix} (a : A i), φ i (src.ret a) = dst.ret a
  call : ∀ {i : Ix} (op : S.Op i) (k : (r : S.Resp op) → C (S.next op r)),
    φ i (src.call op k) = dst.call op (fun r => φ (S.next op r) (k r))
  hole : ∀ {i : Ix} (h : Hole i), φ i (src.hole h) = dst.hole h

/-- A complete path: the interactions performed, each with SOME response, and the result. -/
inductive Runs : {i : Ix} → Prot S Hole A i → Trace S → (j : Ix) → A j → Prop
  | ret {i : Ix} (a : A i) : Runs (.ret a) [] i a
  | call {i : Ix} {op : S.Op i} {k : (r : S.Resp op) → Prot S Hole A (S.next op r)}
      {tr : Trace S} {j : Ix} {a : A j} (r : S.Resp op) :
      Runs (k r) tr j a → Runs (.call op k) (⟨i, op, r⟩ :: tr) j a

/-- A performed prefix and the residual protocol it leaves. -/
inductive Reach : {i : Ix} → Prot S Hole A i → Trace S → (Σ j, Prot S Hole A j) → Prop
  | here {i : Ix} (P : Prot S Hole A i) : Reach P [] ⟨i, P⟩
  | call {i : Ix} {op : S.Op i} {k : (r : S.Resp op) → Prot S Hole A (S.next op r)}
      {tr : Trace S} {R : Σ j, Prot S Hole A j} (r : S.Resp op) :
      Reach (k r) tr R → Reach (.call op k) (⟨i, op, r⟩ :: tr) R

/-- `H` is a history of `P`: the answered part is a prefix, and the in-flight call (if any) is the
call the prefix's residual makes. -/
inductive Started : {i : Ix} → Prot S Hole A i → Hist S → Prop
  | settled {i : Ix} {P : Prot S Hole A i} {t : Trace S} {R : Σ j, Prot S Hole A j} :
      Reach P t R → Started P ⟨t, none⟩
  | uncertain {i : Ix} {P : Prot S Hole A i} {t : Trace S} {j : Ix} {op : S.Op j}
      {k : (r : S.Resp op) → Prot S Hole A (S.next op r)} :
      Reach P t ⟨j, .call op k⟩ → Started P ⟨t, some ⟨j, op⟩⟩

/-- The history has ENTERED hole `h` of the template: the template's prefix reached `h` and
something after it was performed or dispatched (the filling's first call left). -/
def Dispatched {i : Ix} (P : Prot S Hole A i) (H : Hist S) (j : Ix) (h : Hole j) : Prop :=
  ∃ t₁ t₂, H.answered = t₁ ++ t₂ ∧ Reach P t₁ ⟨j, .hole h⟩ ∧ (t₂ ≠ [] ∨ H.inflight.isSome = true)

/-- A well-formed open object: the template is judged, the substitution respects `Ω`, the
history is a history of the current protocol. -/
structure Open.WF {Role Tok Fact Ob : Type} [DecidableEq Role] [DecidableEq Tok]
    (sp : Spec S Tok Fact Ob) {i : Ix} (O : Open S Hole A Role Tok Fact Ob i) : Prop where
  typed : HasProt sp O.me O.Ω O.Γ O.Q O.Φ O.Δ O.template
  substOK : SubstOK sp O.me O.Ω O.σ
  started : Started O.current O.hist

/-- The guard on a re-plan: the new substitution agrees with the old one on every hole the history
has entered (there is no unguarded re-plan in any theorem: each takes this as a hypothesis). -/
def Open.Replan {Role Tok Fact Ob : Type} [DecidableEq Role] {i : Ix} (O : Open S Hole A Role Tok Fact Ob i)
    (σ' : Subst S Hole A) : Prop :=
  ∀ j h, Dispatched O.template O.hist j h → σ'.mine O.me O.Ω j h = O.σ.mine O.me O.Ω j h

end

/-- The fragment's check reads only its support (the soundness of a declared dependency set:
sufficient, not minimal). -/
def Frag.ReadsOnly {Name Key V : Type} (f : Frag Name Key V) : Prop :=
  ∀ w₁ w₂ : Key → V, (∀ k ∈ f.support, w₁ k = w₂ k) → f.check w₁ = f.check w₂


end Nanodregg.Lang.Contextual.Protocol
