/-
# Lang.Proofs.Chain — a law's history, lifted once (LANG-65)

`Lang.Proofs.Std` says what ONE admitted step of a law means. A package author's statements are
about a HISTORY: "at most one payout", "the field is always bounded", "the machine only reaches
states reachable from its start". This module proves the run-level lift once, for every law, so
each such statement is a scheme applied to per-step lemmas.

`Chain R o steps`: `(request, new state)` pairs from the state `o`, each an `R`-step over the state
the previous one left. Two step relations matter: `Admits lib law` (the law alone: a derivation to
`ok`, so a law that faults or refuses never steps) and `Step lib law` (that, and a law change or
adoption keeps the state, `LawKeeps`: KERNEL's `law_judged` judges `relaw` and `adopt` over the
object's unchanged state). A `Step` chain is an `Admits` chain (`chain_mono`); the schemes hold
for every relation.

* `chain_mono`: a chain of stronger steps is a chain of weaker ones;
* `chain_invariant`: a state predicate every step preserves holds at every state the chain reaches;
* `chain_always`: what every step satisfies (about its request, its new state and the state before
  it) holds of every step of the chain;
* `chain_each`: the same for a fact about a step's request and new state alone;
* `chain_sum`: a potential argument; a step's weight is paid by the rise of `φ`, so the weights
  of the whole chain are at most the bound on `φ`;
* `chain_count`: a marked step leads to a stopping state the law admits nothing from, so at most
  one step of the chain is marked; `chain_stops`: nothing follows a stopping state.

The polarity (PROOF-ENGINEERING Q3): wp over the fold, sp over the law. `Admits` stays existential;
`Lang.Proofs.Receiver.fault_never_admits` is the tooth on the judge's side. The kernel's half (a
World's audited history around one object projects to a `Chain` for every law in force) is
KERNEL's `Kernel.Proofs.Logic.History.object_history_chain` (KERNEL-28): an `ObjectHistory` (every
step of the World around one object; an audited log is one, `object_history_of_audit`) is a
`Chain (Step [] t)` for every `NoRef` law `t` in force. The per-law instances are `Lang.Proofs.StdChain`.
-/
import Lang.Proofs.Std

namespace Nanodregg.Lang.Std

open Nanodregg.Lang

/-- A law change (`relaw`) or adoption (`adopt`) keeps the state: the kernel judges both over the
object's unchanged state (`Kernel.Proofs.law_judged`). -/
def LawKeeps (rq n o : Data) : Prop :=
  ∀ ℓ x, rq.field "occasion" = some (.inj ℓ x) → (ℓ = "relaw" ∨ ℓ = "adopt") → n = o

/-- One step of a law's history from `o` to `n` under request `rq`. -/
def Step (lib : List Term) (law : Term) (rq n o : Data) : Prop :=
  Admits lib law rq n o ∧ LawKeeps rq n o

/-- A chain of `R`-steps (`R rq n o`: request `rq` takes `o` to `n`): `(request, new state)` pairs
from `o`, each over the state the previous one left. The request and state types are parameters
(a law's history has `Data` for both; a World's audited log has a `Step` and a `World`, LEDGER-19):
ONE chain scheme for every history. -/
inductive Chain {Q St : Type} (R : Q → St → St → Prop) : St → List (Q × St) → Prop
  | nil (o : St) : Chain R o []
  | cons {o : St} {rq : Q} {n : St} {rest : List (Q × St)} :
      R rq n o → Chain R n rest → Chain R o ((rq, n) :: rest)

variable {Q St : Type} {R : Q → St → St → Prop}

/-- A chain of stronger steps is a chain of weaker ones (a `Step` chain is an `Admits` chain). -/
theorem chain_mono {R' : Q → St → St → Prop} (hR : ∀ rq n o, R rq n o → R' rq n o)
    {o : St} {steps : List (Q × St)} (h : Chain R o steps) : Chain R' o steps := by
  induction h with
  | nil o => exact .nil o
  | cons hs _ ih => exact .cons (hR _ _ _ hs) ih

/-- **The invariant scheme.** A state predicate every step preserves, true at the start, holds at
every state the chain reaches. -/
theorem chain_invariant (inv : St → Prop) (hpres : ∀ rq n o, R rq n o → inv o → inv n)
    {o : St} {steps : List (Q × St)} (h : Chain R o steps) (h0 : inv o) :
    ∀ s ∈ steps, inv s.2 := by
  induction h with
  | nil => simp
  | @cons o rq n rest hs _ ih =>
    intro s hm
    have hn := hpres rq n o hs h0
    rcases List.mem_cons.1 hm with rfl | hm
    · exact hn
    · exact ih hn s hm

/-- **The step scheme.** What every step satisfies, about its request `rq`, its new state `n` and
the state `o'` before it, holds of every step of the chain (paired with the state before it). -/
theorem chain_always (P : Q → St → St → Prop) (hstep : ∀ rq n o, R rq n o → P rq n o)
    {o : St} {steps : List (Q × St)} (h : Chain R o steps) :
    ∀ o' rq n, (o', (rq, n)) ∈ (o :: steps.map Prod.snd).zip steps → P rq n o' := by
  induction h with
  | nil => simp
  | @cons o rq n rest hs _ ih =>
    intro o' rq' n' hm
    simp only [List.map_cons, List.zip_cons_cons, List.mem_cons, Prod.mk.injEq] at hm
    rcases hm with ⟨rfl, rfl, rfl⟩ | hm
    · exact hstep _ _ _ hs
    · exact ih o' rq' n' hm

private theorem mem_zip_prev {s : Q × St} :
    ∀ {o : St} {steps : List (Q × St)}, s ∈ steps → ∃ o', (o', s) ∈ (o :: steps.map Prod.snd).zip steps
  | _, [], h => by simp at h
  | o, a :: rest, h => by
    simp only [List.map_cons, List.zip_cons_cons, List.mem_cons] at h ⊢
    rcases h with rfl | h
    · exact ⟨o, .inl rfl⟩
    · obtain ⟨o', ho'⟩ := mem_zip_prev (o := a.2) h
      exact ⟨o', .inr ho'⟩

/-- The step scheme for a fact about a step's request and new state alone: it holds of every step. -/
theorem chain_each (P : Q → St → Prop) (hstep : ∀ rq n o, R rq n o → P rq n)
    {o : St} {steps : List (Q × St)} (h : Chain R o steps) : ∀ s ∈ steps, P s.1 s.2 := by
  intro s hs
  obtain ⟨o', ho'⟩ := mem_zip_prev (o := o) hs
  exact chain_always (fun rq n _ => P rq n) (fun rq n o hs => hstep rq n o hs) h o' s.1 s.2 ho'

/-- **The potential scheme.** If each step of the chain has its weight `f rq n o` paid by the rise
of `φ` from `o` to `n`, and `φ` is at most `B` at every state the chain holds, the weights of all
the steps plus `φ` at the start are at most `B`. -/
theorem chain_sum (φ : St → Nat) (f : Q → St → St → Nat) (B : Nat)
    {o : St} {steps : List (Q × St)} (h : Chain R o steps)
    (hstep : ∀ rq n o, R rq n o → (rq, n) ∈ steps → f rq n o + φ o ≤ φ n)
    (hB : ∀ s ∈ steps, φ s.2 ≤ B) (h0 : φ o ≤ B) :
    (((o :: steps.map Prod.snd).zip steps).map fun x => f x.2.1 x.2.2 x.1).sum + φ o ≤ B := by
  induction h with
  | nil => simpa using h0
  | @cons o rq n rest hs _ ih =>
    have hn : φ n ≤ B := hB (rq, n) (List.mem_cons_self ..)
    have hr := ih (fun rq' n' o' hs' hm => hstep rq' n' o' hs' (List.mem_cons_of_mem _ hm))
      (fun s hm => hB s (List.mem_cons_of_mem _ hm)) hn
    have he := hstep rq n o hs (List.mem_cons_self ..)
    simp only [List.map_cons, List.zip_cons_cons, List.sum_cons] at hr ⊢
    omega

/-- Nothing follows a stopping state: a state the law admits no step from ends every chain. -/
theorem chain_stops (Stop : St → Prop) (hstop : ∀ rq n o, Stop o → ¬ R rq n o)
    {o : St} {steps : List (Q × St)} (hs : Stop o) (h : Chain R o steps) : steps = [] := by
  cases h with
  | nil => rfl
  | cons ha _ => exact (hstop _ _ _ hs ha).elim

/-- **The once scheme.** If a marked step leads to a state the law admits no step from, at most
one step of any chain is marked. -/
theorem chain_count (mark : Q × St → Bool) (Stop : St → Prop)
    (hmark : ∀ rq n o, R rq n o → mark (rq, n) = true → Stop n)
    (hstop : ∀ rq n o, Stop o → ¬ R rq n o)
    {o : St} {steps : List (Q × St)} (h : Chain R o steps) : (steps.filter mark).length ≤ 1 := by
  induction h with
  | nil => simp
  | @cons o rq n rest hs hr ih =>
    by_cases hm : mark (rq, n) = true
    · rw [chain_stops Stop hstop (hmark rq n o hs hm) hr]
      simp [hm]
    · simp only [List.filter_cons, hm] at ih ⊢
      simpa using ih

/-! ## The occasion of an admitted step -/

private theorem find_label_mem {α : Type} {ℓ : Label} {b : α} :
    ∀ {row : List (Label × α)}, Row.find? ℓ row = some b → ℓ ∈ row.map Prod.fst
  | [], h => by simp [Row.find?] at h
  | (k, a) :: rest, h => by
    simp only [Row.find?] at h
    split at h
    · rename_i hk; subst hk; simp
    · exact List.mem_cons_of_mem _ (find_label_mem h)

/-- An admitted step of a five-armed law (`lawOf5`, and so `lawOf`) names one of the five
occasions. -/
theorem lawOf5_occasion {lib : List Term} {S : Ty} {b ad rl wr iv : At → Term} {rq n o : Data}
    (h : Admits lib (lawOf5 S b ad rl wr iv) rq n o) :
    ∃ ℓ x, rq.field "occasion" = some (.inj ℓ x) ∧
      (ℓ = "adopt" ∨ ℓ = "birth" ∨ ℓ = "invoke" ∨ ℓ = "relaw" ∨ ℓ = "write") := by
  obtain ⟨cenv, w, hb⟩ := h
  simp only [lawOf5, lawBody, lawCase5] at hb
  obtain ⟨ℓ, y, body, hd, hf, _⟩ := case_field (d := rq) (i := 0) rfl hb
  have hm := find_label_mem hf
  simp at hm
  exact ⟨ℓ, y, hd, hm⟩

end Nanodregg.Lang.Std
