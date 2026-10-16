/-
# Lang.Proofs.Row — a pointwise relation between two rows with the same labels survives every row
operation (`find?`, `put`, `merge`, `map`)

This is the one lemma family the soundness proof needs about records: a record VALUE and its
record TYPE are two rows with the same labels, and `get`/`extend` act on both alike.
-/
import Lang.Row

namespace Nanodregg.Lang.Row

variable {α β : Type}

/-- `xs` and `ys` have the same labels in the same order and `R` holds at each position. -/
inductive Rel (R : α → β → Prop) : List (Label × α) → List (Label × β) → Prop
  | nil : Rel R [] []
  | cons {ℓ : Label} {a : α} {b : β} {xs ys} :
      R a b → Rel R xs ys → Rel R ((ℓ, a) :: xs) ((ℓ, b) :: ys)

theorem Rel.find {R : α → β → Prop} {xs : List (Label × α)} {ys : List (Label × β)}
    (h : Rel R xs ys) (ℓ : Label) {b : β} (hb : find? ℓ ys = some b) :
    ∃ a, find? ℓ xs = some a ∧ R a b := by
  induction h with
  | nil => simp [find?] at hb
  | @cons k a b' xs ys hab _ ih =>
    by_cases e : ℓ = k
    · simp only [find?, e, if_true] at hb ⊢
      cases hb; exact ⟨a, rfl, hab⟩
    · simp only [find?, e, if_false] at hb ⊢
      exact ih hb

theorem Rel.find_left {R : α → β → Prop} {xs : List (Label × α)} {ys : List (Label × β)}
    (h : Rel R xs ys) (ℓ : Label) {a : α} (ha : find? ℓ xs = some a) :
    ∃ b, find? ℓ ys = some b ∧ R a b := by
  induction h with
  | nil => simp [find?] at ha
  | @cons k a' b xs ys hab _ ih =>
    by_cases e : ℓ = k
    · simp only [find?, e, if_true] at ha ⊢
      cases ha; exact ⟨b, rfl, hab⟩
    · simp only [find?, e, if_false] at ha ⊢
      exact ih ha

theorem Rel.put {R : α → β → Prop} {xs : List (Label × α)} {ys : List (Label × β)}
    (h : Rel R xs ys) (ℓ : Label) {a : α} {b : β} (hab : R a b) :
    Rel R (Row.put ℓ a xs) (Row.put ℓ b ys) := by
  induction h with
  | nil => exact .cons hab .nil
  | @cons k a' b' xs ys h' hr ih =>
    simp only [Row.put]
    by_cases lt : ℓ < k
    · simp only [if_pos lt]; exact .cons hab (.cons h' hr)
    · by_cases e : ℓ = k
      · subst e; simp only [if_neg lt, if_true]; exact .cons hab hr
      · simp only [if_neg lt, if_neg e]; exact .cons h' ih

theorem Rel.merge {R : α → β → Prop} {xs : List (Label × α)} {ys : List (Label × β)}
    {as : List (Label × α)} {bs : List (Label × β)}
    (h : Rel R xs ys) (h2 : Rel R as bs) : Rel R (Row.merge xs as) (Row.merge ys bs) := by
  induction h2 generalizing xs ys with
  | nil => exact h
  | cons hab _ ih => exact ih (h.put _ hab)

theorem Rel.map_left {γ : Type} {R : α → β → Prop} {S : γ → β → Prop} (f : α → γ)
    {xs : List (Label × α)} {ys : List (Label × β)}
    (h : Rel R xs ys) (hf : ∀ a b, R a b → S (f a) b) :
    Rel S (xs.map fun p => (p.1, f p.2)) ys := by
  induction h with
  | nil => exact .nil
  | cons hab _ ih => exact .cons (hf _ _ hab) ih

theorem Rel.labels {R : α → β → Prop} {xs : List (Label × α)} {ys : List (Label × β)}
    (h : Rel R xs ys) : xs.map Prod.fst = ys.map Prod.fst := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]

end Nanodregg.Lang.Row
