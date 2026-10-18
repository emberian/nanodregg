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

theorem insert_perm (x : Label × α) : ∀ ys : List (Label × α), (insert x ys).Perm (x :: ys)
  | [] => .refl _
  | y :: ys => by
    unfold insert
    split
    · exact .refl _
    · exact ((insert_perm x ys).cons y).trans (.swap x y ys)

theorem sort_perm : ∀ xs : List (Label × α), (sort xs).Perm xs
  | [] => .refl _
  | x :: xs => (insert_perm x (sort xs)).trans ((sort_perm xs).cons x)

theorem insert_map (g : Label × α → Label × β) (hg : ∀ z, (g z).1 = z.1)
    (x : Label × α) : ∀ ys : List (Label × α), (insert x ys).map g = insert (g x) (ys.map g)
  | [] => rfl
  | z :: ys => by
    by_cases hxz : x.1 ≤ z.1 <;> simp [insert, hg, hxz, insert_map g hg x ys]

/-- Sorting commutes with a map that keeps every label. -/
theorem sort_map (g : Label × α → Label × β) (hg : ∀ z, (g z).1 = z.1) :
    ∀ xs : List (Label × α), (sort xs).map g = sort (xs.map g)
  | [] => rfl
  | x :: xs => by
    show (insert x (sort xs)).map g = insert (g x) (sort (xs.map g))
    rw [insert_map g hg, sort_map g hg xs]

theorem length_sort (xs : List (Label × α)) : (sort xs).length = xs.length := (sort_perm xs).length_eq

/-- Inserting related entries at one label keeps two label-aligned rows related. -/
theorem Rel.insert {R : α → β → Prop} {ℓ : Label} {a : α} {b : β} (hab : R a b) :
    ∀ {xs : List (Label × α)} {ys : List (Label × β)}, Rel R xs ys →
      Rel R (Row.insert (ℓ, a) xs) (Row.insert (ℓ, b) ys)
  | _, _, .nil => .cons hab .nil
  | _, _, .cons (ℓ := k) hk hr => by
    by_cases h : ℓ ≤ k
    · simp only [Row.insert, h, if_true]; exact .cons hab (.cons hk hr)
    · simp only [Row.insert, h, if_false]; exact .cons hk (Rel.insert hab hr)

/-- Sorting keeps two label-aligned rows related: the sort looks only at the labels. -/
theorem Rel.sort {R : α → β → Prop} :
    ∀ {xs : List (Label × α)} {ys : List (Label × β)}, Rel R xs ys → Rel R (Row.sort xs) (Row.sort ys)
  | _, _, .nil => .nil
  | _, _, .cons h hr => by
    show Rel R (Row.insert _ (Row.sort _)) (Row.insert _ (Row.sort _))
    exact Rel.insert h (Rel.sort hr)

end Nanodregg.Lang.Row
