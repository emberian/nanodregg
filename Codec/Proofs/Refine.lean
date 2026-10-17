import Codec.Proofs.Raw

/-! # A refinement's lawfulness theorem pins its accept function (CODEC-28)

`refine name c accept back` hides two functions from its `Shape`, so `Tag.of` sees only `name`.
`refine_accept_iff` is why every refinement's lawfulness theorem (`LawfulOn R (refine …)`) is a check
on `accept` and not a promise: on every value the inner codec reads, `accept` admits exactly the
values `R` holds of, spelled by `back`. If `accept` changes what it admits and `R` stays, the theorem
breaks. The teeth (`refine_not_lawful_of_refuses`, `_of_admits`, `_of_respells`) say the same thing
as refutations: a mutated `accept` that refuses an `R`-value, admits a value `R` does not hold of, or
admits a value from a second spelling, is not lawful on `R`.

What no such theorem can see is a change to `accept` and `back` TOGETHER that keeps their composite
lawful on the same `R`: a relabelling, i.e. two same-typed fields or constructors swapped in both
(`Codec.Proofs.RefineTooth.slot_relabel_unseen` proves one exists). That change keeps the shape, the
name, the tag and every theorem; CODEC-28 names it.
-/

namespace Nanodregg.Codec.Stream

variable {α β : Type}

/-- **A refinement's lawfulness pins `accept`.** If the inner codec is lawful on `P` and the
refinement is lawful on `R` (with `R` implying `P` of the spelling), then on every inner value,
`accept` admits exactly the `R`-values that `back` spells as it. -/
theorem refine_accept_iff {P : α → Prop} {R : β → Prop} {c : Stream α} {name : String}
    {accept : α → Option β} {back : β → α} (hc : LawfulOn P c)
    (hr : LawfulOn R (refine name c accept back)) (hR : ∀ y, R y → P (back y)) {x : α} (hx : P x)
    (y : β) : accept x = some y ↔ x = back y ∧ R y := by
  have hg : c.get (c.bytes x) 0 = .ok (x, (c.bytes x).size) := by
    simpa using hc.get_of_occurs x (c.bytes x) 0 hx (occursAt_self _)
  constructor
  · intro ha
    have h1 : (refine name c accept back).get (c.bytes x) 0 = .ok (y, (c.bytes x).size) := by
      simp [refine, hg, ha]
    obtain ⟨hy, hj, ho⟩ := hr.occurs_of_get h1
    rw [refine_bytes] at hj ho
    have he : c.bytes x = c.bytes (back y) := eq_of_occursAt_zero ho (by omega)
    exact ⟨hc.bytes_injective hx (hR y hy) he, hy⟩
  · rintro ⟨he, hy⟩
    have h1 := hr.get_of_occurs y (c.bytes (back y)) 0 hy (by rw [refine_bytes]; exact occursAt_self _)
    rw [refine_bytes, ← he] at h1
    simp only [refine, hg] at h1
    split at h1
    · rename_i y' hy'
      simp only [Except.ok.injEq, Prod.mk.injEq] at h1
      rw [hy', h1.1]
    · cases h1

/-- What a lawful refinement refuses: an inner value that `back` spells for no `R`-value. -/
theorem refine_accept_none {P : α → Prop} {R : β → Prop} {c : Stream α} {name : String}
    {accept : α → Option β} {back : β → α} (hc : LawfulOn P c)
    (hr : LawfulOn R (refine name c accept back)) (hR : ∀ y, R y → P (back y)) {x : α} (hx : P x)
    (hn : ∀ y, R y → back y ≠ x) : accept x = none := by
  cases ha : accept x with
  | none => rfl
  | some y =>
    obtain ⟨he, hy⟩ := (refine_accept_iff hc hr hR hx y).mp ha
    exact absurd he.symm (hn y hy)

/-- **Tooth, refusing.** An `accept` that refuses the spelling of an `R`-value is not lawful on `R`. -/
theorem refine_not_lawful_of_refuses {P : α → Prop} {R : β → Prop} {c : Stream α} {name : String}
    {accept : α → Option β} {back : β → α} (hc : LawfulOn P c) (hR : ∀ y, R y → P (back y)) {y : β}
    (hy : R y) (hn : accept (back y) = none) : ¬ LawfulOn R (refine name c accept back) := fun hr => by
  have := (refine_accept_iff hc hr hR (hR y hy) y).mpr ⟨rfl, hy⟩
  rw [hn] at this; cases this

/-- **Tooth, admitting.** An `accept` that admits, from an inner value, a value `R` does not hold of
is not lawful on `R`. -/
theorem refine_not_lawful_of_admits {P : α → Prop} {R : β → Prop} {c : Stream α} {name : String}
    {accept : α → Option β} {back : β → α} (hc : LawfulOn P c) (hR : ∀ y, R y → P (back y)) {x : α}
    (hx : P x) {y : β} (ha : accept x = some y) (hy : ¬ R y) :
    ¬ LawfulOn R (refine name c accept back) := fun hr =>
  hy ((refine_accept_iff hc hr hR hx y).mp ha).2

/-- **Tooth, respelling.** An `accept` that admits a value from an inner value other than the one
`back` spells it as (a second spelling) is not lawful on any `R` it implies the inner domain of. -/
theorem refine_not_lawful_of_respells {P : α → Prop} {R : β → Prop} {c : Stream α} {name : String}
    {accept : α → Option β} {back : β → α} (hc : LawfulOn P c) (hR : ∀ y, R y → P (back y)) {x : α}
    (hx : P x) {y : β} (ha : accept x = some y) (hne : x ≠ back y) :
    ¬ LawfulOn R (refine name c accept back) := fun hr =>
  hne ((refine_accept_iff hc hr hR hx y).mp ha).1

end Nanodregg.Codec.Stream
