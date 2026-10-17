import Codec.Digest

/-! # The digest order is a lawful total order (what `Std.TreeMap Digest` needs)

`compare` on digests is `compare` on their byte arrays (lexicographic), so its laws are the
array order's, pulled back along `Digest.bytes`, which is injective. -/

namespace Nanodregg.Codec.Digest

theorem compare_def (a b : Digest) : compare a b = compare a.bytes.data b.bytes.data := rfl

theorem ext {a b : Digest} (h : a.bytes.data = b.bytes.data) : a = b := by
  obtain ⟨⟨x⟩, _⟩ := a
  obtain ⟨⟨y⟩, _⟩ := b
  simp only at h
  subst h
  rfl

/-! The laws are theorems (they are Props) registered as instances. -/

@[instance] theorem orientedOrd : Std.OrientedOrd Digest :=
  { eq_swap := fun {a b} => by simp only [compare_def]; exact Std.OrientedCmp.eq_swap }

@[instance] theorem transOrd : Std.TransOrd Digest :=
  { isLE_trans := fun {a b c} h₁ h₂ => by
      simp only [compare_def] at *
      exact Std.TransCmp.isLE_trans h₁ h₂ }

@[instance] theorem lawfulEqOrd : Std.LawfulEqOrd Digest :=
  { eq_of_compare := fun {a b} h => by
      simp only [compare_def] at h
      exact ext (Std.LawfulEqCmp.eq_of_compare h) }

end Nanodregg.Codec.Digest
