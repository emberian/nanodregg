/- Provenance: the all-environment bridge and the ATMS label discipline (P9). -/
import Lang.Proofs.Contextual.Judge

namespace Nanodregg.Lang.Contextual

variable {D : CalculusData} {E : Type}

/-- Grädel–Tannen p19: evaluating deferred literals is the original candidate test. -/
theorem monomial_verified {I : Iface D E} {w : World E} {c : Candidate D} :
    judge I w c = .verified ↔
      D.check I.ctx c.filling I.ty = true ∧ (monomial I c).eval I w = true := by
  simp [judge_verified_iff, Monomial.eval, Monomial.envOK, monomial,
    EnvLit.eval, List.all_eq_true, and_assoc, and_comm, and_left_comm]

/-- **The provenance bridge** (Grädel–Tannen §6 pp19–20): a hole has a verified candidate at `w` iff some
monomial of its ONE retained polynomial evaluates true at `w`, for EVERY world and environment. This is the
bridge to `judge_verified_iff`. -/
theorem provenance_iff {I : Iface D E} {w : World E} {cs : List (Candidate D)} :
    (∃ c ∈ cs, judge I w c = .verified) ↔
      ∃ m ∈ provenance I cs, m.eval I w = true := by
  simp only [provenance, List.mem_map, List.mem_filter]
  constructor
  · rintro ⟨c, hc, hv⟩
    obtain ⟨ht, he⟩ := monomial_verified.mp hv
    exact ⟨monomial I c, ⟨c, ⟨hc, ht⟩, rfl⟩, he⟩
  · rintro ⟨m, ⟨c, ⟨hc, ht⟩, rfl⟩, he⟩
    exact ⟨c, hc, monomial_verified.mpr ⟨ht, he⟩⟩

/-- Grädel–Tannen Def4 p9: complementary token literals cannot both evaluate to true. -/
theorem monomial_complementary_dead {I : Iface D E} {w : World E} {m : Monomial D}
    {t : Token} (hp : t ∈ m.supports) (hn : t ∈ m.blockers) :
    m.eval I w = false := by
  cases h : m.eval I w
  · rfl
  · simp [Monomial.eval, List.all_eq_true] at h
    have a := h.1.2 t hp
    have b := h.2 t hn
    rw [a] at b
    cases b

/-- Grädel–Tannen Def4 p9, applied to Doyle IN/OUT justifications:
a complementary candidate is never verified, regardless of world or environment. -/
theorem provenance_complementary_dead {I : Iface D E} {w : World E} {c : Candidate D}
    {t : Token} (hp : t ∈ effSupports I c) (hn : t ∈ c.blockers) :
    judge I w c ≠ .verified := by
  intro hv
  have he := (monomial_verified.mp hv).2
  rw [monomial_complementary_dead hp hn] at he
  cases he

/-- de Kleer pp144–145 / Grädel–Tannen Def4 p9: every successful product is consistent. -/
theorem eval_consistent {I : Iface D E} {w : World E} {m : Monomial D}
    (h : m.eval I w = true) : m.consistent = true := by
  simp [Monomial.consistent, List.all_eq_true]
  intro t ht hn
  have hf := monomial_complementary_dead (I := I) (w := w) ht hn
  rw [h] at hf
  cases hf

/-- de Kleer p145: the executable subsumption test is literal-set inclusion. -/
theorem subsumes_iff {a b : Monomial D} :
    a.subsumes b = true ↔
    (∀ t ∈ a.supports, t ∈ b.supports) ∧
    (∀ t ∈ a.blockers, t ∈ b.blockers) ∧
    (∀ l ∈ a.envLits, l ∈ b.envLits) := by
  simp [Monomial.subsumes, List.all_eq_true, Bool.and_eq_true, and_assoc]

/-- de Kleer p145: subsumption composes by literal inclusion. -/
theorem subsumes_trans {a b c : Monomial D}
    (hab : a.subsumes b = true) (hbc : b.subsumes c = true) : a.subsumes c = true := by
  obtain ⟨ap, an, ae⟩ := subsumes_iff.mp hab
  obtain ⟨bp, bn, be⟩ := subsumes_iff.mp hbc
  exact subsumes_iff.mpr ⟨fun t ht => bp t (ap t ht), fun t ht => bn t (an t ht),
    fun l hl => be l (ae l hl)⟩

/-- de Kleer p145: a smaller product holds wherever the larger product holds. -/
theorem subsumes_eval {a b : Monomial D} {I : Iface D E} {w : World E}
    (hab : a.subsumes b = true) (hb : b.eval I w = true) : a.eval I w = true := by
  obtain ⟨hp, hn, he⟩ := subsumes_iff.mp hab
  simp only [Monomial.eval, Monomial.envOK, Bool.and_eq_true, List.all_eq_true] at hb ⊢
  exact ⟨⟨fun l hl => hb.1.1 l (he l hl), fun t ht => hb.1.2 t (hp t ht)⟩,
    fun t ht => hb.2 t (hn t ht)⟩

/-- de Kleer p145: absorption keeps original products, not invented explanations. -/
theorem minimal_subset {ms : List (Monomial D)} {m : Monomial D}
    (hm : m ∈ minimal ms) : m ∈ ms := by
  induction ms with
  | nil => simp [minimal] at hm
  | cons a ms ih =>
    simp only [minimal] at hm
    split at hm
    · exact List.mem_cons_of_mem a (ih hm)
    · rcases List.mem_cons.mp hm with rfl | hm
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem a (ih (List.mem_filter.mp hm).1)

/-- de Kleer p145: absorption preserves and covers every successful environment. -/
theorem minimal_eval (ms : List (Monomial D)) (I : Iface D E) (w : World E) :
    (∃ m ∈ minimal ms, m.eval I w = true) ↔ ∃ m ∈ ms, m.eval I w = true := by
  constructor
  · rintro ⟨m, hm, he⟩
    exact ⟨m, minimal_subset hm, he⟩
  · induction ms with
    | nil => simp
    | cons a ms ih =>
      rintro ⟨m, hm, he⟩
      simp only [minimal]
      split
      · rename_i h
        rcases List.mem_cons.mp hm with rfl | hm
        · obtain ⟨n, hn, hna⟩ := List.any_eq_true.mp h
          exact ⟨n, hn, subsumes_eval hna he⟩
        · exact ih ⟨m, hm, he⟩
      · rcases List.mem_cons.mp hm with rfl | hm
        · exact ⟨m, List.mem_cons_self, he⟩
        · obtain ⟨n, hn, hne⟩ := ih ⟨m, hm, he⟩
          cases ha : a.subsumes n with
          | false => exact ⟨n, by simp [hn, ha], hne⟩
          | true => exact ⟨a, List.mem_cons_self, subsumes_eval ha hne⟩

/-- de Kleer p145: every original environment contains a surviving label environment. -/
theorem minimal_covers (ms : List (Monomial D)) {m : Monomial D} (hm : m ∈ ms) :
    ∃ n ∈ minimal ms, n.subsumes m = true := by
  induction ms with
  | nil => simp at hm
  | cons a ms ih =>
    simp only [minimal]
    split
    · rename_i h
      rcases List.mem_cons.mp hm with rfl | hm
      · exact List.any_eq_true.mp h
      · exact ih hm
    · rcases List.mem_cons.mp hm with rfl | hm
      · exact ⟨m, List.mem_cons_self, subsumes_iff.mpr
          ⟨fun _ h => h, fun _ h => h, fun _ h => h⟩⟩
      · obtain ⟨n, hn, hnm⟩ := ih hm
        cases han : a.subsumes n with
        | false => exact ⟨n, by simp [hn, han], hnm⟩
        | true => exact ⟨a, List.mem_cons_self, subsumes_trans han hnm⟩

/-- de Kleer p145: no retained environment is a strict superset of another.
Equal literal sets may have different list orders; the Boolean image identifies them. -/
theorem provenance_minimal (ms : List (Monomial D)) :
    ∀ a ∈ minimal ms, ∀ b ∈ minimal ms,
      a.subsumes b = true → b.subsumes a = true := by
  induction ms with
  | nil => simp [minimal]
  | cons m ms ih =>
    simp only [minimal]
    split
    · exact ih
    · rename_i h
      intro a ha b hb hab
      rcases List.mem_cons.mp ha with rfl | ha <;>
      rcases List.mem_cons.mp hb with rfl | hb
      · exact hab
      · have hf := (List.mem_filter.mp hb).2
        simp [hab] at hf
      · have ha' := (List.mem_filter.mp ha).1
        have ht : (minimal ms).any (fun n => n.subsumes b) = true :=
          List.any_eq_true.mpr ⟨a, ha', hab⟩
        exact False.elim (h ht)
      · exact ih a (List.mem_filter.mp ha).1 b (List.mem_filter.mp hb).1 hab

/-- de Kleer pp144–145: sound, complete, consistent, absorbed labels retain the
all-environment provenance bridge (Grädel–Tannen pp19–20). -/
theorem label_iff {I : Iface D E} {w : World E} {cs : List (Candidate D)} :
    (∃ c ∈ cs, judge I w c = .verified) ↔ ∃ m ∈ label I cs, m.eval I w = true := by
  rw [provenance_iff, label, minimal_eval]
  constructor
  · rintro ⟨m, hm, he⟩
    exact ⟨m, List.mem_filter.mpr ⟨hm, eval_consistent he⟩, he⟩
  · rintro ⟨m, hm, he⟩
    exact ⟨m, (List.mem_filter.mp hm).1, he⟩

end Nanodregg.Lang.Contextual
