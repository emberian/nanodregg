/-
# Protocol.Proofs.Judge — a row passes exactly when its driver saw what it declares
-/
import Protocol.Rows.Judge
import Protocol.Proofs.Table

namespace Nanodregg.Protocol

theorem mismatch_none_iff : ∀ (i : Nat) (gs es : List Expect), mismatch i gs es = none ↔ gs = es
  | _, [], [] => by simp [mismatch]
  | _, [], _ :: _ => by simp [mismatch]
  | _, _ :: _, [] => by simp [mismatch]
  | i, g :: gs, e :: es => by
      by_cases h : g = e
      · subst h; simp [mismatch, mismatch_none_iff (i + 1) gs es]
      · simp [mismatch, h]

theorem sameSet_iff {α : Type} [BEq α] [LawfulBEq α] (a b : List α) :
    sameSet a b = true ↔ ∀ x, x ∈ a ↔ x ∈ b := by
  simp only [sameSet, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem]
  constructor
  · rintro ⟨h1, h2⟩ op; exact ⟨h1 op, h2 op⟩
  · intro h; exact ⟨fun op m => (h op).1 m, fun op m => (h op).2 m⟩

theorem judge_exe_pass_iff {r : Row} {o : Observed} {n : String} {args : List String} {last : String}
    (h : r.drive = .exe n args last) : judge r o = .pass ↔ o.exit = 0 ∧ o.last = last := by
  unfold judge; rw [h]
  by_cases he : o.exit = 0 <;> by_cases hl : o.last = last <;> simp [he, hl]

/-- A member row passes iff every line got its declared outcome, the operations observed on the
wire are exactly the declared ones, and so are the kinds of the calls the clients froze. -/
theorem judge_members_pass_iff {r : Row} {o : Observed} {ls : List Line}
    (h : r.drive = .members ls) :
    judge r o = .pass ↔ o.outcomes = ls.map Line.expect ∧ (∀ op, op ∈ o.ops ↔ op ∈ r.ops) ∧
      ∀ k, k ∈ o.kinds ↔ k ∈ r.kinds := by
  unfold judge; rw [h]
  cases hm : mismatch 0 o.outcomes (ls.map Line.expect) with
  | some why =>
      have : o.outcomes ≠ ls.map Line.expect := fun he => by
        rw [(mismatch_none_iff 0 _ _).mpr he] at hm; cases hm
      simp only [hm]; split <;> simp [this]
  | none =>
      have he := (mismatch_none_iff 0 _ _).mp hm
      simp only [hm]
      by_cases hs : sameSet o.ops r.ops = true
      · by_cases hk : sameSet o.kinds r.kinds = true
        · simp [hs, hk, he, (sameSet_iff _ _).mp hs, (sameSet_iff _ _).mp hk]
        · have : ¬ ∀ k, k ∈ o.kinds ↔ k ∈ r.kinds := fun hh => hk ((sameSet_iff _ _).mpr hh)
          simp [hs, hk, he, this]
      · have : ¬ ∀ op, op ∈ o.ops ↔ op ∈ r.ops := fun hh => hs ((sameSet_iff _ _).mpr hh)
        simp [hs, he, this]

/-- Every row's plant targets a line it has, with an outcome other than the declared one. -/
theorem plants_differ : rows.all Row.plantDiffers = true := by decide

end Nanodregg.Protocol
