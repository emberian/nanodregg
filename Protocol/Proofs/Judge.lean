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

theorem sameOps_iff (a b : List Op) : sameOps a b = true ↔ ∀ op, op ∈ a ↔ op ∈ b := by
  simp only [sameOps, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem]
  constructor
  · rintro ⟨h1, h2⟩ op; exact ⟨h1 op, h2 op⟩
  · intro h; exact ⟨fun op m => (h op).1 m, fun op m => (h op).2 m⟩

theorem judge_exe_pass_iff {r : Row} {o : Observed} {n : String} {args : List String} {last : String}
    (h : r.drive = .exe n args last) : judge r o = .pass ↔ o.exit = 0 ∧ o.last = last := by
  unfold judge; rw [h]
  by_cases he : o.exit = 0 <;> by_cases hl : o.last = last <;> simp [he, hl]

/-- A member row passes iff every line got its declared outcome and the operations observed on the
wire are exactly the declared ones. -/
theorem judge_members_pass_iff {r : Row} {o : Observed} {ls : List Line}
    (h : r.drive = .members ls) :
    judge r o = .pass ↔ o.outcomes = ls.map Line.expect ∧ ∀ op, op ∈ o.ops ↔ op ∈ r.ops := by
  unfold judge; rw [h]
  cases hm : mismatch 0 o.outcomes (ls.map Line.expect) with
  | some why =>
      have : o.outcomes ≠ ls.map Line.expect := fun he => by
        rw [(mismatch_none_iff 0 _ _).mpr he] at hm; cases hm
      simp only [hm]; simp [this]
  | none =>
      have he := (mismatch_none_iff 0 _ _).mp hm
      simp only [hm]
      by_cases hs : sameOps o.ops r.ops = true
      · simp [hs, he, (sameOps_iff _ _).mp hs]
      · have : ¬ ∀ op, op ∈ o.ops ↔ op ∈ r.ops := fun hh => hs ((sameOps_iff _ _).mpr hh)
        simp [hs, he, this]

end Nanodregg.Protocol
