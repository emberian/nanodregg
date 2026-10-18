/-
# Protocol.Proofs.Use — what the use count counts

`mem_shared`: an object is counted exactly when a committed call uses it and is signed for a member
other than the object's maker. `shared_self`: calls each signed for the maker of what they use count
nothing (the plant `oneMember` is a run of that shape). `shared_nodup`: each object counts once.
-/
import Protocol.Use

namespace Nanodregg.Protocol.Use

open Nanodregg.Kernel Nanodregg.Kernel.Receive

variable {D : Type} [Ord D] [DecidableEq D]

omit [Ord D] in
theorem mem_uniq {o : D} : ∀ {l : List D}, o ∈ uniq l ↔ o ∈ l
  | [] => by simp [uniq]
  | x :: xs => by
    unfold uniq
    split
    · rename_i hx
      rw [mem_uniq, List.mem_cons]
      constructor
      · exact Or.inr
      · rintro (rfl | h)
        · exact mem_uniq.mp hx
        · exact h
    · rw [List.mem_cons, List.mem_cons, mem_uniq]

omit [Ord D] in
theorem nodup_uniq : ∀ (l : List D), (uniq l).Nodup
  | [] => by simp [uniq]
  | x :: xs => by
    unfold uniq
    split
    · exact nodup_uniq xs
    · rename_i hx
      exact List.nodup_cons.mpr ⟨hx, nodup_uniq xs⟩

theorem sharedBy_eq_some {X : Ctx D} {w : World D} {c : Call D} {o : D} :
    sharedBy X w c = some o ↔ ∃ m maker, usedBy c = some (m, o) ∧ makerOf X w o = some maker ∧ maker ≠ m := by
  unfold sharedBy
  constructor
  · intro h
    obtain ⟨⟨m, o'⟩, hu, h⟩ := Option.bind_eq_some_iff.mp h
    dsimp only at h
    split at h
    · rename_i maker hmk
      split at h
      · cases h
      · rename_i hne
        cases h
        exact ⟨m, maker, hu, hmk, hne⟩
    · cases h
  · rintro ⟨m, maker, hu, hmk, hne⟩
    rw [hu]
    simp [hmk, hne]

/-- **An object counts exactly when someone other than its maker used it.** -/
theorem mem_shared {X : Ctx D} {w : World D} {calls : List (Call D)} {o : D} :
    o ∈ shared X w calls ↔
      ∃ c ∈ calls, ∃ m maker, usedBy c = some (m, o) ∧ makerOf X w o = some maker ∧ maker ≠ m := by
  unfold shared
  rw [mem_uniq, List.mem_filterMap]
  constructor
  · rintro ⟨c, hc, h⟩
    exact ⟨c, hc, sharedBy_eq_some.mp h⟩
  · rintro ⟨c, hc, h⟩
    exact ⟨c, hc, sharedBy_eq_some.mpr h⟩

/-- **Self-use counts nothing**: if every call that uses an object is signed for that object's
maker, the count is 0, however many calls there are. -/
theorem shared_self {X : Ctx D} {w : World D} {calls : List (Call D)}
    (h : ∀ c ∈ calls, ∀ m o, usedBy c = some (m, o) → makerOf X w o = some m) :
    shared X w calls = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro o ho
  obtain ⟨c, hc, m, maker, hu, hmk, hne⟩ := mem_shared.mp ho
  rw [h c hc m o hu] at hmk
  cases hmk
  exact hne rfl

theorem shared_nodup (X : Ctx D) (w : World D) (calls : List (Call D)) : (shared X w calls).Nodup :=
  nodup_uniq _

end Nanodregg.Protocol.Use
