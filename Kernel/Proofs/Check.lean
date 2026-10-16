/-
# Kernel.Proofs.Check — what the fail-closed combinators guarantee when they pass
-/
import Kernel.Check

namespace Nanodregg.Kernel

theorem req_ok {ε : Type} {b : Bool} {e : ε} : req b e = .ok () ↔ b = true := by
  unfold req; cases b <;> simp

theorem except_bind_ok {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {b : β} :
    (x >>= f) = .ok b ↔ ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x <;> simp [bind, Except.bind]

theorem forEx_ok {α ε : Type} {f : α → Except ε Unit} :
    ∀ {l : List α}, forEx f l = .ok () ↔ ∀ a ∈ l, f a = .ok ()
  | [] => by simp [forEx]
  | a :: rest => by
      unfold forEx
      cases h : f a with
      | error e => simp [h]
      | ok u => cases u; simp [h, forEx_ok]

/-- What `mapEx` returns lines up with its input: any projection the function fixes is fixed. -/
theorem mapEx_map {α β γ ε : Type} {f : α → Except ε β} {g : β → γ} {k : α → γ}
    (hf : ∀ a b, f a = .ok b → g b = k a) :
    ∀ {l : List α} {bs : List β}, mapEx f l = .ok bs → bs.map g = l.map k
  | [], bs, h => by simp [mapEx] at h; subst h; rfl
  | a :: rest, bs, h => by
      unfold mapEx at h
      cases ha : f a with
      | error e => simp [ha] at h
      | ok b =>
          cases hr : mapEx f rest with
          | error e => simp [ha, hr] at h
          | ok bs' =>
              simp [ha, hr] at h; subst h
              simp [hf a b ha, mapEx_map hf hr]

/-- Every element of `mapEx`'s output is some input's image. -/
theorem mapEx_mem {α β ε : Type} {f : α → Except ε β} :
    ∀ {l : List α} {bs : List β}, mapEx f l = .ok bs → ∀ b ∈ bs, ∃ a ∈ l, f a = .ok b
  | [], bs, h => by simp [mapEx] at h; subst h; simp
  | a :: rest, bs, h => by
      unfold mapEx at h
      cases ha : f a with
      | error e => simp [ha] at h
      | ok b =>
          cases hr : mapEx f rest with
          | error e => simp [ha, hr] at h
          | ok bs' =>
              simp [ha, hr] at h; subst h
              intro x hx
              simp only [List.mem_cons] at hx
              rcases hx with hx | hx
              · exact ⟨a, by simp, hx ▸ ha⟩
              · obtain ⟨a', ha', hfa⟩ := mapEx_mem hr x hx
                exact ⟨a', by simp [ha'], hfa⟩

theorem firstDup_go_none {α : Type} [Ord α] [Std.TransOrd α] [Std.LawfulEqOrd α] :
    ∀ {seen : Std.TreeSet α compare} {l : List α}, firstDup.go seen l = none →
      l.Nodup ∧ ∀ a ∈ l, seen.contains a = false
  | seen, [], _ => by simp
  | seen, a :: rest, h => by
      unfold firstDup.go at h
      by_cases hs : seen.contains a = true
      · simp [hs] at h
      · simp [hs] at h
        obtain ⟨hnd, hnot⟩ := firstDup_go_none h
        have hnot' : ∀ x ∈ rest, x ≠ a ∧ seen.contains x = false := by
          intro x hx
          have := hnot x hx
          rw [Std.TreeSet.contains_insert] at this
          simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq] at this
          refine ⟨?_, this.2⟩
          intro hxa; exact this.1 (by rw [hxa]; exact Std.LawfulEqCmp.compare_eq_iff_eq.mpr rfl)
        refine ⟨List.nodup_cons.mpr ⟨fun ha => (hnot' a ha).1 rfl, hnd⟩, ?_⟩
        intro x hx
        simp only [List.mem_cons] at hx
        rcases hx with hx | hx
        · subst hx; simpa using (Bool.eq_false_iff.mpr hs)
        · exact (hnot' x hx).2

/-- `firstDup` finding nothing means there is nothing to find. -/
theorem firstDup_none {α : Type} [Ord α] [Std.TransOrd α] [Std.LawfulEqOrd α] {l : List α}
    (h : firstDup l = none) : l.Nodup :=
  (firstDup_go_none h).1

end Nanodregg.Kernel
