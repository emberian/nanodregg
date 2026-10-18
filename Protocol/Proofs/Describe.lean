/-
# Protocol.Proofs.Describe — a description's method line is the method `invoke` resolves

`methodLine_resolves`: the line `method I LABEL ARG` printed for index I is `Lang.resolveMethod`'s
answer at I. The label is the one `invoke OBJ I` runs, and ARG is `Lang.Print.ty` of the argument type
`Lang.argsOf` reads ARGS at (it asks `resolveMethod` too). So a call made from the text alone names the
method the text names, at the type the text prints. The printer's round trip (`Lang.Proofs.Print`)
makes ARG the text `Lang.Read` reads back as that type.
-/
import Protocol.Command.Describe

namespace Nanodregg.Protocol.Command

variable {D : Type} [Ord D] [DecidableEq D]

omit [Ord D] [DecidableEq D] in
theorem methodLine_resolves {p : Lang.Package} {i : Nat} {ls : List String}
    (h : methodLine (D := D) p i = some ls) :
    ∃ ℓ A ks a, Lang.resolveMethod (D := D) p i = .ok (ℓ, A, ks) ∧ Lang.Print.ty A = some a ∧
      ls.head? = some s!"method {i} {ℓ} {a}" := by
  unfold methodLine at h
  split at h
  · cases h
  · rename_i ℓ A ks hr
    split at h
    · rename_i a cs ha _
      cases h
      exact ⟨ℓ, A, ks, a, hr, ha, rfl⟩
    · cases h

omit [Ord D] [DecidableEq D] in
theorem mem_of_mapM {α β : Type} {f : α → Option β} :
    ∀ {l : List α} {r : List β}, l.mapM f = some r → ∀ x ∈ l, ∃ y, f x = some y ∧ y ∈ r
  | [], _, _, x, hx => by simp at hx
  | a :: l, r, h, x, hx => by
    rw [List.mapM_cons] at h
    cases hfa : f a with
    | none => simp [hfa] at h
    | some b =>
      cases hl : l.mapM f with
      | none => simp [hfa, hl] at h
      | some bs =>
        simp only [hfa, hl, Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq] at h
        subst h
        rcases List.mem_cons.mp hx with rfl | hx
        · exact ⟨b, hfa, List.mem_cons_self⟩
        · obtain ⟨y, hy, hm⟩ := mem_of_mapM hl x hx
          exact ⟨y, hy, List.mem_cons_of_mem _ hm⟩

omit [Ord D] [DecidableEq D] in
/-- A package's description holds the lines of every method index below the method count: none
is skipped (membership; the order is `packageLines`'s by reading). -/
theorem packageLines_methods {p : Lang.Package} {ls : List String}
    (h : packageLines (D := D) p = some ls) (i : Nat) (hi : i < p.methods.length) :
    ∃ ms, methodLine (D := D) p i = some ms ∧ ∀ l ∈ ms, l ∈ ls := by
  unfold packageLines at h
  cases hs : Lang.Print.ty p.state with
  | none => simp [hs] at h
  | some st =>
    cases hm : (List.range p.methods.length).mapM (methodLine (D := D) p) with
    | none => simp [hs, hm] at h
    | some mss =>
      simp only [hs, hm, Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq] at h
      obtain ⟨ms, hms, hmem⟩ := mem_of_mapM hm i (List.mem_range.mpr hi)
      exact ⟨ms, hms, fun l hl => by rw [← h]; simp; right; left; exact ⟨ms, hmem, hl⟩⟩

end Nanodregg.Protocol.Command
