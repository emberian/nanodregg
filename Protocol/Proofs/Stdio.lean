/-
# Protocol.Proofs.Stdio — the stdio surface excludes exactly init, rotate and adopt
-/
import Protocol.Command.Stdio
import Protocol.Proofs.Command

namespace Nanodregg.Protocol.Command

/-- A verb is on the stdio surface exactly when it is none of the three excluded ones. -/
theorem mem_stdioVerbs (v : Verb) : v ∈ stdioVerbs ↔ v ≠ .init ∧ v ≠ .rotate ∧ v ≠ .adopt := by
  cases v <;> decide

/-- What nd checks: a verb's word is on the emitted list exactly when the verb is on the surface. -/
theorem word_mem_stdioWords (v : Verb) :
    v.word ∈ stdioWords ↔ v ≠ .init ∧ v ≠ .rotate ∧ v ≠ .adopt := by
  cases v <;> decide

/-- **What nd's check means, for any string it receives**: a word is on the emitted list exactly
when it reads back as a verb whose `onStdio` arm is true. -/
theorem mem_stdioWords_iff (w : String) :
    w ∈ stdioWords ↔ ∃ v, Verb.ofWord? w = some v ∧ v.onStdio = true := by
  constructor
  · intro h
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp h
    exact ⟨v, Verb.ofWord?_word v, (List.mem_filter.mp hv).2⟩
  · rintro ⟨v, hw, hs⟩
    have hx : v.word = w := by
      unfold Verb.ofWord? at hw
      have := List.find?_some hw
      simpa using this
    subst hx
    exact List.mem_map.mpr ⟨v, List.mem_filter.mpr ⟨Verb.mem_all v, hs⟩, rfl⟩

theorem init_not_on_surface : Verb.init.word ∉ stdioWords := by decide
theorem rotate_not_on_surface : Verb.rotate.word ∉ stdioWords := by decide
theorem adopt_not_on_surface : Verb.adopt.word ∉ stdioWords := by decide

end Nanodregg.Protocol.Command

namespace Nanodregg.Protocol.StdioRefusal

theorem name_injective (a b : StdioRefusal) (h : a.name = b.name) : a = b := by
  cases a <;> cases b <;> first | rfl | (simp [name] at h)

theorem code_injective (a b : StdioRefusal) (h : a.code = b.code) : a = b := by
  cases a <;> cases b <;> first | rfl | (simp [code] at h)

end Nanodregg.Protocol.StdioRefusal
