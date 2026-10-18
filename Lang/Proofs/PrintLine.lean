/-
# Lang.Proofs.PrintLine — a printed value is one line (LANG-56)

`read OBJ` (PROTOCOL-48) prints a programmed object's state as `Lang.Print.data` of it, then one
newline, and a reader of `nd --stdio` reads a reply by lines. `data_one_line`: the printed text holds
no line feed and no carriage return. The printer earns it: a byte string shows as a string literal
only when every character is plain (`plainChar`: no control character, no quote), and as `#hex`
otherwise, which the one reader reads back to the same bytes (`readData_data` is unchanged).
Teeth at the end: a byte string with a line feed prints as hex; plain text prints as itself.
-/
import Lang.Proofs.Print

namespace Nanodregg.Lang.Print

open Read

/-! ## A printed value is one line (PROTOCOL-48: `read OBJ` prints a programmed object's state as one) -/

mutual
/-- Every string of the form is of plain characters (`plainChar`). -/
inductive PlainStrs : SExp → Prop
  | atom {p : Nat} {s : String} : PlainStrs (.atom p s)
  | str {p : Nat} {s : String} : (∀ c ∈ s.toList, plainChar c = true) → PlainStrs (.str p s)
  | list {p : Nat} {xs : List SExp} : PlainStrsL xs → PlainStrs (.list p xs)

inductive PlainStrsL : List SExp → Prop
  | nil : PlainStrsL []
  | cons {x : SExp} {xs : List SExp} : PlainStrs x → PlainStrsL xs → PlainStrsL (x :: xs)
end

/-- No line break. -/
abbrev NoBreak (c : Char) : Prop := c ≠ '\n' ∧ c ≠ '\r'

theorem noBreak_of_not_delim {c : Char} (h : isDelim c = false) : NoBreak c := by
  constructor <;> rintro rfl <;> simp [isDelim] at h <;> exact absurd h (by decide)

theorem noBreak_of_plain {c : Char} (h : plainChar c = true) : NoBreak c := by
  simp only [plainChar, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at h
  constructor <;> rintro rfl <;> simp at h

mutual
theorem chars_noBreak : ∀ {x : SExp}, Ok x → PlainStrs x → ∀ c ∈ chars x, NoBreak c
  | .atom _ s, .atom _ hd, _, c, hc => by simp only [chars] at hc; exact noBreak_of_not_delim (hd c hc)
  | .str _ s, _, .str hp, c, hc => by
    simp only [chars, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | hc | rfl
    · decide
    · exact noBreak_of_plain (hp c hc)
    · decide
  | .list _ xs, .list ho, .list hp, c, hc => by
    simp only [chars, List.mem_cons] at hc
    rcases hc with rfl | hc
    · decide
    · exact items_noBreak ho hp c hc

theorem items_noBreak : ∀ {xs : List SExp}, OkL xs → PlainStrsL xs → ∀ c ∈ items [' '] xs, NoBreak c
  | [], _, _, c, hc => by simp only [items, List.mem_singleton] at hc; subst hc; decide
  | [x], .cons hx _, .cons px _, c, hc => by
    simp only [items, List.mem_append, List.mem_singleton] at hc
    rcases hc with hc | rfl
    · exact chars_noBreak hx px c hc
    · decide
  | x :: y :: ys, .cons hx hr, .cons px pr, c, hc => by
    simp only [items, List.mem_append, List.mem_singleton] at hc
    rcases hc with (hc | rfl) | hc
    · exact chars_noBreak hx px c hc
    · decide
    · exact items_noBreak hr pr c hc
end

mutual
theorem dataSx_plain : ∀ (v : Data) {x : SExp}, dataSx v = some x → PlainStrs x
  | .nat n, _, h => by simp only [dataSx, Option.some.injEq] at h; subst h; exact .atom
  | .bool b, _, h => by simp only [dataSx, Option.some.injEq] at h; subst h; exact .atom
  | .bytes b, _, h => by
    simp only [dataSx, Option.some.injEq] at h; subst h
    rcases bytesSx_cases b with ⟨t, e, -, -, hp⟩ | e <;> rw [e]
    · exact .str hp
    · exact .atom
  | .digest b, _, h => by simp only [dataSx, digestSx, Option.some.injEq] at h; subst h; exact .atom
  | .record fs, _, h => by
    simp only [dataSx, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨xs, hxs, rfl⟩ := h
    exact .list (.cons .atom (dataFieldsSx_plain fs hxs))
  | .inj ℓ v, _, h => by
    simp only [dataSx, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨xl, hl, xv, hv, rfl⟩ := h
    simp only [label] at hl
    split at hl
    · cases hl; exact .list (.cons .atom (.cons (dataSx_plain v hv) .nil))
    · cases hl

theorem dataFieldsSx_plain : ∀ (fs : List (Label × Data)) {xs : List SExp}, dataFieldsSx fs = some xs → PlainStrsL xs
  | [], _, h => by simp only [dataFieldsSx, Option.some.injEq] at h; subst h; exact .nil
  | (ℓ, v) :: fs, _, h => by
    simp only [dataFieldsSx, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨xl, hl, xv, hv, xr, hr, rfl⟩ := h
    simp only [label] at hl
    split at hl
    · cases hl; exact .cons (.list (.cons .atom (.cons (dataSx_plain v hv) .nil))) (dataFieldsSx_plain fs hr)
    · cases hl
end

/-- **A printed value is one line**: `Lang.Print.data`'s text holds no line feed and no carriage
return (a byte string with a control character prints as `#hex`, `bytesSx`). -/
theorem data_one_line {v : Data} {s : String} (h : data v = some s) : ∀ c ∈ s.toList, c ≠ '\n' ∧ c ≠ '\r' := by
  simp only [data, Option.bind_eq_some_iff] at h
  obtain ⟨x, hx, hf⟩ := h
  obtain ⟨-, -, rfl⟩ := fits_some hf
  intro c hc
  simp only [text, String.toList_ofList] at hc
  exact chars_noBreak (dataSx_ok v hx) (dataSx_plain v hx) c hc

/-- The plant's input: text with a line feed prints as `#hex`, so the reply stays one line. -/
theorem newline_bytes_print_hex : data (.bytes "a\nb".toUTF8) = some "#610a62" := by decide +kernel
/-- And its twin: plain text prints as itself. -/
theorem plain_bytes_print_text : data (.bytes "a b".toUTF8) = some "\"a b\"" := by decide +kernel

end Nanodregg.Lang.Print
