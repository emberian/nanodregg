/-
# Lang.Proofs.PrintParse — the reader's parser gives back the form the printer wrote

`sexp_chars`: `Read.sexp` over `Print.chars x` returns `x` up to offsets (`Same`), for a form whose
atoms are atoms and whose strings hold no `"` (`Ok`), within the reader's depth (`Print.need`) and list cap (`Print.width`).
`sexps_items` is the same for the elements of a list under any whitespace separator (`Sep`), and
`parse_text` / `parse_layout` are the two entry points `Lang.Proofs.Print` uses: one form, and a
package laid out one section per line.
-/
import Lang.Print

namespace Nanodregg.Lang.Print

open Read

mutual
/-- A form whose text reads back as itself: atoms are nonempty and delimiter-free, strings hold no `"`. -/
inductive Ok : SExp → Prop
  | atom {p : Nat} {s : String} : s.toList ≠ [] → (∀ c ∈ s.toList, isDelim c = false) → Ok (.atom p s)
  | str {p : Nat} {s : String} : '"' ∉ s.toList → Ok (.str p s)
  | list {p : Nat} {xs : List SExp} : OkL xs → Ok (.list p xs)

inductive OkL : List SExp → Prop
  | nil : OkL []
  | cons {x : SExp} {xs : List SExp} : Ok x → OkL xs → OkL (x :: xs)
end

mutual
/-- The same form, whatever the offsets. -/
inductive Same : SExp → SExp → Prop
  | atom {p q : Nat} {s : String} : Same (.atom p s) (.atom q s)
  | str {p q : Nat} {s : String} : Same (.str p s) (.str q s)
  | list {p q : Nat} {xs ys : List SExp} : SameL xs ys → Same (.list p xs) (.list q ys)

inductive SameL : List SExp → List SExp → Prop
  | nil : SameL [] []
  | cons {x y : SExp} {xs ys : List SExp} : Same x y → SameL xs ys → SameL (x :: xs) (y :: ys)
end

theorem skip_ws : ∀ (ws : List Char) (p : Nat) (cs : List Char), (∀ c ∈ ws, c.isWhitespace = true) →
    skip p (ws ++ cs) = skip (p + ws.length) cs
  | [], p, cs, _ => by simp
  | w :: ws, p, cs, h => by
    have hw : w.isWhitespace = true := h w (List.mem_cons_self ..)
    simp only [List.cons_append, skip, hw, if_true]
    rw [skip_ws ws (p + 1) cs (fun c hc => h c (List.mem_cons_of_mem _ hc))]
    simp only [List.length_cons]; congr 1; omega

theorem skip_stop {c : Char} (p : Nat) (cs : List Char) (hw : c.isWhitespace = false) (hs : c ≠ ';') :
    skip p (c :: cs) = (p, c :: cs) := by
  simp [skip, hw, hs]

/-- What a printed form starts with: never whitespace, a comment, or a `)`. -/
theorem chars_head : ∀ {x : SExp}, Ok x → ∃ c cs, chars x = c :: cs ∧ c.isWhitespace = false ∧
    c ≠ ';' ∧ c ≠ ')'
  | .atom _ s, .atom hne hd => by
    match h : s.toList, hne with
    | c :: cs, _ =>
      have hc := hd c (by rw [h]; exact List.mem_cons_self ..)
      refine ⟨c, cs, by simp [chars, h], ?_, ?_, ?_⟩ <;> simp_all [isDelim]
  | .str _ s, .str _ => ⟨'"', _, rfl, by decide, by decide, by decide⟩
  | .list _ xs, .list _ => ⟨'(', _, rfl, by decide, by decide, by decide⟩

theorem takeWhile_stop {s rest : List Char} (hs : ∀ c ∈ s, isDelim c = false)
    (hr : rest = [] ∨ ∃ c r, rest = c :: r ∧ isDelim c = true) :
    (s ++ rest).takeWhile (fun c => !isDelim c) = s ∧ (s ++ rest).dropWhile (fun c => !isDelim c) = rest := by
  induction s with
  | nil =>
    rcases hr with rfl | ⟨c, r, rfl, hc⟩
    · simp
    · simp [hc]
  | cons a s ih =>
    have ha := hs a (List.mem_cons_self ..)
    obtain ⟨h1, h2⟩ := ih (fun c hc => hs c (List.mem_cons_of_mem _ hc))
    simp [ha, h1, h2]

theorem str_body {s rest : List Char} (hs : '"' ∉ s) :
    (s ++ '"' :: rest).takeWhile (· ≠ '"') = s ∧ (s ++ '"' :: rest).dropWhile (· ≠ '"') = '"' :: rest := by
  induction s with
  | nil => simp
  | cons a s ih =>
    have ha : a ≠ '"' := fun h => hs (h ▸ List.mem_cons_self ..)
    obtain ⟨h1, h2⟩ := ih (fun h => hs (List.mem_cons_of_mem _ h))
    simp only [List.cons_append, List.takeWhile_cons, List.dropWhile_cons, ne_eq, ha,
      not_false_eq_true, decide_true, if_true, h1, h2, and_self]

/-- A list's items with a whitespace separator. -/
def Sep (sep : List Char) : Prop := sep ≠ [] ∧ ∀ c ∈ sep, c.isWhitespace = true

theorem items_head {sep : List Char} (rest : List Char) : ∀ {xs : List SExp}, OkL xs →
    ∃ c cs, items sep xs ++ rest = c :: cs ∧ c.isWhitespace = false ∧ c ≠ ';'
  | [], _ => ⟨')', rest, rfl, by decide, by decide⟩
  | [_], .cons hx _ => by
    obtain ⟨c, cs, hc, hw, hs, _⟩ := chars_head hx
    exact ⟨c, cs ++ ')' :: rest, by simp [items, hc], hw, hs⟩
  | x :: y :: ys, .cons hx _ => by
    obtain ⟨c, cs, hc, hw, hs, _⟩ := chars_head hx
    exact ⟨c, cs ++ (sep ++ (items sep (y :: ys) ++ rest)), by simp [items, hc], hw, hs⟩

theorem skip_items {sep : List Char} (p : Nat) (rest : List Char) {xs : List SExp} (h : OkL xs) :
    skip p (items sep xs ++ rest) = (p, items sep xs ++ rest) := by
  obtain ⟨c, cs, hc, hw, hs⟩ := items_head rest (sep := sep) h
  rw [hc, skip_stop p cs hw hs]

theorem sexpsWith_ws (elem : Nat → List Char → P (SExp × Nat × List Char)) (o n p : Nat) (ws cs : List Char)
    (acc : List SExp) (h : ∀ c ∈ ws, c.isWhitespace = true) :
    sexpsWith elem o n p (ws ++ cs) acc = sexpsWith elem o n (p + ws.length) cs acc := by
  rw [sexpsWith, sexpsWith, skip_ws ws p cs h]

theorem sexp_atom (d p : Nat) (s : String) (rest : List Char) (hne : s.toList ≠ [])
    (hd : ∀ c ∈ s.toList, isDelim c = false) (hr : rest = [] ∨ ∃ c r, rest = c :: r ∧ isDelim c = true) :
    sexp (d + 1) p (s.toList ++ rest) = .ok (.atom p s, p + s.toList.length, rest) := by
  obtain ⟨h1, h2⟩ := takeWhile_stop hd hr
  match hc : s.toList, hne with
  | c :: cs, _ =>
    have hc0 : isDelim c = false := hd c (by rw [hc]; exact List.mem_cons_self ..)
    have hw : c.isWhitespace = false := by simp_all [isDelim]
    have hsc : c ≠ ';' := by intro h; simp_all [isDelim]
    have hl : c ≠ '(' := by intro h; simp_all [isDelim]
    have hq : c ≠ '"' := by intro h; simp_all [isDelim]
    have hp : c ≠ ')' := by intro h; simp_all [isDelim]
    rw [hc] at h1 h2
    rw [sexp, List.cons_append, skip_stop p _ hw hsc]
    split
    · simp_all
    · simp_all
    · simp_all
    · simp_all
    · rename_i heq
      simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      rw [← List.cons_append, h1, h2, ← hc]
      simp

theorem sexp_str (d p : Nat) (s : String) (rest : List Char) (hq : '"' ∉ s.toList) :
    ∃ q, sexp (d + 1) p (chars (.str 0 s) ++ rest) = .ok (.str p s, q, rest) := by
  obtain ⟨h1, h2⟩ := str_body (rest := rest) hq
  simp only [chars, List.cons_append, List.append_assoc]
  rw [sexp, skip_stop p _ (by decide) (by decide)]
  simp only [List.nil_append, h1, h2, String.ofList_toList]
  exact ⟨_, rfl⟩

theorem need_pos (x : SExp) : 1 ≤ need x := by cases x <;> simp [need]

theorem needs_cons {x : SExp} {xs : List SExp} {d : Nat} (h : needs (x :: xs) ≤ d) :
    need x ≤ d ∧ needs xs ≤ d := by
  simp only [needs] at h; omega

theorem widths_cons {x : SExp} {xs : List SExp} {w : Nat} (h : widths (x :: xs) ≤ w) :
    width x ≤ w ∧ widths xs ≤ w := by
  simp only [widths] at h; omega

mutual
theorem sexp_chars : ∀ (d : Nat) {x : SExp}, Ok x → need x ≤ d → width x ≤ listMax → ∀ (p : Nat)
    (rest : List Char), (rest = [] ∨ ∃ c r, rest = c :: r ∧ isDelim c = true) →
    ∃ y q, sexp d p (chars x ++ rest) = .ok (y, q, rest) ∧ Same x y
  | 0, x, _, hn, _, _, _, _ => absurd hn (by have := need_pos x; omega)
  | d + 1, .atom _ s, .atom hne hd, _, _, p, rest, hr =>
    ⟨_, _, sexp_atom d p s rest hne hd hr, .atom⟩
  | d + 1, .str _ s, .str hq, _, _, p, rest, _ => by
    obtain ⟨q, h⟩ := sexp_str d p s rest hq
    exact ⟨_, q, by simpa [chars] using h, .str⟩
  | d + 1, .list _ xs, .list hxs, hn, hw, p, rest, _ => by
    simp only [need] at hn
    simp only [width] at hw
    obtain ⟨ys, q, hys, hsame⟩ :=
      sexps_items d [' '] ⟨by decide, by decide⟩ hxs (by omega) (by omega) listMax p (p + 1) rest []
        (by omega)
    refine ⟨.list p ys, q, ?_, .list hsame⟩
    rw [sexp, chars, List.cons_append, skip_stop p _ (by decide) (by decide)]
    simp only [skip_items (p + 1) rest hxs, hys, List.reverse_nil, List.nil_append, Except.map]

theorem sexps_items : ∀ (d : Nat) (sep : List Char), Sep sep → ∀ {xs : List SExp}, OkL xs →
    needs xs ≤ d → widths xs ≤ listMax → ∀ (n o p : Nat) (rest : List Char) (acc : List SExp),
    xs.length ≤ n →
    ∃ ys q, sexpsWith (fun p cs => sexp d p cs) o n p (items sep xs ++ rest) acc = .ok (acc.reverse ++ ys, q, rest) ∧
      SameL xs ys
  | d, _, _, [], _, _, _, n, o, p, rest, acc, _ => by
    refine ⟨[], p + 1, ?_, .nil⟩
    rw [sexpsWith]
    simp [items, skip]
  | d, sep, hsep, [x], .cons hx _, hn, hw, n, o, p, rest, acc, hl => by
    obtain ⟨hnx, -⟩ := needs_cons hn
    obtain ⟨hwx, -⟩ := widths_cons hw
    obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp at hl; omega⟩
    obtain ⟨y, q, hy, hxy⟩ := sexp_chars d hx hnx hwx p (')' :: rest) (.inr ⟨')', rest, rfl, by decide⟩)
    obtain ⟨ys, q', hys, hnil⟩ := sexps_items d sep hsep .nil (by simp [needs]) (by simp [widths]) n o q rest
      (y :: acc) (by simp)
    cases hnil
    refine ⟨[y], q', ?_, .cons hxy .nil⟩
    obtain ⟨c, cs, hc, hw, hs, hcp⟩ := chars_head hx
    have e : items sep [x] ++ rest = c :: (cs ++ ')' :: rest) := by simp [items, hc]
    rw [e, sexpsWith, skip_stop p _ hw hs]
    split
    · rename_i heq; simp only [Prod.mk.injEq, List.cons.injEq] at heq; exact absurd heq.2.1 hcp
    · simp_all
    · rename_i heq
      simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      simp only
      rw [show c :: (cs ++ ')' :: rest) = chars x ++ ')' :: rest by simp [hc], hy]
      simpa using hys
  | d, sep, hsep, x :: y :: ys, .cons hx hys, hn, hw, n, o, p, rest, acc, hl => by
    obtain ⟨hnx, hnr⟩ := needs_cons hn
    obtain ⟨hwx, hwr⟩ := widths_cons hw
    obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp at hl; omega⟩
    obtain ⟨s0, sr, hs0, hws⟩ : ∃ s0 sr, sep = s0 :: sr ∧ s0.isWhitespace = true := by
      match sep, hsep with
      | s0 :: sr, ⟨_, h⟩ => exact ⟨s0, sr, rfl, h s0 (List.mem_cons_self ..)⟩
    obtain ⟨x', q, hx', hxx⟩ := sexp_chars d hx hnx hwx p (sep ++ items sep (y :: ys) ++ rest)
      (.inr ⟨s0, sr ++ items sep (y :: ys) ++ rest, by simp [hs0], by simp [isDelim, hws]⟩)
    obtain ⟨ys', q', hys', hsame⟩ :=
      sexps_items d sep hsep hys hnr hwr n o (q + sep.length) rest (x' :: acc) (by simp at hl ⊢; omega)
    refine ⟨x' :: ys', q', ?_, .cons hxx hsame⟩
    obtain ⟨c, cs, hc, hw, hs, hcp⟩ := chars_head hx
    have e : items sep (x :: y :: ys) ++ rest = c :: (cs ++ (sep ++ items sep (y :: ys) ++ rest)) := by
      simp [items, hc]
    rw [e, sexpsWith, skip_stop p _ hw hs]
    split
    · rename_i heq; simp only [Prod.mk.injEq, List.cons.injEq] at heq; exact absurd heq.2.1 hcp
    · simp_all
    · rename_i heq
      simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      simp only
      rw [show c :: (cs ++ (sep ++ items sep (y :: ys) ++ rest)) = chars x ++ (sep ++ items sep (y :: ys) ++ rest)
        by simp [hc], hx']
      simp only
      rw [List.append_assoc, sexpsWith_ws _ o n q sep _ _ hsep.2, hys']
      simp
end

theorem parse_text {x : SExp} (h : Ok x) (hn : need x ≤ depthMax) (hw : width x ≤ listMax) :
    ∃ y, parse (text x) = .ok y ∧ Same x y := by
  obtain ⟨y, q, hy, hs⟩ := sexp_chars depthMax h hn hw 0 [] (.inl rfl)
  refine ⟨y, ?_, hs⟩
  simp only [parse, text, String.toList_ofList]
  rw [← List.append_nil (chars x), hy]
  simp [skip]

theorem parse_layout {sep : List Char} (hsep : Sep sep) {xs : List SExp} (h : OkL xs)
    (hn : need (.list 0 xs) ≤ depthMax) (hw : width (.list 0 xs) ≤ listMax) :
    ∃ ys, parse (String.ofList ('(' :: items sep xs ++ ['\n'])) = .ok (.list 0 ys) ∧ SameL xs ys := by
  simp only [need] at hn
  simp only [width] at hw
  obtain ⟨ys, q, hys, hsame⟩ :=
    sexps_items (depthMax - 1) sep hsep h (by omega) (by omega) listMax 0 1 ['\n'] [] (by omega)
  refine ⟨ys, ?_, hsame⟩
  simp only [depthMax] at hys
  simp only [parse, String.toList_ofList, depthMax]
  rw [sexp, List.cons_append, skip_stop 0 _ (by decide) (by decide)]
  simp only [skip_items 1 ['\n'] h]
  simp [hys, Except.map, skip]

end Nanodregg.Lang.Print
