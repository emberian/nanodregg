/-
# Protocol.Proofs.Describe — a description's method line is the method `invoke` resolves

`methodLine_resolves`: the line `method I LABEL ARG` printed for index I is `Lang.resolveMethod`'s
answer at I. The label is the one `invoke OBJ I` runs, and ARG is `Lang.Print.ty` of the argument type
`Lang.argsOf` reads ARGS at (it asks `resolveMethod` too). So a call made from the text alone names the
method the text names, at the type the text prints. The printer's round trip (`Lang.Proofs.Print`)
makes ARG the text `Lang.Read` reads back as that type.
-/
import Protocol.Command.Describe
import Lang.Proofs.PrintLine

namespace Nanodregg.Protocol.Command

variable {D : Type} [Ord D] [DecidableEq D]

omit [Ord D] [DecidableEq D] in
theorem methodLine_resolves {p : Lang.Package} {i : Nat} {ls : List String}
    (h : methodLine (D := D) p i = some ls) :
    ∃ ℓ sg a cs, Lang.resolveMethod (D := D) p i = .ok (ℓ, sg) ∧ Lang.labelAtom ℓ = true ∧
      sg.arg.wf = true ∧ Lang.Print.ty sg.arg = some a ∧ callLines i sg.calls = some cs ∧
      ls = s!"method {i} {ℓ} {a}" :: cs := by
  unfold methodLine at h
  split at h
  · cases h
  · rename_i ℓ sg hr
    split at h
    · rename_i hok
      simp only [Bool.and_eq_true] at hok
      split at h
      · rename_i a cs ha hc
        cases h
        exact ⟨ℓ, sg, a, cs, hr, hok.1, hok.2, ha, hc, rfl⟩
      · cases h
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
      cases hr : p.rels.mapM relLine with
      | none => simp [hs, hm, hr] at h
      | some rs =>
        simp only [hs, hm, hr, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
          Option.some.injEq] at h
        obtain ⟨ms, hms, hmem⟩ := mem_of_mapM hm i (List.mem_range.mpr hi)
        exact ⟨ms, hms, fun l hl => by
          rw [← h]
          exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
            (List.mem_cons_of_mem _ (List.mem_flatten.mpr ⟨ms, hmem, hl⟩))))⟩

omit [Ord D] [DecidableEq D] in
/-- **Every relation of the package has its line** (PROTOCOL-51): the description holds
`relLine r` (LANG's printer's text of `r`) for every relation `r` the package declares, so a
resident learns the relation, its key fields in declared order and its `limit` from the text. -/
theorem packageLines_rels {p : Lang.Package} {ls : List String}
    (h : packageLines (D := D) p = some ls) (r : Lang.Label × Lang.RelDecl) (hr : r ∈ p.rels) :
    ∃ t, relLine r = some t ∧ t ∈ ls := by
  unfold packageLines at h
  cases hs : Lang.Print.ty p.state with
  | none => simp [hs] at h
  | some st =>
    cases hm : (List.range p.methods.length).mapM (methodLine (D := D) p) with
    | none => simp [hs, hm] at h
    | some mss =>
      cases hrs : p.rels.mapM relLine with
      | none => simp [hs, hm, hrs] at h
      | some rs =>
        simp only [hs, hm, hrs, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
          Option.some.injEq] at h
        obtain ⟨t, ht, hmem⟩ := mem_of_mapM hrs r hr
        exact ⟨t, ht, by rw [← h]; exact List.mem_append_right _ hmem⟩

omit [Ord D] [DecidableEq D] in
/-- **A package's doc has its line, and the line reads back as the doc** (LANG-60): the description's
first line is `doc TEXT` with TEXT LANG's printer's text of the doc, one line (`doc_one_line`), which the one
parser and `Lang.Read.doc` read as exactly the doc's bytes. So the Bell states its own clock and
tie rule in text a member reads from `read OBJ ?`, and that text is the package's. -/
theorem packageLines_doc {p : Lang.Package} {ls : List String}
    (h : packageLines (D := D) p = some ls) (hd : Lang.Bounds.docOk p.doc = true)
    (he : p.doc.isEmpty = false) :
    ls.head? = some s!"doc {Lang.Print.bytesText p.doc}" ∧
      (∀ c ∈ (Lang.Print.bytesText p.doc).toList, c ≠ '\n' ∧ c ≠ '\r') ∧
      ∃ y, Lang.Read.parse (Lang.Print.bytesText p.doc) = .ok y ∧ Lang.Read.doc 0 [y] = .ok p.doc := by
  refine ⟨?_, Lang.Print.doc_one_line hd, Lang.Print.doc_text_reads hd he⟩
  unfold packageLines at h
  cases hs : Lang.Print.ty p.state with
  | none => simp [hs] at h
  | some st =>
    cases hm : (List.range p.methods.length).mapM (methodLine (D := D) p) with
    | none => simp [hs, hm] at h
    | some mss =>
      cases hr : p.rels.mapM relLine with
      | none => simp [hs, hm, hr] at h
      | some rs =>
        simp only [hs, hm, hr, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
          Option.some.injEq] at h
        rw [← h]
        simp [docLines, he]

omit [Ord D] [DecidableEq D] in
/-- The twin: a package with the empty doc describes exactly as before LANG-60 (state, methods, laws,
relations; no doc line). -/
theorem packageLines_no_doc {p : Lang.Package} (he : p.doc.isEmpty = true) :
    packageLines (D := D) p = (do
      let st ← Lang.Print.ty p.state
      let ms ← (List.range p.methods.length).mapM (methodLine (D := D) p)
      let rs ← p.rels.mapM relLine
      pure ((s!"state {st}" :: ms.flatten) ++ p.laws.map (fun ℓ => s!"law {ℓ}") ++ rs)) := by
  simp [packageLines, docLines, he]

end Nanodregg.Protocol.Command
