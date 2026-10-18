/-
# Kernel.Proofs.JournalHead — the phone reads the journal against a head (KERNEL-41)

The chain commits the journal's root beside the cells' (`chainNext`), so the replay index is
authenticated: a phone that trusts one head can be shown that a transaction id was admitted, or that
it was not.

* `journal_inclusion_sound` / `journal_exclusion_sound`: a proof that verifies against a World's
  journal root tells the truth about the transaction id, or two of the inputs the read compares
  collide (`inclPres`, `readPres`); teeth `*_sep`;
  `journal_prove_verifies` / `journal_prove_absent`: the World proves every entry it holds, and
  every id it does not.
* `head_journal_read` / `head_journal_absent`: the same against a head record
  `(prev, kind, turnDigest, rd)` that hashes to the chain an admitted turn reached, with `rd` opened
  to `(root', jroot', rroot')` (`rootsDigest`, KERNEL-47).
* `head_absent_admitted`: exclusion is an answer exactly while `journalForgets` is false. A turn
  admitted from `w₀` cannot be shown absent against the head of any World its log reaches below
  `notBefore + 2 * windowMax` (`fold_answers`), but by a collision among the inputs the opening and
  the read compare (`head_absent_admitted_sep`: under `Separates` of those, never). Past it, an
  exclusion proof is sound about the journal (`head_journal_absent`) and says nothing about the
  call: its entry may have been pruned (HOST's `forgotten`).
Premises: `hE : E.Lawful n` with `0 < n` (a digest of no bytes cannot tell an empty leaf from a full
one: `journalBody_inj`), and the journal's invariant `JournalOk` at the World the turn left (every
reached World's: `Receive.reach_journalOk`). A claimed entry's height is below 2^64 (the leaf
digest's `nat64` is injective there; every reached World's heights are: `admit_height_lt`).
-/
import Kernel.Proofs.Cells
import Kernel.Proofs.Journal

namespace Nanodregg.Kernel

variable {D : Type} [Ord D] [DecidableEq D]

/-- An admitted World's height is below 2^64: the turn's `validUntil` is (`checkBounds`), and the
World lands inside the turn's window. -/
theorem admit_height_lt {E : Env D} {w w' : World D} {t : Turn D} (h : World.admit E w t = .ok w') :
    w'.height < 2 ^ 64 := by
  have hw := (admit_window h).2
  have hb := admit_bounded h
  unfold checkBounds at hb
  simp only [except_bind_ok] at hb
  obtain ⟨⟨⟩, _, ⟨⟩, _, ⟨⟩, _, ⟨⟩, _, ⟨⟩, _, ⟨⟩, _, ⟨⟩, _, ⟨⟩, _, ⟨⟩, _, ⟨⟩, _, ⟨⟩, hc, -⟩ := hb
  rw [req_ok] at hc
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hc
  rw [admit_height h]
  have : Bounds.counterLimit = 2 ^ 64 := by decide
  omega

/-- Every journal entry of an admitted World with `JournalOk` has a height below 2^64. -/
theorem admit_journal_heights {E : Env D} {w w' : World D} {t : Turn D} (hw : w.JournalOk E)
    (h : World.admit E w t = .ok w') : ∀ k e, w'.journalAt E k = some e → e.1 < 2 ^ 64 := by
  intro k e he
  have := ((admit_journalOk hw h).2.1 k e he).1
  have := admit_height_lt h
  omega

omit [DecidableEq D] in
theorem journalPre_inj {E : Env D} {n : Nat} (hE : E.Lawful n) {e e' : Nat × D}
    (he : e.1 < 2 ^ 64) (he' : e'.1 < 2 ^ 64) (h : journalPre E e = journalPre E e') : e = e' := by
  obtain ⟨h1, h2⟩ := bytes_append_inj (congrArg Prod.snd h) rfl
  exact Prod.ext (Nanodregg.Codec.Stream.nat64_lawfulOn.bytes_injective he he' h1) (hE.bytes_inj h2)

omit [DecidableEq D] in
/-- A journal leaf digest determines its entry below 2^64, or the two inputs collide (in
`domJournal`). -/
theorem journalDigest_inj {E : Env D} {n : Nat} (hE : E.Lawful n) {e e' : Nat × D}
    (he : e.1 < 2 ^ 64) (he' : e'.1 < 2 ^ 64)
    (h : journalDigest E e = journalDigest E e') :
    e = e' ∨ CollidesAmong E.hash [journalPre E e, journalPre E e'] := by
  by_cases hb : journalPre E e = journalPre E e'
  · exact .inl (journalPre_inj hE he he' hb)
  · exact .inr (.pair hb h)

section Sound
variable {E : Env D} {n : Nat} (hE : E.Lawful n) (hn : 0 < n)

include hE hn in
omit [DecidableEq D] in
/-- **The journal's trie is a `HeadSound` instance** (KERNEL-52) on entries whose height is below
2^64, at a digest of at least one byte (`journalBody_inj`). -/
theorem journal_headSound : HeadSound E (journalSpec E) (fun e : Nat × D => e.1 < 2 ^ 64) (journalPre E) :=
  ⟨journalBody_inj hE hn, dbytes_pair_inj hE, fun _ => rfl, fun _ => rfl, journalPre_inj hE⟩

include hE hn in
/-- **Journal inclusion is sound at the World**: a claimed entry proved against the journal root is
the World's entry, or two of the inputs the read compares collide. -/
theorem journal_inclusion_sound {w : World D} (hc : w.JournalCanon E)
    (hfit : ∀ k e, w.journalAt E k = some e → e.1 < 2 ^ 64) {k : D} {e : Nat × D} (he : e.1 < 2 ^ 64)
    {p : Trie.Proof D D}
    (hv : Trie.verifyInclusion (journalSpec E) (w.journalRoot E) k (journalDigest E e) p = true) :
    w.journalAt E k = some e ∨ CollidesAmong E.hash (inclPres (journalSpec E) (journalPre E) k e p w.journal) :=
  (journal_headSound hE hn).inclusion hc hfit he hv

include hE hn in
/-- **Journal exclusion is sound at the World**: an id proved absent against the journal root is
not in the World's journal, or two of the inputs the read compares collide. -/
theorem journal_exclusion_sound {w : World D} (hc : w.JournalCanon E) {k : D} {p : Trie.Proof D D}
    (hv : Trie.verifyExclusion (journalSpec E) (w.journalRoot E) k p = true) :
    w.journalAt E k = none ∨ CollidesAmong E.hash (readPres (journalSpec E) k p w.journal) :=
  (journal_headSound hE hn).exclusion hc hv

include hE hn in
/-- **The phone's journal read**: a head record that hashes to the chain an admitted turn reached,
and an inclusion proof against the record's journal root, show the entry in that World's journal,
or two of the inputs the opening and the read compare collide. -/
theorem head_journal_read {w w' : World D} {t : Turn D} (hw : w.JournalOk E)
    (h : World.admit E w t = .ok w') {prev td rd root' jroot' rroot' wroot' : D} {g : UInt8}
    (hhead : headLink E prev g td rd = w'.chain) (hrd : rootsDigest E root' jroot' rroot' wroot' = rd) {k : D} {e : Nat × D} (he : e.1 < 2 ^ 64)
    {p : Trie.Proof D D} (hv : Trie.verifyInclusion (journalSpec E) jroot' k (journalDigest E e) p = true) :
    w'.journalAt E k = some e ∨
      CollidesAmong E.hash (headPres E w [.turn t] w' prev g td rd root' jroot' rroot' wroot' ++
        inclPres (journalSpec E) (journalPre E) k e p w'.journal) :=
  (journal_headSound hE hn).head_read (fun _ j _ _ => j) (admit_journalCanon hw.1 h) rfl
    (admit_journal_heights hw h) (head_roots hE (s := .turn t) h hhead hrd) he hv

include hE hn in
/-- **The phone's journal absence** against a head: the id is not in that World's journal, or two of
the inputs the opening and the read compare collide. -/
theorem head_journal_absent {w w' : World D} {t : Turn D} (hc : w.JournalCanon E)
    (h : World.admit E w t = .ok w') {prev td rd root' jroot' rroot' wroot' : D} {g : UInt8}
    (hhead : headLink E prev g td rd = w'.chain) (hrd : rootsDigest E root' jroot' rroot' wroot' = rd) {k : D} {p : Trie.Proof D D}
    (hv : Trie.verifyExclusion (journalSpec E) jroot' k p = true) :
    w'.journalAt E k = none ∨
      CollidesAmong E.hash (headPres E w [.turn t] w' prev g td rd root' jroot' rroot' wroot' ++
        readPres (journalSpec E) k p w'.journal) :=
  (journal_headSound hE hn).head_absent (fun _ j _ _ => j) (admit_journalCanon hc h) rfl
    (head_roots hE (s := .turn t) h hhead hrd) hv

include hE in
/-- A head record that hashes to the chain of a World a log reached after a step names that World's
four roots, or two of the inputs the opening compares collide (`headPres` over the whole log: the
head is the log's last link). -/
theorem fold_head_roots {w₀ w₁ w₂ : World D} {s : Step D} {l : List (Step D)}
    (h₁ : World.step E w₀ s = .ok w₁) (hf : World.fold E w₁ l = .ok w₂)
    {prev td rd root' jroot' rroot' wroot' : D} {g : UInt8}
    (hhead : headLink E prev g td rd = w₂.chain) (hrd : rootsDigest E root' jroot' rroot' wroot' = rd) :
    (root' = w₂.root E ∧ jroot' = w₂.journalRoot E ∧ rroot' = w₂.refusalsRoot E ∧
      wroot' = w₂.rowsRoot E) ∨
      CollidesAmong E.hash (headPres E w₀ (s :: l) w₂ prev g td rd root' jroot' rroot' wroot') := by
  induction l generalizing w₀ w₁ s with
  | nil =>
      simp [World.fold] at hf; subst hf
      exact head_roots hE h₁ hhead hrd
  | cons u us ih =>
      obtain ⟨w₃, h₃, h₄⟩ := fold_cons_ok.mp hf
      rcases ih h₃ h₄ with hr | col
      · exact .inl hr
      · refine .inr (CollidesAmong.mono (fun x hx => ?_) col)
        have hl : foldLinks E w₀ (s :: u :: us) =
            stepLinkPre E w₀.chain s (w₁.roots E) :: foldLinks E w₁ (u :: us) := by
          simp [foldLinks, h₁]
        simp only [headPres, hl, List.mem_cons] at hx ⊢
        rcases hx with h | h | h | h <;> simp [h]

include hE hn in
/-- **Exclusion while `journalForgets` is false is a refutation of admission.** If `t` was admitted
from `w₀` and its log reaches `w₂`, a World at a height where `journalForgets w₂.height t.notBefore`
is false, no proof shows `t`'s transaction id absent against `w₂`'s head, but by a collision among
the inputs the opening and the read compare. -/
theorem head_absent_admitted {w₀ w₁ w₂ : World D} {t : Turn D} {l : List (Step D)}
    (hc : w₀.JournalCanon E) (h₁ : World.admit E w₀ t = .ok w₁) (hf : World.fold E w₁ l = .ok w₂)
    (hnf : journalForgets w₂.height t.notBefore = false) {prev td rd root' jroot' rroot' wroot' : D} {g : UInt8}
    (hhead : headLink E prev g td rd = w₂.chain) (hrd : rootsDigest E root' jroot' rroot' wroot' = rd)
    {p : Trie.Proof D D}
    (hv : Trie.verifyExclusion (journalSpec E) jroot' t.txId p = true) :
    CollidesAmong E.hash (headPres E w₀ (.turn t :: l) w₂ prev g td rd root' jroot' rroot' wroot' ++
      readPres (journalSpec E) t.txId p w₂.journal) := by
  have hin := fold_answers hc h₁ hf hnf
  have hc₂ := fold_journalCanon (admit_journalCanon hc h₁) hf
  rcases fold_head_roots hE (s := .turn t) h₁ hf hhead hrd with ⟨-, rfl, -, -⟩ | col
  · rcases journal_exclusion_sound hE hn hc₂ hv with hnone | col
    · rw [hin] at hnone; cases hnone
    · exact CollidesAmong.mono (fun x hx => List.mem_append_right _ hx) col
  · exact CollidesAmong.mono (fun x hx => List.mem_append_left _ hx) col

/-! ### Teeth: under `Separates` of the inputs each theorem names, its binding fact alone -/

omit [DecidableEq D] in
include hE in
/-- TOOTH (`journalDigest_inj`). -/
theorem journalDigest_inj_sep {e e' : Nat × D} (he : e.1 < 2 ^ 64) (he' : e'.1 < 2 ^ 64)
    (hsep : Separates E.hash [journalPre E e, journalPre E e'])
    (h : journalDigest E e = journalDigest E e') : e = e' :=
  hsep.elim (journalDigest_inj hE he he' h)

include hE hn in
/-- TOOTH (`journal_inclusion_sound`). -/
theorem journal_inclusion_sound_sep {w : World D} (hc : w.JournalCanon E)
    (hfit : ∀ k e, w.journalAt E k = some e → e.1 < 2 ^ 64) {k : D} {e : Nat × D} (he : e.1 < 2 ^ 64)
    {p : Trie.Proof D D} (hsep : Separates E.hash (inclPres (journalSpec E) (journalPre E) k e p w.journal))
    (hv : Trie.verifyInclusion (journalSpec E) (w.journalRoot E) k (journalDigest E e) p = true) :
    w.journalAt E k = some e :=
  hsep.elim (journal_inclusion_sound hE hn hc hfit he hv)

include hE hn in
/-- TOOTH (`journal_exclusion_sound`). -/
theorem journal_exclusion_sound_sep {w : World D} (hc : w.JournalCanon E) {k : D} {p : Trie.Proof D D}
    (hsep : Separates E.hash (readPres (journalSpec E) k p w.journal))
    (hv : Trie.verifyExclusion (journalSpec E) (w.journalRoot E) k p = true) : w.journalAt E k = none :=
  hsep.elim (journal_exclusion_sound hE hn hc hv)

include hE hn in
/-- TOOTH (`head_journal_read`). -/
theorem head_journal_read_sep {w w' : World D} {t : Turn D} (hw : w.JournalOk E)
    (h : World.admit E w t = .ok w') {prev td rd root' jroot' rroot' wroot' : D} {g : UInt8}
    (hhead : headLink E prev g td rd = w'.chain) (hrd : rootsDigest E root' jroot' rroot' wroot' = rd)
    {k : D} {e : Nat × D} (he : e.1 < 2 ^ 64) {p : Trie.Proof D D}
    (hsep : Separates E.hash (headPres E w [.turn t] w' prev g td rd root' jroot' rroot' wroot' ++
      inclPres (journalSpec E) (journalPre E) k e p w'.journal))
    (hv : Trie.verifyInclusion (journalSpec E) jroot' k (journalDigest E e) p = true) :
    w'.journalAt E k = some e :=
  hsep.elim (head_journal_read hE hn hw h hhead hrd he hv)

include hE hn in
/-- TOOTH (`head_journal_absent`). -/
theorem head_journal_absent_sep {w w' : World D} {t : Turn D} (hc : w.JournalCanon E)
    (h : World.admit E w t = .ok w') {prev td rd root' jroot' rroot' wroot' : D} {g : UInt8}
    (hhead : headLink E prev g td rd = w'.chain) (hrd : rootsDigest E root' jroot' rroot' wroot' = rd)
    {k : D} {p : Trie.Proof D D}
    (hsep : Separates E.hash (headPres E w [.turn t] w' prev g td rd root' jroot' rroot' wroot' ++
      readPres (journalSpec E) k p w'.journal))
    (hv : Trie.verifyExclusion (journalSpec E) jroot' k p = true) : w'.journalAt E k = none :=
  hsep.elim (head_journal_absent hE hn hc h hhead hrd hv)

include hE in
/-- TOOTH (`fold_head_roots`). -/
theorem fold_head_roots_sep {w₀ w₁ w₂ : World D} {s : Step D} {l : List (Step D)}
    (h₁ : World.step E w₀ s = .ok w₁) (hf : World.fold E w₁ l = .ok w₂)
    {prev td rd root' jroot' rroot' wroot' : D} {g : UInt8}
    (hsep : Separates E.hash (headPres E w₀ (s :: l) w₂ prev g td rd root' jroot' rroot' wroot'))
    (hhead : headLink E prev g td rd = w₂.chain) (hrd : rootsDigest E root' jroot' rroot' wroot' = rd) :
    root' = w₂.root E ∧ jroot' = w₂.journalRoot E ∧ rroot' = w₂.refusalsRoot E ∧ wroot' = w₂.rowsRoot E :=
  hsep.elim (fold_head_roots hE h₁ hf hhead hrd)

include hE hn in
/-- TOOTH (`head_absent_admitted`): under a hash that separates the inputs the opening and the read
compare, no exclusion proof of an admitted id verifies against a head while `journalForgets` is
false. -/
theorem head_absent_admitted_sep {w₀ w₁ w₂ : World D} {t : Turn D} {l : List (Step D)}
    (hc : w₀.JournalCanon E) (h₁ : World.admit E w₀ t = .ok w₁) (hf : World.fold E w₁ l = .ok w₂)
    (hnf : journalForgets w₂.height t.notBefore = false) {prev td rd root' jroot' rroot' wroot' : D} {g : UInt8}
    (hhead : headLink E prev g td rd = w₂.chain) (hrd : rootsDigest E root' jroot' rroot' wroot' = rd)
    {p : Trie.Proof D D}
    (hsep : Separates E.hash (headPres E w₀ (.turn t :: l) w₂ prev g td rd root' jroot' rroot' wroot' ++
      readPres (journalSpec E) t.txId p w₂.journal)) :
    Trie.verifyExclusion (journalSpec E) jroot' t.txId p = false := by
  cases hv : Trie.verifyExclusion (journalSpec E) jroot' t.txId p
  · rfl
  · exact absurd (head_absent_admitted hE hn hc h₁ hf hnf hhead hrd hv) hsep.not_collides

end Sound

/-- **A World proves every journal entry it holds.** -/
theorem journal_prove_verifies {E : Env D} {w : World D} (hc : w.JournalCanon E) {k : D} {e : Nat × D}
    (hg : w.journalAt E k = some e) :
    Trie.verifyInclusion (journalSpec E) (w.journalRoot E) k (journalDigest E e)
      (w.journal.prove (journalSpec E) k) = true :=
  Trie.prove_includes (journalSpec E) hc.2.1 (Trie.shallow_of_shape _ 0 _ hc.2.2) hg

/-- **A World proves every transaction id it does not hold.** -/
theorem journal_prove_absent {E : Env D} {w : World D} (hc : w.JournalCanon E) {k : D}
    (hg : w.journalAt E k = none) :
    Trie.verifyExclusion (journalSpec E) (w.journalRoot E) k (w.journal.prove (journalSpec E) k) = true :=
  Trie.prove_excludes (journalSpec E) hc.2.1 hc.1 (Trie.shallow_of_shape _ 0 _ hc.2.2) hg

end Nanodregg.Kernel
