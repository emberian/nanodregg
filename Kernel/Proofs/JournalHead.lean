/-
# Kernel.Proofs.JournalHead — the phone reads the journal against a head (KERNEL-41)

The chain commits the journal's root beside the cells' (`chainNext`), so the replay index is
authenticated: a phone that trusts one head can be shown that a transaction id was admitted, or that
it was not.

* `journal_inclusion_sound` / `journal_exclusion_sound`: a proof that verifies against a World's
  journal root tells the truth about the transaction id, or `Collision E.hash`;
  `journal_prove_verifies` / `journal_prove_absent`: the World proves every entry it holds, and
  every id it does not.
* `head_journal_read` / `head_journal_absent`: the same against a head record
  `(prev, kind, turnDigest, rd)` that hashes to the chain an admitted turn reached, with `rd` opened
  to `(root', jroot', rroot')` (`rootsDigest`, KERNEL-47).
* `head_absent_admitted`: exclusion is an answer exactly while `journalForgets` is false. A turn
  admitted from `w₀` cannot be shown absent against the head of any World its log reaches below
  `notBefore + 2 * windowMax` (`fold_answers`), but by a collision. Past it, an exclusion proof is
  sound about the journal (`head_journal_absent`) and says nothing about the call: its entry may
  have been pruned (HOST's `forgotten`).
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
/-- A journal leaf digest determines its entry below 2^64, or the hash collides in `domJournal`. -/
theorem journalDigest_inj {E : Env D} {n : Nat} (hE : E.Lawful n) {e e' : Nat × D}
    (he : e.1 < 2 ^ 64) (he' : e'.1 < 2 ^ 64)
    (h : journalDigest E e = journalDigest E e') : e = e' ∨ Collision E.hash := by
  by_cases hb : Nanodregg.Codec.Stream.nat64.bytes e.1 ++ E.bytes e.2 =
      Nanodregg.Codec.Stream.nat64.bytes e'.1 ++ E.bytes e'.2
  · obtain ⟨h1, h2⟩ := bytes_append_inj hb rfl
    exact .inl (Prod.ext (Nanodregg.Codec.Stream.nat64_lawfulOn.bytes_injective he he' h1) (hE.bytes_inj h2))
  · exact .inr ⟨domJournal, _, _, hb, h⟩

omit [Ord D] [DecidableEq D] in
/-- A journal-trie collision is a `Collision` of the kernel's hash (in `domTrie`). -/
theorem journal_coll_collision {E : Env D} (h : Trie.Coll (journalSpec E)) : Collision E.hash := by
  obtain ⟨a, b, hne, he⟩ := h; exact ⟨domTrie, a, b, hne, he⟩

section Sound
variable {E : Env D} {n : Nat} (hE : E.Lawful n) (hn : 0 < n)

include hE hn in
/-- **Journal inclusion is sound at the World**: a claimed entry proved against the journal root is
the World's entry, or a collision. -/
theorem journal_inclusion_sound {w : World D} (hc : w.JournalCanon E)
    (hfit : ∀ k e, w.journalAt E k = some e → e.1 < 2 ^ 64) {k : D} {e : Nat × D} (he : e.1 < 2 ^ 64)
    {p : Trie.Proof D D}
    (hv : Trie.verifyInclusion (journalSpec E) (w.journalRoot E) k (journalDigest E e) p = true) :
    w.journalAt E k = some e ∨ Collision E.hash := by
  rcases Trie.inclusion_sound (journalSpec E) (journalBody_inj hE hn) (dbytes_pair_inj hE) hc.2.1 hv
    with ⟨v, hg, hd⟩ | c
  · rcases journalDigest_inj hE (hfit k v hg) he hd with rfl | c
    · exact .inl hg
    · exact .inr c
  · exact .inr (journal_coll_collision c)

include hE hn in
/-- **Journal exclusion is sound at the World**: an id proved absent against the journal root is
not in the World's journal, or a collision. -/
theorem journal_exclusion_sound {w : World D} (hc : w.JournalCanon E) {k : D} {p : Trie.Proof D D}
    (hv : Trie.verifyExclusion (journalSpec E) (w.journalRoot E) k p = true) :
    w.journalAt E k = none ∨ Collision E.hash := by
  rcases Trie.exclusion_sound (journalSpec E) (journalBody_inj hE hn) (dbytes_pair_inj hE) hc.2.1 hv
    with h | c
  · exact .inl h
  · exact .inr (journal_coll_collision c)

include hE hn in
/-- **The phone's journal read**: a head record that hashes to the chain an admitted turn reached,
and an inclusion proof against the record's journal root, show the entry in that World's journal,
or a collision. -/
theorem head_journal_read {w w' : World D} {t : Turn D} (hw : w.JournalOk E)
    (h : World.admit E w t = .ok w') {prev td rd root' jroot' rroot' wroot' : D} {g : UInt8}
    (hhead : headLink E prev g td rd = w'.chain) (hrd : rootsDigest E root' jroot' rroot' wroot' = rd) {k : D} {e : Nat × D} (he : e.1 < 2 ^ 64)
    {p : Trie.Proof D D} (hv : Trie.verifyInclusion (journalSpec E) jroot' k (journalDigest E e) p = true) :
    w'.journalAt E k = some e ∨ Collision E.hash := by
  rcases head_roots hE (s := .turn t) h hhead hrd with ⟨-, rfl, -, -⟩ | col
  · exact journal_inclusion_sound hE hn (admit_journalCanon hw.1 h) (admit_journal_heights hw h) he hv
  · exact .inr col

include hE hn in
/-- **The phone's journal absence** against a head: the id is not in that World's journal, or a
collision. -/
theorem head_journal_absent {w w' : World D} {t : Turn D} (hc : w.JournalCanon E)
    (h : World.admit E w t = .ok w') {prev td rd root' jroot' rroot' wroot' : D} {g : UInt8}
    (hhead : headLink E prev g td rd = w'.chain) (hrd : rootsDigest E root' jroot' rroot' wroot' = rd) {k : D} {p : Trie.Proof D D}
    (hv : Trie.verifyExclusion (journalSpec E) jroot' k p = true) :
    w'.journalAt E k = none ∨ Collision E.hash := by
  rcases head_roots hE (s := .turn t) h hhead hrd with ⟨-, rfl, -, -⟩ | col
  · exact journal_exclusion_sound hE hn (admit_journalCanon hc h) hv
  · exact .inr col

include hE hn in
/-- **Exclusion while `journalForgets` is false is a refutation of admission.** If `t` was admitted
from `w₀` and its log reaches `w₂`, a World at a height where `journalForgets w₂.height t.notBefore`
is false, no proof shows `t`'s transaction id absent against `w₂`'s head, but by a collision. -/
theorem head_absent_admitted {w₀ w₁ w₂ : World D} {t : Turn D} {l : List (Step D)}
    (hc : w₀.JournalCanon E) (h₁ : World.admit E w₀ t = .ok w₁) (hf : World.fold E w₁ l = .ok w₂)
    (hnf : journalForgets w₂.height t.notBefore = false) {prev td rd root' jroot' rroot' wroot' : D} {g : UInt8}
    (hhead : headLink E prev g td rd = w₂.chain) (hrd : rootsDigest E root' jroot' rroot' wroot' = rd)
    {p : Trie.Proof D D}
    (hv : Trie.verifyExclusion (journalSpec E) jroot' t.txId p = true) : Collision E.hash := by
  have hin := fold_answers hc h₁ hf hnf
  have hc₂ := fold_journalCanon (admit_journalCanon hc h₁) hf
  -- the head names w₂'s journal root: the last link of the fold that reached it
  have hroot : jroot' = w₂.journalRoot E ∨ Collision E.hash := by
    cases l with
    | nil =>
        simp [World.fold] at hf; subst hf
        rcases head_roots hE (s := .turn t) h₁ hhead hrd with ⟨-, h, -⟩ | col
        · exact .inl h
        · exact .inr col
    | cons u us =>
        rcases List.eq_nil_or_concat (u :: us) with he | ⟨a, b, he⟩
        · cases he
        · rw [he, List.concat_eq_append] at hf
          obtain ⟨w₃, _, h₃⟩ := fold_append.mp hf
          obtain ⟨w₄, h₄, h₅⟩ := fold_cons_ok.mp h₃
          simp [World.fold] at h₅; subst h₅
          rcases head_roots hE h₄ hhead hrd with ⟨-, h, -⟩ | col
          · exact .inl h
          · exact .inr col
  rcases hroot with rfl | col
  · rcases journal_exclusion_sound hE hn hc₂ hv with hnone | col
    · rw [hin] at hnone; cases hnone
    · exact col
  · exact col

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
  Trie.prove_excludes (journalSpec E) hc.2.1 (Trie.shallow_of_shape _ 0 _ hc.2.2) hg

end Nanodregg.Kernel
