/-
# Kernel.Proofs.Journal — the journal is pruned to the window, and what it answers is true (KERNEL-33)

The journal is the second instance of the one trie type (KERNEL-41): `World.journalAt` reads it,
`commit` inserts the turn's entry and, at every multiple of `Bounds.windowMax`, prunes it with the
canonical erase (`Trie.retainAt` at the root) to the entries still `kept` (fewer than `2 * windowMax`
heights old). A lookup after a prune is exact on a canonical trie, so `JournalOk` carries the journal
trie's canonicity (`World.JournalCanon`): genesis gives it, every insert and prune keeps it. Every
theorem that reads the journal after an admission takes it of the World it starts from, and its
`reach_` form, from a genesis, has no premise. What that costs and what it keeps:

* `journal_bounded`: a World every fold reaches (`JournalOk`, from an empty journal) holds fewer
  than `3 * Bounds.windowMax` entries: the journal is a bounded overhead, not history (law 4).
* `admit_retains` / `fold_retains`: an entry stays while the World is fewer than
  `2 * windowMax` heights past it. So `journalForgets` is exact on the near side: a call admitted
  at `h ≥ notBefore` is journaled at every height below `notBefore + 2 * windowMax`
  (`fold_answers`).
* `admit_spacing`: at bare `World.admit`, two admissions of one transaction id are more than
  `2 * windowMax` heights apart (the honest statement: `admit` cannot see that a txId is a call's
  digest; the spacing arm `journal-reuse:ok` admits a pruned txId under a fresh window).
* `admit_twice_window`: a txId is never admitted twice under one window; `submit_once`: through
  `Receive.submit` a CALL is admitted at most once, ever (`replayed` while journaled, its own
  window afterwards). No collision disjunct: one call has one digest and one window. The
  follower's path is the re-derivation (`rederive`: every turn `submit`'s, an `Honest` log by
  `rederiveLog_sound`), so the same holds there. `reach_submit_once` / `reach_derived_once` / `reach_admit_spacing`: from a
  genesis, no premise.
* `reach_journal_bounded`: the bound for every World a genesis reaches, with no premise.
* `admit_prune_verdict`: pruning changes no verdict of any turn whose window ends by its
  transaction id's entry height plus `windowMax` (every call-derived retry): the window is
  checked before the journal, so an expired retry is `outsideWindow` with or without its entry.
* `reach_prune_check_call` (KERNEL-38 (c)): from a genesis, on every honest folded log (the follower's),
  pruning changed no check of a call's retry, with no window premise, or two of the events
  `retryPres` names collide (`call_retry_window`: the never-pruned entry under a call's transaction
  id is the same call's, or a different call with its digest). Its teeth: `_sep`, an instance where
  the window disjunct carries the content, one where it is false, and one (`journal-shadow-reuse`'s
  shape, a call's event under another window) where `hv` fails without the call-log premise, and
  its `Honest` twin on a `Ctx` whose signatures verify, the retry a real `receive` output
  (`honest_retry_window_needs_honest`).
-/
import Kernel.Proofs.Rederive
import Kernel.Proofs.Fold
import Kernel.Proofs.Receive
import Kernel.Receive.Follow
import Kernel.Sim.Shadow
import Kernel.Proofs.Local

namespace Nanodregg.Kernel

variable {D : Type} [Ord D] [DecidableEq D]

theorem windowMax_eq : Bounds.windowMax = 1024 := rfl

/-! ## Counting distinct heights -/

/-- Distinct naturals in a window of `m` heights ending at `H` number at most `m`. -/
theorem nodup_window_length : ∀ (m H : Nat) (l : List Nat), l.Nodup →
    (∀ x ∈ l, x ≤ H ∧ H < x + m) → l.length ≤ m
  | 0, H, [], _, _ => Nat.le_refl _
  | 0, H, x :: _, _, hb => by have := hb x (by simp); omega
  | m + 1, H, l, hn, hb => by
      by_cases hm : H ∈ l
      · have hl := List.length_erase_of_mem hm
        have ih := nodup_window_length m (H - 1) (l.erase H) (hn.erase H) (by
          intro x hx
          rw [hn.mem_erase_iff] at hx
          have := hb x hx.2
          omega)
        have : 0 < l.length := List.length_pos_of_mem hm
        omega
      · have ih := nodup_window_length m (H - 1) l hn (by
          intro x hx
          have := hb x hx
          have hne : x ≠ H := fun he => hm (he ▸ hx)
          omega)
        omega

/-! ## The invariant -/

/-- The journal trie is canonical; every journal entry is at most the World's height and fewer than
`2 * windowMax` heights behind it, plus the heights since the last prune; and distinct entries have
distinct heights (one admission per height). -/
def World.JournalOk (E : Env D) (w : World D) : Prop :=
  w.JournalCanon E ∧
  (∀ (k : D) (e : Nat × D), w.journalAt E k = some e → e.1 ≤ w.height ∧
    w.height < e.1 + 2 * Bounds.windowMax + w.height % Bounds.windowMax) ∧
  (∀ (k₁ k₂ : D) (e₁ e₂ : Nat × D), w.journalAt E k₁ = some e₁ → w.journalAt E k₂ = some e₂ →
    e₁.1 = e₂.1 → k₁ = k₂)

theorem journalOk_of_empty {E : Env D} {w : World D} (h : w.journal = .empty) : w.JournalOk E := by
  have hn : ∀ k : D, w.journalAt E k = none := fun k => by
    unfold World.journalAt; rw [h]; rfl
  refine ⟨by unfold World.JournalCanon; rw [h]; exact Trie.canon_empty _ 0, fun k e he => ?_,
    fun k _ _ _ he _ _ => ?_⟩
  · rw [hn k] at he; cases he
  · rw [hn k] at he; cases he

theorem genesis_journalOk (E : Env D) (o : D) (a : Nat) : (World.genesis E o a).JournalOk E :=
  journalOk_of_empty rfl

/-- A listed journal entry is what the journal holds at its id (a canonical trie lists what it holds). -/
theorem journalAt_of_mem {E : Env D} {w : World D} (hc : w.JournalCanon E) {p : D × (Nat × D)}
    (hp : p ∈ w.journal.toList) : w.journalAt E p.1 = some p.2 :=
  (Trie.mem_toList (journalSpec E) 0 w.journal hc.1 p.1 p.2).mp hp

theorem mem_of_journalAt {E : Env D} {w : World D} (hc : w.JournalCanon E) {k : D} {e : Nat × D}
    (h : w.journalAt E k = some e) : (k, e) ∈ w.journal.toList :=
  (Trie.mem_toList (journalSpec E) 0 w.journal hc.1 k e).mpr h

/-- An entry of a committed World: the turn's own, or an older one that pruning kept. -/
theorem commit_journal_mem {E : Env D} {w : World D} {t : Turn D} {posts : List (Post D)}
    (hc : w.JournalCanon E) {k : D} {e : Nat × D}
    (h : (commit E w t posts).journalAt E k = some e) :
    (k = t.txId ∧ e = (w.height + 1, turnDigest E t)) ∨
      (k ≠ t.txId ∧ w.journalAt E k = some e ∧
        ((w.height + 1) % Bounds.windowMax = 0 → kept (w.height + 1) e = true)) := by
  rw [commit_journalAt hc] at h
  by_cases hk : k = t.txId
  · rw [if_pos hk] at h
    exact .inl ⟨hk, (Option.some.inj h).symm⟩
  · rw [if_neg hk] at h
    right
    refine ⟨hk, ?_⟩
    split at h
    · cases hg : w.journalAt E k with
      | none => rw [hg] at h; cases h
      | some e' =>
          rw [hg] at h
          simp only [Option.filter] at h
          split at h
          · rename_i hkp; cases h; exact ⟨rfl, fun _ => hkp⟩
          · cases h
    · rename_i hz
      exact ⟨h, fun h' => absurd h' hz⟩

/-- **The invariant holds after every admission.** -/
theorem admit_journalOk {E : Env D} {w w' : World D} {t : Turn D} (hw : w.JournalOk E)
    (h : World.admit E w t = .ok w') : w'.JournalOk E := by
  have hc' := admit_journalCanon hw.1 h
  obtain ⟨posts, _, rfl⟩ := admit_ok h
  have hh : (commit E w t posts).height = w.height + 1 := rfl
  refine ⟨hc', fun k e he => ?_, fun k₁ k₂ e₁ e₂ h₁ h₂ heq => ?_⟩
  · rw [hh]
    rcases commit_journal_mem hw.1 he with ⟨_, rfl⟩ | ⟨_, hk, hkept⟩
    · rw [windowMax_eq]; omega
    · have := hw.2.1 k e hk
      by_cases hz : (w.height + 1) % Bounds.windowMax = 0
      · have := hkept hz
        simp only [kept, decide_eq_true_eq] at this
        rw [windowMax_eq] at *; omega
      · rw [windowMax_eq] at *; omega
  · rcases commit_journal_mem hw.1 h₁ with ⟨r₁, rfl⟩ | ⟨n₁, hk₁, _⟩ <;>
      rcases commit_journal_mem hw.1 h₂ with ⟨r₂, rfl⟩ | ⟨n₂, hk₂, _⟩
    · rw [r₁, r₂]
    · have := (hw.2.1 k₂ e₂ hk₂).1; simp at heq; omega
    · have := (hw.2.1 k₁ e₁ hk₁).1; simp at heq; omega
    · exact hw.2.2 k₁ k₂ e₁ e₂ hk₁ hk₂ heq

/-- A recorded refusal keeps `JournalOk`: it moves neither the journal nor the height. -/
theorem refuse_journalOk {E : Env D} {w w' : World D} {r : Refused D} (hw : w.JournalOk E)
    (h : World.refuse E w r = .ok w') : w'.JournalOk E := by
  obtain ⟨_, hj, hh, _⟩ := refuse_frame h
  unfold World.JournalOk World.JournalCanon World.journalAt at *
  rw [hj, hh]; exact hw

theorem fold_journalOk {E : Env D} {w w' : World D} {l : List (Step D)} (hw : w.JournalOk E)
    (h : World.fold E w l = .ok w') : w'.JournalOk E :=
  fold_keeps (P := fun v => v.JournalOk E) admit_journalOk refuse_journalOk hw h

theorem fold_journalCanon {E : Env D} {w w' : World D} {l : List (Step D)} (hc : w.JournalCanon E)
    (h : World.fold E w l = .ok w') : w'.JournalCanon E :=
  fold_keeps (P := fun v => v.JournalCanon E) admit_journalCanon
    (fun hp hr => by show Trie.Canon _ 0 _; rw [(refuse_frame hr).2.1]; exact hp) hc h

/-- The heights of a `JournalOk` journal's listing are distinct. -/
theorem journal_heights_nodup {E : Env D} {w : World D} (hw : w.JournalOk E) :
    (w.journal.toList.map fun p => p.2.1).Nodup := by
  have hk := List.pairwise_map.mp (Trie.toList_nodup (journalSpec E) 0 w.journal hw.1.1)
  apply List.pairwise_map.mpr
  exact hk.imp_of_mem fun {p q} hp hq hpq heq =>
    hpq (hw.2.2 p.1 q.1 p.2 q.2 (journalAt_of_mem hw.1 hp) (journalAt_of_mem hw.1 hq) heq)

/-- **The journal is bounded by the window** (law 4): fewer than `3 * Bounds.windowMax` entries,
whatever the World's history. -/
theorem journal_bounded {E : Env D} {w : World D} (hw : w.JournalOk E) :
    w.journal.toList.length < 3 * Bounds.windowMax := by
  let L := w.journal.toList.map fun p => p.2.1
  have hlen : L.length = w.journal.toList.length := by simp [L]
  have hb : ∀ x ∈ L, x ≤ w.height ∧
      w.height < x + (2 * Bounds.windowMax + w.height % Bounds.windowMax) := by
    intro x hx
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
    have := hw.2.1 p.1 p.2 (journalAt_of_mem hw.1 hp)
    omega
  have := nodup_window_length _ _ L (journal_heights_nodup hw) hb
  have hm : w.height % Bounds.windowMax < Bounds.windowMax := Nat.mod_lt _ (by decide)
  omega

/-- **Every journal entry is at or below the World's height** (CODEC's ask: the decoder's height
bound is met by every reached World). -/
theorem journal_height_le {E : Env D} {w : World D} (hw : w.JournalOk E) :
    ∀ p ∈ w.journal.toList, p.2.1 ≤ w.height :=
  fun p hp => (hw.2.1 p.1 p.2 (journalAt_of_mem hw.1 hp)).1

/-! ## A journal read from bytes (KERNEL-39) -/

omit [Ord D] [DecidableEq D] in
theorem ascendingNat_lt : ∀ {a : Nat} {l : List Nat}, ascendingNat (a :: l) = true → ∀ y ∈ l, a < y
  | _, [], _, y, hy => absurd hy List.not_mem_nil
  | a, b :: l, h, y, hy => by
      simp only [ascendingNat, Bool.and_eq_true, decide_eq_true_eq] at h
      rcases List.mem_cons.mp hy with rfl | hy
      · exact h.1
      · exact Nat.lt_trans h.1 (ascendingNat_lt h.2 y hy)

omit [Ord D] [DecidableEq D] in
theorem ascendingNat_nodup : ∀ {l : List Nat}, ascendingNat l = true → l.Nodup
  | [], _ => List.nodup_nil
  | [_], _ => List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩
  | a :: b :: l, h => by
      have ht : ascendingNat (b :: l) = true := by
        simp only [ascendingNat, Bool.and_eq_true] at h; exact h.2
      refine List.nodup_cons.mpr ⟨fun hm => ?_, ascendingNat_nodup ht⟩
      exact Nat.lt_irrefl a (ascendingNat_lt h a hm)

omit [Ord D] [DecidableEq D] in
theorem ascendingNat_of_sorted : ∀ {l : List Nat}, l.Pairwise (fun a b => a ≤ b) → l.Nodup →
    ascendingNat l = true
  | [], _, _ => rfl
  | [_], _, _ => rfl
  | a :: b :: l, hs, hn => by
      simp only [ascendingNat, Bool.and_eq_true, decide_eq_true_eq]
      have hab : a ≤ b := List.rel_of_pairwise_cons hs (List.mem_cons_self ..)
      have hne : a ≠ b := fun he => (List.nodup_cons.mp hn).1 (he ▸ List.mem_cons_self ..)
      exact ⟨Nat.lt_of_le_of_ne hab hne, ascendingNat_of_sorted hs.of_cons hn.of_cons⟩

omit [Ord D] [DecidableEq D] in
theorem eq_of_nodup_map {α β : Type} {f : α → β} :
    ∀ {l : List α}, (l.map f).Nodup → ∀ {x y : α}, x ∈ l → y ∈ l → f x = f y → x = y
  | [], _, _, _, hx, _, _ => absurd hx List.not_mem_nil
  | a :: l, h, x, y, hx, hy, he => by
      rw [List.map_cons, List.nodup_cons] at h
      rcases List.mem_cons.mp hx with rfl | hxl <;> rcases List.mem_cons.mp hy with rfl | hyl
      · rfl
      · exact absurd (show f x ∈ l.map f by rw [he]; exact List.mem_map_of_mem hyl) h.1
      · exact absurd (show f y ∈ l.map f by rw [← he]; exact List.mem_map_of_mem hxl) h.1
      · exact eq_of_nodup_map h.2 hxl hyl he

/-- **A canonical listing that `journalFits` is a `JournalOk` journal**: what the World decoder's
`kernel/journal` refusal gives every decoded base (whose journal trie the decoder builds, so it is
canonical). -/
theorem journalOk_of_fits {E : Env D} {w : World D} (hc : w.JournalCanon E)
    (h : journalFits w.height w.journal.toList = true) : w.JournalOk E := by
  simp only [journalFits, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨hall, hasc⟩ := h
  have hnd : (w.journal.toList.map fun p => p.2.1).Nodup :=
    (List.mergeSort_perm _ _).nodup_iff.mp (ascendingNat_nodup hasc)
  refine ⟨hc, fun k e he => hall (k, e) (mem_of_journalAt hc he), fun k₁ k₂ e₁ e₂ h₁ h₂ heq => ?_⟩
  have := eq_of_nodup_map hnd (mem_of_journalAt hc h₁) (mem_of_journalAt hc h₂) heq
  exact (Prod.mk.inj this).1

/-- **Every `JournalOk` journal fits**, so the refusal never refuses a base a fold wrote
(`fold_journalOk`, `reach_journal_bounded`'s invariant). -/
theorem journalFits_of_ok {E : Env D} {w : World D} (hw : w.JournalOk E) :
    journalFits w.height w.journal.toList = true := by
  simp only [journalFits, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq]
  refine ⟨fun p hp => hw.2.1 p.1 p.2 (journalAt_of_mem hw.1 hp), ?_⟩
  apply ascendingNat_of_sorted
  · have := List.pairwise_mergeSort (le := fun a b : Nat => decide (a ≤ b))
      (fun a b c hab hbc => by simp only [decide_eq_true_eq] at *; omega)
      (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega)
      (w.journal.toList.map fun p => p.2.1)
    exact this.imp fun h => by simpa using h
  · exact (List.mergeSort_perm _ _).nodup_iff.mpr (journal_heights_nodup hw)

omit [Ord D] [DecidableEq D] in
/-- The refusal refuses: an entry above the World's height does not fit (the entry that would
never be pruned and answer `replayed` forever). -/
theorem journalFits_future (h : Nat) (k d : D) : journalFits h [(k, (h + 1, d))] = false := by
  simp only [journalFits, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_false_iff]
  left
  simp only [decide_eq_false_iff_not, not_and, Nat.not_lt]
  omega

omit [Ord D] [DecidableEq D] in
/-- The refusal refuses: an entry already due for pruning at the last prune does not fit. -/
theorem journalFits_stale (h e : Nat) (k d : D)
    (hs : e + 2 * Bounds.windowMax + h % Bounds.windowMax ≤ h) : journalFits h [(k, (e, d))] = false := by
  simp only [journalFits, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_false_iff]
  left
  simp only [decide_eq_false_iff_not, not_and, Nat.not_lt]
  intro _
  exact hs

omit [Ord D] [DecidableEq D] in
/-- The refusal refuses: two entries at one height do not fit. -/
theorem journalFits_twice (h : Nat) (k₁ k₂ d₁ d₂ : D) :
    journalFits h [(k₁, (h, d₁)), (k₂, (h, d₂))] = false := by
  simp [journalFits, List.mergeSort, ascendingNat]

/-! ## What the journal still answers -/

/-- **An entry stays while it is kept.** -/
theorem admit_retains {E : Env D} {w w' : World D} {t : Turn D} {k : D} {e : Nat × D}
    (hc : w.JournalCanon E) (h : World.admit E w t = .ok w') (hk : w.journalAt E k = some e)
    (hlt : w'.height < e.1 + 2 * Bounds.windowMax) : w'.journalAt E k = some e := by
  have hnew := admit_new h
  obtain ⟨posts, _, rfl⟩ := admit_ok h
  have hne : k ≠ t.txId := fun he => by rw [he, hnew] at hk; cases hk
  have hlt' : w.height + 1 < e.1 + 2 * Bounds.windowMax := hlt
  rw [commit_journalAt hc, if_neg hne]
  have hkept : kept (w.height + 1) e = true := by simp [kept, hlt']
  split <;> simp [hk, Option.filter, hkept]

theorem fold_retains {E : Env D} {k : D} {e : Nat × D} :
    ∀ {w w' : World D} {l : List (Step D)}, w.JournalCanon E → World.fold E w l = .ok w' →
      w.journalAt E k = some e → w'.height < e.1 + 2 * Bounds.windowMax → w'.journalAt E k = some e
  | w, w', [], _, h, hk, _ => by simp [World.fold] at h; subst h; exact hk
  | w, w', .turn t :: rest, hc, h, hk, hlt => by
      obtain ⟨w₁, h₁, h₂⟩ := fold_cons_ok.mp h
      have := fold_height h₂
      exact fold_retains (admit_journalCanon hc h₁) h₂ (admit_retains hc h₁ hk (by omega)) hlt
  | w, w', .refusal r :: rest, hc, h, hk, hlt => by
      obtain ⟨w₁, h₁, h₂⟩ := fold_cons_ok.mp h
      have hc₁ : w₁.JournalCanon E := by unfold World.JournalCanon; rw [(refuse_frame h₁).2.1]; exact hc
      exact fold_retains hc₁ h₂ ((refuse_journalAt h₁ k).trans hk) hlt

/-- **Every journal entry a log reaches is one of its admitted turns** (E5: what a committed
receipt is about). An entry of the World `fold` reaches from `w` was `w`'s own, or is the entry of a
Turn `t` of the log: the prefix before it folds from `w` to `v`, `t` is admitted at `v`, its
transaction id is the key, and the entry is `(v.height + 1, turnDigest t)`. Stated over the folded
World's journal, never a claim. -/
theorem fold_journal_turn {E : Env D} {k : D} {e : Nat × D} :
    ∀ {w w' : World D} {l : List (Step D)}, w.JournalCanon E → World.fold E w l = .ok w' →
      w'.journalAt E k = some e →
      w.journalAt E k = some e ∨
        ∃ l₁ t l₂ v v', l = l₁ ++ Step.turn t :: l₂ ∧ World.fold E w l₁ = .ok v ∧
          World.admit E v t = .ok v' ∧ t.txId = k ∧ e = (v.height + 1, turnDigest E t)
  | w, w', [], _, h, hk => by simp [World.fold] at h; subst h; exact .inl hk
  | w, w', .turn t :: rest, hc, h, hk => by
      obtain ⟨w₁, h₁, h₂⟩ := fold_cons_ok.mp h
      have hc₁ := admit_journalCanon hc h₁
      rcases fold_journal_turn hc₁ h₂ hk with h1 | ⟨l₁, u, l₂, v, v', hl, hv, hu, hk', he⟩
      · obtain ⟨posts, _, hw₁⟩ := admit_ok h₁
        rw [hw₁] at h1
        rcases commit_journal_mem hc h1 with ⟨hkt, het⟩ | ⟨_, hw, _⟩
        · exact .inr ⟨[], t, rest, w, w₁, rfl, rfl, h₁, hkt.symm, het⟩
        · exact .inl hw
      · refine .inr ⟨.turn t :: l₁, u, l₂, v, v', by simp [hl], ?_, hu, hk', he⟩
        exact fold_cons_ok.mpr ⟨w₁, h₁, hv⟩
  | w, w', .refusal r :: rest, hc, h, hk => by
      obtain ⟨w₁, h₁, h₂⟩ := fold_cons_ok.mp h
      have hc₁ : w₁.JournalCanon E := by unfold World.JournalCanon; rw [(refuse_frame h₁).2.1]; exact hc
      rcases fold_journal_turn hc₁ h₂ hk with h1 | ⟨l₁, u, l₂, v, v', hl, hv, hu, hk', he⟩
      · exact .inl ((refuse_journalAt h₁ k).symm.trans h1)
      · refine .inr ⟨.refusal r :: l₁, u, l₂, v, v', by simp [hl], ?_, hu, hk', he⟩
        exact fold_cons_ok.mpr ⟨w₁, h₁, hv⟩

/-- **Absence is an answer below `journalForgets`.** A turn admitted from `w₀` is still journaled
in every later World of the log whose height is below its `notBefore + 2 * windowMax`. So an
un-journaled transaction id at a height where `journalForgets` is false was never admitted by
that log (HOST's `expired`); where it is true, absence says nothing (HOST's `forgotten`). -/
theorem fold_answers {E : Env D} {w₀ w₁ w₂ : World D} {t : Turn D} {l : List (Step D)}
    (hc : w₀.JournalCanon E) (h₁ : World.admit E w₀ t = .ok w₁) (hf : World.fold E w₁ l = .ok w₂)
    (hnf : journalForgets w₂.height t.notBefore = false) :
    w₂.journalAt E t.txId = some (w₀.height + 1, turnDigest E t) := by
  have hwin := (admit_window h₁).1
  simp only [journalForgets, decide_eq_false_iff_not, Nat.not_le] at hnf
  exact fold_retains (admit_journalCanon hc h₁) hf (admit_journaled hc h₁) (by omega)

/-- **Spacing at bare `admit`.** Two admissions of one transaction id, from `w₀` and later from
`w₂`, are more than `2 * windowMax` heights apart. -/
theorem admit_spacing {E : Env D} {w₀ w₁ w₂ w₃ : World D} {t t' : Turn D} {l : List (Step D)}
    (hc : w₀.JournalCanon E) (h₁ : World.admit E w₀ t = .ok w₁) (hf : World.fold E w₁ l = .ok w₂)
    (h₂ : World.admit E w₂ t' = .ok w₃) (hid : t'.txId = t.txId) :
    w₀.height + 1 + 2 * Bounds.windowMax ≤ w₂.height := by
  apply Nat.le_of_not_lt
  intro hlt
  have := fold_retains (admit_journalCanon hc h₁) hf (admit_journaled hc h₁) hlt
  have hnew := admit_new h₂
  rw [hid, this] at hnew
  cases hnew

/-- **One window, one admission.** A transaction id admitted from `w₀` is never admitted again
by a turn with the same window: by then its entry is pruned (`admit_spacing`), so the window has
ended. Every deployed path reaches `World.admit` through `receive`: the writer through
`Receive.submit` (`submit_ok`), the follower through `Receive.rederive` (`submit` again: every logged turn of
an `Honest` log is what `receive` derives from its own event). Two turns derived from one call carry its digest and
its window (`receive_derived`), so on both paths a call is admitted at most once. -/
theorem admit_twice_window {E : Env D} {w₀ w₁ w₂ w₃ : World D} {t t' : Turn D} {l : List (Step D)}
    (hc : w₀.JournalCanon E) (h₁ : World.admit E w₀ t = .ok w₁) (hf : World.fold E w₁ l = .ok w₂)
    (h₂ : World.admit E w₂ t' = .ok w₃) (hid : t'.txId = t.txId) (hv : t'.validUntil = t.validUntil) :
    False := by
  have hsp := admit_spacing hc h₁ hf h₂ hid
  have hw₁ := admit_window h₁
  have hw₂ := admit_window h₂
  have hb := admit_bounded h₁
  unfold checkBounds at hb
  simp only [except_bind_ok] at hb
  obtain ⟨⟨⟩, _, ⟨⟩, _, ⟨⟩, _, ⟨⟩, _, ⟨⟩, _, ⟨⟩, _, ⟨⟩, _, ⟨⟩, _, ⟨⟩, hwm, _⟩ := hb
  rw [req_ok, decide_eq_true_eq] at hwm
  rw [windowMax_eq] at *
  omega

/-- **`absent` becomes final by expiry (HOST-8).** If the journal of `w` lacks `k` and some later
World of an admitted log has it, a turn of that log carries `k` and a window still open after
`w`: its `validUntil` exceeds `w.height`. So once `w.height ≥ v`, a transaction whose signed window
ends at `v` and is absent stays absent, unless another call with a LATER window has the same
transaction id — two different signed calls with one digest (`txIdOf`), a collision. -/
theorem absent_final {E : Env D} {k : D} :
    ∀ {w w' : World D} {l : List (Step D)}, w.JournalCanon E → World.fold E w l = .ok w' →
      w.journalAt E k = none → w'.journalAt E k ≠ none →
        ∃ t ∈ Step.turns l, t.txId = k ∧ w.height < t.validUntil
  | w, w', [], _, h, ha, hj => by simp [World.fold] at h; subst h; exact absurd ha hj
  | w, w', .refusal r :: rest, hc, h, ha, hj => by
      obtain ⟨w₁, h₁, h₂⟩ := fold_cons_ok.mp h
      have hc₁ : w₁.JournalCanon E := by unfold World.JournalCanon; rw [(refuse_frame h₁).2.1]; exact hc
      obtain ⟨u, hu, huk, hlt⟩ := absent_final hc₁ h₂ ((refuse_journalAt h₁ k).trans ha) hj
      exact ⟨u, hu, huk, by rw [(refuse_frame h₁).2.2.1] at hlt; exact hlt⟩
  | w, w', .turn t :: rest, hc, h, ha, hj => by
      obtain ⟨w₁, h₁, h₂⟩ := fold_cons_ok.mp h
      have hwin := (admit_window h₁).2
      have hc₁ := admit_journalCanon hc h₁
      by_cases hk : t.txId = k
      · exact ⟨t, by simp [Step.turns], hk, by omega⟩
      · have ha₁ : w₁.journalAt E k = none := by
          obtain ⟨_, _, rfl⟩ := admit_ok h₁
          rw [commit_journalAt hc, if_neg (Ne.symm hk), ha]
          split <;> rfl
        obtain ⟨u, hu, huk, hlt⟩ := absent_final hc₁ h₂ ha₁ hj
        exact ⟨u, by simp [Step.turns, hu], huk, by rw [admit_height h₁] at hlt; omega⟩

/-- **A journal filtered by `kept H` changes no check** of a turn whose window ends by its
transaction id's entry height plus `windowMax`, at any `H ≤ w.height`: the window is checked first,
and inside it the entry is still kept. -/
theorem check_journal_filter {E : Env D} {w : World D} {t : Turn D} {H : Nat} {J : Journal D}
    (hH : H ≤ w.height)
    (hj : w.journalAt E t.txId = (J.get (journalSpec E) t.txId).filter (kept H))
    (hv : ∀ e, J.get (journalSpec E) t.txId = some e → t.validUntil ≤ e.1 + Bounds.windowMax) :
    check E w t = check E { w with journal := J } t := by
  by_cases hwin : checkWindow w t = .ok ()
  · have hg : J.get (journalSpec E) t.txId = w.journalAt E t.txId := by
      rw [hj]
      cases hg : J.get (journalSpec E) t.txId with
      | none => rfl
      | some e =>
          have hve := hv e hg
          unfold checkWindow at hwin
          rw [req_ok] at hwin
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hwin
          have hkept : kept H e = true := by
            simp only [kept, decide_eq_true_eq]; rw [windowMax_eq] at *; omega
          simp [Option.filter, hkept]
    exact (check_local (w := w) (w' := { w with journal := J }) (t := t) ⟨fun _ _ => rfl, rfl, rfl, rfl, hg, rfl, .same rfl⟩).symm
  · unfold check checkWith
    cases hb : checkBounds t with
    | error _ => simp [bind, Except.bind, Except.map]
    | ok u =>
        cases hw' : checkWindow w t with
        | ok v => exact absurd hw' hwin
        | error e =>
            have : checkWindow { w with journal := J } t = .error e := hw'
            simp [bind, Except.bind, Except.map, this]

/-- **Pruning changes no check.** For a turn whose window ends by its transaction id's entry
height plus `windowMax` (a retry of the call that entry records: same call, same window), the
World with its journal pruned at any `H ≤ w.height` checks it exactly as the World before
pruning: the same refusal, or the same posts. -/
theorem check_prune {E : Env D} {w : World D} {t : Turn D} {H : Nat} (hc : w.JournalCanon E)
    (hH : H ≤ w.height)
    (hv : ∀ e, w.journalAt E t.txId = some e → t.validUntil ≤ e.1 + Bounds.windowMax) :
    check E { w with journal := pruneJournal E H w.journal } t = check E w t := by
  by_cases hz : H % Bounds.windowMax = 0
  · have hj : ({ w with journal := pruneJournal E H w.journal } : World D).journalAt E t.txId =
        (w.journalAt E t.txId).filter (kept H) := by
      show (pruneJournal E H w.journal).get (journalSpec E) t.txId = _
      rw [pruneJournal_get hc, if_pos hz]; rfl
    exact (check_journal_filter (w := { w with journal := pruneJournal E H w.journal }) hH hj hv)
  · have : pruneJournal E H w.journal = w.journal := by unfold pruneJournal; rw [if_neg hz]
    rw [this]

/-- **Pruning changes no verdict** (`check_prune`, at the admission). -/
theorem admit_prune_verdict {E : Env D} {w : World D} {t : Turn D} {H : Nat} (hc : w.JournalCanon E)
    (hH : H ≤ w.height)
    (hv : ∀ e, w.journalAt E t.txId = some e → t.validUntil ≤ e.1 + Bounds.windowMax) (r : Reject D) :
    World.admit E { w with journal := pruneJournal E H w.journal } t = .error r ↔
      World.admit E w t = .error r := by
  unfold World.admit
  rw [check_prune hc hH hv]
  cases check E w t <;> simp

/-! ## The real fold is the never-pruning fold, filtered at the last prune (KERNEL-38)

`admit_prune_verdict` compares ONE prune against the unpruned journal. The deployed fold
inserts and prunes at every turn. `fold_journal_filter` says what that interleaving leaves: the
never-pruning journal (`shadowJournal`) filtered to the entries `kept` at the last prune height
(`lastPrune`), and `fold_prune_check` turns that into the statement about a real history: the
World a fold reaches checks every windowed retry exactly as the same World with the journal that
was never pruned. -/

/-- `j` is `J` filtered to the entries kept at `H`, read at every transaction id. -/
def JournalFiltered (E : Env D) (H : Nat) (j J : Journal D) : Prop :=
  ∀ k : D, j.get (journalSpec E) k = (J.get (journalSpec E) k).filter (kept H)

omit [Ord D] [DecidableEq D] in
theorem lastPrune_le (h : Nat) : lastPrune h ≤ h := Nat.sub_le _ _

omit [Ord D] [DecidableEq D] in
theorem lastPrune_mod (h : Nat) : lastPrune h % Bounds.windowMax = 0 := by
  unfold lastPrune; rw [windowMax_eq]; omega

omit [Ord D] [DecidableEq D] in
theorem lastPrune_succ (h : Nat) :
    lastPrune (h + 1) = if (h + 1) % Bounds.windowMax = 0 then h + 1 else lastPrune h := by
  unfold lastPrune; rw [windowMax_eq]; split <;> omega

omit [Ord D] [DecidableEq D] in
theorem kept_anti {H H' : Nat} {e : Nat × D} (hH : H ≤ H') (h : kept H' e = true) : kept H e = true := by
  simp only [kept, decide_eq_true_eq] at *; omega

omit [Ord D] [DecidableEq D] in
theorem filter_kept_anti {H H' : Nat} (hH : H ≤ H') (o : Option (Nat × D)) :
    (o.filter (kept H)).filter (kept H') = o.filter (kept H') := by
  cases o with
  | none => rfl
  | some e =>
      by_cases h' : kept H' e = true
      · simp [Option.filter, kept_anti hH h', h']
      · by_cases h : kept H e = true <;> simp [Option.filter, h, h']

/-- Every World that holds `JournalOk` is its own journal filtered at its last prune height. -/
theorem journalFiltered_self {E : Env D} {w : World D} (hw : w.JournalOk E) :
    JournalFiltered E (lastPrune w.height) w.journal w.journal := by
  unfold JournalFiltered
  intro k
  cases hg : w.journal.get (journalSpec E) k with
  | none => rfl
  | some e =>
      have := (hw.2.1 k e hg).2
      simp only [Option.filter, kept, lastPrune, decide_eq_true_eq]
      rw [windowMax_eq] at *
      split
      · rfl
      · omega

/-- One commit: the pruned insert is the never-pruned insert filtered at the new last prune. -/
theorem commit_filtered {E : Env D} {w : World D} {t : Turn D} {posts : List (Post D)}
    {J : Journal D} (hc : w.JournalCanon E)
    (hj : JournalFiltered E (lastPrune w.height) w.journal J) :
    JournalFiltered E (lastPrune (w.height + 1)) (commit E w t posts).journal
      (J.insert (journalSpec E) t.txId (w.height + 1, turnDigest E t)) := by
  unfold JournalFiltered at *
  intro k
  have hk' := commit_journalAt (t := t) (posts := posts) hc k
  unfold World.journalAt at hk'
  rw [hk', Trie.get_insert, lastPrune_succ]
  by_cases hz : (w.height + 1) % Bounds.windowMax = 0
  · rw [if_pos hz, if_pos hz]
    by_cases hk : k = t.txId
    · rw [if_pos hk, if_pos hk]
      simp [Option.filter, kept, Bounds.windowMax]
    · rw [if_neg hk, if_neg hk, hj k, filter_kept_anti (Nat.le_succ_of_le (lastPrune_le _))]
  · rw [if_neg hz, if_neg hz]
    by_cases hk : k = t.txId
    · rw [if_pos hk, if_pos hk]
      have := lastPrune_le w.height
      simp only [Option.filter, kept, decide_eq_true_eq]
      split
      · rfl
      · omega
    · rw [if_neg hk, if_neg hk, hj k]

/-- **The real fold's journal is the never-pruning journal, filtered at the last prune height.**
From any World with a canonical journal that is `J` filtered at its last prune
(`journalFiltered_self`: every `JournalOk` World, with `J` its own journal), the World a fold
reaches, which inserted and pruned at every turn, holds exactly the entries of `shadowJournal` that
are `kept` at its own `lastPrune` height. All the prunes of a history are one prune at the last
multiple of `windowMax`, of the journal that never forgot. -/
theorem fold_journal_filter {E : Env D} {l : List (Step D)} :
    ∀ {w w' : World D} {J : Journal D}, w.JournalCanon E →
      JournalFiltered E (lastPrune w.height) w.journal J → World.fold E w l = .ok w' →
      JournalFiltered E (lastPrune w'.height) w'.journal (shadowJournal E w.height J l) := by
  induction l with
  | nil => intro w w' J _ hj h; simp [World.fold] at h; subst h; exact hj
  | cons s rest ih =>
      intro w w' J hc hj h
      obtain ⟨w₁, h₁, h₂⟩ := fold_cons_ok.mp h
      cases s with
      | turn t =>
          have hc₁ := admit_journalCanon hc h₁
          obtain ⟨posts, _, rfl⟩ := admit_ok h₁
          exact ih hc₁ (commit_filtered hc hj) h₂
      | refusal r =>
          obtain ⟨_, hj₁, hh₁, _⟩ := refuse_frame h₁
          have hc₁ : w₁.JournalCanon E := by unfold World.JournalCanon; rw [hj₁]; exact hc
          have := ih (J := J) hc₁ (by rw [hj₁, hh₁]; exact hj) h₂
          rw [hh₁] at this
          exact this

/-- **Pruning changed no check in a real history.** The World `w'` a fold reaches checks a
turn exactly as the same World with the journal that was never pruned, whenever the turn's
window ends by its transaction id's never-pruned entry height plus `windowMax` (a retry of the
call that entry records). This is `check_journal_filter` at `lastPrune w'.height`, through
`fold_journal_filter`. -/
theorem fold_prune_check {E : Env D} {w w' : World D} {l : List (Step D)}
    {J : Journal D} {t : Turn D} (hc : w.JournalCanon E)
    (hj : JournalFiltered E (lastPrune w.height) w.journal J) (h : World.fold E w l = .ok w')
    (hv : ∀ e, (shadowJournal E w.height J l).get (journalSpec E) t.txId = some e →
      t.validUntil ≤ e.1 + Bounds.windowMax) :
    check E w' t = check E { w' with journal := shadowJournal E w.height J l } t :=
  check_journal_filter (lastPrune_le _) (fold_journal_filter hc hj h t.txId) hv

end Nanodregg.Kernel

namespace Nanodregg.Kernel.Receive

open Nanodregg.Kernel

variable {D : Type} [Ord D] [DecidableEq D]

/-- **A call is admitted at most once, ever** (KERNEL-33). After `submit` admitted call `c`, no
World any later log reaches admits `c` again: while its entry is journaled `submit` answers
`replayed`, and by the time it is pruned (`admit_spacing`) the call's own window, fixed by the
call, has ended. No collision disjunct: one call has one digest and one window. The premise is the
journal trie's canonicity at `w₀` (every reached World's: `reach_submit_once`). -/
theorem submit_once {X : Ctx D} {w₀ w₁ w₂ : World D} {c : Call D} {t : Turn D} {l : List (Step D)}
    (hc : w₀.JournalCanon X.env) (h₁ : submit X w₀ c = .ok (t, w₁)) (hf : World.fold X.env w₁ l = .ok w₂) :
    ∀ r, submit X w₂ c ≠ .ok r := by
  intro ⟨t₂, w₃⟩ h₂
  obtain ⟨_, hr₁, ha₁⟩ := submit_ok h₁
  obtain ⟨_, hr₂, ha₂⟩ := submit_ok h₂
  obtain ⟨_, _, _, _, _, hid₁, _, hvu₁⟩ := receive_derived hr₁
  obtain ⟨_, _, _, _, _, hid₂, _, hvu₂⟩ := receive_derived hr₂
  exact admit_twice_window hc ha₁ hf ha₂ (by rw [hid₁, hid₂]) (by rw [hvu₁, hvu₂])

/-- **One call, one admission, on any path through `receive`.** If call `c` derived the turn
admitted from `w₀`, no later World of that log admits a turn `c` derives again. This is the
follower's form: in an `Honest` log every turn is `receive` of its own event's call
on the World before it, so an honest folded log never holds one call twice. -/
theorem derived_once {X : Ctx D} {w₀ w₁ w₂ w₃ : World D} {c : Call D} {t t' : Turn D} {l : List (Step D)}
    (hc : w₀.JournalCanon X.env)
    (hr₁ : receive X w₀ c = .ok t) (h₁ : World.admit X.env w₀ t = .ok w₁)
    (hf : World.fold X.env w₁ l = .ok w₂)
    (hr₂ : receive X w₂ c = .ok t') (h₂ : World.admit X.env w₂ t' = .ok w₃) : False := by
  obtain ⟨_, _, _, _, _, hid₁, _, hvu₁⟩ := receive_derived hr₁
  obtain ⟨_, _, _, _, _, hid₂, _, hvu₂⟩ := receive_derived hr₂
  exact admit_twice_window hc h₁ hf h₂ (by rw [hid₁, hid₂]) (by rw [hvu₁, hvu₂])

/-- **Past `journalForgets` the kernel refuses a call by its window**: its turn's window ends by
`notBefore + windowMax` (`checkBounds`), more than `windowMax` heights ago. So HOST answers such
a submit `uncertain forgotten`, which is what it is for a call committed long ago (its entry
pruned), never a false `refused`. -/
theorem submit_forgotten {X : Ctx D} {w : World D} {c : Call D}
    (hfg : journalForgets w.height c.unsigned.notBefore = true) : ∀ r, submit X w c ≠ .ok r := by
  intro ⟨t, w'⟩ h
  obtain ⟨_, hr, ha⟩ := submit_ok h
  obtain ⟨_, _, _, _, _, _, hnb, hvu⟩ := receive_derived hr
  have hw := admit_window ha
  have hb := admit_bounded ha
  unfold checkBounds at hb
  simp only [except_bind_ok] at hb
  obtain ⟨⟨⟩, _, ⟨⟩, _, ⟨⟩, _, ⟨⟩, _, ⟨⟩, _, ⟨⟩, _, ⟨⟩, _, ⟨⟩, _, ⟨⟩, hwm, _⟩ := hb
  rw [req_ok, decide_eq_true_eq] at hwm
  simp only [journalForgets, decide_eq_true_eq] at hfg
  rw [windowMax_eq] at *
  omega

theorem genesisWorld_journalOk (X : Ctx D) (name nonce : ByteArray) (allowance : Nat)
    (founders : List (ByteArray × D)) : (genesisWorld X name nonce allowance founders).JournalOk X.env :=
  journalOk_of_empty rfl

/-- **Every World a genesis reaches holds `JournalOk`**, no premise. -/
theorem reach_journalOk {X : Ctx D} {name nonce : ByteArray} {allowance : Nat}
    {founders : List (ByteArray × D)} {w : World D} {l : List (Step D)}
    (h : World.fold X.env (genesisWorld X name nonce allowance founders) l = .ok w) : w.JournalOk X.env :=
  fold_journalOk (genesisWorld_journalOk X name nonce allowance founders) h

/-- **Every World a genesis reaches holds fewer than `3 * windowMax` journal entries**, whatever
its history: no premise (law 4 at the World's journal). -/
theorem reach_journal_bounded {X : Ctx D} {name nonce : ByteArray} {allowance : Nat}
    {founders : List (ByteArray × D)} {w : World D} {l : List (Step D)}
    (h : World.fold X.env (genesisWorld X name nonce allowance founders) l = .ok w) :
    w.journal.toList.length < 3 * Bounds.windowMax :=
  journal_bounded (reach_journalOk h)

/-- **From genesis, a call is admitted at most once, ever** (`submit_once`, no premise): `w₀` is
any World a genesis reaches. -/
theorem reach_submit_once {X : Ctx D} {name nonce : ByteArray} {allowance : Nat}
    {founders : List (ByteArray × D)} {l₀ l : List (Step D)} {w₀ w₁ w₂ : World D} {c : Call D} {t : Turn D}
    (h₀ : World.fold X.env (genesisWorld X name nonce allowance founders) l₀ = .ok w₀)
    (h₁ : submit X w₀ c = .ok (t, w₁)) (hf : World.fold X.env w₁ l = .ok w₂) :
    ∀ r, submit X w₂ c ≠ .ok r :=
  submit_once (reach_journalOk h₀).1 h₁ hf

/-- **From genesis, one call, one admission on any path through `receive`** (`derived_once`, no
premise). -/
theorem reach_derived_once {X : Ctx D} {name nonce : ByteArray} {allowance : Nat}
    {founders : List (ByteArray × D)} {l₀ l : List (Step D)} {w₀ w₁ w₂ w₃ : World D} {c : Call D}
    {t t' : Turn D}
    (h₀ : World.fold X.env (genesisWorld X name nonce allowance founders) l₀ = .ok w₀)
    (hr₁ : receive X w₀ c = .ok t) (h₁ : World.admit X.env w₀ t = .ok w₁)
    (hf : World.fold X.env w₁ l = .ok w₂)
    (hr₂ : receive X w₂ c = .ok t') (h₂ : World.admit X.env w₂ t' = .ok w₃) : False :=
  derived_once (reach_journalOk h₀).1 hr₁ h₁ hf hr₂ h₂

/-- **From genesis, two admissions of one transaction id are more than `2 * windowMax` heights
apart** (`admit_spacing`, no premise). -/
theorem reach_admit_spacing {X : Ctx D} {name nonce : ByteArray} {allowance : Nat}
    {founders : List (ByteArray × D)} {l₀ l : List (Step D)} {w₀ w₁ w₂ w₃ : World D} {t t' : Turn D}
    (h₀ : World.fold X.env (genesisWorld X name nonce allowance founders) l₀ = .ok w₀)
    (h₁ : World.admit X.env w₀ t = .ok w₁) (hf : World.fold X.env w₁ l = .ok w₂)
    (h₂ : World.admit X.env w₂ t' = .ok w₃) (hid : t'.txId = t.txId) :
    w₀.height + 1 + 2 * Bounds.windowMax ≤ w₂.height :=
  admit_spacing (reach_journalOk h₀).1 h₁ hf h₂ hid

/-- **From genesis, pruning changed no check** (`fold_prune_check`, every premise but the
window discharged): a World a genesis reaches checks each windowed retry exactly as the same
World carrying the latest entry its log wrote under each transaction id, none pruned. -/
theorem reach_prune_check {X : Ctx D} {name nonce : ByteArray} {allowance : Nat}
    {founders : List (ByteArray × D)} {w : World D} {l : List (Step D)} {t : Turn D}
    (h : World.fold X.env (genesisWorld X name nonce allowance founders) l = .ok w)
    (hv : ∀ e, (shadowJournal X.env (genesisWorld X name nonce allowance founders).height
        (genesisWorld X name nonce allowance founders).journal l).get (journalSpec X.env) t.txId = some e →
      t.validUntil ≤ e.1 + Bounds.windowMax) :
    check X.env w t = check X.env { w with journal := (shadowJournal X.env
      (genesisWorld X name nonce allowance founders).height
      (genesisWorld X name nonce allowance founders).journal l) } t :=
  let hg := genesisWorld_journalOk X name nonce allowance founders
  fold_prune_check hg.1 (journalFiltered_self hg) h hv

/-! ## A call's retry needs no window premise (KERNEL-38 (c))

`fold_prune_check` takes `hv`: the retry's window ends by its transaction id's never-pruned entry
height plus `windowMax`. At bare `admit` that premise cannot be dropped (the sim arm
`journal-shadow-reuse:replayed`: a recycled id under a fresh window is admitted by the real fold and
refused `replayed` against the never-pruned journal). On a log every turn of which is a call's turn
(`CallLog`; every `Honest` log is one, `honest_callLog`), the never-pruned entry under a call's
transaction id was written by a call with that digest: the retry's own call, whose window is the
retry's, or a DIFFERENT call with the same digest, and then two of the events the theorem names
(`retryPres`: the retry's event and every event of the log, under `domTx`) collide. A turn is a
call's turn when its event decodes to that call and it carries the call's bytes, digest and window:
what `Honest` says of every logged turn, and what `receive` gives
(`callTurn_of_receive`). -/

/-- `t` is call `c`'s turn as a follower re-reads it: its event decodes to `c`, and it carries `c`'s
canonical bytes, `c`'s transaction id and `c`'s window end. -/
def CallTurn (X : Ctx D) (t : Turn D) : Prop :=
  ∃ c, X.decodeCall t.event = some c ∧ t.event = X.callBytes c ∧ t.txId = txIdOf X c ∧
    t.validUntil = c.unsigned.validUntil

/-- Every turn of the log is a call's turn. -/
def CallLog (X : Ctx D) (l : List (Step D)) : Prop := ∀ u ∈ Step.turns l, CallTurn X u

/-- A turn `receive` derives from a call its event decodes to is that call's turn. -/
theorem callTurn_of_receive {X : Ctx D} {v : World D} {c : Call D} {t : Turn D}
    (hd : X.decodeCall t.event = some c) (hr : receive X v c = .ok t) : CallTurn X t := by
  obtain ⟨_, _, _, _, he, hid, _, hvu⟩ := receive_derived hr
  exact ⟨c, hd, he, hid, hvu⟩

/-- **An `Honest` log is a call log**: every turn in it is `receive` of the call its own event
decodes to. -/
theorem honest_callLog {X : Ctx D} : ∀ {w w' : World D} {l : List (Step D)},
    Honest X w l → World.fold X.env w l = .ok w' → CallLog X l
  | _, _, [], _, _ => fun u hu => by simp [Step.turns] at hu
  | _, _, .turn t :: _, hh, h => by
      obtain ⟨w₁, h₁, h₂⟩ := fold_cons_ok.mp h
      obtain ⟨c, hd, hr, hrest⟩ := hh
      intro u hu
      simp only [Step.turns, List.mem_cons] at hu
      rcases hu with rfl | hu
      · exact callTurn_of_receive hd hr
      · exact honest_callLog (hrest w₁ h₁) h₂ u hu
  | _, _, .refusal _ :: _, hh, h => by
      obtain ⟨w₁, h₁, h₂⟩ := fold_cons_ok.mp h
      obtain ⟨_, _, _, _, _, hrest⟩ := hh
      intro u hu
      simp only [Step.turns] at hu
      exact honest_callLog (hrest w₁ h₁) h₂ u hu

omit [Ord D] [DecidableEq D] in
/-- Two call turns under one transaction id carry one window, or their events are two different
inputs with one `domTx` digest. -/
theorem callTurn_window {X : Ctx D} {t u : Turn D} (ht : CallTurn X t) (hu : CallTurn X u)
    (hid : t.txId = u.txId) :
    t.validUntil = u.validUntil ∨ CollidesAmong X.env.hash [(domTx, t.event), (domTx, u.event)] := by
  obtain ⟨c, hd, he, hti, hvu⟩ := ht
  obtain ⟨c', hd', he', hui, hvu'⟩ := hu
  by_cases hev : t.event = u.event
  · left
    rw [hev, hd'] at hd
    cases hd
    rw [hvu, hvu']
  · right
    refine CollidesAmong.pair (fun h => hev (Prod.mk.inj h).2) ?_
    have : txIdOf X c = txIdOf X c' := hti.symm.trans (hid.trans hui)
    unfold txIdOf at this
    show X.env.hash domTx t.event = X.env.hash domTx u.event
    rw [he, he']
    exact this

/-- An admitted turn's window ends within `windowMax` of the height it lands at. -/
theorem admit_window_end {E : Env D} {w w' : World D} {t : Turn D} (h : World.admit E w t = .ok w') :
    t.validUntil ≤ w.height + 1 + Bounds.windowMax := by
  have hw := (admit_window h).1
  have hb := admit_bounded h
  unfold checkBounds at hb
  simp only [except_bind_ok] at hb
  obtain ⟨⟨⟩, _, ⟨⟩, _, ⟨⟩, _, ⟨⟩, _, ⟨⟩, _, ⟨⟩, _, ⟨⟩, _, ⟨⟩, _, ⟨⟩, hwm, _⟩ := hb
  rw [req_ok, decide_eq_true_eq] at hwm
  omega

omit [Ord D] [DecidableEq D] in
theorem retryPres_tail {t u : Turn D} {rest : List (Step D)} {x : String × ByteArray}
    (hx : x ∈ retryPres t rest) : x ∈ retryPres t (.turn u :: rest) := by
  simp only [retryPres, Step.turns, List.map_cons, List.mem_cons] at hx ⊢
  rcases hx with h | h
  · exact .inl h
  · exact .inr (.inr h)

/-- The induction behind `call_retry_window`, over any list `S` of inputs holding `retryPres`. -/
theorem shadow_call_window {X : Ctx D} {t : Turn D} (ht : CallTurn X t) :
    ∀ {w w' : World D} {J : Journal D} {l : List (Step D)} (S : List (String × ByteArray)),
      (∀ x ∈ retryPres t l, x ∈ S) → World.fold X.env w l = .ok w' → CallLog X l →
      ((∀ e, J.get (journalSpec X.env) t.txId = some e → t.validUntil ≤ e.1 + Bounds.windowMax) ∨
        CollidesAmong X.env.hash S) →
      (∀ e, (shadowJournal X.env w.height J l).get (journalSpec X.env) t.txId = some e →
        t.validUntil ≤ e.1 + Bounds.windowMax) ∨ CollidesAmong X.env.hash S
  | _, _, _, [], _, _, _, _, hJ => hJ
  | _, _, J, .refusal _ :: rest, S, hS, h, hl, hJ => by
      obtain ⟨w₁, h₁, h₂⟩ := fold_cons_ok.mp h
      have hh := (refuse_frame h₁).2.2.1
      have := shadow_call_window ht (J := J) (l := rest) S
        (fun x hx => hS x (by simpa [retryPres, Step.turns] using hx)) h₂
        (fun u hu => hl u (by simpa [Step.turns] using hu)) hJ
      rw [hh] at this
      exact this
  | w, _, J, .turn u :: rest, S, hS, h, hl, hJ => by
      obtain ⟨w₁, h₁, h₂⟩ := fold_cons_ok.mp h
      have hh := admit_height h₁
      have hu : CallTurn X u := hl u (by simp [Step.turns])
      have hJ' : (∀ e, (J.insert (journalSpec X.env) u.txId (w.height + 1, turnDigest X.env u)).get
            (journalSpec X.env) t.txId = some e → t.validUntil ≤ e.1 + Bounds.windowMax) ∨
          CollidesAmong X.env.hash S := by
        rcases hJ with hJ | hc
        · by_cases hk : t.txId = u.txId
          · rcases callTurn_window ht hu hk with hv | hc
            · left
              intro e he
              rw [Trie.get_insert, if_pos hk] at he
              cases he
              have := admit_window_end h₁
              show t.validUntil ≤ w.height + 1 + Bounds.windowMax
              omega
            · right
              refine hc.mono fun x hx => hS x ?_
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
              rcases hx with rfl | rfl <;> simp [retryPres, Step.turns]
          · left
            intro e he
            rw [Trie.get_insert, if_neg hk] at he
            exact hJ e he
        · exact .inr hc
      have := shadow_call_window ht (J := J.insert (journalSpec X.env) u.txId (w.height + 1, turnDigest X.env u))
        (l := rest) S (fun x hx => hS x (retryPres_tail hx)) h₂
        (fun v hv => hl v (by simp [Step.turns, hv])) hJ'
      rw [hh] at this
      exact this

/-- **A call's retry is windowed on a call log.** On a log the fold admitted every turn of which is a
call's turn, a call's turn `t` (a retry) ends its window by its transaction id's never-pruned entry
height plus `windowMax` (`fold_prune_check`'s `hv`), or two of the events `retryPres t l` names have
one `domTx` digest; given only that the starting journal `J` already meets the bound (true of every
empty journal: the genesis's). -/
theorem call_retry_window {X : Ctx D} {w w' : World D} {J : Journal D} {l : List (Step D)} {t : Turn D}
    (h : World.fold X.env w l = .ok w') (hl : CallLog X l) (ht : CallTurn X t)
    (hJ : ∀ e, J.get (journalSpec X.env) t.txId = some e → t.validUntil ≤ e.1 + Bounds.windowMax) :
    (∀ e, (shadowJournal X.env w.height J l).get (journalSpec X.env) t.txId = some e →
      t.validUntil ≤ e.1 + Bounds.windowMax) ∨ CollidesAmong X.env.hash (retryPres t l) :=
  shadow_call_window ht _ (fun _ hx => hx) h hl (.inl hJ)

/-- **`hv` on an `Honest` log** (the follower's: `rederiveLog_sound`), for a retry `receive` derives from the
call its event decodes to (on any World `v`), up to a collision among `retryPres t l`. -/
theorem honest_retry_window {X : Ctx D} {w w' v : World D} {J : Journal D} {l : List (Step D)}
    {t : Turn D} {c : Call D} (hH : Honest X w l) (h : World.fold X.env w l = .ok w')
    (hd : X.decodeCall t.event = some c) (hr : receive X v c = .ok t)
    (hJ : ∀ e, J.get (journalSpec X.env) t.txId = some e → t.validUntil ≤ e.1 + Bounds.windowMax) :
    (∀ e, (shadowJournal X.env w.height J l).get (journalSpec X.env) t.txId = some e →
      t.validUntil ≤ e.1 + Bounds.windowMax) ∨ CollidesAmong X.env.hash (retryPres t l) :=
  call_retry_window h (honest_callLog hH h) (callTurn_of_receive hd hr) hJ

/-- **Pruning changed no check of a call's retry on an `Honest` log** (`fold_prune_check` with `hv`
discharged by `honest_retry_window`), up to a collision among `retryPres t l`. -/
theorem honest_prune_check {X : Ctx D} {w w' v : World D} {J : Journal D} {l : List (Step D)}
    {t : Turn D} {c : Call D} (hc : w.JournalCanon X.env)
    (hj : JournalFiltered X.env (lastPrune w.height) w.journal J) (h : World.fold X.env w l = .ok w')
    (hH : Honest X w l) (hd : X.decodeCall t.event = some c) (hr : receive X v c = .ok t)
    (hJ : ∀ e, J.get (journalSpec X.env) t.txId = some e → t.validUntil ≤ e.1 + Bounds.windowMax) :
    check X.env w' t = check X.env { w' with journal := shadowJournal X.env w.height J l } t ∨
      CollidesAmong X.env.hash (retryPres t l) :=
  (honest_retry_window hH h hd hr hJ).imp (fold_prune_check hc hj h) id

/-- **From genesis, pruning changed no check of a call's retry: no window premise.** A World `w` the
follower's honest folded log reaches from a genesis checks a call's retry (a turn `receive` derives, on any
World, from the call its event decodes to) exactly as the same World carrying the journal its log
never pruned, or two of the events `retryPres t l` names have one `domTx` digest. -/
theorem reach_prune_check_call {X : Ctx D} {name nonce : ByteArray} {allowance : Nat}
    {founders : List (ByteArray × D)} {w v : World D} {l : List (Step D)} {t : Turn D} {c : Call D}
    (hf : World.fold X.env (genesisWorld X name nonce allowance founders) l = .ok w)
    (hh : Honest X (genesisWorld X name nonce allowance founders) l)
    (hd : X.decodeCall t.event = some c) (hr : receive X v c = .ok t) :
    check X.env w t = check X.env { w with journal := (shadowJournal X.env
      (genesisWorld X name nonce allowance founders).height
      (genesisWorld X name nonce allowance founders).journal l) } t ∨
      CollidesAmong X.env.hash (retryPres t l) :=
  let hg := genesisWorld_journalOk X name nonce allowance founders
  honest_prune_check hg.1 (journalFiltered_self hg) hf hh hd hr (fun e he => by
    rw [show (genesisWorld X name nonce allowance founders).journal = .empty from rfl,
      Trie.get_empty] at he
    cases he)

/-- TOOTH (`reach_prune_check_call`): under a hash that separates the events `retryPres t l` names,
pruning changed no check of a call's retry. -/
theorem reach_prune_check_call_sep {X : Ctx D} {name nonce : ByteArray} {allowance : Nat}
    {founders : List (ByteArray × D)} {w v : World D} {l : List (Step D)} {t : Turn D} {c : Call D}
    (hf : World.fold X.env (genesisWorld X name nonce allowance founders) l = .ok w)
    (hh : Honest X (genesisWorld X name nonce allowance founders) l)
    (hd : X.decodeCall t.event = some c) (hr : receive X v c = .ok t)
    (hsep : Separates X.env.hash (retryPres t l)) :
    check X.env w t = check X.env { w with journal := (shadowJournal X.env
      (genesisWorld X name nonce allowance founders).height
      (genesisWorld X name nonce allowance founders).journal l) } t :=
  hsep.elim (reach_prune_check_call hf hh hd hr)

/-! ### Teeth, on a concrete call log

A toy `Ctx` over one-byte digests: a call's bytes are its window end in two little-endian bytes,
decoded back to the canonical call with that window end; the hash is an input's first byte, so the
events of windows `1` and `2049` (`[1, 0]`, `[1, 8]`) collide and those of `1025` and `2` (`[1, 4]`,
`[2, 0]`) do not. Every turn below has no touches, its charge its weight, and is admitted (by
`decide`) from an empty World at height 0. -/

private def rtEnv : Env UInt8 where
  hash _ b := b.data.getD 0 0
  bytes d := ⟨#[d]⟩
  turnBytes _ := ByteArray.empty
  cellBytes _ := ByteArray.empty

private def rtBytes (v : Nat) : ByteArray := ⟨#[UInt8.ofNat v, UInt8.ofNat (v / 256)]⟩

private def rtCall (v : Nat) : Call UInt8 :=
  let u : Unsigned UInt8 :=
    { world := 0
      member := 0
      key := ByteArray.empty
      notBefore := 0
      validUntil := v
      pins := []
      maxCharge := 0
      body := .revoke 0 }
  { unsigned := u, signature := ByteArray.empty }

private def rtCtx : Ctx UInt8 where
  env := rtEnv
  unsignedBytes _ := ByteArray.empty
  callBytes c := rtBytes c.unsigned.validUntil
  decodeCall b := if b.size = 2 then
      some (rtCall ((b.data.getD 0 0).toNat + 256 * (b.data.getD 1 0).toNat)) else none
  digestOf _ := none
  verify _ _ _ := false
  program :=
    { checkInstall := fun _ _ => .error (.program "toy")
      judge := fun _ _ _ _ _ _ => .error (.program "toy")
      run := fun _ _ _ _ _ _ _ _ => .error (.program "toy")
      rels := fun _ _ _ => .error (.program "toy") }

/-- A turn under window `[nb, v]` carrying the event of the call with window end `ev`, its txId that
event's digest, charging its weight. -/
private def rtTurn (nb v ev : Nat) : Turn UInt8 :=
  let t0 : Turn UInt8 :=
    { txId := rtEnv.hash domTx (rtBytes ev)
      notBefore := nb
      validUntil := v
      touches := []
      creates := []
      nullifiers := []
      charge := 0
      event := rtBytes ev }
  { t0 with charge := t0.weight }

private def rtWorld : World UInt8 where
  trie := .empty
  journal := .empty
  refusals := .empty
  rows := .empty
  height := 0
  steps := 0
  chain := 0
  allowance := 1000000
  origin := 0

private theorem rt_callTurn (nb v : Nat) (hd : rtCtx.decodeCall (rtBytes v) = some (rtCall v)) :
    CallTurn rtCtx (rtTurn nb v v) :=
  ⟨rtCall v, hd, rfl, rfl, rfl⟩

private instance (hash : String → ByteArray → UInt8) (S : List (String × ByteArray)) :
    Decidable (Separates hash S) := by
  unfold Separates; infer_instance

private theorem rt_fold_ok {l : List (Step UInt8)} (h : (World.fold rtEnv rtWorld l).isOk = true) :
    ∃ w', World.fold rtCtx.env rtWorld l = .ok w' := by
  cases hf : World.fold rtEnv rtWorld l with
  | error e => rw [hf] at h; cases h
  | ok w' => exact ⟨w', hf⟩

/-- The retry and a second call: windows `[1, 1025]` and `[1, 2]`, at heights 1 and 2. -/
private def sepLog : List (Step UInt8) := [.turn (rtTurn 1 1025 1025), .turn (rtTurn 1 2 2)]

/-- **TOOTH (`_sep`, on an instance): the window disjunct carries the content.** On a call log the
fold admits, from a World with an empty journal, the retry of the first call has a never-pruned entry
(at height 1) and its window ends exactly at that height plus `windowMax`, while the hash separates
the three events `retryPres` names (two of them distinct): the collision disjunct is false. -/
theorem call_retry_window_sep_instance :
    ∃ (X : Ctx UInt8) (w w' : World UInt8) (l : List (Step UInt8)) (t : Turn UInt8),
      World.fold X.env w l = .ok w' ∧ CallLog X l ∧ CallTurn X t ∧ w.journal = .empty ∧
      Separates X.env.hash (retryPres t l) ∧ ¬ CollidesAmong X.env.hash (retryPres t l) ∧
      (∃ p ∈ retryPres t l, ∃ q ∈ retryPres t l, p ≠ q) ∧
      (shadowJournal X.env w.height w.journal l).get (journalSpec X.env) t.txId =
        some (1, turnDigest X.env t) ∧
      t.validUntil = 1 + Bounds.windowMax := by
  obtain ⟨w', hf⟩ := rt_fold_ok (l := sepLog) (by decide)
  have hsep : Separates rtCtx.env.hash (retryPres (rtTurn 1 1025 1025) sepLog) := by decide
  refine ⟨rtCtx, rtWorld, w', sepLog, rtTurn 1 1025 1025, hf, ?_, rt_callTurn 1 1025 (by decide), rfl,
    hsep, hsep.not_collides, by decide, by decide, rfl⟩
  intro u hu
  simp only [sepLog, Step.turns, List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl
  · exact rt_callTurn 1 1025 (by decide)
  · exact rt_callTurn 1 2 (by decide)

/-- A call log whose one call (window `[1, 1]`, event `[1, 0]`) shares its digest with the retry's
call (window `[1025, 2049]`, event `[1, 8]`). -/
private def colLog : List (Step UInt8) := [.turn (rtTurn 1 1 1)]

/-- **DISJUNCT CHECK (the window disjunct is not provable from the premises).** On a call log the
fold admits, from an empty journal, a call's retry whose window ends past its id's never-pruned entry
height plus `windowMax`: the window disjunct is false, and the collision disjunct holds. -/
theorem call_retry_window_collides_instance :
    ∃ (X : Ctx UInt8) (w w' : World UInt8) (l : List (Step UInt8)) (t : Turn UInt8),
      World.fold X.env w l = .ok w' ∧ CallLog X l ∧ CallTurn X t ∧ w.journal = .empty ∧
      ¬ (∀ e, (shadowJournal X.env w.height w.journal l).get (journalSpec X.env) t.txId = some e →
        t.validUntil ≤ e.1 + Bounds.windowMax) ∧
      CollidesAmong X.env.hash (retryPres t l) := by
  obtain ⟨w', hf⟩ := rt_fold_ok (l := colLog) (by decide)
  refine ⟨rtCtx, rtWorld, w', colLog, rtTurn 1025 2049 2049, hf, ?_, rt_callTurn 1025 2049 (by decide),
    rfl, ?_, ?_⟩
  · intro u hu
    simp only [colLog, Step.turns, List.mem_cons, List.not_mem_nil, or_false] at hu
    subst hu
    exact rt_callTurn 1 1 (by decide)
  · intro hv
    have := hv (1, turnDigest rtEnv (rtTurn 1 1 1)) (by decide)
    revert this
    decide
  · exact ⟨_, List.mem_cons_self .., (domTx, rtBytes 1), List.mem_cons_of_mem _ (List.mem_cons_self ..),
      by decide, by decide⟩

/-- A log whose one turn carries the event of the call with window end `2049` (event `[1, 8]`) under
the window `[1, 1]`: admitted at bare `admit`, but not that call's turn. -/
private def rawLog : List (Step UInt8) := [.turn (rtTurn 1 1 2049)]

/-- **TOOTH (`CallLog` is load-bearing in `call_retry_window`).** Drop the call-log premise and keep
every other premise of `call_retry_window`: a log the fold admits, from an empty journal, whose one
turn carries a call's event under a window not that call's (the `journal-shadow-reuse:replayed` shape:
one transaction id, two windows), and that call's own turn as the retry. That log is no call log;
`hv` fails, and the collision disjunct is false too (the only two events named are one). Its
`¬ Honest` comes only through `honest_callLog`: `rtCtx` accepts no signature, so its `receive` derives
nothing and this instance does not exercise the `hr` premise of the `Honest` forms
(`honest_retry_window_needs_honest` does). -/
theorem call_retry_window_needs_callLog :
    ∃ (X : Ctx UInt8) (w w' : World UInt8) (l : List (Step UInt8)) (t : Turn UInt8),
      World.fold X.env w l = .ok w' ∧ CallTurn X t ∧ w.journal = .empty ∧
      ¬ CallLog X l ∧ ¬ Honest X w l ∧
      ¬ (∀ e, (shadowJournal X.env w.height w.journal l).get (journalSpec X.env) t.txId = some e →
        t.validUntil ≤ e.1 + Bounds.windowMax) ∧
      ¬ CollidesAmong X.env.hash (retryPres t l) := by
  obtain ⟨w', hf⟩ := rt_fold_ok (l := rawLog) (by decide)
  have hnl : ¬ CallLog rtCtx rawLog := by
    intro hl
    obtain ⟨c, hd, -, -, hvu⟩ := hl (rtTurn 1 1 2049) (by simp [rawLog, Step.turns])
    have hd' : rtCtx.decodeCall (rtTurn 1 1 2049).event = some (rtCall 2049) := by decide
    rw [hd'] at hd
    cases hd
    revert hvu
    decide
  have hsep : Separates rtCtx.env.hash (retryPres (rtTurn 1025 2049 2049) rawLog) := by decide
  refine ⟨rtCtx, rtWorld, w', rawLog, rtTurn 1025 2049 2049, hf, rt_callTurn 1025 2049 (by decide), rfl,
    hnl, fun hH => hnl (honest_callLog hH hf), ?_, hsep.not_collides⟩
  intro hv
  have := hv (1, turnDigest rtEnv (rtTurn 1 1 2049)) (by decide)
  revert this
  decide

/-! ### The same tooth on an `Honest` log: two signed rotations

A toy `Ctx` whose calls are key rotations (`rotate` needs no current-key check and reads only the
member's own pinned cell), with every signature accepted and a six-byte codec (window end, member,
new key, next digest, pin) decoded back to the rotation it encodes. A World with two members, 7 and 8,
each precommitted to its next key; the log is member 7's rotation (window `[1, 1025]`) then member
8's (window `[1, 2]`), each `receive` of the call its event decodes to on the World before it. The
retry is member 7's call derived again on the starting World. -/

private def isOkAs {ε α : Type} [DecidableEq α] : Except ε α → α → Bool
  | .ok b, a => decide (b = a)
  | .error _, _ => false

private theorem of_isOkAs {ε α : Type} [DecidableEq α] {x : Except ε α} {a : α}
    (h : isOkAs x a = true) : x = .ok a := by
  cases x with
  | ok b => simp only [isOkAs, decide_eq_true_eq] at h; rw [h]
  | error _ => cases h

/-- `Honest`, decided for logs of turns: each turn is `receive` of the call its event decodes to. -/
private def honestB (X : Ctx UInt8) : World UInt8 → List (Step UInt8) → Bool
  | _, [] => true
  | w, .turn t :: rest =>
      match X.decodeCall t.event with
      | none => false
      | some c => isOkAs (receive X w c) t &&
          match World.admit X.env w t with
          | .ok w' => honestB X w' rest
          | .error _ => true
  | _, .refusal _ :: _ => false

private theorem honest_of_honestB {X : Ctx UInt8} :
    ∀ {w : World UInt8} {l : List (Step UInt8)}, honestB X w l = true → Honest X w l
  | _, [], _ => trivial
  | w, .turn t :: rest, h => by
      simp only [honestB] at h
      split at h
      · cases h
      · rename_i c hd
        simp only [Bool.and_eq_true] at h
        refine ⟨c, hd, of_isOkAs h.1, fun w' ha => ?_⟩
        have h2 := h.2
        rw [ha] at h2
        exact honest_of_honestB h2
  | _, .refusal _ :: _, h => by simp [honestB] at h

private def hCall (m nk nn : UInt8) (vu : Nat) (p : UInt8) : Call UInt8 :=
  let u : Unsigned UInt8 :=
    { world := 0
      member := m
      key := ⟨#[nk]⟩
      notBefore := 1
      validUntil := vu
      pins := [(m, p)]
      maxCharge := 100000
      body := .rotate ⟨#[nk]⟩ nn }
  { unsigned := u, signature := ByteArray.empty }

private def hBytes (c : Call UInt8) : ByteArray :=
  ⟨#[UInt8.ofNat c.unsigned.validUntil, UInt8.ofNat (c.unsigned.validUntil / 256), c.unsigned.member,
    c.unsigned.key.data.getD 0 0, (match c.unsigned.body with | .rotate _ n => n | _ => 0),
    (c.unsigned.pins.head?.map Prod.snd).getD 0]⟩

private def hCtx : Ctx UInt8 where
  env := rtEnv
  unsignedBytes _ := ByteArray.empty
  callBytes := hBytes
  decodeCall b := if b.size = 6 then
      some (hCall (b.data.getD 2 0) (b.data.getD 3 0) (b.data.getD 4 0)
        ((b.data.getD 0 0).toNat + 256 * (b.data.getD 1 0).toNat) (b.data.getD 5 0)) else none
  digestOf b := if b.size = 1 then some (b.data.getD 0 0) else none
  verify _ _ _ := true
  program := rtCtx.program

private def hMember (k nxt : UInt8) : Cell :=
  { kind := kindMember, discipline := .ram, slots := [(slotKey, ⟨#[k]⟩), (slotNext, ⟨#[nxt]⟩)] }

private def hWorld : World UInt8 :=
  let t7 := Trie.T.empty.insert (trieSpec rtEnv) (.cell 7) (.entry (.live (hMember 10 20) 0))
  let tr := t7.insert (trieSpec rtEnv) (.cell 8) (.entry (.live (hMember 11 21) 0))
  { rtWorld with trie := tr }

private def hCall1 : Call UInt8 := hCall 7 20 30 1025 (pinOf rtEnv (some (.live (hMember 10 20) 0)))
private def hCall2 : Call UInt8 := hCall 8 21 31 2 (pinOf rtEnv (some (.live (hMember 11 21) 0)))

private def hDummy : Turn UInt8 := rtTurn 0 0 0

private def hTurn1 : Turn UInt8 := ((receive hCtx hWorld hCall1).toOption).getD hDummy
private def hTurn2 : Turn UInt8 := ((receive hCtx hWorld hCall2).toOption).getD hDummy

private def hLog : List (Step UInt8) := [.turn hTurn1, .turn hTurn2]

/-- **TOOTH (`_sep`, on an `Honest` instance): every premise of `honest_retry_window` holds and the
window disjunct carries the content.** On a two-call `Honest` log the fold admits from a World with
an empty journal, member 7's call re-derived on the starting World (a turn `receive` derives from the
call its event decodes to) has its never-pruned entry at height 1 and its window ends exactly at that
height plus `windowMax`; the hash separates the events `retryPres` names, two of which differ, so the
collision disjunct is false. -/
theorem honest_retry_window_sep_instance :
    ∃ (X : Ctx UInt8) (w w' v : World UInt8) (l : List (Step UInt8)) (t : Turn UInt8) (c : Call UInt8),
      Honest X w l ∧ World.fold X.env w l = .ok w' ∧ X.decodeCall t.event = some c ∧
      receive X v c = .ok t ∧ w.journal = .empty ∧
      Separates X.env.hash (retryPres t l) ∧ ¬ CollidesAmong X.env.hash (retryPres t l) ∧
      (∃ p ∈ retryPres t l, ∃ q ∈ retryPres t l, p ≠ q) ∧
      (shadowJournal X.env w.height w.journal l).get (journalSpec X.env) t.txId =
        some (1, turnDigest X.env t) ∧
      t.validUntil = 1 + Bounds.windowMax := by
  obtain ⟨w', hf⟩ : ∃ w', World.fold hCtx.env hWorld hLog = .ok w' := by
    have h : (World.fold rtEnv hWorld hLog).isOk = true := by decide
    cases hf : World.fold rtEnv hWorld hLog with
    | error e => rw [hf] at h; cases h
    | ok w' => exact ⟨w', hf⟩
  have hsep : Separates hCtx.env.hash (retryPres hTurn1 hLog) := by decide
  refine ⟨hCtx, hWorld, w', hWorld, hLog, hTurn1, hCall1, honest_of_honestB (by decide), hf,
    by decide, of_isOkAs (by decide), rfl, hsep, hsep.not_collides, by decide, by decide, by decide⟩


/-- Member 7's rotation with window end `2049`; its derived turn (window `[1, 2049]`) is the retry. -/
private def hCallR : Call UInt8 := hCall 7 20 30 2049 (pinOf rtEnv (some (.live (hMember 10 20) 0)))
private def hTurnR : Turn UInt8 := ((receive hCtx hWorld hCallR).toOption).getD hDummy

/-- The logged turn: the retry's call event (and its touches and charge) under the window `[1, 1]`. -/
private def hRawLog : List (Step UInt8) := [.turn { hTurnR with validUntil := 1 }]

/-- **TOOTH (`Honest` is load-bearing in `honest_retry_window`; the in-Lean twin of the sim arm
`journal-shadow-reuse:replayed`).** On `hCtx`, where every signature verifies, keep every premise of
`honest_retry_window` but `Honest`: a one-turn log the fold admits from an empty journal, the turn
carrying member 7's call event under the window `[1, 1]` where the call says `2049`, and as the retry
that call's real `receive` output, whose event decodes to the call. The log is not `Honest` (the
call derives another turn), `hv` fails (`2049 > 1 + windowMax`), and the collision disjunct is false
(the two events `retryPres` names are one). So the window premise cannot be dropped for a log the
follower would not take. -/
theorem honest_retry_window_needs_honest :
    ∃ (X : Ctx UInt8) (w w' v : World UInt8) (l : List (Step UInt8)) (t : Turn UInt8) (c : Call UInt8),
      World.fold X.env w l = .ok w' ∧ X.decodeCall t.event = some c ∧ receive X v c = .ok t ∧
      w.journal = .empty ∧ ¬ Honest X w l ∧
      ¬ (∀ e, (shadowJournal X.env w.height w.journal l).get (journalSpec X.env) t.txId = some e →
        t.validUntil ≤ e.1 + Bounds.windowMax) ∧
      ¬ CollidesAmong X.env.hash (retryPres t l) := by
  obtain ⟨w', hf⟩ : ∃ w', World.fold hCtx.env hWorld hRawLog = .ok w' := by
    have h : (World.fold rtEnv hWorld hRawLog).isOk = true := by decide
    cases hf : World.fold rtEnv hWorld hRawLog with
    | error e => rw [hf] at h; cases h
    | ok w' => exact ⟨w', hf⟩
  have hrt : receive hCtx hWorld hCallR = .ok hTurnR := of_isOkAs (by decide)
  have hdt : hCtx.decodeCall hTurnR.event = some hCallR := by decide
  have hnh : ¬ Honest hCtx hWorld hRawLog := by
    rintro ⟨c, hd, hr, -⟩
    rw [show ({ hTurnR with validUntil := 1 } : Turn UInt8).event = hTurnR.event from rfl, hdt] at hd
    cases hd
    rw [hrt] at hr
    have := congrArg Turn.validUntil (Except.ok.inj hr)
    revert this
    decide
  have hsep : Separates hCtx.env.hash (retryPres hTurnR hRawLog) := by decide
  refine ⟨hCtx, hWorld, w', hWorld, hRawLog, hTurnR, hCallR, hf, hdt, hrt, rfl, hnh, ?_, hsep.not_collides⟩
  intro hv
  have := hv (1, turnDigest rtEnv { hTurnR with validUntil := 1 }) (by decide)
  revert this
  decide

end Nanodregg.Kernel.Receive
