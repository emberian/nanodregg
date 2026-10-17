/-
# Kernel.Proofs.Journal — the journal is pruned to the window, and what it answers is true (KERNEL-33)

`commit` prunes the journal at every multiple of `Bounds.windowMax` to the entries still `kept`
(fewer than `2 * windowMax` heights old). What that costs and what it keeps:

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
  window afterwards). No premise and no collision disjunct: one call has one digest and one
  window. The follower's path is the audit (`audit_ok`), where every turn is `receive` of its own
  event, so the same holds there.
* `reach_journal_bounded`: the bound for every World a genesis reaches, with no premise.
* `admit_prune_verdict`: pruning changes no verdict of any turn whose window ends by its
  transaction id's entry height plus `windowMax` (every call-derived retry): the window is
  checked before the journal, so an expired retry is `outsideWindow` with or without its entry.
-/
import Kernel.Proofs.Fold
import Kernel.Proofs.Receive
import Kernel.Receive.Follow
import Kernel.Sim.Shadow

namespace Nanodregg.Kernel

variable {D : Type} [Ord D] [Std.TransOrd D] [Std.LawfulEqOrd D] [DecidableEq D]

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

/-- Every journal entry is at most the World's height and fewer than `2 * windowMax` heights
behind it, plus the heights since the last prune; and distinct entries have distinct heights
(one admission per height). -/
def World.JournalOk (w : World D) : Prop :=
  (∀ (k : D) (e : Nat × D), w.journal[k]? = some e → e.1 ≤ w.height ∧
    w.height < e.1 + 2 * Bounds.windowMax + w.height % Bounds.windowMax) ∧
  (∀ (k₁ k₂ : D) (e₁ e₂ : Nat × D), w.journal[k₁]? = some e₁ → w.journal[k₂]? = some e₂ →
    e₁.1 = e₂.1 → k₁ = k₂)

omit [Std.TransOrd D] [Std.LawfulEqOrd D] [DecidableEq D] in
theorem journalOk_of_empty {w : World D} (h : ∀ k : D, w.journal[k]? = none) : w.JournalOk :=
  ⟨fun k e he => (by rw [h k] at he; cases he), fun k _ _ _ he _ _ => (by rw [h k] at he; cases he)⟩

omit [Std.LawfulEqOrd D] [DecidableEq D] in
theorem genesis_journalOk (E : Env D) (o : D) (a : Nat) : (World.genesis E o a).JournalOk :=
  journalOk_of_empty fun _ => Std.TreeMap.getElem?_emptyc

/-- An entry of a committed World: the turn's own, or an older one that pruning kept. -/
theorem commit_journal_mem {E : Env D} {w : World D} {t : Turn D} {posts : List (Post D)}
    {k : D} {e : Nat × D}
    (h : (commit E w t posts).journal[k]? = some e) :
    (k = t.txId ∧ e = (w.height + 1, turnDigest E t)) ∨
      (k ≠ t.txId ∧ w.journal[k]? = some e ∧
        ((w.height + 1) % Bounds.windowMax = 0 → kept (w.height + 1) e = true)) := by
  change (pruneJournal (w.height + 1) (w.journal.insert t.txId (w.height + 1, turnDigest E t)))[k]? = some e at h
  rw [pruneJournal_get, Std.TreeMap.getElem?_insert] at h
  by_cases hk : compare t.txId k = .eq
  · rw [if_pos hk] at h
    have hk' := Std.LawfulEqCmp.eq_of_compare hk
    subst hk'
    left
    refine ⟨rfl, ?_⟩
    split at h
    · simp only [Option.filter] at h
      split at h
      · cases h; rfl
      · cases h
    · cases h; rfl
  · rw [if_neg hk] at h
    right
    have hne : k ≠ t.txId := fun he => hk (he ▸ Std.ReflCmp.compare_self)
    refine ⟨hne, ?_⟩
    split at h
    · rename_i hz
      cases hg : w.journal[k]? with
      | none => rw [hg] at h; cases h
      | some e' =>
          rw [hg] at h
          simp only [Option.filter] at h
          split at h
          · rename_i hkp; cases h; exact ⟨rfl, fun _ => hkp⟩
          · cases h
    · rename_i hz
      exact ⟨h, fun h' => absurd h' hz⟩

omit [Std.LawfulEqOrd D] in
theorem admit_new {E : Env D} {w w' : World D} {t : Turn D} (h : World.admit E w t = .ok w') :
    w.journal[t.txId]? = none := (admit_journal h).1

/-- **The invariant holds after every admission.** -/
theorem admit_journalOk {E : Env D} {w w' : World D} {t : Turn D} (hw : w.JournalOk)
    (h : World.admit E w t = .ok w') : w'.JournalOk := by
  obtain ⟨posts, _, rfl⟩ := admit_ok h
  have hh : (commit E w t posts).height = w.height + 1 := rfl
  refine ⟨fun k e he => ?_, fun k₁ k₂ e₁ e₂ h₁ h₂ heq => ?_⟩
  · rw [hh]
    rcases commit_journal_mem he with ⟨_, rfl⟩ | ⟨_, hk, hkept⟩
    · rw [windowMax_eq]; omega
    · have := hw.1 k e hk
      by_cases hz : (w.height + 1) % Bounds.windowMax = 0
      · have := hkept hz
        simp only [kept, decide_eq_true_eq] at this
        rw [windowMax_eq] at *; omega
      · rw [windowMax_eq] at *; omega
  · rcases commit_journal_mem h₁ with ⟨r₁, rfl⟩ | ⟨n₁, hk₁, _⟩ <;>
      rcases commit_journal_mem h₂ with ⟨r₂, rfl⟩ | ⟨n₂, hk₂, _⟩
    · rw [r₁, r₂]
    · have := (hw.1 k₂ e₂ hk₂).1; simp at heq; omega
    · have := (hw.1 k₁ e₁ hk₁).1; simp at heq; omega
    · exact hw.2 k₁ k₂ e₁ e₂ hk₁ hk₂ heq

theorem fold_journalOk {E : Env D} :
    ∀ {w w' : World D} {l : List (Turn D)}, w.JournalOk → World.fold E w l = .ok w' → w'.JournalOk
  | w, w', [], hw, h => by simp [World.fold] at h; subst h; exact hw
  | w, w', t :: rest, hw, h => by
      obtain ⟨w₁, h₁, h₂⟩ := fold_cons_ok.mp h
      exact fold_journalOk (admit_journalOk hw h₁) h₂

omit [DecidableEq D] in
/-- **The journal is bounded by the window** (law 4): fewer than `3 * Bounds.windowMax` entries,
whatever the World's history. -/
theorem journal_bounded {w : World D} (hw : w.JournalOk) : w.journal.size < 3 * Bounds.windowMax := by
  let L := w.journal.toList.map fun p => p.2.1
  have hlen : L.length = w.journal.size := by simp [L, Std.TreeMap.length_toList]
  have hmem : ∀ p ∈ w.journal.toList, w.journal[p.1]? = some p.2 := fun p hp =>
    Std.TreeMap.mem_toList_iff_getElem?_eq_some.mp hp
  have hnd : L.Nodup := by
    apply List.pairwise_map.mpr
    exact Std.TreeMap.distinct_keys_toList.imp_of_mem fun {p q} hp hq hpq heq =>
      hpq (by
        have hpq' := hw.2 p.1 q.1 p.2 q.2 (hmem p hp) (hmem q hq) heq
        rw [hpq']; exact Std.ReflCmp.compare_self)
  have hb : ∀ x ∈ L, x ≤ w.height ∧
      w.height < x + (2 * Bounds.windowMax + w.height % Bounds.windowMax) := by
    intro x hx
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
    have := hw.1 p.1 p.2 (hmem p hp)
    omega
  have := nodup_window_length _ _ L hnd hb
  have hm : w.height % Bounds.windowMax < Bounds.windowMax := Nat.mod_lt _ (by decide)
  omega

/-! ## What the journal still answers -/

/-- **An entry stays while it is kept.** -/
theorem admit_retains {E : Env D} {w w' : World D} {t : Turn D} {k : D} {e : Nat × D}
    (h : World.admit E w t = .ok w') (hk : w.journal[k]? = some e)
    (hlt : w'.height < e.1 + 2 * Bounds.windowMax) : w'.journal[k]? = some e := by
  have hnew := admit_new h
  obtain ⟨posts, _, rfl⟩ := admit_ok h
  have hne : t.txId ≠ k := fun he => by rw [he, hk] at hnew; cases hnew
  have hc : compare t.txId k ≠ .eq := fun he => hne (Std.LawfulEqCmp.eq_of_compare he)
  have hlt' : w.height + 1 < e.1 + 2 * Bounds.windowMax := hlt
  change (pruneJournal (w.height + 1) (w.journal.insert t.txId (w.height + 1, turnDigest E t)))[k]? = some e
  rw [pruneJournal_get, Std.TreeMap.getElem?_insert]
  have hkept : kept (w.height + 1) e = true := by simp [kept, hlt']
  rw [if_neg hc]
  split <;> simp [hk, Option.filter, hkept]

theorem fold_retains {E : Env D} {k : D} {e : Nat × D} :
    ∀ {w w' : World D} {l : List (Turn D)}, World.fold E w l = .ok w' → w.journal[k]? = some e →
      w'.height < e.1 + 2 * Bounds.windowMax → w'.journal[k]? = some e
  | w, w', [], h, hk, _ => by simp [World.fold] at h; subst h; exact hk
  | w, w', t :: rest, h, hk, hlt => by
      obtain ⟨w₁, h₁, h₂⟩ := fold_cons_ok.mp h
      have := fold_height h₂
      exact fold_retains h₂ (admit_retains h₁ hk (by omega)) hlt

/-- **Absence is an answer below `journalForgets`.** A turn admitted from `w₀` is still journaled
in every later World of the log whose height is below its `notBefore + 2 * windowMax`. So an
un-journaled transaction id at a height where `journalForgets` is false was never admitted by
that log (HOST's `expired`); where it is true, absence says nothing (HOST's `forgotten`). -/
theorem fold_answers {E : Env D} {w₀ w₁ w₂ : World D} {t : Turn D} {l : List (Turn D)}
    (h₁ : World.admit E w₀ t = .ok w₁) (hf : World.fold E w₁ l = .ok w₂)
    (hnf : journalForgets w₂.height t.notBefore = false) :
    w₂.journal[t.txId]? = some (w₀.height + 1, turnDigest E t) := by
  have hwin := (admit_window h₁).1
  simp only [journalForgets, decide_eq_false_iff_not, Nat.not_le] at hnf
  exact fold_retains hf (admit_journal h₁).2 (by omega)

/-- **Spacing at bare `admit`.** Two admissions of one transaction id, from `w₀` and later from
`w₂`, are more than `2 * windowMax` heights apart. -/
theorem admit_spacing {E : Env D} {w₀ w₁ w₂ w₃ : World D} {t t' : Turn D} {l : List (Turn D)}
    (h₁ : World.admit E w₀ t = .ok w₁) (hf : World.fold E w₁ l = .ok w₂)
    (h₂ : World.admit E w₂ t' = .ok w₃) (hid : t'.txId = t.txId) :
    w₀.height + 1 + 2 * Bounds.windowMax ≤ w₂.height := by
  apply Nat.le_of_not_lt
  intro hlt
  have := fold_retains hf (admit_journal h₁).2 hlt
  have hnew := admit_new h₂
  rw [hid, this] at hnew
  cases hnew

/-- **One window, one admission.** A transaction id admitted from `w₀` is never admitted again
by a turn with the same window: by then its entry is pruned (`admit_spacing`), so the window has
ended. Every deployed path reaches `World.admit` through `receive`: the writer through
`Receive.submit` (`submit_ok`), the follower through the audit (`audit_ok`: every logged turn is
what `receive` derives from its own event). Two turns derived from one call carry its digest and
its window (`receive_ok`), so on both paths a call is admitted at most once. -/
theorem admit_twice_window {E : Env D} {w₀ w₁ w₂ w₃ : World D} {t t' : Turn D} {l : List (Turn D)}
    (h₁ : World.admit E w₀ t = .ok w₁) (hf : World.fold E w₁ l = .ok w₂)
    (h₂ : World.admit E w₂ t' = .ok w₃) (hid : t'.txId = t.txId) (hv : t'.validUntil = t.validUntil) :
    False := by
  have hsp := admit_spacing h₁ hf h₂ hid
  have hw₁ := admit_window h₁
  have hw₂ := admit_window h₂
  have hb := admit_bounded h₁
  unfold checkBounds at hb
  simp only [except_bind_ok] at hb
  obtain ⟨⟨⟩, _, ⟨⟩, _, ⟨⟩, _, ⟨⟩, _, ⟨⟩, _, ⟨⟩, _, ⟨⟩, _, ⟨⟩, _, ⟨⟩, hwm, _⟩ := hb
  rw [req_ok, decide_eq_true_eq] at hwm
  rw [windowMax_eq] at *
  omega

omit [Std.LawfulEqOrd D] in
/-- **Pruning changes no check.** For a turn whose window ends by its transaction id's entry
height plus `windowMax` (a retry of the call that entry records: same call, same window), the
World with its journal pruned at any `H ≤ w.height` checks it exactly as the World before
pruning: the same refusal, or the same posts. -/
theorem check_prune {E : Env D} {w : World D} {t : Turn D} {H : Nat} (hH : H ≤ w.height)
    (hv : ∀ e, w.journal[t.txId]? = some e → t.validUntil ≤ e.1 + Bounds.windowMax) :
    check E { w with journal := pruneJournal H w.journal } t = check E w t := by
    by_cases hwin : checkWindow w t = .ok ()
    · have hg' : (pruneJournal H w.journal)[t.txId]? = w.journal[t.txId]? := by
        rw [pruneJournal_get]
        cases hg : w.journal[t.txId]? with
        | none => split <;> rfl
        | some e =>
            have hve := hv e hg
            unfold checkWindow at hwin
            rw [req_ok] at hwin
            simp only [Bool.and_eq_true, decide_eq_true_eq] at hwin
            have hkept : kept H e = true := by
              simp only [kept, decide_eq_true_eq]; rw [windowMax_eq] at *; omega
            split <;> simp [Option.filter, hkept]
      have hj : checkJournal { w with journal := pruneJournal H w.journal } t = checkJournal w t := by
        unfold checkJournal
        rw [show ({ w with journal := pruneJournal H w.journal } : World D).journal = pruneJournal H w.journal
          from rfl, hg']
      unfold check
      rw [hj]
      rfl
    · unfold check
      cases hb : checkBounds t with
      | error _ => simp [bind, Except.bind]
      | ok u =>
          cases hw' : checkWindow w t with
          | ok v => exact absurd hw' hwin
          | error e =>
              have : checkWindow { w with journal := pruneJournal H w.journal } t = .error e := hw'
              simp [bind, Except.bind, this]

omit [Std.LawfulEqOrd D] in
/-- **Pruning changes no verdict** (`check_prune`, at the admission). -/
theorem admit_prune_verdict {E : Env D} {w : World D} {t : Turn D} {H : Nat} (hH : H ≤ w.height)
    (hv : ∀ e, w.journal[t.txId]? = some e → t.validUntil ≤ e.1 + Bounds.windowMax) (r : Reject D) :
    World.admit E { w with journal := pruneJournal H w.journal } t = .error r ↔
      World.admit E w t = .error r := by
  unfold World.admit
  rw [check_prune hH hv]
  cases check E w t <;> simp

/-! ## The real fold is the never-pruning fold, filtered at the last prune (KERNEL-38)

`admit_prune_verdict` compares ONE prune against the unpruned journal. The deployed fold
inserts and prunes at every turn. `fold_journal_filter` says what that interleaving leaves: the
never-pruning journal (`shadowJournal`) filtered to the entries `kept` at the last prune height
(`lastPrune`), and `fold_prune_check` turns that into the statement about a real history: the
World a fold reaches checks every windowed retry exactly as the same World with the journal that
was never pruned. -/

/-- `j` is `J` filtered to the entries kept at `H`, read at every transaction id. -/
def JournalFiltered (H : Nat) (j J : Std.TreeMap D (Nat × D) compare) : Prop :=
  ∀ k : D, j[k]? = J[k]?.filter (kept H)

omit [Ord D] [Std.TransOrd D] [Std.LawfulEqOrd D] [DecidableEq D] in
theorem lastPrune_le (h : Nat) : lastPrune h ≤ h := Nat.sub_le _ _

omit [Ord D] [Std.TransOrd D] [Std.LawfulEqOrd D] [DecidableEq D] in
theorem lastPrune_mod (h : Nat) : lastPrune h % Bounds.windowMax = 0 := by
  unfold lastPrune; rw [windowMax_eq]; omega

omit [Ord D] [Std.TransOrd D] [Std.LawfulEqOrd D] [DecidableEq D] in
theorem lastPrune_succ (h : Nat) :
    lastPrune (h + 1) = if (h + 1) % Bounds.windowMax = 0 then h + 1 else lastPrune h := by
  unfold lastPrune; rw [windowMax_eq]; split <;> omega

omit [Ord D] [Std.TransOrd D] [Std.LawfulEqOrd D] [DecidableEq D] in
theorem kept_anti {H H' : Nat} {e : Nat × D} (hH : H ≤ H') (h : kept H' e = true) : kept H e = true := by
  simp only [kept, decide_eq_true_eq] at *; omega

omit [Ord D] [Std.TransOrd D] [Std.LawfulEqOrd D] [DecidableEq D] in
theorem filter_kept_anti {H H' : Nat} (hH : H ≤ H') (o : Option (Nat × D)) :
    (o.filter (kept H)).filter (kept H') = o.filter (kept H') := by
  cases o with
  | none => rfl
  | some e =>
      by_cases h' : kept H' e = true
      · simp [Option.filter, kept_anti hH h', h']
      · by_cases h : kept H e = true <;> simp [Option.filter, h, h']

omit [Std.TransOrd D] [Std.LawfulEqOrd D] [DecidableEq D] in
/-- Every World that holds `JournalOk` is its own journal filtered at its last prune height. -/
theorem journalFiltered_self {w : World D} (hw : w.JournalOk) :
    JournalFiltered (lastPrune w.height) w.journal w.journal := by
  unfold JournalFiltered
  intro k
  cases hg : w.journal[k]? with
  | none => rfl
  | some e =>
      have := (hw.1 k e hg).2
      simp only [Option.filter, kept, lastPrune, decide_eq_true_eq]
      rw [windowMax_eq] at *
      split
      · rfl
      · omega

omit [Std.LawfulEqOrd D] in
/-- One commit: the pruned insert is the never-pruned insert filtered at the new last prune. -/
theorem commit_filtered {E : Env D} {w : World D} {t : Turn D} {posts : List (Post D)}
    {J : Std.TreeMap D (Nat × D) compare} (hj : JournalFiltered (lastPrune w.height) w.journal J) :
    JournalFiltered (lastPrune (w.height + 1)) (commit E w t posts).journal
      (J.insert t.txId (w.height + 1, turnDigest E t)) := by
  unfold JournalFiltered at *
  intro k
  change (pruneJournal (w.height + 1) (w.journal.insert t.txId (w.height + 1, turnDigest E t)))[k]? = _
  rw [pruneJournal_get, Std.TreeMap.getElem?_insert, Std.TreeMap.getElem?_insert, lastPrune_succ]
  by_cases hz : (w.height + 1) % Bounds.windowMax = 0
  · rw [if_pos hz, if_pos hz]
    by_cases hc : compare t.txId k = .eq
    · rw [if_pos hc, if_pos hc]
    · rw [if_neg hc, if_neg hc, hj k, filter_kept_anti (Nat.le_succ_of_le (lastPrune_le _))]
  · rw [if_neg hz, if_neg hz]
    by_cases hc : compare t.txId k = .eq
    · rw [if_pos hc, if_pos hc]
      have := lastPrune_le w.height
      simp only [Option.filter, kept, decide_eq_true_eq]
      split
      · rfl
      · omega
    · rw [if_neg hc, if_neg hc, hj k]

omit [Std.LawfulEqOrd D] in
/-- **The real fold's journal is the never-pruning journal, filtered at the last prune height.**
From any World whose journal is `J` filtered at its last prune (`journalFiltered_self`: every
`JournalOk` World, with `J` its own journal), the World a fold reaches, which inserted and pruned
at every turn, holds exactly the entries of `shadowJournal` that are `kept` at its own
`lastPrune` height. All the prunes of a history are one prune at the last multiple of
`windowMax`, of the journal that never forgot. -/
theorem fold_journal_filter {E : Env D} {l : List (Turn D)} :
    ∀ {w w' : World D} {J : Std.TreeMap D (Nat × D) compare},
      JournalFiltered (lastPrune w.height) w.journal J → World.fold E w l = .ok w' →
      JournalFiltered (lastPrune w'.height) w'.journal (shadowJournal E w.height J l) := by
  induction l with
  | nil => intro w w' J hj h; simp [World.fold] at h; subst h; exact hj
  | cons t rest ih =>
      intro w w' J hj h
      obtain ⟨w₁, h₁, h₂⟩ := fold_cons_ok.mp h
      obtain ⟨posts, _, rfl⟩ := admit_ok h₁
      exact ih (commit_filtered hj) h₂

omit [Std.TransOrd D] [Std.LawfulEqOrd D] in
/-- `check` reads the journal only at the turn's transaction id. -/
theorem check_journal_congr {E : Env D} {w : World D} {t : Turn D} {j : Std.TreeMap D (Nat × D) compare}
    (hj : j[t.txId]? = w.journal[t.txId]?) : check E { w with journal := j } t = check E w t := by
  have h : checkJournal { w with journal := j } t = checkJournal w t := by
    unfold checkJournal
    rw [show ({ w with journal := j } : World D).journal = j from rfl, hj]
  unfold check
  rw [h]
  rfl

omit [Std.LawfulEqOrd D] in
/-- **Pruning changed no check in a real history.** The World `w'` a fold reaches checks a
turn exactly as the same World with the journal that was never pruned, whenever the turn's
window ends by its transaction id's never-pruned entry height plus `windowMax` (a retry of the
call that entry records). This is `check_prune` at `lastPrune w'.height`, transported to the real
journal by `fold_journal_filter`. -/
theorem fold_prune_check {E : Env D} {w w' : World D} {l : List (Turn D)}
    {J : Std.TreeMap D (Nat × D) compare} {t : Turn D}
    (hj : JournalFiltered (lastPrune w.height) w.journal J) (h : World.fold E w l = .ok w')
    (hv : ∀ e, (shadowJournal E w.height J l)[t.txId]? = some e →
      t.validUntil ≤ e.1 + Bounds.windowMax) :
    check E w' t = check E { w' with journal := shadowJournal E w.height J l } t := by
  have hp : (pruneJournal (lastPrune w'.height) (shadowJournal E w.height J l))[t.txId]? =
      w'.journal[t.txId]? := by
    have hf := fold_journal_filter hj h
    unfold JournalFiltered at hf
    rw [pruneJournal_get, if_pos (lastPrune_mod _), hf t.txId]
  rw [← check_journal_congr hp]
  exact check_prune (w := { w' with journal := shadowJournal E w.height J l }) (lastPrune_le _) hv

end Nanodregg.Kernel

namespace Nanodregg.Kernel.Receive

open Nanodregg.Kernel

variable {D : Type} [Ord D] [Std.TransOrd D] [Std.LawfulEqOrd D] [DecidableEq D]

/-- **A call is admitted at most once, ever** (KERNEL-33). After `submit` admitted call `c`, no
World any later log reaches admits `c` again: while its entry is journaled `submit` answers
`replayed`, and by the time it is pruned (`admit_spacing`) the call's own window, fixed by the
call, has ended. No premise and no collision disjunct: one call has one digest and one window. -/
theorem submit_once {X : Ctx D} {w₀ w₁ w₂ : World D} {c : Call D} {t : Turn D} {l : List (Turn D)}
    (h₁ : submit X w₀ c = .ok (t, w₁)) (hf : World.fold X.env w₁ l = .ok w₂) :
    ∀ r, submit X w₂ c ≠ .ok r := by
  intro ⟨t₂, w₃⟩ h₂
  obtain ⟨_, hr₁, ha₁⟩ := submit_ok h₁
  obtain ⟨_, hr₂, ha₂⟩ := submit_ok h₂
  obtain ⟨_, _, _, _, _, hid₁, _, hvu₁⟩ := receive_ok hr₁
  obtain ⟨_, _, _, _, _, hid₂, _, hvu₂⟩ := receive_ok hr₂
  exact admit_twice_window ha₁ hf ha₂ (by rw [hid₁, hid₂]) (by rw [hvu₁, hvu₂])

/-- **One call, one admission, on any path through `receive`.** If call `c` derived the turn
admitted from `w₀`, no later World of that log admits a turn `c` derives again. This is the
follower's form: in an `Honest` log (`audit_ok`) every turn is `receive` of its own event's call
on the World before it, so an audited log never holds one call twice. -/
theorem derived_once {X : Ctx D} {w₀ w₁ w₂ w₃ : World D} {c : Call D} {t t' : Turn D} {l : List (Turn D)}
    (hr₁ : receive X w₀ c = .ok t) (h₁ : World.admit X.env w₀ t = .ok w₁)
    (hf : World.fold X.env w₁ l = .ok w₂)
    (hr₂ : receive X w₂ c = .ok t') (h₂ : World.admit X.env w₂ t' = .ok w₃) : False := by
  obtain ⟨_, _, _, _, _, hid₁, _, hvu₁⟩ := receive_ok hr₁
  obtain ⟨_, _, _, _, _, hid₂, _, hvu₂⟩ := receive_ok hr₂
  exact admit_twice_window h₁ hf h₂ (by rw [hid₁, hid₂]) (by rw [hvu₁, hvu₂])

omit [Std.TransOrd D] [Std.LawfulEqOrd D] in
/-- **Past `journalForgets` the kernel refuses a call by its window**: its turn's window ends by
`notBefore + windowMax` (`checkBounds`), more than `windowMax` heights ago. So HOST answers such
a submit `uncertain forgotten`, which is what it is for a call committed long ago (its entry
pruned), never a false `refused`. -/
theorem submit_forgotten {X : Ctx D} {w : World D} {c : Call D}
    (hfg : journalForgets w.height c.unsigned.notBefore = true) : ∀ r, submit X w c ≠ .ok r := by
  intro ⟨t, w'⟩ h
  obtain ⟨_, hr, ha⟩ := submit_ok h
  obtain ⟨_, _, _, _, _, _, hnb, hvu⟩ := receive_ok hr
  have hw := admit_window ha
  have hb := admit_bounded ha
  unfold checkBounds at hb
  simp only [except_bind_ok] at hb
  obtain ⟨⟨⟩, _, ⟨⟩, _, ⟨⟩, _, ⟨⟩, _, ⟨⟩, _, ⟨⟩, _, ⟨⟩, _, ⟨⟩, _, ⟨⟩, hwm, _⟩ := hb
  rw [req_ok, decide_eq_true_eq] at hwm
  simp only [journalForgets, decide_eq_true_eq] at hfg
  rw [windowMax_eq] at *
  omega

omit [Std.LawfulEqOrd D] in
theorem genesisWorld_journalOk (X : Ctx D) (name nonce : ByteArray) (allowance : Nat)
    (founders : List (ByteArray × D)) : (genesisWorld X name nonce allowance founders).JournalOk :=
  journalOk_of_empty fun _ => Std.TreeMap.getElem?_emptyc

/-- **Every World a genesis reaches holds fewer than `3 * windowMax` journal entries**, whatever
its history: no premise (law 4 at the World's journal). -/
theorem reach_journal_bounded {X : Ctx D} {name nonce : ByteArray} {allowance : Nat}
    {founders : List (ByteArray × D)} {w : World D} {l : List (Turn D)}
    (h : World.fold X.env (genesisWorld X name nonce allowance founders) l = .ok w) :
    w.journal.size < 3 * Bounds.windowMax :=
  journal_bounded (fold_journalOk (genesisWorld_journalOk X name nonce allowance founders) h)

omit [Std.LawfulEqOrd D] in
/-- **From genesis, pruning changed no check** (`fold_prune_check`, every premise but the
window discharged): a World a genesis reaches checks each windowed retry exactly as the same
World carrying the latest entry its log wrote under each transaction id, none pruned. -/
theorem reach_prune_check {X : Ctx D} {name nonce : ByteArray} {allowance : Nat}
    {founders : List (ByteArray × D)} {w : World D} {l : List (Turn D)} {t : Turn D}
    (h : World.fold X.env (genesisWorld X name nonce allowance founders) l = .ok w)
    (hv : ∀ e, (shadowJournal X.env (genesisWorld X name nonce allowance founders).height
        (genesisWorld X name nonce allowance founders).journal l)[t.txId]? = some e →
      t.validUntil ≤ e.1 + Bounds.windowMax) :
    check X.env w t = check X.env { w with journal := (shadowJournal X.env
      (genesisWorld X name nonce allowance founders).height
      (genesisWorld X name nonce allowance founders).journal l) } t :=
  fold_prune_check (journalFiltered_self (genesisWorld_journalOk X name nonce allowance founders)) h hv
