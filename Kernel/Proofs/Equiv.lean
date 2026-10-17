/-
# Kernel.Proofs.Equiv — a reopened World decides exactly like the live one

A `Std.TreeMap`'s shape depends on its insertion history, so a World whose journal was rebuilt
from a checkpoint is not `=` to the live one that grew turn by turn (its trie IS: KERNEL-23). What
must hold — and what minidregg's live/reopened divergence violated — is that `World.admit`
cannot tell them apart: extensionally equal Worlds accept the same turns, refuse the same turns
by the same name, and stay extensionally equal.
-/
import Kernel.Proofs.Frame

namespace Nanodregg.Kernel

variable {D : Type} [Ord D] [Std.TransOrd D] [Std.LawfulEqOrd D] [DecidableEq D]

/-- Equality of Worlds up to the journal's tree shape. The trie is history-independent
(`Trie.build_toList`, `Trie.eq_of_get_eq`), so its component is `=`: a World rebuilt from a
checkpoint holds the SAME trie as the live one. The journal is a `Std.TreeMap`, whose shape depends
on its insertion history, so it is compared extensionally. -/
def World.Equiv (a b : World D) : Prop :=
  a.trie = b.trie ∧ a.journal.Equiv b.journal ∧
    a.height = b.height ∧ a.chain = b.chain ∧ a.allowance = b.allowance ∧ a.origin = b.origin

omit [Std.TransOrd D] [Std.LawfulEqOrd D] in
theorem live_congr {E : Env D} {a b : World D} (h : a.Equiv b) (c : D) : a.live E c = b.live E c := by
  unfold World.live World.entry; rw [h.1]

omit [Std.TransOrd D] [Std.LawfulEqOrd D] [DecidableEq D] in
theorem root_congr {E : Env D} {a b : World D} (h : a.Equiv b) : a.root E = b.root E := by
  unfold World.root; rw [h.1]

omit [Std.LawfulEqOrd D] in
theorem check_congr {E : Env D} {a b : World D} (h : a.Equiv b) (t : Turn D) :
    check E a t = check E b t := by
  obtain ⟨hc, hj, hh, _, hal, ho⟩ := h
  have hl : ∀ c, a.live E c = b.live E c := live_congr ⟨hc, hj, hh, ‹_›, hal, ho⟩
  have e1 : checkJournal a t = checkJournal b t := by unfold checkJournal; rw [hj.getElem?_eq]
  have e2 : checkWindow a t = checkWindow b t := by unfold checkWindow; rw [hh]
  have e3 : touchCheck E a = touchCheck E b := by funext x; unfold touchCheck; rw [hl]
  have e4 : checkNullifiers E a t = checkNullifiers E b t := by
    unfold checkNullifiers World.isSpent; rw [hc]
  have e5 : checkCharge a t = checkCharge b t := by unfold checkCharge; rw [hal]
  have e6 : checkCreates E a t = checkCreates E b t := by
    unfold checkCreates World.taken World.entry; rw [hc]
  unfold check; rw [e1, e2, e3, e4, e5, e6]

omit [Std.LawfulEqOrd D] in
theorem commit_congr {E : Env D} {a b : World D} (h : a.Equiv b) (t : Turn D)
    (posts : List (Post D)) : (commit E a t posts).Equiv (commit E b t posts) := by
  obtain ⟨hc, hj, hh, hch, hal, ho⟩ := h
  have ht : commitTrie E a t posts = commitTrie E b t posts := by unfold commitTrie; rw [hc]
  refine ⟨ht, ?_, by simp [commit, hh], by simp [commit, hch, ht], by simp [commit, hal],
    by simp [commit, ho]⟩
  show (a.journal.insert t.txId (a.height + 1, turnDigest E t)).Equiv
    (b.journal.insert t.txId (b.height + 1, turnDigest E t))
  rw [hh]; exact hj.insert _ _

omit [Std.LawfulEqOrd D] in
/-- **Reopen determinism, refusals.** Extensionally equal Worlds refuse a turn by the same name. -/
theorem admit_congr_error {E : Env D} {a b : World D} (h : a.Equiv b) (t : Turn D) (r : Reject D) :
    World.admit E a t = .error r ↔ World.admit E b t = .error r := by
  unfold World.admit; rw [check_congr h]
  cases check E b t <;> simp

omit [Std.LawfulEqOrd D] in
/-- **Reopen determinism, admissions.** Extensionally equal Worlds admit the same turns and stay
extensionally equal. -/
theorem admit_congr_ok {E : Env D} {a b a' : World D} (h : a.Equiv b) {t : Turn D}
    (ha : World.admit E a t = .ok a') : ∃ b', World.admit E b t = .ok b' ∧ a'.Equiv b' := by
  unfold World.admit at ha ⊢
  rw [← check_congr h]
  cases hc : check E a t with
  | error r => simp [hc] at ha
  | ok posts =>
      simp only [hc, Except.ok.injEq] at ha ⊢
      subst ha
      exact ⟨_, rfl, commit_congr h t posts⟩

omit [Std.LawfulEqOrd D] in
/-- **Reopen determinism over a log.** A reopened World folds a suffix exactly as the live one. -/
theorem fold_congr {E : Env D} :
    ∀ {a b a' : World D} {l : List (Turn D)}, a.Equiv b → World.fold E a l = .ok a' →
      ∃ b', World.fold E b l = .ok b' ∧ a'.Equiv b'
  | a, b, a', [], h, ha => by simp [World.fold] at ha; subst ha; exact ⟨b, rfl, h⟩
  | a, b, a', t :: rest, h, ha => by
      obtain ⟨a₁, h₁, h₂⟩ := fold_cons_ok.mp ha
      obtain ⟨b₁, hb₁, he⟩ := admit_congr_ok h h₁
      obtain ⟨b', hb', he'⟩ := fold_congr he h₂
      exact ⟨b', fold_cons_ok.mpr ⟨b₁, hb₁, hb'⟩, he'⟩

end Nanodregg.Kernel
