/-
# Protocol.Proofs.Receipt — a receipt that checks against a World's roots tells the truth

`check_committed`: a receipt that checks `committed h td` against a World's height and roots shows
the World's journal holds `(h, td)` at the id, or the hash collides. `check_absent`: one that checks
`absent` shows the id absent from the journal, or a collision, and is never answered past
`journalForgets`. With KERNEL's `head_roots` (a head link that hashes to a stepped World's chain opens
to that World's roots) these are the phone read of KERNEL-41 (`head_journal_read`) through the
roots a member holds. The refused answer's soundness about the World needs the refusals trie's
inclusion soundness, which KERNEL has not stated (cv); `check_refused` states what the check does
establish: the path verifies against the head's refusals root.
-/
import Protocol.Receipt
import Kernel.Proofs.JournalHead
import Kernel.Proofs.Refusals

namespace Nanodregg.Protocol.Receipt

open Nanodregg.Kernel

variable {D : Type} [Ord D] [DecidableEq D]

omit [Ord D] in
theorem check_ok {E : Env D} {H : Nat} {roots txId : D} {nb : Nat} {r : Receipt D} {a : Answer D}
    (h : check E H roots txId nb r = .ok a) :
    r.txId = txId ∧ rootsDigest E r.root r.jroot r.rroot r.rowsroot = roots ∧ answerOf E H txId nb r = .ok a := by
  unfold check at h
  split at h
  · cases h
  · split at h
    · cases h
    · rename_i h1 h2
      exact ⟨Classical.not_not.mp h1, Classical.not_not.mp h2, h⟩

section Sound
variable {E : Env D} {n : Nat} (hE : E.Lawful n) (hn : 0 < n)

include hE hn in
/-- **A committed receipt is the World's journal entry.** -/
theorem check_committed {w : World D} (hc : w.JournalCanon E)
    (hfit : ∀ k e, w.journalAt E k = some e → e.1 < 2 ^ 64)
    {H : Nat} {txId : D} {nb : Nat} {r : Receipt D} {h : Nat} {td : D}
    (hk : check E H (w.roots E) txId nb r = .ok (.committed h td)) :
    w.journalAt E txId = some (h, td) ∨ Collision E.hash := by
  obtain ⟨-, hr, ha⟩ := check_ok hk
  rcases rootsDigest_inj hE hr with ⟨-, hj, -, -⟩ | col
  · unfold answerOf at ha
    split at ha
    · split at ha
      · rename_i hv
        cases ha
        rw [hj] at hv
        exact journal_inclusion_sound hE hn hc hfit hv.1 hv.2
      · cases ha
    · split at ha <;> cases ha
    · split at ha
      · cases ha
      · split at ha <;> cases ha
  · exact .inr col

include hE hn in
/-- **An absent receipt is the World's journal absence**, and only while `journalForgets` is false. -/
theorem check_absent {w : World D} (hc : w.JournalCanon E)
    {txId : D} {nb : Nat} {r : Receipt D}
    (hk : check E w.height (w.roots E) txId nb r = .ok .absent) :
    journalForgets w.height nb = false ∧ (w.journalAt E txId = none ∨ Collision E.hash) := by
  obtain ⟨-, hr, ha⟩ := check_ok hk
  unfold answerOf at ha
  split at ha
  · split at ha <;> cases ha
  · split at ha <;> cases ha
  · split at ha
    · cases ha
    · rename_i hf
      split at ha
      · rename_i hv
        refine ⟨by simpa using hf, ?_⟩
        rcases rootsDigest_inj hE hr with ⟨-, hj, -, -⟩ | col
        · rw [hj] at hv
          exact journal_exclusion_sound hE hn hc hv.1
        · exact .inr col
      · cases ha

include hE hn in
/-- **A refused receipt is not a committed call**: the id is absent from the World's journal, or a
collision (a relay cannot turn a committed call into `refused`). -/
theorem check_refused_uncommitted {w : World D} (hc : w.JournalCanon E)
    {H : Nat} {txId : D} {nb : Nat} {r : Receipt D} {h code : Nat}
    (hk : check E H (w.roots E) txId nb r = .ok (.refused h code)) :
    w.journalAt E txId = none ∨ Collision E.hash := by
  obtain ⟨-, hr, ha⟩ := check_ok hk
  unfold answerOf at ha
  split at ha
  · split at ha <;> cases ha
  · split at ha
    · rename_i hv
      rcases rootsDigest_inj hE hr with ⟨-, hj, -, -⟩ | col
      · have hx := hv.2
        rw [hj] at hx
        exact journal_exclusion_sound hE hn hc hx
      · exact .inr col
    · cases ha
  · split at ha
    · cases ha
    · split at ha <;> cases ha

end Sound

omit [Ord D] in
/-- **A refused receipt's path verifies against the head's refusals root** for the recorded
refusal it states, the head's roots opening to that root. -/
theorem check_refused {E : Env D} {H : Nat} {roots txId : D} {nb : Nat} {r : Receipt D} {h code : Nat}
    (hk : check E H roots txId nb r = .ok (.refused h code)) :
    rootsDigest E r.root r.jroot r.rroot r.rowsroot = roots ∧
      Trie.verifyInclusion (refusalSpec E) r.rroot (.tx txId) (refusalDigest E (.refused h code)) r.rpath = true := by
  obtain ⟨-, hr, ha⟩ := check_ok hk
  refine ⟨hr, ?_⟩
  unfold answerOf at ha
  split at ha
  · split at ha <;> cases ha
  · split at ha
    · rename_i hv; cases ha; exact hv.1
    · cases ha
  · split at ha
    · cases ha
    · split at ha <;> cases ha

/-! ## Completeness: the member's own receipt checks (PROTOCOL-46) -/

/-- **A World proves every refusals leaf it holds** (the refusals twin of
`Kernel.journal_prove_verifies`). -/
theorem refusals_prove_verifies {E : Env D} {w : World D} (hc : w.RefusalsCanon E) {k : RefusalSlot D}
    {l : RefusalLeaf} (hg : w.refusalAt E k = some l) :
    Trie.verifyInclusion (refusalSpec E) (w.refusalsRoot E) k (refusalDigest E l)
      (w.refusals.prove (refusalSpec E) k) = true :=
  Trie.prove_includes (refusalSpec E) hc.2.1 (Trie.shallow_of_shape _ 0 _ hc.2.2) hg

/-- **A World proves every refusals key it does not hold** (the twin of
`Kernel.journal_prove_absent`). -/
theorem refusals_prove_absent {E : Env D} {w : World D} (hc : w.RefusalsCanon E) {k : RefusalSlot D}
    (hg : w.refusalAt E k = none) :
    Trie.verifyExclusion (refusalSpec E) (w.refusalsRoot E) k (w.refusals.prove (refusalSpec E) k) = true :=
  Trie.prove_excludes (refusalSpec E) hc.2.1 (Trie.shallow_of_shape _ 0 _ hc.2.2) hg

/-- **The receipt a World builds checks against that World's own head**, answering what it states,
unless the answer is `absent` past `journalForgets` (where `check` refuses `forgotten`:
`check_build_forgotten`). So follow, settling from `build`, settles exactly what `check` would
accept; on a JournalCanon World whose journal heights fit a u64 and whose refusals are well formed
(both hold of every World a checked genesis and a fold reach: `deployed_reach_journalOk`,
`deployed_reach_refusalsOk`). -/
theorem check_build {E : Env D} {w : World D} {tx : D} {nb : Nat} (hc : w.JournalCanon E)
    (hr : w.RefusalsOk E) (hfit : ∀ k e, w.journalAt E k = some e → e.1 < 2 ^ 64)
    (hnf : (build E w tx).answer ≠ .absent ∨ journalForgets w.height nb = false) :
    check E w.height (w.roots E) tx nb (build E w tx) = .ok (build E w tx).answer := by
  have hroots : rootsDigest E (build E w tx).root (build E w tx).jroot (build E w tx).rroot
      (build E w tx).rowsroot = w.roots E := rfl
  unfold check
  rw [if_neg (by simp [build]), if_neg (by rw [hroots]; simp)]
  unfold answerOf
  cases hjx : w.journalAt E tx with
  | some e =>
      obtain ⟨h, td⟩ := e
      have ha : (build E w tx).answer = .committed h td := by simp [build, hjx]
      rw [ha]
      simp only
      rw [if_pos ⟨hfit _ _ hjx, journal_prove_verifies hc hjx⟩]
  | none =>
      cases hrx : w.refusalAt E (.tx tx) with
      | some l =>
          cases l with
          | refused h code =>
              have ha : (build E w tx).answer = .refused h code := by simp [build, hjx, hrx]
              rw [ha]
              simp only
              rw [if_pos ⟨refusals_prove_verifies hr.1 hrx, journal_prove_absent hc hjx⟩]
          | count n =>
              have := hr.2 _ _ hrx
              simp [refusalFits] at this
      | none =>
          have ha : (build E w tx).answer = .absent := by simp [build, hjx, hrx]
          rw [ha]
          simp only
          have hf : journalForgets w.height nb = false := by
            rcases hnf with h | h
            · exact absurd ha h
            · exact h
          rw [if_neg (by simp [hf]), if_pos ⟨journal_prove_absent hc hjx, refusals_prove_absent hr.1 hrx⟩]

/-- `check_build`'s premise is exact: the built `absent` past `journalForgets` is refused
`forgotten`, never an answer. -/
theorem check_build_forgotten {E : Env D} {w : World D} {tx : D} {nb : Nat}
    (ha : (build E w tx).answer = .absent) (hf : journalForgets w.height nb = true) :
    check E w.height (w.roots E) tx nb (build E w tx) = .error .forgotten := by
  have hroots : rootsDigest E (build E w tx).root (build E w tx).jroot (build E w tx).rroot
      (build E w tx).rowsroot = w.roots E := rfl
  unfold check
  rw [if_neg (by simp [build]), if_neg (by rw [hroots]; simp)]
  unfold answerOf
  rw [ha]
  simp [hf]

end Nanodregg.Protocol.Receipt
