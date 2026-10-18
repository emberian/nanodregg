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

end Nanodregg.Protocol.Receipt
