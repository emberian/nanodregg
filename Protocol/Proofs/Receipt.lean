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
import Kernel.Proofs.RefusalsHead
import Kernel.Proofs.Journal
import Kernel.Receive.Follow

namespace Nanodregg.Protocol.Receipt

open Nanodregg.Kernel Nanodregg.Kernel.Receive

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
    w.journalAt E txId = some (h, td) ∨
      CollidesAmong E.hash ([rootsPre E r.root r.jroot r.rroot r.rowsroot, w.rootsPre E] ++
        inclPres (journalSpec E) (journalPre E) txId (h, td) r.jpath w.journal) := by
  obtain ⟨-, hr, ha⟩ := check_ok hk
  rcases rootsDigest_inj hE hr with ⟨-, hj, -, -⟩ | col
  · unfold answerOf at ha
    split at ha
    · split at ha
      · rename_i hv
        cases ha
        rw [hj] at hv
        exact (journal_inclusion_sound hE hn hc hfit hv.1 hv.2).imp_right
          (CollidesAmong.mono fun x hx => List.mem_append_right _ hx)
      · cases ha
    · split at ha <;> cases ha
    · split at ha
      · cases ha
      · split at ha <;> cases ha
  · exact .inr (CollidesAmong.mono (fun x hx => List.mem_append_left _ hx) col)

include hE hn in
/-- **An absent receipt is the World's journal absence**, and only while `journalForgets` is false. -/
theorem check_absent {w : World D} (hc : w.JournalCanon E)
    {txId : D} {nb : Nat} {r : Receipt D}
    (hk : check E w.height (w.roots E) txId nb r = .ok .absent) :
    journalForgets w.height nb = false ∧ (w.journalAt E txId = none ∨
      CollidesAmong E.hash ([rootsPre E r.root r.jroot r.rroot r.rowsroot, w.rootsPre E] ++
        readPres (journalSpec E) txId r.jpath w.journal)) := by
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
          exact (journal_exclusion_sound hE hn hc hv.1).imp_right
            (CollidesAmong.mono fun x hx => List.mem_append_right _ hx)
        · exact .inr (CollidesAmong.mono (fun x hx => List.mem_append_left _ hx) col)
      · cases ha

include hE hn in
/-- **A refused receipt is not a committed call**: the id is absent from the World's journal, or a
collision (a relay cannot turn a committed call into `refused`). -/
theorem check_refused_uncommitted {w : World D} (hc : w.JournalCanon E)
    {H : Nat} {txId : D} {nb : Nat} {r : Receipt D} {h code : Nat} {m : D}
    (hk : check E H (w.roots E) txId nb r = .ok (.refused h code m)) :
    w.journalAt E txId = none ∨
      CollidesAmong E.hash ([rootsPre E r.root r.jroot r.rroot r.rowsroot, w.rootsPre E] ++
        readPres (journalSpec E) txId r.jpath w.journal) := by
  obtain ⟨-, hr, ha⟩ := check_ok hk
  unfold answerOf at ha
  split at ha
  · split at ha <;> cases ha
  · split at ha
    · rename_i hv
      rcases rootsDigest_inj hE hr with ⟨-, hj, -, -⟩ | col
      · have hx := hv.2.2.2
        rw [hj] at hx
        exact (journal_exclusion_sound hE hn hc hx).imp_right
          (CollidesAmong.mono fun x hx => List.mem_append_right _ hx)
      · exact .inr (CollidesAmong.mono (fun x hx => List.mem_append_left _ hx) col)
    · cases ha
  · split at ha
    · cases ha
    · split at ha <;> cases ha

/-- Every refusals leaf of a RefusalsOk World fits its wire form (what KERNEL's soundness asks). -/
theorem refusalsOk_fits {w : World D} (hr : w.RefusalsOk E) :
    ∀ k v, w.refusalAt E k = some v → Codec.Kernel.RefusalLeaf.Fits v := by
  intro k v hk
  have hf := hr.2 k v hk
  cases k <;> cases v <;> simp only [refusalFits, Bounds.counterLimit, Bounds.refusalsPerWindow, decide_eq_true_eq] at hf <;>
    simp only [Codec.Kernel.RefusalLeaf.Fits] <;> (try cases hf) <;> omega

include hE in
/-- **A refused receipt is the World's recorded refusal**, its height, code and charged member, or a collision
(KERNEL's `refusal_inclusion_sound`): a relay cannot change what was recorded. -/
theorem check_refused_sound {w : World D} (hr : w.RefusalsOk E)
    {H : Nat} {txId : D} {nb : Nat} {r : Receipt D} {h code : Nat} {m : D}
    (hk : check E H (w.roots E) txId nb r = .ok (.refused h code m)) :
    w.refusalAt E (.tx txId) = some (.refused h code m) ∨
      CollidesAmong E.hash ([rootsPre E r.root r.jroot r.rroot r.rowsroot, w.rootsPre E] ++
        inclPres (refusalSpec E) (refusalPre E) (.tx txId) (.refused h code m) r.rpath w.refusals) := by
  obtain ⟨-, hrd, ha⟩ := check_ok hk
  unfold answerOf at ha
  split at ha
  · split at ha <;> cases ha
  · split at ha
    · rename_i hv
      cases ha
      rcases rootsDigest_inj hE hrd with ⟨-, -, hrr, -⟩ | col
      · have hx := hv.2.2.1
        rw [hrr] at hx
        exact (refusal_inclusion_sound hE hr.1 (refusalsOk_fits hr) (v := .refused h code m) ⟨hv.1, hv.2.1⟩
          hx).imp_right
          (CollidesAmong.mono fun x hx => List.mem_append_right _ hx)
      · exact .inr (CollidesAmong.mono (fun x hx => List.mem_append_left _ hx) col)
    · cases ha
  · split at ha
    · cases ha
    · split at ha <;> cases ha

include hE in
/-- **An absent receipt shows no refusal recorded either**, or a collision. -/
theorem check_absent_unrefused {w : World D} (hr : w.RefusalsOk E)
    {H : Nat} {txId : D} {nb : Nat} {r : Receipt D}
    (hk : check E H (w.roots E) txId nb r = .ok .absent) :
    w.refusalAt E (.tx txId) = none ∨
      CollidesAmong E.hash ([rootsPre E r.root r.jroot r.rroot r.rowsroot, w.rootsPre E] ++
        readPres (refusalSpec E) (.tx txId) r.rpath w.refusals) := by
  obtain ⟨-, hrd, ha⟩ := check_ok hk
  unfold answerOf at ha
  split at ha
  · split at ha <;> cases ha
  · split at ha <;> cases ha
  · split at ha
    · cases ha
    · split at ha
      · rename_i hv
        rcases rootsDigest_inj hE hrd with ⟨-, -, hrr, -⟩ | col
        · have hx := hv.2
          rw [hrr] at hx
          exact (refusal_exclusion_sound hE hr.1 hx).imp_right
            (CollidesAmong.mono fun x hx => List.mem_append_right _ hx)
        · exact .inr (CollidesAmong.mono (fun x hx => List.mem_append_left _ hx) col)
      · cases ha

include hE hn in
/-- TOOTH (`check_committed`): where the hash separates the inputs it compares, a committed receipt
is the World's journal entry. -/
theorem check_committed_sep {w : World D} (hc : w.JournalCanon E)
    (hfit : ∀ k e, w.journalAt E k = some e → e.1 < 2 ^ 64)
    {H : Nat} {txId : D} {nb : Nat} {r : Receipt D} {h : Nat} {td : D}
    (hk : check E H (w.roots E) txId nb r = .ok (.committed h td))
    (hs : Separates E.hash ([rootsPre E r.root r.jroot r.rroot r.rowsroot, w.rootsPre E] ++
      inclPres (journalSpec E) (journalPre E) txId (h, td) r.jpath w.journal)) :
    w.journalAt E txId = some (h, td) :=
  (check_committed hE hn hc hfit hk).resolve_right hs.not_collides

include hE hn in
/-- TOOTH (`check_absent`): where the hash separates the inputs it compares, an absent receipt is
the World's journal absence, while `journalForgets` is false. -/
theorem check_absent_sep {w : World D} (hc : w.JournalCanon E)
    {txId : D} {nb : Nat} {r : Receipt D}
    (hk : check E w.height (w.roots E) txId nb r = .ok .absent)
    (hs : Separates E.hash ([rootsPre E r.root r.jroot r.rroot r.rowsroot, w.rootsPre E] ++
      readPres (journalSpec E) txId r.jpath w.journal)) :
    journalForgets w.height nb = false ∧ w.journalAt E txId = none :=
  have h := check_absent hE hn hc hk
  ⟨h.1, h.2.resolve_right hs.not_collides⟩

include hE hn in
/-- TOOTH (`check_refused_uncommitted`): where the hash separates the inputs it compares, a refused
receipt's id is absent from the World's journal. -/
theorem check_refused_uncommitted_sep {w : World D} (hc : w.JournalCanon E)
    {H : Nat} {txId : D} {nb : Nat} {r : Receipt D} {h code : Nat} {m : D}
    (hk : check E H (w.roots E) txId nb r = .ok (.refused h code m))
    (hs : Separates E.hash ([rootsPre E r.root r.jroot r.rroot r.rowsroot, w.rootsPre E] ++
      readPres (journalSpec E) txId r.jpath w.journal)) :
    w.journalAt E txId = none :=
  (check_refused_uncommitted hE hn hc hk).resolve_right hs.not_collides

include hE in
/-- TOOTH (`check_refused_sound`): where the hash separates the inputs it compares, a refused
receipt is the World's recorded refusal. -/
theorem check_refused_sound_sep {w : World D} (hr : w.RefusalsOk E)
    {H : Nat} {txId : D} {nb : Nat} {r : Receipt D} {h code : Nat} {m : D}
    (hk : check E H (w.roots E) txId nb r = .ok (.refused h code m))
    (hs : Separates E.hash ([rootsPre E r.root r.jroot r.rroot r.rowsroot, w.rootsPre E] ++
      inclPres (refusalSpec E) (refusalPre E) (.tx txId) (.refused h code m) r.rpath w.refusals)) :
    w.refusalAt E (.tx txId) = some (.refused h code m) :=
  (check_refused_sound hE hr hk).resolve_right hs.not_collides

include hE in
/-- TOOTH (`check_absent_unrefused`): where the hash separates the inputs it compares, an absent
receipt shows no refusal recorded. -/
theorem check_absent_unrefused_sep {w : World D} (hr : w.RefusalsOk E)
    {H : Nat} {txId : D} {nb : Nat} {r : Receipt D}
    (hk : check E H (w.roots E) txId nb r = .ok .absent)
    (hs : Separates E.hash ([rootsPre E r.root r.jroot r.rroot r.rowsroot, w.rootsPre E] ++
      readPres (refusalSpec E) (.tx txId) r.rpath w.refusals)) :
    w.refusalAt E (.tx txId) = none :=
  (check_absent_unrefused hE hr hk).resolve_right hs.not_collides

end Sound

omit [Ord D] in
/-- **A refused receipt's path verifies against the head's refusals root** for the recorded
refusal it states, the head's roots opening to that root. -/
theorem check_refused {E : Env D} {H : Nat} {roots txId : D} {nb : Nat} {r : Receipt D} {h code : Nat} {m : D}
    (hk : check E H roots txId nb r = .ok (.refused h code m)) :
    rootsDigest E r.root r.jroot r.rroot r.rowsroot = roots ∧
      Trie.verifyInclusion (refusalSpec E) r.rroot (.tx txId) (refusalDigest E (.refused h code m)) r.rpath = true := by
  obtain ⟨-, hr, ha⟩ := check_ok hk
  refine ⟨hr, ?_⟩
  unfold answerOf at ha
  split at ha
  · split at ha <;> cases ha
  · split at ha
    · rename_i hv; cases ha; exact hv.2.2.1
    · cases ha
  · split at ha
    · cases ha
    · split at ha <;> cases ha

/-! ## Completeness: the member's own receipt checks (PROTOCOL-46) -/

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
          | refused h code m =>
              have ha : (build E w tx).answer = .refused h code m := by simp [build, hjx, hrx]
              rw [ha]
              simp only
              have hf := hr.2 _ _ hrx
              simp only [refusalFits, Bounds.counterLimit, decide_eq_true_eq] at hf
              rw [if_pos ⟨by omega, by omega, refusal_prove_verifies hr.1 hrx, journal_prove_absent hc hjx⟩]
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
          rw [if_neg (by simp [hf]), if_pos ⟨journal_prove_absent hc hjx, refusal_prove_absent hr.1 hrx⟩]

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

/-! ## The premises, discharged on every World folded from a genesis (`Receive.genesisWorld`) -/

/-- A folded World's height stays below 2^64: an admission lands inside its turn's window
(`admit_height_lt`), a recorded refusal keeps the height. -/
theorem fold_height_lt {E : Env D} {w w' : World D} {l : List (Kernel.Step D)} (hw : w.height < 2 ^ 64)
    (h : World.fold E w l = .ok w') : w'.height < 2 ^ 64 :=
  fold_keeps (P := fun v => v.height < 2 ^ 64) (fun _ ha => admit_height_lt ha)
    (fun hp hr => by dsimp only at hp ⊢; rw [(refuse_frame hr).2.2.1]; exact hp) hw h

/-- **Every journal height of a reached World fits a u64**: `JournalOk` puts each entry at or below
the World's height, which `fold_height_lt` bounds. Reached = folded from the World a genesis builds
(`Receive.genesisWorld`, founders included), where every Store starts. -/
theorem reached_journal_fits {X : Ctx D} {name nonce : ByteArray} {a : Nat} {fs : List (ByteArray × D)}
    {l : List (Kernel.Step D)} {w : World D}
    (h : World.fold X.env (genesisWorld X name nonce a fs) l = .ok w) :
    ∀ k e, w.journalAt X.env k = some e → e.1 < 2 ^ 64 := by
  intro k e he
  have h1 := ((fold_journalOk (genesisWorld_journalOk X name nonce a fs) h).2.1 k e he).1
  have h0 : (genesisWorld X name nonce a fs).height < 2 ^ 64 := by simp [genesisWorld, World.genesis]
  have h2 := fold_height_lt h0 h
  omega

/-- **`check_build` on every World folded from a genesis**, no premise but the answer's own: the
receipt follow builds from its World checks against that World's head, answering what it states,
unless `absent` past `journalForgets`. -/
theorem check_build_reached {X : Ctx D} {name nonce : ByteArray} {a : Nat} {fs : List (ByteArray × D)}
    {l : List (Kernel.Step D)} {w : World D}
    (h : World.fold X.env (genesisWorld X name nonce a fs) l = .ok w) {tx : D} {nb : Nat}
    (hnf : (build X.env w tx).answer ≠ .absent ∨ journalForgets w.height nb = false) :
    check X.env w.height (w.roots X.env) tx nb (build X.env w tx) = .ok (build X.env w tx).answer :=
  check_build (fold_journalOk (genesisWorld_journalOk X name nonce a fs) h).1
    (fold_refusalsOk (genesisWorld_refusalsOk X name nonce a fs) h) (reached_journal_fits h) hnf

end Nanodregg.Protocol.Receipt
