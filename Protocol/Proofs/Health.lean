/-
# Protocol.Proofs.Health — a health receipt that checks against a World's head states its counters

`check_sound`: a health receipt that checks against a World's own head (`Head.headOf`) states that
World's three counters for the member — `ticksUsed` (the meter its next Turn is charged against,
KERNEL-68), `refusalCount` and `refusalTotal` (the refusal window, KERNEL-50, KERNEL-55) — or two of the
listed inputs collide: the two roots digests' preimages and, per counter, what its path compares
(an inclusion's when the counter is positive, an exclusion's when it is zero). Through KERNEL's
`refusal_inclusion_sound` / `refusal_exclusion_sound` (`Kernel.Proofs.RefusalsHead`). `check_build`:
the receipt a World builds checks against its own head and answers its own counters.
-/
import Protocol.Health
import Kernel.Proofs.RefusalsHead
import Kernel.Proofs.Admit

namespace Nanodregg.Protocol.Health

open Nanodregg.Kernel

variable {D : Type} [Ord D] [DecidableEq D]

/-- What one counter's path compares: an inclusion's inputs when the counter is positive, an
exclusion's when it is zero. -/
def countPres (E : Env D) (w : World D) (k : WindowSlot D) (n : Nat) (p : Trie.Proof (WindowSlot D) D) :
    List (String × ByteArray) :=
  if n = 0 then readPres (refusalSpec E) k p w.refusals
  else inclPres (refusalSpec E) (refusalPre E) k (.count n) p w.refusals

/-- Every input `check_sound` names: the two roots preimages and the three counters' paths'. -/
def pres (E : Env D) (w : World D) (m : D) (r : Health D) : List (String × ByteArray) :=
  [rootsPre E r.root r.jroot r.rroot r.rowsroot, w.rootsPre E] ++
    (countPres E w (ticksKey m w.height) r.answer.ticks r.tpath ++
     countPres E w (countKey m w.height) r.answer.refusals r.cpath ++
     countPres E w (totalKey w.origin w.height) r.answer.total r.opath)

theorem countAt_ticksKey (E : Env D) (w : World D) (m : D) :
    countAt E w (ticksKey m w.height) = ticksUsed E w m := by
  unfold countAt ticksKey ticksUsed World.meterAt
  split <;> simp_all

theorem countAt_countKey (E : Env D) (w : World D) (m : D) :
    countAt E w (countKey m w.height) = refusalCount E w m := by
  unfold countAt countKey refusalCount World.refusalAt
  rfl

theorem countAt_totalKey (E : Env D) (w : World D) :
    countAt E w (totalKey w.origin w.height) = refusalTotal E w := by
  unfold countAt totalKey refusalTotal World.refusalAt
  rfl

theorem answerOf_eq (E : Env D) (w : World D) (m : D) :
    answerOf E w m = ⟨ticksUsed E w m, refusalCount E w m, refusalTotal E w⟩ := by
  unfold answerOf
  rw [countAt_ticksKey, countAt_countKey, countAt_totalKey]

section Sound
variable {E : Env D} {n : Nat} (hE : E.Lawful n)

include hE in
/-- **One counter's path is the World's counter**, or what it compares collides. -/
theorem counted_sound {w : World D} (hr : w.RefusalsOk E) {k : WindowSlot D} {c : Nat}
    {p : Trie.Proof (WindowSlot D) D} (hp : counted E (w.refusalsRoot E) k c p = true) :
    countAt E w k = c ∨ CollidesAmong E.hash (countPres E w k c p) := by
  unfold counted at hp
  unfold countPres
  by_cases hc : c = 0
  · rw [if_pos hc] at hp ⊢
    rcases refusal_exclusion_sound hE hr.1 hp with hg | col
    · left; subst hc; unfold countAt; rw [hg]
    · exact .inr col
  · rw [if_neg hc] at hp ⊢
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
    rcases refusal_inclusion_sound hE hr.1 (refusalsOk_fits hr) (v := .count c) hp.1 hp.2 with hg | col
    · left; unfold countAt; rw [hg]
    · exact .inr col

include hE in
/-- **A health receipt that checks against a World's own head states that World's counters** for the
member: its meter in the window its next Turn lands in, its refusal count and the World's refusal total
in the window a refusal now lands in — or two of the listed inputs collide. A relay can neither change
a counter nor answer for another window: the windows are the head's height's. -/
theorem check_sound {w : World D} (hr : w.RefusalsOk E) {m : D} {r : Health D} {a : Answer}
    (hk : check E (Head.headOf E w) m r = .ok a) :
    (ticksUsed E w m = a.ticks ∧ refusalCount E w m = a.refusals ∧ refusalTotal E w = a.total) ∨
      CollidesAmong E.hash (pres E w m r) := by
  unfold check at hk
  split at hk
  · cases hk
  · rename_i hm
    split at hk
    · cases hk
    · rename_i hroots
      split at hk
      · rename_i hv
        cases hk
        have hm' : r.member = m := Classical.not_not.mp hm
        have hroots' := Classical.not_not.mp hroots
        simp only [Head.headOf] at hroots' hv
        rw [World.roots_eq] at hroots'
        rcases rootsDigest_inj hE hroots' with ⟨-, -, hrr, -⟩ | col
        · rw [hrr] at hv
          obtain ⟨ht, hc, ho⟩ := hv
          rcases counted_sound hE hr ht with ht | ct
          · rcases counted_sound hE hr hc with hc | cc
            · rcases counted_sound hE hr ho with ho | co
              · left
                rw [← countAt_ticksKey, ← countAt_countKey, ← countAt_totalKey]
                exact ⟨ht, hc, ho⟩
              · exact .inr (CollidesAmong.mono (fun x hx => by unfold pres; simp [hx]) co)
            · exact .inr (CollidesAmong.mono (fun x hx => by unfold pres; simp [hx]) cc)
          · exact .inr (CollidesAmong.mono (fun x hx => by unfold pres; simp [hx]) ct)
        · exact .inr (CollidesAmong.mono (fun x hx => by
            unfold pres; simp only [List.mem_append]; exact .inl hx) col)
      · cases hk

include hE in
/-- TOOTH (`check_sound`): where the hash separates the inputs it names, the receipt's answer is the
World's three counters. -/
theorem check_sound_sep {w : World D} (hr : w.RefusalsOk E) {m : D} {r : Health D} {a : Answer}
    (hk : check E (Head.headOf E w) m r = .ok a) (hs : Separates E.hash (pres E w m r)) :
    ticksUsed E w m = a.ticks ∧ refusalCount E w m = a.refusals ∧ refusalTotal E w = a.total :=
  (check_sound hE hr hk).resolve_right hs.not_collides

end Sound

/-- A counter key's own path verifies at the World's own root, for the counter the World holds
(`refusalFits`: a counter key holds only a `count` leaf, between 1 and its bound). -/
theorem counted_build {E : Env D} {w : World D} (hr : w.RefusalsOk E) {k : WindowSlot D}
    (hk : ∀ x, k ≠ .refusal (.tx x)) :
    counted E (w.refusalsRoot E) k (countAt E w k) (w.refusals.prove (refusalSpec E) k) = true := by
  cases hg : w.refusals.get (refusalSpec E) k with
  | none =>
    have h0 : countAt E w k = 0 := by unfold countAt; rw [hg]
    rw [h0]; unfold counted; rw [if_pos rfl]; exact refusal_prove_absent hr.1 hg
  | some v =>
    have hf := hr.2 k v hg
    cases v with
    | refused h c m' =>
      exfalso
      rcases k with k | k <;> cases k <;> first | exact hk _ rfl | simp [refusalFits] at hf
    | count c =>
      have h1 : countAt E w k = c := by unfold countAt; rw [hg]
      have hb : 1 ≤ c ∧ c < 2 ^ 64 := by
        rcases k with k | k <;> cases k <;>
          simp [refusalFits, Bounds.refusalsPerWindow, Bounds.refusalsPerWindowMax,
            Bounds.ticksPerWindow, Bounds.treeTicksMax] at hf <;> exact ⟨hf.2.1, by have := hf.2.2; omega⟩
      rw [h1]; unfold counted; rw [if_neg (by omega)]
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨hb.2, refusal_prove_verifies hr.1 hg⟩

/-- **The receipt a World builds checks against its own head**, and answers the World's counters. -/
theorem check_build {E : Env D} {w : World D} (hr : w.RefusalsOk E) (m : D) :
    check E (Head.headOf E w) m (build E w m) =
      .ok ⟨ticksUsed E w m, refusalCount E w m, refusalTotal E w⟩ := by
  rw [← answerOf_eq]
  unfold check build
  dsimp only
  rw [if_neg (fun h => h rfl), if_neg (fun h => h (World.roots_eq E w).symm),
    if_pos ⟨counted_build hr (fun _ h => by cases h), counted_build hr (fun _ h => by cases h),
      counted_build hr (fun _ h => by cases h)⟩]

end Nanodregg.Protocol.Health
