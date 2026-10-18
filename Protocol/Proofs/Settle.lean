/-
# Protocol.Proofs.Settle — a `refused` reply is the final one (PROTOCOL-41)

* `final_iff_recorded`: a submit's reply is `refused` exactly when the call was recorded now, or its
  transaction id already holds a recorded refusal, or its window has passed. No other reply is final.
  Off the admitted arm this restates `verdictReply` (a specification, not a finality fact; that is
  `final_recorded`'s); on the admitted arm it uses the kernel (no record before, window open).
* `final_recorded`: a final reply inside the call's window leaves the call recorded in the World the
  Host keeps, under the name the reply states. That record is what makes every later submit
  `refusedFinal` (`Kernel.Receive.judge_recorded_final`, `fold_refused_retains`).
* `declined_open`: a `declined` reply recorded nothing, changed nothing, and the call's window has not
  passed. The attempt store keeps it open.
* `admitted_no_reply`: an admitted call gets no refusal reply.
-/
import Protocol.Settle
import Kernel.Proofs.Refusals
import Kernel.Proofs.Fold

namespace Nanodregg.Protocol.Settle

open Nanodregg.Kernel Nanodregg.Kernel.Receive

variable {D : Type} [Ord D] [DecidableEq D]

theorem judge_admitted {X : Ctx D} {w w' : World D} {c : Call D} {t : Turn D}
    (h : judge X w c = .admitted t w') : submit X w c = .ok (t, w') := by
  unfold judge at h
  split at h
  · rename_i hs; cases h; exact hs
  · split at h
    · split at h <;> cases h
    · cases h

/-- What the receive layer and the kernel say about an admitted call: nothing recorded at its id
before, and its window contains the next height. -/
theorem admitted_facts {X : Ctx D} {w w' : World D} {c : Call D} {t : Turn D}
    (h : judge X w c = .admitted t w') :
    refusedAnswer X w c = none ∧ w.height < c.unsigned.validUntil := by
  have hs := judge_admitted h
  unfold submit at hs
  split at hs
  · cases hs
  · split at hs
    · cases hs
    · rename_i hra
      split at hs
      · cases hs
      · rename_i t' hr
        split at hs
        · cases hs
        · rename_i w'' ha
          have hv := (receive_ok hr).2.2.2.2.2.2.2
          have hw := (admit_window ha).2
          exact ⟨hra, by omega⟩

theorem admitted_no_reply {X : Ctx D} {w : World D} {c : Call D} {t : Turn D} {w' : World D} :
    verdictReply X w c (.admitted t w') = none := rfl

/-- **A reply is final exactly when the refusal is recorded, or was, or the window has passed.** -/
theorem final_iff_recorded {X : Ctx D} {w : World D} {c : Call D} {o : Outcome D}
    (hj : judge X w c = o) :
    (verdictReply X w c o).map Prod.fst = some .refused ↔
      (recordedNow o = true ∨ refusedAnswer X w c ≠ none ∨ c.unsigned.validUntil ≤ w.height) := by
  cases o with
  | admitted t w' =>
      obtain ⟨hra, hlt⟩ := admitted_facts hj
      simp only [verdictReply, Option.map_none, reduceCtorEq, false_iff, recordedNow,
        Bool.false_eq_true, hra, ne_eq, not_true_eq_false, false_or, Nat.not_le]
      exact hlt
  | recorded v r w' => simp [verdictReply, recordedNow]
  | declined v =>
      simp only [verdictReply, recordedNow, Bool.false_eq_true, false_or]
      cases hra : refusedAnswer X w c with
      | some code => simp
      | none =>
          by_cases hl : c.unsigned.validUntil ≤ w.height
          · simp [hl]
          · simp [hl]

/-- **A final reply inside the window is a record in the World the Host keeps**, under the reply's
own name (the recorded code names it, whenever it names anything). -/
theorem final_recorded {X : Ctx D} {w : World D} {c : Call D} {o : Outcome D} {n : String}
    (hj : judge X w c = o) (hr : verdictReply X w c o = some (.refused, n))
    (hin : w.height < c.unsigned.validUntil) :
    ∃ code, refusedAnswer X (keptWorld w o) c = some code ∧ ∀ m, codeName code = some m → m = n := by
  cases o with
  | admitted t w' => cases hr
  | recorded v r w' =>
      obtain ⟨-, -, rfl, href⟩ := judge_recorded hj
      simp only [verdictReply, Option.some.injEq, Prod.mk.injEq, true_and] at hr
      subst hr
      refine ⟨v.code, ?_, fun m hm => ?_⟩
      · have := refuse_recorded href
        simp only [keptWorld, refusedAnswer]
        rw [show (refusedOf X c v).txId = txIdOf X c from rfl] at this
        rw [this]; rfl
      · rw [codeName_code] at hm; exact (Option.some.inj hm).symm
  | declined v =>
      simp only [verdictReply] at hr
      cases hra : refusedAnswer X w c with
      | some code =>
          rw [hra] at hr
          simp only [Option.some.injEq, Prod.mk.injEq, true_and] at hr
          refine ⟨code, hra, fun m hm => ?_⟩
          rw [hm] at hr; simpa using hr
      | none =>
          rw [hra] at hr
          have hl : ¬ c.unsigned.validUntil ≤ w.height := by omega
          simp [hl] at hr

/-- **`declined` is open**: nothing was recorded, the World is unchanged, nothing was recorded for
this call before, and its window has not passed. -/
theorem declined_open {X : Ctx D} {w : World D} {c : Call D} {o : Outcome D} {n : String}
    (hr : verdictReply X w c o = some (.declined, n)) :
    (∃ v, o = .declined v ∧ v.name = n) ∧ keptWorld w o = w ∧ refusedAnswer X w c = none ∧
      w.height < c.unsigned.validUntil := by
  cases o with
  | admitted t w' => cases hr
  | recorded v r w' => simp [verdictReply] at hr
  | declined v =>
      simp only [verdictReply] at hr
      cases hra : refusedAnswer X w c with
      | some code => rw [hra] at hr; simp at hr
      | none =>
          rw [hra] at hr
          by_cases hl : c.unsigned.validUntil ≤ w.height
          · simp [hl] at hr
          · simp only [hl, ↓reduceIte, Option.some.injEq, Prod.mk.injEq, true_and] at hr
            exact ⟨⟨v, rfl, hr⟩, rfl, rfl, by omega⟩

end Nanodregg.Protocol.Settle
