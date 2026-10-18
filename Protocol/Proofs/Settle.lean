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
import Kernel.Proofs.Receive
import Kernel.Proofs.Journal

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

/-! ## The member's settlement (PROTOCOL-46)

What `ofReceipt` says of a receipt follow built from its own World (`Receipt.build`):

* `settle_committed`: `committed h td` is the World's journal entry at the id;
* `settle_final_never_admits`: `refused` or `expired` is final: no World a later log reaches from it
  admits the call (`submit`). Proved from the World alone: the recorded refusal stays below its prune
  height (`Kernel.fold_refused_retains`) and the call's window has closed by then (the checkable arm
  `validUntil ≤ h + 2 · windowMax`); `expired` by the window alone;
* `settle_open_not_final`: every call some World would still admit settles `open` there, never final
  and never "safe to run again": the old terminal `absent` said that of exactly these calls.
-/

section Member

/-- What `build` answers, read from the World. -/
theorem build_answer (E : Env D) (w : World D) (tx : D) :
    (Receipt.build E w tx).answer = match w.journalAt E tx with
      | some (h, td) => .committed h td
      | none => match w.refusalAt E (.tx tx) with
        | some (.refused h code) => .refused h code
        | _ => .absent := rfl

/-- **A committed settlement is the World's journal entry.** -/
theorem settle_committed {E : Env D} {w : World D} {tx : D} {fg : Bool} {H vu h : Nat} {td : D}
    (hv : ofReceipt fg H vu (Receipt.build E w tx).answer = .committed h td) :
    w.journalAt E tx = some (h, td) := by
  rw [build_answer] at hv
  split at hv
  · rename_i h' td' hj
    simp only [ofReceipt, Verdict.committed.injEq] at hv
    obtain ⟨rfl, rfl⟩ := hv
    exact hj
  · split at hv
    · simp only [ofReceipt] at hv; split at hv <;> cases hv
    · simp only [ofReceipt] at hv; split at hv
      · cases hv
      · split at hv <;> cases hv

/-- An admitted call's World: nothing at its id, and its window contains the next height and closes
within `windowMax` of its `notBefore`. -/
theorem submit_facts {X : Ctx D} {w w' : World D} {c : Call D} {t : Turn D}
    (hs : submit X w c = .ok (t, w')) :
    w.journalAt X.env (txIdOf X c) = none ∧ refusedAnswer X w c = none ∧
      w.height < c.unsigned.validUntil ∧ c.unsigned.validUntil ≤ c.unsigned.notBefore + Bounds.windowMax := by
  obtain ⟨hj, hr, ha⟩ := submit_ok hs
  have hra : refusedAnswer X w c = none := by
    unfold submit at hs
    rw [hj] at hs
    simp only at hs
    split at hs
    · cases hs
    · assumption
  obtain ⟨_, _, _, _, _, _, hnb, hvu⟩ := receive_ok hr
  have hw := admit_window ha
  have hb := admit_bounded ha
  unfold checkBounds at hb
  simp only [except_bind_ok] at hb
  obtain ⟨⟨⟩, _, ⟨⟩, _, ⟨⟩, _, ⟨⟩, _, ⟨⟩, _, ⟨⟩, _, ⟨⟩, _, ⟨⟩, _, ⟨⟩, hwm, _⟩ := hb
  rw [req_ok, decide_eq_true_eq] at hwm
  refine ⟨hj, hra, by omega, by omega⟩

/-- **A final settlement is never admitted** (`refused` or `expired`, from the member's own World):
no World any later log reaches from it admits the call. -/
theorem settle_final_never_admits {X : Ctx D} {w w' : World D} {c : Call D} {l : List (Kernel.Step D)}
    (hc : w.RefusalsCanon X.env) (hjc : w.JournalCanon X.env)
    (hv : ofReceipt (journalForgets w.height c.unsigned.notBefore) w.height c.unsigned.validUntil
        (Receipt.build X.env w (txIdOf X c)).answer = .expired ∨
      ∃ code, ofReceipt (journalForgets w.height c.unsigned.notBefore) w.height c.unsigned.validUntil
        (Receipt.build X.env w (txIdOf X c)).answer = .refused code)
    (hf : World.fold X.env w l = .ok w') : ∀ out, submit X w' c ≠ .ok out := by
  intro ⟨t, w''⟩ hs
  obtain ⟨-, hra, hlt, -⟩ := submit_facts hs
  have hh := fold_height hf
  rw [build_answer] at hv
  split at hv
  · rcases hv with hv | ⟨_, hv⟩ <;> cases hv
  · rename_i hj
    split at hv
    · rename_i hh₀ code hr
      simp only [ofReceipt] at hv
      split at hv
      · rename_i hwin
        by_cases hp : w'.height < hh₀ + 2 * Bounds.windowMax
        · obtain ⟨hr', -⟩ := fold_refused_retains hc hjc hf hr hj hp
          unfold refusedAnswer at hra
          rw [hr'] at hra
          cases hra
        · omega
      · rcases hv with hv | ⟨_, hv⟩ <;> cases hv
    · simp only [ofReceipt] at hv
      split at hv
      · rcases hv with hv | ⟨_, hv⟩ <;> cases hv
      · split at hv
        · omega
        · rcases hv with hv | ⟨_, hv⟩ <;> cases hv

/-- **An admissible call settles `open`, never final**: wherever `submit` would still admit the call,
the member's own settlement of it there is `open`. So a run that ends on `absent` with the call's
window live must leave the attempt open: the signed bytes, held by the Host or any relay, may still
be admitted, and a re-signed command would make a second call beside it (the deleted terminal
`absent` said "running the command again is safe" of exactly these calls). -/
theorem settle_open_not_final {X : Ctx D} {w w' : World D} {c : Call D} {t : Turn D}
    (hs : submit X w c = .ok (t, w')) :
    ofReceipt (journalForgets w.height c.unsigned.notBefore) w.height c.unsigned.validUntil
      (Receipt.build X.env w (txIdOf X c)).answer = .open := by
  obtain ⟨hj, hra, hlt, hwm⟩ := submit_facts hs
  have hnf : journalForgets w.height c.unsigned.notBefore = false := by
    simp only [journalForgets, decide_eq_false_iff_not]
    rw [windowMax_eq] at hwm
    rw [windowMax_eq]
    omega
  have hnot : ¬ c.unsigned.validUntil ≤ w.height := by omega
  unfold refusedAnswer at hra
  rw [build_answer]
  simp only [hj]
  cases hr : w.refusalAt X.env (.tx (txIdOf X c)) with
  | none => simp [ofReceipt, hnf, hnot]
  | some leaf =>
      cases leaf with
      | refused h code => simp [hr] at hra
      | count n => simp [ofReceipt, hnf, hnot]

end Member

end Nanodregg.Protocol.Settle
