/-
# Kernel.Proofs.RefuseAdmissible — the record of an admissible call's refusal is one `World.refuse` accepts

`refuse_admissible`: for a call `judge` admits on `w` (its window ending below the counter limit),
while the member and the World have refusal budget left, the judged-refusal record of THAT call
(`refusedOf X c v`, any verdict of a counted code: its event the call's own bytes, no cancel field)
is accepted by `World.refuse` on `w`. `World.refuse` does not re-judge a record (it checks the
record's bounds, the World's step counter, the call's window, the journal, the recorded refusals
and the budgets), so a writer can record an admissible call as refused and the kernel's transition
takes it: only `Honest` (that `judge` decided the step) refuses such a writer. This is the witness
that `Host.host_step_folds_tooth_censor`'s premises hold together (READ-HOST F6).
-/
import Kernel.Proofs.Receive
import Kernel.Proofs.Admit

namespace Nanodregg.Kernel.Receive

open Nanodregg.Kernel

variable {D : Type} [Ord D] [DecidableEq D]

/-- `judge` admits a call exactly through `submit` admitting it. -/
theorem submit_of_judge_admitted {X : Ctx D} {w w₁ : World D} {c : Call D} {t : Turn D}
    (hj : judge X w c = .admitted t w₁) : submit X w c = .ok (t, w₁) := by
  unfold judge judgeBy at hj
  cases h : submit X w c with
  | ok p =>
    obtain ⟨t', w'⟩ := p
    rw [h] at hj
    cases hj
    rfl
  | error e =>
    rw [h] at hj
    simp only at hj
    repeat' split at hj
    all_goals cases hj

/-- **The record of an admissible call's refusal is accepted** (the censor's premises, together).
A call `judge` admits on `w`, its signed window ending below `counterLimit`, a verdict of a counted
code, the member under its `refusalsPerWindow` and the World under `refusalsPerWindowMax`: the record
`refusedOf X c v` carries the call's bytes as its event, no cancel field, and `World.refuse` accepts
it on `w`. -/
theorem refuse_admissible {X : Ctx D} {w w₁ : World D} {c : Call D} {t : Turn D} {v : Verdict D}
    (hj : judge X w c = .admitted t w₁) (hv : v.code < Bounds.counterLimit)
    (hu : c.unsigned.validUntil < Bounds.counterLimit)
    (hm : refusalCount X.env w c.unsigned.member < Bounds.refusalsPerWindow)
    (ht : refusalTotal X.env w < Bounds.refusalsPerWindowMax) :
    (refusedOf X c v).event = X.callBytes c ∧ (refusedOf X c v).cancel.size = 0 ∧
      ∃ w', World.refuse X.env w (refusedOf X c v) = .ok w' := by
  obtain ⟨hjn, hr, ha⟩ := submit_ok (submit_of_judge_admitted hj)
  have hd := receive_derived hr
  obtain ⟨posts, hc, -⟩ := admit_ok ha
  have hb := hc.bounds
  have hjr := hc.journal
  have hw := hc.window
  have hst := hc.steps
  unfold checkWindow at hw
  rw [req_ok, hd.notBefore, hd.validUntil] at hw
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hw
  unfold checkJournal at hjr
  rw [hd.txId, hjn] at hjr
  simp only at hjr
  have hev : (X.callBytes c).size ≤ Bounds.eventBytesMax ∧
      c.unsigned.validUntil ≤ c.unsigned.notBefore + Bounds.windowMax := by
    rw [← hd.event, ← hd.notBefore, ← hd.validUntil]
    unfold checkBounds at hb
    simp only [except_bind_ok] at hb
    obtain ⟨⟨⟩, _, ⟨⟩, _, ⟨⟩, _, ⟨⟩, _, ⟨⟩, he, ⟨⟩, _, ⟨⟩, _, ⟨⟩, _, ⟨⟩, hwin, _⟩ := hb
    rw [req_ok, decide_eq_true_eq] at he hwin
    exact ⟨he, hwin⟩
  have hnb : c.unsigned.notBefore < Bounds.counterLimit := by omega
  refine ⟨rfl, rfl, commitRefusal X.env w (refusedOf X c v), ?_⟩
  have hok : checkRefusal X.env w (refusedOf X c v) = .ok () := by
    unfold checkRefusal checkRefusedBounds
    simp only [refusedOf, recordOf]
    cases hra : w.refusalAt X.env (.tx (txIdOf X c)) with
    | none =>
      simp [req, bind, Except.bind, hst, hjn, hev.1, hev.2, hm, ht, hw.1, hw.2, hv, hu, hnb]
    | some lf =>
      rw [hra] at hjr
      cases lf with
      | refused h' code m => simp at hjr
      | count n =>
        simp [req, bind, Except.bind, hst, hjn, hev.1, hev.2, hm, ht, hw.1, hw.2, hv, hu, hnb]
  unfold World.refuse
  rw [hok]

end Nanodregg.Kernel.Receive
