/-
# Host.Proofs.Serve — the loop decides a submit exactly as `Kernel.Receive.submit` does

`step_submit`: one submit frame carrying call `c`, stepped by the writer's machine from any batch
accumulator, leaves the World `Receive.submit` returns (or the World unchanged when it refuses),
and stages exactly the Turn `Receive.submit` derives (or nothing). The loop adds no decision of its
own between the signed call and the log.

`step_journaled`: a call already in the journal answers `ok` with its ORIGINAL receipt (height and
turn digest from the journal) and leaves the World and the staged Turns as they were — whatever
`receive` would now say about it (a retried rotation must not be re-judged, KERNEL-7).

`handle_lookup_expired` / `lookup_expired_final` (HOST-21): a `lookup` of an un-journaled call whose
window ended at or before the World's height answers `refused expired`, and that answer is final:
if any later World of an admitted log journals the call's transaction id, some Turn of that log
carries the id with a window ending strictly AFTER the call's own. A Turn derived from the call has
the call's window (`receive` copies it), so that Turn is another call with the same `txIdOf`: a
collision.
-/
import Host.Serve
import Kernel.Proofs.Fold
import Kernel.Proofs.Journal
import Kernel.Proofs.RootedFold
import Host.Proofs.Batch

namespace Nanodregg.Host

open Nanodregg.Kernel Nanodregg.Kernel.Receive

variable {D : Type} [Ord D] [DecidableEq D]

theorem step_submit (X : Ctx D) (w : World D) (out : Out (Turn D × (D × D))) (q : Request Frame) (c : Call D)
    (hop : Protocol.Op.ofCode? q.body.op = some .submit) (hc : X.decodeCall q.body.payload = some c) :
    ((machine X).step (w, out) q).1 =
        (match submit X w c with | .ok (_, w') => w' | .error _ => w) ∧
      ((machine X).step (w, out) q).2.staged =
        (match submit X w c with | .ok (t, w') => out.staged.push (t, World.roots X.env w') | .error _ => out.staged) := by
  cases hfg : journalForgets w.height c.unsigned.notBefore
  case true =>
    cases hj : w.journalAt X.env (txIdOf X c) with
    | some p => simp [Machine.step, machine, handle, hop, hc, submit, hj]
    | none =>
      have hs := submit_forgotten (X := X) hfg
      cases hsub : submit X w c with
      | ok r => exact absurd hsub (hs r)
      | error v => simp [Machine.step, machine, handle, hop, hc, hj, hfg]
  case false =>
  simp only [Machine.step, machine, handle, hop, hc, submit]
  cases hj : w.journalAt X.env (txIdOf X c) with
  | some p => simp
  | none =>
    simp only [hfg, Bool.false_eq_true, if_false]
    cases hr : receive X w c with
    | error r => simp
    | ok t =>
      simp only
      cases ha : World.admit X.env w t with
      | error r => simp
      | ok w' => simp

theorem step_journaled (X : Ctx D) (w : World D) (out : Out (Turn D × (D × D))) (q : Request Frame) (c : Call D)
    (h : Nat) (d : D)
    (hop : Protocol.Op.ofCode? q.body.op = some .submit) (hc : X.decodeCall q.body.payload = some c)
    (hj : w.journalAt X.env (txIdOf X c) = some (h, d)) :
    (machine X).step (w, out) q =
      (w, { out with replies := out.replies.push ⟨q.conn, Protocol.Status.ok.code, receipt X h d⟩ }) := by
  simp only [Machine.step, machine, handle, hop, hc, hj]

/-- A hang-up naming `r` is answered with exactly its acknowledgement, `closed ‖ r.name`
(`Protocol.ack r`, whose reason is `r`: `Protocol.ackReason?_ack`), stages nothing and leaves the
World as it was: it changes no other connection's reply. -/
theorem step_hangup (X : Ctx D) (w : World D) (out : Out (Turn D × (D × D))) (q : Request Frame)
    (r : Protocol.CloseReason) (hop : q.body.op = Protocol.hangupCode)
    (hp : Protocol.CloseReason.ofBytes? q.body.payload = some r) :
    (machine X).step (w, out) q =
      (w, { out with replies := out.replies.push ⟨q.conn, Protocol.Status.closed.code, r.name.toUTF8⟩ }) := by
  have hn : Protocol.Op.ofCode? Protocol.hangupCode = none := by decide
  have hk : Protocol.childKindOf? Protocol.hangupCode = some .hangup := by decide
  simp only [Machine.step, machine, handle, hop, hn, hangUpAnswer, hk, hp]

/-- A hang-up whose payload names no `CloseReason` is refused `badHangup` by name, and changes
nothing else either. -/
theorem step_hangup_bad (X : Ctx D) (w : World D) (out : Out (Turn D × (D × D))) (q : Request Frame)
    (hop : q.body.op = Protocol.hangupCode) (hp : Protocol.CloseReason.ofBytes? q.body.payload = none) :
    (machine X).step (w, out) q =
      (w, { out with
        replies := out.replies.push ⟨q.conn, Protocol.Status.refused.code, FrameRefusal.badHangup.name.toUTF8⟩ }) := by
  have hn : Protocol.Op.ofCode? Protocol.hangupCode = none := by decide
  have hk : Protocol.childKindOf? Protocol.hangupCode = some .hangup := by decide
  simp only [Machine.step, machine, handle, hop, hn, hangUpAnswer, hk, hp, named]

/-- The acknowledgement as a reply's `status ‖ payload` is `Protocol.ack r`. -/
theorem hangup_reply_is_ack (r : Protocol.CloseReason) :
    ByteArray.mk #[Protocol.Status.closed.code] ++ r.name.toUTF8 = Protocol.ack r := rfl

theorem handle_lookup_expired (X : Ctx D) (w : World D) (f : Frame) (c : Call D)
    (hop : Protocol.Op.ofCode? f.op = some .lookup) (hc : X.decodeCall f.payload = some c)
    (hj : w.journalAt X.env (txIdOf X c) = none) (hnf : journalForgets w.height c.unsigned.notBefore = false)
    (hv : c.unsigned.validUntil ≤ w.height) :
    handle X w f = .reply Protocol.Status.refused.code "expired".toUTF8 := by
  simp only [handle, hop, hc, hj, hnf, hv, if_true, named, FrameRefusal.name]
  rfl

/-- Past `journalForgets` an un-journaled call's lookup is `uncertain forgotten` (KERNEL-33): its
entry may have been pruned, so neither `expired` nor `absent` would be true. -/
theorem handle_lookup_forgotten (X : Ctx D) (w : World D) (f : Frame) (c : Call D)
    (hop : Protocol.Op.ofCode? f.op = some .lookup) (hc : X.decodeCall f.payload = some c)
    (hj : w.journalAt X.env (txIdOf X c) = none) (hfg : journalForgets w.height c.unsigned.notBefore = true) :
    handle X w f = .reply Protocol.Status.uncertain.code "forgotten".toUTF8 := by
  simp only [handle, hop, hc, hj, hfg, if_true, forgotten]

/-- **`expired` means never committed (KERNEL-33).** A lookup that answers `refused expired`
answers it of a call no Turn derived from it was ever admitted on the way to this World: had
`receive` derived `t` from the call at some earlier World `w₀`, `t` been admitted there and any
admitted log led on to `w`, the journal at `w` would still hold `t`'s id, since below
`journalForgets` nothing admitted is pruned (`Kernel.fold_answers`), and the lookup would have
answered `ok` with its receipt. Stated from the ANSWER, not from the arm's guards. -/
theorem lookup_expired_never_committed (X : Ctx D)
    {w₀ w₁ w : World D} {f : Frame} {c : Call D} {t : Turn D} {l : List (Turn D)}
    (hcw : w₀.JournalCanon X.env)
    (hop : Protocol.Op.ofCode? f.op = some .lookup) (hc : X.decodeCall f.payload = some c)
    (hans : handle X w f = .reply Protocol.Status.refused.code "expired".toUTF8)
    (hr : receive X w₀ c = .ok t) (ha : World.admit X.env w₀ t = .ok w₁)
    (hf : World.fold X.env w₁ l = .ok w) : False := by
  obtain ⟨_, _, _, _, _, htx, hnb, _⟩ := receive_ok hr
  simp only [handle, hop, hc] at hans
  cases hj : w.journalAt X.env (txIdOf X c) with
  | some p =>
    obtain ⟨h, d⟩ := p
    rw [hj] at hans
    simp only [Answer.reply.injEq] at hans
    exact absurd hans.1 (by decide)
  | none =>
    cases hfg : journalForgets w.height c.unsigned.notBefore
    · have hk := fold_answers hcw ha hf (by rw [hnb]; exact hfg)
      rw [htx, hj] at hk
      cases hk
    · rw [hj] at hans
      simp only [hfg, if_true, forgotten, Answer.reply.injEq] at hans
      exact absurd hans.1 (by decide)

/-- **`expired` is final.** Over any admitted log from the World a lookup answered `expired` at,
the call's transaction id is journaled only by a Turn whose window ends after the call's own:
never by the call itself. -/
theorem lookup_expired_final (X : Ctx D) (c : Call D)
    {w w' : World D} {l : List (Turn D)} (hcw : w.JournalCanon X.env) (hf : World.fold X.env w l = .ok w')
    (hj : w.journalAt X.env (txIdOf X c) = none) (hv : c.unsigned.validUntil ≤ w.height)
    (hj' : w'.journalAt X.env (txIdOf X c) ≠ none) :
    ∃ t ∈ l, t.txId = txIdOf X c ∧ c.unsigned.validUntil < t.validUntil := by
  obtain ⟨t, ht, hk, hlt⟩ := absent_final hcw hf hj hj'
  exact ⟨t, ht, hk, by omega⟩


/-- **A batch keeps the journal's invariant (KERNEL-41).** The World the writer's machine keeps
after a batch is the end of a rooted run of admitted Turns from the World before it
(`Machine.staged_rooted`), so a batch from a `JournalOk` World ends at a `JournalOk` World
(`fold_journalOk`). With `Host.Record.foldlM_journalOk` at the open, every World the loop holds is
`JournalOk` once the base it opened from is, which is what the lookup theorems above take. -/
theorem admitBatch_journalOk (X : Ctx D) {w : World D} (qs : List (Request Frame))
    (hw : w.JournalOk X.env) : ((machine X).admitBatch w qs).1.JournalOk X.env :=
  fold_journalOk hw (RootedFold.fold ((machine X).staged_rooted w qs))

end Nanodregg.Host
