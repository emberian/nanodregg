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
import Kernel.Proofs.Refusals
import Protocol.Proofs.Settle
import Host.Proofs.Batch

namespace Nanodregg.Host

open Nanodregg.Kernel Nanodregg.Kernel.Receive

variable {D : Type} [Ord D] [DecidableEq D]

/-- A journaled call is never admitted nor recorded by `judge`: `submit` answers `replayed`, and
`World.refuse` refuses a journaled transaction id. -/
theorem judge_journaled {X : Ctx D} {w : World D} {c : Call D} {h : Nat} {d : D}
    (hj : w.journalAt X.env (txIdOf X c) = some (h, d)) : ∃ v, judge X w c = .declined v := by
  have hs : submit X w c = .error (.rejected (.replayed h)) := by simp [submit, hj]
  have hr : ∀ v, ∃ e, World.refuse X.env w (refusedOf X c v) = .error e := by
    intro v
    unfold World.refuse checkRefusal
    simp only [refusedOf, hj]
    split
    · rename_i hok
      simp only [bind, Except.bind] at hok
      split at hok
      · cases hok
      · split at hok
        · cases hok
        · split at hok
          · cases hok
          · cases hok
    · exact ⟨_, rfl⟩
  unfold judge
  rw [hs]
  simp only
  split
  · obtain ⟨e, he⟩ := hr (.rejected (.replayed h))
    rw [he]
    cases e <;> exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩

/-- **The writer's machine commits only `World.step`'s steps**: a `submit` the handler commits is
`judge`'s `admitted` (the Turn admits to the World committed) or `recorded` (the refusal records to
the World committed), so `Machine.staged_rooted` holds of the Host at `World.step`. -/
theorem machine_commits (X : Ctx D) : (machine X).Commits (World.step X.env) := by
  intro w f s w' st p h
  simp only [machine] at h
  unfold handle at h
  repeat' split at h
  all_goals (try (cases h; done))
  all_goals (cases h)
  all_goals first
    | exact (submit_ok (Protocol.Settle.judge_admitted ‹_›)).2.2
    | exact (judge_recorded ‹_›).2.2.2

/-- What `judge`'s outcome stages (`Machine.step`'s pair), given the World committed. -/
private def judgeStaged (X : Ctx D) (out : Out (Step D × D)) : Outcome D → Array (Step D × D)
  | .admitted t w' => out.staged.push (.turn t, World.roots X.env w')
  | .recorded _ r w' => out.staged.push (.refusal r, World.roots X.env w')
  | .declined _ => out.staged

/-- **The loop decides a submit exactly as `Receive.judge` does (KERNEL-44).** One submit frame
carrying call `c`, stepped by the writer's machine from any batch accumulator, keeps the World
`judge` returns (`Protocol.Settle.keptWorld`) and stages exactly the step `judge` takes (an
admitted Turn, a recorded refusal, or nothing), each with the roots after it; the one exception is
the `forgotten` arm (an unrecorded call past `journalForgets`), which answers `uncertain` and
changes nothing. The loop adds no decision of its own between the signed call and the log. -/
theorem step_submit (X : Ctx D) (w : World D) (out : Out (Step D × D)) (q : Request Frame) (c : Call D)
    (hop : Protocol.Op.ofCode? q.body.op = some .submit) (hc : X.decodeCall q.body.payload = some c) :
    let g := (refusedAnswer X w c).isNone && journalForgets w.height c.unsigned.notBefore
    ((machine X).step (w, out) q).1 = (if g then w else Protocol.Settle.keptWorld w (judge X w c)) ∧
      ((machine X).step (w, out) q).2.staged = (if g then out.staged else judgeStaged X out (judge X w c)) := by
  intro g
  cases hj : w.journalAt X.env (txIdOf X c) with
  | some p =>
    obtain ⟨h, d⟩ := p
    obtain ⟨v, hv⟩ := judge_journaled hj
    simp [Machine.step, machine, handle, hop, hc, hj, hv, Protocol.Settle.keptWorld, judgeStaged]
  | none =>
    cases hg : g with
    | true =>
      simp only [g] at hg
      simp [Machine.step, machine, handle, hop, hc, hj, hg]
    | false =>
      simp only [g] at hg
      cases ho : judge X w c <;>
        simp [Machine.step, machine, handle, hop, hc, hj, hg, ho, Protocol.Settle.keptWorld, judgeStaged]

theorem step_journaled (X : Ctx D) (w : World D) (out : Out (Step D × D)) (q : Request Frame) (c : Call D)
    (h : Nat) (d : D)
    (hop : Protocol.Op.ofCode? q.body.op = some .submit) (hc : X.decodeCall q.body.payload = some c)
    (hj : w.journalAt X.env (txIdOf X c) = some (h, d)) :
    (machine X).step (w, out) q =
      (w, { out with replies := out.replies.push ⟨q.conn, Protocol.Status.ok.code, receipt X h d⟩ }) := by
  simp only [Machine.step, machine, handle, hop, hc, hj]

/-- A hang-up naming `r` is answered with exactly its acknowledgement, `closed ‖ r.name`
(`Protocol.ack r`, whose reason is `r`: `Protocol.ackReason?_ack`), stages nothing and leaves the
World as it was: it changes no other connection's reply. -/
theorem step_hangup (X : Ctx D) (w : World D) (out : Out (Step D × D)) (q : Request Frame)
    (r : Protocol.CloseReason) (hop : q.body.op = Protocol.hangupCode)
    (hp : Protocol.CloseReason.ofBytes? q.body.payload = some r) :
    (machine X).step (w, out) q =
      (w, { out with replies := out.replies.push ⟨q.conn, Protocol.Status.closed.code, r.name.toUTF8⟩ }) := by
  have hn : Protocol.Op.ofCode? Protocol.hangupCode = none := by decide
  have hk : Protocol.childKindOf? Protocol.hangupCode = some .hangup := by decide
  simp only [Machine.step, machine, handle, hop, hn, hangUpAnswer, hk, hp]

/-- A hang-up whose payload names no `CloseReason` is refused `badHangup` by name, and changes
nothing else either. -/
theorem step_hangup_bad (X : Ctx D) (w : World D) (out : Out (Step D × D)) (q : Request Frame)
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
    (hj : w.journalAt X.env (txIdOf X c) = none) (hr : refusedAnswer X w c = none)
    (hnf : journalForgets w.height c.unsigned.notBefore = false)
    (hv : c.unsigned.validUntil ≤ w.height) :
    handle X w f = .reply Protocol.Status.refused.code "expired".toUTF8 := by
  simp only [handle, hop, hc, hj, hr, hnf, hv, if_true, named, FrameRefusal.name]
  rfl

/-- A `lookup` of an un-journaled call whose transaction id holds a recorded refusal answers
`refused` with the name of the recorded code (KERNEL-44: the refusal is final within the window),
before `forgotten`, `expired` or `absent`. -/
theorem handle_lookup_refused (X : Ctx D) (w : World D) (f : Frame) (c : Call D) (code : Nat)
    (hop : Protocol.Op.ofCode? f.op = some .lookup) (hc : X.decodeCall f.payload = some c)
    (hj : w.journalAt X.env (txIdOf X c) = none) (hr : refusedAnswer X w c = some code) :
    handle X w f = .reply Protocol.Status.refused.code (recordedName code).toUTF8 := by
  simp only [handle, hop, hc, hj, hr, named]

/-- **A recorded refusal answers its own name (`Kernel.refused_answers`, PROTOCOL-33's shape).** A
call `judge` recorded with verdict `v` on `w₀`, followed by any log to `w`, is answered by `lookup`
on `w` with `refused v.name` for as long as the journal would still answer it (`journalForgets`
false); past that it is `uncertain forgotten` (`handle_lookup_forgotten`). -/
theorem lookup_recorded_answers (X : Ctx D) {w₀ w₁ w : World D} {f : Frame} {c : Call D} {v : Verdict D}
    {r : Refused D} {l : List (Step D)} (hrc : w₀.RefusalsCanon X.env) (hjc : w₀.JournalCanon X.env)
    (hop : Protocol.Op.ofCode? f.op = some .lookup) (hc : X.decodeCall f.payload = some c)
    (hjg : judge X w₀ c = .recorded v r w₁) (hf : World.fold X.env w₁ l = .ok w)
    (hnf : journalForgets w.height c.unsigned.notBefore = false) :
    handle X w f = .reply Protocol.Status.refused.code v.name.toUTF8 := by
  obtain ⟨-, -, hr, h₁⟩ := judge_recorded hjg
  subst hr
  obtain ⟨-, hnb, -, hj₀, -, -⟩ := refuse_facts h₁
  have hjc₁ : w₁.JournalCanon X.env := by
    unfold World.JournalCanon; rw [(refuse_frame h₁).2.1]; exact hjc
  simp only [journalForgets, decide_eq_false_iff_not, Nat.not_le] at hnf
  obtain ⟨hr₂, hj₂⟩ := fold_refused_retains (refuse_refusalsCanon hrc h₁) hjc₁ hf (refuse_recorded h₁)
    ((refuse_journalAt h₁ _).trans hj₀) (by simp only [refusedOf] at hnb; omega)
  have hra : refusedAnswer X w c = some v.code := by
    unfold refusedAnswer; simp only [refusedOf] at hr₂; rw [hr₂]
  simp only [refusedOf] at hj₂
  rw [handle_lookup_refused X w f c v.code hop hc hj₂ hra, recordedName, codeName_code]
  rfl

/-- Past `journalForgets` an un-journaled call's lookup is `uncertain forgotten` (KERNEL-33): its
entry may have been pruned, so neither `expired` nor `absent` would be true. -/
theorem handle_lookup_forgotten (X : Ctx D) (w : World D) (f : Frame) (c : Call D)
    (hop : Protocol.Op.ofCode? f.op = some .lookup) (hc : X.decodeCall f.payload = some c)
    (hj : w.journalAt X.env (txIdOf X c) = none) (hr : refusedAnswer X w c = none)
    (hfg : journalForgets w.height c.unsigned.notBefore = true) :
    handle X w f = .reply Protocol.Status.uncertain.code "forgotten".toUTF8 := by
  simp only [handle, hop, hc, hj, hr, hfg, if_true, forgotten]

omit [Ord D] [DecidableEq D] in
/-- No recorded code answers `expired`: the names are the receive refusals' and the kernel's, and
the fallback is `refusedFinal`. -/
theorem recordedName_ne_expired (code : Nat) : recordedName code ≠ "expired" := by
  unfold recordedName codeName
  split
  · cases h : refusalNames[code]? with
    | none => simp
    | some s =>
      have hm := List.mem_of_getElem? h
      simp only [Option.getD_some]
      intro he; subst he; revert hm; decide
  · cases h : rejectNames[code - refusalNames.length]? with
    | none => simp
    | some s =>
      have hm := List.mem_of_getElem? h
      simp only [Option.getD_some]
      intro he; subst he; revert hm; decide


/-- **`expired` means never committed (KERNEL-33).** A lookup that answers `refused expired`
answers it of a call no Turn derived from it was ever admitted on the way to this World: had
`receive` derived `t` from the call at some earlier World `w₀`, `t` been admitted there and any
admitted log led on to `w`, the journal at `w` would still hold `t`'s id, since below
`journalForgets` nothing admitted is pruned (`Kernel.fold_answers`), and the lookup would have
answered `ok` with its receipt. Stated from the ANSWER, not from the arm's guards. -/
theorem lookup_expired_never_committed (X : Ctx D)
    {w₀ w₁ w : World D} {f : Frame} {c : Call D} {t : Turn D} {l : List (Step D)}
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
      cases hra : refusedAnswer X w c with
      | some code =>
        simp only [hra, named, Answer.reply.injEq] at hans
        exact recordedName_ne_expired code (String.toByteArray_inj.mp (by simpa using hans.2))
      | none =>
        simp only [hra, hfg, if_true, forgotten, Answer.reply.injEq] at hans
        exact absurd hans.1 (by decide)

/-- **`expired` is final.** Over any admitted log from the World a lookup answered `expired` at,
the call's transaction id is journaled only by a Turn whose window ends after the call's own:
never by the call itself. -/
theorem lookup_expired_final (X : Ctx D) (c : Call D)
    {w w' : World D} {l : List (Step D)} (hcw : w.JournalCanon X.env) (hf : World.fold X.env w l = .ok w')
    (hj : w.journalAt X.env (txIdOf X c) = none) (hv : c.unsigned.validUntil ≤ w.height)
    (hj' : w'.journalAt X.env (txIdOf X c) ≠ none) :
    ∃ t ∈ Step.turns l, t.txId = txIdOf X c ∧ c.unsigned.validUntil < t.validUntil := by
  obtain ⟨t, ht, hk, hlt⟩ := absent_final hcw hf hj hj'
  exact ⟨t, ht, hk, by omega⟩


/-- **A batch keeps the journal's invariant (KERNEL-41).** The World the writer's machine keeps
after a batch is the end of a rooted run of steps from the World before it
(`Machine.staged_rooted` at `machine_commits`), so a batch from a `JournalOk` World ends at a `JournalOk` World
(`fold_journalOk`). With `Host.Record.foldlM_journalOk` at the open, every World the loop holds is
`JournalOk` once the base it opened from is, which is what the lookup theorems above take. -/
theorem admitBatch_journalOk (X : Ctx D) {w : World D} (qs : List (Request Frame))
    (hw : w.JournalOk X.env) : ((machine X).admitBatch w qs).1.JournalOk X.env :=
  fold_journalOk hw (RootedFold.fold ((machine X).staged_rooted (machine_commits X) w qs))

/-- **A batch keeps the refusals' invariant (KERNEL-44)**, as `admitBatch_journalOk` keeps the
journal's: what the lookup theorems' `RefusalsCanon` premise reads. -/
theorem admitBatch_refusalsOk (X : Ctx D) {w : World D} (qs : List (Request Frame))
    (hw : w.RefusalsOk X.env) : ((machine X).admitBatch w qs).1.RefusalsOk X.env :=
  fold_refusalsOk hw (RootedFold.fold ((machine X).staged_rooted (machine_commits X) w qs))

end Nanodregg.Host
