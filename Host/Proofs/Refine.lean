/-
# Host.Proofs.Refine — `Host ⊑ Kernel`: every Host step is an honest fold of the kernel's, every reopen a fold

The Host's state's World component IS the kernel's abstract state (a projection, no abstraction
function), and every edge the Host takes on it is one of three kinds:

* **a step** — `(machine X).step`, one request of a batch, TOTAL over every frame code (the seven
  protocol ops, a hang-up, an unknown code). `host_step_folds`: the World after it is the fold of
  ZERO or ONE kernel steps from the World before it, that list is `Honest` (each step is what
  `judge` decides of its own signed event, or `cancel` of a member's signed cancel: exactly what
  `host follow`'s `absorbStep` re-derives, `absorbStep_honest`), the staged pairs grow by exactly that list (each with the roots after it), and
  a nonempty list comes only from a frame whose op writes (`Op.effect = .write`: `submit` and
  `cancel`, `Protocol.Op.effect_write_iff`). MEASURED at the definition (`Host.Serve.handle`): those
  two are the only ops whose arms commit, `submit` only through `judge` (`step_submit`, sharper: the
  World is `judge`'s) and `cancel` only through `Receive.cancel` (`step_cancel`, HOST-66);
  `lookup`, `read`, `log`, `command`, `resume`, a hang-up and an unknown code reply or
  defer and leave the World. `host_run_folds` composes a batch from any accumulator;
  `host_run_absorbed` says the follower that runs (`host follow`: `Protocol.Command.absorb` over
  the page events `Page.stepEvent` serves) re-derives exactly what the Host staged, reaching the
  World the Host keeps; `honest_page_absorbed` says the same of one page through `absorbPage`
  (HOST-75).
* **a start** — `host genesis`, genesis `host join` and `host import` (also the carried join's import under its signed origin) (KERNEL's
  carry) each make a fresh World, never a step from one: `host_start_kept` says each is `Kept`
  (the relation's invariant half), so `host_run_kept` applies from the first batch.
* **a reopen** (the crash edge) — `host_reopen_folds`: the World the deployed open returns is the
  fold, from a `Kept` base World, of exactly the steps the segment's records decode to, and those
  records are exactly the segment's bytes up to the open's position (`openWith_world`). A fold,
  NOT an audited one: the writer's reopen does not re-judge its own records (`foldStep`), and no
  theorem here ties the segment's bytes to what `admitBatch` staged, so `Honest` is not carried
  across a crash. That is the write side's theorem (a record appended is `Record.codec` of the
  staged batch), not proved here.

`seal`, `sealNow`, `makeRoom` and `finish` are not edges on the World: each is IO whose only pure
act on the resident is `Resident.install`, which rewrites `sealed`, `pending` and `index` and
leaves `world`. That half is IO; the kernel-sim plants (`same`, `reopened`: the four tries'
listings and roots after every seed and after every reopen) STAY as its witness, and as the
witness of IO order, which no theorem here speaks for.

The one premise of the generic theorems is the call codec's canonicity: a call the Ctx decodes
re-encodes to the very bytes it came from (`X.decodeCall b = some c → X.callBytes c = b`), which is
what makes a logged event decode to the call the Host judged. It is discharged at the deployed
`Ctx` by CODEC's `eq_callBytes_of_decodeCall`. Neither `Kept` nor `X.Lawful` is needed for the
fold; `Kept` is carried by the deployed corollaries (`kept_fold`). No landed theorem gains a
premise: this module adds statements and changes none.

Teeth, each a machine equal to the writer's except at ONE frame code (any of the seven ops, a hang-up,
an unknown code), so one per op and more: `host_step_folds_tooth_unmoved` — an arm that stages a
step and keeps the World (a log that lies about the World), every `Ctx`, refused by the fold and
staged conjuncts; `host_step_folds_tooth_wrong_op` — an arm at any op that does not write
(not `submit`, not `cancel`) that commits anything, refused by the op conjunct; `host_step_folds_tooth_unjudged` — on a `Ctx` that decodes
no call, an arm at a `submit` frame that takes a step `World.step` accepts: it `Commits` (so
`staged_rooted` holds of it), every other conjunct holds of `[s]`, and only `Honest` refuses it; `host_step_folds_tooth_censor` — at any `Ctx` meeting the
premise (the deployed one), an arm that records a refusal of a call `judge` would ADMIT, again a
machine that `Commits`, refused only by `Honest`. `kept_refutable` — `Kept` is not every World.
-/
import Host.Proofs.Serve
import Host.Proofs.Deployed
import Kernel.Proofs.Audit
import Kernel.Proofs.Origin
import Protocol.Proofs.Invite
import Protocol.Proofs.Command
import Codec.Proofs.Deployed

namespace Nanodregg.Host

open Nanodregg.Kernel Nanodregg.Kernel.Receive

variable {D : Type} [Ord D] [DecidableEq D]

/-- What the writer's handler commits: a `submit` frame's decoded call, `judge`'s admitted Turn or
recorded refusal, to `judge`'s World; or a `cancel` frame's call and signature, `cancel`'s recorded
cancel, to `cancel`'s World (HOST-66). -/
private theorem handle_commit {X : Ctx D} {w w' : World D} {f : Frame} {s : Step D} {st : UInt8}
    {p : ByteArray} (h : handle X w f = .commit s w' st p) :
    (Protocol.Op.ofCode? f.op = some .submit ∧ ∃ c, X.decodeCall f.payload = some c ∧
      ((∃ t, judge X w c = .admitted t w' ∧ s = .turn t) ∨
        (∃ v r, judge X w c = .recorded v r w' ∧ s = .refusal r))) ∨
    (Protocol.Op.ofCode? f.op = some .cancel ∧ ∃ c sig cb, f.payload[0]? = some Protocol.eventCancel ∧
      Protocol.cancelParts f.payload = some (sig, cb) ∧ X.decodeCall cb = some c ∧
      ∃ v r, cancel X w c sig = .recorded v r w' ∧ s = .refusal r) := by
  unfold handle at h
  cases hop : Protocol.Op.ofCode? f.op with
  | none =>
    simp only [hop] at h
    split at h <;> cases h
  | some op =>
    cases op
    case submit =>
      simp only [hop] at h
      refine .inl ⟨rfl, ?_⟩
      cases hc : X.decodeCall f.payload with
      | none => simp only [hc] at h; cases h
      | some c =>
        simp only [hc] at h
        refine ⟨c, rfl, ?_⟩
        split at h
        · cases h
        · split at h
          · cases h
          · split at h
            · rename_i t w₁ hj
              cases h
              exact .inl ⟨t, hj, rfl⟩
            · rename_i v r w₁ hj
              cases h
              exact .inr ⟨v, r, hj, rfl⟩
            · cases h
    case cancel =>
      simp only [hop] at h
      split at h
      · cases h
      · rename_i sig cb hif
        have hfp : f.payload[0]? = some Protocol.eventCancel ∧ Protocol.cancelParts f.payload = some (sig, cb) := by
          split at hif
          · exact ⟨‹_›, hif⟩
          · cases hif
        split at h
        · cases h
        · rename_i c hc
          split at h
          · cases h
          · split at h
            · cases h
            · split at h
              · rename_i v r w₁ hco
                cases h
                exact .inr ⟨rfl, c, sig, cb, hfp.1, hfp.2, hc, v, r, hco, rfl⟩
              · cases h
    all_goals
      simp only [hop] at h
      repeat' split at h
      all_goals cases h

/-- A cancel `cancel` records is what its record's re-judge records: its signature is non-empty
(`cancelAuth`), so `recordedBy` re-decides it by `cancel` with that signature. -/
private theorem recordedBy_of_cancel {X : Ctx D} {w w' : World D} {c : Call D} {sig : ByteArray}
    {v : Verdict D} {r : Refused D} (h : cancel X w c sig = .recorded v r w') :
    recordedBy X w c r = .recorded v r w' := by
  obtain ⟨ha, -, hr, -⟩ := cancel_recorded h
  subst hr
  have hk : (cancelOf X c sig).cancel.size ≠ 0 :=
    Nat.pos_iff_ne_zero.mp (Protocol.Command.cancelAuth_size ha).1
  unfold recordedBy
  rw [if_neg hk]
  exact h

/-- An `Honest` log continued by an `Honest` log from where it ends is `Honest`. -/
private theorem honest_append {X : Ctx D} :
    ∀ {w w₁ : World D} {l₁ l₂ : List (Step D)}, Honest X w l₁ → World.fold X.env w l₁ = .ok w₁ →
      Honest X w₁ l₂ → Honest X w (l₁ ++ l₂)
  | w, w₁, [], l₂, _, hf, h₂ => by
    simp only [World.fold, Except.ok.injEq] at hf
    subst hf
    exact h₂
  | w, w₁, .turn t :: rest, l₂, h₁, hf, h₂ => by
    obtain ⟨c, hd, hr, k⟩ := h₁
    obtain ⟨v, hv, hfr⟩ := fold_cons_ok.mp hf
    refine ⟨c, hd, hr, fun w' ha => ?_⟩
    have hv' : World.admit X.env w t = .ok v := hv
    rw [hv'] at ha
    cases ha
    exact honest_append (k v hv') hfr h₂
  | w, w₁, .refusal r :: rest, l₂, h₁, hf, h₂ => by
    obtain ⟨c, v₀, u, hd, hj, k⟩ := h₁
    obtain ⟨v, hv, hfr⟩ := fold_cons_ok.mp hf
    refine ⟨c, v₀, u, hd, hj, fun w' ha => ?_⟩
    have hv' : World.refuse X.env w r = .ok v := hv
    rw [hv'] at ha
    cases ha
    exact honest_append (k v hv') hfr h₂

/-! ## The follower that runs: `absorb` over the page events the writer serves (HOST-75)

`host follow` re-derives the writer's log by `Protocol.Command.absorbStep` over the bytes a page
carries, `Page.stepEvent` of each step: `0 ‖ call` for a Turn, `1 ‖ call` for a judged refusal,
`2 ‖ nat64 n ‖ sig ‖ call` for a cancel. The completeness direction, for each kind: an honest step
(`Honest`: what `receive`, `judge` or `cancel` decides of its own event) is absorbed as exactly that
step to exactly the World the kernel's step reaches. No codec premise: `Honest` names the call
each event decodes to. -/

/-- A Turn `receive` derives from `c` on `w` and `World.admit` takes is what `submit` returns: the
admission's journal check is `submit`'s first two arms. -/
private theorem submit_of_admit {X : Ctx D} {w w' : World D} {c : Call D} {t : Turn D}
    (hcr : w.RowsCanon X.env) (hr : receive X w c = .ok t) (ha : World.admit X.env w t = .ok w') :
    submit X w c = .ok (t, w') := by
  obtain ⟨posts, hc, -⟩ := admit_ok ha
  have hj := hc.journal
  have htx := (receive_derived hr).txId
  unfold checkJournal at hj
  have hjn : w.journalAt X.env (txIdOf X c) = none := by
    rw [← htx]
    cases h1 : w.journalAt X.env t.txId with
    | some p => obtain ⟨h0, d0⟩ := p; rw [h1] at hj; cases hj
    | none => rfl
  have hrf : refusedAnswer X w c = none := by
    unfold refusedAnswer
    rw [← htx]
    have hjt : w.journalAt X.env t.txId = none := by rw [htx]; exact hjn
    rw [hjt] at hj
    cases h2 : w.refusalAt X.env (.tx t.txId) with
    | none => rfl
    | some x => rw [h2] at hj; cases x <;> first | rfl | cases hj
  have hr0 := hr
  rw [receive_signed] at hr
  cases hs : signedBy X w c false with
  | error e => rw [hs] at hr; cases hr
  | ok u =>
    cases u
    rw [hs] at hr
    simp only [bind, Except.bind] at hr
    have hp : checkPins X.env w c.unsigned.pins c.unsigned.rowPins c.unsigned.ranges = .ok () := by
      cases hp : checkPins X.env w c.unsigned.pins c.unsigned.rowPins c.unsigned.ranges with
      | ok u => cases u; rfl
      | error r => exact absurd ha (checkPins_error_never_admitted hcr hp hr0 w')
    unfold submit
    rw [hjn]
    simp only [hrf, hs, hp, hr, ha]

private theorem tag_size (b : UInt8) : (⟨#[b]⟩ : ByteArray).size = 1 := rfl

private theorem tagged_pos (b : UInt8) (e : ByteArray) : 0 < (⟨#[b]⟩ ++ e : ByteArray).size := by
  simp only [ByteArray.size_append, tag_size]
  omega

private theorem tagged_head (b : UInt8) (e : ByteArray) :
    (⟨#[b]⟩ ++ e : ByteArray)[0]'(tagged_pos b e) = b := by
  rw [ByteArray.getElem_append_left (by rw [tag_size]; exact Nat.zero_lt_one)]
  rfl

private theorem tagged_tail (b : UInt8) (e : ByteArray) :
    (⟨#[b]⟩ ++ e : ByteArray).extract 1 (⟨#[b]⟩ ++ e : ByteArray).size = e :=
  ByteArray.extract_append_eq_right (tag_size b).symm (by simp only [ByteArray.size_append, tag_size])

/-- **An honest Turn's event is absorbed as that Turn** (the completeness half of the Turn arm):
a Turn `receive` derives from the call its event decodes to, on `w`, and `World.admit` takes to
`w'`, is re-derived from `0 ‖ t.event` by follow's `absorbStep` as exactly `t`, to exactly `w'`. -/
theorem absorbStep_turnEvent {X : Ctx D} {w w' : World D} {c : Call D} {t : Turn D}
    (hcr : w.RowsCanon X.env) (hd : X.decodeCall t.event = some c) (hr : receive X w c = .ok t)
    (ha : World.admit X.env w t = .ok w') :
    Protocol.Command.absorbStep X w (Page.stepEvent (.turn t)) = .ok (.turn t, w') := by
  have hs := submit_of_admit hcr hr ha
  have hne : ¬ Protocol.eventTurn = Protocol.eventCancel := by decide
  unfold Protocol.Command.absorbStep
  simp only [Page.stepEvent, tagged_pos, ↓reduceDIte, tagged_head, hne, ↓reduceIte,
    Protocol.Command.eventCall, tagged_tail, hd, hs]

/-- **An honest judged refusal's event is absorbed as that record** (the completeness half of the
refusal arm, which a page carries as `1 ‖ call` without the record): a refusal `judge` records of
the call its event decodes to is re-derived from the event by follow's own `judge` as exactly
`r`, to exactly the World `judge` reached. -/
theorem absorbStep_refusalEvent {X : Ctx D} {w w' : World D} {c : Call D} {v : Verdict D}
    {r : Refused D} (hd : X.decodeCall r.event = some c) (hj : judge X w c = .recorded v r w') :
    Protocol.Command.absorbStep X w (Page.stepEvent (.refusal r)) = .ok (.refusal r, w') := by
  have hk : r.cancel.size = 0 := by rw [(judge_recorded hj).2.2.1]; rfl
  have hne : ¬ Protocol.eventRefusal = Protocol.eventCancel := by decide
  have hnt : ¬ Protocol.eventRefusal = Protocol.eventTurn := by decide
  unfold Protocol.Command.absorbStep
  simp only [Page.stepEvent, hk, ↓reduceIte, tagged_pos, ↓reduceDIte, tagged_head, hne, hnt,
    Protocol.Command.eventCall, tagged_tail, hd, hj]

/-- **Every honest step's event is absorbed as that step**: the three arms (a cancel by
`Protocol.Command.absorbStep_cancelEvent`). -/
theorem absorbStep_honest {X : Ctx D} {w w' : World D} {s : Step D} {rest : List (Step D)}
    (hcr : w.RowsCanon X.env) (hh : Honest X w (s :: rest)) (hs : World.step X.env w s = .ok w') :
    Protocol.Command.absorbStep X w (Page.stepEvent s) = .ok (s, w') ∧ Honest X w' rest := by
  cases s with
  | turn t =>
    obtain ⟨c, hd, hr, k⟩ := hh
    exact ⟨absorbStep_turnEvent hcr hd hr hs, k w' hs⟩
  | refusal r =>
    obtain ⟨c, v, u, hd, hrb, k⟩ := hh
    refine ⟨?_, k w' hs⟩
    unfold recordedBy at hrb
    split at hrb
    · obtain ⟨-, -, -, hru⟩ := judge_recorded hrb
      have hu : u = w' := by
        have : World.refuse X.env w r = .ok w' := hs
        rw [hru] at this; exact Except.ok.inj this
      subst hu
      exact absorbStep_refusalEvent hd hrb
    · rename_i hk
      obtain ⟨-, -, hro, hru⟩ := cancel_recorded hrb
      have hu : u = w' := by
        have : World.refuse X.env w r = .ok w' := hs
        rw [hru] at this; exact Except.ok.inj this
      subst hu
      have hdec : X.decodeCall (X.callBytes c) = some c := by
        rw [show X.callBytes c = r.event by rw [hro]; rfl]; exact hd
      rw [Page.stepEvent_cancel hk]
      exact Protocol.Command.absorbStep_cancelEvent hdec hrb

/-- **The follower absorbs an honest log exactly** (HOST-75): from any accumulator, `absorb` of the
page events of a rooted run whose steps are `Honest` returns the run's end World and appends exactly
its (step, roots) pairs: what `host follow` persists is what the writer staged. -/
theorem absorb_honest {X : Ctx D} :
    ∀ {w w' : World D} {ps : List (Step D × D)} (acc : Array (Step D × D)),
      w.RowsCanon X.env → World.RootedFold X.env w ps w' → Honest X w (ps.map Prod.fst) →
        Protocol.Command.absorb X w acc (ps.map (Page.stepEvent ∘ Prod.fst)) = .ok (w', acc ++ ps.toArray)
  | w, w', [], acc, _, hf, _ => by
    simp only [World.RootedFold, Rooted] at hf
    subst hf
    simp [Protocol.Command.absorb]
  | w, w', (s, n) :: ps, acc, hcr, hf, hh => by
    obtain ⟨w₁, hs, hn, hr⟩ := hf
    obtain ⟨ha, hh'⟩ := absorbStep_honest hcr hh hs
    have hcr₁ : w₁.RowsCanon X.env := by
      cases s with
      | turn t => exact admit_rowsCanon hcr hs
      | refusal r => exact refuse_rowsCanon hcr hs
    have ih := absorb_honest (acc.push (s, World.roots X.env w₁)) hcr₁ hr hh'
    simp only [List.map_cons, Function.comp, Protocol.Command.absorb, ha]
    rw [ih, hn]
    simp

private theorem rooted_split {E : Env D} :
    ∀ {w w' : World D} {ps : List (Step D × D)} (k : Nat), World.RootedFold E w ps w' →
      ∃ wb, World.RootedFold E w (ps.take k) wb ∧ World.RootedFold E wb (ps.drop k) w'
  | w, w', [], k, h => ⟨w, by simp [World.RootedFold, Rooted], by simpa using h⟩
  | w, w', p :: ps, 0, h => ⟨w, by simp [World.RootedFold, Rooted], by simpa using h⟩
  | w, w', (s, n) :: ps, k + 1, h => by
    obtain ⟨w₁, ha, hn, hr⟩ := h
    obtain ⟨wb, h1, h2⟩ := rooted_split k hr
    exact ⟨wb, ⟨w₁, ha, hn, h1⟩, by simpa using h2⟩

private theorem honest_split {X : Ctx D} :
    ∀ {w w₁ : World D} {l₁ l₂ : List (Step D)}, Honest X w (l₁ ++ l₂) → World.fold X.env w l₁ = .ok w₁ →
      Honest X w l₁ ∧ Honest X w₁ l₂
  | w, w₁, [], l₂, h, hf => by
    simp only [World.fold, Except.ok.injEq] at hf
    subst hf
    exact ⟨trivial, h⟩
  | w, w₁, .turn t :: rest, l₂, h, hf => by
    obtain ⟨c, hd, hr, k⟩ := h
    obtain ⟨v, hv, hfr⟩ := fold_cons_ok.mp hf
    have hv' : World.admit X.env w t = .ok v := hv
    obtain ⟨h1, h2⟩ := honest_split (k v hv') hfr
    refine ⟨⟨c, hd, hr, fun w' ha => ?_⟩, h2⟩
    rw [hv'] at ha
    cases ha
    exact h1
  | w, w₁, .refusal r :: rest, l₂, h, hf => by
    obtain ⟨c, v₀, u, hd, hj, k⟩ := h
    obtain ⟨v, hv, hfr⟩ := fold_cons_ok.mp hf
    have hv' : World.refuse X.env w r = .ok v := hv
    obtain ⟨h1, h2⟩ := honest_split (k v hv') hfr
    refine ⟨⟨c, v₀, u, hd, hj, fun w' ha => ?_⟩, h2⟩
    rw [hv'] at ha
    cases ha
    exact h1

/-- **`honest_page_absorbed`** (HOST-75): a page holding the events of an honest rooted run, stating
the run's end step count and chain, is absorbed by follow's `absorbPage`, wherever the writer's
stated base cuts it: follow reaches the run's end World and keeps exactly its (step, roots) pairs.
Turns, judged refusals and cancels alike (`absorbStep_honest`). -/
theorem honest_page_absorbed {X : Ctx D} {w w' : World D} {ps : List (Step D × D)} (base : Nat)
    (hcr : w.RowsCanon X.env) (hf : World.RootedFold X.env w ps w') (hh : Honest X w (ps.map Prod.fst))
    (hn : ps.length ≤ Protocol.Bounds.pageStepsMax) :
    ∃ wb?, Protocol.Command.absorbPage X w (ps.map (Page.stepEvent ∘ Prod.fst)) w'.steps
      (X.env.bytes w'.chain) base = .ok (w', ps, wb?) := by
  obtain ⟨wb, h1, h2⟩ := rooted_split (base - w.steps) hf
  have hsplit : ps.map Prod.fst = (ps.take (base - w.steps)).map Prod.fst ++ (ps.drop (base - w.steps)).map Prod.fst := by
    rw [← List.map_append, List.take_append_drop]
  rw [hsplit] at hh
  obtain ⟨hh1, hh2⟩ := honest_split hh (RootedFold.fold h1)
  have ha1 := absorb_honest #[] hcr h1 hh1
  have ha2 := absorb_honest (#[] ++ (ps.take (base - w.steps)).toArray)
    (fold_rowsCanon hcr (RootedFold.fold h1)) h2 hh2
  refine ⟨if wb.steps = base then some wb else none, ?_⟩
  unfold Protocol.Command.absorbPage
  have hlen : ¬ Protocol.Bounds.pageStepsMax < (ps.map (Page.stepEvent ∘ Prod.fst)).length := by
    simp only [List.length_map]; omega
  simp only [hlen, ↓reduceIte, ← List.map_take, ← List.map_drop, ha1, ha2, bind, Except.bind, and_self,
    pure, Except.pure]
  simp

private theorem untag {e : ByteArray} (h : 0 < e.size) : e = ⟨#[e[0]]⟩ ++ e.extract 1 e.size := by
  have h1 : (⟨#[e[0]]⟩ : ByteArray).size = 1 := rfl
  apply ByteArray.ext_getElem
  · simp only [ByteArray.size_append, h1, ByteArray.size_extract]; omega
  · intro i hi hj
    by_cases hi0 : i = 0
    · subst hi0
      rw [ByteArray.getElem_append_left (by rw [h1]; exact Nat.zero_lt_one)]
      rfl
    · rw [ByteArray.getElem_append_right (by rw [h1]; omega)]
      simp only [ByteArray.getElem_extract, h1]
      congr 1
      omega

/-- **What the follower absorbs is an honest step, and the page event IS that step's** (HOST-75,
the soundness half): with the call codec canonical (`hX`; deployed: `deployed_canonical`), an event
`absorbStep` takes to step `s` is exactly `Page.stepEvent s` (one encoding per step), `s` is
`World.step`'s on `w`, and `s` is what `receive` / `judge` / `cancel` decides of its own event
(`Honest`). With `absorbStep_honest` this makes `absorbStep` the follower's re-derivation exactly:
an event is absorbed iff it is the page event of an honest step. -/
theorem absorbStep_sound {X : Ctx D} (hX : ∀ b c, X.decodeCall b = some c → X.callBytes c = b)
    {w w' : World D} {e : ByteArray} {s : Step D}
    (h : Protocol.Command.absorbStep X w e = .ok (s, w')) :
    World.step X.env w s = .ok w' ∧ Page.stepEvent s = e ∧
      ∀ rest, Honest X w' rest → Honest X w (s :: rest) := by
  have hws := Protocol.Command.absorbStep_step h
  refine ⟨hws, ?_⟩
  unfold Protocol.Command.absorbStep at h
  split at h
  · rename_i hpos
    split at h
    · -- a cancel
      rename_i htag
      split at h
      · cases h
      · rename_i sig cb hp
        split at h
        · cases h
        · rename_i c hc
          split at h
          · rename_i v r w₁ hco
            simp only [Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            obtain ⟨ha, -, hro, -⟩ := cancel_recorded hco
            have hk : r.cancel.size ≠ 0 := by
              rw [hro]; exact Nat.pos_iff_ne_zero.mp (Protocol.Command.cancelAuth_size ha).1
            have hcb : X.callBytes c = cb := hX _ _ hc
            have hev : r.event = X.callBytes c := by rw [hro]; rfl
            have hsg : r.cancel = sig := by rw [hro]; rfl
            refine ⟨?_, fun rest hr => ⟨c, v, w₁, by rw [hev, hcb]; exact hc, ?_, fun w'' hw => ?_⟩⟩
            · rw [Page.stepEvent_cancel hk, hev, hcb, hsg]
              obtain ⟨he, -, -⟩ := Protocol.Command.cancelParts_some hp hpos
              rw [he, htag]
              rfl
            · unfold recordedBy; rw [if_neg hk, hsg]; exact hco
            · have : World.refuse X.env w r = .ok w'' := hw
              rw [(cancel_recorded hco).2.2.2] at this
              cases this; exact hr
          · cases h
    · split at h
      · cases h
      · rename_i c hc
        have hcb : X.callBytes c = e.extract 1 e.size := hX _ _ hc
        split at h
        · -- a Turn
          rename_i htt
          split at h
          · rename_i t w₁ hs
            simp only [Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            obtain ⟨-, hr, ha⟩ := submit_ok hs
            have hev : t.event = e.extract 1 e.size := by rw [(receive_derived hr).event, hcb]
            refine ⟨?_, fun rest hrest => ⟨c, by rw [hev]; exact hc, hr, fun w'' hw => ?_⟩⟩
            · show ⟨#[Protocol.eventTurn]⟩ ++ t.event = e
              rw [hev, ← htt]; exact (untag hpos).symm
            · rw [ha] at hw; cases hw; exact hrest
          · cases h
          · cases h
        · split at h
          · -- a judged refusal
            rename_i _ htr
            split at h
            · rename_i v r w₁ hj
              simp only [Except.ok.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              obtain ⟨-, -, hro, hrf⟩ := judge_recorded hj
              have hk : r.cancel.size = 0 := by rw [hro]; rfl
              have hev : r.event = e.extract 1 e.size := by rw [hro, ← hcb]; rfl
              refine ⟨?_, fun rest hrest => ⟨c, v, w₁, by rw [hev]; exact hc, recordedBy_of_judge hj,
                fun w'' hw => ?_⟩⟩
              · show (if r.cancel.size = 0 then ⟨#[Protocol.eventRefusal]⟩ ++ r.event
                  else Protocol.cancelEvent r.cancel r.event) = e
                rw [if_pos hk, hev, ← htr]; exact (untag hpos).symm
              · have : World.refuse X.env w r = .ok w'' := hw
                rw [hrf] at this; cases this; exact hrest
            · cases h
          · cases h
  · cases h

/-- **What the follower absorbs is an honest rooted run, and the events are its page events**
(HOST-75, the soundness half over a list; the codec canonical). -/
theorem absorb_sound {X : Ctx D} (hX : ∀ b c, X.decodeCall b = some c → X.callBytes c = b) :
    ∀ {w w' : World D} {acc ts : Array (Step D × D)} {evs : List ByteArray},
      Protocol.Command.absorb X w acc evs = .ok (w', ts) →
      ∃ ps : List (Step D × D), ts = acc ++ ps.toArray ∧ World.RootedFold X.env w ps w' ∧
        Honest X w (ps.map Prod.fst) ∧ evs = ps.map (Page.stepEvent ∘ Prod.fst)
  | w, w', acc, ts, [], h => by
    simp only [Protocol.Command.absorb, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨[], by simp, rfl, trivial, rfl⟩
  | w, w', acc, ts, e :: es, h => by
    unfold Protocol.Command.absorb at h
    split at h
    · rename_i s w₁ hs
      obtain ⟨ps, hts, hr, hh, hevs⟩ := absorb_sound hX h
      obtain ⟨hws, hev, hon⟩ := absorbStep_sound hX hs
      refine ⟨(s, World.roots X.env w₁) :: ps, by rw [hts]; simp, ⟨w₁, hws, rfl, hr⟩, hon _ hh, ?_⟩
      simp only [List.map_cons, Function.comp, hev, hevs]
    · cases h

/-- **The follower absorbs a list of events exactly when they are the page events of an honest
rooted run** (HOST-75): `absorb` is the re-derivation, both ways, from a World whose rows trie is
canonical (`RowsCanon`, which every `Kept` World has and every step keeps). `→` is `absorb_sound`
(the codec canonical); `←` is `absorb_honest`. So the kernel's facts about `Honest` logs (`audit_ok`
turns them into an `audit` the Kernel's theorems take) are facts about what `host follow` keeps. -/
theorem absorb_iff {X : Ctx D} (hX : ∀ b c, X.decodeCall b = some c → X.callBytes c = b)
    {w w' : World D} (hcr : w.RowsCanon X.env) {acc ts : Array (Step D × D)} {evs : List ByteArray} :
    Protocol.Command.absorb X w acc evs = .ok (w', ts) ↔
      ∃ ps : List (Step D × D), ts = acc ++ ps.toArray ∧ World.RootedFold X.env w ps w' ∧
        Honest X w (ps.map Prod.fst) ∧ evs = ps.map (Page.stepEvent ∘ Prod.fst) := by
  constructor
  · exact absorb_sound hX
  · rintro ⟨ps, rfl, hr, hh, rfl⟩
    exact absorb_honest acc hcr hr hh

/-- **`Host ⊑ Kernel`, one step.** Any request, from any batch accumulator: the World the writer's
machine keeps is the fold of at most one kernel step from the World before it; that step is
`Honest` (what `judge` decides of its own signed event); the staged pairs grow by exactly it, with
the roots after it; and a step is taken only for a frame whose op writes (`submit`, `cancel`).
Total over every frame code by `handle`'s match: a new op without a case does not compile, and one
whose arm commits anything but `judge`'s or `cancel`'s answer breaks this statement (`host_step_folds_tooth_unmoved`, `_wrong_op`, `_unjudged`,
`_censor`). -/
theorem host_step_folds (X : Ctx D) (hX : ∀ b c, X.decodeCall b = some c → X.callBytes c = b)
    (w : World D) (out : Out (Step D × D)) (q : Request Frame) :
    ∃ l : List (Step D), l.length ≤ 1 ∧
      World.fold X.env w l = .ok ((machine X).step (w, out) q).1 ∧ Honest X w l ∧
      ((machine X).step (w, out) q).2.staged.toList =
        out.staged.toList ++ l.map (fun s => (s, World.roots X.env ((machine X).step (w, out) q).1)) ∧
      (l ≠ [] → ∃ op, Protocol.Op.ofCode? q.body.op = some op ∧ op.effect = .write) := by
  cases ha : handle X w q.body with
  | reply st p =>
    refine ⟨[], by simp, ?_, trivial, ?_, fun h => absurd rfl h⟩ <;>
      simp [Machine.step, machine, ha, World.fold]
  | defer d =>
    refine ⟨[], by simp, ?_, trivial, ?_, fun h => absurd rfl h⟩ <;>
      simp [Machine.step, machine, ha, World.fold]
  | commit s w' st p =>
    have hstep : (machine X).step (w, out) q =
        (w', { out with staged := out.staged.push (s, World.roots X.env w'),
                        replies := out.replies.push ⟨q.conn, st, p⟩ }) := by
      simp [Machine.step, machine, ha]
    rw [hstep]
    have hws : World.step X.env w s = .ok w' := machine_commits X w q.body s w' st p ha
    rcases handle_commit ha with ⟨hop, c, hc, hj⟩ | ⟨hop, c, sig, cb, -, -, hc, v, r, hco, rfl⟩
    rotate_left
    · -- a cancel (HOST-66): `cancel`'s record, re-decided by `recordedBy`
      have hcb : X.decodeCall (X.callBytes c) = some c := by rw [hX _ _ hc]; exact hc
      refine ⟨[.refusal r], by simp, by simp only [World.fold, hws], ?_, by simp, fun _ => ⟨_, hop, rfl⟩⟩
      obtain ⟨-, -, hr, -⟩ := cancel_recorded hco
      refine ⟨c, v, w', ?_, recordedBy_of_cancel hco, fun _ _ => trivial⟩
      rw [hr]
      exact hcb
    have hcb : X.decodeCall (X.callBytes c) = some c := by rw [hX _ _ hc]; exact hc
    refine ⟨[s], by simp, ?_, ?_, by simp, fun _ => ⟨_, hop, rfl⟩⟩
    · simp only [World.fold, hws]
    · rcases hj with ⟨t, hjt, rfl⟩ | ⟨v, r, hjr, rfl⟩
      · obtain ⟨-, hr, -⟩ := submit_ok (Protocol.Settle.judge_admitted hjt)
        refine ⟨c, ?_, hr, fun _ _ => trivial⟩
        rw [(receive_derived hr).event]
        exact hcb
      · obtain ⟨-, -, hr, -⟩ := judge_recorded hjr
        refine ⟨c, v, w', ?_, recordedBy_of_judge hjr, fun _ _ => trivial⟩
        rw [hr]
        exact hcb

/-- **`Host ⊑ Kernel`, a batch.** Any requests, from any accumulator: the World the writer keeps is
the fold of an `Honest` list of kernel steps, at most one per request, and the steps staged are
exactly that list after those already staged (`Machine.staged_rooted` states the roots). -/
theorem host_run_folds (X : Ctx D) (hX : ∀ b c, X.decodeCall b = some c → X.callBytes c = b) :
    ∀ (qs : List (Request Frame)) (w : World D) (out : Out (Step D × D)),
      ∃ l : List (Step D), l.length ≤ qs.length ∧
        World.fold X.env w l = .ok ((machine X).run (w, out) qs).1 ∧ Honest X w l ∧
        ((machine X).run (w, out) qs).2.staged.toList.map Prod.fst = out.staged.toList.map Prod.fst ++ l
  | [], w, out => ⟨[], Nat.le_refl _, rfl, trivial, by simp [Machine.run]⟩
  | q :: qs, w, out => by
    obtain ⟨l₁, hl₁, hf₁, hh₁, hs₁, -⟩ := host_step_folds X hX w out q
    generalize hacc : (machine X).step (w, out) q = acc at hf₁ hs₁
    obtain ⟨w₁, out₁⟩ := acc
    obtain ⟨l₂, hl₂, hf₂, hh₂, hs₂⟩ := host_run_folds X hX qs w₁ out₁
    have hrun : (machine X).run (w, out) (q :: qs) = (machine X).run (w₁, out₁) qs := by
      simp only [Machine.run, List.foldl_cons, hacc]
    rw [hrun]
    refine ⟨l₁ ++ l₂, by simp; omega, fold_append.mpr ⟨w₁, hf₁, hf₂⟩, honest_append hh₁ hf₁ hh₂, ?_⟩
    rw [hs₂]
    simp only at hs₁
    rw [hs₁]
    simp [Function.comp_def]

/-- **The follower that runs absorbs exactly what the Host staged** (HOST-75): a batch from a World
stages pairs whose page events (`Page.stepEvent`, what a page serves) `host follow`'s `absorb`
re-derives step by step from the same World, reaching the World the Host keeps and appending
exactly the staged (step, roots) pairs. This is the follower `host follow` runs
(`Protocol.Command.absorbStep`, reached by `Follow.answer` → `Command.step` → `absorbPage`). -/
theorem host_run_absorbed (X : Ctx D) (hX : ∀ b c, X.decodeCall b = some c → X.callBytes c = b)
    (w : World D) (hcr : w.RowsCanon X.env) (qs : List (Request Frame)) :
    Protocol.Command.absorb X w #[]
        (((machine X).admitBatch w qs).2.staged.toList.map (Page.stepEvent ∘ Prod.fst)) =
      .ok (((machine X).admitBatch w qs).1, ((machine X).admitBatch w qs).2.staged) := by
  obtain ⟨l, -, -, hh, hs⟩ := host_run_folds X hX qs w {}
  have hs' : ((machine X).admitBatch w qs).2.staged.toList.map Prod.fst = l := by
    simpa using hs
  have hr := (machine X).staged_rooted (machine_commits X) w qs
  rw [← hs'] at hh
  have := absorb_honest #[] hcr hr hh
  simpa using this

/-- **TOOTH (`host_step_folds`, every frame code, every `Ctx`): a step that stages without moving
the World.** A machine equal to the writer's except that its arm at `q`'s frame code (any of the
seven ops, a hang-up, an unknown code) stages a step and keeps the World: no list of at most one
kernel step folds to that World and is what was staged (a fold of one step moves the step
counter, `admit_steps`/`refuse_steps`). -/
theorem host_step_folds_tooth_unmoved (X : Ctx D) (w : World D) (out : Out (Step D × D))
    (q : Request Frame) (s : Step D) (st : UInt8) (p : ByteArray) :
    let m : Machine (World D) (Step D) Frame D :=
      { machine X with handle := fun v f => if f.op = q.body.op then .commit s v st p else handle X v f }
    ¬ ∃ l : List (Step D), l.length ≤ 1 ∧
      World.fold X.env w l = .ok (m.step (w, out) q).1 ∧ Honest X w l ∧
      (m.step (w, out) q).2.staged.toList =
        out.staged.toList ++ l.map (fun s => (s, World.roots X.env (m.step (w, out) q).1)) ∧
      (l ≠ [] → ∃ op, Protocol.Op.ofCode? q.body.op = some op ∧ op.effect = .write) := by
  intro m
  have hm : m.step (w, out) q =
      (w, { out with staged := out.staged.push (s, World.roots X.env w),
                     replies := out.replies.push ⟨q.conn, st, p⟩ }) := by
    simp [m, Machine.step, machine]
  rw [hm]
  rintro ⟨l, hl, hf, -, hs, -⟩
  match l, hl with
  | [], _ => simp at hs
  | [x], _ =>
    obtain ⟨w₁, hx, hn⟩ := fold_cons_ok.mp hf
    have h1 : w₁.steps = w.steps + 1 := by
      cases x with
      | turn t => exact admit_steps hx
      | refusal r => exact refuse_steps hx
    simp only [World.fold, Except.ok.injEq] at hn
    rw [hn] at h1
    omega

/-- **TOOTH (`host_step_folds`'s op conjunct): a World-moving arm at any op that does not write.** A
machine equal to the writer's except that its arm at `q`'s frame code, whose op (if any) is not a
writing one (`submit`, `cancel`), commits any step: the step theorem fails of it (an empty list is
not what was staged, a nonempty one is not a writing op's). -/
theorem host_step_folds_tooth_wrong_op (X : Ctx D) (w w' : World D) (out : Out (Step D × D))
    (q : Request Frame) (s : Step D) (st : UInt8) (p : ByteArray)
    (hop : ∀ op, Protocol.Op.ofCode? q.body.op = some op → op.effect ≠ .write) :
    let m : Machine (World D) (Step D) Frame D :=
      { machine X with handle := fun v f => if f.op = q.body.op then .commit s w' st p else handle X v f }
    ¬ ∃ l : List (Step D), l.length ≤ 1 ∧
      World.fold X.env w l = .ok (m.step (w, out) q).1 ∧ Honest X w l ∧
      (m.step (w, out) q).2.staged.toList =
        out.staged.toList ++ l.map (fun s => (s, World.roots X.env (m.step (w, out) q).1)) ∧
      (l ≠ [] → ∃ op, Protocol.Op.ofCode? q.body.op = some op ∧ op.effect = .write) := by
  intro m
  have hm : m.step (w, out) q =
      (w', { out with staged := out.staged.push (s, World.roots X.env w'),
                      replies := out.replies.push ⟨q.conn, st, p⟩ }) := by
    simp [m, Machine.step, machine]
  rw [hm]
  rintro ⟨l, -, -, -, hs, ho⟩
  match l with
  | [] => simp at hs
  | x :: _ =>
    obtain ⟨op, h1, h2⟩ := ho (List.cons_ne_nil x _)
    exact hop op h1 h2

/-- **TOOTH (`host_step_folds`'s `Honest` conjunct, every frame code): a step the kernel takes but
`judge` did not decide.** On a `Ctx` that decodes no call (any `Ctx` with its decoder emptied), a
machine equal to the writer's except that its arm at `q`'s frame code takes step `s` by
`World.step` wherever the kernel accepts it: it `Commits` to `World.step` (so `staged_rooted`, the
landed batch theorem, holds of it); at a writing frame (`submit` or `cancel`: a forged cancel record
as much as an unjudged Turn, HOST-66) where `s` is accepted, `[s]` meets EVERY
other conjunct of the step theorem (fold, staged, op), and the step theorem fails of it: no
nonempty log is `Honest` on that `Ctx`. So `Honest` alone refuses it. -/
theorem host_step_folds_tooth_unjudged (X : Ctx D) (w w' : World D) (out : Out (Step D × D))
    (q : Request Frame) (s : Step D) (st : UInt8) (p : ByteArray) (hs : World.step X.env w s = .ok w')
    (hop : ∃ op, Protocol.Op.ofCode? q.body.op = some op ∧ op.effect = .write) :
    let X' : Ctx D := { X with decodeCall := fun _ => none }
    let m : Machine (World D) (Step D) Frame D :=
      { machine X' with
        handle := fun v f =>
          if f.op = q.body.op then
            (match World.step X'.env v s with
             | .ok v' => .commit s v' st p
             | .error _ => handle X' v f)
          else handle X' v f }
    m.Commits (World.step X'.env) ∧
    (∃ l : List (Step D), l.length ≤ 1 ∧ World.fold X'.env w l = .ok (m.step (w, out) q).1 ∧
      (m.step (w, out) q).2.staged.toList =
        out.staged.toList ++ l.map (fun s => (s, World.roots X'.env (m.step (w, out) q).1)) ∧
      (l ≠ [] → ∃ op, Protocol.Op.ofCode? q.body.op = some op ∧ op.effect = .write)) ∧
    ¬ ∃ l : List (Step D), l.length ≤ 1 ∧
      World.fold X'.env w l = .ok (m.step (w, out) q).1 ∧ Honest X' w l ∧
      (m.step (w, out) q).2.staged.toList =
        out.staged.toList ++ l.map (fun s => (s, World.roots X'.env (m.step (w, out) q).1)) ∧
      (l ≠ [] → ∃ op, Protocol.Op.ofCode? q.body.op = some op ∧ op.effect = .write) := by
  intro X' m
  have hs' : World.step X'.env w s = .ok w' := hs
  have hm : m.step (w, out) q =
      (w', { out with staged := out.staged.push (s, World.roots X'.env w'),
                      replies := out.replies.push ⟨q.conn, st, p⟩ }) := by
    simp [m, Machine.step, machine, hs']
  refine ⟨?_, ⟨[s], by simp, by rw [hm]; simp only [World.fold, hs'], by rw [hm]; simp, fun _ => hop⟩, ?_⟩
  · intro v f s₁ v₁ st₁ p₁ h
    simp only [m] at h
    split at h
    · split at h
      · rename_i v' hv
        cases h
        exact hv
      · exact machine_commits X' v f s₁ v₁ st₁ p₁ h
    · exact machine_commits X' v f s₁ v₁ st₁ p₁ h
  rw [hm]
  rintro ⟨l, -, -, hh, hs, -⟩
  match l with
  | [] => simp at hs
  | .turn t :: _ =>
    obtain ⟨c, hd, -⟩ := hh
    cases hd
  | .refusal r :: _ =>
    obtain ⟨c, -, -, hd, -⟩ := hh
    cases hd

/-- **TOOTH (`host_step_folds`'s `Honest` conjunct at a decoding `Ctx`): a censoring writer.** At
any `Ctx` meeting the step theorem's premise (the deployed one: `deployed_canonical`), take a frame
carrying call `c` that `judge` would ADMIT on `w`, and a judged-refusal record `r` of that very event (no cancel field, `hk`: a record carrying one is
a member’s cancel, which `recordedBy` re-judges by `cancel`, and whose forgery is `audit_cancel_forged`’s tooth)
which `World.refuse` accepts on `w`. A machine equal to the writer's except that its arm at the
frame's code records `r` wherever `World.refuse` accepts it `Commits` to `World.step`; at a `submit`
frame `[.refusal r]` meets every other conjunct of the step theorem, and the step theorem fails of
it: the one step it staged is a refusal `judge` did not record. So `Honest` alone refuses it. The
premises' joint satisfiability (a refusal record of an admissible call's event that `World.refuse`
accepts on the same World) is not witnessed in Lean. -/
theorem host_step_folds_tooth_censor (X : Ctx D) (hX : ∀ b c, X.decodeCall b = some c → X.callBytes c = b)
    (w w₁ w' : World D) (out : Out (Step D × D)) (q : Request Frame) (c : Call D) (t : Turn D)
    (r : Refused D) (st : UInt8) (p : ByteArray)
    (hc : X.decodeCall q.body.payload = some c) (hj : judge X w c = .admitted t w₁)
    (he : r.event = X.callBytes c) (hk : r.cancel.size = 0) (hr : World.refuse X.env w r = .ok w')
    (hop : Protocol.Op.ofCode? q.body.op = some .submit) :
    let m : Machine (World D) (Step D) Frame D :=
      { machine X with
        handle := fun v f =>
          if f.op = q.body.op then
            (match World.refuse X.env v r with
             | .ok v' => .commit (.refusal r) v' st p
             | .error _ => handle X v f)
          else handle X v f }
    m.Commits (World.step X.env) ∧
    (∃ l : List (Step D), l.length ≤ 1 ∧ World.fold X.env w l = .ok (m.step (w, out) q).1 ∧
      (m.step (w, out) q).2.staged.toList =
        out.staged.toList ++ l.map (fun s => (s, World.roots X.env (m.step (w, out) q).1)) ∧
      (l ≠ [] → ∃ op, Protocol.Op.ofCode? q.body.op = some op ∧ op.effect = .write)) ∧
    ¬ ∃ l : List (Step D), l.length ≤ 1 ∧
      World.fold X.env w l = .ok (m.step (w, out) q).1 ∧ Honest X w l ∧
      (m.step (w, out) q).2.staged.toList =
        out.staged.toList ++ l.map (fun s => (s, World.roots X.env (m.step (w, out) q).1)) ∧
      (l ≠ [] → ∃ op, Protocol.Op.ofCode? q.body.op = some op ∧ op.effect = .write) := by
  intro m
  have hm : m.step (w, out) q =
      (w', { out with staged := out.staged.push (.refusal r, World.roots X.env w'),
                      replies := out.replies.push ⟨q.conn, st, p⟩ }) := by
    simp [m, Machine.step, machine, hr]
  have hr' : World.step X.env w (.refusal r) = .ok w' := hr
  refine ⟨?_, ⟨[.refusal r], by simp, by rw [hm]; simp only [World.fold, hr'], by rw [hm]; simp,
    fun _ => ⟨_, hop, rfl⟩⟩, ?_⟩
  · intro v f s₁ v₁ st₁ p₁ h
    simp only [m] at h
    split at h
    · split at h
      · rename_i v' hv
        cases h
        exact hv
      · exact machine_commits X v f s₁ v₁ st₁ p₁ h
    · exact machine_commits X v f s₁ v₁ st₁ p₁ h
  rw [hm]
  rintro ⟨l, hl, -, hh, hs, -⟩
  match l, hl with
  | [], _ => simp at hs
  | [x], _ =>
    simp at hs
    subst hs
    obtain ⟨c', v, u, hd, hjr, -⟩ := hh
    rw [he, hX _ _ hc, hc] at hd
    cases hd
    rw [recordedBy, if_pos hk, hj] at hjr
    cases hjr

end Nanodregg.Host

namespace Nanodregg.Host.Deployed

open Nanodregg.Kernel Nanodregg.Kernel.Receive Nanodregg.Codec

/-- The deployed call codec is canonical: the generic theorems' one premise. -/
private theorem deployed_canonical : ∀ b c, X.decodeCall b = some c → X.callBytes c = b :=
  fun _ _ h => (Codec.Deployed.eq_callBytes_of_decodeCall _ h).2.symm

/-- **`Host ⊑ Kernel` at the deployed instance, a batch**: from a `Kept` World, the World the writer
keeps after any batch is `Kept`, is the fold of the `Honest` log it staged, and `host follow`'s
`absorb` of that log's page events reaches it, appending exactly the staged pairs. No premise
beyond `Kept`, which every start makes (`host_start_kept`) and every reopen returns
(`host_reopen_folds`). -/
theorem host_run_kept {w : World D} (hk : Kept w) (qs : List (Request Frame)) :
    Kept ((machine X).admitBatch w qs).1 ∧
      World.fold X.env w (((machine X).admitBatch w qs).2.staged.toList.map Prod.fst) =
        .ok ((machine X).admitBatch w qs).1 ∧
      Honest X w (((machine X).admitBatch w qs).2.staged.toList.map Prod.fst) ∧
      Protocol.Command.absorb X w #[]
          (((machine X).admitBatch w qs).2.staged.toList.map (Page.stepEvent ∘ Prod.fst)) =
        .ok (((machine X).admitBatch w qs).1, ((machine X).admitBatch w qs).2.staged) := by
  obtain ⟨l, -, hf, hh, hs⟩ := host_run_folds X deployed_canonical qs w {}
  have hs' : ((machine X).admitBatch w qs).2.staged.toList.map Prod.fst = l := by
    simpa using hs
  rw [← hs'] at hf hh
  exact ⟨kept_fold hk hf, hf, hh, host_run_absorbed X deployed_canonical w hk.rowsCanon qs⟩

/-- **The deployed follower keeps exactly the honest logs** (HOST-75): at the deployed `Ctx`,
`host follow`'s `absorb` accepts a list of page events exactly when they are the page events of an
honest rooted run, and what it keeps is that run; so it passes the kernel's `audit` (`audit_ok`),
and every kernel theorem stated over `audit` (`audit_rooted`, `audit_object_head`,
`audit_package_fixed`, …) holds of the log `host follow` persists. -/
theorem follow_absorbed_audits {w w' : World D} {acc ts : Array (Step D × D)} {evs : List ByteArray}
    (h : Protocol.Command.absorb X w acc evs = .ok (w', ts)) :
    ∃ ps : List (Step D × D), ts = acc ++ ps.toArray ∧ evs = ps.map (Page.stepEvent ∘ Prod.fst) ∧
      audit X w (ps.map Prod.fst) = .ok w' := by
  obtain ⟨ps, hts, hr, hh, hevs⟩ := absorb_sound deployed_canonical h
  exact ⟨ps, hts, hevs, audit_ok.mpr ⟨RootedFold.fold hr, hh⟩⟩

/-- **The three starts are `Kept`.** The World `host genesis` makes (`Receive.genesis`), the one
genesis `host join` accepts (`Protocol.Invite.accept`: the genesis World of the signed inputs), and the one
`host import` carries (`Carry.importWorld`, KERNEL's carry): none is a step, each is a fresh World,
and each meets the relation's invariant. The import arm includes a carried join under its signed
origin; Host.Cli.join_carried_trusted links the actual join effect to that independent pin. -/
theorem host_start_kept :
    (∀ {name nonce : ByteArray} {allowance : Nat} {founders : List (ByteArray × D)} {w : World D},
      Receive.genesis X name nonce allowance founders = .ok w → Kept w) ∧
    (∀ {trusted inv : ByteArray} {i : Protocol.Invite.Invitation D} {w : World D},
      Protocol.Invite.accept X trusted inv = .ok (i, w) → Kept w) ∧
    (∀ {name nonce : ByteArray} {pin : Carry.Pin D} {f : ByteArray} {r : Carry.Read D} {w : World D},
      Carry.importWorld X Codec.Deployed.digestCodec name nonce pin f = .ok (w, r) → Kept w) := by
  have hg : ∀ {name nonce : ByteArray} {allowance : Nat} {founders : List (ByteArray × D)} {w : World D},
      Receive.genesis X name nonce allowance founders = .ok w → Kept w := by
    intro name nonce allowance founders w h
    obtain ⟨hf, rfl⟩ := Receive.genesis_ok.mp h
    exact kept_of_fits (genesisWorld_codecFits hf)
  refine ⟨hg, ?_, fun h => kept_of_fits (importWorld_codecFits h)⟩
  intro trusted inv i w h
  obtain ⟨_, _, _, _, _, hgen⟩ := Protocol.Invite.accept_genesis h
  exact hg hgen

/-- A run of deployed reopen steps over records is the fold of the steps those records decode to. -/
private theorem foldlM_foldStep_folds :
    ∀ {w w' : World D} {rs : List ByteArray}, rs.foldlM foldStep w = .ok w' →
      ∃ pss : List (List (Step D × D)),
        rs.mapM (Record.codec Codec.Deployed.digestCodec).decode = .ok pss ∧
        World.fold X.env w (pss.flatMap (·.map Prod.fst)) = .ok w'
  | w, w', [], h => by
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨[], rfl, rfl⟩
  | w, w', r :: rs, h => by
    simp only [List.foldlM_cons, bind, Except.bind] at h
    split at h
    · cases h
    · rename_i w₁ h₁
      obtain ⟨ps, hd, hr⟩ := Record.step_rooted h₁
      obtain ⟨pss, h₂, hf⟩ := foldlM_foldStep_folds h
      refine ⟨ps :: pss, by simp [List.mapM_cons, hd, h₂, bind, Except.bind, pure, Except.pure], ?_⟩
      simp only [List.flatMap_cons]
      exact fold_append.mpr ⟨w₁, RootedFold.fold hr, hf⟩

/-- **`Host ⊑ Kernel` at the crash edge.** Whatever base file and segment bytes the deployed open
reads, the World it returns is the fold, from the `Kept` World of the base it read, of exactly the
steps its segment's records decode to, those records being exactly the segment's bytes from the
base's offset to the open's position; and that World is `Kept`. With `host_run_kept`, every World
the writer holds, across any number of crashes, is a fold from a base. -/
theorem host_reopen_folds {keys : Keys} {file H I S : ByteArray} {o : Opening (World D)}
    (h : Id.run (openWith keys c world recorder.mark originChain foldStep file H S.size I.size
      (segReader I) (segReader S)) = .ok o) :
    ∃ (b : Base (World D)) (n : Nat) (d : ByteArray) (rs : List ByteArray) (pss : List (List (Step D × D))),
      Base.read keys c world file = .ok (b, n, d) ∧ Kept b.world ∧
      (S.extract b.offset S.size).extract 0 (o.pos.offset - b.offset) = Log.encodeAll keys.segment b.tag.bytes rs ∧
      rs.mapM (Record.codec Codec.Deployed.digestCodec).decode = .ok pss ∧
      World.fold X.env b.world (pss.flatMap (·.map Prod.fst)) = .ok o.opened.world ∧ Kept o.opened.world := by
  obtain ⟨b, n, d, rs, hb, hf, -, -, -, he⟩ :=
    openWith_world keys c world recorder.mark originChain foldStep file H I S h
  obtain ⟨b', n', d', rs', hb', hk, -, hk'⟩ := openWith_kept h
  rw [hb] at hb'
  cases hb'
  obtain ⟨pss, h₂, hfold⟩ := foldlM_foldStep_folds hf
  exact ⟨b, n, d, rs, pss, hb, hk, he, h₂, hfold, hk'⟩

/-- **TOOTH (`Kept`, the relation's invariant half, is not every World).** Any World with its step
counter set to 2^64 is not `Kept`: the start and reopen theorems say something. -/
theorem kept_refutable (w : World D) : ¬ Kept { w with steps := 2 ^ 64 } := by
  intro h
  exact absurd h.stepsLt (by simp)

end Nanodregg.Host.Deployed
