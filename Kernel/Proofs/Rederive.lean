/-
# Kernel.Proofs.Rederive — the one re-deriver accepts exactly the honest folded logs

`Receive.rederive` is the follower's re-derivation of one logged event (`host follow` runs it,
`Protocol.Command.absorbStep`; the runtime auditors run it per step, `rederiveStep`). `Honest` is
what it means of a log: every step is what its own signed event is decided to on the World before
it, a Turn by `receive`, a refusal by its re-judge (`recordedBy`). The two meet here:

* `rederive_step`, `rederive_honest_of_event`: a re-derived event is a step of the kernel's, and an
  honest one; `rederive_sound`: with the call codec canonical, the event IS that step's
  (`Step.event`, one event per step).
* `rederive_honest`: from a World whose rows trie is canonical, every honest step's event
  re-derives exactly that step to exactly the World the kernel's step reaches.
* `rederiveLog_sound`, `rederiveLog_iff`: a log re-derives exactly when it folds and is honest.

So every theorem stated over `World.fold … = .ok w' ∧ Honest …` is a theorem about every log the
follower takes (`Host.Proofs.Refine.absorb_iff` over the page bytes).
-/
import Kernel.Receive.Rederive
import Kernel.Proofs.Fold
import Kernel.Proofs.StaleOnly
import Kernel.Proofs.Receive

namespace Nanodregg.Kernel.Receive

open Nanodregg.Kernel

variable {D : Type} [Ord D] [DecidableEq D]

/-! ## One verify per judgement (PERF-1)

`judge` authenticates a refused call by `authenticatedBy … v.verified`: when `submit`'s verdict was
reached past its signature check, that check's passing is carried, not re-verified. `submit_verified`
says the carried bit is the same verify; `judge_eq` says the decision is the two-verify one;
`verified_eq_false_iff` names exactly the verdicts that verify again (none of them past a passing
verify); `authenticatedBy_verify_irrel` says a carried decision never reads `verify`. -/

omit [Ord D] [DecidableEq D] in
private theorem checkSignature_error {X : Ctx D} {c : Call D} {e : Refusal D}
    (h : checkSignature X c = .error e) : e = .badSignature := by
  unfold checkSignature req at h
  split at h <;> cases h
  rfl

/-- A `receive` that neither refused `wrongWorld` nor `badSignature` was reached through the
signature check passing. -/
theorem receive_checkSignature {X : Ctx D} {w : World D} {c : Call D}
    (hw : receive X w c ≠ .error .wrongWorld) (hb : receive X w c ≠ .error .badSignature) :
    checkSignature X c = .ok () := by
  cases hs : checkSignature X c with
  | ok u => rfl
  | error e =>
    obtain rfl := checkSignature_error hs
    exfalso
    by_cases hwo : c.unsigned.world = w.origin
    · exact hb (by simp [receive, receiveWith, req, hwo, hs, bind, Except.bind])
    · exact hw (by simp [receive, req, hwo, bind, Except.bind])

/-- **The carried bit is the same verify**: a verdict `submit` reached with `verified` set was
reached through `checkSignature` passing, the very check `authenticated` would make. -/
theorem submit_verified {X : Ctx D} {w : World D} {c : Call D} {v : Verdict D}
    (h : submit X w c = .error v) (hv : v.verified = true) : checkSignature X c = .ok () := by
  unfold submit at h
  split at h
  · cases h; simp [Verdict.verified] at hv
  · split at h
    · cases h; simp [Verdict.verified] at hv
    · -- past `signedBy`, the one verify passed; a `signedBy` refusal with `verified` set came after it
      cases hs : checkSignature X c with
      | ok u => rfl
      | error e =>
        obtain rfl := checkSignature_error hs
        exfalso
        have hsb : signedBy X w c false = .error (if c.unsigned.world = w.origin then .badSignature else .wrongWorld) := by
          by_cases hwo : c.unsigned.world = w.origin
          · simp [signedBy, checkSignatureBy, req, hwo, hs, bind, Except.bind]
          · simp [signedBy, req, hwo, bind, Except.bind]
        rw [hsb] at h
        by_cases hwo : c.unsigned.world = w.origin
        · simp only [hwo, if_true] at h; cases h; simp [Verdict.verified] at hv
        · simp only [hwo, if_false] at h; cases h; simp [Verdict.verified] at hv

/-- The authentication `judge` makes is `authenticated`, for every verdict `submit` gives. -/
theorem authenticatedBy_verified {X : Ctx D} {w : World D} {c : Call D} {v : Verdict D}
    (h : submit X w c = .error v) : authenticatedBy X w c v.verified = authenticated X w c := by
  cases hv : v.verified
  · rfl
  · simp only [authenticated, authenticatedBy, signedBy, checkSignatureBy, if_true, Bool.false_eq_true,
      if_false, submit_verified h hv]

/-- **`judge` decides as the two-verify judge did** (PERF-1): with `authenticated` in place of the
carried check, the same Outcome for every call. -/
theorem judge_eq (X : Ctx D) (w : World D) (c : Call D) :
    judge X w c = judgeBy X w c fun _ => authenticated X w c := by
  unfold judge judgeBy
  cases hs : submit X w c with
  | ok p => rfl
  | error v => simp only [authenticatedBy_verified hs]

omit [Ord D] [DecidableEq D] in
/-- TOOTH (the carry is not vacuous): `judge` verifies again for exactly these verdicts, all decided
before `submit`'s verify or by it; every other refusal and every `World.admit` rejection (PERF-1's
`stale` among them) carries it. A `verified` that were always `false` would satisfy `judge_eq` and
save nothing; this refutes it. -/
theorem verified_eq_false_iff (v : Verdict D) :
    v.verified = false ↔ v = .refused .wrongWorld ∨ v = .refused .badSignature ∨
      (∃ h, v = .rejected (.replayed h)) ∨ ∃ k, v = .rejected (.refusedFinal k) := by
  cases v with
  | refused r => cases r <;> simp [Verdict.verified]
  | rejected r => cases r <;> simp [Verdict.verified]

/-- TOOTH (the carried check verifies nothing): with the bit carried, the authentication is the same
under ANY `verify`. -/
theorem authenticatedBy_verify_irrel (X : Ctx D) (f : ByteArray → ByteArray → ByteArray → Bool)
    (w : World D) (c : Call D) :
    authenticatedBy { X with verify := f } w c true = authenticatedBy X w c true := rfl

/-- What `cancel` recording means (KERNEL-60): its authority held on this World, the verdict is
`cancelled`, the record is `cancelOf` the call and the signature, and `World.refuse` took it. -/
theorem cancel_recorded {X : Ctx D} {w w' : World D} {c : Call D} {sig : ByteArray} {v : Verdict D}
    {r : Refused D} (h : cancel X w c sig = .recorded v r w') :
    cancelAuth X w c sig = .ok () ∧ v = .refused .cancelled ∧ r = cancelOf X c sig ∧
      World.refuse X.env w r = .ok w' := by
  unfold cancel at h
  split at h
  · cases h
  · rename_i ha
    split at h
    · rename_i w'' hr
      simp only [Outcome.recorded.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨ha, rfl, rfl, hr⟩
    · cases h

/-- What `judge` recording a refusal means: the call was refused with `v`, it was authenticated, the
record is `refusedOf` the call and the verdict, and `World.refuse` took it. -/
theorem judge_recorded {X : Ctx D} {w w' : World D} {c : Call D} {v : Verdict D} {r : Refused D}
    (h : judge X w c = .recorded v r w') :
    submit X w c = .error v ∧ authenticated X w c = true ∧ r = refusedOf X c v ∧
      World.refuse X.env w r = .ok w' := by
  rw [judge_eq] at h
  unfold judgeBy at h
  split at h
  · cases h
  · rename_i v' hs
    split at h
    · cases h
    · split at h
      · rename_i ha
        split at h
        · rename_i w'' hr
          simp only [Outcome.recorded.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          exact ⟨hs, ha, rfl, hr⟩
        · cases h
        · cases h
        · cases h
      · cases h

/-! ## Stale is never recorded (KERNEL-54) -/

omit [Ord D] [DecidableEq D] in
/-- Only a stale verdict carries the stale code. -/
private theorem code_ne_staleCode {v : Verdict D} (hv : v.isStale = false) : v.code ≠ staleCode := by
  cases v with
  | refused r =>
    have := List.idxOf_le_length (l := refusalNames) (a := r.name)
    simp only [Verdict.code, staleCode]
    have h7 : rejectNames.idxOf "stale" = 7 := by decide
    omega
  | rejected r =>
    simp only [Verdict.code, staleCode, ne_eq, Nat.add_left_cancel_iff]
    cases r <;> first | (simp only [Reject.name]; decide) | simp [Verdict.isStale] at hv

/-- **`judge` declines a stale verdict**: a call `submit` refuses `stale` is never recorded and spends
no budget, whoever signed it. -/
theorem judge_stale_declined {X : Ctx D} {w : World D} {c : Call D} {v : Verdict D}
    (hs : submit X w c = .error v) (hv : v.isStale = true) : judge X w c = .declined v := by
  simp [judge, judgeBy, hs, hv]

/-! ## The pins before the receivers (KERNEL-66) -/

/-- **A stale call is declined before any receiver runs** (KERNEL-66). A call that is neither journaled
nor recorded, that is `authenticated` (it names this World and its member holds the signing key), and
one of whose pins disagrees with the Host's World (`checkPins` fails; by `checkPins_ok_iff` a cell pin,
a row pin or a range read that is not what the World holds) is refused `stale` by `submit` and declined
by `judge`: never recorded, never charged to its member's budget, never final, whatever any receiver
or law would say of the World as it is now (no premise names `receive` or `deriveTurn`). -/
theorem stale_declined_before_receive {X : Ctx D} {w : World D} {c : Call D}
    (hj : w.journalAt X.env (txIdOf X c) = none) (hr : refusedAnswer X w c = none)
    (ha : authenticated X w c = true)
    (hm : checkPins X.env w c.unsigned.pins c.unsigned.rowPins c.unsigned.ranges ≠ .ok ()) :
    ∃ y, checkPins X.env w c.unsigned.pins c.unsigned.rowPins c.unsigned.ranges = .error (.stale y) ∧
      submit X w c = .error (.rejected (.stale y)) ∧ judge X w c = .declined (.rejected (.stale y)) := by
  have hsb : signedBy X w c false = .ok () := by
    unfold authenticated authenticatedBy at ha
    split at ha
    · assumption
    · cases ha
  cases hp : checkPins X.env w c.unsigned.pins c.unsigned.rowPins c.unsigned.ranges with
  | ok u => exact absurd hp hm
  | error e =>
    obtain ⟨y, rfl⟩ := checkPins_error_stale hp
    have hs : submit X w c = .error (.rejected (.stale y)) := by
      unfold submit
      rw [hj, hr, hsb]
      simp only [hp]
    exact ⟨y, rfl, hs, judge_stale_declined hs rfl⟩

/-- **No receiver runs on a stale call** (KERNEL-66): its verdict is the same under ANY program, so no
method's ticks (up to `Bounds.treeTicksMax` per call) and no law's judgement are spent on it: an
authenticated call with garbage pins costs the Host its one verify, its key read and its pin lookups. -/
theorem receive_not_run_on_stale {X : Ctx D} {w : World D} {c : Call D} {y : D}
    (hj : w.journalAt X.env (txIdOf X c) = none) (hr : refusedAnswer X w c = none)
    (ha : authenticated X w c = true)
    (hp : checkPins X.env w c.unsigned.pins c.unsigned.rowPins c.unsigned.ranges = .error (.stale y))
    (P : Program D) : submit { X with program := P } w c = .error (.rejected (.stale y)) := by
  have hsb : signedBy X w c false = .ok () := by
    unfold authenticated authenticatedBy at ha
    split at ha
    · assumption
    · cases ha
  -- `signedBy` reads the World, the verifier, the call's bytes and `rotate` (no program)
  have hsb' : signedBy { X with program := P } w c false = .ok () := hsb
  have hj' : w.journalAt ({ X with program := P } : Ctx D).env (txIdOf { X with program := P } c) = none := hj
  have hr' : refusedAnswer { X with program := P } w c = none := hr
  unfold submit
  rw [hj', hr', hsb']
  simp only [hp]

/-- **Comparing the pins first only renames** (KERNEL-66): a call whose pins `checkPins` refuses is
one no order of the checks would admit: whatever `receive` derives from it, `World.admit` takes no
Turn of it (a cell pin is a touch, a row pin a row touch, a range read the Turn's own:
`admit_pins`, `admit_row_pins`, `admit_range_pins`). So the pins coming first changes which refusal
a stale call gets (and that it is declined, not recorded), never whether a call lands. -/
theorem checkPins_error_never_admitted {X : Ctx D} {w : World D} {c : Call D} {r : Reject D}
    (hc : w.RowsCanon X.env)
    (hp : checkPins X.env w c.unsigned.pins c.unsigned.rowPins c.unsigned.ranges = .error r)
    {t : Turn D} (ht : receive X w c = .ok t) : ∀ w', World.admit X.env w t ≠ .ok w' := by
  intro w' ha
  have hd := receive_derived ht
  obtain ⟨-, d, _k, -, hs⟩ := receiveWith_sealed (receive_ok_with ht).2
  obtain ⟨rts, hrts, hrows, hranges⟩ := sealTurn_rows hs
  have hok : checkPins X.env w c.unsigned.pins c.unsigned.rowPins c.unsigned.ranges = .ok () := by
    refine checkPins_ok_iff.mpr ⟨fun p hp' => ?_, fun p hp' key hk => ?_,
      fun q hq c' s lim cap width rt l hh hl => ?_⟩
    · rw [← hd.pinned] at hp'
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hp'
      exact admit_pins ha x hx
    · obtain ⟨x, hx, hxs, hxe⟩ := rowTouchesOf_pins hrts p hp'
      rw [← hrows] at hx
      exact admit_row_pins hc ha x hx key p.2 (hxs.trans hk) hxe
    · rw [← hranges] at hq
      obtain ⟨c₁, s₁, lim₁, cap₁, width₁, rt₁, l₁, hh₁, hl₁, hp₁⟩ := admit_range_pins ha q hq
      rw [hh] at hh₁
      simp only [Option.some.injEq, Prod.mk.injEq] at hh₁
      obtain ⟨-, -, -, -, rfl, -⟩ := hh₁
      rw [hl] at hl₁
      cases hl₁
      exact hp₁
  rw [hp] at hok
  cases hok

/-- **What `judge` records is never stale.** -/
theorem judge_recorded_not_stale {X : Ctx D} {w w' : World D} {c : Call D} {v : Verdict D} {r : Refused D}
    (h : judge X w c = .recorded v r w') : v.isStale = false ∧ r.code ≠ staleCode := by
  have hs := (judge_recorded h).1
  have hv : v.isStale = false := by
    cases hst : v.isStale
    · rfl
    · rw [judge_stale_declined hs hst] at h; cases h
  obtain rfl := (judge_recorded h).2.2.1
  exact ⟨hv, code_ne_staleCode hv⟩

/-! ## A step's event, and its re-judge -/

omit [Ord D] [DecidableEq D] in
theorem event_unsigned {r : Refused D} (hk : r.cancel.size = 0) :
    (Step.refusal r).event = .refusal r.event := by
  simp [Step.event, hk]

omit [Ord D] [DecidableEq D] in
theorem event_cancel {r : Refused D} (hk : r.cancel.size ≠ 0) :
    (Step.refusal r).event = .cancel r.cancel r.event := by
  simp [Step.event, hk]

/-- A record with no cancel signature is re-judged by `judge`. -/
theorem recordedBy_unsigned {X : Ctx D} {w : World D} {c : Call D} {r : Refused D}
    (hk : r.cancel.size = 0) : recordedBy X w c r = judge X w c := by
  unfold recordedBy
  rw [event_unsigned hk]

/-- A record carrying a cancel signature is re-judged by `cancel` under it. -/
theorem recordedBy_cancel {X : Ctx D} {w : World D} {c : Call D} {r : Refused D}
    (hk : r.cancel.size ≠ 0) : recordedBy X w c r = cancel X w c r.cancel := by
  unfold recordedBy
  rw [event_cancel hk]

/-- **A judged refusal is its own re-judge.** What `judge` records carries no cancel field
(`refusedOf` is `recordOf … ByteArray.empty`), so `recordedBy` of that record IS `judge`: a judged
refusal is re-judged by `judge`, never as a member's cancel. -/
theorem recordedBy_of_judge {X : Ctx D} {w w' : World D} {c : Call D} {v : Verdict D} {r : Refused D}
    (h : judge X w c = .recorded v r w') : recordedBy X w c r = .recorded v r w' := by
  obtain ⟨-, -, hr, -⟩ := judge_recorded h
  have hk : r.cancel.size = 0 := by rw [hr]; rfl
  rw [recordedBy_unsigned hk]
  exact h

/-- The signature length a cancel's authority admits: non-empty, at most `cancelBytesMax`. -/
theorem cancelAuth_size {X : Ctx D} {w : World D} {c : Call D} {sig : ByteArray}
    (h : cancelAuth X w c sig = .ok ()) : 0 < sig.size ∧ sig.size ≤ Kernel.Bounds.cancelBytesMax := by
  unfold cancelAuth at h
  simp only [except_bind_ok] at h
  obtain ⟨⟨⟩, -, ⟨⟩, h2, -⟩ := h
  rw [req_ok] at h2
  simpa using h2

/-- A cancel `cancel` records is what its record's re-judge records: its signature is non-empty
(`cancelAuth`), so `recordedBy` re-decides it by `cancel` with that signature. -/
theorem recordedBy_of_cancel {X : Ctx D} {w w' : World D} {c : Call D} {sig : ByteArray}
    {v : Verdict D} {r : Refused D} (h : cancel X w c sig = .recorded v r w') :
    recordedBy X w c r = .recorded v r w' := by
  obtain ⟨ha, -, hr, -⟩ := cancel_recorded h
  subst hr
  have hk : (cancelOf X c sig).cancel.size ≠ 0 := Nat.pos_iff_ne_zero.mp (cancelAuth_size ha).1
  rw [recordedBy_cancel hk]
  exact h

/-- **What a log's re-judge records**: `World.refuse` took it, and its code is not the stale code
(`judge`'s by `judge_recorded_not_stale`; a cancel's is `cancelled`'s). -/
theorem recordedBy_recorded {X : Ctx D} {w w' : World D} {c : Call D} {r r' : Refused D} {v : Verdict D}
    (h : recordedBy X w c r = .recorded v r' w') :
    World.refuse X.env w r' = .ok w' ∧ r'.code ≠ staleCode := by
  by_cases hk : r.cancel.size = 0
  · rw [recordedBy_unsigned hk] at h
    exact ⟨(judge_recorded h).2.2.2, (judge_recorded_not_stale h).2⟩
  · rw [recordedBy_cancel hk] at h
    obtain ⟨-, rfl, rfl, hr⟩ := cancel_recorded h
    exact ⟨hr, code_ne_staleCode (D := D) (v := .refused .cancelled) rfl⟩

/-! ## Honest logs -/

/-- A log every step of which is exactly what its own event is judged to, on the World before it: a
Turn is what `receive` derives from its event, a recorded refusal is what its re-judge
(`recordedBy`: `judge`, or `cancel` for a cancel) records for its event. A log in which the writer
decided nothing. -/
def Honest (X : Ctx D) : World D → List (Step D) → Prop
  | _, [] => True
  | w, .turn t :: rest => ∃ c, X.decodeCall t.event = some c ∧ receive X w c = .ok t ∧
      ∀ w', World.admit X.env w t = .ok w' → Honest X w' rest
  | w, .refusal r :: rest => ∃ c v w₁, X.decodeCall r.event = some c ∧ recordedBy X w c r = .recorded v r w₁ ∧
      ∀ w', World.refuse X.env w r = .ok w' → Honest X w' rest

/-- **An honest folded log, one step at a time**: its first step is a kernel step that is honest
(`Honest X w [s]`), and the rest is an honest folded log from where it lands. The form every
induction over `World.fold … ∧ Honest …` takes. -/
theorem fold_honest_cons {X : Ctx D} {w w' : World D} {s : Step D} {rest : List (Step D)}
    (hf : World.fold X.env w (s :: rest) = .ok w') (hh : Honest X w (s :: rest)) :
    ∃ w₁, World.step X.env w s = .ok w₁ ∧ Honest X w [s] ∧ World.fold X.env w₁ rest = .ok w' ∧
      Honest X w₁ rest := by
  obtain ⟨w₁, hs, hr⟩ := fold_cons_ok.mp hf
  refine ⟨w₁, hs, ?_, hr, ?_⟩
  · cases s with
    | turn t => obtain ⟨c, hd, hrc, -⟩ := hh; exact ⟨c, hd, hrc, fun _ _ => trivial⟩
    | refusal r => obtain ⟨c, v, u, hd, hj, -⟩ := hh; exact ⟨c, v, u, hd, hj, fun _ _ => trivial⟩
  · cases s with
    | turn t => obtain ⟨c, hd, hrc, k⟩ := hh; exact k w₁ hs
    | refusal r => obtain ⟨c, v, u, hd, hj, k⟩ := hh; exact k w₁ hs

/-- An honest step followed by an honest log from where it lands is an honest log. -/
theorem honest_cons {X : Ctx D} {w w₁ : World D} {s : Step D} {rest : List (Step D)}
    (hs : World.step X.env w s = .ok w₁) (h₁ : Honest X w [s]) (hr : Honest X w₁ rest) :
    Honest X w (s :: rest) := by
  cases s with
  | turn t =>
    obtain ⟨c, hd, hrc, -⟩ := h₁
    refine ⟨c, hd, hrc, fun w' ha => ?_⟩
    have hs' : World.admit X.env w t = .ok w₁ := hs
    rw [hs'] at ha; cases ha; exact hr
  | refusal r =>
    obtain ⟨c, v, u, hd, hj, -⟩ := h₁
    refine ⟨c, v, u, hd, hj, fun w' ha => ?_⟩
    have hs' : World.refuse X.env w r = .ok w₁ := hs
    rw [hs'] at ha; cases ha; exact hr

/-- An `Honest` log continued by an `Honest` log from where it ends is `Honest`. -/
theorem honest_append {X : Ctx D} :
    ∀ {w w₁ : World D} {l₁ l₂ : List (Step D)}, Honest X w l₁ → World.fold X.env w l₁ = .ok w₁ →
      Honest X w₁ l₂ → Honest X w (l₁ ++ l₂)
  | w, w₁, [], l₂, _, hf, h₂ => by
    simp only [World.fold, Except.ok.injEq] at hf
    subst hf
    exact h₂
  | w, w₁, s :: rest, l₂, h₁, hf, h₂ => by
    obtain ⟨v, hs, hh, hfr, hrest⟩ := fold_honest_cons hf h₁
    exact honest_cons hs hh (honest_append hrest hfr h₂)

/-- An `Honest` log's prefix is `Honest`, and so is its suffix from where the prefix's fold lands. -/
theorem honest_split {X : Ctx D} :
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

/-! ## The re-deriver -/

/-- A Turn `receive` derives from `c` on `w` and `World.admit` takes is what `submit` returns, on a
World whose rows trie is canonical: the admission's journal check is `submit`'s first two arms, and
a call whose pins `checkPins` refuses is admitted by no order of the checks
(`checkPins_error_never_admitted`). -/
theorem submit_of_admit {X : Ctx D} {w w' : World D} {c : Call D} {t : Turn D}
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

/-- **What `rederive` takes an event to**, by its kind: a Turn event to `submit`'s Turn, a refusal
event to the record `judge` makes, a cancel event to the record `cancel` makes under its signature;
in each the event's call decodes. -/
theorem rederive_ok {X : Ctx D} {w w' : World D} {ev : Event} {s : Step D}
    (h : rederive X w ev = .ok (s, w')) :
    (∃ b c t, ev = .turn b ∧ X.decodeCall b = some c ∧ submit X w c = .ok (t, w') ∧ s = .turn t) ∨
    (∃ b c v r, ev = .refusal b ∧ X.decodeCall b = some c ∧ judge X w c = .recorded v r w' ∧
      s = .refusal r) ∨
    (∃ sig b c v r, ev = .cancel sig b ∧ X.decodeCall b = some c ∧ cancel X w c sig = .recorded v r w' ∧
      s = .refusal r) := by
  cases ev with
  | turn b =>
    simp only [rederive] at h
    cases hc : X.decodeCall b with
    | none => simp [hc] at h
    | some c =>
      cases hs : submit X w c with
      | ok p =>
        obtain ⟨t, w₁⟩ := p
        simp only [hc, hs, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact .inl ⟨b, c, t, rfl, hc, hs, rfl⟩
      | error v => cases v <;> simp [hc, hs] at h
  | refusal b =>
    simp only [rederive] at h
    cases hc : X.decodeCall b with
    | none => simp [hc] at h
    | some c =>
      cases hj : judge X w c with
      | recorded v r w₁ =>
        simp only [hc, hj, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact .inr (.inl ⟨b, c, v, r, rfl, hc, hj, rfl⟩)
      | admitted t w₁ => simp [hc, hj] at h
      | declined v => simp [hc, hj] at h
  | cancel sig b =>
    simp only [rederive] at h
    cases hc : X.decodeCall b with
    | none => simp [hc] at h
    | some c =>
      cases hk : cancel X w c sig with
      | recorded v r w₁ =>
        simp only [hc, hk, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact .inr (.inr ⟨sig, b, c, v, r, rfl, hc, hk, rfl⟩)
      | admitted t w₁ => simp [hc, hk] at h
      | declined v => simp [hc, hk] at h

/-- **A re-derived event is a step of the kernel's**: the World it reaches is `World.step`'s. -/
theorem rederive_step {X : Ctx D} {w w' : World D} {ev : Event} {s : Step D}
    (h : rederive X w ev = .ok (s, w')) : World.step X.env w s = .ok w' := by
  rcases rederive_ok h with ⟨b, c, t, -, -, hs, rfl⟩ | ⟨b, c, v, r, -, -, hj, rfl⟩ |
      ⟨sig, b, c, v, r, -, -, hk, rfl⟩
  · exact (submit_ok hs).2.2
  · exact (judge_recorded hj).2.2.2
  · exact (cancel_recorded hk).2.2.2

/-- **A step re-derived from its own event is honest** (no codec premise: the event's bytes are the
step's own): a step of the kernel's, and an honest one before any honest continuation. -/
theorem rederive_honest_of_event {X : Ctx D} {w w' : World D} {s : Step D}
    (h : rederive X w s.event = .ok (s, w')) :
    World.step X.env w s = .ok w' ∧ ∀ rest, Honest X w' rest → Honest X w (s :: rest) := by
  have hws := rederive_step h
  refine ⟨hws, fun rest hr => honest_cons hws ?_ hr⟩
  rcases rederive_ok h with ⟨b, c, t, he, hc, hs, rfl⟩ | ⟨b, c, v, r, he, hc, hj, hsr⟩ |
      ⟨sig, b, c, v, r, he, hc, hk, hsr⟩
  · -- a Turn: its event is its call's bytes
    simp only [Step.event, Event.turn.injEq] at he
    subst he
    exact ⟨c, hc, (submit_ok hs).2.1, fun _ _ => trivial⟩
  · subst hsr
    have hk0 : r.cancel.size = 0 := by rw [(judge_recorded hj).2.2.1]; rfl
    rw [event_unsigned hk0, Event.refusal.injEq] at he
    subst he
    exact ⟨c, v, w', hc, recordedBy_of_judge hj, fun _ _ => trivial⟩
  · subst hsr
    obtain ⟨ha, -, hro, -⟩ := cancel_recorded hk
    have hk0 : r.cancel.size ≠ 0 := by
      rw [hro]; exact Nat.pos_iff_ne_zero.mp (cancelAuth_size ha).1
    rw [event_cancel hk0, Event.cancel.injEq] at he
    obtain ⟨-, rfl⟩ := he
    exact ⟨c, v, w', hc, recordedBy_of_cancel hk, fun _ _ => trivial⟩

/-- **What the follower re-derives is an honest step, and the event IS that step's** (with the call
codec canonical, `hX`; deployed: `Codec.Deployed.eq_callBytes_of_decodeCall`): an event `rederive`
takes to `s` is `s.event` (one event per step), `s` is `World.step`'s on `w`, and `s` is what
`receive` / `judge` / `cancel` decides of its own event. -/
theorem rederive_sound {X : Ctx D} (hX : ∀ b c, X.decodeCall b = some c → X.callBytes c = b)
    {w w' : World D} {ev : Event} {s : Step D} (h : rederive X w ev = .ok (s, w')) :
    s.event = ev ∧ World.step X.env w s = .ok w' ∧ ∀ rest, Honest X w' rest → Honest X w (s :: rest) := by
  have he : s.event = ev := by
    rcases rederive_ok h with ⟨b, c, t, rfl, hc, hs, rfl⟩ | ⟨b, c, v, r, rfl, hc, hj, rfl⟩ |
        ⟨sig, b, c, v, r, rfl, hc, hk, rfl⟩
    · show Event.turn t.event = .turn b
      rw [(receive_derived (submit_ok hs).2.1).event, hX _ _ hc]
    · obtain ⟨-, -, hro, -⟩ := judge_recorded hj
      have hk0 : r.cancel.size = 0 := by rw [hro]; rfl
      rw [event_unsigned hk0, show r.event = X.callBytes c by rw [hro]; rfl, hX _ _ hc]
    · obtain ⟨ha, -, hro, -⟩ := cancel_recorded hk
      have hk0 : r.cancel.size ≠ 0 := by
        rw [hro]; exact Nat.pos_iff_ne_zero.mp (cancelAuth_size ha).1
      rw [event_cancel hk0, show r.event = X.callBytes c by rw [hro]; rfl,
        show r.cancel = sig by rw [hro]; rfl, hX _ _ hc]
  subst he
  exact ⟨rfl, rederive_honest_of_event h⟩

/-- **Every honest step's event re-derives exactly that step** (the completeness half), from a World
whose rows trie is canonical: a Turn by `submit` (`submit_of_admit`), a judged refusal by `judge`,
a cancel by `cancel` under its signature, each to exactly the World the kernel's step reaches. -/
theorem rederive_honest {X : Ctx D} {w w' : World D} {s : Step D} {rest : List (Step D)}
    (hcr : w.RowsCanon X.env) (hh : Honest X w (s :: rest)) (hs : World.step X.env w s = .ok w') :
    rederive X w s.event = .ok (s, w') ∧ Honest X w' rest := by
  cases s with
  | turn t =>
    obtain ⟨c, hd, hr, k⟩ := hh
    refine ⟨?_, k w' hs⟩
    have hsub := submit_of_admit hcr hr hs
    simp only [Step.event, rederive, hd, hsub]
  | refusal r =>
    obtain ⟨c, v, u, hd, hrb, k⟩ := hh
    refine ⟨?_, k w' hs⟩
    have hu : u = w' := by
      have h1 := (recordedBy_recorded hrb).1
      have h2 : World.refuse X.env w r = .ok w' := hs
      rw [h1] at h2; exact Except.ok.inj h2
    subst hu
    by_cases hk : r.cancel.size = 0
    · rw [recordedBy_unsigned hk] at hrb
      rw [event_unsigned hk]
      simp only [rederive, hd, hrb]
    · rw [recordedBy_cancel hk] at hrb
      rw [event_cancel hk]
      simp only [rederive, hd, hrb]

/-! ## The re-deriver on a holder's steps -/

/-- `rederiveStep` passes exactly when the step's own event re-derives that very step. -/
theorem rederiveStep_ok {X : Ctx D} {w w' : World D} {s : Step D} :
    rederiveStep X w s = .ok w' ↔ rederive X w s.event = .ok (s, w') := by
  unfold rederiveStep
  cases hr : rederive X w s.event with
  | error v => simp
  | ok p =>
    obtain ⟨s', w₁⟩ := p
    by_cases he : s' = s
    · subst he; simp
    · simp [he]

/-- **A step that re-derives is an honest kernel step**: `World.step`'s, before any honest
continuation. -/
theorem rederiveStep_sound {X : Ctx D} {w w' : World D} {s : Step D} (h : rederiveStep X w s = .ok w') :
    World.step X.env w s = .ok w' ∧ ∀ rest, Honest X w' rest → Honest X w (s :: rest) :=
  rederive_honest_of_event (rederiveStep_ok.mp h)

/-- **A log that re-derives folds and is honest** (no premise). -/
theorem rederiveLog_sound {X : Ctx D} :
    ∀ {w w' : World D} {l : List (Step D)}, rederiveLog X w l = .ok w' →
      World.fold X.env w l = .ok w' ∧ Honest X w l
  | w, w', [], h => by
    simp only [rederiveLog, Except.ok.injEq] at h
    subst h
    exact ⟨rfl, trivial⟩
  | w, w', s :: rest, h => by
    unfold rederiveLog at h
    cases hs : rederiveStep X w s with
    | error f => simp [hs] at h
    | ok w₁ =>
      cases hr : rederiveLog X w₁ rest with
      | error e => obtain ⟨i, f⟩ := e; simp [hs, hr] at h
      | ok v =>
        simp only [hs, hr, Except.ok.injEq] at h
        subst h
        obtain ⟨hws, hon⟩ := rederiveStep_sound hs
        obtain ⟨hf, hh⟩ := rederiveLog_sound hr
        exact ⟨fold_cons_ok.mpr ⟨w₁, hws, hf⟩, hon _ hh⟩

/-- An honest folded log re-derives, from a World whose rows trie is canonical. -/
theorem rederiveLog_of_honest {X : Ctx D} :
    ∀ {w w' : World D} {l : List (Step D)}, w.RowsCanon X.env → World.fold X.env w l = .ok w' →
      Honest X w l → rederiveLog X w l = .ok w'
  | w, w', [], _, hf, _ => by
    simp only [World.fold, Except.ok.injEq] at hf
    subst hf
    rfl
  | w, w', s :: rest, hcr, hf, hh => by
    obtain ⟨w₁, hs, hfr⟩ := fold_cons_ok.mp hf
    obtain ⟨hrd, hh'⟩ := rederive_honest hcr hh hs
    have hcr₁ : w₁.RowsCanon X.env := by
      cases s with
      | turn t => exact admit_rowsCanon hcr hs
      | refusal r => exact refuse_rowsCanon hcr hs
    have hstep : rederiveStep X w s = .ok w₁ := rederiveStep_ok.mpr hrd
    have hrest := rederiveLog_of_honest hcr₁ hfr hh'
    simp only [rederiveLog, hstep, hrest]

/-- **The re-deriver accepts exactly the honest folded logs** (the theorem the runtime auditors'
check stands on), from a World whose rows trie is canonical (every `Kept` World, and every World a
step reaches from one: `admit_rowsCanon`, `refuse_rowsCanon`). -/
theorem rederiveLog_iff {X : Ctx D} {w w' : World D} {l : List (Step D)} (hcr : w.RowsCanon X.env) :
    rederiveLog X w l = .ok w' ↔ World.fold X.env w l = .ok w' ∧ Honest X w l :=
  ⟨rederiveLog_sound, fun ⟨hf, hh⟩ => rederiveLog_of_honest hcr hf hh⟩

/-! ## The cancel record (KERNEL-60, design C1) -/

/-- **A cancel that re-derives was signed by the member** (the binding fact): a logged record
carrying a cancel signature passes only if its event decodes to a call `c`, the record IS
`cancelOf` `c` and that signature (`c`'s own transaction id, member and window, code `cancelled`),
and the signature verifies over `domCancel ‖ txId` under the key the member's live cell holds on
the World before it. -/
theorem rederiveStep_cancel_signed {X : Ctx D} {w w' : World D} {r : Refused D}
    (h : rederiveStep X w (.refusal r) = .ok w') (hk : r.cancel.size ≠ 0) :
    ∃ c m k, X.decodeCall r.event = some c ∧ r = cancelOf X c r.cancel ∧
      w.live X.env c.unsigned.member = some m ∧ m.kind = kindMember ∧ m.slots.get slotKey = some k ∧
      X.verify k (X.cancelMessage c) r.cancel = true := by
  have h' := rederiveStep_ok.mp h
  rw [event_cancel hk] at h'
  simp only [rederive] at h'
  cases hd : X.decodeCall r.event with
  | none => simp [hd] at h'
  | some c =>
    cases hj : cancel X w c r.cancel with
    | recorded v r' w₁ =>
      simp only [hd, hj, Except.ok.injEq, Prod.mk.injEq, Step.refusal.injEq] at h'
      obtain ⟨rfl, -⟩ := h'
      obtain ⟨ha, -, hr, -⟩ := cancel_recorded hj
      unfold cancelAuth at ha
      simp only [except_bind_ok] at ha
      obtain ⟨⟨⟩, -, ⟨⟩, -, ha⟩ := ha
      split at ha
      · rename_i m hm
        split at ha
        · rename_i k hkey
          split at ha
          · rename_i hkind
            exact ⟨c, m, k, rfl, hr, hm, hkind, hkey, req_ok.mp ha⟩
          · cases ha
        · cases ha
      · cases ha
    | admitted t w₁ => simp [hd, hj] at h'
    | declined v => simp [hd, hj] at h'

/-- **A forged cancel is refused by name** (the tooth of `rederiveStep_cancel_signed`): a logged
record with a cancel signature whose authority fails on the World before it (another key's
signature, no member, an empty or overlong signature, another World) is refused `cancelForged`. -/
theorem rederiveStep_cancel_forged {X : Ctx D} {w : World D} {r : Refused D} {c : Call D} {e : Refusal D}
    (hd : X.decodeCall r.event = some c) (hk : r.cancel.size ≠ 0)
    (ha : cancelAuth X w c r.cancel = .error e) :
    rederiveStep X w (.refusal r) = .error (.refused .cancelForged) := by
  simp [rederiveStep, event_cancel hk, rederive, hd, cancel, ha]

/-- **A record with no cancel signature is never a cancel** (ROOT's condition on KERNEL-60 (i)): it
passes exactly when `judge` records it, whatever its code, so a program refusal spelled `cancelled`
is read as a program refusal and never as a member's act. -/
theorem rederiveStep_unsigned_is_judged {X : Ctx D} {w w' : World D} {r : Refused D}
    (hk : r.cancel.size = 0) :
    rederiveStep X w (.refusal r) = .ok w' ↔
      ∃ c v, X.decodeCall r.event = some c ∧ judge X w c = .recorded v r w' := by
  rw [rederiveStep_ok, event_unsigned hk]
  simp only [rederive]
  constructor
  · intro h
    cases hd : X.decodeCall r.event with
    | none => simp [hd] at h
    | some c =>
      cases hj : judge X w c with
      | recorded v r' w₁ =>
        simp only [hd, hj, Except.ok.injEq, Prod.mk.injEq, Step.refusal.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨c, v, rfl, hj⟩
      | admitted t w₁ => simp [hd, hj] at h
      | declined v => simp [hd, hj] at h
  · rintro ⟨c, v, hd, hj⟩
    simp [hd, hj]

/-- **A program refusal spelled `cancelled` carrying a forged cancel field is `cancelForged`** (ROOT's
tooth on KERNEL-60 (i)): the field makes it a cancel, and the follower re-verifies it as one. -/
theorem rederiveStep_program_cancelled_forged {X : Ctx D} {w : World D} {c : Call D} {a : ByteArray}
    {e : Refusal D} (hd : X.decodeCall (recordOf X c (.refused .cancelled) a).event = some c)
    (hk : a.size ≠ 0) (ha : cancelAuth X w c a = .error e) :
    rederiveStep X w (.refusal (recordOf X c (.refused .cancelled) a)) = .error (.refused .cancelForged) :=
  rederiveStep_cancel_forged hd hk ha

/-- **A cancel outside its call's window is declined** (KERNEL-47 amendment 5's reason: a record
made before the call's window opens could be pruned before it closes): early, `outsideWindow`. -/
theorem cancel_early_declined {X : Ctx D} {w : World D} {c : Call D} {sig : ByteArray}
    (ha : cancelAuth X w c sig = .ok ()) (hb : checkRefusedBounds (cancelOf X c sig) = .ok ())
    (hs : checkSteps w = .ok ()) (he : w.height + 1 < c.unsigned.notBefore) :
    cancel X w c sig = .declined (.rejected .outsideWindow) := by
  have hn : ¬ (c.unsigned.notBefore ≤ w.height + 1) := by omega
  have hw : (cancelOf X c sig).notBefore = c.unsigned.notBefore := rfl
  simp only [cancel, ha, World.refuse, checkRefusal, hb, hs, bind, Except.bind]
  simp [req, hw, hn]

/-- **A recorded stale never re-derives** (KERNEL-54): neither `judge` (`judge_recorded_not_stale`)
nor `cancel` (code `cancelled`) records a refusal with the stale code, so a log step recording one is
refused, whatever it is refused by. -/
theorem rederiveStep_stale {X : Ctx D} {w w' : World D} {r : Refused D} (hc : r.code = staleCode) :
    rederiveStep X w (.refusal r) ≠ .ok w' := by
  intro h
  obtain ⟨c, v, u, -, hrb, -⟩ := (rederiveStep_sound h).2 [] trivial
  exact (recordedBy_recorded hrb).2 hc

/-! ## A pinned row effect on an unpinned row names the row (KERNEL-54 day, ROOT) -/

/-- **`rowUnpinned` carries the row's key**: an upsert or a retract (`unpinned = false`) on a row the
caller did not pin is refused with that row's parent, relation AND key bytes, so a client re-signs
pinning exactly that row (`Protocol` derivePins). Before, the refusal named only the relation, and
no client could learn which row to pin. -/
theorem rowTouchesOf_unpinned_key {pins : List (RowSlot D × D)} {key : RowKey D} {a : RowAct}
    {rest : List (RowSlot D × RowAct)} (ha : a.unpinned = false) (hp : ∀ p ∈ pins, p.1 ≠ .row key) :
    rowTouchesOf pins ((.row key, a) :: rest) = .error (.rowUnpinned key.parent key.rel key.k) := by
  have hany : (pins.any fun p => decide (p.1 = .row key)) = false := by
    simp only [List.any_eq_false, decide_eq_true_eq]; exact hp
  simp [rowTouchesOf, forEx, req, ha, hany, RowSlot.under, RowSlot.keyBytes, bind, Except.bind]

end Nanodregg.Kernel.Receive
