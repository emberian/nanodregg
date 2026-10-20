/-
# Kernel.Proofs.Audit — an audited log is exactly an honest one, folded
-/
import Kernel.Receive.Audit
import Kernel.Proofs.Fold

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
    · split at h
      · rename_i r hr
        cases h
        refine receive_checkSignature (w := w) (fun he => ?_) (fun he => ?_)
        · rw [hr] at he; cases he; simp [Verdict.verified] at hv
        · rw [hr] at he; cases he; simp [Verdict.verified] at hv
      · rename_i t hr
        refine receive_checkSignature (by rw [hr]; exact fun he => by cases he)
          (by rw [hr]; exact fun he => by cases he)

/-- The authentication `judge` makes is `authenticated`, for every verdict `submit` gives. -/
theorem authenticatedBy_verified {X : Ctx D} {w : World D} {c : Call D} {v : Verdict D}
    (h : submit X w c = .error v) : authenticatedBy X w c v.verified = authenticated X w c := by
  cases hv : v.verified
  · rfl
  · simp only [authenticated, authenticatedBy, checkSignatureBy, if_true, Bool.false_eq_true,
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

/-- **A judged refusal is its own re-judge.** What `judge` records carries no cancel field
(`refusedOf` is `recordOf … ByteArray.empty`), so `recordedBy` of that record IS `judge`: the
audit re-judges a judged refusal by `judge`, never as a member's cancel. -/
theorem recordedBy_of_judge {X : Ctx D} {w w' : World D} {c : Call D} {v : Verdict D} {r : Refused D}
    (h : judge X w c = .recorded v r w') : recordedBy X w c r = .recorded v r w' := by
  obtain ⟨-, -, hr, -⟩ := judge_recorded h
  have hk : r.cancel.size = 0 := by rw [hr]; rfl
  unfold recordedBy
  rw [if_pos hk]
  exact h

/-- **What a log's re-judge records**: `World.refuse` took it, and its code is not the stale code
(`judge`'s by `judge_recorded_not_stale`; a cancel's is `cancelled`'s). -/
theorem recordedBy_recorded {X : Ctx D} {w w' : World D} {c : Call D} {r r' : Refused D} {v : Verdict D}
    (h : recordedBy X w c r = .recorded v r' w') :
    World.refuse X.env w r' = .ok w' ∧ r'.code ≠ staleCode := by
  unfold recordedBy at h
  split at h
  · exact ⟨(judge_recorded h).2.2.2, (judge_recorded_not_stale h).2⟩
  · obtain ⟨-, rfl, rfl, hr⟩ := cancel_recorded h
    exact ⟨hr, code_ne_staleCode (D := D) (v := .refused .cancelled) rfl⟩

/-- A log every step of which is exactly what its own event is judged to, on the World before it: a
Turn is what `receive` derives from its event, a recorded refusal is what `judge` records for its
event. A log in which the writer decided nothing. -/
def Honest (X : Ctx D) : World D → List (Step D) → Prop
  | _, [] => True
  | w, .turn t :: rest => ∃ c, X.decodeCall t.event = some c ∧ receive X w c = .ok t ∧
      ∀ w', World.admit X.env w t = .ok w' → Honest X w' rest
  | w, .refusal r :: rest => ∃ c v w₁, X.decodeCall r.event = some c ∧ recordedBy X w c r = .recorded v r w₁ ∧
      ∀ w', World.refuse X.env w r = .ok w' → Honest X w' rest


/-- **Re-derivation (PROTOCOL-4).** A logged Turn passes exactly when its event decodes to a call
that derives that very Turn on the World before it. -/
theorem rederive_ok {X : Ctx D} {w : World D} {t : Turn D} :
    rederive X w t = .ok () ↔ ∃ c, X.decodeCall t.event = some c ∧ receive X w c = .ok t := by
  unfold rederive
  constructor
  · intro h
    split at h
    · simp at h
    · rename_i c hd
      split at h
      · simp at h
      · rename_i t' hr
        split at h
        · rename_i ht
          subst ht
          exact ⟨c, hd, hr⟩
        · simp at h
  · rintro ⟨c, hd, hr⟩
    simp [hd, hr]

theorem auditTurn_ok {X : Ctx D} {w w' : World D} {t : Turn D} :
    auditTurn X w t = .ok w' ↔
      (∃ c, X.decodeCall t.event = some c ∧ receive X w c = .ok t) ∧
        World.admit X.env w t = .ok w' := by
  rw [← rederive_ok]
  unfold auditTurn
  constructor
  · intro h
    split at h
    · simp at h
    · rename_i hr
      split at h
      · rename_i v ha
        simp only [Except.ok.injEq] at h
        subst h
        exact ⟨hr, ha⟩
      · simp at h
  · rintro ⟨hr, ha⟩
    simp [hr, ha]

/-- A logged refusal passes exactly when its event decodes to a call that its re-judge
(`recordedBy`: `judge`, or `cancel` for a record carrying a cancel signature) records as this very
refusal, on the World before it; the World it reaches is `World.refuse`'s. -/
theorem auditRefusal_ok {X : Ctx D} {w w' : World D} {r : Refused D} :
    auditRefusal X w r = .ok w' ↔
      ∃ c v, X.decodeCall r.event = some c ∧ recordedBy X w c r = .recorded v r w' := by
  unfold auditRefusal
  constructor
  · intro h
    split at h
    · simp at h
    · split at h
      · simp at h
      · rename_i c hd
        split at h
        · rename_i v r' w₁ hj
          split at h
          · rename_i hr
            subst hr
            simp only [Except.ok.injEq] at h
            subst h
            exact ⟨c, v, hd, hj⟩
          · simp at h
        · simp at h
  · rintro ⟨c, v, hd, hj⟩
    have hc : r.code ≠ staleCode := (recordedBy_recorded hj).2
    simp [hc, hd, hj]

/-- **The audit theorem.** A follower's audit accepts a log exactly when folding it succeeds and
every step in it is what its own signed event is judged to: the writer's authority decided nothing
the follower did not re-derive, neither a Turn nor a recorded refusal. -/
theorem audit_ok {X : Ctx D} :
    ∀ {w w' : World D} {l : List (Step D)},
      audit X w l = .ok w' ↔ World.fold X.env w l = .ok w' ∧ Honest X w l
  | w, w', [] => by simp [audit, World.fold, Honest]
  | w, w', s :: rest => by
      rw [fold_cons_ok]
      unfold audit
      constructor
      · intro h
        cases hs : auditStep X w s with
        | error f => simp [hs] at h
        | ok w₁ =>
            rw [hs] at h
            cases hr : audit X w₁ rest with
            | error e => obtain ⟨i, f⟩ := e; simp [hr] at h
            | ok v =>
                simp only [hr, Except.ok.injEq] at h
                subst h
                obtain ⟨hf, hh⟩ := audit_ok.mp hr
                cases s with
                | turn t =>
                    obtain ⟨⟨c, hd, hrc⟩, ha⟩ := auditTurn_ok.mp hs
                    refine ⟨⟨w₁, ha, hf⟩, c, hd, hrc, ?_⟩
                    intro w'' ha''
                    rw [show World.admit X.env w t = _ from ha] at ha''
                    cases ha''
                    exact hh
                | refusal r =>
                    obtain ⟨c, v₀, hd, hj⟩ := auditRefusal_ok.mp hs
                    have hrf := (recordedBy_recorded hj).1
                    refine ⟨⟨w₁, hrf, hf⟩, c, v₀, w₁, hd, hj, ?_⟩
                    intro w'' hr''
                    rw [hrf] at hr''
                    cases hr''
                    exact hh
      · intro hh
        obtain ⟨⟨w₁, ha, hf⟩, hhon⟩ := hh
        cases s with
        | turn t =>
            obtain ⟨c, hd, hrc, hh⟩ := hhon
            have hs : auditStep X w (.turn t) = .ok w₁ := auditTurn_ok.mpr ⟨⟨c, hd, hrc⟩, ha⟩
            have hr : audit X w₁ rest = .ok w' := audit_ok.mpr ⟨hf, hh w₁ ha⟩
            simp [hs, hr]
        | refusal r =>
            obtain ⟨c, v₀, w₂, hd, hj, hh⟩ := hhon
            have hrf := (recordedBy_recorded hj).1
            have : w₂ = w₁ := by
              have := hrf.symm.trans ha; exact (Except.ok.inj this)
            subst this
            have hs : auditStep X w (.refusal r) = .ok w₂ := auditRefusal_ok.mpr ⟨c, v₀, hd, hj⟩
            have hr : audit X w₂ rest = .ok w' := audit_ok.mpr ⟨hf, hh w₂ hrf⟩
            simp [hs, hr]

/-! ## The cancel record (KERNEL-60, design C1) -/

/-- **A cancel the audit accepts was signed by the member** (the binding fact): a logged record
carrying a cancel signature passes the audit only if its event decodes to a call `c`, the record IS
`cancelOf` `c` and that signature (`c`'s own transaction id, member and window, code `cancelled`),
and the signature verifies over `domCancel ‖ txId` under the key the member's live cell holds on
the World before it. -/
theorem audit_cancel_signed {X : Ctx D} {w w' : World D} {r : Refused D}
    (h : auditRefusal X w r = .ok w') (hk : r.cancel.size ≠ 0) :
    ∃ c m k, X.decodeCall r.event = some c ∧ r = cancelOf X c r.cancel ∧
      w.live X.env c.unsigned.member = some m ∧ m.kind = kindMember ∧ m.slots.get slotKey = some k ∧
      X.verify k (X.cancelMessage c) r.cancel = true := by
  obtain ⟨c, v, hd, hj⟩ := auditRefusal_ok.mp h
  simp only [recordedBy, hk, if_false] at hj
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
        exact ⟨c, m, k, hd, hr.symm ▸ rfl, hm, hkind, hkey, req_ok.mp ha⟩
      · cases ha
    · cases ha
  · cases ha

/-- **A forged cancel is refused by name** (the tooth of `audit_cancel_signed`): a logged record
with a cancel signature whose authority fails on the World before it (another key's signature, no
member, an empty or overlong signature, another World) is refused `cancelForged`. -/
theorem audit_cancel_forged {X : Ctx D} {w : World D} {r : Refused D} {c : Call D} {e : Refusal D}
    (hs : r.code ≠ staleCode) (hd : X.decodeCall r.event = some c) (hk : r.cancel.size ≠ 0)
    (ha : cancelAuth X w c r.cancel = .error e) :
    auditRefusal X w r = .error (.refused .cancelForged) := by
  simp [auditRefusal, hs, hd, recordedBy, hk, cancel, ha, forgedName]

/-- **A record with no cancel signature is never a cancel** (ROOT's condition on KERNEL-60 (i)): it
passes the audit exactly when `judge` records it, whatever its code, so a program refusal spelled
`cancelled` is read as a program refusal and never as a member's act. -/
theorem audit_unsigned_is_judged {X : Ctx D} {w w' : World D} {r : Refused D} (hk : r.cancel.size = 0) :
    auditRefusal X w r = .ok w' ↔
      ∃ c v, X.decodeCall r.event = some c ∧ judge X w c = .recorded v r w' := by
  rw [auditRefusal_ok]
  simp only [recordedBy, hk, if_true]

/-- **A program refusal spelled `cancelled` carrying a forged cancel field is `cancelForged`** (ROOT's
tooth on KERNEL-60 (i)): the field makes it a cancel, and the audit re-verifies it as one. -/
theorem audit_program_cancelled_forged {X : Ctx D} {w : World D} {c : Call D} {a : ByteArray}
    {e : Refusal D} (hd : X.decodeCall (recordOf X c (.refused .cancelled) a).event = some c)
    (hk : a.size ≠ 0) (ha : cancelAuth X w c a = .error e) :
    auditRefusal X w (recordOf X c (.refused .cancelled) a) = .error (.refused .cancelForged) :=
  audit_cancel_forged (by
    have := code_ne_staleCode (D := D) (v := .refused .cancelled) rfl
    simpa [recordOf] using this) hd hk ha

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

/-- **A recorded stale is refused by name**: the follower's audit refuses a log step recording a
refusal with the stale code, `staleRecorded`, before decoding anything. -/
theorem auditRefusal_stale {X : Ctx D} {w : World D} {r : Refused D} (hc : r.code = staleCode) :
    auditRefusal X w r = .error (.refused .staleRecorded) := by
  simp [auditRefusal, hc]

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
