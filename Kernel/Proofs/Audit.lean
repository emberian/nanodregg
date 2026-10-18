/-
# Kernel.Proofs.Audit — an audited log is exactly an honest one, folded
-/
import Kernel.Receive.Audit
import Kernel.Proofs.Fold

namespace Nanodregg.Kernel.Receive

open Nanodregg.Kernel

variable {D : Type} [Ord D] [DecidableEq D]

/-- What `judge` recording a refusal means: the call was refused with `v`, it was authenticated, the
record is `refusedOf` the call and the verdict, and `World.refuse` took it. -/
theorem judge_recorded {X : Ctx D} {w w' : World D} {c : Call D} {v : Verdict D} {r : Refused D}
    (h : judge X w c = .recorded v r w') :
    submit X w c = .error v ∧ authenticated X w c = true ∧ r = refusedOf X c v ∧
      World.refuse X.env w r = .ok w' := by
  unfold judge at h
  split at h
  · cases h
  · rename_i v' hs
    split at h
    · rename_i ha
      split at h
      · rename_i w'' hr
        simp only [Outcome.recorded.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact ⟨hs, ha, rfl, hr⟩
      · cases h
      · cases h
    · cases h

/-- A log every step of which is exactly what its own event is judged to, on the World before it: a
Turn is what `receive` derives from its event, a recorded refusal is what `judge` records for its
event. A log in which the writer decided nothing. -/
def Honest (X : Ctx D) : World D → List (Step D) → Prop
  | _, [] => True
  | w, .turn t :: rest => ∃ c, X.decodeCall t.event = some c ∧ receive X w c = .ok t ∧
      ∀ w', World.admit X.env w t = .ok w' → Honest X w' rest
  | w, .refusal r :: rest => ∃ c v w₁, X.decodeCall r.event = some c ∧ judge X w c = .recorded v r w₁ ∧
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

/-- A logged refusal passes exactly when its event decodes to a call that `judge` records as this
very refusal, on the World before it; the World it reaches is `World.refuse`'s. -/
theorem auditRefusal_ok {X : Ctx D} {w w' : World D} {r : Refused D} :
    auditRefusal X w r = .ok w' ↔
      ∃ c v, X.decodeCall r.event = some c ∧ judge X w c = .recorded v r w' := by
  unfold auditRefusal
  constructor
  · intro h
    split at h
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
    simp [hd, hj]

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
                    have hrf := (judge_recorded hj).2.2.2
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
            have hrf := (judge_recorded hj).2.2.2
            have : w₂ = w₁ := by
              have := hrf.symm.trans ha; exact (Except.ok.inj this)
            subst this
            have hs : auditStep X w (.refusal r) = .ok w₂ := auditRefusal_ok.mpr ⟨c, v₀, hd, hj⟩
            have hr : audit X w₂ rest = .ok w' := audit_ok.mpr ⟨hf, hh w₂ hrf⟩
            simp [hs, hr]

end Nanodregg.Kernel.Receive
