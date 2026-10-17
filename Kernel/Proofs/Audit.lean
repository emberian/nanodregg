/-
# Kernel.Proofs.Audit — an audited log is exactly an honest one, folded
-/
import Kernel.Receive.Audit
import Kernel.Proofs.Fold

namespace Nanodregg.Kernel.Receive

open Nanodregg.Kernel

variable {D : Type} [Ord D] [DecidableEq D]

/-- A log every Turn of which is exactly what `receive` derives from its own event, on the World
before it: a log in which the writer decided nothing. -/
def Honest (X : Ctx D) : World D → List (Turn D) → Prop
  | _, [] => True
  | w, t :: rest => ∃ c, X.decodeCall t.event = some c ∧ receive X w c = .ok t ∧
      ∀ w', World.admit X.env w t = .ok w' → Honest X w' rest


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

theorem auditStep_ok {X : Ctx D} {w w' : World D} {t : Turn D} :
    auditStep X w t = .ok w' ↔
      (∃ c, X.decodeCall t.event = some c ∧ receive X w c = .ok t) ∧
        World.admit X.env w t = .ok w' := by
  rw [← rederive_ok]
  unfold auditStep
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

/-- **The audit theorem.** A follower's audit accepts a log exactly when folding it succeeds and
every Turn in it is what its own signed event derives: the writer's authority decided nothing
the follower did not re-derive. -/
theorem audit_ok {X : Ctx D} :
    ∀ {w w' : World D} {l : List (Turn D)},
      audit X w l = .ok w' ↔ World.fold X.env w l = .ok w' ∧ Honest X w l
  | w, w', [] => by simp [audit, World.fold, Honest]
  | w, w', t :: rest => by
      rw [fold_cons_ok]
      unfold audit
      constructor
      · intro h
        cases hs : auditStep X w t with
        | error f => simp [hs] at h
        | ok w₁ =>
            rw [hs] at h
            cases hr : audit X w₁ rest with
            | error e => obtain ⟨i, f⟩ := e; simp [hr] at h
            | ok v =>
                simp only [hr, Except.ok.injEq] at h
                subst h
                obtain ⟨⟨c, hd, hrc⟩, ha⟩ := auditStep_ok.mp hs
                obtain ⟨hf, hh⟩ := audit_ok.mp hr
                refine ⟨⟨w₁, ha, hf⟩, c, hd, hrc, ?_⟩
                intro w'' ha''
                rw [ha] at ha''
                cases ha''
                exact hh
      · rintro ⟨⟨w₁, ha, hf⟩, c, hd, hrc, hh⟩
        have hs : auditStep X w t = .ok w₁ := auditStep_ok.mpr ⟨⟨c, hd, hrc⟩, ha⟩
        have hr : audit X w₁ rest = .ok w' := audit_ok.mpr ⟨hf, hh w₁ ha⟩
        simp [hs, hr]

end Nanodregg.Kernel.Receive
