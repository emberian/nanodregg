/- C1 (LANG-75.1): the generated hole's support observation against the kernel's pinned cells.
A posted fact is the poster's claim; the probe reads it as current only at a cell the caller's
pinned view holds live (`cited_authenticated` puts `cellLive look g` in that bit). -/
import Lang.Proofs.StdHoleLookup
import Lang.Proofs.Rel

namespace Nanodregg.Lang.Std
open Nanodregg.Kernel.Receive

/-- The model's current observation (1) is a present fact at the support's cell and pin whose cell
is live. -/
theorem holePointObservation_current {cell pin : ByteArray} {pt : Option HolePoint}
    (h : holePointObservation cell pin pt = 1) :
    ∃ p, pt = some p ∧ p.cell = cell ∧ p.pin = some pin ∧ p.live = true := by
  cases pt with
  | none => simp [holePointObservation] at h
  | some p =>
    refine ⟨p, rfl, ?_⟩
    simp only [holePointObservation] at h
    by_cases hc : p.cell = cell
    · simp only [hc, ↓reduceIte] at h
      cases hp : p.pin with
      | none => simp [hp] at h
      | some v =>
        simp only [hp] at h
        by_cases hv : v = pin
        · subst hv
          cases hl : p.live
          · simp [hl] at h
          · exact ⟨hc, rfl, rfl⟩
        · simp [hv] at h
    · simp [hc] at h

/-- **A posted support is checked against the cell it cites** (B2, LANG-75.1): when the generated
probe reads a support as current, the fact is at the support's cell and pin AND, given that the
point's `live` bit is the runtime's (`cited_authenticated`), the caller's pinned view holds that
kernel cell live. A fact naming a cell the kernel never had, or one revoked, never reads current.
Mutation: `holeProbePoint` ignores `live` (the ghost fact of `promo/E1-support-probe.txt` reads 1). -/
theorem posted_support_checked {D : Type} (cell pin : ByteArray) (p : HolePoint) (lib : List Term)
    (env : Env) (look : Pinned D) (g : D) (hlive : p.live = cellLive look g)
    (h : BigStep lib ((holePointData (some p)).toVal :: (holeSupportData cell pin).toVal :: env)
      (activityApply holeProbePoint [.var 1, .var 0]) (.ok (.nat 1))) :
    p.cell = cell ∧ p.pin = some pin ∧ ∃ c, look g = .ok (some c) := by
  have he := bigStep_deterministic (holeProbePoint_meaning cell pin (some p) lib env) h
  simp only [Except.ok.injEq, Val.nat.injEq] at he
  obtain ⟨q, hq, hc, hp, hl⟩ := holePointObservation_current he
  cases hq
  exact ⟨hc, hp, cellLive_iff.mp (hlive ▸ hl)⟩

/-- **A revoked support refuses by itself** (B1 at the generated judge, LANG-75.1): a fact at the
support's cell and pin whose cell the caller pinned at its tombstone (`look g = .ok none`) probes
DEAD (3), and the judge's admission for that support is the named refusal `support0 dead` whatever
the other support observes. With `cited_authenticated` (the bit is `cellLive look g`) this is the
commit's own read, in the same Turn as its spend. Mutation: `holeProbePoint` ignores `live`. -/
theorem revoked_support_refused_hole {D : Type} (cell pin : ByteArray) (p : HolePoint)
    (lib : List Term) (env : Env) (look : Pinned D) (g : D)
    (hlive : p.live = cellLive look g) (hdead : look g = .ok none)
    (hc : p.cell = cell) (hp : p.pin = some pin) :
    BigStep lib ((holePointData (some p)).toVal :: (holeSupportData cell pin).toVal :: env)
      (activityApply holeProbePoint [.var 1, .var 0]) (.ok (.nat 3)) ∧
    ∀ s1, holeAdmission (holeVerdictLabel true false 3 s1) = .error (.refused "support0 dead".toUTF8) := by
  refine ⟨?_, fun s1 => by simp [holeVerdictLabel, holeAdmission]⟩
  have hm := holeProbePoint_meaning cell pin (some p) lib env
  have hdl : p.live = false := by rw [hlive]; simp [cellLive, hdead]
  simpa [holePointObservation, hc, hp, hdl] using hm

end Nanodregg.Lang.Std
