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

/-- **A posted support is checked against the cell it cites** (B2, LANG-75.1; LANG-81 binds the
cell): when the generated probe reads a support as current, the fact is at the support's cell and
pin, and the kernel cell THAT SUPPORT CITES (`digestOf cell = some g`) is live in the caller's pinned
view, given that the point's `live` bit is the runtime's for the cell its key names (`hg`, `hlive`:
what `cited_hole_point` derives from the deployed read). A fact naming a cell the kernel never had,
or one revoked, never reads current. Mutation: `holeProbePoint` ignores `live` (the ghost fact of
`promo/E1-support-probe.txt` reads 1). -/
theorem posted_support_checked {D : Type} (digestOf : ByteArray → Option D) (cell pin : ByteArray)
    (p : HolePoint) (lib : List Term) (env : Env) (look : Pinned D) (g : D)
    (hg : digestOf p.cell = some g) (hlive : p.live = cellLive look g)
    (h : BigStep lib ((holePointData (some p)).toVal :: (holeSupportData cell pin).toVal :: env)
      (activityApply holeProbePoint [.var 1, .var 0]) (.ok (.nat 1))) :
    p.cell = cell ∧ p.pin = some pin ∧ digestOf cell = some g ∧ ∃ c, look g = .ok (some c) := by
  have he := bigStep_deterministic (holeProbePoint_meaning cell pin (some p) lib env) h
  simp only [Except.ok.injEq, Val.nat.injEq] at he
  obtain ⟨q, hq, hc, hp, hl⟩ := holePointObservation_current he
  cases hq
  exact ⟨hc, hp, hc ▸ hg, cellLive_iff.mp (hlive ▸ hl)⟩

/-- **A revoked support refuses by itself** (B1 at the generated judge, LANG-75.1; LANG-81 binds the
cell): a fact at the support's cell and pin, where the kernel cell its key names (`digestOf p.cell =
some g`, so the cell THAT SUPPORT CITES) is pinned at its tombstone (`look g = .ok none`) and the point's bit is
the runtime's for it, probes DEAD (3), and the judge's admission for that support is the named
refusal `support0 dead` whatever the other support observes; the dead cell is the one the support
cites. A tombstone of any OTHER cell does not meet `hg`: the support is refused for its own cell,
never for another's (`other_cell_revoked_current`).
With `cited_hole_point` this is the commit's own read, in the same Turn as its spend. Mutation:
`holeProbePoint` ignores `live`. -/
theorem revoked_support_refused_hole {D : Type} (digestOf : ByteArray → Option D) (cell pin : ByteArray)
    (p : HolePoint) (lib : List Term) (env : Env) (look : Pinned D) (g : D)
    (hg : digestOf p.cell = some g) (hlive : p.live = cellLive look g) (hdead : look g = .ok none)
    (hc : p.cell = cell) (hp : p.pin = some pin) :
    digestOf cell = some g ∧
    BigStep lib ((holePointData (some p)).toVal :: (holeSupportData cell pin).toVal :: env)
      (activityApply holeProbePoint [.var 1, .var 0]) (.ok (.nat 3)) ∧
    ∀ s1, holeAdmission (holeVerdictLabel true false 3 s1) = .error (.refused "support0 dead".toUTF8) := by
  refine ⟨hc ▸ hg, ?_, fun s1 => by simp [holeVerdictLabel, holeAdmission]⟩
  have hm := holeProbePoint_meaning cell pin (some p) lib env
  have hdl : p.live = false := by rw [hlive]; simp [cellLive, hdead]
  simpa [holePointObservation, hc, hp, hdl] using hm

/-- **The deployed read supplies both premises** (LANG-81): on a live, non-receipt read, a slot of
the rows argument that is a hole point `p` has `p.cell` the cell its key names and `p.live` the
caller's pinned view of THAT cell (`cited_authenticated`): exactly `hg` and `hlive` of
`posted_support_checked` and `revoked_support_refused_hole`. -/
theorem cited_hole_point {D : Type} {digestOf : ByteArray → Option D} {rc : Lang.ReceiptCheck}
    {look : Pinned D} {rv : RowView D} {self : D} {i : Nat} {ℓ : Label} {d : RelDecl} {x : RelRead}
    {args v : Data}
    (h : relReads digestOf rc look rv self i ℓ d x args = .ok v) (hl : x.live = true) (hr : x.receipt = false) :
    ∃ ps rest, v = .record (slotsD "p" x.points ps ++ rest) ∧
      ∀ j (hj : j < ps.length) (p : HolePoint), Data.inj "some" ps[j] = holePointData (some p) →
        ∃ g, digestOf p.cell = some g ∧ p.live = cellLive look g := by
  obtain ⟨ps, rest, hv, _, hall⟩ := cited_authenticated h hl
  refine ⟨ps, rest, hv, fun j hj p hp => ?_⟩
  obtain ⟨k, b, g, val, col, _, hkc, hdg, hps, hcol⟩ := hall j hj
  have hc := hcol hr
  subst hc
  rw [hps] at hp
  simp only [holePointData, List.append_nil, List.cons_append, List.nil_append, Data.inj.injEq,
    Data.record.injEq, List.cons.injEq, Prod.mk.injEq, Data.bool.injEq, true_and] at hp
  obtain ⟨rfl, hlv, -⟩ := hp
  simp only [keyCell, Option.some.injEq] at hkc
  subst hkc
  exact ⟨g, hdg, hlv.symm⟩

/-- **The plant's instance** (A15): cell `a` is live and cell `b` is pinned at its tombstone. A
support citing `a`, whose point's bit is `a`'s liveness, probes current (1): it is not refused for
`b`'s revocation. The pre-LANG-81 `revoked_support_refused_hole` quantified a free `g`: at `g := b`
with the point's bit `cellLive look b = false` its premises held for the support citing `a`, and it
concluded that support refused. `hg` (`digestOf a = some b`) is false here, so the restated theorem
cannot be instantiated that way (`hg` needs `digestOf a = some b`). -/
theorem other_cell_revoked_current (a b pin author : ByteArray) (c : Kernel.Cell) (lib : List Term)
    (env : Env) (hab : a ≠ b) :
    let look : Pinned ByteArray := fun g => if g = a then .ok (some c) else .ok none
    look b = .ok none ∧ (some a : Option ByteArray) ≠ some b ∧
    BigStep lib ((holePointData (some ⟨a, author, some pin, cellLive look a⟩)).toVal ::
        (holeSupportData a pin).toVal :: env)
      (activityApply holeProbePoint [.var 1, .var 0]) (.ok (.nat 1)) := by
  intro look
  have hl : cellLive look a = true := by simp [look, cellLive]
  refine ⟨by simp [look, Ne.symm hab], by simpa using hab, ?_⟩
  have hm := holeProbePoint_meaning a pin (some ⟨a, author, some pin, cellLive look a⟩) lib env
  simpa [holePointObservation, hl] using hm

end Nanodregg.Lang.Std
