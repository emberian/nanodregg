/-
# Lang.Proofs.Effect — a returned run moves at most its grade (LANG-89; DESIGN-TYPES §2.4)

`runMeasuredWith_moves_le`: a run that returned had `checkMoves` admit the calls it returned, so
`movesOf calls ≤ S.effect.moves` for its setup `S`, whatever the setup. `runMeasured_moves_le` names
the grade for the deployed setup (`runSetupWith`, so `runMeasured`, `runMeasuredLive`, `runMethod` and
`Lang.program`'s `run`): `S.effect = p.effectOf ℓ` for the resolved method `ℓ` of the loaded package
`p`, so the calls move at most the grade the package declares for the method.

Plant: `checkMoves := fun _ _ => .ok ()` in `Lang/Call.lean` reds `checkMoves_le` (and so both
theorems) and the journey's EF3/EF5 (a run of 20 under a grade of 10 is admitted).
-/
import Lang.Proofs.Load

namespace Nanodregg.Lang

open Nanodregg.Kernel.Receive

/-- `checkMoves` admits exactly the call lists within the grade. -/
theorem checkMoves_le {D : Type} {e : Effect} {calls : List (Body D)} (h : checkMoves e calls = .ok ()) :
    movesOf calls ≤ e.moves := by
  unfold checkMoves at h
  split at h
  · assumption
  · cases h

/-- **A returned run's calls are within its setup's grade.** -/
theorem runMeasuredWith_moves_le {D : Type} {bytesOf : D → ByteArray} {digestOf : ByteArray → Option D}
    {setup : Pinned D → RowView D → D → Kernel.Slots → Nat → ByteArray → Req D → Except (Refusal D) RunSetup}
    {look : Pinned D} {rv : RowView D} {pkg : D} {state : Kernel.Slots} {method : Nat} {args : ByteArray}
    {r : Req D} {budget : Nat} {s : Kernel.Slots} {calls : List (Body D)}
    {rows : List (Kernel.RowSlot D × Kernel.RowAct)} {t n : Nat}
    (h : runMeasuredWith bytesOf digestOf setup look rv pkg state method args r budget = .ok (s, calls, rows, t, n)) :
    ∃ S, setup look rv pkg state method args r = .ok S ∧ movesOf calls ≤ S.effect.moves := by
  unfold runMeasuredWith at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  rename_i S hS
  split at h
  · simp at h
  split at h
  · simp at h
  split at h
  all_goals first | (simp at h; done) | skip
  repeat' split at h
  all_goals first | (simp at h; done) | skip
  simp only [Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨-, rfl, -, -, -⟩ := h
  exact ⟨S, hS, checkMoves_le ‹checkMoves _ _ = .ok _›⟩

/-- **A returned run moves at most the grade its package declares for the method** (LANG-89's
theorem): for the deployed setup, the resolved method `ℓ` of the loaded package `p` has
`movesOf calls ≤ (p.effectOf ℓ).moves`. -/
theorem runMeasured_moves_le {D : Type} {bytesOf : D → ByteArray} {digestOf : ByteArray → Option D}
    {rc : ReceiptCheck} {loader : Pinned D → Nat → ByteArray → Loaded → Except (Refusal D) (Loaded × Nat)}
    {charge : Loaded → Nat} {look : Pinned D} {rv : RowView D} {pkg : D} {state : Kernel.Slots} {method : Nat}
    {args : ByteArray} {r : Req D} {budget : Nat} {s : Kernel.Slots} {calls : List (Body D)}
    {rows : List (Kernel.RowSlot D × Kernel.RowAct)} {t n : Nat}
    (h : runMeasuredWith bytesOf digestOf (runSetupWith bytesOf digestOf rc loader charge) look rv pkg state method args r budget =
      .ok (s, calls, rows, t, n)) :
    ∃ (L : Loaded) (g : Nat) (p : Package) (ℓ : Label) (sg : Sig),
      loader look closureDepthMax (bytesOf pkg) ⟨[], [], []⟩ = .ok (L, g) ∧ L.pkgs[g]? = some p ∧
      resolveMethod (D := D) p method = .ok (ℓ, sg) ∧ movesOf calls ≤ (p.effectOf ℓ).moves := by
  obtain ⟨S, hS, hm⟩ := runMeasuredWith_moves_le h
  obtain ⟨L, g, p, ℓ, sg, sd, ad, wd, -, hL, hp, hres, -, -, -, -, hE⟩ := runSetupWith_spec hS
  rw [hE] at hm
  exact ⟨L, g, p, ℓ, sg, hL, hp, hres, hm⟩

end Nanodregg.Lang
