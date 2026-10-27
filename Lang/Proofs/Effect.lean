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

/-- `checkEffect` admitting means `checkMoves` admitted. -/
theorem checkEffect_moves {D : Type} {ℓ : Label} {e : Effect} {calls : List (Body D)}
    (h : checkEffect ℓ e calls = .ok ()) : checkMoves e calls = .ok () := by
  unfold checkEffect at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  · rename_i u hm; cases u; exact hm

/-- `checkProduces` admits exactly the call lists every package of which has the declared interface:
an `install` or `createOf` whose bytes decode carries a package whose `iface` is `I` (LANG-103). -/
theorem checkProduces_iface {D : Type} {ℓ : Label} {e : Effect} {calls : List (Body D)} {I : Ty}
    (h : checkProduces ℓ e calls = .ok ()) (hI : e.produces = some I) :
    ∀ b ∈ calls, ∀ B, pkgBytesOf b = some B → ∀ p, Wire.decodePackage B = .ok p → p.iface = I := by
  intro b hb B hB p hp
  unfold checkProduces at h
  rw [hI] at h
  simp only at h
  generalize hf : List.find? _ calls = r at h
  cases r with
  | none =>
    have := List.find?_eq_none.mp hf b hb
    simp only [hB, hp] at this
    simpa using this
  | some c => simp only at h; split at h <;> cases h

theorem checkEffect_produces {D : Type} {ℓ : Label} {e : Effect} {calls : List (Body D)}
    (h : checkEffect ℓ e calls = .ok ()) : checkProduces ℓ e calls = .ok () := by
  unfold checkEffect at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  · exact h

/-- **A returned run's calls are within its setup's grade.** -/
theorem runMeasuredWith_moves_le {D : Type} [DecidableEq D] {bytesOf : D → ByteArray} {digestOf : ByteArray → Option D}
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
  exact ⟨S, hS, checkMoves_le (checkEffect_moves ‹checkEffect _ _ _ = .ok _›)⟩

/-- **A returned run moves at most the grade its package declares for the method** (LANG-89's
theorem): for the deployed setup, the resolved method `ℓ` of the loaded package `p` has
`movesOf calls ≤ (p.effectOf ℓ).moves`. -/
theorem runMeasured_moves_le {D : Type} [DecidableEq D] {bytesOf : D → ByteArray} {digestOf : ByteArray → Option D}
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

/-- A returned run had `checkProduces` admit its calls, for its setup's grade. -/
theorem runMeasuredWith_produces {D : Type} [DecidableEq D] {bytesOf : D → ByteArray} {digestOf : ByteArray → Option D}
    {setup : Pinned D → RowView D → D → Kernel.Slots → Nat → ByteArray → Req D → Except (Refusal D) RunSetup}
    {look : Pinned D} {rv : RowView D} {pkg : D} {state : Kernel.Slots} {method : Nat} {args : ByteArray}
    {r : Req D} {budget : Nat} {s : Kernel.Slots} {calls : List (Body D)}
    {rows : List (Kernel.RowSlot D × Kernel.RowAct)} {t n : Nat}
    (h : runMeasuredWith bytesOf digestOf setup look rv pkg state method args r budget = .ok (s, calls, rows, t, n)) :
    ∃ S, setup look rv pkg state method args r = .ok S ∧ checkProduces S.label S.effect calls = .ok () := by
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
  exact ⟨S, hS, checkEffect_produces ‹checkEffect _ _ _ = .ok _›⟩

/-- **A returned run installs only packages of the interface its method declares it produces**
(LANG-103): for the deployed setup, if the resolved method `ℓ` of the loaded package `p` declares
`produces I`, every `install` and `createOf` among the run's calls whose bytes decode carries a
package whose interface is exactly `I`. Bytes that do not decode are refused by the kernel's own
install check (`checkInstall`), so no package of another interface is installed by the run. -/
theorem runMeasured_produces {D : Type} [DecidableEq D] {bytesOf : D → ByteArray} {digestOf : ByteArray → Option D}
    {rc : ReceiptCheck} {loader : Pinned D → Nat → ByteArray → Loaded → Except (Refusal D) (Loaded × Nat)}
    {charge : Loaded → Nat} {look : Pinned D} {rv : RowView D} {pkg : D} {state : Kernel.Slots} {method : Nat}
    {args : ByteArray} {r : Req D} {budget : Nat} {s : Kernel.Slots} {calls : List (Body D)}
    {rows : List (Kernel.RowSlot D × Kernel.RowAct)} {t n : Nat}
    (h : runMeasuredWith bytesOf digestOf (runSetupWith bytesOf digestOf rc loader charge) look rv pkg state method args r budget =
      .ok (s, calls, rows, t, n)) :
    ∃ (L : Loaded) (g : Nat) (p : Package) (ℓ : Label) (sg : Sig),
      loader look closureDepthMax (bytesOf pkg) ⟨[], [], []⟩ = .ok (L, g) ∧ L.pkgs[g]? = some p ∧
      resolveMethod (D := D) p method = .ok (ℓ, sg) ∧
      ∀ I, (p.effectOf ℓ).produces = some I → ∀ b ∈ calls, ∀ B, pkgBytesOf b = some B →
        ∀ q, Wire.decodePackage B = .ok q → q.iface = I := by
  obtain ⟨S, hS, hm⟩ := runMeasuredWith_produces h
  obtain ⟨L, g, p, ℓ, sg, sd, ad, wd, -, hL, hp, hres, -, -, -, -, hE⟩ := runSetupWith_spec hS
  refine ⟨L, g, p, ℓ, sg, hL, hp, hres, fun I hI => checkProduces_iface hm ?_⟩
  rw [hE]; exact hI

end Nanodregg.Lang
