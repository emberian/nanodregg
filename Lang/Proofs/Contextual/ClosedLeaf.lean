import Lang.Proofs.Contextual.ClosedDeployment

namespace Nanodregg.Lang
open Nanodregg.Kernel Nanodregg.Kernel.Receive

/-- A closed leaf ROM is admitted identically, including any boundary refusal. -/
theorem loadUsing_leaf_closed {D : Type} {bytesOf : D → ByteArray}
    {digestOf : ByteArray → Option D} {look : Pinned D} {pkg : D} {p : Package}
    (hid : digestOf (bytesOf pkg) = some pkg) (hp : readPackage look pkg = .ok p)
    (hi : p.imports = []) (hc : p.holes = [])
    (prepare : List Ty → Package → Except String Term) (fuel : Nat) :
    loadUsing digestOf (admitContextual digestOf prepare) look (fuel + 1)
      (bytesOf pkg) ⟨[], [], []⟩ =
    load digestOf look (fuel + 1) (bytesOf pkg) ⟨[], [], []⟩ := by
  unfold load
  rw [loadUsing.eq_def, loadUsing.eq_def]
  simp only [indexIn, idOf, hid, hp, hi]
  rw [loadAllUsing.eq_def, loadAllUsing.eq_def]
  exact admitContextual_closed digestOf prepare _ _ _ _ hc

/-- Empty-signature, no-import packages have identical setups on the live path.
No success or closure assumption is imposed on their callers. -/
theorem runSetupLive_leaf_closed {D : Type} {bytesOf : D → ByteArray}
    {digestOf : ByteArray → Option D} {look : Pinned D} {pkg : D} {p : Package}
    (hid : digestOf (bytesOf pkg) = some pkg) (hp : readPackage look pkg = .ok p)
    (hi : p.imports = []) (hc : p.holes = [])
    (rv : RowView D) (state : Slots) (method : Nat) (args : ByteArray) (r : Req D) :
    runSetupLive bytesOf digestOf look rv pkg state method args r =
      runSetup bytesOf digestOf look rv pkg state method args r := by
  have hl := loadUsing_leaf_closed hid hp hi hc
    (fun Δ p => (instantiateHoles rv r.self Δ p).map (·.body)) (closureDepthMax - 1)
  change loadLive digestOf rv r.self look closureDepthMax (bytesOf pkg) ⟨[], [], []⟩ =
    load digestOf look closureDepthMax (bytesOf pkg) ⟨[], [], []⟩ at hl
  unfold runSetupLive runSetup runSetupWith
  rw [hl]
  cases hr : reqOk bytesOf r <;> simp only [Bool.false_eq_true, if_false, if_true, bind, Except.bind, pure, Except.pure]
  cases hload : load digestOf look closureDepthMax (bytesOf pkg) ⟨[], [], []⟩ with
  | error e => rfl
  | ok x =>
    obtain ⟨L, g⟩ := x
    have hz := (loadLive_of_load rv r.self hload).2
    simp only [hz]

/-- The full measured result, including failures and charged ticks, is unchanged. -/
theorem runMeasuredLive_leaf_closed {D : Type} {bytesOf : D → ByteArray}
    {digestOf : ByteArray → Option D} {look : Pinned D} {pkg : D} {p : Package}
    (hid : digestOf (bytesOf pkg) = some pkg) (hp : readPackage look pkg = .ok p)
    (hi : p.imports = []) (hc : p.holes = [])
    (rv : RowView D) (state : Slots) (method : Nat) (args : ByteArray) (r : Req D) (budget : Nat) :
    runMeasuredLive bytesOf digestOf look rv pkg state method args r budget =
      runMeasured bytesOf digestOf look rv pkg state method args r budget := by
  unfold runMeasuredLive runMeasured runMeasuredWith
  rw [runSetupLive_leaf_closed hid hp hi hc]

/-- A closed leaf's law is identical on contextual deployment, even when it refuses. -/
theorem judgeOneContextual_leaf_closed {D : Type} {bytesOf : D → ByteArray}
    {digestOf : ByteArray → Option D} {look : Pinned D} {pkg : D} {p : Package}
    (hid : digestOf (bytesOf pkg) = some pkg) (hp : readPackage look pkg = .ok p)
    (hi : p.imports = []) (hc : p.holes = [])
    (old new : Slots) (r : Req D) :
    judgeOneWith bytesOf digestOf (loadContextual digestOf) look pkg old new r =
      judgeOne bytesOf digestOf look pkg old new r := by
  have hl := loadUsing_leaf_closed hid hp hi hc (fun _ => unresolvedBody) (closureDepthMax - 1)
  change loadContextual digestOf look closureDepthMax (bytesOf pkg) ⟨[], [], []⟩ =
    load digestOf look closureDepthMax (bytesOf pkg) ⟨[], [], []⟩ at hl
  simp only [judgeOne, judgeOneWith, hl]

end Nanodregg.Lang
