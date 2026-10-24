/-
# Lang.Proofs.LiveClosed — closed packages under the live loader

When a package has no holes the live loader is the closed loader (`program_run_closed`, `runMeasuredLive_closed`, …),
and the leaf forms Kernel and Ledger witnesses consume (`judgeOneContextual_leaf_closed`, `runMeasuredLive_leaf_closed`).
-/
import Lang.Proofs.LiveHoles

namespace Nanodregg.Lang

/-! ## From `Lang.Proofs.Contextual.ClosedDeployment`: Closed packages keep their exact admission and execution under live deployment. -/
section

open Nanodregg.Kernel Nanodregg.Kernel.Receive

/-- The closed admission already excludes every contextual signature. -/
theorem admitPackage_closed {D : Type} {digestOf : ByteArray → Option D}
    {idb : ByteArray} {p : Package} {acc L : Loaded} {gis : List Nat} {g : Nat}
    (h : admitPackage digestOf idb p acc gis = .ok (L, g)) :
    p.holes = [] ∧ L.pkgs = acc.pkgs ++ [p] := by
  unfold admitPackage at h
  repeat' split at h
  all_goals first | (cases h; done) | skip
  simp only [Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨(checkWith_closed ‹_›).1, rfl⟩

theorem admitContextual_closed {D : Type} (digestOf : ByteArray → Option D)
    (prepare : List Ty → Package → Except HoleRefusal Term)
    (idb : ByteArray) (p : Package) (acc : Loaded) (gis : List Nat)
    (hc : p.holes = []) :
    admitContextual digestOf prepare idb p acc gis = admitPackage digestOf idb p acc gis := by
  simp only [admitContextual, hc, List.isEmpty_nil, if_true]

section
variable {D : Type} (digestOf : ByteArray → Option D) (rc : ReceiptCheck) (look : Pinned D)
  (prepare : List Ty → Package → Except HoleRefusal Term)

mutual
/-- A successfully loaded closed closure is admitted identically by live loading.
The closure property is derived from admission, never added to the old load contract. -/
theorem load_closed_live (fuel : Nat) (idb : ByteArray) (acc : Loaded) {L : Loaded} {g : Nat}
    (ha : ∀ p ∈ acc.pkgs, p.holes = [])
    (h : load digestOf look fuel idb acc = .ok (L, g)) :
    loadUsing digestOf (admitContextual digestOf prepare) look fuel idb acc = .ok (L, g) ∧
      ∀ p ∈ L.pkgs, p.holes = [] := by
  change loadUsing digestOf (admitPackage digestOf) look fuel idb acc = _ at h
  unfold loadUsing at h ⊢
  split at h
  · rename_i i hi
    cases h
    exact ⟨rfl, ha⟩
  · rename_i hi
    split at h
    · cases h
    · rename_i fuel
      split at h
      · cases h
      · rename_i id hid
        split at h
        · cases h
        · rename_i p hp
          split at h
          · cases h
          · rename_i acc' gis hall
            obtain ⟨hall', hc⟩ := loadAll_closed_live fuel p.imports acc ha hall
            simp only [hall']
            obtain ⟨hpc, hext⟩ := admitPackage_closed h
            refine ⟨?_, ?_⟩
            · rw [admitContextual_closed digestOf prepare _ _ _ _ hpc]; exact h
            · rw [hext]
              intro q hq
              rcases List.mem_append.mp hq with hq | hq
              · exact hc q hq
              · obtain rfl := List.mem_singleton.mp hq
                exact hpc
termination_by (fuel, 0)

theorem loadAll_closed_live (fuel : Nat) (ds : List ByteArray) (acc : Loaded)
    {L : Loaded} {gs : List Nat}
    (ha : ∀ p ∈ acc.pkgs, p.holes = [])
    (h : loadAll digestOf look fuel ds acc = .ok (L, gs)) :
    loadAllUsing digestOf (admitContextual digestOf prepare) look fuel ds acc = .ok (L, gs) ∧
      ∀ p ∈ L.pkgs, p.holes = [] := by
  change loadAllUsing digestOf (admitPackage digestOf) look fuel ds acc = _ at h
  unfold loadAllUsing at h ⊢
  split at h
  · cases h; exact ⟨rfl, ha⟩
  · rename_i d ds
    split at h
    · cases h
    · rename_i acc1 g1 h1
      obtain ⟨h1', hc1⟩ := load_closed_live fuel d acc ha h1
      simp only [h1']
      split at h
      · cases h
      · rename_i acc2 gs2 h2
        obtain ⟨h2', hc2⟩ := loadAll_closed_live fuel ds acc1 hc1 h2
        simp only [h2']
        cases h; exact ⟨rfl, hc2⟩
termination_by (fuel, ds.length + 1)
end
end

theorem Loaded.preparationCost_closed (L : Loaded) (hc : ∀ p ∈ L.pkgs, p.holes = []) :
    L.preparationCost = 0 := by
  unfold Loaded.preparationCost
  have hm : L.pkgs.map Package.preparationCost = L.pkgs.map (fun _ => 0) := by
    apply List.map_congr_left
    intro p hp
    simp [Package.preparationCost, Package.holeCharge, hc p hp]
  rw [hm]
  have hz : ∀ (ps : List Package) (n : Nat),
      ((ps.map (fun _ => 0)).foldl (· + ·) n) = n := by
    intro ps n
    induction ps generalizing n with
    | nil => rfl
    | cons p ps ih => simpa using ih n
  exact hz _ 0

/-- Closed admission implies the same live library, with zero preparation charge. -/
theorem loadLive_of_load {D : Type} {digestOf : ByteArray → Option D}
    (rv : RowView D) (self : D) {look : Pinned D} {fuel : Nat} {idb : ByteArray}
    {L : Loaded} {g : Nat}
    (h : load digestOf look fuel idb ⟨[], [], []⟩ = .ok (L, g)) :
    loadLive digestOf rv self look fuel idb ⟨[], [], []⟩ = .ok (L, g) ∧
      L.preparationCost = 0 := by
  obtain ⟨hl, hc⟩ := load_closed_live digestOf look
    (fun Δ p => (instantiateHoles digestOf look rv self Δ p).map (·.body)) fuel idb _ (by simp) h
  exact ⟨hl, Loaded.preparationCost_closed L hc⟩

/-- Every successful closed setup is byte-for-byte the setup used by live deployment. -/
theorem runSetupLive_of_runSetup {D : Type}
    {bytesOf : D → ByteArray} {digestOf : ByteArray → Option D} {rc : Lang.ReceiptCheck}
    {look : Pinned D} {rv : RowView D} {pkg : D} {state : Slots} {method : Nat}
    {args : ByteArray} {r : Req D} {S : RunSetup}
    (h : runSetup bytesOf digestOf rc look rv pkg state method args r = .ok S) :
    runSetupLive bytesOf digestOf rc look rv pkg state method args r = .ok S := by
  unfold runSetup runSetupWith at h
  unfold runSetupLive runSetupWith
  simp only [bind, Except.bind, pure, Except.pure] at h ⊢
  split at h
  · rename_i hreq
    rw [if_pos hreq]
    split at h
    · cases h
    · rename_i L g hl
      obtain ⟨hlive, hcost⟩ := loadLive_of_load rv r.self hl
      rw [hlive]
      simp only [hcost]
      exact h
  · cases h

/-- Same result, refusal, calls, edits and ticks for every budget after a closed setup. -/
theorem runMeasuredLive_closed {D : Type}
    {bytesOf : D → ByteArray} {digestOf : ByteArray → Option D} {rc : Lang.ReceiptCheck}
    {look : Pinned D} {rv : RowView D} {pkg : D} {state : Slots} {method : Nat}
    {args : ByteArray} {r : Req D} {S : RunSetup}
    (h : runSetup bytesOf digestOf rc look rv pkg state method args r = .ok S) (budget : Nat) :
    runMeasuredLive bytesOf digestOf rc look rv pkg state method args r budget =
      runMeasured bytesOf digestOf rc look rv pkg state method args r budget := by
  simp only [runMeasuredLive, runMeasured, runMeasuredWith,
    runSetupLive_of_runSetup h, h, bind, Except.bind]

/-- The actual deployed Program.run preserves the entire closed result, including ticks. -/
theorem program_run_closed {D : Type}
    {bytesOf : D → ByteArray} {digestOf : ByteArray → Option D} {rc : Lang.ReceiptCheck}
    {look : Pinned D} {rv : RowView D} {pkg : D} {state : Slots} {method : Nat}
    {args : ByteArray} {r : Req D} {S : RunSetup}
    (h : runSetup bytesOf digestOf rc look rv pkg state method args r = .ok S) (budget : Nat) :
    (program bytesOf digestOf rc).run look rv pkg state method args r budget =
      (runMeasured bytesOf digestOf rc look rv pkg state method args r budget).map
        (fun x => (x.1, x.2.1, x.2.2.1, x.2.2.2.1)) := by
  change (runMeasuredLive bytesOf digestOf rc look rv pkg state method args r budget).map _ = _
  rw [runMeasuredLive_closed h]

/-- Law execution is identical once a closed closure loads, for any request or states. -/
theorem judgeOneContextual_closed {D : Type} (bytesOf : D → ByteArray)
    (digestOf : ByteArray → Option D) (look : Pinned D) (law : D)
    (old new : Slots) (r : Req D) {L : Loaded} {g : Nat}
    (h : load digestOf look closureDepthMax (bytesOf law) ⟨[], [], []⟩ = .ok (L, g)) :
    judgeOneWith bytesOf digestOf (loadContextual digestOf) look law old new r =
      judgeOne bytesOf digestOf look law old new r := by
  have hl := (load_closed_live digestOf look (fun _ => unresolvedBody)
    closureDepthMax (bytesOf law) ⟨[], [], []⟩ (by simp) h).1
  change loadContextual digestOf look closureDepthMax (bytesOf law) ⟨[], [], []⟩ = .ok (L, g) at hl
  simp only [judgeOne, judgeOneWith, hl, h]

end

/-! ## From `Lang.Proofs.Contextual.ClosedLeaf` -/
section

open Nanodregg.Kernel Nanodregg.Kernel.Receive

/-- A closed leaf ROM is admitted identically, including any boundary refusal. -/
theorem loadUsing_leaf_closed {D : Type} {bytesOf : D → ByteArray}
    {digestOf : ByteArray → Option D} {look : Pinned D} {pkg : D} {p : Package}
    (hid : digestOf (bytesOf pkg) = some pkg) (hp : readPackage look pkg = .ok p)
    (hi : p.imports = []) (hc : p.holes = [])
    (prepare : List Ty → Package → Except HoleRefusal Term) (fuel : Nat) :
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
    {digestOf : ByteArray → Option D} {rc : Lang.ReceiptCheck} {look : Pinned D} {pkg : D} {p : Package}
    (hid : digestOf (bytesOf pkg) = some pkg) (hp : readPackage look pkg = .ok p)
    (hi : p.imports = []) (hc : p.holes = [])
    (rv : RowView D) (state : Slots) (method : Nat) (args : ByteArray) (r : Req D) :
    runSetupLive bytesOf digestOf rc look rv pkg state method args r =
      runSetup bytesOf digestOf rc look rv pkg state method args r := by
  have hl := loadUsing_leaf_closed hid hp hi hc
    (fun Δ p => (instantiateHoles digestOf look rv r.self Δ p).map (·.body)) (closureDepthMax - 1)
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
    {digestOf : ByteArray → Option D} {rc : Lang.ReceiptCheck} {look : Pinned D} {pkg : D} {p : Package}
    (hid : digestOf (bytesOf pkg) = some pkg) (hp : readPackage look pkg = .ok p)
    (hi : p.imports = []) (hc : p.holes = [])
    (rv : RowView D) (state : Slots) (method : Nat) (args : ByteArray) (r : Req D) (budget : Nat) :
    runMeasuredLive bytesOf digestOf rc look rv pkg state method args r budget =
      runMeasured bytesOf digestOf rc look rv pkg state method args r budget := by
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

end

end Nanodregg.Lang
