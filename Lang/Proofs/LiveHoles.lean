/-
# Lang.Proofs.LiveHoles — the live contextual runtime: typing, allocation, sources, cost

The live runtime's typing, allocation and authenticated-source invariants (`selectHole_origin`, `holeRow_authenticated`,
`instantiateHoles_typed`, `loadLive_checked`); and its preparation charge (`instantiateHoles_cost`).
Subject: `Lang.LiveHoles`, in the Host closure. The live invoke is `Lang.Proofs.LiveInvoke`; the WASTE need of
`runMeasuredLive` is `Lang.Proofs.LiveNeed` (it sits above `Lang.Proofs.Provenance`).
-/
import Lang.Proofs.Load
import Lang.Proofs.HoleBudget
import Lang.Proofs.Run

namespace Nanodregg.Lang

/-! ## From `Lang.Proofs.Contextual.LiveHoles`: The live runtime's typing, allocation and authenticated-source invariants. -/
section

open Nanodregg.Kernel Nanodregg.Kernel.Receive

theorem checkContextual_shape {Δ : List Ty} {p : Package}
    (h : p.checkContextual Δ = .ok ()) :
    p.checkShape = .ok () ∧ p.checkFields = .ok () := by
  unfold Package.checkContextual at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  repeat' split at h
  all_goals first | (simp at h; done) | skip
  all_goals exact ⟨‹_›, ‹_›⟩

/-- Every successful lookup is one of the caller's authenticated point rows,
at the requested key, including a pinned absence. -/
theorem holeRow_authenticated {D : Type} {rv : RowView D} {self : D}
    {rel : Nat} {key : ByteArray} {leaf : Option RowLeaf}
    (h : holeRow rv self rel key = .ok leaf) :
    (key, leaf) ∈ rv.points self rel := by
  unfold holeRow at h
  cases hf : (rv.points self rel).find? (fun p => decide (p.1 = key)) with
  | none => simp [hf] at h
  | some p =>
    obtain ⟨k, v⟩ := p
    simp only [hf, Except.ok.injEq] at h
    subst v
    have hk := List.find?_some hf
    simp only [decide_eq_true_eq] at hk
    subst k
    exact List.mem_of_find?_eq_some hf

/-- A selected filling is literally code at the authenticated row's index.
Neither code nor the expected support versions come from the caller. -/
theorem selectHole_origin {D : Type} {rv : RowView D} {self : D} {h : HoleROM} {s : HoleSelection}
    (hs : selectHole rv self h = .ok s) :
    ∃ c amount bytes,
      holeRow rv self h.selectionRel h.selectionKey = .ok (some (.row amount bytes s.version)) ∧
      Wire.decodeData .nat bytes = .ok (.nat s.index) ∧
      h.code[s.index]? = some c ∧ s.original = c.body ∧
      c.supports.all (holePinHolds rv self) = true := by
  unfold selectHole at hs
  simp only [bind, Except.bind, pure, Except.pure] at hs
  repeat' split at hs
  all_goals first | (simp at hs; done) | skip
  simp only [Except.ok.injEq] at hs
  subst s
  exact ⟨_, _, _, ‹_›, ‹_›, ‹_›, rfl, ‹_›⟩

/-- Blocked code cannot be mistaken for an authenticated selection receipt. -/
theorem blocked_has_no_receipt (n : Nat) (T : Ty) (why : String) :
    (HoleResolution.blocked n T why).receipt = none := rfl

/-- Resolution preserves the exact refusal returned by fresh authentication.
This equation names the transient term that fillRefs substitutes. -/
theorem resolveHole_refusal {D : Type} {rv : RowView D} {self : D} {h : HoleROM} {why : String}
    (he : selectHole rv self h = .error why) :
    (resolveHole rv self h).body = .refuse h.ty why.toUTF8 ∧
      (resolveHole rv self h).receipt = none := by
  simp [resolveHole, he, HoleResolution.body, HoleResolution.receipt]

/-- Demanding the blocked term fires that same named refusal in one machine step. -/
theorem blocked_step (n : Nat) (T : Ty) (why : String) (lib : List Term) (env : Env) :
    step lib (State.init (HoleResolution.blocked n T why).body env) =
      .fault (.refused why.toUTF8) := rfl

/-- Successful bounded contextual preparation is closed and typed at the
unchanged interface, and its actual allocated syntax is within the bound. -/
theorem instantiateHoles_typed {D : Type} {rv : RowView D} {self : D}
    {Δ : List Ty} {p : Package} {i : HoleInstance}
    (h : instantiateHoles rv self Δ p = .ok i) :
    HasType Δ [] i.body p.iface ∧ Term.nodes i.body ≤ Wire.nodeMax := by
  unfold instantiateHoles at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  repeat' split at h
  all_goals first | (simp at h; done) | skip
  all_goals
    simp only [Except.ok.injEq] at h
    subst i
    exact ⟨checkE_ok_iff.mp ‹_›, (fillBounded_bounds ‹_›).1⟩

/-- The instantiated body introduces no digest literal outside the template
and the actual selected ROM candidates. This binds provenance to this run's
selection receipts rather than arbitrary code in the package. -/
theorem instantiateHoles_sources {D : Type} {rv : RowView D} {self : D}
    {Δ : List Ty} {p : Package} {i : HoleInstance}
    (h : instantiateHoles rv self Δ p = .ok i) :
    ∀ b ∈ i.body.digestLits,
      b ∈ p.body.digestLits ++ i.selections.flatMap (fun s => s.original.digestLits) := by
  unfold instantiateHoles at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  repeat' split at h
  all_goals first | (simp at h; done) | skip
  all_goals
    simp only [Except.ok.injEq] at h
    subst i
    intro b hb
    have ha : List.all _ _ = true := ‹_›
    have he := List.all_eq_true.mp ha b hb
    simp only [List.any_eq_true, decide_eq_true_eq] at he
    obtain ⟨a, hm, rfl⟩ := he
    exact hm

/-- A guard cannot consume more ticks than its fixed invocation allowance. -/
theorem runHoleGuard_cost {D : Type} {rv : RowView D} {self : D} {h : HoleROM} {used : Nat}
    (hr : runHoleGuard rv self h = .ok used) : used ≤ 256 := by
  unfold runHoleGuard at hr
  simp only [bind, Except.bind, pure, Except.pure] at hr
  repeat' split at hr
  all_goals first | (simp at hr; done) | skip
  all_goals
    cases hr
    have hb := run_used_le (lib := []) (cap := Bounds.stackMax) 256
      (State.init h.guard [.bool (h.guardPin.all (holePinHolds rv self))])
    rw [‹run _ _ _ _ _ = _›] at hb
    exact hb



theorem admitContextual_inv {D : Type} {digestOf : ByteArray → Option D}
    {prepare : List Ty → Package → Except String Term}
    {idb : ByteArray} {p : Package} {acc L : Loaded} {gis : List Nat} {g : Nat}
    (hi : Inv acc) (hpw : Wire.packageWire p = true)
    (h : admitContextual digestOf prepare idb p acc gis = .ok (L, g)) :
    Inv L ∧ g < L.pkgs.length ∧ L.pkgs = acc.pkgs ++ [p] := by
  unfold admitContextual at h
  split at h
  · exact admitPackage_inv hi hpw h
  ·
    obtain ⟨hids, hlib, hty, hck⟩ := hi
    split at h
    · simp at h
    · rename_i ifs hifs
      split at h
      · simp at h
      · rename_i hc
        split at h
        · simp at h
        · rename_i body hprepare
          split at h
          · simp at h
          · rename_i htcheck
            split at h
            ·
              simp only [Except.ok.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              have hΔ : Loaded.ifaces ⟨acc.ids ++ [idb], acc.lib ++ [body.relocate fun i => gis.getD i 0],
                  acc.pkgs ++ [p]⟩ = Loaded.ifaces acc ++ [p.iface] := by simp [Loaded.ifaces]
              refine ⟨⟨by simp [hids], by simp [hlib], ?_, ?_⟩, by simp [hids], rfl⟩
              rotate_left
              · intro i P hP
                simp only at hP
                by_cases lt : i < acc.pkgs.length
                · rw [List.getElem?_append_left lt] at hP; exact hck i P hP
                · rw [List.getElem?_append_right (by omega)] at hP
                  have e1 : i - acc.pkgs.length = 0 := by
                    cases h' : i - acc.pkgs.length with
                    | zero => rfl
                    | succ k => rw [h'] at hP; simp at hP
                  rw [e1] at hP; simp at hP; subst hP
                  exact ⟨(checkContextual_shape hc).1, (checkContextual_shape hc).2, hpw⟩
              intro i t P ht hP
              rw [hΔ]
              simp only at ht hP
              by_cases lt : i < acc.lib.length
              · rw [List.getElem?_append_left lt] at ht
                rw [List.getElem?_append_left (by omega)] at hP
                exact (hty i t P ht hP).weaken _
              · rw [List.getElem?_append_right (by omega)] at ht
                rw [List.getElem?_append_right (by omega)] at hP
                have e1 : i - acc.lib.length = 0 := by
                  cases h' : i - acc.lib.length with
                  | zero => rfl
                  | succ k => rw [h'] at ht; simp at ht
                rw [e1] at ht; rw [hlib] at e1; rw [e1] at hP
                simp at ht hP; subst ht; subst hP
                have hb := checkE_ok_iff.mp htcheck
                exact relocate_typed (fun i A hA => getElem?_append_of_some (ifacesAt_spec hifs i A hA)) hb
            · simp at h
            · simp at h

section
variable {D : Type} (digestOf : ByteArray → Option D) (look : Pinned D)
  (admit : ByteArray → Package → Loaded → List Nat → Except (Refusal D) (Loaded × Nat))

mutual
theorem loadUsing_inv (hadmit : ∀ {idb p acc gis L g}, Inv acc → Wire.packageWire p = true →
    admit idb p acc gis = .ok (L, g) →
    Inv L ∧ g < L.pkgs.length ∧ L.pkgs = acc.pkgs ++ [p]) (fuel : Nat) (idb : ByteArray) (acc : Loaded) {L : Loaded} {g : Nat}
    (hi : Inv acc) (h : loadUsing digestOf admit look fuel idb acc = .ok (L, g)) :
    Inv L ∧ g < L.pkgs.length ∧ ∃ ext, L.pkgs = acc.pkgs ++ ext := by
  unfold loadUsing at h
  split at h
  · rename_i i hidx
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨hi, hi.1 ▸ indexIn_lt hidx, [], by simp⟩
  · split at h
    · simp at h
    · rename_i fuel
      split at h
      · simp at h
      · split at h
        · simp at h
        · rename_i p hrp
          split at h
          · simp at h
          · rename_i acc' gis hall
            obtain ⟨hi', _, ext, hext⟩ := loadAllUsing_inv hadmit fuel p.imports acc hi hall
            obtain ⟨hL, hg, hp⟩ := hadmit hi' (readPackage_wire hrp) h
            exact ⟨hL, hg, ext ++ [p], by rw [hp, hext, List.append_assoc]⟩
termination_by (fuel, 0)

theorem loadAllUsing_inv (hadmit : ∀ {idb p acc gis L g}, Inv acc → Wire.packageWire p = true →
    admit idb p acc gis = .ok (L, g) →
    Inv L ∧ g < L.pkgs.length ∧ L.pkgs = acc.pkgs ++ [p]) (fuel : Nat) (ds : List ByteArray) (acc : Loaded) {L : Loaded}
    {gs : List Nat} (hi : Inv acc) (h : loadAllUsing digestOf admit look fuel ds acc = .ok (L, gs)) :
    Inv L ∧ (∀ g ∈ gs, g < L.pkgs.length) ∧ ∃ ext, L.pkgs = acc.pkgs ++ ext := by
  unfold loadAllUsing at h
  split at h
  · simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨hi, by simp, [], by simp⟩
  · rename_i d ds
    split at h
    · simp at h
    · rename_i acc1 g1 h1
      split at h
      · simp at h
      · rename_i acc2 gs2 h2
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨hi1, hg1, e1, he1⟩ := loadUsing_inv hadmit fuel d acc hi h1
        obtain ⟨hi2, hg2, e2, he2⟩ := loadAllUsing_inv hadmit fuel ds acc1 hi1 h2
        refine ⟨hi2, ?_, e1 ++ e2, by rw [he2, he1, List.append_assoc]⟩
        intro g hg
        simp only [List.mem_cons] at hg
        rcases hg with rfl | hg
        · rw [he2]; simp; omega
        · exact hg2 g hg
termination_by (fuel, ds.length + 1)
end
end

/-- Every live invocation library is closed and typed, despite its ROM's open
templates. The result concerns the library actually given to the machine. -/
theorem loadLive_libTy {D : Type} {digestOf : ByteArray → Option D}
    {rv : RowView D} {self : D} {look : Pinned D} {fuel : Nat} {idb : ByteArray}
    {L : Loaded} {g : Nat}
    (h : loadLive digestOf rv self look fuel idb ⟨[], [], []⟩ = .ok (L, g)) :
    LibTy (Loaded.ifaces L) L.lib ∧ g < L.pkgs.length := by
  obtain ⟨⟨_, hlib, hty, _⟩, hg, _⟩ :=
    loadUsing_inv digestOf look _ (fun hi hw ha => admitContextual_inv hi hw ha) fuel idb _ Inv.empty h
  refine ⟨fun i T hT => ?_, hg⟩
  simp only [Loaded.ifaces, List.getElem?_map, Option.map_eq_some_iff] at hT
  obtain ⟨P, hP, rfl⟩ := hT
  have hi : i < L.lib.length := by rw [hlib]; exact (List.getElem?_eq_some_iff.mp hP).1
  exact ⟨L.lib[i], List.getElem?_eq_getElem hi, hty i _ P (List.getElem?_eq_getElem hi) hP⟩


theorem loadLive_checked {D : Type} {digestOf : ByteArray → Option D}
    {rv : RowView D} {self : D} {look : Pinned D} {fuel : Nat} {idb : ByteArray}
    {L : Loaded} {g : Nat}
    (h : loadLive digestOf rv self look fuel idb ⟨[], [], []⟩ = .ok (L, g)) :
    ∀ (i : Nat) (p : Package), L.pkgs[i]? = some p →
      p.checkShape = .ok () ∧ p.checkFields = .ok () ∧ Wire.packageWire p = true :=
  (loadUsing_inv digestOf look _ (fun hi hw ha => admitContextual_inv hi hw ha)
    fuel idb _ Inv.empty h).1.2.2.2

end

/-! ## From `Lang.Proofs.Contextual.LiveCost`: Live preparation is charged from its committed ROM, including blocked holes. -/
section

theorem factor_fold_nodes (xs : List Nat) (Γ : List Ty) (t : Term) :
    Term.nodes ((xs.foldl (fun (a : List Ty × Term) x =>
      (a.1.eraseIdx x, Term.renameVar (lowerIdx x) a.2)) (Γ, t)).2) = Term.nodes t := by
  induction xs generalizing Γ t with
  | nil => rfl
  | cons x xs ih =>
    rw [List.foldl_cons, ih, renameVar_nodes]

theorem factorHole_nodes (h : HoleROM) (c : HoleCode) (removed : List Nat) :
    Term.nodes (factorHole h c removed).2.1 = Term.nodes c.body :=
  factor_fold_nodes removed.reverse h.ctx c.body

theorem selectHole_nodes {D : Type} {rv : Kernel.Receive.RowView D} {self : D}
    {h : HoleROM} {s : HoleSelection} (hs : selectHole rv self h = .ok s) :
    Term.nodes s.body = Term.nodes s.original := by
  unfold selectHole at hs
  simp only [bind, Except.bind, pure, Except.pure] at hs
  repeat' split at hs
  all_goals first | (simp at hs; done) | skip
  simp only [Except.ok.injEq] at hs
  subst s
  rw [renameVar_nodes]
  exact factorHole_nodes _ _ _

theorem foldMax_start {α : Type} (f : α → Nat) (xs : List α) (n : Nat) :
    n ≤ xs.foldl (fun n a => max n (f a)) n := by
  induction xs generalizing n with
  | nil => exact Nat.le_refl n
  | cons x xs ih => exact Nat.le_trans (Nat.le_max_left _ _) (ih _)

theorem foldMax_member {α : Type} (f : α → Nat) (xs : List α) (n : Nat)
    (a : α) (ha : a ∈ xs) : f a ≤ xs.foldl (fun n a => max n (f a)) n := by
  induction xs generalizing n with
  | nil => simp at ha
  | cons x xs ih =>
    simp only [List.mem_cons] at ha
    rcases ha with rfl | ha
    · exact Nat.le_trans (Nat.le_max_right _ _) (foldMax_start f xs _)
    · exact ih _ ha

theorem foldMax_le {α : Type} (f : α → Nat) (xs : List α) (n m : Nat)
    (hn : n ≤ m) (hx : ∀ a ∈ xs, f a ≤ m) :
    xs.foldl (fun n a => max n (f a)) n ≤ m := by
  induction xs generalizing n with
  | nil => exact hn
  | cons x xs ih =>
    exact ih _ (Nat.max_le.mpr ⟨hn, hx x (by simp)⟩)
      (fun a ha => hx a (by simp [ha]))

/-- Selected code retains the ROM candidate's size through strengthening;
a blocked refusal has one node. Both fit the same committed maximum. -/
theorem resolutionMax_committed {D : Type} (rv : Kernel.Receive.RowView D) (self : D)
    (hs : List HoleROM) :
    resolutionMax (hs.map (resolveHole rv self)) ≤
      (hs.flatMap (fun h => h.code)).foldl (fun n c => max n (Term.nodes c.body)) 1 := by
  apply foldMax_le
  · exact foldMax_start _ _ _
  · intro r hr
    obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hr
    cases he : selectHole rv self h with
    | error why =>
      simp only [resolveHole, he, HoleResolution.body, Term.nodes]
      exact foldMax_start _ _ _
    | ok s =>
      simp only [resolveHole, he, HoleResolution.body]
      rw [selectHole_nodes he]
      obtain ⟨c, _, _, _, _, hc, horig, _⟩ := selectHole_origin he
      rw [horig]
      exact foldMax_member (fun c : HoleCode => Term.nodes c.body) _ 1 c (List.mem_flatMap.mpr
        ⟨h, hh, List.mem_of_getElem? hc⟩)

/-- The actual selected/blocked expansion and all signature-guard allowances
fit the preparation charged by the deployed loader from the original ROM. -/
theorem instantiateHoles_cost {D : Type} {rv : Kernel.Receive.RowView D} {self : D}
    {Δ : List Ty} {p : Package} {i : HoleInstance}
    (h : instantiateHoles rv self Δ p = .ok i) :
    i.cost ≤ p.preparationCost := by
  have hc : i.cost = if p.holes.isEmpty then 0 else
      Term.nodes p.body * (resolutionMax (p.holes.map (resolveHole rv self)) + 1) +
        256 * p.holes.length := by
    unfold instantiateHoles at h
    simp only [bind, Except.bind, pure, Except.pure] at h
    repeat' split at h
    all_goals first | (simp at h; done) | skip
    all_goals
      simp only [Except.ok.injEq] at h
      subst i
      simp_all
  rw [hc, Package.preparationCost]
  split
  · exact Nat.le_refl 0
  · have hm := resolutionMax_committed rv self p.holes
    have hmul := Nat.mul_le_mul_left (Term.nodes p.body) (Nat.add_le_add_right hm 1)
    simpa only [Nat.add_comm] using Nat.add_le_add_right hmul (256 * p.holes.length)

end

end Nanodregg.Lang
