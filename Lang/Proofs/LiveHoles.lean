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
Neither code nor the expected support versions come from the caller. Every support holds: a row
support at its ROM version, a cell support pinned and LIVE (E1, LANG-75.1). -/
theorem selectHole_origin {D : Type} {digestOf : ByteArray → Option D} {look : Pinned D} {rv : RowView D} {self : D} {h : HoleROM} {s : HoleSelection}
    (hs : selectHole digestOf look rv self h = .ok s) :
    ∃ c amount bytes,
      holeRow rv self h.selectionRel h.selectionKey = .ok (some (.row amount bytes s.version)) ∧
      Wire.decodeData .nat bytes = .ok (.nat s.index) ∧
      h.code[s.index]? = some c ∧ s.original = c.body ∧
      c.supports.all (supportLive digestOf look rv self) = true := by
  unfold selectHole at hs
  simp only [bind, Except.bind, pure, Except.pure] at hs
  repeat' split at hs
  all_goals first | (simp at hs; done) | skip
  simp only [Except.ok.injEq] at hs
  subst s
  exact ⟨_, _, _, ‹_›, ‹_›, ‹_›, rfl, ‹_›⟩

/-- **A selected candidate's cell supports are live** (E1, LANG-75.1): every `.cell id` support of
the selected candidate names a kernel cell the caller pinned and the World holds live. This is
not implied by `selectHole_origin` alone: under the mutation `supportLive (.cell _) := true` that
theorem still holds and this one fails. -/
theorem selectHole_cell_support {D : Type} {digestOf : ByteArray → Option D} {look : Pinned D}
    {rv : RowView D} {self : D} {h : HoleROM} {s : HoleSelection}
    (hs : selectHole digestOf look rv self h = .ok s) :
    ∃ c, h.code[s.index]? = some c ∧
      ∀ id, SupportPin.cell id ∈ c.supports → ∃ g cell, digestOf id = some g ∧ look g = .ok (some cell) := by
  obtain ⟨c, _, _, _, _, hc, _, hall⟩ := selectHole_origin hs
  refine ⟨c, hc, fun id hid => ?_⟩
  have hl := List.all_eq_true.mp hall _ hid
  simp only [supportLive] at hl
  cases hd : digestOf id with
  | none => simp [hd] at hl
  | some g =>
    simp only [hd, Option.any_some] at hl
    unfold cellLive at hl
    split at hl
    · exact ⟨g, _, rfl, ‹_›⟩
    · cases hl

/-- **A revoked support refuses by itself** (B1 at ROM grain, LANG-75.1): when the selection row
picks a candidate that cites a kernel cell the caller pinned at its tombstone (or absence), no
selection exists, the hole resolves blocked (no receipt), and demanding it faults with its named
refusal (`blocked_step`). The through-`submit` tooth is the journey row "P8.2 re-pinned tombstone". -/
theorem revoked_support_refused {D : Type} {digestOf : ByteArray → Option D} {look : Pinned D}
    {rv : RowView D} {self : D} {h : HoleROM} {amount : Nat} {bytes : ByteArray} {ver i : Nat}
    {c : HoleCode} {id : ByteArray} {g : D}
    (hrow : holeRow rv self h.selectionRel h.selectionKey = .ok (some (.row amount bytes ver)))
    (hdec : Wire.decodeData .nat bytes = .ok (.nat i)) (hc : h.code[i]? = some c)
    (hcell : SupportPin.cell id ∈ c.supports) (hg : digestOf id = some g) (hdead : look g = .ok none) :
    (∀ s, selectHole digestOf look rv self h ≠ .ok s) ∧
      (resolveHole digestOf look rv self h).receipt = none := by
  have hno : ∀ s, selectHole digestOf look rv self h ≠ .ok s := by
    intro s hs
    obtain ⟨c', amount', bytes', hrow', hdec', hc', _, _⟩ := selectHole_origin hs
    rw [hrow] at hrow'
    simp only [Except.ok.injEq, Option.some.injEq, RowLeaf.row.injEq] at hrow'
    obtain ⟨-, rfl, -⟩ := hrow'
    rw [hdec] at hdec'
    simp only [Except.ok.injEq, Data.nat.injEq] at hdec'
    subst hdec'
    obtain ⟨c'', hc'', hlive⟩ := selectHole_cell_support hs
    rw [hc] at hc''
    cases hc''
    obtain ⟨g', cell, hg', hl⟩ := hlive id hcell
    rw [hg] at hg'
    cases hg'
    rw [hdead] at hl
    cases hl
  refine ⟨hno, ?_⟩
  cases he : selectHole digestOf look rv self h with
  | ok s => exact absurd he (hno s)
  | error why => simp [resolveHole, he, HoleResolution.receipt]


/-! ## Selection over the hypotheses (C5, LANG-75.5): soundness and completeness of `selectHole`

`selectHole_hypotheses` says which hypotheses a selection strengthens away (exactly the dead ones) and that the
selected code uses none of them; `selectHole_live_selects` is the converse direction: when none of `selectHole`'s
refusal arms fires, it selects. With `selectHole_origin` they are the deployed judgment of a hole. The five teeth in
`Lang.Proofs.LiveJourney` (`kept_context`, `strengthening_factor`, `alternative_same_filling`, `replacement_filling`,
`used_hypothesis_suspends`) stay standalone closed instances: neither theorem mentions the factor's context or
filling, so they are not corollaries. -/

section HypothesisSelection
variable {D : Type} {digestOf : ByteArray → Option D} {look : Pinned D} {rv : RowView D} {self : D}

/-- The positions `changedHypotheses` strengthens: every observed hypothesis whose pin does not hold. -/
private def deadPositions (digestOf : ByteArray → Option D) (look : Pinned D) (rv : RowView D) (self : D)
    (zs : List (Option SupportPin × Nat)) : List Nat :=
  zs.filterMap fun pi => match pi.1 with
    | some p => if supportLive digestOf look rv self p then none else some pi.2
    | none => none

private theorem changed_fold (h : HoleROM) (c : HoleCode) :
    ∀ (zs : List (Option SupportPin × Nat)) (acc r : List Nat),
      zs.foldlM (hypothesisStep digestOf look rv self h c) acc = .ok r →
      r = acc ++ deadPositions digestOf look rv self zs ∧
      ∀ pi ∈ zs, ∀ p, pi.1 = some p → supportLive digestOf look rv self p = false →
        Term.usesVar pi.2 c.body = false
  | [], acc, r, hf => by
    simp only [List.foldlM, pure, Except.pure, Except.ok.injEq] at hf
    subst hf; simp [deadPositions]
  | (o, x) :: zs, acc, r, hf => by
    rw [List.foldlM_cons] at hf
    cases o with
    | none =>
      obtain ⟨h1, h2⟩ := changed_fold h c zs acc r hf
      refine ⟨by simp [h1, deadPositions], ?_⟩
      intro pi hpi p hp hl
      rcases List.mem_cons.mp hpi with rfl | hpi
      · cases hp
      · exact h2 pi hpi p hp hl
    | some pin =>
      cases hpin : supportPinned digestOf look rv self pin with
      | error e =>
        have : hypothesisStep digestOf look rv self h c acc (some pin, x) = .error e := by
          simp [hypothesisStep, hpin, bind, Except.bind]
        rw [this] at hf; cases hf
      | ok u =>
        cases hlive : supportLive digestOf look rv self pin with
        | true =>
          have : hypothesisStep digestOf look rv self h c acc (some pin, x) = .ok acc := by
            simp [hypothesisStep, hpin, hlive, bind, Except.bind]
          rw [this] at hf
          obtain ⟨h1, h2⟩ := changed_fold h c zs acc r hf
          refine ⟨by simp [h1, deadPositions, hlive], ?_⟩
          intro pi hpi p hp hl
          rcases List.mem_cons.mp hpi with rfl | hpi
          · cases hp; rw [hlive] at hl; cases hl
          · exact h2 pi hpi p hp hl
        | false =>
          cases huse : Term.usesVar x c.body with
          | true =>
            have : hypothesisStep digestOf look rv self h c acc (some pin, x) = .error (.supportMoved h.name x) := by
              simp [hypothesisStep, hpin, hlive, huse, bind, Except.bind]
            rw [this] at hf; cases hf
          | false =>
            have : hypothesisStep digestOf look rv self h c acc (some pin, x) = .ok (acc ++ [x]) := by
              simp [hypothesisStep, hpin, hlive, huse, bind, Except.bind]
            rw [this] at hf
            obtain ⟨h1, h2⟩ := changed_fold h c zs (acc ++ [x]) r hf
            refine ⟨by simp [h1, deadPositions, hlive], ?_⟩
            intro pi hpi p hp hl
            rcases List.mem_cons.mp hpi with rfl | hpi
            · exact huse
            · exact h2 pi hpi p hp hl

/-- One observed step whose pin is used only if live never refuses (whatever it does with a dead unused pin). -/
private theorem hypothesisStep_ok (h : HoleROM) (c : HoleCode) (removed : List Nat) (pin : SupportPin) (x : Nat)
    (hpin : supportPinned digestOf look rv self pin = .ok ())
    (huse : Term.usesVar x c.body = true → supportLive digestOf look rv self pin = true) :
    ∃ r, hypothesisStep digestOf look rv self h c removed (some pin, x) = .ok r := by
  cases hl : supportLive digestOf look rv self pin with
  | true => exact ⟨removed, by simp [hypothesisStep, hpin, hl, bind, Except.bind]⟩
  | false =>
    cases hu : Term.usesVar x c.body with
    | true => have := huse hu; rw [hl] at this; cases this
    | false =>
      simp only [hypothesisStep, hpin, hl, hu, bind, Except.bind, Bool.false_eq_true, if_false]
      first | exact ⟨_, rfl⟩ | (split <;> exact ⟨_, rfl⟩)

private theorem changed_fold_ok (h : HoleROM) (c : HoleCode) :
    ∀ (zs : List (Option SupportPin × Nat)) (acc : List Nat),
      (∀ pi ∈ zs, ∀ p, pi.1 = some p → supportPinned digestOf look rv self p = .ok () ∧
        (Term.usesVar pi.2 c.body = true → supportLive digestOf look rv self p = true)) →
      ∃ r, zs.foldlM (hypothesisStep digestOf look rv self h c) acc = .ok r
  | [], acc, _ => ⟨acc, rfl⟩
  | (o, x) :: zs, acc, hz => by
    have hz' : ∀ pi ∈ zs, _ := fun pi hpi => hz pi (List.mem_cons_of_mem _ hpi)
    rw [List.foldlM_cons]
    cases o with
    | none => exact changed_fold_ok h c zs acc hz'
    | some pin =>
      obtain ⟨hpin, huse⟩ := hz (some pin, x) List.mem_cons_self pin rfl
      obtain ⟨r, hr⟩ := hypothesisStep_ok h c acc pin x hpin huse
      rw [hr]
      exact changed_fold_ok h c zs r hz'

private theorem selectHole_inv {h : HoleROM} {s : HoleSelection}
    (hs : selectHole digestOf look rv self h = .ok s) :
    ∃ c, h.code[s.index]? = some c ∧ s.original = c.body ∧
      changedHypotheses digestOf look rv self h c = .ok s.strengthened := by
  unfold selectHole at hs
  simp only [bind, Except.bind, pure, Except.pure] at hs
  repeat' split at hs
  all_goals first | (simp at hs; done) | skip
  simp only [Except.ok.injEq] at hs
  subst s
  exact ⟨_, ‹h.code[_]? = some _›, rfl, ‹changedHypotheses digestOf look rv self h _ = .ok _›⟩

theorem selectHole_hypotheses {h : HoleROM} {s : HoleSelection}
    (hs : selectHole digestOf look rv self h = .ok s) :
    ∃ c, h.code[s.index]? = some c ∧ s.original = c.body ∧
      ∀ x p, h.hypotheses[x]? = some (some p) →
        (x ∈ s.strengthened ↔ supportLive digestOf look rv self p = false) ∧
        (supportLive digestOf look rv self p = false → Term.usesVar x c.body = false) := by
  obtain ⟨c, hc, ho, hch⟩ := selectHole_inv hs
  refine ⟨c, hc, ho, fun x p hx => ?_⟩
  unfold changedHypotheses at hch
  obtain ⟨hr, hu⟩ := changed_fold h c _ [] _ hch
  have hmem : (some p, x) ∈ h.hypotheses.zipIdx := List.mem_zipIdx_iff_getElem?.mpr hx
  refine ⟨?_, fun hl => hu _ hmem p rfl hl⟩
  rw [hr, List.nil_append]
  simp only [deadPositions, List.mem_filterMap]
  constructor
  · rintro ⟨⟨o, y⟩, hy, he⟩
    have hy' := List.mem_zipIdx_iff_getElem?.mp hy
    cases o with
    | none => cases he
    | some q =>
      simp only at he
      split at he
      · cases he
      · cases he
        rw [hx] at hy'
        cases hy'
        simpa using ‹¬supportLive digestOf look rv self p = true›
  · intro hl
    exact ⟨(some p, x), hmem, by simp [hl]⟩

theorem selectHole_live_selects {h : HoleROM} {amount ver i used : Nat} {bytes : ByteArray} {c : HoleCode}
    (hrow : holeRow rv self h.selectionRel h.selectionKey = .ok (some (.row amount bytes ver)))
    (hdec : Wire.decodeData .nat bytes = .ok (.nat i)) (hc : h.code[i]? = some c)
    (hsup : ∀ p ∈ c.supports, supportObserved digestOf look p = true ∧
      supportLive digestOf look rv self p = true)
    (hhyp : ∀ x p, h.hypotheses[x]? = some (some p) →
      supportPinned digestOf look rv self p = .ok () ∧
      (Term.usesVar x c.body = true → supportLive digestOf look rv self p = true))
    (hgp : ∀ p, h.guardPin = some p → supportPinned digestOf look rv self p = .ok ())
    (hguard : run [] Bounds.stackMax Bounds.holeGuardFuel 0
      (State.init h.guard [.bool (h.guardPin.all (supportLive digestOf look rv self))]) = .value (.bool true) used) :
    ∃ s, selectHole digestOf look rv self h = .ok s ∧ s.index = i ∧ s.version = ver := by
  obtain ⟨removed, hch⟩ : ∃ r, changedHypotheses digestOf look rv self h c = .ok r :=
    changed_fold_ok h c h.hypotheses.zipIdx [] (fun pi hpi p hp => by
      obtain ⟨o, x⟩ := pi
      simp only at hp
      subst hp
      exact hhyp x p (List.mem_zipIdx_iff_getElem?.mp hpi))
  have hg : runHoleGuard digestOf look rv self h = .ok used := by
    unfold runHoleGuard
    cases hgp' : h.guardPin with
    | none =>
      simp only [hgp', Option.all_none] at hguard
      simp [bind, Except.bind, pure, Except.pure, hguard]
    | some p =>
      simp only [hgp', Option.all_some] at hguard
      simp [bind, Except.bind, hgp p hgp', hguard]
  have h1 : c.supports.all (supportObserved digestOf look) = true :=
    List.all_eq_true.mpr fun p hp => (hsup p hp).1
  have h3 : c.supports.all (supportLive digestOf look rv self) = true :=
    List.all_eq_true.mpr fun p hp => (hsup p hp).2
  have h2 : c.supports.all (rowSupportHolds digestOf look rv self) = true :=
    List.all_eq_true.mpr fun p hp => by
      cases p <;> simp only [rowSupportHolds] <;> first | rfl | exact (hsup _ hp).2
  unfold selectHole
  simp only [hrow, hdec, hc, h1, h2, h3, hch, hg, bind, Except.bind, pure, Except.pure]
  exact ⟨_, rfl, rfl, rfl⟩

end HypothesisSelection

/-- Blocked code cannot be mistaken for an authenticated selection receipt. -/
theorem blocked_has_no_receipt (n : Nat) (T : Ty) (why : HoleRefusal) :
    (HoleResolution.blocked n T why).receipt = none := rfl

/-- Resolution preserves the exact refusal returned by fresh authentication.
This equation names the transient term that fillRefs substitutes. -/
theorem resolveHole_refusal {D : Type} {digestOf : ByteArray → Option D} {look : Pinned D} {rv : RowView D} {self : D} {h : HoleROM} {why : HoleRefusal}
    (he : selectHole digestOf look rv self h = .error why) :
    (resolveHole digestOf look rv self h).body = .refuse h.ty why.wire.toUTF8 ∧
      (resolveHole digestOf look rv self h).receipt = none := by
  simp [resolveHole, he, HoleResolution.body, HoleResolution.receipt]

/-- Demanding the blocked term fires that same named refusal in one machine step. -/
theorem blocked_step (n : Nat) (T : Ty) (why : HoleRefusal) (lib : List Term) (env : Env) :
    step lib (State.init (HoleResolution.blocked n T why).body env) =
      .fault (.refused why.wire.toUTF8) := rfl

/-- Successful bounded contextual preparation is closed and typed at the
unchanged interface, and its actual allocated syntax is within the bound. -/
theorem instantiateHoles_typed {D : Type} {digestOf : ByteArray → Option D} {look : Pinned D} {rv : RowView D} {self : D}
    {Δ : List Ty} {p : Package} {i : HoleInstance}
    (h : instantiateHoles digestOf look rv self Δ p = .ok i) :
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
theorem instantiateHoles_sources {D : Type} {digestOf : ByteArray → Option D} {look : Pinned D} {rv : RowView D} {self : D}
    {Δ : List Ty} {p : Package} {i : HoleInstance}
    (h : instantiateHoles digestOf look rv self Δ p = .ok i) :
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
theorem runHoleGuard_cost {D : Type} {digestOf : ByteArray → Option D} {look : Pinned D} {rv : RowView D} {self : D} {h : HoleROM} {used : Nat}
    (hr : runHoleGuard digestOf look rv self h = .ok used) : used ≤ Bounds.holeGuardFuel := by
  unfold runHoleGuard at hr
  simp only [bind, Except.bind, pure, Except.pure] at hr
  repeat' split at hr
  all_goals first | (simp at hr; done) | skip
  all_goals
    cases hr
    have hb := run_used_le (lib := []) (cap := Bounds.stackMax) Bounds.holeGuardFuel
      (State.init h.guard [.bool (h.guardPin.all (supportLive digestOf look rv self))])
    rw [‹run _ _ _ _ _ = _›] at hb
    exact hb



theorem admitContextual_inv {D : Type} {digestOf : ByteArray → Option D}
    {prepare : List Ty → Package → Except HoleRefusal Term}
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

theorem selectHole_nodes {D : Type} {digestOf : ByteArray → Option D} {look : Kernel.Receive.Pinned D} {rv : Kernel.Receive.RowView D} {self : D}
    {h : HoleROM} {s : HoleSelection} (hs : selectHole digestOf look rv self h = .ok s) :
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
theorem resolutionMax_committed {D : Type} (digestOf : ByteArray → Option D) (look : Kernel.Receive.Pinned D) (rv : Kernel.Receive.RowView D) (self : D)
    (hs : List HoleROM) :
    resolutionMax (hs.map (resolveHole digestOf look rv self)) ≤
      (hs.flatMap (fun h => h.code)).foldl (fun n c => max n (Term.nodes c.body)) 1 := by
  apply foldMax_le
  · exact foldMax_start _ _ _
  · intro r hr
    obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hr
    cases he : selectHole digestOf look rv self h with
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
theorem instantiateHoles_cost {D : Type} {digestOf : ByteArray → Option D} {look : Kernel.Receive.Pinned D} {rv : Kernel.Receive.RowView D} {self : D}
    {Δ : List Ty} {p : Package} {i : HoleInstance}
    (h : instantiateHoles digestOf look rv self Δ p = .ok i) :
    i.cost ≤ p.preparationCost := by
  have hc : i.cost = p.holeCharge (resolutionMax (p.holes.map (resolveHole digestOf look rv self))) := by
    unfold instantiateHoles at h
    simp only [bind, Except.bind, pure, Except.pure] at h
    repeat' split at h
    all_goals first | (simp at h; done) | skip
    all_goals
      simp only [Except.ok.injEq] at h
      subst i
      simp_all
  rw [hc, Package.preparationCost, Package.holeCharge, Package.holeCharge]
  split
  · exact Nat.le_refl 0
  · have hm := resolutionMax_committed digestOf look rv self p.holes
    have hmul := Nat.mul_le_mul_left (Term.nodes p.body) (Nat.add_le_add_right hm 1)
    exact Nat.add_le_add_right hmul _

end

end Nanodregg.Lang
