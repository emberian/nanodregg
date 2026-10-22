/-
# Lang.Proofs.LawReceiver — the contextual law receiver

`judgeContextual_mem`, `judgeOneContextual_ok`, `judgeOneContextual_admits_relib`, `loadContextual_top`: consumed by
`Kernel/Proofs/Logic/History` and `Ledger/Proofs/EscrowRun`.
-/
import Lang.Proofs.LawMeaning

namespace Nanodregg.Lang

/-! ## From `Lang.Proofs.Contextual.LawReceiver` -/
section

open Nanodregg.Kernel Nanodregg.Kernel.Receive

section
variable {D : Type} (bytesOf : D → ByteArray) (digestOf : ByteArray → Option D)

/-- Contextual loading retains the original ROM and the precise unresolved body
given to law evaluation. Imports may themselves be contextual. -/
theorem loadContextual_top {look : Pinned D} {law : D} {p : Package} {fuel : Nat} {L : Loaded} {g : Nat}
    (hid : digestOf (bytesOf law) = some law) (hp : readPackage look law = .ok p)
    (h : loadContextual digestOf look (fuel + 1) (bytesOf law) ⟨[], [], []⟩ = .ok (L, g)) :
    L.pkgs[g]? = some p ∧ ∃ f b, unresolvedBody p = .ok b ∧ L.lib[g]? = some (b.relocate f) := by
  unfold loadContextual loadUsing at h
  simp only [indexIn, idOf, hid, hp] at h
  split at h
  · cases h
  · rename_i acc gis hall
    obtain ⟨⟨hids, hlib, _, _⟩, _, _⟩ :=
      loadAllUsing_inv digestOf look _ (fun hi hw ha => admitContextual_inv hi hw ha)
        fuel p.imports _ Inv.empty hall
    unfold admitContextual at h
    split at h
    · rename_i hc
      unfold admitPackage at h
      repeat' split at h
      all_goals first | (cases h; done) | skip
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨by simp [hids], (fun i => gis.getD i 0), p.body,
        by simp [unresolvedBody, hc], by simp [← hlib, hids]⟩
    · split at h
      · cases h
      · split at h
        · cases h
        · split at h
          · cases h
          · rename_i body hb
            split at h
            · cases h
            · split at h
              · simp only [Except.ok.injEq, Prod.mk.injEq] at h
                obtain ⟨rfl, rfl⟩ := h
                exact ⟨by simp [hids], (fun i => gis.getD i 0), body, hb, by simp [← hlib, hids]⟩
              · cases h
              · cases h

theorem judgeOneContextual_ok {look : Pinned D} {law : D} {old new : Kernel.Slots} {r : Req D}
    (h : judgeOneWith bytesOf digestOf (loadContextual digestOf) look law old new r = .ok ()) :
    ∃ L g p o n, loadContextual digestOf look closureDepthMax (bytesOf law) ⟨[], [], []⟩ = .ok (L, g) ∧
      L.pkgs[g]? = some p ∧ readState digestOf (recordRow p.state) old = .ok o ∧
      readState digestOf (recordRow p.state) new = .ok n ∧
      ∀ ℓ ∈ p.laws, runLaw L.lib (.get (.ref g) ℓ) o n (reqData bytesOf r) = .ok (.ok ()) := by
  unfold judgeOneWith at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · split at h
    · cases h
    · rename_i v hload
      obtain ⟨L, g⟩ := v
      split at h
      · rename_i p hp
        split at h
        · rename_i o ho
          split at h
          · rename_i n hn
            split at h
            · cases h
            · rename_i u hfor
              refine ⟨L, g, p, o, n, hload, hp, ho, hn, ?_⟩
              refine forIn_yield_ok _ _ _ (fun ℓ u s hs => ?_) hfor
              split at hs <;> simp_all
          · cases h
        · cases h
      · cases h
  · cases h

end

theorem judgeContextual_mem {D : Type} {bytesOf : D → ByteArray} {digestOf : ByteArray → Option D} {look : Pinned D}
    {pkg : Option D} {laws : List D} {old new : Slots} {r : Req D}
    (h : Lang.judgeContextual bytesOf digestOf look pkg laws old new r = .ok ()) {l : D} (hl : l ∈ pkg.toList ++ laws) :
    Lang.judgeOneWith bytesOf digestOf (loadContextual digestOf) look l old new r = .ok () := by
  unfold Lang.judgeContextual at h
  cases pkg with
  | none =>
      simp only [Option.toList_none, List.nil_append] at hl
      simp only [bind, Except.bind, pure, Except.pure] at h
      split at h
      · cases h
      · rename_i v hf
        refine Lang.forIn_yield_ok (fun l => Lang.judgeOneWith bytesOf digestOf (loadContextual digestOf) look l old new r = .ok ()) laws _
          (fun a u s hs => ?_) (by cases v; exact hf) l hl
        split at hs
        · cases hs
        · rename_i v' hv
          simp only [Except.ok.injEq] at hs
          exact ⟨hs.symm, by cases v'; exact hv⟩
  | some q =>
      simp only [bind, Except.bind] at h
      split at h
      · cases h
      · rename_i v hv
        simp only [Option.toList_some, List.cons_append, List.mem_cons] at hl
        rcases hl with rfl | hl
        · cases v; exact hv
        · split at h
          · cases h
          · rename_i v₂ hf
            refine Lang.forIn_yield_ok (fun l => Lang.judgeOneWith bytesOf digestOf (loadContextual digestOf) look l old new r = .ok ()) laws _
              (fun a u s hs => ?_) (by cases v₂; exact hf) l hl
            split at hs
            · cases hs
            · rename_i v' hv'
              simp only [pure, Except.pure, Except.ok.injEq] at hs
              exact ⟨hs.symm, by cases v'; exact hv'⟩

private theorem runLaw_contextual_body {lib : List Term} {g : Nat} {fs : List (Label × Term)} {ℓ : Label} {A B C : Ty}
    {b : Term} {o n r : Data} (hg : lib[g]? = some (.record fs))
    (hℓ : Row.find? ℓ fs = some (.lam A (.lam B (.lam C b))))
    (h : runLaw lib (.get (.ref g) ℓ) o n r = .ok (.ok ())) :
    ∃ w, BigStep lib [r.toVal, n.toVal, o.toVal] b (.ok (.inj "ok" w)) := by
  have hf : BigStep lib [r.toVal, n.toVal, o.toVal] (.get (.ref g) ℓ) (.ok (.clo (.lam B (.lam C b)) [])) :=
    .get (.ref hg .record) (.field (Std.find_suspend hℓ) .lam)
  unfold runLaw at h
  split at h
  · cases h
  · rename_i v used hrun
    split at h
    · rename_i d f hx
      obtain ⟨w, rfl⟩ := Std.extract_sum_inj hx
      exact ⟨w, Std.applyAt_of_fn hf (run_bigStep hrun)⟩
    all_goals simp at h


/-- A related law retains its three binders and relates their bodies. -/
theorem LawTerm.law_body {A B C : Ty} {b u : Term}
    (h : LawTerm (.lam A (.lam B (.lam C b))) u) :
    ∃ b', u = .lam A (.lam B (.lam C b')) ∧ LawTerm b b' := by
  cases h with | lam h => cases h with | lam h => cases h with | lam h => exact ⟨_, rfl, h⟩

section
variable {D : Type} (bytesOf : D → ByteArray) (digestOf : ByteArray → Option D)

/-- The contextual judge's successful law has the original ROM law's meaning
under every library. No empty-signature or no-hole premise is required. -/
theorem judgeOneContextual_admits_relib {look : Pinned D} {law : D}
    {old new : Slots} {r : Req D} {p : Package} {fs : List (Label × Term)}
    (hid : digestOf (bytesOf law) = some law) (hp : readPackage look law = .ok p) (hb : p.body = .record fs)
    (h : judgeOneWith bytesOf digestOf (loadContextual digestOf) look law old new r = .ok ()) :
    ∃ o n, readState digestOf (recordRow p.state) old = .ok o ∧
      readState digestOf (recordRow p.state) new = .ok n ∧
      ∀ l ∈ p.laws, ∀ t, Row.find? l fs = some t → IsLaw t → NoRef t → ∀ lib' : List Term,
        Std.Admits lib' t (reqData bytesOf r) n o := by
  obtain ⟨L, g, p', o, n, hload, hpg, ho, hn, hall⟩ := judgeOneContextual_ok bytesOf digestOf h
  obtain ⟨hpg', f, body, hbody, hlib⟩ := loadContextual_top bytesOf digestOf
    (fuel := closureDepthMax - 1) hid hp hload
  rw [hpg'] at hpg
  cases hpg
  obtain ⟨fs', hrecord, hfields⟩ := unresolvedBody_field hb hbody
  have hg : L.lib[g]? = some (.record (Term.relocateRow f fs')) := by rw [hlib, hrecord]; rfl
  refine ⟨o, n, ho, hn, fun l hl t hf ht hnr lib' => ?_⟩
  obtain ⟨t', hf', ht'⟩ := hfields l t hf hnr
  have hfind : Row.find? l (Term.relocateRow f fs') = some (t'.relocate f) := by
    rw [find_relocateRow, hf']; rfl
  obtain ⟨A, B, C, b, rfl⟩ := ht
  obtain ⟨b', heq, hbb⟩ := (ht'.relocate_right f).law_body
  rw [heq] at hfind
  obtain ⟨w', hw'⟩ := runLaw_contextual_body hg hfind (hall l hl)
  obtain ⟨result, hrun, hres⟩ := law_bigStep_back (lib := lib') hw'
    (.cons (LawVal.data _) (.cons (LawVal.data _) (.cons (LawVal.data _) .nil))) hbb
  cases hres with | ok hv => cases hv with | inj hv => exact ⟨[], _, hrun⟩

end

end

end Nanodregg.Lang
