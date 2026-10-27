/-
# Lang.Proofs.PrintWire — every package the wire carries and the install check accepts has a text

The wire and the printer share one label rule (`Wire.labelOk`: one atom of at most 64 bytes), and
the reader reads two levels deeper than the wire's tree (`Read.depthMax = Wire.depthMax + 2`). A
printed form is at most one level deeper than its tree: a row entry is one tree node and one list,
and only the leaves `(ref i)` and an empty `(rec)` / `(record)` print as a list over a tree leaf.
A package's sections add the second level. So:

* `tyWire_prints`: a type whose tree fits depth `D` prints within `D + 1`;
* `hasType_prints`: a well-typed term (so no free variable) whose tree fits depth `D` prints within
  `D + 1` under its context's binders;
* `package_prints`: a wire-valid package whose tree fits the wire's bounds and which the install
  check accepts has a text (`Print.package` is `some`);
* `installed_prints` / `installed_reads`: the same for any bytes `decodePackage` accepts, and that
  text reads back to exactly the package (`readPackage_checked`);
* `checkInstall_checked` / `install_reads`: the install check reads its imports' interfaces from
  the loader, so they are canonical, and every package without holes it admits has a text that
  reads back to it (LANG-35, LANG-78; a holed package's read-back is not stated);
* `state_prints`: the state type of an encodable package prints within `Wire.depthMax`, which is
  `StdFits`' premise `TyPrints (Read.depthMax - 2) S`, so `quorum_text_at`, `allowlist_text_at`
  and `machine_text_at` state the stdlib's text theorems over a package's own state type.

The teeth: `deep_*` is a package at the wire's depth bound whose text needs exactly `Read.depthMax`
(so the `+ 2` is not slack), and a label with a space has no bytes (the wire refuses it as the
printer does).
-/
import Lang.Proofs.Prints
import Lang.Proofs.Print
import Lang.Proofs.Wire
import Lang.Proofs.StdFits
import Lang.Proofs.Load
import Lang.Proofs.LiveHoles

namespace Nanodregg.Lang.Print

open Read (listMax depthMax)
open Wire (labelOk)
open Nanodregg.Codec

theorem fits_node {m D : Nat} {g : UInt8} {p : ByteArray} {cs : List Tree}
    (h : (Tree.node g p cs).fits m D = true) : ∃ D', D = D' + 1 ∧ ∀ c ∈ cs, c.fits m D' = true := by
  cases D with
  | zero => simp [Tree.fits] at h
  | succ D =>
    simp only [Tree.fits, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
    exact ⟨D, rfl, h.2⟩

/-! ## Types -/

mutual
theorem tyWire_prints : ∀ (T : Ty) {m D : Nat}, Wire.tyWire T = true → (Wire.tyTree T).fits m D = true →
    TyPrints (D + 1) T
  | .nat, _, _, _, hf => by
    obtain ⟨D', rfl, -⟩ := fits_node hf
    exact (typrints_atom _ (.inl rfl)).mono (by omega)
  | .bool, _, _, _, hf => by
    obtain ⟨D', rfl, -⟩ := fits_node hf
    exact (typrints_atom _ (.inr (.inl rfl))).mono (by omega)
  | .bytes, _, _, _, hf => by
    obtain ⟨D', rfl, -⟩ := fits_node hf
    exact (typrints_atom _ (.inr (.inr (.inl rfl)))).mono (by omega)
  | .digest, _, _, _, hf => by
    obtain ⟨D', rfl, -⟩ := fits_node hf
    exact (typrints_atom _ (.inr (.inr (.inr rfl)))).mono (by omega)
  | .fn a c, _, _, hw, hf => by
    simp only [Wire.tyWire, Bool.and_eq_true] at hw
    obtain ⟨D', rfl, hc⟩ := fits_node hf
    exact typrints_fn (tyWire_prints a hw.1 (hc _ (by simp))) (tyWire_prints c hw.2 (hc _ (by simp)))
  | .record r, _, _, hw, hf => by
    simp only [Wire.tyWire, Bool.and_eq_true, decide_eq_true_eq] at hw
    obtain ⟨D', rfl, hc⟩ := fits_node hf
    exact typrints_record (tyRow_prints r hw.2 hc) (by simp only [listMax_eq, Wire.rowMax] at hw ⊢; omega)
  | .sum r, _, _, hw, hf => by
    simp only [Wire.tyWire, Bool.and_eq_true, decide_eq_true_eq] at hw
    obtain ⟨D', rfl, hc⟩ := fits_node hf
    exact typrints_sum (tyRow_prints r hw.2 hc) (by simp only [listMax_eq, Wire.rowMax] at hw ⊢; omega)

theorem tyRow_prints : ∀ (r : List (Label × Ty)) {m E : Nat}, Wire.tyRowWire r = true →
    (∀ c ∈ Wire.tyRowTree r, c.fits m E = true) → ∀ p ∈ r, labelOk p.1 = true ∧ TyPrints E p.2
  | [], _, _, _, _ => by simp
  | (ℓ, t) :: r, _, _, hw, hc => by
    simp only [Wire.tyRowWire, Bool.and_eq_true] at hw
    simp only [Wire.tyRowTree, List.mem_cons, forall_eq_or_imp] at hc
    obtain ⟨E', rfl, hct⟩ := fits_node hc.1
    exact List.forall_mem_cons.2 ⟨⟨hw.1.1, tyWire_prints t hw.1.2 (hct _ (by simp))⟩, tyRow_prints r hw.2 hc.2⟩
end

/-! ## Terms -/

mutual
theorem hasType_prints {Δ : List Ty} : ∀ {Γ : List Ty} {t : Term} {T : Ty} {m D : Nat}, HasType Δ Γ t T →
    Wire.termWire t = true → (Wire.termTree t).fits m D = true → Prints (D + 1) Γ.length t
  | _, _, _, _, _, .var h, _, hf => by
    obtain ⟨D', rfl, -⟩ := fits_node hf
    obtain ⟨hi, -⟩ := List.getElem?_eq_some_iff.1 h
    exact (prints_var hi).mono (by omega)
  | _, _, _, _, _, .lam (A := A) (b := b) _ hb, hw, hf => by
    simp only [Wire.termWire, Bool.and_eq_true] at hw
    obtain ⟨D', rfl, hc⟩ := fits_node hf
    exact prints_lam (tyWire_prints A hw.1 (hc _ (by simp))) (hasType_prints hb hw.2 (hc _ (by simp)))
  | _, _, _, _, _, .app hf' ha, hw, hf => by
    simp only [Wire.termWire, Bool.and_eq_true] at hw
    obtain ⟨D', rfl, hc⟩ := fits_node hf
    exact prints_app (hasType_prints hf' hw.1 (hc _ (by simp))) (hasType_prints ha hw.2 (hc _ (by simp)))
  | _, _, _, _, _, .fix ht, hw, hf => by
    simp only [Wire.termWire] at hw
    obtain ⟨D', rfl, hc⟩ := fits_node hf
    exact prints_fix (hasType_prints ht hw (hc _ (by simp)))
  | _, _, _, _, _, .nat _, _, hf => by
    obtain ⟨D', rfl, -⟩ := fits_node hf
    exact (prints_nat _ _).mono (by omega)
  | _, _, _, _, _, .bool, _, hf => by
    obtain ⟨D', rfl, -⟩ := fits_node hf
    exact (prints_bool _ _).mono (by omega)
  | _, _, _, _, _, .bytes _, _, hf => by
    obtain ⟨D', rfl, -⟩ := fits_node hf
    exact (prints_bytes _ _).mono (by omega)
  | _, _, _, _, _, .digest _, _, hf => by
    obtain ⟨D', rfl, -⟩ := fits_node hf
    exact (prints_digest _ _).mono (by omega)
  | _, _, _, _, _, .refuse _ _, hw, hf => by
    simp only [Wire.termWire] at hw
    obtain ⟨D', rfl, hc⟩ := fits_node hf
    exact prints_refuse _ (tyWire_prints _ hw (hc _ (by simp)))
  | _, _, _, _, _, .prim ha hb, hw, hf => by
    simp only [Wire.termWire, Bool.and_eq_true] at hw
    obtain ⟨D', rfl, hc⟩ := fits_node hf
    exact prints_prim _ (hasType_prints ha hw.1 (hc _ (by simp))) (hasType_prints hb hw.2 (hc _ (by simp)))
  | _, _, _, _, _, .record _ hfs, hw, hf => by
    simp only [Wire.termWire, Bool.and_eq_true, decide_eq_true_eq] at hw
    obtain ⟨D', rfl, hc⟩ := fits_node hf
    exact prints_record (fieldsTy_prints hfs hw.2 hc) (by simp only [listMax_eq, Wire.rowMax] at hw ⊢; omega)
  | _, _, _, _, _, .get ht _, hw, hf => by
    simp only [Wire.termWire, Bool.and_eq_true] at hw
    obtain ⟨D', rfl, hc⟩ := fits_node hf
    exact prints_get (hasType_prints ht hw.2 (hc _ (by simp))) hw.1
  | _, _, _, _, _, .extend ht _ hfs, hw, hf => by
    simp only [Wire.termWire, Bool.and_eq_true, decide_eq_true_eq] at hw
    obtain ⟨D', rfl, hc⟩ := fits_node hf
    simp only [List.mem_cons, forall_eq_or_imp] at hc
    exact prints_extend (hasType_prints ht hw.1.1 hc.1) (fieldsTy_prints hfs hw.2 hc.2)
      (by simp only [listMax_eq, Wire.rowMax] at hw ⊢; omega)
  | _, _, _, _, _, .inj (r := r) _ _ ht, hw, hf => by
    simp only [Wire.termWire, Bool.and_eq_true] at hw
    obtain ⟨D', rfl, hc⟩ := fits_node hf
    exact prints_inj (tyWire_prints (.sum r) hw.1.1 (hc _ (by simp))) hw.1.2 (hasType_prints ht hw.2 (hc _ (by simp)))
  | _, _, _, _, _, .case ht ha, hw, hf => by
    simp only [Wire.termWire, Bool.and_eq_true, decide_eq_true_eq] at hw
    obtain ⟨D', rfl, hc⟩ := fits_node hf
    simp only [List.mem_cons, forall_eq_or_imp] at hc
    exact prints_case (hasType_prints ht hw.1.1 hc.1) (armsTy_prints ha hw.2 hc.2)
      (by simp only [listMax_eq, Wire.rowMax] at hw ⊢; omega)
  | _, _, _, _, _, .ite hc' ha hb, hw, hf => by
    simp only [Wire.termWire, Bool.and_eq_true] at hw
    obtain ⟨D', rfl, hc⟩ := fits_node hf
    exact prints_ite (hasType_prints hc' hw.1.1 (hc _ (by simp))) (hasType_prints ha hw.1.2 (hc _ (by simp)))
      (hasType_prints hb hw.2 (hc _ (by simp)))
  | _, _, _, _, _, .ref _, _, hf => by
    obtain ⟨D', rfl, -⟩ := fits_node hf
    exact (prints_ref _ _).mono (by omega)

theorem fieldsTy_prints {Δ : List Ty} : ∀ {Γ : List Ty} {fs : List (Label × Term)} {r : List (Label × Ty)} {m E : Nat},
    FieldsTy Δ Γ fs r → Wire.fieldsWire fs = true → (∀ c ∈ Wire.fieldsTree fs, c.fits m E = true) →
    ∀ p ∈ fs, labelOk p.1 = true ∧ Prints E Γ.length p.2
  | _, _, _, _, _, .nil, _, _ => by simp
  | _, _, _, _, _, .cons ht hfs, hw, hc => by
    simp only [Wire.fieldsWire, Bool.and_eq_true] at hw
    simp only [Wire.fieldsTree, List.mem_cons, forall_eq_or_imp] at hc
    obtain ⟨E', rfl, hct⟩ := fits_node hc.1
    exact List.forall_mem_cons.2 ⟨⟨hw.1.1, hasType_prints ht hw.1.2 (hct _ (by simp))⟩, fieldsTy_prints hfs hw.2 hc.2⟩

theorem armsTy_prints {Δ : List Ty} : ∀ {Γ : List Ty} {arms : List (Label × Term)} {r : List (Label × Ty)} {B : Ty}
    {m E : Nat}, ArmsTy Δ Γ arms r B → Wire.fieldsWire arms = true → (∀ c ∈ Wire.fieldsTree arms, c.fits m E = true) →
    ∀ p ∈ arms, labelOk p.1 = true ∧ Prints E (Γ.length + 1) p.2
  | _, _, _, _, _, _, .one hb, hw, hc => by
    simp only [Wire.fieldsWire, Bool.and_eq_true] at hw
    simp only [Wire.fieldsTree, List.mem_cons, forall_eq_or_imp] at hc
    obtain ⟨E', rfl, hct⟩ := fits_node hc.1
    exact List.forall_mem_cons.2 ⟨⟨hw.1.1, hasType_prints hb hw.1.2 (hct _ (by simp))⟩, by simp⟩
  | _, _, _, _, _, _, .cons hb ha _, hw, hc => by
    simp only [Wire.fieldsWire, Bool.and_eq_true] at hw
    simp only [Wire.fieldsTree, List.mem_cons, forall_eq_or_imp] at hc
    obtain ⟨E', rfl, hct⟩ := fits_node hc.1
    exact List.forall_mem_cons.2 ⟨⟨hw.1.1, hasType_prints hb hw.1.2 (hct _ (by simp))⟩, armsTy_prints ha hw.2 hc.2⟩
end

/-! ## Packages -/

theorem checkWith_parts {ifaces : List Ty} {p : Package} (hc : p.checkWith ifaces = .ok ()) :
    p.checkShape = .ok () ∧ ∃ T, inferE ifaces [] p.body (Ω := []) = .ok T := by
  unfold Package.checkWith at hc
  split at hc
  · cases hc
  · cases hc
  · rename_i hshape hbody
    refine ⟨hshape, ?_⟩
    unfold checkE at hbody
    split at hbody
    · rename_i T hT; exact ⟨T, hT⟩
    · cases hbody

theorem checkShape_bounds {p : Package} (h : p.checkShape = .ok ()) :
    p.imports.length ≤ importsMax ∧ p.methods.length ≤ methodsMax ∧ p.laws.length ≤ lawsMax := by
  unfold Package.checkShape at h
  simp only [bind, Except.bind, throw, throwThe, MonadExceptOf.throw, Except.pure, pure] at h
  repeat' split at h
  all_goals first | cases h | skip
  all_goals rename_i h1 h2 h3 _ _; simp only [gt_iff_lt, Nat.not_lt] at h1 h2 h3; exact ⟨h1, h2, h3⟩

theorem labels_mapM_atoms : ∀ (ls : List Label), ls.all labelOk = true → ls.mapM label = some (ls.map atom)
  | [], _ => rfl
  | ℓ :: ls, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    simp [List.mapM_cons, label, h.1, labels_mapM_atoms ls h.2]

theorem needs_map {α : Type} (f : α → Read.SExp) (hf : ∀ a, need (f a) = 1) : ∀ l : List α, needs (l.map f) ≤ 1
  | [] => by simp [needs]
  | a :: l => by simp only [List.map_cons, needs, hf a]; have := needs_map f hf l; omega

theorem widths_map {α : Type} (f : α → Read.SExp) (hf : ∀ a, width (f a) = 0) : ∀ l : List α, widths (l.map f) = 0
  | [] => by simp [widths]
  | a :: l => by simp only [List.map_cons, widths, hf a, widths_map f hf l]; rfl

/-! ## Relations (LANG-49): a relation in the wire's bounds prints -/

theorem optLabel_prints : ∀ (o : Option Label), o.all labelOk = true →
    ∃ xs, optLabelSx o = some xs ∧ needs xs ≤ 1 ∧ widths xs = 0 ∧ xs.length ≤ 1
  | none, _ => ⟨[], rfl, by simp [needs], by simp [widths], by simp⟩
  | some ℓ, h => by
    simp only [Option.all_some] at h
    exact ⟨[atom ℓ], by simp [optLabelSx, label, h], by simp [needs, need, atom],
      by simp [widths, width, atom], by simp⟩

theorem mapM_eq_rowSx : ∀ (key : List (Label × Ty)),
    key.mapM (fun f => do pure (list [← label f.1, ← tySx f.2])) = rowSx key
  | [] => rfl
  | (ℓ, t) :: key => by
    rw [List.mapM_cons, mapM_eq_rowSx key]
    simp only [rowSx]
    cases label ℓ <;> cases tySx t <;> cases rowSx key <;> rfl

theorem rel_prints {r : Label × RelDecl} {m D : Nat} (hw : Wire.relWire r = true)
    (hf : (Wire.relTree r).fits m D = true) (hk : r.2.key.length ≤ keyFieldsMax) :
    ∃ x, relSx r = some x ∧ need x ≤ D + 2 ∧ width x ≤ listMax := by
  obtain ⟨ℓ, d⟩ := r
  simp only [Wire.relWire, Bool.and_eq_true, decide_eq_true_eq] at hw
  obtain ⟨⟨⟨⟨⟨⟨hl, hkw⟩, hv⟩, -⟩, -⟩, hsu⟩, hg⟩ := hw
  obtain ⟨D', rfl, hc⟩ := fits_node hf
  obtain ⟨D'', hD', hkc⟩ := fits_node
    (hc (.node 0 .empty (d.key.map fun f => .node 6 f.1.toUTF8 [Wire.tyTree f.2])) (by simp))
  have hfp : ∀ p ∈ d.key, labelOk p.1 = true ∧ TyPrints D'' p.2 := by
    intro p hp
    have hpw := List.all_eq_true.mp hkw p hp
    simp only [Bool.and_eq_true] at hpw
    obtain ⟨E, hE, hcE⟩ := fits_node (hkc _ (List.mem_map.mpr ⟨p, hp, rfl⟩))
    subst hE
    exact ⟨hpw.1, tyWire_prints p.2 hpw.2 (hcE _ (by simp))⟩
  obtain ⟨xk, hxk, hnk, hwk, hlk⟩ := rowSx_prints hfp
  obtain ⟨xv, hxv, hnv, hwv⟩ := tyWire_prints d.val hv (hc (Wire.tyTree d.val) (by simp))
  obtain ⟨xs, hxs, hns, hws, hls⟩ := optLabel_prints _ hsu
  obtain ⟨xg, hxg, hng, hwg, hlg⟩ := optLabel_prints _ hg
  refine ⟨list [atom ℓ, list (atom "key" :: xk), list [atom "val", xv],
    list [atom "limit", atom (Nat.repr d.limit)], list (atom "sum" :: xs),
    list [atom "cap", atom (Nat.repr d.cap)], list [atom "retract", atom (if d.retract then "true" else "false")],
    list (atom "guard" :: xg)], ?_, ?_, ?_⟩
  · simp only [relSx]
    rw [mapM_eq_rowSx, hxk]
    simp [label, hl, hxv, hxs, hxg]
  · simp only [keyFieldsMax] at hk
    simp only [need, needs, list, atom]
    omega
  · simp only [keyFieldsMax] at hk
    simp only [listMax_eq] at hwk hwv ⊢
    simp only [width, widths, list, atom, List.length_cons, List.length_nil]
    omega

theorem rels_prints {m D : Nat} : ∀ (rels : List (Label × RelDecl)),
    (∀ r ∈ rels, Wire.relWire r = true ∧ (Wire.relTree r).fits m D = true ∧ r.2.key.length ≤ keyFieldsMax) →
    ∃ xR, rels.mapM relSx = some xR ∧ needs xR ≤ D + 2 ∧ widths xR ≤ listMax ∧ xR.length = rels.length
  | [], _ => ⟨[], rfl, by simp [needs], by simp [widths], rfl⟩
  | r :: rels, h => by
    obtain ⟨hw, hf, hk⟩ := h r (by simp)
    obtain ⟨x, hx, hn, hwx⟩ := rel_prints hw hf hk
    obtain ⟨xs, hxs, hns, hws, hl⟩ := rels_prints rels (fun r hr => h r (by simp [hr]))
    refine ⟨x :: xs, by simp [List.mapM_cons, hx, hxs], ?_, ?_, by simp [hl]⟩
    · simp only [needs]; omega
    · simp only [widths]; omega

theorem checkRel_key {S : Ty} {row : List (Label × Ty)} {r : Label × RelDecl}
    (h : checkRel S row r = .ok ()) : r.2.key.length ≤ keyFieldsMax := by
  obtain ⟨ℓ, d⟩ := r
  unfold checkRel at h
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at h
  repeat' split at h
  all_goals first | cases h | skip
  all_goals simp_all

theorem checkRels_bounds {S : Ty} {row : List (Label × Ty)} {rels : List (Label × RelDecl)}
    (h : checkRels S row rels = .ok ()) :
    rels.length ≤ relsMax ∧ ∀ r ∈ rels, r.2.key.length ≤ keyFieldsMax := by
  unfold checkRels at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  repeat' split at h
  all_goals first | cases h | skip
  rename_i hlen _ _ v hfor
  cases v
  refine ⟨by omega, forIn_yield_ok _ _ _ (fun r u s hs => ?_) hfor⟩
  split at hs
  · cases hs
  · rename_i hc; cases hs; exact ⟨rfl, checkRel_key hc⟩

theorem checkFields_checkRels {p : Package} (h : p.checkFields = .ok ()) :
    ∃ row, checkRels p.state row p.rels = .ok () := by
  unfold Package.checkFields at h
  split at h
  · simp only [bind, Except.bind] at h
    split at h
    · cases h
    · rename_i hr; exact ⟨_, hr⟩
  · cases h

/-- A doc the wire admits has a text, two levels deep, at most two wide. -/
theorem docSx_prints {w : ByteArray} (h : Bounds.docOk w = true) :
    ∃ x, docSx w = some x ∧ need x ≤ 2 ∧ width x ≤ 2 := by
  by_cases he : w.isEmpty = true
  · refine ⟨list [atom "doc"], by simp [docSx, h, he], ?_⟩
    simp [need, needs, width, widths, list, atom]
  · refine ⟨list [atom "doc", bytesSx w], by simp [docSx, h, he], ?_⟩
    rcases bytesSx_cases w with ⟨t, e, -⟩ | e <;>
      simp [e, need, needs, width, widths, list, atom]

theorem checkFields_checkEffects {p : Package} (h : p.checkFields = .ok ()) :
    ∃ row, checkEffects p row = .ok () := by
  unfold Package.checkFields at h
  split at h
  · simp only [bind, Except.bind] at h
    split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · cases h
        · rename_i he; exact ⟨_, he⟩
  · cases h

/-- What `checkEffects` accepting says of the table: ascending, every label a method. -/
theorem checkEffects_ok {p : Package} {row : List (Label × Ty)} (h : checkEffects p row = .ok ()) :
    Row.ascending p.effects = true ∧ ∀ e ∈ p.effects, e.1 ∈ p.methods := by
  unfold checkEffects at h
  split at h
  · cases h
  · rename_i hasc
    split at h
    · cases h
    · rename_i hf
      refine ⟨by simpa using hasc, fun e he => ?_⟩
      have := List.find?_eq_none.mp hf e he
      simpa using this

theorem ascending_labels_nodup {α : Type} : ∀ {l : List (Label × α)}, Row.ascending l = true → (l.map (·.1)).Nodup
  | [], _ => List.nodup_nil
  | (k, a) :: l, h => by
    rw [Row.ascending_cons_iff] at h
    simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and]
    exact ⟨fun e he hk => by have := h.1 e he; rw [hk] at this; exact absurd this (String.lt_irrefl _),
      ascending_labels_nodup h.2⟩

/-- A list without repeats that lies in another is no longer than it. -/
theorem length_le_of_nodup_subset {α : Type} [DecidableEq α] :
    ∀ {l₁ l₂ : List α}, l₁.Nodup → (∀ x ∈ l₁, x ∈ l₂) → l₁.length ≤ l₂.length
  | [], _, _, _ => Nat.zero_le _
  | a :: l₁, l₂, hn, hs => by
    simp only [List.nodup_cons] at hn
    have ha : a ∈ l₂ := hs a (List.mem_cons_self ..)
    have ih := length_le_of_nodup_subset (l₂ := l₂.erase a) hn.2 (fun x hx =>
      (List.mem_erase_of_ne (fun e => hn.1 (by rw [← e]; exact hx))).mpr (hs x (List.mem_cons_of_mem _ hx)))
    rw [List.length_erase_of_mem ha] at ih
    have := List.length_pos_of_mem ha
    simp only [List.length_cons]
    omega

/-- An accepted table has at most as many entries as the package has methods (LANG-89). -/
theorem checkEffects_length {p : Package} {row : List (Label × Ty)} (h : checkEffects p row = .ok ()) :
    p.effects.length ≤ p.methods.length := by
  obtain ⟨hasc, hmem⟩ := checkEffects_ok h
  have := length_le_of_nodup_subset (ascending_labels_nodup hasc) (fun x hx => by
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx; exact hmem e he)
  simpa using this

/-- The grades the wire admits print, each `(ℓ N)`: two deep, two wide. -/
theorem effects_mapM_sx : ∀ (es : List (Label × Effect)), es.all Wire.effectWire = true →
    es.mapM effectSx = some (es.map fun e => list [atom e.1, atom (Nat.repr e.2.moves)])
  | [], _ => rfl
  | e :: es, h => by
    simp only [List.all_cons, Bool.and_eq_true, Wire.effectWire] at h
    simp [List.mapM_cons, effectSx, label, h.1.1, effects_mapM_sx es h.2]

theorem effects_needs : ∀ (es : List (Label × Effect)),
    needs (es.map fun e => list [atom e.1, atom (Nat.repr e.2.moves)]) ≤ 2
  | [] => by simp [needs]
  | e :: es => by
    simp only [List.map_cons, needs, need, list, atom]
    have := effects_needs es
    simp only [list, atom] at this
    omega

theorem effects_widths : ∀ (es : List (Label × Effect)),
    widths (es.map fun e => list [atom e.1, atom (Nat.repr e.2.moves)]) ≤ 2
  | [] => by simp [widths]
  | e :: es => by
    simp only [List.map_cons, widths, width, list, atom, List.length_cons, List.length_nil]
    have := effects_widths es
    simp only [list, atom] at this
    omega

theorem package_fitsB_effects {is : List ByteArray} {ms ls : List Label} {xs xi xb xd : Read.SExp}
    (hdn : need xd ≤ 2) (hdw : width xd ≤ 2)
    (hi : is.length ≤ importsMax) (hm : ms.length ≤ methodsMax) (hl : ls.length ≤ lawsMax)
    (hs : need xs ≤ Wire.depthMax) (hsw : width xs ≤ listMax) (hf : need xi ≤ Wire.depthMax) (hfw : width xi ≤ listMax)
    (hb : need xb ≤ Wire.depthMax) (hbw : width xb ≤ listMax)
    {xR : List Read.SExp} (hr : needs xR ≤ Wire.depthMax) (hrw : widths xR ≤ listMax) (hrl : xR.length ≤ relsMax)
    {xE : List Read.SExp} (hen : needs xE ≤ 2) (hew : widths xE ≤ 2) (hel : xE.length ≤ methodsMax) :
    fitsB (list (atom "package" ::
      [list (atom "imports" :: is.map fun i => .str 0 (hex i)), xd, list [atom "state", xs],
       list [atom "iface", xi], list (atom "methods" :: ms.map atom),
       list (atom "laws" :: ls.map atom), list (atom "rels" :: xR), list [atom "body", xb],
       list (atom "effects" :: xE)])) = true := by
  have him := needs_map (fun i : ByteArray => Read.SExp.str 0 (hex i)) (fun _ => rfl) is
  have hiw := widths_map (fun i : ByteArray => Read.SExp.str 0 (hex i)) (fun _ => rfl) is
  have hmm := needs_map atom (fun _ => rfl) ms
  have hmw := widths_map atom (fun _ => rfl) ms
  have hlm := needs_map atom (fun _ => rfl) ls
  have hlw := widths_map atom (fun _ => rfl) ls
  rw [fitsB_iff]
  simp only [importsMax, methodsMax, lawsMax, relsMax] at hi hm hl hrl hel
  simp only [listMax_eq, Wire.depthMax] at hs hsw hf hfw hb hbw hr hrw ⊢
  simp only [depthMax, Wire.depthMax, need, needs, width, widths, list, atom, List.length_cons, List.length_map]
  simp only [List.length_nil, Nat.add_one_le_iff, Nat.max_lt, Nat.max_le]
  omega

theorem package_fitsB {is : List ByteArray} {ms ls : List Label} {xs xi xb xd : Read.SExp}
    (hdn : need xd ≤ 2) (hdw : width xd ≤ 2)
    (hi : is.length ≤ importsMax) (hm : ms.length ≤ methodsMax) (hl : ls.length ≤ lawsMax)
    (hs : need xs ≤ Wire.depthMax) (hsw : width xs ≤ listMax) (hf : need xi ≤ Wire.depthMax) (hfw : width xi ≤ listMax)
    (hb : need xb ≤ Wire.depthMax) (hbw : width xb ≤ listMax)
    {xR : List Read.SExp} (hr : needs xR ≤ Wire.depthMax) (hrw : widths xR ≤ listMax) (hrl : xR.length ≤ relsMax) :
    fitsB (list (atom "package" ::
      [list (atom "imports" :: is.map fun i => .str 0 (hex i)), xd, list [atom "state", xs],
       list [atom "iface", xi], list (atom "methods" :: ms.map atom),
       list (atom "laws" :: ls.map atom), list (atom "rels" :: xR), list [atom "body", xb]])) = true := by
  have him := needs_map (fun i : ByteArray => Read.SExp.str 0 (hex i)) (fun _ => rfl) is
  have hiw := widths_map (fun i : ByteArray => Read.SExp.str 0 (hex i)) (fun _ => rfl) is
  have hmm := needs_map atom (fun _ => rfl) ms
  have hmw := widths_map atom (fun _ => rfl) ms
  have hlm := needs_map atom (fun _ => rfl) ls
  have hlw := widths_map atom (fun _ => rfl) ls
  rw [fitsB_iff]
  simp only [importsMax, methodsMax, lawsMax, relsMax] at hi hm hl hrl
  simp only [listMax_eq, Wire.depthMax] at hs hsw hf hfw hb hbw hr hrw ⊢
  simp only [depthMax, Wire.depthMax, need, needs, width, widths, list, atom, List.length_cons, List.length_map]
  simp only [List.length_nil, Nat.add_one_le_iff, Nat.max_lt, Nat.max_le]
  omega

/-- A package whose tree is in the wire's bounds and which the install check accepts has a text. -/
theorem package_prints {ifaces : List Ty} {p : Package} (hw : Wire.packageWire p = true)
    (hf : (Wire.packageTree p).fits Wire.nodeMax Wire.depthMax = true) (hc : p.checkWith ifaces = .ok ()) :
    (package p).isSome = true := by
  obtain ⟨hshape, T, hT⟩ := checkWith_parts hc
  obtain ⟨hni, hnm, hnl⟩ := checkShape_bounds hshape
  simp only [Wire.packageWire, Bool.and_eq_true] at hw
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hwd, -⟩, hws⟩, hwi⟩, hwb⟩, hwm⟩, hwl⟩, hwr⟩, -⟩, hwe⟩ := hw
  obtain ⟨xd, hxd, hnd, hwxd⟩ := docSx_prints hwd
  obtain ⟨D, hD, hcs⟩ := fits_node hf
  simp only [Wire.depthMax] at hD
  have hD' : D = 1023 := by omega
  subst hD'
  obtain ⟨xs, hxs, hns, hwxs⟩ := tyWire_prints p.state hws (hcs _ (by simp))
  obtain ⟨xi, hxi, hni', hwxi⟩ := tyWire_prints p.iface hwi (hcs _ (by simp))
  obtain ⟨xb, hxb, hnb, hwxb⟩ := hasType_prints (inferE_sound hT) hwb (hcs _ (by simp))
  replace hxb : termSx 0 p.body = some xb := hxb
  have hfields := (checkWith_checked hc).2
  obtain ⟨row, hcr⟩ := checkFields_checkRels hfields
  obtain ⟨hrl, hkl⟩ := checkRels_bounds hcr
  obtain ⟨D2, hD2, hc2⟩ := fits_node (hcs (.node 2 .empty (p.rels.map Wire.relTree)) (by simp))
  obtain ⟨xR, hxR, hnR, hwR, hlR⟩ := rels_prints p.rels (fun r hr =>
    ⟨List.all_eq_true.mp hwr r hr, hc2 _ (List.mem_map.mpr ⟨r, hr, rfl⟩), hkl r hr⟩)
  have hfit := package_fitsB (is := p.imports) (ms := p.methods) (ls := p.laws) hnd hwxd hni hnm hnl hns hwxs hni' hwxi hnb hwxb
    (xR := xR) (by simp only [Wire.depthMax] at hnR ⊢; omega) hwR (by omega)
  obtain ⟨he, hΔ⟩ := checkWith_closed hc
  obtain ⟨rowE, hce⟩ := checkFields_checkEffects hfields
  have hfitE := package_fitsB_effects (is := p.imports) (ms := p.methods) (ls := p.laws) hnd hwxd hni hnm hnl hns hwxs hni' hwxi hnb hwxb
    (xR := xR) (by simp only [Wire.depthMax] at hnR ⊢; omega) hwR (by omega)
    (xE := p.effects.map fun e => list [atom e.1, atom (Nat.repr e.2.moves)]) (effects_needs p.effects)
    (effects_widths p.effects) (by rw [List.length_map]; exact Nat.le_trans (checkEffects_length hce) hnm)
  have htext : (packageText p).isSome = true := by
    rcases hee : p.effects.isEmpty with _ | _
    · -- grades: the ninth section
      simp [packageText, he, hee, sectionsSx, hxd, hxs, hxi, hxb,
        labels_mapM_atoms _ hwm, labels_mapM_atoms _ hwl, hxR, effects_mapM_sx _ hwe, hfitE]
    · simp [packageText, he, hee, sectionsSx, hxd, hxs, hxi, hxb,
        labels_mapM_atoms _ hwm, labels_mapM_atoms _ hwl, hxR, hfit]
  obtain ⟨text, ht⟩ := Option.isSome_iff_exists.mp htext
  have hread := readPackage_closedText (checkShape_wf hshape).1 (checkShape_wf hshape).2
    (checkFields_rels hfields) (hasType_canon hΔ (by simp) (inferE_sound hT)) he ht
  simp [package, ht, he]

/-- Bytes the decoder accepts, of a package the install check accepts, have a text. -/
theorem installed_prints {ifaces : List Ty} {b : ByteArray} {p : Package} (hd : Wire.decodePackage b = .ok p)
    (hc : p.checkWith ifaces = .ok ()) : (package p).isSome = true := by
  have he := Wire.decodePackage_eq_ok_iff.1 hd
  unfold Wire.encodePackage at he
  split at he
  · rename_i hw
    split at he
    · rename_i hf; exact package_prints hw hf hc
    · cases he
  · cases he

/-- ... and that text reads back to exactly the package (over canonical import interfaces). -/
theorem installed_reads {ifaces : List Ty} {b : ByteArray} {p : Package} (hΔ : ∀ A ∈ ifaces, A.wf = true)
    (hd : Wire.decodePackage b = .ok p) (hc : p.checkWith ifaces = .ok ()) :
    ∃ s, package p = some s ∧ Read.readPackage s = .ok p :=
  ⟨(package p).get (installed_prints hd hc), (Option.some_get _).symm,
    readPackage_checked hΔ hc (Option.some_get _).symm⟩

/-- **The install check reads canonical interfaces**: `checkInstall` takes its imports' interfaces
from the loader (LANG-35, LANG-78), which re-checks every package of the closure, so each one passed
`checkShape` and is canonical; a package without holes passed the closed check over them. That is
`installed_reads`' premise, discharged by the check itself. -/
theorem checkInstall_checked {D : Type} {digestOf : ByteArray → Option D} {look : Kernel.Receive.Pinned D}
    {b : ByteArray} (h : checkInstall digestOf look b = .ok ()) :
    ∃ (p : Package) (ifaces : List Ty), Wire.decodePackage b = .ok p ∧
      (p.holes = [] → p.checkWith ifaces = .ok ()) ∧ ∀ A ∈ ifaces, A.wf = true := by
  unfold checkInstall at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  cases hd : Wire.decodePackage b with
  | error e => simp [hd] at h
  | ok p =>
  simp only [hd] at h
  cases hl : loadAllContextual digestOf look (closureDepthMax - 1) p.imports ⟨[], [], []⟩ with
  | error e => simp [hl] at h
  | ok x =>
  obtain ⟨L, gis⟩ := x
  simp only [hl] at h
  cases ha : admitContextual digestOf (fun _ => unresolvedBody) b p L gis with
  | error e => simp [ha] at h
  | ok y =>
  obtain ⟨ifaces, hif, hc⟩ := admitContextual_ifaces ha
  refine ⟨p, ifaces, rfl, hc, fun A hA => ?_⟩
  obtain ⟨i, hi⟩ := List.getElem?_of_mem hA
  have hm := ifacesAt_spec hif i A hi
  simp only [List.getElem?_map, Option.map_eq_some_iff] at hm
  obtain ⟨P, hP, rfl⟩ := hm
  exact (checkShape_wf ((loadAllUsing_inv digestOf look _
    (fun hi hw ha => admitContextual_inv hi hw ha) _ _ _ Inv.empty hl).1.2.2.2 _ P hP).1).2

/-- **Every package without holes the install check admits has a text that reads back to it**:
`installed_reads` over the interfaces `checkInstall` itself supplied. -/
theorem install_reads {D : Type} {digestOf : ByteArray → Option D} {look : Kernel.Receive.Pinned D}
    {b : ByteArray} (h : checkInstall digestOf look b = .ok ()) :
    ∃ p : Package, Wire.decodePackage b = .ok p ∧
      (p.holes = [] → ∃ s, package p = some s ∧ Read.readPackage s = .ok p) := by
  obtain ⟨p, ifaces, hd, hc, hΔ⟩ := checkInstall_checked h
  exact ⟨p, hd, fun h0 => installed_reads hΔ hd (hc h0)⟩

/-- An encodable package's state type prints within the wire's depth: `StdFits`' premise. -/
theorem state_prints {p : Package} {b : ByteArray} (he : Wire.encodePackage p = some b) :
    TyPrints (depthMax - 2) p.state := by
  unfold Wire.encodePackage at he
  split at he
  · rename_i hw
    split at he
    · rename_i hf
      simp only [Wire.packageWire, Bool.and_eq_true] at hw
      obtain ⟨D, hD, hcs⟩ := fits_node hf
      have := tyWire_prints p.state hw.1.1.1.1.1.1.1.2 (hcs _ (by simp))
      exact this.mono (by simp only [depthMax, Wire.depthMax] at hD ⊢; omega)
    · cases he
  · cases he

/-! ## The stdlib's laws over an encodable package's state: `StdFits`' premise discharged -/

theorem quorum_text_at {p : Package} {b : ByteArray} {T : Ty} {ms : List ByteArray} {k : Nat} {g : Label}
    {t : Term} (he : Wire.encodePackage p = some b) (h : Std.quorum p.state T ms k g = .ok t)
    (hg : labelOk g = true) : (term t).isSome = true :=
  quorum_text h (state_prints he) hg

theorem allowlist_text_at {p : Package} {b : ByteArray} {ids : List ByteArray} {t : Term}
    (he : Wire.encodePackage p = some b) (h : Std.allowlist p.state ids = .ok t) : (term t).isSome = true :=
  allowlist_text h (state_prints he)

theorem machine_text_at {p : Package} {b : ByteArray} {f : Label} {states : List Label} {initial : Label}
    {methods : List Label} {edges : List (Label × Label × Label)} {t : Term} (he : Wire.encodePackage p = some b)
    (h : Std.machine p.state f states initial methods edges = .ok t) (hf : labelOk f = true)
    (hst : ∀ x ∈ states, labelOk x = true) : (term t).isSome = true :=
  machine_text h (state_prints he) hf hst

/-! ## Teeth -/

/-- A record type nested `n` levels through field `f`. -/
private def deepTy : Nat → Ty
  | 0 => .record []
  | n + 1 => .record [("f", deepTy n)]

/-- Its value, nested the same way. -/
private def deepT : Nat → Term
  | 0 => .record []
  | n + 1 => .record [("f", deepT n)]

/-- A package at the wire's depth bound: its body's and its interface's trees are 1023 deep. -/
private def deepPkg : Package := ⟨[], .record [], deepTy 511, deepT 511, [], [], [], .empty, [], []⟩

theorem deep_wire : Wire.packageWire deepPkg = true := by decide +kernel

theorem deep_fits : (Wire.packageTree deepPkg).fits Wire.nodeMax Wire.depthMax = true := by decide +kernel

/-- One level deeper and the wire refuses it. -/
theorem deeper_unfit :
    (Wire.packageTree { deepPkg with iface := deepTy 512, body := deepT 512 }).fits Wire.nodeMax Wire.depthMax = false := by
  decide +kernel

theorem deep_checks_toBool : (deepPkg.checkWith []).toBool = true := by decide +kernel

theorem deep_checks : deepPkg.checkWith [] = .ok () := by
  have h := deep_checks_toBool
  revert h
  cases deepPkg.checkWith [] <;> simp [Except.toBool]

theorem deep_prints : (package deepPkg).isSome = true := package_prints deep_wire deep_fits deep_checks

/-- Its text needs exactly `Read.depthMax`: a reader one level shallower would refuse it. -/
theorem deep_needs_depthMax :
    (sectionsSx deepPkg).map (fun xs => need (list (atom "package" :: xs))) = some depthMax := by decide +kernel

/-- A label with a space is not one atom, so the wire refuses it as the printer does. -/
theorem spaced_label_no_bytes :
    (Wire.encodePackage ⟨[], .record [], .record [("a b", .nat)], .record [("a b", .nat 0)], [], [], [], .empty, [], []⟩).isNone = true := by
  decide +kernel

private def labelTree (ℓ : Label) : Tree :=
  .node 0 .empty [.node 0 .empty [], Wire.tyTree (.record []), .node 4 .empty [.node 6 ℓ.toUTF8 [.node 0 .empty []]],
    Wire.termTree (.record []), .node 1 .empty [], .node 1 .empty [], .node 2 .empty [], .node 0 .empty [], .node 3 .empty [],
    .node 4 .empty []]

/-- The decoder's side of the narrowing: a package tree whose interface row holds the label `a b`
reads as no package, and the same tree with `ab` reads. -/
theorem spaced_label_tree_refused : (Wire.packageOf (labelTree "a b")).isNone = true := by decide +kernel

theorem atom_label_tree_reads : (Wire.packageOf (labelTree "ab")).isSome = true := by decide +kernel

end Nanodregg.Lang.Print
