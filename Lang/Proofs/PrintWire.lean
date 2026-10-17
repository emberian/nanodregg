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
  the loader, so they are canonical, and every package it admits has a text that reads back to
  it, with no premise (LANG-35);
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
    exact (typrints_atom _ (.inr (.inr rfl))).mono (by omega)
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
    p.checkShape = .ok () ∧ ∃ T, inferE ifaces [] p.body = .ok T := by
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

theorem package_fitsB {is : List ByteArray} {ms ls : List Label} {xs xi xb : Read.SExp}
    (hi : is.length ≤ importsMax) (hm : ms.length ≤ methodsMax) (hl : ls.length ≤ lawsMax)
    (hs : need xs ≤ Wire.depthMax) (hsw : width xs ≤ listMax) (hf : need xi ≤ Wire.depthMax) (hfw : width xi ≤ listMax)
    (hb : need xb ≤ Wire.depthMax) (hbw : width xb ≤ listMax) :
    fitsB (list (atom "package" ::
      [list (atom "imports" :: is.map fun i => .str 0 (hex i)), list [atom "state", xs],
       list [atom "iface", xi], list (atom "methods" :: ms.map atom),
       list (atom "laws" :: ls.map atom), list [atom "body", xb]])) = true := by
  have him := needs_map (fun i : ByteArray => Read.SExp.str 0 (hex i)) (fun _ => rfl) is
  have hiw := widths_map (fun i : ByteArray => Read.SExp.str 0 (hex i)) (fun _ => rfl) is
  have hmm := needs_map atom (fun _ => rfl) ms
  have hmw := widths_map atom (fun _ => rfl) ms
  have hlm := needs_map atom (fun _ => rfl) ls
  have hlw := widths_map atom (fun _ => rfl) ls
  rw [fitsB_iff]
  simp only [importsMax, methodsMax, lawsMax] at hi hm hl
  simp only [listMax_eq, Wire.depthMax] at hs hsw hf hfw hb hbw ⊢
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
  obtain ⟨⟨⟨⟨⟨-, hws⟩, hwi⟩, hwb⟩, hwm⟩, hwl⟩ := hw
  obtain ⟨D, hD, hcs⟩ := fits_node hf
  simp only [Wire.depthMax] at hD
  have hD' : D = 1023 := by omega
  subst hD'
  obtain ⟨xs, hxs, hns, hwxs⟩ := tyWire_prints p.state hws (hcs _ (by simp))
  obtain ⟨xi, hxi, hni', hwxi⟩ := tyWire_prints p.iface hwi (hcs _ (by simp))
  obtain ⟨xb, hxb, hnb, hwxb⟩ := hasType_prints (inferE_sound hT) hwb (hcs _ (by simp))
  replace hxb : termSx 0 p.body = some xb := hxb
  have hfit := package_fitsB (is := p.imports) (ms := p.methods) (ls := p.laws) hni hnm hnl hns hwxs hni' hwxi hnb hwxb
  simp [package, sectionsSx, hxs, hxi, hxb, labels_mapM_atoms _ hwm, labels_mapM_atoms _ hwl, hfit]

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
from the loader (LANG-35), which re-checks every package of the closure, so each one passed
`checkShape` and is canonical. That is `installed_reads`' premise, discharged by the check itself. -/
theorem checkInstall_checked {D : Type} {digestOf : ByteArray → Option D} {look : Kernel.Receive.Pinned D}
    {b : ByteArray} (h : checkInstall digestOf look b = .ok ()) :
    ∃ (p : Package) (ifaces : List Ty), Wire.decodePackage b = .ok p ∧ p.checkWith ifaces = .ok () ∧
      ∀ A ∈ ifaces, A.wf = true := by
  unfold checkInstall at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  repeat' split at h
  all_goals first | (simp at h; done) | skip
  all_goals
    rename_i p hd _ L hl _ ifaces hif _ hc
    refine ⟨p, ifaces, hd, hc, fun A hA => ?_⟩
    obtain ⟨i, hi⟩ := List.getElem?_of_mem hA
    have hm := ifacesAt_spec hif i A hi
    simp only [List.getElem?_map, Option.map_eq_some_iff] at hm
    obtain ⟨P, hP, rfl⟩ := hm
    exact (checkShape_wf ((loadAll_inv digestOf look _ _ _ Inv.empty hl).1.2.2.2 _ P hP).1).2

/-- **Every package the install check admits has a text that reads back to it**, with no premise:
`installed_reads` over the interfaces `checkInstall` itself supplied. -/
theorem install_reads {D : Type} {digestOf : ByteArray → Option D} {look : Kernel.Receive.Pinned D}
    {b : ByteArray} (h : checkInstall digestOf look b = .ok ()) :
    ∃ (p : Package) (s : String), Wire.decodePackage b = .ok p ∧ package p = some s ∧
      Read.readPackage s = .ok p := by
  obtain ⟨p, ifaces, hd, hc, hΔ⟩ := checkInstall_checked h
  obtain ⟨s, hs, hr⟩ := installed_reads hΔ hd hc
  exact ⟨p, s, hd, hs, hr⟩

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
      have := tyWire_prints p.state hw.1.1.1.1.2 (hcs _ (by simp))
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
private def deepPkg : Package := ⟨[], .record [], deepTy 511, deepT 511, [], []⟩

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
    (Wire.encodePackage ⟨[], .record [], .record [("a b", .nat)], .record [("a b", .nat 0)], [], []⟩).isNone = true := by
  decide +kernel

private def labelTree (ℓ : Label) : Tree :=
  .node 0 .empty [.node 0 .empty [], Wire.tyTree (.record []), .node 4 .empty [.node 6 ℓ.toUTF8 [.node 0 .empty []]],
    Wire.termTree (.record []), .node 1 .empty [], .node 1 .empty []]

/-- The decoder's side of the narrowing: a package tree whose interface row holds the label `a b`
reads as no package, and the same tree with `ab` reads. -/
theorem spaced_label_tree_refused : (Wire.packageOf (labelTree "a b")).isNone = true := by decide +kernel

theorem atom_label_tree_reads : (Wire.packageOf (labelTree "ab")).isSome = true := by decide +kernel

end Nanodregg.Lang.Print
