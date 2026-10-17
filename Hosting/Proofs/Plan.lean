/-
# Hosting.Proofs.Plan — a plan stays inside its grain's directory and never touches what is hidden

`plan_paths`: every path a plan allows lies under `worlds/<l>/grains/<id>`. `plan_not_exposed`: no
allowed path is a prefix of a hidden one or lies inside one (the launcher's `Exposed` check is the
same property on canonical OS paths, a second barrier). `plan_app_only`: only an app is planned
until the resident's two-process shape exists (HOSTING-6).
-/
import Hosting.Plan

namespace Nanodregg.Hosting.Proofs

open Nanodregg.Hosting
open Nanodregg.Codec.Path (clean)

theorem labelOk_clean {l : ByteArray} (h : labelOk l = true) : clean l = true := by
  simp only [labelOk, Bool.and_eq_true] at h; exact h.1

private theorem labelFrom_spec (c : ByteArray) : ∀ (n i : Nat), labelFrom c i n = true →
    ∀ j, i ≤ j → j < i + n → (h : j < c.size) → labelByte c[j] = true
  | 0, _, _, j, h1, h2, _ => by omega
  | n + 1, i, hf, j, h1, h2, hj => by
      simp only [labelFrom, Bool.and_eq_true] at hf
      by_cases hji : j = i
      · subst hji
        have := hf.1; rw [dif_pos hj] at this
        exact this
      · exact labelFrom_spec c n (i + 1) hf.2 j (by omega) (by omega) hj

/-- An accepted label holds only lowercase ASCII letters, digits and `-`. -/
theorem labelOk_bytes {l : ByteArray} (h : labelOk l = true) : ∀ x ∈ l.data.toList, labelByte x = true := by
  simp only [labelOk, Bool.and_eq_true] at h
  intro x hx
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hx
  have hj' : j < l.size := by rw [Array.length_toList] at hj; exact hj
  have := labelFrom_spec l l.size 0 h.2 j (by omega) (by omega) hj'
  simp only [Array.getElem_toList]
  simpa only [ByteArray.getElem_eq_getElem_data] using this

/-- A label byte is neither an ASCII uppercase letter nor a non-ASCII byte: so ASCII case folding
and Unicode normalisation are the identity on an accepted label, and two accepted labels that a
case-insensitive file system identifies are equal. -/
theorem labelByte_folds_to_itself (x : UInt8) (h : labelByte x = true) :
    ¬ (65 ≤ x.toNat ∧ x.toNat ≤ 90) ∧ x.toNat < 128 := by
  have all : ∀ n : Fin 256, labelByte (UInt8.ofNat n) = true →
      ¬ (65 ≤ n.val ∧ n.val ≤ 90) ∧ n.val < 128 := by decide +kernel
  have := all ⟨x.toNat, x.toNat_lt⟩ (by simpa using h)
  simpa using this

/-- Two accepted labels that a case-insensitive file system identifies (equal after ASCII case
folding; no accepted byte is non-ASCII, so Unicode folding and normalisation do not apply) are
equal: they name two directories. -/
theorem labels_fold_injective {a b : ByteArray} (ha : labelOk a = true) (hb : labelOk b = true)
    (h : a.data.toList.map foldByte = b.data.toList.map foldByte) : a = b := by
  have fix : ∀ l : ByteArray, labelOk l = true → l.data.toList.map foldByte = l.data.toList := by
    intro l hl
    conv => rhs; rw [← List.map_id l.data.toList]
    apply List.map_congr_left
    intro x hx
    have := (labelByte_folds_to_itself x (labelOk_bytes hl x hx)).1
    unfold foldByte
    have : ¬ (65 ≤ x && x ≤ 90) = true := by
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      intro ⟨h1, h2⟩; exact this ⟨UInt8.le_iff_toNat_le.mp h1, UInt8.le_iff_toNat_le.mp h2⟩
    simp [this]
  rw [fix a ha, fix b hb] at h
  cases a; cases b; simp_all [Array.toList_inj]

/-- Tooth: the fold is a real fold (`W` and `w` are one name to it), so `labels_fold_injective`
is not true of an identity. -/
theorem foldByte_folds : foldByte 87 = foldByte 119 := by decide

/-- Teeth: the label refusal is not vacuous, and a real label passes. -/
theorem labelOk_refuses_upper : labelOk (lit "W1") = false := by decide
theorem labelOk_refuses_nonascii : labelOk ⟨#[0xc3, 0xa9]⟩ = false := by decide
theorem labelOk_accepts : labelOk (lit "w1") = true ∧ labelOk (lit "alice-2") = true := by decide

/-- Each path of a plan in its ROLE: the program is `pkg/<entry>`, only `pkg` is read, only `vol` is
written, nothing else is executable, and the Store and member workspaces are hidden. (The other
theorems speak of `allowed`, the union; this one says which list each path is in, so a plan that
wrote `pkg` and read `vol` is refused here.) -/
theorem plan_roles {l : ByteArray} {g : Grain} {p : Plan} (h : plan l g = .ok p) :
    labelOk l = true ∧ labelOk g.idHex = true ∧ clean g.entry = true ∧ g.kind = .app ∧
      p = { program := pkgDir l g ++ [g.entry], read := [pkgDir l g], write := [volDir l g],
            exec := [], hidden := [storeDir l, membersDir l] } := by
  unfold plan at h
  by_cases hl : labelOk l = true <;> by_cases hi : labelOk g.idHex = true <;>
    by_cases he : clean g.entry = true <;>
    simp_all [bind, Except.bind, pure, Except.pure] <;>
    cases hk : g.kind <;> simp_all

theorem plan_app_only {l : ByteArray} {g : Grain} {p : Plan} (h : plan l g = .ok p) :
    g.kind = .app := (plan_roles h).2.2.2.1

theorem plan_paths {l : ByteArray} {g : Grain} {p : Plan} (h : plan l g = .ok p) :
    ∀ x ∈ p.allowed, grainDir l g <+: x := by
  obtain ⟨-, -, -, -, rfl⟩ := plan_roles h
  intro x hx
  simp only [Plan.allowed, List.cons_append, List.nil_append, List.append_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact ⟨[lit "pkg", g.entry], by simp [pkgDir]⟩
  · exact ⟨[lit "pkg"], by simp [pkgDir]⟩
  · exact ⟨[lit "vol"], by simp [volDir]⟩

/-- `grains` is neither `store` nor `members`, so the grain directory and the hidden directories
part at the third component. -/
private theorem grains_ne : lit "grains" ≠ lit "store" ∧ lit "grains" ≠ lit "members" := by
  decide

/-- Two paths that agree on `c` and then differ are not prefixes of one another. -/
private theorem parted {c s t : Path} {u v : ByteArray} (huv : u ≠ v) :
    ¬ (c ++ u :: s) <+: (c ++ v :: t) := by
  intro ⟨r, hr⟩
  have := congrArg (fun z => z[c.length]?) hr
  simp only [List.append_assoc, List.cons_append, List.getElem?_append_right (Nat.le_refl _),
    Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq] at this
  exact huv this

theorem plan_not_exposed {l : ByteArray} {g : Grain} {p : Plan} (h : plan l g = .ok p) :
    ∀ hd ∈ p.hidden, ∀ x ∈ p.allowed, ¬ hd <+: x ∧ ¬ x <+: hd := by
  intro hd hh x hx
  obtain ⟨y, rfl⟩ := plan_paths h x hx
  obtain ⟨-, -, -, -, rfl⟩ := plan_roles h
  have hx' : grainDir l g ++ y = worldRoot l ++ lit "grains" :: (g.idHex :: y) := by
    simp [grainDir]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rw [hx']
  rcases hh with rfl | rfl
  · exact ⟨parted (Ne.symm grains_ne.1), parted grains_ne.1⟩
  · exact ⟨parted (Ne.symm grains_ne.2), parted grains_ne.2⟩

/-- No grain may reach the Stores files or a members workspace (where the seeds are). -/
theorem plan_no_store_no_workspace {l : ByteArray} {g : Grain} {p : Plan} (h : plan l g = .ok p) :
    ∀ x ∈ p.allowed, ¬ storeDir l <+: x ∧ ¬ membersDir l <+: x := by
  have hh : storeDir l ∈ p.hidden ∧ membersDir l ∈ p.hidden := by
    obtain ⟨-, -, -, -, rfl⟩ := plan_roles h
    simp
  intro x hx
  exact ⟨(plan_not_exposed h _ hh.1 x hx).1, (plan_not_exposed h _ hh.2 x hx).1⟩

private theorem lits_clean :
    clean (lit "worlds") = true ∧ clean (lit "grains") = true ∧ clean (lit "pkg") = true ∧
      clean (lit "vol") = true ∧ clean (lit "store") = true ∧ clean (lit "members") = true := by
  decide

/-- Every component of every path a plan names is clean: so the list-prefix facts above are facts
about directories (no `..`, no `/`, no empty component), up to symlinks, which the sandbox's
deny-default and the launcher's program check answer. -/
theorem plan_components_clean {l : ByteArray} {g : Grain} {p : Plan} (h : plan l g = .ok p) :
    ∀ x ∈ p.allowed ++ p.hidden, ∀ c ∈ x, clean c = true := by
  obtain ⟨hl, hi, he, -, rfl⟩ := plan_roles h
  have hl := labelOk_clean hl
  have hi := labelOk_clean hi
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := lits_clean
  intro x hx c hc
  simp only [Plan.allowed, List.cons_append, List.nil_append, List.append_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl <;>
    simp only [pkgDir, volDir, grainDir, storeDir, membersDir, worldRoot,
      List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hc <;>
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption

/-- Each refusal is exactly its unclean input (checked in order: label, id, entry). -/
theorem plan_refuses_label (l : ByteArray) (g : Grain) (h : labelOk l = false) :
    plan l g = .error .labelUnclean := by
  simp [plan, h, bind, Except.bind]

theorem plan_refuses_id (l : ByteArray) (g : Grain) (hl : labelOk l = true) (h : labelOk g.idHex = false) :
    plan l g = .error .idUnclean := by
  simp [plan, hl, h, bind, Except.bind, pure, Except.pure]

theorem plan_refuses_entry (l : ByteArray) (g : Grain) (hl : labelOk l = true) (hi : labelOk g.idHex = true)
    (h : clean g.entry = false) : plan l g = .error .entryUnclean := by
  simp [plan, hl, hi, h, bind, Except.bind, pure, Except.pure]

/-- Tooth for `Proofs.Wire.decode_encodeAction` on a launch: a real plan (a 64-byte directory
name, the label `w1`, the entry `app`) encodes into one frame. -/
theorem planned_launch_encodes :
    (match plan (lit "w1") { idHex := ⟨Array.replicate 64 97⟩, kind := .app, entry := lit "app" } with
     | .ok p => (Wire.encodeAction { grain := ⟨Array.replicate 64 97⟩, verdict := .launch p }).isSome
     | .error _ => false) = true := by
  decide +kernel

/-- Plans of two different Stores, or of two different grains, allow disjoint trees: no path one
allows is a prefix of a path the other allows (with `labels_fold_injective`, also on a
case-insensitive file system). -/
theorem plan_disjoint {l l' : ByteArray} {g g' : Grain} {p p' : Plan} (h : plan l g = .ok p)
    (h' : plan l' g' = .ok p') (hne : l ≠ l' ∨ g.idHex ≠ g'.idHex) :
    ∀ x ∈ p.allowed, ∀ y ∈ p'.allowed, ¬ x <+: y := by
  intro x hx y hy hxy
  obtain ⟨u, rfl⟩ := plan_paths h x hx
  obtain ⟨v, rfl⟩ := plan_paths h' y hy
  have e1 : grainDir l g ++ u = [lit "worlds"] ++ l :: (lit "grains" :: g.idHex :: u) := by simp [grainDir, worldRoot]
  have e2 : grainDir l' g' ++ v = [lit "worlds"] ++ l' :: (lit "grains" :: g'.idHex :: v) := by simp [grainDir, worldRoot]
  rw [e1, e2] at hxy
  rcases hne with hl | hi
  · exact parted hl hxy
  · by_cases hll : l = l'
    · subst hll
      have e3 : [lit "worlds"] ++ l :: (lit "grains" :: g.idHex :: u) = [lit "worlds", l, lit "grains"] ++ g.idHex :: u := by simp
      have e4 : [lit "worlds"] ++ l :: (lit "grains" :: g'.idHex :: v) = [lit "worlds", l, lit "grains"] ++ g'.idHex :: v := by simp
      rw [e3, e4] at hxy
      exact parted hi hxy
    · exact parted hll hxy

end Nanodregg.Hosting.Proofs
