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

theorem Refusal.name_injective (a b : Refusal) (h : a.name = b.name) : a = b := by
  cases a <;> cases b <;> simp_all [Refusal.name]

private theorem plan_ok {l : ByteArray} {g : Grain} {p : Plan} (h : plan l g = .ok p) :
    clean l = true ∧ clean g.idHex = true ∧ clean g.entry = true ∧ g.kind = .app ∧
      p = { program := pkgDir l g ++ [g.entry], read := [pkgDir l g], write := [volDir l g],
            exec := [], connect := [], hidden := [storeDir l, membersDir l] } := by
  unfold plan at h
  by_cases hl : clean l = true <;> by_cases hi : clean g.idHex = true <;>
    by_cases he : clean g.entry = true <;>
    simp_all [bind, Except.bind, pure, Except.pure] <;>
    cases hk : g.kind <;> simp_all

theorem plan_app_only {l : ByteArray} {g : Grain} {p : Plan} (h : plan l g = .ok p) :
    g.kind = .app := (plan_ok h).2.2.2.1

theorem plan_paths {l : ByteArray} {g : Grain} {p : Plan} (h : plan l g = .ok p) :
    ∀ x ∈ p.allowed, grainDir l g <+: x := by
  obtain ⟨-, -, -, -, rfl⟩ := plan_ok h
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
  obtain ⟨-, -, -, -, rfl⟩ := plan_ok h
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
    obtain ⟨-, -, -, -, rfl⟩ := plan_ok h
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
  obtain ⟨hl, hi, he, -, rfl⟩ := plan_ok h
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := lits_clean
  intro x hx c hc
  simp only [Plan.allowed, List.cons_append, List.nil_append, List.append_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl <;>
    simp only [pkgDir, volDir, grainDir, storeDir, membersDir, worldRoot,
      List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hc <;>
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption

/-- Each refusal is exactly its unclean input (checked in order: label, id, entry). -/
theorem plan_refuses_label (l : ByteArray) (g : Grain) (h : clean l = false) :
    plan l g = .error .labelUnclean := by
  simp [plan, h, bind, Except.bind]

theorem plan_refuses_id (l : ByteArray) (g : Grain) (hl : clean l = true) (h : clean g.idHex = false) :
    plan l g = .error .idUnclean := by
  simp [plan, hl, h, bind, Except.bind, pure, Except.pure]

theorem plan_refuses_entry (l : ByteArray) (g : Grain) (hl : clean l = true) (hi : clean g.idHex = true)
    (h : clean g.entry = false) : plan l g = .error .entryUnclean := by
  simp [plan, hl, hi, h, bind, Except.bind, pure, Except.pure]

end Nanodregg.Hosting.Proofs
