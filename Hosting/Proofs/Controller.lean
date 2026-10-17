/-
# Hosting.Proofs.Controller — the controller launches only desired, lifecycle, startable grains

`launch_sound`: a launch is for a lifecycle object whose state decodes, whose desired phase is
`running`, that has no running child, is not crash-looping, and whose plan exists (and is that
plan). `kill_sound`: a kill is for a running child whose cell is gone, is not a lifecycle object,
does not decode, or does not desire `running`. `launch_complete`: such a grain IS launched.
`malformed_running_killed`: fail closed. `reconcile_names`: every action is decided on the World's
own cell at a touched id and names that id's directory.
-/
import Hosting.Controller
import Lang.Print

namespace Nanodregg.Hosting.Proofs

open Nanodregg.Kernel Nanodregg.Hosting Nanodregg.Hosting.Controller

theorem launch_sound {label pkgId : ByteArray} {now : Nat} {live : List Live} {g : ByteArray}
    {cell : Option Cell} {p : Plan}
    (h : decideCell label pkgId now live g cell = some (.launch p)) :
    ∃ c gr, cell = some c ∧ isGrain pkgId c = true ∧ grainOf g c = some (gr, .running) ∧
      runningIn live g = false ∧ crashLooping now live g = false ∧ plan label gr = .ok p := by
  unfold decideCell at h
  rcases cell with _ | c
  · by_cases hu : runningIn live g = true <;> simp_all
  · by_cases hg : isGrain pkgId c = true
    · rcases hgr : grainOf g c with _ | ⟨gr, ph⟩
      · by_cases hu : runningIn live g = true <;> simp_all
      · by_cases hph : ph = .running
        · subst hph
          by_cases hu : runningIn live g = true
          · simp_all
          · by_cases hc : crashLooping now live g = true
            · simp_all
            · rcases hp : plan label gr with r | q
              · simp_all
              · simp_all
        · by_cases hu : runningIn live g = true <;> simp_all
    · by_cases hu : runningIn live g = true <;> simp_all

theorem kill_sound {label pkgId : ByteArray} {now : Nat} {live : List Live} {g : ByteArray}
    {cell : Option Cell} (h : decideCell label pkgId now live g cell = some .kill) :
    runningIn live g = true ∧
      (cell = none ∨ ∃ c, cell = some c ∧
        (isGrain pkgId c = false ∨ grainOf g c = none ∨
          ∃ gr ph, grainOf g c = some (gr, ph) ∧ ph ≠ .running)) := by
  unfold decideCell at h
  rcases cell with _ | c
  · by_cases hu : runningIn live g = true <;> simp_all
  · by_cases hg : isGrain pkgId c = true
    · rcases hgr : grainOf g c with _ | ⟨gr, ph⟩
      · by_cases hu : runningIn live g = true <;> simp_all
      · by_cases hph : ph = .running
        · subst hph
          by_cases hu : runningIn live g = true
          · simp_all
          · by_cases hc : crashLooping now live g = true
            · simp_all
            · rcases hp : plan label gr with r | q <;> simp_all
        · by_cases hu : runningIn live g = true
          · simp_all
            exact ⟨gr, ph, ⟨rfl, rfl⟩, hph⟩
          · simp_all
    · by_cases hu : runningIn live g = true <;> simp_all

/-- Fail closed: a running child whose lifecycle cell no longer decodes is killed. -/
theorem malformed_running_killed {label pkgId : ByteArray} {now : Nat} {live : List Live}
    {g : ByteArray} {c : Cell} (hg : isGrain pkgId c = true) (hgr : grainOf g c = none)
    (hu : runningIn live g = true) :
    decideCell label pkgId now live g (some c) = some .kill := by
  simp [decideCell, hg, hgr, hu]

/-- A lifecycle grain that desires `running`, has no child, is not crash-looping, and has a plan
is launched with that plan. -/
theorem launch_complete {label pkgId : ByteArray} {now : Nat} {live : List Live} {g : ByteArray}
    {c : Cell} {gr : Grain} {p : Plan} (hg : isGrain pkgId c = true)
    (hgr : grainOf g c = some (gr, .running)) (hu : runningIn live g = false)
    (hc : crashLooping now live g = false) (hp : plan label gr = .ok p) :
    decideCell label pkgId now live g (some c) = some (.launch p) := by
  simp [decideCell, hg, hgr, hu, hc, hp]

/-- A crash-looping grain is refused by name, never launched. -/
theorem crashLoop_refused {label pkgId : ByteArray} {now : Nat} {live : List Live} {g : ByteArray}
    {c : Cell} {gr : Grain} (hg : isGrain pkgId c = true)
    (hgr : grainOf g c = some (gr, .running)) (hu : runningIn live g = false)
    (hc : crashLooping now live g = true) :
    decideCell label pkgId now live g (some c) = some (.refuse .crashLoop) := by
  simp [decideCell, hg, hgr, hu, hc]

private theorem digit_inj : ∀ a b : Fin 16, Lang.Print.hexDigit a.val = Lang.Print.hexDigit b.val → a = b := by
  decide

private theorem byte_inj {x y : UInt8}
    (h1 : Lang.Print.hexDigit (x.toNat / 16) = Lang.Print.hexDigit (y.toNat / 16))
    (h2 : Lang.Print.hexDigit (x.toNat % 16) = Lang.Print.hexDigit (y.toNat % 16)) : x = y := by
  have hx := x.toNat_lt; have hy := y.toNat_lt
  have e1 := congrArg Fin.val (digit_inj ⟨x.toNat / 16, by omega⟩ ⟨y.toNat / 16, by omega⟩ h1)
  have e2 := congrArg Fin.val (digit_inj ⟨x.toNat % 16, by omega⟩ ⟨y.toNat % 16, by omega⟩ h2)
  simp only at e1 e2
  apply UInt8.toNat_inj.mp
  omega

private def hexL (l : List UInt8) : List Char :=
  l.foldr (fun x cs => Lang.Print.hexDigit (x.toNat / 16) :: Lang.Print.hexDigit (x.toNat % 16) :: cs) []

private theorem hexL_inj : ∀ {a b : List UInt8}, hexL a = hexL b → a = b
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [hexL] at h
  | _ :: _, [], h => by simp [hexL] at h
  | x :: xs, y :: ys, h => by
    simp only [hexL, List.foldr_cons, List.cons.injEq] at h
    obtain ⟨h1, h2, h3⟩ := h
    rw [byte_inj h1 h2, hexL_inj h3]

/-- Distinct ids get distinct directories. -/
theorem dirOf_injective {a b : ByteArray} (h : dirOf a = dirOf b) : a = b := by
  unfold dirOf Lang.Print.hex Lang.Print.hexChars at h
  have h' := String.ofList_inj.mp (String.toByteArray_inj.mp h)
  rw [← Array.foldr_toList, ← Array.foldr_toList] at h'
  have := hexL_inj h'
  cases a; cases b; simp_all

variable {D : Type} [Ord D] [DecidableEq D]

/-- Every action is decided on the World's own cell at a touched id, and names that id's directory:
no caller pairs a cell with a name. -/
theorem reconcile_names {bytesOf : D → ByteArray} {label pkgId : ByteArray} {now : Nat}
    {live : List Live} {w : World D} {ids : List D} {a : Action}
    (h : a ∈ reconcile bytesOf label pkgId now live w ids) :
    ∃ i ∈ ids, a.grain = dirOf (bytesOf i) ∧
      decideCell label pkgId now live (dirOf (bytesOf i)) (w.live i) = some a.verdict := by
  unfold reconcile at h
  obtain ⟨i, hm, hd⟩ := List.mem_filterMap.mp h
  refine ⟨i, List.mem_eraseDups.mp (List.mem_of_mem_take hm), ?_⟩
  rcases hv : decideCell label pkgId now live (dirOf (bytesOf i)) (w.live i) with _ | v
  · simp [hv] at hd
  · simp [hv] at hd
    subst hd
    exact ⟨rfl, rfl⟩

private theorem filterMap_sublist_map {α β : Type} (l : List α) (f : α → Option β) (g : α → β)
    (h : ∀ a b, f a = some b → b = g a) : List.Sublist (l.filterMap f) (l.map g) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rcases hf : f a with _ | b
    · simp only [List.filterMap_cons, hf, List.map_cons]
      exact ih.cons _
    · simp only [List.filterMap_cons, hf, List.map_cons, h a b hf]
      exact ih.cons_cons _

/-- At most one action per grain, given distinct directories for the distinct touched ids (`dirOf`
is lowercase hex, so distinct id bytes give distinct directories). -/
theorem reconcile_one_per_id {bytesOf : D → ByteArray} {label pkgId : ByteArray} {now : Nat}
    {live : List Live} {w : World D} {ids : List D}
    (hnd : ((ids.eraseDups.take Bounds.grainsMax).map fun i => dirOf (bytesOf i)).Nodup) :
    ((reconcile bytesOf label pkgId now live w ids).map (·.grain)).Nodup := by
  unfold reconcile
  rw [List.map_filterMap]
  refine hnd.sublist (filterMap_sublist_map _ _ _ ?_)
  intro i b hb
  rcases hv : decideCell label pkgId now live (dirOf (bytesOf i)) (w.live i) with _ | v <;>
    simp [hv] at hb
  exact hb.symm

theorem reconcile_bounded (bytesOf : D → ByteArray) (label pkgId : ByteArray) (now : Nat)
    (live : List Live) (w : World D) (ids : List D) :
    (reconcile bytesOf label pkgId now live w ids).length ≤ Bounds.grainsMax := by
  unfold reconcile
  exact Nat.le_trans (List.length_filterMap_le _ _) (List.length_take_le _ _)

omit [Ord D] in
private theorem eraseDups_nodup_le : ∀ (n : Nat) (l : List D), l.length ≤ n → l.eraseDups.Nodup
  | 0, [], _ => by simp
  | 0, _ :: _, h => absurd h (by simp)
  | _ + 1, [], _ => by simp
  | n + 1, a :: as, h => by
    rw [List.eraseDups_cons]
    refine List.nodup_cons.mpr ⟨fun hm => ?_, eraseDups_nodup_le n _ ?_⟩
    · have := List.mem_eraseDups.mp hm
      simp at this
    · exact Nat.le_trans (List.length_filter_le _ _) (by simp at h; omega)

omit [Ord D] in
private theorem eraseDups_nodup (l : List D) : l.eraseDups.Nodup := eraseDups_nodup_le _ l (Nat.le_refl _)

/-- One action per grain whenever distinct ids have distinct bytes (`reconcile_one_per_id` with its
premise discharged by `dirOf_injective`). -/
theorem reconcile_distinct {bytesOf : D → ByteArray} (hb : Function.Injective bytesOf)
    {label pkgId : ByteArray} {now : Nat} {live : List Live} {w : World D} {ids : List D} :
    ((reconcile bytesOf label pkgId now live w ids).map (·.grain)).Nodup :=
  reconcile_one_per_id (List.Pairwise.map (fun i => dirOf (bytesOf i))
    (fun _ _ hne heq => hne (hb (dirOf_injective heq)))
    ((eraseDups_nodup ids).sublist (List.take_sublist _ _)))

theorem digest_bytes_injective : Function.Injective Codec.Digest.bytes := by
  intro a b h; cases a; cases b; simp_all

/-- On the deployed ids (32-byte digests), one action per grain per call. -/
theorem reconcile_distinct_deployed {label pkgId : ByteArray} {now : Nat} {live : List Live}
    {w : World Codec.Digest} {ids : List Codec.Digest} :
    ((reconcile Codec.Digest.bytes label pkgId now live w ids).map (·.grain)).Nodup :=
  reconcile_distinct digest_bytes_injective

end Nanodregg.Hosting.Proofs
