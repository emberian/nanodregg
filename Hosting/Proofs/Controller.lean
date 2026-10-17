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
import Lang.Proofs.Print

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

/-- Distinct ids get distinct directories: LANG's `hex_injective` through UTF-8. -/
theorem dirOf_injective {a b : ByteArray} (h : dirOf a = dirOf b) : a = b := by
  unfold dirOf at h
  exact Lang.Print.hex_injective (String.toByteArray_inj.mp h)

section DirLabel

open Nanodregg.Codec.Path (forbidden sep nul freeFrom agreeFrom isWord dot dotdot clean componentMax)

private theorem labelByte_nat {x : UInt8} (h : labelByte x = true) :
    (97 ≤ x.toNat ∧ x.toNat ≤ 122) ∨ (48 ≤ x.toNat ∧ x.toNat ≤ 57) ∨ x.toNat = 45 := by
  simp only [labelByte, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq,
    UInt8.le_iff_toNat_le] at h
  rcases h with (⟨h1, h2⟩ | ⟨h1, h2⟩) | h1
  · exact .inl ⟨by simpa using h1, by simpa using h2⟩
  · exact .inr (.inl ⟨by simpa using h1, by simpa using h2⟩)
  · exact .inr (.inr (by simp [h1]))

private theorem labelByte_free {x : UInt8} (h : labelByte x = true) : forbidden x = false := by
  have := labelByte_nat h
  simp only [forbidden, sep, nul, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq]
  constructor <;> intro he <;> subst he <;> simp at this

private theorem labelFrom_of (c : ByteArray) : ∀ (n i : Nat),
    (∀ j (h : j < c.size), i ≤ j → labelByte c[j] = true) → labelFrom c i n = true
  | 0, _, _ => rfl
  | n + 1, i, h => by
    simp only [labelFrom, Bool.and_eq_true]
    refine ⟨?_, labelFrom_of c n (i + 1) (fun j hj hij => h j hj (by omega))⟩
    split
    · exact h i ‹_› (Nat.le_refl _)
    · rfl

private theorem freeFrom_of (c : ByteArray) : ∀ (n i : Nat),
    (∀ j (h : j < c.size), i ≤ j → labelByte c[j] = true) → freeFrom c i n = true
  | 0, _, _ => rfl
  | n + 1, i, h => by
    simp only [freeFrom, Bool.and_eq_true]
    refine ⟨?_, freeFrom_of c n (i + 1) (fun j hj hij => h j hj (by omega))⟩
    split
    · simp [labelByte_free (h i ‹_› (Nat.le_refl _))]
    · rfl

private theorem not_dot {x : UInt8} (h : labelByte x = true) : (x == 46) = false := by
  have := labelByte_nat h
  simp only [beq_eq_false_iff_ne, ne_eq]
  intro he; subst he; simp at this

/-- A component of label bytes, nonempty and at most `componentMax` long, is an accepted label. -/
theorem labelOk_of {l : ByteArray} (h0 : 0 < l.size) (h64 : l.size ≤ componentMax)
    (hb : ∀ j (h : j < l.size), labelByte l[j] = true) : labelOk l = true := by
  have hd := not_dot (hb 0 h0)
  simp only [labelOk, clean, isWord, dot, dotdot, Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨?_, by simpa using h64⟩, ?_⟩, ?_⟩, freeFrom_of l _ 0 (fun j h _ => hb j h)⟩,
    labelFrom_of l _ 0 (fun j h _ => hb j h)⟩
  · simpa using Nat.pos_iff_ne_zero.mp h0
  · simp only [Bool.not_eq_true', Bool.and_eq_false_iff]; right
    show agreeFrom l _ 0 (0 + 1) = false
    rw [agreeFrom, dif_pos h0, dif_pos (by decide), Bool.and_eq_false_iff]; left
    exact hd
  · simp only [Bool.not_eq_true', Bool.and_eq_false_iff]; right
    show agreeFrom l _ 0 (1 + 1) = false
    rw [agreeFrom, dif_pos h0, dif_pos (by decide), Bool.and_eq_false_iff]; left
    exact hd

private theorem hexDigit_enc : ∀ n, n < 16 →
    ([Lang.Print.hexDigit n].utf8Encode.data.toList.length = 1 ∧
     [Lang.Print.hexDigit n].utf8Encode.data.toList.all labelByte = true) := by
  decide

private theorem enc_hex : ∀ l : List Char, (∀ c ∈ l, ∃ n, n < 16 ∧ c = Lang.Print.hexDigit n) →
    l.utf8Encode.data.toList.length = l.length ∧ l.utf8Encode.data.toList.all labelByte = true
  | [], _ => by simp [List.utf8Encode]
  | c :: l, h => by
    obtain ⟨n, hn, rfl⟩ := h c (by simp)
    obtain ⟨h1, h2⟩ := hexDigit_enc n hn
    obtain ⟨h3, h4⟩ := enc_hex l (fun c hc => h c (by simp [hc]))
    rw [List.utf8Encode_cons]
    simp only [ByteArray.data_append, Array.toList_append, List.length_append, List.all_append,
      Bool.and_eq_true, List.length_cons] at h1 h2 h3 h4 ⊢
    exact ⟨by omega, h2, h4⟩

private theorem hexChars_length (b : ByteArray) : (Lang.Print.hexChars b).length = 2 * b.size := by
  unfold Lang.Print.hexChars
  rw [← Array.foldr_toList]
  have : ∀ l : List UInt8, (l.foldr (fun x cs => Lang.Print.hexDigit (x.toNat / 16) ::
      Lang.Print.hexDigit (x.toNat % 16) :: cs) []).length = 2 * l.length := by
    intro l; induction l with
    | nil => rfl
    | cons x xs ih => simp [ih]; omega
  rw [this, Array.length_toList]; rfl

/-- A grain directory name is an accepted label: lowercase hex, two digits per byte, so a World
id of 1 to 32 bytes never meets `plan`'s `idUnclean` (and two ids are never one directory on a
case-insensitive file system). -/
theorem dirOf_labelOk {b : ByteArray} (h0 : 0 < b.size) (h32 : b.size ≤ 32) : labelOk (dirOf b) = true := by
  have henc := enc_hex (Lang.Print.hexChars b) (fun c hc => Lang.Print.hexChars_digit hc)
  have hd : (dirOf b).data.toList = (Lang.Print.hexChars b).utf8Encode.data.toList := by
    simp [dirOf, Lang.Print.hex]
  have hs : (dirOf b).size = 2 * b.size := by
    rw [← ByteArray.size_data, ← Array.length_toList, hd, henc.1, hexChars_length]
  apply labelOk_of (by omega) (by rw [hs]; simp [componentMax]; omega)
  intro j hj
  have hall := henc.2
  rw [← hd, List.all_eq_true] at hall
  exact hall _ (by simp [ByteArray.getElem_eq_getElem_data])

end DirLabel

variable {D : Type} [Ord D] [DecidableEq D]

/-- Every action is decided on the World's own cell at a touched id, and names that id's directory:
no caller pairs a cell with a name. -/
theorem reconcile_names {E : Env D} {bytesOf : D → ByteArray} {label pkgId : ByteArray} {now : Nat}
    {live : List Live} {w : World D} {ids : List D} {a : Action}
    (h : a ∈ reconcile E bytesOf label pkgId now live w ids) :
    ∃ i ∈ ids, a.grain = dirOf (bytesOf i) ∧
      decideCell label pkgId now live (dirOf (bytesOf i)) (w.live E i) = some a.verdict := by
  unfold reconcile at h
  obtain ⟨i, hm, hd⟩ := List.mem_filterMap.mp h
  refine ⟨i, List.mem_eraseDups.mp (List.mem_of_mem_take hm), ?_⟩
  rcases hv : decideCell label pkgId now live (dirOf (bytesOf i)) (w.live E i) with _ | v
  · simp [hv] at hd
  · simp [hv] at hd
    subst hd
    exact ⟨rfl, rfl⟩

theorem filterMap_sublist_map {α β : Type} (l : List α) (f : α → Option β) (g : α → β)
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
theorem reconcile_one_per_id {E : Env D} {bytesOf : D → ByteArray} {label pkgId : ByteArray} {now : Nat}
    {live : List Live} {w : World D} {ids : List D}
    (hnd : ((ids.eraseDups.take Bounds.grainsMax).map fun i => dirOf (bytesOf i)).Nodup) :
    ((reconcile E bytesOf label pkgId now live w ids).map (·.grain)).Nodup := by
  unfold reconcile
  rw [List.map_filterMap]
  refine hnd.sublist (filterMap_sublist_map _ _ _ ?_)
  intro i b hb
  rcases hv : decideCell label pkgId now live (dirOf (bytesOf i)) (w.live E i) with _ | v <;>
    simp [hv] at hb
  exact hb.symm

theorem reconcile_bounded (E : Env D) (bytesOf : D → ByteArray) (label pkgId : ByteArray) (now : Nat)
    (live : List Live) (w : World D) (ids : List D) :
    (reconcile E bytesOf label pkgId now live w ids).length ≤ Bounds.grainsMax := by
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
theorem reconcile_distinct {E : Env D} {bytesOf : D → ByteArray} (hb : Function.Injective bytesOf)
    {label pkgId : ByteArray} {now : Nat} {live : List Live} {w : World D} {ids : List D} :
    ((reconcile E bytesOf label pkgId now live w ids).map (·.grain)).Nodup :=
  reconcile_one_per_id (List.Pairwise.map (fun i => dirOf (bytesOf i))
    (fun _ _ hne heq => hne (hb (dirOf_injective heq)))
    ((eraseDups_nodup ids).sublist (List.take_sublist _ _)))

theorem digest_bytes_injective : Function.Injective Codec.Digest.bytes := by
  intro a b h; cases a; cases b; simp_all

/-- On the deployed ids (32-byte digests), one action per grain per call. -/
theorem reconcile_distinct_deployed {E : Env Codec.Digest} {label pkgId : ByteArray} {now : Nat} {live : List Live}
    {w : World Codec.Digest} {ids : List Codec.Digest} :
    ((reconcile E Codec.Digest.bytes label pkgId now live w ids).map (·.grain)).Nodup :=
  reconcile_distinct digest_bytes_injective

/-- On the deployed ids (32-byte digests), every grain the controller names is an accepted label:
`plan` never refuses `idUnclean` for a World id. -/
theorem reconcile_labels_deployed {E : Env Codec.Digest} {label pkgId : ByteArray} {now : Nat}
    {live : List Live} {w : World Codec.Digest} {ids : List Codec.Digest} :
    ∀ a ∈ reconcile E Codec.Digest.bytes label pkgId now live w ids, labelOk a.grain = true := by
  intro a ha
  obtain ⟨i, -, hi⟩ := List.mem_filterMap.mp ha
  obtain ⟨v, -, rfl⟩ := Option.map_eq_some_iff.mp hi
  exact dirOf_labelOk (by rw [i.size_eq]; decide) (by rw [i.size_eq]; exact Nat.le_refl _)

end Nanodregg.Hosting.Proofs
