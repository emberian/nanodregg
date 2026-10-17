/-
# Kernel.Proofs.TrieRetain — `retainAt` is the canonical erase (KERNEL-41)

* `toList_retainAt`: what `retainAt path q` lists is the listing filtered by `q`, in order, when `q`
  keeps every entry off the path.
* `canon_retainAt`: it keeps a trie canonical (a node left with one key collapses to that key's
  leaf, one left with none to `empty`).
* `retainAt_eq_build`: it IS `build` of the filtered listing, so the retained trie, and its root,
  depend on the kept contents only (KERNEL-23's history independence carries over).
* `get_retainAt`: every key reads what it read, if `q` keeps it, and nothing otherwise.
-/
import Kernel.Proofs.Trie

namespace Nanodregg.Kernel.Trie

variable {K V D : Type} (S : Spec K V D)

/-- Key `k`'s bits from depth `d` on are `path`: `k` lies in the subtree at `path`. -/
def Under : Nat → List Bool → K → Prop
  | _, [], _ => True
  | d, b :: p, k => S.bit k d = b ∧ Under (d + 1) p k

theorem toList_join (l r : T K V D) : (join S l r).toList = l.toList ++ r.toList := by
  unfold join; split <;> simp [T.toList, mkNode]

/-- A retain that dropped nothing returned its trie unchanged. -/
theorem retainAll_unchanged (q : K → V → Bool) :
    ∀ t : T K V D, (retainAll S q t).2 = false → (retainAll S q t).1 = t
  | .empty, _ => rfl
  | .leaf h kvs, hc => by
      simp only [retainAll] at hc ⊢
      by_cases hall : kvs.all (fun p => q p.1 p.2) = true
      · rw [if_pos hall]
      · rw [if_neg hall] at hc
        by_cases he : (kvs.filter fun p => q p.1 p.2).isEmpty = true
        · rw [if_pos he] at hc; simp at hc
        · rw [if_neg he] at hc; simp at hc
  | .node h l r, hc => by
      simp only [retainAll] at hc ⊢
      split
      · rename_i hab; simp [hab] at hc
      · rfl

theorem toList_retainAll (q : K → V → Bool) :
    ∀ t : T K V D, (retainAll S q t).1.toList = t.toList.filter fun p => q p.1 p.2
  | .empty => rfl
  | .leaf h kvs => by
      simp only [retainAll]
      split
      · rename_i hall
        simp only [T.toList]
        exact (List.filter_eq_self.mpr fun p hp => (List.all_eq_true.mp hall) p hp).symm
      · split
        · rename_i he; simp only [T.toList]; exact (List.isEmpty_iff.mp he).symm
        · simp [T.toList, mkLeaf]
  | .node h l r => by
      have hl := toList_retainAll q l
      have hr := toList_retainAll q r
      simp only [retainAll]
      split
      · simp only [toList_join, T.toList, List.filter_append, hl, hr]
      · rename_i hab
        simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at hab
        rw [retainAll_unchanged S q l hab.1] at hl
        rw [retainAll_unchanged S q r hab.2] at hr
        simp only [T.toList, List.filter_append, ← hl, ← hr]

/-- Two canonical children at `d + 1`, routed by bit `d`, join into a canonical trie at `d`. -/
theorem canon_join {d : Nat} {l r : T K V D} (hd : d < S.depth) (hl : Canon S (d + 1) l)
    (hr : Canon S (d + 1) r) (hlb : ∀ p ∈ l.toList, S.bit p.1 d = false)
    (hrb : ∀ p ∈ r.toList, S.bit p.1 d = true) : Canon S d (join S l r) := by
  obtain ⟨hlR, hlW, hlS⟩ := hl
  obtain ⟨hrR, hrW, hrS⟩ := hr
  have node : 2 ≤ l.toList.length + r.toList.length → Canon S d (mkNode S l r) := fun h2 =>
    ⟨⟨hlb, hrb, hlR, hrR⟩, ⟨rfl, hlW, hrW⟩, ⟨hd, h2, hlS, hrS⟩⟩
  have leafOk : ∀ (h : D) (x : K × V), Routed S (d + 1) (T.leaf h [x] : T K V D) →
      WF S (T.leaf h [x] : T K V D) → Canon S d (T.leaf h [x] : T K V D) :=
    fun h x hR hW => ⟨hR, hW, by simp, fun _ => rfl⟩
  match l, r, hlS, hrS with
  | .empty, .empty, _, _ => exact canon_empty S d
  | .empty, .leaf h [], _, hs => exact absurd rfl hs.1
  | .empty, .leaf h [x], _, _ => exact leafOk h x hrR hrW
  | .empty, .leaf h (a :: b :: rest), _, _ => exact node (by simp [T.toList])
  | .empty, .node h l' r', _, hs => exact node (by simpa [T.toList] using hs.2.1)
  | .leaf h [], _, hs, _ => exact absurd rfl hs.1
  | .leaf h [x], .empty, _, _ => exact leafOk h x hlR hlW
  | .leaf h [x], .leaf h' (y :: ys), _, _ => exact node (by simp [T.toList]; omega)
  | .leaf h [x], .leaf h' [], _, hs => exact absurd rfl hs.1
  | .leaf h [x], .node h' l' r', _, hs =>
      refine node ?_
      have h2 := hs.2.1
      simp only [T.toList, List.length_append, List.length_cons, List.length_nil] at h2 ⊢
      omega
  | .leaf h (a :: b :: rest), r, _, _ => exact node (by simp [T.toList]; omega)
  | .node h l' r', r, hs, _ =>
      refine node ?_
      have h2 := hs.2.1
      simp only [T.toList, List.length_append] at h2 ⊢
      omega

theorem canon_retainAll (q : K → V → Bool) :
    ∀ (d : Nat) (t : T K V D), Canon S d t → Canon S d (retainAll S q t).1
  | d, .empty, _ => canon_empty S d
  | d, .leaf h kvs, ⟨hR, hW, hS⟩ => by
      simp only [retainAll]
      split
      · exact ⟨hR, hW, hS⟩
      · split
        · exact canon_empty S d
        · rename_i he
          have hne : kvs.filter (fun p => q p.1 p.2) ≠ [] := fun h0 => by simp [h0] at he
          refine ⟨(hR.sublist (List.Sublist.map _ List.filter_sublist)), rfl, hne, fun hd => ?_⟩
          have h1 := hS.2 hd
          have hle := (List.filter_sublist (p := fun p : K × V => q p.1 p.2) (l := kvs)).length_le
          have hpos := List.length_pos_iff.mpr hne
          omega
  | d, .node h l r, ⟨hR, hW, hS⟩ => by
      obtain ⟨hlb, hrb, hlR, hrR⟩ := hR
      obtain ⟨_, hlW, hrW⟩ := hW
      obtain ⟨hd, _, hlS, hrS⟩ := hS
      simp only [retainAll]
      split
      · apply canon_join S hd (canon_retainAll q (d + 1) l ⟨hlR, hlW, hlS⟩)
          (canon_retainAll q (d + 1) r ⟨hrR, hrW, hrS⟩)
        · intro p hp
          rw [toList_retainAll, List.mem_filter] at hp
          exact hlb p hp.1
        · intro p hp
          rw [toList_retainAll, List.mem_filter] at hp
          exact hrb p hp.1
      · exact ⟨⟨hlb, hrb, hlR, hrR⟩, ⟨by assumption, hlW, hrW⟩, ⟨hd, by assumption, hlS, hrS⟩⟩

/-- What `retainAt` lists: the listing filtered by `q`, when every entry `q` drops lies under the
path. -/
theorem toList_retainAt (q : K → V → Bool) :
    ∀ (path : List Bool) (d : Nat) (t : T K V D), Routed S d t →
      (∀ p ∈ t.toList, q p.1 p.2 = false → Under S d path p.1) →
      (retainAt S q path t).toList = t.toList.filter fun p => q p.1 p.2
  | [], _, t, _, _ => toList_retainAll S q t
  | _ :: _, _, .empty, _, _ => rfl
  | _ :: _, _, .leaf h kvs, _, _ => toList_retainAll S q (.leaf h kvs)
  | b :: path, d, .node h l r, ⟨hlb, hrb, hlR, hrR⟩, hq => by
      simp only [retainAt]
      cases b
      · simp only [Bool.false_eq_true, if_false, toList_join, T.toList, List.filter_append]
        rw [toList_retainAt q path (d + 1) l hlR fun p hp hf =>
          (hq p (by simp [T.toList, hp]) hf).2]
        congr 1
        refine (List.filter_eq_self.mpr fun p hp => ?_).symm
        cases hqp : q p.1 p.2
        · have := (hq p (by simp [T.toList, hp]) hqp).1; rw [hrb p hp] at this; simp at this
        · rfl
      · simp only [if_true, toList_join, T.toList, List.filter_append]
        rw [toList_retainAt q path (d + 1) r hrR fun p hp hf =>
          (hq p (by simp [T.toList, hp]) hf).2]
        congr 1
        refine (List.filter_eq_self.mpr fun p hp => ?_).symm
        cases hqp : q p.1 p.2
        · have := (hq p (by simp [T.toList, hp]) hqp).1; rw [hlb p hp] at this; simp at this
        · rfl

/-- **`retainAt` keeps a trie canonical.** -/
theorem canon_retainAt (q : K → V → Bool) :
    ∀ (path : List Bool) (d : Nat) (t : T K V D), Canon S d t →
      (∀ p ∈ t.toList, q p.1 p.2 = false → Under S d path p.1) → Canon S d (retainAt S q path t)
  | [], d, t, h, _ => canon_retainAll S q d t h
  | _ :: _, d, .empty, _, _ => canon_empty S d
  | _ :: _, d, .leaf h kvs, hc, _ => canon_retainAll S q d (.leaf h kvs) hc
  | b :: path, d, .node h l r, ⟨hR, hW, hS⟩, hq => by
      obtain ⟨hlb, hrb, hlR, hrR⟩ := hR
      obtain ⟨_, hlW, hrW⟩ := hW
      obtain ⟨hd, _, hlS, hrS⟩ := hS
      have hql : ∀ p ∈ l.toList, q p.1 p.2 = false → Under S (d + 1) path p.1 :=
        fun p hp hf => (hq p (by simp [T.toList, hp]) hf).2
      have hqr : ∀ p ∈ r.toList, q p.1 p.2 = false → Under S (d + 1) path p.1 :=
        fun p hp hf => (hq p (by simp [T.toList, hp]) hf).2
      simp only [retainAt]
      cases b
      · simp only [Bool.false_eq_true, if_false]
        refine canon_join S hd (canon_retainAt q path (d + 1) l ⟨hlR, hlW, hlS⟩ hql) ⟨hrR, hrW, hrS⟩
          (fun p hp => ?_) hrb
        rw [toList_retainAt S q path (d + 1) l hlR hql, List.mem_filter] at hp
        exact hlb p hp.1
      · simp only [if_true]
        refine canon_join S hd ⟨hlR, hlW, hlS⟩ (canon_retainAt q path (d + 1) r ⟨hrR, hrW, hrS⟩ hqr)
          hlb (fun p hp => ?_)
        rw [toList_retainAt S q path (d + 1) r hrR hqr, List.mem_filter] at hp
        exact hrb p hp.1

/-- **`retainAt` is `build` of the filtered listing**: the canonical erase. -/
theorem retainAt_eq_build (q : K → V → Bool) (path : List Bool) {t : T K V D} (h : Canon S 0 t)
    (hq : ∀ p ∈ t.toList, q p.1 p.2 = false → Under S 0 path p.1) :
    retainAt S q path t = build S S.depth 0 (t.toList.filter fun p => q p.1 p.2) := by
  rw [← toList_retainAt S q path 0 t h.1 hq]
  exact (build_toList S 0 _ (canon_retainAt S q path 0 t h hq)).symm

variable [DecidableEq K]

/-- **What `retainAt` reads**: a key reads its old value if `q` keeps it, and nothing otherwise. -/
theorem get_retainAt (q : K → V → Bool) (path : List Bool) {t : T K V D} (h : Canon S 0 t)
    (hq : ∀ p ∈ t.toList, q p.1 p.2 = false → Under S 0 path p.1) (k : K) :
    (retainAt S q path t).get S k = (t.get S k).filter (q k) := by
  have hc := canon_retainAt S q path 0 t h hq
  apply Option.ext
  intro v
  simp only [T.get]
  rw [← mem_toList S 0 _ hc.1, toList_retainAt S q path 0 t h.1 hq, List.mem_filter,
    mem_toList S 0 t h.1]
  cases hg : getAt S k 0 t with
  | none => simp
  | some a =>
      simp only [Option.filter, Option.some.injEq]
      constructor
      · rintro ⟨rfl, h2⟩; simp [h2]
      · intro h2; split at h2 <;> simp_all

end Nanodregg.Kernel.Trie
