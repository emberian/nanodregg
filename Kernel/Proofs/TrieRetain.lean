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

/-- Key `k`'s bits from `d` on are what `path` says (`path[i]`, where it has one, is bit `i`): `k` lies
in the subtree `path` leads to. -/
def Under (d : Nat) (path : List Bool) (k : K) : Prop :=
  ∀ i, d ≤ i → ∀ b, path[i]? = some b → S.bit k i = b

theorem Under.mono {d d' : Nat} {path : List Bool} {k : K} (h : Under S d path k) (hd : d ≤ d') :
    Under S d' path k := fun i hi => h i (Nat.le_trans hd hi)

theorem toList_join (b : Nat) (l r : T K V D) : (join S b l r).toList = l.toList ++ r.toList := by
  cases l with
  | empty => simp [join, T.toList]
  | leaf h kvs =>
      cases r with
      | empty => simp [join, T.toList]
      | leaf h' kvs' => cases kvs <;> simp [join, T.toList, T.first, mkNode]
      | node h' b' rep' l' r' => cases kvs <;> simp [join, T.toList, T.first, mkNode]
  | node h b' rep l' r' => cases r <;> simp [join, T.toList, T.first, mkNode]

theorem join_empty_left (b : Nat) (r : T K V D) : join S b .empty r = r := by
  cases r <;> rfl

theorem join_empty_right (b : Nat) (l : T K V D) : join S b l .empty = l := by
  cases l <;> rfl

/-- Two non-empty sides make a node whose `rep` is the left side's first key. -/
theorem join_eq {b : Nat} {l r : T K V D} {x : K} (hl : l ≠ .empty) (hr : r ≠ .empty) (hx : l.first = some x) :
    join S b l r = mkNode S b x l r := by
  cases l with
  | empty => exact absurd rfl hl
  | leaf h kvs =>
      cases r with
      | empty => exact absurd rfl hr
      | leaf h' kvs' => simp only [join, hx]
      | node h' b' rep' l' r' => simp only [join, hx]
  | node h b' rep l' r' =>
      cases r with
      | empty => exact absurd rfl hr
      | leaf h' kvs' => simp only [join, hx]
      | node h' b'' rep' l'' r'' => simp only [join, hx]

/-- A canonical subtree at `d'` whose keys also agree on `[d, d')` is canonical at `d`. -/
theorem canon_lower {d d' : Nat} (hdd : d ≤ d') : ∀ (t : T K V D), Canon S d' t →
    (∀ p ∈ t.toList, ∀ p' ∈ t.toList, ∀ i, d ≤ i → i < d' → S.bit p.1 i = S.bit p'.1 i) → Canon S d t
  | .empty, _, _ => canon_empty S d
  | .leaf h kvs, ⟨hR, hW, hS⟩, hag =>
      ⟨hR, hW, hS.1, fun h2 p hp q hq i hi hid =>
        if hlt : i < d' then hag p hp q hq i hi hlt else hS.2 h2 p hp q hq i (by omega) hid⟩
  | .node h b rep l r, ⟨hR, hW, hS⟩, hag => by
      obtain ⟨hdb, hagr, hlb, hrb, hlR, hrR⟩ := hR
      obtain ⟨_, hb, hrep, hrne, hlS, hrS⟩ := hS
      obtain ⟨p0, hp0, hp0r⟩ := head_key hrep
      refine ⟨⟨by omega, fun p hp i hi hib => ?_, hlb, hrb, hlR, hrR⟩, hW, ⟨by omega, hb, hrep, hrne, hlS, hrS⟩⟩
      by_cases hlt : i < d'
      · rw [← hp0r]; exact hag p hp p0 (List.mem_append_left _ hp0) i hi hlt
      · exact hagr p hp i (by omega) hib

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
  | .node h b rep l r, hc => by
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
  | .node h b rep l r => by
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

/-- Two canonical children at `b + 1`, routed by bit `b`, whose keys agree on `[d, b)`, join into a
canonical trie at `d` (one side empty: the other, whole). -/
theorem canon_join {d b : Nat} {l r : T K V D} (hdb : d ≤ b) (hd : b < S.depth) (hl : Canon S (b + 1) l)
    (hr : Canon S (b + 1) r) (hlb : ∀ p ∈ l.toList, S.bit p.1 b = false)
    (hrb : ∀ p ∈ r.toList, S.bit p.1 b = true)
    (hag : ∀ p ∈ l.toList ++ r.toList, ∀ p' ∈ l.toList ++ r.toList, ∀ i, d ≤ i → i < b →
      S.bit p.1 i = S.bit p'.1 i) : Canon S d (join S b l r) := by
  have hag' : ∀ (t : T K V D), (∀ p ∈ t.toList, p ∈ l.toList ++ r.toList) →
      (∀ p ∈ t.toList, ∀ p' ∈ t.toList, S.bit p.1 b = S.bit p'.1 b) →
      ∀ p ∈ t.toList, ∀ p' ∈ t.toList, ∀ i, d ≤ i → i < b + 1 → S.bit p.1 i = S.bit p'.1 i :=
    fun t hsub hb p hp p' hp' i hi hib =>
      if hlt : i < b then hag p (hsub p hp) p' (hsub p' hp') i hi hlt
      else by rw [show i = b by omega]; exact hb p hp p' hp'
  by_cases hle : l = .empty
  · subst hle
    rw [join_empty_left]
    exact canon_lower S (by omega) r hr (hag' r (fun p hp => List.mem_append_right _ hp)
      fun p hp p' hp' => by rw [hrb p hp, hrb p' hp'])
  by_cases hre : r = .empty
  · subst hre
    rw [join_empty_right]
    exact canon_lower S (by omega) l hl (hag' l (fun p hp => List.mem_append_left _ hp)
      fun p hp p' hp' => by rw [hlb p hp, hlb p' hp'])
  obtain ⟨hlR, hlW, hlS⟩ := hl
  obtain ⟨hrR, hrW, hrS⟩ := hr
  have hlne := toList_ne_nil S _ l hlS hle
  have hrne := toList_ne_nil S _ r hrS hre
  obtain ⟨x0, hx0, hx0e⟩ : ∃ x0 ∈ l.toList, l.first = some x0.1 := by
    rw [rep_first S _ l hlS]
    cases h' : l.toList with
    | nil => exact absurd h' hlne
    | cons x0 _ => exact ⟨x0, by simp, rfl⟩
  rw [join_eq S hle hre hx0e]
  refine ⟨⟨hdb, fun p hp i hi hib => hag p hp x0 (List.mem_append_left _ hx0) i hi hib, hlb, hrb, hlR, hrR⟩,
    ⟨hd, rfl, hlW, hrW⟩, ⟨hdb, hd, ?_, hrne, hlS, hrS⟩⟩
  rw [← rep_first S _ l hlS, hx0e]

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
          refine ⟨(hR.sublist (List.Sublist.map _ List.filter_sublist)), rfl, hne, fun h2 p hp p' hp' i hi hid => ?_⟩
          have hle := (List.filter_sublist (p := fun p : K × V => q p.1 p.2) (l := kvs)).length_le
          exact hS.2 (by omega) p (List.mem_filter.mp hp).1 p' (List.mem_filter.mp hp').1 i hi hid
  | d, .node h b rep l r, hc => by
      have hc0 := hc
      obtain ⟨⟨hdb, hag, hlb, hrb, hlR, hrR⟩, ⟨hb, _, hlW, hrW⟩, ⟨_, _, _, _, hlS, hrS⟩⟩ := hc
      simp only [retainAll]
      split
      · apply canon_join S hdb hb (canon_retainAll q (b + 1) l ⟨hlR, hlW, hlS⟩)
          (canon_retainAll q (b + 1) r ⟨hrR, hrW, hrS⟩)
        · intro p hp
          rw [toList_retainAll, List.mem_filter] at hp
          exact hlb p hp.1
        · intro p hp
          rw [toList_retainAll, List.mem_filter] at hp
          exact hrb p hp.1
        · intro p hp p' hp' i hi hib
          have sub : ∀ x ∈ (retainAll S q l).1.toList ++ (retainAll S q r).1.toList, x ∈ l.toList ++ r.toList := by
            intro x hx
            rw [toList_retainAll, toList_retainAll] at hx
            rcases List.mem_append.mp hx with hx | hx
            · exact List.mem_append_left _ (List.mem_filter.mp hx).1
            · exact List.mem_append_right _ (List.mem_filter.mp hx).1
          rw [hag p (sub p hp) i hi hib, hag p' (sub p' hp') i hi hib]
      · exact hc0

/-- What `retainAt` lists: the listing filtered by `q`, when every entry `q` drops lies under the
path. -/
theorem toList_retainAt (q : K → V → Bool) :
    ∀ (path : List Bool) (d : Nat) (t : T K V D), Routed S d t →
      (∀ p ∈ t.toList, q p.1 p.2 = false → Under S d path p.1) →
      (retainAt S q path t).toList = t.toList.filter fun p => q p.1 p.2 := by
  intro path d t
  induction t generalizing d with
  | empty => intro _ _; rfl
  | leaf h kvs => intro _ _; exact toList_retainAll S q (.leaf h kvs)
  | node h b rep l r ihl ihr =>
      intro hr hq
      obtain ⟨hdb, _, hlb, hrb, hlR, hrR⟩ := hr
      have hql : ∀ p ∈ l.toList, q p.1 p.2 = false → Under S (b + 1) path p.1 :=
        fun p hp hf => (hq p (List.mem_append_left _ hp) hf).mono S (by omega)
      have hqr : ∀ p ∈ r.toList, q p.1 p.2 = false → Under S (b + 1) path p.1 :=
        fun p hp hf => (hq p (List.mem_append_right _ hp) hf).mono S (by omega)
      simp only [retainAt]
      cases hpb : path[b]? with
      | none => exact toList_retainAll S q (.node h b rep l r)
      | some bb =>
          cases bb
          · simp only [toList_join, T.toList, List.filter_append]
            rw [ihl (b + 1) hlR hql]
            congr 1
            refine (List.filter_eq_self.mpr fun p hp => ?_).symm
            cases hqp : q p.1 p.2
            · have := hq p (List.mem_append_right _ hp) hqp b hdb false hpb
              rw [hrb p hp] at this; cases this
            · rfl
          · simp only [toList_join, T.toList, List.filter_append]
            rw [ihr (b + 1) hrR hqr]
            congr 1
            refine (List.filter_eq_self.mpr fun p hp => ?_).symm
            cases hqp : q p.1 p.2
            · have := hq p (List.mem_append_left _ hp) hqp b hdb true hpb
              rw [hlb p hp] at this; cases this
            · rfl

/-- **`retainAt` keeps a trie canonical.** -/
theorem canon_retainAt (q : K → V → Bool) :
    ∀ (path : List Bool) (d : Nat) (t : T K V D), Canon S d t →
      (∀ p ∈ t.toList, q p.1 p.2 = false → Under S d path p.1) → Canon S d (retainAt S q path t) := by
  intro path d t
  induction t generalizing d with
  | empty => intro _ _; exact canon_empty S d
  | leaf h kvs => intro hc _; exact canon_retainAll S q d (.leaf h kvs) hc
  | node h b rep l r ihl ihr =>
      intro hc hq
      have hc0 := hc
      obtain ⟨⟨hdb, hag, hlb, hrb, hlR, hrR⟩, ⟨hb, _, hlW, hrW⟩, ⟨_, _, _, _, hlS, hrS⟩⟩ := hc
      have hql : ∀ p ∈ l.toList, q p.1 p.2 = false → Under S (b + 1) path p.1 :=
        fun p hp hf => (hq p (List.mem_append_left _ hp) hf).mono S (by omega)
      have hqr : ∀ p ∈ r.toList, q p.1 p.2 = false → Under S (b + 1) path p.1 :=
        fun p hp hf => (hq p (List.mem_append_right _ hp) hf).mono S (by omega)
      have agree : ∀ (A B : List (K × V)), (∀ x ∈ A, x ∈ l.toList) → (∀ x ∈ B, x ∈ r.toList) →
          ∀ p ∈ A ++ B, ∀ p' ∈ A ++ B, ∀ i, d ≤ i → i < b → S.bit p.1 i = S.bit p'.1 i := by
        intro A B hA hB p hp p' hp' i hi hib
        have sub : ∀ x ∈ A ++ B, x ∈ l.toList ++ r.toList := fun x hx => by
          rcases List.mem_append.mp hx with hx | hx
          · exact List.mem_append_left _ (hA x hx)
          · exact List.mem_append_right _ (hB x hx)
        rw [hag p (sub p hp) i hi hib, hag p' (sub p' hp') i hi hib]
      simp only [retainAt]
      cases hpb : path[b]? with
      | none => exact canon_retainAll S q d (.node h b rep l r) hc0
      | some bb =>
          cases bb
          · refine canon_join S hdb hb (ihl (b + 1) ⟨hlR, hlW, hlS⟩ hql) ⟨hrR, hrW, hrS⟩
              (fun p hp => ?_) hrb (agree _ _ (fun x hx => ?_) fun x hx => hx)
            · rw [toList_retainAt S q path (b + 1) l hlR hql, List.mem_filter] at hp
              exact hlb p hp.1
            · rw [toList_retainAt S q path (b + 1) l hlR hql, List.mem_filter] at hx
              exact hx.1
          · refine canon_join S hdb hb ⟨hlR, hlW, hlS⟩ (ihr (b + 1) ⟨hrR, hrW, hrS⟩ hqr)
              hlb (fun p hp => ?_) (agree _ _ (fun x hx => hx) fun x hx => ?_)
            · rw [toList_retainAt S q path (b + 1) r hrR hqr, List.mem_filter] at hp
              exact hrb p hp.1
            · rw [toList_retainAt S q path (b + 1) r hrR hqr, List.mem_filter] at hx
              exact hx.1

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
