/-
# Kernel.Proofs.TrieMap — the trie as the World's map: sums over its listing, and contents determine it

* `sumN_insert_some` / `sumN_insert_none` (and the `Int` twins `sumI_…`): a sum over a routed trie's
  listing moves under one insert by exactly the replaced entry and the new one. These are what the
  World's weight and value sums are restated over (Kernel.Proofs.Weight, Kernel.Proofs.Value).
* `build_perm`: when the bit function SEPARATES keys within `depth` bits, `build` does not care in
  which order it is handed its entries.
* `eq_of_get_eq`: two canonical tries that hold the same value at every key are the SAME trie, so
  they have the same root (KERNEL-23's history independence, stated over contents instead of over a
  listing: whatever order the turns ran in).
-/
import Kernel.Proofs.Trie

namespace Nanodregg.Kernel.Trie

variable {K V D : Type} (S : Spec K V D) [DecidableEq K]

/-! ## Sums over a listing -/

omit [DecidableEq K] in
theorem perm_sumN {α : Type} {l₁ l₂ : List α} (g : α → Nat) (h : l₁.Perm l₂) :
    (l₁.map g).sum = (l₂.map g).sum := (h.map g).sum_nat

omit [DecidableEq K] in
theorem perm_sumI {α : Type} {l₁ l₂ : List α} (g : α → Int) (h : l₁.Perm l₂) :
    (l₁.map g).sum = (l₂.map g).sum := by
  induction h with
  | nil => rfl
  | cons x _ ih => simp [List.sum_cons, ih]
  | swap x y l => simp [List.sum_cons]; omega
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- A key held once: the listing's sum is its entry's plus the rest's. -/
theorem sumI_split (g : K × V → Int) {k : K} {v : V} :
    ∀ (l : List (K × V)), (l.map Prod.fst).Nodup → (k, v) ∈ l →
      (l.map g).sum = g (k, v) + ((l.filter fun p => p.1 ≠ k).map g).sum
  | [], _, h => by simp at h
  | p :: rest, hn, h => by
      simp only [List.map_cons, List.nodup_cons] at hn
      by_cases hp : p.1 = k
      · have hpv : p = (k, v) := by
          rcases List.mem_cons.mp h with he | hr
          · exact he.symm
          · exact absurd (hp ▸ List.mem_map_of_mem (f := Prod.fst) hr) hn.1
        subst hpv
        have hf : rest.filter (fun p => p.1 ≠ k) = rest :=
          List.filter_eq_self.mpr fun q hq => by
            simp only [ne_eq, decide_eq_true_eq]
            intro he
            have hm := List.mem_map_of_mem (f := Prod.fst) hq
            rw [he] at hm; exact hn.1 hm
        rw [List.filter_cons_of_neg (by simp), hf, List.map_cons, List.sum_cons]
      · have hr : (k, v) ∈ rest := by
          rcases List.mem_cons.mp h with he | hr
          · exact absurd (he ▸ rfl) hp
          · exact hr
        rw [List.map_cons, List.sum_cons, sumI_split g rest hn.2 hr,
          List.filter_cons_of_pos (by simpa using hp), List.map_cons, List.sum_cons]
        omega

theorem sumN_split (g : K × V → Nat) {k : K} {v : V} (l : List (K × V)) (hn : (l.map Prod.fst).Nodup)
    (h : (k, v) ∈ l) : (l.map g).sum = g (k, v) + ((l.filter fun p => p.1 ≠ k).map g).sum := by
  have := sumI_split (fun p => (g p : Int)) l hn h
  have e : ∀ l' : List (K × V), ((l'.map fun p => (g p : Int)).sum) = ((l'.map g).sum : Int) := by
    intro l'; induction l' with
    | nil => rfl
    | cons q rest ih => simp [List.sum_cons, ih]
  simp only [e] at this; exact_mod_cast this

theorem filter_ne_of_get_none {t : T K V D} (h : Routed S 0 t) {k : K} (hk : t.get S k = none) :
    t.toList.filter (fun p => p.1 ≠ k) = t.toList :=
  List.filter_eq_self.mpr fun p hp => by
    simp only [ne_eq, decide_eq_true_eq]
    intro he
    have := (mem_toList S 0 t h p.1 p.2).mp hp
    rw [he] at this
    have h2 : t.get S k = some p.2 := this
    rw [hk] at h2; exact absurd h2 (by simp)

theorem sumI_insert_some (g : K × V → Int) {t : T K V D} (h : Routed S 0 t) {k : K} {old : V}
    (v : V) (hk : t.get S k = some old) :
    ((t.insert S k v).toList.map g).sum = (t.toList.map g).sum - g (k, old) + g (k, v) := by
  rw [perm_sumI g (toList_insert_perm S h k v),
    sumI_split g t.toList (toList_nodup S 0 t h) ((mem_toList S 0 t h k old).mpr hk)]
  simp [List.sum_append]; omega

theorem sumI_insert_none (g : K × V → Int) {t : T K V D} (h : Routed S 0 t) {k : K}
    (v : V) (hk : t.get S k = none) :
    ((t.insert S k v).toList.map g).sum = (t.toList.map g).sum + g (k, v) := by
  rw [perm_sumI g (toList_insert_perm S h k v), filter_ne_of_get_none S h hk]
  simp [List.sum_append]

theorem sumN_insert_some (g : K × V → Nat) {t : T K V D} (h : Routed S 0 t) {k : K} {old : V}
    (v : V) (hk : t.get S k = some old) :
    ((t.insert S k v).toList.map g).sum + g (k, old) = (t.toList.map g).sum + g (k, v) := by
  rw [perm_sumN g (toList_insert_perm S h k v),
    sumN_split g t.toList (toList_nodup S 0 t h) ((mem_toList S 0 t h k old).mpr hk)]
  simp [List.sum_append]; omega

theorem sumN_insert_none (g : K × V → Nat) {t : T K V D} (h : Routed S 0 t) {k : K}
    (v : V) (hk : t.get S k = none) :
    ((t.insert S k v).toList.map g).sum = (t.toList.map g).sum + g (k, v) := by
  rw [perm_sumN g (toList_insert_perm S h k v), filter_ne_of_get_none S h hk]
  simp [List.sum_append]

/-- Every listed entry is what the trie holds at its key. -/
theorem get_of_mem {t : T K V D} (h : Routed S 0 t) {p : K × V} (hp : p ∈ t.toList) :
    t.get S p.1 = some p.2 := (mem_toList S 0 t h p.1 p.2).mp hp

/-! ## Contents determine the trie -/

/-- The bit function tells any two keys apart within `depth` bits. The deployed one does (the
World's slot bits: Kernel.Proofs.Cells). -/
def Separates : Prop := ∀ k k' : K, k ≠ k' → ∃ i, i < S.depth ∧ S.bit k i ≠ S.bit k' i

/-- The keys a subtree at depth `d` receives agree below `d`, so if they are told apart at all it
is at a bit in `[d, depth)`. -/
def SepAt (d : Nat) (l : List (K × V)) : Prop :=
  ∀ p ∈ l, ∀ q ∈ l, p.1 ≠ q.1 → ∃ i, d ≤ i ∧ i < S.depth ∧ S.bit p.1 i ≠ S.bit q.1 i

omit [DecidableEq K] in
theorem sepAt_filter {d : Nat} {l : List (K × V)} (h : SepAt S d l) (b : Bool) :
    SepAt S (d + 1) (l.filter fun p => S.bit p.1 d == b) := by
  intro p hp q hq hne
  simp only [List.mem_filter, beq_iff_eq] at hp hq
  obtain ⟨i, hi, hd, hb⟩ := h p hp.1 q hq.1 hne
  refine ⟨i, ?_, hd, hb⟩
  rcases Nat.lt_or_eq_of_le hi with hlt | rfl
  · exact hlt
  · exact absurd (hp.2.trans hq.2.symm) hb

omit [DecidableEq K] in
theorem filter_not_eq (d : Nat) (l : List (K × V)) :
    l.filter (fun p => !S.bit p.1 d) = l.filter (fun p => S.bit p.1 d == false) := by
  congr 1; funext p; cases S.bit p.1 d <;> rfl

omit [DecidableEq K] in
theorem filter_eq_true (d : Nat) (l : List (K × V)) :
    l.filter (fun p => S.bit p.1 d) = l.filter (fun p => S.bit p.1 d == true) := by
  congr 1; funext p; cases S.bit p.1 d <;> rfl

omit [DecidableEq K] in
/-- **`build` is order-blind on separated keys.** -/
theorem build_perm : ∀ (f d : Nat) (l₁ l₂ : List (K × V)), l₁.Perm l₂ → (l₁.map Prod.fst).Nodup →
    f = S.depth - d → SepAt S d l₁ → build S f d l₁ = build S f d l₂
  | f, d, l₁, l₂, hp, hn, hf, hs => by
      match l₁, l₂, hp.length_eq with
      | [], [], _ => rfl
      | [x], l₂, _ =>
          have : l₂ = [x] := (List.perm_singleton.mp hp.symm)
          subst this; rfl
      | a :: b :: rest, l₂, hl =>
          have hl₂ : 2 ≤ l₂.length := by simp at hl; omega
          cases f with
          | zero =>
              exfalso
              have hab : a.1 ≠ b.1 := by
                simp only [List.map_cons, List.nodup_cons, List.mem_cons] at hn
                exact fun he => hn.1 (Or.inl he)
              obtain ⟨i, hi, hd, _⟩ := hs a (by simp) b (by simp) hab
              omega
          | succ f =>
              rw [build_split S f d _ (by simp), build_split S f d l₂ hl₂]
              have hf' : f = S.depth - (d + 1) := by omega
              have hn₀ := (List.Perm.nodup_iff (hp.map Prod.fst)).mp hn
              have sub : ∀ (q : K × V → Bool), ((((a :: b :: rest).filter q).map Prod.fst).Nodup) :=
                fun q => hn.sublist (List.filter_sublist.map Prod.fst)
              rw [filter_not_eq S d (a :: b :: rest), filter_not_eq S d l₂,
                filter_eq_true S d (a :: b :: rest), filter_eq_true S d l₂]
              rw [build_perm f (d + 1) _ _ (hp.filter _) (sub _) hf' (sepAt_filter S hs false),
                build_perm f (d + 1) _ _ (hp.filter _) (sub _) hf' (sepAt_filter S hs true)]
termination_by f => f

/-- **Contents determine the trie.** Two canonical tries that hold the same value at every key are
equal (so: one root), when the bit function separates keys. -/
theorem eq_of_get_eq (hsep : Separates S) {t t' : T K V D} (h : Canon S 0 t) (h' : Canon S 0 t')
    (he : ∀ k, t.get S k = t'.get S k) : t = t' := by
  have hp : t.toList.Perm t'.toList :=
    perm_of_nodup_mem (nodup_of_map_fst (toList_nodup S 0 t h.1))
      (nodup_of_map_fst (toList_nodup S 0 t' h'.1)) fun p => by
        rw [mem_toList S 0 t h.1 p.1 p.2, mem_toList S 0 t' h'.1 p.1 p.2]
        exact iff_of_eq (congrArg (· = some p.2) (he p.1))
  have hs : SepAt S 0 t.toList := fun p _ q _ hne => by
    obtain ⟨i, hi, hb⟩ := hsep p.1 q.1 hne; exact ⟨i, Nat.zero_le _, hi, hb⟩
  rw [← build_toList S 0 t h, ← build_toList S 0 t' h',
    build_perm S _ 0 _ _ hp (toList_nodup S 0 t h.1) rfl hs]

omit [DecidableEq K] in
/-- A canonical shape is shallow: every proof path is at most `depth` long. -/
theorem shallow_of_shape : ∀ (d : Nat) (t : T K V D), Shape S d t → Shallow S d t
  | _, .empty, _ => trivial
  | _, .leaf _ _, _ => trivial
  | d, .node _ l r, ⟨hd, _, hl, hr⟩ => ⟨hd, shallow_of_shape (d + 1) l hl, shallow_of_shape (d + 1) r hr⟩

end Nanodregg.Kernel.Trie
