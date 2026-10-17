import Codec.Proofs.World
import Kernel.Proofs.TrieMap

/-!
# The trie's listing order, from its own bits (CODEC-28 step 2, generic half)

`kernel/trie-order` accepts a listing `l` when the trie `build` makes from it lists `l` back and no
leaf holds a key twice. `build_listing_iff` says what that is without mentioning the trie built: from
depth `d`, `l` is pairwise `BitLt S d` on its keys, i.e. at the first bit in `[d, depth)` where two
listed keys differ, the earlier key's bit is clear. The premise is `Trie.SepAt S d l` (distinct keys
differ somewhere below `depth`), which `Trie.Separates S` gives at depth 0.
`cells_get_ordered` / `cells_get_refused` / `cells_get_ok`: the World codec's trie part, read through
`fitList`, is accepted exactly on such listings and refused `kernel/trie-order` by name on every
other. `Codec.Proofs.SlotOrder` turns `BitLt (trieSpec E) 0` into the order of the bytes.
-/

namespace Nanodregg.Codec.Kernel

open Nanodregg.Kernel Nanodregg.Codec.Stream

section Bits
variable {K V D' : Type} (S : Trie.Spec K V D')

/-- `k` routes before `k'` from depth `d`: at the first bit in `[d, depth)` where they differ, the
bit of `k` is clear and the bit of `k'` is set. -/
def BitLt (d : Nat) (k k' : K) : Prop :=
  ∃ i, d ≤ i ∧ i < S.depth ∧ (∀ j, d ≤ j → j < i → S.bit k j = S.bit k' j) ∧
    S.bit k i = false ∧ S.bit k' i = true

theorem bitLt_irrefl {d : Nat} {k : K} : ¬ BitLt S d k k := fun ⟨_, _, _, _, h1, h2⟩ => by
  rw [h1] at h2; cases h2

theorem bitLt_asymm {d : Nat} {k k' : K} (h : BitLt S d k k') : ¬ BitLt S d k' k := by
  rintro ⟨i', hd', _, hpre', h1', h2'⟩
  obtain ⟨i, hd, _, hpre, h1, h2⟩ := h
  rcases Nat.lt_trichotomy i i' with hlt | rfl | hgt
  · have := hpre' i hd hlt; rw [h1, h2] at this; cases this
  · rw [h1] at h2'; cases h2'
  · have := hpre i' hd' hgt; rw [h1', h2'] at this; cases this

/-- Two keys parted at `d` the other way round are not in `BitLt` order from `d`. -/
theorem not_bitLt_of_bit {d : Nat} {k k' : K} (hk : S.bit k d = true) (hk' : S.bit k' d = false) :
    ¬ BitLt S d k k' := by
  rintro ⟨i, hd, _, hpre, h1, _⟩
  rcases Nat.lt_or_eq_of_le hd with hlt | rfl
  · have := hpre d (Nat.le_refl d) hlt; rw [hk, hk'] at this; cases this
  · rw [hk] at h1; cases h1

theorem bitLt_at {d : Nat} {k k' : K} (hd : d < S.depth) (hk : S.bit k d = false)
    (hk' : S.bit k' d = true) : BitLt S d k k' :=
  ⟨d, Nat.le_refl d, hd, fun _ hj hji => absurd hji (by omega), hk, hk'⟩

theorem not_bitLt_deep {d : Nat} {k k' : K} (hd : S.depth ≤ d) : ¬ BitLt S d k k' :=
  fun ⟨_, h1, h2, _⟩ => by omega

theorem bitLt_of_succ {d : Nat} {k k' : K} (h : BitLt S (d + 1) k k') (he : S.bit k d = S.bit k' d) :
    BitLt S d k k' := by
  obtain ⟨i, hd, hi, hpre, h1, h2⟩ := h
  refine ⟨i, by omega, hi, fun j hj hji => ?_, h1, h2⟩
  rcases Nat.lt_or_eq_of_le hj with hlt | rfl
  · exact hpre j hlt hji
  · exact he

theorem bitLt_succ {d : Nat} {k k' : K} (h : BitLt S d k k') (he : S.bit k d = S.bit k' d) :
    BitLt S (d + 1) k k' := by
  obtain ⟨i, hd, hi, hpre, h1, h2⟩ := h
  refine ⟨i, ?_, hi, fun j hj hji => hpre j (by omega) hji, h1, h2⟩
  rcases Nat.lt_or_eq_of_le hd with hlt | rfl
  · exact hlt
  · rw [h1, h2] at he; cases he

/-- A listing in `BitLt` order from `d` is its keys with bit `d` clear, then those with it set. -/
theorem eq_filter_append {d : Nat} : ∀ (l : List (K × V)), l.Pairwise (fun p q => BitLt S d p.1 q.1) →
    l = l.filter (fun p => !S.bit p.1 d) ++ l.filter (fun p => S.bit p.1 d)
  | [], _ => rfl
  | x :: xs, h => by
    rw [List.pairwise_cons] at h
    have ih := eq_filter_append xs h.2
    cases hx : S.bit x.1 d
    · simp only [List.filter_cons, hx, Bool.not_false, if_true, Bool.false_eq_true, if_false, List.cons_append]
      exact congrArg (x :: ·) ih
    · have hall : ∀ q ∈ xs, S.bit q.1 d = true := fun q hq => by
        cases hq' : S.bit q.1 d
        · exact absurd (h.1 q hq) (not_bitLt_of_bit S hx hq')
        · rfl
      have e1 : xs.filter (fun p => !S.bit p.1 d) = [] :=
        List.filter_eq_nil_iff.mpr fun q hq => by simp [hall q hq]
      have e2 : xs.filter (fun p => S.bit p.1 d) = xs := List.filter_eq_self.mpr fun q hq => hall q hq
      simp [hx, e1, e2]

/-- Keys with bit `d` clear, then keys with it set: the two filters give the two sides back. -/
theorem filter_sides {d : Nat} {A B : List (K × V)} (hA : ∀ p ∈ A, S.bit p.1 d = false)
    (hB : ∀ p ∈ B, S.bit p.1 d = true) :
    (A ++ B).filter (fun p => !S.bit p.1 d) = A ∧ (A ++ B).filter (fun p => S.bit p.1 d) = B := by
  rw [List.filter_append, List.filter_append, List.filter_eq_self.mpr (fun p hp => by simp [hA p hp]),
    List.filter_eq_nil_iff.mpr (fun p hp => by simp [hB p hp]),
    List.filter_eq_nil_iff.mpr (fun p hp => by simp [hA p hp]), List.filter_eq_self.mpr (fun p hp => hB p hp)]
  simp

/-- Within one side of bit `d`, `BitLt` from `d` and from `d + 1` agree. -/
theorem pairwise_succ_iff {d : Nat} {b : Bool} {l : List (K × V)} (hb : ∀ p ∈ l, S.bit p.1 d = b) :
    l.Pairwise (fun p q => BitLt S (d + 1) p.1 q.1) ↔ l.Pairwise (fun p q => BitLt S d p.1 q.1) :=
  ⟨List.Pairwise.imp_of_mem fun ha hb' h => bitLt_of_succ S h ((hb _ ha).trans (hb _ hb').symm),
   List.Pairwise.imp_of_mem fun ha hb' h => bitLt_succ S h ((hb _ ha).trans (hb _ hb').symm)⟩

end Bits

section Build
variable {K V D' : Type} (S : Trie.Spec K V D') [DecidableEq K]

/-- **The listing `build` reads back is the one in bit order.** From depth `d`, with the fuel that
reaches `depth`, the trie `build` makes from `l` lists `l` back with every leaf's keys distinct
exactly when `l` is pairwise `BitLt S d` on its keys. -/
theorem build_listing_iff : ∀ (f d : Nat) (l : List (K × V)), f = S.depth - d → Trie.SepAt S d l →
    ((Trie.build S f d l).toList = l ∧ leavesNodup (Trie.build S f d l) = true ↔
      l.Pairwise (fun p q => BitLt S d p.1 q.1))
  | _, _, [], _, _ => by simp [Trie.build, Trie.T.toList, leavesNodup]
  | f, _, [x], _, _ => by cases f <;> simp [Trie.build, Trie.mkLeaf, Trie.T.toList, leavesNodup]
  | 0, d, a :: b :: rest, hf, hs => by
      have hd : S.depth ≤ d := by omega
      simp only [Trie.build, Trie.mkLeaf, Trie.T.toList, leavesNodup, true_and, decide_eq_true_eq]
      constructor
      · intro hn
        have hab : a.1 ≠ b.1 := by
          intro he; simp only [List.map_cons, List.nodup_cons, List.mem_cons] at hn; exact hn.1 (Or.inl he)
        obtain ⟨i, h1, h2, _⟩ := hs a (by simp) b (by simp) hab
        omega
      · intro hp
        exact absurd ((List.pairwise_cons.mp hp).1 b (by simp)) (not_bitLt_deep S hd)
  | f + 1, d, a :: b :: rest, hf, hs => by
      have hdd : d < S.depth := by omega
      generalize hl : a :: b :: rest = l at hs ⊢
      have h2 : 2 ≤ l.length := by rw [← hl]; simp
      rw [Trie.build_split S f d l h2]
      simp only [Trie.mkNode, Trie.T.toList, leavesNodup, Bool.and_eq_true]
      have hsL : Trie.SepAt S (d + 1) (l.filter fun p => !S.bit p.1 d) := by
        rw [Trie.filter_not_eq]; exact Trie.sepAt_filter S hs false
      have hsR : Trie.SepAt S (d + 1) (l.filter fun p => S.bit p.1 d) := by
        rw [Trie.filter_eq_true]; exact Trie.sepAt_filter S hs true
      have ihL := build_listing_iff f (d + 1) _ (by omega) hsL
      have ihR := build_listing_iff f (d + 1) _ (by omega) hsR
      have bL : ∀ p ∈ l.filter (fun p => !S.bit p.1 d), S.bit p.1 d = false := fun p hp => by
        simpa using (List.mem_filter.mp hp).2
      have bR : ∀ p ∈ l.filter (fun p => S.bit p.1 d), S.bit p.1 d = true := fun p hp =>
        (List.mem_filter.mp hp).2
      constructor
      · rintro ⟨he, hnL, hnR⟩
        have pL := Trie.toList_build S f (d + 1) (l.filter fun p => !S.bit p.1 d)
        have pR := Trie.toList_build S f (d + 1) (l.filter fun p => S.bit p.1 d)
        have mL : ∀ p ∈ (Trie.build S f (d + 1) (l.filter fun p => !S.bit p.1 d)).toList,
            S.bit p.1 d = false := fun p hp => bL p (pL.mem_iff.mp hp)
        have mR : ∀ p ∈ (Trie.build S f (d + 1) (l.filter fun p => S.bit p.1 d)).toList,
            S.bit p.1 d = true := fun p hp => bR p (pR.mem_iff.mp hp)
        have kL := (filter_sides S mL mR).1
        have kR := (filter_sides S mL mR).2
        rw [he] at kL kR
        have eL := kL.symm
        have eR := kR.symm
        have hL := (pairwise_succ_iff S bL).mp (ihL.mp ⟨eL, hnL⟩)
        have hR := (pairwise_succ_iff S bR).mp (ihR.mp ⟨eR, hnR⟩)
        rw [← he, eL, eR, List.pairwise_append]
        exact ⟨hL, hR, fun p hp q hq => bitLt_at S hdd (bL p hp) (bR q hq)⟩
      · intro hp
        have hsplit := eq_filter_append S l hp
        have hL := (ihL.mpr ((pairwise_succ_iff S bL).mpr (hp.sublist List.filter_sublist)))
        have hR := (ihR.mpr ((pairwise_succ_iff S bR).mpr (hp.sublist List.filter_sublist)))
        rw [hL.1, hR.1]
        exact ⟨hsplit.symm, hL.2, hR.2⟩

end Build

section Cells
variable {D : Type} [DecidableEq D]

/-- The listing check `kernel/trie-order` runs, read as the bit order from the root. -/
theorem trieOrder_check_iff (E : Env D) (hsep : Trie.Separates (trieSpec E)) (l : List (Slot D × Leaf)) :
    ((Trie.build (trieSpec E) (trieSpec E).depth 0 l).toList == l &&
        leavesNodup (Trie.build (trieSpec E) (trieSpec E).depth 0 l)) = true ↔
      l.Pairwise (fun p q => BitLt (trieSpec E) 0 p.1 q.1) := by
  rw [Bool.and_eq_true, beq_iff_eq]
  exact build_listing_iff (trieSpec E) _ 0 l rfl
    (fun p _ q _ hne => (hsep p.1 q.1 hne).elim fun i h => ⟨i, Nat.zero_le i, h⟩)

/-- A listing in bit order is accepted: the trie part reads as the trie `build` makes of it. -/
theorem cells_get_ok (E : Env D) (hsep : Trie.Separates (trieSpec E)) {dc : Stream D} {b : ByteArray}
    {i j : Nat} {l : List (Slot D × Leaf)} (h : (fitList dc).get b i = .ok (l, j))
    (ho : l.Pairwise (fun p q => BitLt (trieSpec E) 0 p.1 q.1)) :
    (cells E dc).get b i = .ok (Trie.build (trieSpec E) (trieSpec E).depth 0 l, j) := by
  have hc := (trieOrder_check_iff E hsep l).mpr ho
  simp only [cells, refine, h]
  rw [if_pos hc]

/-- **Every other listing is refused `kernel/trie-order`, by name.** -/
theorem cells_get_refused (E : Env D) (hsep : Trie.Separates (trieSpec E)) {dc : Stream D}
    {b : ByteArray} {i j : Nat} {l : List (Slot D × Leaf)} (h : (fitList dc).get b i = .ok (l, j))
    (ho : ¬ l.Pairwise (fun p q => BitLt (trieSpec E) 0 p.1 q.1)) :
    (cells E dc).get b i = .error (.rejected i "kernel/trie-order") := by
  have hc : ¬ (((Trie.build (trieSpec E) (trieSpec E).depth 0 l).toList == l &&
      leavesNodup (Trie.build (trieSpec E) (trieSpec E).depth 0 l)) = true) :=
    fun hc => ho ((trieOrder_check_iff E hsep l).mp hc)
  simp only [cells, refine, h]
  rw [if_neg hc]

/-- What the trie part accepts was a listing in bit order, and is the trie `build` makes of it. -/
theorem cells_get_ordered (E : Env D) (hsep : Trie.Separates (trieSpec E)) {dc : Stream D}
    {b : ByteArray} {i j : Nat} {t : Cells D} (h : (cells E dc).get b i = .ok (t, j)) :
    ∃ l, (fitList dc).get b i = .ok (l, j) ∧ l.Pairwise (fun p q => BitLt (trieSpec E) 0 p.1 q.1) ∧
      t = Trie.build (trieSpec E) (trieSpec E).depth 0 l := by
  cases hg : (fitList dc).get b i with
  | error e => simp [cells, refine, hg] at h
  | ok r =>
    obtain ⟨l, j'⟩ := r
    by_cases ho : l.Pairwise (fun p q => BitLt (trieSpec E) 0 p.1 q.1)
    · rw [cells_get_ok E hsep hg ho] at h
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨l, rfl, ho, rfl⟩
    · rw [cells_get_refused E hsep hg ho] at h; cases h

end Cells

end Nanodregg.Codec.Kernel
