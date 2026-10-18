import Codec.Proofs.World
import Kernel.Proofs.TrieMap
import Kernel.Proofs.TrieOrder

/-!
# The trie's listing order, from its own bits (CODEC-28 step 2, generic half)

`kernel/trie-order` accepts a listing `l` when the trie `build` makes from it lists `l` back and no
leaf holds a key twice. `build_listing_iff` says what that is without mentioning the trie built: from
depth `d`, `l` is pairwise `BitLt S d` on its keys, i.e. at the first bit in `[d, depth)` where two
listed keys differ, the earlier key's bit is clear. The premise is `Trie.SepAt S d l` (distinct keys
differ somewhere below `depth`), which `Trie.Separates S` gives at depth 0.
`trieListing_get_ok` / `_refused` / `_ordered`: a trie-listing codec (the cells' `kernel/trie-order`,
the journal's `kernel/journal-order`) accepts exactly such listings and refuses every other by its
name; `cells_get_*` are the cells' instances. `Codec.Proofs.SlotOrder` turns `BitLt (trieSpec E) 0` into the order of the bytes.
-/

namespace Nanodregg.Codec.Kernel

open Nanodregg.Kernel Nanodregg.Codec.Stream

section Bits
variable {K V D' : Type} (S : Trie.Spec K V D')

-- `BitLt` and its first lemmas (`bitLt_irrefl` … `bitLt_succ`) are `Kernel.Proofs.TrieOrder`'s.

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

section Listing
variable {K V D' : Type} [DecidableEq K] [DecidableEq V]

/-- The listing check a trie-listing codec runs, read as the bit order from the root. -/
theorem listing_check_iff (S : Trie.Spec K V D') (hsep : Trie.Separates S) (l : List (K × V)) :
    ((Trie.build S S.depth 0 l).toList == l && leavesNodup (Trie.build S S.depth 0 l)) = true ↔
      l.Pairwise (fun p q => BitLt S 0 p.1 q.1) := by
  rw [Bool.and_eq_true, beq_iff_eq]
  exact build_listing_iff S _ 0 l rfl
    (fun p _ q _ hne => (hsep p.1 q.1 hne).elim fun i h => ⟨i, Nat.zero_le i, h⟩)

/-- A listing in bit order is accepted: the codec reads the trie `build` makes of it. -/
theorem trieListing_get_ok (S : Trie.Spec K V D') (hsep : Trie.Separates S) {name : String}
    {c : Stream (List (K × V))} {b : ByteArray} {i j : Nat} {l : List (K × V)}
    (h : c.get b i = .ok (l, j)) (ho : l.Pairwise (fun p q => BitLt S 0 p.1 q.1)) :
    (refine name c (listingAccept S) Trie.T.toList).get b i = .ok (Trie.build S S.depth 0 l, j) := by
  have hc := (listing_check_iff S hsep l).mpr ho
  simp only [listingAccept, refine, h]
  rw [if_pos hc]

/-- **Every other listing is refused by the codec's name.** -/
theorem trieListing_get_refused (S : Trie.Spec K V D') (hsep : Trie.Separates S) {name : String}
    {c : Stream (List (K × V))} {b : ByteArray} {i j : Nat} {l : List (K × V)}
    (h : c.get b i = .ok (l, j)) (ho : ¬ l.Pairwise (fun p q => BitLt S 0 p.1 q.1)) :
    (refine name c (listingAccept S) Trie.T.toList).get b i = .error (.rejected i name) := by
  have hc : ¬ (((Trie.build S S.depth 0 l).toList == l && leavesNodup (Trie.build S S.depth 0 l)) = true) :=
    fun hc => ho ((listing_check_iff S hsep l).mp hc)
  simp only [listingAccept, refine, h]
  rw [if_neg hc]

/-- What a trie-listing codec accepts was a listing in bit order, and is the trie `build` makes of it. -/
theorem trieListing_get_ordered (S : Trie.Spec K V D') (hsep : Trie.Separates S) {name : String}
    {c : Stream (List (K × V))} {b : ByteArray} {i j : Nat} {t : Trie.T K V D'}
    (h : (refine name c (listingAccept S) Trie.T.toList).get b i = .ok (t, j)) :
    ∃ l, c.get b i = .ok (l, j) ∧ l.Pairwise (fun p q => BitLt S 0 p.1 q.1) ∧
      t = Trie.build S S.depth 0 l := by
  cases hg : c.get b i with
  | error e => simp [refine, hg] at h
  | ok r =>
    obtain ⟨l, j'⟩ := r
    by_cases ho : l.Pairwise (fun p q => BitLt S 0 p.1 q.1)
    · rw [trieListing_get_ok S hsep hg ho] at h
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨l, rfl, ho, rfl⟩
    · rw [trieListing_get_refused S hsep hg ho] at h; cases h

/-! ### Separation on the listing (KERNEL-48's rows: a trie separated on its keys' domain only) -/

/-- A listing in bit order whose keys are separated is accepted. -/
theorem trieListing_get_ok_sep (S : Trie.Spec K V D') {name : String}
    {c : Stream (List (K × V))} {b : ByteArray} {i j : Nat} {l : List (K × V)}
    (h : c.get b i = .ok (l, j)) (hsep : Trie.SepAt S 0 l) (ho : l.Pairwise (fun p q => BitLt S 0 p.1 q.1)) :
    (refine name c (listingAccept S) Trie.T.toList).get b i = .ok (Trie.build S S.depth 0 l, j) := by
  have hc := (build_listing_iff S _ 0 l rfl hsep).mpr ho
  simp only [listingAccept, refine, h]
  rw [if_pos (by rw [Bool.and_eq_true, beq_iff_eq]; exact hc)]

/-- **Every other listing whose keys are separated is refused by the codec's name.** -/
theorem trieListing_get_refused_sep (S : Trie.Spec K V D') {name : String}
    {c : Stream (List (K × V))} {b : ByteArray} {i j : Nat} {l : List (K × V)}
    (h : c.get b i = .ok (l, j)) (hsep : Trie.SepAt S 0 l) (ho : ¬ l.Pairwise (fun p q => BitLt S 0 p.1 q.1)) :
    (refine name c (listingAccept S) Trie.T.toList).get b i = .error (.rejected i name) := by
  have hc : ¬ (((Trie.build S S.depth 0 l).toList == l && leavesNodup (Trie.build S S.depth 0 l)) = true) :=
    fun hc => ho ((build_listing_iff S _ 0 l rfl hsep).mp (by rwa [Bool.and_eq_true, beq_iff_eq] at hc))
  simp only [listingAccept, refine, h]
  rw [if_neg hc]

/-- What a trie-listing codec whose decoded keys are separated accepts was a listing in bit order. -/
theorem trieListing_get_ordered_sep (S : Trie.Spec K V D') {name : String}
    {c : Stream (List (K × V))} {b : ByteArray} {i j : Nat} {t : Trie.T K V D'}
    (hsep : ∀ l j, c.get b i = .ok (l, j) → Trie.SepAt S 0 l)
    (h : (refine name c (listingAccept S) Trie.T.toList).get b i = .ok (t, j)) :
    ∃ l, c.get b i = .ok (l, j) ∧ l.Pairwise (fun p q => BitLt S 0 p.1 q.1) ∧
      t = Trie.build S S.depth 0 l := by
  cases hg : c.get b i with
  | error e => simp [refine, hg] at h
  | ok r =>
    obtain ⟨l, j'⟩ := r
    by_cases ho : l.Pairwise (fun p q => BitLt S 0 p.1 q.1)
    · rw [trieListing_get_ok_sep S hg (hsep l j' hg) ho] at h
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨l, rfl, ho, rfl⟩
    · rw [trieListing_get_refused_sep S hg (hsep l j' hg) ho] at h; cases h

end Listing

section Cells
variable {D : Type} [DecidableEq D]

/-- A cells listing in bit order is accepted: the trie part reads as the trie `build` makes of it. -/
theorem cells_get_ok (E : Env D) (hsep : Trie.Separates (trieSpec E)) {dc : Stream D} {b : ByteArray}
    {i j : Nat} {l : List (Slot D × Leaf)} (h : (fitList dc).get b i = .ok (l, j))
    (ho : l.Pairwise (fun p q => BitLt (trieSpec E) 0 p.1 q.1)) :
    (cells E dc).get b i = .ok (Trie.build (trieSpec E) (trieSpec E).depth 0 l, j) :=
  trieListing_get_ok _ hsep h ho

/-- **Every other cells listing is refused `kernel/trie-order`, by name.** -/
theorem cells_get_refused (E : Env D) (hsep : Trie.Separates (trieSpec E)) {dc : Stream D}
    {b : ByteArray} {i j : Nat} {l : List (Slot D × Leaf)} (h : (fitList dc).get b i = .ok (l, j))
    (ho : ¬ l.Pairwise (fun p q => BitLt (trieSpec E) 0 p.1 q.1)) :
    (cells E dc).get b i = .error (.rejected i "kernel/trie-order") :=
  trieListing_get_refused _ hsep h ho

/-- What the trie part accepts was a listing in bit order, and is the trie `build` makes of it. -/
theorem cells_get_ordered (E : Env D) (hsep : Trie.Separates (trieSpec E)) {dc : Stream D}
    {b : ByteArray} {i j : Nat} {t : Cells D} (h : (cells E dc).get b i = .ok (t, j)) :
    ∃ l, (fitList dc).get b i = .ok (l, j) ∧ l.Pairwise (fun p q => BitLt (trieSpec E) 0 p.1 q.1) ∧
      t = Trie.build (trieSpec E) (trieSpec E).depth 0 l :=
  trieListing_get_ordered _ hsep h

end Cells

end Nanodregg.Codec.Kernel
