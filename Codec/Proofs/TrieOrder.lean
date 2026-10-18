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
variable {K V D' : Type} (S : Trie.Spec K V D')

/-- Where `splitBit` finds no bit, every key of the listing agrees with the first on every bit from
`d` below the depth. -/
theorem splitBit_none {d : Nat} {p : K × V} {rest : List (K × V)} (h : Trie.splitBit S d (p :: rest) = none) :
    ∀ q ∈ rest, ∀ i, d ≤ i → i < S.depth → S.bit q.1 i = S.bit p.1 i := by
  intro q hq i hi hd
  simp only [Trie.splitBit] at h
  have := List.find?_range'_eq_none.mp h i hi (by omega)
  simp only [Bool.not_eq_true', List.any_eq_false] at this
  simpa using this q hq

/-- Where `splitBit` finds `b`: it is in `[d, depth)`, every key agrees with the first on `[d, b)`,
and some key differs from the first at `b`. -/
theorem splitBit_some {d b : Nat} {p : K × V} {rest : List (K × V)}
    (h : Trie.splitBit S d (p :: rest) = some b) :
    d ≤ b ∧ b < S.depth ∧ (∀ q ∈ rest, ∀ i, d ≤ i → i < b → S.bit q.1 i = S.bit p.1 i) ∧
      ∃ q ∈ rest, S.bit q.1 b ≠ S.bit p.1 b := by
  simp only [Trie.splitBit] at h
  obtain ⟨h1, h2, h3⟩ := List.find?_range'_eq_some.mp h
  simp only [List.mem_range'_1] at h2
  refine ⟨h2.1, by omega, fun q hq i hi hib => ?_, ?_⟩
  · have := h3 i hi hib
    simp only [Bool.not_eq_true', List.any_eq_false] at this
    simpa using this q hq
  · simp only [List.any_eq_true, bne_iff_ne, ne_eq] at h1
    exact h1

/-- From `d`, `BitLt` reads the same as from `b` for keys that agree on `[d, b)`. -/
theorem bitLt_skip {d b : Nat} {k k' : K} (hdb : d ≤ b) (he : ∀ i, d ≤ i → i < b → S.bit k i = S.bit k' i) :
    BitLt S d k k' ↔ BitLt S b k k' := by
  constructor
  · rintro ⟨i, hi, hd, hj, h0, h1⟩
    have hbi : b ≤ i := by
      apply Nat.le_of_not_lt; intro hlt
      have := he i hi hlt; rw [h0, h1] at this; cases this
    exact ⟨i, hbi, hd, fun j hj1 hj2 => hj j (by omega) hj2, h0, h1⟩
  · rintro ⟨i, hi, hd, hj, h0, h1⟩
    refine ⟨i, by omega, hd, fun j hj1 hj2 => ?_, h0, h1⟩
    by_cases hjb : j < b
    · exact he j hj1 hjb
    · exact hj j (by omega) hj2

/-- Keys separated from `d` that agree on `[d, b)` are separated from `b`. -/
theorem sepAt_skip {d b : Nat} {l : List (K × V)} (h : Trie.SepAt S d l)
    (he : ∀ p ∈ l, ∀ q ∈ l, ∀ i, d ≤ i → i < b → S.bit p.1 i = S.bit q.1 i) : Trie.SepAt S b l := by
  intro p hp q hq hne
  obtain ⟨i, hi, hd, hb⟩ := h p hp q hq hne
  refine ⟨i, Nat.le_of_not_lt fun hlt => hb (he p hp q hq i hi hlt), hd, hb⟩

/-- Keys separated from `d` with bit `d` equal are separated from `d + 1`. -/
theorem sepAt_side {d : Nat} {l : List (K × V)} (h : Trie.SepAt S d l) (c : Bool)
    (hc : ∀ p ∈ l, S.bit p.1 d = c) : Trie.SepAt S (d + 1) l := by
  intro p hp q hq hne
  obtain ⟨i, hi, hd, hb⟩ := h p hp q hq hne
  refine ⟨i, Nat.lt_of_le_of_ne hi ?_, hd, hb⟩
  rintro rfl; exact hb ((hc p hp).trans (hc q hq).symm)

/-- Separation passes to a sub-listing. -/
theorem sepAt_sub {d : Nat} {l l' : List (K × V)} (h : Trie.SepAt S d l) (hs : ∀ p ∈ l', p ∈ l) :
    Trie.SepAt S d l' := fun p hp q hq hne => h p (hs p hp) q (hs q hq) hne

/-- A key of the trie `build` makes is a key it was handed. -/
theorem mem_build : ∀ (f d : Nat) (l : List (K × V)) (x : K × V), x ∈ (Trie.build S f d l).toList → x ∈ l
  | _, _, [], x, hx => by simp [Trie.build, Trie.T.toList] at hx
  | f, _, [y], x, hx => by cases f <;> simpa [Trie.build, Trie.mkLeaf, Trie.T.toList] using hx
  | 0, _, a :: b :: rest, x, hx => by simpa [Trie.build, Trie.mkLeaf, Trie.T.toList] using hx
  | f + 1, d, a :: b :: rest, x, hx => by
    simp only [Trie.build] at hx
    split at hx
    · simpa [Trie.mkLeaf, Trie.T.toList] using hx
    · simp only [Trie.mkNode, Trie.T.toList, List.mem_append] at hx
      rcases hx with hx | hx
      · exact (List.mem_filter.mp (mem_build f _ _ x hx)).1
      · exact (List.mem_filter.mp (mem_build f _ _ x hx)).1

/-- **The listing `build` reads back is the one in bit order.** From depth `d`, with fuel enough to reach
`depth`, the trie `build` makes from `l` lists `l` back with every leaf's keys distinct exactly when `l`
is pairwise `BitLt S d` on its keys. Path compression changes where `build` splits (at the first bit
the keys disagree on, not at every bit), not the order it lists. -/
theorem build_listing_iff_le [DecidableEq K] : ∀ (f d : Nat) (l : List (K × V)), S.depth - d ≤ f → Trie.SepAt S d l →
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
      generalize hl : a :: b :: rest = l at hs ⊢
      cases hsb : Trie.splitBit S d l with
      | none =>
        -- every key agrees with the first on `[d, depth)`: separated, they are one key, twice
        have hag := splitBit_none S (hl ▸ hsb : Trie.splitBit S d (a :: b :: rest) = none)
        have hba : ∀ i, d ≤ i → i < S.depth → S.bit b.1 i = S.bit a.1 i :=
          hag b (by simp)
        have hab : a.1 = b.1 := Classical.byContradiction fun hne => by
          obtain ⟨i, h1, h2, h3⟩ := hs a (by rw [← hl]; simp) b (by rw [← hl]; simp) hne
          exact h3 (hba i h1 h2).symm
        have hbuild : Trie.build S (f + 1) d l = Trie.mkLeaf S l := by
          subst hl; simp only [Trie.build]; rw [hsb]
        rw [hbuild]
        simp only [Trie.mkLeaf, Trie.T.toList, leavesNodup, true_and, decide_eq_true_eq]
        constructor
        · intro hn; subst hl
          simp only [List.map_cons, List.nodup_cons, List.mem_cons] at hn; exact absurd (Or.inl hab) hn.1
        · intro hp; subst hl
          obtain ⟨i, h1, h2, h3, h4, h5⟩ := (List.pairwise_cons.mp hp).1 b (by simp)
          rw [hba i h1 h2] at h5; rw [h4] at h5; cases h5
      | some c =>
        obtain ⟨hdc, hcd, hag, -⟩ := splitBit_some S (hl ▸ hsb : Trie.splitBit S d (a :: b :: rest) = some c)
        -- every key agrees with every other on `[d, c)`
        have hag' : ∀ p ∈ l, ∀ q ∈ l, ∀ i, d ≤ i → i < c → S.bit p.1 i = S.bit q.1 i := by
          have h1 : ∀ p ∈ l, ∀ i, d ≤ i → i < c → S.bit p.1 i = S.bit a.1 i := by
            intro p hp i hi hic
            rw [← hl, List.mem_cons] at hp
            rcases hp with rfl | hp
            · rfl
            · exact hag p hp i hi hic
          intro p hp q hq i hi hic
          rw [h1 p hp i hi hic, h1 q hq i hi hic]
        have hsc := sepAt_skip S hs hag'
        have hiff : l.Pairwise (fun p q => BitLt S d p.1 q.1) ↔ l.Pairwise (fun p q => BitLt S c p.1 q.1) :=
          ⟨List.Pairwise.imp_of_mem fun hp hq h => (bitLt_skip S hdc (fun i h1 h2 => hag' _ hp _ hq i h1 h2)).mp h,
           List.Pairwise.imp_of_mem fun hp hq h => (bitLt_skip S hdc (fun i h1 h2 => hag' _ hp _ hq i h1 h2)).mpr h⟩
        rw [hiff]
        have hbuild : Trie.build S (f + 1) d l = Trie.mkNode S c
            ((Trie.build S f (c + 1) (l.filter fun q => !S.bit q.1 c)).first.getD a.1)
            (Trie.build S f (c + 1) (l.filter fun q => !S.bit q.1 c))
            (Trie.build S f (c + 1) (l.filter fun q => S.bit q.1 c)) := by
          subst hl; simp only [Trie.build]; rw [hsb]
        rw [hbuild]
        simp only [Trie.mkNode, Trie.T.toList, leavesNodup, Bool.and_eq_true]
        have bL : ∀ p ∈ l.filter (fun p => !S.bit p.1 c), S.bit p.1 c = false := fun p hp => by
          simpa using (List.mem_filter.mp hp).2
        have bR : ∀ p ∈ l.filter (fun p => S.bit p.1 c), S.bit p.1 c = true := fun p hp =>
          (List.mem_filter.mp hp).2
        have hsL : Trie.SepAt S (c + 1) (l.filter fun p => !S.bit p.1 c) :=
          sepAt_side S (sepAt_sub S hsc fun p hp => (List.mem_filter.mp hp).1) false bL
        have hsR : Trie.SepAt S (c + 1) (l.filter fun p => S.bit p.1 c) :=
          sepAt_side S (sepAt_sub S hsc fun p hp => (List.mem_filter.mp hp).1) true bR
        have ihL := build_listing_iff_le f (c + 1) _ (by omega) hsL
        have ihR := build_listing_iff_le f (c + 1) _ (by omega) hsR
        constructor
        · rintro ⟨he, hnL, hnR⟩
          have mL : ∀ p ∈ (Trie.build S f (c + 1) (l.filter fun p => !S.bit p.1 c)).toList,
              S.bit p.1 c = false := fun p hp => bL p (mem_build S _ _ _ p hp)
          have mR : ∀ p ∈ (Trie.build S f (c + 1) (l.filter fun p => S.bit p.1 c)).toList,
              S.bit p.1 c = true := fun p hp => bR p (mem_build S _ _ _ p hp)
          have kL := (filter_sides S mL mR).1
          have kR := (filter_sides S mL mR).2
          rw [he] at kL kR
          have hL := (pairwise_succ_iff S bL).mp (ihL.mp ⟨kL.symm, hnL⟩)
          have hR := (pairwise_succ_iff S bR).mp (ihR.mp ⟨kR.symm, hnR⟩)
          rw [← he, ← kL, ← kR, List.pairwise_append]
          exact ⟨hL, hR, fun p hp q hq => bitLt_at S hcd (bL p (kL ▸ hp)) (bR q (kR ▸ hq))⟩
        · intro hp
          have hsplit := eq_filter_append S l hp
          have hL := ihL.mpr ((pairwise_succ_iff S bL).mpr (hp.sublist List.filter_sublist))
          have hR := ihR.mpr ((pairwise_succ_iff S bR).mpr (hp.sublist List.filter_sublist))
          rw [hL.1, hR.1]
          exact ⟨hsplit.symm, hL.2, hR.2⟩

/-- **The listing `build` reads back is the one in bit order** (the fuel `build`'s callers hand it). -/
theorem build_listing_iff [DecidableEq K] (f d : Nat) (l : List (K × V)) (hf : f = S.depth - d)
    (hs : Trie.SepAt S d l) :
    ((Trie.build S f d l).toList = l ∧ leavesNodup (Trie.build S f d l) = true ↔
      l.Pairwise (fun p q => BitLt S d p.1 q.1)) :=
  build_listing_iff_le S f d l (by omega) hs

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
