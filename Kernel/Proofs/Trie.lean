/-
# Kernel.Proofs.Trie — the Merkle trie is an exact map, and its proofs are sound

* `get_insert`: after `insert k v`, `k` reads `v` and every other key reads what it did, for ANY
  bit function and ANY tree (no premise): `insAt` splits exactly where `getAt`'s `diverge` check
  refuses.
* `inclusion_sound` / `exclusion_sound`: a proof that verifies against the root of a well-formed
  trie tells the truth about the key, or two different byte strings among those the read compares
  (`readPres`: the proof's, then the trie's along the key's path) have one hash (`CollAmong`).
  Inclusion also needs the trie routed (a key that leaves a node's skipped bits is answered `none`
  by `getAt`, so a malformed tree could hold it in a leaf); exclusion does not.
* `rep_first`: a canonical node's `rep` is the first key it lists. `rep` is a cache, not hashed: two
  well-formed trees with the same branching bits and entries have one root and one proof per key
  whatever their `rep`s (`hashOf_rep_irrel`, `proveAt_rep_irrel`); a wrong `rep` is a refusal, never
  a wrong read (`getAt_rep_sound`, tooth `getAt_wrong_rep`).
* Teeth (`Teeth.*`, on a toy whose hash is injective): `inclusion_needs_routed`,
  `prove_excludes_needs_routed`, `ascends_bound_needed`, `unary_routed_wf_not_shape`,
  `hashOf_rep_irrel_needs_wf`.
-/
import Kernel.Trie
import Kernel.Proofs.Bytes

namespace Nanodregg.Kernel.Trie

variable {K V D : Type} (S : Spec K V D) [DecidableEq K]

/-! ## The map -/

theorem find_cons {α : Type} {k : K} {p : K × α} {rest : List (K × α)} :
    find k (p :: rest) = if p.1 = k then some p.2 else find k rest := by
  unfold find; by_cases h : p.1 = k <;> simp [List.find?, h]

theorem find_nil {α : Type} {k : K} : find k ([] : List (K × α)) = none := rfl

theorem find_append {α : Type} {k : K} :
    ∀ {a b : List (K × α)}, find k (a ++ b) = (find k a).or (find k b)
  | [], _ => by simp [find_nil]
  | p :: rest, b => by
      rw [List.cons_append, find_cons, find_cons, find_append]
      split <;> simp

theorem find_filter {α : Type} {k : K} {q : K → Bool} :
    ∀ {l : List (K × α)}, find k (l.filter fun p => q p.1) = if q k then find k l else none
  | [] => by simp [find_nil]
  | p :: rest => by
      by_cases hq : q p.1
      · rw [List.filter_cons_of_pos (by simpa using hq), find_cons, find_cons, find_filter]
        by_cases hk : p.1 = k
        · subst hk; simp [hq]
        · simp [hk]
      · rw [List.filter_cons_of_neg (by simpa using hq), find_cons, find_filter]
        by_cases hk : p.1 = k
        · subst hk; simp [hq]
        · simp [hk]

theorem find_none_of_not_any {α : Type} {k : K} :
    ∀ {l : List (K × α)}, l.any (fun p => p.1 = k) = false → find k l = none
  | [], _ => rfl
  | p :: rest, h => by
      simp only [List.any_cons, Bool.or_eq_false_iff, decide_eq_false_iff_not] at h
      rw [find_cons, if_neg h.1]; exact find_none_of_not_any (by simpa using h.2)

theorem find_replace_ne {k k' : K} {v : V} (hk : k' ≠ k) :
    ∀ {l : List (K × V)}, find k' (l.map fun p => if p.1 = k then (k, v) else p) = find k' l
  | [] => rfl
  | p :: rest => by
      rw [List.map_cons, find_cons, find_cons, find_replace_ne hk]
      by_cases hp : p.1 = k
      · subst hp; simp [Ne.symm hk]
      · simp [hp]

theorem find_replace {k k' : K} {v : V} :
    ∀ {l : List (K × V)}, l.any (fun p => p.1 = k) = true →
      find k' (l.map fun p => if p.1 = k then (k, v) else p) = if k' = k then some v else find k' l
  | [], h => by simp at h
  | p :: rest, h => by
      by_cases hk : k' = k
      · subst hk
        rw [List.map_cons, find_cons]
        by_cases hp : p.1 = k'
        · simp [hp]
        · simp only [hp, if_false]
          have hr : rest.any (fun p => p.1 = k') = true := by simpa [hp] using h
          rw [find_replace hr]; simp
      · rw [find_replace_ne hk]; simp [hk]

/-! ## Bits: `find?` over a range, `diverge`, `splitBit` -/

omit [DecidableEq K] in
theorem find_range' (P : Nat → Bool) : ∀ (n d c : Nat), (List.range' d n).find? P = some c ↔
    d ≤ c ∧ c < d + n ∧ P c = true ∧ ∀ i, d ≤ i → i < c → P i = false
  | 0, d, c => by
      simp only [List.range'_zero, List.find?_nil]
      constructor
      · intro h; cases h
      · rintro ⟨h1, h2, -⟩; omega
  | n + 1, d, c => by
      rw [List.range'_succ]
      cases hP : P d
      · simp only [List.find?_cons, hP]
        rw [find_range' P n (d + 1) c]
        constructor
        · rintro ⟨h1, h2, h3, h4⟩
          refine ⟨by omega, by omega, h3, fun i hi hic => ?_⟩
          rcases Nat.lt_or_eq_of_le hi with h | rfl
          · exact h4 i h hic
          · exact hP
        · rintro ⟨h1, h2, h3, h4⟩
          have hne : c ≠ d := by rintro rfl; rw [hP] at h3; cases h3
          exact ⟨by omega, by omega, h3, fun i hi hic => h4 i (by omega) hic⟩
      · simp only [List.find?_cons, hP, Option.some.injEq]
        constructor
        · rintro rfl; exact ⟨Nat.le_refl _, by omega, hP, fun i hi hic => absurd hic (by omega)⟩
        · rintro ⟨h1, h2, h3, h4⟩
          rcases Nat.lt_or_eq_of_le h1 with h | h
          · have := h4 d (Nat.le_refl _) h; rw [hP] at this; cases this
          · exact h

omit [DecidableEq K] in
theorem find_range'_none (P : Nat → Bool) (n d : Nat) : (List.range' d n).find? P = none ↔
    ∀ i, d ≤ i → i < d + n → P i = false := by
  rw [List.find?_eq_none]
  constructor
  · intro h i h1 h2; simpa using h i (List.mem_range'_1.mpr ⟨h1, h2⟩)
  · intro h i hi; have := List.mem_range'_1.mp hi; simp [h i this.1 this.2]

omit [DecidableEq K] in
theorem bool_ne {a b : Bool} (h : a ≠ b) : a = !b := by cases a <;> cases b <;> simp_all

omit [DecidableEq K] in
theorem diverge_none {k k' : K} {d b : Nat} :
    diverge S k k' d b = none ↔ ∀ i, d ≤ i → i < b → S.bit k i = S.bit k' i := by
  unfold diverge; rw [find_range'_none]
  constructor
  · intro h i h1 h2; simpa using h i h1 (by omega)
  · intro h i h1 h2; simp [h i h1 (by omega)]

omit [DecidableEq K] in
theorem diverge_some {k k' : K} {d b c : Nat} :
    diverge S k k' d b = some c ↔
      d ≤ c ∧ c < b ∧ S.bit k c ≠ S.bit k' c ∧ ∀ i, d ≤ i → i < c → S.bit k i = S.bit k' i := by
  unfold diverge; rw [find_range']
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨h1, by omega, by simpa using h3, fun i hi hic => by simpa using h4 i hi hic⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨h1, by omega, by simpa using h3, fun i hi hic => by simpa using h4 i hi hic⟩

omit [DecidableEq K] in
/-- Bits `k'` and `k''` share on `[d, b)` do not change where `k` first leaves them. -/
theorem diverge_congr {k k' k'' : K} {d b : Nat} (h : ∀ i, d ≤ i → i < b → S.bit k' i = S.bit k'' i) :
    diverge S k k' d b = diverge S k k'' d b := by
  cases h1 : diverge S k k'' d b with
  | none =>
      rw [diverge_none] at h1 ⊢; intro i hi hib; rw [h1 i hi hib, h i hi hib]
  | some c =>
      rw [diverge_some] at h1 ⊢
      obtain ⟨a, e, f, g⟩ := h1
      exact ⟨a, e, by rwa [h c a e], fun i hi hic => by rw [g i hi hic, h i hi (by omega)]⟩

omit [DecidableEq K] in
/-- Bits `k` and `k'` agree on `[d, d')`: their first difference from `d` is their first from `d'`. -/
theorem diverge_skip {k k' : K} {d d' b : Nat} (hd : d ≤ d')
    (h : ∀ i, d ≤ i → i < d' → S.bit k i = S.bit k' i) : diverge S k k' d b = diverge S k k' d' b := by
  cases h1 : diverge S k k' d' b with
  | none =>
      rw [diverge_none] at h1 ⊢; intro i hi hib
      by_cases hl : i < d'
      · exact h i hi hl
      · exact h1 i (by omega) hib
  | some c =>
      rw [diverge_some] at h1 ⊢
      obtain ⟨a, e, f, g⟩ := h1
      refine ⟨by omega, e, f, fun i hi hic => ?_⟩
      by_cases hl : i < d'
      · exact h i hi hl
      · exact g i (by omega) hic

omit [DecidableEq K] in
theorem diverge_widen {k k' : K} {d b b' c : Nat} (h : diverge S k k' d b = some c) (hb : b ≤ b') :
    diverge S k k' d b' = some c := by
  obtain ⟨a, e, f, g⟩ := (diverge_some S).mp h
  exact (diverge_some S).mpr ⟨a, by omega, f, g⟩

omit [DecidableEq K] in
theorem precedes_of_diverge {k k' : K} {d b c : Nat} (h : diverge S k k' d b = some c) (hb : b ≤ S.depth) :
    precedes S k k' d = !S.bit k c := by
  unfold precedes; rw [diverge_widen S h hb]

omit [DecidableEq K] in
theorem precedes_of_agree {k k' : K} {d : Nat} (h : ∀ i, d ≤ i → i < S.depth → S.bit k i = S.bit k' i) :
    precedes S k k' d = false := by
  unfold precedes; rw [(diverge_none S).mpr h]

omit [DecidableEq K] in
theorem precedes_skip {k k' : K} {d d' : Nat} (hd : d ≤ d') (h : ∀ i, d ≤ i → i < d' → S.bit k i = S.bit k' i) :
    precedes S k k' d = precedes S k k' d' := by
  unfold precedes; rw [diverge_skip S hd h]

omit [DecidableEq K] in
theorem any_split (p : K × V) (rest : List (K × V)) (i : Nat) :
    (rest.any fun q => S.bit q.1 i != S.bit p.1 i) = true ↔
      ∃ x ∈ p :: rest, ∃ y ∈ p :: rest, S.bit x.1 i ≠ S.bit y.1 i := by
  rw [List.any_eq_true]
  constructor
  · rintro ⟨q, hq, h⟩; exact ⟨q, List.mem_cons_of_mem _ hq, p, by simp, by simpa using h⟩
  · rintro ⟨x, hx, y, hy, h⟩
    by_cases hxp : S.bit x.1 i = S.bit p.1 i
    · have hyp : S.bit y.1 i ≠ S.bit p.1 i := fun e => h (hxp.trans e.symm)
      rcases List.mem_cons.mp hy with rfl | hy'
      · exact absurd rfl hyp
      · exact ⟨y, hy', by simpa using hyp⟩
    · rcases List.mem_cons.mp hx with rfl | hx'
      · exact absurd rfl hxp
      · exact ⟨x, hx', by simpa using hxp⟩

omit [DecidableEq K] in
theorem splitBit_some {d c : Nat} {p : K × V} {rest : List (K × V)} :
    splitBit S d (p :: rest) = some c ↔ d ≤ c ∧ c < S.depth ∧ (∃ q ∈ rest, S.bit q.1 c ≠ S.bit p.1 c) ∧
      ∀ i, d ≤ i → i < c → ∀ q ∈ rest, S.bit q.1 i = S.bit p.1 i := by
  unfold splitBit; rw [find_range']
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    obtain ⟨q, hq, hne⟩ := List.any_eq_true.mp h3
    refine ⟨h1, by omega, ⟨q, hq, by simpa using hne⟩, fun i hi hic q hq => ?_⟩
    have := List.any_eq_false.mp (h4 i hi hic) q hq
    simpa using this
  · rintro ⟨h1, h2, ⟨q, hq, hne⟩, h4⟩
    refine ⟨h1, by omega, List.any_eq_true.mpr ⟨q, hq, by simpa using hne⟩, fun i hi hic => ?_⟩
    exact List.any_eq_false.mpr fun q hq => by simpa using h4 i hi hic q hq

omit [DecidableEq K] in
theorem splitBit_none {d : Nat} {p : K × V} {rest : List (K × V)} :
    splitBit S d (p :: rest) = none ↔ ∀ i, d ≤ i → i < S.depth → ∀ q ∈ rest, S.bit q.1 i = S.bit p.1 i := by
  unfold splitBit; rw [find_range'_none]
  constructor
  · intro h i hi hid q hq
    have := List.any_eq_false.mp (h i hi (by omega)) q hq
    simpa using this
  · intro h i hi hid
    exact List.any_eq_false.mpr fun q hq => by simpa using h i hi (by omega) q hq

omit [DecidableEq K] in
/-- Every entry agrees with the head on the bits below the split. -/
theorem splitBit_agree {d c : Nat} {p : K × V} {rest : List (K × V)} (h : splitBit S d (p :: rest) = some c) :
    ∀ x ∈ p :: rest, ∀ i, d ≤ i → i < c → S.bit x.1 i = S.bit p.1 i := by
  obtain ⟨_, _, _, h4⟩ := (splitBit_some S).mp h
  intro x hx i hi hic
  rcases List.mem_cons.mp hx with rfl | hx'
  · rfl
  · exact h4 i hi hic x hx'

omit [DecidableEq K] in
/-- A split has entries on both sides. -/
theorem splitBit_sides {d c : Nat} {p : K × V} {rest : List (K × V)} (h : splitBit S d (p :: rest) = some c) :
    (∃ x ∈ p :: rest, S.bit x.1 c = false) ∧ (∃ x ∈ p :: rest, S.bit x.1 c = true) := by
  obtain ⟨_, _, ⟨q, hq, hne⟩, _⟩ := (splitBit_some S).mp h
  have hq' : q ∈ p :: rest := List.mem_cons_of_mem _ hq
  have hp' : p ∈ p :: rest := by simp
  have := bool_ne hne
  cases hpc : S.bit p.1 c
  · rw [hpc] at this; exact ⟨⟨p, hp', hpc⟩, ⟨q, hq', this⟩⟩
  · rw [hpc] at this; exact ⟨⟨q, hq', this⟩, ⟨p, hp', hpc⟩⟩

omit [DecidableEq K] in
theorem splitBit_bounds {d c : Nat} {kvs : List (K × V)} (h : splitBit S d kvs = some c) : d ≤ c ∧ c < S.depth := by
  cases kvs with
  | nil => cases h
  | cons p rest => obtain ⟨h1, h2, _⟩ := (splitBit_some S).mp h; exact ⟨h1, h2⟩

omit [DecidableEq K] in
theorem head_key {α β : Type} {x : α} : ∀ {l : List (α × β)}, l.head?.map Prod.fst = some x → ∃ p ∈ l, p.1 = x
  | [], h => by simp at h
  | p :: _, h => ⟨p, by simp, by simpa using h⟩

omit [DecidableEq K] in
theorem head_append_of {α β : Type} {x : α} {l₂ : List (α × β)} :
    ∀ {l₁ : List (α × β)}, l₁.head?.map Prod.fst = some x → (l₁ ++ l₂).head?.map Prod.fst = some x
  | [], h => by simp at h
  | _ :: _, h => h

omit [DecidableEq K] in
theorem ne_nil_of_perm {α : Type} {l₁ l₂ : List α} (hp : l₁.Perm l₂) (hne : l₂ ≠ []) : l₁ ≠ [] := by
  intro h; rw [h] at hp; exact hne hp.symm.eq_nil

theorem find_mem {α : Type} {k : K} {v : α} : ∀ {l : List (K × α)}, find k l = some v → (k, v) ∈ l
  | [], h => by cases h
  | p :: rest, h => by
      rw [find_cons] at h
      split at h
      · rename_i hp; simp only [Option.some.injEq] at h; subst h; rw [← hp]; simp
      · exact List.mem_cons_of_mem _ (find_mem h)

theorem find_absent {α : Type} {k : K} : ∀ {l : List (K × α)}, (∀ p ∈ l, p.1 ≠ k) → find k l = none
  | [], _ => rfl
  | p :: rest, h => by
      rw [find_cons, if_neg (h p (by simp))]
      exact find_absent fun q hq => h q (List.mem_cons_of_mem _ hq)

/-! ## `build` -/

omit [DecidableEq K] in
/-- `build` on entries that part at bit `b`, with fuel left, is a node at `b` over the two filters,
its `rep` the left side's first key. -/
theorem build_split (f d b : Nat) (p : K × V) (rest : List (K × V)) (h : splitBit S d (p :: rest) = some b) :
    build S (f + 1) d (p :: rest) =
      mkNode S b ((build S f (b + 1) ((p :: rest).filter fun q => !S.bit q.1 b)).first.getD p.1)
        (build S f (b + 1) ((p :: rest).filter fun q => !S.bit q.1 b))
        (build S f (b + 1) ((p :: rest).filter fun q => S.bit q.1 b)) := by
  cases rest with
  | nil => obtain ⟨_, _, ⟨q, hq, _⟩, _⟩ := (splitBit_some S).mp h; cases hq
  | cons x xs => simp only [build, h]

omit [DecidableEq K] in
/-- Entries that agree on every bit from `d` on make one leaf. -/
theorem build_agree (f d : Nat) (p : K × V) (rest : List (K × V))
    (h : ∀ i, d ≤ i → i < S.depth → ∀ q ∈ rest, S.bit q.1 i = S.bit p.1 i) :
    build S f d (p :: rest) = mkLeaf S (p :: rest) := by
  cases rest with
  | nil => cases f <;> rfl
  | cons x xs =>
      cases f with
      | zero => rfl
      | succ f => simp only [build, (splitBit_none S).mpr h]

omit [DecidableEq K] in
theorem build_first_mem : ∀ (f d : Nat) (kvs : List (K × V)) (x : K),
    (build S f d kvs).first = some x → ∃ p ∈ kvs, p.1 = x
  | _, _, [], _, h => by simp [build, T.first] at h
  | f, _, [y], x, h => by
      cases f <;> simp [build, mkLeaf, T.first] at h <;> exact ⟨y, by simp, h⟩
  | 0, _, a :: b :: rest, x, h => by
      simp [build, mkLeaf, T.first] at h; exact ⟨a, by simp, h⟩
  | f + 1, d, a :: b :: rest, x, h => by
      simp only [build] at h
      cases hs : splitBit S d (a :: b :: rest) with
      | none => rw [hs] at h; simp [mkLeaf, T.first] at h; exact ⟨a, by simp, h⟩
      | some c =>
          rw [hs] at h; dsimp only at h
          cases hl : (build S f (c + 1) ((a :: b :: rest).filter fun q => !S.bit q.1 c)).first with
          | none =>
              rw [hl] at h; simp only [mkNode, T.first, Option.getD, Option.some.injEq] at h
              exact ⟨a, by simp, h⟩
          | some y =>
              rw [hl] at h; simp only [mkNode, T.first, Option.getD, Option.some.injEq] at h
              obtain ⟨p, hp, hpy⟩ := build_first_mem f (c + 1) _ y hl
              exact ⟨p, (List.mem_filter.mp hp).1, hpy.trans h⟩

omit [DecidableEq K] in
theorem build_first_some : ∀ (f d : Nat) (kvs : List (K × V)), kvs ≠ [] → ∃ x, (build S f d kvs).first = some x
  | _, _, [], h => absurd rfl h
  | f, _, [y], _ => by cases f <;> exact ⟨y.1, rfl⟩
  | 0, _, a :: b :: rest, _ => ⟨a.1, rfl⟩
  | f + 1, d, a :: b :: rest, _ => by
      simp only [build]
      cases splitBit S d (a :: b :: rest) with
      | none => exact ⟨a.1, rfl⟩
      | some c => exact ⟨_, rfl⟩

omit [DecidableEq K] in
/-- A split node's `rep` is one of the entries' keys. -/
theorem build_node_rep (f d c : Nat) (p : K × V) (rest : List (K × V)) (h : splitBit S d (p :: rest) = some c) :
    ∃ rep, (∃ x ∈ p :: rest, x.1 = rep) ∧ build S (f + 1) d (p :: rest) =
      mkNode S c rep (build S f (c + 1) ((p :: rest).filter fun q => !S.bit q.1 c))
        (build S f (c + 1) ((p :: rest).filter fun q => S.bit q.1 c)) := by
  rw [build_split S f d c p rest h]
  cases hf : (build S f (c + 1) ((p :: rest).filter fun q => !S.bit q.1 c)).first with
  | none => exact ⟨p.1, ⟨p, by simp, rfl⟩, rfl⟩
  | some y =>
      obtain ⟨x, hx, hxy⟩ := build_first_mem S _ _ _ y hf
      exact ⟨y, ⟨x, (List.mem_filter.mp hx).1, hxy⟩, rfl⟩

theorem getAt_build :
    ∀ (f d : Nat) (kvs : List (K × V)) (k : K), getAt S k d (build S f d kvs) = find k kvs
  | _, _, [], _ => by simp [build, getAt, find_nil]
  | f, _, [x], k => by cases f <;> simp [build, getAt, mkLeaf]
  | 0, _, a :: b :: rest, k => by simp [build, getAt, mkLeaf]
  | f + 1, d, a :: b :: rest, k => by
      cases hs : splitBit S d (a :: b :: rest) with
      | none => simp only [build, hs, mkLeaf, getAt]
      | some c =>
          obtain ⟨rep, ⟨x, hx, hxr⟩, hb⟩ := build_node_rep S f d c a (b :: rest) hs
          rw [hb]
          have hag := splitBit_agree S hs
          simp only [mkNode, getAt]
          cases hdk : diverge S k rep d c with
          | some e =>
              obtain ⟨hde, hec, hne, _⟩ := (diverge_some S).mp hdk
              simp only
              symm
              cases hf : find k (a :: b :: rest) with
              | none => rfl
              | some w =>
                  have hm := find_mem hf
                  have h1 := hag _ hm e hde hec
                  have h2 := hag x hx e hde hec
                  rw [hxr] at h2; simp only at h1
                  exact absurd (h1.trans h2.symm) hne
          | none =>
              simp only
              cases hb : S.bit k c
              · simp only
                rw [getAt_build f (c + 1), find_filter (q := fun x => !S.bit x c)]; simp [hb]
              · simp only
                rw [getAt_build f (c + 1), find_filter (q := fun x => S.bit x c)]; simp [hb]

/-! ## The insert that re-hashed a split leaf (cv 01a15107-2263)

`insAt` keeps the cached digest of a one-entry leaf a new key splits; before, it `build`t the pair
and re-hashed that leaf. `insAtRebuild` is that insert, kept as the reference the theorems about
`insAt` were first proved for: the two tries agree but for cached digests, unconditionally
(`hashEq_insAt`), so every routing and shape fact transfers; and on a well-formed trie they are the
SAME trie, digests included (`insAt_eq_rebuild`): no root, proof or head moves. -/

/-- `insAt` before cv 01a15107-2263: a new key reaching a leaf `build`s the leaf's entries with it. -/
private def insAtRebuild (k : K) (v : V) : Nat → T K V D → T K V D
  | _, .empty => mkLeaf S [(k, v)]
  | d, .leaf _ kvs =>
      if kvs.any (fun p => p.1 = k) then mkLeaf S (kvs.map fun p => if p.1 = k then (k, v) else p)
      else build S (S.depth - d) d (kvs ++ [(k, v)])
  | d, .node h b rep l r =>
      match diverge S k rep d b with
      | some c =>
          match S.bit k c with
          | true => mkNode S c rep (.node h b rep l r) (mkLeaf S [(k, v)])
          | false => mkNode S c k (mkLeaf S [(k, v)]) (.node h b rep l r)
      | none =>
          match S.bit k b with
          | true => mkNode S b rep l (insAtRebuild k v (b + 1) r)
          | false => mkNode S b (if precedes S k rep (b + 1) then k else rep) (insAtRebuild k v (b + 1) l) r

omit [DecidableEq K] in
/-- Two tries equal but for their cached digests. -/
def HashEq : T K V D → T K V D → Prop
  | .empty, .empty => True
  | .leaf _ kvs, .leaf _ kvs' => kvs = kvs'
  | .node _ b rep l r, .node _ b' rep' l' r' => b = b' ∧ rep = rep' ∧ HashEq l l' ∧ HashEq r r'
  | _, _ => False

omit [DecidableEq K] in
theorem hashEq_refl : ∀ t : T K V D, HashEq t t
  | .empty => trivial
  | .leaf _ _ => rfl
  | .node _ _ _ l r => ⟨rfl, rfl, hashEq_refl l, hashEq_refl r⟩

/-- A lookup does not read cached digests. -/
theorem getAt_hashEq (k : K) : ∀ (d : Nat) (t u : T K V D), HashEq t u → getAt S k d t = getAt S k d u
  | _, .empty, .empty, _ => rfl
  | _, .leaf _ _, .leaf _ _, h => by simp only [HashEq] at h; subst h; rfl
  | d, .node _ b rep l r, .node _ b' rep' l' r', h => by
      obtain ⟨rfl, rfl, hl, hr⟩ := h
      simp only [getAt]; rw [getAt_hashEq k (b + 1) l l' hl, getAt_hashEq k (b + 1) r r' hr]
  | _, .empty, .leaf .., h | _, .empty, .node .., h | _, .leaf .., .empty, h
  | _, .leaf .., .node .., h | _, .node .., .empty, h | _, .node .., .leaf .., h => by simp [HashEq] at h

omit [DecidableEq K] in
/-- Nor does a listing. -/
theorem toList_hashEq : ∀ (t u : T K V D), HashEq t u → t.toList = u.toList
  | .empty, .empty, _ => rfl
  | .leaf _ _, .leaf _ _, h => by simp only [HashEq] at h; subst h; rfl
  | .node _ _ _ l r, .node _ _ _ l' r', h => by
      obtain ⟨-, -, hl, hr⟩ := h
      simp only [T.toList]; rw [toList_hashEq l l' hl, toList_hashEq r r' hr]
  | .empty, .leaf .., h | .empty, .node .., h | .leaf .., .empty, h
  | .leaf .., .node .., h | .node .., .empty, h | .node .., .leaf .., h => by simp [HashEq] at h

omit [DecidableEq K] in
theorem build_single (f d : Nat) (x : K × V) : build S f d [x] = mkLeaf S [x] := by cases f <;> rfl

omit [DecidableEq K] in
/-- `build` of a one-entry leaf's entry and a key that leaves it at `c`: one node over the two
leaves, ordered by the key's bit `c`. -/
theorem build_pair (d c : Nat) (p : K × V) (k : K) (v : V) (hc : diverge S k p.1 d S.depth = some c) :
    build S (S.depth - d) d ([p] ++ [(k, v)]) =
      match S.bit k c with
      | true => mkNode S c p.1 (mkLeaf S [p]) (mkLeaf S [(k, v)])
      | false => mkNode S c k (mkLeaf S [(k, v)]) (mkLeaf S [p]) := by
  obtain ⟨hdc, hcd, hne, -⟩ := (diverge_some S).mp hc
  obtain ⟨f, hf⟩ : ∃ f, S.depth - d = f + 1 := ⟨S.depth - d - 1, by omega⟩
  have hs : splitBit S d ([p] ++ [(k, v)]) = some c := by
    simp only [splitBit, List.cons_append, List.nil_append, List.any_cons, List.any_nil, Bool.or_false]
    simp only [diverge] at hc
    rw [← hc]
  have hp : S.bit p.1 c = !S.bit k c := by
    cases h1 : S.bit k c <;> cases h2 : S.bit p.1 c <;> simp_all
  rw [hf]
  simp only [List.cons_append, List.nil_append] at hs ⊢
  rw [build_split S f d c p [(k, v)] hs]
  cases hk : S.bit k c <;> simp only [hk, Bool.not_false, Bool.not_true] at hp <;>
    simp [List.filter, hk, hp, mkLeaf, T.first, build_single]

/-- **`insAt` is `insAtRebuild` but for cached digests**, on ANY trie: the same nodes, branching bits,
`rep`s and entries. -/
private theorem hashEq_insAt (k : K) (v : V) : ∀ (d : Nat) (t : T K V D), HashEq (insAt S k v d t) (insAtRebuild S k v d t)
  | _, .empty => hashEq_refl _
  | d, .leaf h kvs => by
      simp only [insAt, insAtRebuild]
      split
      · exact hashEq_refl _
      · match kvs with
        | [p] =>
            simp only
            cases hc : diverge S k p.1 d S.depth with
            | none => exact hashEq_refl _
            | some c =>
                simp only
                rw [build_pair S d c p k v hc]
                cases S.bit k c <;> exact ⟨rfl, rfl, rfl, rfl⟩
        | [] => exact hashEq_refl _
        | _ :: _ :: _ => exact hashEq_refl _
  | d, .node h b rep l r => by
      simp only [insAt, insAtRebuild]
      cases diverge S k rep d b with
      | some c => simp only; cases S.bit k c <;> exact hashEq_refl _
      | none =>
          simp only
          cases S.bit k b
          · exact ⟨rfl, rfl, hashEq_insAt k v (b + 1) l, hashEq_refl r⟩
          · exact ⟨rfl, rfl, hashEq_refl l, hashEq_insAt k v (b + 1) r⟩

private theorem getAt_insAtRebuild (k k' : K) (v : V) :
    ∀ (d : Nat) (t : T K V D), getAt S k' d (insAtRebuild S k v d t) = if k' = k then some v else getAt S k' d t
  | d, .empty => by
      simp only [insAtRebuild, mkLeaf, getAt, find_cons, find_nil]
      by_cases h : k' = k
      · subst h; simp
      · simp [h, Ne.symm h]
  | d, .leaf h kvs => by
      simp only [insAtRebuild]
      split
      · rename_i hany; simp only [mkLeaf, getAt]; exact find_replace hany
      · rename_i hany
        rw [getAt_build, find_append, getAt, find_cons, find_nil]
        by_cases hk : k' = k
        · subst hk; simp [find_none_of_not_any (Bool.eq_false_iff.mpr hany)]
        · simp [hk, Ne.symm hk]
  | d, .node h b rep l r => by
      simp only [insAtRebuild]
      cases hdk : diverge S k rep d b with
      | some c =>
          dsimp only
          obtain ⟨hdc, hcb, hkc, hpre⟩ := (diverge_some S).mp hdk
          have hrc := bool_ne (Ne.symm hkc)
          -- `k'` against the old node, split at `c`
          have hsplit : ∀ (hk' : ∀ i, d ≤ i → i < c → S.bit k' i = S.bit rep i),
              S.bit k' c = S.bit rep c → diverge S k' rep d b = diverge S k' rep (c + 1) b :=
            fun hk' hc => diverge_skip S (by omega) fun i hi hic =>
              if hlt : i < c then hk' i hi hlt else by rw [show i = c by omega]; exact hc
          have hout : ∀ (hk' : ∀ i, d ≤ i → i < c → S.bit k' i = S.bit rep i),
              S.bit k' c ≠ S.bit rep c → diverge S k' rep d b = some c :=
            fun hk' hc => (diverge_some S).mpr ⟨hdc, hcb, hc, hk'⟩
          have hfar : ∀ e, diverge S k' rep d c = some e → diverge S k' rep d b = some e ∧ k' ≠ k := by
            intro e he
            obtain ⟨hde, hec, hne, _⟩ := (diverge_some S).mp he
            refine ⟨diverge_widen S he (by omega), fun hkk => ?_⟩
            subst hkk; exact hne (hpre e hde hec)
          cases hkb : S.bit k c
          · -- `k` goes left: its leaf, then the old node; the new `rep` is `k`
            have hcong : diverge S k' k d c = diverge S k' rep d c := diverge_congr S hpre
            simp only [mkNode, mkLeaf, getAt, hcong]
            cases h1 : diverge S k' rep d c with
            | some e =>
                obtain ⟨h2, hne⟩ := hfar e h1
                simp [h2, hne]
            | none =>
                have hk' := (diverge_none S).mp h1
                cases h3 : S.bit k' c
                · simp only [find_cons, find_nil]
                  by_cases hkk : k' = k
                  · subst hkk; simp
                  · have : diverge S k' rep d b = some c :=
                      hout hk' (by rw [h3, hrc, hkb]; decide)
                    simp [this, hkk, Ne.symm hkk]
                · have hkk : k' ≠ k := by rintro rfl; rw [hkb] at h3; cases h3
                  rw [hsplit hk' (by rw [h3, hrc, hkb]; rfl)]
                  simp [hkk]
          · -- `k` goes right: the old node, then its leaf
            simp only [mkNode, mkLeaf, getAt]
            cases h1 : diverge S k' rep d c with
            | some e =>
                obtain ⟨h2, hne⟩ := hfar e h1
                simp [h2, hne]
            | none =>
                have hk' := (diverge_none S).mp h1
                cases h3 : S.bit k' c
                · have hkk : k' ≠ k := by rintro rfl; rw [hkb] at h3; cases h3
                  rw [hsplit hk' (by rw [h3, hrc, hkb]; rfl)]
                  simp [hkk]
                · simp only [find_cons, find_nil]
                  by_cases hkk : k' = k
                  · subst hkk; simp
                  · have : diverge S k' rep d b = some c :=
                      hout hk' (by rw [h3, hrc, hkb]; decide)
                    simp [this, hkk, Ne.symm hkk]
      | none =>
          have hagk := (diverge_none S).mp hdk
          cases hkb : S.bit k b
          · have hcong : diverge S k' (if precedes S k rep (b + 1) then k else rep) d b =
                diverge S k' rep d b := by
              split
              · exact diverge_congr S hagk
              · rfl
            simp only [mkNode, getAt, hcong]
            cases h1 : diverge S k' rep d b with
            | some e =>
                have hkk : k' ≠ k := by rintro rfl; rw [hdk] at h1; cases h1
                simp [hkk]
            | none =>
                cases h2 : S.bit k' b
                · simp only; rw [getAt_insAtRebuild k k' v (b + 1) l]
                · have hkk : k' ≠ k := by rintro rfl; rw [hkb] at h2; cases h2
                  simp [hkk]
          · simp only [mkNode, getAt]
            cases h1 : diverge S k' rep d b with
            | some e =>
                have hkk : k' ≠ k := by rintro rfl; rw [hdk] at h1; cases h1
                simp [hkk]
            | none =>
                cases h2 : S.bit k' b
                · have hkk : k' ≠ k := by rintro rfl; rw [hkb] at h2; cases h2
                  simp [hkk]
                · simp only; rw [getAt_insAtRebuild k k' v (b + 1) r]

/-- `getAt` after `insAt` (the cached digests do not route, `getAt_hashEq`). -/
theorem getAt_insAt (k k' : K) (v : V) :
    ∀ (d : Nat) (t : T K V D), getAt S k' d (insAt S k v d t) = if k' = k then some v else getAt S k' d t :=
  fun d t => (getAt_hashEq S k' d _ _ (hashEq_insAt S k v d t)).trans (getAt_insAtRebuild S k k' v d t)

/-- **The trie is a map.** -/
theorem get_insert (t : T K V D) (k k' : K) (v : V) :
    (t.insert S k v).get S k' = if k' = k then some v else t.get S k' :=
  getAt_insAt S k k' v 0 t

theorem get_insert_self (t : T K V D) (k : K) (v : V) : (t.insert S k v).get S k = some v := by
  simp [get_insert]

theorem get_insert_ne (t : T K V D) {k k' : K} (v : V) (h : k' ≠ k) :
    (t.insert S k v).get S k' = t.get S k' := by
  simp [get_insert, h]

theorem get_empty (k : K) : (T.empty : T K V D).get S k = none := rfl

/-! ## The batch is the sequential trie (cv 01a15107-2281) -/

theorem seal_insLeafU (k : K) (v : V) (d : Nat) (h : D) (kvs : List (K × V))
    (keep : U K V D) (hk : keep.seal S = .leaf h kvs) :
    (insLeafU S k v d keep kvs).seal S = insAt S k v d (.leaf h kvs) := by
  by_cases ha : kvs.any (fun p => p.1 = k) = true
  · simp only [insLeafU, insAt, ha, if_true]; rfl
  · simp only [Bool.not_eq_true] at ha
    rcases kvs with _ | ⟨p, _ | ⟨q, rest⟩⟩
    · rfl
    · have hp : p.1 ≠ k := by simpa using ha
      cases hd : diverge S k p.1 d S.depth with
      | none =>
          simp only [insLeafU, insAt, List.any_cons, List.any_nil, Bool.or_false, decide_eq_true_eq, hp, if_false, hd]
          rfl
      | some c =>
          simp only [insLeafU, insAt, List.any_cons, List.any_nil, Bool.or_false, decide_eq_true_eq, hp, if_false, hd]
          cases hb : S.bit k c
          · show mkNode S c k (mkLeaf S [(k, v)]) (keep.seal S) = _
            rw [hk]
          · show mkNode S c p.1 (keep.seal S) (mkLeaf S [(k, v)]) = _
            rw [hk]
    · simp only [insLeafU, insAt, ha, Bool.false_eq_true, if_false]
      rfl

/-- Sealing `insT` of a clean subtree is `insAt` of it: no premise. -/
theorem seal_insT (k : K) (v : V) : ∀ (d : Nat) (t : T K V D),
    (insT S k v d t).seal S = insAt S k v d t
  | _, .empty => by simp only [insT, insAt, U.seal]
  | d, .leaf h kvs => seal_insLeafU S k v d h kvs (.clean (.leaf h kvs)) rfl
  | d, .node h b rep l r => by
      simp only [insT, insAt]
      cases hd : diverge S k rep d b
      · dsimp only
        cases hb : S.bit k b
        · dsimp only
          rw [show (U.node b (if precedes S k rep (b + 1) = true then k else rep) (insT S k v (b + 1) l) (.clean r)).seal S
            = mkNode S b (if precedes S k rep (b + 1) = true then k else rep) ((insT S k v (b + 1) l).seal S) r from rfl,
            seal_insT k v (b + 1) l]
        · dsimp only
          rw [show (U.node b rep (.clean l) (insT S k v (b + 1) r)).seal S
            = mkNode S b rep l ((insT S k v (b + 1) r).seal S) from rfl,
            seal_insT k v (b + 1) r]
      · dsimp only
        cases S.bit k _ <;> rfl

/-- **Sealing an overlay insert is the insert of the sealed trie**, for ANY overlay, ANY bit function
and ANY tree: no premise (unlike `insAt_eq_rebuild`, which needs `WF`: the overlay keeps every cached
digest `insAt` keeps, and recomputes none). -/
theorem seal_insU (k : K) (v : V) : ∀ (d : Nat) (u : U K V D),
    (insU S k v d u).seal S = insAt S k v d (u.seal S)
  | d, .clean t => seal_insT S k v d t
  | d, .leaf kvs => seal_insLeafU S k v d (leafHash S (digests S kvs)) kvs (.leaf kvs) rfl
  | d, .node b rep l r => by
      have hs : (U.node b rep l r).seal S = .node (nodeHash S b ((l.seal S).hashOf S) ((r.seal S).hashOf S)) b rep (l.seal S) (r.seal S) := rfl
      rw [hs]
      simp only [insU, insAt]
      cases hd : diverge S k rep d b
      · dsimp only
        cases hb : S.bit k b
        · dsimp only
          rw [show (U.node b (if precedes S k rep (b + 1) = true then k else rep) (insU S k v (b + 1) l) r).seal S
            = mkNode S b (if precedes S k rep (b + 1) = true then k else rep) ((insU S k v (b + 1) l).seal S) (r.seal S) from rfl,
            seal_insU k v (b + 1) l]
        · dsimp only
          rw [show (U.node b rep l (insU S k v (b + 1) r)).seal S
            = mkNode S b rep (l.seal S) ((insU S k v (b + 1) r).seal S) from rfl,
            seal_insU k v (b + 1) r]
      · dsimp only
        cases S.bit k _ <;> rfl

theorem seal_foldl : ∀ (kvs : List (K × V)) (u : U K V D),
    (kvs.foldl (fun u p => insU S p.1 p.2 0 u) u).seal S = kvs.foldl (fun t p => t.insert S p.1 p.2) (u.seal S)
  | [], _ => rfl
  | p :: rest, u => by simp only [List.foldl]; rw [seal_foldl rest, seal_insU]; rfl

/-- **A read of the overlay is the read of the sealed trie**: no premise (`getAt` never reads a
digest). -/
theorem getAtU_seal (k : K) : ∀ (d : Nat) (u : U K V D), U.getAt S k d u = getAt S k d (u.seal S)
  | _, .clean _ => rfl
  | _, .leaf _ => rfl
  | d, .node b rep l r => by
      show _ = getAt S k d (.node _ b rep (l.seal S) (r.seal S))
      simp only [U.getAt, getAt]
      cases diverge S k rep d b with
      | some _ => rfl
      | none =>
          dsimp only
          cases S.bit k b
          · exact getAtU_seal k (b + 1) l
          · exact getAtU_seal k (b + 1) r

/-! ## A removal on the overlay is the removal of the sealed trie (cv 01a15460-e096) -/

omit [DecidableEq K] in
theorem first_seal : ∀ (u : U K V D), (u.seal S).first = u.first
  | .clean _ => rfl
  | .leaf _ => rfl
  | .node .. => rfl

omit [DecidableEq K] in
/-- Sealing an overlay join is the join of the sealed sides: `.clean .empty` is the one overlay that
seals to `.empty`, and `U.first` is `T.first` of the sealed side. -/
theorem seal_joinU (b : Nat) (l r : U K V D) : (joinU b l r).seal S = join S b (l.seal S) (r.seal S) := by
  cases l with
  | clean t =>
      cases t with
      | empty => cases r with
        | clean t' => cases t' <;> rfl
        | leaf _ => rfl
        | node _ _ _ _ => rfl
      | leaf h kvs => cases kvs <;> cases r with
        | clean t' => cases t' <;> rfl
        | leaf _ => rfl
        | node _ _ _ _ => rfl
      | node _ _ _ _ => cases r with
        | clean t' => cases t' <;> rfl
        | leaf _ => rfl
        | node _ _ _ _ => rfl
  | leaf kvs => cases kvs <;> cases r with
      | clean t' => cases t' <;> rfl
      | leaf _ => rfl
      | node _ _ _ _ => rfl
  | node _ _ _ _ => cases r with
      | clean t' => cases t' <;> rfl
      | leaf _ => rfl
      | node _ _ _ _ => rfl

omit [DecidableEq K] in
theorem seal_retainLeafU (q : K → V → Bool) (h : D) (kvs : List (K × V)) (keep : U K V D)
    (hk : keep.seal S = .leaf h kvs) :
    (retainLeafU q keep kvs).seal S = (retainAll S q (.leaf h kvs)).1 := by
  simp only [retainLeafU, retainAll]
  by_cases ha : (kvs.all fun p => q p.1 p.2) = true
  · rw [if_pos ha, if_pos ha]; exact hk
  · rw [if_neg ha, if_neg ha]
    split <;> rfl

omit [DecidableEq K] in
/-- Sealing `retainAtT` of a clean subtree is `retainAt` of it: no premise. -/
theorem seal_retainAtT (q : K → V → Bool) (path : List Bool) :
    ∀ (t : T K V D), (retainAtT S q path t).seal S = retainAt S q path t
  | .empty => rfl
  | .leaf h kvs => seal_retainLeafU S q h kvs (.clean (.leaf h kvs)) rfl
  | .node h b rep l r => by
      simp only [retainAtT, retainAt]
      cases path[b]? with
      | none => rfl
      | some side =>
          cases side
          · rw [seal_joinU, seal_retainAtT q path l]; rfl
          · rw [seal_joinU, seal_retainAtT q path r]; rfl

omit [DecidableEq K] in
/-- **Sealing an overlay removal is the removal of the sealed trie**, for ANY overlay, ANY bit function
and ANY path: no premise (as `seal_insU`). A retract on the rows overlay joins the batch
(`World.uStore`), and the batch sealed once is each touch on the trie in turn (`Admit.rowsRun_eq`). -/
theorem seal_retainAtU (q : K → V → Bool) (path : List Bool) :
    ∀ (u : U K V D), (retainAtU S q path u).seal S = retainAt S q path (u.seal S)
  | .clean t => seal_retainAtT S q path t
  | .leaf kvs => seal_retainLeafU S q (leafHash S (digests S kvs)) kvs (.leaf kvs) rfl
  | .node b rep l r => by
      have hs : (U.node b rep l r).seal S =
          .node (nodeHash S b ((l.seal S).hashOf S) ((r.seal S).hashOf S)) b rep (l.seal S) (r.seal S) := rfl
      rw [hs]
      simp only [retainAtU, retainAt]
      cases path[b]? with
      | none => rfl
      | some side =>
          cases side
          · rw [seal_joinU, seal_retainAtU q path l]
          · rw [seal_joinU, seal_retainAtU q path r]

/-- **The batch is the sequential trie**: `insertAll` (one pass on the overlay, sealed once) is each
key inserted in turn, as a `T` value, cached digests included. No premise. -/
theorem insertAll_eq_foldl (t : T K V D) (kvs : List (K × V)) :
    insertAll S t kvs = kvs.foldl (fun t p => t.insert S p.1 p.2) t :=
  seal_foldl S kvs (.clean t)

end Nanodregg.Kernel.Trie

namespace Nanodregg.Kernel.Trie

variable {K V D : Type} (S : Spec K V D) [DecidableEq K]

/-! ## Soundness of proofs -/

/-- Every cached digest is the digest of what it caches, and every branching bit fits the u16 its
node commits (it lies below `depth`). -/
def WF : T K V D → Prop
  | .empty => True
  | .leaf h kvs => h = leafHash S (digests S kvs)
  | .node h b _ l r => b < S.depth ∧ h = nodeHash S b (l.hashOf S) (r.hashOf S) ∧ WF l ∧ WF r

/-- Each node at depth `d` branches at a bit `b ≥ d`; every key below it agrees with its `rep` on the
skipped bits `[d, b)`; its left keys have bit `b` clear and its right keys have it set; a leaf's
keys are distinct. -/
def Routed : Nat → T K V D → Prop
  | _, .empty => True
  | _, .leaf _ kvs => (kvs.map Prod.fst).Nodup
  | d, .node _ b rep l r => d ≤ b ∧
      (∀ p ∈ l.toList ++ r.toList, ∀ i, d ≤ i → i < b → S.bit p.1 i = S.bit rep i) ∧
      (∀ p ∈ l.toList, S.bit p.1 b = false) ∧ (∀ p ∈ r.toList, S.bit p.1 b = true) ∧
      Routed (b + 1) l ∧ Routed (b + 1) r

/-- Two different byte strings OF `L` with one digest. A collision among SOME two byte strings is a
theorem of every hash into a finite digest type (pigeonhole), so it binds nothing; the soundness
theorems below name the byte strings they compare (`readPres`: what the presented proof hashes and
what the trie hashed along the key's path) and escape only by a collision among those. -/
def CollAmong (L : List ByteArray) : Prop := ∃ a ∈ L, ∃ b ∈ L, a ≠ b ∧ S.hash a = S.hash b

omit [DecidableEq K] in
theorem CollAmong.mono {L L' : List ByteArray} (hsub : ∀ x ∈ L, x ∈ L') :
    CollAmong S L → CollAmong S L'
  | ⟨a, ha, b, hb, hne, h⟩ => ⟨a, hsub a ha, b, hsub b hb, hne, h⟩

omit [DecidableEq K] in
/-- Two different heads with one digest collide among the two lists. -/
theorem CollAmong.heads {x y : ByteArray} {L L' : List ByteArray} (h : S.hash x = S.hash y)
    (hne : x ≠ y) : CollAmong S ((x :: L) ++ (y :: L')) :=
  ⟨x, by simp, y, by simp, hne, h⟩

omit [DecidableEq K] in
/-- A collision among the tails is one among the lists. -/
theorem CollAmong.tails {x y : ByteArray} {L L' : List ByteArray} :
    CollAmong S (L ++ L') → CollAmong S ((x :: L) ++ (y :: L')) :=
  CollAmong.mono S fun z hz => by
    simp only [List.mem_append, List.mem_cons] at hz ⊢
    rcases hz with h | h <;> simp [h]

omit [DecidableEq K] in
theorem tagged_inj {a b : UInt8} {x y : ByteArray} (h : tagged a x = tagged b y) : a = b ∧ x = y := by
  unfold tagged at h
  obtain ⟨h₁, h₂⟩ := bytes_append_inj h rfl
  refine ⟨?_, h₂⟩
  have := congrArg (fun z : ByteArray => z.data.toList) h₁
  simpa using this

/-- **A branching bit's two bytes name it**, below `2 ^ 16`. -/
theorem u16_inj {a b : Nat} (ha : a < 2 ^ 16) (hb : b < 2 ^ 16) (h : u16 a = u16 b) : a = b := by
  unfold u16 at h
  have h1 := congrArg (fun z : ByteArray => z.data.toList) h
  simp at h1
  obtain ⟨e1, e2⟩ := h1
  have f1 := congrArg UInt8.toNat e1
  have f2 := congrArg UInt8.toNat e2
  simp at f1 f2
  omega

omit [DecidableEq K] in
/-- Two node preimages with branching bits below `2 ^ 16` agree on the bit and on the rest. -/
theorem node_bytes {b b' : Nat} {x y x' y' : ByteArray} (hb : b < 2 ^ 16) (hb' : b' < 2 ^ 16)
    (h : u16 b ++ x ++ y = u16 b' ++ x' ++ y') : b = b' ∧ x ++ y = x' ++ y' := by
  rw [ByteArray.append_assoc, ByteArray.append_assoc] at h
  obtain ⟨h1, h2⟩ := bytes_append_inj h rfl
  exact ⟨u16_inj hb hb' h1, h2⟩

theorem find_digests {k : K} :
    ∀ {kvs : List (K × V)}, find k (digests S kvs) = (find k kvs).map S.vdigest
  | [] => rfl
  | p :: rest => by
      simp only [digests, List.map_cons] at *
      rw [find_cons, find_cons]
      split
      · simp
      · exact find_digests

/-- **If `getAt` reads a value, the proof's end holds its digest**, for any tree: `proveAt` follows
the key's bits, as `getAt` does once no skipped bit refuses it. -/
theorem getAt_some_proveAt (k : K) :
    ∀ (d : Nat) (t : T K V D) (v : V), getAt S k d t = some v →
      ∃ kds, (proveAt S k t).term = some kds ∧ find k kds = some (S.vdigest v)
  | _, .empty, _, h => by cases h
  | _, .leaf _ kvs, v, h => ⟨_, rfl, by simp only [getAt] at h; rw [find_digests, h]; rfl⟩
  | d, .node _ b rep l r, v, h => by
      simp only [getAt] at h
      cases hd : diverge S k rep d b with
      | some _ => rw [hd] at h; cases h
      | none =>
          rw [hd] at h
          cases hb : S.bit k b
          · rw [hb] at h; simp only [proveAt, hb]; exact getAt_some_proveAt k (b + 1) l v h
          · rw [hb] at h; simp only [proveAt, hb]; exact getAt_some_proveAt k (b + 1) r v h

/-- A key no entry of the trie has: the proof's end does not hold it. -/
theorem proveAt_absent (k : K) : ∀ (t : T K V D), (∀ p ∈ t.toList, p.1 ≠ k) →
    (match (proveAt S k t).term with
      | none => none
      | some kds => find k kds) = none
  | .empty, _ => rfl
  | .leaf _ kvs, h => by
      simp only [proveAt]; rw [find_digests, find_absent (l := kvs) h]; rfl
  | .node _ b _ l r, h => by
      cases hb : S.bit k b
      · simp only [proveAt, hb]
        exact proveAt_absent k l fun p hp => h p (List.mem_append_left _ hp)
      · simp only [proveAt, hb]
        exact proveAt_absent k r fun p hp => h p (List.mem_append_right _ hp)

/-- **On a routed trie, what a proof ends at says what the trie holds at the key.** -/
theorem getAt_proveAt (k : K) :
    ∀ (d : Nat) (t : T K V D), Routed S d t → (getAt S k d t).map S.vdigest =
      match (proveAt S k t).term with
      | none => none
      | some kds => find k kds
  | _, .empty, _ => rfl
  | _, .leaf _ kvs, _ => by simp [getAt, proveAt, find_digests]
  | d, .node h b rep l r, hr => by
      obtain ⟨_, hag, _, _, hl, hr'⟩ := hr
      cases hd : diverge S k rep d b with
      | some e =>
          obtain ⟨hde, heb, hne, _⟩ := (diverge_some S).mp hd
          have hg : getAt S k d (.node h b rep l r) = none := by simp [getAt, hd]
          rw [hg, proveAt_absent S k _ fun p hp hpk => hne (by rw [← hpk]; exact hag p hp e hde heb)]
          rfl
      | none =>
          cases hb : S.bit k b
          · simp only [getAt, proveAt, hd, hb]; exact getAt_proveAt k (b + 1) l hl
          · simp only [getAt, proveAt, hd, hb]; exact getAt_proveAt k (b + 1) r hr'

/-- The converse of `getAt_some_proveAt`, on a routed trie: a proof's end that holds the key's
digest means `getAt` reads a value with that digest. -/
theorem proveAt_some_getAt (k : K) :
    ∀ (d : Nat) (t : T K V D) (kds : List (K × D)) (dig : D), Routed S d t →
      (proveAt S k t).term = some kds → find k kds = some dig →
      ∃ v, getAt S k d t = some v ∧ S.vdigest v = dig := by
  intro d t kds dig hr ht hf
  have := getAt_proveAt S k d t hr
  rw [ht] at this; simp only at this; rw [hf] at this
  cases hg : getAt S k d t with
  | none => rw [hg] at this; cases this
  | some v => rw [hg] at this; exact ⟨v, rfl, by simpa using this⟩

variable (hL : ∀ x y, leafBody S x = leafBody S y → x = y)
  (hN : ∀ a b c e, S.dbytes a ++ S.dbytes b = S.dbytes c ++ S.dbytes e → a = c ∧ b = e)
include hL hN

omit [DecidableEq K] in
/-- **A path that recomputes the root ends where the trie's path for the key ends**, or two of the
byte strings compared collide: one the path hashes (`climbPres`) against one the trie hashed along
the key's path (`pathPres`). Its bits must lie below `depth` (`ascends`), as a well-formed node's
do: two bits are told apart by their u16 only below `2 ^ 16`. -/
theorem climb_sound (k : K) :
    ∀ (d : Nat) (t : T K V D) (sibs : List (Nat × D)) (term : Option (List (K × D))),
      WF S t → ascends S d sibs = true → climb S k sibs (termHash S term) = t.hashOf S →
      term = (proveAt S k t).term ∨ CollAmong S (climbPres S k sibs term ++ pathPres S k t)
  | d, .empty, [], none, _, _, _ => .inl rfl
  | d, .empty, [], some kds, _, _, h => by
      simp only [climb, termHash, T.hashOf, leafHash, emptyHash] at h
      exact .inr (CollAmong.heads S h fun he => absurd (tagged_inj he).1 (by decide))
  | d, .empty, (b', s) :: rest, term, _, _, h => by
      simp only [climb, T.hashOf, emptyHash] at h
      cases hk : S.bit k b' <;> simp only [hk] at h <;>
      · simp only [climbPres, pathPres, hk]
        exact .inr (CollAmong.heads S h fun he => absurd (tagged_inj he).1 (by decide))
  | d, .leaf hv kvs, [], none, hw, _, h => by
      simp only [climb, termHash, T.hashOf, WF, emptyHash] at h hw; rw [hw] at h
      exact .inr (CollAmong.heads S h fun he => absurd (tagged_inj he).1 (by decide))
  | d, .leaf hv kvs, [], some kds, hw, _, h => by
      simp only [climb, termHash, T.hashOf, WF] at h hw; rw [hw] at h
      by_cases he : termPre S (some kds) = termPre S (some (digests S kvs))
      · exact .inl (by simp [proveAt, hL _ _ (tagged_inj he).2])
      · exact .inr (CollAmong.heads S h he)
  | d, .leaf hv kvs, (b', s) :: rest, term, hw, _, h => by
      simp only [climb, T.hashOf, WF] at h hw; rw [hw] at h
      cases hk : S.bit k b' <;> simp only [hk] at h <;>
      · simp only [climbPres, pathPres, hk]
        exact .inr (CollAmong.heads S h fun he => absurd (tagged_inj he).1 (by decide))
  | d, .node hv b rep l r, [], none, hw, _, h => by
      simp only [climb, termHash, T.hashOf, WF, emptyHash] at h hw; rw [hw.2.1] at h
      exact .inr (CollAmong.heads S h fun he => absurd (tagged_inj he).1 (by decide))
  | d, .node hv b rep l r, [], some kds, hw, _, h => by
      simp only [climb, termHash, T.hashOf, WF, leafHash] at h hw; rw [hw.2.1] at h
      exact .inr (CollAmong.heads S h fun he => absurd (tagged_inj he).1 (by decide))
  | d, .node hv b rep l r, (b', s) :: rest, term, hw, ha, h => by
      obtain ⟨hb, hh, hwl, hwr⟩ := hw
      simp only [ascends, Bool.and_eq_true, decide_eq_true_eq] at ha
      obtain ⟨⟨_, hb'⟩, ha⟩ := ha
      have l1 : b < 2 ^ 16 := Nat.lt_trans hb S.depth_lt
      have l2 : b' < 2 ^ 16 := Nat.lt_trans hb' S.depth_lt
      simp only [climb, T.hashOf] at h; rw [hh] at h
      cases hk : S.bit k b'
      · simp only [hk] at h
        by_cases hx : nodePre S b' (climb S k rest (termHash S term)) s = nodePre S b (l.hashOf S) (r.hashOf S)
        · obtain ⟨rfl, hxy⟩ := node_bytes l2 l1 (tagged_inj hx).2
          simp only [proveAt, climbPres, pathPres, hk]
          rcases climb_sound k (b' + 1) l rest term hwl ha (hN _ _ _ _ hxy).1 with he | c
          · exact .inl he
          · exact .inr (CollAmong.tails S c)
        · simp only [climbPres, pathPres, hk]
          exact .inr (CollAmong.heads S h hx)
      · simp only [hk] at h
        by_cases hx : nodePre S b' s (climb S k rest (termHash S term)) = nodePre S b (l.hashOf S) (r.hashOf S)
        · obtain ⟨rfl, hxy⟩ := node_bytes l2 l1 (tagged_inj hx).2
          simp only [proveAt, climbPres, pathPres, hk]
          rcases climb_sound k (b' + 1) r rest term hwr ha (hN _ _ _ _ hxy).2 with he | c
          · exact .inl he
          · exact .inr (CollAmong.tails S c)
        · simp only [climbPres, pathPres, hk]
          exact .inr (CollAmong.heads S h hx)

variable [DecidableEq D]

/-- **Inclusion is sound.** A proof that verifies against a well-formed, routed trie's root shows
the digest of the value the trie holds at the key, or two of the byte strings the read compares
collide (`readPres`: the proof's against the trie's path). -/
theorem inclusion_sound {t : T K V D} {k : K} {dig : D} {p : Proof K D} (hw : WF S t)
    (hr : Routed S 0 t) (hv : verifyInclusion S (t.hashOf S) k dig p = true) :
    (∃ v, t.get S k = some v ∧ S.vdigest v = dig) ∨ CollAmong S (readPres S k p t) := by
  unfold verifyInclusion at hv
  cases ht : p.term with
  | none => simp [ht] at hv
  | some kds =>
      simp only [ht, Bool.and_eq_true, decide_eq_true_eq] at hv
      rcases climb_sound S hL hN k 0 t p.sibs p.term hw hv.1 (by rw [ht]; exact hv.2.2) with he | c
      · rw [ht] at he
        exact .inl (proveAt_some_getAt S k 0 t kds dig hr he.symm hv.2.1)
      · exact .inr c

/-- **Exclusion is sound.** A proof of absence that verifies against a well-formed trie's root
means the trie holds nothing at the key, or two of the byte strings the read compares collide. -/
theorem exclusion_sound {t : T K V D} {k : K} {p : Proof K D} (hw : WF S t)
    (hv : verifyExclusion S (t.hashOf S) k p = true) : t.get S k = none ∨ CollAmong S (readPres S k p t) := by
  unfold verifyExclusion at hv
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hv
  rcases climb_sound S hL hN k 0 t p.sibs p.term hw hv.1.1 hv.2 with he | c
  · left
    cases hg : t.get S k with
    | none => rfl
    | some v =>
        obtain ⟨kds, hk, hf⟩ := getAt_some_proveAt S k 0 t v hg
        have hn := hv.1.2
        rw [he, hk] at hn
        simp [hf] at hn
  · exact .inr c

omit hL hN

/-! ## Every trie the operations build is well formed, shallow, and proves what it holds -/

/-- Every node at depth `d` branches at a bit in `[d, depth)`: a proof path's bits ascend below
`depth`. -/
def Shallow : Nat → T K V D → Prop
  | _, .empty => True
  | _, .leaf _ _ => True
  | d, .node _ b _ l r => d ≤ b ∧ b < S.depth ∧ Shallow (b + 1) l ∧ Shallow (b + 1) r

omit [DecidableEq K] [DecidableEq D] in
theorem wf_mkLeaf (kvs : List (K × V)) : WF S (mkLeaf S kvs) := rfl

omit [DecidableEq K] [DecidableEq D] in
theorem wf_mkNode {b : Nat} {rep : K} {l r : T K V D} (hb : b < S.depth) (hl : WF S l) (hr : WF S r) :
    WF S (mkNode S b rep l r) :=
  ⟨hb, rfl, hl, hr⟩

omit [DecidableEq K] [DecidableEq D] in
theorem wf_build : ∀ (f d : Nat) (kvs : List (K × V)), WF S (build S f d kvs)
  | _, _, [] => by simp [build, WF]
  | f, _, [x] => by cases f <;> exact wf_mkLeaf S _
  | 0, _, a :: b :: rest => wf_mkLeaf S _
  | f + 1, d, a :: b :: rest => by
      simp only [build]
      cases hs : splitBit S d (a :: b :: rest) with
      | none => exact wf_mkLeaf S _
      | some c =>
          exact wf_mkNode S (splitBit_bounds S hs).2 (wf_build f (c + 1) _) (wf_build f (c + 1) _)

omit [DecidableEq K] [DecidableEq D] in
theorem shallow_build' : ∀ (f d : Nat) (kvs : List (K × V)), Shallow S d (build S f d kvs)
  | _, _, [] => by simp [build, Shallow]
  | f, _, [x] => by cases f <;> simp [build, mkLeaf, Shallow]
  | 0, _, a :: b :: rest => by simp [build, mkLeaf, Shallow]
  | f + 1, d, a :: b :: rest => by
      simp only [build]
      cases hs : splitBit S d (a :: b :: rest) with
      | none => simp [mkLeaf, Shallow]
      | some c =>
          have hb := splitBit_bounds S hs
          simp only [mkNode, Shallow]
          exact ⟨hb.1, hb.2, shallow_build' f (c + 1) _, shallow_build' f (c + 1) _⟩

omit [DecidableEq K] [DecidableEq D] in
theorem shallow_build : ∀ (f d : Nat) (kvs : List (K × V)), f ≤ S.depth - d → Shallow S d (build S f d kvs) :=
  fun f d kvs _ => shallow_build' S f d kvs

omit [DecidableEq D] in
/-- **`insAt` is `insAtRebuild`, digests included, on a well-formed trie** (cv 01a15107-2263): the
split leaf it keeps carries the digest `insAtRebuild` recomputes, so the insert reaches the very
same trie, and no root, proof or head moves; it only skips that one hash. -/
private theorem insAt_eq_rebuild (k : K) (v : V) : ∀ (d : Nat) (t : T K V D), WF S t →
    insAt S k v d t = insAtRebuild S k v d t
  | _, .empty, _ => rfl
  | d, .leaf h kvs, hw => by
      simp only [insAt, insAtRebuild]
      split
      · rfl
      · match kvs with
        | [p] =>
            simp only
            cases hc : diverge S k p.1 d S.depth with
            | none => rfl
            | some c =>
                simp only
                rw [build_pair S d c p k v hc]
                have hl : (T.leaf h [p] : T K V D) = mkLeaf S [p] := by
                  simp only [WF] at hw; rw [hw]; rfl
                cases hb : S.bit k c <;> simp only [hl]
        | [] => rfl
        | _ :: _ :: _ => rfl
  | d, .node h b rep l r, hw => by
      obtain ⟨-, -, hl, hr⟩ := hw
      simp only [insAt, insAtRebuild]
      cases diverge S k rep d b with
      | some c => rfl
      | none =>
          simp only
          cases S.bit k b
          · rw [insAt_eq_rebuild k v (b + 1) l hl]
          · rw [insAt_eq_rebuild k v (b + 1) r hr]

omit [DecidableEq D] in
/-- **The split leaf is kept, digest and all** (cv 01a15107-2263): a new key leaving a one-entry leaf
gets one node over THAT leaf, whatever digest it carries; nothing re-hashes it. So `insAt_eq_rebuild`'s
`WF` is load-bearing: a leaf carrying a digest other than `leafHash` of its entries keeps it, where
`insAtRebuild` recomputed it. -/
theorem insAt_split_keeps (k : K) (v : V) (d c : Nat) (h : D) (p : K × V)
    (hc : diverge S k p.1 d S.depth = some c) :
    insAt S k v d (.leaf h [p]) =
      match S.bit k c with
      | true => mkNode S c p.1 (.leaf h [p]) (mkLeaf S [(k, v)])
      | false => mkNode S c k (mkLeaf S [(k, v)]) (.leaf h [p]) := by
  have hk : p.1 ≠ k := fun he => ((diverge_some S).mp hc).2.2.1 (by rw [he])
  simp only [insAt, List.any_cons, List.any_nil, Bool.or_false, decide_eq_true_eq, hk, if_false, hc]
  cases S.bit k c <;> rfl

omit [DecidableEq D] in
/-- `insAt_eq_rebuild`'s `WF` is load-bearing: a split leaf carrying a digest other than its entries'
`leafHash` keeps it under `insAt`, where `insAtRebuild` recomputed it. -/
private theorem insAt_ne_rebuild_of_stale (k : K) (v : V) (d c : Nat) (h : D) (p : K × V)
    (hh : h ≠ leafHash S (digests S [p])) (hc : diverge S k p.1 d S.depth = some c) :
    insAt S k v d (.leaf h [p]) ≠ insAtRebuild S k v d (.leaf h [p]) := by
  have hk : p.1 ≠ k := fun he => ((diverge_some S).mp hc).2.2.1 (by rw [he])
  rw [insAt_split_keeps S k v d c h p hc]
  simp only [insAtRebuild, List.any_cons, List.any_nil, Bool.or_false, decide_eq_true_eq, hk, if_false]
  rw [build_pair S d c p k v hc]
  cases S.bit k c <;> simp [mkNode, mkLeaf, hh]

omit [DecidableEq D] in
private theorem wf_insAtRebuild (k : K) (v : V) : ∀ (d : Nat) (t : T K V D), WF S t → WF S (insAtRebuild S k v d t)
  | _, .empty, _ => wf_mkLeaf S _
  | d, .leaf _ kvs, _ => by
      simp only [insAtRebuild]; split
      · exact wf_mkLeaf S _
      · exact wf_build S _ _ _
  | d, .node h b rep l r, hw => by
      obtain ⟨hb, hh, hl, hr⟩ := hw
      simp only [insAtRebuild]
      cases hdk : diverge S k rep d b with
      | some c =>
          dsimp only
          have hcb := ((diverge_some S).mp hdk).2.1
          cases S.bit k c
          · exact wf_mkNode S (by omega) (wf_mkLeaf S _) ⟨hb, hh, hl, hr⟩
          · exact wf_mkNode S (by omega) ⟨hb, hh, hl, hr⟩ (wf_mkLeaf S _)
      | none =>
          cases S.bit k b
          · exact wf_mkNode S hb (wf_insAtRebuild k v (b + 1) l hl) hr
          · exact wf_mkNode S hb hl (wf_insAtRebuild k v (b + 1) r hr)

omit [DecidableEq D] in
theorem wf_insAt (k : K) (v : V) : ∀ (d : Nat) (t : T K V D), WF S t → WF S (insAt S k v d t) :=
  fun d t h => (insAt_eq_rebuild S k v d t h) ▸ wf_insAtRebuild S k v d t h

omit [DecidableEq D] in
private theorem shallow_insAtRebuild (k : K) (v : V) :
    ∀ (d : Nat) (t : T K V D), Shallow S d t → Shallow S d (insAtRebuild S k v d t)
  | _, .empty, _ => by simp [insAtRebuild, mkLeaf, Shallow]
  | d, .leaf _ kvs, _ => by
      simp only [insAtRebuild]; split
      · simp [mkLeaf, Shallow]
      · exact shallow_build' S _ _ _
  | d, .node h b rep l r, hs => by
      obtain ⟨hdb, hb, hl, hr⟩ := hs
      simp only [insAtRebuild]
      cases hdk : diverge S k rep d b with
      | some c =>
          dsimp only
          obtain ⟨hdc, hcb, _, _⟩ := (diverge_some S).mp hdk
          cases S.bit k c
          · simp only [mkNode, mkLeaf, Shallow]
            exact ⟨hdc, by omega, trivial, by omega, hb, hl, hr⟩
          · simp only [mkNode, mkLeaf, Shallow]
            exact ⟨hdc, by omega, ⟨by omega, hb, hl, hr⟩, trivial⟩
      | none =>
          cases S.bit k b
          · exact ⟨hdb, hb, shallow_insAtRebuild k v (b + 1) l hl, hr⟩
          · exact ⟨hdb, hb, hl, shallow_insAtRebuild k v (b + 1) r hr⟩

omit [DecidableEq K] [DecidableEq D] in
theorem shallow_hashEq : ∀ (d : Nat) (t u : T K V D), HashEq t u → Shallow S d u → Shallow S d t
  | _, .empty, .empty, _, _ => trivial
  | _, .leaf _ _, .leaf _ _, _, _ => trivial
  | d, .node _ b _ l r, .node _ b' _ l' r', h, hs => by
      obtain ⟨rfl, -, hl, hr⟩ := h
      obtain ⟨h1, h2, h3, h4⟩ := hs
      exact ⟨h1, h2, shallow_hashEq (b + 1) l l' hl h3, shallow_hashEq (b + 1) r r' hr h4⟩
  | _, .empty, .leaf .., h, _ | _, .empty, .node .., h, _ | _, .leaf .., .empty, h, _
  | _, .leaf .., .node .., h, _ | _, .node .., .empty, h, _ | _, .node .., .leaf .., h, _ => by
      simp [HashEq] at h

omit [DecidableEq D] in
theorem shallow_insAt (k : K) (v : V) :
    ∀ (d : Nat) (t : T K V D), Shallow S d t → Shallow S d (insAt S k v d t) :=
  fun d t h => shallow_hashEq S d _ _ (hashEq_insAt S k v d t) (shallow_insAtRebuild S k v d t h)

omit [DecidableEq D] in
theorem wf_insert {t : T K V D} (k : K) (v : V) (h : WF S t) : WF S (t.insert S k v) :=
  wf_insAt S k v 0 t h

omit [DecidableEq D] in
theorem shallow_insert {t : T K V D} (k : K) (v : V) (h : Shallow S 0 t) :
    Shallow S 0 (t.insert S k v) :=
  shallow_insAt S k v 0 t h

omit [DecidableEq K] [DecidableEq D] in
theorem climb_proveAt (k : K) : ∀ (t : T K V D), WF S t →
    climb S k (proveAt S k t).sibs (termHash S (proveAt S k t).term) = t.hashOf S
  | .empty, _ => rfl
  | .leaf _ kvs, hw => by simp only [proveAt, climb, termHash, T.hashOf]; exact hw.symm
  | .node _ b _ l r, hw => by
      simp only [proveAt, T.hashOf]
      cases hb : S.bit k b
      · simp only [climb, hb]; rw [climb_proveAt k l hw.2.2.1]; exact hw.2.1.symm
      · simp only [climb, hb]; rw [climb_proveAt k r hw.2.2.2]; exact hw.2.1.symm

omit [DecidableEq K] [DecidableEq D] in
/-- A shallow trie's proof paths pass `verify`'s bound: their bits ascend below `depth`. -/
theorem ascends_proveAt (k : K) : ∀ (d : Nat) (t : T K V D), Shallow S d t →
    ascends S d (proveAt S k t).sibs = true
  | _, .empty, _ => rfl
  | _, .leaf _ _, _ => rfl
  | d, .node _ b _ l r, hs => by
      obtain ⟨hdb, hb, hl, hr⟩ := hs
      cases hk : S.bit k b
      · simp only [proveAt, hk, ascends, Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨⟨hdb, hb⟩, ascends_proveAt k (b + 1) l hl⟩
      · simp only [proveAt, hk, ascends, Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨⟨hdb, hb⟩, ascends_proveAt k (b + 1) r hr⟩

omit [DecidableEq K] [DecidableEq D] in
theorem ascends_length : ∀ (d : Nat) (sibs : List (Nat × D)), ascends S d sibs = true →
    sibs.length ≤ S.depth - d
  | _, [], _ => by simp
  | d, (b, _) :: rest, h => by
      simp only [ascends, Bool.and_eq_true, decide_eq_true_eq] at h
      have := ascends_length (b + 1) rest h.2
      simp only [List.length_cons]; omega

omit [DecidableEq K] [DecidableEq D] in
theorem proveAt_length (k : K) : ∀ (d : Nat) (t : T K V D), Shallow S d t →
    (proveAt S k t).sibs.length ≤ S.depth - d :=
  fun d t hs => ascends_length S d _ (ascends_proveAt S k d t hs)

/-- **A trie proves what it holds.** -/
theorem prove_includes {t : T K V D} {k : K} {v : V} (hw : WF S t) (hs : Shallow S 0 t)
    (hg : t.get S k = some v) : verifyInclusion S (t.hashOf S) k (S.vdigest v) (t.prove S k) = true := by
  obtain ⟨kds, hk, hf⟩ := getAt_some_proveAt S k 0 t v hg
  have hc := climb_proveAt S k t hw
  have ha := ascends_proveAt S k 0 t hs
  unfold T.prove verifyInclusion
  rw [hk] at hc ⊢
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨ha, hf, hc⟩

/-- **A routed trie proves what it does not hold.** (Routed: on a malformed tree the key's bits
could reach a leaf that holds it while `getAt` refuses it on a skipped bit.) -/
theorem prove_excludes {t : T K V D} {k : K} (hw : WF S t) (hr : Routed S 0 t) (hs : Shallow S 0 t)
    (hg : t.get S k = none) : verifyExclusion S (t.hashOf S) k (t.prove S k) = true := by
  have hp := getAt_proveAt S k 0 t hr
  have hc := climb_proveAt S k t hw
  have ha := ascends_proveAt S k 0 t hs
  unfold T.get at hg; unfold T.prove verifyExclusion
  rw [hg] at hp
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨ha, ?_⟩, hc⟩
  cases ht : (proveAt S k t).term with
  | none => rfl
  | some kds => simp only [ht] at hp; simp [← hp]

/-! ## Routing: every key sits where its bits send it, once -/

omit [DecidableEq K] [DecidableEq D] in
theorem toList_build : ∀ (f d : Nat) (kvs : List (K × V)), (build S f d kvs).toList.Perm kvs
  | _, _, [] => by simp [build, T.toList]
  | f, _, [x] => by cases f <;> simp [build, mkLeaf, T.toList]
  | 0, _, a :: b :: rest => by simp [build, mkLeaf, T.toList]
  | f + 1, d, a :: b :: rest => by
      simp only [build]
      cases hs : splitBit S d (a :: b :: rest) with
      | none => simp [mkLeaf, T.toList]
      | some c =>
          simp only [mkNode, T.toList]
          refine ((toList_build f (c + 1) _).append (toList_build f (c + 1) _)).trans ?_
          have := List.filter_append_perm (fun p : K × V => !S.bit p.1 c) (a :: b :: rest)
          simpa [Bool.not_not] using this

omit [DecidableEq K] [DecidableEq D] in
theorem routed_build : ∀ (f d : Nat) (kvs : List (K × V)), (kvs.map Prod.fst).Nodup →
    Routed S d (build S f d kvs)
  | _, _, [], _ => by simp [build, Routed]
  | f, _, [x], _ => by cases f <;> simp [build, mkLeaf, Routed]
  | 0, _, a :: b :: rest, h => by simpa [build, mkLeaf, Routed] using h
  | f + 1, d, a :: b :: rest, h => by
      cases hs : splitBit S d (a :: b :: rest) with
      | none => simpa [build, hs, mkLeaf, Routed] using h
      | some c =>
          obtain ⟨rep, ⟨x, hx, hxr⟩, hb⟩ := build_node_rep S f d c a (b :: rest) hs
          rw [hb]
          have hag := splitBit_agree S hs
          have hbd := splitBit_bounds S hs
          simp only [mkNode, Routed]
          refine ⟨hbd.1, fun p hp i hi hic => ?_, fun p hp => ?_, fun p hp => ?_,
            routed_build f (c + 1) _ ?_, routed_build f (c + 1) _ ?_⟩
          · have hp' : p ∈ a :: b :: rest := by
              rcases List.mem_append.mp hp with hp | hp
              · exact (List.mem_filter.mp ((toList_build S f (c + 1) _).mem_iff.mp hp)).1
              · exact (List.mem_filter.mp ((toList_build S f (c + 1) _).mem_iff.mp hp)).1
            rw [← hxr, hag p hp' i hi hic, hag x hx i hi hic]
          · have := (toList_build S f (c + 1) _).mem_iff.mp hp; simp at this; simpa using this.2
          · have := (toList_build S f (c + 1) _).mem_iff.mp hp; simp at this; exact this.2
          · exact (h.sublist (List.Sublist.map _ List.filter_sublist))
          · exact (h.sublist (List.Sublist.map _ List.filter_sublist))

omit [DecidableEq D] in
/-- What a routed trie lists is what it holds. -/
theorem mem_toList : ∀ (d : Nat) (t : T K V D), Routed S d t →
    ∀ (k : K) (v : V), (k, v) ∈ t.toList ↔ getAt S k d t = some v
  | _, .empty, _, k, v => by simp [T.toList, getAt]
  | _, .leaf _ kvs, h, k, v => by
      simp only [T.toList, getAt, Routed] at h ⊢
      induction kvs with
      | nil => simp [find_nil]
      | cons p rest ih =>
          simp only [List.map_cons, List.nodup_cons] at h
          rw [find_cons, List.mem_cons]
          by_cases hp : p.1 = k
          · subst hp
            have hn : ∀ x, (p.1, x) ∉ rest := fun x hx => h.1 (List.mem_map.mpr ⟨_, hx, rfl⟩)
            rw [if_pos rfl]
            constructor
            · rintro (he | hm)
              · rw [← he]
              · exact absurd hm (hn v)
            · intro he; left; obtain ⟨a, b⟩ := p; simp only [Option.some.injEq] at he; rw [he]
          · rw [if_neg hp, ← ih h.2]
            constructor
            · rintro (he | hm)
              · exact absurd (by rw [← he]) hp
              · exact hm
            · exact .inr
  | d, .node _ b rep l r, h, k, v => by
      obtain ⟨_, hag, hlb, hrb, hl, hr⟩ := h
      cases hd : diverge S k rep d b with
      | some e =>
          obtain ⟨hde, heb, hne, _⟩ := (diverge_some S).mp hd
          simp only [getAt, hd]
          constructor
          · intro hm; exact absurd (hag _ hm e hde heb) hne
          · intro h; simp at h
      | none =>
          simp only [T.toList, getAt, hd, List.mem_append]
          cases hb : S.bit k b
          · rw [← mem_toList (b + 1) l hl k v]
            constructor
            · rintro (hm | hm)
              · exact hm
              · have := hrb _ hm; simp [hb] at this
            · exact .inl
          · rw [← mem_toList (b + 1) r hr k v]
            constructor
            · rintro (hm | hm)
              · have := hlb _ hm; simp [hb] at this
              · exact hm
            · exact .inr

omit [DecidableEq D] in
/-- What `getAt` reads, any tree lists. -/
theorem mem_of_getAt : ∀ (d : Nat) (t : T K V D) (k : K) (v : V),
    getAt S k d t = some v → (k, v) ∈ t.toList
  | _, .empty, _, _, h => by cases h
  | _, .leaf _ kvs, _, _, h => find_mem h
  | d, .node _ b rep l r, k, v, h => by
      simp only [getAt] at h
      cases hd : diverge S k rep d b with
      | some _ => rw [hd] at h; cases h
      | none =>
          rw [hd] at h
          cases hb : S.bit k b
          · rw [hb] at h; exact List.mem_append_left _ (mem_of_getAt (b + 1) l k v h)
          · rw [hb] at h; exact List.mem_append_right _ (mem_of_getAt (b + 1) r k v h)

omit [DecidableEq D] in
private theorem keys_insAtRebuild (k : K) (v : V) : ∀ (d : Nat) (t : T K V D) (p : K × V),
    p ∈ (insAtRebuild S k v d t).toList → p ∈ t.toList ∨ p = (k, v)
  | _, .empty, p, h => by simp [insAtRebuild, mkLeaf, T.toList] at h; exact .inr h
  | d, .leaf _ kvs, p, h => by
      simp only [insAtRebuild] at h
      split at h
      · simp only [mkLeaf, T.toList, List.mem_map] at h
        obtain ⟨q, hq, he⟩ := h
        by_cases hk : q.1 = k
        · simp [hk] at he; exact .inr he.symm
        · simp [hk] at he; subst he; exact .inl hq
      · have := (toList_build S _ _ _).mem_iff.mp h
        simp only [List.mem_append, List.mem_singleton] at this
        exact this
  | d, .node h b rep l r, p, hp => by
      simp only [insAtRebuild] at hp
      cases hdk : diverge S k rep d b with
      | some c =>
          rw [hdk] at hp; dsimp only at hp
          cases hkc : S.bit k c
          · rw [hkc] at hp
            simp only [mkNode, mkLeaf, T.toList, List.mem_append, List.mem_singleton] at hp ⊢
            rcases hp with hp | hp | hp
            · exact .inr hp
            · exact .inl (.inl hp)
            · exact .inl (.inr hp)
          · rw [hkc] at hp
            simp only [mkNode, mkLeaf, T.toList, List.mem_append, List.mem_singleton] at hp ⊢
            rcases hp with (hp | hp) | hp
            · exact .inl (.inl hp)
            · exact .inl (.inr hp)
            · exact .inr hp
      | none =>
          rw [hdk] at hp
          cases hb : S.bit k b
          · rw [hb] at hp
            simp only [mkNode, T.toList, List.mem_append] at hp ⊢
            rcases hp with hp | hp
            · rcases keys_insAtRebuild k v (b + 1) l p hp with hp | hp
              · exact .inl (.inl hp)
              · exact .inr hp
            · exact .inl (.inr hp)
          · rw [hb] at hp
            simp only [mkNode, T.toList, List.mem_append] at hp ⊢
            rcases hp with hp | hp
            · exact .inl (.inl hp)
            · rcases keys_insAtRebuild k v (b + 1) r p hp with hp | hp
              · exact .inl (.inr hp)
              · exact .inr hp

omit [DecidableEq D] in
theorem keys_insAt (k : K) (v : V) : ∀ (d : Nat) (t : T K V D) (p : K × V),
    p ∈ (insAt S k v d t).toList → p ∈ t.toList ∨ p = (k, v) :=
  fun d t p h => keys_insAtRebuild S k v d t p (toList_hashEq _ _ (hashEq_insAt S k v d t) ▸ h)

omit [DecidableEq D] in
theorem map_fst_replace {k : K} {v : V} :
    ∀ (l : List (K × V)), (l.map fun p => if p.1 = k then (k, v) else p).map Prod.fst = l.map Prod.fst
  | [] => rfl
  | p :: rest => by
      simp only [List.map_cons, map_fst_replace rest]
      by_cases h : p.1 = k <;> simp [h]

omit [DecidableEq D] in
private theorem routed_insAtRebuild (k : K) (v : V) : ∀ (d : Nat) (t : T K V D), Routed S d t →
    Routed S d (insAtRebuild S k v d t)
  | _, .empty, _ => by simp [insAtRebuild, mkLeaf, Routed]
  | d, .leaf _ kvs, h => by
      simp only [insAtRebuild]
      split
      · simp only [mkLeaf, Routed] at h ⊢; rw [map_fst_replace]; exact h
      · rename_i hany
        apply routed_build
        simp only [Routed] at h
        rw [List.map_append, List.nodup_append]
        refine ⟨h, by simp, ?_⟩
        intro a ha b hb; simp at hb; subst hb
        intro he; subst he
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ha
        exact hany (List.any_eq_true.mpr ⟨q, hq, by simp⟩)
  | d, .node h b rep l r, hr => by
      obtain ⟨hdb, hag, hlb, hrb, hl, hrr⟩ := hr
      simp only [insAtRebuild]
      cases hdk : diverge S k rep d b with
      | some c =>
          dsimp only
          obtain ⟨hdc, hcb, hkc, hpre⟩ := (diverge_some S).mp hdk
          have hrc := bool_ne (Ne.symm hkc)
          have hold : Routed S (c + 1) (T.node h b rep l r) :=
            ⟨by omega, fun p hp i hi hib => hag p hp i (by omega) hib, hlb, hrb, hl, hrr⟩
          have hleaf : Routed S (c + 1) (mkLeaf S [(k, v)] : T K V D) := by simp [mkLeaf, Routed]
          have hc : ∀ p ∈ (T.node h b rep l r).toList, S.bit p.1 c = S.bit rep c :=
            fun p hp => hag p hp c hdc hcb
          cases hkb : S.bit k c
          · refine ⟨hdc, fun p hp i hi hic => ?_, fun p hp => ?_, fun p hp => ?_, hleaf, hold⟩
            · rcases List.mem_append.mp hp with hp | hp
              · rw [List.mem_singleton.mp hp]
              · rw [hag p hp i hi (by omega), hpre i hi hic]
            · rw [List.mem_singleton.mp hp]; exact hkb
            · rw [hc p hp, hrc, hkb]; rfl
          · refine ⟨hdc, fun p hp i hi hic => ?_, fun p hp => ?_, fun p hp => ?_, hold, hleaf⟩
            · rcases List.mem_append.mp hp with hp | hp
              · exact hag p hp i hi (by omega)
              · rw [List.mem_singleton.mp hp]; exact hpre i hi hic
            · rw [hc p hp, hrc, hkb]; rfl
            · rw [List.mem_singleton.mp hp]; exact hkb
      | none =>
          have hagk := (diverge_none S).mp hdk
          cases hkb : S.bit k b
          · have hrep : ∀ i, d ≤ i → i < b →
                S.bit (if precedes S k rep (b + 1) then k else rep) i = S.bit rep i := by
              intro i hi hib; split
              · exact hagk i hi hib
              · rfl
            refine ⟨hdb, fun p hp i hi hib => ?_, fun p hp => ?_, hrb, routed_insAtRebuild k v (b + 1) l hl, hrr⟩
            · rw [hrep i hi hib]
              rcases List.mem_append.mp hp with hp | hp
              · rcases keys_insAtRebuild S k v (b + 1) l p hp with hp | rfl
                · exact hag p (List.mem_append_left _ hp) i hi hib
                · exact hagk i hi hib
              · exact hag p (List.mem_append_right _ hp) i hi hib
            · rcases keys_insAtRebuild S k v (b + 1) l p hp with hp | rfl
              · exact hlb p hp
              · exact hkb
          · refine ⟨hdb, fun p hp i hi hib => ?_, hlb, fun p hp => ?_, hl, routed_insAtRebuild k v (b + 1) r hrr⟩
            · rcases List.mem_append.mp hp with hp | hp
              · exact hag p (List.mem_append_left _ hp) i hi hib
              · rcases keys_insAtRebuild S k v (b + 1) r p hp with hp | rfl
                · exact hag p (List.mem_append_right _ hp) i hi hib
                · exact hagk i hi hib
            · rcases keys_insAtRebuild S k v (b + 1) r p hp with hp | rfl
              · exact hrb p hp
              · exact hkb

omit [DecidableEq K] [DecidableEq D] in
theorem routed_hashEq : ∀ (d : Nat) (t u : T K V D), HashEq t u → Routed S d u → Routed S d t
  | _, .empty, .empty, _, _ => trivial
  | _, .leaf _ _, .leaf _ _, h, hr => by simp only [HashEq] at h; subst h; exact hr
  | d, .node _ b rep l r, .node _ b' rep' l' r', h, hr => by
      obtain ⟨rfl, rfl, hl, hr'⟩ := h
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hr
      rw [← toList_hashEq l l' hl, ← toList_hashEq r r' hr'] at h2
      rw [← toList_hashEq l l' hl] at h3
      rw [← toList_hashEq r r' hr'] at h4
      exact ⟨h1, h2, h3, h4, routed_hashEq (b + 1) l l' hl h5, routed_hashEq (b + 1) r r' hr' h6⟩
  | _, .empty, .leaf .., h, _ | _, .empty, .node .., h, _ | _, .leaf .., .empty, h, _
  | _, .leaf .., .node .., h, _ | _, .node .., .empty, h, _ | _, .node .., .leaf .., h, _ => by
      simp [HashEq] at h

omit [DecidableEq D] in
theorem routed_insAt (k : K) (v : V) : ∀ (d : Nat) (t : T K V D), Routed S d t →
    Routed S d (insAt S k v d t) :=
  fun d t h => routed_hashEq S d _ _ (hashEq_insAt S k v d t) (routed_insAtRebuild S k v d t h)

omit [DecidableEq D] in
theorem routed_insert {t : T K V D} (k : K) (v : V) (h : Routed S 0 t) : Routed S 0 (t.insert S k v) :=
  routed_insAt S k v 0 t h

omit [DecidableEq K] [DecidableEq D] in
/-- A routed trie's listing has each key once. -/
theorem toList_nodup : ∀ (d : Nat) (t : T K V D), Routed S d t → (t.toList.map Prod.fst).Nodup
  | _, .empty, _ => by simp [T.toList]
  | _, .leaf _ _, h => h
  | d, .node _ b _ l r, h => by
      obtain ⟨_, _, hlb, hrb, hl, hr⟩ := h
      simp only [T.toList, List.map_append, List.nodup_append]
      refine ⟨toList_nodup (b + 1) l hl, toList_nodup (b + 1) r hr, ?_⟩
      intro a ha c hc he; subst he
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ha
      obtain ⟨q, hq, hq'⟩ := List.mem_map.mp hc
      have h1 := hlb p hp; have h2 := hrb q hq; rw [hq'] at h2; simp [h1] at h2

omit [DecidableEq K] [DecidableEq D] in
theorem nodup_of_map_fst {α β : Type} {l : List (α × β)} (h : (l.map Prod.fst).Nodup) : l.Nodup :=
  List.Pairwise.of_map Prod.fst (fun _ _ hne he => hne (congrArg Prod.fst he)) h

omit [DecidableEq K] [DecidableEq D] in
theorem perm_of_nodup_mem {α : Type} {l₁ l₂ : List α} (h₁ : l₁.Nodup) (h₂ : l₂.Nodup)
    (h : ∀ a, a ∈ l₁ ↔ a ∈ l₂) : l₁.Perm l₂ := by
  classical
  rw [List.perm_iff_count]
  intro a
  have c₁ := List.nodup_iff_count.mp h₁ a
  have c₂ := List.nodup_iff_count.mp h₂ a
  have p := (List.count_pos_iff (a := a) (l := l₁)).trans ((h a).trans (List.count_pos_iff (a := a) (l := l₂)).symm)
  omega

omit [DecidableEq D] in
/-- **What an insert lists**: every other entry, and the new one. -/
theorem toList_insert_perm {t : T K V D} (h : Routed S 0 t) (k : K) (v : V) :
    (t.insert S k v).toList.Perm ((t.toList.filter fun p => p.1 ≠ k) ++ [(k, v)]) := by
  have hr := routed_insert S k v h
  apply perm_of_nodup_mem (nodup_of_map_fst (toList_nodup S 0 _ hr)) ?_
  · rintro ⟨a, b⟩
    rw [mem_toList S 0 _ hr]
    simp only [List.mem_append, List.mem_filter, List.mem_singleton, decide_eq_true_eq]
    have := getAt_insAt S k a v 0 t
    unfold T.insert; rw [this]
    by_cases ha : a = k
    · subst ha; simp [eq_comm]
    · simp [ha, mem_toList S 0 t h]
  · refine List.nodup_append.mpr ⟨(nodup_of_map_fst (toList_nodup S 0 t h)).sublist List.filter_sublist,
      by simp, ?_⟩
    intro x hx y hy he; subst he; simp at hy; subst hy; simp at hx

/-! ## History independence: a reachable trie IS the trie `build` makes from its listing

`Canon` is what every trie the operations reach satisfies: routed, well formed, and of canonical
SHAPE (a leaf holds at least one entry, and several only when their keys agree on every bit left; a
node branches at a bit in `[d, depth)`, has two non-empty children, and its `rep` is the first key
it lists). `build_toList` is then KERNEL-23's history independence, exactly (=): the trie is a
function of its listing, so two Worlds with the same contents have the same trie and the same root,
whatever order the turns ran in, and a decoder may rebuild a trie from its entries without reading a
single node hash (CODEC-19). -/

/-- The canonical shape at depth `d`. -/
def Shape : Nat → T K V D → Prop
  | _, .empty => True
  | d, .leaf _ kvs => kvs ≠ [] ∧
      (2 ≤ kvs.length → ∀ p ∈ kvs, ∀ q ∈ kvs, ∀ i, d ≤ i → i < S.depth → S.bit p.1 i = S.bit q.1 i)
  | d, .node _ b rep l r => d ≤ b ∧ b < S.depth ∧ l.toList.head?.map Prod.fst = some rep ∧
      r.toList ≠ [] ∧ Shape (b + 1) l ∧ Shape (b + 1) r

def Canon (d : Nat) (t : T K V D) : Prop := Routed S d t ∧ WF S t ∧ Shape S d t

omit [DecidableEq K] [DecidableEq D] in
/-- **`rep` is derived**: in a canonical shape every subtree's `first` (a node's `rep`) is the first
key it lists. -/
theorem rep_first : ∀ (d : Nat) (t : T K V D), Shape S d t → t.first = t.toList.head?.map Prod.fst
  | _, .empty, _ => rfl
  | _, .leaf _ _, _ => rfl
  | _, .node _ _ rep l r, hs => by
      obtain ⟨_, _, hrep, _, _, _⟩ := hs
      simp only [T.first, T.toList]
      exact (head_append_of hrep).symm

omit [DecidableEq K] [DecidableEq D] in
/-- **A canonical node has two non-empty children.** `Shape` is the conjunct that does it: a unary
node can be routed and well formed (tooth `Teeth.unary_routed_wf_not_shape`). -/
theorem canon_no_empty_child {d : Nat} {h : D} {b : Nat} {rep : K} {l r : T K V D}
    (hc : Canon S d (.node h b rep l r)) : l ≠ .empty ∧ r ≠ .empty := by
  obtain ⟨_, _, hs⟩ := hc
  obtain ⟨_, _, hrep, hrne, _, _⟩ := hs
  constructor
  · rintro rfl; simp [T.toList] at hrep
  · rintro rfl; simp [T.toList] at hrne

omit [DecidableEq K] [DecidableEq D] in
/-- Fuel beyond `depth - d` changes nothing: every node `build` makes branches at a bit in
`[d, depth)`. -/
theorem build_eq_of_fuel : ∀ (f f' d : Nat) (kvs : List (K × V)), S.depth - d ≤ f → S.depth - d ≤ f' →
    build S f d kvs = build S f' d kvs
  | _, _, _, [], _, _ => by simp [build]
  | f, f', _, [x], _, _ => by cases f <;> cases f' <;> simp [build]
  | 0, 0, _, a :: b :: rest, _, _ => rfl
  | 0, f' + 1, d, a :: b :: rest, h, _ => by
      have hn : splitBit S d (a :: b :: rest) = none :=
        (splitBit_none S).mpr fun i h1 h2 => absurd h2 (by omega)
      simp [build, hn]
  | f + 1, 0, d, a :: b :: rest, _, h => by
      have hn : splitBit S d (a :: b :: rest) = none :=
        (splitBit_none S).mpr fun i h1 h2 => absurd h2 (by omega)
      simp [build, hn]
  | f + 1, f' + 1, d, a :: b :: rest, h, h' => by
      simp only [build]
      cases hs : splitBit S d (a :: b :: rest) with
      | none => rfl
      | some c =>
          have hb := splitBit_bounds S hs
          dsimp only
          rw [build_eq_of_fuel f f' (c + 1) ((a :: b :: rest).filter fun q => !S.bit q.1 c) (by omega) (by omega),
            build_eq_of_fuel f f' (c + 1) ((a :: b :: rest).filter fun q => S.bit q.1 c) (by omega) (by omega)]

omit [DecidableEq K] [DecidableEq D] in
/-- A canonical shape's non-empty subtree lists something. -/
theorem toList_ne_nil : ∀ (d : Nat) (t : T K V D), Shape S d t → t ≠ .empty → t.toList ≠ []
  | _, .empty, _, h => absurd rfl h
  | _, .leaf _ _, hs, _ => hs.1
  | _, .node _ _ _ l r, hs, _ => by
      obtain ⟨_, _, hrep, _, _, _⟩ := hs
      obtain ⟨p, hp, _⟩ := head_key hrep
      exact List.ne_nil_of_mem (List.mem_append_left _ hp)

omit [DecidableEq K] [DecidableEq D] in
theorem shape_build_le : ∀ (f d : Nat) (kvs : List (K × V)), S.depth - d ≤ f → Shape S d (build S f d kvs)
  | _, _, [], _ => by simp [build, Shape]
  | f, _, [x], _ => by cases f <;> simp [build, mkLeaf, Shape]
  | 0, d, a :: b :: rest, h => by
      simp only [build, mkLeaf, Shape]
      exact ⟨by simp, fun _ p _ q _ i hi hid => absurd hid (by omega)⟩
  | f + 1, d, a :: b :: rest, h => by
      cases hs : splitBit S d (a :: b :: rest) with
      | none =>
          have hag := (splitBit_none S).mp hs
          rw [build_agree S (f + 1) d a (b :: rest) hag]
          simp only [mkLeaf, Shape]
          refine ⟨by simp, fun _ p hp q hq i hi hid => ?_⟩
          have e : ∀ x ∈ a :: b :: rest, S.bit x.1 i = S.bit a.1 i := fun x hx => by
            rcases List.mem_cons.mp hx with rfl | hx
            · rfl
            · exact hag i hi hid x hx
          rw [e p hp, e q hq]
      | some c =>
          have hbd := splitBit_bounds S hs
          obtain ⟨⟨xl, hxl, hbl⟩, ⟨xr, hxr, hbr⟩⟩ := splitBit_sides S hs
          rw [build_split S f d c a (b :: rest) hs]
          have hlS := shape_build_le f (c + 1) ((a :: b :: rest).filter fun q => !S.bit q.1 c) (by omega)
          have hrS := shape_build_le f (c + 1) ((a :: b :: rest).filter fun q => S.bit q.1 c) (by omega)
          have hlne : (build S f (c + 1) ((a :: b :: rest).filter fun q => !S.bit q.1 c)).toList ≠ [] :=
            ne_nil_of_perm (toList_build S _ _ _) (List.ne_nil_of_mem (List.mem_filter.mpr ⟨hxl, by simp [hbl]⟩))
          have hrne : (build S f (c + 1) ((a :: b :: rest).filter fun q => S.bit q.1 c)).toList ≠ [] :=
            ne_nil_of_perm (toList_build S _ _ _) (List.ne_nil_of_mem (List.mem_filter.mpr ⟨hxr, hbr⟩))
          have hfirst := rep_first S (c + 1) _ hlS
          simp only [mkNode, Shape]
          refine ⟨hbd.1, hbd.2, ?_, hrne, hlS, hrS⟩
          rw [hfirst]
          cases hl : (build S f (c + 1) ((a :: b :: rest).filter fun q => !S.bit q.1 c)).toList with
          | nil => exact absurd hl hlne
          | cons x xs => rfl

omit [DecidableEq K] [DecidableEq D] in
theorem shape_build : ∀ (f d : Nat) (kvs : List (K × V)), f = S.depth - d → Shape S d (build S f d kvs) :=
  fun f d kvs h => shape_build_le S f d kvs (by omega)

omit [DecidableEq D] in
/-- An insert never lists fewer entries. -/
private theorem length_insAtRebuild (k : K) (v : V) : ∀ (d : Nat) (t : T K V D),
    t.toList.length ≤ (insAtRebuild S k v d t).toList.length
  | _, .empty => by simp [T.toList]
  | d, .leaf _ kvs => by
      simp only [insAtRebuild]; split
      · simp [mkLeaf, T.toList]
      · rw [(toList_build S _ _ _).length_eq]; simp [T.toList]
  | d, .node h b rep l r => by
      simp only [insAtRebuild]
      cases hdk : diverge S k rep d b with
      | some c =>
          dsimp only
          cases S.bit k c <;> simp [mkNode, mkLeaf, T.toList] <;> omega
      | none =>
          dsimp only
          cases S.bit k b
          · simp only [mkNode, T.toList, List.length_append]
            have := length_insAtRebuild k v (b + 1) l; omega
          · simp only [mkNode, T.toList, List.length_append]
            have := length_insAtRebuild k v (b + 1) r; omega

omit [DecidableEq D] in
/-- An insert never lists fewer entries. -/
theorem length_insAt (k : K) (v : V) : ∀ (d : Nat) (t : T K V D),
    t.toList.length ≤ (insAt S k v d t).toList.length :=
  fun d t => (toList_hashEq _ _ (hashEq_insAt S k v d t)) ▸ length_insAtRebuild S k v d t

omit [DecidableEq D] in
/-- Where an insert puts its key in trie order: first exactly when it `precedes` the old first key. -/
private theorem first_insAtRebuild (k : K) (v : V) : ∀ (d : Nat) (t : T K V D) (x : K), Routed S d t → Shape S d t →
    t.toList.head?.map Prod.fst = some x →
    (insAtRebuild S k v d t).toList.head?.map Prod.fst = some (if precedes S k x d then k else x)
  | _, .empty, _, _, _, hx => by simp [T.toList] at hx
  | d, .leaf h kvs, x, _, hs, hx => by
      obtain ⟨_, hag⟩ := hs
      obtain ⟨p, rest, rfl⟩ : ∃ p rest, kvs = p :: rest := by
        cases kvs with
        | nil => simp [T.toList] at hx
        | cons p rest => exact ⟨p, rest, rfl⟩
      have hpx : p.1 = x := by simpa [T.toList] using hx
      subst hpx
      have hall : ∀ q ∈ rest, ∀ i, d ≤ i → i < S.depth → S.bit q.1 i = S.bit p.1 i := by
        intro q hq i hi hid
        have hlen := List.length_pos_of_mem hq
        exact hag (by simp only [List.length_cons]; omega) q (List.mem_cons_of_mem _ hq) p (by simp) i hi hid
      simp only [insAtRebuild]
      split
      · rename_i hany
        have hpre : precedes S k p.1 d = false := by
          by_cases hk : k = p.1
          · rw [hk]; exact precedes_of_agree S fun _ _ _ => rfl
          · obtain ⟨q, hq, hqk⟩ := List.any_eq_true.mp hany
            have hqk : q.1 = k := by simpa using hqk
            rcases List.mem_cons.mp hq with rfl | hq'
            · exact absurd hqk.symm hk
            · exact precedes_of_agree S fun i hi hid => by rw [← hqk]; exact hall q hq' i hi hid
        rw [hpre]
        by_cases hp : p.1 = k <;> simp [mkLeaf, T.toList, hp]
      · rename_i hany
        rw [List.cons_append]
        cases hdv : diverge S k p.1 d S.depth with
        | none =>
            have hagk := (diverge_none S).mp hdv
            have hpre : precedes S k p.1 d = false := by unfold precedes; rw [hdv]
            rw [hpre, build_agree S _ d p (rest ++ [(k, v)]) fun i hi hid q hq => by
              rcases List.mem_append.mp hq with hq | hq
              · exact hall q hq i hi hid
              · rw [List.mem_singleton.mp hq]; exact hagk i hi hid]
            simp [mkLeaf, T.toList]
        | some c =>
            obtain ⟨hdc, hcd, hne, hpre'⟩ := (diverge_some S).mp hdv
            have hpre : precedes S k p.1 d = !S.bit k c := by unfold precedes; rw [hdv]
            have hsplit : splitBit S d (p :: (rest ++ [(k, v)])) = some c := by
              refine (splitBit_some S).mpr ⟨hdc, hcd, ⟨(k, v), by simp, hne⟩, fun i hi hic q hq => ?_⟩
              rcases List.mem_append.mp hq with hq | hq
              · exact hall q hq i hi (by omega)
              · rw [List.mem_singleton.mp hq]; exact hpre' i hi hic
            have hfuel : S.depth - d = (S.depth - d - 1) + 1 := by omega
            rw [hpre, hfuel, build_split S _ d c p _ hsplit]
            have hrest : ∀ q ∈ rest, S.bit q.1 c = S.bit p.1 c := fun q hq => hall q hq c hdc hcd
            have hpc := bool_ne (Ne.symm hne)
            cases hkc : S.bit k c
            · rw [hkc] at hpc
              have h1 : rest.filter (fun q => !S.bit q.1 c) = [] :=
                List.filter_eq_nil_iff.mpr fun q hq => by simp [hrest q hq, hpc]
              have hf : (p :: (rest ++ [(k, v)])).filter (fun q => !S.bit q.1 c) = [(k, v)] := by
                rw [List.filter_cons, List.filter_append, h1]
                simp [hpc, hkc]
              rw [hf]
              cases S.depth - d - 1 <;> simp [build, mkNode, mkLeaf, T.toList]
            · rw [hkc] at hpc
              have h1 : rest.filter (fun q => !S.bit q.1 c) = rest :=
                List.filter_eq_self.mpr fun q hq => by simp [hrest q hq, hpc]
              have hf : (p :: (rest ++ [(k, v)])).filter (fun q => !S.bit q.1 c) = p :: rest := by
                rw [List.filter_cons, List.filter_append, h1]
                simp [hpc, hkc]
              rw [hf, build_agree S _ (c + 1) p rest fun i hi hid q hq => hall q hq i (by omega) hid]
              simp [mkNode, mkLeaf, T.toList]
  | d, .node h b rep l r, x, hr, hs, hx => by
      obtain ⟨hdb, hag, hlb, hrb, hlR, hrR⟩ := hr
      obtain ⟨_, hb, hrep, hrne, hlS, hrS⟩ := hs
      have hxr : x = rep := by
        have := head_append_of (l₂ := r.toList) hrep
        simp only [T.toList] at hx
        exact Option.some.inj (hx.symm.trans this)
      subst hxr
      obtain ⟨p0, hp0, hp0r⟩ := head_key hrep
      have hrepb : S.bit x b = false := by rw [← hp0r]; exact hlb p0 hp0
      simp only [insAtRebuild]
      cases hdk : diverge S k x d b with
      | some c =>
          dsimp only
          rw [precedes_of_diverge S hdk (by omega)]
          cases hkc : S.bit k c
          · simp [mkNode, mkLeaf, T.toList]
          · simp only [mkNode, mkLeaf, T.toList]
            rw [List.append_assoc, head_append_of hrep]; simp
      | none =>
          dsimp only
          have hagk := (diverge_none S).mp hdk
          cases hkb : S.bit k b
          · have ih := first_insAtRebuild k v (b + 1) l x hlR hlS hrep
            have hsk : precedes S k x d = precedes S k x (b + 1) :=
              precedes_skip S (by omega) fun i hi hib =>
                if h' : i < b then hagk i hi h' else by rw [show i = b by omega, hkb, hrepb]
            rw [hsk]
            simp only [mkNode, T.toList]
            exact head_append_of ih
          · have hdv : diverge S k x d (b + 1) = some b :=
              (diverge_some S).mpr ⟨hdb, by omega, by rw [hkb, hrepb]; decide, hagk⟩
            rw [precedes_of_diverge S hdv (by omega), hkb]
            simp only [mkNode, T.toList]
            rw [head_append_of hrep]; simp

omit [DecidableEq D] in
/-- Where an insert puts its key in trie order: first exactly when it `precedes` the old first key. -/
theorem first_insAt (k : K) (v : V) : ∀ (d : Nat) (t : T K V D) (x : K), Routed S d t → Shape S d t →
    t.toList.head?.map Prod.fst = some x →
    (insAt S k v d t).toList.head?.map Prod.fst = some (if precedes S k x d then k else x) :=
  fun d t x hr hs hx => (toList_hashEq _ _ (hashEq_insAt S k v d t)) ▸ first_insAtRebuild S k v d t x hr hs hx

omit [DecidableEq D] in
/-- An insert keeps the canonical shape of a routed trie. (Routed: the new `rep` is chosen by
`precedes` against the old one, which reads the order the keys are routed in.) -/
private theorem shape_insAtRebuild (k : K) (v : V) : ∀ (d : Nat) (t : T K V D), Routed S d t → Shape S d t →
    Shape S d (insAtRebuild S k v d t)
  | _, .empty, _, _ => by simp [insAtRebuild, mkLeaf, Shape]
  | d, .leaf _ kvs, _, hs => by
      simp only [insAtRebuild]; split
      · obtain ⟨hne, hag⟩ := hs
        simp only [mkLeaf, Shape]
        refine ⟨by simpa using hne, fun h2 p hp q hq i hi hid => ?_⟩
        obtain ⟨p', hp', rfl⟩ := List.mem_map.mp hp
        obtain ⟨q', hq', rfl⟩ := List.mem_map.mp hq
        have e : ∀ x : K × V, (if x.1 = k then (k, v) else x).1 = x.1 := fun x => by
          by_cases hx : x.1 = k
          · rw [if_pos hx]; exact hx.symm
          · rw [if_neg hx]
        rw [e, e]
        exact hag (by simpa using h2) p' hp' q' hq' i hi hid
      · exact shape_build S _ _ _ rfl
  | d, .node h b rep l r, hr, hs => by
      obtain ⟨hdb, hag, hlb, hrb, hlR, hrR⟩ := hr
      obtain ⟨_, hb, hrep, hrne, hlS, hrS⟩ := hs
      have hleaf : ∀ e, Shape S e (mkLeaf S [(k, v)] : T K V D) := fun e => ⟨by simp, fun h2 => by simp at h2⟩
      simp only [insAtRebuild]
      cases hdk : diverge S k rep d b with
      | some c =>
          dsimp only
          obtain ⟨hdc, hcb, _, _⟩ := (diverge_some S).mp hdk
          have hold : Shape S (c + 1) (T.node h b rep l r) := ⟨by omega, hb, hrep, hrne, hlS, hrS⟩
          have hlne : (T.node h b rep l r).toList ≠ [] := by
            obtain ⟨p0, hp0, _⟩ := head_key hrep
            exact List.ne_nil_of_mem (List.mem_append_left _ hp0)
          cases S.bit k c
          · exact ⟨hdc, by omega, rfl, hlne, hleaf _, hold⟩
          · exact ⟨hdc, by omega, head_append_of hrep, by simp [mkLeaf, T.toList], hold, hleaf _⟩
      | none =>
          dsimp only
          cases hkb : S.bit k b
          · exact ⟨hdb, hb, first_insAtRebuild S k v (b + 1) l rep hlR hlS hrep, hrne,
              shape_insAtRebuild k v (b + 1) l hlR hlS, hrS⟩
          · refine ⟨hdb, hb, hrep, ?_, hlS, shape_insAtRebuild k v (b + 1) r hrR hrS⟩
            intro h0
            have := length_insAtRebuild S k v (b + 1) r
            rw [h0, List.length_nil] at this
            exact hrne (List.eq_nil_of_length_eq_zero (Nat.le_zero.mp this))

omit [DecidableEq K] [DecidableEq D] in
theorem shape_hashEq : ∀ (d : Nat) (t u : T K V D), HashEq t u → Shape S d u → Shape S d t
  | _, .empty, .empty, _, _ => trivial
  | _, .leaf _ _, .leaf _ _, h, hs => by simp only [HashEq] at h; subst h; exact hs
  | d, .node _ b rep l r, .node _ b' rep' l' r', h, hs => by
      obtain ⟨rfl, rfl, hl, hr⟩ := h
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hs
      rw [← toList_hashEq l l' hl] at h3
      rw [← toList_hashEq r r' hr] at h4
      exact ⟨h1, h2, h3, h4, shape_hashEq (b + 1) l l' hl h5, shape_hashEq (b + 1) r r' hr h6⟩
  | _, .empty, .leaf .., h, _ | _, .empty, .node .., h, _ | _, .leaf .., .empty, h, _
  | _, .leaf .., .node .., h, _ | _, .node .., .empty, h, _ | _, .node .., .leaf .., h, _ => by
      simp [HashEq] at h

omit [DecidableEq D] in
/-- An insert keeps the canonical shape of a routed trie. -/
theorem shape_insAt (k : K) (v : V) : ∀ (d : Nat) (t : T K V D), Routed S d t → Shape S d t →
    Shape S d (insAt S k v d t) :=
  fun d t hr hs => shape_hashEq S d _ _ (hashEq_insAt S k v d t) (shape_insAtRebuild S k v d t hr hs)

omit [DecidableEq K] [DecidableEq D] in
theorem canon_empty (d : Nat) : Canon S d (T.empty : T K V D) := ⟨trivial, trivial, trivial⟩

omit [DecidableEq K] [DecidableEq D] in
/-- What `build` makes from distinct keys, with the fuel that reaches `depth`, is canonical. -/
theorem canon_build (d : Nat) (kvs : List (K × V)) (h : (kvs.map Prod.fst).Nodup) :
    Canon S d (build S (S.depth - d) d kvs) :=
  ⟨routed_build S _ d kvs h, wf_build S _ d kvs, shape_build S _ d kvs rfl⟩

omit [DecidableEq D] in
theorem canon_insert {t : T K V D} (k : K) (v : V) (h : Canon S 0 t) : Canon S 0 (t.insert S k v) :=
  ⟨routed_insAt S k v 0 t h.1, wf_insAt S k v 0 t h.2.1, shape_insAt S k v 0 t h.1 h.2.2⟩

omit [DecidableEq K] [DecidableEq D] in
/-- **History independence**: a canonical trie is the one `build` makes from its own listing. -/
theorem build_toList : ∀ (d : Nat) (t : T K V D), Canon S d t → build S (S.depth - d) d t.toList = t
  | _, .empty, _ => by simp [T.toList, build]
  | d, .leaf h kvs, ⟨_, hw, hs⟩ => by
      simp only [T.toList]
      simp only [WF] at hw
      obtain ⟨hne, hag⟩ := hs
      match kvs, hne, hag, hw with
      | [], hne, _, _ => exact absurd rfl hne
      | p :: rest, _, hag, hw =>
          rw [build_agree S _ d p rest fun i hi hid q hq =>
            hag (by have := List.length_pos_of_mem hq; simp only [List.length_cons]; omega)
              q (List.mem_cons_of_mem _ hq) p (by simp) i hi hid]
          simp [mkLeaf, hw]
  | d, .node h b rep l r, ⟨hr, hw, hs⟩ => by
      obtain ⟨hdb, hag, hlb, hrb, hlR, hrR⟩ := hr
      obtain ⟨hb, hh, hlW, hrW⟩ := hw
      obtain ⟨_, _, hrep, hrne, hlS, hrS⟩ := hs
      have e1 : (l.toList ++ r.toList).filter (fun p => !S.bit p.1 b) = l.toList := by
        rw [List.filter_append, List.filter_eq_self.mpr fun p hp => by simp [hlb p hp],
          List.filter_eq_nil_iff.mpr fun p hp => by simp [hrb p hp], List.append_nil]
      have e2 : (l.toList ++ r.toList).filter (fun p => S.bit p.1 b) = r.toList := by
        rw [List.filter_append, List.filter_eq_nil_iff.mpr fun p hp => by simp [hlb p hp],
          List.filter_eq_self.mpr fun p hp => by simp [hrb p hp], List.nil_append]
      obtain ⟨hd0, ls, hl⟩ : ∃ p ls, l.toList = p :: ls := by
        cases h' : l.toList with
        | nil => rw [h'] at hrep; simp at hrep
        | cons p ls => exact ⟨p, ls, rfl⟩
      have hd0l : hd0 ∈ l.toList := by rw [hl]; simp
      obtain ⟨q, hq⟩ : ∃ q, q ∈ r.toList := by
        cases h' : r.toList with
        | nil => exact absurd h' hrne
        | cons q _ => exact ⟨q, by simp⟩
      have hsplit : splitBit S d (hd0 :: (ls ++ r.toList)) = some b := by
        refine (splitBit_some S).mpr ⟨hdb, hb, ⟨q, List.mem_append_right _ hq,
          by rw [hrb q hq, hlb hd0 hd0l]; decide⟩, fun i hi hib q' hq' => ?_⟩
        have hq'' : q' ∈ l.toList ++ r.toList := by
          rcases List.mem_append.mp hq' with h1 | h1
          · rw [hl]; exact List.mem_append_left _ (List.mem_cons_of_mem _ h1)
          · exact List.mem_append_right _ h1
        rw [hag q' hq'' i hi hib, hag hd0 (List.mem_append_left _ hd0l) i hi hib]
      have hf : S.depth - d = (S.depth - d - 1) + 1 := by omega
      have hfl : build S (S.depth - d - 1) (b + 1) l.toList = l :=
        (build_eq_of_fuel S _ _ _ _ (by omega) (Nat.le_refl _)).trans (build_toList (b + 1) l ⟨hlR, hlW, hlS⟩)
      have hfr : build S (S.depth - d - 1) (b + 1) r.toList = r :=
        (build_eq_of_fuel S _ _ _ _ (by omega) (Nat.le_refl _)).trans (build_toList (b + 1) r ⟨hrR, hrW, hrS⟩)
      have hlfirst : l.first = some rep := (rep_first S _ l hlS).trans hrep
      simp only [T.toList]
      rw [hf, hl, List.cons_append, build_split S _ d b hd0 _ hsplit, ← List.cons_append, ← hl, e1, e2,
        hfl, hfr, hlfirst]
      simp [mkNode, hh]

omit [DecidableEq K] [DecidableEq D] in
/-- Two canonical tries with the same listing are the same trie (so: the same root). -/
theorem eq_of_toList_eq {t t' : T K V D} (h : Canon S 0 t) (h' : Canon S 0 t') (he : t.toList = t'.toList) :
    t = t' := by
  rw [← build_toList S 0 t h, ← build_toList S 0 t' h', he]

/-! ## `rep` is a cache: the root does not commit it, and a wrong one is a refusal -/

/-- Two trees with the same hashed fields: the same shape, the same branching bits, the same leaf
entries. Their nodes' `rep`s and every cached digest are free. -/
def RepEq : T K V D → T K V D → Prop
  | .empty, .empty => True
  | .leaf _ kvs, .leaf _ kvs' => kvs = kvs'
  | .node _ b _ l r, .node _ b' _ l' r' => b = b' ∧ RepEq l l' ∧ RepEq r r'
  | _, _ => False

omit [DecidableEq K] [DecidableEq D] in
/-- **The root is a function of the hashed fields only**: two well-formed trees with the same
branching bits and leaf entries have one root, whatever their `rep`s. (Tooth for `WF`:
`Teeth.hashOf_rep_irrel_needs_wf`.) -/
theorem hashOf_rep_irrel : ∀ (t t' : T K V D), WF S t → WF S t' → RepEq t t' →
    t.hashOf S = t'.hashOf S
  | .empty, .empty, _, _, _ => rfl
  | .leaf _ _, .leaf _ _, hw, hw', he => by
      simp only [WF, T.hashOf] at hw hw' ⊢; rw [hw, hw', he]
  | .node _ _ _ l r, .node _ _ _ l' r', hw, hw', he => by
      obtain ⟨rfl, hl, hr⟩ := he
      have el := hashOf_rep_irrel l l' hw.2.2.1 hw'.2.2.1 hl
      have er := hashOf_rep_irrel r r' hw.2.2.2 hw'.2.2.2 hr
      exact hw.2.1.trans (el ▸ er ▸ hw'.2.1.symm)
  | .empty, .leaf _ _, _, _, he => (he : False).elim
  | .empty, .node _ _ _ _ _, _, _, he => (he : False).elim
  | .leaf _ _, .empty, _, _, he => (he : False).elim
  | .leaf _ _, .node _ _ _ _ _, _, _, he => (he : False).elim
  | .node _ _ _ _ _, .empty, _, _, he => (he : False).elim
  | .node _ _ _ _ _, .leaf _ _, _, _, he => (he : False).elim

omit [DecidableEq K] [DecidableEq D] in
theorem toList_rep_irrel : ∀ (t t' : T K V D), RepEq t t' → t.toList = t'.toList
  | .empty, .empty, _ => rfl
  | .leaf _ _, .leaf _ _, he => he
  | .node _ _ _ l r, .node _ _ _ l' r', he => by
      simp only [T.toList]; rw [toList_rep_irrel l l' he.2.1, toList_rep_irrel r r' he.2.2]
  | .empty, .leaf _ _, he => (he : False).elim
  | .empty, .node _ _ _ _ _, he => (he : False).elim
  | .leaf _ _, .empty, he => (he : False).elim
  | .leaf _ _, .node _ _ _ _ _, he => (he : False).elim
  | .node _ _ _ _ _, .empty, he => (he : False).elim
  | .node _ _ _ _ _, .leaf _ _, he => (he : False).elim

omit [DecidableEq K] [DecidableEq D] in
/-- A proof does not read `rep` either (and `climb` reads only the proof): two well-formed trees
with the same hashed fields give every key one proof. -/
theorem proveAt_rep_irrel (k : K) : ∀ (t t' : T K V D), WF S t → WF S t' → RepEq t t' →
    proveAt S k t = proveAt S k t'
  | .empty, .empty, _, _, _ => rfl
  | .leaf _ _, .leaf _ _, _, _, he => by simp only [RepEq] at he; subst he; rfl
  | .node _ _ _ l r, .node _ _ _ l' r', hw, hw', he => by
      obtain ⟨rfl, hl, hr⟩ := he
      obtain ⟨_, _, hwl, hwr⟩ := hw
      obtain ⟨_, _, hwl', hwr'⟩ := hw'
      simp only [proveAt]
      rw [proveAt_rep_irrel k l l' hwl hwl' hl, proveAt_rep_irrel k r r' hwr hwr' hr,
        hashOf_rep_irrel S l l' hwl hwl' hl, hashOf_rep_irrel S r r' hwr hwr' hr]
  | .empty, .leaf _ _, _, _, he => (he : False).elim
  | .empty, .node _ _ _ _ _, _, _, he => (he : False).elim
  | .leaf _ _, .empty, _, _, he => (he : False).elim
  | .leaf _ _, .node _ _ _ _ _, _, _, he => (he : False).elim
  | .node _ _ _ _ _, .empty, _, _, he => (he : False).elim
  | .node _ _ _ _ _, .leaf _ _, _, _, he => (he : False).elim

omit [DecidableEq D] in
/-- **A wrong `rep` is a refusal, never a wrong read**: on a routed trie, the same tree with any
`rep`s reads every key either as the trie does or `none`. -/
theorem getAt_rep_sound (k : K) : ∀ (d : Nat) (t t' : T K V D), Routed S d t → RepEq t t' →
    getAt S k d t' = getAt S k d t ∨ getAt S k d t' = none := by
  intro d t t' hr he
  cases hg : getAt S k d t' with
  | none => exact .inr rfl
  | some v =>
      left
      have hm := mem_of_getAt S d t' k v hg
      rw [← toList_rep_irrel t t' he] at hm
      exact ((mem_toList S d t hr k v).mp hm).symm

end Nanodregg.Kernel.Trie

namespace Nanodregg.Kernel.Trie.RepTooth

/-- A two-bit toy spec (keys are `Nat`s read bit by bit). Every digest is `0`, so it has collisions
everywhere: it serves `getAt` teeth only, which read no digest. The proof teeth use `Teeth.toyI`. -/
private def toy : Spec Nat Nat Nat where
  bit k i := k.testBit i
  depth := 2
  depth_lt := by decide
  hash _ := 0
  dbytes _ := ByteArray.empty
  kbytes _ := ByteArray.empty
  vdigest v := v

/-- Tooth for `getAt_rep_sound` (a `getAt` tooth only; its toy hash is constant): keys `0` and `2` part at bit 1, under a node whose `rep` is `0`.
Corrupt the `rep` to `1` (which leaves bit 0) and key `0`, present in the left leaf, reads `none`:
the wrong cache refuses, it does not misread. -/
theorem getAt_wrong_rep :
    (T.node 0 1 0 (.leaf 0 [(0, 7)]) (.leaf 0 [(2, 8)]) : T Nat Nat Nat).get toy 0 = some 7 ∧
    (T.node 0 1 1 (.leaf 0 [(0, 7)]) (.leaf 0 [(2, 8)]) : T Nat Nat Nat).get toy 0 = none := by
  decide

end Nanodregg.Kernel.Trie.RepTooth

/-! ## Teeth for the proof premises, on a toy with an injective hash

`toyI` hashes a byte string to its own bytes, so equal digests are equal bytes and `CollAmong toyI L`
is false for every `L` (`toyI_noColl`); its key and digest encodings are prefix-free, so
`climb_sound`'s `hL` and `hN` hold too (`toyI_hL`, `toyI_hN`). What each tooth below exhibits is therefore no hash's fault: the
premise or check it names is the one that stops it. -/

namespace Nanodregg.Kernel.Trie.Teeth

/-- Byte stuffing: every byte behind a `1`, then a `0` (prefix-free). -/
private def enc : List UInt8 → List UInt8
  | [] => [0]
  | x :: xs => 1 :: x :: enc xs

/-- A key in unary: `n` ones, then a `0` (prefix-free). -/
private def unary : Nat → List UInt8
  | 0 => [0]
  | n + 1 => 1 :: unary n

/-- Two bits of a `Nat` key; the digest of a byte string is the string. -/
private def toyI : Spec Nat Nat (List UInt8) where
  bit k i := k.testBit i
  depth := 2
  depth_lt := by decide
  hash b := b.data.toList
  dbytes d := ⟨(enc d).toArray⟩
  kbytes k := ⟨(unary k).toArray⟩
  vdigest v := unary v

private theorem enc_prefix : ∀ {a c s s' : List UInt8}, enc a ++ s = enc c ++ s' → a = c ∧ s = s'
  | [], [], _, _, h => by simpa [enc] using h
  | [], _ :: _, _, _, h => by simp [enc] at h
  | _ :: _, [], _, _, h => by simp [enc] at h
  | _ :: _, _ :: _, _, _, h => by
      simp only [enc, List.cons_append, List.cons.injEq] at h
      obtain ⟨_, rfl, h⟩ := h
      obtain ⟨rfl, rfl⟩ := enc_prefix h
      exact ⟨rfl, rfl⟩

private theorem unary_prefix : ∀ {a c : Nat} {s s' : List UInt8}, unary a ++ s = unary c ++ s' →
    a = c ∧ s = s'
  | 0, 0, _, _, h => by simpa [unary] using h
  | 0, _ + 1, _, _, h => by simp [unary] at h
  | _ + 1, 0, _, _, h => by simp [unary] at h
  | _ + 1, _ + 1, _, _, h => by
      simp only [unary, List.cons_append, List.cons.injEq] at h
      obtain ⟨rfl, rfl⟩ := unary_prefix h.2
      exact ⟨rfl, rfl⟩

/-- `toyI`'s hash is injective. -/
theorem toyI_noColl (L : List ByteArray) : ¬ CollAmong toyI L := by
  rintro ⟨a, -, b, -, hne, h⟩
  exact hne (ByteArray.ext (Array.toList_inj.mp h))

/-- `climb_sound`'s `hN` holds for `toyI`. -/
theorem toyI_hN : ∀ a b c e : List UInt8,
    toyI.dbytes a ++ toyI.dbytes b = toyI.dbytes c ++ toyI.dbytes e → a = c ∧ b = e := by
  intro a b c e h
  have h' := congrArg (fun z : ByteArray => z.data.toList) h
  simp only [ByteArray.data_append, Array.toList_append, toyI] at h'
  obtain ⟨rfl, h2⟩ := enc_prefix h'
  exact ⟨rfl, (enc_prefix (s := []) (s' := []) (by simpa using h2)).1⟩

private theorem leafBody_list : ∀ (x : List (Nat × List UInt8)),
    (leafBody toyI x).data.toList = x.foldr (fun p acc => unary p.1 ++ (enc p.2 ++ acc)) []
  | [] => rfl
  | p :: rest => by
      simp only [leafBody, List.foldr_cons] at *
      rw [← leafBody_list rest]
      simp [leafBody, toyI, ByteArray.data_append]

/-- `climb_sound`'s `hL` holds for `toyI`. -/
theorem toyI_hL : ∀ x y, leafBody toyI x = leafBody toyI y → x = y := by
  intro x y h
  have h' := congrArg (fun z : ByteArray => z.data.toList) h
  simp only [leafBody_list] at h'
  clear h
  induction x generalizing y with
  | nil => cases y with
    | nil => rfl
    | cons q ys => obtain ⟨k, d⟩ := q; cases k <;> simp [unary] at h'
  | cons p xs ih => cases y with
    | nil => obtain ⟨k, d⟩ := p; cases k <;> simp [unary] at h'
    | cons q ys =>
      simp only [List.foldr_cons] at h'
      obtain ⟨h1, h2⟩ := unary_prefix h'
      obtain ⟨h3, h4⟩ := enc_prefix h2
      rw [ih ys h4]
      cases p; cases q; simp_all

/-- Tooth for `hashOf_rep_irrel`'s `WF` premises: a leaf whose cached digest is stale has the
entries of a well-formed one and another root. -/
theorem hashOf_rep_irrel_needs_wf :
    RepEq (T.leaf [] [(0, 7)] : T Nat Nat (List UInt8)) (mkLeaf toyI [(0, 7)]) ∧
    WF toyI (mkLeaf toyI [(0, 7)] : T Nat Nat (List UInt8)) ∧
    (T.leaf [] [(0, 7)] : T Nat Nat (List UInt8)).hashOf toyI ≠ (mkLeaf toyI [(0, 7)]).hashOf toyI :=
  ⟨rfl, wf_mkLeaf toyI _, by decide⟩

/-- A node branching at bit 0 whose left child is empty, over key `1`. -/
private def unaryT : T Nat Nat (List UInt8) := mkNode toyI 0 1 .empty (mkLeaf toyI [(1, 8)])

/-- Tooth for `canon_no_empty_child`: a unary node is routed and well formed (its digest is honest,
key `1` has bit 0 set), so `Shape` is the conjunct that refuses it. -/
theorem unary_routed_wf_not_shape :
    Routed toyI 0 unaryT ∧ WF toyI unaryT ∧ ¬ Shape toyI 0 unaryT ∧ ¬ Canon toyI 0 unaryT := by
  have hs : ¬ Shape toyI 0 unaryT := by simp [unaryT, mkNode, Shape, T.toList]
  refine ⟨?_, wf_mkNode toyI (by decide) trivial (wf_mkLeaf toyI _), hs, fun hc => hs hc.2.2⟩
  simp [unaryT, mkNode, mkLeaf, Routed, T.toList, toyI]

/-- Keys `0` (left) and `2` (right) part at bit 1, under a node whose `rep` is `1`: the keys leave
it on the skipped bit 0. Every digest is honest; only the routing is broken. -/
private def badRep : T Nat Nat (List UInt8) :=
  mkNode toyI 1 1 (mkLeaf toyI [(0, 7)]) (mkLeaf toyI [(2, 8)])

private theorem badRep_facts :
    WF toyI badRep ∧ Shallow toyI 0 badRep ∧ ¬ Routed toyI 0 badRep := by
  refine ⟨wf_mkNode toyI (by decide) (wf_mkLeaf toyI _) (wf_mkLeaf toyI _),
    ⟨by decide, by decide, trivial, trivial⟩, fun hr => ?_⟩
  have := hr.2.1 (0, 7) (by simp [mkLeaf, T.toList]) 0 (Nat.le_refl _) (by decide)
  simp [toyI] at this

/-- Tooth for `inclusion_sound`'s `Routed` premise: on a well-formed, shallow tree with a corrupt
`rep`, under an injective hash, the tree's own proof for key `0` verifies inclusion of `7` while
`get` reads `none` (it refuses `0` on the skipped bit the `rep` claims). -/
theorem inclusion_needs_routed :
    WF toyI badRep ∧ Shallow toyI 0 badRep ∧ ¬ Routed toyI 0 badRep ∧
    (∀ L, ¬ CollAmong toyI L) ∧ (∀ x y, leafBody toyI x = leafBody toyI y → x = y) ∧
    (∀ a b c e, toyI.dbytes a ++ toyI.dbytes b = toyI.dbytes c ++ toyI.dbytes e → a = c ∧ b = e) ∧
    verifyInclusion toyI (badRep.hashOf toyI) 0 (toyI.vdigest 7) (badRep.prove toyI 0) = true ∧
    badRep.get toyI 0 = none :=
  ⟨badRep_facts.1, badRep_facts.2.1, badRep_facts.2.2, toyI_noColl, toyI_hL, toyI_hN,
    by decide, by decide⟩

/-- Tooth for `prove_excludes`'s `Routed` premise: the same tree reads key `0` as `none`, but its
own proof for `0` ends at the leaf holding `0`, so it does not verify exclusion. -/
theorem prove_excludes_needs_routed :
    WF toyI badRep ∧ Shallow toyI 0 badRep ∧ ¬ Routed toyI 0 badRep ∧
    badRep.get toyI 0 = none ∧
    verifyExclusion toyI (badRep.hashOf toyI) 0 (badRep.prove toyI 0) = false :=
  ⟨badRep_facts.1, badRep_facts.2.1, badRep_facts.2.2, by decide, by decide⟩

/-- Keys `0` (left) and `1` (right) part at bit 0: a canonical trie. -/
private def goodT : T Nat Nat (List UInt8) :=
  mkNode toyI 0 0 (mkLeaf toyI [(0, 7)]) (mkLeaf toyI [(1, 8)])

/-- An exclusion proof for key `1`: it ends at the left leaf (which does not hold `1`), with the
right leaf as its sibling at a node it claims branches at bit `2 ^ 16`. Key `1`'s bit `2 ^ 16` is
clear, so `climb` puts the end on the left: the node's bytes are `goodT`'s root's, since
`u16 (2 ^ 16) = u16 0`. -/
private def forged : Proof Nat (List UInt8) :=
  ⟨some (digests toyI [(0, 7)]), [(2 ^ 16, (mkLeaf toyI [(1, 8)] : T Nat Nat (List UInt8)).hashOf toyI)]⟩

/-- `ascends` without its `< depth` half. -/
private def ascendsNoBound : Nat → List (Nat × List UInt8) → Bool
  | _, [] => true
  | d, (b, _) :: rest => decide (d ≤ b) && ascendsNoBound (b + 1) rest

/-- `verifyExclusion` with `ascendsNoBound` for `ascends`. -/
private def verifyExclusionNoBound (root : List UInt8) (k : Nat) (p : Proof Nat (List UInt8)) : Bool :=
  ascendsNoBound 0 p.sibs &&
  (match p.term with
   | some kds => (find k kds).isNone
   | none => true) &&
  decide (climb toyI k p.sibs (termHash toyI p.term) = root)

/-- Tooth for the `< depth` half of `ascends` (in `verifyExclusion`, and in `climb_sound`'s
premise): a sibling bit claimed as `b + 2 ^ 16` aliases `u16 b`. On a canonical trie, under an
injective hash with `hL` and `hN`, a verifier without the bound accepts `forged`, an exclusion proof
for key `1`, which the trie holds. `verifyExclusion` refuses it. -/
theorem ascends_bound_needed :
    u16 (0 + 2 ^ 16) = u16 0 ∧
    Canon toyI 0 goodT ∧ (∀ L, ¬ CollAmong toyI L) ∧ (∀ x y, leafBody toyI x = leafBody toyI y → x = y) ∧
    (∀ a b c e, toyI.dbytes a ++ toyI.dbytes b = toyI.dbytes c ++ toyI.dbytes e → a = c ∧ b = e) ∧
    goodT.get toyI 1 = some 8 ∧
    verifyExclusionNoBound (goodT.hashOf toyI) 1 forged = true ∧
    verifyExclusion toyI (goodT.hashOf toyI) 1 forged = false := by
  refine ⟨by decide, ⟨?_, wf_mkNode toyI (by decide) (wf_mkLeaf toyI _) (wf_mkLeaf toyI _), ?_⟩,
    toyI_noColl, toyI_hL, toyI_hN, by decide, by decide, by decide⟩
  · simp [goodT, mkNode, mkLeaf, Routed, T.toList, toyI]
  · simp [goodT, mkNode, mkLeaf, Shape, T.toList, toyI]

end Nanodregg.Kernel.Trie.Teeth

namespace Nanodregg.Kernel.Trie

/-- A root read through a lazy empty digest (`T.rootWith`, the World's four roots) is the root,
when the thunk holds the empty digest. -/
theorem rootWith_eq {K V D : Type} (S : Spec K V D) (t : T K V D) (e : Thunk D)
    (he : e.get = emptyHash S) : t.rootWith S e = t.hashOf S := by
  cases t <;> first | exact he | rfl

end Nanodregg.Kernel.Trie
