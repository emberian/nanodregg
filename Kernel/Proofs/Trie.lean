/-
# Kernel.Proofs.Trie — the Merkle trie is an exact map, and its proofs are sound

* `get_insert`: after `insert k v`, `k` reads `v` and every other key reads what it did, for ANY
  bit function (no premise).
* `inclusion_sound` / `exclusion_sound`: a proof that verifies against the root of a well-formed
  trie tells the truth about the key, or exhibits two different byte strings with one hash.
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

theorem getAt_build :
    ∀ (f d : Nat) (kvs : List (K × V)) (k : K), getAt S k d (build S f d kvs) = find k kvs
  | _, _, [], _ => by simp [build, getAt, find_nil]
  | f, _, [x], k => by cases f <;> simp [build, getAt, mkLeaf]
  | 0, _, a :: b :: rest, k => by simp [build, getAt, mkLeaf]
  | f + 1, d, a :: b :: rest, k => by
      simp only [build, mkNode, getAt]
      cases hb : S.bit k d
      · simp only
        rw [getAt_build f (d + 1), find_filter (q := fun x => !S.bit x d)]; simp [hb]
      · simp only
        rw [getAt_build f (d + 1), find_filter (q := fun x => S.bit x d)]; simp [hb]

theorem getAt_insAt (k k' : K) (v : V) :
    ∀ (d : Nat) (t : T K V D), getAt S k' d (insAt S k v d t) = if k' = k then some v else getAt S k' d t
  | d, .empty => by
      simp only [insAt, mkLeaf, getAt, find_cons, find_nil]
      by_cases h : k' = k
      · subst h; simp
      · simp [h, Ne.symm h]
  | d, .leaf h kvs => by
      simp only [insAt]
      split
      · rename_i hany; simp only [mkLeaf, getAt]; exact find_replace hany
      · rename_i hany
        rw [getAt_build, find_append, getAt, find_cons, find_nil]
        by_cases hk : k' = k
        · subst hk; simp [find_none_of_not_any (Bool.eq_false_iff.mpr hany)]
        · simp [hk, Ne.symm hk]
  | d, .node h l r => by
      simp only [insAt]
      cases hb : S.bit k d
      · simp only [mkNode, getAt]
        cases hb' : S.bit k' d
        · simp only; rw [getAt_insAt k k' v (d + 1) l]
        · have hne : k' ≠ k := fun he => by subst he; simp [hb] at hb'
          simp [hne]
      · simp only [mkNode, getAt]
        cases hb' : S.bit k' d
        · have hne : k' ≠ k := fun he => by subst he; simp [hb] at hb'
          simp [hne]
        · simp only; rw [getAt_insAt k k' v (d + 1) r]

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

end Nanodregg.Kernel.Trie

namespace Nanodregg.Kernel.Trie

variable {K V D : Type} (S : Spec K V D) [DecidableEq K]

/-! ## Soundness of proofs -/

/-- Every cached digest is the digest of what it caches. -/
def WF : T K V D → Prop
  | .empty => True
  | .leaf h kvs => h = leafHash S (digests S kvs)
  | .node h l r => h = nodeHash S (l.hashOf S) (r.hashOf S) ∧ WF l ∧ WF r

/-- Two different byte strings with one digest. -/
def Coll : Prop := ∃ a b : ByteArray, a ≠ b ∧ S.hash a = S.hash b

omit [DecidableEq K] in
theorem tagged_inj {a b : UInt8} {x y : ByteArray} (h : tagged a x = tagged b y) : a = b ∧ x = y := by
  unfold tagged at h
  obtain ⟨h₁, h₂⟩ := bytes_append_inj h rfl
  refine ⟨?_, h₂⟩
  have := congrArg (fun z : ByteArray => z.data.toList) h₁
  simpa using this

omit [DecidableEq K] in
/-- Equal digests of differently tagged or different bytes are a collision. -/
theorem hash_tagged {a b : UInt8} {x y : ByteArray}
    (h : S.hash (tagged a x) = S.hash (tagged b y)) : (a = b ∧ x = y) ∨ Coll S := by
  by_cases he : tagged a x = tagged b y
  · exact .inl (tagged_inj he)
  · exact .inr ⟨_, _, he, h⟩

theorem find_digests {k : K} :
    ∀ {kvs : List (K × V)}, find k (digests S kvs) = (find k kvs).map S.vdigest
  | [] => rfl
  | p :: rest => by
      simp only [digests, List.map_cons] at *
      rw [find_cons, find_cons]
      split
      · simp
      · exact find_digests

/-- What a proof ends at says what the trie holds at the key. -/
theorem getAt_proveAt (k : K) :
    ∀ (d : Nat) (t : T K V D), (getAt S k d t).map S.vdigest =
      match (proveAt S k d t).term with
      | none => none
      | some kds => find k kds
  | _, .empty => rfl
  | _, .leaf _ kvs => by simp [getAt, proveAt, find_digests]
  | d, .node _ l r => by
      simp only [getAt, proveAt]
      cases S.bit k d <;> simp only <;> exact getAt_proveAt k (d + 1) _

variable (hL : ∀ x y, leafBody S x = leafBody S y → x = y)
  (hN : ∀ a b c e, S.dbytes a ++ S.dbytes b = S.dbytes c ++ S.dbytes e → a = c ∧ b = e)
include hL hN

omit [DecidableEq K] in
/-- **A path that recomputes the root ends where the trie's path for the key ends**, or the hash
has a collision. -/
theorem climb_sound (k : K) :
    ∀ (d : Nat) (t : T K V D) (sibs : List D) (term : Option (List (K × D))),
      WF S t → climb S k d sibs (termHash S term) = t.hashOf S →
      term = (proveAt S k d t).term ∨ Coll S
  | d, .empty, [], none, _, _ => .inl rfl
  | d, .empty, [], some kds, _, h => by
      rcases hash_tagged S h with ⟨h1, _⟩ | c
      · exact absurd h1 (by decide)
      · exact .inr c
  | d, .empty, s :: rest, term, _, h => by
      simp only [climb] at h
      split at h <;>
      · rcases hash_tagged S h with ⟨h1, _⟩ | c
        · exact absurd h1 (by decide)
        · exact .inr c
  | d, .leaf hv kvs, [], none, hw, h => by
      simp only [climb, termHash, T.hashOf, WF] at h hw; rw [hw] at h
      rcases hash_tagged S h with ⟨h1, _⟩ | c
      · exact absurd h1 (by decide)
      · exact .inr c
  | d, .leaf hv kvs, [], some kds, hw, h => by
      simp only [climb, termHash, T.hashOf, WF] at h hw; rw [hw] at h
      rcases hash_tagged S h with ⟨_, hb⟩ | c
      · exact .inl (by simp [proveAt, hL _ _ hb])
      · exact .inr c
  | d, .leaf hv kvs, s :: rest, term, hw, h => by
      simp only [climb, T.hashOf, WF] at h hw; rw [hw] at h
      split at h <;>
      · rcases hash_tagged S h with ⟨h1, _⟩ | c
        · exact absurd h1 (by decide)
        · exact .inr c
  | d, .node hv l r, [], none, hw, h => by
      simp only [climb, termHash, T.hashOf, WF] at h hw; rw [hw.1] at h
      rcases hash_tagged S h with ⟨h1, _⟩ | c
      · exact absurd h1 (by decide)
      · exact .inr c
  | d, .node hv l r, [], some kds, hw, h => by
      simp only [climb, termHash, T.hashOf, WF] at h hw; rw [hw.1] at h
      rcases hash_tagged S h with ⟨h1, _⟩ | c
      · exact absurd h1 (by decide)
      · exact .inr c
  | d, .node hv l r, s :: rest, term, hw, h => by
      simp only [climb, T.hashOf, WF] at h hw; rw [hw.1] at h
      simp only [proveAt]
      cases hb : S.bit k d
      · simp only [hb] at h ⊢
        rcases hash_tagged S h with ⟨_, hx⟩ | c
        · exact climb_sound k (d + 1) l rest term hw.2.1 (hN _ _ _ _ hx).1
        · exact .inr c
      · simp only [hb] at h ⊢
        rcases hash_tagged S h with ⟨_, hx⟩ | c
        · exact climb_sound k (d + 1) r rest term hw.2.2 (hN _ _ _ _ hx).2
        · exact .inr c

variable [DecidableEq D]

/-- **Inclusion is sound.** A proof that verifies against a well-formed trie's root shows the
digest of the value the trie holds at the key, or the hash has a collision. -/
theorem inclusion_sound {t : T K V D} {k : K} {dig : D} {p : Proof K D} (hw : WF S t)
    (hv : verifyInclusion S (t.hashOf S) k dig p = true) :
    (∃ v, t.get S k = some v ∧ S.vdigest v = dig) ∨ Coll S := by
  unfold verifyInclusion at hv
  cases ht : p.term with
  | none => simp [ht] at hv
  | some kds =>
      simp only [ht, Bool.and_eq_true, decide_eq_true_eq] at hv
      rcases climb_sound S hL hN k 0 t p.sibs (some kds) hw hv.2.2 with he | c
      · have hg := getAt_proveAt S k 0 t
        rw [← he] at hg; simp only at hg; rw [hv.2.1] at hg
        cases hget : getAt S k 0 t with
        | none => simp [hget] at hg
        | some v => exact .inl ⟨v, hget, by simpa [hget] using hg⟩
      · exact .inr c

/-- **Exclusion is sound.** A proof of absence that verifies against a well-formed trie's root
means the trie holds nothing at the key, or the hash has a collision. -/
theorem exclusion_sound {t : T K V D} {k : K} {p : Proof K D} (hw : WF S t)
    (hv : verifyExclusion S (t.hashOf S) k p = true) : t.get S k = none ∨ Coll S := by
  unfold verifyExclusion at hv
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hv
  rcases climb_sound S hL hN k 0 t p.sibs p.term hw hv.2 with he | c
  · have hg := getAt_proveAt S k 0 t
    rw [← he] at hg
    cases ht : p.term with
    | none => simp only [ht] at hg; exact .inl (by simpa [T.get] using hg)
    | some kds =>
        have hn := hv.1.2; simp only [ht, Option.isNone_iff_eq_none] at hn
        simp only [ht, hn] at hg; exact .inl (by simpa [T.get] using hg)
  · exact .inr c

omit hL hN

/-! ## Every trie the operations build is well formed, shallow, and proves what it holds -/

/-- No node at or below `depth`: every proof path is at most `depth` long. -/
def Shallow : Nat → T K V D → Prop
  | _, .empty => True
  | _, .leaf _ _ => True
  | d, .node _ l r => d < S.depth ∧ Shallow (d + 1) l ∧ Shallow (d + 1) r

omit [DecidableEq K] [DecidableEq D] in
theorem wf_mkLeaf (kvs : List (K × V)) : WF S (mkLeaf S kvs) := rfl

omit [DecidableEq K] [DecidableEq D] in
theorem wf_mkNode {l r : T K V D} (hl : WF S l) (hr : WF S r) : WF S (mkNode S l r) :=
  ⟨rfl, hl, hr⟩

omit [DecidableEq K] [DecidableEq D] in
theorem wf_build : ∀ (f d : Nat) (kvs : List (K × V)), WF S (build S f d kvs)
  | _, _, [] => by simp [build, WF]
  | f, _, [x] => by cases f <;> exact wf_mkLeaf S _
  | 0, _, a :: b :: rest => wf_mkLeaf S _
  | f + 1, d, a :: b :: rest => wf_mkNode S (wf_build f (d + 1) _) (wf_build f (d + 1) _)

omit [DecidableEq K] [DecidableEq D] in
theorem shallow_build : ∀ (f d : Nat) (kvs : List (K × V)), f ≤ S.depth - d → Shallow S d (build S f d kvs)
  | _, _, [], _ => by simp [build, Shallow]
  | f, _, [x], _ => by cases f <;> simp [build, mkLeaf, Shallow]
  | 0, _, a :: b :: rest, _ => by simp [build, mkLeaf, Shallow]
  | f + 1, d, a :: b :: rest, h => by
      simp only [build, mkNode, Shallow]
      exact ⟨by omega, shallow_build f (d + 1) _ (by omega), shallow_build f (d + 1) _ (by omega)⟩

omit [DecidableEq D] in
theorem wf_insAt (k : K) (v : V) : ∀ (d : Nat) (t : T K V D), WF S t → WF S (insAt S k v d t)
  | _, .empty, _ => wf_mkLeaf S _
  | d, .leaf _ kvs, _ => by
      simp only [insAt]; split
      · exact wf_mkLeaf S _
      · exact wf_build S _ _ _
  | d, .node _ l r, hw => by
      simp only [insAt]
      cases S.bit k d
      · exact wf_mkNode S (wf_insAt k v (d + 1) l hw.2.1) hw.2.2
      · exact wf_mkNode S hw.2.1 (wf_insAt k v (d + 1) r hw.2.2)

omit [DecidableEq D] in
theorem shallow_insAt (k : K) (v : V) :
    ∀ (d : Nat) (t : T K V D), Shallow S d t → Shallow S d (insAt S k v d t)
  | _, .empty, _ => by simp [insAt, mkLeaf, Shallow]
  | d, .leaf _ kvs, _ => by
      simp only [insAt]; split
      · simp [mkLeaf, Shallow]
      · exact shallow_build S _ _ _ (Nat.le_refl _)
  | d, .node _ l r, hs => by
      simp only [insAt]
      cases S.bit k d
      · exact ⟨hs.1, shallow_insAt k v (d + 1) l hs.2.1, hs.2.2⟩
      · exact ⟨hs.1, hs.2.1, shallow_insAt k v (d + 1) r hs.2.2⟩

omit [DecidableEq D] in
theorem wf_insert {t : T K V D} (k : K) (v : V) (h : WF S t) : WF S (t.insert S k v) :=
  wf_insAt S k v 0 t h

omit [DecidableEq D] in
theorem shallow_insert {t : T K V D} (k : K) (v : V) (h : Shallow S 0 t) :
    Shallow S 0 (t.insert S k v) :=
  shallow_insAt S k v 0 t h

omit [DecidableEq K] [DecidableEq D] in
theorem climb_proveAt (k : K) : ∀ (d : Nat) (t : T K V D), WF S t →
    climb S k d (proveAt S k d t).sibs (termHash S (proveAt S k d t).term) = t.hashOf S
  | _, .empty, _ => rfl
  | _, .leaf _ kvs, hw => by simp only [proveAt, climb, termHash, T.hashOf]; exact hw.symm
  | d, .node _ l r, hw => by
      simp only [proveAt, T.hashOf]
      cases hb : S.bit k d
      · simp only [climb, hb]; rw [climb_proveAt k (d + 1) l hw.2.1]; exact hw.1.symm
      · simp only [climb, hb]; rw [climb_proveAt k (d + 1) r hw.2.2]; exact hw.1.symm

omit [DecidableEq K] [DecidableEq D] in
theorem proveAt_length (k : K) : ∀ (d : Nat) (t : T K V D), Shallow S d t →
    (proveAt S k d t).sibs.length ≤ S.depth - d
  | _, .empty, _ => by simp [proveAt]
  | _, .leaf _ _, _ => by simp [proveAt]
  | d, .node _ l r, hs => by
      have hl := proveAt_length k (d + 1) l hs.2.1
      have hr := proveAt_length k (d + 1) r hs.2.2
      have h1 := hs.1
      simp only [proveAt]
      cases S.bit k d <;> simp only [List.length_cons] <;> omega

/-- **A trie proves what it holds.** -/
theorem prove_includes {t : T K V D} {k : K} {v : V} (hw : WF S t) (hs : Shallow S 0 t)
    (hg : t.get S k = some v) : verifyInclusion S (t.hashOf S) k (S.vdigest v) (t.prove S k) = true := by
  have hp := getAt_proveAt S k 0 t
  have hc := climb_proveAt S k 0 t hw
  have hl := proveAt_length S k 0 t hs
  unfold T.get at hg; unfold T.prove verifyInclusion
  rw [hg] at hp
  cases ht : (proveAt S k 0 t).term with
  | none => simp [ht] at hp
  | some kds =>
      simp only [ht] at hp hc
      simp only [Bool.and_eq_true, decide_eq_true_eq, ← hp]
      exact ⟨by omega, by simp, hc⟩

/-- **A trie proves what it does not hold.** -/
theorem prove_excludes {t : T K V D} {k : K} (hw : WF S t) (hs : Shallow S 0 t)
    (hg : t.get S k = none) : verifyExclusion S (t.hashOf S) k (t.prove S k) = true := by
  have hp := getAt_proveAt S k 0 t
  have hc := climb_proveAt S k 0 t hw
  have hl := proveAt_length S k 0 t hs
  unfold T.get at hg; unfold T.prove verifyExclusion
  rw [hg] at hp
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by omega, ?_⟩, hc⟩
  cases ht : (proveAt S k 0 t).term with
  | none => rfl
  | some kds => simp only [ht] at hp; simp [← hp]

end Nanodregg.Kernel.Trie
