import Codec.World
import Codec.Proofs.Raw
import Kernel.Proofs.TrieMap

/-!
# A trie proof's wire is canonical (KERNEL-49 (a), CODEC-35)

`proof S kc dc` writes a `Trie.Proof` (what its path ends at, then each sibling with the bit its node
branches on) and reads one back only when it is `proofShaped`: the bits ascend below `S.depth`
(`Trie.ascends S 0`), and it ends at a non-empty leaf or at the empty trie with no sibling.
* `proof_lawfulOn`: lawful on exactly `ProofFits` (the entries' and siblings' parts in their codecs'
  domains, at most `worldMax` entries, and `proofShaped`; the length and u16 bounds follow from the
  ascent, `Trie.ascends_length` / `ascends_lt`), so `decode b = .ok p ↔ b = bytes p`.
* `prove_fits`: every proof a canonical trie makes is in that domain, so it round-trips.
* `proof_decode_inclusion_iff` / `proof_decode_exclusion_iff`: on a decoded proof the verifiers'
  first check (the ascent) holds, and what is left is the leaf lookup and the climb.
* `proof_get_refused`: a path that is not `proofShaped` is refused by name.
-/

namespace Nanodregg.Codec.Kernel

open Nanodregg.Kernel Nanodregg.Codec.Stream

variable {K V D : Type} [DecidableEq K]

omit [DecidableEq K] in
/-- Every bit of an ascending path is below the depth. -/
theorem ascends_lt (S : Trie.Spec K V D) :
    ∀ (d : Nat) (l : List (Nat × D)), Trie.ascends S d l = true → ∀ x ∈ l, x.1 < S.depth
  | _, [], _, _, hx => by simp at hx
  | d, (b, s) :: rest, h, x, hx => by
    simp only [Trie.ascends, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases List.mem_cons.mp hx with rfl | hx
    · exact h.1.2
    · exact ascends_lt S (b + 1) rest h.2 x hx

/-- The proofs the wire carries: the leaf's entries (at most `worldMax`) with keys and digests in their
codecs' domains, every sibling's digest in its codec's domain, and the shape of a path a trie can show. -/
def ProofFits (S : Trie.Spec K V D) (PK : K → Prop) (PD : D → Prop) (p : Trie.Proof K D) : Prop :=
  OptionFits (fun l => l.length ≤ worldMax ∧ ∀ x ∈ l, PK x.1 ∧ PD x.2) p.term ∧
    (∀ x ∈ p.sibs, PD x.2) ∧ proofShaped S (p.term, p.sibs) = true

/-- **`kernel/proof` is lawful on exactly `ProofFits`.** -/
theorem proof_lawfulOn (S : Trie.Spec K V D) {PK : K → Prop} {PD : D → Prop} {kc : Stream K}
    {dc : Stream D} (hk : LawfulOn PK kc) (hd : LawfulOn PD dc) :
    LawfulOn (ProofFits S PK PD) (proof S kc dc) := by
  have hdepth : S.depth < 2 ^ 32 := Nat.lt_trans S.depth_lt (by decide)
  have hw := product_lawfulOn (option_lawfulOn (rawList_lawfulOn (product_lawfulOn hk hd) worldMax (by decide)))
    (rawList_lawfulOn (product_lawfulOn nat16_lawfulOn hd) S.depth hdepth)
  refine (refine_lawfulOn_where hw "kernel/proof" (Q := fun p => proofShaped S (p.term, p.sibs) = true)
    ?_ ?_ ?_).mono ?_ ?_
  · intro y _ hq; simp [hq]
  · intro x y h
    split at h
    · cases h; rfl
    · cases h
  · intro x y h
    split at h
    · rename_i hq; cases h; exact hq
    · cases h
  · rintro p ⟨⟨ht, hs⟩, ha⟩
    exact ⟨ht, fun x hx => (hs.2 x hx).2, ha⟩
  · rintro p ⟨ht, hs, ha⟩
    have hasc : Trie.ascends S 0 p.sibs = true := by
      simp only [proofShaped, Bool.and_eq_true] at ha; exact ha.1
    refine ⟨⟨ht, ?_, fun x hx => ⟨?_, hs x hx⟩⟩, ha⟩
    · have := Trie.ascends_length S 0 p.sibs hasc; omega
    · exact Nat.lt_trans (ascends_lt S 0 p.sibs hasc x hx) S.depth_lt

omit [DecidableEq K] in
/-- What a proof's path ends at is (the digests of) a contiguous run of the trie's listing. -/
theorem proveAt_term_sublist (S : Trie.Spec K V D) (k : K) :
    ∀ (t : Trie.T K V D) (kds : List (K × D)), (Trie.proveAt S k t).term = some kds →
      ∃ kvs, kds = Trie.digests S kvs ∧ kvs.Sublist t.toList
  | .empty, _, h => by simp [Trie.proveAt] at h
  | .leaf _ kvs, kds, h => by
    simp only [Trie.proveAt, Option.some.injEq] at h
    exact ⟨kvs, h.symm, by simp [Trie.T.toList]⟩
  | .node _ b _ l r, kds, h => by
    simp only [Trie.proveAt] at h
    split at h
    · obtain ⟨kvs, e, hs⟩ := proveAt_term_sublist S k r kds h
      exact ⟨kvs, e, hs.trans (by simp [Trie.T.toList])⟩
    · obtain ⟨kvs, e, hs⟩ := proveAt_term_sublist S k l kds h
      exact ⟨kvs, e, hs.trans (by simp [Trie.T.toList])⟩

omit [DecidableEq K] in
/-- Below a canonical shape, a non-empty subtree's proof ends at a non-empty leaf. -/
theorem proveAt_term_ne (S : Trie.Spec K V D) (k : K) :
    ∀ (d : Nat) (t : Trie.T K V D), Trie.Shape S d t → t ≠ .empty →
      ∃ kds, kds ≠ [] ∧ (Trie.proveAt S k t).term = some kds
  | _, .empty, _, h => absurd rfl h
  | _, .leaf _ kvs, hs, _ => ⟨Trie.digests S kvs, by simpa [Trie.digests] using hs.1, rfl⟩
  | _, .node _ b _ l r, hs, _ => by
    obtain ⟨-, -, hrep, hrne, hl, hr⟩ := hs
    simp only [Trie.proveAt]
    split
    · exact proveAt_term_ne S k (b + 1) r hr (by rintro rfl; simp [Trie.T.toList] at hrne)
    · exact proveAt_term_ne S k (b + 1) l hl (by rintro rfl; simp [Trie.T.toList] at hrep)

/-- **Every proof a canonical trie makes is on the wire's domain**, so `kernel/proof` reads it back:
the keys it shows are the trie's (in the key codec's domain when every listed key is), and the
digest codec is total. -/
theorem prove_fits (S : Trie.Spec K V D) {PK : K → Prop} {t : Trie.T K V D} (k : K)
    (hc : Trie.Canon S 0 t) (hlen : t.toList.length ≤ worldMax) (hk : ∀ p ∈ t.toList, PK p.1) :
    ProofFits S PK (fun _ => True) (t.prove S k) := by
  have hasc := Trie.ascends_proveAt S k 0 t (Trie.shallow_of_shape S 0 t hc.2.2)
  cases ht : t with
  | empty => simp [ProofFits, Trie.T.prove, Trie.proveAt, proofShaped, OptionFits, Trie.ascends]
  | leaf h kvs =>
    rw [ht] at hc hasc hk hlen
    obtain ⟨kds, hne, he⟩ := proveAt_term_ne S k 0 _ hc.2.2 (by simp)
    obtain ⟨kvs', e, hsub⟩ := proveAt_term_sublist S k _ kds he
    refine ⟨?_, fun _ _ => trivial, ?_⟩
    · show OptionFits _ (Trie.proveAt S k (.leaf h kvs)).term
      rw [he]
      refine ⟨?_, fun x hx => ⟨?_, trivial⟩⟩
      · rw [e, Trie.digests, List.length_map]; exact Nat.le_trans hsub.length_le hlen
      · rw [e, Trie.digests, List.mem_map] at hx
        obtain ⟨q, hq, rfl⟩ := hx
        exact hk q (hsub.subset hq)
    · show proofShaped S ((Trie.proveAt S k (.leaf h kvs)).term, (Trie.proveAt S k (.leaf h kvs)).sibs) = true
      simp only [proofShaped, he, Bool.and_eq_true]
      exact ⟨hasc, by simpa using hne⟩
  | node h b rep l r =>
    rw [ht] at hc hasc hk hlen
    obtain ⟨kds, hne, he⟩ := proveAt_term_ne S k 0 _ hc.2.2 (by simp)
    obtain ⟨kvs', e, hsub⟩ := proveAt_term_sublist S k _ kds he
    refine ⟨?_, fun _ _ => trivial, ?_⟩
    · show OptionFits _ (Trie.proveAt S k (.node h b rep l r)).term
      rw [he]
      refine ⟨?_, fun x hx => ⟨?_, trivial⟩⟩
      · rw [e, Trie.digests, List.length_map]; exact Nat.le_trans hsub.length_le hlen
      · rw [e, Trie.digests, List.mem_map] at hx
        obtain ⟨q, hq, rfl⟩ := hx
        exact hk q (hsub.subset hq)
    · show proofShaped S ((Trie.proveAt S k (.node h b rep l r)).term,
          (Trie.proveAt S k (.node h b rep l r)).sibs) = true
      simp only [proofShaped, he, Bool.and_eq_true]
      exact ⟨hasc, by simpa using hne⟩

/-- A decoded proof's bits ascend below the depth: the first check `verifyInclusion` and
`verifyExclusion` make holds of every proof `kernel/proof` reads. -/
theorem proof_decode_ascends (S : Trie.Spec K V D) {PK : K → Prop} {PD : D → Prop} {kc : Stream K}
    {dc : Stream D} (hk : LawfulOn PK kc) (hd : LawfulOn PD dc) {b : ByteArray} {p : Trie.Proof K D}
    (h : (proof S kc dc).decode b = .ok p) : Trie.ascends S 0 p.sibs = true := by
  have := (((proof_lawfulOn S hk hd).decode_eq_ok_iff).mp h).1.2.2
  simp only [proofShaped, Bool.and_eq_true] at this
  exact this.1

/-- **On a decoded proof, inclusion is the leaf lookup and the climb.** -/
theorem proof_decode_inclusion_iff [DecidableEq D] (S : Trie.Spec K V D) {PK : K → Prop} {PD : D → Prop}
    {kc : Stream K} {dc : Stream D} (hk : LawfulOn PK kc) (hd : LawfulOn PD dc) {b : ByteArray}
    {p : Trie.Proof K D} (h : (proof S kc dc).decode b = .ok p) (root : D) (k : K) (dig : D) :
    Trie.verifyInclusion S root k dig p = true ↔
      ∃ kds, p.term = some kds ∧ Trie.find k kds = some dig ∧ Trie.climb S k p.sibs (Trie.termHash S p.term) = root := by
  have ha := proof_decode_ascends S hk hd h
  unfold Trie.verifyInclusion
  rw [ha, Bool.true_and]
  cases ht : p.term with
  | none => simp
  | some kds => simp

/-- **On a decoded proof, exclusion is the leaf's miss (or the empty trie) and the climb.** -/
theorem proof_decode_exclusion_iff [DecidableEq D] (S : Trie.Spec K V D) {PK : K → Prop} {PD : D → Prop}
    {kc : Stream K} {dc : Stream D} (hk : LawfulOn PK kc) (hd : LawfulOn PD dc) {b : ByteArray}
    {p : Trie.Proof K D} (h : (proof S kc dc).decode b = .ok p) (root : D) (k : K) :
    Trie.verifyExclusion S root k p = true ↔
      (∀ kds, p.term = some kds → Trie.find k kds = none) ∧
        Trie.climb S k p.sibs (Trie.termHash S p.term) = root := by
  have ha := proof_decode_ascends S hk hd h
  unfold Trie.verifyExclusion
  rw [ha, Bool.true_and]
  cases ht : p.term with
  | none => simp
  | some kds => simp

/-- **A path that is not `proofShaped` is refused `kernel/proof`, by name.** -/
theorem proof_get_refused (S : Trie.Spec K V D) {kc : Stream K} {dc : Stream D} {b : ByteArray}
    {i j : Nat} {x : Option (List (K × D)) × List (Nat × D)}
    (h : (proofWire S.depth kc dc).get b i = .ok (x, j)) (ha : proofShaped S x = false) :
    (proof S kc dc).get b i = .error (.rejected i "kernel/proof") := by
  simp [proof, refine, h, ha]

end Nanodregg.Codec.Kernel
