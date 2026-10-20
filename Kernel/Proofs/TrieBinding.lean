import Kernel.TrieBinding
import Kernel.Proofs.Cells
import Kernel.Proofs.RowsHeadRead

namespace Nanodregg.Kernel.Trie
variable {K V D : Type} (S : Spec K V D)

theorem hash_rootPre (t : T K V D) (hw : WF S t) :
    S.hash (rootPre S t) = t.hashOf S := by
  cases t with
  | empty => rfl
  | leaf h kvs => exact hw.symm
  | node h b rep l r => exact hw.2.1.symm

theorem rootPre_mem (t : T K V D) : rootPre S t ∈ nodePres S t := by
  cases t <;> simp [nodePres]

/-- Hashing induction binds the ordered key/value-digest listing under separation
of the actual node inputs. Representative caches are not hashed. -/
theorem digests_eq_of_root
    (hL : ∀ x y, leafBody S x = leafBody S y → x = y)
    (hN : ∀ a b c e, S.dbytes a ++ S.dbytes b = S.dbytes c ++ S.dbytes e → a = c ∧ b = e)
    (L : List ByteArray)
    (hs : ∀ a ∈ L, ∀ b ∈ L, S.hash a = S.hash b → a = b) :
    ∀ (t u : T K V D), WF S t → WF S u →
      (∀ x ∈ nodePres S t, x ∈ L) → (∀ x ∈ nodePres S u, x ∈ L) →
      t.hashOf S = u.hashOf S → digests S t.toList = digests S u.toList := by
  intro t
  induction t with
  | empty =>
      intro u ht hu hmt hmu he
      have hp := hs _ (hmt _ (rootPre_mem S _)) _ (hmu _ (rootPre_mem S _))
        ((hash_rootPre S _ ht).trans (he.trans (hash_rootPre S _ hu).symm))
      cases u with
      | empty => rfl
      | leaf h kvs => exact False.elim (by have := (tagged_inj hp).1; contradiction)
      | node h b rep l r => exact False.elim (by have := (tagged_inj hp).1; contradiction)
  | leaf h kvs =>
      intro u ht hu hmt hmu he
      have hp := hs _ (hmt _ (rootPre_mem S _)) _ (hmu _ (rootPre_mem S _))
        ((hash_rootPre S _ ht).trans (he.trans (hash_rootPre S _ hu).symm))
      cases u with
      | empty => exact False.elim (by have := (tagged_inj hp).1; contradiction)
      | leaf h' kvs' => exact hL _ _ (tagged_inj hp).2
      | node h' b rep l r => exact False.elim (by have := (tagged_inj hp).1; contradiction)
  | node h b rep l r ihl ihr =>
      intro u ht hu hmt hmu he
      have hp := hs _ (hmt _ (rootPre_mem S _)) _ (hmu _ (rootPre_mem S _))
        ((hash_rootPre S _ ht).trans (he.trans (hash_rootPre S _ hu).symm))
      cases u with
      | empty => exact False.elim (by have := (tagged_inj hp).1; contradiction)
      | leaf h' kvs' => exact False.elim (by have := (tagged_inj hp).1; contradiction)
      | node h' b' rep' l' r' =>
          have hn := node_bytes (Nat.lt_trans ht.1 S.depth_lt)
            (Nat.lt_trans hu.1 S.depth_lt) (tagged_inj hp).2
          have hd := hN _ _ _ _ hn.2
          have hl := ihl l' ht.2.2.1 hu.2.2.1
            (fun x hx => hmt x (by simp [nodePres, hx]))
            (fun x hx => hmu x (by simp [nodePres, hx])) hd.1
          have hr := ihr r' ht.2.2.2 hu.2.2.2
            (fun x hx => hmt x (by simp [nodePres, hx]))
            (fun x hx => hmu x (by simp [nodePres, hx])) hd.2
          change digests S (l.toList ++ r.toList) = digests S (l'.toList ++ r'.toList)
          simp only [digests, List.map_append] at hl hr ⊢
          rw [hl, hr]

end Nanodregg.Kernel.Trie

namespace Nanodregg.Kernel
variable {K V D : Type}

private theorem list_eq_of_digests (S : Trie.Spec K V D) :
    ∀ (a b : List (K × V)),
      (∀ p ∈ a, ∀ q ∈ b, S.vdigest p.2 = S.vdigest q.2 → p.2 = q.2) →
      Trie.digests S a = Trie.digests S b → a = b
  | [], [], _, _ => rfl
  | [], _ :: _, _, h => by simp [Trie.digests] at h
  | _ :: _, [], _, h => by simp [Trie.digests] at h
  | p :: a, q :: b, hv, h => by
      simp only [Trie.digests, List.map_cons, List.cons.injEq, Prod.mk.injEq] at h
      have hp : p = q := Prod.ext h.1.1 (hv p (by simp) q (by simp) h.1.2)
      have ht := list_eq_of_digests S a b
        (fun x hx y hy => hv x (by simp [hx]) y (by simp [hy])) h.2
      rw [hp, ht]

/-- Equal roots determine canonical tries, or the actual node/value inputs
of those two tries collide. No assertion of global collision resistance. -/
theorem HeadSound.root_binds {E : Env D} {S : Trie.Spec K V D}
    {Fits : V → Prop} {vpre : V → String × ByteArray}
    (hs : HeadSound E S Fits vpre) {t u : Trie.T K V D}
    (ht : Trie.Canon S 0 t) (hu : Trie.Canon S 0 u)
    (ft : ∀ p ∈ t.toList, Fits p.2) (fu : ∀ p ∈ u.toList, Fits p.2)
    (he : t.hashOf S = u.hashOf S) :
    t = u ∨ CollidesAmong E.hash (bindingPres S vpre t u) := by
  classical
  by_cases hc : CollidesAmong E.hash (bindingPres S vpre t u)
  · exact .inr hc
  have sep : Separates E.hash (bindingPres S vpre t u) := by
    intro p hp q hq heq
    by_cases hn : p = q
    · exact hn
    · exact False.elim (hc ⟨p, hp, q, hq, hn, heq⟩)
  have ns : ∀ a ∈ Trie.nodePres S t ++ Trie.nodePres S u,
      ∀ b ∈ Trie.nodePres S t ++ Trie.nodePres S u, S.hash a = S.hash b → a = b := by
    intro a ha b hb hab
    have hab' : E.hash domTrie a = E.hash domTrie b := by simpa [hs.hash_eq] using hab
    exact congrArg Prod.snd (sep (domTrie, a)
      (List.mem_append_left _ (List.mem_map_of_mem ha)) (domTrie, b)
      (List.mem_append_left _ (List.mem_map_of_mem hb)) hab')
  have hd := Trie.digests_eq_of_root S hs.body_inj hs.pair_inj _ ns t u ht.2.1 hu.2.1
    (fun x hx => List.mem_append_left _ hx) (fun x hx => List.mem_append_right _ hx) he
  refine .inl (Trie.eq_of_toList_eq S ht hu (list_eq_of_digests S _ _ ?_ hd))
  intro p hp q hq hv
  apply hs.vpre_inj (ft p hp) (fu q hq)
  apply sep (vpre p.2) (List.mem_append_right _
    (List.mem_map_of_mem (List.mem_append_left _ hp))) (vpre q.2)
    (List.mem_append_right _ (List.mem_map_of_mem (List.mem_append_right _ hq)))
  simpa only [hs.vdigest_eq] using hv

/-- The binding fact alone when the finite, explicit inputs are separated. -/
theorem HeadSound.root_binds_sep {E : Env D} {S : Trie.Spec K V D}
    {Fits : V → Prop} {vpre : V → String × ByteArray}
    (hs : HeadSound E S Fits vpre) {t u : Trie.T K V D}
    (ht : Trie.Canon S 0 t) (hu : Trie.Canon S 0 u)
    (ft : ∀ p ∈ t.toList, Fits p.2) (fu : ∀ p ∈ u.toList, Fits p.2)
    (he : t.hashOf S = u.hashOf S)
    (hsep : Separates E.hash (bindingPres S vpre t u)) : t = u :=
  hsep.elim (hs.root_binds ht hu ft fu he)

end Nanodregg.Kernel

namespace Nanodregg.Kernel.Receive
open Nanodregg.Kernel Nanodregg.Codec Nanodregg.Codec.Deployed

/-- Deployed cells: equal roots bind the entire trie, including cached digests. -/
theorem deployed_trie_root_binds {t u : Trie.T (Slot Digest) Leaf Digest}
    (ht : Trie.Canon (trieSpec env) 0 t) (hu : Trie.Canon (trieSpec env) 0 u)
    (ft : ∀ p ∈ t.toList, p.2.CellFit Codec.Kernel.Cell.Fits)
    (fu : ∀ p ∈ u.toList, p.2.CellFit Codec.Kernel.Cell.Fits)
    (he : t.hashOf (trieSpec env) = u.hashOf (trieSpec env)) :
    t = u ∨ CollidesAmong env.hash (bindingPres (trieSpec env) (leafPre env) t u) :=
  (cells_headSound deployed_lawful).root_binds ht hu ft fu he

/-- Deployed rows: the other roots-to-tries step needed by start_carry_commits. -/
theorem deployed_rows_root_binds {t u : Rows Digest}
    (ht : Trie.Canon (rowSpec env) 0 t) (hu : Trie.Canon (rowSpec env) 0 u)
    (ft : ∀ p ∈ t.toList, Codec.Kernel.RowLeaf.Fits p.2)
    (fu : ∀ p ∈ u.toList, Codec.Kernel.RowLeaf.Fits p.2)
    (he : t.hashOf (rowSpec env) = u.hashOf (rowSpec env)) :
    t = u ∨ CollidesAmong env.hash (bindingPres (rowSpec env) rowLeafPre t u) :=
  (row_headSound deployed_lawful).root_binds ht hu ft fu he

end Nanodregg.Kernel.Receive
