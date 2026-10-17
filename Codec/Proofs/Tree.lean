import Codec.Tree
import Codec.Proofs.Varint

/-! # The tree codec is lawful, hence canonical

`tree_lawful max depth fits : Lawful (Stream.tree max depth fits)`: every tree that fits is read back
from its bytes, and whatever is read IS the bytes of what was read. Proof: induction on the depth,
with an inner induction over a node's children. -/

namespace Nanodregg.Codec

open Stream

namespace Tree

theorem putD_eq (d : Nat) (t : Tree) (buf : ByteArray) : putD d t buf = buf ++ putD d t ByteArray.empty := by
  induction d generalizing t buf with
  | zero => simp [putD, ByteArray.append_empty]
  | succ d ih =>
    obtain ⟨tag, p, cs⟩ := t
    have fold : ∀ (l : List Tree) (out : ByteArray),
        l.foldl (fun o c => putD d c o) out = out ++ l.foldl (fun o c => putD d c o) ByteArray.empty := by
      intro l
      induction l with
      | nil => intro out; simp [ByteArray.append_empty]
      | cons c l ihl =>
        intro out
        simp only [List.foldl_cons]
        rw [ihl, ihl (putD d c ByteArray.empty), ih c out, ByteArray.append_assoc]
    simp only [putD]
    rw [fold cs, fold cs (putVarint _ _), putVarint_eq _ (putVarint _ _ ++ _), putVarint_eq _ (buf.push _),
      putVarint_eq _ (putVarint _ (ByteArray.empty.push _) ++ _), putVarint_eq _ (ByteArray.empty.push _),
      push_eq_append, push_eq_append]
    simp only [ByteArray.append_assoc, ByteArray.empty_append]

theorem kidsBytes_nil (d : Nat) : kidsBytes d [] = ByteArray.empty := rfl

theorem foldl_putD (d : Nat) (l : List Tree) (out : ByteArray) :
    l.foldl (fun o c => putD d c o) out = out ++ kidsBytes d l := by
  unfold kidsBytes
  induction l generalizing out with
  | nil => simp [ByteArray.append_empty]
  | cons c l ihl =>
    simp only [List.foldl_cons]
    rw [ihl, ihl (putD d c ByteArray.empty), putD_eq d c out, ByteArray.append_assoc]

theorem kidsBytes_cons (d : Nat) (c : Tree) (l : List Tree) :
    kidsBytes d (c :: l) = putD d c ByteArray.empty ++ kidsBytes d l := by
  simp only [kidsBytes, List.foldl_cons]
  rw [foldl_putD]; rfl

theorem putD_node (d : Nat) (tag : UInt8) (p : ByteArray) (cs : List Tree) :
    putD (d + 1) (node tag p cs) ByteArray.empty =
      u8.bytes tag ++ varint.bytes p.size ++ p ++ varint.bytes cs.length ++ kidsBytes d cs := by
  simp only [putD]
  rw [foldl_putD, putVarint_eq, putVarint_eq, push_eq_append, ByteArray.empty_append]
  rfl

theorem sizeD_eq (d : Nat) (t : Tree) : sizeD d t = (putD d t ByteArray.empty).size := by
  induction d generalizing t with
  | zero => rfl
  | succ d ih =>
    obtain ⟨tag, p, cs⟩ := t
    have fold : ∀ (l : List Tree) (k : Nat), l.foldl (fun n c => n + sizeD d c) k = k + (kidsBytes d l).size := by
      intro l
      induction l with
      | nil => intro k; simp [kidsBytes_nil]
      | cons c l ihl => intro k; rw [List.foldl_cons, ihl, kidsBytes_cons, ByteArray.size_append, ih, Nat.add_assoc]
    rw [putD_node]
    simp only [sizeD, fold, ByteArray.size_append, u8_size, varintSize_eq]

theorem getD_of_occurs (max limit : Nat) (small : max < 2 ^ 32) (b : ByteArray) (d : Nat) :
    ∀ (t : Tree) (h : t.fits max d = true) (i : Nat), OccursAt b i (putD d t ByteArray.empty) →
      getD max limit b d i = .ok (⟨t, h⟩, i + (putD d t ByteArray.empty).size) := by
  induction d with
  | zero => intro t h; simp [fits] at h
  | succ d ih =>
    have kids : ∀ (l : List Tree), (∀ c ∈ l, c.fits max d = true) → ∀ (acc : Array (Fitting max d))
        (pos : Nat), OccursAt b pos (kidsBytes d l) →
        ∃ a, getKids max limit b d l.length pos acc = .ok (a, pos + (kidsBytes d l).size) ∧
          a.toList.map Subtype.val = acc.toList.map Subtype.val ++ l := by
      intro l
      induction l with
      | nil => intro _ acc pos _; exact ⟨acc, by simp [getKids, kidsBytes_nil], by simp⟩
      | cons c l ihl =>
        intro hf acc pos ho
        rw [kidsBytes_cons] at ho ⊢
        obtain ⟨o1, o2⟩ := occursAt_append.mp ho
        have hc := hf c (List.mem_cons_self ..)
        obtain ⟨a, ga, ha⟩ := ihl (fun x hx => hf x (List.mem_cons_of_mem _ hx)) (acc.push ⟨c, hc⟩) _ o2
        refine ⟨a, ?_, ?_⟩
        · rw [List.length_cons, getKids, ih c hc pos o1]
          simp only [ga, ByteArray.size_append, Nat.add_assoc]
        · rw [ha]; simp
    intro t h i hocc
    obtain ⟨tag, p, cs⟩ := t
    have h' := h
    simp only [fits, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h'
    obtain ⟨⟨hp, hcs⟩, hk⟩ := h'
    rw [putD_node] at hocc ⊢
    obtain ⟨h4, hK⟩ := occursAt_append.mp hocc
    obtain ⟨h3, hC⟩ := occursAt_append.mp h4
    obtain ⟨h2, hP⟩ := occursAt_append.mp h3
    obtain ⟨hA, hB⟩ := occursAt_append.mp h2
    simp only [ByteArray.size_append, u8_size] at hK hC hP hB
    have g1 := u8_lawful.get_of_occurs _ _ _ hA
    have g2 := varint_lawfulOn.get_of_occurs _ _ _ (by omega) hB
    have g3 := varint_lawfulOn.get_of_occurs _ _ _ (by omega) hC
    simp only [u8_size] at g1
    obtain ⟨a, ga, ha⟩ := kids cs hk #[] _ hK
    have hpe := hP.2
    have hpb := hP.1
    have hal : a.size ≤ max := by
      have := congrArg List.length ha
      simp at this; omega
    simp only [ByteArray.size_append, u8_size, Nat.add_assoc] at g1 g2 g3 ga hpe hpb ⊢
    rw [getD]
    simp only [g1, g2, hp, hpb, ↓reduceDIte, g3, hcs, ↓reduceIte, ga, hal, hpe, Nat.add_assoc]
    simp only [ha, List.map_nil, List.nil_append]

theorem occurs_of_getD (max limit : Nat) (b : ByteArray) (d : Nat) :
    ∀ (i : Nat) (t : Fitting max d) (j : Nat), getD max limit b d i = .ok (t, j) →
      j = i + (putD d t.val ByteArray.empty).size ∧ OccursAt b i (putD d t.val ByteArray.empty) := by
  induction d with
  | zero => intro i t j h; rw [getD] at h; cases h
  | succ d ih =>
    have kids : ∀ (n pos : Nat) (acc a : Array (Fitting max d)) (r : Nat), pos ≤ b.size →
        getKids max limit b d n pos acc = .ok (a, r) →
        ∃ l : List (Fitting max d), a = acc ++ l.toArray ∧ l.length = n ∧
          r = pos + (kidsBytes d (l.map Subtype.val)).size ∧ OccursAt b pos (kidsBytes d (l.map Subtype.val)) := by
      intro n
      induction n with
      | zero =>
        intro pos acc a r hpos h
        rw [getKids] at h
        cases h
        exact ⟨[], by simp, rfl, by simp [kidsBytes_nil],
          ⟨by simp [kidsBytes_nil]; omega, by simp [kidsBytes_nil, ByteArray.extract_same]⟩⟩
      | succ n ihn =>
        intro pos acc a r hpos h
        rw [getKids] at h
        split at h
        · rename_i c j hc
          obtain ⟨rfl, oc⟩ := ih pos c j hc
          obtain ⟨l, rfl, hl, rfl, ol⟩ := ihn _ (acc.push c) a r (by have := oc.1; omega) h
          refine ⟨c :: l, by simp, by simp [hl], ?_, ?_⟩
          · simp only [List.map_cons, kidsBytes_cons, ByteArray.size_append, Nat.add_assoc]
          · simp only [List.map_cons, kidsBytes_cons]; exact occursAt_append.mpr ⟨oc, ol⟩
        · cases h
    intro i t j h
    rw [getD] at h
    split at h
    · cases h
    · rename_i tag j1 h1
      split at h
      · cases h
      · rename_i n k h2
        split at h
        · rename_i hn
          split at h
          · rename_i hb
            split at h
            · cases h
            · rename_i m l h3
              split at h
              · rename_i hm
                split at h
                · rename_i cs r h4
                  split at h
                  · rename_i hl
                    cases h
                    obtain ⟨rfl, oA⟩ := u8_lawful.occurs_of_get h1
                    obtain ⟨_, rfl, oB⟩ := varint_lawfulOn.occurs_of_get h2
                    obtain ⟨_, rfl, oC⟩ := varint_lawfulOn.occurs_of_get h3
                    obtain ⟨ks, rfl, hks, rfl, oK⟩ := kids _ _ _ _ _ (by have := oC.1; omega) h4
                    have sA : (u8.bytes tag).size = 1 := rfl
                    simp only [sA] at oB oC oK hb ⊢
                    have hsz : (b.extract (i + 1 + (varint.bytes n).size)
                        (i + 1 + (varint.bytes n).size + n)).size = n := by
                      rw [ByteArray.size_extract]; omega
                    have hmap : (#[] ++ ks.toArray).toList.map Subtype.val = ks.map Subtype.val := by simp
                    simp only [hmap]
                    rw [putD_node]
                    have hlen : (ks.map Subtype.val).length = m := by simp [hks]
                    simp only [hsz, hlen]
                    refine ⟨by simp only [ByteArray.size_append, hsz, sA]; omega, ?_⟩
                    refine occursAt_append.mpr ⟨occursAt_append.mpr ⟨occursAt_append.mpr
                      ⟨occursAt_append.mpr ⟨oA, ?_⟩, ?_⟩, ?_⟩, ?_⟩
                    · rw [sA]; exact oB
                    · rw [ByteArray.size_append, sA, ← Nat.add_assoc]
                      exact ⟨by rw [hsz]; exact hb, by rw [hsz]⟩
                    · rw [ByteArray.size_append, ByteArray.size_append, sA, hsz,
                        show i + (1 + (varint.bytes n).size + n) = i + 1 + (varint.bytes n).size + n by omega]
                      exact oC
                    · rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_append, sA, hsz,
                        show i + (1 + (varint.bytes n).size + n + (varint.bytes m).size) =
                          i + 1 + (varint.bytes n).size + n + (varint.bytes m).size by omega]
                      exact oK
                  · cases h
                · cases h
              · cases h
          · cases h
        · cases h

end Tree

namespace Stream

theorem tree_lawful (max depth : Nat) (fits : max < 2 ^ 32) : Lawful (tree max depth fits) where
  put_eq t buf := Tree.putD_eq depth t.val buf
  size_eq t := Tree.sizeD_eq depth t.val
  get_of_occurs t b i h := Tree.getD_of_occurs max depth fits b depth t.val t.2 i h
  occurs_of_get {b i v j} h := Tree.occurs_of_getD max depth b depth i v j h

end Stream
end Nanodregg.Codec
