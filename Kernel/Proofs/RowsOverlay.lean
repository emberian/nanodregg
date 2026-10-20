import Kernel.World
import Kernel.Proofs.Trie

namespace Nanodregg.Kernel
variable {K V D : Type}

theorem takeListU_seal (S : Trie.Spec K V D) :
    ∀ (u : Trie.U K V D) (n : Nat), takeListU n u = takeList n (u.seal S) := by
  intro u
  induction u with
  | clean t => intro n; rfl
  | leaf kvs => intro n; rfl
  | node b rep l r ihl ihr =>
      intro n
      simp only [takeListU, Trie.U.seal, Trie.mkNode, takeList]
      rw [ihl, ihr]

theorem underU_seal (S : Trie.Spec K V D) (pre : ByteArray) (n : Nat) :
    ∀ (u : Trie.U K V D), underU S pre n u = under S pre n (u.seal S) := by
  intro u
  induction u with
  | clean t => rfl
  | leaf kvs => rfl
  | node b rep l r ihl ihr =>
      simp only [underU, Trie.U.seal, Trie.mkNode, under]
      rw [ihl, ihr]
      split
      · rfl
      · split
        · exact takeListU_seal S (.node b rep l r) n
        · rfl

private theorem foldl_commutes {A B C : Type} (g : A → B) (f : A → C → A) (f' : B → C → B)
    (h : ∀ a c, g (f a c) = f' (g a) c) :
    ∀ (xs : List C) (a : A), g (xs.foldl f a) = xs.foldl f' (g a)
  | [], _ => rfl
  | x :: xs, a => by simp only [List.foldl_cons]; rw [foldl_commutes g f f' h xs (f a x), h]

variable [DecidableEq D]

/-- Unconditional equality of the trie and freed weight; no invariant or new
hypothesis is needed by rowsRun_eq or any of its consumers. -/
theorem dropHeadsU_seal (E : Env D) (t : Turn D) (acc : Trie.U (RowSlot D) RowLeaf D × Nat) :
    Prod.map (fun u => u.seal (rowSpec E)) id (dropHeadsU E t acc) =
      dropHeads E t (Prod.map (fun u => u.seal (rowSpec E)) id acc) := by
  unfold dropHeadsU dropHeads
  apply foldl_commutes
  intro acc x
  cases x.act <;> try rfl
  rw [underU_seal]
  apply foldl_commutes
  intro acc p
  simp only [Prod.map, id_eq, Trie.seal_retainAtU]

end Nanodregg.Kernel
