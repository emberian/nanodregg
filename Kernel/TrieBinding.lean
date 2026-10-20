/- Finite inputs for whole-trie binding, including the values behind leaf digests. -/
import Kernel.World

namespace Nanodregg.Kernel.Trie
variable {K V D : Type} (S : Spec K V D)

/-- The input at the root, read from the actual cached children. -/
def rootPre : T K V D → ByteArray
  | .empty => termPre S none
  | .leaf _ kvs => termPre S (some (digests S kvs))
  | .node _ b _ l r => nodePre S b (l.hashOf S) (r.hashOf S)

/-- All node/leaf inputs of the whole trie, in root-left-right order. -/
def nodePres : T K V D → List ByteArray
  | .empty => [rootPre S .empty]
  | .leaf h kvs => [rootPre S (.leaf h kvs)]
  | .node h b rep l r => rootPre S (.node h b rep l r) :: (nodePres l ++ nodePres r)

end Nanodregg.Kernel.Trie

namespace Nanodregg.Kernel
variable {K V D : Type}

/-- Both trees' node inputs and value inputs. Finite, built from these two tries only. -/
def bindingPres (S : Trie.Spec K V D) (vpre : V → String × ByteArray)
    (t u : Trie.T K V D) : List (String × ByteArray) :=
  trieIn (Trie.nodePres S t ++ Trie.nodePres S u) ++
    (t.toList ++ u.toList).map (fun p => vpre p.2)

end Nanodregg.Kernel
