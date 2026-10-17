/-
# Kernel.Trie — a persistent binary Merkle trie (KERNEL-23)

The authenticated map the World's cells and spent nullifiers live in. Keys are routed by their bits
(`Spec.bit k d`: bit `d` of the key) down an UNCOMPRESSED binary trie: a subtree holding no key is
`empty`, one holding one key is a `leaf`, one holding more is a `node` whose children split them by
the next bit. The shape is therefore a function of the key set, not of the insertion order. A leaf
holds a LIST of entries only at `Spec.depth`, where keys whose bits agree that far can no longer be
told apart (an encoding that is not injective; the deployed one is). So `get` after `insert` is
exact for ANY bit function: correctness never rests on a hash or an encoding, only the proofs' size
does.

Every node caches its digest. One byte domain separates the three shapes: `empty = H(0)`,
`leaf = H(1 ‖ k ‖ digest v …)`, `node = H(2 ‖ left ‖ right)`. A node's depth is its position, so
the branching bit needs no committing: a proof's i-th sibling sits at depth i, and the side is the
key's bit i. That makes EXCLUSION proofs as sound as inclusion ones (Kernel.Proofs.Trie).

Work per `insert`: one path from the root to the key's leaf is rebuilt, one hash per node on it
(and one for its leaf); the empty subtree's digest is hashed at most once per turn (KERNEL-35).
-/
namespace Nanodregg.Kernel.Trie

/-- How a trie routes, hashes and encodes. -/
structure Spec (K V D : Type) where
  /-- bit `d` of a key -/
  bit : K → Nat → Bool
  /-- the depth below which a leaf holds one key -/
  depth : Nat
  hash : ByteArray → D
  dbytes : D → ByteArray
  kbytes : K → ByteArray
  /-- what a leaf commits to of a value -/
  vdigest : V → D

inductive T (K V D : Type) where
  | empty
  | leaf (h : D) (kvs : List (K × V))
  | node (h : D) (l r : T K V D)

/-- What a proof carries of the subtree it ends at: an empty side, or a leaf's entries as
(key, value digest). -/
structure Proof (K D : Type) where
  term : Option (List (K × D))
  /-- the siblings along the key's path, from the root down -/
  sibs : List D

variable {K V D : Type} (S : Spec K V D)

/-- A shape tag, then its bytes. -/
def tagged (t : UInt8) (b : ByteArray) : ByteArray := ⟨#[t]⟩ ++ b

def leafBody (kds : List (K × D)) : ByteArray :=
  kds.foldr (fun p acc => S.kbytes p.1 ++ S.dbytes p.2 ++ acc) ByteArray.empty

def emptyHash : D := S.hash (tagged 0 ByteArray.empty)
def leafHash (kds : List (K × D)) : D := S.hash (tagged 1 (leafBody S kds))
def nodeHash (l r : D) : D := S.hash (tagged 2 (S.dbytes l ++ S.dbytes r))

def digests (kvs : List (K × V)) : List (K × D) := kvs.map fun p => (p.1, S.vdigest p.2)

/-- The empty subtree's digest, forced at most once by whoever holds it (KERNEL-35). -/
abbrev EmptyDigest (D : Type) := Thunk D

/-- A subtree's digest. `e` is the empty subtree's, `emptyHash S` unless a caller passes its own
lazy copy: the mutation path makes one per `World.commitTrie` and forces it only if a path meets an
empty sibling, so an insert pays no hash for an empty sibling and a turn pays at most one. Every
theorem is stated at the default. -/
def T.hashOf (t : T K V D) (e : EmptyDigest D := Thunk.mk fun _ => emptyHash S) : D :=
  match t with
  | .empty => e.get
  | .leaf h _ => h
  | .node h _ _ => h

def mkLeaf (kvs : List (K × V)) : T K V D := .leaf (leafHash S (digests S kvs)) kvs

def mkNode (l r : T K V D) (e : EmptyDigest D := Thunk.mk fun _ => emptyHash S) : T K V D :=
  .node (nodeHash S (l.hashOf S e) (r.hashOf S e)) l r

variable [DecidableEq K]

/-- The value at `k` in a leaf's entries. -/
def find {α : Type} (k : K) (kvs : List (K × α)) : Option α := (kvs.find? fun p => p.1 = k).map (·.2)

/-- The value at `k`, walking from depth `d`. -/
def getAt (k : K) : Nat → T K V D → Option V
  | _, .empty => none
  | _, .leaf _ kvs => find k kvs
  | d, .node _ l r =>
      match S.bit k d with
      | true => getAt k (d + 1) r
      | false => getAt k (d + 1) l

/-- The canonical subtree at depth `d` holding `kvs` (`fuel` levels left before `depth`); `e` as in
`T.hashOf`. -/
def build (f d : Nat) (kvs : List (K × V)) (e : EmptyDigest D := Thunk.mk fun _ => emptyHash S) :
    T K V D :=
  match f, d, kvs with
  | _, _, [] => .empty
  | _, _, [x] => mkLeaf S [x]
  | 0, _, kvs => mkLeaf S kvs
  | f + 1, d, kvs =>
      mkNode S (build f (d + 1) (kvs.filter fun p => !S.bit p.1 d) e)
        (build f (d + 1) (kvs.filter fun p => S.bit p.1 d) e) e

/-- Set `k` to `v`, from depth `d`: one path rebuilt; `e` as in `T.hashOf`. -/
def insAt (k : K) (v : V) (d : Nat) (t : T K V D)
    (e : EmptyDigest D := Thunk.mk fun _ => emptyHash S) : T K V D :=
  match d, t with
  | _, .empty => mkLeaf S [(k, v)]
  | d, .leaf _ kvs =>
      if kvs.any (fun p => p.1 = k) then mkLeaf S (kvs.map fun p => if p.1 = k then (k, v) else p)
      else build S (S.depth - d) d (kvs ++ [(k, v)]) e
  | d, .node _ l r =>
      match S.bit k d with
      | true => mkNode S l (insAt k v (d + 1) r e) e
      | false => mkNode S (insAt k v (d + 1) l e) r e

/-- The proof for `k`, from depth `d`: the siblings down its path and what the path ends at; `e` as
in `T.hashOf` (an empty sibling costs at most one hash per proof). -/
def proveAt (k : K) (d : Nat) (t : T K V D) (e : EmptyDigest D := Thunk.mk fun _ => emptyHash S) :
    Proof K D :=
  match d, t with
  | _, .empty => ⟨none, []⟩
  | _, .leaf _ kvs => ⟨some (digests S kvs), []⟩
  | d, .node _ l r =>
      match S.bit k d with
      | true => let p := proveAt k (d + 1) r e; ⟨p.term, l.hashOf S e :: p.sibs⟩
      | false => let p := proveAt k (d + 1) l e; ⟨p.term, r.hashOf S e :: p.sibs⟩

def termHash : Option (List (K × D)) → D
  | none => emptyHash S
  | some kds => leafHash S kds

/-- The root a path recomputes: the siblings from depth `d` down, over the end's digest. -/
def climb (k : K) : Nat → List D → D → D
  | _, [], h => h
  | d, s :: rest, h =>
      let c := climb k (d + 1) rest h
      match S.bit k d with
      | true => nodeHash S s c
      | false => nodeHash S c s

def T.get (t : T K V D) (k : K) : Option V := getAt S k 0 t
def T.insert (t : T K V D) (k : K) (v : V) (e : EmptyDigest D := Thunk.mk fun _ => emptyHash S) :
    T K V D :=
  insAt S k v 0 t e
def T.prove (t : T K V D) (k : K) (e : EmptyDigest D := Thunk.mk fun _ => emptyHash S) :
    Proof K D :=
  proveAt S k 0 t e

/-- Every entry, left to right. -/
def T.toList : T K V D → List (K × V)
  | .empty => []
  | .leaf _ kvs => kvs
  | .node _ l r => l.toList ++ r.toList

def insertAll (t : T K V D) (kvs : List (K × V)) : T K V D :=
  kvs.foldl (fun t p => t.insert S p.1 p.2) t

variable [DecidableEq D]

/-- Does `p` show `k` ↦ a value with digest `dig` under `root`? Bounded: a path longer than
`depth` is refused before anything is hashed. -/
def verifyInclusion (root : D) (k : K) (dig : D) (p : Proof K D) : Bool :=
  p.sibs.length ≤ S.depth &&
  match p.term with
  | some kds => find k kds = some dig && climb S k 0 p.sibs (termHash S p.term) = root
  | none => false

/-- Does `p` show `k` absent under `root`? -/
def verifyExclusion (root : D) (k : K) (p : Proof K D) : Bool :=
  p.sibs.length ≤ S.depth &&
  (match p.term with
   | some kds => (find k kds).isNone
   | none => true) &&
  climb S k 0 p.sibs (termHash S p.term) = root

end Nanodregg.Kernel.Trie
