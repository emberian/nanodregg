/-
# Kernel.Trie — a persistent, path-compressed binary Merkle trie (KERNEL-23, KERNEL-49 (a))

The authenticated map the World's cells, journal, refusals and rows live in. Keys are routed by
their bits (`Spec.bit k i`: bit `i` of the key). A subtree holding no key is `empty` (only ever a
whole trie: no node has an empty child), one holding one key is a `leaf`, and one holding more is a
`node` that BRANCHES at `b`, the first bit on which its keys differ: those with bit `b` clear go
left, the rest right. The bits every key of the subtree agrees on are skipped, so a path is as long
as the number of branchings above the key, not the key's length. The shape is a function of the key
set, not of the insertion order. A leaf holds a LIST of entries only when its keys agree on every
bit below `Spec.depth` (an encoding that is not injective; the deployed ones are). So `get` after
`insert` is exact for ANY bit function and ANY tree, canonical or not: a node keeps a representative
key (`rep`), `getAt` refuses a key that leaves it on the skipped bits, and `insAt` splits exactly
there, so the two always agree on where a key belongs (`Kernel.Proofs.Trie.get_insert`, no
premise). Correctness never rests on a hash or an encoding, only the proofs' soundness does.

Every node caches its digest. One byte domain separates the three shapes: `empty = H(0)`,
`leaf = H(1 ‖ k ‖ digest v …)`, `node = H(2 ‖ u16 b ‖ left ‖ right)`. The branching bit IS
committed: a proof's i-th sibling carries the bit its node branches on, and the side is the key's
bit there. Without `b` in the hash a proof could claim other bits and steer a key's walk to a leaf
`get` never reaches, and an exclusion proof would forge (the sim plant `depth-unhashed`). With it,
exclusion proofs are as sound as inclusion ones (Kernel.Proofs.Trie). `Spec.depth_lt` keeps every
branching bit inside a u16.

Work per `insert`: one path from the root to the key's leaf is rebuilt, one hash per node on it,
plus its leaf, plus at most one new node where the key's bits first leave the path's. A one-entry
leaf the new key splits keeps its cached digest: a leaf's hash commits its entries, not its
position (cv 01a15107-2263; `Kernel.Proofs.Trie.insAt_eq_rebuild`: the same trie as re-hashing it).
A batch (`insertAll`, cv 01a15107-2281) writes its keys on the dirty overlay `U` and hashes once at
`U.seal`: a node several of its keys pass through is hashed once, not once per key.
-/
namespace Nanodregg.Kernel.Trie

/-- How a trie routes, hashes and encodes. -/
structure Spec (K V D : Type) where
  /-- bit `i` of a key -/
  bit : K → Nat → Bool
  /-- the bits a key is routed by: a node branches below it, and a leaf holds several keys only
  when they agree on every bit below it -/
  depth : Nat
  /-- a node commits its branching bit as a u16 -/
  depth_lt : depth < 2 ^ 16
  hash : ByteArray → D
  dbytes : D → ByteArray
  kbytes : K → ByteArray
  /-- what a leaf commits to of a value -/
  vdigest : V → D

inductive T (K V D : Type) where
  | empty
  | leaf (h : D) (kvs : List (K × V))
  /-- `b`: the bit the node branches on; `rep`: its first key in trie order, a cache (not hashed)
  of the bits every key below agrees on, which `getAt` checks and `insAt` splits at -/
  | node (h : D) (b : Nat) (rep : K) (l r : T K V D)

/-- What a proof carries of the subtree it ends at: an empty trie, or a leaf's entries as
(key, value digest). -/
structure Proof (K D : Type) where
  term : Option (List (K × D))
  /-- the siblings along the key's path, from the root down, each with the bit its node branches
  on -/
  sibs : List (Nat × D)

variable {K V D : Type} (S : Spec K V D)

/-- A shape tag, then its bytes. -/
def tagged (t : UInt8) (b : ByteArray) : ByteArray := ⟨#[t]⟩ ++ b

/-- A branching bit's two bytes, big-endian (injective below `2 ^ 16`). -/
def u16 (b : Nat) : ByteArray := ⟨#[(b / 256).toUInt8, b.toUInt8]⟩

def leafBody (kds : List (K × D)) : ByteArray :=
  kds.foldr (fun p acc => S.kbytes p.1 ++ S.dbytes p.2 ++ acc) ByteArray.empty

def emptyHash : D := S.hash (tagged 0 ByteArray.empty)
def leafHash (kds : List (K × D)) : D := S.hash (tagged 1 (leafBody S kds))
def nodeHash (b : Nat) (l r : D) : D := S.hash (tagged 2 (u16 b ++ S.dbytes l ++ S.dbytes r))

def digests (kvs : List (K × V)) : List (K × D) := kvs.map fun p => (p.1, S.vdigest p.2)

/-- A subtree's digest. Only a whole trie is ever `empty`, so the empty digest is hashed only where
a root is read (`T.rootWith`). -/
def T.hashOf : T K V D → D
  | .empty => emptyHash S
  | .leaf h _ => h
  | .node h _ _ _ _ => h

/-- A root's digest, an empty trie's read from `e`: the World commits four roots per head and shares
one lazy empty digest among them, so a head pays at most one hash for its empty tries (KERNEL-35, at
the roots only). -/
def T.rootWith (t : T K V D) (e : Thunk D) : D :=
  match t with
  | .empty => e.get
  | t => t.hashOf S

def mkLeaf (kvs : List (K × V)) : T K V D := .leaf (leafHash S (digests S kvs)) kvs

def mkNode (b : Nat) (rep : K) (l r : T K V D) : T K V D :=
  .node (nodeHash S b (l.hashOf S) (r.hashOf S)) b rep l r

variable [DecidableEq K]

/-- The value at `k` in a leaf's entries. -/
def find {α : Type} (k : K) (kvs : List (K × α)) : Option α := (kvs.find? fun p => p.1 = k).map (·.2)


/-- The first bit from `d` below `depth` on which the keys of `kvs` do not all agree. -/
def splitBit (d : Nat) : List (K × V) → Option Nat
  | [] => none
  | p :: rest => (List.range' d (S.depth - d)).find? fun i => rest.any fun q => S.bit q.1 i != S.bit p.1 i

/-- The first bit from `d` below `b` on which `k` and `k'` differ. -/
def diverge (k k' : K) (d b : Nat) : Option Nat :=
  (List.range' d (b - d)).find? fun i => S.bit k i != S.bit k' i

/-- The value at `k`, in a subtree whose keys agree with `k` on every bit below `d`: at a node
branching at `b`, `k` must agree with the node's `rep` on the skipped bits `[d, b)` (else no key
below is `k`), then it follows its bit `b`; at a leaf, whole keys are compared. -/
def getAt (k : K) : Nat → T K V D → Option V
  | _, .empty => none
  | _, .leaf _ kvs => find k kvs
  | d, .node _ b rep l r =>
      match diverge S k rep d b with
      | some _ => none
      | none =>
          match S.bit k b with
          | true => getAt k (b + 1) r
          | false => getAt k (b + 1) l

/-- Whether `k` comes before `k'` in trie order, given they agree below `d`: at their first
differing bit below `depth`, `k`'s is clear. Keys agreeing on every bit below `depth` share a leaf,
where a new key goes last. -/
def precedes (k k' : K) (d : Nat) : Bool :=
  match diverge S k k' d S.depth with
  | some e => !S.bit k e
  | none => false

/-- The subtree's first key in trie order, read from its root (no walk). -/
def T.first : T K V D → Option K
  | .empty => none
  | .leaf _ kvs => kvs.head?.map (·.1)
  | .node _ _ rep _ _ => some rep

/-- The canonical subtree holding `kvs`, whose keys agree on every bit below `d` (`fuel` levels
left; `depth - d` always suffices, since each node branches at a bit `≥ d`). -/
def build (f d : Nat) (kvs : List (K × V)) : T K V D :=
  match f, kvs with
  | _, [] => .empty
  | _, [x] => mkLeaf S [x]
  | 0, kvs => mkLeaf S kvs
  | f + 1, p :: rest =>
      match splitBit S d (p :: rest) with
      | none => mkLeaf S (p :: rest)
      | some b =>
          let l := build f (b + 1) ((p :: rest).filter fun q => !S.bit q.1 b)
          mkNode S b (l.first.getD p.1) l (build f (b + 1) ((p :: rest).filter fun q => S.bit q.1 b))

/-- Set `k` to `v` in a subtree whose keys agree with `k` on every bit below `d`: one path rebuilt.
Where `k` first leaves a node's skipped bits (against its `rep`, as `getAt` reads), a new node
branches between `k`'s leaf and the node, whose cached hash is kept. A node's `rep` becomes `k` when
`k` lands first in trie order. -/
def insAt (k : K) (v : V) : Nat → T K V D → T K V D
  | _, .empty => mkLeaf S [(k, v)]
  | d, .leaf h kvs =>
      if kvs.any (fun p => p.1 = k) then mkLeaf S (kvs.map fun p => if p.1 = k then (k, v) else p)
      else
        match kvs with
        | [p] =>
            -- a new key leaving a one-entry leaf: one node over the leaf, whose cached digest stands
            -- (a leaf's hash commits its entries, not its position; cv 01a15107-2263)
            match diverge S k p.1 d S.depth with
            | some c =>
                match S.bit k c with
                | true => mkNode S c p.1 (.leaf h [p]) (mkLeaf S [(k, v)])
                | false => mkNode S c k (mkLeaf S [(k, v)]) (.leaf h [p])
            | none => build S (S.depth - d) d ([p] ++ [(k, v)])
        | _ => build S (S.depth - d) d (kvs ++ [(k, v)])
  | d, .node h b rep l r =>
      match diverge S k rep d b with
      | some c =>
          match S.bit k c with
          | true => mkNode S c rep (.node h b rep l r) (mkLeaf S [(k, v)])
          | false => mkNode S c k (mkLeaf S [(k, v)]) (.node h b rep l r)
      | none =>
          match S.bit k b with
          | true => mkNode S b rep l (insAt k v (b + 1) r)
          | false => mkNode S b (if precedes S k rep (b + 1) then k else rep) (insAt k v (b + 1) l) r

/-- The proof for `k`: the siblings down its path, each with its node's branching bit, and what the
path ends at. It follows `k`'s bits only (a key that leaves a node's skipped bits is shown absent by
the leaf its bits reach, which does not hold it). -/
def proveAt (k : K) : T K V D → Proof K D
  | .empty => ⟨none, []⟩
  | .leaf _ kvs => ⟨some (digests S kvs), []⟩
  | .node _ b _ l r =>
      match S.bit k b with
      | true => let p := proveAt k r; ⟨p.term, (b, l.hashOf S) :: p.sibs⟩
      | false => let p := proveAt k l; ⟨p.term, (b, r.hashOf S) :: p.sibs⟩

def termHash : Option (List (K × D)) → D
  | none => emptyHash S
  | some kds => leafHash S kds

/-- The root a path recomputes: the siblings from the root down, over the end's digest. -/
def climb (k : K) : List (Nat × D) → D → D
  | [], h => h
  | (b, s) :: rest, h =>
      let c := climb k rest h
      match S.bit k b with
      | true => nodeHash S b s c
      | false => nodeHash S b c s

def T.get (t : T K V D) (k : K) : Option V := getAt S k 0 t
def T.insert (t : T K V D) (k : K) (v : V) : T K V D := insAt S k v 0 t
def T.prove (t : T K V D) (k : K) : Proof K D := proveAt S k t

/-- Every entry, left to right. -/
def T.toList : T K V D → List (K × V)
  | .empty => []
  | .leaf _ kvs => kvs
  | .node _ _ _ l r => l.toList ++ r.toList

/-! ## A batch: the dirty overlay (cv 01a15107-2281)

`U` is a trie a batch is writing. It holds NO digest: a `clean` subtree is a `T` kept whole, with its
cached digests, and a `leaf` or `node` is one the batch wrote and has not hashed. `U.seal` is its only
reader: it hashes each written node and leaf once, over its children's digests, and returns the `T`.
One `clean` subtree is the batch's own: `insLeafU`'s build fallback (a new key that does not leave a
one-entry leaf below `depth`, or any multi-entry leaf) returns `.clean (build …)`, a `T` the batch wrote
and hashed AT INSERT TIME, not at seal; a later key of the same batch entering it re-hashes its path.
Unreachable under injective key bytes (every leaf holds one entry, no two keys share a full bit path),
which the deployed specs have.
`T` stays the only authenticated shape: nothing reads, proves, lists or encodes a `U`. The batch IS the
sequential inserts (`Kernel.Proofs.Trie.seal_insU`, `insertAll_eq_foldl`: equal as `T` values, cached
digests included, no premise); what the sequential fold hashed again (the nodes on a key's path an
earlier insert of the same batch had already rebuilt) is hashed once. -/
inductive U (K V D : Type) where
  | clean (t : T K V D)
  | leaf (kvs : List (K × V))
  | node (b : Nat) (rep : K) (l r : U K V D)

/-- The trie a batch wrote: each written node and leaf hashed once, over its children's digests. -/
def U.seal : U K V D → T K V D
  | .clean t => t
  | .leaf kvs => mkLeaf S kvs
  | .node b rep l r => mkNode S b rep (l.seal) (r.seal)

/-- `insAt` at a leaf holding `kvs`, on the overlay: `keep` is the leaf as it stands (clean or written),
kept whole under the node a new key splits it with. -/
def insLeafU (k : K) (v : V) (d : Nat) (keep : U K V D) (kvs : List (K × V)) : U K V D :=
  if kvs.any (fun p => p.1 = k) then .leaf (kvs.map fun p => if p.1 = k then (k, v) else p)
  else
    match kvs with
    | [p] =>
        match diverge S k p.1 d S.depth with
        | some c =>
            match S.bit k c with
            | true => .node c p.1 keep (.leaf [(k, v)])
            | false => .node c k (.leaf [(k, v)]) keep
        | none => .clean (build S (S.depth - d) d ([p] ++ [(k, v)]))
    | _ => .clean (build S (S.depth - d) d (kvs ++ [(k, v)]))

/-- `insAt`, case for case, from a clean subtree: the path to `k` is written (unhashed), every
subtree off it is kept as it stands, digest and all. Structural on `T`, so the kernel reduces it
(`Codec.Proofs.ListingPin` decides listings through it). -/
def insT (k : K) (v : V) : Nat → T K V D → U K V D
  | _, .empty => .leaf [(k, v)]
  | d, .leaf h kvs => insLeafU S k v d (.clean (.leaf h kvs)) kvs
  | d, .node h b rep l r =>
      match diverge S k rep d b with
      | some c =>
          match S.bit k c with
          | true => .node c rep (.clean (.node h b rep l r)) (.leaf [(k, v)])
          | false => .node c k (.leaf [(k, v)]) (.clean (.node h b rep l r))
      | none =>
          match S.bit k b with
          | true => .node b rep (.clean l) (insT k v (b + 1) r)
          | false => .node b (if precedes S k rep (b + 1) then k else rep) (insT k v (b + 1) l) (.clean r)

/-- `insAt`, case for case, on the overlay: down the written nodes, then `insT` from the first clean
subtree. `Kernel.Proofs.Trie.seal_insU`: sealing it is `insAt` of the sealed trie. -/
def insU (k : K) (v : V) : Nat → U K V D → U K V D
  | d, .clean t => insT S k v d t
  | d, .leaf kvs => insLeafU S k v d (.leaf kvs) kvs
  | d, .node b rep l r =>
      match diverge S k rep d b with
      | some c =>
          match S.bit k c with
          | true => .node c rep (.node b rep l r) (.leaf [(k, v)])
          | false => .node c k (.leaf [(k, v)]) (.node b rep l r)
      | none =>
          match S.bit k b with
          | true => .node b rep l (insU k v (b + 1) r)
          | false => .node b (if precedes S k rep (b + 1) then k else rep) (insU k v (b + 1) l) r

/-- Every entry of `kvs` set, in order, in one pass: the batch on the dirty overlay, sealed once. The
same trie as inserting each in turn (`Kernel.Proofs.Trie.insertAll_eq_foldl`, no premise); each node on
a changed path is hashed once. -/
def insertAll (t : T K V D) (kvs : List (K × V)) : T K V D :=
  (kvs.foldl (fun u p => insU S p.1 p.2 0 u) (.clean t)).seal S

/-- The value at `k` on the overlay, as `getAt` reads it of the sealed trie (`Kernel.Proofs.Trie.getAtU_seal`,
no premise): `getAt` reads branching bits, `rep`s and entries, never a digest, so nothing is hashed. -/
def U.getAt (k : K) : Nat → U K V D → Option V
  | d, .clean t => Trie.getAt S k d t
  | _, .leaf kvs => find k kvs
  | d, .node b rep l r =>
      match diverge S k rep d b with
      | some _ => none
      | none =>
          match S.bit k b with
          | true => U.getAt k (b + 1) r
          | false => U.getAt k (b + 1) l

/-! ## Retain: the canonical erase (KERNEL-41)

`retainAt path q` keeps, in the subtree `path` leads to, the entries `q` keeps. What it returns is
the canonical trie of what is left (`Kernel.Proofs.TrieRetain.retainAt_eq_build`), without listing
and rebuilding it: a subtree that drops nothing is returned as it is (no hash), a leaf is re-hashed
only when it keeps some of several entries, and a node one of whose children keeps nothing is
replaced by the other child whole (`join`), its cached hash reused. -/

/-- Two children of a node branching at `b`, joined canonically: a node, unless one side is empty,
when the other side is returned whole (a subtree's hash commits its own branching bits, not its
position, so its cached hash stands). -/
def join (b : Nat) (l r : T K V D) : T K V D :=
  match l, r with
  | .empty, r => r
  | l, .empty => l
  | l, r =>
      match l.first with
      | some x => mkNode S b x l r
      | none => r

/-- The entries of `t` that `q` keeps, and whether any was dropped. -/
def retainAll (q : K → V → Bool) : T K V D → T K V D × Bool
  | .empty => (.empty, false)
  | .leaf h kvs =>
      if kvs.all (fun p => q p.1 p.2) then (.leaf h kvs, false)
      else
        let kept := kvs.filter fun p => q p.1 p.2
        if kept.isEmpty then (.empty, true) else (mkLeaf S kept, true)
  | .node h b rep l r =>
      let x := retainAll q l
      let y := retainAll q r
      if x.2 || y.2 then (join S b x.1 y.1, true) else (.node h b rep l r, false)

/-- `retainAll q` on the subtree `path` leads to (at a node branching at `b`, the path's bit `b`
chooses the side), the nodes above it re-joined; where the path has no bit `b`, the whole subtree is
filtered. Entries off the path are kept, so a caller's `q` must keep them (the kernel's keeps every
slot that is not the one removed, or not a journal entry). -/
def retainAt (q : K → V → Bool) (path : List Bool) : T K V D → T K V D
  | .empty => .empty
  | .leaf h kvs => (retainAll S q (.leaf h kvs)).1
  | .node h b rep l r =>
      match path[b]? with
      | some true => join S b l (retainAt q path r)
      | some false => join S b (retainAt q path l) r
      | none => (retainAll S q (.node h b rep l r)).1

/-! ### Retain on the overlay (cv 01a15460-e096): a removal joins the batch instead of sealing it -/

/-- The first key of an overlay, as `T.first` reads the sealed trie (`Kernel.Proofs.Trie.first_seal`). -/
def U.first : U K V D → Option K
  | .clean t => t.first
  | .leaf kvs => kvs.head?.map (·.1)
  | .node _ rep _ _ => some rep

/-- `join` on the overlay: an empty side (`.clean .empty`, the one overlay that seals to `.empty`)
yields the other side whole, as it stands; else a written node, unhashed. -/
def joinU (b : Nat) (l r : U K V D) : U K V D :=
  match l, r with
  | .clean .empty, r => r
  | l, .clean .empty => l
  | l, r =>
      match l.first with
      | some x => .node b x l r
      | none => r

/-- `retainAll` at a leaf holding `kvs`, on the overlay: `keep` is the leaf as it stands (clean or
written) where nothing is dropped; the kept entries written, unhashed, where some are. -/
def retainLeafU (q : K → V → Bool) (keep : U K V D) (kvs : List (K × V)) : U K V D :=
  if kvs.all (fun p => q p.1 p.2) then keep
  else
    let kept := kvs.filter fun p => q p.1 p.2
    if kept.isEmpty then .clean .empty else .leaf kept

/-- `retainAt`, case for case, from a clean subtree: the nodes above the path's end re-joined on the
overlay (written, unhashed; one whose other side is empty gives way to that side whole), every
subtree off the path kept as it stands, digest and all. The `none` arm (a node branching at a bit the
path has no entry for) filters the sealed subtree whole, as `retainAt` does; it is there for
totality only: the kernel's paths (`rowPath`, `Bounds.rowDepth` entries = the rows spec's `depth`)
have a bit for every `b < depth`, and a node of a canonical trie branches at `b < depth`. -/
def retainAtT (q : K → V → Bool) (path : List Bool) : T K V D → U K V D
  | .empty => .clean .empty
  | .leaf h kvs => retainLeafU q (.clean (.leaf h kvs)) kvs
  | .node h b rep l r =>
      match path[b]? with
      | some true => joinU b (.clean l) (retainAtT q path r)
      | some false => joinU b (retainAtT q path l) (.clean r)
      | none => .clean (retainAll S q (.node h b rep l r)).1

/-- `retainAt` on the overlay: down the written nodes, then `retainAtT` from the first clean subtree.
`Kernel.Proofs.Trie.seal_retainAtU`: sealing it is `retainAt` of the sealed trie, no premise, so a
removal joins the batch instead of sealing it (`World.uStore`). The `none` arm is `retainAtT`'s. -/
def retainAtU (q : K → V → Bool) (path : List Bool) : U K V D → U K V D
  | .clean t => retainAtT S q path t
  | .leaf kvs => retainLeafU q (.leaf kvs) kvs
  | .node b rep l r =>
      match path[b]? with
      | some true => joinU b l (retainAtU q path r)
      | some false => joinU b (retainAtU q path l) r
      | none => .clean (retainAll S q ((U.node b rep l r).seal S)).1

/-- The siblings' branching bits ascend from `d` and stay below `depth`: a path is at most `depth`
long, and every bit it claims fits the u16 a node commits. -/
def ascends : Nat → List (Nat × D) → Bool
  | _, [] => true
  | d, (b, _) :: rest => decide (d ≤ b) && decide (b < S.depth) && ascends (b + 1) rest

variable [DecidableEq D]

/-- Does `p` show `k` ↦ a value with digest `dig` under `root`? Bounded: a path whose bits do not
ascend below `depth` is refused before anything is hashed. -/
def verifyInclusion (root : D) (k : K) (dig : D) (p : Proof K D) : Bool :=
  ascends S 0 p.sibs &&
  match p.term with
  | some kds => find k kds = some dig && climb S k p.sibs (termHash S p.term) = root
  | none => false

/-- Does `p` show `k` absent under `root`? -/
def verifyExclusion (root : D) (k : K) (p : Proof K D) : Bool :=
  ascends S 0 p.sibs &&
  (match p.term with
   | some kds => (find k kds).isNone
   | none => true) &&
  climb S k p.sibs (termHash S p.term) = root

/-! ### What a read compares: the bytes each hash along a path takes (KERNEL-56) -/

omit [DecidableEq K] [DecidableEq D] in
/-- The bytes a path's end hashes: an empty trie's tag, or a leaf's entries. -/
def termPre : Option (List (K × D)) → ByteArray
  | none => tagged 0 ByteArray.empty
  | some kds => tagged 1 (leafBody S kds)

omit [DecidableEq K] [DecidableEq D] in
/-- The bytes a node hashes. -/
def nodePre (b : Nat) (l r : D) : ByteArray := tagged 2 (u16 b ++ S.dbytes l ++ S.dbytes r)

omit [DecidableEq K] [DecidableEq D] in
/-- The bytes `climb` hashes for `k`, from the root down, then the end's (`termPre`). -/
def climbPres (k : K) : List (Nat × D) → Option (List (K × D)) → List ByteArray
  | [], term => [termPre S term]
  | (b, s) :: rest, term =>
      (match S.bit k b with
       | true => nodePre S b s (climb S k rest (termHash S term))
       | false => nodePre S b (climb S k rest (termHash S term)) s) :: climbPres k rest term

omit [DecidableEq K] [DecidableEq D] in
/-- The bytes a trie hashed along the path `proveAt` follows for `k` (each node over its children's
cached digests), then its end's. -/
def pathPres (k : K) : T K V D → List ByteArray
  | .empty => [termPre S none]
  | .leaf _ kvs => [termPre S (some (digests S kvs))]
  | .node _ b _ l r =>
      nodePre S b (l.hashOf S) (r.hashOf S) ::
        (match S.bit k b with
         | true => pathPres k r
         | false => pathPres k l)

omit [DecidableEq K] [DecidableEq D] in
/-- **What a read compares**: the bytes the presented proof `p` hashes for `k`, then the bytes the
trie `t` hashed along `k`'s path. Every soundness theorem of a proof escapes only by a collision
among these. -/
def readPres (k : K) (p : Proof K D) (t : T K V D) : List ByteArray :=
  climbPres S k p.sibs p.term ++ pathPres S k t

end Nanodregg.Kernel.Trie
