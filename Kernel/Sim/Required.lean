/-
# Kernel.Sim.Required — the trie hashes a transition REQUIRES, read off the tries it built (cv 01a14afe-7380)

The hash counter (`Gen.countingEnv`, KERNEL-36) says how many trie-domain hashes a transition MADE.
A ratio over named things (hashes per touched cell, per nullifier, per refusal) then moves with the
trie's SHAPE, which follows the run's random ids: a re-draw of every id (a signature byte, a domain
string, another seed set) moved those rows by 1-4% with no code changed, so real waste below that
noise was invisible. The denominator here is instead what the design requires FOR THE TRIES THE RUN
BUILT, counted from their shapes, never from `log2 n`:

* an insert of `k` (`Trie.insAt`: one path rebuilt) requires, read off the trie after it: one hash
  per node on `k`'s path (each node's digest covers the changed leaf) and `k`'s leaf; a one-entry
  leaf the new key splits is NOT re-hashed (its digest commits its entries, not its position:
  `insAt` puts one node over it, cv 01a15107-2263, `Kernel.Proofs.Trie.insAt_eq_rebuild`): `insertReq`;
* a removal (`Trie.retainAt`, the canonical erase: the journal's and the refusals' prunes, a row
  retract, a retired parent's heads) requires one hash per node or leaf of the trie after it whose
  digest is not the digest of the subtree it replaced (a subtree that kept everything, or that
  `join` promoted whole, is not re-hashed): `fresh`;
* an inclusion proof of `k` (`Trie.proveAt`) requires, on the wire, the bytes of the end of
  `k`'s path (its leaf's entries) and of one sibling per node on the path, both sized by the proof
  codec itself (cv 01a15107-2290): `proofReq`;
* a head forces the empty trie's digest once when one of its four roots is empty (ONE lazy copy
  shared by the roots, KERNEL-35 at the roots only since KERNEL-49 (a)): `emptyRoots`.

A transition's requirement is the sum over the trie operations it makes, in the order it makes them
(an insert's path is the path in the trie as it stands after THAT insert; a later insert of the same
turn can add a node above it). The operations are the kernel's: the cell keys from `check`'s posts,
the born ids and the nullifiers (`commitTrie`'s order), the journal insert and `pruneJournal`, the
refusals' `pruneRefusals`, each row touch's row and head writes (`rowStep`) and the heads `dropHeads`
lists with the kernel's own `under`. Each replay must reach the root the real transition reached, or
the requirement is refused (`.error`): an operation list that drifted from the kernel's is never a
denominator.

Exact by construction for the design as it stands, but for one case the deployed tries never
reach: a new key leaving a MULTI-entry leaf (`insAt` `build`s it again, one hash over the model,
never under). A leaf holds two entries only for keys equal on every bit within `S.depth`, which the
four key encodings (fixed-width or prefix-free within depth) rule out. With that: a kernel that hashes what `insertReq`, `fresh`
and `emptyRoots` name, and nothing else, counts ratio 1.000 on every draw. A regression that hashes
more (the plant `hash-required:empty-per-insert`, KERNEL-35's per-insert empty digest written on the
compressed trie) reads above 1; a count BELOW the requirement fails the run (`Gen.countTurn`): the
design changed and this model must be re-derived with it. Sim-only and the bench's: no deployed
module names it.
-/
import Kernel.World

namespace Nanodregg.Kernel.Sim.Required

open Nanodregg.Kernel

section Generic

variable {K V D : Type} (S : Trie.Spec K V D)

/-- A whole empty trie. -/
def isEmpty : Trie.T K V D → Bool
  | .empty => true
  | _ => false

/-- `k`'s path depth in `t`: the nodes above the leaf it reaches. -/
def pathDepth (k : K) : Trie.T K V D → Nat
  | .node _ b _ l r => (match S.bit k b with | true => pathDepth k r | false => pathDepth k l) + 1
  | _ => 0

/-- What `k`'s path in `t` ends at, as a proof states it (`Trie.Proof.term`): `none` at the empty
trie, else the entries of the leaf it reaches, each as its key and value digest. -/
def termAt (k : K) : Trie.T K V D → Option (List (K × D))
  | .empty => none
  | .leaf _ kvs => some (Trie.digests S kvs)
  | .node _ b _ l r => match S.bit k b with | true => termAt k r | false => termAt k l

/-- **What a proof of `k` in `t` requires on the wire** (cv 01a15107-2290), at a proof codec's
`size`: the path's end with no sibling, and one sibling's bytes per node on the path (`pathDepth`).
A sibling's bytes are the codec's own: its size with the one sibling `sib` less its size with none,
so a layout change moves the requirement with it, and `74 + 34n` is nowhere written here. Exact for a
codec whose siblings are all one width (CODEC's `sibling`: a `nat16` bit and a fixed-width digest). -/
def proofReq (size : Trie.Proof K D → Nat) (sib : Nat × D) (k : K) (t : Trie.T K V D) : Nat :=
  let bare := size ⟨termAt S k t, []⟩
  bare + pathDepth S k t * (size ⟨termAt S k t, [sib]⟩ - bare)

variable [DecidableEq K]

/-- **What an insert of `k` requires**, read off the trie after it (`post`): a hash per node on
`k`'s path and its leaf. The leaf a new key splits keeps its cached digest (cv 01a15107-2263). -/
def insertReq (post : Trie.T K V D) (k : K) : Nat := pathDepth S k post + 1

/-- Below `t`'s nodes that branch before bit `b`, the subtree a key like `rep` reaches. -/
def below (rep : K) (b : Nat) : Trie.T K V D → Trie.T K V D
  | .node h b' rep' l r =>
      if b' < b then (match S.bit rep b' with
        | true => below rep b r
        | false => below rep b l)
      else .node h b' rep' l r
  | t => t

/-- The subtree of `t` that a node branching at `b` over keys like `rep` sees on side `side`: `t`'s
own child when `t` branches at `b` there, else `t` (the node is new: both its sides are compared
against what it split). -/
def toward (rep : K) (b : Nat) (side : Bool) (t : Trie.T K V D) : Trie.T K V D :=
  match below S rep b t with
  | .node h b' rep' l r => if b' = b then (if side then r else l) else .node h b' rep' l r
  | t' => t'

variable [DecidableEq D]

/-- The same subtree: both empty, or the same cached digest (a node's commits its branching bit). -/
def same : Trie.T K V D → Trie.T K V D → Bool
  | .empty, .empty => true
  | .leaf h _, .leaf h' _ => decide (h = h')
  | .node h _ _ _ _, .node h' _ _ _ _ => decide (h = h')
  | _, _ => false

/-- **What a removal requires**: the nodes and leaves of `post` whose digest is not the subtree's of
`pre` at the same place (a node at the same branching bit over the same keys; a leaf, below every
node above it). One hash each; a subtree that kept everything, or was promoted whole by `join`, is
`same` and costs nothing. -/
def fresh (post pre : Trie.T K V D) : Nat :=
  match post with
  | .empty => 0
  | .leaf h kvs =>
      match kvs with
      | (k, _) :: _ => if same (.leaf h kvs) (below S k S.depth pre) then 0 else 1
      | [] => 1
  | .node h b rep l r =>
      if same (.node h b rep l r) (below S rep b pre) then 0
      else 1 + fresh l (toward S rep b false pre) + fresh r (toward S rep b true pre)

/-- One trie operation of a transition. -/
inductive Op (K : Type) where
  /-- `T.insert` of `k` -/
  | ins (k : K)
  /-- `Trie.retainAt` dropping `k` along `path` -/
  | del (k : K) (path : List Bool)

/-- Apply `o` to `t` (an insert takes `val k`), adding what it requires to `n`. -/
def apply (val : K → V) : Trie.T K V D × Nat → Op K → Trie.T K V D × Nat
  | (t, n), .ins k => let t' := t.insert S k (val k); (t', n + insertReq S t' k)
  | (t, n), .del k path =>
      let t' := Trie.retainAt S (fun k' _ => decide (k' ≠ k)) path t
      (t', n + fresh S t' t)

/-- `ops` in order from `t`: the trie they reach and what they require. -/
def applyAll (val : K → V) (t : Trie.T K V D) (ops : List (Op K)) : Trie.T K V D × Nat :=
  ops.foldl (apply S val) (t, 0)

end Generic

variable {D : Type} [Ord D] [DecidableEq D]

/-- A head's empty digest: 1 when one of the four roots it commits is empty (one shared copy). -/
def emptyRoots (w : World D) : Nat :=
  if isEmpty w.trie || isEmpty w.journal || isEmpty w.refusals || isEmpty w.rows then 1 else 0

/-- What an admission requires, by part (`total` is their sum). -/
structure Parts where
  cells : Nat := 0
  nullifiers : Nat := 0
  journal : Nat := 0
  rows : Nat := 0
  refusals : Nat := 0
  roots : Nat := 0
  deriving Repr

def Parts.total (p : Parts) : Nat := p.cells + p.nullifiers + p.journal + p.rows + p.refusals + p.roots

def Parts.add (p q : Parts) : Parts :=
  { cells := p.cells + q.cells, nullifiers := p.nullifiers + q.nullifiers, journal := p.journal + q.journal,
    rows := p.rows + q.rows, refusals := p.refusals + q.refusals, roots := p.roots + q.roots }

/-- A placeholder leaf for a row key the turn writes and then removes (an insert's value never moves
a shape: only `fresh` reads digests, and only of tries this replay built). -/
def rowDummy : RowLeaf := .row 0 ByteArray.empty 0

/-- The rows operations of one row touch, as `rowStep` makes them: an insert or upsert writes the row
then its head (`setHead`), a retract removes the row (`retainAt` along `rowPath`) then writes the
head, a declare writes the head, a keep nothing. -/
def rowOps (E : Env D) (x : RowTouch D) : List (Op (RowSlot D)) :=
  match x.slot, x.act with
  | .head p rel, .declare .. => [.ins (.head p rel)]
  | .row key, .insert .. | .row key, .upsert .. => [.ins (.row key), .ins (.head key.parent key.rel)]
  | .row key, .retract => [.del (.row key) (rowPath E (.row key)), .ins (.head key.parent key.rel)]
  | _, _ => []

/-- The rows a turn writes, from `w`'s: each touch's operations in order, then each retired parent's
heads removed (`dropHeads`, listed by the kernel's own `under` on the rows as they then stand). -/
def rowsReq (E : Env D) (w : World D) (t : Turn D) (val : RowSlot D → RowLeaf) : Rows D × Nat :=
  let S := rowSpec E
  let (r, n) := applyAll S val w.rows (t.rows.flatMap (rowOps E))
  t.touches.foldl (fun (acc : Rows D × Nat) x => match x.act with
    | .retire =>
        let heads := (under S (E.bytes x.cell) 257 acc.1).filterMap fun p => match p.1 with
          | .head q rel => if q = x.cell then some (Op.del (.head q rel) (rowPath E (.head q rel))) else none
          | .row _ => none
        heads.foldl (apply S val) acc
    | _ => acc) (r, n)

/-- **What an admission `w → w'` of `t` requires** (`E` uncounted). `.error` when `t` does not
re-check on `w` or a replay does not reach `w'`'s root. -/
def admit (E : Env D) (w : World D) (t : Turn D) (w' : World D) : Except String Parts := do
  let posts ← match check E w t with
    | .ok p => pure p
    | .error r => throw s!"the turn does not re-check ({r.name})"
  let S := trieSpec E
  let cval := fun s => (w'.trie.get S s).getD .spent
  let (tc, nc) := applyAll S cval w.trie
    ((posts.map fun p => Op.ins (Slot.cell p.cell)) ++ (createdIds t).map fun c => .ins (.cell c))
  let (tn, nn) := applyAll S cval tc (t.nullifiers.map fun n => .ins (.nullifier n))
  unless tn.hashOf S == w'.root E do throw "the cell and nullifier inserts do not reach the admitted root"
  let JS := journalSpec E
  let H := w.height + 1
  let j1 := w.journal.insert JS t.txId (H, turnDigest E t)
  let j2 := pruneJournal E H j1
  unless j2.hashOf JS == w'.journalRoot E do throw "the journal insert and prune do not reach the admitted journal root"
  let RS := rowSpec E
  let (rows, nr) := rowsReq E w t fun k => (w'.rows.get RS k).getD rowDummy
  unless rows.hashOf RS == w'.rowsRoot E do throw "the row operations do not reach the admitted rows root"
  pure { cells := nc, nullifiers := nn, journal := insertReq JS j1 t.txId + fresh JS j2 j1,
         rows := nr, refusals := fresh (refusalSpec E) w'.refusals w.refusals, roots := emptyRoots w' }

/-- **What recording a refusal `w → w'` requires**: its three inserts (the transaction's leaf, the
member's window count, then the World's window total, `commitRefusals`; KERNEL-55 R1) and the head's
empty digest. -/
def refuse (E : Env D) (w : World D) (r : Refused D) (w' : World D) : Except String Nat := do
  let RS := refusalSpec E
  let (t, n) := applyAll RS (fun k => (w'.refusals.get RS k).getD (.count 0)) w.refusals
    [.ins (.tx r.txId), .ins (.count r.member (refusalWindow w.height)),
     .ins (.total w.origin (refusalWindow w.height))]
  unless t.hashOf RS == w'.refusalsRoot E do throw "the refusal's inserts do not reach the recorded refusals root"
  pure (n + emptyRoots w')

/-- What one log step `w → w'` requires (`World.step`'s two kinds). -/
def step (E : Env D) (w : World D) (s : Step D) (w' : World D) : Except String Nat :=
  match s with
  | .turn t => (admit E w t w').map Parts.total
  | .refusal r => refuse E w r w'

end Nanodregg.Kernel.Sim.Required
