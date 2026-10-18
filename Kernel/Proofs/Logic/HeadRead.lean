/-
# Kernel.Proofs.Logic.HeadRead — the head-read family, stated once (KERNEL-52)

Every trie the chain commits in `rootsDigest` is read the same way: a proof that verifies against
a canonical trie's root tells the truth about the key, or the kernel's hash collides; and against a
head record, through the four roots `head_roots` opens, the same holds of whichever root the trie
is. (That a canonical trie proves what it holds and what it does not needs no instance:
`Trie.prove_includes` / `Trie.prove_excludes` are already stated over any `Trie.Spec`.)

`HeadSound E S Fits` is what a `Trie.Spec` must give for that: its leaf bodies and node pairs are
injective (`Trie.inclusion_sound`'s premises), its leaf digest determines a value on `Fits` up to a
`Collision`, and a trie collision is a `Collision`. The instances: `cells_headSound`
(`Kernel.Proofs.Cells`: `Fits` is `Leaf.CellFit Cell.Fits`, where `hE.cellBytes_injOn` makes the
cell codec injective), `journal_headSound` (`Kernel.Proofs.JournalHead`: needs `0 < n`; `Fits` is a
height below 2^64), `refusal_headSound` (`Kernel.Proofs.RefusalsHead`: `Fits` is
`RefusalLeaf.Fits`). The rows are not an instance: their key bytes are not injective outside
`rowFits` (`byte8` wraps both the relation byte and the key-length byte at 256), so `Trie.inclusion_sound`'s unconditional `hL`
fails for them (decisions/kernel.md KERNEL-52).
-/
import Kernel.Proofs.Fold
import Kernel.Proofs.TrieMap

namespace Nanodregg.Kernel

variable {D : Type} [Ord D] [DecidableEq D] {K V : Type} [DecidableEq K]

/-- **What the head-read family needs of a trie**: injective leaf bodies and node pairs, a leaf
digest that determines a value on `Fits` up to a `Collision`, and a trie collision that is one. -/
structure HeadSound (E : Env D) (S : Trie.Spec K V D) (Fits : V → Prop) : Prop where
  body_inj : ∀ x y, Trie.leafBody S x = Trie.leafBody S y → x = y
  pair_inj : ∀ a b c e, S.dbytes a ++ S.dbytes b = S.dbytes c ++ S.dbytes e → a = c ∧ b = e
  vdigest_inj : ∀ {v v' : V}, Fits v → Fits v' → S.vdigest v = S.vdigest v' → v = v' ∨ Collision E.hash
  coll : Trie.Coll S → Collision E.hash

namespace HeadSound

variable {E : Env D} {S : Trie.Spec K V D} {Fits : V → Prop}

omit [Ord D] in
/-- **Inclusion is sound**: a claimed value proved against a canonical trie's root, on a trie whose
values and the claimed one fit, is the trie's value, or a collision. -/
theorem inclusion (hs : HeadSound E S Fits) {t : Trie.T K V D} (hc : Trie.Canon S 0 t)
    (hfit : ∀ k v, t.get S k = some v → Fits v) {k : K} {v : V} (hv : Fits v) {p : Trie.Proof K D}
    (hp : Trie.verifyInclusion S (t.hashOf S) k (S.vdigest v) p = true) :
    t.get S k = some v ∨ Collision E.hash := by
  rcases Trie.inclusion_sound S hs.body_inj hs.pair_inj hc.2.1 hc.1 hp with ⟨v', hg, hd⟩ | c
  · rcases hs.vdigest_inj (hfit k v' hg) hv hd with rfl | c
    · exact .inl hg
    · exact .inr c
  · exact .inr (hs.coll c)

omit [Ord D] in
/-- **Exclusion is sound**: a key proved absent against a canonical trie's root is absent, or a
collision. -/
theorem exclusion (hs : HeadSound E S Fits) {t : Trie.T K V D} (hc : Trie.Canon S 0 t) {k : K}
    {p : Trie.Proof K D} (hp : Trie.verifyExclusion S (t.hashOf S) k p = true) :
    t.get S k = none ∨ Collision E.hash := by
  rcases Trie.exclusion_sound S hs.body_inj hs.pair_inj hc.2.1 hp with h | c
  · exact .inl h
  · exact .inr (hs.coll c)

/-- **The phone's read against a head**: given what `head_roots` opens a head record to, a proof
against the root `pick` selects, of a canonical trie whose root that is, is sound as at the
World. -/
theorem head_read (hs : HeadSound E S Fits) (pick : D → D → D → D → D) {t : Trie.T K V D}
    {w' : World D} (hc : Trie.Canon S 0 t)
    (hroot : pick (w'.root E) (w'.journalRoot E) (w'.refusalsRoot E) (w'.rowsRoot E) = t.hashOf S)
    (hfit : ∀ k v, t.get S k = some v → Fits v) {root' jroot' rroot' wroot' : D}
    (hroots : (root' = w'.root E ∧ jroot' = w'.journalRoot E ∧ rroot' = w'.refusalsRoot E ∧
      wroot' = w'.rowsRoot E) ∨ Collision E.hash)
    {k : K} {v : V} (hv : Fits v) {p : Trie.Proof K D}
    (hp : Trie.verifyInclusion S (pick root' jroot' rroot' wroot') k (S.vdigest v) p = true) :
    t.get S k = some v ∨ Collision E.hash := by
  rcases hroots with ⟨rfl, rfl, rfl, rfl⟩ | col
  · rw [hroot] at hp; exact hs.inclusion hc hfit hv hp
  · exact .inr col

/-- **The phone's absence against a head**, as `head_read`. -/
theorem head_absent (hs : HeadSound E S Fits) (pick : D → D → D → D → D) {t : Trie.T K V D}
    {w' : World D} (hc : Trie.Canon S 0 t)
    (hroot : pick (w'.root E) (w'.journalRoot E) (w'.refusalsRoot E) (w'.rowsRoot E) = t.hashOf S)
    {root' jroot' rroot' wroot' : D}
    (hroots : (root' = w'.root E ∧ jroot' = w'.journalRoot E ∧ rroot' = w'.refusalsRoot E ∧
      wroot' = w'.rowsRoot E) ∨ Collision E.hash)
    {k : K} {p : Trie.Proof K D}
    (hp : Trie.verifyExclusion S (pick root' jroot' rroot' wroot') k p = true) :
    t.get S k = none ∨ Collision E.hash := by
  rcases hroots with ⟨rfl, rfl, rfl, rfl⟩ | col
  · rw [hroot] at hp; exact hs.exclusion hc hp
  · exact .inr col

end HeadSound

end Nanodregg.Kernel
