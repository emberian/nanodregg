/-
# Kernel.Proofs.Logic.HeadRead — the head-read family, stated once (KERNEL-52, KERNEL-56)

Every trie the chain commits in `rootsDigest` is read the same way: a proof that verifies against
a canonical trie's root tells the truth about the key, or two of the inputs the read compares
collide; and against a head record, through the four roots `head_roots` opens, the same holds of
whichever root the trie is, the head's opening inputs added. (That a canonical trie proves what it
holds and what it does not needs no instance: `Trie.prove_includes` / `Trie.prove_excludes` are
already stated over any `Trie.Spec`.)

The inputs a read compares (KERNEL-56) are named, never quantified: `readPres S k p t`, the
trie-node bytes the presented proof `p` hashes for `k` and those the trie `t` hashed along `k`'s
path (`Trie.readPres`), in `domTrie`; an inclusion read adds `inclPres`, the claimed value's leaf
input and the trie's value's at `k`. A collision among SOME two inputs is a theorem of every lawful
`Env` (pigeonhole), so it is no disjunct here.

`HeadSound E S Fits vpre` is what a `Trie.Spec` must give for that: its leaf bodies and node pairs
are injective (`Trie.inclusion_sound`'s premises), its node hash is the kernel's in `domTrie`, its
leaf digest is the kernel's hash of `vpre v`, and `vpre` is injective on `Fits`. The instances:
`cells_headSound` (`Kernel.Proofs.Cells`: `Fits` is `Leaf.CellFit Cell.Fits`, where
`hE.cellBytes_injOn` makes the cell codec injective), `journal_headSound`
(`Kernel.Proofs.JournalHead`: needs `0 < n`; `Fits` is a height below 2^64), `refusal_headSound`
(`Kernel.Proofs.RefusalsHead`: `Fits` is `RefusalLeaf.Fits`). The rows are not an instance: their
key bytes are not injective outside `rowFits` (`byte8` wraps both the relation byte and the
key-length byte at 256), so `Trie.inclusion_sound`'s unconditional `hL` fails for them
(decisions/kernel.md KERNEL-52). Teeth: `inclusion_sep`, `exclusion_sep`, `head_read_sep`,
`head_absent_sep`: under `Separates` the read is its binding fact alone.
-/
import Kernel.Proofs.Fold
import Kernel.Proofs.TrieMap

namespace Nanodregg.Kernel

variable {D : Type} [Ord D] [DecidableEq D] {K V : Type} [DecidableEq K]

omit [Ord D] [DecidableEq D] [DecidableEq K] in
/-- A trie collision among `L`, under a `Spec` whose hash is the kernel's in `domTrie`, is a
collision among `trieIn L`. -/
theorem collidesAmong_trieIn {E : Env D} {S : Trie.Spec K V D} (hs : ∀ b, S.hash b = E.hash domTrie b)
    {L : List ByteArray} : Trie.CollAmong S L → CollidesAmong E.hash (trieIn L)
  | ⟨a, ha, b, hb, hne, h⟩ =>
      ⟨(domTrie, a), List.mem_map_of_mem ha, (domTrie, b), List.mem_map_of_mem hb,
        fun he => hne (congrArg Prod.snd he), by simpa [hs] using h⟩

/-- **What the head-read family needs of a trie**: injective leaf bodies and node pairs, the node
hash the kernel's in `domTrie`, the leaf digest the kernel's hash of `vpre`, and `vpre` injective on
`Fits`. -/
structure HeadSound (E : Env D) (S : Trie.Spec K V D) (Fits : V → Prop)
    (vpre : V → String × ByteArray) : Prop where
  body_inj : ∀ x y, Trie.leafBody S x = Trie.leafBody S y → x = y
  pair_inj : ∀ a b c e, S.dbytes a ++ S.dbytes b = S.dbytes c ++ S.dbytes e → a = c ∧ b = e
  hash_eq : ∀ b, S.hash b = E.hash domTrie b
  vdigest_eq : ∀ v, S.vdigest v = E.hash (vpre v).1 (vpre v).2
  vpre_inj : ∀ {v v' : V}, Fits v → Fits v' → vpre v = vpre v' → v = v'

namespace HeadSound

variable {E : Env D} {S : Trie.Spec K V D} {Fits : V → Prop} {vpre : V → String × ByteArray}

omit [Ord D] in
/-- **Inclusion is sound**: a claimed value proved against a canonical trie's root, on a trie whose
values and the claimed one fit, is the trie's value, or two of the inputs the read compares collide
(`inclPres`). -/
theorem inclusion (hs : HeadSound E S Fits vpre) {t : Trie.T K V D} (hc : Trie.Canon S 0 t)
    (hfit : ∀ k v, t.get S k = some v → Fits v) {k : K} {v : V} (hv : Fits v) {p : Trie.Proof K D}
    (hp : Trie.verifyInclusion S (t.hashOf S) k (S.vdigest v) p = true) :
    t.get S k = some v ∨ CollidesAmong E.hash (inclPres S vpre k v p t) := by
  rcases Trie.inclusion_sound S hs.body_inj hs.pair_inj hc.2.1 hc.1 hp with ⟨v', hg, hd⟩ | c
  · by_cases he : vpre v' = vpre v
    · rw [hs.vpre_inj (hfit k v' hg) hv he] at hg; exact .inl hg
    · refine .inr ⟨vpre v', ?_, vpre v, List.mem_cons_self .., he, ?_⟩
      · simp [inclPres, hg]
      · rw [← hs.vdigest_eq, ← hs.vdigest_eq]; exact hd
  · refine .inr (CollidesAmong.mono (fun x hx => ?_) (collidesAmong_trieIn hs.hash_eq c))
    simp only [inclPres, List.mem_cons, List.mem_append]
    exact .inr (.inr hx)

omit [Ord D] in
/-- **Exclusion is sound**: a key proved absent against a canonical trie's root is absent, or two of
the inputs the read compares collide (`readPres`). -/
theorem exclusion (hs : HeadSound E S Fits vpre) {t : Trie.T K V D} (hc : Trie.Canon S 0 t) {k : K}
    {p : Trie.Proof K D} (hp : Trie.verifyExclusion S (t.hashOf S) k p = true) :
    t.get S k = none ∨ CollidesAmong E.hash (readPres S k p t) := by
  rcases Trie.exclusion_sound S hs.body_inj hs.pair_inj hc.2.1 hp with h | c
  · exact .inl h
  · exact .inr (collidesAmong_trieIn hs.hash_eq c)

/-- **The phone's read against a head**: given what `head_roots` opens a head record to (up to a
collision among the opening's inputs `H`), a proof against the root `pick` selects, of a canonical
trie whose root that is, is sound as at the World. `H` is the opening's input list: every instance
gets it from `head_roots` / `fold_head_roots` (`headPres …`). -/
theorem head_read (hs : HeadSound E S Fits vpre) (pick : D → D → D → D → D) {t : Trie.T K V D}
    {w' : World D} (hc : Trie.Canon S 0 t)
    (hroot : pick (w'.root E) (w'.journalRoot E) (w'.refusalsRoot E) (w'.rowsRoot E) = t.hashOf S)
    (hfit : ∀ k v, t.get S k = some v → Fits v) {root' jroot' rroot' wroot' : D}
    {H : List (String × ByteArray)}
    (hroots : (root' = w'.root E ∧ jroot' = w'.journalRoot E ∧ rroot' = w'.refusalsRoot E ∧
      wroot' = w'.rowsRoot E) ∨ CollidesAmong E.hash H)
    {k : K} {v : V} (hv : Fits v) {p : Trie.Proof K D}
    (hp : Trie.verifyInclusion S (pick root' jroot' rroot' wroot') k (S.vdigest v) p = true) :
    t.get S k = some v ∨ CollidesAmong E.hash (H ++ inclPres S vpre k v p t) := by
  rcases hroots with ⟨rfl, rfl, rfl, rfl⟩ | col
  · rw [hroot] at hp
    rcases hs.inclusion hc hfit hv hp with h | col
    · exact .inl h
    · exact .inr (CollidesAmong.mono (fun x hx => List.mem_append_right _ hx) col)
  · exact .inr (CollidesAmong.mono (fun x hx => List.mem_append_left _ hx) col)

/-- **The phone's absence against a head**, as `head_read` (`H` the opening's input list, from
`head_roots` / `fold_head_roots`: `headPres …`). -/
theorem head_absent (hs : HeadSound E S Fits vpre) (pick : D → D → D → D → D) {t : Trie.T K V D}
    {w' : World D} (hc : Trie.Canon S 0 t)
    (hroot : pick (w'.root E) (w'.journalRoot E) (w'.refusalsRoot E) (w'.rowsRoot E) = t.hashOf S)
    {root' jroot' rroot' wroot' : D} {H : List (String × ByteArray)}
    (hroots : (root' = w'.root E ∧ jroot' = w'.journalRoot E ∧ rroot' = w'.refusalsRoot E ∧
      wroot' = w'.rowsRoot E) ∨ CollidesAmong E.hash H)
    {k : K} {p : Trie.Proof K D}
    (hp : Trie.verifyExclusion S (pick root' jroot' rroot' wroot') k p = true) :
    t.get S k = none ∨ CollidesAmong E.hash (H ++ readPres S k p t) := by
  rcases hroots with ⟨rfl, rfl, rfl, rfl⟩ | col
  · rw [hroot] at hp
    rcases hs.exclusion hc hp with h | col
    · exact .inl h
    · exact .inr (CollidesAmong.mono (fun x hx => List.mem_append_right _ hx) col)
  · exact .inr (CollidesAmong.mono (fun x hx => List.mem_append_left _ hx) col)

omit [Ord D] in
/-- TOOTH (`inclusion`): under a hash that separates the inputs the read compares, a verified
inclusion is the trie's value. -/
theorem inclusion_sep (hs : HeadSound E S Fits vpre) {t : Trie.T K V D} (hc : Trie.Canon S 0 t)
    (hfit : ∀ k v, t.get S k = some v → Fits v) {k : K} {v : V} (hv : Fits v) {p : Trie.Proof K D}
    (hsep : Separates E.hash (inclPres S vpre k v p t))
    (hp : Trie.verifyInclusion S (t.hashOf S) k (S.vdigest v) p = true) : t.get S k = some v :=
  hsep.elim (hs.inclusion hc hfit hv hp)

omit [Ord D] in
/-- TOOTH (`exclusion`): under a hash that separates the inputs the read compares, a verified
exclusion is the trie's absence. -/
theorem exclusion_sep (hs : HeadSound E S Fits vpre) {t : Trie.T K V D} (hc : Trie.Canon S 0 t)
    {k : K} {p : Trie.Proof K D} (hsep : Separates E.hash (readPres S k p t))
    (hp : Trie.verifyExclusion S (t.hashOf S) k p = true) : t.get S k = none :=
  hsep.elim (hs.exclusion hc hp)

/-- TOOTH (`head_read`): under a hash that separates the opening's and the read's inputs, a read
against a head is the trie's value. -/
theorem head_read_sep (hs : HeadSound E S Fits vpre) (pick : D → D → D → D → D) {t : Trie.T K V D}
    {w' : World D} (hc : Trie.Canon S 0 t)
    (hroot : pick (w'.root E) (w'.journalRoot E) (w'.refusalsRoot E) (w'.rowsRoot E) = t.hashOf S)
    (hfit : ∀ k v, t.get S k = some v → Fits v) {root' jroot' rroot' wroot' : D}
    {H : List (String × ByteArray)}
    (hroots : (root' = w'.root E ∧ jroot' = w'.journalRoot E ∧ rroot' = w'.refusalsRoot E ∧
      wroot' = w'.rowsRoot E) ∨ CollidesAmong E.hash H)
    {k : K} {v : V} (hv : Fits v) {p : Trie.Proof K D}
    (hsep : Separates E.hash (H ++ inclPres S vpre k v p t))
    (hp : Trie.verifyInclusion S (pick root' jroot' rroot' wroot') k (S.vdigest v) p = true) :
    t.get S k = some v :=
  hsep.elim (hs.head_read pick hc hroot hfit hroots hv hp)

/-- TOOTH (`head_absent`), as `head_read_sep`. -/
theorem head_absent_sep (hs : HeadSound E S Fits vpre) (pick : D → D → D → D → D) {t : Trie.T K V D}
    {w' : World D} (hc : Trie.Canon S 0 t)
    (hroot : pick (w'.root E) (w'.journalRoot E) (w'.refusalsRoot E) (w'.rowsRoot E) = t.hashOf S)
    {root' jroot' rroot' wroot' : D} {H : List (String × ByteArray)}
    (hroots : (root' = w'.root E ∧ jroot' = w'.journalRoot E ∧ rroot' = w'.refusalsRoot E ∧
      wroot' = w'.rowsRoot E) ∨ CollidesAmong E.hash H)
    {k : K} {p : Trie.Proof K D} (hsep : Separates E.hash (H ++ readPres S k p t))
    (hp : Trie.verifyExclusion S (pick root' jroot' rroot' wroot') k p = true) : t.get S k = none :=
  hsep.elim (hs.head_absent pick hc hroot hroots hp)

end HeadSound

end Nanodregg.Kernel
