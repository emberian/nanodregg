/-
# Kernel.Proofs.Cells — the World's map is canonical, authenticated, and bound into the chain

KERNEL-23 part 2, at the World:
* `World.Canon`: the World's trie is canonical. Genesis is (`genesis_canon`), and every admitted
  turn keeps it (`admit_canon`, `fold_canon`). Every theorem below takes it as its premise.
* `trie_ext`: two canonical Worlds that hold the same leaf at every slot have the SAME trie, so the
  same root, whatever order their turns ran in (history independence over contents).
* `slot_inclusion_sound` / `slot_exclusion_sound`: a proof that verifies against a World's root
  tells the truth about the slot, or two of the inputs the read compares collide (`inclPres`,
  `readPres`; KERNEL-56: a collision among SOME two inputs is a theorem of every lawful `Env`).
  `prove_verifies` / `prove_excludes'`: the World proves every slot it holds, and every slot it does
  not.
* `journal_separate`, `journalBody_inj`: the journal trie's parameters meet the same premises (its
  phone theorems: `Kernel.Proofs.JournalHead`).
* `head_read_sound`: the phone's theorem. Take a head record `(prev, turnDigest, root', jroot')` that hashes
  to the chain of a World an admitted turn reached, and a proof that verifies against `root'`. Then
  that World holds the slot, or two of the inputs the opening (`headPres`) and the read compare
  collide. Teeth (`*_sep`): under `Separates` of those inputs, the binding fact alone.
Premises: `hE : E.Lawful n` (`Kernel.Proofs.Lawful`: one digest size `n ≤ 32`, injective digest
bytes, `cellBytes` injective on `Cell.Fits`; it is not injective on every cell, CODEC-12), and every live
cell of the World fits (`w.CellsFit Cell.Fits E`). `Kernel.Proofs.CellsFit` proves that
genesis, admit and fold keep `CellsFit Cell.Fits` (KERNEL-31), and `Kernel.Proofs.RootedDeployed`
discharges every premise at the deployed codec (`deployed_head_read_sound` and the inclusion
instances), for every World a checked genesis and a fold reach.
-/
import Kernel.Proofs.Frame
import Kernel.Proofs.TrieMap
import Kernel.Receive.Follow
import Kernel.Proofs.Lawful
import Kernel.Proofs.Logic.HeadRead

namespace Nanodregg.Kernel

variable {D : Type} [Ord D] [DecidableEq D]

/-- The World's trie is canonical (`Trie.Canon` at the root). -/
def World.Canon (E : Env D) (w : World D) : Prop := Trie.Canon (trieSpec E) 0 w.trie

omit [Ord D] in
theorem insertAll_canon {E : Env D} :
    ∀ {m : Cells D} (ps : List (D × Entry)), Trie.Canon (trieSpec E) 0 m →
      Trie.Canon (trieSpec E) 0 (insertAll E m ps)
  | _, [], h => h
  | _, _ :: rest, h => insertAll_canon rest (Trie.canon_insert _ _ _ h)

omit [Ord D] in
theorem spendAll_canon {E : Env D} :
    ∀ {m : Cells D} (ns : List D), Trie.Canon (trieSpec E) 0 m →
      Trie.Canon (trieSpec E) 0 (spendAll E m ns)
  | _, [], h => h
  | _, _ :: rest, h => spendAll_canon rest (Trie.canon_insert _ _ _ h)

omit [DecidableEq D] in
theorem genesis_canon (E : Env D) (o : D) (a : Nat) : (World.genesis E o a).Canon E :=
  Trie.canon_empty _ 0

theorem admit_canon {E : Env D} {w w' : World D} {t : Turn D} (hc : w.Canon E)
    (h : World.admit E w t = .ok w') : w'.Canon E := by
  obtain ⟨posts, _, rfl⟩ := admit_ok h
  have := spendAll_canon t.nullifiers (insertAll_canon (bornEntries t) (insertAll_canon (posts.map Post.pair) hc))
  rwa [← commit_trie_eq (t := t)] at this

theorem refuse_canon {E : Env D} {w w' : World D} {r : Refused D} (hc : w.Canon E)
    (h : World.refuse E w r = .ok w') : w'.Canon E := by
  show Trie.Canon _ 0 _; rw [refuse_trie h]; exact hc

theorem step_canon {E : Env D} {w w' : World D} {s : Step D} (hc : w.Canon E)
    (h : World.step E w s = .ok w') : w'.Canon E := by
  cases s with
  | turn t => exact admit_canon hc h
  | refusal r => exact refuse_canon hc h

theorem fold_canon {E : Env D} {w w' : World D} {l : List (Step D)} (hc : w.Canon E)
    (h : World.fold E w l = .ok w') : w'.Canon E :=
  fold_keeps (P := fun v => v.Canon E) admit_canon refuse_canon hc h

theorem receive_genesis_canon (X : Receive.Ctx D) (name nonce : ByteArray) (allowance : Nat)
    (founders : List (ByteArray × D)) (auth : Receive.Authority) : (Receive.genesisWorld X name nonce allowance founders auth).Canon X.env :=
  insertAll_canon _ (Trie.canon_empty _ 0)

/-! ## The deployed parameters satisfy the trie's premises -/

section Params
variable {E : Env D} {n : Nat} (hE : E.Lawful n)

include hE in
omit [DecidableEq D] in
/-- The slot bits tell any two slots apart within the trie's depth. -/
theorem slots_separate : Trie.Separates (trieSpec E) := by
  have hn := hE.n_le
  intro k k' hne
  by_cases hk : k.isNullifier = k'.isNullifier
  · have hid : k.id ≠ k'.id := by
      intro he; apply hne
      cases k <;> cases k' <;> simp_all [Slot.isNullifier, Slot.id]
    have hbne : E.bytes k.id ≠ E.bytes k'.id := fun he => hid (hE.bytes_inj he)
    have : ∃ i, i < 8 * n ∧ byteBit (E.bytes k.id) i ≠ byteBit (E.bytes k'.id) i := by
      apply Classical.byContradiction; intro hno
      apply hbne; apply byteBit_ext (by rw [hE.size, hE.size])
      intro i hi
      exact Classical.byContradiction fun hneq => hno ⟨i, by rw [hE.size] at hi; exact hi, hneq⟩
    obtain ⟨i, hi, hbit⟩ := this
    exact ⟨i + 1, by show i + 1 < Bounds.trieDepth; unfold Bounds.trieDepth; omega, hbit⟩
  · exact ⟨0, by show 0 < Bounds.trieDepth; decide, hk⟩

include hE in
omit [DecidableEq D] in
theorem slotBytes_inj {s s' : Slot D} (h : slotBytes E s = slotBytes E s') : s = s' := by
  unfold slotBytes at h
  obtain ⟨ht, hi⟩ := bytes_append_inj h rfl
  have hid := hE.bytes_inj hi
  have htag : s.isNullifier = s'.isNullifier := by
    by_cases a : s.isNullifier <;> by_cases b : s'.isNullifier <;> simp_all
  cases s <;> cases s' <;> simp_all [Slot.isNullifier, Slot.id]

include hE in
omit [DecidableEq D] in
theorem dbytes_pair_inj : ∀ a b c e : D, E.bytes a ++ E.bytes b = E.bytes c ++ E.bytes e → a = c ∧ b = e := by
  intro a b c e h
  obtain ⟨h1, h2⟩ := bytes_append_inj h (by rw [hE.size, hE.size])
  exact ⟨hE.bytes_inj h1, hE.bytes_inj h2⟩

omit [DecidableEq D] in
theorem leafBody_size (kds : List (Slot D × D)) (hE : E.Lawful n) :
    (Trie.leafBody (trieSpec E) kds).size = (1 + 2 * n) * kds.length := by
  induction kds with
  | nil => rfl
  | cons p rest ih =>
      show (slotBytes E p.1 ++ E.bytes p.2 ++ Trie.leafBody (trieSpec E) rest).size = _
      simp only [ByteArray.size_append, ih, slotBytes, hE.size, List.length_cons]
      simp only [ByteArray.size, Array.size]
      simp; rw [Nat.mul_add, Nat.mul_one]; omega

include hE in
omit [DecidableEq D] in
theorem leafBody_inj : ∀ x y : List (Slot D × D),
    Trie.leafBody (trieSpec E) x = Trie.leafBody (trieSpec E) y → x = y
  | [], [], _ => rfl
  | [], q :: ys, h => by
      have := congrArg ByteArray.size h
      rw [leafBody_size _ hE, leafBody_size _ hE] at this
      simp only [List.length_nil, List.length_cons, Nat.mul_zero, Nat.mul_add, Nat.mul_one] at this
      omega
  | p :: xs, [], h => by
      have := congrArg ByteArray.size h
      rw [leafBody_size _ hE, leafBody_size _ hE] at this
      simp only [List.length_nil, List.length_cons, Nat.mul_zero, Nat.mul_add, Nat.mul_one] at this
      omega
  | p :: xs, q :: ys, h => by
      change slotBytes E p.1 ++ E.bytes p.2 ++ Trie.leafBody (trieSpec E) xs =
        slotBytes E q.1 ++ E.bytes q.2 ++ Trie.leafBody (trieSpec E) ys at h
      have hs : ∀ (r : Slot D × D), (slotBytes E r.1 ++ E.bytes r.2).size = 1 + 2 * n := by
        intro r; simp only [ByteArray.size_append, slotBytes, hE.size]; simp [ByteArray.size]; omega
      obtain ⟨hh, ht⟩ := bytes_append_inj h (by rw [hs, hs])
      have hk : (slotBytes E p.1).size = (slotBytes E q.1).size := by
        simp only [slotBytes, ByteArray.size_append, hE.size]; rfl
      obtain ⟨hk', hd⟩ := bytes_append_inj hh hk
      have := leafBody_inj xs ys ht
      rw [Prod.ext (slotBytes_inj hE hk') (hE.bytes_inj hd), this]

include hE in
omit [DecidableEq D] in
/-- **The journal's bits tell any two transaction ids apart within its depth** (KERNEL-41). -/
theorem journal_separate : Trie.Separates (journalSpec E) := by
  have hn := hE.n_le
  intro k k' hne
  have hbne : E.bytes k ≠ E.bytes k' := fun he => hne (hE.bytes_inj he)
  have : ∃ i, i < 8 * n ∧ byteBit (E.bytes k) i ≠ byteBit (E.bytes k') i := by
    apply Classical.byContradiction; intro hno
    apply hbne; apply byteBit_ext (by rw [hE.size, hE.size])
    intro i hi
    exact Classical.byContradiction fun hneq => hno ⟨i, by rw [hE.size] at hi; exact hi, hneq⟩
  obtain ⟨i, hi, hbit⟩ := this
  exact ⟨i, by show i < Bounds.journalDepth; unfold Bounds.journalDepth; omega, hbit⟩

omit [DecidableEq D] in
theorem refusalKeyBytes_size (hE : E.Lawful n) (k : WindowSlot D) : (refusalKeyBytes E k).size = 1 + n + 8 := by
  rcases k with k | k <;> cases k <;> simp [refusalKeyBytes, hE.size, Nanodregg.Codec.Stream.nat64_bytes] <;> rfl

include hE in
omit [DecidableEq D] in
/-- A refusals key's bytes determine it (a kind byte, a digest of fixed size, eight bytes). -/
theorem refusalKeyBytes_inj {k k' : WindowSlot D} (h : refusalKeyBytes E k = refusalKeyBytes E k') : k = k' := by
  have hsz : ∀ d : D, (E.bytes d).size = n := hE.size
  rcases k with k | k <;> rcases k' with k' | k' <;> cases k <;> cases k' <;> simp only [refusalKeyBytes, Nanodregg.Codec.Stream.nat64_bytes] at h <;>
    obtain ⟨h1, hw⟩ := bytes_append_inj h (by simp [hsz]) <;>
    obtain ⟨h0, hm⟩ := bytes_append_inj h1 rfl <;>
    (try (have := congrArg (fun z : ByteArray => z.data.toList) h0; simp at this; done)) <;>
    (try (rw [hE.bytes_inj hm]; done)) <;>
    rw [hE.bytes_inj hm, Nanodregg.Codec.Stream.bytes_injective Nanodregg.Codec.Stream.u64_lawful hw]

include hE in
omit [DecidableEq D] in
/-- **The refusals trie's bits tell any two keys apart within its depth** (KERNEL-47 amendment 4):
no premise but a lawful `Env`. A refused id, a count and a total never share a route (the kind
byte), two counts (or two totals) differ in their digest or their window's eight bytes. -/
theorem refusals_separate : Trie.Separates (refusalSpec E) := by
  have hn := hE.n_le
  intro k k' hne
  have hbne : refusalKeyBytes E k ≠ refusalKeyBytes E k' := fun he => hne (refusalKeyBytes_inj hE he)
  have : ∃ i, i < 8 * (1 + n + 8) ∧ byteBit (refusalKeyBytes E k) i ≠ byteBit (refusalKeyBytes E k') i := by
    apply Classical.byContradiction; intro hno
    apply hbne; apply byteBit_ext (by rw [refusalKeyBytes_size hE, refusalKeyBytes_size hE])
    intro i hi
    exact Classical.byContradiction fun hneq =>
      hno ⟨i, by rw [refusalKeyBytes_size hE] at hi; exact hi, hneq⟩
  obtain ⟨i, hi, hbit⟩ := this
  exact ⟨i, by show i < Bounds.refusalDepth; unfold Bounds.refusalDepth; omega, hbit⟩

omit [DecidableEq D] in
theorem journalBody_size (kds : List (D × D)) (hE : E.Lawful n) :
    (Trie.leafBody (journalSpec E) kds).size = (2 * n) * kds.length := by
  induction kds with
  | nil => rfl
  | cons p rest ih =>
      show (E.bytes p.1 ++ E.bytes p.2 ++ Trie.leafBody (journalSpec E) rest).size = _
      simp only [ByteArray.size_append, ih, hE.size, List.length_cons]
      rw [Nat.mul_add, Nat.mul_one]; omega

include hE in
omit [DecidableEq D] in
/-- A journal leaf's body determines its entries, at a digest of at least one byte (`hn`: with no
bytes there is nothing to tell an empty leaf from a full one; the deployed digest has 32). -/
theorem journalBody_inj (hn : 0 < n) : ∀ x y : List (D × D),
    Trie.leafBody (journalSpec E) x = Trie.leafBody (journalSpec E) y → x = y
  | [], [], _ => rfl
  | [], q :: ys, h => by
      have := congrArg ByteArray.size h
      rw [journalBody_size _ hE, journalBody_size _ hE] at this
      simp only [List.length_nil, List.length_cons, Nat.mul_zero, Nat.mul_add, Nat.mul_one] at this
      have : 0 < 2 * n * ys.length + 2 * n := by omega
      omega
  | p :: xs, [], h => by
      have := congrArg ByteArray.size h
      rw [journalBody_size _ hE, journalBody_size _ hE] at this
      simp only [List.length_nil, List.length_cons, Nat.mul_zero, Nat.mul_add, Nat.mul_one] at this
      omega
  | p :: xs, q :: ys, h => by
      change E.bytes p.1 ++ E.bytes p.2 ++ Trie.leafBody (journalSpec E) xs =
        E.bytes q.1 ++ E.bytes q.2 ++ Trie.leafBody (journalSpec E) ys at h
      obtain ⟨hh, ht⟩ := bytes_append_inj h (by simp only [ByteArray.size_append, hE.size])
      obtain ⟨hk, hd⟩ := bytes_append_inj hh (by rw [hE.size, hE.size])
      rw [Prod.ext (hE.bytes_inj hk) (hE.bytes_inj hd), journalBody_inj hn xs ys ht]

end Params

/-! ## Inclusion and exclusion at the World -/

/-- A leaf whose cell (if any) satisfies `F`: the cells on which the cell codec is injective
(deployed: `Codec.Cell.Fits`; the deployed codec is NOT injective on all cells, CODEC-12), with its
version below 2^64 (KERNEL-54: `leafBytes` spells it in eight bytes). -/
def Leaf.CellFit (F : Cell → Prop) : Leaf → Prop
  | .entry (.live c v) => F c ∧ v < 2 ^ 64
  | _ => True

/-- Every leaf the World holds satisfies `F`. -/
def World.CellsFit (F : Cell → Prop) (E : Env D) (w : World D) : Prop :=
  ∀ s l, w.trie.get (trieSpec E) s = some l → l.CellFit F

omit [Ord D] [DecidableEq D] in
theorem leafBytes_inj {E : Env D} {F : Cell → Prop} (hcb : InjOn F E) {l l' : Leaf}
    (hf : l.CellFit F) (hf' : l'.CellFit F) (h : leafBytes E l = leafBytes E l') : l = l' := by
  have one : ∀ {a b : UInt8}, (⟨#[a]⟩ : ByteArray) = ⟨#[b]⟩ → a = b := by
    intro a b he; simpa using congrArg (fun z : ByteArray => z.data) he
  have lone : ∀ {a b : UInt8} {x y : ByteArray}, (⟨#[a]⟩ : ByteArray) ++ x ++ y = ⟨#[b]⟩ → a = b := by
    intro a b x y he
    have hd := congrArg (fun z : ByteArray => z.data.toList) he
    simp [ByteArray.data_append] at hd
    exact hd.1
  cases l with
  | entry e =>
      cases e with
      | live c v =>
          cases l' with
          | entry e' =>
              cases e' with
              | live c' v' =>
                  obtain ⟨h1, hx⟩ := bytes_append_inj h
                    (by simp only [ByteArray.size_append, nat64_size])
                  obtain ⟨_, hn⟩ := bytes_append_inj h1 rfl
                  have hv := Nanodregg.Codec.Stream.nat64_lawfulOn.bytes_injective hf.2 hf'.2 hn
                  rw [hcb _ _ hf.1 hf'.1 hx, hv]
              | tomb => have := lone h; simp at this
          | spent => have := lone h; simp at this
      | tomb =>
          cases l' with
          | entry e' =>
              cases e' with
              | live c' => have := lone h.symm; simp at this
              | tomb => rfl
          | spent => have := one h; simp at this
  | spent =>
      cases l' with
      | entry e' =>
          cases e' with
          | live c' => have := lone h.symm; simp at this
          | tomb => have := one h; simp at this
      | spent => rfl

omit [Ord D] [DecidableEq D] in
/-- A leaf digest determines its leaf on `F`, or the two inputs collide (in `domLeaf`). -/
theorem leafDigest_inj {E : Env D} {F : Cell → Prop} (hcb : InjOn F E) {l l' : Leaf}
    (hf : l.CellFit F) (hf' : l'.CellFit F)
    (h : leafDigest E l = leafDigest E l') : l = l' ∨ CollidesAmong E.hash [leafPre E l, leafPre E l'] := by
  by_cases hb : leafBytes E l = leafBytes E l'
  · exact .inl (leafBytes_inj hcb hf hf' hb)
  · exact .inr (.pair (fun he => hb (congrArg Prod.snd he)) h)

section Sound
variable {E : Env D} {n : Nat} (hE : E.Lawful n)
include hE

omit [DecidableEq D] in
/-- **The cells' trie is a `HeadSound` instance** (KERNEL-52) on `Leaf.CellFit Cell.Fits`, where
the cell codec is injective (`hE.cellBytes_injOn`). -/
theorem cells_headSound : HeadSound E (trieSpec E) (Leaf.CellFit Codec.Kernel.Cell.Fits) (leafPre E) :=
  ⟨leafBody_inj hE, dbytes_pair_inj hE, fun _ => rfl, fun _ => rfl,
    fun hf hf' h => leafBytes_inj hE.cellBytes_injOn hf hf' (congrArg Prod.snd h)⟩

/-- **Inclusion is sound at the World**, for a claimed leaf and a World whose cells fit
(`Cell.Fits`, where a lawful `Env`'s cell codec is injective), or two of the inputs the read compares
collide (`inclPres`). -/
theorem slot_inclusion_sound {w : World D} (hc : w.Canon E)
    (hwf : w.CellsFit Codec.Kernel.Cell.Fits E) {s : Slot D} {l : Leaf}
    (hlf : l.CellFit Codec.Kernel.Cell.Fits)
    {p : Trie.Proof (Slot D) D} (hv : Trie.verifyInclusion (trieSpec E) (w.root E) s (leafDigest E l) p = true) :
    w.trie.get (trieSpec E) s = some l ∨ CollidesAmong E.hash (inclPres (trieSpec E) (leafPre E) s l p w.trie) :=
  (cells_headSound hE).inclusion hc hwf hlf hv

/-- **Exclusion is sound at the World**, or two of the inputs the read compares collide
(`readPres`). -/
theorem slot_exclusion_sound {w : World D} (hc : w.Canon E) {s : Slot D} {p : Trie.Proof (Slot D) D}
    (hv : Trie.verifyExclusion (trieSpec E) (w.root E) s p = true) :
    w.trie.get (trieSpec E) s = none ∨ CollidesAmong E.hash (readPres (trieSpec E) s p w.trie) :=
  (cells_headSound hE).exclusion hc hv

/-- A live cell proved against the root is the World's live cell, or two of the inputs the read
compares collide. -/
theorem live_inclusion_sound {w : World D} (hc : w.Canon E)
    (hwf : w.CellsFit Codec.Kernel.Cell.Fits E) {c : D} {cell : Cell} {v : Nat}
    (hcf : (Leaf.entry (.live cell v)).CellFit Codec.Kernel.Cell.Fits)
    {p : Trie.Proof (Slot D) D}
    (hv : Trie.verifyInclusion (trieSpec E) (w.root E) (.cell c) (leafDigest E (.entry (.live cell v))) p = true) :
    w.entry E c = some (.live cell v) ∨
      CollidesAmong E.hash (inclPres (trieSpec E) (leafPre E) (.cell c) (.entry (.live cell v)) p w.trie) := by
  rcases slot_inclusion_sound hE hc hwf hcf hv with hg | col
  · left; unfold World.entry; rw [hg]
  · exact .inr col

/-- An unspent nullifier proved against the root is unspent in the World, or two of the inputs the
read compares collide. -/
theorem unspent_sound {w : World D} (hc : w.Canon E) {nf : D} {p : Trie.Proof (Slot D) D}
    (hv : Trie.verifyExclusion (trieSpec E) (w.root E) (.nullifier nf) p = true) :
    w.isSpent E nf = false ∨ CollidesAmong E.hash (readPres (trieSpec E) (.nullifier nf) p w.trie) := by
  rcases slot_exclusion_sound hE hc hv with hg | col
  · left; unfold World.isSpent; rw [hg]; rfl
  · exact .inr col

/-- **History independence at the World.** Two canonical Worlds that hold one leaf at every slot
hold one trie, so one root. -/
theorem trie_ext {a b : World D} (ha : a.Canon E) (hb' : b.Canon E)
    (he : ∀ s, a.trie.get (trieSpec E) s = b.trie.get (trieSpec E) s) : a.trie = b.trie :=
  Trie.eq_of_get_eq (trieSpec E) (slots_separate hE) ha hb' he

omit [DecidableEq D] in
/-- A head record that hashes to a chain link names that link's roots digest, or the record's and
the link's inputs collide. -/
theorem headLink_roots {c prev td rd : D} {g : UInt8} {s : Step D} {rs : D}
    (hhead : headLink E prev g td rd = stepLink E c s rs) :
    rd = rs ∨ CollidesAmong E.hash [linkPre E prev g td rd, stepLinkPre E c s rs] := by
  rw [stepLink_eq] at hhead
  rcases headLink_inj hE hhead with ⟨_, _, _, h⟩ | col
  · exact .inl h
  · exact .inr col

omit [DecidableEq D] in
/-- The roots digest opens to one quadruple of roots, or the two inputs collide (in `domRoots`). -/
theorem rootsDigest_inj {a b c d a' b' c' d' : D} (h : rootsDigest E a b c d = rootsDigest E a' b' c' d') :
    (a = a' ∧ b = b' ∧ c = c' ∧ d = d') ∨ CollidesAmong E.hash [rootsPre E a b c d, rootsPre E a' b' c' d'] := by
  unfold rootsDigest at h
  by_cases hin : E.bytes a ++ E.bytes b ++ E.bytes c ++ E.bytes d =
      E.bytes a' ++ E.bytes b' ++ E.bytes c' ++ E.bytes d'
  · obtain ⟨habc, hd⟩ := bytes_append_inj hin (by simp [hE.size])
    obtain ⟨hab, hc⟩ := bytes_append_inj habc (by simp [hE.size])
    obtain ⟨ha, hb⟩ := bytes_append_inj hab (by simp [hE.size])
    exact .inl ⟨hE.bytes_inj ha, hE.bytes_inj hb, hE.bytes_inj hc, hE.bytes_inj hd⟩
  · exact .inr (.pair (fun he => hin (congrArg Prod.snd he)) h)

/-- A head record that hashes to the chain a step reached, with its roots digest opened, names that
World's four roots (cells', journal's, refusals', rows'), or two of the inputs the opening compares
collide (`headPres`: the record's link against the step's, the record's roots against the World's).
Any step: a phone reads a head after a recorded refusal as after a Turn. -/
theorem head_roots {w w' : World D} {s : Step D} (h : World.step E w s = .ok w')
    {prev td rd root' jroot' rroot' wroot' : D} {g : UInt8} (hhead : headLink E prev g td rd = w'.chain)
    (hrd : rootsDigest E root' jroot' rroot' wroot' = rd) :
    (root' = w'.root E ∧ jroot' = w'.journalRoot E ∧ rroot' = w'.refusalsRoot E ∧ wroot' = w'.rowsRoot E) ∨
      CollidesAmong E.hash (headPres E w [s] w' prev g td rd root' jroot' rroot' wroot') := by
  have hl : foldLinks E w [s] = [stepLinkPre E w.chain s (w'.roots E)] := by simp [foldLinks, h]
  rw [step_chain h] at hhead
  rcases headLink_roots hE hhead with rfl | col
  · rw [World.roots_eq] at hrd
    rcases rootsDigest_inj hE hrd with hr | col
    · exact .inl hr
    · refine .inr (CollidesAmong.mono (fun x hx => ?_) col)
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
      rcases hx with rfl | rfl <;> simp [headPres, World.rootsPre]
  · refine .inr (CollidesAmong.mono (fun x hx => ?_) col)
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl <;> simp [headPres, hl]

/-- A head record that hashes to a stepped World's chain names that World's root, or two of the
inputs the opening compares collide. -/
theorem head_root {w w' : World D} {s : Step D} (h : World.step E w s = .ok w') {prev td rd root' jroot' rroot' wroot' : D}
    {g : UInt8} (hhead : headLink E prev g td rd = w'.chain) (hrd : rootsDigest E root' jroot' rroot' wroot' = rd) :
    root' = w'.root E ∨ CollidesAmong E.hash (headPres E w [s] w' prev g td rd root' jroot' rroot' wroot') := by
  rcases head_roots hE h hhead hrd with ⟨hr, _⟩ | col
  · exact .inl hr
  · exact .inr col

/-- **The phone's read.** A head record that hashes to the chain a step reached, its roots digest
opened, and a proof that verifies against the opened cells' root, show a slot of that World, or two
of the inputs the opening and the read compare collide. -/
theorem head_read_sound {w w' : World D} {s : Step D}
    (hc : w.Canon E) (h : World.step E w s = .ok w') (hwf : w'.CellsFit Codec.Kernel.Cell.Fits E)
    {prev td rd root' jroot' rroot' wroot' : D} {g : UInt8}
    (hhead : headLink E prev g td rd = w'.chain) (hrd : rootsDigest E root' jroot' rroot' wroot' = rd)
    {sl : Slot D} {l : Leaf} (hlf : l.CellFit Codec.Kernel.Cell.Fits)
    {p : Trie.Proof (Slot D) D}
    (hv : Trie.verifyInclusion (trieSpec E) root' sl (leafDigest E l) p = true) :
    w'.trie.get (trieSpec E) sl = some l ∨
      CollidesAmong E.hash (headPres E w [s] w' prev g td rd root' jroot' rroot' wroot' ++
        inclPres (trieSpec E) (leafPre E) sl l p w'.trie) :=
  (cells_headSound hE).head_read (fun r _ _ _ => r) (step_canon hc h) rfl hwf (head_roots hE h hhead hrd) hlf hv

/-- **The phone's read of an absence** (an unspent nullifier, an unused id) against a head. -/
theorem head_absent_sound {w w' : World D} {s : Step D} (hc : w.Canon E)
    (h : World.step E w s = .ok w') {prev td rd root' jroot' rroot' wroot' : D} {g : UInt8}
    (hhead : headLink E prev g td rd = w'.chain) (hrd : rootsDigest E root' jroot' rroot' wroot' = rd)
    {sl : Slot D} {p : Trie.Proof (Slot D) D}
    (hv : Trie.verifyExclusion (trieSpec E) root' sl p = true) :
    w'.trie.get (trieSpec E) sl = none ∨
      CollidesAmong E.hash (headPres E w [s] w' prev g td rd root' jroot' rroot' wroot' ++
        readPres (trieSpec E) sl p w'.trie) :=
  (cells_headSound hE).head_absent (fun r _ _ _ => r) (step_canon hc h) rfl (head_roots hE h hhead hrd) hv

/-! ### Teeth: under `Separates` of the inputs each theorem names, its binding fact alone -/

omit [DecidableEq D] in
/-- TOOTH (`leafDigest_inj`). -/
theorem leafDigest_inj_sep {l l' : Leaf} (hf : l.CellFit Codec.Kernel.Cell.Fits)
    (hf' : l'.CellFit Codec.Kernel.Cell.Fits) (hsep : Separates E.hash [leafPre E l, leafPre E l'])
    (h : leafDigest E l = leafDigest E l') : l = l' :=
  hsep.elim (leafDigest_inj hE.cellBytes_injOn hf hf' h)

omit [DecidableEq D] in
/-- TOOTH (`rootsDigest_inj`). -/
theorem rootsDigest_inj_sep {a b c d a' b' c' d' : D}
    (hsep : Separates E.hash [rootsPre E a b c d, rootsPre E a' b' c' d'])
    (h : rootsDigest E a b c d = rootsDigest E a' b' c' d') : a = a' ∧ b = b' ∧ c = c' ∧ d = d' :=
  hsep.elim (rootsDigest_inj hE h)

/-- TOOTH (`slot_inclusion_sound`). -/
theorem slot_inclusion_sound_sep {w : World D} (hc : w.Canon E)
    (hwf : w.CellsFit Codec.Kernel.Cell.Fits E) {s : Slot D} {l : Leaf}
    (hlf : l.CellFit Codec.Kernel.Cell.Fits) {p : Trie.Proof (Slot D) D}
    (hsep : Separates E.hash (inclPres (trieSpec E) (leafPre E) s l p w.trie))
    (hv : Trie.verifyInclusion (trieSpec E) (w.root E) s (leafDigest E l) p = true) :
    w.trie.get (trieSpec E) s = some l :=
  hsep.elim (slot_inclusion_sound hE hc hwf hlf hv)

/-- TOOTH (`slot_exclusion_sound`). -/
theorem slot_exclusion_sound_sep {w : World D} (hc : w.Canon E) {s : Slot D} {p : Trie.Proof (Slot D) D}
    (hsep : Separates E.hash (readPres (trieSpec E) s p w.trie))
    (hv : Trie.verifyExclusion (trieSpec E) (w.root E) s p = true) :
    w.trie.get (trieSpec E) s = none :=
  hsep.elim (slot_exclusion_sound hE hc hv)

/-- TOOTH (`head_roots`): under a hash that separates the opening's inputs, a head record that
hashes to a stepped World's chain opens to that World's roots. -/
theorem head_roots_sep {w w' : World D} {s : Step D} (h : World.step E w s = .ok w')
    {prev td rd root' jroot' rroot' wroot' : D} {g : UInt8}
    (hsep : Separates E.hash (headPres E w [s] w' prev g td rd root' jroot' rroot' wroot'))
    (hhead : headLink E prev g td rd = w'.chain) (hrd : rootsDigest E root' jroot' rroot' wroot' = rd) :
    root' = w'.root E ∧ jroot' = w'.journalRoot E ∧ rroot' = w'.refusalsRoot E ∧ wroot' = w'.rowsRoot E :=
  hsep.elim (head_roots hE h hhead hrd)

/-- TOOTH (`head_read_sound`). -/
theorem head_read_sound_sep {w w' : World D} {s : Step D}
    (hc : w.Canon E) (h : World.step E w s = .ok w') (hwf : w'.CellsFit Codec.Kernel.Cell.Fits E)
    {prev td rd root' jroot' rroot' wroot' : D} {g : UInt8}
    (hhead : headLink E prev g td rd = w'.chain) (hrd : rootsDigest E root' jroot' rroot' wroot' = rd)
    {sl : Slot D} {l : Leaf} (hlf : l.CellFit Codec.Kernel.Cell.Fits) {p : Trie.Proof (Slot D) D}
    (hsep : Separates E.hash (headPres E w [s] w' prev g td rd root' jroot' rroot' wroot' ++
      inclPres (trieSpec E) (leafPre E) sl l p w'.trie))
    (hv : Trie.verifyInclusion (trieSpec E) root' sl (leafDigest E l) p = true) :
    w'.trie.get (trieSpec E) sl = some l :=
  hsep.elim (head_read_sound hE hc h hwf hhead hrd hlf hv)

/-- TOOTH (`head_absent_sound`). -/
theorem head_absent_sound_sep {w w' : World D} {s : Step D} (hc : w.Canon E)
    (h : World.step E w s = .ok w') {prev td rd root' jroot' rroot' wroot' : D} {g : UInt8}
    (hhead : headLink E prev g td rd = w'.chain) (hrd : rootsDigest E root' jroot' rroot' wroot' = rd)
    {sl : Slot D} {p : Trie.Proof (Slot D) D}
    (hsep : Separates E.hash (headPres E w [s] w' prev g td rd root' jroot' rroot' wroot' ++
      readPres (trieSpec E) sl p w'.trie))
    (hv : Trie.verifyExclusion (trieSpec E) root' sl p = true) :
    w'.trie.get (trieSpec E) sl = none :=
  hsep.elim (head_absent_sound hE hc h hhead hrd hv)

end Sound

/-- **A World proves what it holds.** -/
theorem prove_verifies {E : Env D} {w : World D} (hc : w.Canon E) {s : Slot D} {l : Leaf}
    (hg : w.trie.get (trieSpec E) s = some l) :
    Trie.verifyInclusion (trieSpec E) (w.root E) s (leafDigest E l) (w.trie.prove (trieSpec E) s) = true :=
  Trie.prove_includes (trieSpec E) hc.2.1 (Trie.shallow_of_shape _ 0 _ hc.2.2) hg

/-- **A World proves what it does not hold.** -/
theorem prove_absent {E : Env D} {w : World D} (hc : w.Canon E) {s : Slot D}
    (hg : w.trie.get (trieSpec E) s = none) :
    Trie.verifyExclusion (trieSpec E) (w.root E) s (w.trie.prove (trieSpec E) s) = true :=
  Trie.prove_excludes (trieSpec E) hc.2.1 hc.1 (Trie.shallow_of_shape _ 0 _ hc.2.2) hg

end Nanodregg.Kernel
