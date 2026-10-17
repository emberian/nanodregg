/-
# Kernel.Proofs.Cells — the World's map is canonical, authenticated, and bound into the chain

KERNEL-23 part 2, at the World:
* `World.Canon`: the World's trie is canonical. Genesis is (`genesis_canon`), and every admitted
  turn keeps it (`admit_canon`, `fold_canon`). Every theorem below takes it as its premise.
* `trie_ext`: two canonical Worlds that hold the same leaf at every slot have the SAME trie, so the
  same root, whatever order their turns ran in (history independence over contents).
* `slot_inclusion_sound` / `slot_exclusion_sound`: a proof that verifies against a World's root
  tells the truth about the slot, or `Collision E.hash`. `prove_verifies` / `prove_excludes'`: the
  World proves every slot it holds, and every slot it does not.
* `head_read_sound`: the phone's theorem. Take a head record `(prev, turnDigest, root')` that hashes
  to the chain of a World an admitted turn reached, and a proof that verifies against `root'`. Then
  that World holds the slot, or the hash collides.
Premises: `E.bytes` is injective with one size `n`, `n ≤ 32` (CODEC proves this for the deployed
digest); `E.cellBytes` is injective on a predicate `F` (`InjOn F E`), and every live cell of the World
satisfies `F` (`w.CellsFit F E`). At the deployed codec `F` must be `Cell.Fits`: `cellBytes` is
injective only there (`Codec.Kernel.cellBytes_injective`). OPEN GAP (KERNEL-30, cv 01a1498e-853e):
no theorem yet shows that genesis, admit and fold keep `CellsFit Cell.Fits`, so these read theorems
cover a World whose cells are known to fit, and the kernel does not yet prove that its own Worlds do.
That proof lands with KERNEL-31.
-/
import Kernel.Proofs.Frame
import Kernel.Proofs.TrieMap
import Kernel.Receive.Follow

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
  exact spendAll_canon _ (insertAll_canon _ (insertAll_canon _ hc))

theorem fold_canon {E : Env D} :
    ∀ {w w' : World D} {l : List (Turn D)}, w.Canon E → World.fold E w l = .ok w' → w'.Canon E
  | w, w', [], hc, h => by simp [World.fold] at h; subst h; exact hc
  | w, w', t :: rest, hc, h => by
      obtain ⟨w₁, h₁, h₂⟩ := fold_cons_ok.mp h
      exact fold_canon (admit_canon hc h₁) h₂

theorem receive_genesis_canon (X : Receive.Ctx D) (name nonce : ByteArray) (allowance : Nat)
    (founders : List (ByteArray × D)) : (Receive.genesis X name nonce allowance founders).Canon X.env :=
  insertAll_canon _ (Trie.canon_empty _ 0)

/-! ## The deployed parameters satisfy the trie's premises -/

section Params
variable {E : Env D} {n : Nat} (hsz : ∀ d, (E.bytes d).size = n) (hb : Function.Injective E.bytes)

omit [Ord D] [DecidableEq D] in
theorem testBit_byte {x : UInt8} {k : Nat} (hk : 8 ≤ k) : x.toNat.testBit k = false :=
  Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le x.toNat_lt (Nat.pow_le_pow_right (by decide) hk))

omit [Ord D] [DecidableEq D] in
/-- Two byte strings of one size with the same bits are equal. -/
theorem byteBit_ext {a b : ByteArray} (hs : a.size = b.size)
    (h : ∀ i, i < 8 * a.size → byteBit a i = byteBit b i) : a = b := by
  apply ByteArray.ext; apply Array.ext (by simpa using hs)
  intro j hja hjb
  have hj : j < a.size := hja
  apply UInt8.toNat_inj.mp
  apply Nat.eq_of_testBit_eq
  intro k
  by_cases hk : k < 8
  · have hi := h (8 * j + (7 - k)) (by omega)
    have e1 : (8 * j + (7 - k)) / 8 = j := by omega
    have e2 : 7 - (8 * j + (7 - k)) % 8 = k := by omega
    unfold byteBit at hi
    simp only [e1, e2, hj, hs ▸ hj, dite_true] at hi
    exact hi
  · rw [testBit_byte (by omega), testBit_byte (by omega)]

include hsz hb in
omit [Ord D] [DecidableEq D] in
/-- The slot bits tell any two slots apart within the trie's depth. -/
theorem slots_separate (hn : n ≤ 32) : Trie.Separates (trieSpec E) := by
  intro k k' hne
  by_cases hk : k.isNullifier = k'.isNullifier
  · have hid : k.id ≠ k'.id := by
      intro he; apply hne
      cases k <;> cases k' <;> simp_all [Slot.isNullifier, Slot.id]
    have hbne : E.bytes k.id ≠ E.bytes k'.id := fun he => hid (hb he)
    have : ∃ i, i < 8 * n ∧ byteBit (E.bytes k.id) i ≠ byteBit (E.bytes k'.id) i := by
      apply Classical.byContradiction; intro hno
      apply hbne; apply byteBit_ext (by rw [hsz, hsz])
      intro i hi
      exact Classical.byContradiction fun hneq => hno ⟨i, by rw [hsz] at hi; exact hi, hneq⟩
    obtain ⟨i, hi, hbit⟩ := this
    exact ⟨i + 1, by show i + 1 < Bounds.trieDepth; unfold Bounds.trieDepth; omega, hbit⟩
  · exact ⟨0, by show 0 < Bounds.trieDepth; decide, hk⟩

include hb in
omit [Ord D] [DecidableEq D] in
theorem slotBytes_inj {s s' : Slot D} (h : slotBytes E s = slotBytes E s') : s = s' := by
  unfold slotBytes at h
  obtain ⟨ht, hi⟩ := bytes_append_inj h rfl
  have hid := hb hi
  have htag : s.isNullifier = s'.isNullifier := by
    by_cases a : s.isNullifier <;> by_cases b : s'.isNullifier <;> simp_all
  cases s <;> cases s' <;> simp_all [Slot.isNullifier, Slot.id]

include hsz hb in
omit [Ord D] [DecidableEq D] in
theorem dbytes_pair_inj : ∀ a b c e : D, E.bytes a ++ E.bytes b = E.bytes c ++ E.bytes e → a = c ∧ b = e := by
  intro a b c e h
  obtain ⟨h1, h2⟩ := bytes_append_inj h (by rw [hsz, hsz])
  exact ⟨hb h1, hb h2⟩

omit [Ord D] [DecidableEq D] in
theorem leafBody_size (kds : List (Slot D × D)) (hsz : ∀ d, (E.bytes d).size = n) :
    (Trie.leafBody (trieSpec E) kds).size = (1 + 2 * n) * kds.length := by
  induction kds with
  | nil => rfl
  | cons p rest ih =>
      show (slotBytes E p.1 ++ E.bytes p.2 ++ Trie.leafBody (trieSpec E) rest).size = _
      simp only [ByteArray.size_append, ih, slotBytes, hsz, List.length_cons]
      simp only [ByteArray.size, Array.size]
      simp; rw [Nat.mul_add, Nat.mul_one]; omega

include hsz hb in
omit [Ord D] [DecidableEq D] in
theorem leafBody_inj : ∀ x y : List (Slot D × D),
    Trie.leafBody (trieSpec E) x = Trie.leafBody (trieSpec E) y → x = y
  | [], [], _ => rfl
  | [], q :: ys, h => by
      have := congrArg ByteArray.size h
      rw [leafBody_size _ hsz, leafBody_size _ hsz] at this
      simp only [List.length_nil, List.length_cons, Nat.mul_zero, Nat.mul_add, Nat.mul_one] at this
      omega
  | p :: xs, [], h => by
      have := congrArg ByteArray.size h
      rw [leafBody_size _ hsz, leafBody_size _ hsz] at this
      simp only [List.length_nil, List.length_cons, Nat.mul_zero, Nat.mul_add, Nat.mul_one] at this
      omega
  | p :: xs, q :: ys, h => by
      change slotBytes E p.1 ++ E.bytes p.2 ++ Trie.leafBody (trieSpec E) xs =
        slotBytes E q.1 ++ E.bytes q.2 ++ Trie.leafBody (trieSpec E) ys at h
      have hs : ∀ (r : Slot D × D), (slotBytes E r.1 ++ E.bytes r.2).size = 1 + 2 * n := by
        intro r; simp only [ByteArray.size_append, slotBytes, hsz]; simp [ByteArray.size]; omega
      obtain ⟨hh, ht⟩ := bytes_append_inj h (by rw [hs, hs])
      have hk : (slotBytes E p.1).size = (slotBytes E q.1).size := by
        simp only [slotBytes, ByteArray.size_append, hsz]; rfl
      obtain ⟨hk', hd⟩ := bytes_append_inj hh hk
      have := leafBody_inj xs ys ht
      rw [Prod.ext (slotBytes_inj hb hk') (hb hd), this]

end Params

/-! ## Inclusion and exclusion at the World -/

omit [Ord D] [DecidableEq D] in
/-- A trie collision is a `Collision` of the kernel's hash (in `domTrie`). -/
theorem coll_collision {E : Env D} (h : Trie.Coll (trieSpec E)) : Collision E.hash := by
  obtain ⟨a, b, hne, he⟩ := h; exact ⟨domTrie, a, b, hne, he⟩

/-- A leaf whose cell (if any) satisfies `F`: the cells on which the cell codec is injective
(deployed: `Codec.Cell.Fits`; the deployed codec is NOT injective on all cells, CODEC-12). -/
def Leaf.CellFit (F : Cell → Prop) : Leaf → Prop
  | .entry (.live c) => F c
  | _ => True

/-- Every leaf the World holds satisfies `F`. -/
def World.CellsFit (F : Cell → Prop) (E : Env D) (w : World D) : Prop :=
  ∀ s l, w.trie.get (trieSpec E) s = some l → l.CellFit F

/-- The cell codec is injective on `F`. -/
def InjOn (F : Cell → Prop) (E : Env D) : Prop :=
  ∀ a b, F a → F b → E.cellBytes a = E.cellBytes b → a = b

omit [Ord D] [DecidableEq D] in
theorem leafBytes_inj {E : Env D} {F : Cell → Prop} (hcb : InjOn F E) {l l' : Leaf}
    (hf : l.CellFit F) (hf' : l'.CellFit F) (h : leafBytes E l = leafBytes E l') : l = l' := by
  have tag : ∀ {a b : UInt8} {x y : ByteArray}, (⟨#[a]⟩ : ByteArray) ++ x = ⟨#[b]⟩ ++ y → a = b ∧ x = y := by
    intro a b x y he
    obtain ⟨h1, h2⟩ := bytes_append_inj he rfl
    exact ⟨by simpa using congrArg (fun z : ByteArray => z.data) h1, h2⟩
  have one : ∀ {a b : UInt8}, (⟨#[a]⟩ : ByteArray) = ⟨#[b]⟩ → a = b := by
    intro a b he; simpa using congrArg (fun z : ByteArray => z.data) he
  have lone : ∀ {a b : UInt8} {x : ByteArray}, (⟨#[a]⟩ : ByteArray) ++ x = ⟨#[b]⟩ → a = b := by
    intro a b x he
    have hd := congrArg (fun z : ByteArray => z.data.toList) he
    simp [ByteArray.data_append] at hd
    exact hd.1
  cases l with
  | entry e =>
      cases e with
      | live c =>
          cases l' with
          | entry e' =>
              cases e' with
              | live c' => obtain ⟨_, hx⟩ := tag h; rw [hcb _ _ hf hf' hx]
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
theorem leafDigest_inj {E : Env D} {F : Cell → Prop} (hcb : InjOn F E) {l l' : Leaf}
    (hf : l.CellFit F) (hf' : l'.CellFit F)
    (h : leafDigest E l = leafDigest E l') : l = l' ∨ Collision E.hash := by
  by_cases hb : leafBytes E l = leafBytes E l'
  · exact .inl (leafBytes_inj hcb hf hf' hb)
  · exact .inr ⟨domLeaf, _, _, hb, h⟩

section Sound
variable {E : Env D} {n : Nat} (hsz : ∀ d, (E.bytes d).size = n) (hb : Function.Injective E.bytes)
include hsz hb

/-- **Inclusion is sound at the World**, for a claimed leaf and a World whose cells the cell codec
encodes injectively (`F`). -/
theorem slot_inclusion_sound {F : Cell → Prop} (hcb : InjOn F E) {w : World D} (hc : w.Canon E)
    (hwf : w.CellsFit F E) {s : Slot D} {l : Leaf} (hlf : l.CellFit F)
    {p : Trie.Proof (Slot D) D} (hv : Trie.verifyInclusion (trieSpec E) (w.root E) s (leafDigest E l) p = true) :
    w.trie.get (trieSpec E) s = some l ∨ Collision E.hash := by
  rcases Trie.inclusion_sound (trieSpec E) (leafBody_inj hsz hb) (dbytes_pair_inj hsz hb) hc.2.1 hv
    with ⟨v, hg, hd⟩ | c
  · rcases leafDigest_inj hcb (hwf s v hg) hlf hd with rfl | c
    · exact .inl hg
    · exact .inr c
  · exact .inr (coll_collision c)

/-- **Exclusion is sound at the World.** -/
theorem slot_exclusion_sound {w : World D} (hc : w.Canon E) {s : Slot D} {p : Trie.Proof (Slot D) D}
    (hv : Trie.verifyExclusion (trieSpec E) (w.root E) s p = true) :
    w.trie.get (trieSpec E) s = none ∨ Collision E.hash := by
  rcases Trie.exclusion_sound (trieSpec E) (leafBody_inj hsz hb) (dbytes_pair_inj hsz hb) hc.2.1 hv
    with h | c
  · exact .inl h
  · exact .inr (coll_collision c)

/-- A live cell proved against the root is the World's live cell, or the hash collides. -/
theorem live_inclusion_sound {F : Cell → Prop} (hcb : InjOn F E) {w : World D} (hc : w.Canon E)
    (hwf : w.CellsFit F E) {c : D} {cell : Cell} (hcf : F cell) {p : Trie.Proof (Slot D) D}
    (hv : Trie.verifyInclusion (trieSpec E) (w.root E) (.cell c) (leafDigest E (.entry (.live cell))) p = true) :
    w.live E c = some cell ∨ Collision E.hash := by
  rcases slot_inclusion_sound hsz hb hcb hc hwf (l := .entry (.live cell)) hcf hv with hg | col
  · left; unfold World.live World.entry; rw [hg]
  · exact .inr col

/-- An unspent nullifier proved against the root is unspent in the World, or the hash collides. -/
theorem unspent_sound {w : World D} (hc : w.Canon E) {nf : D} {p : Trie.Proof (Slot D) D}
    (hv : Trie.verifyExclusion (trieSpec E) (w.root E) (.nullifier nf) p = true) :
    w.isSpent E nf = false ∨ Collision E.hash := by
  rcases slot_exclusion_sound hsz hb hc hv with hg | col
  · left; unfold World.isSpent; rw [hg]; rfl
  · exact .inr col

/-- **History independence at the World.** Two canonical Worlds that hold one leaf at every slot
hold one trie, so one root. -/
theorem trie_ext (hn : n ≤ 32) {a b : World D} (ha : a.Canon E) (hb' : b.Canon E)
    (he : ∀ s, a.trie.get (trieSpec E) s = b.trie.get (trieSpec E) s) : a.trie = b.trie :=
  Trie.eq_of_get_eq (trieSpec E) (slots_separate hsz hb hn) ha hb' he

/-- A head record that hashes to an admitted World's chain names that World's root, or the hash
collides. -/
theorem head_root {w w' : World D} {t : Turn D} (h : World.admit E w t = .ok w') {prev td root' : D}
    (hhead : E.hash domChain (E.bytes prev ++ E.bytes td ++ E.bytes root') = w'.chain) :
    root' = w'.root E ∨ Collision E.hash := by
  rw [admit_chain h] at hhead
  unfold chainNext at hhead
  by_cases hin : E.bytes prev ++ E.bytes td ++ E.bytes root' =
      E.bytes w.chain ++ E.bytes (turnDigest E t) ++ E.bytes (w'.root E)
  · obtain ⟨_, hr⟩ := bytes_append_inj hin (by simp [hsz])
    exact .inl (hb hr)
  · exact .inr ⟨domChain, _, _, hin, hhead⟩

/-- **The phone's read.** A head record that hashes to the chain an admitted turn reached, and a
proof that verifies against the record's root, show a slot of that World, or a collision. -/
theorem head_read_sound {F : Cell → Prop} (hcb : InjOn F E) {w w' : World D} {t : Turn D}
    (hc : w.Canon E) (h : World.admit E w t = .ok w') (hwf : w'.CellsFit F E) {prev td root' : D}
    (hhead : E.hash domChain (E.bytes prev ++ E.bytes td ++ E.bytes root') = w'.chain)
    {s : Slot D} {l : Leaf} (hlf : l.CellFit F) {p : Trie.Proof (Slot D) D}
    (hv : Trie.verifyInclusion (trieSpec E) root' s (leafDigest E l) p = true) :
    w'.trie.get (trieSpec E) s = some l ∨ Collision E.hash := by
  rcases head_root hsz hb h hhead with rfl | col
  · exact slot_inclusion_sound hsz hb hcb (admit_canon hc h) hwf hlf hv
  · exact .inr col

/-- **The phone's read of an absence** (an unspent nullifier, an unused id) against a head. -/
theorem head_absent_sound {w w' : World D} {t : Turn D} (hc : w.Canon E)
    (h : World.admit E w t = .ok w') {prev td root' : D}
    (hhead : E.hash domChain (E.bytes prev ++ E.bytes td ++ E.bytes root') = w'.chain)
    {s : Slot D} {p : Trie.Proof (Slot D) D}
    (hv : Trie.verifyExclusion (trieSpec E) root' s p = true) :
    w'.trie.get (trieSpec E) s = none ∨ Collision E.hash := by
  rcases head_root hsz hb h hhead with rfl | col
  · exact slot_exclusion_sound hsz hb (admit_canon hc h) hv
  · exact .inr col

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
  Trie.prove_excludes (trieSpec E) hc.2.1 (Trie.shallow_of_shape _ 0 _ hc.2.2) hg

end Nanodregg.Kernel
