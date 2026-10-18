import Codec.Proofs.SlotOrder
import Codec.Proofs.RowOrder
import Kernel.Proofs.RootedDeployed

/-!
# The deployed World listing is ordered by its bytes (CODEC-28 step 2)

At the deployed codec, `kernel/trie-order` accepts the World's trie listing exactly when it is
strictly ascending by (kind: cells first, then the id's 32 bytes in `Digest` order), and refuses every
other listing by name (`trieOrder_iff`, `trieOrder_refuses`, `trieOrder_accepted`). The statement
names no trie: it is pinned to `Digest`'s `compare`, so a change of KERNEL's routing (`slotBit`,
`byteBit`, `trieSpec`'s depth) breaks `Codec.Kernel.bitLt_trieSpec_iff` here instead of moving what
a base's bytes must look like.

Teeth, over two cell ids that differ in byte 0 (`lo` = 0x01…, `hi` = 0x80…):
* `cells_refuses_bytes_descending`: the listing `hi, lo` is refused `kernel/trie-order` by name;
  `cells_reads_bytes_ascending`: `lo, hi` is read back.
* `lsbRouting_refuted`: a routing that reads each id byte low bit first is not the byte order (the
  order theorem is false for it), and its check admits the listing `hi, lo` that the deployed codec
  refuses: the mutation would have changed which bytes decode.
* The journal (KERNEL-41): `journalOrder_iff` / `journalOrder_refuses`, and the teeth
  `journal_refuses_ids_descending` / `journal_reads_ids_ascending`.
-/

namespace Nanodregg.Codec.Deployed

open Nanodregg.Kernel Nanodregg.Codec.Kernel Nanodregg.Codec.Stream

/-- At the deployed digest, `SlotBefore` is cells first, then `Digest`'s own order. -/
theorem slotBefore_iff (s s' : Slot Digest) :
    SlotBefore env s s' ↔ (s.isNullifier = false ∧ s'.isNullifier = true) ∨
      (s.isNullifier = s'.isNullifier ∧ compare s.id s'.id = .lt) := Iff.rfl

/-- **The deployed trie listing is accepted exactly when strictly ascending by (kind, id bytes).** -/
theorem trieOrder_iff {b : ByteArray} {i j : Nat} {l : List (Slot Digest × Leaf)}
    (h : (fitList digestCodec).get b i = .ok (l, j)) :
    (cells env digestCodec).get b i = .ok (Trie.build (trieSpec env) (trieSpec env).depth 0 l, j) ↔
      l.Pairwise (fun p q => SlotBefore env p.1 q.1) := by
  constructor
  · intro hc
    by_cases ho : l.Pairwise (fun p q => SlotBefore env p.1 q.1)
    · exact ho
    · rw [cells_get_refused_slotBefore Receive.deployed_lawful h ho] at hc; cases hc
  · exact cells_get_ok_slotBefore Receive.deployed_lawful h

/-- **Any other deployed listing is refused `kernel/trie-order` by name.** -/
theorem trieOrder_refuses {b : ByteArray} {i j : Nat} {l : List (Slot Digest × Leaf)}
    (h : (fitList digestCodec).get b i = .ok (l, j)) (ho : ¬ l.Pairwise (fun p q => SlotBefore env p.1 q.1)) :
    (cells env digestCodec).get b i = .error (.rejected i "kernel/trie-order") :=
  cells_get_refused_slotBefore Receive.deployed_lawful h ho

/-- Whatever the deployed trie part reads was a listing strictly ascending by (kind, id bytes). -/
theorem trieOrder_accepted {b : ByteArray} {i j : Nat} {t : Cells Digest}
    (h : (cells env digestCodec).get b i = .ok (t, j)) :
    ∃ l, (fitList digestCodec).get b i = .ok (l, j) ∧ l.Pairwise (fun p q => SlotBefore env p.1 q.1) ∧
      t = Trie.build (trieSpec env) (trieSpec env).depth 0 l :=
  cells_get_slotBefore Receive.deployed_lawful h

/-! ## Teeth -/

private def lo : Digest := ⟨⟨#[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩, by decide⟩
private def hi : Digest := ⟨⟨#[128, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩, by decide⟩

private theorem lo_hi : compare lo hi = .lt :=
  (compare_lt_iff_bits (a := lo.bytes) (b := hi.bytes) (by decide)).mpr
    ⟨0, fun _ h => absurd h (by omega), by decide, by decide⟩

private theorem hi_lo : compare hi lo = .gt := by
  rw [Std.OrientedCmp.eq_swap (cmp := compare), lo_hi]; rfl

private theorem fitList_get (l : List (Slot Digest × Leaf))
    (hf : TrieListFits (fun _ => True) l ∧ ∀ p ∈ l, Leaf.fits p.1 p.2 = true) :
    (fitList digestCodec).get ((fitList digestCodec).bytes l) 0 =
      .ok (l, ((fitList digestCodec).bytes l).size) := by
  simpa using (fitList_lawfulOn digest_lawful.on).get_of_occurs l _ 0 hf (occursAt_self _)

/-- **Tooth.** Two cells listed with their ids in descending byte order are refused
`kernel/trie-order` by name. -/
theorem cells_refuses_bytes_descending :
    (cells env digestCodec).decode
        ((fitList digestCodec).bytes [(.cell hi, .entry .tomb), (.cell lo, .entry .tomb)]) =
      .error (.rejected 0 "kernel/trie-order") := by
  have hg := fitList_get [(.cell hi, .entry .tomb), (.cell lo, .entry .tomb)]
    ⟨⟨by decide, by simp [Entry.Fits, Leaf.Fits]⟩, by decide⟩
  have ho : ¬ [((Slot.cell hi : Slot Digest), Leaf.entry .tomb), (.cell lo, .entry .tomb)].Pairwise
      (fun p q => SlotBefore env p.1 q.1) := by
    intro hp
    rcases (List.pairwise_cons.mp hp).1 _ (List.mem_singleton_self _) with ⟨_, h⟩ | ⟨_, h⟩
    · cases h
    · have : compare hi lo = .lt := h
      rw [hi_lo] at this; cases this
  unfold Stream.decode
  rw [trieOrder_refuses hg ho]

/-- The same two cells in ascending byte order are read back. -/
theorem cells_reads_bytes_ascending :
    (cells env digestCodec).decode
        ((fitList digestCodec).bytes [(.cell lo, .entry .tomb), (.cell hi, .entry .tomb)]) =
      .ok (Trie.build (trieSpec env) (trieSpec env).depth 0 [(.cell lo, .entry .tomb), (.cell hi, .entry .tomb)]) := by
  have hg := fitList_get [(.cell lo, .entry .tomb), (.cell hi, .entry .tomb)]
    ⟨⟨by decide, by simp [Entry.Fits, Leaf.Fits]⟩, by decide⟩
  have ho : [((Slot.cell lo : Slot Digest), Leaf.entry .tomb), (.cell hi, .entry .tomb)].Pairwise
      (fun p q => SlotBefore env p.1 q.1) :=
    List.pairwise_pair.mpr (Or.inr ⟨rfl, lo_hi⟩)
  unfold Stream.decode
  rw [(trieOrder_iff hg).mpr ho]
  simp

/-- **Tooth (the routing mutation).** A trie that reads each id byte low bit first is not ordered by
the bytes: `bitLt_trieSpec_iff` is false for it, and its listing check admits `hi, lo`, the listing
the deployed codec refuses (`cells_refuses_bytes_descending`). -/
theorem lsbRouting_refuted :
    let S' : Trie.Spec (Slot Digest) Leaf Digest :=
      { trieSpec env with
        bit := fun s i => match i with
          | 0 => s.isNullifier
          | i + 1 => if h : i / 8 < (env.bytes s.id).size
              then ((env.bytes s.id)[i / 8]'h).toNat.testBit (i % 8) else false }
    let l : List (Slot Digest × Leaf) := [(.cell hi, .entry .tomb), (.cell lo, .entry .tomb)]
    (¬ ∀ s s' : Slot Digest, BitLt S' 0 s s' ↔ SlotBefore env s s') ∧
      (Trie.build S' S'.depth 0 l).toList = l ∧ leavesNodup (Trie.build S' S'.depth 0 l) = true := by
  intro S' l
  have hhl : BitLt S' 0 (.cell hi) (.cell lo) :=
    ⟨1, Nat.zero_le _, by decide, fun j _ hj => by
      have : j = 0 := by omega
      subst this; rfl, by decide, by decide⟩
  refine ⟨fun H => ?_, (build_listing_iff S' _ 0 l rfl ?_).mpr ?_⟩
  · have hlh : BitLt S' 0 (.cell lo) (.cell hi) := (H _ _).mpr (Or.inr ⟨rfl, lo_hi⟩)
    exact bitLt_asymm S' hlh hhl
  · intro p hp q hq hne
    simp only [l, List.mem_cons, List.not_mem_nil, or_false] at hp hq
    rcases hp with rfl | rfl <;> rcases hq with rfl | rfl
    · exact absurd rfl hne
    · exact ⟨1, Nat.zero_le _, by decide, by decide⟩
    · exact ⟨1, Nat.zero_le _, by decide, by decide⟩
    · exact absurd rfl hne
  · exact List.pairwise_pair.mpr hhl

/-! ## The journal (KERNEL-41) -/

/-- At the deployed digest, `JournalBefore` is `Digest`'s own order on the transaction ids. -/
theorem journalBefore_iff (p q : Digest × (Nat × Digest)) : JournalBefore env p q ↔ compare p.1 q.1 = .lt :=
  Iff.rfl

/-- **The deployed journal listing is accepted exactly when strictly ascending by transaction id.** -/
theorem journalOrder_iff {b : ByteArray} {i j : Nat} {l : List (Digest × (Nat × Digest))}
    (h : (rawList Bounds.journalMax (product digestCodec (product nat64 digestCodec))).get b i = .ok (l, j)) :
    (journalTrie env digestCodec).get b i = .ok (Trie.build (journalSpec env) (journalSpec env).depth 0 l, j) ↔
      l.Pairwise (fun p q => compare p.1 q.1 = .lt) := by
  constructor
  · intro hc
    by_cases ho : l.Pairwise (JournalBefore env)
    · exact ho
    · rw [journalTrie_get_refused Receive.deployed_lawful h ho] at hc; cases hc
  · exact journalTrie_get_ok Receive.deployed_lawful h

/-- **Any other deployed journal listing is refused `kernel/journal-order` by name.** -/
theorem journalOrder_refuses {b : ByteArray} {i j : Nat} {l : List (Digest × (Nat × Digest))}
    (h : (rawList Bounds.journalMax (product digestCodec (product nat64 digestCodec))).get b i = .ok (l, j))
    (ho : ¬ l.Pairwise (fun p q => compare p.1 q.1 = .lt)) :
    (journalTrie env digestCodec).get b i = .error (.rejected i "kernel/journal-order") :=
  journalTrie_get_refused Receive.deployed_lawful h ho

private theorem journalList_get (l : List (Digest × (Nat × Digest)))
    (hf : l.length ≤ Bounds.journalMax ∧ ∀ p ∈ l, True ∧ p.2.1 < 2 ^ 64 ∧ True) :
    (rawList Bounds.journalMax (product digestCodec (product nat64 digestCodec))).get
        ((rawList Bounds.journalMax (product digestCodec (product nat64 digestCodec))).bytes l) 0 =
      .ok (l, ((rawList Bounds.journalMax (product digestCodec (product nat64 digestCodec))).bytes l).size) := by
  simpa using (rawList_lawfulOn (product_lawfulOn digest_lawful.on (product_lawfulOn nat64_lawfulOn digest_lawful.on))
    Bounds.journalMax (by decide)).get_of_occurs l _ 0 hf (occursAt_self _)

/-- **Tooth.** Two journal entries listed with their transaction ids in descending byte order are refused
`kernel/journal-order` by name. -/
theorem journal_refuses_ids_descending :
    (journalTrie env digestCodec).decode
        ((rawList Bounds.journalMax (product digestCodec (product nat64 digestCodec))).bytes
          [(hi, (1, lo)), (lo, (2, lo))]) =
      .error (.rejected 0 "kernel/journal-order") := by
  have hg := journalList_get [(hi, (1, lo)), (lo, (2, lo))] ⟨by decide, by decide⟩
  have ho : ¬ [(hi, (1, lo)), (lo, (2, lo))].Pairwise
      (fun p q : Digest × (Nat × Digest) => compare p.1 q.1 = .lt) := by
    intro hp
    have : compare hi lo = .lt := (List.pairwise_cons.mp hp).1 _ (List.mem_singleton_self _)
    rw [hi_lo] at this; cases this
  unfold Stream.decode
  rw [journalOrder_refuses hg ho]

/-- The same two entries in ascending id order are read back. -/
theorem journal_reads_ids_ascending :
    (journalTrie env digestCodec).decode
        ((rawList Bounds.journalMax (product digestCodec (product nat64 digestCodec))).bytes
          [(lo, (2, lo)), (hi, (1, lo))]) =
      .ok (Trie.build (journalSpec env) (journalSpec env).depth 0 [(lo, (2, lo)), (hi, (1, lo))]) := by
  have hg := journalList_get [(lo, (2, lo)), (hi, (1, lo))] ⟨by decide, by decide⟩
  unfold Stream.decode
  rw [(journalOrder_iff hg).mpr (List.pairwise_pair.mpr lo_hi)]
  simp

/-! ## The refusals (KERNEL-44) -/

/-- **The deployed refusals listing is accepted exactly when strictly ascending by key bytes**
(`refusalKeyBytes`: kind byte, the 32 digest bytes, the window's eight bytes). -/
theorem refusalOrder_iff {b : ByteArray} {i j : Nat} {l : List (RefusalSlot Digest × RefusalLeaf)}
    (h : (rawList worldMax (product (refusalSlot digestCodec) refusalLeaf)).get b i = .ok (l, j)) :
    (refusalsTrie env digestCodec).get b i = .ok (Trie.build (refusalSpec env) (refusalSpec env).depth 0 l, j) ↔
      l.Pairwise (RefusalBefore env) := by
  constructor
  · intro hc
    by_cases ho : l.Pairwise (RefusalBefore env)
    · exact ho
    · rw [refusalsTrie_get_refused Receive.deployed_lawful h ho] at hc; cases hc
  · exact refusalsTrie_get_ok Receive.deployed_lawful h

/-- **Any other deployed refusals listing is refused `kernel/refusal-order` by name.** -/
theorem refusalOrder_refuses {b : ByteArray} {i j : Nat} {l : List (RefusalSlot Digest × RefusalLeaf)}
    (h : (rawList worldMax (product (refusalSlot digestCodec) refusalLeaf)).get b i = .ok (l, j))
    (ho : ¬ l.Pairwise (RefusalBefore env)) :
    (refusalsTrie env digestCodec).get b i = .error (.rejected i "kernel/refusal-order") :=
  refusalsTrie_get_refused Receive.deployed_lawful h ho

/-! ## The rows (KERNEL-46/48) -/

/-- The deployed digest codec writes the deployed `Env`'s bytes. -/
theorem digestCodec_bytes (d : Digest) : digestCodec.bytes d = env.bytes d := by
  show ByteArray.empty ++ d.bytes = d.bytes
  rw [ByteArray.empty_append]

/-- **The deployed rows key bytes are injective on keys within bounds** (`rowKeyBytes_inj`). -/
theorem rowKeyBytes_inj {s s' : RowSlot Digest} (hs : RowSlot.Fits (fun _ => True) s)
    (hs' : RowSlot.Fits (fun _ => True) s') (h : rowKeyBytes env s = rowKeyBytes env s') : s = s' :=
  Nanodregg.Codec.Kernel.rowKeyBytes_inj digestCodec_lawful.on digestCodec_bytes hs hs' h

/-- **The deployed rows listing is accepted exactly when strictly ascending by key bytes**
(`rowKeyBytes`: the parent's 32 bytes, the relation, the kind, a row's length byte and key). -/
theorem rowOrder_iff {b : ByteArray} {i j : Nat} {l : List (RowSlot Digest × RowLeaf)}
    (h : (rowsListing digestCodec).get b i = .ok (l, j)) :
    (rowsTrie env digestCodec).get b i = .ok (Trie.build (rowSpec env) (rowSpec env).depth 0 l, j) ↔
      l.Pairwise (RowBefore env) := by
  constructor
  · intro hc
    by_cases ho : l.Pairwise (RowBefore env)
    · exact ho
    · rw [rowsTrie_get_refused digestCodec_lawful.on Receive.deployed_lawful digestCodec_bytes h ho] at hc; cases hc
  · exact rowsTrie_get_ok digestCodec_lawful.on Receive.deployed_lawful digestCodec_bytes h

/-- **Any other deployed rows listing is refused `kernel/row-order` by name.** -/
theorem rowOrder_refuses {b : ByteArray} {i j : Nat} {l : List (RowSlot Digest × RowLeaf)}
    (h : (rowsListing digestCodec).get b i = .ok (l, j)) (ho : ¬ l.Pairwise (RowBefore env)) :
    (rowsTrie env digestCodec).get b i = .error (.rejected i "kernel/row-order") :=
  rowsTrie_get_refused digestCodec_lawful.on Receive.deployed_lawful digestCodec_bytes h ho

end Nanodregg.Codec.Deployed
