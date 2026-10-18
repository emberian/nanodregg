import Codec.WorldSize
import Codec.Proofs.World
import Codec.Deployed
import Kernel.Proofs.Weight

/-!
# Codec.Proofs.WorldSize — a World's encoded size as a function of its weight (cv 01a150a3-2523)

KERNEL-55 bounds a reached World's storage weight by its genesis allowance
(`Kernel.allowance_bounds_world`); HOST's `worldBytesMax` bounds its ENCODED size. This module is the
bridge, at a 32-byte digest (the deployed one).

* `world_size_eq`, exact: the World's bytes plus 8 per live cell and per rows entry equal its weight,
  plus `worldFixed` (four list headers, three u64 counters, two digests), the journal's bytes
  (`journalBytes`, 72 per entry), the refusals' bytes (`refusalsBytes`), 3 per live cell and per
  tombstone (the slot's kind byte, the leaf's tag and the entry's tag, none of which the weight
  charges), 2 per spent nullifier (kind byte and leaf tag), and the version varints (`versionBytes`).
  `World.weight` charges each version (a live cell's counter, a head's floor, a row's version) at
  eight bytes (`counterWeight`); the wire writes it as a u64 varint of one to ten bytes (KERNEL-54).
  Every byte of the encoding is named by one term.
* `world_size_le`, the corollary HOST reads: on `World.CodecFits` (versions below `2^64`, so at most
  ten bytes each), `entrySlack.2 · size ≤ entrySlack.1 · weight + entrySlack.2 · (journalBytes +
  refusalsBytes + worldFixed)`, `entrySlack = (54, 49)`; `world_size_le_div` the floor-division form.
* The slack is ATTAINED: an empty live cell weighs 49 (32 id, 8 version charge, 9 cell) and writes 54
  at a ten-byte version (`world_size_slack_tight`: a one-cell World at version `2^63`, in
  `World.CodecFits`, meets the bound with equality, and every ratio below `54/49` fails for it). Every other entry kind is below 54/49: a
  tombstone 35/32, a spent nullifier 34/32, a head 86/84, a row at most `weight + 2` over `weight ≥ 56`.
* `refusalsBytes_le_of_fits`: on a listing `refusalsFits` admits, at most 82 bytes per refused
  transaction and 50 per count or total (KERNEL-55 R1), so HOST bounds `refusalsBytes` from KERNEL's
  counts alone.
-/

namespace Nanodregg.Codec.Kernel

open Nanodregg.Kernel Nanodregg.Codec.Stream

variable {D : Type} [Ord D]

/-! ## Entry by entry -/

private theorem foldl_add_size' {β : Type} (f : β → Nat) : ∀ (l : List β) (a : Nat),
    l.foldl (fun n x => n + f x) a = a + (l.map f).sum
  | [], a => by simp
  | x :: l, a => by rw [List.foldl_cons, foldl_add_size' f l, List.map_cons, List.sum_cons]; omega

private theorem map_const_sum {β : Type} (l : List β) (c : Nat) : (l.map fun _ => c).sum = c * l.length := by
  induction l with
  | nil => simp
  | cons x l ih => simp only [List.map_cons, List.sum_cons, List.length_cons, ih, Nat.mul_succ]; omega

private theorem rawList_size' {α : Type} (max : Nat) (c : Stream α) (l : List α) :
    (rawList max c).size l = 4 + (l.map c.size).sum := by
  show l.foldl (fun n x => n + c.size x) 4 = _
  exact foldl_add_size' _ l 4

omit [Ord D] in
/-- A cells listing entry: its bytes plus 8 at a live cell are its weight plus 3 (live or tomb) or 2
(spent) plus its version varint. -/
theorem cellItem_size {dc : Stream D} (hdc : ∀ d, dc.size d = 32) (p : Slot D × Leaf) :
    (product (slot dc) leaf).size p + 8 * cellItemLive p =
      p.2.weight + 3 * (cellItemLive p + cellItemTomb p) + 2 * cellItemSpent p + cellItemVersion p := by
  obtain ⟨s, l⟩ := p
  rcases l with (⟨c, v⟩ | _) | _ <;> cases s <;>
    simp [product, slot, leaf, leafWire, entry, entryWire, refine, choice, tagged, unit, hdc, cell_size,
      Leaf.weight, Entry.weight, digestWeight, counterWeight, cellItemLive, cellItemTomb, cellItemSpent,
      cellItemVersion] <;> omega

omit [Ord D] in
/-- A rows listing entry: its bytes plus 8 are its weight (`rowEntryWeight`) plus its varint. -/
theorem rowItem_size {dc : Stream D} (hdc : ∀ d, dc.size d = 32) (p : RowSlot D × RowLeaf) :
    (product (rowKey dc) rowLeaf).size p + 8 = rowEntryWeight p + rowItemVersion p := by
  obtain ⟨s, l⟩ := p
  have hk := rowKey_size hdc s
  cases l <;>
    simp [product, rowLeaf, rowLeafWire, rowLeafToWire, refine, choice, tagged, nat64, Stream.bool, u8,
      rawBytes, rowEntryWeight, RowLeaf.weight, counterWeight, headerWeight, rowItemVersion, hk] <;> omega

omit [Ord D] in
theorem journalItem_size {dc : Stream D} (hdc : ∀ d, dc.size d = 32) (p : D × (Nat × D)) :
    (product dc (product nat64 dc)).size p = 72 := by
  simp [product, nat64, hdc]

omit [Ord D] in
theorem refusalItem_size {dc : Stream D} (hdc : ∀ d, dc.size d = 32) (p : RefusalSlot D × RefusalLeaf D) :
    (product (refusalSlot dc) (refusalLeaf dc)).size p = refusalEntryBytes p := by
  obtain ⟨k, v⟩ := p
  cases k <;> cases v <;>
    simp [product, refusalSlot, refusalSlotWire, refusalLeaf, refusalLeafWire, refine, choice, tagged, nat64,
      u64, hdc, refusalEntryBytes]

/-! ## The exact size -/

omit [Ord D] in
private theorem cells_list_size {dc : Stream D} (hdc : ∀ d, dc.size d = 32) (l : List (Slot D × Leaf)) :
    (l.map (product (slot dc) leaf).size).sum + 8 * (l.map cellItemLive).sum =
      (l.map fun p => p.2.weight).sum + 3 * ((l.map cellItemLive).sum + (l.map cellItemTomb).sum) +
        2 * (l.map cellItemSpent).sum + (l.map cellItemVersion).sum := by
  induction l with
  | nil => simp
  | cons p l ih =>
    have := cellItem_size hdc p
    simp only [List.map_cons, List.sum_cons]
    omega

omit [Ord D] in
private theorem rows_list_size {dc : Stream D} (hdc : ∀ d, dc.size d = 32) (l : List (RowSlot D × RowLeaf)) :
    (l.map (product (rowKey dc) rowLeaf).size).sum + 8 * l.length =
      (l.map rowEntryWeight).sum + (l.map rowItemVersion).sum := by
  induction l with
  | nil => simp
  | cons p l ih =>
    have := rowItem_size hdc p
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    omega

/-- **A World's encoded size, exactly, against its weight** (cv 01a150a3-2523), at any 32-byte digest
codec: the bytes plus 8 per live cell and per rows entry (the version charge `World.weight` makes)
equal the weight, the fixed bytes, the journal's and the refusals' bytes, 3 per live cell and per
tombstone, 2 per spent nullifier, and the version varints. -/
theorem world_size_eq [DecidableEq D] (E : Env D) {dc : Stream D} (hdc : ∀ d, dc.size d = 32) (w : World D) :
    (world E dc).size w + 8 * (liveCount w + rowsCount w) =
      w.weight + worldFixed + journalBytes w + refusalsBytes w + 3 * (liveCount w + tombCount w) +
        2 * spentCount w + versionBytes w := by
  have hc := cells_list_size hdc w.trie.toList
  have hr := rows_list_size hdc w.rows.toList
  simp only [world, parentedWire, headedWire, rowsWire, countedWire, stepsWire, disjointWire, refusalsWire,
    journalWire, worldWire, toWire, cells, fitList, journalTrie, refusalsTrie, rowsTrie, rowsListing, refine,
    product, nat64, id, hdc, rawList_size'] at hc hr ⊢
  have hj : (w.journal.toList.map (fun _ => 32 + (8 + 32))).sum = 72 * w.journal.toList.length :=
    map_const_sum _ _
  have hf : (w.refusals.toList.map (fun v => (refusalSlot dc).size v.fst + (refusalLeaf dc).size v.snd)).sum =
      refusalsBytes w := by
    unfold refusalsBytes; congr 1; apply List.map_congr_left; intro p _; exact refusalItem_size hdc p
  simp only [World.weight, cellsWeight, rowsWeight, liveCount, tombCount, spentCount,
    rowsCount, versionBytes, worldFixed, journalBytes]
  omega

/-- The same, of the bytes: a lawful digest codec writes what `size` counts. -/
theorem world_bytes_size_eq [DecidableEq D] (E : Env D) {PD : D → Prop} {dc : Stream D} (hd : LawfulOn PD dc)
    (hdc : ∀ d, dc.size d = 32) (w : World D) :
    ((world E dc).bytes w).size + 8 * (liveCount w + rowsCount w) =
      w.weight + worldFixed + journalBytes w + refusalsBytes w + 3 * (liveCount w + tombCount w) +
        2 * spentCount w + versionBytes w := by
  rw [← (world_lawfulOn E hd).size_eq w]
  exact world_size_eq E hdc w

/-! ## The bound -/

omit [Ord D] in
theorem cellItem_slack {dc : Stream D} (hdc : ∀ d, dc.size d = 32) (p : Slot D × Leaf) (hp : Leaf.Fits p.2) :
    entrySlack.2 * (product (slot dc) leaf).size p ≤ entrySlack.1 * p.2.weight := by
  have h := cellItem_size hdc p
  obtain ⟨s, l⟩ := p
  rcases l with (⟨c, v⟩ | _) | _
  · have hv : varint64.size v ≤ 10 := by
      rw [varint64_size_eq]; exact varint64_size_le hp.2
    simp only [cellItemLive, cellItemTomb, cellItemSpent, cellItemVersion, Leaf.weight, Entry.weight,
      digestWeight, counterWeight, Cell.weight, entrySlack] at h hv ⊢
    omega
  · simp only [cellItemLive, cellItemTomb, cellItemSpent, cellItemVersion, Leaf.weight, Entry.weight,
      digestWeight, entrySlack] at h ⊢
    omega
  · simp only [cellItemLive, cellItemTomb, cellItemSpent, cellItemVersion, Leaf.weight, digestWeight,
      entrySlack] at h ⊢
    omega

omit [Ord D] in
theorem rowItem_slack {dc : Stream D} (hdc : ∀ d, dc.size d = 32) (p : RowSlot D × RowLeaf) (hp : RowLeaf.Fits p.2) :
    entrySlack.2 * (product (rowKey dc) rowLeaf).size p ≤ entrySlack.1 * rowEntryWeight p := by
  have h := rowItem_size hdc p
  obtain ⟨s, l⟩ := p
  have hs : 34 ≤ s.weight := by cases s <;> simp [RowSlot.weight, digestWeight] <;> omega
  cases l with
  | head c su li k wd r f =>
    have hv : varint64.size f ≤ 10 := by rw [varint64_size_eq]; exact varint64_size_le hp.2.2.2.2.2
    simp only [rowItemVersion, rowEntryWeight, RowLeaf.weight, counterWeight, entrySlack] at h hv ⊢
    omega
  | row a v u =>
    have hv : varint64.size u ≤ 10 := by rw [varint64_size_eq]; exact varint64_size_le hp.2.2
    simp only [rowItemVersion, rowEntryWeight, RowLeaf.weight, counterWeight, headerWeight, entrySlack] at h hv ⊢
    omega

omit [Ord D] in
private theorem slack_sum {α : Type} (f g : α → Nat) (P : α → Prop) (h : ∀ x, P x → entrySlack.2 * f x ≤ entrySlack.1 * g x) :
    ∀ l : List α, (∀ x ∈ l, P x) → entrySlack.2 * (l.map f).sum ≤ entrySlack.1 * (l.map g).sum
  | [], _ => by simp
  | x :: l, hl => by
    have h1 := h x (hl x (List.mem_cons_self ..))
    have h2 := slack_sum f g P h l (fun y hy => hl y (List.mem_cons_of_mem _ hy))
    simp only [List.map_cons, List.sum_cons, Nat.mul_add]
    omega

/-- **A fitting World's bytes are within `54/49` of its weight**, plus its journal's and refusals'
bytes and `worldFixed` (division-free; the form HOST's `reached_size_le` reads). -/
theorem world_size_le [DecidableEq D] {E : Env D} {PD : D → Prop} {dc : Stream D} (hd : LawfulOn PD dc)
    (hdc : ∀ d, dc.size d = 32) {w : World D} (hw : World.CodecFits E PD w) :
    entrySlack.2 * ((world E dc).bytes w).size ≤
      entrySlack.1 * w.weight + entrySlack.2 * (journalBytes w + refusalsBytes w + worldFixed) := by
  have hc := slack_sum _ _ (fun p : Slot D × Leaf => Leaf.Fits p.2) (cellItem_slack hdc) w.trie.toList
    (fun p hp => (hw.cells.1.1.2 p hp).2)
  have hr := slack_sum _ _ (fun p : RowSlot D × RowLeaf => RowLeaf.Fits p.2) (rowItem_slack hdc) w.rows.toList
    (fun p hp => (hw.rows.listing.1.2 p hp).2)
  rw [← (world_lawfulOn E hd).size_eq w]
  simp only [world, parentedWire, headedWire, rowsWire, countedWire, stepsWire, disjointWire, refusalsWire,
    journalWire, worldWire, toWire, cells, fitList, journalTrie, refusalsTrie, rowsTrie, rowsListing, refine,
    product, nat64, id, hdc, rawList_size'] at hc hr ⊢
  have hj : (w.journal.toList.map (fun _ => 32 + (8 + 32))).sum = 72 * w.journal.toList.length :=
    map_const_sum _ _
  have hf : (w.refusals.toList.map (fun v => (refusalSlot dc).size v.fst + (refusalLeaf dc).size v.snd)).sum =
      refusalsBytes w := by
    unfold refusalsBytes; congr 1; apply List.map_congr_left; intro p _; exact refusalItem_size hdc p
  simp only [World.weight, cellsWeight, rowsWeight, worldFixed, journalBytes, entrySlack] at hc hr ⊢
  omega

/-- The floor-division form: `size ≤ 54 · weight / 49 + journalBytes + refusalsBytes + worldFixed`. -/
theorem world_size_le_div [DecidableEq D] {E : Env D} {PD : D → Prop} {dc : Stream D} (hd : LawfulOn PD dc)
    (hdc : ∀ d, dc.size d = 32) {w : World D} (hw : World.CodecFits E PD w) :
    ((world E dc).bytes w).size ≤
      entrySlack.1 * w.weight / entrySlack.2 + journalBytes w + refusalsBytes w + worldFixed := by
  have h := world_size_le hd hdc hw
  have hq : ((world E dc).bytes w).size - (journalBytes w + refusalsBytes w + worldFixed) ≤
      entrySlack.1 * w.weight / entrySlack.2 :=
    (Nat.le_div_iff_mul_le (by decide)).mpr (by rw [Nat.mul_comm]; simp only [entrySlack] at h ⊢; omega)
  omega

/-! ## The refusals' bytes, from their counts -/

omit [Ord D] in
theorem refusalItemTx_sum_le : ∀ l : List (RefusalSlot D × RefusalLeaf D), (l.map refusalItemTx).sum ≤ l.length
  | [] => by simp
  | (k, v) :: l => by
    have := refusalItemTx_sum_le l
    cases k <;> simp only [List.map_cons, List.sum_cons, List.length_cons, refusalItemTx] <;> omega

/-- **On a listing `refusalsFits` admits, a refused transaction's entry is 82 bytes and every other
entry (a member's count, the World's total) 50**: `82 · tx + 50 · (length − tx)`. So `refusalsBytes`
is bounded by KERNEL's counts of the listing, which this module does not prove (KERNEL-55 R1's
refusals bound, `Kernel.refusals_bounded` and `Kernel.refusals_length_le`). -/
theorem refusalsBytes_eq_of_fits [DecidableEq D] {w : World D}
    (hf : refusalsFits w.height w.refusals.toList = true) :
    refusalsBytes w = 82 * (w.refusals.toList.map refusalItemTx).sum +
      50 * (w.refusals.toList.length - (w.refusals.toList.map refusalItemTx).sum) := by
  unfold refusalsBytes
  have hall := List.all_eq_true.mp hf
  generalize w.refusals.toList = l at hall ⊢
  induction l with
  | nil => simp
  | cons p l ih =>
    have hp := hall p (List.mem_cons_self ..)
    have ih := ih (fun q hq => hall q (List.mem_cons_of_mem _ hq))
    have hle := refusalItemTx_sum_le l
    obtain ⟨k, v⟩ := p
    cases k <;> cases v <;> simp_all [refusalFits, refusalEntryBytes, refusalItemTx] <;> omega

/-- The bound HOST discharges from KERNEL's counts: at most 82 bytes per entry, and 50 per entry that
is no refused transaction's. -/
theorem refusalsBytes_le_of_fits [DecidableEq D] {w : World D}
    (hf : refusalsFits w.height w.refusals.toList = true) :
    refusalsBytes w ≤ 82 * (w.refusals.toList.map refusalItemTx).sum +
      50 * (w.refusals.toList.length - (w.refusals.toList.map refusalItemTx).sum) :=
  Nat.le_of_eq (refusalsBytes_eq_of_fits hf)

/-! ## The slack is attained (the tooth) -/

private theorem varint64_size_2p63 : varint64.size (2 ^ 63) = 10 := by
  rw [varint64_size_eq]
  exact Nat.le_antisymm (varint_size_le _ 9 (by decide)) (varint_size_ge _ 9 (by decide))

private theorem slackWorld_trie (E : Env D) (d : D) : (slackWorld E d).trie.toList = [slackItem d] := by
  cases hd : (trieSpec E).depth <;> simp [slackWorld, Trie.build, Trie.mkLeaf, Trie.T.toList, hd]

private theorem slackWorld_rows (E : Env D) (d : D) : (slackWorld E d).rows.toList = [] := by
  simp [slackWorld, Trie.T.toList]

private theorem slackWorld_journal (E : Env D) (d : D) : (slackWorld E d).journal.toList = [] := by
  simp [slackWorld, Trie.T.toList]

private theorem slackWorld_refusals (E : Env D) (d : D) : (slackWorld E d).refusals.toList = [] := by
  simp [slackWorld, Trie.T.toList]

theorem slackWorld_weight [DecidableEq D] (E : Env D) (d : D) : (slackWorld E d).weight = 49 := by
  rw [World.weight, cellsWeight, rowsWeight, slackWorld_trie, slackWorld_rows]
  simp [slackItem, Leaf.weight, Entry.weight, Cell.weight, Slots.weight, digestWeight, counterWeight]

theorem slackWorld_size [DecidableEq D] (E : Env D) {dc : Stream D} (hdc : ∀ d, dc.size d = 32) (d : D) :
    (world E dc).size (slackWorld E d) = 158 := by
  have h := world_size_eq E hdc (slackWorld E d)
  have v := varint64_size_2p63
  rw [slackWorld_weight] at h
  simp only [liveCount, tombCount, spentCount, rowsCount, versionBytes, journalBytes, refusalsBytes,
    slackWorld_trie, slackWorld_rows, slackWorld_journal, slackWorld_refusals, slackItem, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, List.length_nil, cellItemLive, cellItemTomb, cellItemSpent,
    cellItemVersion, worldFixed, v] at h
  omega

theorem slackWorld_rest (E : Env D) (d : D) :
    journalBytes (slackWorld E d) + refusalsBytes (slackWorld E d) = 0 := by
  simp [journalBytes, refusalsBytes, slackWorld_journal, slackWorld_refusals]

/-- `slackWorld` is in the World codec's domain (`World.CodecFits`, every digest admitted): a canonical
one-leaf cells trie, an empty journal, refusals and rows, height and steps 0. -/
theorem slackWorld_codecFits [DecidableEq D] (E : Env D) (d : D) :
    World.CodecFits E (fun _ => True) (slackWorld E d) where
  cells := ⟨⟨⟨by rw [slackWorld_trie]; simp [worldMax], fun p hp => by
      rw [slackWorld_trie] at hp; simp only [List.mem_singleton] at hp; subst hp
      exact ⟨trivial, by simp [slackItem, Leaf.Fits, Entry.Fits, Cell.Fits, Slots.Fits]⟩⟩,
    fun p hp => by rw [slackWorld_trie] at hp; simp only [List.mem_singleton] at hp; subst hp; rfl⟩,
    by simpa using Trie.canon_build (trieSpec E) 0 [slackItem d] (by simp)⟩
  journal := ⟨⟨by simp [slackWorld, Trie.T.toList, Bounds.journalMax], by simp [slackWorld, Trie.T.toList]⟩,
    Trie.canon_empty _ 0⟩
  refusals := ⟨⟨by simp [slackWorld, Trie.T.toList, worldMax], by simp [slackWorld, Trie.T.toList]⟩, Trie.canon_empty _ 0⟩
  height := by simp [slackWorld]
  stepsLt := by simp [slackWorld]
  chain := trivial
  budget := by rw [slackWorld_weight]; simp [slackWorld]
  origin := trivial
  journalFits := by simp [journalFits, slackWorld, Trie.T.toList, ascendingNat]
  refusalsFits := by simp [refusalsFits, slackWorld, Trie.T.toList]
  refusalsDisjoint := by simp [refusalsDisjoint, slackWorld, Trie.T.toList]
  steps := by simp [slackWorld]
  refusalsCounted := by simp [refusalsCounted, refusalTally, slackWorld, Trie.T.toList]
  rows := ⟨⟨⟨by simp [slackWorld, Trie.T.toList, worldMax], by simp [slackWorld, Trie.T.toList]⟩, Trie.canon_empty _ 0⟩,
    by simp [rowsFits, ascendingBytes, slackWorld, Trie.T.toList], by simp [rowsHeaded, slackWorld, Trie.T.toList],
    by simp [rowsParented, slackWorld, Trie.T.toList]⟩

/-- **Tooth: the slack `54/49` is attained, so no smaller ratio bounds the codec's domain.** At any
32-byte digest codec, the one-cell World `slackWorld` is in `world_size_le`'s premise
(`World.CodecFits`), meets its bound with EQUALITY (`49 · 158 = 54 · 49 + 49 · 104`), and for EVERY
ratio `a / b` below `54 / 49` the same bound at `(a, b)` is false for it. -/
theorem world_size_slack_tight [DecidableEq D] (E : Env D) {dc : Stream D} (hdc : ∀ d, dc.size d = 32) (d : D) :
    World.CodecFits E (fun _ => True) (slackWorld E d) ∧
    entrySlack.2 * (world E dc).size (slackWorld E d) =
        entrySlack.1 * (slackWorld E d).weight + entrySlack.2 * (journalBytes (slackWorld E d) +
          refusalsBytes (slackWorld E d) + worldFixed) ∧
      ∀ a b : Nat, a * entrySlack.2 < entrySlack.1 * b →
        ¬ (b * (world E dc).size (slackWorld E d) ≤
          a * (slackWorld E d).weight + b * (journalBytes (slackWorld E d) +
            refusalsBytes (slackWorld E d) + worldFixed)) := by
  have hs := slackWorld_size E hdc d
  have hw := slackWorld_weight E d
  have hr := slackWorld_rest E d
  refine ⟨slackWorld_codecFits E d, ?_, ?_⟩
  · rw [hs, hw, hr]; simp [entrySlack, worldFixed]
  · intro a b hab
    rw [hs, hw, hr]
    simp only [entrySlack, worldFixed] at hab ⊢
    omega

end Nanodregg.Codec.Kernel

namespace Nanodregg.Codec.Deployed

open Nanodregg.Kernel Nanodregg.Codec.Kernel Nanodregg.Codec.Stream

/-- `world_size_le` at the deployed digest codec (32 bytes, lawful): the form HOST's `reached_size_le` reads. -/
theorem world_size_le_deployed {w : World Digest} (hw : World.CodecFits env (fun _ => True) w) :
    entrySlack.2 * ((Codec.Kernel.world env digestCodec).bytes w).size ≤
      entrySlack.1 * w.weight + entrySlack.2 * (journalBytes w + refusalsBytes w + worldFixed) :=
  Codec.Kernel.world_size_le Stream.digest_lawful.on (fun _ => rfl) hw

/-- The tooth at the deployed codec: the 32-byte premise of `world_size_slack_tight` is met, so the
slack `54/49` is attained by a deployed World in the codec's domain. -/
theorem world_size_slack_tight_deployed (d : Digest) :
    World.CodecFits env (fun _ => True) (slackWorld env d) ∧
    entrySlack.2 * (Codec.Kernel.world env digestCodec).size (slackWorld env d) =
        entrySlack.1 * (slackWorld env d).weight + entrySlack.2 * (journalBytes (slackWorld env d) +
          refusalsBytes (slackWorld env d) + worldFixed) ∧
      ∀ a b : Nat, a * entrySlack.2 < entrySlack.1 * b →
        ¬ (b * (Codec.Kernel.world env digestCodec).size (slackWorld env d) ≤
          a * (slackWorld env d).weight + b * (journalBytes (slackWorld env d) +
            refusalsBytes (slackWorld env d) + worldFixed)) :=
  world_size_slack_tight env (fun _ => rfl) d

end Nanodregg.Codec.Deployed
