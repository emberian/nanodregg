import Codec.Proofs.TrieOrderDeployed
import Kernel.Proofs.RowsHead
import Kernel.Sim

/-!
# A reached World's rows are in the codec's domain (HOST-12's export completeness, CODEC-34)

`rowsCodecFits_of_ok`: a World whose rows trie is canonical (`World.RowsCanon`), whose rows hold
KERNEL's reached-World invariant (`World.RowsOk`: every entry fits, every head counts its rows, every
head's parent is a live cell) and whose listing is within the wire's bound, has rows the World codec
writes and reads back (`RowsCodecFits`). The only field not handed over by `RowsOk` is the listing's
order, and it comes from canonicity:

* a canonical trie lists its keys in bit order (`build_listing_iff` at `Trie.build_toList`);
* bit order is key-byte `compare` order on keys within bounds (`bitLt_rowSpec_iff`);
* `compare` on the bytes' arrays is `<` on their lists (`toList_lt_of_compare_lt`), which is what
  `rowsFits`' `ascendingBytes` decides.

`hlen` is the caller's: `RowsOk` bounds rows per relation, not the listing (the parents are not
statically bounded; `rowsTrie` names `worldMax` as the wire's map bound). The premises meet at genesis
(`Deployed.genesis_rowsCodecFits`), and every World the deployed fold reaches from genesis discharges
them (`Deployed.fold_rowsCodecFits`, through KERNEL's `deployed_fold_rowsOk`).

The tooth `rowsCodecFits_needs_order`: two heads every per-entry and per-relation check accepts, listed
in the wrong order (a non-canonical leaf), fit no `RowsCodecFits` whatever the cells; listed in order
they pass `rowsFits`.
-/

namespace Nanodregg.Codec.Kernel

open Nanodregg.Kernel Nanodregg.Codec.Stream

/-! ## Bytes: `compare` on the array is `<` on the list -/

private theorem toList_loop (d : Array UInt8) : ∀ (n i : Nat) (r : List UInt8), d.size - i = n →
    ByteArray.toList.loop ⟨d⟩ i r = r.reverse ++ d.toList.drop i
  | 0, i, r, h => by
    have hs : (⟨d⟩ : ByteArray).size = d.size := rfl
    rw [ByteArray.toList.loop, if_neg (by omega)]
    rw [List.drop_eq_nil_of_le (by rw [Array.length_toList]; omega), List.append_nil]
  | n + 1, i, r, h => by
    have hs : (⟨d⟩ : ByteArray).size = d.size := rfl
    have hi : i < d.size := by omega
    rw [ByteArray.toList.loop, if_pos (by omega), toList_loop d n (i + 1) _ (by omega)]
    have hl : i < d.toList.length := by rw [Array.length_toList]; exact hi
    have e : d.toList.drop i = d.toList[i] :: d.toList.drop (i + 1) := List.drop_eq_getElem_cons hl
    rw [e]
    have hg : (⟨d⟩ : ByteArray).get! i = d.toList[i]'hl := by
      show d[i]! = _
      rw [getElem!_pos d i hi, Array.getElem_toList]
    rw [hg, List.reverse_cons, List.append_assoc, List.singleton_append]

/-- `ByteArray.toList` is the list of the underlying array. -/
theorem byteArray_toList_eq (a : ByteArray) : a.toList = a.data.toList := by
  obtain ⟨d⟩ := a
  rw [ByteArray.toList, toList_loop d _ 0 [] rfl, List.reverse_nil, List.nil_append, List.drop_zero]

private theorem lt_of_compareLex_lt : ∀ (xs ys : List UInt8), List.compareLex compare xs ys = .lt → xs < ys
  | [], [], h => by simp [List.compareLex_nil_nil] at h
  | [], _ :: _, _ => List.Lex.nil
  | _ :: _, [], h => by simp [List.compareLex_cons_nil] at h
  | x :: xs, y :: ys, h => by
    rw [List.compareLex_cons_cons] at h
    cases hc : compare x y with
    | lt => exact List.Lex.rel (compareOfLessAndEq_eq_lt.mp hc)
    | eq =>
      rw [hc, Ordering.eq_then] at h
      have hxy : x = y := Std.LawfulEqCmp.eq_of_compare hc
      subst hxy
      exact List.Lex.cons (lt_of_compareLex_lt xs ys h)
    | gt => rw [hc] at h; cases h

/-- **`compare` on two byte strings' arrays is `<` on their lists** (the bridge from the trie's
key-byte order to `ascendingBytes`). -/
theorem toList_lt_of_compare_lt {a b : ByteArray} (h : compare a.data b.data = .lt) : a.toList < b.toList := by
  rw [byteArray_toList_eq, byteArray_toList_eq]
  rw [Array.compare_eq_compare_toList, List.compare_eq_compareLex] at h
  exact lt_of_compareLex_lt _ _ h

/-- A list pairwise below in `compare` is `ascendingBytes`. -/
theorem ascendingBytes_of_pairwise :
    ∀ {l : List ByteArray}, l.Pairwise (fun a b => compare a.data b.data = .lt) → ascendingBytes l = true
  | [], _ => rfl
  | [_], _ => rfl
  | a :: b :: rest, h => by
    simp only [ascendingBytes, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨toList_lt_of_compare_lt ((List.pairwise_cons.mp h).1 b (by simp)),
      ascendingBytes_of_pairwise (List.pairwise_cons.mp h).2⟩

/-! ## The reached World's rows -/

variable {D : Type} [Ord D] [DecidableEq D]

omit [Ord D] [DecidableEq D] in
/-- An entry `rowFits` admits has its key in the key codec's domain. -/
theorem rowSlot_fits_of_rowFits {s : RowSlot D} {v : RowLeaf} (h : rowFits s v = true) :
    RowSlot.Fits (fun _ => True) s := by
  cases s <;> cases v <;> simp_all [RowSlot.Fits, rowFits]

/-- **A reached World's rows are in the codec's domain.** Over a lawful `Env` and a digest codec
writing its bytes: canonical rows holding `RowsOk`, at most `worldMax` of them, are `RowsCodecFits`
(the listing ascending by key bytes comes from canonicity; every other field from `RowsOk`). -/
theorem rowsCodecFits_of_ok {dc : Stream D} (hd : Stream.Lawful dc) {E : Env D} {n : Nat} (hE : E.Lawful n)
    (hb : ∀ d, dc.bytes d = E.bytes d) {w : World D} (hc : w.RowsCanon E) (hok : w.RowsOk E)
    (hlen : w.rows.toList.length ≤ worldMax) : RowsCodecFits E (fun _ => True) w.trie w.rows := by
  obtain ⟨hfit, hhead, hpar⟩ := hok
  have hslot : ∀ p ∈ w.rows.toList, RowSlot.Fits (fun _ => True) p.1 := fun p hp =>
    rowSlot_fits_of_rowFits (hfit p hp)
  have hbuild := Trie.build_toList (rowSpec E) 0 w.rows hc
  have hbit : w.rows.toList.Pairwise (fun p q => BitLt (rowSpec E) 0 p.1 q.1) :=
    (build_listing_iff (rowSpec E) _ 0 _ rfl (rows_sepAt hE fun p hp => rowSlotFits_of_rowFits (hfit p hp))).mp
      ⟨by rw [hbuild], by rw [hbuild]; exact leavesNodup_of_routed (rowSpec E) 0 w.rows hc.1⟩
  have hord : (w.rows.toList.map fun p => rowKeyBytes E p.1).Pairwise
      (fun a b => compare a.data b.data = .lt) := by
    rw [List.pairwise_map]
    exact hbit.imp_of_mem fun hp hq h => (bitLt_rowSpec_iff hd.on hE hb (hslot _ hp) (hslot _ hq)).mp h
  have hfits : rowsFits E w.rows.toList = true := by
    simp only [rowsFits, Bool.and_eq_true, List.all_eq_true]
    exact ⟨ascendingBytes_of_pairwise hord, hfit⟩
  exact ⟨⟨⟨hlen, fun p hp => ⟨hslot p hp, rowLeaf_fits_of_rowsFits hfits p hp⟩⟩, hc⟩, hfits, hhead, hpar⟩

/-! ## The tooth: without the order canonicity gives, the checks `RowsOk` names are not enough -/

/-- Two heads of one parent (relations 0 and 1), each declared empty: in key-byte order. -/
private abbrev headsInOrder : List (RowSlot Sim.D × RowLeaf) :=
  [(.head 0 0, .head 0 0 0 0 0 false 0), (.head 0 1, .head 0 0 0 0 0 false 0)]

/-- The same two heads swapped, as one leaf: not the canonical trie of its entries. -/
private abbrev headsSwapped : Rows Sim.D := .leaf 0 headsInOrder.reverse

/-- **Tooth: the order is what canonicity adds.** The two heads swapped, as a (non-canonical) leaf,
pass every per-entry check (`rowFits`) and the per-relation one (`rowsHeaded`), are within the wire's
bound, and still fit no `RowsCodecFits` over any cells: `rowsFits` refuses their order. In order they
pass `rowsFits`, so the swap is the whole difference. The swapped leaf is not `Trie.Canon` (by
`rowsCodecFits_of_ok`, contraposed: it is the canonicity premise the order is drawn from). -/
theorem rowsCodecFits_needs_order :
    rowsFits Sim.env headsInOrder = true ∧
    (∀ p ∈ headsSwapped.toList, rowFits p.1 p.2 = true) ∧ rowsHeaded headsSwapped.toList = true ∧
      headsSwapped.toList.length ≤ worldMax ∧
      ∀ (PD : Sim.D → Prop) (t : Cells Sim.D), ¬ RowsCodecFits Sim.env PD t headsSwapped := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, fun PD t h => ?_⟩
  have hf := h.fits
  revert hf
  decide +kernel

end Nanodregg.Codec.Kernel

namespace Nanodregg.Codec.Deployed

open Nanodregg.Kernel Nanodregg.Codec.Stream Nanodregg.Codec.Kernel

/-- **A reached deployed World's rows are in the codec's domain** (`Codec.Kernel.rowsCodecFits_of_ok`
at `Receive.deployed_lawful` and `digestCodec_bytes`). -/
theorem rowsCodecFits_of_ok {w : World Digest} (hc : w.RowsCanon env) (hok : w.RowsOk env)
    (hlen : w.rows.toList.length ≤ worldMax) : RowsCodecFits env (fun _ => True) w.trie w.rows :=
  Nanodregg.Codec.Kernel.rowsCodecFits_of_ok digestCodec_lawful Receive.deployed_lawful digestCodec_bytes hc hok hlen

/-- **The premises meet at genesis** (`genesis_rowsCanon`, `genesis_rowsOk`): a deployed genesis World's
rows are in the codec's domain through `rowsCodecFits_of_ok`, not around it. -/
theorem genesis_rowsCodecFits (o : Digest) (a : Nat) :
    RowsCodecFits env (fun _ => True) (World.genesis env o a).trie (World.genesis env o a).rows :=
  rowsCodecFits_of_ok (genesis_rowsCanon env o a) (genesis_rowsOk env o a)
    (by simp [World.genesis, Trie.T.toList])

/-- **Every World the deployed fold reaches from genesis has its rows in the codec's domain**, given the
listing within the wire's bound: `RowsCanon` and `RowsOk` are discharged by KERNEL's
`deployed_fold_rowsOk` (`fold_rowsCanon`, `fold_rowsOk`), so only `hlen` is the caller's. -/
theorem fold_rowsCodecFits {o : Digest} {a : Nat} {l : List (Step Digest)} {w : World Digest}
    (h : World.fold env (World.genesis env o a) l = .ok w) (hlen : w.rows.toList.length ≤ worldMax) :
    RowsCodecFits env (fun _ => True) w.trie w.rows :=
  let ⟨hc, hok⟩ := deployed_fold_rowsOk h
  rowsCodecFits_of_ok hc hok hlen

end Nanodregg.Codec.Deployed
