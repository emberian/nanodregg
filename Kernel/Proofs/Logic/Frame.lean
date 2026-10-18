/-
# Kernel.Proofs.Logic.Frame — the frame rule, stated once (KERNEL-51)

An admitted turn changes only its footprint. `CellFoot t` is what the turn may write in the cells'
trie: the cell of a non-`keep` touch, a born id, a spent nullifier. `RowFoot t` is what it may write
in the rows' trie: the slot of a non-`keep` row touch, the head of a row it writes (the head is a
shared counter, so it is inside), and the heads of a parent it retires (`dropHeads`).

`admit_Frame`: outside the footprints every slot reads as before, the journal and the refusals lose
only what the prune drops. (The height, the steps and the origin are `admit_height`, `admit_steps`,
`admit_origin`, below this module; they are not restated here.) Each field of
`Frame` carries only the premise its own trie's read needs, and the cells' field none, so a cell
reader applying the rule discharges nothing. `not_cellFoot_iff`: at a cell the footprint is
exactly the two hypotheses the hand-stated frames took. The teeth: without `born`, or without
`head`, the frame is false.
-/
import Kernel.Proofs.Rows

namespace Nanodregg.Kernel

variable {D : Type}

/-- The cells' footprint of a turn: the cell of a non-`keep` touch, a born id, a spent nullifier. -/
inductive CellFoot (t : Turn D) : Slot D → Prop
  | touched {x : Touch D} (hx : x ∈ t.touches) (hne : x.act ≠ .keep) : CellFoot t (.cell x.cell)
  | born {c : D} (hc : c ∈ createdIds t) : CellFoot t (.cell c)
  | spent {n : D} (hn : n ∈ t.nullifiers) : CellFoot t (.nullifier n)

/-- The rows' footprint of a turn: the slot of a non-`keep` row touch, the head of the relation a
non-`keep` row touch writes into, and every head of a parent the turn retires. -/
inductive RowFoot (t : Turn D) : RowSlot D → Prop
  | slot {x : RowTouch D} (hx : x ∈ t.rows) (hne : x.act ≠ .keep) : RowFoot t x.slot
  | head {x : RowTouch D} {key : RowKey D} (hx : x ∈ t.rows) (hne : x.act ≠ .keep) (hs : x.slot = .row key) :
      RowFoot t (.head key.parent key.rel)
  | dropped {x : Touch D} (hx : x ∈ t.touches) (hr : x.act = .retire) (rel : Nat) : RowFoot t (.head x.cell rel)

/-- **The footprint at a cell is the old hypotheses.** A cell is outside a turn's footprint exactly
when every touch of it is a `keep` and the turn does not bear it: the two premises `admit_frame`
always took, so the footprint is no larger than what the hand-stated frames assumed. -/
theorem not_cellFoot_iff {t : Turn D} {c : D} :
    ¬ CellFoot t (.cell c) ↔ (∀ x ∈ t.touches, x.cell = c → x.act = .keep) ∧ c ∉ createdIds t := by
  constructor
  · intro h
    refine ⟨fun x hx hxc => Decidable.byContradiction fun hne => h ?_, fun hb => h (.born hb)⟩
    rw [← hxc]; exact .touched hx hne
  · rintro ⟨hl, hb⟩ hf
    cases hf with
    | touched hx hne => exact hne (hl _ hx rfl)
    | born hc => exact hb hc

variable [Ord D] [DecidableEq D]

/-- **Frame.** What an admitted turn leaves alone, per trie, each field with only its own premise:
the cells outside `CellFoot` with none; the rows outside `RowFoot` on canonical rows; every other
journal entry, and every refusals leaf, as before up to the prune, on a canonical journal and
canonical refusals. -/
structure Frame (E : Env D) (w w' : World D) (t : Turn D) : Prop where
  cells : ∀ s, ¬ CellFoot t s → w'.trie.get (trieSpec E) s = w.trie.get (trieSpec E) s
  rows : w.RowsCanon E → ∀ s, ¬ RowFoot t s → rowAt E w'.rows s = rowAt E w.rows s
  journal : w.JournalCanon E → ∀ k, k ≠ t.txId →
    w'.journalAt E k = if (w.height + 1) % Bounds.windowMax = 0
      then (w.journalAt E k).filter (kept (w.height + 1)) else w.journalAt E k
  refusals : w.RefusalsCanon E → ∀ k,
    w'.refusalAt E k = if (w.height + 1) % Bounds.windowMax = 0
      then (w.refusalAt E k).filter (keptRefusal (w.height + 1) k) else w.refusalAt E k

/-- **The frame rule.** Every admitted turn frames its footprint. -/
theorem admit_Frame {E : Env D} {w w' : World D} {t : Turn D} (h : World.admit E w t = .ok w') :
    Frame E w w' t := by
  obtain ⟨posts, hk, rfl⟩ := admit_ok h
  refine ⟨fun s hs => ?_, fun hr s hs => ?_, fun hc k hne => ?_, fun hc k => ?_⟩
  · show (commitTrie E w t posts).get _ _ = _
    cases s with
    | cell c =>
        refine commitTrie_entry (fun hm => ?_) (fun hm => hs (.born ?_))
        · rw [List.map_map] at hm
          obtain ⟨p, hp, he⟩ := List.mem_map.mp hm
          obtain ⟨x, hx, hxc, hne⟩ := posts_touched hk p hp
          have hc : c = x.cell := he.symm.trans hxc
          subst hc
          exact hs (.touched hx hne)
        · simpa [bornEntries, createdIds, List.map_map, Function.comp_def] using hm
    | nullifier n => rw [commitTrie_nul, if_neg (fun hn => hs (.spent hn))]
  · have hrun := hk.rows
    unfold rowsRun at hrun
    simp only [except_bind_ok] at hrun
    obtain ⟨⟨⟩, -, ⟨⟩, -, hrun⟩ := hrun
    split at hrun
    · simp at hrun
    · rw [except_bind_ok] at hrun
      obtain ⟨acc, hf, he⟩ := hrun
      simp only [pure, Except.pure, Except.ok.injEq] at he
      show rowAt E (rowsAfter E w t).1 s = rowAt E w.rows s
      rw [← he]
      unfold rowAt
      rw [dropHeads_get_out t (fun x hx hr rel e => hs (by rw [e]; exact .dropped hx hr rel)) acc
          (foldRows_weight t.rows (w.rows, 0) acc hr hf).2,
        foldRows_get_out t.rows (w.rows, 0) acc hr hf
          (fun x hx hne => ⟨fun e => hs (by rw [e]; exact .slot hx hne),
            fun key hs' e => hs (by rw [e]; exact .head hx hne hs')⟩)]
  · rw [commit_journalAt hc, if_neg hne]
  · unfold World.refusalAt
    rw [commit_refusals]
    exact pruneRefusals_get hc k

/-! ## Teeth: a footprint smaller by one constructor makes the rule false -/

/-- The cell the teeth's turns bear or pin: an empty RAM cell. -/
private def toothCell : Cell := ⟨0, .ram, []⟩

/-- From genesis (height 0): bear `toothCell` at `c`, touch nothing, pay the exact weight. -/
private def bornTurn (c : D) : Turn D :=
  { txId := c, notBefore := 1, validUntil := 1, touches := [], creates := [(c, toothCell)],
    nullifiers := [], charge := 170, event := ByteArray.empty }

/-- **Tooth: `born` is in the cells' footprint.** From genesis a turn bearing one cell is admitted,
and the frame over the footprint without `born` (the cells of non-`keep` touches, and the
nullifiers) is false for it: the born slot reads empty before and the cell after. -/
theorem cellFoot_needs_born (E : Env D) (o c : D) :
    ∃ w w' t, World.admit E w t = .ok w' ∧
      ¬ ∀ s, (∀ x ∈ t.touches, x.act ≠ .keep → s ≠ .cell x.cell) → (∀ n ∈ t.nullifiers, s ≠ .nullifier n) →
        w'.trie.get (trieSpec E) s = w.trie.get (trieSpec E) s := by
  have hc : check E (World.genesis E o 170) (bornTurn c) = .ok [] := rfl
  refine ⟨_, _, bornTurn c, show World.admit E _ _ = .ok (commit E (World.genesis E o 170) (bornTurn c) []) by
    unfold World.admit; rw [hc], fun hall => ?_⟩
  have h := hall (.cell c) (fun x hx => by simp [bornTurn] at hx) (fun n hn => by simp [bornTurn] at hn)
  change (Trie.T.empty.insert (trieSpec E) (.cell c) (.entry (.live toothCell 0))).get (trieSpec E) (.cell c) =
    none at h
  rw [Trie.get_insert_self] at h
  cases h

/-- A World holding one live cell `p` with one declared relation `0` under it (no rows, limit 1). -/
private def rowWorld (E : Env D) (o p : D) : World D :=
  { World.genesis E o 250 with
    trie := (Trie.T.empty : Cells D).insert (trieSpec E) (.cell p) (.entry (.live toothCell 0))
    rows := (Trie.T.empty : Rows D).insert (rowSpec E) (.head p 0) (.head 0 0 1 0 0 false 0) }

/-- Pin `p` (`keep`) and insert one row into its relation `0`, paying the exact weight. -/
private def rowTurn (E : Env D) (o p : D) : Turn D :=
  { txId := o, notBefore := 1, validUntil := 1, touches := [⟨p, pinOf E (some (.live toothCell 0)), .keep⟩], creates := [],
    nullifiers := [], charge := 250, event := ByteArray.empty,
    rows := [⟨.row ⟨p, 0, ByteArray.empty⟩, none, .insert 0 ByteArray.empty⟩] }

/-- **Tooth: `head` is in the rows' footprint.** A turn inserting one row is admitted on canonical
rows, and the frame over the footprint without `head` (the non-`keep` row touches' slots, and the
heads of retired parents) is false for it: the relation's head counts the row. -/
theorem rowFoot_needs_head (E : Env D) (o p : D) :
    ∃ w w' t, World.admit E w t = .ok w' ∧ w.RowsCanon E ∧
      ¬ ∀ s, (∀ x ∈ t.rows, x.act ≠ .keep → s ≠ x.slot) →
          (∀ x ∈ t.touches, x.act = .retire → ∀ rel, s ≠ .head x.cell rel) →
        rowAt E w'.rows s = rowAt E w.rows s := by
  have hr : (rowWorld E o p).rows = (Trie.T.empty : Rows D).insert (rowSpec E) (.head p 0) (.head 0 0 1 0 0 false 0) :=
    rfl
  have hlive : (rowWorld E o p).live E p = some toothCell := by
    simp [rowWorld, World.live, World.entry, Trie.get_insert_self]
  have hentry : (rowWorld E o p).entry E p = some (.live toothCell 0) := by
    simp [rowWorld, World.entry, Trie.get_insert_self]
  have hmap : mapEx (touchCheck E (rowWorld E o p)) (rowTurn E o p).touches = .ok [none] := by
    simp [rowTurn, mapEx, touchCheck, hentry, req, Functor.map, Except.map]
  have hrun : rowsRun E (rowWorld E o p) (rowTurn E o p) =
      .ok (setHead E (((Trie.T.empty : Rows D).insert (rowSpec E) (.head p 0) (.head 0 0 1 0 0 false 0)).insert
        (rowSpec E) (.row ⟨p, 0, ByteArray.empty⟩) (.row 0 ByteArray.empty 0)) p 0 1 0 1 0 0 false 0, 0) := by
    simp [rowsRun, rowTurn, rowStepFreed, rowStep, hlive, req, headOf, headFloor, rowAt, hr, Trie.get_insert_self,
      Trie.get_insert_ne, Trie.get_empty, dropHeads, rowFreed, Bounds.rowsMax, Bounds.rangesMax, Bounds.keyBytesMax,
      bind, Except.bind, pure, Except.pure]
  have hc : check E (rowWorld E o p) (rowTurn E o p) = .ok [] := by
    unfold check checkWith; rw [hmap, hrun]; rfl
  refine ⟨_, _, rowTurn E o p, show World.admit E _ _ = .ok (commit E (rowWorld E o p) (rowTurn E o p) []) by
    unfold World.admit; rw [hc], by unfold World.RowsCanon; rw [hr]; exact Trie.canon_insert _ _ _ (Trie.canon_empty _ 0),
    fun hall => ?_⟩
  have h := hall (.head p 0) (fun x hx _ => by simp [rowTurn] at hx; subst hx; simp)
    (fun x hx => by simp [rowTurn] at hx; subst hx; simp)
  change rowAt E (rowsAfter E (rowWorld E o p) (rowTurn E o p)).1 (.head p 0) = rowAt E (rowWorld E o p).rows (.head p 0)
    at h
  rw [show rowsAfter E (rowWorld E o p) (rowTurn E o p) = _ by unfold rowsAfter; rw [hrun]] at h
  simp [rowAt, setHead, Trie.get_insert_self, hr] at h

end Nanodregg.Kernel
