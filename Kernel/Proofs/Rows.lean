/-
# Kernel.Proofs.Rows — what an admitted turn does to the rows (KERNEL-46/48)

* `rowsRun_weight`: the rows move by exactly the row touches' growth less what they give back
  (`rowFreed`), so `World.weight` (cells and rows) is conserved by `Kernel.Proofs.Weight`;
* `rowsRun_canon`, `admit_rowsCanon`, `fold_rowsCanon`: the rows trie stays canonical.
-/
import Kernel.Proofs.Refuse
import Kernel.Proofs.TrieMap
import Kernel.Receive.Follow

namespace Nanodregg.Kernel

variable {D : Type} [Ord D] [DecidableEq D]

-- `rowPath` is `List.range Bounds.rowDepth` mapped: whnf of a statement about it would build the
-- 1304-element list, so it is unfolded only where a proof asks (`under_rowPath`)
attribute [local irreducible] rowPath

/-- The rows trie is canonical: what every rows theorem rests on, as `World.Canon` for the cells. -/
def World.RowsCanon (E : Env D) (w : World D) : Prop := Trie.Canon (rowSpec E) 0 w.rows

/-! ## A key lies under its own path -/

omit [Ord D] [DecidableEq D] in
theorem under_range {K V : Type} (S : Trie.Spec K V D) (k : K) (n : Nat) :
    Trie.Under S 0 ((List.range n).map (S.bit k)) k := by
  intro i _ b hb
  rw [List.getElem?_map] at hb
  rcases h : (List.range n)[i]? with _ | j
  · simp [h] at hb
  · obtain ⟨hlt, hj⟩ := List.getElem?_eq_some_iff.mp h
    rw [List.getElem_range] at hj
    subst hj
    simpa [h] using hb

omit [Ord D] [DecidableEq D] in
theorem under_rowPath (E : Env D) (s : RowSlot D) : Trie.Under (rowSpec E) 0 (rowPath E s) s := by
  unfold rowPath; exact under_range (rowSpec E) s _

/-! ## The rows' weight under one write -/

omit [Ord D] in
theorem rowsWeight_insert_some {E : Env D} {r : Rows D} (hr : Trie.Routed (rowSpec E) 0 r)
    {k : RowSlot D} {old : RowLeaf} (v : RowLeaf) (h : r.get (rowSpec E) k = some old) :
    rowsWeight (r.insert (rowSpec E) k v) + rowEntryWeight (k, old) = rowsWeight r + rowEntryWeight (k, v) :=
  Trie.sumN_insert_some (rowSpec E) rowEntryWeight hr v h

omit [Ord D] in
theorem rowsWeight_insert_none {E : Env D} {r : Rows D} (hr : Trie.Routed (rowSpec E) 0 r)
    {k : RowSlot D} (v : RowLeaf) (h : r.get (rowSpec E) k = none) :
    rowsWeight (r.insert (rowSpec E) k v) = rowsWeight r + rowEntryWeight (k, v) :=
  Trie.sumN_insert_none (rowSpec E) rowEntryWeight hr v h

omit [Ord D] in
/-- The retract's erase: every entry but `k`'s, so the weight drops by exactly `k`'s entry. -/
theorem rowsWeight_retain {E : Env D} {r : Rows D} (hr : Trie.Canon (rowSpec E) 0 r)
    {k : RowSlot D} {old : RowLeaf} (h : r.get (rowSpec E) k = some old) (P : List Bool)
    (hu : Trie.Under (rowSpec E) 0 P k) :
    rowsWeight (Trie.retainAt (rowSpec E) (fun k' _ => decide (k' ≠ k)) P r) +
      rowEntryWeight (k, old) = rowsWeight r ∧
    Trie.Canon (rowSpec E) 0 (Trie.retainAt (rowSpec E) (fun k' _ => decide (k' ≠ k)) P r) ∧
    ∀ k', (Trie.retainAt (rowSpec E) (fun k' _ => decide (k' ≠ k)) P r).get (rowSpec E) k' =
      if k' = k then none else r.get (rowSpec E) k' := by
  have hq : ∀ p ∈ r.toList, decide (p.1 ≠ k) = false → Trie.Under (rowSpec E) 0 P p.1 := by
    rintro ⟨pk, pv⟩ _ hf
    have : pk = k := Classical.not_not.mp (of_decide_eq_false hf)
    subst this
    exact hu
  refine ⟨?_, Trie.canon_retainAt (rowSpec E) (fun k' _ => decide (k' ≠ k)) P 0 r hr hq,
    fun k' => ?_⟩
  · unfold rowsWeight
    rw [Trie.toList_retainAt (rowSpec E) (fun k' _ => decide (k' ≠ k)) P 0 r hr.1 hq,
      Trie.sumN_split rowEntryWeight r.toList (Trie.toList_nodup (rowSpec E) 0 r hr.1)
        ((Trie.mem_toList (rowSpec E) 0 r hr.1 k old).mpr h)]
    omega
  · rw [Trie.get_retainAt (rowSpec E) (fun k' _ => decide (k' ≠ k)) P hr hq k']
    by_cases hk : k' = k
    · subst hk; simp
    · simp only [hk, if_false, ne_eq, not_false_eq_true]
      cases Trie.T.get (rowSpec E) r k' <;> rfl

omit [Ord D] in
/-- Writing a head over a head: the weight is unchanged (a head's size does not depend on its
counters). -/
theorem rowsWeight_setHead {E : Env D} {r : Rows D} (hr : Trie.Routed (rowSpec E) 0 r) {p : D} {rel : Nat}
    {c s l cap wd : Nat} {rt : Bool} {c' s' : Nat}
    (h : r.get (rowSpec E) (.head p rel) = some (.head c s l cap wd rt)) :
    rowsWeight (setHead E r p rel c' s' l cap wd rt) = rowsWeight r := by
  have := rowsWeight_insert_some hr (.head c' s' l cap wd rt) h
  simp only [rowEntryWeight, RowLeaf.weight] at this
  unfold setHead
  change rowsWeight (r.insert (rowSpec E) (.head p rel) (.head c' s' l cap wd rt)) = rowsWeight r
  omega

omit [Ord D] in
theorem headOf_some {E : Env D} {r : Rows D} {p : D} {rel : Nat} {c s l cap wd : Nat} {rt : Bool}
    (h : headOf E r p rel = some (c, s, l, cap, wd, rt)) :
    r.get (rowSpec E) (.head p rel) = some (.head c s l cap wd rt) := by
  unfold headOf rowAt at h
  split at h
  · rename_i hg; simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := h; exact hg
  · simp at h

/-! ## One row touch -/

omit [Ord D] [DecidableEq D] in
theorem head_ne_row {p : D} {rel : Nat} {key : RowKey D} : (RowSlot.head p rel : RowSlot D) ≠ .row key :=
  fun h => by cases h

/-- **One row touch moves the rows' weight exactly**: by its growth, less what it gives back; and
the rows stay canonical. -/
theorem rowStep_weight {E : Env D} {w : World D} {t : Turn D} {r r' : Rows D} {x : RowTouch D}
    (hr : Trie.Canon (rowSpec E) 0 r) (h : rowStep E w t r x = .ok r') :
    rowsWeight r' + rowFreed E r x = rowsWeight r + x.growth ∧ Trie.Canon (rowSpec E) 0 r' := by
  obtain ⟨slot, seen, act⟩ := x
  cases slot with
  | head p rel =>
      cases act with
      | declare limit cap width retract =>
          unfold rowStep at h
          simp only [except_bind_ok] at h
          obtain ⟨⟨⟩, -, ⟨⟩, -, ⟨⟩, -, ⟨⟩, -, ⟨⟩, hn, hw⟩ := h
          simp only [pure, Except.pure, Except.ok.injEq] at hw
          subst hw
          have hn : r.get (rowSpec E) (.head p rel) = none := by
            have := req_ok.mp hn; unfold rowAt at this; simpa [Option.isNone_iff_eq_none] using this
          refine ⟨?_, Trie.canon_insert (rowSpec E) _ _ hr⟩
          unfold setHead
          change rowsWeight (r.insert (rowSpec E) _ _) + _ = _
          rw [rowsWeight_insert_none hr.1 _ hn]
          simp only [rowFreed, RowTouch.growth, rowEntryWeight, Nat.add_zero]
      | keep => simp [rowStep] at h
      | insert _ _ => simp [rowStep] at h
      | upsert _ _ => simp [rowStep] at h
      | retract => simp [rowStep] at h
  | row key =>
      unfold rowStep at h
      simp only [except_bind_ok] at h
      obtain ⟨⟨⟩, -, ⟨⟩, -, ⟨⟩, -, h⟩ := h
      split at h
      · simp at h
      · rename_i count sum limit cap width retract hhead
        have hg := headOf_some hhead
        simp only [except_bind_ok] at h
        obtain ⟨⟨⟩, -, h⟩ := h
        cases act with
        | keep =>
            simp only [except_bind_ok] at h
            obtain ⟨⟨⟩, -, h⟩ := h
            simp only [pure, Except.pure, Except.ok.injEq] at h
            subst h
            exact ⟨by simp only [rowFreed, RowTouch.growth, Nat.add_zero], hr⟩
        | insert amt v =>
            simp only [except_bind_ok] at h
            obtain ⟨⟨⟩, -, ⟨⟩, hn, ⟨⟩, -, ⟨⟩, -, ⟨⟩, -, h⟩ := h
            simp only [pure, Except.pure, Except.ok.injEq] at h
            subst h
            have hn : r.get (rowSpec E) (.row key) = none := by
              have := req_ok.mp hn; unfold rowAt at this; simpa [Option.isNone_iff_eq_none] using this
            have hr1 := Trie.canon_insert (rowSpec E) (.row key) (.row amt v) hr
            have hg1 : (r.insert (rowSpec E) (.row key) (.row amt v)).get (rowSpec E) (.head key.parent key.rel) =
                some (.head count sum limit cap width retract) := by
              rw [Trie.get_insert_ne (rowSpec E) _ _ head_ne_row]; exact hg
            refine ⟨?_, Trie.canon_insert (rowSpec E) _ _ hr1⟩
            rw [rowsWeight_setHead hr1.1 hg1]
            change rowsWeight (r.insert (rowSpec E) _ _) + _ = _
            rw [rowsWeight_insert_none hr.1 _ hn]
            simp only [rowFreed, RowTouch.growth, rowEntryWeight, Nat.add_zero]
        | upsert amt v =>
            simp only [except_bind_ok] at h
            obtain ⟨⟨⟩, -, ⟨⟩, -, ⟨⟩, -, ⟨⟩, -, h⟩ := h
            simp only [pure, Except.pure, Except.ok.injEq] at h
            subst h
            have hr1 := Trie.canon_insert (rowSpec E) (.row key) (.row amt v) hr
            have hg1 : (r.insert (rowSpec E) (.row key) (.row amt v)).get (rowSpec E) (.head key.parent key.rel) =
                some (.head count sum limit cap width retract) := by
              rw [Trie.get_insert_ne (rowSpec E) _ _ head_ne_row]; exact hg
            refine ⟨?_, Trie.canon_insert (rowSpec E) _ _ hr1⟩
            rw [rowsWeight_setHead hr1.1 hg1]
            change rowsWeight (r.insert (rowSpec E) _ _) + _ = _
            cases hc : r.get (rowSpec E) (.row key) with
            | none =>
                rw [rowsWeight_insert_none hr.1 _ hc]
                simp only [rowFreed, rowAt, hc, Option.map_none, Option.getD_none, RowTouch.growth,
                  rowEntryWeight, Nat.add_zero]
            | some old =>
                have := rowsWeight_insert_some hr.1 (.row amt v) hc
                simp only [rowFreed, rowAt, hc, Option.map_some, Option.getD_some, RowTouch.growth]
                simp only [rowEntryWeight] at this ⊢
                omega
        | retract =>
            simp only [except_bind_ok] at h
            obtain ⟨⟨⟩, -, ⟨⟩, -, h⟩ := h
            split at h
            · rename_i a val hc
              simp only [pure, Except.pure, Except.ok.injEq] at h
              subst h
              have hc' : r.get (rowSpec E) (.row key) = some (.row a val) := hc
              obtain ⟨hw, hcan, hget⟩ := rowsWeight_retain hr hc' (rowPath E (.row key)) (under_rowPath E (.row key))
              have hg1 := hget (.head key.parent key.rel)
              rw [if_neg head_ne_row, hg] at hg1
              refine ⟨?_, Trie.canon_insert (rowSpec E) _ _ hcan⟩
              have hs := rowsWeight_setHead (c' := count - 1) (s' := sum - a) hcan.1 hg1
              simp only [rowFreed, rowAt, hc', Option.map_some, Option.getD_some, RowTouch.growth]
              omega
            · simp at h
        | declare _ _ _ _ => simp at h

/-! ## Every row touch of a turn -/

theorem foldRows_weight {E : Env D} {w : World D} {t : Turn D} :
    ∀ (l : List (RowTouch D)) (acc rr : Rows D × Nat), Trie.Canon (rowSpec E) 0 acc.1 →
      l.foldlM (rowStepFreed E w t) acc = .ok rr →
      rowsWeight rr.1 + rr.2 = rowsWeight acc.1 + acc.2 + (l.map RowTouch.growth).sum ∧
        Trie.Canon (rowSpec E) 0 rr.1
  | [], acc, rr, hc, h => by
      simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h
      subst h; simp [hc]
  | x :: rest, acc, rr, hc, h => by
      rw [List.foldlM_cons, except_bind_ok] at h
      obtain ⟨acc', h1, h2⟩ := h
      unfold rowStepFreed at h1
      rw [except_bind_ok] at h1
      obtain ⟨r1, hs, he⟩ := h1
      simp only [pure, Except.pure, Except.ok.injEq] at he
      subst he
      obtain ⟨hw, hc1⟩ := rowStep_weight hc hs
      obtain ⟨ih, hc2⟩ := foldRows_weight rest _ rr hc1 h2
      refine ⟨?_, hc2⟩
      simp only [List.map_cons, List.sum_cons] at ih ⊢
      omega

/-! ## A retired parent's heads leave (`dropHeads`) -/

omit [Ord D] [DecidableEq D] in
theorem takeList_sublist {K V : Type} : ∀ (n : Nat) (t : Trie.T K V D), (takeList n t).Sublist t.toList
  | _, .empty => by simp [takeList, Trie.T.toList]
  | n, .leaf _ kvs => by simpa [takeList, Trie.T.toList] using List.take_sublist n kvs
  | n, .node _ _ _ l r => by
      unfold takeList; simp only [Trie.T.toList]
      split
      · exact List.nil_sublist _
      · exact (takeList_sublist n l).append (takeList_sublist _ r)

omit [Ord D] [DecidableEq D] in
/-- A bounded listing lists entries the trie holds, each once. -/
theorem under_sublist {K V : Type} (S : Trie.Spec K V D) (pre : ByteArray) (n : Nat) :
    ∀ (t : Trie.T K V D), (under S pre n t).Sublist t.toList
  | .empty => by simp [under, Trie.T.toList]
  | .leaf _ kvs => by
      simp only [under, Trie.T.toList]
      exact (List.take_sublist _ _).trans List.filter_sublist
  | .node h b rep l r => by
      unfold under; simp only [Trie.T.toList]
      split
      · split
        · exact (under_sublist S pre n r).trans (List.sublist_append_right _ _)
        · exact (under_sublist S pre n l).trans (List.sublist_append_left _ _)
      · split
        · exact takeList_sublist n (.node h b rep l r)
        · exact List.nil_sublist _

omit [Ord D] in
/-- Removing listed entries one at a time: each gives back exactly its weight. -/
theorem dropList_weight {E : Env D} :
    ∀ (L : List (RowSlot D × RowLeaf)) (acc : Rows D × Nat), Trie.Canon (rowSpec E) 0 acc.1 →
      (L.map Prod.fst).Nodup → (∀ q ∈ L, q ∈ acc.1.toList) →
      let rr := L.foldl (fun acc p =>
          (Trie.retainAt (rowSpec E) (fun k _ => decide (k ≠ p.1)) (rowPath E p.1) acc.1, acc.2 + rowEntryWeight p)) acc
      rowsWeight rr.1 + rr.2 = rowsWeight acc.1 + acc.2 ∧ Trie.Canon (rowSpec E) 0 rr.1
  | [], acc, hc, _, _ => ⟨rfl, hc⟩
  | p :: L, acc, hc, hn, hm => by
      simp only [List.foldl_cons]
      have hp : acc.1.get (rowSpec E) p.1 = some p.2 := Trie.get_of_mem (rowSpec E) hc.1 (hm p (by simp))
      obtain ⟨hw, hcan, hget⟩ := rowsWeight_retain hc hp (rowPath E p.1) (under_rowPath E p.1)
      simp only [List.map_cons, List.nodup_cons] at hn
      have ih := dropList_weight L (_, acc.2 + rowEntryWeight p) hcan hn.2 (by
        intro q hq
        have hq1 : q.1 ≠ p.1 := fun e => hn.1 (e ▸ List.mem_map_of_mem hq)
        have hg := Trie.get_of_mem (rowSpec E) hc.1 (hm q (List.mem_cons_of_mem _ hq))
        refine (Trie.mem_toList (rowSpec E) 0 _ hcan.1 q.1 q.2).mpr ?_
        change Trie.T.get _ _ _ = _
        rw [hget, if_neg hq1, hg])
      refine ⟨?_, ih.2⟩
      have h1 := ih.1
      have e1 : ((Trie.retainAt (rowSpec E) (fun k _ => decide (k ≠ p.1)) (rowPath E p.1) acc.1, acc.2 + rowEntryWeight p) : Rows D × Nat).1 =
          Trie.retainAt (rowSpec E) (fun k _ => decide (k ≠ p.1)) (rowPath E p.1) acc.1 := rfl
      rw [e1] at h1
      rw [show ((p.1, p.2) : RowSlot D × RowLeaf) = p from rfl] at hw
      dsimp only at h1 ⊢
      omega

omit [Ord D] in
/-- **`dropHeads` gives back exactly what it removes**, and the rows stay canonical. -/
theorem dropHeads_weight {E : Env D} (t : Turn D) :
    ∀ (acc : Rows D × Nat), Trie.Canon (rowSpec E) 0 acc.1 →
      rowsWeight (dropHeads E t acc).1 +
          (dropHeads E t acc).2 = rowsWeight acc.1 + acc.2 ∧
        Trie.Canon (rowSpec E) 0 (dropHeads E t acc).1 := by
  unfold dropHeads
  generalize t.touches = xs
  induction xs with
  | nil => intro acc hc; exact ⟨rfl, hc⟩
  | cons x xs ih =>
      intro acc hc
      simp only [List.foldl_cons]
      split
      · have hsub : ((under (rowSpec E) (E.bytes x.cell) 257 acc.1).filter fun p => match p.1 with
            | .head q _ => decide (q = x.cell)
            | .row _ => false).Sublist acc.1.toList :=
          List.filter_sublist.trans (under_sublist (rowSpec E) (E.bytes x.cell) 257 acc.1)
        have h1 := dropList_weight _ acc hc
          (List.Sublist.nodup (hsub.map Prod.fst) (Trie.toList_nodup (rowSpec E) 0 acc.1 hc.1))
          (fun q hq => hsub.subset hq)
        have h2 := ih _ h1.2
        exact ⟨h2.1.trans h1.1, h2.2⟩
      · exact ih acc hc

/-- **A turn's row touches move the rows' weight exactly**: by their growth, less what they give
back; and the rows stay canonical. -/
theorem rowsRun_weight {E : Env D} {w : World D} {t : Turn D} {rr : Rows D × Nat}
    (hr : w.RowsCanon E) (h : rowsRun E w t = .ok rr) :
    rowsWeight rr.1 + rr.2 = rowsWeight w.rows + (t.rows.map RowTouch.growth).sum ∧
      Trie.Canon (rowSpec E) 0 rr.1 := by
  unfold rowsRun at h
  simp only [except_bind_ok] at h
  obtain ⟨⟨⟩, -, ⟨⟩, -, h⟩ := h
  split at h
  · simp at h
  · rw [except_bind_ok] at h
    obtain ⟨acc, hf, he⟩ := h
    simp only [pure, Except.pure, Except.ok.injEq] at he
    subst he
    have h1 := foldRows_weight t.rows (w.rows, 0) acc hr hf
    have h2 := dropHeads_weight (E := E) t acc h1.2
    simp only [Nat.add_zero] at h1
    exact ⟨by omega, h2.2⟩

/-- What `commit` writes to the rows: `rowsAfter` (at the trie's empty digest, the same value). -/
theorem admit_rows {E : Env D} {w w' : World D} {t : Turn D} (h : World.admit E w t = .ok w') :
    ∃ posts, Checked E w t posts ∧ w'.rows = (rowsAfter E w t).1 := by
  obtain ⟨posts, hk, rfl⟩ := admit_ok h
  exact ⟨posts, hk, rfl⟩

/-- **The rows' storage after a turn**: exactly the row touches' growth less what they give back. -/
theorem rowsAfter_weight {E : Env D} {w : World D} {t : Turn D} {posts : List (Post D)}
    (hr : w.RowsCanon E) (hk : Checked E w t posts) :
    rowsWeight (rowsAfter E w t).1 + (rowsAfter E w t).2 = rowsWeight w.rows + (t.rows.map RowTouch.growth).sum :=
  (rowsRun_weight hr hk.rows).1

theorem admit_rowsCanon {E : Env D} {w w' : World D} {t : Turn D} (hr : w.RowsCanon E)
    (h : World.admit E w t = .ok w') : w'.RowsCanon E := by
  obtain ⟨_, hk, he⟩ := admit_rows h
  unfold World.RowsCanon; rw [he]
  exact (rowsRun_weight hr hk.rows).2

/-- **A refusal leaves the rows as they were** (KERNEL-47's frame, for the fourth trie). -/
theorem refuse_rows {E : Env D} {w w' : World D} {r : Refused D} (h : World.refuse E w r = .ok w') :
    w'.rows = w.rows := by
  obtain ⟨_, rfl⟩ := refuse_ok h; rfl

theorem refuse_rowsCanon {E : Env D} {w w' : World D} {r : Refused D} (hr : w.RowsCanon E)
    (h : World.refuse E w r = .ok w') : w'.RowsCanon E := by
  unfold World.RowsCanon; rw [refuse_rows h]; exact hr

theorem fold_rowsCanon {E : Env D} {w w' : World D} {l : List (Step D)} (hr : w.RowsCanon E)
    (h : World.fold E w l = .ok w') : w'.RowsCanon E :=
  fold_keeps (P := fun v => v.RowsCanon E) admit_rowsCanon refuse_rowsCanon hr h

omit [DecidableEq D] in
theorem genesis_rowsCanon (E : Env D) (o : D) (a : Nat) : (World.genesis E o a).RowsCanon E :=
  Trie.canon_empty _ 0

theorem receive_genesis_rowsCanon (X : Receive.Ctx D) (name nonce : ByteArray) (allowance : Nat)
    (founders : List (ByteArray × D)) : (Receive.genesisWorld X name nonce allowance founders).RowsCanon X.env :=
  Trie.canon_empty _ 0

/-! ## The two pin kinds bind (LANG-14 R1: a moved row pin and a moved range pin are both `stale`) -/

/-- **Range pins from the intent.** Every range read of an admitted turn named a relation that
exists, its listing fit `most`, and its pin is the listing's in the pre-state. -/
theorem admit_range_pins {E : Env D} {w w' : World D} {t : Turn D} (h : World.admit E w t = .ok w') :
    ∀ q ∈ t.ranges, ∃ c s lim cap width rt l, headOf E w.rows q.parent q.rel = some (c, s, lim, cap, width, rt) ∧
      rangeRows E w.rows q.parent q.rel width q.pre q.most = some l ∧
      rangePin E q.parent q.rel width q.pre l = q.seen := by
  obtain ⟨_, hk, _⟩ := admit_ok h
  intro q hq
  have hq' := (forEx_ok.mp hk.ranges) q hq
  simp only [except_bind_ok] at hq'
  obtain ⟨⟨⟩, -, hq'⟩ := hq'
  split at hq'
  · simp at hq'
  · rename_i c s lim cap width rt hh
    simp only [except_bind_ok] at hq'
    obtain ⟨⟨⟩, -, hq'⟩ := hq'
    split at hq'
    · simp at hq'
    · rename_i l hl
      exact ⟨c, s, lim, cap, width, rt, l, hh, hl, of_decide_eq_true (req_ok.mp hq')⟩

/-- **A stale range pin is refused**: a range whose listing in the pre-state has another pin is
admitted by no World transition. -/
theorem range_stale_refused {E : Env D} {w : World D} {t : Turn D} {q : RangeRead D} (hq : q ∈ t.ranges)
    (hstale : ∀ c s lim cap width rt l, headOf E w.rows q.parent q.rel = some (c, s, lim, cap, width, rt) →
      rangeRows E w.rows q.parent q.rel width q.pre q.most = some l →
      rangePin E q.parent q.rel width q.pre l ≠ q.seen) :
    ∀ w', World.admit E w t ≠ .ok w' := by
  intro w' h
  obtain ⟨c, s, lim, cap, width, rt, l, hh, hl, hp⟩ := admit_range_pins h q hq
  exact hstale c s lim cap width rt l hh hl hp

/-- A row touch that passes saw its row's pin in the rows it was judged on. -/
theorem rowStep_pin {E : Env D} {w : World D} {t : Turn D} {r r' : Rows D} {x : RowTouch D}
    {key : RowKey D} {s : D} (hs : x.slot = .row key) (hseen : x.seen = some s)
    (h : rowStep E w t r x = .ok r') :
    rowPin E (rowAt E r (.row key)) = s := by
  obtain ⟨slot, seen, act⟩ := x
  simp only at hs hseen
  subst hs hseen
  unfold rowStep at h
  simp only [except_bind_ok] at h
  obtain ⟨⟨⟩, -, ⟨⟩, -, ⟨⟩, -, h⟩ := h
  split at h
  · simp at h
  · simp only [except_bind_ok] at h
    obtain ⟨⟨⟩, -, h⟩ := h
    cases act with
    | keep =>
        simp only [except_bind_ok] at h
        obtain ⟨⟨⟩, hp, -⟩ := h
        exact of_decide_eq_true (req_ok.mp hp)
    | insert _ _ =>
        simp only [except_bind_ok] at h
        obtain ⟨⟨⟩, hp, -⟩ := h
        simp [req] at hp
    | upsert _ _ =>
        simp only [except_bind_ok] at h
        obtain ⟨⟨⟩, hp, -⟩ := h
        exact of_decide_eq_true (req_ok.mp hp)
    | retract =>
        simp only [except_bind_ok] at h
        obtain ⟨⟨⟩, hp, -⟩ := h
        exact of_decide_eq_true (req_ok.mp hp)
    | declare _ _ _ _ => simp at h

/-- A row touch writes only its own slot and heads: every other row reads as before. -/
theorem rowStep_get_other {E : Env D} {w : World D} {t : Turn D} {r r' : Rows D} {x : RowTouch D}
    (hr : Trie.Canon (rowSpec E) 0 r) (h : rowStep E w t r x = .ok r')
    {key : RowKey D} (hne : x.slot ≠ .row key) :
    r'.get (rowSpec E) (.row key) = r.get (rowSpec E) (.row key) := by
  have hhr : ∀ (p : D) (rel : Nat), (RowSlot.row key : RowSlot D) ≠ .head p rel := fun _ _ h => by cases h
  obtain ⟨slot, seen, act⟩ := x
  simp only at hne
  cases slot with
  | head p rel =>
      cases act with
      | declare limit cap width retract =>
          unfold rowStep at h
          simp only [except_bind_ok] at h
          obtain ⟨⟨⟩, -, ⟨⟩, -, ⟨⟩, -, ⟨⟩, -, ⟨⟩, -, hw⟩ := h
          simp only [pure, Except.pure, Except.ok.injEq] at hw
          subst hw
          exact Trie.get_insert_ne (rowSpec E) _ _ (hhr p rel)
      | keep => simp [rowStep] at h
      | insert _ _ => simp [rowStep] at h
      | upsert _ _ => simp [rowStep] at h
      | retract => simp [rowStep] at h
  | row k0 =>
      have hk : (RowSlot.row key : RowSlot D) ≠ .row k0 := fun e => hne e.symm
      unfold rowStep at h
      simp only [except_bind_ok] at h
      obtain ⟨⟨⟩, -, ⟨⟩, -, ⟨⟩, -, h⟩ := h
      split at h
      · simp at h
      · simp only [except_bind_ok] at h
        obtain ⟨⟨⟩, -, h⟩ := h
        cases act with
        | keep =>
            simp only [except_bind_ok] at h
            obtain ⟨⟨⟩, -, h⟩ := h
            simp only [pure, Except.pure, Except.ok.injEq] at h
            subst h; rfl
        | insert amt v =>
            simp only [except_bind_ok] at h
            obtain ⟨⟨⟩, -, ⟨⟩, -, ⟨⟩, -, ⟨⟩, -, ⟨⟩, -, h⟩ := h
            simp only [pure, Except.pure, Except.ok.injEq] at h
            subst h
            unfold setHead
            rw [Trie.get_insert_ne (rowSpec E) _ _ (hhr _ _), Trie.get_insert_ne (rowSpec E) _ _ hk]
        | upsert amt v =>
            simp only [except_bind_ok] at h
            obtain ⟨⟨⟩, -, ⟨⟩, -, ⟨⟩, -, ⟨⟩, -, h⟩ := h
            simp only [pure, Except.pure, Except.ok.injEq] at h
            subst h
            unfold setHead
            rw [Trie.get_insert_ne (rowSpec E) _ _ (hhr _ _), Trie.get_insert_ne (rowSpec E) _ _ hk]
        | retract =>
            simp only [except_bind_ok] at h
            obtain ⟨⟨⟩, -, ⟨⟩, -, h⟩ := h
            split at h
            · rename_i a val hc
              simp only [pure, Except.pure, Except.ok.injEq] at h
              subst h
              have hc' : r.get (rowSpec E) (.row k0) = some (.row a val) := hc
              obtain ⟨-, -, hget⟩ := rowsWeight_retain hr hc' (rowPath E (.row k0)) (under_rowPath E (.row k0))
              unfold setHead
              rw [Trie.get_insert_ne (rowSpec E) _ _ (hhr _ _), hget, if_neg hk]
            · simp at h
        | declare _ _ _ _ => simp at h

theorem foldRows_pins {E : Env D} {w : World D} {t : Turn D} :
    ∀ (l : List (RowTouch D)) (acc rr : Rows D × Nat), Trie.Canon (rowSpec E) 0 acc.1 →
      (l.map RowTouch.slot).Nodup →
      l.foldlM (rowStepFreed E w t) acc = .ok rr →
      ∀ x ∈ l, ∀ key s, x.slot = .row key → x.seen = some s → rowPin E (rowAt E acc.1 (.row key)) = s
  | [], _, _, _, _, _, x, hx, _, _, _, _ => by simp at hx
  | y :: rest, acc, rr, hc, hn, h, x, hx, key, s, hs, hseen => by
      rw [List.foldlM_cons, except_bind_ok] at h
      obtain ⟨acc', h1, h2⟩ := h
      unfold rowStepFreed at h1
      rw [except_bind_ok] at h1
      obtain ⟨r1, hstep, he⟩ := h1
      simp only [pure, Except.pure, Except.ok.injEq] at he
      subst he
      simp only [List.map_cons, List.nodup_cons] at hn
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact rowStep_pin hs hseen hstep
      · have hc1 := (rowStep_weight hc hstep).2
        have ih := foldRows_pins rest (r1, acc.2 + rowFreed E acc.1 y) rr hc1 hn.2 h2 x hx' key s hs hseen
        have hne : y.slot ≠ .row key := by
          intro e; apply hn.1; rw [e, ← hs]; exact List.mem_map_of_mem hx'
        unfold rowAt at ih ⊢
        rw [← rowStep_get_other hc hstep hne]
        exact ih

omit [Ord D] in
theorem nodup_of_find_none {α β : Type} [DecidableEq β] {f : α → β} {l : List α}
    (h : l.find? (fun x => decide (1 < (l.filter fun y => decide (f y = f x)).length)) = none) :
    (l.map f).Nodup := by
  rw [List.nodup_iff_count]
  intro b
  by_cases hb : b ∈ l.map f
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hb
    have := List.find?_eq_none.mp h x hx
    simp only [decide_eq_true_eq, Nat.not_lt] at this
    have e : (l.map f).count (f x) = (l.filter fun y => decide (f y = f x)).length := by
      rw [List.count_eq_countP, List.countP_map, List.countP_eq_length_filter]; rfl
    omega
  · rw [List.count_eq_zero_of_not_mem hb]; omega

/-- **Row pins from the intent.** Every pinned row touch of an admitted turn saw, in the
pre-state, exactly the row the signer saw (slots are distinct, so no earlier touch of the turn moved
it). -/
theorem admit_row_pins {E : Env D} {w w' : World D} {t : Turn D} (hr : w.RowsCanon E)
    (h : World.admit E w t = .ok w') :
    ∀ x ∈ t.rows, ∀ key s, x.slot = .row key → x.seen = some s → rowPin E (rowAt E w.rows (.row key)) = s := by
  obtain ⟨_, hk, _⟩ := admit_ok h
  have hrun := hk.rows
  unfold rowsRun at hrun
  simp only [except_bind_ok] at hrun
  obtain ⟨⟨⟩, -, ⟨⟩, -, hrun⟩ := hrun
  split at hrun
  · simp at hrun
  · rename_i hfind
    rw [except_bind_ok] at hrun
    obtain ⟨acc, hrun, -⟩ := hrun
    exact foldRows_pins t.rows (w.rows, 0) acc hr (nodup_of_find_none hfind) hrun

/-- **A stale row pin is refused**: a row touch whose pin disagrees with the pre-state row is
admitted by no World transition. -/
theorem rows_stale_refused {E : Env D} {w : World D} {t : Turn D} {x : RowTouch D} {key : RowKey D} {s : D}
    (hr : w.RowsCanon E) (hx : x ∈ t.rows) (hs : x.slot = .row key) (hseen : x.seen = some s)
    (hstale : rowPin E (rowAt E w.rows (.row key)) ≠ s) : ∀ w', World.admit E w t ≠ .ok w' :=
  fun _ h => hstale (admit_row_pins hr h x hx key s hs hseen)
