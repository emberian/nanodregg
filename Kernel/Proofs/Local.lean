/-
# Kernel.Proofs.Local — the locality half of the frame rule (cv 01a14f65, KERNEL-51's follow-on)

`admit_Frame` says what an admitted turn WRITES: nothing outside its footprint. `check_local` says
what a check READS: nothing outside its read set. Two Worlds that `Agree E w w' t` (the cells on
`CellRead t`, the scalars `check` reads, the journal and the refusals at the turn's own keys, the
rows by `RowsAgree`) check `t` alike: the same refusal, or the same posts.

The cells take no trie-wide premise: `touches_local`, `checkNullifiers_local` and
`checkCreates_local` each read one slot per element. The rows are the same trie
(`RowsAgree.same`, no premise) or agree slot-wise on canonical tries (`RowsAgree.read`): a range
read and a retirement list a prefix (`under`), which walks the trie's shape, and `under_local` is
where the canonical premises are spent.

The teeth: `check_local_outside` (an admitted pair differing at a cell outside the read set, the
theorem's instance); `check_unread_row` (a row written outside the rows' read set changes no check:
`RowsAgree.read` over rows that differ); `check_reads_kept` and its `_sep` form (a `keep`-pinned cell is read but not written: a World
differing there alone, every other field equal, refuses the turn the other admits, unless two named
pin preimages collide), so the read set is strictly larger than the footprint and cannot shrink to
it.
-/
import Kernel.Proofs.RowsSep
import Kernel.Proofs.RowsRange
import Kernel.Proofs.Logic.Frame

namespace Nanodregg.Kernel

variable {D : Type} [Ord D] [DecidableEq D]

/-! ## The cells: one slot per read, no premise -/

private theorem entry_local {E : Env D} {w w' : World D} {c : D}
    (h : w'.trie.get (trieSpec E) (.cell c) = w.trie.get (trieSpec E) (.cell c)) : w'.entry E c = w.entry E c := by
  unfold World.entry; rw [h]

/-- The touches read each touched cell's entry, and nothing else of the World. -/
theorem touches_local {E : Env D} {w w' : World D} {t : Turn D}
    (hc : ∀ s, CellRead t s → w'.trie.get (trieSpec E) s = w.trie.get (trieSpec E) s) :
    mapEx (touchCheck E w') t.touches = mapEx (touchCheck E w) t.touches :=
  mapEx_congr fun x hx => by unfold touchCheck; rw [entry_local (hc _ (.touched hx))]

/-- The nullifier check reads each spent nullifier's slot. -/
theorem checkNullifiers_local {E : Env D} {w w' : World D} {t : Turn D}
    (hc : ∀ s, CellRead t s → w'.trie.get (trieSpec E) s = w.trie.get (trieSpec E) s) :
    checkNullifiers E w' t = checkNullifiers E w t :=
  forEx_congr fun n hn => by simp only [World.isSpent, hc _ (.spent hn)]

/-- The births read each born id's slot. -/
theorem checkCreates_local {E : Env D} {w w' : World D} {t : Turn D}
    (hc : ∀ s, CellRead t s → w'.trie.get (trieSpec E) s = w.trie.get (trieSpec E) s) :
    checkCreates E w' t = checkCreates E w t := by
  have h : forEx (fun c => req (!w'.taken E c) (Reject.idTaken c)) (createdIds t) =
      forEx (fun c => req (!w.taken E c) (Reject.idTaken c)) (createdIds t) :=
    forEx_congr fun c hb => by simp only [World.taken, entry_local (hc _ (.born hb))]
  unfold checkCreates; rw [h]

/-- A touched cell reads live alike (a row touch's parent and a range's are pinned before they are
read, so every cell the rows read is a touched one). -/
theorem live_local {E : Env D} {w w' : World D} {t : Turn D}
    (hc : ∀ s, CellRead t s → w'.trie.get (trieSpec E) s = w.trie.get (trieSpec E) s) :
    ∀ c, (t.touches.any fun y => decide (y.cell = c)) = true → w'.live E c = w.live E c := by
  intro c h
  obtain ⟨y, hy, hyc⟩ := List.any_eq_true.mp h
  have e : y.cell = c := of_decide_eq_true hyc
  subst e
  unfold World.live; rw [entry_local (hc _ (.touched hy))]

/-! ## The rows -/

omit [Ord D] in
private theorem headOf_congr {E : Env D} {r r' : Rows D} {p : D} {rel : Nat}
    (h : rowAt E r' (.head p rel) = rowAt E r (.head p rel)) : headOf E r' p rel = headOf E r p rel := by
  unfold headOf; rw [h]

omit [Ord D] in
private theorem headFloor_congr {E : Env D} {r r' : Rows D} {p : D} {rel : Nat}
    (h : rowAt E r' (.head p rel) = rowAt E r (.head p rel)) : headFloor E r' p rel = headFloor E r p rel := by
  unfold headFloor; rw [h]

/-- A row touch reads the World through its parent's liveness (pinned first: `rowParentUnpinned`)
and its relation's floor before the turn. -/
private theorem rowStep_world {E : Env D} {w w' : World D} {t : Turn D} {r : Rows D} {x : RowTouch D}
    (hl : ∀ c, (t.touches.any fun y => decide (y.cell = c)) = true → w'.live E c = w.live E c)
    (hfl : ∀ key, x.slot = .row key →
      headFloor E w'.rows key.parent key.rel = headFloor E w.rows key.parent key.rel) :
    rowStep E w' t r x = rowStep E w t r x := by
  obtain ⟨slot, seen, act⟩ := x
  cases slot with
  | head p rel => cases act <;> rfl
  | row key =>
      simp only [rowStep]
      rw [hfl key rfl]
      by_cases ht : (t.touches.any fun y => decide (y.cell = key.parent)) = true
      · rw [hl _ ht]
      · simp [req, ht, bind, Except.bind]

omit [Ord D] [DecidableEq D] in
private theorem req_bind {α : Type} {b : Bool} {e : Reject D} {f : Unit → Except (Reject D) α} :
    (req b e >>= f) = if b then f () else .error e := by
  unfold req; cases b <;> rfl

/-- Two runs agree: the same refusal, or results related by `P`. -/
private def ExRel {α : Type} (P : α → α → Prop) : Except (Reject D) α → Except (Reject D) α → Prop
  | .error e, .error e' => e = e'
  | .ok a, .ok a' => P a a'
  | _, _ => False

omit [Ord D] in
private theorem tr_insert {E : Env D} {r r' : Rows D} (k : RowSlot D) (v : RowLeaf) {s : RowSlot D}
    (h : rowAt E r' s = rowAt E r s) :
    rowAt E (r'.insert (rowSpec E) k v) s = rowAt E (r.insert (rowSpec E) k v) s := by
  unfold rowAt at h ⊢; rw [Trie.get_insert, Trie.get_insert, h]

omit [Ord D] in
private theorem retain_under {E : Env D} (r : Rows D) (k : RowSlot D) :
    ∀ p ∈ r.toList, decide (p.1 ≠ k) = false → Trie.Under (rowSpec E) 0 (rowPath E k) p.1 := by
  rintro ⟨pk, pv⟩ _ hf
  have : pk = k := Classical.not_not.mp (of_decide_eq_false hf)
  subst this
  exact under_rowPath E pk

omit [Ord D] in
private theorem get_retain {E : Env D} {r : Rows D} (hr : Trie.Canon (rowSpec E) 0 r) (k s : RowSlot D) :
    rowAt E (Trie.retainAt (rowSpec E) (fun k' _ => decide (k' ≠ k)) (rowPath E k) r) s =
      (rowAt E r s).filter fun _ => decide (s ≠ k) := by
  unfold rowAt
  exact Trie.get_retainAt (rowSpec E) _ _ hr (retain_under r k) s

omit [Ord D] in
private theorem canon_retain {E : Env D} {r : Rows D} (hr : Trie.Canon (rowSpec E) 0 r) (k : RowSlot D) :
    Trie.Canon (rowSpec E) 0 (Trie.retainAt (rowSpec E) (fun k' _ => decide (k' ≠ k)) (rowPath E k) r) :=
  Trie.canon_retainAt (rowSpec E) _ _ 0 r hr (retain_under r k)

omit [Ord D] in
private theorem tr_retain {E : Env D} {r r' : Rows D} (hr : Trie.Canon (rowSpec E) 0 r)
    (hr' : Trie.Canon (rowSpec E) 0 r') (k : RowSlot D) {s : RowSlot D} (h : rowAt E r' s = rowAt E r s) :
    rowAt E (Trie.retainAt (rowSpec E) (fun k' _ => decide (k' ≠ k)) (rowPath E k) r') s =
      rowAt E (Trie.retainAt (rowSpec E) (fun k' _ => decide (k' ≠ k)) (rowPath E k) r) s := by
  rw [get_retain hr', get_retain hr, h]

omit [Ord D] [DecidableEq D] in
private theorem exRel_ite {α : Type} {P : α → α → Prop} {c : Prop} [Decidable c] {a a' b b' : Except (Reject D) α}
    (h1 : c → ExRel P a a') (h2 : ¬ c → ExRel P b b') : ExRel P (if c then a else b) (if c then a' else b') := by
  by_cases hc : c
  · rw [if_pos hc, if_pos hc]; exact h1 hc
  · rw [if_neg hc, if_neg hc]; exact h2 hc

/-- **One row touch, two tries**: on tries that read the same at the touch's slot and its row's
head, the step refuses alike or writes alike (every slot reading the same before reads the same
after). -/
private theorem rowStep_local {E : Env D} {w : World D} {t : Turn D} {r r' : Rows D} {x : RowTouch D}
    (hr : Trie.Canon (rowSpec E) 0 r) (hr' : Trie.Canon (rowSpec E) 0 r')
    (hs : rowAt E r' x.slot = rowAt E r x.slot)
    (hh : ∀ key, x.slot = .row key → rowAt E r' (.head key.parent key.rel) = rowAt E r (.head key.parent key.rel)) :
    ExRel (fun a a' => ∀ s, rowAt E r' s = rowAt E r s → rowAt E a' s = rowAt E a s)
      (rowStep E w t r x) (rowStep E w t r' x) := by
  obtain ⟨slot, seen, act⟩ := x
  cases slot with
  | head p rel =>
      simp only at hs
      cases act with
      | declare limit cap width retract =>
          simp only [rowStep, req_bind, hs]
          repeat (refine exRel_ite (fun _ => ?_) (fun _ => ?_))
          all_goals simp only [ExRel, pure, Except.pure]
          intro s h; exact tr_insert _ _ h
      | _ => simp [rowStep, ExRel]
  | row key =>
      simp only at hs hh
      have hH := headOf_congr (hh key rfl)
      have hF := headFloor_congr (hh key rfl)
      cases act <;> simp only [rowStep, req_bind, hH, hF, hs] <;>
        rcases headOf E r key.parent key.rel with _ | ⟨c, sm, lim, cap, wd, rt⟩ <;>
        rcases seen with _ | sn <;>
        rcases rowAt E r (.row key) with _ | (⟨_, _, _, _, _, _, _⟩ | ⟨a, v, u⟩) <;>
        simp only [req_bind, pure, Except.pure] <;>
        (repeat (refine exRel_ite (fun _ => ?_) (fun _ => ?_))) <;>
        simp only [ExRel, setHead] <;>
        first
          | rfl
          | (intro s h; first
              | exact h
              | exact tr_insert _ _ (tr_insert _ _ h)
              | exact tr_insert _ _ (tr_retain hr hr' _ h))

omit [Ord D] in
private theorem rowFreed_congr {E : Env D} {r r' : Rows D} {x : RowTouch D}
    (h : rowAt E r' x.slot = rowAt E r x.slot) : rowFreed E r' x = rowFreed E r x := by
  unfold rowFreed; rw [h]

/-- A row touch writes only its slot and its row's head, so what it leaves fits if they do. -/
private theorem rowStep_fits {E : Env D} {w : World D} {t : Turn D} {r a : Rows D} {x : RowTouch D}
    (hr : Trie.Canon (rowSpec E) 0 r) (h : rowStep E w t r x = .ok a) (hx : RowSlotFits x.slot)
    (hxh : ∀ key, x.slot = .row key → RowSlotFits (.head key.parent key.rel : RowSlot D))
    (hf : ∀ s, rowAt E r s ≠ none → RowSlotFits s) : ∀ s, rowAt E a s ≠ none → RowSlotFits s := by
  intro s hs
  by_cases h1 : s = x.slot
  · exact h1 ▸ hx
  · by_cases h2 : ∃ key, x.slot = .row key ∧ s = .head key.parent key.rel
    · obtain ⟨key, hk, rfl⟩ := h2; exact hxh key hk
    · apply hf
      have e := rowStep_get_out hr h (s := s) fun _ => ⟨h1, fun key hk e => h2 ⟨key, hk, e⟩⟩
      unfold rowAt at hs ⊢; rwa [← e]

/-- What two runs of the rows keep related: both tries canonical, the same freed total, the same
reads on `A`, and the first run's entries fitting (the keys `under_local` separates). -/
private structure Inv (E : Env D) (A : RowSlot D → Prop) (a a' : Rows D × Nat) : Prop where
  canon : Trie.Canon (rowSpec E) 0 a.1
  canon' : Trie.Canon (rowSpec E) 0 a'.1
  freed : a'.2 = a.2
  agree : ∀ s, A s → rowAt E a'.1 s = rowAt E a.1 s
  fits : ∀ s, rowAt E a.1 s ≠ none → RowSlotFits s

/-- **The row touches, two Worlds**: every touch reads on `A` (its slot, its row's head) and fits,
and the Worlds agree on each row's floor and on the touched cells: the runs refuse alike or keep
`Inv`. -/
private theorem fold_local {E : Env D} {w w' : World D} {t : Turn D} {A : RowSlot D → Prop}
    (hl : ∀ c, (t.touches.any fun y => decide (y.cell = c)) = true → w'.live E c = w.live E c) :
    ∀ (l : List (RowTouch D)) (acc acc' : Rows D × Nat),
      (∀ x ∈ l, A x.slot ∧ RowSlotFits x.slot ∧ ∀ key, x.slot = .row key →
        A (.head key.parent key.rel) ∧ headFloor E w'.rows key.parent key.rel = headFloor E w.rows key.parent key.rel) →
      Inv E A acc acc' →
      ExRel (Inv E A) (l.foldlM (rowStepFreed E w t) acc) (l.foldlM (rowStepFreed E w' t) acc')
  | [], acc, acc', _, h => h
  | x :: rest, acc, acc', hx, h => by
      obtain ⟨hAs, hfs, hAh⟩ := hx x (by simp)
      have hw : rowStep E w' t acc'.1 x = rowStep E w t acc'.1 x :=
        rowStep_world hl fun key hk => (hAh key hk).2
      have hst := rowStep_local (w := w) (t := t) h.canon h.canon' (h.agree _ hAs)
        fun key hk => h.agree _ (hAh key hk).1
      have hxh : ∀ key, x.slot = .row key → RowSlotFits (.head key.parent key.rel : RowSlot D) := by
        intro key hk; rw [hk] at hfs; exact hfs.1
      simp only [List.foldlM_cons, rowStepFreed, hw]
      cases hR : rowStep E w t acc.1 x with
      | error e =>
          cases hR' : rowStep E w t acc'.1 x with
          | error e' => rw [hR, hR'] at hst; cases hst; rfl
          | ok a' => rw [hR, hR'] at hst; exact hst.elim
      | ok a =>
          cases hR' : rowStep E w t acc'.1 x with
          | error e' => rw [hR, hR'] at hst; exact hst.elim
          | ok a' =>
              rw [hR, hR'] at hst
              exact fold_local hl rest _ _ (fun y hy => hx y (List.mem_cons_of_mem _ hy))
                { canon := (rowStep_weight h.canon hR).2
                  canon' := (rowStep_weight h.canon' hR').2
                  freed := by show acc'.2 + _ = acc.2 + _; rw [h.freed, rowFreed_congr (h.agree _ hAs)]
                  agree := fun s hs => hst s (h.agree s hs)
                  fits := rowStep_fits h.canon hR hfs hxh h.fits }

omit [Ord D] in
/-- The bridge to `RowsAgree.read`'s `hf`: a canonical rows trie whose entries fit (`rowFits`, what `World.RowsOk` holds) holds only fitting slots. -/
theorem rowSlotFits_of_held {E : Env D} {r : Rows D} (hc : Trie.Canon (rowSpec E) 0 r)
    (hf : ∀ p ∈ r.toList, rowFits p.1 p.2 = true) : ∀ s, rowAt E r s ≠ none → RowSlotFits s := by
  intro s hs
  obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp hs
  exact rowSlotFits_of_rowFits (hf (s, v) ((Trie.mem_toList (rowSpec E) 0 r hc.1 s v).mpr hv))

/-- **A listing reads only under its prefix**: on canonical tries over a lawful `Env`, whose keys
fit, `under` at a prefix (long enough for every key reaching it: `under_eq`'s premise) lists the
same on two tries that read the same at every key starting with it. -/
theorem under_local {E : Env D} {n : Nat} (hE : E.Lawful n) {r r' : Rows D}
    (hc : Trie.Canon (rowSpec E) 0 r) (hc' : Trie.Canon (rowSpec E) 0 r')
    (hf : ∀ s, rowAt E r s ≠ none → RowSlotFits s) {pre : ByteArray}
    (hlong : ∀ s : RowSlot D, (∀ i, i < 8 * pre.size → byteBit (rowKeyBytes E s) i = byteBit pre i) →
      pre.size ≤ (rowKeyBytes E s).size)
    (hag : ∀ s, startsWith pre (rowKeyBytes E s) = true → rowAt E r' s = rowAt E r s) (m : Nat) :
    under (rowSpec E) pre m r' = under (rowSpec E) pre m r := by
  have hu : ∀ {u : Rows D}, Trie.Canon (rowSpec E) 0 u →
      under (rowSpec E) pre m u = (u.toList.filter fun p => startsWith pre (rowKeyBytes E p.1)).take m :=
    fun hu => under_eq (rowSpec E) (fun _ _ => rfl) pre m 0 _ hu.1 hu.2.2
      (fun _ _ _ _ _ hi => absurd hi (Nat.not_lt_zero _)) (fun p _ hb => hlong p.1 hb)
  let q : RowSlot D → RowLeaf → Bool := fun k _ => startsWith pre (rowKeyBytes E k)
  have hq : ∀ (u : Rows D), ∀ p ∈ u.toList, q p.1 p.2 = false → Trie.Under (rowSpec E) 0 [] p.1 :=
    fun _ _ _ _ _ _ b hb => by simp at hb
  have hlist : ∀ {u : Rows D}, Trie.Canon (rowSpec E) 0 u →
      (Trie.retainAt (rowSpec E) q [] u).toList = u.toList.filter fun p => q p.1 p.2 :=
    fun hu => Trie.toList_retainAt (rowSpec E) q [] 0 _ hu.1 (hq _)
  have heq : Trie.retainAt (rowSpec E) q [] r = Trie.retainAt (rowSpec E) q [] r' := by
    apply Trie.eq_of_get_eq_on (rowSpec E) RowSlotFits (fun _ _ hs _ hne => rows_separateOn hE hs hne)
      (Trie.canon_retainAt (rowSpec E) q [] 0 r hc (hq r)) (Trie.canon_retainAt (rowSpec E) q [] 0 r' hc' (hq r'))
    · intro p hp
      rw [hlist hc, List.mem_filter] at hp
      apply hf p.1
      have hg : r.get (rowSpec E) p.1 = some p.2 := (Trie.mem_toList (rowSpec E) 0 r hc.1 p.1 p.2).mp hp.1
      unfold rowAt; rw [hg]; simp
    · intro k
      rw [Trie.get_retainAt (rowSpec E) q [] hc (hq r) k, Trie.get_retainAt (rowSpec E) q [] hc' (hq r') k]
      by_cases hk : startsWith pre (rowKeyBytes E k) = true
      · have e := hag k hk; unfold rowAt at e; rw [e]
      · simp [q, hk]
  rw [hu hc, hu hc', ← hlist hc, ← hlist hc', heq]

omit [DecidableEq D] in
private theorem bytes_long {E : Env D} {n : Nat} (hE : E.Lawful n) (c : D) (s : RowSlot D) :
    (E.bytes c).size ≤ (rowKeyBytes E s).size := by
  cases s <;> simp [rowKeyBytes, rowsPrefix, ByteArray.size_append, hE.size] <;> omega

omit [Ord D] in
/-- The retired parents' heads, removed one path each, keep `Inv`. -/
private theorem drop_inner {E : Env D} {A : RowSlot D → Prop} :
    ∀ (L : List (RowSlot D × RowLeaf)) (acc acc' : Rows D × Nat), Inv E A acc acc' →
      Inv E A (L.foldl (fun acc p => (Trie.retainAt (rowSpec E) (fun k _ => decide (k ≠ p.1)) (rowPath E p.1) acc.1,
          acc.2 + rowEntryWeight p)) acc)
        (L.foldl (fun acc p => (Trie.retainAt (rowSpec E) (fun k _ => decide (k ≠ p.1)) (rowPath E p.1) acc.1,
          acc.2 + rowEntryWeight p)) acc')
  | [], _, _, h => h
  | p :: L, acc, acc', h => drop_inner L _ _
      { canon := canon_retain h.canon p.1
        canon' := canon_retain h.canon' p.1
        freed := by show acc'.2 + _ = acc.2 + _; rw [h.freed]
        agree := fun s hs => tr_retain h.canon h.canon' p.1 (h.agree s hs)
        fits := fun s hs => h.fits s fun e => hs (by rw [get_retain h.canon, e]; rfl) }

/-- **The retired parents' heads, two Worlds**: on runs related by `Inv` over a set holding every
key under a retired parent, `dropHeads` keeps `Inv` (each listing is the same, `under_local`). -/
private theorem dropHeads_local {E : Env D} {n : Nat} (hE : E.Lawful n) {t : Turn D} {A : RowSlot D → Prop}
    (hA : ∀ x ∈ t.touches, x.act = .retire → ∀ s, startsWith (E.bytes x.cell) (rowKeyBytes E s) = true → A s) :
    ∀ (acc acc' : Rows D × Nat), Inv E A acc acc' → Inv E A (dropHeads E t acc) (dropHeads E t acc') := by
  unfold dropHeads
  generalize t.touches = xs at hA
  induction xs with
  | nil => intro acc acc' h; exact h
  | cons x xs ih =>
      intro acc acc' h
      simp only [List.foldl_cons]
      apply ih (fun y hy => hA y (List.mem_cons_of_mem _ hy))
      cases hx : x.act with
      | retire =>
          simp only []
          rw [under_local hE h.canon h.canon' h.fits (fun s _ => bytes_long hE x.cell s)
            (fun s hs => h.agree s (hA x List.mem_cons_self hx s hs)) 257]
          exact drop_inner _ _ _ h
      | keep => exact h
      | write _ => exact h

/-- The rows-remaining check lists under each retired parent's bytes. -/
private theorem rowsRemain_read {E : Env D} {n : Nat} (hE : E.Lawful n) {w w' : World D} {t : Turn D}
    (hc : w.RowsCanon E) (hc' : w'.RowsCanon E) (hf : ∀ s, rowAt E w.rows s ≠ none → RowSlotFits s)
    (h : ∀ s, RowRead E t s → rowAt E w'.rows s = rowAt E w.rows s) :
    checkRowsRemain E w' t = checkRowsRemain E w t := by
  unfold checkRowsRemain
  refine forEx_congr fun x hx => ?_
  cases ha : x.act with
  | retire =>
      simp only []
      rw [under_local hE hc hc' hf (fun s _ => bytes_long hE x.cell s) (fun s hs => h s (.retired hx ha hs)) 257]
  | keep => rfl
  | write _ => rfl

/-- The range reads list under each range's prefix, at the width its head declares. -/
private theorem ranges_read {E : Env D} {n : Nat} (hE : E.Lawful n) {w w' : World D} {t : Turn D}
    (hc : w.RowsCanon E) (hc' : w'.RowsCanon E) (hf : ∀ s, rowAt E w.rows s ≠ none → RowSlotFits s)
    (h : ∀ s, RowRead E t s → rowAt E w'.rows s = rowAt E w.rows s) :
    checkRanges E w' t = checkRanges E w t := by
  unfold checkRanges
  refine forEx_congr fun q hq => ?_
  have hhd := h _ (.rangeHead hq)
  simp only [headOf_congr hhd, headFloor_congr hhd]
  cases hH : headOf E w.rows q.parent q.rel with
  | none => rfl
  | some v =>
      obtain ⟨c, sm, lim, cap, width, rt⟩ := v
      by_cases hw : q.pre.size ≤ width
      · have hr : rangeRows E w'.rows q.parent q.rel width q.pre q.most =
            rangeRows E w.rows q.parent q.rel width q.pre q.most := by
          unfold rangeRows
          rw [under_local hE hc hc' hf (fun s hb => range_prefix_long E hE.size hw s hb)
            (fun s hs => h s (.ranged hq width hs))]
        simp only [hr]
      · simp [req_bind, hw]

omit [Ord D] [DecidableEq D] in
private theorem fits_of_all {x : RowTouch D}
    (h : (match x.slot with
      | .row key => decide (key.rel < 256) && decide (key.k.size ≤ Bounds.keyBytesMax)
      | .head _ rel => decide (rel < 256)) = true) : RowSlotFits x.slot := by
  obtain ⟨slot, _, _⟩ := x
  cases slot <;> simp_all [RowSlotFits]

/-- **The rows run, two Worlds**: slot-wise agreement on `RowRead`, canonical fitting tries: the
runs refuse alike or give back the same. -/
private theorem rowsRun_read {E : Env D} {n : Nat} (hE : E.Lawful n) {w w' : World D} {t : Turn D}
    (hl : ∀ c, (t.touches.any fun y => decide (y.cell = c)) = true → w'.live E c = w.live E c)
    (hc : w.RowsCanon E) (hc' : w'.RowsCanon E) (hf : ∀ s, rowAt E w.rows s ≠ none → RowSlotFits s)
    (h : ∀ s, RowRead E t s → rowAt E w'.rows s = rowAt E w.rows s) :
    ExRel (fun rr rr' : Rows D × Nat => rr'.2 = rr.2) (rowsRun E w t) (rowsRun E w' t) := by
  have hinv : Inv E (RowRead E t) (w.rows, 0) (w'.rows, 0) := ⟨hc, hc', rfl, h, hf⟩
  unfold rowsRun
  simp only [req_bind]
  refine exRel_ite (fun _ => ?_) (fun _ => rfl)
  refine exRel_ite (fun hall => ?_) (fun _ => rfl)
  split
  · rfl
  · have hfold := fold_local hl t.rows (w.rows, 0) (w'.rows, 0)
      (fun x hx => ⟨.slot hx, fits_of_all (List.all_eq_true.mp hall x hx),
        fun key hk => ⟨.head hx hk, headFloor_congr (h _ (.head hx hk))⟩⟩) hinv
    revert hfold
    cases t.rows.foldlM (rowStepFreed E w t) (w.rows, 0) <;>
      cases t.rows.foldlM (rowStepFreed E w' t) (w'.rows, 0) <;> intro hfold
    · exact hfold
    · exact hfold.elim
    · exact hfold.elim
    · exact (dropHeads_local hE (fun x hx hr s hs => .retired hx hr hs) _ _ hfold).freed

/-- On the same rows, the run reads the World only through the touched cells. -/
private theorem rowsRun_same {E : Env D} {w w' : World D} {t : Turn D}
    (hl : ∀ c, (t.touches.any fun y => decide (y.cell = c)) = true → w'.live E c = w.live E c)
    (h : w'.rows = w.rows) : rowsRun E w' t = rowsRun E w t := by
  have e : rowStepFreed E w' t = rowStepFreed E w t := by
    funext acc x; unfold rowStepFreed; rw [rowStep_world hl fun key _ => by rw [h]]
  unfold rowsRun; rw [e, h]

/-- **The rows' checks read the rows' read set**: on Worlds whose touched cells agree and whose rows
`RowsAgree`, the rows-remaining check, the range reads and the run's verdict and give-back are the
same. -/
theorem rows_local {E : Env D} {w w' : World D} {t : Turn D}
    (hcells : ∀ s, CellRead t s → w'.trie.get (trieSpec E) s = w.trie.get (trieSpec E) s)
    (hr : RowsAgree E w w' t) :
    checkRowsRemain E w' t = checkRowsRemain E w t ∧ checkRanges E w' t = checkRanges E w t ∧
      (rowsRun E w' t).map Prod.snd = (rowsRun E w t).map Prod.snd := by
  have hl := live_local hcells
  cases hr with
  | same h => exact ⟨by unfold checkRowsRemain; rw [h], by unfold checkRanges; rw [h], by rw [rowsRun_same hl h]⟩
  | read hE hc hc' hf h =>
      refine ⟨rowsRemain_read hE hc hc' hf h, ranges_read hE hc hc' hf h, ?_⟩
      have hx := rowsRun_read hE hl hc hc' hf h
      revert hx
      cases rowsRun E w t <;> cases rowsRun E w' t <;> intro hx
      · cases hx; rfl
      · exact hx.elim
      · exact hx.elim
      · simp only [Except.map]; rw [hx]

/-- **Locality (the frame rule's read half).** Two Worlds that agree on what `check E · t` reads
check `t` alike: the same refusal, or the same posts. -/
theorem check_local {E : Env D} {w w' : World D} {t : Turn D} (h : Agree E w w' t) :
    check E w' t = check E w t := by
  obtain ⟨hcells, hH, hS, hA, hJ, hR, hrows⟩ := h
  obtain ⟨hrem, hran, hrun⟩ := rows_local hcells hrows
  have hwin : checkWindow w' t = checkWindow w t := by unfold checkWindow; rw [hH]
  have hjour : checkJournal E w' t = checkJournal E w t := by unfold checkJournal; rw [hJ, hR]
  have hst : checkSteps w' = checkSteps w := by unfold checkSteps; rw [hS]
  have hch : ∀ b, checkCharge w' t b = checkCharge w t b := by intro b; unfold checkCharge; rw [hA]
  show Prod.fst <$> checkWith E w' t = Prod.fst <$> checkWith E w t
  unfold checkWith
  simp only [hwin, hjour, touches_local hcells, checkNullifiers_local hcells, hrem, hran,
    checkCreates_local hcells, hst, hch, map_bind, map_pure]
  revert hrun
  cases rowsRun E w t <;> cases rowsRun E w' t <;> intro hrun
  · cases hrun; rfl
  · cases hrun
  · cases hrun
  · rename_i a b
    obtain ⟨r1, n1⟩ := a
    obtain ⟨r2, n2⟩ := b
    change Except.ok n2 = Except.ok n1 at hrun
    cases hrun; rfl

/-! ## Teeth: the theorem holds of a real pair, and its read set cannot shrink to the footprint -/

/-- An empty RAM cell. -/
private def readCell : Cell := ⟨0, .ram, []⟩

/-- From genesis: `readCell` live at `p`, the allowance exactly the keep turn's weight. -/
private def keptWorld (E : Env D) (o p : D) : World D :=
  { World.genesis E o 145 with
    trie := (Trie.T.empty : Cells D).insert (trieSpec E) (.cell p) (.entry (.live readCell 0)) }

/-- Pin `p` (`keep`) at its live pin, touch nothing else, pay the exact weight. -/
private def keepTurn (E : Env D) (o p : D) : Turn D :=
  { txId := o, notBefore := 1, validUntil := 1, touches := [⟨p, pinOf E (some (.live readCell 0)), .keep⟩],
    creates := [], nullifiers := [], charge := 145, event := ByteArray.empty }

private theorem keepTurn_admitted (E : Env D) (o p : D) (w : World D) (hw : w = keptWorld E o p) :
    check E w (keepTurn E o p) = .ok [] := by
  subst hw
  have hentry : (keptWorld E o p).entry E p = some (.live readCell 0) := by
    simp [keptWorld, World.entry, Trie.get_insert_self]
  have hmap : mapEx (touchCheck E (keptWorld E o p)) (keepTurn E o p).touches = .ok [none] := by
    simp [keepTurn, mapEx, touchCheck, hentry, req, bind, Except.bind, pure, Except.pure]
  unfold check checkWith; rw [hmap]; rfl

/-- **Tooth: Worlds differing outside the read set check alike** (an instance of `check_local`): a
second live cell at `q ≠ p`, outside what the keep turn reads; the turn is admitted from both. -/
theorem check_local_outside (E : Env D) (o p q : D) (hq : q ≠ p) :
    ∃ w w' t, ¬ CellRead t (.cell q) ∧ w'.trie.get (trieSpec E) (.cell q) ≠ w.trie.get (trieSpec E) (.cell q) ∧
      check E w' t = .ok [] ∧ check E w t = .ok [] := by
  let w := keptWorld E o p
  let w' : World D := { w with trie := w.trie.insert (trieSpec E) (.cell q) (.entry (.live readCell 0)) }
  have hnr : ¬ CellRead (keepTurn E o p) (.cell q) := by
    intro h
    cases h with
    | touched hx => simp [keepTurn] at hx; exact hq (by rw [hx])
    | born hc => simp [keepTurn, createdIds] at hc
  have hw : check E w (keepTurn E o p) = .ok [] := keepTurn_admitted E o p w rfl
  refine ⟨w, w', keepTurn E o p, hnr, ?_, ?_, hw⟩
  · show (w.trie.insert (trieSpec E) (.cell q) (.entry (.live readCell 0))).get (trieSpec E) (.cell q) ≠ _
    rw [Trie.get_insert_self]
    simp [w, keptWorld, Trie.get_insert, hq, Trie.get_empty]
  · rw [check_local (w := w) (w' := w') (t := keepTurn E o p)
      ⟨fun s hs => Trie.get_insert_ne _ _ _ fun e => hnr (e ▸ hs), rfl, rfl, rfl, rfl, rfl, .same rfl⟩, hw]

/-- **Tooth: a `keep` pin is read, so the read set cannot shrink to the footprint.** `keptWorld` and
genesis differ only at `p`, which the keep turn reads and does not write; the turn is admitted from
the first and refused from the second, unless the absent pin's and the live pin's preimages collide.
Agreement on the footprint alone does not fix a check. -/
theorem check_reads_kept (E : Env D) (o p : D) :
    ∃ w w' t, ¬ CellFoot t (.cell p) ∧ CellRead t (.cell p) ∧
      (∀ s, s ≠ .cell p → w'.trie.get (trieSpec E) s = w.trie.get (trieSpec E) s) ∧
      w'.height = w.height ∧ w'.steps = w.steps ∧ w'.allowance = w.allowance ∧ w'.journal = w.journal ∧
      w'.refusals = w.refusals ∧ w'.rows = w.rows ∧ check E w t = .ok [] ∧
      (check E w' t ≠ check E w t ∨ CollidesAmong E.hash [pinPre E none, pinPre E (some (.live readCell 0))]) := by
  have hw := keepTurn_admitted E o p _ rfl
  refine ⟨keptWorld E o p, World.genesis E o 145, keepTurn E o p, ?_, .touched (x := ⟨p, pinOf E (some (.live readCell 0)), .keep⟩) (by simp [keepTurn]),
    fun s hs => ?_, rfl, rfl, rfl, rfl, rfl, rfl, hw, ?_⟩
  · intro h
    cases h with
    | touched hx hne => simp [keepTurn] at hx; exact hne (by rw [hx])
    | born hc => simp [keepTurn, createdIds] at hc
  · show (Trie.T.empty : Cells D).get (trieSpec E) s = _
    simp [keptWorld, Trie.get_insert, hs, Trie.get_empty]
  · by_cases hpin : pinOf E none = pinOf E (some (.live readCell 0))
    · refine .inr ⟨pinPre E none, by simp, pinPre E (some (.live readCell 0)), by simp, ?_, hpin⟩
      intro h
      have := congrArg Prod.fst h
      simp [pinPre, domAbsent, domCell] at this
    · left
      have hmap : mapEx (touchCheck E (World.genesis E o 145)) (keepTurn E o p).touches = .error (.stale p) := by
        simp [keepTurn, mapEx, touchCheck, World.entry, World.genesis, Trie.get_empty, req, hpin, bind, Except.bind]
      have hc : check E (World.genesis E o 145) (keepTurn E o p) = .error (.stale p) := by
        unfold check checkWith; rw [hmap]; rfl
      rw [hc, hw]; simp

/-- **`check_reads_kept`, binding**: when the two pin preimages are separated, the World differing
only at the kept cell checks the turn differently. -/
theorem check_reads_kept_sep (E : Env D) (o p : D)
    (hs : Separates E.hash [pinPre E none, pinPre E (some (.live readCell 0))]) :
    ∃ w w' t, ¬ CellFoot t (.cell p) ∧ CellRead t (.cell p) ∧
      (∀ s, s ≠ .cell p → w'.trie.get (trieSpec E) s = w.trie.get (trieSpec E) s) ∧
      check E w t = .ok [] ∧ check E w' t ≠ check E w t := by
  obtain ⟨w, w', t, h1, h2, h3, -, -, -, -, -, -, h10, h11⟩ := check_reads_kept E o p
  exact ⟨w, w', t, h1, h2, h3, h10, hs.elim h11⟩

/-- **Tooth: the rows half binds rows that differ** (`RowsAgree.read`'s instance): on canonical,
rows over a lawful `Env` whose held slots fit, writing a row at a slot the turn does not read (for a turn
with range reads, any key outside their prefixes and heads) changes no check, though the rows now
differ there. -/
theorem check_unread_row {E : Env D} {n : Nat} (hE : E.Lawful n) {w : World D} {t : Turn D}
    (hc : w.RowsCanon E) (hf : ∀ s, rowAt E w.rows s ≠ none → RowSlotFits s)
    {k : RowSlot D} {v : RowLeaf} (hk : ¬ RowRead E t k) (hnone : rowAt E w.rows k = none) :
    ({ w with rows := w.rows.insert (rowSpec E) k v } : World D).rows ≠ w.rows ∧
      check E { w with rows := w.rows.insert (rowSpec E) k v } t = check E w t := by
  refine ⟨fun h => ?_, check_local (w := w) (w' := { w with rows := w.rows.insert (rowSpec E) k v }) (t := t)
    ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl, rfl, .read hE hc (Trie.canon_insert (rowSpec E) k v hc) hf
      fun s hs => Trie.get_insert_ne _ _ _ fun e => hk (e ▸ hs)⟩⟩
  have e := congrArg (fun r => r.get (rowSpec E) k) h
  simp only [Trie.get_insert_self] at e
  unfold rowAt at hnone
  rw [hnone] at e
  cases e
