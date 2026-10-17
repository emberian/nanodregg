/-
# Kernel.Proofs.Weight — the budget bounds the World

A turn's charge includes `Turn.growth`, the most it can add to the World. `admit_world_weight`:
an admitted turn adds at most that, so over any admitted log the World's storage plus the budget
left never exceeds where they started (`fold_world_weight`). With a genesis budget below a bound,
the World's size is below it forever: HOST-14's `worldBytesMax` is the genesis allowance.
-/
import Kernel.Proofs.Frame

namespace Nanodregg.Kernel

/-! ## A write grows a cell by at most its ops -/

theorem slots_weight_set (k : Nat) (v : ByteArray) :
    ∀ s : Slots, Slots.weight (s.set k v) ≤ Slots.weight s + (8 + v.size)
  | [] => by simp [Slots.set, Slots.weight]
  | (k', v') :: rest => by
      have ih := slots_weight_set k v rest
      simp only [Slots.weight, List.map_cons, List.sum_cons] at ih ⊢
      unfold Slots.set
      split
      · simp only [List.map_cons, List.sum_cons]; omega
      · split
        · simp only [List.map_cons, List.sum_cons]; omega
        · simp only [List.map_cons, List.sum_cons] at ih ⊢; omega

theorem slots_weight_erase (k : Nat) :
    ∀ s : Slots, Slots.weight (s.erase k) ≤ Slots.weight s
  | [] => by simp [Slots.erase]
  | (k', v') :: rest => by
      have ih := slots_weight_erase k rest
      simp only [Slots.weight, List.map_cons, List.sum_cons] at ih ⊢
      unfold Slots.erase
      split
      · omega
      · simp only [List.map_cons, List.sum_cons]; omega

theorem slots_weight_applyOps :
    ∀ (ops : List Op) (s : Slots),
      Slots.weight (applyOps s ops) ≤ Slots.weight s + (ops.map Op.weight).sum
  | [], s => by simp [applyOps]
  | o :: rest, s => by
      have ih := slots_weight_applyOps rest (applyOp s o)
      have step : Slots.weight (applyOp s o) ≤ Slots.weight s + o.weight := by
        cases o with
        | set k v => exact slots_weight_set k v s
        | erase k => have := slots_weight_erase k s; simp only [applyOp, Op.weight]; omega
      simp only [applyOps, List.foldl_cons, List.map_cons, List.sum_cons] at ih ⊢
      omega

variable {D : Type} [Ord D] [DecidableEq D]

omit [Ord D] [DecidableEq D] in
theorem postWrite_weight {c : D} {cell post : Cell} {ops : List Op}
    (h : postWrite c cell ops = .ok post) : post.weight ≤ cell.weight + (ops.map Op.weight).sum := by
  have key : post = { cell with slots := applyOps cell.slots ops } := by
    unfold postWrite at h
    split at h
    · simp at h
    · simp only [except_bind_ok, pure, Except.pure, Except.ok.injEq] at h
      obtain ⟨_, _, _, _, h⟩ := h; exact h.symm
    · simp only [except_bind_ok, pure, Except.pure, Except.ok.injEq] at h
      obtain ⟨_, _, h⟩ := h; exact h.symm
  subst key
  have := slots_weight_applyOps ops cell.slots
  simp only [Cell.weight]; omega

/-! ## The cell map's weight under one insertion -/

section Cells
variable [Std.TransOrd D] [Std.LawfulEqOrd D]

theorem cellsWeight_insert (m : Std.TreeMap D Entry compare) (k : D) (e : Entry) :
    cellsWeight (m.insert k e) = digestWeight + e.weight +
      ((m.toList.filter (¬k == ·.1)).map fun p => digestWeight + p.2.weight).sum := by
  unfold cellsWeight
  rw [(Std.TreeMap.toList_insert_perm.map (fun p : D × Entry => digestWeight + p.2.weight)).sum_nat]
  simp [List.sum_cons]

/-- Overwriting an entry: the map's weight moves by the difference. -/
theorem cellsWeight_overwrite {m : Std.TreeMap D Entry compare} {k : D} {old : Entry} (e : Entry)
    (h : m[k]? = some old) : cellsWeight (m.insert k e) + old.weight = cellsWeight m + e.weight := by
  have heq : (m.insert k old).Equiv m := by
    apply Std.TreeMap.Equiv.of_forall_constGet?_eq
    intro k'
    rw [Std.TreeMap.getElem?_insert]
    split
    · rename_i hc; rw [← Std.LawfulEqCmp.eq_of_compare hc, h]
    · rfl
  have hm : cellsWeight (m.insert k old) = cellsWeight m := by
    unfold cellsWeight
    exact ((Std.TreeMap.equiv_iff_toList_perm.mp heq).map _).sum_nat
  have h1 := cellsWeight_insert m k e
  have h2 := cellsWeight_insert m k old
  omega

/-- A fresh entry: the map's weight grows by exactly the entry with its id. -/
theorem cellsWeight_fresh {m : Std.TreeMap D Entry compare} {k : D} (e : Entry)
    (h : m[k]? = none) : cellsWeight (m.insert k e) = cellsWeight m + (digestWeight + e.weight) := by
  rw [cellsWeight_insert]
  have : m.toList.filter (¬k == ·.1) = m.toList := by
    apply List.filter_eq_self.mpr
    intro p hp
    have hg := Std.TreeMap.mem_toList_iff_getElem?_eq_some.mp hp
    simp only [decide_eq_true_eq, beq_iff_eq]
    intro hk
    rw [← hk, h] at hg
    simp at hg
  rw [this]; unfold cellsWeight; omega

end Cells

/-! ## What one turn adds -/

section Turn
variable [Std.TransOrd D] [Std.LawfulEqOrd D]

omit [Std.TransOrd D] [Std.LawfulEqOrd D] in
/-- A touch that changes its cell replaces an existing entry by one at most its ops heavier. -/
theorem touchCheck_weight {E : Env D} {w : World D} {x : Touch D} {p : D × Entry}
    (h : touchCheck E w x = .ok (some p)) :
    p.1 = x.cell ∧ ∃ old, w.cells[x.cell]? = some old ∧ p.2.weight ≤ old.weight + x.act.opsWeight := by
  have hlive : ∀ cell, w.live x.cell = some cell → w.cells[x.cell]? = some (.live cell) := by
    intro cell hc
    unfold World.live at hc
    split at hc
    · rename_i hh; simp only [Option.some.injEq] at hc; rw [hh, hc]
    · simp at hc
  unfold touchCheck at h
  simp only [except_bind_ok] at h
  obtain ⟨⟨⟩, _, h⟩ := h
  cases ha : x.act with
  | keep => rw [ha] at h; simp [pure, Except.pure] at h
  | write ops =>
      rw [ha] at h
      cases hc : w.live x.cell with
      | none => rw [hc] at h; simp at h
      | some cell =>
          rw [hc] at h
          simp only [except_bind_ok, pure, Except.pure, Except.ok.injEq, Option.some.injEq] at h
          obtain ⟨post, hp, rfl⟩ := h
          refine ⟨rfl, .live cell, hlive cell hc, ?_⟩
          simpa [Entry.weight, Act.opsWeight] using postWrite_weight hp
  | retire =>
      rw [ha] at h
      cases hc : w.live x.cell with
      | none => rw [hc] at h; simp at h
      | some cell =>
          rw [hc] at h
          simp only [except_bind_ok, pure, Except.pure, Except.ok.injEq, Option.some.injEq] at h
          obtain ⟨_, _, rfl⟩ := h
          exact ⟨rfl, .live cell, hlive cell hc, by simp [Entry.weight]⟩

theorem touches_weight {E : Env D} {w : World D} :
    ∀ (l : List (Touch D)) (raw : List (Option (D × Entry))) (m : Std.TreeMap D Entry compare),
      (l.map Touch.cell).Nodup → mapEx (touchCheck E w) l = .ok raw →
      (∀ x ∈ l, m[x.cell]? = w.cells[x.cell]?) →
      cellsWeight (insertAll m raw.reduceOption) ≤
        cellsWeight m + (l.map fun x => x.act.opsWeight).sum
  | [], raw, m, _, h, _ => by
      simp [mapEx] at h; subst h; simp [insertAll, List.reduceOption]
  | x :: rest, raw, m, hn, h, hm => by
      unfold mapEx at h
      cases hx : touchCheck E w x with
      | error e => simp [hx] at h
      | ok r =>
          cases hr : mapEx (touchCheck E w) rest with
          | error e => simp [hx, hr] at h
          | ok raw' =>
              simp only [hx, hr, Except.ok.injEq] at h
              subst h
              simp only [List.map_cons, List.nodup_cons] at hn
              have hm' : ∀ y ∈ rest, m[y.cell]? = w.cells[y.cell]? := fun y hy => hm y (by simp [hy])
              cases r with
              | none =>
                  have := touches_weight rest raw' m hn.2 hr hm'
                  simp only [List.reduceOption, List.filterMap_cons, id, List.map_cons,
                    List.sum_cons] at this ⊢
                  omega
              | some p =>
                  obtain ⟨hp1, old, hold, hw⟩ := touchCheck_weight hx
                  have hmx : m[p.1]? = some old := by rw [hp1, hm x (by simp), hold]
                  have hins := cellsWeight_overwrite p.2 hmx
                  have hm'' : ∀ y ∈ rest, (m.insert p.1 p.2)[y.cell]? = w.cells[y.cell]? := by
                    intro y hy
                    rw [Std.TreeMap.getElem?_insert]
                    have : compare p.1 y.cell ≠ .eq := by
                      intro he
                      apply hn.1
                      rw [← hp1, Std.LawfulEqCmp.eq_of_compare he]
                      exact List.mem_map_of_mem hy
                    simp [this, hm' y hy]
                  have := touches_weight rest raw' (m.insert p.1 p.2) hn.2 hr hm''
                  simp only [List.reduceOption, List.filterMap_cons, id, List.map_cons,
                    List.sum_cons] at this ⊢
                  show cellsWeight (insertAll (m.insert p.1 p.2) _) ≤ _
                  omega

end Turn

section World
variable [Std.TransOrd D] [Std.LawfulEqOrd D]

omit [Ord D] [Std.TransOrd D] [Std.LawfulEqOrd D] [DecidableEq D] in
theorem noDup_nodup {α : Type} [Ord α] [Std.TransOrd α] [Std.LawfulEqOrd α] {l : List α}
    {e : α → Reject D} (h : noDup l e = .ok ()) : l.Nodup := by
  unfold noDup at h
  split at h
  · rename_i hf; exact firstDup_none hf
  · simp at h

theorem born_weight :
    ∀ (ps : List (D × Cell)) (m : Std.TreeMap D Entry compare), (ps.map Prod.fst).Nodup →
      (∀ p ∈ ps, m[p.1]? = none) →
      cellsWeight (insertAll m (ps.map fun p => (p.1, Entry.live p.2))) =
        cellsWeight m + (ps.map fun p => digestWeight + p.2.weight).sum
  | [], m, _, _ => by simp [insertAll]
  | p :: rest, m, hn, hf => by
      simp only [List.map_cons, List.nodup_cons] at hn
      have hf' : ∀ q ∈ rest, (m.insert p.1 (.live p.2))[q.1]? = none := by
        intro q hq
        rw [Std.TreeMap.getElem?_insert]
        have : compare p.1 q.1 ≠ .eq := by
          intro he
          apply hn.1
          rw [Std.LawfulEqCmp.eq_of_compare he]
          exact List.mem_map_of_mem hq
        simp [this, hf q (by simp [hq])]
      have ih := born_weight rest (m.insert p.1 (.live p.2)) hn.2 hf'
      have h1 := cellsWeight_fresh (Entry.live p.2) (hf p (by simp))
      simp only [List.map_cons, List.sum_cons]
      show cellsWeight (insertAll (m.insert p.1 (.live p.2)) _) = _
      rw [ih, h1]; simp [Entry.weight]; omega

omit [Std.LawfulEqOrd D] [DecidableEq D] in
theorem spendAll_size :
    ∀ (s : Std.TreeSet D compare) (ns : List D), (spendAll s ns).size ≤ s.size + ns.length
  | s, [] => by simp [spendAll]
  | s, n :: rest => by
      have ih := spendAll_size (s.insert n) rest
      have := Std.TreeSet.size_insert_le (t := s) (k := n)
      show (spendAll (s.insert n) rest).size ≤ _
      simp only [List.length_cons]; omega

/-- **An admitted turn adds at most its growth to the World.** -/
theorem admit_world_weight {E : Env D} {w w' : World D} {t : Turn D}
    (h : World.admit E w t = .ok w') : w'.weight ≤ w.weight + t.growth := by
  obtain ⟨posts, hk, rfl⟩ := admit_ok h
  obtain ⟨raw, hm, hposts⟩ := hk.touches
  -- the touches' cells are distinct, and the born ids are distinct, fresh and untouched
  have hshape := hk.shape
  unfold checkShape at hshape
  simp only [except_bind_ok] at hshape
  obtain ⟨⟨⟩, hnt, _⟩ := hshape
  have hcr := hk.creates
  unfold checkCreates at hcr
  simp only [except_bind_ok] at hcr
  obtain ⟨⟨⟩, hnb, ⟨⟩, hnbt, hfresh⟩ := hcr
  have nt := noDup_nodup hnt
  have nb := noDup_nodup hnb
  have nbt := noDup_nodup hnbt
  -- the touches
  have ht := touches_weight t.touches raw w.cells nt hm (fun _ _ => rfl)
  rw [← hposts] at ht
  -- the births
  have hids : (createdPairs E t).map Prod.fst = createdIds E t := by
    unfold createdPairs; exact List.map_fst_zip (by simp [createdIds])
  have hsnd : (createdPairs E t).map Prod.snd = t.creates := by
    unfold createdPairs; exact List.map_snd_zip (by simp [createdIds])
  have hpk : ∀ p ∈ posts, p.1 ∈ t.touches.map Touch.cell := by
    intro p hp
    obtain ⟨x, hx, he, _⟩ := posts_touched hk p hp
    rw [he]; exact List.mem_map_of_mem hx
  have hfr : ∀ p ∈ createdPairs E t, (insertAll w.cells posts)[p.1]? = none := by
    intro p hp
    have hb : p.1 ∈ createdIds E t := by rw [← hids]; exact List.mem_map_of_mem hp
    have hnot : p.1 ∉ posts.map Prod.fst := by
      intro hm'
      obtain ⟨q, hq, hqe⟩ := List.mem_map.mp hm'
      have := hpk q hq
      rw [hqe] at this
      exact (List.nodup_append.mp nbt).2.2 _ this _ hb rfl
    rw [insertAll_get_of_not_mem hnot]
    have := (forEx_ok.mp hfresh) p.1 hb
    rw [req_ok] at this
    cases hh : w.cells[p.1]? with
    | none => rfl
    | some e => rw [Std.TreeMap.contains_eq_isSome_getElem?, hh] at this; simp at this
  have hb := born_weight (createdPairs E t) (insertAll w.cells posts) (by rw [hids]; exact nb) hfr
  have hbsum : ((createdPairs E t).map fun p => digestWeight + p.2.weight).sum =
      (t.creates.map fun c => digestWeight + c.weight).sum := by
    rw [← hsnd, List.map_map]; rfl
  -- journal and spent
  have hj := Std.TreeMap.size_insert_le (t := w.journal) (k := t.txId) (v := (w.height + 1, turnDigest E t))
  have hs := spendAll_size w.spent t.nullifiers
  unfold World.weight commit Turn.growth
  dsimp only
  have hc : cellsWeight (insertAll (insertAll w.cells posts) (bornEntries E t)) ≤
      cellsWeight w.cells + (t.touches.map fun x => x.act.opsWeight).sum +
        (t.creates.map fun c => digestWeight + c.weight).sum := by
    unfold bornEntries; rw [hb, ← hbsum]; omega
  have : digestWeight * (spendAll w.spent t.nullifiers).size ≤
      digestWeight * w.spent.size + digestWeight * t.nullifiers.length := by
    rw [← Nat.mul_add]; exact Nat.mul_le_mul_left _ hs
  have : journalWeight * (w.journal.insert t.txId (w.height + 1, turnDigest E t)).size ≤
      journalWeight * w.journal.size + journalWeight := by
    have := Nat.mul_le_mul_left journalWeight hj; rw [Nat.mul_add, Nat.mul_one] at this; exact this
  omega

/-- **The budget bounds the World.** Over any admitted log, the World's storage plus the log
records' storage plus the budget left never exceed the World's storage and budget at the start:
a World folded from a genesis with budget `A` never holds more than its genesis storage plus `A`. -/
theorem fold_world_weight {E : Env D} :
    ∀ {w w' : World D} {l : List (Turn D)}, World.fold E w l = .ok w' →
      w'.weight + (l.map Turn.logWeight).sum + w'.allowance ≤ w.weight + w.allowance
  | w, w', [], h => by simp [World.fold] at h; subst h; simp
  | w, w', t :: rest, h => by
      obtain ⟨w₁, h₁, h₂⟩ := fold_cons_ok.mp h
      have ih := fold_world_weight h₂
      have hw := admit_world_weight h₁
      obtain ⟨hc, _, hal⟩ := admit_charge h₁
      unfold Turn.weight at hc
      simp only [List.map_cons, List.sum_cons]
      omega

end World

end Nanodregg.Kernel
