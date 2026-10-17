/-
# Kernel.Proofs.Weight — the budget bounds the World

A turn's charge includes `Turn.growth`, the most it can add to the World; what its touches do not
use of that (a retired cell's weight, a write's ops beyond what the cell grew) is credited back
(KERNEL-15). So storage is CONSERVED: over any admitted log, World storage plus log storage plus
the budget left equal where they started (`fold_conserves`), and with a genesis budget below a
bound the World's size is below it forever (`fold_world_weight`): HOST-14's `worldBytesMax` is the
genesis allowance. `admit_retire`: retiring gives back exactly the retired cells' weight.
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
    · simp only [except_bind_ok, pure, Except.pure, Except.ok.injEq] at h
      obtain ⟨_, _, _, _, h⟩ := h; exact h.symm
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

/-! ## What one turn adds, and what it gives back -/

section Turn
variable [Std.TransOrd D] [Std.LawfulEqOrd D]

omit [DecidableEq D] [Std.TransOrd D] [Std.LawfulEqOrd D] in
theorem live_get {w : World D} {c : D} {cell : Cell} (hc : w.live c = some cell) :
    w.cells[c]? = some (.live cell) := by
  unfold World.live at hc
  split at hc
  · rename_i hh; simp only [Option.some.injEq] at hc; rw [hh, hc]
  · simp at hc

omit [Std.TransOrd D] [Std.LawfulEqOrd D] in
/-- A touch that changes its cell replaces an existing entry, and the new entry plus what the
touch gives back is exactly the old entry plus the ops it was charged for. -/
theorem touchCheck_weight {E : Env D} {w : World D} {x : Touch D} {p : Post D}
    (h : touchCheck E w x = .ok (some p)) :
    p.cell = x.cell ∧ ∃ old, w.cells[x.cell]? = some old ∧
      p.entry.weight + p.freed = old.weight + x.act.opsWeight := by
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
          refine ⟨rfl, .live cell, live_get hc, ?_⟩
          have := postWrite_weight hp
          simp only [Entry.weight, Act.opsWeight]; omega
  | retire =>
      rw [ha] at h
      cases hc : w.live x.cell with
      | none => rw [hc] at h; simp at h
      | some cell =>
          rw [hc] at h
          simp only [except_bind_ok, pure, Except.pure, Except.ok.injEq, Option.some.injEq] at h
          obtain ⟨_, _, rfl⟩ := h
          exact ⟨rfl, .live cell, live_get hc, by simp [Entry.weight, Act.opsWeight]⟩

omit [Std.TransOrd D] [Std.LawfulEqOrd D] in
/-- A touch that changes nothing is a `keep`, and was charged for no ops. -/
theorem touchCheck_none {E : Env D} {w : World D} {x : Touch D}
    (h : touchCheck E w x = .ok none) : x.act = .keep := by
  unfold touchCheck at h
  simp only [except_bind_ok] at h
  obtain ⟨⟨⟩, _, h⟩ := h
  cases ha : x.act with
  | keep => rfl
  | write ops =>
      rw [ha] at h
      cases hc : w.live x.cell with
      | none => rw [hc] at h; simp at h
      | some cell =>
          rw [hc] at h
          simp only [except_bind_ok, pure, Except.pure] at h
          obtain ⟨_, _, h⟩ := h; simp at h
  | retire =>
      rw [ha] at h
      cases hc : w.live x.cell with
      | none => rw [hc] at h; simp at h
      | some cell =>
          rw [hc] at h
          simp only [except_bind_ok, pure, Except.pure] at h
          obtain ⟨_, _, h⟩ := h; simp at h

omit [Ord D] [DecidableEq D] [Std.TransOrd D] [Std.LawfulEqOrd D] in
theorem credit_cons (p : Post D) (l : List (Post D)) : credit (p :: l) = p.freed + credit l := by
  simp [credit]

theorem touches_weight {E : Env D} {w : World D} :
    ∀ (l : List (Touch D)) (raw : List (Option (Post D))) (m : Std.TreeMap D Entry compare),
      (l.map Touch.cell).Nodup → mapEx (touchCheck E w) l = .ok raw →
      (∀ x ∈ l, m[x.cell]? = w.cells[x.cell]?) →
      cellsWeight (insertAll m (raw.reduceOption.map Post.pair)) + credit raw.reduceOption =
        cellsWeight m + (l.map fun x => x.act.opsWeight).sum
  | [], raw, m, _, h, _ => by
      simp [mapEx] at h; subst h; simp [insertAll, List.reduceOption, credit]
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
                  have hk := touchCheck_none hx
                  simp only [List.reduceOption, List.filterMap_cons, id, List.map_cons,
                    List.sum_cons, hk, Act.opsWeight] at this ⊢
                  omega
              | some p =>
                  obtain ⟨hp1, old, hold, hw⟩ := touchCheck_weight hx
                  have hmx : m[p.cell]? = some old := by rw [hp1, hm x (by simp), hold]
                  have hins := cellsWeight_overwrite p.entry hmx
                  have hm'' : ∀ y ∈ rest, (m.insert p.cell p.entry)[y.cell]? = w.cells[y.cell]? := by
                    intro y hy
                    rw [Std.TreeMap.getElem?_insert]
                    have : compare p.cell y.cell ≠ .eq := by
                      intro he
                      apply hn.1
                      rw [← hp1, Std.LawfulEqCmp.eq_of_compare he]
                      exact List.mem_map_of_mem hy
                    simp [this, hm' y hy]
                  have := touches_weight rest raw' (m.insert p.cell p.entry) hn.2 hr hm''
                  simp only [List.reduceOption, List.filterMap_cons, id, List.map_cons,
                    List.sum_cons] at this ⊢
                  rw [credit_cons]
                  show cellsWeight (insertAll (m.insert p.cell p.entry) _) + _ = _
                  omega

omit [Std.TransOrd D] [Std.LawfulEqOrd D] in
/-- What a turn that only keeps and retires gives back: exactly the weight of each cell it
retires (KERNEL-15). -/
theorem credit_retires {E : Env D} {w : World D} :
    ∀ (l : List (Touch D)) (raw : List (Option (Post D))),
      mapEx (touchCheck E w) l = .ok raw → (∀ x ∈ l, x.act = .keep ∨ x.act = .retire) →
      credit raw.reduceOption =
        ((l.filter fun x => x.act == .retire).map fun x => ((w.live x.cell).map Cell.weight).getD 0).sum
  | [], raw, h, _ => by simp [mapEx] at h; subst h; simp [List.reduceOption, credit]
  | x :: rest, raw, h, ha => by
      unfold mapEx at h
      cases hx : touchCheck E w x with
      | error e => simp [hx] at h
      | ok r =>
          cases hr : mapEx (touchCheck E w) rest with
          | error e => simp [hx, hr] at h
          | ok raw' =>
              simp only [hx, hr, Except.ok.injEq] at h
              subst h
              have ih := credit_retires rest raw' hr (fun y hy => ha y (by simp [hy]))
              rcases ha x (by simp) with hk | hk
              · have : r = none := by
                  unfold touchCheck at hx
                  simp only [except_bind_ok, hk] at hx
                  obtain ⟨⟨⟩, _, hx⟩ := hx
                  simp [pure, Except.pure] at hx; exact hx.symm
                subst this
                simp [List.reduceOption, hk] at ih ⊢
                exact ih
              · unfold touchCheck at hx
                simp only [except_bind_ok, hk] at hx
                obtain ⟨⟨⟩, _, hx⟩ := hx
                cases hc : w.live x.cell with
                | none => rw [hc] at hx; simp at hx
                | some cell =>
                    rw [hc] at hx
                    simp only [except_bind_ok, pure, Except.pure, Except.ok.injEq] at hx
                    obtain ⟨_, _, rfl⟩ := hx
                    simp only [List.reduceOption, List.filterMap_cons, id, List.filter_cons, hk,
                      beq_self_eq_true, if_true, List.map_cons, List.sum_cons, hc, Option.map_some,
                      Option.getD_some] at ih ⊢
                    rw [credit_cons]
                    dsimp only
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

omit [DecidableEq D] in
/-- Fresh, distinct nullifiers grow the spent set by exactly their number. -/
theorem spendAll_size :
    ∀ (s : Std.TreeSet D compare) (ns : List D), ns.Nodup → (∀ n ∈ ns, s.contains n = false) →
      (spendAll s ns).size = s.size + ns.length
  | s, [], _, _ => by simp [spendAll]
  | s, n :: rest, hn, hf => by
      simp only [List.nodup_cons] at hn
      have hf' : ∀ m ∈ rest, (s.insert n).contains m = false := by
        intro m hm
        rw [Std.TreeSet.contains_insert]
        have : ¬ compare n m = .eq := by
          intro he; apply hn.1; rw [Std.LawfulEqCmp.eq_of_compare he]; exact hm
        simp [this, hf m (by simp [hm])]
      have ih := spendAll_size (s.insert n) rest hn.2 hf'
      have := Std.TreeSet.size_insert (t := s) (k := n)
      rw [hf n (by simp)] at this
      show (spendAll (s.insert n) rest).size = _
      simp only [List.length_cons] at ih ⊢; simp at this; omega

/-- **An admitted turn moves storage exactly.** The World grows by the turn's growth less what its
touches give back. -/
theorem admit_world_weight {E : Env D} {w w' : World D} {t : Turn D} {posts : List (Post D)}
    (hk : Checked E w t posts) (h : w' = commit E w t posts) :
    w'.weight + credit posts = w.weight + t.growth := by
  subst h
  obtain ⟨raw, hm, hposts⟩ := hk.touches
  have hshape := hk.shape
  unfold checkShape at hshape
  simp only [except_bind_ok] at hshape
  obtain ⟨⟨⟩, hnt, ⟨⟩, hnn, _⟩ := hshape
  have hcr := hk.creates
  unfold checkCreates at hcr
  simp only [except_bind_ok] at hcr
  obtain ⟨⟨⟩, hnb, ⟨⟩, hnbt, hfresh⟩ := hcr
  have nt := noDup_nodup hnt
  have nb := noDup_nodup hnb
  have nbt := noDup_nodup hnbt
  have nn := noDup_nodup hnn
  -- the touches
  have ht := touches_weight t.touches raw w.cells nt hm (fun _ _ => rfl)
  rw [← hposts] at ht
  -- the births
  have hids : (createdPairs E t).map Prod.fst = createdIds E t := by
    unfold createdPairs; exact List.map_fst_zip (by simp [createdIds])
  have hsnd : (createdPairs E t).map Prod.snd = t.creates := by
    unfold createdPairs; exact List.map_snd_zip (by simp [createdIds])
  have hpk : ∀ p ∈ posts, p.cell ∈ t.touches.map Touch.cell := by
    intro p hp
    obtain ⟨x, hx, he, _⟩ := posts_touched hk p hp
    rw [he]; exact List.mem_map_of_mem hx
  have hfr : ∀ p ∈ createdPairs E t, (insertAll w.cells (posts.map Post.pair))[p.1]? = none := by
    intro p hp
    have hb : p.1 ∈ createdIds E t := by rw [← hids]; exact List.mem_map_of_mem hp
    have hnot : p.1 ∉ (posts.map Post.pair).map Prod.fst := by
      intro hm'
      rw [List.map_map] at hm'
      obtain ⟨q, hq, hqe⟩ := List.mem_map.mp hm'
      have := hpk q hq
      rw [show (Prod.fst ∘ Post.pair) q = q.cell from rfl] at hqe
      rw [hqe] at this
      exact (List.nodup_append.mp nbt).2.2 _ this _ hb rfl
    rw [insertAll_get_of_not_mem hnot]
    have := (forEx_ok.mp hfresh) p.1 hb
    rw [req_ok] at this
    cases hh : w.cells[p.1]? with
    | none => rfl
    | some e => rw [Std.TreeMap.contains_eq_isSome_getElem?, hh] at this; simp at this
  have hb := born_weight (createdPairs E t) (insertAll w.cells (posts.map Post.pair))
    (by rw [hids]; exact nb) hfr
  have hbsum : ((createdPairs E t).map fun p => digestWeight + p.2.weight).sum =
      (t.creates.map fun c => digestWeight + c.weight).sum := by
    rw [← hsnd, List.map_map]; rfl
  -- the journal entry is new, and so is every nullifier
  have hj : (w.journal.insert t.txId (w.height + 1, turnDigest E t)).size = w.journal.size + 1 := by
    have hjr := hk.journal
    unfold checkJournal at hjr
    have hnone : w.journal[t.txId]? = none := by
      cases hh : w.journal[t.txId]? with
      | none => rfl
      | some v => rw [hh] at hjr; simp at hjr
    rw [Std.TreeMap.size_insert, Std.TreeMap.contains_eq_isSome_getElem?, hnone]; simp
  have hs : (spendAll w.spent t.nullifiers).size = w.spent.size + t.nullifiers.length := by
    apply spendAll_size _ _ nn
    intro n hn
    have := (forEx_ok.mp hk.nullifiers) n hn
    rw [req_ok] at this
    simpa using this
  unfold World.weight commit Turn.growth
  dsimp only
  have hc : cellsWeight (insertAll (insertAll w.cells (posts.map Post.pair)) (bornEntries E t)) +
      credit posts = cellsWeight w.cells + (t.touches.map fun x => x.act.opsWeight).sum +
        (t.creates.map fun c => digestWeight + c.weight).sum := by
    unfold bornEntries; rw [hb, ← hbsum]; omega
  rw [hj, hs, Nat.mul_add, Nat.mul_add, Nat.mul_one]
  omega

/-- **Storage is conserved.** An admitted turn's World storage, plus its log record, plus the
budget left, is exactly the World storage and budget before it: nothing is created or lost, a
retirement or a shrinking write hands its bytes back to the budget. -/
theorem admit_conserves {E : Env D} {w w' : World D} {t : Turn D}
    (h : World.admit E w t = .ok w') :
    w'.weight + t.logWeight + w'.allowance = w.weight + w.allowance := by
  obtain ⟨hc, posts, hk, _, hal⟩ := admit_charge h
  obtain ⟨posts', hk', hw'⟩ := admit_ok h
  have : posts' = posts := by
    obtain ⟨r1, h1, e1⟩ := hk.touches
    obtain ⟨r2, h2, e2⟩ := hk'.touches
    rw [h1] at h2; cases h2; rw [e1, e2]
  subst this
  have hw := admit_world_weight hk' hw'
  unfold Turn.weight at hc
  omega

omit [Std.TransOrd D] [Std.LawfulEqOrd D] in
/-- **Credit on retirement** (KERNEL-15). A turn that only keeps and retires cells leaves the
budget at what it was, plus the weight of every cell it retired, less its charge. -/
theorem admit_retire {E : Env D} {w w' : World D} {t : Turn D}
    (h : World.admit E w t = .ok w') (ha : ∀ x ∈ t.touches, x.act = .keep ∨ x.act = .retire) :
    w'.allowance + t.charge = w.allowance +
      ((t.touches.filter fun x => x.act == .retire).map fun x =>
        ((w.live x.cell).map Cell.weight).getD 0).sum := by
  obtain ⟨_, posts, hk, _, hal⟩ := admit_charge h
  obtain ⟨raw, hm, rfl⟩ := hk.touches
  rw [hal, credit_retires t.touches raw hm ha]

/-- **The budget bounds the World, exactly.** Over any admitted log, the World's storage plus the
log records' storage plus the budget left equal the World's storage and budget at the start. -/
theorem fold_conserves {E : Env D} :
    ∀ {w w' : World D} {l : List (Turn D)}, World.fold E w l = .ok w' →
      w'.weight + (l.map Turn.logWeight).sum + w'.allowance = w.weight + w.allowance
  | w, w', [], h => by simp [World.fold] at h; subst h; simp
  | w, w', t :: rest, h => by
      obtain ⟨w₁, h₁, h₂⟩ := fold_cons_ok.mp h
      have ih := fold_conserves h₂
      have hw := admit_conserves h₁
      simp only [List.map_cons, List.sum_cons]
      omega

/-- HOST-14's `worldBytesMax`: a World folded from `w` never holds more than `w`'s storage plus
its budget, whatever it admits and retires (credit never lets it exceed the genesis bound). -/
theorem fold_world_weight {E : Env D} {w w' : World D} {l : List (Turn D)}
    (h : World.fold E w l = .ok w') : w'.weight ≤ w.weight + w.allowance := by
  have := fold_conserves h; omega

end World

end Nanodregg.Kernel
