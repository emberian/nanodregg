/-
# Kernel.Proofs.Value — value is conserved by `World.admit` itself (LEDGER-2)

Every theorem here is about `World.admit` (and `World.fold`), for ANY turn it admits: a turn a
receiver derived, a package posted, or a forged log carries. So no receiver needs a conservation
proof of its own, and a buggy one cannot mint.

* `admit_value`: every denomination's balance sum is unchanged (an EQUALITY, KERNEL-19's style);
  `fold_value` over a log.
* `admit_floors`: every denomination's floor sum is unchanged, unless the turn bears it.
* `admit_floorOk`: every live value cell decodes and is within its floor, after every turn.
* `outstanding_le_floors`: on such a World, what is outstanding (the positive balances) is at most
  the floor sum plus the balance sum, so at most the floor sum when value sums to 0.
* `admit_birth`: a denomination's floor sum is 0 before the turn that bears it (given the digest's
  bytes injective), and `fold_floors_held`: once the World holds its well's id, no log moves it.
  So its floor sum is SET at birth and fixed forever: the issuance cap is a theorem of the
  kernel, not a promise of the issuing receiver.
* `cellsSum_noValue`, `floorOk_noValue`: a World with no value cells (a genesis) sums to 0 and is
  within its floors, so every World folded from one satisfies the premises above.

Conservation is not ownership: the kernel judges WHAT a turn does to value, never WHO may do it
(a forged log that moves A's balance to B is conserved and folds). Authority is the receivers'
(`Kernel.Proofs.Ledger.transfer_authorized`), and the audit's re-derivation is what refuses a
forged log (`eventMismatch`).
-/
import Kernel.Proofs.Weight
import Kernel.Proofs.Rooted

namespace Nanodregg.Kernel

/-! ## Flow arithmetic -/

/-- `g` reads a flow's balance or its floor: negation and merging act on it as on a number. -/
structure Linear (g : Flow → Int) : Prop where
  neg : ∀ f, g f.neg = - g f
  merge : ∀ a f : Flow,
    g { a with balance := a.balance + f.balance, floor := a.floor + f.floor } = g a + g f

theorem linear_balance : Linear Flow.balance := ⟨fun _ => rfl, fun _ _ => rfl⟩
theorem linear_floor : Linear Flow.floor := ⟨fun _ => rfl, fun _ _ => rfl⟩

theorem sumBy_nil (g : Flow → Int) (d : ByteArray) : sumBy g d [] = 0 := rfl

theorem sumBy_cons (g : Flow → Int) (d : ByteArray) (f : Flow) (fs : List Flow) :
    sumBy g d (f :: fs) = (if f.denom = d then g f else 0) + sumBy g d fs := by
  simp [sumBy]

theorem sumBy_append (g : Flow → Int) (d : ByteArray) (a b : List Flow) :
    sumBy g d (a ++ b) = sumBy g d a + sumBy g d b := by
  simp [sumBy, List.sum_append]

theorem sumBy_flatMap {α : Type} (g : Flow → Int) (d : ByteArray) (h : α → List Flow) :
    ∀ l : List α, sumBy g d (l.flatMap h) = (l.map fun a => sumBy g d (h a)).sum
  | [] => rfl
  | a :: rest => by
      rw [List.flatMap_cons, sumBy_append, sumBy_flatMap g d h rest]
      simp

/-- Flows whose every entry of denomination `d` reads 0 sum to 0 there. -/
theorem sumBy_zero (g : Flow → Int) (d : ByteArray) :
    ∀ fs : List Flow, (∀ a ∈ fs, a.denom = d → g a = 0) → sumBy g d fs = 0
  | [], _ => rfl
  | a :: rest, h => by
      rw [sumBy_cons, sumBy_zero g d rest (fun b hb => h b (by simp [hb]))]
      by_cases ha : a.denom = d
      · simp [ha, h a (by simp) ha]
      · simp [ha]

/-- A change from `pre` to `post` moves exactly the post-value less the pre-value. -/
theorem sumBy_flowsOf {g : Flow → Int} (hg : Linear g) (d : ByteArray) (pre post : Option Cell) :
    sumBy g d (flowsOf pre post) = sumBy g d (flowsOf none post) - sumBy g d (flowsOf none pre) := by
  unfold flowsOf
  rw [sumBy_append, sumBy_append, sumBy_append]
  cases hp : pre.bind Value.ofCell with
  | none => simp [sumBy]
  | some v =>
      simp only [Option.bind_none, Option.map_none, Option.toList_none, Option.map_some,
        Option.toList_some]
      simp only [sumBy, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hg.neg]
      have : v.flow.neg.denom = v.flow.denom := rfl
      rw [this]
      split <;> omega

/-- Adding a flow into the association list adds it to its denomination's sum. -/
theorem sumBy_addFlow {g : Flow → Int} (hg : Linear g) (d : ByteArray) (f : Flow) :
    ∀ acc : List Flow, sumBy g d (addFlow acc f) = sumBy g d acc + sumBy g d [f]
  | [] => by simp [addFlow, sumBy]
  | a :: rest => by
      unfold addFlow
      split
      · rename_i he
        rw [sumBy_cons, sumBy_cons, sumBy_cons, sumBy_nil, hg.merge]
        show (if a.denom = d then g a + g f else 0) + _ = _
        by_cases had : a.denom = d
        · have hfd : f.denom = d := he ▸ had
          simp only [had, hfd, if_true]; omega
        · have hfd : ¬ f.denom = d := fun h => had (he.trans h)
          simp only [had, hfd, if_false]; omega
      · rw [sumBy_cons g d a (addFlow rest f), sumBy_addFlow hg d f rest, sumBy_cons g d a rest]
        omega

theorem accumulateFrom_sum {g : Flow → Int} (hg : Linear g) (d : ByteArray) :
    ∀ (fs acc0 acc : List Flow), accumulateFrom acc0 fs = some acc →
      sumBy g d acc = sumBy g d acc0 + sumBy g d fs
  | [], acc0, acc, h => by
      simp only [accumulateFrom, Option.some.injEq] at h
      subst h; simp [sumBy]
  | f :: fs, acc0, acc, h => by
      simp only [accumulateFrom] at h
      split at h
      · rw [accumulateFrom_sum hg d fs _ acc h, sumBy_addFlow hg]
        simp only [sumBy_cons, sumBy_nil]; omega
      · simp at h

/-- The accumulated sums are the flows' sums, denomination by denomination. -/
theorem accumulate_sum {g : Flow → Int} (hg : Linear g) (d : ByteArray) {fs acc : List Flow}
    (h : accumulate fs = some acc) : sumBy g d acc = sumBy g d fs := by
  have := accumulateFrom_sum hg d fs [] acc h
  rw [this, sumBy_nil]; omega

/-! ## What `checkValue` guarantees -/

variable {D : Type} [Ord D] [DecidableEq D]

omit [Ord D] [DecidableEq D] in
/-- A turn that passes `checkValue` bears only value cells that decode within their floors, and
moves no denomination's balance sum, nor the floor sum of any denomination it does not bear. -/
theorem checkValue_ok {E : Env D} {t : Turn D} {posts : List (Post D)}
    (h : checkValue E t posts = .ok ()) :
    (∀ p ∈ createdPairs E t, checkValueCell p.1 p.2 = .ok ()) ∧
      (∀ d, sumBy Flow.balance d (valueFlows E t posts) = 0) ∧
      (∀ d, d ∉ (createdIds E t).map E.bytes → sumBy Flow.floor d (valueFlows E t posts) = 0) := by
  unfold checkValue at h
  simp only [except_bind_ok] at h
  obtain ⟨⟨⟩, hb, h⟩ := h
  refine ⟨forEx_ok.mp hb, ?_⟩
  split at h
  · simp at h
  · rename_i acc hacc
    have hall := forEx_ok.mp h
    have each : ∀ a ∈ acc, a.balance = 0 ∧ (a.floor = 0 ∨ a.denom ∈ (createdIds E t).map E.bytes) := by
      intro a ha
      have := hall a ha
      simp only [except_bind_ok] at this
      obtain ⟨⟨⟩, h1, h2⟩ := this
      rw [req_ok, decide_eq_true_eq] at h1
      rw [req_ok, Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true] at h2
      refine ⟨h1, h2.imp id fun ⟨b, hb, he⟩ => ?_⟩
      rw [← of_decide_eq_true he]; exact hb
    refine ⟨fun d => ?_, fun d hd => ?_⟩
    · rw [← accumulate_sum linear_balance d hacc]
      exact sumBy_zero _ d acc fun a ha _ => (each a ha).1
    · rw [← accumulate_sum linear_floor d hacc]
      refine sumBy_zero _ d acc fun a ha had => ?_
      rcases (each a ha).2 with h0 | hm
      · exact h0
      · exact absurd (had ▸ hm) hd

/-! ## Sums over the cell map -/

section Cells
variable [Std.TransOrd D] [Std.LawfulEqOrd D]

theorem perm_sum_int {l₁ l₂ : List Int} (h : l₁.Perm l₂) : l₁.sum = l₂.sum := by
  induction h with
  | nil => rfl
  | cons x _ ih => simp [List.sum_cons, ih]
  | swap x y l => simp [List.sum_cons]; omega
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem cellsSum_insert (f : Entry → Int) (m : Std.TreeMap D Entry compare) (k : D) (e : Entry) :
    cellsSum f (m.insert k e) = f e + ((m.toList.filter (¬k == ·.1)).map fun p => f p.2).sum := by
  unfold cellsSum
  rw [perm_sum_int (Std.TreeMap.toList_insert_perm.map (fun p : D × Entry => f p.2))]
  simp [List.sum_cons]

/-- Overwriting an entry moves the sum by the difference. -/
theorem cellsSum_overwrite (f : Entry → Int) {m : Std.TreeMap D Entry compare} {k : D} {old : Entry}
    (e : Entry) (h : m[k]? = some old) : cellsSum f (m.insert k e) = cellsSum f m - f old + f e := by
  have heq : (m.insert k old).Equiv m := by
    apply Std.TreeMap.Equiv.of_forall_constGet?_eq
    intro k'
    rw [Std.TreeMap.getElem?_insert]
    split
    · rename_i hc; rw [← Std.LawfulEqCmp.eq_of_compare hc, h]
    · rfl
  have hm : cellsSum f (m.insert k old) = cellsSum f m := by
    unfold cellsSum
    exact perm_sum_int ((Std.TreeMap.equiv_iff_toList_perm.mp heq).map _)
  have h1 := cellsSum_insert f m k e
  have h2 := cellsSum_insert f m k old
  omega

/-- A fresh entry adds exactly its own contribution. -/
theorem cellsSum_fresh (f : Entry → Int) {m : Std.TreeMap D Entry compare} {k : D} (e : Entry)
    (h : m[k]? = none) : cellsSum f (m.insert k e) = cellsSum f m + f e := by
  rw [cellsSum_insert]
  have : m.toList.filter (¬k == ·.1) = m.toList := by
    apply List.filter_eq_self.mpr
    intro p hp
    have hg := Std.TreeMap.mem_toList_iff_getElem?_eq_some.mp hp
    simp only [decide_eq_true_eq, beq_iff_eq]
    intro hk
    rw [← hk, h] at hg
    simp at hg
  rw [this]; unfold cellsSum; omega

end Cells

/-! ## What one admitted turn does to the sums -/

section Turn
variable [Std.TransOrd D] [Std.LawfulEqOrd D]

omit [Std.TransOrd D] [Std.LawfulEqOrd D] in
/-- A touch that changes its cell replaces a live cell, and its flows are that change. -/
theorem touchCheck_flows {E : Env D} {w : World D} {x : Touch D} {p : Post D}
    (h : touchCheck E w x = .ok (some p)) :
    p.cell = x.cell ∧ ∃ cell, w.cells[x.cell]? = some (.live cell) ∧
      p.flows = flowsOf (some cell) p.entry.cell? := by
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
          obtain ⟨post, _, rfl⟩ := h
          exact ⟨rfl, cell, live_get hc, rfl⟩
  | retire =>
      rw [ha] at h
      cases hc : w.live x.cell with
      | none => rw [hc] at h; simp at h
      | some cell =>
          rw [hc] at h
          simp only [except_bind_ok, pure, Except.pure, Except.ok.injEq, Option.some.injEq] at h
          obtain ⟨_, _, rfl⟩ := h
          exact ⟨rfl, cell, live_get hc, rfl⟩

/-- The touches move each sum by exactly their flows. -/
theorem touches_sum {E : Env D} {w : World D} {g : Flow → Int} (hg : Linear g) (d : ByteArray) :
    ∀ (l : List (Touch D)) (raw : List (Option (Post D))) (m : Std.TreeMap D Entry compare),
      (l.map Touch.cell).Nodup → mapEx (touchCheck E w) l = .ok raw →
      (∀ x ∈ l, m[x.cell]? = w.cells[x.cell]?) →
      cellsSum (entrySum g d) (insertAll m (raw.reduceOption.map Post.pair)) =
        cellsSum (entrySum g d) m + sumBy g d (raw.reduceOption.flatMap Post.flows)
  | [], raw, m, _, h, _ => by
      simp [mapEx] at h; subst h; simp [insertAll, List.reduceOption, sumBy]
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
                  have := touches_sum hg d rest raw' m hn.2 hr hm'
                  simpa [List.reduceOption, List.filterMap_cons] using this
              | some p =>
                  obtain ⟨hp1, cell, hold, hfl⟩ := touchCheck_flows hx
                  have hmx : m[p.cell]? = some (.live cell) := by rw [hp1, hm x (by simp), hold]
                  have hins := cellsSum_overwrite (entrySum g d) p.entry hmx
                  have hm'' : ∀ y ∈ rest, (m.insert p.cell p.entry)[y.cell]? = w.cells[y.cell]? := by
                    intro y hy
                    rw [Std.TreeMap.getElem?_insert]
                    have : compare p.cell y.cell ≠ .eq := by
                      intro he
                      apply hn.1
                      rw [← hp1, Std.LawfulEqCmp.eq_of_compare he]
                      exact List.mem_map_of_mem hy
                    simp [this, hm' y hy]
                  have ih := touches_sum hg d rest raw' (m.insert p.cell p.entry) hn.2 hr hm''
                  have hdelta : sumBy g d p.flows =
                      entrySum g d p.entry - entrySum g d (.live cell) := by
                    rw [hfl, sumBy_flowsOf hg]; rfl
                  simp only [List.reduceOption, List.filterMap_cons, id, List.map_cons,
                    List.flatMap_cons] at ih ⊢
                  rw [sumBy_append]
                  show cellsSum (entrySum g d) (insertAll (m.insert p.cell p.entry) _) = _
                  rw [ih, hins, hdelta]
                  omega

/-- Fresh births add exactly their own contributions. -/
theorem born_sum (f : Entry → Int) :
    ∀ (ps : List (D × Cell)) (m : Std.TreeMap D Entry compare), (ps.map Prod.fst).Nodup →
      (∀ p ∈ ps, m[p.1]? = none) →
      cellsSum f (insertAll m (ps.map fun p => (p.1, Entry.live p.2))) =
        cellsSum f m + (ps.map fun p => f (.live p.2)).sum
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
      have ih := born_sum f rest (m.insert p.1 (.live p.2)) hn.2 hf'
      have h1 := cellsSum_fresh f (Entry.live p.2) (hf p (by simp))
      simp only [List.map_cons, List.sum_cons]
      show cellsSum f (insertAll (m.insert p.1 (.live p.2)) _) = _
      rw [ih, h1]; omega

/-- **An admitted turn moves every sum by exactly its flows.** -/
theorem admit_sum {E : Env D} {w w' : World D} {t : Turn D} {g : Flow → Int} (hg : Linear g)
    (d : ByteArray) (h : World.admit E w t = .ok w') :
    ∃ posts, Checked E w t posts ∧ w'.sumOf g d = w.sumOf g d + sumBy g d (valueFlows E t posts) := by
  obtain ⟨posts, hk, rfl⟩ := admit_ok h
  refine ⟨posts, hk, ?_⟩
  obtain ⟨raw, hm, hposts⟩ := hk.touches
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
  have ht := touches_sum hg d t.touches raw w.cells nt hm (fun _ _ => rfl)
  rw [← hposts] at ht
  have hids : (createdPairs E t).map Prod.fst = createdIds E t := by
    unfold createdPairs; exact List.map_fst_zip (by simp [createdIds])
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
  have hb := born_sum (entrySum g d) (createdPairs E t) (insertAll w.cells (posts.map Post.pair))
    (by rw [hids]; exact nb) hfr
  have hbsum : ((createdPairs E t).map fun p => entrySum g d (.live p.2)) =
      (createdPairs E t).map fun p => sumBy g d (flowsOf none (some p.2)) := rfl
  unfold World.sumOf commit valueFlows
  dsimp only
  unfold bornEntries
  rw [hb, ht, hbsum, sumBy_append, sumBy_flatMap g d (fun p => flowsOf none (some p.2)) (createdPairs E t)]
  omega

/-- **Value is conserved.** Whatever turn `World.admit` admits, every denomination's balance sum
is exactly what it was. -/
theorem admit_value {E : Env D} {w w' : World D} {t : Turn D}
    (h : World.admit E w t = .ok w') (d : ByteArray) : w'.valueSum d = w.valueSum d := by
  obtain ⟨posts, hk, hs⟩ := admit_sum linear_balance d h
  unfold World.valueSum
  rw [hs, (checkValue_ok hk.value).2.1 d]; omega

/-- **Floors are conserved outside a birth.** A turn moves no floor sum but that of a
denomination it bears. -/
theorem admit_floors {E : Env D} {w w' : World D} {t : Turn D}
    (h : World.admit E w t = .ok w') {d : ByteArray} (hd : d ∉ (createdIds E t).map E.bytes) :
    w'.floorSum d = w.floorSum d := by
  obtain ⟨posts, hk, hs⟩ := admit_sum linear_floor d h
  unfold World.floorSum
  rw [hs, (checkValue_ok hk.value).2.2 d hd]; omega

/-- **Value is conserved over a log.** -/
theorem fold_value {E : Env D} (d : ByteArray) :
    ∀ {w w' : World D} {l : List (Turn D)}, World.fold E w l = .ok w' → w'.valueSum d = w.valueSum d
  | w, w', [], h => by simp [World.fold] at h; subst h; rfl
  | w, w', t :: rest, h => by
      obtain ⟨w₁, h₁, h₂⟩ := fold_cons_ok.mp h
      rw [fold_value d h₂, admit_value h₁ d]

/-- **The cap is fixed after birth.** Over a log none of whose turns bears `d`, its floor sum
does not move. -/
theorem fold_floors {E : Env D} {d : ByteArray} :
    ∀ {w w' : World D} {l : List (Turn D)}, World.fold E w l = .ok w' →
      (∀ t ∈ l, d ∉ (createdIds E t).map E.bytes) → w'.floorSum d = w.floorSum d
  | w, w', [], h, _ => by simp [World.fold] at h; subst h; rfl
  | w, w', t :: rest, h, hn => by
      obtain ⟨w₁, h₁, h₂⟩ := fold_cons_ok.mp h
      rw [fold_floors h₂ (fun u hu => hn u (by simp [hu])), admit_floors h₁ (hn t (by simp))]

/-! ## Floors: every live value cell is within its floor -/

/-- A value cell decodes and is within its floor (any other cell trivially). -/
def ValueOk (cell : Cell) : Prop :=
  cell.discipline = .value → ∃ v, Value.ofCell cell = some v ∧ v.withinFloor = true

/-- Every live value cell of the World is `ValueOk`. -/
def FloorOk (w : World D) : Prop := ∀ c cell, w.live c = some cell → ValueOk cell

omit [Ord D] [DecidableEq D] [Std.TransOrd D] [Std.LawfulEqOrd D] in
theorem checkValueCell_valueOk {c : D} {cell : Cell} (h : checkValueCell c cell = .ok ()) :
    ValueOk cell := by
  intro hv
  unfold checkValueCell at h
  rw [if_pos hv] at h
  split at h
  · simp at h
  · rename_i v hv'
    exact ⟨v, hv', req_ok.mp h⟩

omit [Ord D] [DecidableEq D] [Std.TransOrd D] [Std.LawfulEqOrd D] in
/-- A write leaves a value cell only in a `ValueOk` state (`postWrite` judges it). -/
theorem postWrite_valueOk {c : D} {cell post : Cell} {ops : List Op}
    (h : postWrite c cell ops = .ok post) : ValueOk post := by
  intro hv
  have hd := (postWrite_keeps h).2.1
  unfold postWrite at h
  split at h
  · simp at h
  · rename_i hc; rw [hc] at hd; rw [hd] at hv; cases hv
  · rename_i hc; rw [hc] at hd; rw [hd] at hv; cases hv
  · simp only [except_bind_ok, pure, Except.pure, Except.ok.injEq] at h
    obtain ⟨⟨⟩, _, ⟨⟩, hcv, rfl⟩ := h
    exact checkValueCell_valueOk hcv hv

omit [Ord D] [DecidableEq D] [Std.TransOrd D] [Std.LawfulEqOrd D] in
theorem mem_createdPairs_of_mem {E : Env D} {t : Turn D} {c : Cell} (h : c ∈ t.creates) :
    ∃ id, (id, c) ∈ createdPairs E t := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem h
  have hlen : (createdIds E t).length = t.creates.length := by simp [createdIds]
  refine ⟨(createdIds E t)[i]'(by omega), ?_⟩
  unfold createdPairs
  have hz : i < ((createdIds E t).zip t.creates).length := by simp [hlen, hi]
  have := List.getElem_mem hz
  rw [List.getElem_zip] at this
  exact this

/-- **Every live value cell stays within its floor**, whatever turn is admitted: a written one
because `postWrite` judged it, a born one because `checkValue` did, an untouched one because it
was before. -/
theorem admit_floorOk {E : Env D} {w w' : World D} {t : Turn D} (hf : FloorOk w)
    (h : World.admit E w t = .ok w') : FloorOk w' := by
  intro c cell hl
  rcases admit_live h hl with hb | ⟨pre, hpre, rfl | ⟨ops, hw⟩⟩
  · obtain ⟨posts, hk, _⟩ := admit_ok h
    obtain ⟨id, hid⟩ := mem_createdPairs_of_mem (E := E) hb
    exact checkValueCell_valueOk ((checkValue_ok hk.value).1 _ hid)
  · exact hf c _ hpre
  · exact postWrite_valueOk hw

theorem fold_floorOk {E : Env D} :
    ∀ {w w' : World D} {l : List (Turn D)}, FloorOk w → World.fold E w l = .ok w' → FloorOk w'
  | w, w', [], hf, h => by simp [World.fold] at h; subst h; exact hf
  | w, w', t :: rest, hf, h => by
      obtain ⟨w₁, h₁, h₂⟩ := fold_cons_ok.mp h
      exact fold_floorOk (admit_floorOk hf h₁) h₂

omit [Ord D] [DecidableEq D] [Std.TransOrd D] [Std.LawfulEqOrd D] in
theorem ofCell_value {cell : Cell} {v : Value} (h : Value.ofCell cell = some v) :
    cell.discipline = .value := by
  unfold Value.ofCell at h
  split at h
  · assumption
  · simp at h

omit [Ord D] [DecidableEq D] [Std.TransOrd D] [Std.LawfulEqOrd D] in
/-- One entry: what it has outstanding is at most its floor plus its balance. -/
theorem entry_outstanding {e : Entry} (hv : ∀ cell, e = .live cell → ValueOk cell) (d : ByteArray) :
    entrySum (fun f => max f.balance 0) d e ≤ entrySum Flow.floor d e + entrySum Flow.balance d e := by
  cases e with
  | tomb => simp [entrySum, Entry.cell?, flowsOf, sumBy]
  | live cell =>
      unfold entrySum
      simp only [Entry.cell?, flowsOf, Option.bind_none, Option.map_none, Option.toList_none,
        List.nil_append, Option.bind_some]
      cases ho : Value.ofCell cell with
      | none => simp [sumBy]
      | some v =>
          obtain ⟨v', hv', hw⟩ := hv cell rfl (ofCell_value ho)
          rw [ho, Option.some.injEq] at hv'
          subst hv'
          simp only [Option.map_some, Option.toList_some, sumBy, List.map_cons, List.map_nil,
            List.sum_cons, List.sum_nil, Value.flow]
          have : -(v.floor : Int) ≤ v.balance := of_decide_eq_true hw
          split <;> omega

omit [DecidableEq D] in
/-- **Outstanding is bounded by the floors.** On a World whose live value cells are within their
floors, what is outstanding of a denomination (its positive balances) is at most its floor sum
plus its balance sum. -/
theorem outstanding_le_floors {w : World D} (hf : FloorOk w) (d : ByteArray) :
    w.outstanding d ≤ w.floorSum d + w.valueSum d := by
  unfold World.outstanding World.floorSum World.valueSum World.sumOf cellsSum
  have key : ∀ l : List (D × Entry), (∀ p ∈ l, w.cells[p.1]? = some p.2) →
      (l.map fun p => entrySum (fun f => max f.balance 0) d p.2).sum ≤
        (l.map fun p => entrySum Flow.floor d p.2).sum + (l.map fun p => entrySum Flow.balance d p.2).sum := by
    intro l
    induction l with
    | nil => simp
    | cons p rest ih =>
        intro hl
        have hp := entry_outstanding (e := p.2) (fun cell he => hf p.1 cell (by
          unfold World.live; rw [hl p (by simp), he])) d
        have := ih (fun q hq => hl q (by simp [hq]))
        simp only [List.map_cons, List.sum_cons]
        omega
  exact key _ fun p hp => Std.TreeMap.mem_toList_iff_getElem?_eq_some.mp hp

omit [DecidableEq D] in
/-- **The cap.** Where value sums to 0, nothing more is outstanding than the floors. -/
theorem outstanding_le_cap {w : World D} (hf : FloorOk w) {d : ByteArray} (h0 : w.valueSum d = 0) :
    w.outstanding d ≤ w.floorSum d := by
  have := outstanding_le_floors hf d; omega

/-! ## Birth: a floor sum is set once -/

/-- Every denomination with a floor names an id the World holds (live or tombstoned). -/
def FloorsBorn (E : Env D) (w : World D) : Prop :=
  ∀ d, w.floorSum d ≠ 0 → ∃ id, w.cells.contains id = true ∧ E.bytes id = d

omit [DecidableEq D] in
theorem insertAll_contains {k : D} :
    ∀ {m : Std.TreeMap D Entry compare} {ps : List (D × Entry)},
      (m.contains k = true ∨ k ∈ ps.map Prod.fst) → (insertAll m ps).contains k = true
  | m, [], h => by simpa using h
  | m, p :: rest, h => by
      show (insertAll (m.insert p.1 p.2) rest).contains k = true
      apply insertAll_contains
      rcases h with hm | hm
      · left; rw [Std.TreeMap.contains_insert]; simp [hm]
      · simp only [List.map_cons, List.mem_cons] at hm
        rcases hm with he | hm
        · left; rw [Std.TreeMap.contains_insert]; subst he; simp
        · right; exact hm

/-- `FloorsBorn` is kept by every admitted turn. -/
theorem admit_floorsBorn {E : Env D} {w w' : World D} {t : Turn D} (hb : FloorsBorn E w)
    (h : World.admit E w t = .ok w') : FloorsBorn E w' := by
  intro d hd
  have hw' := h
  obtain ⟨posts, hk, rfl⟩ := admit_ok hw'
  by_cases hborn : d ∈ (createdIds E t).map E.bytes
  · obtain ⟨id, hid, rfl⟩ := List.mem_map.mp hborn
    refine ⟨id, ?_, rfl⟩
    show (insertAll (insertAll w.cells (posts.map Post.pair)) (bornEntries E t)).contains id = true
    apply insertAll_contains; right
    unfold bornEntries createdPairs
    rw [List.map_map]
    have : (Prod.fst ∘ fun p : D × Cell => (p.1, Entry.live p.2)) = Prod.fst := rfl
    rw [this, List.map_fst_zip (by simp [createdIds])]
    exact hid
  · rw [admit_floors h hborn] at hd
    obtain ⟨id, hc, he⟩ := hb d hd
    refine ⟨id, ?_, he⟩
    show (insertAll (insertAll w.cells (posts.map Post.pair)) (bornEntries E t)).contains id = true
    exact insertAll_contains (.inl (insertAll_contains (.inl hc)))

omit [Std.TransOrd D] [Std.LawfulEqOrd D] in
/-- **A denomination's floor is set at its birth.** Before the turn that bears it, its floor sum is
0, given the digest's bytes injective (a fresh id's bytes are no held id's bytes). With
`fold_floors_held`, its floor sum after birth is what the birth turn set, forever. -/
theorem admit_birth {E : Env D} {w w' : World D} {t : Turn D} (hb : FloorsBorn E w)
    (hinj : ∀ a b : D, E.bytes a = E.bytes b → a = b) (h : World.admit E w t = .ok w')
    {d : ByteArray} (hd : d ∈ (createdIds E t).map E.bytes) : w.floorSum d = 0 := by
  obtain ⟨posts, hk, _⟩ := admit_ok h
  obtain ⟨id, hid, rfl⟩ := List.mem_map.mp hd
  apply Classical.byContradiction
  intro hne
  obtain ⟨id', hc, he⟩ := hb _ hne
  have := hinj _ _ he
  subst this
  have hcr := hk.creates
  unfold checkCreates at hcr
  simp only [except_bind_ok] at hcr
  obtain ⟨⟨⟩, _, ⟨⟩, _, hfresh⟩ := hcr
  have := (forEx_ok.mp hfresh) id' hid
  rw [req_ok] at this
  simp [hc] at this

theorem fold_floorsBorn {E : Env D} :
    ∀ {w w' : World D} {l : List (Turn D)}, FloorsBorn E w → World.fold E w l = .ok w' → FloorsBorn E w'
  | w, w', [], hb, h => by simp [World.fold] at h; subst h; exact hb
  | w, w', t :: rest, hb, h => by
      obtain ⟨w₁, h₁, h₂⟩ := fold_cons_ok.mp h
      exact fold_floorsBorn (admit_floorsBorn hb h₁) h₂


omit [Std.TransOrd D] [Std.LawfulEqOrd D] in
/-- A turn never bears an id the World already holds, so never a held id's denomination (given the
digest's bytes injective): `checkCreates` refuses a live or tombstoned id (`idTaken`). -/
theorem admit_not_born {E : Env D} {w w' : World D} {t : Turn D}
    (hinj : ∀ a b : D, E.bytes a = E.bytes b → a = b) (h : World.admit E w t = .ok w')
    {id : D} (hc : w.cells.contains id = true) : E.bytes id ∉ (createdIds E t).map E.bytes := by
  obtain ⟨posts, hk, _⟩ := admit_ok h
  intro hm
  obtain ⟨id', hid, he⟩ := List.mem_map.mp hm
  have := hinj _ _ he
  subst this
  have hcr := hk.creates
  unfold checkCreates at hcr
  simp only [except_bind_ok] at hcr
  obtain ⟨⟨⟩, _, ⟨⟩, _, hfresh⟩ := hcr
  have := (forEx_ok.mp hfresh) id' hid
  rw [req_ok] at this
  simp [hc] at this

/-- **The cap is fixed forever.** Once a World holds the id that names a denomination (its well:
from the turn that bore it on), no admitted log moves that denomination's floor sum. With
`admit_birth` (0 before) and `dispatch_value_born` (the birth sets it to the signed cap). -/
theorem fold_floors_held {E : Env D} (hinj : ∀ a b : D, E.bytes a = E.bytes b → a = b) {id : D} :
    ∀ {w w' : World D} {l : List (Turn D)}, World.fold E w l = .ok w' → w.cells.contains id = true →
      w'.floorSum (E.bytes id) = w.floorSum (E.bytes id)
  | w, w', [], h, _ => by simp [World.fold] at h; subst h; rfl
  | w, w', t :: rest, h, hc => by
      obtain ⟨w₁, h₁, h₂⟩ := fold_cons_ok.mp h
      have hc₁ : w₁.cells.contains id = true := by
        obtain ⟨posts, _, rfl⟩ := admit_ok h₁
        exact insertAll_contains (.inl (insertAll_contains (.inl hc)))
      rw [fold_floors_held hinj h₂ hc₁, admit_floors h₁ (admit_not_born hinj h₁ hc)]

/-! ## Genesis holds no value -/

omit [DecidableEq D] in
/-- A cell map none of whose entries is a value cell contributes 0 to every value measure. -/
theorem cellsSum_noValue {m : Std.TreeMap D Entry compare} {g : Flow → Int} {d : ByteArray}
    (h : ∀ (k : D) (e : Entry), m[k]? = some e → ∀ c : Cell, e = .live c → c.discipline ≠ .value) :
    cellsSum (entrySum g d) m = 0 := by
  unfold cellsSum
  have key : ∀ l : List (D × Entry), (∀ p ∈ l, m[p.1]? = some p.2) →
      (l.map fun p => entrySum g d p.2).sum = 0 := by
    intro l
    induction l with
    | nil => intro _; rfl
    | cons p rest ih =>
        intro hl
        have hp : entrySum g d p.2 = 0 := by
          cases he : p.2 with
          | tomb => simp [entrySum, Entry.cell?, flowsOf, sumBy]
          | live c =>
              have hnv := h p.1 p.2 (hl p (by simp)) c he
              have : Value.ofCell c = none := by unfold Value.ofCell; simp [hnv]
              simp [entrySum, Entry.cell?, flowsOf, this, sumBy]
        simp only [List.map_cons, List.sum_cons, hp, ih (fun q hq => hl q (by simp [hq]))]
        rfl
  exact key _ fun p hp => Std.TreeMap.mem_toList_iff_getElem?_eq_some.mp hp

omit [DecidableEq D] [Std.TransOrd D] [Std.LawfulEqOrd D] in
/-- Such a map's World is within its floors, trivially. -/
theorem floorOk_noValue {w : World D}
    (h : ∀ (k : D) (e : Entry), w.cells[k]? = some e → ∀ c : Cell, e = .live c → c.discipline ≠ .value) : FloorOk w := by
  intro k c hl hv
  unfold World.live at hl
  split at hl
  · rename_i hh; simp only [Option.some.injEq] at hl; subst hl; exact absurd hv (h k _ hh _ rfl)
  · simp at hl

end Turn

end Nanodregg.Kernel
