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
import Kernel.Proofs.Lawful

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
    (∀ p ∈ t.creates, checkValueCell p.1 p.2 = .ok ()) ∧
      (∀ d, sumBy Flow.balance d (valueFlows t posts) = 0) ∧
      (∀ d, d ∉ (createdIds t).map E.bytes → sumBy Flow.floor d (valueFlows t posts) = 0) := by
  unfold checkValue at h
  simp only [except_bind_ok] at h
  obtain ⟨⟨⟩, hb, h⟩ := h
  refine ⟨forEx_ok.mp hb, ?_⟩
  split at h
  · simp at h
  · rename_i acc hacc
    have hall := forEx_ok.mp h
    have each : ∀ a ∈ acc, a.balance = 0 ∧ (a.floor = 0 ∨ a.denom ∈ (createdIds t).map E.bytes) := by
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

omit [Ord D] in
/-- Overwriting a slot moves the sum by the difference. -/
theorem cellsSum_overwrite (f : Entry → Int) {E : Env D} {m : Cells D}
    (hr : Trie.Routed (trieSpec E) 0 m) {k : Slot D} {old : Leaf} (v : Leaf)
    (h : m.get (trieSpec E) k = some old) :
    cellsSum f (m.insert (trieSpec E) k v) = cellsSum f m - old.sumOf f + v.sumOf f :=
  Trie.sumI_insert_some (trieSpec E) (fun p => p.2.sumOf f) hr v h

omit [Ord D] in
/-- A fresh slot adds exactly its own contribution. -/
theorem cellsSum_fresh (f : Entry → Int) {E : Env D} {m : Cells D}
    (hr : Trie.Routed (trieSpec E) 0 m) {k : Slot D} (v : Leaf) (h : m.get (trieSpec E) k = none) :
    cellsSum f (m.insert (trieSpec E) k v) = cellsSum f m + v.sumOf f :=
  Trie.sumI_insert_none (trieSpec E) (fun p => p.2.sumOf f) hr v h

omit [Ord D] in
/-- Writing an entry at a cell slot that holds no entry adds exactly the entry's contribution
(whatever else the slot held contributes nothing). -/
theorem cellsSum_write (f : Entry → Int) {E : Env D} {m : Cells D}
    (hr : Trie.Routed (trieSpec E) 0 m) {k : Slot D} (e : Entry)
    (h : ∀ e', m.get (trieSpec E) k ≠ some (.entry e')) :
    cellsSum f (m.insert (trieSpec E) k (.entry e)) = cellsSum f m + f e := by
  cases hg : m.get (trieSpec E) k with
  | none => rw [cellsSum_fresh f hr _ hg]; rfl
  | some l =>
      cases l with
      | entry e' => exact absurd hg (h e')
      | spent => rw [cellsSum_overwrite f hr _ hg]; simp [Leaf.sumOf]

/-! ## What one admitted turn does to the sums -/

section Turn
variable [Std.TransOrd D] [Std.LawfulEqOrd D]

omit [Std.TransOrd D] [Std.LawfulEqOrd D] in
/-- A touch that changes its cell replaces a live cell, and its flows are that change. -/
theorem touchCheck_flows {E : Env D} {w : World D} {x : Touch D} {p : Post D}
    (h : touchCheck E w x = .ok (some p)) :
    p.cell = x.cell ∧ ∃ cell, w.trie.get (trieSpec E) (.cell x.cell) = some (.entry (.live cell)) ∧
      p.flows = flowsOf (some cell) p.entry.cell? := by
  unfold touchCheck at h
  simp only [except_bind_ok] at h
  obtain ⟨⟨⟩, _, h⟩ := h
  cases ha : x.act with
  | keep => rw [ha] at h; simp [pure, Except.pure] at h
  | write ops =>
      rw [ha] at h
      cases hc : w.live E x.cell with
      | none => rw [hc] at h; simp at h
      | some cell =>
          rw [hc] at h
          simp only [except_bind_ok, pure, Except.pure, Except.ok.injEq, Option.some.injEq] at h
          obtain ⟨post, _, rfl⟩ := h
          exact ⟨rfl, cell, live_get hc, rfl⟩
  | retire =>
      rw [ha] at h
      cases hc : w.live E x.cell with
      | none => rw [hc] at h; simp at h
      | some cell =>
          rw [hc] at h
          simp only [except_bind_ok, pure, Except.pure, Except.ok.injEq, Option.some.injEq] at h
          obtain ⟨_, _, rfl⟩ := h
          exact ⟨rfl, cell, live_get hc, rfl⟩

omit [Std.TransOrd D] [Std.LawfulEqOrd D] in
/-- The touches move each sum by exactly their flows. -/
theorem touches_sum {E : Env D} {w : World D} {g : Flow → Int} (hg : Linear g) (d : ByteArray) :
    ∀ (l : List (Touch D)) (raw : List (Option (Post D))) (m : Cells D),
      Trie.Routed (trieSpec E) 0 m →
      (l.map Touch.cell).Nodup → mapEx (touchCheck E w) l = .ok raw →
      (∀ x ∈ l, m.get (trieSpec E) (.cell x.cell) = w.trie.get (trieSpec E) (.cell x.cell)) →
      cellsSum (entrySum g d) (insertAll E m (raw.reduceOption.map Post.pair)) =
        cellsSum (entrySum g d) m + sumBy g d (raw.reduceOption.flatMap Post.flows)
  | [], raw, m, _, _, h, _ => by
      simp [mapEx] at h; subst h; simp [insertAll, List.reduceOption, sumBy]
  | x :: rest, raw, m, hrt, hn, h, hm => by
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
              have hm' : ∀ y ∈ rest, m.get (trieSpec E) (.cell y.cell) =
                  w.trie.get (trieSpec E) (.cell y.cell) := fun y hy => hm y (by simp [hy])
              cases r with
              | none =>
                  have := touches_sum hg d rest raw' m hrt hn.2 hr hm'
                  simpa [List.reduceOption, List.filterMap_cons] using this
              | some p =>
                  obtain ⟨hp1, cell, hold, hfl⟩ := touchCheck_flows hx
                  have hmx : m.get (trieSpec E) (.cell p.cell) = some (.entry (.live cell)) := by
                    rw [hp1, hm x (by simp), hold]
                  have hins := cellsSum_overwrite (entrySum g d) hrt (.entry p.entry) hmx
                  simp only [Leaf.sumOf] at hins
                  have hm'' : ∀ y ∈ rest, (m.insert (trieSpec E) (.cell p.cell) (.entry p.entry)).get
                      (trieSpec E) (.cell y.cell) = w.trie.get (trieSpec E) (.cell y.cell) := by
                    intro y hy
                    rw [Trie.get_insert_ne]
                    · exact hm' y hy
                    · intro he
                      injection he with he
                      apply hn.1
                      rw [← hp1, ← he]
                      exact List.mem_map_of_mem hy
                  have ih := touches_sum hg d rest raw' _ (Trie.routed_insert _ _ _ hrt) hn.2 hr hm''
                  have hdelta : sumBy g d p.flows =
                      entrySum g d p.entry - entrySum g d (.live cell) := by
                    rw [hfl, sumBy_flowsOf hg]; rfl
                  simp only [List.reduceOption, List.filterMap_cons, id, List.map_cons,
                    List.flatMap_cons] at ih ⊢
                  rw [sumBy_append]
                  show cellsSum (entrySum g d)
                    (insertAll E (m.insert (trieSpec E) (.cell p.cell) (.entry p.entry)) _) = _
                  rw [ih, hins, hdelta]
                  omega

omit [Ord D] in
/-- Births at cell slots that hold no entry add exactly their own contributions. -/
theorem born_sum (f : Entry → Int) {E : Env D} :
    ∀ (ps : List (D × Cell)) (m : Cells D), Trie.Routed (trieSpec E) 0 m → (ps.map Prod.fst).Nodup →
      (∀ p ∈ ps, ∀ e, m.get (trieSpec E) (.cell p.1) ≠ some (.entry e)) →
      cellsSum f (insertAll E m (ps.map fun p => (p.1, Entry.live p.2))) =
        cellsSum f m + (ps.map fun p => f (.live p.2)).sum
  | [], m, _, _, _ => by simp [insertAll]
  | p :: rest, m, hrt, hn, hf => by
      simp only [List.map_cons, List.nodup_cons] at hn
      have hf' : ∀ q ∈ rest, ∀ e, (m.insert (trieSpec E) (.cell p.1) (.entry (.live p.2))).get
          (trieSpec E) (.cell q.1) ≠ some (.entry e) := by
        intro q hq e
        rw [Trie.get_insert_ne]
        · exact hf q (by simp [hq]) e
        · intro he
          injection he with he
          apply hn.1
          rw [← he]
          exact List.mem_map_of_mem hq
      have ih := born_sum f rest _ (Trie.routed_insert _ _ _ hrt) hn.2 hf'
      have h1 := cellsSum_write f hrt (Entry.live p.2) (hf p (by simp))
      simp only [List.map_cons, List.sum_cons]
      show cellsSum f (insertAll E (m.insert (trieSpec E) (.cell p.1) (.entry (.live p.2))) _) = _
      rw [ih, h1]; omega

/-- **An admitted turn moves every sum by exactly its flows.** -/
theorem admit_sum {E : Env D} {w w' : World D} {t : Turn D} {g : Flow → Int} (hg : Linear g)
    (d : ByteArray) (hc : w.Canon E) (h : World.admit E w t = .ok w') :
    ∃ posts, Checked E w t posts ∧ w'.sumOf g d = w.sumOf g d + sumBy g d (valueFlows t posts) := by
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
  obtain ⟨⟨⟩, _, ⟨⟩, hnb, ⟨⟩, hnbt, hfresh⟩ := hcr
  have nt := noDup_nodup hnt
  have nb := noDup_nodup hnb
  have nbt := noDup_nodup hnbt
  have ht := touches_sum hg d t.touches raw w.trie hc.1 nt hm (fun _ _ => rfl)
  rw [← hposts] at ht
  have hids : t.creates.map Prod.fst = createdIds t := by
    rfl
  have hpk : ∀ p ∈ posts, p.cell ∈ t.touches.map Touch.cell := by
    intro p hp
    obtain ⟨x, hx, he, _⟩ := posts_touched hk p hp
    rw [he]; exact List.mem_map_of_mem hx
  have hfr : ∀ p ∈ t.creates, ∀ e,
      (insertAll E w.trie (posts.map Post.pair)).get (trieSpec E) (.cell p.1) ≠ some (.entry e) := by
    intro p hp e
    have hb : p.1 ∈ createdIds t := by rw [← hids]; exact List.mem_map_of_mem hp
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
    intro hg'
    have he : w.entry E p.1 = some e := by unfold World.entry; rw [hg']
    simp [World.taken, he] at this
  have hb := born_sum (entrySum g d) t.creates (insertAll E w.trie (posts.map Post.pair))
    (insertAll_canon _ hc).1 (by rw [hids]; exact nb) hfr
  have hbsum : (t.creates.map fun p => entrySum g d (.live p.2)) =
      t.creates.map fun p => sumBy g d (flowsOf none (some p.2)) := rfl
  have hsp : ∀ (m : Cells D) (ns : List D), Trie.Routed (trieSpec E) 0 m →
      (∀ n ∈ ns, ∀ e, m.get (trieSpec E) (.nullifier n) ≠ some (.entry e)) →
      cellsSum (entrySum g d) (spendAll E m ns) = cellsSum (entrySum g d) m := by
    intro m ns
    induction ns generalizing m with
    | nil => intro _ _; rfl
    | cons n rest ih =>
        intro hrt hne
        show cellsSum (entrySum g d) (spendAll E (m.insert (trieSpec E) (.nullifier n) .spent) rest) = _
        rw [ih _ (Trie.routed_insert _ _ _ hrt) (fun k hk e => by
          rw [Trie.get_insert]
          split
          · simp
          · exact hne k (by simp [hk]) e)]
        cases hg' : m.get (trieSpec E) (.nullifier n) with
        | none => rw [cellsSum_fresh _ hrt _ hg']; simp [Leaf.sumOf]
        | some l =>
            rw [cellsSum_overwrite _ hrt _ hg']
            cases l with
            | spent => simp [Leaf.sumOf]
            | entry e => exact absurd hg' (hne n (by simp) e)
  have hun : ∀ n ∈ t.nullifiers, ∀ e,
      (insertAll E (insertAll E w.trie (posts.map Post.pair)) (bornEntries t)).get (trieSpec E)
        (.nullifier n) ≠ some (.entry e) := by
    intro n hn e
    rw [insertAll_get_nullifier, insertAll_get_nullifier]
    have := (forEx_ok.mp hk.nullifiers) n hn
    rw [req_ok] at this
    intro hg'
    simp [World.isSpent, hg'] at this
  unfold World.sumOf commit commitWith valueFlows commitTrie
  dsimp only
  rw [hsp _ _ (insertAll_canon _ (insertAll_canon _ hc)).1 hun]
  unfold bornEntries
  rw [hb, ht, hbsum, sumBy_append, sumBy_flatMap g d (fun p => flowsOf none (some p.2)) t.creates]
  omega

/-- **Value is conserved.** Whatever turn `World.admit` admits, every denomination's balance sum
is exactly what it was. -/
theorem admit_value {E : Env D} {w w' : World D} {t : Turn D} (hc : w.Canon E)
    (h : World.admit E w t = .ok w') (d : ByteArray) : w'.valueSum d = w.valueSum d := by
  obtain ⟨posts, hk, hs⟩ := admit_sum linear_balance d hc h
  unfold World.valueSum
  rw [hs, (checkValue_ok hk.value).2.1 d]; omega

/-- **Floors are conserved outside a birth.** A turn moves no floor sum but that of a
denomination it bears. -/
theorem admit_floors {E : Env D} {w w' : World D} {t : Turn D} (hc : w.Canon E)
    (h : World.admit E w t = .ok w') {d : ByteArray} (hd : d ∉ (createdIds t).map E.bytes) :
    w'.floorSum d = w.floorSum d := by
  obtain ⟨posts, hk, hs⟩ := admit_sum linear_floor d hc h
  unfold World.floorSum
  rw [hs, (checkValue_ok hk.value).2.2 d hd]; omega

omit [Std.TransOrd D] [Std.LawfulEqOrd D] in
/-- A recorded refusal moves no sum over the cells (it leaves the cells' trie as it was). -/
theorem refuse_sumOf {E : Env D} {w w' : World D} {r : Refused D} (h : World.refuse E w r = .ok w')
    (g : Flow → Int) (d : ByteArray) : w'.sumOf g d = w.sumOf g d := by
  unfold World.sumOf; rw [refuse_trie h]

omit [Std.TransOrd D] [Std.LawfulEqOrd D] in
theorem refuse_taken {E : Env D} {w w' : World D} {r : Refused D} (h : World.refuse E w r = .ok w')
    (c : D) : w'.taken E c = w.taken E c := by
  unfold World.taken; rw [refuse_entry h]

/-- **Value is conserved over a log.** -/
theorem fold_value {E : Env D} (d : ByteArray) :
    ∀ {w w' : World D} {l : List (Step D)}, w.Canon E → World.fold E w l = .ok w' →
      w'.valueSum d = w.valueSum d
  | w, w', [], _, h => by simp [World.fold] at h; subst h; rfl
  | w, w', .turn t :: rest, hc, h => by
      obtain ⟨w₁, h₁, h₂⟩ := fold_cons_ok.mp h
      rw [fold_value d (admit_canon hc h₁) h₂, admit_value hc h₁ d]
  | w, w', .refusal r :: rest, hc, h => by
      obtain ⟨w₁, h₁, h₂⟩ := fold_cons_ok.mp h
      rw [fold_value d (refuse_canon hc h₁) h₂]; exact refuse_sumOf h₁ _ d

/-- **The cap is fixed after birth.** Over a log none of whose turns bears `d`, its floor sum
does not move. -/
theorem fold_floors {E : Env D} {d : ByteArray} :
    ∀ {w w' : World D} {l : List (Step D)}, w.Canon E → World.fold E w l = .ok w' →
      (∀ t ∈ Step.turns l, d ∉ (createdIds t).map E.bytes) → w'.floorSum d = w.floorSum d
  | w, w', [], _, h, _ => by simp [World.fold] at h; subst h; rfl
  | w, w', .turn t :: rest, hc, h, hn => by
      obtain ⟨w₁, h₁, h₂⟩ := fold_cons_ok.mp h
      rw [fold_floors (admit_canon hc h₁) h₂ (fun u hu => hn u (by simp [Step.turns, hu])),
        admit_floors hc h₁ (hn t (by simp [Step.turns]))]
  | w, w', .refusal r :: rest, hc, h, hn => by
      obtain ⟨w₁, h₁, h₂⟩ := fold_cons_ok.mp h
      rw [fold_floors (refuse_canon hc h₁) h₂ hn]; exact refuse_sumOf h₁ _ d

/-! ## Floors: every live value cell is within its floor -/

/-- A value cell decodes and is within its floor (any other cell trivially). -/
def ValueOk (cell : Cell) : Prop :=
  cell.discipline = .value → ∃ v, Value.ofCell cell = some v ∧ v.withinFloor = true

/-- Every live value cell of the World is `ValueOk`. -/
def FloorOk (E : Env D) (w : World D) : Prop := ∀ c cell, w.live E c = some cell → ValueOk cell

omit [Ord D] [DecidableEq D] in
theorem checkValueCell_valueOk {c : D} {cell : Cell} (h : checkValueCell c cell = .ok ()) :
    ValueOk cell := by
  intro hv
  unfold checkValueCell at h
  rw [if_pos hv] at h
  split at h
  · simp at h
  · rename_i v hv'
    exact ⟨v, hv', req_ok.mp h⟩

omit [Ord D] [DecidableEq D] in
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

omit [Std.TransOrd D] [Std.LawfulEqOrd D] in
/-- **Every live value cell stays within its floor**, whatever turn is admitted: a written one
because `postWrite` judged it, a born one because `checkValue` did, an untouched one because it
was before. -/
theorem admit_floorOk {E : Env D} {w w' : World D} {t : Turn D} (hf : FloorOk E w)
    (h : World.admit E w t = .ok w') : FloorOk E w' := by
  intro c cell hl
  rcases admit_live h hl with hb | ⟨pre, hpre, rfl | ⟨ops, hw⟩⟩
  · obtain ⟨posts, hk, _⟩ := admit_ok h
    exact checkValueCell_valueOk ((checkValue_ok hk.value).1 _ hb)
  · exact hf c _ hpre
  · exact postWrite_valueOk hw

omit [Std.TransOrd D] [Std.LawfulEqOrd D] in
theorem fold_floorOk {E : Env D} {w w' : World D} {l : List (Step D)} (hf : FloorOk E w)
    (h : World.fold E w l = .ok w') : FloorOk E w' :=
  fold_keeps (P := fun v => FloorOk E v) admit_floorOk
    (fun hp hr => fun c cell hl => hp c cell ((refuse_live hr c).symm.trans hl)) hf h

omit [Ord D] [DecidableEq D] in
theorem ofCell_value {cell : Cell} {v : Value} (h : Value.ofCell cell = some v) :
    cell.discipline = .value := by
  unfold Value.ofCell at h
  split at h
  · assumption
  · simp at h

omit [Ord D] [DecidableEq D] in
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

omit [Std.TransOrd D] [Std.LawfulEqOrd D] in
/-- **Outstanding is bounded by the floors.** On a World whose live value cells are within their
floors, what is outstanding of a denomination (its positive balances) is at most its floor sum
plus its balance sum. -/
theorem outstanding_le_floors {E : Env D} {w : World D} (hc : w.Canon E) (hfit : w.Slotted E)
    (hf : FloorOk E w) (d : ByteArray) : w.outstanding d ≤ w.floorSum d + w.valueSum d := by
  unfold World.outstanding World.floorSum World.valueSum World.sumOf cellsSum
  have key : ∀ l : List (Slot D × Leaf), (∀ p ∈ l, w.trie.get (trieSpec E) p.1 = some p.2) →
      (l.map fun p => p.2.sumOf (entrySum (fun f => max f.balance 0) d)).sum ≤
        (l.map fun p => p.2.sumOf (entrySum Flow.floor d)).sum +
          (l.map fun p => p.2.sumOf (entrySum Flow.balance d)).sum := by
    intro l
    induction l with
    | nil => simp
    | cons p rest ih =>
        intro hl
        have hp : p.2.sumOf (entrySum (fun f => max f.balance 0) d) ≤
            p.2.sumOf (entrySum Flow.floor d) + p.2.sumOf (entrySum Flow.balance d) := by
          obtain ⟨s, l⟩ := p
          have hg := hl (s, l) (by simp)
          cases l with
          | spent => simp [Leaf.sumOf]
          | entry e =>
              cases s with
              | nullifier n => exact absurd (hfit _ _ hg) (by simp [Leaf.fits])
              | cell c =>
                  exact entry_outstanding (fun cell he => hf c cell (by
                    unfold World.live World.entry; rw [hg, he])) d
        have := ih (fun q hq => hl q (by simp [hq]))
        simp only [List.map_cons, List.sum_cons]
        omega
  exact key _ fun p hp => Trie.get_of_mem _ hc.1 hp

omit [Std.TransOrd D] [Std.LawfulEqOrd D] in
/-- **The cap.** Where value sums to 0, nothing more is outstanding than the floors. -/
theorem outstanding_le_cap {E : Env D} {w : World D} (hc : w.Canon E) (hfit : w.Slotted E)
    (hf : FloorOk E w) {d : ByteArray} (h0 : w.valueSum d = 0) :
    w.outstanding d ≤ w.floorSum d := by
  have := outstanding_le_floors hc hfit hf d; omega

/-! ## Birth: a floor sum is set once -/

/-- Every denomination with a floor names an id the World holds (live or tombstoned). -/
def FloorsBorn (E : Env D) (w : World D) : Prop :=
  ∀ d, w.floorSum d ≠ 0 → ∃ id, w.taken E id = true ∧ E.bytes id = d

omit [Std.TransOrd D] [Std.LawfulEqOrd D] in
theorem taken_iff {E : Env D} {w : World D} {c : D} :
    w.taken E c = true ↔ ∃ e, w.trie.get (trieSpec E) (.cell c) = some (.entry e) := by
  unfold World.taken
  constructor
  · intro h
    obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp h
    exact ⟨e, entry_get he⟩
  · rintro ⟨e, he⟩
    unfold World.entry; rw [he]; rfl

omit [Ord D] in
theorem insertAll_hasEntry {E : Env D} {k : D} :
    ∀ {m : Cells D} {ps : List (D × Entry)},
      ((∃ e, m.get (trieSpec E) (.cell k) = some (.entry e)) ∨ k ∈ ps.map Prod.fst) →
      ∃ e, (insertAll E m ps).get (trieSpec E) (.cell k) = some (.entry e)
  | m, [], h => by simpa using h
  | m, p :: rest, h => by
      show ∃ e, (insertAll E (m.insert (trieSpec E) (.cell p.1) (.entry p.2)) rest).get _ _ = _
      apply insertAll_hasEntry
      rcases h with ⟨e, hm⟩ | hm
      · left
        rw [Trie.get_insert]
        split
        · exact ⟨p.2, rfl⟩
        · exact ⟨e, hm⟩
      · simp only [List.map_cons, List.mem_cons] at hm
        rcases hm with he | hm
        · left; rw [he, Trie.get_insert_self]; exact ⟨p.2, rfl⟩
        · right; exact hm

omit [Std.TransOrd D] [Std.LawfulEqOrd D] in
theorem commit_taken {E : Env D} {w : World D} {t : Turn D} {posts : List (Post D)} {id : D}
    (h : w.taken E id = true ∨ id ∈ createdIds t) : (commit E w t posts).taken E id = true := by
  apply taken_iff.mpr
  rw [show (commit E w t posts).trie = commitTrie E w t posts from rfl, commitTrie_cell]
  apply insertAll_hasEntry
  rcases h with h | h
  · exact .inl (insertAll_hasEntry (.inl (taken_iff.mp h)))
  · right
    unfold bornEntries
    rw [List.map_map]
    have : (Prod.fst ∘ fun p : D × Cell => (p.1, Entry.live p.2)) = Prod.fst := rfl
    rw [this]
    exact h

/-- `FloorsBorn` is kept by every admitted turn. -/
theorem admit_floorsBorn {E : Env D} {w w' : World D} {t : Turn D} (hc : w.Canon E)
    (hb : FloorsBorn E w) (h : World.admit E w t = .ok w') : FloorsBorn E w' := by
  intro d hd
  have hw' := h
  obtain ⟨posts, hk, rfl⟩ := admit_ok hw'
  by_cases hborn : d ∈ (createdIds t).map E.bytes
  · obtain ⟨id, hid, rfl⟩ := List.mem_map.mp hborn
    exact ⟨id, commit_taken (.inr hid), rfl⟩
  · rw [admit_floors hc h hborn] at hd
    obtain ⟨id, hcn, he⟩ := hb d hd
    exact ⟨id, commit_taken (.inl hcn), he⟩

omit [Std.TransOrd D] [Std.LawfulEqOrd D] in
/-- **A denomination's floor is set at its birth.** Before the turn that bears it, its floor sum is
0, given the digest's bytes injective (a fresh id's bytes are no held id's bytes). With
`fold_floors_held`, its floor sum after birth is what the birth turn set, forever. -/
theorem admit_birth {E : Env D} {n : Nat} {w w' : World D} {t : Turn D} (hb : FloorsBorn E w)
    (hE : E.Lawful n) (h : World.admit E w t = .ok w')
    {d : ByteArray} (hd : d ∈ (createdIds t).map E.bytes) : w.floorSum d = 0 := by
  obtain ⟨posts, hk, _⟩ := admit_ok h
  obtain ⟨id, hid, rfl⟩ := List.mem_map.mp hd
  apply Classical.byContradiction
  intro hne
  obtain ⟨id', hc, he⟩ := hb _ hne
  have := hE.bytes_eq he
  subst this
  have hcr := hk.creates
  unfold checkCreates at hcr
  simp only [except_bind_ok] at hcr
  obtain ⟨⟨⟩, _, ⟨⟩, _, ⟨⟩, _, hfresh⟩ := hcr
  have := (forEx_ok.mp hfresh) id' hid
  rw [req_ok] at this
  simp [hc] at this

theorem fold_floorsBorn {E : Env D} {w w' : World D} {l : List (Step D)} (hc : w.Canon E)
    (hb : FloorsBorn E w) (h : World.fold E w l = .ok w') : FloorsBorn E w' :=
  (fold_keeps (P := fun v => v.Canon E ∧ FloorsBorn E v)
    (fun hp ha => ⟨admit_canon hp.1 ha, admit_floorsBorn hp.1 hp.2 ha⟩)
    (fun hp hr => ⟨refuse_canon hp.1 hr, fun d hd => by
      unfold World.floorSum at hd; rw [refuse_sumOf hr] at hd
      obtain ⟨id, hcn, he⟩ := hp.2 d hd
      exact ⟨id, (refuse_taken hr id).trans hcn, he⟩⟩) ⟨hc, hb⟩ h).2


omit [Std.TransOrd D] [Std.LawfulEqOrd D] in
/-- A turn never bears an id the World already holds, so never a held id's denomination (given a
lawful `Env`: its digest bytes are injective): `checkCreates` refuses a live or tombstoned id (`idTaken`). -/
theorem admit_not_born {E : Env D} {n : Nat} {w w' : World D} {t : Turn D}
    (hE : E.Lawful n) (h : World.admit E w t = .ok w')
    {id : D} (hc : w.taken E id = true) : E.bytes id ∉ (createdIds t).map E.bytes := by
  obtain ⟨posts, hk, _⟩ := admit_ok h
  intro hm
  obtain ⟨id', hid, he⟩ := List.mem_map.mp hm
  have := hE.bytes_eq he
  subst this
  have hcr := hk.creates
  unfold checkCreates at hcr
  simp only [except_bind_ok] at hcr
  obtain ⟨⟨⟩, _, ⟨⟩, _, ⟨⟩, _, hfresh⟩ := hcr
  have := (forEx_ok.mp hfresh) id' hid
  rw [req_ok] at this
  simp [hc] at this

/-- **The cap is fixed forever.** Once a World holds the id that names a denomination (its well:
from the turn that bore it on), no admitted log moves that denomination's floor sum. With
`admit_birth` (0 before) and `dispatch_value_born` (the birth sets it to the signed cap). -/
theorem fold_floors_held {E : Env D} {n : Nat} (hE : E.Lawful n) {id : D} :
    ∀ {w w' : World D} {l : List (Step D)}, w.Canon E → World.fold E w l = .ok w' →
      w.taken E id = true → w'.floorSum (E.bytes id) = w.floorSum (E.bytes id)
  | w, w', [], _, h, _ => by simp [World.fold] at h; subst h; rfl
  | w, w', .refusal r :: rest, hcn, h, hc => by
      obtain ⟨w₁, h₁, h₂⟩ := fold_cons_ok.mp h
      rw [fold_floors_held hE (refuse_canon hcn h₁) h₂ ((refuse_taken h₁ id).trans hc)]
      exact refuse_sumOf h₁ _ _
  | w, w', .turn t :: rest, hcn, h, hc => by
      obtain ⟨w₁, h₁, h₂⟩ := fold_cons_ok.mp h
      have hc₁ : w₁.taken E id = true := by
        obtain ⟨posts, _, rfl⟩ := admit_ok h₁
        exact commit_taken (.inl hc)
      rw [fold_floors_held hE (admit_canon hcn h₁) h₂ hc₁,
        admit_floors hcn h₁ (admit_not_born hE h₁ hc)]

/-! ## Genesis holds no value -/

omit [Ord D] in
/-- A cell map none of whose entries is a value cell contributes 0 to every value measure. -/
theorem cellsSum_noValue {E : Env D} {m : Cells D} {g : Flow → Int} {d : ByteArray}
    (hr : Trie.Routed (trieSpec E) 0 m)
    (h : ∀ (s : Slot D) (e : Entry), m.get (trieSpec E) s = some (.entry e) →
      ∀ c : Cell, e = .live c → c.discipline ≠ .value) :
    cellsSum (entrySum g d) m = 0 := by
  unfold cellsSum
  have key : ∀ l : List (Slot D × Leaf), (∀ p ∈ l, m.get (trieSpec E) p.1 = some p.2) →
      (l.map fun p => p.2.sumOf (entrySum g d)).sum = 0 := by
    intro l
    induction l with
    | nil => intro _; rfl
    | cons p rest ih =>
        intro hl
        have hp : p.2.sumOf (entrySum g d) = 0 := by
          obtain ⟨s, l⟩ := p
          cases l with
          | spent => rfl
          | entry e =>
              cases he : e with
              | tomb => simp [Leaf.sumOf, entrySum, Entry.cell?, flowsOf, sumBy]
              | live c =>
                  have hnv := h s e (hl (s, .entry e) (by simp)) c he
                  have : Value.ofCell c = none := by unfold Value.ofCell; simp [hnv]
                  simp [Leaf.sumOf, entrySum, Entry.cell?, flowsOf, this, sumBy]
        simp only [List.map_cons, List.sum_cons, hp, ih (fun q hq => hl q (by simp [hq]))]
        rfl
  exact key _ fun p hp => Trie.get_of_mem _ hr hp

omit [Std.TransOrd D] [Std.LawfulEqOrd D] in
/-- Such a World is within its floors, trivially. -/
theorem floorOk_noValue {E : Env D} {w : World D}
    (h : ∀ (k : D) (e : Entry), w.entry E k = some e → ∀ c : Cell, e = .live c → c.discipline ≠ .value) :
    FloorOk E w := by
  intro k c hl hv
  exact absurd hv (h k _ (live_entry hl) _ rfl)

end Turn

end Nanodregg.Kernel
