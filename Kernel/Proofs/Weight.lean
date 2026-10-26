/-
# Kernel.Proofs.Weight — the budget bounds the World

A turn's charge includes `Turn.growth`, the most it can add to the World; what its touches do not
use of that (a retired cell's weight, a write's ops beyond what the cell grew) is credited back
(KERNEL-15). So storage is CONSERVED: over any admitted log, World storage plus log storage plus
the budget left equal where they started (`fold_conserves`): the allowance budgets turn records and
World weight (not the whole Store: record framing, recorded refusals and the index are not charged).
A turn adds to the World at most `84/61` of its record (`Turn.growth_le_logWeight`, tight at a
pinless declare, `RowTouch.declare_growth_tight`), so the potential `145 · weight + 84 · allowance`
never rises (`fold_potential`, KERNEL-55) and the World stays within `84/145` of its allowance
(`allowance_bounds_world`). Deriving HOST's `worldBytesMax` from it also needs CODEC's World size
equality, which is not yet a theorem (KERNEL-55 part 2).
`fold_world_weight` (weight ≤ weight + allowance) is its weakening. `admit_retire`: retiring gives
back exactly the retired cells' weight.
-/
import Kernel.Proofs.Cells
import Kernel.Proofs.Rows

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
        | set k v => have := slots_weight_set k v s; simp only [applyOp, Op.weight]; omega
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

/-! ## The map's weight under one insertion -/

omit [Ord D] in
/-- Overwriting a slot: the map's weight moves by the difference. -/
theorem cellsWeight_overwrite {E : Env D} {m : Cells D} (hr : Trie.Routed (trieSpec E) 0 m)
    {k : Slot D} {old : Leaf} (v : Leaf) (h : m.get (trieSpec E) k = some old) :
    cellsWeight (m.insert (trieSpec E) k v) + old.weight = cellsWeight m + v.weight :=
  Trie.sumN_insert_some (trieSpec E) (fun p => p.2.weight) hr v h

omit [Ord D] in
/-- A fresh slot: the map's weight grows by exactly the new leaf (its id included). -/
theorem cellsWeight_fresh {E : Env D} {m : Cells D} (hr : Trie.Routed (trieSpec E) 0 m)
    {k : Slot D} (v : Leaf) (h : m.get (trieSpec E) k = none) :
    cellsWeight (m.insert (trieSpec E) k v) = cellsWeight m + v.weight :=
  Trie.sumN_insert_none (trieSpec E) (fun p => p.2.weight) hr v h

/-! ## What one turn adds, and what it gives back -/

section Turn

/-- A touch that changes its cell replaces an existing entry, and the new entry plus what the
touch gives back is exactly the old entry plus the ops it was charged for. -/
theorem touchCheck_weight {E : Env D} {w : World D} {x : Touch D} {p : Post D}
    (h : touchCheck E w x = .ok (some p)) :
    p.cell = x.cell ∧ ∃ old, w.trie.get (trieSpec E) (.cell x.cell) = some (.entry old) ∧
      p.entry.weight + p.freed = old.weight + x.act.opsWeight := by
  unfold touchCheck at h
  simp only [except_bind_ok] at h
  obtain ⟨⟨⟩, _, h⟩ := h
  cases ha : x.act with
  | keep => rw [ha] at h; simp [pure, Except.pure] at h
  | write ops =>
      rw [ha] at h
      cases hc : w.entry E x.cell with
      | none => rw [hc] at h; simp at h
      | some e =>
          cases e with
          | tomb => rw [hc] at h; simp at h
          | live cell v =>
              rw [hc] at h
              simp only [except_bind_ok, pure, Except.pure, Except.ok.injEq, Option.some.injEq] at h
              obtain ⟨⟨⟩, _, post, hp, rfl⟩ := h
              refine ⟨rfl, .live cell v, entry_get hc, ?_⟩
              have := postWrite_weight hp
              simp only [Entry.weight, Act.opsWeight]; omega
  | retire =>
      rw [ha] at h
      cases hc : w.entry E x.cell with
      | none => rw [hc] at h; simp at h
      | some e =>
          cases e with
          | tomb => rw [hc] at h; simp at h
          | live cell v =>
              rw [hc] at h
              simp only [except_bind_ok, pure, Except.pure, Except.ok.injEq, Option.some.injEq] at h
              obtain ⟨⟨⟩, _, rfl⟩ := h
              exact ⟨rfl, .live cell v, entry_get hc, by simp [Entry.weight, Act.opsWeight]⟩

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
      cases hc : w.entry E x.cell with
      | none => rw [hc] at h; simp at h
      | some e =>
          cases e with
          | tomb => rw [hc] at h; simp at h
          | live cell v =>
              rw [hc] at h
              simp only [except_bind_ok, pure, Except.pure] at h
              obtain ⟨⟨⟩, _, _, _, h⟩ := h; simp at h
  | retire =>
      rw [ha] at h
      cases hc : w.entry E x.cell with
      | none => rw [hc] at h; simp at h
      | some e =>
          cases e with
          | tomb => rw [hc] at h; simp at h
          | live cell v =>
              rw [hc] at h
              simp only [except_bind_ok, pure, Except.pure] at h
              obtain ⟨⟨⟩, _, h⟩ := h; simp at h

omit [Ord D] [DecidableEq D] in
theorem credit_cons (p : Post D) (l : List (Post D)) : credit (p :: l) = p.freed + credit l := by
  simp [credit]

theorem touches_weight {E : Env D} {w : World D} :
    ∀ (l : List (Touch D)) (raw : List (Option (Post D))) (m : Cells D),
      Trie.Routed (trieSpec E) 0 m →
      (l.map Touch.cell).Nodup → mapEx (touchCheck E w) l = .ok raw →
      (∀ x ∈ l, m.get (trieSpec E) (.cell x.cell) = w.trie.get (trieSpec E) (.cell x.cell)) →
      cellsWeight (insertAll E m (raw.reduceOption.map Post.pair)) + credit raw.reduceOption =
        cellsWeight m + (l.map fun x => x.act.opsWeight).sum
  | [], raw, m, _, _, h, _ => by
      simp [mapEx] at h; subst h; simp [insertAll, List.reduceOption, credit]
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
                  have := touches_weight rest raw' m hrt hn.2 hr hm'
                  have hk := touchCheck_none hx
                  simp only [List.reduceOption, List.filterMap_cons, id, List.map_cons,
                    List.sum_cons, hk, Act.opsWeight] at this ⊢
                  omega
              | some p =>
                  obtain ⟨hp1, old, hold, hw⟩ := touchCheck_weight hx
                  have hmx : m.get (trieSpec E) (.cell p.cell) = some (.entry old) := by
                    rw [hp1, hm x (by simp), hold]
                  have hins := cellsWeight_overwrite hrt (.entry p.entry) hmx
                  simp only [Leaf.weight] at hins
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
                  have := touches_weight rest raw' _ (Trie.routed_insert _ _ _ hrt) hn.2 hr hm''
                  simp only [List.reduceOption, List.filterMap_cons, id, List.map_cons,
                    List.sum_cons] at this ⊢
                  rw [credit_cons]
                  show cellsWeight (insertAll E (m.insert (trieSpec E) (.cell p.cell) (.entry p.entry)) _)
                    + _ = _
                  omega

/-- What a turn that only keeps and retires gives back: exactly the weight of each cell it
retires (KERNEL-15). -/
theorem credit_retires {E : Env D} {w : World D} :
    ∀ (l : List (Touch D)) (raw : List (Option (Post D))),
      mapEx (touchCheck E w) l = .ok raw → (∀ x ∈ l, x.act = .keep ∨ x.act = .retire) →
      credit raw.reduceOption =
        ((l.filter fun x => x.act == .retire).map fun x => ((w.entry E x.cell).map Entry.weight).getD 0).sum
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
                cases hc : w.entry E x.cell with
                | none => rw [hc] at hx; simp at hx
                | some e =>
                    cases e with
                    | tomb => rw [hc] at hx; simp at hx
                    | live cell v =>
                        rw [hc] at hx
                        simp only [except_bind_ok, pure, Except.pure, Except.ok.injEq] at hx
                        obtain ⟨_, _, rfl⟩ := hx
                        simp only [List.reduceOption, List.filterMap_cons, id, List.filter_cons, hk,
                          beq_self_eq_true, if_true, List.map_cons, List.sum_cons, hc, Option.map_some,
                          Option.getD_some] at ih ⊢
                        rw [credit_cons]
                        simp only [Entry.weight]
                        omega

omit [Ord D] [DecidableEq D] in
private theorem sum_map_mul_le {α : Type} (f g : α → Nat) (a b : Nat) (h : ∀ x, a * f x ≤ b * g x) :
    ∀ l : List α, a * (l.map f).sum ≤ b * (l.map g).sum
  | [] => by simp
  | x :: l => by
      have := sum_map_mul_le f g a b h l
      have := h x
      simp only [List.map_cons, List.sum_cons, Nat.mul_add]; omega

omit [Ord D] [DecidableEq D] in
/-- A row touch adds to the World at most `84/61` of its log bytes. -/
theorem RowTouch.growth_le_weight (x : RowTouch D) : 61 * x.growth ≤ 84 * x.weight := by
  rcases x with ⟨slot, seen, act⟩
  cases slot with
  | head p rel =>
      have := natBytes_size_pos rel
      cases act <;>
        simp only [RowTouch.growth, RowTouch.weight, RowSlot.weight, RowLeaf.weight, RowAct.logWeight,
          digestWeight, counterWeight, headerWeight] <;> split <;> omega
  | row key =>
      have := natBytes_size_pos key.rel
      have := natBytes_size_pos key.k.size
      cases act <;>
        simp only [RowTouch.growth, RowTouch.weight, RowSlot.weight, RowLeaf.weight, RowAct.logWeight,
          digestWeight, counterWeight, headerWeight] <;> split <;> omega

omit [Ord D] [DecidableEq D] in
/-- **A turn adds to the World at most `84/61` of its log record** (KERNEL-55): term by term, a
create (`40 + w` against `32 + w`), a write's ops (against its act), a nullifier (32 against 32), an
insert or upsert, and a declare at a head (84 against 61, the tight term: the head's floor, count and
sum are World bytes the log does not carry). -/
theorem Turn.growth_le_logWeight (t : Turn D) : 61 * t.growth ≤ 84 * t.logWeight := by
  have hc := sum_map_mul_le (fun p : D × Cell => digestWeight + counterWeight + p.2.weight)
    (fun p => digestWeight + p.2.weight) 61 84
    (fun p => by simp only [digestWeight, counterWeight]; omega) t.creates
  have ht := sum_map_mul_le (fun x : Touch D => x.act.opsWeight) Touch.weight 61 84
    (fun x => by
      rcases x with ⟨c, s, a⟩
      cases a <;> simp only [Act.opsWeight, Touch.weight, Act.logWeight, headerWeight, digestWeight] <;> omega)
    t.touches
  have hr := sum_map_mul_le RowTouch.growth RowTouch.weight 61 84 RowTouch.growth_le_weight t.rows
  simp only [Turn.growth, Turn.logWeight, Nat.mul_add] at *
  omega

omit [Ord D] [DecidableEq D] in
/-- **The tooth: `84/61` is attained** by a row touch, a declare at a head of a relation below 128 (a
one-byte `natBytes`) with no pin (growth 84, log 61), so `RowTouch.growth_le_weight`'s ratio cannot be
lowered. A relation of 128 or more has a two-byte slot on both sides, and a lower ratio. At turn level
(80 fixed log bytes per turn) 84/61 is the supremum over unboundedly many such declares, not an
attained value. -/
theorem RowTouch.declare_growth_tight (p : D) {rel : Nat} (hrel : rel < 128) (limit cap width : Nat)
    (retract : Bool) :
    61 * (RowTouch.mk (.head p rel) none (.declare limit cap width retract)).growth =
      84 * (RowTouch.mk (.head p rel) none (.declare limit cap width retract)).weight := by
  have h1 : (natBytes rel).size = 1 := by rw [natBytes_eq, Nanodregg.Codec.Stream.varint_bytes_small hrel]; rfl
  simp [RowTouch.growth, RowTouch.weight, RowSlot.weight, RowLeaf.weight, RowAct.logWeight,
    digestWeight, counterWeight, h1]

end Turn

section World

omit [Ord D] [DecidableEq D] in
theorem noDup_nodup {α : Type} [Ord α] [Std.TransOrd α] [Std.LawfulEqOrd α] {l : List α}
    {e : α → Reject D} (h : noDup l e = .ok ()) : l.Nodup := by
  unfold noDup at h
  split at h
  · rename_i hf; exact firstDup_none hf
  · simp at h

omit [Ord D] in
theorem born_weight {E : Env D} :
    ∀ (ps : List (D × Cell)) (m : Cells D), Trie.Routed (trieSpec E) 0 m → (ps.map Prod.fst).Nodup →
      (∀ p ∈ ps, m.get (trieSpec E) (.cell p.1) = none) →
      cellsWeight (insertAll E m (ps.map fun p => (p.1, Entry.live p.2 0))) =
        cellsWeight m + (ps.map fun p => digestWeight + counterWeight + p.2.weight).sum
  | [], m, _, _, _ => by simp [insertAll]
  | p :: rest, m, hrt, hn, hf => by
      simp only [List.map_cons, List.nodup_cons] at hn
      have hf' : ∀ q ∈ rest, (m.insert (trieSpec E) (.cell p.1) (.entry (.live p.2 0))).get
          (trieSpec E) (.cell q.1) = none := by
        intro q hq
        rw [Trie.get_insert_ne]
        · exact hf q (by simp [hq])
        · intro he
          injection he with he
          apply hn.1
          rw [← he]
          exact List.mem_map_of_mem hq
      have ih := born_weight rest _ (Trie.routed_insert _ _ _ hrt) hn.2 hf'
      have h1 := cellsWeight_fresh hrt (.entry (.live p.2 0)) (hf p (by simp))
      simp only [List.map_cons, List.sum_cons]
      show cellsWeight (insertAll E (m.insert (trieSpec E) (.cell p.1) (.entry (.live p.2 0))) _) = _
      rw [ih, h1]; simp [Leaf.weight, Entry.weight]; omega

omit [Ord D] in
/-- Fresh, distinct nullifiers grow the map's weight by exactly one id each. -/
theorem spendAll_weight {E : Env D} :
    ∀ (m : Cells D) (ns : List D), Trie.Routed (trieSpec E) 0 m → ns.Nodup →
      (∀ n ∈ ns, m.get (trieSpec E) (.nullifier n) = none) →
      cellsWeight (spendAll E m ns) = cellsWeight m + digestWeight * ns.length
  | m, [], _, _, _ => by simp [spendAll]
  | m, n :: rest, hrt, hn, hf => by
      simp only [List.nodup_cons] at hn
      have hf' : ∀ k ∈ rest, (m.insert (trieSpec E) (.nullifier n) .spent).get
          (trieSpec E) (.nullifier k) = none := by
        intro k hk
        rw [Trie.get_insert_ne]
        · exact hf k (by simp [hk])
        · intro he; injection he with he; apply hn.1; rw [← he]; exact hk
      have ih := spendAll_weight _ rest (Trie.routed_insert _ _ _ hrt) hn.2 hf'
      have h1 := cellsWeight_fresh hrt .spent (hf n (by simp))
      show cellsWeight (spendAll E (m.insert (trieSpec E) (.nullifier n) .spent) rest) = _
      have e1 : Leaf.weight .spent = digestWeight := rfl
      have e2 : (n :: rest).length = rest.length + 1 := rfl
      rw [ih, h1, e1, e2, Nat.mul_succ]; omega

theorem receive_genesis_slotted (X : Receive.Ctx D) (name nonce : ByteArray) (allowance : Nat)
    (founders : List (ByteArray × D)) (auth : Receive.Authority) : (Receive.genesisWorld X name nonce allowance founders auth).Slotted X.env :=
  insertAll_fits _ (fun s _ hg => nomatch hg.symm.trans (Trie.get_empty (trieSpec X.env) s))

variable [Std.TransOrd D] [Std.LawfulEqOrd D]

/-- **An admitted turn moves storage exactly.** The World (cells and rows) grows by the turn's
growth less what its touches and its row touches give back. -/
theorem admit_world_weight {E : Env D} {w w' : World D} {t : Turn D} {posts : List (Post D)}
    (hc : w.Canon E) (hf : w.Slotted E) (hr : w.RowsCanon E) (hk : Checked E w t posts)
    (h : w' = commit E w t posts) :
    w'.weight + credit posts + (rowsAfter E w t).2 = w.weight + t.growth := by
  subst h
  obtain ⟨raw, hm, hposts⟩ := hk.touches
  have hshape := hk.shape
  unfold checkShape at hshape
  simp only [except_bind_ok] at hshape
  obtain ⟨⟨⟩, hnt, ⟨⟩, hnn, _⟩ := hshape
  have hcr := hk.creates
  unfold checkCreates at hcr
  simp only [except_bind_ok] at hcr
  obtain ⟨⟨⟩, _, ⟨⟩, hnb, ⟨⟩, hnbt, hfresh⟩ := hcr
  have nt := noDup_nodup hnt
  have nb := noDup_nodup hnb
  have nbt := noDup_nodup hnbt
  have nn := noDup_nodup hnn
  -- the touches
  have ht := touches_weight t.touches raw w.trie hc.1 nt hm (fun _ _ => rfl)
  rw [← hposts] at ht
  -- the births
  have hids : t.creates.map Prod.fst = createdIds t := rfl
  have hpk : ∀ p ∈ posts, p.cell ∈ t.touches.map Touch.cell := by
    intro p hp
    obtain ⟨x, hx, he, _⟩ := posts_touched hk p hp
    rw [he]; exact List.mem_map_of_mem hx
  have hfr : ∀ p ∈ t.creates,
      (insertAll E w.trie (posts.map Post.pair)).get (trieSpec E) (.cell p.1) = none := by
    intro p hp
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
    apply get_cell_none hf
    cases he : w.entry E p.1 with
    | none => rfl
    | some e => simp [World.taken, he] at this
  have hr₁ := (insertAll_canon (posts.map Post.pair) hc).1
  have hb := born_weight t.creates (insertAll E w.trie (posts.map Post.pair)) hr₁
    (by rw [hids]; exact nb) hfr
  -- every nullifier is new
  have hr₂ := (insertAll_canon (bornEntries t) (insertAll_canon (posts.map Post.pair) hc)).1
  have hs := spendAll_weight (E := E)
    (insertAll E (insertAll E w.trie (posts.map Post.pair)) (bornEntries t)) t.nullifiers hr₂ nn
    (by
      intro n hn
      have := (forEx_ok.mp hk.nullifiers) n hn
      rw [req_ok] at this
      rw [insertAll_get_nullifier, insertAll_get_nullifier]
      cases hg : w.trie.get (trieSpec E) (.nullifier n) with
      | none => rfl
      | some l => simp [World.isSpent, hg] at this)
  unfold World.weight commit commitWith Turn.growth
  dsimp only
  have hcw : cellsWeight (insertAll E (insertAll E w.trie (posts.map Post.pair)) (bornEntries t)) +
      credit posts = cellsWeight w.trie + (t.touches.map fun x => x.act.opsWeight).sum +
        (t.creates.map fun p => digestWeight + counterWeight + p.2.weight).sum := by
    unfold bornEntries; rw [hb]; omega
  rw [commitTrie_eq, hs]
  have hrw := rowsAfter_weight hr hk
  omega

/-- **Storage is conserved.** An admitted turn's World storage, plus its log record, plus the
budget left, is exactly the World storage and budget before it: nothing is created or lost, a
retirement or a shrinking write hands its bytes back to the budget. -/
theorem admit_conserves {E : Env D} {w w' : World D} {t : Turn D} (hc : w.Canon E) (hf : w.Slotted E)
    (hr : w.RowsCanon E) (h : World.admit E w t = .ok w') :
    w'.weight + t.logWeight + w'.allowance = w.weight + w.allowance := by
  obtain ⟨hch, posts, hk, _, hal⟩ := admit_charge h
  obtain ⟨posts', hk', hw'⟩ := admit_ok h
  have : posts' = posts := by
    obtain ⟨r1, h1, e1⟩ := hk.touches
    obtain ⟨r2, h2, e2⟩ := hk'.touches
    rw [h1] at h2; cases h2; rw [e1, e2]
  subst this
  have hw := admit_world_weight hc hf hr hk' hw'
  unfold Turn.weight at hch
  omega

omit [Std.TransOrd D] [Std.LawfulEqOrd D] in
/-- **Credit on retirement** (KERNEL-15). A turn that only keeps and retires cells leaves the
budget at what it was, plus the weight of every cell it retired, plus what its row touches give
back (`rowsAfter`; nothing for a turn with no row touches), less its charge. -/
theorem admit_retire {E : Env D} {w w' : World D} {t : Turn D}
    (h : World.admit E w t = .ok w') (ha : ∀ x ∈ t.touches, x.act = .keep ∨ x.act = .retire) :
    w'.allowance + t.charge = w.allowance +
      ((t.touches.filter fun x => x.act == .retire).map fun x =>
        ((w.entry E x.cell).map Entry.weight).getD 0).sum + (rowsAfter E w t).2 := by
  obtain ⟨_, posts, hk, _, hal⟩ := admit_charge h
  obtain ⟨raw, hm, rfl⟩ := hk.touches
  rw [hal, credit_retires t.touches raw hm ha]

/-- **The budget bounds the World, exactly.** Over any admitted log, the World's storage plus the
storage of the log's TURN records plus the budget left equal the World's storage and budget at the
start. Recorded refusals are not charged to the budget (KERNEL-44): their log bytes are bounded by
rate instead, `Bounds.refusalsPerWindow` per member per window (`fold_member_refusals_le`). -/
theorem fold_conserves {E : Env D} :
    ∀ {w w' : World D} {l : List (Step D)}, w.Canon E → w.Slotted E → w.RowsCanon E →
      World.fold E w l = .ok w' →
      w'.weight + ((Step.turns l).map Turn.logWeight).sum + w'.allowance = w.weight + w.allowance
  | w, w', [], _, _, _, h => by simp [World.fold] at h; subst h; simp [Step.turns]
  | w, w', .turn t :: rest, hc, hf, hr, h => by
      obtain ⟨w₁, h₁, h₂⟩ := fold_cons_ok.mp h
      have ih := fold_conserves (admit_canon hc h₁) (admit_slotted hf h₁) (admit_rowsCanon hr h₁) h₂
      have hw := admit_conserves hc hf hr h₁
      simp only [Step.turns, List.map_cons, List.sum_cons]
      omega
  | w, w', .refusal r :: rest, hc, hf, hr, h => by
      obtain ⟨w₁, h₁, h₂⟩ := fold_cons_ok.mp h
      have ih := fold_conserves (refuse_canon hc h₁)
        (fun s l hg => hf s l (by rw [← refuse_trie h₁]; exact hg)) (refuse_rowsCanon hr h₁) h₂
      obtain ⟨ht, -, -, ha, -⟩ := refuse_frame h₁
      have hw : w₁.weight = w.weight := by unfold World.weight; rw [ht, refuse_rows h₁]
      simp only [Step.turns]
      omega

/-- A World folded from `w` never holds more than `w`'s storage plus its budget, whatever it admits
and retires. The weak form: `allowance_bounds_world` is the stronger one (`84/145` of the
allowance). -/
theorem fold_world_weight {E : Env D} {w w' : World D} {l : List (Step D)} (hc : w.Canon E)
    (hf : w.Slotted E) (hr : w.RowsCanon E) (h : World.fold E w l = .ok w') :
    w'.weight ≤ w.weight + w.allowance := by
  have := fold_conserves hc hf hr h; omega

/-- **The potential never rises over a turn** (KERNEL-55). -/
theorem admit_potential {E : Env D} {w w' : World D} {t : Turn D} (hc : w.Canon E) (hf : w.Slotted E)
    (hr : w.RowsCanon E) (h : World.admit E w t = .ok w') : potential w' ≤ potential w := by
  have hcons := admit_conserves hc hf hr h
  obtain ⟨posts', hk', hw'⟩ := admit_ok h
  have hww := admit_world_weight hc hf hr hk' hw'
  have hg := Turn.growth_le_logWeight t
  simp only [potential, potentialRatio]
  omega

/-- **The potential never rises over a fold**: a turn by `admit_potential`; a recorded refusal
leaves weight and allowance alone (`refuse_frame`). -/
theorem fold_potential {E : Env D} :
    ∀ {w w' : World D} {l : List (Step D)}, w.Canon E → w.Slotted E → w.RowsCanon E →
      World.fold E w l = .ok w' → potential w' ≤ potential w
  | w, w', [], _, _, _, h => by simp [World.fold] at h; subst h; exact Nat.le_refl _
  | w, w', .turn t :: rest, hc, hf, hr, h => by
      obtain ⟨w₁, h₁, h₂⟩ := fold_cons_ok.mp h
      have ih := fold_potential (admit_canon hc h₁) (admit_slotted hf h₁) (admit_rowsCanon hr h₁) h₂
      have := admit_potential hc hf hr h₁
      omega
  | w, w', .refusal r :: rest, hc, hf, hr, h => by
      obtain ⟨w₁, h₁, h₂⟩ := fold_cons_ok.mp h
      have ih := fold_potential (refuse_canon hc h₁)
        (fun s l hg => hf s l (by rw [← refuse_trie h₁]; exact hg)) (refuse_rowsCanon hr h₁) h₂
      obtain ⟨ht, -, -, ha, -⟩ := refuse_frame h₁
      have hw : w₁.weight = w.weight := by unfold World.weight; rw [ht, refuse_rows h₁]
      have : potential w₁ = potential w := by simp only [potential, hw, ha]
      omega

/-- **The allowance bounds the World at `84/145` of itself** (KERNEL-55, ROOT's Q1 = B): every
World a fold reaches from `w` has `145 · weight ≤ 145 · w.weight + 84 · w.allowance`. HOST's
World bound is to follow from this theorem (a World's weight is at most `w.weight + ⌊84 · w.allowance / 145⌋`,
the floor valid since weights are whole numbers), with CODEC's size equality (KERNEL-55 part 2). -/
theorem allowance_bounds_world {E : Env D} {w w' : World D} {l : List (Step D)} (hc : w.Canon E)
    (hf : w.Slotted E) (hr : w.RowsCanon E) (h : World.fold E w l = .ok w') :
    potentialRatio.2 * w'.weight ≤ potential w := by
  have := fold_potential hc hf hr h
  simp only [potential, potentialRatio] at *
  omega

end World

end Nanodregg.Kernel
