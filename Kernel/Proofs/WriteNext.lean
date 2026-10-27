/-
# Kernel.Proofs.WriteNext — what a write or a law change leaves, and every cell stays canonical

`invoke_next_slots` (`Kernel.Proofs.InvokeNext`) says the state an admitted invoke leaves reads, key
by key, what its run returned; the run's state passed `checkState`, so its `diffOps` write is
exact. A `write` has no such check: its new state is `applyEdits` of the cell's state, and that is
canonical only when the cell is. So the write's link rests on a World invariant, proved here:

* `CellsCanon E w`: every live cell's slots are strictly ascending (`Slots.ascending`, the form
  `checkShape` demands of a birth). `admit_cellsCanon`: every admitted turn keeps it (a birth is
  checked `nonCanonicalCell`; a write's `set`/`erase` keep the order); `fold_cellsCanon`
  (along every fold, the follower's too); `genesis_cellsCanon`: the founders' cells are `slotsOf`, so genesis has it.
* `write_next_slots`: a signed `write` of `obj` derived from `w` and admitted to `w'`, over a
  canonical cell: the laws in force judged the move to `applyEdits (stateOf cell) edits`
  (`write_judged`), and `obj` is live in `w'` with a state that reads that, key by key.
* `law_next_slots`: a signed `law` turn changes only law slots: `obj` is live in `w'` and its state
  reads, key by key, what it read before (no canonicity premise: law keys are below `stateBase`).
* `retire_next`, `retire_next_tomb` (KERNEL-70): a signed `retire` of a live object, derived: its
  owner signed it, every law in force (its package's, then its cell's) judged the occasion `retire`
  over its last state, unchanged; admitted, `w'` holds its tombstone. `retire_final`: every later
  fold keeps it (every grant over the object is dead); `retire_frees_credit`: the allowance gains
  the object's weight, once, plus its heads'.

Tooth: `write_needs_canon`: on a cell holding key 16 twice, the edit-free write's own `diffOps` is
one `set` (distinct keys, so `checkShape` admits it) that re-sets the FIRST entry to the second
value: the state the cell then reads is not the state the laws judged, so `write_next_slots`'
canonicity premise is load-bearing, and `CellsCanon` is what discharges it. `law_slots_need_bound`:
`checkLaws` refuses a fifteenth law, whose slot would be `stateBase`.
-/
import Kernel.Proofs.InvokeNext
import Kernel.Proofs.Rooted
import Kernel.Proofs.Versions
import Kernel.Proofs.Weight

namespace Nanodregg.Kernel.Receive

open Nanodregg.Kernel

/-! ## Ascending slots -/

private theorem foldl_inv {α β : Type} (P : α → Prop) (f : α → β → α) (hf : ∀ a b, P a → P (f a b)) :
    ∀ (l : List β) (a : α), P a → P (l.foldl f a)
  | [], _, h => h
  | b :: rest, a, h => foldl_inv P f hf rest (f a b) (hf a b h)

/-- `Slots.ascending` is strict sortedness by key. -/
theorem ascending_iff : ∀ s : Slots, Slots.ascending s = true ↔ s.Pairwise (fun a b => a.1 < b.1)
  | [] => by simp [Slots.ascending]
  | [_] => by simp [Slots.ascending]
  | a :: b :: rest => by
      simp only [Slots.ascending, Bool.and_eq_true, decide_eq_true_eq, ascending_iff (b :: rest)]
      constructor
      · rintro ⟨hab, hp⟩
        refine List.pairwise_cons.mpr ⟨fun q hq => ?_, hp⟩
        rcases List.mem_cons.mp hq with rfl | hq
        · exact hab
        · exact Nat.lt_trans hab ((List.pairwise_cons.mp hp).1 q hq)
      · intro h
        exact ⟨(List.pairwise_cons.mp h).1 b (List.mem_cons_self ..), (List.pairwise_cons.mp h).2⟩

theorem mem_set {k : Nat} {v : ByteArray} :
    ∀ {s : Slots} {q : Nat × ByteArray}, q ∈ Slots.set k v s → q = (k, v) ∨ q ∈ s
  | [], q, h => by simp [Slots.set] at h; exact .inl h
  | (k', v') :: rest, q, h => by
      simp only [Slots.set] at h
      by_cases hlt : k < k'
      · rw [if_pos hlt] at h
        simp only [List.mem_cons] at h
        rcases h with h | h | h
        · exact .inl h
        · exact .inr (h ▸ List.mem_cons_self ..)
        · exact .inr (List.mem_cons_of_mem _ h)
      · rw [if_neg hlt] at h
        by_cases heq : k = k'
        · rw [if_pos heq] at h
          simp only [List.mem_cons] at h
          rcases h with h | h
          · exact .inl h
          · exact .inr (List.mem_cons_of_mem _ h)
        · rw [if_neg heq] at h
          simp only [List.mem_cons] at h
          rcases h with h | h
          · exact .inr (h ▸ List.mem_cons_self ..)
          · rcases mem_set h with h | h
            · exact .inl h
            · exact .inr (List.mem_cons_of_mem _ h)

theorem set_pairwise {k : Nat} {v : ByteArray} :
    ∀ {s : Slots}, s.Pairwise (fun a b => a.1 < b.1) → (Slots.set k v s).Pairwise (fun a b => a.1 < b.1)
  | [], _ => by simp [Slots.set]
  | (k', v') :: rest, h => by
      have h1 := (List.pairwise_cons.mp h).1
      have h2 := (List.pairwise_cons.mp h).2
      simp only [Slots.set]
      by_cases hlt : k < k'
      · rw [if_pos hlt]
        refine List.pairwise_cons.mpr ⟨fun q hq => ?_, h⟩
        rcases List.mem_cons.mp hq with rfl | hq
        · exact hlt
        · exact Nat.lt_trans hlt (h1 q hq)
      rw [if_neg hlt]
      by_cases heq : k = k'
      · rw [if_pos heq]
        subst heq
        exact List.pairwise_cons.mpr ⟨h1, h2⟩
      · rw [if_neg heq]
        refine List.pairwise_cons.mpr ⟨fun q hq => ?_, set_pairwise h2⟩
        rcases mem_set hq with rfl | hq
        · show k' < k; omega
        · exact h1 q hq

private theorem erase_sublist {k : Nat} : ∀ s : Slots, (Slots.erase k s).Sublist s
  | [] => by simp [Slots.erase]
  | (k', v') :: rest => by
      simp only [Slots.erase]
      by_cases h : k = k'
      · rw [if_pos h]; exact List.sublist_cons_self _ _
      · rw [if_neg h]; exact (erase_sublist rest).cons_cons _

/-- The ordered-and-at-least-`lo` shape of a canonical state. -/
private def Canon (lo : Nat) (s : Slots) : Prop :=
  s.Pairwise (fun a b => a.1 < b.1) ∧ ∀ q ∈ s, lo ≤ q.1

private theorem applyEdits_canon {s : Slots} (h : Canon stateBase s) (edits : List (Nat × Option ByteArray)) :
    Canon stateBase (applyEdits s edits) := by
  unfold applyEdits
  refine foldl_inv (Canon stateBase) _ (fun s e hs => ?_) edits s h
  obtain ⟨hp, hk⟩ := hs
  cases e.2 with
  | some v =>
      refine ⟨set_pairwise hp, fun q hq => ?_⟩
      rcases mem_set hq with rfl | hq
      · show stateBase ≤ stateBase + e.1; omega
      · exact hk q hq
  | none => exact ⟨hp.sublist (erase_sublist s), fun q hq => hk q ((erase_sublist s).subset hq)⟩

private theorem applyOps_pairwise :
    ∀ (ops : List Op) (s : Slots), s.Pairwise (fun a b => a.1 < b.1) →
      (applyOps s ops).Pairwise (fun a b => a.1 < b.1) := by
  intro ops s h
  unfold applyOps
  refine foldl_inv (fun s : Slots => s.Pairwise (fun a b => a.1 < b.1)) _ (fun s o hs => ?_) ops s h
  cases o with
  | set k v => exact set_pairwise hs
  | erase k => exact hs.sublist (erase_sublist s)

private theorem stateOf_canon {cell : Cell} (h : Slots.ascending cell.slots = true) :
    Canon stateBase (stateOf cell) :=
  ⟨((ascending_iff _).mp h).filter _, fun q hq => by
    simp only [stateOf, List.mem_filter, decide_eq_true_eq] at hq; exact hq.2⟩

private theorem checkStateFrom_of {D : Type} :
    ∀ (lo : Nat) (s : Slots), Canon lo s → checkStateFrom (D := D) lo s = .ok ()
  | _, [], _ => rfl
  | lo, p :: rest, ⟨hp, hk⟩ => by
      have h1 : lo ≤ p.1 := hk p (List.mem_cons_self ..)
      simp only [checkStateFrom, req, decide_eq_true h1, if_true, bind, Except.bind]
      exact checkStateFrom_of (p.1 + 1) rest
        ⟨(List.pairwise_cons.mp hp).2, fun q hq => (List.pairwise_cons.mp hp).1 q hq⟩

/-- **An edited canonical state is a canonical state**: `applyEdits` of a canonical cell's state
passes `checkState`, as a run's state must. -/
theorem applyEdits_checkState {D : Type} {cell : Cell} (h : Slots.ascending cell.slots = true)
    (edits : List (Nat × Option ByteArray)) : checkState (D := D) (applyEdits (stateOf cell) edits) = .ok () :=
  checkStateFrom_of _ _ (applyEdits_canon (stateOf_canon h) edits)

/-! ## Every live cell is canonical -/

/-- **Every live cell's slots are canonical**: strictly ascending by key, the form `checkShape`
demands of a birth. -/
def CellsCanon {D : Type} [Ord D] [DecidableEq D] (E : Env D) (w : World D) : Prop :=
  ∀ id cell, w.live E id = some cell → Slots.ascending cell.slots = true

variable {D : Type} [Ord D] [DecidableEq D]

/-- **The kernel keeps every cell canonical** whatever turn it admits: a birth passed
`checkShape`'s `nonCanonicalCell`, a write's `set`/`erase` keep the order. -/
theorem admit_cellsCanon {E : Env D} {w w' : World D} {t : Turn D} (hw : CellsCanon E w)
    (h : World.admit E w t = .ok w') : CellsCanon E w' := by
  intro id c' hl
  rcases admit_live h hl with hb | ⟨cell, hold, rfl | ⟨ops, hp⟩⟩
  · obtain ⟨posts, hk, _⟩ := admit_ok h
    have hs := hk.shape
    unfold checkShape at hs
    simp only [except_bind_ok] at hs
    obtain ⟨⟨⟩, -, ⟨⟩, -, ⟨⟩, -, hf⟩ := hs
    obtain ⟨i, hi⟩ := List.mem_iff_getElem.mp hb
    have hz : ((id, c'), i) ∈ t.creates.zipIdx := by
      rw [List.mem_zipIdx_iff_getElem?]
      simp [List.getElem?_eq_getElem hi.1, hi.2]
    have := (forEx_ok.mp hf) _ hz
    rwa [req_ok] at this
  · exact hw id _ hold
  · unfold postWrite at hp
    have hc := hw id cell hold
    split at hp
    · cases hp
    all_goals
      simp only [except_bind_ok, pure, Except.pure, Except.ok.injEq] at hp
      obtain ⟨⟨⟩, -, hp⟩ := hp
      first
        | (obtain ⟨⟨⟩, -, rfl⟩ := hp
           exact (ascending_iff _).mpr (applyOps_pairwise ops _ ((ascending_iff _).mp hc)))
        | (subst hp
           exact (ascending_iff _).mpr (applyOps_pairwise ops _ ((ascending_iff _).mp hc)))

/-- **Every cell stays canonical along a fold.** -/
theorem fold_cellsCanon {E : Env D} {w w' : World D} {l : List (Step D)} (hw : CellsCanon E w)
    (h : World.fold E w l = .ok w') : CellsCanon E w' :=
  fold_keeps (P := fun v => CellsCanon E v) admit_cellsCanon
    (fun hp hr => fun id cell hl => hp id cell ((refuse_live hr id).symm.trans hl)) hw h

omit [Ord D] [DecidableEq D] in
theorem slotsOf_ascending (ps : List (Nat × ByteArray)) : Slots.ascending (slotsOf ps) = true := by
  unfold slotsOf
  refine (ascending_iff _).mpr (foldl_inv (fun s : Slots => s.Pairwise (fun a b => a.1 < b.1)) _
    (fun s p hs => set_pairwise hs) ps [] List.Pairwise.nil)

/-- **Genesis is canonical**: the founders' member and root grant cells and the authority cell are
`slotsOf`. -/
theorem genesis_cellsCanon (X : Ctx D) (name nonce : ByteArray) (allowance : Nat)
    (founders : List (ByteArray × D)) (auth : Authority) :
    CellsCanon X.env (genesisWorld X name nonce allowance founders auth) := by
  intro id cell hl
  rcases mem_genesisEntries (genesis_live hl) with hm | ⟨-, he⟩
  case inr =>
    injection he with he _
    subst he
    exact slotsOf_ascending _
  obtain ⟨p, _, ⟨_, he⟩ | ⟨_, he⟩⟩ := mem_founderEntries hm
  · injection he with he _
    subst he
    exact slotsOf_ascending _
  · injection he with he _
    subst he
    exact slotsOf_ascending _

/-! ## A write, derived and admitted -/

omit [Ord D] in
private theorem actFor_single {obj : D} {a : Act} : actFor [(obj, a)] obj = a := by
  simp [actFor, List.find?]

/-- The signed Body's receiver, alone: a non-invoke signed call's Draft is its receiver's. -/
private theorem receive_root {X : Ctx D} {w : World D} {c : Call D} {t : Turn D}
    (hc : receive X w c = .ok t) :
    ∃ r, dispatch X (pinned X.env w c.unsigned.pins) (rowView X.env w c.unsigned) c
        (tree X (pinned X.env w c.unsigned.pins) (rowView X.env w c.unsigned) c Bounds.callDepthMax)
        ⟨[], poolOf c.unsigned.body, 0⟩ c.unsigned.member c.unsigned.body = .ok r ∧
      sealTurn X c r.1.creates r.1.effects r.1.nullifiers r.1.rows (poolOf c.unsigned.body - r.2.pool) = .ok t := by
  obtain ⟨-, hw⟩ := receive_ok_with hc
  obtain ⟨-, d, k, hd, hs⟩ := receiveWith_sealed hw
  unfold deriveWithTicks at hd
  cases hR : dispatch X (pinned X.env w c.unsigned.pins) (rowView X.env w c.unsigned) c
      (tree X (pinned X.env w c.unsigned.pins) (rowView X.env w c.unsigned) c Bounds.callDepthMax)
      ⟨[], poolOf c.unsigned.body, 0⟩ c.unsigned.member c.unsigned.body with
  | error e => rw [hR] at hd; cases hd
  | ok r =>
      rw [hR] at hd
      simp only [Except.map, Except.ok.injEq, Prod.mk.injEq] at hd
      obtain ⟨rfl, rfl⟩ := hd
      exact ⟨r, rfl, hs⟩

/-- An admitted turn whose one act at a live, pinned cell is `writeOf obj ops`: the cell is live
after, with `ops` applied (or kept, when there are none), `ops`' keys distinct. -/
private theorem admit_writeOf {X : Ctx D} {w w' : World D} {c : Call D} {t : Turn D} {obj : D}
    {cell : Cell} {ops : List Op} {cr : List (D × Cell)} {ns : List D} {rs : List (RowSlot D × RowAct)}
    {k : Nat} (hs : sealTurn X c cr (writeOf obj ops) ns rs k = .ok t) (ha : World.admit X.env w t = .ok w')
    (hl : w.live X.env obj = some cell) (hp : ∃ q ∈ c.unsigned.pins, q.1 = obj) :
    w'.live X.env obj = some { cell with slots := applyOps cell.slots ops } ∧ (opKeys ops).Nodup := by
  obtain ⟨-, -, htouch, -⟩ := sealTurn_ok hs
  have hact : ∀ x ∈ t.touches, x.cell = obj → x.act = if ops.isEmpty then .keep else .write ops := by
    intro x hx hxc
    rw [htouch] at hx
    obtain ⟨q', -, rfl⟩ := List.mem_map.mp hx
    simp only at hxc ⊢
    rw [hxc]
    exact actFor_single
  by_cases he : ops.isEmpty = true
  · have hnil : ops = [] := List.isEmpty_iff.mp he
    subst hnil
    obtain ⟨posts, hk, -⟩ := admit_ok ha
    have hframe := admit_frame (c := obj) ha (fun x hx hxc => by rw [hact x hx hxc, if_pos he])
      (live_not_created hk hl)
    refine ⟨?_, List.nodup_nil⟩
    unfold World.live; rw [hframe]; exact hl
  · obtain ⟨q, hq, hqc⟩ := hp
    exact admit_live_write ha hl ⟨_, by rw [htouch]; exact List.mem_map.mpr ⟨q, hq, rfl⟩, hqc⟩
      (fun x hx hxc => by rw [hact x hx hxc, if_neg he])

/-- **A write leaves exactly the state its laws judged.** A signed `write` of `obj`, derived from
`w` and admitted to `w'`, over a canonical cell (`CellsCanon` gives it at every World a fold
reaches from genesis): the laws in force judged, on `write`, the move from the cell's state to
`applyEdits` of it (`write_judged`), and `obj` is live in `w'` with a state that reads that edited
state at every key, its slots still canonical. -/
theorem write_next_slots {X : Ctx D} {w w' : World D} {c : Call D} {t : Turn D} {obj : D}
    {edits : List (Nat × Option ByteArray)} {via : Option D} {cell : Cell}
    (hc : receive X w c = .ok t) (ha : World.admit X.env w t = .ok w')
    (hb : c.unsigned.body = .write obj edits via) (hl : w.live X.env obj = some cell)
    (hcan : Slots.ascending cell.slots = true) :
    ∃ principal laws,
      packageOf X obj cell = .ok none ∧
      ownerAuthority X (pinned X.env w c.unsigned.pins) c.unsigned.member obj cell .mutate via = .ok principal ∧
      lawsOf X obj cell = .ok laws ∧
      X.program.judge (pinned X.env w c.unsigned.pins) none laws (stateOf cell) (applyEdits (stateOf cell) edits)
        (reqOf c.unsigned obj principal .write) = .ok () ∧
      ∃ cell', w'.live X.env obj = some cell' ∧ Slots.ascending cell'.slots = true ∧
        ∀ k, (stateOf cell').get k = (applyEdits (stateOf cell) edits).get k := by
  obtain ⟨r, hr, hs⟩ := receive_root hc
  rw [hb] at hr
  have hw := stepped_draft hr
  obtain ⟨cell₀, principal, laws, hk, hp, hau, hlw, hj, hd⟩ := write_judged hw
  obtain ⟨hlive, hpin⟩ := readKind_pinned hk
  rw [hl] at hlive
  cases hlive
  rw [hd] at hs
  obtain ⟨hl', hn⟩ := admit_writeOf hs ha hl hpin
  exact ⟨principal, laws, hp, hau, hlw, hj, _, hl',
    (ascending_iff _).mpr (applyOps_pairwise _ _ ((ascending_iff _).mp hcan)),
    diffOps_next (D := D) (applyEdits_checkState hcan edits) hn⟩


/-! ## A law change, derived and admitted -/

omit [Ord D] [DecidableEq D] in
private theorem get_erase_ne {j k : Nat} (h : j ≠ k) : ∀ s : Slots, (Slots.erase j s).get k = s.get k
  | [] => rfl
  | (k', v') :: rest => by
      have ih := get_erase_ne h rest
      simp only [Slots.get] at ih ⊢
      simp only [Slots.erase]
      by_cases hj : j = k'
      · subst hj
        have hb : (k == j) = false := by simp [Ne.symm h]
        simp [List.lookup, hb]
      · rw [if_neg hj]; by_cases hk : k = k' <;> simp [List.lookup, hk, ih]

omit [Ord D] [DecidableEq D] in
theorem get_applyOps_ne {k : Nat} :
    ∀ (ops : List Op) (s : Slots), (∀ o ∈ ops, o.key ≠ k) → (applyOps s ops).get k = s.get k
  | [], _, _ => rfl
  | o :: rest, s, h => by
      show (applyOps (applyOp s o) rest).get k = s.get k
      rw [get_applyOps_ne rest _ (fun o' ho' => h o' (List.mem_cons_of_mem _ ho'))]
      have hk := h o (List.mem_cons_self ..)
      cases o with
      | set k' v => exact slots_get_set_ne v (Ne.symm hk) s
      | erase k' => exact get_erase_ne hk s

omit [Ord D] [DecidableEq D] in
private theorem get_stateFilter (k : Nat) :
    ∀ s : Slots, Slots.get (s.filter fun p => decide (stateBase ≤ p.1)) k = if stateBase ≤ k then s.get k else none
  | [] => by simp [Slots.get, List.lookup]
  | (k', v') :: rest => by
      have ih := get_stateFilter k rest
      simp only [Slots.get] at ih ⊢
      by_cases hk' : stateBase ≤ k'
      · rw [List.filter_cons_of_pos (p := fun p : Nat × ByteArray => decide (stateBase ≤ p.1)) (decide_eq_true hk')]
        by_cases hk : k = k'
        · subst hk; simp [List.lookup, hk']
        · have hb : (k == k') = false := by simp [hk]
          simp [List.lookup, hb, ih]
      · rw [List.filter_cons_of_neg (p := fun p : Nat × ByteArray => decide (stateBase ≤ p.1))
          (by simpa using hk'), ih]
        by_cases hk : k = k'
        · subst hk; simp [hk']
        · have hb : (k == k') = false := by simp [hk]
          simp [List.lookup, hb]

omit [Ord D] [DecidableEq D] in
theorem diffOps_keys {old new : Slots} {o : Op} (h : o ∈ diffOps old new) :
    (∃ p ∈ new, o.key = p.1) ∨ (∃ p ∈ old, o.key = p.1) := by
  simp only [diffOps, List.mem_append, List.mem_map, List.mem_filter] at h
  rcases h with ⟨p, ⟨hp, -⟩, rfl⟩ | ⟨p, ⟨hp, -⟩, rfl⟩
  · exact .inl ⟨p, hp, rfl⟩
  · exact .inr ⟨p, hp, rfl⟩

/-- **A law change leaves the state.** A signed `law` turn on `obj`, derived from `w` and admitted to
`w'`: the laws in force judged it on `relaw` and every added law on `adopt` over the unchanged state
(`law_judged`), and `obj` is live in `w'` with a state that reads, at every key, what it read: the
turn writes only law slots, every one below `stateBase`. -/
theorem law_next_slots {X : Ctx D} {w w' : World D} {c : Call D} {t : Turn D} {obj : D}
    {laws' : List D} {via : Option D} {cell : Cell}
    (hc : receive X w c = .ok t) (ha : World.admit X.env w t = .ok w')
    (hb : c.unsigned.body = .law obj laws' via) (hl : w.live X.env obj = some cell) :
    ∃ principal laws,
      packageOf X obj cell = .ok none ∧
      ownerAuthority X (pinned X.env w c.unsigned.pins) c.unsigned.member obj cell .mutate via = .ok principal ∧
      lawsOf X obj cell = .ok laws ∧
      X.program.judge (pinned X.env w c.unsigned.pins) none laws (stateOf cell) (stateOf cell)
        (reqOf c.unsigned obj principal (.relaw laws')) = .ok () ∧
      X.program.judge (pinned X.env w c.unsigned.pins) none (laws'.filter fun l => decide (l ∉ laws))
        (stateOf cell) (stateOf cell) (reqOf c.unsigned obj principal (.adopt laws')) = .ok () ∧
      ∃ cell', w'.live X.env obj = some cell' ∧ ∀ k, (stateOf cell').get k = (stateOf cell).get k := by
  obtain ⟨r, hr, hs⟩ := receive_root hc
  rw [hb] at hr
  have hw := stepped_draft hr
  obtain ⟨cell₀, principal, laws, hk, hp, hau, hcl, hlw, hrel, had, hd⟩ := law_judged hw
  obtain ⟨hlive, hpin⟩ := readKind_pinned hk
  rw [hl] at hlive
  cases hlive
  rw [hd] at hs
  obtain ⟨hl', -⟩ := admit_writeOf hs ha hl hpin
  refine ⟨principal, laws, hp, hau, hlw, hrel, had, _, hl', fun k => ?_⟩
  unfold checkLaws at hcl
  simp only [except_bind_ok] at hcl
  obtain ⟨⟨⟩, hlen, -⟩ := hcl
  rw [req_ok, decide_eq_true_eq] at hlen
  simp only [stateOf]
  rw [get_stateFilter, get_stateFilter]
  by_cases hk : stateBase ≤ k
  · rw [if_pos hk, if_pos hk]
    refine get_applyOps_ne _ _ (fun o ho he => ?_)
    rcases diffOps_keys ho with ⟨p, hp', hpk⟩ | ⟨p, hp', hpk⟩
    · simp only [lawSlots, List.mem_map] at hp'
      obtain ⟨⟨l, i⟩, hi, rfl⟩ := hp'
      have := (List.mem_zipIdx hi).2.1
      simp only [lawBase, stateBase] at hpk hlen hk this ⊢
      omega
    · simp only [lawSlotsOf, List.mem_filter, Bool.and_eq_true, decide_eq_true_eq] at hp'
      omega
  · rw [if_neg hk, if_neg hk]


/-- The touch a derived `retire` of `obj` leaves on `obj`: a signed retire's Turn touches `obj`, pinned,
with the act `retire`, and its receiver's check passed at the pinned view. -/
private theorem retire_derived {X : Ctx D} {w : World D} {c : Call D} {t : Turn D} {obj : D}
    (hc : receive X w c = .ok t) (hb : c.unsigned.body = .retire obj) :
    (∃ a : At D, a.actor = c.unsigned.member ∧ retireCheck X (pinned X.env w c.unsigned.pins) c a obj = .ok ()) ∧
      (∃ q ∈ c.unsigned.pins, q.1 = obj) ∧ ∃ x ∈ t.touches, x.cell = obj ∧ x.act = .retire := by
  obtain ⟨r, hr, hs⟩ := receive_root hc
  rw [hb] at hr
  have hw := stepped_draft hr
  unfold retire at hw
  simp only [except_bind_ok] at hw
  obtain ⟨⟨⟩, hchk, hd⟩ := hw
  simp only [pure, Except.pure, Except.ok.injEq] at hd
  rw [← hd] at hs
  obtain ⟨-, -, htouch, -, -, -, -, -, -, hpins⟩ := sealTurn_ok hs
  obtain ⟨q, hq, hqe⟩ := hpins (obj, .retire) (List.mem_singleton_self _)
  refine ⟨⟨_, rfl, hchk⟩, ⟨q, hq, hqe⟩, { cell := q.1, seen := q.2, act := actFor [(obj, Act.retire)] q.1 }, ?_, hqe, ?_⟩
  · rw [htouch]; exact List.mem_map.mpr ⟨q, hq, rfl⟩
  · simp only; rw [hqe]; exact actFor_single

/-- **A retirement is its owner's and judged** (KERNEL-70). A signed `retire` of a live object `obj`,
derived from `w`: the object's owner slot names the signer's member, and every law in force (the
package, then the cell's laws) judged the occasion `retire` from the object's last state to the
same state. Admitted, it leaves `obj`'s tombstone (`retire_next_tomb`). -/
theorem retire_next {X : Ctx D} {w : World D} {c : Call D} {t : Turn D} {obj : D} {cell : Cell}
    (hc : receive X w c = .ok t) (hb : c.unsigned.body = .retire obj) (hl : w.live X.env obj = some cell)
    (hk : cell.kind = kindObject) :
    ∃ pkg laws,
      slotDigest X obj cell slotOwner = .ok c.unsigned.member ∧
      packageOf X obj cell = .ok pkg ∧ lawsOf X obj cell = .ok laws ∧
      X.program.judge (pinned X.env w c.unsigned.pins) pkg laws (stateOf cell) (stateOf cell)
        (reqOf c.unsigned obj c.unsigned.member .retire) = .ok () := by
  obtain ⟨⟨a, ha, hchk⟩, ⟨q, hq, hxc⟩, -⟩ := retire_derived hc hb
  have hlook : pinned X.env w c.unsigned.pins obj = .ok (some cell) := by
    have hany : (c.unsigned.pins.any fun p => decide (p.1 = obj)) = true :=
      List.any_eq_true.mpr ⟨q, hq, by simpa using hxc⟩
    simp [pinned, hany, hl]
  simp only [retireCheck, hlook] at hchk
  obtain ⟨cell₀, hcell, hchk⟩ := except_bind_ok.mp hchk
  simp only [Except.ok.injEq] at hcell
  subst hcell
  have hng : kindObject ≠ kindGrant := by decide
  rw [if_neg (by rw [hk]; exact hng), if_pos hk] at hchk
  simp only [except_bind_ok] at hchk
  obtain ⟨owner, hown, ⟨⟩, hreq, pkg, hpkg, laws, hlaws, hj⟩ := hchk
  rw [req_ok, decide_eq_true_eq] at hreq
  subst hreq
  rw [ha] at hown hj
  exact ⟨pkg, laws, hown, hpkg, hlaws, hj⟩

/-- **An admitted retirement leaves a tombstone** (KERNEL-70), under a lawful `Ord`: a signed
`retire` of `obj`, derived from `w` and admitted to `w'`, leaves `obj`'s tombstone in `w'`, which every
later fold keeps (`fold_tomb_stays`). -/
theorem retire_next_tomb [Std.TransOrd D] [Std.LawfulEqOrd D] {X : Ctx D} {w w' : World D} {c : Call D}
    {t : Turn D} {obj : D} (hc : receive X w c = .ok t) (ha : World.admit X.env w t = .ok w')
    (hb : c.unsigned.body = .retire obj) : w'.entry X.env obj = some .tomb := by
  obtain ⟨-, -, x, hx, rfl, hact⟩ := retire_derived hc hb
  exact admit_retire_tomb ha hx hact

/-- **A retirement is final: every grant over the retired object is dead** (KERNEL-70). After an
admitted `retire` of `obj`, every World a fold reaches holds its tombstone and no live cell at its id:
whatever grants on it remain (their issuers may still retire them and take their storage back) and
whoever signs through them, no admitted turn writes, invokes, relaws or re-creates `obj` again — a
derivation that reads it finds no cell (`missingCell`, or `stale` for a call pinned at its last live
entry), and `World.admit` never advances a tombstone (`fold_tomb_stays`) nor bears a cell at a taken
id (`idTaken`). -/
theorem retire_final [Std.TransOrd D] [Std.LawfulEqOrd D] {X : Ctx D} {w w' w'' : World D} {c : Call D}
    {t : Turn D} {obj : D} {l : List (Step D)} (hc : receive X w c = .ok t)
    (ha : World.admit X.env w t = .ok w') (hb : c.unsigned.body = .retire obj)
    (hf : World.fold X.env w' l = .ok w'') :
    w''.entry X.env obj = some .tomb ∧ w''.live X.env obj = none := by
  have ht := fold_tomb_stays hf (retire_next_tomb hc ha hb)
  exact ⟨ht, by unfold World.live; rw [ht]⟩

/-- **A retirement gives the object's storage back, once** (KERNEL-70 through KERNEL-19's credit):
a signed `retire` of `obj`, derived from `w` and admitted to `w'`, leaves the World's allowance at
what it was, plus the weight of `obj`'s entry, plus what the turn's row touches give back (a retired
object's relation heads leave with it: `rowsAfter`), less the turn's charge. -/
theorem retire_frees_credit [Std.TransOrd D] [Std.LawfulEqOrd D] {X : Ctx D} {w w' : World D}
    {c : Call D} {t : Turn D} {obj : D} (hc : receive X w c = .ok t) (ha : World.admit X.env w t = .ok w')
    (hb : c.unsigned.body = .retire obj) :
    w'.allowance + t.charge =
      w.allowance + ((w.entry X.env obj).map Entry.weight).getD 0 + (rowsAfter X.env w t).2 := by
  obtain ⟨r, hr, hs⟩ := receive_root hc
  rw [hb] at hr
  have hw := stepped_draft hr
  unfold retire at hw
  simp only [except_bind_ok] at hw
  obtain ⟨⟨⟩, -, hd⟩ := hw
  simp only [pure, Except.pure, Except.ok.injEq] at hd
  rw [← hd] at hs
  obtain ⟨-, -, htouch, -⟩ := sealTurn_ok hs
  have hof : ∀ x ∈ t.touches, x.act = .retire → x.cell = obj := by
    intro x hx hxa
    rw [htouch] at hx
    obtain ⟨q, -, rfl⟩ := List.mem_map.mp hx
    simp only [actFor, List.find?] at hxa ⊢
    by_cases hq : obj = q.1
    · exact hq.symm
    · simp [hq] at hxa
  have hact : ∀ x ∈ t.touches, x.act = .keep ∨ x.act = .retire := by
    intro x hx
    rw [htouch] at hx
    obtain ⟨q, -, rfl⟩ := List.mem_map.mp hx
    simp only [actFor, List.find?]
    by_cases hq : obj = q.1 <;> simp [hq]
  rw [admit_retire ha hact]
  obtain ⟨-, -, x, hx, hxc, hxa⟩ := retire_derived hc hb
  have hnd : (t.touches.map Touch.cell).Nodup := by
    obtain ⟨posts, hk, -⟩ := admit_ok ha
    have hshape := hk.shape
    unfold checkShape at hshape
    simp only [except_bind_ok] at hshape
    obtain ⟨⟨⟩, hnd, -⟩ := hshape
    exact firstDup_none (noDup_none hnd)
  have hndf : ((t.touches.filter fun x => x.act == .retire).map Touch.cell).Nodup :=
    hnd.sublist ((List.filter_sublist (l := t.touches)).map _)
  have hall : ∀ y ∈ t.touches.filter (fun x => x.act == .retire), y.cell = obj := fun y hy => by
    obtain ⟨hy, hya⟩ := List.mem_filter.mp hy
    exact hof y hy (by simpa using hya)
  have hxf : x ∈ t.touches.filter (fun x => x.act == .retire) := List.mem_filter.mpr ⟨hx, by simp [hxa]⟩
  generalize t.touches.filter (fun x => x.act == .retire) = F at hndf hall hxf
  match F, hndf, hall, hxf with
  | [], _, _, hxf => cases hxf
  | [y], _, hall, _ => simp [hall y (List.mem_singleton_self _)]
  | y :: z :: _, hndf, hall, _ =>
      have hy := hall y (by simp)
      have hz := hall z (by simp)
      simp only [List.map_cons, List.nodup_cons, List.mem_cons, not_or] at hndf
      exact absurd (hy.trans hz.symm) hndf.1.1

/-! ## Tooth -/

/-- An object cell holding state key 16 twice: not canonical. -/
private def twiceCell : Cell :=
  { kind := kindObject, discipline := .ram, slots := [(16, ByteArray.mk #[1]), (16, ByteArray.mk #[2])] }

/-- **The canonicity premise is load-bearing.** A cell holding state key 16 twice (`1`, then `2`):
the edit-free write judges the move from that state to itself, its `diffOps` is one `set` (keys
distinct: admitted by `checkShape`), and the cell it leaves reads `2` at key 16 where the judged
state reads `1`. -/
theorem write_needs_canon :
    ∃ (cell : Cell) (edits : List (Nat × Option ByteArray)),
      (opKeys (diffOps (stateOf cell) (applyEdits (stateOf cell) edits))).Nodup ∧
      (stateOf { cell with
          slots := (applyOps cell.slots (diffOps (stateOf cell) (applyEdits (stateOf cell) edits))) }).get 16 ≠
        (applyEdits (stateOf cell) edits).get 16 :=
  ⟨twiceCell, [], by decide, by decide⟩

omit [Ord D] [DecidableEq D] in
/-- **The law-slot bound is load-bearing for `law_next_slots`.** Fifteen laws would put a law slot at
`stateBase`, a state key the law turn's write would then set, so the state would not read as before;
`checkLaws` refuses exactly that list (`tooManyLaws`). -/
theorem law_slots_need_bound (X : Ctx D) (look : Pinned D) (l : D) :
    checkLaws look (List.replicate 15 l) = .error .tooManyLaws ∧
      (stateBase, X.env.bytes l) ∈ lawSlots X (List.replicate 15 l) := by
  refine ⟨by simp [checkLaws, req, lawBase, stateBase, bind, Except.bind], ?_⟩
  simp [lawSlots, List.replicate, List.zipIdx, lawBase, stateBase]

end Nanodregg.Kernel.Receive
