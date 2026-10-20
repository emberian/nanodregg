/-
# Kernel.Proofs.WriteNext — what a write or a law change leaves, and every cell stays canonical

`invoke_next_slots` (`Kernel.Proofs.InvokeNext`) says the state an admitted invoke leaves reads, key
by key, what its run returned; the run's state passed `checkState`, so its `diffOps` write is
exact. A `write` has no such check: its new state is `applyEdits` of the cell's state, and that is
canonical only when the cell is. So the write's link rests on a World invariant, proved here:

* `CellsCanon E w`: every live cell's slots are strictly ascending (`Slots.ascending`, the form
  `checkShape` demands of a birth). `admit_cellsCanon`: every admitted turn keeps it (a birth is
  checked `nonCanonicalCell`; a write's `set`/`erase` keep the order); `fold_cellsCanon`,
  `audit_cellsCanon`; `genesis_cellsCanon`: the founders' cells are `slotsOf`, so genesis has it.
* `write_next_slots`: a signed `write` of `obj` derived from `w` and admitted to `w'`, over a
  canonical cell: the laws in force judged the move to `applyEdits (stateOf cell) edits`
  (`write_judged`), and `obj` is live in `w'` with a state that reads that, key by key.
* `law_next_slots`: a signed `law` turn changes only law slots: `obj` is live in `w'` and its state
  reads, key by key, what it read before (no canonicity premise: law keys are below `stateBase`).

Tooth: `write_needs_canon`: on a cell holding key 16 twice, the edit-free write's own `diffOps` is
one `set` (distinct keys, so `checkShape` admits it) that re-sets the FIRST entry to the second
value: the state the cell then reads is not the state the laws judged, so `write_next_slots`'
canonicity premise is load-bearing, and `CellsCanon` is what discharges it. `law_slots_need_bound`:
`checkLaws` refuses a fifteenth law, whose slot would be `stateBase`.
-/
import Kernel.Proofs.InvokeNext
import Kernel.Proofs.Rooted

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

private theorem mem_set {k : Nat} {v : ByteArray} :
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

private theorem set_pairwise {k : Nat} {v : ByteArray} :
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

/-- **Every cell stays canonical along an audited log.** -/
theorem audit_cellsCanon {X : Ctx D} {w w' : World D} {l : List (Step D)} (hw : CellsCanon X.env w)
    (h : audit X w l = .ok w') : CellsCanon X.env w' :=
  fold_cellsCanon hw (audit_ok.mp h).1

omit [Ord D] [DecidableEq D] in
private theorem slotsOf_ascending (ps : List (Nat × ByteArray)) : Slots.ascending (slotsOf ps) = true := by
  unfold slotsOf
  refine (ascending_iff _).mpr (foldl_inv (fun s : Slots => s.Pairwise (fun a b => a.1 < b.1)) _
    (fun s p hs => set_pairwise hs) ps [] List.Pairwise.nil)

/-- **Genesis is canonical**: the founders' member and root grant cells are `slotsOf`. -/
theorem genesis_cellsCanon (X : Ctx D) (name nonce : ByteArray) (allowance : Nat)
    (founders : List (ByteArray × D)) :
    CellsCanon X.env (genesisWorld X name nonce allowance founders) := by
  intro id cell hl
  obtain ⟨p, _, ⟨_, he⟩ | ⟨_, he⟩⟩ := mem_founderEntries (genesis_live hl)
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
      sealTurn X c r.1.creates r.1.effects r.1.nullifiers r.1.rows = .ok t := by
  obtain ⟨-, hw⟩ := receive_ok_with hc
  obtain ⟨-, d, hd, hs⟩ := receiveWith_sealed hw
  rw [derive_eq] at hd
  cases hR : dispatch X (pinned X.env w c.unsigned.pins) (rowView X.env w c.unsigned) c
      (tree X (pinned X.env w c.unsigned.pins) (rowView X.env w c.unsigned) c Bounds.callDepthMax)
      ⟨[], poolOf c.unsigned.body, 0⟩ c.unsigned.member c.unsigned.body with
  | error e => rw [hR] at hd; cases hd
  | ok r =>
      rw [hR] at hd
      simp only [Except.map, Except.ok.injEq] at hd
      subst hd
      exact ⟨r, rfl, hs⟩

/-- An admitted turn whose one act at a live, pinned cell is `writeOf obj ops`: the cell is live
after, with `ops` applied (or kept, when there are none), `ops`' keys distinct. -/
private theorem admit_writeOf {X : Ctx D} {w w' : World D} {c : Call D} {t : Turn D} {obj : D}
    {cell : Cell} {ops : List Op} {cr : List (D × Cell)} {ns : List D} {rs : List (RowSlot D × RowAct)}
    (hs : sealTurn X c cr (writeOf obj ops) ns rs = .ok t) (ha : World.admit X.env w t = .ok w')
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
`w` and admitted to `w'`, over a canonical cell (`CellsCanon` gives it at every World an audited
log reaches from genesis): the laws in force judged, on `write`, the move from the cell's state to
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
private theorem get_applyOps_ne {k : Nat} :
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
private theorem diffOps_keys {old new : Slots} {o : Op} (h : o ∈ diffOps old new) :
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
