/-
# Kernel.Proofs.RowsComm — two rains on one bell commute (KERNEL-46 amendment 3)

Two turns admissible from one World, whose footprints are disjoint outside the relations' heads
(`RowsCommFoot`), and whose head updates fit together (`RowsFitTogether`), are BOTH admitted in
BOTH orders, and reach the same cells and the same rows; the head moves by the sum of both turns'
inserts (`admit_comm`). The rows-level core is `rowsRun_comm`.

Teeth: `two_rains` (the premises hold of two single-insert turns into one relation),
`plant_second_rain_stale` (an insert that pins its head refuses the second rain), and
`write_repin_refused` (a parent written by the first turn refuses the second's pin).
-/
import Kernel.Proofs.Rows
import Kernel.Proofs.RowsHead
import Kernel.Proofs.RowsSep
import Kernel.Proofs.Cells
import Kernel.Proofs.Local

namespace Nanodregg.Kernel

variable {D : Type} [DecidableEq D]

attribute [local irreducible] rowPath

/-! ## What a list of inserts does, as a function of the rows' reads -/

/-- Every row touch is an insert into a row slot. -/
def InsOnly (xs : List (RowTouch D)) : Prop :=
  ∀ x ∈ xs, ∃ key amt v, x.slot = .row key ∧ x.act = .insert amt v

/-- What one insert does to the read at slot `s` (`o`: the read before it), given its relations'
floors `F` (KERNEL-54: an insert's row takes its relation's floor as its version, and no insert moves
a floor, so `F` is the pre-state's for a whole list of inserts). -/
private def view1 (F : D → Nat → Nat) (x : RowTouch D) (s : RowSlot D) (o : Option RowLeaf) : Option RowLeaf :=
  match x.slot, x.act with
  | .row key, .insert amt v =>
      if s = .row key then some (.row amt v (F key.parent key.rel))
      else match s, o with
        | .head p rel, some (.head c sm l cap wd rt fl) =>
            if key.parent = p ∧ key.rel = rel then some (.head (c + 1) (sm + amt) l cap wd rt fl) else o
        | _, _ => o
  | _, _ => o

/-- What a list of inserts does to the read at slot `s`, in order. -/
private def view (F : D → Nat → Nat) : List (RowTouch D) → RowSlot D → Option RowLeaf → Option RowLeaf
  | [], _, o => o
  | x :: rest, s, o => view F rest s (view1 F x s o)

private theorem view1_head (F : D → Nat → Nat) (x : RowTouch D) (p : D) (rel c sm l cap wd : Nat) (rt : Bool) (fl : Nat) :
    view1 F x (.head p rel) (some (.head c sm l cap wd rt fl)) =
      some (.head (c + insN1 p rel x) (sm + insA1 p rel x) l cap wd rt fl) := by
  obtain ⟨slot, seen, act⟩ := x
  cases slot with
  | head _ _ => cases act <;> simp [view1, insN1, insA1]
  | row k =>
      cases act with
      | insert amt v =>
          simp only [view1, insN1, insA1]
          rw [if_neg (by intro h; cases h)]
          by_cases hk : k.parent = p ∧ k.rel = rel
          · simp [hk]
          · simp [hk]
      | _ => simp [view1, insN1, insA1]

/-- **The head is additive**: after a list of inserts a head counts and sums them all. -/
private theorem view_head (F : D → Nat → Nat) (p : D) (rel : Nat) (l cap wd : Nat) (rt : Bool) (fl : Nat) :
    ∀ (xs : List (RowTouch D)) (c sm : Nat), view F xs (.head p rel) (some (.head c sm l cap wd rt fl)) =
      some (.head (c + insN p rel xs) (sm + insA p rel xs) l cap wd rt fl)
  | [], c, sm => by simp [view, insN, insA]
  | x :: rest, c, sm => by
      simp only [view, view1_head, insN, insA]
      rw [view_head F p rel l cap wd rt fl rest]
      simp only [Nat.add_assoc]

private theorem view1_ne (F : D → Nat → Nat) (x : RowTouch D) (s : RowSlot D) (o : Option RowLeaf)
    (hs : ∀ key, s = .row key → x.slot ≠ .row key)
    (hh : ∀ p rel, s = .head p rel → insN1 p rel x = 0) : view1 F x s o = o := by
  obtain ⟨slot, seen, act⟩ := x
  cases slot with
  | head _ _ => cases act <;> rfl
  | row k =>
      cases act with
      | insert amt v =>
          simp only [view1]
          have h1 : s ≠ .row k := fun e => hs k e rfl
          rw [if_neg h1]
          cases s with
          | row _ => rfl
          | head p rel =>
              have h0 := hh p rel rfl
              simp only [insN1] at h0
              cases o with
              | none => rfl
              | some lf =>
                  cases lf with
                  | row _ _ _ => rfl
                  | head c sm l cap wd rt fl =>
                      simp only
                      rw [if_neg]
                      intro hk; rw [if_pos hk] at h0; exact absurd h0 (by decide)
      | _ => rfl

/-- A row slot no touch of the list names reads as before. -/
private theorem view_row_out (F : D → Nat → Nat) (k : RowKey D) :
    ∀ (xs : List (RowTouch D)) (o : Option RowLeaf), (∀ x ∈ xs, x.slot ≠ .row k) → view F xs (.row k) o = o
  | [], _, _ => rfl
  | x :: rest, o, h => by
      simp only [view]
      rw [view1_ne F x (.row k) o (fun key e => by cases e; exact h x (by simp)) (fun _ _ e => by cases e)]
      exact view_row_out F k rest o (fun y hy => h y (by simp [hy]))

/-- A head slot that does not hold a head reads as before. -/
private theorem view_head_other (F : D → Nat → Nat) (p : D) (rel : Nat) :
    ∀ (xs : List (RowTouch D)) (o : Option RowLeaf), (∀ c sm l cap wd rt fl, o ≠ some (.head c sm l cap wd rt fl)) →
      view F xs (.head p rel) o = o
  | [], _, _ => rfl
  | x :: rest, o, h => by
      simp only [view]
      have e : view1 F x (.head p rel) o = o := by
        obtain ⟨slot, seen, act⟩ := x
        cases slot with
        | head _ _ => cases act <;> rfl
        | row k =>
            cases act with
            | insert amt v =>
                simp only [view1]
                rw [if_neg (by intro h; cases h)]
                cases o with
                | none => rfl
                | some lf =>
                    cases lf with
                    | row _ _ _ => rfl
                    | head c sm l cap wd rt fl => exact absurd rfl (h c sm l cap wd rt fl)
            | _ => rfl
      rw [e]; exact view_head_other F p rel rest o h

/-- **Two lists of inserts commute on every read**, when no row slot is in both. -/
private theorem view_comm {F : D → Nat → Nat} {xs ys : List (RowTouch D)}
    (hd : ∀ x ∈ xs, ∀ y ∈ ys, x.slot ≠ y.slot) (s : RowSlot D) (o : Option RowLeaf) :
    view F ys s (view F xs s o) = view F xs s (view F ys s o) := by
  cases s with
  | row k =>
      by_cases h1 : ∃ x ∈ xs, x.slot = .row k
      · have h2 : ∀ y ∈ ys, y.slot ≠ .row k := by
          obtain ⟨x, hx', hxs⟩ := h1
          intro y hy' e; exact hd x hx' y hy' (hxs.trans e.symm)
        rw [view_row_out F k ys _ h2, view_row_out F k ys _ h2]
      · have h1' : ∀ x ∈ xs, x.slot ≠ .row k := fun x hx' e => h1 ⟨x, hx', e⟩
        rw [view_row_out F k xs _ h1', view_row_out F k xs _ h1']
  | head p rel =>
      by_cases ho : ∃ c sm l cap wd rt fl, o = some (.head c sm l cap wd rt fl)
      · obtain ⟨c, sm, l, cap, wd, rt, fl, rfl⟩ := ho
        rw [view_head, view_head, view_head, view_head, Nat.add_right_comm c, Nat.add_right_comm sm]
      · have ho' : ∀ c sm l cap wd rt fl, o ≠ some (.head c sm l cap wd rt fl) :=
          fun c sm l cap wd rt fl e => ho ⟨c, sm, l, cap, wd, rt, fl, e⟩
        rw [view_head_other F p rel xs o ho', view_head_other F p rel ys o ho', view_head_other F p rel xs o ho']

/-- A list of inserts leaves every relation's floor where it was. -/
private theorem headFloor_view {E : Env D} {F : D → Nat → Nat} {xs : List (RowTouch D)} {r r' : Rows D}
    (h : ∀ s, r'.get (rowSpec E) s = view F xs s (r.get (rowSpec E) s)) : headFloor E r' = headFloor E r := by
  funext p rel
  unfold headFloor rowAt
  rw [h]
  cases hg : r.get (rowSpec E) (.head p rel) with
  | none => rw [view_head_other F p rel xs none (fun _ _ _ _ _ _ _ e => by cases e)]
  | some lf =>
      cases lf with
      | row a b u => rw [view_head_other F p rel xs _ (fun _ _ _ _ _ _ _ e => by cases e)]
      | head c sm l cap wd rt fl => rw [view_head]

private theorem insA_zero (p : D) (rel : Nat) :
    ∀ xs : List (RowTouch D), insN p rel xs = 0 → insA p rel xs = 0
  | [], _ => rfl
  | x :: rest, h => by
      simp only [insN, insA] at h ⊢
      have h2 := insA_zero p rel rest (by omega)
      have h1 : insA1 p rel x = 0 := by
        have hn : insN1 p rel x = 0 := by omega
        obtain ⟨slot, seen, act⟩ := x
        cases slot with
        | head _ _ => cases act <;> rfl
        | row k =>
            cases act with
            | insert amt v =>
                simp only [insN1, insA1] at hn ⊢
                by_cases hk : k.parent = p ∧ k.rel = rel
                · rw [if_pos hk] at hn; exact absurd hn (by decide)
                · rw [if_neg hk]
            | _ => rfl
      omega

/-! ## One insert, on the rows it is judged on -/

section
variable [Ord D]

/-- The parts of an insert's judgement that do not read the rows: its parent is pinned by the turn,
live, and not retired by it; it carries no pin; its value fits. -/
private def Stat (E : Env D) (w : World D) (t : Turn D) (x : RowTouch D) (key : RowKey D) (v : ByteArray) :
    Prop :=
  (t.touches.any fun y => decide (y.cell = key.parent)) = true ∧ (w.live E key.parent).isSome = true ∧
    (!(t.touches.any fun y => decide (y.cell = key.parent) && decide (y.act = .retire))) = true ∧
    x.seen = none ∧ v.size ≤ Bounds.valueBytesMax

/-- What a list of inserts needs of the rows it starts from to pass, all at once: each insert's
static part, its row absent, its relation declared at its key's width; and per relation, the count
and the sum after all of the list's inserts within the limit and the cap. -/
private def Cond (E : Env D) (w : World D) (t : Turn D) (r : Rows D) (xs : List (RowTouch D)) : Prop :=
  (∀ x ∈ xs, ∀ key amt v, x.slot = .row key → x.act = .insert amt v →
      Stat E w t x key v ∧ rowAt E r (.row key) = none ∧
      ∃ c sm l cap rt, headOf E r key.parent key.rel = some (c, sm, l, cap, key.k.size, rt)) ∧
    ∀ p rel, 0 < insN p rel xs → ∃ c sm l cap wd rt, headOf E r p rel = some (c, sm, l, cap, wd, rt) ∧
      c + insN p rel xs ≤ l ∧ sm + insA p rel xs ≤ cap


private theorem ins_step_ok {E : Env D} {w : World D} {t : Turn D} {r r' : Rows D} {x : RowTouch D}
    {key : RowKey D} {amt : Nat} {v : ByteArray} (hs : x.slot = .row key) (ha : x.act = .insert amt v)
    (h : rowStep E w t r x = .ok r') :
    Stat E w t x key v ∧ rowAt E r (.row key) = none ∧ ∃ c sm l cap rt,
      headOf E r key.parent key.rel = some (c, sm, l, cap, key.k.size, rt) ∧ c < l ∧ sm + amt ≤ cap ∧
      r' = setHead E (r.insert (rowSpec E) (.row key) (.row amt v (headFloor E r key.parent key.rel))) key.parent
        key.rel (c + 1) (sm + amt) l cap key.k.size rt (headFloor E r key.parent key.rel) := by
  obtain ⟨slot, seen, act⟩ := x
  simp only at hs ha
  subst hs ha
  unfold rowStep at h
  simp only [except_bind_ok] at h
  obtain ⟨⟨⟩, h1, ⟨⟩, h2, ⟨⟩, h3, h⟩ := h
  split at h
  · simp at h
  · rename_i c sm l cap wd rt hhead
    simp only [except_bind_ok] at h
    obtain ⟨⟨⟩, hw, h⟩ := h
    obtain ⟨⟨⟩, hsn, ⟨⟩, hn, ⟨⟩, hfull, ⟨⟩, hcap, ⟨⟩, hv, h⟩ := h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    have hw' := of_decide_eq_true (req_ok.mp hw)
    subst hw'
    exact ⟨⟨req_ok.mp h1, req_ok.mp h2, req_ok.mp h3, Option.isNone_iff_eq_none.mp (req_ok.mp hsn),
      of_decide_eq_true (req_ok.mp hv)⟩, Option.isNone_iff_eq_none.mp (req_ok.mp hn), c, sm, l, cap, rt,
      hhead, of_decide_eq_true (req_ok.mp hfull), of_decide_eq_true (req_ok.mp hcap), rfl⟩

private theorem ins_step_of {E : Env D} {w : World D} {t : Turn D} {r : Rows D} {x : RowTouch D}
    {key : RowKey D} {amt : Nat} {v : ByteArray} (hs : x.slot = .row key) (ha : x.act = .insert amt v)
    (hst : Stat E w t x key v) (hrow : rowAt E r (.row key) = none) {c sm l cap : Nat} {rt : Bool}
    (hh : headOf E r key.parent key.rel = some (c, sm, l, cap, key.k.size, rt)) (hcl : c < l)
    (hcap : sm + amt ≤ cap) :
    rowStep E w t r x = .ok (setHead E (r.insert (rowSpec E) (.row key) (.row amt v (headFloor E r key.parent key.rel)))
      key.parent key.rel (c + 1) (sm + amt) l cap key.k.size rt (headFloor E r key.parent key.rel)) := by
  obtain ⟨slot, seen, act⟩ := x
  simp only at hs ha
  subst hs ha
  obtain ⟨h1, h2, h3, h4, h5⟩ := hst
  obtain rfl : seen = none := h4
  unfold rowStep
  simp [req, h1, h2, h3, hh, hrow, hcl, hcap, h5, bind, Except.bind, pure, Except.pure]

omit [Ord D] in
private theorem get_step {E : Env D} (r : Rows D) (key : RowKey D) (amt : Nat) (v : ByteArray) (u : Nat)
    (c sm l cap wd : Nat) (rt : Bool) (fl : Nat) (s : RowSlot D) :
    (setHead E (r.insert (rowSpec E) (.row key) (.row amt v u)) key.parent key.rel c sm l cap wd rt fl).get
        (rowSpec E) s =
      if s = .head key.parent key.rel then some (.head c sm l cap wd rt fl)
      else if s = .row key then some (.row amt v u) else r.get (rowSpec E) s := by
  unfold setHead
  rw [Trie.get_insert, Trie.get_insert]

omit [Ord D] in
private theorem headOf_step {E : Env D} (r : Rows D) (key : RowKey D) (amt : Nat) (v : ByteArray) (u : Nat)
    (c sm l cap wd : Nat) (rt : Bool) (fl : Nat) (p : D) (rel : Nat) :
    headOf E (setHead E (r.insert (rowSpec E) (.row key) (.row amt v u)) key.parent key.rel c sm l cap wd rt fl)
        p rel =
      if key.parent = p ∧ key.rel = rel then some (c, sm, l, cap, wd, rt) else headOf E r p rel := by
  unfold headOf rowAt
  rw [get_step]
  by_cases hk : key.parent = p ∧ key.rel = rel
  · obtain ⟨rfl, rfl⟩ := hk; simp
  · have h1 : (RowSlot.head p rel : RowSlot D) ≠ .head key.parent key.rel := by
      intro e; injection e with e1 e2; exact hk ⟨e1.symm, e2.symm⟩
    rw [if_neg h1, if_neg (by intro e; cases e), if_neg hk]

omit [Ord D] in
private theorem rowAt_step {E : Env D} (r : Rows D) (key k : RowKey D) (amt : Nat) (v : ByteArray) (u : Nat)
    (c sm l cap wd : Nat) (rt : Bool) (fl : Nat) (hk : k ≠ key) :
    rowAt E (setHead E (r.insert (rowSpec E) (.row key) (.row amt v u)) key.parent key.rel c sm l cap wd rt fl)
        (.row k) = rowAt E r (.row k) := by
  unfold rowAt
  rw [get_step, if_neg (by intro e; cases e), if_neg (by intro e; injection e with e; exact hk e)]

omit [Ord D] in
/-- An insert leaves every relation's floor where it was. -/
private theorem headFloor_step {E : Env D} (r : Rows D) (key : RowKey D) (amt : Nat) (v : ByteArray) (u : Nat)
    (c sm l cap wd : Nat) (rt : Bool) :
    headFloor E (setHead E (r.insert (rowSpec E) (.row key) (.row amt v u)) key.parent key.rel c sm l cap wd rt
      (headFloor E r key.parent key.rel)) = headFloor E r := by
  funext p rel
  by_cases hk : key.parent = p ∧ key.rel = rel
  · obtain ⟨rfl, rfl⟩ := hk
    conv => lhs; unfold headFloor rowAt
    rw [get_step, if_pos rfl]
    rfl
  · have h1 : (RowSlot.head p rel : RowSlot D) ≠ .head key.parent key.rel := by
      intro e; injection e with e1 e2; exact hk ⟨e1.symm, e2.symm⟩
    unfold headFloor rowAt
    rw [get_step, if_neg h1, if_neg (by intro e; cases e)]

omit [Ord D] in
/-- One insert's rows, read anywhere, are `view1` of the rows before it. -/
private theorem step_view {E : Env D} {r : Rows D} {x : RowTouch D} {key : RowKey D} {amt : Nat}
    {v : ByteArray} (hs : x.slot = .row key) (ha : x.act = .insert amt v) {c sm l cap wd : Nat} {rt : Bool} {fl : Nat}
    (hh : r.get (rowSpec E) (.head key.parent key.rel) = some (.head c sm l cap wd rt fl)) (s : RowSlot D) :
    (setHead E (r.insert (rowSpec E) (.row key) (.row amt v fl)) key.parent key.rel (c + 1) (sm + amt) l cap wd rt
      fl).get (rowSpec E) s = view1 (headFloor E r) x s (r.get (rowSpec E) s) := by
  have hf : headFloor E r key.parent key.rel = fl := by unfold headFloor rowAt; rw [hh]
  rw [get_step]
  simp only [view1, hs, ha, hf]
  cases s with
  | row k =>
      rw [if_neg (by intro e; cases e)]
  | head p rel =>
      have hr : (RowSlot.head p rel : RowSlot D) ≠ .row key := by intro e; cases e
      by_cases hk : key.parent = p ∧ key.rel = rel
      · obtain ⟨rfl, rfl⟩ := hk
        rw [if_pos rfl, if_neg hr, hh]; simp
      · have h1 : (RowSlot.head p rel : RowSlot D) ≠ .head key.parent key.rel := by
          intro e; injection e with e1 e2; exact hk ⟨e1.symm, e2.symm⟩
        rw [if_neg h1, if_neg hr, if_neg hr]
        cases hg : r.get (rowSpec E) (.head p rel) with
        | none => rfl
        | some lf =>
            cases lf with
            | row _ _ _ => rfl
            | head c' sm' l' cap' wd' rt' fl' => simp only; rw [if_neg hk]

/-! ## A list of inserts: what it needs of the rows it starts from, and what it leaves -/

/-- **A run of inserts, forward**: if it passes, it gave nothing back, every read after it is `view`
of the read before, and the rows it started from met `Cond`. -/
private theorem fold_fwd {E : Env D} {w : World D} {t : Turn D} :
    ∀ (xs : List (RowTouch D)) (acc rr : Rows D × Nat), InsOnly xs → (xs.map RowTouch.slot).Nodup →
      xs.foldlM (rowStepFreed E w t) acc = .ok rr →
      rr.2 = acc.2 ∧ (∀ s, rr.1.get (rowSpec E) s = view (headFloor E acc.1) xs s (acc.1.get (rowSpec E) s)) ∧
        Cond E w t acc.1 xs
  | [], acc, rr, _, _, h => by
      simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h
      subst h
      exact ⟨rfl, fun _ => rfl, fun x hx => by simp at hx, fun p rel h => by simp [insN] at h⟩
  | x :: rest, acc, rr, hi, hn, h => by
      rw [List.foldlM_cons, except_bind_ok] at h
      obtain ⟨acc', h1, h2⟩ := h
      unfold rowStepFreed at h1
      rw [except_bind_ok] at h1
      obtain ⟨r1, hstep, he⟩ := h1
      simp only [pure, Except.pure, Except.ok.injEq] at he
      subst he
      obtain ⟨key, amt, v, hs, ha⟩ := hi x (by simp)
      have hfr : rowFreed E acc.1 x = 0 := by simp [rowFreed, ha]
      obtain ⟨hst, hrow, c, sm, l, cap, rt, hh, hcl, hcap, rfl⟩ := ins_step_ok hs ha hstep
      simp only [List.map_cons, List.nodup_cons] at hn
      have hirest : InsOnly rest := fun z hz => hi z (by simp [hz])
      obtain ⟨ih2, ihv, ihc1, ihc2⟩ := fold_fwd rest _ rr hirest hn.2 h2
      simp only [hfr, Nat.add_zero, headFloor_step] at ih2 ihv ihc1 ihc2
      have hnot : ∀ z ∈ rest, z.slot ≠ .row key := fun z hz e =>
        hn.1 (by rw [hs, ← e]; exact List.mem_map_of_mem hz)
      refine ⟨ih2, fun s => ?_, fun z hz kz amt' v' hzs hza => ?_, fun p rel hpos => ?_⟩
      · rw [ihv s, step_view hs ha (headOf_some hh) s]; rfl
      · rcases List.mem_cons.mp hz with rfl | hz'
        · have e1 : kz = key := by rw [hs] at hzs; injection hzs with e; exact e.symm
          subst e1
          rw [ha] at hza; injection hza with e2 e3; subst e2 e3
          exact ⟨hst, hrow, c, sm, l, cap, rt, hh⟩
        · obtain ⟨hst', hrow', c', sm', l', cap', rt', hh'⟩ := ihc1 z hz' kz amt' v' hzs hza
          have hk : kz ≠ key := fun e => hnot z hz' (by rw [hzs, e])
          refine ⟨hst', by rw [← rowAt_step acc.1 key kz amt v _ (c + 1) (sm + amt) l cap key.k.size rt _ hk]; exact hrow', ?_⟩
          rw [headOf_step] at hh'
          split at hh'
          · rename_i hpr
            obtain ⟨hp, hr⟩ := hpr
            simp only [Option.some.injEq, Prod.mk.injEq] at hh'
            obtain ⟨-, -, -, -, ew, -⟩ := hh'
            refine ⟨c, sm, l, cap, rt, ?_⟩
            rw [← hp, ← hr, ← ew]; exact hh
          · exact ⟨c', sm', l', cap', rt', hh'⟩
      · simp only [insN, insA] at hpos ⊢
        by_cases hpr : key.parent = p ∧ key.rel = rel
        · have hnx : insN1 p rel x = 1 := by simp [insN1, hs, ha, hpr]
          have hax : insA1 p rel x = amt := by simp [insA1, hs, ha, hpr]
          obtain ⟨rfl, rfl⟩ := hpr
          refine ⟨c, sm, l, cap, key.k.size, rt, hh, ?_⟩
          by_cases hr0 : 0 < insN key.parent key.rel rest
          · obtain ⟨c', sm', l', cap', wd', rt', hh', h1, h2⟩ := ihc2 _ _ hr0
            rw [headOf_step, if_pos ⟨rfl, rfl⟩] at hh'
            simp only [Option.some.injEq, Prod.mk.injEq] at hh'
            obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := hh'
            omega
          · have h0 : insN key.parent key.rel rest = 0 := by omega
            have := insA_zero _ _ rest h0
            omega
        · have hnx : insN1 p rel x = 0 := by simp [insN1, hs, ha, hpr]
          have hax : insA1 p rel x = 0 := by simp [insA1, hs, ha, hpr]
          obtain ⟨c', sm', l', cap', wd', rt', hh', h1, h2⟩ := ihc2 p rel (by omega)
          rw [headOf_step, if_neg hpr] at hh'
          exact ⟨c', sm', l', cap', wd', rt', hh', by omega, by omega⟩

/-- **A run of inserts, backward**: from rows meeting `Cond`, it passes, giving nothing back. -/
private theorem fold_bwd {E : Env D} {w : World D} {t : Turn D} :
    ∀ (xs : List (RowTouch D)) (r : Rows D) (f : Nat), InsOnly xs → (xs.map RowTouch.slot).Nodup →
      Cond E w t r xs → ∃ r', xs.foldlM (rowStepFreed E w t) (r, f) = .ok (r', f)
  | [], r, _, _, _, _ => ⟨r, rfl⟩
  | x :: rest, r, f, hi, hn, ⟨hc1, hc2⟩ => by
      obtain ⟨key, amt, v, hs, ha⟩ := hi x (by simp)
      obtain ⟨hst, hrow, c, sm, l, cap, rt, hh⟩ := hc1 x (by simp) key amt v hs ha
      have hnx : insN1 key.parent key.rel x = 1 := by simp [insN1, hs, ha]
      have hax : insA1 key.parent key.rel x = amt := by simp [insA1, hs, ha]
      obtain ⟨c', sm', l', cap', wd', rt', hh', hfit, hcapfit⟩ :=
        hc2 key.parent key.rel (by simp only [insN]; omega)
      rw [hh] at hh'
      simp only [Option.some.injEq, Prod.mk.injEq] at hh'
      obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := hh'
      simp only [insN, insA, hnx, hax] at hfit hcapfit
      have hstep := ins_step_of (w := w) (t := t) hs ha hst hrow hh (by omega) (by omega)
      simp only [List.map_cons, List.nodup_cons] at hn
      have hirest : InsOnly rest := fun z hz => hi z (by simp [hz])
      have hnot : ∀ z ∈ rest, z.slot ≠ .row key := fun z hz e =>
        hn.1 (by rw [hs, ← e]; exact List.mem_map_of_mem hz)
      have hcond : Cond E w t (setHead E (r.insert (rowSpec E) (.row key) (.row amt v (headFloor E r key.parent key.rel)))
          key.parent key.rel (c + 1) (sm + amt) l cap key.k.size rt (headFloor E r key.parent key.rel)) rest := by
        refine ⟨fun z hz kz amt' v' hzs hza => ?_, fun p rel hpos => ?_⟩
        · obtain ⟨hst', hrow', c', sm', l', cap', rt', hh'⟩ := hc1 z (by simp [hz]) kz amt' v' hzs hza
          have hk : kz ≠ key := fun e => hnot z hz (by rw [hzs, e])
          refine ⟨hst', by rw [rowAt_step r key kz amt v _ (c + 1) (sm + amt) l cap key.k.size rt _ hk]; exact hrow', ?_⟩
          rw [headOf_step]
          split
          · rename_i hpr
            obtain ⟨hp, hr⟩ := hpr
            rw [← hp, ← hr, hh] at hh'
            simp only [Option.some.injEq, Prod.mk.injEq] at hh'
            obtain ⟨-, -, -, -, ew, -⟩ := hh'
            exact ⟨c + 1, sm + amt, l, cap, rt, by rw [ew]⟩
          · exact ⟨c', sm', l', cap', rt', hh'⟩
        · by_cases hpr : key.parent = p ∧ key.rel = rel
          · obtain ⟨rfl, rfl⟩ := hpr
            exact ⟨c + 1, sm + amt, l, cap, key.k.size, rt, by rw [headOf_step, if_pos ⟨rfl, rfl⟩],
              by omega, by omega⟩
          · have hnx0 : insN1 p rel x = 0 := by simp [insN1, hs, ha, hpr]
            have hax0 : insA1 p rel x = 0 := by simp [insA1, hs, ha, hpr]
            obtain ⟨c', sm', l', cap', wd', rt', hh', h1, h2⟩ := hc2 p rel (by simp only [insN]; omega)
            simp only [insN, insA, hnx0, hax0, Nat.zero_add] at h1 h2
            exact ⟨c', sm', l', cap', wd', rt', by rw [headOf_step, if_neg hpr]; exact hh', h1, h2⟩
      obtain ⟨r', hr'⟩ := fold_bwd rest _ f hirest hn.2 hcond
      refine ⟨r', ?_⟩
      have h1 : rowStepFreed E w t (r, f) x = .ok (setHead E (r.insert (rowSpec E) (.row key)
          (.row amt v (headFloor E r key.parent key.rel))) key.parent key.rel (c + 1) (sm + amt) l cap key.k.size rt
          (headFloor E r key.parent key.rel), f) := by
        unfold rowStepFreed; rw [hstep]; simp [rowFreed, ha, bind, Except.bind, pure, Except.pure]
      rw [List.foldlM_cons, h1]
      exact hr'

/-! ## The rows of a turn that retires nothing and only inserts -/

/-- A turn retires no cell. -/
def NoRetire (t : Turn D) : Prop := ∀ x ∈ t.touches, x.act ≠ .retire

omit [Ord D] in
private theorem foldl_noRetire {E : Env D} :
    ∀ (l : List (Touch D)) (acc : Rows D × Nat), (∀ x ∈ l, x.act ≠ .retire) →
      l.foldl (fun acc x => match x.act with
        | .retire =>
            ((under (rowSpec E) (E.bytes x.cell) 257 acc.1).filter fun p => match p.1 with
              | .head q _ => decide (q = x.cell)
              | .row _ => false).foldl (fun acc p =>
                (Trie.retainAt (rowSpec E) (fun k _ => decide (k ≠ p.1)) (rowPath E p.1) acc.1,
                  acc.2 + rowEntryWeight p)) acc
        | _ => acc) acc = acc
  | [], _, _ => rfl
  | x :: rest, acc, h => by
      rw [List.foldl_cons]
      have hx : x.act ≠ .retire := h x (by simp)
      have e1 : (match x.act with
        | .retire =>
            ((under (rowSpec E) (E.bytes x.cell) 257 acc.1).filter fun p => match p.1 with
              | .head q _ => decide (q = x.cell)
              | .row _ => false).foldl (fun acc p =>
                (Trie.retainAt (rowSpec E) (fun k _ => decide (k ≠ p.1)) (rowPath E p.1) acc.1,
                  acc.2 + rowEntryWeight p)) acc
        | _ => acc) = acc := by
        cases ha : x.act with
        | retire => exact absurd ha hx
        | _ => rfl
      rw [e1]
      exact foldl_noRetire rest acc (fun y hy => h y (by simp [hy]))

omit [Ord D] in
/-- A turn that retires nothing drops no head. -/
private theorem dropHeads_noRetire {E : Env D} {t : Turn D} (h : NoRetire t)
    (acc : Rows D × Nat) : dropHeads E t acc = acc :=
  foldl_noRetire t.touches acc h

/-- What a passing `rowsRun` of a turn that retires nothing is: its run of row touches, from the
World's rows, over distinct slots. -/
private theorem rowsRun_fold {E : Env D} {w : World D} {t : Turn D} {rr : Rows D × Nat} (hnr : NoRetire t)
    (h : rowsRun E w t = .ok rr) :
    (t.rows.map RowTouch.slot).Nodup ∧ t.rows.foldlM (rowStepFreed E w t) (w.rows, 0) = .ok rr := by
  unfold rowsRun at h
  simp only [except_bind_ok] at h
  obtain ⟨⟨⟩, -, ⟨⟩, -, h⟩ := h
  split at h
  · simp at h
  · rename_i hfind
    rw [except_bind_ok] at h
    obtain ⟨acc, hacc, he⟩ := h
    simp only [pure, Except.pure, Except.ok.injEq, dropHeads_noRetire hnr] at he
    subst he
    exact ⟨nodup_of_find_none hfind, hacc⟩

/-- A passing `rowsRun` of a turn that retires nothing stays passing from any World whose run of
the turn's row touches passes. -/
private theorem rowsRun_of_fold {E : Env D} {w w' : World D} {t : Turn D} {rr rr' : Rows D × Nat}
    (hnr : NoRetire t) (h : rowsRun E w t = .ok rr)
    (hf : t.rows.foldlM (rowStepFreed E w' t) (w'.rows, 0) = .ok rr') :
    rowsRun E w' t = .ok rr' := by
  unfold rowsRun at h ⊢
  simp only [except_bind_ok] at h ⊢
  obtain ⟨⟨⟩, h1, ⟨⟩, h2, h⟩ := h
  refine ⟨(), h1, (), h2, ?_⟩
  split at h
  · simp at h
  · simp only [except_bind_ok]
    exact ⟨rr', hf, by simp [pure, Except.pure, dropHeads_noRetire hnr]⟩

private theorem stat_live {E : Env D} {w w' : World D} {t : Turn D} {x : RowTouch D} {key : RowKey D}
    {v : ByteArray}
    (hl : ∀ c, (t.touches.any fun y => decide (y.cell = c)) = true → w'.live E c = w.live E c)
    (h : Stat E w t x key v) : Stat E w' t x key v := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨h1, by rw [hl _ h1]; exact h2, h3, h4, h5⟩

omit [Ord D] in
private theorem get_headOf {E : Env D} {r : Rows D} {p : D} {rel c sm l cap wd : Nat} {rt : Bool} {fl : Nat}
    (h : r.get (rowSpec E) (.head p rel) = some (.head c sm l cap wd rt fl)) :
    headOf E r p rel = some (c, sm, l, cap, wd, rt) := by
  unfold headOf rowAt; rw [h]

/-- Two turns' inserts fit together in every relation either inserts into: the count after both
within the head's `limit`, the `amt` sum after both within its `cap`. Read on the pre-state rows. -/
def RowsFitTogether (E : Env D) (r : Rows D) (t₁ t₂ : Turn D) : Prop :=
  ∀ p rel, 0 < insN p rel t₁.rows + insN p rel t₂.rows → ∀ c sm l cap wd rt,
    headOf E r p rel = some (c, sm, l, cap, wd, rt) →
      c + insN p rel t₁.rows + insN p rel t₂.rows ≤ l ∧ sm + insA p rel t₁.rows + insA p rel t₂.rows ≤ cap

omit [Ord D] in
private theorem fit_symm {E : Env D} {r : Rows D} {t₁ t₂ : Turn D} (h : RowsFitTogether E r t₁ t₂) :
    RowsFitTogether E r t₂ t₁ := by
  intro p rel hpos c sm l cap wd rt hh
  have := h p rel (by omega) c sm l cap wd rt hh
  omega

/-- **One order**: after the first turn's rows, the second turn's rows still run, give nothing back,
and leave every read at `view` of both lists over the pre-state. -/
private theorem rowsRun_after {E : Env D} {w w₁ : World D} {t₁ t₂ : Turn D} {rr₁ rr₂ : Rows D × Nat}
    (hnr₁ : NoRetire t₁) (hnr₂ : NoRetire t₂) (hi₁ : InsOnly t₁.rows) (hi₂ : InsOnly t₂.rows)
    (hd : ∀ x ∈ t₁.rows, ∀ y ∈ t₂.rows, x.slot ≠ y.slot) (hfit : RowsFitTogether E w.rows t₁ t₂)
    (h₁ : rowsRun E w t₁ = .ok rr₁) (h₂ : rowsRun E w t₂ = .ok rr₂)
    (hrows : w₁.rows = rr₁.1)
    (hl : ∀ c, (t₂.touches.any fun y => decide (y.cell = c)) = true → w₁.live E c = w.live E c) :
    ∃ rr, rowsRun E w₁ t₂ = .ok rr ∧ rr.2 = 0 ∧
      ∀ s, rr.1.get (rowSpec E) s =
        view (headFloor E w.rows) t₂.rows s (view (headFloor E w.rows) t₁.rows s (w.rows.get (rowSpec E) s)) := by
  obtain ⟨hn₁, hf₁⟩ := rowsRun_fold hnr₁ h₁
  obtain ⟨hn₂, hf₂⟩ := rowsRun_fold hnr₂ h₂
  obtain ⟨-, hv₁, -⟩ := fold_fwd _ _ _ hi₁ hn₁ hf₁
  obtain ⟨-, -, hc1, hc2⟩ := fold_fwd _ _ _ hi₂ hn₂ hf₂
  simp only at hv₁ hc1 hc2
  have hcond : Cond E w₁ t₂ w₁.rows t₂.rows := by
    refine ⟨fun z hz kz amt v hzs hza => ?_, fun p rel hpos => ?_⟩
    · obtain ⟨hst, hrow, c, sm, l, cap, rt, hh⟩ := hc1 z hz kz amt v hzs hza
      have hout : ∀ x ∈ t₁.rows, x.slot ≠ .row kz := fun x hx e => hd x hx z hz (e.trans hzs.symm)
      refine ⟨stat_live hl hst, ?_, c + insN kz.parent kz.rel t₁.rows, sm + insA kz.parent kz.rel t₁.rows,
        l, cap, rt, ?_⟩
      · unfold rowAt at hrow ⊢; rw [hrows, hv₁, view_row_out _ _ _ _ hout]; exact hrow
      · apply get_headOf; rw [hrows, hv₁, headOf_some hh, view_head]
    · obtain ⟨c, sm, l, cap, wd, rt, hh, -, -⟩ := hc2 p rel hpos
      obtain ⟨f1, f2⟩ := hfit p rel (by omega) c sm l cap wd rt hh
      refine ⟨c + insN p rel t₁.rows, sm + insA p rel t₁.rows, l, cap, wd, rt, ?_, by omega, by omega⟩
      apply get_headOf; rw [hrows, hv₁, headOf_some hh, view_head]
  obtain ⟨r', hr'⟩ := fold_bwd _ w₁.rows 0 hi₂ hn₂ hcond
  obtain ⟨-, hv, -⟩ := fold_fwd _ _ _ hi₂ hn₂ hr'
  have hF : headFloor E w₁.rows = headFloor E w.rows := headFloor_view (fun s => by rw [hrows, hv₁])
  refine ⟨(r', 0), rowsRun_of_fold hnr₂ h₂ hr', rfl, fun s => ?_⟩
  rw [hv s]; simp only; rw [hF, hrows, hv₁]

/-- **The rows commute (the rows-level core of `admit_comm`).** Two turns that retire nothing and
only insert, into disjoint row slots, whose inserts fit together in every relation, each run from
the World: then from any World holding the other's rows (and the same live parents on what each
pins), each still runs, in both orders; both orders give nothing back, read the same at every
slot, and every head has moved by the sum of both turns' inserts. -/
theorem rowsRun_comm {E : Env D} {w w₁ w₂ : World D} {t₁ t₂ : Turn D} {rr₁ rr₂ : Rows D × Nat}
    (hnr₁ : NoRetire t₁) (hnr₂ : NoRetire t₂) (hi₁ : InsOnly t₁.rows) (hi₂ : InsOnly t₂.rows)
    (hd : ∀ x ∈ t₁.rows, ∀ y ∈ t₂.rows, x.slot ≠ y.slot) (hfit : RowsFitTogether E w.rows t₁ t₂)
    (h₁ : rowsRun E w t₁ = .ok rr₁) (h₂ : rowsRun E w t₂ = .ok rr₂)
    (hrows₁ : w₁.rows = rr₁.1) (hrows₂ : w₂.rows = rr₂.1)
    (hl₁ : ∀ c, (t₂.touches.any fun y => decide (y.cell = c)) = true → w₁.live E c = w.live E c)
    (hl₂ : ∀ c, (t₁.touches.any fun y => decide (y.cell = c)) = true → w₂.live E c = w.live E c) :
    ∃ rr₁₂ rr₂₁, rowsRun E w₁ t₂ = .ok rr₁₂ ∧ rowsRun E w₂ t₁ = .ok rr₂₁ ∧
      rr₁₂.2 = 0 ∧ rr₂₁.2 = 0 ∧ (∀ s, rowAt E rr₁₂.1 s = rowAt E rr₂₁.1 s) ∧
      ∀ p rel c sm l cap wd rt, headOf E w.rows p rel = some (c, sm, l, cap, wd, rt) →
        headOf E rr₁₂.1 p rel = some (c + insN p rel t₁.rows + insN p rel t₂.rows,
          sm + insA p rel t₁.rows + insA p rel t₂.rows, l, cap, wd, rt) := by
  have hd' : ∀ y ∈ t₂.rows, ∀ x ∈ t₁.rows, y.slot ≠ x.slot := fun y hy x hx e => hd x hx y hy e.symm
  obtain ⟨rr₁₂, hr₁₂, hf₁₂, hv₁₂⟩ := rowsRun_after hnr₁ hnr₂ hi₁ hi₂ hd hfit h₁ h₂ hrows₁ hl₁
  obtain ⟨rr₂₁, hr₂₁, hf₂₁, hv₂₁⟩ := rowsRun_after hnr₂ hnr₁ hi₂ hi₁ hd' (fit_symm hfit) h₂ h₁ hrows₂ hl₂
  refine ⟨rr₁₂, rr₂₁, hr₁₂, hr₂₁, hf₁₂, hf₂₁, fun s => ?_, fun p rel c sm l cap wd rt hh => ?_⟩
  · unfold rowAt; rw [hv₁₂, hv₂₁, view_comm hd]
  · apply get_headOf; rw [hv₁₂, headOf_some hh, view_head, view_head]

/-! ## The cells under two turns -/

omit [Ord D] in
private theorem insertAll_congr {E : Env D} {c : D} :
    ∀ {m m' : Cells D} {ps : List (D × Entry)}, m.get (trieSpec E) (.cell c) = m'.get (trieSpec E) (.cell c) →
      (insertAll E m ps).get (trieSpec E) (.cell c) = (insertAll E m' ps).get (trieSpec E) (.cell c)
  | _, _, [], h => h
  | m, m', p :: rest, h => by
      show (insertAll E (m.insert (trieSpec E) (.cell p.1) (.entry p.2)) rest).get _ _ =
        (insertAll E (m'.insert (trieSpec E) (.cell p.1) (.entry p.2)) rest).get _ _
      apply insertAll_congr
      rw [Trie.get_insert, Trie.get_insert]
      by_cases hc : (Slot.cell c : Slot D) = .cell p.1
      · rw [if_pos hc, if_pos hc]
      · rw [if_neg hc, if_neg hc]; exact h

/-- The map after a turn, at a cell, depends on the map before only through that cell. -/
private theorem commitTrie_congr {E : Env D} {w' w'' : World D} {t : Turn D} {posts : List (Post D)} {c : D}
    (h : w'.trie.get (trieSpec E) (.cell c) = w''.trie.get (trieSpec E) (.cell c)) :
    (commitTrie E w' t posts).get (trieSpec E) (.cell c) = (commitTrie E w'' t posts).get (trieSpec E) (.cell c) := by
  rw [commitTrie_cell, commitTrie_cell]; exact insertAll_congr (insertAll_congr h)

/-! ## The footprint and the second admission -/

/-- **Footprints disjoint outside the heads** (KERNEL-46 amendment 3): distinct transaction ids; a
cell both turns touch is only pinned (`keep`) by both; neither retires a cell; a cell one bears is
neither touched nor borne by the other; no nullifier spent by both; every row touch an insert, into
row slots the other does not name; no range reads. Every clause reads the two Turns only. -/
def RowsCommFoot (t₁ t₂ : Turn D) : Prop :=
  t₁.txId ≠ t₂.txId ∧
  (∀ x ∈ t₁.touches, ∀ y ∈ t₂.touches, x.cell = y.cell → x.act = .keep ∧ y.act = .keep) ∧
  NoRetire t₁ ∧ NoRetire t₂ ∧
  (∀ c ∈ createdIds t₁, c ∉ t₂.touches.map Touch.cell ∧ c ∉ createdIds t₂) ∧
  (∀ c ∈ createdIds t₂, c ∉ t₁.touches.map Touch.cell) ∧
  (∀ n ∈ t₁.nullifiers, n ∉ t₂.nullifiers) ∧
  InsOnly t₁.rows ∧ InsOnly t₂.rows ∧
  (∀ x ∈ t₁.rows, ∀ y ∈ t₂.rows, x.slot ≠ y.slot) ∧
  t₁.ranges = [] ∧ t₂.ranges = []

omit [Ord D] [DecidableEq D] in
private theorem foot_symm {t₁ t₂ : Turn D} (h : RowsCommFoot t₁ t₂) : RowsCommFoot t₂ t₁ := by
  obtain ⟨hid, hk, hr₁, hr₂, hb₁, hb₂, hn, hi₁, hi₂, hd, hq₁, hq₂⟩ := h
  refine ⟨Ne.symm hid, fun y hy x hx e => (hk x hx y hy e.symm).symm, hr₂, hr₁,
    fun c hc => ⟨hb₂ c hc, fun h' => (hb₁ c h').2 hc⟩, fun c hc => (hb₁ c hc).1,
    fun n hn₂ hn₁ => hn n hn₁ hn₂, hi₂, hi₁, fun y hy x hx e => hd x hx y hy e.symm, hq₂, hq₁⟩

omit [Ord D] [DecidableEq D] in
/-- Disjoint footprints share no cell: a cell in one turn's `CellFoot` is outside the other's. -/
private theorem foot_cell_disjoint {t₁ t₂ : Turn D} {c : D} (hfoot : RowsCommFoot t₁ t₂)
    (h₁ : CellFoot t₁ (.cell c)) : ¬ CellFoot t₂ (.cell c) := by
  obtain ⟨-, hkp, -, -, hb₁, hb₂, -⟩ := hfoot
  cases h₁ with
  | touched hx hne =>
      exact not_cellFoot_iff.mpr ⟨fun y hy hyc => absurd (hkp _ hx _ hy hyc.symm).1 hne,
        fun hb => hb₂ _ hb (List.mem_map_of_mem hx)⟩
  | born hc =>
      exact not_cellFoot_iff.mpr ⟨fun y hy hyc => absurd (by rw [← hyc]; exact List.mem_map_of_mem hy) (hb₁ _ hc).1,
        (hb₁ _ hc).2⟩

/-- **The second admission**: after `t₁`, `t₂` passes every check with the touches' results it had
from `w`, and its rows run from `t₁`'s, reading `view` of both lists. -/
private theorem check_after {E : Env D} {w : World D} {t₁ t₂ : Turn D} {posts₁ posts₂ : List (Post D)}
    (hjc : w.JournalCanon E) (hrc : w.RefusalsCanon E)
    (hfoot : RowsCommFoot t₁ t₂) (hfit : RowsFitTogether E w.rows t₁ t₂)
    (hwin : w.height + 2 ≤ t₂.validUntil) (hchg : t₁.charge + t₂.charge ≤ w.allowance)
    (hsteps : w.steps + 2 < Bounds.counterLimit)
    (hk₁ : Checked E w t₁ posts₁) (hk₂ : Checked E w t₂ posts₂) (hnew : w.journalAt E t₂.txId = none)
    (ha₁ : World.admit E w t₁ = .ok (commit E w t₁ posts₁)) :
    check E (commit E w t₁ posts₁) t₂ = .ok posts₂ ∧
      ∀ s, (rowsAfter E (commit E w t₁ posts₁) t₂).1.get (rowSpec E) s =
        view (headFloor E w.rows) t₂.rows s (view (headFloor E w.rows) t₁.rows s (w.rows.get (rowSpec E) s)) := by
  obtain ⟨hid, hkp, hnr₁, hnr₂, hb₁, hb₂, hnul, hi₁, hi₂, hd, -, hq₂⟩ := hfoot
  -- every cell `t₂` reads, in `(commit E w t₁ posts₁)` as in `w`
  have hcells : ∀ s, CellRead t₂ s →
      (commit E w t₁ posts₁).trie.get (trieSpec E) s = w.trie.get (trieSpec E) s := by
    intro s hs
    cases hs with
    | @touched y hy =>
        exact (admit_Frame ha₁).cells _ (not_cellFoot_iff.mpr
          ⟨fun x hx hxc => (hkp x hx y hy hxc).1, fun hc1 => (hb₁ _ hc1).1 (List.mem_map_of_mem hy)⟩)
    | @born c hc =>
        exact (admit_Frame ha₁).cells _ (not_cellFoot_iff.mpr
          ⟨fun x hx hxc => absurd (List.mem_map_of_mem hx) (hxc ▸ hb₂ c hc), fun hc1 => (hb₁ c hc1).2 hc⟩)
    | @spent n hn =>
        show (commitTrie E w t₁ posts₁).get _ _ = _
        rw [commitTrie_nul, if_neg fun h1 => hnul n h1 hn]
  -- the rows
  have hrun₁ := hk₁.rows
  have hrun₂ := hk₂.rows
  obtain ⟨rr, hrr, hrr0, hview⟩ := rowsRun_after hnr₁ hnr₂ hi₁ hi₂ hd hfit hrun₁ hrun₂ rfl (live_local hcells)
  have hafter : rowsAfter E (commit E w t₁ posts₁) t₂ = rr := by unfold rowsAfter; rw [hrr]
  refine ⟨?_, by rw [hafter]; exact hview⟩
  -- the touches
  obtain ⟨raw, hmap, hposts⟩ := hk₂.touches
  have hmap' : mapEx (touchCheck E (commit E w t₁ posts₁)) t₂.touches = .ok raw := by
    rw [← hmap]
    exact touches_local hcells
  -- the window
  have hwin' : checkWindow (commit E w t₁ posts₁) t₂ = .ok () := by
    have h := hk₂.window
    simp only [checkWindow, req_ok, Bool.and_eq_true, decide_eq_true_eq] at h ⊢
    exact ⟨by show _ ≤ w.height + 1 + 1; omega, by show w.height + 1 + 1 ≤ _; omega⟩
  -- the journal
  have hjour : checkJournal E (commit E w t₁ posts₁) t₂ = .ok () := by
    have h := hk₂.journal
    unfold checkJournal at h ⊢
    rw [hnew] at h
    have hj : (commit E w t₁ posts₁).journalAt E t₂.txId = none := by
      rw [commit_journalAt hjc, if_neg (Ne.symm hid), hnew]
      split <;> rfl
    rw [hj]
    have hr : (commit E w t₁ posts₁).refusalAt E (.tx t₂.txId) =
        if (w.height + 1) % Bounds.windowMax = 0 then (w.refusalAt E (.tx t₂.txId)).filter
          (keptRefusal (w.height + 1) (.tx t₂.txId)) else w.refusalAt E (.tx t₂.txId) :=
      pruneRefusals_get hrc _
    have hw : ∀ hh code mb, w.refusalAt E (.tx t₂.txId) ≠ some (.refused hh code mb) := by
      intro hh code mb he; rw [he] at h; simp at h
    have hw1 : ∀ hh code mb, (commit E w t₁ posts₁).refusalAt E (.tx t₂.txId) ≠ some (.refused hh code mb) := by
      intro hh code mb he
      rw [hr] at he
      split at he
      · cases hra : w.refusalAt E (.tx t₂.txId) with
        | none => rw [hra] at he; simp at he
        | some lf =>
            rw [hra] at he
            simp only [Option.filter] at he
            split at he
            · exact hw hh code mb (by rw [hra, he])
            · simp at he
      · exact hw hh code mb he
    cases hra : (commit E w t₁ posts₁).refusalAt E (.tx t₂.txId) with
    | none => rfl
    | some lf =>
        cases lf with
        | refused hh code mb => exact absurd hra (hw1 hh code mb)
        | count n => rfl
  -- the nullifiers
  have hnul' : checkNullifiers E (commit E w t₁ posts₁) t₂ = .ok () := by
    rw [checkNullifiers_local hcells]; exact hk₂.nullifiers
  -- no retirement: no row remains to check
  have hremain : checkRowsRemain E (commit E w t₁ posts₁) t₂ = .ok () := by
    apply forEx_ok.mpr
    intro x hx
    cases ha : x.act with
    | retire => exact absurd ha (hnr₂ x hx)
    | keep => rfl
    | write _ => rfl
  have hranges : checkRanges E (commit E w t₁ posts₁) t₂ = .ok () := by unfold checkRanges; rw [hq₂]; rfl
  -- the charge
  have hcharge : checkCharge (commit E w t₁ posts₁) t₂ (credit posts₂ + rr.2) = .ok () := by
    have h := hk₂.charge
    simp only [checkCharge, except_bind_ok, req_ok, decide_eq_true_eq] at h ⊢
    obtain ⟨⟨⟩, hc1, -⟩ := h
    refine ⟨(), hc1, ?_⟩
    show t₂.charge ≤ w.allowance + credit posts₁ + (rowsAfter E w t₁).2 - t₁.charge + _
    omega
  -- the births
  have hcreates : checkCreates E (commit E w t₁ posts₁) t₂ = .ok () := by
    rw [checkCreates_local hcells]; exact hk₂.creates
  have hst : checkSteps (commit E w t₁ posts₁) = .ok () := by
    unfold checkSteps; rw [req_ok]; exact decide_eq_true (by show w.steps + 1 + 1 < _; omega)
  suffices hw : checkWith E (commit E w t₁ posts₁) t₂ = .ok (posts₂, rr) by unfold check; rw [hw]; rfl
  unfold checkWith
  simp only [except_bind_ok]
  exact ⟨(), hk₂.bounds, (), hwin', (), hjour, (), hk₂.shape, raw, hmap', (), hposts ▸ hk₂.value, (), hnul',
    (), hremain, (), hranges, rr, hrr, (), hposts ▸ hcharge, (), hcreates, (), hst, by rw [hposts]; rfl⟩

/-! ## Two rains on one bell -/

/-- **Admission commutes (KERNEL-46 amendment 3).** Two turns admitted from `w`, whose footprints are
disjoint outside the heads (`RowsCommFoot`), whose inserts fit together in every relation they
insert into (`RowsFitTogether`), whose windows reach the height after both, whose charges the
budget covers together, and with room for two steps: BOTH orders admit, they hold the same cells
and nullifiers and read the same at every rows slot, and every head has moved by the sum of both
turns' inserts. (On canonical journals and refusals: every reached World's.) -/
theorem admit_comm {E : Env D} {w w₁ w₂ : World D} {t₁ t₂ : Turn D}
    (hjc : w.JournalCanon E) (hrc : w.RefusalsCanon E)
    (hfoot : RowsCommFoot t₁ t₂) (hfit : RowsFitTogether E w.rows t₁ t₂)
    (hwin₁ : w.height + 2 ≤ t₁.validUntil) (hwin₂ : w.height + 2 ≤ t₂.validUntil)
    (hchg : t₁.charge + t₂.charge ≤ w.allowance) (hsteps : w.steps + 2 < Bounds.counterLimit)
    (h₁ : World.admit E w t₁ = .ok w₁) (h₂ : World.admit E w t₂ = .ok w₂) :
    ∃ w₁₂ w₂₁, World.admit E w₁ t₂ = .ok w₁₂ ∧ World.admit E w₂ t₁ = .ok w₂₁ ∧
      (∀ s, rowAt E w₁₂.rows s = rowAt E w₂₁.rows s) ∧
      (∀ s, w₁₂.trie.get (trieSpec E) s = w₂₁.trie.get (trieSpec E) s) ∧
      ∀ p rel c sm l cap wd rt, headOf E w.rows p rel = some (c, sm, l, cap, wd, rt) →
        headOf E w₁₂.rows p rel = some (c + insN p rel t₁.rows + insN p rel t₂.rows,
          sm + insA p rel t₁.rows + insA p rel t₂.rows, l, cap, wd, rt) := by
  obtain ⟨posts₁, hk₁, rfl⟩ := admit_ok h₁
  obtain ⟨posts₂, hk₂, rfl⟩ := admit_ok h₂
  obtain ⟨hc12, hv12⟩ := check_after hjc hrc hfoot hfit hwin₂ hchg hsteps hk₁ hk₂ (admit_new h₂) h₁
  obtain ⟨hc21, hv21⟩ := check_after hjc hrc (foot_symm hfoot) (fit_symm hfit) hwin₁ (by omega) hsteps
    hk₂ hk₁ (admit_new h₁) h₂
  have hd := hfoot.2.2.2.2.2.2.2.2.2.1
  have h₁₂ : World.admit E (commit E w t₁ posts₁) t₂ = .ok (commit E (commit E w t₁ posts₁) t₂ posts₂) := by
    unfold World.admit; rw [hc12]
  have h₂₁ : World.admit E (commit E w t₂ posts₂) t₁ = .ok (commit E (commit E w t₂ posts₂) t₁ posts₁) := by
    unfold World.admit; rw [hc21]
  refine ⟨commit E (commit E w t₁ posts₁) t₂ posts₂, commit E (commit E w t₂ posts₂) t₁ posts₁,
    h₁₂, h₂₁, fun s => ?_, fun s => ?_,
    fun p rel c sm l cap wd rt hh => ?_⟩
  · show rowAt E (rowsAfter E _ t₂).1 s = rowAt E (rowsAfter E _ t₁).1 s
    unfold rowAt; rw [hv12, hv21, view_comm hd]
  · show (commitTrie E (commit E w t₁ posts₁) t₂ posts₂).get _ s = (commitTrie E (commit E w t₂ posts₂) t₁ posts₁).get _ s
    cases s with
    | nullifier n =>
        rw [commitTrie_nul, commitTrie_nul]
        show (if n ∈ t₂.nullifiers then some .spent else (commitTrie E w t₁ posts₁).get _ _) =
          (if n ∈ t₁.nullifiers then some .spent else (commitTrie E w t₂ posts₂).get _ _)
        rw [commitTrie_nul, commitTrie_nul]
        by_cases h1 : n ∈ t₁.nullifiers <;> by_cases h2 : n ∈ t₂.nullifiers <;> simp [h1, h2]
    | cell c =>
        by_cases hf₁ : CellFoot t₁ (.cell c)
        · have hf₂ := foot_cell_disjoint hfoot hf₁
          exact ((admit_Frame h₁₂).cells _ hf₂).trans (commitTrie_congr ((admit_Frame h₂).cells _ hf₂).symm)
        · exact (commitTrie_congr ((admit_Frame h₁).cells _ hf₁)).trans ((admit_Frame h₂₁).cells _ hf₁).symm
  · apply get_headOf
    show (rowsAfter E _ t₂).1.get _ _ = _
    rw [hv12, headOf_some hh, view_head, view_head]

/-- **One trie, so one root**: on a lawful `Env` and a canonical World, the two orders' cell tries are
equal (`trie_ext`: contents determine a canonical trie). -/
theorem admit_comm_trie {E : Env D} {n : Nat} (hE : E.Lawful n) {w w₁ w₂ w₁₂ w₂₁ : World D}
    {t₁ t₂ : Turn D} (hc : w.Canon E) (h₁ : World.admit E w t₁ = .ok w₁) (h₂ : World.admit E w t₂ = .ok w₂)
    (h₁₂ : World.admit E w₁ t₂ = .ok w₁₂) (h₂₁ : World.admit E w₂ t₁ = .ok w₂₁)
    (he : ∀ s, w₁₂.trie.get (trieSpec E) s = w₂₁.trie.get (trieSpec E) s) : w₁₂.trie = w₂₁.trie :=
  trie_ext hE (admit_canon (admit_canon hc h₁) h₁₂) (admit_canon (admit_canon hc h₂) h₂₁) he

/-- **One rows trie, so one rows root**: on a lawful `Env` and a World whose rows are canonical and
fit (`RowsOk`, every reached World's), the two orders' rows tries are equal (`rows_ext`, by
`rows_separateOn`): the rows root the chain commits is the same. -/
theorem admit_comm_rows {E : Env D} {n : Nat} (hE : E.Lawful n) {w w₁ w₂ w₁₂ w₂₁ : World D}
    {t₁ t₂ : Turn D} (hr : w.RowsCanon E) (hok : w.RowsOk E) (h₁ : World.admit E w t₁ = .ok w₁)
    (h₂ : World.admit E w t₂ = .ok w₂) (h₁₂ : World.admit E w₁ t₂ = .ok w₁₂) (h₂₁ : World.admit E w₂ t₁ = .ok w₂₁)
    (he : ∀ s, rowAt E w₁₂.rows s = rowAt E w₂₁.rows s) : w₁₂.rows = w₂₁.rows :=
  rows_ext hE (admit_rowsCanon (admit_rowsCanon hr h₁) h₁₂) (admit_rowsCanon (admit_rowsCanon hr h₂) h₂₁)
    (admit_rowsOk hE (admit_rowsCanon hr h₁) (admit_rowsOk hE hr hok h₁) h₁₂).1 he

/-! ## Teeth -/

/-- A rain: one turn that pins parent `p` (`keep`) and inserts one row into its relation `rel`. -/
private def rain (id p seen : D) (rel : Nat) (k : ByteArray) (amt : Nat) (v : ByteArray) (h ch : Nat) : Turn D :=
  { txId := id, notBefore := h + 1, validUntil := h + 2, touches := [⟨p, seen, .keep⟩], creates := [],
    nullifiers := [], charge := ch, event := ByteArray.empty,
    rows := [⟨.row ⟨p, rel, k⟩, none, .insert amt v⟩], ranges := [] }

omit [Ord D] in
/-- **Tooth 1: two rains on one bell meet the premises.** Two single-insert turns into one relation of
one parent, each pinning the parent with `keep`, under distinct keys and transaction ids, with the
relation's count and sum after both within its limit and cap, satisfy `RowsCommFoot` and
`RowsFitTogether`, their windows reach the height after both, and together they insert two rows
and `a₁ + a₂`. (`admit_comm`'s remaining premises read the World: canonical journal and refusals hold
of every reached World; the budget and the step room are numbers on `w`.) -/
theorem two_rains (E : Env D) (r : Rows D) (h : Nat) (id₁ id₂ p s₁ s₂ : D) (rel : Nat) (k₁ k₂ v₁ v₂ : ByteArray)
    (a₁ a₂ ch₁ ch₂ : Nat) (hid : id₁ ≠ id₂) (hk : k₁ ≠ k₂) {c sm l cap wd : Nat} {rt : Bool}
    (hh : headOf E r p rel = some (c, sm, l, cap, wd, rt)) (hl : c + 2 ≤ l) (hcap : sm + a₁ + a₂ ≤ cap) :
    RowsCommFoot (rain id₁ p s₁ rel k₁ a₁ v₁ h ch₁) (rain id₂ p s₂ rel k₂ a₂ v₂ h ch₂) ∧
      RowsFitTogether E r (rain id₁ p s₁ rel k₁ a₁ v₁ h ch₁) (rain id₂ p s₂ rel k₂ a₂ v₂ h ch₂) ∧
      h + 2 ≤ (rain id₁ p s₁ rel k₁ a₁ v₁ h ch₁ : Turn D).validUntil ∧
      h + 2 ≤ (rain id₂ p s₂ rel k₂ a₂ v₂ h ch₂ : Turn D).validUntil ∧
      insN p rel (rain id₁ p s₁ rel k₁ a₁ v₁ h ch₁).rows + insN p rel (rain id₂ p s₂ rel k₂ a₂ v₂ h ch₂).rows = 2 ∧
      insA p rel (rain id₁ p s₁ rel k₁ a₁ v₁ h ch₁).rows + insA p rel (rain id₂ p s₂ rel k₂ a₂ v₂ h ch₂).rows =
        a₁ + a₂ := by
  refine ⟨⟨hid, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl⟩, ?_, Nat.le_refl _, Nat.le_refl _, ?_, ?_⟩
  · intro x hx y hy _
    simp only [rain, List.mem_singleton] at hx hy
    subst hx hy; exact ⟨rfl, rfl⟩
  · intro x hx; simp only [rain, List.mem_singleton] at hx; subst hx; intro e; cases e
  · intro x hx; simp only [rain, List.mem_singleton] at hx; subst hx; intro e; cases e
  · intro c hc; simp [rain, createdIds] at hc
  · intro c hc; simp [rain, createdIds] at hc
  · intro n hn; simp [rain] at hn
  · intro x hx; simp only [rain, List.mem_singleton] at hx; subst hx; exact ⟨_, _, _, rfl, rfl⟩
  · intro x hx; simp only [rain, List.mem_singleton] at hx; subst hx; exact ⟨_, _, _, rfl, rfl⟩
  · intro x hx y hy e
    simp only [rain, List.mem_singleton] at hx hy
    subst hx hy
    simp only [RowSlot.row.injEq, RowKey.mk.injEq] at e
    exact hk e.2.2
  · intro p' rel' hpos c' sm' l' cap' wd' rt' hh'
    by_cases hpr : p = p' ∧ rel = rel'
    · obtain ⟨rfl, rfl⟩ := hpr
      rw [hh] at hh'
      simp only [Option.some.injEq, Prod.mk.injEq] at hh'
      obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := hh'
      simp [rain, insN, insA, insN1, insA1]
      omega
    · simp [rain, insN, insN1, hpr] at hpos
  · simp [rain, insN, insN1]
  · simp [rain, insA, insA1]

/-- The REJECTED design (KERNEL-46 amendment 3): an insert that also pins its relation's head (the
signer's `seen` is the head's pin), then runs as an insert. -/
private def plantStep (E : Env D) (w : World D) (t : Turn D) (r : Rows D) (x : RowTouch D) :
    Except (Reject D) (Rows D) :=
  match x.slot, x.act with
  | .row key, .insert _ _ => do
      req (decide (x.seen = some (rowPin E (headFloor E r key.parent key.rel) (rowAt E r (.head key.parent key.rel))))) (.stale key.parent)
      rowStep E w t r { x with seen := none }
  | _, _ => rowStep E w t r x

/-- **Tooth 2: an insert that pins its head refuses the second rain `stale`.** After the first rain
inserts into a relation, the head has moved (its count by one), so a second insert into the same
relation whose head pin was taken on the rows before is refused under `plantStep`, whatever else is
true, unless two different row leaves share a digest. `admit_comm` needs heads unpinned. -/
theorem plant_second_rain_stale {E : Env D} {w : World D} {t₁ t₂ : Turn D} {r r₁ : Rows D}
    {x₁ x₂ : RowTouch D} {k₁ k₂ : RowKey D} {a₁ a₂ : Nat} {v₁ v₂ : ByteArray}
    (hinj : ∀ l l' : RowLeaf, rowDigest E l = rowDigest E l' → l = l')
    (hs₁ : x₁.slot = .row k₁) (ha₁ : x₁.act = .insert a₁ v₁) (h₁ : rowStep E w t₁ r x₁ = .ok r₁)
    (hs₂ : x₂.slot = .row k₂) (ha₂ : x₂.act = .insert a₂ v₂) (hp : k₂.parent = k₁.parent) (hr : k₂.rel = k₁.rel)
    (hseen : x₂.seen = some (rowPin E (headFloor E r k₁.parent k₁.rel) (rowAt E r (.head k₁.parent k₁.rel)))) :
    plantStep E w t₂ r₁ x₂ = .error (.stale k₂.parent) := by
  obtain ⟨-, -, c, sm, l, cap, rt, hh, -, -, hr1⟩ := ins_step_ok hs₁ ha₁ h₁
  have hg := headOf_some hh
  have hmoved : ∀ f f', rowPin E f (rowAt E r₁ (.head k₁.parent k₁.rel)) ≠
      rowPin E f' (rowAt E r (.head k₁.parent k₁.rel)) := by
    intro f f'
    rw [hr1]
    unfold rowAt
    rw [get_step, if_pos rfl, hg]
    intro e
    have := hinj _ _ e
    injection this with e1
    omega
  obtain ⟨slot, seen, act⟩ := x₂
  simp only at hs₂ ha₂ hseen
  subst hs₂ ha₂ hseen
  unfold plantStep
  simp only [hp, hr]
  have hne : ¬ (some (rowPin E (headFloor E r k₁.parent k₁.rel) (rowAt E r (.head k₁.parent k₁.rel))) =
      some (rowPin E (headFloor E r₁ k₁.parent k₁.rel) (rowAt E r₁ (.head k₁.parent k₁.rel)))) :=
    fun e => hmoved _ _ (Option.some.inj e).symm
  rw [decide_eq_false hne]
  rfl

/-- **Tooth 3: a written parent re-pins.** If the first turn WRITES a cell the second pins, and the
write moves that cell's pin, the footprint is not `RowsCommFoot`, and the second turn is refused
after the first (`stale_refused`): the `keep`-only clause of the footprint is what lets both pin
one parent. -/
theorem write_repin_refused {E : Env D} {w w₁ w₂ : World D} {t₁ t₂ : Turn D} {x y : Touch D} {ops : List Op}
    (h₂ : World.admit E w t₂ = .ok w₂) (hx : x ∈ t₁.touches) (hxw : x.act = .write ops)
    (hy : y ∈ t₂.touches) (hxy : x.cell = y.cell)
    (hmove : pinOf E (w₁.entry E x.cell) ≠ pinOf E (w.entry E x.cell)) :
    ¬ RowsCommFoot t₁ t₂ ∧ ∀ w', World.admit E w₁ t₂ ≠ .ok w' := by
  refine ⟨fun hf => ?_, stale_refused hy ?_⟩
  · have := (hf.2.1 x hx y hy hxy).1
    rw [hxw] at this; cases this
  · rw [← admit_pins h₂ y hy, ← hxy]; exact hmove

end

end Nanodregg.Kernel
