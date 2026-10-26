/-
# Kernel.Proofs.StaleOnly — a `stale` refusal names a pin that disagrees (PROTOCOL-19, KERNEL-23 agreed)

The converse of `stale_refused`, `rows_stale_refused` and `range_stale_refused`: `World.admit` refuses
`.stale y` only where one of the turn's pins disagrees with the World it is judged on — a touch's
cell pin, a pinned row touch's row pin, or a range read's listing pin, each naming `y`. `.stale` is
built at three places only (`touchCheck`, `rowStep`'s `pinned`, `checkRanges`); every other check is
shown never to yield it.
-/
import Kernel.Proofs.Admit
import Kernel.Proofs.Rows
import Kernel.Tactics.StaleOnly

namespace Nanodregg.Kernel

variable {D : Type}

/-- A check whose every `stale y` refusal satisfies `P y`. -/
def StaleOnly {α : Type} (P : D → Prop) (x : Except (Reject D) α) : Prop :=
  ∀ y, x = .error (.stale y) → P y

namespace StaleOnly

variable {P : D → Prop}

theorem ok {α : Type} (a : α) : StaleOnly P (.ok a : Except (Reject D) α) := fun _ h => by cases h

theorem pure' {α : Type} (a : α) : StaleOnly P (pure a : Except (Reject D) α) := fun _ h => by cases h

theorem error {α : Type} {e : Reject D} (he : ∀ y, e = .stale y → P y) :
    StaleOnly P (.error e : Except (Reject D) α) := fun y h => he y (by cases h; rfl)

theorem req {b : Bool} {e : Reject D} (he : ∀ y, e = .stale y → b = false → P y) :
    StaleOnly P (Nanodregg.Kernel.req b e) := by
  intro y h
  unfold Nanodregg.Kernel.req at h
  cases b
  · exact he y (by cases h; rfl) rfl
  · cases h

theorem bind {α β : Type} {x : Except (Reject D) α} {f : α → Except (Reject D) β}
    (hx : StaleOnly P x) (hf : ∀ a, x = .ok a → StaleOnly P (f a)) : StaleOnly P (x >>= f) := by
  intro y h
  cases hc : x with
  | error e =>
    rw [hc] at h
    exact hx y (by rw [hc]; simpa [Bind.bind, Except.bind] using h)
  | ok a => rw [hc] at h; exact hf a hc y h

theorem forEx {α : Type} {f : α → Except (Reject D) Unit} :
    ∀ {l : List α}, (∀ a ∈ l, StaleOnly P (f a)) → StaleOnly P (Nanodregg.Kernel.forEx f l)
  | [], _ => fun _ h => by cases h
  | a :: rest, hl => by
      intro y h
      unfold Nanodregg.Kernel.forEx at h
      split at h
      · exact forEx (fun b hb => hl b (List.mem_cons_of_mem _ hb)) y h
      · rename_i e he
        exact hl a List.mem_cons_self y (by rw [he]; cases h; rfl)

theorem mapEx {α β : Type} {f : α → Except (Reject D) β} :
    ∀ {l : List α}, (∀ a ∈ l, StaleOnly P (f a)) → StaleOnly P (Nanodregg.Kernel.mapEx f l)
  | [], _ => fun _ h => by cases h
  | a :: rest, hl => by
      intro y h
      unfold Nanodregg.Kernel.mapEx at h
      split at h
      · split at h
        · cases h
        · rename_i e he
          exact mapEx (fun b hb => hl b (List.mem_cons_of_mem _ hb)) y (by rw [he]; cases h; rfl)
      · rename_i e he
        exact hl a List.mem_cons_self y (by rw [he]; cases h; rfl)

theorem noDup {α : Type} [Ord α] {l : List α} {e : α → Reject D} (he : ∀ a y, e a ≠ .stale y) :
    StaleOnly P (Nanodregg.Kernel.noDup l e) := by
  intro y h
  unfold Nanodregg.Kernel.noDup at h
  split at h
  · cases h
  · rename_i a _
    injection h with h'
    exact (he a y h').elim

theorem mono {α : Type} {Q : D → Prop} {x : Except (Reject D) α} (h : StaleOnly P x)
    (hpq : ∀ y, P y → Q y) : StaleOnly Q x := fun y hy => hpq y (h y hy)

theorem none {α : Type} {x : Except (Reject D) α} (h : StaleOnly (fun _ => False) x) : StaleOnly P x :=
  fun y hy => (h y hy).elim

end StaleOnly

variable [Ord D] [DecidableEq D]

omit [Ord D] [DecidableEq D] in
theorem checkBounds_staleOnly {P : D → Prop} (t : Turn D) : StaleOnly P (checkBounds t) := by
  unfold checkBounds; stale_only

omit [DecidableEq D] in
theorem checkWindow_staleOnly {P : D → Prop} (w : World D) (t : Turn D) : StaleOnly P (checkWindow w t) := by
  unfold checkWindow; stale_only

theorem checkJournal_staleOnly {P : D → Prop} (E : Env D) (w : World D) (t : Turn D) :
    StaleOnly P (checkJournal E w t) := by
  unfold checkJournal; stale_only

omit [DecidableEq D] in
theorem checkShape_staleOnly {P : D → Prop} (t : Turn D) : StaleOnly P (checkShape t) := by
  unfold checkShape; stale_only

omit [Ord D] [DecidableEq D] in
theorem checkValueCell_staleOnly {P : D → Prop} (c : D) (cell : Cell) : StaleOnly P (checkValueCell c cell) := by
  unfold checkValueCell; stale_only

omit [Ord D] [DecidableEq D] in
theorem checkValue_staleOnly {P : D → Prop} (E : Env D) (t : Turn D) (posts : List (Post D)) :
    StaleOnly P (checkValue E t posts) := by
  unfold checkValue
  stale_only
  all_goals exact checkValueCell_staleOnly _ _

theorem checkNullifiers_staleOnly {P : D → Prop} (E : Env D) (w : World D) (t : Turn D) :
    StaleOnly P (checkNullifiers E w t) := by
  unfold checkNullifiers; stale_only

omit [DecidableEq D] in
theorem checkRowsRemain_staleOnly {P : D → Prop} (E : Env D) (w : World D) (t : Turn D) :
    StaleOnly P (checkRowsRemain E w t) := by
  unfold checkRowsRemain; stale_only

omit [DecidableEq D] in
theorem checkCharge_staleOnly {P : D → Prop} (w : World D) (t : Turn D) (b : Nat) :
    StaleOnly P (checkCharge w t b) := by
  unfold checkCharge; stale_only

theorem checkCreates_staleOnly {P : D → Prop} (E : Env D) (w : World D) (t : Turn D) :
    StaleOnly P (checkCreates E w t) := by
  unfold checkCreates; stale_only

theorem checkTicks_staleOnly {P : D → Prop} (E : Env D) (w : World D) (t : Turn D) :
    StaleOnly P (checkTicks E w t) := by
  unfold checkTicks; stale_only

omit [DecidableEq D] in
theorem checkSteps_staleOnly {P : D → Prop} (w : World D) : StaleOnly P (checkSteps (D := D) w) := by
  unfold checkSteps; stale_only

omit [Ord D] [DecidableEq D] in
theorem postWrite_staleOnly {P : D → Prop} (c : D) (cell : Cell) (ops : List Op) :
    StaleOnly P (postWrite c cell ops) := by
  unfold postWrite
  stale_only
  all_goals exact checkValueCell_staleOnly _ _

/-- A touch is refused `stale` only by its own cell pin disagreeing. -/
theorem touchCheck_staleOnly (E : Env D) (w : World D) (x : Touch D) :
    StaleOnly (fun y => x.cell = y ∧ pinOf E (w.entry E x.cell) ≠ x.seen) (touchCheck E w x) := by
  by_cases hp : pinOf E (w.entry E x.cell) = x.seen
  · intro y h
    exfalso
    revert h
    apply StaleOnly.none (P := fun _ => False)
    unfold touchCheck
    apply StaleOnly.bind
    · apply StaleOnly.req; intro _ _ hb; simp [hp] at hb
    · intro _ _
      stale_only
      all_goals exact postWrite_staleOnly _ _ _
  · intro y h
    rw [touchCheck_stale hp] at h
    cases h
    exact ⟨rfl, hp⟩

/-- A row touch is refused `stale` only by its own row pin disagreeing with the rows it is judged
on (its relation's floor read on the World's rows, as `rowStep` reads it). -/
theorem rowStep_staleOnly (E : Env D) (w : World D) (t : Turn D) (r : Rows D) (x : RowTouch D) :
    StaleOnly (fun y => ∃ key s, x.slot = .row key ∧ key.parent = y ∧ x.seen = some s ∧
      rowPin E (headFloor E w.rows key.parent key.rel) (rowAt E r (.row key)) ≠ s) (rowStep E w t r x) := by
  obtain ⟨slot, seen, act⟩ := x
  cases slot with
  | head p rel => cases act <;> (unfold rowStep rowStepOn; simp only [setHeadOn_trie]; stale_only)
  | row key =>
    cases act <;> unfold rowStep rowStepOn <;> simp only [headOfOn_trie, headFloorOn_trie, setHeadOn_trie] <;> stale_only
    all_goals
      apply StaleOnly.req
      intro y hy hb
      cases hy
      exact ⟨key, _, rfl, rfl, rfl, by simpa using hb⟩

/-- The rows fold: a `stale` refusal is a pinned row touch whose pin disagrees with the rows the
fold started from (slots are distinct, so no earlier touch of the turn moved its row). -/
theorem foldRows_staleOnly (E : Env D) (w : World D) (t : Turn D) :
    ∀ (l : List (RowTouch D)) (acc : Rows D × Nat), Trie.Canon (rowSpec E) 0 acc.1 →
      (l.map RowTouch.slot).Nodup →
      StaleOnly (fun y => ∃ x ∈ l, ∃ key s, x.slot = .row key ∧ key.parent = y ∧ x.seen = some s ∧
        rowPin E (headFloor E w.rows key.parent key.rel) (rowAt E acc.1 (.row key)) ≠ s)
        (l.foldlM (rowStepFreed E w t) acc)
  | [], _, _, _ => fun _ h => by cases h
  | z :: rest, acc, hc, hn => by
      rw [List.foldlM_cons]
      simp only [List.map_cons, List.nodup_cons] at hn
      apply StaleOnly.bind
      · unfold rowStepFreed rowStepFreedOn; simp only [rowStepOn_trie, rowFreedOn_trie]
        apply StaleOnly.bind
        · exact (rowStep_staleOnly E w t acc.1 z).mono fun y ⟨key, s, h1, h2, h3, h4⟩ =>
            ⟨z, List.mem_cons_self, key, s, h1, h2, h3, h4⟩
        · intros; exact StaleOnly.pure' _
      · intro acc' hacc'
        unfold rowStepFreed rowStepFreedOn at hacc'; simp only [rowStepOn_trie, rowFreedOn_trie] at hacc'
        rw [except_bind_ok] at hacc'
        obtain ⟨r1, hstep, he⟩ := hacc'
        simp only [pure, Except.pure, Except.ok.injEq] at he
        subst he
        have hc1 := (rowStep_weight hc hstep).2
        refine (foldRows_staleOnly E w t rest _ hc1 hn.2).mono ?_
        rintro y ⟨x, hx, key, s, hs, hp, hseen, hne⟩
        refine ⟨x, List.mem_cons_of_mem _ hx, key, s, hs, hp, hseen, ?_⟩
        have hne' : z.slot ≠ .row key := by
          intro e; apply hn.1; rw [e, ← hs]; exact List.mem_map_of_mem hx
        unfold rowAt at hne ⊢
        rwa [rowStep_get_out (s := .row key) hc hstep fun _ => ⟨fun e => hne' e.symm, fun _ _ e => by cases e⟩] at hne

/-- `rowsRun`: a `stale` refusal is a pinned row touch disagreeing with the World's rows. -/
theorem rowsRun_staleOnly (E : Env D) (w : World D) (t : Turn D) (hr : w.RowsCanon E) :
    StaleOnly (fun y => ∃ x ∈ t.rows, ∃ key s, x.slot = .row key ∧ key.parent = y ∧ x.seen = some s ∧
      rowPin E (headFloor E w.rows key.parent key.rel) (rowAt E w.rows (.row key)) ≠ s) (rowsRun E w t) := by
  rw [rowsRun_eq]
  apply StaleOnly.bind
  · apply StaleOnly.req; intro _ h; cases h
  · intro _ _
    apply StaleOnly.bind
    · apply StaleOnly.req; intro _ h; cases h
    · intro _ _
      split
      · apply StaleOnly.error; intro _ h; cases h
      · rename_i hfind
        apply StaleOnly.bind
        · exact foldRows_staleOnly E w t t.rows (w.rows, 0) hr (nodup_of_find_none hfind)
        · intros; exact StaleOnly.pure' _

/-- `checkRanges`: a `stale` refusal is a range read whose listing's pin disagrees. -/
theorem checkRanges_staleOnly (E : Env D) (w : World D) (t : Turn D) :
    StaleOnly (fun y => ∃ q ∈ t.ranges, q.parent = y ∧ ∃ c s lim cap width rt l,
      headOf E w.rows q.parent q.rel = some (c, s, lim, cap, width, rt) ∧
      rangeRows E w.rows q.parent q.rel width q.pre q.most = some l ∧
      rangePin E q.parent q.rel width q.pre (headFloor E w.rows q.parent q.rel) l ≠ q.seen)
      (checkRanges E w t) := by
  unfold checkRanges
  apply StaleOnly.forEx
  intro q hq
  apply StaleOnly.bind
  · apply StaleOnly.req; intro _ h; cases h
  · intro _ _
    split
    · apply StaleOnly.error; intro _ h; cases h
    · rename_i c s lim cap width rt hh
      apply StaleOnly.bind
      · apply StaleOnly.req; intro _ h; cases h
      · intro _ _
        split
        · apply StaleOnly.error; intro _ h; cases h
        · rename_i l hl
          apply StaleOnly.req
          intro y hy hb
          cases hy
          exact ⟨q, hq, rfl, c, s, lim, cap, width, rt, l, hh, hl, by simpa using hb⟩

/-- **A `stale` refusal names a pin that disagrees** (the converse of `stale_refused`,
`rows_stale_refused` and `range_stale_refused`): when `World.admit` refuses a turn `.stale y`, one
of the turn's pins disagrees with the World — a touch's cell pin at `y`, a pinned row touch under
`y` whose row pin is not the World's, or a range read under `y` whose listing's pin is not. -/
theorem admit_stale_pin {E : Env D} {w : World D} {t : Turn D} {y : D}
    (hr : w.RowsCanon E) (h : World.admit E w t = .error (.stale y)) :
    (∃ x ∈ t.touches, x.cell = y ∧ pinOf E (w.entry E x.cell) ≠ x.seen) ∨
    (∃ x ∈ t.rows, ∃ key s, x.slot = .row key ∧ key.parent = y ∧ x.seen = some s ∧
        rowPin E (headFloor E w.rows key.parent key.rel) (rowAt E w.rows (.row key)) ≠ s) ∨
    (∃ q ∈ t.ranges, q.parent = y ∧ ∃ c s lim cap width rt l,
        headOf E w.rows q.parent q.rel = some (c, s, lim, cap, width, rt) ∧
        rangeRows E w.rows q.parent q.rel width q.pre q.most = some l ∧
        rangePin E q.parent q.rel width q.pre (headFloor E w.rows q.parent q.rel) l ≠ q.seen) := by
  have hw : checkWith E w t = .error (.stale y) := by
    unfold World.admit check at h
    cases hc : checkWith E w t with
    | ok pr => rw [hc] at h; cases h
    | error e => rw [hc] at h; cases h; rfl
  suffices hso : StaleOnly (fun y => (∃ x ∈ t.touches, x.cell = y ∧ pinOf E (w.entry E x.cell) ≠ x.seen) ∨
    (∃ x ∈ t.rows, ∃ key s, x.slot = .row key ∧ key.parent = y ∧ x.seen = some s ∧
        rowPin E (headFloor E w.rows key.parent key.rel) (rowAt E w.rows (.row key)) ≠ s) ∨
    (∃ q ∈ t.ranges, q.parent = y ∧ ∃ c s lim cap width rt l,
        headOf E w.rows q.parent q.rel = some (c, s, lim, cap, width, rt) ∧
        rangeRows E w.rows q.parent q.rel width q.pre q.most = some l ∧
        rangePin E q.parent q.rel width q.pre (headFloor E w.rows q.parent q.rel) l ≠ q.seen))
      (checkWith E w t) from hso y hw
  unfold checkWith
  refine StaleOnly.bind (checkBounds_staleOnly t) fun _ _ => ?_
  refine StaleOnly.bind (checkWindow_staleOnly w t) fun _ _ => ?_
  refine StaleOnly.bind (checkJournal_staleOnly E w t) fun _ _ => ?_
  refine StaleOnly.bind (checkShape_staleOnly t) fun _ _ => ?_
  refine StaleOnly.bind (StaleOnly.mapEx fun x hx => (touchCheck_staleOnly E w x).mono
    fun y ⟨h1, h2⟩ => .inl ⟨x, hx, h1, h2⟩) fun _ _ => ?_
  refine StaleOnly.bind (checkValue_staleOnly E t _) fun _ _ => ?_
  refine StaleOnly.bind (checkNullifiers_staleOnly E w t) fun _ _ => ?_
  refine StaleOnly.bind (checkRowsRemain_staleOnly E w t) fun _ _ => ?_
  refine StaleOnly.bind ((checkRanges_staleOnly E w t).mono fun _ h => .inr (.inr h)) fun _ _ => ?_
  refine StaleOnly.bind ((rowsRun_staleOnly E w t hr).mono fun _ h => .inr (.inl h)) fun _ _ => ?_
  refine StaleOnly.bind (checkCharge_staleOnly w t _) fun _ _ => ?_
  refine StaleOnly.bind (checkCreates_staleOnly E w t) fun _ _ => ?_
  refine StaleOnly.bind (checkTicks_staleOnly E w t) fun _ _ => ?_
  refine StaleOnly.bind (checkSteps_staleOnly w) fun _ _ => ?_
  exact StaleOnly.pure' _

/-! ## Each disjunct is live (KERNEL-23's separation instances)

On one concrete World (cell 7 live, its relation 3 declared at width 1, no rows), three turns are
each refused `stale 7`, and for each exactly one of `admit_stale_pin`'s disjuncts holds: a stale
cell pin with no row or range read; a stale row pin under a current cell pin and no range read; a
stale range pin under a current cell pin and no row touch. So no disjunct stands in for another.
Toy parameters only (a byte-sum hash); the deployed hash is never evaluated here. -/

private def sEnv : Env UInt8 where
  hash d b := UInt8.ofNat (d.length + b.size + (b.data.toList.map UInt8.toNat).sum)
  bytes d := ⟨#[d]⟩
  turnBytes _ := ByteArray.empty
  cellBytes _ := ByteArray.empty

private def sCell : Cell := { kind := 0, discipline := .ram, slots := [] }

private def sW : World UInt8 where
  trie := Trie.T.empty.insert (trieSpec sEnv) (.cell 7) (.entry (.live sCell 0))
  journal := .empty
  refusals := .empty
  rows := Trie.T.empty.insert (rowSpec sEnv) (.head 7 3) (.head 0 0 10 100 1 true 0)
  height := 0
  steps := 0
  chain := 0
  allowance := 1000000
  origin := 0

private def sKey : RowKey UInt8 := ⟨7, 3, ⟨#[1]⟩⟩

/-- The current cell pin of cell 7, and a stale one (the absent pin). -/
private def sKeep : Touch UInt8 := ⟨7, pinOf sEnv (some (.live sCell 0)), .keep⟩
private def sStaleKeep : Touch UInt8 := ⟨7, pinOf sEnv none, .keep⟩

private def sTurn0 (ts : List (Touch UInt8)) (rs : List (RowTouch UInt8)) (qs : List (RangeRead UInt8)) :
    Turn UInt8 :=
  { txId := 1, notBefore := 0, validUntil := 1, touches := ts, creates := [], nullifiers := [],
    charge := 0, event := ByteArray.empty, rows := rs, ranges := qs, member := 0 }

private def sTurn (ts : List (Touch UInt8)) (rs : List (RowTouch UInt8)) (qs : List (RangeRead UInt8)) :
    Turn UInt8 := { sTurn0 ts rs qs with charge := (sTurn0 ts rs qs).weight }

/-- A stale cell pin. -/
private def sTc : Turn UInt8 := sTurn [sStaleKeep] [] []
/-- A stale row pin (it names the row present, the row is absent), the cell pin current. -/
private def sTr : Turn UInt8 :=
  sTurn [sKeep] [⟨.row sKey, some (rowPin sEnv 0 (some (.row 1 ByteArray.empty 0))), .keep⟩] []
/-- A stale range pin (the whole relation read at a pin of 0), the cell pin current. -/
private def sTq : Turn UInt8 := sTurn [sKeep] [] [⟨7, 3, ByteArray.empty, 10, 0⟩]

private def staleName (t : Turn UInt8) : Option UInt8 :=
  match World.admit sEnv sW t with
  | .error (.stale y) => some y
  | _ => none

private theorem staleName_eq {t : Turn UInt8} {y : UInt8} (h : staleName t = some y) :
    World.admit sEnv sW t = .error (.stale y) := by
  unfold staleName at h
  split at h
  · rename_i y' he; cases h; exact he
  · cases h

private theorem sTc_stale : staleName sTc = some 7 := by decide +kernel
private theorem sTr_stale : staleName sTr = some 7 := by decide +kernel
private theorem sTq_stale : staleName sTq = some 7 := by decide +kernel
private theorem sKeep_current : pinOf sEnv (sW.entry sEnv 7) = sKeep.seen := by decide +kernel
private theorem sStale_ne : pinOf sEnv (sW.entry sEnv 7) ≠ sStaleKeep.seen := by decide +kernel
private theorem sRow_ne : rowPin sEnv (headFloor sEnv sW.rows sKey.parent sKey.rel) (rowAt sEnv sW.rows (.row sKey)) ≠
    rowPin sEnv 0 (some (.row 1 ByteArray.empty 0)) := by decide +kernel
private theorem sRange : headOf sEnv sW.rows 7 3 = some (0, 0, 10, 100, 1, true) ∧
    rangeRows sEnv sW.rows 7 3 1 ByteArray.empty 10 = some [] ∧
    rangePin sEnv 7 3 1 ByteArray.empty (headFloor sEnv sW.rows 7 3) [] ≠ 0 := by decide +kernel

/-- **The cell disjunct is live**: a turn refused `stale 7` by its cell pin alone. -/
theorem stale_pin_cell_live :
    ∃ (E : Env UInt8) (w : World UInt8) (t : Turn UInt8) (y : UInt8),
      World.admit E w t = .error (.stale y) ∧
      (∃ x ∈ t.touches, x.cell = y ∧ pinOf E (w.entry E x.cell) ≠ x.seen) ∧
      t.rows = [] ∧ t.ranges = [] :=
  ⟨sEnv, sW, sTc, 7, staleName_eq sTc_stale, ⟨sStaleKeep, List.mem_singleton_self _, rfl, sStale_ne⟩, rfl, rfl⟩

/-- **The row disjunct is live**: every cell pin current, no range read, refused `stale 7` by a row pin. -/
theorem stale_pin_row_live :
    ∃ (E : Env UInt8) (w : World UInt8) (t : Turn UInt8) (y : UInt8),
      World.admit E w t = .error (.stale y) ∧
      (∀ x ∈ t.touches, pinOf E (w.entry E x.cell) = x.seen) ∧
      (∃ x ∈ t.rows, ∃ key s, x.slot = .row key ∧ key.parent = y ∧ x.seen = some s ∧
        rowPin E (headFloor E w.rows key.parent key.rel) (rowAt E w.rows (.row key)) ≠ s) ∧
      t.ranges = [] :=
  ⟨sEnv, sW, sTr, 7, staleName_eq sTr_stale,
    fun x hx => by rcases List.mem_singleton.mp hx with rfl; exact sKeep_current,
    ⟨_, List.mem_singleton_self _, sKey, _, rfl, rfl, rfl, sRow_ne⟩, rfl⟩

/-- **The range disjunct is live**: every cell pin current, no row touch, refused `stale 7` by a range pin. -/
theorem stale_pin_range_live :
    ∃ (E : Env UInt8) (w : World UInt8) (t : Turn UInt8) (y : UInt8),
      World.admit E w t = .error (.stale y) ∧
      (∀ x ∈ t.touches, pinOf E (w.entry E x.cell) = x.seen) ∧ t.rows = [] ∧
      (∃ q ∈ t.ranges, q.parent = y ∧ ∃ c s lim cap width rt l,
        headOf E w.rows q.parent q.rel = some (c, s, lim, cap, width, rt) ∧
        rangeRows E w.rows q.parent q.rel width q.pre q.most = some l ∧
        rangePin E q.parent q.rel width q.pre (headFloor E w.rows q.parent q.rel) l ≠ q.seen) :=
  ⟨sEnv, sW, sTq, 7, staleName_eq sTq_stale,
    fun x hx => by rcases List.mem_singleton.mp hx with rfl; exact sKeep_current, rfl,
    ⟨_, List.mem_singleton_self _, rfl, 0, 0, 10, 100, 1, true, [], sRange.1, sRange.2.1, sRange.2.2⟩⟩

/-- **TOOTH (`admit_stale_pin`'s contrapositive)**: a turn whose every pin agrees with the World is
never refused `stale`. -/
theorem admit_not_stale {E : Env D} {w : World D} {t : Turn D} (hr : w.RowsCanon E)
    (hc : ∀ x ∈ t.touches, pinOf E (w.entry E x.cell) = x.seen)
    (hrw : ∀ x ∈ t.rows, ∀ key s, x.slot = .row key → x.seen = some s →
      rowPin E (headFloor E w.rows key.parent key.rel) (rowAt E w.rows (.row key)) = s)
    (hq : ∀ q ∈ t.ranges, ∀ c s lim cap width rt l,
      headOf E w.rows q.parent q.rel = some (c, s, lim, cap, width, rt) →
      rangeRows E w.rows q.parent q.rel width q.pre q.most = some l →
      rangePin E q.parent q.rel width q.pre (headFloor E w.rows q.parent q.rel) l = q.seen)
    (y : D) : World.admit E w t ≠ .error (.stale y) := by
  intro h
  rcases admit_stale_pin hr h with ⟨x, hx, -, hne⟩ | ⟨x, hx, key, s, hs, -, hseen, hne⟩ |
      ⟨q, hq', -, c, s, lim, cap, width, rt, l, hh, hl, hne⟩
  · exact hne (hc x hx)
  · exact hne (hrw x hx key s hs hseen)
  · exact hne (hq q hq' c s lim cap width rt l hh hl)

/-! ## The pins compared before anything is derived (KERNEL-66)

`checkPins` is the Host's comparison of a call's pins with its World before `receive` runs. It passes
exactly when none of the three disagreements `admit_stale_pin` names holds for the call's own pins
(`checkPins_ok_iff`), and it refuses nothing but `stale` (`checkPins_error_stale`). -/

/-- **What `checkPins` passes is agreement** (KERNEL-66): every cell pin agrees with its entry, every
row pin at a row slot with its row and its relation's floor, and every range read whose relation has
a head and whose listing fits its `most` with that listing's pin: `admit_not_stale`'s three premises,
read off the call's pins. -/
theorem checkPins_ok_iff {E : Env D} {w : World D} {pins : List (D × D)} {rowPins : List (RowSlot D × D)}
    {ranges : List (RangeRead D)} :
    checkPins E w pins rowPins ranges = .ok () ↔
      (∀ p ∈ pins, pinOf E (w.entry E p.1) = p.2) ∧
      (∀ p ∈ rowPins, ∀ key, p.1 = .row key →
        rowPin E (headFloor E w.rows key.parent key.rel) (rowAt E w.rows (.row key)) = p.2) ∧
      (∀ q ∈ ranges, ∀ c s lim cap width rt l,
        headOf E w.rows q.parent q.rel = some (c, s, lim, cap, width, rt) →
        rangeRows E w.rows q.parent q.rel width q.pre q.most = some l →
        rangePin E q.parent q.rel width q.pre (headFloor E w.rows q.parent q.rel) l = q.seen) := by
  have hcell : ∀ p : D × D, req (decide (pinOf E (w.entry E p.1) = p.2)) (Reject.stale p.1) = .ok () ↔
      pinOf E (w.entry E p.1) = p.2 := fun p => by rw [req_ok, decide_eq_true_eq]
  have hrow : ∀ p : RowSlot D × D, (match p.1 with
      | .row key => req (decide (rowPin E (headFloor E w.rows key.parent key.rel) (rowAt E w.rows (.row key)) = p.2))
          (Reject.stale key.parent)
      | .head .. => (.ok () : Except (Reject D) Unit)) = .ok () ↔
      ∀ key, p.1 = .row key → rowPin E (headFloor E w.rows key.parent key.rel) (rowAt E w.rows (.row key)) = p.2 := by
    intro ⟨slot, d⟩
    cases slot with
    | head q rel => simp
    | row key => simp [req_ok]
  have hq : ∀ q : RangeRead D, (match headOf E w.rows q.parent q.rel with
      | none => (.ok () : Except (Reject D) Unit)
      | some (_, _, _, _, width, _) =>
          match rangeRows E w.rows q.parent q.rel width q.pre q.most with
          | none => .ok ()
          | some l => req (decide (rangePin E q.parent q.rel width q.pre (headFloor E w.rows q.parent q.rel) l =
              q.seen)) (Reject.stale q.parent)) = .ok () ↔
      ∀ c s lim cap width rt l, headOf E w.rows q.parent q.rel = some (c, s, lim, cap, width, rt) →
        rangeRows E w.rows q.parent q.rel width q.pre q.most = some l →
        rangePin E q.parent q.rel width q.pre (headFloor E w.rows q.parent q.rel) l = q.seen := by
    intro q
    cases hh : headOf E w.rows q.parent q.rel with
    | none => simp
    | some hd =>
      obtain ⟨c, s, lim, cap, width, rt⟩ := hd
      simp only
      constructor
      · intro h c' s' lim' cap' width' rt' l h1 h2
        simp only [Option.some.injEq, Prod.mk.injEq] at h1
        obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := h1
        rw [h2] at h
        exact of_decide_eq_true (req_ok.mp h)
      · intro h
        cases hl : rangeRows E w.rows q.parent q.rel width q.pre q.most with
        | none => rfl
        | some l => exact req_ok.mpr (decide_eq_true (h c s lim cap width rt l rfl hl))
  unfold checkPins
  simp only [except_bind_ok]
  constructor
  · rintro ⟨⟨⟩, hc, ⟨⟩, hr, hg⟩
    exact ⟨fun p hp => (hcell p).mp (forEx_ok.mp hc p hp), fun p hp => (hrow p).mp (forEx_ok.mp hr p hp),
      fun q hq' => (hq q).mp (forEx_ok.mp hg q hq')⟩
  · rintro ⟨hc, hr, hg⟩
    exact ⟨(), forEx_ok.mpr fun p hp => (hcell p).mpr (hc p hp), (), forEx_ok.mpr fun p hp => (hrow p).mpr (hr p hp),
      forEx_ok.mpr fun q hq' => (hq q).mpr (hg q hq')⟩

omit [Ord D] [DecidableEq D] in
private theorem forEx_error_stale {α : Type} {f : α → Except (Reject D) Unit}
    (hf : ∀ a e, f a = .error e → ∃ y, e = .stale y) :
    ∀ {l : List α} {e : Reject D}, Nanodregg.Kernel.forEx f l = .error e → ∃ y, e = .stale y
  | [], _, h => by cases h
  | a :: rest, e, h => by
      unfold Nanodregg.Kernel.forEx at h
      split at h
      · exact forEx_error_stale hf h
      · rename_i e' he
        cases h
        exact hf a _ he

omit [Ord D] [DecidableEq D] in
private theorem req_error_stale {b : Bool} {y : D} {e : Reject D} (h : req b (Reject.stale y) = .error e) :
    e = .stale y := by
  cases b <;> simp [req] at h; exact h.symm

/-- **`checkPins` refuses nothing but `stale`**: a disagreement is the only thing it reads. -/
theorem checkPins_error_stale {E : Env D} {w : World D} {pins : List (D × D)} {rowPins : List (RowSlot D × D)}
    {ranges : List (RangeRead D)} {e : Reject D} (h : checkPins E w pins rowPins ranges = .error e) :
    ∃ y, e = .stale y := by
  unfold checkPins at h
  cases h1 : Nanodregg.Kernel.forEx (fun p => req (decide (pinOf E (w.entry E p.1) = p.2)) (Reject.stale p.1)) pins with
  | error e1 =>
    rw [h1] at h; cases h
    exact forEx_error_stale (fun p _ he => ⟨_, req_error_stale he⟩) h1
  | ok u =>
    rw [h1] at h
    simp only [bind, Except.bind] at h
    split at h
    · rename_i e2 h2
      cases h
      refine forEx_error_stale (fun p e' he => ?_) h2
      obtain ⟨slot, d⟩ := p
      cases slot with
      | head _ _ => cases he
      | row key => exact ⟨_, req_error_stale he⟩
    · refine forEx_error_stale (fun q e' he => ?_) h
      simp only at he
      split at he
      · cases he
      · split at he
        · cases he
        · exact ⟨_, req_error_stale he⟩

end Nanodregg.Kernel
