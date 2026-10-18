/-
# Kernel.Proofs.RowsHead — every reached World's rows are well-formed (KERNEL-48)

`World.RowsOk` is the reached-World rows invariant, stated on the Bool predicates a decoded base is
checked by (`rowFits`, `rowsHeaded`, `rowsParented`: CODEC-9 refines its decode on them):

* every rows entry fits its kind and every bound admission keeps (`rowFits`);
* every row has its head, at the head's width, and every head's count and sum are its rows'
  (`rowsHeaded`);
* every head's parent is a live cell (`rowsParented`).

`genesis_rowsOk`, `admit_rowsOk`, `refuse_rowsOk`, `fold_rowsOk`, `carry_rowsOk`: it holds at
genesis and every step keeps it. `head_sum` reads a head's counters back as its rows' count and sum;
`fold_head_sum` is it on every World a log reaches. `admit_rows_listing`: a turn adds at most one
rows entry per row touch.
-/
import Kernel.Proofs.Rows
import Kernel.Proofs.RowsRange
import Kernel.Proofs.Frame
import Kernel.Proofs.Carry
import Kernel.Proofs.RootedDeployed

namespace Nanodregg.Kernel

variable {D : Type} [Ord D] [DecidableEq D]

attribute [local irreducible] rowPath

/-- **The reached-World rows invariant** (KERNEL-48): every entry fits, every row is headed and
every head counts its rows, every head's parent is live. -/
def World.RowsOk (E : Env D) (w : World D) : Prop :=
  (∀ p ∈ w.rows.toList, rowFits p.1 p.2 = true) ∧ rowsHeaded w.rows.toList = true ∧
    rowsParented E w.trie w.rows = true

/-! ## Counting a relation's rows -/

/-- The parent a rows key is under. -/
private def parentOf : RowSlot D → D
  | .head p _ => p
  | .row key => key.parent

/-- 1 at a row of `(p, rel)`. -/
private def gc (p : D) (rel : Nat) : RowSlot D × RowLeaf → Nat
  | (.row key, .row _ _) => if key.parent = p ∧ key.rel = rel then 1 else 0
  | _ => 0

/-- Its `amt` at a row of `(p, rel)`. -/
private def gs (p : D) (rel : Nat) : RowSlot D × RowLeaf → Nat
  | (.row key, .row amt _) => if key.parent = p ∧ key.rel = rel then amt else 0
  | _ => 0

omit [Ord D] in
private theorem gc_head (p : D) (rel : Nat) (q : D) (r : Nat) (v : RowLeaf) : gc p rel (.head q r, v) = 0 := by
  cases v <;> rfl

omit [Ord D] in
private theorem gs_head (p : D) (rel : Nat) (q : D) (r : Nat) (v : RowLeaf) : gs p rel (.head q r, v) = 0 := by
  cases v <;> rfl

omit [Ord D] in
private theorem gc_row_ne {p : D} {rel : Nat} {key : RowKey D} (h : ¬(key.parent = p ∧ key.rel = rel)) (v : RowLeaf) :
    gc p rel (.row key, v) = 0 := by
  cases v <;> simp [gc, h]

omit [Ord D] in
private theorem gs_row_ne {p : D} {rel : Nat} {key : RowKey D} (h : ¬(key.parent = p ∧ key.rel = rel)) (v : RowLeaf) :
    gs p rel (.row key, v) = 0 := by
  cases v <;> simp [gs, h]

omit [Ord D] [DecidableEq D] in
private theorem sum_zero {α : Type} (g : α → Nat) : ∀ (l : List α), (∀ q ∈ l, g q = 0) → (l.map g).sum = 0
  | [], _ => rfl
  | q :: l, h => by
      simp only [List.map_cons, List.sum_cons, h q (by simp), sum_zero g l (fun q' hq => h q' (by simp [hq]))]

omit [Ord D] [DecidableEq D] in
private theorem len_eq {α : Type} : ∀ (l : List α), (l.map fun _ => 1).sum = l.length
  | [] => rfl
  | _ :: l => by simp only [List.map_cons, List.sum_cons, len_eq l, List.length_cons]; omega

omit [Ord D] [DecidableEq D] in
/-- What a relation's rows count is, from a filterMap that lists them (`rowsHeaded`'s `rowsOf`). -/
private theorem filterMap_rows [DecidableEq D] {p : D} {rel : Nat} {F : RowSlot D × RowLeaf → Option (RowKey D × Nat)}
    (h1 : ∀ key amt v, F (.row key, .row amt v) =
      if key.parent = p ∧ key.rel = rel then some (key, amt) else none)
    (h2 : ∀ q r v, F (.head q r, v) = none)
    (h3 : ∀ key c s l cap wd rt, F (.row key, .head c s l cap wd rt) = none) :
    ∀ l : List (RowSlot D × RowLeaf),
      (l.filterMap F).length = (l.map (gc p rel)).sum ∧ ((l.filterMap F).map (·.2)).sum = (l.map (gs p rel)).sum
  | [] => ⟨rfl, rfl⟩
  | q :: l => by
      obtain ⟨ih1, ih2⟩ := filterMap_rows h1 h2 h3 l
      obtain ⟨_ | key, ⟨c0, s0, l0, cap0, wd0, rt0⟩ | ⟨amt, v⟩⟩ := q
      · simp only [List.filterMap_cons, h2, List.map_cons, List.sum_cons, gc_head, gs_head, Nat.zero_add]
        exact ⟨ih1, ih2⟩
      · simp only [List.filterMap_cons, h2, List.map_cons, List.sum_cons, gc_head, gs_head, Nat.zero_add]
        exact ⟨ih1, ih2⟩
      · have e1 : gc p rel (.row key, .head c0 s0 l0 cap0 wd0 rt0) = 0 := rfl
        have e2 : gs p rel (.row key, .head c0 s0 l0 cap0 wd0 rt0) = 0 := rfl
        simp only [List.filterMap_cons, h3, List.map_cons, List.sum_cons, e1, e2, Nat.zero_add]
        exact ⟨ih1, ih2⟩
      · by_cases hk : key.parent = p ∧ key.rel = rel
        · have e : F (.row key, .row amt v) = some (key, amt) := by rw [h1]; simp [hk.1, hk.2]
          simp only [List.filterMap_cons, e, List.length_cons, List.map_cons, List.sum_cons]
          simp only [gc, gs, hk, and_self, if_true]
          exact ⟨by omega, by omega⟩
        · have e : F (.row key, .row amt v) = none := by rw [h1, if_neg hk]
          simp only [List.filterMap_cons, e, List.map_cons, List.sum_cons, gc_row_ne hk, gs_row_ne hk, Nat.zero_add]
          exact ⟨ih1, ih2⟩

omit [Ord D] [DecidableEq D] in
private theorem filterMap_rows_len [DecidableEq D] {p : D} {rel : Nat} {F : RowSlot D × RowLeaf → Option (RowKey D × Nat)}
    (h1 : ∀ key amt v, F (.row key, .row amt v) =
      if key.parent = p ∧ key.rel = rel then some (key, amt) else none)
    (h2 : ∀ q r v, F (.head q r, v) = none)
    (h3 : ∀ key c s l cap wd rt, F (.row key, .head c s l cap wd rt) = none) (l : List (RowSlot D × RowLeaf)) :
    (l.filterMap F).length = (l.map (gc p rel)).sum := (filterMap_rows h1 h2 h3 l).1

omit [Ord D] [DecidableEq D] in
private theorem filterMap_rows_sum [DecidableEq D] {p : D} {rel : Nat} {F : RowSlot D × RowLeaf → Option (RowKey D × Nat)}
    (h1 : ∀ key amt v, F (.row key, .row amt v) =
      if key.parent = p ∧ key.rel = rel then some (key, amt) else none)
    (h2 : ∀ q r v, F (.head q r, v) = none)
    (h3 : ∀ key c s l cap wd rt, F (.row key, .head c s l cap wd rt) = none) (l : List (RowSlot D × RowLeaf)) :
    ((l.filterMap F).map (·.2)).sum = (l.map (gs p rel)).sum := (filterMap_rows h1 h2 h3 l).2

omit [Ord D] in
/-- `rowsHeaded`, as a statement about membership and counts. -/
private theorem rowsHeaded_iff (l : List (RowSlot D × RowLeaf)) :
    rowsHeaded l = true ↔
      (∀ key v, (RowSlot.row key, v) ∈ l →
        ∃ c s lim cap rt, (RowSlot.head key.parent key.rel, RowLeaf.head c s lim cap key.k.size rt) ∈ l) ∧
      (∀ p rel c s lim cap wd rt, (RowSlot.head p rel, RowLeaf.head c s lim cap wd rt) ∈ l →
        (l.map (gc p rel)).sum = c ∧ (l.map (gs p rel)).sum = s) := by
  unfold rowsHeaded
  simp only [Bool.and_eq_true, List.all_eq_true]
  constructor
  · rintro ⟨hA, hB⟩
    refine ⟨fun key v hm => ?_, fun p rel c s lim cap wd rt hm => ?_⟩
    · have := hA _ hm
      simp only [List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq, List.mem_filterMap] at this
      obtain ⟨⟨hp, hr, c, s, wd⟩, ⟨⟨_ | _, _ | _⟩, hq, he⟩, ⟨e1, e2⟩, e3⟩ := this
      · simp only [Option.some.injEq, Prod.mk.injEq] at he
        obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := he
        simp only at e1 e2 e3
        subst e1 e2 e3
        exact ⟨_, _, _, _, _, hq⟩
      · simp at he
      · simp at he
      · simp at he
    · have := hB (p, rel, c, s, wd) (List.mem_filterMap.mpr ⟨_, hm, rfl⟩)
      simp only [decide_eq_true_eq] at this
      obtain ⟨hc, hs⟩ := this
      rw [filterMap_rows_len] at hc
      rw [filterMap_rows_sum] at hs
      · exact ⟨hc, hs⟩
      all_goals first | (intro _ _ v; cases v <;> rfl) | (intros; rfl)
  · rintro ⟨hA, hB⟩
    refine ⟨fun q hq => ?_, fun h hh => ?_⟩
    · obtain ⟨_ | key, v⟩ := q
      · rfl
      · obtain ⟨c, s, lim, cap, rt, hm⟩ := hA key v hq
        simp only [List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq, List.mem_filterMap]
        exact ⟨(key.parent, key.rel, c, s, key.k.size), ⟨_, hm, rfl⟩, ⟨rfl, rfl⟩, rfl⟩
    · obtain ⟨⟨_ | _, _ | _⟩, hq, he⟩ := List.mem_filterMap.mp hh
      · simp only [Option.some.injEq] at he
        subst he
        obtain ⟨hc, hs⟩ := hB _ _ _ _ _ _ _ _ hq
        simp only [decide_eq_true_eq]
        rw [filterMap_rows_len, filterMap_rows_sum]
        · exact ⟨hc, hs⟩
        all_goals first | (intro _ _ v; cases v <;> rfl) | (intros; rfl)
      · simp at he
      · simp at he
      · simp at he

/-! ## The invariant on one rows trie, read through `get` -/

/-- Every entry fits; every row's head exists at its width; every head counts its rows. -/
private def Inv (E : Env D) (r : Rows D) : Prop :=
  (∀ k v, r.get (rowSpec E) k = some v → rowFits k v = true) ∧
  (∀ key v, r.get (rowSpec E) (.row key) = some v →
    ∃ c s lim cap rt, r.get (rowSpec E) (.head key.parent key.rel) = some (.head c s lim cap key.k.size rt)) ∧
  (∀ p rel c s lim cap wd rt, r.get (rowSpec E) (.head p rel) = some (.head c s lim cap wd rt) →
    (r.toList.map (gc p rel)).sum = c ∧ (r.toList.map (gs p rel)).sum = s)

omit [Ord D] in
private theorem inv_iff {E : Env D} {r : Rows D} (hr : Trie.Routed (rowSpec E) 0 r) :
    Inv E r ↔ (∀ q ∈ r.toList, rowFits q.1 q.2 = true) ∧ rowsHeaded r.toList = true := by
  have hm : ∀ k v, (k, v) ∈ r.toList ↔ r.get (rowSpec E) k = some v := fun k v => Trie.mem_toList (rowSpec E) 0 r hr k v
  rw [rowsHeaded_iff]
  constructor
  · rintro ⟨hF, h1, h2⟩
    refine ⟨fun q hq => hF q.1 q.2 ((hm q.1 q.2).mp hq), fun key v hq => ?_, fun p rel c s lim cap wd rt hq => ?_⟩
    · obtain ⟨c, s, lim, cap, rt, hg⟩ := h1 key v ((hm _ _).mp hq)
      exact ⟨c, s, lim, cap, rt, (hm _ _).mpr hg⟩
    · exact h2 p rel c s lim cap wd rt ((hm _ _).mp hq)
  · rintro ⟨hF, h1, h2⟩
    refine ⟨fun k v hg => hF (k, v) ((hm k v).mpr hg), fun key v hg => ?_, fun p rel c s lim cap wd rt hg => ?_⟩
    · obtain ⟨c, s, lim, cap, rt, hq⟩ := h1 key v ((hm _ _).mpr hg)
      exact ⟨c, s, lim, cap, rt, (hm _ _).mp hq⟩
    · exact h2 p rel c s lim cap wd rt ((hm _ _).mpr hg)

/-! ## Sums and lengths over a rows trie -/

omit [Ord D] [DecidableEq D] in
private theorem sum_filter_not {K V : Type} (g : K × V → Nat) (Z : K → Bool)
    (hg : ∀ k v, Z k = true → g (k, v) = 0) :
    ∀ l : List (K × V), (l.map g).sum = ((l.filter fun q => !Z q.1).map g).sum
  | [] => rfl
  | ⟨k, v⟩ :: l => by
      have ih := sum_filter_not g Z hg l
      cases hz : Z k
      · simp [hz, ih]
      · simp [hz, ih, hg k v hz]

omit [Ord D] [DecidableEq D] in
/-- Two routed tries that agree off the keys `Z` names, summed by a `g` that vanishes on those keys. -/
private theorem sum_congr_get {K V : Type} [DecidableEq K] (S : Trie.Spec K V D) {r r' : Trie.T K V D}
    (hr : Trie.Routed S 0 r) (hr' : Trie.Routed S 0 r') (g : K × V → Nat) (Z : K → Bool)
    (hg : ∀ k v, Z k = true → g (k, v) = 0) (he : ∀ k, Z k = false → r.get S k = r'.get S k) :
    (r.toList.map g).sum = (r'.toList.map g).sum := by
  rw [sum_filter_not g Z hg r.toList, sum_filter_not g Z hg r'.toList]
  apply Trie.perm_sumN
  apply Trie.perm_of_nodup_mem (List.filter_sublist.nodup (Trie.nodup_of_map_fst (Trie.toList_nodup S 0 r hr)))
    (List.filter_sublist.nodup (Trie.nodup_of_map_fst (Trie.toList_nodup S 0 r' hr')))
  rintro ⟨k, v⟩
  simp only [List.mem_filter]
  constructor
  · rintro ⟨hm, hz⟩
    have hz' : Z k = false := by simpa using hz
    refine ⟨(Trie.mem_toList S 0 r' hr' k v).mpr ?_, hz⟩
    show Trie.T.get S r' k = some v
    rw [← he k hz']; exact (Trie.mem_toList S 0 r hr k v).mp hm
  · rintro ⟨hm, hz⟩
    have hz' : Z k = false := by simpa using hz
    refine ⟨(Trie.mem_toList S 0 r hr k v).mpr ?_, hz⟩
    show Trie.T.get S r k = some v
    rw [he k hz']; exact (Trie.mem_toList S 0 r' hr' k v).mp hm

omit [Ord D] in
/-- A retract's erase gives back exactly the erased entry, under any `g`. -/
private theorem sum_retain {E : Env D} {r : Rows D} (hr : Trie.Canon (rowSpec E) 0 r) {k : RowSlot D}
    {old : RowLeaf} (h : r.get (rowSpec E) k = some old) (g : RowSlot D × RowLeaf → Nat) :
    ((Trie.retainAt (rowSpec E) (fun k' _ => decide (k' ≠ k)) (rowPath E k) r).toList.map g).sum + g (k, old) =
      (r.toList.map g).sum := by
  have hq : ∀ p ∈ r.toList, decide (p.1 ≠ k) = false → Trie.Under (rowSpec E) 0 (rowPath E k) p.1 := by
    rintro ⟨pk, pv⟩ _ hf
    have : pk = k := Classical.not_not.mp (of_decide_eq_false hf)
    subst this
    exact under_rowPath E pk
  rw [Trie.toList_retainAt (rowSpec E) (fun k' _ => decide (k' ≠ k)) (rowPath E k) 0 r hr.1 hq,
    Trie.sumN_split g r.toList (Trie.toList_nodup (rowSpec E) 0 r hr.1)
      ((Trie.mem_toList (rowSpec E) 0 r hr.1 k old).mpr h)]
  omega

omit [Ord D] [DecidableEq D] in
private theorem nodup_map_inj {α β : Type} {f : α → β} (hf : ∀ a b, f a = f b → a = b) :
    ∀ {l : List α}, l.Nodup → (l.map f).Nodup
  | [], _ => List.nodup_nil
  | a :: l, h => by
      rw [List.nodup_cons] at h
      rw [List.map_cons, List.nodup_cons]
      refine ⟨fun hm => ?_, nodup_map_inj hf h.2⟩
      obtain ⟨b, hb, he⟩ := List.mem_map.mp hm
      exact h.1 (hf b a he ▸ hb)

omit [Ord D] [DecidableEq D] in
private theorem nodup_len_le {α : Type} [DecidableEq α] {l1 l2 : List α} (h1 : l1.Nodup) (h2 : l2.Nodup)
    (h : ∀ a ∈ l1, a ∈ l2) : l1.length ≤ l2.length := by
  have hp : l1.Perm (l2.filter fun a => decide (a ∈ l1)) :=
    Trie.perm_of_nodup_mem h1 (List.filter_sublist.nodup h2) (fun a => by
      simp only [List.mem_filter, decide_eq_true_eq]
      exact ⟨fun ha => ⟨h a ha, ha⟩, fun ha => ha.2⟩)
  rw [hp.length_eq]; exact List.length_filter_le _ _

omit [Ord D] in
private theorem len_insert_le {E : Env D} {r : Rows D} (hr : Trie.Routed (rowSpec E) 0 r) (k : RowSlot D)
    (v : RowLeaf) : (r.insert (rowSpec E) k v).toList.length ≤ r.toList.length + 1 := by
  rw [(Trie.toList_insert_perm (rowSpec E) hr k v).length_eq, List.length_append]
  have := List.length_filter_le (fun p : RowSlot D × RowLeaf => decide (p.1 ≠ k)) r.toList
  simp only [List.length_singleton]
  omega

omit [Ord D] in
private theorem len_insert_some {E : Env D} {r : Rows D} (hr : Trie.Routed (rowSpec E) 0 r) {k : RowSlot D}
    {old : RowLeaf} (h : r.get (rowSpec E) k = some old) (v : RowLeaf) :
    (r.insert (rowSpec E) k v).toList.length = r.toList.length := by
  have := Trie.sumN_insert_some (rowSpec E) (fun _ => 1) hr v h
  rw [len_eq, len_eq] at this
  dsimp only at this
  omega

omit [Ord D] in
private theorem len_retain_le {E : Env D} {r : Rows D} (hr : Trie.Canon (rowSpec E) 0 r) (k : RowSlot D) :
    (Trie.retainAt (rowSpec E) (fun k' _ => decide (k' ≠ k)) (rowPath E k) r).toList.length ≤ r.toList.length ∧
      Trie.Canon (rowSpec E) 0 (Trie.retainAt (rowSpec E) (fun k' _ => decide (k' ≠ k)) (rowPath E k) r) := by
  have hq : ∀ p ∈ r.toList, decide (p.1 ≠ k) = false → Trie.Under (rowSpec E) 0 (rowPath E k) p.1 := by
    rintro ⟨pk, pv⟩ _ hf
    have : pk = k := Classical.not_not.mp (of_decide_eq_false hf)
    subst this
    exact under_rowPath E pk
  refine ⟨?_, Trie.canon_retainAt (rowSpec E) _ _ 0 r hr hq⟩
  rw [Trie.toList_retainAt (rowSpec E) (fun k' _ => decide (k' ≠ k)) (rowPath E k) 0 r hr.1 hq]
  exact List.length_filter_le _ _

/-! ## One row touch keeps the invariant -/

/-- Every head's parent is live in the pre-state, or born by the turn. -/
private def Par (E : Env D) (w : World D) (t : Turn D) (r : Rows D) : Prop :=
  ∀ q rel v, r.get (rowSpec E) (.head q rel) = some v → (w.live E q).isSome = true ∨ q ∈ createdIds t

/-- No row is under a parent one of `xs` retires. -/
private def NoRetL (E : Env D) (xs : List (Touch D)) (r : Rows D) : Prop :=
  ∀ key v, r.get (rowSpec E) (.row key) = some v → ∀ x ∈ xs, x.cell = key.parent → x.act ≠ .retire

/-- A row write's head update (`setHead` over the rows `r1` the write left) keeps the invariant. -/
private theorem setHead_inv {E : Env D} {w : World D} {t : Turn D} {r r1 r' : Rows D} {key : RowKey D}
    {count sum limit cap width : Nat} {retract : Bool} {c' s' : Nat}
    (hr : Trie.Canon (rowSpec E) 0 r) (hr1 : Trie.Canon (rowSpec E) 0 r1)
    (hi : Inv E r) (hp : Par E w t r) (hn : NoRetL E t.touches r)
    (hg : r.get (rowSpec E) (.head key.parent key.rel) = some (.head count sum limit cap width retract))
    (hlive : (w.live E key.parent).isSome = true)
    (hret : ∀ x ∈ t.touches, x.cell = key.parent → x.act ≠ .retire)
    (h1 : ∀ k, k ≠ .row key → r1.get (rowSpec E) k = r.get (rowSpec E) k)
    (h2 : ∀ l, r1.get (rowSpec E) (.row key) = some l → rowFits (.row key) l = true ∧ key.k.size = width)
    (hc : (r1.toList.map (gc key.parent key.rel)).sum = c')
    (hs : (r1.toList.map (gs key.parent key.rel)).sum = s')
    (hcl : c' ≤ limit) (hsc : s' ≤ cap)
    (he : r' = setHead E r1 key.parent key.rel c' s' limit cap width retract) :
    Inv E r' ∧ Par E w t r' ∧ NoRetL E t.touches r' := by
  obtain ⟨hF, hH1, hH2⟩ := hi
  have hget : ∀ k, r'.get (rowSpec E) k =
      if k = .head key.parent key.rel then some (.head c' s' limit cap width retract) else r1.get (rowSpec E) k := by
    intro k; rw [he]; unfold setHead; exact Trie.get_insert (rowSpec E) r1 _ k _
  have hR' : Trie.Routed (rowSpec E) 0 r' := by
    rw [he]; unfold setHead; exact (Trie.canon_insert (rowSpec E) _ _ hr1).1
  clear he
  have hrh : ∀ (k : RowKey D) (q : D) (rl : Nat), (RowSlot.row k : RowSlot D) ≠ .head q rl := fun _ _ _ h => by cases h
  have hsum1 : ∀ g : RowSlot D × RowLeaf → Nat, (∀ v, g (.head key.parent key.rel, v) = 0) →
      (r'.toList.map g).sum = (r1.toList.map g).sum := fun g hg0 =>
    sum_congr_get (rowSpec E) hR' hr1.1 g (fun k => decide (k = .head key.parent key.rel))
      (fun k v hk => by rw [of_decide_eq_true hk]; exact hg0 v)
      (fun k hk => by rw [hget, if_neg (of_decide_eq_false hk)])
  have hsum0 : ∀ g : RowSlot D × RowLeaf → Nat, (∀ v, g (.row key, v) = 0) →
      (r1.toList.map g).sum = (r.toList.map g).sum := fun g hg0 =>
    sum_congr_get (rowSpec E) hr1.1 hr.1 g (fun k => decide (k = .row key))
      (fun k v hk => by rw [of_decide_eq_true hk]; exact hg0 v)
      (fun k hk => h1 k (of_decide_eq_false hk))
  refine ⟨⟨fun k v hkv => ?_, fun key' v hkv => ?_, fun p rel c s lim cap0 wd rt hkv => ?_⟩, fun q rel v hkv => ?_,
    fun key' v hkv x hx hxc => ?_⟩
  · -- every entry fits
    rw [hget] at hkv
    split at hkv
    · rename_i hk
      subst hk
      simp only [Option.some.injEq] at hkv
      subst hkv
      have := hF _ _ hg
      simp only [rowFits, Bool.and_eq_true, decide_eq_true_eq] at this ⊢
      omega
    · by_cases hk : k = .row key
      · subst hk; exact (h2 v hkv).1
      · rw [h1 k hk] at hkv; exact hF k v hkv
  · -- every row has its head, at its width
    rw [hget, if_neg (hrh _ _ _)] at hkv
    by_cases hk : key' = key
    · subst hk
      refine ⟨c', s', limit, cap, retract, ?_⟩
      rw [hget, if_pos rfl, (h2 v hkv).2]
    · have hne : (RowSlot.row key' : RowSlot D) ≠ .row key := fun h => hk (by injection h)
      rw [h1 _ hne] at hkv
      obtain ⟨c, s, lim, cap1, rt, hg'⟩ := hH1 key' v hkv
      by_cases hpr : (RowSlot.head key'.parent key'.rel : RowSlot D) = .head key.parent key.rel
      · rw [hpr, hg] at hg'
        simp only [Option.some.injEq, RowLeaf.head.injEq] at hg'
        refine ⟨c', s', limit, cap, retract, ?_⟩
        rw [hget, if_pos hpr, hg'.2.2.2.2.1]
      · exact ⟨c, s, lim, cap1, rt, by rw [hget, if_neg hpr, h1 _ (hrh _ _ _).symm, hg']⟩
  · -- every head counts its rows
    rw [hget] at hkv
    split at hkv
    · rename_i hk
      simp only [Option.some.injEq, RowLeaf.head.injEq] at hkv
      obtain ⟨rfl, rfl, -, -, -, -⟩ := hkv
      simp only [RowSlot.head.injEq] at hk
      obtain ⟨rfl, rfl⟩ := hk
      rw [hsum1 _ (gc_head _ _ _ _), hsum1 _ (gs_head _ _ _ _)]
      exact ⟨hc, hs⟩
    · rename_i hk
      rw [h1 _ (hrh _ _ _).symm] at hkv
      have hm : ¬(key.parent = p ∧ key.rel = rel) := fun ⟨e1, e2⟩ => hk (by rw [e1, e2])
      rw [hsum1 _ (gc_head _ _ _ _), hsum1 _ (gs_head _ _ _ _), hsum0 _ (gc_row_ne hm), hsum0 _ (gs_row_ne hm)]
      exact hH2 p rel c s lim cap0 wd rt hkv
  · -- every head's parent is live or born
    rw [hget] at hkv
    split at hkv
    · rename_i hk
      simp only [RowSlot.head.injEq] at hk
      rw [hk.1]; exact .inl hlive
    · rw [h1 _ (hrh _ _ _).symm] at hkv; exact hp q rel v hkv
  · -- no row under a retired parent
    rw [hget, if_neg (hrh _ _ _)] at hkv
    by_cases hk : key' = key
    · subst hk; exact hret x hx hxc
    · have hne : (RowSlot.row key' : RowSlot D) ≠ .row key := fun h => hk (by injection h)
      rw [h1 _ hne] at hkv; exact hn key' v hkv x hx hxc

/-- A `declare` keeps the invariant: its head is fresh, so no row is of it yet. -/
private theorem declare_inv {E : Env D} {w : World D} {t : Turn D} {r r' : Rows D} {p : D} {rel limit cap width : Nat}
    {retract : Bool} (hr : Trie.Canon (rowSpec E) 0 r) (hi : Inv E r) (hp : Par E w t r) (hn : NoRetL E t.touches r)
    (hnone : r.get (rowSpec E) (.head p rel) = none) (hrel : rel < 256) (hlim : limit ≤ Bounds.rowsPerRelationMax)
    (hwd : width ≤ Bounds.keyBytesMax) (hcap : cap < Bounds.counterLimit) (hlate : p ∈ createdIds t)
    (he : r' = setHead E r p rel 0 0 limit cap width retract) :
    Inv E r' ∧ Par E w t r' ∧ NoRetL E t.touches r' := by
  obtain ⟨hF, hH1, hH2⟩ := hi
  have hget : ∀ k, r'.get (rowSpec E) k =
      if k = .head p rel then some (.head 0 0 limit cap width retract) else r.get (rowSpec E) k := by
    intro k; rw [he]; unfold setHead; exact Trie.get_insert (rowSpec E) r _ k _
  have hR' : Trie.Routed (rowSpec E) 0 r' := by
    rw [he]; unfold setHead; exact (Trie.canon_insert (rowSpec E) _ _ hr).1
  clear he
  have hrh : ∀ (k : RowKey D) (q : D) (rl : Nat), (RowSlot.row k : RowSlot D) ≠ .head q rl := fun _ _ _ h => by cases h
  have hsum : ∀ g : RowSlot D × RowLeaf → Nat, (∀ v, g (.head p rel, v) = 0) →
      (r'.toList.map g).sum = (r.toList.map g).sum := fun g hg0 =>
    sum_congr_get (rowSpec E) hR' hr.1 g (fun k => decide (k = .head p rel))
      (fun k v hk => by rw [of_decide_eq_true hk]; exact hg0 v)
      (fun k hk => by rw [hget, if_neg (of_decide_eq_false hk)])
  refine ⟨⟨fun k v hkv => ?_, fun key' v hkv => ?_, fun q rl c s lim cap0 wd rt hkv => ?_⟩, fun q rl v hkv => ?_,
    fun key' v hkv x hx hxc => ?_⟩
  · rw [hget] at hkv
    split at hkv
    · rename_i hk
      subst hk
      simp only [Option.some.injEq] at hkv
      subst hkv
      simp only [rowFits, Bool.and_eq_true, decide_eq_true_eq]
      omega
    · exact hF k v hkv
  · rw [hget, if_neg (hrh _ _ _)] at hkv
    obtain ⟨c, s, lim, cap1, rt, hg'⟩ := hH1 key' v hkv
    have hne : (RowSlot.head key'.parent key'.rel : RowSlot D) ≠ .head p rel := fun h => by
      rw [h, hnone] at hg'; cases hg'
    exact ⟨c, s, lim, cap1, rt, by rw [hget, if_neg hne, hg']⟩
  · rw [hget] at hkv
    split at hkv
    · rename_i hk
      simp only [Option.some.injEq, RowLeaf.head.injEq] at hkv
      obtain ⟨rfl, rfl, -, -, -, -⟩ := hkv
      simp only [RowSlot.head.injEq] at hk
      obtain ⟨rfl, rfl⟩ := hk
      rw [hsum _ (gc_head _ _ _ _), hsum _ (gs_head _ _ _ _)]
      -- no row is of the fresh head: each would need it
      have hz : ∀ g : RowSlot D × RowLeaf → Nat, (∀ key v, ¬(key.parent = q ∧ key.rel = rl) → g (.row key, v) = 0) →
          (∀ q' r' v, g (.head q' r', v) = 0) → (r.toList.map g).sum = 0 := by
        intro g hg1 hg2
        apply sum_zero
        rintro ⟨_ | key, v⟩ hm
        · exact hg2 _ _ _
        · apply hg1
          rintro ⟨e1, e2⟩
          obtain ⟨c, s, lim, cap1, rt, hg'⟩ := hH1 key v (Trie.get_of_mem (rowSpec E) hr.1 hm)
          rw [e1, e2, hnone] at hg'
          cases hg'
      exact ⟨hz _ (fun _ v h => gc_row_ne h v) (gc_head _ _), hz _ (fun _ v h => gs_row_ne h v) (gs_head _ _)⟩
    · rename_i hk
      have hm : ∀ g : RowSlot D × RowLeaf → Nat, (∀ v, g (.head p rel, v) = 0) →
          (r'.toList.map g).sum = (r.toList.map g).sum := hsum
      rw [hm _ (gc_head _ _ _ _), hm _ (gs_head _ _ _ _)]
      exact hH2 q rl c s lim cap0 wd rt hkv
  · rw [hget] at hkv
    split at hkv
    · rename_i hk
      simp only [RowSlot.head.injEq] at hk
      rw [hk.1]; exact .inr hlate
    · exact hp q rl v hkv
  · rw [hget, if_neg (hrh _ _ _)] at hkv
    exact hn key' v hkv x hx hxc

/-- **One row touch keeps the invariant** (on the rows judged so far this turn). -/
private theorem rowStep_inv {E : Env D} {w : World D} {t : Turn D} {r r' : Rows D} {x : RowTouch D}
    (hr : Trie.Canon (rowSpec E) 0 r) (hi : Inv E r) (hp : Par E w t r) (hn : NoRetL E t.touches r)
    (hb : ∀ key, x.slot = .row key → key.rel < 256 ∧ key.k.size ≤ Bounds.keyBytesMax)
    (h : rowStep E w t r x = .ok r') :
    Inv E r' ∧ Par E w t r' ∧ NoRetL E t.touches r' := by
  obtain ⟨slot, seen, act⟩ := x
  cases slot with
  | head p rel =>
      cases act with
      | declare limit cap width retract =>
          unfold rowStep at h
          simp only [except_bind_ok] at h
          obtain ⟨⟨⟩, hrel, ⟨⟩, -, ⟨⟩, hlate, ⟨⟩, hbd, ⟨⟩, hn0, hw⟩ := h
          simp only [pure, Except.pure, Except.ok.injEq] at hw
          have hn0 : r.get (rowSpec E) (.head p rel) = none := by
            have := req_ok.mp hn0; unfold rowAt at this; simpa [Option.isNone_iff_eq_none] using this
          have hrel : rel < 256 := of_decide_eq_true (req_ok.mp hrel)
          have hbd := req_ok.mp hbd
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hbd
          have hlate : p ∈ createdIds t := by simpa using req_ok.mp hlate
          exact declare_inv hr hi hp hn hn0 hrel hbd.1.1 hbd.1.2 hbd.2 hlate hw.symm
      | keep => simp [rowStep] at h
      | insert _ _ => simp [rowStep] at h
      | upsert _ _ => simp [rowStep] at h
      | retract => simp [rowStep] at h
  | row key =>
      have hbk := hb key rfl
      unfold rowStep at h
      simp only [except_bind_ok] at h
      obtain ⟨⟨⟩, -, ⟨⟩, hlive, ⟨⟩, hret, h⟩ := h
      have hlive : (w.live E key.parent).isSome = true := req_ok.mp hlive
      have hret : ∀ x ∈ t.touches, x.cell = key.parent → x.act ≠ .retire := by
        have h0 := req_ok.mp hret
        simp only [Bool.not_eq_eq_eq_not, Bool.not_true, List.any_eq_false, Bool.and_eq_true,
          decide_eq_true_eq, not_and] at h0
        exact h0
      split at h
      · simp at h
      · rename_i count sum limit cap width retract hhead
        have hg := headOf_some hhead
        simp only [except_bind_ok] at h
        obtain ⟨⟨⟩, hwd, h⟩ := h
        have hwd : key.k.size = width := of_decide_eq_true (req_ok.mp hwd)
        have hfh := hi.1 _ _ hg
        simp only [rowFits, Bool.and_eq_true, decide_eq_true_eq] at hfh
        obtain ⟨hcnt, hsm⟩ := hi.2.2 _ _ _ _ _ _ _ _ hg
        have hins : ∀ (amt : Nat) (v : ByteArray), ∀ k, k ≠ .row key →
            (r.insert (rowSpec E) (.row key) (.row amt v)).get (rowSpec E) k = r.get (rowSpec E) k :=
          fun amt v k hk => Trie.get_insert_ne (rowSpec E) _ _ hk
        have hfit : ∀ (amt : Nat) (v : ByteArray), amt < Bounds.counterLimit → v.size ≤ Bounds.valueBytesMax →
            ∀ l, (r.insert (rowSpec E) (.row key) (.row amt v)).get (rowSpec E) (.row key) = some l →
              rowFits (.row key) l = true ∧ key.k.size = width := by
          intro amt v ha hv l hl
          rw [Trie.get_insert_self] at hl
          simp only [Option.some.injEq] at hl
          subst hl
          refine ⟨?_, hwd⟩
          simp only [rowFits, Bool.and_eq_true, decide_eq_true_eq]
          exact ⟨⟨⟨hbk.1, hbk.2⟩, ha⟩, hv⟩
        have e1 : ∀ amt v, gc key.parent key.rel (.row key, .row amt v) = 1 := fun _ _ => by simp [gc]
        have e2 : ∀ amt v, gs key.parent key.rel (.row key, .row amt v) = amt := fun _ _ => by simp [gs]
        cases act with
        | keep =>
            simp only [except_bind_ok] at h
            obtain ⟨⟨⟩, -, h⟩ := h
            simp only [pure, Except.pure, Except.ok.injEq] at h
            subst h
            exact ⟨hi, hp, hn⟩
        | insert amt v =>
            simp only [except_bind_ok] at h
            obtain ⟨⟨⟩, -, ⟨⟩, hnone, ⟨⟩, hlt, ⟨⟩, hcap, ⟨⟩, hv, h⟩ := h
            simp only [pure, Except.pure, Except.ok.injEq] at h
            have hnone : r.get (rowSpec E) (.row key) = none := by
              have := req_ok.mp hnone; unfold rowAt at this; simpa [Option.isNone_iff_eq_none] using this
            have hlt : count < limit := of_decide_eq_true (req_ok.mp hlt)
            have hcap : sum + amt ≤ cap := of_decide_eq_true (req_ok.mp hcap)
            have hv : v.size ≤ Bounds.valueBytesMax := of_decide_eq_true (req_ok.mp hv)
            refine setHead_inv hr (Trie.canon_insert (rowSpec E) (.row key) (.row amt v) hr) hi hp hn hg hlive hret
              (hins amt v) (hfit amt v (by omega) hv) ?_ ?_ (by omega) hcap h.symm
            · rw [Trie.sumN_insert_none (rowSpec E) (gc key.parent key.rel) hr.1 (.row amt v) hnone, hcnt, e1]
            · rw [Trie.sumN_insert_none (rowSpec E) (gs key.parent key.rel) hr.1 (.row amt v) hnone, hsm, e2]
        | upsert amt v =>
            simp only [except_bind_ok] at h
            obtain ⟨⟨⟩, -, ⟨⟩, hv, ⟨⟩, hfull, ⟨⟩, hcap, h⟩ := h
            simp only [pure, Except.pure, Except.ok.injEq] at h
            have hv : v.size ≤ Bounds.valueBytesMax := of_decide_eq_true (req_ok.mp hv)
            have hfull := req_ok.mp hfull
            have hcap := of_decide_eq_true (req_ok.mp hcap)
            unfold rowAt at hfull hcap h
            cases hc : r.get (rowSpec E) (.row key) with
            | none =>
                simp only [hc, Option.isNone_none, Bool.not_true, Bool.false_or, decide_eq_true_eq,
                  if_true, Nat.sub_zero] at hfull hcap h
                refine setHead_inv hr (Trie.canon_insert (rowSpec E) (.row key) (.row amt v) hr) hi hp hn hg hlive hret
                  (hins amt v) (hfit amt v (by omega) hv) ?_ ?_ (by omega) hcap h.symm
                · rw [Trie.sumN_insert_none (rowSpec E) (gc key.parent key.rel) hr.1 (.row amt v) hc, hcnt, e1]
                · rw [Trie.sumN_insert_none (rowSpec E) (gs key.parent key.rel) hr.1 (.row amt v) hc, hsm, e2]
            | some old =>
                cases old with
                | head c0 s0 l0 cap0 wd0 rt0 =>
                    have := hi.1 _ _ hc
                    simp [rowFits] at this
                | row a val =>
                    simp only [hc, Option.isNone_some, Bool.not_false, Bool.true_or, Bool.false_eq_true, ↓reduceIte] at hfull hcap h
                    have hsplit := Trie.sumN_split (gs key.parent key.rel) r.toList
                      (Trie.toList_nodup (rowSpec E) 0 r hr.1) ((Trie.mem_toList (rowSpec E) 0 r hr.1 _ _).mpr hc)
                    rw [hsm, e2] at hsplit
                    have hc1 := Trie.sumN_insert_some (rowSpec E) (gc key.parent key.rel) hr.1 (.row amt v) hc
                    have hs1 := Trie.sumN_insert_some (rowSpec E) (gs key.parent key.rel) hr.1 (.row amt v) hc
                    rw [hcnt, e1, e1] at hc1
                    rw [hsm, e2, e2] at hs1
                    refine setHead_inv hr (Trie.canon_insert (rowSpec E) (.row key) (.row amt v) hr) hi hp hn hg hlive
                      hret (hins amt v) (hfit amt v (by omega) hv) (by omega) (by omega) (by omega) hcap h.symm
        | retract =>
            simp only [except_bind_ok] at h
            obtain ⟨⟨⟩, -, ⟨⟩, -, h⟩ := h
            split at h
            · rename_i a val hc
              simp only [pure, Except.pure, Except.ok.injEq] at h
              have hc' : r.get (rowSpec E) (.row key) = some (.row a val) := hc
              obtain ⟨-, hcan1, hget1⟩ := rowsWeight_retain hr hc' (rowPath E (.row key)) (under_rowPath E (.row key))
              have sc := sum_retain hr hc' (gc key.parent key.rel)
              have ss := sum_retain hr hc' (gs key.parent key.rel)
              rw [e1, hcnt] at sc
              rw [e2, hsm] at ss
              refine setHead_inv hr hcan1 hi hp hn hg hlive hret (fun k hk => by rw [hget1, if_neg hk]) ?_
                (by omega) (by omega) (by omega) (by omega) h.symm
              intro l hl
              rw [hget1, if_pos rfl] at hl
              cases hl
            · simp at h
        | declare _ _ _ _ => simp at h

/-- **Every row touch of a turn keeps the invariant.** -/
private theorem foldRows_inv {E : Env D} {w : World D} {t : Turn D} :
    ∀ (l : List (RowTouch D)) (acc rr : Rows D × Nat), Trie.Canon (rowSpec E) 0 acc.1 → Inv E acc.1 →
      Par E w t acc.1 → NoRetL E t.touches acc.1 →
      (∀ x ∈ l, ∀ key, x.slot = .row key → key.rel < 256 ∧ key.k.size ≤ Bounds.keyBytesMax) →
      l.foldlM (rowStepFreed E w t) acc = .ok rr →
      Trie.Canon (rowSpec E) 0 rr.1 ∧ Inv E rr.1 ∧ Par E w t rr.1 ∧ NoRetL E t.touches rr.1
  | [], acc, rr, hc, hi, hp, hn, _, h => by
      simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h
      subst h; exact ⟨hc, hi, hp, hn⟩
  | x :: rest, acc, rr, hc, hi, hp, hn, hb, h => by
      rw [List.foldlM_cons, except_bind_ok] at h
      obtain ⟨acc', h1, h2⟩ := h
      unfold rowStepFreed at h1
      rw [except_bind_ok] at h1
      obtain ⟨r1, hs, he⟩ := h1
      simp only [pure, Except.pure, Except.ok.injEq] at he
      subst he
      obtain ⟨hi1, hp1, hn1⟩ := rowStep_inv hc hi hp hn (hb x (by simp)) hs
      exact foldRows_inv rest _ rr (rowStep_weight hc hs).2 hi1 hp1 hn1 (fun y hy => hb y (by simp [hy])) h2

/-! ## One row touch adds at most one entry -/

omit [Ord D] in
private theorem setHead_len {E : Env D} {r : Rows D} (hr : Trie.Routed (rowSpec E) 0 r) {p : D} {rel : Nat}
    {old : RowLeaf} (h : r.get (rowSpec E) (.head p rel) = some old) (c s l cap wd : Nat) (rt : Bool) :
    (setHead E r p rel c s l cap wd rt).toList.length =
      r.toList.length := by
  unfold setHead; exact len_insert_some hr h _

private theorem rowStep_len {E : Env D} {w : World D} {t : Turn D} {r r' : Rows D} {x : RowTouch D}
    (hr : Trie.Canon (rowSpec E) 0 r) (h : rowStep E w t r x = .ok r') :
    r'.toList.length ≤ r.toList.length + 1 := by
  obtain ⟨slot, seen, act⟩ := x
  cases slot with
  | head p rel =>
      cases act with
      | declare limit cap width retract =>
          unfold rowStep at h
          simp only [except_bind_ok] at h
          obtain ⟨⟨⟩, -, ⟨⟩, -, ⟨⟩, -, ⟨⟩, -, ⟨⟩, -, hw⟩ := h
          simp only [pure, Except.pure, Except.ok.injEq] at hw
          subst hw
          unfold setHead
          exact len_insert_le hr.1 _ _
      | keep => simp [rowStep] at h
      | insert _ _ => simp [rowStep] at h
      | upsert _ _ => simp [rowStep] at h
      | retract => simp [rowStep] at h
  | row key =>
      unfold rowStep at h
      simp only [except_bind_ok] at h
      obtain ⟨⟨⟩, -, ⟨⟩, -, ⟨⟩, -, h⟩ := h
      split at h
      · simp at h
      · rename_i count sum limit cap width retract hhead
        have hg := headOf_some hhead
        simp only [except_bind_ok] at h
        obtain ⟨⟨⟩, -, h⟩ := h
        have hins : ∀ (amt : Nat) (v : ByteArray),
            (r.insert (rowSpec E) (.row key) (.row amt v)).get (rowSpec E) (.head key.parent key.rel) =
              some (.head count sum limit cap width retract) :=
          fun amt v => by rw [Trie.get_insert_ne (rowSpec E) _ _ head_ne_row]; exact hg
        cases act with
        | keep =>
            simp only [except_bind_ok] at h
            obtain ⟨⟨⟩, -, h⟩ := h
            simp only [pure, Except.pure, Except.ok.injEq] at h
            subst h; omega
        | insert amt v =>
            simp only [except_bind_ok] at h
            obtain ⟨⟨⟩, -, ⟨⟩, -, ⟨⟩, -, ⟨⟩, -, ⟨⟩, -, h⟩ := h
            simp only [pure, Except.pure, Except.ok.injEq] at h
            subst h
            rw [setHead_len (Trie.canon_insert (rowSpec E) (.row key) (.row amt v) hr).1 (hins amt v)]
            exact len_insert_le hr.1 _ _
        | upsert amt v =>
            simp only [except_bind_ok] at h
            obtain ⟨⟨⟩, -, ⟨⟩, -, ⟨⟩, -, ⟨⟩, -, h⟩ := h
            simp only [pure, Except.pure, Except.ok.injEq] at h
            subst h
            rw [setHead_len (Trie.canon_insert (rowSpec E) (.row key) (.row amt v) hr).1 (hins amt v)]
            exact len_insert_le hr.1 _ _
        | retract =>
            simp only [except_bind_ok] at h
            obtain ⟨⟨⟩, -, ⟨⟩, -, h⟩ := h
            split at h
            · rename_i a val hc
              simp only [pure, Except.pure, Except.ok.injEq] at h
              subst h
              have hc' : r.get (rowSpec E) (.row key) = some (.row a val) := hc
              obtain ⟨-, hcan1, hget1⟩ := rowsWeight_retain hr hc' (rowPath E (.row key)) (under_rowPath E (.row key))
              have hg1 := hget1 (.head key.parent key.rel)
              rw [if_neg head_ne_row, hg] at hg1
              rw [setHead_len hcan1.1 hg1]
              have := (len_retain_le hr (.row key)).1
              omega
            · simp at h
        | declare _ _ _ _ => simp at h

private theorem foldRows_len {E : Env D} {w : World D} {t : Turn D} :
    ∀ (l : List (RowTouch D)) (acc rr : Rows D × Nat), Trie.Canon (rowSpec E) 0 acc.1 →
      l.foldlM (rowStepFreed E w t) acc = .ok rr →
      Trie.Canon (rowSpec E) 0 rr.1 ∧ rr.1.toList.length ≤ acc.1.toList.length + l.length
  | [], acc, rr, hc, h => by
      simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h
      subst h; exact ⟨hc, by simp⟩
  | x :: rest, acc, rr, hc, h => by
      rw [List.foldlM_cons, except_bind_ok] at h
      obtain ⟨acc', h1, h2⟩ := h
      unfold rowStepFreed at h1
      rw [except_bind_ok] at h1
      obtain ⟨r1, hs, he⟩ := h1
      simp only [pure, Except.pure, Except.ok.injEq] at he
      subst he
      have hl := rowStep_len hc hs
      obtain ⟨hc2, hl2⟩ := foldRows_len rest _ rr (rowStep_weight hc hs).2 h2
      refine ⟨hc2, ?_⟩
      simp only [List.length_cons] at hl2 ⊢
      omega

omit [Ord D] in
private theorem dropList_len {E : Env D} :
    ∀ (L : List (RowSlot D × RowLeaf)) (acc : Rows D × Nat), Trie.Canon (rowSpec E) 0 acc.1 →
      Trie.Canon (rowSpec E) 0 (L.foldl (fun acc p =>
          (Trie.retainAt (rowSpec E) (fun k _ => decide (k ≠ p.1)) (rowPath E p.1) acc.1, acc.2 + rowEntryWeight p)) acc).1 ∧
      (L.foldl (fun acc p =>
          (Trie.retainAt (rowSpec E) (fun k _ => decide (k ≠ p.1)) (rowPath E p.1) acc.1, acc.2 + rowEntryWeight p)) acc).1.toList.length ≤
        acc.1.toList.length
  | [], acc, hc => ⟨hc, Nat.le_refl _⟩
  | p :: L, acc, hc => by
      simp only [List.foldl_cons]
      obtain ⟨hl, hcan⟩ := len_retain_le hc p.1
      obtain ⟨h1, h2⟩ := dropList_len L (Trie.retainAt (rowSpec E) (fun k _ => decide (k ≠ p.1)) (rowPath E p.1) acc.1,
        acc.2 + rowEntryWeight p) hcan
      exact ⟨h1, Nat.le_trans h2 hl⟩

omit [Ord D] in
private theorem dropHeads_len {E : Env D} (t : Turn D) :
    ∀ (acc : Rows D × Nat), Trie.Canon (rowSpec E) 0 acc.1 →
      (dropHeads E t acc).1.toList.length ≤ acc.1.toList.length := by
  unfold dropHeads
  generalize t.touches = xs
  induction xs with
  | nil => intro acc _; exact Nat.le_refl _
  | cons x xs ih =>
      intro acc hc
      simp only [List.foldl_cons]
      split
      · have h1 := dropList_len (E := E) ((under (rowSpec E) (E.bytes x.cell) 257 acc.1).filter fun p =>
          match p.1 with
          | .head q _ => decide (q = x.cell)
          | .row _ => false) acc hc
        exact Nat.le_trans (ih _ h1.1) h1.2
      · exact ih acc hc

/-- **A turn adds at most one rows entry per row touch** (HOST-12's export bound): the rows' listing
grows by at most the turn's row touches. -/
theorem admit_rows_listing {E : Env D} {w w' : World D} {t : Turn D} (hr : w.RowsCanon E)
    (h : World.admit E w t = .ok w') : w'.rows.toList.length ≤ w.rows.toList.length + t.rows.length := by
  obtain ⟨_, hk, he⟩ := admit_rows h
  rw [he]
  have hrun := hk.rows
  unfold rowsRun at hrun
  simp only [except_bind_ok] at hrun
  obtain ⟨⟨⟩, -, ⟨⟩, -, hrun⟩ := hrun
  split at hrun
  · simp at hrun
  · rw [except_bind_ok] at hrun
    obtain ⟨acc, hf, hd⟩ := hrun
    simp only [pure, Except.pure, Except.ok.injEq] at hd
    rw [← hd]
    obtain ⟨hc1, hl1⟩ := foldRows_len t.rows (w.rows, 0) acc hr hf
    exact Nat.le_trans (dropHeads_len t acc hc1) hl1

/-! ## `dropHeads` removes exactly the retired parents' heads -/

/-- A parent's listing (`under` at its id's bytes) is exactly the entries under it: with every digest
`n` bytes and injective, a key starts with the parent's bytes iff the parent is its own. -/
private theorem startsWith_key {E : Env D} {n : Nat} (hE : E.Lawful n) (p : D) (s : RowSlot D) :
    startsWith (E.bytes p) (rowKeyBytes E s) = decide (parentOf s = p) := by
  have hx : ∀ (q : D) (b : ByteArray), startsWith (E.bytes p) (E.bytes q ++ b) = decide (q = p) := by
    intro q b
    unfold startsWith
    rw [ByteArray.extract_append_eq_left (by rw [hE.size, hE.size])]
    by_cases hq : q = p
    · subst hq; simp
    · rw [decide_eq_false hq]
      exact decide_eq_false fun he => hq (hE.bytes_inj he)
  cases s with
  | head q rel =>
      simp only [rowKeyBytes, parentOf, ByteArray.append_assoc]
      exact hx q _
  | row key =>
      simp only [rowKeyBytes, rowsPrefix, parentOf, ByteArray.append_assoc]
      exact hx key.parent _

private theorem under_parent {E : Env D} {n : Nat} (hE : E.Lawful n) {r : Rows D}
    (hc : Trie.Canon (rowSpec E) 0 r) (p : D) (m : Nat) :
    under (rowSpec E) (E.bytes p) m r = (r.toList.filter fun q => decide (parentOf q.1 = p)).take m := by
  have hlong : ∀ q : RowSlot D × RowLeaf, (E.bytes p).size ≤ ((rowSpec E).kbytes q.1).size := by
    rintro ⟨s, _⟩
    show (E.bytes p).size ≤ (rowKeyBytes E s).size
    cases s <;> simp [rowKeyBytes, rowsPrefix, ByteArray.size_append, hE.size] <;> omega
  rw [under_eq (rowSpec E) (fun _ _ => rfl) (E.bytes p) m 0 r hc.1 hc.2.2
    (fun _ _ _ _ _ hi => absurd hi (Nat.not_lt_zero _)) (fun q _ _ => hlong q)]
  congr 1
  exact List.filter_congr fun q _ => startsWith_key hE p q.1

/-- `checkRowsRemain` passed: no row of the pre-state is under a parent the turn retires. -/
private theorem noRet_pre {E : Env D} {n : Nat} (hE : E.Lawful n) {w : World D} {t : Turn D}
    (hr : w.RowsCanon E) (h : checkRowsRemain E w t = .ok ()) : NoRetL E t.touches w.rows := by
  intro key v hg x hx hc ha
  have h1 := (forEx_ok.mp h) x hx
  simp only [ha] at h1
  have h2 := req_ok.mp h1
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h2
  obtain ⟨hlen, hall⟩ := h2
  rw [under_parent hE hr x.cell 257] at hlen hall
  have hmem : (RowSlot.row key, v) ∈ w.rows.toList.filter (fun q => decide (parentOf q.1 = x.cell)) :=
    List.mem_filter.mpr ⟨(Trie.mem_toList (rowSpec E) 0 _ hr.1 _ _).mpr hg, by simp [parentOf, hc]⟩
  rw [List.length_take] at hlen
  rw [List.take_of_length_le (by omega)] at hall
  have := hall _ hmem
  simp at this

/-- The pre-state's heads have live parents (`rowsParented`). -/
private theorem par_pre {E : Env D} {w : World D} {t : Turn D} (hr : w.RowsCanon E)
    (hp : rowsParented E w.trie w.rows = true) : Par E w t w.rows := by
  intro q rel v hg
  left
  unfold rowsParented at hp
  have := (List.all_eq_true.mp hp) _ ((Trie.mem_toList (rowSpec E) 0 _ hr.1 _ _).mpr hg)
  simp only at this
  split at this
  · rename_i c hc
    rw [get_live hc]; rfl
  · cases this

/-- The heads a list of touches retires. -/
private def retiredIn (xs : List (Touch D)) : RowSlot D → Bool
  | .head q _ => xs.any fun x => decide (x.act = .retire) && decide (x.cell = q)
  | .row _ => false

/-- A key is a head of `c`. -/
private def headIs (c : D) : RowSlot D → Bool
  | .head q _ => decide (q = c)
  | .row _ => false

/-- **`dropHeads` removes exactly the heads of the parents the turn retires**: a key reads as absent
if it is one, as before otherwise. -/
private theorem dropHeads_char {E : Env D} {n : Nat} (hE : E.Lawful n) (t : Turn D) (acc : Rows D × Nat)
    (hc : Trie.Canon (rowSpec E) 0 acc.1) (hf : ∀ k v, acc.1.get (rowSpec E) k = some v → rowFits k v = true)
    (hn : NoRetL E t.touches acc.1) (k : RowSlot D) :
    (dropHeads E t acc).1.get (rowSpec E) k =
      if retiredIn t.touches k then none else acc.1.get (rowSpec E) k := by
  unfold dropHeads
  generalize t.touches = xs at hn ⊢
  induction xs generalizing acc with
  | nil => cases k <;> simp [retiredIn]
  | cons x xs ih =>
      simp only [List.foldl_cons]
      have hn' : ∀ (r : Rows D), (∀ key v, r.get (rowSpec E) (.row key) = some v →
          acc.1.get (rowSpec E) (.row key) = some v) → NoRetL E xs r :=
        fun r hsub key v h y hy => hn key v (hsub key v h) y (List.mem_cons_of_mem _ hy)
      cases hx : x.act with
      | retire =>
          dsimp only
          have hnx : ∀ key v, acc.1.get (rowSpec E) (.row key) = some v → key.parent ≠ x.cell :=
            fun key v hg he => hn key v hg x (by simp) he.symm hx
          have hP : ∀ q ∈ acc.1.toList, parentOf q.1 = x.cell → ∃ rel, q.1 = .head x.cell rel ∧ rel < 256 := by
            rintro ⟨s, v⟩ hq hpq
            have hg := Trie.get_of_mem (rowSpec E) hc.1 hq
            cases s with
            | row key => exact absurd hpq (hnx key v hg)
            | head q rel =>
                simp only [parentOf] at hpq
                subst hpq
                refine ⟨rel, rfl, ?_⟩
                have := hf _ _ hg
                cases v with
                | head c0 s0 l0 cap0 wd0 rt0 =>
                    simp only [rowFits, Bool.and_eq_true, decide_eq_true_eq] at this
                    omega
                | row a0 v0 => simp [rowFits] at this
          have hlen : (acc.1.toList.filter fun q => decide (parentOf q.1 = x.cell)).length ≤ 256 := by
            have h1 := nodup_len_le (l1 := (acc.1.toList.filter fun q => decide (parentOf q.1 = x.cell)).map Prod.fst)
              (l2 := (List.range 256).map (RowSlot.head x.cell))
              ((List.filter_sublist.map Prod.fst).nodup (Trie.toList_nodup (rowSpec E) 0 _ hc.1))
              (nodup_map_inj (fun a b h => by injection h) List.nodup_range)
              (by
                intro a ha
                obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ha
                obtain ⟨hq1, hq2⟩ := List.mem_filter.mp hq
                obtain ⟨rel, he, hrel⟩ := hP q hq1 (of_decide_eq_true hq2)
                rw [he]; exact List.mem_map.mpr ⟨rel, List.mem_range.mpr hrel, rfl⟩)
            simpa using h1
          have hlist : under (rowSpec E) (E.bytes x.cell) 257 acc.1 =
              acc.1.toList.filter fun q => decide (parentOf q.1 = x.cell) := by
            rw [under_parent hE hc, List.take_of_length_le (by omega)]
          rw [hlist]
          have hsubL : ∀ q ∈ ((acc.1.toList.filter fun q => decide (parentOf q.1 = x.cell)).filter
              fun p => headIs x.cell p.1), q ∈ acc.1.toList :=
            fun q hq => (List.mem_filter.mp (List.mem_filter.mp hq).1).1
          have hnodL : ((((acc.1.toList.filter fun q => decide (parentOf q.1 = x.cell)).filter
              fun p => headIs x.cell p.1)).map Prod.fst).Nodup :=
            ((List.filter_sublist.trans List.filter_sublist).map Prod.fst).nodup
              (Trie.toList_nodup (rowSpec E) 0 _ hc.1)
          have hgetL := dropList_get _ acc hc hnodL hsubL
          have hcanL := (dropList_weight _ acc hc hnodL hsubL).2
          have hfL : ∀ k v, (List.foldl (fun acc p =>
              (Trie.retainAt (rowSpec E) (fun k _ => decide (k ≠ p.1)) (rowPath E p.1) acc.1, acc.2 + rowEntryWeight p)) acc
              ((acc.1.toList.filter fun q => decide (parentOf q.1 = x.cell)).filter
                fun p => headIs x.cell p.1)).1.get (rowSpec E) k = some v → rowFits k v = true := by
            intro k v h; rw [hgetL k] at h; split at h
            · cases h
            · exact hf k v h
          have hnL := hn' _ (fun key v h => by
            rw [hgetL] at h; split at h
            · cases h
            · exact h)
          refine (ih _ hcanL hfL hnL).trans ?_
          rw [hgetL k]
          cases k with
          | row key =>
              have hm : (RowSlot.row key) ∉ (((acc.1.toList.filter fun q => decide (parentOf q.1 = x.cell)).filter
                  fun p => headIs x.cell p.1)).map Prod.fst := by
                intro hm; obtain ⟨q, hq, hq1⟩ := List.mem_map.mp hm
                have := (List.mem_filter.mp hq).2; rw [hq1] at this; simp [headIs] at this
              rw [if_neg hm]
              simp [retiredIn]
          | head q rel =>
              by_cases hq : q = x.cell
              · subst hq
                have hr : retiredIn (x :: xs) (.head x.cell rel) = true := by simp [retiredIn, hx]
                rw [hr, if_pos rfl]
                split
                · rfl
                · cases hg : acc.1.get (rowSpec E) (.head x.cell rel) with
                  | none => split <;> rfl
                  | some v =>
                      split
                      · rfl
                      · rename_i hnm
                        exact (hnm (List.mem_map.mpr ⟨(.head x.cell rel, v), List.mem_filter.mpr
                          ⟨List.mem_filter.mpr ⟨(Trie.mem_toList (rowSpec E) 0 acc.1 hc.1 (.head x.cell rel) v).mpr hg,
                            by simp [parentOf]⟩, by simp [headIs]⟩, rfl⟩)).elim
              · have hm : (RowSlot.head q rel) ∉ (((acc.1.toList.filter fun q => decide (parentOf q.1 = x.cell)).filter
                    fun p => headIs x.cell p.1)).map Prod.fst := by
                  intro hm; obtain ⟨p', hp', hp1⟩ := List.mem_map.mp hm
                  have := (List.mem_filter.mp hp').2; rw [hp1] at this; simp [headIs, hq] at this
                have hr : retiredIn (x :: xs) (.head q rel) = retiredIn xs (.head q rel) := by
                  simp [retiredIn, Ne.symm hq]
                rw [hr, if_neg hm]
      | keep =>
          dsimp only
          refine (ih acc hc hf (hn' acc.1 fun _ _ h => h)).trans ?_
          cases k <;> simp [retiredIn, hx]
      | write ops =>
          dsimp only
          refine (ih acc hc hf (hn' acc.1 fun _ _ h => h)).trans ?_
          cases k <;> simp [retiredIn, hx]

omit [Ord D] in
/-- What `dropHeads` leaves keeps the invariant: only heads leave, and none of them has a row. -/
private theorem inv_after {E : Env D} {t : Turn D} {r res : Rows D} (hr : Trie.Routed (rowSpec E) 0 r)
    (hres : Trie.Routed (rowSpec E) 0 res) (hi : Inv E r) (hn : NoRetL E t.touches r)
    (hchar : ∀ k, res.get (rowSpec E) k = if retiredIn t.touches k then none else r.get (rowSpec E) k) :
    Inv E res := by
  obtain ⟨hF, hH1, hH2⟩ := hi
  have hsum : ∀ g : RowSlot D × RowLeaf → Nat, (∀ q rl v, g (.head q rl, v) = 0) →
      (res.toList.map g).sum = (r.toList.map g).sum := fun g hg0 =>
    sum_congr_get (rowSpec E) hres hr g (retiredIn t.touches)
      (fun k v hk => by cases k with
        | head q rl => exact hg0 q rl v
        | row key => simp [retiredIn] at hk)
      (fun k hk => by rw [hchar, if_neg (by simp [hk])])
  refine ⟨fun k v hkv => ?_, fun key v hkv => ?_, fun p rel c s lim cap wd rt hkv => ?_⟩
  · rw [hchar] at hkv; split at hkv
    · cases hkv
    · exact hF k v hkv
  · rw [hchar, if_neg (by simp [retiredIn])] at hkv
    obtain ⟨c, s, lim, cap, rt, hg⟩ := hH1 key v hkv
    refine ⟨c, s, lim, cap, rt, ?_⟩
    rw [hchar, if_neg, hg]
    intro hret
    simp only [retiredIn, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hret
    obtain ⟨x, hx, hxa, hxc⟩ := hret
    exact hn key v hkv x hx hxc hxa
  · rw [hchar] at hkv; split at hkv
    · cases hkv
    · rw [hsum _ (fun _ _ _ => gc_head _ _ _ _ _), hsum _ (fun _ _ _ => gs_head _ _ _ _ _)]
      exact hH2 p rel c s lim cap wd rt hkv

/-! ## The cells after a turn: a parent that is live and not retired, or born, is live -/

omit [Ord D] in
private theorem insertAll_live {E : Env D} {c : D} :
    ∀ {m : Cells D} {ps : List (D × Entry)}, (∀ q ∈ ps, q.1 = c → ∃ cell, q.2 = .live cell) →
      ((∃ cell, m.get (trieSpec E) (.cell c) = some (.entry (.live cell))) ∨ c ∈ ps.map Prod.fst) →
      ∃ cell, (insertAll E m ps).get (trieSpec E) (.cell c) = some (.entry (.live cell))
  | m, [], _, h => by
      rcases h with h | h
      · exact h
      · simp at h
  | m, q :: rest, hq, h => by
      show ∃ cell, (insertAll E (m.insert (trieSpec E) (.cell q.1) (.entry q.2)) rest).get _ _ = _
      apply insertAll_live (fun q' hq' => hq q' (List.mem_cons_of_mem _ hq'))
      by_cases hqc : q.1 = c
      · obtain ⟨cell, hcell⟩ := hq q (by simp) hqc
        left; exact ⟨cell, by rw [Trie.get_insert, if_pos (by rw [hqc]), hcell]⟩
      · rcases h with ⟨cell, hm⟩ | h
        · left
          exact ⟨cell, by rw [Trie.get_insert, if_neg (fun he => hqc (by injection he with he; exact he.symm)), hm]⟩
        · simp only [List.map_cons, List.mem_cons] at h
          rcases h with h | h
          · exact absurd h.symm hqc
          · right; exact h

private theorem touchCheck_entry {E : Env D} {w : World D} {x : Touch D} {p : Post D}
    (h : touchCheck E w x = .ok (some p)) : x.act = .retire ∨ ∃ cell, p.entry = .live cell := by
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
          exact .inr ⟨post, rfl⟩
  | retire => exact .inl rfl

/-- A parent live before the turn and not retired by it, or born by it, is live after it. -/
private theorem commit_live {E : Env D} {w : World D} {t : Turn D} {posts : List (Post D)}
    (hk : Checked E w t posts) {c : D}
    (hc : ((w.live E c).isSome = true ∧ ∀ x ∈ t.touches, x.cell = c → x.act ≠ .retire) ∨ c ∈ createdIds t) :
    ∃ cell, (commit E w t posts).trie.get (trieSpec E) (.cell c) = some (.entry (.live cell)) := by
  show ∃ cell, (commitTrie E w t posts).get (trieSpec E) (.cell c) = _
  rw [commitTrie_cell]
  apply insertAll_live
  · intro q hq _
    unfold bornEntries at hq
    obtain ⟨⟨_, cell⟩, _, rfl⟩ := List.mem_map.mp hq
    exact ⟨cell, rfl⟩
  · rcases hc with ⟨hl, hnr⟩ | hb
    · left
      apply insertAll_live
      · intro q hq hqc
        obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
        obtain ⟨raw, hm, rfl⟩ := hk.touches
        have hp' : some p ∈ raw := by simpa [List.reduceOption, List.mem_filterMap] using hp
        obtain ⟨x, hx, hr⟩ := mapEx_mem hm (some p) hp'
        have hcell := (touchCheck_some hr).1
        rcases touchCheck_entry hr with ha | he
        · exact absurd ha (hnr x hx (by rw [← hcell]; exact hqc))
        · exact he
      · left
        obtain ⟨cell, hcell⟩ := Option.isSome_iff_exists.mp hl
        exact ⟨cell, live_get hcell⟩
    · right
      simpa [bornEntries, createdIds, List.map_map, Function.comp_def] using hb

/-- **An admitted turn keeps the rows invariant.** The premises: a lawful `Env` (the parent listing
`dropHeads` and `checkRowsRemain` read is the parent's entries: digests one size and injective), the
rows canonical, and the invariant itself. -/
theorem admit_rowsOk {E : Env D} {n : Nat} (hE : E.Lawful n) {w w' : World D} {t : Turn D}
    (hr : w.RowsCanon E) (hok : w.RowsOk E) (h : World.admit E w t = .ok w') : w'.RowsOk E := by
  have hrows : w'.rows = (rowsAfter E w t).1 := by obtain ⟨_, _, he⟩ := admit_rows h; exact he
  obtain ⟨posts, hk, hw'⟩ := admit_ok h
  have htrie : w'.trie = (commit E w t posts).trie := by rw [hw']
  have hrun := hk.rows
  unfold rowsRun at hrun
  simp only [except_bind_ok] at hrun
  obtain ⟨⟨⟩, -, ⟨⟩, hbd, hrun⟩ := hrun
  split at hrun
  · simp at hrun
  rw [except_bind_ok] at hrun
  obtain ⟨acc, hf, hd⟩ := hrun
  simp only [pure, Except.pure, Except.ok.injEq] at hd
  have hb : ∀ x ∈ t.rows, ∀ key, x.slot = .row key → key.rel < 256 ∧ key.k.size ≤ Bounds.keyBytesMax := by
    intro x hx key hs
    have := (List.all_eq_true.mp (req_ok.mp hbd)) x hx
    rw [hs] at this
    simpa [Bool.and_eq_true, decide_eq_true_eq] using this
  obtain ⟨hF0, hH0, hP0⟩ := hok
  have hi0 : Inv E w.rows := (inv_iff hr.1).mpr ⟨hF0, hH0⟩
  obtain ⟨hca, hia, hpa, hna⟩ := foldRows_inv t.rows (w.rows, 0) acc hr hi0 (par_pre hr hP0)
    (noRet_pre hE hr hk.rowsRemain) hb hf
  have hchar := dropHeads_char hE t acc hca hia.1 hna
  have hcan' := (dropHeads_weight t acc hca).2
  rw [hd] at hchar hcan'
  have hi' := inv_after hca.1 hcan'.1 hia hna hchar
  obtain ⟨hF', hH'⟩ := (inv_iff hcan'.1).mp hi'
  refine ⟨?_, ?_, ?_⟩
  · rw [hrows]; exact hF'
  · rw [hrows]; exact hH'
  · rw [hrows, htrie]
    unfold rowsParented
    rw [List.all_eq_true]
    rintro ⟨s, v⟩ hm
    cases s with
    | row _ => rfl
    | head q rel =>
        dsimp only
        have hg : (rowsAfter E w t).1.get (rowSpec E) (.head q rel) = some v :=
          (Trie.mem_toList (rowSpec E) 0 _ hcan'.1 _ _).mp hm
        rw [hchar] at hg
        split at hg
        · cases hg
        · rename_i hnr
          have hnr' : ∀ x ∈ t.touches, x.cell = q → x.act ≠ .retire := by
            intro x hx hxc hxa
            apply hnr
            simp only [retiredIn, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq]
            exact ⟨x, hx, hxa, hxc⟩
          obtain ⟨cell, hcell⟩ := commit_live hk (by
            rcases hpa q rel v hg with hl | hb
            · exact .inl ⟨hl, hnr'⟩
            · exact .inr hb)
          rw [hcell]

/-! ## Genesis and refusal -/

theorem genesis_rowsOk (E : Env D) (o : D) (a : Nat) : (World.genesis E o a).RowsOk E :=
  ⟨fun _ h => by simp [World.genesis, Trie.T.toList] at h, rfl, rfl⟩

theorem receive_genesis_rowsOk (X : Receive.Ctx D) (name nonce : ByteArray) (allowance : Nat)
    (founders : List (ByteArray × D)) : (Receive.genesisWorld X name nonce allowance founders).RowsOk X.env :=
  ⟨fun _ h => by simp [Receive.genesisWorld, World.genesis, Trie.T.toList] at h, rfl, rfl⟩

theorem refuse_rowsOk {E : Env D} {w w' : World D} {r : Refused D} (hok : w.RowsOk E)
    (h : World.refuse E w r = .ok w') : w'.RowsOk E := by
  unfold World.RowsOk; rw [refuse_rows h, refuse_trie h]; exact hok

/-! ## Teeth -/

/-- **Tooth: a head whose count its rows do not reach is refused by `rowsHeaded`.** A listing with
one head counting one row (sum 5) and no row. -/
theorem rowsHeaded_head_bumped :
    rowsHeaded ([(RowSlot.head (0 : Nat) 0, RowLeaf.head 1 5 4 10 2 false)] : List (RowSlot Nat × RowLeaf)) = false := by
  decide

omit [Ord D] in
/-- **Tooth: a head left behind its retired parent is refused by `rowsParented`** (what happens
if `dropHeads` did not run): the parent's slot holds a tombstone, the rows still hold its head. -/
theorem rowsParented_orphan_head (E : Env D) (p : D) (rel : Nat) (l : RowLeaf) :
    rowsParented E ((Trie.T.empty : Cells D).insert (trieSpec E) (.cell p) (.entry .tomb))
      ((Trie.T.empty : Rows D).insert (rowSpec E) (.head p rel) l) = false := by
  unfold rowsParented
  simp [Trie.T.insert, Trie.insAt, Trie.mkLeaf, Trie.T.toList, Trie.T.get, Trie.getAt, Trie.find_cons]

/-! ## Every reached World -/

/-- **Every World a log reaches keeps the rows invariant** (with the rows canonical). -/
theorem fold_rowsOk {E : Env D} {n : Nat} (hE : E.Lawful n) {w w' : World D} {l : List (Step D)}
    (hr : w.RowsCanon E) (hok : w.RowsOk E) (h : World.fold E w l = .ok w') : w'.RowsOk E :=
  (fold_keeps (P := fun v => v.RowsCanon E ∧ v.RowsOk E)
    (fun ⟨hc, ho⟩ ha => ⟨admit_rowsCanon hc ha, admit_rowsOk hE hc ho ha⟩)
    (fun ⟨hc, ho⟩ hf => ⟨refuse_rowsCanon hc hf, refuse_rowsOk ho hf⟩) ⟨hr, hok⟩ h).2

/-- **A carry keeps the rows invariant**: the carried World holds the exported one's trie and rows. -/
theorem carry_rowsOk {X : Receive.Ctx D} {name nonce : ByteArray} {w w' : World D} (hok : w.RowsOk X.env)
    (h : Receive.carry X name nonce w.origin w.carried = .ok w') : w'.RowsOk X.env := by
  obtain ⟨_, rfl⟩ := Receive.carry_ok.mp h
  exact hok

omit [Ord D] [DecidableEq D] in
private theorem filterMap_amts [DecidableEq D] {p : D} {rel : Nat} {F : RowSlot D × RowLeaf → Option Nat}
    (h1 : ∀ key amt v, F (.row key, .row amt v) = if key.parent = p ∧ key.rel = rel then some amt else none)
    (h2 : ∀ q r v, F (.head q r, v) = none)
    (h3 : ∀ key c s l cap wd rt, F (.row key, .head c s l cap wd rt) = none) :
    ∀ l : List (RowSlot D × RowLeaf),
      (l.filterMap F).length = (l.map (gc p rel)).sum ∧ (l.filterMap F).sum = (l.map (gs p rel)).sum
  | [] => ⟨rfl, rfl⟩
  | q :: l => by
      obtain ⟨ih1, ih2⟩ := filterMap_amts h1 h2 h3 l
      obtain ⟨_ | key, ⟨c0, s0, l0, cap0, wd0, rt0⟩ | ⟨amt, v⟩⟩ := q
      · simp only [List.filterMap_cons, h2, List.map_cons, List.sum_cons, gc_head, gs_head, Nat.zero_add]
        exact ⟨ih1, ih2⟩
      · simp only [List.filterMap_cons, h2, List.map_cons, List.sum_cons, gc_head, gs_head, Nat.zero_add]
        exact ⟨ih1, ih2⟩
      · have e1 : gc p rel (.row key, .head c0 s0 l0 cap0 wd0 rt0) = 0 := rfl
        have e2 : gs p rel (.row key, .head c0 s0 l0 cap0 wd0 rt0) = 0 := rfl
        simp only [List.filterMap_cons, h3, List.map_cons, List.sum_cons, e1, e2, Nat.zero_add]
        exact ⟨ih1, ih2⟩
      · by_cases hk : key.parent = p ∧ key.rel = rel
        · have e : F (.row key, .row amt v) = some amt := by rw [h1, if_pos hk]
          simp only [List.filterMap_cons, e, List.length_cons, List.map_cons, List.sum_cons]
          simp only [gc, gs, hk, and_self, if_true]
          exact ⟨by omega, by omega⟩
        · have e : F (.row key, .row amt v) = none := by rw [h1, if_neg hk]
          simp only [List.filterMap_cons, e, List.map_cons, List.sum_cons, gc_row_ne hk, gs_row_ne hk, Nat.zero_add]
          exact ⟨ih1, ih2⟩

omit [Ord D] [DecidableEq D] in
private theorem filterMap_amts_len [DecidableEq D] {p : D} {rel : Nat} {F : RowSlot D × RowLeaf → Option Nat}
    (h1 : ∀ key amt v, F (.row key, .row amt v) = if key.parent = p ∧ key.rel = rel then some amt else none)
    (h2 : ∀ q r v, F (.head q r, v) = none)
    (h3 : ∀ key c s l cap wd rt, F (.row key, .head c s l cap wd rt) = none) (l : List (RowSlot D × RowLeaf)) :
    (l.filterMap F).length = (l.map (gc p rel)).sum := (filterMap_amts h1 h2 h3 l).1

omit [Ord D] [DecidableEq D] in
private theorem filterMap_amts_sum [DecidableEq D] {p : D} {rel : Nat} {F : RowSlot D × RowLeaf → Option Nat}
    (h1 : ∀ key amt v, F (.row key, .row amt v) = if key.parent = p ∧ key.rel = rel then some amt else none)
    (h2 : ∀ q r v, F (.head q r, v) = none)
    (h3 : ∀ key c s l cap wd rt, F (.row key, .head c s l cap wd rt) = none) (l : List (RowSlot D × RowLeaf)) :
    (l.filterMap F).sum = (l.map (gs p rel)).sum := (filterMap_amts h1 h2 h3 l).2

/-- **A head counts its rows** (`head_sum`): on canonical rows that keep the invariant, a head's
count is the number of rows of its relation, its sum their `amt`s' sum, within its cap and limit,
and every row of it has its key at the head's width. -/
theorem head_sum {E : Env D} {w : World D} (hr : w.RowsCanon E) (hok : w.RowsOk E) {p : D}
    {rel c s l cap wd : Nat} {rt : Bool} (h : rowAt E w.rows (.head p rel) = some (.head c s l cap wd rt)) :
    c = (w.rows.toList.filterMap fun q => match q with
          | (.row key, .row amt _) => if key.parent = p ∧ key.rel = rel then some amt else none
          | _ => none).length ∧
      s = (w.rows.toList.filterMap fun q => match q with
          | (.row key, .row amt _) => if key.parent = p ∧ key.rel = rel then some amt else none
          | _ => none).sum ∧
      s ≤ cap ∧ c ≤ l ∧
      ∀ key v, (RowSlot.row key, v) ∈ w.rows.toList → key.parent = p → key.rel = rel → key.k.size = wd := by
  have hi : Inv E w.rows := (inv_iff hr.1).mpr ⟨hok.1, hok.2.1⟩
  have hg : w.rows.get (rowSpec E) (.head p rel) = some (.head c s l cap wd rt) := h
  obtain ⟨hc, hs⟩ := hi.2.2 _ _ _ _ _ _ _ _ hg
  have hfit := hi.1 _ _ hg
  simp only [rowFits, Bool.and_eq_true, decide_eq_true_eq] at hfit
  refine ⟨?_, ?_, by omega, by omega, fun key v hm hp hrel => ?_⟩
  · rw [filterMap_amts_len, hc]
    all_goals first | (intro _ _ v; cases v <;> rfl) | (intros; rfl)
  · rw [filterMap_amts_sum, hs]
    all_goals first | (intro _ _ v; cases v <;> rfl) | (intros; rfl)
  · obtain ⟨c', s', l', cap', rt', hg'⟩ := hi.2.1 key v (Trie.get_of_mem (rowSpec E) hr.1 hm)
    rw [hp, hrel, hg] at hg'
    simp only [Option.some.injEq, RowLeaf.head.injEq] at hg'
    exact hg'.2.2.2.2.1.symm

/-- **`head_sum` on every World a log reaches from genesis**: every premise discharged but the
`Env`'s lawfulness (`Receive.deployed_lawful` at the deployed codec: `deployed_fold_head_sum`). -/
theorem fold_head_sum {E : Env D} {n : Nat} (hE : E.Lawful n) {o : D} {a : Nat} {l : List (Step D)}
    {w : World D} (h : World.fold E (World.genesis E o a) l = .ok w) {p : D} {rel c s lim cap wd : Nat}
    {rt : Bool} (hh : rowAt E w.rows (.head p rel) = some (.head c s lim cap wd rt)) :
    c = (w.rows.toList.filterMap fun q => match q with
          | (.row key, .row amt _) => if key.parent = p ∧ key.rel = rel then some amt else none
          | _ => none).length ∧
      s = (w.rows.toList.filterMap fun q => match q with
          | (.row key, .row amt _) => if key.parent = p ∧ key.rel = rel then some amt else none
          | _ => none).sum ∧
      s ≤ cap ∧ c ≤ lim ∧
      ∀ key v, (RowSlot.row key, v) ∈ w.rows.toList → key.parent = p → key.rel = rel → key.k.size = wd :=
  head_sum (fold_rowsCanon (genesis_rowsCanon E o a) h)
    (fold_rowsOk hE (genesis_rowsCanon E o a) (genesis_rowsOk E o a) h) hh

/-- **Deployed: every World a log reaches from genesis has canonical rows that keep the invariant**,
every premise discharged (`Receive.deployed_lawful`): `head_sum` applies to it with nothing left
to assume (`fold_head_sum` at the deployed `Env`). -/
theorem deployed_fold_rowsOk {o : Nanodregg.Codec.Digest} {a : Nat} {l : List (Step Nanodregg.Codec.Digest)}
    {w : World Nanodregg.Codec.Digest}
    (h : World.fold Nanodregg.Codec.Deployed.env (World.genesis Nanodregg.Codec.Deployed.env o a) l = .ok w) :
    w.RowsCanon Nanodregg.Codec.Deployed.env ∧ w.RowsOk Nanodregg.Codec.Deployed.env :=
  ⟨fold_rowsCanon (genesis_rowsCanon _ o a) h,
    fold_rowsOk Receive.deployed_lawful (genesis_rowsCanon _ o a) (genesis_rowsOk _ o a) h⟩

/-! ## Tooth: the row write is what keeps a head's count -/

/-- The insert arm of `rowStep` with its row write deleted: the head is bumped, the row is not
written. -/
private def plantInsert (E : Env D) (r : Rows D) (key : RowKey D) (amt : Nat) : Rows D :=
  match headOf E r key.parent key.rel with
  | some (count, sum, limit, cap, width, retract) =>
      setHead E r key.parent key.rel (count + 1) (sum + amt) limit cap width retract
  | none => r

private theorem plant_breaks (E : Env D) (p : D) (cell : Cell) (w0 : World D)
    (htrie : w0.trie = (Trie.T.empty : Cells D).insert (trieSpec E) (.cell p) (.entry (.live cell)))
    (hrows : w0.rows = (Trie.T.empty : Rows D).insert (rowSpec E) (.head p 0) (.head 0 0 1 10 0 false)) :
    w0.RowsOk E ∧ ¬({ w0 with rows := plantInsert E w0.rows ⟨p, 0, ByteArray.empty⟩ 5 } : World D).RowsOk E := by
  have hr0 : Trie.Canon (rowSpec E) 0 w0.rows := by
    rw [hrows]; exact Trie.canon_insert (rowSpec E) _ _ (Trie.canon_empty _ 0)
  have hget0 : ∀ k, w0.rows.get (rowSpec E) k =
      if k = .head p 0 then some (.head 0 0 1 10 0 false) else none := by
    intro k; rw [hrows, Trie.get_insert, Trie.get_empty]
  have hall0 : ∀ q ∈ w0.rows.toList, q.1 = .head p 0 := by
    rintro ⟨k, l⟩ hq
    have := Trie.get_of_mem (rowSpec E) hr0.1 hq
    rw [hget0] at this
    split at this
    · assumption
    · cases this
  have hplant : plantInsert E w0.rows ⟨p, 0, ByteArray.empty⟩ 5 =
      setHead E w0.rows p 0 (0 + 1) (0 + 5) 1 10 0 false := by
    unfold plantInsert headOf rowAt
    rw [hget0, if_pos rfl]
  refine ⟨?_, ?_⟩
  · have hi : Inv E w0.rows := by
      refine ⟨fun k v hkv => ?_, fun key v hkv => ?_, fun q rl c s lim cap wd rt hkv => ?_⟩
      · rw [hget0] at hkv
        split at hkv
        · rename_i hk; subst hk
          simp only [Option.some.injEq] at hkv; subst hkv
          rfl
        · cases hkv
      · rw [hget0, if_neg (fun h => by cases h)] at hkv; cases hkv
      · have hz : ∀ g : RowSlot D × RowLeaf → Nat, (∀ q r v, g (.head q r, v) = 0) → (w0.rows.toList.map g).sum = 0 := by
          intro g hg
          apply sum_zero
          rintro ⟨k, v⟩ hq
          rw [show k = .head p 0 from hall0 _ hq]; exact hg _ _ _
        rw [hget0] at hkv
        split at hkv
        · simp only [Option.some.injEq, RowLeaf.head.injEq] at hkv
          obtain ⟨rfl, rfl, -⟩ := hkv
          exact ⟨hz _ (gc_head _ _), hz _ (gs_head _ _)⟩
        · cases hkv
    obtain ⟨hf, hh⟩ := (inv_iff hr0.1).mp hi
    refine ⟨hf, hh, ?_⟩
    unfold rowsParented
    rw [List.all_eq_true]
    intro q hq
    rw [hall0 q hq, htrie]
    dsimp only
    simp only [Trie.get_insert_self]
  · rintro ⟨hf, hh, -⟩
    simp only at hf hh
    rw [hplant] at hf hh
    have hr1 : Trie.Canon (rowSpec E) 0
        (setHead E w0.rows p 0 (0 + 1) (0 + 5) 1 10 0 false) := by
      unfold setHead; exact Trie.canon_insert (rowSpec E) _ _ hr0
    have hi := (inv_iff hr1.1).mpr ⟨hf, hh⟩
    have hg1 : (setHead E w0.rows p 0 (0 + 1) (0 + 5) 1 10 0 false).get (rowSpec E) (.head p 0) =
        some (.head (0 + 1) (0 + 5) 1 10 0 false) := by
      unfold setHead; exact Trie.get_insert_self (rowSpec E) _ _ _
    have hc := (hi.2.2 _ _ _ _ _ _ _ _ hg1).1
    have hz : ((setHead E w0.rows p 0 (0 + 1) (0 + 5) 1 10 0 false).toList.map (gc p 0)).sum = 0 := by
      apply sum_zero
      rintro ⟨k, v⟩ hq
      have := Trie.get_of_mem (rowSpec E) hr1.1 hq
      unfold setHead at this
      rw [Trie.get_insert] at this
      split at this
      · rename_i hk; rw [show k = .head p 0 from hk]; exact gc_head _ _ _ _ _
      · rw [hget0] at this
        split at this
        · rename_i hk; rw [show k = .head p 0 from hk]; exact gc_head _ _ _ _ _
        · cases this
    omega

/-- **Tooth: the row write is what keeps a head's count.** There is a World satisfying `RowsOk` (one
live parent, one declared relation under it, no rows) from which the insert arm without its row
write (`plantInsert`) leaves rows that violate `RowsOk`: the head counts one row and none is there.
So `admit_rowsOk` holds because `rowStep` writes the row it counts. -/
theorem plantInsert_breaks_rowsOk (E : Env D) (o p : D) (cell : Cell) :
    ∃ w0 : World D, w0.RowsOk E ∧
      ¬({ w0 with rows := plantInsert E w0.rows ⟨p, 0, ByteArray.empty⟩ 5 } : World D).RowsOk E :=
  ⟨{ World.genesis E o 0 with
      trie := (Trie.T.empty : Cells D).insert (trieSpec E) (.cell p) (.entry (.live cell))
      rows := (Trie.T.empty : Rows D).insert (rowSpec E) (.head p 0) (.head 0 0 1 10 0 false) },
    plant_breaks E p cell _ rfl rfl⟩


end Nanodregg.Kernel
