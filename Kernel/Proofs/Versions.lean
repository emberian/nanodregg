/-
# Kernel.Proofs.Versions — a stale pin observed on the fold is behind for ever (KERNEL-54)

A pin names a monotone version (a cell's write count in its entry, a row's version, a relation's
floor), so the World a fold reaches never holds an observed pin's value again once it has moved: a
`stale` refusal is final by monotonicity and needs no record (`Receive.judge` declines it).

The statements are in the W0 form ROOT ruled: the pin was OBSERVED at an earlier World of the same
fold (`w₀`, with `w₀ →* w →* w'`). A pin naming a FUTURE state (the next version is predictable) is
stale now and may match later; it is AHEAD, not final, and nothing here claims otherwise. The
follower judges against its own fold, so it knows which World it observed a pin at.

Each theorem's hash escape is a collision among a CONCRETE list of inputs (`CollidesAmong hash S`),
the (domain, bytes) inputs of the very pins it compares: `pinPre`, `rowPre`, `rangePre` and, as a
range pin embeds its rows' leaf digests, `leafPres` of both listings (`CollidesAmong` and its tooth
`Separates` live in `Kernel.Proofs.Fold`). A collision among SOME two inputs is not a disjunct:
pigeonhole proves it of every hash into a finite `D`, so it would make each statement vacuous (KERNEL-56
deleted every such predicate). Two inputs in different domains are two different inputs, so no premise
separates the domains.

* `stale_behind_forever` — cells: a cell pin observed at `w₀` and stale at `w` is stale at every `w'`
  the fold reaches, or the hash collides on the pin inputs of `w₀`'s and `w'`'s entry. The pin reads
  the ENTRY: absent, tombstone and live are three domains, and a live pin names the version.
* `row_stale_behind_forever`, `range_stale_behind_forever` — rows and ranges: the same, or the
  parent is RETIRED (its entry a tombstone: a retired parent drops its heads, so its floor reads 0 again; but every row touch
  and range read under it is refused `orphanRow`/`rowParentUnpinned` before any pin is read, and a
  tombstone is never reborn: still final). Both assume a lawful `Ord D` (`Std.TransOrd`,
  `Std.LawfulEqOrd`, as `Budget` and `Ledger` do): under an `Ord` that never answers `.eq`,
  `checkShape` admits `[retire p, write p]`, `dropHeads` resets `p`'s floor while `p` stays live, and
  the old absent pin recurs. The range theorem reads every range with `pre.size ≤ width`, at any
  relation and width (cv 01a14f7e: the relation and the width are LEB128 in the keys and the pin, so
  relation 259 is not relation 3, which the one-byte encoding made it, with relation 259's floor 0
  for ever, and insert then retract returned the pin with the parent live).
* `pinOf_old_recurs` — the TOOTH: under the pin before KERNEL-54 (a content digest of `w.live`, which
  reads a tombstone as absent), never born → born → retired returns the absent pin; under `pinOf`
  it does not. `rowPin_old_floor_recurs` — the second: a retired parent's floor reads 0 again, so
  the parent-gone disjunct is needed. `rangePin_floorless_recurs` — the third: without the floor a
  range pin recurs (insert then retract under a live parent), so the floor is what the range theorem
  rests on.
-/
import Kernel.Proofs.RowsHead
import Kernel.Proofs.CellsFit
import Kernel.Proofs.Lawful

namespace Nanodregg.Kernel

open Nanodregg.Codec.Kernel (Cell.Fits)

variable {D : Type} [Ord D] [DecidableEq D]

/-! ## Cells: an entry only moves forward along the fold

Per cell id, along `World.fold`: absent → live at version 0 (a birth, only of an id not taken) →
live at one more version per write → tombstone (a retirement), and a tombstone for ever. `EAdv a b`
says `b` is strictly past `a` in that order; every step either keeps an entry or moves it strictly
forward (`admit_entryStep`), so an entry that has moved never comes back (`entry_behind_forever`). -/

/-- The entry `b` is strictly past the entry `a`. -/
private def EAdv : Option Entry → Option Entry → Prop
  | none, some _ => True
  | some (.live _ v), some (.live _ v') => v < v'
  | some (.live _ _), some .tomb => True
  | _, _ => False

private theorem eAdv_trans {a b c : Option Entry} (h₁ : EAdv a b) (h₂ : EAdv b c) : EAdv a c := by
  rcases a with _ | (⟨_, _⟩ | _) <;> rcases b with _ | (⟨_, _⟩ | _) <;>
    rcases c with _ | (⟨_, _⟩ | _) <;> simp only [EAdv] at h₁ h₂ ⊢ <;> omega

/-- One step keeps the entry or moves it strictly forward. -/
private def EStep (a b : Option Entry) : Prop := a = b ∨ EAdv a b

private theorem eStep_trans {a b c : Option Entry} (h₁ : EStep a b) (h₂ : EStep b c) : EStep a c := by
  rcases h₁ with rfl | h₁
  · exact h₂
  · rcases h₂ with rfl | h₂
    · exact .inr h₁
    · exact .inr (eAdv_trans h₁ h₂)

/-- What a touch leaves behind is at its own cell and strictly past the entry it was judged on: a
write one version on, a retirement the tombstone, both of a live cell. -/
private theorem touchCheck_adv {E : Env D} {w : World D} {x : Touch D} {p : Post D}
    (h : touchCheck E w x = .ok (some p)) :
    p.cell = x.cell ∧ EAdv (w.entry E x.cell) (some p.entry) := by
  unfold touchCheck at h
  simp only [except_bind_ok] at h
  obtain ⟨⟨⟩, -, h⟩ := h
  revert h
  generalize w.entry E x.cell = cur
  intro h
  cases hx : x.act with
  | keep => rw [hx] at h; cases h
  | write ops =>
      rw [hx] at h
      rcases cur with _ | (⟨cell, ver⟩ | _)
      · cases h
      · simp only [except_bind_ok] at h
        obtain ⟨⟨⟩, -, post, -, hp⟩ := h
        simp only [pure, Except.pure, Except.ok.injEq, Option.some.injEq] at hp
        subst hp
        exact ⟨rfl, by simp only [EAdv]; omega⟩
      · cases h
  | retire =>
      rw [hx] at h
      rcases cur with _ | (⟨cell, ver⟩ | _)
      · cases h
      · simp only [except_bind_ok] at h
        obtain ⟨⟨⟩, -, hp⟩ := h
        simp only [pure, Except.pure, Except.ok.injEq, Option.some.injEq] at hp
        subst hp
        exact ⟨rfl, trivial⟩
      · cases h

/-- **An admitted turn keeps each entry or moves it strictly forward.** A born id was not taken
(`checkCreates`), and its birth is written last; a touched id holds what one of its touches left,
each judged on the entry before the turn; any other id is untouched. -/
private theorem admit_entryStep {E : Env D} {w w' : World D} {t : Turn D}
    (h : World.admit E w t = .ok w') (c : D) : EStep (w.entry E c) (w'.entry E c) := by
  obtain ⟨posts, hk, rfl⟩ := admit_ok h
  have hent : (commit E w t posts).entry E c =
      match (insertAll E (insertAll E w.trie (posts.map Post.pair)) (bornEntries t)).get (trieSpec E)
        (.cell c) with
      | some (.entry e) => some e
      | _ => none := by
    show (match (commitTrie E w t posts).get (trieSpec E) (.cell c) with
      | some (.entry e) => some e
      | _ => none) = _
    rw [commitTrie_cell]
  by_cases hb : c ∈ (bornEntries t).map Prod.fst
  · obtain ⟨e, he, hg⟩ := insertAll_get_mem (m := insertAll E w.trie (posts.map Post.pair)) hb
    rw [hent, hg]
    obtain ⟨⟨c', cell⟩, hm, hce⟩ := List.mem_map.mp he
    simp only [Prod.mk.injEq] at hce
    obtain ⟨rfl, rfl⟩ := hce
    have hnot : w.taken E c' = false := by
      have := hk.creates
      unfold checkCreates at this
      simp only [except_bind_ok] at this
      obtain ⟨⟨⟩, -, ⟨⟩, -, ⟨⟩, -, hf⟩ := this
      have := req_ok.mp (forEx_ok.mp hf c' (List.mem_map.mpr ⟨(c', cell), hm, rfl⟩))
      simpa using this
    unfold World.taken at hnot
    have hn : w.entry E c' = none := by
      cases hw : w.entry E c' with
      | none => rfl
      | some _ => rw [hw] at hnot; cases hnot
    rw [hn]
    exact .inr trivial
  · by_cases hp : c ∈ (posts.map Post.pair).map Prod.fst
    · rw [hent, insertAll_get_of_not_mem hb]
      obtain ⟨e, he, hg⟩ := insertAll_get_mem (m := w.trie) hp
      rw [hg]
      obtain ⟨p, hpm, hpe⟩ := List.mem_map.mp he
      simp only [Post.pair, Prod.mk.injEq] at hpe
      obtain ⟨rfl, rfl⟩ := hpe
      obtain ⟨raw, hm, rfl⟩ := hk.touches
      have hp' : some p ∈ raw := by simpa [List.reduceOption, List.mem_filterMap] using hpm
      obtain ⟨x, -, hx⟩ := mapEx_mem hm (some p) hp'
      obtain ⟨hc, hadv⟩ := touchCheck_adv hx
      rw [hc]
      exact .inr hadv
    · left
      unfold World.entry
      show _ = (match (commitTrie E w t posts).get (trieSpec E) (.cell c) with
        | some (.entry e) => some e
        | _ => none)
      rw [commitTrie_entry hp hb]
      rfl

/-- **Along a fold each entry is kept or moves strictly forward** (a refusal moves no cell). -/
private theorem fold_entryStep {E : Env D} (c : D) :
    ∀ {w w' : World D} {l : List (Step D)}, World.fold E w l = .ok w' →
      EStep (w.entry E c) (w'.entry E c)
  | w, w', [], h => by
      simp only [World.fold, Except.ok.injEq] at h
      subst h; exact .inl rfl
  | w, w', s :: rest, h => by
      obtain ⟨w1, h1, h2⟩ := fold_cons_ok.mp h
      have hs : EStep (w.entry E c) (w1.entry E c) := by
        cases s with
        | turn t => exact admit_entryStep h1 c
        | refusal r => exact .inl (refuse_entry h1 c).symm
      exact eStep_trans hs (fold_entryStep c h2)

/-- **An entry that has moved never comes back** (no hash): observed at `w₀`, different at `w`,
then strictly past `w₀`'s at every World the fold reaches from `w`. -/
private theorem entry_behind_forever {E : Env D} {w₀ w w' : World D} {l₁ l₂ : List (Step D)}
    (h₁ : World.fold E w₀ l₁ = .ok w) (h₂ : World.fold E w l₂ = .ok w') {c : D}
    (hne : w.entry E c ≠ w₀.entry E c) : EAdv (w₀.entry E c) (w'.entry E c) := by
  rcases fold_entryStep c h₁ with heq | hadv
  · exact absurd heq.symm hne
  · rcases fold_entryStep c h₂ with heq | hadv'
    · rw [← heq]; exact hadv
    · exact eAdv_trans hadv hadv'

/-! ### Pins name their inputs

A pin is the hash of one (domain, bytes) input. A theorem that a pin has moved can fail only where
the hash maps two DIFFERENT inputs to one digest, and the inputs in question are the theorem's own:
the pin inputs of the Worlds it compares. `CollidesAmong hash S` says exactly that, for a list `S`
the theorem builds from its own objects (`CollidesAmong`, Kernel/Proofs/Fold.lean). -/

omit [Ord D] [DecidableEq D] in
theorem pinOf_eq_pre (E : Env D) (e : Option Entry) : pinOf E e = E.hash (pinPre E e).1 (pinPre E e).2 := by
  rcases e with _ | (⟨_, _⟩ | _) <;> rfl

/-- An entry's version fits `nat64` (what `pinOf` spells; `Leaf.CellFit` holds it of a fit World). -/
private def VerFit : Option Entry → Prop
  | some (.live _ v) => v < 2 ^ 64
  | _ => True

private theorem cellsFit_verFit {E : Env D} {w : World D} (hf : w.CellsFit Cell.Fits E) (c : D) :
    VerFit (w.entry E c) := by
  cases he : w.entry E c with
  | none => trivial
  | some e =>
      cases e with
      | tomb => trivial
      | live cell v => exact (hf _ _ (entry_get he)).2

omit [Ord D] [DecidableEq D] in
/-- **An entry strictly past another has another pin input**: absent, tombstone and live are three
domains, and two live entries differ in their eight version bytes. -/
private theorem pinPre_adv_ne {E : Env D} {a b : Option Entry} (ha : VerFit a) (hb : VerFit b)
    (hadv : EAdv a b) : pinPre E b ≠ pinPre E a := by
  rcases a with _ | (⟨c, v⟩ | _) <;> rcases b with _ | (⟨c', v'⟩ | _) <;> simp only [EAdv] at hadv
  · intro h; have h1 := congrArg Prod.fst h; simp only [pinPre] at h1; exact absurd h1 (by decide)
  · intro h; have h1 := congrArg Prod.fst h; simp only [pinPre] at h1; exact absurd h1 (by decide)
  · intro h
    simp only [pinPre, Prod.mk.injEq] at h
    have := (bytes_append_inj h.2 (by simp [nat64_size])).1
    have := Nanodregg.Codec.Stream.nat64_lawfulOn.bytes_injective hb ha this
    omega
  · intro h; have h1 := congrArg Prod.fst h; simp only [pinPre] at h1; exact absurd h1 (by decide)

/-- **A cell pin observed on the fold and stale now is stale for ever.** From a World whose cells fit
(every reached World's: `fold_cellsFit`): if the pin of `c`'s entry at `w₀` differs from its pin at
`w`, a World the fold reaches from `w₀`, then no World the fold reaches from `w` holds the pin `w₀`
held, unless the hash collides on the two pin inputs compared, `w₀`'s and `w'`'s (they differ: the
entry has moved strictly forward). -/
theorem stale_behind_forever {E : Env D} {w₀ w w' : World D}
    {l₁ l₂ : List (Step D)} (hf : w₀.CellsFit Cell.Fits E)
    (h₁ : World.fold E w₀ l₁ = .ok w) (h₂ : World.fold E w l₂ = .ok w') {c : D}
    (hstale : pinOf E (w.entry E c) ≠ pinOf E (w₀.entry E c)) :
    pinOf E (w'.entry E c) ≠ pinOf E (w₀.entry E c) ∨
      CollidesAmong E.hash [pinPre E (w₀.entry E c), pinPre E (w'.entry E c)] := by
  have hne : w.entry E c ≠ w₀.entry E c := fun h => hstale (by rw [h])
  have hf' : w'.CellsFit Cell.Fits E := fold_cellsFit (fold_cellsFit hf h₁) h₂
  have hpre : pinPre E (w'.entry E c) ≠ pinPre E (w₀.entry E c) :=
    pinPre_adv_ne (cellsFit_verFit hf c) (cellsFit_verFit hf' c) (entry_behind_forever h₁ h₂ hne)
  by_cases hp : pinOf E (w'.entry E c) = pinOf E (w₀.entry E c)
  · exact .inr ⟨_, List.mem_cons_self, _, List.mem_cons_of_mem _ List.mem_cons_self,
      fun h => hpre h.symm, (pinOf_eq_pre E _).symm.trans (hp.symm.trans (pinOf_eq_pre E _))⟩
  · exact .inl hp

/-! ## Rows: a row slot's pin state only moves forward while its parent is not retired

What a row pin reads of a slot is its leaf, or (absent) its relation's floor (`PS`). Every change of
that state raises the rank `rk`: an insert (version = the floor) and a fresh upsert lift an absent
slot at floor `f` (rank `2f`) to rank `2f + 1`; an upsert bumps the version; a retract leaves the slot
absent at a floor past the version it removed; a retract elsewhere in the relation raises the floor.
So one row touch keeps a slot's state or raises its rank, and never lowers its relation's floor
(`rowStep_mono`); a turn none of whose touches retires the parent likewise (`admit_rowsMono`): only
`dropHeads` resets a floor, and only the retired parent's. -/

/-- What a row pin reads of a slot: its leaf, or (absent) its relation's floor. -/
private def PS : Option RowLeaf → Nat → Option RowLeaf × Nat
  | none, f => (none, f)
  | some l, _ => (some l, 0)

/-- The rank of a slot's pin state, which every change raises. -/
private def rk : Option RowLeaf → Nat → Nat
  | none, f => 2 * f
  | some (.row _ _ v), _ => 2 * v + 1
  | some (.head ..), _ => 0

private theorem rk_of_ps {o o' : Option RowLeaf} {f f' : Nat} (h : PS o f = PS o' f') :
    rk o f = rk o' f' := by
  rcases o with _ | l <;> rcases o' with _ | l' <;>
    simp only [PS, Prod.mk.injEq, Option.some.injEq, reduceCtorEq, false_and] at h
  · rw [h.2]
  · rw [h.1]; cases l' <;> rfl

/-- One stretch of the fold keeps a slot's pin state or raises its rank. -/
private def RStep (a b : Option RowLeaf × Nat) : Prop := PS a.1 a.2 = PS b.1 b.2 ∨ rk a.1 a.2 < rk b.1 b.2

private theorem rStep_trans {a b c : Option RowLeaf × Nat} (h₁ : RStep a b) (h₂ : RStep b c) : RStep a c := by
  rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂
  · exact .inl (h₁.trans h₂)
  · exact .inr (by rw [rk_of_ps h₁]; exact h₂)
  · exact .inr (by rw [← rk_of_ps h₂]; exact h₁)
  · exact .inr (Nat.lt_trans h₁ h₂)

/-- A row slot's state in some rows: its leaf and its relation's floor. -/
private def st (E : Env D) (r : Rows D) (key : RowKey D) : Option RowLeaf × Nat :=
  (rowAt E r (.row key), headFloor E r key.parent key.rel)

/-- From `r` to `r'`, the slot's relation's floor does not fall and its pin state moves forward. -/
private def Mono (E : Env D) (r r' : Rows D) (key : RowKey D) : Prop :=
  headFloor E r key.parent key.rel ≤ headFloor E r' key.parent key.rel ∧ RStep (st E r key) (st E r' key)

omit [Ord D] in
private theorem mono_refl (E : Env D) (r : Rows D) (key : RowKey D) : Mono E r r key :=
  ⟨Nat.le_refl _, .inl rfl⟩

omit [Ord D] in
private theorem mono_trans {E : Env D} {r r' r'' : Rows D} {key : RowKey D} (h₁ : Mono E r r' key)
    (h₂ : Mono E r' r'' key) : Mono E r r'' key :=
  ⟨Nat.le_trans h₁.1 h₂.1, rStep_trans h₁.2 h₂.2⟩

omit [Ord D] in
private theorem mono_of_eq {E : Env D} {r r' : Rows D} {key : RowKey D}
    (ha : rowAt E r' (.row key) = rowAt E r (.row key))
    (hf : headFloor E r' key.parent key.rel = headFloor E r key.parent key.rel) : Mono E r r' key := by
  unfold Mono st; rw [ha, hf]; exact ⟨Nat.le_refl _, .inl rfl⟩

omit [Ord D] in
private theorem rowAt_setHead_row (E : Env D) (r : Rows D) (p : D) (rel c s l cap w : Nat) (rt : Bool)
    (fl : Nat) (k : RowKey D) : rowAt E (setHead E r p rel c s l cap w rt fl) (.row k) = rowAt E r (.row k) := by
  unfold rowAt setHead; rw [Trie.get_insert, if_neg (by intro h; cases h)]

omit [Ord D] in
private theorem headFloor_setHead (E : Env D) (r : Rows D) (q : D) (rel' c s l cap w : Nat) (rt : Bool)
    (fl : Nat) (p : D) (rel : Nat) :
    headFloor E (setHead E r q rel' c s l cap w rt fl) p rel =
      if p = q ∧ rel = rel' then fl else headFloor E r p rel := by
  unfold headFloor setHead rowAt
  rw [Trie.get_insert]
  by_cases h : p = q ∧ rel = rel'
  · obtain ⟨rfl, rfl⟩ := h; simp
  · rw [if_neg (by intro he; injection he with h1 h2; exact h ⟨h1, h2⟩), if_neg h]

omit [Ord D] in
private theorem headFloor_insert_row (E : Env D) (r : Rows D) (k : RowKey D) (l : RowLeaf) (p : D) (rel : Nat) :
    headFloor E (r.insert (rowSpec E) (.row k) l) p rel = headFloor E r p rel := by
  unfold headFloor rowAt; rw [Trie.get_insert, if_neg (by intro h; cases h)]

omit [Ord D] in
private theorem rowAt_insert_row (E : Env D) (r : Rows D) (k' : RowKey D) (l : RowLeaf) (k : RowKey D) :
    rowAt E (r.insert (rowSpec E) (.row k') l) (.row k) = if k = k' then some l else rowAt E r (.row k) := by
  unfold rowAt; rw [Trie.get_insert]
  by_cases h : k = k'
  · subst h; simp
  · rw [if_neg (by intro he; injection he with he; exact h he), if_neg h]

omit [Ord D] in
/-- What the canonical erase of a row (`retainAt`, a retract) reads. -/
private theorem get_retain_row {E : Env D} {r : Rows D} (hr : Trie.Canon (rowSpec E) 0 r) (key' : RowKey D)
    (s : RowSlot D) :
    (Trie.retainAt (rowSpec E) (fun k _ => decide (k ≠ .row key')) (rowPath E (.row key')) r).get (rowSpec E) s =
      if s = .row key' then none else r.get (rowSpec E) s := by
  rw [Trie.get_retainAt (rowSpec E) _ _ hr]
  · by_cases h : s = .row key'
    · subst h; simp
    · rw [if_neg h]
      cases r.get (rowSpec E) s <;> simp [h]
  · intro p _ hq
    have : p.1 = .row key' := by simpa using hq
    rw [this]; exact under_rowPath E _

omit [Ord D] in
/-- A write of row `key'` with the relation's floor kept (an insert or an upsert): every slot moves
forward, given that the written leaf ranks above what the slot held. -/
private theorem mono_write {E : Env D} {r : Rows D} {key' : RowKey D} {L : RowLeaf} {c s l cap w : Nat} {rt : Bool}
    (hL : rk (rowAt E r (.row key')) (headFloor E r key'.parent key'.rel) <
      rk (some L) (headFloor E r key'.parent key'.rel)) (key : RowKey D) :
    Mono E r (setHead E (r.insert (rowSpec E) (.row key') L) key'.parent key'.rel c s l cap w rt
      (headFloor E r key'.parent key'.rel)) key := by
  have hf : headFloor E (setHead E (r.insert (rowSpec E) (.row key') L) key'.parent key'.rel c s l cap w rt
      (headFloor E r key'.parent key'.rel)) key.parent key.rel = headFloor E r key.parent key.rel := by
    rw [headFloor_setHead, headFloor_insert_row]
    split
    · rename_i h; rw [h.1, h.2]
    · rfl
  by_cases hk : key = key'
  · subst hk
    refine ⟨by rw [hf]; exact Nat.le_refl _, .inr ?_⟩
    unfold st
    rw [hf, rowAt_setHead_row, rowAt_insert_row, if_pos rfl]
    exact hL
  · exact mono_of_eq (by rw [rowAt_setHead_row, rowAt_insert_row, if_neg hk]) hf

omit [Ord D] in
/-- A retract of row `key'` (present, at version `u`): the floor rises past `u`, every slot moves
forward. -/
private theorem mono_retract {E : Env D} {r : Rows D} (hr : Trie.Canon (rowSpec E) 0 r) {key' : RowKey D}
    {a u : Nat} {val : ByteArray} (hcur : rowAt E r (.row key') = some (.row a val u)) {c s l cap w : Nat}
    {rt : Bool} (key : RowKey D) :
    Mono E r (setHead E (Trie.retainAt (rowSpec E) (fun k _ => decide (k ≠ .row key')) (rowPath E (.row key')) r)
      key'.parent key'.rel c s l cap w rt (max (headFloor E r key'.parent key'.rel) u + 1)) key := by
  have hrow : ∀ k, rowAt E (setHead E (Trie.retainAt (rowSpec E) (fun k _ => decide (k ≠ .row key'))
      (rowPath E (.row key')) r) key'.parent key'.rel c s l cap w rt
      (max (headFloor E r key'.parent key'.rel) u + 1)) (.row k) =
        if k = key' then none else rowAt E r (.row k) := by
    intro k
    rw [rowAt_setHead_row]
    unfold rowAt
    rw [get_retain_row hr]
    by_cases hk : k = key'
    · subst hk; simp
    · rw [if_neg (by intro he; injection he with he; exact hk he), if_neg hk]
  have hfl : ∀ p rel, headFloor E (Trie.retainAt (rowSpec E) (fun k _ => decide (k ≠ .row key'))
      (rowPath E (.row key')) r) p rel = headFloor E r p rel := by
    intro p rel
    unfold headFloor rowAt
    rw [get_retain_row hr, if_neg (by intro h; cases h)]
  unfold Mono st
  rw [headFloor_setHead, hfl, hrow]
  by_cases hrel : key.parent = key'.parent ∧ key.rel = key'.rel
  · rw [if_pos hrel]
    have hF : headFloor E r key.parent key.rel = headFloor E r key'.parent key'.rel := by rw [hrel.1, hrel.2]
    refine ⟨by rw [hF]; omega, ?_⟩
    by_cases hk : key = key'
    · subst hk
      rw [if_pos rfl, hcur]
      right; simp only [rk]; omega
    · rw [if_neg hk]
      cases ho : rowAt E r (.row key) with
      | none => right; simp only [rk]; omega
      | some lf => left; rfl
  · rw [if_neg hrel]
    have hk : key ≠ key' := by rintro rfl; exact hrel ⟨rfl, rfl⟩
    rw [if_neg hk]
    exact ⟨Nat.le_refl _, .inl rfl⟩

omit [Ord D] in
/-- A declare (of a relation with no head): every slot keeps its state. -/
private theorem mono_declare {E : Env D} {r : Rows D} {q : D} {rel' : Nat} (hn : rowAt E r (.head q rel') = none)
    {l cap w : Nat} {rt : Bool} (key : RowKey D) : Mono E r (setHead E r q rel' 0 0 l cap w rt 0) key := by
  refine mono_of_eq (rowAt_setHead_row ..) ?_
  rw [headFloor_setHead]
  split
  · rename_i h
    unfold headFloor
    rw [h.1, h.2, hn]
  · rfl

/-- **One row touch moves every row slot forward** and lowers no floor. -/
private theorem rowStep_mono {E : Env D} {w : World D} {t : Turn D} {r r' : Rows D} {x : RowTouch D}
    (hr : Trie.Canon (rowSpec E) 0 r) (h : rowStep E w t r x = .ok r') (key : RowKey D) : Mono E r r' key := by
  obtain ⟨slot, seen, act⟩ := x
  cases slot with
  | head q rel' =>
      cases act with
      | declare l cap w rt =>
          simp only [rowStep, rowStepOn, setHeadOn_trie, except_bind_ok] at h
          obtain ⟨⟨⟩, -, ⟨⟩, -, ⟨⟩, -, ⟨⟩, -, ⟨⟩, hn, h⟩ := h
          simp only [pure, Except.pure, Except.ok.injEq] at h
          subst h
          have hn' : rowAt E r (.head q rel') = none := by simpa using req_ok.mp hn
          exact mono_declare hn' key
      | keep => simp [rowStep, rowStepOn] at h
      | insert _ _ => simp [rowStep, rowStepOn] at h
      | upsert _ _ => simp [rowStep, rowStepOn] at h
      | retract => simp [rowStep, rowStepOn] at h
  | row key' =>
      simp only [rowStep, rowStepOn, headOfOn_trie, headFloorOn_trie, setHeadOn_trie, except_bind_ok] at h
      obtain ⟨⟨⟩, -, ⟨⟩, -, ⟨⟩, -, h⟩ := h
      rcases hh : headOf E r key'.parent key'.rel with _ | ⟨count, sum, limit, cap, width, retract⟩
      · rw [hh] at h; cases h
      · rw [hh] at h
        simp only [except_bind_ok] at h
        obtain ⟨⟨⟩, -, h⟩ := h
        cases act with
        | keep =>
            simp only [except_bind_ok] at h
            obtain ⟨_, -, h⟩ := h
            simp only [pure, Except.pure, Except.ok.injEq] at h
            subst h; exact mono_refl E r key
        | insert amt v =>
            simp only [except_bind_ok] at h
            obtain ⟨⟨⟩, -, ⟨⟩, hcur, ⟨⟩, -, ⟨⟩, -, ⟨⟩, -, h⟩ := h
            simp only [pure, Except.pure, Except.ok.injEq] at h
            subst h
            have hn : rowAt E r (.row key') = none := by simpa using req_ok.mp hcur
            refine mono_write ?_ key
            rw [hn]; simp only [rk]; omega
        | upsert amt v =>
            simp only [except_bind_ok] at h
            obtain ⟨_, -, ⟨⟩, -, ⟨⟩, -, ⟨⟩, -, ⟨⟩, -, h⟩ := h
            simp only [pure, Except.pure, Except.ok.injEq] at h
            subst h
            refine mono_write ?_ key
            rcases rowAt E r (.row key') with _ | (⟨⟩ | ⟨a, val, u⟩) <;> simp only [rk] <;> omega
        | retract =>
            simp only [except_bind_ok] at h
            obtain ⟨_, -, ⟨⟩, -, h⟩ := h
            rcases hc : rowAt E r (.row key') with _ | (⟨⟩ | ⟨a, val, u⟩)
            · rw [hc] at h; cases h
            · rw [hc] at h; cases h
            · rw [hc] at h
              simp only [except_bind_ok] at h
              obtain ⟨⟨⟩, -, h⟩ := h
              simp only [pure, Except.pure, Except.ok.injEq] at h
              subst h
              exact mono_retract hr hc key
        | declare _ _ _ _ => simp at h

/-- Every row touch of a turn, in order, moves every slot forward. -/
private theorem foldRows_mono {E : Env D} {w : World D} {t : Turn D} (key : RowKey D) :
    ∀ (l : List (RowTouch D)) (acc rr : Rows D × Nat), Trie.Canon (rowSpec E) 0 acc.1 →
      l.foldlM (rowStepFreed E w t) acc = .ok rr → Mono E acc.1 rr.1 key
  | [], acc, rr, _, h => by
      simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h
      subst h; exact mono_refl E _ key
  | x :: rest, acc, rr, hc, h => by
      rw [List.foldlM_cons, except_bind_ok] at h
      obtain ⟨acc', h1, h2⟩ := h
      unfold rowStepFreed rowStepFreedOn at h1; simp only [rowStepOn_trie, rowFreedOn_trie] at h1
      rw [except_bind_ok] at h1
      obtain ⟨r1, hs, he⟩ := h1
      simp only [pure, Except.pure, Except.ok.injEq] at he
      subst he
      exact mono_trans (rowStep_mono hc hs key) (foldRows_mono key rest _ rr (rowStep_weight hc hs).2 h2)

/-- **A turn none of whose touches retires the slot's parent moves the slot forward**: its row
touches do (`foldRows_mono`), and `dropHeads` drops only retired parents' heads. -/
private theorem admit_rowsMono {E : Env D} {w w' : World D} {t : Turn D} (hr : w.RowsCanon E)
    (h : World.admit E w t = .ok w') (key : RowKey D)
    (hnr : ∀ x ∈ t.touches, x.act = .retire → x.cell ≠ key.parent) : Mono E w.rows w'.rows key := by
  obtain ⟨posts, hk, hrows⟩ := admit_rows h
  have hrun := hk.rows
  rw [rowsRun_eq] at hrun
  simp only [except_bind_ok] at hrun
  obtain ⟨⟨⟩, -, ⟨⟩, -, hrun⟩ := hrun
  split at hrun
  · cases hrun
  · simp only [except_bind_ok] at hrun
    obtain ⟨acc, hf, hd⟩ := hrun
    simp only [pure, Except.pure, Except.ok.injEq] at hd
    have hm := foldRows_mono key t.rows (w.rows, 0) acc hr hf
    have hca := (foldRows_weight t.rows (w.rows, 0) acc hr hf).2
    have hget : ∀ s, (∀ x ∈ t.touches, x.act = .retire → ∀ rel, s ≠ .head x.cell rel) →
        w'.rows.get (rowSpec E) s = acc.1.get (rowSpec E) s := by
      intro s hs; rw [hrows, ← hd]; exact dropHeads_get_out t hs acc hca
    refine mono_trans hm (mono_of_eq ?_ ?_)
    · unfold rowAt; exact hget _ (fun _ _ _ _ he => by cases he)
    · unfold headFloor rowAt
      rw [hget _ (fun x hx hret rel he => hnr x hx hret (by injection he with h1; exact h1.symm))]

private theorem eAdv_tomb {b : Option Entry} : ¬ EAdv (some .tomb) b := by
  rcases b with _ | (⟨_, _⟩ | _) <;> simp [EAdv]

/-- **Along a fold that leaves the parent untombed, every slot under it moves forward**, given that
a turn retiring the parent tombs it (`hkill`; `admit_retire_tomb` under a lawful `Ord`). A tombstone
is for ever, so no turn along the way retired the parent. -/
private theorem fold_rowsMono {E : Env D} (key : RowKey D)
    (hkill : ∀ {v v' : World D} {t : Turn D}, World.admit E v t = .ok v' →
      v'.entry E key.parent ≠ some .tomb → ∀ x ∈ t.touches, x.act = .retire → x.cell ≠ key.parent) :
    ∀ {w w' : World D} {l : List (Step D)}, w.RowsCanon E → World.fold E w l = .ok w' →
      w'.entry E key.parent ≠ some .tomb → Mono E w.rows w'.rows key
  | w, w', [], _, h, _ => by
      simp only [World.fold, Except.ok.injEq] at h
      subst h; exact mono_refl E _ key
  | w, w', s :: rest, hr, h, ht => by
      obtain ⟨w1, h1, h2⟩ := fold_cons_ok.mp h
      have ht1 : w1.entry E key.parent ≠ some .tomb := by
        intro h1t
        rcases fold_entryStep key.parent h2 with he | hadv
        · exact ht (he ▸ h1t)
        · rw [h1t] at hadv; exact eAdv_tomb hadv
      cases s with
      | turn t =>
          exact mono_trans (admit_rowsMono hr h1 key (hkill h1 ht1))
            (fold_rowsMono key hkill (admit_rowsCanon hr h1) h2 ht)
      | refusal r =>
          exact mono_trans (mono_of_eq (by rw [refuse_rows h1]) (by rw [refuse_rows h1]))
            (fold_rowsMono key hkill (refuse_rowsCanon hr h1) h2 ht)

/-! ### A turn that retires a cell tombs it (under a lawful `Ord`)

`checkShape` refuses a turn touching one cell twice through `firstDup`, which detects a duplicate
only when `compare` is lawful (`firstDup_none`). Under an `Ord` that never answers `.eq`, a turn
`[retire c, write c]` passes, `dropHeads` drops `c`'s heads, and the write leaves `c` live: its
relations' floors read 0 again with `c` alive. So the rows half needs `Std.TransOrd D` and
`Std.LawfulEqOrd D`, which the deployed digest has. -/

private theorem touchCheck_retire {E : Env D} {w : World D} {x : Touch D} {r : Option (Post D)}
    (h : touchCheck E w x = .ok r) (hret : x.act = .retire) : ∃ p, r = some p ∧ p.entry = .tomb := by
  unfold touchCheck at h
  simp only [except_bind_ok] at h
  obtain ⟨⟨⟩, -, h⟩ := h
  revert h
  generalize w.entry E x.cell = cur
  intro h
  rw [hret] at h
  rcases cur with _ | (⟨cell, ver⟩ | _)
  · cases h
  · simp only [except_bind_ok] at h
    obtain ⟨⟨⟩, -, hp⟩ := h
    simp only [pure, Except.pure, Except.ok.injEq] at hp
    exact ⟨_, hp.symm, rfl⟩
  · cases h

/-- **Under a lawful `Ord`, a turn that retires a cell leaves its tombstone.** -/
private theorem admit_retire_tomb [Std.TransOrd D] [Std.LawfulEqOrd D] {E : Env D} {w w' : World D}
    {t : Turn D} (h : World.admit E w t = .ok w') {x : Touch D} (hx : x ∈ t.touches)
    (hret : x.act = .retire) : w'.entry E x.cell = some .tomb := by
  obtain ⟨posts, hk, rfl⟩ := admit_ok h
  have hshape := hk.shape
  unfold checkShape at hshape
  simp only [except_bind_ok] at hshape
  obtain ⟨⟨⟩, hnd, -⟩ := hshape
  have hnd' : (t.touches.map Touch.cell).Nodup := firstDup_none (noDup_none hnd)
  have hcr := hk.creates
  unfold checkCreates at hcr
  simp only [except_bind_ok] at hcr
  obtain ⟨⟨⟩, -, ⟨⟩, -, ⟨⟩, hbt, -⟩ := hcr
  have hbt' := firstDup_none (noDup_none hbt)
  have hnb : x.cell ∉ (bornEntries t).map Prod.fst := by
    intro hm
    have hm' : x.cell ∈ createdIds t := by simpa [bornEntries, createdIds] using hm
    exact (List.nodup_append.mp hbt').2.2 x.cell (List.mem_map_of_mem hx) x.cell hm' rfl
  obtain ⟨raw, hm, hpe⟩ := hk.touches
  obtain ⟨rx, hrx, hfx⟩ := mapEx_fwd hm x hx
  obtain ⟨px, rfl, hpx⟩ := touchCheck_retire hfx hret
  have hpxc : px.cell = x.cell := (touchCheck_adv hfx).1
  have hpxin : px ∈ posts := by rw [hpe]; simpa [List.reduceOption, List.mem_filterMap] using hrx
  have hmem : x.cell ∈ (posts.map Post.pair).map Prod.fst := by
    rw [List.map_map]; exact List.mem_map.mpr ⟨px, hpxin, hpxc⟩
  unfold World.entry
  show (match (commitTrie E w t posts).get (trieSpec E) (.cell x.cell) with
    | some (.entry e) => some e
    | _ => none) = _
  rw [commitTrie_cell, insertAll_get_of_not_mem hnb]
  obtain ⟨e, he, hg⟩ := insertAll_get_mem (E := E) (m := w.trie) hmem
  rw [hg]
  obtain ⟨p, hpm, hpe'⟩ := List.mem_map.mp he
  simp only [Post.pair, Prod.mk.injEq] at hpe'
  obtain ⟨hpc, rfl⟩ := hpe'
  rw [hpe] at hpm
  have hp' : some p ∈ raw := by simpa [List.reduceOption, List.mem_filterMap] using hpm
  obtain ⟨y, hy, hfy⟩ := mapEx_mem hm (some p) hp'
  have hyc : p.cell = y.cell := (touchCheck_adv hfy).1
  have hxy : y = x := eq_of_nodup_map hnd' hy hx (by rw [← hyc, hpc])
  subst hxy
  rw [hfx] at hfy
  simp only [Except.ok.injEq, Option.some.injEq] at hfy
  simp only [← hfy, hpx]

/-! ### Row pins: two different states pin differently -/

omit [Ord D] [DecidableEq D] in
private theorem rowPin_of_ps (E : Env D) {o o' : Option RowLeaf} {f f' : Nat} (h : PS o f = PS o' f') :
    rowPin E f o = rowPin E f' o' := by
  rcases o with _ | l <;> rcases o' with _ | l' <;>
    simp only [PS, Prod.mk.injEq, Option.some.injEq, reduceCtorEq, false_and, true_and, and_true] at h
  · rw [h]
  · rw [h]; rfl

/-- A slot's state fits what the pins spell: the floor and a row leaf's counters in eight bytes each,
the value within `Bounds.valueBytesMax`. -/
private def SFit (a : Option RowLeaf × Nat) : Prop :=
  a.2 < 2 ^ 64 ∧ ∀ l, a.1 = some l → ∃ amt val ver, l = .row amt val ver ∧ amt < 2 ^ 64 ∧ ver < 2 ^ 64 ∧
    val.size ≤ Bounds.valueBytesMax

omit [Ord D] in
private theorem rowFits_get {E : Env D} {r : Rows D} (hr : Trie.Canon (rowSpec E) 0 r)
    (hfit : ∀ p ∈ r.toList, rowFits p.1 p.2 = true) {s : RowSlot D} {l : RowLeaf}
    (h : rowAt E r s = some l) : rowFits s l = true :=
  hfit (s, l) ((Trie.mem_toList (rowSpec E) 0 r hr.1 s l).mpr h)

omit [Ord D] in
private theorem sFit_of_fits {E : Env D} {r : Rows D} (hr : Trie.Canon (rowSpec E) 0 r)
    (hfit : ∀ p ∈ r.toList, rowFits p.1 p.2 = true) (key : RowKey D) : SFit (st E r key) := by
  refine ⟨?_, ?_⟩
  · show headFloor E r key.parent key.rel < 2 ^ 64
    unfold headFloor
    cases hh : rowAt E r (.head key.parent key.rel) with
    | none => simp
    | some l =>
        cases l with
        | head c s lim cap wd rt fl =>
            have := rowFits_get hr hfit hh
            simp only [rowFits, Bool.and_eq_true, decide_eq_true_eq] at this
            rw [← counterLimit_eq]; exact this.2
        | row _ _ _ => simp
  · intro l hl
    have := rowFits_get hr hfit hl
    cases l with
    | head c s lim cap wd rt fl => simp [rowFits] at this
    | row amt val ver =>
        simp only [rowFits, Bool.and_eq_true, decide_eq_true_eq] at this
        obtain ⟨⟨⟨⟨-, -⟩, ha⟩, hs⟩, hv⟩ := this
        rw [counterLimit_eq] at ha hv
        exact ⟨amt, val, ver, rfl, ha, hv, hs⟩

private theorem rowLeafBytes_row_inj {amt val ver amt' val' ver'} (ha : amt < 2 ^ 64) (ha' : amt' < 2 ^ 64)
    (hv : ver < 2 ^ 64) (hv' : ver' < 2 ^ 64) (hs : val.size ≤ Bounds.valueBytesMax)
    (hs' : val'.size ≤ Bounds.valueBytesMax)
    (h : rowLeafBytes (.row amt val ver) = rowLeafBytes (.row amt' val' ver')) :
    RowLeaf.row amt val ver = .row amt' val' ver' := by
  simp only [rowLeafBytes] at h
  obtain ⟨h12, hval⟩ := bytes_append_inj h (by simp [byte8, nat64_size])
  obtain ⟨h1, hver⟩ := bytes_append_inj h12 (by simp [byte8, nat64_size])
  obtain ⟨-, hamt⟩ := bytes_append_inj h1 (by simp [byte8])
  rw [Nanodregg.Codec.Stream.nat64_lawfulOn.bytes_injective ha ha' hamt,
    Nanodregg.Codec.Stream.nat64_lawfulOn.bytes_injective hv hv' hver,
    (Nanodregg.Codec.Stream.rawBytes_lawfulOn _ (by decide)).bytes_injective hs hs' hval]

omit [Ord D] [DecidableEq D] in
theorem rowPin_eq_pre (E : Env D) (floor : Nat) (o : Option RowLeaf) :
    rowPin E floor o = E.hash (rowPre floor o).1 (rowPre floor o).2 := by
  cases o <;> rfl

/-- **Two different slot states (both fitting) have different pin inputs**: an absent slot's and a
present one's are two domains, two floors differ in eight bytes, two row leaves in their bytes. -/
private theorem rowPre_ps_ne {a b : Option RowLeaf × Nat} (ha : SFit a) (hb : SFit b)
    (hne : PS a.1 a.2 ≠ PS b.1 b.2) : rowPre b.2 b.1 ≠ rowPre a.2 a.1 := by
  obtain ⟨oa, fa⟩ := a
  obtain ⟨ob, fb⟩ := b
  obtain ⟨hfa, hla⟩ := ha
  obtain ⟨hfb, hlb⟩ := hb
  simp only at hfa hla hfb hlb hne ⊢
  rcases oa with _ | la <;> rcases ob with _ | lb
  · have hf : fa ≠ fb := fun h => hne (by rw [h])
    intro h
    simp only [rowPre, Prod.mk.injEq] at h
    exact hf (Nanodregg.Codec.Stream.nat64_lawfulOn.bytes_injective hfb hfa h.2).symm
  · intro h; have h1 := congrArg Prod.fst h; simp only [rowPre] at h1; exact absurd h1 (by decide)
  · intro h; have h1 := congrArg Prod.fst h; simp only [rowPre] at h1; exact absurd h1 (by decide)
  · have hl : la ≠ lb := fun h => hne (by rw [h]; rfl)
    obtain ⟨amt, val, ver, rfl, h1, h2, h3⟩ := hla _ rfl
    obtain ⟨amt', val', ver', rfl, h1', h2', h3'⟩ := hlb _ rfl
    intro h
    simp only [rowPre, Prod.mk.injEq] at h
    exact hl (rowLeafBytes_row_inj h1' h1 h2' h2 h3' h3 h.2).symm

/-- A tombstone at the end of a stretch of the fold was a tombstone all along from where it first
appears: if the end is not one, no World before it was. -/
private theorem not_tomb_before {E : Env D} {w w' : World D} {l : List (Step D)}
    (h : World.fold E w l = .ok w') {c : D} (ht : w'.entry E c ≠ some .tomb) : w.entry E c ≠ some .tomb := by
  intro h0
  rcases fold_entryStep c h with he | hadv
  · exact ht (he ▸ h0)
  · rw [h0] at hadv; exact eAdv_tomb hadv

/-- **A row pin observed on the fold and stale now is stale for ever**, or the row's parent is retired (its entry a tombstone)
(then every row touch under it is refused before its pin is read, for ever), or the hash collides on
the two row-pin inputs compared, `w₀`'s and `w'`'s (they differ: the slot has moved strictly
forward). Under a lawful `Ord D`: with one that never answers `.eq`, `checkShape` admits
`[retire p, write p]`, `dropHeads` resets `p`'s floor and `p` stays live, so the old pin recurs. -/
theorem row_stale_behind_forever [Std.TransOrd D] [Std.LawfulEqOrd D] {E : Env D} {n : Nat}
    (hE : E.Lawful n) {w₀ w w' : World D}
    {l₁ l₂ : List (Step D)} (hr : w₀.RowsCanon E) (hok : w₀.RowsOk E)
    (h₁ : World.fold E w₀ l₁ = .ok w) (h₂ : World.fold E w l₂ = .ok w') {key : RowKey D}
    (hstale : rowPin E (headFloor E w.rows key.parent key.rel) (rowAt E w.rows (.row key)) ≠
      rowPin E (headFloor E w₀.rows key.parent key.rel) (rowAt E w₀.rows (.row key))) :
    rowPin E (headFloor E w'.rows key.parent key.rel) (rowAt E w'.rows (.row key)) ≠
        rowPin E (headFloor E w₀.rows key.parent key.rel) (rowAt E w₀.rows (.row key)) ∨
      w'.entry E key.parent = some .tomb ∨
      CollidesAmong E.hash [rowPre (headFloor E w₀.rows key.parent key.rel) (rowAt E w₀.rows (.row key)),
        rowPre (headFloor E w'.rows key.parent key.rel) (rowAt E w'.rows (.row key))] := by
  by_cases hl : w'.entry E key.parent = some .tomb
  · exact .inr (.inl hl)
  have ht' : w'.entry E key.parent ≠ some .tomb := hl
  have ht := not_tomb_before h₂ ht'
  have hkill : ∀ {v v' : World D} {t : Turn D}, World.admit E v t = .ok v' →
      v'.entry E key.parent ≠ some .tomb → ∀ x ∈ t.touches, x.act = .retire → x.cell ≠ key.parent :=
    fun h hn x hx hret hc => hn (hc ▸ admit_retire_tomb h hx hret)
  have hm₁ := fold_rowsMono key hkill hr h₁ ht
  have hm₂ := fold_rowsMono key hkill (fold_rowsCanon hr h₁) h₂ ht'
  have hps : PS (st E w₀.rows key).1 (st E w₀.rows key).2 ≠ PS (st E w.rows key).1 (st E w.rows key).2 :=
    fun h => hstale (rowPin_of_ps E h).symm
  have hlt : rk (st E w₀.rows key).1 (st E w₀.rows key).2 < rk (st E w'.rows key).1 (st E w'.rows key).2 := by
    rcases hm₁.2 with h | h
    · exact absurd h hps
    · rcases hm₂.2 with h' | h'
      · rw [← rk_of_ps h']; exact h
      · omega
  have hne : PS (st E w₀.rows key).1 (st E w₀.rows key).2 ≠ PS (st E w'.rows key).1 (st E w'.rows key).2 :=
    fun h => by have := rk_of_ps h; omega
  have hr' := fold_rowsCanon (fold_rowsCanon hr h₁) h₂
  have hok' := fold_rowsOk hE (fold_rowsCanon hr h₁) (fold_rowsOk hE hr hok h₁) h₂
  have hpre := rowPre_ps_ne (sFit_of_fits hr hok.1 key) (sFit_of_fits hr' hok'.1 key) hne
  by_cases hp : rowPin E (headFloor E w'.rows key.parent key.rel) (rowAt E w'.rows (.row key)) =
      rowPin E (headFloor E w₀.rows key.parent key.rel) (rowAt E w₀.rows (.row key))
  · exact .inr (.inr ⟨_, List.mem_cons_self, _, List.mem_cons_of_mem _ List.mem_cons_self,
      fun h => hpre h.symm, (rowPin_eq_pre E _ _).symm.trans (hp.symm.trans (rowPin_eq_pre E _ _))⟩)
  · exact .inl hp

/-! ## Ranges: a listing and its floor never return together

Under a range prefix (`pre.size ≤ width`, what `checkRanges` admits; any relation and width,
cv 01a14f7e), every listed row is a row of the relation (`listed`), so its floor is the range's. If the range pin at `w'` equals
`w₀`'s, the floor and the listing are `w₀`'s (one domain, `rangePin_dec`); the floor is monotone, so it
was the same all along, and with the floor fixed each row slot only moves forward: a slot that moved
by `w` has not come back at `w'`, so neither has the listing. -/

/-- A listed entry: a row of the relation, at the relation's width, its leaf fitting. -/
private def Listed (parent : D) (rel width : Nat) (p : RowSlot D × RowLeaf) : Prop :=
  ∃ k amt val ver, p = (.row ⟨parent, rel, k⟩, .row amt val ver) ∧ k.size = width ∧ amt < 2 ^ 64 ∧
    ver < 2 ^ 64 ∧ val.size ≤ Bounds.valueBytesMax

omit [Ord D] in
private theorem listed {E : Env D} {n : Nat} (hsize : ∀ d, (E.bytes d).size = n)
    (hinj : Function.Injective E.bytes) {r : Rows D} (hc : Trie.Canon (rowSpec E) 0 r)
    (hfit : ∀ p ∈ r.toList, rowFits p.1 p.2 = true) {parent : D} {rel width : Nat} {pre : ByteArray}
    (hw : pre.size ≤ width) {most : Nat}
    {l : List (RowSlot D × RowLeaf)} (h : rangeRows E r parent rel width pre most = some l) :
    ∀ p ∈ l, Listed parent rel width p := by
  intro ⟨s, v⟩ hp
  obtain ⟨hg, hs⟩ := (range_rows_mem hsize hc hw h s v).mp hp
  have hf := rowFits_get hc hfit hg
  obtain ⟨k, rfl, hk⟩ := listed_key E hsize hinj hs
  cases v with
  | head c s lim cap wd rt fl => simp [rowFits] at hf
  | row amt val ver =>
      simp only [rowFits, Bool.and_eq_true, decide_eq_true_eq] at hf
      obtain ⟨⟨⟨⟨-, -⟩, ha⟩, hsz⟩, hv⟩ := hf
      rw [counterLimit_eq] at ha hv
      exact ⟨k, amt, val, ver, rfl, hk, ha, hv, hsz⟩

/-- The listing's bytes in `rangePinBytes`. -/
private def listBytes (E : Env D) (l : List (RowSlot D × RowLeaf)) : ByteArray :=
  l.foldl (fun acc p => acc ++ rowKeyBytes E p.1 ++ E.bytes (rowDigest E p.2)) ByteArray.empty

omit [Ord D] [DecidableEq D] in
private theorem foldl_shift (E : Env D) :
    ∀ (l : List (RowSlot D × RowLeaf)) (a : ByteArray),
      l.foldl (fun acc p => acc ++ rowKeyBytes E p.1 ++ E.bytes (rowDigest E p.2)) a = a ++ listBytes E l
  | [], a => by simp [listBytes]
  | p :: l, a => by
      unfold listBytes
      simp only [List.foldl_cons]
      rw [foldl_shift E l, foldl_shift E l (ByteArray.empty ++ rowKeyBytes E p.1 ++ E.bytes (rowDigest E p.2))]
      simp [ByteArray.append_assoc]

omit [Ord D] [DecidableEq D] in
private theorem listBytes_cons (E : Env D) (p : RowSlot D × RowLeaf) (l : List (RowSlot D × RowLeaf)) :
    listBytes E (p :: l) = (rowKeyBytes E p.1 ++ E.bytes (rowDigest E p.2)) ++ listBytes E l := by
  conv => lhs; unfold listBytes
  simp only [List.foldl_cons]
  rw [foldl_shift]
  simp

omit [Ord D] [DecidableEq D] in
private theorem listBytes_size {E : Env D} {n : Nat} (hsize : ∀ d, (E.bytes d).size = n) {parent : D}
    {rel width : Nat} : ∀ {l : List (RowSlot D × RowLeaf)}, (∀ p ∈ l, Listed parent rel width p) →
      (listBytes E l).size = l.length * (n + (natBytes rel).size + 1 + (natBytes width).size + width + n)
  | [], _ => by simp [listBytes]
  | p :: l, h => by
      rw [listBytes_cons, ByteArray.size_append, listBytes_size hsize (fun q hq => h q (List.mem_cons_of_mem _ hq))]
      obtain ⟨k, amt, val, ver, rfl, hk, -⟩ := h p List.mem_cons_self
      simp only [rowKeyBytes, rowsPrefix, ByteArray.size_append, byte8_size, hsize, hk, List.length_cons,
        Nat.succ_mul]
      omega

omit [Ord D] [DecidableEq D] in
theorem leafPres_cons (p : RowSlot D × RowLeaf) (l : List (RowSlot D × RowLeaf)) :
    leafPres (p :: l) = (domRowLeaf, rowLeafBytes p.2) :: leafPres l := rfl

omit [DecidableEq D] in
/-- **The listing's bytes determine the listing**, or the hash collides on two of the listings'
leaf inputs (in `domRowLeaf`). -/
private theorem listBytes_inj {E : Env D} {n : Nat} (hE : E.Lawful n) {parent : D} {rel width : Nat} :
    ∀ {l l' : List (RowSlot D × RowLeaf)}, (∀ p ∈ l, Listed parent rel width p) →
      (∀ p ∈ l', Listed parent rel width p) → listBytes E l = listBytes E l' →
        l = l' ∨ CollidesAmong E.hash (leafPres l ++ leafPres l')
  | [], [], _, _, _ => .inl rfl
  | [], q :: l', _, h', he => by
      have := congrArg ByteArray.size he
      rw [listBytes_size hE.size h'] at this
      have h0 : (listBytes E ([] : List (RowSlot D × RowLeaf))).size = 0 := rfl
      rw [h0, List.length_cons, Nat.succ_mul] at this
      generalize l'.length * (n + (natBytes rel).size + 1 + (natBytes width).size + width + n) = A at this
      omega
  | p :: l, [], h, _, he => by
      have := congrArg ByteArray.size he
      rw [listBytes_size hE.size h] at this
      have h0 : (listBytes E ([] : List (RowSlot D × RowLeaf))).size = 0 := rfl
      rw [h0, List.length_cons, Nat.succ_mul] at this
      generalize l.length * (n + (natBytes rel).size + 1 + (natBytes width).size + width + n) = A at this
      omega
  | p :: l, q :: l', h, h', he => by
      obtain ⟨k, amt, val, ver, rfl, hk, ha, hv, hs⟩ := h p List.mem_cons_self
      obtain ⟨k', amt', val', ver', rfl, hk', ha', hv', hs'⟩ := h' q List.mem_cons_self
      rw [listBytes_cons, listBytes_cons] at he
      obtain ⟨hb, hrest⟩ := bytes_append_inj he (by simp [rowKeyBytes, rowsPrefix, byte8, hE.size, hk, hk'])
      obtain ⟨hkb, hdb⟩ := bytes_append_inj hb (by simp [rowKeyBytes, rowsPrefix, byte8, hE.size, hk, hk'])
      have hkk : k = k' := by
        simp only [rowKeyBytes, hk, hk'] at hkb
        exact (ByteArray.append_right_inj _).mp hkb
      have hd := hE.bytes_inj hdb
      rcases listBytes_inj hE (fun x hx => h x (List.mem_cons_of_mem _ hx))
          (fun x hx => h' x (List.mem_cons_of_mem _ hx)) hrest with hl | hc
      · by_cases hlb : rowLeafBytes (.row amt val ver) = rowLeafBytes (.row amt' val' ver')
        · have := rowLeafBytes_row_inj ha ha' hv hv' hs hs' hlb
          subst hkk; rw [this, hl]; exact .inl rfl
        · exact .inr ⟨_, List.mem_append.mpr (.inl List.mem_cons_self), _,
            List.mem_append.mpr (.inr List.mem_cons_self), fun h => hlb (congrArg Prod.snd h), hd⟩
      · exact .inr (hc.mono fun x hx => (List.mem_append.mp hx).elim
          (fun h => List.mem_append.mpr (.inl (List.mem_cons_of_mem _ h)))
          (fun h => List.mem_append.mpr (.inr (List.mem_cons_of_mem _ h))))

omit [Ord D] [DecidableEq D] in
private theorem nat32_size (k : Nat) : (Nanodregg.Codec.Stream.nat32.bytes k).size = 4 := by
  rw [Nanodregg.Codec.Stream.nat32_bytes, Nanodregg.Codec.Stream.u32_bytes]; rfl

omit [DecidableEq D] in
/-- **A range pin's bytes determine its floor and listing** (both fitting), or the hash collides. -/
private theorem rangePin_dec {E : Env D} {n : Nat} (hE : E.Lawful n) {parent : D} {rel width : Nat}
    {pre : ByteArray} {f f' : Nat} {l l' : List (RowSlot D × RowLeaf)} (hf : f < 2 ^ 64) (hf' : f' < 2 ^ 64)
    (hl : ∀ p ∈ l, Listed parent rel width p) (hl' : ∀ p ∈ l', Listed parent rel width p)
    (h : rangePinBytes E parent rel width pre f l = rangePinBytes E parent rel width pre f' l') :
    (f = f' ∧ l = l') ∨ CollidesAmong E.hash (leafPres l ++ leafPres l') := by
  unfold rangePinBytes at h
  rw [foldl_shift, foldl_shift] at h
  simp only [ByteArray.empty_append] at h
  obtain ⟨h1, hx⟩ := bytes_append_inj h (by simp only [ByteArray.size_append, nat64_size, nat32_size])
  obtain ⟨h2, -⟩ := bytes_append_inj h1 (by simp only [ByteArray.size_append, nat64_size])
  obtain ⟨-, hfl⟩ := bytes_append_inj h2 rfl
  rcases listBytes_inj hE hl hl' hx with he | hc
  · exact .inl ⟨Nanodregg.Codec.Stream.nat64_lawfulOn.bytes_injective hf hf' hfl, he⟩
  · exact .inr hc

omit [Ord D] [DecidableEq D] in
/-- Two lists strictly sorted by one asymmetric relation, with the same members, are equal. -/
private theorem pairwise_ext {α : Type} {R : α → α → Prop} (hasym : ∀ a b, R a b → ¬ R b a) :
    ∀ {l l' : List α}, l.Pairwise R → l'.Pairwise R → (∀ x, x ∈ l ↔ x ∈ l') → l = l'
  | [], [], _, _, _ => rfl
  | [], b :: _, _, _, hm => absurd ((hm b).mpr List.mem_cons_self) (by simp)
  | a :: _, [], _, _, hm => absurd ((hm a).mp List.mem_cons_self) (by simp)
  | a :: l, b :: l', hp, hp', hm => by
      rw [List.pairwise_cons] at hp hp'
      have hab : a = b := by
        rcases List.mem_cons.mp ((hm a).mp List.mem_cons_self) with h | h
        · exact h
        · rcases List.mem_cons.mp ((hm b).mpr List.mem_cons_self) with h' | h'
          · exact h'.symm
          · exact absurd (hp.1 b h') (hasym _ _ (hp'.1 a h))
      subst hab
      have ht : ∀ x, x ∈ l ↔ x ∈ l' := by
        intro x
        constructor
        · intro hx
          rcases List.mem_cons.mp ((hm x).mp (List.mem_cons_of_mem _ hx)) with h | h
          · subst h; exact absurd (hp.1 _ hx) (fun hr => hasym _ _ hr hr)
          · exact h
        · intro hx
          rcases List.mem_cons.mp ((hm x).mpr (List.mem_cons_of_mem _ hx)) with h | h
          · subst h; exact absurd (hp'.1 _ hx) (fun hr => hasym _ _ hr hr)
          · exact h
      rw [pairwise_ext hasym hp.2 hp'.2 ht]

omit [Ord D] [DecidableEq D] in
private theorem ps_floor {o o' : Option RowLeaf} {f : Nat} : PS o f = PS o' f ↔ o = o' := by
  rcases o with _ | l <;> rcases o' with _ | l' <;> simp [PS]

/-- **A range pin observed on the fold and stale now is stale for ever**, or the parent is retired (its entry a tombstone), or
the hash collides among the inputs compared: the two range-pin inputs (`w₀`'s and `w'`'s) and the
leaf inputs of both listings (a range pin embeds its rows' leaf digests). The listing under a prefix
(each row's leaf digest with its version) and the relation's floor never return together to what
`w₀` held. Under a lawful `Ord D` (as for rows), at a range with `pre.size ≤ width`, any relation and
width (cv 01a14f7e removed `rel < 256` and `width < 256`: under the one-byte encoding relation 259's
listing was relation 3's while its floor was relation 259's, 0 for ever). -/
theorem range_stale_behind_forever [Std.TransOrd D] [Std.LawfulEqOrd D] {E : Env D} {n : Nat}
    (hE : E.Lawful n) {w₀ w w' : World D}
    {l₁ l₂ : List (Step D)} (hr : w₀.RowsCanon E) (hok : w₀.RowsOk E)
    (h₁ : World.fold E w₀ l₁ = .ok w) (h₂ : World.fold E w l₂ = .ok w')
    {parent : D} {rel width most : Nat} {pre : ByteArray} {l₀ l l' : List (RowSlot D × RowLeaf)}
    (hwd : pre.size ≤ width)
    (h0 : rangeRows E w₀.rows parent rel width pre most = some l₀)
    (hw : rangeRows E w.rows parent rel width pre most = some l)
    (hw' : rangeRows E w'.rows parent rel width pre most = some l')
    (hstale : rangePin E parent rel width pre (headFloor E w.rows parent rel) l ≠
      rangePin E parent rel width pre (headFloor E w₀.rows parent rel) l₀) :
    rangePin E parent rel width pre (headFloor E w'.rows parent rel) l' ≠
        rangePin E parent rel width pre (headFloor E w₀.rows parent rel) l₀ ∨
      w'.entry E parent = some .tomb ∨
      CollidesAmong E.hash (rangePre E parent rel width pre (headFloor E w₀.rows parent rel) l₀ ::
        rangePre E parent rel width pre (headFloor E w'.rows parent rel) l' :: (leafPres l₀ ++ leafPres l')) := by
  by_cases hl : w'.entry E parent = some .tomb
  · exact .inr (.inl hl)
  have ht' : w'.entry E parent ≠ some .tomb := hl
  have ht := not_tomb_before h₂ ht'
  have hrw := fold_rowsCanon hr h₁
  have hokw := fold_rowsOk hE hr hok h₁
  have hr' := fold_rowsCanon hrw h₂
  have hok' := fold_rowsOk hE hrw hokw h₂
  have hkill : ∀ (key : RowKey D), key.parent = parent → ∀ {v v' : World D} {t : Turn D},
      World.admit E v t = .ok v' → v'.entry E key.parent ≠ some .tomb →
        ∀ x ∈ t.touches, x.act = .retire → x.cell ≠ key.parent :=
    fun _ _ _ _ _ h hn x hx hret hc => hn (hc ▸ admit_retire_tomb h hx hret)
  have hm₁ : ∀ key : RowKey D, key.parent = parent → Mono E w₀.rows w.rows key :=
    fun key hp => fold_rowsMono key (hkill key hp) hr h₁ (by rw [hp]; exact ht)
  have hm₂ : ∀ key : RowKey D, key.parent = parent → Mono E w.rows w'.rows key :=
    fun key hp => fold_rowsMono key (hkill key hp) hrw h₂ (by rw [hp]; exact ht')
  have hF₁ := (hm₁ ⟨parent, rel, ByteArray.empty⟩ rfl).1
  have hF₂ := (hm₂ ⟨parent, rel, ByteArray.empty⟩ rfl).1
  simp only at hF₁ hF₂
  by_cases hpin : rangePin E parent rel width pre (headFloor E w'.rows parent rel) l' =
      rangePin E parent rel width pre (headFloor E w₀.rows parent rel) l₀
  · by_cases hb : rangePinBytes E parent rel width pre (headFloor E w'.rows parent rel) l' =
        rangePinBytes E parent rel width pre (headFloor E w₀.rows parent rel) l₀
    · have hfit0 := (sFit_of_fits hr hok.1 ⟨parent, rel, ByteArray.empty⟩).1
      have hfit' := (sFit_of_fits hr' hok'.1 ⟨parent, rel, ByteArray.empty⟩).1
      have hL₀ := listed hE.size hE.bytes_inj hr hok.1 hwd h0
      have hL := listed hE.size hE.bytes_inj hrw hokw.1 hwd hw
      have hL' := listed hE.size hE.bytes_inj hr' hok'.1 hwd hw'
      rcases rangePin_dec hE hfit' hfit0 hL' hL₀ hb with ⟨hF, hll⟩ | hc
      · exfalso
        simp only [st] at hF
        have hFw : headFloor E w.rows parent rel = headFloor E w₀.rows parent rel := by omega
        have hne : l ≠ l₀ := fun h => hstale (by rw [h, hFw])
        -- the listings differ in some member
        have hmem : ¬ ∀ x, x ∈ l ↔ x ∈ l₀ := by
          intro hall
          have hasym : ∀ a b : RowSlot D × RowLeaf,
              compare (rowKeyBytes E a.1).data (rowKeyBytes E b.1).data = .lt →
                ¬ compare (rowKeyBytes E b.1).data (rowKeyBytes E a.1).data = .lt := by
            intro a b h h'
            rw [Std.OrientedCmp.eq_swap (cmp := compare)] at h
            rw [h'] at h; cases h
          exact hne (pairwise_ext hasym
            (range_rows_sorted hE.size hE.n_le hE.bytes_inj hrw hokw.1 hwd hw)
            (range_rows_sorted hE.size hE.n_le hE.bytes_inj hr hok.1 hwd h0) hall)
        apply hmem
        intro ⟨s, v⟩
        -- a slot under the prefix reads at `w` what it reads at `w₀`
        have hmw := range_rows_mem hE.size hrw hwd hw
        have hm0 := range_rows_mem hE.size hr hwd h0
        have hm' := range_rows_mem hE.size hr' hwd hw'
        by_cases hsw : startsWith (rowsPrefix E parent rel width ++ pre) (rowKeyBytes E s) = true
        · have hsame : rowAt E w.rows s = rowAt E w₀.rows s := by
            apply Classical.byContradiction; intro hdiff
            -- the slot is a row of the relation: it is held at `w` or at `w₀`
            obtain ⟨key, rfl, hkp, hkr⟩ : ∃ key : RowKey D, s = .row key ∧ key.parent = parent ∧ key.rel = rel := by
              cases hs1 : rowAt E w.rows s with
              | some v1 =>
                  obtain ⟨k, rfl, -⟩ := listed_key E hE.size hE.bytes_inj hsw
                  exact ⟨_, rfl, rfl, rfl⟩
              | none =>
                  cases hs0 : rowAt E w₀.rows s with
                  | some v0 =>
                      obtain ⟨k, rfl, -⟩ := listed_key E hE.size hE.bytes_inj hsw
                      exact ⟨_, rfl, rfl, rfl⟩
                  | none => exact absurd (hs1.trans hs0.symm) hdiff
            have e0 : (st E w₀.rows key).2 = headFloor E w₀.rows parent rel := by simp [st, hkp, hkr]
            have e1 : (st E w.rows key).2 = headFloor E w₀.rows parent rel := by simp [st, hkp, hkr, hFw]
            have e2 : (st E w'.rows key).2 = headFloor E w₀.rows parent rel := by simp [st, hkp, hkr, hF]
            have hps : PS (st E w₀.rows key).1 (st E w₀.rows key).2 ≠ PS (st E w.rows key).1 (st E w.rows key).2 := by
              rw [e0, e1, ne_eq, ps_floor]; exact fun h => hdiff h.symm
            have hlt : rk (st E w₀.rows key).1 (st E w₀.rows key).2 < rk (st E w'.rows key).1 (st E w'.rows key).2 := by
              rcases (hm₁ key hkp).2 with h | h
              · exact absurd h hps
              · rcases (hm₂ key hkp).2 with h' | h'
                · rw [← rk_of_ps h']; exact h
                · omega
            have hsame' : rowAt E w'.rows (.row key) = rowAt E w₀.rows (.row key) := by
              apply Option.ext
              intro v
              have a := hm' (.row key) v
              have b := hm0 (.row key) v
              rw [hll] at a
              rw [a] at b
              simp only [hsw, and_true] at b
              exact b
            have : PS (st E w₀.rows key).1 (st E w₀.rows key).2 = PS (st E w'.rows key).1 (st E w'.rows key).2 := by
              rw [e0, e2, ps_floor]; exact hsame'.symm
            have := rk_of_ps this
            omega
          rw [hmw, hm0, hsame]
        · constructor
          · intro h; exact absurd ((hmw s v).mp h).2 hsw
          · intro h; exact absurd ((hm0 s v).mp h).2 hsw
      · exact .inr (.inr (hc.mono fun x hx => List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (List.mem_append.mpr (List.mem_append.mp hx).symm))))
    · exact .inr (.inr ⟨_, List.mem_cons_self, _, List.mem_cons_of_mem _ List.mem_cons_self,
        fun h => hb (congrArg Prod.snd h).symm, hpin.symm⟩)
  · exact .inl hpin

/-! ## The tooth: the pin before KERNEL-54 recurs -/

/-- The pin before KERNEL-54: a content digest of the LIVE cell (`w.live` reads a tombstone as
absent), no version. Kept only as the tooth's subject. -/
private def pinOfContent (E : Env D) : Option Cell → D
  | none => E.hash domAbsent ByteArray.empty
  | some c => E.hash "nanodregg/kernel/pin-cell/v1" (E.cellBytes c)

/-- The tooth's `Env`: one-byte digests; the hash reads the domain's length and the input's size and
byte sum (so the absent and tombstone pins differ, and so do two floors). Toy parameters only: the
deployed hash is never evaluated here. -/
private def vEnv : Env UInt8 where
  hash d b := UInt8.ofNat (d.length + b.size + (b.data.toList.map UInt8.toNat).sum)
  bytes d := ⟨#[d]⟩
  turnBytes _ := ByteArray.empty
  cellBytes _ := ByteArray.empty

private def vCell : Cell := { kind := 0, discipline := .ram, slots := [] }

private def vBirth0 : Turn UInt8 :=
  { txId := 1, notBefore := 0, validUntil := 1, touches := [], creates := [(5, vCell)],
    nullifiers := [], charge := 0, event := ByteArray.empty }

private def vBirth : Turn UInt8 := { vBirth0 with charge := vBirth0.weight }

private def vRetire0 : Turn UInt8 :=
  { txId := 2, notBefore := 0, validUntil := 2, touches := [⟨5, pinOf vEnv (some (.live vCell 0)), .retire⟩],
    creates := [], nullifiers := [], charge := 0, event := ByteArray.empty }

private def vRetire : Turn UInt8 := { vRetire0 with charge := vRetire0.weight }

private def vW0 : World UInt8 := World.genesis vEnv 0 1000000

/-- Everything the tooth claims of the two turns, as one computed Bool. -/
private def vCheck : Bool :=
  match World.admit vEnv vW0 vBirth with
  | .ok w₁ => (w₁.live vEnv 5).isSome &&
      decide (pinOfContent vEnv (w₁.live vEnv 5) ≠ pinOfContent vEnv (vW0.live vEnv 5)) &&
      match World.admit vEnv w₁ vRetire with
      | .ok w₂ => decide (w₂.entry vEnv 5 = some .tomb) &&
          decide (pinOfContent vEnv (vW0.live vEnv 5) = pinOfContent vEnv (w₂.live vEnv 5)) &&
          decide (pinOf vEnv (vW0.entry vEnv 5) ≠ pinOf vEnv (w₂.entry vEnv 5))
      | .error _ => false
  | .error _ => false

private theorem vCheck_true : vCheck = true := by decide

/-- **TOOTH: the old pin recurs, the entry pin does not.** On a concrete World and `Env`: a turn bears
cell `c`, the next retires it; before the birth `c` held nothing, between it was live, after it is a
tombstone. The pin before KERNEL-54 (`pinOfContent` of `w.live`) is the same before the birth and
after the retirement (A→B→A: an observation of absence would match again), and `pinOf` of the entry
is not. -/
theorem pinOf_old_recurs :
    ∃ (E : Env UInt8) (w₀ w₁ w₂ : World UInt8) (t₁ t₂ : Turn UInt8) (c : UInt8),
      World.admit E w₀ t₁ = .ok w₁ ∧ World.admit E w₁ t₂ = .ok w₂ ∧
      w₀.entry E c = none ∧ (w₁.live E c).isSome = true ∧ w₂.entry E c = some .tomb ∧
      pinOfContent E (w₁.live E c) ≠ pinOfContent E (w₀.live E c) ∧
      pinOfContent E (w₀.live E c) = pinOfContent E (w₂.live E c) ∧
      pinOf E (w₀.entry E c) ≠ pinOf E (w₂.entry E c) := by
  have hc := vCheck_true
  unfold vCheck at hc
  cases h₁ : World.admit vEnv vW0 vBirth with
  | error e => rw [h₁] at hc; cases hc
  | ok w₁ =>
      rw [h₁] at hc
      dsimp only at hc
      cases h₂ : World.admit vEnv w₁ vRetire with
      | error e => rw [h₂] at hc; simp at hc
      | ok w₂ =>
          rw [h₂] at hc
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
          obtain ⟨⟨hl, hst⟩, ⟨ht, hcont⟩, hpin⟩ := hc
          exact ⟨vEnv, vW0, w₁, w₂, vBirth, vRetire, 5, h₁, h₂, by decide, hl, ht, hst, hcont, hpin⟩

/-! ## The second tooth: a retired parent's floor reads 0 again, and the row is dead

Why `row_stale_behind_forever` and `range_stale_behind_forever` carry the disjunct
`w'.entry E parent = some .tomb`: a retirement drops its parent's heads (`dropHeads`), so the relation's floor
reads 0 again, and an absent row's pin at the OLD floor recurs. On a concrete World (cell 7 live, its
relation 3 declared at width 1 with retracts allowed, no rows): insert the row `[1]`, so its pin
moves (stale against the first World); retract it (the floor rises to 1); retire cell 7. The row's
pin is then the absent pin at floor 0 again, the very pin the first World held, and cell 7 is a
tombstone: every row touch under it is refused before any pin is read (`rowParentUnpinned` or
`orphanRow`), so no turn touching the row is ever admitted again. -/

private def dKey : RowKey UInt8 := ⟨7, 3, ⟨#[1]⟩⟩

private def dW0 : World UInt8 where
  trie := Trie.T.empty.insert (trieSpec vEnv) (.cell 7) (.entry (.live vCell 0))
  journal := .empty
  refusals := .empty
  rows := Trie.T.empty.insert (rowSpec vEnv) (.head 7 3) (.head 0 0 10 100 1 true 0)
  height := 0
  steps := 0
  chain := 0
  allowance := 1000000
  origin := 0

private def dKeep : Touch UInt8 := ⟨7, pinOf vEnv (some (.live vCell 0)), .keep⟩

private def dT1₀ : Turn UInt8 :=
  { txId := 1, notBefore := 0, validUntil := 1, touches := [dKeep], creates := [], nullifiers := [],
    charge := 0, event := ByteArray.empty, rows := [⟨.row dKey, none, .insert 1 ByteArray.empty⟩] }

private def dT1 : Turn UInt8 := { dT1₀ with charge := dT1₀.weight }

private def dT2₀ : Turn UInt8 :=
  { txId := 2, notBefore := 0, validUntil := 2, touches := [dKeep], creates := [], nullifiers := [],
    charge := 0, event := ByteArray.empty,
    rows := [⟨.row dKey, some (rowPin vEnv 0 (some (.row 1 ByteArray.empty 0))), .retract⟩] }

private def dT2 : Turn UInt8 := { dT2₀ with charge := dT2₀.weight }

private def dT3₀ : Turn UInt8 :=
  { txId := 3, notBefore := 0, validUntil := 3, touches := [⟨7, pinOf vEnv (some (.live vCell 0)), .retire⟩],
    creates := [], nullifiers := [], charge := 0, event := ByteArray.empty }

private def dT3 : Turn UInt8 := { dT3₀ with charge := dT3₀.weight }

/-- The row's pin at a World (the absent pin names the relation's floor). -/
private def dPin (w : World UInt8) : UInt8 :=
  rowPin vEnv (headFloor vEnv w.rows dKey.parent dKey.rel) (rowAt vEnv w.rows (.row dKey))

private def dCheck : Bool :=
  match World.fold vEnv dW0 [.turn dT1] with
  | .ok w => decide (dPin w ≠ dPin dW0) &&
      match World.fold vEnv w [.turn dT2, .turn dT3] with
      | .ok w' => decide (dPin w' = dPin dW0) && (w'.live vEnv 7).isNone &&
          decide (w'.entry vEnv 7 = some .tomb) && decide (headFloor vEnv w'.rows 7 3 = 0)
      | .error _ => false
  | .error _ => false

private theorem dCheck_true : dCheck = true := by decide +kernel

/-- Every row touch of an admitted turn passed `rowStep` on the rows it was judged on. -/
theorem foldRows_each {E : Env D} {w : World D} {t : Turn D} :
    ∀ (l : List (RowTouch D)) (acc rr : Rows D × Nat), l.foldlM (rowStepFreed E w t) acc = .ok rr →
      ∀ x ∈ l, ∃ r r', rowStep E w t r x = .ok r'
  | [], _, _, _, x, hx => by simp at hx
  | y :: rest, acc, rr, h, x, hx => by
      rw [List.foldlM_cons, except_bind_ok] at h
      obtain ⟨acc', h1, h2⟩ := h
      rcases List.mem_cons.mp hx with rfl | hx
      · unfold rowStepFreed rowStepFreedOn at h1; simp only [rowStepOn_trie, rowFreedOn_trie] at h1
        rw [except_bind_ok] at h1
        obtain ⟨r1, hs, -⟩ := h1
        exact ⟨_, _, hs⟩
      · exact foldRows_each rest acc' rr h2 x hx

/-- A row touch under a parent that is not live is refused before its pin is read. -/
theorem rowStep_dead {E : Env D} {w : World D} {t : Turn D} {r : Rows D} {x : RowTouch D}
    {key : RowKey D} (hx : x.slot = .row key) (hl : w.live E key.parent = none) :
    rowStep E w t r x = .error (.rowParentUnpinned key.parent) ∨
      rowStep E w t r x = .error (.orphanRow key.parent) := by
  unfold rowStep rowStepOn; simp only [headOfOn_trie, headFloorOn_trie, setHeadOn_trie]
  rw [hx]
  by_cases ht : (t.touches.any fun y => decide (y.cell = key.parent)) = true
  · right
    simp [req, ht, hl, bind, Except.bind]
  · left
    simp only [Bool.not_eq_true] at ht
    simp [req, ht, bind, Except.bind]

/-- A row touch under a parent that is not live: no turn naming it is admitted. -/
theorem admit_dead {E : Env D} {w w' : World D} {t : Turn D} {key : RowKey D}
    (hl : w.live E key.parent = none) (hx : ∃ x ∈ t.rows, x.slot = .row key) :
    World.admit E w t ≠ .ok w' := by
  intro h
  obtain ⟨posts, hk, -⟩ := admit_ok h
  have hr := hk.rows
  rw [rowsRun_eq] at hr
  simp only [except_bind_ok] at hr
  obtain ⟨⟨⟩, -, ⟨⟩, -, hr⟩ := hr
  split at hr
  · cases hr
  · simp only [except_bind_ok] at hr
    obtain ⟨acc, hf, -⟩ := hr
    obtain ⟨x, hxm, hxs⟩ := hx
    obtain ⟨r, r', hs⟩ := foldRows_each _ _ _ hf x hxm
    rcases rowStep_dead (t := t) (r := r) hxs hl with he | he <;> rw [he] at hs <;> cases hs

/-- **TOOTH: after its parent retires, a row's absent pin at the OLD floor recurs, and the row is
dead.** On a concrete World whose rows are canonical and well-formed (the premises of
`row_stale_behind_forever`): the row's pin moves (stale at `w`), then at `w'` it is again exactly the
pin of the first World (absent at floor 0: the retirement dropped the head and its floor), while the
parent is a tombstone; every row touch under it is refused `rowParentUnpinned` or `orphanRow`, and no
turn naming the row is admitted. So the disjunct `w'.entry E key.parent = some .tomb` is needed, and it is
final. -/
theorem rowPin_old_floor_recurs :
    ∃ (E : Env UInt8) (w₀ w w' : World UInt8) (l₁ l₂ : List (Step UInt8)) (key : RowKey UInt8),
      w₀.RowsCanon E ∧ w₀.RowsOk E ∧
      World.fold E w₀ l₁ = .ok w ∧ World.fold E w l₂ = .ok w' ∧
      rowPin E (headFloor E w.rows key.parent key.rel) (rowAt E w.rows (.row key)) ≠
        rowPin E (headFloor E w₀.rows key.parent key.rel) (rowAt E w₀.rows (.row key)) ∧
      rowPin E (headFloor E w'.rows key.parent key.rel) (rowAt E w'.rows (.row key)) =
        rowPin E (headFloor E w₀.rows key.parent key.rel) (rowAt E w₀.rows (.row key)) ∧
      headFloor E w'.rows key.parent key.rel = 0 ∧
      w'.live E key.parent = none ∧ w'.entry E key.parent = some .tomb ∧
      (∀ (t : Turn UInt8) (r : Rows UInt8) (x : RowTouch UInt8), x.slot = .row key →
        rowStep E w' t r x = .error (.rowParentUnpinned key.parent) ∨
          rowStep E w' t r x = .error (.orphanRow key.parent)) ∧
      (∀ (t : Turn UInt8) (v : World UInt8), (∃ x ∈ t.rows, x.slot = .row key) → World.admit E w' t ≠ .ok v) := by
  have hc := dCheck_true
  unfold dCheck at hc
  cases h₁ : World.fold vEnv dW0 [.turn dT1] with
  | error e => rw [h₁] at hc; cases hc
  | ok w =>
      rw [h₁] at hc
      dsimp only at hc
      cases h₂ : World.fold vEnv w [.turn dT2, .turn dT3] with
      | error e => rw [h₂] at hc; simp at hc
      | ok w' =>
          rw [h₂] at hc
          simp only [Bool.and_eq_true, decide_eq_true_eq, Option.isNone_iff_eq_none] at hc
          obtain ⟨hst, ⟨⟨hrec, hl⟩, htb⟩, hfl⟩ := hc
          refine ⟨vEnv, dW0, w, w', [.turn dT1], [.turn dT2, .turn dT3], dKey,
            Trie.canon_insert _ _ _ (Trie.canon_empty _ 0), by unfold World.RowsOk; decide, h₁, h₂, hst, hrec, hfl, hl, htb,
            fun t r x hx => rowStep_dead hx hl, fun t v hx => admit_dead hl hx⟩

/-! ## The third tooth: without the floor a range pin recurs

Why `rangePin` names the relation's floor (KERNEL-54): a listing returns. On the second tooth's World
(cell 7 live, its relation 3 at width 1 with retracts allowed, no rows), read the whole relation
(empty prefix): insert the row `[1]` (the listing grows), then retract it (the listing is empty
again, the floor rises to 1) while cell 7 stays live. The floorless pin (the floor fixed at 0, the
shape before KERNEL-54) moved and came back, so a stale range read would match again; the real
pin, with the floor, has not come back. -/

/-- The range pin before KERNEL-54: no floor (fixed at 0). -/
private def rangePinFloorless (E : Env D) (parent : D) (rel width : Nat) (pre : ByteArray)
    (l : List (RowSlot D × RowLeaf)) : D :=
  rangePin E parent rel width pre 0 l

/-- The inserted row, as the whole relation lists it. -/
private def rL : List (RowSlot UInt8 × RowLeaf) := [(.row dKey, .row 1 ByteArray.empty 0)]

private def rRows (w : World UInt8) : Option (List (RowSlot UInt8 × RowLeaf)) :=
  rangeRows vEnv w.rows 7 3 1 ByteArray.empty 5

private def rPin (w : World UInt8) (l : List (RowSlot UInt8 × RowLeaf)) : UInt8 :=
  rangePin vEnv 7 3 1 ByteArray.empty (headFloor vEnv w.rows 7 3) l

private def rCheck : Bool :=
  decide (rRows dW0 = some []) &&
  decide (rangePinFloorless vEnv 7 3 1 ByteArray.empty rL ≠ rangePinFloorless vEnv 7 3 1 ByteArray.empty []) &&
  match World.fold vEnv dW0 [.turn dT1] with
  | .ok w => decide (rRows w = some rL) && decide (rPin w rL ≠ rPin dW0 []) &&
      match World.fold vEnv w [.turn dT2] with
      | .ok w' => decide (rRows w' = some []) && decide (w'.entry vEnv 7 = some (.live vCell 0)) &&
          decide (rPin w' [] ≠ rPin dW0 [])
      | .error _ => false
  | .error _ => false

private theorem rCheck_true : rCheck = true := by decide +kernel

/-- **The floor is what makes `range_stale_behind_forever` true.** Every premise of that theorem
holds (a lawful `Ord UInt8`, `pre.size ≤ width`, the range pin stale at `w`), the
parent is LIVE at `w'` (so the parent-gone disjunct is false), the listing at `w'` is the listing at
`w₀`, and the floorless pin, which moved at `w`, is again `w₀`'s at `w'`; the pin with the floor is
not. -/
theorem rangePin_floorless_recurs :
    ∃ (E : Env UInt8) (w₀ w w' : World UInt8) (l₁ l₂ : List (Step UInt8)) (parent : UInt8)
      (rel width most : Nat) (pre : ByteArray) (L₀ L L' : List (RowSlot UInt8 × RowLeaf)),
      w₀.RowsCanon E ∧ w₀.RowsOk E ∧
      World.fold E w₀ l₁ = .ok w ∧ World.fold E w l₂ = .ok w' ∧
      pre.size ≤ width ∧
      rangeRows E w₀.rows parent rel width pre most = some L₀ ∧
      rangeRows E w.rows parent rel width pre most = some L ∧
      rangeRows E w'.rows parent rel width pre most = some L' ∧
      rangePin E parent rel width pre (headFloor E w.rows parent rel) L ≠
        rangePin E parent rel width pre (headFloor E w₀.rows parent rel) L₀ ∧
      (∃ c v, w'.entry E parent = some (.live c v)) ∧
      L' = L₀ ∧
      rangePinFloorless E parent rel width pre L ≠ rangePinFloorless E parent rel width pre L₀ ∧
      rangePinFloorless E parent rel width pre L' = rangePinFloorless E parent rel width pre L₀ ∧
      rangePin E parent rel width pre (headFloor E w'.rows parent rel) L' ≠
        rangePin E parent rel width pre (headFloor E w₀.rows parent rel) L₀ := by
  have hc := rCheck_true
  unfold rCheck at hc
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨h0, hfl⟩, hc⟩ := hc
  cases h₁ : World.fold vEnv dW0 [.turn dT1] with
  | error e => rw [h₁] at hc; cases hc
  | ok w =>
      rw [h₁] at hc
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      obtain ⟨⟨hL, hst⟩, hc⟩ := hc
      cases h₂ : World.fold vEnv w [.turn dT2] with
      | error e => rw [h₂] at hc; cases hc
      | ok w' =>
          rw [h₂] at hc
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
          obtain ⟨⟨hL', hlive⟩, hne⟩ := hc
          exact ⟨vEnv, dW0, w, w', [.turn dT1], [.turn dT2], 7, 3, 1, 5, ByteArray.empty, [], rL, [],
            Trie.canon_insert _ _ _ (Trie.canon_empty _ 0), by unfold World.RowsOk; decide, h₁, h₂,
            by decide, h0, hL, hL', hst, ⟨_, _, hlive⟩, rfl, hfl, rfl, hne⟩

/-! ## Teeth (KERNEL-56): under a hash that separates the inputs compared, the collision arm is gone -/

/-- TOOTH (`stale_behind_forever`): where the hash separates the two pin inputs, a cell pin observed
on the fold and stale now is stale for ever. -/
theorem stale_behind_forever_sep {E : Env D} {w₀ w w' : World D}
    {l₁ l₂ : List (Step D)} (hf : w₀.CellsFit Cell.Fits E)
    (h₁ : World.fold E w₀ l₁ = .ok w) (h₂ : World.fold E w l₂ = .ok w') {c : D}
    (hs : Separates E.hash [pinPre E (w₀.entry E c), pinPre E (w'.entry E c)])
    (hstale : pinOf E (w.entry E c) ≠ pinOf E (w₀.entry E c)) :
    pinOf E (w'.entry E c) ≠ pinOf E (w₀.entry E c) :=
  hs.elim (stale_behind_forever hf h₁ h₂ hstale)

/-- TOOTH (`row_stale_behind_forever`): where the hash separates the two row-pin inputs, a row pin
observed on the fold and stale now is stale for ever, or the parent is retired. -/
theorem row_stale_behind_forever_sep [Std.TransOrd D] [Std.LawfulEqOrd D] {E : Env D} {n : Nat}
    (hE : E.Lawful n) {w₀ w w' : World D}
    {l₁ l₂ : List (Step D)} (hr : w₀.RowsCanon E) (hok : w₀.RowsOk E)
    (h₁ : World.fold E w₀ l₁ = .ok w) (h₂ : World.fold E w l₂ = .ok w') {key : RowKey D}
    (hs : Separates E.hash [rowPre (headFloor E w₀.rows key.parent key.rel) (rowAt E w₀.rows (.row key)),
      rowPre (headFloor E w'.rows key.parent key.rel) (rowAt E w'.rows (.row key))])
    (hstale : rowPin E (headFloor E w.rows key.parent key.rel) (rowAt E w.rows (.row key)) ≠
      rowPin E (headFloor E w₀.rows key.parent key.rel) (rowAt E w₀.rows (.row key))) :
    rowPin E (headFloor E w'.rows key.parent key.rel) (rowAt E w'.rows (.row key)) ≠
        rowPin E (headFloor E w₀.rows key.parent key.rel) (rowAt E w₀.rows (.row key)) ∨
      w'.entry E key.parent = some .tomb :=
  (row_stale_behind_forever hE hr hok h₁ h₂ hstale).imp_right hs.elim

/-- TOOTH (`range_stale_behind_forever`): where the hash separates the two range-pin inputs and both
listings' leaf inputs, a range pin observed on the fold and stale now is stale for ever, or the
parent is retired. -/
theorem range_stale_behind_forever_sep [Std.TransOrd D] [Std.LawfulEqOrd D] {E : Env D} {n : Nat}
    (hE : E.Lawful n) {w₀ w w' : World D}
    {l₁ l₂ : List (Step D)} (hr : w₀.RowsCanon E) (hok : w₀.RowsOk E)
    (h₁ : World.fold E w₀ l₁ = .ok w) (h₂ : World.fold E w l₂ = .ok w')
    {parent : D} {rel width most : Nat} {pre : ByteArray} {l₀ l l' : List (RowSlot D × RowLeaf)}
    (hwd : pre.size ≤ width)
    (h0 : rangeRows E w₀.rows parent rel width pre most = some l₀)
    (hw : rangeRows E w.rows parent rel width pre most = some l)
    (hw' : rangeRows E w'.rows parent rel width pre most = some l')
    (hs : Separates E.hash (rangePre E parent rel width pre (headFloor E w₀.rows parent rel) l₀ ::
      rangePre E parent rel width pre (headFloor E w'.rows parent rel) l' :: (leafPres l₀ ++ leafPres l')))
    (hstale : rangePin E parent rel width pre (headFloor E w.rows parent rel) l ≠
      rangePin E parent rel width pre (headFloor E w₀.rows parent rel) l₀) :
    rangePin E parent rel width pre (headFloor E w'.rows parent rel) l' ≠
        rangePin E parent rel width pre (headFloor E w₀.rows parent rel) l₀ ∨
      w'.entry E parent = some .tomb :=
  (range_stale_behind_forever hE hr hok h₁ h₂ hwd h0 hw hw' hstale).imp_right hs.elim
