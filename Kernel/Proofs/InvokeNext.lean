/-
# Kernel.Proofs.InvokeNext — the next run of an object is handed what this run returned

LEDGER's `Runs` (`Ledger.Proofs.EscrowRun`) chains the receiver's runs on one object: each next run
reads slots that hold, key by key, what the run before it returned (`∀ k, next.get k = s.get k`).
That link is the kernel's: `invoke` writes `writeOf obj (diffOps old s)`, `World.admit` applies it,
and the next `invokeRun` reads the cell back through its pins. Proved here of those definitions:

* `diffOps_next`: the write `diffOps` derives from a run's state `s`, applied to the cell, leaves a
  cell whose state reads `s` at every key, when `s` passed `checkState` (every key at least
  `stateBase`, strictly ascending) and the write's keys are distinct (`checkShape`'s
  `duplicateKey`).
* `admit_live_write`: an admitted turn whose every touch of a live cell writes `ops` (and which
  touches it) leaves it live with `applyOps` of its slots, and `ops`' keys distinct.
* `invokeRun_live`: a successful `invokeRun` through `w`'s pins ran on the cell live in `w`.
* `invoke_next_slots`: a signed invoke of `obj`, derived from `w` and admitted to `w'`, whose run
  returned `s`: `obj` is live in `w'` and its state reads `s` at every key. `invoke_next_run`: so
  the state the next invoke of `obj` on `w'` is handed (`stateOf` of `invokeRun`'s cell) is `Runs`'
  `next` for this run's `s`.

No premise beyond the admitted turn and the run that names `s`: the cells' trie reads back exactly
what was inserted (`Trie.get_insert`, no collision escape), and the act the Turn carries at `obj` is
the invoke's own (`writeOf` claims the cell even when the run writes nothing, and it is the first
effect of the signed call's Draft).

Teeth: `next_slots_tooth` (a turn that writes another value at a state key than the run returned
leaves the next state disagreeing with the run's there), `checkState_dup_refused` and
`diffOps_dup_tooth` (a run returning one key twice is refused; without that refusal its derived
write leaves the second value while the run's slots read the first).
-/
import Kernel.Proofs.Tree
import Kernel.Proofs.Frame

namespace Nanodregg.Kernel.Receive

open Nanodregg.Kernel

/-- `==` on byte strings is equality (`ByteArray`'s `BEq` compares the arrays). -/
private instance : LawfulBEq ByteArray where
  rfl := by
    intro ⟨a⟩
    show (a == a) = true
    exact beq_self_eq_true a
  eq_of_beq := by
    intro ⟨a⟩ ⟨b⟩ h
    have : (a == b) = true := h
    rw [eq_of_beq this]

/-! ## Slots, key by key -/

/-- The values a slot list holds at key `k`, in order (`Slots.get` reads the first). -/
private def vals (k : Nat) : Slots → List ByteArray
  | [] => []
  | p :: rest => if p.1 = k then p.2 :: vals k rest else vals k rest

private theorem get_vals (k : Nat) : ∀ s : Slots, s.get k = (vals k s).head?
  | [] => rfl
  | (a, b) :: rest => by
      have ih := get_vals k rest
      by_cases h : a = k
      · subst h; simp [Slots.get, List.lookup, vals]
      · have hb : (k == a) = false := beq_eq_false_iff_ne.mpr (Ne.symm h)
        simp only [Slots.get] at ih
        simp only [Slots.get, List.lookup, hb, vals, if_neg h, ih]

private theorem vals_set_ne {j k : Nat} (v : ByteArray) (h : j ≠ k) :
    ∀ s : Slots, vals k (Slots.set j v s) = vals k s
  | [] => by simp [Slots.set, vals, h]
  | (a, b) :: rest => by
      unfold Slots.set
      split
      · simp [vals, h]
      · split
        · rename_i he; subst he; simp [vals, h]
        · simp [vals, vals_set_ne v h rest]

private theorem get_set_self (k : Nat) (v : ByteArray) : ∀ s : Slots, (Slots.set k v s).get k = some v
  | [] => by simp [Slots.set, Slots.get]
  | (a, b) :: rest => by
      unfold Slots.set
      split
      · simp [Slots.get, List.lookup]
      · split
        · simp [Slots.get, List.lookup]
        · rename_i h2
          have ih := get_set_self k v rest
          have hb : (k == a) = false := beq_eq_false_iff_ne.mpr h2
          simp only [Slots.get] at ih
          simp only [Slots.get, List.lookup, hb, ih]

private theorem vals_erase_ne {j k : Nat} (h : j ≠ k) : ∀ s : Slots, vals k (Slots.erase j s) = vals k s
  | [] => rfl
  | (a, b) :: rest => by
      unfold Slots.erase
      split
      · rename_i he; subst he; simp [vals, h]
      · simp [vals, vals_erase_ne h rest]

private theorem vals_erase_self (k : Nat) : ∀ s : Slots, vals k (Slots.erase k s) = (vals k s).tail
  | [] => rfl
  | (a, b) :: rest => by
      unfold Slots.erase
      split
      · rename_i he; subst he; simp [vals]
      · rename_i hne; simp [vals, Ne.symm hne, vals_erase_self k rest]

private theorem vals_applyOp_ne {k : Nat} {o : Op} (h : o.key ≠ k) (s : Slots) :
    vals k (applyOp s o) = vals k s := by
  cases o with
  | set j v => exact vals_set_ne v h s
  | erase j => exact vals_erase_ne h s

private theorem vals_applyOps_ne {k : Nat} :
    ∀ {ops : List Op}, (∀ o ∈ ops, o.key ≠ k) → ∀ s, vals k (applyOps s ops) = vals k s
  | [], _, _ => rfl
  | o :: rest, h, s => by
      show vals k (applyOps (applyOp s o) rest) = _
      rw [vals_applyOps_ne (fun o' ho' => h o' (List.mem_cons_of_mem _ ho')),
        vals_applyOp_ne (h o List.mem_cons_self)]

/-- Of a write with distinct keys, the one op at `k` decides the cell's values there: the ops
before it leave them, and the ops after it too. -/
private theorem applyOps_at {k : Nat} {ops : List Op} {o : Op} (hn : (opKeys ops).Nodup) (ho : o ∈ ops)
    (hk : o.key = k) (s : Slots) :
    ∃ s', vals k s' = vals k s ∧ vals k (applyOps s ops) = vals k (applyOp s' o) := by
  obtain ⟨as, bs, rfl⟩ := List.append_of_mem ho
  unfold opKeys at hn
  rw [List.map_append, List.map_cons, List.nodup_append] at hn
  obtain ⟨-, hbs, hdis⟩ := hn
  refine ⟨applyOps s as, vals_applyOps_ne (fun o' ho' he => ?_) s, ?_⟩
  · exact hdis _ (List.mem_map_of_mem ho') _ List.mem_cons_self (he.trans hk.symm)
  · show vals k ((as ++ o :: bs).foldl applyOp s) = _
    rw [List.foldl_append, List.foldl_cons]
    refine vals_applyOps_ne (fun o' ho' he => (List.nodup_cons.mp hbs).1 ?_) _
    rw [hk, ← he]; exact List.mem_map_of_mem ho'

private theorem vals_nil {k : Nat} : ∀ {s : Slots}, (∀ p ∈ s, p.1 ≠ k) → vals k s = []
  | [], _ => rfl
  | p :: rest, h => by
      simp [vals, h p List.mem_cons_self, vals_nil (fun q hq => h q (List.mem_cons_of_mem _ hq))]

private theorem vals_filter {k : Nat} {c : Nat × ByteArray → Bool} :
    ∀ {s : Slots}, (∀ p ∈ s, p.1 = k → c p = true) → vals k (s.filter c) = vals k s
  | [], _ => rfl
  | p :: rest, h => by
      have ih := vals_filter (s := rest) (fun q hq => h q (List.mem_cons_of_mem _ hq))
      by_cases hp : p.1 = k
      · rw [List.filter_cons_of_pos (h p List.mem_cons_self hp)]; simp [vals, hp, ih]
      · by_cases hc : c p = true
        · rw [List.filter_cons_of_pos hc]; simp [vals, hp, ih]
        · rw [List.filter_cons_of_neg hc]; simp [vals, hp, ih]

private theorem vals_stateOf (c : Cell) (k : Nat) :
    vals k (stateOf c) = if stateBase ≤ k then vals k c.slots else [] := by
  unfold stateOf
  split
  · rename_i hk
    exact vals_filter (fun p _ he => by rw [he]; simpa using hk)
  · rename_i hk
    exact vals_nil (fun p hp he => by
      have := (List.mem_filter.mp hp).2
      rw [he] at this
      exact hk (by simpa using this))

private theorem mem_vals {p : Nat × ByteArray} : ∀ {s : Slots}, p ∈ s → p.2 ∈ vals p.1 s
  | [], h => by simp at h
  | q :: rest, h => by
      rcases List.mem_cons.mp h with rfl | h
      · simp [vals]
      · by_cases hq : q.1 = p.1
        · simp [vals, hq, mem_vals h]
        · simp [vals, hq, mem_vals h]

private theorem vals_le_one {k : Nat} : ∀ {s : Slots}, (s.map Prod.fst).Nodup → (vals k s).length ≤ 1
  | [], _ => by simp [vals]
  | p :: rest, h => by
      rw [List.map_cons, List.nodup_cons] at h
      by_cases hp : p.1 = k
      · simp only [vals, if_pos hp]
        rw [vals_nil (fun q hq he => h.1 (by rw [hp, ← he]; exact List.mem_map_of_mem hq))]
        simp
      · simp only [vals, if_neg hp]; exact vals_le_one h.2

private theorem mem_diffOps {old new : Slots} {o : Op} :
    o ∈ diffOps old new ↔
      (∃ p ∈ new, (old.get p.1 != some p.2) = true ∧ o = .set p.1 p.2) ∨
        (∃ p ∈ old, (new.get p.1).isNone = true ∧ o = .erase p.1) := by
  unfold diffOps
  simp only [List.mem_append, List.mem_map, List.mem_filter]
  constructor
  · rintro (⟨p, ⟨hp, hc⟩, rfl⟩ | ⟨p, ⟨hp, hc⟩, rfl⟩)
    · exact .inl ⟨p, hp, hc, rfl⟩
    · exact .inr ⟨p, hp, hc, rfl⟩
  · rintro (⟨p, hp, hc, rfl⟩ | ⟨p, hp, hc, rfl⟩)
    · exact .inl ⟨p, ⟨hp, hc⟩, rfl⟩
    · exact .inr ⟨p, ⟨hp, hc⟩, rfl⟩

variable {D : Type}

/-- A state that passed `checkStateFrom lo`: every key at least `lo`, each key holding exactly one
value. -/
private theorem checkStateFrom_ok {lo : Nat} :
    ∀ {s : Slots}, checkStateFrom (D := D) lo s = .ok () →
      (∀ p ∈ s, lo ≤ p.1) ∧ ∀ p ∈ s, vals p.1 s = [p.2]
  | [], _ => by simp
  | p :: rest, h => by
      simp only [checkStateFrom, except_bind_ok] at h
      obtain ⟨⟨⟩, hp, hr⟩ := h
      rw [req_ok, decide_eq_true_eq] at hp
      obtain ⟨hlo, hv⟩ := checkStateFrom_ok hr
      refine ⟨fun q hq => ?_, fun q hq => ?_⟩
      · rcases List.mem_cons.mp hq with rfl | hq
        · exact hp
        · have := hlo q hq; omega
      · rcases List.mem_cons.mp hq with rfl | hq
        · show (if q.1 = q.1 then q.2 :: vals q.1 rest else vals q.1 rest) = [q.2]
          rw [if_pos rfl, vals_nil (fun r hr he => by have := hlo r hr; omega)]
        · have hne : p.1 ≠ q.1 := by have := hlo q hq; omega
          show (if p.1 = q.1 then p.2 :: vals q.1 rest else vals q.1 rest) = [q.2]
          rw [if_neg hne]; exact hv q hq

/-- **The write a run's state derives leaves exactly that state.** Over any cell, the write
`diffOps (stateOf cell) s` (what `invoke` writes from a run that returned `s`), applied, leaves a
cell whose state reads `s` at every key, when `s` passed `checkState` and the write's keys are
distinct. -/
theorem diffOps_next {cell : Cell} {s : Slots} (hs : checkState (D := D) s = .ok ())
    (hn : (opKeys (diffOps (stateOf cell) s)).Nodup) (k : Nat) :
    (stateOf { cell with slots := applyOps cell.slots (diffOps (stateOf cell) s) }).get k = s.get k := by
  obtain ⟨hge, hone⟩ := checkStateFrom_ok hs
  rw [get_vals, get_vals, vals_stateOf]
  rcases Nat.lt_or_ge k stateBase with hk | hk
  · rw [if_neg (by omega), vals_nil (fun p hp he => by have := hge p hp; omega)]
  rw [if_pos hk]
  dsimp only
  have hold : vals k (stateOf cell) = vals k cell.slots := by rw [vals_stateOf, if_pos hk]
  by_cases hq : ∃ q ∈ s, q.1 = k
  · obtain ⟨q, hq, rfl⟩ := hq
    rw [hone q hq]
    by_cases ho : (stateOf cell).get q.1 = some q.2
    · have hno : ∀ o ∈ diffOps (stateOf cell) s, o.key ≠ q.1 := by
        intro o hmem hkey
        rcases mem_diffOps.mp hmem with ⟨p, hp, hc, rfl⟩ | ⟨p, hp, hc, rfl⟩
        · have hpk : p.1 = q.1 := hkey
          have hv : p.2 ∈ vals q.1 s := hpk ▸ mem_vals hp
          rw [hone q hq, List.mem_singleton] at hv
          rw [hpk, hv, ho] at hc
          simp at hc
        · have hpk : p.1 = q.1 := hkey
          rw [hpk, get_vals, hone q hq] at hc
          simp at hc
      rw [vals_applyOps_ne hno, ← hold, ← get_vals, ho]
      rfl
    · have hm : Op.set q.1 q.2 ∈ diffOps (stateOf cell) s :=
        mem_diffOps.mpr (.inl ⟨q, hq, by simpa using ho, rfl⟩)
      obtain ⟨s', -, he⟩ := applyOps_at (k := q.1) hn hm rfl cell.slots
      rw [he, ← get_vals]
      exact get_set_self q.1 q.2 s'
  · have hq' : ∀ q ∈ s, q.1 ≠ k := fun q hm' he => hq ⟨q, hm', he⟩
    rw [vals_nil hq']
    have hsk : s.get k = none := by rw [get_vals, vals_nil hq']; rfl
    by_cases hp : ∃ p ∈ stateOf cell, p.1 = k
    · obtain ⟨p, hp, rfl⟩ := hp
      have hm : Op.erase p.1 ∈ diffOps (stateOf cell) s :=
        mem_diffOps.mpr (.inr ⟨p, hp, by rw [hsk]; rfl, rfl⟩)
      obtain ⟨s', hs', he⟩ := applyOps_at (k := p.1) hn hm rfl cell.slots
      rw [he]
      show (vals p.1 (Slots.erase p.1 s')).head? = none
      rw [vals_erase_self, hs', ← hold]
      have hle : (vals p.1 (stateOf cell)).length ≤ 1 := by
        have hB : (((stateOf cell).filter fun p => (s.get p.1).isNone).map Prod.fst).Nodup := by
          unfold opKeys diffOps at hn
          rw [List.map_append, List.nodup_append] at hn
          have h2 := hn.2.1
          rw [List.map_map] at h2
          exact h2
        have := vals_le_one (k := p.1) hB
        rwa [vals_filter (fun r _ hr => by rw [hr, hsk]; rfl)] at this
      cases hv : vals p.1 (stateOf cell) with
      | nil => rfl
      | cons a l =>
          rw [hv] at hle
          cases l with
          | nil => rfl
          | cons _ _ => simp at hle
    · have hp' : ∀ p ∈ stateOf cell, p.1 ≠ k := fun p hm' he => hp ⟨p, hm', he⟩
      have hno : ∀ o ∈ diffOps (stateOf cell) s, o.key ≠ k := by
        intro o hmem hkey
        rcases mem_diffOps.mp hmem with ⟨p, hp, -, rfl⟩ | ⟨p, hp, -, rfl⟩
        · exact hq' p hp hkey
        · exact hp' p hp hkey
      rw [vals_applyOps_ne hno, ← hold, vals_nil hp']

/-! ## An admitted write -/

variable [Ord D] [DecidableEq D]

omit [Ord D] [DecidableEq D] in
private theorem postWrite_slots {c : D} {cell post : Cell} {ops : List Op}
    (h : postWrite c cell ops = .ok post) : post = { cell with slots := applyOps cell.slots ops } := by
  unfold postWrite at h
  cases hd : cell.discipline <;> simp only [hd] at h
  · cases h
  · simp only [except_bind_ok, pure, Except.pure] at h
    obtain ⟨⟨⟩, -, ⟨⟩, -, h⟩ := h
    cases h; rfl
  · simp only [except_bind_ok, pure, Except.pure] at h
    obtain ⟨⟨⟩, -, h⟩ := h
    cases h; rfl
  · simp only [except_bind_ok, pure, Except.pure] at h
    obtain ⟨⟨⟩, -, ⟨⟩, -, h⟩ := h
    cases h; rfl

private theorem touchCheck_write {E : Env D} {w : World D} {y : Touch D} {ops : List Op} {cell : Cell}
    {ver : Nat} {p : Post D} (hy : y.act = .write ops) (he : w.entry E y.cell = some (.live cell ver))
    (h : touchCheck E w y = .ok (some p)) :
    p.entry = .live { cell with slots := applyOps cell.slots ops } (ver + 1) := by
  unfold touchCheck at h
  simp only [except_bind_ok] at h
  obtain ⟨⟨⟩, -, h⟩ := h
  rw [hy, he] at h
  simp only [except_bind_ok] at h
  obtain ⟨⟨⟩, -, post, hp, h⟩ := h
  simp only [pure, Except.pure, Except.ok.injEq, Option.some.injEq] at h
  subst h
  show Entry.live post (ver + 1) = _
  rw [postWrite_slots hp]

/-- **An admitted write reads back.** An admitted turn that touches a live cell, every touch of it
writing `ops`, leaves the cell live with `ops` applied to its slots; `ops`' keys are distinct
(`checkShape`). -/
theorem admit_live_write {E : Env D} {w w' : World D} {t : Turn D} {obj : D} {cell : Cell} {ops : List Op}
    (h : World.admit E w t = .ok w') (hl : w.live E obj = some cell)
    (hx : ∃ x ∈ t.touches, x.cell = obj) (hall : ∀ x ∈ t.touches, x.cell = obj → x.act = .write ops) :
    w'.live E obj = some { cell with slots := applyOps cell.slots ops } ∧ (opKeys ops).Nodup := by
  obtain ⟨posts, hk, rfl⟩ := admit_ok h
  obtain ⟨x, hxm, hxc⟩ := hx
  obtain ⟨ver, hver⟩ := live_entry hl
  obtain ⟨raw, hm, hposts⟩ := hk.touches
  have hpost : ∀ p ∈ posts, p.cell = obj → p.entry = .live { cell with slots := applyOps cell.slots ops } (ver + 1) := by
    intro p hp hpc
    have hp' : some p ∈ raw := by rw [hposts] at hp; simpa [List.reduceOption, List.mem_filterMap] using hp
    obtain ⟨y, hy, hr⟩ := mapEx_mem hm (some p) hp'
    have hyc : y.cell = obj := (touchCheck_some hr).1.symm.trans hpc
    exact touchCheck_write (hall y hy hyc) (by rw [hyc]; exact hver) hr
  -- the touch of `obj` leaves a post there
  obtain ⟨rx, hrx, hfx⟩ := mapEx_fwd hm x hxm
  obtain ⟨px, hpx⟩ : ∃ px, rx = some px := by
    unfold touchCheck at hfx
    simp only [except_bind_ok] at hfx
    obtain ⟨⟨⟩, -, hfx⟩ := hfx
    rw [hall x hxm hxc, hxc, hver] at hfx
    simp only [except_bind_ok] at hfx
    obtain ⟨⟨⟩, -, post, -, hfx⟩ := hfx
    simp only [pure, Except.pure, Except.ok.injEq] at hfx
    exact ⟨_, hfx.symm⟩
  subst hpx
  have hpxm : px ∈ posts := by rw [hposts]; simpa [List.reduceOption, List.mem_filterMap] using hrx
  have hpxc : px.cell = obj := (touchCheck_some hfx).1.trans hxc
  have hin : obj ∈ (posts.map Post.pair).map Prod.fst := by
    rw [List.map_map]; exact List.mem_map.mpr ⟨px, hpxm, hpxc⟩
  obtain ⟨e, he, hg⟩ := insertAll_get_mem (E := E) (m := w.trie) hin
  obtain ⟨q, hq, hqe⟩ := List.mem_map.mp he
  simp only [Post.pair, Prod.mk.injEq] at hqe
  obtain ⟨hqc, rfl⟩ := hqe
  have hborn : obj ∉ (bornEntries t).map Prod.fst := by
    have := live_not_created hk hl
    simpa [bornEntries, createdIds, List.map_map, Function.comp_def] using this
  refine ⟨get_live (v := ver + 1) ?_, ?_⟩
  · show (commitTrie E w t posts).get (trieSpec E) (.cell obj) = _
    rw [commitTrie_cell, insertAll_get_of_not_mem hborn, hg, hpost q hq hqc]
  · have hs := hk.shape
    unfold checkShape at hs
    simp only [except_bind_ok] at hs
    obtain ⟨⟨⟩, -, ⟨⟩, -, ⟨⟩, hf, -⟩ := hs
    have hn := firstDup_none (noDup_none ((forEx_ok.mp hf) x hxm))
    have hops : x.ops = ops := by unfold Touch.ops; rw [hall x hxm hxc]
    rwa [hops] at hn

/-! ## The signed invoke, derived and admitted -/

omit [Ord D] [DecidableEq D] in
private theorem foldCalls_effects {sub : Sub D} {obj : D} :
    ∀ (calls : List (Body D)) (acc : Draft D × Walk D) {r : Draft D × Walk D},
      calls.foldlM (callStep sub obj) acc = .ok r → ∃ l, r.1.effects = acc.1.effects ++ l
  | [], acc, r, h => by
      simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h
      subst h; exact ⟨[], by simp⟩
  | b :: rest, acc, r, h => by
      rw [List.foldlM_cons] at h
      simp only [except_bind_ok] at h
      obtain ⟨s, hs1, h⟩ := h
      unfold callStep at hs1
      simp only [except_bind_ok, pure, Except.pure, Except.ok.injEq] at hs1
      obtain ⟨q, -, rfl⟩ := hs1
      obtain ⟨l, hl⟩ := foldCalls_effects rest _ h
      exact ⟨q.1.effects ++ l, by rw [hl]; simp [Draft.append]⟩

omit [Ord D] in
private theorem invokeRun_cell {X : Ctx D} {look : Pinned D} {c : Call D} {actor obj : D} {method : Nat}
    {via : Option D} {cell : Cell} {p : D} {r : Req D}
    (h : invokeRun X look c actor obj method via = .ok (cell, p, r)) :
    readKind look obj kindObject = .ok cell := by
  unfold invokeRun at h
  simp only [except_bind_ok] at h
  obtain ⟨cell', hc, pkg, -, p', -, pr, -, h⟩ := h
  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  rw [← h.1]; exact hc

private theorem readKind_pinned {E : Env D} {w : World D} {pins : List (D × D)} {c : D} {kind : Nat}
    {cell : Cell} (h : readKind (pinned E w pins) c kind = .ok cell) :
    w.live E c = some cell ∧ ∃ q ∈ pins, q.1 = c := by
  unfold readKind pinned at h
  by_cases hp : (pins.any fun p => decide (p.1 = c)) = true
  · rw [if_pos hp] at h
    obtain ⟨q, hq, hqc⟩ := List.any_eq_true.mp hp
    refine ⟨?_, q, hq, of_decide_eq_true hqc⟩
    cases hl : w.live E c with
    | none => rw [hl] at h; cases h
    | some cl =>
        rw [hl] at h
        simp only at h
        split at h
        · cases h; rfl
        · cases h
  · rw [if_neg hp] at h; cases h

/-- **An invoke runs on the live cell it read** (LEDGER-6): an `invokeRun` through the pins of `w`
that succeeded handed the run the cell `obj` holds live in `w`. No premise: `pinned` answers only
for a pinned id, and with `w.live` itself. -/
theorem invokeRun_live {X : Ctx D} {w : World D} {pins : List (D × D)} {c : Call D} {actor obj : D}
    {method : Nat} {via : Option D} {cell : Cell} {p : D} {r : Req D}
    (h : invokeRun X (pinned X.env w pins) c actor obj method via = .ok (cell, p, r)) :
    w.live X.env obj = some cell :=
  (readKind_pinned (invokeRun_cell h)).1

omit [Ord D] in
private theorem actFor_head {obj : D} {a : Act} {l : List (D × Act)} : actFor ((obj, a) :: l) obj = a := by
  simp [actFor, List.find?]

/-- **The next run of an object is handed what this run returned.** A signed invoke of `obj`,
derived from `w` (`receive`) and admitted to `w'`, whose run (the program at what the cell's
package names, on the cell's state, at the call's budget) returned the slots `s`: `obj` is live in
`w'`, and its state holds, at every key, what `s` holds. -/
theorem invoke_next_slots {X : Ctx D} {w w' : World D} {c : Call D} {t : Turn D}
    {obj : D} {method : Nat} {args : ByteArray} {budget : Nat} {via : Option D}
    {cell : Cell} {p : D} {r : Req D} {s : Slots} {calls : List (Body D)}
    {rows : List (RowSlot D × RowAct)} {used : Nat}
    (hc : receive X w c = .ok t) (ha : World.admit X.env w t = .ok w')
    (hb : c.unsigned.body = .invoke obj method args budget via)
    (hr : invokeRun X (pinned X.env w c.unsigned.pins) c c.unsigned.member obj method via = .ok (cell, p, r))
    (hp : X.program.run (pinned X.env w c.unsigned.pins) (rowView X.env w c.unsigned) p (stateOf cell)
      method args r (min budget (poolOf c.unsigned.body)) = .ok (s, calls, rows, used)) :
    ∃ cell', w'.live X.env obj = some cell' ∧ ∀ k, (stateOf cell').get k = s.get k := by
  obtain ⟨-, hw⟩ := receive_ok_with hc
  obtain ⟨-, d, hd, hs⟩ := receiveWith_sealed hw
  obtain ⟨-, -, htouch, -⟩ := sealTurn_ok hs
  rw [derive_eq, hb] at hd
  cases hdisp : invoke X (pinned X.env w c.unsigned.pins) (rowView X.env w c.unsigned) c
      (tree X (pinned X.env w c.unsigned.pins) (rowView X.env w c.unsigned) c Bounds.callDepthMax)
      ⟨[], poolOf (Body.invoke obj method args budget via), 0⟩ c.unsigned.member obj method args budget via with
  | error e => simp only [dispatch, hdisp] at hd; cases hd
  | ok q =>
    simp only [dispatch, hdisp, Except.map, Except.ok.injEq] at hd
    subst hd
    obtain ⟨-, cell₀, p₀, r₀, new, calls₀, rows₀, used₀, hr₀, hp₀, -, -, -, hst, -, hdc⟩ := invoke_ok hdisp
    obtain ⟨l, hl⟩ := foldCalls_effects _ _ hdc
    rw [hr] at hr₀
    simp only [Except.ok.injEq, Prod.mk.injEq] at hr₀
    obtain ⟨rfl, rfl, rfl⟩ := hr₀
    rw [hb] at hp
    have hnew : new = s := by
      have := hp₀.symm.trans hp
      simp only [Except.ok.injEq, Prod.mk.injEq] at this
      exact this.1
    subst hnew
    obtain ⟨hlive, q₀, hq₀, hqc⟩ := readKind_pinned (invokeRun_cell hr)
    have hact : ∀ x ∈ t.touches, x.cell = obj →
        x.act = if (diffOps (stateOf cell) new).isEmpty then .keep else .write (diffOps (stateOf cell) new) := by
      intro x hx hxc
      rw [htouch] at hx
      obtain ⟨q', -, rfl⟩ := List.mem_map.mp hx
      simp only at hxc ⊢
      rw [hxc, hl]
      exact actFor_head
    have hex : ∃ x ∈ t.touches, x.cell = obj := by
      rw [htouch]
      exact ⟨_, List.mem_map.mpr ⟨q₀, hq₀, rfl⟩, hqc⟩
    by_cases he : (diffOps (stateOf cell) new).isEmpty = true
    · have hnil : diffOps (stateOf cell) new = [] := List.isEmpty_iff.mp he
      refine ⟨cell, ?_, fun k => ?_⟩
      · obtain ⟨posts, hk, -⟩ := admit_ok ha
        have hframe := admit_frame (c := obj) ha
          (fun x hx hxc => by rw [hact x hx hxc, if_pos he])
          (live_not_created hk hlive)
        unfold World.live; rw [hframe]; exact hlive
      · have := diffOps_next (D := D) hst (by rw [hnil]; exact List.nodup_nil) k
        rwa [hnil] at this
    · obtain ⟨hlive', hn⟩ := admit_live_write ha hlive hex
        (fun x hx hxc => by rw [hact x hx hxc, if_neg he])
      exact ⟨_, hlive', diffOps_next hst hn⟩

/-- **The state the next invoke is handed** (`Runs`' link, LEDGER-14): after the admitted invoke
of `invoke_next_slots`, every invoke of `obj` derived on `w'` (any call, signer, method and pins)
runs on a state that holds, at every key, what the run returned. -/
theorem invoke_next_run {X : Ctx D} {w w' : World D} {c : Call D} {t : Turn D}
    {obj : D} {method : Nat} {args : ByteArray} {budget : Nat} {via : Option D}
    {cell : Cell} {p : D} {r : Req D} {s : Slots} {calls : List (Body D)}
    {rows : List (RowSlot D × RowAct)} {used : Nat}
    (hc : receive X w c = .ok t) (ha : World.admit X.env w t = .ok w')
    (hb : c.unsigned.body = .invoke obj method args budget via)
    (hr : invokeRun X (pinned X.env w c.unsigned.pins) c c.unsigned.member obj method via = .ok (cell, p, r))
    (hp : X.program.run (pinned X.env w c.unsigned.pins) (rowView X.env w c.unsigned) p (stateOf cell)
      method args r (min budget (poolOf c.unsigned.body)) = .ok (s, calls, rows, used))
    {pins' : List (D × D)} {c' : Call D} {actor' : D} {method' : Nat} {via' : Option D}
    {cell' : Cell} {p' : D} {r' : Req D}
    (hr' : invokeRun X (pinned X.env w' pins') c' actor' obj method' via' = .ok (cell', p', r')) :
    ∀ k, (stateOf cell').get k = s.get k := by
  obtain ⟨cell'', hl, hk⟩ := invoke_next_slots hc ha hb hr hp
  have hl' := invokeRun_live hr'
  rw [hl] at hl'
  cases hl'
  exact hk

/-- **The run the next state comes from was judged** (LEDGER-14 `Runs`' judge premise): under
`invoke_next_slots`' premises, the laws in force admitted the run's slots `s` over the cell's state,
under the request the invoke ran with. -/
theorem invoke_next_judged {X : Ctx D} {w w' : World D} {c : Call D} {t : Turn D}
    {obj : D} {method : Nat} {args : ByteArray} {budget : Nat} {via : Option D}
    {cell : Cell} {p : D} {r : Req D} {s : Slots} {calls : List (Body D)}
    {rows : List (RowSlot D × RowAct)} {used : Nat}
    (hc : receive X w c = .ok t) (_ha : World.admit X.env w t = .ok w')
    (hb : c.unsigned.body = .invoke obj method args budget via)
    (hr : invokeRun X (pinned X.env w c.unsigned.pins) c c.unsigned.member obj method via = .ok (cell, p, r))
    (hp : X.program.run (pinned X.env w c.unsigned.pins) (rowView X.env w c.unsigned) p (stateOf cell)
      method args r (min budget (poolOf c.unsigned.body)) = .ok (s, calls, rows, used)) :
    ∃ laws, X.program.judge (pinned X.env w c.unsigned.pins) (some p) laws (stateOf cell) s r = .ok () := by
  obtain ⟨-, hw⟩ := receive_ok_with hc
  obtain ⟨-, d, hd, -⟩ := receiveWith_sealed hw
  rw [derive_eq, hb] at hd
  cases hdisp : invoke X (pinned X.env w c.unsigned.pins) (rowView X.env w c.unsigned) c
      (tree X (pinned X.env w c.unsigned.pins) (rowView X.env w c.unsigned) c Bounds.callDepthMax)
      ⟨[], poolOf (Body.invoke obj method args budget via), 0⟩ c.unsigned.member obj method args budget via with
  | error e => simp only [dispatch, hdisp] at hd; cases hd
  | ok q =>
    obtain ⟨-, cell₀, p₀, r₀, new, calls₀, rows₀, used₀, hr₀, hp₀, -, -, -, -, ⟨laws, -, hj⟩, -⟩ := invoke_ok hdisp
    rw [hr] at hr₀
    simp only [Except.ok.injEq, Prod.mk.injEq] at hr₀
    obtain ⟨rfl, rfl, rfl⟩ := hr₀
    rw [hb] at hp
    have hnew : new = s := by
      have := hp₀.symm.trans hp
      simp only [Except.ok.injEq, Prod.mk.injEq] at this
      exact this.1
    subst hnew
    exact ⟨laws, hj⟩

/-! ## Teeth -/

omit [Ord D] [DecidableEq D] in
/-- **A turn that writes another value breaks the chain.** A run that returned `[(16, 1)]` over a
cell holding `[(16, 0)]`: the write `diffOps` derives leaves state 16 at 1; a write of 2 there
instead (distinct keys, as `checkShape` admits) leaves 2, so the next state is not the run's. -/
theorem next_slots_tooth :
    checkState (D := D) [(16, ⟨#[1]⟩)] = .ok () ∧
      (stateOf ⟨0, .ram, applyOps [(16, ⟨#[0]⟩)]
        (diffOps (stateOf ⟨0, .ram, [(16, ⟨#[0]⟩)]⟩) [(16, ⟨#[1]⟩)])⟩).get 16 = some ⟨#[1]⟩ ∧
      (opKeys [Op.set 16 ⟨#[2]⟩]).Nodup ∧
      (stateOf ⟨0, .ram, applyOps [(16, ⟨#[0]⟩)] [Op.set 16 ⟨#[2]⟩]⟩).get 16 = some ⟨#[2]⟩ ∧
      (⟨#[2]⟩ : ByteArray) ≠ ⟨#[1]⟩ := by
  refine ⟨rfl, diffOps_next (D := D) (cell := ⟨0, .ram, [(16, ⟨#[0]⟩)]⟩) rfl (by decide) 16, by decide,
    by decide, fun h => ?_⟩
  have := congrArg ByteArray.data h
  simp at this

omit [Ord D] [DecidableEq D] in
/-- **A run returning one key twice is refused** (`stateKey`), the second key not above the
first. -/
theorem checkState_dup_refused :
    checkState (D := D) [(16, ⟨#[0]⟩), (16, ⟨#[1]⟩)] = .error (.stateKey 16) := rfl

omit [Ord D] [DecidableEq D] in
/-- **Without that refusal the link fails**: over a cell holding `[(16, 0)]`, a run state
`[(16, 0), (16, 1)]` derives the write `[set 16 1]` (its keys distinct, so `checkShape` admits it),
which leaves 1 at key 16, while the run's slots read 0 there. -/
theorem diffOps_dup_tooth :
    diffOps (stateOf ⟨0, .ram, [(16, ⟨#[0]⟩)]⟩) [(16, ⟨#[0]⟩), (16, ⟨#[1]⟩)] = [.set 16 ⟨#[1]⟩] ∧
      (opKeys [Op.set 16 ⟨#[1]⟩]).Nodup ∧
      (stateOf ⟨0, .ram, applyOps [(16, ⟨#[0]⟩)] [.set 16 ⟨#[1]⟩]⟩).get 16 = some ⟨#[1]⟩ ∧
      Slots.get [(16, ⟨#[0]⟩), (16, ⟨#[1]⟩)] 16 = some ⟨#[0]⟩ ∧ (⟨#[1]⟩ : ByteArray) ≠ ⟨#[0]⟩ := by
  refine ⟨by decide, by decide, by decide, by decide, fun h => ?_⟩
  have := congrArg ByteArray.data h
  simp at this

end Nanodregg.Kernel.Receive
