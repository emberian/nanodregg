/-
# Kernel.Proofs.CellsFit — every cell of a kernel World fits CODEC's cell codec (KERNEL-31)

The read theorems of `Kernel.Proofs.Cells` take `w.CellsFit F E`, and at the deployed codec `F` must
be CODEC's own `Cell.Fits` (kind below 2^32, at most `Bounds.slotsPerCellMax` slots, keys below
2^32, values at most `Bounds.valueBytesMax` bytes): `cellBytes` is injective only there
(`Codec.Kernel.cellBytes_injective`). This module proves that the kernel keeps exactly that
predicate, not a twin of it:

* `genesis_cellsFit`: the genesis World's cells fit, given `GenesisFits` (a founder's key is a
  value slot) and digest bytes of at most `Bounds.valueBytesMax` (a grant's target, grantee and
  issuer, a member's next-key digest);
* `admit_cellsFit`, `fold_cellsFit`: every admitted turn keeps it. A born cell fits by
  `checkBounds` (`Codec.Kernel.checkBounds_fits`); a written cell's slots are its old slots or a
  `set` op's pair (`mem_applyOps`), each op bounded by `checkBounds`, and the count by `postWrite`'s
  own check; a tombstone and a spent nullifier hold no cell.
-/
import Kernel.Proofs.Cells
import Kernel.Proofs.Rooted
import Kernel.Proofs.Origin
import Codec.Proofs.Kernel

namespace Nanodregg.Kernel

open Nanodregg.Codec.Kernel (Cell.Fits Slots.Fits Op.Fits Act.Fits checkBounds_fits)
open Nanodregg.Codec.Stream (u64_size)

/-! ## Slot lists: what `set`, `erase`, `applyOps` and `slotsOf` can leave -/

theorem mem_slots_set {q : Nat × ByteArray} {k : Nat} {v : ByteArray} :
    ∀ {s : Slots}, q ∈ Slots.set k v s → q = (k, v) ∨ q ∈ s
  | [], h => by simpa [Slots.set] using h
  | (k', v') :: rest, h => by
      unfold Slots.set at h
      split at h
      · simpa only [List.mem_cons] using h
      · split at h
        · simp only [List.mem_cons] at h ⊢
          rcases h with h | h
          · exact .inl h
          · exact .inr (.inr h)
        · simp only [List.mem_cons] at h ⊢
          rcases h with h | h
          · exact .inr (.inl h)
          · rcases mem_slots_set h with h | h
            · exact .inl h
            · exact .inr (.inr h)

theorem length_slots_set {k : Nat} {v : ByteArray} : ∀ {s : Slots}, (Slots.set k v s).length ≤ s.length + 1
  | [] => by simp [Slots.set]
  | (k', v') :: rest => by
      unfold Slots.set
      split
      · simp
      · split
        · simp
        · have := @length_slots_set k v rest
          simp only [List.length_cons]; omega

theorem mem_slots_erase {q : Nat × ByteArray} {k : Nat} : ∀ {s : Slots}, q ∈ Slots.erase k s → q ∈ s
  | [], h => h
  | (k', v') :: rest, h => by
      unfold Slots.erase at h
      split at h
      · exact List.mem_cons_of_mem _ h
      · simp only [List.mem_cons] at h ⊢
        rcases h with h | h
        · exact .inl h
        · exact .inr (mem_slots_erase h)

/-- A slot after a write is an old slot, or the pair of one of its `set` ops. -/
theorem mem_applyOps {q : Nat × ByteArray} :
    ∀ {ops : List Op} {s : Slots}, q ∈ applyOps s ops → q ∈ s ∨ Op.set q.1 q.2 ∈ ops
  | [], _, h => .inl h
  | o :: ops, s, h => by
      have h' : q ∈ applyOps (applyOp s o) ops := h
      rcases mem_applyOps h' with h | h
      · cases o with
        | set k v =>
            rcases mem_slots_set (s := s) h with rfl | h
            · exact .inr (by simp)
            · exact .inl h
        | erase k => exact .inl (mem_slots_erase (s := s) h)
      · exact .inr (List.mem_cons_of_mem _ h)

theorem slots_foldl_set {q : Nat × ByteArray} :
    ∀ {ps : List (Nat × ByteArray)} {s : Slots},
      (q ∈ ps.foldl (fun s p => s.set p.1 p.2) s → q ∈ s ∨ q ∈ ps) ∧
        (ps.foldl (fun s p => s.set p.1 p.2) s).length ≤ s.length + ps.length
  | [], _ => ⟨.inl, by simp⟩
  | p :: rest, s => by
      obtain ⟨hm, hl⟩ := @slots_foldl_set q rest (s.set p.1 p.2)
      refine ⟨fun h => ?_, ?_⟩
      · rcases hm h with h | h
        · rcases mem_slots_set h with rfl | h
          · exact .inr (by simp)
          · exact .inl h
        · exact .inr (List.mem_cons_of_mem _ h)
      · have := @length_slots_set p.1 p.2 s
        simp only [List.foldl_cons, List.length_cons] at hl ⊢; omega

/-- `slotsOf` fits when every pair it is given fits and there are few enough of them. -/
theorem slotsOf_fits {ps : List (Nat × ByteArray)} (hl : ps.length ≤ Bounds.slotsPerCellMax)
    (hp : ∀ q ∈ ps, q.1 < 2 ^ 32 ∧ q.2.size ≤ Bounds.valueBytesMax) : Slots.Fits (Receive.slotsOf ps) := by
  unfold Receive.slotsOf
  refine ⟨?_, fun q hq => ?_⟩
  · have := (@slots_foldl_set (0, ByteArray.empty) ps []).2
    simp only [List.length_nil, Nat.zero_add] at this; omega
  · rcases (@slots_foldl_set q ps []).1 hq with h | h
    · simp at h
    · exact hp q h

/-! ## A written cell fits -/

variable {D : Type} [Ord D] [DecidableEq D]

omit [Ord D] [DecidableEq D] in
/-- What `postWrite` returns is the cell with the ops applied, within the slot count. -/
theorem postWrite_ok {c : D} {cell post : Cell} {ops : List Op} (h : postWrite c cell ops = .ok post) :
    post = { cell with slots := applyOps cell.slots ops } ∧ post.slots.length ≤ Bounds.slotsPerCellMax := by
  unfold postWrite at h
  split at h
  · simp at h
  · simp only [except_bind_ok, pure, Except.pure, Except.ok.injEq] at h
    obtain ⟨⟨⟩, _, ⟨⟩, hr, h⟩ := h
    rw [req_ok, decide_eq_true_eq] at hr
    subst h; exact ⟨rfl, hr⟩
  · simp only [except_bind_ok, pure, Except.pure, Except.ok.injEq] at h
    obtain ⟨⟨⟩, hr, h⟩ := h
    rw [req_ok, decide_eq_true_eq] at hr
    subst h; exact ⟨rfl, hr⟩
  · simp only [except_bind_ok, pure, Except.pure, Except.ok.injEq] at h
    obtain ⟨⟨⟩, hr, ⟨⟩, _, h⟩ := h
    rw [req_ok, decide_eq_true_eq] at hr
    subst h; exact ⟨rfl, hr⟩

omit [Ord D] [DecidableEq D] in
/-- A write of bounded ops into a fitting cell leaves a fitting cell. -/
theorem postWrite_fits {c : D} {cell post : Cell} {ops : List Op} (hc : Cell.Fits cell)
    (ho : ∀ o ∈ ops, Op.Fits o) (h : postWrite c cell ops = .ok post) : Cell.Fits post := by
  obtain ⟨rfl, hl⟩ := postWrite_ok h
  refine ⟨hc.1, hl, fun q hq => ?_⟩
  rcases mem_applyOps hq with h | h
  · exact hc.2.2 q h
  · exact ho _ h

/-- A touch that leaves something behind, over a fitting World and a bounded act, leaves a fitting
entry. -/
theorem touchCheck_cellFit {E : Env D} {w : World D} {x : Touch D} {p : Post D}
    (hw : w.CellsFit Cell.Fits E) (hx : Act.Fits x.act) (h : touchCheck E w x = .ok (some p)) :
    (Leaf.entry p.entry).CellFit Cell.Fits := by
  unfold touchCheck at h
  simp only [except_bind_ok] at h
  obtain ⟨⟨⟩, _, h⟩ := h
  cases ha : x.act with
  | keep => rw [ha] at h; simp [pure, Except.pure] at h
  | write ops =>
      rw [ha] at h hx
      cases hc : w.live E x.cell with
      | none => rw [hc] at h; simp at h
      | some cell =>
          rw [hc] at h
          simp only [except_bind_ok, pure, Except.pure, Except.ok.injEq, Option.some.injEq] at h
          obtain ⟨post, hp, rfl⟩ := h
          exact postWrite_fits (hw _ _ (live_get hc)) hx.2 hp
  | retire =>
      rw [ha] at h
      cases hc : w.live E x.cell with
      | none => rw [hc] at h; simp at h
      | some cell =>
          rw [hc] at h
          simp only [except_bind_ok, pure, Except.pure, Except.ok.injEq, Option.some.injEq] at h
          obtain ⟨_, _, rfl⟩ := h
          trivial

/-! ## The map under insertion -/

omit [Ord D] in
theorem insertAll_cellFit {E : Env D} {F : Cell → Prop} :
    ∀ {m : Cells D} (ps : List (D × Entry)), (∀ p ∈ ps, (Leaf.entry p.2).CellFit F) →
      (∀ s l, m.get (trieSpec E) s = some l → l.CellFit F) →
      ∀ s l, (insertAll E m ps).get (trieSpec E) s = some l → l.CellFit F
  | _, [], _, h => h
  | m, p :: rest, hp, h => by
      apply insertAll_cellFit (m := m.insert (trieSpec E) (.cell p.1) (.entry p.2)) rest
        (fun q hq => hp q (List.mem_cons_of_mem _ hq))
      intro s l hg
      rw [Trie.get_insert] at hg
      split at hg
      · simp only [Option.some.injEq] at hg; subst hg; exact hp p (by simp)
      · exact h s l hg

omit [Ord D] in
theorem spendAll_cellFit {E : Env D} {F : Cell → Prop} :
    ∀ {m : Cells D} (ns : List D), (∀ s l, m.get (trieSpec E) s = some l → l.CellFit F) →
      ∀ s l, (spendAll E m ns).get (trieSpec E) s = some l → l.CellFit F
  | _, [], h => h
  | m, n :: rest, h => by
      apply spendAll_cellFit (m := m.insert (trieSpec E) (.nullifier n) .spent) rest
      intro s l hg
      rw [Trie.get_insert] at hg
      split at hg
      · simp only [Option.some.injEq] at hg; subst hg; trivial
      · exact h s l hg

/-! ## Genesis, admit, fold -/

/-- **Genesis fits.** A founder's member cell holds its key and its next-key digest bytes; its root
grant holds three digests and two rights slots. -/
theorem genesis_cellsFit {X : Receive.Ctx D} {name nonce : ByteArray} {allowance : Nat}
    {founders : List (ByteArray × D)} (hf : Receive.GenesisFits X name nonce allowance founders)
    (hbd : ∀ d, (X.env.bytes d).size ≤ Bounds.valueBytesMax) :
    (Receive.genesisWorld X name nonce allowance founders).CellsFit Cell.Fits X.env := by
  have hv : Bounds.eventBytesMax = Bounds.valueBytesMax := rfl
  have hr : Receive.rightSlots [.observe, .enroll Receive.enrollMax] =
      [(Receive.rightKey .observe, ByteArray.empty),
       (Receive.enrollBase, Receive.countBytes (Receive.enrollUnits [.observe, .enroll Receive.enrollMax]))] := rfl
  have kM : Receive.kindMember < 2 ^ 32 := by decide
  have kG : Receive.kindGrant < 2 ^ 32 := by decide
  have k0 : Receive.slotKey < 2 ^ 32 := by decide
  have k1 : Receive.slotNext < 2 ^ 32 := by decide
  have kT : Receive.grantTarget < 2 ^ 32 := by decide
  have kE : Receive.grantGrantee < 2 ^ 32 := by decide
  have kI : Receive.grantIssuer < 2 ^ 32 := by decide
  have kO : Receive.rightKey .observe < 2 ^ 32 := by decide
  have kB : Receive.enrollBase < 2 ^ 32 := by decide
  have l2 : 2 ≤ Bounds.slotsPerCellMax := by decide
  have l5 : 5 ≤ Bounds.slotsPerCellMax := by decide
  have v0 : ByteArray.empty.size ≤ Bounds.valueBytesMax := by decide
  have v8 : ∀ n, (Receive.countBytes n).size ≤ Bounds.valueBytesMax := fun n => by
    simp [Receive.countBytes, Bounds.valueBytesMax]
  refine insertAll_cellFit _ ?_ (fun s _ hg => nomatch hg.symm.trans (Trie.get_empty (trieSpec X.env) s))
  rintro ⟨id, e⟩ hq
  obtain ⟨p, hp, ⟨_, he⟩ | ⟨_, he⟩⟩ := Receive.mem_founderEntries hq
  · subst he
    have hk := (hf.2.2.2.1 p.1 (List.fst_mem_of_mem_zipIdx hp)).1
    refine ⟨kM, slotsOf_fits (by simpa using l2) fun q hq => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact ⟨k0, hv ▸ hk⟩
    · exact ⟨k1, hbd _⟩
  · subst he
    refine ⟨kG, slotsOf_fits ?_ fun q hq => ?_⟩
    · rw [hr]; simpa using l5
    rw [hr] at hq
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact ⟨kT, hbd _⟩
    · exact ⟨kE, hbd _⟩
    · exact ⟨kI, hbd _⟩
    · exact ⟨kO, v0⟩
    · exact ⟨kB, v8 _⟩

/-- **Admit keeps the cells fitting.** -/
theorem admit_cellsFit {E : Env D} {w w' : World D} {t : Turn D} (hw : w.CellsFit Cell.Fits E)
    (h : World.admit E w t = .ok w') : w'.CellsFit Cell.Fits E := by
  obtain ⟨posts, hk, rfl⟩ := admit_ok h
  obtain ⟨_, _, _, ⟨_, htf⟩, ⟨_, hcf⟩, _⟩ := checkBounds_fits t hk.bounds
  have hborn : ∀ p ∈ bornEntries t, (Leaf.entry p.2).CellFit Cell.Fits := by
    intro q hq
    simp only [bornEntries, List.mem_map] at hq
    obtain ⟨c, hc, rfl⟩ := hq
    exact (hcf c hc).2
  have hposts : ∀ p ∈ posts.map Post.pair, (Leaf.entry p.2).CellFit Cell.Fits := by
    intro q hq
    simp only [List.mem_map] at hq
    obtain ⟨p, hp, rfl⟩ := hq
    obtain ⟨raw, hm, hpr⟩ := hk.touches
    have hp' : some p ∈ raw := by simpa [hpr, List.reduceOption, List.mem_filterMap] using hp
    obtain ⟨x, hx, hr⟩ := mapEx_mem hm (some p) hp'
    exact touchCheck_cellFit hw (htf x hx).2.2 hr
  exact spendAll_cellFit _ (insertAll_cellFit _ hborn (insertAll_cellFit _ hposts hw))

/-- **Fold keeps the cells fitting.** -/
theorem fold_cellsFit {E : Env D} {w w' : World D} {l : List (Step D)} (hf : w.CellsFit Cell.Fits E)
    (h : World.fold E w l = .ok w') : w'.CellsFit Cell.Fits E :=
  fold_keeps (P := fun v => v.CellsFit Cell.Fits E) admit_cellsFit
    (fun hp hr => fun s l hg => hp s l (by rw [← refuse_trie hr]; exact hg)) hf h

end Nanodregg.Kernel
